use std::collections::{VecDeque};
use std::{cmp};
use syscall::error::Result;

use crate::disk::Disk;
use crate::BLOCK_SIZE;

use crate::lru_cache::LruCache;
use core::sync::atomic::{ AtomicU64, Ordering };
use std::time::UNIX_EPOCH;

struct CacheEntry {
    data: [u8; BLOCK_SIZE as usize],
    dirty: bool,
    last_modified: u64,
}

pub struct DiskCache<T> {
    inner: T,
    cache: LruCache<u64, CacheEntry>,
    last_writeback: AtomicU64,
    writeback_interval: u64,
    order: VecDeque<u64>,
    size: usize,
}

// return current timestamp in seconds since UNIX_EPOCH
fn current_timestamp() -> u64 {
    std::time::SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
}

impl<T: Disk> DiskCache<T> {
    pub fn new(inner: T) -> Self {
        // 16 MB cache
        let size = 16 * 1024 * 1024 / BLOCK_SIZE as usize;
        let writeback_interval = 5u64;
        DiskCache {
            inner,
            cache: LruCache::new(size),
            last_writeback: AtomicU64::new(current_timestamp()),
            writeback_interval,
            order: VecDeque::with_capacity(size),
            size,
        }
    }

    fn check_writeback(&mut self) -> Result<()> {
        let now = current_timestamp();
        let last = self.last_writeback.load(Ordering::Relaxed);

        if now - last >= self.writeback_interval || self.cache.map.len() > self.cache.capacity {
            self.writeback_dirty_blocks()?;
            self.last_writeback.store(now, Ordering::Relaxed);
        }
        Ok(())
    }
    fn writeback_dirty_blocks(&mut self) -> Result<()> {
        // kprintln!("DiskCache: writeback dirty blocks");
        let dirty_keys = self.cache.filter_keys(|entry| entry.dirty);

        for block in dirty_keys {
            if let Some(entry) = self.cache.get_mut(&block) {
                unsafe { self.inner.write_at(block, &entry.data)? };
                entry.dirty = false;
            }
        }
        Ok(())
    }

    fn block_slices_mut(buffer: &mut [u8]) -> impl Iterator<Item = &mut [u8]> {
        buffer.chunks_mut(BLOCK_SIZE as usize)
    }

    fn block_slices(buffer: &[u8]) -> impl Iterator<Item = &[u8]> {
        (0..(buffer.len() + BLOCK_SIZE as usize - 1) / (BLOCK_SIZE as usize)).map(move |i| {
            let start = i * BLOCK_SIZE as usize;
            let end = cmp::min(start + BLOCK_SIZE as usize, buffer.len());
            &buffer[start..end]
        })
    }
}

impl<T: Disk> Disk for DiskCache<T> {
    unsafe fn read_at(&mut self, block: u64, buffer: &mut [u8]) -> Result<usize> {
        self.check_writeback()?;

        let mut read = 0;
        let mut need_read_from_disk = false;

        for (i, buf_slice) in Self::block_slices_mut(buffer).enumerate() {
            let current_block = block + i as u64;

            if let Some(entry) = self.cache.get_mut(&current_block) {
                buf_slice.copy_from_slice(&entry.data[..buf_slice.len()]);
                read += buf_slice.len();
            } else {
                need_read_from_disk = true;
                break;
            }
        }

        if need_read_from_disk {
            let disk_read = self.inner.read_at(block, buffer)?;

            for (i, data_slice) in Self::block_slices_mut(buffer).enumerate() {
                let current_block = block + i as u64;
                let mut cache_data = [0u8; BLOCK_SIZE as usize];
                cache_data[..data_slice.len()].copy_from_slice(data_slice);

                self.cache.put(
                    current_block,
                    CacheEntry {
                        data: cache_data,
                        dirty: false,
                        last_modified: current_timestamp(),
                    },
                );
            }
            read = disk_read;
        }

        Ok(read)
    }

    unsafe fn write_at(&mut self, block: u64, buffer: &[u8]) -> Result<usize> {
        self.check_writeback()?;

        let mut written = 0;

        for (i, data_slice) in Self::block_slices(buffer).enumerate() {
            let current_block = block + i as u64;
            let mut cache_data = [0u8; BLOCK_SIZE as usize];
            cache_data[..data_slice.len()].copy_from_slice(data_slice);

            self.cache.put(
                current_block,
                CacheEntry {
                    data: cache_data,
                    dirty: true,
                    last_modified: current_timestamp(),
                },
            );
            written += data_slice.len();
        }

        Ok(written)
    }

    fn size(&mut self) -> Result<u64> {
        self.inner.size()
    }
}
