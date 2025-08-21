use alloc::{
    boxed::Box,
    collections::{BTreeMap, VecDeque},
    vec::Vec,
};
use core::{
    cmp::min,
    mem,
    ops::{Deref, DerefMut},
};
use syscall::error::{
    Error, Result, EEXIST, EINVAL, EIO, EISDIR, ENOENT, ENOSPC, ENOTDIR, ENOTEMPTY, ERANGE,
};

use crate::{
    htree::{self, HTreeHash, HTreeNode, HTreePtr},
    AllocEntry, AllocList, Allocator, BlockAddr, BlockData, BlockLevel, BlockPtr, BlockTrait,
    DirEntry, DirList, Disk, FileSystem, Header, Node, NodeLevel, RecordRaw, TreeData, TreePtr,
    ALLOC_GC_THRESHOLD, ALLOC_LIST_ENTRIES, DIR_ENTRY_MAX_LENGTH, HEADER_RING,
};

pub struct Transaction<'a, D: Disk> {
    fs: &'a mut FileSystem<D>,
    //TODO: make private
    pub header: Header,
    //TODO: make private
    pub header_changed: bool,
    allocator: Allocator,
    allocator_log: VecDeque<AllocEntry>,
    deallocate: Vec<BlockAddr>,
    write_cache: BTreeMap<BlockAddr, Box<[u8]>>,
}

impl<'a, D: Disk> Transaction<'a, D> {
    pub(crate) fn new(fs: &'a mut FileSystem<D>) -> Self {
        let header = fs.header;
        let allocator = fs.allocator.clone();
        Self {
            fs,
            header,
            header_changed: false,
            allocator,
            allocator_log: VecDeque::new(),
            deallocate: Vec::new(),
            write_cache: BTreeMap::new(),
        }
    }

    pub fn commit(mut self, squash: bool) -> Result<()> {
        self.sync(squash)?;
        self.fs.header = self.header;
        self.fs.allocator = self.allocator;
        Ok(())
    }

    //
    // MARK: block operations
    //

    /// Allocate a new block of size `level`, returning its address.
    /// - returns `Err(ENOSPC)` if a block of this size could not be alloated.
    /// - unsafe because order must be done carefully and changes must be flushed to disk
    pub(crate) unsafe fn allocate(&mut self, level: BlockLevel) -> Result<BlockAddr> {
        match self.allocator.allocate(level) {
            Some(addr) => {
                self.allocator_log.push_back(AllocEntry::allocate(addr));
                Ok(addr)
            }
            None => Err(Error::new(ENOSPC)),
        }
    }

    /// Deallocate the given block.
    /// - unsafe because order must be done carefully and changes must be flushed to disk
    pub(crate) unsafe fn deallocate(&mut self, addr: BlockAddr) {
        //TODO: should we use some sort of not-null abstraction?
        assert!(!addr.is_null());

        // Remove from write_cache if it is there, since it no longer needs to be written
        //TODO: for larger blocks do we need to check for sub-blocks in here?
        self.write_cache.remove(&addr);

        // Search and remove the last matching entry in allocator_log
        let mut found = false;
        for i in (0..self.allocator_log.len()).rev() {
            let entry = self.allocator_log[i];
            if entry.index() == addr.index() && entry.count() == -addr.level().blocks() {
                found = true;
                self.allocator_log.remove(i);
                break;
            }
        }

        if found {
            // Deallocate immediately since it is an allocation that was not needed
            self.allocator.deallocate(addr);
        } else {
            // Deallocate later when syncing filesystem, to avoid re-use
            self.deallocate.push(addr);
        }
    }

    fn deallocate_block<T: BlockTrait>(&mut self, ptr: BlockPtr<T>) {
        if !ptr.is_null() {
            unsafe {
                self.deallocate(ptr.addr());
            }
        }
    }

    /// Drain `self.allocator_log` and `self.deallocate`,
    /// updating the [`AllocList`] with the resulting state.
    ///
    /// This method does not write anything to disk,
    /// all writes are cached.
    ///
    /// To keep the allocator log from growing excessively, it will
    /// periodically be fully rebuilt using the state of `self.allocator`.
    /// This rebuild can be forced by setting `force_squash` to `true`.
    fn sync_allocator(&mut self, force_squash: bool) -> Result<bool> {
        let mut prev_ptr = BlockPtr::default();
        let should_gc = self.header.generation() % ALLOC_GC_THRESHOLD == 0
            && self.header.generation() >= ALLOC_GC_THRESHOLD
            && self.allocator.free() > 0;
        if force_squash || should_gc {
            // Clear and rebuild alloc log
            self.allocator_log.clear();
            let levels = self.allocator.levels();
            for level in (0..levels.len()).rev() {
                let count = (1 << level) as i64;
                'indices: for &index in levels[level].iter() {
                    for entry in self.allocator_log.iter_mut() {
                        if index + count as u64 == entry.index() {
                            // New entry is at start of existing entry
                            *entry = AllocEntry::new(index, count + entry.count());
                            continue 'indices;
                        } else if entry.index() + entry.count() as u64 == index {
                            // New entry is at end of existing entry
                            *entry = AllocEntry::new(entry.index(), entry.count() + count);
                            continue 'indices;
                        }
                    }

                    self.allocator_log.push_back(AllocEntry::new(index, count));
                }
            }

            // Prepare to deallocate old alloc blocks
            let mut alloc_ptr = self.header.alloc;
            while !alloc_ptr.is_null() {
                let alloc = self.read_block(alloc_ptr)?;
                self.deallocate.push(alloc.addr());
                alloc_ptr = alloc.data().prev;
            }
        } else {
            // Return if there are no log changes
            if self.allocator_log.is_empty() && self.deallocate.is_empty() {
                return Ok(false);
            }

            // Push old alloc block to front of allocator log
            //TODO: just skip this if it is already full?
            let alloc = self.read_block(self.header.alloc)?;
            for i in (0..alloc.data().entries.len()).rev() {
                let entry = alloc.data().entries[i];
                if !entry.is_null() {
                    self.allocator_log.push_front(entry);
                }
            }

            // Prepare to deallocate old alloc block
            self.deallocate.push(alloc.addr());

            // Link to previous alloc block
            prev_ptr = alloc.data().prev;
        }

        // Allocate required blocks, including CoW of current alloc tail
        let mut new_blocks = Vec::new();
        while new_blocks.len() * ALLOC_LIST_ENTRIES
            <= self.allocator_log.len() + self.deallocate.len()
        {
            new_blocks.push(unsafe { self.allocate(BlockLevel::default())? });
        }

        // De-allocate old blocks (after allocation to prevent re-use)
        //TODO: optimize allocator log in memory
        while let Some(addr) = self.deallocate.pop() {
            self.allocator.deallocate(addr);
            self.allocator_log.push_back(AllocEntry::deallocate(addr));
        }

        for new_block in new_blocks {
            let mut alloc = BlockData::<AllocList>::empty(new_block).unwrap();
            alloc.data_mut().prev = prev_ptr;
            for entry in alloc.data_mut().entries.iter_mut() {
                if let Some(log_entry) = self.allocator_log.pop_front() {
                    *entry = log_entry;
                } else {
                    break;
                }
            }
            prev_ptr = unsafe { self.write_block(alloc)? };
        }

        self.header.alloc = prev_ptr;
        self.header_changed = true;

        Ok(true)
    }

    /// Write all changes cached in this [`Transaction`] to disk.
    pub fn sync(&mut self, force_squash: bool) -> Result<bool> {
        // Make sure alloc is synced
        self.sync_allocator(force_squash)?;

        // Write all items in write cache
        for (addr, raw) in self.write_cache.iter_mut() {
            // sync_alloc must have changed alloc block pointer
            // if we have any blocks to write
            assert!(self.header_changed);

            self.fs.encrypt(raw, *addr);
            let count = unsafe { self.fs.disk.write_at(self.fs.block + addr.index(), raw)? };
            if count != raw.len() {
                // Read wrong number of bytes
                #[cfg(feature = "log")]
                log::error!("SYNC WRITE_CACHE: WRONG NUMBER OF BYTES");
                return Err(Error::new(EIO));
            }
        }
        self.write_cache.clear();

        // Do nothing if there are no changes to write.
        //
        // This only happens if `self.write_cache` was empty,
        // and the fs header wasn't changed by another operation.
        if !self.header_changed {
            return Ok(false);
        }

        // Update header to next generation
        let gen = self.header.update(self.fs.cipher_opt.as_ref());
        let gen_block = gen % HEADER_RING;

        // Write header
        let count = unsafe {
            self.fs
                .disk
                .write_at(self.fs.block + gen_block, &self.header)?
        };
        if count != mem::size_of_val(&self.header) {
            // Read wrong number of bytes
            #[cfg(feature = "log")]
            log::error!("SYNC: WRONG NUMBER OF BYTES");
            return Err(Error::new(EIO));
        }

        self.header_changed = false;
        Ok(true)
    }

    pub fn read_block<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: BlockPtr<T>,
    ) -> Result<BlockData<T>> {
        if ptr.is_null() {
            // Pointer is invalid (should this return None?)
            #[cfg(feature = "log")]
            log::error!("READ_BLOCK: POINTER IS NULL");
            return Err(Error::new(ENOENT));
        }

        let mut data = match T::empty(ptr.addr().level()) {
            Some(some) => some,
            None => {
                #[cfg(feature = "log")]
                log::error!("READ_BLOCK: INVALID BLOCK LEVEL FOR TYPE");
                return Err(Error::new(ENOENT));
            }
        };
        if let Some(raw) = self.write_cache.get(&ptr.addr()) {
            data.copy_from_slice(raw);
        } else {
            let count = unsafe {
                self.fs
                    .disk
                    .read_at(self.fs.block + ptr.addr().index(), &mut data)?
            };
            if count != data.len() {
                // Read wrong number of bytes
                #[cfg(feature = "log")]
                log::error!("READ_BLOCK: WRONG NUMBER OF BYTES");
                return Err(Error::new(EIO));
            }
            self.fs.decrypt(&mut data, ptr.addr());
        }

        let block = BlockData::new(ptr.addr(), data);
        let block_ptr = block.create_ptr();
        if block_ptr.hash() != ptr.hash() {
            // Incorrect hash
            #[cfg(feature = "log")]
            log::error!(
                "READ_BLOCK: INCORRECT HASH 0x{:X} != 0x{:X} for block 0x{:X}",
                block_ptr.hash(),
                ptr.hash(),
                ptr.addr().index()
            );
            return Err(Error::new(EIO));
        }
        Ok(block)
    }

    /// Read block data or, if pointer is null, return default block data
    ///
    /// # Safety
    /// Unsafe because it creates strange BlockData types that must be swapped before use
    unsafe fn read_block_or_empty<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: BlockPtr<T>,
    ) -> Result<BlockData<T>> {
        if ptr.is_null() {
            match T::empty(ptr.addr().level()) {
                Some(empty) => Ok(BlockData::new(BlockAddr::default(), empty)),
                None => {
                    #[cfg(feature = "log")]
                    log::error!("READ_BLOCK_OR_EMPTY: INVALID BLOCK LEVEL FOR TYPE");
                    Err(Error::new(ENOENT))
                }
            }
        } else {
            self.read_block(ptr)
        }
    }

    unsafe fn read_record<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: BlockPtr<T>,
        level: BlockLevel,
    ) -> Result<BlockData<T>> {
        let record = unsafe { self.read_block_or_empty(ptr)? };
        if record.addr().level() >= level {
            // Return record if it is larger than or equal to requested level
            return Ok(record);
        }

        // If a larger level was requested,
        // create a fake record with the requested level
        // and fill it with the data in the original record.
        let (_old_addr, old_raw) = unsafe { record.into_parts() };
        let mut raw = match T::empty(level) {
            Some(empty) => empty,
            None => {
                #[cfg(feature = "log")]
                log::error!("READ_RECORD: INVALID BLOCK LEVEL FOR TYPE");
                return Err(Error::new(ENOENT));
            }
        };
        let len = min(raw.len(), old_raw.len());
        raw[..len].copy_from_slice(&old_raw[..len]);
        Ok(BlockData::new(BlockAddr::null(level), raw))
    }

    /// Write block data to a new address, returning new address
    pub fn sync_block<T: BlockTrait + Deref<Target = [u8]>>(
        &mut self,
        mut block: BlockData<T>,
    ) -> Result<BlockPtr<T>> {
        // Swap block to new address
        let level = block.addr().level();
        let old_addr = block.swap_addr(unsafe { self.allocate(level)? });
        // Deallocate old address (will only take effect after sync_allocator, which helps to
        // prevent re-use before a new header is written
        if !old_addr.is_null() {
            unsafe {
                self.deallocate(old_addr);
            }
        }
        // Write new block
        unsafe { self.write_block(block) }
    }

    /// Write block data, returning a calculated block pointer
    ///
    /// # Safety
    /// Unsafe to encourage CoW semantics
    pub(crate) unsafe fn write_block<T: BlockTrait + Deref<Target = [u8]>>(
        &mut self,
        block: BlockData<T>,
    ) -> Result<BlockPtr<T>> {
        if block.addr().is_null() {
            // Pointer is invalid
            #[cfg(feature = "log")]
            log::error!("WRITE_BLOCK: POINTER IS NULL");
            return Err(Error::new(ENOENT));
        }

        //TODO: do not convert to boxed slice if it already is one
        self.write_cache.insert(
            block.addr(),
            block.data().deref().to_vec().into_boxed_slice(),
        );

        Ok(block.create_ptr())
    }

    //
    // MARK: tree operations
    //

    /// Walk the tree and return the contents and address
    /// of the data block that `ptr` points too.
    fn read_tree_and_addr<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: TreePtr<T>,
    ) -> Result<(TreeData<T>, BlockAddr)> {
        if ptr.is_null() {
            // ID is invalid (should this return None?)
            #[cfg(feature = "log")]
            log::error!("READ_TREE: ID IS NULL");
            return Err(Error::new(ENOENT));
        }

        println!("get: {}", ptr.id());
        let arc = self.fs.inode_to_block_id.clone();
        let mut lock = arc.write().unwrap();
        if let Some(&bock_ptr) = lock.get(&ptr.id())
        {
            let raw = self.read_block(bock_ptr)?;
            let mut data = T::empty(BlockLevel::default()).unwrap();
            data.copy_from_slice(raw.data());
            return Ok((TreeData::new(ptr.id(), data), bock_ptr.addr()))
        }
        // panic!("READ_TREE: ID IS NULL");
        println!("read_tree: {} cache miss", ptr.id());

        let (i3, i2, i1, i0) = ptr.indexes();
        let l3 = self.read_block(self.header.tree)?;
        let l2 = self.read_block(l3.data().ptrs[i3])?;
        let l1 = self.read_block(l2.data().ptrs[i2])?;
        let l0 = self.read_block(l1.data().ptrs[i1])?;
        let raw = self.read_block(l0.data().ptrs[i0])?;

        //TODO: transmute instead of copy?
        let mut data = match T::empty(BlockLevel::default()) {
            Some(some) => some,
            None => {
                #[cfg(feature = "log")]
                log::error!("READ_TREE: INVALID BLOCK LEVEL FOR TYPE");
                return Err(Error::new(ENOENT));
            }
        };
        data.copy_from_slice(raw.data());

        lock.insert(ptr.id(), l0.data().ptrs[i0]);

        Ok((TreeData::new(ptr.id(), data), l0.data().ptrs[i0].addr()))

    }

    /// Walk the tree and return the contents of the data block that `ptr` points too.
    pub fn read_tree<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: TreePtr<T>,
    ) -> Result<TreeData<T>> {
        Ok(self.read_tree_and_addr(ptr)?.0)
    }

    /// Insert `block_ptr` into the first free slot in the tree,
    /// returning a pointer to that slot.
    pub fn insert_tree<T: Deref<Target = [u8]>>(
        &mut self,
        block_ptr: BlockPtr<T>,
    ) -> Result<TreePtr<T>> {
        // Remember that if there is a free block at any level it will always sync when it
        // allocates at the lowest level, so we can save a write by not writing each level as it
        // is allocated.
        let mut lock = self.fs.treetable.write().unwrap();
        let id = lock.insert().unwrap();
        self.fs.inode_to_block_id.write().unwrap().insert(id, unsafe { block_ptr.cast() });
        println!("insert: {}", id);
        let tree_ptr = TreePtr::new(id);

        Ok(tree_ptr)
    }

    /// Clear the previously claimed slot in the tree for the given `ptr`. Note that this
    /// should only be called after the corresponding node block has already been deallocated.
    fn remove_tree<T: BlockTrait + DerefMut<Target = [u8]>>(
        &mut self,
        ptr: TreePtr<T>,
    ) -> Result<()> {
        if ptr.is_null() {
            // ID is invalid (should this return None?)
            #[cfg(feature = "log")]
            log::error!("READ_TREE: ID IS NULL");
            return Err(Error::new(ENOENT));
        }
        let (i3, i2, i1, i0) = ptr.indexes();
        let mut l3 = self.read_block(self.header.tree)?;
        let mut l2 = self.read_block(l3.data().ptrs[i3])?;
        let mut l1 = self.read_block(l2.data().ptrs[i2])?;
        let mut l0 = self.read_block(l1.data().ptrs[i1])?;

        // Clear the value in the tree, but do not deallocate the node block, as that should already
        // have been done at the node level. The inner tree nodes can be deallocated if they are empty.
        l0.data_mut().set_branch_full(i0, false);
        l0.data_mut().ptrs[i0] = BlockPtr::default();
        let l0_ptr = if l0.data().tree_list_is_empty() {
            unsafe { self.deallocate(l0.addr()) };
            BlockPtr::default()
        } else {
            self.sync_block(l0)?
        };

        l1.data_mut().set_branch_full(i1, false);
        l1.data_mut().ptrs[i1] = l0_ptr;
        let l1_ptr = if l1.data().tree_list_is_empty() {
            unsafe { self.deallocate(l1.addr()) };
            BlockPtr::default()
        } else {
            self.sync_block(l1)?
        };

        l2.data_mut().set_branch_full(i2, false);
        l2.data_mut().ptrs[i2] = l1_ptr;
        let l2_ptr = if l2.data().tree_list_is_empty() {
            unsafe { self.deallocate(l2.addr()) };
            BlockPtr::default()
        } else {
            self.sync_block(l2)?
        };

        l3.data_mut().set_branch_full(i3, false);
        l3.data_mut().ptrs[i3] = l2_ptr;
        let l3_ptr = if l3.data().tree_list_is_empty() {
            unsafe { self.deallocate(l3.addr()) };
            BlockPtr::default()
        } else {
            self.sync_block(l3)?
        };

        self.header.tree = l3_ptr;
        self.header_changed = true;
        Ok(())
    }

    pub fn sync_trees<T: Deref<Target = [u8]>>(&mut self, nodes: &[TreeData<T>]) -> Result<()> {
        for node in nodes.iter().rev() {
            let ptr = node.ptr();
            if ptr.is_null() {
                // ID is invalid
                #[cfg(feature = "log")]
                log::error!("SYNC_TREE: ID IS NULL");
                return Err(Error::new(ENOENT));
            }
        }

        for node in nodes.iter().rev() {
            let arc = self.fs.inode_to_block_id.clone();
            let lock = arc.read().unwrap();
            println!("get: {}", node.id());

            if let Some(&block_ptr) = lock.get(&node.id()) {
                let mut raw = self.read_block(block_ptr)?;
                if raw.data().deref() == node.data().deref() {
                    continue;
                }
                raw.data_mut().copy_from_slice(node.data().deref());
                unsafe { self.write_block(raw)?; }
            } else {
                panic!("SYNC_TREES: cache miss:{}", node.id());
            }
        }

        Ok(())
    }

    pub fn sync_tree<T: Deref<Target = [u8]>>(&mut self, node: TreeData<T>) -> Result<()> {
        self.sync_trees(&[node])
    }

    //
    // MARK: node operations
    //

    /// Write all children of `parent_ptr` to `children`.
    /// `parent_ptr` must point to a directory node.
    pub fn child_nodes(
        &mut self,
        parent_ptr: TreePtr<Node>,
        children: &mut Vec<DirEntry>,
    ) -> Result<()> {
        let parent = self.read_tree(parent_ptr)?;
        if parent.data().level0[0].is_marker() {
            let htree_levels = parent.data().level0[0].addr().level().0;
            let htree_root = if htree_levels == 0 {
                // Create a fake root to satisfy the recursive child_nodes_inner function signature
                let mut fake_htree_node =
                    BlockData::<HTreeNode<RecordRaw>>::empty(BlockAddr::default()).unwrap();
                let dir_ptr = parent.data().level0[1];
                let htree_ptr = HTreePtr::new(HTreeHash::MAX, dir_ptr);
                fake_htree_node.data_mut().ptrs[0] = htree_ptr;
                fake_htree_node
            } else {
                let htree_record_ptr = parent.data().level0[1];
                let htree_ptr: BlockPtr<HTreeNode<RecordRaw>> = unsafe { htree_record_ptr.cast() };
                self.read_block(htree_ptr)?
            };
            self.child_nodes_inner(htree_root.data(), children, htree_levels.max(1))?;
        }
        Ok(())
    }

    fn child_nodes_inner(
        &mut self,
        htree_node: &HTreeNode<RecordRaw>,
        children: &mut Vec<DirEntry>,
        htree_levels: usize,
    ) -> Result<()> {
        assert!(htree_levels > 0);
        if htree_levels == 1 {
            for entry in htree_node.ptrs.iter().filter(|entry| !entry.is_null()) {
                let dir_ptr: BlockPtr<DirList> = unsafe { entry.ptr.cast() };
                let dir = self.read_block(dir_ptr)?;
                for entry in dir.data().entries() {
                    children.push(entry);
                }
            }
        } else {
            for entry in htree_node.ptrs.iter().filter(|entry| !entry.is_null()) {
                let htree_ptr: BlockPtr<HTreeNode<RecordRaw>> = unsafe { entry.ptr.cast() };
                let htree_node = self.read_block(htree_ptr)?;
                self.child_nodes_inner(htree_node.data(), children, htree_levels - 1)?;
            }
        }

        Ok(())
    }

    /// Find a node that is a child of the `parent_ptr` and is named `name`.
    /// Returns ENOENT if this node is not found.
    pub fn find_node(&mut self, parent_ptr: TreePtr<Node>, name: &str) -> Result<TreeData<Node>> {
        let parent = self.read_tree(parent_ptr)?;
        if !parent.data().level0[0].is_marker() {
            return Err(Error::new(ENOENT));
        }

        let htree_levels = parent.data().level0[0].addr().level().0;

        let root_htree_node = if htree_levels == 0 {
            // Create a fake root to satisfy the recursive inner_find_node function signature
            let mut fake_htree_node =
                BlockData::<HTreeNode<RecordRaw>>::empty(BlockAddr::default()).unwrap();
            let dir_ptr = parent.data().level0[1];
            let htree_ptr = HTreePtr::new(HTreeHash::MAX, dir_ptr);
            fake_htree_node.data_mut().ptrs[0] = htree_ptr;
            fake_htree_node
        } else {
            let root_htree_ptr: BlockPtr<HTreeNode<RecordRaw>> =
                unsafe { parent.data().level0[1].cast() };
            self.read_block(root_htree_ptr)?
        };

        let result = self.find_node_inner(
            root_htree_node.data(),
            name,
            HTreeHash::from_name(name),
            htree_levels.max(1),
        )?;
        result
            .map(|(tree_node, _address)| tree_node)
            .ok_or(Error::new(ENOENT))
    }

    fn find_node_inner(
        &mut self,
        parent_htree_node: &HTreeNode<RecordRaw>,
        name: &str,
        name_hash: HTreeHash,
        htree_levels: usize,
    ) -> Result<Option<(TreeData<Node>, BlockAddr)>> {
        assert!(htree_levels > 0);
        if htree_levels == 1 {
            // If we are at the leaf level, search for the name
            for (_, htree_ptr) in parent_htree_node.find_ptrs_for_read(name_hash) {
                let dir_ptr: BlockPtr<DirList> = unsafe { htree_ptr.ptr.cast() };
                let dir = self.read_block(dir_ptr)?;

                if let Some(entry) = dir.data().find_entry(name) {
                    let node_ptr = entry.node_ptr();
                    return Ok(Some(self.read_tree_and_addr(node_ptr)?));
                }
            }
            #[cfg(feature = "log")]
            log::trace!("FIND_NODE: Node not found in leaf level 1");
            return Ok(None);
        }

        // Otherwise, search the next level of the H-tree
        for (_, entry) in parent_htree_node.find_ptrs_for_read(name_hash) {
            let htree_ptr: BlockPtr<HTreeNode<RecordRaw>> = unsafe { entry.ptr.cast() };
            let htree_node = self.read_block(htree_ptr)?;
            let result =
                self.find_node_inner(htree_node.data(), name, name_hash, htree_levels - 1)?;
            if let Some(node) = result {
                return Ok(Some(node));
            }
        }

        #[cfg(feature = "log")]
        log::trace!(
            "FIND_NODE: Node not found in higher level: {}",
            htree_levels
        );
        Ok(None)
    }

    /// Create a new node in the tree with the given parameters.
    pub fn create_node(
        &mut self,
        parent_ptr: TreePtr<Node>,
        name: &str,
        mode: u16,
        ctime: u64,
        ctime_nsec: u32,
    ) -> Result<TreeData<Node>> {
        self.check_name(&parent_ptr, name)?;

        unsafe {
            let parent = self.read_tree(parent_ptr)?;
            let node_block_data = BlockData::new(
                self.allocate(BlockLevel::default())?,
                Node::new(
                    mode,
                    parent.data().uid(),
                    parent.data().gid(),
                    ctime,
                    ctime_nsec,
                ),
            );
            let node_block_ptr = self.write_block(node_block_data)?;
            let node_ptr = self.insert_tree(node_block_ptr)?;

            self.link_node(parent_ptr, name, node_ptr)?;

            //TODO: do not re-read node
            self.read_tree(node_ptr)
        }
    }

    pub fn link_node(
        &mut self,
        parent_ptr: TreePtr<Node>,
        name: &str,
        node_ptr: TreePtr<Node>,
    ) -> Result<()> {
        let mut parent = self.read_tree(parent_ptr)?;
        let mut node = self.read_tree(node_ptr)?;

        // Increment node reference counter
        let links = node.data().links();
        node.data_mut().set_links(links + 1);

        let dir_entry = DirEntry::new(node_ptr, name);
        let dir_entry_htree_hash = HTreeHash::from_name(name);
        let record_byte_size = parent.data().record_level().bytes();

        // If this is a brand new directory, create the first DirList block
        if !parent.data().level0[0].is_marker() {
            let marker: BlockPtr<RecordRaw> = BlockPtr::marker(0);
            assert!(marker.is_marker());

            parent.data_mut().level0[0] = BlockPtr::marker(0);
            assert!(parent.data().level0[0].is_marker());

            // Create the first DirList block
            let dir = BlockData::<DirList>::empty(BlockAddr::default()).unwrap();
            let dir_ptr = self.sync_block(dir)?;

            // Add the DirList directly to the parent directory
            parent.data_mut().level0[1] = unsafe { dir_ptr.cast() };
            let size = parent.data().size() + record_byte_size;
            parent.data_mut().set_size(size);
        }

        let mut htree_levels = parent.data().level0[0].addr().level().0;

        let mut htree_root = if htree_levels == 0 {
            // If we have no H-tree root, create a fake one to satisfy the recurisve inner_link_node function
            let mut fake_htree_node =
                BlockData::<HTreeNode<RecordRaw>>::empty(BlockAddr::default()).unwrap();
            let dir_ptr = parent.data().level0[1];
            let htree_ptr = HTreePtr::new(HTreeHash::MAX, dir_ptr);
            fake_htree_node.data_mut().ptrs[0] = htree_ptr;
            fake_htree_node
        } else {
            // Otherwise get the real H-tree root
            let htree_root_ptr: BlockPtr<HTreeNode<RecordRaw>> =
                unsafe { parent.data().level0[1].cast() };
            self.read_block(htree_root_ptr)?
        };

        let new_sibling = self.link_node_inner(
            &mut parent,
            htree_root.data_mut(),
            dir_entry,
            dir_entry_htree_hash,
            htree_levels.max(1),
        )?;

        // If we used a fake root, and we grew beyond a single DirList block, we need to create a real root
        if htree_levels == 0 && !htree_root.data().ptrs[1].is_null() {
            htree_levels = 1;
            parent.data_mut().level0[0] = BlockPtr::marker(1);
            let size = parent.data().size() + record_byte_size;
            parent.data_mut().set_size(size);
        }

        // If the H-tree root was split, create a new root to hold the old root as a sibling along with the new sibling
        if let Some((sibling_htree_hash, unallocated_sibling)) = new_sibling {
            assert!(htree_levels > 0);

            // Prep the new sibling H-tree block to be added to the new root
            let mut sibling =
                BlockData::<HTreeNode<RecordRaw>>::empty(BlockAddr::default()).unwrap();
            let _ = mem::replace(sibling.data_mut(), unallocated_sibling);
            let sibling_block_ptr = self.sync_block(sibling)?;
            let sibling_htree_ptr = HTreePtr::new(sibling_htree_hash, sibling_block_ptr);
            let sibling_record_ptr: HTreePtr<RecordRaw> = unsafe { sibling_htree_ptr.cast() };

            // Prep the existing H-tree root to become a sibling
            let root_htree_hash = htree_root
                .data()
                .find_max_htree_hash()
                .ok_or(Error::new(EIO))?;
            let root_block_ptr = self.sync_block(htree_root)?;
            let root_htree_ptr = HTreePtr::new(root_htree_hash, root_block_ptr);
            let root_record_ptr: HTreePtr<RecordRaw> = unsafe { root_htree_ptr.cast() };

            // Create the new root H-tree block
            let mut new_root =
                BlockData::<HTreeNode<RecordRaw>>::empty(BlockAddr::default()).unwrap();
            new_root.data_mut().ptrs[0] = sibling_record_ptr;
            let unexpected_sibling = htree::add_inner_node(new_root.data_mut(), root_record_ptr)?;
            assert!(unexpected_sibling.is_none());
            let new_root_ptr = self.sync_block(new_root)?;

            // Add the parent node pointer, increase the level, and increase one block size per allocated block
            parent.data_mut().level0[0] = BlockPtr::marker(htree_levels as u8 + 1);
            parent.data_mut().level0[1] = unsafe { new_root_ptr.cast() };
            let size = parent.data().size() + 2 * record_byte_size;
            parent.data_mut().set_size(size);
        } else if htree_levels > 0 {
            // Update the parent node with the new root pointer
            let root_block_ptr = self.sync_block(htree_root)?;
            parent.data_mut().level0[1] = unsafe { root_block_ptr.cast() };
        } else {
            // Update the parent with the DirList block, ignoring the fake htree_root
            parent.data_mut().level0[1] = htree_root.data().ptrs[0].ptr;
        }
        self.sync_trees(&[parent, node])?;
        Ok(())
    }

    fn link_node_inner(
        &mut self,
        parent_dir_node: &mut TreeData<Node>,
        parent_htree_node: &mut HTreeNode<RecordRaw>,
        dir_entry: DirEntry,
        dir_entry_htree_hash: HTreeHash,
        htree_levels: usize,
    ) -> Result<Option<(HTreeHash, HTreeNode<RecordRaw>)>> {
        let record_byte_size = parent_dir_node.data().record_level().bytes();

        // Find the entry to update
        let mut htree_ptr = parent_htree_node.ptrs[0];
        let mut htree_ptr_idx = 0;
        for (idx, entry) in parent_htree_node.ptrs.iter().enumerate() {
            if entry.is_null() {
                break;
            }
            htree_ptr = *entry;
            htree_ptr_idx = idx;
            if htree_ptr.htree_hash >= dir_entry_htree_hash {
                break;
            }
        }

        // The recursion terminates by processing the last inner node
        assert!(htree_levels > 0);
        if htree_levels == 1 {
            // Add the entry to the DirList block
            let dir_ptr: BlockPtr<DirList> = unsafe { htree_ptr.ptr.cast() };
            let mut dir = self.read_block(dir_ptr)?;
            let unallocated_sibling =
                htree::add_dir_entry(dir.data_mut(), &mut htree_ptr.htree_hash, dir_entry)?;
            let dir_record_ptr = unsafe { self.sync_block(dir)?.cast() };
            parent_htree_node.ptrs[htree_ptr_idx] =
                HTreePtr::new(htree_ptr.htree_hash, dir_record_ptr);

            if let Some((new_hash, new_unallocated_dir)) = unallocated_sibling {
                // The DirList block was split, so we need to add it to the h-tree
                let mut dir = BlockData::<DirList>::empty(BlockAddr::default()).unwrap();
                let _ = mem::replace(dir.data_mut(), new_unallocated_dir);
                let dir_ptr = self.sync_block(dir)?;
                let dir_htree_ptr = HTreePtr::new(new_hash, dir_ptr);
                let dir_record_ptr: HTreePtr<RecordRaw> = unsafe { dir_htree_ptr.cast() };
                let size = parent_dir_node.data().size() + record_byte_size;
                parent_dir_node.data_mut().set_size(size);

                // We mutate the parent, but let the caller write the parent to disk
                return htree::add_inner_node(parent_htree_node, dir_record_ptr);
            }
            return Ok(None);
        }

        // Recursively insert the entry into the next H-tree level
        let htree_block_ptr: BlockPtr<HTreeNode<RecordRaw>> = unsafe { htree_ptr.ptr.cast() };
        let mut htree_block = self.read_block(htree_block_ptr)?;
        let unallocated_sibling = self.link_node_inner(
            parent_dir_node,
            htree_block.data_mut(),
            dir_entry,
            dir_entry_htree_hash,
            htree_levels - 1,
        )?;

        // Write the muteated H-tree block back to disk and update the parent node's pointer
        let htree_hash = htree_block.data().find_max_htree_hash().unwrap();
        let htree_block_ptr = self.sync_block(htree_block)?;
        let htree_record_ptr: BlockPtr<RecordRaw> = unsafe { htree_block_ptr.cast() };
        parent_htree_node.ptrs[htree_ptr_idx] = HTreePtr::new(htree_hash, htree_record_ptr);

        // If the inner insert function returns a new H-tree sibling block, write it and add it to the parent H-tree node
        if let Some((new_hash, new_unallocated_sibling)) = unallocated_sibling {
            let mut sibling =
                BlockData::<HTreeNode<RecordRaw>>::empty(BlockAddr::default()).unwrap();
            let _ = mem::replace(sibling.data_mut(), new_unallocated_sibling);
            let sibling_ptr = self.sync_block(sibling)?;
            let sibling_htree_ptr = HTreePtr::new(new_hash, sibling_ptr);
            let sibling_record_ptr: HTreePtr<RecordRaw> = unsafe { sibling_htree_ptr.cast() };
            let size = parent_dir_node.data().size() + record_byte_size;
            parent_dir_node.data_mut().set_size(size);

            // We mutate the parent, but let the caller write the parent to disk
            return htree::add_inner_node(parent_htree_node, sibling_record_ptr);
        }

        Ok(None)
    }

    pub fn remove_node(
        &mut self,
        parent_ptr: TreePtr<Node>,
        name: &str,
        mode: u16,
    ) -> Result<Option<u32>> {
        let mut parent = self.read_tree(parent_ptr)?;
        let record_level = parent.data().record_level();
        let records = parent.data().size() / record_level.bytes();
        // error!("remove_node:records:{:?}", records);
        for record_offset in 0..records {
            let mut dir_record_ptr = self.node_record_ptr(&parent, record_offset)?;
            let mut dir_ptr: BlockPtr<DirList> = unsafe { dir_record_ptr.cast() };
            let mut dir = self.read_block(dir_ptr)?;
            let mut node_opt = None;
            for entry in dir.data().entries() {
                let node_ptr = entry.node_ptr();

                // Skip empty entries
                if node_ptr.is_null() {
                    continue;
                }

                // Check if name matches
                if let Some(entry_name) = entry.name() {
                    if entry_name == name {
                        // Read node and test type against requested type
                        let node = self.read_tree(node_ptr)?;
                        if node.data().mode() & Node::MODE_TYPE == mode {
                            if node.data().is_dir()
                                && node.data().size() > 0
                                && node.data().links() == 1
                            {
                                // Tried to remove directory that still has entries
                                return Err(Error::new(ENOTEMPTY));
                            }

                            // Save node and clear entry
                            node_opt = Some(node);
                            dir.data_mut().remove_entry(entry_name);
                            break;
                        } else if node.data().is_dir() {
                            // Found directory instead of requested type
                            return Err(Error::new(EISDIR));
                        } else {
                            // Did not find directory when requested
                            return Err(Error::new(ENOTDIR));
                        }
                    }
                }
            }

            if let Some(mut node) = node_opt {
                let node_ptr = node.ptr();
                let mut remove = false;
                let links = node.data().links();
                if links > 1 {
                    node.data_mut().set_links(links - 1);
                } else {
                    node.data_mut().set_links(0);
                    self.truncate_node_inner(&mut node, 0)?;
                    remove = true;
                }

                if record_offset == records - 1 && dir.data().is_empty() {
                    let mut remove_record = record_offset;
                    loop {
                        // Remove empty parent record, if it is at the end
                        self.remove_node_record_ptr(&mut parent, remove_record)?;
                        parent
                            .data_mut()
                            .set_size(remove_record * record_level.bytes());

                        // Keep going for any other empty records
                        if remove_record > 0 {
                            remove_record -= 1;
                            dir_record_ptr = self.node_record_ptr(&parent, remove_record)?;
                            dir_ptr = unsafe { dir_record_ptr.cast() };
                            dir = self.read_block(dir_ptr)?;
                            if dir.data().is_empty() {
                                continue;
                            }
                        }
                        break;
                    }
                    self.sync_trees(&[parent, node])?;
                } else {
                    // Save new parent record
                    // dir_ptr = self.sync_block(dir)?;
                    unsafe { self.write_block(dir)?; }
                    // self.sync_trees(&[node])?;
                    // dir_record_ptr = dir_ptr.cast();
                    // self.sync_node_record_ptr(&mut parent, record_offset, dir_record_ptr)?;
                }

                // Sync both parent and node at the same time

                if remove {
                    // Deallocate node if it is no longer linked
                    // let node_addr = self.walk_through_tree(node_ptr)?.addr();
                    let _ = self.fs.treetable.write().unwrap().free(node_ptr.id());
                    let block_ptr =
                        self.fs.inode_to_block_id
                            .write()
                            .unwrap()
                            .remove(&node_ptr.id())
                            .unwrap_or_else(|| panic!("Node not found in INODE2BID"));
                    unsafe { self.deallocate(block_ptr.addr()) };
                    println!("remove: {}", node_ptr.id());
                    return Ok(Some(node_ptr.id()));
                }

                return Ok(None);
            }
        }

        Err(Error::new(ENOENT))
    }

    pub fn rename_node(
        &mut self,
        orig_parent_ptr: TreePtr<Node>,
        orig_name: &str,
        new_parent_ptr: TreePtr<Node>,
        new_name: &str,
    ) -> Result<()> {
        let orig = self.find_node(orig_parent_ptr, orig_name)?;

        // TODO: only allow ENOENT as an error?
        if let Ok(new) = self.find_node(new_parent_ptr, new_name) {
            // Move to same name, return
            if new.id() == orig.id() {
                return Ok(());
            }

            // Remove new name
            // (we renamed to a node that already exists, overwrite it.)
            self.remove_node(
                new_parent_ptr,
                new_name,
                new.data().mode() & Node::MODE_TYPE,
            )?;
        }

        // Link original file to new name
        self.check_name(&new_parent_ptr, new_name)?;
        self.link_node(new_parent_ptr, new_name, orig.ptr())?;

        // Remove original file
        self.remove_node(
            orig_parent_ptr,
            orig_name,
            orig.data().mode() & Node::MODE_TYPE,
        )?;

        Ok(())
    }

    fn check_name(&mut self, parent_ptr: &TreePtr<Node>, name: &str) -> Result<()> {
        if name.contains(':') {
            return Err(Error::new(EINVAL));
        }

        if name.len() > DIR_ENTRY_MAX_LENGTH {
            return Err(Error::new(EINVAL));
        }

        // TODO: Can this be removed if link_node satisfies this check itself?
        if self.find_node(*parent_ptr, name).is_ok() {
            return Err(Error::new(EEXIST));
        }

        Ok(())
    }

    /// Get a pointer to a the record of `node` with the given offset.
    /// (i.e, to the `n`th record of `node`.)
    fn node_record_ptr(
        &mut self,
        node: &TreeData<Node>,
        record_offset: u64,
    ) -> Result<BlockPtr<RecordRaw>> {
        unsafe {
            match NodeLevel::new(record_offset).ok_or(Error::new(ERANGE))? {
                NodeLevel::L0(i0) => Ok(node.data().level0[i0]),
                NodeLevel::L1(i1, i0) => {
                    let l0 = self.read_block_or_empty(node.data().level1[i1])?;
                    Ok(l0.data().ptrs[i0])
                }
                NodeLevel::L2(i2, i1, i0) => {
                    let l1 = self.read_block_or_empty(node.data().level2[i2])?;
                    let l0 = self.read_block_or_empty(l1.data().ptrs[i1])?;
                    Ok(l0.data().ptrs[i0])
                }
                NodeLevel::L3(i3, i2, i1, i0) => {
                    let l2 = self.read_block_or_empty(node.data().level3[i3])?;
                    let l1 = self.read_block_or_empty(l2.data().ptrs[i2])?;
                    let l0 = self.read_block_or_empty(l1.data().ptrs[i1])?;
                    Ok(l0.data().ptrs[i0])
                }
                NodeLevel::L4(i4, i3, i2, i1, i0) => {
                    let l3 = self.read_block_or_empty(node.data().level4[i4])?;
                    let l2 = self.read_block_or_empty(l3.data().ptrs[i3])?;
                    let l1 = self.read_block_or_empty(l2.data().ptrs[i2])?;
                    let l0 = self.read_block_or_empty(l1.data().ptrs[i1])?;
                    Ok(l0.data().ptrs[i0])
                }
            }
        }
    }

    fn remove_node_record_ptr(
        &mut self,
        node: &mut TreeData<Node>,
        record_offset: u64,
    ) -> Result<()> {
        unsafe {
            match NodeLevel::new(record_offset).ok_or(Error::new(ERANGE))? {
                NodeLevel::L0(i0) => {
                    self.deallocate_block(node.data_mut().level0[i0].clear());
                }
                NodeLevel::L1(i1, i0) => {
                    let mut l0 = self.read_block_or_empty(node.data().level1[i1])?;
                    self.deallocate_block(l0.data_mut().ptrs[i0].clear());
                    if l0.data().is_empty() {
                        self.deallocate_block(node.data_mut().level1[i1].clear());
                    } else {
                        node.data_mut().level1[i1] = self.sync_block(l0)?;
                    }
                }
                NodeLevel::L2(i2, i1, i0) => {
                    let mut l1 = self.read_block_or_empty(node.data().level2[i2])?;
                    let mut l0 = self.read_block_or_empty(l1.data().ptrs[i1])?;
                    self.deallocate_block(l0.data_mut().ptrs[i0].clear());
                    if l0.data().is_empty() {
                        self.deallocate_block(l1.data_mut().ptrs[i1].clear());
                    } else {
                        l1.data_mut().ptrs[i1] = self.sync_block(l0)?;
                    }
                    if l1.data().is_empty() {
                        self.deallocate_block(node.data_mut().level2[i2].clear());
                    } else {
                        node.data_mut().level2[i2] = self.sync_block(l1)?;
                    }
                }
                NodeLevel::L3(i3, i2, i1, i0) => {
                    let mut l2 = self.read_block_or_empty(node.data().level3[i3])?;
                    let mut l1 = self.read_block_or_empty(l2.data().ptrs[i2])?;
                    let mut l0 = self.read_block_or_empty(l1.data().ptrs[i1])?;
                    self.deallocate_block(l0.data_mut().ptrs[i0].clear());
                    if l0.data().is_empty() {
                        self.deallocate_block(l1.data_mut().ptrs[i1].clear());
                    } else {
                        l1.data_mut().ptrs[i1] = self.sync_block(l0)?;
                    }
                    if l1.data().is_empty() {
                        self.deallocate_block(l2.data_mut().ptrs[i2].clear());
                    } else {
                        l2.data_mut().ptrs[i2] = self.sync_block(l1)?;
                    }
                    if l2.data().is_empty() {
                        self.deallocate_block(node.data_mut().level3[i3].clear());
                    } else {
                        node.data_mut().level3[i3] = self.sync_block(l2)?;
                    }
                }
                NodeLevel::L4(i4, i3, i2, i1, i0) => {
                    let mut l3 = self.read_block_or_empty(node.data().level4[i4])?;
                    let mut l2 = self.read_block_or_empty(l3.data().ptrs[i3])?;
                    let mut l1 = self.read_block_or_empty(l2.data().ptrs[i2])?;
                    let mut l0 = self.read_block_or_empty(l1.data().ptrs[i1])?;
                    self.deallocate_block(l0.data_mut().ptrs[i0].clear());
                    if l0.data().is_empty() {
                        self.deallocate_block(l1.data_mut().ptrs[i1].clear());
                    } else {
                        l1.data_mut().ptrs[i1] = self.sync_block(l0)?;
                    }
                    if l1.data().is_empty() {
                        self.deallocate_block(l2.data_mut().ptrs[i2].clear());
                    } else {
                        l2.data_mut().ptrs[i2] = self.sync_block(l1)?;
                    }
                    if l2.data().is_empty() {
                        self.deallocate_block(l3.data_mut().ptrs[i3].clear());
                    } else {
                        l3.data_mut().ptrs[i3] = self.sync_block(l2)?;
                    }
                    if l3.data().is_empty() {
                        self.deallocate_block(node.data_mut().level4[i4].clear());
                    } else {
                        node.data_mut().level4[i4] = self.sync_block(l3)?;
                    }
                }
            }

            Ok(())
        }
    }

    /// Set the record at `ptr` as the data at `record_offset` of `node`.
    fn sync_node_record_ptr(
        &mut self,
        node: &mut TreeData<Node>,
        record_offset: u64,
        ptr: BlockPtr<RecordRaw>,
    ) -> Result<()> {
        unsafe {
            match NodeLevel::new(record_offset).ok_or(Error::new(ERANGE))? {
                NodeLevel::L0(i0) => {
                    node.data_mut().level0[i0] = ptr;
                }
                NodeLevel::L1(i1, i0) => {
                    let mut l0 = self.read_block_or_empty(node.data().level1[i1])?;

                    l0.data_mut().ptrs[i0] = ptr;
                    node.data_mut().level1[i1] = self.sync_block(l0)?;
                }
                NodeLevel::L2(i2, i1, i0) => {
                    let mut l1 = self.read_block_or_empty(node.data().level2[i2])?;
                    let mut l0 = self.read_block_or_empty(l1.data().ptrs[i1])?;

                    l0.data_mut().ptrs[i0] = ptr;
                    l1.data_mut().ptrs[i1] = self.sync_block(l0)?;
                    node.data_mut().level2[i2] = self.sync_block(l1)?;
                }
                NodeLevel::L3(i3, i2, i1, i0) => {
                    let mut l2 = self.read_block_or_empty(node.data().level3[i3])?;
                    let mut l1 = self.read_block_or_empty(l2.data().ptrs[i2])?;
                    let mut l0 = self.read_block_or_empty(l1.data().ptrs[i1])?;

                    l0.data_mut().ptrs[i0] = ptr;
                    l1.data_mut().ptrs[i1] = self.sync_block(l0)?;
                    l2.data_mut().ptrs[i2] = self.sync_block(l1)?;
                    node.data_mut().level3[i3] = self.sync_block(l2)?;
                }
                NodeLevel::L4(i4, i3, i2, i1, i0) => {
                    let mut l3 = self.read_block_or_empty(node.data().level4[i4])?;
                    let mut l2 = self.read_block_or_empty(l3.data().ptrs[i3])?;
                    let mut l1 = self.read_block_or_empty(l2.data().ptrs[i2])?;
                    let mut l0 = self.read_block_or_empty(l1.data().ptrs[i1])?;

                    l0.data_mut().ptrs[i0] = ptr;
                    l1.data_mut().ptrs[i1] = self.sync_block(l0)?;
                    l2.data_mut().ptrs[i2] = self.sync_block(l1)?;
                    l3.data_mut().ptrs[i3] = self.sync_block(l2)?;
                    node.data_mut().level4[i4] = self.sync_block(l3)?;
                }
            }
        }

        Ok(())
    }

    pub fn read_node_inner(
        &mut self,
        node: &TreeData<Node>,
        mut offset: u64,
        buf: &mut [u8],
    ) -> Result<usize> {
        let node_size = node.data().size();
        let record_level = node.data().record_level();

        let mut bytes_read = 0;
        while bytes_read < buf.len() && offset < node_size {
            // How many bytes we've read into the next record
            let j = (offset % record_level.bytes()) as usize;

            // Number of bytes to read in this iteration
            let len = min(
                buf.len() - bytes_read, // number of bytes we have left in `buf`
                min(
                    record_level.bytes() - j as u64, // number of bytes we haven't read in this record
                    node_size - offset,              // number of bytes left in this node
                ) as usize,
            );

            let record_idx = offset / record_level.bytes();
            let record_ptr = self.node_record_ptr(node, record_idx)?;

            // The level of the record to read.
            // This is at most `record_level` due to the way `len` is computed.
            let level = BlockLevel::for_bytes((j + len) as u64);

            let record = unsafe { self.read_record(record_ptr, level)? };
            buf[bytes_read..bytes_read + len].copy_from_slice(&record.data()[j..j + len]);

            bytes_read += len;
            offset += len as u64;
        }
        Ok(bytes_read)
    }

    pub fn read_node(
        &mut self,
        node_ptr: TreePtr<Node>,
        offset: u64,
        buf: &mut [u8],
        atime: u64,
        atime_nsec: u32,
    ) -> Result<usize> {
        let mut node = self.read_tree(node_ptr)?;
        let mut node_changed = false;

        let i = self.read_node_inner(&node, offset, buf)?;
        if i > 0 {
            let node_atime = node.data().atime();
            if atime > node_atime.0 || (atime == node_atime.0 && atime_nsec > node_atime.1) {
                let is_old = atime - node_atime.0 > 3600; // Last read was more than a day ago
                if is_old {
                    node.data_mut().set_atime(atime, atime_nsec);
                    node_changed = true;
                }
            }
        }

        if node_changed {
            self.sync_tree(node)?;
        }

        Ok(i)
    }

    pub fn truncate_node_inner(&mut self, node: &mut TreeData<Node>, size: u64) -> Result<bool> {
        let old_size = node.data().size();
        let record_level = node.data().record_level();

        // Size already matches, return
        if old_size == size {
            return Ok(false);
        }

        if old_size < size {
            // If we're "truncating" to a larger size,
            // write zeroes until the size matches
            let zeroes = RecordRaw::empty(record_level).unwrap();

            let mut offset = old_size;
            while offset < size {
                let start = offset % record_level.bytes();
                if start == 0 {
                    // We don't have to write completely zero records as read will interpret
                    // null record pointers as zero records
                    offset = size;
                    break;
                }
                let end = if offset / record_level.bytes() == size / record_level.bytes() {
                    size % record_level.bytes()
                } else {
                    record_level.bytes()
                };
                self.write_node_inner(node, &mut offset, &zeroes[start as usize..end as usize])?;
            }
            assert_eq!(offset, size);
        } else {
            // Deallocate records
            for record in
                (size.div_ceil(record_level.bytes())..old_size / record_level.bytes()).rev()
            {
                self.remove_node_record_ptr(node, record)?;
            }
        }

        // Update size
        node.data_mut().set_size(size);

        Ok(true)
    }

    /// Truncate the given node to the given size.
    ///
    /// If `size` is larger than the node's current size,
    /// expand the node with zeroes.
    pub fn truncate_node(
        &mut self,
        node_ptr: TreePtr<Node>,
        size: u64,
        mtime: u64,
        mtime_nsec: u32,
    ) -> Result<()> {
        let mut node = self.read_tree(node_ptr)?;
        if self.truncate_node_inner(&mut node, size)? {
            let node_mtime = node.data().mtime();
            if mtime > node_mtime.0 || (mtime == node_mtime.0 && mtime_nsec > node_mtime.1) {
                node.data_mut().set_mtime(mtime, mtime_nsec);
            }

            self.sync_tree(node)?;
        }

        Ok(())
    }

    pub fn write_node_inner(
        &mut self,
        node: &mut TreeData<Node>,
        offset: &mut u64,
        buf: &[u8],
    ) -> Result<bool> {
        let mut node_changed = false;

        let record_level = node.data().record_level();
        let node_records = node.data().size().div_ceil(record_level.bytes());

        let mut i = 0;
        while i < buf.len() {
            let j = (*offset % record_level.bytes()) as usize;
            let len = min(buf.len() - i, record_level.bytes() as usize - j);
            let level = BlockLevel::for_bytes((j + len) as u64);

            let mut record_ptr = if node_records > (*offset / record_level.bytes()) {
                self.node_record_ptr(node, *offset / record_level.bytes())?
            } else {
                BlockPtr::null(level)
            };
            let mut record = unsafe { self.read_record(record_ptr, level)? };

            if buf[i..i + len] != record.data()[j..j + len] {
                unsafe {
                    // CoW record using its current level
                    let mut old_addr = record.swap_addr(self.allocate(record.addr().level())?);

                    // If the record was resized we need to dealloc the original ptr
                    if old_addr.is_null() {
                        old_addr = record_ptr.addr();
                    }

                    record.data_mut()[j..j + len].copy_from_slice(&buf[i..i + len]);
                    record_ptr = self.write_block(record)?;

                    if !old_addr.is_null() {
                        self.deallocate(old_addr);
                    }
                }

                self.sync_node_record_ptr(node, *offset / record_level.bytes(), record_ptr)?;
                node_changed = true;
            }

            i += len;
            *offset += len as u64;
        }

        if node.data().size() < *offset {
            node.data_mut().set_size(*offset);
            node_changed = true;
        }

        Ok(node_changed)
    }

    /// Write the bytes at `buf` to `node` starting at `offset`.
    pub fn write_node(
        &mut self,
        node_ptr: TreePtr<Node>,
        mut offset: u64,
        buf: &[u8],
        mtime: u64,
        mtime_nsec: u32,
    ) -> Result<usize> {
        let mut node = self.read_tree(node_ptr)?;

        if self.write_node_inner(&mut node, &mut offset, buf)? {
            let node_mtime = node.data().mtime();
            if mtime > node_mtime.0 || (mtime == node_mtime.0 && mtime_nsec > node_mtime.1) {
                node.data_mut().set_mtime(mtime, mtime_nsec);
            }

            self.sync_tree(node)?;
        }

        Ok(buf.len())
    }
}
