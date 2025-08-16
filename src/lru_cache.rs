struct Node<K, V> {
    key: K,
    value: V,
    prev: usize,
    next: usize,
}

pub struct LruCache<K, V> {
    pub capacity: usize,
    pub map: std::collections::HashMap<K, usize>,
    nodes: Vec<Node<K, V>>,
    head: usize,
    tail: usize,
    free_indices: Vec<usize>,
}

use alloc::vec::Vec;

impl<K, V> LruCache<K, V>
    where K: Eq + Clone + core::hash::Hash {
    pub fn new(capacity: usize) -> LruCache<K, V> {
        Self {
            nodes: Vec::with_capacity(capacity),
            map: std::collections::HashMap::new(),
            head: usize::MAX,
            tail: usize::MAX,
            capacity,
            free_indices: Vec::with_capacity(capacity),
        }
    }

    pub fn get(&mut self, key: &K) -> Option<&V> {
        let index = *self.map.get(key)?;
        self.move_to_head(index);
        Some(&self.nodes[index].value)
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let index = *self.map.get(key)?;
        self.move_to_head(index);
        Some(&mut self.nodes[index].value)
    }

    pub fn put(&mut self, key: K, value: V) {
        if let Some(index) = self.map.get(&key) {
            self.nodes[*index].value = value;
            self.move_to_head(*index);
            return;
        }

        let new_node = Node {
            key: key.clone(),
            value,
            prev: usize::MAX,
            next: self.head,
        };

        let index = if self.free_indices.is_empty() {
            self.nodes.push(new_node);
            self.nodes.len() - 1
        } else {
            let index = self.free_indices.pop().unwrap();
            self.nodes[index] = new_node;
            index
        };

        if self.head != usize::MAX {
            self.nodes[self.head].prev = index;
        } else {
            self.tail = index;
        }
        self.head = index;

        self.map.insert(key, index);

        if self.map.len() > self.capacity {
            self.remove_tail();
        }
    }

    fn move_to_head(&mut self, index: usize) {
        if index == self.head {
            return;
        }

        let prev = self.nodes[index].prev;
        let next = self.nodes[index].next;

        if prev != usize::MAX {
            self.nodes[prev].next = next;
        }
        if next != usize::MAX {
            self.nodes[next].prev = prev;
        }

        self.nodes[index].prev = usize::MAX;
        self.nodes[index].next = self.head;
        self.nodes[self.head].prev = index;
        self.head = index;

        if index == self.tail {
            self.tail = prev;
        }
    }

    fn remove_tail(&mut self) {
        if self.tail == usize::MAX {
            return;
        }

        let old_tail = self.tail;
        let new_tail = self.nodes[old_tail].prev;

        self.tail = new_tail;
        if new_tail != usize::MAX {
            self.nodes[new_tail].next = usize::MAX;
        } else {
            self.head = usize::MAX;
        }

        let key = &self.nodes[old_tail].key;
        self.map.remove(key);

        self.free_indices.push(old_tail);
    }

    pub fn filter_keys<F>(&self, predicate: F) -> Vec<K>
    where
        K: Clone,
        F: Fn(&V) -> bool,
    {
        self.map
            .iter()
            .filter_map(|(key, &index)| {
                if predicate(&self.nodes[index].value) {
                    Some(key.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn put_quiet(&mut self, key: K, value: V) {
        // 如果键已存在，更新值但不调整位置
        if let Some(index) = self.map.get(&key) {
            self.nodes[*index].value = value;
            return;
        }

        // 容量满时先移除最久未使用的条目
        if self.map.len() >= self.capacity {
            self.remove_tail();
        }

        // 创建新节点并插入链表尾部
        let new_node = Node {
            key: key.clone(),
            value,
            prev: self.tail,
            next: usize::MAX,
        };

        // 获取存储位置
        let index = if self.free_indices.is_empty() {
            self.nodes.push(new_node);
            self.nodes.len() - 1
        } else {
            let index = self.free_indices.pop().unwrap();
            self.nodes[index] = new_node;
            index
        };

        // 更新链表指针
        if self.tail != usize::MAX {
            self.nodes[self.tail].next = index;
        } else {
            self.head = index; // 空链表时初始化头指针
        }
        self.tail = index;

        // 更新哈希表
        self.map.insert(key, index);
    }
}