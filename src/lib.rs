#![feature(build_hasher_simple_hash_one)]

use std::{
    collections::{
        hash_map::{DefaultHasher, Entry},
        HashMap, VecDeque,
    },
    hash::{BuildHasher, BuildHasherDefault, Hash},
};

use nohash_hasher::IntMap;

#[derive(Default)]
struct LruCacheQueue(VecDeque<usize>);

impl LruCacheQueue {
    /// Pushes a new element to the back of the queue.
    pub fn push(&mut self, val: usize) {
        self.0.push_back(val);
    }

    /// Moves the given element to the back of the queue.
    ///
    /// # Returns
    /// Whether the element was found and moved to the back of the queue.
    pub fn refresh(&mut self, value: usize) -> bool {
        match self.0.iter().position(|&x| x == value) {
            None => false,
            Some(pos) => {
                let items_index = self.0.remove(pos).unwrap();
                self.0.push_back(items_index);
                debug_assert_eq!(items_index, value);
                true
            },
        }
    }

    /// Moves the least recently used element to the back of the queue.
    ///
    /// # Returns
    /// Returns the index of the element that was moved, or `None` if the queue is empty.
    pub fn rotate(&mut self) -> Option<usize> {
        self.0.rotate_left(1);
        self.0.back().copied()
    }

    /// Returns the queue as a slice.
    pub fn as_slice(&mut self) -> &[usize] {
        self.0.make_contiguous()
    }
}

/// An LRU cache that holds a fixed number of items.
/// If the cache is full, the least recently used item is dropped.
///
/// <p style="background:rgba(255,181,77,0.16);padding:0.75em;">
/// <strong>Warning:</strong> If multiple keys with colliding hashes are used they will be treated as the same key.
/// </p>
///
/// # Examples
/// ```
/// use lor_lru::LruCache;
/// let mut cache = LruCache::new(3);
///
/// cache.insert("foo");                         //  , ,  ->  , ,0
/// cache.insert("bar");                         //  , ,0 ->  ,0,1
/// cache.insert("baz");                         //  ,0,1 -> 0,1,2
/// assert_eq!(cache.get_key(0), Some(&"foo"));  // 0,1,2 -> 1,2,0
/// assert_eq!(cache.get_key(1), Some(&"bar"));  // 1,2,0 -> 2,0,1
/// assert_eq!(cache.get_key(2), Some(&"baz"));  // 2,0,1 -> 0,1,2
/// assert_eq!(cache.get_key(3), None);          // 3 out of range - no change
///
/// cache.insert("qux");                         // 0,1,2 -> 1,2,0 - 0 is replaced
/// assert_eq!(cache.get_key(0), Some(&"qux"));  // 0 already last - no change
///
/// cache.use_slot(1);                           // 1,2,0 -> 2,0,1
/// cache.insert("quux");                        // 2,0,1 -> 0,1,2 - 2 is replaced
/// assert_eq!(cache.get_key(2), Some(&"quux")); // 2 already last - no change
/// ```
pub struct LruCache<K: Hash, S = BuildHasherDefault<DefaultHasher>> {
    capacity: usize,

    queue: LruCacheQueue,
    dedup: IntMap<u64, usize>,
    items: Vec<K>,

    hash_builder: S,
}

impl<K: Hash> LruCache<K> {
    /// Creates a new  instance of `LruCache` with the given capacity.
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0);

        Self {
            capacity,

            dedup: HashMap::default(),
            queue: LruCacheQueue::default(),
            items: Vec::default(),

            hash_builder: BuildHasherDefault::default(),
        }
    }
}

impl<K: Hash, S: BuildHasher> LruCache<K, S> {
    /// Returns the key currently in requested slot.
    ///
    /// This counts as using the key.
    pub fn get_key(&mut self, slot: usize) -> Option<&K> {
        self.items.get(slot).map(|key| {
            assert!(self.queue.refresh(slot));
            key
        })
    }

    /// Returns the slot a key is in.
    ///
    /// This counts as using the key.
    pub fn get_slot(&mut self, key: &K) -> Option<usize> {
        self.dedup.get(&self.hash_builder.hash_one(key)).map(|&slot| {
            assert!(self.queue.refresh(slot));
            slot
        })
    }

    /// Returns `true` if the cache contains the provided key.
    pub fn contains_key(&self, key: &K) -> bool {
        self.dedup.contains_key(&self.hash_builder.hash_one(key))
    }

    /// Inserts a key into the cache.
    ///
    /// # Returns
    /// The slot the key was placed in, or `Err(key)` if the key is already in the cache.
    ///
    /// # Errors
    /// If the key is already present in the cache.
    pub fn insert(&mut self, key: K) -> Result<usize, K> {
        match self.contains_key(&key) {
            true => Err(key),
            false => Ok(self.insert_or_use(key)),
        }
    }

    /// Inserts a key into the cache.
    ///
    /// If the key is already present in the cache, this counts as using the key.
    ///
    /// # Returns
    /// The slot the key was found or placed in.
    pub fn insert_or_use(&mut self, key: K) -> usize {
        let next = self.items.len();

        match self.dedup.entry(self.hash_builder.hash_one(&key)) {
            Entry::Vacant(slot_entry) if next < self.capacity => {
                self.queue.push(next);
                slot_entry.insert(next);
                self.items.push(key);

                next
            },
            Entry::Vacant(slot_entry) => {
                let slot = self.queue.rotate().unwrap();
                slot_entry.insert(slot);

                let old_key = std::mem::replace(&mut self.items[slot], key);
                self.dedup.remove(&self.hash_builder.hash_one(&old_key));

                slot
            },
            Entry::Occupied(entry) => {
                let slot = *entry.get();
                assert!(self.queue.refresh(slot));

                slot
            },
        }
    }

    /// Explicitly use a key.
    ///
    /// # Returns
    /// A boolean indicating whether the key was found and used.
    pub fn use_key(&mut self, key: &K) -> bool {
        self.get_slot(key).is_some()
    }

    /// Explicitly use a slot.
    ///
    /// # Returns
    /// A boolean indicating whether the slot was found and used.
    pub fn use_slot(&mut self, slot: usize) -> bool {
        self.get_key(slot).is_some()
    }

    /// Returns the number of elements in the cache.
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Returns the number of elements the cache can hold.
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Returns `true` if the cache is empty.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Returns `true` if the cache is full.
    pub fn is_full(&self) -> bool {
        self.items.len() == self.capacity
    }

    /// Returns an iterator over the slots in the cache, in order of most to least recently used.
    pub fn iter_slots<'a>(&'a mut self) -> impl Iterator<Item = usize> + 'a {
        #![allow(clippy::needless_lifetimes)] // False positive.

        self.queue.as_slice().iter().rev().copied()
    }

    /// Returns an iterator over the keys in the cache, in order of most to least recently used.
    pub fn iter_keys(&mut self) -> impl Iterator<Item = &K> {
        self.queue.as_slice().iter().rev().map(|&i| &self.items[i])
    }

    /// Returns an iterator over the keys and their slots in the cache, in order of most to least recently used.
    pub fn iter_pairs(&mut self) -> impl Iterator<Item = (usize, &K)> {
        self.queue.as_slice().iter().rev().map(|&i| (i, &self.items[i]))
    }
}

#[test]
fn test_lru_cache() {
    let mut cache = LruCache::<u8>::new(3);

    assert_eq!(cache.get_key(0), None);
    assert_eq!(cache.get_key(1), None);
    assert_eq!(cache.get_key(2), None);

    cache.insert_or_use(11);
    cache.insert_or_use(22);
    cache.insert_or_use(33);

    assert_eq!(cache.get_key(1), Some(&22));
    assert_eq!(cache.get_key(2), Some(&33));
    assert_eq!(cache.get_key(0), Some(&11));

    let slot = cache.insert(44);
    assert_eq!(slot, Ok(1));

    assert_eq!(cache.get_key(1), Some(&44));
}

#[test]
fn test_lru_cache_get_key() {
    let mut cache = LruCache::<u8>::new(3);

    assert_eq!(cache.get_key(0), None);

    let s1 = cache.insert_or_use(11);
    let s2 = cache.insert_or_use(22);

    assert_eq!(cache.get_key(s1), Some(&11));
    assert_eq!(cache.get_key(s2), Some(&22));
}

#[test]
fn test_lru_cache_get_slot() {
    let mut cache = LruCache::<u8>::new(3);

    assert_eq!(None, cache.get_slot(&11));

    assert_eq!(Some(cache.insert_or_use(11)), cache.get_slot(&11));
    assert_eq!(Some(cache.insert_or_use(22)), cache.get_slot(&22));
}

#[test]
fn test_lru_cache_contains_key() {
    let mut cache = LruCache::<u8>::new(3);

    assert!(!cache.contains_key(&11));
    cache.insert_or_use(11);
    assert!(cache.contains_key(&11));
}

#[test]
fn test_lru_cache_insert() {
    let mut cache = LruCache::<u8>::new(3);

    assert_eq!(cache.get_key(0), None);
    assert_eq!(cache.insert(11), Ok(0));
}

#[test]
fn test_lru_cache_insert_duplicate() {
    let mut cache = LruCache::<u8>::new(3);

    assert_eq!(cache.insert(11), Ok(0));
    assert_eq!(cache.insert(11), Err(11));
}

#[test]
fn test_lru_cache_insert_or_use_inserts() {
    let mut cache = LruCache::<u8>::new(3);
    assert_eq!(cache.insert_or_use(11), 0);
    assert_eq!(cache.get_key(0), Some(&11));
}

#[test]
fn test_lru_cache_insert_or_use_uses() {
    let mut cache = LruCache::<u8>::new(3);

    assert_eq!(cache.insert_or_use(11), 0);
    assert_eq!(cache.insert_or_use(22), 1);
    assert_eq!(cache.insert_or_use(11), 0);
    assert_eq!(cache.insert_or_use(33), 2);
}

#[test]
#[should_panic(expected = "assertion failed: capacity > 0")]
fn test_lru_cache_cap_zero() {
    let _ = LruCache::<u8>::new(0);
}

#[test]
fn test_lru_cache_use_key() {
    let mut cache = LruCache::<u8>::new(2);
    assert_eq!(cache.insert_or_use(11), 0);
    assert_eq!(cache.insert_or_use(22), 1);

    assert!(cache.use_key(&11));
    assert_eq!(cache.iter_keys().next(), Some(&11));

    assert!(cache.use_key(&22));
    assert_eq!(cache.iter_keys().next(), Some(&22));
}

#[test]
fn test_lru_cache_use_slot() {
    let mut cache = LruCache::<u8>::new(2);
    assert_eq!(cache.insert_or_use(11), 0);
    assert_eq!(cache.insert_or_use(22), 1);

    assert!(cache.use_slot(0));
    assert_eq!(cache.iter_keys().next(), Some(&11));

    assert!(cache.use_slot(1));
    assert_eq!(cache.iter_keys().next(), Some(&22));
}

#[test]
fn test_lru_cache_use_key_not_found() {
    let mut cache = LruCache::<u8>::new(2);
    assert!(!cache.use_key(&11));
}

#[test]
fn test_lru_cache_use_slot_not_found() {
    let mut cache = LruCache::<u8>::new(2);
    assert!(!cache.use_slot(0));
}

#[test]
fn test_lru_hash_collision() {
    struct LargeHashronCollider(u8);
    impl Hash for LargeHashronCollider {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            0.hash(state);
        }
    }

    let mut cache = LruCache::<LargeHashronCollider>::new(2);

    assert_eq!(cache.insert_or_use(LargeHashronCollider(11)), 0);
    assert_eq!(cache.insert_or_use(LargeHashronCollider(22)), 0);
}
