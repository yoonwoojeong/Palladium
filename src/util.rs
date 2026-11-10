//! Small utilities: a fast non-cryptographic hasher and a 64-bit mixing function.

use std::hash::{BuildHasherDefault, Hasher};

/// The classic "Fx" multiply-rotate hasher (as used in rustc).
#[derive(Default, Clone, Copy)]
pub struct FxHasher {
    hash: u64,
}

const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;

impl FxHasher {
    #[inline]
    fn add(&mut self, w: u64) {
        self.hash = (self.hash.rotate_left(5) ^ w).wrapping_mul(SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for c in &mut chunks {
            self.add(u64::from_le_bytes(c.try_into().unwrap()));
        }
        let rem = chunks.remainder();
        if !rem.is_empty() {
            let mut buf = [0u8; 8];
            buf[..rem.len()].copy_from_slice(rem);
            self.add(u64::from_le_bytes(buf));
        }
    }
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u16(&mut self, i: u16) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.hash.rotate_left(26)
    }
}

pub type FxBuild = BuildHasherDefault<FxHasher>;
pub type FxHashMap<K, V> = std::collections::HashMap<K, V, FxBuild>;
pub type FxHashSet<K> = std::collections::HashSet<K, FxBuild>;

/// Map from dense ids (all >= 1, as `TermId`s are) to ids. Each slot stores its generation
/// with the value, and a slot is live only when its generation is the current one, so `clear`
/// is O(1) and keeps the allocation: clearing must not zero the (possibly multi-million entry)
/// table, and growing after a clear must not re-zero the prefix.
#[derive(Default)]
pub struct DenseMap {
    v: Vec<(u32, u32)>,
    gen: u32,
}

impl DenseMap {
    #[inline]
    pub fn get(&self, k: u32) -> Option<u32> {
        match self.v.get(k as usize) {
            Some(&(g, x)) if g == self.gen && x != 0 => Some(x),
            _ => None,
        }
    }

    #[inline]
    pub fn insert(&mut self, k: u32, val: u32) {
        let i = k as usize;
        if i >= self.v.len() {
            let n = (i + 1).max(self.v.len() * 2);
            self.v.resize(n, (0, 0));
        }
        self.v[i] = (self.gen, val);
    }

    pub fn clear(&mut self) {
        self.gen = self.gen.wrapping_add(1);
        if self.gen == 0 {
            self.v.fill((0, 0));
            self.gen = 1;
        }
    }
}

/// Hashed map `u32 -> u32` with O(1) logical clear and memory proportional to the number of
/// live entries (not to the key range). Used for the import memo, whose keys range over the
/// whole file (tens of millions of expressions) while one checking run touches a few thousand
/// per declaration: a dense table would be re-zeroed on every reset.
/// Slots are `(key, generation, value)`; a slot is occupied only when its generation is current.
pub struct GenMap {
    slots: Vec<(u32, u32, u32)>,
    gen: u32,
    len: usize,
}

impl Default for GenMap {
    fn default() -> Self {
        GenMap { slots: vec![(0, 0, 0); 1 << 12], gen: 1, len: 0 }
    }
}

impl GenMap {
    #[inline]
    fn start(key: u32, mask: usize) -> usize {
        ((key as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 32) as usize & mask
    }

    #[inline]
    pub fn get(&self, key: u32) -> Option<u32> {
        let mask = self.slots.len() - 1;
        let mut i = Self::start(key, mask);
        loop {
            let (k, g, v) = self.slots[i];
            if g != self.gen {
                return None;
            }
            if k == key {
                return Some(v);
            }
            i = (i + 1) & mask;
        }
    }

    #[inline]
    pub fn insert(&mut self, key: u32, val: u32) {
        if (self.len + 1) * 2 > self.slots.len() {
            let old = std::mem::replace(&mut self.slots, vec![(0, 0, 0); 0]);
            let cap = old.len() * 2;
            self.slots = vec![(0, 0, 0); cap];
            let gen = self.gen;
            let mask = cap - 1;
            for (k, g, v) in old {
                if g == gen {
                    let mut i = Self::start(k, mask);
                    while self.slots[i].1 == gen {
                        i = (i + 1) & mask;
                    }
                    self.slots[i] = (k, gen, v);
                }
            }
        }
        let mask = self.slots.len() - 1;
        let gen = self.gen;
        let mut i = Self::start(key, mask);
        loop {
            let (k, g, _) = self.slots[i];
            if g != gen {
                self.slots[i] = (key, gen, val);
                self.len += 1;
                return;
            }
            if k == key {
                self.slots[i] = (key, gen, val);
                return;
            }
            i = (i + 1) & mask;
        }
    }

    /// Drops every entry in O(1); the table is zeroed only when the generation wraps.
    pub fn clear(&mut self) {
        self.len = 0;
        self.gen = self.gen.wrapping_add(1);
        if self.gen == 0 {
            self.slots.fill((0, 0, 0));
            self.gen = 1;
        }
    }
}

/// A good 64-bit mixing function of two words (used for hash-consing).
#[inline]
pub fn mix(a: u64, b: u64) -> u64 {
    let x = (a ^ b.rotate_left(32)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    let y = (b ^ x).wrapping_mul(0xC2B2_AE3D_27D4_EB4F);
    y ^ (y >> 32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mix_spreads_low_bits() {
        // Consecutive inputs must not collide in the low 16 bits.
        let mut seen = FxHashSet::default();
        for i in 0..10_000u64 {
            seen.insert(mix(i, 7) & 0xFFFF);
        }
        assert!(seen.len() > 9_000, "only {} distinct low-16 values", seen.len());
    }

    #[test]
    fn fx_map_works() {
        let mut m: FxHashMap<u64, u32> = FxHashMap::default();
        for i in 0..1000u64 {
            m.insert(i * 31, i as u32);
        }
        assert_eq!(m.get(&(31 * 500)), Some(&500));
        assert_eq!(m.get(&1), None);
    }
}
