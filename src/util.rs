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
