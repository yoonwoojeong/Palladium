//! Arbitrary precision natural numbers (placeholder; replaced by the real implementation).
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct BigNat(u64);
impl BigNat {
    pub fn zero() -> Self { BigNat(0) }
    pub fn from_u64(x: u64) -> Self { BigNat(x) }
    pub fn to_u64(&self) -> Option<u64> { Some(self.0) }
    pub fn is_zero(&self) -> bool { self.0 == 0 }
    /// Placeholder: decimal digits only, values below 2^64 (the real bignum replaces this file).
    pub fn from_decimal(s: &[u8]) -> Option<BigNat> {
        if s.is_empty() { return None; }
        let mut v: u64 = 0;
        for &b in s {
            if !b.is_ascii_digit() { return None; }
            v = v.checked_mul(10)?.checked_add((b - b'0') as u64)?;
        }
        Some(BigNat(v))
    }
}
