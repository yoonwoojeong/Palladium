//! Arbitrary precision natural numbers (placeholder; replaced by the real implementation).
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct BigNat(u64);
impl BigNat {
    pub fn zero() -> Self { BigNat(0) }
    pub fn from_u64(x: u64) -> Self { BigNat(x) }
    pub fn to_u64(&self) -> Option<u64> { Some(self.0) }
    pub fn is_zero(&self) -> bool { self.0 == 0 }
}
