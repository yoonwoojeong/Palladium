//! Arbitrary precision natural numbers.
//!
//! Canonical representation: values below 2^64 are `Repr::Small` and never allocate.
//! Larger values are `Repr::Big`: little-endian `u64` limbs with a nonzero top limb and
//! at least two limbs. Every operation normalizes its result, so the derived
//! `PartialEq`/`Eq`/`Hash` agree with numeric equality.

use std::cmp::Ordering;

/// Operands at least this many limbs long (on both sides) use Karatsuba multiplication.
const KARATSUBA_MIN: usize = 40;
/// Largest power of ten below 2^64; decimal conversion works in chunks of this size.
const TEN19: u64 = 10_000_000_000_000_000_000;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Repr {
    Small(u64),
    Big(Vec<u64>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct BigNat {
    repr: Repr,
}

impl Default for BigNat {
    fn default() -> Self {
        Self::zero()
    }
}

impl BigNat {
    /// Builds a value from limbs, trimming high zero limbs and choosing the canonical form.
    fn from_limbs(v: Vec<u64>) -> Self {
        let v = trim_vec(v);
        match v.len() {
            0 => Self::zero(),
            1 => Self::from_u64(v[0]),
            _ => BigNat { repr: Repr::Big(v) },
        }
    }

    /// Returns the limbs of `self`. Small values are written into `buf`; the slice may
    /// contain high zero limbs (consumers trim).
    fn limbs<'a>(&'a self, buf: &'a mut [u64; 1]) -> &'a [u64] {
        match &self.repr {
            Repr::Small(x) => {
                buf[0] = *x;
                &buf[..]
            }
            Repr::Big(v) => v.as_slice(),
        }
    }

    /// Applies `f` to the limb slices of `self` and `o`.
    fn limb_pair<R>(&self, o: &Self, f: impl FnOnce(&[u64], &[u64]) -> R) -> R {
        let (mut ba, mut bb) = ([0u64; 1], [0u64; 1]);
        let a = self.limbs(&mut ba);
        let b = o.limbs(&mut bb);
        f(a, b)
    }

    pub fn zero() -> Self {
        BigNat { repr: Repr::Small(0) }
    }

    pub fn from_u64(x: u64) -> Self {
        BigNat { repr: Repr::Small(x) }
    }

    pub fn to_u64(&self) -> Option<u64> {
        match self.repr {
            Repr::Small(x) => Some(x),
            Repr::Big(_) => None,
        }
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.repr, Repr::Small(0))
    }

    /// Parses ASCII decimal digits (at least one; leading zeros allowed).
    pub fn from_decimal(s: &[u8]) -> Option<Self> {
        if s.is_empty() || !s.iter().all(|c| c.is_ascii_digit()) {
            return None;
        }
        let mut limbs: Vec<u64> = Vec::with_capacity(s.len() / 19 * 2 + 2);
        // The first chunk takes the remainder so every later chunk has 19 digits.
        let mut take = match s.len() % 19 {
            0 => 19,
            r => r,
        };
        let mut pos = 0;
        while pos < s.len() {
            let mut val: u64 = 0;
            let mut mul: u64 = 1;
            for &c in &s[pos..pos + take] {
                val = val * 10 + (c - b'0') as u64;
                mul *= 10;
            }
            mul_add_small(&mut limbs, mul, val);
            pos += take;
            take = 19;
        }
        Some(Self::from_limbs(limbs))
    }

    pub fn to_decimal(&self) -> String {
        let mut limbs = match &self.repr {
            Repr::Small(x) => return x.to_string(),
            Repr::Big(v) => v.clone(),
        };
        // Repeated division by 10^19; the remainders are the decimal chunks, low first.
        let mut chunks: Vec<u64> = Vec::with_capacity(limbs.len() * 2);
        while !limbs.is_empty() {
            let mut r: u128 = 0;
            for i in (0..limbs.len()).rev() {
                let cur = (r << 64) | limbs[i] as u128;
                limbs[i] = (cur / TEN19 as u128) as u64;
                r = cur % TEN19 as u128;
            }
            chunks.push(r as u64);
            while limbs.last() == Some(&0) {
                limbs.pop();
            }
        }
        let mut s = String::with_capacity(chunks.len() * 19);
        let mut it = chunks.iter().rev();
        if let Some(top) = it.next() {
            s.push_str(&top.to_string());
        }
        for c in it {
            s.push_str(&format!("{:019}", c));
        }
        s
    }

    /// Number of significant bits; 0 for zero.
    pub fn bit_len(&self) -> u64 {
        match &self.repr {
            Repr::Small(x) => 64 - x.leading_zeros() as u64,
            Repr::Big(v) => {
                let top = v[v.len() - 1];
                64 * (v.len() as u64 - 1) + (64 - top.leading_zeros() as u64)
            }
        }
    }

    pub fn add(&self, o: &Self) -> Self {
        if let (Repr::Small(x), Repr::Small(y)) = (&self.repr, &o.repr) {
            if let Some(s) = x.checked_add(*y) {
                return Self::from_u64(s);
            }
        }
        self.limb_pair(o, |a, b| Self::from_limbs(add_limbs(a, b)))
    }

    /// Truncated subtraction: returns 0 when `o >= self`.
    pub fn sub(&self, o: &Self) -> Self {
        if let (Repr::Small(x), Repr::Small(y)) = (&self.repr, &o.repr) {
            return Self::from_u64(x.saturating_sub(*y));
        }
        if Ord::cmp(self, o) != Ordering::Greater {
            return Self::zero();
        }
        self.limb_pair(o, |a, b| Self::from_limbs(sub_limbs(a, b)))
    }

    pub fn mul(&self, o: &Self) -> Self {
        if let (Repr::Small(x), Repr::Small(y)) = (&self.repr, &o.repr) {
            if let Some(p) = x.checked_mul(*y) {
                return Self::from_u64(p);
            }
        }
        self.limb_pair(o, |a, b| Self::from_limbs(mul_limbs(a, b)))
    }

    /// Quotient and remainder. Lean semantics for a zero divisor: `(0, self)`.
    pub fn div_rem(&self, o: &Self) -> (Self, Self) {
        if o.is_zero() {
            return (Self::zero(), self.clone());
        }
        if let (Repr::Small(x), Repr::Small(y)) = (&self.repr, &o.repr) {
            return (Self::from_u64(*x / *y), Self::from_u64(*x % *y));
        }
        self.limb_pair(o, |a, b| {
            let (q, r) = div_rem_limbs(a, b);
            (Self::from_limbs(q), Self::from_limbs(r))
        })
    }

    /// Quotient; `x / 0 = 0`.
    pub fn div(&self, o: &Self) -> Self {
        self.div_rem(o).0
    }

    /// Remainder; `x % 0 = x`.
    pub fn rem(&self, o: &Self) -> Self {
        self.div_rem(o).1
    }

    /// Greatest common divisor; `gcd(0, y) = y` and `gcd(x, 0) = x`.
    pub fn gcd(&self, o: &Self) -> Self {
        if let (Repr::Small(x), Repr::Small(y)) = (&self.repr, &o.repr) {
            let (mut a, mut b) = (*x, *y);
            while b != 0 {
                let t = a % b;
                a = b;
                b = t;
            }
            return Self::from_u64(a);
        }
        let mut a = self.clone();
        let mut b = o.clone();
        while !b.is_zero() {
            let r = a.rem(&b);
            a = b;
            b = r;
        }
        a
    }

    /// `self^exp` by repeated squaring; `0^0 = 1`.
    pub fn pow(&self, mut exp: u64) -> Self {
        let mut result = Self::from_u64(1);
        if exp == 0 {
            return result;
        }
        let mut base = self.clone();
        loop {
            if exp & 1 == 1 {
                result = result.mul(&base);
            }
            exp >>= 1;
            if exp == 0 {
                break;
            }
            base = base.mul(&base);
        }
        result
    }

    /// Floor of log2; `log2(0) = 0`.
    pub fn log2(&self) -> Self {
        match self.bit_len() {
            0 => Self::zero(),
            n => Self::from_u64(n - 1),
        }
    }

    pub fn and(&self, o: &Self) -> Self {
        if let (Repr::Small(x), Repr::Small(y)) = (&self.repr, &o.repr) {
            return Self::from_u64(x & y);
        }
        self.limb_pair(o, |a, b| {
            let n = a.len().min(b.len());
            Self::from_limbs((0..n).map(|i| a[i] & b[i]).collect())
        })
    }

    pub fn or(&self, o: &Self) -> Self {
        if let (Repr::Small(x), Repr::Small(y)) = (&self.repr, &o.repr) {
            return Self::from_u64(x | y);
        }
        self.limb_pair(o, |a, b| {
            let n = a.len().max(b.len());
            Self::from_limbs((0..n).map(|i| limb_at(a, i) | limb_at(b, i)).collect())
        })
    }

    pub fn xor(&self, o: &Self) -> Self {
        if let (Repr::Small(x), Repr::Small(y)) = (&self.repr, &o.repr) {
            return Self::from_u64(x ^ y);
        }
        self.limb_pair(o, |a, b| {
            let n = a.len().max(b.len());
            Self::from_limbs((0..n).map(|i| limb_at(a, i) ^ limb_at(b, i)).collect())
        })
    }

    /// `self * 2^n`.
    pub fn shl(&self, n: u64) -> Self {
        if n == 0 || self.is_zero() {
            return self.clone();
        }
        if let Repr::Small(x) = self.repr {
            if n < 64 && x.leading_zeros() as u64 >= n {
                return Self::from_u64(x << n);
            }
        }
        let mut buf = [0u64; 1];
        let a = trim(self.limbs(&mut buf));
        let limb_shift = (n / 64) as usize;
        let bit = (n % 64) as u32;
        let mut r = vec![0u64; limb_shift + a.len() + 1];
        if bit == 0 {
            r[limb_shift..limb_shift + a.len()].copy_from_slice(a);
        } else {
            let mut carry = 0u64;
            for (i, &x) in a.iter().enumerate() {
                r[limb_shift + i] = (x << bit) | carry;
                carry = x >> (64 - bit);
            }
            r[limb_shift + a.len()] = carry;
        }
        Self::from_limbs(r)
    }

    /// `floor(self / 2^n)`.
    pub fn shr(&self, n: u64) -> Self {
        if n == 0 {
            return self.clone();
        }
        let v = match &self.repr {
            Repr::Small(x) => return Self::from_u64(if n >= 64 { 0 } else { x >> n }),
            Repr::Big(v) => v,
        };
        let limb_shift = n / 64;
        if limb_shift >= v.len() as u64 {
            return Self::zero();
        }
        let src = &v[limb_shift as usize..];
        let bit = (n % 64) as u32;
        if bit == 0 {
            return Self::from_limbs(src.to_vec());
        }
        let r: Vec<u64> = (0..src.len())
            .map(|i| {
                let hi = if i + 1 < src.len() { src[i + 1] } else { 0 };
                (src[i] >> bit) | (hi << (64 - bit))
            })
            .collect();
        Self::from_limbs(r)
    }

    pub fn succ(&self) -> Self {
        self.add(&Self::from_u64(1))
    }

    /// Predecessor; `pred(0) = 0`.
    pub fn pred(&self) -> Self {
        self.sub(&Self::from_u64(1))
    }
}

impl Ord for BigNat {
    fn cmp(&self, other: &Self) -> Ordering {
        match (&self.repr, &other.repr) {
            (Repr::Small(x), Repr::Small(y)) => x.cmp(y),
            (Repr::Small(_), Repr::Big(_)) => Ordering::Less,
            (Repr::Big(_), Repr::Small(_)) => Ordering::Greater,
            (Repr::Big(x), Repr::Big(y)) => cmp_limbs(x, y),
        }
    }
}

impl PartialOrd for BigNat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(Ord::cmp(self, other))
    }
}

// ---------------------------------------------------------------------------
// Limb-slice helpers. Inputs may carry high zero limbs unless noted.
// ---------------------------------------------------------------------------

fn trim(mut s: &[u64]) -> &[u64] {
    while let Some((&0, rest)) = s.split_last() {
        s = rest;
    }
    s
}

fn trim_vec(mut v: Vec<u64>) -> Vec<u64> {
    while v.last() == Some(&0) {
        v.pop();
    }
    v
}

fn limb_at(s: &[u64], i: usize) -> u64 {
    if i < s.len() {
        s[i]
    } else {
        0
    }
}

fn cmp_limbs(a: &[u64], b: &[u64]) -> Ordering {
    let a = trim(a);
    let b = trim(b);
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    Ordering::Equal
}

/// Sum with result length `max(len) + 1` (top limb may be zero).
fn add_limbs(a: &[u64], b: &[u64]) -> Vec<u64> {
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let mut r = Vec::with_capacity(a.len() + 1);
    let mut carry = false;
    for i in 0..a.len() {
        let (s1, c1) = a[i].overflowing_add(limb_at(b, i));
        let (s2, c2) = s1.overflowing_add(carry as u64);
        r.push(s2);
        carry = c1 | c2;
    }
    r.push(carry as u64);
    r
}

/// Difference of limb slices; requires `a >= b`. Result is trimmed.
fn sub_limbs(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut r = a.to_vec();
    sub_into(&mut r, trim(b));
    trim_vec(r)
}

/// `res -= src` in place; requires `res >= src` (as numbers) and `src.len() <= res.len()`.
fn sub_into(res: &mut [u64], src: &[u64]) {
    debug_assert!(src.len() <= res.len());
    let mut borrow = false;
    for i in 0..src.len() {
        let (d1, o1) = res[i].overflowing_sub(src[i]);
        let (d2, o2) = d1.overflowing_sub(borrow as u64);
        res[i] = d2;
        borrow = o1 | o2;
    }
    let mut k = src.len();
    while borrow {
        let (d, o) = res[k].overflowing_sub(1);
        res[k] = d;
        borrow = o;
        k += 1;
    }
}

/// `res += src << (64 * off)`, carrying into `res`. The sum must fit in `res`.
fn add_at(res: &mut [u64], src: &[u64], off: usize) {
    let mut carry = false;
    for (i, &s) in src.iter().enumerate() {
        let (s1, c1) = res[off + i].overflowing_add(s);
        let (s2, c2) = s1.overflowing_add(carry as u64);
        res[off + i] = s2;
        carry = c1 | c2;
    }
    let mut k = off + src.len();
    while carry {
        let (s, c) = res[k].overflowing_add(1);
        res[k] = s;
        carry = c;
        k += 1;
    }
}

/// `v = v * m + add` in place.
fn mul_add_small(v: &mut Vec<u64>, m: u64, add: u64) {
    let mut carry = add as u128;
    for x in v.iter_mut() {
        let t = *x as u128 * m as u128 + carry;
        *x = t as u64;
        carry = t >> 64;
    }
    if carry != 0 {
        v.push(carry as u64);
    }
}

/// Schoolbook product; result length `a.len() + b.len()`.
fn mul_school(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut r = vec![0u64; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        if x == 0 {
            continue;
        }
        let mut carry: u64 = 0;
        for (j, &y) in b.iter().enumerate() {
            let t = x as u128 * y as u128 + r[i + j] as u128 + carry as u128;
            r[i + j] = t as u64;
            carry = (t >> 64) as u64;
        }
        // Row i is the first to write index i + b.len(), so it was still zero.
        r[i + b.len()] = carry;
    }
    r
}

/// Product with result length `a.len() + b.len()` (value exact, may have high zeros).
fn mul_limbs(a: &[u64], b: &[u64]) -> Vec<u64> {
    let total = a.len() + b.len();
    let a = trim(a);
    let b = trim(b);
    if a.is_empty() || b.is_empty() {
        return vec![0; total];
    }
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    if b.len() < KARATSUBA_MIN {
        let mut r = mul_school(a, b);
        r.resize(total, 0);
        return r;
    }
    if a.len() >= 2 * b.len() {
        // Unbalanced: multiply b against blocks of a of length b.len().
        let mut res = vec![0u64; total];
        for (i, chunk) in a.chunks(b.len()).enumerate() {
            let p = mul_limbs(chunk, b);
            add_at(&mut res, trim(&p), i * b.len());
        }
        return res;
    }
    // Balanced Karatsuba. Here b.len() <= a.len() < 2 b.len(), so m < b.len().
    let m = a.len() / 2;
    let (a0, a1) = a.split_at(m);
    let (b0, b1) = b.split_at(m);
    let z0 = mul_limbs(a0, b0);
    let z2 = mul_limbs(a1, b1);
    let sa = add_limbs(a0, a1);
    let sb = add_limbs(b0, b1);
    let mut z1 = mul_limbs(&sa, &sb);
    sub_into(&mut z1, trim(&z0));
    sub_into(&mut z1, trim(&z2));
    let mut res = vec![0u64; total];
    add_at(&mut res, trim(&z0), 0);
    add_at(&mut res, trim(&z1), m);
    add_at(&mut res, trim(&z2), 2 * m);
    res
}

/// `u << s` for `s < 64`; result length `u.len() + 1`.
fn shl_limbs(u: &[u64], s: u32) -> Vec<u64> {
    let mut r = vec![0u64; u.len() + 1];
    if s == 0 {
        r[..u.len()].copy_from_slice(u);
        return r;
    }
    let mut carry = 0u64;
    for (i, &x) in u.iter().enumerate() {
        r[i] = (x << s) | carry;
        carry = x >> (64 - s);
    }
    r[u.len()] = carry;
    r
}

/// Quotient and remainder by Knuth algorithm D. Requires `v` nonzero.
fn div_rem_limbs(u: &[u64], v: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let u = trim(u);
    let v = trim(v);
    assert!(!v.is_empty(), "bignat: division by zero");
    if cmp_limbs(u, v) == Ordering::Less {
        return (Vec::new(), u.to_vec());
    }
    if v.len() == 1 {
        let d = v[0] as u128;
        let mut q = vec![0u64; u.len()];
        let mut r: u128 = 0;
        for i in (0..u.len()).rev() {
            // r < d, so the quotient digit fits in 64 bits.
            let cur = (r << 64) | u[i] as u128;
            q[i] = (cur / d) as u64;
            r = cur % d;
        }
        return (q, vec![r as u64]);
    }

    let n = v.len();
    let m = u.len() - n;
    // Normalize so the top divisor limb has its high bit set.
    let s = v[n - 1].leading_zeros();
    let vn_full = shl_limbs(v, s);
    let vn = &vn_full[..n];
    let mut un = shl_limbs(u, s); // length u.len() + 1
    let mut q = vec![0u64; m + 1];
    let base: u128 = 1u128 << 64;
    let vtop = vn[n - 1] as u128;
    let vsec = vn[n - 2] as u128;

    for j in (0..=m).rev() {
        let num = ((un[j + n] as u128) << 64) | un[j + n - 1] as u128;
        let mut qhat = num / vtop;
        let mut rhat = num % vtop;
        // Refine the estimate using the next limb. Short-circuiting keeps
        // `qhat * vsec` below 2^128: it is only evaluated once qhat < base.
        while qhat >= base || qhat * vsec > ((rhat << 64) | un[j + n - 2] as u128) {
            qhat -= 1;
            rhat += vtop;
            if rhat >= base {
                break;
            }
        }
        // Multiply and subtract qhat * vn from un[j..=j+n].
        let qh = qhat as u64;
        let mut carry: u64 = 0;
        let mut borrow = false;
        for i in 0..n {
            let p = qh as u128 * vn[i] as u128 + carry as u128;
            carry = (p >> 64) as u64;
            let (t1, o1) = un[i + j].overflowing_sub(p as u64);
            let (t2, o2) = t1.overflowing_sub(borrow as u64);
            un[i + j] = t2;
            borrow = o1 | o2;
        }
        let (t1, o1) = un[j + n].overflowing_sub(carry);
        let (t2, o2) = t1.overflowing_sub(borrow as u64);
        un[j + n] = t2;
        let mut digit = qh;
        if o1 | o2 {
            // The estimate was one too large: add the divisor back.
            digit -= 1;
            let mut c = false;
            for i in 0..n {
                let (s1, c1) = un[i + j].overflowing_add(vn[i]);
                let (s2, c2) = s1.overflowing_add(c as u64);
                un[i + j] = s2;
                c = c1 | c2;
            }
            un[j + n] = un[j + n].wrapping_add(c as u64);
        }
        q[j] = digit;
    }

    // Remainder is un[0..n] shifted back down by s.
    let mut r = vec![0u64; n];
    for i in 0..n {
        r[i] = if s == 0 {
            un[i]
        } else {
            (un[i] >> s) | (un[i + 1] << (64 - s))
        };
    }
    (q, r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    fn n(s: &str) -> BigNat {
        BigNat::from_decimal(s.as_bytes()).expect("valid decimal literal")
    }

    fn small(x: &BigNat) -> u64 {
        x.to_u64().expect("value fits in u64")
    }

    /// Checks the canonical-form invariant that derived Eq/Hash rely on.
    fn canon(x: &BigNat) {
        if let Repr::Big(v) = &x.repr {
            assert!(v.len() >= 2, "Big with fewer than two limbs");
            assert_ne!(*v.last().unwrap(), 0, "Big with zero top limb");
        }
    }

    fn hash_of(x: &BigNat) -> u64 {
        let mut h = DefaultHasher::new();
        x.hash(&mut h);
        h.finish()
    }

    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn below(&mut self, m: u64) -> u64 {
            self.next() % m
        }

        fn limb(&mut self) -> u64 {
            match self.below(8) {
                0 => 0,
                1 => u64::MAX,
                2 => 1,
                3 => 1 << 63,
                _ => self.next(),
            }
        }

        fn limbs_between(&mut self, lo: u64, hi: u64) -> BigNat {
            let k = lo + self.below(hi - lo + 1);
            let v: Vec<u64> = (0..k).map(|_| self.limb()).collect();
            BigNat::from_limbs(v)
        }
    }

    #[test]
    fn edge_cases() {
        let zero = BigNat::zero();
        let one = BigNat::from_u64(1);
        let max = BigNat::from_u64(u64::MAX);
        let two64 = n("18446744073709551616");
        let two128 = n("340282366920938463463374607431768211456");
        let two128m1 = n("340282366920938463463374607431768211455");

        // Zero and parsing.
        assert!(zero.is_zero());
        assert_eq!(zero.to_decimal(), "0");
        assert_eq!(n("000"), zero);
        assert_eq!(n("0007").to_decimal(), "7");
        assert!(BigNat::from_decimal(b"").is_none());
        assert!(BigNat::from_decimal(b"12a").is_none());
        assert!(BigNat::from_decimal(b"+1").is_none());
        assert!(BigNat::from_decimal(b" 1").is_none());
        assert!(BigNat::from_decimal(b"-1").is_none());

        // Boundary values and canonical form.
        assert_eq!(max.to_u64(), Some(u64::MAX));
        assert_eq!(two64.to_u64(), None);
        assert_eq!(two64.sub(&one), max);
        assert_eq!(two64.sub(&one).to_u64(), Some(u64::MAX));
        assert_eq!(max.add(&one), two64);
        assert_eq!(max.succ(), two64);
        assert_eq!(two64.pred().to_u64(), Some(u64::MAX));
        assert_eq!(one.pred(), zero);
        assert_eq!(zero.pred(), zero);
        assert_eq!(two128m1.add(&one), two128);
        assert_eq!(two128.sub(&one), two128m1);
        assert_eq!(two128.to_decimal(), "340282366920938463463374607431768211456");
        assert_eq!(two128m1.to_decimal(), "340282366920938463463374607431768211455");
        assert_eq!(hash_of(&two64.sub(&one)), hash_of(&max));

        // Carries and borrows across limbs.
        let sq = max.mul(&max);
        assert_eq!(sq, n("340282366920938463426481119284349108225"));
        assert_eq!(sq.add(&max).add(&one), two128.sub(&two64).add(&one));
        assert_eq!(two64.sub(&one).add(&one), two64);
        assert_eq!(two128.sub(&one).add(&one), two128);
        assert_eq!(two128.sub(&two64), n("340282366920938463444927863358058659840"));

        // Truncated subtraction.
        assert_eq!(BigNat::from_u64(5).sub(&BigNat::from_u64(7)), zero);
        assert_eq!(two64.sub(&two128), zero);
        assert_eq!(zero.sub(&max), zero);
        assert_eq!(max.sub(&max), zero);

        // Division and remainder, including zero divisors (Lean semantics).
        let seven = BigNat::from_u64(7);
        assert_eq!(seven.div(&zero), zero);
        assert_eq!(seven.rem(&zero), seven);
        assert_eq!(zero.div(&zero), zero);
        assert_eq!(zero.rem(&zero), zero);
        assert_eq!(two128.div_rem(&zero), (zero.clone(), two128.clone()));
        assert_eq!(two128.div(&two64), two64);
        assert_eq!(two128.rem(&two64), zero);
        assert_eq!(two128m1.div(&two64), max);
        assert_eq!(two128m1.rem(&two64), max);
        assert_eq!(two64.div(&max), one);
        assert_eq!(two64.rem(&max), one);
        assert_eq!(max.div(&two64), zero);
        assert_eq!(max.rem(&two64), max);

        // Powers.
        assert_eq!(zero.pow(0), one);
        assert_eq!(max.pow(0), one);
        assert_eq!(zero.pow(5), zero);
        assert_eq!(BigNat::from_u64(2).pow(10), BigNat::from_u64(1024));
        assert_eq!(BigNat::from_u64(2).pow(64), two64);
        assert_eq!(BigNat::from_u64(2).pow(128), two128);
        assert_eq!(max.pow(2), sq);
        assert_eq!(one.pow(1_000_000), one);

        // Shifts.
        assert_eq!(one.shl(0), one);
        assert_eq!(one.shl(63).to_u64(), Some(1 << 63));
        assert_eq!(one.shl(64), two64);
        assert_eq!(one.shl(64).to_u64(), None);
        assert_eq!(one.shl(65), two64.shl(1));
        assert_eq!(one.shl(1000).bit_len(), 1001);
        assert_eq!(one.shl(1000).shr(1000), one);
        assert_eq!(one.shl(64).shr(64), one);
        assert_eq!(one.shl(64).shr(64).to_u64(), Some(1));
        assert_eq!(one.shr(0), one);
        assert_eq!(one.shr(1), zero);
        assert_eq!(one.shr(63), zero);
        assert_eq!(one.shr(64), zero);
        assert_eq!(one.shr(1000), zero);
        assert_eq!(max.shr(63).to_u64(), Some(1));
        assert_eq!(two128m1.shr(64), max);
        assert_eq!(two128m1.shr(127), one);
        assert_eq!(two128m1.shr(128), zero);
        assert_eq!(zero.shl(1000), zero);
        assert_eq!(zero.shr(1000), zero);
        assert_eq!(max.shl(1), n("36893488147419103230"));

        // log2 at powers of two and their neighbours.
        assert_eq!(zero.log2(), zero);
        assert_eq!(one.log2(), zero);
        assert_eq!(BigNat::from_u64(3).log2(), one);
        for k in 1u64..=200 {
            let p = one.shl(k);
            assert_eq!(p.log2().to_u64(), Some(k), "log2(2^{k})");
            assert_eq!(p.sub(&one).log2().to_u64(), Some(k - 1), "log2(2^{k}-1)");
            assert_eq!(p.add(&one).log2().to_u64(), Some(k), "log2(2^{k}+1)");
        }
        assert_eq!(BigNat::from_u64(0).bit_len(), 0);
        assert_eq!(max.bit_len(), 64);
        assert_eq!(two64.bit_len(), 65);
        assert_eq!(two128m1.bit_len(), 128);
        assert_eq!(two128.bit_len(), 129);

        // Ordering across the inline/heap boundary.
        assert!(max < two64);
        assert!(two64 > max);
        assert!(zero < one);
        assert!(two64 < two128);
        assert!(two128m1 < two128);
        assert_eq!(two64.cmp(&two64), Ordering::Equal);

        // Bit operations.
        let a = two64.add(&BigNat::from_u64(5));
        let b = two64.add(&BigNat::from_u64(3));
        assert_eq!(a.and(&b), two64.add(&one));
        assert_eq!(a.or(&b), two64.add(&BigNat::from_u64(7)));
        assert_eq!(a.xor(&b), BigNat::from_u64(6));
        assert_eq!(a.xor(&a), zero);
        assert_eq!(two64.and(&max), zero);
        assert_eq!(two64.or(&max), two64.add(&max));
        assert_eq!(max.xor(&two64), two64.add(&max));
        assert_eq!(a.and(&zero), zero);
        assert_eq!(a.or(&zero), a);

        // gcd.
        assert_eq!(zero.gcd(&seven), seven);
        assert_eq!(seven.gcd(&zero), seven);
        assert_eq!(zero.gcd(&zero), zero);
        assert_eq!(BigNat::from_u64(12).gcd(&BigNat::from_u64(18)), BigNat::from_u64(6));
        assert_eq!(one.shl(100).gcd(&one.shl(80).mul(&BigNat::from_u64(3))), one.shl(80));
        assert_eq!(two128m1.gcd(&two64), one);

        // Multiplication of mixed sizes.
        assert_eq!(max.mul(&zero), zero);
        assert_eq!(max.mul(&one), max);
        assert_eq!(max.mul(&two64), max.shl(64));
    }

    #[test]
    fn python_vectors() {
        const VECTORS: &[(&str, &str, &str, &str)] = include!("bignat_vectors.in");
        assert!(VECTORS.len() >= 2000, "expected at least 2000 vectors, got {}", VECTORS.len());
        for (i, &(op, a, b, want)) in VECTORS.iter().enumerate() {
            let x = n(a);
            let y = n(b);
            let got = match op {
                "add" => x.add(&y).to_decimal(),
                "sub" => x.sub(&y).to_decimal(),
                "mul" => x.mul(&y).to_decimal(),
                "div" => x.div(&y).to_decimal(),
                "rem" => x.rem(&y).to_decimal(),
                "gcd" => x.gcd(&y).to_decimal(),
                "and" => x.and(&y).to_decimal(),
                "or" => x.or(&y).to_decimal(),
                "xor" => x.xor(&y).to_decimal(),
                "shl" => x.shl(small(&y)).to_decimal(),
                "shr" => x.shr(small(&y)).to_decimal(),
                "pow" => x.pow(small(&y)).to_decimal(),
                "log2" => x.log2().to_decimal(),
                "cmp" => match x.cmp(&y) {
                    Ordering::Less => "-1".to_string(),
                    Ordering::Equal => "0".to_string(),
                    Ordering::Greater => "1".to_string(),
                },
                _ => panic!("vector {i}: unknown op {op}"),
            };
            assert_eq!(got, want, "vector {i}: {op}({a}, {b})");
            // Results must also compare equal to the canonical parse of the expected value.
            if op != "cmp" {
                let parsed = n(want);
                let canonical = match op {
                    "add" => x.add(&y),
                    "sub" => x.sub(&y),
                    "mul" => x.mul(&y),
                    "div" => x.div(&y),
                    "rem" => x.rem(&y),
                    "gcd" => x.gcd(&y),
                    "and" => x.and(&y),
                    "or" => x.or(&y),
                    "xor" => x.xor(&y),
                    "shl" => x.shl(small(&y)),
                    "shr" => x.shr(small(&y)),
                    "pow" => x.pow(small(&y)),
                    _ => x.log2(),
                };
                canon(&canonical);
                assert_eq!(canonical, parsed, "vector {i}: {op}({a}, {b}) canonical form");
            }
        }
    }

    #[test]
    fn random_identities() {
        let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
        for it in 0..4000u32 {
            let a = if it % 5 == 0 { rng.limbs_between(40, 64) } else { rng.limbs_between(0, 64) };
            let mut b = if it % 5 == 1 { rng.limbs_between(40, 64) } else { rng.limbs_between(0, 64) };
            if b.is_zero() {
                b = BigNat::from_u64(1 + rng.below(1000));
            }

            let (q, r) = a.div_rem(&b);
            canon(&q);
            canon(&r);
            assert!(r < b, "remainder not below divisor");
            assert_eq!(q.mul(&b).add(&r), a, "a == q*b + r");
            assert_eq!(a.div(&b), q);
            assert_eq!(a.rem(&b), r);

            assert_eq!(a.add(&b).sub(&b), a, "(a+b)-b == a");
            assert_eq!(a.mul(&b).div(&b), a, "(a*b)/b == a");
            assert_eq!(BigNat::from_decimal(a.to_decimal().as_bytes()).unwrap(), a, "decimal round trip");

            let k = rng.below(300);
            assert_eq!(a.shl(k).shr(k), a, "shl/shr round trip");
            assert_eq!(a.shl(k), a.mul(&BigNat::from_u64(1).shl(k)), "shl is multiplication");

            let (x, y) = if a >= b { (a.clone(), b.clone()) } else { (b.clone(), a.clone()) };
            assert_eq!(x.sub(&y).add(&y), x, "truncated sub when x >= y");
            assert_eq!(a > b, !a.sub(&b).is_zero(), "order agrees with sub");

            assert_eq!(a.and(&b).add(&a.xor(&b)), a.or(&b), "or == and + xor");
            assert_eq!(a.xor(&b).xor(&b), a, "xor involution");

            let g = a.gcd(&b);
            if !g.is_zero() {
                assert!(a.rem(&g).is_zero() && b.rem(&g).is_zero(), "gcd divides both");
            }

            // Split b at a random bit s: a*b == a*(b >> s) << s + a*(b mod 2^s).
            let s = rng.below(b.bit_len() + 1);
            let lo = b.and(&BigNat::from_u64(1).shl(s).pred());
            let hi = b.shr(s);
            assert_eq!(a.mul(&b), a.mul(&hi).shl(s).add(&a.mul(&lo)), "distributivity over split");
        }
    }

    #[test]
    fn large_decimal_round_trip() {
        let mut rng = Rng(0xD1B5_4A32_D192_ED03);
        let mut s = String::with_capacity(100_000);
        s.push((b'1' + rng.below(9) as u8) as char);
        for _ in 1..100_000 {
            s.push((b'0' + rng.below(10) as u8) as char);
        }
        let x = BigNat::from_decimal(s.as_bytes()).unwrap();
        assert_eq!(x.to_decimal(), s);
        let sq = x.mul(&x);
        assert_eq!(sq.div(&x), x);
        assert!(sq.rem(&x).is_zero());
        assert_eq!(BigNat::from_decimal(b"0000").unwrap().to_decimal(), "0");
    }
}
