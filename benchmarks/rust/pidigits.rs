// pidigits reference for SUITE-1: the Benchmarks Game program (description page fetched 2026-11-04):
// Gibbons' unbounded spigot as run by the Game's C/Rust entries — state (k, acc, den, num) over
// arbitrary-precision SIGNED integers starting (0, 0, 1, 1); next_term composes k2 = 2k+1,
// acc = (acc + 2*num)*k2, den *= k2, num *= k until num <= acc and extract(3) == extract(4) with
// extract(j) = (num*j + acc) / den truncating toward zero; then emit d = extract(3) and eliminate
// (acc = (acc - den*d)*10, num *= 10). The Game entries rely on GMP; offline this carries a
// hand-rolled bignum (base 2^32 limbs, signed magnitude) implementing exactly the mpz operations the
// algorithm needs (mul/add by small, signed compare, truncating division with a small quotient).
// Written for this benchmark.
// usage: pidigits N   -> prints digits 10 per line "digits\t:total", partial line space-padded
use std::cmp::Ordering;

#[derive(Clone, PartialEq, Eq)]
struct Big {
    neg: bool,
    mag: Vec<u32>, // little-endian, no trailing zero limbs; [] = 0 (neg false)
}

impl Big {
    fn from_i64(v: i64) -> Big {
        let neg = v < 0;
        let mut m = (v.unsigned_abs() as u128) as u128;
        let mut mag = Vec::new();
        while m > 0 { mag.push(m as u32); m >>= 32; }
        Big { neg: neg && !mag.is_empty(), mag }
    }
    fn is_zero(&self) -> bool { self.mag.is_empty() }
    fn to_i64(&self) -> i64 {
        let mut v: u128 = 0;
        for &l in self.mag.iter().rev() { v = (v << 32) | l as u128; }
        if self.neg { -(v as i64) } else { v as i64 }
    }
    fn cmp_mag(a: &[u32], b: &[u32]) -> Ordering {
        if a.len() != b.len() { return a.len().cmp(&b.len()) }
        for i in (0..a.len()).rev() {
            if a[i] != b[i] { return a[i].cmp(&b[i]) }
        }
        Ordering::Equal
    }
    fn cmp(&self, other: &Big) -> Ordering {
        match (self.neg, other.neg) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            (false, false) => Self::cmp_mag(&self.mag, &other.mag),
            (true, true) => Self::cmp_mag(&other.mag, &self.mag),
        }
    }
    fn add_mag(a: &[u32], b: &[u32]) -> Vec<u32> {
        let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };
        let mut out = Vec::with_capacity(long.len() + 1);
        let mut carry = 0u64;
        for i in 0..long.len() {
            let s = long[i] as u64 + if i < short.len() { short[i] as u64 } else { 0 } + carry;
            out.push(s as u32);
            carry = s >> 32;
        }
        if carry > 0 { out.push(carry as u32) }
        out
    }
    fn sub_mag(a: &[u32], b: &[u32]) -> Vec<u32> { // requires |a| >= |b|
        let mut out = Vec::with_capacity(a.len());
        let mut borrow = 0i64;
        for i in 0..a.len() {
            let s = a[i] as i64 - if i < b.len() { b[i] as i64 } else { 0 } - borrow;
            if s < 0 { out.push((s + (1i64 << 32)) as u32); borrow = 1 } else { out.push(s as u32); borrow = 0 }
        }
        while let Some(&0) = out.last() { out.pop(); }
        out
    }
    fn add(&self, other: &Big) -> Big {
        if self.neg == other.neg {
            Big { neg: self.neg, mag: Self::add_mag(&self.mag, &other.mag) }
        } else {
            match Self::cmp_mag(&self.mag, &other.mag) {
                Ordering::Equal => Big { neg: false, mag: Vec::new() },
                Ordering::Greater => Big { neg: self.neg, mag: Self::sub_mag(&self.mag, &other.mag) },
                Ordering::Less => Big { neg: other.neg, mag: Self::sub_mag(&other.mag, &self.mag) },
            }
        }
    }
    fn neg_of(&self) -> Big { Big { neg: !self.neg && !self.is_zero(), mag: self.mag.clone() } }
    // self * c for small c >= 0
    fn mul_small(&self, c: u64) -> Big {
        if c == 0 || self.is_zero() { return Big { neg: false, mag: Vec::new() } }
        let mut out = Vec::with_capacity(self.mag.len() + 2);
        let mut carry = 0u64;
        for &l in &self.mag {
            let p = l as u64 * c + carry;
            out.push(p as u32);
            carry = p >> 32;
        }
        while carry > 0 { out.push(carry as u32); carry >>= 32; }
        Big { neg: self.neg, mag: out }
    }
    // self + other * c for small c >= 0
    fn addmul_small(&self, other: &Big, c: u64) -> Big {
        self.add(&other.mul_small(c))
    }
    // |self| / |other|, quotient only; quotient is small (< 2^32) by construction here
    fn div_quot(&self, other: &Big) -> u64 {
        // |self| / |other|, quotient only; precondition |self| >= |other| and quotient < 2^32.
        // One normalized 64/32 Knuth-style estimate from the top limbs, then correct by trial
        // multiplication (at most a couple of O(len) steps).
        let n = &self.mag;
        let d = &other.mag;
        debug_assert!(!d.is_empty());
        if Big::cmp_mag(n, d) == Ordering::Less { return 0 }
        let dl = *d.last().unwrap() as u128;
        let s = dl.leading_zeros() as u32; // dl != 0 so s < 32
        // normalized top 64 bits of d
        let dtop: u128 = if d.len() >= 2 {
            (dl << s) | ((d[d.len() - 2] as u128) >> (32 - s))
        } else {
            dl << s
        };
        // top 64 bits of n, shifted by s too (with the next limb's bits shifted in)
        let nwin: u128 = if n.len() >= 2 {
            ((n[n.len() - 1] as u128) << 32) | (n[n.len() - 2] as u128)
        } else {
            n[0] as u128
        };
        let ntop: u128 = if n.len() >= 3 && s > 0 {
            (nwin << s) | ((n[n.len() - 3] as u128) >> (32 - s))
        } else {
            nwin << s
        };
        let mut q = (ntop / dtop) as u128;
        if q == 0 { q = 1 }
        loop {
            // verify: |self| - q*|other| in [0, |other|)
            let qo = Big { neg: false, mag: mul_small_mag(d, q as u64) };
            match Big::cmp_mag(n, &qo.mag) {
                Ordering::Less => q -= 1, // overestimate; estimate is within a few of the truth
                Ordering::Greater | Ordering::Equal => {
                    // underestimate? remainder still >= divisor
                    let qo1 = Big { neg: false, mag: mul_small_mag(d, q as u64 + 1) };
                    if Big::cmp_mag(n, &qo1.mag) != Ordering::Less { q += 1; continue }
                    return q as u64;
                }
            }
        }
    }
}

fn mul_small_mag(mag: &[u32], c: u64) -> Vec<u32> {
    if c == 0 { return Vec::new() }
    let mut out = Vec::with_capacity(mag.len() + 2);
    let mut carry = 0u64;
    for &l in mag {
        let p = l as u64 * c + carry;
        out.push(p as u32);
        carry = p >> 32;
    }
    while carry > 0 { out.push(carry as u32); carry >>= 32; }
    out
}

struct Ctx { k: i64, acc: Big, den: Big, num: Big }

fn next_term(c: &mut Ctx) {
    c.k += 1;
    let k2 = (c.k * 2 + 1) as u64;
    c.acc = c.acc.addmul_small(&c.num, 2).mul_small(k2);
    c.den = c.den.mul_small(k2);
    c.num = c.num.mul_small(c.k as u64);
}

fn extract(c: &Ctx, nth: u64) -> i64 {
    let t = c.num.mul_small(nth).add(&c.acc);
    let (num_mag, neg) = if !t.neg { (&t.mag, false) } else { (&t.neg_of().mag, true) };
    // (num*j + acc) is positive whenever the algorithm calls this (num, den > 0, num <= acc),
    // but truncate toward zero correctly anyway
    if Big::cmp_mag(num_mag, &c.den.mag) == Ordering::Less {
        return 0; // includes truncation of values in (-1, 0) toward zero
    }
    let q = Big { neg: false, mag: num_mag.to_vec() }.div_quot(&c.den);
    if neg { -(q as i64) } else { q as i64 }
}

fn eliminate(c: &mut Ctx, d: i64) {
    // acc = (acc - den*d) * 10; num = num * 10
    let acc2 = c.acc.add(&c.den.mul_small(d as u64).neg_of());
    c.acc = acc2.mul_small(10);
    c.num = c.num.mul_small(10);
}

fn next(c: &mut Ctx) -> i64 {
    loop {
        next_term(c);
        if c.num.cmp(&c.acc) == Ordering::Greater { continue }
        let d3 = extract(c, 3);
        let d4 = extract(c, 4);
        if d3 != d4 { continue }
        eliminate(c, d3);
        return d3;
    }
}

fn main() {
    let n: usize = std::env::args().nth(1).map(|s| s.parse().unwrap()).unwrap_or(30);
    let mut c = Ctx { k: 0, acc: Big::from_i64(0), den: Big::from_i64(1), num: Big::from_i64(1) };
    let mut line = String::new();
    let mut i = 0usize;
    for _ in 0..n {
        let d = next(&mut c);
        line.push((b'0' + d as u8) as char);
        i += 1;
        if i % 10 == 0 {
            println!("{}\t:{}", line, i);
            line.clear();
        }
    }
    if !line.is_empty() {
        let pad = " ".repeat(10 - i % 10);
        println!("{}{}\t:{}", line, pad, i);
    }
}
