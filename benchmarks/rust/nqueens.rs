// nqueens reference for PERF-KIT-0: the Koka/Perceus suite program nqueens (koka-lang/koka
// test/bench/koka/nqueens.kk) in the shape of that suite's C++ version (test/bench/cpp/nqueens.cpp):
// solutions are persistent singly-linked lists whose tails are shared; `safe` checks column and both
// diagonals against the queens already placed; append_safe walks the columns n..1; extend/find_solutions
// grow the solution set one row at a time. Safe Rust: Rc cells, freed when the last owner drops
// (the C++ original leaks). Written for this benchmark (the suite publishes no Rust version).
// usage: nqueens N REPS   -> prints the solution count; best time of REPS runs to stderr.
use std::hint::black_box;
use std::rc::Rc;
use std::time::Instant;

enum List<T> { Nil, Cons(T, Rc<List<T>>) }
type Soln = Rc<List<i32>>;
type Solns = Rc<List<Soln>>;

fn safe(queen: i32, xs: &Soln) -> bool {
    let mut cur = xs;
    let mut diag = 1;
    while let List::Cons(q, tail) = &**cur {
        if queen == *q || queen == *q + diag || queen == *q - diag { return false; }
        diag += 1;
        cur = tail;
    }
    true
}

fn append_safe(k: i32, soln: &Soln, solns: Solns) -> Solns {
    let mut acc = solns;
    let mut n = k;
    while n > 0 {
        if safe(n, soln) {
            acc = Rc::new(List::Cons(Rc::new(List::Cons(n, soln.clone())), acc));
        }
        n -= 1;
    }
    acc
}

fn extend(n: i32, solns: &Solns) -> Solns {
    let mut acc: Solns = Rc::new(List::Nil);
    let mut cur = solns;
    while let List::Cons(soln, rest) = &**cur {
        acc = append_safe(n, soln, acc);
        cur = rest;
    }
    acc
}

fn len<T>(xs: &Rc<List<T>>) -> i64 {
    let mut n = 0;
    let mut cur = xs;
    while let List::Cons(_, tail) = &**cur { n += 1; cur = tail; }
    n
}

fn nqueens(n: i32) -> i64 {
    let mut acc: Solns = Rc::new(List::Cons(Rc::new(List::Nil), Rc::new(List::Nil)));
    for _ in 0..n { acc = extend(n, &acc); }
    let r = len(&acc);
    // drop iteratively-safe: the lists are at most n*count cells long on the spine; default drop recursion
    // depth is the spine length, so drop the spine by hand to avoid a stack overflow at n = 13.
    let mut cur = acc;
    loop {
        match Rc::try_unwrap(cur) {
            Ok(List::Cons(_, tail)) => cur = tail,
            _ => break,
        }
    }
    r
}

// harness only: process CPU time (user+sys, all threads), so a loaded shared machine inflates it less than wall
#[repr(C)] struct Ts { s: i64, ns: i64 }
extern "C" { fn clock_gettime(id: i32, ts: *mut Ts) -> i32; }
fn cpu_s() -> f64 { let mut t = Ts { s: 0, ns: 0 }; unsafe { clock_gettime(12, &mut t); } t.s as f64 + t.ns as f64 * 1e-9 }

fn main() {
    // list drops recurse along the spine: run on a thread with a large stack (all-safe, no unsafe)
    std::thread::Builder::new().stack_size(1 << 30).spawn(real_main).unwrap().join().unwrap();
}

fn real_main() {
    let a: Vec<String> = std::env::args().collect();
    let n: i32 = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(13);
    let reps: usize = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);
    let mut best = f64::MAX; let mut bestc = f64::MAX; let mut r = 0;
    for _ in 0..reps {
        let c0 = cpu_s(); let t = Instant::now();
        r = black_box(nqueens(black_box(n)));
        best = best.min(t.elapsed().as_secs_f64()); bestc = bestc.min(cpu_s() - c0);
    }
    println!("{}", r);
    eprintln!("best_s {:.9} best_cpu_s {:.9}", best, bestc);
}
