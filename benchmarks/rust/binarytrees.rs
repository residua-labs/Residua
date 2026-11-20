// binary-trees reference for the benchmark kit: Computer Language Benchmarks Game, binary-trees. The Game's
// Rust entries use typed_arena / toolshed arenas and threads (rules ask for no custom arena; the
// published entries have one). This is the straightforward single-threaded program of the rules: one
// Box allocation per node (leaves included), trees dropped when the check is done. The tree type and
// recursion follow the Game's Rust entry #1 (Option<..> children, a node for depth >= 0), with Box in place
// of the arena. Output text is the Game's.
// usage: binarytrees N REPS   -> prints the Game's output for N; best time of REPS runs to stderr.
use std::hint::black_box;
use std::time::Instant;

struct Tree { l: Option<Box<Tree>>, r: Option<Box<Tree>> }

fn item_check(t: &Option<Box<Tree>>) -> i32 {
    match t { None => 0, Some(b) => 1 + item_check(&b.l) + item_check(&b.r) }
}

fn bottom_up_tree(depth: i32) -> Option<Box<Tree>> {
    if depth >= 0 {
        Some(Box::new(Tree { l: bottom_up_tree(depth - 1), r: bottom_up_tree(depth - 1) }))
    } else { None }
}

fn inner(depth: i32, iterations: i32) -> String {
    let mut chk = 0;
    for _ in 1..iterations + 1 {
        let a = bottom_up_tree(depth);
        chk += item_check(&a);
    }
    format!("{}\t trees of depth {}\t check: {}", iterations, depth, chk)
}

fn run(n: i32) -> String {
    let min_depth = 4;
    let max_depth = if min_depth + 2 > n { min_depth + 2 } else { n };
    let mut out = String::new();
    {
        let depth = max_depth + 1;
        let tree = bottom_up_tree(depth);
        out += &format!("stretch tree of depth {}\t check: {}\n", depth, item_check(&tree));
    }
    let long_lived_tree = bottom_up_tree(max_depth);
    for depth in (min_depth..max_depth + 1).filter(|d| d % 2 == 0) {
        let iterations = 1 << ((max_depth - depth + min_depth) as u32);
        out += &inner(depth, iterations);
        out += "\n";
    }
    out += &format!("long lived tree of depth {}\t check: {}\n", max_depth, item_check(&long_lived_tree));
    out
}

// harness only: process CPU time (user+sys, all threads), so a loaded shared machine inflates it less than wall
#[repr(C)] struct Ts { s: i64, ns: i64 }
extern "C" { fn clock_gettime(id: i32, ts: *mut Ts) -> i32; }
fn cpu_s() -> f64 { let mut t = Ts { s: 0, ns: 0 }; unsafe { clock_gettime(12, &mut t); } t.s as f64 + t.ns as f64 * 1e-9 }

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let n: i32 = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(10);
    let reps: usize = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);
    let mut best = f64::MAX; let mut bestc = f64::MAX; let mut out = String::new();
    for _ in 0..reps {
        let c0 = cpu_s(); let t = Instant::now();
        out = black_box(run(black_box(n)));
        best = best.min(t.elapsed().as_secs_f64()); bestc = bestc.min(cpu_s() - c0);
    }
    print!("{}", out);
    eprintln!("best_s {:.9} best_cpu_s {:.9}", best, bestc);
}
