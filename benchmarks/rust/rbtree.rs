// rbtree reference for the benchmark kit: the Koka/Perceus suite program rbtree (koka-lang/koka
// test/bench/koka/rbtree.kk, from the Lean 4 IFL19 rbmap benchmark), same algorithm: insert keys
// n-1 .. 0 (value = key % 10 == 0) one at a time into a red-black tree with the Okasaki-style
// balance-left / balance-right of that source, then fold counting the true values. Safe Rust, owned
// nodes (Box) consumed and rebuilt by each insert, which is the in-place-reuse form of the persistent
// algorithm (Lean/Koka reach the same by reference-count reuse). Written for this benchmark.
// usage: rbtree N REPS   -> prints the count; best time of REPS runs to stderr.
use std::hint::black_box;
use std::time::Instant;

#[derive(Clone, Copy, PartialEq)]
enum Color { Red, Black }
enum Tree { Leaf, Node(Box<N>) }
struct N { c: Color, l: Tree, k: i32, v: bool, r: Tree }
use Tree::*;

fn node(c: Color, l: Tree, k: i32, v: bool, r: Tree) -> Tree { Node(Box::new(N { c, l, k, v, r })) }
fn is_red(t: &Tree) -> bool { matches!(t, Node(n) if n.c == Color::Red) }

fn balance_left(l: Tree, k: i32, v: bool, r: Tree) -> Tree {
    match l {
        Leaf => Leaf,
        Node(ln) => {
            let N { c: _, l: lx_, k: ky, v: vy, r: ry } = *ln;
            // case 1: left child of l is red
            if let Node(ref a) = lx_ { if a.c == Color::Red {
                if let Node(a) = lx_ {
                    let N { c: _, l: lx, k: kx, v: vx, r: rx } = *a;
                    return node(Color::Red, node(Color::Black, lx, kx, vx, rx), ky, vy, node(Color::Black, ry, k, v, r));
                } else { unreachable!() }
            } }
            // case 2: right child of l is red
            if let Node(ref a) = ry { if a.c == Color::Red {
                if let Node(a) = ry {
                    let N { c: _, l: lx, k: kx, v: vx, r: rx } = *a;
                    return node(Color::Red, node(Color::Black, lx_, ky, vy, lx), kx, vx, node(Color::Black, rx, k, v, r));
                } else { unreachable!() }
            } }
            node(Color::Black, node(Color::Red, lx_, ky, vy, ry), k, v, r)
        }
    }
}

fn balance_right(l: Tree, k: i32, v: bool, r: Tree) -> Tree {
    match r {
        Leaf => Leaf,
        Node(rn) => {
            let N { c: _, l: lx_, k: kx, v: vx, r: rx_ } = *rn;
            if let Node(ref a) = lx_ { if a.c == Color::Red {
                if let Node(a) = lx_ {
                    let N { c: _, l: lx, k: ky, v: vy, r: ry } = *a;
                    return node(Color::Red, node(Color::Black, l, k, v, lx), ky, vy, node(Color::Black, ry, kx, vx, rx_));
                } else { unreachable!() }
            } }
            if let Node(ref a) = rx_ { if a.c == Color::Red {
                if let Node(a) = rx_ {
                    let N { c: _, l: ly, k: ky, v: vy, r: ry } = *a;
                    return node(Color::Red, node(Color::Black, l, k, v, lx_), kx, vx, node(Color::Black, ly, ky, vy, ry));
                } else { unreachable!() }
            } }
            node(Color::Black, l, k, v, node(Color::Red, lx_, kx, vx, rx_))
        }
    }
}

fn ins(t: Tree, k: i32, v: bool) -> Tree {
    match t {
        Leaf => node(Color::Red, Leaf, k, v, Leaf),
        Node(n) => {
            let N { c, l, k: kx, v: vx, r } = *n;
            if c == Color::Red {
                if k < kx { node(Color::Red, ins(l, k, v), kx, vx, r) }
                else if k > kx { node(Color::Red, l, kx, vx, ins(r, k, v)) }
                else { node(Color::Red, l, k, v, r) }
            } else if k < kx {
                if is_red(&l) { balance_left(ins(l, k, v), kx, vx, r) } else { node(Color::Black, ins(l, k, v), kx, vx, r) }
            } else if k > kx {
                if is_red(&r) { balance_right(l, kx, vx, ins(r, k, v)) } else { node(Color::Black, l, kx, vx, ins(r, k, v)) }
            } else { node(Color::Black, l, k, v, r) }
        }
    }
}

fn set_black(t: Tree) -> Tree {
    match t { Node(n) => { let N { c: _, l, k, v, r } = *n; node(Color::Black, l, k, v, r) } Leaf => Leaf }
}

fn fold_count(t: &Tree, b: i32) -> i32 {
    match t { Leaf => b, Node(n) => { let a = fold_count(&n.l, b); fold_count(&n.r, if n.v { a + 1 } else { a }) } }
}

fn make_tree(n: i32) -> Tree {
    let mut t = Leaf;
    let mut i = n;
    while i > 0 { i -= 1; t = set_black(ins(t, i, i % 10 == 0)); }
    t
}

// harness only: process CPU time (user+sys, all threads), so a loaded shared machine inflates it less than wall
#[repr(C)] struct Ts { s: i64, ns: i64 }
extern "C" { fn clock_gettime(id: i32, ts: *mut Ts) -> i32; }
fn cpu_s() -> f64 { let mut t = Ts { s: 0, ns: 0 }; unsafe { clock_gettime(12, &mut t); } t.s as f64 + t.ns as f64 * 1e-9 }

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let n: i32 = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(4200000);
    let reps: usize = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);
    let mut best = f64::MAX; let mut bestc = f64::MAX; let mut r = 0;
    for _ in 0..reps {
        let c0 = cpu_s(); let t = Instant::now();
        let tree = make_tree(black_box(n));
        r = black_box(fold_count(&tree, 0));
        best = best.min(t.elapsed().as_secs_f64()); bestc = bestc.min(cpu_s() - c0);
        std::mem::forget(tree);
    }
    println!("{}", r);
    eprintln!("best_s {:.9} best_cpu_s {:.9}", best, bestc);
}
