// rbtreeck reference for SUITE-1: the Koka/Perceus suite program test/bench/koka/rbtree-ck.kk
// (koka-lang/koka, master, fetched 2026-11-04): same red-black insert algorithm as rbtree.rs (that
// file), but make-tree-aux keeps every freq-th tree alive in a list and the entry counts the trues
// in the head of that list (Koka conses `t'` when `n % freq == 0`). Nodes are Rc because the kept
// list shares subtrees with the live tree (Koka shares by reference-counting). Written for this
// benchmark.
// usage: rbtreeck FREQ N   -> prints the count
use std::env;
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq)]
enum Color { Red, Black }

struct N { c: Color, l: Tree, k: i32, v: bool, r: Tree }

#[derive(Clone)]
enum Tree { Leaf, Node(Rc<N>) }
use Tree::*;

fn node(c: Color, l: Tree, k: i32, v: bool, r: Tree) -> Tree { Node(Rc::new(N { c, l, k, v, r })) }
fn is_red(t: &Tree) -> bool { matches!(t, Node(n) if n.c == Color::Red) }

fn balance_left(l: &Tree, k: i32, v: bool, r: Tree) -> Tree {
    match l {
        Leaf => Leaf,
        Node(ln) => {
            // case 1: left child of l is red
            if let Node(a) = &ln.l { if a.c == Color::Red {
                return node(Color::Red,
                    node(Color::Black, a.l.clone(), a.k, a.v, a.r.clone()),
                    ln.k, ln.v,
                    node(Color::Black, ln.r.clone(), k, v, r));
            } }
            // case 2: right child of l is red
            if let Node(a) = &ln.r { if a.c == Color::Red {
                return node(Color::Red,
                    node(Color::Black, ln.l.clone(), ln.k, ln.v, a.l.clone()),
                    a.k, a.v,
                    node(Color::Black, a.r.clone(), k, v, r));
            } }
            node(Color::Black, node(Color::Red, ln.l.clone(), ln.k, ln.v, ln.r.clone()), k, v, r)
        }
    }
}

fn balance_right(l: Tree, k: i32, v: bool, r: &Tree) -> Tree {
    match r {
        Leaf => Leaf,
        Node(rn) => {
            // case 1: left child of r is red
            if let Node(a) = &rn.l { if a.c == Color::Red {
                return node(Color::Red,
                    node(Color::Black, l.clone(), k, v, a.l.clone()),
                    a.k, a.v,
                    node(Color::Black, a.r.clone(), rn.k, rn.v, rn.r.clone()));
            } }
            // case 2: right child of r is red
            if let Node(a) = &rn.r { if a.c == Color::Red {
                return node(Color::Red,
                    node(Color::Black, l.clone(), k, v, rn.l.clone()),
                    rn.k, rn.v,
                    node(Color::Black, a.l.clone(), a.k, a.v, a.r.clone()));
            } }
            node(Color::Black, l, k, v, node(Color::Red, rn.l.clone(), rn.k, rn.v, rn.r.clone()))
        }
    }
}

fn ins(t: &Tree, k: i32, v: bool) -> Tree {
    match t {
        Leaf => node(Color::Red, Leaf, k, v, Leaf),
        Node(n) if n.c == Color::Red => {
            if k < n.k { node(Color::Red, ins(&n.l, k, v), n.k, n.v, n.r.clone()) }
            else if k > n.k { node(Color::Red, n.l.clone(), n.k, n.v, ins(&n.r, k, v)) }
            else { node(Color::Red, n.l.clone(), k, v, n.r.clone()) }
        }
        Node(n) => {
            // black parent: rebalance only if the child we descend into is red; the balance
            // result REPLACES this node (rbtree.rsd/rbtree-ck.kk: no outer wrap)
            if k < n.k {
                let il = ins(&n.l, k, v);
                if is_red(&n.l) { balance_left(&il, n.k, n.v, n.r.clone()) }
                else { node(Color::Black, il, n.k, n.v, n.r.clone()) }
            } else if k > n.k {
                let ir = ins(&n.r, k, v);
                if is_red(&n.r) { balance_right(n.l.clone(), n.k, n.v, &ir) }
                else { node(Color::Black, n.l.clone(), n.k, n.v, ir) }
            } else {
                node(Color::Black, n.l.clone(), k, v, n.r.clone())
            }
        }
    }
}

fn set_black(t: Tree) -> Tree {
    match t {
        Node(b) => {
            if b.c == Color::Black { Node(b) }
            else { Node(Rc::new(N { c: Color::Black, l: b.l.clone(), k: b.k, v: b.v, r: b.r.clone() })) }
        }
        Leaf => Leaf,
    }
}

fn insert(t: &Tree, k: i32, v: bool) -> Tree { set_black(ins(t, k, v)) }

fn fold_count(t: &Tree, acc: i64) -> i64 {
    match t {
        Leaf => acc,
        Node(n) => fold_count(&n.r, fold_count(&n.l, acc) + if n.v { 1 } else { 0 }),
    }
}

// koka make-tree-aux: at step m (m = n .. 1) insert key m (value = m % 10 == 0); cons t' when
// m % freq == 0; at m = 0 cons the current tree; head of the list = that final tree. Vec mirrors
// the list (Koka shares the trees; Rc clones below are cheap).
fn make_tree_aux(m: i32, freq: i32, t: &Tree, ts: &mut Vec<Tree>) {
    if m == 0 { ts.push(t.clone()); return }
    let t1 = insert(t, m, (m % 10) == 0);
    if m % freq == 0 { ts.push(t1.clone()) }
    make_tree_aux(m - 1, freq, &t1, ts)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let freq: i32 = args.get(1).map(|s| s.parse().unwrap()).unwrap_or(5).max(1);
    let n: i32 = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(4200000);
    // deep linear recursion over the insert loop: big stack, as elsewhere in this corpus
    std::thread::Builder::new().stack_size(1 << 30).spawn(move || {
        let mut ts: Vec<Tree> = Vec::new();
        make_tree_aux(n, freq, &Leaf, &mut ts);
        // head of the Koka list = the most recently consed tree = the final tree
        let head = ts.last().unwrap().clone();
        drop(ts);
        println!("{}", fold_count(&head, 0));
    }).unwrap().join().unwrap();
}
