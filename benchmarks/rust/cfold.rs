// cfold reference for the suite record: the Koka/Perceus suite program test/bench/koka/cfold.kk
// (koka-lang/koka, master, fetched 2026-11-04), adapted from the Lean 4 IFL19 const_fold.hs: build a
// full Add/Mul tree of depth n over Var 1 and small Vals, re-associate every chain to the right,
// constant-fold bottom-up with exactly cfold.kk's match arms, and print eval(e) then
// eval(cfold(reassoc(e))) one per line for mk_expr(20, 1). Written for this benchmark.
// usage: cfold [N]   -> prints the two evaluations (N defaults to 20)
use std::rc::Rc;

#[derive(Clone)]
enum Expr {
    Val(i64),
    Var(i64),
    Add(Rc<Expr>, Rc<Expr>),
    Mul(Rc<Expr>, Rc<Expr>),
}
use Expr::*;

fn mk_expr(n: i64, v: i64) -> Expr {
    if n == 0 {
        if v == 0 { Var(1) } else { Val(v) }
    } else {
        Add(Rc::new(mk_expr(n - 1, v + 1)), Rc::new(mk_expr(n - 1, (v - 1).max(0))))
    }
}

// append_add(e0, e3): descend the right spine of Add nodes, rebuild right-associated
fn append_add(e0: &Expr, e3: Expr) -> Expr {
    match e0 {
        Add(e1, e2) => Add(Rc::clone(e1), Rc::new(append_add(e2, e3))),
        _ => Add(Rc::new(e0.clone()), Rc::new(e3)),
    }
}
fn append_mul(e0: &Expr, e3: Expr) -> Expr {
    match e0 {
        Mul(e1, e2) => Mul(Rc::clone(e1), Rc::new(append_mul(e2, e3))),
        _ => Mul(Rc::new(e0.clone()), Rc::new(e3)),
    }
}

fn reassoc(e: &Expr) -> Expr {
    match e {
        Add(e1, e2) => append_add(&reassoc(e1), reassoc(e2)),
        Mul(e1, e2) => append_mul(&reassoc(e1), reassoc(e2)),
        _ => e.clone(),
    }
}

fn cfold(e: &Expr) -> Expr {
    match e {
        Add(e1, e2) => {
            let e1c = cfold(e1);
            let e2c = cfold(e2);
            match &e1c {
                Val(a) => match &e2c {
                    Val(b) => Val(a + b),
                    Add(f, g) => {
                        // cfold.kk: Add(f, Val b) -> Add(Val(a+b), f); Add(Val b, f) -> Add(Val(a+b), f)
                        if let Val(b) = &**g { return Add(Rc::new(Val(a + b)), Rc::clone(f)); }
                        if let Val(b) = &**f { return Add(Rc::new(Val(a + b)), Rc::new((**g).clone())); }
                        Add(Rc::new(e1c.clone()), Rc::new(e2c.clone()))
                    }
                    _ => Add(Rc::new(e1c.clone()), Rc::new(e2c.clone())),
                },
                _ => Add(Rc::new(e1c), Rc::new(e2c)),
            }
        }
        Mul(e1, e2) => {
            let e1c = cfold(e1);
            let e2c = cfold(e2);
            match &e1c {
                Val(a) => match &e2c {
                    Val(b) => Val(a * b),
                    Mul(f, g) => {
                        // cfold.kk: Mul(f, Val b) -> Mul(Val(a*b), f); Mul(Val b, f) -> Mul(Val(a*b), f)
                        if let Val(b) = &**g { return Mul(Rc::new(Val(a * b)), Rc::clone(f)); }
                        if let Val(b) = &**f { return Mul(Rc::new(Val(a * b)), Rc::new((**g).clone())); }
                        Mul(Rc::new(e1c.clone()), Rc::new(e2c.clone()))
                    }
                    _ => Mul(Rc::new(e1c.clone()), Rc::new(e2c.clone())),
                },
                _ => Mul(Rc::new(e1c), Rc::new(e2c)),
            }
        }
        _ => e.clone(),
    }
}

fn eval_expr(e: &Expr) -> i64 {
    match e {
        Var(_) => 0,
        Val(v) => *v,
        Add(l, r) => eval_expr(l) + eval_expr(r),
        Mul(l, r) => eval_expr(l) * eval_expr(r),
    }
}

fn main() {
    let n: i64 = std::env::args().nth(1).map(|s| s.parse().unwrap()).unwrap_or(20);
    // deep recursion over the 2^21-long reassoc/cfold chains: big stack, as elsewhere in this corpus
    std::thread::Builder::new().stack_size(1 << 30).spawn(move || {
        let e = mk_expr(n, 1);
        let v1 = eval_expr(&e);
        println!("{}", v1);
        let v2 = eval_expr(&cfold(&reassoc(&e)));
        println!("{}", v2);
    }).unwrap().join().unwrap();
}
