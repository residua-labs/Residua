// deriv reference for SUITE-1: the Koka/Perceus suite program test/bench/koka/deriv.kk
// (koka-lang/koka, master, fetched 2026-11-04), from the Lean 4 IFL19 deriv benchmark: symbolic
// differentiation of pow(x,x)/10 via smart constructors (add/mul/pow normalize Val/0/1 and flatten
// Add/Mul chains exactly as deriv.kk's `add`/`mul`/`powr` do; the .rsd derives them with explicit
// fuel, which is only its termination proof, not a behavioral difference), then d/dx applied
// incrementally, printing "i+1 count: N" for i = 0..9 and "done". Written for this benchmark.
// usage: deriv   -> prints the ten lines and "done"
use std::rc::Rc;

#[derive(Clone)]
enum Expr {
    Val(i64),
    Var(&'static str),
    Add(Rc<Expr>, Rc<Expr>),
    Mul(Rc<Expr>, Rc<Expr>),
    Pow(Rc<Expr>, Rc<Expr>),
    Ln(Rc<Expr>),
}
use Expr::*;

fn val(n: i64) -> Expr { Val(n) }
// deriv.kk `add` (the .rsd's addAux with sufficient fuel; same cases, same order):
// val+val; 0+f; f+0; f+val n (swap); val n + (val m + f) -> val(n+m) + f;
// f + (val n + g) -> val n + (f + g); (f + g) + h -> f + (g + h); else Add.
fn add(a: Expr, b: Expr) -> Expr {
    match (&a, &b) {
        (Val(n), Val(m)) => val(n + m),
        (Val(0), _) => b,
        (_, Val(0)) => a,
        (_, Val(_)) => add(b, a),
        (Val(n), Add(l, r)) => match **l {
            Val(m) => add(val(n + m), (**r).clone()),
            ref _l => Add(Rc::new(a), Rc::new(b)),
        },
        (_, Add(l, r)) => match **l {
            Val(_) => add((**l).clone(), add(a, (**r).clone())),
            ref _l => match &a {
                Add(af, ag) => {
                    let (afc, agc) = ((**af).clone(), (**ag).clone());
                    add(afc, add(agc, b))
                }
                _ => Add(Rc::new(a), Rc::new(b)),
            },
        },
        (Add(af, ag), _) => add((**af).clone(), add((**ag).clone(), b)),
        _ => Add(Rc::new(a), Rc::new(b)),
    }
}
// deriv.kk `mul` (the .rsd's mulAux): val*val; val 0; val 1; f*val n (swap);
// val n * (val m * f) -> val(n*m) * f; f * (val n * g) -> val n * (f * g);
// (f * g) * h -> f * (g * h); else Mul.
fn mul(a: Expr, b: Expr) -> Expr {
    match (&a, &b) {
        (Val(n), Val(m)) => val(n * m),
        (Val(0), _) | (_, Val(0)) => val(0),
        (Val(1), _) => b,
        (_, Val(_)) => mul(b, a),
        (Val(n), Mul(l, r)) => match **l {
            Val(m) => mul(val(n * m), (**r).clone()),
            ref _l => Mul(Rc::new(a), Rc::new(b)),
        },
        (_, Mul(l, r)) => match **l {
            Val(_) => mul((**l).clone(), mul(a, (**r).clone())),
            ref _l => match &a {
                Mul(af, ag) => {
                    let (afc, agc) = ((**af).clone(), (**ag).clone());
                    mul(afc, mul(agc, b))
                }
                _ => Mul(Rc::new(a), Rc::new(b)),
            },
        },
        (Mul(af, ag), _) => mul((**af).clone(), mul((**ag).clone(), b)),
        _ => Mul(Rc::new(a), Rc::new(b)),
    }
}
fn pown(m: i64, n: i64) -> i64 { if n == 0 { 1 } else { m.pow(n as u32) } }
fn powr(a: Expr, b: Expr) -> Expr {
    match (&a, &b) {
        (Val(m), Val(n)) => val(pown(*m, *n)),
        (_, Val(0)) => val(1),
        (_, Val(1)) => a,
        (Val(0), _) => val(0),
        _ => Pow(Rc::new(a), Rc::new(b)),
    }
}
fn ln_e(a: Expr) -> Expr { match a { Val(1) => Val(0), _ => Ln(Rc::new(a)) } }

fn d(x: &'static str, e: &Expr) -> Expr {
    match e {
        Val(_) => val(0),
        Var(y) => val(if *y == x { 1 } else { 0 }),
        Add(f, g) => add(d(x, f), d(x, g)),
        Mul(f, g) => add(mul((**f).clone(), d(x, g)), mul((**g).clone(), d(x, f))),
        Pow(f, g) => mul(
            powr((**f).clone(), (**g).clone()),
            add(
                mul(mul((**g).clone(), d(x, f)), powr((**f).clone(), val(-1))),
                mul(ln_e((**f).clone()), d(x, g)),
            ),
        ),
        Ln(f) => mul(d(x, f), powr((**f).clone(), val(-1))),
    }
}

// deriv.kk count: Val and Var both count as 1
fn count(x: &str, e: &Expr) -> i64 {
    match e {
        Val(_) | Var(_) => 1,
        Var(y) => if *y == x { 1 } else { 0 },
        Add(f, g) | Mul(f, g) | Pow(f, g) => count(x, f) + count(x, g),
        Ln(f) => count(x, f),
    }
}

fn main() {
    // deriv.kk main: f := powr (var "x") (var "x"); nest(deriv, 10, f): each step f := d/dx f, print "i+1 count: n"
    // big stack for the smart-constructor recursion over the final expressions
    std::thread::Builder::new().stack_size(1 << 30).spawn(|| {
        let mut f = powr(Var("x"), Var("x"));
        for i in 1..=10 {
            f = d("x", &f);
            println!("{} count: {}", i, count("x", &f));
        }
        println!("done");
    }).unwrap().join().unwrap();
}
