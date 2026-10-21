/-
RCIC 06 §15 — counted runs of the first-order machine (`Raw.step`, the model
pinned to `apps/rcic-scm-core`), and big-step evaluation rules derived from
it, for reasoning about one program's runs (#6029 K4-2).

`Reach p n c c'`: `n` transitions of `Raw.step`, each a `next`, lead from
`c` to `c'`. 06 §15 "`SCM-Cost-0` charges one unit per transition", so `n`
is the SCM-Cost-0 cost of that stretch. `Evals p env e v n` says that `e`
evaluates to `v` in `n` transitions under ANY continuation: the rules below
are stated for every continuation, so composing them needs no frame-stack
extension lemma.

Nothing here is a new semantics: every rule is proved by unfolding
`Raw.step` and composing `Reach`. The rules cover the expression forms the
compact instantiate program uses (lit, var, let, if, field, two- and
three-field records, nil, cons, pair, binary primitives that return,
handle whose body returns, list fold).
-/
import rcic.ScmMachineRaw

namespace Rcic.Scm.Raw
open Rcic.Scm

/-- `n` transitions of `step`, each a `next`. -/
inductive Reach (p : RawProg) : Nat → Config → Config → Prop where
  | refl (c : Config) : Reach p 0 c c
  | cons {n : Nat} {c c' c'' : Config} : Raw.step p c = next c' → Reach p n c' c'' → Reach p (n + 1) c c''

theorem Reach.trans {p : RawProg} {m n : Nat} {a b c : Config} (h1 : Reach p m a b) (h2 : Reach p n b c) :
    Reach p (m + n) a c := by
  induction h1 with
  | refl => simpa using h2
  | cons hs _ ih =>
    have := Reach.cons hs (ih h2)
    rwa [Nat.add_right_comm] at this

theorem Reach.single {p : RawProg} {c c' : Config} (h : Raw.step p c = next c') : Reach p 1 c c' :=
  Reach.cons h (Reach.refl c')

/-- `e` evaluates to `v` in `n` transitions under every continuation. -/
def Evals (p : RawProg) (env : List Val) (e : RawExpr) (v : Val) (n : Nat) : Prop :=
  ∀ k : List Frame, Reach p n ⟨.evalC env e, k⟩ ⟨.retC v, k⟩

/-- The rest of a list fold: from returning `acc` into a `foldI` frame over
    `xs`, to returning the result `r` into the frames below, in `n`. -/
def FoldRuns (p : RawProg) (env : List Val) (xs : List Val) (body : RawExpr) (acc r : Val) (n : Nat) : Prop :=
  ∀ k : List Frame, Reach p n ⟨.retC acc, .foldI env xs body :: k⟩ ⟨.retC r, k⟩

theorem ev_lit (p : RawProg) (env : List Val) (v : Val) (t : CoreTy) : Evals p env (.lit v t) v 1 :=
  fun _ => Reach.single rfl

theorem ev_var {p : RawProg} {env : List Val} {i : Int} {v : Val} (h : nth? env i = some v) :
    Evals p env (.var i) v 1 := by
  intro k
  apply Reach.single
  simp [step, evalStep, h, retTo]

theorem ev_let {p : RawProg} {env : List Val} {a b : RawExpr} {va vb : Val} {na nb : Nat}
    (ha : Evals p env a va na) (hb : Evals p (va :: env) b vb nb) :
    Evals p env (.letE a b) vb (na + nb + 2) := by
  intro k
  have h1 : Reach p 1 ⟨.evalC env (.letE a b), k⟩ ⟨.evalC env a, .letF env b :: k⟩ := Reach.single rfl
  have h2 : Reach p 1 ⟨.retC va, .letF env b :: k⟩ ⟨.evalC (va :: env) b, k⟩ := Reach.single rfl
  have := (h1.trans (ha _)).trans (h2.trans (hb k))
  rwa [show 1 + na + (1 + nb) = na + nb + 2 by omega] at this

theorem ev_if_true {p : RawProg} {env : List Val} {c th el : RawExpr} {v : Val} {nc nt : Nat}
    (hc : Evals p env c (.b 1) nc) (ht : Evals p env th v nt) :
    Evals p env (.ifE c th el) v (nc + nt + 2) := by
  intro k
  have h1 : Reach p 1 ⟨.evalC env (.ifE c th el), k⟩ ⟨.evalC env c, .ifF env th el :: k⟩ := Reach.single rfl
  have h2 : Reach p 1 ⟨.retC (.b 1), .ifF env th el :: k⟩ ⟨.evalC env th, k⟩ := Reach.single rfl
  have := (h1.trans (hc _)).trans (h2.trans (ht k))
  rwa [show 1 + nc + (1 + nt) = nc + nt + 2 by omega] at this

theorem ev_if_false {p : RawProg} {env : List Val} {c th el : RawExpr} {x : Int} {v : Val} {nc ne : Nat}
    (hc : Evals p env c (.b x) nc) (hx : x ≠ 1) (he : Evals p env el v ne) :
    Evals p env (.ifE c th el) v (nc + ne + 2) := by
  intro k
  have h1 : Reach p 1 ⟨.evalC env (.ifE c th el), k⟩ ⟨.evalC env c, .ifF env th el :: k⟩ := Reach.single rfl
  have h2 : Reach p 1 ⟨.retC (.b x), .ifF env th el :: k⟩ ⟨.evalC env el, k⟩ := by
    apply Reach.single; simp [step, retStep, evalTo, hx]
  have := (h1.trans (hc _)).trans (h2.trans (he k))
  rwa [show 1 + nc + (1 + ne) = nc + ne + 2 by omega] at this

theorem ev_field {p : RawProg} {env : List Val} {r : RawExpr} {i : Int} {fs : List Val} {x : Val} {nr : Nat}
    (hr : Evals p env r (.r fs) nr) (hx : nth? fs i = some x) :
    Evals p env (.field r i) x (nr + 2) := by
  intro k
  have h1 : Reach p 1 ⟨.evalC env (.field r i), k⟩ ⟨.evalC env r, .fieldF i :: k⟩ := Reach.single rfl
  have h2 : Reach p 1 ⟨.retC (.r fs), .fieldF i :: k⟩ ⟨.retC x, k⟩ := by
    apply Reach.single; simp [step, retStep, retTo, hx]
  have := (h1.trans (hr _)).trans h2
  rwa [show 1 + nr + 1 = nr + 2 by omega] at this

theorem ev_rec2 {p : RawProg} {env : List Val} {keys : List String} {f1 f2 : RawExpr} {v1 v2 : Val} {n1 n2 : Nat}
    (h1 : Evals p env f1 v1 n1) (h2 : Evals p env f2 v2 n2) :
    Evals p env (.recordE keys [f1, f2]) (.r [v1, v2]) (n1 + n2 + 3) := by
  intro k
  have s1 : Reach p 1 ⟨.evalC env (.recordE keys [f1, f2]), k⟩ ⟨.evalC env f1, .recF env [] [f2] :: k⟩ :=
    Reach.single rfl
  have s2 : Reach p 1 ⟨.retC v1, .recF env [] [f2] :: k⟩ ⟨.evalC env f2, .recF env [v1] [] :: k⟩ :=
    Reach.single rfl
  have s3 : Reach p 1 ⟨.retC v2, .recF env [v1] [] :: k⟩ ⟨.retC (.r [v1, v2]), k⟩ := Reach.single rfl
  have := (((s1.trans (h1 _)).trans s2).trans (h2 _)).trans s3
  rwa [show 1 + n1 + 1 + n2 + 1 = n1 + n2 + 3 by omega] at this

theorem ev_rec3 {p : RawProg} {env : List Val} {keys : List String} {f1 f2 f3 : RawExpr} {v1 v2 v3 : Val}
    {n1 n2 n3 : Nat} (h1 : Evals p env f1 v1 n1) (h2 : Evals p env f2 v2 n2) (h3 : Evals p env f3 v3 n3) :
    Evals p env (.recordE keys [f1, f2, f3]) (.r [v1, v2, v3]) (n1 + n2 + n3 + 4) := by
  intro k
  have s1 : Reach p 1 ⟨.evalC env (.recordE keys [f1, f2, f3]), k⟩ ⟨.evalC env f1, .recF env [] [f2, f3] :: k⟩ :=
    Reach.single rfl
  have s2 : Reach p 1 ⟨.retC v1, .recF env [] [f2, f3] :: k⟩ ⟨.evalC env f2, .recF env [v1] [f3] :: k⟩ :=
    Reach.single rfl
  have s3 : Reach p 1 ⟨.retC v2, .recF env [v1] [f3] :: k⟩ ⟨.evalC env f3, .recF env [v1, v2] [] :: k⟩ :=
    Reach.single rfl
  have s4 : Reach p 1 ⟨.retC v3, .recF env [v1, v2] [] :: k⟩ ⟨.retC (.r [v1, v2, v3]), k⟩ := Reach.single rfl
  have := (((((s1.trans (h1 _)).trans s2).trans (h2 _)).trans s3).trans (h3 _)).trans s4
  rwa [show 1 + n1 + 1 + n2 + 1 + n3 + 1 = n1 + n2 + n3 + 4 by omega] at this

theorem ev_nil (p : RawProg) (env : List Val) (t : CoreTy) : Evals p env (.nil t) (.l []) 1 :=
  fun _ => Reach.single rfl

theorem ev_cons {p : RawProg} {env : List Val} {h tl : RawExpr} {vh : Val} {xs : List Val} {nh nt : Nat}
    (hh : Evals p env h vh nh) (ht : Evals p env tl (.l xs) nt) :
    Evals p env (.cons h tl) (.l (vh :: xs)) (nh + nt + 3) := by
  intro k
  have s1 : Reach p 1 ⟨.evalC env (.cons h tl), k⟩ ⟨.evalC env h, .consH env tl :: k⟩ := Reach.single rfl
  have s2 : Reach p 1 ⟨.retC vh, .consH env tl :: k⟩ ⟨.evalC env tl, .consT vh :: k⟩ := Reach.single rfl
  have s3 : Reach p 1 ⟨.retC (.l xs), .consT vh :: k⟩ ⟨.retC (.l (vh :: xs)), k⟩ := Reach.single rfl
  have := (((s1.trans (hh _)).trans s2).trans (ht _)).trans s3
  rwa [show 1 + nh + 1 + nt + 1 = nh + nt + 3 by omega] at this

theorem ev_pair {p : RawProg} {env : List Val} {a b : RawExpr} {va vb : Val} {na nb : Nat}
    (ha : Evals p env a va na) (hb : Evals p env b vb nb) :
    Evals p env (.pair a b) (.p va vb) (na + nb + 3) := by
  intro k
  have s1 : Reach p 1 ⟨.evalC env (.pair a b), k⟩ ⟨.evalC env a, .pairL env b :: k⟩ := Reach.single rfl
  have s2 : Reach p 1 ⟨.retC va, .pairL env b :: k⟩ ⟨.evalC env b, .pairR va :: k⟩ := Reach.single rfl
  have s3 : Reach p 1 ⟨.retC vb, .pairR va :: k⟩ ⟨.retC (.p va vb), k⟩ := Reach.single rfl
  have := (((s1.trans (ha _)).trans s2).trans (hb _)).trans s3
  rwa [show 1 + na + 1 + nb + 1 = na + nb + 3 by omega] at this

/-- A binary primitive whose law returns a value (`ok 1`, `kind 0`). -/
theorem ev_prim2 {p : RawProg} {env : List Val} {op : String} {a b : RawExpr} {va vb v : Val} {na nb : Nat}
    {st : Int} (ha : Evals p env a va na) (hb : Evals p env b vb nb)
    (ho : scmPrim 0 op [va, vb] 0 = ⟨1, 0, v, "", st, ""⟩) :
    Evals p env (.prim op [a, b]) v (na + nb + 3) := by
  intro k
  have s1 : Reach p 1 ⟨.evalC env (.prim op [a, b]), k⟩ ⟨.evalC env a, .argsF env 0 op 0 [] [b] :: k⟩ :=
    Reach.single rfl
  have s2 : Reach p 1 ⟨.retC va, .argsF env 0 op 0 [] [b] :: k⟩ ⟨.evalC env b, .argsF env 0 op 0 [va] [] :: k⟩ :=
    Reach.single rfl
  have s3 : Reach p 1 ⟨.retC vb, .argsF env 0 op 0 [va] [] :: k⟩ ⟨.retC v, k⟩ := by
    apply Reach.single
    simp only [step, retStep]
    simp [ho, retTo]
  have := (((s1.trans (ha _)).trans s2).trans (hb _)).trans s3
  rwa [show 1 + na + 1 + nb + 1 = na + nb + 3 by omega] at this

/-- Transport `Evals` across equal results and counts. -/
theorem Evals.cast {p : RawProg} {env : List Val} {e : RawExpr} {v v' : Val} {n n' : Nat}
    (h : Evals p env e v n) (hv : v = v') (hn : n = n') : Evals p env e v' n' := by
  subst hv hn; exact h

/-- A handler around a body that returns: the handler frame is popped. -/
theorem ev_handle {p : RawProg} {env : List Val} {r : String} {body h : RawExpr} {v : Val} {nb : Nat}
    (hb : Evals p env body v nb) : Evals p env (.handle r body h) v (nb + 2) := by
  intro k
  have s1 : Reach p 1 ⟨.evalC env (.handle r body h), k⟩ ⟨.evalC env body, .handleF r env h :: k⟩ :=
    Reach.single rfl
  have s2 : Reach p 1 ⟨.retC v, .handleF r env h :: k⟩ ⟨.retC v, k⟩ := Reach.single rfl
  have := ((s1.trans (hb _)).trans s2)
  rwa [show 1 + nb + 1 = nb + 2 by omega] at this

theorem foldRuns_nil (p : RawProg) (env : List Val) (body : RawExpr) (acc : Val) :
    FoldRuns p env [] body acc acc 1 :=
  fun _ => Reach.single rfl

theorem foldRuns_cons {p : RawProg} {env : List Val} {x : Val} {xs : List Val} {body : RawExpr}
    {acc acc' r : Val} {nb m : Nat} (hb : Evals p (x :: acc :: env) body acc' nb)
    (hrest : FoldRuns p env xs body acc' r m) :
    FoldRuns p env (x :: xs) body acc r (nb + m + 1) := by
  intro k
  have s1 : Reach p 1 ⟨.retC acc, .foldI env (x :: xs) body :: k⟩ ⟨.evalC (x :: acc :: env) body, .foldI env xs body :: k⟩ :=
    Reach.single rfl
  have := (s1.trans (hb _)).trans (hrest k)
  rwa [show 1 + nb + m = nb + m + 1 by omega] at this

theorem ev_fold {p : RawProg} {env : List Val} {l init body : RawExpr} {xs : List Val} {v0 r : Val}
    {nl ni m : Nat} (hl : Evals p env l (.l xs) nl) (hi : Evals p env init v0 ni)
    (hf : FoldRuns p env xs body v0 r m) :
    Evals p env (.fold l init body) r (nl + ni + m + 2) := by
  intro k
  have s1 : Reach p 1 ⟨.evalC env (.fold l init body), k⟩ ⟨.evalC env l, .foldL env init body :: k⟩ :=
    Reach.single rfl
  have s2 : Reach p 1 ⟨.retC (.l xs), .foldL env init body :: k⟩ ⟨.evalC env init, .foldI env xs body :: k⟩ :=
    Reach.single rfl
  have := (((s1.trans (hl _)).trans s2).trans (hi _)).trans (hf k)
  rwa [show 1 + nl + 1 + ni + m = nl + ni + m + 2 by omega] at this

/-- A configuration returning into no frame is final: the runner stops there. -/
theorem step_ret_nil (p : RawProg) (v : Val) : step p ⟨.retC v, []⟩ = final 1 v "" := rfl

end Rcic.Scm.Raw
