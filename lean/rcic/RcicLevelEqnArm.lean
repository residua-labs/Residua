/-
RM-023 slice 3 (revised on `ScmRun` + `RcicLevelEqnStep`) — `StepRefines`
on the whole `levelEqual` arm over `stepI`.

`eqnImpl L` runs the typed program `eqnProg L`, whose entry is `levelEqnCore`
(`levelEqnCore.erase = levelEqnBody` from `RcicLevelEqnImage`), with `refuseCore`
and `okCore` at indices 1 and 6 and the four leaf bodies (`paramsBody`,
`unionBody`, `subsetsBody`, `allNoneBody`) from `L : LeafBodies` at indices
2..5. `encodeState` writes only `entryEnv l1 l2` (`[levelStr l1, levelStr l2, 0]`)
and `levelEqnCore`; it computes no equality decision (`encodeState_zero_ne_max_zero`).
`ScmLeavesAgree L` states that the four leaf bodies in `eqnProg L` evaluate on
`stepI` (`EvalsI`) to `paramsOf`, `unionNat`, `allSubsets`, `allNoneAgree`,
on the checked-bound domain (`natsIn64`/`setsIn64`/`levelIn64`) where the
`natsVal` encoding is exact — the unbounded quantifier was uninhabitable
(`union_evals_unbounded_impossible`, audit P1 on #7134). `StepRefines` is
proved on `levelDom64`, the in-range slice of `levelDom`.
`closure_claim` stays 0.
-/
import rcic.RcicLevelEqnImage
import rcic.RcicLevelEqnStep
import rcic.RcicScmRefinement
import rcic.ScmRun

namespace Rcic.LevelEqnArm

open Rcic.Scm
open Rcic.Declarative hiding denote
open Rcic.LevelKind
open Rcic.LevelEqnImage
open Rcic.LevelEqnStep
open Rcic.ScmRefinement
open Rcic.Machine

def h1 : inI64 1 := ⟨by decide, by decide⟩

def natCore (n : Nat) : CoreVal .i64 :=
  if h : inI64 (Int.ofNat n) then .i64V (Int.ofNat n) h else .i64V 0 h0

def natsCore : List Nat → CoreList .i64
  | [] => .nil
  | n :: xs => .cons (natCore n) (natsCore xs)

def natsVal (xs : List Nat) : CoreVal natListTy := .listV (natsCore xs)

def setsCore : List (List Nat) → CoreList natListTy
  | [] => .nil
  | xs :: xss => .cons (natsVal xs) (setsCore xss)

def setsVal (xss : List (List Nat)) : CoreVal (.list natListTy) := .listV (setsCore xss)

def paramsVal (xs : List Nat) : CoreVal paramsTy :=
  .recordV (.cons (.i64V 1 h1) (.cons (natsVal xs) (.cons (.strV "") .nil)))

def okRecVal (v : CoreVal .i64) : CoreVal resTy :=
  .recordV (.cons (.i64V 1 h1) (.cons v (.cons (.strV "") .nil)))

def refuseRecVal (c : String) : CoreVal resTy :=
  .recordV (.cons (.i64V 0 h0) (.cons (.i64V 0 h0) (.cons (.strV c) .nil)))

def verdictVal (b : Bool) : CoreVal resTy :=
  if b then okRecVal (.i64V 1 h1) else refuseRecVal "[rcic_level_not_equal]"

/-! ## Checked bounds for the `natsVal`/`setsVal` encoding

`natCore` is exact only inside `inI64`: out-of-range `Nat`s collapse onto
`0`. `ScmLeavesAgree` therefore quantifies its list-valued leaf arguments
over `natsIn64`/`setsIn64` only (independent audit, #7134, 2026-10-15T05:15Z
P1); `union_evals_unbounded_impossible` pins the contradiction the
unbounded quantifier carried. `levelIn64 l` bounds `l`'s parameter indices
(`paramsOf l` are what get i64-encoded); the entry encoding `levelStr` is a
string, so `imax`/payload positions need no bound. -/

def natIn64 (n : Nat) : Prop := inI64 (Int.ofNat n)

instance (n : Nat) : Decidable (natIn64 n) :=
  inferInstanceAs (Decidable (inI64 _))

def natsIn64 (xs : List Nat) : Prop := ∀ x ∈ xs, natIn64 x

def setsIn64 (xss : List (List Nat)) : Prop := ∀ xs ∈ xss, natsIn64 xs

def levelIn64 (l : Level) : Prop := natsIn64 (paramsOf l)

theorem mem_insertNat (i x : Nat) {xs : List Nat} (h : x ∈ insertNat i xs) :
    x = i ∨ x ∈ xs := by
  induction xs with
  | nil => exact Or.inl (List.mem_singleton.mp h)
  | cons j js ih =>
      simp only [insertNat] at h
      split at h
      · next heq =>
          exact (List.mem_cons.mp h).elim
            (fun e => Or.inl (e.trans (of_decide_eq_true heq).symm))
            (fun h' => Or.inr (List.mem_cons_of_mem _ h'))
      · split at h
        · exact List.mem_cons.mp h
        · exact (List.mem_cons.mp h).elim
            (fun e => Or.inr (List.mem_cons.mpr (Or.inl e)))
            (fun h' => (ih h').elim Or.inl
              (fun h'' => Or.inr (List.mem_cons_of_mem _ h'')))

theorem natsIn64_insertNat {i : Nat} {xs : List Nat}
    (hi : natIn64 i) (hxs : natsIn64 xs) : natsIn64 (insertNat i xs) :=
  fun x h => (mem_insertNat i x h).elim (fun e => e.symm ▸ hi) (hxs x)

theorem natsIn64_foldInsertNat {xs : List Nat} :
    ∀ (acc : List Nat), natsIn64 acc → natsIn64 xs →
      natsIn64 (foldInsertNat acc xs) := by
  induction xs with
  | nil => exact fun _ hacc _ => hacc
  | cons x xs ih =>
      intro acc hacc hxs
      exact ih _ (natsIn64_insertNat (hxs x (List.mem_cons_self _ _)) hacc)
        (fun y hy => hxs y (List.mem_cons_of_mem _ hy))

theorem natsIn64_unionNat {xs ys : List Nat} (hxs : natsIn64 xs) (hys : natsIn64 ys) :
    natsIn64 (unionNat xs ys) :=
  natsIn64_foldInsertNat xs hxs hys

theorem mem_consEach {i : Nat} {ys : List Nat} {xss : List (List Nat)}
    (h : ys ∈ consEach i xss) : ∃ zs ∈ xss, ys = i :: zs := by
  induction xss with
  | nil => cases h
  | cons xs xss ih =>
      cases List.mem_cons.mp h with
      | inl e => exact ⟨xs, List.mem_cons_self _ _, e⟩
      | inr h' =>
          obtain ⟨zs, hzs, e⟩ := ih h'
          exact ⟨zs, List.mem_cons_of_mem _ hzs, e⟩

theorem sublist_allSubsets (xs : List Nat) :
    ∀ ys ∈ allSubsets xs, ∀ y ∈ ys, y ∈ xs := by
  induction xs with
  | nil =>
      intro ys hys y hy
      rw [show allSubsets [] = [[]] from rfl, List.mem_singleton] at hys
      exact hys ▸ hy
  | cons i is ih =>
      intro ys hys y hy
      rw [show allSubsets (i :: is) =
        allSubsets is ++ consEach i (allSubsets is) from rfl] at hys
      cases List.mem_append.mp hys with
      | inl h => exact List.mem_cons_of_mem i (ih ys h y hy)
      | inr h =>
          obtain ⟨zs, hzs, e⟩ := mem_consEach h
          subst e
          cases List.mem_cons.mp hy with
          | inl e => exact List.mem_cons.mpr (Or.inl e)
          | inr h' => exact List.mem_cons_of_mem i (ih zs hzs y h')

theorem setsIn64_allSubsets {xs : List Nat} (hxs : natsIn64 xs) :
    setsIn64 (allSubsets xs) :=
  fun ys hys y hy => hxs y (sublist_allSubsets xs ys hys y hy)

/-! ## Signature and intrinsic composer bodies -/

def fnEqn : FnSig := ⟨[levelTy, levelTy, .i64], resTy⟩
def fnRefuse : FnSig := ⟨[strTy], resTy⟩
def fnParams : FnSig := ⟨[levelTy], paramsTy⟩
def fnUnion : FnSig := ⟨[natListTy, natListTy], natListTy⟩
def fnSubsets : FnSig := ⟨[natListTy], .list natListTy⟩
def fnAllNone : FnSig := ⟨[levelTy, levelTy, natListTy, .list natListTy, .i64], resTy⟩
def fnOk : FnSig := ⟨[.i64], resTy⟩

def S_eqn (extra : List FnSig) (cat : List CatalogEntry) : Sig :=
  ⟨fnEqn :: fnRefuse :: fnParams :: fnUnion :: fnSubsets :: fnAllNone :: fnOk :: extra, [], cat⟩

section Builders
variable {extra : List FnSig} {cat : List CatalogEntry} {Γ : List CoreTy}

def cLitI0 : CoreExpr (S_eqn extra cat) Γ .i64 := .lit (.i64V 0 h0)
def cLitI1 : CoreExpr (S_eqn extra cat) Γ .i64 := .lit (.i64V 1 h1)
def cLitS (s : String) : CoreExpr (S_eqn extra cat) Γ strTy := .lit (.strV s)
def cEq (a b : CoreExpr (S_eqn extra cat) Γ .i64) : CoreExpr (S_eqn extra cat) Γ .bool :=
  .prim .eq (.cons a (.cons b .nil))
def cLt (a b : CoreExpr (S_eqn extra cat) Γ .i64) : CoreExpr (S_eqn extra cat) Γ .bool :=
  .prim .lt (.cons a (.cons b .nil))

def cRefuse (e : CoreExpr (S_eqn extra cat) Γ strTy) : CoreExpr (S_eqn extra cat) Γ resTy :=
  .call (.local 1 fnRefuse rfl) (.cons e .nil)
def cParams (e : CoreExpr (S_eqn extra cat) Γ levelTy) : CoreExpr (S_eqn extra cat) Γ paramsTy :=
  .call (.local 2 fnParams rfl) (.cons e .nil)
def cUnion (a b : CoreExpr (S_eqn extra cat) Γ natListTy) : CoreExpr (S_eqn extra cat) Γ natListTy :=
  .call (.local 3 fnUnion rfl) (.cons a (.cons b .nil))
def cSubsets (a : CoreExpr (S_eqn extra cat) Γ natListTy) :
    CoreExpr (S_eqn extra cat) Γ (.list natListTy) :=
  .call (.local 4 fnSubsets rfl) (.cons a .nil)
def cAllNone (l1 l2 : CoreExpr (S_eqn extra cat) Γ levelTy)
    (p : CoreExpr (S_eqn extra cat) Γ natListTy)
    (ns : CoreExpr (S_eqn extra cat) Γ (.list natListTy))
    (f : CoreExpr (S_eqn extra cat) Γ .i64) : CoreExpr (S_eqn extra cat) Γ resTy :=
  .call (.local 5 fnAllNone rfl) (.cons l1 (.cons l2 (.cons p (.cons ns (.cons f .nil)))))
def cOk (e : CoreExpr (S_eqn extra cat) Γ .i64) : CoreExpr (S_eqn extra cat) Γ resTy :=
  .call (.local 6 fnOk rfl) (.cons e .nil)

def paramsFs : List (String × CoreTy) := [("ok", i64), ("params", natListTy), ("code", strTy)]
def resFs : List (String × CoreTy) := [("ok", i64), ("val", i64), ("code", strTy)]

def pOk (e : CoreExpr (S_eqn extra cat) Γ paramsTy) : CoreExpr (S_eqn extra cat) Γ .i64 :=
  .fieldE (fs := paramsFs) 0 "ok" rfl e
def pList (e : CoreExpr (S_eqn extra cat) Γ paramsTy) : CoreExpr (S_eqn extra cat) Γ natListTy :=
  .fieldE (fs := paramsFs) 1 "params" rfl e
def pCode (e : CoreExpr (S_eqn extra cat) Γ paramsTy) : CoreExpr (S_eqn extra cat) Γ strTy :=
  .fieldE (fs := paramsFs) 2 "code" rfl e

def rOk (e : CoreExpr (S_eqn extra cat) Γ resTy) : CoreExpr (S_eqn extra cat) Γ .i64 :=
  .fieldE (fs := resFs) 0 "ok" rfl e
def rVal (e : CoreExpr (S_eqn extra cat) Γ resTy) : CoreExpr (S_eqn extra cat) Γ .i64 :=
  .fieldE (fs := resFs) 1 "val" rfl e
def rCode (e : CoreExpr (S_eqn extra cat) Γ resTy) : CoreExpr (S_eqn extra cat) Γ strTy :=
  .fieldE (fs := resFs) 2 "code" rfl e
end Builders

/-- `scm/rcic/level_eqn.scm` as an intrinsic `CoreExpr`. -/
def levelEqnCore {extra : List FnSig} {cat : List CatalogEntry} :
    CoreExpr (S_eqn extra cat) [levelTy, levelTy, .i64] resTy :=
  .ifE (cLt (.var 2 rfl) cLitI0)
    (cRefuse (cLitS "[rcic_level_fuel]"))
    (.letE (cParams (.var 0 rfl))
      (.ifE (cEq (pOk (.var 0 rfl)) cLitI0)
        (cRefuse (pCode (.var 0 rfl)))
        (.letE (cParams (.var 2 rfl))
          (.ifE (cEq (pOk (.var 0 rfl)) cLitI0)
            (cRefuse (pCode (.var 0 rfl)))
            (.letE (cUnion (pList (.var 1 rfl)) (pList (.var 0 rfl)))
              (.letE (cSubsets (.var 0 rfl))
                (.letE (cAllNone (.var 4 rfl) (.var 5 rfl) (.var 1 rfl) (.var 0 rfl) (.var 6 rfl))
                  (.ifE (cEq (rOk (.var 0 rfl)) cLitI0)
                    (cRefuse (rCode (.var 0 rfl)))
                    (.ifE (cEq (rVal (.var 0 rfl)) cLitI1)
                      (cOk cLitI1)
                      (cRefuse (cLitS "[rcic_level_not_equal]")))))))))))

def refuseCore {extra : List FnSig} {cat : List CatalogEntry} :
    CoreExpr (S_eqn extra cat) [strTy] resTy :=
  .recordE (.cons "ok" cLitI0 (.cons "val" cLitI0 (.cons "code" (.var 0 rfl) .nil))) rfl

def okCore {extra : List FnSig} {cat : List CatalogEntry} :
    CoreExpr (S_eqn extra cat) [.i64] resTy :=
  .recordE (.cons "ok" cLitI1 (.cons "val" (.var 0 rfl) (.cons "code" (cLitS "") .nil))) rfl

def inlinedAcceptCore {extra : List FnSig} {cat : List CatalogEntry} :
    CoreExpr (S_eqn extra cat) [levelTy, levelTy, .i64] resTy :=
  cOk cLitI1

theorem levelEqnCore_erase {extra : List FnSig} {cat : List CatalogEntry} :
    (levelEqnCore (extra := extra) (cat := cat)).erase = levelEqnBody := rfl

theorem refuseCore_erase {extra : List FnSig} {cat : List CatalogEntry} :
    (refuseCore (extra := extra) (cat := cat)).erase =
      .recordE ["ok", "val", "code"] [li 0, li 0, v 0] := rfl

theorem okCore_erase {extra : List FnSig} {cat : List CatalogEntry} :
    (okCore (extra := extra) (cat := cat)).erase =
      .recordE ["ok", "val", "code"] [li 1, v 0, ls ""] := rfl

theorem inlinedAcceptCore_erase {extra : List FnSig} {cat : List CatalogEntry} :
    (inlinedAcceptCore (extra := extra) (cat := cat)).erase = inlinedAccept := rfl

#print axioms Rcic.LevelEqnArm.levelEqnCore_erase
#print axioms Rcic.LevelEqnArm.refuseCore_erase
#print axioms Rcic.LevelEqnArm.okCore_erase
#print axioms Rcic.LevelEqnArm.inlinedAcceptCore_erase

/-! ## Small-step evaluation over `stepI` (`EvalsI`) -/

theorem step1 {S : Sig} {T : CoreTy} {prog : Bodies S S.fns}
    {c c' : Config S T} (hs : stepI prog c = .next c') :
    SCMRuns prog 1 c c' :=
  SCMRuns.step hs (SCMRuns.refl c')

theorem stepL {S : Sig} {T : CoreTy} {prog : Bodies S S.fns}
    {n : Nat} {c c' c'' : Config S T}
    (hr : SCMRuns prog n c' c'') (hs : stepI prog c = .next c') :
    SCMRuns prog (n + 1) c c'' :=
  SCMRuns.step hs hr

/-- `e` in `env` steps under `stepI prog` to `.retC v` in `n` transitions
for every continuation `k`. -/
abbrev EvalsI {S : Sig} (prog : Bodies S S.fns) {Γ : List CoreTy} {A : CoreTy}
    (env : CoreVals Γ) (e : CoreExpr S Γ A) (v : CoreVal A) (n : Nat) : Prop :=
  ∀ {T : CoreTy} (k : Cont S A T),
    SCMRuns prog n ⟨A, .evalC env e, k⟩ ⟨A, .retC v, k⟩

section EvalsLemmas
variable {S : Sig} {prog : Bodies S S.fns} {Γ : List CoreTy} {env : CoreVals Γ}

theorem evI_lit {A : CoreTy} {v w : CoreVal A} (hv : v = w := by rfl) :
    EvalsI prog env (.lit v) w 1 :=
  hv ▸ fun _ => step1 rfl

theorem evI_var {A : CoreTy} {i : Nat} {h : Γ.get? i = some A} {v : CoreVal A}
    (hv : env.get i h = v := by rfl) :
    EvalsI prog env (.var i h) v 1 :=
  hv ▸ fun _ => step1 rfl

theorem evI_let {A B : CoreTy} {a : CoreExpr S Γ A} {b : CoreExpr S (A :: Γ) B}
    {va : CoreVal A} {vb : CoreVal B} {na nb : Nat}
    (ha : EvalsI prog env a va na) (hb : EvalsI prog (.cons va env) b vb nb) :
    EvalsI prog env (.letE a b) vb ((na + (nb + 1)) + 1) :=
  fun k => stepL (SCMRuns.trans (ha (.cons (.letF env b) k)) (stepL (hb k) rfl)) rfl

theorem evI_if_true {A : CoreTy} {c : CoreExpr S Γ .bool} {th el : CoreExpr S Γ A}
    {v : CoreVal A} {nc nt : Nat}
    (hc : EvalsI prog env c (.boolV true) nc) (ht : EvalsI prog env th v nt) :
    EvalsI prog env (.ifE c th el) v ((nc + (nt + 1)) + 1) :=
  fun k => stepL (SCMRuns.trans (hc (.cons (.ifF env th el) k)) (stepL (ht k) rfl)) rfl

theorem evI_if_false {A : CoreTy} {c : CoreExpr S Γ .bool} {th el : CoreExpr S Γ A}
    {v : CoreVal A} {nc ne : Nat}
    (hc : EvalsI prog env c (.boolV false) nc) (he : EvalsI prog env el v ne) :
    EvalsI prog env (.ifE c th el) v ((nc + (ne + 1)) + 1) :=
  fun k => stepL (SCMRuns.trans (hc (.cons (.ifF env th el) k)) (stepL (he k) rfl)) rfl

theorem evI_field {fs : List (String × CoreTy)} {A : CoreTy}
    {i : Nat} {key : String} {h : fs.get? i = some (key, A)}
    {r : CoreExpr S Γ (.record fs)} {xs : CoreVals (fs.map Prod.snd)}
    {v : CoreVal A} {nr : Nat}
    (hr : EvalsI prog env r (.recordV xs) nr)
    (hv : recordField fs xs i h = v := by rfl) :
    EvalsI prog env (.fieldE (fs := fs) i key h r) v ((nr + 1) + 1) :=
  hv ▸ fun k => stepL (SCMRuns.trans (hr (.cons (.fieldF i key h) k)) (step1 rfl)) rfl

theorem evI_rec3 {k1 k2 k3 : String} {A1 A2 A3 : CoreTy}
    {e1 : CoreExpr S Γ A1} {e2 : CoreExpr S Γ A2} {e3 : CoreExpr S Γ A3}
    {v1 : CoreVal A1} {v2 : CoreVal A2} {v3 : CoreVal A3} {n1 n2 n3 : Nat}
    (h1 : EvalsI prog env e1 v1 n1)
    (h2 : EvalsI prog env e2 v2 n2)
    (h3 : EvalsI prog env e3 v3 n3)
    (hk : keysUnique ([(k1, A1), (k2, A2), (k3, A3)].map Prod.fst) = true) :
    EvalsI prog env
      (.recordE (fs := [(k1, A1), (k2, A2), (k3, A3)])
        (.cons k1 e1 (.cons k2 e2 (.cons k3 e3 .nil))) hk)
      (.recordV (.cons v1 (.cons v2 (.cons v3 .nil))))
      ((n1 + ((n2 + ((n3 + 1) + 1)) + 1)) + 1) :=
  fun k =>
    stepL (SCMRuns.trans
      (h1 (.cons (.recF [(k1, A1), (k2, A2), (k3, A3)] [] [(k2, A2), (k3, A3)]
        k1 rfl env .nil (.cons k2 e2 (.cons k3 e3 .nil))) k))
      (stepL (SCMRuns.trans
        (h2 (.cons (.recF [(k1, A1), (k2, A2), (k3, A3)] [(k1, A1)] [(k3, A3)]
          k2 rfl env (.cons v1 .nil) (.cons k3 e3 .nil)) k))
        (stepL (SCMRuns.trans
          (h3 (.cons (.recF [(k1, A1), (k2, A2), (k3, A3)] [(k1, A1), (k2, A2)] []
            k3 rfl env (.cons v1 (.cons v2 .nil)) .nil) k))
          (step1 rfl)) rfl)) rfl)) rfl

theorem evI_eq {a b : CoreExpr S Γ .i64} {x y : Int} {hx : inI64 x} {hy : inI64 y}
    {r : Bool} {na nb : Nat}
    (ha : EvalsI prog env a (.i64V x hx) na) (hb : EvalsI prog env b (.i64V y hy) nb)
    (hr : (x == y) = r := by rfl) :
    EvalsI prog env (.prim .eq (.cons a (.cons b .nil))) (.boolV r)
      ((na + ((nb + 1) + 1)) + 1) :=
  hr ▸ fun k =>
    stepL (SCMRuns.trans
      (ha (.cons (.primArgsF .eq [] [.i64] rfl env .nil (.cons b .nil)) k))
      (stepL (SCMRuns.trans
        (hb (.cons (.primArgsF .eq [.i64] [] rfl env (.cons (.i64V x hx) .nil) .nil) k))
        (step1 rfl)) rfl)) rfl

theorem evI_lt {a b : CoreExpr S Γ .i64} {x y : Int} {hx : inI64 x} {hy : inI64 y}
    {r : Bool} {na nb : Nat}
    (ha : EvalsI prog env a (.i64V x hx) na) (hb : EvalsI prog env b (.i64V y hy) nb)
    (hr : decide (x < y) = r := by rfl) :
    EvalsI prog env (.prim .lt (.cons a (.cons b .nil))) (.boolV r)
      ((na + ((nb + 1) + 1)) + 1) :=
  hr ▸ fun k =>
    stepL (SCMRuns.trans
      (ha (.cons (.primArgsF .lt [] [.i64] rfl env .nil (.cons b .nil)) k))
      (stepL (SCMRuns.trans
        (hb (.cons (.primArgsF .lt [.i64] [] rfl env (.cons (.i64V x hx) .nil) .nil) k))
        (step1 rfl)) rfl)) rfl

theorem evI_add {a b : CoreExpr S Γ .i64} {x y : Int} {hx : inI64 x} {hy : inI64 y}
    {hz : inI64 (x + y)} {na nb : Nat}
    (ha : EvalsI prog env a (.i64V x hx) na) (hb : EvalsI prog env b (.i64V y hy) nb) :
    EvalsI prog env (.prim .add (.cons a (.cons b .nil))) (.i64V (x + y) hz)
      ((na + ((nb + 1) + 1)) + 1) :=
  fun k =>
    stepL (SCMRuns.trans
      (ha (.cons (.primArgsF .add [] [.i64] rfl env .nil (.cons b .nil)) k))
      (stepL (SCMRuns.trans
        (hb (.cons (.primArgsF .add [.i64] [] rfl env (.cons (.i64V x hx) .nil) .nil) k))
        (step1 (by
          simp only [stepI, retI, CoreVals.snoc, primSig, primLaw, checkedI64,
            dif_pos hz, nxt]))) rfl)) rfl

theorem evI_call1 {A1 R : CoreTy} {i : Nat} {hf : S.fns.get? i = some ⟨[A1], R⟩}
    {e1 : CoreExpr S Γ A1} {v1 : CoreVal A1} {w : CoreVal R} {n1 nb : Nat}
    (h1 : EvalsI prog env e1 v1 n1)
    (hb : EvalsI prog (.cons v1 .nil) (prog.at i ⟨[A1], R⟩ hf) w nb) :
    EvalsI prog env (.call (.local i ⟨[A1], R⟩ hf) (.cons e1 .nil)) w
      ((n1 + ((nb + 1) + 1)) + 1) :=
  fun k =>
    stepL (SCMRuns.trans
      (h1 (.cons (.callArgsF i ⟨[A1], R⟩ hf [] [] rfl env .nil .nil) k))
      (stepL (SCMRuns.trans (hb (.cons .retF k)) (step1 rfl)) rfl)) rfl

theorem evI_call2 {A1 A2 R : CoreTy} {i : Nat} {hf : S.fns.get? i = some ⟨[A1, A2], R⟩}
    {e1 : CoreExpr S Γ A1} {e2 : CoreExpr S Γ A2}
    {v1 : CoreVal A1} {v2 : CoreVal A2} {w : CoreVal R} {n1 n2 nb : Nat}
    (h1 : EvalsI prog env e1 v1 n1) (h2 : EvalsI prog env e2 v2 n2)
    (hb : EvalsI prog (.cons v1 (.cons v2 .nil)) (prog.at i ⟨[A1, A2], R⟩ hf) w nb) :
    EvalsI prog env (.call (.local i ⟨[A1, A2], R⟩ hf) (.cons e1 (.cons e2 .nil))) w
      ((n1 + ((n2 + ((nb + 1) + 1)) + 1)) + 1) :=
  fun k =>
    stepL (SCMRuns.trans
      (h1 (.cons (.callArgsF i ⟨[A1, A2], R⟩ hf [] [A2] rfl env .nil (.cons e2 .nil)) k))
      (stepL (SCMRuns.trans
        (h2 (.cons (.callArgsF i ⟨[A1, A2], R⟩ hf [A1] [] rfl env (.cons v1 .nil) .nil) k))
        (stepL (SCMRuns.trans (hb (.cons .retF k)) (step1 rfl)) rfl)) rfl)) rfl

theorem evI_call5 {A1 A2 A3 A4 A5 R : CoreTy} {i : Nat}
    {hf : S.fns.get? i = some ⟨[A1, A2, A3, A4, A5], R⟩}
    {e1 : CoreExpr S Γ A1} {e2 : CoreExpr S Γ A2} {e3 : CoreExpr S Γ A3}
    {e4 : CoreExpr S Γ A4} {e5 : CoreExpr S Γ A5}
    {v1 : CoreVal A1} {v2 : CoreVal A2} {v3 : CoreVal A3}
    {v4 : CoreVal A4} {v5 : CoreVal A5} {w : CoreVal R}
    {n1 n2 n3 n4 n5 nb : Nat}
    (h1 : EvalsI prog env e1 v1 n1) (h2 : EvalsI prog env e2 v2 n2)
    (h3 : EvalsI prog env e3 v3 n3) (h4 : EvalsI prog env e4 v4 n4)
    (h5 : EvalsI prog env e5 v5 n5)
    (hb : EvalsI prog (.cons v1 (.cons v2 (.cons v3 (.cons v4 (.cons v5 .nil)))))
      (prog.at i ⟨[A1, A2, A3, A4, A5], R⟩ hf) w nb) :
    EvalsI prog env
      (.call (.local i ⟨[A1, A2, A3, A4, A5], R⟩ hf)
        (.cons e1 (.cons e2 (.cons e3 (.cons e4 (.cons e5 .nil)))))) w
      ((n1 + ((n2 + ((n3 + ((n4 + ((n5 + ((nb + 1) + 1)) + 1)) + 1)) + 1)) + 1)) + 1) :=
  let f : FnSig := ⟨[A1, A2, A3, A4, A5], R⟩
  fun k =>
    stepL (SCMRuns.trans
      (h1 (.cons (.callArgsF i f hf [] [A2, A3, A4, A5] rfl env .nil
        (.cons e2 (.cons e3 (.cons e4 (.cons e5 .nil))))) k))
      (stepL (SCMRuns.trans
        (h2 (.cons (.callArgsF i f hf [A1] [A3, A4, A5] rfl env (.cons v1 .nil)
          (.cons e3 (.cons e4 (.cons e5 .nil)))) k))
        (stepL (SCMRuns.trans
          (h3 (.cons (.callArgsF i f hf [A1, A2] [A4, A5] rfl env (.cons v1 (.cons v2 .nil))
            (.cons e4 (.cons e5 .nil))) k))
          (stepL (SCMRuns.trans
            (h4 (.cons (.callArgsF i f hf [A1, A2, A3] [A5] rfl env
              (.cons v1 (.cons v2 (.cons v3 .nil))) (.cons e5 .nil)) k))
            (stepL (SCMRuns.trans
              (h5 (.cons (.callArgsF i f hf [A1, A2, A3, A4] [] rfl env
                (.cons v1 (.cons v2 (.cons v3 (.cons v4 .nil)))) .nil) k))
              (stepL (SCMRuns.trans (hb (.cons .retF k)) (step1 rfl)) rfl)) rfl)) rfl)) rfl)) rfl)) rfl
end EvalsLemmas

/-! ## Leaf bodies and full typed program `eqnProg` -/

structure LeafBodies where
  extra : List FnSig := []
  cat : List CatalogEntry := []
  paramsBody : CoreExpr (S_eqn extra cat) [levelTy] paramsTy
  unionBody : CoreExpr (S_eqn extra cat) [natListTy, natListTy] natListTy
  subsetsBody : CoreExpr (S_eqn extra cat) [natListTy] (.list natListTy)
  allNoneBody : CoreExpr (S_eqn extra cat) [levelTy, levelTy, natListTy, .list natListTy, .i64] resTy
  extraBodies : Bodies (S_eqn extra cat) extra

def eqnProg (L : LeafBodies) : Bodies (S_eqn L.extra L.cat) (S_eqn L.extra L.cat).fns :=
  .cons levelEqnCore
    (.cons refuseCore
      (.cons L.paramsBody
        (.cons L.unionBody
          (.cons L.subsetsBody
            (.cons L.allNoneBody
              (.cons okCore L.extraBodies))))))

def rawFns : {S : Sig} → {fs : List FnSig} → Bodies S fs → List RawFnDef
  | _, [], .nil => []
  | _, f :: _, .cons b bs => ⟨f.params, f.result, b.erase⟩ :: rawFns bs

def rawProgOf (L : LeafBodies) : RawProg :=
  ⟨rawFns (eqnProg L), [], L.cat, 0⟩

theorem rawFns_map_body {S : Sig} :
    ∀ {fs : List FnSig} (bs : Bodies S fs),
      (rawFns bs).map RawFnDef.body = ElabErase.Bodies.erasures bs
  | [], .nil => rfl
  | _ :: _, .cons b bs => congrArg (List.cons b.erase) (rawFns_map_body bs)

theorem eqnProg_erasures (L : LeafBodies) :
    ElabErase.Bodies.erasures (eqnProg L) = (rawProgOf L).fns.map RawFnDef.body :=
  (rawFns_map_body (eqnProg L)).symm

theorem refuseCore_evals {extra : List FnSig} {cat : List CatalogEntry}
    (prog : Bodies (S_eqn extra cat) (S_eqn extra cat).fns) (c : String) :
    EvalsI prog (.cons (.strV c) .nil) refuseCore (refuseRecVal c) 7 :=
  evI_rec3 (k1 := "ok") (k2 := "val") (k3 := "code")
    evI_lit evI_lit evI_var rfl

theorem okCore_evals {extra : List FnSig} {cat : List CatalogEntry}
    (prog : Bodies (S_eqn extra cat) (S_eqn extra cat).fns) (v : CoreVal .i64) :
    EvalsI prog (.cons v .nil) okCore (okRecVal v) 7 :=
  evI_rec3 (k1 := "ok") (k2 := "val") (k3 := "code")
    evI_lit evI_var evI_lit rfl

#print axioms Rcic.Scm.SCMRuns.trans
#print axioms Rcic.LevelEqnArm.step1
#print axioms Rcic.LevelEqnArm.stepL
#print axioms Rcic.LevelEqnArm.evI_lit
#print axioms Rcic.LevelEqnArm.evI_var
#print axioms Rcic.LevelEqnArm.evI_let
#print axioms Rcic.LevelEqnArm.evI_if_true
#print axioms Rcic.LevelEqnArm.evI_if_false
#print axioms Rcic.LevelEqnArm.evI_field
#print axioms Rcic.LevelEqnArm.evI_rec3
#print axioms Rcic.LevelEqnArm.evI_eq
#print axioms Rcic.LevelEqnArm.evI_lt
#print axioms Rcic.LevelEqnArm.evI_call1
#print axioms Rcic.LevelEqnArm.evI_call2
#print axioms Rcic.LevelEqnArm.evI_call5
#print axioms Rcic.LevelEqnArm.rawFns_map_body
#print axioms Rcic.LevelEqnArm.eqnProg_erasures
#print axioms Rcic.LevelEqnArm.refuseCore_evals
#print axioms Rcic.LevelEqnArm.okCore_evals

/-! ## `ScmLeavesAgree` and `stepI` execution of `levelEqnCore`

Anchor note (measured READ-ONLY against Fusion `#5507` F1/F2 and `#5933` M4 per
`BOOTSTRAP_OVERLAP.md`): `#5933` `integration/rcic-bootstrap/m4/` proves the 45-module
`level_eqn` leaf hierarchy (`M4ParamsResult`, `M4NatSetResult`, `M4SubsetsResult`,
`M4AllNoneResult`, `M4LevelEqnResult`, `M4EntryCompletion`) over `MSTNFSlotSemanticsCoreMWE.evalLF`,
and `#5507` plans F2 for full executable-checker alignment; neither states `StepRefines`
over `Rcic.Scm.stepI`. `ScmLeavesAgree` is the exact interface seam between this `stepI`
composer refinement and the leaf semantics (waiting on F2 / `evalLF`↔`stepI` leaf transport
rather than rebuilding the 40-module leaf tree in parallel). Repaired per the independent
audit on #7134 (2026-10-15T05:15Z): P1 — the leaf argument quantifiers are now
checked-bound (`natsIn64`/`setsIn64`), the only domain on which `natsVal` is exact; the
unbounded shape is refuted by `union_evals_unbounded_impossible`. P2 — the shared
concatenation lemma lives at `Rcic.Scm.SCMRuns.trans`. The joint inhabitant (real leaf
bodies for all in-range inputs) remains the F2 transport residual.

Re-audit status (#7134, 2026-10-15T14:52Z, audit lane 3): REFUSE stood on the
nonvacuity obligation alone — the repaired interface was acknowledged; the
verdict's disjunction was EITHER a joint `ScmLeavesAgree` supplier for all
four bodies on this wire OR an explicit scope ruling accepting only the
conditional seam.

SCOPE RULING (posted on #7134, 2026-10-15): the conditional seam is
ACCEPTED, with F2 leaf transport named and RM-023 staying PARTIAL, on one
condition — a non-vacuity witness: a concrete wire input where the leaf
obligations are PROVED and `levelEqual_stepRefines` runs. That witness is
`witness_agreeAt`/`witness_stepRefines` below: the pointwise predicate
`ScmLeavesAgreeAt` (the obligations instantiated at exactly the arguments
`composer_evalsI` consumes) is proved at `(.zero, .zero)` for
`witnessLeaves`, and `levelEqual_stepRefines_at` runs the same composer
path on `levelDomAt .zero .zero`. `ScmLeavesAgree` itself stays
uninhabited — the uniform supplier remains the F2 transport
(`scm/rcic/level_eqn_*` ported to `stepI` machines), and `closure_claim`
stays 0. `witness_not_agreeAt` refutes the pointwise predicate at
`(.param 0, .param 1)` — the same discriminating point as
`badLeaves_not_agree` — so the witness is evidence the seam fires
concretely, not a hollow inhabitant. -/

/-- The exact interface seam between this `stepI` composer refinement and
the leaf semantics, on the domain where the `natsVal`/`setsVal` encoding is
exact: every list argument is bounded by `natsIn64`/`setsIn64` (audit P1 —
the unbounded quantifier was uninhabitable, see
`union_evals_unbounded_impossible`). `levelStr` stays unbounded: it is a
lossless string encoding. A supplier must still deliver all four leaf bodies
for every in-range input — the joint inhabitant is the F2 leaf transport
(`scm/rcic/level_eqn_*.scm` on this wire), not yet linked. -/
structure ScmLeavesAgree (L : LeafBodies) : Prop where
  params_evals : ∀ (l : Level), levelIn64 l →
    ∃ n, EvalsI (eqnProg L) (.cons (levelStr l) .nil)
      L.paramsBody (paramsVal (paramsOf l)) n
  union_evals : ∀ (xs ys : List Nat), natsIn64 xs → natsIn64 ys →
    ∃ n, EvalsI (eqnProg L) (.cons (natsVal xs) (.cons (natsVal ys) .nil))
      L.unionBody (natsVal (unionNat xs ys)) n
  subsets_evals : ∀ (xs : List Nat), natsIn64 xs →
    ∃ n, EvalsI (eqnProg L) (.cons (natsVal xs) .nil)
      L.subsetsBody (setsVal (allSubsets xs)) n
  allNone_evals : ∀ (l1 l2 : Level) (ps : List Nat) (nss : List (List Nat)),
    natsIn64 ps → setsIn64 nss →
    ∃ n, EvalsI (eqnProg L)
      (.cons (levelStr l1) (.cons (levelStr l2)
        (.cons (natsVal ps) (.cons (setsVal nss) (.cons (.i64V 0 h0) .nil)))))
      L.allNoneBody
      (okRecVal (if allNoneAgree l1 l2 ps nss then .i64V 1 h1 else .i64V 0 h0)) n

/-- The pointwise seam: the five leaf obligations instantiated at exactly
the arguments `composer_evalsI` consumes for request `(l1, l2)`.
`ScmLeavesAgree` is this predicate uniformly quantified over the in-range
domain; the conditional theorems need only the instance — that is what the
non-vacuity witness `witness_agreeAt` discharges at `(.zero, .zero)`. -/
structure ScmLeavesAgreeAt (L : LeafBodies) (l1 l2 : Level) : Prop where
  params_evals_l1 : ∃ n, EvalsI (eqnProg L) (.cons (levelStr l1) .nil)
    L.paramsBody (paramsVal (paramsOf l1)) n
  params_evals_l2 : ∃ n, EvalsI (eqnProg L) (.cons (levelStr l2) .nil)
    L.paramsBody (paramsVal (paramsOf l2)) n
  union_evals : ∃ n, EvalsI (eqnProg L)
    (.cons (natsVal (paramsOf l1)) (.cons (natsVal (paramsOf l2)) .nil))
    L.unionBody (natsVal (unionNat (paramsOf l1) (paramsOf l2))) n
  subsets_evals : ∃ n, EvalsI (eqnProg L)
    (.cons (natsVal (unionNat (paramsOf l1) (paramsOf l2))) .nil)
    L.subsetsBody (setsVal (allSubsets (unionNat (paramsOf l1) (paramsOf l2)))) n
  allNone_evals : ∃ n, EvalsI (eqnProg L)
    (.cons (levelStr l1) (.cons (levelStr l2)
      (.cons (natsVal (unionNat (paramsOf l1) (paramsOf l2)))
        (.cons (setsVal (allSubsets (unionNat (paramsOf l1) (paramsOf l2))))
          (.cons (.i64V 0 h0) .nil)))))
    L.allNoneBody
    (okRecVal (if allNoneAgree l1 l2 (unionNat (paramsOf l1) (paramsOf l2))
        (allSubsets (unionNat (paramsOf l1) (paramsOf l2)))
      then .i64V 1 h1 else .i64V 0 h0)) n

theorem ScmLeavesAgree.at {L : LeafBodies} (h : ScmLeavesAgree L)
    {l1 l2 : Level} (hl1 : levelIn64 l1) (hl2 : levelIn64 l2) :
    ScmLeavesAgreeAt L l1 l2 where
  params_evals_l1 := h.params_evals l1 hl1
  params_evals_l2 := h.params_evals l2 hl2
  union_evals := h.union_evals (paramsOf l1) (paramsOf l2) hl1 hl2
  subsets_evals := h.subsets_evals _ (natsIn64_unionNat hl1 hl2)
  allNone_evals := h.allNone_evals l1 l2 _ _ (natsIn64_unionNat hl1 hl2)
    (setsIn64_allSubsets (natsIn64_unionNat hl1 hl2))

theorem tail_evalsI (L : LeafBodies)
    (env4 : CoreVals [.list natListTy, natListTy, paramsTy, paramsTy, levelTy, levelTy, .i64])
    (b : Bool) :
    ∃ n, EvalsI (eqnProg L)
      (.cons (okRecVal (if b then .i64V 1 h1 else .i64V 0 h0)) env4)
      (.ifE (cEq (rOk (.var 0 rfl)) cLitI0)
        (cRefuse (rCode (.var 0 rfl)))
        (.ifE (cEq (rVal (.var 0 rfl)) cLitI1)
          (cOk cLitI1)
          (cRefuse (cLitS "[rcic_level_not_equal]"))))
      (verdictVal b) n := by
  cases b with
  | true =>
    exact ⟨_, evI_if_false (evI_eq (evI_field evI_var) evI_lit)
      (evI_if_true (evI_eq (evI_field evI_var) evI_lit)
        (evI_call1 evI_lit (okCore_evals (eqnProg L) (.i64V 1 h1))))⟩
  | false =>
    exact ⟨_, evI_if_false (evI_eq (evI_field evI_var) evI_lit)
      (evI_if_false (evI_eq (evI_field evI_var) evI_lit)
        (evI_call1 evI_lit (refuseCore_evals (eqnProg L) "[rcic_level_not_equal]")))⟩

theorem composer_evalsI {L : LeafBodies} {l1 l2 : Level}
    (h : ScmLeavesAgreeAt L l1 l2) :
    ∃ n, EvalsI (eqnProg L) (entryEnv l1 l2) levelEqnCore (verdictVal (decEqN l1 l2)) n := by
  obtain ⟨np1, hp1⟩ := h.params_evals_l1
  obtain ⟨np2, hp2⟩ := h.params_evals_l2
  obtain ⟨nu, hu⟩ := h.union_evals
  obtain ⟨ns, hs⟩ := h.subsets_evals
  obtain ⟨na, ha⟩ := h.allNone_evals
  obtain ⟨nt, ht⟩ := tail_evalsI L _ (decEqN l1 l2)
  exact ⟨_, evI_if_false (evI_lt evI_var evI_lit)
    (evI_let (evI_call1 evI_var hp1)
      (evI_if_false (evI_eq (evI_field evI_var) evI_lit)
        (evI_let (evI_call1 evI_var hp2)
          (evI_if_false (evI_eq (evI_field evI_var) evI_lit)
            (evI_let (evI_call2 (evI_field evI_var) (evI_field evI_var) hu)
              (evI_let (evI_call1 evI_var hs)
                (evI_let (evI_call5 evI_var evI_var evI_var evI_var evI_var ha)
                  ht)))))))⟩

/-! ## RM-022 / RM-023 on the `levelEqual` arm over `stepI` -/

open Witness

def encodeLevels (s : RawState) : Level × Level :=
  match s.task with
  | .levelEqual l1 l2 => (l1, l2)
  | _ => (.zero, .zero)

/-- `encodeState` writes only `entryEnv l1 l2` (`[levelStr l1, levelStr l2, 0]`)
and `levelEqnCore`; it computes no equality decision. -/
def encodeState {extra : List FnSig} {cat : List CatalogEntry} (s : RawState) :
    Config (S_eqn extra cat) resTy :=
  let p := encodeLevels s
  ⟨resTy, .evalC (entryEnv p.1 p.2) levelEqnCore, .nil⟩

def resOkVal : CoreVal resTy → Int × Int × String
  | .recordV (.cons (.i64V ok _) (.cons (.i64V val _) (.cons (.strV code) .nil))) =>
    (ok, val, code)

def decodeRes {extra : List FnSig} {cat : List CatalogEntry} :
    Final (S_eqn extra cat) resTy → RunResult
  | .returned v =>
    let r := resOkVal v
    if r.1 == 1 && r.2.1 == 1 then .accepted .conversionConfirmed
    else .refused r.2.2
  | .raised _ _ _ => .integrity "[rcic_scm_core_row_safety]"

def eqnImpl (L : LeafBodies) : ScmImpl :=
  ⟨S_eqn L.extra L.cat, resTy, eqnProg L, encodeState, decodeRes⟩

def finalCfg {extra : List FnSig} {cat : List CatalogEntry} (b : Bool) :
    Config (S_eqn extra cat) resTy :=
  ⟨resTy, .retC (verdictVal b), .nil⟩

def eqnRel (L : LeafBodies) (s : RawState)
    (c : Config (S_eqn L.extra L.cat) resTy) : Prop :=
  levelDom s ∧ ∃ k, SCMRuns (eqnProg L) k c (finalCfg (levelBit s))

theorem encodeState_zero_ne_max_zero {extra : List FnSig} {cat : List CatalogEntry}
    (amb : Ambient) (b : Nat) :
    (encodeState ⟨amb, .levelEqual .zero .zero, b⟩ : Config (S_eqn extra cat) resTy) ≠
      encodeState ⟨amb, .levelEqual (.max .zero .zero) .zero, b⟩ := by
  intro h
  have hctl : (encodeState ⟨amb, .levelEqual .zero .zero, b⟩ :
      Config (S_eqn extra cat) resTy).erase.ctl =
    (encodeState ⟨amb, .levelEqual (.max .zero .zero) .zero, b⟩ :
      Config (S_eqn extra cat) resTy).erase.ctl := congrArg (fun c => c.erase.ctl) h
  dsimp [encodeState, encodeLevels, Config.erase, Control.erase, entryEnv,
    CoreVals.erase, levelStr, CoreVal.erase] at hctl
  injection hctl with henv _
  injection henv with hhead _
  injection hhead with henc
  have h1 := Inst.decLevel_self .zero
  rw [henc] at h1
  exact Level.noConfusion (Option.some.inj (h1.symm.trans (Inst.decLevel_self _)))

theorem decodeRes_verdict {extra : List FnSig} {cat : List CatalogEntry} (b : Bool) :
    decodeRes (extra := extra) (cat := cat) (.returned (verdictVal b)) =
      levelDecode (.returned (.boolV b)) := by
  cases b <;> rfl

theorem eqn_kernel {extra : List FnSig} {cat : List CatalogEntry}
    {s : RawState} (hd : levelDom s) :
    kernelStepRaw s =
      .result (decodeRes (extra := extra) (cat := cat)
        (.returned (verdictVal (levelBit s)))) := by
  rw [decodeRes_verdict]
  exact level_kernel hd

/-- The `levelDom` slice on which the checked-bound `ScmLeavesAgree` seam
applies: the two request levels' `paramsOf` must land in `i64`. -/
def levelDom64 (s : RawState) : Prop :=
  ∃ l1 l2 b, s.task = .levelEqual l1 l2 ∧ s.budget = b + 1 ∧
    levelIn64 l1 ∧ levelIn64 l2

theorem levelDom64_levelDom {s : RawState} (hd : levelDom64 s) : levelDom s :=
  let ⟨l1, l2, b, ht, hb, _, _⟩ := hd
  ⟨l1, l2, b, ht, hb⟩

/-- Shared skeleton: `eqnImpl L` refines the kernel on ANY domain whose
members come with a machine run to the verdict. The `next`/`final` legs are
domain-independent (`eqnRel` already embeds `levelDom`). -/
theorem levelEqual_stepRefines_on {L : LeafBodies} {D : RawState → Prop}
    (hrun : ∀ s, D s → levelDom s ∧
      ∃ n, SCMRuns (eqnProg L) n (encodeState s) (finalCfg (levelBit s))) :
    StepRefines (eqnImpl L) D (eqnRel L) where
  init := by
    intro s hd
    obtain ⟨hdm, n, hr⟩ := hrun s hd
    exact ⟨hdm, n, hr⟩
  next := by
    intro s c c' ⟨hd, k, hruns⟩ hs
    cases hruns with
    | refl =>
      have hs' : (StepResult.final (.returned (verdictVal (levelBit s))) :
          StepResult (S_eqn L.extra L.cat) resTy) = .next c' := hs
      exact StepResult.noConfusion hs'
    | step hs0 hruns' =>
      have heq := StepResult.next.inj (hs0.symm.trans hs)
      exact Or.inl ⟨hd, _, heq ▸ hruns'⟩
  final := by
    intro s c o ⟨hd, k, hruns⟩ hs
    cases hruns with
    | refl =>
      have hs' : (StepResult.final (.returned (verdictVal (levelBit s))) :
          StepResult (S_eqn L.extra L.cat) resTy) = .final o := hs
      cases StepResult.final.inj hs'
      exact eqn_kernel (extra := L.extra) (cat := L.cat) hd
    | step hs0 _ =>
      exact StepResult.noConfusion (hs0.symm.trans hs)

/-- The slice of `levelDom64` at one fixed request pair — the domain of the
non-vacuity witness. -/
def levelDomAt (l1 l2 : Level) (s : RawState) : Prop :=
  ∃ b, s.task = .levelEqual l1 l2 ∧ s.budget = b + 1

/-- RM-022 on every in-range, positive-budget `levelEqual` request over
`stepI`. -/
theorem levelEqual_stepRefines {L : LeafBodies} (h : ScmLeavesAgree L) :
    StepRefines (eqnImpl L) levelDom64 (eqnRel L) :=
  levelEqual_stepRefines_on fun s hd => by
    obtain ⟨l1, l2, b, ht, hb, hl1, hl2⟩ := hd
    obtain ⟨n, hn⟩ := composer_evalsI (h.at hl1 hl2)
    refine ⟨⟨l1, l2, b, ht, hb⟩, n, ?_⟩
    show SCMRuns (eqnProg L) n (encodeState s) (finalCfg (levelBit s))
    simp only [encodeState, encodeLevels, levelBit, ht]
    exact hn .nil

/-- The conditional seam RUN on a single concrete request pair: the
pointwise obligations `ScmLeavesAgreeAt` suffice for `StepRefines` on the
pair's slice. This is the theorem the non-vacuity witness instantiates. -/
theorem levelEqual_stepRefines_at {L : LeafBodies} {l1 l2 : Level}
    (h : ScmLeavesAgreeAt L l1 l2) :
    StepRefines (eqnImpl L) (levelDomAt l1 l2) (eqnRel L) :=
  levelEqual_stepRefines_on fun s hd => by
    obtain ⟨b, ht, hb⟩ := hd
    obtain ⟨n, hn⟩ := composer_evalsI h
    refine ⟨⟨l1, l2, b, ht, hb⟩, n, ?_⟩
    show SCMRuns (eqnProg L) n (encodeState s) (finalCfg (levelBit s))
    simp only [encodeState, encodeLevels, levelBit, ht]
    exact hn .nil

theorem levelEqual_terminates {L : LeafBodies} (h : ScmLeavesAgree L)
    {s : RawState} (hd : levelDom64 s) :
    ImplTerminates (eqnImpl L) s := by
  obtain ⟨_, n, hruns⟩ := (levelEqual_stepRefines h).init hd
  exact ⟨n, finalCfg (levelBit s), .returned (verdictVal (levelBit s)), hruns, rfl⟩

/-- RM-023, UNSOUND, over `stepI`: reference refusal at `decEqN = false`
implies `eqnImpl L` accepts at no budget, on the in-range slice. -/
theorem levelEqual_unsound {L : LeafBodies} (h : ScmLeavesAgree L)
    (amb : Ambient) (l1 l2 : Level) (b : Nat)
    (hl1 : levelIn64 l1) (hl2 : levelIn64 l2)
    (hdec : decEqN l1 l2 = false) (p : AcceptedPayload) :
    ¬ ImplAccepts (eqnImpl L) ⟨amb, .levelEqual l1 l2, b + 1⟩ p :=
  RM023_unsound (levelEqual_stepRefines h) ⟨l1, l2, b, rfl, rfl, hl1, hl2⟩ (k := 1)
    (by
      show runRaw 1 ⟨amb, .levelEqual l1 l2, b + 1⟩ = .refused "[rcic_level_not_equal]"
      simp only [runRaw, kernelStepRaw, hdec]
      have hneq : ¬ ((false : Bool) = true) := fun c => Bool.noConfusion c
      simp only [if_neg hneq])
    p

/-- RM-023 converse over `stepI`: `eqN` implies SCM acceptance, on the
in-range slice. -/
theorem levelEqual_accepts {L : LeafBodies} (h : ScmLeavesAgree L)
    (amb : Ambient) (l1 l2 : Level) (b : Nat)
    (hl1 : levelIn64 l1) (hl2 : levelIn64 l2) (heq : eqN l1 l2) :
    ImplAccepts (eqnImpl L) ⟨amb, .levelEqual l1 l2, b + 1⟩ .conversionConfirmed :=
  RM023_accept_complete (levelEqual_stepRefines h) ⟨l1, l2, b, rfl, rfl, hl1, hl2⟩
    (levelEqual_terminates h ⟨l1, l2, b, rfl, rfl, hl1, hl2⟩) (k := 1)
    (by
      show runRaw 1 ⟨amb, .levelEqual l1 l2, b + 1⟩ = .accepted .conversionConfirmed
      simp only [runRaw, RM011_levelEqual_complete amb l1 l2 b heq])

/-- Bridge to `ScmRun.run`: any returning `runLoopI` of `eqnProg L` on `encodeState`
agrees with `Scm.Run.run` on `rawProgOf L` and `levelEqnBody` under `hbound`. -/
theorem levelEqual_run_agrees (L : LeafBodies) (l1 l2 : Level)
    (left : Nat) (v : CoreVal resTy) (k : Int)
    (hbound : ∀ {n : Nat} {c' : Config (S_eqn L.extra L.cat) resTy},
      SCMRuns (eqnProg L) n ⟨resTy, .evalC (entryEnv l1 l2) levelEqnCore, .nil⟩ c' →
      ∀ c'', stepI (eqnProg L) c' = .next c'' →
        Raw.step (rawProgOf L) c'.erase ≠ Raw.stuck)
    (hr : runLoopI (eqnProg L) ⟨resTy, .evalC (entryEnv l1 l2) levelEqnCore, .nil⟩
      left 0 = .done (.returned v) k) :
    Rcic.Scm.Run.run left (rawProgOf L) (entryEnv l1 l2).erase levelEqnBody =
      some v.erase :=
  Rcic.Scm.Run.run_agrees_runLoopI_of_erasures (rawProgOf L) (eqnProg L)
    (eqnProg_erasures L) (entryEnv l1 l2) levelEqnCore left v k hbound hr

/-! ## Tooth: `inlinedAcceptCore` on `stepI` with `encodeState` does not refine -/

def inlinedProg (L : LeafBodies) : Bodies (S_eqn L.extra L.cat) (S_eqn L.extra L.cat).fns :=
  .cons inlinedAcceptCore
    (.cons refuseCore
      (.cons L.paramsBody
        (.cons L.unionBody
          (.cons L.subsetsBody
            (.cons L.allNoneBody
              (.cons okCore L.extraBodies))))))

def encodeInlined {extra : List FnSig} {cat : List CatalogEntry} (s : RawState) :
    Config (S_eqn extra cat) resTy :=
  let p := encodeLevels s
  ⟨resTy, .evalC (entryEnv p.1 p.2) inlinedAcceptCore, .nil⟩

def inlineImpl (L : LeafBodies) : ScmImpl :=
  ⟨S_eqn L.extra L.cat, resTy, inlinedProg L, encodeInlined, decodeRes⟩

theorem inlined_evalsI (L : LeafBodies) (l1 l2 : Level) :
    EvalsI (inlinedProg L) (entryEnv l1 l2) inlinedAcceptCore (verdictVal true) 11 :=
  evI_call1 (n1 := 1) (nb := 7) evI_lit (okCore_evals (inlinedProg L) (.i64V 1 h1))

theorem inlined_not_refines (L : LeafBodies) (amb : Ambient)
    (R : RawState → Config (S_eqn L.extra L.cat) resTy → Prop) :
    ¬ StepRefines (inlineImpl L) (· = ⟨amb, .levelEqual (.param 0) (.param 1), 1⟩) R := by
  intro hr
  have hruns : SCMRuns (inlinedProg L) 11
      (encodeInlined ⟨amb, .levelEqual (.param 0) (.param 1), 1⟩) (finalCfg true) :=
    inlined_evalsI L (.param 0) (.param 1) .nil
  have hdone := Rcic.Scm.Theorems.runLoopI_complete (inlinedProg L) hruns
    (o := .returned (verdictVal true)) rfl 11 (Nat.le_refl 11) 0
  exact RM023_unsound hr rfl (k := 1)
    (by
      show runRaw 1 ⟨amb, .levelEqual (.param 0) (.param 1), 1⟩ =
        .refused "[rcic_level_not_equal]"
      simp only [runRaw, RM011_param0_param1_refused amb])
    .conversionConfirmed ⟨11, 0, _, .returned (verdictVal true), hdone, rfl⟩

theorem natCore_in {n : Nat} (h : inI64 (Int.ofNat n)) :
    natCore n = .i64V (Int.ofNat n) h := by
  unfold natCore
  rw [dif_pos h]

theorem natCore_out {n : Nat} (h : ¬ inI64 (Int.ofNat n)) :
    natCore n = .i64V 0 h0 := by
  unfold natCore
  rw [dif_neg h]

theorem scmRuns_ret_unique {S : Sig} {A : CoreTy} {prog : Bodies S S.fns}
    {m n : Nat} {c : Config S A} {v w : CoreVal A}
    (h1 : SCMRuns prog m c ⟨A, .retC v, .nil⟩)
    (h2 : SCMRuns prog n c ⟨A, .retC w, .nil⟩) : v = w := by
  have r1 := Rcic.Scm.Theorems.runLoopI_complete prog h1
    (o := .returned v) rfl (m + n) (Nat.le_add_right m n) 0
  have r2 := Rcic.Scm.Theorems.runLoopI_complete prog h2
    (o := .returned w) rfl (m + n) (Nat.le_add_left n m) 0
  cases (RunI.done.inj (r1.symm.trans r2)).1
  rfl

instance (xs : List Nat) : Decidable (natsIn64 xs) :=
  inferInstanceAs (Decidable (∀ x ∈ xs, natIn64 x))

instance (xss : List (List Nat)) : Decidable (setsIn64 xss) :=
  inferInstanceAs (Decidable (∀ xs ∈ xss, natsIn64 xs))

/-- Same-index injectivity of `listV` / `cons` (constructor discrimination,
no evaluation — `CoreList` is a mutual inductive, so spine recursion does not
reduce definitionally). -/
theorem listV_inj {t : CoreTy} {xs ys : CoreList t}
    (h : CoreVal.listV xs = CoreVal.listV ys) : xs = ys := by
  cases h
  rfl

theorem cons_tail_inj {t : CoreTy} {x y : CoreVal t} {xs ys : CoreList t}
    (h : CoreList.cons x xs = CoreList.cons y ys) : xs = ys := by
  cases h
  rfl

/-- Audit P1 (#7134, 2026-10-15T05:15Z), machine-checked: the *unbounded*
`union_evals` obligation is uninhabitable. `natCore` collapses `2^63` onto
`0`, so `([2^63], [0])` and `([0], [0])` enter `unionBody` through identical
argument values while `unionNat` returns `[0, 2^63]` and `[0]` —
`scmRuns_ret_unique` then forces two different return values equal. -/
theorem union_evals_unbounded_impossible {L : LeafBodies}
    (h : ∀ (xs ys : List Nat),
      ∃ n, EvalsI (eqnProg L) (.cons (natsVal xs) (.cons (natsVal ys) .nil))
        L.unionBody (natsVal (unionNat xs ys)) n) :
    False := by
  have hB : natCore (2^63) = .i64V 0 h0 := natCore_out (n := 2^63) (by decide)
  have h0e : natCore 0 = .i64V 0 h0 := by
    have h0i : inI64 (Int.ofNat 0) := by decide
    unfold natCore
    rw [dif_pos h0i]
    rfl
  have henc : natsVal [2^63] = natsVal [0] := by
    show (.listV (natsCore [2^63]) : CoreVal natListTy) = .listV (natsCore [0])
    rw [show natsCore [2^63] = .cons (natCore (2^63)) .nil from rfl,
      show natsCore [0] = .cons (natCore 0) .nil from rfl, hB, h0e]
  obtain ⟨n1, h1'⟩ := h [2^63] [0]
  obtain ⟨n2, h2'⟩ := h [0] [0]
  have hrun1 : SCMRuns (eqnProg L) n1
      ⟨natListTy, .evalC (.cons (natsVal [0]) (.cons (natsVal [0]) .nil))
        L.unionBody, .nil⟩
      ⟨natListTy, .retC (natsVal (unionNat [2^63] [0])), .nil⟩ :=
    henc ▸ h1' .nil
  have hval : natsVal (unionNat [2^63] [0]) = natsVal (unionNat [0] [0]) :=
    scmRuns_ret_unique hrun1 (h2' .nil)
  rw [show unionNat [2^63] [0] = [0, 2^63] from rfl,
    show unionNat [0] [0] = [0] from rfl] at hval
  have hcl : natsCore [0, 2^63] = natsCore [0] := listV_inj hval
  rw [show natsCore [0, 2^63] = .cons (natCore 0) (.cons (natCore (2^63)) .nil) from rfl,
    show natsCore [0] = .cons (natCore 0) .nil from rfl] at hcl
  have htl : CoreList.cons (natCore (2^63)) CoreList.nil = CoreList.nil :=
    cons_tail_inj hcl
  cases htl

/-- Leaf-premise tooth: `eqnImpl badLeaves` keeps `levelEqnCore` and `encodeState`
intact while the leaf bodies return constant literals, violating `ScmLeavesAgree`
and refuting `StepRefines (eqnImpl badLeaves)`. -/
def badLeaves : LeafBodies where
  paramsBody := .lit (paramsVal [])
  unionBody := .lit (natsVal [])
  subsetsBody := .lit (setsVal [])
  allNoneBody := .lit (okRecVal (.i64V 1 h1))
  extraBodies := .nil

theorem badLeaves_not_agree : ¬ ScmLeavesAgree badLeaves := by
  intro h
  obtain ⟨n, hn⟩ := h.allNone_evals (.param 0) (.param 1) [0, 1] [[], [1], [0], [0, 1]]
    (by decide) (by decide)
  have heq := (scmRuns_ret_unique (hn .nil) (step1 rfl)).symm
  have hval : resOkVal (okRecVal (.i64V 1 h1)) =
      resOkVal (okRecVal (if allNoneAgree (.param 0) (.param 1) [0, 1] [[], [1], [0], [0, 1]]
        then .i64V 1 h1 else .i64V 0 h0)) := congrArg resOkVal heq
  revert hval
  decide

theorem badLeaves_evalsI (l1 l2 : Level) :
    ∃ n, EvalsI (eqnProg badLeaves) (entryEnv l1 l2) levelEqnCore (verdictVal true) n := by
  obtain ⟨nt, ht⟩ := tail_evalsI badLeaves _ true
  exact ⟨_, evI_if_false (evI_lt evI_var evI_lit)
    (evI_let (evI_call1 evI_var evI_lit)
      (evI_if_false (evI_eq (evI_field evI_var) evI_lit)
        (evI_let (evI_call1 evI_var evI_lit)
          (evI_if_false (evI_eq (evI_field evI_var) evI_lit)
            (evI_let (evI_call2 (evI_field evI_var) (evI_field evI_var) evI_lit)
              (evI_let (evI_call1 evI_var evI_lit)
                (evI_let (evI_call5 evI_var evI_var evI_var evI_var evI_var evI_lit)
                  ht)))))))⟩

theorem badLeaves_not_refines (amb : Ambient)
    (R : RawState → Config (S_eqn badLeaves.extra badLeaves.cat) resTy → Prop) :
    ¬ StepRefines (eqnImpl badLeaves)
        (· = ⟨amb, .levelEqual (.param 0) (.param 1), 1⟩) R := by
  intro hr
  obtain ⟨n, hn⟩ := badLeaves_evalsI (.param 0) (.param 1)
  have hruns : SCMRuns (eqnProg badLeaves) n
      (encodeState ⟨amb, .levelEqual (.param 0) (.param 1), 1⟩) (finalCfg true) :=
    hn .nil
  have hdone := Rcic.Scm.Theorems.runLoopI_complete (eqnProg badLeaves) hruns
    (o := .returned (verdictVal true)) rfl n (Nat.le_refl n) 0
  exact RM023_unsound hr rfl (k := 1)
    (by
      show runRaw 1 ⟨amb, .levelEqual (.param 0) (.param 1), 1⟩ =
        .refused "[rcic_level_not_equal]"
      simp only [runRaw, RM011_param0_param1_refused amb])
    .conversionConfirmed ⟨n, 0, _, .returned (verdictVal true), hdone, rfl⟩

/-! ## Non-vacuity witness: the seam fires concretely at `(.zero, .zero)`

Scope-ruling condition on #7134 (2026-10-15): the conditional seam is
accepted provided a concrete wire input exists where the leaf obligations
are PROVED and `levelEqual_stepRefines` runs. `witnessLeaves` supplies
pointwise leaf bodies — `paramsBody` constructs the empty-params record,
`unionBody` returns arg0 (the union, correct on `([], [])`), `subsetsBody`
returns `allSubsets [] = [[]]`, and `allNoneBody` builds the ok-record
computing its `val` field as `fuel + 1` read from the wire environment —
each discharged by a real `SCMRuns` trace through `stepI`. `ScmLeavesAgree`
remains uninhabited: this is pointwise evidence the conditional seam fires,
not the F2 supplier; `witness_not_agreeAt` refutes the same predicate at
`(.param 0, .param 1)` so the pointwise check discriminates. -/

def witnessLeaves : LeafBodies where
  paramsBody :=
    .recordE (.cons "ok" cLitI1 (.cons "params" (.lit (natsVal []))
      (.cons "code" (cLitS "") .nil))) rfl
  unionBody := .var 0 rfl
  subsetsBody := .lit (setsVal [[]])
  allNoneBody :=
    .recordE (.cons "ok" cLitI1
      (.cons "val" (.prim .add (.cons (.var 4 rfl) (.cons cLitI1 .nil)))
        (.cons "code" (cLitS "") .nil))) rfl
  extraBodies := .nil

/-- `paramsBody` evaluates to the empty-params record — correct at
`l = .zero` where `paramsOf .zero = []`. -/
theorem witness_params_evals :
    ∃ n, EvalsI (eqnProg witnessLeaves) (.cons (levelStr .zero) .nil)
      witnessLeaves.paramsBody (paramsVal (paramsOf .zero)) n := by
  rw [show paramsOf .zero = [] from rfl]
  exact ⟨_, evI_rec3 (k1 := "ok") (k2 := "params") (k3 := "code")
    evI_lit evI_lit evI_lit rfl⟩

/-- `allNoneBody` evaluates to the `ok=1`/`val=1` record on any entry env —
its `val` field is `fuel + 1`. -/
theorem witness_allNone_evals (l1 l2 : Level) (ps : List Nat)
    (nss : List (List Nat)) :
    ∃ n, EvalsI (eqnProg witnessLeaves)
      (.cons (levelStr l1) (.cons (levelStr l2)
        (.cons (natsVal ps) (.cons (setsVal nss) (.cons (.i64V 0 h0) .nil)))))
      witnessLeaves.allNoneBody (okRecVal (.i64V 1 h1)) n :=
  ⟨_, evI_rec3 (k1 := "ok") (k2 := "val") (k3 := "code")
    evI_lit
    (evI_add (x := 0) (y := 1) (hx := h0) (hy := h1)
      (hz := ⟨by decide, by decide⟩)
      (evI_var (i := 4) (v := .i64V 0 h0)) evI_lit)
    evI_lit rfl⟩

/-- The pointwise leaf obligations at `(.zero, .zero)`: `paramsOf .zero = []`,
`unionNat [] [] = []`, `allSubsets [] = [[]]`, and
`allNoneAgree .zero .zero [] [[]] = true` (`agreeAt` reduces: `noneOf` is
`false` and the `nf`-comparison is reflexive), so the required `allNoneBody`
output is the `ok=1`/`val=1` record `witness_allNone_evals` produces. Every
leaf body is a genuine `stepI` computation. -/
theorem witness_agreeAt : ScmLeavesAgreeAt witnessLeaves .zero .zero where
  params_evals_l1 := witness_params_evals
  params_evals_l2 := witness_params_evals
  union_evals := ⟨_, evI_var⟩
  subsets_evals := ⟨_, evI_lit⟩
  allNone_evals := witness_allNone_evals .zero .zero _ _

/-- `levelEqual_stepRefines` run on the concrete wire input: `eqnImpl
witnessLeaves` refines the kernel on the `levelDomAt .zero .zero` slice. -/
theorem witness_stepRefines :
    StepRefines (eqnImpl witnessLeaves) (levelDomAt .zero .zero)
      (eqnRel witnessLeaves) :=
  levelEqual_stepRefines_at witness_agreeAt

/-- The concrete machine run the refinement wraps: `encodeState` of
`⟨amb, .levelEqual .zero .zero, b+1⟩` reaches `finalCfg (decEqN .zero .zero)`. -/
theorem witness_runs (amb : Ambient) (b : Nat) :
    ∃ n, SCMRuns (eqnProg witnessLeaves) n
      (encodeState ⟨amb, .levelEqual .zero .zero, b + 1⟩)
      (finalCfg (levelBit ⟨amb, .levelEqual .zero .zero, b + 1⟩)) :=
  (witness_stepRefines.init (s := ⟨amb, .levelEqual .zero .zero, b + 1⟩) ⟨b, rfl, rfl⟩).2

theorem witness_terminates (amb : Ambient) (b : Nat) :
    ImplTerminates (eqnImpl witnessLeaves)
      ⟨amb, .levelEqual .zero .zero, b + 1⟩ := by
  obtain ⟨_, n, hruns⟩ :=
    witness_stepRefines.init (s := ⟨amb, .levelEqual .zero .zero, b + 1⟩) ⟨b, rfl, rfl⟩
  exact ⟨n, finalCfg (levelBit _), .returned (verdictVal (levelBit _)),
    hruns, rfl⟩

/-- The wire input is accepted: `decEqN .zero .zero` holds
(`eqN .zero .zero` is reflexivity), so the SCM verdict is
`.accepted .conversionConfirmed`. -/
theorem witness_accepts (amb : Ambient) (b : Nat) :
    ImplAccepts (eqnImpl witnessLeaves) ⟨amb, .levelEqual .zero .zero, b + 1⟩
      .conversionConfirmed :=
  RM023_accept_complete witness_stepRefines (s := ⟨amb, .levelEqual .zero .zero, b + 1⟩)
    ⟨b, rfl, rfl⟩
    (witness_terminates amb b) (k := 1)
    (by
      show runRaw 1 ⟨amb, .levelEqual .zero .zero, b + 1⟩ =
        .accepted .conversionConfirmed
      simp only [runRaw, RM011_levelEqual_complete amb .zero .zero b (fun _ => rfl)])

/-- The pointwise predicate discriminates: at `(.param 0, .param 1)` — the
same counterexample point as `badLeaves_not_agree` — the required
`allNoneBody` output is the `ok=0` record (`allNoneAgree` is `false`
there), while `witnessLeaves.allNoneBody` returns `ok=1` on every
environment (it reads only the fuel slot). `scmRuns_ret_unique` forces the
contradiction. -/
theorem witness_not_agreeAt :
    ¬ ScmLeavesAgreeAt witnessLeaves (.param 0) (.param 1) := by
  intro h
  obtain ⟨n, hn⟩ := h.allNone_evals
  obtain ⟨m, hm⟩ := witness_allNone_evals (.param 0) (.param 1)
    (unionNat (paramsOf (.param 0)) (paramsOf (.param 1)))
    (allSubsets (unionNat (paramsOf (.param 0)) (paramsOf (.param 1))))
  have heq := scmRuns_ret_unique (hn .nil) (hm .nil)
  have hval := congrArg resOkVal heq
  revert hval
  decide

#print axioms Rcic.LevelEqnArm.tail_evalsI
#print axioms Rcic.LevelEqnArm.composer_evalsI
#print axioms Rcic.LevelEqnArm.encodeState_zero_ne_max_zero
#print axioms Rcic.LevelEqnArm.decodeRes_verdict
#print axioms Rcic.LevelEqnArm.eqn_kernel
#print axioms Rcic.LevelEqnArm.levelEqual_stepRefines
#print axioms Rcic.LevelEqnArm.levelEqual_terminates
#print axioms Rcic.LevelEqnArm.levelEqual_unsound
#print axioms Rcic.LevelEqnArm.levelEqual_accepts
#print axioms Rcic.LevelEqnArm.levelEqual_run_agrees
#print axioms Rcic.LevelEqnArm.inlined_evalsI
#print axioms Rcic.LevelEqnArm.inlined_not_refines
#print axioms Rcic.LevelEqnArm.mem_insertNat
#print axioms Rcic.LevelEqnArm.natsIn64_unionNat
#print axioms Rcic.LevelEqnArm.sublist_allSubsets
#print axioms Rcic.LevelEqnArm.setsIn64_allSubsets
#print axioms Rcic.LevelEqnArm.levelDom64_levelDom
#print axioms Rcic.LevelEqnArm.natCore_in
#print axioms Rcic.LevelEqnArm.natCore_out
#print axioms Rcic.LevelEqnArm.scmRuns_ret_unique
#print axioms Rcic.LevelEqnArm.union_evals_unbounded_impossible
#print axioms Rcic.LevelEqnArm.badLeaves_not_agree
#print axioms Rcic.LevelEqnArm.badLeaves_evalsI
#print axioms Rcic.LevelEqnArm.badLeaves_not_refines
#print axioms Rcic.LevelEqnArm.witness_agreeAt
#print axioms Rcic.LevelEqnArm.witness_stepRefines
#print axioms Rcic.LevelEqnArm.witness_accepts
#print axioms Rcic.LevelEqnArm.witness_not_agreeAt

end Rcic.LevelEqnArm

