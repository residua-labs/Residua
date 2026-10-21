import rcic.RcicPinEqIotaStarK

/-! `RcicKGateNoGo` — the K-gate no-go tooth (cc ruling on #6293, 02:25Z).

**Abstract half** — ported from `~/.residua-lean/files/KGateNoGo.lean`:
any recursor denotation `G` (index of the parameter `a`, index of the
major's type `b`) that is monotone in both indices, fires on the ⊥
diagonal (`G ⊥ ⊥ = m`, forced by ι★K soundness under λ — `pinEq_convK`
closed over `a`), with `m` in an upward-closed summand (Π lifted), is in
that summand EVERYWHERE, including at distinct atoms. So no stuck value
outside the Π summand exists. The T3 equality-gated clause is not
monotone (`t3Rec_not_monotone`): the gate cannot be a monotone semantic
denotation — it must live in the logical relation.

**Tree half** — `pinEq_convK_diag`: the `hdiag` premise pinned on the
RCIC tree. `pinEq_convK` (`RcicPinEqIotaStarK.lean:478`) is
`rec α a M m a p ≡ m` at `eqJoinCtx = [p, m, M, a, α]`; closing it under
4× `ConvT.lam` peels `p, m, M, a` — `eqJoinCtx`'s stored types are
already at tail scope, so the lam domains are `eqPTy`, `eqMinorT`,
`eqMotT`, `bvar 0` verbatim, no shifting. The closed conversion
`λ p m M a. rec α a M m a p ≡ λ p m M a. m` at `[α]` is what conversion
soundness evaluates at `a ↦ ⊥` — the diagonal premise `G ⊥ ⊥ = m` any
K-gate model must validate. -/

namespace Rcic

/-! ## abstract no-go -/

theorem kgate_nogo {D : Type} (le : D → D → Prop) (bot : D) (hbot : ∀ x, le bot x)
    (isPi : D → Prop) (hup : ∀ {x y}, le x y → isPi x → isPi y)
    (G : D → D → D)
    (hmono : ∀ {a a' b b'}, le a a' → le b b' → le (G a b) (G a' b'))
    (m : D) (hm : isPi m) (hdiag : G bot bot = m) :
    ∀ a b, isPi (G a b) :=
  fun a b => hup (hmono (hbot a) (hbot b)) (hdiag ▸ hm)

/-- A 5-point fragment of the T3 domain: ⊥, two atoms, the fire value (a Π
code), the stuck value `recNeut` (its own summand). Flat order above ⊥. -/
inductive Pt | bot | nuA | nuB | piM | neut
  deriving DecidableEq

def Pt.le : Pt → Pt → Prop
  | .bot, _ => True
  | x, y => x = y

def Pt.isPi : Pt → Prop
  | .piM => True
  | _ => False

/-- T3 §6.1 literally: fire iff the index denotations are equal. -/
def t3Rec (a b : Pt) : Pt := if b = a then .piM else .neut

/-- T3's clause is not monotone: the ⊥ diagonal fires, distinct atoms are stuck. -/
theorem t3Rec_not_monotone :
    ¬ (∀ {a a' b b' : Pt}, Pt.le a a' → Pt.le b b' →
        Pt.le (t3Rec a b) (t3Rec a' b')) := by
  intro h
  have := @h .bot .nuA .bot .nuB trivial trivial
  simp [t3Rec, Pt.le] at this

/-- And via the general lemma: every monotone repair fires at distinct atoms. -/
theorem every_monotone_repair_fires (G : Pt → Pt → Pt)
    (hmono : ∀ {a a' b b'}, Pt.le a a' → Pt.le b b' → Pt.le (G a b) (G a' b'))
    (hdiag : G .bot .bot = .piM) : G .nuA .nuB = .piM := by
  have h := kgate_nogo Pt.le .bot (fun _ => by cases ‹Pt› <;> trivial) Pt.isPi
    (fun {x y} hxy hx => by
      cases x <;> cases y <;> simp_all [Pt.le, Pt.isPi])
    G hmono .piM trivial hdiag .nuA .nuB
  revert h
  cases G .nuA .nuB <;> simp [Pt.isPi]

/-! ## `hdiag` pinned on the tree: 4× `ConvT.lam` closure of `pinEq_convK` -/

section treePin

open Rcic.Declarative

/-- `[m, M, a, α]` — `eqJoinCtx` with `p` peeled. -/
private def kgCtxMMA : LCtx := eqJoinCtx.tail

/-- `[M, a, α]` — `eqJoinCtx` with `p, m` peeled. -/
private def kgCtxMA : LCtx := eqJoinCtx.tail.tail

/-- `[a, α]` — `eqJoinCtx` with `p, m, M` peeled. -/
private def kgCtxAa : LCtx := eqJoinCtx.tail.tail.tail

/-- `[α]` — `eqJoinCtx` with `p, m, M, a` peeled. -/
def kgCtxα : LCtx := eqJoinCtx.tail.tail.tail.tail

private def kgTyMMAα : HasTyT eqEnvT 1 kgCtxMMA (.bvar 3) (.sort (.succ .zero)) :=
  HasTyT.bvar _ 3 _ rfl

private def kgTyMMAa : HasTyT eqEnvT 1 kgCtxMMA (.bvar 2) (.bvar 3) :=
  HasTyT.bvar _ 2 _ rfl

private def kgTyFamApp1 : HasTyT eqEnvT 1 kgCtxMMA (.app (.const 63 []) (.bvar 3))
    (.pi (.bvar 3) (.pi (.bvar 4) (.sort .zero))) :=
  HasTyT.app _ _ _ _ _ (HasTyT.const _ 63 [] eqFamT rfl rfl rfl) kgTyMMAα

private def kgTyFamApp2 : HasTyT eqEnvT 1 kgCtxMMA
    (.app (.app (.const 63 []) (.bvar 3)) (.bvar 2))
    (.pi (.bvar 3) (.sort .zero)) :=
  HasTyT.app _ _ _ _ _ kgTyFamApp1 kgTyMMAa

/-- `Eq α a a : Sort 0` at `[m, M, a, α]` — `p`'s stored type as the
innermost lam domain (peeled first). -/
def kgPTyTy : HasTyT eqEnvT 1 kgCtxMMA eqPTy (.sort .zero) :=
  HasTyT.app _ _ _ _ _ kgTyFamApp2 kgTyMMAa

private def kgTyMAα : HasTyT eqEnvT 1 kgCtxMA (.bvar 2) (.sort (.succ .zero)) :=
  HasTyT.bvar _ 2 _ rfl

private def kgTyMAa : HasTyT eqEnvT 1 kgCtxMA (.bvar 1) (.bvar 2) :=
  HasTyT.bvar _ 1 _ rfl

private def kgTyMAM : HasTyT eqEnvT 1 kgCtxMA (.bvar 0) (lift 0 1 eqMotT) :=
  HasTyT.bvar _ 0 _ rfl

private def kgTyMAMa : HasTyT eqEnvT 1 kgCtxMA (.app (.bvar 0) (.bvar 1))
    (.pi (foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 1])
      (.sort (.param 0))) :=
  HasTyT.app _ _ _ _ _ kgTyMAM kgTyMAa

private def kgTyRefl1 : HasTyT eqEnvT 1 kgCtxMA (.app (.const 64 []) (.bvar 2))
    (.pi (.bvar 2) (foldApps (.const 63 []) [.bvar 3, .bvar 0, .bvar 0])) :=
  HasTyT.app _ _ _ _ _ (HasTyT.const _ 64 [] eqReflT rfl rfl rfl) kgTyMAα

private def kgTyRefl : HasTyT eqEnvT 1 kgCtxMA
    (.app (.app (.const 64 []) (.bvar 2)) (.bvar 1))
    (foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 1]) :=
  HasTyT.app _ _ _ _ _ kgTyRefl1 kgTyMAa

/-- `M a (refl α a) : Sort (param 0)` at `[M, a, α]` — `m`'s stored type
as the third lam domain. -/
def kgMinorTy : HasTyT eqEnvT 1 kgCtxMA eqMinorT (.sort (.param 0)) :=
  HasTyT.app _ _ _ _ _ kgTyMAMa kgTyRefl

private def kgTyAaα : HasTyT eqEnvT 1 kgCtxAa (.bvar 1) (.sort (.succ .zero)) :=
  HasTyT.bvar _ 1 _ rfl

/-- the `b`-extended context `[b : α, a : α, α : Sort 1]` —
`HasTyT.pi`'s premise ctx for `eqMotT`'s body. -/
private def kgCtxBa : LCtx := .assumption (.bvar 1) :: kgCtxAa

private def kgTyBaα : HasTyT eqEnvT 1 kgCtxBa (.bvar 2) (.sort (.succ .zero)) :=
  HasTyT.bvar _ 2 _ rfl

private def kgTyBaa : HasTyT eqEnvT 1 kgCtxBa (.bvar 1) (.bvar 2) :=
  HasTyT.bvar _ 1 _ rfl

private def kgTyBab : HasTyT eqEnvT 1 kgCtxBa (.bvar 0) (.bvar 2) :=
  HasTyT.bvar _ 0 _ rfl

private def kgTyEqB1 : HasTyT eqEnvT 1 kgCtxBa (.app (.const 63 []) (.bvar 2))
    (.pi (.bvar 2) (.pi (.bvar 3) (.sort .zero))) :=
  HasTyT.app _ _ _ _ _ (HasTyT.const _ 63 [] eqFamT rfl rfl rfl) kgTyBaα

private def kgTyEqB2 : HasTyT eqEnvT 1 kgCtxBa
    (.app (.app (.const 63 []) (.bvar 2)) (.bvar 1)) (.pi (.bvar 2) (.sort .zero)) :=
  HasTyT.app _ _ _ _ _ kgTyEqB1 kgTyBaa

private def kgTyEqB : HasTyT eqEnvT 1 kgCtxBa
    (.app (.app (.app (.const 63 []) (.bvar 2)) (.bvar 1)) (.bvar 0))
    (.sort .zero) :=
  HasTyT.app _ _ _ _ _ kgTyEqB2 kgTyBab

/-- `Eq α a b → Sort (param 0) : Sort (imax 0 (succ (param 0)))` at
`[b, a, α]` — `eqMotT`'s inner arrow. -/
private def kgTyMotInner : HasTyT eqEnvT 1 kgCtxBa
    (.pi (foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 0])
      (.sort (.param 0)))
    (.sort (.imax .zero (.succ (.param 0)))) :=
  HasTyT.pi _ _ _ _ _ kgTyEqB (HasTyT.sort _ _)

/-- `Π (b : α), Eq α a b → Sort (param 0)` at `[a, α]` — `M`'s stored
type as the second lam domain. -/
def kgMotTy : HasTyT eqEnvT 1 kgCtxAa eqMotT
    (.sort (.imax (.succ .zero) (.imax .zero (.succ (.param 0))))) :=
  HasTyT.pi _ _ _ _ _ kgTyAaα kgTyMotInner

/-- `α : Sort 1` at `[α]` — `a`'s stored type (`bvar 0` at tail scope) as
the innermost lam domain. -/
def kgATy : HasTyT eqEnvT 1 kgCtxα (.bvar 0) (.sort (.succ .zero)) :=
  HasTyT.bvar _ 0 _ rfl

/-- the closed LHS telescope `λ a M m p. rec α a M m a p` — `ConvT.lam`
peels `eqJoinCtx`'s head, so `p` is wrapped first and `a` lands
outermost; each domain is `eqJoinCtx`'s stored type verbatim (already at
tail scope). -/
def kgDiagL : Expr Nat :=
  .lam (.bvar 0) (.lam eqMotT (.lam eqMinorT (.lam eqPTy
    (.app eqRecFive (.bvar 0)))))

/-- the closed RHS telescope `λ a M m p. m`. -/
def kgDiagR : Expr Nat :=
  .lam (.bvar 0) (.lam eqMotT (.lam eqMinorT (.lam eqPTy (.bvar 1))))

/-- the closure type `Π (a : α) M m p, M a p`. -/
def kgDiagT : Expr Nat :=
  .pi (.bvar 0) (.pi eqMotT (.pi eqMinorT (.pi eqPTy eqMotAp)))

/-- PIN: `hdiag` on the tree. `pinEq_convK` closed under 4× `ConvT.lam`
— `λ a M m p. rec α a M m a p ≡ λ a M m p. m` at `[α]` (the innermost
`ConvT.lam` peels `p`, the outermost `a`). Conversion soundness forces
the bodies equal at `a ↦ ⊥`: the recursor's denotation on the ⊥
diagonal equals the minor's — `G ⊥ ⊥ = m̂` in the model reading. -/
def pinEq_convK_diag :
    Nonempty (ConvT eqEnvT 1 kgCtxα kgDiagL kgDiagR kgDiagT) := by
  obtain ⟨h⟩ := pinEq_convK
  exact ⟨ConvT.lam _ _ _ _ _ _ _ (ConvT.refl _ _ _ kgATy)
    (ConvT.lam _ _ _ _ _ _ _ (ConvT.refl _ _ _ kgMotTy)
      (ConvT.lam _ _ _ _ _ _ _ (ConvT.refl _ _ _ kgMinorTy)
        (ConvT.lam _ _ _ _ _ _ _ (ConvT.refl _ _ _ kgPTyTy) h)))⟩

end treePin

#print axioms kgate_nogo
#print axioms t3Rec_not_monotone
#print axioms every_monotone_repair_fires
#print axioms pinEq_convK_diag

end Rcic
