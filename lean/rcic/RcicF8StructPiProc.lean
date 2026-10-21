import rcic.RcicF8ProofIndexPayload
import rcic.RcicF8EvInvT
import rcic.RcicEtaKDecide
import rcic.RcicA2SortSupport
import rcic.RcicF8StructPiPayload
import rcic.RcicF8EvPar
import rcic.RcicF8JEndpointRefutation
import rcic.RcicF8XValleyVia

/-!
# Conditional StructPi supplier

`no_proofIndex_at_pi` refutes a `ProofIndexPayload` whose source is `.pi A B`.
The chain is `EvTy.invPiT` composed with the payload's chain to its proposition,
then `F8EtaK.separationAt_of_sortUniq`. `su : SortUnique` stays an explicit premise.

`StructPiProcWfP` answers a Π-source `EvPar` only when the caller supplies
`CtxWfT` of that same context. The `structPi` arm returns the payload already
in the step. The `proofIndex` arm is `no_proofIndex_at_pi` at the supplied
`CtxWfT`. It is not `∀ R, StructPiProc R` and not `StructPiProcP.ofTotal`.
Nothing here derives `CtxWfT` from an `EvPar` or from `EnvWfT` alone.

`structPiProcWfP_atSeg` applies that supplier at the segment `CtxWfT` the
landed `SuppliersVia.atSeg` already receives. It discards the view. `structPiSeg`
does not: it returns that view with `S` replaced. The replacement answers with
`structPiProcWfP` only when the request's context is the caller-supplied
segment, and refuses every other context. `atSeg` still copies `S`
(`StructPiProcP`). This module does not restate `SuppliersVia`, `atSeg`, or
`withJ`.

W-P-SUPPLY and W-P-H4 stay open. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat}

/-- A proof-index payload cannot sit on a Π. `su` is a parameter. -/
theorem no_proofIndex_at_pi (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {R : List (Jd E n)} {A B b T : Expr Nat}
    (p : ProofIndexPayload R Γ (.pi A B) b T) : False := by
  have hcl : EnvClosed E := envClosed_of_envWfT hW
  have hinst : EnvMembersSubstStable E := envMembersSubstStable_of_envWfT hW
  have inv : EvInvPi R Γ A B T := p.leftTy.invPiT rfl
  have hc : TyConvT E n Γ (.sort (.imax inv.u inv.v)) p.proposition :=
    (EvTc.trans inv.hc p.chain).val hcl hinst
  have hP : HasTyT E n Γ p.proposition (.sort .zero) := p.propTy.val hcl hinst
  exact F8EtaK.separationAt_of_sortUniq hW (su hW) hΓ hP hc

/-- The same fact at a concrete Π, `.pi (.sort .zero) (.sort .zero)`, on the
    empty environment and the empty context. `su` stays a parameter. -/
theorem no_proofIndex_at_pi_pin (su : F8A2Support.SortUnique emptyEnv 0)
    {R : List (Jd emptyEnv 0)} {b T : Expr Nat}
    (p : ProofIndexPayload R [] (.pi (.sort .zero) (.sort .zero)) b T) : False :=
  no_proofIndex_at_pi EnvWfT.empty su CtxWfT.nil p

/-- H-STRUCTPI, partial and context-conditioned: a Π-source step in a context
    the caller has already certified, or a refusal. Not `∀ R, StructPiProc R`. -/
abbrev StructPiProcWfP (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {A B q T : Expr Nat}, CtxWfT E n Γ →
    EvPar R Γ (.pi A B) q T →
    Option (Σ' (A' B' : Expr Nat), q = .pi A' B' ×' StructPiPayload R Γ A B A' B' T)

/-- Leaf contract of an answer: each cited leaf is a `SubEq` leaf of the input step. -/
def StructPiContractWfP (S : ∀ R : List (Jd E n), StructPiProcWfP R) : Prop :=
  ∀ R {Γ : LCtx} {A B q T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (s : EvPar R Γ (.pi A B) q T)
    (r : Σ' (A' B' : Expr Nat), q = .pi A' B' ×' StructPiPayload R Γ A B A' B' T),
    S R hΓ s = some r →
      ∀ ℓ ∈ r.2.2.2.hc.leaves ++ r.2.2.2.hcB.leaves, ∃ ℓ' ∈ s.leaves, SubEq ℓ ℓ'

/-- The `structPi` arm returns the payload in the step. `proofIndex` is impossible
    at the supplied `CtxWfT`. `refl` is not a structPi producer. `hΓ` is an
    argument, never constructed here. -/
def structPiProcWfP (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    ∀ R : List (Jd E n), StructPiProcWfP R :=
  fun _ {_ _ _ _ _} hΓ s => match s with
    | .structPi (A' := A') (B' := B') p => some ⟨A', B', rfl, p⟩
    | .proofIndex p => False.elim (no_proofIndex_at_pi hW su hΓ p)
    | .refl _ => none

theorem structPiProcWfP_contract (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    StructPiContractWfP (structPiProcWfP hW su) := by
  intro R Γ A B q T hΓ s r hr ℓ hℓ
  cases s with
  | structPi p =>
      simp only [structPiProcWfP, Option.some.injEq] at hr
      subst hr
      refine ⟨ℓ, ?_, .inl rfl⟩
      simp only [EvPar.leaves, StructPiPayload.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with hℓ | hℓ
      · exact .inl (.inl (.inl (.inl (.inr hℓ))))
      · exact .inl (.inl (.inr hℓ))
  | proofIndex p => exact (no_proofIndex_at_pi hW su hΓ p).elim
  | refl _ =>
      unfold structPiProcWfP at hr
      exact Option.noConfusion hr

/-- Inventing `hΓ` is impossible: `illCtx` is not well-formed. -/
theorem no_invent_hΓ :
    ¬ ∀ Γ : LCtx, Nonempty (CtxWfT emptyEnv 0 Γ) :=
  fun h => JTileS0.illCtx_not_wf (h XTileQ1.illCtx)

/-- A Π typing that lives at `illCtx`. Provenance does not ask for `CtxWfT`. -/
def illPiTy : HasTyT emptyEnv 0 XTileQ1.illCtx
    (.pi (.sort .zero) (.sort .zero))
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi XTileQ1.illCtx (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (.sort _ .zero) (.sort _ .zero)

def illPiR : List (Jd emptyEnv 0) := [.ty illPiTy]

def illPiPayload : StructPiPayload illPiR XTileQ1.illCtx
    (.sort .zero) (.sort .zero) (.sort .zero) (.sort .zero)
    (.sort (.imax (.succ .zero) (.succ .zero))) where
  u := .succ .zero
  v := .succ .zero
  hA := .sort .zero
  hc := .sorts .zero .zero (fun _ => rfl)
  hB := .sort .zero
  hcB := .sorts .zero .zero (fun _ => rfl)
  hrt := .lit illPiTy ⟨.ty illPiTy, List.Mem.head [], .inl rfl⟩
  idx := .refl _ _

/-- Premise-free mutant: a Π step is answered with no `CtxWfT` argument. -/
def structPiProcMut (R : List (Jd E n)) {Γ : LCtx} {A B q T : Expr Nat}
    (s : EvPar R Γ (.pi A B) q T) :
    Option (Σ' (A' B' : Expr Nat), q = .pi A' B' ×' StructPiPayload R Γ A B A' B' T) :=
  match s with
  | .structPi (A' := A') (B' := B') p => some ⟨A', B', rfl, p⟩
  | .proofIndex _ => none
  | .refl _ => none

/-- The mutant accepts the Π step at `illCtx`, and that context has no `CtxWfT`. -/
theorem mutant_pi_at_illCtx :
    structPiProcMut illPiR (EvPar.structPi illPiPayload) =
      some ⟨.sort .zero, .sort .zero, rfl, illPiPayload⟩ ∧
    ¬ Nonempty (CtxWfT emptyEnv 0 XTileQ1.illCtx) :=
  ⟨rfl, JTileS0.illCtx_not_wf⟩

/-- Answer the Π step at the segment `CtxWfT` `SuppliersVia.atSeg` already
    takes. The landed view is built so the certificate is that argument;
    its `S` is not read (`S := X.S`, still `StructPiProcP`). -/
def structPiProcWfP_atSeg (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (X : SuppliersVia E n) {Γ' : LCtx} (hΓ' : CtxWfT E n Γ')
    {R : List (Jd E n)} {A B q T : Expr Nat}
    (s : EvPar R Γ' (.pi A B) q T) :
    Option (Σ' (A' B' : Expr Nat), q = .pi A' B' ×' StructPiPayload R Γ' A B A' B' T) :=
  (fun (_ : Suppliers E n) => structPiProcWfP hW su R hΓ' s) (X.atSeg hΓ')

/-- `S` for one segment. `hΓ'` is an argument. A request at that context is
    `structPiProcWfP`; a request at any other context is `none`. -/
def structPiSegS (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ' : LCtx} (hΓ' : CtxWfT E n Γ') :
    ∀ R : List (Jd E n), StructPiProcP R :=
  fun R {Γ} {_ _ _ _} s =>
    if h : Γ = Γ' then structPiProcWfP hW su R (h.symm ▸ hΓ') s else none

theorem structPiSegS_eq (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ' : LCtx} (hΓ' : CtxWfT E n Γ') {R : List (Jd E n)} {A B q T : Expr Nat}
    (s : EvPar R Γ' (.pi A B) q T) :
    structPiSegS hW su hΓ' R s = structPiProcWfP hW su R hΓ' s := by
  show (if h : Γ' = Γ' then structPiProcWfP hW su R (h.symm ▸ hΓ') s else none) =
    structPiProcWfP hW su R hΓ' s
  exact dif_pos rfl

theorem structPiSegS_contract (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ' : LCtx} (hΓ' : CtxWfT E n Γ') :
    StructPiContractP (structPiSegS hW su hΓ') := by
  intro R Γ A B q T s r hr ℓ hℓ
  unfold structPiSegS at hr
  split at hr
  · next h =>
      subst h
      exact structPiProcWfP_contract hW su R hΓ' s r hr ℓ hℓ
  · exact Option.noConfusion hr

/-- The segment view `readStarC` calls. `K`/`J`/`D`/`U` are `X.atSeg hΓ'`.
    `S` is `structPiSegS`, so the view is not discarded. -/
def structPiSeg (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (X : SuppliersVia E n) {Γ' : LCtx} (hΓ' : CtxWfT E n Γ') : Suppliers E n :=
  { X.atSeg hΓ' with
    S := structPiSegS hW su hΓ'
    hS := structPiSegS_contract hW su hΓ' }

/-- At the supplied segment, the adapter's `S` is `structPiProcWfP`. -/
theorem structPiSeg_S_eq (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (X : SuppliersVia E n) {Γ' : LCtx} (hΓ' : CtxWfT E n Γ')
    {R : List (Jd E n)} {A B q T : Expr Nat}
    (s : EvPar R Γ' (.pi A B) q T) :
    (structPiSeg hW su X hΓ').S R s = structPiProcWfP hW su R hΓ' s :=
  structPiSegS_eq hW su hΓ' s

theorem structPiSeg_contract (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (X : SuppliersVia E n) {Γ' : LCtx} (hΓ' : CtxWfT E n Γ') :
    StructPiContractP (structPiSeg hW su X hΓ').S :=
  (structPiSeg hW su X hΓ').hS

/-- A real `EvPar.structPi` (`pinSelfPayload`) at `[]` (`CtxWfT.nil`, not
    `illCtx`) goes through the adapter's `S`. The answer is that payload, and
    `hS` puts each cited leaf under a `SubEq` leaf of the step. `hW` and `su`
    stay parameters. -/
theorem structPiSeg_structPi (hW : EnvWfT emptyEnv)
    (su : F8A2Support.SortUnique emptyEnv 0) (hsep : SepAll emptyEnv 0) :
    (structPiSeg hW su (SuppliersVia.declining hsep) CtxWfT.nil).S pinPiR
        (EvPar.structPi pinSelfPayload) =
      some ⟨.sort .zero, .sort .zero, rfl, pinSelfPayload⟩ ∧
    ∀ ℓ ∈ pinSelfPayload.hc.leaves ++ pinSelfPayload.hcB.leaves,
      ∃ ℓ' ∈ (EvPar.structPi pinSelfPayload).leaves, SubEq ℓ ℓ' := by
  have hAns :
      (structPiSeg hW su (SuppliersVia.declining hsep) CtxWfT.nil).S pinPiR
          (EvPar.structPi pinSelfPayload) =
        some ⟨.sort .zero, .sort .zero, rfl, pinSelfPayload⟩ := by
    rw [structPiSeg_S_eq hW su (SuppliersVia.declining hsep) CtxWfT.nil
      (EvPar.structPi pinSelfPayload)]
    rfl
  refine ⟨hAns, fun ℓ hℓ => ?_⟩
  exact (structPiSeg_contract hW su (SuppliersVia.declining hsep) CtxWfT.nil)
    pinPiR (EvPar.structPi pinSelfPayload)
    ⟨.sort .zero, .sort .zero, rfl, pinSelfPayload⟩ hAns ℓ hℓ

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.no_proofIndex_at_pi
#print axioms Rcic.Declarative.F8Measure.no_proofIndex_at_pi_pin
#print axioms Rcic.Declarative.F8Measure.StructPiProcWfP
#print axioms Rcic.Declarative.F8Measure.StructPiContractWfP
#print axioms Rcic.Declarative.F8Measure.structPiProcWfP
#print axioms Rcic.Declarative.F8Measure.structPiProcWfP_contract
#print axioms Rcic.Declarative.F8Measure.no_invent_hΓ
#print axioms Rcic.Declarative.F8Measure.illPiTy
#print axioms Rcic.Declarative.F8Measure.illPiR
#print axioms Rcic.Declarative.F8Measure.illPiPayload
#print axioms Rcic.Declarative.F8Measure.structPiProcMut
#print axioms Rcic.Declarative.F8Measure.mutant_pi_at_illCtx
#print axioms Rcic.Declarative.F8Measure.structPiProcWfP_atSeg
#print axioms Rcic.Declarative.F8Measure.structPiSegS
#print axioms Rcic.Declarative.F8Measure.structPiSegS_eq
#print axioms Rcic.Declarative.F8Measure.structPiSegS_contract
#print axioms Rcic.Declarative.F8Measure.structPiSeg
#print axioms Rcic.Declarative.F8Measure.structPiSeg_S_eq
#print axioms Rcic.Declarative.F8Measure.structPiSeg_contract
#print axioms Rcic.Declarative.F8Measure.structPiSeg_structPi
