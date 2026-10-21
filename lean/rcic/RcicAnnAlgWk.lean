import rcic.RcicAnnWeaken

/-!
# M2-a (ii.1) — algorithmic equality weakens, on the copy

`AlgEq`/`AlgEqW`/`AlgNeu` under one insertion, then along a `WkSpecA`. Each
arm is the operations layer applied to its premises: `RedTo` and `IsPropTy`
through `RcicAnnWkOps`, the typing premises of `AlgEq.irr` through
`RcicAnnWeaken`, the variable arm through `RcicAnnCtxMorph` (the no-value
side too — a let-bound variable stays let-bound), η under the binder through
`liftA_zero_succ_swap` as in the declarative η. This is the base datum of the
relation's clauses (`hc : Nonempty (AlgEq …)`), so it is what M2-a (ii.2)
weakens the relation with.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section AlgWeaken
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

mutual

def algEqWeakenA (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) :
    {c : Nat} → {Γ : LCtxA} → c ≤ Γ.length → {a b A : ExprA} →
    AlgEq E I n Γ a b A →
    AlgEq E I n (insertAtA d c Γ) (liftA c 1 a) (liftA c 1 b) (liftA c 1 A)
  | _, _, hc, _, _, _, .red ha hb hA h =>
      .red (redTo_liftA hE hI d hc ha) (redTo_liftA hE hI d hc hb) (redTo_liftA hE hI d hc hA)
        (algEqWWeakenA hE hI d hc h)
  | _, _, hc, _, _, _, .irr hA hP ha hb =>
      .irr (redTo_liftA hE hI d hc hA) ((isPropTy_liftA_iff hE hI d hc _).2 hP)
        (hasTyWeakenA hE hI d hc ha) (hasTyWeakenA hE hI d hc hb)

def algEqWWeakenA (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) :
    {c : Nat} → {Γ : LCtxA} → c ≤ Γ.length → {a b A : ExprA} →
    AlgEqW E I n Γ a b A →
    AlgEqW E I n (insertAtA d c Γ) (liftA c 1 a) (liftA c 1 b) (liftA c 1 A)
  | c, Γ, hc, _, _, _, @AlgEqW.eta _ _ _ _ a b A B u v h => by
      have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
      have h' : AlgEq E I n (.assumption (liftA c 1 A) :: insertAtA d c Γ)
          (.app (liftA (c + 1) 1 (liftA 0 1 a)) (liftA (c + 1) 1 (.bvar 0)))
          (.app (liftA (c + 1) 1 (liftA 0 1 b)) (liftA (c + 1) 1 (.bvar 0)))
          (liftA (c + 1) 1 B) := algEqWeakenA hE hI d (c := c + 1) hc' h
      rw [liftA_bvar, shiftIdx_succ_zero, ← liftA_zero_succ_swap, ← liftA_zero_succ_swap] at h'
      show AlgEqW E I n (insertAtA d c Γ) (liftA c 1 a) (liftA c 1 b)
        (.pi (liftA c 1 A) u (liftA (c + 1) 1 B) v)
      exact .eta h'
  | _, _, _, _, _, _, .sorts h => .sorts h
  | c, Γ, hc, _, _, _, @AlgEqW.pi _ _ _ _ A A' B B' u v l hA hB => by
      have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
      show AlgEqW E I n (insertAtA d c Γ) (.pi (liftA c 1 A) u (liftA (c + 1) 1 B) v)
        (.pi (liftA c 1 A') u (liftA (c + 1) 1 B') v) (.sort l)
      exact .pi (algEqWeakenA hE hI d hc hA) (algEqWeakenA hE hI d (c := c + 1) hc' hB)
  | _, _, hc, _, _, _, .neu h hty =>
      .neu (algNeuWeakenA hE hI d hc h) (algEqWeakenA hE hI d hc hty)

def algNeuWeakenA (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) :
    {c : Nat} → {Γ : LCtxA} → c ≤ Γ.length → {a b A : ExprA} →
    AlgNeu E I n Γ a b A →
    AlgNeu E I n (insertAtA d c Γ) (liftA c 1 a) (liftA c 1 b) (liftA c 1 A)
  | c, Γ, hc, _, _, _, @AlgNeu.bvar _ _ _ _ i A h hv => by
      rw [liftA_bvar]
      have h' := lookupTypeA_insertAtA d c Γ hc i
      rw [h, Option.map_some'] at h'
      have hv' := lookupValueA_insertAtA d c Γ hc i
      rw [hv, Option.map_none'] at hv'
      exact .bvar h' hv'
  | c, _, _, _, _, _, @AlgNeu.const _ _ _ _ r ls ls' m hres h => by
      have hcl : liftA c 1 (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA ls m.mtypeA := by
        rw [← instantiateLevelsA_liftA, (hE r m hres).1 c]
      show AlgNeu E I n (insertAtA d c _) (.const r ls) (.const r ls')
        (liftA c 1 (instantiateLevelsA ls m.mtypeA))
      rw [hcl]
      exact .const hres h
  | c, _, hc, _, _, _, @AlgNeu.app _ _ _ _ f g a b Tf A B u v hf hred ha => by
      show AlgNeu E I n (insertAtA d c _) (.app (liftA c 1 f) (liftA c 1 a))
        (.app (liftA c 1 g) (liftA c 1 b)) (liftA c 1 (instantiate0A a B))
      rw [liftA_instantiate0A]
      exact .app (algNeuWeakenA hE hI d hc hf) (redTo_liftA hE hI d hc hred)
        (algEqWeakenA hE hI d hc ha)

end

/-! ## along a weakening spec -/

def algEq_wk (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {a b A : ExprA} →
    AlgEq E I n Γ a b A → AlgEq E I n (wkCtxA ρ Γ) (wkExprA ρ a) (wkExprA ρ b) (wkExprA ρ A)
  | _, [], _, _, _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, _, _, _, h =>
      algEq_wk hE hI (insertAtA d c Γ) ρ hρ (algEqWeakenA hE hI d hc h)

theorem algEq_wk_ne (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} (ρ : WkSpecA)
    (hρ : WkSpecA.ok ρ Γ) {a b A : ExprA} (h : Nonempty (AlgEq E I n Γ a b A)) :
    Nonempty (AlgEq E I n (wkCtxA ρ Γ) (wkExprA ρ a) (wkExprA ρ b) (wkExprA ρ A)) :=
  h.elim fun h => ⟨algEq_wk hE hI Γ ρ hρ h⟩

end AlgWeaken

#print axioms algEqWeakenA
#print axioms algEq_wk
#print axioms algEq_wk_ne

end Rcic.Declarative.Ann
