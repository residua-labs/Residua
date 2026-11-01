import rcic.RcicF3BoundedBetaOrigin
import rcic.RcicF3DBoundDefs

/-!
# Bounded evidence at an actual first reader beta demand

An original BoundDG field derivation supplies all the evidence below.
The source is decomposed at its actual appsSpine equation. All outer
application and type-conversion steps retain their original valuation,
level bound, constant bounds and local context.

The resulting argument is typed at the application's expected domain D.
The lambda retains its original annotation A, and the actual bounded
conversion chain between their Pi types is exposed. No equality of A
and D, semantic argument membership, or fitting own context is asserted.
This is automatic source provenance, not a new public syntax guard or a
premise added to the original root. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.BoundedReaderDemand
open Rcic.Declarative

variable {E : ResolvedEnv} {n : Nat}

/-- Only the outer typing constructor is inspected. -/
noncomputable def NoOuterConversion :
    {Γ : LCtx} → {e T : Expr Nat} → HasTyT E n Γ e T → Prop
  | _, _, _, .conv _ _ _ _ _ _ _ => False
  | _, _, _, _ => True

/-- One reusable extraction for every subject expression. The actual
outer conversions are composed in their original order. -/
theorem strip_conversions (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    LOKt σ N K d →
      ∃ (S : Expr Nat) (d0 : HasTyT E n Γ e S)
        (c : TyConvT E n Γ S T),
        LOKt σ N K d0 ∧ NoOuterConversion d0 ∧
          BoundedBVar.Bounded σ N K c
  | Γ, _, _, .sort _ l, hd =>
      ⟨_, .sort Γ l, .refl Γ _, hd, trivial, by simpa only [BoundedBVar.Bounded] using True.intro⟩
  | Γ, _, _, .bvar _ i A h, hd =>
      ⟨_, .bvar Γ i A h, .refl Γ _, hd, trivial, by simpa only [BoundedBVar.Bounded] using True.intro⟩
  | Γ, _, _, .const _ r ls m hm hn hl, hd =>
      ⟨_, .const Γ r ls m hm hn hl, .refl Γ _, hd, trivial, by simpa only [BoundedBVar.Bounded] using True.intro⟩
  | Γ, _, _, .pi _ A u B v dA dB, hd =>
      ⟨_, .pi Γ A u B v dA dB, .refl Γ _, hd, trivial, by simpa only [BoundedBVar.Bounded] using True.intro⟩
  | Γ, _, _, .lam _ A u body B dA db, hd =>
      ⟨_, .lam Γ A u body B dA db, .refl Γ _, hd, trivial, by simpa only [BoundedBVar.Bounded] using True.intro⟩
  | Γ, _, _, .app _ f a A B df da, hd =>
      ⟨_, .app Γ f a A B df da, .refl Γ _, hd, trivial, by simpa only [BoundedBVar.Bounded] using True.intro⟩
  | Γ, _, _, .letE _ A u v B body dA dv db, hd =>
      ⟨_, .letE Γ A u v B body dA dv db, .refl Γ _, hd, trivial, by simpa only [BoundedBVar.Bounded] using True.intro⟩
  | Γ, _, _, .lit _ k T de, hd =>
      ⟨_, .lit Γ k T de, .refl Γ _, hd, trivial, by simpa only [BoundedBVar.Bounded] using True.intro⟩
  | Γ, _, _, .conv _ _ S T u d c, hd => by
      obtain ⟨S0, d0, c0, h0, hcore, hc0⟩ :=
        strip_conversions σ N K d hd.1
      exact ⟨S0, d0, .trans Γ S0 S T c0 (.of Γ S T u c),
        h0, hcore, by simpa only [BoundedBVar.Bounded] using And.intro hc0 hd.2⟩

/-- Application inversion preserves the actual expected domain and the
complete outer conversion chain. -/
theorem application_parts (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {f a T : Expr Nat}
    (d : HasTyT E n Γ (.app f a) T) (hd : LOKt σ N K d) :
    ∃ (D C : Expr Nat)
      (df : HasTyT E n Γ f (.pi D C)) (da : HasTyT E n Γ a D)
      (c : TyConvT E n Γ (instantiate0 a C) T),
      LOKt σ N K df ∧ LOKt σ N K da ∧
        BoundedBVar.Bounded σ N K c := by
  obtain ⟨S, d0, c, h0, hcore, hc⟩ := strip_conversions σ N K d hd
  cases d0 with
  | app =>
      rename_i D C df da
      exact ⟨D, C, df, da, c, h0.1, h0.2, hc⟩
  | conv => exact False.elim hcore

/-- Lambda inversion exposes its original annotated domain together
with every bounded conversion to the application's requested Pi. -/
theorem lambda_parts (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {A body T : Expr Nat}
    (d : HasTyT E n Γ (.lam A body) T) (hd : LOKt σ N K d) :
    ∃ (u : Level) (B : Expr Nat)
      (dA : HasTyT E n Γ A (.sort u))
      (db : HasTyT E n (.assumption A :: Γ) body B)
      (c : TyConvT E n Γ (.pi A B) T),
      LOKt σ N K dA ∧ LOKt σ N K db ∧
        BoundedBVar.Bounded σ N K c := by
  obtain ⟨S, d0, c, h0, hcore, hc⟩ := strip_conversions σ N K d hd
  cases d0 with
  | lam =>
      rename_i u B dA db
      exact ⟨u, B, dA, db, c, h0.1, h0.2, hc⟩
  | conv => exact False.elim hcore

/-- Exact syntactic evidence at one beta demand. D is intentionally
distinct from A: their Pi conversion is produced, not silently inverted. -/
def BetaDemand (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A body arg : Expr Nat) : Prop :=
  ∃ (D C : Expr Nat) (u : Level) (B : Expr Nat)
    (dA : HasTyT E n Γ A (.sort u))
    (db : HasTyT E n (.assumption A :: Γ) body B)
    (da : HasTyT E n Γ arg D)
    (c : TyConvT E n Γ (.pi A B) (.pi D C)),
    LOKt σ N K dA ∧ LOKt σ N K db ∧ LOKt σ N K da ∧
      BoundedBVar.Bounded σ N K c

/-- The first beta node selected by the actual weak-head reader exposes
bounded premises directly from the source derivation, even with a suffix
of further applications and conversions around both heads. -/
theorem of_appsSpine (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    {Γ : LCtx} {e T A body arg : Expr Nat} {args : List (Expr Nat)}
    (d : HasTyT E n Γ e T) (hd : LOKt σ N K d)
    (hs : appsSpine e = (.lam A body, arg :: args)) :
    BetaDemand σ N K E n Γ A body arg := by
  have he := foldApps_appsSpine e
  rw [hs] at he
  change foldApps (.app (.lam A body) arg) args = e at he
  have hsource : ∃ d' : HasTyT E n Γ
      (foldApps (.app (.lam A body) arg) args) T, LOKt σ N K d' := by
    rw [he]
    exact ⟨d, hd⟩
  obtain ⟨d', hd'⟩ := hsource
  obtain ⟨T0, dr, hr⟩ :=
    lok_head σ N K args (.app (.lam A body) arg) d' hd'
  obtain ⟨D, C, df, da, _cout, hf, ha, _hcout⟩ :=
    application_parts σ N K dr hr
  obtain ⟨u, B, dA, db, c, hA, hb, hc⟩ :=
    lambda_parts σ N K df hf
  exact ⟨D, C, u, B, dA, db, da, c, hA, hb, ha, hc⟩

/-- Original BoundDG pays this evidence in the exact family-only global
scope and original own-parameter/earlier-field context. There is no fit,
mirror, membership, reader-preservation or normalization premise. -/
theorem of_boundDG (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E'
      hE hfam hctors hrec hmem))
    (node : RecNode E E' f rr rm)
    (j : Fin node.a.constructors.length) (vs : List Nat)
    (hvl : vs.length = node.a.family.member.arity)
    (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (k : Fin (node.a.constructorViews j).fields.length)
    {A body arg : Expr Nat} {args : List (Expr Nat)}
    (hs : appsSpine ((node.a.constructorViews j).fields[k]) =
      (.lam A body, arg :: args)) :
    BetaDemand (σOf vs) 4 K (extendEnv E f fm) node.a.family.member.arity
      (policyPrefixContext
        ((node.a.constructorViews j).parameters ++ (node.a.constructorViews j).fields)
        ((node.a.constructorViews j).parameters.length + k.val)) A body arg := by
  obtain ⟨l, d, hd⟩ := hD.2 node j vs hvl hvs k
  exact of_appsSpine (σOf vs) 4 K d hd hs

end Rcic.F3.PSet.BoundedReaderDemand

#print axioms Rcic.F3.PSet.BoundedReaderDemand.strip_conversions
#print axioms Rcic.F3.PSet.BoundedReaderDemand.of_appsSpine
#print axioms Rcic.F3.PSet.BoundedReaderDemand.of_boundDG
