import rcic.RcicAnnLRWk
import rcic.RcicAnnLRRedG
/-!
# M2-a (ii.2) — the relation weakens, on the copy (amended by M1-d (iv))

L-RING C6's device (`RcicLRWk`, famrel-local) on `EqKAg`/`TyKAg`: weakening is
proved through the mutual recursor with two motives — type equality weakens to
the extension; type validity weakens to SOME relation at the extension that
contains the weakened pairs — and the Kripke clauses go through by COMPOSITION
of specs (`WkSpecA.comp`), never by their induction hypotheses. The base data
are typed reduction and conversion along a spec (`RcicAnnTyRedWk`), stuckness
and the prop key (`RcicAnnWkOps`). Lower heights enter as hypotheses
(`LowEqWkA`/`LowTyWkA`) and are tied by strong induction on the height
(`LR_wk_allAg`). The `fam` clause (M2-f (3)) weakens through `lfpWA_wk` (`RcicAnnFamWk`):
the clause relations at the extension are the originals at the composed spec, the
weakened clause's fixed point is the original's at the composed world (`lfpWA_reindex`), and
the fixed point's pairs weaken into it, the position
relations transported by the induction hypothesis and the kill criterion. No
ring-form premise anywhere.

`LRRelAg`: relatedness at a type through ANY validity derivation — canonical by
`TyKA_uniqueg` (the kill criterion), so THE relation at a type, and it weakens.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) motives and lower-height hypotheses -/

abbrev WkMotEqAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (LE : LowEqTA k) (LT : LowTyTA k) (Γ : LCtxA) (A B : ExprA) : Prop :=
  ∀ σ : WkSpecA, WkOkA E I n σ Γ →
    EqKAg E I n ρ₀ k LE LT (wkCtxA σ Γ) (wkExprA σ A) (wkExprA σ B)

abbrev WkMotTyAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (LE : LowEqTA k) (LT : LowTyTA k) (Γ : LCtxA) (A : ExprA) (R : ExprA → ExprA → Prop) : Prop :=
  ∀ σ : WkSpecA, WkOkA E I n σ Γ → ∃ R' : ExprA → ExprA → Prop,
    TyKAg E I n ρ₀ k LE LT (wkCtxA σ Γ) (wkExprA σ A) R' ∧
    ∀ x y : ExprA, R x y → R' (wkExprA σ x) (wkExprA σ y)

/-! ## (2) the minors, in constructor order -/

section Minors
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

theorem wkMinor_eqA_sortg (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A B : ExprA}
    {l l' : Level}
    (hA : WhTyA E I n Γ A (.sort l)) (hB : WhTyA E I n Γ B (.sort l'))
    (hk : ht ρ₀ l < k) (hl : eqN l l')
    (hc : Nonempty (TyConvA E I n Γ A B)) :
    WkMotEqAg E I n ρ₀ k LE LT Γ A B := fun σ hσ => by
  have hA' := whTyA_wk hE hI Γ σ hσ.1 hA
  have hB' := whTyA_wk hE hI Γ σ hσ.1 hB
  simp only [wkExprA_sort] at hA' hB'
  exact .sort hA' hB' hk hl (tyConvA_wk_ne hE hI σ hσ.1 hc)

theorem wkMinor_eqA_pig (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA}
    {A B D C D' C' : ExprA} {u v u' v' : Level}
    (hA : WhTyA E I n Γ A (.pi D u C v)) (hB : WhTyA E I n Γ B (.pi D' u' C' v'))
    (hu : eqN u u') (hv : eqN v v')
    (hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
    (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
    (hD'ty : Nonempty (HasTyA E I n Γ D' (.sort u')))
    (hC'ty : Nonempty (HasTyA E I n (.assumption D' :: Γ) C' (.sort v')))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (hDeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
    (hc : Nonempty (TyConvA E I n Γ A B))
    (_ihD : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ),
      WkMotTyAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (_ihDeq : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ),
      WkMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (_ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      WkMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C'))) :
    WkMotEqAg E I n ρ₀ k LE LT Γ A B := fun σ hσ => by
  have hA' := whTyA_wk hE hI Γ σ hσ.1 hA
  have hB' := whTyA_wk hE hI Γ σ hσ.1 hB
  rw [wkExprA_pi_ub] at hA' hB'
  have hDty' := hasTyA_wk_ne hE hI σ hσ.1 hDty
  have hD'ty' := hasTyA_wk_ne hE hI σ hσ.1 hD'ty
  rw [wkExprA_sort] at hDty' hD'ty'
  refine .pi hA' hB' hu hv hDty' (hasTyA_wk_ne_binder hE hI σ hσ.1 hCty) hD'ty'
    (hasTyA_wk_ne_binder hE hI σ hσ.1 hC'ty)
    (fun ρ => RD (WkSpecA.comp σ ρ)) ?_ ?_ ?_ (tyConvA_wk_ne hE hI σ hσ.1 hc)
  · intro ρ hρ
    have h := hD (WkSpecA.comp σ ρ) (wkOkA_comp hσ hρ)
    rw [wkCtxA_comp, wkExprA_comp] at h
    exact h
  · intro ρ hρ
    have h := hDeq (WkSpecA.comp σ ρ) (wkOkA_comp hσ hρ)
    rw [wkCtxA_comp, wkExprA_comp, wkExprA_comp] at h
    exact h
  · intro ρ hρ a a' hr
    have h := hC (WkSpecA.comp σ ρ) (wkOkA_comp hσ hρ) a a' hr
    rw [wkCtxA_comp, WkSpecA.ub_comp, wkExprA_comp, wkExprA_comp] at h
    exact h

/-- what a Kripke datum's induction hypothesis gives at an extension: the pairs of the
    relation at the identity world map into whatever relation the datum has there (the
    kill criterion identifies the two, M2-f (3c)). -/
theorem wkRelA_stepg {Γ : LCtxA} {σ : WkSpecA} (hσ : WkOkA E I n σ Γ) {D : ExprA}
    {Q Q' : ExprA → ExprA → Prop} (hQ : WkMotTyAg E I n ρ₀ k LE LT Γ D Q)
    (hQ' : TyKAg E I n ρ₀ k LE LT (wkCtxA σ Γ) (wkExprA σ D) Q') :
    ∀ f f', Q f f' → Q' (wkExprA σ f) (wkExprA σ f') := by
  intro f f' h
  obtain ⟨R', hR', hmap⟩ := hQ σ hσ
  rw [TyKA_uniqueg hQ' hR']
  exact hmap f f' h

theorem wkMinor_eqA_famg (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A B : ExprA} {r : Nat}
    {ls ls' : List Level} {ps ps' is is' : List ExprA} {m : CheckedMemberA} {u₀ : Level}
    (hA : WhTyA E I n Γ A (foldAppsA (.const r ls) (ps ++ is)))
    (hB : WhTyA E I n Γ B (foldAppsA (.const r ls') (ps' ++ is')))
    (hnA : hStepFnA E I.fn Γ (foldAppsA (.const r ls) (ps ++ is)) = none)
    (hnB : hStepFnA E I.fn Γ (foldAppsA (.const r ls') (ps' ++ is')) = none)
    (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM)
    (hsh : piBodyA m.mtypeA = .sort u₀)
    (hls : eqNList ls ls')
    (hps : ps.length = m.nparamsA)
    (hps' : ps'.length = m.nparamsA)
    (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop) (RsI : InnerRelsA)
    (hFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA)
        (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), E.members c = some cm → cm.mclass =
        .constructorM → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        D (Rs ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre)))
    (hFldF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), eqNListB n ls lsF →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → ArgsRelPA
        (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some
        (.pi D uD C vC) → TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
        (RsF ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre)))
    (hFldeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some
        (.pi D' uD' C' vC') → EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (hFldRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ (FieldShape.recursive 0) :: ks → eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some
        (.pi D' uD' C' vC') → RecDomRelA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ)) D
        D')
    (hFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF)
        m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        applyTelA pre' TF' = some (.pi D' uD' C' vC') → EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (hXFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA (ps'.map (wkExprA ρ))
        (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some
        (.pi D' uD' C' vC') → EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (hXRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ (FieldShape.recursive 0) :: ks → eqNList ls lsA → eqNListB n lsA lsC → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some
        (.pi D' uD' C' vC') → RecDomRelXA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ))
        (ps'.map (wkExprA ρ)) D D')
    (hXRes : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds : List FieldShape) (T T' : ExprA) (pre pre' : List ExprA)
        (R R' : ExprA), E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some
        r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        kinds pre pre' → applyTelA pre T = some R → applyTelA pre T' = some R' → RecDomRelXA E I n
        (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) R R')
    (hXResR : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds : List FieldShape) (T T' T'' : ExprA)
        (pre pre' : List ExprA) (R' R'' : ExprA), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → eqNList ls
        lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' → applyTelA (ps'.map (wkExprA ρ))
        (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T'' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        kinds pre pre' → applyTelA pre' T' = some R' → applyTelA pre' T'' = some R'' → RecDomRelXA E
        I n (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) R' R'')
    (hXFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA (ps'.map (wkExprA ρ))
        (instantiateLevelsA lsF m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF) m.nparamsA
        (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) → applyTelA pre
        TF' = some (.pi D' uD' C' vC') → EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (hxs : ∀ (TF : ExprA), applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF → ArgsRelPA
        (RsF [] ls) m.nparamsA ps TF is is')
    (hc : Nonempty (TyConvA E I n Γ A B))
    (hpar : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ lsX : List Level, eqNListB n ls lsX →
        ParConvA E I n (wkCtxA ρ Γ) (instantiateLevelsA lsX m.mtypeA) (instantiateLevelsA lsX m.mtypeA)
          (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)))
    (hFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        TyKAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁
          (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' zs.length zs))
    (hFldIeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
        EqKAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
    (hFldIRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
        applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
        RecDomRelA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (RsF (WkSpecA.comp ρ ρ')) ls
          ((ps.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁')
    (hXFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA zs (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
        EqKAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
    (hXRecI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
        applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs (wkExprA ρ' D') = some C₁' →
        RecDomRelXA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (RsF (WkSpecA.comp ρ ρ')) ls
          ((ps.map (wkExprA ρ)).map (wkExprA ρ')) ((ps'.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁')
    (hFldIdom : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        applyTelA pre' T' = some (.pi D' uD' C' vC') →
        Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D'))
    (hXFldIdom : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
        Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D'))
    (_ihFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA)
        (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), E.members c = some cm → cm.mclass =
        .constructorM → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → WkMotTyAg E I n ρ₀ k LE LT
        (wkCtxA ρ Γ) D (Rs ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre)))
    (ihFldF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), eqNListB n ls lsF →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → ArgsRelPA
        (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some
        (.pi D uD C vC) → WkMotTyAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
        (RsF ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre)))
    (_ihFldeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some
        (.pi D' uD' C' vC') → WkMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (_ihFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF)
        m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        applyTelA pre' TF' = some (.pi D' uD' C' vC') → WkMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (_ihXFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA (ps'.map (wkExprA ρ))
        (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some
        (.pi D' uD' C' vC') → WkMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (_ihXFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA (ps'.map (wkExprA ρ))
        (instantiateLevelsA lsF m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF) m.nparamsA
        (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) → applyTelA pre
        TF' = some (.pi D' uD' C' vC') → WkMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (_ihFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        WkMotTyAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁
          (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' zs.length zs))
    (_ihFldIeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
        WkMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
    (_ihXFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA zs (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
        WkMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁') :
    WkMotEqAg E I n ρ₀ k LE LT Γ A B := by
  intro σ hσ
  have hA' := whTyA_wk hE hI Γ σ hσ.1 hA
  have hB' := whTyA_wk hE hI Γ σ hσ.1 hB
  rw [wkExprA_foldAppsA, wkExprA_const, List.map_append] at hA' hB'
  have hnA' := hStepFnA_wk_none hE hI Γ σ hσ.1 hnA
  have hnB' := hStepFnA_wk_none hE hI Γ σ hσ.1 hnB
  rw [wkExprA_foldAppsA, wkExprA_const, List.map_append] at hnA' hnB'
  have hclF := liftA_instantiateLevelsA_closed (hE r m hm).1 ls
  -- the index relations weaken along the fiber: the induction hypothesis at the identity
  -- world, then the datum at the extension (`wkRelA_stepg`)
  have hcompF : ∀ (lsF : List Level) (TF : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
      (C : ExprA) (vC : Level) (f f' : ExprA), eqNListB n ls lsF →
      applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF →
      ArgsRelPA (RsF [] lsF) m.nparamsA ps TF pre pre' →
      ArgsRelPA (RsF σ lsF) m.nparamsA (ps.map (wkExprA σ)) (wkExprA σ TF) (pre.map (wkExprA σ))
        (pre'.map (wkExprA σ)) →
      applyTelA pre TF = some (.pi D uD C vC) →
      RsF [] lsF (m.nparamsA + pre.length) (ps ++ pre) f f' →
      RsF σ lsF (m.nparamsA + pre.length) ((ps ++ pre).map (wkExprA σ)) (wkExprA σ f)
        (wkExprA σ f') := by
    intro lsF TF pre pre' D uD C vC f f' hl hTF hw hw' hT hr
    have hclF' := liftA_instantiateLevelsA_closed (hE r m hm).1 lsF
    have hQ := ihFldF [] (wkOk₀A_nil _ _ _ _) lsF TF pre pre' D uD C vC hl
      (by rw [map_wkExprA_nil]; exact hTF) (by rw [map_wkExprA_nil]; exact hw) hT
    rw [map_wkExprA_nil] at hQ
    have hTσ : applyTelA (ps.map (wkExprA σ)) (instantiateLevelsA lsF m.mtypeA) =
        some (wkExprA σ TF) := by
      rw [applyTelA_wk_closed σ ps hclF', hTF]; rfl
    have hTw : applyTelA (pre.map (wkExprA σ)) (wkExprA σ TF) =
        some (.pi (wkExprA σ D) uD (wkExprA (WkSpecA.ub σ) C) vC) := by
      rw [applyTelA_wk σ pre TF, hT]
      show some (wkExprA σ (.pi D uD C vC)) = _
      rw [wkExprA_pi_ub]
    have hQ' := hFldF σ (wkOk₀A_of hσ) lsF (wkExprA σ TF) (pre.map (wkExprA σ))
      (pre'.map (wkExprA σ)) (wkExprA σ D) uD (wkExprA (WkSpecA.ub σ) C) vC hl hTσ hw' hTw
    rw [List.length_map, ← List.map_append] at hQ'
    exact wkRelA_stepg hσ hQ hQ' f f' hr
  refine .fam hA' hB' hnA' hnB' hm hind hsh hls (by rw [List.length_map]; exact hps)
    (by rw [List.length_map]; exact hps') (fun ρ => Rs (WkSpecA.comp σ ρ))
    (fun ρ => RsF (WkSpecA.comp σ ρ)) (fun ρ => RsI (WkSpecA.comp σ ρ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (tyConvA_wk_ne hE hI σ hσ.1 hc)
    (fun ρ hρ => by
      simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex]
      exact hpar (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    have h := hFld (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex]
    exact hFldF (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
  · intro ρ hρ
    have h := hFldeq (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hFldRec (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex]
    exact hFldFeq (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
  · intro ρ hρ
    have h := hXFld (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hXRec (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hXRes (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hXResR (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex]
    exact hXFeq (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
  · -- the index walk: at the extension, from the weakened telescope
    intro TF hTF
    obtain ⟨TF₀, hTF₀, rfl⟩ : ∃ TF₀, applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF₀ ∧
        wkExprA σ TF₀ = TF := by
      rw [applyTelA_wk_closed σ ps hclF] at hTF
      cases h0 : applyTelA ps (instantiateLevelsA ls m.mtypeA) with
      | none => rw [h0] at hTF; simp at hTF
      | some TF₀ => rw [h0] at hTF; exact ⟨TF₀, rfl, Option.some.inj hTF⟩
    show ArgsRelPA (RsF (WkSpecA.comp σ []) ls) _ _ _ _ _
    rw [WkSpecA.comp_nil]
    exact argsRelPA_wk σ (fun pre pre' D uD C vC f f' hw hw' hT hr =>
        hcompF ls TF₀ pre pre' D uD C vC f f' (eqNListB_refl (whTyA_famApp_bounded hA)) hTF₀ hw hw' hT hr)
      (hxs TF₀ hTF₀) (pre := []) (pre' := []) (by simp) (by simp) rfl (.nil _ _ _) (.nil _ _ _)
  · intro ρ hρ
    have h := hFldI (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hFldIeq (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hFldIRec (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hXFldI (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hXRecI (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hFldIdom (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hXFldIdom (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h

theorem wkMinor_eqA_stuckg (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A B N N' : ExprA}
    (hA : WhTyA E I n Γ A N) (hB : WhTyA E I n Γ B N')
    (hN : TripleLikeA E I Γ N) (hN' : TripleLikeA E I Γ N')
    (hc : Nonempty (TyConvA E I n Γ A B)) (hPP : IsPropTy E I Γ N ↔ IsPropTy E I Γ N') :
    WkMotEqAg E I n ρ₀ k LE LT Γ A B := fun σ hσ =>
  .stuck (whTyA_wk hE hI Γ σ hσ.1 hA) (whTyA_wk hE hI Γ σ hσ.1 hB)
    (tripleLikeA_wk hE hI Γ σ hσ.1 hN) (tripleLikeA_wk hE hI Γ σ hσ.1 hN')
    (tyConvA_wk_ne hE hI σ hσ.1 hc)
    ((isPropTy_wk_iff hE hI Γ σ hσ.1 N).trans (hPP.trans (isPropTy_wk_iff hE hI Γ σ hσ.1 N').symm))

theorem wkMinor_tyA_propg (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A A' : ExprA}
    (hA : WhTyA E I n Γ A A') (hn : hStepFnA E I.fn Γ A' = none) (hP : IsPropTy E I Γ A') :
    WkMotTyAg E I n ρ₀ k LE LT Γ A (fun a b =>
      Nonempty (HasTyA E I n Γ a A') ∧ Nonempty (HasTyA E I n Γ b A') ∧
      Nonempty (ConvA E I n Γ a b A')) := fun σ hσ =>
  ⟨_, .prop (whTyA_wk hE hI Γ σ hσ.1 hA) (hStepFnA_wk_none hE hI Γ σ hσ.1 hn)
      ((isPropTy_wk_iff hE hI Γ σ hσ.1 A').2 hP),
    fun _ _ ⟨hx, hy, hc⟩ =>
      ⟨hasTyA_wk_ne hE hI σ hσ.1 hx, hasTyA_wk_ne hE hI σ hσ.1 hy, convA_wk_ne hE hI σ hσ.1 hc⟩⟩

/-- DT-025/A-6 S1-g.2: a key-proposition weakens (`isPropTy_wk_iff`). -/
theorem propValidKA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} (σ : WkSpecA)
    (hσ : WkSpecA.ok σ Γ) {a : ExprA} (h : PropValidKA E I n Γ a) :
    PropValidKA E I n (wkCtxA σ Γ) (wkExprA σ a) := by
  obtain ⟨N, hN, hn, hP⟩ := h
  exact ⟨_, whTyA_wk hE hI Γ σ hσ hN, hStepFnA_wk_none hE hI Γ σ hσ hn,
    (isPropTy_wk_iff hE hI Γ σ hσ N).2 hP⟩

theorem wkMinor_tyA_sortPg (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A : ExprA}
    {l : Level} (hA : WhTyA E I n Γ A (.sort l)) (hz : isZero l = true) :
    WkMotTyAg E I n ρ₀ k LE LT Γ A (fun a b =>
      PropValidKA E I n Γ a ∧ PropValidKA E I n Γ b ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l)) ∧ PropEqA E I n Γ a b) := fun σ hσ => by
  have hA' := whTyA_wk hE hI Γ σ hσ.1 hA
  rw [wkExprA_sort] at hA'
  refine ⟨_, .sortP hA' hz, ?_⟩
  intro x y ⟨h1, h2, hx, hy, hc, hp⟩
  refine ⟨propValidKA_wk hE hI σ hσ.1 h1, propValidKA_wk hE hI σ hσ.1 h2, ?_, ?_, ?_,
    propEqA_wk hE hI hp σ hσ⟩
  · have h := hasTyA_wk_ne hE hI σ hσ.1 hx
    rw [wkExprA_sort] at h
    exact h
  · have h := hasTyA_wk_ne hE hI σ hσ.1 hy
    rw [wkExprA_sort] at h
    exact h
  · have h := convA_wk_ne hE hI σ hσ.1 hc
    rw [wkExprA_sort] at h
    exact h

theorem wkMinor_tyA_sortTg (hE : EnvClosedA E) (hI : IotaLiftA I)
    (HLE : LowEqWkA E I n k LE) (HLT : LowTyWkA E I n k LT) {Γ : LCtxA} {A : ExprA}
    {l : Level}
    (hA : WhTyA E I n Γ A (.sort l)) (hz : isZero l = false) (hk : ht ρ₀ l < k) :
    WkMotTyAg E I n ρ₀ k LE LT Γ A (fun a b =>
      LE (ht ρ₀ l) hk Γ a b ∧
      (∃ R, LT (ht ρ₀ l) hk Γ a R) ∧
      (∃ R, LT (ht ρ₀ l) hk Γ b R) ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l))) := fun σ hσ => by
  have hA' := whTyA_wk hE hI Γ σ hσ.1 hA
  rw [wkExprA_sort] at hA'
  refine ⟨_, .sortT hA' hz hk, ?_⟩
  intro x y ⟨h1, ⟨R1, hLT1⟩, ⟨R2, hLT2⟩, hx, hy, hc⟩
  refine ⟨HLE _ _ Γ σ hσ x y h1, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨R', hR'⟩ := HLT _ _ Γ σ hσ x R1 hLT1
    exact ⟨R', hR'⟩
  · obtain ⟨R', hR'⟩ := HLT _ _ Γ σ hσ y R2 hLT2
    exact ⟨R', hR'⟩
  · have h := hasTyA_wk_ne hE hI σ hσ.1 hx
    rw [wkExprA_sort] at h
    exact h
  · have h := hasTyA_wk_ne hE hI σ hσ.1 hy
    rw [wkExprA_sort] at h
    exact h
  · have h := convA_wk_ne hE hI σ hσ.1 hc
    rw [wkExprA_sort] at h
    exact h

theorem wkMinor_tyA_pig (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A D C : ExprA}
    {u v : Level}
    (hA : WhTyA E I n Γ A (.pi D u C v))
    (hnp : ¬ IsPropTy E I Γ (.pi D u C v))
    (hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
    (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (RC : WkSpecA → ExprA → ExprA → ExprA → Prop)
    (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (hCeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C)))
    (_ihD : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ),
      WkMotTyAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (_ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      WkMotTyAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (_ihCeq : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      WkMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C))) :
    WkMotTyAg E I n ρ₀ k LE LT Γ A (fun f g =>
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
      Nonempty (HasTyA E I n Γ f (.pi D u C v)) ∧ Nonempty (HasTyA E I n Γ g (.pi D u C v)) ∧
      Nonempty (ConvA E I n Γ f g (.pi D u C v))) := fun σ hσ => by
  have hA' := whTyA_wk hE hI Γ σ hσ.1 hA
  rw [wkExprA_pi_ub] at hA'
  have hnp' : ¬ IsPropTy E I (wkCtxA σ Γ) (wkExprA σ (.pi D u C v)) :=
    fun h => hnp ((isPropTy_wk_iff hE hI Γ σ hσ.1 _).1 h)
  rw [wkExprA_pi_ub] at hnp'
  have hDty' := hasTyA_wk_ne hE hI σ hσ.1 hDty
  rw [wkExprA_sort] at hDty'
  refine ⟨_, .pi hA' hnp' hDty' (hasTyA_wk_ne_binder hE hI σ hσ.1 hCty)
    (fun ρ => RD (WkSpecA.comp σ ρ)) ?_ (fun ρ => RC (WkSpecA.comp σ ρ)) ?_ ?_, ?_⟩
  · intro ρ hρ
    have h := hD (WkSpecA.comp σ ρ) (wkOkA_comp hσ hρ)
    rw [wkCtxA_comp, wkExprA_comp] at h
    exact h
  · intro ρ hρ a a' hr
    have h := hC (WkSpecA.comp σ ρ) (wkOkA_comp hσ hρ) a a' hr
    rw [wkCtxA_comp, WkSpecA.ub_comp, wkExprA_comp] at h
    exact h
  · intro ρ hρ a a' hr
    have h := hCeq (WkSpecA.comp σ ρ) (wkOkA_comp hσ hρ) a a' hr
    rw [wkCtxA_comp, WkSpecA.ub_comp, wkExprA_comp] at h
    exact h
  · intro f g ⟨h1, h2, h3, h4⟩
    refine ⟨fun ρ hρ a a' hr => ?_, ?_, ?_, ?_⟩
    · have h := h1 (WkSpecA.comp σ ρ) (wkOkA_comp hσ hρ) a a' hr
      rw [wkExprA_comp, wkExprA_comp] at h
      exact h
    · have h := hasTyA_wk_ne hE hI σ hσ.1 h2
      rw [wkExprA_pi_ub] at h
      exact h
    · have h := hasTyA_wk_ne hE hI σ hσ.1 h3
      rw [wkExprA_pi_ub] at h
      exact h
    · have h := convA_wk_ne hE hI σ hσ.1 h4
      rw [wkExprA_pi_ub] at h
      exact h

theorem wkMinor_tyA_famg (hE : EnvClosedA E) (hEN : EnvNormClosedA E) (hI : IotaLiftA I) {Γ : LCtxA}
    {A : ExprA} {r : Nat} {ls
    : List Level} {ps is : List ExprA} {m : CheckedMemberA} {u u₀ : Level}
    (hA : WhTyA E I n Γ A (foldAppsA (.const r ls) (ps ++ is)))
    (hn : hStepFnA E I.fn Γ (foldAppsA (.const r ls) (ps ++ is)) = none)
    (hnp : ¬ IsPropTy E I Γ (foldAppsA (.const r ls) (ps ++ is)))
    (hm : E.members r = some m)
    (hind : m.mclass = .inductiveM)
    (hsh : piBodyA m.mtypeA = .sort u₀)
    (hps : ps.length = m.nparamsA)
    (hu : applyTelA (ps ++ is) (instantiateLevelsA ls m.mtypeA) = some (.sort u))
    (hz : isZero u = false)
    (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsF : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop) (RsI : InnerRelsA)
    (hFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA)
        (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), E.members c = some cm → cm.mclass =
        .constructorM → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        D (Rs ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre)))
    (hFldF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), eqNListB n ls lsF →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → ArgsRelPA
        (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some
        (.pi D uD C vC) → TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
        (RsF ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre)))
    (hFldeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some
        (.pi D' uD' C' vC') → EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (hFldRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ (FieldShape.recursive 0) :: ks → eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some
        (.pi D' uD' C' vC') → RecDomRelA E I n (wkCtxA ρ Γ) r m (RsF ρ) ls (ps.map (wkExprA ρ)) D
        D')
    (hFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF)
        m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        applyTelA pre' TF' = some (.pi D' uD' C' vC') → EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (hxsD : ∀ (TF : ExprA), applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF → ArgsRelPA
        (RsF [] ls) m.nparamsA ps TF is is)
    (hFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        TyKAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁
          (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' zs.length zs))
    (hFldIeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
        EqKAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
    (hFldIRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
        applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
        RecDomRelA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (RsF (WkSpecA.comp ρ ρ')) ls
          ((ps.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁')
    (hFldIdom : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        applyTelA pre' T' = some (.pi D' uD' C' vC') →
        Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D'))
    (ihFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA)
        (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), E.members c = some cm → cm.mclass =
        .constructorM → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → WkMotTyAg E I n ρ₀ k LE LT
        (wkCtxA ρ Γ) D (Rs ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre)))
    (ihFldF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), eqNListB n ls lsF →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → ArgsRelPA
        (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some
        (.pi D uD C vC) → WkMotTyAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
        (RsF ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre)))
    (_ihFldeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), E.members c = some cm → cm.mclass = .constructorM
        → memberFamRefA cm = some r → ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre
        ++ FieldShape.nonrecursive :: ks → eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' → ArgsRelA (Rs ρ c lsC)
        (famRecRelA m (ps.map (wkExprA ρ)) lsA
        (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
        (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ'))) m.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some
        (.pi D' uD' C' vC') → WkMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (_ihFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF)
        m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        applyTelA pre' TF' = some (.pi D' uD' C' vC') → WkMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (_ihFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        WkMotTyAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁
          (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' zs.length zs))
    (_ihFldIeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
        (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
        (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
        kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
            (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) ρ))
            (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
              (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp ρ ρ')))
          m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
          (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
        ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
          (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
        WkMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁') :
    WkMotTyAg E I n ρ₀ k LE LT Γ A (fun a b =>
 LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) []
        (foldAppsA (.const r ls) (ps ++ is)) a b) := by
  intro σ hσ
  have hA' := whTyA_wk hE hI Γ σ hσ.1 hA
  rw [wkExprA_foldAppsA, wkExprA_const, List.map_append] at hA'
  have hn' := hStepFnA_wk_none hE hI Γ σ hσ.1 hn
  rw [wkExprA_foldAppsA, wkExprA_const, List.map_append] at hn'
  have hnp' : ¬ IsPropTy E I (wkCtxA σ Γ) (wkExprA σ (foldAppsA (.const r ls) (ps ++ is))) :=
    fun h => hnp ((isPropTy_wk_iff hE hI Γ σ hσ.1 _).1 h)
  rw [wkExprA_foldAppsA, wkExprA_const, List.map_append] at hnp'
  have hclF := liftA_instantiateLevelsA_closed (hE r m hm).1 ls
  -- the index relations weaken along the fiber: the induction hypothesis at the identity
  -- world, then the datum at the extension (`wkRelA_stepg`)
  have hcompF : ∀ (lsF : List Level) (TF : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
      (C : ExprA) (vC : Level) (f f' : ExprA), eqNListB n ls lsF →
      applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF →
      ArgsRelPA (RsF [] lsF) m.nparamsA ps TF pre pre' →
      ArgsRelPA (RsF σ lsF) m.nparamsA (ps.map (wkExprA σ)) (wkExprA σ TF) (pre.map (wkExprA σ))
        (pre'.map (wkExprA σ)) →
      applyTelA pre TF = some (.pi D uD C vC) →
      RsF [] lsF (m.nparamsA + pre.length) (ps ++ pre) f f' →
      RsF σ lsF (m.nparamsA + pre.length) ((ps ++ pre).map (wkExprA σ)) (wkExprA σ f)
        (wkExprA σ f') := by
    intro lsF TF pre pre' D uD C vC f f' hl hTF hw hw' hT hr
    have hclF' := liftA_instantiateLevelsA_closed (hE r m hm).1 lsF
    have hQ := ihFldF [] (wkOk₀A_nil _ _ _ _) lsF TF pre pre' D uD C vC hl
      (by rw [map_wkExprA_nil]; exact hTF) (by rw [map_wkExprA_nil]; exact hw) hT
    rw [map_wkExprA_nil] at hQ
    have hTσ : applyTelA (ps.map (wkExprA σ)) (instantiateLevelsA lsF m.mtypeA) =
        some (wkExprA σ TF) := by
      rw [applyTelA_wk_closed σ ps hclF', hTF]; rfl
    have hTw : applyTelA (pre.map (wkExprA σ)) (wkExprA σ TF) =
        some (.pi (wkExprA σ D) uD (wkExprA (WkSpecA.ub σ) C) vC) := by
      rw [applyTelA_wk σ pre TF, hT]
      show some (wkExprA σ (.pi D uD C vC)) = _
      rw [wkExprA_pi_ub]
    have hQ' := hFldF σ (wkOk₀A_of hσ) lsF (wkExprA σ TF) (pre.map (wkExprA σ))
      (pre'.map (wkExprA σ)) (wkExprA σ D) uD (wkExprA (WkSpecA.ub σ) C) vC hl hTσ hw' hTw
    rw [List.length_map, ← List.map_append] at hQ'
    exact wkRelA_stepg hσ hQ hQ' f f' hr
  -- the plain fields weaken likewise
  have hcomp : ∀ (c : Nat) (cm : CheckedMemberA) (lsC lsA : List Level) (kinds ksPre ks : List FieldShape)
      (T : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (f f' : ExprA),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
      eqNList ls lsA → eqNListB n lsA lsC →
      applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      ArgsRelA (Rs [] c lsC) (famRecRelA m ps lsA (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) []))
        (famFunRelA E I n (wkCtxA [] Γ) m (innerRelsA RsI [] c lsC) ps lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp [] ρ')))
        m.nparamsA ps T ksPre pre pre' →
      ArgsRelA (Rs σ c lsC) (famRecRelA m (ps.map (wkExprA σ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) σ))
        (famFunRelA E I n (wkCtxA σ Γ) m (innerRelsA RsI σ c lsC) (ps.map (wkExprA σ)) lsA
          (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) (WkSpecA.comp σ ρ')))
        m.nparamsA (ps.map (wkExprA σ)) (wkExprA σ T) ksPre (pre.map (wkExprA σ))
        (pre'.map (wkExprA σ)) →
      applyTelA pre T = some (.pi D uD C vC) →
      Rs [] c lsC (m.nparamsA + ksPre.length) (ps ++ pre) f f' →
      Rs σ c lsC (m.nparamsA + ksPre.length) ((ps ++ pre).map (wkExprA σ)) (wkExprA σ f)
        (wkExprA σ f') := by
    intro c cm lsC lsA kinds ksPre ks T pre pre' D uD C vC f f' hcm hk hfam hkinds hsp hlA hlAC hT
      hpre hpre' hTD hr
    have hclC := liftA_instantiateLevelsA_closed (envNormClosedA_getD hEN hE hcm hk) lsC
    have hQ := ihFld [] (wkOk₀A_nil _ _ _ _) c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk
      hfam hkinds hsp hlA hlAC (by rw [map_wkExprA_nil]; exact hT)
      (by rw [map_wkExprA_nil]; exact hpre) hTD
    rw [map_wkExprA_nil] at hQ
    have hTσ : applyTelA (ps.map (wkExprA σ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
        some (wkExprA σ T) := by
      rw [applyTelA_wk_closed σ ps hclC, hT]; rfl
    have hTw : applyTelA (pre.map (wkExprA σ)) (wkExprA σ T) =
        some (.pi (wkExprA σ D) uD (wkExprA (WkSpecA.ub σ) C) vC) := by
      rw [applyTelA_wk σ pre T, hTD]
      show some (wkExprA σ (.pi D uD C vC)) = _
      rw [wkExprA_pi_ub]
    have hQ' := hFld σ (wkOk₀A_of hσ) c cm lsA lsC kinds ksPre ks (wkExprA σ T) (pre.map (wkExprA σ))
      (pre'.map (wkExprA σ)) (wkExprA σ D) uD (wkExprA (WkSpecA.ub σ) C) vC hcm hk hfam hkinds hsp
      hlA hlAC hTσ hpre' hTw
    rw [← List.map_append] at hQ'
    exact wkRelA_stepg hσ hQ hQ' f f' hr
  refine ⟨_, .fam hA' hn' hnp' hm hind hsh (by rw [List.length_map]; exact hps) ?_ hz
    (fun ρ => Rs (WkSpecA.comp σ ρ)) (fun ρ => RsF (WkSpecA.comp σ ρ)) (fun ρ => RsI (WkSpecA.comp σ ρ))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
  · rw [← List.map_append, applyTelA_wk_closed σ (ps ++ is) hclF, hu]
    show some (wkExprA σ (.sort u)) = _
    rw [wkExprA_sort]
  · intro ρ hρ
    have h := hFld (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex]
    exact hFldF (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
  · intro ρ hρ
    have h := hFldeq (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hFldRec (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex]
    exact hFldFeq (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
  · -- the index walk: at the extension, from the weakened telescope
    intro TF hTF
    obtain ⟨TF₀, hTF₀, rfl⟩ : ∃ TF₀, applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF₀ ∧
        wkExprA σ TF₀ = TF := by
      rw [applyTelA_wk_closed σ ps hclF] at hTF
      cases h0 : applyTelA ps (instantiateLevelsA ls m.mtypeA) with
      | none => rw [h0] at hTF; simp at hTF
      | some TF₀ => rw [h0] at hTF; exact ⟨TF₀, rfl, Option.some.inj hTF⟩
    show ArgsRelPA (RsF (WkSpecA.comp σ []) ls) _ _ _ _ _
    rw [WkSpecA.comp_nil]
    exact argsRelPA_wk σ (fun pre pre' D uD C vC f f' hw hw' hT hr =>
        hcompF ls TF₀ pre pre' D uD C vC f f' (eqNListB_refl (whTyA_famApp_bounded hA)) hTF₀ hw hw' hT hr)
      (hxsD TF₀ hTF₀) (pre := []) (pre' := []) (by simp) (by simp) rfl (.nil _ _ _) (.nil _ _ _)
  · intro ρ hρ
    have h := hFldI (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hFldIeq (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hFldIRec (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro ρ hρ
    have h := hFldIdom (WkSpecA.comp σ ρ) (wkOk₀A_comp hσ hρ)
    simp only [map_wkExprA_comp, ← wkCtxA_comp, lfpWA_reindex, innerRelsA_comp, WkSpecA.comp_assoc] at h ⊢
    exact h
  · intro a b hab
    have hab' : LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) [] (foldAppsA (.const r ls) (ps ++ is)) a b :=
      hab
    show LfpWA (FamPhiWA E I n (wkCtxA σ Γ) r m (fun ρ => Rs (WkSpecA.comp σ ρ))
      (fun ρ => RsF (WkSpecA.comp σ ρ)) (fun ρ => RsI (WkSpecA.comp σ ρ))) [] _ _ _
    rw [lfpWA_reindex σ [], WkSpecA.comp_nil]
    have h := lfpWA_wk hE hEN hI hσ hm hcomp hcompF (carrierParamsA_famApp hps ls)
      (by rw [carrierLevelsA_foldAppsA]; exact eqNListA_refl ls) hab'
    rw [wkExprA_foldAppsA, wkExprA_const, List.map_append] at h
    exact h

theorem wkMinor_tyA_stuckg (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA} {A N : ExprA}
    (hA : WhTyA E I n Γ A N) (hN : StuckA E I Γ N) (hnp : ¬ IsPropTy E I Γ N) :
    WkMotTyAg E I n ρ₀ k LE LT Γ A (fun a b =>
      Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
      Nonempty (ConvA E I n Γ a b N) ∧
      ∃ Na, TyHRedStarA E I n Γ a Na N ∧ hStepFnA E I.fn Γ Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ b Nb N ∧ hStepFnA E I.fn Γ Nb = none) := fun σ hσ =>
  ⟨_, .stuck (whTyA_wk hE hI Γ σ hσ.1 hA) (stuckA_wk hE hI Γ σ hσ.1 hN)
      (fun h => hnp ((isPropTy_wk_iff hE hI Γ σ hσ.1 N).1 h)),
    fun _ _ ⟨hx, hy, hc, Na, cha, hna, Nb, chb, hnb⟩ =>
      ⟨hasTyA_wk_ne hE hI σ hσ.1 hx, hasTyA_wk_ne hE hI σ hσ.1 hy, convA_wk_ne hE hI σ hσ.1 hc,
        wkExprA σ Na, tyHRedStarA_wk hE hI σ hσ.1 cha, hStepFnA_wk_none hE hI Γ σ hσ.1 hna,
        wkExprA σ Nb, tyHRedStarA_wk hE hI σ hσ.1 chb, hStepFnA_wk_none hE hI Γ σ hσ.1 hnb⟩⟩

end Minors

/-! ## (3) one height, lower heights as hypotheses -/

theorem EqKA_wkg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
    {LE : LowEqTA k} {LT : LowTyTA k} (hE : EnvClosedA E) (hEN : EnvNormClosedA E) (hI : IotaLiftA I)
    (HLE : LowEqWkA E I n k LE) (HLT : LowTyWkA E I n k LT) :
    {Γ : LCtxA} → {A B : ExprA} → EqKAg E I n ρ₀ k LE LT Γ A B →
      ∀ σ : WkSpecA, WkOkA E I n σ Γ →
        EqKAg E I n ρ₀ k LE LT (wkCtxA σ Γ) (wkExprA σ A) (wkExprA σ B) :=
  fun {_Γ _A _B} h =>
  EqKAg.rec (motive_1 := fun Γ A B _ => WkMotEqAg E I n ρ₀ k LE LT Γ A B)
    (motive_2 := fun Γ A R _ => WkMotTyAg E I n ρ₀ k LE LT Γ A R)
    (wkMinor_eqA_sortg hE hI) (wkMinor_eqA_pig hE hI) (wkMinor_eqA_famg hE hI) (wkMinor_eqA_stuckg hE hI)
    (wkMinor_tyA_propg hE hI) (wkMinor_tyA_sortTg hE hI HLE HLT) (wkMinor_tyA_sortPg hE hI)
    (wkMinor_tyA_pig hE hI) (wkMinor_tyA_famg hE hEN hI) (wkMinor_tyA_stuckg hE hI)
    h

theorem TyKA_wkg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
    {LE : LowEqTA k} {LT : LowTyTA k} (hE : EnvClosedA E) (hEN : EnvNormClosedA E) (hI : IotaLiftA I)
    (HLE : LowEqWkA E I n k LE) (HLT : LowTyWkA E I n k LT) :
    {Γ : LCtxA} → {A : ExprA} → {R : ExprA → ExprA → Prop} → TyKAg E I n ρ₀ k LE LT Γ A R →
      ∀ σ : WkSpecA, WkOkA E I n σ Γ → ∃ R' : ExprA → ExprA → Prop,
        TyKAg E I n ρ₀ k LE LT (wkCtxA σ Γ) (wkExprA σ A) R' ∧
        ∀ x y : ExprA, R x y → R' (wkExprA σ x) (wkExprA σ y) :=
  fun {_Γ _A _R} h =>
  TyKAg.rec (motive_1 := fun Γ A B _ => WkMotEqAg E I n ρ₀ k LE LT Γ A B)
    (motive_2 := fun Γ A R _ => WkMotTyAg E I n ρ₀ k LE LT Γ A R)
    (wkMinor_eqA_sortg hE hI) (wkMinor_eqA_pig hE hI) (wkMinor_eqA_famg hE hI) (wkMinor_eqA_stuckg hE hI)
    (wkMinor_tyA_propg hE hI) (wkMinor_tyA_sortTg hE hI HLE HLT) (wkMinor_tyA_sortPg hE hI)
    (wkMinor_tyA_pig hE hI) (wkMinor_tyA_famg hE hEN hI) (wkMinor_tyA_stuckg hE hI)
    h

/-! ## (4) every height: the knot -/

theorem LR_wk_allAg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hEN : EnvNormClosedA E) (hI : IotaLiftA I) : ∀ k : Nat,
    (∀ {Γ : LCtxA} {A B : ExprA}, LREqAg E I n ρ₀ k Γ A B →
      ∀ σ : WkSpecA, WkOkA E I n σ Γ →
        LREqAg E I n ρ₀ k (wkCtxA σ Γ) (wkExprA σ A) (wkExprA σ B)) ∧
    (∀ {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop},
      LRTyAg E I n ρ₀ k Γ A R → ∀ σ : WkSpecA, WkOkA E I n σ Γ →
      ∃ R' : ExprA → ExprA → Prop,
        LRTyAg E I n ρ₀ k (wkCtxA σ Γ) (wkExprA σ A) R' ∧
        ∀ x y : ExprA, R x y → R' (wkExprA σ x) (wkExprA σ y)) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have HLE : LowEqWkA E I n k (fun j _ => LREqAg E I n ρ₀ j) :=
      fun j hj Γ σ hσ a b h => (ih j hj).1 h σ hσ
    have HLT : LowTyWkA E I n k (fun j _ => LRTyAg E I n ρ₀ j) :=
      fun j hj Γ σ hσ A R h => ((ih j hj).2 h σ hσ).elim fun R' hR' => ⟨R', hR'.1⟩
    refine ⟨fun h σ hσ => ?_, fun h σ hσ => ?_⟩
    · rw [LREqA_eqg] at h ⊢
      exact EqKA_wkg hE hEN hI HLE HLT h σ hσ
    · rw [LRTyA_eqg] at h ⊢
      exact TyKA_wkg hE hEN hI HLE HLT h σ hσ

theorem LREqA_wkg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hEN : EnvNormClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA} {A B : ExprA}
    (h : LREqAg E I n ρ₀ k Γ A B) (σ : WkSpecA) (hσ : WkOkA E I n σ Γ) :
    LREqAg E I n ρ₀ k (wkCtxA σ Γ) (wkExprA σ A) (wkExprA σ B) :=
  (LR_wk_allAg hE hEN hI k).1 h σ hσ

theorem LRTyA_wkg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hEN : EnvNormClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA} {A : ExprA}
    {R : ExprA → ExprA → Prop}
    (h : LRTyAg E I n ρ₀ k Γ A R) (σ : WkSpecA) (hσ : WkOkA E I n σ Γ) :
    ∃ R' : ExprA → ExprA → Prop,
      LRTyAg E I n ρ₀ k (wkCtxA σ Γ) (wkExprA σ A) R' ∧
      ∀ x y : ExprA, R x y → R' (wkExprA σ x) (wkExprA σ y) :=
  (LR_wk_allAg hE hEN hI k).2 h σ hσ

/-! ## (5) THE relation at a type, and it weakens -/

def LRRelAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (Γ : LCtxA) (A a b : ExprA) : Prop :=
  ∃ R : ExprA → ExprA → Prop, LRTyAg E I n ρ₀ k Γ A R ∧ R a b

theorem LRRelAg.of {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
    {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyAg E I n ρ₀ k Γ A R) {a b : ExprA} (hab : R a b) : LRRelAg E I n ρ₀ k Γ A a b :=
  ⟨R, h, hab⟩

theorem LRRelAg.at {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
    {Γ : LCtxA} {A a b : ExprA} (h : LRRelAg E I n ρ₀ k Γ A a b)
    {R : ExprA → ExprA → Prop} (hR : LRTyAg E I n ρ₀ k Γ A R) : R a b := by
  obtain ⟨R', hR', hab⟩ := h
  rw [LRTyA_uniqueg hR hR']
  exact hab

theorem LRRelA_wkg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hE : EnvClosedA E) (hEN : EnvNormClosedA E) (hI : IotaLiftA I) {k : Nat} {Γ : LCtxA} {A a b : ExprA}
    (h : LRRelAg E I n ρ₀ k Γ A a b) (σ : WkSpecA) (hσ : WkOkA E I n σ Γ) :
    LRRelAg E I n ρ₀ k (wkCtxA σ Γ) (wkExprA σ A) (wkExprA σ a) (wkExprA σ b) := by
  obtain ⟨R, hR, hab⟩ := h
  obtain ⟨R', hR', hmap⟩ := LRTyA_wkg hE hEN hI hR σ hσ
  exact ⟨R', hR', hmap a b hab⟩

#print axioms EqKA_wkg
#print axioms TyKA_wkg
#print axioms LR_wk_allAg
#print axioms LREqA_wkg
#print axioms LRTyA_wkg
#print axioms LRRelA_wkg

end Rcic.Declarative.Ann
