import rcic.RcicAnnLRPer
import rcic.RcicAnnLRExpG
import rcic.RcicAnnLRConvG
/-!
# M2-d — the relation is a partial equivalence: symmetry and transitivity of
# `EqKAg` and of every term relation; validity transports along `EqKAg`

L-RING's `RcicLRPer` on the copy, with its residuals DISCHARGED: the face
carried `LRTyConj` (conjugation of the codomain relations) and `TyKDomSwap`
(validity of the right domain) as named hypotheses; here both are theorems,
because `eqKA_transportg` (M2-b (ii)) identifies the relations at `EqKAg`-equal
types and the one-sided codomain datum makes symmetry's pi case direct.

Order, as the dependencies dictate (M2_PLAN §3):
1. `eqKA_transport_perg` — transport AND every term relation's PER, one
   induction (M2-f (3b)): the pi cases of PER move across `C[a'] ≡ C[a]` by
   the transport induction hypothesis, and the `fam` case of transport moves
   the carrier along related indices by the index relations' PER; the `fam`
   case of PER is the fixed point's symmetry and transitivity (`lfpWA_symm`,
   `lfpWA_trans`, `RcicAnnFamPer`); `eqKA_transportg` and `tyKA_perg` are its
   projections (lower heights' PER as hypotheses);
2. `eqKA_transg` — induction on the first derivation, transport identifying the
   middle domain relations (at `fam`: the second index walk read with the
   first's relations and composed);
3. `eqKA_symm_validg` — symmetry TOGETHER with validity transport
   (`EqKAg A B → TyKAg A R → ∃ R', TyKAg B R'`), by one induction: the pi case's
   right-domain validity is the induction hypothesis on `hDeq`, its `hCeq` for
   `B` is `C'[a] ≡ C[a] ≡ C[a'] ≡ C'[a']` (the symmetry induction hypothesis,
   `hCeq`, and the one-sided `hC` at the reflexive pair `RD a' a'` from 1.).
Then the knot over all heights by strong induction (`LRPerA_allg`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (0) the canonical relation of a type -/

section Canon
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

/-- the relation a valid type gets, as a relation on terms (by `TyKA_uniqueg`
    there is one). -/
def canonRelAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (LE : LowEqTA k) (LT : LowTyTA k) (Γ : LCtxA) (A : ExprA) : ExprA → ExprA → Prop :=
  fun x y => ∃ R, TyKAg E I n ρ₀ k LE LT Γ A R ∧ R x y

theorem canonRelA_eqg {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : TyKAg E I n ρ₀ k LE LT Γ A R) : canonRelAg E I n ρ₀ k LE LT Γ A = R := by
  funext x y
  apply propext
  exact ⟨fun ⟨R', hR', hxy⟩ => by rw [← TyKA_uniqueg hR' h]; exact hxy, fun hxy => ⟨R, h, hxy⟩⟩

theorem tyKA_canong {Γ : LCtxA} {A : ExprA} (h : ∃ R, TyKAg E I n ρ₀ k LE LT Γ A R) :
    TyKAg E I n ρ₀ k LE LT Γ A (canonRelAg E I n ρ₀ k LE LT Γ A) := by
  obtain ⟨R, hR⟩ := h
  rw [canonRelA_eqg hR]
  exact hR

end Canon

/-! ## (1) every term relation is a PER (lower heights as hypotheses) -/

/-! `LowEqSymmA`, `LowEqTransA` and `PerMotA` live in `RcicAnnLRConv` (M2-f (3b)). -/

section TermPer
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

/-- DT-025/A-6 S1-g.2: the guarded stuck clause's chained quadruple is a PER — the chains
    travel with their terms (symmetry swaps them; transitivity keeps the outer two). -/
theorem perMinor_quadg {Γ : LCtxA} (N : ExprA) :
    PerMotA (fun a b : ExprA => Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
      Nonempty (ConvA E I n Γ a b N) ∧
      ∃ Na, TyHRedStarA E I n Γ a Na N ∧ hStepFnA E I.fn Γ Na = none ∧
        ∃ Nb, TyHRedStarA E I n Γ b Nb N ∧ hStepFnA E I.fn Γ Nb = none) :=
  ⟨fun _ _ ⟨h1, h2, h3, Na, cha, hna, Nb, chb, hnb⟩ =>
      ⟨h2, h1, h3.elim fun c => ⟨.symm _ _ _ _ c⟩, Nb, chb, hnb, Na, cha, hna⟩,
   fun _ _ _ ⟨h1, _, h3, Na, cha, hna, _⟩ ⟨_, h2', h3', _, _, _, Nc, chc, hnc⟩ =>
     ⟨h1, h2', h3.elim fun c => h3'.elim fun c' => ⟨.trans _ _ _ _ _ c c'⟩,
       Na, cha, hna, Nc, chc, hnc⟩⟩

/-- DT-025/A-6 S1-g.2: the guarded `sortP` relation (key-propositions) is a PER. -/
theorem perMinor_sortPg {Γ : LCtxA} (l : Level) :
    PerMotA (fun a b : ExprA =>
      PropValidKA E I n Γ a ∧ PropValidKA E I n Γ b ∧
      Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
      Nonempty (ConvA E I n Γ a b (.sort l)) ∧ PropEqA E I n Γ a b) :=
  ⟨fun _ _ ⟨h1, h2, h4, h5, h6, h7⟩ =>
     ⟨h2, h1, h5, h4, h6.elim fun c => ⟨.symm _ _ _ _ c⟩, propEqA_symm h7⟩,
   fun _ _ _ ⟨h1, _, h4, _, h6, h7⟩ ⟨_, h3', _, h5', h6', h7'⟩ =>
     ⟨h1, h3', h4, h5', h6.elim fun c => h6'.elim fun c' => ⟨.trans _ _ _ _ _ c c'⟩,
      propEqA_trans h7 h7'⟩⟩

theorem perMinor_pig {Γ : LCtxA} {A D C : ExprA} {u v : Level}
    (_hA : WhTyA E I n Γ A (.pi D u C v)) (_hnp : ¬ IsPropTy E I Γ (.pi D u C v))
    (_hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
    (_hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (_hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (RC : WkSpecA → ExprA → ExprA → ExprA → Prop)
    (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
    (_hCeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C)))
    (ihD : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ), PerMotA (RD ρ))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      PerMotA (RC ρ a))
    (ihCeq : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C))) :
    PerMotA (fun f g : ExprA =>
      (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
      Nonempty (HasTyA E I n Γ f (.pi D u C v)) ∧ Nonempty (HasTyA E I n Γ g (.pi D u C v)) ∧
      Nonempty (ConvA E I n Γ f g (.pi D u C v))) := by
  -- the codomain relations at related arguments are one relation
  have hmove : ∀ ρ (hρ : WkOkA E I n ρ Γ) a a', RD ρ a a' → RC ρ a' = RC ρ a := fun ρ hρ a a' hr =>
    ihCeq ρ hρ a' a ((ihD ρ hρ).1 a a' hr) _ _ (hC ρ hρ a' a ((ihD ρ hρ).1 a a' hr)) (hC ρ hρ a a' hr)
  refine ⟨fun f g ⟨h1, h2, h3, h4⟩ => ⟨fun ρ hρ a a' hr => ?_, h3, h2, h4.elim fun c => ⟨.symm _ _ _ _ c⟩⟩,
    fun f g h ⟨h1, h2, _, h4⟩ ⟨h1', _, h3', h4'⟩ =>
      ⟨fun ρ hρ a a' hr => ?_, h2, h3', h4.elim fun c => h4'.elim fun c' => ⟨.trans _ _ _ _ _ c c'⟩⟩⟩
  · have hr' : RD ρ a' a := (ihD ρ hρ).1 a a' hr
    have h := (ihC ρ hρ a' a hr').1 _ _ (h1 ρ hρ a' a hr')
    rw [hmove ρ hρ a a' hr] at h
    exact h
  · have hr' : RD ρ a' a := (ihD ρ hρ).1 a a' hr
    have hrr : RD ρ a' a' := (ihD ρ hρ).2 a' a a' hr' hr
    have h := h1' ρ hρ a' a' hrr
    rw [hmove ρ hρ a a' hr] at h
    exact (ihC ρ hρ a a' hr).2 _ _ _ (h1 ρ hρ a a' hr) h

/-- the fam clause: the fixed point is a PER on its fiber, from the clause's data and the
    induction hypotheses on its field and index domains at every world (`idxPerA_ofg`,
    `ctorPerA_ofg`, then `lfpWA_symm` / `lfpWA_trans`, M2-f (3c); R-NoFunRec-1 step 1 (1a)), and at a
    function-recursive field on its inner domains at every extension (R-NoFunRec-1 step 1 (1b)). -/
theorem perMinor_famg (hEN : EnvNormCtorTypeA E) {Γ : LCtxA} {A : ExprA} {r : Nat}
    {ls : List Level} {ps is : List ExprA} {m :
    CheckedMemberA} {u u₀ : Level}
    (_hA : WhTyA E I n Γ A (foldAppsA (.const r ls) (ps ++ is)))
    (_hn : hStepFnA E I.fn Γ (foldAppsA (.const r ls) (ps ++ is)) = none)
    (_hnp : ¬ IsPropTy E I Γ (foldAppsA (.const r ls) (ps ++ is)))
    (_hm : E.members r = some m)
    (_hind : m.mclass = .inductiveM)
    (hsh : piBodyA m.mtypeA = .sort u₀)
    (hps : ps.length = m.nparamsA)
    (_hu : applyTelA (ps ++ is) (instantiateLevelsA ls m.mtypeA) = some (.sort u))
    (_hz : isZero u = false)
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
    (_hFldeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
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
    (_hFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF)
        m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        applyTelA pre' TF' = some (.pi D' uD' C' vC') → EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (_hxsD : ∀ (TF : ExprA), applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF → ArgsRelPA
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
    (_hFldIeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
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
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → PerMotA
        (Rs ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre)))
    (ihFldF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), eqNListB n ls lsF →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → ArgsRelPA
        (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some
        (.pi D uD C vC) → PerMotA (RsF ρ lsF (m.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre)))
    (ihFldeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
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
        (.pi D' uD' C' vC') → TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (ihFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF)
        m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        applyTelA pre' TF' = some (.pi D' uD' C' vC') → TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
        D')
    (ihFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
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
        PerMotA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ' zs.length zs))
    (ihFldIeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
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
        TransMotAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁') :
    PerMotA (fun a b =>
 LfpWA (FamPhiWA E I n Γ r m Rs RsF RsI) []
        (foldAppsA (.const r ls) (ps ++ is)) a b) := by
  have w0 := wkOk₀A_nil E I n Γ
  have hP : FiberPerWA E I n Γ r m Rs RsF RsI ps ls := fun ρ hρ =>
    ⟨idxPerA_ofg hsh (hFldF ρ hρ) (ihFldF ρ hρ) (ihFldFeq ρ hρ),
     ctorPerA_ofg hEN (by rw [List.length_map]; exact hps) (hFld ρ hρ) (ihFld ρ hρ) (ihFldeq ρ hρ) (hFldRec ρ hρ)
       (hFldI ρ hρ) (ihFldI ρ hρ) (ihFldIeq ρ hρ) (hFldIRec ρ hρ) (hFldIdom ρ hρ)⟩
  have hAp : carrierParamsA m (foldAppsA (.const r ls) (ps ++ is)) = ps.map (wkExprA []) := by
    rw [map_wkExprA_nil]; exact carrierParamsA_famApp hps ls
  have hAl : eqNList ls (carrierLevelsA (foldAppsA (.const r ls) (ps ++ is))) := by
    rw [carrierLevelsA_foldAppsA]; exact eqNListA_refl ls
  exact ⟨fun _ _ h => lfpWA_symm hP hps w0 hAp hAl h,
    fun _ _ _ h₁ h₂ => lfpWA_trans hP hps w0 hAp hAl h₁ h₂⟩

/-- **transport and PER in one induction** (one height, lower heights as
    hypotheses): every type equality transports the term relation, and every term
    relation is a PER. Simultaneous because each needs the other on sub-derivations
    (M2-f (3b)): PER at a pi moves across `C[a'] ≡ C[a]` by transport, and transport
    at a family moves the carrier along related indices, which flips and composes the
    index walks by the index relations' PER. -/
theorem eqKA_transport_perg (hEN : EnvNormCtorTypeA E) (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE) :
    (∀ {Γ : LCtxA} {A B : ExprA}, EqKAg E I n ρ₀ k LE LT Γ A B → TransMotAg E I n ρ₀ k LE LT Γ A B) ∧
    (∀ {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop},
      TyKAg E I n ρ₀ k LE LT Γ A R → PerMotA R) :=
  ⟨fun h => EqKAg.rec (motive_1 := fun Γ A B _ => TransMotAg E I n ρ₀ k LE LT Γ A B)
    (motive_2 := fun _ _ R _ => PerMotA R)
    (fun hA hB hk hl hc => transMinor_sortg hA hB hk hl hc)
    (fun hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc ihD ihDeq ihC =>
      transMinor_pig hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc ihD ihDeq ihC)
    (transMinor_famg hEN)
    (fun hA hB hN hN' hc hPP => transMinor_stuckg hA hB hN hN' hc hPP)
    (fun _ _ _ => perMinor_triple _)
    (fun _ _ hk => perMinor_sortT HS HT hk)
    (fun _ _ => perMinor_sortPg _)
    (fun hA hnp hDty hCty RD hD RC hC hCeq ihD ihC ihCeq =>
      perMinor_pig hA hnp hDty hCty RD hD RC hC hCeq ihD ihC ihCeq)
    (perMinor_famg hEN)
    (fun _ _ _ => perMinor_quadg _)
    h,
  fun h => TyKAg.rec (motive_1 := fun Γ A B _ => TransMotAg E I n ρ₀ k LE LT Γ A B)
    (motive_2 := fun _ _ R _ => PerMotA R)
    (fun hA hB hk hl hc => transMinor_sortg hA hB hk hl hc)
    (fun hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc ihD ihDeq ihC =>
      transMinor_pig hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc ihD ihDeq ihC)
    (transMinor_famg hEN)
    (fun hA hB hN hN' hc hPP => transMinor_stuckg hA hB hN hN' hc hPP)
    (fun _ _ _ => perMinor_triple _)
    (fun _ _ hk => perMinor_sortT HS HT hk)
    (fun _ _ => perMinor_sortPg _)
    (fun hA hnp hDty hCty RD hD RC hC hCeq ihD ihC ihCeq =>
      perMinor_pig hA hnp hDty hCty RD hD RC hC hCeq ihD ihC ihCeq)
    (perMinor_famg hEN)
    (fun _ _ _ => perMinor_quadg _)
    h⟩

/-- **type equality transports the term relation** (one height). -/
theorem eqKA_transportg (hEN : EnvNormCtorTypeA E) (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE)
    {Γ : LCtxA} {A B : ExprA}
    (h : EqKAg E I n ρ₀ k LE LT Γ A B) {R R' : ExprA → ExprA → Prop}
    (tA : TyKAg E I n ρ₀ k LE LT Γ A R) (tB : TyKAg E I n ρ₀ k LE LT Γ B R') : R = R' :=
  (eqKA_transport_perg hEN HS HT).1 h R R' tA tB

/-- **every term relation is a PER** (one height). -/
theorem tyKA_perg (hEN : EnvNormCtorTypeA E) (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE)
    {Γ : LCtxA} {A : ExprA}
    {R : ExprA → ExprA → Prop} (h : TyKAg E I n ρ₀ k LE LT Γ A R) : PerMotA R :=
  (eqKA_transport_perg hEN HS HT).2 h

/-- a fiber's index and constructor walks flip and compose (`IdxPerA`, `CtorPerA`), from a
    clause's data there: every relation a PER (`tyKA_perg`) and transport along the domain
    equalities (`eqKA_transportg`) (M2-f (3c)), the inner domains' at a function-recursive field
    likewise (R-NoFunRec-1 step 1 (1b)). -/
theorem famFiberPerAg (hEN : EnvNormCtorTypeA E) (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE)
    {Γ : LCtxA} {r : Nat}
    {m : CheckedMemberA} {u₀ : Level} (hsh : piBodyA m.mtypeA = .sort u₀) {ps : List ExprA}
    {ls₀ : List Level} {Rs : Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    {RsF : List Level → Nat → List ExprA → ExprA → ExprA → Prop} {X : CRelA}
    {RI : Nat → List Level → Nat → List ExprA → WkSpecA → Nat → List ExprA → ExprA → ExprA → Prop}
    {XF : WkSpecA → CRelA} {RsFX : WkSpecA → List Level → Nat → List ExprA → ExprA → ExprA → Prop}
    (hps : ps.length = m.nparamsA)
    (hFld : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC : List Level) (kinds ksPre ks : List FieldShape)
        (T : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        TyKAg E I n ρ₀ k LE LT Γ D (Rs c lsC (m.nparamsA + ksPre.length) (ps ++ pre)))
    (hFldF : ∀ (lsF : List Level) (TF : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
        (C : ExprA) (vC : Level), eqNListB n ls₀ lsF →
        applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF →
        ArgsRelPA (RsF lsF) m.nparamsA ps TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        TyKAg E I n ρ₀ k LE LT Γ D (RsF lsF (m.nparamsA + pre.length) (ps ++ pre)))
    (hFldeq : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC lsC' : List Level)
        (kinds ksPre ks : List FieldShape) (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
        (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA ps (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some (.pi D' uD' C' vC') →
        EqKAg E I n ρ₀ k LE LT Γ D D')
    (hFldRec : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC lsC' : List Level)
        (kinds ksPre ks : List FieldShape) (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level)
        (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA ps (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some (.pi D' uD' C' vC') →
        RecDomRelA E I n Γ r m RsF ls₀ ps D D')
    (hFldFeq : ∀ (lsF lsF' : List Level) (TF TF' : ExprA) (pre pre' : List ExprA) (D : ExprA)
        (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        eqNListB n ls₀ lsF → eqNListB n lsF lsF' →
        applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TF →
        applyTelA ps (instantiateLevelsA lsF' m.mtypeA) = some TF' →
        ArgsRelPA (RsF lsF) m.nparamsA ps TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        applyTelA pre' TF' = some (.pi D' uD' C' vC') → EqKAg E I n ρ₀ k LE LT Γ D D')
    (hFldI : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC : List Level) (kinds ksPre ks : List FieldShape)
        (j : Nat) (T : ExprA) (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' Γ → ∀ (zs zs' : List ExprA) (D₁ : ExprA) (u₁ : Level) (C₁ : ExprA)
          (v₁ : Level),
        ArgsRelPA (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        TyKAg E I n ρ₀ k LE LT (wkCtxA ρ' Γ) D₁ (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ' zs.length zs))
    (hFldIeq : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC lsC' : List Level)
        (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA)
        (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA ps (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' Γ → ∀ (zs zs' : List ExprA) (D₁ : ExprA) (u₁ : Level) (C₁ : ExprA)
          (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
        ArgsRelPA (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' →
        applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
        applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
        EqKAg E I n ρ₀ k LE LT (wkCtxA ρ' Γ) D₁ D₁')
    (hFldIRec : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC lsC' : List Level)
        (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA)
        (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA ps (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some (.pi D' uD' C' vC') →
        ∀ (ρ' : WkSpecA), WkOkA E I n ρ' Γ → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
        ArgsRelPA (RI c lsC (m.nparamsA + ksPre.length) (ps ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' →
        zs.length = j + 1 → applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
        RecDomRelA E I n (wkCtxA ρ' Γ) r m (RsFX ρ') ls₀ (ps.map (wkExprA ρ')) C₁ C₁')
    (hFldIdom : ∀ (c : Nat) (cm : CheckedMemberA) (lsA lsC lsC' : List Level)
        (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA) (pre pre' : List ExprA) (D : ExprA)
        (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
        E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
        ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
        eqNList ls₀ lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
        applyTelA ps (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
        applyTelA ps (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
        ArgsRelA (Rs c lsC) (famRecRelA m ps lsA X) (famFunRelA E I n Γ m (RI c lsC) ps lsA XF)
          m.nparamsA ps T ksPre pre pre' →
        applyTelA pre T = some (.pi D uD C vC) → applyTelA pre' T' = some (.pi D' uD' C' vC') →
        Nonempty (TyConvA E I n Γ D D')) :
    IdxPerA n RsF m ps ls₀ ∧ CtorPerA E I n Γ r m Rs RsF RI X XF RsFX ps ls₀ :=
  ⟨idxPerA_ofg hsh hFldF
    (fun lsF TF pre pre' D uD C vC hl hTF hw hT => tyKA_perg hEN HS HT (hFldF lsF TF pre pre' D uD C vC hl hTF hw hT))
    (fun lsF lsF' TF TF' pre pre' D uD C vC D' uD' C' vC' hl hll hTF hTF' hw hT hT' _ _ tD tD' =>
      eqKA_transportg hEN HS HT (hFldFeq lsF lsF' TF TF' pre pre' D uD C vC D' uD' C' vC' hl hll hTF hTF' hw hT hT')
        tD tD'),
   ctorPerA_ofg hEN hps hFld
    (fun c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
      tyKA_perg hEN HS HT (hFld c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC h1 h2 h3 h4 h5 h6 h7 h8 h9 h10))
    (fun c cm lsA lsC lsC' kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' h1 h2 h3 h4 h5 h6 h7 h8 h9
        h10 h11 h12 h13 _ _ tD tD' =>
      eqKA_transportg hEN HS HT (hFldeq c cm lsA lsC lsC' kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC'
        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13) tD tD')
    hFldRec hFldI
    (fun c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ρ' hρ' zs zs' D₁ u₁
        C₁ v₁ hz hD₁ =>
      tyKA_perg hEN HS HT (hFldI c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ρ'
        hρ' zs zs' D₁ u₁ C₁ v₁ hz hD₁))
    (fun c cm lsA lsC lsC' kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' h1 h2 h3 h4 h5 h6 h7 h8 h9
        h10 h11 h12 h13 ρ' hρ' zs zs' D₁ u₁ C₁ v₁ D₁' u₁' C₁' v₁' hz hD₁ hD₁' _ _ tD tD' =>
      eqKA_transportg hEN HS HT (hFldIeq c cm lsA lsC lsC' kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC'
        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 ρ' hρ' zs zs' D₁ u₁ C₁ v₁ D₁' u₁' C₁' v₁' hz hD₁ hD₁') tD tD')
    hFldIRec hFldIdom⟩

end TermPer

/-! ## (1b) the carried inner relations; a cross-related pair back at an extension -/

section InnerCarry
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {r : Nat} {m : CheckedMemberA}

end InnerCarry

/-! ## (2) `EqKAg` is transitive -/

section EqTrans
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

abbrev TransMotEqAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (LE : LowEqTA k) (LT : LowTyTA k) (Γ : LCtxA) (A B : ExprA) : Prop :=
  ∀ X : ExprA, EqKAg E I n ρ₀ k LE LT Γ B X → EqKAg E I n ρ₀ k LE LT Γ A X

theorem transEqMinor_sortg {Γ : LCtxA} {A B : ExprA} {l l' : Level}
    (hA : WhTyA E I n Γ A (.sort l)) (hB : WhTyA E I n Γ B (.sort l'))
    (hk : ht ρ₀ l < k) (hl : eqN l l') (hc : Nonempty (TyConvA E I n Γ A B)) :
    TransMotEqAg E I n ρ₀ k LE LT Γ A B := by
  intro X h2
  cases h2 with
  | sort hB' hX _ hl' hc' =>
      have e := whTyA_det hB hB' (hStepFnA_sort _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
      exact .sort hA hX hk (eqNA_trans hl hl') (hc.elim fun c => hc'.elim fun c' => ⟨.trans _ _ _ _ c c'⟩)
  | pi hB' _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hB hB' (hStepFnA_sort _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      cases e
  | fam hB' _ hnB' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hB hB' (hStepFnA_sort _ _ _ _) hnB'
      exact absurd e.symm (foldAppsA_const_ne_sort _ _ _ _)
  | stuck hB' _ hN _ _ =>
      have e := whTyA_det hB hB' (hStepFnA_sort _ _ _ _) hN.1
      subst e
      exact (tripleLikeA_not_sort hN).elim

theorem transEqMinor_stuckg {Γ : LCtxA} {A B N N' : ExprA}
    (hA : WhTyA E I n Γ A N) (hB : WhTyA E I n Γ B N')
    (hN : TripleLikeA E I Γ N) (hN' : TripleLikeA E I Γ N') (hc : Nonempty (TyConvA E I n Γ A B))
    (hPP : IsPropTy E I Γ N ↔ IsPropTy E I Γ N') :
    TransMotEqAg E I n ρ₀ k LE LT Γ A B := by
  intro X h2
  cases h2 with
  | sort hB' _ _ _ _ =>
      have e := whTyA_det hB hB' hN'.1 (hStepFnA_sort _ _ _ _)
      subst e
      exact (tripleLikeA_not_sort hN').elim
  | pi hB' hX _ hv' _ _ _ _ _ _ _ _ hc' =>
      -- `B`'s normal form is a triple-like pi: a proposition; so is `X`'s, by `=ₙ`
      have e := whTyA_det hB hB' hN'.1 (hStepFnA_pi _ _ _ _ _ _ _)
      subst e
      have hPB := tripleLikeA_pi_isProp hN'
      refine .stuck hA hX hN
        ⟨hStepFnA_pi _ _ _ _ _ _ _, Or.inl ((isPropTy_pi_eqN hv').1 hPB)⟩
        (hc.elim fun c => hc'.elim fun c' => ⟨.trans _ _ _ _ c c'⟩)
        ⟨fun _ => ?_, fun _ => hPP.2 hPB⟩
      exact (isPropTy_pi_eqN hv').1 hPB
  | @fam _ _ _ _ lsB _ psB _ _ _ _ _ hB' hX hnB' hnX hm' hind' hsh' hls' hpsB hpsX _ _ _ _ _ _ _ _ _ _ _ _ _ hxs' hc' =>
      -- `B`'s family application is triple-like: a proposition; so is `X`'s
      have e := whTyA_det hB hB' hN'.1 hnB'
      subst e
      have hP := tripleLikeA_famApp_isProp hm' hind' hN'
      obtain ⟨TF, hTF⟩ := famApp_tel_of_isProp hm' hsh' hP lsB (xs' := psB) rfl
      have hlen := argsRelPA_length (hxs' TF hTF)
      refine .stuck hA hX hN
        ⟨hnX, Or.inl ((isPropTy_famApp_congr hm' hsh' hls'
          (by simp only [List.length_append, hpsB, hpsX, hlen])).1 hP)⟩
        (hc.elim fun c => hc'.elim fun c' => ⟨.trans _ _ _ _ c c'⟩)
        ⟨fun _ => ?_, fun _ => hPP.2 hP⟩
      exact (isPropTy_famApp_congr hm' hsh' hls'
          (by simp only [List.length_append, hpsB, hpsX, hlen])).1 hP
  | stuck hB'' hX hN'' hNX hc' hPP' =>
      have e := whTyA_det hB hB'' hN'.1 hN''.1
      subst e
      exact .stuck hA hX hN hNX (hc.elim fun c => hc'.elim fun c' => ⟨.trans _ _ _ _ c c'⟩)
        (hPP.trans hPP')

theorem transEqMinor_pig (hEN : EnvNormCtorTypeA E) (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE)
    {Γ : LCtxA} {A B D C D' C' : ExprA} {u v u' v' : Level}
    (hA : WhTyA E I n Γ A (.pi D u C v)) (hB : WhTyA E I n Γ B (.pi D' u' C' v'))
    (hu : eqN u u') (hv : eqN v v')
    (hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
    (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
    (_hD'ty : Nonempty (HasTyA E I n Γ D' (.sort u')))
    (_hC'ty : Nonempty (HasTyA E I n (.assumption D' :: Γ) C' (.sort v')))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (hDeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (_hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
    (hc : Nonempty (TyConvA E I n Γ A B))
    (_ihD : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ), True)
    (ihDeq : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ),
      TransMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      TransMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C'))) :
    TransMotEqAg E I n ρ₀ k LE LT Γ A B := by
  intro X h2
  cases h2 with
  | sort hB' _ _ _ _ =>
      have e := whTyA_det hB hB' (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
  | fam hB' _ hnB' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hB hB' (hStepFnA_pi _ _ _ _ _ _ _) hnB'
      exact absurd e.symm (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | stuck hB' hX hN hNX hc' hPP' =>
      -- `B`'s pi is triple-like: a proposition; so is `A`'s, by `=ₙ`; the
      -- equality `A ≡ X` is by conversion
      have e := whTyA_det hB hB' (hStepFnA_pi _ _ _ _ _ _ _) hN.1
      subst e
      have hPB := tripleLikeA_pi_isProp hN
      refine .stuck hA hX
        ⟨hStepFnA_pi _ _ _ _ _ _ _, Or.inl ((isPropTy_pi_eqN hv).2 hPB)⟩
        hNX (hc.elim fun c => hc'.elim fun c' => ⟨.trans _ _ _ _ c c'⟩)
        ⟨fun _ => hPP'.1 hPB, fun _ => ?_⟩
      exact (isPropTy_pi_eqN hv).2 hPB
  | pi hB' hX hu' hv' _ _ hD''ty hC''ty RD' hD' hD'eq hC' hc' =>
      have e := whTyA_det hB hB' (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      cases e
      -- the middle domain's two relations are one
      have hRD : ∀ ρ (hρ : WkOkA E I n ρ Γ), RD ρ = RD' ρ := fun ρ hρ =>
        eqKA_transportg hEN HS HT (hDeq ρ hρ) (hD ρ hρ) (hD' ρ hρ)
      refine .pi hA hX (eqNA_trans hu hu') (eqNA_trans hv hv') hDty hCty hD''ty hC''ty RD hD
        (fun ρ hρ => ihDeq ρ hρ _ (hD'eq ρ hρ))
        (fun ρ hρ a a' hr => ihC ρ hρ a a' hr _ (hC' ρ hρ a a' (by rw [← hRD ρ hρ]; exact hr)))
        (hc.elim fun c => hc'.elim fun c' => ⟨.trans _ _ _ _ c c'⟩)

/-- the fam clause (M2-f (3c)): two equalities through one family application compose.
    The left data stay; the cross data compose through the middle: a left walk crosses to the
    middle's own data (`argsRelA_famCross_fwd`, the cross data `CrossDataA` from transport
    against the middle's own data), the second equality's cross datum applies there, and the
    first's induction hypothesis closes (`hXFld`, `hXFeq`, and at a function-recursive field `hXFldI`
    once the inner walk has crossed too) or the cross-related pairs compose (`recDomRelXA_comp`, at the
    composed world for the inner codomains); the index walks compose on the left fiber. Through a triple-like middle
    the family application is a proposition, and so is the third type. -/
theorem transEqMinor_famg (hEN : EnvNormCtorTypeA E) (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE)
    {Γ : LCtxA} {A B : ExprA} {r
    : Nat} {ls ls' : List Level} {ps ps' is is' : List ExprA} {m : CheckedMemberA} {u₀ : Level}
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
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → True)
    (_ihFldF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), eqNListB n ls lsF →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → ArgsRelPA
        (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some
        (.pi D uD C vC) → True)
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
        (.pi D' uD' C' vC') → TransMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (_ihFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF)
        m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        applyTelA pre' TF' = some (.pi D' uD' C' vC') → TransMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
        D')
    (ihXFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
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
        (.pi D' uD' C' vC') → TransMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (ihXFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA (ps'.map (wkExprA ρ))
        (instantiateLevelsA lsF m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF) m.nparamsA
        (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) → applyTelA pre
        TF' = some (.pi D' uD' C' vC') → TransMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
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
        True)
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
        TransMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
    (ihXFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
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
        TransMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁') :
    TransMotEqAg E I n ρ₀ k LE LT Γ A B := by
  intro X h2
  have hpl : ps.length = ps'.length := by rw [hps, hps']
  have hplρ : ∀ ρ : WkSpecA, (ps.map (wkExprA ρ)).length = (ps'.map (wkExprA ρ)).length := fun ρ => by
    simp [hpl]
  have hpsρ : ∀ ρ : WkSpecA, (ps.map (wkExprA ρ)).length = m.nparamsA := fun ρ => by simp [hps]
  have hps'ρ : ∀ ρ : WkSpecA, (ps'.map (wkExprA ρ)).length = m.nparamsA := fun ρ => by simp [hps']
  have hPer : FiberPerWA E I n Γ r m Rs RsF RsI ps ls := fun ρ hρ =>
    famFiberPerAg hEN HS HT hsh (by rw [List.length_map]; exact hps) (hFld ρ hρ) (hFldF ρ hρ) (hFldeq ρ hρ)
      (hFldRec ρ hρ) (hFldFeq ρ hρ) (hFldI ρ hρ) (hFldIeq ρ hρ) (hFldIRec ρ hρ)
      (hFldIdom ρ hρ)
  have w0 := wkOk₀A_nil E I n Γ
  cases h2 with
  | @fam _ _ _ _ _ ls'' _ ps'' _ is'' _ _ hB₂ hX₂ hnB₂ hnX₂ hm₂ _ _ hls₂ hps₂ hps₂' Rs₂ RsF₂ RsI₂ hFld₂
      hFldF₂ _ _ _ hXFld₂ hXRec₂ hXRes₂ hXResR₂ hXFeq₂ hxs₂ hc₂ hpar₂ hFldI₂ _ _ hXFldI₂ hXRecI₂ _ hXFldIdom₂ =>
      have e := whTyA_det hB hB₂ hnB hnB₂
      obtain ⟨er, els, exs⟩ := foldAppsA_const_inj e
      subst er; subst els
      rw [hm] at hm₂
      injection hm₂ with em
      subst em
      obtain ⟨eps, eis⟩ := List.append_inj exs (by rw [hps', hps₂])
      subst eps; subst eis
      have hps''ρ : ∀ ρ : WkSpecA, (ps''.map (wkExprA ρ)).length = m.nparamsA := fun ρ => by simp [hps₂']
      -- the cross data from the left data to the middle's own, from transport
      have hXρ : CrossWA E I n Γ r m Rs Rs₂ RsF RsF₂ RsI RsI₂ ps ps' ls ls' := by
        intro ρ hρ
        refine ⟨fun lsF TF TF' pre pre' D uD C vC D' uD' C' vC' hl hTF hTF' hw hw' hD hD' =>
          eqKA_transportg hEN HS HT (hXFeq ρ hρ lsF TF TF' pre pre' D uD C vC D' uD' C' vC' hl hTF hTF' hw hD hD')
            (hFldF ρ hρ lsF TF pre pre' D uD C vC hl hTF hw hD)
            (hFldF₂ ρ hρ lsF TF' pre pre' D' uD' C' vC' ⟨eqNListA_trans (eqNListA_symm hls) hl.1, hl.2⟩ hTF' hw' hD'),
         fun c cm lsA lsA' lsC kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds hsp
            hlA hlAC hlA' hlA'C hT hT' hw hw' hD hD' =>
          eqKA_transportg hEN HS HT (hXFld ρ hρ c cm lsA lsC kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC'
              hcm hk hfam hkinds hsp hlA hlAC hT hT' hw hD hD')
            (hFld ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlAC hT hw hD)
            (hFld₂ ρ hρ c cm lsA' lsC kinds ksPre ks T' pre pre' D' uD' C' vC' hcm hk hfam hkinds hsp hlA'
              hlA'C hT' hw' hD'),
         hXRec ρ hρ, ?_,
         fun c cm lsA lsC lsC' kinds T T₁ T' T₁' pre pre' R R₁ R' R₁' hcm hk hfam hkinds hlA hlAC hlCC hT hT₁
            hT' hT₁' hw hR hR₁ hR' hR₁' =>
          ⟨hXRes ρ hρ c cm lsA lsC kinds T T₁ pre pre' R R₁ hcm hk hfam hkinds hlA hlAC hT hT₁ hw hR hR₁,
           hXResR ρ hρ c cm lsA lsC lsC' kinds T T' T₁' pre pre' R' R₁' hcm hk hfam hkinds hlA hlAC hlCC hT hT'
             hT₁' hw hR' hR₁'⟩,
         hpar ρ hρ, hXFldIdom ρ hρ⟩
        -- (I): along doubly-walked inner prefixes the two inner relations are one (transport against
        -- the middle's own data); the inner telescopes are rigid of one Π-count
        intro c cm lsA lsA' lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds hsp
          hlA hlAC hlA' hlA'C hT hT' hw hw' hD hD' ρ' hρ'
        have hrD := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hpsρ ρ) (argsRelA_length hw).1 hT hD
        have hrD' := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hps'ρ ρ) (argsRelA_length hw').1 hT' hD'
        have hwD := rigid_wkExprA ρ' D hrD.1
        have hwD' := rigid_wkExprA ρ' D' hrD'.1
        exact innerCrossA_of_one hwD.1 hwD'.1 (by rw [hwD.2, hwD'.2, hrD.2, hrD'.2])
          (fun q q' D₁ u₁ C₁ v₁ D₁' u₁' C₁' v₁' wl wr h1 h1' =>
            eqKA_transportg hEN HS HT
              (hXFldI ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam
                hkinds hsp hlA hlAC hT hT' hw hD hD' ρ' hρ' q q' D₁ u₁ C₁ v₁ D₁' u₁' C₁' v₁' wl h1 h1')
              (hFldI ρ hρ c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlAC
                hT hw hD ρ' hρ' q q' D₁ u₁ C₁ v₁ wl h1)
              (hFldI₂ ρ hρ c cm lsA' lsC kinds ksPre ks j T' pre pre' D' uD' C' vC' hcm hk hfam hkinds hsp
                hlA' hlA'C hT' hw' hD' ρ' hρ' q q' D₁' u₁' C₁' v₁' wr h1'))
          (fun zs zs' C₁ C₁' hzs hl hC hC' =>
            hXRecI ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam
              hkinds hsp hlA hlAC hT hT' hw hD hD' ρ' hρ' zs zs' C₁ C₁' hzs hl hC hC')
      refine .fam hA hX₂ hnA hnX₂ hm hind hsh (eqNListA_trans hls hls₂) hps hps₂' Rs RsF RsI hFld hFldF hFldeq
        hFldRec hFldFeq ?_ ?_ ?_ ?_ ?_ ?_ (hc.elim fun c => hc₂.elim fun c₂ => ⟨.trans _ _ _ _ c c₂⟩)
        (fun ρ hρ lsX hlX => parConvA_trans (hpar ρ hρ lsX hlX)
          (hpar₂ ρ hρ lsX ⟨eqNListA_trans (eqNListA_symm hls) hlX.1, hlX.2⟩)) hFldI hFldIeq hFldIRec ?_ ?_ hFldIdom ?_
      · intro ρ hρ c cm lsA lsC kinds ksPre ks T T'' pre pre' D uD C vC D'' uD'' C'' vC'' hcm hk hfam hkinds
          hsp hlA hlAC hT hT'' hw hD hD''
        have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
        obtain ⟨T', hT'⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ ρ) hT
        obtain ⟨D', uD', C', vC', hD'⟩ := applyTelA_pi_cross hrig (hplρ ρ) hT hT' rfl hD
        have hw' := argsRelA_famCross_fwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam
          hkinds hlA hlAC (eqNListA_refl lsA) hT hT' hsp hw
        exact ihXFld ρ hρ c cm lsA lsC kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds
          hsp hlA hlAC hT hT' hw hD hD' D''
          (hXFld₂ ρ hρ c cm lsA lsC kinds ksPre ks T' T'' pre pre' D' uD' C' vC' D'' uD'' C'' vC'' hcm hk hfam
            hkinds hsp (eqNListA_trans (eqNListA_symm hls) hlA) hlAC hT' hT'' hw' hD' hD'')
      · intro ρ hρ c cm lsA lsC kinds ksPre ks T T'' pre pre' D uD C vC D'' uD'' C'' vC'' hcm hk hfam hkinds
          hsp hlA hlAC hT hT'' hw hD hD''
        have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
        obtain ⟨T', hT'⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ ρ) hT
        obtain ⟨D', uD', C', vC', hD'⟩ := applyTelA_pi_cross hrig (hplρ ρ) hT hT' rfl hD
        have hw' := argsRelA_famCross_fwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam
          hkinds hlA hlAC (eqNListA_refl lsA) hT hT' hsp hw
        exact recDomRelXA_comp hsh (hPer ρ hρ).1 (hXρ ρ hρ) (hplρ ρ)
          (hXRec ρ hρ c cm lsA lsC kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds hsp
            hlA hlAC hT hT' hw hD hD')
          (hXRec₂ ρ hρ c cm lsA lsC kinds ksPre ks T' T'' pre pre' D' uD' C' vC' D'' uD'' C'' vC'' hcm hk hfam
            hkinds hsp (eqNListA_trans (eqNListA_symm hls) hlA) hlAC hT' hT'' hw' hD' hD'')
      · intro ρ hρ c cm lsA lsC kinds T T'' pre pre' R R'' hcm hk hfam hkinds hlA hlAC hT hT'' hw hR hR''
        have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
        obtain ⟨T', hT'⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ ρ) hT
        obtain ⟨R', hR'⟩ := applyTelA_some_cross hrig (hplρ ρ) hT hT' rfl hR
        have hw' := argsRelA_famCross_fwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam
          hkinds hlA hlAC (eqNListA_refl lsA) hT hT' (List.append_nil kinds).symm hw
        exact recDomRelXA_comp hsh (hPer ρ hρ).1 (hXρ ρ hρ) (hplρ ρ)
          (hXRes ρ hρ c cm lsA lsC kinds T T' pre pre' R R' hcm hk hfam hkinds hlA hlAC hT hT' hw hR hR')
          (hXRes₂ ρ hρ c cm lsA lsC kinds T' T'' pre pre' R' R'' hcm hk hfam hkinds
            (eqNListA_trans (eqNListA_symm hls) hlA) hlAC hT' hT'' hw' hR' hR'')
      · intro ρ hρ c cm lsA lsC lsC' kinds T T' T'' pre pre' R' R'' hcm hk hfam hkinds hlA hlAC hlCC hT hT' hT''
          hw hR' hR''
        have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
        obtain ⟨Tb, hTb⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ ρ) hT
        obtain ⟨Tb', hTb'⟩ := applyTelA_some_transfer_levels hrig lsC' lsC' (hplρ ρ) hT'
        obtain ⟨Rb', hRb'⟩ := applyTelA_some_cross hrig (hplρ ρ) hT' hTb' rfl hR'
        have hw' := argsRelA_famCross_fwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam
          hkinds hlA hlAC (eqNListA_refl lsA) hT hTb (List.append_nil kinds).symm hw
        exact recDomRelXA_comp hsh (hPer ρ hρ).1 (hXρ ρ hρ) (hplρ ρ)
          (hXResR ρ hρ c cm lsA lsC lsC' kinds T T' Tb' pre pre' R' Rb' hcm hk hfam hkinds hlA hlAC hlCC hT hT'
            hTb' hw hR' hRb')
          (hXResR₂ ρ hρ c cm lsA lsC lsC' kinds Tb Tb' T'' pre pre' Rb' R'' hcm hk hfam hkinds
            (eqNListA_trans (eqNListA_symm hls) hlA) hlAC hlCC hTb hTb' hT'' hw' hRb' hR'')
      · intro ρ hρ lsF TF TF'' pre pre' D uD C vC D'' uD'' C'' vC'' hl hTF hTF'' hw hD hD''
        obtain ⟨TF', hTF'⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) lsF lsF (hplρ ρ) hTF
        obtain ⟨D', uD', C', vC', hD'⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) (hplρ ρ) hTF hTF' rfl hD
        have hw' := argsRelPA_famCross_fwd hsh (hXρ ρ hρ) (hplρ ρ) hl hTF hTF' hw
        exact ihXFeq ρ hρ lsF TF TF' pre pre' D uD C vC D' uD' C' vC' hl hTF hTF' hw hD hD' D''
          (hXFeq₂ ρ hρ lsF TF' TF'' pre pre' D' uD' C' vC' D'' uD'' C'' vC'' ⟨eqNListA_trans (eqNListA_symm hls) hl.1, hl.2⟩
            hTF' hTF'' hw' hD' hD'')
      · intro TF hTF
        have hX0 := hXρ [] w0
        have hI0 := (hPer [] w0).1
        simp only [map_wkExprA_nil] at hX0 hI0
        obtain ⟨TF', hTF'⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) ls ls' hpl hTF
        obtain ⟨TFl, hTFl⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) ls ls' (xs' := ps) rfl hTF
        have hbB : eqNListB n ls ls' := ⟨hls, whTyA_famApp_bounded hB⟩
        have w2 := argsRelPA_famCross_bwd hsh hX0 hpl hbB hTFl hTF' (hxs₂ TF' hTF')
        exact hI0.comp (eqNListB_refl (whTyA_famApp_bounded hA)) hbB hTF hTFl (hxs TF hTF) w2
      · -- the inner cross data compose through the middle: the outer walk and then the inner walk cross
        -- to the middle's own data, whose cross datum applies there
        intro ρ hρ c cm lsA lsC kinds ksPre ks j T T'' pre pre' D uD C vC D'' uD'' C'' vC'' hcm hk hfam hkinds
          hsp hlA hlAC hT hT'' hw hD hD'' ρ' hρ' zs zs' D₁ u₁ C₁ v₁ D₁'' u₁'' C₁'' v₁'' hzs hD₁ hD₁''
        have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
        obtain ⟨T', hT'⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ ρ) hT
        obtain ⟨D', uD', C', vC', hD'⟩ := applyTelA_pi_cross hrig (hplρ ρ) hT hT' rfl hD
        have hw' := argsRelA_famCross_fwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam
          hkinds hlA hlAC (eqNListA_refl lsA) hT hT' hsp hw
        have hlA' := eqNListA_trans (eqNListA_symm hls) hlA
        have hIX := (hXρ ρ hρ).2.2.2.1 c cm lsA lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC'
          hcm hk hfam hkinds hsp hlA hlAC hlA' hlAC hT hT' hw hw' hD hD' ρ' hρ'
        have hrD := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hpsρ ρ) (argsRelA_length hw).1 hT hD
        have hrD' := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hps'ρ ρ) (argsRelA_length hw).1 hT' hD'
        have hwD := rigid_wkExprA ρ' D hrD.1
        have hwD' := rigid_wkExprA ρ' D' hrD'.1
        obtain ⟨D₁', u₁', C₁', v₁', hD₁'⟩ := applyTelA_pi_transfer hwD.1 hwD'.1
          (by rw [hwD.2, hwD'.2, hrD.2, hrD'.2]) rfl hD₁
        exact ihXFldI ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds
          hsp hlA hlAC hT hT' hw hD hD' ρ' hρ' zs zs' D₁ u₁ C₁ v₁ D₁' u₁' C₁' v₁' hzs hD₁ hD₁' D₁''
          (hXFldI₂ ρ hρ c cm lsA lsC kinds ksPre ks j T' T'' pre pre' D' uD' C' vC' D'' uD'' C'' vC'' hcm hk hfam
            hkinds hsp hlA' hlAC hT' hT'' hw' hD' hD'' ρ' hρ' zs zs' D₁' u₁' C₁' v₁' D₁'' u₁'' C₁'' v₁''
            (hIX.2.1 zs zs' hzs) hD₁' hD₁'')
      · -- the inner codomains: the two cross-related pairs compose at the composed world
        intro ρ hρ c cm lsA lsC kinds ksPre ks j T T'' pre pre' D uD C vC D'' uD'' C'' vC'' hcm hk hfam hkinds
          hsp hlA hlAC hT hT'' hw hD hD'' ρ' hρ' zs zs' C₁ C₁'' hzs hlen hC₁ hC₁''
        have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
        obtain ⟨T', hT'⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ ρ) hT
        obtain ⟨D', uD', C', vC', hD'⟩ := applyTelA_pi_cross hrig (hplρ ρ) hT hT' rfl hD
        have hw' := argsRelA_famCross_fwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam
          hkinds hlA hlAC (eqNListA_refl lsA) hT hT' hsp hw
        have hlA' := eqNListA_trans (eqNListA_symm hls) hlA
        have hIX := (hXρ ρ hρ).2.2.2.1 c cm lsA lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC'
          hcm hk hfam hkinds hsp hlA hlAC hlA' hlAC hT hT' hw hw' hD hD' ρ' hρ'
        have hrD := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hpsρ ρ) (argsRelA_length hw).1 hT hD
        have hrD' := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hps'ρ ρ) (argsRelA_length hw).1 hT' hD'
        have hwD := rigid_wkExprA ρ' D hrD.1
        have hwD' := rigid_wkExprA ρ' D' hrD'.1
        obtain ⟨C₁', hC₁'⟩ := applyTelA_some_of_cnt hwD.1 hwD'.1 (by rw [hwD.2, hwD'.2, hrD.2, hrD'.2]) hC₁
        have hρc := wkOk₀A_comp_ext hρ hρ'
        exact recDomRelXA_of_comp_world (recDomRelXA_comp hsh (hPer _ hρc).1 (hXρ _ hρc) (hplρ _)
          (recDomRelXA_comp_world (hXRecI ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C'
            vC' hcm hk hfam hkinds hsp hlA hlAC hT hT' hw hD hD' ρ' hρ' zs zs' C₁ C₁' hzs hlen hC₁ hC₁'))
          (recDomRelXA_comp_world (hXRecI₂ ρ hρ c cm lsA lsC kinds ksPre ks j T' T'' pre pre' D' uD' C' vC' D''
            uD'' C'' vC'' hcm hk hfam hkinds hsp hlA' hlAC hT' hT'' hw' hD' hD'' ρ' hρ' zs zs' C₁' C₁''
            (hIX.2.1 zs zs' hzs) hlen hC₁' hC₁'')))
      · -- the declared domains of a function-recursive position: the outer walk crosses to the middle's
        -- own data, whose cross datum applies there; the two conversions compose
        intro ρ hρ c cm lsA lsC kinds ksPre ks j T T'' pre pre' D uD C vC D'' uD'' C'' vC'' hcm hk hfam hkinds
          hsp hlA hlAC hT hT'' hw hD hD''
        have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
        obtain ⟨T', hT'⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ ρ) hT
        obtain ⟨D', uD', C', vC', hD'⟩ := applyTelA_pi_cross hrig (hplρ ρ) hT hT' rfl hD
        have hw' := argsRelA_famCross_fwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam
          hkinds hlA hlAC (eqNListA_refl lsA) hT hT' hsp hw
        have hlA' := eqNListA_trans (eqNListA_symm hls) hlA
        obtain ⟨c₁⟩ := hXFldIdom ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm
          hk hfam hkinds hsp hlA hlAC hT hT' hw hD hD'
        obtain ⟨c₂⟩ := hXFldIdom₂ ρ hρ c cm lsA lsC kinds ksPre ks j T' T'' pre pre' D' uD' C' vC' D'' uD''
          C'' vC'' hcm hk hfam hkinds hsp hlA' hlAC hT' hT'' hw' hD' hD''
        exact ⟨.trans _ _ _ _ c₁ c₂⟩
  | stuck hB' hX hN hNX hc' hPP' =>
      have e := whTyA_det hB hB' hnB hN.1
      subst e
      have hP := tripleLikeA_famApp_isProp hm hind hN
      obtain ⟨TF, hTF⟩ := famApp_tel_of_isProp hm hsh hP ls (xs' := ps) (by rw [hps, hps'])
      have hlen : (ps ++ is).length = (ps' ++ is').length := by
        simp only [List.length_append, hps, hps', argsRelPA_length (hxs TF hTF)]
      refine .stuck hA hX ⟨hnA, Or.inl ((isPropTy_famApp_congr hm hsh hls hlen).2 hP)⟩
        hNX (hc.elim fun c => hc'.elim fun c' => ⟨.trans _ _ _ _ c c'⟩)
        ⟨fun _ => hPP'.1 hP, fun _ => ?_⟩
      exact (isPropTy_famApp_congr hm hsh hls hlen).2 hP
  | sort hB' _ _ _ _ =>
      have e := whTyA_det hB hB' hnB (hStepFnA_sort _ _ _ _)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | pi hB' _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hB hB' hnB (hStepFnA_pi _ _ _ _ _ _ _)
      exact absurd e (foldAppsA_const_ne_pi _ _ _ _ _ _ _)

/-- **`EqKAg` is transitive** (one height; the lower heights' PER through
    transport and the index walks). -/
theorem eqKA_transg (hEN : EnvNormCtorTypeA E) (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE) :
    {Γ : LCtxA} → {A B X : ExprA} →
    EqKAg E I n ρ₀ k LE LT Γ A B → EqKAg E I n ρ₀ k LE LT Γ B X → EqKAg E I n ρ₀ k LE LT Γ A X :=
  fun {_Γ _A _B X} h h2 =>
  EqKAg.rec (motive_1 := fun Γ A B _ => TransMotEqAg E I n ρ₀ k LE LT Γ A B)
    (motive_2 := fun _ _ _ _ => True)
    (fun hA hB hk hl hc => transEqMinor_sortg hA hB hk hl hc)
    (fun hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc ihD ihDeq ihC =>
      transEqMinor_pig hEN HS HT hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc ihD ihDeq ihC)
    (transEqMinor_famg hEN HS HT)
    (fun hA hB hN hN' hc hPP => transEqMinor_stuckg hA hB hN hN' hc hPP)
    (fun _ _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ => True.intro)
    h X h2

end EqTrans

/-! ## (3) `EqKAg` is symmetric, and validity transports along it -/

section EqSymm
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}
  {LE : LowEqTA k} {LT : LowTyTA k}

abbrev SymmMotEqAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (LE : LowEqTA k) (LT : LowTyTA k) (Γ : LCtxA) (A B : ExprA) : Prop :=
  EqKAg E I n ρ₀ k LE LT Γ B A ∧
  (∀ R : ExprA → ExprA → Prop, TyKAg E I n ρ₀ k LE LT Γ A R → ∃ R', TyKAg E I n ρ₀ k LE LT Γ B R')

theorem symmEqMinor_sortg {Γ : LCtxA} {A B : ExprA} {l l' : Level}
    (hA : WhTyA E I n Γ A (.sort l)) (hB : WhTyA E I n Γ B (.sort l'))
    (hk : ht ρ₀ l < k) (hl : eqN l l') (hc : Nonempty (TyConvA E I n Γ A B)) :
    SymmMotEqAg E I n ρ₀ k LE LT Γ A B :=
  have hk' : ht ρ₀ l' < k := by rw [← ht_of_eqN hl]; exact hk
  ⟨.sort hB hA hk' (eqNA_symm hl) (hc.elim fun c => ⟨c.symm⟩), fun _ _ => by
    cases hz : isZero l' with
    | false => exact ⟨_, .sortT hB hz hk'⟩
    | true => exact ⟨_, .sortP hB hz⟩⟩

theorem symmEqMinor_stuckg {Γ : LCtxA} {A B N N' : ExprA}
    (hA : WhTyA E I n Γ A N) (hB : WhTyA E I n Γ B N')
    (hN : TripleLikeA E I Γ N) (hN' : TripleLikeA E I Γ N') (hc : Nonempty (TyConvA E I n Γ A B))
    (hPP : IsPropTy E I Γ N ↔ IsPropTy E I Γ N') :
    SymmMotEqAg E I n ρ₀ k LE LT Γ A B :=
  -- validity moves to `B` on `A`'s side of the boundary, which `hPP` carries across
  ⟨.stuck hB hA hN' hN (hc.elim fun c => ⟨c.symm⟩) hPP.symm, fun _ tA =>
    tyKA_valid_of_tripleLikeg hB hN'
      ((tyKA_tripleLike_casesg hA hN tA).elim (fun ⟨hP, _⟩ => .inl (hPP.1 hP))
        (fun ⟨_, hnp, _⟩ => .inr fun hP' => hnp (hPP.2 hP')))⟩

theorem symmEqMinor_pig (hEN : EnvNormCtorTypeA E) (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE)
    {Γ : LCtxA} {A B D C D' C' : ExprA} {u v u' v' : Level}
    (hA : WhTyA E I n Γ A (.pi D u C v)) (hB : WhTyA E I n Γ B (.pi D' u' C' v'))
    (hu : eqN u u') (hv : eqN v v')
    (hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
    (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
    (hD'ty : Nonempty (HasTyA E I n Γ D' (.sort u')))
    (hC'ty : Nonempty (HasTyA E I n (.assumption D' :: Γ) C' (.sort v')))
    (RD : WkSpecA → ExprA → ExprA → Prop)
    (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
    (_hDeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
    (hc : Nonempty (TyConvA E I n Γ A B))
    (_ihD : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ), True)
    (ihDeq : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ),
      SymmMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
    (ihC : ∀ (ρ : WkSpecA) (_hρ : WkOkA E I n ρ Γ) (a a' : ExprA) (_hr : RD ρ a a'),
      SymmMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ)
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
        (instantiate0A a (wkExprA (WkSpecA.ub ρ) C'))) :
    SymmMotEqAg E I n ρ₀ k LE LT Γ A B := by
  -- the right domain is valid (the induction hypothesis on `hDeq`), with the
  -- canonical relation, which is the left domain's relation
  have hD' : ∀ ρ (hρ : WkOkA E I n ρ Γ),
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D')
        (canonRelAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D')) :=
    fun ρ hρ => tyKA_canong ((ihDeq ρ hρ).2 (RD ρ) (hD ρ hρ))
  have hRD' : ∀ ρ (hρ : WkOkA E I n ρ Γ),
      canonRelAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D') = RD ρ :=
    fun ρ hρ => eqKA_transportg hEN HS HT (ihDeq ρ hρ).1 (hD' ρ hρ) (hD ρ hρ)
  refine ⟨.pi hB hA (eqNA_symm hu) (eqNA_symm hv) hD'ty hC'ty hDty hCty _ hD'
    (fun ρ hρ => (ihDeq ρ hρ).1)
    (fun ρ hρ a a' hr' => (ihC ρ hρ a a' (by rw [← hRD' ρ hρ]; exact hr')).1)
    (hc.elim fun c => ⟨c.symm⟩), fun R tA => ?_⟩
  cases tA with
  | sortT hA₁ _ _ =>
      have e := whTyA_det hA hA₁ (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
  | sortP hA₁ _ =>
      have e := whTyA_det hA hA₁ (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_sort _ _ _ _)
      cases e
  | stuck hA₁ hN₁ =>
      have e := whTyA_det hA hA₁ (hStepFnA_pi _ _ _ _ _ _ _) hN₁.1
      subst e
      exact (stuckA_not_pi hN₁).elim
  | fam hA₁ hn₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hA₁ (hStepFnA_pi _ _ _ _ _ _ _) hn₁
      exact absurd e.symm (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | prop hA₁ hn₁ hP₁ =>
      have e := whTyA_det hA hA₁ (hStepFnA_pi _ _ _ _ _ _ _) hn₁
      subst e
      exact ⟨_, .prop hB (hStepFnA_pi _ _ _ _ _ _ _) ((isPropTy_pi_eqN hv).1 hP₁)⟩
  | pi hA₁ hnp₁ _ _ RD₁ hD₁ RC₁ hC₁ hCeq₁ =>
      have e := whTyA_det hA hA₁ (hStepFnA_pi _ _ _ _ _ _ _) (hStepFnA_pi _ _ _ _ _ _ _)
      cases e
      have hRD₁ : ∀ ρ (hρ : WkOkA E I n ρ Γ), RD ρ = RD₁ ρ :=
        fun ρ hρ => TyKA_uniqueg (hD ρ hρ) (hD₁ ρ hρ)
      refine ⟨_, .pi hB (fun h => hnp₁ ((isPropTy_pi_eqN hv).2 h)) hD'ty hC'ty _ hD'
        (fun ρ a => canonRelAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
        (fun ρ hρ a a' hr' => ?_) (fun ρ hρ a a' hr' => ?_)⟩
      · -- validity of `C'[a]`: the induction hypothesis on `hC`, from `C[a]`'s
        have hr : RD ρ a a' := by rw [← hRD' ρ hρ]; exact hr'
        have hr₁ : RD₁ ρ a a' := by rw [← hRD₁ ρ hρ]; exact hr
        exact tyKA_canong ((ihC ρ hρ a a' hr).2 (RC₁ ρ a) (hC₁ ρ hρ a a' hr₁))
      · -- `C'[a] ≡ C[a] ≡ C[a'] ≡ C'[a']`
        have hr : RD ρ a a' := by rw [← hRD' ρ hρ]; exact hr'
        have hr₁ : RD₁ ρ a a' := by rw [← hRD₁ ρ hρ]; exact hr
        have hper := tyKA_perg hEN HS HT (hD ρ hρ)
        have hrr : RD ρ a' a' := hper.2 a' a a' (hper.1 a a' hr) hr
        exact eqKA_transg hEN HS HT (ihC ρ hρ a a' hr).1
          (eqKA_transg hEN HS HT (hCeq₁ ρ hρ a a' hr₁) (hC ρ hρ a' a' hrr))

/-- the fam clause (M2-f (3c)): the equality reversed. The right instance's data are the left
    data CARRIED across the parameters (`famCarryRsA`, `famCarryRsFA`): at the right parameters
    and a prefix, the left relation at the left parameters and the same prefix. Their validity is
    the cross data's symmetry induction hypothesis (validity transport) with transport
    (`eqKA_transportg`), a right walk crossing back to the left (`argsRelA_famCross_bwd`); their
    equalities chain through the left fiber (`ctorWalkA_flip`, `recDomRelXA_chain`); the reversed
    cross data are the induction hypothesis's symmetry and the reversed pairs
    (`recDomRelXA_rev`). At a function-recursive field the carried inner relations are the left ones
    (`famCarryRsIA`, `innerRelsA_carry`) and the inner data move back the same way, the inner walks
    crossing by the cross data's (I) and flipping by the fiber's `InnerPerA` (R-NoFunRec-1 step 1 (1b)).
    A family clause at `A` moves to `B` with the same carried data; the
    Prop boundary and the sort are carried by the family's result sort. -/
theorem symmEqMinor_famg (hEN : EnvNormCtorTypeA E) (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE)
    {Γ : LCtxA} {A B : ExprA} {r
    : Nat} {ls ls' : List Level} {ps ps' is is' : List ExprA} {m : CheckedMemberA} {u₀ : Level}
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
        ksPre pre pre' → applyTelA pre T = some (.pi D uD C vC) → True)
    (_ihFldF : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), eqNListB n ls lsF →
        applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → ArgsRelPA
        (RsF ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some
        (.pi D uD C vC) → True)
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
        (.pi D' uD' C' vC') → SymmMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (_ihFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA
        (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF)
        m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) →
        applyTelA pre' TF' = some (.pi D' uD' C' vC') → SymmMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D
        D')
    (ihXFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
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
        (.pi D' uD' C' vC') → SymmMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
    (ihXFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF TF' : ExprA)
        (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level) (D' : ExprA)
        (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → applyTelA (ps.map (wkExprA ρ))
        (instantiateLevelsA lsF m.mtypeA) = some TF → applyTelA (ps'.map (wkExprA ρ))
        (instantiateLevelsA lsF m.mtypeA) = some TF' → ArgsRelPA (RsF ρ lsF) m.nparamsA
        (ps.map (wkExprA ρ)) TF pre pre' → applyTelA pre TF = some (.pi D uD C vC) → applyTelA pre
        TF' = some (.pi D' uD' C' vC') → SymmMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D D')
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
        True)
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
        SymmMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
    (ihXFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
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
        SymmMotEqAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁') :
    SymmMotEqAg E I n ρ₀ k LE LT Γ A B := by
  have hpl : ps.length = ps'.length := by rw [hps, hps']
  have hplρ : ∀ ρ : WkSpecA, (ps.map (wkExprA ρ)).length = (ps'.map (wkExprA ρ)).length := fun ρ => by
    simp [hpl]
  have hplρ' : ∀ ρ : WkSpecA, (ps'.map (wkExprA ρ)).length = (ps.map (wkExprA ρ)).length := fun ρ =>
    (hplρ ρ).symm
  have hpsρ : ∀ ρ : WkSpecA, (ps.map (wkExprA ρ)).length = m.nparamsA := fun ρ => by simp [hps]
  have hps'ρ : ∀ ρ : WkSpecA, (ps'.map (wkExprA ρ)).length = m.nparamsA := fun ρ => by simp [hps']
  have hPer : FiberPerWA E I n Γ r m Rs RsF RsI ps ls := fun ρ hρ =>
    famFiberPerAg hEN HS HT hsh (by rw [List.length_map]; exact hps) (hFld ρ hρ) (hFldF ρ hρ) (hFldeq ρ hρ)
      (hFldRec ρ hρ) (hFldFeq ρ hρ) (hFldI ρ hρ) (hFldIeq ρ hρ) (hFldIRec ρ hρ) (hFldIdom ρ hρ)
  -- the cross data from the left data to the CARRIED left data
  have hXρ : CrossWA E I n Γ r m Rs (famCarryRsA m ps Rs) RsF (famCarryRsFA m ps RsF) RsI
      (famCarryRsIA m ps RsI) ps ps' ls ls' := by
    intro ρ hρ
    refine ⟨fun _ _ _ pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => (carryRelA_app (hps'ρ ρ) _ pre).symm,
     fun _ _ _ _ _ _ _ _ _ _ pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
       (carryRelA_app (hps'ρ ρ) _ pre).symm,
     hXRec ρ hρ, ?_,
     fun c cm lsA lsC lsC' kinds T T₁ T' T₁' pre pre' R R₁ R' R₁' hcm hk hfam hkinds hlA hlAC hlCC hT hT₁ hT'
        hT₁' hw hR hR₁ hR' hR₁' =>
      ⟨hXRes ρ hρ c cm lsA lsC kinds T T₁ pre pre' R R₁ hcm hk hfam hkinds hlA hlAC hT hT₁ hw hR hR₁,
       hXResR ρ hρ c cm lsA lsC lsC' kinds T T' T₁' pre pre' R' R₁' hcm hk hfam hkinds hlA hlAC hlCC hT hT' hT₁'
         hw hR' hR₁'⟩,
     hpar ρ hρ, hXFldIdom ρ hρ⟩
    -- (I): the carried inner relations at the right parameters are the left ones at the left
    -- parameters (`innerRelsA_carry`); the inner telescopes are rigid of one Π-count
    intro c cm lsA lsA' lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds hsp
      hlA hlAC _ _ hT hT' hw hw' hD hD' ρ' hρ'
    have hrD := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hpsρ ρ) (argsRelA_length hw).1 hT hD
    have hrD' := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hps'ρ ρ) (argsRelA_length hw').1 hT' hD'
    have hwD := rigid_wkExprA ρ' D hrD.1
    have hwD' := rigid_wkExprA ρ' D' hrD'.1
    exact innerCrossA_of_one hwD.1 hwD'.1 (by rw [hwD.2, hwD'.2, hrD.2, hrD'.2])
      (fun q _ _ _ _ _ _ _ _ _ _ _ _ _ => Eq.symm (congrFun (congrFun
        (innerRelsA_carry (ps := ps) RsI hps' ρ c lsC (m.nparamsA + ksPre.length) pre ρ') q.length) q))
      (fun zs zs' C₁ C₁' hzs hl hC hC' =>
        hXRecI ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds hsp
          hlA hlAC hT hT' hw hD hD' ρ' hρ' zs zs' C₁ C₁' hzs hl hC hC')
  -- the carried data are valid, and their equalities hold, at every world
  have hFldB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T' : ExprA) (pre pre' : List ExprA)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
      eqNList ls' lsA → eqNListB n lsA lsC →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T' ksPre pre pre' →
      applyTelA pre T' = some (.pi D' uD' C' vC') →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D'
        (famCarryRsA m ps Rs ρ c lsC (m.nparamsA + ksPre.length) (ps'.map (wkExprA ρ) ++ pre)) := by
    intro ρ hρ c cm lsA lsC kinds ksPre ks T' pre pre' D' uD' C' vC' hcm hk hfam hkinds hsp hlA hlAC hT' hwB hD'
    have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    obtain ⟨T, hT⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ' ρ) hT'
    obtain ⟨D, uD, C, vC, hD⟩ := applyTelA_pi_cross hrig (hplρ' ρ) hT' hT rfl hD'
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT hT' hsp hwB
    have hDD' := hXFld ρ hρ c cm lsA lsC kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds
      hsp hlA₀ hlAC hT hT' hwA hD hD'
    have tD := hFld ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA₀ hlAC hT hwA
      hD
    obtain ⟨R', tD'⟩ := (ihXFld ρ hρ c cm lsA lsC kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' hcm hk
      hfam hkinds hsp hlA₀ hlAC hT hT' hwA hD hD').2 _ tD
    have e := eqKA_transportg hEN HS HT hDD' tD tD'
    show TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D'
      (carryRelA m (ps.map (wkExprA ρ)) (Rs ρ c lsC) _ (ps'.map (wkExprA ρ) ++ pre))
    rw [carryRelA_app (hps'ρ ρ), e]
    exact tD'
  have hFldFB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF' : ExprA)
      (pre pre' : List ExprA) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      eqNListB n ls' lsF →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF' →
      ArgsRelPA (famCarryRsFA m ps RsF ρ lsF) m.nparamsA (ps'.map (wkExprA ρ)) TF' pre pre' →
      applyTelA pre TF' = some (.pi D' uD' C' vC') →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D'
        (famCarryRsFA m ps RsF ρ lsF (m.nparamsA + pre.length) (ps'.map (wkExprA ρ) ++ pre)) := by
    intro ρ hρ lsF TF' pre pre' D' uD' C' vC' hl hTF' hwB hD'
    have hl₀ : eqNListB n ls lsF := ⟨eqNListA_trans hls hl.1, hl.2⟩
    obtain ⟨TF, hTF⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) lsF lsF (hplρ' ρ) hTF'
    obtain ⟨D, uD, C, vC, hD⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) (hplρ' ρ) hTF' hTF rfl hD'
    have hwA := argsRelPA_famCross_bwd hsh (hXρ ρ hρ) (hplρ ρ) hl₀ hTF hTF' hwB
    have hDD' := hXFeq ρ hρ lsF TF TF' pre pre' D uD C vC D' uD' C' vC' hl₀ hTF hTF' hwA hD hD'
    have tD := hFldF ρ hρ lsF TF pre pre' D uD C vC hl₀ hTF hwA hD
    obtain ⟨R', tD'⟩ := (ihXFeq ρ hρ lsF TF TF' pre pre' D uD C vC D' uD' C' vC' hl₀ hTF hTF' hwA hD hD').2 _ tD
    have e := eqKA_transportg hEN HS HT hDD' tD tD'
    show TyKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D'
      (carryRelA m (ps.map (wkExprA ρ)) (RsF ρ lsF) _ (ps'.map (wkExprA ρ) ++ pre))
    rw [carryRelA_app (hps'ρ ρ), e]
    exact tD'
  have hFldeqB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T'₁ T'₂ : ExprA) (pre pre' : List ExprA)
      (D'₁ : ExprA) (uD'₁ : Level) (C'₁ : ExprA) (vC'₁ : Level) (D'₂ : ExprA) (uD'₂ : Level) (C'₂ : ExprA)
      (vC'₂ : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
      eqNList ls' lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T'₁ →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T'₂ →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T'₁ ksPre pre pre' →
      applyTelA pre T'₁ = some (.pi D'₁ uD'₁ C'₁ vC'₁) → applyTelA pre' T'₂ = some (.pi D'₂ uD'₂ C'₂ vC'₂) →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D'₁ D'₂ := by
    intro ρ hρ c cm lsA lsC lsC' kinds ksPre ks T'₁ T'₂ pre pre' D'₁ uD'₁ C'₁ vC'₁ D'₂ uD'₂ C'₂ vC'₂ hcm hk hfam
      hkinds hsp hlA hlAC hlsC hT'₁ hT'₂ hwB hD'₁ hD'₂
    have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    obtain ⟨T₁, hT₁⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ' ρ) hT'₁
    obtain ⟨T₂, hT₂⟩ := applyTelA_some_transfer_levels hrig lsC' lsC' (hplρ' ρ) hT'₂
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT₁ hT'₁ hsp hwB
    have hwA' := ctorWalkA_flip hEN hPer hps hρ hcm hk hfam hkinds hlA₀ hlAC hlsC hT₁ hT₂ hsp
      hwA
    obtain ⟨D₁, uD₁, C₁, vC₁, hD₁⟩ := applyTelA_pi_cross hrig (hplρ' ρ) hT'₁ hT₁ rfl hD'₁
    obtain ⟨D₂, uD₂, C₂, vC₂, hD₂⟩ := applyTelA_pi_cross hrig (hplρ' ρ) hT'₂ hT₂ rfl hD'₂
    have e1 := (ihXFld ρ hρ c cm lsA lsC kinds ksPre ks T₁ T'₁ pre pre' D₁ uD₁ C₁ vC₁ D'₁ uD'₁ C'₁ vC'₁ hcm hk
      hfam hkinds hsp hlA₀ hlAC hT₁ hT'₁ hwA hD₁ hD'₁).1
    have e2 := hFldeq ρ hρ c cm lsA lsC lsC' kinds ksPre ks T₁ T₂ pre pre' D₁ uD₁ C₁ vC₁ D₂ uD₂ C₂ vC₂ hcm hk hfam
      hkinds hsp hlA₀ hlAC hlsC hT₁ hT₂ hwA hD₁ hD₂
    have e3 := hXFld ρ hρ c cm lsA lsC' kinds ksPre ks T₂ T'₂ pre' pre D₂ uD₂ C₂ vC₂ D'₂ uD'₂ C'₂ vC'₂ hcm hk hfam
      hkinds hsp hlA₀ (eqNListB_trans hlAC hlsC) hT₂ hT'₂ hwA' hD₂ hD'₂
    exact eqKA_transg hEN HS HT (eqKA_transg hEN HS HT e1 e2) e3
  have hFldRecB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T'₁ T'₂ : ExprA) (pre pre' : List ExprA)
      (D'₁ : ExprA) (uD'₁ : Level) (C'₁ : ExprA) (vC'₁ : Level) (D'₂ : ExprA) (uD'₂ : Level) (C'₂ : ExprA)
      (vC'₂ : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
      eqNList ls' lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T'₁ →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T'₂ →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T'₁ ksPre pre pre' →
      applyTelA pre T'₁ = some (.pi D'₁ uD'₁ C'₁ vC'₁) → applyTelA pre' T'₂ = some (.pi D'₂ uD'₂ C'₂ vC'₂) →
      RecDomRelA E I n (wkCtxA ρ Γ) r m (famCarryRsFA m ps RsF ρ) ls' (ps'.map (wkExprA ρ)) D'₁ D'₂ := by
    intro ρ hρ c cm lsA lsC lsC' kinds ksPre ks T'₁ T'₂ pre pre' D'₁ uD'₁ C'₁ vC'₁ D'₂ uD'₂ C'₂ vC'₂ hcm hk hfam
      hkinds hsp hlA hlAC hlsC hT'₁ hT'₂ hwB hD'₁ hD'₂
    have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    obtain ⟨T₁, hT₁⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ' ρ) hT'₁
    obtain ⟨T₂, hT₂⟩ := applyTelA_some_transfer_levels hrig lsC' lsC' (hplρ' ρ) hT'₂
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT₁ hT'₁ hsp hwB
    have hwA' := ctorWalkA_flip hEN hPer hps hρ hcm hk hfam hkinds hlA₀ hlAC hlsC hT₁ hT₂ hsp
      hwA
    obtain ⟨D₁, uD₁, C₁, vC₁, hD₁⟩ := applyTelA_pi_cross hrig (hplρ' ρ) hT'₁ hT₁ rfl hD'₁
    obtain ⟨D₂, uD₂, C₂, vC₂, hD₂⟩ := applyTelA_pi_cross hrig (hplρ' ρ) hT'₂ hT₂ rfl hD'₂
    have r1 := hXRec ρ hρ c cm lsA lsC kinds ksPre ks T₁ T'₁ pre pre' D₁ uD₁ C₁ vC₁ D'₁ uD'₁ C'₁ vC'₁ hcm hk hfam
      hkinds hsp hlA₀ hlAC hT₁ hT'₁ hwA hD₁ hD'₁
    have r2 := hFldRec ρ hρ c cm lsA lsC lsC' kinds ksPre ks T₁ T₂ pre pre' D₁ uD₁ C₁ vC₁ D₂ uD₂ C₂ vC₂ hcm hk hfam
      hkinds hsp hlA₀ hlAC hlsC hT₁ hT₂ hwA hD₁ hD₂
    have r3 := hXRec ρ hρ c cm lsA lsC' kinds ksPre ks T₂ T'₂ pre' pre D₂ uD₂ C₂ vC₂ D'₂ uD'₂ C'₂ vC'₂ hcm hk hfam
      hkinds hsp hlA₀ (eqNListB_trans hlAC hlsC) hT₂ hT'₂ hwA' hD₂ hD'₂
    exact recDomRelXA_lvl (eqNListA_symm hls) (recDomRelXA_chain hsh (hPer ρ hρ).1 (hps'ρ ρ) (hplρ ρ) r1 r2 r3)
  have hFldFeqB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF'₁ TF'₂ : ExprA)
      (pre pre' : List ExprA) (D'₁ : ExprA) (uD'₁ : Level) (C'₁ : ExprA) (vC'₁ : Level)
      (D'₂ : ExprA) (uD'₂ : Level) (C'₂ : ExprA) (vC'₂ : Level), eqNListB n ls' lsF → eqNListB n lsF lsF' →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF'₁ →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF'₂ →
      ArgsRelPA (famCarryRsFA m ps RsF ρ lsF) m.nparamsA (ps'.map (wkExprA ρ)) TF'₁ pre pre' →
      applyTelA pre TF'₁ = some (.pi D'₁ uD'₁ C'₁ vC'₁) → applyTelA pre' TF'₂ = some (.pi D'₂ uD'₂ C'₂ vC'₂) →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D'₁ D'₂ := by
    intro ρ hρ lsF lsF' TF'₁ TF'₂ pre pre' D'₁ uD'₁ C'₁ vC'₁ D'₂ uD'₂ C'₂ vC'₂ hl hll hTF'₁ hTF'₂ hwB hD'₁ hD'₂
    have hl₀ : eqNListB n ls lsF := ⟨eqNListA_trans hls hl.1, hl.2⟩
    obtain ⟨TF₁, hTF₁⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) lsF lsF (hplρ' ρ) hTF'₁
    obtain ⟨TF₂, hTF₂⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) lsF' lsF' (hplρ' ρ) hTF'₂
    have hwA := argsRelPA_famCross_bwd hsh (hXρ ρ hρ) (hplρ ρ) hl₀ hTF₁ hTF'₁ hwB
    have hwA' := (hPer ρ hρ).1.flip hl₀ hll hTF₁ hTF₂ hwA
    obtain ⟨D₁, uD₁, C₁, vC₁, hD₁⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) (hplρ' ρ) hTF'₁ hTF₁ rfl hD'₁
    obtain ⟨D₂, uD₂, C₂, vC₂, hD₂⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) (hplρ' ρ) hTF'₂ hTF₂ rfl hD'₂
    have e1 := (ihXFeq ρ hρ lsF TF₁ TF'₁ pre pre' D₁ uD₁ C₁ vC₁ D'₁ uD'₁ C'₁ vC'₁ hl₀ hTF₁ hTF'₁ hwA hD₁ hD'₁).1
    have e2 := hFldFeq ρ hρ lsF lsF' TF₁ TF₂ pre pre' D₁ uD₁ C₁ vC₁ D₂ uD₂ C₂ vC₂ hl₀ hll hTF₁ hTF₂ hwA hD₁ hD₂
    have e3 := hXFeq ρ hρ lsF' TF₂ TF'₂ pre' pre D₂ uD₂ C₂ vC₂ D'₂ uD'₂ C'₂ vC'₂ (eqNListB_trans hl₀ hll) hTF₂ hTF'₂
      hwA' hD₂ hD'₂
    exact eqKA_transg hEN HS HT (eqKA_transg hEN HS HT e1 e2) e3
  -- the reversed cross data
  have hXFldB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T' T : ExprA)
      (pre pre' : List ExprA) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level)
      (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
      eqNList ls' lsA → eqNListB n lsA lsC →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T' ksPre pre pre' →
      applyTelA pre T' = some (.pi D' uD' C' vC') → applyTelA pre T = some (.pi D uD C vC) →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D' D := by
    intro ρ hρ c cm lsA lsC kinds ksPre ks T' T pre pre' D' uD' C' vC' D uD C vC hcm hk hfam hkinds hsp hlA hlAC
      hT' hT hwB hD' hD
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT hT' hsp hwB
    exact (ihXFld ρ hρ c cm lsA lsC kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds hsp
      hlA₀ hlAC hT hT' hwA hD hD').1
  have hXRecB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T' T : ExprA)
      (pre pre' : List ExprA) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level)
      (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
      eqNList ls' lsA → eqNListB n lsA lsC →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T' ksPre pre pre' →
      applyTelA pre T' = some (.pi D' uD' C' vC') → applyTelA pre T = some (.pi D uD C vC) →
      RecDomRelXA E I n (wkCtxA ρ Γ) r m (famCarryRsFA m ps RsF ρ) ls' (ps'.map (wkExprA ρ))
        (ps.map (wkExprA ρ)) D' D := by
    intro ρ hρ c cm lsA lsC kinds ksPre ks T' T pre pre' D' uD' C' vC' D uD C vC hcm hk hfam hkinds hsp hlA hlAC
      hT' hT hwB hD' hD
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT hT' hsp hwB
    exact recDomRelXA_lvl (eqNListA_symm hls) (recDomRelXA_rev hsh (hPer ρ hρ).1 (hps'ρ ρ) (hplρ ρ)
      (hXRec ρ hρ c cm lsA lsC kinds ksPre ks T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds hsp hlA₀
        hlAC hT hT' hwA hD hD'))
  have hXResB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds : List FieldShape) (T' T : ExprA) (pre pre' : List ExprA) (R' R : ExprA),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      eqNList ls' lsA → eqNListB n lsA lsC →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T' kinds pre pre' →
      applyTelA pre T' = some R' → applyTelA pre T = some R →
      RecDomRelXA E I n (wkCtxA ρ Γ) r m (famCarryRsFA m ps RsF ρ) ls' (ps'.map (wkExprA ρ))
        (ps.map (wkExprA ρ)) R' R := by
    intro ρ hρ c cm lsA lsC kinds T' T pre pre' R' R hcm hk hfam hkinds hlA hlAC hT' hT hwB hR' hR
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT hT' (List.append_nil kinds).symm hwB
    exact recDomRelXA_lvl (eqNListA_symm hls) (recDomRelXA_rev hsh (hPer ρ hρ).1 (hps'ρ ρ) (hplρ ρ)
      (hXRes ρ hρ c cm lsA lsC kinds T T' pre pre' R R' hcm hk hfam hkinds hlA₀ hlAC hT hT' hwA hR hR'))
  have hXResRB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds : List FieldShape) (T' T'' Tq : ExprA) (pre pre' : List ExprA)
      (R'' Rq : ExprA),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      eqNList ls' lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T'' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some Tq →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T' kinds pre pre' →
      applyTelA pre' T'' = some R'' → applyTelA pre' Tq = some Rq →
      RecDomRelXA E I n (wkCtxA ρ Γ) r m (famCarryRsFA m ps RsF ρ) ls' (ps'.map (wkExprA ρ))
        (ps.map (wkExprA ρ)) R'' Rq := by
    intro ρ hρ c cm lsA lsC lsC' kinds T' T'' Tq pre pre' R'' Rq hcm hk hfam hkinds hlA hlAC hlCC hT' hT''
      hTq hwB hR'' hRq
    have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    obtain ⟨T, hT⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ' ρ) hT'
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT hT' (List.append_nil kinds).symm hwB
    exact recDomRelXA_lvl (eqNListA_symm hls) (recDomRelXA_rev hsh (hPer ρ hρ).1 (hps'ρ ρ) (hplρ ρ)
      (hXResR ρ hρ c cm lsA lsC lsC' kinds T Tq T'' pre pre' Rq R'' hcm hk hfam hkinds hlA₀ hlAC hlCC hT hTq
        hT'' hwA hRq hR''))
  have hXFeqB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF' TF : ExprA)
      (pre pre' : List ExprA) (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level)
      (D : ExprA) (uD : Level) (C : ExprA) (vC : Level), eqNListB n ls' lsF →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF →
      ArgsRelPA (famCarryRsFA m ps RsF ρ lsF) m.nparamsA (ps'.map (wkExprA ρ)) TF' pre pre' →
      applyTelA pre TF' = some (.pi D' uD' C' vC') → applyTelA pre TF = some (.pi D uD C vC) →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ Γ) D' D := by
    intro ρ hρ lsF TF' TF pre pre' D' uD' C' vC' D uD C vC hl hTF' hTF hwB hD' hD
    have hl₀ : eqNListB n ls lsF := ⟨eqNListA_trans hls hl.1, hl.2⟩
    have hwA := argsRelPA_famCross_bwd hsh (hXρ ρ hρ) (hplρ ρ) hl₀ hTF hTF' hwB
    exact (ihXFeq ρ hρ lsF TF TF' pre pre' D uD C vC D' uD' C' vC' hl₀ hTF hTF' hwA hD hD').1
  -- the carried inner data at a function-recursive field (R-NoFunRec-1 step 1 (1b)): the walks cross back
  -- to the left fiber (the outer by `argsRelA_famCross_bwd`, the inner by the cross data's (I)), where the
  -- left data and the cross data's induction hypotheses apply
  have hFldIB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
      eqNList ls' lsA → eqNListB n lsA lsC →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
        (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
      ArgsRelPA (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC (m.nparamsA + ksPre.length) (ps'.map (wkExprA ρ) ++ pre) ρ') 0 []
        (wkExprA ρ' D) zs zs' →
      applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
      TyKAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁
        (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC (m.nparamsA + ksPre.length) (ps'.map (wkExprA ρ) ++ pre) ρ' zs.length zs) := by
    intro ρ hρ c cm lsA lsC kinds ksPre ks j T' pre pre' D' uD' C' vC' hcm hk hfam hkinds hsp hlA hlAC hT' hwB hD'
      ρ' hρ' zs zs' X₁ ux₁ Y₁ vx₁ hzsB hX₁
    have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    obtain ⟨T, hT⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ' ρ) hT'
    obtain ⟨D, uD, C, vC, hD⟩ := applyTelA_pi_cross hrig (hplρ' ρ) hT' hT rfl hD'
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT hT' hsp hwB
    have hzsA := ((hXρ ρ hρ).2.2.2.1 c cm lsA lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk
      hfam hkinds hsp hlA₀ hlAC hlA hlAC hT hT' hwA hwB hD hD' ρ' hρ').1 zs zs' hzsB
    have hrD := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hpsρ ρ) (argsRelA_length hwA).1 hT hD
    have hrD' := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hps'ρ ρ) (argsRelA_length hwB).1 hT' hD'
    have hwD := rigid_wkExprA ρ' D hrD.1
    have hwD' := rigid_wkExprA ρ' D' hrD'.1
    obtain ⟨X₀, ux₀, Y₀, vx₀, hX₀⟩ := applyTelA_pi_transfer hwD'.1 hwD.1 (by rw [hwD.2, hwD'.2, hrD.2, hrD'.2])
      rfl hX₁
    have tX := hFldI ρ hρ c cm lsA lsC kinds ksPre ks j T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA₀ hlAC hT hwA
      hD ρ' hρ' zs zs' X₀ ux₀ Y₀ vx₀ hzsA hX₀
    obtain ⟨R', tX'⟩ := (ihXFldI ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam
      hkinds hsp hlA₀ hlAC hT hT' hwA hD hD' ρ' hρ' zs zs' X₀ ux₀ Y₀ vx₀ X₁ ux₁ Y₁ vx₁ hzsA hX₀ hX₁).2 _ tX
    have e := eqKA_transportg hEN HS HT (hXFldI ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC'
      hcm hk hfam hkinds hsp hlA₀ hlAC hT hT' hwA hD hD' ρ' hρ' zs zs' X₀ ux₀ Y₀ vx₀ X₁ ux₁ Y₁ vx₁ hzsA hX₀ hX₁) tX tX'
    rw [innerRelsA_carry RsI hps' ρ c lsC _ pre ρ', e]
    exact tX'
  have hFldIeqB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
      eqNList ls' lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      applyTelA pre' T' = some (.pi D' uD' C' vC') →
      ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
        (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
      ArgsRelPA (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC (m.nparamsA + ksPre.length) (ps'.map (wkExprA ρ) ++ pre) ρ') 0 []
        (wkExprA ρ' D) zs zs' →
      applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
      applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁' := by
    intro ρ hρ c cm lsA lsC lsC' kinds ksPre ks j T'₁ T'₂ pre pre' D'₁ uD'₁ C'₁ vC'₁ D'₂ uD'₂ C'₂ vC'₂ hcm hk hfam
      hkinds hsp hlA hlAC hlsC hT'₁ hT'₂ hwB hD'₁ hD'₂ ρ' hρ' zs zs' X₁ ux₁ Y₁ vx₁ X₂ ux₂ Y₂ vx₂ hzsB hX₁ hX₂
    have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    obtain ⟨T₁, hT₁⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ' ρ) hT'₁
    obtain ⟨T₂, hT₂⟩ := applyTelA_some_transfer_levels hrig lsC' lsC' (hplρ' ρ) hT'₂
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT₁ hT'₁ hsp hwB
    have hwA' := ctorWalkA_flip hEN hPer hps hρ hcm hk hfam hkinds hlA₀ hlAC hlsC hT₁ hT₂ hsp hwA
    obtain ⟨D₁, uD₁, C₁, vC₁, hD₁⟩ := applyTelA_pi_cross hrig (hplρ' ρ) hT'₁ hT₁ rfl hD'₁
    obtain ⟨D₂, uD₂, C₂, vC₂, hD₂⟩ := applyTelA_pi_cross hrig (hplρ' ρ) hT'₂ hT₂ rfl hD'₂
    have hzsA := ((hXρ ρ hρ).2.2.2.1 c cm lsA lsA lsC kinds ksPre ks j T₁ T'₁ pre pre' D₁ uD₁ C₁ vC₁ D'₁ uD'₁ C'₁
      vC'₁ hcm hk hfam hkinds hsp hlA₀ hlAC hlA hlAC hT₁ hT'₁ hwA hwB hD₁ hD'₁ ρ' hρ').1 zs zs' hzsB
    obtain ⟨D₂x, uD₂x, C₂x, vC₂x, hD₂x, -, -, hfun, -⟩ := (hPer ρ hρ).2 c cm kinds lsA lsC lsC' T₁ T₂ hcm hk hfam
      hkinds hlA₀ hlAC hlsC hT₁ hT₂ _ ksPre ks pre pre' pre D₁ uD₁ C₁ vC₁ hsp hwA hwA' hD₁
    rw [hD₂] at hD₂x
    cases hD₂x
    have hzs2 := (hfun j rfl ρ' hρ').2.1 zs zs' hzsA
    have hr1 := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hpsρ ρ) (argsRelA_length hwA).1 hT₁ hD₁
    have hr1' := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hps'ρ ρ) (argsRelA_length hwB).1 hT'₁ hD'₁
    have hr2 := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hpsρ ρ) (argsRelA_length hwA).2 hT₂ hD₂
    have hr2' := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hps'ρ ρ) (argsRelA_length hwB).2 hT'₂ hD'₂
    have hw1 := rigid_wkExprA ρ' D₁ hr1.1
    have hw1' := rigid_wkExprA ρ' D'₁ hr1'.1
    have hw2 := rigid_wkExprA ρ' D₂ hr2.1
    have hw2' := rigid_wkExprA ρ' D'₂ hr2'.1
    obtain ⟨Z₁, uz₁, W₁, vz₁, hZ₁⟩ := applyTelA_pi_transfer hw1'.1 hw1.1 (by rw [hw1.2, hw1'.2, hr1.2, hr1'.2])
      rfl hX₁
    obtain ⟨Z₂, uz₂, W₂, vz₂, hZ₂⟩ := applyTelA_pi_transfer hw2'.1 hw2.1 (by rw [hw2.2, hw2'.2, hr2.2, hr2'.2])
      rfl hX₂
    have e1 := (ihXFldI ρ hρ c cm lsA lsC kinds ksPre ks j T₁ T'₁ pre pre' D₁ uD₁ C₁ vC₁ D'₁ uD'₁ C'₁ vC'₁ hcm hk
      hfam hkinds hsp hlA₀ hlAC hT₁ hT'₁ hwA hD₁ hD'₁ ρ' hρ' zs zs' Z₁ uz₁ W₁ vz₁ X₁ ux₁ Y₁ vx₁ hzsA hZ₁ hX₁).1
    have e2 := hFldIeq ρ hρ c cm lsA lsC lsC' kinds ksPre ks j T₁ T₂ pre pre' D₁ uD₁ C₁ vC₁ D₂ uD₂ C₂ vC₂ hcm hk
      hfam hkinds hsp hlA₀ hlAC hlsC hT₁ hT₂ hwA hD₁ hD₂ ρ' hρ' zs zs' Z₁ uz₁ W₁ vz₁ Z₂ uz₂ W₂ vz₂ hzsA hZ₁ hZ₂
    have e3 := hXFldI ρ hρ c cm lsA lsC' kinds ksPre ks j T₂ T'₂ pre' pre D₂ uD₂ C₂ vC₂ D'₂ uD'₂ C'₂ vC'₂ hcm hk
      hfam hkinds hsp hlA₀ (eqNListB_trans hlAC hlsC) hT₂ hT'₂ hwA' hD₂ hD'₂ ρ' hρ' zs' zs' Z₂ uz₂ W₂ vz₂ X₂ ux₂
      Y₂ vx₂ hzs2 hZ₂ hX₂
    exact eqKA_transg hEN HS HT (eqKA_transg hEN HS HT e1 e2) e3
  have hFldIRecB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
      eqNList ls' lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      applyTelA pre' T' = some (.pi D' uD' C' vC') →
      ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
      ArgsRelPA (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC (m.nparamsA + ksPre.length) (ps'.map (wkExprA ρ) ++ pre) ρ') 0 []
        (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
      applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
      RecDomRelA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (famCarryRsFA m ps RsF (WkSpecA.comp ρ ρ')) ls'
        ((ps'.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁' := by
    intro ρ hρ c cm lsA lsC lsC' kinds ksPre ks j T'₁ T'₂ pre pre' D'₁ uD'₁ C'₁ vC'₁ D'₂ uD'₂ C'₂ vC'₂ hcm hk hfam
      hkinds hsp hlA hlAC hlsC hT'₁ hT'₂ hwB hD'₁ hD'₂ ρ' hρ' zs zs' Q₁ Q₂ hzsB hlen hQ₁ hQ₂
    have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    obtain ⟨T₁, hT₁⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ' ρ) hT'₁
    obtain ⟨T₂, hT₂⟩ := applyTelA_some_transfer_levels hrig lsC' lsC' (hplρ' ρ) hT'₂
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT₁ hT'₁ hsp hwB
    have hwA' := ctorWalkA_flip hEN hPer hps hρ hcm hk hfam hkinds hlA₀ hlAC hlsC hT₁ hT₂ hsp hwA
    obtain ⟨D₁, uD₁, C₁, vC₁, hD₁⟩ := applyTelA_pi_cross hrig (hplρ' ρ) hT'₁ hT₁ rfl hD'₁
    obtain ⟨D₂, uD₂, C₂, vC₂, hD₂⟩ := applyTelA_pi_cross hrig (hplρ' ρ) hT'₂ hT₂ rfl hD'₂
    have hzsA := ((hXρ ρ hρ).2.2.2.1 c cm lsA lsA lsC kinds ksPre ks j T₁ T'₁ pre pre' D₁ uD₁ C₁ vC₁ D'₁ uD'₁ C'₁
      vC'₁ hcm hk hfam hkinds hsp hlA₀ hlAC hlA hlAC hT₁ hT'₁ hwA hwB hD₁ hD'₁ ρ' hρ').1 zs zs' hzsB
    obtain ⟨D₂x, uD₂x, C₂x, vC₂x, hD₂x, -, -, hfun, -⟩ := (hPer ρ hρ).2 c cm kinds lsA lsC lsC' T₁ T₂ hcm hk hfam
      hkinds hlA₀ hlAC hlsC hT₁ hT₂ _ ksPre ks pre pre' pre D₁ uD₁ C₁ vC₁ hsp hwA hwA' hD₁
    rw [hD₂] at hD₂x
    cases hD₂x
    have hzs2 := (hfun j rfl ρ' hρ').2.1 zs zs' hzsA
    have hr1 := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hpsρ ρ) (argsRelA_length hwA).1 hT₁ hD₁
    have hr1' := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hps'ρ ρ) (argsRelA_length hwB).1 hT'₁ hD'₁
    have hr2 := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hpsρ ρ) (argsRelA_length hwA).2 hT₂ hD₂
    have hr2' := rigTel_of_shape hEN hcm hk hfam hkinds hsp (hps'ρ ρ) (argsRelA_length hwB).2 hT'₂ hD'₂
    have hw1 := rigid_wkExprA ρ' D₁ hr1.1
    have hw1' := rigid_wkExprA ρ' D'₁ hr1'.1
    have hw2 := rigid_wkExprA ρ' D₂ hr2.1
    have hw2' := rigid_wkExprA ρ' D'₂ hr2'.1
    obtain ⟨P₁, hP₁⟩ := applyTelA_some_of_cnt hw1'.1 hw1.1 (by rw [hw1.2, hw1'.2, hr1.2, hr1'.2]) hQ₁
    obtain ⟨P₂, hP₂⟩ := applyTelA_some_of_cnt hw2'.1 hw2.1 (by rw [hw2.2, hw2'.2, hr2.2, hr2'.2]) hQ₂
    have hlen' : zs'.length = j + 1 := (argsRelPA_length hzsA).symm.trans hlen
    have hρc := wkOk₀A_comp_ext hρ hρ'
    exact recDomRelXA_of_comp_world (recDomRelXA_lvl (eqNListA_symm hls) (recDomRelXA_chain hsh (hPer _ hρc).1
      (hps'ρ _) (hplρ _)
      (recDomRelXA_comp_world (hXRecI ρ hρ c cm lsA lsC kinds ksPre ks j T₁ T'₁ pre pre' D₁ uD₁ C₁ vC₁ D'₁ uD'₁ C'₁
        vC'₁ hcm hk hfam hkinds hsp hlA₀ hlAC hT₁ hT'₁ hwA hD₁ hD'₁ ρ' hρ' zs zs' P₁ Q₁ hzsA hlen hP₁ hQ₁))
      (recDomRelXA_comp_world (hFldIRec ρ hρ c cm lsA lsC lsC' kinds ksPre ks j T₁ T₂ pre pre' D₁ uD₁ C₁ vC₁ D₂ uD₂
        C₂ vC₂ hcm hk hfam hkinds hsp hlA₀ hlAC hlsC hT₁ hT₂ hwA hD₁ hD₂ ρ' hρ' zs zs' P₁ P₂ hzsA hlen hP₁ hP₂))
      (recDomRelXA_comp_world (hXRecI ρ hρ c cm lsA lsC' kinds ksPre ks j T₂ T'₂ pre' pre D₂ uD₂ C₂ vC₂ D'₂ uD'₂ C'₂
        vC'₂ hcm hk hfam hkinds hsp hlA₀ (eqNListB_trans hlAC hlsC) hT₂ hT'₂ hwA' hD₂ hD'₂ ρ' hρ' zs' zs' P₂ Q₂ hzs2
        hlen' hP₂ hQ₂))))
  have hXFldIB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
      eqNList ls' lsA → eqNListB n lsA lsC →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
      ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
        (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
      ArgsRelPA (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC (m.nparamsA + ksPre.length) (ps'.map (wkExprA ρ) ++ pre) ρ') 0 []
        (wkExprA ρ' D) zs zs' →
      applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
      applyTelA zs (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
      EqKAg E I n ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁' := by
    intro ρ hρ c cm lsA lsC kinds ksPre ks j T' T pre pre' D' uD' C' vC' D uD C vC hcm hk hfam hkinds hsp hlA hlAC
      hT' hT hwB hD' hD ρ' hρ' zs zs' X₁ ux₁ Y₁ vx₁ X₀ ux₀ Y₀ vx₀ hzsB hX₁ hX₀
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT hT' hsp hwB
    have hzsA := ((hXρ ρ hρ).2.2.2.1 c cm lsA lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk
      hfam hkinds hsp hlA₀ hlAC hlA hlAC hT hT' hwA hwB hD hD' ρ' hρ').1 zs zs' hzsB
    exact (ihXFldI ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds hsp
      hlA₀ hlAC hT hT' hwA hD hD' ρ' hρ' zs zs' X₀ ux₀ Y₀ vx₀ X₁ ux₁ Y₁ vx₁ hzsA hX₀ hX₁).1
  have hFldIdomB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
      eqNList ls' lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      applyTelA pre' T' = some (.pi D' uD' C' vC') →
      Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D') := by
    intro ρ hρ c cm lsA lsC lsC' kinds ksPre ks j T'₁ T'₂ pre pre' D'₁ uD'₁ C'₁ vC'₁ D'₂ uD'₂ C'₂ vC'₂ hcm hk hfam
      hkinds hsp hlA hlAC hlsC hT'₁ hT'₂ hwB hD'₁ hD'₂
    have hrig := rigid_of_memberFamRefA_getD hEN hcm hk hfam
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    obtain ⟨T₁, hT₁⟩ := applyTelA_some_transfer_levels hrig lsC lsC (hplρ' ρ) hT'₁
    obtain ⟨T₂, hT₂⟩ := applyTelA_some_transfer_levels hrig lsC' lsC' (hplρ' ρ) hT'₂
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT₁ hT'₁ hsp hwB
    have hwA' := ctorWalkA_flip hEN hPer hps hρ hcm hk hfam hkinds hlA₀ hlAC hlsC hT₁ hT₂ hsp hwA
    obtain ⟨D₁, uD₁, C₁, vC₁, hD₁⟩ := applyTelA_pi_cross hrig (hplρ' ρ) hT'₁ hT₁ rfl hD'₁
    obtain ⟨D₂, uD₂, C₂, vC₂, hD₂⟩ := applyTelA_pi_cross hrig (hplρ' ρ) hT'₂ hT₂ rfl hD'₂
    obtain ⟨c₁⟩ := hXFldIdom ρ hρ c cm lsA lsC kinds ksPre ks j T₁ T'₁ pre pre' D₁ uD₁ C₁ vC₁ D'₁ uD'₁ C'₁ vC'₁
      hcm hk hfam hkinds hsp hlA₀ hlAC hT₁ hT'₁ hwA hD₁ hD'₁
    obtain ⟨c₂⟩ := hFldIdom ρ hρ c cm lsA lsC lsC' kinds ksPre ks j T₁ T₂ pre pre' D₁ uD₁ C₁ vC₁ D₂ uD₂ C₂ vC₂
      hcm hk hfam hkinds hsp hlA₀ hlAC hlsC hT₁ hT₂ hwA hD₁ hD₂
    obtain ⟨c₃⟩ := hXFldIdom ρ hρ c cm lsA lsC' kinds ksPre ks j T₂ T'₂ pre' pre D₂ uD₂ C₂ vC₂ D'₂ uD'₂ C'₂ vC'₂
      hcm hk hfam hkinds hsp hlA₀ (eqNListB_trans hlAC hlsC) hT₂ hT'₂ hwA' hD₂ hD'₂
    exact ⟨.trans _ _ _ _ (.trans _ _ _ _ c₁.symm c₂) c₃⟩
  have hXFldIdomB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
      eqNList ls' lsA → eqNListB n lsA lsC →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
      Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D') := by
    intro ρ hρ c cm lsA lsC kinds ksPre ks j T' T pre pre' D' uD' C' vC' D uD C vC hcm hk hfam hkinds hsp hlA hlAC
      hT' hT hwB hD' hD
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT hT' hsp hwB
    obtain ⟨c₁⟩ := hXFldIdom ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam
      hkinds hsp hlA₀ hlAC hT hT' hwA hD hD'
    exact ⟨c₁.symm⟩
  have hXRecIB : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
      ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
      eqNList ls' lsA → eqNListB n lsA lsC →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famCarryRsA m ps Rs ρ c lsC) (famRecRelA m (ps'.map (wkExprA ρ)) lsA
          (LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI))
            ρ))
          (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC) (ps'.map (wkExprA ρ))
            lsA (fun ρ' => LfpWA (FamPhiWA E I n Γ r m (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF)
              (famCarryRsIA m ps RsI)) (WkSpecA.comp ρ ρ')))
        m.nparamsA (ps'.map (wkExprA ρ)) T ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
      ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
      ArgsRelPA (innerRelsA (famCarryRsIA m ps RsI) ρ c lsC (m.nparamsA + ksPre.length) (ps'.map (wkExprA ρ) ++ pre) ρ') 0 []
        (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
      applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs (wkExprA ρ' D') = some C₁' →
      RecDomRelXA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (famCarryRsFA m ps RsF (WkSpecA.comp ρ ρ')) ls'
        ((ps'.map (wkExprA ρ)).map (wkExprA ρ')) ((ps.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁' := by
    intro ρ hρ c cm lsA lsC kinds ksPre ks j T' T pre pre' D' uD' C' vC' D uD C vC hcm hk hfam hkinds hsp hlA hlAC
      hT' hT hwB hD' hD ρ' hρ' zs zs' Q P hzsB hlen hQ hP
    have hlA₀ : eqNList ls lsA := eqNListA_trans hls hlA
    have hwA := argsRelA_famCross_bwd hsh hEN (fun ρ hρ => (hPer ρ hρ).1) hXρ hps hps' hls hρ hcm hk hfam hkinds
      hlA₀ hlAC (eqNListA_refl lsA) hT hT' hsp hwB
    have hzsA := ((hXρ ρ hρ).2.2.2.1 c cm lsA lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC D' uD' C' vC' hcm hk
      hfam hkinds hsp hlA₀ hlAC hlA hlAC hT hT' hwA hwB hD hD' ρ' hρ').1 zs zs' hzsB
    have hρc := wkOk₀A_comp_ext hρ hρ'
    exact recDomRelXA_of_comp_world (recDomRelXA_lvl (eqNListA_symm hls) (recDomRelXA_rev hsh (hPer _ hρc).1
      (hps'ρ _) (hplρ _) (recDomRelXA_comp_world (hXRecI ρ hρ c cm lsA lsC kinds ksPre ks j T T' pre pre' D uD C vC
        D' uD' C' vC' hcm hk hfam hkinds hsp hlA₀ hlAC hT hT' hwA hD hD' ρ' hρ' zs zs' P Q hzsA hlen hP hQ))))
  -- the indices at the identity world, at plain parameters
  have w0 := wkOk₀A_nil E I n Γ
  have hI0 := (hPer [] w0).1
  simp only [map_wkExprA_nil] at hI0
  have hbA : levelsBounded n ls = true := whTyA_famApp_bounded hA
  have hbB : eqNListB n ls ls' := ⟨hls, whTyA_famApp_bounded hB⟩
  have hcarry0 : ∀ (lsF : List Level) (TFl TF' : ExprA) (xs xs' : List ExprA), eqNListB n ls lsF →
      applyTelA ps (instantiateLevelsA lsF m.mtypeA) = some TFl →
      applyTelA ps' (instantiateLevelsA lsF m.mtypeA) = some TF' →
      ArgsRelPA (RsF [] lsF) m.nparamsA ps TFl xs xs' →
      ArgsRelPA (famCarryRsFA m ps RsF [] lsF) m.nparamsA ps' TF' xs xs' := by
    intro lsF TFl TF' xs xs' _ hTFl hTF' hw
    have h := argsRelPA_cross (R := RsF [] lsF) (R' := famCarryRsFA m ps RsF [] lsF) (i₀ := m.nparamsA)
      (prev₀ := ps) (prev₀' := ps') (T₀ := TFl) (T₀' := TF')
      (fun pre _ A u B v _ _ hT => by
        obtain ⟨A', u', B', v', hT'⟩ := applyTelA_pi_cross (rigid_of_sortBody hsh) hpl hTFl hTF' rfl hT
        refine ⟨A', u', B', v', hT', fun f f' hr => ?_⟩
        show carryRelA m (ps.map (wkExprA [])) (RsF [] lsF) _ (ps' ++ pre) f f'
        rw [carryRelA_app hps', map_wkExprA_nil]
        exact hr)
      hw [] [] TF' (by simp) (by simp) rfl rfl (.nil _ _ _) (.nil _ _ _)
    simpa using h
  have hxsB : ∀ (TF' : ExprA), applyTelA ps' (instantiateLevelsA ls' m.mtypeA) = some TF' →
      ArgsRelPA (famCarryRsFA m ps RsF [] ls') m.nparamsA ps' TF' is' is := by
    intro TF' hTF'
    obtain ⟨TF, hTF⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) ls' ls hpl.symm hTF'
    obtain ⟨TFl, hTFl⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) ls ls' (xs' := ps) rfl hTF
    exact hcarry0 ls' TFl TF' is' is hbB hTFl hTF' (hI0.flip (eqNListB_refl hbA) hbB hTF hTFl (hxs TF hTF))
  have hxsDB : ∀ (TF' : ExprA), applyTelA ps' (instantiateLevelsA ls' m.mtypeA) = some TF' →
      ArgsRelPA (famCarryRsFA m ps RsF [] ls') m.nparamsA ps' TF' is' is' := by
    intro TF' hTF'
    obtain ⟨TF, hTF⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) ls' ls hpl.symm hTF'
    obtain ⟨TFl, hTFl⟩ := applyTelA_some_transfer_levels (rigid_of_sortBody hsh) ls ls' (xs' := ps) rfl hTF
    have hfl := hI0.flip (eqNListB_refl hbA) hbB hTF hTFl (hxs TF hTF)
    exact hcarry0 ls' TFl TF' is' is' hbB hTFl hTF'
      (hI0.comp hbB (eqNListB_symm hbB hbA) hTFl hTF hfl (hxs TF hTF))
  refine ⟨.fam hB hA hnB hnA hm hind hsh (eqNListA_symm hls) hps' hps (famCarryRsA m ps Rs)
    (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI) hFldB hFldFB hFldeqB hFldRecB hFldFeqB hXFldB hXRecB hXResB
    hXResRB hXFeqB hxsB (hc.elim fun c => ⟨c.symm⟩)
    (fun ρ hρ lsX hlX => parConvA_symm (hpar ρ hρ lsX ⟨eqNListA_trans hls hlX.1, hlX.2⟩)) hFldIB hFldIeqB
    hFldIRecB hXFldIB hXRecIB hFldIdomB hXFldIdomB, fun R tA => ?_⟩
  cases tA with
  | fam hA₁ hn₁ hnp₁ hm₁ _ hsh₁ hps₁ hu₁ hz₁ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hA₁ hnA hn₁
      obtain ⟨er, els, exs⟩ := foldAppsA_const_inj e
      subst er; subst els
      rw [hm] at hm₁
      injection hm₁ with em
      subst em
      obtain ⟨eps, eis⟩ := List.append_inj exs (by rw [hps, hps₁])
      subst eps; subst eis
      obtain ⟨TF, hTF, _⟩ := applyTelA_append_some hu₁
      have hlen : (ps ++ is).length = (ps' ++ is').length := by
        simp only [List.length_append, hps, hps', argsRelPA_length (hxs TF hTF)]
      obtain ⟨hu', hz'⟩ := famApp_sort_transfer hsh₁ hls hlen hu₁
      exact ⟨_, .fam hB hnB (fun h => hnp₁ ((isPropTy_famApp_congr hm hsh hls hlen).2 h)) hm hind hsh₁ hps' hu'
        (hz'.trans hz₁) (famCarryRsA m ps Rs) (famCarryRsFA m ps RsF) (famCarryRsIA m ps RsI) hFldB hFldFB hFldeqB
        hFldRecB hFldFeqB hxsDB hFldIB hFldIeqB hFldIRecB hFldIdomB⟩
  | prop hA₁ hn₁ hP₁ =>
      have e := whTyA_det hA hA₁ hnA hn₁
      subst e
      obtain ⟨TF, hTF⟩ := famApp_tel_of_isProp hm hsh hP₁ ls (xs' := ps) rfl
      have hlen : (ps ++ is).length = (ps' ++ is').length := by
        simp only [List.length_append, hps, hps', argsRelPA_length (hxs TF hTF)]
      exact ⟨_, .prop hB hnB ((isPropTy_famApp_congr hm hsh hls hlen).1 hP₁)⟩
  | sortT hA₁ _ _ =>
      have e := whTyA_det hA hA₁ hnA (hStepFnA_sort _ _ _ _)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | sortP hA₁ _ =>
      have e := whTyA_det hA hA₁ hnA (hStepFnA_sort _ _ _ _)
      exact absurd e (foldAppsA_const_ne_sort _ _ _ _)
  | pi hA₁ _ _ _ _ _ _ _ _ =>
      have e := whTyA_det hA hA₁ hnA (hStepFnA_pi _ _ _ _ _ _ _)
      exact absurd e (foldAppsA_const_ne_pi _ _ _ _ _ _ _)
  | stuck hA₁ hN₁ =>
      have e := whTyA_det hA hA₁ hnA hN₁.1
      exact (stuckA_not_fam hN₁ (by rw [← e, foldAppsA_const_head]) hm hind).elim

/-- **`EqKAg` is symmetric, and validity transports along it** (one height). -/
theorem eqKA_symm_validg (hEN : EnvNormCtorTypeA E) (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE) :
    {Γ : LCtxA} → {A B : ExprA} → EqKAg E I n ρ₀ k LE LT Γ A B →
    EqKAg E I n ρ₀ k LE LT Γ B A ∧
    (∀ R : ExprA → ExprA → Prop, TyKAg E I n ρ₀ k LE LT Γ A R → ∃ R', TyKAg E I n ρ₀ k LE LT Γ B R') :=
  fun {_Γ _A _B} h =>
  EqKAg.rec (motive_1 := fun Γ A B _ => SymmMotEqAg E I n ρ₀ k LE LT Γ A B)
    (motive_2 := fun _ _ _ _ => True)
    (fun hA hB hk hl hc => symmEqMinor_sortg hA hB hk hl hc)
    (fun hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc ihD ihDeq ihC =>
      symmEqMinor_pig hEN HS HT hA hB hu hv hDty hCty hD'ty hC'ty RD hD hDeq hC hc ihD ihDeq ihC)
    (symmEqMinor_famg hEN HS HT)
    (fun hA hB hN hN' hc hPP => symmEqMinor_stuckg hA hB hN hN' hc hPP)
    (fun _ _ _ => True.intro)
    (fun _ _ _ => True.intro)
    (fun _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro)
    (fun _ _ _ => True.intro)
    h

theorem eqKA_symmg (hEN : EnvNormCtorTypeA E) (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE)
    {Γ : LCtxA} {A B : ExprA}
    (h : EqKAg E I n ρ₀ k LE LT Γ A B) : EqKAg E I n ρ₀ k LE LT Γ B A :=
  (eqKA_symm_validg hEN HS HT h).1

theorem eqKA_validg (hEN : EnvNormCtorTypeA E) (HS : LowEqSymmA k LE) (HT : LowEqTransA k LE)
    {Γ : LCtxA} {A B : ExprA}
    (h : EqKAg E I n ρ₀ k LE LT Γ A B) {R : ExprA → ExprA → Prop}
    (hA : TyKAg E I n ρ₀ k LE LT Γ A R) : ∃ R', TyKAg E I n ρ₀ k LE LT Γ B R' :=
  (eqKA_symm_validg hEN HS HT h).2 R hA

end EqSymm

/-! ## (4) the knot over all heights -/

/-- the PER properties at height `k` of the tied relation. -/
def LRPerAg (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) : Prop :=
  (∀ {Γ : LCtxA} {A B : ExprA}, LREqAg E I n ρ₀ k Γ A B → LREqAg E I n ρ₀ k Γ B A) ∧
  (∀ {Γ : LCtxA} {A B X : ExprA}, LREqAg E I n ρ₀ k Γ A B → LREqAg E I n ρ₀ k Γ B X →
    LREqAg E I n ρ₀ k Γ A X) ∧
  (∀ {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}, LRTyAg E I n ρ₀ k Γ A R → PerMotA R) ∧
  (∀ {Γ : LCtxA} {A B : ExprA}, LREqAg E I n ρ₀ k Γ A B →
    (∃ R, LRTyAg E I n ρ₀ k Γ A R) → ∃ R', LRTyAg E I n ρ₀ k Γ B R')

theorem LRPerA_allg {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}
    (hEN : EnvNormCtorTypeA E) :
    ∀ k : Nat, LRPerAg E I n ρ₀ k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have HS : LowEqSymmA k (fun j _ => LREqAg E I n ρ₀ j) := fun j hj _ _ _ h => (ih j hj).1 h
    have HT : LowEqTransA k (fun j _ => LREqAg E I n ρ₀ j) :=
      fun j hj _ _ _ _ h h' => (ih j hj).2.1 h h'
    refine ⟨fun h => ?_, fun h h' => ?_, fun h => ?_, fun h hA => ?_⟩
    · rw [LREqA_eqg] at h ⊢; exact eqKA_symmg hEN HS HT h
    · rw [LREqA_eqg] at h h' ⊢; exact eqKA_transg hEN HS HT h h'
    · rw [LRTyA_eqg] at h; exact tyKA_perg hEN HS HT h
    · obtain ⟨R, hR⟩ := hA
      rw [LREqA_eqg] at h
      rw [LRTyA_eqg] at hR
      obtain ⟨R', hR'⟩ := eqKA_validg hEN HS HT h hR
      exact ⟨R', by rw [LRTyA_eqg]; exact hR'⟩

section Knot
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {k : Nat}

/-- the lower heights' symmetry and transitivity, from the knot. -/
theorem lowEqSymmA_allg (hEN : EnvNormCtorTypeA E) (k : Nat) : LowEqSymmA k (fun j _ => LREqAg E I n ρ₀ j) :=
  fun j _ _ _ _ h => (LRPerA_allg hEN j).1 h

theorem lowEqTransA_allg (hEN : EnvNormCtorTypeA E) (k : Nat) : LowEqTransA k (fun j _ => LREqAg E I n ρ₀ j) :=
  fun j _ _ _ _ _ h h' => (LRPerA_allg hEN j).2.1 h h'

/-- type equality transports the term relation (the knotted form; moved here from
    `RcicAnnLRConv`, M2-f (3b): transport now uses the lower heights' PER). -/
theorem LREqA_transportg (hEN : EnvNormCtorTypeA E) {Γ : LCtxA} {A B : ExprA}
    (h : LREqAg E I n ρ₀ k Γ A B)
    {R R' : ExprA → ExprA → Prop} (hA : LRTyAg E I n ρ₀ k Γ A R) (hB : LRTyAg E I n ρ₀ k Γ B R') :
    R = R' := by
  rw [LREqA_eqg] at h
  rw [LRTyA_eqg] at hA hB
  exact eqKA_transportg hEN (lowEqSymmA_allg hEN k) (lowEqTransA_allg hEN k) h hA hB

/-- related at `A`, and `A ≡ B` with `B` valid: related at `B`. -/
theorem LRRelA_transportg (hEN : EnvNormCtorTypeA E) {Γ : LCtxA} {A B a b : ExprA}
    (h : LREqAg E I n ρ₀ k Γ A B)
    (hB : ∃ R', LRTyAg E I n ρ₀ k Γ B R') (hab : LRRelAg E I n ρ₀ k Γ A a b) :
    LRRelAg E I n ρ₀ k Γ B a b := by
  obtain ⟨R, hR, hab⟩ := hab
  obtain ⟨R', hR'⟩ := hB
  refine ⟨R', hR', ?_⟩
  rw [LREqA_transportg hEN h hR hR'] at hab
  exact hab

theorem LREqA_symmg (hEN : EnvNormCtorTypeA E) {Γ : LCtxA} {A B : ExprA}
    (h : LREqAg E I n ρ₀ k Γ A B) :
    LREqAg E I n ρ₀ k Γ B A := (LRPerA_allg hEN k).1 h

theorem LREqA_transg (hEN : EnvNormCtorTypeA E) {Γ : LCtxA} {A B X : ExprA}
    (h : LREqAg E I n ρ₀ k Γ A B)
    (h' : LREqAg E I n ρ₀ k Γ B X) : LREqAg E I n ρ₀ k Γ A X := (LRPerA_allg hEN k).2.1 h h'

theorem LREqA_validg (hEN : EnvNormCtorTypeA E) {Γ : LCtxA} {A B : ExprA}
    (h : LREqAg E I n ρ₀ k Γ A B)
    (hA : ∃ R, LRTyAg E I n ρ₀ k Γ A R) : ∃ R', LRTyAg E I n ρ₀ k Γ B R' :=
  (LRPerA_allg hEN k).2.2.2 h hA

theorem LRRelA_symmg (hEN : EnvNormCtorTypeA E) {Γ : LCtxA} {A a b : ExprA}
    (h : LRRelAg E I n ρ₀ k Γ A a b) :
    LRRelAg E I n ρ₀ k Γ A b a := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨R, hR, ((LRPerA_allg hEN k).2.2.1 hR).1 a b hab⟩

theorem LRRelA_transg (hEN : EnvNormCtorTypeA E) {Γ : LCtxA} {A a b c : ExprA}
    (h : LRRelAg E I n ρ₀ k Γ A a b)
    (h' : LRRelAg E I n ρ₀ k Γ A b c) : LRRelAg E I n ρ₀ k Γ A a c := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨R, hR, ((LRPerA_allg hEN k).2.2.1 hR).2 a b c hab (h'.at hR)⟩

/-- related terms are self-related. -/
theorem LRRelA_refl_leftg (hEN : EnvNormCtorTypeA E) {Γ : LCtxA} {A a b : ExprA}
    (h : LRRelAg E I n ρ₀ k Γ A a b) :
    LRRelAg E I n ρ₀ k Γ A a a := LRRelA_transg hEN h (LRRelA_symmg hEN h)

/-- transport without a validity hypothesis on the right: `A ≡ B` with `A` valid
    makes `B` valid. -/
theorem LRRelA_transport'g (hEN : EnvNormCtorTypeA E) {Γ : LCtxA} {A B a b : ExprA}
    (h : LREqAg E I n ρ₀ k Γ A B)
    (hab : LRRelAg E I n ρ₀ k Γ A a b) : LRRelAg E I n ρ₀ k Γ B a b := by
  obtain ⟨R, hR, hab'⟩ := hab
  exact LRRelA_transportg hEN h (LREqA_validg hEN h ⟨R, hR⟩) ⟨R, hR, hab'⟩

end Knot

#print axioms eqKA_transport_perg
#print axioms eqKA_transportg
#print axioms tyKA_perg
#print axioms LREqA_transportg
#print axioms LRRelA_transportg
#print axioms eqKA_transg
#print axioms eqKA_symm_validg
#print axioms LRPerA_allg
#print axioms LRRelA_symmg
#print axioms LRRelA_transg
#print axioms LRRelA_transport'g

end Rcic.Declarative.Ann
