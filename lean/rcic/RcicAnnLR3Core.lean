import rcic.RcicAnnLR3Family
import rcic.RcicAnnLR3PropEq
import rcic.RcicAnnLR

/-!
# LR3 simultaneous relational-head and syntactic-index core

This is the changed-definition seed from the non-G `RcicAnnLR` core. One
explicit certified `HeadLayerA3` parameter is shared across the entire tower,
all contexts and all worlds. The family operator uses that layer's typed
term chains and positive normality. Both `EqKA3.fam` and `TyKA3.fam` use the canonical declared-telescope
index relation; neither asks for logical-relation validity at an index domain.
Index-domain transport is annotated typed conversion. Every plain constructor
field and every inner domain of a function-recursive field still carries the
new semantic validity/equality judgment. Recursive fields retain the same
least-fixed-point positions and typed carrier/parameter coherence.

The proposition key is `IsPropTyA3`, based on relational `SortOfA3` and the
same layer's weak-head witnesses. A later positive certificate language can
be supplied by another certified head layer without copying this tower.
The lower-height type aliases and the head-independent
typed conversion, telescope, world, and fixed-point algebra are shared.
No fundamental theorem, PER, weakening, row theorem, or environment supplier
for the new tower is asserted here. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

/-- The family operator using the supplied layer's typed chains and normality. -/
def FamPhiWA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (r : Nat) (m : CheckedMemberA)
    (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
    (RsI : InnerRelsA) (X : WRelA) (ρ : WkSpecA) : CRelA :=
  FamPhiWParamA3 E I n (TyHRedStarA3 E I n H) H.normal Γ r m Rs RsI X ρ

/-- A valid proposition-as-type has a typed LR3 chain to a triple-like form. -/
def PropValidA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n)
    (Γ : LCtxA) (a : ExprA) : Prop :=
  ∃ N, WhTyA3 E I n H Γ a N ∧ TripleLikeA3 E I n H Γ N

mutual

inductive EqKA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n) (ρ₀ : Nat → Nat) (k : Nat)
    (LE : LowEqTA k) (LT : LowTyTA k) : LCtxA → ExprA → ExprA → Prop
  | sort {Γ : LCtxA} {A B : ExprA} {l l' : Level}
      (hA : WhTyA3 E I n H Γ A (.sort l)) (hB : WhTyA3 E I n H Γ B (.sort l'))
      (hk : ht ρ₀ l < k) (hl : eqN l l')
      (hc : Nonempty (TyConvA E I n Γ A B)) : EqKA3 E I n H ρ₀ k LE LT Γ A B
  | pi {Γ : LCtxA} {A B D C D' C' : ExprA} {u v u' v' : Level}
      (hA : WhTyA3 E I n H Γ A (.pi D u C v)) (hB : WhTyA3 E I n H Γ B (.pi D' u' C' v'))
      (hu : eqN u u') (hv : eqN v v')
      (hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
      (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
      (hD'ty : Nonempty (HasTyA E I n Γ D' (.sort u')))
      (hC'ty : Nonempty (HasTyA E I n (.assumption D' :: Γ) C' (.sort v')))
      (RD : WkSpecA → ExprA → ExprA → Prop)
      (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
        TyKA3 E I n H ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
      (hDeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
        EqKA3 E I n H ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (wkExprA ρ D'))
      (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKA3 E I n H ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C')))
      (hc : Nonempty (TyConvA E I n Γ A B)) : EqKA3 E I n H ρ₀ k LE LT Γ A B

  | fam {Γ : LCtxA} {A B : ExprA} {r : Nat} {ls ls' : List Level} {ps ps' is is' : List ExprA}
      {m : CheckedMemberA} {u₀ : Level}
      (hA : WhTyA3 E I n H Γ A (foldAppsA (.const r ls) (ps ++ is)))
      (hB : WhTyA3 E I n H Γ B (foldAppsA (.const r ls') (ps' ++ is')))
      (hnA : H.normal Γ (foldAppsA (.const r ls) (ps ++ is)))
      (hnB : H.normal Γ (foldAppsA (.const r ls') (ps' ++ is')))
      (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
      (hsh : piBodyA m.mtypeA = .sort u₀) (hls : eqNList ls ls')
      (hps : ps.length = m.nparamsA) (hps' : ps'.length = m.nparamsA)
      (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
      (RsI : InnerRelsA)
      (hFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA)
          (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          TyKA3 E I n H ρ₀ k LE LT (wkCtxA ρ Γ) D
            (Rs ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre)))
      (hFldeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          EqKA3 E I n H ρ₀ k LE LT (wkCtxA ρ Γ) D D')
      (hFldRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          RecDomRelA E I n (wkCtxA ρ Γ) r m (RouteCIndex.IndexRelsA E I n Γ m ρ) ls (ps.map (wkExprA ρ)) D D')
      (hFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' →
          ArgsRelPA (RouteCIndex.IndexRelsA E I n Γ m ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
          applyTelA pre TF = some (.pi D uD C vC) →
          applyTelA pre' TF' = some (.pi D' uD' C' vC') →
          Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D'))
      (hXFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
          EqKA3 E I n H ρ₀ k LE LT (wkCtxA ρ Γ) D D')
      (hXRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
          RecDomRelXA E I n (wkCtxA ρ Γ) r m (RouteCIndex.IndexRelsA E I n Γ m ρ) ls (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) D D')
      (hXRes : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds : List FieldShape) (T T' : ExprA) (pre pre' : List ExprA)
          (R R' : ExprA),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T kinds pre pre' →
          applyTelA pre T = some R → applyTelA pre T' = some R' →
          RecDomRelXA E I n (wkCtxA ρ Γ) r m (RouteCIndex.IndexRelsA E I n Γ m ρ) ls (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) R R')
      (hXResR : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds : List FieldShape) (T T' T'' : ExprA) (pre pre' : List ExprA)
          (R' R'' : ExprA),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T'' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T kinds pre pre' →
          applyTelA pre' T' = some R' → applyTelA pre' T'' = some R'' →
          RecDomRelXA E I n (wkCtxA ρ Γ) r m (RouteCIndex.IndexRelsA E I n Γ m ρ) ls (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) R' R'')
      (hXFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF TF' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF →
          applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF' →
          ArgsRelPA (RouteCIndex.IndexRelsA E I n Γ m ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
          applyTelA pre TF = some (.pi D uD C vC) → applyTelA pre TF' = some (.pi D' uD' C' vC') →
          Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D'))
      (hxs : ∀ (TF : ExprA), applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF →
          ArgsRelPA (RouteCIndex.IndexRelsA E I n Γ m [] ls) m.nparamsA ps TF is is')
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
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
            (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' →
          applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
          TyKA3 E I n H ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁
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
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
            (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' →
          applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
          applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
          EqKA3 E I n H ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
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
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
          applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
          RecDomRelA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (RouteCIndex.IndexRelsA E I n Γ m (WkSpecA.comp ρ ρ')) ls
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
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
            (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' →
          applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
          applyTelA zs (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
          EqKA3 E I n H ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
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
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
          applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs (wkExprA ρ' D') = some C₁' →
          RecDomRelXA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (RouteCIndex.IndexRelsA E I n Γ m (WkSpecA.comp ρ ρ')) ls
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
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
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
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
          Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D')) :
      EqKA3 E I n H ρ₀ k LE LT Γ A B
  | stuck {Γ : LCtxA} {A B N N' : ExprA}
      (hA : WhTyA3 E I n H Γ A N) (hB : WhTyA3 E I n H Γ B N')
      (hN : TripleLikeA3 E I n H Γ N) (hN' : TripleLikeA3 E I n H Γ N')
      (hc : Nonempty (TyConvA E I n Γ A B)) : EqKA3 E I n H ρ₀ k LE LT Γ A B

inductive TyKA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n) (ρ₀ : Nat → Nat) (k : Nat)
    (LE : LowEqTA k) (LT : LowTyTA k) : LCtxA → ExprA → (ExprA → ExprA → Prop) → Prop

  | prop {Γ : LCtxA} {A A' : ExprA}
      (hA : WhTyA3 E I n H Γ A A') (hn : H.normal Γ A')
      (hP : IsPropTyA3 E I n H Γ A') :
      TyKA3 E I n H ρ₀ k LE LT Γ A (fun a b =>
        Nonempty (HasTyA E I n Γ a A') ∧ Nonempty (HasTyA E I n Γ b A') ∧
        Nonempty (ConvA E I n Γ a b A'))

  | sortT {Γ : LCtxA} {A : ExprA} {l : Level}
      (hA : WhTyA3 E I n H Γ A (.sort l)) (hz : isZero l = false) (hk : ht ρ₀ l < k) :
      TyKA3 E I n H ρ₀ k LE LT Γ A (fun a b =>
        LE (ht ρ₀ l) hk Γ a b ∧
        (∃ R, LT (ht ρ₀ l) hk Γ a R) ∧
        (∃ R, LT (ht ρ₀ l) hk Γ b R) ∧
        Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
        Nonempty (ConvA E I n Γ a b (.sort l)))

  | sortP {Γ : LCtxA} {A : ExprA} {l : Level}
      (hA : WhTyA3 E I n H Γ A (.sort l)) (hz : isZero l = true) :
      TyKA3 E I n H ρ₀ k LE LT Γ A (fun a b =>
        PropValidA3 E I n H Γ a ∧ PropValidA3 E I n H Γ b ∧
        Nonempty (HasTyA E I n Γ a (.sort l)) ∧ Nonempty (HasTyA E I n Γ b (.sort l)) ∧
        Nonempty (ConvA E I n Γ a b (.sort l)) ∧ PropEqA3 E I n H Γ a b)
  | pi {Γ : LCtxA} {A D C : ExprA} {u v : Level}
      (hA : WhTyA3 E I n H Γ A (.pi D u C v))
      (hnp : ¬ IsPropTyA3 E I n H Γ (.pi D u C v))
      (hDty : Nonempty (HasTyA E I n Γ D (.sort u)))
      (hCty : Nonempty (HasTyA E I n (.assumption D :: Γ) C (.sort v)))
      (RD : WkSpecA → ExprA → ExprA → Prop)
      (hD : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
        TyKA3 E I n H ρ₀ k LE LT (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ))
      (RC : WkSpecA → ExprA → ExprA → ExprA → Prop)
      (hC : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        TyKA3 E I n H ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) (RC ρ a))
      (hCeq : ∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
        EqKA3 E I n H ρ₀ k LE LT (wkCtxA ρ Γ)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C))) :
      TyKA3 E I n H ρ₀ k LE LT Γ A (fun f g =>
        (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a a' : ExprA, RD ρ a a' →
          RC ρ a (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')) ∧
        Nonempty (HasTyA E I n Γ f (.pi D u C v)) ∧ Nonempty (HasTyA E I n Γ g (.pi D u C v)) ∧
        Nonempty (ConvA E I n Γ f g (.pi D u C v)))

  | fam {Γ : LCtxA} {A : ExprA} {r : Nat} {ls : List Level} {ps is : List ExprA}
      {m : CheckedMemberA} {u u₀ : Level}
      (hA : WhTyA3 E I n H Γ A (foldAppsA (.const r ls) (ps ++ is)))
      (hn : H.normal Γ (foldAppsA (.const r ls) (ps ++ is)))
      (hnp : ¬ IsPropTyA3 E I n H Γ (foldAppsA (.const r ls) (ps ++ is)))
      (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
      (hsh : piBodyA m.mtypeA = .sort u₀) (hps : ps.length = m.nparamsA)
      (hu : applyTelA (ps ++ is) (instantiateLevelsA ls m.mtypeA) = some (.sort u))
      (hz : isZero u = false)
      (Rs : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop)
      (RsI : InnerRelsA)
      (hFld : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA)
          (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          TyKA3 E I n H ρ₀ k LE LT (wkCtxA ρ Γ) D
            (Rs ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre)))
      (hFldeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          EqKA3 E I n H ρ₀ k LE LT (wkCtxA ρ Γ) D D')
      (hFldRec : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          RecDomRelA E I n (wkCtxA ρ Γ) r m (RouteCIndex.IndexRelsA E I n Γ m ρ) ls (ps.map (wkExprA ρ)) D D')
      (hFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' →
          ArgsRelPA (RouteCIndex.IndexRelsA E I n Γ m ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
          applyTelA pre TF = some (.pi D uD C vC) →
          applyTelA pre' TF' = some (.pi D' uD' C' vC') →
          Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D'))
      (hxsD : ∀ (TF : ExprA), applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF →
          ArgsRelPA (RouteCIndex.IndexRelsA E I n Γ m [] ls) m.nparamsA ps TF is is)
      (hFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
            (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' →
          applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
          TyKA3 E I n H ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁
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
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
            (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' →
          applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
          applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
          EqKA3 E I n H ρ₀ k LE LT (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
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
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
          applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
          RecDomRelA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m (RouteCIndex.IndexRelsA E I n Γ m (WkSpecA.comp ρ ρ')) ls
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
              (LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D')) :
      TyKA3 E I n H ρ₀ k LE LT Γ A (fun a b =>
        LfpWA (FamPhiWA3 E I n H Γ r m Rs RsI) [] (foldAppsA (.const r ls) (ps ++ is)) a b)
  | stuck {Γ : LCtxA} {A N : ExprA}
      (hA : WhTyA3 E I n H Γ A N) (hN : StuckA3 E I n H Γ N) :
      TyKA3 E I n H ρ₀ k LE LT Γ A (fun a b =>
        Nonempty (HasTyA E I n Γ a N) ∧ Nonempty (HasTyA E I n Γ b N) ∧
        Nonempty (ConvA E I n Γ a b N))
end

mutual
def LREqA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n) (ρ₀ : Nat → Nat) :
    (k : Nat) → LCtxA → ExprA → ExprA → Prop
  | k => EqKA3 E I n H ρ₀ k (fun j _ => LREqA3 E I n H ρ₀ j) (fun j _ => LRTyA3 E I n H ρ₀ j)
  termination_by k => k
  decreasing_by all_goals assumption
def LRTyA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n) (ρ₀ : Nat → Nat) :
    (k : Nat) → LCtxA → ExprA → (ExprA → ExprA → Prop) → Prop
  | k => TyKA3 E I n H ρ₀ k (fun j _ => LREqA3 E I n H ρ₀ j) (fun j _ => LRTyA3 E I n H ρ₀ j)
  termination_by k => k
  decreasing_by all_goals assumption
end

theorem LREqA3_eq (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n) (ρ₀ : Nat → Nat) (k : Nat) :
    LREqA3 E I n H ρ₀ k =
      EqKA3 E I n H ρ₀ k (fun j _ => LREqA3 E I n H ρ₀ j) (fun j _ => LRTyA3 E I n H ρ₀ j) := by
  rw [LREqA3]

theorem LRTyA3_eq (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n) (ρ₀ : Nat → Nat) (k : Nat) :
    LRTyA3 E I n H ρ₀ k =
      TyKA3 E I n H ρ₀ k (fun j _ => LREqA3 E I n H ρ₀ j) (fun j _ => LRTyA3 E I n H ρ₀ j) := by
  rw [LRTyA3]


/-- The term relation at a type in the new simultaneous tower. -/
def LRRelA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (H : HeadLayerA3 E I n) (ρ₀ : Nat → Nat) (k : Nat)
    (Γ : LCtxA) (A a b : ExprA) : Prop :=
  ∃ R : ExprA → ExprA → Prop, LRTyA3 E I n H ρ₀ k Γ A R ∧ R a b

#print axioms FamPhiWA3
#print axioms PropValidA3
#print axioms EqKA3
#print axioms TyKA3
#print axioms LREqA3
#print axioms LRTyA3
#print axioms LREqA3_eq
#print axioms LRTyA3_eq
#print axioms LRRelA3

end Rcic.Declarative.Ann.LR3
