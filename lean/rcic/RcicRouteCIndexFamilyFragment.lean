import rcic.RcicRouteCIndexTransport

/-!
# A field-preserving family clause and an inhabited large-index fragment

The constructor below composes the landed family operator and the landed
semantics of its non-index positions. The family telescope itself is checked
by annotated typed conversion. The supplied Pi action for the admitted family
`F : (x : Sort 1) → Sort 1` retains semantic arguments at the Pi domain and
returns these structural family certificates. It is a fragment of the desired
replacement, not the full mutual logical relation or a row supplier.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.RouteCIndex

open Rcic.Declarative

/-- The landed family validity obligations with syntactic index domains.
Every non-index field and every inner function-field domain retains `LRTyA`;
field-domain equality retains `LREqA`. Only index-domain validity disappears. -/
inductive IndexFamTyA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat) :
    LCtxA → ExprA → (ExprA → ExprA → Prop) → Prop
  | fam {Γ : LCtxA} {A : ExprA} {r : Nat} {ls : List Level} {ps is : List ExprA}
      {m : CheckedMemberA} {u u₀ : Level}
      (hA : WhTyA E I n Γ A (foldAppsA (.const r ls) (ps ++ is)))
      (hn : hStepFnA E I.fn Γ (foldAppsA (.const r ls) (ps ++ is)) = none)
      (hnp : ¬ IsPropTy E I Γ (foldAppsA (.const r ls) (ps ++ is)))
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
              (LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          LRTyA E I n ρ₀ k (wkCtxA ρ Γ) D
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
              (LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          LREqA E I n ρ₀ k (wkCtxA ρ Γ) D D')
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
              (LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          RecDomRelA E I n (wkCtxA ρ Γ) r m ((IndexRelsA E I n Γ m) ρ) ls (ps.map (wkExprA ρ)) D D')
      (hFldFeq : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
          (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF m.mtypeA) = some TF →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' m.mtypeA) = some TF' →
          ArgsRelPA ((IndexRelsA E I n Γ m) ρ lsF) m.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
          applyTelA pre TF = some (.pi D uD C vC) →
          applyTelA pre' TF' = some (.pi D' uD' C' vC') →
          Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D'))
      (hxsD : ∀ (TF : ExprA), applyTelA ps (instantiateLevelsA ls m.mtypeA) = some TF →
          ArgsRelPA ((IndexRelsA E I n Γ m) [] ls) m.nparamsA ps TF is is)
      (hFldI : ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
          (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (j : Nat) (T : ExprA)
          (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
          E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some r →
          ctorShapesA r m.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
          kinds = ksPre ++ FieldShape.recursive (j + 1) :: ks →
          eqNList ls lsA → eqNListB n lsA lsC →
          applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
          ArgsRelA (Rs ρ c lsC) (famRecRelA m (ps.map (wkExprA ρ)) lsA
              (LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
            (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' →
          applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
          LRTyA E I n ρ₀ k (wkCtxA ρ' (wkCtxA ρ Γ)) D₁
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
              (LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
            (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' →
          applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
          applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
          LREqA E I n ρ₀ k (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁')
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
              (LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
          ArgsRelPA (innerRelsA RsI ρ c lsC (m.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre) ρ') 0 []
            (wkExprA ρ' D) zs zs' → zs.length = j + 1 →
          applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
          RecDomRelA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) r m ((IndexRelsA E I n Γ m) (WkSpecA.comp ρ ρ')) ls
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
              (LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) ρ))
              (famFunRelA E I n (wkCtxA ρ Γ) m (innerRelsA RsI ρ c lsC) (ps.map (wkExprA ρ)) lsA
                (fun ρ' => LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) (WkSpecA.comp ρ ρ')))
            m.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
          applyTelA pre T = some (.pi D uD C vC) →
          applyTelA pre' T' = some (.pi D' uD' C' vC') →
          Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D')) :
      IndexFamTyA E I n ρ₀ k Γ A (fun a b =>
        LfpWA (FamPhiWA E I n Γ r m Rs (IndexRelsA E I n Γ m) RsI) [] (foldAppsA (.const r ls) (ps ++ is)) a b)

/-- No constructors of `F` are present in the admitted boundary environment. -/
theorem pin_noCtor : NoFamilyCtorA (pinFamFEnvA 0) 0 := by
  intro c cm hm hc _
  rw [pinFamF_ind hm] at hc
  cases hc

def emptyFieldRelsA : WkSpecA → Nat → List Level → Nat → List ExprA → ExprA → ExprA → Prop :=
  fun _ _ _ _ _ _ _ => False

def emptyInnerRelsA : InnerRelsA := fun _ _ _ _ _ _ _ _ _ => False

/-- The actual structural carrier of `F a`, with an empty constructor signature. -/
def pinCarrierA (n : Nat) (Γ : LCtxA) (A : ExprA) : ExprA → ExprA → Prop :=
  IndexFamRelA (pinFamFEnvA 0) noIotaA n Γ 0 (pinFamFA 0)
    emptyFieldRelsA emptyInnerRelsA [] A

def pinAppTy {n : Nat} {Γ : LCtxA} {a : ExprA}
    (ha : HasTyA (pinFamFEnvA 0) noIotaA n Γ a (.sort (.succ .zero))) :
    HasTyA (pinFamFEnvA 0) noIotaA n Γ (.app (.const 0 []) a) (.sort (.succ .zero)) :=
  .app Γ (.const 0 []) a (.sort (.succ .zero)) (.sort (.succ .zero))
    (.succ (.succ .zero)) (.succ (.succ .zero)) (.succ (.succ .zero))
    (.sort _ (.succ .zero)) (.sort Γ (.succ .zero)) (pinFamFConstTy (pinFamF_members 0) n Γ) ha

theorem pinApp_nf (Γ : LCtxA) (a : ExprA) :
    hStepFnA (pinFamFEnvA 0) noIotaA.fn Γ (foldAppsA (.const 0 []) [a]) = none :=
  hStepFnA_constSpine_none (noIotaA_recHead _) (pinFamF_members 0) (Or.inr rfl)
    (fun h => MemberClass.noConfusion h) Γ _ (by rw [foldAppsA_const_head])

theorem pinApp_notProp (Γ : LCtxA) (a : ExprA) :
    ¬ IsPropTy (pinFamFEnvA 0) noIotaA Γ (foldAppsA (.const 0 []) [a]) := by
  intro h
  have hz := ((isPropTy_famApp_iff (u₀ := .succ .zero) (pinFamF_members 0) rfl [] [a]).1 h).2.2
  exact Bool.noConfusion hz

theorem pin_index_domain {ls : List Level} {pre : List ExprA} {D C : ExprA} {u v : Level}
    (h : applyTelA pre (instantiateLevelsA ls (pinFamFA 0).mtypeA) = some (.pi D u C v)) :
    pre = [] ∧ D = .sort (.succ .zero) := by
  cases pre with
  | nil => cases h; exact ⟨rfl, rfl⟩
  | cons a rest =>
      have e : applyTelA (a :: rest) (instantiateLevelsA ls (pinFamFA 0).mtypeA) =
          applyTelA rest (.sort (.succ .zero)) := rfl
      rw [e] at h
      exact (applyTelA_sort_ne_pi rest h).elim

/-- The fixture supplies the typed domain conversions consumed by general
index PER and carrier transport, in every context. -/
theorem pin_indexDomains (n : Nat) (Γ : LCtxA) :
    IndexDomainsConvertA (pinFamFEnvA 0) noIotaA n Γ (pinFamFA 0) [] [] := by
  intro lsF lsF' TF TF' pre pre' D uD C vC D' uD' C' vC' _ _ hTF hTF' _ hD hD'
  cases hTF
  cases hTF'
  obtain ⟨_, rfl⟩ := pin_index_domain hD
  obtain ⟨_, rfl⟩ := pin_index_domain hD'
  exact ⟨.refl _ _⟩

theorem pin_indexPer (n : Nat) (Γ : LCtxA) :
    IdxPerA n (IndexRelsA (pinFamFEnvA 0) noIotaA n Γ (pinFamFA 0) []) (pinFamFA 0) [] [] :=
  indexRelsA_per rfl (pin_indexDomains n Γ)

/-- Formation of `F a` at every height. The index is merely typed at its
declared sort; it is not recursively interpreted at the carrier height. -/
theorem pin_family_formation {n k : Nat} (ρ₀ : Nat → Nat) {Γ : LCtxA} {a : ExprA}
    (ha : HasTyA (pinFamFEnvA 0) noIotaA n Γ a (.sort (.succ .zero))) :
    IndexFamTyA (pinFamFEnvA 0) noIotaA n ρ₀ k Γ (.app (.const 0 []) a)
      (pinCarrierA n Γ (.app (.const 0 []) a)) := by
  refine .fam (r := 0) (ls := []) (ps := []) (is := [a]) (m := pinFamFA 0)
    (u := .succ .zero) (u₀ := .succ .zero) (whTyA_of_hasTy (pinAppTy ha))
    (pinApp_nf Γ a) (pinApp_notProp Γ a) (pinFamF_members 0) rfl rfl rfl rfl rfl
    emptyFieldRelsA emptyInnerRelsA ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro ρ _
    exact pin_indexDomains n (wkCtxA ρ Γ)
  · intro TF hTF
    cases hTF
    refine .cons _ _ _ _ _ _ _ _ _ _ ?_ (.nil _ _ _)
    exact ⟨.sort (.succ .zero), .succ (.succ .zero), .sort (.succ .zero),
      .succ (.succ .zero), rfl, ⟨.refl _ _ _ ha⟩⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk'
    rw [pinFamF_ind hcm] at hk'
    cases hk'

/-- A sort-level family pair has structural carrier certificates on both sides,
agreement of those carrier relations, and the two typings and conversion. -/
def IndexFamSortPairA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat)
    (k : Nat) (Γ : LCtxA) (u : Level) (A B : ExprA) : Prop :=
  ∃ R S, IndexFamTyA E I n ρ₀ k Γ A R ∧ IndexFamTyA E I n ρ₀ k Γ B S ∧
    (∀ a b, R a b ↔ S a b) ∧ Nonempty (HasTyA E I n Γ A (.sort u)) ∧
    Nonempty (HasTyA E I n Γ B (.sort u)) ∧ Nonempty (ConvA E I n Γ A B (.sort u))

/-- Application for the positive fragment, including structural carrier
transport. No semantic premise about an index at height `1` is required. -/
theorem pin_family_application {n k : Nat} (ρ₀ : Nat → Nat) {Γ : LCtxA} {a b : ExprA}
    (ha : HasTyA (pinFamFEnvA 0) noIotaA n Γ a (.sort (.succ .zero)))
    (hb : HasTyA (pinFamFEnvA 0) noIotaA n Γ b (.sort (.succ .zero)))
    (hab : ConvA (pinFamFEnvA 0) noIotaA n Γ a b (.sort (.succ .zero))) :
    IndexFamSortPairA (pinFamFEnvA 0) noIotaA n ρ₀ k Γ (.succ .zero)
      (.app (.const 0 []) a) (.app (.const 0 []) b) := by
  have hc : ConvA (pinFamFEnvA 0) noIotaA n Γ (.app (.const 0 []) a)
      (.app (.const 0 []) b) (.sort (.succ .zero)) :=
    .app Γ _ _ _ _ _ _ _ _ (.refl _ _ _ (pinFamFConstTy (pinFamF_members 0) n Γ))
      hab (.sort _ (.succ .zero)) (pinAppTy hb)
  have ht : Nonempty (TyConvA (pinFamFEnvA 0) noIotaA n Γ
      (.app (.const 0 []) a) (.app (.const 0 []) b)) :=
    ⟨.of Γ _ _ (.succ .zero) (.succ .zero) (.succ .zero)
      (pinAppTy ha) (eqNA_refl _) (pinAppTy hb) (eqNA_refl _) hc⟩
  refine ⟨_, _, pin_family_formation ρ₀ ha, pin_family_formation ρ₀ hb, ?_,
    ⟨pinAppTy ha⟩, ⟨pinAppTy hb⟩, ⟨hc⟩⟩
  intro x y
  have hw : IndexWalkA (pinFamFEnvA 0) noIotaA n Γ (pinFamFA 0).mtypeA (pinFamFA 0).mtypeA [a] [b] :=
    .cons _ _ _ _ _ _ _ _ a b [] [] ⟨hab⟩ ⟨.refl _ _⟩ (.nil _ _)
  constructor
  · intro hxy
    exact indexFamRelA_carrier (ps := []) (ls₀ := []) (ls := []) (ls' := []) (is := [a]) (is' := [b])
      rfl (pin_indexDomains n Γ) rfl trivial ⟨trivial, rfl⟩ rfl rfl hw ht hxy
  · intro hxy
    exact indexFamRelA_carrier (ps := []) (ls₀ := []) (ls := []) (ls' := []) (is := [b]) (is' := [a])
      rfl (pin_indexDomains n Γ) rfl trivial ⟨trivial, rfl⟩ rfl rfl
      (indexWalkA_symm hw) (tyConvA_symm_ne ht) hxy

/-- A Pi interpretation into the new family fragment. Its arguments use the
landed logical relation at the Pi domain, and its results retain family structure. -/
def IndexFamilyActionA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat)
    (k : Nat) (Γ : LCtxA) (D : ExprA) (u v : Level) (f g : ExprA) : Prop :=
  Nonempty (HasTyA E I n Γ D (.sort u)) ∧ ht ρ₀ v < k ∧
  (∀ ρ : WkSpecA, WkOkA E I n ρ Γ →
    ∃ RD, LRTyA E I n ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ D) RD) ∧
  (∀ ρ : WkSpecA, WkOkA E I n ρ Γ → ∀ a b : ExprA,
    LRRelA E I n ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ D) a b →
    IndexFamSortPairA E I n ρ₀ (ht ρ₀ v) (wkCtxA ρ Γ) v
      (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) b)) ∧
  DeclPairA E I n Γ (.pi D u (.sort v) (.succ v)) f g

/-- The actual all-world Pi supplier for the admitted large-index member. -/
theorem pin_member_action (n k : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA) (hk : 1 < k) :
    IndexFamilyActionA (pinFamFEnvA 0) noIotaA n ρ₀ k Γ
      (.sort (.succ .zero)) (.succ (.succ .zero)) (.succ .zero) (.const 0 []) (.const 0 []) := by
  refine ⟨⟨.sort Γ (.succ .zero)⟩, hk, ?_, ?_, ⟨pinFamFConstTy (pinFamF_members 0) n Γ⟩,
    ⟨pinFamFConstTy (pinFamF_members 0) n Γ⟩,
    ⟨.refl _ _ _ (pinFamFConstTy (pinFamF_members 0) n Γ)⟩⟩
  · intro ρ _
    rw [wkExprA_sort]
    exact LRTyA_sort_valid _ hk
  · intro ρ _ a b hab
    rw [wkExprA_sort] at hab
    obtain ⟨ha, hb⟩ := LRRelA_hasTy hab
    have hc := LRRelA_conv hab
    rw [wkExprA_const]
    exact ha.elim fun ta => hb.elim fun tb => hc.elim fun tc => pin_family_application ρ₀ ta tb tc

/-- Exact environment-member quantifiers of the inhabited fragment. This is
not `EnvSemA`: its codomain is the separately named Pi/family interpretation. -/
def IndexFamilyMemberSupplyA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) : Prop :=
  ∀ r m, E.members r = some m → ∀ ls ls' : List Level, ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ Δ : LCtxA, Nonempty (CtxWfA E I n Δ) →
      ∃ D u v, instantiateLevelsA ls m.mtypeA = .pi D u (.sort v) (.succ v) ∧
        IndexFamilyActionA E I n ρ₀ k Δ D u v (.const r ls) (.const r ls')

/-- Every member of the actual admitted large-index environment is supplied. -/
theorem pin_members_supply (n : Nat) (ρ₀ : Nat → Nat) :
    IndexFamilyMemberSupplyA (pinFamFEnvA 0) noIotaA n ρ₀ := by
  intro r m hm ls ls' hlen _ _ hls
  by_cases hr : r = 0
  · subst hr
    cases hm
    have hnil : ls = [] := list_nil_of_length_zero ls hlen
    subst hnil
    have hnil' : ls' = [] := eqNList_nil_left hls
    subst hnil'
    refine ⟨2, fun k hk Δ _ => ⟨_, _, _, rfl, pin_member_action n k ρ₀ Δ (by omega)⟩⟩
  · simp [pinFamFEnvA, extendEnvA, emptyEnvA, hr] at hm

/-- The family-result fragment of the fundamental conclusion, retaining the
type-equality half and the original valid-substitution quantifiers. -/
def IndexFamilyFundArmA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat)
    (Γ : LCtxA) (e e' : ExprA) (u : Level) : Prop :=
    ∃ k₀ : Nat, ∀ k, k₀ ≤ k → ∀ (Δ : LCtxA) (σ σ' : SubstA),
      Nonempty (CtxWfA E I n Δ) → ValidSubstA E I n ρ₀ k Δ σ σ' Γ →
      LREqA E I n ρ₀ k Δ (substA σ (.sort u)) (substA σ' (.sort u)) ∧
      IndexFamSortPairA E I n ρ₀ (ht ρ₀ u) Δ u (substA σ e) (substA σ' e')

/-- A fundamental application arm over the original valid substitutions.
The index induction hypothesis is used to extract typed conversion and the
type-equality half; results retain the new carrier at its own height. -/
theorem pin_family_fund_arm {n : Nat} (ρ₀ : Nat → Nat) {Γ : LCtxA} {a b : ExprA}
    (hindex : FundArmA (pinFamFEnvA 0) noIotaA n ρ₀ Γ a b (.sort (.succ .zero))) :
    IndexFamilyFundArmA (pinFamFEnvA 0) noIotaA n ρ₀ Γ
      (.app (.const 0 []) a) (.app (.const 0 []) b) (.succ .zero) := by
  obtain ⟨k₀, hi⟩ := hindex
  refine ⟨k₀, fun k hk Δ σ σ' hΔ hσ => ?_⟩
  have hp := hi k hk Δ σ σ' hΔ hσ
  refine ⟨hp.1, ?_⟩
  have hab := hp.2
  simp only [substA_sort] at hab
  obtain ⟨ha, hb⟩ := LRRelA_hasTy hab
  have hc := LRRelA_conv hab
  simp only [substA_app, substA_const]
  exact ha.elim fun ta => hb.elim fun tb => hc.elim fun tc => pin_family_application ρ₀ ta tb tc

/-- An actual fundamental supplier for the closed large-index application:
the index arm is supplied by the landed sort arm, with no `EnvSemA` premise. -/
theorem closed_application_fund (n : Nat) (ρ₀ : Nat → Nat) (Γ : LCtxA) :
    IndexFamilyFundArmA (pinFamFEnvA 0) noIotaA n ρ₀ Γ pinFamFAppA pinFamFAppA (.succ .zero) :=
  pin_family_fund_arm ρ₀ (hasTyArmSortA_holds Γ .zero)

/-- Concrete positive counterpart to `closed_application_unrelated`. -/
theorem closed_application_related (n : Nat) (ρ₀ : Nat → Nat) :
    IndexFamSortPairA (pinFamFEnvA 0) noIotaA n ρ₀ (ht ρ₀ (.succ .zero)) [] (.succ .zero)
      pinFamFAppA pinFamFAppA :=
  pin_family_application ρ₀ (.sort _ .zero) (.sort _ .zero) (.refl _ _ _ (.sort _ .zero))

/-- The next boundary is inhabited: the environment and closed application
have the new structural fragment, while the landed full conclusion stays false. -/
theorem inhabited_next_boundary (n : Nat) :
    Nonempty (EnvWfA noIotaA (pinFamFEnvA 0)) ∧
    IndexFamilyMemberSupplyA (pinFamFEnvA 0) noIotaA n (fun _ => 1) ∧
    IndexFamSortPairA (pinFamFEnvA 0) noIotaA n (fun _ => 1) 1 [] (.succ .zero)
      pinFamFAppA pinFamFAppA ∧
    ¬ EnvSemA (pinFamFEnvA 0) noIotaA n (fun _ => 1) :=
  ⟨⟨RouteCLargeIndex.envWf⟩, pin_members_supply n (fun _ => 1),
    closed_application_related n (fun _ => 1), pinFamF0_envSem_false posValA_one⟩

/-- The Pi action is nonvacuous at its supplied threshold: `Sort 0` is an
actual related argument in the old domain, while its image has the new carrier. -/
theorem pin_action_nonvacuous (n : Nat) (ρ₀ : Nat → Nat) :
    LRRelA (pinFamFEnvA 0) noIotaA n ρ₀ 2 [] (.sort (.succ .zero))
      (.sort .zero) (.sort .zero) ∧
    IndexFamilyActionA (pinFamFEnvA 0) noIotaA n ρ₀ 2 []
      (.sort (.succ .zero)) (.succ (.succ .zero)) (.succ .zero) (.const 0 []) (.const 0 []) ∧
    IndexFamSortPairA (pinFamFEnvA 0) noIotaA n ρ₀ 1 [] (.succ .zero)
      pinFamFAppA pinFamFAppA :=
  ⟨LRRelA_sorts [] (Nat.lt_succ_self 1) (eqNA_refl _),
    pin_member_action n 2 ρ₀ [] (by decide), closed_application_related n ρ₀⟩

/-- The exact obstruction to feeding this fragment to the unchanged sort/fund
consumers: even an embedding that is allowed to choose a larger old height is
refuted by the supplied closed pair. A new mutual tower is still required. -/
theorem no_old_sort_bridge (n : Nat) :
    ¬ (∀ (Γ : LCtxA) (A B : ExprA),
      IndexFamSortPairA (pinFamFEnvA 0) noIotaA n (fun _ => 1) 1 Γ (.succ .zero) A B →
      ∃ k, LRRelA (pinFamFEnvA 0) noIotaA n (fun _ => 1) k Γ (.sort (.succ .zero)) A B) := by
  intro h
  obtain ⟨k, hk⟩ := h [] pinFamFAppA pinFamFAppA (closed_application_related n (fun _ => 1))
  exact RouteCLargeIndex.closed_application_unrelated n k pinFamFAppA hk

-- BEGIN RCIC_ROUTE_C_INDEX_ROOTS
#print axioms IndexFamTyA
#print axioms pin_noCtor
#print axioms emptyFieldRelsA
#print axioms emptyInnerRelsA
#print axioms pinCarrierA
#print axioms pinAppTy
#print axioms pinApp_nf
#print axioms pinApp_notProp
#print axioms pin_index_domain
#print axioms pin_indexDomains
#print axioms pin_indexPer
#print axioms pin_family_formation
#print axioms IndexFamSortPairA
#print axioms pin_family_application
#print axioms IndexFamilyActionA
#print axioms pin_member_action
#print axioms IndexFamilyMemberSupplyA
#print axioms pin_members_supply
#print axioms IndexFamilyFundArmA
#print axioms pin_family_fund_arm
#print axioms closed_application_fund
#print axioms closed_application_related
#print axioms inhabited_next_boundary
#print axioms pin_action_nonvacuous
#print axioms no_old_sort_bridge
#print axioms IndexFamTyA.fam
#print axioms IndexFamTyA.rec
-- END RCIC_ROUTE_C_INDEX_ROOTS

end Rcic.Declarative.Ann.RouteCIndex
