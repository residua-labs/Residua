import rcic.RcicNativeTypedModelCovWIrrelFullProofEquality

/-!
# Actual dependent domains are not determined by compact prefixes

This is a measurement of the landed grammar, with no grammar changes.
An admitted rigid axiom has the universe-1 instance of the identity signature.
At the same actual universe vector, its Nat, Nat-arrow, and Prop type
arguments all produce the same nonbottom compact prefix with one bottom
field. The second native domain is the actual earlier type argument.

The function/type distinction below uses native type conversion, not a
syntactic test. Its negative cases are supplied by native Sort/Pi
separation in the actual admitted environment. The impossibility is only
for a classifier of the compact alone; a classifier given actual native
application evidence is not refuted. The rigid axiom is explicitly not
claimed to be the transparent operational identity definition.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelKFragmentAudit TypedModelCovWAudit TypedModelCovWEtaAudit
open TypedModelCovWIrrelAudit

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def covWMatrixIdType : Expr Nat :=
  .pi (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))

def covWMatrixIdMember : CheckedMember :=
  ⟨.axiomM, 0, covWMatrixIdType, none⟩

def covWMatrixIdEnv : ResolvedEnv := extendEnv natEnvU 4 covWMatrixIdMember

def covWMatrixIdEnv_wf : EnvWfT covWMatrixIdEnv :=
  .axiom natEnvU 4 covWMatrixIdType
    (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero))) natEnvUWfT rfl
    (.pi [] (.sort (.succ .zero)) (.succ (.succ .zero))
      (.pi (.bvar 0) (.bvar 1)) (.imax (.succ .zero) (.succ .zero))
      (.sort [] (.succ .zero))
      (.pi _ (.bvar 0) (.succ .zero) (.bvar 1) (.succ .zero)
        (.bvar _ 0 _ rfl) (.bvar _ 1 _ rfl)))
    (fun _ => rfl) rfl

theorem covWMatrixIdEnv_inScope : covWMatrixIdEnv_wf.InScope :=
  natEnvUWfT_inScope

def covWMatrixId : Expr Nat := .const 4 []
def covWMatrixNat : Expr Nat := .const 0 []
def covWMatrixArrow : Expr Nat := .pi covWMatrixNat covWMatrixNat
def covWMatrixProp : Expr Nat := .sort .zero
def covWMatrixFalse : Expr Nat := .pi (.sort .zero) (.bvar 0)
def covWMatrixIdPrefix : CptWIrrel := .spine 4 [] [.bot]

def covWMatrix_nat_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWMatrixIdEnv n Γ covWMatrixNat (.sort (.succ .zero)) :=
  .const Γ 0 [] natFamMember rfl rfl rfl

def covWMatrix_arrow_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWMatrixIdEnv n Γ covWMatrixArrow (.sort (.succ .zero)) :=
  .conv Γ covWMatrixArrow
    (.sort (.imax (.succ .zero) (.succ .zero))) (.sort (.succ .zero))
    (.succ (.imax (.succ .zero) (.succ .zero)))
    (.pi Γ covWMatrixNat (.succ .zero) covWMatrixNat (.succ .zero)
      (covWMatrix_nat_ty n Γ) (covWMatrix_nat_ty n _))
    (.sorts Γ (.imax (.succ .zero) (.succ .zero)) (.succ .zero) (fun _ => rfl))

def covWMatrix_prop_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWMatrixIdEnv n Γ covWMatrixProp (.sort (.succ .zero)) :=
  .sort Γ .zero

def covWMatrix_false_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWMatrixIdEnv n Γ covWMatrixFalse (.sort .zero) :=
  .conv Γ covWMatrixFalse (.sort (.imax (.succ .zero) .zero)) (.sort .zero)
    (.succ (.imax (.succ .zero) .zero))
    (.pi Γ (.sort .zero) (.succ .zero) (.bvar 0) .zero
      (.sort Γ .zero) (.bvar _ 0 _ rfl))
    (.sorts Γ (.imax (.succ .zero) .zero) .zero (fun _ => rfl))

def covWMatrix_zero_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWMatrixIdEnv n Γ (.const 1 []) covWMatrixNat :=
  .const Γ 1 [] natZeroMember rfl rfl rfl

def covWMatrix_succ_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWMatrixIdEnv n Γ (.const 2 []) covWMatrixArrow :=
  .const Γ 2 [] natSuccMember rfl rfl rfl

def covWMatrix_id_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWMatrixIdEnv n Γ covWMatrixId
      (.pi (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))) :=
  .const Γ 4 [] covWMatrixIdMember rfl rfl rfl

def covWMatrix_id_partial_ty {n : Nat} {Γ : LCtx} {A : Expr Nat}
    (hA : HasTyT covWMatrixIdEnv n Γ A (.sort (.succ .zero))) :
    HasTyT covWMatrixIdEnv n Γ (.app covWMatrixId A) (.pi A (lift 0 1 A)) :=
  .app Γ covWMatrixId A (.sort (.succ .zero)) (.pi (.bvar 0) (.bvar 1))
    (covWMatrix_id_ty n Γ) hA

def covWMatrix_id_nat_zero_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWMatrixIdEnv n Γ
      (.app (.app covWMatrixId covWMatrixNat) (.const 1 [])) covWMatrixNat :=
  .app Γ _ _ covWMatrixNat covWMatrixNat
    (covWMatrix_id_partial_ty (covWMatrix_nat_ty n Γ)) (covWMatrix_zero_ty n Γ)

def covWMatrix_id_arrow_succ_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWMatrixIdEnv n Γ
      (.app (.app covWMatrixId covWMatrixArrow) (.const 2 [])) covWMatrixArrow :=
  .app Γ _ _ covWMatrixArrow covWMatrixArrow
    (covWMatrix_id_partial_ty (covWMatrix_arrow_ty n Γ)) (covWMatrix_succ_ty n Γ)

def covWMatrix_id_prop_false_ty (n : Nat) (Γ : LCtx) :
    HasTyT covWMatrixIdEnv n Γ
      (.app (.app covWMatrixId covWMatrixProp) covWMatrixFalse) covWMatrixProp :=
  .app Γ _ _ covWMatrixProp covWMatrixProp
    (covWMatrix_id_partial_ty (covWMatrix_prop_ty n Γ)) (covWMatrix_false_ty n Γ)

/-- A syntactically exposed declared prefix together with its actual native
typing. This measurement certificate includes the earlier native terms. -/
def CovWMatrixActualPosition (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (r : Nat) (ls : List Level) (xs : List (Expr Nat)) (D B : Expr Nat) : Prop :=
  ∃ m, E.members r = some m ∧ ls.length = m.arity ∧ levelsBounded n ls = true ∧
    applyTel xs (instantiateLevels ls m.mtype) = some (.pi D B) ∧
    Nonempty (HasTyT E n Γ (foldApps (.const r ls) xs) (.pi D B))

theorem covWMatrix_id_actual_position {n : Nat} {Γ : LCtx} {A : Expr Nat}
    (hA : HasTyT covWMatrixIdEnv n Γ A (.sort (.succ .zero))) :
    CovWMatrixActualPosition covWMatrixIdEnv n Γ 4 [] [A]
      A (lift 0 1 A) :=
  ⟨covWMatrixIdMember, rfl, rfl, rfl, rfl, ⟨covWMatrix_id_partial_ty hA⟩⟩

theorem covWMatrix_id_actual_domains (n : Nat) :
    CovWMatrixActualPosition covWMatrixIdEnv n [] 4 []
      [covWMatrixNat] covWMatrixNat covWMatrixNat ∧
    CovWMatrixActualPosition covWMatrixIdEnv n [] 4 []
      [covWMatrixArrow] covWMatrixArrow covWMatrixArrow ∧
    CovWMatrixActualPosition covWMatrixIdEnv n [] 4 []
      [covWMatrixProp] covWMatrixProp covWMatrixProp :=
  ⟨covWMatrix_id_actual_position (covWMatrix_nat_ty n []),
    covWMatrix_id_actual_position (covWMatrix_arrow_ty n []),
    covWMatrix_id_actual_position (covWMatrix_prop_ty n [])⟩

private theorem id_rigid : RigidConst covWMatrixIdEnv 4 := by
  intro m hm
  have he : m = covWMatrixIdMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

private theorem id_not_propCtor : ¬ PropCtorT covWMatrixIdEnv 4 := by
  rintro ⟨m, fam, fm, hm, hk, _⟩
  have he : m = covWMatrixIdMember := Option.some.inj hm.symm
  subst m
  cases hk

theorem covWMatrix_id_prefix_raw (n : Nat) (ρ : EnvWIrrel) (A : Expr Nat) :
    ApproxTWIrrel covWMatrixIdEnv n ρ (.app covWMatrixId A) covWMatrixIdPrefix :=
  covWIrrel_raw_appSpine_bot (.const ρ 4 [] id_rigid id_not_propCtor)

theorem covWMatrix_id_prefix_guarded (n : Nat) (Γ : LCtx)
    (ρ : EnvWIrrel) (A : Expr Nat) :
    ApproxTKWIrrel covWMatrixIdEnv n Γ ρ (.app covWMatrixId A) covWMatrixIdPrefix :=
  covWIrrel_guarded_appSpine_bot
    (.free (kFreeT_rigid_const id_rigid [])
      (.const ρ 4 [] id_rigid id_not_propCtor))

theorem covWMatrix_id_prefix_nonbottom : covWMatrixIdPrefix ≠ .bot :=
  fun h => CptWIrrel.noConfusion h

private def castTy {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e : Expr Nat} :
    {A B : Expr Nat} → TyConvT E n Γ A B → HasTyT E n Γ e A → HasTyT E n Γ e B
  | _, _, .refl _ _, ht => ht
  | _, _, .of _ A B u hc, ht => .conv Γ e A B u ht hc
  | _, _, .trans _ _ _ _ h₁ h₂, ht => castTy h₂ (castTy h₁ ht)

/-- A function domain is classified up to actual native type conversion. -/
def CovWMatrixFunctionDomain (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (D : Expr Nat) : Prop :=
  ∃ A B, Nonempty (TyConvT E n Γ D (.pi A B))

/-- Universe domains contain type arguments, including propositions at Sort 0. -/
def CovWMatrixTypeDomain (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (D : Expr Nat) : Prop :=
  ∃ l, Nonempty (TyConvT E n Γ D (.sort l))

theorem covWMatrix_arrow_function (n : Nat) :
    CovWMatrixFunctionDomain covWMatrixIdEnv n [] covWMatrixArrow :=
  ⟨covWMatrixNat, covWMatrixNat, ⟨.refl [] covWMatrixArrow⟩⟩

theorem covWMatrix_prop_type (n : Nat) :
    CovWMatrixTypeDomain covWMatrixIdEnv n [] covWMatrixProp :=
  ⟨.zero, ⟨.refl [] covWMatrixProp⟩⟩

theorem covWMatrix_prop_not_function (n : Nat) :
    ¬ CovWMatrixFunctionDomain covWMatrixIdEnv n [] covWMatrixProp := by
  rintro ⟨A, B, ⟨hc⟩⟩
  exact covWIrrel_native_not_sort_and_pi covWMatrixIdEnv_wf covWMatrixIdEnv_inScope
    .nil (covWMatrix_false_ty n []) (castTy hc (covWMatrix_false_ty n []))

theorem covWMatrix_arrow_not_type (n : Nat) :
    ¬ CovWMatrixTypeDomain covWMatrixIdEnv n [] covWMatrixArrow := by
  rintro ⟨l, ⟨hc⟩⟩
  exact covWIrrel_native_not_sort_and_pi covWMatrixIdEnv_wf covWMatrixIdEnv_inScope
    .nil (castTy hc (covWMatrix_succ_ty n [])) (covWMatrix_succ_ty n [])

/-- No Prop-valued function classifier of the compact alone can classify
both actual typed prefixes. This does not assume classifier decidability. -/
theorem covWMatrix_no_compact_function_classifier (n : Nat) :
    ¬ ∃ classify : CptWIrrel → Prop,
      ∀ (A : Expr Nat) (c : CptWIrrel),
        Nonempty (HasTyT covWMatrixIdEnv n [] A (.sort (.succ .zero))) →
        ApproxTKWIrrel covWMatrixIdEnv n [] EnvWIrrel.bot (.app covWMatrixId A) c →
        c ≠ .bot → (classify c ↔ CovWMatrixFunctionDomain covWMatrixIdEnv n [] A) := by
  rintro ⟨classify, hc⟩
  have ha := hc covWMatrixArrow covWMatrixIdPrefix ⟨covWMatrix_arrow_ty n []⟩
    (covWMatrix_id_prefix_guarded n [] EnvWIrrel.bot covWMatrixArrow)
    covWMatrix_id_prefix_nonbottom
  have hp := hc covWMatrixProp covWMatrixIdPrefix ⟨covWMatrix_prop_ty n []⟩
    (covWMatrix_id_prefix_guarded n [] EnvWIrrel.bot covWMatrixProp)
    covWMatrix_id_prefix_nonbottom
  exact covWMatrix_prop_not_function n (hp.mp (ha.mpr (covWMatrix_arrow_function n)))

theorem covWMatrix_no_compact_type_classifier (n : Nat) :
    ¬ ∃ classify : CptWIrrel → Prop,
      ∀ (A : Expr Nat) (c : CptWIrrel),
        Nonempty (HasTyT covWMatrixIdEnv n [] A (.sort (.succ .zero))) →
        ApproxTKWIrrel covWMatrixIdEnv n [] EnvWIrrel.bot (.app covWMatrixId A) c →
        c ≠ .bot → (classify c ↔ CovWMatrixTypeDomain covWMatrixIdEnv n [] A) := by
  rintro ⟨classify, hc⟩
  have ha := hc covWMatrixArrow covWMatrixIdPrefix ⟨covWMatrix_arrow_ty n []⟩
    (covWMatrix_id_prefix_guarded n [] EnvWIrrel.bot covWMatrixArrow)
    covWMatrix_id_prefix_nonbottom
  have hp := hc covWMatrixProp covWMatrixIdPrefix ⟨covWMatrix_prop_ty n []⟩
    (covWMatrix_id_prefix_guarded n [] EnvWIrrel.bot covWMatrixProp)
    covWMatrix_id_prefix_nonbottom
  exact covWMatrix_arrow_not_type n (ha.mp (hp.mpr (covWMatrix_prop_type n)))

theorem covWMatrix_no_compact_domain_decoder (n : Nat) :
    ¬ ∃ decode : CptWIrrel → Expr Nat,
      ∀ (A : Expr Nat) (c : CptWIrrel),
        Nonempty (HasTyT covWMatrixIdEnv n [] A (.sort (.succ .zero))) →
        ApproxTKWIrrel covWMatrixIdEnv n [] EnvWIrrel.bot (.app covWMatrixId A) c →
        c ≠ .bot → decode c = A := by
  rintro ⟨decode, hc⟩
  have hn := hc covWMatrixNat covWMatrixIdPrefix ⟨covWMatrix_nat_ty n []⟩
    (covWMatrix_id_prefix_guarded n [] EnvWIrrel.bot covWMatrixNat)
    covWMatrix_id_prefix_nonbottom
  have ha := hc covWMatrixArrow covWMatrixIdPrefix ⟨covWMatrix_arrow_ty n []⟩
    (covWMatrix_id_prefix_guarded n [] EnvWIrrel.bot covWMatrixArrow)
    covWMatrix_id_prefix_nonbottom
  exact Expr.noConfusion (hn.symm.trans ha)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_POSITIONS_ROOTS
#print axioms covWMatrixIdType
#print axioms covWMatrixIdMember
#print axioms covWMatrixIdEnv
#print axioms covWMatrixIdEnv_wf
#print axioms covWMatrixIdEnv_inScope
#print axioms covWMatrixId
#print axioms covWMatrixNat
#print axioms covWMatrixArrow
#print axioms covWMatrixProp
#print axioms covWMatrixFalse
#print axioms covWMatrixIdPrefix
#print axioms covWMatrix_nat_ty
#print axioms covWMatrix_arrow_ty
#print axioms covWMatrix_prop_ty
#print axioms covWMatrix_false_ty
#print axioms covWMatrix_zero_ty
#print axioms covWMatrix_succ_ty
#print axioms covWMatrix_id_ty
#print axioms covWMatrix_id_partial_ty
#print axioms covWMatrix_id_nat_zero_ty
#print axioms covWMatrix_id_arrow_succ_ty
#print axioms covWMatrix_id_prop_false_ty
#print axioms CovWMatrixActualPosition
#print axioms covWMatrix_id_actual_position
#print axioms covWMatrix_id_actual_domains
#print axioms covWMatrix_id_prefix_raw
#print axioms covWMatrix_id_prefix_guarded
#print axioms covWMatrix_id_prefix_nonbottom
#print axioms CovWMatrixFunctionDomain
#print axioms CovWMatrixTypeDomain
#print axioms covWMatrix_arrow_function
#print axioms covWMatrix_prop_type
#print axioms covWMatrix_prop_not_function
#print axioms covWMatrix_arrow_not_type
#print axioms covWMatrix_no_compact_function_classifier
#print axioms covWMatrix_no_compact_type_classifier
#print axioms covWMatrix_no_compact_domain_decoder
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_MATRIX_POSITIONS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWMatrixAudit
