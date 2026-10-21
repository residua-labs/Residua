import rcic.RcicNativeTypedModelCovSProofControls
import rcic.RcicNativeTypedModelKIndexFree

/-!
# The constructor-projection observation boundary

`projFields` is encoded by the admitted proposition recursor.  Native
projection returns the actual proof field.  The old compact model instead
feeds bottom to proposition-recursion fields, and a projection minor cannot
recover a non-bottom proof observation.  A body-free native proof supplies
that missing observation on the right of the proposed equivalence.

Every environment, native typing, and observation used below is supplied.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovUAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit TypedModelKAudit
open TypedModelKFragmentAudit ReadbackCKAudit ReadbackCK2Audit

def covUProjPMember : CheckedMember := ⟨.axiomM, 0, .sort .zero, none⟩
def covUProjPEnv : ResolvedEnv := extendEnv andEnvU 3 covUProjPMember
def covUProjProofMember : CheckedMember := ⟨.axiomM, 0, .const 3 [], none⟩
def covUProjEnv : ResolvedEnv := extendEnv covUProjPEnv 4 covUProjProofMember

def covUProjPEnvWfT : EnvWfT covUProjPEnv :=
  .axiom andEnvU 3 (.sort .zero) (.succ .zero) andEnvUWfT rfl
    (.sort [] .zero) (fun _ => rfl) rfl

def covUProjEnvWfT : EnvWfT covUProjEnv :=
  .axiom covUProjPEnv 4 (.const 3 []) .zero covUProjPEnvWfT rfl
    (.const [] 3 [] covUProjPMember rfl rfl rfl) (fun _ => rfl) rfl

abbrev covUProjP : Expr Nat := .const 3 []
abbrev covUProjProof : Expr Nat := .const 4 []
abbrev covUProjPairType : Expr Nat := andApp covUProjP covUProjP
def covUProjPair : Expr Nat :=
  foldApps (.const 1 []) [covUProjP, covUProjP, covUProjProof, covUProjProof]
def covUProjMotive : Expr Nat := .lam covUProjPairType covUProjP
def covUProjMinor : Expr Nat := .lam covUProjP (.lam covUProjP (.bvar 1))
def covUProjTerm : Expr Nat :=
  recCall (.const 2 [.zero])
    [covUProjP, covUProjP, covUProjMotive, covUProjMinor] covUProjPair

def covUProjP_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUProjEnv n Γ covUProjP (.sort .zero) :=
  .const Γ 3 [] covUProjPMember rfl rfl rfl

def covUProjProof_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUProjEnv n Γ covUProjProof covUProjP :=
  .const Γ 4 [] covUProjProofMember rfl rfl rfl

def covUProjPairType_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUProjEnv n Γ covUProjPairType (.sort .zero) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (.const Γ 0 [] andFamMember rfl rfl rfl) (covUProjP_ty n Γ))
    (covUProjP_ty n Γ)

def covUProjPair_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUProjEnv n Γ covUProjPair covUProjPairType :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _ (.const Γ 1 [] andIntroMember rfl rfl rfl)
          (covUProjP_ty n Γ)) (covUProjP_ty n Γ))
      (covUProjProof_ty n Γ)) (covUProjProof_ty n Γ)

theorem covUProj_P_rigid : RigidConst covUProjEnv 3 := by
  intro m hm
  have he : m = covUProjPMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

theorem covUProj_proof_rigid : RigidConst covUProjEnv 4 := by
  intro m hm
  have he : m = covUProjProofMember := Option.some.inj hm.symm
  subst m
  exact ⟨Or.inl rfl, by decide⟩

theorem covUProj_proof_not_propCtor : ¬ PropCtorT covUProjEnv 4 := by
  rintro ⟨m, fam, fm, hm, hctor, _⟩
  have he : m = covUProjProofMember := Option.some.inj hm.symm
  subst m
  exact MemberClass.noConfusion hctor

theorem covUProj_proof_observed (n : Nat) (Γ : LCtx) (ρ : EnvT) :
    ApproxTK covUProjEnv n Γ ρ covUProjProof (.spine 4 []) :=
  .free (kFreeT_rigid_const covUProj_proof_rigid [])
    (.const ρ 4 [] covUProj_proof_rigid covUProj_proof_not_propCtor)

theorem covUProj_P_observation_positive {ρ : EnvT} {c : CptT}
    (h : ApproxT covUProjEnv ρ covUProjP c) : IsPropCT covUProjEnv c := by
  rcases approxT_rigid_const_inv covUProj_P_rigid h with rfl | rfl
  · exact .bot
  · exact .spine (m := covUProjPMember) rfl rfl

theorem covUProj_minor_bot {ρ : EnvT} {c : CptT}
    (h : ApproxT covUProjEnv ρ covUProjMinor c) : c = .bot := by
  rcases approxT_lam_inv h with hbot | ⟨a, g, rfl, ha, hne, hg⟩
  · exact hbot
  · obtain ⟨s, hs, hnb⟩ := hne
    have hdem : ∀ u ∈ s.1, u = .bot :=
      fun u hu => ctyS_prop_bot (covUProj_P_observation_positive ha) ((hg s hs).1 u hu)
    rcases approxT_lam_inv (hg s hs).2 with hbot | ⟨b, g', he, _, hne', hg'⟩
    · exact (hnb hbot).elim
    · obtain ⟨t, ht, hnb'⟩ := hne'
      have hb := approxT_bvar_inv (hg' t ht).2
      have hb' : t.2 = .bot ∨ t.2 ∈ s.1 := hb
      rcases hb' with hb | hb
      · exact (hnb' hb).elim
      · exact (hnb' (hdem _ hb)).elim

theorem covUProj_app_bot_of_function_bot {E : ResolvedEnv} {ρ : EnvT}
    {f a : Expr Nat} (hf : ∀ c, ApproxT E ρ f c → c = .bot)
    {c : CptT} (h : ApproxT E ρ (.app f a) c) : c = .bot := by
  rcases approxT_app_inv h with hb | ⟨g, s, _, hfg, _⟩ | ⟨r, args, u, _, hfr, _⟩
  · exact hb
  · exact CptT.noConfusion (hf _ hfg)
  · exact CptT.noConfusion (hf _ hfr)

private theorem covUProj_and_sub : ∀ r m, andEnvU.members r = some m →
    covUProjEnv.members r = some m := by
  intro r m hm
  rcases andEnvU_mem hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem covUProj_rec_schema (w : IotaWitnessS covUProjEnv) (hr : w.recRef = 2) :
    PropFamilyS w ∧ w.preMajor.length = 4 ∧ w.fields.length = 2 ∧
      w.schema = .app (.app (.bvar 2) (.bvar 1)) (.bvar 0) := by
  have hm : w.recMember = andRecMemberU := by
    have hh := w.hrec
    rw [hr] at hh
    exact (Option.some.inj hh).symm
  have hd := IotaWitnessS.recData_admitted andGroupAdmitted covUProj_and_sub w hr hm
  change w.familyRef = 0 ∧ w.famMember = andFamMember ∧
    w.nparams = 2 ∧ w.nindices = 0 ∧ w.nMinors = 1 at hd
  obtain ⟨hf, hfm, hnp, hni, hnm⟩ := hd
  have hci : w.ctorIdx = 0 := by have hh := w.hidx; rw [hnm] at hh; omega
  have hcr : w.ctorRef = 1 := by rw [w.hctorIdx, hf, hci]
  have hcm : w.ctorMember = andIntroMember := by
    have hh := w.hctor
    rw [hcr] at hh
    exact (Option.some.inj hh).symm
  have hfl : w.fields.length = 2 := by
    have hh := w.hnpar
    rw [hnp, hcm] at hh
    change 2 + w.fields.length = 4 at hh
    omega
  have hpeel := w.hpeel
  rw [hnp, hfl, hcm] at hpeel
  have hp : ([.sort .zero, .sort .zero, .bvar 1, .bvar 1],
      andApp (.bvar 3) (.bvar 2)) = (w.ctorDoms, w.ctorResult) := Option.some.inj hpeel
  have hds : w.ctorDoms = [.sort .zero, .sort .zero, .bvar 1, .bvar 1] :=
    (congrArg Prod.fst hp).symm
  have hres : w.ctorResult = andApp (.bvar 3) (.bvar 2) :=
    (congrArg Prod.snd hp).symm
  have hsh := w.hshapes
  rw [hf, hfm, hnp, hni, hds] at hsh
  have hshapes : w.shapes = [.nonrecursive, .nonrecursive] :=
    fieldShapesFuel_agree covUProjEnv hsh
      (show fieldShapesFuel covUProjEnv 8 0 andFamMember.arity 2 0 2
        ([.sort .zero, .sort .zero, .bvar 1, .bvar 1].drop 2) =
          some [.nonrecursive, .nonrecursive] from rfl)
  have hsc := w.hschema
  rw [hr, hm, hfl, hni, hnm, hci, hnp, hds, hres, hshapes] at hsc
  have hschema : w.schema = .app (.app (.bvar 2) (.bvar 1)) (.bvar 0) :=
    iotaOpenRhs_agree covUProjEnv (fuel₂ := 8) hsc (by rfl)
  refine ⟨?_, ?_, hfl, hschema⟩
  · change piBody w.famMember.mtype = .sort .zero
    rw [hfm]
    rfl
  · rw [w.hpre, hnp, hni, hnm]

private theorem covUProj_four_demands (us : List (List CptT)) (h : us.length = 4) :
    ∃ u0 u1 u2 u3, us = [u0, u1, u2, u3] := by
  rcases us with _ | ⟨u0, _ | ⟨u1, _ | ⟨u2, _ | ⟨u3, us⟩⟩⟩⟩
  · cases h
  · cases h
  · cases h
  · cases h
  · have hz : us.length = 0 := by simp only [List.length_cons] at h; omega
    obtain rfl := List.eq_nil_of_length_eq_zero hz
    exact ⟨u0, u1, u2, u3, rfl⟩

theorem covUProj_term_bot {ρ : EnvT} {c : CptT}
    (h : ApproxT covUProjEnv ρ covUProjTerm c) : c = .bot := by
  obtain ⟨d, hd, hfold⟩ := (approxT_foldApps_iff covUProjEnv ρ (.const 2 [.zero])
    [covUProjP, covUProjP, covUProjMotive, covUProjMinor, covUProjPair] c).mp h
  rcases approxT_propRec_inv
      (fun hr => (hr _ (rfl : covUProjEnv.members 2 = some andRecMemberU)).2 rfl)
      (fun m body hδ => by
        obtain ⟨hm, _, hnrec, _⟩ := hδ
        have hem : andRecMemberU = m := Option.some.inj hm
        exact hnrec (hem ▸ (rfl : andRecMemberU.mclass = .recursorM)))
      (fun w hw => (covUProj_rec_schema w hw).1) hd with
      rfl | ⟨w, us, c0, hw, hlen, hschema, rfl⟩
  · exact foldAppCptT_bot_inv hfold
  · obtain ⟨_, hpre, hfl, hschemaEq⟩ := covUProj_rec_schema w hw
    obtain ⟨u0, u1, u2, u3, rfl⟩ := covUProj_four_demands us (hlen.trans hpre)
    rcases (foldAppCptT_curryStepT_iff (show
      ([u0, u1, u2, u3] ++ [[]]).length =
        [covUProjP, covUProjP, covUProjMotive, covUProjMinor, covUProjPair].length from rfl)).mp
        hfold with hb | ⟨hargs, he⟩
    · exact hb
    · have hu3 : ∀ u ∈ u3, u = .bot := by
        cases hargs with
        | cons _ hargs =>
          cases hargs with
          | cons _ hargs =>
            cases hargs with
            | cons _ hargs =>
              cases hargs with
              | cons hminor _ => exact fun u hu => covUProj_minor_bot (hminor u hu)
      have hfields : w.fields.map (fun _ => ([] : List CptT)) = [[], []] := by
        rw [List.map_const', hfl]
        rfl
      rw [hschemaEq, hfields] at hschema
      have hbvar : ∀ b, ApproxT covUProjEnv
          (EnvT.pushArgs (([u0, u1, u2, u3] ++ [[], []]).map demandT) EnvT.bot)
          (.bvar 2) b → b = .bot := by
        intro b hb
        have hh : b = .bot ∨ b ∈ u3 := approxT_bvar_inv hb
        exact hh.elim id (hu3 b)
      rw [he]
      exact covUProj_app_bot_of_function_bot
        (fun b hb => covUProj_app_bot_of_function_bot hbvar hb) hschema

theorem covUProj_term_only_bottom (n : Nat) (Γ : LCtx) (ρ : EnvT) (c : CptT) :
    ApproxTK covUProjEnv n Γ ρ covUProjTerm c ↔ c = .bot :=
  ⟨fun h => covUProj_term_bot (approxTK_forget h), fun h => h ▸ .bot _ _ _⟩

def covUProjMotive_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUProjEnv n Γ covUProjMotive (.pi covUProjPairType (.sort .zero)) :=
  .lam Γ covUProjPairType .zero covUProjP (.sort .zero)
    (covUProjPairType_ty n Γ) (covUProjP_ty n _)

private def covUProjPairTel : Expr Nat :=
  foldApps (.const 1 []) [covUProjP, covUProjP, .bvar 1, .bvar 0]

private def covUProjPairTel_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUProjEnv n (.assumption covUProjP :: .assumption covUProjP :: Γ)
      covUProjPairTel covUProjPairType :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.const (.assumption covUProjP :: .assumption covUProjP :: Γ)
            1 [] andIntroMember rfl rfl rfl)
          (covUProjP_ty n _)) (covUProjP_ty n _))
      (.bvar _ 1 _ rfl)) (.bvar _ 0 _ rfl)

def covUProjMinor_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUProjEnv n Γ covUProjMinor
      (.pi covUProjP (.pi covUProjP (.app covUProjMotive covUProjPairTel))) :=
  .lam _ _ .zero _ _ (covUProjP_ty n _)
    (.lam _ _ .zero _ _ (covUProjP_ty n _)
      (.conv _ _ covUProjP _ .zero (.bvar _ 1 _ rfl)
        (.symm _ _ _ _ (.beta _ _ _ _ _ .zero
          (covUProjPairType_ty n _) (covUProjP_ty n _) (covUProjPairTel_ty n Γ)))))

def covUProjTerm_ty (n : Nat) (Γ : LCtx) :
    HasTyT covUProjEnv n Γ covUProjTerm covUProjP :=
  .conv _ _ (.app covUProjMotive covUProjPair) covUProjP .zero
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.app _ _ _ _ _
            (.app _ _ _ _ _ (.const Γ 2 [.zero] andRecMemberU rfl rfl rfl)
              (covUProjP_ty n Γ)) (covUProjP_ty n Γ))
          (covUProjMotive_ty n Γ)) (covUProjMinor_ty n Γ)) (covUProjPair_ty n Γ))
    (.beta _ _ _ _ _ .zero (covUProjPairType_ty n Γ)
      (covUProjP_ty n _) (covUProjPair_ty n Γ))

/-- The actual fieldful proposition-singleton witness: no placeholder or
untyped descriptor is used to identify the projection. -/
def covUProjW : IotaWitness covUProjEnv where
  recRef := 2
  ctorRef := 1
  ls := [.zero]
  lsC := []
  recMember := andRecMemberU
  ctorMember := andIntroMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [covUProjP, covUProjP, covUProjMotive, covUProjMinor]
  fields := [covUProjProof, covUProjProof]
  ctorParams := [covUProjP, covUProjP]
  kinds := [.plain, .plain]
  minor := covUProjMinor
  hlen := rfl
  familyRef := 0
  famMember := andFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 2
  nindices := 0
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.sort .zero, .sort .zero, .bvar 1, .bvar 1]
  ctorResult := andApp (.bvar 3) (.bvar 2)
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.sort .zero, .sort .zero, andMotTy, andMinorTy,
    andApp (.bvar 3) (.bvar 2)]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := by decide
  hctorClosed := by decide
  hlsLen := rfl
  ctorAfterParams := .pi covUProjP (.pi covUProjP covUProjPairType)
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

theorem covUProj_is_projection :
    KFieldW covUProjW ∧ revealedPos? covUProjW 0 = none ∧
      (projFields covUProjW (ctorMajor covUProjW)).getD 0 (.sort .zero) =
        covUProjTerm ∧
      covUProjW.fields.getD 0 (.sort .zero) = covUProjProof :=
  ⟨⟨by decide, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem covUProj_native_readback (n : Nat) (Γ : LCtx) :
    RedR (WhStepCK2 covUProjEnv n) Γ covUProjTerm covUProjProof :=
  .step (.ctx (.iota (.ofU covUProjW)))
    (.step (.ctx (.appHead (.beta _ _ _)))
      (.step (.ctx (.beta _ _ _)) (.refl _)))

/-- The requested equivalence is false even for a closed, natively typed
projection in an admitted environment, with its constructor major and field
typings supplied.  The failing direction is field-to-projection. -/
theorem covU_proj_ctor_observation_boundary (n : Nat) :
    Nonempty (EnvWfT covUProjEnv) ∧
    Nonempty (CtxWfT covUProjEnv n []) ∧
    Nonempty (HasTyT covUProjEnv n [] covUProjP (.sort .zero)) ∧
    Nonempty (HasTyT covUProjEnv n [] covUProjProof covUProjP) ∧
    Nonempty (HasTyT covUProjEnv n [] covUProjPair covUProjPairType) ∧
    Nonempty (HasTyT covUProjEnv n [] covUProjTerm covUProjP) ∧
    0 < covUProjW.fields.length ∧
    KFieldW covUProjW ∧
    revealedPos? covUProjW 0 = none ∧
    (projFields covUProjW (ctorMajor covUProjW)).getD 0 (.sort .zero) = covUProjTerm ∧
    covUProjW.fields.getD 0 (.sort .zero) = covUProjProof ∧
    RedR (WhStepCK2 covUProjEnv n) [] covUProjTerm covUProjProof ∧
    ApproxTK covUProjEnv n [] EnvT.bot covUProjTerm .bot ∧
    ApproxTK covUProjEnv n [] EnvT.bot covUProjProof (.spine 4 []) ∧
    (.spine 4 [] : CptT) ≠ .bot ∧
    ¬ (∀ c, ApproxTK covUProjEnv n [] EnvT.bot covUProjTerm c ↔
      ApproxTK covUProjEnv n [] EnvT.bot covUProjProof c) := by
  refine ⟨⟨covUProjEnvWfT⟩, ⟨.nil⟩, ⟨covUProjP_ty n []⟩,
    ⟨covUProjProof_ty n []⟩, ⟨covUProjPair_ty n []⟩, ⟨covUProjTerm_ty n []⟩,
    (by decide), covUProj_is_projection.1, covUProj_is_projection.2.1,
    covUProj_is_projection.2.2.1, covUProj_is_projection.2.2.2,
    covUProj_native_readback n [], .bot _ _ _, covUProj_proof_observed n [] EnvT.bot,
    (by intro he; cases he), ?_⟩
  intro h
  have hh := (h (.spine 4 [])).mpr (covUProj_proof_observed n [] EnvT.bot)
  exact CptT.noConfusion (covUProj_term_bot (approxTK_forget hh))

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_U_PROJECTION_ROOTS
#print axioms covUProjPMember
#print axioms covUProjPEnv
#print axioms covUProjProofMember
#print axioms covUProjEnv
#print axioms covUProjPEnvWfT
#print axioms covUProjEnvWfT
#print axioms covUProjP
#print axioms covUProjProof
#print axioms covUProjPairType
#print axioms covUProjPair
#print axioms covUProjMotive
#print axioms covUProjMinor
#print axioms covUProjTerm
#print axioms covUProjP_ty
#print axioms covUProjProof_ty
#print axioms covUProjPairType_ty
#print axioms covUProjPair_ty
#print axioms covUProj_P_rigid
#print axioms covUProj_proof_rigid
#print axioms covUProj_proof_not_propCtor
#print axioms covUProj_proof_observed
#print axioms covUProj_P_observation_positive
#print axioms covUProj_minor_bot
#print axioms covUProj_app_bot_of_function_bot
#print axioms covUProj_rec_schema
#print axioms covUProj_term_bot
#print axioms covUProj_term_only_bottom
#print axioms covUProjMotive_ty
#print axioms covUProjMinor_ty
#print axioms covUProjTerm_ty
#print axioms covUProjW
#print axioms covUProj_is_projection
#print axioms covUProj_native_readback
#print axioms covU_proj_ctor_observation_boundary
-- END RCIC_NATIVE_TYPED_MODEL_COV_U_PROJECTION_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovUAudit
