import rcic.RcicF3IndexedBranchFields
import rcic.RcicF3IndexedPropEvalValue
import rcic.RcicF3IndexedPropCtor
import rcic.RcicF3PiRawIHAnyAttack
import rcic.RcicF3AIndexedPropContract

/-!
# Actual inhabited depth-three Branch evaluation and generated IH

The source constructs the actual motive and minor in the installed Branch
table, invokes the indexed candidate and constructor producers, and uses
the generated recursive packet on the same original field tuple.

The root index is trueCode; a selected child has falseCode as its index.
The fixed parameter is falseCode and remains in both complete keys. The
ordinary constructor field is trueCode and is retained as data. The
recursive proof field is pempty, with membership supplied by the Branch
field construction and produced candidate closure.

The motive is a constant singleton data type at the complete valuation
sigmaOf [1]. Its actual typed endpoint also produces evaluation
functionality, without a key-coherence premise.

This synthetic fixture supplies no imported Acc instance, modern iota,
original D acceptance, or whole-tier closure.
scope_closure_claim = 0. closure_claim = 0.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000


namespace Rcic.F3.PSet.IndexedBranchEvalAttack

open Rcic.Declarative PiIndex RawFamily PropEval
open PropEvalSafeIndex (falseCode trueCode)
open PiRawIHAnyAttack (datum domain domain_dich type_mem)

noncomputable abbrev fd : FamData := IndexedBranchFields.fd
noncomputable abbrev sigma : Nat → Nat := σOf [1]
noncomputable abbrev bound : Nat → Nat := fun _ => 1

noncomputable def mu (P : Premises4) : Nat → List Nat → PSet.{4} :=
  IndexedBranchFixture.table P

noncomputable abbrev model (P : Premises4) : Interp.{4} := mkM P (mu P)

theorem ctorClasses :
    ∀ c ∈ [(1, IndexedBranchFixture.introMember)],
      c.2.mclass = .constructorM := by
  intro c hc
  cases List.mem_singleton.mp hc
  rfl

noncomputable def plan : EvalPlan.Plan := EvalPlan.ofNode IndexedBranchFixture.node

private theorem groupRecNode_eta
    {Ebase : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (hlay : FamilyLayout Ebase) (hrmK : rm.mclass = .recursorM)
    {S E E' : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E ms E')
    (hl : ∀ c, c ∈ ms → c.1 = f ∨ c.2.mclass ≠ .inductiveM)
    (hinv : GroupWalkInv Ebase E f)
    (hsub : ∀ r m, Ebase.members r = some m → E.members r = some m)
    (huniq : ∀ c, c ∈ ms → c.2.mclass = .recursorM → c.1 = rr ∧ c.2 = rm)
    (hin : (rr, rm) ∈ ms) :
    groupRecNode hlay hrmK hmem hl hinv hsub huniq hin =
      groupRecNode hlay hrmK hmem hl hinv hsub
        (fun c hc hk => ⟨(huniq c hc hk).1, (huniq c hc hk).2⟩) hin := rfl

private theorem canonical_node :
    (groupNode (.empty : EnvWfT emptyEnv)
      (f := 0) (fm := IndexedBranchFixture.famMember)
      (ctors := [(1, IndexedBranchFixture.introMember)])
      (rr := 2) (rm := IndexedBranchFixture.recMember)
      rfl ctorClasses rfl IndexedBranchFixture.membersT).val =
        IndexedBranchFixture.node := by
  unfold groupNode
  rw [groupRecNode_eta]
  with_unfolding_all rfl

theorem canonical_plan :
    EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
      (f := 0) (fm := IndexedBranchFixture.famMember)
      (ctors := [(1, IndexedBranchFixture.introMember)])
      (rr := 2) (rm := IndexedBranchFixture.recMember)
      rfl ctorClasses rfl IndexedBranchFixture.membersT = plan :=
  congrArg (fun nd : IndexedBranchFixture.Node => EvalPlan.ofNode nd)
    canonical_node

private theorem group_prop :
    UniformProp
      (EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
        (f := 0) (fm := IndexedBranchFixture.famMember)
        (ctors := [(1, IndexedBranchFixture.introMember)])
        (rr := 2) (rm := IndexedBranchFixture.recMember)
        rfl ctorClasses rfl IndexedBranchFixture.membersT).node.a.family.resultLevel := by
  rw [canonical_plan]
  exact fun _ => rfl

noncomputable def motive (P : Premises4) : PSet.{4} :=
  piLam (model P) sigma (fun _ => tyv domain)
    (push [falseCode] ρ0) IndexedBranchFixture.motiveTy

noncomputable def start (P : Premises4) : Nat → PSet.{4} :=
  vcons (motive P) (push [falseCode] ρ0)

noncomputable def minor (P : Premises4) : PSet.{4} :=
  piLam (model P) sigma (fun _ => datum)
    (start P) IndexedBranchFixture.minorTy

noncomputable def C (P : Premises4) : Context where
  E := emptyEnv
  E' := IndexedBranchFixture.env
  f := 0
  rr := 2
  rm := IndexedBranchFixture.recMember
  node := IndexedBranchFixture.node
  M := model P
  σ := sigma
  parameters := [falseCode]
  motive := motive P
  minors := [minor P]
  minor_length := rfl

noncomputable def N (P : Premises4) : Frame := NormPropEval.base P (mu P) (C P)
noncomputable def X (P : Premises4) : Frame := NormPropEval.candidate P (mu P) (C P)

noncomputable def rootKey : Index.{4} := key [falseCode, trueCode]
noncomputable def childKey : Index.{4} := key [falseCode, falseCode]
noncomputable def selected : List PSet.{4} := [falseCode, pempty, pempty]

noncomputable def beforeField (P : Premises4) : Nat → PSet.{4} :=
  vcons trueCode (start P)

noncomputable def atField (P : Premises4) : Nat → PSet.{4} :=
  vcons pempty (beforeField P)

theorem family_equation (P : Premises4) :
    ∀ vs, Equiv (mu P 0 vs) (ofFrame P (mu P) fd (N P) vs) := by
  have h := PointwisePropPrefix.family_equation_of_group P
    (PointwiseRole.arities IndexedBranchFixture.env) (mu P)
    (f := 0) (fm := IndexedBranchFixture.famMember)
    (ctors := [(1, IndexedBranchFixture.introMember)])
    (rr := 2) (rm := IndexedBranchFixture.recMember)
    .empty rfl ctorClasses rfl IndexedBranchFixture.membersT
    (NormRole.envCtx IndexedBranchFixture.envWfT)
    (EvalRole.envPlan IndexedBranchFixture.envWfT)
    (fun _ _ => rfl) (IndexedBranchFixture.table_faithful P) group_prop
  dsimp only at h
  rw [canonical_plan] at h
  exact h

theorem normalized_closed (P : Premises4) :
    Admissible (EvalPlanNormal.fd plan) (N P) ∧
      Closed P (mu P) (EvalPlanNormal.fd plan) (N P) :=
  EvalPlanNormalProp.normalized_closed P (mu P) plan
    IndexedBranchFixture.famMember [(1, IndexedBranchFixture.introMember)]
    .empty IndexedBranchFixture.membersT sigma rfl rfl

private theorem family_free :
    ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false := by
  intro e he
  change e ∈ [(.sort .zero : Expr Nat), .sort .zero] at he
  rcases List.mem_cons.mp he with rfl | he
  · rfl
  · cases List.mem_singleton.mp he
    rfl

private theorem raw_bounded : FamBounded fd 0 := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro e he
    cases List.mem_singleton.mp he
    rfl
  · intro e he
    cases List.mem_singleton.mp he
    rfl
  · intro c hc
    change c ∈ [([Expr.sort .zero, IndexedBranchFixture.field], [Expr.bvar 1])] at hc
    cases List.mem_singleton.mp hc
    constructor
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rfl
      · cases List.mem_singleton.mp he
        rfl
    · intro e he
      cases List.mem_singleton.mp he
      rfl

/-- The reader prefix has no transparent definition bodies, in any model. -/
private theorem prefix_bodies (M : Interp.{4}) (tau : Nat → Nat) :
    DeltaNormalize.BodyEquations M IndexedBranchFixture.groupPrefix tau := by
  intro r ls b hb rho
  have hn : transparentBody IndexedBranchFixture.groupPrefix r ls = none := by
    cases r with
    | zero => rfl
    | succ r =>
        cases r with
        | zero => rfl
        | succ r => rfl
  rw [hn] at hb
  cases hb

theorem normalize_ctor (P : Premises4) (Y : Frame) :
    ∀ vs i z, CtorAt P (mu P) fd Y vs i z →
      CtorAt P (mu P) (EvalPlanNormal.fd plan) Y vs i z :=
  EvalPlanNormal.ctorAt_of_bodyEquations P (mu P) plan Y
    (fun tau => prefix_bodies _ tau)

theorem raw_closed (P : Premises4) (Y : Frame)
    (hc : Closed P (mu P) (EvalPlanNormal.fd plan) Y) :
    Closed P (mu P) fd Y :=
  fun vs i z hz => hc vs i z (normalize_ctor P Y vs i z hz)

theorem constructor_sound (P : Premises4) :
    MemberSound P (mu P) bound 1 IndexedBranchFixture.introMember := by
  let cp := EvalPlan.ofGroup (.empty : EnvWfT emptyEnv)
    (f := 0) (fm := IndexedBranchFixture.famMember)
    (ctors := [(1, IndexedBranchFixture.introMember)])
    (rr := 2) (rm := IndexedBranchFixture.recMember)
    rfl ctorClasses rfl IndexedBranchFixture.membersT
  have hc : cp.node.a.constructors.length = 1 :=
    node_ctors_length (ctors := [(1, IndexedBranchFixture.introMember)]) cp.node rfl
  let j : Fin cp.node.a.constructors.length := ⟨0, by rw [hc]; decide⟩
  have h := IndexedPropCtor.member_sound P (mu P) bound
    (f := 0) (fm := IndexedBranchFixture.famMember)
    (ctors := [(1, IndexedBranchFixture.introMember)])
    (rr := 2) (rm := IndexedBranchFixture.recMember)
    .empty rfl ctorClasses rfl IndexedBranchFixture.membersT
    (IndexedBranchFixture.indexed_bound bound) (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities IndexedBranchFixture.env)
    (PointwiseRole.arities_agree IndexedBranchFixture.env)
    (NormRole.envCtx IndexedBranchFixture.envWfT)
    (EvalRole.envPlan IndexedBranchFixture.envWfT)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (IndexedBranchFixture.table_faithful P) group_prop j
  change MemberSound P (mu P) bound 1 (cp.node.a.constructors[j.val]) at h
  rw [(IndexedBranchFixture.constructor_info cp.node j).1] at h
  exact h

theorem parameter_mem (P : Premises4) :
    falseCode ∈ Ed (model P) (tyv (U W4 0)) :=
  IndexedBranchDomain.false_mem_sort P (mu P) sigma ρ0

theorem motive_mem (P : Premises4) :
    motive P ∈ Ed (model P)
      (den (model P) sigma (push [falseCode] ρ0) IndexedBranchFixture.motiveTy) := by
  refine piLam_mem (model P) sigma (envResp_const _)
    IndexedBranchFixture.motiveTy (push [falseCode] ρ0) ?_
  intro x hx h hh
  exact mem_congr_right (ed_tyv (model P) (U4_dich 1)).symm (type_mem P)

theorem motive_apply (P : Premises4) (x h : PSet.{4})
    (hx : x ∈ Ed (model P) (tyv (U W4 0)))
    (hh : h ∈ Ed (model P) (fapps (mu P 0 []) [falseCode, x])) :
    Equiv (fapps (motive P) [x, h]) (tyv domain) :=
  fapps_piLam (model P) sigma (envResp_const _) (.sort (.param 0))
    [.sort .zero, IndexedBranchFixture.famApp (.bvar 1) (.bvar 0)]
    (push [falseCode] ρ0) [x, h] ⟨hx, hh, True.intro⟩

theorem constructor_apply (P : Premises4) (x g : PSet.{4})
    (hx : x ∈ Ed (model P) (tyv (U W4 0)))
    (hg : g ∈ Ed (model P)
      (den (model P) sigma (IndexedBranchDomain.originalAssignment falseCode x)
        IndexedBranchFixture.field)) :
    fapps (mu P 1 []) [falseCode, x, g] ∈
      Ed (model P) (fapps (mu P 0 []) [falseCode, x]) := by
  have hm := (constructor_sound P sigma [] ρ0 rfl
    (fun _ h => nomatch h)).1
  change mu P 1 [] ∈ Ed (model P)
    (den (model P) sigma ρ0 IndexedBranchFixture.introMember.mtype) at hm
  exact mem_fapps (model P) sigma
    (IndexedBranchFixture.famApp (.bvar 2) (.bvar 1))
    [.sort .zero, .sort .zero, IndexedBranchFixture.field]
    ρ0 (mu P 1 []) [falseCode, x, g] hm
    ⟨parameter_mem P, hx, hg, True.intro⟩

theorem minor_mem (P : Premises4) :
    minor P ∈ Ed (model P)
      (den (model P) sigma (start P) IndexedBranchFixture.minorTy) := by
  refine piLam_mem (model P) sigma (envResp_const _)
    IndexedBranchFixture.minorTy (start P) ?_
  intro x hx g hg ih hih
  have hg' : g ∈ Ed (model P)
      (den (model P) sigma
        (push [x] (push [motive P] (push [falseCode] ρ0)))
        (Rcic.Declarative.lift 1 1 IndexedBranchFixture.field)) := hg
  have hdrop : den (model P) sigma
      (push [x] (push [motive P] (push [falseCode] ρ0)))
      (Rcic.Declarative.lift 1 1 IndexedBranchFixture.field) =
      den (model P) sigma (IndexedBranchDomain.originalAssignment falseCode x)
        IndexedBranchFixture.field :=
    den_lift_push (model P) sigma [x] [motive P]
      (push [falseCode] ρ0) IndexedBranchFixture.field
  rw [hdrop] at hg'
  have hc := constructor_apply P x g hx hg'
  have he := motive_apply P x (fapps (mu P 1 []) [falseCode, x, g]) hx hc
  change datum ∈ Ed (model P)
    (fapps (motive P) [x, fapps (mu P 1 []) [falseCode, x, g]])
  exact mem_congr_right
    ((ed_congr (model P) he).trans (ed_tyv (model P) domain_dich)).symm
    (mem_singleton.mpr Equiv.rfl)

/-- A typed constant motive forces every actual evaluation result into
the singleton data domain. Its fitting arguments are recovered, not assumed. -/
theorem eval_domain (P : Premises4) {i : Index.{4}} {z : PSet.{4}}
    (heval : Eval (C P) i z) : z ∈ domain := by
  obtain ⟨j, ps, xs, hkey, hparams, hps, hfields, hz⟩ := heval.result_typed
  let is := (C P).indicesAt j ps xs
  let c := (C P).constructorAt j ps xs
  have hz' : z ∈ Ed (model P) (fapps (motive P) (is ++ [c])) := by
    change z ∈ Ed (model P) (fapp (fapps (motive P) is) c) at hz
    simpa only [fapps_append, fapps] using hz
  have hne : ¬ Equiv (fapps (motive P) (is ++ [c])) pempty := by
    intro h
    exact not_mem_pempty
      (mem_congr_right ((ed_congr (model P) h).trans (ed_pempty (model P))) hz')
  have his : is.length = 1 := by
    change ((IndexedBranchFixture.node.a.constructorViews j).resultIndices.map
      (den (model P) sigma (push xs (push ps ρ0)))).length = 1
    rw [List.length_map, (IndexedBranchFixture.node.a.constructorViews j).indexCount]
    rfl
  have hfit := fits_of_typed_fapps_ne (model P) sigma (.sort (.param 0))
    [.sort .zero, IndexedBranchFixture.famApp (.bvar 1) (.bvar 0)]
    (push [falseCode] ρ0) (motive P) (is ++ [c])
    (by simp only [List.length_append, his]; rfl) (motive_mem P) hne
  have hvalue : Equiv (fapps (motive P) (is ++ [c])) (tyv domain) :=
    fapps_piLam (model P) sigma (envResp_const _) (.sort (.param 0))
      [.sort .zero, IndexedBranchFixture.famApp (.bvar 1) (.bvar 0)]
      (push [falseCode] ρ0) (is ++ [c]) hfit
  exact mem_congr_right
    ((ed_congr (model P) hvalue).trans (ed_tyv (model P) domain_dich)) hz'

theorem eval_nonempty (P : Premises4) {i : Index.{4}} {z : PSet.{4}}
    (heval : Eval (C P) i z) : ¬ Equiv z pempty :=
  fun h => dataVal_ne_pempty 17 []
    ((mem_singleton.mp (eval_domain P heval)).symm.trans h)

theorem functional (P : Premises4) :
    ∀ i z z', Eval (C P) i z → Eval (C P) i z' → Equiv z z' :=
  fun _ _ _ hz hz' =>
    (mem_singleton.mp (eval_domain P hz)).trans
      (mem_singleton.mp (eval_domain P hz')).symm

private theorem levels_bound : ∀ u, u ∈ ([1] : List Nat) → u ≤ bound 2 := by
  intro u hu
  cases List.mem_singleton.mp hu
  exact Nat.le_refl 1

theorem candidate_closed (P : Premises4) :
    Admissible (EvalPlanNormal.fd plan) (X P) ∧
      Closed P (mu P) (EvalPlanNormal.fd plan) (X P) :=
  IndexedPropEval.candidate_closed P (mu P) bound (C P) rfl
    IndexedBranchFixture.famMember [(1, IndexedBranchFixture.introMember)]
    .empty rfl ctorClasses rfl IndexedBranchFixture.membersT
    (IndexedBranchFixture.indexed_bound bound) (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities IndexedBranchFixture.env) (fun _ _ h => nomatch h)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv))
    (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (family_equation P) [1] rfl levels_bound rfl rfl (.param 0)
    (motive_mem P) ⟨minor_mem P, True.intro⟩

theorem constructor_step (P : Premises4) :
    ∀ vs i z, CtorAt P (mu P) (EvalPlanNormal.fd plan) (X P) vs i z →
      PropEvalCandidate.EvalPredicate (C P) vs i z :=
  IndexedPropEval.constructor_step P (mu P) bound (C P) rfl
    IndexedBranchFixture.famMember [(1, IndexedBranchFixture.introMember)]
    .empty rfl ctorClasses rfl IndexedBranchFixture.membersT
    (IndexedBranchFixture.indexed_bound bound) (PointwiseRole.gInv_empty P bound)
    (PointwiseRole.arities IndexedBranchFixture.env) (fun _ _ h => nomatch h)
    (NormRole.envCtx (.empty : EnvWfT emptyEnv))
    (EvalRole.envPlan (.empty : EnvWfT emptyEnv))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ h => nomatch h)
    (family_equation P) [1] rfl levels_bound rfl rfl (.param 0)
    (motive_mem P) ⟨minor_mem P, True.intro⟩

/-- The same ordinary root fields fit any admissible closed frame at the
full syntax valuation. Each child callback is constructed using its negative proof. -/
theorem fields_at_frame (P : Premises4) (Y : Frame)
    (hY : Admissible fd Y) (hc : Closed P (mu P) fd Y)
    (tau : Nat → Nat) :
    TelFits (IndexedBranchFields.model P (mu P) Y) tau
      [.sort .zero, IndexedBranchFixture.field]
      (push [falseCode] ρ0) [trueCode, pempty] := by
  have hp : falseCode ∈ Ed (IndexedBranchFields.model P (mu P) Y)
      (tyv (U W4 0)) :=
    IndexedBranchDomain.false_mem_sort P (RawFamily.table P (mu P) fd Y) tau ρ0
  refine ⟨IndexedBranchDomain.true_mem_sort P
    (RawFamily.table P (mu P) fd Y) tau _, ?_, True.intro⟩
  apply IndexedBranchFields.field_mem_of_children P (mu P) Y hY
    tau falseCode trueCode hp
  intro y n h hzs
  have he : ∀ z, z ∈ Ed (IndexedBranchFields.model P (mu P) Y) y → False :=
    IndexedBranchDomain.original_child_empty P
      (RawFamily.table P (mu P) fd Y) tau falseCode trueCode y n h hzs
  exact hc [] (key [falseCode, y]) pempty
    (IndexedBranchFields.empty_ctor P (mu P) Y hY falseCode y hp hzs.1 he)

theorem fields_raw (P : Premises4) :
    TelFits (model P) sigma [.sort .zero, IndexedBranchFixture.field]
      (push [falseCode] ρ0) [trueCode, pempty] :=
  (TelFits_tables_equiv P
    (table_equiv P (mu P) fd (N P) (family_equation P)) sigma
    [.sort .zero, IndexedBranchFixture.field]
    (push [falseCode] ρ0) [trueCode, pempty]).mpr
    (fields_at_frame P (N P) (normalized_closed P).1
      (raw_closed P (N P) (normalized_closed P).2) sigma)

theorem fields_candidate (P : Premises4) :
    TelFits (IndexedBranchFields.model P (mu P) (X P)) sigma
      [.sort .zero, IndexedBranchFixture.field]
      (push [falseCode] ρ0) [trueCode, pempty] :=
  fields_at_frame P (X P) (candidate_closed P).1
    (raw_closed P (X P) (candidate_closed P).2) sigma

theorem root_ctor (P : Premises4) :
    CtorAt P (mu P) (EvalPlanNormal.fd plan) (X P) [] rootKey pempty :=
  normalize_ctor P (X P) [] rootKey pempty
    (IndexedBranchFields.ctor_of_closed P (mu P) (X P)
      (candidate_closed P).1 (raw_closed P (X P) (candidate_closed P).2)
      falseCode trueCode
      (IndexedBranchDomain.false_mem_sort P
        (RawFamily.table P (mu P) fd (X P)) (σOf []) ρ0)
      (IndexedBranchDomain.true_mem_sort P
        (RawFamily.table P (mu P) fd (X P)) (σOf []) ρ0))

theorem root_step (P : Premises4) :
    PropEvalCandidate.EvalPredicate (C P) [] rootKey pempty :=
  constructor_step P [] rootKey pempty (root_ctor P)

theorem root_eval (P : Premises4) : ∃ z, Eval (C P) rootKey z :=
  root_step P (fun u hu => (Nat.not_lt_zero u hu).elim) rfl

private theorem inserted_field_den (M : Interp.{4}) (tau : Nat → Nat)
    (p x mo g : PSet.{4}) :
    den M tau (IndexedBranchDomain.assignment p x mo g)
      (policyPi IndexedBranchDomain.domains
        (foldApps (.const 0 []) IndexedBranchDomain.arguments)) =
      den M tau (IndexedBranchDomain.originalAssignment p x)
        IndexedBranchFixture.field := by
  change den M tau (vcons g (vcons x (vcons mo (push [p] ρ0))))
      (Rcic.Declarative.lift 0 1
        (Rcic.Declarative.lift 1 1 IndexedBranchFixture.field)) = _
  rw [den_lift01]
  exact den_lift_push M tau [x] [mo] (push [p] ρ0) IndexedBranchFixture.field

theorem inserted_raw (P : Premises4) :
    pempty ∈ Ed (C P).M
      (den (C P).M (C P).σ (atField P)
        (policyPi IndexedBranchDomain.domains
          (foldApps (.const 0 []) IndexedBranchDomain.arguments))) := by
  change pempty ∈ Ed (model P)
    (den (model P) sigma
      (IndexedBranchDomain.assignment falseCode trueCode (motive P) pempty)
      (policyPi IndexedBranchDomain.domains
        (foldApps (.const 0 []) IndexedBranchDomain.arguments)))
  rw [inserted_field_den]
  exact (fields_raw P).2.1

theorem inserted_candidate (P : Premises4) :
    pempty ∈ Ed (IndexedBranchFields.model P (mu P) (X P))
      (den (IndexedBranchFields.model P (mu P) (X P)) sigma (atField P)
        (policyPi IndexedBranchDomain.domains
          (foldApps (.const 0 []) IndexedBranchDomain.arguments))) := by
  change pempty ∈ Ed (IndexedBranchFields.model P (mu P) (X P))
    (den (IndexedBranchFields.model P (mu P) (X P)) sigma
      (IndexedBranchDomain.assignment falseCode trueCode (motive P) pempty)
      (policyPi IndexedBranchDomain.domains
        (foldApps (.const 0 []) IndexedBranchDomain.arguments)))
  rw [inserted_field_den]
  exact (fields_candidate P).2.1

theorem selected_fits (P : Premises4) :
    TelFits (C P).M (C P).σ IndexedBranchDomain.domains (atField P) selected :=
  IndexedBranchFixture.selected_child_at_table P (motive P) pempty

private theorem domains_free :
    ∀ e ∈ IndexedBranchDomain.domains, occursConst 0 e = false := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · rfl
  rcases List.mem_cons.mp he with rfl | he
  · rfl
  cases List.mem_singleton.mp he
  rfl

private theorem arguments_free :
    ∀ e ∈ IndexedBranchDomain.arguments, occursConst 0 e = false := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · rfl
  cases List.mem_singleton.mp he
  rfl

theorem prefix_read (P : Premises4) (zs : List PSet.{4})
    (hzs : TelFits (C P).M (C P).σ IndexedBranchDomain.domains (atField P) zs) :
    (IndexedBranchDomain.arguments.take 1).map
      (den (C P).M (C P).σ (push zs (atField P))) = [falseCode] := by
  change (IndexedBranchDomain.arguments.take 1).map
    (den (model P) sigma (push zs
      (IndexedBranchDomain.assignment falseCode trueCode (motive P) pempty))) =
        [falseCode]
  obtain ⟨y, hy, _⟩ := IndexedBranchDomain.fitted_arguments P (mu P) sigma
    falseCode trueCode (motive P) pempty zs hzs
  rw [List.map_take, hy]
  rfl

theorem packet (P : Premises4) :
    RecursivePacket (C P) 32 3
      (Rcic.Declarative.lift 1 1 IndexedBranchFixture.field)
      (.bvar 1) (beforeField P) pempty := by
  obtain ⟨endVal, hEnd, hF, hProp⟩ :=
    NormPropEval.frame_inputs P (mu P) (C P) rfl raw_bounded
      (N P) (family_equation P) (normalized_closed P).1 rfl
  have hguarded : ∀ i z, Eval (C P) i z → z ∈ childCarrier (C P) (.param 0) i := by
    intro i z hz
    exact hz.mem_guarded_of_typed_motive (.param 0) rfl (motive_mem P) hProp
  exact recursive_packet_on_frame P (mu P) (C P) rfl
    (N P) (normalized_closed P).1 family_free
    32 3 (Rcic.Declarative.lift 1 1 IndexedBranchFixture.field)
    (.bvar 1) (beforeField P) pempty (.param 0) rfl
    endVal hEnd rfl hF (motive_mem P)
    IndexedBranchDomain.domains IndexedBranchDomain.arguments rfl rfl
    IndexedBranchFixture.depth3_reads.1 domains_free arguments_free
    (prefix_read P) rfl hProp (inserted_raw P) (inserted_candidate P)
    hguarded (functional P)

/-- The packet's existential type and reader are identified with the
actual executable depth-three declarations, before selecting a child. -/
theorem typed_ih (P : Premises4) :
    ∃ ih : PSet.{4},
      ih ∈ Ed (C P).M
        (den (C P).M (C P).σ (atField P) IndexedBranchFixture.ihTy) ∧
      ∀ zs, TelFits (C P).M (C P).σ
        IndexedBranchDomain.domains (atField P) zs →
        Eval (C P)
          (key (IndexedBranchDomain.arguments.map
            (den (C P).M (C P).σ (push zs (atField P)))))
          (fapps ih zs) := by
  obtain ⟨ihT, ih, ds, args, htype, hih, hscan, hdepth, hargc, hchildren⟩ := packet P
  have htype' : IndexedBranchFixture.ihTy = ihT :=
    Option.some.inj (IndexedBranchFixture.depth3_reads.2.symm.trans htype)
  subst ihT
  have hpairs := Option.some.inj
    (IndexedBranchFixture.depth3_reads.1.symm.trans hscan)
  have hds : IndexedBranchDomain.domains = ds := congrArg Prod.fst hpairs
  have hspine :
      foldApps (.const 0 [] : Expr Nat) IndexedBranchDomain.arguments =
        foldApps (.const 0 []) args := congrArg Prod.snd hpairs
  have hargs : IndexedBranchDomain.arguments = args := by
    have hs := congrArg appsSpine hspine
    simpa only [appsSpine_foldApps, appsSpine, List.nil_append]
      using congrArg Prod.snd hs
  subst ds
  subst args
  exact ⟨ih, hih, hchildren⟩

noncomputable def IHComponent (P : Premises4) : Prop :=
  ∃ ih : PSet.{4},
    ih ∈ Ed (C P).M
      (den (C P).M (C P).σ (atField P) IndexedBranchFixture.ihTy) ∧
    (∀ zs, TelFits (C P).M (C P).σ
      IndexedBranchDomain.domains (atField P) zs →
      Eval (C P)
        (key (IndexedBranchDomain.arguments.map
          (den (C P).M (C P).σ (push zs (atField P)))))
        (fapps ih zs)) ∧
    Eval (C P) childKey (fapps ih selected) ∧
    fapps ih selected ∈ domain ∧ ¬ Equiv (fapps ih selected) pempty

theorem ih_component (P : Premises4) : IHComponent P := by
  obtain ⟨ih, hih, hchildren⟩ := typed_ih P
  have he : Eval (C P) childKey (fapps ih selected) :=
    hchildren selected (selected_fits P)
  exact ⟨ih, hih, hchildren, he, eval_domain P he, eval_nonempty P he⟩

structure Witness (P : Premises4) : Prop where
  checkpoint : IndexedBranchFixture.Witness P
  complete_valuation : (C P).σ 0 = 1
  motive_typed : motive P ∈ Ed (model P)
    (den (model P) sigma (push [falseCode] ρ0) IndexedBranchFixture.motiveTy)
  minor_typed : minor P ∈ Ed (model P)
    (den (model P) sigma (start P) IndexedBranchFixture.minorTy)
  candidate : Admissible (EvalPlanNormal.fd plan) (X P) ∧
    Closed P (mu P) (EvalPlanNormal.fd plan) (X P)
  original_fields : TelFits (IndexedBranchFields.model P (mu P) (X P)) sigma
    [.sort .zero, IndexedBranchFixture.field]
    (push [falseCode] ρ0) [trueCode, pempty]
  actual_ctor : CtorAt P (mu P) (EvalPlanNormal.fd plan) (X P) [] rootKey pempty
  actual_step : PropEvalCandidate.EvalPredicate (C P) [] rootKey pempty
  depth : IndexedBranchDomain.domains.length = 3
  actual_child : TelFits (C P).M (C P).σ
    IndexedBranchDomain.domains (atField P) selected
  root : ∃ z, Eval (C P) rootKey z ∧ z ∈ domain ∧ ¬ Equiv z pempty
  executable_ih : IHComponent P
  separate_keys : childKey ≠ rootKey

theorem component_witness (P : Premises4) : Witness P := by
  obtain ⟨z, hz⟩ := root_eval P
  exact ⟨IndexedBranchFixture.component_witness P, rfl,
    motive_mem P, minor_mem P, candidate_closed P, fields_candidate P,
    root_ctor P, root_step P, rfl, selected_fits P,
    ⟨z, hz, eval_domain P hz, eval_nonempty P hz⟩, ih_component P,
    IndexedBranchDomain.child_parent_keys_ne P falseCode⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

theorem composed_witness (P : Premises4) :
    AIndexedPropContract.Components P ∧ Witness P :=
  ⟨AIndexedPropContract.components P, component_witness P⟩

theorem composed_nonrefutable (P : Premises4) :
    ¬ ((AIndexedPropContract.Components P ∧ Witness P) → (Premises4 → False)) :=
  fun h => h (composed_witness P) P

end Rcic.F3.PSet.IndexedBranchEvalAttack

#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.canonical_plan
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.family_equation
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.constructor_sound
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.motive_mem
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.minor_mem
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.eval_domain
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.candidate_closed
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.constructor_step
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.fields_candidate
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.root_step
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.packet
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.typed_ih
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.ih_component
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.component_witness
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.component_nonrefutable
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.composed_witness
#print axioms Rcic.F3.PSet.IndexedBranchEvalAttack.composed_nonrefutable
