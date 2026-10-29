import rcic.RcicAnnLR3ContentJ
import rcic.RcicAnnLR3EqKLikeHook
import rcic.RcicAnnLR3CandidateReader

/-!
# The J Ty arm on the Target (content model, K-like hook)

In the AnySort Eq environment (`EqLargeFixture`, Eq family 63, refl 64,
recursor 65) with the K-like hook (`EqKLikeHook.eqKHook`):

- the hook computes the Eq family to the index-retaining family term
  (`eqK_fam_image`) and refl to its closed constructor term
  (`eqK_refl_image`);
- the evaluator's image of the recursor type at any level `l` is the image
  of the content code `recCode 63 u rfImg` (`recTy_image`, with
  `eval ν l = some u`); `rfImg` is the raw image of `refl A a`
  (`refl_img`);
- the recursor value is a K-like operator (`kTerm_klike`).

**`rec_judgment`.** In `annSemantics ContentCodes.codeSystem` over this
environment and hook, `Eq.rec` at any level is a member of its type at every
raw environment: an actual `Judgment` for the recursor constant, with the
motive's codomain any `Sort u` (large elimination). The code system is the
content one: `∀ X : Prop, X` is empty in it.

Not claimed: the other constants of the environment, a reader, or a
Fundamental theorem. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.ContentJTarget

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open TypeZeroTowerProbe (imaxN withBot)
open CandidateTowerProbe (REnv rcons)
open IotaRecursor AdmissionUniverseReadback EqTargetIota IndexFamilyHook EqLargeFixture EqKLikeHook
open ContentCodes ContentJ

/-! ## Images of source types as images of content codes -/

section Generic

variable {E : ResolvedEnvA} {H : EnvironmentEval.FamilySyntax} {ν : Valuation}

theorem pi_img {ρ : EnvI} {A B : ExprA} {u v : Level} {a b : Nat} {cA : DCode a} {cB : DCode b}
    (hu : eval ν u = some a) (hv : eval ν v = some b)
    (hA : ValueEq (EnvironmentEval.denote E H ν ρ A) (image ρ cA))
    (hB : ∀ x, ValueEq (EnvironmentEval.denote E H ν (rcons x ρ) B) (image (rcons x ρ) cB)) :
    ValueEq (EnvironmentEval.denote E H ν ρ (.pi A u B v)) (image ρ (DCode.pi cA cB)) := by
  have h := EnvironmentEval.denote_pi_value E H ν ρ A B u v
  have hl := NeutralCodes.valueEq_eq (EnvironmentEval.denote_lambda_graph E H ν ρ A B u)
  rw [hl, hu, hv, TowerSourcePi.imaxLevel_some, NeutralCodes.valueEq_eq hA,
    CandidateCodeSystem.legalGraph_congr (G := fun x => image (rcons x ρ) cB)
      (fun x => by
        rw [← CandidateReader.rcons_eq_cons x ρ]
        exact hB x)] at h
  exact h

theorem sort_img (ρ : EnvI) (l : Level) {k : Nat} (hl : eval ν l = some k) :
    ValueEq (EnvironmentEval.denote E H ν ρ (.sort l)) (image ρ (DCode.univ k)) := by
  have hs : EnvironmentEval.denote E H ν ρ (.sort l) = universeValue (eval ν l) :=
    (EnvironmentEval.annSemantics ContentCodes.codeSystem E H).sort_image ν [] ρ l
  rw [hs, hl]
  exact ValueEq.refl _

theorem bvar_img (ρ : EnvI) (k i : Nat) :
    ValueEq (EnvironmentEval.denote E H ν ρ (.bvar i)) (image ρ (DCode.var k i [])) :=
  CandidateCodeSystem.bvar_image E H ν ρ i

theorem bvar_wb (ρ : EnvI) (i : Nat) :
    ValueEq (EnvironmentEval.denote E H ν ρ (.bvar i)) (wb i ρ) :=
  CandidateCodeSystem.bvar_image E H ν ρ i

theorem app2_img (ρ : EnvI) (k i : Nat) {X Y : ExprA} {tX tY : TImg}
    (hX : ValueEq (EnvironmentEval.denote E H ν ρ X) (tX ρ))
    (hY : ValueEq (EnvironmentEval.denote E H ν ρ Y) (tY ρ)) :
    ValueEq (EnvironmentEval.denote E H ν ρ (.app (.app (.bvar i) X) Y))
      (image ρ (DCode.var k i [tX, tY])) := by
  rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_application E H ν ρ _ Y),
    NeutralCodes.valueEq_eq (EnvironmentEval.denote_application E H ν ρ _ X),
    NeutralCodes.valueEq_eq (CandidateCodeSystem.bvar_image E H ν ρ i),
    NeutralCodes.valueEq_eq hX, NeutralCodes.valueEq_eq hY]
  exact ValueEq.refl _

end Generic

/-! ## The K-like hook at the Eq family and refl -/

section Fixture

variable (hE : EnvWfA (iotaIfaceA env) env)

/-- Applications of the Eq family. -/
def eq3 (X Y Z : ExprA) : ExprA := (((ExprA.const 63 []).app X).app Y).app Z

theorem eqK_fam_image (ν : Valuation) (ρ : EnvI) :
    EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ (.const 63 []) =
      denI ρ (familyTerm 3 (some 0) 63) := by
  have hm : env.members 63 = some fam := rfl
  have hbody : EnvironmentEval.definitionBody (SemanticMemberEval.view env) 63 [] = none := by
    rw [SemanticMemberEval.definitionBody_preserved]
    simp [EnvironmentEval.definitionBody, hm, fam, transparent]
  have hread : readAdmitted hE ν (instantiateLevelsA [] famTy) = none :=
    read_pi_none hE ν _ _ _ _
  have hv : (SemanticMemberEval.view env).members 63 = some (SemanticMemberEval.route fam) := by
    simp [SemanticMemberEval.view, hm]
  have hrigid : EnvironmentEval.rigidTerm (SemanticMemberEval.view env) (hook hE eqKHook)
      ν 63 [] = familyTerm 3 (some 0) 63 := by
    have hc : fam.mclass = .inductiveM := rfl
    have ht : fam.mtypeA = famTy := rfl
    simp [EnvironmentEval.rigidTerm, hv, SemanticMemberEval.route, hc, hook, hm, eqKHook,
      indexHook, ht, fam_sortTail]
    rw [hread]
    rfl
  rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_rigid hbody _ ν ρ), hrigid]

theorem eqK_refl_image (ν : Valuation) (ρ : EnvI) :
    EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ (.const 64 []) =
      denI ρ (iotaTerm env 64) := by
  have hm : env.members 64 = some reflMember := rfl
  have hbody : EnvironmentEval.definitionBody (SemanticMemberEval.view env) 64 [] = none := by
    rw [SemanticMemberEval.definitionBody_preserved]
    simp [EnvironmentEval.definitionBody, hm, reflMember, transparent]
  obtain ⟨A, u, B, v, hT⟩ := eq_ctorRecPi 64 reflMember hm (Or.inl rfl) []
  have hread : readAdmitted hE ν (instantiateLevelsA [] reflMember.mtypeA) = none := by
    rw [hT]
    exact read_pi_none hE ν A u B v
  have hv : (SemanticMemberEval.view env).members 64 =
      some (SemanticMemberEval.route reflMember) := by
    simp [SemanticMemberEval.view, hm]
  have hrigid : EnvironmentEval.rigidTerm (SemanticMemberEval.view env) (hook hE eqKHook)
      ν 64 [] = iotaTerm env 64 := by
    have hc : reflMember.mclass = .constructorM := rfl
    simp [EnvironmentEval.rigidTerm, hv, SemanticMemberEval.route, hc, hook, hm, hread, eqKHook,
      indexHook]
  rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_rigid hbody _ ν ρ), hrigid]

theorem eq3_img (ν : Valuation) (ρ : EnvI) {X Y Z : ExprA} {a : Nat} {cX : DCode a} {tY tZ : TImg}
    (hX : ValueEq (EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ X)
      (image ρ cX))
    (hY : ValueEq (EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ Y)
      (tY ρ))
    (hZ : ValueEq (EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ Z)
      (tZ ρ)) :
    ValueEq (EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ (eq3 X Y Z))
      (image ρ (DCode.eq 63 cX tY tZ)) := by
  show ValueEq (EnvironmentEval.denote _ _ ν ρ (foldAppsA (.const 63 []) [X, Y, Z])) _
  rw [denote_foldAppsA, eqK_fam_image hE ν ρ]
  simp only [List.map]
  refine (familyTerm_apply 3 (some 0) 63 ρ
    [EnvironmentEval.denote _ (hook hE eqKHook) ν ρ X, EnvironmentEval.denote _ (hook hE eqKHook) ν ρ Y,
      EnvironmentEval.denote _ (hook hE eqKHook) ν ρ Z] rfl (by
    intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact EnvironmentEval.denote_bot _ _ _ _ _)).trans ?_
  rw [NeutralCodes.valueEq_eq hX, NeutralCodes.valueEq_eq hY, NeutralCodes.valueEq_eq hZ]
  exact ValueEq.refl _

/-- The raw value of the refl constructor (a closed term). -/
def c64 : Value := denI EnvI.bot (iotaTerm env 64)

/-- The raw image of `refl A a` in the context `[P, a, A]`. -/
def rfImg : TImg := fun σ => IotaRecursor.applyAll c64 [withBot (σ 2), withBot (σ 1)]

theorem rfImg_tok : TOk rfImg :=
  ⟨applyAll_cont [wb 2, wb 1] (f := fun _ => c64) (LevelGirard.const_cont _) (by
    intro t ht
    rcases mem_two ht with rfl | rfl
    · exact (wb_tok 2).1
    · exact (wb_tok 1).1),
   fun _ => applyAll_bot _ _ (ApproxI.bot _ _)⟩

theorem rfImg_closed : TClosed 3 rfImg := fun σ σ' h => by
  show IotaRecursor.applyAll c64 [withBot (σ 2), withBot (σ 1)] =
    IotaRecursor.applyAll c64 [withBot (σ' 2), withBot (σ' 1)]
  rw [h 2 (by decide), h 1 (by decide)]

theorem rfImg_free (σ : REnv) (v : Value) : rfImg (CandidateTowerCoherence.upd σ 0 v) = rfImg σ := by
  show IotaRecursor.applyAll c64 [wb 2 (CandidateTowerCoherence.upd σ 0 v),
      wb 1 (CandidateTowerCoherence.upd σ 0 v)] = IotaRecursor.applyAll c64 [wb 2 σ, wb 1 σ]
  rw [wb_upd (by decide) σ v, wb_upd (by decide) σ v]

theorem refl_img (ν : Valuation) (ρ : EnvI) :
    ValueEq (EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ
      (.app (.app (.const 64 []) (.bvar 2)) (.bvar 1))) (rfImg ρ) := by
  rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_application _ _ ν ρ _ (.bvar 1)),
    NeutralCodes.valueEq_eq (EnvironmentEval.denote_application _ _ ν ρ _ (.bvar 2)),
    eqK_refl_image hE ν ρ, denI_closed (iotaTerm env 64) (nbound_iotaTerm env 64) ρ EnvI.bot,
    NeutralCodes.valueEq_eq (CandidateCodeSystem.bvar_image _ _ ν ρ 2),
    NeutralCodes.valueEq_eq (CandidateCodeSystem.bvar_image _ _ ν ρ 1)]
  exact ValueEq.refl _

/-- The fixture's recursor type at the level `l`. -/
def recTyL (l : Level) : ExprA :=
  .pi (.sort (.succ .zero)) (.succ (.succ .zero))
    (.pi (.bvar 0) (.succ .zero)
      (.pi (.pi (.bvar 1) (.succ .zero) (.pi (eq3 (.bvar 2) (.bvar 1) (.bvar 0)) .zero (.sort l) (.succ l))
          (.imax .zero (.succ l)))
        (.imax (.succ .zero) (.imax .zero (.succ l)))
        (.pi (.app (.app (.bvar 0) (.bvar 1)) (.app (.app (.const 64 []) (.bvar 2)) (.bvar 1))) l
          (.pi (.bvar 3) (.succ .zero)
            (.pi (eq3 (.bvar 4) (.bvar 3) (.bvar 0)) .zero (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) l)
            (.imax .zero l))
          (.imax (.succ .zero) (.imax .zero l)))
        (.imax l (.imax (.succ .zero) (.imax .zero l))))
      (.imax (.imax (.succ .zero) (.imax .zero (.succ l))) (.imax l (.imax (.succ .zero) (.imax .zero l)))))
    (.imax (.succ .zero) (.imax (.imax (.succ .zero) (.imax .zero (.succ l)))
      (.imax l (.imax (.succ .zero) (.imax .zero l)))))

theorem recTy_inst (l : Level) : instantiateLevelsA [l] recMember.mtypeA = recTyL l := rfl

/-- The evaluator's image of the recursor type is the image of `recCode`. -/
theorem recTy_image (ν : Valuation) (l : Level) {u : Nat} (hl : eval ν l = some u) (ρ : EnvI) :
    ValueEq (EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ (recTyL l))
      (image ρ (recCode 63 u rfImg)) := by
  have e0 : eval ν .zero = some 0 := rfl
  have e1 : eval ν (.succ .zero) = some 1 := rfl
  have e2 : eval ν (.succ (.succ .zero)) = some 2 := rfl
  have eS : eval ν (.succ l) = some (u + 1) := by simp [eval, hl]
  have i0S := TowerSourcePi.eval_imax_some ν e0 eS
  have i10S := TowerSourcePi.eval_imax_some ν e1 i0S
  have i0u := TowerSourcePi.eval_imax_some ν e0 hl
  have i10u := TowerSourcePi.eval_imax_some ν e1 i0u
  have iu10u := TowerSourcePi.eval_imax_some ν hl i10u
  have iPcod := TowerSourcePi.eval_imax_some ν i10S iu10u
  have iAcod := TowerSourcePi.eval_imax_some ν e1 iPcod
  refine pi_img e2 iAcod (sort_img ρ _ e1) (fun xA => ?_)
  refine pi_img e1 iPcod (bvar_img _ 1 0) (fun xa => ?_)
  refine pi_img i10S iu10u ?_ (fun xP => ?_)
  · refine pi_img e1 i0S (bvar_img _ 1 1) (fun xb => ?_)
    exact pi_img e0 eS (eq3_img hE ν _ (bvar_img _ 1 2) (bvar_wb _ 1) (bvar_wb _ 0))
      (fun _ => sort_img _ _ hl)
  refine pi_img hl i10u (app2_img _ u 0 (bvar_wb _ 1) (refl_img hE ν _)) (fun xm => ?_)
  refine pi_img e1 i0u (bvar_img _ 1 3) (fun xb => ?_)
  exact pi_img e0 hl (eq3_img hE ν _ (bvar_img _ 1 4) (bvar_wb _ 3) (bvar_wb _ 0))
    (fun _ => app2_img _ u 3 (bvar_wb _ 1) (bvar_wb _ 0))

/-- The K-like recursor value is a K-like operator. -/
theorem kTerm_klike (ρ : EnvI) : KLikeOp (denI ρ kTerm) :=
  ⟨ApproxI.bot _ _, fun xA xa xP xm xb xh hA ha hP hm hb hh =>
    kTerm_apply ρ [xA, xa, xP, xm, xb, xh] rfl (by
      intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)⟩

/-- **The J Ty arm on the Target.** In the content code system over the
AnySort Eq environment with the K-like hook, the recursor constant at any
level is a member of its type, at every raw environment. -/
theorem rec_judgment (ν : Valuation) (l : Level) {u : Nat} (hl : eval ν l = some u) (ρ : EnvI) :
    Judgment (EnvironmentEval.annSemantics ContentCodes.codeSystem (SemanticMemberEval.view env)
        (hook hE eqKHook)) ν [] ρ (.const 65 [l]) (.const 65 [l])
      (instantiateLevelsA [l] recMember.mtypeA) := by
  rw [recTy_inst]
  have hw := recCode_wfc 63 u rfImg_tok rfImg_closed rfImg_free
  have himg : ValueEq (EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ
      (recTyL l)) (image σ0 (recCode 63 u rfImg)) := by
    rw [← image_closed _ 0 ρ σ0 hw.2 (fun _ h => absurd h (Nat.not_lt_zero _))]
    exact recTy_image hE ν l hl ρ
  have hc := family.ok_code (c := recCode 63 u rfImg) hw himg
  refine ⟨_, El σ0 ρ0 (recCode 63 u rfImg), hc, ContentCodes.codeSystem.defined hc, ?_⟩
  show El σ0 ρ0 _ (EnvironmentEval.denote _ _ ν ρ (.const 65 [l]))
    (EnvironmentEval.denote _ _ ν ρ (.const 65 [l]))
  rw [rec_const_image hE ν ρ [l]]
  exact rec_member 63 u rfImg rfImg_tok.2 (kTerm_klike ρ) σ0 ρ0 sat0

end Fixture

end Rcic.Declarative.Ann.LR3.ContentJTarget
