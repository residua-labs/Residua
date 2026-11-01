import rcic.RcicF3NormDataRec
import rcic.RcicF3NormDataRead
import rcic.RcicF3NormPropEvalValue
import rcic.RcicF3TableSound

/-!
# Normalized DATA recursion in the actual requested motive

The actual faithful family equation makes its frame update pointwise
equivalent to the installed table. Typed parameters, motive and minors
transport at the unchanged valuation. Constructor read equations supply
the literal data codes. Produced normalized recursion then inhabits the
guarded motive; the actual fitting indices and major remove that guard.

The result is the actual nodeCore in the original table. No raw-family
equation, recursive-totality callback or erasure of a data major is used.
The small normalized candidate and ordinary reader soundness are explicit
component inputs. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataValue
open Rcic.Declarative PiIndex RawFamily PropEval

theorem nodeCore_mem (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (C : Context)
    (hM : C.M = mkM P μ)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT C.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : C.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv C.E C.f fm) C.E
      ((C.f, fm) :: ctors ++ [(C.rr, C.rm)]) C.E')
    (hBound : BoundG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hBoundD : BoundDG K (EnvWfT.group C.E C.f fm ctors C.rr C.rm C.E'
      hE hfam hctors hrec hmem))
    (hpar : ∀ j : Fin C.node.a.constructors.length,
      (C.node.a.constructorViews j).parameters = C.node.a.family.parameters)
    (hPred : NormRole.GInv P K hE)
    (ctx : Nat → Role) (plans : EvalRole.Plans)
    (hctx : ∀ r, Dom C.E r → ctx r = NormRole.envCtx hE r)
    (hplans : ∀ r, Dom C.E r → plans r = EvalRole.envPlan hE r)
    (hFaith : EvalRole.Faithful role P μ ctx plans C.E)
    (hFamily : ∀ vs, Equiv (μ C.node.a.family.ref vs)
      (ofFrame P μ (famDataOf C.node.a)
        (frame P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node))) vs))
    (hCtor : ∀ (j : Fin C.node.a.constructors.length) vs,
      Equiv (μ (C.node.a.family.ref + 1 + j.val) vs)
        (piLam (mkM P μ) (σOf vs)
          (ctorEnd (mkM P μ) (σOf vs) (famDataOf C.node.a) j.val
            (C.node.a.constructorViews j).fields.length) ρ0
          (C.node.a.constructors[j.val]).mtype))
    (hsmall : ∃ A, Admissible (EvalPlanNormal.fd (EvalPlan.ofNode C.node)) A ∧
      Closed P μ (EvalPlanNormal.fd (EvalPlan.ofNode C.node)) A)
    (hvs : ∀ u, u ∈ (canonL C.node.a.family.member.arity).map (evalTotal C.σ) → u ≤ K C.rr)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel ≠ 0)
    {n : Nat} (hReader : EnvSound C.M C.σ K C.node.E0 n)
    (v : Level)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors)
    (is : List PSet.{4}) (major : PSet.{4})
    (hps : TelFits C.M C.σ C.node.a.family.parameters ρ0 C.parameters)
    (his : TelFits C.M C.σ C.node.a.family.indices (push C.parameters ρ0) is)
    (hmajor : major ∈ Ed C.M (fapps (C.M.μ C.node.a.family.ref
      ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
      (C.parameters ++ is))) :
    RecPlan.nodeCore C.M C.node C.minors major ∈ Ed C.M
      (fapps C.motive (is ++ [major])) := by
  let p := EvalPlan.ofNode C.node
  let N := frame P μ (EvalPlanNormal.fd p)
  let ν := table P μ (famDataOf C.node.a) N
  let MN := mkM P ν
  let D := C.withModel MN
  let vs := (canonL C.node.a.family.member.arity).map (evalTotal C.σ)
  have hN : Admissible (famDataOf C.node.a) N :=
    frame_admissible P μ (EvalPlanNormal.fd p) hsmall
  obtain ⟨_, _, _, hTF, _, hB⟩ :=
    CandidatePrefixFromGroup.syntax_facts hE hmem C.node
  have hCB : ∀ j : Fin C.node.a.constructors.length,
      exprLevelsBounded C.node.a.family.member.arity
        (C.node.a.constructors[j.val]).mtype = true := by
    intro j
    have h := (hTF _ _ (node_ctor_member C.node j)).2.1
    rw [(C.node.a.constructorViews j).arity] at h
    exact h
  have hEq : ∀ r ls, Equiv (μ r ls) (ν r ls) :=
    table_equiv P μ (famDataOf C.node.a) N hFamily
  have hmoN : C.motive ∈ Ed MN (den MN C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))) := by
    apply (TableSound.value_mem_iff P hEq C.σ _ _ _).mp
    simpa only [hM] using hmo
  have hminorsN : TelFits MN C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors := by
    apply (TelFits_tables_equiv P hEq C.σ _ _ _).mp
    simpa only [hM] using hminors
  have hpsN : TelFits MN C.σ C.node.a.family.parameters ρ0 C.parameters := by
    apply (TelFits_tables_equiv P hEq C.σ _ _ _).mp
    simpa only [hM] using hps
  have hisN : TelFits MN C.σ C.node.a.family.indices (push C.parameters ρ0) is := by
    apply (TelFits_tables_equiv P hEq C.σ _ _ _).mp
    simpa only [hM] using his
  have hmajorN : major ∈ Ed MN
      (fapps (ν C.node.a.family.ref vs) (C.parameters ++ is)) := by
    apply mem_congr_right (ed_congr MN (fapps_congr (hEq _ _) _))
    simpa only [hM] using hmajor
  have hReaderN : EnvSound MN C.σ K C.node.E0 n := by
    apply TableSound.environment P hEq C.σ
    simpa only [hM] using hReader
  have hctorN : ∀ (j : Fin D.node.a.constructors.length) xs,
      TelFits D.M D.σ (D.node.a.constructorViews j).fields (push D.parameters ρ0) xs →
      Equiv (D.constructorAt j D.parameters xs) (dataVal j.val xs) := by
    intro j xs hx
    have hj : j.val < C.node.a.constructors.length := j.isLt
    have hc := NormDataRead.constructor_at P μ p hB hCB hCtor C.σ j
    have ht := piLam_tables P hEq C.σ
      (ctorEnd_resp (mkM P μ) C.σ (famDataOf C.node.a) j.val
        (C.node.a.constructorViews j).fields.length)
      (g₂ := ctorEnd MN C.σ (famDataOf C.node.a) j.val
        (C.node.a.constructorViews j).fields.length)
      (fun _ => Equiv.rfl) (C.node.a.constructors[j.val]).mtype ρ0
    have hvalue := (hEq _ _).symm.trans (hc.trans ht)
    exact RawDataMinor.constructor_data MN C.σ C.node j C.parameters xs
      h0 (hpar j) hpsN hx hvalue
  have hcore := NormDataRec.nodeCore_guarded_of_small_frame P μ K D rfl fm ctors
    hE hfam hctors hrec hmem hBound hBoundD hpar hPred ctx plans hctx hplans hFaith
    hsmall hvs h0 hReaderN v hps.length hmoN hminorsN hctorN
  have hmajorFrame := NormPropEval.major_at_frame P μ C hM hB hFamily hN
    is major hps his hmajor
  have hkey : RawFamilyRec.paramKey C.node.a.family.parameters.length (key (C.parameters ++ is)) =
      key C.parameters := by
    rw [← hps.length]
    exact RawFamilyRec.paramKey_append C.parameters is
  have hr := hcore (key (C.parameters ++ is)) major hkey hmajorFrame
  have hTy := PiRawMotiveAny.motive_mem_U MN rfl C.σ C.node.a.family.ref
    (canonL C.node.a.family.member.arity) C.node.a.family.parameters C.node.a.family.indices
    C.parameters is hps.length C.motive major v hmoN hisN hmajorN
  have hg := PiRawMotiveAny.guarded_key MN C.σ (evalTotal C.σ v)
    (ν C.node.a.family.ref vs) C.motive C.parameters C.node.a.family.indices
    (push C.parameters ρ0) is major hisN hmajorN hTy
  have hout : RecPlan.nodeCore MN C.node C.minors major ∈
      Ed MN (fapps C.motive (is ++ [major])) := mem_congr_right hg hr
  have he : RecPlan.nodeCore MN C.node C.minors major =
      RecPlan.nodeCore C.M C.node C.minors major := by
    rw [hM]
    unfold RecPlan.nodeCore RecPlan.core
    rw [recCore_of_dec (M := MN) (M' := mkM P μ) rfl]
  rw [he] at hout
  simpa only [hM] using hout

end Rcic.F3.PSet.NormDataValue
