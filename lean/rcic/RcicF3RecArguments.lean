import rcic.RcicF3IndexedPropPlainIota

/-!
# Universal argument recovery from a nonempty installed recursor application

This factors the left-spine argument of IndexedPropPlainIota. Its proof uses
only the installed recursor equation, its admitted plan, and the literal
legacy witness. It imposes no constructor selection, field-shape condition,
NoFunRec, source context, right-hand side, or completed-environment soundness.
Every parameter, motive, minor, index, and major binder is retained.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.RecArguments
open Rcic.Declarative Rcic.Model.PS RawFamily PropEval

noncomputable def valuation {S : ResolvedEnv} (w : IotaWitness S)
    (σ : Nat → Nat) : Nat → Nat := σOf (w.ls.map (evalTotal σ))

/-- The complete arguments of the actual installed left application. -/
structure Arguments (M : Interp.{4}) (p : EvalPlan.Plan)
    {S : ResolvedEnv} (w : IotaWitness S) (σ : Nat → Nat)
    (ρ : Nat → PSet.{4}) (ps : List PSet.{4}) (mo : PSet.{4})
    (ms is : List PSet.{4}) : Prop where
  split : w.preMajor.map (den M σ ρ) = ps ++ mo :: (ms ++ is)
  parameters_length : ps.length = p.node.a.family.parameters.length
  minors_length : ms.length = p.node.a.constructors.length
  indices_length : is.length = p.node.a.family.indices.length
  parameters_fit : TelFits M (valuation w σ) p.node.a.family.parameters ρ0 ps
  motive_fit : mo ∈ Ed M (den M (valuation w σ) (push ps ρ0)
    (policyMotiveType p.node.a.family p.node.a.policy))
  minors_fit : TelFits M (valuation w σ) p.node.a.minorTypes
    (vcons mo (push ps ρ0)) ms
  indices_fit : TelFits M (valuation w σ) p.node.a.family.indices (push ps ρ0) is
  major_fit : den M σ ρ (ctorMajor w) ∈ Ed M
    (fapps (M.μ p.node.a.family.ref
      ((policyFamilyLevels p.node.a.family).map (evalTotal (valuation w σ))))
      (ps ++ is))
  lhs_endpoint : Equiv (den M σ ρ (iotaLhsOf w))
    (EvalPlanValue.endValue M (valuation w σ) p
      (push (ps ++ mo :: (ms ++ (is ++ [den M σ ρ (ctorMajor w)]))) ρ0))

/-- Nonempty evaluation of the installed telescope forces every actual
argument into its stored dependent domain. No RHS premise is used. -/
theorem of_nonempty (M : Interp.{4}) (p : EvalPlan.Plan)
    (hRec : ∀ vs, Equiv (M.μ p.rr vs)
      (EvalPlanValue.memberValue M (σOf vs) p p.rm))
    {S : ResolvedEnv} (w : IotaWitness S)
    (hwr : w.recRef = p.rr) (hm : w.recMember = p.rm)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (hne : ¬ Equiv (den M σ ρ (iotaLhsOf w)) pempty) :
    ∃ ps mo ms is, Arguments M p w σ ρ ps mo ms is := by
  let a := p.node.a
  let τ := σOf (w.ls.map (evalTotal σ))
  let g := EvalPlanValue.endValue M τ p
  obtain ⟨hnp, hnM, hnq, _hfr⟩ := iota_align a w hwr hm
  have hk : a.minorTypes.length = a.constructors.length := a.minorCount
  have hrecμ := hRec (w.ls.map (evalTotal σ))
  change Equiv (M.μ p.rr (w.ls.map (evalTotal σ)))
    (piLam M τ g ρ0 p.rm.mtype) at hrecμ
  have hlhs : den M σ ρ (iotaLhsOf w) =
      fapps (M.μ p.rr (w.ls.map (evalTotal σ)))
        (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)]) := by
    unfold iotaLhsOf recCall
    rw [fapps_den_append_singleton, hwr]
    rfl
  have hpvl : (w.preMajor.map (den M σ ρ)).length =
      a.family.parameters.length + 1 + a.constructors.length + a.family.indices.length := by
    rw [List.length_map, w.hpre, hnp, hnM, hnq]
  rw [recType_eq a] at hrecμ
  have hne' : ¬ Equiv (fapps
      (piLam M τ g ρ0 (policyPi (recPreDomsOf a ++ [recMajorOf a]) (recResultOf a)))
      (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)])) pempty := fun he =>
    hne (by rw [hlhs]; exact (fapps_congr hrecμ _).trans he)
  have hlenD : (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)]).length =
      (recPreDomsOf a ++ [recMajorOf a]).length := by
    rw [List.length_append, List.length_append, hpvl, recPreDomsOf_length]
    rfl
  have hresp : EnvResp g := EvalPlanValue.endValue_resp M τ p
  have hfit := fits_of_fapps_ne M τ hresp (recResultOf a)
    (recPreDomsOf a ++ [recMajorOf a]) ρ0 _ hlenD hne'
  have heq := fapps_piLam M τ hresp (recResultOf a)
    (recPreDomsOf a ++ [recMajorOf a]) ρ0 _ hfit
  rw [show recResultOf a = foldApps (.bvar (a.minorTypes.length + a.family.indices.length + 1)) _ from rfl,
    piLam_foldApps M _ _ _ _ (fun _ _ h => Expr.noConfusion h)] at heq
  have hL : Equiv (den M σ ρ (iotaLhsOf w))
      (g (push (w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)]) ρ0)) := by
    rw [hlhs]
    exact (fapps_congr hrecμ _).trans heq
  obtain ⟨xs0, ys0, hxy, hf1, hf2⟩ := TelFits_split _ _ _ _ hfit
  have hx0 : xs0 = w.preMajor.map (den M σ ρ) := by
    exact (List.append_inj hxy.symm (by rw [hf1.length, hpvl, recPreDomsOf_length])).1
  subst xs0
  have hy0 : ys0 = [den M σ ρ (ctorMajor w)] := (List.append_cancel_left hxy).symm
  subst ys0
  have hmaj : den M σ ρ (ctorMajor w) ∈ Ed M
      (den M τ (push (w.preMajor.map (den M σ ρ)) ρ0) (recMajorOf a)) := hf2.1
  have hsplit := list_split4 (w.preMajor.map (den M σ ρ)) a.family.parameters.length
    a.constructors.length a.family.indices.length hpvl pempty
  generalize hps : (w.preMajor.map (den M σ ρ)).take a.family.parameters.length = ps at hsplit
  generalize hmo : (w.preMajor.map (den M σ ρ)).getD a.family.parameters.length pempty = mo at hsplit
  generalize hms : ((w.preMajor.map (den M σ ρ)).drop (a.family.parameters.length + 1)).take
    a.constructors.length = ms at hsplit
  generalize his : (w.preMajor.map (den M σ ρ)).drop
    (a.family.parameters.length + 1 + a.constructors.length) = is at hsplit
  have hpsl : ps.length = a.family.parameters.length := by rw [← hps, List.length_take]; omega
  have hmsl : ms.length = a.constructors.length := by
    rw [← hms, List.length_take, List.length_drop]
    omega
  have hisl : is.length = a.family.indices.length := by rw [← his, List.length_drop]; omega
  have henv : w.preMajor.map (den M σ ρ) ++ [den M σ ρ (ctorMajor w)] =
      ps ++ mo :: (ms ++ (is ++ [den M σ ρ (ctorMajor w)])) := by
    rw [hsplit]
    simp only [List.append_assoc, List.cons_append]
  rw [henv] at hL
  rw [hsplit, den_recMajor M _ a ps mo ms is _ hpsl (by rw [hmsl, hk]) hisl] at hmaj
  rw [hsplit] at hf1
  unfold recPreDomsOf at hf1
  obtain ⟨xa, xb, hxab, hfa, hfb⟩ := TelFits_split _ _ _ _ hf1
  have hxa : xa = ps := (List.append_inj hxab.symm (by rw [hfa.length, hpsl])).1
  subst xa
  have hxb : xb = mo :: (ms ++ is) := (List.append_cancel_left hxab).symm
  subst xb
  obtain ⟨ya, yb, hyab, hya, hyb⟩ := TelFits_split _ _ _ _ hfb.2
  have hya' : ya = ms := (List.append_inj hyab.symm (by rw [hya.length, hmsl, hk])).1
  subst ya
  have hyb' : yb = is := (List.append_cancel_left hyab).symm
  subst yb
  have hisfit : TelFits M τ a.family.indices (push ps ρ0) is := by
    apply (TelFits_liftFields M τ (mo :: ms) (push ps ρ0) a.family.indices [] is).mp
    show TelFits M τ (liftFields (ms.length + 1) a.family.indices 0)
      (push ms (vcons mo (push ps ρ0))) is
    rw [hmsl, ← hk]
    exact hyb
  exact ⟨ps, mo, ms, is,
    ⟨hsplit, hpsl, hmsl, hisl, hfa, hfb.1, hya, hisfit, hmaj, hL⟩⟩

end Rcic.F3.PSet.RecArguments

#print axioms Rcic.F3.PSet.RecArguments.of_nonempty
