import rcic.RcicF3NormPropCtor
import rcic.RcicF3RawFamilyWalk

/-!
# Stored data constructors for the normalized family interpretation

The original own-parameter telescope is retained. Actual bounded field
typing supplies its SmallAlong bound, and inhabited normalization preserves
that bound at the same values and complete result key. Thus constructor
typing needs an admissible closed normalized frame, without a global
raw-family comparison or an extra normalization callback.

The frame and the ordinary walk environments remain explicit component
inputs here. Their universal production and universal A remain open.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.NormDataCtor
open Rcic.Declarative Rcic.Model.PS RawFamily PiIndex

/-- Both original result typehood and actual field-set bounds are retained.
Inhabited forward normalization pays the constructor closure inputs. -/
theorem value_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (p : EvalPlan.Plan) (C : Frame)
    (hC : Admissible (EvalPlanNormal.fd p) C)
    (hc : Closed P μ (EvalPlanNormal.fd p) C)
    (vs : List Nat) (hvs : vs.length = p.node.a.family.member.arity)
    (j : Fin p.node.a.constructors.length)
    (hf : ∀ us, Equiv (μ p.node.a.family.ref us)
      (ofFrame P μ (EvalPlanNormal.fd p) C us))
    (hδ : DeltaNormalize.BodyEquations (mkM P μ) p.node.E0 (σOf vs))
    (hsmall : evalTotal (σOf vs) p.node.a.family.resultLevel ≠ 0 →
      ∀ ps xs, TelFits (mkM P μ) (σOf vs) (p.node.a.constructorViews j).parameters ρ0 ps →
        TelFits (mkM P μ) (σOf vs) (p.node.a.constructorViews j).fields (push ps ρ0) xs →
        SmallAlong (mkM P μ) (σOf vs) (W4 (evalTotal (σOf vs) p.node.a.family.resultLevel))
          (p.node.a.constructorViews j).fields (push ps ρ0) xs)
    (htyp : ∀ zs, TelFits (mkM P μ) (σOf vs)
        ((p.node.a.constructorViews j).parameters ++ (p.node.a.constructorViews j).fields)
        ρ0 zs → ∃ v,
      den (mkM P μ) (σOf vs) (push zs ρ0)
        (foldApps (.const p.node.a.family.ref (policyFamilyLevels p.node.a.family))
          (policyParameterLocals (p.node.a.constructorViews j).parameters.length
            (p.node.a.constructorViews j).fields.length ++
            (p.node.a.constructorViews j).resultIndices)) ∈
        Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push zs ρ0) (.sort v))) :
    piLam (mkM P μ) (σOf vs)
        (ctorEnd (mkM P μ) (σOf vs) (EvalPlanNormal.fd p) j.val
          (p.node.a.constructorViews j).fields.length) ρ0
        (p.node.a.constructors[j.val]).mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0
        (p.node.a.constructors[j.val]).mtype) := by
  let M := mkM P μ
  let fd := EvalPlanNormal.fd p
  let cv := p.node.a.constructorViews j
  rw [cv.storedType]
  refine piLam_mem M _ (ctorEnd_resp M _ fd j.val cv.fields.length) _ ρ0 ?_
  refine piGood_policyPi_fits M _ _ _ _ ρ0 fun zs hz => ?_
  refine piGood_foldApps M _ _ _ _ (fun _ _ h => Expr.noConfusion h) _ ?_
  obtain ⟨ps, xs, rfl, hps, hxs⟩ := TelFits_split cv.parameters cv.fields ρ0 zs hz
  have hpl : ps.length = cv.parameters.length := hps.length
  have hxl : xs.length = cv.fields.length := hxs.length
  have hlevels : policyFamilyLevels p.node.a.family =
      (List.range vs.length).map Level.param := by
    rw [hvs]
    rfl
  have hR : Equiv (den M (σOf vs) (push (ps ++ xs) ρ0)
      (foldApps (.const p.node.a.family.ref (policyFamilyLevels p.node.a.family))
        (policyParameterLocals cv.parameters.length cv.fields.length ++ cv.resultIndices)))
      (fapps (ofFrame P μ fd C vs)
        (ps ++ cv.resultIndices.map (den M (σOf vs) (push xs (push ps ρ0))))) := by
    rw [hlevels, den_foldApps, List.map_append, ← hpl, ← hxl, den_paramLocals]
    change Equiv (fapps (μ p.node.a.family.ref
      (((List.range vs.length).map Level.param).map (evalTotal (σOf vs)))) _) _
    rw [map_param_σOf, push_append]
    exact fapps_congr (hf vs) _
  obtain ⟨v, hv0⟩ := htyp (ps ++ xs) hz
  have hv := mem_congr_left hR hv0
  have hne := ne_of_mem_sort (M := M) rfl hv
  have hfit : TelFits M (σOf vs) (fd.params ++ fd.indices) ρ0
      (ps ++ cv.resultIndices.map (den M (σOf vs) (push xs (push ps ρ0)))) :=
    fits_of_fapps_ne M (σOf vs)
      (endValue_resp C vs (fd.params.length + fd.indices.length)) (.sort fd.resLevel)
      (fd.params ++ fd.indices) ρ0 _
      (by
        rw [List.length_append, List.length_append, List.length_map,
          hpl, cv.parameterCount, cv.indexCount]
        rfl) hne
  have he := hR.trans (apply_ofFrame P μ fd C vs _ hfit)
  refine mem_congr_right ((ed_congr M he).trans
    (ed_tyv M (admissible_dich hC vs _))).symm ?_
  have hp : TelFits M (σOf vs) fd.params ρ0 ps :=
    telFits_prefix M (σOf vs) fd.params fd.indices ρ0 ps _
      (hpl.trans cv.parameterCount) hfit
  have hn := EvalPlanNormal.fields_forward M p.node.E0 (σOf vs) hδ
    (p.constructors j).fields (push ps ρ0) xs hxs
  let jn : Fin fd.ctors.length :=
    ⟨j.val, by simpa only [fd, EvalPlanNormal.ctors_length] using j.isLt⟩
  have hi : EvalPlanNormal.index p jn = j := Fin.ext rfl
  have hg := EvalPlanNormal.ctor_get p jn
  rw [hi] at hg
  have hh := ctor_end_mem P μ fd C hc hf vs jn ps xs hp
    (by rw [hg]; exact hn.1)
    (by rw [hg]; intro hne; exact (hn.2 _).mp (hsmall hne ps xs hps hxs))
  rw [hg] at hh
  rw [← hxl]
  exact hh

/-- The original stored constructor is sound at its own instance bound.
The supplied field-size producer concerns the original own telescope. -/
theorem member_sound_of_inputs (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (p : EvalPlan.Plan)
    (C : Frame) (hC : Admissible (EvalPlanNormal.fd p) C)
    (hc : Closed P μ (EvalPlanNormal.fd p) C)
    (j : Fin p.node.a.constructors.length)
    (hTF : TypeFacts p.E')
    (hbody : (p.node.a.constructors[j.val]).body = none)
    (hF : ∀ vs, Equiv (μ (p.f + 1 + j.val) vs)
      (piLam (mkM P μ) (σOf vs)
        (ctorEnd (mkM P μ) (σOf vs) (EvalPlanNormal.fd p) j.val
          (nfOf (EvalPlanNormal.fd p) j.val)) ρ0
        (p.node.a.constructors[j.val]).mtype))
    (hf : ∀ vs, Equiv (μ p.node.a.family.ref vs)
      (ofFrame P μ (EvalPlanNormal.fd p) C vs))
    (hδ : ∀ vs, DeltaNormalize.BodyEquations (mkM P μ) p.node.E0 (σOf vs))
    (htyp : ∀ vs, vs.length = p.node.a.family.member.arity →
      (∀ v, v ∈ vs → v ≤ K (p.f + 1 + j.val)) →
      ∀ zs, TelFits (mkM P μ) (σOf vs)
        ((p.node.a.constructorViews j).parameters ++ (p.node.a.constructorViews j).fields)
        ρ0 zs → ∃ v,
      den (mkM P μ) (σOf vs) (push zs ρ0)
        (foldApps (.const p.node.a.family.ref (policyFamilyLevels p.node.a.family))
          (policyParameterLocals (p.node.a.constructorViews j).parameters.length
            (p.node.a.constructorViews j).fields.length ++
              (p.node.a.constructorViews j).resultIndices)) ∈
        Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push zs ρ0) (.sort v)))
    (hsmall : ∀ vs, vs.length = p.node.a.family.member.arity →
      (∀ v, v ∈ vs → v ≤ K (p.f + 1 + j.val)) →
      evalTotal (σOf vs) p.node.a.family.resultLevel ≠ 0 →
      ∀ ps xs, TelFits (mkM P μ) (σOf vs) (p.node.a.constructorViews j).parameters ρ0 ps →
        TelFits (mkM P μ) (σOf vs) (p.node.a.constructorViews j).fields (push ps ρ0) xs →
        SmallAlong (mkM P μ) (σOf vs) (W4 (evalTotal (σOf vs) p.node.a.family.resultLevel))
          (p.node.a.constructorViews j).fields (push ps ρ0) xs) :
    MemberSound P μ K (p.f + 1 + j.val) (p.node.a.constructors[j.val]) := by
  have hctor := node_ctor_member p.node j
  intro σ ls ρ hlen hlevels
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  have hvs : (ls.map (evalTotal σ)).length = p.node.a.family.member.arity := by
    rw [List.length_map, hlen, (p.node.a.constructorViews j).arity]
  have hbound : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K (p.f + 1 + j.val) := by
    intro v hv
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
    exact hlevels l hl
  rw [den_inst_canon (mkM P μ) σ ls ρ (p.node.a.constructors[j.val]).mtype
    (hTF _ _ hctor).1 (hlen ▸ (hTF _ _ hctor).2.1)]
  refine mem_congr_left (hF _).symm ?_
  rw [NormPropCtor.field_count]
  exact value_mem P μ p C hC hc (ls.map (evalTotal σ)) hvs j hf (hδ _)
    (hsmall _ hvs hbound) (htyp _ hvs hbound)

/-- The actual constructor walk produces the original field-size and result
typehood inputs. Its own parameter cut may differ from the recursor cut. -/
theorem constructor_at_walk (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) (p : EvalPlan.Plan) {Ew : ResolvedEnv} {fm : CheckedMember}
    (i : Fin p.node.a.constructors.length)
    (fam : PolicyFamilyView Ew)
    (cv : PolicyConstructorView Ew fam (p.node.a.constructors[i.val]))
    (hsub : ∀ r m, Ew.members r = some m → p.E'.members r = some m)
    (C : Frame) (hC : Admissible (EvalPlanNormal.fd p) C)
    (hc : Closed P μ (EvalPlanNormal.fd p) C)
    (hfam : ∀ vs, Equiv (μ p.node.a.family.ref vs)
      (ofFrame P μ (EvalPlanNormal.fd p) C vs))
    (hF : ∀ vs, Equiv (μ (p.f + 1 + i.val) vs)
      (piLam (mkM P μ) (σOf vs)
        (ctorEnd (mkM P μ) (σOf vs) (EvalPlanNormal.fd p) i.val
          (nfOf (EvalPlanNormal.fd p) i.val)) ρ0 (p.node.a.constructors[i.val]).mtype))
    (hδ : ∀ vs, DeltaNormalize.BodyEquations (mkM P μ) p.node.E0 (σOf vs))
    (hTF : TypeFacts p.E') (hbody : (p.node.a.constructors[i.val]).body = none)
    (h07 : FieldUniverseAdmitted cv)
    (hag : AgreeAt p.node.a.family.parameters.length Ew fam _ cv)
    (hES : ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv p.E p.f fm) n)
    (hEw : ∀ σ n, EnvSound (mkM P μ) σ K Ew n)
    (hB1 : ∀ vs : List Nat, vs.length = p.node.a.family.member.arity →
      (∀ v, v ∈ vs → v ≤ K (p.f + 1 + i.val)) →
      ∃ (u : Level) (d : HasTyT (extendEnv p.E p.f fm) p.node.a.family.member.arity []
        (p.node.a.constructors[i.val]).mtype (.sort u)), LOKt (σOf vs) 4 K d)
    (hB2 : ∀ vs : List Nat, vs.length = fam.member.arity →
      (∀ v, v ∈ vs → v ≤ K (p.f + 1 + i.val)) →
      ∀ k : Fin (cv.parameters ++ cv.fields).length,
      ∃ d : HasTyT Ew fam.member.arity
        (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
        ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)),
        LOKt (σOf vs) 4 K d) :
    MemberSound P μ K (p.f + 1 + i.val) (p.node.a.constructors[i.val]) := by
  have hstO := cv.storedType
  have hstR := (p.node.a.constructorViews i).storedType
  have hspl := policyPi_split_eq _ _ _ _
    (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
    (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
    (hstO.symm.trans hstR)
  have hcat := hspl.1
  have href : fam.ref = p.node.a.family.ref := foldApps_const_head hspl.2
  have hfamO : fam.member = p.node.a.family.member := by
    have h := hsub fam.ref fam.member fam.present
    rw [href, p.node.fam] at h
    exact Option.some.inj (h.symm.trans (node_fam_member p.node))
  have hres : fam.resultLevel = p.node.a.family.resultLevel := by
    have h1 := fam.storedType
    have h2 := p.node.a.family.storedType
    rw [hfamO] at h1
    have he := (policyPi_split_eq _ _ _ _ (expr_not_pi_of_sort _)
      (expr_not_pi_of_sort _) (h1.symm.trans h2)).2
    injection he
  have har : fam.member.arity = p.node.a.family.member.arity := by rw [hfamO]
  refine member_sound_of_inputs P μ K p C hC hc i hTF hbody hF hfam hδ ?_ ?_
  · intro vs hvl hbd zs hz
    obtain ⟨u, d, hd⟩ := hB1 vs hvl hbd
    have hs := hsound_ty (P.good _ rfl) (hES (σOf vs) _) d hd
    exact tel_end_type' _ _ d (p.node.a.constructorViews i).storedType hs ρ0 zs True.intro hz
  · intro vs hvl hbd h0 ps xs hp hx
    have hvlO : vs.length = fam.member.arity := by rw [har]; exact hvl
    have hg : AgreeAt (p.node.a.constructorViews i).parameters.length Ew fam _ cv := by
      rw [(p.node.a.constructorViews i).parameterCount]
      exact hag
    have h0O : evalTotal (σOf vs) fam.resultLevel ≠ 0 := by rw [hres]; exact h0
    have hs := RawFamilyWalk.fields_small P μ K fam cv
      (p.node.a.constructorViews i).parameters (p.node.a.constructorViews i).fields
      hcat.symm h07 hg vs (hEw _ _) (hB2 vs hvlO hbd) h0O ps xs hp hx
    rw [hres] at hs
    exact hs

end Rcic.F3.PSet.NormDataCtor
