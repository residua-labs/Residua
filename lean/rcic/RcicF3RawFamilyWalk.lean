import rcic.RcicF3RawFamilyCtor
import rcic.RcicF3RoleGroup
/-!
# Stored constructors over the raw repaired frame

The bounded constructor walk derives original result typehood and all field
size bounds, including differing parameter cuts. Literal data constructors
then inhabit their original stored types without a family fixed-point premise.
Admissibility and closure of the proposed frame are still component inputs;
producing the universal frame and raw recursor remains open. This module adds
no apex hypothesis. `closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawFamilyWalk
open Rcic.Declarative Rcic.Model.PS RawFamily
theorem ctor_member_sound (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {c : Nat}
    {cm : CheckedMember} (fd : FamData) (C : Frame) (hC : Admissible fd C) (hc : Closed P μ fd C) (j : Nat) (cps fs ri : List (Expr Nat))
    (hj : fd.ctors[j]? = some (fs, ri)) (hnp : cps.length = fd.params.length) (hq : ri.length = fd.indices.length)
    (hst : cm.mtype = policyPi (cps ++ fs) (foldApps (.const fd.fref ((List.range cm.arity).map Level.param))
      (policyParameterLocals cps.length fs.length ++ ri)))
    (hcl : ∀ k, Rcic.Declarative.lift k 1 cm.mtype = cm.mtype)
    (hlvl : exprLevelsBounded cm.arity cm.mtype = true) (hbody : cm.body = none)
    (hF : ∀ vs, Equiv (μ c vs)
      (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) fd j (nfOf fd j)) ρ0 cm.mtype))
    (hfam : ∀ vs, Equiv (μ fd.fref vs) (ofFrame P μ fd C vs))
    (htyp : ∀ vs, vs.length = cm.arity → (∀ v, v ∈ vs → v ≤ K c) →
      ∀ zs, TelFits (mkM P μ) (σOf vs) (cps ++ fs) ρ0 zs → ∃ v,
      den (mkM P μ) (σOf vs) (push zs ρ0) (foldApps (.const fd.fref ((List.range vs.length).map Level.param))
        (policyParameterLocals cps.length fs.length ++ ri)) ∈
        Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push zs ρ0) (.sort v)))
    (hsmall : ∀ vs, vs.length = cm.arity → (∀ v, v ∈ vs → v ≤ K c) →
      evalTotal (σOf vs) fd.resLevel ≠ 0 → ∀ ps xs, TelFits (mkM P μ) (σOf vs) cps ρ0 ps →
      TelFits (mkM P μ) (σOf vs) fs (push ps ρ0) xs →
      SmallAlong (mkM P μ) (σOf vs) (W4 (evalTotal (σOf vs) fd.resLevel)) fs (push ps ρ0) xs) :
    MemberSound P μ K c cm := by
  intro σ ls ρ hlen hl
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  have hvl : (ls.map (evalTotal σ)).length = cm.arity := by rw [List.length_map, hlen]
  have hbd : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K c := by
    intro v hv
    obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hv
    exact hl l hl'
  rw [den_inst_canon (mkM P μ) σ ls ρ cm.mtype hcl (hlen ▸ hlvl)]
  refine mem_congr_left (hF _).symm ?_
  have hnf : nfOf fd j = fs.length := by unfold nfOf; rw [hj]
  rw [hnf, hst]
  have hst' : (List.range cm.arity).map Level.param = (List.range (ls.map (evalTotal σ)).length).map Level.param := by
    rw [hvl]
  rw [hst']
  exact ctor_value_mem P μ fd C hC hc (ls.map (evalTotal σ)) j cps fs ri hj hnp hq hfam
    (htyp _ hvl hbd) (hsmall _ hvl hbd)

/-- The walk's own bounded domain derivations supply every field-size bound,
even when its parameter cut differs from the recursor's cut. -/
theorem fields_small (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) {Ew : ResolvedEnv} {m : CheckedMember}
    (fam : PolicyFamilyView Ew) (cv : PolicyConstructorView Ew fam m)
    (Ps Fs : List (Expr Nat)) (hcat : Ps ++ Fs = cv.parameters ++ cv.fields)
    (h07 : FieldUniverseAdmitted cv) (hag : AgreeAt Ps.length Ew fam m cv)
    (vs : List Nat) (hE : EnvSound (mkM P μ) (σOf vs) K Ew fam.member.arity)
    (hB : ∀ k : Fin (cv.parameters ++ cv.fields).length,
      ∃ d : HasTyT Ew fam.member.arity
        (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
        ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)),
        LOKt (σOf vs) 4 K d)
    (h0 : evalTotal (σOf vs) fam.resultLevel ≠ 0)
    (ps xs : List PSet.{4})
    (hp : TelFits (mkM P μ) (σOf vs) Ps ρ0 ps)
    (hx : TelFits (mkM P μ) (σOf vs) Fs (push ps ρ0) xs) :
    SmallAlong (mkM P μ) (σOf vs) (W4 (evalTotal (σOf vs) fam.resultLevel))
      Fs (push ps ρ0) xs := by
  have hD : RefsIn (Dom Ew) (cv.parameters ++ cv.fields) := by
    intro A hA r hr
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hA
    obtain ⟨d, _⟩ := hB ⟨k, hk⟩
    exact hasTyT_denRefs d r hr
  have hlev : ∀ (j : Fin Fs.length)
      (hk : Ps.length + j.val < (cv.parameters ++ cv.fields).length),
      evalTotal (σOf vs) (cv.domainsTyped.levels ⟨Ps.length + j.val, hk⟩) ≤
        evalTotal (σOf vs) fam.resultLevel := by
    intro j hk
    rcases Nat.lt_or_ge (Ps.length + j.val) cv.parameters.length with hpar | hfld
    · rcases hag _ hk (by omega) hpar with hp | hle
      · exact absurd (hp _) h0
      · exact leN_evalTotal hle (σOf vs)
    · have hj : Ps.length + j.val - cv.parameters.length < cv.fields.length := by
        simp only [List.length_append] at hk
        omega
      let j' : Fin cv.fields.length := ⟨_, hj⟩
      have hi : (⟨Ps.length + j.val, hk⟩ : Fin (cv.parameters ++ cv.fields).length) =
          cv.fieldIndex j' := Fin.ext (by
            show Ps.length + j.val = cv.parameters.length +
              (Ps.length + j.val - cv.parameters.length)
            omega)
      rw [hi]
      rcases h07 j' with hp | ⟨_, hle⟩
      · exact absurd (hp _) h0
      · exact leN_evalTotal hle (σOf vs)
  exact field_small_gen P μ μ K (Epre := Ew) fam.member.arity
    (cv.parameters ++ cv.fields) Ps Fs hcat cv.domainsTyped.levels fam.resultLevel
    vs hE hB (fun _ _ _ => rfl) hD h0 hlev ps xs hp hx

/-- A real preceding constructor environment supplies original stored typing
and field bounds. Frame admissibility/closure and the two literal table entries
remain the semantic component inputs; no family fixed-point equation is used. -/
theorem constructor_at_walk (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (K : Nat → Nat) {E E' Ew : ResolvedEnv} {f rr : Nat} {rm fm : CheckedMember}
    (node : RecNode E E' f rr rm) (i : Fin node.a.constructors.length)
    (fam : PolicyFamilyView Ew)
    (cv : PolicyConstructorView Ew fam (node.a.constructors[i.val]))
    (hsub : ∀ r m, Ew.members r = some m → E'.members r = some m)
    (C : Frame) (hC : Admissible (famDataOf node.a) C)
    (hc : Closed P μ (famDataOf node.a) C)
    (hfam : ∀ vs, Equiv (μ node.a.family.ref vs)
      (ofFrame P μ (famDataOf node.a) C vs))
    (hF : ∀ vs, Equiv (μ (f + 1 + i.val) vs)
      (piLam (mkM P μ) (σOf vs)
        (ctorEnd (mkM P μ) (σOf vs) (famDataOf node.a) i.val
          (nfOf (famDataOf node.a) i.val)) ρ0 (node.a.constructors[i.val]).mtype))
    (hTF : TypeFacts E') (hbody : (node.a.constructors[i.val]).body = none)
    (h07 : FieldUniverseAdmitted cv)
    (hag : AgreeAt node.a.family.parameters.length Ew fam _ cv)
    (hE0 : ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n)
    (hEw : ∀ σ n, EnvSound (mkM P μ) σ K Ew n)
    (hB1 : ∀ vs : List Nat, vs.length = node.a.family.member.arity →
      (∀ v, v ∈ vs → v ≤ K (f + 1 + i.val)) →
      ∃ (u : Level) (d : HasTyT (extendEnv E f fm) node.a.family.member.arity []
        (node.a.constructors[i.val]).mtype (.sort u)), LOKt (σOf vs) 4 K d)
    (hB2 : ∀ vs : List Nat, vs.length = fam.member.arity →
      (∀ v, v ∈ vs → v ≤ K (f + 1 + i.val)) →
      ∀ k : Fin (cv.parameters ++ cv.fields).length,
      ∃ d : HasTyT Ew fam.member.arity
        (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
        ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)),
        LOKt (σOf vs) 4 K d) :
    MemberSound P μ K (f + 1 + i.val) (node.a.constructors[i.val]) := by
  have hstO := cv.storedType
  have hstR := (node.a.constructorViews i).storedType
  have hspl := policyPi_split_eq _ _ _ _
    (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
    (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
    (hstO.symm.trans hstR)
  have hcat := hspl.1
  have href : fam.ref = node.a.family.ref := foldApps_const_head hspl.2
  have hfamO : fam.member = node.a.family.member := by
    have h := hsub fam.ref fam.member fam.present
    rw [href, node.fam] at h
    exact Option.some.inj (h.symm.trans (node_fam_member node))
  have hres : fam.resultLevel = node.a.family.resultLevel := by
    have h1 := fam.storedType
    have h2 := node.a.family.storedType
    rw [hfamO] at h1
    have he := (policyPi_split_eq _ _ _ _ (expr_not_pi_of_sort _)
      (expr_not_pi_of_sort _) (h1.symm.trans h2)).2
    injection he
  have har : fam.member.arity = node.a.family.member.arity := by rw [hfamO]
  refine ctor_member_sound P (famDataOf node.a) C hC hc i.val
    (node.a.constructorViews i).parameters (node.a.constructorViews i).fields
    (node.a.constructorViews i).resultIndices (famDataOf_ctor node.a i)
    (node.a.constructorViews i).parameterCount (node.a.constructorViews i).indexCount ?_
    (hTF _ _ (node_ctor_member node i)).1
    (hTF _ _ (node_ctor_member node i)).2.1 hbody hF hfam ?_ ?_
  · rw [(node.a.constructorViews i).storedType, (node.a.constructorViews i).arity]
    rfl
  · intro vs hvl hbd zs hz
    obtain ⟨u, d, hd⟩ := hB1 vs (hvl.trans (node.a.constructorViews i).arity) hbd
    have hs := hsound_ty (P.good _ rfl) (hE0 (σOf vs) _) d hd
    have ht := tel_end_type' _ _ d (node.a.constructorViews i).storedType hs ρ0 zs True.intro hz
    have he : (List.range vs.length).map Level.param = policyFamilyLevels node.a.family := by
      rw [hvl, (node.a.constructorViews i).arity]
      rfl
    rw [he]
    exact ht
  · intro vs hvl hbd h0 ps xs hp hx
    have hvlO : vs.length = fam.member.arity := by
      rw [har, ← (node.a.constructorViews i).arity]
      exact hvl
    have hg : AgreeAt (node.a.constructorViews i).parameters.length Ew fam _ cv := by
      rw [(node.a.constructorViews i).parameterCount]
      exact hag
    have h0O : evalTotal (σOf vs) fam.resultLevel ≠ 0 := by rw [hres]; exact h0
    have hs := fields_small P μ K fam cv
      (node.a.constructorViews i).parameters (node.a.constructorViews i).fields
      hcat.symm h07 hg vs (hEw _ _) (hB2 vs hvlO hbd) h0O ps xs hp hx
    rw [hres] at hs
    exact hs

end Rcic.F3.PSet.RawFamilyWalk
