import rcic.RcicF3PiCanonicalGroup
import rcic.RcicF3DEnv
/-! Complete admitted signatures read in each preceding constructor environment.
Transparent-body agreement preserves normalization and field views. The bounded
wrapper derives EnvSound and body regularity from ordinary prefix AllSound and
final-environment iota; it assumes neither at the full admission environment.
This is a Prop-family constructor component, not a group/A producer.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiCanonicalWalk
open Rcic.Declarative PiValueRule PiValueExtract PiCanonicalGroup

theorem telescope_env {E₁ E₂ : ResolvedEnv}
    (h : ∀ r ls, transparentBody E₁ r ls = transparentBody E₂ r ls) :
    ∀ fuel e, piTelescopeFuel E₁ fuel e = piTelescopeFuel E₂ fuel e
  | 0, _ => rfl
  | fuel + 1, e => by
      simp only [piTelescopeFuel, whnfFuel_congr_env h]
      cases hw : whnfFuel E₂ fuel e with
      | none => rfl
      | some w =>
          cases w with
          | pi A B =>
              dsimp only
              rw [telescope_env h fuel B]
          | bvar _ => rfl
          | sort _ => rfl
          | const _ _ => rfl
          | app _ _ => rfl
          | lam _ _ => rfl
          | letE _ _ _ => rfl
          | lit _ => rfl


theorem views_env {E₁ E₂ : ResolvedEnv}
    (h : ∀ r ls, transparentBody E₁ r ls = transparentBody E₂ r ls)
    {fuel f nu ar : Nat} {As : List (Expr Nat)} {fs : List FieldSpec}
    (hv : Views E₁ fuel f nu ar As fs) : Views E₂ fuel f nu ar As fs := by
  induction hv with
  | nil => exact .nil
  | @cons A a As fs hv ht ih =>
      refine .cons ?_ ih
      cases a with
      | plain B => exact hv
      | recursive ds args =>
          exact ⟨(telescope_env h (fuel - 1) A).symm.trans hv.1, hv.2⟩


theorem constructor_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E Ew : ResolvedEnv} {r n : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h : IotaDescriptorClause E a)
    (henv : ∀ r ls, transparentBody E r ls = transparentBody Ew r ls)
    (hfree : ∀ A ∈ a.family.parameters, occursConst a.family.ref A = false)
    (vs : List Nat) (hvs : vs.length = a.family.member.arity) (K : Nat → Nat)
    (hE : EnvSound (mkM P (upd μ a.family.ref (PiValue.table P μ
      (predicate P μ (a.family.parameters ++ a.family.indices) (constructors a h.fuelAt))
      (a.family.parameters ++ a.family.indices)))) (σOf vs) K Ew n)
    (hb : BodiesOK Ew (σOf vs) K)
    (hR : PiHereditary.BodiesRegular (mkM P (upd μ a.family.ref (PiValue.table P μ
      (predicate P μ (a.family.parameters ++ a.family.indices) (constructors a h.fuelAt))
      (a.family.parameters ++ a.family.indices)))) (σOf vs) K Ew)
    (i : Fin (constructors a h.fuelAt).length) {u : Level}
    (d : HasTyT Ew n [] a.constructors[(index a h.fuelAt i).val].mtype (.sort u))
    (hd : LOKt (σOf vs) 4 K d) :
    let M := mkM P (upd μ a.family.ref (PiValue.table P μ
      (predicate P μ (a.family.parameters ++ a.family.indices) (constructors a h.fuelAt))
      (a.family.parameters ++ a.family.indices)))
    let T := a.constructors[(index a h.fuelAt i).val].mtype
    piLam M (σOf vs) (fun _ => pempty) ρ0 T ∈ Ed M (den M (σOf vs) ρ0 T) := by
  let j := index a h.fuelAt i
  let cv := a.constructorViews j
  obtain ⟨fs, hv, hf⟩ := slot_spec a h j
  have hv' : Views Ew (h.fuelAt j) a.family.ref vs.length
      (a.family.parameters ++ a.family.indices).length cv.fields fs := by
    rw [hvs]
    exact views_env henv hv
  have hc : ((constructors a h.fuelAt)[i.val]).fields =
      a.family.parameters.map FieldSpec.plain ++ fs := (congrArg Constructor.fields
        (lookup a h.fuelAt i)).trans hf
  have hr : ((constructors a h.fuelAt)[i.val]).result =
      policyParameterLocals cv.parameters.length cv.fields.length ++ cv.resultIndices := by
    rw [lookup]
    rfl
  have hresult : ∀ e ∈ policyParameterLocals cv.parameters.length cv.fields.length ++
      cv.resultIndices, occursConst a.family.ref e = false := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · simp only [policyParameterLocals, List.mem_map] at he
      obtain ⟨k, _, rfl⟩ := he
      rfl
    · exact cv.noFamilyInIndices e he
  have ht : a.constructors[j.val].mtype = policyPi (cv.parameters ++ cv.fields)
      (foldApps (.const a.family.ref ((List.range vs.length).map Level.param))
        (policyParameterLocals cv.parameters.length cv.fields.length ++ cv.resultIndices)) := by
    rw [cv.storedType]
    simp only [policyFamilyLevels, hvs]
  generalize he : a.constructors[j.val].mtype = T at d hd ⊢
  rw [he] at ht
  cases ht
  exact PiCanonicalParams.constructor_mem P μ a.family.ref a.family.parameters
    a.family.indices (constructors a h.fuelAt) vs i cv.parameters cv.fields
    cv.resultIndices fs cv.parameterCount cv.indexCount hfree hv' hc hr hresult
    K hE hb hR d hd


/-- The actual preceding walk environment pays semantic conditions from its
ordinary invariant; the full admission environment is used only for reading. -/
theorem constructor_mem_of_bound (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {S E₀ E E' Ew Efin : ResolvedEnv} {ms : List (Nat × CheckedMember)}
    (hmem : GroupMembersT S E₀ ms E')
    (hW : EnvWfT E₀) (K : Nat → Nat) (hB : BoundG K hW)
    (hsubE : ∀ r m, E₀.members r = some m → E.members r = some m)
    (hsubE' : ∀ r m, E.members r = some m → E'.members r = some m)
    (hsubw : ∀ r m, E₀.members r = some m → Ew.members r = some m)
    (hsubw' : ∀ r m, Ew.members r = some m → E'.members r = some m)
    (hfin : ∀ r m, Ew.members r = some m → Efin.members r = some m)
    {r n : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h : IotaDescriptorClause E a)
    (hfree : ∀ A ∈ a.family.parameters, occursConst a.family.ref A = false)
    (vs : List Nat) (hvs : vs.length = a.family.member.arity)
    (i : Fin (constructors a h.fuelAt).length) {u : Level}
    (d : HasTyT Ew n [] a.constructors[(index a h.fuelAt i).val].mtype (.sort u))
    (hd : LOKt (σOf vs) 4 K d) :
    let ν := upd μ a.family.ref (PiValue.table P μ
      (predicate P μ (a.family.parameters ++ a.family.indices) (constructors a h.fuelAt))
      (a.family.parameters ++ a.family.indices))
    AllSound P ν K Ew →
    (∀ r m, Ew.members r = some m → m.mclass = .recursorM → IotaAt P ν K Efin r) →
    let M := mkM P ν
    let T := a.constructors[(index a h.fuelAt i).val].mtype
    piLam M (σOf vs) (fun _ => pempty) ρ0 T ∈ Ed M (den M (σOf vs) ρ0 T) := by
  dsimp only
  intro hAw hIw
  have hnew : ∀ r m, Ew.members r = some m → E₀.members r = none → m.body = none := by
    intro r m hm h0
    rcases groupMembersT_cases hmem r m (hsubw' r m hm) with hbase | hgroup
    · rw [hbase] at h0
      cases h0
    · exact groupMembersT_body_none hmem r m hgroup
  have henv : ∀ r ls, transparentBody E r ls = transparentBody Ew r ls := by
    intro r ls
    exact (transparentBody_eq_base hmem hsubE hsubE' r ls).symm.trans
      (transparentBody_eq_base hmem hsubw hsubw' r ls)
  refine constructor_mem P μ a h henv hfree vs hvs K
    (envSound_of P hfin hAw hIw (σOf vs) n)
    (bodiesOK_of_envWfT K hW hB hsubw hnew (σOf vs)) ?_ i d hd
  exact PiHereditary.bodiesRegular_of_bound P _ K hW hB
    (allSound_prefix hsubw hAw) (fun r m hm hk => hIw r m (hsubw r m hm) hk)
    (fun r m hm => hfin r m (hsubw r m hm)) hsubw hnew (σOf vs)


end Rcic.F3.PSet.PiCanonicalWalk
