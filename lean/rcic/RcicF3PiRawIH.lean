import rcic.RcicF3PiSyntaxIH
import rcic.RcicF3PiRawMotive
import rcic.RcicF3PiTypedCompile
/-! General-depth IH type fidelity for normalized recursive fields.
Actual field membership recovers fitting indices from the constructed family
table; ordinary proof-motive typing pays leaf exactness. The raw group and
minor assembly remain open. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawIH
open Rcic.Declarative PiIndex
universe u

theorem fits_tail (M : Interp.{u}) (σ : Nat → Nat)
    (ds es : List (Expr Nat)) (ρ : Nat → PSet.{u}) (xs ys : List PSet.{u})
    (hl : xs.length = ds.length) (h : TelFits M σ (ds ++ es) ρ (xs ++ ys)) :
    TelFits M σ es (push xs ρ) ys := by
  induction ds generalizing ρ xs with
  | nil =>
    cases xs with
    | nil => exact h
    | cons _ _ => exact False.elim (Nat.noConfusion hl)
  | cons A ds ih =>
    cases xs with
    | nil => exact False.elim (Nat.noConfusion hl)
    | cons x xs => exact ih (vcons x ρ) xs (Nat.succ.inj hl) h.2

def fieldApp (n : Nat) : Expr Nat := foldApps (.bvar n) (policyLocals n)

/-- Elementary de Bruijn evaluation, including depth zero. -/
theorem den_fieldApp (M : Interp.{u}) (σ : Nat → Nat) (ρ : Nat → PSet.{u})
    (xs : List PSet.{u}) :
    den M σ (push xs ρ) (fieldApp xs.length) = fapps (ρ 0) xs := by
  rw [fieldApp, den_foldApps, den_policyLocals]
  change fapps (push xs ρ xs.length) xs = _
  rw [show xs.length = 0 + xs.length by omega, push_ge]

/-- The admitted motive type supplies a genuine type value at fitting majors. -/
theorem motive_tagged {M : Interp.{4}} (hU : M.U = U W4)
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (vs : List Nat)
    (ps is : List PSet.{4}) (mo z : PSet.{4})
    (hps : ps.length = a.family.parameters.length) (hpol : a.policy = .propOnly)
    (hmo : mo ∈ Ed M (den M (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (his : TelFits M (σOf vs) a.family.indices (push ps ρ0) is)
    (hz : z ∈ Ed M (fapps
      (M.μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (ps ++ is))) :
    Equiv (tyv (Ed M (fapps mo (is ++ [z])))) (fapps mo (is ++ [z])) := by
  have hmt : policyMotiveType a.family a.policy = policyPi (a.family.indices ++
      [foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyLocals (a.family.parameters.length + a.family.indices.length))]) (.sort .zero) := by
    rw [hpol, policyPi_append]; rfl
  rw [hmt] at hmo
  have hzF : z ∈ Ed M (den M (σOf vs) (push is (push ps ρ0))
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyLocals (a.family.parameters.length + a.family.indices.length)))) := by
    have hF := Fapp_den M (σOf vs) a.family.ref (policyFamilyLevels a.family) ps is ρ0
    rw [hps, his.length] at hF
    rw [hF]; exact hz
  have ht := mem_fapps M (σOf vs) (.sort .zero) _ (push ps ρ0) mo (is ++ [z]) hmo
    (TelFits.append his ⟨hzF, trivial⟩)
  have hsort : den M (σOf vs) (push (is ++ [z]) (push ps ρ0)) (.sort .zero) =
      tyv (M.U 0) := rfl
  rw [hsort, hU] at ht
  exact PiTypedCompile.tyv_ed_of_mem_U M W4 0
    (mem_congr_right (ed_tyv M (U4_dich 0)) ht)
/-- Exact normalized raw IH types for the constructed family table. Parameter
readback is a structural equation, not a recursive-field or motive wall. -/
theorem normalized_spec (M : Interp.{4}) (hU : M.U = U W4) (σ : Nat → Nat)
    (f : Nat) (ls : List Level) (φ : Index.{4} → Prop)
    (Ps Is : List (Expr Nat)) (ps : List PSet.{4}) (hps : ps.length = Ps.length)
    (hF : Equiv (M.μ f (ls.map (evalTotal σ)))
      (PiValue.value M σ φ (Ps ++ Is) ρ0))
    (mo : PSet.{4})
    (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi Is (.pi (foldApps (.const f ls) (policyLocals (Ps.length + Is.length)))
        (.sort .zero)))))
    (ds args : List (Expr Nat)) (ha : args.length = (Ps ++ Is).length)
    (ρ : Nat → PSet.{4})
    (hprefix : ∀ xs, TelFits M σ ds ρ xs →
      (args.take Ps.length).map (den M σ (push xs ρ)) = ps)
    (Mx : Expr Nat) (hMx : den M σ ρ Mx = mo)
    (hx : ρ 0 ∈ Ed M (den M σ ρ
      (policyPi ds (foldApps (.const f ls) args)))) :
    Equiv ((PiIndex.tel M σ ds args ρ).erasedIHType M
      (PiRawMotive.guarded M σ (M.μ f (ls.map (evalTotal σ))) mo ps Is (push ps ρ0))
      (ρ 0))
      (den M σ ρ (policyPi ds (foldApps (Rcic.Declarative.lift 0 ds.length Mx)
        (args.drop Ps.length ++ [fieldApp ds.length])))) := by
  let F := M.μ f (ls.map (evalTotal σ))
  let C := PiRawMotive.guarded M σ F mo ps Is (push ps ρ0)
  apply PiSyntaxIH.compile_spec M σ (read M σ args) C
    (PiRawMotive.guarded_dich M σ F mo ps Is (push ps ρ0))
  apply (PiSyntaxIH.endEq_iff M σ (read M σ args) C _ ds ρ (ρ 0)).mpr
  intro xs hxs
  let js := (args.drop Ps.length).map (den M σ (push xs ρ))
  let z := fapps (ρ 0) xs
  have he : args.map (den M σ (push xs ρ)) = ps ++ js := by
    have he := congrArg (fun as => as.map (den M σ (push xs ρ)))
      (List.take_append_drop Ps.length args)
    dsimp only at he
    rw [List.map_append, hprefix xs hxs] at he
    exact he.symm
  have hz : z ∈ Ed M (fapps F (ps ++ js)) := by
    have ht := mem_fapps M σ (foldApps (.const f ls) args) ds ρ (ρ 0) xs hx hxs
    rw [den_foldApps, he] at ht
    exact ht
  have hl : (ps ++ js).length = (Ps ++ Is).length := by
    rw [← he, List.length_map, ha]
  have hfit := (PiValue.apply_mem_iff M σ φ (Ps ++ Is) ρ0 (ps ++ js) hl z).mp
    (mem_congr_right (ed_congr M (fapps_congr hF (ps ++ js))) hz)
  have his := fits_tail M σ Ps Is ρ0 ps js hps hfit.1
  have hmo' : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi (Is ++ [foldApps (.const f ls) (policyLocals (Ps.length + Is.length))])
        (.sort .zero))) := by
    rw [policyPi_append]; exact hmo
  have hzF : z ∈ Ed M (den M σ (push js (push ps ρ0))
      (foldApps (.const f ls) (policyLocals (Ps.length + Is.length)))) := by
    have hF := Fapp_den M σ f ls ps js ρ0
    rw [hps, his.length] at hF
    rw [hF]; exact hz
  have htype := mem_fapps M σ (.sort .zero) _ (push ps ρ0) mo (js ++ [z]) hmo'
    (TelFits.append his ⟨hzF, True.intro⟩)
  have hsort : den M σ (push (js ++ [z]) (push ps ρ0)) (.sort .zero) = tyv (M.U 0) := rfl
  rw [hsort, hU] at htype
  have hU0 := mem_congr_right (ed_tyv M (U4_dich 0)) htype
  have hguard := PiRawMotive.guarded_key M σ F mo ps Is (push ps ρ0) js z his hz
    (fun y hy => ed_of_mem_U0 M hU0 hy)
  have htag := PiTypedCompile.tyv_ed_of_mem_U M W4 0 hU0
  have hr : read M σ args (push xs ρ) = key (ps ++ js) := congrArg key he
  change Equiv (tyv (C (read M σ args (push xs ρ)) z)) _
  rw [hr]
  have hden : den M σ (push xs ρ)
      (foldApps (Rcic.Declarative.lift 0 ds.length Mx)
        (args.drop Ps.length ++ [fieldApp ds.length])) = fapps mo (js ++ [z]) := by
    rw [den_foldApps, ← hxs.length, den_lift0_push, hMx,
      List.map_append, List.map_cons, List.map_nil, den_fieldApp]
  rw [hden]
  exact (tyv_congr hguard).trans htag
/-- Elementary readback of the executable IH builder, with unrestricted depth. -/
theorem funIHType_eq (E : ResolvedEnv) (fuel np : Nat) (A M : Expr Nat)
    (ds args : List (Expr Nat)) (f : Nat) (ls : List Level)
    (hread : piTelescopeFuel E fuel (Rcic.Declarative.lift 0 1 A) =
      some (ds, foldApps (.const f ls) args)) :
    funIHType E fuel np A M ds.length = some (policyPi ds
      (foldApps (Rcic.Declarative.lift 0 ds.length (Rcic.Declarative.lift 0 1 M))
        (args.drop np ++ [fieldApp ds.length]))) := by
  simp only [funIHType, hread, if_pos rfl, familyIdx_foldApps_const]
  rfl
/-- Elementary composition with the executable recursor IH builder. -/
theorem builder_spec (M : Interp.{4}) (hU : M.U = U W4) (σ : Nat → Nat)
    (f : Nat) (ls : List Level) (φ : Index.{4} → Prop)
    (Ps Is : List (Expr Nat)) (ps : List PSet.{4}) (hps : ps.length = Ps.length)
    (hF : Equiv (M.μ f (ls.map (evalTotal σ)))
      (PiValue.value M σ φ (Ps ++ Is) ρ0))
    (mo : PSet.{4})
    (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi Is (.pi (foldApps (.const f ls) (policyLocals (Ps.length + Is.length)))
        (.sort .zero)))))
    (E : ResolvedEnv) (fuel : Nat) (A : Expr Nat)
    (ds args : List (Expr Nat)) (ha : args.length = (Ps ++ Is).length)
    (ρ : Nat → PSet.{4})
    (hprefix : ∀ xs, TelFits M σ ds ρ xs →
      (args.take Ps.length).map (den M σ (push xs ρ)) = ps)
    (Mx : Expr Nat) (hMx : den M σ ρ (Rcic.Declarative.lift 0 1 Mx) = mo)
    (hread : piTelescopeFuel E fuel (Rcic.Declarative.lift 0 1 A) =
      some (ds, foldApps (.const f ls) args))
    (ih : Expr Nat) (hih : funIHType E fuel Ps.length A Mx ds.length = some ih)
    (hx : ρ 0 ∈ Ed M (den M σ ρ
      (policyPi ds (foldApps (.const f ls) args)))) :
    Equiv ((PiIndex.tel M σ ds args ρ).erasedIHType M
      (PiRawMotive.guarded M σ (M.μ f (ls.map (evalTotal σ))) mo ps Is (push ps ρ0))
      (ρ 0))
      (den M σ ρ ih) := by
  have he := funIHType_eq E fuel Ps.length A Mx ds args f ls hread
  have hi := Option.some.inj (he.symm.trans hih)
  rw [← hi]
  exact normalized_spec M hU σ f ls φ Ps Is ps hps hF mo hmo ds args ha ρ
    hprefix (Rcic.Declarative.lift 0 1 Mx) hMx hx
end Rcic.F3.PSet.PiRawIH
