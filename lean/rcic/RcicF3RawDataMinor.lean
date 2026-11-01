import rcic.RcicF3RawFamilyMinor
import rcic.RcicF3PropEvalMotiveGuard

/-!
# Actual stored data minors at arbitrary recursive depth

The admitted minor derivation and ordinary typed minor tuple supply the
executable application. Its nonempty typed-motive endpoint recovers its
dependent index and major fitting proofs. This does not use proof erasure
or assume evaluation existence. The local recursive map is required only
below the current constructor, at its complete parameter/index key.

Admissible family interpretation, ordinary environment soundness and the
constructor's literal data-code equation remain explicit component inputs.
Universal frame existence and universal A are not asserted.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.RawDataMinor
open Rcic.Declarative PiIndex RawFamily PropEval

/-- A literal constructor abstraction, applied to its own fitting
parameter/field telescope, yields the original data code. The existing
checked parameter equality is used only to identify that own telescope. -/
theorem constructor_data (M : Interp.{4}) (σ : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}
    (node : RecNode E E' f rr rm) (j : Fin node.a.constructors.length)
    (ps xs : List PSet.{4})
    (h0 : evalTotal σ node.a.family.resultLevel ≠ 0)
    (hpar : (node.a.constructorViews j).parameters = node.a.family.parameters)
    (hps : TelFits M σ node.a.family.parameters ρ0 ps)
    (hxs : TelFits M σ (node.a.constructorViews j).fields (push ps ρ0) xs)
    (hctor : Equiv
      (M.μ (node.a.family.ref + 1 + j.val)
        ((policyFamilyLevels node.a.family).map (evalTotal σ)))
      (piLam M σ (ctorEnd M σ (famDataOf node.a) j.val
        (node.a.constructorViews j).fields.length) ρ0 (node.a.constructors[j.val]).mtype)) :
    Equiv (fapps (M.μ (node.a.family.ref + 1 + j.val)
      ((policyFamilyLevels node.a.family).map (evalTotal σ))) (ps ++ xs))
      (dataVal j.val xs) := by
  let c := node.a.constructorViews j
  have hp : TelFits M σ c.parameters ρ0 ps := by rw [hpar]; exact hps
  have he := fapps_congr hctor (ps ++ xs)
  rw [c.storedType] at he
  have ha := fapps_piLam M σ
    (ctorEnd_resp M σ (famDataOf node.a) j.val c.fields.length)
    (foldApps (.const node.a.family.ref (policyFamilyLevels node.a.family))
      (policyParameterLocals c.parameters.length c.fields.length ++ c.resultIndices))
    (c.parameters ++ c.fields) ρ0 (ps ++ xs) (TelFits.append hp hxs)
  rw [piLam_foldApps_const] at ha
  have hend : ctorEnd M σ (famDataOf node.a) j.val c.fields.length
      (push (ps ++ xs) ρ0) = dataVal j.val xs := by
    unfold ctorEnd
    change cond M.dec (evalTotal σ node.a.family.resultLevel = 0) pempty
      (dataVal j.val (lastVals (node.a.constructorViews j).fields.length
        (push (ps ++ xs) ρ0))) = dataVal j.val xs
    rw [cond_neg h0, push_append, ← hxs.length, lastVals_push]
  rw [hend] at ha
  exact he.trans ha

/-- A typed motive with an inhabited result supplies its own fitting index
and major arguments, at the complete key and the motive's actual universe. -/
theorem endpoint_guarded (M : Interp.{4}) (hU : M.U = U W4)
    (σ : Nat → Nat) (f : Nat) (ls : List Level)
    (Ps Is : List (Expr Nat)) (ps : List PSet.{4})
    (hps : ps.length = Ps.length) (mo : PSet.{4}) (v : Level)
    (hmo : mo ∈ Ed M (den M σ (push ps ρ0)
      (policyPi Is (.pi (foldApps (.const f ls)
        (policyLocals (Ps.length + Is.length))) (.sort v)))))
    (is : List PSet.{4}) (major out : PSet.{4})
    (hlen : is.length = Is.length)
    (hout : out ∈ Ed M (fapp (fapps mo is) major)) :
    out ∈ PiRawMotiveAny.guarded M σ (evalTotal σ v)
      (M.μ f (ls.map (evalTotal σ))) mo ps Is (push ps ρ0)
      (key (ps ++ is)) major := by
  let A := foldApps (.const f ls) (policyLocals (Ps.length + Is.length))
  let T : Expr Nat := .pi A (.sort v)
  have hne : ¬ Equiv (fapp (fapps mo is) major) pempty := by
    intro he
    exact not_mem_pempty
      (mem_congr_right ((ed_congr M he).trans (ed_pempty M)) hout)
  have hmoNe : ¬ Equiv (fapps mo is) pempty := by
    intro he
    exact hne ((fapp_congr he Equiv.rfl).trans (fapp_pempty major))
  have his : TelFits M σ Is (push ps ρ0) is :=
    fits_of_typed_fapps_ne M σ T Is (push ps ρ0) mo is hlen hmo hmoNe
  have hm := mem_fapps M σ T Is (push ps ρ0) mo is hmo his
  have hzDen : major ∈ Ed M (den M σ (push is (push ps ρ0)) A) :=
    mem_dom_of_fapp_ne M
      (den_resp M σ (push is (push ps ρ0)) (.sort v)) hm hne
  have hF := Fapp_den M σ f ls ps is ρ0
  rw [hps, his.length] at hF
  have hz : major ∈ Ed M
      (fapps (M.μ f (ls.map (evalTotal σ))) (ps ++ is)) := by
    rw [← hF]
    exact hzDen
  have hT := PiRawMotiveAny.motive_mem_U M hU σ f ls Ps Is ps is
    hps mo major v hmo his hz
  have hg := PiRawMotiveAny.guarded_key M σ (evalTotal σ v)
    (M.μ f (ls.map (evalTotal σ))) mo ps Is (push ps ρ0) is major his hz hT
  apply mem_congr_right hg.symm
  simpa only [fapps_append, fapps] using hout

/-- Select the actual stored minor from h12 and the typed minor telescope,
then run the already produced arbitrary-depth field/IH spine. No local
minor-application contract or result-typing callback is supplied. -/
theorem apply_stored (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context) (A : Frame)
    (hM : C.M = mkM P (table P μ (famDataOf C.node.a) A))
    (hA : Admissible (famDataOf C.node.a) A)
    (K : Nat → Nat)
    (hB : FamBounded (famDataOf C.node.a) C.node.a.family.member.arity)
    (hf : ∀ e ∈ (famDataOf C.node.a).params ++ (famDataOf C.node.a).indices,
      occursConst (famDataOf C.node.a).fref e = false)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel ≠ 0)
    {n : Nat} (htf : TypeFacts C.node.E0)
    (hE : EnvSound C.M C.σ K C.node.E0 n)
    (hb : BodiesOK C.node.E0 C.σ K)
    (v : Level) (hps : C.parameters.length = C.node.a.family.parameters.length)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors)
    (j : Fin C.node.a.constructors.length) (xs : List PSet.{4})
    (hI : ∀ T ∈ (C.node.a.constructorViews j).fields, InstOK C.node.E0 C.σ K T)
    (hxs : TelFits C.M C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs)
    (g : PSet.{4} → PSet.{4})
    (hg : ∀ x y, Equiv x y → Equiv (g x) (g y))
    (hmap : ∀ i y, RawFamilyRec.paramKey C.parameters.length i = key C.parameters →
      MemT y (dataVal j.val xs) →
      y ∈ A ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)) i →
      g y ∈ PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v)
        (C.M.μ C.node.a.family.ref
          ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
        C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0) i y) :
    fapps (C.minors.getD j.val pempty) (RecPlan.args g (C.node.h14.shapesAt j) xs) ∈
      Ed C.M (C.endpoint j C.parameters xs) := by
  let M := mkM P (table P μ (famDataOf C.node.a) A)
  let c := C.node.a.constructorViews j
  let T := foldApps (.const C.node.a.family.ref (policyFamilyLevels C.node.a.family))
    (policyParameterLocals c.parameters.length c.fields.length ++ c.resultIndices)
  obtain ⟨ss, fuel, hshapes, hderived⟩ := C.node.h12 j
  have hsame : ss = C.node.h14.shapesAt j :=
    fieldShapesFuel_unique hshapes (C.node.h14.analyzed j)
  subst ss
  have hj : j.val < C.node.a.minorTypes.length := by
    rw [C.node.a.minorCount]
    exact j.isLt
  let R := C.node.a.minorTypes[j.val]'hj
  have hstored : C.node.a.minorTypes[j.val]? = some R := List.getElem?_eq_getElem hj
  have hd : derivedMinor C.node.a j fuel (C.node.h14.shapesAt j) = some R :=
    hderived.trans hstored
  have hR : minorFromTelescope C.node.E0 fuel C.node.a.family.parameters.length
      (C.rootMx j) (C.rootAcc j) (C.node.h14.shapesAt j)
      (Rcic.Declarative.lift 0 (C.prefix j).length (policyPi c.fields T)) = some R := by
    rw [C.prefix_length j]
    exact hd
  have hminor : C.minors.getD j.val pempty ∈
      Ed C.M (den C.M C.σ (C.rootCtx j C.parameters) R) := by
    have hh := TelFits_get C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors hminors j.val hj
    simpa only [Context.rootCtx, Context.prefix, push, R] using hh
  have hmo' : C.motive ∈ Ed M (den M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))) := by simpa only [hM] using hmo
  have hh := RawFamilyMinor.apply_admitted P μ (famDataOf C.node.a) A hA
    C.σ K C.node.a.family.member.arity hB hf h0 v C.parameters (C.prefix j)
    hps C.motive g hg hmo' C.node.E0 n htf
    (by simpa only [hM] using hE) hb fuel j.val (C.node.h14.shapesAt j)
    c.fields T (C.rootMx j) (C.rootAcc j) xs hshapes hI
    (by simpa only [hM] using hxs)
    (by simpa only [hM] using C.rootMx_den j C.parameters)
    (by simpa only [hM] using hmap) R (C.minors.getD j.val pempty) hR
    (by simpa only [hM] using hminor)
  have hidx : familyIdx C.node.a.family.parameters.length T = c.resultIndices := by
    dsimp only [T]
    rw [familyIdx_foldApps_const,
      List.drop_append_of_le_length
        (by rw [length_paramLocals, c.parameterCount]; exact Nat.le_refl _),
      List.drop_eq_nil_of_le
        (by rw [length_paramLocals, c.parameterCount]; exact Nat.le_refl _),
      List.nil_append]
  change familyIdx (famDataOf C.node.a).params.length T = c.resultIndices at hidx
  rw [hidx] at hh
  have hh' : fapps (C.minors.getD j.val pempty)
      (RecPlan.args g (C.node.h14.shapesAt j) xs) ∈ Ed C.M
      (fapp (fapps C.motive (c.resultIndices.map
        (den C.M C.σ (push xs (push C.parameters ρ0)))))
        (fapps (den C.M C.σ (C.rootCtx j C.parameters) (C.rootAcc j)) xs)) := by
    simpa only [hM] using hh
  rw [C.rootAcc_den j C.parameters hps, ← fapps_append] at hh'
  exact hh'

/-- The actual constructor/dataVal equation closes the stored-minor step
in the guarded motive. The conclusion retains its complete dependent key. -/
theorem apply_stored_guarded (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (C : Context) (A : Frame)
    (hM : C.M = mkM P (table P μ (famDataOf C.node.a) A))
    (hA : Admissible (famDataOf C.node.a) A) (K : Nat → Nat)
    (hB : FamBounded (famDataOf C.node.a) C.node.a.family.member.arity)
    (hf : ∀ e ∈ (famDataOf C.node.a).params ++ (famDataOf C.node.a).indices,
      occursConst (famDataOf C.node.a).fref e = false)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel ≠ 0)
    {n : Nat} (htf : TypeFacts C.node.E0)
    (hE : EnvSound C.M C.σ K C.node.E0 n) (hb : BodiesOK C.node.E0 C.σ K)
    (v : Level) (hps : C.parameters.length = C.node.a.family.parameters.length)
    (hmo : C.motive ∈ Ed C.M (den C.M C.σ (push C.parameters ρ0)
      (policyPi C.node.a.family.indices
        (.pi (foldApps (.const C.node.a.family.ref
          (canonL C.node.a.family.member.arity))
          (policyLocals (C.node.a.family.parameters.length + C.node.a.family.indices.length)))
          (.sort v)))))
    (hminors : TelFits C.M C.σ C.node.a.minorTypes
      (vcons C.motive (push C.parameters ρ0)) C.minors)
    (j : Fin C.node.a.constructors.length) (xs : List PSet.{4})
    (hI : ∀ T ∈ (C.node.a.constructorViews j).fields, InstOK C.node.E0 C.σ K T)
    (hxs : TelFits C.M C.σ (C.node.a.constructorViews j).fields
      (push C.parameters ρ0) xs)
    (g : PSet.{4} → PSet.{4}) (hg : ∀ x y, Equiv x y → Equiv (g x) (g y))
    (hmap : ∀ i y, RawFamilyRec.paramKey C.parameters.length i = key C.parameters →
      MemT y (dataVal j.val xs) →
      y ∈ A ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)) i →
      g y ∈ PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v)
        (C.M.μ C.node.a.family.ref
          ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
        C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0) i y)
    (hctor : Equiv (C.constructorAt j C.parameters xs) (dataVal j.val xs)) :
    fapps (C.minors.getD j.val pempty) (RecPlan.args g (C.node.h14.shapesAt j) xs) ∈
      PiRawMotiveAny.guarded C.M C.σ (evalTotal C.σ v)
        (C.M.μ C.node.a.family.ref
          ((canonL C.node.a.family.member.arity).map (evalTotal C.σ)))
        C.motive C.parameters C.node.a.family.indices (push C.parameters ρ0)
        (key (C.parameters ++ C.indicesAt j C.parameters xs)) (dataVal j.val xs) := by
  have hm := apply_stored P μ C A hM hA K hB hf h0 htf hE hb v hps
    hmo hminors j xs hI hxs g hg hmap
  have hU : C.M.U = U W4 := by rw [hM]; rfl
  have hn : (C.indicesAt j C.parameters xs).length = C.node.a.family.indices.length := by
    rw [Context.indicesAt, List.length_map]
    exact (C.node.a.constructorViews j).indexCount
  have hm' : fapps (C.minors.getD j.val pempty)
      (RecPlan.args g (C.node.h14.shapesAt j) xs) ∈ Ed C.M
      (fapp (fapps C.motive (C.indicesAt j C.parameters xs)) (dataVal j.val xs)) :=
    mem_congr_right (ed_congr C.M (fapp_congr Equiv.rfl hctor)) hm
  exact endpoint_guarded C.M hU C.σ C.node.a.family.ref
    (canonL C.node.a.family.member.arity) C.node.a.family.parameters C.node.a.family.indices
    C.parameters hps C.motive v hmo (C.indicesAt j C.parameters xs) (dataVal j.val xs)
    _ hn hm'

end Rcic.F3.PSet.RawDataMinor
