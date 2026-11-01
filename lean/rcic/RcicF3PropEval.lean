import rcic.RcicF3RawFamilyRec
import rcic.RcicF3PiRawMinor
import rcic.RcicF3PropEvalExtract

/-!
# Indexed evaluation of actual stored recursive minors

The fixed context contains an admitted RecNode and its parameter slice.
Recursive inputs use the executable IH type and the normalized telescope's
complete parameter/index key. The root is the actual derivedMinor start state.
Existence, singleton functionality, iota and read congruence remain open.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PropEval
open Rcic.Declarative PiIndex

/-- The fixed semantic inputs; the minor-list length fixes the motive binder. -/
structure Context where
  E : ResolvedEnv
  E' : ResolvedEnv
  f : Nat
  rr : Nat
  rm : CheckedMember
  node : RecNode E E' f rr rm
  M : Interp.{4}
  σ : Nat → Nat
  parameters : List PSet.{4}
  motive : PSet.{4}
  minors : List PSet.{4}
  minor_length : minors.length = node.a.constructors.length

def Context.prefix (C : Context) (j : Fin C.node.a.constructors.length) :
    List PSet.{4} := C.motive :: C.minors.take j.val

def Context.rootCtx (C : Context) (j : Fin C.node.a.constructors.length)
    (ps : List PSet.{4}) : Nat → PSet.{4} :=
  push (C.prefix j) (push ps ρ0)

def Context.rootMx (C : Context) (j : Fin C.node.a.constructors.length) : Expr Nat :=
  .bvar j.val

def Context.rootAcc (C : Context) (j : Fin C.node.a.constructors.length) : Expr Nat :=
  foldApps (.const (C.node.a.family.ref + 1 + j.val) (policyFamilyLevels C.node.a.family))
    (policyParameterLocals C.node.a.family.parameters.length (1 + j.val))

noncomputable def Context.rootT (C : Context) (j : Fin C.node.a.constructors.length) : Expr Nat :=
  Rcic.Declarative.lift 0 (1 + j.val) (ctorFieldTelescope (C.node.a.constructorViews j))

mutual
  /-- A result of an actual stored minor at the complete family key. -/
  inductive Eval (C : Context) : Index.{4} → PSet.{4} → Prop where
    | root (j : Fin C.node.a.constructors.length) (ps xs ys : List PSet.{4})
        (fuel : Nat) (R : Expr Nat) (out z : PSet.{4})
        (hps : TelFits C.M C.σ C.node.a.family.parameters ρ0 ps)
        (hparameters : LEq ps C.parameters)
        (hfields : TelFits C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0) xs)
        (hshapes : fieldShapesFuel C.node.E0 fuel C.node.a.family.ref
          C.node.a.family.member.arity C.node.a.family.parameters.length
          C.node.a.family.indices.length C.node.a.family.parameters.length
          (C.node.a.constructorViews j).fields = some (C.node.h14.shapesAt j))
        (hstored : C.node.a.minorTypes[j.val]? = some R)
        (hderived : derivedMinor C.node.a j fuel (C.node.h14.shapesAt j) = some R)
        (hminor : C.minors.getD j.val pempty ∈ Ed C.M (den C.M C.σ (C.rootCtx j ps) R))
        (hinputs : Inputs C fuel (C.rootMx j) (C.rootAcc j) (C.node.h14.shapesAt j)
          (C.rootT j) (C.rootCtx j ps) xs ys out)
        (hresult : Equiv z (fapps (C.minors.getD j.val pempty) ys)) :
        Eval C (key (ps ++ (C.node.a.constructorViews j).resultIndices.map
          (den C.M C.σ (push xs (push ps ρ0))))) z

  /-- Actual typed field/IH spines with a recursive evaluation at each fitting leaf. -/
  inductive Inputs (C : Context) :
      Nat → Expr Nat → Expr Nat → List FieldShape → Expr Nat →
        (Nat → PSet.{4}) → List PSet.{4} → List PSet.{4} → PSet.{4} → Prop where
    | done (fuel : Nat) (Mx acc T : Expr Nat) (ρ : Nat → PSet.{4}) :
        Inputs C fuel Mx acc [] T ρ [] []
          (den C.M C.σ ρ (.app (foldApps Mx (familyIdx C.node.a.family.parameters.length T)) acc))
    | plain {fuel : Nat} {Mx acc A B : Expr Nat} {ss : List FieldShape}
        {ρ : Nat → PSet.{4}} {xs ys : List PSet.{4}} {out : PSet.{4}}
        (x : PSet.{4}) (hx : x ∈ Ed C.M (den C.M C.σ ρ A))
        (tail : Inputs C fuel (Rcic.Declarative.lift 0 1 Mx)
          (.app (Rcic.Declarative.lift 0 1 acc) (.bvar 0)) ss B (vcons x ρ) xs ys out) :
        Inputs C fuel Mx acc (.nonrecursive :: ss) (.pi A B) ρ (x :: xs) (x :: ys) out
    | recursive {fuel : Nat} {Mx acc A B : Expr Nat} {ss : List FieldShape}
        {ρ : Nat → PSet.{4}} {xs ys : List PSet.{4}} {out : PSet.{4}}
        (inner : Nat) (ihT : Expr Nat)
        (hread : funIHType C.node.E0 fuel C.node.a.family.parameters.length A Mx inner = some ihT)
        (x ih : PSet.{4}) (hx : x ∈ Ed C.M (den C.M C.σ ρ A))
        (hih : ih ∈ Ed C.M (den C.M C.σ (vcons x ρ) ihT))
        (ds args : List (Expr Nat))
        (hscan : piTelescopeFuel C.node.E0 fuel (Rcic.Declarative.lift 0 1 A) =
          some (ds, foldApps (.const C.node.a.family.ref
            (canonL C.node.a.family.member.arity)) args))
        (hdepth : ds.length = inner)
        (hargc : args.length = C.node.a.family.parameters.length + C.node.a.family.indices.length)
        (hchildren : ∀ zs, TelFits C.M C.σ ds (vcons x ρ) zs →
          Eval C (key (args.map (den C.M C.σ (push zs (vcons x ρ))))) (fapps ih zs))
        (tail : Inputs C fuel (Rcic.Declarative.lift 0 2 Mx)
          (.app (Rcic.Declarative.lift 0 2 acc) (.bvar 1)) ss
          (Rcic.Declarative.lift 0 1 B) (vcons ih (vcons x ρ)) xs ys out) :
        Inputs C fuel Mx acc (.recursive inner :: ss) (.pi A B) ρ
          (x :: xs) (x :: ih :: ys) out
end

theorem Context.prefix_length (C : Context) (j : Fin C.node.a.constructors.length) :
    (C.prefix j).length = 1 + j.val := by
  have hj : j.val ≤ C.minors.length := by rw [C.minor_length]; exact Nat.le_of_lt j.isLt
  simp only [Context.prefix, List.length_cons, List.length_take, Nat.min_eq_left hj]
  omega

theorem Context.rootMx_den (C : Context) (j : Fin C.node.a.constructors.length)
    (ps : List PSet.{4}) : den C.M C.σ (C.rootCtx j ps) (C.rootMx j) = C.motive := by
  have hj : j.val ≤ C.minors.length := by rw [C.minor_length]; exact Nat.le_of_lt j.isLt
  have hl : (C.minors.take j.val).length = j.val := by
    rw [List.length_take, Nat.min_eq_left hj]
  change push (C.motive :: C.minors.take j.val) (push ps ρ0) j.val = C.motive
  simpa only [hl] using push_cons_len_index C.motive (C.minors.take j.val) (push ps ρ0)

/-- The root accumulator denotes the actual constructor applied to the parameters. -/
theorem Context.rootAcc_den (C : Context) (j : Fin C.node.a.constructors.length)
    (ps : List PSet.{4}) (hps : ps.length = C.node.a.family.parameters.length) :
    den C.M C.σ (C.rootCtx j ps) (C.rootAcc j) =
      fapps (C.M.μ (C.node.a.family.ref + 1 + j.val)
        ((policyFamilyLevels C.node.a.family).map (evalTotal C.σ))) ps := by
  unfold Context.rootAcc
  rw [den_foldApps]
  have hp := den_paramLocals C.M C.σ ps (C.prefix j) ρ0
  rw [push_append] at hp
  have he : (policyParameterLocals C.node.a.family.parameters.length (1 + j.val)).map
      (den C.M C.σ (C.rootCtx j ps)) = ps := by
    rw [← hps, ← C.prefix_length j]
    exact hp
  rw [he]
  rfl

/-- Erase only the child-evaluation certificates, preserving the exact typed spine. -/
theorem Inputs.erase {C : Context} {fuel : Nat} {Mx acc T : Expr Nat}
    {ss : List FieldShape} {ρ : Nat → PSet.{4}} {xs ys : List PSet.{4}} {out : PSet.{4}}
    (h : Inputs C fuel Mx acc ss T ρ xs ys out) :
    PiRawMinor.Inputs C.M C.σ C.node.E0 fuel C.node.a.family.parameters.length
      Mx acc ss T ρ xs ys out := by
  induction h using Inputs.rec (motive_1 := fun _ _ _ => True) with
  | root => trivial
  | done fuel Mx acc T ρ => exact .done Mx acc T ρ
  | @plain fuel Mx acc A B ss ρ xs ys out x hx tail ih =>
      exact .plain x hx ih
  | @recursive fuel Mx acc A B ss ρ xs ys out inner ihT hr x ih hx hih ds args hscan
      hdepth hargc hchildren tail _ iht =>
      exact .recursive inner ihT hr x ih hx hih iht

/-- Checked composition with the executable minor builder. -/
theorem Inputs.apply {C : Context} {fuel : Nat} {Mx acc T R : Expr Nat}
    {ss : List FieldShape} {ρ : Nat → PSet.{4}} {xs ys : List PSet.{4}}
    {out F : PSet.{4}} (h : Inputs C fuel Mx acc ss T ρ xs ys out)
    (hR : minorFromTelescope C.node.E0 fuel C.node.a.family.parameters.length
      Mx acc ss T = some R)
    (hF : F ∈ Ed C.M (den C.M C.σ ρ R)) : fapps F ys ∈ Ed C.M out :=
  PiRawMinor.apply C.M C.σ C.node.E0 fuel C.node.a.family.parameters.length h.erase hR hF

/-- The literal judgment is closed under equivalence of its output. -/
theorem Eval.output_congr {C : Context} {i : Index.{4}} {z z' : PSet.{4}}
    (h : Eval C i z) (he : Equiv z' z) : Eval C i z' := by
  cases h with
  | root j ps xs ys fuel R out z hps hp hf hs hst hd hm hi hr =>
      exact .root j ps xs ys fuel R out z' hps hp hf hs hst hd hm hi (he.trans hr)

/-- The complete result key retains the fixed parameter slice. -/
theorem Eval.parameters {C : Context} {i : Index.{4}} {z : PSet.{4}}
    (h : Eval C i z) : RawFamilyRec.paramKey C.node.a.family.parameters.length i =
      key C.parameters := by
  cases h with
  | root j ps xs ys fuel R out z hps hp hf hs hst hd hm hi hr =>
      rw [← hps.length, RawFamilyRec.paramKey_append]
      exact (key_eq_iff _ _).mpr hp

/-- A result has the endpoint typing obtained from its actual stored minor.
Converting this endpoint into the guarded motive still needs constructor typing. -/
theorem Eval.endpoint_typed {C : Context} {i : Index.{4}} {z : PSet.{4}}
    (h : Eval C i z) : ∃ (j : Fin C.node.a.constructors.length) (ps xs ys : List PSet.{4})
      (fuel : Nat) (out : PSet.{4}),
      i = key (ps ++ (C.node.a.constructorViews j).resultIndices.map
        (den C.M C.σ (push xs (push ps ρ0)))) ∧
      TelFits C.M C.σ C.node.a.family.parameters ρ0 ps ∧
      TelFits C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0) xs ∧
      Inputs C fuel (C.rootMx j) (C.rootAcc j) (C.node.h14.shapesAt j)
        (C.rootT j) (C.rootCtx j ps) xs ys out ∧ z ∈ Ed C.M out := by
  cases h with
  | root j ps xs ys fuel R out z hps hp hf hs hst hd hm hi hr =>
      refine ⟨j, ps, xs, ys, fuel, out, rfl, hps, hf, hi, ?_⟩
      exact mem_congr_left hr.symm (hi.apply hd hm)

/-- The endpoint uses the original fields, dependent indices and actual constructor. -/
noncomputable def Context.endpoint (C : Context) (j : Fin C.node.a.constructors.length)
    (ps xs : List PSet.{4}) : PSet.{4} :=
  fapp (fapps C.motive ((C.node.a.constructorViews j).resultIndices.map
    (den C.M C.σ (push xs (push ps ρ0)))))
    (fapps (C.M.μ (C.node.a.family.ref + 1 + j.val)
      ((policyFamilyLevels C.node.a.family).map (evalTotal C.σ))) (ps ++ xs))

/-- Remove the inserted motive, prior minors and IH binders from the endpoint. -/
theorem Inputs.root_endpoint {C : Context} (j : Fin C.node.a.constructors.length)
    {ps xs ys : List PSet.{4}} {fuel : Nat} {out : PSet.{4}}
    (h : Inputs C fuel (C.rootMx j) (C.rootAcc j) (C.node.h14.shapesAt j)
      (C.rootT j) (C.rootCtx j ps) xs ys out)
    (hps : TelFits C.M C.σ C.node.a.family.parameters ρ0 ps)
    (hx : TelFits C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0) xs) :
    out = C.endpoint j ps xs := by
  let c := C.node.a.constructorViews j
  let T := foldApps (.const C.node.a.family.ref (policyFamilyLevels C.node.a.family))
    (policyParameterLocals c.parameters.length c.fields.length ++ c.resultIndices)
  have he := PiRawMinor.endpoint C.M C.σ C.node.E0 fuel C.node.a.family.parameters.length
    h.erase (liftFields (1 + j.val) c.fields 0)
    (Rcic.Declarative.lift c.fields.length (1 + j.val) T)
    (by change Rcic.Declarative.lift 0 (1 + j.val) (policyPi c.fields T) = _
        rw [lift_policyPi, Nat.zero_add])
    (by rw [liftFields_length']; exact hx.length.symm)
  have hidx : (familyIdx C.node.a.family.parameters.length
      (Rcic.Declarative.lift c.fields.length (1 + j.val) T)).map
      (den C.M C.σ (push xs (C.rootCtx j ps))) =
      c.resultIndices.map (den C.M C.σ (push xs (push ps ρ0))) := by
    dsimp only [T]
    rw [familyIdx_lift, familyIdx_foldApps_const,
      List.drop_append_of_le_length (by rw [length_paramLocals, c.parameterCount]; exact Nat.le_refl _),
      List.drop_eq_nil_of_le (by rw [length_paramLocals, c.parameterCount]; exact Nat.le_refl _),
      List.nil_append, List.map_map, ← hx.length]
    exact List.map_congr_left fun e _ => by
      change den C.M C.σ (push xs (push (C.prefix j) (push ps ρ0)))
        (Rcic.Declarative.lift xs.length (1 + j.val) e) = _
      rw [← C.prefix_length j, den_lift_push]
  rw [C.rootMx_den j ps, C.rootAcc_den j ps hps.length, hidx, ← fapps_append] at he
  exact he

/-- Produced endpoint typing at the original constructor and dependent indices. -/
theorem Eval.result_typed {C : Context} {i : Index.{4}} {z : PSet.{4}}
    (h : Eval C i z) : ∃ (j : Fin C.node.a.constructors.length) (ps xs : List PSet.{4}),
      i = key (ps ++ (C.node.a.constructorViews j).resultIndices.map
        (den C.M C.σ (push xs (push ps ρ0)))) ∧
      LEq ps C.parameters ∧ TelFits C.M C.σ C.node.a.family.parameters ρ0 ps ∧
      TelFits C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0) xs ∧
      z ∈ Ed C.M (C.endpoint j ps xs) := by
  cases h with
  | root j ps xs ys fuel R out z hps hp hf hs hst hd hm hi hr =>
      refine ⟨j, ps, xs, rfl, hp, hps, hf, ?_⟩
      have ht := mem_congr_left hr.symm (hi.apply hd hm)
      rw [hi.root_endpoint j hps hf] at ht
      exact ht

end Rcic.F3.PSet.PropEval
