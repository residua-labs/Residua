import rcic.RcicF3PiValueRule
/-! Executable admitted-field extraction and forward constructor closure.
Actual original field tuples enter a normalized positive signature. This
component retains ordinary environment and constant-instance bounds; it does
not reverse hidden normalization, pay recursor soundness or produce the
universal repaired group invariant. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiValueExtract
open Rcic.Declarative PiValueRule
universe u

/-- Executable extraction follows the existing admission result and its exact reader. -/
def field (E : ResolvedEnv) (fuel f nu np ni depth : Nat) (A : Expr Nat) : Option FieldSpec :=
  match fieldAnalyze E fuel f nu np ni depth A with
  | .permitted .nonrecursive _ => some (.plain A)
  | .permitted (.recursive _) _ =>
      match piTelescopeFuel E (fuel - 1) A with
      | some (ds, b) => some (.recursive ds (appsSpine b).2)
      | none => none
  | _ => none

/-- The extraction witness records syntax and free scans only, not a semantic conclusion. -/
def View (E : ResolvedEnv) (fuel f nu ar : Nat) (A : Expr Nat) : FieldSpec → Prop
  | .plain B => B = A ∧ occursConst f A = false
  | .recursive ds args =>
      piTelescopeFuel E (fuel - 1) A =
        some (ds, foldApps (.const f ((List.range nu).map Level.param)) args) ∧
      (∀ e ∈ ds, occursConst f e = false) ∧
      (∀ e ∈ args, occursConst f e = false) ∧ args.length = ar

/-- Admission in its actual parameter-local scope supplies an executable view. -/
theorem field_of_admitted {E : ResolvedEnv} {fuel f nu np ni depth : Nat}
    {A : Expr Nat} {s : FieldShape} {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni depth A = .permitted s idx)
    (hs : np ≤ depth) :
    ∃ a, field E fuel f nu np ni depth A = some a ∧ View E fuel f nu (np + ni) A a := by
  cases s with
  | nonrecursive =>
    exact ⟨.plain A, by simp only [field, h], rfl, fieldAnalyze_nonrec_free h⟩
  | recursive inner =>
    obtain ⟨ds, args, _, hl, hr, hd, ha⟩ := PiIndependent.admitted_shape h (by omega)
    refine ⟨.recursive ds args, ?_, hr, hd, ha, hl⟩
    simp only [field, h, hr]
    congr 2
    exact congrArg Prod.snd (appsSpine_foldApps_const f ((List.range nu).map Level.param) args)

def fields (E : ResolvedEnv) (fuel f nu np ni : Nat) : Nat → List (Expr Nat) → Option (List FieldSpec)
  | _, [] => some []
  | depth, A :: As => do
      let a ← field E fuel f nu np ni depth A
      let rest ← fields E fuel f nu np ni (depth + 1) As
      pure (a :: rest)

inductive Views (E : ResolvedEnv) (fuel f nu ar : Nat) :
    List (Expr Nat) → List FieldSpec → Prop where
  | nil : Views E fuel f nu ar [] []
  | cons {A a As rest} (head : View E fuel f nu ar A a)
      (tail : Views E fuel f nu ar As rest) : Views E fuel f nu ar (A :: As) (a :: rest)

/-- Complete admitted field lists have executable views at their actual depths. -/
theorem fields_of_admitted {E : ResolvedEnv} {fuel f nu np ni : Nat} :
    ∀ (As : List (Expr Nat)) (depth : Nat) (ss : List FieldShape),
    fieldShapesFuel E fuel f nu np ni depth As = some ss → np ≤ depth →
    ∃ fs, fields E fuel f nu np ni depth As = some fs ∧
      Views E fuel f nu (np + ni) As fs := by
  intro As
  induction As with
  | nil =>
      intro depth ss _ _
      exact ⟨[], rfl, .nil⟩
  | cons A As ih =>
      intro depth ss h hs
      cases ha : fieldAnalyze E fuel f nu np ni depth A with
      | unresolved => simp only [fieldShapesFuel, ha] at h; cases h
      | refused why => simp only [fieldShapesFuel, ha] at h; cases h
      | permitted s idx =>
          cases ht : fieldShapesFuel E fuel f nu np ni (depth + 1) As with
          | none => simp only [fieldShapesFuel, ha, ht] at h; cases h
          | some rest =>
              obtain ⟨a, hfa, hva⟩ := field_of_admitted ha hs
              obtain ⟨fs, hfs, hvs⟩ := ih (depth + 1) rest ht (by omega)
              refine ⟨a :: fs, ?_, .cons hva hvs⟩
              simp only [fields, hfa, hfs, Option.bind_some, pure]
              rfl

/-- Every admitted list carries the free scans and arities required by the normalized signature. -/
theorem Views.clean {E : ResolvedEnv} {fuel f nu ar : Nat} :
    ∀ {As fs}, Views E fuel f nu ar As fs → Clean f ar fs := by
  intro As fs h
  induction h with
  | nil => exact True.intro
  | @cons A a As rest hv ht ih =>
      cases a with
      | plain B => exact ⟨hv.1.symm ▸ hv.2, ih⟩
      | recursive ds args => exact ⟨hv.2.1, hv.2.2.1, hv.2.2.2, ih⟩

/-- Inhabited original fields enter the normalized field computed by admission. -/
theorem View.mem (M : Interp.{u}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n fuel f nu ar : Nat}
    (hE : EnvSound M σ K E n) (hb : BodiesOK E σ K)
    {A : Expr Nat} {a : FieldSpec} (hv : View E fuel f nu ar A a)
    (hI : InstOK E σ K A) (ρ : Nat → PSet.{u}) (x : PSet.{u})
    (hx : x ∈ Ed M (den M σ ρ A)) :
    x ∈ Ed M (den M σ ρ (fieldExpr f ((List.range nu).map Level.param) a)) := by
  cases a with
  | plain B =>
      change x ∈ Ed M (den M σ ρ B)
      rw [hv.1]
      exact hx
  | recursive ds args =>
      exact mem_congr_right (ed_congr M (den_piTelescope_of_mem M σ K hE hb
        (fuel - 1) A ds (foldApps (.const f ((List.range nu).map Level.param)) args)
        ρ x hv.1 hI hx).symm) hx

/-- A dependent original tuple enters the extracted normalized constructor tuple. -/
theorem Views.mem (M : Interp.{u}) (σ K : Nat → Nat)
    {E : ResolvedEnv} {n fuel f nu ar : Nat}
    (hE : EnvSound M σ K E n) (hb : BodiesOK E σ K) :
    ∀ {As fs}, Views E fuel f nu ar As fs →
    (∀ A ∈ As, InstOK E σ K A) → ∀ ρ xs,
    TelFits M σ As ρ xs →
    TelFits M σ (fs.map (fieldExpr f ((List.range nu).map Level.param))) ρ xs := by
  intro As fs hv
  induction hv with
  | nil =>
      intro _ ρ xs hx
      exact hx
  | @cons A a As rest hv ht ih =>
      intro hI ρ xs hx
      cases xs with
      | nil => exact hx.elim
      | cons x xs =>
          exact ⟨View.mem M σ K hE hb hv (hI A (List.mem_cons_self _ _)) ρ x hx.1,
            ih (fun B hB => hI B (List.mem_cons_of_mem _ hB)) (vcons x ρ) xs hx.2⟩

/-- Admission and the executable reader feed actual raw tuples into constructor closure.
No normalized-tuple or shape premise is supplied by the caller. -/
theorem close_admitted_tuple (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (f : Nat) (famDs : List (Expr Nat)) (cs : List Constructor) (vs : List Nat)
    (c : Fin cs.length) {E : ResolvedEnv} {n fuel np ni depth : Nat}
    {As : List (Expr Nat)} {ss : List FieldShape}
    (ha : fieldShapesFuel E fuel f vs.length np ni depth As = some ss)
    (hs : np ≤ depth) (har : np + ni = famDs.length)
    (hf : fields E fuel f vs.length np ni depth As = some (cs[c]).fields)
    (K : Nat → Nat)
    (hE : EnvSound (mkM P (upd μ f (PiValue.table P μ
      (predicate P μ famDs cs) famDs))) (σOf vs) K E n)
    (hb : BodiesOK E (σOf vs) K)
    (hI : ∀ A ∈ As, InstOK E (σOf vs) K A)
    (xs : List PSet.{4})
    (hx : TelFits (mkM P (upd μ f (PiValue.table P μ
      (predicate P μ famDs cs) famDs))) (σOf vs) As ρ0 xs) :
    predicate P μ famDs cs vs
      (PiIndex.read (mkM P μ) (σOf vs) (cs[c]).result (push xs ρ0)) := by
  obtain ⟨fs, hfs, hv⟩ := fields_of_admitted As depth ss ha hs
  have he : fs = (cs[c]).fields := Option.some.inj (hfs.symm.trans hf)
  subst fs
  have hc := hv.clean
  rw [har] at hc
  exact close_tuple P μ f famDs cs vs c hc xs
    (hv.mem _ (σOf vs) K hE hb hI ρ0 xs hx)

end Rcic.F3.PSet.PiValueExtract
