import rcic.RcicF3PiRawRename

/-!
# Original field admission through interleaved minor binders

A view records the successful normalized telescope and its complete canonical
parameter prefix at the actual minor-builder fuel. Admission produces the
view. Inserting binders preserves it, so repeated IH insertion does not
require assuming re-admission of the shifted field.
closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.PiRawFieldViews
open Rcic.Declarative

def View (E : ResolvedEnv) (fuel f nu np ni prior : Nat)
    (A : Expr Nat) : FieldShape → Prop
  | .nonrecursive => True
  | .recursive inner =>
      ∃ ds idx : List (Expr Nat), ds.length = inner ∧ idx.length = ni ∧
        piTelescopeFuel E fuel A = some (ds, foldApps (.const f (canonL nu))
          (policyParameterLocals np (prior + ds.length) ++ idx))

inductive Views (E : ResolvedEnv) (fuel f nu np ni : Nat) :
    Nat → List FieldShape → List (Expr Nat) → Prop where
  | nil (prior : Nat) : Views E fuel f nu np ni prior [] []
  | cons {prior : Nat} {s : FieldShape} {A : Expr Nat}
      {ss : List FieldShape} {Fs : List (Expr Nat)}
      (head : View E fuel f nu np ni prior A s)
      (tail : Views E fuel f nu np ni (prior + 1) ss Fs) :
      Views E fuel f nu np ni prior (s :: ss) (A :: Fs)

/-- Successful original admission supplies the complete recursive reader,
at the fuel used by minorFromTelescope rather than one less. -/
theorem of_admitted {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {A : Expr Nat} {s : FieldShape} {idx : List (Expr Nat)}
    (h : fieldAnalyze E fuel f nu np ni (np + prior) A = .permitted s idx) :
    View E fuel f nu np ni prior A s := by
  cases s with
  | nonrecursive => trivial
  | recursive inner =>
    obtain ⟨ds, b, hr, hl, _, _, hp⟩ := PiIndependent.recursive_scans h
    obtain ⟨ix, hb, hi, _⟩ := properFamilyFuel_shape (by omega) hp
    rw [show ds.length + (np + prior) = np + (prior + ds.length) by omega,
      paramLocals_top] at hb
    rw [hb] at hr
    exact ⟨ds, ix, hl, hi, piTelescopeFuel_mono E (Nat.sub_le fuel 1) hr⟩

/-- The entire original field list supplies views in the same admitted order. -/
theorem of_fields {E : ResolvedEnv} {fuel f nu np ni : Nat} :
    ∀ (Fs : List (Expr Nat)) (prior : Nat) (ss : List FieldShape),
      fieldShapesFuel E fuel f nu np ni (np + prior) Fs = some ss →
      Views E fuel f nu np ni prior ss Fs := by
  intro Fs
  induction Fs with
  | nil =>
    intro prior ss h
    have he : ss = [] := (Option.some.inj h).symm
    subst ss
    exact .nil prior
  | cons A Fs ih =>
    intro prior ss h
    cases ha : fieldAnalyze E fuel f nu np ni (np + prior) A with
    | unresolved => simp only [fieldShapesFuel, ha] at h; cases h
    | refused why => simp only [fieldShapesFuel, ha] at h; cases h
    | permitted s idx =>
      cases ht : fieldShapesFuel E fuel f nu np ni ((np + prior) + 1) Fs with
      | none => simp only [fieldShapesFuel, ha, ht] at h; cases h
      | some rest =>
        have he : ss = s :: rest := by
          simpa only [fieldShapesFuel, ha, ht, Option.bind_some, Option.map_some', pure, Option.some.injEq]
            using h.symm
        subst ss
        have ht' : fieldShapesFuel E fuel f nu np ni (np + (prior + 1)) Fs =
            some rest := by simpa only [Nat.add_assoc] using ht
        exact .cons (of_admitted ha) (ih (prior + 1) rest ht')

theorem View.lift {E : ResolvedEnv} (hcl : EnvClosed E)
    {fuel f nu np ni prior : Nat} {A : Expr Nat} {s : FieldShape}
    (h : View E fuel f nu np ni prior A s) (c a : Nat) (hc : c ≤ prior) :
    View E fuel f nu np ni (prior + a) (Rcic.Declarative.lift c a A) s := by
  cases s with
  | nonrecursive => trivial
  | recursive inner =>
    obtain ⟨ds, idx, hl, hi, hr⟩ := h
    have ht := PiRawRename.read_lift E hcl fuel hr c a
    rw [foldApps_lift, Rcic.Declarative.lift, List.map_append,
      policyParameterLocals_lift_le np (prior + ds.length) (c + ds.length) a (by omega)] at ht
    refine ⟨liftFields a ds c, idx.map (Rcic.Declarative.lift (c + ds.length) a),
      ?_, ?_, ?_⟩
    · rw [liftFields_length']; exact hl
    · rw [List.length_map]; exact hi
    · rw [liftFields_length']
      rw [show prior + a + ds.length = prior + ds.length + a by omega]
      exact ht

/-- An inserted IH may occur before any suffix of the previous locals.
Repeated use covers arbitrary interleavings of recursive and plain fields. -/
theorem Views.lift {E : ResolvedEnv} (hcl : EnvClosed E)
    {fuel f nu np ni prior : Nat} {ss : List FieldShape} {Fs : List (Expr Nat)}
    (h : Views E fuel f nu np ni prior ss Fs) (c a : Nat) (hc : c ≤ prior) :
    Views E fuel f nu np ni (prior + a) ss (liftFields a Fs c) := by
  induction h generalizing c with
  | nil prior => exact .nil (prior + a)
  | @cons prior s A ss Fs hh ht ih =>
    change Views E fuel f nu np ni (prior + a) (s :: ss)
      (Rcic.Declarative.lift c a A :: liftFields a Fs (c + 1))
    refine .cons (hh.lift hcl c a hc) ?_
    have hr := ih (c + 1) (by omega)
    simpa only [Nat.add_assoc, Nat.add_comm 1 a] using hr

theorem Views.length {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (h : Views E fuel f nu np ni prior ss Fs) : ss.length = Fs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih


/-- The executable IH reader inserts its field binder. The parameter prefix
still denotes the original parameter tuple after all prior insertions. -/
theorem View.ih_read (M : Interp.{4}) (σ : Nat → Nat)
    (ps pre : List PSet.{4}) (ρ : Nat → PSet.{4}) (x : PSet.{4})
    {E : ResolvedEnv} (hcl : EnvClosed E) {fuel f nu np ni inner : Nat}
    {A : Expr Nat} (hps : ps.length = np)
    (h : View E fuel f nu np ni pre.length A (.recursive inner)) :
    ∃ ds args : List (Expr Nat), ds.length = inner ∧ args.length = np + ni ∧
      piTelescopeFuel E fuel (Rcic.Declarative.lift 0 1 A) =
        some (ds, foldApps (.const f (canonL nu)) args) ∧
      ∀ xs, xs.length = ds.length →
        (args.take np).map
          (den M σ (push xs (vcons x (push pre (push ps ρ))))) = ps := by
  obtain ⟨ds, idx, hl, hi, hr⟩ := h
  have ht := PiRawRename.read_lift E hcl fuel hr 0 1
  rw [foldApps_lift, Rcic.Declarative.lift] at ht
  simp only [Nat.zero_add] at ht
  let args := policyParameterLocals np (pre.length + ds.length) ++ idx
  refine ⟨liftFields 1 ds 0, args.map (Rcic.Declarative.lift ds.length 1),
    ?_, ?_, ht, ?_⟩
  · rw [liftFields_length']; exact hl
  · simp only [List.length_map, args, List.length_append, policyParameterLocals_length, hi]
  · intro xs hxs
    rw [liftFields_length'] at hxs
    rw [← List.map_take, List.map_map]
    have he : (den M σ (push xs (vcons x (push pre (push ps ρ)))) ∘
        Rcic.Declarative.lift ds.length 1) = den M σ (push xs (push pre (push ps ρ))) := by
      funext e
      rw [← hxs]
      exact den_lift_push M σ xs [x] (push pre (push ps ρ)) e
    rw [he]
    dsimp only [args]
    rw [← hps, ← hxs]
    exact PiRawParams.param_prefix M σ ps pre xs ρ idx

end Rcic.F3.PSet.PiRawFieldViews
