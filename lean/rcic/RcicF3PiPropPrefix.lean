import rcic.RcicF3PiPropField
/-! Canonical recursive proof slots in dependent constructor telescopes.
Successful admission and the complete proof face imply erasure; pointwise
semantic equality transports every later field and result index. The
ordinary environment and body obligations remain explicit. This component
does not construct a raw-group signature. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiPropPrefix
open Rcic.Declarative
universe u

def erase : List FieldShape → List PSet.{u} → List PSet.{u}
  | [], xs => xs
  | .nonrecursive :: ss, x :: xs => x :: erase ss xs
  | .recursive _ :: ss, _ :: xs => pempty :: erase ss xs
  | _ :: _, [] => []

def Erases (M : Interp.{u}) (σ : Nat → Nat) :
    List FieldShape → List (Expr Nat) → Prop
  | [], [] => True
  | .nonrecursive :: ss, _ :: ds => Erases M σ ss ds
  | .recursive _ :: ss, A :: ds =>
      (∀ ρ x, x ∈ Ed M (den M σ ρ A) → Equiv x pempty) ∧ Erases M σ ss ds
  | _, _ => False

theorem erase_equiv (M : Interp.{u}) (σ : Nat → Nat) :
    ∀ ss ds, Erases M σ ss ds → ∀ ρ xs, TelFits M σ ds ρ xs → LEq xs (erase ss xs) := by
  intro ss
  induction ss with
  | nil =>
    intro ds hs ρ xs hx
    cases ds with
    | nil => cases xs with
      | nil => trivial
      | cons x xs => exact False.elim hx
    | cons A ds => exact False.elim hs
  | cons s ss ih =>
    intro ds hs ρ xs hx
    cases ds with
    | nil => cases s <;> exact False.elim hs
    | cons A ds =>
      cases xs with
      | nil => exact False.elim hx
      | cons x xs =>
        cases s with
        | nonrecursive => exact ⟨Equiv.rfl, ih ds hs (vcons x ρ) xs hx.2⟩
        | recursive m => exact ⟨hs.1 ρ x hx.1, ih ds hs.2 (vcons x ρ) xs hx.2⟩
theorem erases_of_analysis (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (X : List Nat → PSet.{4}) (σ K : Nat → Nat) {E : ResolvedEnv}
    {n fuel f nu np ni : Nat}
    (hE : EnvSound (mkM P (upd μ f X)) σ K E n) (hb : BodiesOK E σ K)
    (hX : ∀ xs, xs.length = np + ni → ∀ z, z ∈ Ed (mkM P (upd μ f X))
      (fapps (X (((List.range nu).map Level.param).map (evalTotal σ))) xs) →
      Equiv z pempty) :
    ∀ ds depth ss, np ≤ depth →
      fieldShapesFuel E fuel f nu np ni depth ds = some ss →
      (∀ T ∈ ds, InstOK E σ K T) → Erases (mkM P (upd μ f X)) σ ss ds := by
  intro ds
  induction ds with
  | nil =>
    intro depth ss _ h _
    simp only [fieldShapesFuel, Option.some.injEq] at h
    subst ss
    trivial
  | cons A ds ih =>
    intro depth ss hdepth h hI
    cases ha : fieldAnalyze E fuel f nu np ni depth A with
    | unresolved => simp [fieldShapesFuel, ha] at h
    | refused reason => simp [fieldShapesFuel, ha] at h
    | permitted s idx =>
      simp only [fieldShapesFuel, ha] at h
      cases ht : fieldShapesFuel E fuel f nu np ni (depth + 1) ds with
      | none => rw [ht] at h; cases h
      | some ts =>
        rw [ht] at h
        have hs : s :: ts = ss := Option.some.inj h
        subst ss
        have htail := ih (depth + 1) ts (by omega) ht
          (fun T hT => hI T (List.mem_cons_of_mem _ hT))
        cases s with
        | nonrecursive => exact htail
        | recursive m =>
          exact ⟨fun ρ x hx => PiPropField.admitted_empty P μ X σ K ha (by omega)
            (hI A (List.mem_cons_self _ _)) hE hb hX ρ x hx, htail⟩
/-- Elementary transport: canonicalizing recursive proof slots preserves
all later dependent field types and every constructor result index. -/
theorem canonical_tuple (M : Interp.{u}) (σ : Nat → Nat)
    (ss : List FieldShape) (ds : List (Expr Nat)) (h : Erases M σ ss ds)
    (ρ : Nat → PSet.{u}) (xs : List PSet.{u}) (hx : TelFits M σ ds ρ xs) :
    LEq xs (erase ss xs) ∧ TelFits M σ ds ρ (erase ss xs) ∧
      ∀ es : List (Expr Nat), LEq (es.map (den M σ (push xs ρ)))
        (es.map (den M σ (push (erase ss xs) ρ))) := by
  have he := erase_equiv M σ ss ds h ρ xs hx
  exact ⟨he, TelFits_congr M σ ds (fun _ => Equiv.rfl) he hx,
    fun es => LEq_map_den M σ (push_congr he (fun _ => Equiv.rfl)) es⟩
end Rcic.F3.PSet.PiPropPrefix
