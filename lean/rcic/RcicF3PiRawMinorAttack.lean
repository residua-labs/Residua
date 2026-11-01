import rcic.RcicF3PiRawMinor
import rcic.RcicF3PiRawIHAttack
/-! Actual depth-three raw minor application with a later dependent data
field and retained result index, at every numeric family label. These are
semantic minor fixtures, not universally typed raw groups. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawMinorAttack
open Rcic.Declarative PiRawIHAttack

def later (f : Nat) : Expr Nat := .app (.lam (field f) (dom f)) (.bvar 0)
def result (f : Nat) : Expr Nat := foldApps (.const f []) [.bvar 0]
def fields (f : Nat) : List (Expr Nat) := [field f, later f]
def telescope (f : Nat) : Expr Nat := policyPi (fields f) (result f)
def shapes : List FieldShape := [.recursive 3, .nonrecursive]
def minor (f : Nat) (A : Expr Nat) : Expr Nat :=
  .pi A (.pi (ihExpr f) (.pi (Rcic.Declarative.lift 0 1 (later f))
    (.app (foldApps (.bvar 3) [.bvar 0])
      (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0)))))
def start (P : Premises4) (f : Nat) : Nat → PSet.{4} := vcons (motive P f) ρ0

theorem later_dom (P : Premises4) (f : Nat) (ρ : Nat → PSet.{4})
    (hx : ρ 0 ∈ Ed (model P f) (den (model P f) (σOf []) ρ (field f))) :
    Equiv (den (model P f) (σOf []) ρ (later f))
      (den (model P f) (σOf []) ρ (dom f)) := by
  exact beta_val (model P f) (den_resp (model P f) (σOf []) ρ (dom f)) hx
/-- A genuine typed minor, including all IH values and later dependent data
values in its domain. No minor-membership premise is supplied. -/
theorem minor_typed (P : Premises4) (f : Nat) :
    let M := model P f
    piLam M (σOf []) (fun _ => pempty) (start P f) (minor f (field f)) ∈
      Ed M (den M (σOf []) (start P f) (minor f (field f))) := by
  dsimp only
  let M := model P f
  apply piLam_mem M (σOf []) (envResp_const pempty)
  change ∀ x, x ∈ Ed M (den M (σOf []) (start P f) (field f)) →
    ∀ i, i ∈ Ed M (den M (σOf []) (vcons x (start P f)) (ihExpr f)) →
    ∀ y, y ∈ Ed M (den M (σOf []) (vcons i (vcons x (start P f)))
      (Rcic.Declarative.lift 0 1 (later f))) → _
  intro x hx i hi y hy
  have hd : den M (σOf []) (vcons i (vcons x (start P f)))
      (Rcic.Declarative.lift 0 1 (later f)) =
      den M (σOf []) (vcons x (start P f)) (later f) :=
    den_lift0_push M (σOf []) [i] (vcons x (start P f)) (later f)
  rw [hd] at hy
  have hy' : y ∈ Ed M (den M (σOf []) ρ0 (dom f)) :=
    mem_congr_right (ed_congr M (later_dom P f (vcons x (start P f)) hx)) hy
  let z := fapps (pempty : PSet.{4}) [x, y]
  have hfit : TelFits M (σOf []) [dom f] ρ0 [y] := ⟨hy', True.intro⟩
  have hz : z ∈ Ed M (fapps (M.μ f []) [y]) := by
    apply mem_congr_right (ed_congr M (fapps_congr (family P f) [y])).symm
    exact mem_congr_right
      (PiValue.apply_ed M (σOf []) (fun _ => True) [dom f] ρ0 [y] hfit).symm
      (mem_tv.mpr ⟨True.intro, fapps_pempty [x, y]⟩)
  have hfits : TelFits M (σOf []) [dom f, major f] ρ0 [y, z] :=
    ⟨hy', hz, True.intro⟩
  change pempty ∈ Ed M (fapps (motive P f) [y, z])
  exact mem_congr_right (PiValue.apply_ed M (σOf []) (fun _ => True)
    [dom f, major f] ρ0 [y, z] hfits).symm
    (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)

/-- Elementary executable readback at every numeric label. -/
theorem builder (f : Nat) :
    minorFromTelescope emptyEnv 32 0 (.bvar 0) (.bvar 1) shapes (telescope f) =
      some (minor f (field f)) := by
  rfl

/-- Inhabited application of the actual builder: all field/IH/minor
memberships are constructed, and the later data field is the result index. -/
theorem inhabited (P : Premises4) (f : Nat) :
    let M := model P f
    ∃ ih out,
      PiRawMinor.Inputs M (σOf []) emptyEnv 32 0 (.bvar 0) (.bvar 1)
        shapes (telescope f) (start P f) [pempty, PiPropPrefixAttack.datum]
        [pempty, ih, PiPropPrefixAttack.datum] out ∧
      fapps (piLam M (σOf []) (fun _ => pempty) (start P f) (minor f (field f)))
        [pempty, ih, PiPropPrefixAttack.datum] ∈
        Ed M (fapps (motive P f) [PiPropPrefixAttack.datum,
          fapps pempty [pempty, PiPropPrefixAttack.datum]]) := by
  dsimp only
  let M := model P f
  let d : PSet.{4} := PiPropPrefixAttack.datum
  obtain ⟨hmo, hds, hx, ih, hih⟩ := PiRawIHAttack.inhabited P f
  have hy : d ∈ Ed M (den M (σOf []) (vcons ih (assignment P f))
      (Rcic.Declarative.lift 0 1 (later f))) := by
    have hd : den M (σOf []) (vcons ih (assignment P f))
        (Rcic.Declarative.lift 0 1 (later f)) =
        den M (σOf []) (assignment P f) (later f) :=
      den_lift0_push M (σOf []) [ih] (assignment P f) (later f)
    rw [hd]
    exact mem_congr_right (ed_congr M (later_dom P f (assignment P f) hx)).symm hds.1
  have ht := PiRawMinor.Inputs.done (M := M) (σ := σOf []) (E := emptyEnv)
    (fuel := 32) (np := 0) (.bvar 3)
    (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0)) (result f)
    (vcons d (vcons ih (assignment P f)))
  have hp := PiRawMinor.Inputs.plain (Mx := .bvar 2)
    (acc := .app (.bvar 3) (.bvar 1)) (B := result f) (ss := []) d hy ht
  have hi : PiRawMinor.Inputs M (σOf []) emptyEnv 32 0 (.bvar 0) (.bvar 1)
      shapes (telescope f) (start P f) [pempty, d] [pempty, ih, d] _ :=
    PiRawMinor.Inputs.recursive 3 (ihExpr f) (by rfl) pempty ih hx hih hp
  refine ⟨ih, _, hi, ?_⟩
  exact PiRawMinor.apply_endpoint M (σOf []) emptyEnv 32 0 hi (builder f)
    (minor_typed P f) (fields f) (result f) rfl rfl

/-- An actual out-of-domain later data value is refused. -/
theorem later_refused (P : Premises4) (f : Nat) (ρ : Nat → PSet.{4})
    (hx : ρ 0 ∈ Ed (model P f) (den (model P f) (σOf []) ρ (field f))) :
    dataVal 8 [] ∉ Ed (model P f) (den (model P f) (σOf []) ρ (later f)) := by
  intro hy
  let M := model P f
  have hd := mem_congr_right (ed_congr M (later_dom P f ρ hx)) hy
  have hn : f + 1 ≠ f := by omega
  change dataVal 8 [] ∈ Ed M ((upd base f
    (PiValue.table P base (fun _ _ => True) [dom f])) (f + 1) []) at hd
  rw [upd_ne _ _ _ hn] at hd
  have hdom : Dich (PiPropPrefixAttack.domain : PSet.{4}) :=
    Or.inr (fun h => dataVal_ne_pempty 7 [] (mem_singleton.mp h).symm)
  have he := mem_singleton.mp (mem_congr_right (ed_tyv M hdom) hd)
  have htags : 8 = 7 := (dataVal_inj rfl he).1
  cases htags

/-- The new input spine cannot silently replace the retained data field. -/
theorem wrong_spine_refused (P : Premises4) (f : Nat) :
    ¬ ∃ ih out, PiRawMinor.Inputs (model P f) (σOf []) emptyEnv 32 0
      (.bvar 0) (.bvar 1) shapes (telescope f) (start P f)
      [pempty, dataVal 8 []] [pempty, ih, dataVal 8 []] out := by
  rintro ⟨i, out, h⟩
  cases h with
  | recursive inner ihT hr x ih hx hi tail =>
    cases tail with
    | plain y hy tail =>
      have hd : den (model P f) (σOf []) (vcons i (assignment P f))
          (Rcic.Declarative.lift 0 1 (later f)) =
          den (model P f) (σOf []) (assignment P f) (later f) :=
        den_lift0_push (model P f) (σOf []) [i] (assignment P f) (later f)
      change dataVal 8 [] ∈ Ed (model P f) (den (model P f) (σOf [])
        (vcons i (assignment P f)) (Rcic.Declarative.lift 0 1 (later f))) at hy
      rw [hd] at hy
      exact later_refused P f (assignment P f) hx hy

/-- Elementary beta/delta/let and relabelled builder pins. Delta asserts
reader computation only, not typing of the alias environment. -/
theorem hidden_builders : ∀ f ∈ [1, 2, 987],
    ∀ A ∈ [field f, beta f, delta f, zeta f],
      minorFromTelescope (env f) 32 0 (.bvar 0) (.bvar 1) shapes
        (policyPi [A, later f] (result f)) = some (minor f A) := by
  decide

end Rcic.F3.PSet.PiRawMinorAttack
