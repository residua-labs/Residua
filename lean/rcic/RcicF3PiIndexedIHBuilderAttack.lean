import rcic.RcicF3PiIndexedIHBuilder
import rcic.RcicF3PiRawIHAnyAttack
import rcic.RcicF3PiTypedExt

/-!
# A produced executable IH over an inhabited depth-three proof field

The source field erases to pempty, its actual domains are inhabited, and
the extra-universe motive requires nonempty data. The new indexed operation
inhabits the actual IH type; the old graph-depth operation fails that type.
Hidden delta aliases are reader fixtures, not fully typed raw groups.
This is a semantic builder component, not a universal recursor producer.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiIndexedIHBuilderAttack
open Rcic.Declarative PiIndex
open PiRawIHAttack (model dom ds args field major ihExpr)
open PiRawIHAnyAttack (datum domain σ v motive assignment)

def source (P : Premises4) (f : Nat) : PSet.{4} := (model P f).μ f []
def carrier (P : Premises4) (f : Nat) : Index.{4} → PSet.{4} → PSet.{4} :=
  PiRawMotiveAny.guarded (model P f) σ 1 (source P f) (motive P f) [] [dom f] ρ0
def indexedValue (P : Premises4) (f : Nat) : PSet.{4} :=
  (tel (model P f) σ (ds f) args (assignment P f)).indexedIH
    (model P f) (fun _ _ => datum) pempty

theorem family_prop (P : Premises4) (f : Nat) (ys : List PSet.{4})
    (hys : ys.length = args.length) (x : PSet.{4})
    (hx : x ∈ Ed (model P f) (fapps (source P f) ys)) : Equiv x pempty := by
  have h := (PiValue.apply_mem_iff (model P f) σ (fun _ => True) [dom f] ρ0 ys hys x).mp
    (mem_congr_right (ed_congr (model P f) (fapps_congr (PiRawIHAttack.family P f) ys)) hx)
  exact h.2.2

/-- The leaf map is typed from actual family and motive facts at the full key. -/
theorem map_at_key (P : Premises4) (f : Nat) (is : List PSet.{4})
    (his : is.length = args.length) (x : PSet.{4})
    (hx : x ∈ proofFibre (model P f) (source P f) (key is)) :
    datum ∈ carrier P f (key is) x := by
  let M := model P f
  have hd := proofFibre_key M (source P f) is
    (fun ys hys z hz => family_prop P f ys (hys.trans his) z hz)
  have hxF : x ∈ Ed M (fapps (source P f) is) := mem_congr_right hd hx
  have hfit := ((PiValue.apply_mem_iff M σ (fun _ => True) [dom f] ρ0 is his x).mp
    (mem_congr_right (ed_congr M (fapps_congr (PiRawIHAttack.family P f) is)) hxF)).1
  have hden := Fapp_den M σ f [] [] is ρ0
  rw [hfit.length] at hden
  change den M σ (push is ρ0) (major f) = fapps (M.μ f []) is at hden
  have hmajor : x ∈ Ed M (den M σ (push is ρ0) (major f)) := by rw [hden]; exact hxF
  have hm := PiRawIHAnyAttack.motive_apply P f is x (TelFits.append hfit ⟨hmajor, True.intro⟩)
  have hT : fapps (motive P f) (is ++ [x]) ∈ M.U 1 :=
    mem_congr_left hm.symm (PiRawIHAnyAttack.type_mem P)
  have hg := PiRawMotiveAny.guarded_key M σ 1 (source P f) (motive P f)
    [] [dom f] ρ0 is x hfit hxF hT
  exact mem_congr_right hg.symm (mem_congr_right
    ((ed_congr M hm).trans (ed_tyv M PiRawIHAnyAttack.domain_dich)).symm
    (mem_singleton.mpr Equiv.rfl))

theorem leaf_map (P : Premises4) (f : Nat) :
    let M := model P f
    let t := tel M σ (ds f) args (assignment P f)
    ∀ p x, x ∈ proofFibre M (source P f) (t.result p) →
      datum ∈ carrier P f (t.result p) x := by
  dsimp only
  intro p x hx
  let M := model P f
  obtain ⟨xs, _, he⟩ := PiSyntaxCompile.result_fits M σ (read M σ args)
    (ds f) (assignment P f) p
  change (tel (model P f) σ (ds f) args (assignment P f)).result p =
    read M σ args (push xs (assignment P f)) at he
  rw [he] at hx ⊢
  exact map_at_key P f (args.map (den M σ (push xs (assignment P f))))
    (by simp only [List.length_map]) x hx

/-- A successful normalized read produces the actual builder result and membership. -/
theorem builder_at_read (P : Premises4) (f : Nat) (E : ResolvedEnv) (fuel : Nat)
    (A : Expr Nat) (hread : piTelescopeFuel E fuel (Rcic.Declarative.lift 0 1 A) =
      some (ds f, foldApps (.const f []) args)) :
    funIHType E fuel 0 A (.bvar 0) 3 = some (ihExpr f) ∧
      indexedValue P f ∈ Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f)) := by
  have hb : funIHType E fuel 0 A (.bvar 0) 3 = some (ihExpr f) :=
    PiRawIH.funIHType_eq E fuel 0 A (.bvar 0) (ds f) args f [] hread
  obtain ⟨ih, hih, hmem⟩ := PiRawIHAny.indexed_builder_mem
    (model P f) rfl σ f [] (PiValue.endValue (fun _ => True) 1) (PiValue.endValue_resp _ _)
    .zero v [] [dom f] [] rfl (PiRawIHAttack.family P f) (motive P f)
    (PiRawIHAnyAttack.motive_mem P f) E fuel A (ds f) args rfl (assignment P f)
    (fun _ _ => rfl) (.bvar 0) rfl hread (family_prop P f)
    (PiRawIHAnyAttack.field_mem P f (assignment P f)) (fun _ _ => datum) (leaf_map P f)
  have hi : ih = ihExpr f := Option.some.inj (hih.symm.trans hb)
  subst ih
  exact ⟨hb, hmem⟩

theorem original_read (f : Nat) :
    piTelescopeFuel emptyEnv 32 (Rcic.Declarative.lift 0 1 (field f)) =
      some (ds f, foldApps (.const f []) args) := by rfl

theorem value_mem (P : Premises4) (f : Nat) :
    indexedValue P f ∈ Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f)) :=
  (builder_at_read P f emptyEnv 32 (field f) (original_read f)).2

/-- Three actual-domain applications observe the nonempty data result. -/
theorem application (P : Premises4) (f : Nat) :
    Equiv (fapps (indexedValue P f)
      [PiPropPrefixAttack.datum, PiPropPrefixAttack.datum, PiPropPrefixAttack.datum]) datum := by
  let M := model P f
  let D := Ed M (M.μ (f + 1) [])
  let a := PiPropPrefixAttack.datum
  let H : PSet.{4} → PSet.{4} := fun z => lamVal M (tyv D) (classFiber D (fun _ => z))
  have hfit : TelFits M σ (ds f) (assignment P f) [a, a, a] :=
    (PiRawIHAnyAttack.inhabited P f).2.1
  have ha : a ∈ D := hfit.1
  have hH : ∀ z, Equiv (fapp (H z) a) z := by
    intro z
    have ha' : a ∈ Ed M (tyv D) :=
      mem_congr_right (ed_tyv M (dich_ed M (M.μ (f + 1) []))).symm ha
    refine (beta_val M (fun _ _ h => classFiber_congr D _ h) ha').trans ?_
    obtain ⟨j, hj⟩ := ha
    exact (classFiber_congr D _ hj.symm).trans (classFiber_at D _ j)
  change Equiv (fapp (fapp (fapp (H (H (H datum))) a) a) a) datum
  exact (fapp_congr ((fapp_congr (hH (H (H datum))) Equiv.rfl).trans
    (hH (H datum))) Equiv.rfl).trans (hH datum)

/-- The old graph-depth value fails the very same executable IH type. -/
theorem old_not_mem (P : Premises4) (f : Nat) :
    ihAtN (fun _ => datum) 3 pempty ∉
      Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f)) := by
  intro h
  let M := model P f
  let ρ := assignment P f
  let xs := [PiPropPrefixAttack.datum, PiPropPrefixAttack.datum, PiPropPrefixAttack.datum]
  have hfit : TelFits M σ (ds f) ρ xs := (PiRawIHAnyAttack.inhabited P f).2.1
  have hm := mem_fapps M σ
    (foldApps (Rcic.Declarative.lift 0 (ds f).length (.bvar 1))
      (args ++ [PiRawIH.fieldApp (ds f).length]))
    (ds f) ρ (ihAtN (fun _ => datum) 3 pempty) xs h hfit
  have he := PiRawIHAnyAttack.leaf P f xs hfit
  have hd := mem_singleton.mp (mem_congr_right
    ((ed_congr M he).trans (ed_tyv M PiRawIHAnyAttack.domain_dich)) hm)
  have h0 : Equiv (ihAtN (fun _ => datum) 3 pempty) pempty :=
    ihAtN_empty_succ (fun _ => datum) 2 Equiv.rfl
  exact dataVal_ne_pempty 17 [] (hd.symm.trans ((fapps_congr h0 xs).trans (fapps_pempty xs)))

def Witness (P : Premises4) (f : Nat) : Prop :=
  funIHType emptyEnv 32 0 (field f) (.bvar 0) 3 = some (ihExpr f) ∧
  pempty ∈ Ed (model P f) (den (model P f) σ (assignment P f) (field f)) ∧
  indexedValue P f ∈ Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f)) ∧
  Equiv (fapps (indexedValue P f)
    [PiPropPrefixAttack.datum, PiPropPrefixAttack.datum, PiPropPrefixAttack.datum]) datum ∧
  ihAtN (fun _ => datum) 3 pempty ∉
    Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f))

theorem inhabited (P : Premises4) (f : Nat) : Witness P f :=
  ⟨(builder_at_read P f emptyEnv 32 (field f) (original_read f)).1,
    PiRawIHAnyAttack.field_mem P f (assignment P f), value_mem P f, application P f, old_not_mem P f⟩

theorem component_nonrefutable (P : Premises4) (f : Nat) :
    ¬ (Witness P f → (Premises4 → False)) := fun h => h (inhabited P f) P

theorem hidden_reads : ∀ f ∈ [1, 2, 987],
    ∀ A ∈ [field f, PiRawIHAttack.beta f, PiRawIHAttack.delta f, PiRawIHAttack.zeta f],
    piTelescopeFuel (PiRawIHAttack.env f) 32 (Rcic.Declarative.lift 0 1 A) =
      some (ds f, foldApps (.const f []) args) := by decide

theorem hidden_values (P : Premises4) : ∀ f ∈ [1, 2, 987],
    ∀ A ∈ [field f, PiRawIHAttack.beta f, PiRawIHAttack.delta f, PiRawIHAttack.zeta f],
      funIHType (PiRawIHAttack.env f) 32 0 A (.bvar 0) 3 = some (ihExpr f) ∧
      indexedValue P f ∈ Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f)) :=
  fun f hf A hA => builder_at_read P f _ 32 A (hidden_reads f hf A hA)

/-- Typed telescope extensionality identifies any inhabitant of this raw IH type. -/
theorem value_unique (P : Premises4) (f : Nat) {y : PSet.{4}}
    (hy : y ∈ Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f))) :
    Equiv y (indexedValue P f) := by
  let M := model P f
  let ρ := assignment P f
  let b := foldApps (Rcic.Declarative.lift 0 (ds f).length (.bvar 1))
    (args ++ [PiRawIH.fieldApp (ds f).length])
  apply typed_tel_ext M σ (ds f) b ρ hy (value_mem P f)
  intro xs hxs
  have he := (ed_congr M (PiRawIHAnyAttack.leaf P f xs hxs)).trans
    (ed_tyv M PiRawIHAnyAttack.domain_dich)
  have hy' := mem_congr_right he (mem_fapps M σ b (ds f) ρ y xs hy hxs)
  have hi' := mem_congr_right he
    (mem_fapps M σ b (ds f) ρ (indexedValue P f) xs (value_mem P f) hxs)
  exact (mem_singleton.mp hy').trans (mem_singleton.mp hi').symm

theorem comparison_witness (P : Premises4) (f : Nat) :
    indexedValue P f ∈ Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f)) ∧
    ∀ y, y ∈ Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f)) →
      Equiv y (indexedValue P f) :=
  ⟨value_mem P f, fun _ hy => value_unique P f hy⟩

theorem comparison_nonrefutable (P : Premises4) (f : Nat) :
    ¬ ((indexedValue P f ∈ Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f)) ∧
      ∀ y, y ∈ Ed (model P f) (den (model P f) σ (assignment P f) (ihExpr f)) →
        Equiv y (indexedValue P f)) → (Premises4 → False)) :=
  fun h => h (comparison_witness P f) P

end Rcic.F3.PSet.PiIndexedIHBuilderAttack
