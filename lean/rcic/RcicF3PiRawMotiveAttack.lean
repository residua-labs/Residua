import rcic.RcicF3PiRawMotive
import rcic.RcicF3PiIndexAttack
/-! Inhabited raw proof-motive, hidden forms and guarded-domain attacks.
These are raw motive/IH components, not complete raw recursor groups.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiRawMotiveAttack
open Rcic.Declarative PiIndex PiRawMotive
universe u

def table (f : Nat) : Nat → List Nat → PSet.{4} :=
  fun r _ => if r = f then PiPropPrefixAttack.proofTy else pempty

def beta (f : Nat) : Expr Nat :=
  .app (.lam (.sort .zero) (.bvar 0)) (.const f [])
def zeta (f : Nat) : Expr Nat :=
  .letE (.sort .zero) (.const f []) (.bvar 0)

theorem forms (P : Premises4) (f : Nat) (σ : Nat → Nat) :
    ∀ A ∈ [Expr.const f [], beta f, zeta f],
      Equiv (den (mkM P (table f)) σ ρ0 A) PiPropPrefixAttack.proofTy := by
  intro A hA
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl
  · change Equiv (if f = f then PiPropPrefixAttack.proofTy else pempty) _
    rw [if_pos rfl]
    exact Equiv.rfl
  · have hf : (PiPropPrefixAttack.proofTy : PSet.{4}) ∈
        Ed (mkM P (table f)) (tyv (U W4 0)) := by
      apply mem_congr_right (ed_tyv _ (U4_dich 0)).symm
      exact mem_sImage_tyv.mpr ⟨_, mem_propSets.mpr (fun _ h => (mem_tv.mp h).2), Equiv.rfl⟩
    change Equiv (fapp (lamVal (mkM P (table f)) (tyv (U W4 0)) (fun x => x))
      (if f = f then PiPropPrefixAttack.proofTy else pempty)) _
    rw [if_pos rfl]
    exact beta_val _ (fun _ _ h => h) hf
  · change Equiv (if f = f then PiPropPrefixAttack.proofTy else pempty) _
    rw [if_pos rfl]
    exact Equiv.rfl

/-- Actual raw abstraction type membership, guarded exactness, and both
ordinary and aliased proof majors are inhabited at every numeric label. -/
theorem typed_forms (P : Premises4) (f : Nat) (σ : Nat → Nat) :
    let M := mkM P (table f)
    ∀ A ∈ [Expr.const f [], beta f, zeta f],
      let mo := PiValue.value M σ (fun _ => True) [A] ρ0
      mo ∈ Ed M (den M σ ρ0 (policyPi [A] (.sort .zero))) ∧
      ∀ z ∈ ([pempty, PiPropPrefixAttack.alias] : List PSet.{4}),
        z ∈ Ed M PiPropPrefixAttack.proofTy ∧
        Equiv (guarded M σ PiPropPrefixAttack.proofTy mo [] [] ρ0 (key []) z)
          (Ed M (fapps mo [z])) ∧
        pempty ∈ guarded M σ PiPropPrefixAttack.proofTy mo [] [] ρ0 (key []) z := by
  dsimp only
  intro A hA
  let M := mkM P (table f)
  let mo := PiValue.value M σ (fun _ => True) [A] ρ0
  refine ⟨PiValue.value_mem P (table f) σ (fun _ => True) [A] ρ0, ?_⟩
  intro z hz
  have hproof : z ∈ Ed M PiPropPrefixAttack.proofTy := by
    apply mem_congr_right (ed_tyv M (dich_tv True)).symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact mem_tv.mpr ⟨True.intro, Equiv.rfl⟩
    · exact mem_tv.mpr ⟨True.intro, PiPropPrefixAttack.alias_equiv⟩
  have hfit : TelFits M σ [A] ρ0 [z] := by
    exact ⟨mem_congr_right (ed_congr M (forms P f σ A hA)).symm hproof, True.intro⟩
  have hread := PiValue.apply_ed M σ (fun _ => True) [A] ρ0 [z] hfit
  have he := guarded_key M σ PiPropPrefixAttack.proofTy mo [] [] ρ0 [] z
    True.intro hproof (fun y hy => PiValue.complete_empty M σ (fun _ => True)
      [A] ρ0 [z] rfl hy)
  refine ⟨hproof, he, ?_⟩
  apply mem_congr_right he.symm
  exact mem_congr_right hread.symm (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)

/-- Unused labels are retained: outside the fitting label the guard can be
inhabited even when the actual raw motive is empty. Exactness needs its domain. -/
theorem unused_label (M : Interp.{u}) (σ : Nat → Nat) :
    let mo := lamVal M PiPropPrefixAttack.proofTy (fun _ => tyv (tv False))
    pempty ∈ guarded M σ PiPropPrefixAttack.proofTy mo [] [] (fun _ => pempty) (key [pempty]) pempty ∧
      pempty ∉ Ed M (fapps mo [pempty]) ∧
      ¬ Equiv (guarded M σ PiPropPrefixAttack.proofTy mo [] [] (fun _ => pempty)
        (key [pempty]) pempty) (Ed M (fapps mo [pempty])) := by
  dsimp only
  let mo := lamVal M PiPropPrefixAttack.proofTy (fun _ => tyv (tv False))
  have hz : (pempty : PSet.{u}) ∈ Ed M PiPropPrefixAttack.proofTy :=
    mem_congr_right (ed_tyv M (dich_tv True)).symm
      (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)
  have hg : pempty ∈ guarded M σ PiPropPrefixAttack.proofTy mo [] []
      (fun _ => pempty) (key [pempty]) pempty := by
    apply mem_tv.mpr
    refine ⟨?_, Equiv.rfl⟩
    intro is hi hf _
    cases is with
    | nil => exact False.elim (PiIndexAttack.extra_argument_refused [] hi)
    | cons _ _ => cases hf
  have hn : pempty ∉ Ed M (fapps mo [pempty]) := by
    intro h
    have he := beta_val M (b := fun _ => tyv (tv False))
      (fun _ _ _ => Equiv.rfl) hz
    have hm := mem_congr_right ((ed_congr M he).trans (ed_tyv M (dich_tv False))) h
    exact (mem_tv.mp hm).1
  exact ⟨hg, hn, fun he => hn (mem_congr_right he hg)⟩

/-- A genuine data-valued raw motive is inhabited, but cannot be replaced
by the proof guard. This pins the propOnly boundary of this bridge. -/
theorem data_guard_refused (M : Interp.{u}) (σ : Nat → Nat) (tag : Nat) :
    let mo := lamVal M PiPropPrefixAttack.proofTy
      (fun _ => tyv (singleton (dataVal tag [])))
    dataVal tag [] ∈ Ed M (fapps mo [pempty]) ∧
      pempty ∉ guarded M σ PiPropPrefixAttack.proofTy mo [] []
        (fun _ => pempty) (key []) pempty ∧
      ¬ Equiv (guarded M σ PiPropPrefixAttack.proofTy mo [] []
        (fun _ => pempty) (key []) pempty) (Ed M (fapps mo [pempty])) := by
  dsimp only
  let mo := lamVal M PiPropPrefixAttack.proofTy
    (fun _ => tyv (singleton (dataVal tag [])))
  have hz : (pempty : PSet.{u}) ∈ Ed M PiPropPrefixAttack.proofTy :=
    mem_congr_right (ed_tyv M (dich_tv True)).symm
      (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)
  have hd : Dich (singleton (dataVal tag []) : PSet.{u}) :=
    Or.inr (fun h => dataVal_ne_pempty tag [] (mem_singleton.mp h).symm)
  have he := (ed_congr M (beta_val M
    (b := fun _ => tyv (singleton (dataVal tag [])))
    (fun _ _ _ => Equiv.rfl) hz)).trans (ed_tyv M hd)
  have hm : dataVal tag [] ∈ Ed M (fapps mo [pempty]) :=
    mem_congr_right he.symm (mem_singleton.mpr Equiv.rfl)
  have hn : pempty ∉ guarded M σ PiPropPrefixAttack.proofTy mo [] []
      (fun _ => pempty) (key []) pempty := by
    intro h
    have hh := (mem_tv.mp h).1 [] rfl True.intro hz
    exact dataVal_ne_pempty tag [] (mem_singleton.mp (mem_congr_right he hh)).symm
  refine ⟨hm, hn, ?_⟩
  intro h
  exact dataVal_ne_pempty tag [] (guarded_prop M σ PiPropPrefixAttack.proofTy mo
    [] [] (fun _ => pempty) (key []) pempty (dataVal tag [])
      (mem_congr_right h.symm hm))

/-- This actual typed constant proof motive supplies the IH face globally;
the fitting branch is constructed from family membership, not assumed. -/
theorem total_forms (P : Premises4) (f : Nat) (σ : Nat → Nat)
    (A : Expr Nat) (hA : A ∈ [Expr.const f [], beta f, zeta f]) :
    let M := mkM P (table f)
    let mo := PiValue.value M σ (fun _ => True) [A] ρ0
    ∀ i z, pempty ∈ guarded M σ PiPropPrefixAttack.proofTy mo [] [] ρ0 i z := by
  dsimp only
  intro i z
  apply mem_tv.mpr
  refine ⟨?_, Equiv.rfl⟩
  intro is _ hf hz
  cases is with
  | nil =>
    have ht : TelFits (mkM P (table f)) σ [A] ρ0 [z] :=
      ⟨mem_congr_right (ed_congr _ (forms P f σ A hA)).symm hz, True.intro⟩
    exact mem_congr_right (PiValue.apply_ed _ σ (fun _ => True) [A] ρ0 [z] ht).symm
      (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)
  | cons _ _ => cases hf

def triple : RecTel.{4,5} Index.{4} 3 :=
  .pi (tv True) (fun _ => .pi (tv True) (fun _ => .pi (tv True) (fun _ => .ret (key []))))

theorem triple_dich : triple.DomainsDich :=
  ⟨dich_tv True, fun _ => ⟨dich_tv True, fun _ => ⟨dich_tv True, fun _ => True.intro⟩⟩⟩

/-- Actual depth-three field and IH values inhabit the guard, and each IH
read has the original raw motive's element set. Raw group extraction is open. -/
theorem triple_readback (P : Premises4) (f : Nat) (σ : Nat → Nat)
    (A : Expr Nat) (hA : A ∈ [Expr.const f [], beta f, zeta f]) :
    let M := mkM P (table f)
    let mo := PiValue.value M σ (fun _ => True) [A] ρ0
    ∃ x ih, x ∈ Ed M (triple.erasedType M (fun _ => tv True)) ∧
      ih ∈ Ed M (triple.erasedIHType M
        (guarded M σ PiPropPrefixAttack.proofTy mo [] [] ρ0) x) ∧
      ∀ p, triple.tel.flatten (triple.erasedRead M ih) p ∈ Ed M
        (fapps mo [triple.tel.flatten (triple.erasedRead M x) p]) := by
  dsimp only
  let M := mkM P (table f)
  let mo := PiValue.value M σ (fun _ => True) [A] ρ0
  let C := guarded M σ PiPropPrefixAttack.proofTy mo [] [] ρ0
  let X : Index.{4} → PSet.{4} := fun _ => tv True
  let v : PiTel.Value.{4,5} triple.tel (fun _ => PSet.{4}) :=
    triple.tel.unflatten (fun _ => pempty)
  let x := triple.erasedEncode M v
  have hx : x ∈ Ed M (triple.erasedType M X) := by
    apply triple.erasedEncode_mem M triple_dich X (fun _ => dich_tv True)
    apply (PiTel.all_iff _ _ _).mpr
    intro p
    rw [PiTel.flatten_unflatten]
    exact mem_tv.mpr ⟨True.intro, Equiv.rfl⟩
  let ih := triple.erasedIH M (fun _ => pempty) x
  have hi : ih ∈ Ed M (triple.erasedIHType M C x) :=
    triple.erasedIH_mem M triple_dich X (fun _ => dich_tv True) C
      (guarded_dich M σ PiPropPrefixAttack.proofTy mo [] [] ρ0)
      (fun _ => pempty) (fun i z _ => total_forms P f σ A hA i z) hx
  refine ⟨x, ih, hx, hi, ?_⟩
  intro p
  apply guarded_ih_read M σ PiPropPrefixAttack.proofTy mo [] [] ρ0
    triple triple_dich x ih hi p [] rfl True.intro
  have hr := (triple.erasedRead_spec M triple_dich X (fun _ => dich_tv True) hx).1
  exact mem_congr_right (ed_tyv M (dich_tv True)).symm
    ((PiTel.all_iff _ _ _).mp hr p)

end Rcic.F3.PSet.PiRawMotiveAttack
