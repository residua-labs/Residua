import rcic.RcicF3PSet

/-!
# Canonical extraction from a bounded functional evaluation relation

Separation is saturated under Equiv, so it respects the bound's stored
representatives. Union then extracts the unique extensional result without
selecting an existential witness. Evaluation existence and functionality
are explicit inputs to correctness, not universal producers. closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PropEvalExtract
universe u

def Sat (R : PSet.{u} → Prop) (x : PSet.{u}) : Prop :=
  ∃ v : PSet.{u}, R v ∧ Equiv x v

def collected (T : PSet.{u}) (R : PSet.{u} → Prop) : PSet.{u} :=
  sep (Sat R) T

def value (T : PSet.{u}) (R : PSet.{u} → Prop) : PSet.{u} :=
  sUnion (collected T R)

variable {R S : PSet.{u} → Prop} {T U A v x y : PSet.{u}}

theorem sat_self (h : R x) : Sat R x := ⟨x, h, Equiv.rfl⟩

theorem sat_congr (h : Equiv x y) : Sat R x ↔ Sat R y := by
  constructor
  · rintro ⟨v, hv, hx⟩; exact ⟨v, hv, h.symm.trans hx⟩
  · rintro ⟨v, hv, hy⟩; exact ⟨v, hv, h.trans hy⟩

theorem mem_collected : x ∈ collected T R ↔ x ∈ T ∧ Sat R x := by
  constructor
  · intro hx
    obtain ⟨i, hi, he⟩ := mem_sep.mp hx
    exact ⟨⟨i, he⟩, (sat_congr he).mp hi⟩
  · rintro ⟨⟨i, he⟩, hx⟩
    exact mem_sep.mpr ⟨i, (sat_congr he).mpr hx, he⟩

/-- The result may itself be empty; the collection must contain a result. -/
theorem union_eq_of_mem {C : PSet.{u}} (hv : v ∈ C)
    (hAll : ∀ t, t ∈ C → Equiv t v) : Equiv (sUnion C) v := by
  apply ext
  intro z
  constructor
  · intro hz
    obtain ⟨t, ht, hz⟩ := mem_sUnion.mp hz
    exact mem_congr_right (hAll t ht) hz
  · intro hz
    exact mem_sUnion.mpr ⟨v, hv, hz⟩

theorem value_equiv (hv : v ∈ T) (hr : R v)
    (hfun : ∀ x y, x ∈ T → y ∈ T → R x → R y → Equiv x y) :
    Equiv (value T R) v := by
  apply union_eq_of_mem
  · exact mem_collected.mpr ⟨hv, sat_self hr⟩
  · intro x hx
    obtain ⟨hx, w, hw, he⟩ := mem_collected.mp hx
    exact he.trans (hfun w v (mem_congr_left he hx) hv hw hr)

/-- Checked composition of existence, bounded functionality and output typing. -/
theorem value_spec (hex : ∃ v, v ∈ T ∧ R v)
    (hfun : ∀ x y, x ∈ T → y ∈ T → R x → R y → Equiv x y)
    (htype : ∀ v, v ∈ T → R v → v ∈ A) :
    value T R ∈ A ∧ Sat R (value T R) := by
  obtain ⟨v, hv, hr⟩ := hex
  have he := value_equiv hv hr hfun
  exact ⟨mem_congr_left he.symm (htype v hv hr), ⟨v, hr, he⟩⟩

theorem value_mem_bound (hex : ∃ v, v ∈ T ∧ R v)
    (hfun : ∀ x y, x ∈ T → y ∈ T → R x → R y → Equiv x y) :
    value T R ∈ T := (value_spec hex hfun (fun _ hv _ => hv)).1

/-- Literal evaluation follows when the relation has output congruence. -/
theorem value_spec_of_output_congr (hex : ∃ v, v ∈ T ∧ R v)
    (hfun : ∀ x y, x ∈ T → y ∈ T → R x → R y → Equiv x y)
    (htype : ∀ v, v ∈ T → R v → v ∈ A)
    (hout : ∀ x y, Equiv x y → R x → R y) :
    value T R ∈ A ∧ R (value T R) := by
  obtain ⟨ht, v, hv, he⟩ := value_spec hex hfun htype
  exact ⟨ht, hout v _ he.symm hv⟩

/-- Extensional read transport for the bounded extraction component. -/
theorem collected_congr (hTU : Equiv T U)
    (hSat : ∀ x, Sat R x ↔ Sat S x) :
    Equiv (collected T R) (collected U S) := by
  apply ext
  intro x
  constructor
  · intro hx
    obtain ⟨ht, hr⟩ := mem_collected.mp hx
    exact mem_collected.mpr ⟨mem_congr_right hTU ht, (hSat x).mp hr⟩
  · intro hx
    obtain ⟨ht, hr⟩ := mem_collected.mp hx
    exact mem_collected.mpr ⟨mem_congr_right hTU.symm ht, (hSat x).mpr hr⟩

theorem value_congr (hTU : Equiv T U) (hSat : ∀ x, Sat R x ↔ Sat S x) :
    Equiv (value T R) (value U S) := sUnion_congr (collected_congr hTU hSat)

/-- Extraction does not create a result when the relation has no inhabitant. -/
theorem value_empty (h : ∀ x, ¬ R x) : Equiv (value T R) pempty := by
  apply ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, _⟩ := mem_sUnion.mp hz
    obtain ⟨_, v, hv, _⟩ := mem_collected.mp hx
    exact (h v hv).elim
  · intro hz
    exact (not_mem_pempty hz).elim

/-- An unconditional inhabited result relation, including an empty result. -/
theorem singleton_witness (target : PSet.{u}) :
    (∃ v, v ∈ singleton target ∧ Equiv v target) ∧
      Equiv (value (singleton target) (fun v => Equiv v target)) target := by
  refine ⟨⟨target, mem_singleton.mpr Equiv.rfl, Equiv.rfl⟩, ?_⟩
  exact value_equiv (mem_singleton.mpr Equiv.rfl) Equiv.rfl
    (fun _ _ _ _ hx hy => hx.trans hy.symm)

theorem singleton_nonrefutable (target : PSet.{u}) :
    ¬ (Equiv (value (singleton target) (fun v => Equiv v target)) target → False) :=
  fun h => h (singleton_witness target).2

theorem empty_result :
    Equiv (value (singleton (pempty : PSet.{u})) (fun v => Equiv v pempty)) pempty :=
  (singleton_witness pempty).2

theorem nonempty_result : (pempty : PSet.{u}) ∈
    value (singleton (singleton pempty)) (fun v => Equiv v (singleton pempty)) :=
  mem_congr_right (singleton_witness (singleton pempty)).2.symm
    (mem_singleton.mpr Equiv.rfl)

/-- The predicate can distinguish literal presentations: saturation still
uses a bound which stores an equivalent representative of the desired result. -/
theorem representative_witness (v w : PSet.{u}) (h : Equiv v w) :
    Equiv (value (singleton w) (fun z => z = v)) v := by
  exact value_equiv (mem_singleton.mpr h) rfl
    (fun _ _ _ _ hx hy => by subst_vars; exact Equiv.rfl)

end Rcic.F3.PSet.PropEvalExtract
