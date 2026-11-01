import rcic.RcicF3PiEraseField
/-!
# Compile dependent semantic domains with R-CIC proof erasure

Every binder domain is obtained from `Ed`; its dichotomy is proved, not
assumed. The compiled telescope denotes the actual nested `piVal` type,
including empty and proof domains. Domain and result extensionality are
explicit semantic premises. Their raw typed-syntax extraction is unpaid.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiEraseCompile
universe u v

/-- Products depend on the domain element set, including when empty. -/
theorem piVal_ed_domain (M : Interp.{u}) (A : PSet.{u}) (B : PSet.{u} → PSet.{u})
    (hB : ∀ a b, Equiv a b → Equiv (B a) (B b)) :
    Equiv (piVal M (tyv (Ed M A)) B) (piVal M A B) := by
  have eA := ed_tyv M (dich_ed M A)
  apply tyv_congr
  apply cond_congr
  · constructor
    · intro h x hx
      exact h x (mem_congr_right eA.symm hx)
    · intro h x hx
      exact h x (mem_congr_right eA hx)
  · apply ext; intro z; constructor
    · intro hz
      obtain ⟨hφ, hz⟩ := mem_tv.mp hz
      exact mem_tv.mpr ⟨fun x hx => hφ x (mem_congr_right eA.symm hx), hz⟩
    · intro hz
      obtain ⟨hφ, hz⟩ := mem_tv.mp hz
      exact mem_tv.mpr ⟨fun x hx => hφ x (mem_congr_right eA hx), hz⟩
  · exact piSet_congr_on eA (fun a b h => ed_congr M (hB a b h))
      (fun a b h => ed_congr M (hB a b h)) (fun _ _ => Equiv.rfl)

/-- Product values use the actual type denotation at each argument binder. -/
def products (M : Interp.{u}) (D : Nat → (Nat → PSet.{u}) → PSet.{u})
    (L : (Nat → PSet.{u}) → PSet.{u}) : Nat → (Nat → PSet.{u}) → PSet.{u}
  | 0, ρ => L ρ
  | m + 1, ρ => piVal M (D m ρ) (fun a => products M D L m (vcons a ρ))

/-- All compiler domains are Ed element sets; no premise about their
inhabitation or proof face is required. -/
def compile {I : Type v} (M : Interp.{u})
    (D : Nat → (Nat → PSet.{u}) → PSet.{u}) (R : (Nat → PSet.{u}) → I) :=
  PiCompile.compile (fun m ρ => Ed M (D m ρ)) R

/-- Structural induction; each domain invariant is the existing dich_ed law. -/
theorem compile_domains {I : Type v} (M : Interp.{u})
    (D : Nat → (Nat → PSet.{u}) → PSet.{u}) (R : (Nat → PSet.{u}) → I) :
    ∀ m ρ, (compile M D R m ρ).DomainsDich := by
  intro m
  induction m with
  | zero => intro ρ; trivial
  | succ m ih =>
    intro ρ
    exact ⟨dich_ed M _, fun _ => ih _⟩

/-- Nested product values respect equivalent argument environments. -/
theorem products_congr (M : Interp.{u})
    (D : Nat → (Nat → PSet.{u}) → PSet.{u}) (L : (Nat → PSet.{u}) → PSet.{u})
    (hD : ∀ m ρ ρ', (∀ j, Equiv (ρ j) (ρ' j)) → Equiv (D m ρ) (D m ρ'))
    (hL : ∀ ρ ρ', (∀ j, Equiv (ρ j) (ρ' j)) → Equiv (L ρ) (L ρ')) :
    ∀ m ρ ρ', (∀ j, Equiv (ρ j) (ρ' j)) →
      Equiv (products M D L m ρ) (products M D L m ρ') := by
  intro m
  induction m with
  | zero => exact hL
  | succ m ih =>
    intro ρ ρ' hρ
    exact piVal_congr M (hD m ρ ρ' hρ)
      (fun a b h => ih _ _ (vcons_congr h hρ))

/-- Exact actual-product semantics of the compiled telescope. Arbitrary
finite depth and dependent result indices are retained. -/
theorem compile_spec {I : Type v} (M : Interp.{u})
    (D : Nat → (Nat → PSet.{u}) → PSet.{u}) (R : (Nat → PSet.{u}) → I)
    (hD : ∀ m ρ ρ', (∀ j, Equiv (ρ j) (ρ' j)) → Equiv (D m ρ) (D m ρ'))
    (hR : ∀ ρ ρ', (∀ j, Equiv (ρ j) (ρ' j)) → R ρ = R ρ')
    (X : I → PSet.{u}) (hX : ∀ i, Dich (X i)) : ∀ m ρ,
      Equiv ((compile M D R m ρ).erasedType M X)
        (products M D (fun ρ => tyv (X (R ρ))) m ρ) := by
  have hL : ∀ ρ ρ', (∀ j, Equiv (ρ j) (ρ' j)) →
      Equiv (tyv (X (R ρ))) (tyv (X (R ρ'))) := by
    intro ρ ρ' hρ
    rw [hR ρ ρ' hρ]
    exact Equiv.rfl
  intro m
  induction m with
  | zero => intro ρ; exact Equiv.rfl
  | succ m ih =>
    intro ρ
    let A := Ed M (D m ρ)
    let C := fun a => tyv (classFiber A (fun q =>
      Ed M ((compile M D R m (vcons (PiCompile.classValue A q) ρ)).erasedType M X)) a)
    have hC : ∀ a b, Equiv a b → Equiv (C a) (C b) :=
      fun _ _ h => tyv_congr (classFiber_congr A _ h)
    change Equiv (piVal M (tyv A) C)
      (piVal M (D m ρ) (fun a => products M D (fun ρ => tyv (X (R ρ))) m (vcons a ρ)))
    apply Equiv.trans (piVal_ed_domain M (D m ρ) C hC)
    apply piVal_congr_on M (B' := fun a => products M D (fun ρ => tyv (X (R ρ))) m (vcons a ρ))
      Equiv.rfl hC (fun a b h => products_congr M D _ hD hL m _ _
        (vcons_congr h (fun _ => Equiv.rfl)))
    intro a ha
    obtain ⟨i, hi⟩ := ha
    let q := Quotient.mk (FSetoid A) i
    have ef := (classFiber_congr A (fun q =>
      Ed M ((compile M D R m (vcons (PiCompile.classValue A q) ρ)).erasedType M X))
      hi.symm).trans (classFiber_at A _ i)
    exact (tyv_congr ef).trans
      (((compile M D R m (vcons (PiCompile.classValue A q) ρ)).erasedType_tagged M X hX).trans
        ((ih _).trans (products_congr M D _ hD hL m _ _
          (vcons_congr ((PiCompile.classValue_at A i).trans hi) (fun _ => Equiv.rfl)))))

end Rcic.F3.PSet.PiEraseCompile
