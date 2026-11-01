import rcic.RcicF3PiField

/-!
# Choice-free arguments for dependent telescope compilation

Quotient branch addresses must be read as actual set arguments when
compiling dependent domains. `classValue` constructs that argument by
unioning its equivalence class, without choosing a representative.

This is a semantic compilation component, not typed-syntax extraction
or a `StepAG` producer. `closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.F3.PSet.PiCompile
universe u v

/-- An extensional set value at a quotient address, without choice. -/
def classValue (A : PSet.{u}) (q : FBr A) : PSet.{u} :=
  sUnion (mk {i : A.Idx // Quotient.mk (FSetoid A) i = q} (fun i => A.Func i.1))

/-- Reading the class of an index retains precisely its set value. -/
theorem classValue_at (A : PSet.{u}) (i : A.Idx) :
    Equiv (classValue A (Quotient.mk (FSetoid A) i)) (A.Func i) := by
  apply sUnion_equiv_of_const
  · intro b hb
    obtain ⟨⟨j, hj⟩, he⟩ := hb
    exact he.symm.trans (Quotient.exact hj)
  · exact ⟨⟨i, rfl⟩, Equiv.refl _⟩

/-- Every quotient address reads an actual member of its domain. -/
theorem classValue_mem (A : PSet.{u}) (q : FBr A) : classValue A q ∈ A := by
  refine Quotient.inductionOn q ?_
  intro i
  exact mem_congr_left (classValue_at A i).symm ⟨i, Equiv.refl _⟩

/-- An extensional dependent codomain is recovered on every domain
member. Values outside the domain have no membership obligation. -/
theorem classFiber_value (A : PSet.{u}) (B : PSet.{u} → PSet.{u})
    (hB : ∀ a b, Equiv a b → Equiv (B a) (B b)) (a : PSet.{u}) (ha : a ∈ A) :
    Equiv (classFiber A (fun q => B (classValue A q)) a) (B a) := by
  obtain ⟨i, hi⟩ := ha
  exact (classFiber_congr A _ hi.symm).trans
    ((classFiber_at A _ i).trans (hB _ _ ((classValue_at A i).trans hi)))

/-- Elementary product congruence turns class readback into an exact
dependent-product interpretation. -/
theorem pi_classValue (A : PSet.{u}) (B : PSet.{u} → PSet.{u})
    (hB : ∀ a b, Equiv a b → Equiv (B a) (B b)) :
    Equiv (piSet A (classFiber A (fun q => B (classValue A q)))) (piSet A B) :=
  piSet_congr_on Equiv.rfl (fun _ _ h => classFiber_congr A _ h) hB
    (classFiber_value A B hB)

/-- Literal nested set products. `D m` is the next domain when `m`
binders remain after it; each domain can inspect the full environment. -/
def products (D : Nat → (Nat → PSet.{u}) → PSet.{u})
    (L : (Nat → PSet.{u}) → PSet.{u}) : Nat → (Nat → PSet.{u}) → PSet.{u}
  | 0, ρ => L ρ
  | m + 1, ρ => piSet (D m ρ) (fun a => products D L m (vcons a ρ))

/-- Compile dependent domains by reading actual arguments at quotient
addresses. `R` retains the result index after every binder. -/
def compile {I : Type v} (D : Nat → (Nat → PSet.{u}) → PSet.{u})
    (R : (Nat → PSet.{u}) → I) : (m : Nat) → (Nat → PSet.{u}) → RecTel.{u, v} I m
  | 0, ρ => .ret (R ρ)
  | m + 1, ρ => .pi (D m ρ)
      (fun q => compile D R m (vcons (classValue (D m ρ) q) ρ))

/-- Nested products respect pointwise-equivalent environments when
their domains and leaves do. No bound on the number of binders is used. -/
theorem products_congr (D : Nat → (Nat → PSet.{u}) → PSet.{u})
    (L : (Nat → PSet.{u}) → PSet.{u})
    (hD : ∀ m ρ ρ', (∀ j, Equiv (ρ j) (ρ' j)) → Equiv (D m ρ) (D m ρ'))
    (hL : ∀ ρ ρ', (∀ j, Equiv (ρ j) (ρ' j)) → Equiv (L ρ) (L ρ')) :
    ∀ m ρ ρ', (∀ j, Equiv (ρ j) (ρ' j)) →
      Equiv (products D L m ρ) (products D L m ρ') := by
  intro m
  induction m with
  | zero => exact hL
  | succ m ih =>
    intro ρ ρ' hρ
    exact piSet_congr (hD m ρ ρ' hρ)
      (fun a b h => ih _ _ (vcons_congr h hρ))

/-- The compiled telescope denotes exactly the literal nested products.
The premises are semantic extensionality of the supplied domains and
result selector; deriving them from typed syntax is a separate bridge. -/
theorem compile_spec {I : Type v} (D : Nat → (Nat → PSet.{u}) → PSet.{u})
    (R : (Nat → PSet.{u}) → I)
    (hD : ∀ m ρ ρ', (∀ j, Equiv (ρ j) (ρ' j)) → Equiv (D m ρ) (D m ρ'))
    (hR : ∀ ρ ρ', (∀ j, Equiv (ρ j) (ρ' j)) → R ρ = R ρ')
    (X : I → PSet.{u}) : ∀ m ρ,
      Equiv ((compile D R m ρ).denote X) (products D (fun ρ => X (R ρ)) m ρ) := by
  have hL : ∀ ρ ρ', (∀ j, Equiv (ρ j) (ρ' j)) →
      Equiv (X (R ρ)) (X (R ρ')) := by
    intro ρ ρ' hρ
    rw [hR ρ ρ' hρ]
    exact Equiv.rfl
  intro m
  induction m with
  | zero => intro ρ; exact Equiv.rfl
  | succ m ih =>
    intro ρ
    change Equiv
      (piSet (D m ρ) (classFiber (D m ρ) (fun q =>
        (compile D R m (vcons (classValue (D m ρ) q) ρ)).denote X)))
      (piSet (D m ρ) (fun a => products D (fun ρ => X (R ρ)) m (vcons a ρ)))
    apply piSet_congr_on (A := D m ρ) (A' := D m ρ)
      (B' := fun a => products D (fun ρ => X (R ρ)) m (vcons a ρ)) Equiv.rfl
      (fun _ _ h => classFiber_congr (D m ρ) _ h)
      (fun a b h => products_congr D _ hD hL m (vcons a ρ) (vcons b ρ)
        (vcons_congr h (fun j => Equiv.refl (ρ j))))
    intro a ha
    obtain ⟨i, hi⟩ := ha
    exact (classFiber_congr (D m ρ) _ hi.symm).trans
      ((classFiber_at (D m ρ) _ i).trans
        ((ih _).trans (products_congr D _ hD hL m
          (vcons (classValue (D m ρ) (Quotient.mk (FSetoid (D m ρ)) i)) ρ)
          (vcons a ρ)
          (vcons_congr ((classValue_at (D m ρ) i).trans hi)
            (fun j => Equiv.refl (ρ j))))))

end Rcic.F3.PSet.PiCompile
