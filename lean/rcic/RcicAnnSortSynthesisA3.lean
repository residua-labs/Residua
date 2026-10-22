import rcic.RcicAnnAlg

/-!
# Relational sort synthesis for the A3 head layer

`InferA3` follows the syntax-directed clauses of `inferA`, including both
recursive synthesis premises of a lambda and normalization of an application's
inferred function type.  Its parameter `W` is the new finite normal-form
relation; no old fuel predicate occurs in a constructor.

Inference uniqueness is proved by induction on the finite inference derivation
and functionality of `W`.  Sort uniqueness then uses that result and the same
normal-form uniqueness.  No declarative type-uniqueness premise is used.
The concrete head layer supplies `W` from its new typed chains and normality.
-/

namespace Rcic.Declarative.Ann.LR3Sort

open Rcic.Declarative

set_option autoImplicit false
set_option maxRecDepth 8192

abbrev WhnfRelA3 := LCtxA → ExprA → ExprA → Prop

def WhnfDetA3 (W : WhnfRelA3) : Prop :=
  ∀ (Γ : LCtxA) {a b c : ExprA}, W Γ a b → W Γ a c → b = c

def SortReflA3 (W : WhnfRelA3) : Prop :=
  ∀ (Γ : LCtxA) (l : Level), W Γ (.sort l) (.sort l)

/-- Finite syntax-directed synthesis, with explicit finite reduction witnesses
at exactly the two normalization sites of the old synthesis algorithm. -/
inductive InferA3 (E : ResolvedEnvA) (W : WhnfRelA3) :
    LCtxA → ExprA → ExprA → Prop
  | bvar {Γ : LCtxA} {i : Nat} {T : ExprA}
      (h : lookupTypeA Γ i = some T) : InferA3 E W Γ (.bvar i) T
  | sort (Γ : LCtxA) (l : Level) :
      InferA3 E W Γ (.sort l) (.sort (.succ l))
  | const {Γ : LCtxA} {r : Nat} {ls : List Level} {m : CheckedMemberA}
      (hres : E.members r = some m) (hlen : ls.length = m.arity) :
      InferA3 E W Γ (.const r ls) (instantiateLevelsA ls m.mtypeA)
  | pi (Γ : LCtxA) (D : ExprA) (u : Level) (C : ExprA) (v : Level) :
      InferA3 E W Γ (.pi D u C v) (.sort (.imax u v))
  | lam {Γ : LCtxA} {D : ExprA} {u : Level} {body B TB : ExprA} {v : Level}
      (hbody : InferA3 E W (.assumption D :: Γ) body B)
      (hB : InferA3 E W (.assumption D :: Γ) B TB)
      (hTB : W (.assumption D :: Γ) TB (.sort v)) :
      InferA3 E W Γ (.lam D u body) (.pi D u B v)
  | app {Γ : LCtxA} {f a Tf D B : ExprA} {u v : Level}
      (hf : InferA3 E W Γ f Tf)
      (hTf : W Γ Tf (.pi D u B v)) :
      InferA3 E W Γ (.app f a) (instantiate0A a B)
  | letE {Γ : LCtxA} {D value body B : ExprA}
      (hbody : InferA3 E W (.letBinding D value :: Γ) body B) :
      InferA3 E W Γ (.letE D value body) (instantiate0A value B)
  | lit {Γ : LCtxA} {t : Nat} {T : ExprA}
      (hexp : InferA3 E W Γ (natExpandA t) T) :
      InferA3 E W Γ (.lit t) T

/-- Uniqueness of synthesized syntax.  In the lambda case the first induction
hypothesis identifies the body type, the second identifies its synthesized type,
and normal-form uniqueness identifies its sort annotation. -/
theorem InferA3.det {E : ResolvedEnvA} {W : WhnfRelA3}
    (hW : WhnfDetA3 W) {Γ : LCtxA} {e T U : ExprA}
    (h : InferA3 E W Γ e T) (h' : InferA3 E W Γ e U) : T = U := by
  induction h generalizing U with
  | bvar h =>
      cases h' with
      | bvar h' => exact Option.some.inj (h.symm.trans h')
  | sort => cases h'; rfl
  | const hres hlen =>
      cases h' with
      | const hres' hlen' =>
          have hm := Option.some.inj (hres.symm.trans hres')
          cases hm
          rfl
  | pi => cases h'; rfl
  | lam hbody hB hTB ihBody ihB =>
      cases h' with
      | lam hbody' hB' hTB' =>
          have hb := ihBody hbody'
          cases hb
          have htb := ihB hB'
          cases htb
          have hv := ExprA.sort.inj (hW _ hTB hTB')
          cases hv
          rfl
  | app hf hTf ihF =>
      cases h' with
      | app hf' hTf' =>
          have ht := ihF hf'
          cases ht
          have hp := hW _ hTf hTf'
          cases hp
          rfl
  | letE hbody ihBody =>
      cases h' with
      | letE hbody' =>
          have hb := ihBody hbody'
          cases hb
          rfl
  | lit hexp ihExp =>
      cases h' with
      | lit hexp' => exact ihExp hexp'

/-- Sort synthesis carries both the inferred type and its new normal-form
witness.  It is a relation on the syntax and context, with no fuel index. -/
def SortOfA3 (E : ResolvedEnvA) (W : WhnfRelA3) (Γ : LCtxA)
    (A : ExprA) (l : Level) : Prop :=
  ∃ T, InferA3 E W Γ A T ∧ W Γ T (.sort l)

def IsPropTyA3 (E : ResolvedEnvA) (W : WhnfRelA3) (Γ : LCtxA)
    (A : ExprA) : Prop :=
  ∃ l, SortOfA3 E W Γ A l ∧ isZero l = true

/-- Sort uniqueness uses inference uniqueness as well as the finite-chain
uniqueness contract; a chain lemma alone cannot identify two inferred types. -/
theorem SortOfA3.det {E : ResolvedEnvA} {W : WhnfRelA3}
    (hW : WhnfDetA3 W) {Γ : LCtxA} {A : ExprA} {l l' : Level}
    (h : SortOfA3 E W Γ A l) (h' : SortOfA3 E W Γ A l') : l = l' := by
  obtain ⟨T, ht, hw⟩ := h
  obtain ⟨T', ht', hw'⟩ := h'
  have hT := ht.det hW ht'
  cases hT
  exact ExprA.sort.inj (hW Γ hw hw')

theorem SortOfA3.sort {E : ResolvedEnvA} {W : WhnfRelA3}
    (hSort : SortReflA3 W) (Γ : LCtxA) (l : Level) :
    SortOfA3 E W Γ (.sort l) (.succ l) :=
  ⟨.sort (.succ l), .sort Γ l, hSort Γ (.succ l)⟩

theorem SortOfA3.pi {E : ResolvedEnvA} {W : WhnfRelA3}
    (hSort : SortReflA3 W) (Γ : LCtxA) (D : ExprA) (u : Level)
    (C : ExprA) (v : Level) :
    SortOfA3 E W Γ (.pi D u C v) (.imax u v) :=
  ⟨.sort (.imax u v), .pi Γ D u C v, hSort Γ (.imax u v)⟩

/-- Once a synthesized sort is supplied, the Prop key is exactly the old
syntactic Boolean test of that level. -/
theorem isPropTyA3_iff_of_sort {E : ResolvedEnvA} {W : WhnfRelA3}
    (hW : WhnfDetA3 W) {Γ : LCtxA} {A : ExprA} {l : Level}
    (h : SortOfA3 E W Γ A l) : IsPropTyA3 E W Γ A ↔ isZero l = true := by
  constructor
  · intro ⟨l', h', hz⟩
    have hl := h'.det hW h
    cases hl
    exact hz
  · intro hz
    exact ⟨l, h, hz⟩

theorem not_isPropTyA3_of_sort {E : ResolvedEnvA} {W : WhnfRelA3}
    (hW : WhnfDetA3 W) {Γ : LCtxA} {A : ExprA} {l : Level}
    (h : SortOfA3 E W Γ A l) (hz : isZero l = false) :
    ¬ IsPropTyA3 E W Γ A := by
  intro hp
  have he := (isPropTyA3_iff_of_sort hW h).mp hp
  rw [hz] at he
  exact Bool.noConfusion he

theorem not_isPropTyA3_sort {E : ResolvedEnvA} {W : WhnfRelA3}
    (hW : WhnfDetA3 W) (hSort : SortReflA3 W) (Γ : LCtxA) (l : Level) :
    ¬ IsPropTyA3 E W Γ (.sort l) :=
  not_isPropTyA3_of_sort hW (SortOfA3.sort hSort Γ l) rfl

/-- The Pi key remains decidable from the codomain annotation.  No domain
validity, conversion decision, or declarative type-uniqueness premise is added. -/
theorem isPropTyA3_pi_iff {E : ResolvedEnvA} {W : WhnfRelA3}
    (hW : WhnfDetA3 W) (hSort : SortReflA3 W) (Γ : LCtxA)
    (D : ExprA) (u : Level) (C : ExprA) (v : Level) :
    IsPropTyA3 E W Γ (.pi D u C v) ↔ isZero v = true := by
  rw [isPropTyA3_iff_of_sort hW (SortOfA3.pi hSort Γ D u C v)]
  rfl

#print axioms InferA3.det
#print axioms SortOfA3.det
#print axioms SortOfA3.sort
#print axioms SortOfA3.pi
#print axioms isPropTyA3_iff_of_sort
#print axioms not_isPropTyA3_of_sort
#print axioms not_isPropTyA3_sort
#print axioms isPropTyA3_pi_iff

end Rcic.Declarative.Ann.LR3Sort
