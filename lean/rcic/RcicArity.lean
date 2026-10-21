/-
RCIC Annex 22 UNIT A1 — the harity leaf (00 §19.3 C-6 (1) and C-6 (2)).

LEAF DISCIPLINE (annex 22.6 / A1-R0): this file has `rcic.RcicEnv` as its
ONLY import. It does not import `rcic.RcicLevelZero`: no A1 statement
consumes `levelIsZero`, `eqN_imax_zero_iff`, `eqN_imax_succ_ne_zero` or
`zeroRank` (22.7 D-13; 00 §20.10 P9 CONFIRMED). Rebuild closure is the
six-module RcicEnv import closure plus this file; the Diamond is not
rebuilt by an A1 iteration.

A1 does not reach Conv, ParRed, HasTy. Those names appear in this file
only in this sentence. The ring-free object C-6 (2) calls "harity's
first consumer" is stated at the level where it is true (A1-5, A1-6).
It is not "an arity-headed application is not Prop-typed" — C-6 (1)
measures that sentence false, and A1-7 pins the counterexample. It is
not a cut of the irr arm: C-6 (2) states that its use at irr re-enters
the ring at both horns and C-6 (3) records the ring; A1 does not go
there. It moves no 00 §19.2 row.

No sorry, no axiom, no Classical, no native_decide, no admit, no bare
simp. Statements of 22.1 verbatim. Type chains in Σ' / ×'.
-/
import rcic.RcicEnv

namespace Rcic.Declarative

/-! ## A1-1..A1-4 — ring-free isArity facts (00 §19.3 C-6 (2); 22.7 D-01) -/

/-- C-6 (2)'s first sub-lemma. `isArity` and `piResult` recurse through
the same `.pi` clause; the six non-`.sort` non-`.pi` arms die on
`isArity t = true`. `Σ'` and not `∃` (00 §18.3 rule 1). Lean 4
rejects `theorem` at a Type-valued conclusion, so this is a
`noncomputable def` with 22.1's type verbatim — the same keyword
ruling as `applyTel_cons_inv` (`def` at `Σ'`) plus `noncomputable`
because the `induction` tactic uses `Expr.rec`. -/
noncomputable def isArity_piResult_sort :
    (t : Expr Nat) → isArity t = true → Σ' l : Level, piResult t = .sort l := by
  intro t ht
  induction t with
  | sort l =>
      simp only [isArity, piResult] at ht ⊢
      exact ⟨l, rfl⟩
  | pi _ B _ ihB =>
      simp only [isArity, piResult] at ht ⊢
      exact ihB ht
  | bvar _ =>
      simp only [isArity] at ht
      exact Bool.noConfusion ht
  | const _ _ =>
      simp only [isArity] at ht
      exact Bool.noConfusion ht
  | app _ _ _ _ =>
      simp only [isArity] at ht
      exact Bool.noConfusion ht
  | lam _ _ _ _ =>
      simp only [isArity] at ht
      exact Bool.noConfusion ht
  | letE _ _ _ _ _ _ =>
      simp only [isArity] at ht
      exact Bool.noConfusion ht
  | lit _ =>
      simp only [isArity] at ht
      exact Bool.noConfusion ht

/-- C-6 (2)'s second sub-lemma, as an equality of Bools so it rewrites
in both directions. `instantiateLevels` preserves the head constructor;
`isArity` at `.pi` reads only the codomain. -/
theorem isArity_instantiateLevels :
    (ls : List Level) → (t : Expr Nat) →
    isArity (instantiateLevels ls t) = isArity t := by
  intro ls t
  induction t with
  | sort _ =>
      simp only [instantiateLevels, isArity]
  | pi _ b _ ihb =>
      simp only [instantiateLevels, isArity]
      exact ihb
  | bvar _ =>
      simp only [instantiateLevels, isArity]
  | const _ _ =>
      simp only [instantiateLevels, isArity]
  | app _ _ _ _ =>
      simp only [instantiateLevels, isArity]
  | lam _ _ _ _ =>
      simp only [instantiateLevels, isArity]
  | letE _ _ _ _ _ _ =>
      simp only [instantiateLevels, isArity]
  | lit _ =>
      simp only [instantiateLevels, isArity]

/-- NOT named by C-6 (2); derived from `applyTel`'s recursive clause
(22.7 D-01). Implication, not Bool-equality: the equality form is
FALSE (22.7 D-11) and the counterexample is the `example` below.
Induction generalizes `i` and `r` because the `.pi` clause moves both. -/
theorem isArity_instantiate :
    (t : Expr Nat) → (i : Nat) → (r : Expr Nat) →
    isArity t = true → isArity (instantiate i r t) = true := by
  intro t i r ht
  induction t generalizing i r with
  | sort _ =>
      simp only [instantiate, isArity]
  | pi _ b _ ihb =>
      simp only [isArity] at ht
      simp only [instantiate, isArity]
      exact ihb (i + 1) (lift 0 1 r) ht
  | bvar _ =>
      simp only [isArity] at ht
      exact Bool.noConfusion ht
  | const _ _ =>
      simp only [isArity] at ht
      exact Bool.noConfusion ht
  | app _ _ _ _ =>
      simp only [isArity] at ht
      exact Bool.noConfusion ht
  | lam _ _ _ _ =>
      simp only [isArity] at ht
      exact Bool.noConfusion ht
  | letE _ _ _ _ _ _ =>
      simp only [isArity] at ht
      exact Bool.noConfusion ht
  | lit _ =>
      simp only [isArity] at ht
      exact Bool.noConfusion ht

-- 22.7 D-11: the Bool-equality form of A1-3 is FALSE; this is
-- the witness. `instantiate` is not isArity-preserving at
-- `.bvar`.
example :
    isArity (instantiate 0 (.sort .zero) (.bvar 0 : Expr Nat))
        = true
      ∧ isArity (.bvar 0 : Expr Nat) = false := ⟨rfl, rfl⟩

/-- `applyTel` preserves `isArity`. Not `Σ' l, U = .sort l`: that
shape is false at `xs = []` with a non-empty telescope (22.7 D-02).
The sort form is recovered by composing with `isArity_piResult_sort`
through `piResult`. -/
theorem applyTel_isArity {T U : Expr Nat} :
    (xs : List (Expr Nat)) → isArity T = true →
    applyTel xs T = some U → isArity U = true := by
  intro xs hT happ
  induction xs generalizing T U with
  | nil =>
      simp only [applyTel_nil] at happ
      injection happ with hU
      subst hU
      exact hT
  | cons x xs ih =>
      obtain ⟨A, B, hTpi, happ'⟩ := applyTel_cons_inv x xs happ
      subst hTpi
      have hB : isArity B = true := by
        simp only [isArity] at hT
        exact hT
      have hInst : isArity (instantiate0 x B) = true :=
        isArity_instantiate B 0 x hB
      exact ih hInst happ'

/-! ## A1-5..A1-6 — the arity-typed consumer of `harity` -/

/-- THE ARITY-TYPED CONSUMER OF `harity` — the first proof that READS
the constructor field (`RcicEnv.lean` `EnvWf.indMember`'s `harity`).
`EnvWf` is Type-valued, so a recursion over it is a `def` (00 §20.8.L
D-1, settled). Template: `envWf_body_arity_zero`. The `.indMember`
hit arm applies `harity` to the class hypothesis. The eight `_harity`
elimination sites are not this file's to edit. -/
def envWf_isArity : {E : ResolvedEnv} → {n : Nat} → EnvWf E n →
    ∀ r m, E.members r = some m → m.mclass = .inductiveM →
    isArity m.mtype = true
  | _, _, .empty _ => fun _ _ hm _ => by
      simp only [emptyEnv] at hm
      cases hm
  | _, _, .axiom E r A u hE hfresh _hA _hcl => fun r' m' hm' hclass => by
      by_cases hrr : r' = r
      · subst hrr
        simp only [extendEnv, if_pos rfl] at hm'
        cases hm'
        exact MemberClass.noConfusion hclass
      · simp only [extendEnv, if_neg hrr] at hm'
        exact envWf_isArity hE r' m' hm' hclass
  | _, _, .definition E r A v u hE hfresh _hA _hv _hclA _hclv =>
      fun r' m' hm' hclass => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          exact MemberClass.noConfusion hclass
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envWf_isArity hE r' m' hm' hclass
  | _, _, .thm E r A p hE hfresh _hA _hp _hclA _hclp => fun r' m' hm' hclass => by
      by_cases hrr : r' = r
      · subst hrr
        simp only [extendEnv, if_pos rfl] at hm'
        cases hm'
        exact MemberClass.noConfusion hclass
      · simp only [extendEnv, if_neg hrr] at hm'
        exact envWf_isArity hE r' m' hm' hclass
  | _, _, .opaque E r A v u hE hfresh _hA _hv _hclA _hclv =>
      fun r' m' hm' hclass => by
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm'
          cases hm'
          exact MemberClass.noConfusion hclass
        · simp only [extendEnv, if_neg hrr] at hm'
          exact envWf_isArity hE r' m' hm' hclass
  | _, _, .indMember E r m hE hfresh _hind _hnobody _hclT harity _hlvlB _hcanon
      _harities _hidxAdm _hadm => fun r' m' hm' hclass => by
      by_cases hrr : r' = r
      · subst hrr
        simp only [extendEnv, if_pos rfl] at hm'
        cases hm'
        exact harity hclass
      · simp only [extendEnv, if_neg hrr] at hm'
        exact envWf_isArity hE r' m' hm' hclass

/-- The composite: an arity's applications land in an arity.
Method: A1-5, A1-2, A1-4. No new induction.

S-8: this is not "an arity-headed application is not Prop-typed"
(C-6 (1) measures that false; A1-7 pins the counterexample). It is
not a cut of the irr arm (C-6 (2): use at irr re-enters the ring at
both horns; C-6 (3) records the ring; A1 does not go there). It
moves no 00 §19.2 row. -/
theorem envWf_famApp_arity {E : ResolvedEnv} {n : Nat} {r : Nat}
    {m : CheckedMember} {ls : List Level} {xs : List (Expr Nat)}
    {U : Expr Nat} :
    EnvWf E n → E.members r = some m → m.mclass = .inductiveM →
    applyTel xs (instantiateLevels ls m.mtype) = some U →
    isArity U = true := by
  intro hE hm hclass happ
  have hT : isArity m.mtype = true := envWf_isArity hE r m hm hclass
  have hls : isArity (instantiateLevels ls m.mtype) = true := by
    rw [isArity_instantiateLevels ls m.mtype]
    exact hT
  exact applyTel_isArity xs hls happ

/-! ## A1-7..A1-8 — C-6 (1) pin at the landed `pinFamEnv` -/

/-- `EnvWf` ADMITS the Prop-valued family `pinFamEnv` (segment 11's
carrier: an inductive at ref 0 whose stored type IS `.sort .zero` and
IS an arity). Transcribed from `natEnvWfPrefixAt`'s innermost node
with universe arity `0 → 1` and level `.succ .zero → .zero`. Type-valued
conclusion, so a `def`. -/
def pinFamGroupView : PolicyFamilyView pinFamEnv where
  ref := 0
  member := ⟨.inductiveM, 1, .sort .zero, none⟩
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def pinFamGroupAdmitted :
    IndGroupAdmitted emptyEnv 0 ⟨.inductiveM, 1, .sort .zero, none⟩ :=
  .family rfl pinFamGroupView rfl rfl (Or.inl (fun _ => rfl))

def pinFamEnv_envWf (n : Nat) : EnvWf pinFamEnv n :=
  .indMember _ 0 ⟨.inductiveM, 1, .sort .zero, none⟩ (.empty n)
    rfl (Or.inl rfl) rfl (fun _ => rfl) (fun _ => rfl)
    rfl rfl rfl (fun h => absurd h (by decide)) pinFamGroupAdmitted

/-- The fixture is a real filter case, not a vacuous one: the tree's
four existing `isArity` pins are all at `.sort (.succ .zero)`-headed
types, and the one negative pin is at a `.bvar`-headed one. This is
the first Prop-valued family `harity` admits. -/
theorem pinFamEnv_member_isArity :
    isArity (⟨.inductiveM, 1, .sort .zero, none⟩ : CheckedMember).mtype
      = true := rfl

end Rcic.Declarative
