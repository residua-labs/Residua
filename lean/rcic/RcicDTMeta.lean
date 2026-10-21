/-
RCIC DT metatheory — knife 2 M-010 FINAL batch.
All templates on main (#3683-3694): SubstCalc, CtxMorph, Weaken, Subst,
Invert, InvertFamily (6 inversions), SortConvChar/PiConvInj obligations.

Debt-carrying theorems use the inversion family + named obligations:
- DT-023: hasTyBvarEmptyFalse witness (direct from #3694)
- DT-021: SortConvChar premise (confluence-class obligation)
- DT-012: double inversion + PiConvInj premise
- DT-010/011: Step case analysis + PiConvInj + hasTySubst
- DT-006: letBinding variant (mechanical, same pattern)
-/
import rcic.RcicDeclarative
import rcic.RcicSubstCalc
import rcic.RcicDerivationRec
import rcic.RcicCtxMorph
import rcic.RcicWeaken
import rcic.RcicSubst
import rcic.RcicInvert
import rcic.RcicInvertFamily
import rcic.RcicSubstLet
import rcic.RcicIota
import rcic.RcicEnv

namespace Rcic.Declarative

/-! ## IDX-R2: the `n = 0` openness supply

`idxSrcLevelsOpen` (`RcicDeclarative.lean:1329`) is the declaration-side
openness predicate. The brick below is the piece step 6 of IDX-R2 needs:
at fuel `0`, a `HasTy` of the term already forces the `HasTy.const` fuel
premise of every constant reachable on its app-spine, so a typing of `x`
discharges `idxSrcLevelsOpen fam pf x` unconditionally. The binder case
is `true` by definition (`idxSrcLevelsOpen` does not walk under binders),
so no recursion under `pi` / `lam` / `letE` is needed. -/
theorem levelsOpen_of_hwf_zero {ls : List Level}
    (hwf : ∀ l ∈ ls, ∃ k, eval (fun _ => none) l = none ∨ k < 0) :
    levelsOpen ls = true := by
  induction ls with
  | nil => rfl
  | cons a t iht =>
      simp only [levelsOpen, Bool.and_eq_true]
      refine ⟨?_, iht (fun l hl => hwf l (List.mem_cons_of_mem a hl))⟩
      rcases hwf a (List.mem_cons_self a t) with ⟨k, hk⟩
      cases hk with
      | inl he => simp only [levelOpen, he]
      | inr hk => exact absurd hk (Nat.not_lt_zero k)

theorem idxSrcLevelsOpen_const {fam r : Nat} {pf : List (Expr Nat)}
    {ls : List Level} (h : levelsOpen ls = true) :
    idxSrcLevelsOpen fam pf (.const r ls) = true := by
  simp only [idxSrcLevelsOpen]
  split
  · rfl
  · split
    · rfl
    · exact h

theorem idxSrcLevelsOpen_of_hasTy_zero {E : ResolvedEnv} :
    {Γ : LCtx} → {x X : Expr Nat} → (h : HasTy E 0 Γ x X) → (fam : Nat) →
    (pf : List (Expr Nat)) → idxSrcLevelsOpen fam pf x = true
  | _, _, _, .sort _ _, _, _ => rfl
  | _, _, _, .bvar _ _ _ _, _, _ => rfl
  | _, _, _, .const _ r ls m hm hlen hwf, _, _ =>
      idxSrcLevelsOpen_const (levelsOpen_of_hwf_zero hwf)
  | _, _, _, .pi _ _ _ _ _ _ _, _, _ => rfl
  | _, _, _, .lam _ _ _ _ _ _ _, _, _ => rfl
  | _, _, _, .app _ f a A B hf ha, fam, pf => by
      show (idxSrcLevelsOpen fam pf f && idxSrcLevelsOpen fam pf a) = true
      rw [idxSrcLevelsOpen_of_hasTy_zero hf fam pf,
        idxSrcLevelsOpen_of_hasTy_zero ha fam pf, Bool.and_self]
  | _, _, _, .letE _ _ _ _ _ _ _ _, _, _ => rfl
  | _, _, _, .lit _ _ _ _, _, _ => rfl
  | _, _, _, .conv _ _ _ _ h _, fam, pf =>
      idxSrcLevelsOpen_of_hasTy_zero h fam pf

#print axioms levelsOpen_of_hwf_zero
#print axioms idxSrcLevelsOpen_const
#print axioms idxSrcLevelsOpen_of_hasTy_zero

/-! ## Clean DT theorems (directly from constructors/templates) -/

theorem DT009_conversion_preserves {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B : Expr Nat} (h : HasTy E n Γ e A) (hc : Conv E n Γ A B) :
    Nonempty (HasTy E n Γ e B) := ⟨.conv _ _ _ _ h hc⟩

mutual

def stepExt {E E' : ResolvedEnv} {n : Nat}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    {Γ : LCtx} → {a b : Expr Nat}→ Step E n Γ a b → Step E' n Γ a b
  | _, _, _, .beta _ _ _ _ => .beta _ _ _ _
  | _, _, _, .zeta _ _ _ _ => .zeta _ _ _ _
  | _, _, _, .zetaLocal _ _ _ h => .zetaLocal _ _ _ h
  | _, _, _, .delta _ r ls m b hres hbody htr =>
      .delta _ r ls m b (hext r m hres) hbody htr
  | _, _, _, .iota _ _ _ h => .iota _ _ _ (derivedIotaExt hext h)
  | _, _, _, .lit _ t exp h => .lit _ _ _ h

def convExt {E E' : ResolvedEnv} {n : Nat}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    {Γ : LCtx}→ {a b : Expr Nat}→ Conv E n Γ a b → Conv E' n Γ a b
  | _, _, _, .refl _ _ => .refl _ _
  | _, _, _, .symm _ _ _ h => .symm _ _ _ (convExt hext h)
  | _, _, _, .trans _ _ _ _ h1 h2 => .trans _ _ _ _ (convExt hext h1) (convExt hext h2)
  | _, _, _, .step _ _ _ hs => .step _ _ _ (stepExt hext hs)
  | _, _, _, .app _ _ _ _ _ h1 h2 => .app _ _ _ _ _ (convExt hext h1) (convExt hext h2)
  | _, _, _, .lam _ _ _ _ _ hA hb => .lam _ _ _ _ _ (convExt hext hA) (convExt hext hb)
  | _, _, _, .pi _ _ _ _ _ hA hb => .pi _ _ _ _ _ (convExt hext hA) (convExt hext hb)
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb =>
      .letE _ _ _ _ _ _ _ (convExt hext hA) (convExt hext hv) (convExt hext hb)
  | _, _, _, .sorts Γ l1 l2 h => .sorts Γ l1 l2 h
  | _, _, _, .consts Γ r ls ls' h => .consts Γ r ls ls' h
  | _, _, _, .eta Γ f A B hh => .eta Γ f A B (hasTyExt hext hh)
  | _, _, _, .irr _ _ _ _ hP hp hq =>
      .irr _ _ _ _ (hasTyExt hext hP) (hasTyExt hext hp) (hasTyExt hext hq)

def hasTyExt {E E' : ResolvedEnv} {n : Nat}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    {Γ : LCtx}→ {e A : Expr Nat}→ HasTy E n Γ e A → HasTy E' n Γ e A
  | _, _, _, .sort _ _ => .sort _ _
  | _, _, _, .bvar _ _ _ h => .bvar _ _ _ h
  | _, _, _, .const _ r ls m hres hlen hwf => .const _ r ls m (hext r m hres) hlen hwf
  | _, _, _, .pi _ _ _ _ _ hA hB => .pi _ _ _ _ _ (hasTyExt hext hA) (hasTyExt hext hB)
  | _, _, _, .lam _ _ _ _ _ hA hb => .lam _ _ _ _ _ (hasTyExt hext hA) (hasTyExt hext hb)
  | _, _, _, .app _ _ _ _ _ hf ha => .app _ _ _ _ _ (hasTyExt hext hf) (hasTyExt hext ha)
  | _, _, _, .letE _ _ _ _ _ hA hv hb =>
      .letE _ _ _ _ _ (hasTyExt hext hA) (hasTyExt hext hv) (hasTyExt hext hb)
  | _, _, _, .conv _ _ _ _ h hc => .conv _ _ _ _ (hasTyExt hext h) (convExt hext hc)
  | _, _, _, .lit _ _ _ hexp => .lit _ _ _ (hasTyExt hext hexp)

end

theorem DT013_environment_weakening {E E' : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A : Expr Nat} (h : HasTy E n Γ e A)
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    Nonempty (HasTy E' n Γ e A) := ⟨hasTyExt hext h⟩

/-- M-003 (00 §20.6 RULE CHANGES). Conclusion moved
    old:  Nonempty (Conv E n Γ (.const r ls) b)
    new:  Nonempty (Conv E n Γ (.const r ls) (instantiateLevels ls b))
in lockstep with `Step.delta`'s conclusion index. The old form is the
`ls = []` instance (`instantiateLevels_nil`), which under `EnvWf` is the
only reachable one (`envWf_body_arity_zero`). Not a weakening: the
theorem is exactly 02 §9 as written. -/
theorem DT014_transparent_delta_soundness {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) :
    Nonempty (Conv E n Γ (.const r ls) (instantiateLevels ls b)) :=
  ⟨.step _ _ _ (.delta _ r ls m b hres hbody htr)⟩

theorem DT016_proof_irrelevance_soundness {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {P p q : Expr Nat} (hP : HasTy E n Γ P (.sort .zero))
    (hp : HasTy E n Γ p P) (hq : HasTy E n Γ q P) :
    Nonempty (Conv E n Γ p q) := ⟨.irr _ _ _ _ hP hp hq⟩

theorem DT004_lifting_preserves_typing {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {d : LocalDecl} {e A : Expr Nat}
    (hE : EnvWf E n)
    (h : HasTy E n Γ e A) :
    Nonempty (HasTy E n (insertAt d 0 Γ) (lift 0 1 e) (lift 0 1 A)) :=
  Nonempty.intro (hasTyWeaken d hE h)

theorem DT005_substitution_preserves_typing {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} (hE : EnvWf E n)
    {A B v e : Expr Nat}
    (hv : HasTy E n Γ v A)
    (he : HasTy E n (LocalDecl.assumption A :: Γ) e B) :
    Nonempty (HasTy E n Γ (instantiate0 v e) (instantiate0 v B)) := by
  have h := hasTySubst (j := 0) hE v A he
    (by simp) (by simp only [substRemove_zero_cons, lift_zero]; exact hv)
  simp only [substRemove_zero_cons, lift_zero, instantiate0] at h
  exact Nonempty.intro h

/-! ## DT-003: context regularity -/

-- `CtxWf` moved to `RcicInvertFamily` (00 §19.2 erratum 2): the
-- conversion-injectivity obligations `PiConvInj` / `SortConvChar` /
-- `FamAppConvInj` are conditioned on it, and they are stated there.
-- Constructors unchanged.

theorem DT003_context_regularity {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A : Expr Nat}
    (hΓ : CtxWf E n (LocalDecl.assumption A :: Γ)) :
    ∃ u, Nonempty (HasTy E n Γ A (.sort u)) := by
  cases hΓ with
  | assumption _ _ u _ hA' => exact ⟨u, Nonempty.intro hA'⟩

/-! ## DT-007: typing regularity (sort case) -/

theorem DT007_typing_regularity {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {l : Level} (h : HasTy E n Γ (.sort l) (.sort (.succ l))) :
    ∃ u, Nonempty (HasTy E n Γ (.sort (.succ l)) (.sort u)) :=
  ⟨.succ (.succ l), ⟨.sort _ _⟩⟩

/-! ## DT-008: convertibility is a typed equivalence -/

theorem DT008_convertibility_typed_equivalence {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (∀ a, Nonempty (Conv E n Γ a a))
    ∧ (∀ a b, Nonempty (Conv E n Γ a b) → Nonempty (Conv E n Γ b a))
    ∧ (∀ a b c, Nonempty (Conv E n Γ a b) → Nonempty (Conv E n Γ b c) → Nonempty (Conv E n Γ a c)) := by
  refine ⟨fun _ => ⟨.refl _ _⟩, ?_, ?_⟩
  · intro a b h
    exact h.elim (fun h' => ⟨.symm _ _ _ h'⟩)
  · intro a b c h1 h2
    exact h1.elim (fun h1' => h2.elim (fun h2' => ⟨.trans _ _ _ _ h1' h2'⟩))

/-! ## DT-015: rigidity (stepConstInv wrapper) -/

theorem DT015_rigidity {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember}
    (hres : E.members r = some m) (hrigid : transparent m.mclass = false)
    {e' : Expr Nat} (hstep : Step E n Γ (.const r ls) e') :
    Nonempty (DerivedIota E (.const r ls) e') := by
  cases stepConstInv hstep rfl with
  | inl delta =>
    -- 00 §20.6 / W4: the delta summand now binds the STORED body `b0`
    -- separately and says how `e'` is built from it. Rigidity reads only
    -- the transparency component, so the content is unchanged.
    let ⟨m', _b0, hres', hbody', htr', _hbeq⟩ := delta
    rw [hres] at hres'; cases hres'
    rw [hrigid] at htr'; exact absurd htr' (by simp)
  | inr hι => exact (derivedIota_const_false hι).elim

/-! ## Debt-carrying DT theorems (now with inversion family + obligations) -/

/-- DT-021: "no universe cumulativity" — one-line wrapper over
SortConvChar. Footprint (M-003, O-3 restatement): `SortConvChar` is
`EnvWf`+`CtxWf`-conditioned (00 §19.2 errata; the `EnvWf`-only form is
refuted in a junk LOCAL context), so this wrapper carries both. -/
theorem DT021_no_cumulativity {E : ResolvedEnv} {n : Nat}
    (hscc : SortConvChar E n) (hE : EnvWf E n) {Γ : LCtx}
    (hΓ : CtxWf E n Γ)
    {u v : Level} (hc : Conv E n Γ (.sort u) (.sort v)) :
    eqN u v := hscc hE Γ u v hΓ hc

/-- DT-023 (02 §14): "not every raw expression is typable" — existence
claim; witness is the mechanizer's free choice. Restated over the
already-proven `hasTyBvarEmptyFalse` (00 §18.1). -/
theorem DT023_not_everything_typable {E : ResolvedEnv} {n : Nat} :
    ¬ ∃ A, Nonempty (HasTy E n [] (.bvar 0) A) :=
  fun ⟨_, ⟨h⟩⟩ => hasTyBvarEmptyFalse h

/-! ## DT-006: let substitution (00 §18.2 D-1) -/

/-- One-line wrapper over `hasTySubstLet` at `j = 0`. The stored-value
identification: the construction substitutes the let's OWN value.
Footprint (M-003): the six transport premises of DT-005, because
`hasTySubstLet` consumes them. -/
theorem DT006_let_substitution_preserves {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} (hE : EnvWf E n)
    {A v B e : Expr Nat}
    (hv : HasTy E n Γ v A)
    (he : HasTy E n (LocalDecl.letBinding A v :: Γ) e B) :
    Nonempty (HasTy E n Γ (instantiate0 v e) (instantiate0 v B)) := by
  have hget : (LocalDecl.letBinding A v :: Γ)[(0:Nat)]? =
      some (.letBinding A v) := List.getElem?_cons_zero
  have hvty : HasTy E n (substRemove v 0 (LocalDecl.letBinding A v :: Γ))
      (lift 0 0 v) (lift 0 0 A) := by
    rw [substRemove_zero_cons, lift_zero, lift_zero]
    exact hv
  have h := hasTySubstLet (j := 0) hE A v he hget hvty
  rw [substRemove_zero_cons, lift_zero] at h
  exact Nonempty.intro h

/-! ## DT-010/011: subject reduction (00 §18.2 D-2, D-3) -/

inductive Steps (E : ResolvedEnv) (n : Nat) : LCtx → Expr Nat → Expr Nat → Type
  | refl (Γ : LCtx) (e : Expr Nat) : Steps E n Γ e e
  | step (Γ : LCtx) (a b c : Expr Nat) (h1 : Step E n Γ a b) (h2 : Steps E n Γ b c) :
      Steps E n Γ a c

/-- CtxWf lookup: a stored let-value is typed at its stored type, in the
context that contains it. Induction on CtxWf; transport with `hasTyWeaken`
at cutoff 0 and `lift_lift_merge` (the hvty-transport template).
Footprint: EnvClosed / IotaLift / LitLift. -/
noncomputable def ctxWfLookupValue {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) :
    {Γ : LCtx} → CtxWf E n Γ → {i : Nat} → {v : Expr Nat} →
    lookupValue Γ i = some v →
    Σ' (A : Expr Nat), (lookupType Γ i = some A) ×' HasTy E n Γ v A := by
  intro Γ hΓ i v hvl
  induction hΓ generalizing i v with
  | nil =>
      simp only [lookupValue, List.get?_nil] at hvl
      exact Option.noConfusion hvl
  | assumption Γ A u hΓ hA ih =>
      cases i with
      | zero =>
          simp only [lookupValue, List.get?_cons_zero] at hvl
          exact Option.noConfusion hvl
      | succ i' =>
          rw [lookupValue_cons_succ (LocalDecl.assumption A) Γ i'] at hvl
          cases hopt : lookupValue Γ i' with
          | none =>
              rw [hopt, Option.map_none'] at hvl
              exact Option.noConfusion hvl
          | some v0 =>
              rw [hopt, Option.map_some'] at hvl
              injection hvl with hvEq
              have ⟨A0, hlk0, hv0⟩ := ih hopt
              refine ⟨lift 0 1 A0, ?_, ?_⟩
              · have hlt := lookupType_cons_succ (LocalDecl.assumption A) Γ i'
                rw [hlt, hlk0, Option.map_some']
              · subst hvEq
                exact hasTyWeaken (LocalDecl.assumption A) hE (c := 0) hv0
  | letBinding Γ A u w hΓ hA hv ih =>
      cases i with
      | zero =>
          have hvEq : v = lift 0 (0+1) w := by
            simp only [lookupValue, List.get?_cons_zero] at hvl
            injection hvl with hraw
            exact hraw.symm
          have hlk : lookupType (LocalDecl.letBinding A w :: Γ) 0 =
              some (lift 0 (0+1) A) := by
            simp only [lookupType, List.get?_cons_zero]
          subst hvEq
          exact ⟨lift 0 (0+1) A, hlk,
            hasTyWeaken (LocalDecl.letBinding A w) hE (c := 0) hv⟩
      | succ i' =>
          rw [lookupValue_cons_succ (LocalDecl.letBinding A w) Γ i'] at hvl
          cases hopt : lookupValue Γ i' with
          | none =>
              rw [hopt, Option.map_none'] at hvl
              exact Option.noConfusion hvl
          | some v0 =>
              rw [hopt, Option.map_some'] at hvl
              injection hvl with hvEq
              have ⟨A0, hlk0, hv0⟩ := ih hopt
              refine ⟨lift 0 1 A0, ?_, ?_⟩
              · have hlt := lookupType_cons_succ (LocalDecl.letBinding A w) Γ i'
                rw [hlt, hlk0, Option.map_some']
              · subst hvEq
                exact hasTyWeaken (LocalDecl.letBinding A w) hE (c := 0) hv0

/-- F-04: the RAW (monomorphic) body-typing recursion over `EnvWf` at
the admission n. []→Γ via hasTyClosedWeaken. LitLift discharged
(`litLift`). This is the whole content; `envWf_bodyTyped` below is the
`EnvBodyTyped` wrapper that collapses the level list. -/
def envWf_bodyTypedRaw {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) :
    ∀ (Γ : LCtx) (r : Nat) (m : CheckedMember) (b : Expr Nat),
      E.members r = some m → m.body = some b → HasTy E n Γ b m.mtype
  | Γ, r', m', b, hm, hb =>
    match hE with
    | .empty _ => by
        simp only [emptyEnv] at hm
        cases hm
    | .axiom E r A u hE hfresh hA hcl => by
        have hext := members_extend_preserved (m := ⟨.axiomM, 0, A, none⟩) hfresh
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          cases hb
        · simp only [extendEnv, if_neg hrr] at hm
          exact hasTyExt hext (envWf_bodyTypedRaw hE Γ r' m' b hm hb)
    | .definition E r A v u hE hfresh hA hv hclA hclv => by
        have hext :=
          members_extend_preserved (m := ⟨.definitionM, 0, A, some v⟩) hfresh
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          injection hb with hb'
          subst hb'
          exact hasTyExt hext (hasTyClosedWeaken hE hclv hclA Γ hv)
        · simp only [extendEnv, if_neg hrr] at hm
          exact hasTyExt hext (envWf_bodyTypedRaw hE Γ r' m' b hm hb)
    | .thm E r A p hE hfresh hA hp hclA hclp => by
        have hext :=
          members_extend_preserved (m := ⟨.theoremM, 0, A, some p⟩) hfresh
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          injection hb with hb'
          subst hb'
          exact hasTyExt hext (hasTyClosedWeaken hE hclp hclA Γ hp)
        · simp only [extendEnv, if_neg hrr] at hm
          exact hasTyExt hext (envWf_bodyTypedRaw hE Γ r' m' b hm hb)
    | .opaque E r A v u hE hfresh hA hv hclA hclv => by
        have hext :=
          members_extend_preserved (m := ⟨.opaqueM, 0, A, some v⟩) hfresh
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          injection hb with hb'
          subst hb'
          exact hasTyExt hext (hasTyClosedWeaken hE hclv hclA Γ hv)
        · simp only [extendEnv, if_neg hrr] at hm
          exact hasTyExt hext (envWf_bodyTypedRaw hE Γ r' m' b hm hb)
    | .indMember E r m hE hfresh hind hnobody hclT _harity
        _hlvlB _hcanon _harities _hidxAdm _hadm => by
        have hext := members_extend_preserved (m := m) hfresh
        by_cases hrr : r' = r
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          rw [hnobody] at hb
          cases hb
        · simp only [extendEnv, if_neg hrr] at hm
          exact hasTyExt hext (envWf_bodyTypedRaw hE Γ r' m' b hm hb)

/-- F-04 / 00 §20.6 MONOMORPHIC DELTA: the `EnvBodyTyped` inhabitant.

The obligation is stated at 02 §9's full generality (a level list plus
`HasTy.const`'s own `hlen`), but the discharge is monomorphic and
introduces NO level-substitution metatheorem: under `EnvWf` a member
that has a body has `arity = 0` (`envWf_body_arity_zero`, sealed in W3),
so `hlen` forces `ls = []` and `instantiateLevels_nil` reduces both
indices to the raw recursion `envWf_bodyTypedRaw`.

This is the tripwire §20.6 asked for: the day a polymorphic-definition
constructor is admitted, `hz` stops going through HERE — at one site —
and demands the real theorem, instead of a scattering of consumers
breaking while the obligation silently understates the rule. -/
def envWf_bodyTyped {E : ResolvedEnv} {n : Nat}
    (hE : EnvWf E n) : EnvBodyTyped E n := by
  intro Γ r m b ls hm hb hlen
  have hz : ls = [] := by
    have h0 := envWf_body_arity_zero hE r m b hm hb
    rw [h0] at hlen
    cases ls with
    | nil => rfl
    | cons _ xs =>
        exfalso
        simp only [List.length_cons] at hlen
        omega
  subst hz
  simp only [instantiateLevels_nil]
  exact envWf_bodyTypedRaw hE Γ r m b hm hb

/-- Type-valued one-step subject reduction (00 §18.2 D-2). Terminal
`∃`/`Nonempty` wrappers live on the theorem. Footprint (M-003):
`PiConvInj` (EnvWf+CtxWf-conditioned, O-3), `CtxWf`, `IotaPreserve`,
plus the six transport premises `hasTySubst`/`hasTySubstLet` consume
(EnvClosed/IotaLift/LitLift/EnvSubst/IotaSubst/LitSubst).
EnvBodyTyped discharged (O-2): delta uses `envWf_bodyTyped`.
`hpci` is applied at `hE`.

M-003 (00 §19.7 E-LitP DISCHARGE, O-2; segment 7a). Premise deleted:
    old:  … (hIotaP : IotaPreserve E n) (hLitP : LitPreserve E n)
    new:  … (hIotaP : IotaPreserve E n)
`LitPreserve` was discharged VACUOUSLY there (`HasTy` then had no `lit`
rule) and is discharged FOR REAL since DT-017 (00 §20.11): `HasTy.lit`
types a literal at the type of its `LiteralExpansion`, `hasTyLitInv`
reads that content off the derivation and `HasTy.conv` transports it —
the sealed `litPreserve` (`RcicInvertFamily.lean`). The `.lit` arm
obtains the fact from `litPreserve E n` instead of from a premise; the
conclusion is unchanged and one hypothesis is gone. TRIPWIRE FIRED and
took E-LitP's FIRST disjunct: `hLitP` is re-carried NOWHERE — not here,
not at DT-010, not at DT-011; the vacuous inhabitant and the refutation
it rested on are DELETED with their seal entries (00 §20.11 T3).

M-003 (00 §20.6 DISCHARGE, O-2). Premise deleted:
    old:  … (hs) (hlc : StepLevelCoherent hs) (hic : StepIndexCoherent hs)
    new:  … (hs) (hic : StepIndexCoherent hs)
`HasTy.const` is no longer level-inert (00 §20.6 rule change), so the
major's constructor universes ARE forced by the redex's own typing:
`iotaLhs_ctorParams_levels_conv` derives what `StepLevelCoherent` used
to assume.

M-003 (00 §19.2 ERRATUM 6 DISCHARGE, O-2). Second premise deleted:
    old:  … (hs) (hic : StepIndexCoherent hs)
    new:  … (hs)
`StepIndexCoherent` carried the per-redex agreement between the major's
index slots and the constructor's result indices as a SYNTACTIC
equation. No typing delivers that equation, so the premise was
unsatisfiable at every redex whose indices are convertible without
being syntactically equal, and this statement was VACUOUS exactly
there. Restated at the conversion layer (`IndexCoherentConv`,
`RcicInvertFamily`) it is DERIVED inside `iotaPreserve` by
`iotaLhs_ctorIdx_conv`, off the same `FamAppConvInj` application that
supplies the parameter and level halves. The `.iota` arm now hands
`ty` and `hΓ` to `IotaPreserve` and nothing else. Strengthening: the
conclusion is unchanged and one hypothesis is gone. -/
noncomputable def oneStepSR {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hIotaP : IotaPreserve E n)
    {Γ : LCtx} (hΓ : CtxWf E n Γ)
    {e A e' : Expr Nat} (h : HasTy E n Γ e A) (hs : Step E n Γ e e') :
    Σ' (B : Expr Nat), HasTy E n Γ e' B ×' Conv E n Γ A B :=
  match hs with
  | .beta _ Abody body arg => by
      let ⟨A_inv, B_inv, hf, ha, hcv⟩ := hasTyAppInv h rfl
      let ⟨_u, B_lam, _hAty, hbody, hcv_lam⟩ := hasTyLamInv hf rfl
      let ⟨hdom, hcod⟩ := hpci hE Γ Abody B_lam A_inv B_inv hΓ hcv_lam
      have ha' : HasTy E n Γ arg Abody :=
        .conv _ _ _ _ ha (.symm _ _ _ hdom)
      have hget : (LocalDecl.assumption Abody :: Γ)[(0:Nat)]? =
          some (.assumption Abody) := List.getElem?_cons_zero
      have hvty : HasTy E n (substRemove arg 0 (LocalDecl.assumption Abody :: Γ))
          (lift 0 0 arg) (lift 0 0 Abody) := by
        rw [substRemove_zero_cons, lift_zero, lift_zero]
        exact ha'
      have hty0 := hasTySubst (j := 0) hE
        arg Abody hbody hget hvty
      have hcod0 := convSubst (j := 0) hE
        arg Abody hcod hget hvty
      rw [substRemove_zero_cons, lift_zero] at hty0 hcod0
      exact ⟨instantiate0 arg B_lam, hty0,
        .symm _ _ _ (.trans _ _ _ _ hcod0 hcv)⟩
  | .zeta _ Alet value body => by
      let ⟨_u, B_let, _hAty, hv, hb, hcv⟩ := hasTyLetInv h rfl
      have hget : (LocalDecl.letBinding Alet value :: Γ)[(0:Nat)]? =
          some (.letBinding Alet value) := List.getElem?_cons_zero
      have hvty : HasTy E n (substRemove value 0 (LocalDecl.letBinding Alet value :: Γ))
          (lift 0 0 value) (lift 0 0 Alet) := by
        rw [substRemove_zero_cons, lift_zero, lift_zero]
        exact hv
      have hty0 := hasTySubstLet (j := 0) hE
        Alet value hb hget hvty
      have hcod0 := convSubstLet (j := 0) hE
        Alet value (a := B_let) (b := B_let)
        (.refl (LocalDecl.letBinding Alet value :: Γ) B_let) hget hvty
      rw [substRemove_zero_cons, lift_zero] at hty0 hcod0
      exact ⟨instantiate0 value B_let, hty0,
        .symm _ _ _ (.trans _ _ _ _ hcod0 hcv)⟩
  | .zetaLocal _ i v hvl => by
      let ⟨A_lk, hlk, hcv⟩ := hasTyBvarInv h rfl
      let ⟨A_v, hlk', hvty⟩ := ctxWfLookupValue hE hΓ hvl
      have hEq : some A_lk = some A_v := hlk.symm.trans hlk'
      injection hEq with hAeq
      subst hAeq
      exact ⟨A_lk, hvty, .symm _ _ _ hcv⟩
  | .delta _ r ls m b hres hbody _htr => by
      -- 00 §20.6: the reduct is `instantiateLevels ls b` and its type is
      -- `instantiateLevels ls m.mtype`; `hasTyConstInv`'s `hlen` (no
      -- longer discarded) is exactly `EnvBodyTyped`'s third premise.
      let ⟨m', hres', hlen, hcv⟩ := hasTyConstInv h rfl
      have hmeq : some m = some m' := hres.symm.trans hres'
      injection hmeq with hmeq'
      subst hmeq'
      have hty := envWf_bodyTyped hE Γ r m b ls hres hbody hlen
      exact ⟨A, .conv _ _ _ _ hty hcv, .refl _ _⟩
  | .iota _ _ _ (.of w) =>
      have ty : IotaTyping E w := envWf_iotaTyping hE w
      ⟨A, hIotaP Γ (iotaLhsOf w) (iotaRhsOf w) A (.of w) ty hΓ h,
        .refl _ _⟩
  | .lit _ t exp hlexp =>
      ⟨A, litPreserve E n Γ t exp A hlexp h, .refl _ _⟩

/-! ### 0-ary IotaPreserve alignment (05 §13 last-Π / 05 §12 minor).

Type-valued uniqueness on a const-headed application spine: DT-012's
const+app cases only (no sort, no SortConvChar). Footprint: `PiConvInj`
(EnvWf-conditioned, O-3) + `convSubst`. Inverted last-Π body converts
to the `instTel` η-shape; inverted minor type converts to `app F ctor`
given 05 §12 `hmin`. -/

def uniqueTy_const {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {A B : Expr Nat}
    (hA : HasTy E n Γ (.const r ls) A)
    (hB : HasTy E n Γ (.const r ls) B) :
    Conv E n Γ A B := by
  let ⟨m1, hres1, _, hc1⟩ := hasTyConstInv hA rfl
  let ⟨m2, hres2, _, hc2⟩ := hasTyConstInv hB rfl
  have hEq : some m1 = some m2 := hres1.symm.trans hres2
  injection hEq with hmeq
  subst hmeq
  exact .trans _ _ _ _ (.symm _ _ _ hc1) hc2

def uniqueTy_app_of {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    {f x : Expr Nat}
    (hfun : ∀ {A B : Expr Nat},
      HasTy E n Γ f A → HasTy E n Γ f B → Conv E n Γ A B)
    {A B : Expr Nat}
    (hA : HasTy E n Γ (.app f x) A)
    (hB : HasTy E n Γ (.app f x) B) :
    Conv E n Γ A B :=
  let ⟨A1, B1, hf1, ha1, hc1⟩ := hasTyAppInv hA rfl
  let ⟨A2, B2, hf2, _ha2, hc2⟩ := hasTyAppInv hB rfl
  have hπ := hfun hf1 hf2
  let ⟨_hdom, hcod⟩ := hpci hE Γ A1 B1 A2 B2 hΓ hπ
  have hget : (LocalDecl.assumption A1 :: Γ)[(0:Nat)]? =
      some (.assumption A1) := List.getElem?_cons_zero
  have hvty : HasTy E n (substRemove x 0 (LocalDecl.assumption A1 :: Γ))
      (lift 0 0 x) (lift 0 0 A1) := by
    rw [substRemove_zero_cons, lift_zero, lift_zero]
    exact ha1
  have hcod0 := convSubst (j := 0) hE x A1 hcod hget hvty
  by
    rw [substRemove_zero_cons, lift_zero] at hcod0
    exact .trans _ _ _ _ (.symm _ _ _ hc1) (.trans _ _ _ _ hcod0 hc2)

/-- Uniqueness at a constructor-level expansion. TWO CASES, no
    induction on `t`: `natExpand 0` is a bare constant and
    `natExpand (t+1)` an application whose HEAD is a bare constant,
    so `uniqueTy_const` closes the head at both. -/
def uniqueTy_natExpand {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n) (hE : EnvWf E n)
    {Γ : LCtx} (hΓ : CtxWf E n Γ) :
    (t : Nat) → {A B : Expr Nat} →
    HasTy E n Γ (natExpand t) A → HasTy E n Γ (natExpand t) B →
    Conv E n Γ A B
  | 0, _, _, hA, hB => uniqueTy_const hA hB
  | _ + 1, _, _, hA, hB =>
      uniqueTy_app_of hpci hE hΓ (fun h1 h2 => uniqueTy_const h1 h2) hA hB

def uniqueTy_foldApps {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    {f : Expr Nat}
    (hfun : ∀ {A B : Expr Nat},
      HasTy E n Γ f A → HasTy E n Γ f B → Conv E n Γ A B) :
    {xs : List (Expr Nat)} → {A B : Expr Nat} →
    HasTy E n Γ (foldApps f xs) A →
    HasTy E n Γ (foldApps f xs) B →
    Conv E n Γ A B
  | [], A, B, hA, hB => hfun hA hB
  | x :: xs, A, B, hA, hB =>
      uniqueTy_foldApps hpci hE hΓ
        (f := Expr.app f x)
        (hfun := fun hA' hB' =>
          uniqueTy_app_of hpci hE hΓ hfun hA' hB')
        (A := A) (B := B)
        (by simp only [foldApps] at hA; exact hA)
        (by simp only [foldApps] at hB; exact hB)

/-- M-003 (00 §20.6 RULE CHANGES + DISCHARGE). Statement change:
    old:  HasTy E n Γ (.const w.recRef w.ls) w.recMember.mtype
    new:  Σ' (_ : w.ls.length = w.recMember.arity),
            HasTy E n Γ (.const w.recRef w.ls)
              (instantiateLevels w.ls w.recMember.mtype)
The type index follows `HasTy.const`'s (the old form is no longer what
the rule produces), and `hasTyConstInv`'s `hlen` — previously discarded
— is returned rather than thrown away: it is the arity fact the §20.6
DISCHARGE needs to turn 05 §2/§3 admission data into
`w.famMember.arity ≤ w.ls.length`. Nothing is weakened; both components
are read off the same inversion. -/
def hasTy_rec_mtype {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {T : Expr Nat}
    (h : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (_ : w.ls.length = w.recMember.arity),
      HasTy E n Γ (.const w.recRef w.ls)
        (instantiateLevels w.ls w.recMember.mtype) := by
  have hl : iotaLhsOf w =
      foldApps (.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w]) := rfl
  rw [hl] at h
  cases hargs : w.preMajor ++ [ctorMajor w] with
  | nil =>
      have ⟨_, h2⟩ := List.append_eq_nil.mp hargs
      cases h2
  | cons y ys =>
      rw [hargs] at h
      have sp := invertSpine (f := Expr.const w.recRef w.ls) (xs := y :: ys) h
      cases sp with
      | cons hf _ha _s =>
          let ⟨m, hres, hlen, hcv⟩ := hasTyConstInv hf rfl
          have hmeq : some m = some w.recMember := hres.symm.trans w.hrec
          injection hmeq with heq
          subst heq
          exact ⟨hlen, .conv _ _ _ _ hf (.symm _ _ _ hcv)⟩

def typedApplyTel {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    {f T : Expr Nat}
    (hfT : HasTy E n Γ f T)
    (hfun : ∀ {A B : Expr Nat},
      HasTy E n Γ f A → HasTy E n Γ f B → Conv E n Γ A B) :
    {args : List (Expr Nat)} → {U R : Expr Nat} →
    applyTel args T = some U →
    SpineInv E n Γ f args R →
    HasTy E n Γ (foldApps f args) U
  | [], U, _R, happ, _sp => by
      simp only [applyTel] at happ
      injection happ with hU
      subst hU
      simp only [foldApps]
      exact hfT
  | x :: xs, U, _R, happ, sp =>
      let ⟨A_T, B_T, hTeq, happ'⟩ := applyTel_cons_inv x xs happ
      by
        subst hTeq
        cases sp with
        | cons hf ha s =>
            have hπ := hfun hfT hf
            let ⟨hdom, _hcod⟩ := hpci hE Γ A_T B_T _ _ hΓ hπ
            have haT : HasTy E n Γ x A_T :=
              .conv _ _ _ _ ha (.symm _ _ _ hdom)
            have hfapp : HasTy E n Γ (.app f x) (instantiate0 x B_T) :=
              .app _ _ _ _ _ hfT haT
            have ih := typedApplyTel hpci hE hΓ hfapp
              (fun hA' hB' =>
                uniqueTy_app_of hpci hE hΓ hfun hA' hB')
              happ' s
            simp only [foldApps]
            exact ih

/-- `foldApps` congruence over a pointwise `Conv` list. Iterated
`Conv.app`; nothing is introduced at the congruence layer.

MOVED UP (00 §19.2 erratum 6): it now serves `iotaPreserve_nil` as
well, which sits above the §20.5 bridge section where it used to
live. Its only dependencies are `ConvArgs` and `Conv.app`. -/
def convArgs_foldApps {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {xs ys : List (Expr Nat)} → ConvArgs E n Γ xs ys →
    {f g : Expr Nat} → Conv E n Γ f g →
    Conv E n Γ (foldApps f xs) (foldApps g ys)
  | [], [], .nil, _f, _g, hf => hf
  | _ :: _, _ :: _, .cons hx hs, _f, _g, hf =>
      convArgs_foldApps hs (.app _ _ _ _ _ hf hx)

/-- 0-ary IotaPreserve from the 05 §12 witness fields plus the per-redex
index CONVERSION. 00 §19.2 erratum 5: `IotaTyping.hminApply` is deleted;
its content at `fields = []` is `hminTel` (the minor domain IS
`iotaMdom`, whose 0-ary conclusion reads the result indices off
`ctorAfterParams`) together with the relation between those result
indices and the major's index slots — a fact about the redex, not about
the witness, since no `IotaWitness` field constrains
`preMajor.drop (nparams + 1 + nMinors)`.

M-003 (00 §19.2 ERRATUM 6, O-2). Premise restated:
    old:  (hic : IndexCoherent w)
    new:  {U} (hU : applyTel w.fields w.ctorAfterParams = some U)
          (hidxC : ConvArgs E n Γ (familyIdx w.nparams U)
                     (w.preMajor.drop (w.nparams + 1 + w.nMinors)))
The syntactic equation is strictly stronger than anything the redex's
typing delivers (`IndexCoherentConv`, `RcicInvertFamily`). At the
conversion layer the minor domain lands at the TELESCOPE's own result
indices `familyIdx w.nparams U`, and the retype to the major's index
slots happens ONCE, in the closing `HasTy.conv`, through
`convArgs_foldApps` under the `Conv.app` congruence that already moved
the argument (`ctorMajorRec ⇝ ctorMajor`). This lemma sits UPSTREAM of
the discharge `iotaLhs_ctorIdx_conv`, so it takes the conversion rather
than deriving it; its join points supply it from `hfaci`. -/
def iotaPreserve_nil {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hmajconv : Conv E n Γ (ctorMajorRec w) (ctorMajor w))
    {U : Expr Nat}
    (hU : applyTel w.fields w.ctorAfterParams = some U)
    (hidxC : ConvArgs E n Γ (familyIdx w.nparams U)
      (w.preMajor.drop (w.nparams + 1 + w.nMinors)))
    (hflds : w.fields = [])
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    HasTy E n Γ (iotaRhsOf w) T := by
  have hk : w.kinds = [] := by
    have hlen := w.hlen
    rw [hflds] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  have hUeq : U = w.ctorAfterParams := by
    have h : applyTel w.fields w.ctorAfterParams = some w.ctorAfterParams := by
      rw [hflds]
      exact applyTel_nil _
    exact Option.some.inj (hU.symm.trans h)
  rw [hUeq] at hidxC
  have hmdom : ty.mdom =
      .app (foldApps ty.motive
        (familyIdx w.nparams w.ctorAfterParams))
        (ctorMajorRec w) := by
    rw [ty.hminTel]
    simp only [iotaMdom, hk, minorTel, ctorMajorRec, hflds,
      List.append_nil]
  have hmin : applyTel (w.preMajor.take (w.nparams + 1 + w.ctorIdx))
      (instantiateLevels w.ls w.recMember.mtype) =
      some (Expr.pi ty.mdom ty.restMin) := ty.hminDom
  rw [hmdom] at hmin
  have ⟨A, B, _Mty, _Fpack, A_syn, hpre, hctor, hcv, _hminor, happ, _hηpack⟩ :=
    iotaPreserve_nil_pack w hT
  let Fη : Expr Nat :=
    foldApps ty.motive (w.preMajor.drop (w.nparams + 1 + w.nMinors))
  let FηC : Expr Nat :=
    foldApps ty.motive (familyIdx w.nparams w.ctorAfterParams)
  have hFconv : Conv E n Γ FηC Fη :=
    convArgs_foldApps hidxC (.refl _ ty.motive)
  have hη : instTel w.preMajor w.recBody =
      .app (lift 0 1 Fη) (.bvar 0) := instTel_hrecBody w ty.hmotive
  have hfT := (hasTy_rec_mtype w hT).2
  have spPre :=
    invertSpine (f := Expr.const w.recRef w.ls) (xs := w.preMajor) hpre
  have hpre_syn :
      HasTy E n Γ (foldApps (.const w.recRef w.ls) w.preMajor)
        (.pi A_syn (instTel w.preMajor w.recBody)) :=
    typedApplyTel hpci hE hΓ hfT uniqueTy_const happ spPre
  have hπ :=
    uniqueTy_foldApps hpci hE hΓ uniqueTy_const hpre hpre_syn
  let ⟨_hdom, hcod⟩ :=
    hpci hE Γ A B A_syn (instTel w.preMajor w.recBody) hΓ hπ
  have hget : (LocalDecl.assumption A :: Γ)[(0:Nat)]? =
      some (.assumption A) := List.getElem?_cons_zero
  have hvty : HasTy E n (substRemove (ctorMajor w) 0
      (LocalDecl.assumption A :: Γ))
      (lift 0 0 (ctorMajor w)) (lift 0 0 A) := by
    rw [substRemove_zero_cons, lift_zero, lift_zero]
    exact hctor
  have hinst := convSubst (j := 0) hE
    (ctorMajor w) A hcod hget hvty
  rw [substRemove_zero_cons, lift_zero] at hinst
  have hη' : instantiate0 (ctorMajor w) (instTel w.preMajor w.recBody) =
      .app Fη (ctorMajor w) := by
    rw [hη, instantiate0_eta]
  have hinst' : Conv E n Γ (instantiate0 (ctorMajor w) B)
      (.app Fη (ctorMajor w)) := by
    rw [← hη']
    exact hinst
  have hlen := w.hpre
  have hidx := w.hidx
  have kdef : w.nparams + 1 + w.ctorIdx < w.preMajor.length := by omega
  have hx : (w.preMajor ++ [ctorMajor w])[w.nparams + 1 + w.ctorIdx]? =
      some w.minor := by
    have happ := List.getElem?_append_left (l₂ := [ctorMajor w]) kdef
    exact happ.trans w.hminor
  have htk : (w.preMajor ++ [ctorMajor w]).take
      (w.nparams + 1 + w.ctorIdx) = w.preMajor.take
        (w.nparams + 1 + w.ctorIdx) :=
    List.take_append_of_le_length (Nat.le_of_lt kdef)
  have hcons := drop_eq_cons_of_get hx
  have hsplit := List.take_append_drop (w.nparams + 1 + w.ctorIdx)
    (w.preMajor ++ [ctorMajor w])
  have hl : iotaLhsOf w =
      foldApps (.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w]) := rfl
  have hT' : HasTy E n Γ
      (foldApps (.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w])) T := by
    rw [← hl]; exact hT
  have hfold : foldApps (.const w.recRef w.ls)
      (w.preMajor ++ [ctorMajor w]) =
      foldApps
        (.app (foldApps (.const w.recRef w.ls)
          (w.preMajor.take (w.nparams + 1 + w.ctorIdx))) w.minor)
        ((w.preMajor ++ [ctorMajor w]).drop
          (w.nparams + 1 + w.ctorIdx + 1)) := by
    conv =>
      lhs
      rw [← hsplit, foldApps_append, htk, hcons, foldApps]
  have hTapp : HasTy E n Γ
      (foldApps
        (.app (foldApps (.const w.recRef w.ls)
          (w.preMajor.take (w.nparams + 1 + w.ctorIdx))) w.minor)
        ((w.preMajor ++ [ctorMajor w]).drop
          (w.nparams + 1 + w.ctorIdx + 1))) T := by
    rw [← hfold]; exact hT'
  have ⟨_, hfapp⟩ :=
    hasTyFoldAppsInv
      (f := Expr.app (foldApps (.const w.recRef w.ls)
        (w.preMajor.take (w.nparams + 1 + w.ctorIdx))) w.minor)
      (xs := (w.preMajor ++ [ctorMajor w]).drop
        (w.nparams + 1 + w.ctorIdx + 1)) hTapp
  have ⟨Mty', Bapp, hpreK, hminor', _⟩ := hasTyAppInv hfapp rfl
  have spK := invertSpine
    (f := Expr.const w.recRef w.ls)
    (xs := w.preMajor.take (w.nparams + 1 + w.ctorIdx)) hpreK
  have hmin_ty :
      HasTy E n Γ
        (foldApps (.const w.recRef w.ls)
          (w.preMajor.take (w.nparams + 1 + w.ctorIdx)))
        (.pi (.app FηC (ctorMajorRec w)) ty.restMin) := by
    have hmin' : applyTel
        (w.preMajor.take (w.nparams + 1 + w.ctorIdx))
        (instantiateLevels w.ls w.recMember.mtype) =
        some (.pi (.app FηC (ctorMajorRec w)) ty.restMin) := hmin
    exact typedApplyTel hpci hE hΓ hfT uniqueTy_const hmin' spK
  have hπm : Conv E n Γ (.pi Mty' Bapp)
      (.pi (.app FηC (ctorMajorRec w)) ty.restMin) :=
    uniqueTy_foldApps (f := Expr.const w.recRef w.ls)
      (xs := w.preMajor.take (w.nparams + 1 + w.ctorIdx))
      hpci hE hΓ uniqueTy_const hpreK hmin_ty
  let ⟨hdomM, _hcodM⟩ :=
    hpci hE Γ Mty' Bapp (.app FηC (ctorMajorRec w)) ty.restMin hΓ hπm
  rw [iotaRhs_nil_fields w hflds]
  exact .conv _ _ _ _ hminor'
    (.trans _ _ _ _ hdomM
      (.trans _ _ _ _ (.app _ _ _ _ _ hFconv hmajconv)
        (.trans _ _ _ _ (.symm _ _ _ hinst') hcv)))

/-- Arguments inhabiting a Π-telescope (introduction form of `applyTel`). -/
inductive TelArgs (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    List (Expr Nat) → Expr Nat → Expr Nat → Type
  | nil {T : Expr Nat} : TelArgs E n Γ [] T T
  | cons {x : Expr Nat} {xs : List (Expr Nat)} {A B U : Expr Nat}
      (hx : HasTy E n Γ x A)
      (ht : TelArgs E n Γ xs (instantiate0 x B) U) :
      TelArgs E n Γ (x :: xs) (.pi A B) U

def hasTy_fold_telArgs {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f T : Expr Nat} (hf : HasTy E n Γ f T) :
    {args : List (Expr Nat)} → {U : Expr Nat} →
    TelArgs E n Γ args T U →
    HasTy E n Γ (foldApps f args) U
  | [], _, .nil => hf
  | _ :: _, _, .cons hx ht =>
      hasTy_fold_telArgs (.app _ _ _ _ _ hf hx) ht

def telArgs_cons_inv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {x : Expr Nat} {xs : List (Expr Nat)} {T U : Expr Nat}
    (h : TelArgs E n Γ (x :: xs) T U) :
    Σ' (A B : Expr Nat),
      (T = .pi A B) ×' HasTy E n Γ x A ×'
      TelArgs E n Γ xs (instantiate0 x B) U := by
  cases h with
  | cons hx ht => exact ⟨_, _, rfl, hx, ht⟩

def telArgs_append {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {xs ys : List (Expr Nat)} → {T U V : Expr Nat} →
    TelArgs E n Γ xs T U → TelArgs E n Γ ys U V →
    TelArgs E n Γ (xs ++ ys) T V
  | [], ys, T, U, V, h1, h2 => by
      cases h1
      simp only [List.nil_append]
      exact h2
  | x :: xs, ys, T, U, V, h1, h2 => by
      have ⟨A, B, hT, hx, ht⟩ := telArgs_cons_inv h1
      subst hT
      simp only [List.cons_append]
      exact TelArgs.cons hx (telArgs_append ht h2)

/-- Syntactic type of the `i`-th argument of a TelArgs spine. -/
def telArgs_nth {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {xs : List (Expr Nat)} → {T U : Expr Nat} →
    TelArgs E n Γ xs T U →
    {i : Nat} → {x : Expr Nat} →
    xs[i]? = some x →
    Σ' (A : Expr Nat), HasTy E n Γ x A
  | [], _, _, .nil, i, x, hx => by
      simp only [List.getElem?_nil] at hx
      exact Option.noConfusion hx
  | y :: ys, T, U, h, i, x, hx =>
      match i with
      | 0 => by
          have ⟨A, B, hT, hy, _⟩ := telArgs_cons_inv h
          have hyx : y = x := by
            simp only [List.getElem?_cons_zero] at hx
            injection hx
          subst hyx
          exact ⟨A, hy⟩
      | i' + 1 => by
          have ⟨A, B, hT, _, ht⟩ := telArgs_cons_inv h
          exact telArgs_nth ht (i := i') (x := x) (by
            simp only [List.getElem?_cons_succ] at hx
            exact hx)

/-- Lookup the `i`-th TelArgs inhabitant at the syntactic `applyTel`
domain (not the inverted type). `telArgs_nth.fst` is not
definitionally that domain. -/
def telArgs_lookup {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {xs : List (Expr Nat)} → {T U : Expr Nat} →
    TelArgs E n Γ xs T U →
    {i : Nat} → {x : Expr Nat} →
    xs[i]? = some x →
    {A B : Expr Nat} →
    applyTel (xs.take i) T = some (Expr.pi A B) →
    HasTy E n Γ x A
  | [], _, _, .nil, i, x, hi, A, B, happ => by
      simp only [List.getElem?_nil] at hi
      exact Option.noConfusion hi
  | y :: ys, T, U, h, 0, x, hi, A, B, happ => by
      have ⟨A0, B0, hT, hy, _⟩ := telArgs_cons_inv h
      subst hT
      simp only [List.take_zero, applyTel] at happ
      injection happ with hπ
      injection hπ with hA _
      subst hA
      have hyx : y = x := by
        simp only [List.getElem?_cons_zero] at hi
        injection hi
      subst hyx
      exact hy
  | y :: ys, T, U, h, i' + 1, x, hi, A, B, happ => by
      have ⟨A0, B0, hT, _, ht⟩ := telArgs_cons_inv h
      subst hT
      exact telArgs_lookup ht
        (i := i') (x := x)
        (by simp only [List.getElem?_cons_succ] at hi; exact hi)
        happ

theorem telArgs_applyTel {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {args : List (Expr Nat)} → {T U : Expr Nat} →
    TelArgs E n Γ args T U → applyTel args T = some U
  | [], T, U, h => by
      cases h
      rfl
  | x :: xs, T, U, h => by
      have ⟨A, B, hT, _, ht⟩ := telArgs_cons_inv h
      subst hT
      simp only [applyTel]
      exact telArgs_applyTel ht


/-! ### 00 §20.5 bridges: free ctor-side fields enter through typing.

`ctorParams` / `lsC` are FREE witness fields (00 §20.1). The redex's
own typing is the only thing that relates them to the recursor-side
copies `preMajor.take nparams` / `ls`, and that relation is a POINTWISE
`Conv`, never a syntactic equation (00 §20.5, refuted under every other
carrier). These five lemmas are the machinery that consumes it. -/

/-- A `Conv` on the SUBSTITUTED VALUE transports through `instantiate0`.
Both ends are `Step.zeta` on the same `letE`, so no typing premise is
needed (the zeta step is untyped). -/
def conv_instantiate0_value {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v v' B : Expr Nat} (hv : Conv E n Γ v v') :
    Conv E n Γ (instantiate0 v B) (instantiate0 v' B) :=
  .trans _ _ _ _
    (.symm _ _ _ (.step _ _ _ (.zeta Γ (.sort .zero) v B)))
    (.trans _ _ _ _
      (.letE _ _ _ _ _ _ _ (.refl _ _) hv (.refl _ _))
      (.step _ _ _ (.zeta Γ (.sort .zero) v' B)))

/-- Split a pointwise `Conv` list at a prefix of known length. -/
def convArgs_append_split {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {xs xs' ys ys' : List (Expr Nat)} →
    ConvArgs E n Γ (xs ++ ys) (xs' ++ ys') →
    xs.length = xs'.length →
    ConvArgs E n Γ xs xs' ×' ConvArgs E n Γ ys ys'
  | [], [], _, _, h, _ => ⟨.nil, h⟩
  | [], _ :: _, _, _, _, hlen => by
      simp only [List.length_nil, List.length_cons] at hlen
      cases hlen
  | _ :: _, [], _, _, _, hlen => by
      simp only [List.length_nil, List.length_cons] at hlen
      cases hlen
  | x :: xs, x' :: xs', ys, ys', h, hlen => by
      cases h with
      | cons hx hs =>
          have hlen' : xs.length = xs'.length := Nat.succ.inj hlen
          have ⟨h1, h2⟩ := convArgs_append_split hs hlen'
          exact ⟨.cons hx h1, h2⟩

/-- Pointwise-convertible argument lists applied to convertible
telescopes give convertible results. `TelArgs` supplies the typing of
each left-hand argument that `convSubst` consumes; the value-side step
is `conv_instantiate0_value`. -/
def convArgs_applyTel {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n) (hE : EnvWf E n) (hΓ : CtxWf E n Γ) :
    {xs ys : List (Expr Nat)} → ConvArgs E n Γ xs ys →
    {T U T' U' : Expr Nat} →
    TelArgs E n Γ xs T U →
    Conv E n Γ T T' →
    applyTel ys T' = some U' →
    Conv E n Γ U U'
  | [], [], .nil, _T, _U, _T', _U', ht, hc, happ => by
      cases ht
      simp only [applyTel] at happ
      injection happ with hU
      subst hU
      exact hc
  | x :: _xs, y :: ys, .cons hx hs, _T, _U, _T', _U', ht, hc, happ => by
      have ⟨A, B, hT, hxA, ht'⟩ := telArgs_cons_inv ht
      subst hT
      have ⟨A', B', hT', happ'⟩ := applyTel_cons_inv y ys happ
      subst hT'
      have ⟨_hdom, hcod⟩ := hpci hE Γ A B A' B' hΓ hc
      have hget : (LocalDecl.assumption A :: Γ)[(0:Nat)]? =
          some (.assumption A) := List.getElem?_cons_zero
      have hvty : HasTy E n (substRemove x 0 (LocalDecl.assumption A :: Γ))
          (lift 0 0 x) (lift 0 0 A) := by
        rw [substRemove_zero_cons, lift_zero, lift_zero]
        exact hxA
      have hcod0 := convSubst (j := 0) hE x A hcod hget hvty
      rw [substRemove_zero_cons, lift_zero] at hcod0
      exact convArgs_applyTel hpci hE hΓ hs ht'
        (.trans _ _ _ _ hcod0 (conv_instantiate0_value hx)) happ'

/-- Retype a `TelArgs` along a `Conv` on its TELESCOPE. The SUBJECTS
are unchanged: each argument is retyped by `HasTy.conv` at the
convertible domain. (Retyping subjects along a `Conv` on subjects
would be unsound and is never done here.) -/
def telArgs_conv_dom {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n) (hE : EnvWf E n) (hΓ : CtxWf E n Γ) :
    {xs : List (Expr Nat)} → {T U T' U' : Expr Nat} →
    TelArgs E n Γ xs T U →
    Conv E n Γ T T' →
    applyTel xs T' = some U' →
    TelArgs E n Γ xs T' U'
  | [], _T, _U, _T', _U', ht, _hc, happ => by
      cases ht
      simp only [applyTel] at happ
      injection happ with hU
      subst hU
      exact TelArgs.nil
  | x :: xs, _T, _U, _T', _U', ht, hc, happ => by
      have ⟨A, B, hT, hxA, ht'⟩ := telArgs_cons_inv ht
      subst hT
      have ⟨A', B', hT', happ'⟩ := applyTel_cons_inv x xs happ
      subst hT'
      have ⟨hdom, hcod⟩ := hpci hE Γ A B A' B' hΓ hc
      have hget : (LocalDecl.assumption A :: Γ)[(0:Nat)]? =
          some (.assumption A) := List.getElem?_cons_zero
      have hvty : HasTy E n (substRemove x 0 (LocalDecl.assumption A :: Γ))
          (lift 0 0 x) (lift 0 0 A) := by
        rw [substRemove_zero_cons, lift_zero, lift_zero]
        exact hxA
      have hcod0 := convSubst (j := 0) hE x A hcod hget hvty
      rw [substRemove_zero_cons, lift_zero] at hcod0
      exact TelArgs.cons (.conv _ _ _ _ hxA hdom)
        (telArgs_conv_dom hpci hE hΓ ht' hcod0 happ')

/-- 00 §20.5 `hparamAlign` consumer: the recursor's and the
constructor's parameter Π-domains are SYNTACTICALLY equal at every
position when both stored types are applied to the same parameter
prefix, so recursor-side parameters typed at the recursor telescope
are read at the constructor telescope by rewrite (no conversion). -/
def telArgs_paramAlign_go {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (recType ctorType : Expr Nat) :
    (pre ps : List (Expr Nat)) → {Ur Uc Vr Vc : Expr Nat} →
    applyTel pre recType = some Ur →
    applyTel pre ctorType = some Uc →
    TelArgs E n Γ ps Ur Vr →
    recCtorParamAlignGo recType ctorType pre ps = true →
    applyTel ps Uc = some Vc →
    TelArgs E n Γ ps Uc Vc
  | _pre, [], _Ur, _Uc, _Vr, _Vc, _hr, _hc, ht, _halign, happ => by
      cases ht
      simp only [applyTel] at happ
      injection happ with hV
      subst hV
      exact TelArgs.nil
  | pre, x :: xs, _Ur, _Uc, _Vr, _Vc, hr, hc, ht, halign, happ => by
      have ⟨A, B, hUr, hxA, ht'⟩ := telArgs_cons_inv ht
      subst hUr
      have ⟨Ac, Bc, hUc, happ'⟩ := applyTel_cons_inv x xs happ
      subst hUc
      simp only [recCtorParamAlignGo, hr, hc] at halign
      have ⟨heq, hrest⟩ := bool_and_true halign
      have hAcA : Ac = A := of_decide_eq_true heq
      subst hAcA
      exact TelArgs.cons hxA
        (telArgs_paramAlign_go recType ctorType (pre ++ [x]) xs
          (applyTel_snoc x pre recType hr)
          (applyTel_snoc x pre ctorType hc) ht' hrest happ')

/-- n-ary IotaPreserve given TelArgs of `rhsArgs` at the 05 §12
minor domain, ending at `F ctor`. Last-Π alignment is the 0-ary
path; the remaining work is constructing `TelArgs` from the ctor
spine (plain fields) plus recursor-prefix applications (IHs).

M-003 (00 §19.2 ERRATUM 6, O-3 RIDER). Premise added and `ht`'s
ENDPOINT restated:
    old:  (ht : TelArgs … (.app (foldApps ty.motive
            (w.preMajor.drop (w.nparams + 1 + w.nMinors))) (ctorMajorRec w)))
    new:  {U} (hidxC : ConvArgs E n Γ (familyIdx w.nparams U)
                         (w.preMajor.drop (w.nparams + 1 + w.nMinors)))
          (ht : TelArgs … (.app (foldApps ty.motive
            (familyIdx w.nparams U)) (ctorMajorRec w)))
Forced, not chosen: `applyTel_rhsArgs_minorTel` COMPUTES the endpoint
of `rhsArgs` at `ty.mdom` to be `.app (foldApps M (familyIdx nparams U))
(foldApps ctorAcc fields)` for the telescope's OWN endpoint `U`, and
`telArgs_applyTel` says a `TelArgs` entails that equation — `applyTel`
is a function, so the endpoint is pinned and a `TelArgs` at the major's
index slots is not statable. The equation the deleted `IndexCoherent`
premise supplied as a REWRITE has no `ConvArgs` counterpart, so the
retype moves up one level into the single `HasTy.conv` below: the
`Conv.app` congruence that already moved the ARGUMENT (`hmajconv`,
`ctorMajorRec ⇝ ctorMajor`) now also moves the FUNCTION (`hFconv`,
motive-at-ctor-indices ⇝ motive-at-major-indices), by
`convArgs_foldApps` on the discharged `ConvArgs`. Nothing new is
introduced at the congruence layer. -/
def iotaPreserve_of_telArgs {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    (hmajconv : Conv E n Γ (ctorMajorRec w) (ctorMajor w))
    (hmdom : HasTy E n Γ w.minor ty.mdom)
    {U : Expr Nat}
    (hidxC : ConvArgs E n Γ (familyIdx w.nparams U)
      (w.preMajor.drop (w.nparams + 1 + w.nMinors)))
    (ht : TelArgs E n Γ
      (rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
        w.fields w.kinds w.ctorAfterParams)
      ty.mdom
      (.app (foldApps ty.motive
        (familyIdx w.nparams U))
        (ctorMajorRec w))) :
    HasTy E n Γ (iotaRhsOf w) T := by
  have ⟨A, B, _Mty, _Fpack, A_syn, hpre, hctor, hcv, _hminor, happ, _⟩ :=
    iotaPreserve_nil_pack w hT
  have hfT := (hasTy_rec_mtype w hT).2
  have spPre :=
    invertSpine (f := Expr.const w.recRef w.ls) (xs := w.preMajor) hpre
  have hpre_syn :
      HasTy E n Γ (foldApps (.const w.recRef w.ls) w.preMajor)
        (.pi A_syn (instTel w.preMajor w.recBody)) :=
    typedApplyTel hpci hE hΓ hfT uniqueTy_const happ spPre
  have hπ :=
    uniqueTy_foldApps hpci hE hΓ uniqueTy_const hpre hpre_syn
  let ⟨_hdom, hcod⟩ :=
    hpci hE Γ A B A_syn (instTel w.preMajor w.recBody) hΓ hπ
  have hget : (LocalDecl.assumption A :: Γ)[(0:Nat)]? =
      some (.assumption A) := List.getElem?_cons_zero
  have hvty : HasTy E n (substRemove (ctorMajor w) 0
      (LocalDecl.assumption A :: Γ))
      (lift 0 0 (ctorMajor w)) (lift 0 0 A) := by
    rw [substRemove_zero_cons, lift_zero, lift_zero]
    exact hctor
  have hinst := convSubst (j := 0) hE
    (ctorMajor w) A hcod hget hvty
  rw [substRemove_zero_cons, lift_zero] at hinst
  let Fη : Expr Nat :=
    foldApps ty.motive (w.preMajor.drop (w.nparams + 1 + w.nMinors))
  have hη : instTel w.preMajor w.recBody =
      .app (lift 0 1 Fη) (.bvar 0) := instTel_hrecBody w ty.hmotive
  have hη' : instantiate0 (ctorMajor w) (instTel w.preMajor w.recBody) =
      .app Fη (ctorMajor w) := by
    rw [hη, instantiate0_eta]
  have hinst' : Conv E n Γ (instantiate0 (ctorMajor w) B)
      (.app Fη (ctorMajor w)) := by
    rw [← hη']
    exact hinst
  let FηC : Expr Nat :=
    foldApps ty.motive (familyIdx w.nparams U)
  have hFconv : Conv E n Γ FηC Fη :=
    convArgs_foldApps hidxC (.refl _ ty.motive)
  have hrhs : HasTy E n Γ (iotaRhsOf w)
      (.app FηC
        (ctorMajorRec w)) := by
    change HasTy E n Γ
        (foldApps w.minor
          (rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
            w.fields w.kinds w.ctorAfterParams))
        (.app FηC (ctorMajorRec w))
    exact hasTy_fold_telArgs hmdom ht
  exact .conv _ _ _ _ hrhs
    (.trans _ _ _ _ (.app _ _ _ _ _ hFconv hmajconv)
      (.trans _ _ _ _ (.symm _ _ _ hinst') hcv))

def uniqueTy_bvar {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A B : Expr Nat}
    (hA : HasTy E n Γ (.bvar i) A)
    (hB : HasTy E n Γ (.bvar i) B) :
    Conv E n Γ A B := by
  let ⟨A1, hlk1, hc1⟩ := hasTyBvarInv hA rfl
  let ⟨A2, hlk2, hc2⟩ := hasTyBvarInv hB rfl
  have hEq : some A1 = some A2 := hlk1.symm.trans hlk2
  injection hEq with hAeq
  subst hAeq
  exact .trans _ _ _ _ (.symm _ _ _ hc1) hc2

/-- TelArgs from a spine inversion plus the syntactic `applyTel` of
the same function. Retypes arguments via PiConvInj of the function's
two Π types (the typedApplyTel circle-breaker). -/
def telArgs_of_spine {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    {f T : Expr Nat}
    (hfT : HasTy E n Γ f T)
    (hfun : ∀ {A B : Expr Nat},
      HasTy E n Γ f A → HasTy E n Γ f B → Conv E n Γ A B) :
    {args : List (Expr Nat)} → {U R : Expr Nat} →
    applyTel args T = some U →
    SpineInv E n Γ f args R →
    TelArgs E n Γ args T U
  | [], U, _R, happ, _sp => by
      simp only [applyTel] at happ
      injection happ with hU
      subst hU
      exact TelArgs.nil
  | x :: xs, U, _R, happ, sp =>
      let ⟨A_T, B_T, hTeq, happ'⟩ := applyTel_cons_inv x xs happ
      by
        subst hTeq
        cases sp with
        | cons hf ha s =>
            have hπ := hfun hfT hf
            let ⟨hdom, _hcod⟩ := hpci hE Γ A_T B_T _ _ hΓ hπ
            have haT : HasTy E n Γ x A_T :=
              .conv _ _ _ _ ha (.symm _ _ _ hdom)
            have hfapp : HasTy E n Γ (.app f x) (instantiate0 x B_T) :=
              .app _ _ _ _ _ hfT haT
            have ih := telArgs_of_spine hpci hE hΓ hfapp
              (fun hA' hB' =>
                uniqueTy_app_of hpci hE hΓ hfun hA' hB')
              happ' s
            exact TelArgs.cons haT ih

/-- The selected minor inhabits the 05 §12 telescope `mdom`. -/
def hasTy_minor_mdom {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    HasTy E n Γ w.minor ty.mdom := by
  have hfT := (hasTy_rec_mtype w hT).2
  have hlen := w.hpre
  have hidx := w.hidx
  have kdef : w.nparams + 1 + w.ctorIdx < w.preMajor.length := by omega
  have hx : (w.preMajor ++ [ctorMajor w])[w.nparams + 1 + w.ctorIdx]? =
      some w.minor := by
    have happ := List.getElem?_append_left (l₂ := [ctorMajor w]) kdef
    exact happ.trans w.hminor
  have htk : (w.preMajor ++ [ctorMajor w]).take
      (w.nparams + 1 + w.ctorIdx) = w.preMajor.take
        (w.nparams + 1 + w.ctorIdx) :=
    List.take_append_of_le_length (Nat.le_of_lt kdef)
  have hcons := drop_eq_cons_of_get hx
  have hsplit := List.take_append_drop (w.nparams + 1 + w.ctorIdx)
    (w.preMajor ++ [ctorMajor w])
  have hl : iotaLhsOf w =
      foldApps (.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w]) := rfl
  have hT' : HasTy E n Γ
      (foldApps (.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w])) T := by
    rw [← hl]; exact hT
  have hfold : foldApps (.const w.recRef w.ls)
      (w.preMajor ++ [ctorMajor w]) =
      foldApps
        (.app (foldApps (.const w.recRef w.ls)
          (w.preMajor.take (w.nparams + 1 + w.ctorIdx))) w.minor)
        ((w.preMajor ++ [ctorMajor w]).drop
          (w.nparams + 1 + w.ctorIdx + 1)) := by
    conv =>
      lhs
      rw [← hsplit, foldApps_append, htk, hcons, foldApps]
  have hTapp : HasTy E n Γ
      (foldApps
        (.app (foldApps (.const w.recRef w.ls)
          (w.preMajor.take (w.nparams + 1 + w.ctorIdx))) w.minor)
        ((w.preMajor ++ [ctorMajor w]).drop
          (w.nparams + 1 + w.ctorIdx + 1))) T := by
    rw [← hfold]; exact hT'
  have ⟨_, hfapp⟩ :=
    hasTyFoldAppsInv
      (f := Expr.app (foldApps (.const w.recRef w.ls)
        (w.preMajor.take (w.nparams + 1 + w.ctorIdx))) w.minor)
      (xs := (w.preMajor ++ [ctorMajor w]).drop
        (w.nparams + 1 + w.ctorIdx + 1)) hTapp
  have ⟨Mty', Bapp, hpreK, hminor', _⟩ := hasTyAppInv hfapp rfl
  have spK := invertSpine
    (f := Expr.const w.recRef w.ls)
    (xs := w.preMajor.take (w.nparams + 1 + w.ctorIdx)) hpreK
  have hmin_ty :
      HasTy E n Γ
        (foldApps (.const w.recRef w.ls)
          (w.preMajor.take (w.nparams + 1 + w.ctorIdx)))
        (.pi ty.mdom ty.restMin) :=
    typedApplyTel hpci hE hΓ hfT uniqueTy_const ty.hminDom spK
  have hπm : Conv E n Γ (.pi Mty' Bapp) (.pi ty.mdom ty.restMin) :=
    uniqueTy_foldApps (f := Expr.const w.recRef w.ls)
      (xs := w.preMajor.take (w.nparams + 1 + w.ctorIdx))
      hpci hE hΓ uniqueTy_const hpreK hmin_ty
  let ⟨hdomM, _⟩ := hpci hE Γ Mty' Bapp ty.mdom ty.restMin hΓ hπm
  exact .conv _ _ _ _ hminor' hdomM

/-- 0-ary TelArgs: `hminTel` says `mdom = iotaMdom w motive`, whose
0-ary conclusion is `M (familyIdx nparams ctorAfterParams) ctorMajorRec`
— the TELESCOPE's own result indices, at the 0-ary endpoint
`U = w.ctorAfterParams`. 00 §19.2 erratum 5: this is what the deleted
`IotaTyping.hminApply` used to assert in one piece — one half a witness
fact, the other half a redex fact.

M-003 (00 §19.2 ERRATUM 6, O-3 RIDER). Premise dropped and CONCLUSION
restated:
    old:  (hic : IndexCoherent w) → TelArgs … (.app (foldApps ty.motive
            (w.preMajor.drop (w.nparams + 1 + w.nMinors))) (ctorMajorRec w))
    new:  Σ' U, (applyTel w.fields w.ctorAfterParams = some U) ×'
            TelArgs … (.app (foldApps ty.motive (familyIdx w.nparams U))
              (ctorMajorRec w))
Forced, not chosen — see `iotaPreserve_of_telArgs` for the reason
(`telArgs_applyTel` + `applyTel_rhsArgs_minorTel` pin the endpoint).
The `U` is returned WITH its `applyTel` equation so the consumer can
feed exactly that `U` to `IndexCoherentConv`'s ∀-form; a `Σ'`-packaged
coherence statement would have produced a second `U` needing an
equality bridge. -/
def telArgs_nil_of_hmin {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) (ty : IotaTyping E w)
    (hflds : w.fields = []) :
    Σ' (U : Expr Nat),
      (applyTel w.fields w.ctorAfterParams = some U) ×'
      TelArgs E n Γ
        (rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
          w.fields w.kinds w.ctorAfterParams)
        ty.mdom
        (.app (foldApps ty.motive
          (familyIdx w.nparams U))
          (ctorMajorRec w)) := by
  have hk : w.kinds = [] := by
    have hlen := w.hlen
    rw [hflds] at hlen
    exact List.eq_nil_of_length_eq_zero hlen
  have hU : applyTel w.fields w.ctorAfterParams = some w.ctorAfterParams := by
    rw [hflds]
    exact applyTel_nil _
  have hmdom : ty.mdom =
      .app (foldApps ty.motive
        (familyIdx w.nparams w.ctorAfterParams))
        (ctorMajorRec w) := by
    rw [ty.hminTel]
    simp only [iotaMdom, hk, minorTel, ctorMajorRec, hflds,
      List.append_nil]
  refine ⟨w.ctorAfterParams, hU, ?_⟩
  simp only [hflds, hk, rhsArgs]
  rw [hmdom]
  exact TelArgs.nil

/-- Constructor const inhabits its stored type, from a typed iota lhs.

M-003 (00 §20.6 RULE CHANGES + DISCHARGE). Statement change:
    old:  HasTy E n Γ (.const w.ctorRef w.lsC) w.ctorMember.mtype
    new:  Σ' (_ : w.lsC.length = w.ctorMember.arity),
            HasTy E n Γ (.const w.ctorRef w.lsC)
              (instantiateLevels w.lsC w.ctorMember.mtype)
This is 00 §20.6 STORED-TYPE VIEW (3), the lhs-side view: the type of
the ACTUAL major. It stays confined to the derivation of the level fact
and never becomes an `IotaTyping` field (RULE ∀-BUNDLE). `hlen` is
returned for the same reason as on the recursor side. -/
def hasTy_const_of_ctorMajor {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (_ : w.lsC.length = w.ctorMember.arity),
      HasTy E n Γ (.const w.ctorRef w.lsC)
        (instantiateLevels w.lsC w.ctorMember.mtype) := by
  have ⟨_, _, _, _, _, _, hctor, _, _, _, _⟩ := iotaPreserve_nil_pack w hT
  have sp := invertSpine
    (f := Expr.const w.ctorRef w.lsC)
    (xs := w.ctorParams ++ w.fields) hctor
  let ⟨_, hf⟩ := spineInv_fun_ty sp
  let ⟨m, hres, hlen, hcv⟩ := hasTyConstInv hf rfl
  have hmeq : some m = some w.ctorMember := hres.symm.trans w.hctor
  injection hmeq with heq
  subst heq
  exact ⟨hlen, .conv _ _ _ _ hf (.symm _ _ _ hcv)⟩

/-- TelArgs of constructor fields after ctor-side params (`lsC`). -/
def telArgs_fields {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (After U : Expr Nat),
      (applyTel w.ctorParams (instantiateLevels w.lsC w.ctorMember.mtype) =
        some After) ×'
      TelArgs E n Γ w.fields After U := by
  have hfT := (hasTy_const_of_ctorMajor w hT).2
  have ⟨_, _, _, _, _, _, hctor, _, _, _, _⟩ := iotaPreserve_nil_pack w hT
  have spAll := invertSpine
    (f := Expr.const w.ctorRef w.lsC)
    (xs := w.ctorParams ++ w.fields) hctor
  have ⟨_, spP, spF⟩ := spineInv_append
    (xs := w.ctorParams) (ys := w.fields) spAll
  have htelC : isPiTel (w.nparams + w.fields.length)
      (instantiateLevels w.lsC w.ctorMember.mtype) = true :=
    peelPis_isPiTel _ _ (peelPis_instantiateLevels w.lsC _ _ w.hpeel)
  have htelP : isPiTel w.nparams
      (instantiateLevels w.lsC w.ctorMember.mtype) = true :=
    isPiTel_le (by omega) htelC
  have ⟨After, hAfter⟩ :=
    applyTel_isPiTel w.nparams (instantiateLevels w.lsC w.ctorMember.mtype)
      w.ctorParams (by rw [w.hctorParams]) htelP
  have hparams :
      HasTy E n Γ (foldApps (.const w.ctorRef w.lsC) w.ctorParams) After :=
    typedApplyTel hpci hE hΓ hfT uniqueTy_const hAfter spP
  have htelF : isPiTel w.kinds.length After = true :=
    isPiTel_of_applyTel w.nparams w.kinds.length
      (instantiateLevels w.lsC w.ctorMember.mtype)
      w.ctorParams (by rw [w.hctorParams])
      (by rw [w.hlen]; exact htelC) hAfter
  have ⟨U, happF⟩ :=
    applyTel_isPiTel w.kinds.length After w.fields (by rw [w.hlen]) htelF
  refine ⟨After, U, hAfter, telArgs_of_spine hpci hE hΓ hparams ?_ happF spF⟩
  intro A B hA hB
  exact uniqueTy_foldApps hpci hE hΓ uniqueTy_const hA hB

/-- TelArgs of the constructor spine (`ctorParams ++ fields`, `lsC`). -/
def telArgs_ctorSpine {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (U : Expr Nat),
      TelArgs E n Γ (w.ctorParams ++ w.fields)
        (instantiateLevels w.lsC w.ctorMember.mtype) U := by
  have hfT := (hasTy_const_of_ctorMajor w hT).2
  have ⟨_, _, _, _, _, _, hctor, _, _, _, _⟩ := iotaPreserve_nil_pack w hT
  have spAll := invertSpine
    (f := Expr.const w.ctorRef w.lsC)
    (xs := w.ctorParams ++ w.fields) hctor
  have ⟨_, spP, _spF⟩ := spineInv_append
    (xs := w.ctorParams) (ys := w.fields) spAll
  have ⟨After, Uf, hAfter, hfields⟩ := telArgs_fields hpci hE hΓ w hT
  have hparams :
      TelArgs E n Γ w.ctorParams
        (instantiateLevels w.lsC w.ctorMember.mtype) After :=
    telArgs_of_spine hpci hE hΓ hfT uniqueTy_const hAfter spP
  exact ⟨Uf, telArgs_append hparams hfields⟩


/-- TelArgs of the CTOR-side parameters at the constructor telescope
(the ctor-side half of `telArgs_ctorSpine`, exposed so its `After`
endpoint can be moved to the recursor-side copy). -/
def telArgs_ctorParams {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (After : Expr Nat),
      (applyTel w.ctorParams (instantiateLevels w.lsC w.ctorMember.mtype) =
        some After) ×'
      TelArgs E n Γ w.ctorParams
        (instantiateLevels w.lsC w.ctorMember.mtype) After := by
  have hfT := (hasTy_const_of_ctorMajor w hT).2
  have ⟨_, _, _, _, _, _, hctor, _, _, _, _⟩ := iotaPreserve_nil_pack w hT
  have spAll := invertSpine
    (f := Expr.const w.ctorRef w.lsC)
    (xs := w.ctorParams ++ w.fields) hctor
  have ⟨_, spP, _spF⟩ := spineInv_append
    (xs := w.ctorParams) (ys := w.fields) spAll
  have ⟨After, _Uf, hAfter, _hfields⟩ := telArgs_fields hpci hE hΓ w hT
  exact ⟨After, hAfter,
    telArgs_of_spine hpci hE hΓ hfT uniqueTy_const hAfter spP⟩

/-- 00 §20.6 DISCHARGE, recursor half of the arity fact:
`w.famMember.arity ≤ w.ls.length`. `hasTyConstInv`'s `hlen` (returned by
`hasTy_rec_mtype`) says `w.ls.length = w.recMember.arity`; 05 §11 group
arity coherence on `EnvWf` (`witness_recArity`) says that is `nU` or
`nU + 1`. This is the premise `applyTel_recPrefix_idx_last` carries. -/
theorem witness_famArity_le_ls {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvWf E n) (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    w.famMember.arity ≤ w.ls.length := by
  have hlen := (hasTy_rec_mtype w hT).1
  cases witness_recArity hE w with
  | inl h => omega
  | inr h => omega

/-- 00 §20.6 DISCHARGE, constructor half: the major's universe list has
EXACTLY the family arity, so truncating it at `nU` is the identity.
`hasTyConstInv`'s `hlen` gives `w.lsC.length = w.ctorMember.arity`;
05 §3 (`witness_ctorArity`) turns that into `= w.famMember.arity`. This
is what makes `ctorSpine_famApp`'s head `w.lsC.take nU` readable as
`w.lsC`, i.e. what makes `eqNList w.lsC (w.ls.take nU)` — the erratum-4
shape of `LevelCoherent` — the thing `FamAppConvInj` hands back. -/
theorem witness_lsC_length {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvWf E n) (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    w.lsC.length = w.famMember.arity := by
  have hlen := (hasTy_const_of_ctorMajor w hT).1
  rw [hlen, witness_ctorArity hE w]

theorem witness_lsC_take {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hE : EnvWf E n) (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    w.lsC.take w.famMember.arity = w.lsC := by
  rw [← witness_lsC_length hE w hT]
  exact List.take_length w.lsC

/-- The two family-application views of the major, CONVERTED — the
PRE-SPLIT content that both 00 §20.6's level discharge and 00 §19.2
erratum 6's index discharge read off ONE `FamAppConvInj` row.

Ctor side: the constructor telescope at the FREE `ctorParams`, as a
family application (`ctorSpine_famApp` over `ty.hctorResShape`, at the
00 §20.6 lhs-side view `instantiateLevels w.lsC`, whose head
`w.lsC.take nU` is `w.lsC` by `witness_lsC_take`). Recursor side: the
recursor's expected major domain (`applyTel_recPrefix_idx_last` over
the recursor-side view `instantiateLevels w.ls`, head
`w.ls.take nU`, DERIVED from `hmajorTy`'s canonical vector by
`map_instLevel_canonical`). Type uniqueness on the const-headed spine
(`uniqueTy_foldApps`, `hpci`) converts them. Never a syntactic equation
(00 §20.5).

It does NOT take `hfaci`: this is the INPUT to `FamAppConvInj`, not its
output. That is exactly what makes it usable twice — the LEVEL half
(`iotaLhs_ctorParams_levels_conv`) and the INDEX half
(`iotaLhs_ctorIdx_conv`) are two readings of the SAME conversion. -/
def iotaLhs_famApp_conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (idx : List (Expr Nat)),
      (applyTel (w.ctorParams ++ w.fields)
          (instantiateLevels w.lsC w.ctorMember.mtype) =
        some (foldApps (Expr.const w.familyRef w.lsC)
          (w.ctorParams ++ idx))) ×'
      Conv E n Γ
        (foldApps (Expr.const w.familyRef w.lsC) (w.ctorParams ++ idx))
        (foldApps (Expr.const w.familyRef (w.ls.take w.famMember.arity))
          (w.preMajor.take w.nparams ++
            w.preMajor.drop (w.nparams + 1 + w.nMinors))) := by
  have hidxlen :
      (w.preMajor.drop (w.nparams + 1 + w.nMinors)).length = w.nindices := by
    simp only [List.length_drop]
    have := w.hpre
    omega
  have ⟨Bih, hlastIdx⟩ :=
    applyTel_recPrefix_idx_last w (witness_famArity_le_ls hE w hT)
      (w.preMajor.drop (w.nparams + 1 + w.nMinors)) hidxlen
  have hpre0 : recPrefix w.preMajor w.nparams w.nMinors ++
      w.preMajor.drop (w.nparams + 1 + w.nMinors) = w.preMajor := by
    simp only [recPrefix]
    exact List.take_append_drop (w.nparams + 1 + w.nMinors) w.preMajor
  rw [hpre0] at hlastIdx
  have ⟨A, B, _Mty, _Fp, A_syn, hpre, hctor, _hcv, _hminor, happ, _hη⟩ :=
    iotaPreserve_nil_pack w hT
  have hAsyn : A_syn =
      foldApps (Expr.const w.familyRef (w.ls.take w.famMember.arity))
        (w.preMajor.take w.nparams ++
          w.preMajor.drop (w.nparams + 1 + w.nMinors)) := by
    have h : some (Expr.pi A_syn (instTel w.preMajor w.recBody)) =
        some (Expr.pi
          (foldApps (Expr.const w.familyRef (w.ls.take w.famMember.arity))
            (w.preMajor.take w.nparams ++
              w.preMajor.drop (w.nparams + 1 + w.nMinors))) Bih) :=
      happ.symm.trans hlastIdx
    have hπ := Option.some.inj h
    rw [Expr.pi.injEq] at hπ
    exact hπ.1
  have hfT := (hasTy_rec_mtype w hT).2
  have spPre :=
    invertSpine (f := Expr.const w.recRef w.ls) (xs := w.preMajor) hpre
  have hpre_syn :
      HasTy E n Γ (foldApps (.const w.recRef w.ls) w.preMajor)
        (.pi A_syn (instTel w.preMajor w.recBody)) :=
    typedApplyTel hpci hE hΓ hfT uniqueTy_const happ spPre
  have hπ := uniqueTy_foldApps hpci hE hΓ uniqueTy_const hpre hpre_syn
  have ⟨hdom, _hcod⟩ :=
    hpci hE Γ A B A_syn (instTel w.preMajor w.recBody) hΓ hπ
  have hctorSyn : HasTy E n Γ (ctorMajor w) A_syn :=
    .conv _ _ _ _ hctor hdom
  have ⟨Uctor, htelC⟩ := telArgs_ctorSpine hpci hE hΓ w hT
  have hUctor := telArgs_applyTel htelC
  have ⟨idx, hres⟩ :=
    ctorSpine_famApp w ty.hctorResShape w.lsC
      (Nat.le_of_eq (witness_lsC_length hE w hT).symm)
      w.ctorParams w.fields w.hctorParams rfl
  rw [witness_lsC_take hE w hT] at hres
  have hUeq : Uctor = foldApps (Expr.const w.familyRef w.lsC)
      (w.ctorParams ++ idx) := by
    have h : some Uctor = some (foldApps (Expr.const w.familyRef w.lsC)
        (w.ctorParams ++ idx)) := hUctor.symm.trans hres
    injection h
  have hfC := (hasTy_const_of_ctorMajor w hT).2
  have hctorU : HasTy E n Γ (ctorMajor w) Uctor :=
    hasTy_fold_telArgs hfC htelC
  have hconvU : Conv E n Γ Uctor A_syn :=
    uniqueTy_foldApps hpci hE hΓ uniqueTy_const hctorU hctorSyn
  rw [hUeq, hAsyn] at hconvU
  exact ⟨idx, hres, hconvU⟩

/-- 00 §20.6 DISCHARGE OF `LevelCoherent` (O-1) together with 00 §20.5
RULE FREE-FIELDS-ENTER-THROUGH-TYPING.

Two conclusions off ONE conversion — `iotaLhs_famApp_conv`'s — where
the tree previously discarded the first (`_hls` at the `FamAppConvInj`
call):

  `.1`  `eqNList w.lsC (w.ls.take w.famMember.arity)` — the erratum-4
        shape of the former `LevelCoherent` PREMISE, now a theorem;
  `.2`  the pointwise `ConvArgs` between the FREE ctor-side parameters
        of the major and the recursor-side copy `preMajor.take nparams`.

`FamAppConvInj` splits the pack's `Conv` into its LEVEL half and its
ARGUMENT half; `convArgs_append_split` takes the parameter prefix off
the latter.

Footprint (M-003): no new obligation. `FamAppConvInj` becomes strictly
more load-bearing — it now carries the level fact that used to enter as
a premise — and the two arity readouts (`witness_famArity_le_ls`,
`witness_lsC_take`) are `EnvWf` consequences of the 05 §2/§3 admission
checks W3 added to `EnvWf.indMember`. The INDEX half of the same
`FamAppConvInj` application is read by `iotaLhs_ctorIdx_conv` below
(00 §19.2 erratum 6); one row, three chains. -/
def iotaLhs_ctorParams_levels_conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (hfaci : FamAppConvInj E n)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    eqNList w.lsC (w.ls.take w.famMember.arity) ×'
      ConvArgs E n Γ w.ctorParams (w.preMajor.take w.nparams) := by
  have ⟨idx, _hres, hconvU⟩ := iotaLhs_famApp_conv hpci hE hΓ w ty hT
  have ⟨hls, hcargs⟩ :=
    hfaci hE Γ w.familyRef w.famMember w.lsC (w.ls.take w.famMember.arity)
      (w.ctorParams ++ idx)
      (w.preMajor.take w.nparams ++
        w.preMajor.drop (w.nparams + 1 + w.nMinors))
      hΓ w.hfam w.hfamK hconvU
  have hlenEq : w.ctorParams.length =
      (w.preMajor.take w.nparams).length := by
    rw [w.hctorParams]
    simp only [List.length_take]
    have := w.hpre
    omega
  exact ⟨hls, (convArgs_append_split hcargs hlenEq).1⟩

/-- The argument half of `iotaLhs_ctorParams_levels_conv`, under its old
name so every existing call site is unchanged (00 §20.6: "keep
`iotaLhs_ctorParams_conv` as its `.2`"). -/
def iotaLhs_ctorParams_conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (hfaci : FamAppConvInj E n)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    ConvArgs E n Γ w.ctorParams (w.preMajor.take w.nparams) :=
  (iotaLhs_ctorParams_levels_conv hpci hE hΓ hfaci w ty hT).2

/-- 00 §19.2 ERRATUM 6 DISCHARGE (O-1) of the `IndexCoherent` row, at
the corrected Conv-level statement `IndexCoherentConv`
(`RcicInvertFamily`). The major's INDEX arguments and the constructor's
result indices AT THE ACTUAL FIELDS are pointwise convertible, derived
from the redex's own typing — 00 §20.5 RULE
FREE-FIELDS-ENTER-THROUGH-TYPING, discharged rather than assumed.

No new obligation: `hpci`, `hE`, `hΓ`, `hfaci` are exactly the premises
`iotaPreserve` already carries, and every consumer supplies them.

Route. The constructor telescope is read as a family application TWICE
(`ctorSpine_famApp`): once at the FREE `w.ctorParams` under the
lhs-side view (inside `iotaLhs_famApp_conv`), and once at the
RECURSOR-side copy `w.preMajor.take w.nparams` under the recursor-side
view — the second reading pins the ∀-bound endpoint `U` as
`foldApps (I (ls.take nU)) (take nparams ++ idx')`, because
`applyTel_append_of` sends `w.hctorAfter` and the caller's `hU` to the
same telescope and `applyTel` is a function. `familyIdx_foldApps_const`
(`RcicIota`, syntactic) then reads `familyIdx nparams U = idx'`.
`convArgs_applyTel` over `iotaLhs_ctorParams_conv` (parameters) and the
00 §20.6 view conversion (levels) moves the ctor-side endpoint `Uctor`
to `U`; composing with the pack's own `Conv` gives a conversion between
the two family applications, and ONE `FamAppConvInj` application splits
it, `convArgs_append_split` dropping the common parameter prefix.

Composition happens at the `Conv` layer, BEFORE `hfaci` is applied — no
`convArgs_symm` / `convArgs_trans` is needed, and neither exists in the
tree.

STILL UNEXERCISED AT EVERY CARRIER, AND THE REMAINDER IS NAMED
(00 §20.7 D12 / CORRECTION SITE 7). Until that segment's batch B5 this
docstring said the blocker was `EnvWf`, uninhabited over an indexed
family. It no longer is: `vecEnvWfAt` inhabits `EnvWf vecEnv n` at every
`n`, and `vecRecAdmitted.typing` supplies `ty`. TWO of the SIX inputs
above are therefore supplied outright, and a THIRD only at one context:
`hΓ : CtxWf E n Γ` is free at `Γ = []` (`CtxWf.nil`) but not at a
generic `Γ`, since `.assumption` / `.letBinding` demand `HasTy`
derivations. What remains unsupplied is `hpci : PiConvInj` and
`hfaci : FamAppConvInj` — two OPEN 00 §19.2 rows on F-05b's own wall —
and `hT`, a `HasTy` derivation at `iotaLhsOf w`, which no fixture in
the tree carries. The admission bundle is NECESSARY BUT NOT SUFFICIENT
here, so this is still sealed and type-checked, not evaluated. -/
def iotaLhs_ctorIdx_conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (hfaci : FamAppConvInj E n)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    IndexCoherentConv n Γ w := by
  intro U hU
  have hlenP : (w.preMajor.take w.nparams).length = w.nparams := by
    simp only [List.length_take]
    have := w.hpre
    omega
  have ⟨idx', hres'⟩ :=
    ctorSpine_famApp w ty.hctorResShape w.ls
      (witness_famArity_le_ls hE w hT)
      (w.preMajor.take w.nparams) w.fields hlenP rfl
  have happ2 : applyTel (w.preMajor.take w.nparams ++ w.fields)
      (instantiateLevels w.ls w.ctorMember.mtype) = some U :=
    applyTel_append_of (w.preMajor.take w.nparams) w.fields w.hctorAfter hU
  have hUeq' : U = foldApps (Expr.const w.familyRef
      (w.ls.take w.famMember.arity))
      (w.preMajor.take w.nparams ++ idx') := by
    have h : some U = some (foldApps (Expr.const w.familyRef
        (w.ls.take w.famMember.arity))
        (w.preMajor.take w.nparams ++ idx')) := happ2.symm.trans hres'
    injection h
  have hidxU : familyIdx w.nparams U = idx' := by
    rw [hUeq']
    exact familyIdx_foldApps_const hlenP
  have ⟨Uctor, htelC⟩ := telArgs_ctorSpine hpci hE hΓ w hT
  have ⟨idx, hres, hconvPack⟩ := iotaLhs_famApp_conv hpci hE hΓ w ty hT
  have hUctorEq : Uctor = foldApps (Expr.const w.familyRef w.lsC)
      (w.ctorParams ++ idx) := by
    have h : some Uctor = some (foldApps (Expr.const w.familyRef w.lsC)
        (w.ctorParams ++ idx)) := (telArgs_applyTel htelC).symm.trans hres
    injection h
  have ⟨hls, hcargsP⟩ :=
    iotaLhs_ctorParams_levels_conv hpci hE hΓ hfaci w ty hT
  have hviews : Conv E n Γ (instantiateLevels w.lsC w.ctorMember.mtype)
      (instantiateLevels w.ls w.ctorMember.mtype) := by
    rw [witness_ctorMtype_view hE w w.ls]
    exact convInstantiateLevels w.ctorMember.mtype hls Γ
  have hcargsPF : ConvArgs E n Γ (w.ctorParams ++ w.fields)
      (w.preMajor.take w.nparams ++ w.fields) :=
    convArgs_append hcargsP (convArgs_refl w.fields)
  have hconvUU : Conv E n Γ Uctor U :=
    convArgs_applyTel hpci hE hΓ hcargsPF htelC hviews happ2
  have hconvPack' : Conv E n Γ Uctor
      (foldApps (Expr.const w.familyRef (w.ls.take w.famMember.arity))
        (w.preMajor.take w.nparams ++
          w.preMajor.drop (w.nparams + 1 + w.nMinors))) := by
    rw [hUctorEq]
    exact hconvPack
  have hconvIdx : Conv E n Γ U
      (foldApps (Expr.const w.familyRef (w.ls.take w.famMember.arity))
        (w.preMajor.take w.nparams ++
          w.preMajor.drop (w.nparams + 1 + w.nMinors))) :=
    .trans _ _ _ _ (.symm _ _ _ hconvUU) hconvPack'
  rw [hUeq'] at hconvIdx
  have ⟨_hls', hcargsIdx⟩ :=
    hfaci hE Γ w.familyRef w.famMember (w.ls.take w.famMember.arity)
      (w.ls.take w.famMember.arity)
      (w.preMajor.take w.nparams ++ idx')
      (w.preMajor.take w.nparams ++
        w.preMajor.drop (w.nparams + 1 + w.nMinors))
      hΓ w.hfam w.hfamK hconvIdx
  rw [hidxU]
  exact (convArgs_append_split hcargsIdx rfl).2

/-- 0-ary IotaPreserve via `hasTy_minor_mdom` + `TelArgs.nil`, with the
per-redex index conversion DISCHARGED (00 §19.2 erratum 6).
n-ary wall (attempt 12): `telArgs_of_spine` retypes args from two Π
typings of the *function*. For the minor, the second Π typing is the
rhs spine (`foldApps minor rhsArgs`), which is the goal. Ctor-spine
field types therefore do not pci-retype into `mdom` domains without a
05 §12 domain-alignment (ctor field type = minor telescope domain).
Failing statement: `IotaPreserve`.

M-003 (00 §19.2 ERRATUM 6 DISCHARGE, O-2). Premise deleted, obligation
premise added:
    old:  … (hΓ) (w) (ty) {T} (hmajconv) (hic : IndexCoherent w) (hflds) (hT)
    new:  … (hΓ) (hfaci : FamAppConvInj E n) (w) (ty) {T} (hmajconv)
          (hflds) (hT)
`hfaci` is what `iotaLhs_ctorIdx_conv` consumes, and every consumer of
this lemma's siblings (`iotaPreserve_plain`, `iotaPreserve_of_align`,
`iotaPreserve`) already carries it, so the file's M-003 footprint is
unchanged: `PiConvInj · FamAppConvInj · EnvWf · CtxWf`. The definition
MOVED down the file, past `iotaLhs_ctorIdx_conv`, for that reason —
that is the whole of the relocation. -/
def iotaPreserve_zero {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (hfaci : FamAppConvInj E n)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hmajconv : Conv E n Γ (ctorMajorRec w) (ctorMajor w))
    (hflds : w.fields = [])
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    HasTy E n Γ (iotaRhsOf w) T :=
  let ⟨U, hU, ht⟩ := telArgs_nil_of_hmin (Γ := Γ) w ty hflds
  iotaPreserve_of_telArgs hpci hE hΓ w ty hT hmajconv
    (hasTy_minor_mdom hpci hE hΓ w ty hT)
    (iotaLhs_ctorIdx_conv hpci hE hΓ hfaci w ty hT U hU)
    ht

/-- Recursor-side parameters read at the CONSTRUCTOR telescope, by
`hparamAlign` (00 §20.5 declaration-level T-class; a rewrite, not a
conversion). Endpoint is `w.ctorAfterParams` by `w.hctorAfter`. -/
def telArgs_params_ctor {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    TelArgs E n Γ (w.preMajor.take w.nparams)
      (instantiateLevels w.ls w.ctorMember.mtype)
      w.ctorAfterParams := by
  have hfT := (hasTy_rec_mtype w hT).2
  have ⟨_, _, _, _, _, hpre, _, _, _, _, _⟩ := iotaPreserve_nil_pack w hT
  have spAll := invertSpine (f := Expr.const w.recRef w.ls)
    (xs := w.preMajor) hpre
  have hsplit : w.preMajor =
      w.preMajor.take w.nparams ++ w.preMajor.drop w.nparams :=
    (List.take_append_drop w.nparams w.preMajor).symm
  rw [hsplit] at spAll
  have ⟨_, spP, _⟩ := spineInv_append
    (xs := w.preMajor.take w.nparams)
    (ys := w.preMajor.drop w.nparams) spAll
  have htelR : isPiTel w.nparams
      (instantiateLevels w.ls w.recMember.mtype) = true :=
    isPiTel_le (by omega)
      (peelPis_isPiTel _ _ (peelPis_instantiateLevels w.ls _ _ w.hpeelRec))
  have hlenP : (w.preMajor.take w.nparams).length = w.nparams := by
    simp only [List.length_take]
    have := w.hpre
    omega
  have ⟨_Up, happP⟩ := applyTel_isPiTel w.nparams
    (instantiateLevels w.ls w.recMember.mtype)
    (w.preMajor.take w.nparams) hlenP htelR
  have htelRec := telArgs_of_spine hpci hE hΓ hfT uniqueTy_const happP spP
  exact telArgs_paramAlign_go (instantiateLevels w.ls w.recMember.mtype)
    (instantiateLevels w.ls w.ctorMember.mtype) []
    (w.preMajor.take w.nparams) (applyTel_nil _) (applyTel_nil _)
    htelRec ty.hparamAlign w.hctorAfter

/-- Constructor fields read at the RECURSOR-side constructor telescope
`w.ctorAfterParams`. The domains move by `convArgs_applyTel` over
`iotaLhs_ctorParams_conv`; `telArgs_conv_dom` retypes each field. -/
def telArgs_fields_rec {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (hfaci : FamAppConvInj E n)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (U : Expr Nat), TelArgs E n Γ w.fields w.ctorAfterParams U := by
  have ⟨After, _Uf, hAfter, hfields⟩ := telArgs_fields hpci hE hΓ w hT
  have ⟨After', hAfter', htelP⟩ := telArgs_ctorParams hpci hE hΓ w hT
  have hAeq : After' = After := by
    have h : some After' = some After := hAfter'.symm.trans hAfter
    injection h
  subst hAeq
  have ⟨hls, hcargs⟩ := iotaLhs_ctorParams_levels_conv hpci hE hΓ hfaci w ty hT
  -- 00 §20.6 VIEW (2): the lhs-side view of the constructor's stored
  -- type (`instantiateLevels w.lsC`, what the major's own typing gives)
  -- converts to the recursor-side view (`instantiateLevels w.ls`, what
  -- `hctorAfter` reads) through the discharged level fact alone —
  -- `instantiateLevels_take` collapses `w.ls` to `w.ls.take nU`, and
  -- `convInstantiateLevels` closes the `eqNList` gap.
  have hviews : Conv E n Γ (instantiateLevels w.lsC w.ctorMember.mtype)
      (instantiateLevels w.ls w.ctorMember.mtype) := by
    rw [witness_ctorMtype_view hE w w.ls]
    exact convInstantiateLevels w.ctorMember.mtype hls Γ
  have hconv : Conv E n Γ After' w.ctorAfterParams :=
    convArgs_applyTel hpci hE hΓ hcargs htelP hviews w.hctorAfter
  have ⟨U, happU⟩ := applyTel_isPiTel w.kinds.length w.ctorAfterParams
    w.fields w.hlen.symm w.hctorTel
  exact ⟨U, telArgs_conv_dom hpci hE hΓ hfields hconv happU⟩

/-- The recursor-side constructor spine at the constructor telescope:
`preMajor.take nparams ++ fields`. This is the list every index walk
(`hidxWalk` / `hidxPos` / `hidxTy`, all keyed on `recParamsFields`)
indexes into. -/
def telArgs_recParamsFields {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (hfaci : FamAppConvInj E n)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (U : Expr Nat),
      TelArgs E n Γ (w.preMajor.take w.nparams ++ w.fields)
        (instantiateLevels w.ls w.ctorMember.mtype) U := by
  have hp := telArgs_params_ctor hpci hE hΓ w ty hT
  have ⟨U, hf⟩ := telArgs_fields_rec hpci hE hΓ hfaci w ty hT
  exact ⟨U, telArgs_append hp hf⟩

/-- The two forms of the major are convertible: `ctorMajorRec` (the
R-determined recursor-side application the rhs typing produces) and
`ctorMajor` (the lhs major, at the FREE `lsC` / `ctorParams`).

M-003 (00 §20.6 DISCHARGE, O-2). Premise deleted:
    old:  … (ty) (hlc : LevelCoherent w) (hT) → Conv …
    new:  … (ty) (hT) → Conv …
Both halves now come from ONE call to
`iotaLhs_ctorParams_levels_conv`: heads from its `.1` (the former
premise, now derived on the `FamAppConvInj` row), arguments from its
`.2`. Strengthening — the conclusion is unchanged and one hypothesis is
gone. -/
def conv_ctorMajorRec {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (hfaci : FamAppConvInj E n)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    Conv E n Γ (ctorMajorRec w) (ctorMajor w) :=
  let ⟨hls, hcargs⟩ := iotaLhs_ctorParams_levels_conv hpci hE hΓ hfaci w ty hT
  .symm _ _ _
    (convArgs_foldApps
      (convArgs_append hcargs (convArgs_refl w.fields))
      (.consts Γ w.ctorRef w.lsC (w.ls.take w.famMember.arity) hls))

/-- Recursor prefix applied to a field: IH typing `F f`. -/
def hasTy_recCall {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    {f A_syn : Expr Nat}
    (hx : HasTy E n Γ f A_syn)
    (hlast : applyTel w.preMajor (instantiateLevels w.ls w.recMember.mtype) =
      some (Expr.pi A_syn (instTel w.preMajor w.recBody))) :
    HasTy E n Γ
      (recCall (.const w.recRef w.ls) w.preMajor f)
      (.app (foldApps (recMotiveOf w)
        (w.preMajor.drop (w.nparams + 1 + w.nMinors))) f) := by
  have hfT := (hasTy_rec_mtype w hT).2
  have ⟨_, _, _, _, _, hpre, _, _, _, _, _⟩ := iotaPreserve_nil_pack w hT
  have spPre := invertSpine (f := Expr.const w.recRef w.ls)
    (xs := w.preMajor) hpre
  have hpre_syn :
      HasTy E n Γ (foldApps (.const w.recRef w.ls) w.preMajor)
        (.pi A_syn (instTel w.preMajor w.recBody)) :=
    typedApplyTel hpci hE hΓ hfT uniqueTy_const hlast spPre
  have sp := invertSpine
    (f := Expr.const w.recRef w.ls) (xs := w.preMajor) hpre_syn
  have spf := spineInv_snoc sp hx
  have hη : instTel w.preMajor w.recBody =
      .app (lift 0 1 (foldApps (recMotiveOf w)
        (w.preMajor.drop (w.nparams + 1 + w.nMinors)))) (.bvar 0) :=
    instTel_hrecBody w (recMotiveOf_spec w)
  have happ := applyTel_snoc f w.preMajor
    (instantiateLevels w.ls w.recMember.mtype) hlast
  rw [hη] at happ
  simp only [instantiate0_eta] at happ
  have hty := typedApplyTel hpci hE hΓ hfT uniqueTy_const happ spf
  simp only [recCall]
  exact hty

/-- 05 §14 IH typing: recursor applied to field indices, last-Π
domain is the field type `A` (not the major `A_syn`). No `Conv A A_syn`.
`hpreIdx` is the remaining n-ary work: type `recPrefix ++ familyIdx`. -/
def hasTy_recCallField {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    {f A B : Expr Nat}
    (hx : HasTy E n Γ f A)
    (hpreIdx : HasTy E n Γ
      (foldApps (.const w.recRef w.ls)
        (recPrefix w.preMajor w.nparams w.nMinors ++
          familyIdx w.nparams A))
      (.pi A B))
    (hlast : applyTel
      (recPrefix w.preMajor w.nparams w.nMinors ++
        familyIdx w.nparams A)
      (instantiateLevels w.ls w.recMember.mtype) = some (.pi A B))
    (hB : B = .app (lift 0 1
      (foldApps (recMotiveOf w) (familyIdx w.nparams A))) (.bvar 0)) :
    HasTy E n Γ
      (recCallField (.const w.recRef w.ls) w.preMajor
        w.nparams w.nMinors f A)
      (.app (foldApps (recMotiveOf w) (familyIdx w.nparams A)) f) := by
  have hfT := (hasTy_rec_mtype w hT).2
  have sp := invertSpine
    (f := Expr.const w.recRef w.ls)
    (xs := recPrefix w.preMajor w.nparams w.nMinors ++
      familyIdx w.nparams A) hpreIdx
  have spf := spineInv_snoc sp hx
  have happ := applyTel_snoc f
    (recPrefix w.preMajor w.nparams w.nMinors ++
      familyIdx w.nparams A)
    (instantiateLevels w.ls w.recMember.mtype) hlast
  rw [hB] at happ
  simp only [instantiate0_eta] at happ
  have hty := typedApplyTel hpci hE hΓ hfT uniqueTy_const happ spf
  simp only [recCallField]
  exact hty

/-- Recursor prefix `params motive minors` is typed from the iota lhs. -/
def hasTy_recPrefix {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (U : Expr Nat),
      HasTy E n Γ
        (foldApps (.const w.recRef w.ls)
          (recPrefix w.preMajor w.nparams w.nMinors)) U := by
  have ⟨_, _, _, _, _, hpre, _, _, _, _, _⟩ := iotaPreserve_nil_pack w hT
  have sp := invertSpine (f := Expr.const w.recRef w.ls)
    (xs := w.preMajor) hpre
  have hsplit :
      w.preMajor =
        recPrefix w.preMajor w.nparams w.nMinors ++
          w.preMajor.drop (w.nparams + 1 + w.nMinors) :=
    (List.take_append_drop (w.nparams + 1 + w.nMinors) w.preMajor).symm
  rw [hsplit] at sp
  have ⟨_, _, srest⟩ := spineInv_append
    (xs := recPrefix w.preMajor w.nparams w.nMinors)
    (ys := w.preMajor.drop (w.nparams + 1 + w.nMinors)) sp
  let ⟨U, hf⟩ := spineInv_fun_ty srest
  exact ⟨U, hf⟩

/-- Apply already-typed field indices to the recursor prefix (05 §8). -/
def hasTy_recPrefix_idx {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {rec : Expr Nat} {pre : List (Expr Nat)} {nparams nMinors : Nat}
    {A U V : Expr Nat}
    (hpre : HasTy E n Γ
      (foldApps rec (recPrefix pre nparams nMinors)) U)
    (hidx : TelArgs E n Γ (familyIdx nparams A) U V) :
    HasTy E n Γ
      (foldApps rec (recPrefix pre nparams nMinors ++ familyIdx nparams A))
      V := by
  have h := hasTy_fold_telArgs hpre hidx
  rw [foldApps_append]
  exact h

/-- A term on the constructor spine is typed (params then fields). -/
def hasTy_mem_ctorSpine {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    {x : Expr Nat} {i : Nat}
    (hi : (w.ctorParams ++ w.fields)[i]? = some x) :
    Σ' (A : Expr Nat), HasTy E n Γ x A := by
  have ⟨_, _, _, _, _, _, hctor, _, _, _, _⟩ := iotaPreserve_nil_pack w hT
  exact hasTyArgOfFold
    (f := Expr.const w.ctorRef w.lsC)
    (xs := w.ctorParams ++ w.fields) hctor hi

/-- Apply `familyIdx` to the recursor remainder after `recPrefix`.
Lookup-TelArgs of those indices at this type needs Conv of the
ctor-spine type of each index with the recursor index-telescope
domain (not definitional; M-001). -/
def applyTel_familyIdx {E : ResolvedEnv} (w : IotaWitness E)
    (A : Expr Nat) {U : Expr Nat}
    (happPre : applyTel (recPrefix w.preMajor w.nparams w.nMinors)
      (instantiateLevels w.ls w.recMember.mtype) = some U)
    (hlen : (familyIdx w.nparams A).length = w.nindices) :
    Σ' (V : Expr Nat),
      applyTel (familyIdx w.nparams A) U = some V := by
  have htel1 := isPiTel_recPrefix_rem_inst w w.ls happPre
  have htel0 := isPiTel_mono w.nindices U htel1
  exact applyTel_isPiTel w.nindices U (familyIdx w.nparams A) hlen htel0

/-- Recover a typing of `x` from an argument of a typed spine. -/
def hasTy_in_appsSpine_args {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (h : HasTy E n Γ e T) {x : Expr Nat} {i : Nat}
    (hi : (appsSpine e).2[i]? = some x) :
    Σ' (A : Expr Nat), HasTy E n Γ x A :=
  hasTyArgOfFold (f := (appsSpine e).1) (xs := (appsSpine e).2)
    (by
      have he : foldApps (appsSpine e).1 (appsSpine e).2 = e :=
        foldApps_appsSpine e
      rw [he]
      exact h) hi

/-- Recursor prefix at the syntactic remainder after `applyTel`. -/
def typed_recPrefix {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (U : Expr Nat),
      (applyTel (recPrefix w.preMajor w.nparams w.nMinors)
        (instantiateLevels w.ls w.recMember.mtype) = some U) ×'
      HasTy E n Γ
        (foldApps (.const w.recRef w.ls)
          (recPrefix w.preMajor w.nparams w.nMinors)) U := by
  have ⟨U, happ⟩ := applyTel_recPrefix_inst w w.ls
  have hfT := (hasTy_rec_mtype w hT).2
  have ⟨_, _, _, _, _, hpre, _, _, _, _, _⟩ := iotaPreserve_nil_pack w hT
  have spAll := invertSpine (f := Expr.const w.recRef w.ls)
    (xs := w.preMajor) hpre
  have hsplit :
      w.preMajor =
        recPrefix w.preMajor w.nparams w.nMinors ++
          w.preMajor.drop (w.nparams + 1 + w.nMinors) :=
    (List.take_append_drop (w.nparams + 1 + w.nMinors) w.preMajor).symm
  rw [hsplit] at spAll
  have ⟨_, spPre, _⟩ := spineInv_append
    (xs := recPrefix w.preMajor w.nparams w.nMinors)
    (ys := w.preMajor.drop (w.nparams + 1 + w.nMinors)) spAll
  exact ⟨U, happ,
    typedApplyTel hpci hE hΓ hfT uniqueTy_const happ spPre⟩

/-- Type uniqueness, Type-valued (DT-012 as a `def`). Footprint (M-003):
`PiConvInj` + `SortConvChar` (both `EnvWf`+`CtxWf`-conditioned, O-3) +
`convSubst`/`convSubstLet`. Used to unique-ty an index term at
ctor-spine vs inverted-spine types; not threaded into IotaPreserve
(F-05a stays `PiConvInj`-only). -/
def uniqueTy_term {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n) (hscc : SortConvChar E n)
    (hE : EnvWf E n) :
    (Γ : LCtx) → CtxWf E n Γ → (e : Expr Nat) → {A B : Expr Nat} →
    HasTy E n Γ e A → HasTy E n Γ e B → Conv E n Γ A B
  | Γ, hΓ, .bvar i, A, B, hA, hB => uniqueTy_bvar hA hB
  | Γ, hΓ, .sort l, A, B, hA, hB =>
      .trans _ _ _ _ (.symm _ _ _ (hasTySortInv hA rfl))
        (hasTySortInv hB rfl)
  | Γ, hΓ, .const r ls, A, B, hA, hB => uniqueTy_const hA hB
  | Γ, hΓ, .app f a, A, B, hA, hB =>
      uniqueTy_app_of hpci hE hΓ
        (fun hA' hB' => uniqueTy_term hpci hscc hE Γ hΓ f hA' hB')
        hA hB
  | Γ, hΓ, .lam A0 body, A, B, hA, hB =>
      let ⟨u0, B1, hA0ty, hbody1, hc1⟩ := hasTyLamInv hA rfl
      let ⟨_, B2, _, hbody2, hc2⟩ := hasTyLamInv hB rfl
      have hBconv :=
        uniqueTy_term hpci hscc hE
          (LocalDecl.assumption A0 :: Γ)
          (.assumption Γ A0 u0 hΓ hA0ty) body hbody1 hbody2
      have hπ : Conv E n Γ (.pi A0 B1) (.pi A0 B2) :=
        .pi _ _ _ _ _ (.refl _ _) hBconv
      .trans _ _ _ _ (.symm _ _ _ hc1) (.trans _ _ _ _ hπ hc2)
  | Γ, hΓ, .pi A0 B0, A, B, hA, hB =>
      let ⟨u, v, hAty, hBty, hcA⟩ := hasTyPiInv hA rfl
      let ⟨u', v', hAty', hBty', hcB⟩ := hasTyPiInv hB rfl
      have hΓ' : CtxWf E n (LocalDecl.assumption A0 :: Γ) :=
        .assumption Γ A0 u hΓ hAty
      have hAu := uniqueTy_term hpci hscc hE Γ hΓ A0 hAty hAty'
      have hBv :=
        uniqueTy_term hpci hscc hE
          (LocalDecl.assumption A0 :: Γ) hΓ' B0 hBty hBty'
      have eu : eqN u u' := hscc hE Γ u u' hΓ hAu
      have ev : eqN v v' :=
        hscc hE (LocalDecl.assumption A0 :: Γ) v v' hΓ' hBv
      have eimax : eqN (.imax u v) (.imax u' v') := fun ρ => by
        simp only [eval]
        rw [eu ρ, ev ρ]
      .trans _ _ _ _ (.symm _ _ _ hcA)
        (.trans _ _ _ _ (.sorts _ _ _ eimax) hcB)
  | Γ, hΓ, .letE A0 val body, A, B, hA, hB =>
      let ⟨u0, B1, hA0ty, hv1, hb1, hc1⟩ := hasTyLetInv hA rfl
      let ⟨_, B2, _, _hv2, hb2, hc2⟩ := hasTyLetInv hB rfl
      have hBconv :=
        uniqueTy_term hpci hscc hE
          (LocalDecl.letBinding A0 val :: Γ)
          (.letBinding Γ A0 u0 val hΓ hA0ty hv1) body hb1 hb2
      have hget : (LocalDecl.letBinding A0 val :: Γ)[(0:Nat)]? =
          some (.letBinding A0 val) := List.getElem?_cons_zero
      have hvty : HasTy E n (substRemove val 0
          (LocalDecl.letBinding A0 val :: Γ))
          (lift 0 0 val) (lift 0 0 A0) := by
        rw [substRemove_zero_cons, lift_zero, lift_zero]
        exact hv1
      have hcod0 := convSubstLet (j := 0) hE A0 val
        hBconv hget hvty
      by
        rw [substRemove_zero_cons, lift_zero] at hcod0
        exact .trans _ _ _ _ (.symm _ _ _ hc1) (.trans _ _ _ _ hcod0 hc2)
  | Γ, hΓ, .lit t, A, B, hA, hB =>
      let ⟨_Ta, hexpA, hcA⟩ := hasTyLitInv hA rfl
      let ⟨_Tb, hexpB, hcB⟩ := hasTyLitInv hB rfl
      .trans _ _ _ _ (.symm _ _ _ hcA)
        (.trans _ _ _ _ (uniqueTy_natExpand hpci hE hΓ t hexpA hexpB) hcB)

/-- Transport a spine inversion along equality of the argument list. -/
def spineInv_args_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f : Expr Nat}
    {xs ys : List (Expr Nat)} {T : Expr Nat}
    (h : xs = ys) (s : SpineInv E n Γ f xs T) :
    SpineInv E n Γ f ys T := by
  rw [← h]; exact s

/-- Honest PiConvInj retype (M-001): `x` is the first remaining major
index, so the inverted spine types `x` at `Ainv`; unique-ty against the
ctor-spine typing, pci of the two Π typings of `recPrefix`. Does not
identify a subterm of a computed index (`succ n`) with the index type
(that would fake `Afound = Ainv`). -/
def conv_ctor_rec_idx {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n) (hscc : SortConvChar E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    {x Afound A B : Expr Nat}
    (hx : HasTy E n Γ x Afound)
    (hg : HasTy E n Γ
      (foldApps (.const w.recRef w.ls)
        (recPrefix w.preMajor w.nparams w.nMinors)) (.pi A B))
    (hxm : (w.preMajor.drop (w.nparams + 1 + w.nMinors))[0]? = some x) :
    Conv E n Γ Afound A := by
  have ⟨_, _, _, _, _, hpre, _, _, _, _, _⟩ := iotaPreserve_nil_pack w hT
  have spAll := invertSpine (f := Expr.const w.recRef w.ls)
    (xs := w.preMajor) hpre
  have hsplit :
      w.preMajor =
        recPrefix w.preMajor w.nparams w.nMinors ++
          w.preMajor.drop (w.nparams + 1 + w.nMinors) :=
    (List.take_append_drop (w.nparams + 1 + w.nMinors) w.preMajor).symm
  rw [hsplit] at spAll
  have ⟨_, _, spRest⟩ := spineInv_append
    (xs := recPrefix w.preMajor w.nparams w.nMinors)
    (ys := w.preMajor.drop (w.nparams + 1 + w.nMinors)) spAll
  cases hdrop : w.preMajor.drop (w.nparams + 1 + w.nMinors) with
  | nil =>
      rw [hdrop] at hxm
      cases hxm
  | cons m ms =>
      have spRest' := spineInv_args_eq hdrop spRest
      have hx0 : m = x := by
        rw [hdrop] at hxm
        simp only [List.getElem?_cons_zero] at hxm
        injection hxm
      cases spRest' with
      | cons hf ha _s =>
          have hπm := uniqueTy_foldApps hpci hE hΓ uniqueTy_const
            hg hf
          have ⟨hdom, _⟩ := hpci hE Γ A B _ _ hΓ hπm
          subst hx0
          exact .trans _ _ _ _
            (uniqueTy_term hpci hscc hE Γ hΓ m hx ha)
            (.symm _ _ _ hdom)

/-- TelArgs of `familyIdx` when it equals the major-index spine
(05 §8 exact occurrence at the result indices). PiConvInj retypes each
argument from the inverted spine; no `Afound = A` (M-001). Indexed
constructors whose field indices are not the result indices (Vec.cons:
`n` vs `n+1`) are not this lemma. -/
def telArgs_familyIdx_of_majors {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    {A : Expr Nat}
    (heq : familyIdx w.nparams A =
      w.preMajor.drop (w.nparams + 1 + w.nMinors)) :
    Σ' (U V : Expr Nat),
      (applyTel (recPrefix w.preMajor w.nparams w.nMinors)
        (instantiateLevels w.ls w.recMember.mtype) = some U) ×'
      (applyTel (familyIdx w.nparams A) U = some V) ×'
      TelArgs E n Γ (familyIdx w.nparams A) U V := by
  have ⟨U, happ, hty⟩ := typed_recPrefix hpci hE hΓ w hT
  have hlen : (familyIdx w.nparams A).length = w.nindices := by
    rw [heq]
    simp only [List.length_drop]
    have := w.hpre
    omega
  have ⟨V, happIdx⟩ := applyTel_familyIdx w A happ hlen
  have ⟨_, _, _, _, _, hpre, _, _, _, _, _⟩ := iotaPreserve_nil_pack w hT
  have spAll := invertSpine (f := Expr.const w.recRef w.ls)
    (xs := w.preMajor) hpre
  have hsplit :
      w.preMajor =
        recPrefix w.preMajor w.nparams w.nMinors ++
          w.preMajor.drop (w.nparams + 1 + w.nMinors) :=
    (List.take_append_drop (w.nparams + 1 + w.nMinors) w.preMajor).symm
  rw [hsplit] at spAll
  have ⟨_, _, spRest⟩ := spineInv_append
    (xs := recPrefix w.preMajor w.nparams w.nMinors)
    (ys := w.preMajor.drop (w.nparams + 1 + w.nMinors)) spAll
  have spIdx := spineInv_args_eq heq.symm spRest
  exact ⟨U, V, happ, happIdx,
    telArgs_of_spine hpci hE hΓ hty
      (fun hA hB =>
        uniqueTy_foldApps hpci hE hΓ uniqueTy_const hA hB)
      happIdx spIdx⟩

/-- Recursor prefix plus field indices, when those indices are the
major-index spine. Last-Π domain is the recursor remainder (major type),
not definitionally the field type (M-001). -/
def hasTy_recPrefix_idx_of_majors {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    {A : Expr Nat}
    (heq : familyIdx w.nparams A =
      w.preMajor.drop (w.nparams + 1 + w.nMinors)) :
    Σ' (V : Expr Nat),
      HasTy E n Γ
        (foldApps (.const w.recRef w.ls)
          (recPrefix w.preMajor w.nparams w.nMinors ++
            familyIdx w.nparams A)) V ×'
      (applyTel
        (recPrefix w.preMajor w.nparams w.nMinors ++
          familyIdx w.nparams A)
        (instantiateLevels w.ls w.recMember.mtype) = some V) := by
  have ⟨U, V, happ, happIdx, htel⟩ :=
    telArgs_familyIdx_of_majors hpci hE hΓ w hT heq
  have ⟨U', happPre, hty⟩ := typed_recPrefix hpci hE hΓ w hT
  have hU : U = U' := by
    have h : some U = some U' := happ.symm.trans happPre
    injection h
  subst hU
  have htyV := hasTy_recPrefix_idx hty htel
  have happAll := applyTel_append_of
    (recPrefix w.preMajor w.nparams w.nMinors)
    (familyIdx w.nparams A) happ happIdx
  exact ⟨V, htyV, happAll⟩

/-- 05 §13 last-Π is `I params field_indices`, equal to the DirectRec
field type (not `Afound = A`). `familyIdx = majors` supplies the
prefix typing via pci retype of the major-index spine. -/
def hasTy_recCallField_aligned {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    {f A B : Expr Nat} {ks : List RecKind} {fs : List (Expr Nat)}
    (hx : HasTy E n Γ f A)
    (hsp : directRecFamilySpineExact w.familyRef
      (w.ls.take w.famMember.arity) w.nparams
      (w.preMajor.take w.nparams) (.directRec :: ks)
      (.pi A B) (f :: fs) = true)
    (hlen : (familyIdx w.nparams A).length = w.nindices)
    (heq : familyIdx w.nparams A =
      w.preMajor.drop (w.nparams + 1 + w.nMinors)) :
    HasTy E n Γ
      (recCallField (.const w.recRef w.ls) w.preMajor
        w.nparams w.nMinors f A)
      (.app (foldApps (recMotiveOf w) (familyIdx w.nparams A)) f) := by
  have ⟨_args, _hspine, hAfam⟩ := directRec_eq_family hsp
  have ⟨Bih, hlast⟩ :=
    applyTel_recPrefix_idx_last w (witness_famArity_le_ls hE w hT)
      (familyIdx w.nparams A) hlen
  rw [← hAfam] at hlast
  have ⟨V, htyV, happAll⟩ :=
    hasTy_recPrefix_idx_of_majors hpci hE hΓ w hT heq
  have hVU : V = Expr.pi A Bih := by
    have h : some V = some (Expr.pi A Bih) := happAll.symm.trans hlast
    injection h
  subst hVU
  have hpre0 : recPrefix w.preMajor w.nparams w.nMinors ++
      familyIdx w.nparams A = w.preMajor := by
    simp only [recPrefix]
    rw [heq]
    exact List.take_append_drop (w.nparams + 1 + w.nMinors) w.preMajor
  have ⟨A_syn, hrecLast⟩ := recLastPi_inst w w.ls
  have hη := instTel_hrecBody w (recMotiveOf_spec w)
  have hBih : Bih =
      Expr.app (lift 0 1 (foldApps (recMotiveOf w) (familyIdx w.nparams A)))
        (.bvar 0) := by
    have h : some (Expr.pi A Bih) =
        some (Expr.pi A_syn (instTel w.preMajor w.recBody)) := by
      have h1 := hlast
      rw [hpre0] at h1
      exact h1.symm.trans hrecLast
    injection h with hπ
    injection hπ with _hA hbody
    rw [hbody, hη, heq]
  exact hasTy_recCallField hpci hE hΓ w hT hx htyV hlast hBih

/-- `.app` case of `hasTy_of_idxSrc`. The two subderivations are
arguments: the recursive calls stay on the source, not inside `cases`. -/
def hasTy_appIdx {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {Uctor : Expr Nat} (fam : Nat) (ctorType : Expr Nat)
    (pf : List (Expr Nat)) (hpf : TelArgs E n Γ pf ctorType Uctor)
    (sf sa : IdxSrc)
    (ihsf : ∀ y Ty, idxSrcMatch fam pf y sf = true →
      idxSrcTy fam E ctorType pf y sf = some Ty →
      IdxSrcFuel n y sf → HasTy E n Γ y Ty)
    (ihsa : ∀ y Ty, idxSrcMatch fam pf y sa = true →
      idxSrcTy fam E ctorType pf y sa = some Ty →
      IdxSrcFuel n y sa → HasTy E n Γ y Ty)
    (x Ac : Expr Nat)
    (hmatch : idxSrcMatch fam pf x (.app sf sa) = true)
    (hty : idxSrcTy fam E ctorType pf x (.app sf sa) = some Ac)
    (hfuel : IdxSrcFuel n x (.app sf sa)) : HasTy E n Γ x Ac := by
  cases x with
  | app f a =>
      simp only [idxSrcMatch, Bool.and_eq_true] at hmatch
      simp only [idxSrcTy] at hty
      cases htf : idxSrcTy fam E ctorType pf f sf with
      | none => simp only [htf] at hty; cases hty
      | some Tf =>
          cases hta : idxSrcTy fam E ctorType pf a sa with
          | none => simp only [htf, hta] at hty; cases hty
          | some Ta =>
              cases Tf with
              | pi A B =>
                  simp only [htf, hta] at hty
                  if hTA : Ta = A then
                    rw [hTA] at hta
                    simp only [if_pos hTA] at hty
                    cases hty
                    exact HasTy.app Γ f a A B
                      (ihsf f (.pi A B) hmatch.1 htf hfuel.1)
                      (ihsa a A hmatch.2 hta hfuel.2)
                  else
                    simp only [if_neg hTA] at hty
                    cases hty
              | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
                  simp only [htf, hta] at hty
                  cases hty
  | bvar _ | sort _ | const _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
      simp only [idxSrcMatch] at hmatch
      nomatch hmatch

/-- A matched `IdxSrc` is a real typing derivation. `.pos` and
`.constField` read one telescope slot; `.app` is the two subderivations,
not a requirement that the whole term equal a field. `.lit` is `none`. -/
def hasTy_of_idxSrc {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {Uctor : Expr Nat} (fam : Nat) (ctorType : Expr Nat)
    (pf : List (Expr Nat)) (hpf : TelArgs E n Γ pf ctorType Uctor)
    (x : Expr Nat) (s : IdxSrc) (Ac : Expr Nat)
    (hmatch : idxSrcMatch fam pf x s = true)
    (hty : idxSrcTy fam E ctorType pf x s = some Ac)
    (hfuel : IdxSrcFuel n x s) : HasTy E n Γ x Ac :=
  match s with
  | .pos i => by
      simp only [idxSrcMatch] at hmatch
      have hx : pf[i]? = some x := of_decide_eq_true hmatch
      simp only [idxSrcTy] at hty
      cases happ : applyTel (pf.take i) ctorType with
      | none => simp only [happ] at hty; cases hty
      | some U =>
          cases U with
          | pi A B =>
              simp only [happ] at hty
              cases hty
              exact telArgs_lookup hpf hx happ
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              simp only [happ] at hty
              cases hty
  | .constField i => by
      cases x with
      | const r ls =>
          simp only [idxSrcMatch] at hmatch
          have hx : pf[i]? = some (.const r ls) := of_decide_eq_true hmatch
          simp only [idxSrcTy] at hty
          cases happ : applyTel (pf.take i) ctorType with
          | none => simp only [happ] at hty; cases hty
          | some U =>
              cases U with
              | pi A B =>
                  simp only [happ] at hty
                  cases hty
                  exact telArgs_lookup hpf hx happ
              | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
                  simp only [happ] at hty
                  cases hty
      | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcMatch] at hmatch
          nomatch hmatch
  | .constNotFam r => by
      cases x with
      | const r' ls =>
          simp only [idxSrcMatch, idxSrcTy] at hmatch hty
          simp only [hmatch, if_true] at hty
          cases hm : E.members r with
          | none => simp only [hm] at hty; cases hty
          | some m =>
              simp only [hm] at hty
              cases hlen : decide (ls.length = m.arity) with
              | false => simp only [hlen] at hty; cases hty
              | true =>
                  simp only [hlen, if_true] at hty
                  cases hty
                  have hr := (bool_and_true hmatch).1
                  have hr' : r' = r := of_decide_eq_true hr
                  cases hr'
                  exact HasTy.const Γ r ls m hm (of_decide_eq_true hlen) hfuel
      | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcMatch] at hmatch
          nomatch hmatch
  | .app sf sa =>
      hasTy_appIdx fam ctorType pf hpf sf sa
        (fun y Ty hy hyty hyfuel =>
          hasTy_of_idxSrc fam ctorType pf hpf y sf Ty hy hyty hyfuel)
        (fun y Ty hy hyty hyfuel =>
          hasTy_of_idxSrc fam ctorType pf hpf y sa Ty hy hyty hyfuel)
        x Ac hmatch hty hfuel
  | .sort => by
      cases x with
      | sort u =>
          simp only [idxSrcTy] at hty
          cases hty
          exact HasTy.sort Γ u
      | bvar _ | const _ _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ =>
          simp only [idxSrcTy] at hty
          cases hty
  | .lit _ => by
      simp only [idxSrcTy] at hty
      cases hty

/-- TelArgs of an arbitrary index list given composable `IdxSrc`
evidence. An index may be an application of sourced subterms; it does
not have to equal one field. -/
def telArgs_idxGo {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    {Uctor : Expr Nat}
    (hctor : TelArgs E n Γ (w.preMajor.take w.nparams ++ w.fields)
      (instantiateLevels w.ls w.ctorMember.mtype) Uctor) :
    (pre rest : List (Expr Nat)) → (ss : List IdxSrc) → {U : Expr Nat} →
    HasTy E n Γ
      (foldApps (.const w.recRef w.ls)
        (recPrefix w.preMajor w.nparams w.nMinors ++ pre)) U →
    applyTel (recPrefix w.preMajor w.nparams w.nMinors ++ pre)
      (instantiateLevels w.ls w.recMember.mtype) = some U →
    idxSrcAlignGo w.familyRef E
      (instantiateLevels w.ls w.recMember.mtype)
      (instantiateLevels w.ls w.ctorMember.mtype)
      (recPrefix w.preMajor w.nparams w.nMinors)
      (w.preMajor.take w.nparams ++ w.fields) pre rest ss = true →
    idxSrcZip w.familyRef
      (w.preMajor.take w.nparams ++ w.fields) rest ss = true →
    IdxSrcFuelList n rest ss →
    Σ' (V : Expr Nat), TelArgs E n Γ rest U V
  | pre, [], [], U, hfun, happ, _, _, _ => ⟨U, TelArgs.nil⟩
  | pre, x :: xs, s :: ss, U, hfun, happ, halign, hzip, hfuelL => by
      have ⟨hmatch, hzip'⟩ := idxSrcZip_cons hzip
      simp only [idxSrcAlignGo] at halign
      cases happR : applyTel
          (recPrefix w.preMajor w.nparams w.nMinors ++ pre)
          (instantiateLevels w.ls w.recMember.mtype) with
      | none =>
          simp only [happR] at halign
          nomatch halign
      | some Ur =>
          have hU : U = Ur := by
            have : some U = some Ur := happ.symm.trans happR
            injection this
          subst hU
          match U with
          | .pi Ar Br =>
              simp only [happR] at halign
              cases hty : idxSrcTy w.familyRef E
                  (instantiateLevels w.ls w.ctorMember.mtype)
                  (w.preMajor.take w.nparams ++ w.fields) x s with
              | none =>
                  simp only [hty] at halign
                  nomatch halign
              | some Ac =>
                  simp only [hty] at halign
                  have ⟨heq, hrest⟩ := bool_and_true halign
                  have hAcAr : Ac = Ar := of_decide_eq_true heq
                  have hxAc := hasTy_of_idxSrc w.familyRef
                    (instantiateLevels w.ls w.ctorMember.mtype)
                    (w.preMajor.take w.nparams ++ w.fields) hctor
                    x s Ac hmatch hty hfuelL.1
                  have hxAr : HasTy E n Γ x Ar := by
                    rw [hAcAr] at hxAc
                    exact hxAc
                  have hassoc :
                      recPrefix w.preMajor w.nparams w.nMinors ++
                        pre ++ [x] =
                      recPrefix w.preMajor w.nparams w.nMinors ++
                        (pre ++ [x]) :=
                    List.append_assoc _ _ _
                  have hfapp : HasTy E n Γ
                      (foldApps (.const w.recRef w.ls)
                        (recPrefix w.preMajor w.nparams w.nMinors ++
                          (pre ++ [x])))
                      (instantiate0 x Br) := by
                    have hfa := foldApps_append
                      (.const w.recRef w.ls)
                      (recPrefix w.preMajor w.nparams w.nMinors ++ pre)
                      [x]
                    rw [← hassoc, hfa, foldApps]
                    exact .app _ _ _ _ _ hfun hxAr
                  have happ' :
                      applyTel (recPrefix w.preMajor w.nparams
                          w.nMinors ++ (pre ++ [x]))
                        (instantiateLevels w.ls w.recMember.mtype) =
                        some (instantiate0 x Br) := by
                    have hsnoc := applyTel_snoc x
                      (recPrefix w.preMajor w.nparams w.nMinors ++ pre)
                      (instantiateLevels w.ls w.recMember.mtype) happR
                    rw [← hassoc]
                    exact hsnoc
                  have ⟨V, ht⟩ := telArgs_idxGo hpci hE hΓ w hT
                    hctor (pre ++ [x]) xs ss hfapp happ' hrest hzip' hfuelL.2
                  exact ⟨V, TelArgs.cons hxAr ht⟩
          | .bvar _ =>
              simp only [happR] at halign; nomatch halign
          | .sort _ =>
              simp only [happR] at halign; nomatch halign
          | .const _ _ =>
              simp only [happR] at halign; nomatch halign
          | .app _ _ =>
              simp only [happR] at halign; nomatch halign
          | .lam _ _ =>
              simp only [happR] at halign; nomatch halign
          | .letE _ _ _ =>
              simp only [happR] at halign; nomatch halign
          | .lit _ =>
              simp only [happR] at halign; nomatch halign
  | pre, [], _ :: _, U, hfun, happ, halign, hzip, hfuelL => by
      simp only [idxSrcZip] at hzip; nomatch hzip
  | pre, _ :: _, [], U, hfun, happ, halign, hzip, hfuelL => by
      simp only [idxSrcZip] at hzip; nomatch hzip

/-- TelArgs of an arbitrary index list at the recursor remainder after
`recPrefix`. `idxSrcAlign` says each source's type is the recursor
domain; `idxSrcZip` says the source matches the index term. -/
def telArgs_familyIdx {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    {Uctor : Expr Nat}
    (hctor : TelArgs E n Γ (w.preMajor.take w.nparams ++ w.fields)
      (instantiateLevels w.ls w.ctorMember.mtype) Uctor)
    (idx : List (Expr Nat)) (ss : List IdxSrc)
    (halign : idxSrcAlign w.familyRef E
      (instantiateLevels w.ls w.recMember.mtype)
      (instantiateLevels w.ls w.ctorMember.mtype)
      (recPrefix w.preMajor w.nparams w.nMinors)
      (w.preMajor.take w.nparams ++ w.fields) idx ss = true)
    (hzip : idxSrcZip w.familyRef
      (w.preMajor.take w.nparams ++ w.fields) idx ss = true)
    (hfuelL : IdxSrcFuelList n idx ss) :
    Σ' (U V : Expr Nat),
      (applyTel (recPrefix w.preMajor w.nparams w.nMinors)
        (instantiateLevels w.ls w.recMember.mtype) = some U) ×'
      HasTy E n Γ
        (foldApps (.const w.recRef w.ls)
          (recPrefix w.preMajor w.nparams w.nMinors)) U ×'
      TelArgs E n Γ idx U V := by
  have ⟨U, happ, hty⟩ := typed_recPrefix hpci hE hΓ w hT
  have hnil :
      recPrefix w.preMajor w.nparams w.nMinors ++ [] =
        recPrefix w.preMajor w.nparams w.nMinors :=
    List.append_nil _
  have hty' : HasTy E n Γ
      (foldApps (.const w.recRef w.ls)
        (recPrefix w.preMajor w.nparams w.nMinors ++ [])) U := by
    rw [hnil]; exact hty
  have happ' : applyTel
      (recPrefix w.preMajor w.nparams w.nMinors ++ [])
      (instantiateLevels w.ls w.recMember.mtype) = some U := by
    rw [hnil]; exact happ
  have ⟨V, htel⟩ := telArgs_idxGo hpci hE hΓ w hT hctor [] idx ss
    hty' happ' (by
      simp only [idxSrcAlign] at halign
      exact halign) hzip hfuelL
  exact ⟨U, V, happ, hty, htel⟩

/-- Recursor prefix plus field indices given composable sources. -/
def hasTy_recPrefix_idx_of_align {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    {A : Expr Nat} {Uctor : Expr Nat}
    (hctor : TelArgs E n Γ (w.preMajor.take w.nparams ++ w.fields)
      (instantiateLevels w.ls w.ctorMember.mtype) Uctor)
    (ss : List IdxSrc)
    (halign : idxSrcAlign w.familyRef E
      (instantiateLevels w.ls w.recMember.mtype)
      (instantiateLevels w.ls w.ctorMember.mtype)
      (recPrefix w.preMajor w.nparams w.nMinors)
      (w.preMajor.take w.nparams ++ w.fields)
      (familyIdx w.nparams A) ss = true)
    (hzip : idxSrcZip w.familyRef
      (w.preMajor.take w.nparams ++ w.fields)
      (familyIdx w.nparams A) ss = true)
    (hfuelL : IdxSrcFuelList n (familyIdx w.nparams A) ss) :
    Σ' (V : Expr Nat),
      HasTy E n Γ
        (foldApps (.const w.recRef w.ls)
          (recPrefix w.preMajor w.nparams w.nMinors ++
            familyIdx w.nparams A)) V ×'
      (applyTel
        (recPrefix w.preMajor w.nparams w.nMinors ++
          familyIdx w.nparams A)
        (instantiateLevels w.ls w.recMember.mtype) = some V) := by
  have ⟨U, V, happ, hty, htel⟩ :=
    telArgs_familyIdx hpci hE hΓ w hT hctor
      (familyIdx w.nparams A) ss halign hzip hfuelL
  have htyV := hasTy_recPrefix_idx hty htel
  have happIdx := telArgs_applyTel htel
  have happAll := applyTel_append_of
    (recPrefix w.preMajor w.nparams w.nMinors)
    (familyIdx w.nparams A) happ happIdx
  exact ⟨V, htyV, happAll⟩

/-- 05 §14 IH typing for arbitrary field indices (Vec.cons: `n` vs
`n+1`). Last-Π is `I params idx` via `applyTel_recPrefix_idx_last`.
The index TelArgs come from `IdxSrc`, not from `Afound = A` and not
from the whole index equaling one field. -/
def hasTy_recCallField_of_align {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    {f A B : Expr Nat} {ks : List RecKind} {fs : List (Expr Nat)}
    {Uctor : Expr Nat}
    (hx : HasTy E n Γ f A)
    (hsp : directRecFamilySpineExact w.familyRef
      (w.ls.take w.famMember.arity) w.nparams
      (w.preMajor.take w.nparams) (.directRec :: ks)
      (.pi A B) (f :: fs) = true)
    (hlen : (familyIdx w.nparams A).length = w.nindices)
    (hctor : TelArgs E n Γ (w.preMajor.take w.nparams ++ w.fields)
      (instantiateLevels w.ls w.ctorMember.mtype) Uctor)
    (ss : List IdxSrc)
    (halign : idxSrcAlign w.familyRef E
      (instantiateLevels w.ls w.recMember.mtype)
      (instantiateLevels w.ls w.ctorMember.mtype)
      (recPrefix w.preMajor w.nparams w.nMinors)
      (w.preMajor.take w.nparams ++ w.fields)
      (familyIdx w.nparams A) ss = true)
    (hzip : idxSrcZip w.familyRef
      (w.preMajor.take w.nparams ++ w.fields)
      (familyIdx w.nparams A) ss = true)
    (hfuelL : IdxSrcFuelList n (familyIdx w.nparams A) ss) :
    HasTy E n Γ
      (recCallField (.const w.recRef w.ls) w.preMajor
        w.nparams w.nMinors f A)
      (.app (foldApps (recMotiveOf w) (familyIdx w.nparams A)) f) := by
  have ⟨_args, _hspine, hAfam⟩ := directRec_eq_family hsp
  have ⟨Bih, hlast⟩ :=
    applyTel_recPrefix_idx_last w (witness_famArity_le_ls hE w hT)
      (familyIdx w.nparams A) hlen
  rw [← hAfam] at hlast
  have ⟨V, htyV, happAll⟩ :=
    hasTy_recPrefix_idx_of_align hpci hE hΓ w hT hctor ss
      halign hzip hfuelL
  have hVU : V = Expr.pi A Bih := by
    have h : some V = some (Expr.pi A Bih) := happAll.symm.trans hlast
    injection h
  subst hVU
  have ⟨A_syn, hrecLast⟩ :=
    recLastPi_idx_inst w w.ls (familyIdx w.nparams A) hlen
  have hη := instTel_hrecBody_idx w (familyIdx w.nparams A) hlen
    (recMotiveOf_spec w)
  have hBih : Bih =
      Expr.app (lift 0 1 (foldApps (recMotiveOf w) (familyIdx w.nparams A)))
        (.bvar 0) := by
    have h : some (Expr.pi A Bih) =
        some (Expr.pi A_syn
          (instTel (recPrefix w.preMajor w.nparams w.nMinors ++
            familyIdx w.nparams A) w.recBody)) :=
      hlast.symm.trans hrecLast
    injection h with hπ
    injection hπ with _hA hbody
    rw [hbody, hη]
  exact hasTy_recCallField hpci hE hΓ w hT hx htyV hlast hBih

/-- All-plain kinds: no IH insertion. DirectRec remainder is
`hasTy_recPrefix_idx` (field indices from the ctor spine, 05 §8).

00 §19.2 erratum 5: `minorTel` no longer takes a pre-applied redex-scope
`F`; its conclusion reads the rewritten result indices off the walk's
own telescope, so the endpoint is `M (familyIdx nparams U) (ctor fs)`
where `U` is the telescope's own endpoint (`happ`). `hres` is the
base-case `familyIdx` totality guard (M-001) that `minorTel`'s
`instantiate` transport now needs. -/
def telArgs_minor_plain {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (w : IotaWitness E)
    (M ctorAcc : Expr Nat)
    (ks : List RecKind) (Ttel : Expr Nat) (fs : List (Expr Nat))
    (hplain : kinds_all_plain ks = true)
    (htel : isPiTel ks.length Ttel = true)
    (hres : resultConstHead ks Ttel = true)
    (hlen : ks.length = fs.length)
    {U : Expr Nat}
    (happ : applyTel fs Ttel = some U)
    (hfs : TelArgs E n Γ fs Ttel U) :
    TelArgs E n Γ
      (rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
        fs ks Ttel)
      (minorTel M w.nparams ctorAcc ks Ttel)
      (.app (foldApps M (familyIdx w.nparams U)) (foldApps ctorAcc fs)) :=
  match ks, Ttel, fs with
  | [], _, [] => by
      simp only [applyTel] at happ
      injection happ with hU
      subst hU
      simp only [rhsArgs, minorTel, foldApps]
      exact TelArgs.nil
  | [], _, _ :: _ => by
      simp only [List.length_nil, List.length_cons] at hlen
      cases hlen
  | .plain :: ks, .pi A B, [] => by
      simp only [List.length_cons, List.length_nil] at hlen
      cases hlen
  | .plain :: ks, .pi A B, f :: fs => by
      simp only [kinds_all_plain] at hplain
      simp only [isPiTel, List.length_cons] at htel hlen
      simp only [resultConstHead] at hres
      simp only [applyTel] at happ
      have ⟨A', B', hTeq, hx, ht⟩ := telArgs_cons_inv hfs
      injection hTeq with hA hB
      subst hA
      subst hB
      have hlen' : ks.length = fs.length := Nat.succ.inj hlen
      have htel' := isPiTel_instantiate 0 f ks.length B htel
      have hres' := resultConstHead_instantiate 0 f ks B htel hres
      have hrest :=
        telArgs_minor_plain w M (.app ctorAcc f) ks (instantiate0 f B) fs
          hplain htel' hres' hlen' happ ht
      have hinst := instantiate0_minorTel_plain M w.nparams ctorAcc
        f ks B htel (directRecConstHead_of_plain ks B hplain) hres
      simp only [rhsArgs, minorTel]
      exact TelArgs.cons hx (by
        rw [hinst]
        exact hrest)
  | .plain :: _, .bvar _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: _, .sort _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: _, .const _ _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: _, .app _ _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: _, .lam _ _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: _, .letE _ _ _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: _, .lit _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: _, _, _ => by
      simp only [kinds_all_plain] at hplain
      nomatch hplain

/-- n-ary TelArgs of `rhsArgs` at `mdom` for all-plain constructors
(no IH). DirectRec needs `hasTy_recPrefix_idx`.

00 §19.2 erratum 5: `minorTel` ends at `M (familyIdx nparams U)
(ctor fields)` for the telescope's OWN endpoint `U`.

M-003 (00 §19.2 ERRATUM 6, O-3 RIDER). Premise dropped and CONCLUSION
restated, exactly as `telArgs_nil_of_hmin`:
    old:  (hic : IndexCoherent w) → TelArgs … (.app (foldApps ty.motive
            (w.preMajor.drop (w.nparams + 1 + w.nMinors))) (ctorMajorRec w))
    new:  Σ' U, (applyTel w.fields w.ctorAfterParams = some U) ×'
            TelArgs … (.app (foldApps ty.motive (familyIdx w.nparams U))
              (ctorMajorRec w))
`applyTel` is a function and `applyTel_rhsArgs_minorTel` computes the
endpoint, so the conclusion is pinned there; the return of `U` with its
equation is what lets the consumer feed `IndexCoherentConv`'s ∀-form
the `U` it already holds. -/
def telArgs_of_minorTel_plain {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (hfaci : FamAppConvInj E n)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    (hplain : kinds_all_plain w.kinds = true) :
    Σ' (U : Expr Nat),
      (applyTel w.fields w.ctorAfterParams = some U) ×'
      TelArgs E n Γ
        (rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
          w.fields w.kinds w.ctorAfterParams)
        ty.mdom
        (.app (foldApps ty.motive
          (familyIdx w.nparams U))
          (ctorMajorRec w)) := by
  have ⟨U, hfields⟩ := telArgs_fields_rec hpci hE hΓ hfaci w ty hT
  have happ : applyTel w.fields w.ctorAfterParams = some U :=
    telArgs_applyTel hfields
  have hwalk :=
    telArgs_minor_plain w ty.motive
      (foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
        (w.preMajor.take w.nparams))
      w.kinds w.ctorAfterParams w.fields hplain w.hctorTel w.hresTel
      w.hlen happ hfields
  have hC : foldApps
      (foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
        (w.preMajor.take w.nparams)) w.fields = ctorMajorRec w :=
    (foldApps_append (.const w.ctorRef (w.ls.take w.famMember.arity))
      (w.preMajor.take w.nparams) w.fields).symm
  rw [hC] at hwalk
  rw [ty.hminTel]
  exact ⟨U, happ, hwalk⟩

def iotaPreserve_plain {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (hfaci : FamAppConvInj E n)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hplain : kinds_all_plain w.kinds = true)
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    HasTy E n Γ (iotaRhsOf w) T :=
  let ⟨U, hU, ht⟩ :=
    telArgs_of_minorTel_plain hpci hE hΓ hfaci w ty hT hplain
  iotaPreserve_of_telArgs hpci hE hΓ w ty hT
    (conv_ctorMajorRec hpci hE hΓ hfaci w ty hT)
    (hasTy_minor_mdom hpci hE hΓ w ty hT)
    (iotaLhs_ctorIdx_conv hpci hE hΓ hfaci w ty hT U hU)
    ht

/-- n-ary TelArgs of `rhsArgs` at `minorTel`, including DirectRec IHs
(05 §14 field indices). `recIdxTySrcWalk` aligns each index source
with the recursor domain. A compound index is an `IdxSrc.app`.
`recIdxFromSpineWalk` is a separate conjunct, not this evidence.

00 §19.2 erratum 5: no pre-applied `F`; the conclusion's motive
arguments are read off the telescope's own endpoint `U` (`happ`), and
`hres` is the base-case `familyIdx` totality guard (M-001). 00 §19.2
erratum 4: `hspine`'s level list is the recursor's TRUNCATED to the
family arity, so it agrees with `applyTel_recPrefix_idx_last`'s head
through `directRec_eq_family`. -/
def telArgs_minor {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (w : IotaWitness E) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T)
    {Uctor : Expr Nat}
    (hctor : TelArgs E n Γ (w.preMajor.take w.nparams ++ w.fields)
      (instantiateLevels w.ls w.ctorMember.mtype) Uctor)
    (M ctorAcc : Expr Nat)
    (hM : M = recMotiveOf w)
    (ks : List RecKind) (Ttel : Expr Nat) (fs : List (Expr Nat))
    (htel : isPiTel ks.length Ttel = true)
    (hfam : directRecConstHead ks Ttel = true)
    (hres : resultConstHead ks Ttel = true)
    (hspine : directRecFamilySpineExact w.familyRef
      (w.ls.take w.famMember.arity) w.nparams
      (w.preMajor.take w.nparams) ks Ttel fs = true)
    (hwalk : recIdxFromSpineWalk w.familyRef w.nparams w.nindices
      (w.preMajor.take w.nparams ++ w.fields) ks Ttel fs = true)
    (pss : List (List IdxSrc))
    (hpos : recIdxSrcWalk w.familyRef w.nparams
      (w.preMajor.take w.nparams ++ w.fields) ks Ttel fs pss = true)
    (halignW : recIdxTySrcWalk w.familyRef E
      (instantiateLevels w.ls w.recMember.mtype)
      (instantiateLevels w.ls w.ctorMember.mtype)
      w.nparams (recPrefix w.preMajor w.nparams w.nMinors)
      (w.preMajor.take w.nparams ++ w.fields) ks Ttel fs pss = true)
    (hfuelW : recIdxSrcFuelWalk n w.nparams ks Ttel fs pss)
    (hlen : ks.length = fs.length)
    {U : Expr Nat}
    (happ : applyTel fs Ttel = some U)
    (hfs : TelArgs E n Γ fs Ttel U) :
    TelArgs E n Γ
      (rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
        fs ks Ttel)
      (minorTel M w.nparams ctorAcc ks Ttel)
      (.app (foldApps M (familyIdx w.nparams U)) (foldApps ctorAcc fs)) :=
  match ks, Ttel, fs with
  | [], _, [] => by
      simp only [applyTel] at happ
      injection happ with hU
      subst hU
      simp only [rhsArgs, minorTel, foldApps]
      exact TelArgs.nil
  | [], _, _ :: _ => by
      simp only [List.length_nil, List.length_cons] at hlen
      cases hlen
  | .plain :: ks, .pi A B, [] => by
      simp only [List.length_cons, List.length_nil] at hlen
      cases hlen
  | .directRec :: ks, .pi A B, [] => by
      simp only [List.length_cons, List.length_nil] at hlen
      cases hlen
  | .plain :: ks, .pi A B, f :: fs => by
      simp only [isPiTel, List.length_cons] at htel hlen
      simp only [directRecConstHead] at hfam
      simp only [resultConstHead] at hres
      simp only [applyTel] at happ
      simp only [directRecFamilySpineExact] at hspine
      simp only [recIdxFromSpineWalk] at hwalk
      cases pss with
      | nil => simp only [recIdxSrcWalk] at hpos; nomatch hpos
      | cons src pss =>
          cases src with
          | nil =>
              simp only [recIdxSrcWalk] at hpos
              simp only [recIdxTySrcWalk] at halignW
              simp only [recIdxSrcFuelWalk] at hfuelW
              have ⟨A', B', hTeq, hx, ht⟩ := telArgs_cons_inv hfs
              injection hTeq with hA hB
              subst hA
              subst hB
              have hlen' : ks.length = fs.length := Nat.succ.inj hlen
              have htel' := isPiTel_instantiate 0 f ks.length B htel
              have hfam' :=
                directRecConstHead_instantiate 0 f ks B htel hfam
              have hres' := resultConstHead_instantiate 0 f ks B htel hres
              have hrest :=
                telArgs_minor hpci hE hΓ w hT hctor
                  M (.app ctorAcc f) hM ks (instantiate0 f B) fs
                  htel' hfam' hres' hspine hwalk pss hpos halignW hfuelW
                  hlen' happ ht
              have hinst := instantiate0_minorTel_plain M w.nparams
                ctorAcc f ks B htel hfam hres
              simp only [rhsArgs, minorTel]
              exact TelArgs.cons hx (by
                rw [hinst]
                exact hrest)
          | cons _ _ =>
              simp only [recIdxSrcWalk] at hpos; nomatch hpos
  | .directRec :: ks, .pi A B, f :: fs => by
      simp only [isPiTel, List.length_cons] at htel hlen
      have ⟨A', B', hTeq, hx, ht⟩ := telArgs_cons_inv hfs
      injection hTeq with hA hB
      subst hA
      subst hB
      have hlen' : ks.length = fs.length := Nat.succ.inj hlen
      have ⟨hidxlen, _, hwalk'⟩ := recIdxFromSpineWalk_directRec hwalk
      have hspine' := directRecFamilySpineExact_directRec hspine
      simp only [directRecConstHead] at hfam
      simp only [resultConstHead] at hres
      simp only [applyTel] at happ
      have ⟨_, hfamB⟩ := bool_and_true hfam
      have htel' := isPiTel_instantiate 0 f ks.length B htel
      have hfam' := directRecConstHead_instantiate 0 f ks B htel hfamB
      have hres' := resultConstHead_instantiate 0 f ks B htel hres
      cases pss with
      | nil => simp only [recIdxSrcWalk] at hpos; nomatch hpos
      | cons src pss =>
          have ⟨hzip, hpos'⟩ := recIdxSrcWalk_directRec hpos
          have ⟨halign, halignW'⟩ := recIdxTySrcWalk_directRec halignW
          simp only [recIdxSrcFuelWalk] at hfuelW
          have hih := hasTy_recCallField_of_align hpci hE hΓ w hT
            hx hspine hidxlen hctor src halign hzip hfuelW.1
          have hih' : HasTy E n Γ
              (recCallField (.const w.recRef w.ls) w.preMajor
                w.nparams w.nMinors f A)
              (instantiate0 f
                (.app (lift 0 1 (foldApps M (familyIdx w.nparams A)))
                  (.bvar 0))) := by
            rw [instantiate0_eta, hM]
            exact hih
          have hrest :=
            telArgs_minor hpci hE hΓ w hT hctor
              M (.app ctorAcc f) hM ks (instantiate0 f B) fs
              htel' hfam' hres' hspine' hwalk' pss hpos' halignW' hfuelW.2
              hlen' happ ht
          have hinst := instantiate0_minorTel_directRec M w.nparams
            ctorAcc f (recCallField (.const w.recRef w.ls) w.preMajor
              w.nparams w.nMinors f A)
            ks B htel hfamB hres
          simp only [rhsArgs, minorTel]
          exact TelArgs.cons hx (TelArgs.cons hih' (by
            rw [hinst]
            exact hrest))
  | .plain :: _, .bvar _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: _, .sort _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: _, .const _ _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: _, .app _ _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: _, .lam _ _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: _, .letE _ _ _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .plain :: _, .lit _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: _, .bvar _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: _, .sort _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: _, .const _ _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: _, .app _ _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: _, .lam _ _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: _, .letE _ _ _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel
  | .directRec :: _, .lit _, _ => by
      simp only [isPiTel, List.length_cons] at htel; nomatch htel

/-- n-ary TelArgs of `rhsArgs` at `mdom` given index-domain alignment.
Conclusion restated by 00 §19.2 erratum 6 exactly as
`telArgs_of_minorTel_plain`'s (see there for why the endpoint is pinned
and why `U` travels with its `applyTel` equation).

M-003 (00 §19.2 ERRATUM 6, O-3 RIDER):
    old:  (hic : IndexCoherent w) → TelArgs … (.app (foldApps ty.motive
            (w.preMajor.drop (w.nparams + 1 + w.nMinors))) (ctorMajorRec w))
    new:  Σ' U, (applyTel w.fields w.ctorAfterParams = some U) ×'
            TelArgs … (.app (foldApps ty.motive (familyIdx w.nparams U))
              (ctorMajorRec w)) -/
def telArgs_of_minorTel {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (hfaci : FamAppConvInj E n)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    Σ' (U : Expr Nat),
      (applyTel w.fields w.ctorAfterParams = some U) ×'
      TelArgs E n Γ
        (rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
          w.fields w.kinds w.ctorAfterParams)
        ty.mdom
        (.app (foldApps ty.motive
          (familyIdx w.nparams U))
          (ctorMajorRec w)) := by
  have ⟨_Uctor, hctor⟩ := telArgs_recParamsFields hpci hE hΓ hfaci w ty hT
  have ⟨U, hfields⟩ := telArgs_fields_rec hpci hE hΓ hfaci w ty hT
  have happ : applyTel w.fields w.ctorAfterParams = some U :=
    telArgs_applyTel hfields
  have hwalk :=
    telArgs_minor hpci hE hΓ w hT hctor
      ty.motive
      (foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
        (w.preMajor.take w.nparams))
        (Option.some.inj (ty.hmotive.symm.trans (recMotiveOf_spec w)))
      w.kinds w.ctorAfterParams w.fields
      w.hctorTel
      w.hfamTel w.hresTel ty.hfamSpineExact ty.hidxWalk ty.idxPositions
      ty.hidxPos ty.hidxTy
      (ty.hidxFuel n (hasTy_iotaLhs_rawConstOK w hT)) w.hlen happ hfields
  have hC : foldApps
      (foldApps (.const w.ctorRef (w.ls.take w.famMember.arity))
        (w.preMajor.take w.nparams)) w.fields = ctorMajorRec w :=
    (foldApps_append (.const w.ctorRef (w.ls.take w.famMember.arity))
      (w.preMajor.take w.nparams) w.fields).symm
  rw [hC] at hwalk
  rw [ty.hminTel]
  exact ⟨U, happ, hwalk⟩

/-- The join point (00 §19.2 erratum 6): the telescope produces the
endpoint `U` with its `applyTel` equation, and `iotaLhs_ctorIdx_conv`
delivers the index `ConvArgs` AT THAT SAME `U` — which is the concrete
reason `IndexCoherentConv` quantifies over `U` under `applyTel`'s
equation instead of packaging it in a `Σ'`.

M-003 (00 §19.2 ERRATUM 6 DISCHARGE, O-2). Premise deleted:
    old:  … (w) (ty) (hic : IndexCoherent w) {T} (hT)
    new:  … (w) (ty) {T} (hT) -/
def iotaPreserve_of_align {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (hfaci : FamAppConvInj E n)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    HasTy E n Γ (iotaRhsOf w) T :=
  let ⟨U, hU, ht⟩ := telArgs_of_minorTel hpci hE hΓ hfaci w ty hT
  iotaPreserve_of_telArgs hpci hE hΓ w ty hT
    (conv_ctorMajorRec hpci hE hΓ hfaci w ty hT)
    (hasTy_minor_mdom hpci hE hΓ w ty hT)
    (iotaLhs_ctorIdx_conv hpci hE hΓ hfaci w ty hT U hU)
    ht

/-- n-ary IotaPreserve when the family has no indices (`List.cons`,
`Nat.succ`). `familyIdx = []`, so `idxTyAlign` is trivial. Vec.cons
(`n` vs `n+1`) still uses `iotaPreserve_of_align`.

M-003 (00 §19.2 ERRATUM 6 DISCHARGE, O-2). Premise deleted:
    old:  … (w) (ty) (hic : IndexCoherent w) {T} (_hn) (hT)
    new:  … (w) (ty) {T} (_hn) (hT)
The old docstring recorded why `hic` was PASSED THROUGH rather than
discharged here: at `nindices = 0` the right-hand side
`preMajor.drop (nparams+1+nMinors)` is `[]` only PROPOSITIONALLY and
the left-hand side is not reducible without the constructor's result
shape, so the syntactic equation was not `rfl`-dischargeable in place —
"deriving it would need `hctorResShape` / `ctorSpine_famApp` to pin the
result spine's index count". That is precisely what erratum 6's
discharge does, at every `nindices`, at the conversion layer; the
special case therefore needs no argument of its own, and `_hn` is now
unused by the proof. -/
def iotaPreserve_nindices_zero {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hpci : PiConvInj E n)
    (hE : EnvWf E n)
    (hΓ : CtxWf E n Γ)
    (hfaci : FamAppConvInj E n)
    (w : IotaWitness E) (ty : IotaTyping E w) {T : Expr Nat}
    (_hn : w.nindices = 0)
    (hT : HasTy E n Γ (iotaLhsOf w) T) :
    HasTy E n Γ (iotaRhsOf w) T :=
  iotaPreserve_of_align hpci hE hΓ hfaci w ty hT

/-- F-05a: IotaPreserve is a theorem over DerivedIota + IotaTyping +
`CtxWf`. Footprint (M-003): `PiConvInj`, `FamAppConvInj` (§19.2 row,
owner 02 conv meta — the free `ctorParams` reach their recursor-side
copy only through the redex's own typing), `EnvWf`, `CtxWf`. NO
per-redex premise remains.

00 §20.6 DISCHARGE (O-2): `LevelCoherent` is gone from this list. With
`HasTy.const` level-instantiated, the redex's own typing forces the
major's constructor universes, and `iotaLhs_ctorParams_levels_conv`
reads them out on the same `FamAppConvInj` row that already carried the
argument half.

00 §19.2 ERRATUM 6 DISCHARGE (O-2): `IndexCoherent` is gone too. It was
stated as a syntactic EQUATION, strictly stronger than the redex's
typing delivers, so this statement was VACUOUS at every redex whose
major indices are convertible without being syntactically equal —
the normal case for any family whose indices contain a redex. Restated
as `IndexCoherentConv` it is derived by `iotaLhs_ctorIdx_conv` off the
SAME `FamAppConvInj` row again. That row is now TRIPLY load-bearing per
redex — parameters, levels, indices — all three reading one
`iotaLhs_famApp_conv` pack; no new obligation, and if `FamAppConvInj`
is later found to need conditioning beyond `EnvWf` + `CtxWf`, three
chains move at once. -/
def iotaPreserve {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n)
    (hfaci : FamAppConvInj E n)
    (hE : EnvWf E n) :
    IotaPreserve E n :=
  fun Γ lhs rhs T hι =>
    match hι with
    | .of w =>
        fun ty hΓ hT =>
          iotaPreserve_of_align hpci hE hΓ hfaci w ty hT

/-- O-2: IotaPreserve deleted from the DT-010/011 premises
(`iotaPreserve` discharges it). O-3 (00 §20.5): DT-010 gains
`FamAppConvInj`; `CtxWf` was already carried. 00 §20.6 DISCHARGE
(O-2): the per-step `StepLevelCoherent` premise is DELETED — the fact
is now derived.

M-003 (00 §19.2 ERRATUM 6 DISCHARGE, O-2). Premise deleted:
    old:  … (hs : Step E n Γ e e') (hic : StepIndexCoherent hs)
    new:  … (hs : Step E n Γ e e')
The per-step index premise carried the major's index slots as a
syntactic equation; it is now derived inside `iotaPreserve` at the
conversion layer (`iotaLhs_ctorIdx_conv`). This is the maturity content
of the flip: DT-010 becomes USABLE FOR THE FIRST TIME at redexes whose
indices are convertible without being syntactically equal — before the
flip it was, at every such redex, a statement with an unsatisfiable
premise. Strengthening: the conclusion is unchanged and one hypothesis
is gone. -/
theorem DT010_one_step_subject_reduction {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n)
    (hfaci : FamAppConvInj E n)
    (hE : EnvWf E n)
    {Γ : LCtx} (hΓ : CtxWf E n Γ)
    {e A e' : Expr Nat} (h : HasTy E n Γ e A) (hs : Step E n Γ e e') :
    ∃ B, Nonempty (HasTy E n Γ e' B) ∧ Nonempty (Conv E n Γ A B) :=
  let ⟨B, hty, hcv⟩ := oneStepSR hpci hE
    (iotaPreserve hpci hfaci hE) hΓ h hs
  ⟨B, ⟨hty⟩, ⟨hcv⟩⟩

-- ══ DELETED (00 §19.2 ERRATUM 6, O-2) ══
-- `StepsIndexCoherent` — the DT-011 chain premise "every `.iota` step
-- in the multi-step derivation is index-coherent". Its level sibling
-- `StepsLevelCoherent` went with 00 §20.6's discharge; this one goes
-- with erratum 6's. Both are now derived per redex inside
-- `iotaPreserve`, so the chain has nothing left to accumulate and
-- DT-011's induction carries no coherence argument at all.
--
-- Had the corrected Γ-dependent form been LANDED instead of
-- discharged, this recursion's `∧` would have had to become `×'`: a
-- `Prop` chain premise cannot feed the `Σ'`-valued `oneStepSR`. That
-- churn is what the same-patch discharge removes; the forms are
-- recorded in 00 §19.2 erratum 6 should the discharge ever be
-- unlanded.

/-- M-003 (00 §19.2 ERRATUM 6 DISCHARGE, O-2). Premise deleted:
    old:  … (hs : Steps E n Γ e e') (hic : StepsIndexCoherent hs)
    new:  … (hs : Steps E n Γ e e')
Same content as DT-010's note: the chain premise was a conjunction of
per-step syntactic equations, unsatisfiable exactly where the theorem
was wanted. Strengthening: the conclusion is unchanged and one
hypothesis is gone. -/
theorem DT011_multi_step_subject_reduction {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n)
    (hfaci : FamAppConvInj E n)
    (hE : EnvWf E n)
    {Γ : LCtx} (hΓ : CtxWf E n Γ)
    {e A e' : Expr Nat} (h : HasTy E n Γ e A) (hs : Steps E n Γ e e') :
    ∃ B, Nonempty (HasTy E n Γ e' B) ∧ Nonempty (Conv E n Γ A B) := by
  induction hs generalizing A with
  | refl _ => exact ⟨A, ⟨h⟩, ⟨.refl _ _⟩⟩
  | step a b c h1 h2 ih =>
      let ⟨B1, hty1, hcv1⟩ := oneStepSR hpci hE
        (iotaPreserve hpci hfaci hE) hΓ h h1
      have ⟨B2, ⟨hty2⟩, ⟨hcv2⟩⟩ := ih hty1
      exact ⟨B2, ⟨hty2⟩, ⟨.trans _ _ _ _ hcv1 hcv2⟩⟩

/- IotaPreserve discharged: `iotaPreserve` over all DerivedIota.
Positions (`idxPositions` / `hidxPos` / `hidxTy`) pin ctor/rec
index-domain alignment without `listIndexOf`. O-2: DT-010/011 drop
the IotaPreserve premise. Lit* remain 08. closure_claim stays 0. -/

/-- DT-012: type uniqueness by expression induction (00 §18.2 D-4).
Footprint (M-003): `PiConvInj` + `SortConvChar` (both
`EnvWf`+`CtxWf`-conditioned, O-3 / §19.2 erratum 2), plus the six
transport premises `convSubst`/`convSubstLet` consume. `hpci`/`hscc`
are applied at `hE` and at `hΓ`; the binder cases rebuild `CtxWf` for
the extended context from the inverted domain typing. -/
theorem DT012_type_uniqueness {E : ResolvedEnv} {n : Nat}
    (hpci : PiConvInj E n) (hscc : SortConvChar E n)
    (hE : EnvWf E n)
    {Γ : LCtx} (hΓ : CtxWf E n Γ)
    {e A B : Expr Nat} (hA : HasTy E n Γ e A) (hB : HasTy E n Γ e B) :
    Nonempty (Conv E n Γ A B) := by
  induction e generalizing Γ A B with
  | bvar i =>
      let ⟨A1, hlk1, hc1⟩ := hasTyBvarInv hA rfl
      let ⟨A2, hlk2, hc2⟩ := hasTyBvarInv hB rfl
      have hEq : some A1 = some A2 := hlk1.symm.trans hlk2
      injection hEq with hAeq
      subst hAeq
      exact ⟨.trans _ _ _ _ (.symm _ _ _ hc1) hc2⟩
  | sort l =>
      exact ⟨.trans _ _ _ _ (.symm _ _ _ (hasTySortInv hA rfl))
        (hasTySortInv hB rfl)⟩
  | const r ls =>
      let ⟨m1, hres1, _hlen1, hc1⟩ := hasTyConstInv hA rfl
      let ⟨m2, hres2, _hlen2, hc2⟩ := hasTyConstInv hB rfl
      have hEq : some m1 = some m2 := hres1.symm.trans hres2
      injection hEq with hmeq
      subst hmeq
      exact ⟨.trans _ _ _ _ (.symm _ _ _ hc1) hc2⟩
  | app f a ihf _iha =>
      let ⟨A1, B1, hf1, ha1, hc1⟩ := hasTyAppInv hA rfl
      let ⟨A2, B2, hf2, _ha2, hc2⟩ := hasTyAppInv hB rfl
      have ⟨hπ⟩ := ihf hΓ hf1 hf2
      let ⟨_hdom, hcod⟩ := hpci hE Γ A1 B1 A2 B2 hΓ hπ
      have hget : (LocalDecl.assumption A1 :: Γ)[(0:Nat)]? =
          some (.assumption A1) := List.getElem?_cons_zero
      have hvty : HasTy E n (substRemove a 0 (LocalDecl.assumption A1 :: Γ))
          (lift 0 0 a) (lift 0 0 A1) := by
        rw [substRemove_zero_cons, lift_zero, lift_zero]
        exact ha1
      have hcod0 := convSubst (j := 0) hE
        a A1 hcod hget hvty
      rw [substRemove_zero_cons, lift_zero] at hcod0
      exact ⟨.trans _ _ _ _ (.symm _ _ _ hc1) (.trans _ _ _ _ hcod0 hc2)⟩
  | lam A0 body _ihA ihb =>
      let ⟨u0, B1, hA0ty, hbody1, hc1⟩ := hasTyLamInv hA rfl
      let ⟨_u', B2, _hAty', hbody2, hc2⟩ := hasTyLamInv hB rfl
      have ⟨hBconv⟩ := ihb (.assumption Γ A0 u0 hΓ hA0ty) hbody1 hbody2
      have hπ : Conv E n Γ (.pi A0 B1) (.pi A0 B2) :=
        .pi _ _ _ _ _ (.refl _ _) hBconv
      exact ⟨.trans _ _ _ _ (.symm _ _ _ hc1) (.trans _ _ _ _ hπ hc2)⟩
  | pi A0 B0 ihA ihB =>
      let ⟨u, v, hAty, hBty, hcA⟩ := hasTyPiInv hA rfl
      let ⟨u', v', hAty', hBty', hcB⟩ := hasTyPiInv hB rfl
      have hΓ' : CtxWf E n (LocalDecl.assumption A0 :: Γ) :=
        .assumption Γ A0 u hΓ hAty
      have ⟨hAu⟩ := ihA hΓ hAty hAty'
      have ⟨hBv⟩ := ihB hΓ' hBty hBty'
      have eu : eqN u u' := hscc hE Γ u u' hΓ hAu
      have ev : eqN v v' :=
        hscc hE (LocalDecl.assumption A0 :: Γ) v v' hΓ' hBv
      have eimax : eqN (.imax u v) (.imax u' v') := fun ρ => by
        simp only [eval]
        rw [eu ρ, ev ρ]
      exact ⟨.trans _ _ _ _ (.symm _ _ _ hcA)
        (.trans _ _ _ _ (.sorts _ _ _ eimax) hcB)⟩
  | letE A0 val body _ihA _ihv ihb =>
      let ⟨u0, B1, hA0ty, hv1, hb1, hc1⟩ := hasTyLetInv hA rfl
      let ⟨_u', B2, _hAty', _hv2, hb2, hc2⟩ := hasTyLetInv hB rfl
      have ⟨hBconv⟩ :=
        ihb (.letBinding Γ A0 u0 val hΓ hA0ty hv1) hb1 hb2
      have hget : (LocalDecl.letBinding A0 val :: Γ)[(0:Nat)]? =
          some (.letBinding A0 val) := List.getElem?_cons_zero
      have hvty : HasTy E n (substRemove val 0 (LocalDecl.letBinding A0 val :: Γ))
          (lift 0 0 val) (lift 0 0 A0) := by
        rw [substRemove_zero_cons, lift_zero, lift_zero]
        exact hv1
      have hcod0 := convSubstLet (j := 0) hE
        A0 val hBconv hget hvty
      rw [substRemove_zero_cons, lift_zero] at hcod0
      exact ⟨.trans _ _ _ _ (.symm _ _ _ hc1) (.trans _ _ _ _ hcod0 hc2)⟩
  | lit t =>
      let ⟨_Ta, hexpA, hcA⟩ := hasTyLitInv hA rfl
      let ⟨_Tb, hexpB, hcB⟩ := hasTyLitInv hB rfl
      exact ⟨.trans _ _ _ _ (.symm _ _ _ hcA)
        (.trans _ _ _ _ (uniqueTy_natExpand hpci hE hΓ t hexpA hexpB) hcB)⟩

end Rcic.Declarative
