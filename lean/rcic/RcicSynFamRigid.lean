import rcic.RcicSynSortRow
import rcic.RcicSynStarLift
import rcic.RcicInvertFamily

/-!
# Syntactic sortRow, step 4c — erased family-head rigidity

`research/rcic/sortrow/S4_IOTA_SPINE_CIRCULARITY.md` §5–6 (ChatGPT, spec #7322; this module
is its 4c obligation).

1. **`TableWF.rigid` does not imply that a family head has no rule.** `badFamilyRule f` —
   head `f`, `major := none`, nullary constant right-hand side `sort 0` — makes
   `[badFamilyRule f]` a well-formed table (`badFamilyTable_wf`) with a genuine root step
   `const f [] → sort 0` (`badFamily_croot`). `rigid` quantifies only over rules whose
   `major = some (d, m)`, so it is vacuous on this rule.
2. **The missing invariant is `NoHeadRule tbl f`** (`∀ ρ ∈ tbl, ρ.head ≠ f`). Under it an
   `EStep tbl`-star out of a family-headed erased spine `appN (const f ls) xs` stays a
   `const f ls`-headed spine of the same arity, pointwise (`rstar_eStep_appN_const_inv`):
   a β or η root step is refuted by the head shape (the spine head is a `const`, never a
   `lam`), and a `CRoot` on any prefix would need a rule with `head = f`, excluded by
   `NoHeadRule`. Only steps inside the arguments remain.
3. **Erased inversion** (`convE_appN_const_inv_wf`): for a well-formed table with no
   family-head rule, `ConvMod (EStep tbl) LvlEq` between two `const f` spines yields
   `eqNList ls ls'`, equal arities, and pointwise `ConvMod` on the arguments. The proof
   runs through `joinMod_of_convMod` (`eStep_strongSim`, `confluent_eStep_wf`), the §2
   preservation on both join sides, and `LvlEq` spine inversion — the same route as
   `convE_pi_inv_wf`.

Teeth: `not_rstar_spine_inv_without_noHeadRule` refuses the premise-free inversion under
`badFamilyRule`; `erased_conv_not_typed_row` refuses the wrong-accept consumer that reads
an erased spine row ≈-faithfully — on a real inversion input (a β step inside the sole
argument of two `const 0` spines under `NoHeadRule []`), where `convE_appN_const_inv_wf`
genuinely fires yet the promoted `LvlEq` argument row does not exist. The builder half
`built_no_family_rule` waits for the builder implementation and stays open — nothing
here discharges it. `closure_claim` stays 0.
-/

namespace List

/-- pointwise relation on two lists (absent from this toolchain's core `List`). -/
inductive Forall₂ {α : Type} (R : α → α → Prop) : List α → List α → Prop
  | nil : Forall₂ R [] []
  | cons {x x' : α} {xs xs' : List α} (h : R x x') (hs : Forall₂ R xs xs') :
      Forall₂ R (x :: xs) (x' :: xs')

end List

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `TableWF.rigid` does not imply `NoHeadRule` -/

/-- S4 §5's counterexample rule: a family-headed, major-less, nullary rule with a constant
    `sort 0` right-hand side. `rigid` never sees it because `major = none`. -/
def badFamilyRule (f : Nat) : CRule where
  head := f
  nargs := fun _ => 0
  major := none
  rhs := fun _ _ => .sort .zero

/-- the singleton bad table is well-formed — every `TableWF` field holds. -/
theorem badFamilyTable_wf (f : Nat) : TableWF [badFamilyRule f] where
  congr :=
    { rhs := by
        intro ρ hρ _ _ _ _ _ _
        simp only [List.mem_singleton] at hρ; subst hρ
        exact .sort (eqN_refl _)
      nargs := by
        intro ρ hρ _ _ _
        simp only [List.mem_singleton] at hρ; subst hρ; rfl
      marity := by
        intro ρ hρ _ _ hm
        simp only [List.mem_singleton] at hρ; subst hρ; cases hm }
  closed := by
    intro ρ hρ _ _
    simp only [List.mem_singleton] at hρ; subst hρ; trivial
  rigid := by
    intro ρ hρ _ _ hm
    simp only [List.mem_singleton] at hρ; subst hρ; cases hm
  bare_unique := by
    intro ρ hρ _ σ hσ _
    simp only [List.mem_singleton] at hρ hσ; subst hρ; subst hσ; rfl
  ctor_disjoint := by
    intro ρ hρ _ _ _ _ _ _ _ hm
    simp only [List.mem_singleton] at hρ; subst hρ; cases hm
  bare_nullary := by
    intro ρ hρ _ ls
    simp only [List.mem_singleton] at hρ; subst hρ; rfl

/-- the bad rule genuinely fires: `const f [] → sort 0` is a root step of the table. -/
theorem badFamily_croot (f : Nat) : CRoot [badFamilyRule f] (.const f []) (.sort .zero) :=
  .bare (List.mem_singleton_self _) rfl [] [] rfl

/-- S4 §6's invariant: no rule of the table is headed at `f`. -/
def NoHeadRule (tbl : List CRule) (f : Nat) : Prop := ∀ ρ ∈ tbl, ρ.head ≠ f

/-- the bad table violates it — its one rule is headed exactly at `f`. -/
theorem badFamily_not_noHeadRule (f : Nat) : ¬ NoHeadRule [badFamilyRule f] f :=
  fun h => h _ (List.mem_singleton_self _) rfl

/-- S4 §5 headline: a well-formed table need not have `NoHeadRule` — `rigid` alone cannot
    give it. -/
theorem rigid_not_noHeadRule :
    ∃ tbl : List CRule, TableWF tbl ∧ ∃ f : Nat, ¬ NoHeadRule tbl f :=
  ⟨[badFamilyRule 0], badFamilyTable_wf 0, 0, badFamily_not_noHeadRule 0⟩

/-! ## §2 star head/arity preservation under `NoHeadRule` -/

/-- a one-step map on list relations. -/
theorem OneStep.map {R S : ETm → ETm → Prop} (himp : ∀ {a b : ETm}, R a b → S a b) :
    {xs xs' : List ETm} → OneStep R xs xs' → OneStep S xs xs'
  | _, _, .head xs h => .head xs (himp h)
  | _, _, .tail x h => .tail x (OneStep.map himp h)

/-- pointwise `R*`. -/
theorem forall2_rstar_refl {R : ETm → ETm → Prop} (xs : List ETm) :
    List.Forall₂ (RStar R) xs xs := by
  induction xs with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (.refl _) ih

theorem forall2_rstar_trans {R : ETm → ETm → Prop} {xs ys zs : List ETm}
    (h1 : List.Forall₂ (RStar R) xs ys) :
    List.Forall₂ (RStar R) ys zs → List.Forall₂ (RStar R) xs zs := by
  induction h1 generalizing zs with
  | nil => intro h; cases h; exact .nil
  | cons hx _ ih =>
      intro h
      cases h with
      | cons hy hys => exact .cons (hx.trans' hy) (ih hys)

theorem OneStep.forall2_rstar {R : ETm → ETm → Prop} {xs xs' : List ETm}
    (h : OneStep R xs xs') : List.Forall₂ (RStar R) xs xs' := by
  induction h with
  | head xs h => exact .cons (.single h) (forall2_rstar_refl xs)
  | tail x _ ih => exact .cons (.refl _) ih

/-- S4 §6: one `EStep` out of a `const f`-headed spine is a step inside one argument —
    `NoHeadRule` kills the `CRoot`-on-a-prefix case, and β/η root steps are refuted by the
    `const` head shape. -/
theorem eStep_appN_const_inv {tbl : List CRule} {f : Nat} {ls : List Level}
    {xs : List ETm} {c : ETm} (hN : NoHeadRule tbl f)
    (h : EStep tbl (ETm.appN (.const f ls) xs) c) :
    ∃ xs', c = ETm.appN (.const f ls) xs' ∧ OneStep (EStep tbl) xs xs' := by
  cases h with
  | inl hr =>
      rcases rStep_split hr with hb | hc
      · obtain ⟨xs', rfl, h'⟩ := betaStep_appN_const_inv hb
        exact ⟨xs', rfl, h'.map (fun h => .inl (rStep_of_betaStep h))⟩
      · rcases cStep_appN_const_inv hc with ⟨xs', rfl, h'⟩ | ⟨ys, zs, b, rfl, hroot, rfl⟩
        · exact ⟨xs', rfl, h'.map (fun h => .inl (rStep_of_cStep h))⟩
        · obtain ⟨ρ, hρ, hhead, _⟩ := cRoot_inv hroot
          exact absurd hhead (hN ρ hρ)
  | inr he =>
      obtain ⟨xs', rfl, h'⟩ := etaStep_appN_const_inv he
      exact ⟨xs', rfl, h'.map (fun h => .inr h)⟩

/-- the star lift: a `const f`-headed spine reduces only inside its arguments, preserving
    head and arity, pointwise. -/
theorem rstar_eStep_appN_const_inv {tbl : List CRule} {f : Nat} {ls : List Level}
    {xs : List ETm} {t : ETm} (hN : NoHeadRule tbl f)
    (h : RStar (EStep tbl) (ETm.appN (.const f ls) xs) t) :
    ∃ xs', t = ETm.appN (.const f ls) xs' ∧ xs'.length = xs.length ∧
      List.Forall₂ (RStar (EStep tbl)) xs xs' := by
  generalize hs : ETm.appN (.const f ls) xs = s at h
  induction h generalizing xs with
  | refl =>
      subst hs
      exact ⟨xs, rfl, rfl, forall2_rstar_refl xs⟩
  | step h1 _ ih =>
      subst hs
      obtain ⟨xs₁, rfl, hone⟩ := eStep_appN_const_inv hN h1
      obtain ⟨xs', rfl, hl, hstar⟩ := ih rfl
      exact ⟨xs', rfl, hl.trans hone.length_eq,
        forall2_rstar_trans hone.forall2_rstar hstar⟩

/-! ## §3 erased inversion -/

/-- per-argument `ConvMod` from a `≈`-joined pair of argument lists. -/
theorem forall2_convE_of_joins {tbl : List CRule} :
    {xs xs₁ ys₁ ys : List ETm} → List.Forall₂ (RStar (EStep tbl)) xs xs₁ →
    LvlEqList xs₁ ys₁ → List.Forall₂ (RStar (EStep tbl)) ys ys₁ →
    List.Forall₂ (ConvMod (EStep tbl) LvlEq) xs ys := by
  intro xs xs₁ ys₁ ys hx
  induction hx generalizing ys₁ ys with
  | nil =>
      intro hq hy
      cases hq
      cases hy
      exact .nil
  | cons hx _ ih =>
      intro hq hy
      cases hq with
      | cons hql hqs =>
          cases hy with
          | cons hyr hys =>
              exact .cons ((convMod_of_rstar_fwd hx).trans
                ((ConvMod.eqv hql).trans (convMod_of_rstar_rev hyr))) (ih hqs hys)

theorem forall2_length_eq {R : ETm → ETm → Prop} {xs ys : List ETm}
    (h : List.Forall₂ R xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

/-- ERASED FAMILY INVERSION (S4 §6): under `NoHeadRule`, convertible `const f` spines have
    `=ₙ` level lists, equal arities, and pointwise-convertible arguments. Erased only —
    it is not `FamAppConvInj` (the typed row), which stays a separate obligation. -/
theorem convE_appN_const_inv_wf {tbl : List CRule} (hW : TableWF tbl) {f : Nat}
    (hN : NoHeadRule tbl f) {ls ls' : List Level} {xs ys : List ETm}
    (h : ConvMod (EStep tbl) LvlEq (ETm.appN (.const f ls) xs)
      (ETm.appN (.const f ls') ys)) :
    eqNList ls ls' ∧ xs.length = ys.length ∧
      List.Forall₂ (ConvMod (EStep tbl) LvlEq) xs ys := by
  obtain ⟨c, d, hc, hq, hd⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr) (confluent_eStep_wf hW) h
  obtain ⟨xs₁, rfl, hxl, hxs₁⟩ := rstar_eStep_appN_const_inv hN hc
  obtain ⟨ys₁, rfl, hyl, hys₁⟩ := rstar_eStep_appN_const_inv hN hd
  obtain ⟨f', xs', hdeq, hf, hxs'⟩ := lvlEq_appN_inv hq
  cases hf with
  | const _ hls =>
      obtain ⟨-, rfl, rfl⟩ := ETm.appN_const_inj hdeq
      exact ⟨hls, hxl.symm.trans (hxs'.length_eq.trans hyl),
        forall2_convE_of_joins hxs₁ hxs' hys₁⟩

/-! ## §4 teeth -/

/-- TOOTH 1 (S4 §5–6): the premise-free inversion is refused. Without `NoHeadRule`, the
    bad table steps `const f []` clean off its spine — every `xs'`-shaped conclusion is
    unreachable. -/
theorem badFamily_star_escapes (f : Nat) :
    RStar (EStep [badFamilyRule f]) (.const f []) (.sort .zero) ∧
      ¬ ∃ xs' : List ETm, ETm.sort .zero = ETm.appN (.const f []) xs' :=
  ⟨.single (.inl (.cr (badFamily_croot f))),
    fun ⟨xs', h⟩ => appN_const_ne_sort f [] xs' .zero h.symm⟩

theorem not_rstar_spine_inv_without_noHeadRule (f : Nat) :
    ¬ (∀ {t : ETm}, RStar (EStep [badFamilyRule f]) (.const f []) t →
        ∃ xs', t = ETm.appN (.const f []) xs') :=
  fun h => (badFamily_star_escapes f).2 (h (badFamily_star_escapes f).1)

/-- the empty table is well-formed — every `TableWF` field is vacuous. -/
theorem emptyTable_wf : TableWF [] where
  congr :=
    { rhs := by intro ρ hρ; exact absurd hρ (List.not_mem_nil _)
      nargs := by intro ρ hρ; exact absurd hρ (List.not_mem_nil _)
      marity := by intro ρ hρ; exact absurd hρ (List.not_mem_nil _) }
  closed := by intro ρ hρ; exact absurd hρ (List.not_mem_nil _)
  rigid := by intro ρ hρ; exact absurd hρ (List.not_mem_nil _)
  bare_unique := by intro ρ hρ; exact absurd hρ (List.not_mem_nil _)
  ctor_disjoint := by intro ρ hρ; exact absurd hρ (List.not_mem_nil _)
  bare_nullary := by intro ρ hρ; exact absurd hρ (List.not_mem_nil _)

/-- no rule of `[]` is headed anywhere — `NoHeadRule` holds vacuously. -/
theorem noHeadRule_empty (f : Nat) : NoHeadRule [] f :=
  fun ρ hρ => absurd hρ (List.not_mem_nil _)

/-- CONTROL INPUT (S4 §6): a genuine β step inside the sole argument of a `const 0`
    spine — `appN (const 0 []) [(λ.0) (const 9 [])] → appN (const 0 []) [const 9 []]`.
    The endpoints are two `const 0`-headed spines, so unlike `badFamilyRule`'s escape
    this IS an input to the erased inversion being protected. -/
theorem ctl_step :
    EStep []
      (ETm.appN (.const 0 []) [.app (.lam (.bvar 0)) (.const 9 [])])
      (ETm.appN (.const 0 []) [.const 9 []]) :=
  .inl (.appR _ (.beta _ _))

/-- the same input as a `ConvMod` — the premise shape of `convE_appN_const_inv_wf`. -/
theorem ctl_conv :
    ConvMod (EStep []) LvlEq
      (ETm.appN (.const 0 []) [.app (.lam (.bvar 0)) (.const 9 [])])
      (ETm.appN (.const 0 []) [.const 9 []]) :=
  .fwd ctl_step

/-- the protected inversion genuinely fires on the control input: all premises are
    inhabited, so `convE_appN_const_inv_wf` delivers its honest `ConvMod` row. -/
theorem ctl_erased_inversion_fires :
    eqNList ([] : List Level) [] ∧
      ([.app (.lam (.bvar 0)) (.const 9 [])] : List ETm).length =
        ([.const 9 []] : List ETm).length ∧
      List.Forall₂ (ConvMod (EStep []) LvlEq)
        [.app (.lam (.bvar 0)) (.const 9 [])] [.const 9 []] :=
  convE_appN_const_inv_wf emptyTable_wf (noHeadRule_empty 0) ctl_conv

/-- the exact boundary, on the same input: the argument pair is not `≈` — `LvlEq` is
    ctor-shape-respecting, and a β-redex is not a `const`. -/
theorem ctl_args_not_lvlEq :
    ¬ List.Forall₂ LvlEq
      [.app (.lam (.bvar 0)) (.const 9 [])] [.const 9 []] := by
  intro h; cases h with | cons h1 _ => cases h1

/-- WRONG-ACCEPT CONSUMER (S4 §6): the mutant that reads an erased `const f`-spine
    conversion — the input shape `convE_appN_const_inv_wf` is proved on — as the
    ≈-faithful row a `FamAppConvInj`-strength (typed) consumer needs (`ConvArgs`
    is ≈-faithful): the erased conclusion with its per-argument `ConvMod`
    promoted to `LvlEq`. -/
def ErasedAsTypedRow (tbl : List CRule) (f : Nat) : Prop :=
  ∀ {ls ls' : List Level} {xs ys : List ETm},
    ConvMod (EStep tbl) LvlEq (ETm.appN (.const f ls) xs)
      (ETm.appN (.const f ls') ys) →
    eqNList ls ls' ∧ xs.length = ys.length ∧ List.Forall₂ LvlEq xs ys

/-- TOOTH 2 (S4 §6): the wrong-accept consumer is refused on an actual
    erased-inversion input. The `const 0`-spine pair satisfies every premise of
    `convE_appN_const_inv_wf` and fires it (`ctl_erased_inversion_fires`); on the
    same pair the promoted `LvlEq` row does not exist (`ctl_args_not_lvlEq`), so
    `ErasedAsTypedRow` cannot be built on this table. -/
theorem erased_conv_not_typed_row :
    (TableWF [] ∧ NoHeadRule [] 0 ∧
      ConvMod (EStep []) LvlEq
        (ETm.appN (.const 0 []) [.app (.lam (.bvar 0)) (.const 9 [])])
        (ETm.appN (.const 0 []) [.const 9 []])) ∧
      ¬ ErasedAsTypedRow [] 0 :=
  ⟨⟨emptyTable_wf, noHeadRule_empty 0, ctl_conv⟩,
    fun h => ctl_args_not_lvlEq (h ctl_conv).2.2⟩

/-- the weakened consumer: accepts an argument pair as a typed family row after
    checking ONLY the erased evidence — arity plus the pointwise `ConvMod` row
    `convE_appN_const_inv_wf` actually returns. It is wrong precisely because it
    never inspects ≈-faithfulness: this predicate IS the erased row, mislabeled
    as a typed-family row. -/
def weakAcceptsAsTypedRow (tbl : List CRule) (xs ys : List ETm) : Prop :=
  xs.length = ys.length ∧ List.Forall₂ (ConvMod (EStep tbl) LvlEq) xs ys

/-- the exact typed contract on the same input, restated at the production
    row: `FamAppConvInj` (`RcicInvertFamily:248`) delivers `eqNList ×'
    ConvArgs` only to a `const r`-headed pair whose `r` resolves to an
    `inductiveM` member of `E` — and the `ConvArgs` payload itself. `xs ys`
    are the input's `Expr Nat` arguments. (The full production signature also
    asks `EnvWf`/`CtxWf`/spine-`Conv`; this is the premise pack that already
    fails on the control input.) -/
def exactTypedRowContract (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (r : Nat) (xs ys : List (Expr Nat)) : Prop :=
  (∃ m : CheckedMember, E.members r = some m ∧ m.mclass = .inductiveM) ∧
    Nonempty (ConvArgs E n Γ xs ys)

/-- REFUSE on the control input: the typed lift of the ctl argument pair —
    `app (lam (sort 0) (bvar 0)) (const 9 [])` vs `const 9 []` — is not a
    typed family row under `emptyEnv`: member `0` does not resolve at all, so
    no `inductiveM` member backs the `const 0` spine head. -/
theorem ctl_not_typed_family_row (n : Nat) :
    ¬ exactTypedRowContract emptyEnv n [] 0
      [.app (.lam (.sort .zero) (.bvar 0)) (.const 9 [])] [.const 9 []] := by
  rintro ⟨⟨m, hm, -⟩, -⟩
  have hmn : emptyEnv.members 0 = none := rfl
  rw [hmn] at hm
  exact Option.noConfusion hm

/-- TOOTH 2b (S4 §6), the ACCEPT/REFUSE pair on the `ctl_step` input: the
    weakened consumer ACCEPTS — `weakAcceptsAsTypedRow` holds on the erased
    arguments, since `ctl_erased_inversion_fires` delivers the erased row —
    and the exact production contract REFUSES the same input —
    `ctl_not_typed_family_row`: `emptyEnv` has no `inductiveM` member `0`, so
    no `FamAppConvInj` row exists to deliver `ConvArgs` there. The erased row
    is not a typed family row. -/
theorem typed_row_accept_refuse_pair :
    weakAcceptsAsTypedRow []
      [.app (.lam (.bvar 0)) (.const 9 [])] [.const 9 []] ∧
      ¬ exactTypedRowContract emptyEnv 0 [] 0
        [.app (.lam (.sort .zero) (.bvar 0)) (.const 9 [])] [.const 9 []] :=
  ⟨⟨rfl, ctl_erased_inversion_fires.2.2⟩, ctl_not_typed_family_row 0⟩

end Rcic.Syn

#print axioms Rcic.Syn.badFamilyTable_wf
#print axioms Rcic.Syn.badFamily_croot
#print axioms Rcic.Syn.badFamily_not_noHeadRule
#print axioms Rcic.Syn.rigid_not_noHeadRule
#print axioms Rcic.Syn.eStep_appN_const_inv
#print axioms Rcic.Syn.rstar_eStep_appN_const_inv
#print axioms Rcic.Syn.forall2_convE_of_joins
#print axioms Rcic.Syn.convE_appN_const_inv_wf
#print axioms Rcic.Syn.badFamily_star_escapes
#print axioms Rcic.Syn.not_rstar_spine_inv_without_noHeadRule
#print axioms Rcic.Syn.emptyTable_wf
#print axioms Rcic.Syn.noHeadRule_empty
#print axioms Rcic.Syn.ctl_step
#print axioms Rcic.Syn.ctl_conv
#print axioms Rcic.Syn.ctl_erased_inversion_fires
#print axioms Rcic.Syn.ctl_args_not_lvlEq
#print axioms Rcic.Syn.erased_conv_not_typed_row
#print axioms Rcic.Syn.ctl_not_typed_family_row
#print axioms Rcic.Syn.typed_row_accept_refuse_pair
