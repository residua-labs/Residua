import rcic.RcicAnnLR3RCodeSoundInterface
import rcic.RcicAnnLR3GuardedConversionUniverse
import rcic.RcicAnnLR3NoneSortSupply

/-!
# Universe points are not realized in a closed world

The universe codes of the tagged tower have mandatory designated points:
the native neutral type codes `value (some j) name`, one for every name,
and these points are pairwise unrelated. `RCodeSound.realization` asks that
every member be related to the evaluation of an actual source fragment of
the fixed world, and universe relatedness is conversion, which preserves
type images. So a sound universe instance needs closed source types whose
evaluator images are those native neutral type values.

**Equivariance.** Swapping the native names 3 and 4 fixes every constant
that the evaluator's translation of an admitted closed source can produce:
the tags 10 and 11, the level references (100 and above), and the literal
constants 1 and 2. The approximation relation is equivariant under the swap
(`approxI_swap`). Therefore every typed closed source in the empty
environment has a swap-invariant image (`closed_image_invariant`), while
`value k 3` is swapped to `value k 4`, which is a different value by the
inherited name injectivity. No closed admitted source has a native neutral
image (`no_closed_native_image`).

**Boundary.** In the empty admitted world, no `RCodeSound` instance has any
code whose relation determines erasures and that has a member with a native
neutral image of name 3 (`no_sound_with_native_member`). In particular no
instance has the conversion universe as its code (`no_sound_conversion_universe`).
`boundary_premises` separately constructs the positive side for every `j`:
- admission of the empty world (`EnvWfA`, `CtxWfA`);
- typing of the source sort `Sort (levelNumeral j)`;
- the evaluator's image of that sort, equal to `universeValue (some j)`, which
  is the conversion universe's type image;
- the universe's point 3 as a member, with native image `value (some j) 3`.

Positive-level universe instances therefore need realization in extension
worlds, where fresh type variables carry the reflected names, rather than in
one fixed finite world. The level-zero instances are unaffected, because
irrelevance relates every member. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.SoundUniverseRealizationBoundary

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements RCodeSoundInterface

universe u v

/-! ## The name swap -/

def swapName (n : Nat) : Nat := if n = 3 then 4 else if n = 4 then 3 else n

theorem swapName_swapName (n : Nat) : swapName (swapName n) = n := by
  unfold swapName
  by_cases h3 : n = 3
  · subst h3; rfl
  · by_cases h4 : n = 4
    · subst h4; rfl
    · rw [if_neg h3, if_neg h4, if_neg h3, if_neg h4]

theorem swapName_fixed {n : Nat} (h3 : n ≠ 3) (h4 : n ≠ 4) : swapName n = n := by
  unfold swapName
  rw [if_neg h3, if_neg h4]

mutual
def swapC : CptI → CptI
  | .bot => .bot
  | .sort => .sort
  | .pi a f => .pi (swapC a) (swapG f)
  | .lam f => .lam (swapG f)
  | .spine r args => .spine (swapName r) (swapL args)
def swapL : List CptI → List CptI
  | [] => []
  | c :: cs => swapC c :: swapL cs
def swapG : List (List CptI × CptI) → List (List CptI × CptI)
  | [] => []
  | (us, c) :: g => (swapL us, swapC c) :: swapG g
end

mutual
theorem swapC_swapC : (c : CptI) → swapC (swapC c) = c
  | .bot => rfl
  | .sort => rfl
  | .pi a f => by simp only [swapC, swapC_swapC a, swapG_swapG f]
  | .lam f => by simp only [swapC, swapG_swapG f]
  | .spine r args => by simp only [swapC, swapName_swapName r, swapL_swapL args]
theorem swapL_swapL : (cs : List CptI) → swapL (swapL cs) = cs
  | [] => rfl
  | c :: cs => by simp only [swapL, swapC_swapC c, swapL_swapL cs]
theorem swapG_swapG : (g : List (List CptI × CptI)) → swapG (swapG g) = g
  | [] => rfl
  | (us, c) :: g => by simp only [swapG, swapL_swapL us, swapC_swapC c, swapG_swapG g]
end

theorem swapL_append (xs ys : List CptI) : swapL (xs ++ ys) = swapL xs ++ swapL ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      show swapC x :: swapL (xs ++ ys) = swapC x :: (swapL xs ++ swapL ys)
      rw [ih]

theorem mem_swapL {c : CptI} {us : List CptI} : c ∈ swapL us ↔ swapC c ∈ us := by
  induction us with
  | nil => simp [swapL]
  | cons x xs ih =>
      simp only [swapL, List.mem_cons, ih]
      constructor
      · rintro (h | h)
        · left; rw [h, swapC_swapC]
        · right; exact h
      · rintro (h | h)
        · left; rw [← h, swapC_swapC]
        · right; exact h

theorem mem_swapG {s : List CptI × CptI} {g : List (List CptI × CptI)} :
    s ∈ swapG g ↔ (swapL s.1, swapC s.2) ∈ g := by
  induction g with
  | nil => simp [swapG]
  | cons x xs ih =>
      rcases x with ⟨us, c⟩
      rcases s with ⟨vs, d⟩
      simp only [swapG, List.mem_cons, ih, Prod.mk.injEq]
      constructor
      · rintro (⟨h1, h2⟩ | h)
        · left; exact ⟨by rw [h1, swapL_swapL], by rw [h2, swapC_swapC]⟩
        · right; exact h
      · rintro (⟨h1, h2⟩ | h)
        · left; exact ⟨by rw [← h1, swapL_swapL], by rw [← h2, swapC_swapC]⟩
        · right; exact h

def swapE : Expr Nat → Expr Nat
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls => .const (swapName r) ls
  | .app f a => .app (swapE f) (swapE a)
  | .lam A b => .lam (swapE A) (swapE b)
  | .pi A B => .pi (swapE A) (swapE B)
  | .letE A x b => .letE (swapE A) (swapE x) (swapE b)
  | .lit n => .lit n

def swapEnv (ρ : EnvI) : EnvI := fun i c => ρ i (swapC c)

theorem swapEnv_cons (S : CptI → Prop) (ρ : EnvI) :
    swapEnv (EnvI.cons S ρ) = EnvI.cons (fun c => S (swapC c)) (swapEnv ρ) := by
  funext i c
  cases i <;> rfl

theorem swapEnv_bot : swapEnv EnvI.bot = EnvI.bot := by
  funext i d
  apply propext
  show swapC d = .bot ↔ d = .bot
  constructor
  · intro h
    rw [← swapC_swapC d, h]
    rfl
  · intro h
    rw [h]
    rfl

theorem demand_swap (us : List CptI) :
    (fun c => demand us (swapC c)) = demand (swapL us) := by
  funext c
  apply propext
  exact mem_swapL.symm

theorem natExpand_swap (t : Nat) : swapE (natExpand t) = natExpand t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      show Expr.app (.const (swapName 2) []) (swapE (natExpand t)) = _
      rw [ih]
      rfl

/-- The approximation relation is equivariant under the name swap. -/
theorem approxI_swap {ρ : EnvI} {t : Expr Nat} {c : CptI} (h : ApproxI ρ t c) :
    ApproxI (swapEnv ρ) (swapE t) (swapC c) := by
  induction h with
  | bot ρ e => exact .bot _ _
  | @bvar ρ i c h =>
      exact ApproxI.bvar (show ρ i (swapC (swapC c)) by rw [swapC_swapC]; exact h)
  | sort ρ l => exact .sort _ _
  | @pi ρ A B a f hA hB ihA ihB =>
      refine .pi ihA ?_
      intro s hs
      have hs' := mem_swapG.mp hs
      have h := ihB _ hs'
      rw [swapEnv_cons, demand_swap, swapL_swapL, swapC_swapC] at h
      exact h
  | @lam ρ A b f hb ihb =>
      refine .lam ?_
      intro s hs
      have hs' := mem_swapG.mp hs
      have h := ihb _ hs'
      rw [swapEnv_cons, demand_swap, swapL_swapL, swapC_swapC] at h
      exact h
  | @app ρ f a g s hf hs ha ihf iha =>
      refine .app (g := swapG g) (s := (swapL s.1, swapC s.2)) ihf ?_ ?_
      · apply mem_swapG.mpr
        rw [swapL_swapL, swapC_swapC]
        exact hs
      · intro u hu
        have hu' := mem_swapL.mp hu
        have h := iha _ hu'
        rw [swapC_swapC] at h
        exact h
  | const ρ r ls => exact .const _ _ _
  | @appSpine ρ f a r args u hf ha ihf iha =>
      show ApproxI _ _ (.spine (swapName r) (swapL (args ++ [u])))
      rw [swapL_append]
      exact .appSpine ihf iha
  | letE h ih => exact .letE ih
  | @lit ρ t c h ih =>
      apply ApproxI.lit
      rw [← natExpand_swap t]
      exact ih

/-! ## Closed admitted sources have swap-invariant images -/

def Fixed : Expr Nat → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const r _ => swapName r = r
  | .app f a => Fixed f ∧ Fixed a
  | .lam A b => Fixed A ∧ Fixed b
  | .pi A B => Fixed A ∧ Fixed B
  | .letE A x b => Fixed A ∧ Fixed x ∧ Fixed b
  | .lit _ => True

theorem swapE_fixed : (t : Expr Nat) → Fixed t → swapE t = t
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const r ls, h => by
      show Expr.const (swapName r) ls = _
      rw [show swapName r = r from h]
  | .app f a, h => by
      show Expr.app (swapE f) (swapE a) = _
      rw [swapE_fixed f h.1, swapE_fixed a h.2]
  | .lam A b, h => by
      show Expr.lam (swapE A) (swapE b) = _
      rw [swapE_fixed A h.1, swapE_fixed b h.2]
  | .pi A B, h => by
      show Expr.pi (swapE A) (swapE B) = _
      rw [swapE_fixed A h.1, swapE_fixed B h.2]
  | .letE A x b, h => by
      show Expr.letE (swapE A) (swapE x) (swapE b) = _
      rw [swapE_fixed A h.1, swapE_fixed x h.2.1, swapE_fixed b h.2.2]
  | .lit _, _ => rfl

/-- Source constants are among the fixed names. -/
def FixedA : ExprA → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const r _ => swapName r = r
  | .app f a => FixedA f ∧ FixedA a
  | .lam A _ b => FixedA A ∧ FixedA b
  | .pi A _ B _ => FixedA A ∧ FixedA B
  | .letE A x b => FixedA A ∧ FixedA x ∧ FixedA b
  | .lit _ => True

theorem fixedA_natExpand : (n : Nat) → FixedA (natExpandA n)
  | 0 => rfl
  | n + 1 => ⟨rfl, fixedA_natExpand n⟩

theorem fixed_levelTerm (i : Option Nat) : Fixed (levelTerm i) := by
  cases i with
  | none => rfl
  | some k =>
      show swapName (101 + k) = 101 + k
      exact swapName_fixed (by omega) (by omega)

theorem fixed_taggedTerm (i : Option Nat) (p : Expr Nat) (hp : Fixed p) :
    Fixed (taggedTerm i p) := ⟨⟨rfl, fixed_levelTerm i⟩, hp⟩

theorem translation_fixed {F : EnvironmentEval.FamilySyntax} {ν : Valuation}
    {e : ExprA} {t : Expr Nat} (h : EnvironmentEval.Translation emptyEnvA F ν e t) :
    FixedA e → Fixed t := by
  induction h with
  | cut e => intro _; exact ⟨trivial, trivial⟩
  | bvar i => intro _; trivial
  | sort l => intro _; exact fixed_taggedTerm _ _ ⟨rfl, fixed_levelTerm _⟩
  | constBody body _ _ => intro _; exact Option.noConfusion body
  | @constRigid r ls _ => intro h; exact h
  | app _ _ ihf iha => intro h; exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ ihA ihb => intro h; exact ⟨ihA h.1, ihb h.2⟩
  | pi _ _ ihA ihB => intro h; exact fixed_taggedTerm _ _ ⟨ihA h.1, ihB h.2⟩
  | letE _ _ _ ihA ihv ihb => intro h; exact ⟨ihA h.1, ihv h.2.1, ihb h.2.2⟩
  | @lit n t _ ih => intro _; exact ih (fixedA_natExpand n)

/-- An admitted source in the empty environment mentions no constant. -/
theorem fixedA_of_typed {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {e A : ExprA} :
    HasTyA emptyEnvA I n Γ e A → FixedA e
  | .sort _ _ => trivial
  | .bvar _ _ _ _ _ _ => trivial
  | .const _ _ _ _ _ hres _ _ _ => Option.noConfusion hres
  | .pi _ _ _ _ _ hA hB => ⟨fixedA_of_typed hA, fixedA_of_typed hB⟩
  | .lam _ _ _ _ _ _ hA _ hb => ⟨fixedA_of_typed hA, fixedA_of_typed hb⟩
  | .app _ _ _ _ _ _ _ _ _ _ hf ha => ⟨fixedA_of_typed hf, fixedA_of_typed ha⟩
  | .letE _ _ _ _ _ _ _ hA hv _ hb =>
      ⟨fixedA_of_typed hA, fixedA_of_typed hv, fixedA_of_typed hb⟩
  | .lit _ _ _ _ => trivial
  | .conv _ _ _ _ _ _ h _ _ _ _ => fixedA_of_typed h

/-- Every closed admitted source in the empty world has a swap-invariant image. -/
theorem closed_image_invariant (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (e : ExprA) (he : FixedA e) (c : CptI) :
    EnvironmentEval.denote emptyEnvA F ν EnvI.bot e (swapC c) ↔
      EnvironmentEval.denote emptyEnvA F ν EnvI.bot e c := by
  have hbot := swapEnv_bot
  constructor
  · rintro ⟨t, ht, hc⟩
    have h := approxI_swap hc
    rw [hbot, swapE_fixed t (translation_fixed ht he), swapC_swapC] at h
    exact ⟨t, ht, h⟩
  · rintro ⟨t, ht, hc⟩
    have h := approxI_swap hc
    rw [hbot, swapE_fixed t (translation_fixed ht he)] at h
    exact ⟨t, ht, h⟩

theorem levelRef_ge (k : Option Nat) : 100 ≤ levelRef k := by
  cases k with
  | none => exact Nat.le_refl _
  | some j => show 100 ≤ 101 + j; omega

theorem swapE_term (k : Option Nat) (a b : Nat) (hab : swapName a = b) :
    swapE (NativeMemberValues.term k a) = NativeMemberValues.term k b := by
  show Expr.app (.app (.const (swapName 10) []) (.const (swapName (levelRef k)) []))
    (.const (swapName a) []) = _
  rw [swapName_fixed (by omega) (by omega),
    swapName_fixed (by have := levelRef_ge k; omega) (by have := levelRef_ge k; omega), hab]
  rfl

theorem native_value_swap (k : Option Nat) (c : CptI) :
    NativeMemberValues.value k 3 (swapC c) ↔ NativeMemberValues.value k 4 c := by
  constructor
  · intro h
    have h' := approxI_swap h
    rw [swapC_swapC, swapEnv_bot, swapE_term k 3 4 rfl] at h'
    exact h'
  · intro h
    have h' := approxI_swap h
    rw [swapEnv_bot, swapE_term k 4 3 rfl] at h'
    exact h'

/-- No admitted closed source in the empty environment has a native neutral
type image. -/
theorem no_closed_native_image (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (e : ExprA) (he : FixedA e) (k : Option Nat) :
    ¬ ValueEq (EnvironmentEval.denote emptyEnvA F ν EnvI.bot e) (NativeMemberValues.value k 3) := by
  intro h
  have h34 : ValueEq (NativeMemberValues.value k 3) (NativeMemberValues.value k 4) := by
    intro c
    rw [← native_value_swap, ← h, ← h, closed_image_invariant F ν e he]
  have := TaggedSaturatedTower.native_value_name_injective k 3 4 h34
  omega

/-! ## The boundary for sound instances -/

def emptyWorld (F : EnvironmentEval.FamilySyntax) (ν : Valuation) : World where
  env := emptyEnvA
  iota := iotaIfaceA emptyEnvA
  levelCount := 0
  context := []
  family := F
  valuation := ν
  rawEnvironment := EnvI.bot
  envWf := .empty
  contextWf := .nil

/-- No sound instance in the empty world has a code whose relation determines
erasures and that has a member with a native neutral image. -/
theorem no_sound_with_native_member (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    {k : Nat} (C : RCodeSound.{u,v} (emptyWorld F ν) k)
    (hdet : ∀ x y : C.Element, Related x y → ValueEq (C.erase x) (C.erase y))
    (x : C.Element) (j : Option Nat) (hx : ValueEq (C.erase x) (NativeMemberValues.value j 3)) :
    False := by
  obtain ⟨s, hs⟩ := C.realization x
  have he := (hdet _ _ hs).symm.trans hx
  exact no_closed_native_image F ν _ (fixedA_of_typed (C.source s).typed) j
    ((C.erasure s).symm.trans he)

/-- In particular no sound instance in the empty world has the conversion
universe as its code. The admitted source sort with exactly this type image
is constructed separately in `boundary_premises`. -/
theorem no_sound_conversion_universe (F : EnvironmentEval.FamilySyntax) (ν : Valuation)
    (j : Nat) (C : RCodeSound.{u+1,v} (emptyWorld F ν) (j+1))
    (hC : C.code = GuardedConversionUniverse.conversionUniverse.{u} j) : False := by
  have hdet : ∀ D : GuardedTaggedCode.Code.{u+1} (j+1),
      D = GuardedConversionUniverse.conversionUniverse.{u} j →
      ∀ a b : D.Element, D.view.relation a b → ValueEq (D.erase a) (D.erase b) := by
    intro D hD
    subst hD
    intro a b h
    exact GuardedTaggedCode.converts_type_image h
  have hpt : ∀ D : GuardedTaggedCode.Code.{u+1} (j+1),
      D = GuardedConversionUniverse.conversionUniverse.{u} j →
      ValueEq (D.erase (D.view.point 3)) (NativeMemberValues.value (some j) 3) := by
    intro D hD
    subst hD
    exact ValueEq.refl _
  exact no_sound_with_native_member F ν C (fun x y h => hdet C.code hC x.val y.val h)
    (C.point 3) (some j) (hpt C.code hC)

/-- The level numeral `j`: `succ` applied `j` times to `zero`. -/
def levelNumeral : Nat → Level
  | 0 => .zero
  | j + 1 => .succ (levelNumeral j)

theorem eval_levelNumeral (ν : Valuation) : (j : Nat) → eval ν (levelNumeral j) = some j
  | 0 => rfl
  | j + 1 => by
      show (eval ν (levelNumeral j)).map Nat.succ = some (j + 1)
      rw [eval_levelNumeral ν j]
      rfl

/-- The positive side, all constructed for every `F`, `ν`, `j`:
- admission of the empty world;
- typing of the source sort `Sort (levelNumeral j)`;
- the evaluator's image of that sort, which is exactly the conversion
  universe's type image `universeValue (some j)`;
- the universe's point 3 as a member, with native image `value (some j) 3`. -/
theorem boundary_premises (F : EnvironmentEval.FamilySyntax) (ν : Valuation) (j : Nat) :
    Nonempty (EnvWfA (iotaIfaceA emptyEnvA) emptyEnvA) ∧
    Nonempty (CtxWfA emptyEnvA (iotaIfaceA emptyEnvA) 0 []) ∧
    Nonempty (HasTyA emptyEnvA (iotaIfaceA emptyEnvA) 0 []
      (.sort (levelNumeral j)) (.sort (.succ (levelNumeral j)))) ∧
    (emptyWorld F ν).evaluate (.sort (levelNumeral j)) = universeValue (some j) ∧
    (GuardedConversionUniverse.conversionUniverse.{0} j).view.value = universeValue (some j) ∧
    (GuardedConversionUniverse.conversionUniverse.{0} j).view.relation
      ((GuardedConversionUniverse.conversionUniverse.{0} j).view.point 3)
      ((GuardedConversionUniverse.conversionUniverse.{0} j).view.point 3) ∧
    (GuardedConversionUniverse.conversionUniverse.{0} j).erase
      ((GuardedConversionUniverse.conversionUniverse.{0} j).view.point 3) =
      NativeMemberValues.value (some j) 3 := by
  refine ⟨⟨.empty⟩, ⟨.nil⟩, ⟨.sort [] _⟩, ?_, rfl,
    (GuardedConversionUniverse.conversionUniverse.{0} j).view.point_member 3, rfl⟩
  have h : (emptyWorld F ν).evaluate (.sort (levelNumeral j)) =
      universeValue (eval ν (levelNumeral j)) :=
    (EnvironmentEval.annSemantics NoneSortSupply.codeSystem emptyEnvA F).sort_image ν [] EnvI.bot _
  rw [h, eval_levelNumeral]

end Rcic.Declarative.Ann.LR3.SoundUniverseRealizationBoundary
