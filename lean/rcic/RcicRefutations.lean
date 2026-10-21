/-
RCIC type-④ refutations (00 §19.2 errata 2/3, §20.5) — COMPILED evidence
that two conditioning shapes are unsatisfiable, so no obligation may be
landed in either shape.

Three independent refutations live here:

  (R-ctx)   The `EnvWf`-only, ∀Γ-unconstrained pair `PiConvInj` /
            `SortConvChar` (the shape landed by `910087743`) is refuted
            at `emptyEnv`. `EnvWf` constrains the ENVIRONMENT only; the
            junk `x : Prop := Prop` relocates into the LOCAL CONTEXT,
            where `Step.zetaLocal` is unconditioned and `lookupType` /
            `lookupValue` never compare a let's annotation with its
            value. Correction (§19.2 erratum 2): condition on `CtxWf`.

  (R-arity) Family-head conversion injectivity is refuted over an
            environment whose only member is an `inductiveM` family
            whose stored type is NOT an arity — `I : Π (P : Prop),
            Π (Q : Prop), Q`. Then `I X` is PROOF-valued, two of its
            applications inhabit one Prop, and `Conv.irr` identifies
            them; both halves (levels and arguments) fall. Correction
            (§19.2 erratum 3): `EnvWf.indMember` must carry the arity
            check for `inductiveM`.

  (R-lvl)   02 §2's level well-formedness is not transcribed into
            `HasTy`. `HasTy.const`'s `hwf` is INVERTED at `n = 0`
            (a level is admitted iff it MENTIONS a parameter) and
            VACUOUS at `n ≥ 1` (`k := 0` admits every level);
            `HasTy.sort` carries no side condition at all. The
            entanglement: under the UNTYPED `Conv.sorts` the levels
            of TYPES are unbounded even where every SUBJECT's are,
            so the correction cannot be made on `HasTy.sort` and
            `HasTy.const` alone. Correction (00 §19.7 E-LvlWf):
            `levelsBounded n ls` on `const`, `levelBounded n l` on
            `sort` — recorded there, NOT landed here.

Every refuted statement is written out HERE as a LOCAL, unconditioned
copy of the shape being refuted, never through the shared `PiConvInj` /
`SortConvChar` / `FamAppConvInj` definitions: a refutation that reads
its own target from a definition another patch may edit is not evidence
about the shape it names. Only landed constructors are used
(`Step.zetaLocal`, `HasTy.bvar/sort/pi/app/const/conv`, `Conv.irr/step/
symm/trans/sorts`, `EnvWf.empty/indMember`, `extendEnv`, `emptyEnv`,
`lookupType`, `lookupValue`). No `sorry`, no `native_decide`, no
`Classical.choice`; axioms ⊆ {propext, Quot.sound}.

A failed refutation is not evidence of soundness; a refutation that
compiles is evidence of unsoundness OF THE SHAPE IT STATES, and of
nothing wider.

Import discipline: RcicDeclarative (the theory) + RcicEnv (`EnvWf`)
+ RcicInvertFamily (`CtxWf` lives only there — `inductive CtxWf` is
one hit in `lean/rcic/*.lean`; B-c-A2/A4 carry `CtxWf E n Γ →` in
the statement). NOT RcicDTMeta (red), NOT RcicParRed (the level
teeth it holds are three lines each and are re-proved locally under
distinct names, so this file does not rebuild behind the 13.8k-line
ParRed file). InvertFamily's import closure is seven rcic modules
and contains no ParRed module and no Diamond; the rebuild-cost
reason of the two exclusions does not reach it.
-/
import rcic.RcicDeclarative
import rcic.RcicEnv
import rcic.RcicInvertFamily

namespace Rcic.Declarative

/-! ## §0 Level teeth (local; `RcicParRed`'s copies are not imported) -/

/-- `imax l 0` is lazy in `l` and equals `0` at every valuation.
Local copy of `eqN_imax_zero` (RcicParRed), to keep this file off the
ParRed rebuild edge. -/
theorem refutEqN_imax_zero (l : Level) : eqN (.imax l .zero) .zero :=
  fun _ρ => rfl

/-- `0 =ₙ succ 0` is false: at the empty valuation the two sides are
`some 0` and `some 1`. -/
theorem refutEqN_zero_succ_false : ¬ eqN .zero (.succ .zero) := by
  intro h
  have hv : (some 0 : Option Nat) = some 1 := h (fun _ => none)
  injection hv with hv'
  exact Nat.noConfusion hv'

/-- Two distinct level PARAMETERS are not `=ₙ`: the valuation that
separates them separates the evaluations. Used instead of `0` / `succ 0`
in the family refutation because `HasTy.const`'s `hwf` premise demands
`eval (fun _ => none) l = none` or a universe bound, and an unbound
parameter satisfies the first disjunct at every `n`. -/
theorem refutEqN_param01_false : ¬ eqN (.param 0) (.param 1) := by
  intro h
  have hv : (some 0 : Option Nat) = some 1 :=
    h (fun i => if i = 0 then some 0 else some 1)
  injection hv with hv'
  exact Nat.noConfusion hv'

/-- `Π A. C` with `C` a Prop is a Prop: `HasTy.pi` ascribes
`sort (imax u 0)`, and `imax _ 0 =ₙ 0`. -/
def refutPiIsProp {E : ResolvedEnv} {n : Nat} (Γ : LCtx) (A : Expr Nat)
    (u : Level) (C : Expr Nat)
    (hA : HasTy E n Γ A (.sort u))
    (hC : HasTy E n (LocalDecl.assumption A :: Γ) C (.sort .zero)) :
    HasTy E n Γ (.pi A C) (.sort .zero) :=
  .conv _ _ _ _ (.pi Γ A u C .zero hA hC)
    (.sorts _ _ _ (refutEqN_imax_zero u))

/-! ## §1 (R-ctx) The `EnvWf`-only, ∀Γ-unconstrained pair is refuted

00 §19.2 erratum 2. `EnvWf` type-checks stored bodies
(`EnvWf.definition`'s `hv : HasTy E n [] v A`), which is what moved
`piIrrEnv`'s junk `T : Prop := Prop` out of reach. The SAME junk is
constructible in the local context of a well-formed (here: EMPTY)
environment, because the analogous check lives in `CtxWf.letBinding`
and no landed conversion obligation carries `CtxWf`. -/

/-- Junk LOCAL context `x : Prop := Prop`. -/
def junkLetCtx : LCtx := [LocalDecl.letBinding (.sort .zero) (.sort .zero)]

/-- `lookupType` reads the ANNOTATION (`Sort 0`). -/
theorem junkLetCtx_lookupType : lookupType junkLetCtx 0 = some (.sort .zero) := rfl

/-- `lookupValue` reads the VALUE (`Sort 0`) — nothing relates the two
outside `CtxWf`. -/
theorem junkLetCtx_lookupValue : lookupValue junkLetCtx 0 = some (.sort .zero) := rfl

/-- `bvar 0` IS a Prop in this context (`HasTy.bvar` reads the
annotation alone). -/
def junkLetCtx_hasTyP {E : ResolvedEnv} {n : Nat} :
    HasTy E n junkLetCtx (.bvar 0) (.sort .zero) :=
  .bvar junkLetCtx 0 (.sort .zero) junkLetCtx_lookupType

/-- …and every type converts INTO it: `Step.zetaLocal` is unconditioned
(no environment and no context well-formedness premise). -/
def junkLetCtx_convP {E : ResolvedEnv} {n : Nat} :
    Conv E n junkLetCtx (.sort .zero) (.bvar 0) :=
  .symm _ _ _ (.step _ _ _ (.zetaLocal junkLetCtx 0 (.sort .zero)
    junkLetCtx_lookupValue))

/-- Under one more binder the junk let sits at index 1, so `bvar 1` is a
Prop there; hence `Π A. bvar 1` is a proof of the Prop `bvar 0`. -/
def junkLetCtx_tyPi {E : ResolvedEnv} {n : Nat} (A : Expr Nat) (u : Level)
    (hA : HasTy E n junkLetCtx A (.sort u)) :
    HasTy E n junkLetCtx (.pi A (.bvar 1)) (.bvar 0) :=
  .conv _ _ _ _
    (.pi junkLetCtx A u (.bvar 1) .zero hA
      (.bvar (LocalDecl.assumption A :: junkLetCtx) 1 (.sort .zero) rfl))
    (.trans _ _ (.sort .zero) _
      (.sorts _ _ _ (refutEqN_imax_zero u)) junkLetCtx_convP)

/-- Two Π's with DIFFERENT domain universes and the SAME codomain,
identified by proof irrelevance at the Prop `bvar 0`. The environment is
arbitrary — in particular `emptyEnv`, which is `EnvWf` by
`EnvWf.empty`. -/
def junkLetCtx_pi_pi {E : ResolvedEnv} {n : Nat} :
    Conv E n junkLetCtx
      (.pi (.sort .zero) (.bvar 1))
      (.pi (.sort (.succ .zero)) (.bvar 1)) :=
  .irr junkLetCtx (.bvar 0) _ _ junkLetCtx_hasTyP
    (junkLetCtx_tyPi (.sort .zero) (.succ .zero) (.sort junkLetCtx .zero))
    (junkLetCtx_tyPi (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort junkLetCtx (.succ .zero)))

/-- TYPE-④ (00 §19.2 erratum 2). The pair of obligations in the shape
LANDED by `910087743` — conditioned on `EnvWf E n` and quantified over
ALL `Γ` — is refuted at `emptyEnv`.

The two premises are written out here as local copies of `PiConvInj` /
`SortConvChar` rather than applied through those definitions, so that
this refutation states its own target and cannot be silently retargeted
by an edit to `RcicInvertFamily`.

Correction: both rows (and every conversion-injectivity row) carry
`CtxWf E n Γ` as well. `CtxWf.letBinding` demands `hv : HasTy Γ v A`,
which is exactly the check `lookupType` / `lookupValue` do not perform;
`junkLetCtx` is not `CtxWf` because `HasTy Γ (Sort 0) (Sort 0)` would be
needed. This is a correction, not a weakening: the kernel converts only
in well-formed contexts. -/
theorem piConvInj_envOnly_false {n : Nat}
    (hp : EnvWf emptyEnv n →
      ∀ (Γ : LCtx) (A B A' B' : Expr Nat),
        Conv emptyEnv n Γ (.pi A B) (.pi A' B') →
          Conv emptyEnv n Γ A A' ×'
            Conv emptyEnv n (LocalDecl.assumption A :: Γ) B B')
    (hs : EnvWf emptyEnv n →
      ∀ (Γ : LCtx) (u v : Level),
        Conv emptyEnv n Γ (.sort u) (.sort v) → eqN u v) : False :=
  refutEqN_zero_succ_false
    (hs (.empty n) junkLetCtx .zero (.succ .zero)
      (hp (.empty n) junkLetCtx
          (.sort .zero) (.bvar 1) (.sort (.succ .zero)) (.bvar 1)
          junkLetCtx_pi_pi).1)

/-! ## §2 (R-arity) Family-head injectivity is refuted without an arity
check

00 §19.2 erratum 3 / §20.5. `EnvWf.indMember` (as landed) does not
transcribe 04/05's check that an `inductiveM` family's stored type is an
ARITY (`Π …, Sort u`). Without it the member below is admitted:

    I : Π (P : Prop), Π (Q : Prop), Q

`I X` has type `Π (Q : Prop), Q` — a Prop that does NOT mention `X`, for
every Prop `X` and every universe-argument list. So `Conv.irr` relates
`I ls X` to `I ls' Y` for arbitrary `ls`, `ls'`, `X`, `Y`, and BOTH
halves of family-head injectivity fall. `Γ = []` throughout: no context
junk is used, so this refutation is independent of §1. -/

/-- `Π (Q : Prop), Q` — a closed Prop that is not a sort. -/
def refutFamC : Expr Nat := .pi (.sort .zero) (.bvar 0)

def refutFamC_isProp {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTy E n Γ refutFamC (.sort .zero) :=
  refutPiIsProp Γ (.sort .zero) (.succ .zero) (.bvar 0)
    (.sort Γ .zero)
    (.bvar (LocalDecl.assumption (.sort .zero) :: Γ) 0 (.sort .zero) rfl)

/-- The proof-valued "family": `I : Π (P : Prop), Π (Q : Prop), Q`.
`mclass = inductiveM`, one universe argument, no body. Its stored type
is NOT an arity — the check erratum 3 adds. -/
def famPropMember : CheckedMember :=
  ⟨.inductiveM, 1, .pi (.sort .zero) refutFamC, none⟩

def famPropEnv : ResolvedEnv := extendEnv emptyEnv 0 famPropMember

theorem famPropEnv_lookup : famPropEnv.members 0 = some famPropMember := rfl

theorem famPropMember_closed (k : Nat) :
    lift k 1 famPropMember.mtype = famPropMember.mtype := by
  simp only [famPropMember, refutFamC, lift]
  rw [if_neg (Nat.not_succ_le_zero (k + 1))]

/-- Erratum 3 evidence, post-correction form. Before `harity`, this
environment was `EnvWf` via `EnvWf.indMember` (the defect: the
well-formedness judgment admitted a proof-valued family, and the
refutations below then ran under `EnvWf`). With `harity` in
`indMember`, the family is rejected exactly because its stored type is
not an arity — this is the check the counterexample family fails. -/
theorem famPropMember_not_arity : isArity famPropMember.mtype = false := by
  rfl

/-- `I [param i] : Π (P : Prop), Π (Q : Prop), Q`. 00 §20.6 landed
`instantiateLevels` in `HasTy.const`, so the general claim "typing is
level-inert" is now FALSE and is NOT what this refutation rests on.
What it rests on is sharper and unaffected: `famPropMember.mtype`
mentions no `Level.param` at all, so `instantiateLevels ls` is the
IDENTITY on it — here even definitionally (`instLevel ls .zero` is
`rfl`), which is why the ascription below still elaborates unchanged.
An unbound `param` discharges `hwf` at every `n`. -/
def famProp_head {n : Nat} (Γ : LCtx) (i : Nat) :
    HasTy famPropEnv n Γ (.const 0 [.param i])
      (.pi (.sort .zero) refutFamC) :=
  .const Γ 0 [.param i] famPropMember famPropEnv_lookup rfl
    (fun l hl => ⟨0, Or.inl (by
      cases hl with
      | head => rfl
      | tail _ h => nomatch h)⟩)

/-- `I [param i] X : Π (Q : Prop), Q` for EVERY Prop `X`: the type does
not mention `X` (`instantiate0` does not reach the inner binder's
`bvar 0`). This is what an arity check would forbid. -/
def famProp_app {n : Nat} (Γ : LCtx) (i : Nat) (X : Expr Nat)
    (hX : HasTy famPropEnv n Γ X (.sort .zero)) :
    HasTy famPropEnv n Γ (.app (.const 0 [.param i]) X) refutFamC :=
  .app Γ (.const 0 [.param i]) X (.sort .zero) refutFamC
    (famProp_head Γ i) hX

/-- Proof irrelevance at the Prop `Π (Q : Prop), Q` identifies two
applications of the family that differ in BOTH the universe arguments
and the value argument. `Γ = []`: no context junk. -/
def famProp_irr {n : Nat} (i j : Nat) (X Y : Expr Nat)
    (hX : HasTy famPropEnv n [] X (.sort .zero))
    (hY : HasTy famPropEnv n [] Y (.sort .zero)) :
    Conv famPropEnv n []
      (foldApps (.const 0 [.param i]) [X])
      (foldApps (.const 0 [.param j]) [Y]) :=
  .irr [] refutFamC _ _ (refutFamC_isProp [])
    (famProp_app [] i X hX) (famProp_app [] j Y hY)

/-- TYPE-④ (00 §19.2 erratum 3 / §20.5). Family-head conversion
injectivity — stated here as a LOCAL unconditioned copy of the §20.5
`FamAppConvInj` shape, at the single-argument spine, with the LEVEL half
alone — is refuted over an environment whose only member is an
`inductiveM` family with a non-arity (proof-valued) stored type.

The witness takes the SAME argument on both sides, so this half is
independent of any statement about the arguments: what fails is
`eqNList ls ls'`, for `ls = [param 0]` and `ls' = [param 1]`.

Two facts collaborate and both are landed: this family's stored type
mentions no `Level.param`, so `instantiateLevels ls` is the identity on
it and `.const r ls` / `.const r ls'` have the same type for every list
(00 §20.6's `HasTy.const` change does NOT rescue the row — the level
list it now carries reaches only the parameters the stored type
actually mentions, and this one mentions none), so the two applications
are typed at one Prop; and `Conv.irr` then identifies them. An arity
check on `inductiveM` cuts this (a family application would be a type,
never a proof); nothing else in the landed `EnvWf` does. -/
theorem famAppConvInj_noArity_false {n : Nat}
    (hfa : ∀ (Γ : LCtx) (ls ls' : List Level) (x y : Expr Nat),
      Conv famPropEnv n Γ (foldApps (.const 0 ls) [x])
        (foldApps (.const 0 ls') [y]) →
        eqNList ls ls' ×' Conv famPropEnv n Γ x y) : False :=
  refutEqN_param01_false
    (hfa [] [.param 0] [.param 1] refutFamC refutFamC
      (famProp_irr 0 1 refutFamC refutFamC
        (refutFamC_isProp []) (refutFamC_isProp []))).1.1


/-! ### The ARGUMENT half of the same defect

The level half above is refuted outright. The argument half —
`Conv (I ls X) (I ls' Y) → Conv X Y` — is refuted in the shape
`piConvInj_sortConvChar_false` uses: in CONJUNCTION with the two rows
one is trying to prove. Under O-3 a row refutable together with rows
one is trying to prove is not admissible. -/

/-- `Π (Sort 0). (Π (Q : Prop), Q)` — a Prop. -/
def famProp_X : Expr Nat := .pi (.sort .zero) refutFamC

/-- `Π (Sort 1). (Π (Q : Prop), Q)` — also a Prop, differing exactly in
the domain universe. -/
def famProp_Y : Expr Nat := .pi (.sort (.succ .zero)) refutFamC

def famProp_X_isProp {n : Nat} (Γ : LCtx) :
    HasTy famPropEnv n Γ famProp_X (.sort .zero) :=
  refutPiIsProp Γ (.sort .zero) (.succ .zero) refutFamC
    (.sort Γ .zero) (refutFamC_isProp _)

def famProp_Y_isProp {n : Nat} (Γ : LCtx) :
    HasTy famPropEnv n Γ famProp_Y (.sort .zero) :=
  refutPiIsProp Γ (.sort (.succ .zero)) (.succ (.succ .zero)) refutFamC
    (.sort Γ (.succ .zero)) (refutFamC_isProp _)

/-- TYPE-④ (00 §19.2 erratum 3 / §20.5), ARGUMENT half. Family-head
injectivity's argument component, at ONE universe-argument list and with
`Γ = []` (so neither the level half nor context junk is in play), is
refuted in conjunction with the `PiConvInj` / `SortConvChar` pair over
the same environment — all three stated here as local copies.

THE REASON, stated once: `Conv.irr` is cut at a Π head because both
sides are necessarily TYPE-valued; an inductive-family application may
be PROOF-valued whenever the family's stored type is not an arity, and
then two applications of one family at different arguments legitimately
inhabit one Prop. -/
theorem famAppConvInj_piConvInj_sortConvChar_noArity_false {n : Nat}
    (hfa : ∀ (Γ : LCtx) (ls ls' : List Level) (x y : Expr Nat),
      Conv famPropEnv n Γ (foldApps (.const 0 ls) [x])
        (foldApps (.const 0 ls') [y]) →
        eqNList ls ls' ×' Conv famPropEnv n Γ x y)
    (hp : ∀ (Γ : LCtx) (A B A' B' : Expr Nat),
      Conv famPropEnv n Γ (.pi A B) (.pi A' B') →
        Conv famPropEnv n Γ A A' ×'
          Conv famPropEnv n (LocalDecl.assumption A :: Γ) B B')
    (hs : ∀ (Γ : LCtx) (u v : Level),
      Conv famPropEnv n Γ (.sort u) (.sort v) → eqN u v) : False :=
  refutEqN_zero_succ_false
    (hs [] .zero (.succ .zero)
      (hp [] (.sort .zero) refutFamC (.sort (.succ .zero)) refutFamC
          (hfa [] [.param 0] [.param 0] famProp_X famProp_Y
            (famProp_irr 0 0 famProp_X famProp_Y
              (famProp_X_isProp []) (famProp_Y_isProp []))).2).1)

/-! ## §3 (R-lvl) 02 §2's level well-formedness is not transcribed into
`HasTy`: the landed side condition is INVERTED at `n = 0` and VACUOUS at
`n ≥ 1`, `HasTy.sort` carries none, and — the entanglement — under the
UNTYPED `Conv.sorts` the levels of TYPES are unbounded even where the
levels of every SUBJECT are.

00 §19.7 E-LvlWf / §20.12 (the F-04 verdict). Open on record since
§20.6 as R-8 ("`hwf` near-vacuous; `HasTy.sort` carries no `n ⊢u l
wf`"); this section COMPILES it. 02 §2
(`02_DECLARATIVE_THEORY.md:32`): "`param i` is well formed iff `i <
n`"; 02 §8 puts `n ⊢u l wf` on Sort (`:180`) and "every level is
well formed" on Constant (`:195`). The landed rule
(`RcicDeclarative.lean`, `HasTy.const`) demands instead

    hwf : ∀ l ∈ ls, ∃ k, eval (fun _ => none) l = none ∨ k < n

which at `n ≥ 1` is satisfied by `k := 0` for EVERY level, and at `n
= 0` demands `eval (fun _ => none) l = none` of every level — the
level UNDEFINED under the empty valuation, i.e. a parameter in a
STRICT position: `.param 0` admitted, `.zero` refused, and `.imax
(.param 0) .zero` REFUSED although it mentions a parameter (`imax`'s
lazy zero branch evaluates it to `some 0`; the sharpness pin in 3.2).
Inverted against 02 §2 on the closed levels; NOT "admitted iff it
mentions a parameter" (Codex review of #3835, corrected here).
`HasTy.sort` has no side condition at all. The
machine never sees this (`hwf_of_ls`, `RcicMachine`, discharges the
premise at `ls = []` only), and the one landed inversion that DOES
return the field (`hasTyConstWf`, `RcicParRedSR`) has a single
consumer, which transports it along `eqNList` and never evaluates
it. The CORRECT predicate exists on the tree (`levelBounded` /
`levelsBounded`, `RcicLevelCalc`, consumed by `hlvlB`) and has
carriers (`apps/rcic-level-eval` `[rcic_level_param_unbound]`,
`apps/rcic-instantiate-levels` `[rcic_inst_levels_param_unbound]`);
the CORRECTION is NOT landed here — it edits the root inductive (31
modules) and, by §3.4 below, cannot by itself bound the levels of
TYPES: that needs 02 §8's TYPED conversion rule, which is F-05b's
ring, not F-04's.

Every statement below is type-④ evidence "of the shape it states,
and of nothing wider" (this file's rule, above). The
`EnvWf`-conditioned form is refuted at `emptyEnv` (`EnvWf.empty`)
and `Γ = []` (`CtxWf.nil` inhabits it, `RcicInvertFamily`), so
neither conditioning rescues it. Import discipline UNCHANGED:
`RcicDeclarative` + `RcicEnv` (`levelBounded` reaches this file
through `RcicEnv → RcicIota → RcicLevelCalc`). No new definition is
introduced — no predicate, no class, no name from 00 §19.3's
not-introduced list; the predicates refuted are written INSIDE the
refuting statement's hypothesis, as `piConvInj_envOnly_false` (§1)
writes its. -/

/-- The one-member arity-1 family environment `RcicEnv` pins its
admission checks against (`pinFamEnv`), read at ref 0. -/
theorem pinFamEnv_lookup :
    pinFamEnv.members 0 = some ⟨.inductiveM, 1, .sort .zero, none⟩ := rfl

/-! ### 3.1 `HasTy.sort`: `sort (param i)` at `n = 0`, in every
environment -/

/-- 02 §8 Sort requires `0 ⊢u param i wf`, which 02 §2 refuses at
every `i`; the landed rule types it in every environment and
context. -/
def hasTy_sort_unbounded_at_zero {E : ResolvedEnv} (Γ : LCtx) (i : Nat) :
    HasTy E 0 Γ (.sort (.param i)) (.sort (.succ (.param i))) :=
  .sort Γ (.param i)

/-! ### 3.2 `hwf` at `n = 0`: INVERTED — `param 0` admitted, `zero`
refused -/

/-- `const 0 [param 0]` at `n = 0`: 02 §2 refuses `param 0` (`0 < 0`
is false); the landed `hwf` ADMITS it, because `eval (fun _ => none)
(.param 0) = none` discharges the first disjunct. The ascribed type
`.sort .zero` IS `instantiateLevels [.param 0] (.sort .zero)` by
unfolding (`instLevel _ .zero` is `rfl`; `famProp_head`'s
precedent). The ADMITTING half is not new: `famProp_head (n := 0)`
is the sealed instance at `famPropEnv` (00 §19.1 O-4). This one is
at `pinFamEnv`, whose member IS an arity where `famPropMember`'s is
not, so it is the instance a post-erratum-3 reader wants. -/
def hasTy_const_param_admitted_at_zero (Γ : LCtx) :
    HasTy pinFamEnv 0 Γ (.const 0 [.param 0]) (.sort .zero) :=
  .const Γ 0 [.param 0] ⟨.inductiveM, 1, .sort .zero, none⟩ pinFamEnv_lookup rfl
    (fun l hl => ⟨0, Or.inl (by
      cases hl with
      | head => rfl
      | tail _ h => nomatch h)⟩)

/-- LOCAL COPY of `hasTyConstWf` (`RcicParRedSR`, sealed; its one
consumer `hasTyConstMove` transports the field along `eqNList` and
never evaluates it), kept off the ParRedSR edge per this file's own import
discipline. Nine arms (fording, 00 §18.3 rule 2): `const`
reads, `conv` recurses, seven `nomatch`. Adds no inversion the tree
lacks; it makes the field readable from a module whose closure is
two files. -/
theorem hasTyConst_hwf {E : ResolvedEnv} {n : Nat} {r : Nat} {ls : List Level} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T → e = .const r ls →
    ∀ l ∈ ls, ∃ k, eval (fun _ => none) l = none ∨ k < n
  | _, _, _, .const _ _ _ _ _ _ hwf, heq => by
      injection heq with h1 h2; subst h1; subst h2; exact hwf
  | _, _, _, .conv _ _ _ _ h _, heq => hasTyConst_hwf h heq
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- `const r [zero]` at `n = 0` is untypable in EVERY environment —
even one whose member `r` has arity 1 and whose 02 §8 rule types it.
`zero` is the one level 02 §2 makes well formed at every `n`; the
landed `hwf` refuses it because `eval (fun _ => none) .zero = some 0`
fails the first disjunct and `k < 0` fails the second. -/
theorem hasTy_const_zero_refused_at_zero {E : ResolvedEnv} {Γ : LCtx}
    {r : Nat} {T : Expr Nat} (h : HasTy E 0 Γ (.const r [.zero]) T) : False :=
  match hasTyConst_hwf h rfl .zero (List.mem_cons_self Level.zero []) with
  | ⟨_, Or.inl hnone⟩ =>
      have hv : (some 0 : Option Nat) = none := hnone
      Option.noConfusion hv
  | ⟨k, Or.inr hlt⟩ => Nat.not_lt_zero k hlt

/-- SHARPNESS (Codex review of #3835): "mentions a parameter" is the
WRONG characterisation of `hwf` at `n = 0` — the predicate is
`eval (fun _ => none) l = none`, and `.imax (.param 0) .zero` mentions a
parameter yet evaluates, by `imax`'s lazy zero branch, so `hwf`
REFUSES it. Pinned by `rfl`; not sealed (an `example`, as §20.10's
sharpness pin). -/
example : eval (fun _ => none) (.imax (.param 0) .zero) = some 0 := rfl

/-! ### 3.3 `hwf` at `n ≥ 1`: VACUOUS — every level admitted -/

/-- At every positive `n`, EVERY level list of the right length is
admitted: `k := 0 < n` discharges the second disjunct without reading
the level. `param 5` at `n = 1` is the instance 02 §2 refuses. -/
def hasTy_const_anyLevel_admitted_at_succ (n : Nat) (Γ : LCtx) (l : Level) :
    HasTy pinFamEnv (n + 1) Γ (.const 0 [l]) (.sort .zero) :=
  .const Γ 0 [l] ⟨.inductiveM, 1, .sort .zero, none⟩ pinFamEnv_lookup rfl
    (fun _ _ => ⟨0, Or.inr (Nat.zero_lt_succ n)⟩)

/-- TYPE-④. "Every derivable constant's levels are bounded by `n`" —
the predicate the R-8 correction would make true — is FALSE on the
landed rule: `levelsBounded 1 [.param 5] = false` and the constant is
typed. -/
theorem hasTy_const_levelsBounded_false
    (h : ∀ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (r : Nat) (ls : List Level)
      (T : Expr Nat), HasTy E n Γ (.const r ls) T → levelsBounded n ls = true) :
    False :=
  have hv : (false : Bool) = true :=
    h pinFamEnv 1 [] 0 [.param 5] (.sort .zero)
      (hasTy_const_anyLevel_admitted_at_succ 0 [] (.param 5))
  Bool.noConfusion hv

/-- TYPE-④, the Sort side: "every derivable `sort l`'s level is
bounded by `n`" is FALSE on the landed rule (`levelBounded 0
(.param 0) = false`). -/
theorem hasTy_sort_levelBounded_false
    (h : ∀ (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l : Level) (T : Expr Nat),
      HasTy E n Γ (.sort l) T → levelBounded n l = true) : False :=
  have hv : (false : Bool) = true :=
    h emptyEnv 0 [] (.param 0) (.sort (.succ (.param 0)))
      (hasTy_sort_unbounded_at_zero [] 0)
  Bool.noConfusion hv

/-! ### 3.4 The ENTANGLEMENT: bounding subjects does not bound TYPES

`HasTy.conv` carries no typing of its target `B`; `Conv.sorts` needs
only `eqN l₁ l₂`; and `eqN .zero (.imax (.param i) .zero)` HOLDS at
every `ρ` (`refutEqN_imax_zero`, §0). So from ANY Prop-typed `A` the
untyped conversion yields `HasTy Γ A (.sort (.imax (.param i)
.zero))` at `n = 0`, whose level mentions an unbound parameter — and
the derivation below uses ONLY level-bounded subjects (`sort zero`,
`bvar`, `pi` at `imax (succ zero) zero`, then `conv` to `sort
zero`). This is why the R-8 correction, applied to `HasTy.sort` and
`HasTy.const` alone, would leave `hasTy_typeLevel_bounded_false`
REFUTED: bounding the levels of TYPES requires 02 §8's TYPED
conversion rule (`E;n;Γ ⊢ A ≈ B : sort u`), which the transcription
table in `RcicDeclarative` marks "quoted" and which, measured, drops
the `sort u` typing — F-05b's ring (00 §19.3), not F-04's. -/

/-- The untyped sort conversion at an unbound parameter, at
`n = 0`. -/
def conv_sorts_unbounded_at_zero {E : ResolvedEnv} (Γ : LCtx) (i : Nat) :
    Conv E 0 Γ (.sort .zero) (.sort (.imax (.param i) .zero)) :=
  .sorts Γ .zero (.imax (.param i) .zero) (fun _ρ => rfl)

/-- The closed Prop `Π (Q : Prop), Q` (`refutFamC`, §2), whose every
subject is level-bounded at `n = 0`, ascribed a sort mentioning
`param i` by one untyped conversion. -/
def hasTy_typeSort_unbounded_at_zero {E : ResolvedEnv} (Γ : LCtx) (i : Nat) :
    HasTy E 0 Γ refutFamC (.sort (.imax (.param i) .zero)) :=
  .conv Γ refutFamC (.sort .zero) (.sort (.imax (.param i) .zero))
    (refutFamC_isProp Γ) (conv_sorts_unbounded_at_zero Γ i)

/-- TYPE-④, `EnvWf`-conditioned and `Γ`-quantified: "under a
well-formed environment, every type's ascribed sort level is bounded
by `n`" is FALSE at `emptyEnv` (`EnvWf.empty`) and `Γ = []` — so
neither `EnvWf` nor `CtxWf` conditioning rescues it. The failing
statement of any "types are level-bounded" claim, written out; it
survives the R-8 correction unchanged, because no subject in its
witness is unbounded. -/
theorem hasTy_typeLevel_bounded_false
    (h : ∀ (E : ResolvedEnv) (n : Nat), EnvWf E n →
      ∀ (Γ : LCtx) (A : Expr Nat) (u : Level),
        HasTy E n Γ A (.sort u) → levelBounded n u = true) : False :=
  have hv : (false : Bool) = true :=
    h emptyEnv 0 (.empty 0) [] refutFamC (.imax (.param 9) .zero)
      (hasTy_typeSort_unbounded_at_zero [] 9)
  Bool.noConfusion hv

/-! ## §4 (R-conv) Untyped conversion: a discarded argument and an
untyped `HasTy.conv` target.

Annex 22 B-c Batch A. Two sentences of `00` §19.3's dilemma, compiled.
NONE of the four names refutes a `00` §19.2 row, and none refutes
route (c). -/

/-- Witness both refutations consume: the β-redex
`app (lam (sort 0) (sort l)) (bvar 0)` is untypable in the empty
context, because inversion at `.app` yields a typing of `bvar 0`
and `hasTyBvarEmptyFalse` refuses that. `l` is universal so A2
(`l := .zero`) and A4 (`l := .succ .zero`) share this lemma. -/
theorem betaRedex_bvar0_untypable {E : ResolvedEnv} {n : Nat}
    {l : Level} {T : Expr Nat}
    (h : HasTy E n [] (.app (.lam (.sort .zero) (.sort l)) (.bvar 0)) T) :
    False :=
  let ⟨_A, _B, _hf, ha, _hc⟩ := hasTyAppInv h rfl
  hasTyBvarEmptyFalse ha

/-- LOCAL COMPILED COPY OF A KNOWN FACT — subject expansion fails in
every calculus with untyped β, because a discarded ill-typed argument
leaves no trace in the reduct. NOT a finding. What it buys is that
`00` §19.3's sentence "plus subject expansion, which is on no ledger"
stops being a claim a reader must trust and becomes a name a reader
greps. -/
theorem subjectExpansion_false
    (h : ∀ (E : ResolvedEnv) (n : Nat), EnvWf E n →
      ∀ (Γ : LCtx) (a b T : Expr Nat), CtxWf E n Γ →
        Step E n Γ a b → HasTy E n Γ b T → HasTy E n Γ a T) :
    False :=
  betaRedex_bvar0_untypable
    (h emptyEnv 0 (.empty 0) [] _ _ (.sort (.succ .zero)) .nil
      (.beta [] (.sort .zero) (.sort .zero) (.bvar 0))
      (.sort [] .zero))

/-- Witness `hasTy_typeSorted_false` consumes. `HasTy.conv`'s target
`B` carries no typing premise (`RcicDeclarative.lean:1133`), which is
the whole content of the witness: `.sort 0` is ascribed the untypable
β-redex `app (lam (sort 0) (sort 1)) (bvar 0)` by converting along
the untyped `Conv` of that redex. -/
def hasTy_convTarget_untypable :
    HasTy emptyEnv 0 []
      (.sort .zero)
      (.app (.lam (.sort .zero) (.sort (.succ .zero))) (.bvar 0)) :=
  .conv [] (.sort .zero) (.sort (.succ .zero)) _
    (.sort [] .zero)
    (.symm [] _ _
      (.step [] _ _
        (.beta [] (.sort .zero) (.sort (.succ .zero)) (.bvar 0))))

/-- M-001 witness for E-ConvTy. Named `hasTy_typeSorted_false` WITHOUT
the word validity, so the `00` §20.8 S-2 grep stays empty on a
declaration name. `02` §8's conversion rule is TYPED
(`E;n;Γ ⊢ A ≈ B : sort u`, `02_DECLARATIVE_THEORY.md:248`) and `02`
§10 is typed at every clause (`:281-289`, proof irrelevance
`:311-320`), so "every type is sorted" is a THEOREM of `02` and is
FALSE of the landed `HasTy`, whose `Conv` is untyped
(`RcicDeclarative.lean:1156`) and whose `HasTy.conv` target is
untyped by construction (`:1133`). The gap between the two is
exactly what E-ConvTy asks a ruling about, and this theorem is its
compiled witness. -/
theorem hasTy_typeSorted_false
    (h : ∀ (E : ResolvedEnv) (n : Nat), EnvWf E n →
      ∀ (Γ : LCtx) (e T : Expr Nat), CtxWf E n Γ →
        HasTy E n Γ e T → Σ' (u : Level), HasTy E n Γ T (.sort u)) :
    False :=
  let ⟨_u, hT⟩ := h emptyEnv 0 (.empty 0) [] _ _ .nil
    hasTy_convTarget_untypable
  betaRedex_bvar0_untypable hT

end Rcic.Declarative
