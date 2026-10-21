import rcic.RcicAnnInfer
import rcic.RcicLevelCalc

/-!
# M1-c (i) — the declarative typed calculus on the annotated copy

`HasTyA` / `ConvA` are 02 §8 / §10 on `ExprA`, TYPED (`Γ ⊢ a ≡ b : A`, the
R-TypedRules shape of the typed face), with two arms reading a binder sort off
the SUBJECT where the tree's arm takes it from a derivation: `pi` reads `u`, `v`
off `.pi A u B v`, `lam` reads its domain sort off `.lam A u body`. The
derivation still has to DERIVE `A : sort u` for the annotated `u`: annotations
are validated by typing, never trusted. Ported from `RcicProbeAnn.lean` §(2)
(I-3e-38, `wip/rcic-face`) with three changes, each named: (i) the environment
is the twin `ResolvedEnvA`, so `const`/`delta`/`consts` read `mtypeA`/`bodyA`
directly and the probe's erasure equations (its measured cost) are gone; (ii)
ι is the 05-owned interface `IotaIfaceA`, a parameter — a FUNCTION `fn` for the
algorithm, whose GRAPH `rel` the declarative side quotes; (iii) literals expand on the copy (`natExpandA`).

The `conv`/`tyConv` arms carry the tree's coherence premises VERBATIM
(`hAl`, `hlu`, `hB`): whether the annotation makes `hlu` redundant is a
measurement for M2's fundamental theorem, not an assumption of the
definition (R-RingAnnotated: it does not, by itself). The `lam`/`pi`
congruences relate annotations by `=ₙ` (R-TypedRules (6), M2-e (5); until then
they kept the SAME annotation on both sides). An annotation is still read off
the subject and validated by typing, never derived from a conversion of
types — `=ₙ` is a fact of the level calculus, decidable on its own, the same
datum `EqKA.pi` carries (`hu`, `hv`) and `sorts`/`consts` already relate —
so this does not reopen the ring. Without it the copy is INCOMPLETE for the
kernel on its most basic polymorphic use: `consts` at `List.{0}` and
`List.{max 0 0}` needs its right side typed at the LEFT's instantiated type,
i.e. a conversion between two pis whose annotations are `succ 0` and
`succ (max 0 0)`, which no rule with syntactically equal annotations provides
(measured, M2-e (5)); and the level-irrelevance lemma (two `=ₙ`
instantiations of one typed term are convertible), which the semantic
environment of a polymorphic member needs, is derivable only with it.

Nothing here is claimed sound against the tree's `HasTy`/`Conv`: the tree's
`Conv` is total (R-ConvCollapse), so such a bridge carries no information;
the bridge is M3's.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- 05's ι, as the copy's PARAMETER: the partial head-step FUNCTION the
    algorithm runs (`hStepFnA`). The declarative calculus quotes its graph AT
    THE POSITION THE HEAD STEP CONSULTS IT (`ConvA.iota` below, through
    `IotaIfaceA.rel`). `hStepFnA` asks `fn` only for an application whose head
    is not a λ and does not step (`hStepFnA_app_nonlam`); a graph quoted
    anywhere else — `fn` relating two stuck constants, two λs, an application
    whose head steps first — would be a declarative ι step the algorithm never
    takes: `whnfA` would leave both sides unchanged, `AlgEq` could not relate
    the two heads, and `ConvA ⊆ AlgEq` (M2) would fail (Codex P1 on #6107,
    both rounds). So a declarative ι step is BY DEFINITION one the head step
    takes, and the algorithm's ι is complete for it. What M2 asks of `fn`
    beyond this is stated there as named hypotheses on the interface, and
    typing of the reduct is NOT among the sufficient ones: a `fn` with
    `fn e = some e` on a well-typed stuck application (`loopIotaA` below) is
    positional, lift-stable and types its reducts, yet `whnfA` answers `none`
    at every fuel, so no `AlgEq` relates `e` to itself at a non-propositional
    type and `ConvA ⊆ AlgEq` fails (Codex P1 on #6107, third round). What
    excludes it is SEMANTIC, not a measure on `fn` — real ι has no
    well-founded measure of its own, and termination of ι together with β is
    the fundamental theorem's CONCLUSION, not its premise: (a) ι fires only on
    constant-headed spines, so variable-headed neutrals stay stuck (M2-c's
    reflection lemma needs exactly that), and (b) every opaque constant
    inhabits the relation at its type (semantic environment well-formedness,
    the fundamental theorem's hypothesis, M2-e). Under (b) a looping `fn` is
    contradictory: the head constant's membership at its pi type puts the
    stuck application into the relation at the codomain, which demands a
    normal form. (b) is where the recursor's content enters (M2-f / M3). -/
structure IotaIfaceA where
  fn : IotaFnA

/-- the declarative ι relation: the function's graph, where the head step
    realises it (so it reads `E` and `Γ`: whether the head is stuck is theirs). -/
def IotaIfaceA.rel (I : IotaIfaceA) (E : ResolvedEnvA) (Γ : LCtxA) (e e' : ExprA) : Prop :=
  I.fn e = some e' ∧ hStepFnA E I.fn Γ e = some e'

theorem IotaIfaceA.rel.graph {I : IotaIfaceA} {E : ResolvedEnvA} {Γ : LCtxA} {e e' : ExprA}
    (h : I.rel E Γ e e') : I.fn e = some e' := h.1

/-- what the fundamental theorem's ι arm consumes: a declarative ι step IS a
    head step. -/
theorem IotaIfaceA.rel.exec {I : IotaIfaceA} {E : ResolvedEnvA} {Γ : LCtxA} {e e' : ExprA}
    (h : I.rel E Γ e e') : hStepFnA E I.fn Γ e = some e' := h.2

/-- at the position the head step consults `fn` — an application whose head is
    not a λ and does not step, off the struct position (W-1 (e)) — every value of `fn` is a
    declarative ι step. -/
theorem IotaIfaceA.rel_of_pos (I : IotaIfaceA) (E : ResolvedEnvA) (Γ : LCtxA) {f x e' : ExprA}
    (hnl : ∀ A u b, f ≠ .lam A u b) (hf : hStepFnA E I.fn Γ f = none)
    (hp : structPosA E f = false) (h : I.fn (.app f x) = some e') : I.rel E Γ (.app f x) e' :=
  ⟨h, hStepFnA_app_iota E I.fn Γ hnl hf hp h⟩

/-- ι fires only on spines headed by a RECURSOR of `E`, AT THE RECURSOR'S TELESCOPE
    ARITY (05 §11–13: the ι rules are the recursors', on full applications; the
    count is `piCountA m.mtypeA`, the Π-binders of the stored type, not `m.arity`).
    Stronger than `IotaConstHeadA` (`RcicAnnLRNeut`): what makes every other
    constant's spine stuck (M2-e (4)), and — M2-f (1) — what keeps every spine
    strictly below the major normal under substitution, since `IotaSubstA` states
    only success preservation. -/
def IotaRecHeadA (E : ResolvedEnvA) (I : IotaIfaceA) : Prop :=
  ∀ e e', I.fn e = some e' →
    ∃ r ls m, (appsSpineA e).1 = .const r ls ∧ E.members r = some m ∧ m.mclass = .recursorM ∧
      (appsSpineA e).2.length = piCountA m.mtypeA

/-- the trivial interface: no ι at all (the λ-profile, DT-020's shape). -/
def noIotaA : IotaIfaceA where
  fn := fun _ => none

theorem noIotaA_rel_false {E : ResolvedEnvA} {Γ : LCtxA} {e e' : ExprA}
    (h : noIotaA.rel E Γ e e') : False := Option.noConfusion h.1

theorem noIotaA_recHead (E : ResolvedEnvA) : IotaRecHeadA E noIotaA :=
  fun _ _ h => Option.noConfusion h

/-- THE LOOP (Codex P1 on #6107, third round), pinned: every term steps to
    itself. It is positional (`loopIotaA_rel`: at a variable-headed stuck
    application the head step IS this `fn`), it commutes with every lift and
    substitution, and it types its reducts (they are the terms themselves) —
    and where it fires nothing has a normal form (`loopIotaA_no_whnf`). The
    hypotheses that exclude it are the semantic ones named on `IotaIfaceA`;
    no condition on the graph alone does. -/
def loopIotaA : IotaIfaceA where
  fn := fun e => some e

theorem loopIotaA_rel (E : ResolvedEnvA) (A x : ExprA) :
    loopIotaA.rel E [.assumption A] (.app (.bvar 0) x) (.app (.bvar 0) x) :=
  ⟨rfl, by
    rw [hStepFnA_app_nonlam E loopIotaA.fn _ x (fun _ _ _ h => ExprA.noConfusion h)]
    rfl⟩

theorem loopIotaA_no_whnf (E : ResolvedEnvA) (A x : ExprA) :
    ∀ fuel, whnfA E loopIotaA.fn [.assumption A] fuel (.app (.bvar 0) x) = none
  | 0 => by simp only [whnfA, (loopIotaA_rel E A x).exec]
  | fuel + 1 => by
      simp only [whnfA, (loopIotaA_rel E A x).exec]
      exact loopIotaA_no_whnf E A x fuel

mutual

/-- Typing on the copy, 02 §8 arm for arm; `pi`/`lam` read the annotation. -/
inductive HasTyA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    LCtxA → ExprA → ExprA → Type
  | sort (Γ : LCtxA) (l : Level) :
      HasTyA E I n Γ (.sort l) (.sort (.succ l))
  | bvar (Γ : LCtxA) (i : Nat) (A : ExprA) (u : Level)
      (h : lookupTypeA Γ i = some A) (hA : HasTyA E I n Γ A (.sort u)) :
      HasTyA E I n Γ (.bvar i) A
  | const (Γ : LCtxA) (r : Nat) (ls : List Level) (m : CheckedMemberA) (u : Level)
      (hres : E.members r = some m) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true)
      (hT : HasTyA E I n Γ (instantiateLevelsA ls m.mtypeA) (.sort u)) :
      HasTyA E I n Γ (.const r ls) (instantiateLevelsA ls m.mtypeA)
  /-- THE ANNOTATION'S FIRST ARM: `u` and `v` are the SUBJECT's, and the
      derivation must derive them. -/
  | pi (Γ : LCtxA) (A : ExprA) (u : Level) (B : ExprA) (v : Level)
      (hA : HasTyA E I n Γ A (.sort u))
      (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v)) :
      HasTyA E I n Γ (.pi A u B v) (.sort (.imax u v))
  /-- THE ANNOTATION'S SECOND ARM: the DOMAIN sort is the subject's; the
      codomain sort `v` is a constructor index (the shape annotates the lam's
      domain only). -/
  | lam (Γ : LCtxA) (A : ExprA) (u : Level) (body B : ExprA) (v : Level)
      (hA : HasTyA E I n Γ A (.sort u))
      (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
      (hbody : HasTyA E I n (.assumption A :: Γ) body B) :
      HasTyA E I n Γ (.lam A u body) (.pi A u B v)
  | app (Γ : LCtxA) (f a A B : ExprA) (u v w : Level)
      (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
      (hTy : HasTyA E I n Γ (instantiate0A a B) (.sort w))
      (hf : HasTyA E I n Γ f (.pi A u B v)) (ha : HasTyA E I n Γ a A) :
      HasTyA E I n Γ (.app f a) (instantiate0A a B)
  | letE (Γ : LCtxA) (A : ExprA) (u w : Level) (value B body : ExprA)
      (hA : HasTyA E I n Γ A (.sort u))
      (hv : HasTyA E I n Γ value A)
      (hTy : HasTyA E I n Γ (instantiate0A value B) (.sort w))
      (hb : HasTyA E I n (.letBinding A value :: Γ) body B) :
      HasTyA E I n Γ (.letE A value body) (instantiate0A value B)
  /-- the tree's M-001 deviation preserved: the literal is typed at the type
      of its expansion. -/
  | lit (Γ : LCtxA) (t : Nat) (T : ExprA)
      (hexp : HasTyA E I n Γ (natExpandA t) T) :
      HasTyA E I n Γ (.lit t) T
  /-- `conv`, the tree's VERBATIM, `hlu` included (see the file comment). -/
  | conv (Γ : LCtxA) (e A B : ExprA) (l u : Level)
      (h : HasTyA E I n Γ e A)
      (hAl : HasTyA E I n Γ A (.sort l)) (hlu : eqN l u)
      (hB : HasTyA E I n Γ B (.sort u))
      (hc : ConvA E I n Γ A B (.sort u)) : HasTyA E I n Γ e B

/-- Typed conversion on the copy, 02 §10 + §9 as typed rules (R-TypedRules). -/
inductive ConvA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    LCtxA → ExprA → ExprA → ExprA → Type
  | refl (Γ : LCtxA) (a A : ExprA) (h : HasTyA E I n Γ a A) :
      ConvA E I n Γ a a A
  | symm (Γ : LCtxA) (a b A : ExprA) (h : ConvA E I n Γ a b A) :
      ConvA E I n Γ b a A
  | trans (Γ : LCtxA) (a b c A : ExprA)
      (h1 : ConvA E I n Γ a b A) (h2 : ConvA E I n Γ b c A) :
      ConvA E I n Γ a c A
  | beta (Γ : LCtxA) (A : ExprA) (u : Level) (body arg B : ExprA)
      (hA : HasTyA E I n Γ A (.sort u))
      (hbody : HasTyA E I n (.assumption A :: Γ) body B)
      (harg : HasTyA E I n Γ arg A)
      (hred : HasTyA E I n Γ (instantiate0A arg body) (instantiate0A arg B)) :
      ConvA E I n Γ (.app (.lam A u body) arg) (instantiate0A arg body)
        (instantiate0A arg B)
  | zeta (Γ : LCtxA) (A value body B : ExprA) (u : Level)
      (hA : HasTyA E I n Γ A (.sort u))
      (hv : HasTyA E I n Γ value A)
      (hb : HasTyA E I n (.letBinding A value :: Γ) body B)
      (hred : HasTyA E I n Γ (instantiate0A value body) (instantiate0A value B)) :
      ConvA E I n Γ (.letE A value body) (instantiate0A value body)
        (instantiate0A value B)
  | zetaLocal (Γ : LCtxA) (i : Nat) (A v : ExprA)
      (hval : lookupValueA Γ i = some v)
      (hty : lookupTypeA Γ i = some A)
      (hv : HasTyA E I n Γ v A) :
      ConvA E I n Γ (.bvar i) v A
  | delta (Γ : LCtxA) (r : Nat) (ls : List Level) (m : CheckedMemberA) (b : ExprA)
      (hres : E.members r = some m) (hbody : m.bodyA = some b)
      (htr : transparent m.mclass = true)
      (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true)
      (hb : HasTyA E I n Γ (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA)) :
      ConvA E I n Γ (.const r ls) (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA)
  /-- ι through the interface — its graph where the head step realises it, so
      executable by definition; both endpoints typed at `T` (R-TypedRules (4):
      the right-hand typing is an M-001 deviation from 02 §9's bare ι line,
      NAMED here, discharged when the rows close). -/
  | iota (Γ : LCtxA) (lhs rhs T : ExprA)
      (h : I.rel E Γ lhs rhs)
      (hlhs : HasTyA E I n Γ lhs T)
      (hrhs : HasTyA E I n Γ rhs T) :
      ConvA E I n Γ lhs rhs T
  /-- W-1 (e): ι AT A STRUCT GROUP, as `main` has it. There the head step is the struct arm's at
      every major (`structPosA`: ι is not consulted), so `iota` above, whose relation asks that ι's
      contractum be the head step's, does not fire. This rule is ι there: a recursor spine at its
      major (`hrec`) where the struct arm answers (`hs`, its reduct `e`) converts to ι's contractum
      (`h`, the minor at the constructor's fields), both sides typed at `T`. It carries a conversion
      from that contractum to the arm's reduct (`hcv`): the relation goes through the struct arm's
      step, and erasure keeps only `main`'s ι (README W-1 (e)-0). -/
  | structIota (Γ : LCtxA) (f a rhs e T : ExprA)
      (hrec : recAtMajorA E f = true) (hs : structArmA E f a = some e)
      (h : I.fn (.app f a) = some rhs)
      (hlhs : HasTyA E I n Γ (.app f a) T)
      (hrhs : HasTyA E I n Γ rhs T)
      (hcv : ConvA E I n Γ rhs e T) :
      ConvA E I n Γ (.app f a) rhs T
  | lit (Γ : LCtxA) (t : Nat) (T : ExprA)
      (hexp : HasTyA E I n Γ (natExpandA t) T) :
      ConvA E I n Γ (.lit t) (natExpandA t) T
  /-- `hB` is an M-001 deviation from 02 §10's bare congruence (R-TypedRules (5),
      M2-e (2)): the codomain's typing, as `HasTyA.app` already carries it. Without
      it the fundamental theorem's `app` arm at a PROPOSITIONAL pi cannot reach the
      codomain's relation (the pi's relation is structure-free there,
      R-PropOutOfTower) short of uniqueness of types — a row. Derivable whenever
      the judgment is well-formed; NAMED here, discharged when the rows close. -/
  | app (Γ : LCtxA) (f g a b A B : ExprA) (u v : Level)
      (h1 : ConvA E I n Γ f g (.pi A u B v)) (h2 : ConvA E I n Γ a b A)
      (hB : HasTyA E I n (.assumption A :: Γ) B (.sort v))
      (hrt : HasTyA E I n Γ (.app g b) (instantiate0A a B)) :
      ConvA E I n Γ (.app f a) (.app g b) (instantiate0A a B)
  /-- the annotations related by `=ₙ` (R-TypedRules (6), file comment); the
      right side typed at the LEFT's pi, as the kernel types it. -/
  | lam (Γ : LCtxA) (A A' b b' B : ExprA) (u u' v : Level)
      (hu : eqN u u')
      (hA : ConvA E I n Γ A A' (.sort u))
      (hb : ConvA E I n (.assumption A :: Γ) b b' B)
      (hrt : HasTyA E I n Γ (.lam A' u' b') (.pi A u B v)) :
      ConvA E I n Γ (.lam A u b) (.lam A' u' b') (.pi A u B v)
  /-- the annotations related by `=ₙ` (R-TypedRules (6)); the right pi typed at
      the LEFT's sort. -/
  | pi (Γ : LCtxA) (A A' B B' : ExprA) (u u' v v' : Level)
      (hu : eqN u u') (hv : eqN v v')
      (hA : ConvA E I n Γ A A' (.sort u))
      (hB : ConvA E I n (.assumption A :: Γ) B B' (.sort v))
      (hrt : HasTyA E I n Γ (.pi A' u' B' v') (.sort (.imax u v))) :
      ConvA E I n Γ (.pi A u B v) (.pi A' u' B' v') (.sort (.imax u v))
  | letE (Γ : LCtxA) (A A' v v' b b' B : ExprA) (u : Level)
      (hA : ConvA E I n Γ A A' (.sort u)) (hv : ConvA E I n Γ v v' A)
      (hb : ConvA E I n (.letBinding A v :: Γ) b b' B)
      (hrt : HasTyA E I n Γ (.letE A' v' b') (instantiate0A v B)) :
      ConvA E I n Γ (.letE A v b) (.letE A' v' b') (instantiate0A v B)
  | sorts (Γ : LCtxA) (l₁ l₂ : Level) (h : eqN l₁ l₂) :
      ConvA E I n Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁))
  | consts (Γ : LCtxA) (r : Nat) (ls ls' : List Level) (m : CheckedMemberA)
      (hres : E.members r = some m)
      (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true)
      (hwf' : levelsBounded n ls' = true)
      (h : eqNList ls ls')
      (hrt : HasTyA E I n Γ (.const r ls') (instantiateLevelsA ls m.mtypeA)) :
      ConvA E I n Γ (.const r ls) (.const r ls') (instantiateLevelsA ls m.mtypeA)
  | eta (Γ : LCtxA) (f A B : ExprA) (u v : Level)
      (h : HasTyA E I n Γ f (.pi A u B v))
      (hrt : HasTyA E I n Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) (.pi A u B v)) :
      ConvA E I n Γ (.lam A u (.app (liftA 0 1 f) (.bvar 0))) f (.pi A u B v)
  /-- proof irrelevance, 02 §10's rule: the proposition is typed at `sort 0`
      — a DERIVATION, on the declarative side; the algorithm will key the
      same clause on `inferSortA`, and that the two agree is M2's. -/
  | irr (Γ : LCtxA) (P p q : ExprA)
      (hP : HasTyA E I n Γ P (.sort .zero))
      (hp : HasTyA E I n Γ p P) (hq : HasTyA E I n Γ q P) :
      ConvA E I n Γ p q P
  /-- `tyConv`, the tree's VERBATIM, both coherence premises included. -/
  | tyConv (Γ : LCtxA) (a b A A' : ExprA) (l l' u : Level)
      (h : ConvA E I n Γ a b A)
      (hAl : HasTyA E I n Γ A (.sort l)) (hlu : eqN l u)
      (hA'l : HasTyA E I n Γ A' (.sort l')) (hl'u : eqN l' u)
      (hA : ConvA E I n Γ A A' (.sort u)) :
      ConvA E I n Γ a b A'

end

/-- the ι rule's redex is a recursor spine of `E` at exact arity ON THE REDEXES `E` TYPES:
    what context conversion and level irrelevance consume (M2-f (4b)). It follows from
    `IotaRecHeadA E I` (`iotaRecHeadTypedA_of`), and it holds at a PREFIX of an environment
    where `IotaRecHeadA` does (`iotaRecHeadTypedA_prefix`: a typed redex's head is a member of
    the prefix) — where the full `IotaRecHeadA` may fail, the interface firing on a later
    recursor. -/
def IotaRecHeadTypedA (E : ResolvedEnvA) (I : IotaIfaceA) : Prop :=
  ∀ (n : Nat) (Γ : LCtxA) (e e' T : ExprA), I.fn e = some e' → Nonempty (HasTyA E I n Γ e T) →
    ∃ r ls m, (appsSpineA e).1 = .const r ls ∧ E.members r = some m ∧ m.mclass = .recursorM ∧
      (appsSpineA e).2.length = piCountA m.mtypeA

theorem iotaRecHeadTypedA_of {E : ResolvedEnvA} {I : IotaIfaceA} (hR : IotaRecHeadA E I) :
    IotaRecHeadTypedA E I :=
  fun _ _ e e' _ h _ => hR e e' h

/-! ## non-vacuity: the copy is inhabited, on a pi with two annotated sorts -/

/-- `Π (x : Sort 0), Sort 0 : Sort 2` — `pinPiA` typed, both sorts derived. -/
def pinPiA_ty (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    HasTyA E I n [] pinPiA (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (.sort [] .zero) (.sort _ .zero)

/-- the identity on `Sort 0`, typed at the annotated pi: `λ (x : Sort 0). x`. -/
def idSort0_ty (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    HasTyA E I n [] (.lam (.sort .zero) (.succ .zero) (.bvar 0))
      (.pi (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)) :=
  .lam [] (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero) (.succ .zero)
    (.sort [] .zero)
    (.sort _ .zero)
    (.bvar _ 0 (.sort .zero) (.succ .zero) rfl (.sort _ .zero))

/-- the β-redex `(λ (x : Sort 1). x) (Sort 0)` converts to `Sort 0` at `Sort 1`:
    a `ConvA.beta` whose four typing premises are `sort`/`bvar` leaves (the
    lam's domain `Sort 1` carries its sort `2`; the argument `Sort 0 : Sort 1`). -/
def idSort1_beta (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    ConvA E I n [] (.app (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)) (.sort .zero))
      (.sort .zero) (.sort (.succ .zero)) :=
  .beta [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0) (.sort .zero) (.sort (.succ .zero))
    (.sort [] (.succ .zero))
    (.bvar _ 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl (.sort _ (.succ .zero)))
    (.sort [] .zero)
    (.sort [] .zero)

/-- the annotation is CHECKED, not trusted: `pinPiAlt` (domain sort annotated
    `0`) cannot be typed at any sort by the `pi` arm's first premise alone
    (`Sort 0 : Sort 0` has no derivation whose type is literally `sort zero`
    without `conv`); stated here as the SHAPE the derivation would need, not
    as a theorem — `¬ HasTyA … pinPiAlt …` needs the inversion lemmas of M2. -/
example : pinPiAlt = .pi (.sort .zero) .zero (.sort .zero) (.succ .zero) := rfl

/-- a typed term's de Bruijn indices are all bound by its context — typing gives scope
    (R-NoDeltaRec-4d: the δ-reached field's `idx` need their bound as evidence). -/
theorem lookupTypeA_lt_length {Γ : LCtxA} {i : Nat} {A : ExprA} (h : lookupTypeA Γ i = some A) :
    i < Γ.length := by
  by_cases hi : i < Γ.length
  · exact hi
  · unfold lookupTypeA at h
    rw [List.get?_eq_none.mpr (by omega : Γ.length ≤ i)] at h
    exact Option.noConfusion h

/-- `&&`-introduction at `= true` (the `Prop`-valued `Bool.and_eq_true` does not compose as
    `Eq.mpr` cleanly in mutual recursion blocks; this tiny helper does). -/
theorem andB_true {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]; rfl

/-- `liftA` never un-bounds a scope: a term whose bvars sit under `c` binders keeps them under
    `c + k` after any `liftA` (R-NoDeltaRec-4d). -/
theorem boundOkB_liftA (d k : Nat) :
    ∀ (c : Nat) (e : ExprA), boundOkB c e = true → boundOkB (c + k) (liftA d k e) = true
  | c, .bvar i, h => by
      have hi := of_decide_eq_true h
      show boundOkB (c + k) (liftA d k (.bvar i)) = true
      simp only [liftA, boundOkB]
      by_cases hd : d ≤ i
      · simp only [if_pos hd]; exact decide_eq_true (by omega)
      · simp only [if_neg hd]; exact decide_eq_true (by omega)
  | _, .sort _, _ => rfl
  | _, .const _ _, _ => rfl
  | c, .app f x, h => by
      rw [liftA_app]
      exact andB_true (boundOkB_liftA d k c f (boolAnd_left h))
        (boundOkB_liftA d k c x (boolAnd_right h))
  | c, .lam a u b, h => by
      rw [liftA_lam]
      exact andB_true (boundOkB_liftA d k c a (boolAnd_left h))
        (by rw [Nat.add_right_comm]; exact boundOkB_liftA (d + 1) k (c + 1) b (boolAnd_right h))
  | c, .pi a u b v, h => by
      rw [liftA_pi]
      exact andB_true (boundOkB_liftA d k c a (boolAnd_left h))
        (by rw [Nat.add_right_comm]; exact boundOkB_liftA (d + 1) k (c + 1) b (boolAnd_right h))
  | c, .letE a w b, h => by
      rw [liftA_letE]
      exact andB_true
        (andB_true (boundOkB_liftA d k c a (boolAnd_left (boolAnd_left h)))
          (boundOkB_liftA d k c w (boolAnd_right (boolAnd_left h))))
        (by rw [Nat.add_right_comm]; exact boundOkB_liftA (d + 1) k (c + 1) b (boolAnd_right h))
  | _, .lit _, _ => rfl

/-- instantiating a `bvar < c`-bound position keeps scope: the substituted index is replaced by
    a `c`-bound term and the rest shift down (R-NoDeltaRec-4d). -/
theorem boundOkB_instantiateA (d : Nat) :
    ∀ (c : Nat) (e : ExprA) (r : ExprA),
      d ≤ c → boundOkB (c + 1) e = true → boundOkB c r = true →
      boundOkB c (instantiateA d r e) = true
  | c, .bvar i, r, hd, h, hr => by
      have hi := of_decide_eq_true h
      show boundOkB c (instantiateA d r (.bvar i)) = true
      unfold instantiateA
      by_cases he : i = d
      · simp only [if_pos he]; exact hr
      · simp only [if_neg he]
        by_cases hlt : d < i
        · simp only [if_pos hlt]; exact decide_eq_true (by omega)
        · simp only [if_neg hlt]; exact decide_eq_true (by omega)
  | _, .sort _, _, _, _, _ => rfl
  | _, .const _ _, _, _, _, _ => rfl
  | c, .app f x, r, hd, h, hr => by
      show boundOkB c (.app (instantiateA d r f) (instantiateA d r x)) = true
      exact andB_true (boundOkB_instantiateA d c f r hd (boolAnd_left h) hr)
        (boundOkB_instantiateA d c x r hd (boolAnd_right h) hr)
  | c, .lam a u b, r, hd, h, hr => by
      show boundOkB c (.lam (instantiateA d r a) u (instantiateA (d + 1) (liftA 0 1 r) b)) = true
      exact andB_true (boundOkB_instantiateA d c a r hd (boolAnd_left h) hr)
        (boundOkB_instantiateA (d + 1) (c + 1) b (liftA 0 1 r) (by omega) (boolAnd_right h)
          (boundOkB_liftA 0 1 c r hr))
  | c, .pi a u b v, r, hd, h, hr => by
      show boundOkB c (.pi (instantiateA d r a) u (instantiateA (d + 1) (liftA 0 1 r) b) v) = true
      exact andB_true (boundOkB_instantiateA d c a r hd (boolAnd_left h) hr)
        (boundOkB_instantiateA (d + 1) (c + 1) b (liftA 0 1 r) (by omega) (boolAnd_right h)
          (boundOkB_liftA 0 1 c r hr))
  | c, .letE a w b, r, hd, h, hr => by
      show boundOkB c (.letE (instantiateA d r a) (instantiateA d r w)
        (instantiateA (d + 1) (liftA 0 1 r) b)) = true
      exact andB_true
        (andB_true (boundOkB_instantiateA d c a r hd (boolAnd_left (boolAnd_left h)) hr)
          (boundOkB_instantiateA d c w r hd (boolAnd_right (boolAnd_left h)) hr))
        (boundOkB_instantiateA (d + 1) (c + 1) b (liftA 0 1 r) (by omega) (boolAnd_right h)
          (boundOkB_liftA 0 1 c r hr))
  | _, .lit _, _, _, _, _ => rfl

/-- `instantiateLevelsA` does not move de Bruijn indices — `boundOkB` is untouched. -/
theorem boundOkB_instantiateLevelsA (ls : List Level) :
    ∀ (c : Nat) (e : ExprA), boundOkB c (instantiateLevelsA ls e) = boundOkB c e
  | _, .bvar _ => rfl
  | _, .sort _ => rfl
  | _, .const _ _ => rfl
  | c, .app f x => by
      show boundOkB c (.app (instantiateLevelsA ls f) (instantiateLevelsA ls x)) =
        boundOkB c (.app f x)
      simp only [boundOkB, boundOkB_instantiateLevelsA ls]
  | c, .lam a u b => by
      show boundOkB c (.lam (instantiateLevelsA ls a) u (instantiateLevelsA ls b)) =
        boundOkB c (.lam a u b)
      simp only [boundOkB, boundOkB_instantiateLevelsA ls]
  | c, .pi a u b v => by
      show boundOkB c (.pi (instantiateLevelsA ls a) u (instantiateLevelsA ls b) v) =
        boundOkB c (.pi a u b v)
      simp only [boundOkB, boundOkB_instantiateLevelsA ls]
  | c, .letE a w b => by
      show boundOkB c (.letE (instantiateLevelsA ls a) (instantiateLevelsA ls w)
        (instantiateLevelsA ls b)) = boundOkB c (.letE a w b)
      simp only [boundOkB, boundOkB_instantiateLevelsA ls]
  | _, .lit _ => rfl

mutual

/-- a typed expression is scope-bounded by its context — every free `bvar` of `e` sits under
    a Γ-binder (`boundOkB Γ.length`, R-NoDeltaRec-4d). `HasTyA`/`ConvA` are mutual, so the
    scope lemma is mutual — the same shape as `hasTyA_constsIn`. -/
theorem hasTyA_boundOk {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    {Γ : LCtxA} → {e T : ExprA} → HasTyA E I n Γ e T → boundOkB Γ.length e = true
  | _, _, _, .sort _ _ => rfl
  | _, _, _, .bvar _ i _ _ h _ => by
      exact decide_eq_true (lookupTypeA_lt_length h)
  | _, _, _, .const _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, .pi _ _ _ _ _ hA hB => by
      exact andB_true (hasTyA_boundOk hA) (hasTyA_boundOk hB)
  | _, _, _, .lam _ _ _ _ _ _ hA _ hbody => by
      exact andB_true (hasTyA_boundOk hA) (hasTyA_boundOk hbody)
  | _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf ha => by
      exact andB_true (hasTyA_boundOk hf) (hasTyA_boundOk ha)
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv _ hb => by
      exact andB_true (andB_true (hasTyA_boundOk hA) (hasTyA_boundOk hv)) (hasTyA_boundOk hb)
  | _, _, _, .lit _ _ _ _ => rfl
  | _, _, _, .conv _ _ _ _ _ _ h _ _ _ _ => hasTyA_boundOk h

/-- both endpoints of a typed conversion are scope-bounded (the mutual partner). -/
theorem convA_boundOk {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    {Γ : LCtxA} → {a b A : ExprA} → ConvA E I n Γ a b A →
      boundOkB Γ.length a = true ∧ boundOkB Γ.length b = true
  | _, _, _, _, .refl _ _ _ h => ⟨hasTyA_boundOk h, hasTyA_boundOk h⟩
  | _, _, _, _, .symm _ _ _ _ h => (convA_boundOk h).symm
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => ⟨(convA_boundOk h1).1, (convA_boundOk h2).2⟩
  | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg hred => by
      refine ⟨andB_true ?_ (hasTyA_boundOk harg), hasTyA_boundOk hred⟩
      exact andB_true (hasTyA_boundOk hA) (hasTyA_boundOk hbody)
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb hred => by
      refine ⟨andB_true ?_ (hasTyA_boundOk hb), hasTyA_boundOk hred⟩
      exact andB_true (hasTyA_boundOk hA) (hasTyA_boundOk hv)
  | _, _, _, _, .zetaLocal _ _ _ _ _ hty hv =>
      ⟨decide_eq_true (lookupTypeA_lt_length hty), hasTyA_boundOk hv⟩
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb =>
      ⟨rfl, hasTyA_boundOk hb⟩
  | _, _, _, _, .iota _ _ _ _ _ hlhs hrhs =>
      ⟨hasTyA_boundOk hlhs, hasTyA_boundOk hrhs⟩
  | _, _, _, _, .structIota _ _ _ _ _ _ _ _ _ hlhs hrhs _ =>
      ⟨hasTyA_boundOk hlhs, hasTyA_boundOk hrhs⟩
  | _, _, _, _, .lit _ _ _ hexp => ⟨rfl, hasTyA_boundOk hexp⟩
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ h1 h2 _ _ => by
      have h1' := convA_boundOk h1; have h2' := convA_boundOk h2
      exact ⟨andB_true h1'.1 h2'.1, andB_true h1'.2 h2'.2⟩
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ hA hb hrt => by
      have hA' := convA_boundOk hA; have hb' := convA_boundOk hb
      have hrt' := hasTyA_boundOk hrt
      refine ⟨(andB_true hA'.1 ?_), ?_⟩
      · exact hb'.1
      · exact hrt'
  | _, _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ hA hB hrt => by
      have hA' := convA_boundOk hA; have hB' := convA_boundOk hB
      have hrt' := hasTyA_boundOk hrt
      refine ⟨(andB_true hA'.1 ?_), ?_⟩
      · exact hB'.1
      · exact hrt'
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hrt => by
      have hA' := convA_boundOk hA; have hv' := convA_boundOk hv
      have hb' := convA_boundOk hb; have hrt' := hasTyA_boundOk hrt
      exact ⟨andB_true (andB_true hA'.1 hv'.1) hb'.1, hrt'⟩
  | _, _, _, _, .sorts _ _ _ _ => ⟨rfl, rfl⟩
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl⟩
  | _, _, _, _, .eta _ _ _ _ _ _ h hrt => by
      have hrt' := hasTyA_boundOk hrt
      exact ⟨hrt', hasTyA_boundOk h⟩
  | _, _, _, _, .irr _ _ _ _ _ hp hq =>
      ⟨hasTyA_boundOk hp, hasTyA_boundOk hq⟩
  | _, _, _, _, .tyConv _ _ _ _ _ _ _ _ h _ _ _ _ _ => convA_boundOk h

end

#print axioms pinPiA_ty
#print axioms idSort0_ty
#print axioms idSort1_beta
#print axioms IotaIfaceA.rel_of_pos
#print axioms loopIotaA_rel
#print axioms loopIotaA_no_whnf
#print axioms lookupTypeA_lt_length
#print axioms hasTyA_boundOk

end Rcic.Declarative.Ann
