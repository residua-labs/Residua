import rcic.RcicAnnSyntax
import rcic.RcicLevelZero

/-!
# M1-b (i) — weak-head reduction on the annotated copy

`hStepFnA` is ONE weak-head step on `ExprA` as a FUNCTION: β at the head of an
application spine, a step in the head of the spine, ζ, ζ-local, δ on transparent
members of the environment twin, lit, and ι THROUGH A PARAMETER `iota`
(`IotaFnA`): 05 owns ι's content, the tree's machine (`RcicMachine.lean`,
`MachineRed`) carries no ι arm at all, and M1–M2 are stated for every `iota`,
with the properties they need carried as hypotheses where they are used.
`whnfA` iterates it under fuel and answers `none` when the fuel runs out before
a normal form, never a wrong term. The spine utilities mirror the tree's
`appsSpine`/`foldApps` with the tree's own proofs.

No erasure bridge for reduction is stated here: the tree's `Conv` is total
(R-ConvCollapse), so "erases to a `Conv`" carries no information, and the tree
has no head-step function to compare against; the bridge is M3's.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (2a) the spine, mirrored -/

def appsSpineA : ExprA → ExprA × List ExprA
  | .app f x =>
      let p := appsSpineA f
      (p.1, p.2 ++ [x])
  | e => (e, [])

def foldAppsA (f : ExprA) : List ExprA → ExprA
  | [] => f
  | x :: xs => foldAppsA (.app f x) xs

theorem foldAppsA_append (f : ExprA) (xs ys : List ExprA) :
    foldAppsA f (xs ++ ys) = foldAppsA (foldAppsA f xs) ys := by
  induction xs generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih (.app f x)

theorem appsSpineA_foldAppsA (f : ExprA) (xs : List ExprA) :
    appsSpineA (foldAppsA f xs) =
      ((appsSpineA f).1, (appsSpineA f).2 ++ xs) := by
  induction xs generalizing f with
  | nil => simp only [foldAppsA, List.append_nil]
  | cons x xs ih =>
      simp only [foldAppsA]
      have ih' := ih (.app f x)
      simp only [appsSpineA] at ih' ⊢
      rw [ih']
      simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem foldAppsA_appsSpineA :
    (e : ExprA) → foldAppsA (appsSpineA e).1 (appsSpineA e).2 = e
  | .app f x => by
      simp only [appsSpineA, foldAppsA_append, foldAppsA]
      have ih := foldAppsA_appsSpineA f
      simp only [ih]
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .lam _ _ _ => rfl
  | .pi _ _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-! ## (2b) literals on the copy (02 §8 / §13 shape, no binder, so no annotation) -/

def litZeroA : ExprA := .const 1 []
def litSuccA (e : ExprA) : ExprA := .app (.const 2 []) e

def natExpandA : Nat → ExprA
  | 0 => litZeroA
  | n + 1 => litSuccA (natExpandA n)

theorem erase_natExpandA : (t : Nat) → erase (natExpandA t) = natExpand t
  | 0 => rfl
  | n + 1 => by
      simp only [natExpandA, litSuccA, erase, natExpand, litSucc, erase_natExpandA n]

/-! ## (2c′) R-MajorStep (M2-f (1)): the major position of a recursor spine -/

/-- leading Π-count of an annotated type (main's `piCount` through erasure). -/
def piCountA : ExprA → Nat
  | .pi _ _ B _ => piCountA B + 1
  | _ => 0

theorem piCountA_erase : (T : ExprA) → piCount (erase T) = piCountA T
  | .pi _ _ B _ => by
      show piCount (erase B) + 1 = piCountA B + 1
      rw [piCountA_erase B]
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- the last Π-domain of a type: a recursor's major premise (05 §13). -/
def lastPiDomA : ExprA → Option ExprA
  | .pi A _ B _ =>
      match lastPiDomA B with
      | some D => some D
      | none => some A
  | _ => none

/-- the recursor member at `r` belongs to a group with a constructor. Under 05 §3's layout the
    family is at `f`, its constructors at `f + 1, …`, and the recursor after them, so a group
    without constructors is exactly one whose recursor is at `f + 1`, where `f` heads the
    major's type. A shape that is not recognized counts as having a constructor. -/
def recHasCtorA (r : Nat) (m : CheckedMemberA) : Bool :=
  match lastPiDomA m.mtypeA with
  | some D =>
      match (appsSpineA D).1 with
      | .const f _ => !(decide (r = f + 1))
      | _ => true
  | none => true

/-- the decision at a spine head `h` with `k` arguments: a recursor member of `E`
    applied to exactly `piCountA m.mtypeA − 1` arguments — the major is the LAST
    of the recursor type's Π-binders (05 §13), so this is the telescope count,
    not `m.arity` (the universe-parameter count) — whose group has a constructor
    (O1-a: at a group without one ι never fires, so the major is not reduced). -/
def recAtMajorA' (E : ResolvedEnvA) : ExprA → Nat → Bool
  | .const r _, k =>
      match E.members r with
      | some m => decide (m.mclass = .recursorM ∧ k + 1 = piCountA m.mtypeA) && recHasCtorA r m
      | none => false
  | _, _ => false

/-- `f` is a recursor spine of `E` AT ITS MAJOR: the next argument is the major.
    Read off the syntax and `E` alone. -/
def recAtMajorA (E : ResolvedEnvA) (f : ExprA) : Bool :=
  recAtMajorA' E (appsSpineA f).1 (appsSpineA f).2.length

/-- the Π-binders of a type, each domain with its annotated sort, from the outside in. -/
def piDomListA : ExprA → List (ExprA × Level)
  | .pi A u B _ => (A, u) :: piDomListA B
  | _ => []

/-- O1-b-1 (K-unit): the recursor member `m` at `r` is the recursor of a UNIT GROUP, read off its own
    type, whose last three binders are then the motive, the minor and the major:
    * the major's domain `D` is headed by the family `f`, and the recursor sits at `f + 2` (05 §3: one
      constructor);
    * the major's binder is annotated with a sort that is zero at every valuation (`levelIsZero`): a
      `Prop` family;
    * the third binder from the end is the motive without indices, `Π (t : D'), Sort w` with `D` the
      same `D'` past the motive and the minor (`D = liftA 0 2 D'`). With an index there it is a minor
      (whose codomain is never a sort) or an index (whose type cannot name `f`);
    * the minor's domain is not a Π (the constructor has no field).
    At such a group every proof of the family is convertible to the constructor (`irr`, 02 §10), so ι's
    reduct at the constructor — the minor, applied to no field — is a reduct at every major (README
    O1-b-0, `pinTrueConv`). It reads no member but `m`, as `recAtMajorA` does. -/
def unitGroupA (r : Nat) (m : CheckedMemberA) : Bool :=
  match (piDomListA m.mtypeA).reverse with
  | (D, uD) :: (Dm, _) :: (Dmot, _) :: _ =>
      (match (appsSpineA D).1 with
        | .const f _ => decide (r = f + 2)
        | _ => false) &&
      levelIsZero uD &&
      (match Dmot with
        | .pi D' _ (.sort _) _ => decide (D = liftA 0 2 D')
        | _ => false) &&
      (match Dm with
        | .pi _ _ _ _ => false
        | _ => true)
  | _ => false

/-- the spine head `h` is a recursor of a unit group. -/
def unitHeadA (E : ResolvedEnvA) : ExprA → Bool
  | .const r _ =>
      match E.members r with
      | some m => unitGroupA r m
      | none => false
  | _ => false

/-- the K-unit reduct of a spine `f` at its major: `f`'s last argument (the minor), when `f`'s head
    is a recursor of a unit group. The arm reads it only where the major arm is live
    (`recAtMajorA E f`), so the head is a recursor at its major and the last argument is the minor. -/
def unitMinorA (E : ResolvedEnvA) : ExprA → Option ExprA
  | .app g mn => if unitHeadA E (appsSpineA g).1 then some mn else none
  | _ => none

theorem unitHeadA_of_not_const (E : ResolvedEnvA) :
    (h : ExprA) → (∀ r ls, h ≠ .const r ls) → unitHeadA E h = false
  | .const r ls, hn => absurd rfl (hn r ls)
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .app _ _, _ => rfl
  | .lam _ _ _, _ => rfl
  | .pi _ _ _ _, _ => rfl
  | .letE _ _ _, _ => rfl
  | .lit _, _ => rfl

/-- a recursor whose major binder (its last) is annotated with a sort that is not zero is no unit
    group. -/
theorem unitGroupA_of_majorSort {r : Nat} {m : CheckedMemberA} {D : ExprA} {w : Level}
    {rest : List (ExprA × Level)} (h : (piDomListA m.mtypeA).reverse = (D, w) :: rest)
    (hz : levelIsZero w = false) : unitGroupA r m = false := by
  unfold unitGroupA
  rw [h]
  match rest with
  | [] => rfl
  | [_] => rfl
  | (Dm, _) :: (Dmot, _) :: _ =>
      dsimp only
      rw [hz, Bool.and_false, Bool.false_and, Bool.false_and]

/-! ## (2c″) W-1 (a): the struct arm (K-struct without recursion) -/

/-- apply arguments along a Π-telescope, each `instantiate0A` of the next body;
    `none` when the type runs out of Πs (main's `applyTel`). -/
def applyTelA : List ExprA → ExprA → Option ExprA
  | [], T => some T
  | a :: as, .pi _ _ B _ => applyTelA as (instantiate0A a B)
  | _ :: _, _ => none

/-- a telescope's domains lifted past `a` binders inserted below it (the cutoff grows under each
    binder). -/
def liftDomsA (c a : Nat) : List (ExprA × Level) → List (ExprA × Level)
  | [] => []
  | (D, u) :: ds => (liftA c a D, u) :: liftDomsA (c + 1) a ds

theorem liftDomsA_length (c a : Nat) : (ds : List (ExprA × Level)) → (liftDomsA c a ds).length = ds.length
  | [] => rfl
  | _ :: ds => by simp only [liftDomsA, List.length_cons, liftDomsA_length (c + 1) a ds]

theorem liftA_foldAppsA (c a : Nat) :
    (h : ExprA) → (xs : List ExprA) → liftA c a (foldAppsA h xs) = foldAppsA (liftA c a h) (xs.map (liftA c a))
  | _, [] => rfl
  | h, x :: xs => liftA_foldAppsA c a (.app h x) xs

theorem piDomListA_length : (T : ExprA) → (piDomListA T).length = piCountA T
  | .pi _ _ B _ => by simp only [piDomListA, piCountA, List.length_cons, piDomListA_length B]
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- a telescope's domains at instantiated levels. -/
def instDomsA (ls : List Level) (ds : List (ExprA × Level)) : List (ExprA × Level) :=
  ds.map fun d => (instantiateLevelsA ls d.1, instLevel ls d.2)

theorem instantiateLevelsA_foldAppsA (ls : List Level) :
    (h : ExprA) → (xs : List ExprA) →
    instantiateLevelsA ls (foldAppsA h xs) =
      foldAppsA (instantiateLevelsA ls h) (xs.map (instantiateLevelsA ls))
  | _, [] => rfl
  | h, x :: xs => instantiateLevelsA_foldAppsA ls (.app h x) xs

/-- a λ-telescope over binders given outermost first (each domain in the context of the earlier
    binders), around a body. -/
def lamTelA : List (ExprA × Level) → ExprA → ExprA
  | [], b => b
  | (D, u) :: ds, b => .lam D u (lamTelA ds b)

/-- W-1 (a): the recursor member `m` at `r` is the recursor of a STRUCT GROUP, read off its own type.
    Its last three binders are the motive, the minor and the major, as at a unit group (`unitGroupA`:
    one constructor, a `Prop` family, a motive without indices), and:
    * the motive's sort is not zero at every valuation (`levelIsZero`): AnySort, so no binder of the
      minor is an induction hypothesis, whose sort is the motive's;
    * the minor's domain is a Π (the constructor has a field), and every binder of its telescope is
      annotated with a sort that is zero at every valuation: every field is a proof.
    At such a group every proof of the family is convertible to the constructor applied to the
    proof's projections (`irr`, 02 §10), where ι fires (README W-1-0). Disjoint from `unitGroupA`,
    whose minor's domain is no Π. It reads no member but `m`, as `unitGroupA` does. -/
def structGroupA (r : Nat) (m : CheckedMemberA) : Bool :=
  match (piDomListA m.mtypeA).reverse with
  | (D, uD) :: (Dm, _) :: (Dmot, _) :: _ =>
      (match (appsSpineA D).1 with
        | .const f _ => decide (r = f + 2)
        | _ => false) &&
      levelIsZero uD &&
      (match Dmot with
        | .pi D' _ (.sort w) _ => decide (D = liftA 0 2 D') && !levelIsZero w
        | _ => false) &&
      (match Dm with
        | .pi _ _ _ _ => (piDomListA Dm).all (fun p => levelIsZero p.2)
        | _ => false)
  | _ => false

/-- the `i`-th field selector over the minor's field binders `ds`: `λ f₀ … f_{k-1}. f_i`. -/
def fieldSelA (ds : List (ExprA × Level)) (i : Nat) : ExprA :=
  lamTelA ds (.bvar (ds.length - 1 - i))

/-- the projection of `x` at field `i`: the recursor `r` at the levels `ls₀` (the motive's level zero)
    over the parameters `ps`, the motive `λ (_ : S) uS. F` with `F` the field's domain, the selector of
    field `i` over the minor's binders `ds`, and `x` (README W-1-0: 02 has no primitive projection;
    ADR_CIC_FULL_ADOPTION §3 derives `proj` from the recursor). -/
def structProjA (r : Nat) (ls₀ : List Level) (ps : List ExprA) (S : ExprA) (uS : Level)
    (ds : List (ExprA × Level)) (x : ExprA) (i : Nat) (F : ExprA) : ExprA :=
  foldAppsA (.const r ls₀) (ps ++ [.lam S uS (liftA 0 1 F), fieldSelA ds i, x])

/-- the projections of `x` along a field telescope (the minor's domain at the spine's parameters and
    motive), from field `i` on, at most `k` of them: each field's domain has the earlier fields
    instantiated at their projections. -/
def structProjsA (r : Nat) (ls₀ : List Level) (ps : List ExprA) (S : ExprA) (uS : Level)
    (ds : List (ExprA × Level)) (x : ExprA) : Nat → Nat → ExprA → List ExprA
  | 0, _, _ => []
  | k + 1, i, .pi F _ B _ =>
      structProjA r ls₀ ps S uS ds x i F ::
        structProjsA r ls₀ ps S uS ds x k (i + 1) (instantiate0A (structProjA r ls₀ ps S uS ds x i F) B)
  | _ + 1, _, .bvar _ => []
  | _ + 1, _, .sort _ => []
  | _ + 1, _, .const _ _ => []
  | _ + 1, _, .app _ _ => []
  | _ + 1, _, .lam _ _ _ => []
  | _ + 1, _, .letE _ _ _ => []
  | _ + 1, _, .lit _ => []

/-- the recursor's levels with the motive's set to zero: the motive's universe is the recursor's
    last (05 §11: AnySort's `param fm.arity`, the recursor's arity `fm.arity + 1`). -/
def motZeroLevelsA (ls : List Level) : List Level := ls.set (ls.length - 1) .zero

/-- W-1 (b′): the number of fields of a struct group's constructor, read off the recursor member's own
    type: the Π-count of its minor's domain (the binder before the major). A count fixed by the member,
    not by the domain the spine's arguments instantiate (that can only gain Π-binders, at a substituted
    variable), so the arm makes as many projections after a substitution as before. -/
def structFieldCountA (m : CheckedMemberA) : Nat :=
  match (piDomListA m.mtypeA).reverse with
  | _ :: (Dm, _) :: _ => piCountA Dm
  | _ => 0

/-- what the struct arm reads off a recursor spine `.app g mn` before its major: the recursor `rec`,
    its levels with the motive's at zero `ls₀`, the parameters `ps`, the major's domain `S` with its
    sort `uS`, the minor's domain `Dm` (its binders the fields), the minor `mn`, and the member's field
    count `nf` (`structFieldCountA`). -/
structure StructSpineA : Type where
  r : Nat
  ls₀ : List Level
  ps : List ExprA
  S : ExprA
  uS : Level
  Dm : ExprA
  mn : ExprA
  nf : Nat

/-- the struct arm's reduct at the major `x`: the minor applied to the projections of `x`, one per field
    of the member (`nf`), each selector over the first `nf` binders of the minor's domain. -/
def StructSpineA.reduct (d : StructSpineA) (x : ExprA) : ExprA :=
  foldAppsA d.mn (structProjsA d.r d.ls₀ d.ps d.S d.uS ((piDomListA d.Dm).take d.nf) x d.nf 0 d.Dm)

/-- W-1 (a): the struct arm's reading of a recursor spine `.app g mn`, its head `.const r ls` the
    recursor of a struct group and `g`'s arguments the parameters and the motive. Read off the
    recursor's type at the spine's levels, applied along `g`'s arguments: `Π (m : Dm), B` with `Dm`
    the minor's domain, and `B` at the minor `Π (t : S) uS, …`, `S` the major's domain. -/
def structSpineA (E : ResolvedEnvA) : ExprA → Option StructSpineA
  | .app g mn =>
      match (appsSpineA g).1 with
      | .const r ls =>
          match E.members r with
          | some m =>
              if structGroupA r m then
                match applyTelA (appsSpineA g).2 (instantiateLevelsA ls m.mtypeA) with
                | some (.pi Dm _ B _) =>
                    match instantiate0A mn B with
                    | .pi S uS _ _ =>
                        some ⟨r, motZeroLevelsA ls, (appsSpineA g).2.dropLast, S, uS, Dm, mn, structFieldCountA m⟩
                    | _ => none
                | _ => none
              else none
          | none => none
      | _ => none
  | _ => none

/-- W-1 (a), THE STRUCT ARM's reduct at a recursor spine `f` at its major `x`: the minor applied to the
    major's projections (`StructSpineA.reduct`), when the minor's domain at the spine has at least the
    member's field count of binders (W-1 (b′)). Whether it answers reads `f` alone
    (`structArmA_none_any`). -/
def structArmA (E : ResolvedEnvA) (f x : ExprA) : Option ExprA :=
  (structSpineA E f).bind (fun d => if d.nf ≤ piCountA d.Dm then some (d.reduct x) else none)

/-- whether the struct arm answers does not depend on the major. -/
theorem structArmA_none_any (E : ResolvedEnvA) (f : ExprA) {x : ExprA} (h : structArmA E f x = none)
    (y : ExprA) : structArmA E f y = none := by
  unfold structArmA at h ⊢
  cases hs : structSpineA E f with
  | none => rfl
  | some d =>
      rw [hs, Option.some_bind] at h
      rw [Option.some_bind]
      by_cases hn : d.nf ≤ piCountA d.Dm
      · rw [if_pos hn] at h; exact Option.noConfusion h
      · rw [if_neg hn]

/-- the struct arm's answer, read back: the spine's reading, the count's check, the reduct. -/
theorem structArmA_some {E : ResolvedEnvA} {f x e : ExprA} (h : structArmA E f x = some e) :
    ∃ d, structSpineA E f = some d ∧ d.nf ≤ piCountA d.Dm ∧ d.reduct x = e := by
  unfold structArmA at h
  cases hs : structSpineA E f with
  | none => rw [hs, Option.none_bind] at h; exact Option.noConfusion h
  | some d =>
      rw [hs, Option.some_bind] at h
      by_cases hn : d.nf ≤ piCountA d.Dm
      · rw [if_pos hn] at h; exact ⟨d, rfl, hn, Option.some.inj h⟩
      · rw [if_neg hn] at h; exact Option.noConfusion h

/-- the arm is dead at a recursor that is no struct group's. -/
theorem structSpineA_of_not_struct {E : ResolvedEnvA} {g : ExprA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (hsp : (appsSpineA g).1 = .const r ls) (hres : E.members r = some m)
    (hns : structGroupA r m = false) (mn : ExprA) : structSpineA E (.app g mn) = none := by
  simp only [structSpineA, hsp, hres, hns]
  rfl

theorem structArmA_of_not_struct {E : ResolvedEnvA} {g : ExprA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (hsp : (appsSpineA g).1 = .const r ls) (hres : E.members r = some m)
    (hns : structGroupA r m = false) (mn x : ExprA) : structArmA E (.app g mn) x = none := by
  unfold structArmA
  rw [structSpineA_of_not_struct hsp hres hns mn]
  rfl

/-- a recursor whose major binder (its last) is annotated with a sort that is not zero is no struct
    group. -/
theorem structGroupA_of_majorSort {r : Nat} {m : CheckedMemberA} {D : ExprA} {w : Level}
    {rest : List (ExprA × Level)} (h : (piDomListA m.mtypeA).reverse = (D, w) :: rest)
    (hz : levelIsZero w = false) : structGroupA r m = false := by
  unfold structGroupA
  rw [h]
  match rest with
  | [] => rfl
  | [_] => rfl
  | (Dm, _) :: (Dmot, _) :: _ =>
      dsimp only
      rw [hz, Bool.and_false, Bool.false_and, Bool.false_and]

/-- a struct group is no unit group: the unit test needs the minor's domain to be no Π. -/
theorem unitGroupA_false_of_struct {r : Nat} {m : CheckedMemberA} (h : structGroupA r m = true) :
    unitGroupA r m = false := by
  unfold structGroupA at h
  unfold unitGroupA
  generalize (piDomListA m.mtypeA).reverse = L at h ⊢
  match L, h with
  | (D, uD) :: (Dm, uDm) :: (Dmot, uDmot) :: rest, h =>
      cases Dm <;> first | (simp at h; done) | simp
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl

theorem recAtMajorA'_of_not_const (E : ResolvedEnvA) (k : Nat) :
    (h : ExprA) → (∀ r ls, h ≠ .const r ls) → recAtMajorA' E h k = false
  | .const r ls, hn => absurd rfl (hn r ls)
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .app _ _, _ => rfl
  | .lam _ _ _, _ => rfl
  | .pi _ _ _ _, _ => rfl
  | .letE _ _ _, _ => rfl
  | .lit _, _ => rfl

/-- the arm is live exactly at a recursor member of `E` with the major next, whose group has a
    constructor. -/
theorem recAtMajorA'_const (E : ResolvedEnvA) (r : Nat) (ls : List Level) (k : Nat) :
    recAtMajorA' E (.const r ls) k = true ↔
      ∃ m, E.members r = some m ∧ m.mclass = .recursorM ∧ k + 1 = piCountA m.mtypeA ∧
        recHasCtorA r m = true := by
  show (match E.members r with
    | some m => decide (m.mclass = .recursorM ∧ k + 1 = piCountA m.mtypeA) && recHasCtorA r m
    | none => false) = true ↔ _
  cases hm : E.members r with
  | none =>
      constructor
      · intro h; exact Bool.noConfusion h
      · rintro ⟨m, hm', _⟩; cases hm'
  | some m =>
      constructor
      · intro h
        rw [Bool.and_eq_true] at h
        have h' := of_decide_eq_true h.1
        exact ⟨m, rfl, h'.1, h'.2, h.2⟩
      · rintro ⟨m', hm', hc, hk, hh⟩
        cases hm'
        rw [Bool.and_eq_true]
        exact ⟨decide_eq_true ⟨hc, hk⟩, hh⟩

theorem recAtMajorA_of_head_not_const (E : ResolvedEnvA) {f : ExprA}
    (hn : ∀ r ls, (appsSpineA f).1 ≠ .const r ls) : recAtMajorA E f = false :=
  recAtMajorA'_of_not_const E _ _ hn

theorem recAtMajorA_not_lam (E : ResolvedEnvA) (A : ExprA) (u : Level) (b : ExprA) :
    recAtMajorA E (.lam A u b) = false := rfl

/-- a live arm has a constant head: a recursor member of `E` at the major. -/
theorem recAtMajorA_true {E : ResolvedEnvA} {f : ExprA} (h : recAtMajorA E f = true) :
    ∃ r ls m, (appsSpineA f).1 = .const r ls ∧ E.members r = some m ∧ m.mclass = .recursorM ∧
      (appsSpineA f).2.length + 1 = piCountA m.mtypeA := by
  unfold recAtMajorA at h
  cases hh : (appsSpineA f).1 with
  | const r ls =>
      rw [hh] at h
      obtain ⟨m, hm, hc, hk, _⟩ := (recAtMajorA'_const E r ls _).1 h
      exact ⟨r, ls, m, rfl, hm, hc, hk⟩
  | bvar i => rw [hh] at h; exact Bool.noConfusion h
  | sort _ => rw [hh] at h; exact Bool.noConfusion h
  | app _ _ => rw [hh] at h; exact Bool.noConfusion h
  | lam _ _ _ => rw [hh] at h; exact Bool.noConfusion h
  | pi _ _ _ _ => rw [hh] at h; exact Bool.noConfusion h
  | letE _ _ _ => rw [hh] at h; exact Bool.noConfusion h
  | lit _ => rw [hh] at h; exact Bool.noConfusion h

/-- the arm at a constant head that is a member of `E` but not a recursor is dead. -/
theorem recAtMajorA_of_not_rec {E : ResolvedEnvA} {f : ExprA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (hsp : (appsSpineA f).1 = .const r ls) (hres : E.members r = some m)
    (hnr : m.mclass ≠ .recursorM) : recAtMajorA E f = false := by
  cases h : recAtMajorA E f with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨r', ls', m', hsp', hres', hc, _⟩ := recAtMajorA_true h
      have e : ExprA.const r ls = .const r' ls' := hsp.symm.trans hsp'
      injection e with e1 _
      subst e1
      rw [hres] at hres'
      cases hres'
      exact hnr hc

/-- a spine STRICTLY BELOW the major position of its recursor head, if any: along
    its head chain the major arm is never live (`recAtMajorA_of_below`), so the
    step there reads no argument. Vacuous for a head that is no recursor of `E`. -/
def BelowMajorA (E : ResolvedEnvA) (e : ExprA) : Prop :=
  ∀ r ls m, (appsSpineA e).1 = .const r ls → E.members r = some m → m.mclass = .recursorM →
    (appsSpineA e).2.length < piCountA m.mtypeA

theorem appsSpineA_app_fst (f x : ExprA) : (appsSpineA (.app f x)).1 = (appsSpineA f).1 := rfl
theorem appsSpineA_app_snd (f x : ExprA) :
    (appsSpineA (.app f x)).2 = (appsSpineA f).2 ++ [x] := rfl

theorem belowMajorA_app {E : ResolvedEnvA} {f x : ExprA} (h : BelowMajorA E (.app f x)) :
    BelowMajorA E f := fun r ls m hsp hres hc => by
  have := h r ls m hsp hres hc
  rw [appsSpineA_app_snd, List.length_append, List.length_singleton] at this
  omega

theorem recAtMajorA_of_below {E : ResolvedEnvA} {f x : ExprA} (h : BelowMajorA E (.app f x)) :
    recAtMajorA E f = false := by
  cases hr : recAtMajorA E f with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨r, ls, m, hsp, hres, hc, hk⟩ := recAtMajorA_true hr
      have := h r ls m hsp hres hc
      rw [appsSpineA_app_snd, List.length_append, List.length_singleton] at this
      omega

/-- a spine of length `piCountA m.mtypeA` at a recursor `m` (the ι redex shape, 05
    §11): its FUNCTION part is strictly below the major. -/
theorem belowMajorA_of_at {E : ResolvedEnvA} {f x : ExprA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (hsp : (appsSpineA (.app f x)).1 = .const r ls)
    (hres : E.members r = some m) (hlen : (appsSpineA (.app f x)).2.length = piCountA m.mtypeA) :
    BelowMajorA E f := fun r' ls' m' hsp' hres' _ => by
  have e : ExprA.const r ls = .const r' ls' := hsp.symm.trans hsp'
  injection e with e1 _
  subst e1
  rw [hres] at hres'
  cases hres'
  rw [appsSpineA_app_snd, List.length_append, List.length_singleton] at hlen
  omega

/-- a spine at its major position is strictly below it. -/
theorem belowMajorA_of_rec {E : ResolvedEnvA} {f : ExprA} (h : recAtMajorA E f = true) :
    BelowMajorA E f := fun r' ls' m' hsp' hres' _ => by
  obtain ⟨r, ls, m, hsp, hres, _, hk⟩ := recAtMajorA_true h
  have e : ExprA.const r ls = .const r' ls' := hsp.symm.trans hsp'
  injection e with e1 _
  subst e1
  rw [hres] at hres'
  cases hres'
  omega

/-- W-1 (e): the spine `f`'s head is a recursor of a STRUCT GROUP of `E`. Read off the head alone, so
    every operation that keeps a spine's head keeps it. -/
def structHeadA (E : ResolvedEnvA) (f : ExprA) : Bool :=
  match (appsSpineA f).1 with
  | .const r _ =>
      match E.members r with
      | some m => structGroupA r m
      | none => false
  | _ => false

/-- W-1 (e): THE STRUCT POSITION: `f` is a struct group's recursor spine at its major. There the head
    step is the struct arm's, and ι is not consulted. -/
def structPosA (E : ResolvedEnvA) (f : ExprA) : Bool := recAtMajorA E f && structHeadA E f

theorem structHeadA_of_spine {E : ResolvedEnvA} {f : ExprA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (hsp : (appsSpineA f).1 = .const r ls) (hres : E.members r = some m) :
    structHeadA E f = structGroupA r m := by
  unfold structHeadA; rw [hsp]; simp only [hres]

/-- where the struct head fails, the struct arm does not answer. -/
theorem structArmA_of_structHead {E : ResolvedEnvA} {f : ExprA} (h : structHeadA E f = false)
    (x : ExprA) : structArmA E f x = none := by
  cases f with
  | app g mn =>
      have hsp : (appsSpineA (.app g mn)).1 = (appsSpineA g).1 := rfl
      cases hh : (appsSpineA g).1 with
      | const r ls =>
          cases hres : E.members r with
          | none =>
              unfold structArmA structSpineA
              simp only [hh, hres]; rfl
          | some m =>
              have hns : structGroupA r m = false := by
                rw [← structHeadA_of_spine (hsp.trans hh) hres]; exact h
              exact structArmA_of_not_struct hh hres hns mn x
      | _ =>
          unfold structArmA structSpineA
          simp only [hh]; rfl
  | _ => rfl

/-- where the struct arm answers, the head is a struct group's recursor. -/
theorem structHeadA_of_structArmA {E : ResolvedEnvA} {f x e : ExprA} (h : structArmA E f x = some e) :
    structHeadA E f = true := by
  cases hh : structHeadA E f with
  | true => rfl
  | false => rw [structArmA_of_structHead hh x] at h; exact Option.noConfusion h

/-- where the K-unit arm answers, the head is no struct group's: a unit group is no struct group. -/
theorem structHeadA_of_unitMinorA {E : ResolvedEnvA} {f mn : ExprA} (h : unitMinorA E f = some mn) :
    structHeadA E f = false := by
  cases f with
  | app g mn' =>
      have hsp : (appsSpineA (.app g mn')).1 = (appsSpineA g).1 := rfl
      cases hh : (appsSpineA g).1 with
      | const r ls =>
          cases hres : E.members r with
          | none =>
              unfold structHeadA; rw [hsp, hh]; simp only [hres]
          | some m =>
              rw [structHeadA_of_spine (hsp.trans hh) hres]
              cases hns : structGroupA r m with
              | false => rfl
              | true =>
                  have h' : unitMinorA E (.app g mn') = none := by
                    simp [unitMinorA, unitHeadA, hh, hres, unitGroupA_false_of_struct hns]
                  rw [h'] at h; exact Option.noConfusion h
      | _ => unfold structHeadA; rw [hsp, hh]
  | _ => exact Option.noConfusion h

theorem structPosA_of_rec {E : ResolvedEnvA} {f : ExprA} (hrec : recAtMajorA E f = true) :
    structPosA E f = structHeadA E f := by
  unfold structPosA; rw [hrec]; rfl

theorem structPosA_of_not_rec {E : ResolvedEnvA} {f : ExprA} (hrec : recAtMajorA E f = false) :
    structPosA E f = false := by
  unfold structPosA; rw [hrec]; rfl

theorem structPosA_of_head {E : ResolvedEnvA} {f : ExprA} (hh : structHeadA E f = false) :
    structPosA E f = false := by
  unfold structPosA; rw [hh, Bool.and_false]

/-- the struct position, read back. -/
theorem structPosA_true {E : ResolvedEnvA} {f : ExprA} (h : structPosA E f = true) :
    recAtMajorA E f = true ∧ structHeadA E f = true := by
  unfold structPosA at h
  exact Bool.and_eq_true_iff.mp h

/-! ## (2c) the head step -/

/-- the 05-owned ι as the copy's PARAMETER: a partial head step on full
    recursor applications. `hStepFnA` hands it the whole spine once the head is
    stuck; the major premise it does not reduce is the step function's own
    (R-MajorStep). -/
abbrev IotaFnA := ExprA → Option ExprA

/-- ONE weak-head step. Arms in order: β at the head; a step in the head of the
    spine, else, at a STRUCT GROUP's recursor spine at its major (W-1 (a): a `Prop` family without
    indices whose single constructor has only non-recursive proof fields, AnySort; `structPosA`), the
    struct arm: the minor applied to the major's projections, whatever the major, never stepping it
    (`structArmA`; W-1 (e): ι is not consulted there, so a constructor major takes the arm too); else
    ι on the spine; else
    (R-MajorStep, M2-f (1)) a step in the MAJOR of a recursor spine at its major position, its group
    having a constructor (O1-a: without one ι never fires, so the major is never read) — except at a
    UNIT GROUP (O1-b-1, K-unit: a `Prop` family without indices whose single constructor has no
    field), where the spine steps to its minor, reading no major (`unitMinorA`); ζ; ζ-local; δ
    (transparent members only, the body instantiated at the levels); lit;
    `sort`/`lam`/`pi` are normal.
    The major arm is what makes the structural relation at an inductive type a
    congruence for the recursor (L-RING C4 P1): `rec P mz ms ((λx.x) zero)` steps
    to `rec P mz ms zero`. It is the copy's STRATEGY (02 §9 is a relation and 02
    §10 its congruence closure; the step is already a conversion), named M-001
    deviation R-MajorStep; main's `whStepFn` does not take it. -/
def hStepFnA (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) : ExprA → Option ExprA
  | .app (.lam _A _u body) arg => some (instantiate0A arg body)
  | .app f x =>
      match hStepFnA E iota Γ f with
      | some f' => some (.app f' x)
      | none =>
          if structPosA E f then structArmA E f x
          else
            match iota (.app f x) with
            | some e' => some e'
            | none =>
                if recAtMajorA E f then
                  match unitMinorA E f with
                  | some mn => some mn
                  | none => (hStepFnA E iota Γ x).map (ExprA.app f)
                else none
  | .letE _A value body => some (instantiate0A value body)
  | .bvar i => lookupValueA Γ i
  | .const r ls =>
      match E.members r with
      | some m =>
          if transparent m.mclass then m.bodyA.map (instantiateLevelsA ls) else none
      | none => none
  | .lit t => some (natExpandA t)
  | .sort _ => none
  | .lam _ _ _ => none
  | .pi _ _ _ _ => none

theorem hStepFnA_app_lam (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (A : ExprA) (u : Level)
    (body arg : ExprA) :
    hStepFnA E iota Γ (.app (.lam A u body) arg) = some (instantiate0A arg body) := rfl

/-- the second arm written out, for a head that is not a λ: a step in the head,
    else, at the struct position, the struct arm, else `iota` on the whole application — the ONLY
    place `iota` is consulted — else the major arm. -/
theorem hStepFnA_app_nonlam (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) {f : ExprA}
    (x : ExprA) (hnl : ∀ A u b, f ≠ .lam A u b) :
    hStepFnA E iota Γ (.app f x) =
      match hStepFnA E iota Γ f with
      | some f' => some (.app f' x)
      | none =>
          if structPosA E f then structArmA E f x
          else
            match iota (.app f x) with
            | some e' => some e'
            | none =>
                if recAtMajorA E f then
                  match unitMinorA E f with
                  | some mn => some mn
                  | none => (hStepFnA E iota Γ x).map (ExprA.app f)
                else none := by
  cases f with
  | lam A u b => exact absurd rfl (hnl A u b)
  | _ => rfl

/-- the arms of an application whose head is not a λ, one lemma each. -/
theorem hStepFnA_app_head (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) {f f' : ExprA}
    (x : ExprA) (hf : hStepFnA E iota Γ f = some f') :
    hStepFnA E iota Γ (.app f x) = some (.app f' x) := by
  have hnl : ∀ A u b, f ≠ .lam A u b := fun A u b e => by subst e; exact Option.noConfusion hf
  rw [hStepFnA_app_nonlam E iota Γ x hnl, hf]

/-- at the struct position (W-1 (a), (e)) the step is the struct arm's, and ι is not consulted. -/
theorem hStepFnA_app_structPos (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) {f x : ExprA}
    (hnl : ∀ A u b, f ≠ .lam A u b) (hf : hStepFnA E iota Γ f = none)
    (hp : structPosA E f = true) : hStepFnA E iota Γ (.app f x) = structArmA E f x := by
  rw [hStepFnA_app_nonlam E iota Γ x hnl, hf]
  dsimp only
  rw [if_pos hp]

theorem hStepFnA_app_iota (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) {f x e' : ExprA}
    (hnl : ∀ A u b, f ≠ .lam A u b) (hf : hStepFnA E iota Γ f = none)
    (hp : structPosA E f = false) (hi : iota (.app f x) = some e') :
    hStepFnA E iota Γ (.app f x) = some e' := by
  rw [hStepFnA_app_nonlam E iota Γ x hnl, hf]
  dsimp only
  rw [if_neg (by rw [hp]; exact Bool.false_ne_true), hi]

theorem hStepFnA_app_major (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) {f x : ExprA}
    (hnl : ∀ A u b, f ≠ .lam A u b) (hf : hStepFnA E iota Γ f = none)
    (hp : structPosA E f = false) (hi : iota (.app f x) = none) :
    hStepFnA E iota Γ (.app f x) =
      if recAtMajorA E f then
        match unitMinorA E f with
        | some mn => some mn
        | none => (hStepFnA E iota Γ x).map (ExprA.app f)
      else none := by
  rw [hStepFnA_app_nonlam E iota Γ x hnl, hf]
  dsimp only
  rw [if_neg (by rw [hp]; exact Bool.false_ne_true), hi]

/-- the major arm dead: the application is normal. -/
theorem hStepFnA_app_none (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) {f x : ExprA}
    (hnl : ∀ A u b, f ≠ .lam A u b) (hf : hStepFnA E iota Γ f = none)
    (hi : iota (.app f x) = none) (hrec : recAtMajorA E f = false) :
    hStepFnA E iota Γ (.app f x) = none := by
  rw [hStepFnA_app_major E iota Γ hnl hf (structPosA_of_not_rec hrec) hi, hrec]
  rfl

/-- the major arm live at a group that is neither a unit group nor a struct group: the step is the
    major's. -/
theorem hStepFnA_app_atMajor (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) {f x : ExprA}
    (hnl : ∀ A u b, f ≠ .lam A u b) (hf : hStepFnA E iota Γ f = none)
    (hi : iota (.app f x) = none) (hrec : recAtMajorA E f = true) (hu : unitMinorA E f = none)
    (hs : structHeadA E f = false) :
    hStepFnA E iota Γ (.app f x) = (hStepFnA E iota Γ x).map (ExprA.app f) := by
  rw [hStepFnA_app_major E iota Γ hnl hf (structPosA_of_head hs) hi, hrec, if_pos rfl, hu]

/-- the major arm live at a unit group (O1-b-1, K-unit): the step is to the minor, whatever the
    major. -/
theorem hStepFnA_app_unit (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) {f x mn : ExprA}
    (hnl : ∀ A u b, f ≠ .lam A u b) (hf : hStepFnA E iota Γ f = none)
    (hi : iota (.app f x) = none) (hrec : recAtMajorA E f = true) (hu : unitMinorA E f = some mn) :
    hStepFnA E iota Γ (.app f x) = some mn := by
  rw [hStepFnA_app_major E iota Γ hnl hf (structPosA_of_head (structHeadA_of_unitMinorA hu)) hi, hrec,
    if_pos rfl, hu]

/-- the struct arm at a struct group (W-1 (a), (e)): the step is to the minor applied to the major's
    projections, never a step of the major, whatever ι says. -/
theorem hStepFnA_app_struct (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) {f x e : ExprA}
    (hnl : ∀ A u b, f ≠ .lam A u b) (hf : hStepFnA E iota Γ f = none)
    (hrec : recAtMajorA E f = true) (hs : structArmA E f x = some e) :
    hStepFnA E iota Γ (.app f x) = some e := by
  rw [hStepFnA_app_structPos E iota Γ hnl hf (by rw [structPosA_of_rec hrec]; exact structHeadA_of_structArmA hs),
    hs]

/-- a normal application whose head is not a λ: the head is normal, and off the struct position ι
    refused. -/
theorem hStepFnA_app_none_inv (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) {f x : ExprA}
    (hnl : ∀ A u b, f ≠ .lam A u b) (h : hStepFnA E iota Γ (.app f x) = none) :
    hStepFnA E iota Γ f = none ∧ (structPosA E f = false → iota (.app f x) = none) := by
  rw [hStepFnA_app_nonlam E iota Γ x hnl] at h
  cases hf : hStepFnA E iota Γ f with
  | some f' => rw [hf] at h; exact Option.noConfusion h
  | none =>
      refine ⟨rfl, fun hp => ?_⟩
      rw [hf] at h
      dsimp only at h
      rw [if_neg (by rw [hp]; exact Bool.false_ne_true)] at h
      cases hi : iota (.app f x) with
      | some e' => rw [hi] at h; exact Option.noConfusion h
      | none => rfl

theorem lamA_or_not (f : ExprA) :
    (∃ A u b, f = .lam A u b) ∨ (∀ A u b, f ≠ .lam A u b) := by
  cases f with
  | lam A u b => exact Or.inl ⟨A, u, b, rfl⟩
  | _ => exact Or.inr (fun _ _ _ h => ExprA.noConfusion h)

/-- weak-head normal form under fuel: `some w` only when `w` is NORMAL for
    `hStepFnA`; `none` when the fuel runs out first. -/
def whnfA (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) : Nat → ExprA → Option ExprA
  | 0, e =>
      match hStepFnA E iota Γ e with
      | none => some e
      | some _ => none
  | fuel + 1, e =>
      match hStepFnA E iota Γ e with
      | some e' => whnfA E iota Γ fuel e'
      | none => some e

theorem whnfA_normal (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) :
    (fuel : Nat) → (e w : ExprA) → whnfA E iota Γ fuel e = some w →
      hStepFnA E iota Γ w = none
  | 0, e, w, h => by
      simp only [whnfA] at h
      split at h
      · cases h; assumption
      · cases h
  | fuel + 1, e, w, h => by
      simp only [whnfA] at h
      split at h
      · exact whnfA_normal E iota Γ fuel _ w h
      · cases h; assumption

theorem whnfA_of_normal (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA)
    (fuel : Nat) (e : ExprA) (h : hStepFnA E iota Γ e = none) :
    whnfA E iota Γ fuel e = some e := by
  cases fuel with
  | zero => simp only [whnfA, h]
  | succ fuel => simp only [whnfA, h]

/-- more fuel never changes a `some` answer. -/
theorem whnfA_fuel_mono (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) :
    (fuel : Nat) → (e w : ExprA) → whnfA E iota Γ fuel e = some w →
      whnfA E iota Γ (fuel + 1) e = some w
  | 0, e, w, h => by
      cases hs : hStepFnA E iota Γ e with
      | none =>
          simp only [whnfA, hs] at h ⊢
          exact h
      | some e' =>
          simp only [whnfA, hs] at h
          cases h
  | fuel + 1, e, w, h => by
      cases hs : hStepFnA E iota Γ e with
      | none =>
          simp only [whnfA, hs] at h ⊢
          exact h
      | some e' =>
          simp only [whnfA, hs] at h ⊢
          exact whnfA_fuel_mono E iota Γ fuel e' w h

/-! ## (2d) pins: sorts, lams and pis are normal; β and ζ fire; the oracle is reached only on a stuck head -/

example (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (l : Level) :
    hStepFnA E iota Γ (.sort l) = none := rfl
example (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (A B : ExprA) (u v : Level) :
    hStepFnA E iota Γ (.pi A u B v) = none := rfl
example (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (A b : ExprA) (u : Level) :
    hStepFnA E iota Γ (.lam A u b) = none := rfl
example (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (A body arg : ExprA) (u : Level) :
    hStepFnA E iota Γ (.app (.lam A u body) arg) = some (instantiate0A arg body) := rfl
example (E : ResolvedEnvA) (iota : IotaFnA) (Γ : LCtxA) (A value body : ExprA) :
    hStepFnA E iota Γ (.letE A value body) = some (instantiate0A value body) := rfl
/-- the identity at `Sort 0` applied to `Sort 0` β-reduces to `Sort 0`. -/
example : hStepFnA emptyEnvA (fun _ => none) []
    (.app (.lam (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)) (.sort .zero))
    = some (.sort .zero) := by decide
/-- a stuck neutral head reaches the oracle with the whole spine. -/
example (E : ResolvedEnvA) (Γ : LCtxA) (x : ExprA) (hE : E.members 7 = none) :
    hStepFnA E (fun e => some e) Γ (.app (.const 7 []) x) = some (.app (.const 7 []) x) := by
  have hrec : recAtMajorA E (.const 7 []) = false := by
    simp [recAtMajorA, recAtMajorA', appsSpineA, hE]
  exact hStepFnA_app_iota E _ Γ (fun _ _ _ h => ExprA.noConfusion h) (by simp [hStepFnA, hE])
    (structPosA_of_not_rec hrec) rfl

/-! ## (2e) R-MajorStep pins (M2-f (1)): the major steps at the major position only -/

/-- a recursor member with a four-binder type (motive, two minors, major). -/
def pinRecTypeA : ExprA :=
  .pi (.sort .zero) (.succ .zero) (.pi (.sort .zero) (.succ .zero) (.pi (.sort .zero) (.succ .zero)
    (.pi (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)) (.succ .zero)) (.succ .zero)) (.succ .zero)
def pinRecMemberA : CheckedMemberA := ⟨.recursorM, 0, pinRecTypeA, none, 0, none⟩
def pinRecEnvA : ResolvedEnvA := extendEnvA emptyEnvA 9 pinRecMemberA
def pinIdRedexA : ExprA := .app (.lam (.sort .zero) (.succ .zero) (.bvar 0)) (.sort .zero)

example : piCountA pinRecTypeA = 4 := rfl
/-- AT the major: the major's β step is the spine's step (C4 P1's pair). -/
example : hStepFnA pinRecEnvA (fun _ => none) []
    (.app (.app (.app (.app (.const 9 []) (.sort .zero)) (.sort .zero)) (.sort .zero)) pinIdRedexA) =
    some (.app (.app (.app (.app (.const 9 []) (.sort .zero)) (.sort .zero)) (.sort .zero)) (.sort .zero)) := by
  decide
/-- BELOW the major: a redex in a minor position does not step the spine. -/
example : hStepFnA pinRecEnvA (fun _ => none) []
    (.app (.app (.app (.const 9 []) (.sort .zero)) (.sort .zero)) pinIdRedexA) = none := by decide
/-- OVER-APPLIED with a normal major: normal (the arm needs the major next). -/
example : hStepFnA pinRecEnvA (fun _ => none) []
    (.app (.app (.app (.app (.app (.const 9 []) (.sort .zero)) (.sort .zero)) (.sort .zero)) (.sort .zero))
      (.sort .zero)) = none := by decide
/-- OVER-APPLIED with a reducible major: the step is in the head, at the major. -/
example : hStepFnA pinRecEnvA (fun _ => none) []
    (.app (.app (.app (.app (.app (.const 9 []) (.sort .zero)) (.sort .zero)) (.sort .zero)) pinIdRedexA)
      (.sort .zero)) =
    some (.app (.app (.app (.app (.app (.const 9 []) (.sort .zero)) (.sort .zero)) (.sort .zero)) (.sort .zero))
      (.sort .zero)) := by decide
/-- a NON-recursor head never reaches the arm, whatever the count. -/
example : hStepFnA (extendEnvA emptyEnvA 9 ⟨.axiomM, 0, pinRecTypeA, none, 0, none⟩) (fun _ => none) []
    (.app (.app (.app (.app (.const 9 []) (.sort .zero)) (.sort .zero)) (.sort .zero)) pinIdRedexA) = none := by
  decide

#print axioms foldAppsA_appsSpineA
#print axioms erase_natExpandA
#print axioms piCountA_erase
#print axioms recAtMajorA_true
#print axioms recAtMajorA_of_below
#print axioms belowMajorA_of_at
#print axioms hStepFnA_app_none_inv
#print axioms whnfA_normal
#print axioms whnfA_of_normal
#print axioms whnfA_fuel_mono
#print axioms hStepFnA_app_struct
#print axioms structArmA_none_any
#print axioms unitGroupA_false_of_struct
#print axioms structGroupA_of_majorSort

end Rcic.Declarative.Ann
