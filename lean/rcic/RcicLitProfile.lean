import rcic.RcicFixtures

/-!
# Annex 25.3 `LiteralProfile` — the DT-017 literal-profile object

Annex 25 (`docs/rcic/00_ANNEX_25_OBJECT_DECISIONS.md`, cc ruling R-OBJ,
#6358) decides the object M-002b held out (`00_MASTER_CLOSURE_SPEC.md:3002`):

> `LiteralProfile {kinds: nat, type_ref, zero_ref, succ_ref}`
> (`MemberRef`s, 04 §3). Declared type = `const type_ref []`;
> expansion(n) = `succ_ref`ⁿ applied to `zero_ref`. Membership: the tag
> is a canonical Nat and `kinds` contains `nat`. Validation:
> `lookupMember` (04 §11) resolves all three; ⊢ `zero_ref : type_ref`;
> ⊢ `succ_ref : type_ref → type_ref`. FREE CHOICE: kinds = `{nat}`.
> Retiring the M-001 deviation (00:1272) is done as a **parallel rule
> plus a bridge lemma**, never by editing `HasTy.lit`/`HasTyT.lit`.

Kernel-side the `MemberRef`s are `Nat` member indices
(`ResolvedEnv.members : Nat → Option CheckedMember`); the group
dimension of 04 §3 lives in the carrier layer
(`apps/rcic-lit-profile`), which composes `rcic.lookup`.

**The parallel rule** (`LitProfileTy`) is a standalone inductive, not a
derived `HasTyT` theorem: for non-native profiles the sealed
`HasTyT.lit` (`RcicDeclarative.lean:3216`) is *definitionally* unable to
type `.lit t` at `const type_ref` — its premise is `natExpand t`, which
expands through refs 1 and 2 only. `HasTyT.lit` is therefore measured
as the native-profile special case of the general rule, and the bridge
(`litProfileTy_bridge`) is exactly where the two coincide.

**The agreement theorem** (`profileExpand_hasTyT`) is the 02 §8
declared-type/expansion agreement the DT-017 row records as
unmechanized (`00 §20.11`: "the profile's DECLARED type is not carried
… and 02 §8's declared-type/expansion agreement is NOT mechanized"),
proved by induction on the literal at fixed universe arity — the shape
`natExpand_hasTy_natPrefix` (`RcicFixtures.lean:126`) already pins for
the native profile.

The scm carrier (`apps/rcic-lit-profile`) validates the same object
against a `lookupMember`-shaped image; its member-type check is
stored-type equality, which is what `LitProfileValid`'s `mtype`
equalities transcribe.

`closure_claim = 0`. This module lands the OBJECT; it does not move
DT-017's row status.
-/

namespace Rcic.Declarative

/-! ## The object (25.3) -/

/-- 25.3 `LiteralProfile` — kernel-side form. `MemberRef`s are `Nat`
    member indices into `ResolvedEnv.members`; `kinds` is the annex's
    `{nat}`-style kind set. -/
structure LiteralProfile where
  kinds : List Nat
  type_ref : Nat
  zero_ref : Nat
  succ_ref : Nat

/-- The `nat` literal-kind code — the FREE CHOICE set `{nat}` is the
    smallest set the landed rule carries (`Expr.lit : Nat`). -/
def litKindNat : Nat := 0

/-- 25.3 declared type: `const type_ref []`. -/
def declTy (lp : LiteralProfile) : Expr Nat := .const lp.type_ref []

/-- 25.3 expansion: `succ_ref`ⁿ applied to `zero_ref` — `natExpand`
    generalized from refs 1/2 to the profile's own refs. -/
def profileExpand (lp : LiteralProfile) : Nat → Expr Nat
  | 0 => .const lp.zero_ref []
  | t + 1 => .app (.const lp.succ_ref []) (profileExpand lp t)

/-- 25.3 validation as member-record facts: `nat ∈ kinds` (the tag is a
    canonical Nat by `Expr.lit : Nat`), `lookupMember` resolves all
    three refs, and the stored types read `zero : type` and
    `succ : type → type`. `arity = 0` is carried because the declared
    type uses `const _ []` — a level-polymorphic member cannot serve. -/
structure LitProfileValid (E : ResolvedEnv) (lp : LiteralProfile) : Prop where
  nat_mem : litKindNat ∈ lp.kinds
  type_mem : ∃ m, E.members lp.type_ref = some m
  zero : ∃ m, E.members lp.zero_ref = some m ∧ m.arity = 0 ∧
    m.mtype = .const lp.type_ref []
  succ : ∃ m, E.members lp.succ_ref = some m ∧ m.arity = 0 ∧
    m.mtype = .pi (.const lp.type_ref []) (.const lp.type_ref [])
  /-- cc ruling on #6544, decision (i): the three refs ARE the native
      ones `HasTyT.lit`/`ConvT.lit` consult — `type_ref = 0`,
      `zero_ref = 1`, `succ_ref = 2` (`natExpand`'s hardcoded refs).
      The pre-clause measurement (below, "the `litProfileValid_native`
      fork") found validity env-relative without this clause; with it
      the collapse holds at every env, unconditionally. -/
  native : lp.type_ref = 0 ∧ lp.zero_ref = 1 ∧ lp.succ_ref = 2

/-! ## The parallel rule (M-001 retirement) -/

/-- 02 §8's literal rule with the DECLARED type — parallel to the
    sealed `HasTyT.lit`, which types `.lit t` at the expansion's type
    over `natExpand`. Here the literal is typed at the profile's
    declared `const type_ref []` from the profile's own expansion
    typed there, with `nat`-kind membership as the 03 §10 "validate
    profile membership" clause. `HasTy.lit`/`HasTyT.lit` are not
    edited. -/
inductive LitProfileTy (E : ResolvedEnv) (n : Nat) (lp : LiteralProfile) :
    LCtx → Expr Nat → Type where
  | intro (Γ : LCtx) (t : Nat) (hmem : litKindNat ∈ lp.kinds)
      (hexp : HasTyT E n Γ (profileExpand lp t) (declTy lp)) :
      LitProfileTy E n lp Γ (.lit t)

/-! ## DT-017 agreement — by induction on the literal -/

/-- 02 §8 declared-type/expansion agreement: under a valid profile the
    expansion `succ_ref`ⁿ `zero_ref` types at the declared
    `const type_ref []`. Induction on the literal at fixed arity —
    `zero` by `HasTyT.const`, `succ`ⁿ⁺¹ by `HasTyT.app` against
    `succ : type → type`, `instantiate0`/`instantiateLevels` on the
    const-shaped types all `rfl`.

    `HasTyT` is a `Type`, so the member witnesses cannot be `∃`-eliminated
    out of the `Prop` validity record. The proof instead matches the
    `Option`/`CheckedMember` data directly and reads the stored-type
    equalities back out of `v` as `Prop` `have`s; the `subst`s then make
    `instantiateLevels []` collapse by `rfl`. The unresolvable arms fail
    closed by `absurd` on the validity clause. -/
def profileExpand_hasTyT {E : ResolvedEnv} {n : Nat} {lp : LiteralProfile}
    {Γ : LCtx} (v : LitProfileValid E lp) :
    (t : Nat) → HasTyT E n Γ (profileExpand lp t) (declTy lp)
  | 0 =>
    match hm : E.members lp.zero_ref with
    | none =>
        absurd v.zero (by
          rintro ⟨m, hm2, -, -⟩
          rw [hm] at hm2
          nomatch hm2)
    | some ⟨mc, ma, mt, mb⟩ => by
        have hma : ma = 0 := by
          obtain ⟨m', hm', ha', -⟩ := v.zero
          rw [hm] at hm'
          cases hm'
          exact ha'
        have hmt : mt = .const lp.type_ref [] := by
          obtain ⟨m', hm', -, ht'⟩ := v.zero
          rw [hm] at hm'
          cases hm'
          exact ht'
        subst hma
        subst hmt
        exact HasTyT.const Γ lp.zero_ref [] ⟨mc, 0, .const lp.type_ref [], mb⟩ hm rfl rfl
  | t + 1 =>
    match hm : E.members lp.succ_ref with
    | none =>
        absurd v.succ (by
          rintro ⟨m, hm2, -, -⟩
          rw [hm] at hm2
          nomatch hm2)
    | some ⟨mc, ma, mt, mb⟩ => by
        have hma : ma = 0 := by
          obtain ⟨m', hm', ha', -⟩ := v.succ
          rw [hm] at hm'
          cases hm'
          exact ha'
        have hmt : mt = .pi (.const lp.type_ref []) (.const lp.type_ref []) := by
          obtain ⟨m', hm', -, ht'⟩ := v.succ
          rw [hm] at hm'
          cases hm'
          exact ht'
        subst hma
        subst hmt
        exact HasTyT.app Γ (.const lp.succ_ref []) (profileExpand lp t)
          (.const lp.type_ref []) (.const lp.type_ref [])
          (HasTyT.const Γ lp.succ_ref []
            ⟨mc, 0, .pi (.const lp.type_ref []) (.const lp.type_ref []), mb⟩
            hm rfl rfl)
          (profileExpand_hasTyT v t)

/-- The parallel rule in inference form: a valid profile plus a literal
    gives the literal typed at the declared type. -/
def litProfileTy_of_valid {E : ResolvedEnv} {n : Nat} {lp : LiteralProfile}
    {Γ : LCtx} (v : LitProfileValid E lp) (t : Nat) :
    LitProfileTy E n lp Γ (.lit t) :=
  .intro Γ t v.nat_mem (profileExpand_hasTyT v t)

/-! ## The bridge to `HasTyT.lit` -/

/-- At native shape (`zero_ref = 1`, `succ_ref = 2`) the profile
    expansion IS `natExpand` — the sealed rule's expansion is the
    native-profile special case, by reflexivity of the two definitions
    after the ref equalities. -/
theorem profileExpand_native {lp : LiteralProfile}
    (hz : lp.zero_ref = 1) (hs : lp.succ_ref = 2) :
    (t : Nat) → profileExpand lp t = natExpand t
  | 0 => by
      show Expr.const lp.zero_ref [] = Expr.const 1 []
      rw [hz]
  | t + 1 => by
      show Expr.app (Expr.const lp.succ_ref []) (profileExpand lp t) =
        Expr.app (Expr.const 2 []) (natExpand t)
      rw [hs]
      exact congrArg (fun e => Expr.app (Expr.const 2 []) e) (profileExpand_native hz hs t)

/-- The bridge: at native shape a `LitProfileTy` derivation lands in
    `HasTyT` — `HasTyT.lit` is the parallel rule's native-profile
    instance. The sealed rule is not edited; the profile expansion is
    rewritten to `natExpand` inside the carried evidence. -/
def litProfileTy_bridge {E : ResolvedEnv} {n : Nat} {lp : LiteralProfile}
    {Γ : LCtx} {t : Nat}
    (h : LitProfileTy E n lp Γ (.lit t))
    (hz : lp.zero_ref = 1) (hs : lp.succ_ref = 2) :
    HasTyT E n Γ (.lit t) (declTy lp) :=
  match h with
  | .intro _ _ _ hexp =>
      HasTyT.lit Γ t (declTy lp) ((profileExpand_native hz hs t).symm ▸ hexp)

/-- The converse bridge: at native shape, `HasTyT.lit`-shaped evidence
    (a `natExpand` typing at the declared type) produces the parallel
    rule's judgment. -/
def litProfileTy_of_expansion {E : ResolvedEnv} {n : Nat} {lp : LiteralProfile}
    {Γ : LCtx} {t : Nat}
    (hmem : litKindNat ∈ lp.kinds)
    (hexp : HasTyT E n Γ (natExpand t) (declTy lp))
    (hz : lp.zero_ref = 1) (hs : lp.succ_ref = 2) :
    LitProfileTy E n lp Γ (.lit t) :=
  .intro Γ t hmem (profileExpand_native hz hs t ▸ hexp)

/-! ## Pins: the native profile at `natEnvPrefix`

`natEnvPrefix` members 0/1/2 are `inductiveM (Sort 1)` /
`⟨.const 0 []⟩` / `⟨.pi (.const 0) (.const 0)⟩` — a `LitProfileValid`
native profile `{kinds = {nat}, type = 0, zero = 1, succ = 2}` with all
clauses `rfl`. -/

/-- The native profile — `natExpand`'s hardcoded refs as an object. -/
def natProfile : LiteralProfile := ⟨[litKindNat], 0, 1, 2⟩

/-- `natEnvPrefix` validates the native profile: `nat ∈ {nat}`, the
    three members resolve, zero stores `N`, succ stores `N → N`. -/
theorem natProfile_valid : LitProfileValid natEnvPrefix natProfile where
  nat_mem := by decide
  type_mem := ⟨natFamMember, rfl⟩
  zero := ⟨natZeroMember, rfl, rfl, rfl⟩
  succ := ⟨natSuccMember, rfl, rfl, rfl⟩
  native := ⟨rfl, rfl, rfl⟩

/-- The parallel rule firing at the native profile: `.lit t : N` as a
    `LitProfileTy` derivation. -/
def pin_litProfileTy_nat (n t : Nat) :
    LitProfileTy natEnvPrefix n natProfile [] (.lit t) :=
  litProfileTy_of_valid natProfile_valid t

/-- The bridge applied: the same literal lands in `HasTyT` at the
    declared type — the native-profile instance of `HasTyT.lit`. -/
def pin_litProfile_bridge_nat (n t : Nat) :
    HasTyT natEnvPrefix n [] (.lit t) (declTy natProfile) :=
  litProfileTy_bridge (pin_litProfileTy_nat n t) rfl rfl

/-- The converse bridge applied end to end: expansion evidence
    reproved through `profileExpand_hasTyT`, rewritten across the
    native `profileExpand = natExpand` equality, and lifted into
    `LitProfileTy` by `litProfileTy_of_expansion`. -/
def pin_litProfile_of_expansion_nat (n t : Nat) :
    LitProfileTy natEnvPrefix n natProfile [] (.lit t) :=
  litProfileTy_of_expansion (by decide)
    ((profileExpand_native (lp := natProfile) rfl rfl t).symm ▸
      profileExpand_hasTyT natProfile_valid t)
    rfl rfl

/-! ## Teeth — one per `LitProfileValid` clause -/

/-- `kinds` without `nat`: membership fails — the profile does not
    admit the literal kind. -/
theorem tooth_litProfile_kind_missing :
    ¬ LitProfileValid natEnvPrefix ⟨[], 0, 1, 2⟩ := by
  rintro ⟨hmem, -, -, -, -⟩
  nomatch hmem

/-- An unresolvable `type_ref`: the env holds no member at 9 —
    `lookupMember` fails closed. -/
theorem tooth_litProfile_type_unref :
    ¬ LitProfileValid natEnvPrefix ⟨[litKindNat], 9, 1, 2⟩ := by
  rintro ⟨-, ⟨m, hm⟩, -, -, -⟩
  nomatch hm

/-- `zero_ref` naming a member whose stored type is not
    `const type_ref` (ref 0 is the family's `Sort 1`): the
    `⊢ zero : type` clause fails. -/
theorem tooth_litProfile_zero_type :
    ¬ LitProfileValid natEnvPrefix ⟨[litKindNat], 0, 0, 2⟩ := by
  rintro ⟨-, -, ⟨m, hm, -, hty⟩, -, -⟩
  cases hm
  nomatch hty

/-- `succ_ref` naming a member whose stored type is not
    `type → type` (ref 1 stores `N`, not `N → N`): the
    `⊢ succ : type → type` clause fails. -/
theorem tooth_litProfile_succ_type :
    ¬ LitProfileValid natEnvPrefix ⟨[litKindNat], 0, 1, 1⟩ := by
  rintro ⟨-, -, -, ⟨m, hm, -, hty⟩, -⟩
  cases hm
  nomatch hty

/-! ## The `litProfileValid_native` fork — measured, then decided

Step 1 of the DT-017 deciding work (cc ruling on #6544): does
`LitProfileValid E lp` force `profileExpand lp t = natExpand t` (with
`declTy lp` the type `HasTyT.lit` assigns)? The pre-clause measurement:
**env-relative, not absolute** — `LitProfileValid`'s clauses were
stored-type checks only, so a second Nat-like group validated a
non-native profile. cc's ruling (decision (i)) added the `native`
clause pinning `type_ref = 0 ∧ zero_ref = 1 ∧ succ_ref = 2` — the refs
`HasTyT.lit`/`ConvT.lit` consult — so the collapse now holds at EVERY
env (`litProfileValid_expand_eq`), and the measured non-native profile
is a REFUSAL witness (`tooth_litProfile_nonnative`), not a valid
counterexample.

What is kept from the measurement: `natEnvPrefix_mem_none`/`_bound`
(the fixture's ref bound), `natEnv2`/`nat2*Member`/`altNatProfile` (the
non-native object, now refused), and the two data teeth
(`profileExpand altNatProfile ≠ natExpand`, `declTy altNatProfile ≠
const 0 []`). -/

/-- The collapse, now universal: a valid profile's expansion IS
    `natExpand` and its declared type IS `const 0 []` — the type
    `natExpand_hasTy_natPrefix` assigns and `HasTy.lit`/`HasTyT.lit`
    consume. Post-decision-(i): the `native` clause forces the refs, so
    no env-uniqueness premise is needed. -/
theorem litProfileValid_expand_eq {E : ResolvedEnv} {lp : LiteralProfile}
    (v : LitProfileValid E lp) (t : Nat) :
    profileExpand lp t = natExpand t ∧ declTy lp = .const 0 [] := by
  obtain ⟨ht, hz, hs⟩ := v.native
  exact ⟨profileExpand_native hz hs t, by unfold declTy; rw [ht]⟩

/-- `natEnvPrefix` holds exactly three members: nothing resolves at
    `r ≥ 3`. -/
theorem natEnvPrefix_mem_none {r : Nat} (h : 3 ≤ r) :
    natEnvPrefix.members r = none := by
  have h2 : ¬ r = 2 := by omega
  have h1 : ¬ r = 1 := by omega
  have h0 : ¬ r = 0 := by omega
  simp only [natEnvPrefix, extendEnv, emptyEnv, if_neg h2, if_neg h1,
    if_neg h0]

/-- Every resolvable `natEnvPrefix` ref is one of `0 / 1 / 2`. -/
theorem natEnvPrefix_mem_bound {r : Nat} {m : CheckedMember}
    (h : natEnvPrefix.members r = some m) : r = 0 ∨ r = 1 ∨ r = 2 := by
  match r with
  | 0 => exact .inl rfl
  | 1 => exact .inr (.inl rfl)
  | 2 => exact .inr (.inr rfl)
  | r + 3 =>
      rw [natEnvPrefix_mem_none (r := r + 3) (by omega)] at h
      nomatch h

/-- `litProfileValid_native`, per-env face: over `natEnvPrefix` a valid
    profile carries the native refs — post-decision-(i) this is the
    `native` clause itself. (The env-bound machinery above is what made
    the collapse derivable BEFORE the clause landed.) -/
theorem litProfileValid_natPrefix_native {lp : LiteralProfile}
    (v : LitProfileValid natEnvPrefix lp) :
    lp.type_ref = 0 ∧ lp.zero_ref = 1 ∧ lp.succ_ref = 2 :=
  v.native

/-- The `litProfileValid_native` content at `natEnvPrefix`: the profile
    expansion collapses to `natExpand`, and the declared type is
    `const 0 []` — the env-specialized face of
    `litProfileValid_expand_eq`. -/
theorem litProfileValid_natPrefix_expand_eq {lp : LiteralProfile}
    (v : LitProfileValid natEnvPrefix lp) (t : Nat) :
    profileExpand lp t = natExpand t ∧ declTy lp = .const 0 [] :=
  litProfileValid_expand_eq v t

/-- The second group's family member (ref 3): same `inductiveM` shape
    as `natFamMember`, its own ref. -/
def nat2FamMember : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩

/-- The second group's zero (ref 4): stored type `const 3 []`. -/
def nat2ZeroMember : CheckedMember := ⟨.constructorM, 0, .const 3 [], none⟩

/-- The second group's succ (ref 5): stored type `const 3 → const 3`. -/
def nat2SuccMember : CheckedMember :=
  ⟨.constructorM, 0, .pi (.const 3 []) (.const 3 []), none⟩

/-- `natEnvPrefix` extended by the second Nat-like group at refs
    3/4/5 — the counterexample env. -/
def natEnv2 : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv natEnvPrefix 3 nat2FamMember)
    4 nat2ZeroMember) 5 nat2SuccMember

/-- The non-native profile on `natEnv2`: `{nat}` kinds, refs 3/4/5. -/
def altNatProfile : LiteralProfile := ⟨[litKindNat], 3, 4, 5⟩

/-- The refusal tooth (cc ruling (3)): a non-native profile is REFUSED —
    `altNatProfile` still satisfies the four env clauses over `natEnv2`,
    but the `native` clause pins refs 0/1/2 and `type_ref = 3` fails. -/
theorem tooth_litProfile_nonnative :
    ¬ LitProfileValid natEnv2 altNatProfile := by
  rintro ⟨-, -, -, -, ⟨h3, -, -⟩⟩
  nomatch h3

/-- Expansion tooth: the refused non-native profile's expansion is not
    `natExpand` — already at `t = 0` (`const 4 []` vs `const 1 []`). -/
theorem tooth_litProfile_nonnative_expand :
    profileExpand altNatProfile 0 ≠ natExpand 0 := by
  intro h; nomatch h

/-- Declared-type tooth: the refused non-native profile's declared type
    is `const 3 []`, not the `const 0 []` `HasTyT.lit` assigns at
    `natEnvPrefix`. -/
theorem tooth_litProfile_nonnative_declTy :
    declTy altNatProfile ≠ .const 0 [] := by
  intro h; nomatch h

/-! ## DT-017 — the deciding pair (cc ruling #6544, decision (i))

02:242 / §14 "literal expansion soundness": at EVERY env carrying a
valid profile, the sealed rules consume the profile's own data —
`HasTyT.lit` types `.lit t` at `declTy lp` and `ConvT.lit` pairs `.lit
t` with `profileExpand lp t` at that type. Under the `native` clause
the profile's data IS the native data (`litProfileValid_expand_eq`), so
both sides discharge against `natExpand`/`const 0 []` — the measured
env-relativity is gone by construction. This is the statement the S0
plan's `LitProfileTy`-flavored shape could not discharge: no parallel
relation stands between the profile and `HasTyT`/`ConvT` here — the
rules themselves deliver the pair. -/

/-- DT-017: literal expansion soundness — the literal's type and
    expansion under `HasTyT.lit`/`ConvT.lit` equal the profile's. -/
def DT017T_litExpansionSound {E : ResolvedEnv} {n : Nat}
    {lp : LiteralProfile} {Γ : LCtx}
    (v : LitProfileValid E lp) (t : Nat) :
    HasTyT E n Γ (.lit t) (declTy lp) ×'
      ConvT E n Γ (.lit t) (profileExpand lp t) (declTy lp) :=
  have heq := (litProfileValid_expand_eq v t).1
  have hexp : HasTyT E n Γ (natExpand t) (declTy lp) :=
    heq ▸ profileExpand_hasTyT v t
  ⟨ HasTyT.lit Γ t (declTy lp) hexp,
    heq.symm ▸ ConvT.lit Γ t (natExpand t) (declTy lp) (.of t) hexp ⟩

/-- The deciding pair at the native fixture: `.lit t` typed at `N` and
    convertible to `natExpand t` — the E-NatRef content as a DT-017
    instance. -/
def pin_DT017T_nat (n t : Nat) :
    HasTyT natEnvPrefix n [] (.lit t) (declTy natProfile) ×'
      ConvT natEnvPrefix n [] (.lit t) (profileExpand natProfile t)
        (declTy natProfile) :=
  DT017T_litExpansionSound natProfile_valid t

#print axioms profileExpand_hasTyT
#print axioms litProfileTy_bridge
#print axioms litProfileTy_of_expansion
#print axioms pin_litProfileTy_nat
#print axioms pin_litProfile_bridge_nat
#print axioms tooth_litProfile_kind_missing
#print axioms tooth_litProfile_type_unref
#print axioms tooth_litProfile_zero_type
#print axioms tooth_litProfile_succ_type
#print axioms litProfileValid_expand_eq
#print axioms natEnvPrefix_mem_none
#print axioms natEnvPrefix_mem_bound
#print axioms litProfileValid_natPrefix_native
#print axioms litProfileValid_natPrefix_expand_eq
#print axioms tooth_litProfile_nonnative
#print axioms tooth_litProfile_nonnative_expand
#print axioms tooth_litProfile_nonnative_declTy
#print axioms DT017T_litExpansionSound
#print axioms pin_DT017T_nat
