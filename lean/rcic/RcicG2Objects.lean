/-
RCIC 07 §3/§14/§18 — G2-S1 object layer: the support inductive blocks and
the `SV<d>` mirroring, as `CheckedMember` blocks plus the `Val → Expr`
embedding.

Rulings on #6697 (cc): (a) **no `lit` anywhere** — the scm runtime refuses
literals and `.lit` was the batch-21 aliasing hole; (b) **no unary Nat for
large values** — `Pos`/`BNat` binary blocks carry i64 payloads (offset
`n + 2^63`, two's-complement aligned), codepoints, and byte values;
(c) `SVP<r>` is a `definitionM` alias to `SV<payload digest>` — this module
builds only the `SV` blocks it aliases to; (d) `Eq` is an inductive block
(the `RcicPinEq` precedent), connectives `And`/`Or`/`True`/`False` are
inductive blocks (`andEnvU` precedent, `RcicTypedGroupPins:2445`).

Member shapes follow `RcicFixtures`' `natEnvU` block: family `inductiveM`
at a `Sort` arity, constructors `constructorM` storing their full type,
one `recursorM` (arity 1, `param 0` motive level) last — `EnvWfT.group`'s
05 §3 order (family, ctors, recursor). Blocks are CONTIGUOUS
`(f, fm) :: ctors ++ [(rr, rm)]` ranges, the `GroupMembersT` shape the S3
admission slice (the G2 refinement of dt025's G1-S3) consumes.

`SV<d>` mirroring: one inductive group per `CoreTy` subterm of a bound
type. Each ctor's field types are *other* `SV<…>` `const`s — which is what
forces the digest set to the transitive subterm closure (S0_G2 §1). The
`Val` grammar (`ScmCore.lean:199`) supplies the value-side constructors.

This file defines OBJECTS only — member lists, term builders, and their
`HasTyT` typing lemmas over abstract membership hypotheses. The concrete
pin environment and per-`CoreTy`-form embedding pins live in
`RcicG2Pins`. `EnvWfT` admission of these blocks is G2-S3, not this slice.
-/
import rcic.RcicFixtures
import rcic.ScmCore

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm

/-- Indices the support blocks occupy inside an environment under
    construction: the family member of `Pos`, of `BNat`, and of `Bool`.
    `SV<i64>`/`SV<str>`/`SV<bytes>` ctor fields reference `bPos`/`bBNat`;
    `AssertTerm.bool` compiles against `bBool`. -/
structure SupRefs where
  bPos : Nat
  bBNat : Nat
  bBool : Nat
  deriving Repr

/-- Application spine: `appsp c [x₀,…] = app (… (app (const c) x₀) …)`. -/
def appsp (c : Nat) (xs : List (Expr Nat)) : Expr Nat :=
  xs.foldl Expr.app (.const c [])

/-! ## Support block templates — contiguous `EnvWfT.group`-shaped ranges -/

/-- `Pos := one | bit0 Pos | bit1 Pos` at base `b`: the positive binary
    naturals. Recursor:
    `Π (P : Pos → Sort u), P one → (∀ p, P p → P (bit0 p)) →
      (∀ p, P p → P (bit1 p)) → ∀ p, P p`. -/
def posRecTy (b : Nat) : Expr Nat :=
  .pi (.pi (.const b []) (.sort (.param 0)))            -- P : Pos → Sort u
   (.pi (.app (.bvar 0) (.const (b + 1) []))            -- m1 : P one
    (.pi (.pi (.const b [])                             -- m0 : Π p : Pos,
          (.pi (.app (.bvar 2) (.bvar 0))               --        Π ih : P p,
            (.app (.bvar 3) (.app (.const (b + 2) []) (.bvar 1)))))  -- P (bit0 p)
     (.pi (.pi (.const b [])                            -- m1' : Π p : Pos,
          (.pi (.app (.bvar 3) (.bvar 0))               --        Π ih : P p,
            (.app (.bvar 4) (.app (.const (b + 3) []) (.bvar 1)))))  -- P (bit1 p)
      (.pi (.const b [])                                -- major : Pos
        (.app (.bvar 4) (.bvar 0))))))                  -- body : P major

def posMembersAt (b : Nat) : List (Nat × CheckedMember) :=
  [ (b,     ⟨.inductiveM, 0, .sort (.succ .zero), none⟩),
    (b + 1, ⟨.constructorM, 0, .const b [], none⟩),
    (b + 2, ⟨.constructorM, 0, .pi (.const b []) (.const b []), none⟩),
    (b + 3, ⟨.constructorM, 0, .pi (.const b []) (.const b []), none⟩),
    (b + 4, ⟨.recursorM, 1, posRecTy b, none⟩) ]

/-- `BNat := zero | pos Pos` at base `b` with `Pos`'s family at `pf`.
    Recursor: `Π (P : BNat → Sort u), P zero → (∀ p : Pos, P (pos p)) →
    ∀ n, P n` (`pos`'s field is `Pos`, not `BNat` — no IH). -/
def bnatRecTy (b pf : Nat) : Expr Nat :=
  .pi (.pi (.const b []) (.sort (.param 0)))            -- P : BNat → Sort u
   (.pi (.app (.bvar 0) (.const (b + 1) []))            -- mz : P zero
    (.pi (.pi (.const pf [])                            -- ms : Π p : Pos,
          (.app (.bvar 2) (.app (.const (b + 2) []) (.bvar 0))))  -- P (pos p)
     (.pi (.const b [])                                 -- major : BNat
       (.app (.bvar 3) (.bvar 0)))))                    -- body : P major

def bnatMembersAt (b pf : Nat) : List (Nat × CheckedMember) :=
  [ (b,     ⟨.inductiveM, 0, .sort (.succ .zero), none⟩),
    (b + 1, ⟨.constructorM, 0, .const b [], none⟩),
    (b + 2, ⟨.constructorM, 0, .pi (.const pf []) (.const b []), none⟩),
    (b + 3, ⟨.recursorM, 1, bnatRecTy b pf, none⟩) ]

/-- `Bool := false | true` at base `b`. -/
def boolRecTy (b : Nat) : Expr Nat :=
  .pi (.pi (.const b []) (.sort (.param 0)))            -- P : Bool → Sort u
   (.pi (.app (.bvar 0) (.const (b + 1) []))            -- mf : P false
    (.pi (.app (.bvar 1) (.const (b + 2) []))           -- mt : P true
     (.pi (.const b [])                                 -- major : Bool
       (.app (.bvar 3) (.bvar 0)))))                    -- body : P major

def boolMembersAt (b : Nat) : List (Nat × CheckedMember) :=
  [ (b,     ⟨.inductiveM, 0, .sort (.succ .zero), none⟩),
    (b + 1, ⟨.constructorM, 0, .const b [], none⟩),
    (b + 2, ⟨.constructorM, 0, .const b [], none⟩),
    (b + 3, ⟨.recursorM, 1, boolRecTy b, none⟩) ]

/-- `True` (a `Prop`) at base `b`: one nullary ctor `tt`. -/
def trueRecTy (b : Nat) : Expr Nat :=
  .pi (.pi (.const b []) (.sort (.param 0)))            -- P : True → Sort u
   (.pi (.app (.bvar 0) (.const (b + 1) []))            -- mt : P tt
    (.pi (.const b [])                                  -- major : True
      (.app (.bvar 2) (.bvar 0))))                     -- body : P major

def trueMembersAt (b : Nat) : List (Nat × CheckedMember) :=
  [ (b,     ⟨.inductiveM, 0, .sort .zero, none⟩),
    (b + 1, ⟨.constructorM, 0, .const b [], none⟩),
    (b + 2, ⟨.recursorM, 1, trueRecTy b, none⟩) ]

/-- `False` (a `Prop`) at base `b`: no ctors; the recursor is the
    eliminator `Π (P : False → Sort u) (x : False), P x`. -/
def falseRecTy (b : Nat) : Expr Nat :=
  .pi (.pi (.const b []) (.sort (.param 0)))            -- P : False → Sort u
   (.pi (.const b [])                                   -- major : False
     (.app (.bvar 1) (.bvar 0)))                        -- body : P major

def falseMembersAt (b : Nat) : List (Nat × CheckedMember) :=
  [ (b,     ⟨.inductiveM, 0, .sort .zero, none⟩),
    (b + 1, ⟨.recursorM, 1, falseRecTy b, none⟩) ]

/-- `And`/`Or`/`Eq`'s family type `Prop → Prop → Prop` (shared shape). -/
def propPropFamTy : Expr Nat :=
  .pi (.sort .zero) (.pi (.sort .zero) (.sort .zero))

/-- `And : Prop → Prop → Prop` at base `b`, the `andEnvU` shape shifted.
    `intro : Π (A B : Prop), A → B → And A B`;
    `And.rec : Π (A B : Prop) (P : And A B → Sort u)
      (m : Π (a : A) (b : B), P (intro A B a b)) (t : And A B), P t`. -/
def andApp (b : Nat) (x y : Expr Nat) : Expr Nat :=
  .app (.app (.const b []) x) y

def andIntroTy (b : Nat) : Expr Nat :=
  .pi (.sort .zero) (.pi (.sort .zero) (.pi (.bvar 1) (.pi (.bvar 1)
    (andApp b (.bvar 3) (.bvar 2)))))

def andRecTy (b : Nat) : Expr Nat :=
  .pi (.sort .zero) (.pi (.sort .zero)                  -- A B : Prop
   (.pi (.pi (andApp b (.bvar 1) (.bvar 0)) (.sort (.param 0)))  -- P : And A B → Sort u
    (.pi (.pi (.bvar 2)                                     -- m : Π (a:A)
          (.pi (.bvar 2)                                    --     (b:B),
            (.app (.bvar 2)                                 --   P
              (appsp (b + 1) [.bvar 4, .bvar 3, .bvar 1, .bvar 0]))))  -- (intro A B a b)
     (.pi (andApp b (.bvar 3) (.bvar 2))                    -- t : And A B
       (.app (.bvar 2) (.bvar 0))))))                       -- P t

def andMembersAt (b : Nat) : List (Nat × CheckedMember) :=
  [ (b,     ⟨.inductiveM, 0, propPropFamTy, none⟩),
    (b + 1, ⟨.constructorM, 0, andIntroTy b, none⟩),
    (b + 2, ⟨.recursorM, 1, andRecTy b, none⟩) ]

/-- `Or : Prop → Prop → Prop` at base `b`: `inl : Π A B, A → Or A B`,
    `inr : Π A B, B → Or A B`; recursor with two minors. Two constructors
    in `Prop` select `EliminationSelection.multipleProp`, so the policy is
    `propOnly`: the motive lands in `Sort 0` and the recursor has the
    family's arity (0), no motive level. -/
def orApp (b : Nat) (x y : Expr Nat) : Expr Nat :=
  .app (.app (.const b []) x) y

def orInlTy (b : Nat) : Expr Nat :=
  .pi (.sort .zero) (.pi (.sort .zero) (.pi (.bvar 1)
    (orApp b (.bvar 2) (.bvar 1))))

def orInrTy (b : Nat) : Expr Nat :=
  .pi (.sort .zero) (.pi (.sort .zero) (.pi (.bvar 0)
    (orApp b (.bvar 2) (.bvar 1))))

def orRecTy (b : Nat) : Expr Nat :=
  .pi (.sort .zero) (.pi (.sort .zero)                  -- A B : Prop
   (.pi (.pi (orApp b (.bvar 1) (.bvar 0)) (.sort .zero))  -- P : Or A B → Prop
    (.pi (.pi (.bvar 2)                                      -- ml : Π (a:A),
          (.app (.bvar 1)                                    --   P
            (appsp (b + 1) [.bvar 3, .bvar 2, .bvar 0])))      --   (inl A B a)
     (.pi (.pi (.bvar 2)                                     -- mr : Π (b:B),
          (.app (.bvar 2)                                    --   P
            (appsp (b + 2) [.bvar 4, .bvar 3, .bvar 0])))      --   (inr A B b)
      (.pi (orApp b (.bvar 4) (.bvar 3))                     -- t : Or A B
        (.app (.bvar 3) (.bvar 0)))))))                      -- P t

def orMembersAt (b : Nat) : List (Nat × CheckedMember) :=
  [ (b,     ⟨.inductiveM, 0, propPropFamTy, none⟩),
    (b + 1, ⟨.constructorM, 0, orInlTy b, none⟩),
    (b + 2, ⟨.constructorM, 0, orInrTy b, none⟩),
    (b + 3, ⟨.recursorM, 0, orRecTy b, none⟩) ]

/-- `Eq : Π (A : Sort 1) (a b : A), Prop` at base `b` — the
    `RcicPinEqEraseWf` block (`eqFamT`/`eqReflT`/`eqRecT`) shifted to `b`:
    family arity 0 with `A`, `a` parameters and `b` the sole index.
    Monomorphic at `Sort 1` because every G2 carrier (`SV<d>`, `BNat`,
    `Bool`) is a `Sort 1` family. `refl : Π (A : Sort 1) (a : A),
    Eq A a a`; `Eq.rec` is the J eliminator, arity 1 (the motive level):
    `Π (A : Sort 1) (a : A) (P : Π (b : A), Eq A a b → Sort v)
      (h : P a (refl A a)) (b : A) (e : Eq A a b), P b e`. -/
def eqFamTy : Expr Nat :=
  .pi (.sort (.succ .zero)) (.pi (.bvar 0) (.pi (.bvar 1) (.sort .zero)))

def eqApp (b : Nat) (A x y : Expr Nat) : Expr Nat :=
  .app (.app (.app (.const b []) A) x) y

def eqReflTy (b : Nat) : Expr Nat :=
  .pi (.sort (.succ .zero)) (.pi (.bvar 0)
    (eqApp b (.bvar 1) (.bvar 0) (.bvar 0)))

def eqRecTy (b : Nat) : Expr Nat :=
  .pi (.sort (.succ .zero))                                 -- A : Sort 1
   (.pi (.bvar 0)                                           -- a : A
    (.pi (.pi (.bvar 1)                                     -- P : Π (b : A),
          (.pi (eqApp b (.bvar 2) (.bvar 1) (.bvar 0))      --   Eq A a b →
            (.sort (.param 0))))                            --   Sort v
     (.pi (.app (.app (.bvar 0) (.bvar 1))                  -- h : P a
            (.app (.app (.const (b + 1) []) (.bvar 2)) (.bvar 1)))  -- (refl A a)
      (.pi (.bvar 3)                                        -- b : A
        (.pi (eqApp b (.bvar 4) (.bvar 3) (.bvar 0))        -- e : Eq A a b
          (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))))    -- P b e

def eqMembersAt (b : Nat) : List (Nat × CheckedMember) :=
  [ (b,     ⟨.inductiveM, 0, eqFamTy, none⟩),
    (b + 1, ⟨.constructorM, 0, eqReflTy b, none⟩),
    (b + 2, ⟨.recursorM, 1, eqRecTy b, none⟩) ]

/-! ## `SV<d>` blocks — constructors mirroring `CoreTy d` (`ScmCore.lean:72`) -/

/-- One constructor field of an `SV<d>` ctor: its domain `Expr` (a closed
    `const` — a sibling `SV<…>` family or `BNat`) and whether it is
    SELF-typed (the `SV<d>` family itself — self fields earn a recursor
    induction hypothesis). -/
structure SvField where
  dom : Expr Nat
  self : Bool := false

/-- `refOf` maps a `CoreTy` subterm to its `SV` family's member index.
    The constructor field lists of `SV<t>`'s block, in `EnvWfT.group`
    order — one `List SvField` per ctor, mirroring `CoreTy`'s forms. -/
def svCtors (sup : SupRefs) (refOf : CoreTy → Nat) (fam : Nat) :
    CoreTy → List (List SvField)
  | .i64      => [ [⟨.const sup.bBNat [], false⟩] ]           -- mk : BNat → SV
  | .bool     => [ [], [] ]                                   -- ff, tt
  | .str      => [ [], [⟨.const sup.bBNat [], false⟩,         -- snil ;
                        ⟨.const fam [], true⟩] ]              -- scons cp self
  | .bytes    => [ [], [⟨.const sup.bBNat [], false⟩,         -- bnil ;
                        ⟨.const fam [], true⟩] ]              -- bcons byte self
  | .list t   => [ [], [⟨.const (refOf t) [], false⟩,         -- nil ;
                        ⟨.const fam [], true⟩] ]              -- cons x self
  | .pair a b => [ [⟨.const (refOf a) [], false⟩,             -- mk a b
                    ⟨.const (refOf b) [], false⟩] ]
  | .sum ts   => ts.map fun tᵢ => [⟨.const (refOf tᵢ) [], false⟩]  -- injᵢ x
  | .record fs => [ fs.map fun ⟨_, tᵢ⟩ => ⟨.const (refOf tᵢ) [], false⟩ ] -- mk fields

/-- A ctor's stored `mtype`: `Π fields → SV<fam>`. -/
def svCtorTy (fam : Nat) (fields : List SvField) : Expr Nat :=
  fields.foldr (fun f T => .pi f.dom T) (.const fam [])

/-- The recursor type of `SV<d>` at family index `f` with ctor member
    indices `ctorRefs`. Per `natRecTypeU`'s 05 §11 order —
    params (0) · motive · minors · major — each minor is
    `Π fields, (Π ih : P field)ⱼ∈self, P (ctor fields)`; the motive's
    level is `param 0` (arity 1). -/
def svRecTy (f : Nat) (ctors : List (Nat × List SvField)) : Expr Nat :=
  let motive : Expr Nat := .pi (.const f []) (.sort (.param 0))
  let minors : List (Expr Nat) := ctors.mapIdx fun i (cIdx, fs) =>
    let k := fs.length
    let selfs : List Nat := (fs.enum.filter (·.2.self)).map Prod.fst
    let s := selfs.length
    let ctorApp : Expr Nat := (List.range k).foldl
      (fun e j => .app e (.bvar (k + s - 1 - j))) (.const cIdx [])
    let ihDoms : List (Expr Nat) := selfs.mapIdx fun j fpos =>
      .app (.bvar (i + k + j)) (.bvar (k + j - fpos - 1))
    (fs.map SvField.dom ++ ihDoms).foldr Expr.pi
      (.app (.bvar (i + k + s)) ctorApp)
  .pi motive (minors.foldr Expr.pi
    (.pi (.const f []) (.app (.bvar (minors.length + 1)) (.bvar 0))))

/-- `SV<t>`'s contiguous member block at base `b` — `[fam, ctors…, rec]`,
    `EnvWfT.group`'s `(f, fm) :: ctors ++ [(rr, rm)]` shape. The recursor
    index is `b + 1 + #ctors`. -/
def svMembersAt (sup : SupRefs) (refOf : CoreTy → Nat) (b : Nat)
    (t : CoreTy) : List (Nat × CheckedMember) :=
  let fields := svCtors sup refOf b t
  (b, ⟨.inductiveM, 0, .sort (.succ .zero), none⟩) ::
    (fields.mapIdx fun j fs =>
      (b + 1 + j, ⟨.constructorM, 0, svCtorTy b fs, none⟩)) ++
    [(b + 1 + fields.length,
      ⟨.recursorM, 1,
        svRecTy b ((List.range fields.length).map (b + 1 + ·) |>.zip
          fields), none⟩)]

/-- A `definitionM` member — the `SVP<r>` alias shape (ruling 1): body a
    bare family `const`, `mtype` the `Sort 1` arity. -/
def svAliasMemberAt (r tgt : Nat) : Nat × CheckedMember :=
  (r, ⟨.definitionM, 0, .sort (.succ .zero), some (.const tgt [])⟩)

/-! ## Term builders — binary naturals (no `lit`, no unary Nat) -/

/-- Bits of `n` below the leading one, MSB→LSB:
    `posBits 1 = []`, `posBits 6 = [true, false]` (`110`). `irreducible`:
    it is well-founded (`termination_by n`), so kernel `whnf` of any term
    containing `posBits n` would unfold the `Acc` certificate — `O(n)`
    recursion, fatal at i64 scale. Keeping it rigid lets `posTermAux`-
    headed terms stay stuck-but-matchable; literal-freedom and typing
    are proven compositionally instead of by evaluation. -/
@[irreducible]
def posBits : Nat → List Bool
  | 0 => []
  | 1 => []
  | n + 2 => posBits ((n + 2) / 2) ++ [(n + 2) % 2 == 1]
termination_by n => n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- `Pos` tower over a bit list — folds `e ↦ bit0 e` / `e ↦ bit1 e`
    MSB→LSB onto the base term `e`. -/
def posTermAux (sup : SupRefs) (e : Expr Nat) : List Bool → Expr Nat
  | [] => e
  | b :: bs =>
      posTermAux sup
        (.app (.const (if b then sup.bPos + 3 else sup.bPos + 2) []) e) bs

/-- The `Pos` constructor term of `n ≥ 1` (callers guarantee nonzero). -/
def posTerm (sup : SupRefs) (n : Nat) : Expr Nat :=
  posTermAux sup (.const (sup.bPos + 1) []) (posBits n)

/-- The `BNat` constructor term of `n : Nat`. -/
def bnatTerm (sup : SupRefs) (n : Nat) : Expr Nat :=
  if n = 0 then .const (sup.bBNat + 1) []
  else .app (.const (sup.bBNat + 2) []) (posTerm sup n)

/-- The i64 payload encode — ruling 2: `BNat` at offset `n + 2^63`
    (two's-complement aligned). Out-of-range `Int`s are refused. -/
def i64Term (sup : SupRefs) (mk : Nat) (n : Int) : Option (Expr Nat) :=
  if -(2^63 : Int) ≤ n ∧ n < 2^63
  then some (.app (.const mk []) (bnatTerm sup (n + 2^63).toNat))
  else none

/-- `cons`-tower builder: `consTower nilIdx cIdx [e₀,…,eₖ] =
    cons e₀ (cons … (cons eₖ nil))`. -/
def consTower (nilIdx cIdx : Nat) (es : List (Expr Nat)) : Expr Nat :=
  es.foldr (fun e acc => .app (.app (.const cIdx []) e) acc)
    (.const nilIdx [])

/-- A string embedded as an `SV<str>` `scons` tower over codepoint
    `BNat`s (ruling 6). -/
def strTerm (sup : SupRefs) (snil scons : Nat) (s : String) : Expr Nat :=
  consTower snil scons (s.toList.map (fun c => bnatTerm sup c.toNat))

/-- A byte list embedded as an `SV<bytes>` `bcons` tower over byte-value
    `BNat`s; elements out of `[0, 256)` refuse. -/
def bytesTerm (sup : SupRefs) (bnil bcons : Nat) (bs : List Int) :
    Option (Expr Nat) :=
  if bs.all fun b => decide (0 ≤ b ∧ b < 256) then
    some (consTower bnil bcons (bs.map (fun b => bnatTerm sup b.toNat)))
  else none

/-- Elementwise `Option` traversal. -/
def mapOpt : List α → (α → Option β) → Option (List β)
  | [], _ => some []
  | a :: as, f => do
      let b ← f a
      let bs ← mapOpt as f
      pure (b :: bs)

/-! ## `Val → Expr` embedding — the `ValueAt`-becomes-`HasTyT` direction -/

/-- `embedValAt sup refOf t v` — `v` embedded as an `SV<t>` constructor
    term when `v` matches `t`'s shape. The shape checks mirror `toCore`
    (`ScmCore.lean:235`) pointwise: i64 range, bool ∈ {0,1}, bytes ∈
    [0,256), list elementwise, pair componentwise, sum tag `get?`,
    record positional arity. `refOf t'` is `SV<t'`'s family index; the
    ctor of `SV<t>` at position `j` is `refOf t + 1 + j`. -/
def embedValAt (sup : SupRefs) (refOf : CoreTy → Nat) :
    CoreTy → Val → Option (Expr Nat)
  | .i64, .i n =>
      i64Term sup (refOf .i64 + 1) n
  | .bool, .b b =>
      if b = 0 then some (.const (refOf .bool + 1) [])
      else if b = 1 then some (.const (refOf .bool + 2) [])
      else none
  | .str, .s s =>
      some (strTerm sup (refOf .str + 1) (refOf .str + 2) s)
  | .bytes, .y bs =>
      bytesTerm sup (refOf .bytes + 1) (refOf .bytes + 2) bs
  | .list t, .l xs => do
      let es ← mapOpt xs.attach (fun ⟨x, _⟩ => embedValAt sup refOf t x)
      pure (consTower (refOf (.list t) + 1) (refOf (.list t) + 2) es)
  | .pair a b, .p x y => do
      let x' ← embedValAt sup refOf a x
      let y' ← embedValAt sup refOf b y
      pure (.app (.app (.const (refOf (.pair a b) + 1) []) x') y')
  | .sum ts, .j i v => do
      if i < 0 then none else
      match ts.get? i.toNat with
      | some tᵢ =>
          match embedValAt sup refOf tᵢ v with
          | some v' => pure (.app (.const (refOf (.sum ts) + 1 + i.toNat) []) v')
          | none => none
      | none => none
  | .record fs, .r xs => do
      if fs.length = xs.length then
        match mapOpt (fs.zip xs).attach
            (fun ⟨(f, x), _⟩ => embedValAt sup refOf f.2 x) with
        | some es => pure (appsp (refOf (.record fs) + 1) es)
        | none => none
      else none
  | _, _ => none
termination_by _ v => sizeOf v
decreasing_by
  all_goals
    (first
      | exact Nat.lt_of_lt_of_le
          (List.sizeOf_lt_of_mem (List.of_mem_zip ‹_›).2) (by simp)
      | exact Nat.lt_of_lt_of_le (List.sizeOf_lt_of_mem ‹_›) (by simp)
      | decreasing_tactic
      | simp_arith)

/-! ## Generic typing lemmas for the builders -/

/-- `HasTyT` of a `const` at an arity-0 member — the premise pack the
    pins consume. -/
def const_ty (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (r : Nat)
    (m : CheckedMember) (hr : E.members r = some m) (ha : m.arity = 0) :
    HasTyT E n Γ (.const r []) (instantiateLevels [] m.mtype) :=
  .const Γ r [] m hr (by rw [ha]; rfl) rfl

/-- `bit0`/`bit1`-fold typing: if `e : Pos` in `E`, so is
    `posTermAux sup e bs`. Equation-style on `bs` — `HasTyT` is data
    (`Type`), so `induction`/`List.rec` is not available. -/
def posTermAux_ty (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (sup : SupRefs)
    (h0 : E.members (sup.bPos + 2) =
      some ⟨.constructorM, 0, .pi (.const sup.bPos []) (.const sup.bPos []), none⟩)
    (h1 : E.members (sup.bPos + 3) =
      some ⟨.constructorM, 0, .pi (.const sup.bPos []) (.const sup.bPos []), none⟩) :
    ∀ (e : Expr Nat) (bs : List Bool),
    HasTyT E n Γ e (.const sup.bPos []) →
    HasTyT E n Γ (posTermAux sup e bs) (.const sup.bPos [])
  | _, [], he => he
  | e, false :: bs, he =>
      posTermAux_ty E n Γ sup h0 h1
        (.app (.const (sup.bPos + 2) []) e) bs
        (.app _ _ _ _ _ (const_ty E n Γ _ _ h0 rfl) he)
  | e, true :: bs, he =>
      posTermAux_ty E n Γ sup h0 h1
        (.app (.const (sup.bPos + 3) []) e) bs
        (.app _ _ _ _ _ (const_ty E n Γ _ _ h1 rfl) he)

/-- `posTerm m : Pos` (the `posBits` list is irrelevant to the typing —
    the fold preserves it for any bits). -/
def posTerm_ty (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (sup : SupRefs) (m : Nat)
    (h0 : E.members (sup.bPos + 2) =
      some ⟨.constructorM, 0, .pi (.const sup.bPos []) (.const sup.bPos []), none⟩)
    (h1 : E.members (sup.bPos + 3) =
      some ⟨.constructorM, 0, .pi (.const sup.bPos []) (.const sup.bPos []), none⟩)
    (hone : E.members (sup.bPos + 1) =
      some ⟨.constructorM, 0, .const sup.bPos [], none⟩) :
    HasTyT E n Γ (posTerm sup m) (.const sup.bPos []) :=
  posTermAux_ty E n Γ sup h0 h1 _ _ (const_ty E n Γ _ _ hone rfl)

/-- `bnatTerm m : BNat`. -/
def bnatTerm_ty (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (sup : SupRefs) (m : Nat)
    (h0 : E.members (sup.bPos + 2) =
      some ⟨.constructorM, 0, .pi (.const sup.bPos []) (.const sup.bPos []), none⟩)
    (h1 : E.members (sup.bPos + 3) =
      some ⟨.constructorM, 0, .pi (.const sup.bPos []) (.const sup.bPos []), none⟩)
    (hone : E.members (sup.bPos + 1) =
      some ⟨.constructorM, 0, .const sup.bPos [], none⟩)
    (hz : E.members (sup.bBNat + 1) =
      some ⟨.constructorM, 0, .const sup.bBNat [], none⟩)
    (hp : E.members (sup.bBNat + 2) =
      some ⟨.constructorM, 0, .pi (.const sup.bPos []) (.const sup.bBNat []), none⟩) :
    HasTyT E n Γ (bnatTerm sup m) (.const sup.bBNat []) := by
  unfold bnatTerm
  split
  · exact const_ty E n Γ _ _ hz rfl
  · exact .app _ _ _ _ _ (const_ty E n Γ _ _ hp rfl)
      (posTerm_ty E n Γ sup m h0 h1 hone)

/-- A `cons`-tower over a `map`ped list (`consTower nil c (l.map g)`),
    inducting on the SOURCE list `l`: `HasTyT` is data (`Type`), so a
    `map`-membership `∃` cannot be eliminated to name the elements.
    `const_ty`'s `instantiateLevels []` collapses on `const`-built
    codomains by computation; `elemTy` itself is `const`-built at every
    use site (an `SV<…>`/`BNat` family `const`), so the ctor domain
    rewrite `instantiateLevels [] elemTy = elemTy` is `rfl` there and
    `instantiateLevels_nil` closes the general case. -/
def consTowerMap_ty (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (f nilIdx cIdx : Nat) (elemTy : Expr Nat) {α : Type} (g : α → Expr Nat)
    (hnil : E.members nilIdx =
      some ⟨.constructorM, 0, .const f [], none⟩)
    (hcons : E.members cIdx =
      some ⟨.constructorM, 0,
        .pi elemTy (.pi (.const f []) (.const f [])), none⟩)
    (hg : ∀ a, HasTyT E n Γ (g a) elemTy) :
    ∀ (l : List α),
      HasTyT E n Γ (consTower nilIdx cIdx (l.map g)) (.const f [])
  | [] => const_ty E n Γ _ _ hnil rfl
  | a :: as => by
      have hc := const_ty E n Γ _ _ hcons rfl
      rw [instantiateLevels_nil] at hc
      exact .app _ _ _ _ _
        (.app _ _ _ _ _ hc (hg a))
        (consTowerMap_ty E n Γ f nilIdx cIdx elemTy g hnil hcons hg as)

/-- The premise pack shared by every `BNat`-valued builder — Pos's two
    bit ctors, `one`, and BNat's `zero`/`pos`. -/
structure BNatPrereq (E : ResolvedEnv) (sup : SupRefs) : Prop where
  h0 : E.members (sup.bPos + 2) =
    some ⟨.constructorM, 0, .pi (.const sup.bPos []) (.const sup.bPos []), none⟩
  h1 : E.members (sup.bPos + 3) =
    some ⟨.constructorM, 0, .pi (.const sup.bPos []) (.const sup.bPos []), none⟩
  hone : E.members (sup.bPos + 1) =
    some ⟨.constructorM, 0, .const sup.bPos [], none⟩
  hz : E.members (sup.bBNat + 1) =
    some ⟨.constructorM, 0, .const sup.bBNat [], none⟩
  hp : E.members (sup.bBNat + 2) =
    some ⟨.constructorM, 0, .pi (.const sup.bPos []) (.const sup.bBNat []), none⟩

/-- `strTerm`'s tower types at `SV<str>`. -/
def strTerm_ty (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (sup : SupRefs) (snil scons strFam : Nat) (s : String)
    (hb : BNatPrereq E sup)
    (hnil : E.members snil = some ⟨.constructorM, 0, .const strFam [], none⟩)
    (hcons : E.members scons = some ⟨.constructorM, 0,
      .pi (.const sup.bBNat []) (.pi (.const strFam []) (.const strFam [])), none⟩) :
    HasTyT E n Γ (strTerm sup snil scons s) (.const strFam []) :=
  consTowerMap_ty E n Γ strFam snil scons (.const sup.bBNat [])
    (fun c : Char => bnatTerm sup c.toNat) hnil hcons
    (fun c => bnatTerm_ty E n Γ sup c.toNat hb.h0 hb.h1 hb.hone hb.hz hb.hp)
    s.toList

/-- The byte tower inside `bytesTerm` types at `SV<bytes>` whenever it
    exists — the range guard decides `some`/`none`; the tower's typing
    is unconditional. -/
def bytesTerm_ty (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (sup : SupRefs) (bnil bcons bnatFam : Nat) (bs : List Int)
    (e : Expr Nat)
    (hb : BNatPrereq E sup)
    (hbytes : bytesTerm sup bnil bcons bs = some e)
    (hnil : E.members bnil = some ⟨.constructorM, 0, .const bnatFam [], none⟩)
    (hcons : E.members bcons = some ⟨.constructorM, 0,
      .pi (.const sup.bBNat []) (.pi (.const bnatFam []) (.const bnatFam [])), none⟩) :
    HasTyT E n Γ e (.const bnatFam []) := by
  unfold bytesTerm at hbytes
  split at hbytes
  · injection hbytes with hbytes; subst hbytes
    exact consTowerMap_ty E n Γ bnatFam bnil bcons (.const sup.bBNat [])
      (fun b : Int => bnatTerm sup b.toNat) hnil hcons
      (fun b => bnatTerm_ty E n Γ sup b.toNat hb.h0 hb.h1 hb.hone hb.hz hb.hp)
      bs
  · contradiction

end Rcic.G2
