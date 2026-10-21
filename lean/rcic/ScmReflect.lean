/-
RCIC 07 §14 — the reflective assertion language: closed typed syntax,
denotation, decision procedure, and the CT-012 reflection theorem
`decideProp p e pe = true ↔ denoteProp p e pe` — sound AND complete.

Owner text (`docs/rcic/07_SCM_CONTRACTS.md`, §14 "Reflective assertion
language"): the assertion language is closed and typed — variables,
canonical literals, typed constructors/projections, checked arithmetic,
finite-list quantifiers, sum tests, and q-addressed certified pure
predicate calls. It excludes unbounded recursion, IO, and untrusted host
predicates. The reflection obligation is the biconditional: the decision
procedure reports true exactly when the denotation holds.

Model shape (the cc ruling on #6392 — strict partiality):
- Terms denote into `Option (denTy T)`: checked arithmetic and typed
  variable lookup can fail, and `none` is undefinedness, not a value.
- The proposition denotation is STRICT at the proposition level:
  `denoteP p e pe : Option Prop`, and any undefined subterm makes the
  whole proposition undefined. In particular `not p` is undefined when
  `p` is undefined — atom-level `False` cannot leak through negation
  (`not (eq overflow 0)` and `not (pcall unknown)` are undefined, so the
  decider answers false; the negation teeth are in the shared corpus).
- `evalP p e pe : Option Bool` mirrors `denoteP` constructor for
  constructor; `decideProp p e pe := evalP p e pe == some true` — the
  decider answers true exactly on defined-true.

Predicate calls are q-addressed into a `PredEnv := String → Option
CertifiedPred`; `CertifiedPred` bundles a decider `dec`, a denotation
`den`, and `cert : dec a = true ↔ den a`. The certificate is a field, so
an untrusted host predicate is UNINHABITABLE — `bogus_pred_uninhabited`.
Calls consult only the environment (`pcall_uses_env` — the IO tooth),
and an unknown q or arity/argument failure is undefined, not a host
escape (`pcall_unknown_none`).

Excluded constructs, one tooth each:
  - unbounded recursion: no recursion constructor exists; the fuel
    mutant `evalPF` diverges from the strict semantics at fuel 0 on a
    true proposition (`evalPF_zero_breaks`), while `evalP` needs no fuel
    at all — the grammar is total by construction.
  - IO: `pcall_uses_env` — a predicate call's meaning is exhausted by
    `pe q`; there is no ambient state or effect channel.
  - untrusted host predicates: `bogus_pred_uninhabited` — `dec ≡ true`
    with `den ≡ False` cannot carry a certificate; `pcall_unknown_none`
    — an unknown q is undefined, not a host dispatch.

`closure_claim` stays 0.
-/
import rcic.ScmCore

namespace Rcic.Scm.Reflect
open Rcic.Scm

/-! ## `Val` equality: `beq` is lawful (needed for `eq` at type `val`) -/

mutual
/-- Reflexivity of the carrier's value `beq`. -/
def Val.beq_rfl : (a : Val) → Val.beq a a = true
  | .i _ => LawfulBEq.rfl
  | .b _ => LawfulBEq.rfl
  | .s _ => LawfulBEq.rfl
  | .y _ => LawfulBEq.rfl
  | .l xs => Val.beqList_rfl xs
  | .p a b => Bool.and_eq_true_iff.mpr ⟨Val.beq_rfl a, Val.beq_rfl b⟩
  | .j _ v => Bool.and_eq_true_iff.mpr ⟨LawfulBEq.rfl, Val.beq_rfl v⟩
  | .r xs => Val.beqList_rfl xs
/-- Reflexivity on the list payload used by `.l` and `.r`. -/
def Val.beqList_rfl : (xs : List Val) → Val.beqList xs xs = true
  | [] => rfl
  | x :: xs => Bool.and_eq_true_iff.mpr ⟨Val.beq_rfl x, Val.beqList_rfl xs⟩
end

mutual
/-- Soundness of the carrier's value `beq`. -/
def Val.eq_of_beq : (a b : Val) → Val.beq a b = true → a = b
  | .i _u, .i _w, h => congrArg Val.i (LawfulBEq.eq_of_beq h)
  | .b _u, .b _w, h => congrArg Val.b (LawfulBEq.eq_of_beq h)
  | .s _u, .s _w, h => congrArg Val.s (LawfulBEq.eq_of_beq h)
    | .y _u, .y _w, h => congrArg Val.y (LawfulBEq.eq_of_beq h)
  | .l _xs, .l _ys, h => congrArg Val.l (Val.eq_of_beqList _ _ h)
  | .p _x1 _x2, .p _y1 _y2, h =>
    (Val.eq_of_beq _ _ (Bool.and_eq_true_iff.mp h).1) ▸
      (Val.eq_of_beq _ _ (Bool.and_eq_true_iff.mp h).2) ▸ rfl
  | .j m _v, .j n _w, h =>
    (LawfulBEq.eq_of_beq (Bool.and_eq_true_iff.mp h).1 : m = n) ▸
      (Val.eq_of_beq _ _ (Bool.and_eq_true_iff.mp h).2) ▸ rfl
  | .r _xs, .r _ys, h => congrArg Val.r (Val.eq_of_beqList _ _ h)
  | .i _, .b _, h | .i _, .s _, h | .i _, .y _, h | .i _, .l _, h | .i _, .p _ _, h
    | .i _, .j _ _, h | .i _, .r _, h | .b _, .i _, h | .b _, .s _, h | .b _, .y _, h
    | .b _, .l _, h | .b _, .p _ _, h | .b _, .j _ _, h | .b _, .r _, h | .s _, .i _, h
    | .s _, .b _, h | .s _, .y _, h | .s _, .l _, h | .s _, .p _ _, h | .s _, .j _ _, h
    | .s _, .r _, h | .y _, .i _, h | .y _, .b _, h | .y _, .s _, h | .y _, .l _, h
    | .y _, .p _ _, h | .y _, .j _ _, h | .y _, .r _, h | .l _, .i _, h | .l _, .b _, h
    | .l _, .s _, h | .l _, .y _, h | .l _, .p _ _, h | .l _, .j _ _, h | .l _, .r _, h
    | .p _ _, .i _, h | .p _ _, .b _, h | .p _ _, .s _, h | .p _ _, .y _, h | .p _ _, .l _, h
    | .p _ _, .j _ _, h | .p _ _, .r _, h | .j _ _, .i _, h | .j _ _, .b _, h | .j _ _, .s _, h
    | .j _ _, .y _, h | .j _ _, .l _, h | .j _ _, .p _ _, h | .j _ _, .r _, h | .r _, .i _, h
    | .r _, .b _, h | .r _, .s _, h | .r _, .y _, h | .r _, .l _, h | .r _, .p _ _, h
    | .r _, .j _ _, h => (nomatch h)
/-- Soundness on the list payload. -/
def Val.eq_of_beqList : (xs ys : List Val) → Val.beqList xs ys = true → xs = ys
  | [], [], _ => rfl
  | _x :: _xs, _y :: _ys, h =>
    (Val.eq_of_beq _ _ (Bool.and_eq_true_iff.mp h).1) ▸
      (Val.eq_of_beqList _ _ (Bool.and_eq_true_iff.mp h).2) ▸ rfl
  | [], _ :: _, h | _ :: _, [], h => (nomatch h)
end

instance : DecidableEq Val := fun a b =>
  if h : Val.beq a b then isTrue (Val.eq_of_beq a b h)
  else isFalse (fun e => h (e ▸ Val.beq_rfl b))

/-! ## The closed typed assertion grammar (§14) -/

/-- The assertion types: machine `Int`, `Bool`, `String`, raw `Val`,
    products, sums, lists, and record schemas (Annex 26.30).
    The kernel recursor occupies `ATy.rec`, so the schema constructor
    is `rec_`. `closure_claim` stays 0. -/
inductive ATy where
  | int | bool | str | val
  | prod (a b : ATy)
  | sum (a b : ATy)
  | list (a : ATy)
  /-- Field types in schema order. The nested product is `recDen`. -/
  | rec_ (fs : List (String × ATy))
deriving Repr

/- `deriving DecidableEq` does not handle the nested `List` schema.
   `beq` is the same decision, proved by recursion on the type. -/
mutual
def ATy.beq : ATy → ATy → Bool
  | .int, .int => true
  | .bool, .bool => true
  | .str, .str => true
  | .val, .val => true
  | .prod a b, .prod c d => ATy.beq a c && ATy.beq b d
  | .sum a b, .sum c d => ATy.beq a c && ATy.beq b d
  | .list a, .list b => ATy.beq a b
  | .rec_ fs, .rec_ gs => schemaBeq fs gs
  | _, _ => false
/-- Schema equality, field by field, in order. -/
def schemaBeq : List (String × ATy) → List (String × ATy) → Bool
  | [], [] => true
  | (k, t) :: fs, (k', t') :: gs => (k == k') && ATy.beq t t' && schemaBeq fs gs
  | _, _ => false
end

mutual
theorem ATy.beq_rfl : (a : ATy) → ATy.beq a a = true
  | .int => rfl
  | .bool => rfl
  | .str => rfl
  | .val => rfl
  | .prod a b => Bool.and_eq_true_iff.mpr ⟨ATy.beq_rfl a, ATy.beq_rfl b⟩
  | .sum a b => Bool.and_eq_true_iff.mpr ⟨ATy.beq_rfl a, ATy.beq_rfl b⟩
  | .list a => ATy.beq_rfl a
  | .rec_ fs => schemaBeq_rfl fs
theorem schemaBeq_rfl : (fs : List (String × ATy)) → schemaBeq fs fs = true
  | [] => rfl
  | (_, t) :: fs =>
    Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨LawfulBEq.rfl, ATy.beq_rfl t⟩, schemaBeq_rfl fs⟩
end

mutual
theorem ATy.eq_of_beq : (a b : ATy) → ATy.beq a b = true → a = b
  | .int, .int, _ => rfl
  | .bool, .bool, _ => rfl
  | .str, .str, _ => rfl
  | .val, .val, _ => rfl
  | .prod a b, .prod c d, h => by
    have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    cases ATy.eq_of_beq a c h1
    cases ATy.eq_of_beq b d h2
    rfl
  | .sum a b, .sum c d, h => by
    have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    cases ATy.eq_of_beq a c h1
    cases ATy.eq_of_beq b d h2
    rfl
  | .list a, .list b, h => congrArg ATy.list (ATy.eq_of_beq a b h)
  | .rec_ fs, .rec_ gs, h => congrArg ATy.rec_ (schema_eq_of_beq fs gs h)
  | .int, .bool, h | .int, .str, h | .int, .val, h | .int, .prod _ _, h
  | .int, .sum _ _, h | .int, .list _, h | .int, .rec_ _, h
  | .bool, .int, h | .bool, .str, h | .bool, .val, h | .bool, .prod _ _, h
  | .bool, .sum _ _, h | .bool, .list _, h | .bool, .rec_ _, h
  | .str, .int, h | .str, .bool, h | .str, .val, h | .str, .prod _ _, h
  | .str, .sum _ _, h | .str, .list _, h | .str, .rec_ _, h
  | .val, .int, h | .val, .bool, h | .val, .str, h | .val, .prod _ _, h
  | .val, .sum _ _, h | .val, .list _, h | .val, .rec_ _, h
  | .prod _ _, .int, h | .prod _ _, .bool, h | .prod _ _, .str, h | .prod _ _, .val, h
  | .prod _ _, .sum _ _, h | .prod _ _, .list _, h | .prod _ _, .rec_ _, h
  | .sum _ _, .int, h | .sum _ _, .bool, h | .sum _ _, .str, h | .sum _ _, .val, h
  | .sum _ _, .prod _ _, h | .sum _ _, .list _, h | .sum _ _, .rec_ _, h
  | .list _, .int, h | .list _, .bool, h | .list _, .str, h | .list _, .val, h
  | .list _, .prod _ _, h | .list _, .sum _ _, h | .list _, .rec_ _, h
  | .rec_ _, .int, h | .rec_ _, .bool, h | .rec_ _, .str, h | .rec_ _, .val, h
  | .rec_ _, .prod _ _, h | .rec_ _, .sum _ _, h | .rec_ _, .list _, h => nomatch h
theorem schema_eq_of_beq : (fs gs : List (String × ATy)) → schemaBeq fs gs = true → fs = gs
  | [], [], _ => rfl
  | (k, t) :: fs, (k', t') :: gs, h => by
    have ⟨hkt, hfs⟩ := Bool.and_eq_true_iff.mp h
    have ⟨hk, ht⟩ := Bool.and_eq_true_iff.mp hkt
    have hk' : k = k' := LawfulBEq.eq_of_beq hk
    have ht' : t = t' := ATy.eq_of_beq t t' ht
    have hgs : fs = gs := schema_eq_of_beq fs gs hfs
    cases hk'; cases ht'; cases hgs
    rfl
  | [], _ :: _, h | _ :: _, [], h => nomatch h
end

instance : DecidableEq ATy := fun a b =>
  if h : ATy.beq a b then isTrue (ATy.eq_of_beq a b h)
  else isFalse (fun e => h (e ▸ ATy.beq_rfl b))

mutual
/-- Denotation of an assertion type. A record schema is the nested
    product of its field types, and the empty schema denotes `Unit`. -/
@[reducible] def denTy : ATy → Type
  | .int => Int
  | .bool => Bool
  | .str => String
  | .val => Val
  | .prod a b => denTy a × denTy b
  | .sum a b => denTy a ⊕ denTy b
  | .list a => List (denTy a)
  | .rec_ fs => recDen fs
/-- Nested product of a record schema. Empty schema denotes `Unit`. -/
@[reducible] def recDen : List (String × ATy) → Type
  | [] => Unit
  | (_, t) :: fs => denTy t × recDen fs
end

mutual
/-- Decidable equality of every denoted type. `eq` is total on
    denotation; partiality comes only from the terms. -/
def denTyDecEq : (t : ATy) → DecidableEq (denTy t)
  | .int => inferInstanceAs (DecidableEq Int)
  | .bool => inferInstanceAs (DecidableEq Bool)
  | .str => inferInstanceAs (DecidableEq String)
  | .val => inferInstanceAs (DecidableEq Val)
  | .prod a b => haveI := denTyDecEq a; haveI := denTyDecEq b
      inferInstanceAs (DecidableEq (denTy a × denTy b))
  | .sum a b => haveI := denTyDecEq a; haveI := denTyDecEq b
      inferInstanceAs (DecidableEq (denTy a ⊕ denTy b))
  | .list a => haveI := denTyDecEq a; inferInstanceAs (DecidableEq (List (denTy a)))
  | .rec_ fs => recDenDecEq fs
/-- Decidable equality of a record schema's nested product. -/
def recDenDecEq : (fs : List (String × ATy)) → DecidableEq (recDen fs)
  | [] => inferInstanceAs (DecidableEq Unit)
  | (_, t) :: fs =>
    haveI := denTyDecEq t
    haveI := recDenDecEq fs
    inferInstanceAs (DecidableEq (denTy t × recDen fs))
end

instance denTy_instDecEq (T : ATy) : DecidableEq (denTy T) := denTyDecEq T

/-- An assertion context: the types of the free variables. -/
abbrev ACtx := List ATy

/-- A runtime environment: tagged values, one per context entry. -/
abbrev AEnv := List (Sigma denTy)

/-- Typed variable lookup: the env entry must exist and carry the
    variable's declared tag. A missing entry or a tag mismatch is
    undefined — the `lookupEnv` refusal arm. -/
def lookupEnv (e : AEnv) (i : Nat) (T : ATy) : Option (denTy T) :=
  match e.get? i with
  | some ⟨T', v⟩ => if h : T' = T then some (h ▸ v) else none
  | none => none

/-! ## Annex 26.29 — key uniqueness and the raw-value injection

`record` denotes `some (.r vs)` only when its keys are duplicate-free.
Field values are injected into `Val` and projected back by tag.
`closure_claim` stays 0. -/

/-- Duplicate-free keys. A `record` with a repeated key denotes `none`. -/
def noDupKeys : List String → Bool
  | [] => true
  | k :: ks => !(ks.elem k) && noDupKeys ks

/-- `noDupKeys` decides `List.Nodup`. -/
theorem noDupKeys_iff : ∀ ks : List String, noDupKeys ks = true ↔ ks.Nodup
  | [] => Iff.intro (fun _ => List.Pairwise.nil) (fun _ => rfl)
  | k :: ks => by
    rw [noDupKeys, Bool.and_eq_true_iff, List.nodup_cons]
    constructor
    · rintro ⟨hk, hks⟩
      refine ⟨?_, (noDupKeys_iff ks).mp hks⟩
      rw [Bool.not_eq_true'] at hk
      intro hmem
      exact nomatch hk.symm.trans (List.elem_iff.mpr hmem)
    · rintro ⟨hmem, hnd⟩
      refine ⟨?_, (noDupKeys_iff ks).mpr hnd⟩
      rw [Bool.not_eq_true']
      exact Bool.eq_false_iff.mpr (fun ht => hmem (List.elem_iff.mp ht))

mutual
/-- Inject a denoted assertion value into the raw carrier. A record is
    `.r` of these injections, in schema order. -/
def packVal : (T : ATy) → denTy T → Val
  | .int, n => .i n
  | .bool, b => .b (if b then (1 : Int) else 0)
  | .str, s => .s s
  | .val, v => v
  | .prod a b, (x, y) => .p (packVal a x) (packVal b y)
  | .sum a _, .inl x => .j 0 (packVal a x)
  | .sum _ b, .inr y => .j 1 (packVal b y)
  | .list a, xs => .l (packList a xs)
  | .rec_ fs, v => .r (packRec fs v)
/-- List payload of `packVal` at `.list`. -/
def packList (a : ATy) : List (denTy a) → List Val
  | [] => []
  | x :: xs => packVal a x :: packList a xs
/-- Record payload of `packVal` at `.rec_`, in schema order. -/
def packRec : (fs : List (String × ATy)) → recDen fs → List Val
  | [], () => []
  | (_, t) :: fs, (x, rest) => packVal t x :: packRec fs rest
end

mutual
/-- Project a raw value at an assertion type. A tag mismatch is `none`
    — the same refusal as `lookupEnv`. -/
def unpackVal : (T : ATy) → Val → Option (denTy T)
  | .int, .i n => some n
  | .int, _ => none
  | .bool, .b n =>
    if n = 0 then some false else if n = 1 then some true else none
  | .bool, _ => none
  | .str, .s s => some s
  | .str, _ => none
  | .val, v => some v
  | .prod a b, .p x y =>
    match unpackVal a x, unpackVal b y with
    | some x', some y' => some (x', y')
    | _, _ => none
  | .prod _ _, _ => none
  | .sum a b, .j i v =>
    if i = 0 then (unpackVal a v).map Sum.inl
    else if i = 1 then (unpackVal b v).map Sum.inr
    else none
  | .sum _ _, _ => none
  | .list a, .l xs => unpackList a xs
  | .list _, _ => none
  | .rec_ fs, .r xs => unpackRec fs xs
  | .rec_ _, _ => none
/-- List payload of `unpackVal` at `.list`. One bad element is `none`. -/
def unpackList (a : ATy) : List Val → Option (List (denTy a))
  | [] => some []
  | v :: vs =>
    match unpackVal a v, unpackList a vs with
    | some x, some xs => some (x :: xs)
    | _, _ => none
/-- Record payload of `unpackVal` at `.rec_`. A length mismatch or one
    bad field is `none`. -/
def unpackRec : (fs : List (String × ATy)) → List Val → Option (recDen fs)
  | [], [] => some ()
  | [], _ :: _ => none
  | _ :: _, [] => none
  | (_, t) :: fs, v :: vs =>
    match unpackVal t v, unpackRec fs vs with
    | some x, some rest => some (x, rest)
    | _, _ => none
end

/-- `AssertTerm Γ T` — the closed typed term grammar: variables,
    canonical literals, typed constructors/projections, checked
    arithmetic, finite lists, `snoc`, `record`, and typed `field`.
    No recursion, no IO, no host calls. Annex 26.29.
    `Γ` is a parameter so `record`'s field list may nest `AssertTerm Γ`. -/
inductive AssertTerm (Γ : ACtx) : ATy → Type where
  | litI : Int → AssertTerm Γ .int
  | litB : Bool → AssertTerm Γ .bool
  | litS : String → AssertTerm Γ .str
  | litV : Val → AssertTerm Γ .val
  | var : (i : Nat) → Γ.get? i = some T → AssertTerm Γ T
  | pair : AssertTerm Γ a → AssertTerm Γ b → AssertTerm Γ (.prod a b)
  | fst : AssertTerm Γ (.prod a b) → AssertTerm Γ a
  | snd : AssertTerm Γ (.prod a b) → AssertTerm Γ b
  | inl : AssertTerm Γ a → AssertTerm Γ (.sum a b)
  | inr : AssertTerm Γ b → AssertTerm Γ (.sum a b)
  | add : AssertTerm Γ .int → AssertTerm Γ .int → AssertTerm Γ .int
  | sub : AssertTerm Γ .int → AssertTerm Γ .int → AssertTerm Γ .int
  | mul : AssertTerm Γ .int → AssertTerm Γ .int → AssertTerm Γ .int
  | nil : AssertTerm Γ (.list a)
  | cons : AssertTerm Γ a → AssertTerm Γ (.list a) → AssertTerm Γ (.list a)
  /-- `xs ++ [x]`. Either side `none` makes the term `none`. -/
  | snoc : AssertTerm Γ (.list a) → AssertTerm Γ a → AssertTerm Γ (.list a)
  /-- Keys and fields. Denotes `some (.r vs)` when the keys are
      duplicate-free, the lengths match, and every field denotes. -/
  | record : List String → List (Sigma (AssertTerm Γ)) → AssertTerm Γ .val
  /-- The `i`-th slot of a record, at tag `T`. Miss, non-record, and
      mistag are `none`. -/
  | field : AssertTerm Γ .val → (i : Nat) → AssertTerm Γ T

/- `denoteTerm` — the term denotation, `Option`-valued: checked
    arithmetic refuses out-of-i64 results, and typed lookup refuses
    missing or mistagged entries. `snoc`, `record`, and `field`
    propagate `none`. `none` is undefinedness. -/
mutual
/-- Term denotation. `none` is undefinedness. -/
def denoteTerm : AssertTerm Γ T → AEnv → Option (denTy T)
  | .litI n, _ => some n
  | .litB b, _ => some b
  | .litS s, _ => some s
  | .litV v, _ => some v
  | .var i _, e => lookupEnv e i _
  | .pair t u, e =>
    match denoteTerm t e with
    | some x => (denoteTerm u e).map (x, ·)
    | none => none
  | .fst t, e => (denoteTerm t e).map Prod.fst
  | .snd t, e => (denoteTerm t e).map Prod.snd
  | .inl t, e => (denoteTerm t e).map Sum.inl
  | .inr t, e => (denoteTerm t e).map Sum.inr
  | .add t u, e =>
    match denoteTerm t e, denoteTerm u e with
    | some x, some y => if inI64 ((x : Int) + (y : Int)) then some (x + y) else none
    | _, _ => none
  | .sub t u, e =>
    match denoteTerm t e, denoteTerm u e with
    | some x, some y => if inI64 ((x : Int) - (y : Int)) then some (x - y) else none
    | _, _ => none
  | .mul t u, e =>
    match denoteTerm t e, denoteTerm u e with
    | some x, some y => if inI64 ((x : Int) * (y : Int)) then some (x * y) else none
    | _, _ => none
  | .nil, _ => some []
  | .cons t ts, e =>
    match denoteTerm t e with
    | some x => (denoteTerm ts e).map (x :: ·)
    | none => none
  | .snoc ts t, e =>
    match denoteTerm ts e, denoteTerm t e with
    | some xs, some x => some (xs ++ [x])
    | _, _ => none
  | .record keys fields, e =>
    if keys.length == fields.length && noDupKeys keys then
      (denoteFields fields e).map Val.r
    else none
  | .field t i, e =>
    match denoteTerm t e with
    | some (.r xs) =>
      match xs.get? i with
      | some v => unpackVal T v
      | none => none
    | _ => none
/-- Field denotation for `record`. One undefined field is `none`. -/
def denoteFields {Γ : ACtx} : List (Sigma (AssertTerm Γ)) → AEnv → Option (List Val)
  | [], _ => some []
  | ⟨T, t⟩ :: rest, e =>
    match denoteTerm t e with
    | none => none
    | some v => (denoteFields rest e).map (packVal T v :: ·)
end

/-- `AssertProp Γ` — the closed proposition grammar: comparisons,
    connectives, finite-list quantifiers, sum tests, certified
    predicate calls. -/
inductive AssertProp : ACtx → Type where
  | eq : AssertTerm Γ T → AssertTerm Γ T → AssertProp Γ
  | lt : AssertTerm Γ .int → AssertTerm Γ .int → AssertProp Γ
  | le : AssertTerm Γ .int → AssertTerm Γ .int → AssertProp Γ
  | and : AssertProp Γ → AssertProp Γ → AssertProp Γ
  | or : AssertProp Γ → AssertProp Γ → AssertProp Γ
  | impl : AssertProp Γ → AssertProp Γ → AssertProp Γ
  | not : AssertProp Γ → AssertProp Γ
  | allIn : AssertTerm Γ (.list a) → AssertProp (a :: Γ) → AssertProp Γ
  | exIn : AssertTerm Γ (.list a) → AssertProp (a :: Γ) → AssertProp Γ
  | isInl : AssertTerm Γ (.sum a b) → AssertProp Γ
  | isInr : AssertTerm Γ (.sum a b) → AssertProp Γ
  | pcall : (q : String) → List (Sigma (AssertTerm Γ)) → AssertProp Γ

/-- A certified pure predicate: a decider, a denotation, and the
    certificate that they agree — the only admissible call target. The
    certificate is a field, so an untrusted predicate is uninhabitable. -/
structure CertifiedPred where
  nargs : Nat
  dec : List (Sigma denTy) → Bool
  den : List (Sigma denTy) → Prop
  cert : ∀ a, dec a = true ↔ den a

/-- The q-addressed certified predicate environment (the semantic
    reading of §25.11's `rcic-pred-env` data lane, #6371). -/
abbrev PredEnv := String → Option CertifiedPred

/-- Argument evaluation for predicate calls: every argument term must
    denote. -/
def denoteArgs : List (Sigma (AssertTerm Γ)) → AEnv → Option (List (Sigma denTy))
  | [], _ => some []
  | ⟨T, t⟩ :: rest, e =>
    match denoteTerm t e with
    | some v => (denoteArgs rest e).map (⟨T, v⟩ :: ·)
    | none => none

/-- `denoteP` — the strict proposition denotation. Any undefined
    subterm makes the whole proposition `none`. -/
def denoteP : AssertProp Γ → AEnv → PredEnv → Option Prop
  | .eq t u, e, _ =>
    match denoteTerm t e with
    | some x => (denoteTerm u e).map (x = ·)
    | none => none
  | .lt t u, e, _ =>
    match denoteTerm t e with
    | some x => (denoteTerm u e).map (x < ·)
    | none => none
  | .le t u, e, _ =>
    match denoteTerm t e with
    | some x => (denoteTerm u e).map (x ≤ ·)
    | none => none
  | .and p q, e, pe =>
    match denoteP p e pe with
    | some P => (denoteP q e pe).map (P ∧ ·)
    | none => none
  | .or p q, e, pe =>
    match denoteP p e pe with
    | some P => (denoteP q e pe).map (P ∨ ·)
    | none => none
  | .impl p q, e, pe =>
    match denoteP p e pe with
    | some P => (denoteP q e pe).map (P → ·)
    | none => none
  | .not p, e, pe => (denoteP p e pe).map Not
  | .allIn t p, e, pe =>
    match denoteTerm t e with
    | none => none
    | some xs =>
      if xs.all (fun x => (denoteP p (⟨_, x⟩ :: e) pe).isSome) then
        some (∀ x ∈ xs, ∃ Q, denoteP p (⟨_, x⟩ :: e) pe = some Q ∧ Q)
      else none
  | .exIn t p, e, pe =>
    match denoteTerm t e with
    | none => none
    | some xs =>
      if xs.all (fun x => (denoteP p (⟨_, x⟩ :: e) pe).isSome) then
        some (∃ x ∈ xs, ∃ Q, denoteP p (⟨_, x⟩ :: e) pe = some Q ∧ Q)
      else none
  | .isInl t, e, _ =>
    (denoteTerm t e).map fun v => ∃ x, v = Sum.inl x
  | .isInr t, e, _ =>
    (denoteTerm t e).map fun v => ∃ x, v = Sum.inr x
  | .pcall q args, e, pe =>
    match pe q with
    | none => none
    | some cp =>
      match denoteArgs args e with
      | none => none
      | some argv => if argv.length = cp.nargs then some (cp.den argv) else none

/-- `denoteProp p e pe` — the §14 denotation as a `Prop`: `p` denotes
    some proposition and it holds. -/
def denoteProp {Γ} (p : AssertProp Γ) (e : AEnv) (pe : PredEnv) : Prop :=
  ∃ P, denoteP p e pe = some P ∧ P

/-! ## The decision procedure -/

/-- Strict universal quantification over a finite list of `Option Bool`
    body answers: `none` anywhere makes the whole `none`; every element
    must answer `some true` for `some true`. -/
def evalAll (f : α → Option Bool) : List α → Option Bool
  | [] => some true
  | x :: xs =>
    match f x with
    | none => none
    | some b =>
      match evalAll f xs with
      | none => none
      | some r => some (b && r)

/-- Strict existential quantification, dual to `evalAll`. -/
def evalAny (f : α → Option Bool) : List α → Option Bool
  | [] => some false
  | x :: xs =>
    match f x with
    | none => none
    | some b =>
      match evalAny f xs with
      | none => none
      | some r => some (b || r)

/-- `evalP` — the executable strict evaluation, `Option Bool`. -/
def evalP : AssertProp Γ → AEnv → PredEnv → Option Bool
  | .eq t u, e, _ =>
    (denoteTerm t e).bind fun x => (denoteTerm u e).bind fun y => some (decide (x = y))
  | .lt t u, e, _ =>
    (denoteTerm t e).bind fun x => (denoteTerm u e).bind fun y => some (decide (x < y))
  | .le t u, e, _ =>
    (denoteTerm t e).bind fun x => (denoteTerm u e).bind fun y => some (decide (x ≤ y))
  | .and p q, e, pe =>
    (evalP p e pe).bind fun a => (evalP q e pe).bind fun b => some (a && b)
  | .or p q, e, pe =>
    (evalP p e pe).bind fun a => (evalP q e pe).bind fun b => some (a || b)
  | .impl p q, e, pe =>
    (evalP p e pe).bind fun a => (evalP q e pe).bind fun b => some (!a || b)
  | .not p, e, pe => (evalP p e pe).map (!·)
  | .allIn t p, e, pe =>
    (denoteTerm t e).bind fun xs => evalAll (fun x => evalP p (⟨_, x⟩ :: e) pe) xs
  | .exIn t p, e, pe =>
    (denoteTerm t e).bind fun xs => evalAny (fun x => evalP p (⟨_, x⟩ :: e) pe) xs
  | .isInl t, e, _ =>
    (denoteTerm t e).bind fun v => match v with | .inl _ => some true | .inr _ => some false
  | .isInr t, e, _ =>
    (denoteTerm t e).bind fun v => match v with | .inr _ => some true | .inl _ => some false
  | .pcall q args, e, pe =>
    (pe q).bind fun cp => (denoteArgs args e).bind fun argv =>
      if argv.length = cp.nargs then some (cp.dec argv) else none

/-- `decideProp p e pe` — the §14 decision procedure: the decider answers
    true exactly on defined-true. -/
def decideProp {Γ} (p : AssertProp Γ) (e : AEnv) (pe : PredEnv) : Bool :=
  evalP p e pe == some true

/-! ## Strict-fold lemmas -/

/-- `evalAll` answers `some true` iff every element answers `some true`. -/
theorem evalAll_true_iff {f : α → Option Bool} {xs : List α} :
    evalAll f xs = some true ↔ ∀ x ∈ xs, f x = some true := by
  induction xs with
  | nil => simp [evalAll]
  | cons x xs ih =>
    unfold evalAll
    constructor
    · intro h
      cases hx : f x <;> rw [hx] at h
      · exact absurd h (by simp)
      · rename_i b
        cases ht : evalAll f xs <;> rw [ht] at h
        · exact absurd h (by simp)
        · rename_i r
          rw [Option.some.injEq] at h
          obtain ⟨hb, hr⟩ := Bool.and_eq_true_iff.mp h
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hm
          · exact hb ▸ hx
          · exact ih.mp (hr ▸ ht) y hm
    · intro h
      have hx : f x = some true := h x (List.mem_cons_self _ _)
      have hrest : evalAll f xs = some true :=
        ih.mpr fun y hy => h y (List.mem_cons_of_mem _ hy)
      simp [hx, hrest]

/-- `evalAll` answers `none` iff some element answers `none`. -/
theorem evalAll_none_iff {f : α → Option Bool} {xs : List α} :
    evalAll f xs = none ↔ ∃ x ∈ xs, f x = none := by
  induction xs with
  | nil => simp [evalAll]
  | cons x xs ih =>
    unfold evalAll
    constructor
    · intro h
      cases hx : f x <;> rw [hx] at h
      · exact ⟨x, List.mem_cons_self _ _, hx⟩
      · cases ht : evalAll f xs <;> rw [ht] at h
        · obtain ⟨y, hy, hfy⟩ := ih.mp ht
          exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩
        · exact absurd h (by simp)
    · rintro ⟨y, hy, hfy⟩
      rcases List.mem_cons.mp hy with rfl | hm
      · rw [hfy]
      · cases hx : f x
        · rfl
        · rw [ih.mpr ⟨y, hm, hfy⟩]

/-- `evalAll` answering `some _` means every element was defined. -/
theorem evalAll_defined {f : α → Option Bool} {xs : List α} {b : Bool}
    (h : evalAll f xs = some b) : ∀ x ∈ xs, ∃ c, f x = some c := by
  intro x hx
  cases hx2 : f x
  · have : evalAll f xs = none := evalAll_none_iff.mpr ⟨x, hx, hx2⟩
    simp_all
  · exact ⟨_, rfl⟩

/-- `evalAny` answers `none` iff some element answers `none`. -/
theorem evalAny_none_iff {f : α → Option Bool} {xs : List α} :
    evalAny f xs = none ↔ ∃ x ∈ xs, f x = none := by
  induction xs with
  | nil => simp [evalAny]
  | cons x xs ih =>
    unfold evalAny
    constructor
    · intro h
      cases hx : f x <;> rw [hx] at h
      · exact ⟨x, List.mem_cons_self _ _, hx⟩
      · cases ht : evalAny f xs <;> rw [ht] at h
        · obtain ⟨y, hy, hfy⟩ := ih.mp ht
          exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩
        · exact absurd h (by simp)
    · rintro ⟨y, hy, hfy⟩
      rcases List.mem_cons.mp hy with rfl | hm
      · rw [hfy]
      · cases hx : f x
        · rfl
        · rw [ih.mpr ⟨y, hm, hfy⟩]

/-- `evalAny` answering `some _` means every element was defined. -/
theorem evalAny_defined {f : α → Option Bool} {xs : List α} {b : Bool}
    (h : evalAny f xs = some b) : ∀ x ∈ xs, ∃ c, f x = some c := by
  intro x hx
  cases hx2 : f x
  · have : evalAny f xs = none := evalAny_none_iff.mpr ⟨x, hx, hx2⟩
    simp_all
  · exact ⟨_, rfl⟩

/-- All-defined lists make `evalAny` defined. -/
theorem evalAny_some_of_defined {f : α → Option Bool} {xs : List α}
    (hd : ∀ x ∈ xs, ∃ b, f x = some b) : ∃ r, evalAny f xs = some r := by
  induction xs with
  | nil => exact ⟨false, rfl⟩
  | cons x xs ih =>
    obtain ⟨b, hb⟩ := hd x (List.mem_cons_self _ _)
    obtain ⟨r, hr⟩ := ih fun y hy => hd y (List.mem_cons_of_mem _ hy)
    exact ⟨b || r, by unfold evalAny; rw [hb, hr]⟩

/-- `evalAny` answers `some true` iff every element is defined and at
    least one answers `some true`. -/
theorem evalAny_true_iff {f : α → Option Bool} {xs : List α} :
    evalAny f xs = some true ↔
      (∀ x ∈ xs, ∃ b, f x = some b) ∧ ∃ x ∈ xs, f x = some true := by
  induction xs with
  | nil => simp [evalAny]
  | cons x xs ih =>
    unfold evalAny
    constructor
    · intro h
      cases hx : f x <;> rw [hx] at h
      · exact absurd h (by simp)
      · rename_i b
        cases ht : evalAny f xs <;> rw [ht] at h
        · exact absurd h (by simp)
        · rename_i r
          rw [Option.some.injEq] at h
          rcases Bool.or_eq_true_iff.mp h with hb | hr
          · subst hb
            refine ⟨fun y hy =>
                (List.mem_cons.mp hy).elim (fun e => ⟨true, e ▸ hx⟩)
                  (fun hm => evalAny_defined ht y hm), ?_⟩
            exact ⟨x, List.mem_cons_self _ _, hx⟩
          · obtain ⟨hd, he⟩ := ih.mp (hr ▸ ht)
            obtain ⟨z, hz, hfz⟩ := he
            exact ⟨fun y hy =>
                (List.mem_cons.mp hy).elim (fun e => ⟨b, e ▸ hx⟩) (fun hm => hd y hm),
              ⟨z, List.mem_cons_of_mem _ hz, hfz⟩⟩
    · rintro ⟨hd, y, hy, hfy⟩
      rcases List.mem_cons.mp hy with rfl | hm
      · rw [hfy]
        obtain ⟨r, hr⟩ := evalAny_some_of_defined
          fun y' hy' => hd y' (List.mem_cons_of_mem _ hy')
        rw [hr]; rfl
      · obtain ⟨b, hb⟩ := hd x (List.mem_cons_self _ _)
        rw [hb, ih.mpr ⟨fun y' hy' => hd y' (List.mem_cons_of_mem _ hy'), ⟨y, hm, hfy⟩⟩]
        cases b <;> rfl

/-- `xs.all` failing means some element's guard is `false`. -/
theorem all_ne_true {g : α → Bool} {xs : List α} (h : xs.all g ≠ true) :
    ∃ x ∈ xs, g x = false := by
  induction xs with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
    rw [List.all_cons] at h
    cases hgx : g x
    · exact ⟨x, List.mem_cons_self _ _, hgx⟩
    · rw [hgx, Bool.true_and] at h
      obtain ⟨y, hy, hyf⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, hyf⟩

/-- A `false` list-all carries its witness — constructive replacement
    for `List.all_eq_false` (which proves through `Classical.choice`). -/
theorem all_false_witness {g : α → Bool} {xs : List α} (h : xs.all g = false) :
    ∃ x ∈ xs, g x = false := by
  induction xs with
  | nil => simp [List.all] at h
  | cons x xs ih =>
    rw [List.all_cons] at h
    cases hx : g x
    · exact ⟨x, List.mem_cons_self _ _, hx⟩
    · rw [hx] at h
      obtain ⟨y, hy, hfy⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-! ## The reflection theorem (CT-012) -/

/-- The executable and denotational evaluations agree exactly:
    `some true` iff the denotation holds, `none` iff the denotation is
    undefined. Soundness and completeness together. -/
theorem evalP_correct : ∀ {Γ} (p : AssertProp Γ) (e : AEnv) (pe : PredEnv),
    (evalP p e pe = some true ↔ ∃ P, denoteP p e pe = some P ∧ P) ∧
    (evalP p e pe = none ↔ denoteP p e pe = none) := by
  intro Γ p e pe
  induction p generalizing e pe with
  | eq t u =>
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · exact absurd h (by simp)
        · cases hu : denoteTerm u e <;> simp only [hu, Option.none_bind, Option.some_bind] at h
          · exact absurd h (by simp)
          · rename_i x y
            rw [Option.some.injEq] at h
            exact ⟨x = y, by simp only [denoteP, ht, hu, Option.map_some'], of_decide_eq_true h⟩
      · rintro ⟨P, hP, hhold⟩
        cases ht : denoteTerm t e <;> simp only [denoteP, ht] at hP
        · exact absurd hP (by simp)
        · cases hu : denoteTerm u e <;> simp only [hu, Option.map_none', Option.map_some'] at hP
          · exact absurd hP (by simp)
          · cases hP
            simp only [evalP, ht, hu, Option.some_bind]
            exact congrArg _ (decide_eq_true hhold)
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · simp only [denoteP, ht]
        · cases hu : denoteTerm u e <;> simp only [hu, Option.none_bind, Option.some_bind] at h
          · simp only [denoteP, ht, hu, Option.map_none']
          · exact absurd h (by simp)
      · intro h
        cases ht : denoteTerm t e <;> simp only [denoteP, ht] at h
        · simp only [evalP, ht, Option.none_bind]
        · cases hu : denoteTerm u e <;> simp only [hu, Option.map_none', Option.map_some'] at h
          · simp only [evalP, ht, hu, Option.some_bind, Option.none_bind]
          · exact absurd h (by simp)
  | lt t u =>
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · exact absurd h (by simp)
        · cases hu : denoteTerm u e <;> simp only [hu, Option.none_bind, Option.some_bind] at h
          · exact absurd h (by simp)
          · rename_i x y
            rw [Option.some.injEq] at h
            exact ⟨(x : Int) < y, by simp only [denoteP, ht, hu, Option.map_some'], of_decide_eq_true h⟩
      · rintro ⟨P, hP, hhold⟩
        cases ht : denoteTerm t e <;> simp only [denoteP, ht] at hP
        · exact absurd hP (by simp)
        · cases hu : denoteTerm u e <;> simp only [hu, Option.map_none', Option.map_some'] at hP
          · exact absurd hP (by simp)
          · cases hP
            simp only [evalP, ht, hu, Option.some_bind]
            exact congrArg _ (decide_eq_true hhold)
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · simp only [denoteP, ht]
        · cases hu : denoteTerm u e <;> simp only [hu, Option.none_bind, Option.some_bind] at h
          · simp only [denoteP, ht, hu, Option.map_none']
          · exact absurd h (by simp)
      · intro h
        cases ht : denoteTerm t e <;> simp only [denoteP, ht] at h
        · simp only [evalP, ht, Option.none_bind]
        · cases hu : denoteTerm u e <;> simp only [hu, Option.map_none', Option.map_some'] at h
          · simp only [evalP, ht, hu, Option.some_bind, Option.none_bind]
          · exact absurd h (by simp)
  | le t u =>
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · exact absurd h (by simp)
        · cases hu : denoteTerm u e <;> simp only [hu, Option.none_bind, Option.some_bind] at h
          · exact absurd h (by simp)
          · rename_i x y
            rw [Option.some.injEq] at h
            exact ⟨(x : Int) ≤ y, by simp only [denoteP, ht, hu, Option.map_some'], of_decide_eq_true h⟩
      · rintro ⟨P, hP, hhold⟩
        cases ht : denoteTerm t e <;> simp only [denoteP, ht] at hP
        · exact absurd hP (by simp)
        · cases hu : denoteTerm u e <;> simp only [hu, Option.map_none', Option.map_some'] at hP
          · exact absurd hP (by simp)
          · cases hP
            simp only [evalP, ht, hu, Option.some_bind]
            exact congrArg _ (decide_eq_true hhold)
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · simp only [denoteP, ht]
        · cases hu : denoteTerm u e <;> simp only [hu, Option.none_bind, Option.some_bind] at h
          · simp only [denoteP, ht, hu, Option.map_none']
          · exact absurd h (by simp)
      · intro h
        cases ht : denoteTerm t e <;> simp only [denoteP, ht] at h
        · simp only [evalP, ht, Option.none_bind]
        · cases hu : denoteTerm u e <;> simp only [hu, Option.map_none', Option.map_some'] at h
          · simp only [evalP, ht, hu, Option.some_bind, Option.none_bind]
          · exact absurd h (by simp)
  | and p q ihp ihq =>
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        simp only [evalP] at h
        cases hp : evalP p e pe <;> simp only [hp, Option.none_bind, Option.some_bind] at h
        · exact absurd h (by simp)
        · cases hq : evalP q e pe <;> simp only [hq, Option.none_bind, Option.some_bind] at h
          · exact absurd h (by simp)
          · rename_i a b
            rw [Option.some.injEq] at h
            obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
            subst ha hb
            obtain ⟨P, hP, hPh⟩ := (ihp e pe).1.mp hp
            obtain ⟨Q, hQ, hQh⟩ := (ihq e pe).1.mp hq
            exact ⟨P ∧ Q, by simp only [denoteP, hP, hQ, Option.map_some'], ⟨hPh, hQh⟩⟩
      · rintro ⟨P, hP, hhold⟩
        cases hp : denoteP p e pe <;> simp only [denoteP, hp] at hP
        · exact absurd hP (by simp)
        · cases hq : denoteP q e pe <;> simp only [hq, Option.map_some', Option.map_none'] at hP
          · exact absurd hP (by simp)
          · rename_i P' Q'
            cases hP
            obtain ⟨hP'h, hQ'h⟩ := hhold
            simp only [evalP, (ihp e pe).1.mpr ⟨P', hp, hP'h⟩,
              (ihq e pe).1.mpr ⟨Q', hq, hQ'h⟩, Option.some_bind]
            rfl
    · constructor
      · intro h
        simp only [evalP] at h
        cases hp : evalP p e pe <;> simp only [hp, Option.none_bind, Option.some_bind] at h
        · simp only [denoteP, (ihp e pe).2.mp hp]
        · cases hq : evalP q e pe <;> simp only [hq, Option.none_bind, Option.some_bind] at h
          · obtain ⟨P', hP'⟩ : ∃ P', denoteP p e pe = some P' := by
              cases hd : denoteP p e pe
              · rw [(ihp e pe).2.mpr hd] at hp; simp at hp
              · exact ⟨_, rfl⟩
            simp only [denoteP, hP', (ihq e pe).2.mp hq, Option.map_none']
          · exact absurd h (by simp)
      · intro h
        cases hp : denoteP p e pe <;> simp only [denoteP, hp] at h
        · simp only [evalP, (ihp e pe).2.mpr hp, Option.none_bind]
        · cases hq : denoteP q e pe <;> simp only [hq, Option.map_some', Option.map_none'] at h
          · obtain ⟨a, ha⟩ : ∃ a, evalP p e pe = some a := by
              cases hd : evalP p e pe
              · rw [(ihp e pe).2.mp hd] at hp; simp at hp
              · exact ⟨_, rfl⟩
            simp only [evalP, ha, Option.some_bind, (ihq e pe).2.mpr hq, Option.none_bind]
          · exact absurd h (by simp)
  | or p q ihp ihq =>
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        simp only [evalP] at h
        cases hp : evalP p e pe <;> simp only [hp, Option.none_bind, Option.some_bind] at h
        · exact absurd h (by simp)
        · cases hq : evalP q e pe <;> simp only [hq, Option.none_bind, Option.some_bind] at h
          · exact absurd h (by simp)
          · rename_i a b
            rw [Option.some.injEq] at h
            rcases Bool.or_eq_true_iff.mp h with ha | hb
            · subst ha
              obtain ⟨P, hP, hPh⟩ := (ihp e pe).1.mp hp
              obtain ⟨Q, hQ⟩ : ∃ Q, denoteP q e pe = some Q := by
                cases hd : denoteP q e pe
                · rw [(ihq e pe).2.mpr hd] at hq; simp at hq
                · exact ⟨_, rfl⟩
              exact ⟨P ∨ Q, by simp only [denoteP, hP, hQ, Option.map_some'], .inl hPh⟩
            · subst hb
              obtain ⟨Q, hQ, hQh⟩ := (ihq e pe).1.mp hq
              obtain ⟨P, hP⟩ : ∃ P, denoteP p e pe = some P := by
                cases hd : denoteP p e pe
                · rw [(ihp e pe).2.mpr hd] at hp; simp at hp
                · exact ⟨_, rfl⟩
              exact ⟨P ∨ Q, by simp only [denoteP, hP, hQ, Option.map_some'], .inr hQh⟩
      · rintro ⟨P, hP, hhold⟩
        cases hp : denoteP p e pe <;> simp only [denoteP, hp] at hP
        · exact absurd hP (by simp)
        · cases hq : denoteP q e pe <;> simp only [hq, Option.map_some', Option.map_none'] at hP
          · exact absurd hP (by simp)
          · rename_i P' Q'
            cases hP
            rcases hhold with hP'h | hQ'h
            · have hev := (ihp e pe).1.mpr ⟨P', hp, hP'h⟩
              obtain ⟨b, hb⟩ : ∃ b, evalP q e pe = some b := by
                cases hd : evalP q e pe
                · rw [(ihq e pe).2.mp hd] at hq; simp at hq
                · exact ⟨_, rfl⟩
              simp only [evalP, hev, Option.some_bind, hb]
              rfl
            · have hev := (ihq e pe).1.mpr ⟨Q', hq, hQ'h⟩
              obtain ⟨a, ha⟩ : ∃ a, evalP p e pe = some a := by
                cases hd : evalP p e pe
                · rw [(ihp e pe).2.mp hd] at hp; simp at hp
                · exact ⟨_, rfl⟩
              simp only [evalP, ha, Option.some_bind, hev]
              cases a
              · rfl
              · rfl
    · constructor
      · intro h
        simp only [evalP] at h
        cases hp : evalP p e pe <;> simp only [hp, Option.none_bind, Option.some_bind] at h
        · simp only [denoteP, (ihp e pe).2.mp hp]
        · cases hq : evalP q e pe <;> simp only [hq, Option.none_bind, Option.some_bind] at h
          · obtain ⟨P', hP'⟩ : ∃ P', denoteP p e pe = some P' := by
              cases hd : denoteP p e pe
              · rw [(ihp e pe).2.mpr hd] at hp; simp at hp
              · exact ⟨_, rfl⟩
            simp only [denoteP, hP', (ihq e pe).2.mp hq, Option.map_none']
          · exact absurd h (by simp)
      · intro h
        cases hp : denoteP p e pe <;> simp only [denoteP, hp] at h
        · simp only [evalP, (ihp e pe).2.mpr hp, Option.none_bind]
        · cases hq : denoteP q e pe <;> simp only [hq, Option.map_some', Option.map_none'] at h
          · obtain ⟨a, ha⟩ : ∃ a, evalP p e pe = some a := by
              cases hd : evalP p e pe
              · rw [(ihp e pe).2.mp hd] at hp; simp at hp
              · exact ⟨_, rfl⟩
            simp only [evalP, ha, Option.some_bind, (ihq e pe).2.mpr hq, Option.none_bind]
          · exact absurd h (by simp)
  | impl p q ihp ihq =>
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        simp only [evalP] at h
        cases hp : evalP p e pe <;> simp only [hp, Option.none_bind, Option.some_bind] at h
        · exact absurd h (by simp)
        · cases hq : evalP q e pe <;> simp only [hq, Option.none_bind, Option.some_bind] at h
          · exact absurd h (by simp)
          · rename_i a b
            rw [Option.some.injEq] at h
            obtain ⟨P, hP⟩ : ∃ P, denoteP p e pe = some P := by
              cases hd : denoteP p e pe
              · rw [(ihp e pe).2.mpr hd] at hp; simp at hp
              · exact ⟨_, rfl⟩
            obtain ⟨Q, hQ⟩ : ∃ Q, denoteP q e pe = some Q := by
              cases hd : denoteP q e pe
              · rw [(ihq e pe).2.mpr hd] at hq; simp at hq
              · exact ⟨_, rfl⟩
            refine ⟨P → Q, ?_, ?_⟩
            · simp only [denoteP, hP, hQ, Option.map_some']
            · intro hph
              have hev := (ihp e pe).1.mpr ⟨P, hP, hph⟩
              rw [hp] at hev
              cases hev
              rcases Bool.or_eq_true_iff.mp h with hb | hb
              · exact absurd hb (by simp)
              · obtain ⟨Q', hQ', hQ'h⟩ := (ihq e pe).1.mp (hb ▸ hq)
                rw [hQ'] at hQ
                cases hQ
                exact hQ'h
      · rintro ⟨P, hP, hhold⟩
        cases hp : denoteP p e pe <;> simp only [denoteP, hp] at hP
        · exact absurd hP (by simp)
        · cases hq : denoteP q e pe <;> simp only [hq, Option.map_some', Option.map_none'] at hP
          · exact absurd hP (by simp)
          · rename_i P' Q'
            cases hP
            obtain ⟨a, ha⟩ : ∃ a, evalP p e pe = some a := by
              cases hd : evalP p e pe
              · rw [(ihp e pe).2.mp hd] at hp; simp at hp
              · exact ⟨_, rfl⟩
            obtain ⟨b, hb⟩ : ∃ b, evalP q e pe = some b := by
              cases hd : evalP q e pe
              · rw [(ihq e pe).2.mp hd] at hq; simp at hq
              · exact ⟨_, rfl⟩
            simp only [evalP, ha, Option.some_bind, hb]
            cases a <;> cases b
            · rfl
            · rfl
            · exfalso
              obtain ⟨P'', hP'', hP''h⟩ := (ihp e pe).1.mp ha
              rw [hP''] at hp; cases hp
              have hq' := (ihq e pe).1.mpr ⟨Q', hq, hhold hP''h⟩
              rw [hb] at hq'
              exact absurd hq' (by simp)
            · rfl
    · constructor
      · intro h
        simp only [evalP] at h
        cases hp : evalP p e pe <;> simp only [hp, Option.none_bind, Option.some_bind] at h
        · simp only [denoteP, (ihp e pe).2.mp hp]
        · cases hq : evalP q e pe <;> simp only [hq, Option.none_bind, Option.some_bind] at h
          · obtain ⟨P', hP'⟩ : ∃ P', denoteP p e pe = some P' := by
              cases hd : denoteP p e pe
              · rw [(ihp e pe).2.mpr hd] at hp; simp at hp
              · exact ⟨_, rfl⟩
            simp only [denoteP, hP', (ihq e pe).2.mp hq, Option.map_none']
          · exact absurd h (by simp)
      · intro h
        cases hp : denoteP p e pe <;> simp only [denoteP, hp] at h
        · simp only [evalP, (ihp e pe).2.mpr hp, Option.none_bind]
        · cases hq : denoteP q e pe <;> simp only [hq, Option.map_some', Option.map_none'] at h
          · obtain ⟨a, ha⟩ : ∃ a, evalP p e pe = some a := by
              cases hd : evalP p e pe
              · rw [(ihp e pe).2.mp hd] at hp; simp at hp
              · exact ⟨_, rfl⟩
            simp only [evalP, ha, Option.some_bind, (ihq e pe).2.mpr hq, Option.none_bind]
          · exact absurd h (by simp)
  | not p ih =>
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        simp only [evalP, Option.map_eq_some'] at h
        obtain ⟨b, hb, hbt⟩ := h
        have hb2 : b = false := by cases b <;> simp_all
        subst hb2
        obtain ⟨P, hP⟩ : ∃ P, denoteP p e pe = some P := by
          cases hd : denoteP p e pe
          · rw [(ih e pe).2.mpr hd] at hb; simp at hb
          · exact ⟨_, rfl⟩
        have hnh : ¬ P := fun hph => by
          have h' := (ih e pe).1.mpr ⟨P, hP, hph⟩
          rw [hb] at h'
          exact absurd h' (by simp)
        exact ⟨¬ P, by simp only [denoteP, hP, Option.map_some'], hnh⟩
      · rintro ⟨P, hP, hhold⟩
        cases hp : denoteP p e pe <;> simp only [denoteP, hp, Option.map_some', Option.map_none'] at hP
        · exact absurd hP (by simp)
        · rename_i Q
          cases hP
          obtain ⟨b, hb⟩ : ∃ b, evalP p e pe = some b := by
            cases hd : evalP p e pe
            · rw [(ih e pe).2.mp hd] at hp; simp at hp
            · exact ⟨_, rfl⟩
          have hb2 : b = false := by
            cases hb2 : b
            · rfl
            · exfalso
              obtain ⟨P'', hP'', hP''h⟩ := (ih e pe).1.mp (hb2 ▸ hb)
              rw [hP''] at hp; cases hp
              exact hhold hP''h
          subst hb2
          simp only [evalP, hb, Option.map_some']
          rfl
    · constructor
      · intro h
        simp only [evalP, Option.map_eq_none'] at h
        simp only [denoteP, (ih e pe).2.mp h, Option.map_none']
      · intro h
        simp only [denoteP, Option.map_eq_none'] at h
        simp only [evalP, (ih e pe).2.mpr h, Option.map_none']
  | allIn t p ih =>
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · exact absurd h (by simp)
        · rename_i xs
          have hall : ∀ x ∈ xs, evalP p (⟨_, x⟩ :: e) pe = some true := evalAll_true_iff.mp h
          have hdef : ∀ x ∈ xs, ∃ Q, denoteP p (⟨_, x⟩ :: e) pe = some Q ∧ Q :=
            fun x hx => (ih _ _).1.mp (hall x hx)
          have hguard : xs.all (fun x => (denoteP p (⟨_, x⟩ :: e) pe).isSome) = true := by
            rw [List.all_eq_true]
            intro x hx
            obtain ⟨Q, hQ, -⟩ := hdef x hx
            rw [hQ]
            rfl
          refine ⟨∀ x ∈ xs, ∃ Q, denoteP p (⟨_, x⟩ :: e) pe = some Q ∧ Q, ?_, ?_⟩
          · simp only [denoteP, ht]; rw [if_pos hguard]
          · exact hdef
      · rintro ⟨P, hP, hhold⟩
        cases ht : denoteTerm t e <;> simp only [denoteP, ht] at hP
        · exact absurd hP (by simp)
        · rename_i xs
          by_cases hg : xs.all (fun x => (denoteP p (⟨_, x⟩ :: e) pe).isSome) = true
          · rw [if_pos hg] at hP
            cases hP
            simp only [evalP, ht, Option.some_bind]
            apply evalAll_true_iff.mpr
            intro x hx
            obtain ⟨Q, hQ, hQh⟩ := hhold x hx
            exact (ih _ _).1.mpr ⟨Q, hQ, hQh⟩
          · rw [if_neg hg] at hP
            exact absurd hP (by simp)
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · simp only [denoteP, ht]
        · rename_i xs
          obtain ⟨x, hx, hfnone⟩ := evalAll_none_iff.mp h
          have hd : denoteP p (⟨_, x⟩ :: e) pe = none := (ih _ _).2.mp hfnone
          simp only [denoteP, ht]
          have hg : ¬ xs.all (fun x => (denoteP p (⟨_, x⟩ :: e) pe).isSome) = true := by
            intro hg; rw [List.all_eq_true] at hg
            have hsv := hg x hx
            rw [hd] at hsv
            exact absurd hsv (by simp)
          rw [if_neg hg]
      · intro h
        cases ht : denoteTerm t e <;> simp only [denoteP, ht] at h
        · simp only [evalP, ht, Option.none_bind]
        · rename_i xs
          by_cases hg : xs.all (fun x => (denoteP p (⟨_, x⟩ :: e) pe).isSome) = true
          · rw [if_pos hg] at h
            exact absurd h (by simp)
          · obtain ⟨x, hx, hxf⟩ : ∃ x ∈ xs, ¬ (denoteP p (⟨_, x⟩ :: e) pe).isSome = true := by
              cases hall : xs.all (fun x => (denoteP p (⟨_, x⟩ :: e) pe).isSome)
              · have ⟨x, hx, hxf'⟩ := all_false_witness hall
                exact ⟨x, hx, fun h => by rw [h] at hxf'; exact Bool.noConfusion hxf'⟩
              · exact absurd hall hg
            have hd : denoteP p (⟨_, x⟩ :: e) pe = none := by
              cases hd : denoteP p (⟨_, x⟩ :: e) pe
              · rfl
              · rw [hd] at hxf
                simp at hxf
            have he : evalP p (⟨_, x⟩ :: e) pe = none := (ih _ _).2.mpr hd
            simp only [evalP, ht, Option.some_bind]
            exact evalAll_none_iff.mpr ⟨x, hx, he⟩
  | exIn t p ih =>
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · exact absurd h (by simp)
        · rename_i xs
          obtain ⟨hdef, y, hy, hfy⟩ := evalAny_true_iff.mp h
          have hguard : xs.all (fun x => (denoteP p (⟨_, x⟩ :: e) pe).isSome) = true := by
            rw [List.all_eq_true]
            intro x hx
            obtain ⟨b, hb⟩ := hdef x hx
            cases hd : denoteP p (⟨_, x⟩ :: e) pe
            · exfalso
              rw [(ih _ _).2.mpr hd] at hb
              simp at hb
            · rfl
          refine ⟨∃ y ∈ xs, ∃ Q, denoteP p (⟨_, y⟩ :: e) pe = some Q ∧ Q, ?_, ?_⟩
          · simp only [denoteP, ht]; rw [if_pos hguard]
          · obtain ⟨Q, hQ, hQh⟩ := (ih _ _).1.mp hfy
            exact ⟨y, hy, Q, hQ, hQh⟩
      · rintro ⟨P, hP, hhold⟩
        cases ht : denoteTerm t e <;> simp only [denoteP, ht] at hP
        · exact absurd hP (by simp)
        · rename_i xs
          by_cases hg : xs.all (fun x => (denoteP p (⟨_, x⟩ :: e) pe).isSome) = true
          · rw [if_pos hg] at hP
            cases hP
            simp only [evalP, ht, Option.some_bind]
            apply evalAny_true_iff.mpr
            constructor
            · intro x hx
              obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hg x hx)
              cases hb : evalP p (⟨_, x⟩ :: e) pe
              · rw [(ih _ _).2.mp hb] at hQ; simp at hQ
              · exact ⟨_, rfl⟩
            · obtain ⟨y, hy, Q, hQ, hQh⟩ := hhold
              exact ⟨y, hy, (ih _ _).1.mpr ⟨Q, hQ, hQh⟩⟩
          · rw [if_neg hg] at hP
            exact absurd hP (by simp)
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · simp only [denoteP, ht]
        · rename_i xs
          obtain ⟨x, hx, hfnone⟩ := evalAny_none_iff.mp h
          have hd : denoteP p (⟨_, x⟩ :: e) pe = none := (ih _ _).2.mp hfnone
          simp only [denoteP, ht]
          have hg : ¬ xs.all (fun x => (denoteP p (⟨_, x⟩ :: e) pe).isSome) = true := by
            intro hg; rw [List.all_eq_true] at hg
            have hsv := hg x hx
            rw [hd] at hsv
            exact absurd hsv (by simp)
          rw [if_neg hg]
      · intro h
        cases ht : denoteTerm t e <;> simp only [denoteP, ht] at h
        · simp only [evalP, ht, Option.none_bind]
        · rename_i xs
          by_cases hg : xs.all (fun x => (denoteP p (⟨_, x⟩ :: e) pe).isSome) = true
          · rw [if_pos hg] at h
            exact absurd h (by simp)
          · obtain ⟨x, hx, hxf⟩ : ∃ x ∈ xs, ¬ (denoteP p (⟨_, x⟩ :: e) pe).isSome = true := by
              cases hall : xs.all (fun x => (denoteP p (⟨_, x⟩ :: e) pe).isSome)
              · have ⟨x, hx, hxf'⟩ := all_false_witness hall
                exact ⟨x, hx, fun h => by rw [h] at hxf'; exact Bool.noConfusion hxf'⟩
              · exact absurd hall hg
            have hd : denoteP p (⟨_, x⟩ :: e) pe = none := by
              cases hd : denoteP p (⟨_, x⟩ :: e) pe
              · rfl
              · rw [hd] at hxf
                simp at hxf
            have he : evalP p (⟨_, x⟩ :: e) pe = none := (ih _ _).2.mpr hd
            simp only [evalP, ht, Option.some_bind]
            exact evalAny_none_iff.mpr ⟨x, hx, he⟩
  | isInl t =>
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · exact absurd h (by simp)
        · rename_i v
          cases v with
          | inl x =>
            exact ⟨∃ x', Sum.inl x = Sum.inl x',
              by simp only [denoteP, ht, Option.map_some']; rfl, ⟨x, rfl⟩⟩
          | inr x =>
            exact absurd h (by simp)
      · rintro ⟨P, hP, hhold⟩
        cases ht : denoteTerm t e <;> simp only [denoteP, ht, Option.map_some', Option.map_none'] at hP
        · exact absurd hP (by simp)
        · rename_i v
          cases hP
          obtain ⟨x, hx⟩ := hhold
          simp only [evalP, ht, Option.some_bind]
          rw [hx]
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · simp only [denoteP, ht, Option.map_none']
        · rename_i v
          cases v <;> exact absurd h (by simp)
      · intro h
        cases ht : denoteTerm t e <;> simp only [denoteP, ht, Option.map_some', Option.map_none'] at h
        · simp only [evalP, ht, Option.none_bind]
        · rename_i v
          cases v <;> exact absurd h (by simp)
  | isInr t =>
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · exact absurd h (by simp)
        · rename_i v
          cases v with
          | inr x =>
            exact ⟨∃ x', Sum.inr x = Sum.inr x',
              by simp only [denoteP, ht, Option.map_some']; rfl, ⟨x, rfl⟩⟩
          | inl x =>
            exact absurd h (by simp)
      · rintro ⟨P, hP, hhold⟩
        cases ht : denoteTerm t e <;> simp only [denoteP, ht, Option.map_some', Option.map_none'] at hP
        · exact absurd hP (by simp)
        · rename_i v
          cases hP
          obtain ⟨x, hx⟩ := hhold
          simp only [evalP, ht, Option.some_bind]
          rw [hx]
    · constructor
      · intro h
        simp only [evalP] at h
        cases ht : denoteTerm t e <;> simp only [ht, Option.none_bind, Option.some_bind] at h
        · simp only [denoteP, ht, Option.map_none']
        · rename_i v
          cases v <;> exact absurd h (by simp)
      · intro h
        cases ht : denoteTerm t e <;> simp only [denoteP, ht, Option.map_some', Option.map_none'] at h
        · simp only [evalP, ht, Option.none_bind]
        · rename_i v
          cases v <;> exact absurd h (by simp)
  | pcall q args =>
    refine ⟨?_, ?_⟩
    · constructor
      · intro h
        simp only [evalP] at h
        cases hq : pe q <;> simp only [hq, Option.none_bind, Option.some_bind] at h
        · exact absurd h (by simp)
        · rename_i cp
          cases ha : denoteArgs args e <;> simp only [ha, Option.none_bind, Option.some_bind] at h
          · exact absurd h (by simp)
          · rename_i argv
            by_cases har : argv.length = cp.nargs
            · rw [if_pos har] at h
              rw [Option.some.injEq] at h
              exact ⟨_, by simp only [denoteP, hq, ha, if_pos har], (cp.cert argv).mp h⟩
            · rw [if_neg har] at h
              exact absurd h (by simp)
      · rintro ⟨P, hP, hhold⟩
        cases hq : pe q <;> simp only [denoteP, hq] at hP
        · exact absurd hP (by simp)
        · rename_i cp
          cases ha : denoteArgs args e <;> simp only [ha] at hP
          · exact absurd hP (by simp)
          · rename_i argv
            by_cases har : argv.length = cp.nargs
            · rw [if_pos har] at hP
              cases hP
              simp only [evalP, hq, ha, Option.some_bind, if_pos har]
              exact congrArg _ ((cp.cert argv).mpr hhold)
            · rw [if_neg har] at hP
              exact absurd hP (by simp)
    · constructor
      · intro h
        simp only [evalP] at h
        cases hq : pe q <;> simp only [hq, Option.none_bind, Option.some_bind] at h
        · simp only [denoteP, hq]
        · rename_i cp
          cases ha : denoteArgs args e <;> simp only [ha, Option.none_bind, Option.some_bind] at h
          · simp only [denoteP, hq, ha, Option.none_bind]
          · rename_i argv
            by_cases har : argv.length = cp.nargs
            · rw [if_pos har] at h
              exact absurd h (by simp)
            · rw [if_neg har] at h
              simp only [denoteP, hq, ha, Option.some_bind, if_neg har]
      · intro h
        cases hq : pe q <;> simp only [denoteP, hq] at h
        · simp only [evalP, hq, Option.none_bind]
        · rename_i cp
          cases ha : denoteArgs args e <;> simp only [ha] at h
          · simp only [evalP, hq, ha, Option.some_bind, Option.none_bind]
          · rename_i argv
            by_cases har : argv.length = cp.nargs
            · rw [if_pos har] at h
              exact absurd h (by simp)
            · rw [if_neg har] at h
              simp only [evalP, hq, ha, Option.some_bind, if_neg har]

/-- **CT-012.** The §14 reflection theorem: `decideProp` answers `true`
    exactly when the strict denotation holds — sound and complete. -/
theorem decideProp_iff {Γ} (p : AssertProp Γ) (e : AEnv) (pe : PredEnv) :
    decideProp p e pe = true ↔ denoteProp p e pe := by
  unfold decideProp denoteProp
  rw [show (evalP p e pe == some true) = (evalP p e pe = some true) from
    propext beq_iff_eq]
  exact (evalP_correct p e pe).1

/-- Strictness lemma: `not` is undefined exactly when its argument is —
    negation cannot repair undefinedness. -/
theorem denoteP_not_none_iff {Γ} {p : AssertProp Γ} {e : AEnv} {pe : PredEnv} :
    denoteP (.not p) e pe = none ↔ denoteP p e pe = none := by
  simp only [denoteP, Option.map_eq_none']

/-- An undefined `not` decides false — strict partiality propagates. -/
theorem decideProp_not_of_undefined {Γ} {p : AssertProp Γ} {e : AEnv} {pe : PredEnv}
    (h : evalP p e pe = none) : decideProp (.not p) e pe = false := by
  simp only [decideProp, evalP, h, Option.map_none']
  rfl

/-! ## Teeth, one per excluded construct and refusal arm -/

/-- The fuel mutant: a fuel-bounded lookalike — the *unbounded recursion*
    tooth. -/
def evalPF : Nat → AssertProp Γ → AEnv → PredEnv → Option Bool
  | 0, _, _, _ => none
  | _ + 1, .eq t u, e, _ =>
    (denoteTerm t e).bind fun x => (denoteTerm u e).bind fun y => some (decide (x = y))
  | _ + 1, .lt t u, e, _ =>
    (denoteTerm t e).bind fun x => (denoteTerm u e).bind fun y => some (decide (x < y))
  | _ + 1, .le t u, e, _ =>
    (denoteTerm t e).bind fun x => (denoteTerm u e).bind fun y => some (decide (x ≤ y))
  | n + 1, .and p q, e, pe =>
    (evalPF n p e pe).bind fun a => (evalPF n q e pe).bind fun b => some (a && b)
  | n + 1, .or p q, e, pe =>
    (evalPF n p e pe).bind fun a => (evalPF n q e pe).bind fun b => some (a || b)
  | n + 1, .impl p q, e, pe =>
    (evalPF n p e pe).bind fun a => (evalPF n q e pe).bind fun b => some (!a || b)
  | n + 1, .not p, e, pe => (evalPF n p e pe).map (!·)
  | n + 1, .allIn t p, e, pe =>
    (denoteTerm t e).bind fun xs => evalAll (fun x => evalPF n p (⟨_, x⟩ :: e) pe) xs
  | n + 1, .exIn t p, e, pe =>
    (denoteTerm t e).bind fun xs => evalAny (fun x => evalPF n p (⟨_, x⟩ :: e) pe) xs
  | _ + 1, .isInl t, e, _ =>
    (denoteTerm t e).bind fun v => match v with | .inl _ => some true | .inr _ => some false
  | _ + 1, .isInr t, e, _ =>
    (denoteTerm t e).bind fun v => match v with | .inr _ => some true | .inl _ => some false
  | _ + 1, .pcall q args, e, pe =>
    (pe q).bind fun cp => (denoteArgs args e).bind fun argv =>
      if argv.length = cp.nargs then some (cp.dec argv) else none

/-- The fuel mutant diverges from the strict semantics at fuel 0 on the
    simplest true proposition — while `evalP` needs no fuel. -/
theorem evalPF_zero_breaks :
    ∃ p : AssertProp [], denoteProp p [] (fun _ => none) ∧
      evalPF 0 p [] (fun _ => none) = none ∧ decideProp p [] (fun _ => none) = true :=
  ⟨.eq (.litI 0) (.litI 0),
   ⟨0 = 0, by simp only [denoteP, denoteTerm, Option.map_some'], rfl⟩,
   rfl, by simp only [decideProp, evalP, denoteTerm, Option.some_bind]; rfl⟩

/-- The *IO* tooth: a predicate call's meaning is exhausted by the
    environment entry — no ambient state or effect channel exists. -/
theorem pcall_uses_env {Γ} {q : String} {args : List (Sigma (AssertTerm Γ))}
    {e : AEnv} {pe₁ pe₂ : PredEnv} (h : pe₁ q = pe₂ q) :
    evalP (.pcall q args) e pe₁ = evalP (.pcall q args) e pe₂ ∧
    denoteP (.pcall q args) e pe₁ = denoteP (.pcall q args) e pe₂ := by
  simp only [evalP, denoteP, h]
  exact ⟨trivial, trivial⟩

/-- The *untrusted host predicate* tooth: a predicate that decides true
    while denoting False cannot be built — the certificate field makes
    it uninhabitable. -/
theorem bogus_pred_uninhabited :
    ¬ ∃ cp : CertifiedPred, cp.dec = (fun _ => true) ∧ cp.den = (fun _ => False) := by
  rintro ⟨cp, hd, hden⟩
  have h := (cp.cert []).mp (by rw [hd])
  rw [hden] at h
  exact h

/-- An unknown q is undefined, not a host dispatch. -/
theorem pcall_unknown_none {Γ} {q : String} {args : List (Sigma (AssertTerm Γ))}
    {e : AEnv} {pe : PredEnv} (h : pe q = none) :
    evalP (.pcall q args) e pe = none ∧ denoteP (.pcall q args) e pe = none := by
  simp only [evalP, denoteP, h, Option.none_bind]
  exact ⟨trivial, trivial⟩

/-- Lookup refusal arm: a missing env entry is undefined. -/
theorem lookupEnv_miss {e : AEnv} {i : Nat} {T : ATy} (h : e.get? i = none) :
    lookupEnv e i T = none := by
  unfold lookupEnv; rw [h]

/-- Lookup refusal arm: a mistagged env entry is undefined. -/
theorem lookupEnv_mistag {e : AEnv} {i : Nat} {T T' : ATy} {v : denTy T'}
    (h : e.get? i = some ⟨T', v⟩) (hne : T' ≠ T) :
    lookupEnv e i T = none := by
  simp only [lookupEnv, h]; rw [dif_neg hne]

/-- Checked-arithmetic refusal arm: an out-of-i64 result is undefined. -/
theorem denoteTerm_add_overflow {e : AEnv}
    (ht : denoteTerm t e = some x) (hu : denoteTerm u e = some y)
    (hov : ¬ inI64 ((x : Int) + (y : Int))) :
    denoteTerm (.add t u) e = none := by
  simp only [denoteTerm, ht, hu]
  rw [if_neg hov]

/-! ## Annex 26.29 — the three `denoteTerm` arms -/

theorem denoteTerm_snoc_eq {Γ a}
    (ts : AssertTerm Γ (.list a)) (t : AssertTerm Γ a) (e : AEnv) :
    denoteTerm (.snoc ts t) e =
      match denoteTerm ts e, denoteTerm t e with
      | some xs, some x => some (xs ++ [x])
      | _, _ => none := by
  rfl

theorem denoteTerm_record_eq {Γ}
    (keys : List String) (fields : List (Sigma (AssertTerm Γ))) (e : AEnv) :
    denoteTerm (.record keys fields) e =
      if keys.length == fields.length && noDupKeys keys then
        (denoteFields fields e).map Val.r
      else none := by
  rfl

theorem denoteTerm_field_eq {Γ T}
    (t : AssertTerm Γ .val) (i : Nat) (e : AEnv) :
    denoteTerm (.field t i) e =
      match denoteTerm t e with
      | some (.r xs) =>
        match xs.get? i with
        | some v => unpackVal T v
        | none => none
      | _ => none := by
  rfl

theorem pack_unpack_int (n : Int) :
    unpackVal .int (packVal .int n) = some n := by
  simp [packVal, unpackVal]

theorem pack_unpack_bool_tt :
    unpackVal .bool (packVal .bool true) = some true := by
  simp [packVal, unpackVal]

theorem pack_unpack_bool_ff :
    unpackVal .bool (packVal .bool false) = some false := by
  simp [packVal, unpackVal]

theorem pack_unpack_str (s : String) :
    unpackVal .str (packVal .str s) = some s := by
  simp [packVal, unpackVal]

theorem pack_unpack_nil (a : ATy) :
    unpackVal (.list a) (packVal (.list a) ([] : List (denTy a))) = some [] := by
  simp [packVal, packList, unpackVal, unpackList]

/-- An `int` slot read as `bool` is a mistag. -/
theorem unpack_int_as_bool (n : Int) :
    unpackVal .bool (packVal .int n) = none := by
  simp [packVal, unpackVal]

/-! ## Annex 26.30 — `ATy.rec_` -/

/-- `nil` at a list of records denotes the empty list. The schema is not a value. -/
theorem denoteTerm_nil_at_rec {Γ : ACtx} (fs : List (String × ATy)) (e : AEnv) :
    denoteTerm (.nil : AssertTerm Γ (.list (.rec_ fs))) e = some [] := rfl

/-- The empty schema packs and unpacks as `Val.r []`. -/
theorem pack_unpack_rec_empty :
    unpackVal (.rec_ []) (packVal (.rec_ []) ()) = some () := by
  rw [packVal.eq_9, packRec.eq_1, unpackVal.eq_14, unpackRec.eq_1]

/-- One `int` field round-trips through `Val.r`. -/
theorem pack_unpack_rec_int (n : Int) :
    unpackVal (.rec_ [("k", .int)]) (packVal (.rec_ [("k", .int)]) (n, ())) =
      some (n, ()) := by
  rw [packVal.eq_9, packRec.eq_2, packVal.eq_1, packRec.eq_1,
      unpackVal.eq_14, unpackRec.eq_4, unpackVal.eq_1, unpackRec.eq_1]

/-- A longer payload than the schema is `none`. -/
theorem unpack_rec_len :
    unpackVal (.rec_ []) (.r [.i 0]) = none := rfl

/-- One field that fails to unpack makes the record `none`. -/
theorem unpack_rec_bad_field :
    unpackVal (.rec_ [("k", .int)]) (.r [.b 0]) = none := rfl

#print axioms noDupKeys_iff
#print axioms denoteTerm_snoc_eq
#print axioms denoteTerm_record_eq
#print axioms denoteTerm_field_eq
#print axioms pack_unpack_int
#print axioms pack_unpack_bool_tt
#print axioms pack_unpack_bool_ff
#print axioms pack_unpack_str
#print axioms pack_unpack_nil
#print axioms unpack_int_as_bool
#print axioms ATy.beq_rfl
#print axioms schemaBeq_rfl
#print axioms ATy.eq_of_beq
#print axioms schema_eq_of_beq
#print axioms denoteTerm_nil_at_rec
#print axioms pack_unpack_rec_empty
#print axioms pack_unpack_rec_int
#print axioms unpack_rec_len
#print axioms unpack_rec_bad_field

end Rcic.Scm.Reflect
