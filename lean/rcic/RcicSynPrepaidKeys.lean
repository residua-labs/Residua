/-
RcicSynPrepaidKeys — S18 (`research/rcic/sortrow/S18_PREPAID_OCCURRENCE_KEYS.md`,
PR #7395): exact occurrence keys and completion certificates for `prepaidUse`.
Credit: ChatGPT S18.

§1 a cache key is never just a Goal or its endpoints. `QueryKey` carries the
   frozen-forest code, the original root and call occurrence, the request
   kind, each input's FieldPath/DRef code (and its `reg`), the original
   replacement/bridge reference, and the level-map code. Every field is a
   finite code, so full-key equality is decidable — reuse is authorized by
   full key equality, never by hash or endpoint equality, and there is no
   comparison of arbitrary functions.

§2 `entries : Array QueryKey` is the data table; `proofs : ∀ i, Ans
   (decode entries[i])` is the semantic proof table — `S18Forest.ans`
   decodes a key to its real PB request (`decodeKey`), and an answer is a
   real `CvP` at the decoded input's endpoints. `lookup : QueryKey →
   Option (Fin entries.size)` with `lookup_exact`; `prepaidUse` only
   transports the existing `proofs i` along `lookup_exact` — no
   re-materialized typed input, no new IH call.

§4 controls (kernel-computed): `refl`'s `c.h` vs `c.dl` are distinct
   original field positions decoding to the SAME actual `s18S` — their
   decoded Goals/contexts/maps are equal (proved by kernel), yet their
   keys differ, so exact lookup of `k₂` misses while a Goal-only lookup
   hits; the same input position under the real `instLevel [.zero]` code
   misses; a replacement from another original occurrence misses. A
   lookup miss never means the demand does not exist.

The shared FieldPath/DRef layer is NOT on main yet — `FieldPathStub` /
`DRefCode` are minimal local stand-ins, clearly named, to be replaced when
the layer lands. Nothing existing is touched.
-/

import rcic.RcicDeclarative
import rcic.RcicConvPlus

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 finite key codes (stand-ins for the shared FieldPath/DRef layer) -/

/-- Stand-in for the shared `FieldPath` layer (to be replaced when it
    lands): a field path into a derivation or expression, as a list of
    child indices. -/
abbrev FieldPathStub : Type := List Nat

/-- `DRefCode` — §1's deterministic reference codes: an original `path`;
    the `h` field position (§4's control uses `refl.h`); the `reg`, `dl`,
    `dr` projections of a reference; an original `lazyT`ransport together
    with its parameter references (as field paths — a `List DRefCode`
    payload would make `DecidableEq` non-derivable; paths are the
    stand-in anyway). Finite codes — decidable equality, no function
    comparison. -/
inductive DRefCode : Type
  | path : FieldPathStub → DRefCode
  | h : DRefCode → DRefCode
  | reg : DRefCode → DRefCode
  | dl : DRefCode → DRefCode
  | dr : DRefCode → DRefCode
  | lazyT : DRefCode → List FieldPathStub → DRefCode
  deriving DecidableEq

/-- `LevelMapCode` — §1's level-map codes: the identity map; an original
    `linst` argument list (the list itself is the finite code); composition
    in original order. Never a comparison of arbitrary level functions. -/
inductive LevelMapCode : Type
  | identity : LevelMapCode
  | linst : List Level → LevelMapCode
  | comp : LevelMapCode → LevelMapCode → LevelMapCode
  deriving DecidableEq

/-- Codes decode to REAL maps: `linst ls` decodes to the actual
    `instLevel ls`, composition in original order. -/
def LevelMapCode.eval : LevelMapCode → Level → Level
  | .identity => fun l => l
  | .linst ls => instLevel ls
  | .comp f g => fun l => f.eval (g.eval l)

/-- §1's "request kind"; `pb` is §4's PB request. -/
inductive ReqKind : Type
  | pb | he
  deriving DecidableEq

/-- `QueryKey` — §1: a cache key is never just a Goal or its endpoints.
    Every field is a finite code in the frozen forest, so full-key
    equality is decidable. The Goal is NOT a stored field — §1 computes
    context, map and subject from these codes in the same frozen Forest;
    `decodeKey` below is that computation. -/
structure QueryKey : Type where
  /-- frozen-forest version stamp -/
  forest : Nat
  /-- the original root object's reference -/
  root : DRefCode
  /-- the original call occurrence's path -/
  callOccurrence : FieldPathStub
  requestKind : ReqKind
  inputOccurrence : DRefCode
  inputReg : DRefCode
  replacement : DRefCode
  levelMap : LevelMapCode
  deriving DecidableEq

/-! ## §2 the two tables, exact lookup, transport-only consumption -/

/-- §2: the data table (`entries`) is separate from the semantic proof
    table (`proofs`). `Ans` is the answer family over decoded keys —
    instantiated below by `S18Forest.ans`, the `decodeKey` composition. -/
structure PrepaidTable (Ans : QueryKey → Type) : Type where
  entries : Array QueryKey
  proofs : (i : Fin entries.size) → Ans (entries.get i)

/-- First-hit scan for a key in a list; the hit is the exact list index. -/
def findKey : (xs : List QueryKey) → QueryKey → Option (Fin xs.length)
  | [], _ => none
  | x :: xs, k =>
      if x = k then some ⟨0, Nat.zero_lt_succ _⟩
      else (findKey xs k).map fun i => ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-- §2: `lookup : QueryKey → Option (Fin entries.size)`. -/
def PrepaidTable.lookup (t : PrepaidTable Ans) (k : QueryKey) :
    Option (Fin t.entries.size) :=
  findKey t.entries.toList k

/-- A hit is an exact match: `findKey` returns the index of an entry that
    IS the key. -/
theorem findKey_exact {k : QueryKey} {xs : List QueryKey} {i : Fin xs.length}
    (h : findKey xs k = some i) : xs.get i = k := by
  induction xs with
  | nil => exact Option.noConfusion h
  | cons x xs ih =>
      by_cases hx : x = k
      · have hi : i = ⟨0, Nat.zero_lt_succ xs.length⟩ := by
          have hit : findKey (x :: xs) k =
              some ⟨0, Nat.zero_lt_succ xs.length⟩ := by simp [findKey, hx]
          rw [hit] at h; exact (Option.some.inj h).symm
        subst hi; exact hx
      · cases hk : findKey xs k with
        | none =>
            have hz : findKey (x :: xs) k = none := by simp [findKey, hx, hk]
            rw [hz] at h; exact Option.noConfusion h
        | some j =>
            have hit : findKey (x :: xs) k =
                some ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
              simp [findKey, hx, hk]
            rw [hit] at h
            have hi := Option.some.inj h
            subst hi
            exact ih hk

/-- §2: `lookup_exact : lookup k = some i → entries[i] = k`. -/
theorem PrepaidTable.lookup_exact {Ans : QueryKey → Type} {t : PrepaidTable Ans}
    {k : QueryKey} {i : Fin t.entries.size}
    (h : t.lookup k = some i) : t.entries.get i = k :=
  findKey_exact h

/-- §2: `prepaidUse` — consumption only transports the existing `proofs i`
    along `lookup_exact`. No re-materialized typed input, no new IH call,
    no restored historical provider atom. -/
def PrepaidTable.prepaidUse (t : PrepaidTable Ans) (k : QueryKey)
    {i : Fin t.entries.size} (h : t.lookup k = some i) : Ans k :=
  t.lookup_exact h ▸ t.proofs i

/-- The mechanism IS the transport: `prepaidUse` unfolds to `proofs i`
    rewritten along `lookup_exact`, nothing else. -/
theorem s18_prepaidUse_only_transports {Ans : QueryKey → Type}
    (t : PrepaidTable Ans) (k : QueryKey) {i : Fin t.entries.size}
    (h : t.lookup k = some i) :
    t.prepaidUse k h = t.lookup_exact h ▸ t.proofs i := rfl

/-! ## §4 controls: same semantic query at a different occurrence must miss

The fixture's frozen forest: three REAL original objects and a decoder
binding every used `DRefCode`/`LevelMapCode` to them. -/

/-- §4's minimal control typing: `s : TyP emptyEnv 0 [] (sort 0) (sort 1)`. -/
def s18S : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort emptyEnv 0 [] .zero (.succ .zero) (fun _ => rfl)

/-- `c := CvP.refl … s s s` — the three `TyP` fields `h`, `dl`, `dr` carry
    definitionally equal typing values at three ORIGINAL field positions. -/
def s18C : CvP emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  CvP.refl emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) s18S s18S s18S

/-- The frozen forest of the §4 fixture: the original `refl` node at
    occurrence `[0]` and two TyP objects at occurrences `[1,0]`/`[1,1]`
    carrying the SAME type/term at DIFFERENT original positions. -/
structure S18Forest : Type where
  /-- the original `refl` node -/
  c : CvP emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort (.succ .zero))
  /-- the original replacement object at occurrence `[1,0]` -/
  repA : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero))
  /-- ANOTHER original occurrence's object at `[1,1]` — same type/term -/
  repB : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero))

/-- §4's frozen forest: `c` is `s18C`; `repA` is `s18S` itself; `repB` is
    `s18C.dr` — a different original occurrence holding the same value. -/
def s18Forest : S18Forest := ⟨s18C, s18S, s18C.dr⟩

/-- Decoded objects range over ALL indices — the decode Sigmas are fully
    general (the fixture's objects happen to live at `emptyEnv, 0, []`,
    but field positions on transports move the indices). -/
abbrev CvPRef : Type :=
  Σ' (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (a b T : Expr Nat),
    CvP E n Γ a b T
abbrev TyPRef : Type :=
  Σ' (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e T : Expr Nat),
    TyP E n Γ e T

/-- Decode a CvP-valued reference: `[0]` is the frozen `refl` node. -/
def S18Forest.decodeCvP (F : S18Forest) : DRefCode → Option CvPRef
  | .path [0] => some ⟨_, _, _, _, _, _, F.c⟩
  | _ => none

/-- `.h` is an original field position only on `refl`/`eta` nodes; the
    decode refuses everywhere else — positions exist only where the
    field exists. -/
def s18CvH? : CvPRef → Option TyPRef
  | ⟨_, _, _, _, _, _, .refl _ _ _ _ _ h _ _⟩ => some ⟨_, _, _, _, _, h⟩
  | ⟨_, _, _, _, _, _, .eta _ _ _ _ _ _ h _ _⟩ => some ⟨_, _, _, _, _, h⟩
  | _ => none

/-- Decode a TyP-valued reference: `[1,0]`/`[1,1]` are the two original
    replacement-pool occurrences; `.h`/`.dl`/`.dr` project the referenced
    CvP node's REAL fields; `.reg d` decodes `d` and takes its actual
    `TyP.reg.2`. `lazyT` nodes are not present in this finite forest. -/
def S18Forest.decodeTyP (F : S18Forest) : DRefCode → Option TyPRef
  | .path [1, 0] => some ⟨_, _, _, _, _, F.repA⟩
  | .path [1, 1] => some ⟨_, _, _, _, _, F.repB⟩
  | .path _ => none
  | .h c => (F.decodeCvP c).bind s18CvH?
  | .dl c => (F.decodeCvP c).map fun ⟨_, _, _, _, _, _, cv⟩ =>
      ⟨_, _, _, _, _, cv.dl⟩
  | .dr c => (F.decodeCvP c).map fun ⟨_, _, _, _, _, _, cv⟩ =>
      ⟨_, _, _, _, _, cv.dr⟩
  | .reg d => (F.decodeTyP d).map fun ⟨E, n, Γ, _, T, D⟩ =>
      ⟨E, n, Γ, T, .sort D.reg.1, D.reg.2⟩
  | .lazyT .. => none

/-- §2's decoded request: what a key MEANS in the frozen forest. Every
    field is a REAL object decoded from the key's codes — the original
    root, the PB input and its regularity, the replacement, the context
    and the decoded level map. -/
structure PBRequest : Type where
  root : CvPRef
  input : TyPRef
  inputReg : TyPRef
  replacement : TyPRef
  /-- the request's context — the decoded input's own `Γ` -/
  ctx : LCtx
  /-- the decoded level map — a real `Level → Level` -/
  levelMap : Level → Level

/-- The decoded input's subject. -/
def PBRequest.subj (r : PBRequest) : Expr Nat := r.input.2.2.2.1
/-- The decoded input's ambient type. -/
def PBRequest.objTy (r : PBRequest) : Expr Nat := r.input.2.2.2.2.1

/-- A PB request's semantic Goal — COMPUTED from the decoded input
    (§1: the subject/type pair is computed from the codes, never stored
    as a key field). -/
def PBRequest.goal (r : PBRequest) : Expr Nat × Expr Nat :=
  (r.subj, r.objTy)

/-- §2's `Answer`: the decoded PB certificate — a real `CvP` at the
    request's decoded endpoints and indices. Its indices ARE the output
    equation: an exact certificate of a real returned object. -/
def PBRequest.answer (r : PBRequest) : Type :=
  CvP r.input.1 r.input.2.1 r.input.2.2.1 r.subj r.subj r.objTy

/-- §1's computation: decode a key to its real request in the forest. -/
def S18Forest.decodeKey (F : S18Forest) (k : QueryKey) :
    Option PBRequest := do
  let root ← F.decodeCvP k.root
  let input ← F.decodeTyP k.inputOccurrence
  let inputReg ← F.decodeTyP k.inputReg
  let replacement ← F.decodeTyP k.replacement
  some ⟨root, input, inputReg, replacement, input.2.2.1, k.levelMap.eval⟩

/-- The decoded Goal of a key (`none` when the key does not decode). -/
def S18Forest.goalOf (F : S18Forest) (k : QueryKey) :
    Option (Expr Nat × Expr Nat) :=
  (F.decodeKey k).map (·.goal)

/-- §2: `Ans (decode k)` — the answer family over the DECODED key. -/
def S18Forest.Answer : Option PBRequest → Type
  | some r => r.answer
  | none => PUnit

def S18Forest.ans (F : S18Forest) (k : QueryKey) : Type :=
  S18Forest.Answer (F.decodeKey k)

/-- `c`'s own reference; its decoding equation is `decodeCvP` at `[0]`. -/
def s18CRef : DRefCode := .path [0]

/-- §4: `k₁` — a PB request on `c.h` and its reg; `k₂` — the same semantic
    request on `c.dl` and its reg. Identical forest/root/call/level-map
    codes; they differ ONLY in the occurrence codes. -/
def s18Base : QueryKey :=
  { forest := 0, root := s18CRef, callOccurrence := [0], requestKind := .pb,
    inputOccurrence := .h s18CRef, inputReg := .reg (.h s18CRef),
    replacement := .path [1, 0],
    levelMap := .identity }

def s18K1 : QueryKey := s18Base

def s18K2 : QueryKey :=
  { s18Base with inputOccurrence := .dl s18CRef,
                 inputReg := .reg (.dl s18CRef) }

/-- Same input position as `k₁` but a different `linst` map code —
    decoding to the real `instLevel [.zero]`. -/
def s18K3 : QueryKey := { s18Base with levelMap := .linst [.zero] }

/-- Same everything as `k₁` but the replacement comes from ANOTHER
    original occurrence (`[1,1]` → `s18C.dr`, not `[1,0]` → `s18S`). -/
def s18K4 : QueryKey := { s18Base with replacement := .path [1, 1] }

/-- The table holding only `k₁`'s completed entry: its proof is `s18C`
    itself — the real `CvP` certificate at the decoded goal. -/
def s18Table : PrepaidTable s18Forest.ans where
  entries := #[s18K1]
  proofs := fun i =>
    match i with
    | ⟨0, _⟩ => s18C
    | ⟨Nat.succ _, h⟩ =>
        absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)

/-! ### decoding equations — the codes are bound to the actual objects -/

/-- `refl`'s `h` field position decodes to the ACTUAL `s18S`. -/
theorem s18_decode_input_is_c_h :
    s18Forest.decodeTyP (.h s18CRef) = some ⟨_, _, _, _, _, s18S⟩ := rfl

/-- `refl`'s `dl` field position decodes to the SAME actual `s18S` —
    `c.h` and `c.dl` are definitionally equal typing VALUES at distinct
    original field positions. -/
theorem s18_k1_k2_same_input :
    s18Forest.decodeTyP (.dl s18CRef) = s18Forest.decodeTyP (.h s18CRef) :=
  rfl

/-- `c.h`'s reg decodes to the actual `s18S.reg.2`. -/
theorem s18_decode_reg_is_c_h_reg :
    s18Forest.decodeTyP (.reg (.h s18CRef)) =
      some ⟨_, _, _, _, _, s18S.reg.2⟩ := rfl

/-- `c.dl`'s reg decodes to the same actual regularity. -/
theorem s18_k1_k2_same_reg :
    s18Forest.decodeTyP (.reg (.dl s18CRef)) =
      s18Forest.decodeTyP (.reg (.h s18CRef)) := rfl

/-- The actual PB Goal equality: `k₁` and `k₂` decode to the same goal
    `(sort 0, sort 1)` — endpoint equality is not authorization. -/
theorem s18_k1_k2_same_goal :
    s18Forest.goalOf s18K1 = s18Forest.goalOf s18K2 := rfl

/-- The actual context equality: both requests decode in `Γ = []`. -/
theorem s18_k1_k2_same_ctx :
    (s18Forest.decodeKey s18K1).map (·.ctx) =
      (s18Forest.decodeKey s18K2).map (·.ctx) := rfl

/-- The actual map equality: both requests decode under the identity
    level map. -/
theorem s18_k1_k2_same_map :
    s18K1.levelMap.eval = s18K2.levelMap.eval := rfl

/-- `k₃`'s map code decodes to the REAL `instLevel [.zero]` — an actual
    linst, not a tag. -/
theorem s18_k3_map_is_real_linst : s18K3.levelMap.eval = instLevel [.zero] :=
  rfl

/-- …which agrees with `k₁`'s identity on every level of the decoded
    goal — same semantic request, different map code. -/
theorem s18_k3_map_agrees_on_goal :
    s18K3.levelMap.eval .zero = s18K1.levelMap.eval .zero ∧
      s18K3.levelMap.eval (.succ .zero) = s18K1.levelMap.eval (.succ .zero) :=
  ⟨rfl, rfl⟩

/-- `k₄`'s replacement code decodes to a REAL other original occurrence —
    `s18C.dr` at `[1,1]` — carrying the same decoded type/term as `[1,0]`. -/
theorem s18_k4_replacement_same_semantics :
    s18Forest.decodeTyP (.path [1, 1]) = s18Forest.decodeTyP (.path [1, 0]) :=
  rfl

/-- The semantic requests still coincide for the map and replacement
    variations — only the codes differ. -/
theorem s18_k3_same_goal : s18Forest.goalOf s18K3 = s18Forest.goalOf s18K1 :=
  rfl

theorem s18_k4_same_goal : s18Forest.goalOf s18K4 = s18Forest.goalOf s18K1 :=
  rfl

/-! ### the controls -/

/-- §4 control 1: `refl.h` and `refl.dl` are DIFFERENT original field
    positions — the keys differ even though every semantic field agrees. -/
theorem s18_h_dl_keys_differ : s18K1 ≠ s18K2 := by decide

/-- §4 control 1: with only `k₁` in the table, exact lookup of `k₂`
    MISSES — reuse without original-source authorization is refused. -/
theorem s18_exact_lookup_misses_occurrence : s18Table.lookup s18K2 = none := rfl

/-- A Goal-only scan for the first entry whose DECODED goal matches. -/
def S18Forest.findGoal (F : S18Forest) : (xs : List QueryKey) →
    Option (Expr Nat × Expr Nat) → Option (Fin xs.length)
  | [], _ => none
  | x :: xs, g =>
      if F.goalOf x = g then some ⟨0, Nat.zero_lt_succ _⟩
      else (F.findGoal xs g).map fun i => ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-- The weak lookup the control contrasts against: decoded Goal only. -/
def S18Forest.lookupGoal (F : S18Forest) (t : PrepaidTable Ans)
    (g : Option (Expr Nat × Expr Nat)) : Option (Fin t.entries.size) :=
  F.findGoal t.entries.toList g

/-- …while a Goal-only lookup WOULD hit — the wrong accept the exact key
    refuses. Endpoint equality is not authorization. -/
theorem s18_goal_only_lookup_would_hit :
    (s18Forest.lookupGoal s18Table (s18Forest.goalOf s18K2)).isSome = true :=
  rfl

/-- §4 control 2: same input position, a different `linst` map code —
    misses. -/
theorem s18_exact_lookup_misses_linst : s18Table.lookup s18K3 = none := rfl

/-- §4 control 3: same type/term but a replacement from another original
    occurrence — misses. -/
theorem s18_exact_lookup_misses_replacement : s18Table.lookup s18K4 = none := rfl

/-- Positive control: the stored key hits, and `prepaidUse` can serve the
    `k₁` answer purely by transport. -/
theorem s18_lookup_stored_hits :
    s18Table.lookup s18K1 = some ⟨0, Nat.zero_lt_succ _⟩ := rfl

/-- The transported answer IS the decoded PB certificate: `Ans k₁` is
    the real `CvP` type at `c.h`'s endpoints, not a numeric reflexive
    certificate. -/
theorem s18_prepaid_is_decoded_certificate :
    s18Forest.ans s18K1 =
      CvP emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  rfl

/-- `prepaidUse` serving the `k₁` answer: it typechecks as a REAL `CvP`
    at the decoded endpoints only because `lookup_exact` transports the
    stored `s18C` along the exact key equality. -/
def s18Prepaid :
    CvP emptyEnv 0 [] (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  s18Table.prepaidUse s18K1 s18_lookup_stored_hits

end Rcic.Syn

#print axioms Rcic.Syn.findKey_exact
#print axioms Rcic.Syn.PrepaidTable.lookup_exact
#print axioms Rcic.Syn.s18_prepaidUse_only_transports
#print axioms Rcic.Syn.s18_decode_input_is_c_h
#print axioms Rcic.Syn.s18_k1_k2_same_input
#print axioms Rcic.Syn.s18_decode_reg_is_c_h_reg
#print axioms Rcic.Syn.s18_k1_k2_same_reg
#print axioms Rcic.Syn.s18_k1_k2_same_goal
#print axioms Rcic.Syn.s18_k1_k2_same_ctx
#print axioms Rcic.Syn.s18_k1_k2_same_map
#print axioms Rcic.Syn.s18_k3_map_is_real_linst
#print axioms Rcic.Syn.s18_k3_map_agrees_on_goal
#print axioms Rcic.Syn.s18_k4_replacement_same_semantics
#print axioms Rcic.Syn.s18_k3_same_goal
#print axioms Rcic.Syn.s18_k4_same_goal
#print axioms Rcic.Syn.s18_h_dl_keys_differ
#print axioms Rcic.Syn.s18_exact_lookup_misses_occurrence
#print axioms Rcic.Syn.s18_goal_only_lookup_would_hit
#print axioms Rcic.Syn.s18_exact_lookup_misses_linst
#print axioms Rcic.Syn.s18_exact_lookup_misses_replacement
#print axioms Rcic.Syn.s18_lookup_stored_hits
#print axioms Rcic.Syn.s18_prepaid_is_decoded_certificate
