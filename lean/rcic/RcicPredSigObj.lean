/-
RCIC 07 §3/:78–96 — G1-S1: the contract predicate-signature objects
(`exprOfSig`/`spellOf`) over the canonical member order.

Ruling on #6652 (cc, five points): (1) shape (b) — flat `const`-members —
with the member-to-digest binding fixed by a CANONICAL member-order rule;
(2) `axiomM` for the predicate/type-object members (the typing clause binds
types only, `d:`/`o:` bodies stay unwired); (3) one checked group per
contract; (4) `SVP<r>` members as constants; (5) `Nat` enters as a
natEnvU-style inductive block — no `lit` anywhere.

THE CANONICAL ORDER (ruling 1). Member names are excluded from checked-group
identity (04 §5) and `axiomM` members carry no body, so nothing in the bytes
says which `sv_k : Sort 1` stands for which type digest — the binding must be
a fixed rule over canonical bytes. Within a contract's predicate group the
members are, in order:

  [ SV<d>  | d ∈ sortDedup {tin, tst, tout} ]       — axiomM, mtype = Sort 1
  [ SVP<r> | r ∈ sortDedup residues ]               — axiomM, mtype = Sort 1
  [ NatFam, NatZero, NatSucc, NatRec ]              — the Nat inductive block
  [ pre, returnGuard, returnPost ]                  — axiomM, signature mtypes
  [ residueGuard(r) | r ∈ sortDedup residues ]      — axiomM (slot order)
  [ residuePost(r)  | r ∈ sortDedup residues ]      — axiomM (slot order)
  [ bound ]                                         — axiomM

`exprOfSig`/`spellOf` compute member indices from this rule and the
contract's own digests; `memberEntries` lists the member VALUES in the same
order, so the in-group member index is the list index. S4 proves `spellOf`
injective on the `exprOfSig` image and that the binding is recovered from
the group and contract bytes alone.

Signature table (07:78–96; `SV x := .const (svIndexOf x) []`,
`SVP r := .const (svpIndexOf r) []`, `Nat := .const natFamIndex []`,
`Prop := .sort .zero`):

  pre, returnGuard, residueGuard(r) : SV tin → SV tst → Prop
  returnPost : SV tin → SV tst → SV tout → SV tst → Prop
  residuePost(r) : SV tin → SV tst → SVP r → Prop
  bound : SV tin → SV tst → Nat

`residueGuard(r)`'s type does NOT mention `r` (07:88–89: SV Input → SV State
→ Prop) — `r` selects WHICH member; the `mtype` is `pre`'s. `residuePost(r)`'s
third argument is the `SVP<r>` member's type.

Tokens: `svToken d := "SV<" ++ d ++ ">"`, `svpToken r := "SVP<" ++ r ++ ">"`,
`"Nat"`, `"Prop"`, plus per-slot member atoms for totality. The surface
grammar is this module's; agreement with `rcic.pred_sig_spell` (CT-001's
speller lane, ruled on #6580) is the S4 bridge's obligation.
-/
import rcic.RcicFixtures
import rcic.RcicScopeExactModel

namespace Rcic.PredSig
open Rcic.Declarative Rcic.ScopeExact

/-- The contract data the signature objects read — `Contract.tin/tst/tout`
(bound-type digests) and `Contract.row`/`cases`' residue ids, projected
(`ScmContract.Contract` stays unimported; the byte-level bridge is S4's). -/
structure ContractSigData where
  tin : String
  tst : String
  tout : String
  residues : List String
  deriving DecidableEq

/-- The six predicate slots (07:78–96). `residueGuard`/`residuePost` carry
the residue id they are the guard/post FOR — the contract admits one member
per (slot, residue) pair there. -/
inductive PredSlot : Type
  | pre | returnGuard | returnPost
  | residueGuard (r : String) | residuePost (r : String)
  | bound
  deriving DecidableEq

/-- The distinct bound-type digests, canonicalized (sorted, deduplicated —
`RcicScopeExactModel`'s `residue_rows` canon). -/
def ContractSigData.svDigests (cd : ContractSigData) : List String :=
  listCanon [cd.tin, cd.tst, cd.tout]

/-- The distinct residue ids, canonicalized. -/
def ContractSigData.resIds (cd : ContractSigData) : List String :=
  listCanon cd.residues

/-- Member counts of each layout block. -/
def svCount (cd : ContractSigData) : Nat := (cd.svDigests).length
def svpCount (cd : ContractSigData) : Nat := (cd.resIds).length

/-- Block bases in the canonical order. -/
def svpBase (cd : ContractSigData) : Nat := svCount cd
def natBase (cd : ContractSigData) : Nat := svpBase cd + svpCount cd
def predBase (cd : ContractSigData) : Nat := natBase cd + 4

/-- `SV<d>`'s member index — `d`'s position in the sorted distinct digests. -/
def svIndexOf (cd : ContractSigData) (d : String) : Nat :=
  (cd.svDigests).findIdx (· == d)

/-- `SVP<r>`'s member index — after the SV block, `r`'s position in the
sorted distinct residue ids. -/
def svpIndexOf (cd : ContractSigData) (r : String) : Nat :=
  svpBase cd + (cd.resIds).findIdx (· == r)

/-- The Nat block's member indices: fam, zero, succ, rec (natEnvU order). -/
def natFamIndex (cd : ContractSigData) : Nat := natBase cd
def natZeroIndex (cd : ContractSigData) : Nat := natBase cd + 1
def natSuccIndex (cd : ContractSigData) : Nat := natBase cd + 2
def natRecIndex (cd : ContractSigData) : Nat := natBase cd + 3

/-- A predicate slot's member index: slot order first (pre, returnGuard,
returnPost), then the two per-residue slots each sorted by residue id, then
`bound` last. For `r ∉ cd.residues` the `findIdx` fallback lands past the
block — a member index it does NOT denote (S4 premises `r ∈ cd.residues`). -/
def predIndex (cd : ContractSigData) : PredSlot → Nat
  | .pre => predBase cd
  | .returnGuard => predBase cd + 1
  | .returnPost => predBase cd + 2
  | .residueGuard r => predBase cd + 3 + (cd.resIds).findIdx (· == r)
  | .residuePost r =>
      predBase cd + 3 + svpCount cd + (cd.resIds).findIdx (· == r)
  | .bound => predBase cd + 3 + 2 * svpCount cd

/-- Total member count of the contract's predicate group. -/
def memberCount (cd : ContractSigData) : Nat := predIndex cd .bound + 1

/-- Token atoms. -/
def svToken (d : String) : String := "SV<" ++ d ++ ">"
def svpToken (r : String) : String := "SVP<" ++ r ++ ">"
def guardToken (r : String) : String := "residueGuard<" ++ r ++ ">"
def postToken (r : String) : String := "residuePost<" ++ r ++ ">"

/-- The denotation token of each member index — `const i`'s spelling. -/
def memberTokens (cd : ContractSigData) : List String :=
  (cd.svDigests).map svToken ++
  (cd.resIds).map svpToken ++
  ["Nat", "Nat.zero", "Nat.succ", "Nat.rec"] ++
  ["pre", "returnGuard", "returnPost"] ++
  (cd.resIds).map guardToken ++
  (cd.resIds).map postToken ++
  ["bound"]

/-- `memberTokens`' index view — `atomsOf cd i` is `const i`'s denotation. -/
def atomsOf (cd : ContractSigData) (i : Nat) : Option String :=
  (memberTokens cd)[i]?

/-- The `Expr` for `SV<d>` (an SV member reference). -/
def svExpr (cd : ContractSigData) (d : String) : Expr Nat :=
  .const (svIndexOf cd d) []

/-- The `Expr` for `SVP<r>` (an SVP member reference). -/
def svpExpr (cd : ContractSigData) (r : String) : Expr Nat :=
  .const (svpIndexOf cd r) []

/-- The `Expr` for `Nat` (the Nat-block family reference). -/
def natExpr (cd : ContractSigData) : Expr Nat := .const (natFamIndex cd) []

/-- The `Expr` for `Prop`. -/
def propExpr : Expr Nat := .sort .zero

/-- `A₁ → … → Aₙ → R` as a `pi`-telescope (non-dependent: codomains are
`bvar`-free in every signature here). -/
def arrowList (args : List (Expr Nat)) (ret : Expr Nat) : Expr Nat :=
  args.foldr Expr.pi ret

/-- `exprOfSig` — the signature `Expr` of a predicate slot, computed from
the canonical member order and the contract's own digests (07:78–96). -/
def exprOfSig (cd : ContractSigData) : PredSlot → Expr Nat
  | .pre | .returnGuard =>
      arrowList [svExpr cd cd.tin, svExpr cd cd.tst] propExpr
  | .residueGuard _ =>
      arrowList [svExpr cd cd.tin, svExpr cd cd.tst] propExpr
  | .returnPost =>
      arrowList
        [svExpr cd cd.tin, svExpr cd cd.tst,
         svExpr cd cd.tout, svExpr cd cd.tst] propExpr
  | .residuePost r =>
      arrowList
        [svExpr cd cd.tin, svExpr cd cd.tst, svpExpr cd r] propExpr
  | .bound =>
      arrowList [svExpr cd cd.tin, svExpr cd cd.tst] (natExpr cd)

/-- `spellOf` — the signature's surface token, reading `const i` through the
member denotation table and flattening `pi` telescopes (`SV<…>SV<…>Prop`).
`none` off the signature image (level-polymorphic consts, non-`Prop` sorts,
non-signature constructors). -/
def spellOf (atoms : Nat → Option String) : Expr Nat → Option String
  | .pi a b => do
      let sa ← spellOf atoms a
      let sb ← spellOf atoms b
      pure (sa ++ sb)
  | .const r [] => atoms r
  | .sort l => if l = .zero then some "Prop" else none
  | _ => none

/-- The SV/SVP type-object member: `axiomM`, arity 0, no body, type `Sort 1`
(`SemanticValue T` is a data type, not a proposition). -/
def typeObjectMember : CheckedMember := ⟨.axiomM, 0, .sort (.succ .zero), none⟩

/-- The Nat block at base `b` — the `natEnvU` member shapes with family
references shifted to the block's position (`RcicFixtures`' own members are
`const 0`-based and only fit base 0). -/
def natZeroMemberAt (b : Nat) : CheckedMember :=
  ⟨.constructorM, 0, .const b [], none⟩
def natSuccMemberAt (b : Nat) : CheckedMember :=
  ⟨.constructorM, 0, .pi (.const b []) (.const b []), none⟩

/-- `natRecTypeU` at family index `b` (ctor indices `b+1`, `b+2`). -/
def natRecTypeAt (b : Nat) : Expr Nat :=
  .pi (.pi (.const b []) (.sort (.param 0)))              -- P     : N → Sort u
   (.pi (.app (.bvar 0) (.const (b + 1) []))              -- mz    : P zero
    (.pi (.pi (.const b [])                               -- ms    : Π n : N,
          (.pi (.app (.bvar 2) (.bvar 0))                 --            Π ih : P n,
            (.app (.bvar 3) (.app (.const (b + 2) []) (.bvar 1)))))
     (.pi (.const b [])                                   -- major : N
      (.app (.bvar 3) (.bvar 0)))))                       -- body  : P major

def natRecMemberAt (b : Nat) : CheckedMember :=
  ⟨.recursorM, 1, natRecTypeAt b, none⟩

/-- A predicate member: `axiomM`, arity 0, no body, `mtype` = `exprOfSig`. -/
def predMember (cd : ContractSigData) (slot : PredSlot) : CheckedMember :=
  ⟨.axiomM, 0, exprOfSig cd slot, none⟩

/-- The contract group's member values in canonical order — list index IS the
in-group member index. -/
def memberEntries (cd : ContractSigData) : List CheckedMember :=
  List.replicate (svCount cd) typeObjectMember ++
  List.replicate (svpCount cd) typeObjectMember ++
  [ natFamMember, natZeroMemberAt (natBase cd),
    natSuccMemberAt (natBase cd), natRecMemberAt (natBase cd) ] ++
  [ predMember cd .pre, predMember cd .returnGuard, predMember cd .returnPost ] ++
  (cd.resIds).map (fun r => predMember cd (.residueGuard r)) ++
  (cd.resIds).map (fun r => predMember cd (.residuePost r)) ++
  [ predMember cd .bound ]

/-! ## Pins — a concrete contract (three distinct digests, one residue). -/

/-- `tin = "d0"`, `tst = "d1"`, `tout = "d2"` sort in listed order; one
residue `"r0"`. Layout: SVs at 0,1,2; `SVP<r0>` at 3; Nat block 4–7;
pre 8, rg 9, rp 10, guard(r0) 11, post(r0) 12, bound 13 — fourteen members. -/
def pinSigData : ContractSigData := ⟨"d0", "d1", "d2", ["r0"]⟩

theorem pin_svDigests : pinSigData.svDigests = ["d0", "d1", "d2"] := rfl
theorem pin_resIds : pinSigData.resIds = ["r0"] := rfl
theorem pin_memberCount : memberCount pinSigData = 14 := rfl

theorem pin_predIndex_pre : predIndex pinSigData .pre = 8 := rfl
theorem pin_predIndex_bound : predIndex pinSigData .bound = 13 := rfl
theorem pin_predIndex_guard :
    predIndex pinSigData (.residueGuard "r0") = 11 := rfl
theorem pin_predIndex_post :
    predIndex pinSigData (.residuePost "r0") = 12 := rfl

theorem pin_exprOfSig_pre :
    exprOfSig pinSigData .pre =
      .pi (.const 0 []) (.pi (.const 1 []) (.sort .zero)) := rfl

theorem pin_exprOfSig_returnPost :
    exprOfSig pinSigData .returnPost =
      .pi (.const 0 []) (.pi (.const 1 [])
        (.pi (.const 2 []) (.pi (.const 1 []) (.sort .zero)))) := rfl

theorem pin_exprOfSig_bound :
    exprOfSig pinSigData .bound =
      .pi (.const 0 []) (.pi (.const 1 []) (.const 4 [])) := rfl

theorem pin_exprOfSig_residuePost :
    exprOfSig pinSigData (.residuePost "r0") =
      .pi (.const 0 []) (.pi (.const 1 [])
        (.pi (.const 3 []) (.sort .zero))) := rfl

/-- `pre`, `returnGuard`, `residueGuard r` share one signature (07:88–89);
they are different MEMBERS, not different types. -/
theorem pin_exprOfSig_guard_eq_pre :
    exprOfSig pinSigData (.residueGuard "r0") = exprOfSig pinSigData .pre := rfl

theorem pin_spellOf_pre :
    spellOf (atomsOf pinSigData) (exprOfSig pinSigData .pre) =
      some "SV<d0>SV<d1>Prop" := rfl

theorem pin_spellOf_returnPost :
    spellOf (atomsOf pinSigData) (exprOfSig pinSigData .returnPost) =
      some "SV<d0>SV<d1>SV<d2>SV<d1>Prop" := rfl

theorem pin_spellOf_residuePost :
    spellOf (atomsOf pinSigData) (exprOfSig pinSigData (.residuePost "r0")) =
      some "SV<d0>SV<d1>SVP<r0>Prop" := rfl

theorem pin_spellOf_bound :
    spellOf (atomsOf pinSigData) (exprOfSig pinSigData .bound) =
      some "SV<d0>SV<d1>Nat" := rfl

theorem pin_memberEntries_len :
    (memberEntries pinSigData).length = memberCount pinSigData := rfl

end Rcic.PredSig
