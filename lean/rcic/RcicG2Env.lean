/-
RCIC 07 §3 — G2-S1: the refined predicate environment. G1's canonical member
order (`RcicPredSigObj`) with each `SV<d>` slot expanded in place to its
inductive block, `SVP<r>` as a `definitionM` alias (ruling 1 on #6697), and
the support blocks (`RcicG2Objects`) between the SVP segment and the Nat
block:

  [ SV<d> block | d ∈ sortDedup (dig ∘ subterm closure) ]  — fam, ctors…, rec
  [ SVP<r>      | r ∈ sortDedup residues ]                 — definitionM alias
  [ Pos BNat Bool True False And Or Eq ]                   — support (28)
  [ NatFam, NatZero, NatSucc, NatRec ]                     — G1's Nat block
  [ pre, returnGuard, returnPost, residueGuard…, residuePost…, bound ]

The ordering RULE is G1's (sorted dedup digests → sorted residue ids → Nat →
predicates); the digest set is the transitive `CoreTy`-subterm closure of
`{tin, tst, tout}` and the residue payload types (S0_G2 §1, forced: an
`SV<d>` constructor's fields name other `SV<…>` families). Every member's
`mtype` is G1's: SV/SVP members `Sort 1`, Nat members G1's, predicate members
`exprOfSig` with each `const` at the refined index.

Index order is not admission order: `SV<i64>`/`SV<str>`/`SV<bytes>` fields
name `BNat`, so the support blocks admit first. `EnvWfT` admits at any fresh
index, so the two orders are independent.

`dig` is the bound-type digest (in production the content hash of `encTy t`);
it is a parameter here, as G1 takes digests as opaque strings. G1 files are
not edited — this module only reads them. Predicate members stay `axiomM`
here; their compiled `AssertProp` bodies are G2-S2.
-/
import rcic.RcicG2Objects
import rcic.RcicPredEnvObj

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm Rcic.PredSig Rcic.ScopeExact

/-! ## The subterm closure -/

mutual
/-- `t` and every `CoreTy` subterm of `t`, preorder. -/
def subtermsOf : CoreTy → List CoreTy
  | .i64 => [.i64]
  | .bool => [.bool]
  | .str => [.str]
  | .bytes => [.bytes]
  | .list t => .list t :: subtermsOf t
  | .pair a b => .pair a b :: (subtermsOf a ++ subtermsOf b)
  | .sum ts => .sum ts :: subtermsOfList ts
  | .record fs => .record fs :: subtermsOfFields fs
def subtermsOfList : List CoreTy → List CoreTy
  | [] => []
  | t :: ts => subtermsOf t ++ subtermsOfList ts
def subtermsOfFields : List (String × CoreTy) → List CoreTy
  | [] => []
  | (_, t) :: fs => subtermsOf t ++ subtermsOfFields fs
end

/-- G2's contract data: G1's projection (`sig`) refined by the bound
    `CoreTy`s, the residue payload types, and the digest map. -/
structure G2SigData where
  tin : CoreTy
  tst : CoreTy
  tout : CoreTy
  residues : List String
  payloadTy : String → CoreTy
  dig : CoreTy → String

namespace G2SigData

/-- The G1 contract data this G2 data refines. -/
def sig (g : G2SigData) : ContractSigData :=
  ⟨g.dig g.tin, g.dig g.tst, g.dig g.tout, g.residues⟩

def resIds (g : G2SigData) : List String := listCanon g.residues

theorem resIds_eq_sig (g : G2SigData) : g.resIds = g.sig.resIds := rfl

/-- The closure roots: the three bound types and every residue payload. -/
def roots (g : G2SigData) : List CoreTy :=
  [g.tin, g.tst, g.tout] ++ g.resIds.map g.payloadTy

/-- The transitive subterm closure of the roots (with repeats). -/
def closure (g : G2SigData) : List CoreTy := subtermsOfList g.roots

/-- The SV segment's keys: the closure's digests, sorted and deduplicated —
    G1's `svDigests` rule over the refined set. -/
def svKeys (g : G2SigData) : List String := listCanon (g.closure.map g.dig)

/-- The `CoreTy` a key decodes to (the first closure member with that
    digest; `dig` injective on the closure makes it unique). -/
def tyOfKey (g : G2SigData) (d : String) : CoreTy :=
  (g.closure.find? (fun t => g.dig t == d)).getD .i64

end G2SigData

/-! ## Block sizes and the index layout -/

/-- Constructor count of `SV<t>`'s block — `(svCtors …).length`. -/
def ctorCount : CoreTy → Nat
  | .sum ts => ts.length
  | .bool | .str | .bytes | .list _ => 2
  | _ => 1

theorem svCtors_length (sup : SupRefs) (refOf : CoreTy → Nat) (fam : Nat) :
    ∀ t, (svCtors sup refOf fam t).length = ctorCount t
  | .i64 | .bool | .str | .bytes | .list _ | .pair _ _ | .record _ => rfl
  | .sum ts => by simp [svCtors, ctorCount]

/-- `SV<t>`'s block size: family + constructors + recursor. -/
def blockSize (t : CoreTy) : Nat := 2 + ctorCount t

theorem svMembersAt_length (sup : SupRefs) (refOf : CoreTy → Nat) (b : Nat)
    (t : CoreTy) : (svMembersAt sup refOf b t).length = blockSize t := by
  simp [svMembersAt, blockSize, svCtors_length]
  omega

/-- The support segment's size (`Pos` 5, `BNat` 4, `Bool` 4, `True` 3,
    `False` 2, `And` 3, `Or` 4, `Eq` 3). -/
def supportSize : Nat := 28

/-- The support blocks at base `b`, contiguous, in the order listed. -/
def supportMembersAt (b : Nat) : List (Nat × CheckedMember) :=
  posMembersAt b ++ bnatMembersAt (b + 5) b ++ boolMembersAt (b + 9) ++
  trueMembersAt (b + 13) ++ falseMembersAt (b + 16) ++ andMembersAt (b + 18) ++
  orMembersAt (b + 21) ++ eqMembersAt (b + 25)

theorem supportMembersAt_length (b : Nat) :
    (supportMembersAt b).length = supportSize := rfl

namespace G2SigData

/-- Size of the block at key `d`. -/
def keySize (g : G2SigData) (d : String) : Nat := blockSize (g.tyOfKey d)

/-- `SV<d>`'s family index: the sizes of every block whose key sorts
    before `d`. -/
def svFamAt (g : G2SigData) (d : String) : Nat :=
  ((g.svKeys.take (g.svKeys.findIdx (· == d))).map g.keySize).sum

/-- `SV<t>`'s family index, through its digest. -/
def svFamOf (g : G2SigData) (t : CoreTy) : Nat := g.svFamAt (g.dig t)

def svSegLen (g : G2SigData) : Nat := (g.svKeys.map g.keySize).sum
def svpBase (g : G2SigData) : Nat := g.svSegLen
def svpCount (g : G2SigData) : Nat := g.resIds.length
def svpIndexOf (g : G2SigData) (r : String) : Nat :=
  g.svpBase + g.resIds.findIdx (· == r)
def supBase (g : G2SigData) : Nat := g.svpBase + g.svpCount
def natBase (g : G2SigData) : Nat := g.supBase + supportSize
def predBase (g : G2SigData) : Nat := g.natBase + 4

/-- The support-block family bases `RcicG2Objects`' builders read. -/
def sup (g : G2SigData) : SupRefs := ⟨g.supBase, g.supBase + 5, g.supBase + 9⟩

/-- G1's `predIndex` formula at the refined `predBase`. -/
def predIndex (g : G2SigData) : PredSlot → Nat
  | .pre => g.predBase
  | .returnGuard => g.predBase + 1
  | .returnPost => g.predBase + 2
  | .residueGuard r => g.predBase + 3 + g.resIds.findIdx (· == r)
  | .residuePost r => g.predBase + 3 + g.svpCount + g.resIds.findIdx (· == r)
  | .bound => g.predBase + 3 + 2 * g.svpCount

def memberCount (g : G2SigData) : Nat := g.predIndex .bound + 1

/-! ## Signatures at the refined indices -/

def svExpr (g : G2SigData) (t : CoreTy) : Expr Nat := .const (g.svFamOf t) []
def svpExpr (g : G2SigData) (r : String) : Expr Nat := .const (g.svpIndexOf r) []
def natExpr (g : G2SigData) : Expr Nat := .const g.natBase []

/-- G1's `exprOfSig` table (07:78–96), each `const` at the refined index. -/
def exprOfSig (g : G2SigData) : PredSlot → Expr Nat
  | .pre | .returnGuard =>
      arrowList [g.svExpr g.tin, g.svExpr g.tst] propExpr
  | .residueGuard _ =>
      arrowList [g.svExpr g.tin, g.svExpr g.tst] propExpr
  | .returnPost =>
      arrowList
        [g.svExpr g.tin, g.svExpr g.tst, g.svExpr g.tout, g.svExpr g.tst] propExpr
  | .residuePost r =>
      arrowList [g.svExpr g.tin, g.svExpr g.tst, g.svpExpr r] propExpr
  | .bound =>
      arrowList [g.svExpr g.tin, g.svExpr g.tst] g.natExpr

/-! ## The member table -/

/-- `SV<d>`'s block at its family index. -/
def svBlock (g : G2SigData) (d : String) : List (Nat × CheckedMember) :=
  svMembersAt g.sup g.svFamOf (g.svFamAt d) (g.tyOfKey d)

/-- The SV segment: every key's block, in key order. -/
def svSegEntries (g : G2SigData) : List CheckedMember :=
  g.svKeys.flatMap fun d => (g.svBlock d).map Prod.snd

/-- `SVP<r>`: a `definitionM` alias to `SV<payload r>`'s family (ruling 1),
    `mtype` G1's `Sort 1`. -/
def svpMember (g : G2SigData) (r : String) : CheckedMember :=
  (svAliasMemberAt (g.svpIndexOf r) (g.svFamOf (g.payloadTy r))).2

def svpEntries (g : G2SigData) : List CheckedMember := g.resIds.map g.svpMember

def natEntries (g : G2SigData) : List CheckedMember :=
  [ natFamMember, natZeroMemberAt g.natBase, natSuccMemberAt g.natBase,
    natRecMemberAt g.natBase ]

/-- A predicate member — `axiomM` with G1's signature `mtype`; the compiled
    body is G2-S2's. -/
def predMember (g : G2SigData) (s : PredSlot) : CheckedMember :=
  ⟨.axiomM, 0, g.exprOfSig s, none⟩

def predEntries (g : G2SigData) : List CheckedMember :=
  [ g.predMember .pre, g.predMember .returnGuard, g.predMember .returnPost ] ++
  g.resIds.map (fun r => g.predMember (.residueGuard r)) ++
  g.resIds.map (fun r => g.predMember (.residuePost r)) ++
  [ g.predMember .bound ]

/-- The contract group's members in canonical order — list index IS the
    in-group member index. -/
def memberEntries (g : G2SigData) : List CheckedMember :=
  g.svSegEntries ++ g.svpEntries ++ (supportMembersAt g.supBase).map Prod.snd ++
  g.natEntries ++ g.predEntries

/-- The refined predicate environment. -/
def predEnv (g : G2SigData) : ResolvedEnv where
  members := fun i => (g.memberEntries)[i]?

end G2SigData

/-! ## CT-001's typing clause at the refined indices -/

/-- Every `SV<d>` family member (`svMembersAt`'s head). -/
def svFamMember : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩

/-- `const r : Sort 1` for an arity-0 member stored at `Sort 1` — an
    `SV<…>` family or an `SVP<…>` alias alike. -/
def sortOneConstTy (E : ResolvedEnv) {n : Nat} {Γ : LCtx} {r : Nat}
    {m : CheckedMember} (h : E.members r = some m) (ha : m.arity = 0)
    (ht : m.mtype = .sort (.succ .zero)) :
    HasTyT E n Γ (.const r []) (.sort (.succ .zero)) := by
  have h' := const_ty E n Γ r m h ha
  rw [ht] at h'
  exact h'

namespace G2SigData

/-- Each signature types at `Sort 1` in any env carrying the `SV<…>`
    families of `tin`/`tst`/`tout`, the `SVP<r>` aliases, and the Nat
    family — G1's `predSlotTy` with inductive families in the SV slots. -/
def predSlotTy (g : G2SigData) {E : ResolvedEnv}
    (htin : E.members (g.svFamOf g.tin) = some svFamMember)
    (htst : E.members (g.svFamOf g.tst) = some svFamMember)
    (htout : E.members (g.svFamOf g.tout) = some svFamMember)
    (hnat : E.members g.natBase = some natFamMember)
    (hsvp : ∀ r : String, r ∈ g.resIds →
      E.members (g.svpIndexOf r) = some (g.svpMember r))
    (s : PredSlot) (hs : s.validFor g.sig) :
    Σ' u, HasTyT E 0 [] (g.exprOfSig s) (.sort u) := by
  have sv : ∀ {Γ : LCtx} (t : CoreTy),
      E.members (g.svFamOf t) = some svFamMember →
      HasTyT E 0 Γ (g.svExpr t) (.sort (.succ .zero)) :=
    fun t h => sortOneConstTy E h rfl rfl
  have pr : ∀ {Γ : LCtx}, HasTyT E 0 Γ propExpr (.sort (.succ .zero)) :=
    .sort _ .zero
  cases s with
  | pre | returnGuard | residueGuard _ =>
      exact ⟨_, .pi [] _ _ _ _ (sv _ htin) (.pi _ _ _ _ _ (sv _ htst) pr)⟩
  | returnPost =>
      exact ⟨_, .pi [] _ _ _ _ (sv _ htin) (.pi _ _ _ _ _ (sv _ htst)
        (.pi _ _ _ _ _ (sv _ htout) (.pi _ _ _ _ _ (sv _ htst) pr)))⟩
  | residuePost r =>
      exact ⟨_, .pi [] _ _ _ _ (sv _ htin) (.pi _ _ _ _ _ (sv _ htst)
        (.pi _ _ _ _ _ (sortOneConstTy E (hsvp r hs) rfl rfl) pr))⟩
  | bound =>
      exact ⟨_, .pi [] _ _ _ _ (sv _ htin) (.pi _ _ _ _ _ (sv _ htst)
        (sortOneConstTy E hnat rfl rfl))⟩

end G2SigData

end Rcic.G2
