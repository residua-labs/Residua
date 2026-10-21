/-
RCIC 07 §3/§18 — G2-S1 pins at the refined predicate environment
(`RcicG2Env`): one concrete contract whose subterm closure meets each of
`CoreTy`'s eight forms exactly once, its canonical layout, CT-001's typing
clause at every predicate slot, and — per form — a concrete `Val` that
`embedValAt` embeds as a constructor term which `HasTyT`-checks at that
form's `SV<d>` family in `pinG2.predEnv`.

The contract: `tin = record [x : str, y : bytes]`,
`tst = sum [list bool, pair bool i64]`, `tout = i64`, one residue `r0` whose
payload is `bool`; `dig = encTy` (the canonical wire bytes stand in for the
content hash — any injective digest gives the same order argument). Layout
(68 members):

```
SV<Lb>        0 fam  1 nil   2 cons   3 rec      list bool
SV<Pbi>       4 fam  5 mk    6 rec              pair bool i64
SV<R2;…>      7 fam  8 mk    9 rec              record [x:str, y:bytes]
SV<S2;…>     10 fam 11 inj0 12 inj1  13 rec      sum [list bool, pair bool i64]
SV<b>        14 fam 15 ff   16 tt    17 rec      bool
SV<i>        18 fam 19 mk   20 rec              i64
SV<s>        21 fam 22 snil 23 scons 24 rec      str
SV<y>        25 fam 26 bnil 27 bcons 28 rec      bytes
SVP<r0>      29 (alias of SV<b>)
Pos 30–34  BNat 35–38  Bool 39–42  True 43–45  False 46–47
And 48–50  Or 51–54  Eq 55–57
Nat 58–61
pre 62  returnGuard 63  returnPost 64  residueGuard<r0> 65
residuePost<r0> 66  bound 67
```

Pins run on `pinG2.predEnv` itself; `EnvWfT` admission of the blocks is a
separate obligation.
-/
import rcic.RcicG2Env
import rcic.RcicG2Pins
import rcic.ScmWire

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm Rcic.Scm.Wire Rcic.PredSig

def pinG2 : G2SigData where
  tin := .record [("x", .str), ("y", .bytes)]
  tst := .sum [.list .bool, .pair .bool .i64]
  tout := .i64
  residues := ["r0"]
  payloadTy := fun _ => .bool
  dig := encTy

/-! ## Layout -/

/-- The closure's eight digests in canonical (sorted) order — one per
    `CoreTy` form. -/
theorem pinG2_svKeys :
    pinG2.svKeys = ["Lb", "Pbi", "R2;1:xs1:yy", "S2;LbPbi", "b", "i", "s", "y"] := by
  decide

theorem pinG2_fam_list : pinG2.svFamOf (.list .bool) = 0 := by decide
theorem pinG2_fam_pair : pinG2.svFamOf (.pair .bool .i64) = 4 := by decide
theorem pinG2_fam_record : pinG2.svFamOf pinG2.tin = 7 := by decide
theorem pinG2_fam_sum : pinG2.svFamOf pinG2.tst = 10 := by decide
theorem pinG2_fam_bool : pinG2.svFamOf .bool = 14 := by decide
theorem pinG2_fam_i64 : pinG2.svFamOf .i64 = 18 := by decide
theorem pinG2_fam_str : pinG2.svFamOf .str = 21 := by decide
theorem pinG2_fam_bytes : pinG2.svFamOf .bytes = 25 := by decide

theorem pinG2_sup : pinG2.sup = ⟨30, 35, 39⟩ := rfl
theorem pinG2_natBase : pinG2.natBase = 58 := by decide
theorem pinG2_memberCount : pinG2.memberCount = 68 := by decide
theorem pinG2_memberEntries_length :
    pinG2.memberEntries.length = pinG2.memberCount := by decide

theorem pinG2_predIndex_pre : pinG2.predIndex .pre = 62 := by decide
theorem pinG2_predIndex_bound : pinG2.predIndex .bound = 67 := by decide

/-- `SVP<r0>` is a `definitionM` alias whose body is `SV<bool>`'s family. -/
theorem pinG2_svp :
    pinG2.predEnv.members 29 =
      some ⟨.definitionM, 0, .sort (.succ .zero), some (.const 14 [])⟩ := rfl

theorem pinG2_past_end : pinG2.predEnv.members 68 = none := rfl

/-! ## CT-001's typing clause at every slot -/

theorem pinG2_resIds : pinG2.resIds = ["r0"] := by decide

theorem pinG2_svpMem (r : String) (hr : r ∈ pinG2.resIds) :
    pinG2.predEnv.members (pinG2.svpIndexOf r) = some (pinG2.svpMember r) := by
  rw [pinG2_resIds, List.mem_singleton] at hr
  subst hr
  rfl

/-- Each predicate slot's member is stored at its refined index with its
    signature `mtype`, and that `mtype` is a `Sort u` type in the env. -/
def pinG2_member_typing (s : PredSlot) (hs : s.validFor pinG2.sig) :
    PProd (pinG2.predEnv.members (pinG2.predIndex s) = some (pinG2.predMember s))
      (Σ' u, HasTyT pinG2.predEnv 0 [] (pinG2.exprOfSig s) (.sort u)) := by
  refine ⟨?_, pinG2.predSlotTy rfl rfl rfl rfl pinG2_svpMem s hs⟩
  cases s with
  | pre | returnGuard | returnPost | bound => rfl
  | residueGuard r | residuePost r =>
      have hr : r ∈ pinG2.resIds := hs
      rw [pinG2_resIds, List.mem_singleton] at hr
      subst hr
      rfl

/-! ## Per-form embeddings, typed at the refined env

Each pin states the embedding (`embedValAt … = some e`) and the typing
`HasTyT pinG2.predEnv 0 [] e (pinG2.svExpr t)` — the family index is the
layout function's, not a literal. -/

theorem pinG2_fam_tin :
    pinG2.svFamOf (.record [("x", .str), ("y", .bytes)]) = 7 := by decide
theorem pinG2_fam_tst :
    pinG2.svFamOf (.sum [.list .bool, .pair .bool .i64]) = 10 := by decide

theorem pinG2_bnat : BNatPrereq pinG2.predEnv pinG2.sup := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The constructor members the pins apply, read off the env. -/
theorem g2m1 : pinG2.predEnv.members 1 = some ⟨.constructorM, 0, .const 0 [], none⟩ := rfl
theorem g2m2 : pinG2.predEnv.members 2 =
    some ⟨.constructorM, 0, .pi (.const 14 []) (.pi (.const 0 []) (.const 0 [])), none⟩ := rfl
theorem g2m5 : pinG2.predEnv.members 5 =
    some ⟨.constructorM, 0, .pi (.const 14 []) (.pi (.const 18 []) (.const 4 [])), none⟩ := rfl
theorem g2m8 : pinG2.predEnv.members 8 =
    some ⟨.constructorM, 0, .pi (.const 21 []) (.pi (.const 25 []) (.const 7 [])), none⟩ := rfl
theorem g2m12 : pinG2.predEnv.members 12 =
    some ⟨.constructorM, 0, .pi (.const 4 []) (.const 10 []), none⟩ := rfl
theorem g2m15 : pinG2.predEnv.members 15 = some ⟨.constructorM, 0, .const 14 [], none⟩ := rfl
theorem g2m16 : pinG2.predEnv.members 16 = some ⟨.constructorM, 0, .const 14 [], none⟩ := rfl
theorem g2m19 : pinG2.predEnv.members 19 =
    some ⟨.constructorM, 0, .pi (.const 35 []) (.const 18 []), none⟩ := rfl

/-- `const c` at its stored arity-0 constructor type. -/
abbrev g2c (c : Nat) {m : CheckedMember} (h : pinG2.predEnv.members c = some m)
    (ha : m.arity = 0) := const_ty pinG2.predEnv 0 [] c m h ha

/-- i64 — `.i (-1)` is `SV<i>.mk` over the `BNat` tower of `-1 + 2^63`. -/
def g2I64 : Expr Nat :=
  .app (.const 19 []) (bnatTerm pinG2.sup ((-1 : Int) + 2^63).toNat)

theorem g2_i64_embeds :
    embedValAt pinG2.sup pinG2.svFamOf .i64 (.i (-1)) = some g2I64 := by
  simp [embedValAt, i64Term, pinG2_fam_i64, g2I64]

def g2_i64_ty : HasTyT pinG2.predEnv 0 [] g2I64 (pinG2.svExpr .i64) :=
  .app _ _ _ _ _ (g2c 19 g2m19 rfl)
    (bnatTerm_ty _ 0 [] pinG2.sup _ pinG2_bnat.h0 pinG2_bnat.h1 pinG2_bnat.hone
      pinG2_bnat.hz pinG2_bnat.hp)

/-- bool — `.b 1` is `SV<b>.tt`. -/
theorem g2_bool_embeds :
    embedValAt pinG2.sup pinG2.svFamOf .bool (.b 1) = some (.const 16 []) := by
  simp [embedValAt, pinG2_fam_bool]

def g2_bool_ty : HasTyT pinG2.predEnv 0 [] (.const 16 []) (pinG2.svExpr .bool) :=
  g2c 16 g2m16 rfl

/-- str — `.s "ab"` is an `scons` tower over codepoint `BNat`s. -/
def g2Str : Expr Nat := strTerm pinG2.sup 22 23 "ab"

theorem g2_str_embeds :
    embedValAt pinG2.sup pinG2.svFamOf .str (.s "ab") = some g2Str := by
  simp [embedValAt, pinG2_fam_str, g2Str]

def g2_str_ty : HasTyT pinG2.predEnv 0 [] g2Str (pinG2.svExpr .str) :=
  strTerm_ty _ 0 [] pinG2.sup 22 23 21 "ab" pinG2_bnat rfl rfl

/-- bytes — `.y [0, 255]` is a `bcons` tower over byte-value `BNat`s. -/
def g2Bytes : Expr Nat :=
  consTower 26 27 [bnatTerm pinG2.sup 0, bnatTerm pinG2.sup 255]

theorem g2_bytes_embeds :
    embedValAt pinG2.sup pinG2.svFamOf .bytes (.y [0, 255]) = some g2Bytes := by
  simp [embedValAt, pinG2_fam_bytes, bytesTerm, g2Bytes]

def g2_bytes_ty : HasTyT pinG2.predEnv 0 [] g2Bytes (pinG2.svExpr .bytes) :=
  bytesTerm_ty _ 0 [] pinG2.sup 26 27 25 [0, 255] _ pinG2_bnat rfl rfl rfl

/-- list — `.l [.b 0, .b 1]` is `cons ff (cons tt nil)` at `SV<Lb>`. -/
def g2List : Expr Nat := consTower 1 2 [.const 15 [], .const 16 []]

theorem g2_list_embeds :
    embedValAt pinG2.sup pinG2.svFamOf (.list .bool) (.l [.b 0, .b 1]) =
      some g2List := by
  simp [embedValAt, pinG2_fam_list, pinG2_fam_bool, mapOpt, g2List]

def g2_list_ty : HasTyT pinG2.predEnv 0 [] g2List (pinG2.svExpr (.list .bool)) :=
  .app _ _ _ _ _ (.app _ _ _ _ _ (g2c 2 g2m2 rfl) (g2c 15 g2m15 rfl))
    (.app _ _ _ _ _ (.app _ _ _ _ _ (g2c 2 g2m2 rfl) (g2c 16 g2m16 rfl))
      (g2c 1 g2m1 rfl))

/-- pair — `.p (.b 1) (.i (-1))` is `SV<Pbi>.mk tt (mkI64 …)`. -/
def g2Pair : Expr Nat := .app (.app (.const 5 []) (.const 16 [])) g2I64

theorem g2_pair_embeds :
    embedValAt pinG2.sup pinG2.svFamOf (.pair .bool .i64) (.p (.b 1) (.i (-1))) =
      some g2Pair := by
  simp [embedValAt, i64Term, pinG2_fam_pair, pinG2_fam_bool, pinG2_fam_i64,
    g2Pair, g2I64]

def g2_pair_ty : HasTyT pinG2.predEnv 0 [] g2Pair (pinG2.svExpr (.pair .bool .i64)) :=
  .app _ _ _ _ _ (.app _ _ _ _ _ (g2c 5 g2m5 rfl) (g2c 16 g2m16 rfl)) g2_i64_ty

theorem pinG2_tst : pinG2.tst = .sum [.list .bool, .pair .bool .i64] := rfl
theorem pinG2_tin : pinG2.tin = .record [("x", .str), ("y", .bytes)] := rfl

/-- sum — `tst`'s second variant: `.j 1 (pair …)` is `inj₁` over the pair. -/
def g2Sum : Expr Nat := .app (.const 12 []) g2Pair

theorem g2_sum_embeds :
    embedValAt pinG2.sup pinG2.svFamOf (.sum [.list .bool, .pair .bool .i64])
      (.j 1 (.p (.b 1) (.i (-1)))) = some g2Sum := by
  simp [embedValAt, i64Term, pinG2_fam_tst, pinG2_fam_pair, pinG2_fam_bool,
    pinG2_fam_i64, g2Sum, g2Pair, g2I64]

def g2_sum_ty : HasTyT pinG2.predEnv 0 [] g2Sum (pinG2.svExpr pinG2.tst) :=
  .app _ _ _ _ _ (g2c 12 g2m12 rfl) g2_pair_ty

/-- record — `tin`: `.r [.s "ab", .y [0, 255]]` is `SV<R…>.mk` over the
    string and byte towers, positional in `fs` order. -/
def g2Record : Expr Nat := appsp 8 [g2Str, g2Bytes]

theorem g2_record_embeds :
    embedValAt pinG2.sup pinG2.svFamOf (.record [("x", .str), ("y", .bytes)])
      (.r [.s "ab", .y [0, 255]]) = some g2Record := by
  simp [embedValAt, pinG2_fam_tin, pinG2_fam_str, pinG2_fam_bytes, bytesTerm,
    mapOpt, g2Record, g2Str, g2Bytes]

def g2_record_ty : HasTyT pinG2.predEnv 0 [] g2Record (pinG2.svExpr pinG2.tin) :=
  .app _ _ _ _ _ (.app _ _ _ _ _ (g2c 8 g2m8 rfl) g2_str_ty) g2_bytes_ty

/-- A concrete value embeds at `t` as a literal-free constructor term that
    types at `SV<t>`'s family in the refined env. -/
def EmbedsAndTypes (g : G2SigData) (t : CoreTy) (v : Val) : Prop :=
  ∃ e, embedValAt g.sup g.svFamOf t v = some e ∧ hasLit e = false ∧
    Nonempty (HasTyT g.predEnv 0 [] e (g.svExpr t))

theorem g2I64_noLit : hasLit g2I64 = false := by
  rw [g2I64, hasLit_app, hasLit_const, bnatTerm_noLit]; rfl

theorem g2Pair_noLit : hasLit g2Pair = false := by
  rw [g2Pair, hasLit_app, hasLit_app, hasLit_const, hasLit_const, g2I64_noLit]; rfl

theorem g2Bytes_noLit : hasLit g2Bytes = false :=
  consTower_noLit 26 27 _ (fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact bnatTerm_noLit _ 0
    rcases List.mem_cons.mp he with rfl | he
    · exact bnatTerm_noLit _ 255
    exact absurd he (List.not_mem_nil _))

/-- **Every `CoreTy` form** (the pin contract's closure meets each once):
    a concrete value embeds, carries no `lit`, and type-checks at its
    `SV<d>` family in `pinG2.predEnv`. -/
theorem pinG2_all_forms :
    EmbedsAndTypes pinG2 .i64 (.i (-1)) ∧
    EmbedsAndTypes pinG2 .bool (.b 1) ∧
    EmbedsAndTypes pinG2 .str (.s "ab") ∧
    EmbedsAndTypes pinG2 .bytes (.y [0, 255]) ∧
    EmbedsAndTypes pinG2 (.list .bool) (.l [.b 0, .b 1]) ∧
    EmbedsAndTypes pinG2 (.pair .bool .i64) (.p (.b 1) (.i (-1))) ∧
    EmbedsAndTypes pinG2 pinG2.tst (.j 1 (.p (.b 1) (.i (-1)))) ∧
    EmbedsAndTypes pinG2 pinG2.tin (.r [.s "ab", .y [0, 255]]) :=
  ⟨⟨_, g2_i64_embeds, g2I64_noLit, ⟨g2_i64_ty⟩⟩,
   ⟨_, g2_bool_embeds, hasLit_const 16, ⟨g2_bool_ty⟩⟩,
   ⟨_, g2_str_embeds, strTerm_noLit _ 22 23 "ab", ⟨g2_str_ty⟩⟩,
   ⟨_, g2_bytes_embeds, g2Bytes_noLit, ⟨g2_bytes_ty⟩⟩,
   ⟨_, g2_list_embeds, consTower_noLit 1 2 _ (fun e he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact hasLit_const 15
      rcases List.mem_cons.mp he with rfl | he
      · exact hasLit_const 16
      exact absurd he (List.not_mem_nil _)), ⟨g2_list_ty⟩⟩,
   ⟨_, g2_pair_embeds, g2Pair_noLit, ⟨g2_pair_ty⟩⟩,
   ⟨_, g2_sum_embeds, by rw [g2Sum, hasLit_app, hasLit_const, g2Pair_noLit]; rfl,
      ⟨g2_sum_ty⟩⟩,
   ⟨_, g2_record_embeds, appsp_noLit 8 _ (fun e he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact strTerm_noLit _ 22 23 "ab"
      rcases List.mem_cons.mp he with rfl | he
      · exact g2Bytes_noLit
      exact absurd he (List.not_mem_nil _)), ⟨g2_record_ty⟩⟩⟩

/-- Refusal tooth: a value of the wrong shape does not embed (`toCore`'s
    shape check, pointwise) — `.b 2` is not a `bool`, and a 3-field record
    value is not `tin`. -/
theorem pinG2_refuses :
    embedValAt pinG2.sup pinG2.svFamOf .bool (.b 2) = none ∧
    embedValAt pinG2.sup pinG2.svFamOf pinG2.tin (.r [.s "a", .y [], .b 0]) = none := by
  constructor
  · simp [embedValAt]
  · simp [pinG2_tin, embedValAt]

end Rcic.G2
