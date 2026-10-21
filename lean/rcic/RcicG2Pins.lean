/-
RCIC 07 §3/§18 — G2-S1 pins: a concrete support+SV environment and, for
each of `CoreTy`'s eight forms, a concrete `Val` that `embedValAt`
embeds and `HasTyT` type-checks at the corresponding `SV<d>` family.

Pin layout (contiguous member indices, `EnvWfT.group` order per block):

```
Pos                    0 fam   1 one    2 bit0   3 bit1   4 rec
BNat                   5 fam   6 zero   7 pos    8 rec
Bool                   9 fam  10 false 11 true  12 rec
True                  13 fam  14 tt    15 rec
False                 16 fam  17 rec
And                   18 fam  19 intro 20 rec
Or                    21 fam  22 inl   23 inr   24 rec
Eq                    25 fam  26 refl  27 rec
SV<i64>               28 fam  29 mk    30 rec
SV<bool>              31 fam  32 ff    33 tt    34 rec
SV<str>               35 fam  36 snil  37 scons 38 rec
SV<bytes>             39 fam  40 bnil  41 bcons 42 rec
SV<list bool>         43 fam  44 nil   45 cons  46 rec
SV<pair bool i64>     47 fam  48 mk    49 rec
SV<sum [bool,i64]>    50 fam  51 inj0  52 inj1  53 rec
SV<record x:bool y:i64> 54 fam 55 mk   56 rec
```

The `SV` digest set is the transitive `CoreTy`-subterm closure (S0_G2
§1): every subterm named inside a ctor field — `bool`/`i64` under
`list`/`pair`/`sum`/`record` — has its own `SV<…>` block in this env.

Pins run on the raw `ResolvedEnv` — `HasTyT.const` needs member
resolution only, not `EnvWfT` (the group-admission half is G2-S3).
Every pin is `no lit` — checked per term by `hasLit` (ruling: the
scm runtime refuses literals; the `.lit` surface is also the batch-21
aliasing hole).
-/
import rcic.RcicG2Objects

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm

/-- Does `e` contain a `.lit` node anywhere? The ruling's prohibition,
    made checkable. -/
def hasLit {R : Type} : Expr R → Bool
  | .lit _ => true
  | .app f x => hasLit f || hasLit x
  | .lam a b => hasLit a || hasLit b
  | .pi a b => hasLit a || hasLit b
  | .letE a v b => hasLit a || hasLit v || hasLit b
  | _ => false

/-! ## `hasLit` compositional lemmas

    `posBits` is well-founded (`termination_by n`), so `hasLit` never
    kernel-reduces on a `BNat` tower — and `simp` on the equation lemmas
    hits the `Acc`-certificate depth for `n + 2^63`-scale inputs. The
    teeth are proven compositionally instead: every builder is
    literal-free by construction. -/

theorem posTermAux_noLit (sup : SupRefs) :
    ∀ (bs : List Bool) (e : Expr Nat), hasLit e = false →
      hasLit (posTermAux sup e bs) = false
  | [], _, he => he
  | _ :: bs, e, he => posTermAux_noLit sup bs _ (by simp [hasLit, he])

theorem posTerm_noLit (sup : SupRefs) (n : Nat) :
    hasLit (posTerm sup n) = false :=
  posTermAux_noLit sup _ _ rfl

theorem bnatTerm_noLit (sup : SupRefs) (n : Nat) :
    hasLit (bnatTerm sup n) = false := by
  unfold bnatTerm; split
  · rfl
  · simp [hasLit, posTerm_noLit]

theorem consTower_noLit (nilIdx cIdx : Nat) :
    ∀ (es : List (Expr Nat)), (∀ e ∈ es, hasLit e = false) →
      hasLit (consTower nilIdx cIdx es) = false
  | [], _ => rfl
  | e :: es, h => by
      show hasLit (.app (.app (.const cIdx []) e)
        (consTower nilIdx cIdx es)) = false
      simp [hasLit, h e (List.mem_cons_self _ _),
        consTower_noLit nilIdx cIdx es
          (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem foldl_app_noLit {acc : Expr Nat} (hacc : hasLit acc = false) :
    ∀ (xs : List (Expr Nat)), (∀ e ∈ xs, hasLit e = false) →
      hasLit (xs.foldl Expr.app acc) = false
  | [], _ => hacc
  | e :: es, h =>
      foldl_app_noLit (by simp [hasLit, hacc, h e (List.mem_cons_self _ _)]) es
        (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem appsp_noLit (c : Nat) (xs : List (Expr Nat))
    (h : ∀ e ∈ xs, hasLit e = false) : hasLit (appsp c xs) = false :=
  foldl_app_noLit (acc := .const c []) rfl xs h

theorem strTerm_noLit (sup : SupRefs) (snil scons : Nat) (s : String) :
    hasLit (strTerm sup snil scons s) = false := by
  apply consTower_noLit
  intro e he
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp he
  exact bnatTerm_noLit sup c.toNat

/-! ## The concrete environment -/

/-- Support-block family bases: `Pos` at 0, `BNat` at 5, `Bool` at 9. -/
def pinSup : SupRefs := ⟨0, 5, 9⟩

/-- `SV<d>` family index per `CoreTy` in the pin set — the subterm
    closure of the pin types. Out-of-set types map to 0 (unreferenced by
    every pin term — `embedValAt` only consults `refOf` at members of
    the closure). -/
def pinRefOf : CoreTy → Nat
  | .i64 => 28
  | .bool => 31
  | .str => 35
  | .bytes => 39
  | .list .bool => 43
  | .pair .bool .i64 => 47
  | .sum [.bool, .i64] => 50
  | .record [(_, .bool), (_, .i64)] => 54
  | _ => 0

/-- The pin member table — support blocks then the eight `SV<d>` groups,
    in index order. -/
def pinMembers : List CheckedMember :=
  (posMembersAt 0).map Prod.snd ++
  (bnatMembersAt 5 0).map Prod.snd ++
  (boolMembersAt 9).map Prod.snd ++
  (trueMembersAt 13).map Prod.snd ++
  (falseMembersAt 16).map Prod.snd ++
  (andMembersAt 18).map Prod.snd ++
  (orMembersAt 21).map Prod.snd ++
  (eqMembersAt 25).map Prod.snd ++
  (svMembersAt pinSup pinRefOf 28 .i64).map Prod.snd ++
  (svMembersAt pinSup pinRefOf 31 .bool).map Prod.snd ++
  (svMembersAt pinSup pinRefOf 35 .str).map Prod.snd ++
  (svMembersAt pinSup pinRefOf 39 .bytes).map Prod.snd ++
  (svMembersAt pinSup pinRefOf 43 (.list .bool)).map Prod.snd ++
  (svMembersAt pinSup pinRefOf 47 (.pair .bool .i64)).map Prod.snd ++
  (svMembersAt pinSup pinRefOf 50 (.sum [.bool, .i64])).map Prod.snd ++
  (svMembersAt pinSup pinRefOf 54
    (.record [("x", .bool), ("y", .i64)])).map Prod.snd

/-- The raw resolved env — member `i` is `pinMembers[i]?`. -/
def pinEnv : ResolvedEnv := ⟨fun i => pinMembers[i]?⟩

/-- The support-block premise pack, discharged by index lookups. -/
theorem pinSup_ok : BNatPrereq pinEnv pinSup :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Per-form pins -/

/-- i64 — `.i (-1)` embeds at offset `-1 + 2^63` as a `BNat` tower under
    `SV<i64>.mk`, and types at `SV<i64>` (member 28). -/
def pinI64Term : Expr Nat :=
  .app (.const 29 []) (bnatTerm pinSup ((-1 : Int) + 2^63).toNat)

theorem pin_i64_embeds :
    embedValAt pinSup pinRefOf .i64 (.i (-1)) = some pinI64Term := by
  simp [embedValAt, pinRefOf, i64Term, pinI64Term]

def pin_i64_ty : HasTyT pinEnv 0 [] pinI64Term (.const 28 []) :=
  .app _ _ _ _ _ (const_ty pinEnv 0 [] 29 _ rfl rfl)
    (bnatTerm_ty pinEnv 0 [] pinSup _ pinSup_ok.h0 pinSup_ok.h1
      pinSup_ok.hone pinSup_ok.hz pinSup_ok.hp)

/-- bool — `.b 1` embeds to `SV<bool>.tt` (member 33). -/
theorem pin_bool_embeds :
    embedValAt pinSup pinRefOf .bool (.b 1) = some (.const 33 []) := by
  simp [embedValAt, pinRefOf]

def pin_bool_ty : HasTyT pinEnv 0 [] (.const 33 []) (.const 31 []) :=
  const_ty pinEnv 0 [] 33 _ rfl rfl

/-- str — `.s "ab"` embeds as `scons 97 (scons 98 snil)` over codepoint
    `BNat`s, and types at `SV<str>` (member 35). -/
theorem pin_str_embeds :
    embedValAt pinSup pinRefOf .str (.s "ab") =
      some (strTerm pinSup 36 37 "ab") := by
  simp [embedValAt, pinRefOf]

def pin_str_ty :
    HasTyT pinEnv 0 [] (strTerm pinSup 36 37 "ab") (.const 35 []) :=
  strTerm_ty pinEnv 0 [] pinSup 36 37 35 "ab" pinSup_ok rfl rfl

/-- bytes — `.y [0, 255]` embeds as `bcons 0 (bcons 255 bnil)` and types
    at `SV<bytes>` (member 39). -/
theorem pin_bytes_embeds :
    embedValAt pinSup pinRefOf .bytes (.y [0, 255]) =
      some (consTower 40 41
        [bnatTerm pinSup 0, bnatTerm pinSup 255]) := by
  simp [embedValAt, pinRefOf, bytesTerm]

def pin_bytes_ty :
    HasTyT pinEnv 0 []
      (consTower 40 41 [bnatTerm pinSup 0, bnatTerm pinSup 255])
      (.const 39 []) :=
  bytesTerm_ty pinEnv 0 [] pinSup 40 41 39 [0, 255] _ pinSup_ok rfl rfl rfl

/-- list — `.l [.b 0, .b 1]` embeds as `cons ff (cons tt nil)` at
    `SV<list bool>` (member 43). -/
theorem pin_list_embeds :
    embedValAt pinSup pinRefOf (.list .bool) (.l [.b 0, .b 1]) =
      some (consTower 44 45 [.const 32 [], .const 33 []]) := by
  simp [embedValAt, pinRefOf, mapOpt]

def pin_list_ty :
    HasTyT pinEnv 0 [] (consTower 44 45 [.const 32 [], .const 33 []])
      (.const 43 []) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (const_ty pinEnv 0 [] 45 _ rfl rfl)
      (const_ty pinEnv 0 [] 32 _ rfl rfl))
    (.app _ _ _ _ _
      (.app _ _ _ _ _ (const_ty pinEnv 0 [] 45 _ rfl rfl)
        (const_ty pinEnv 0 [] 33 _ rfl rfl))
      (const_ty pinEnv 0 [] 44 _ rfl rfl))

/-- pair — `.p (.b 1) (.i (-1))` embeds as `mk tt (mkI64 …)` at
    `SV<pair bool i64>` (member 47). -/
def pinPairTerm : Expr Nat :=
  .app (.app (.const 48 []) (.const 33 [])) pinI64Term

theorem pin_pair_embeds :
    embedValAt pinSup pinRefOf (.pair .bool .i64) (.p (.b 1) (.i (-1))) =
      some pinPairTerm := by
  simp [embedValAt, pinRefOf, i64Term, pinI64Term, pinPairTerm]

def pin_pair_ty : HasTyT pinEnv 0 [] pinPairTerm (.const 47 []) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (const_ty pinEnv 0 [] 48 _ rfl rfl)
      (const_ty pinEnv 0 [] 33 _ rfl rfl))
    pin_i64_ty

/-- sum — `.j 1 (.i (-1))` embeds under `inj₁` (member 52, the i64
    variant of `sum [bool, i64]`) at `SV<sum [bool,i64]>` (member 50). -/
theorem pin_sum_embeds :
    embedValAt pinSup pinRefOf (.sum [.bool, .i64]) (.j 1 (.i (-1))) =
      some (.app (.const 52 []) pinI64Term) := by
  simp [embedValAt, pinRefOf, i64Term, pinI64Term]

def pin_sum_ty :
    HasTyT pinEnv 0 [] (.app (.const 52 []) pinI64Term) (.const 50 []) :=
  .app _ _ _ _ _ (const_ty pinEnv 0 [] 52 _ rfl rfl) pin_i64_ty

/-- record — `.r [.b 1, .i (-1)]` embeds as `mk tt (mkI64 …)` at
    `SV<record x:bool y:i64>` (member 54), fields positional in `fs`
    order (toCore's `toCoreVals (fs.map Prod.snd) xs`, `ScmCore:250`). -/
theorem pin_record_embeds :
    embedValAt pinSup pinRefOf (.record [("x", .bool), ("y", .i64)])
        (.r [.b 1, .i (-1)]) =
      some (appsp 55 [.const 33 [], pinI64Term]) := by
  simp [embedValAt, pinRefOf, i64Term, pinI64Term, mapOpt]

def pin_record_ty :
    HasTyT pinEnv 0 [] (appsp 55 [.const 33 [], pinI64Term]) (.const 54 []) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (const_ty pinEnv 0 [] 55 _ rfl rfl)
      (const_ty pinEnv 0 [] 33 _ rfl rfl))
    pin_i64_ty

/-! ## `no lit` teeth -/

/-- `hasLit` of an application, as a rewrite — the teeth never unfold
    `hasLit` on a `BNat` tower by evaluation (the kernel would chase
    `posBits`' `Acc` certificate at `2^63` scale). -/
theorem hasLit_app (f x : Expr Nat) :
    hasLit (.app f x) = (hasLit f || hasLit x) := by
  simp only [hasLit]

theorem hasLit_const (c : Nat) : hasLit (.const c [] : Expr Nat) = false := by
  simp only [hasLit]

theorem pinI64Term_noLit : hasLit pinI64Term = false := by
  rw [pinI64Term, hasLit_app, hasLit_const, bnatTerm_noLit]; rfl

theorem pinPairTerm_noLit : hasLit pinPairTerm = false := by
  rw [pinPairTerm, hasLit_app, hasLit_app, hasLit_const, hasLit_const,
    pinI64Term_noLit]; rfl

theorem pinSumTerm_noLit :
    hasLit (.app (.const 52 []) pinI64Term) = false := by
  rw [hasLit_app, hasLit_const, pinI64Term_noLit]; rfl

theorem pinRecordTerm_noLit :
    hasLit (appsp 55 [.const 33 [], pinI64Term]) = false :=
  appsp_noLit 55 _ (fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact hasLit_const 33
    rcases List.mem_cons.mp he with rfl | he
    · exact pinI64Term_noLit
    exact absurd he (List.not_mem_nil _))

theorem pinBytesTerm_noLit :
    hasLit (consTower 40 41 [bnatTerm pinSup 0, bnatTerm pinSup 255]) = false :=
  consTower_noLit 40 41 _ (fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact bnatTerm_noLit pinSup 0
    rcases List.mem_cons.mp he with rfl | he
    · exact bnatTerm_noLit pinSup 255
    exact absurd he (List.not_mem_nil _))

theorem pinListTerm_noLit :
    hasLit (consTower 44 45 [.const 32 [], .const 33 []]) = false :=
  consTower_noLit 44 45 _ (fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact hasLit_const 32
    rcases List.mem_cons.mp he with rfl | he
    · exact hasLit_const 33
    exact absurd he (List.not_mem_nil _))

/-- Every pin term is literal-free (the ruling's prohibition, checked
    per term). -/
theorem pins_no_lit :
    hasLit pinI64Term = false ∧ hasLit (.const 33 [] : Expr Nat) = false ∧
    hasLit (strTerm pinSup 36 37 "ab") = false ∧
    hasLit (consTower 40 41 [bnatTerm pinSup 0, bnatTerm pinSup 255]) = false ∧
    hasLit (consTower 44 45 [.const 32 [], .const 33 []]) = false ∧
    hasLit pinPairTerm = false ∧
    hasLit (.app (.const 52 []) pinI64Term) = false ∧
    hasLit (appsp 55 [.const 33 [], pinI64Term]) = false :=
  ⟨pinI64Term_noLit, hasLit_const 33, strTerm_noLit pinSup 36 37 "ab",
    pinBytesTerm_noLit, pinListTerm_noLit, pinPairTerm_noLit,
    pinSumTerm_noLit, pinRecordTerm_noLit⟩

end Rcic.G2
