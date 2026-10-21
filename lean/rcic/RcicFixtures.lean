/-
RCIC 00 §20.5 CARRIER PIN — the first constructed `ResolvedEnv` in this
tree, and the first consumer of `iotaTypingCert`.

§20.5 asks for a concrete inductive (a `Nat`- or `List`-shaped fixture)
with a constructed `IotaWitness` for which `iotaTypingCert` returns
`some` BY EVALUATION. FIVE groups are built here, four of them carrying
witnesses and all of those positive:

  Nat   familyRef 0, zero 1, succ 2, N.rec    3  nparams 0, nindices 0
  NatU  the same family and constructors, `N.rec` at `ls = [param 0]`
        (05 §11 AnySort large elimination) — the erratum 4 carrier
  List  familyRef 0, nil  1, cons 2, L.rec    3  nparams 1, nindices 0
  Vec   familyRef 4, vnil 5, vcons 6, Vec.rec 7  nparams 1, nindices 1
  ListU familyRef 8, nilU 9, consU 10, ListU.rec 11  nparams 1,
        nindices 0, FAMILY ARITY 1 — the universe-polymorphic carrier
        (§5), which carries NO `IotaWitness` in this batch: its witness
        and its `iotaTypingCert` pin land with the `hlsLen` field
        (00 §20.7). What it pins today is DECLARATION content plus the
        admission `Bool` of §6

Three of the four WITNESS-CARRYING groups are monomorphic (`ls = []`).
`NatU` is not, and that
is its point: `hmajorTy` pins the last recursor domain's head to
`.const familyRef (ls.take famMember.arity)` (00 §19.2 erratum 4), so a
recursor whose level list is LONGER than the family's arity is
admissible. On `main` the comparand was the untruncated `ls`, which
forced `ls = []` and made every large-eliminating recursor witness
UNCONSTRUCTIBLE — §1.3 is that fixture, and every pin in it is a
prediction that could have failed.

Every pin below is closed by `rfl`, `decide`, `trivial` or a plain
term — no `native_decide` (it would introduce `Lean.ofReduceBool`,
outside the seal's `allowedAxioms := [propext, Quot.sound]`), no
`sorry`, no `simp`.

WHY THE LIST GROUP IS HERE TOO. At `nparams = 0` the fields
`hparamAlign`, `hctorResShape`, `hidxWalk`, `hidxPos`, `hidxTy` and the
params-half of `hfamSpineExact` are VACUOUSLY true, and
`ctorMajor w = ctorMajorRec w` whenever `lsC = ls`. A bare green cert
at Nat therefore does NOT exhibit the ∀-BUNDLE defect §20.5 exists to
catch. The List group makes `hparamAlign` / `hctorResShape` /
`hfamSpineExact` non-vacuous and makes the FREE field `ctorParams`
variable (it is length-pinned to `nparams`, so it cannot move at Nat).

THE `Vec` GROUP IS THE INDEXED CARRIER (§4). `hidxTy` / `idxPositions`
are vacuous at `nindices = 0`; making them non-vacuous needs
`nindices ≥ 1`, and at `nindices ≥ 1` the honest encoding WAS refused
on `main` — by `hminTel`, and by that field alone. 00 §19.2 erratum 5
(E-idx) removed that refutation: `minorTel` now reads its conclusion
off its own `T`, so `iotaMdom wVcons` IS the recursor's minor domain
and `iotaTypingCert wVcons` is `some`. The erratum's second half
deleted `IotaTyping.hminApply`, whose content is now DERIVED at the
iota site (`iotaLhs_ctorIdx_conv`, at the Conv-level statement
`IndexCoherentConv` — 00 §19.2 erratum 6); `wVconsBadIdx` (§4.1) is the
junk-index witness that shows why it could not stay a bundle field. REMOVING A
REFUTATION IS NOT INHABITING THE BUNDLE — §4.2 says what is still open.

The `iotaReductCert` pins import `rcic.RcicParRed`, and §6's admission
pins import `rcic.RcicAdmit`; those are the only dependencies of this
file outside `rcic.RcicIota` / `rcic.RcicEnv`.

Redex arguments are CLOSED terms chosen for their syntactic shape.
Typed plausibility is not an `IotaWitness` or `IotaTyping` condition —
neither structure mentions `HasTy` — so no term below claims to be
well-typed at its slot; the Nat group's arguments happen to be
typed-plausible, the List group's are not throughout.
-/
import rcic.RcicEnv
import rcic.RcicIota
import rcic.RcicParRed
import rcic.RcicAdmit

namespace Rcic.Declarative

/-! ## 1. The Nat-shaped group

`N : Sort 1`, `zero : N`, `succ : N → N`,
`N.rec : Π (P : N → Sort 1) (mz : P zero)
           (ms : Π n:N, Π ih:P n, P (succ n)) (major : N), P major`.

Member order is 05 §3 consecutive refs: family, constructors
`1..nMinors`, recursor. -/

def natFamMember : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩
def natZeroMember : CheckedMember := ⟨.constructorM, 0, .const 0 [], none⟩
def natSuccMember : CheckedMember :=
  ⟨.constructorM, 0, .pi (.const 0 []) (.const 0 []), none⟩

/-- `N.rec`'s stored type. Argument order is 05 §11 fixed:
params (0) · motive (1) · minors (2) · major indices (0) · major (1). -/
def natRecType : Expr Nat :=
  .pi (.pi (.const 0 []) (.sort (.succ .zero)))          -- d0  P     : N → Sort 1
   (.pi (.app (.bvar 0) (.const 1 []))                    -- d1  mz    : P zero
    (.pi (.pi (.const 0 [])                               -- d2  ms    : Π n : N,
          (.pi (.app (.bvar 2) (.bvar 0))                 --              Π ih : P n,
            (.app (.bvar 3) (.app (.const 2 []) (.bvar 1)))))  --         P (succ n)
     (.pi (.const 0 [])                                   -- d3  major : N   ← hmajorTy
      (.app (.bvar 3) (.bvar 0)))))                       -- body : P major  ← hrecBody

def natRecMember : CheckedMember := ⟨.recursorM, 0, natRecType, none⟩

/-- The family-and-constructors prefix: the environment at which the
recursor is still fresh (05 admission records the recursor group on
exactly this prefix). -/
def natEnvPrefix : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv emptyEnv 0 natFamMember) 1 natZeroMember)
    2 natSuccMember

def natEnv : ResolvedEnv := extendEnv natEnvPrefix 3 natRecMember

/-- 00 §19.7 E-NatRef: the constructor-level expansion of every Nat
literal is TYPABLE at the family `N` (`.const 0 []`) in the 05 §3
environment `natEnvPrefix`, at every universe arity `n`, in the empty
context — `natExpand 0 = .const 1 []` by `HasTy.const` at `zero : N`,
and `natExpand (t+1) = .app (.const 2 []) (natExpand t)` by `HasTy.app`
at `succ : N → N` with the IH; the three `instantiateLevels [] _` /
`instantiate0 _ (.const 0 [])` results are definitional. Sealed: this
is the non-vacuity witness DT-017's `HasTy.lit` CONSUMES
(`pin_hasTyLit_natPrefix` below is `HasTy.lit` over it, 00 §20.11 T4),
and the pin that the pre-E-NatRef numbering (`zero` at ref 0, `succ`
at ref 1)
could never have supplied — under `natEnvPrefix` that `litSucc`
applies a term of type `N` to the family. -/
def natExpand_hasTy_natPrefix (n : Nat) :
    (t : Nat) → HasTy natEnvPrefix n [] (natExpand t) (.const 0 [])
  | 0 =>
      HasTy.const [] 1 [] natZeroMember rfl rfl (fun _ h => nomatch h)
  | t + 1 =>
      HasTy.app [] (.const 2 []) (natExpand t) (.const 0 []) (.const 0 [])
        (HasTy.const [] 2 [] natSuccMember rfl rfl (fun _ h => nomatch h))
        (natExpand_hasTy_natPrefix n t)

/-- §16 M-002c / M-005: the closed derivation for the `lit`
    judgment form — a literal IS typed, at the family `N`, over the
    05 §3 environment `natEnvPrefix`, at every `n` and `t`. This
    term is what makes `hasTyLitFalse` FALSE, so that deletion is a
    MEASURED consequence, not a claim. Type-valued: a closed
    derivation, not a `Nonempty` wrapper. -/
def pin_hasTyLit_natPrefix (n t : Nat) :
    HasTy natEnvPrefix n [] (.lit t) (.const 0 []) :=
  .lit [] t (.const 0 []) (natExpand_hasTy_natPrefix n t)

/-- 05 §5/§6/§13 telescope arithmetic, by evaluation:
`piCount` 0 / 0 / 1 / 4 and `4 = 0 + 1 + 2 + 0 + 1`. -/
theorem pin_natEnv_piCounts :
    (piCount natFamMember.mtype, piCount natZeroMember.mtype,
      piCount natSuccMember.mtype, piCount natRecMember.mtype)
      = (0, 0, 1, 0 + 1 + 2 + 0 + 1) := rfl

/-- 00 §19.2 erratum 3 (E-arity): the family's stored type is an arity. -/
theorem pin_natEnv_isArity : isArity natFamMember.mtype = true := rfl

def natMotive : Expr Nat := .lam (.const 0 []) (.const 0 [])
def natMinorZ : Expr Nat := .const 1 []
def natMinorS : Expr Nat := .lam (.const 0 []) (.lam (.const 0 []) (.const 1 []))
def natField : Expr Nat := .const 1 []

def natRecDoms : List (Expr Nat) :=
  [ .pi (.const 0 []) (.sort (.succ .zero))
  , .app (.bvar 0) (.const 1 [])
  , .pi (.const 0 []) (.pi (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (.app (.const 2 []) (.bvar 1))))
  , .const 0 [] ]

/-- Witness A: the `succ` redex `N.rec P z s (succ n)`. -/
def wSucc : IotaWitness natEnv where
  recRef := 3
  ctorRef := 2
  ls := []
  lsC := []
  recMember := natRecMember
  ctorMember := natSuccMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [natMotive, natMinorZ, natMinorS]
  fields := [natField]
  ctorParams := []
  kinds := [.directRec]
  minor := natMinorS
  hlen := rfl
  familyRef := 0
  famMember := natFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 2
  ctorIdx := 1
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.const 0 []]
  ctorResult := .const 0 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := natRecDoms
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .pi (.const 0 []) (.const 0 [])
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- Witness B: the `zero` redex `N.rec P z s zero` (the empty-kinds
base clause of every walk). -/
def wZero : IotaWitness natEnv where
  recRef := 3
  ctorRef := 1
  ls := []
  lsC := []
  recMember := natRecMember
  ctorMember := natZeroMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [natMotive, natMinorZ, natMinorS]
  fields := []
  ctorParams := []
  kinds := []
  minor := natMinorZ
  hlen := rfl
  familyRef := 0
  famMember := natFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 2
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := []
  ctorResult := .const 0 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := natRecDoms
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .const 0 []
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-! ### 1.1 The Nat pins (§20.5 carrier pin, evaluated) -/

theorem pin_iotaTypingCert_succ : (iotaTypingCert wSucc).isSome = true := rfl

theorem pin_iotaTypingCert_zero : (iotaTypingCert wZero).isSome = true := rfl

/-- The redex is the Nat iota: `N.rec P z s (succ n)`. -/
theorem pin_iotaLhs_succ :
    iotaLhsOf wSucc =
      recCall (.const 3 []) [natMotive, natMinorZ, natMinorS]
        (.app (.const 2 []) natField) := rfl

/-- The contractum is `s n (N.rec P z s n)` — the field, then the
recursive call at the field (05 §14). -/
theorem pin_iotaRhs_succ :
    iotaRhsOf wSucc =
      foldApps natMinorS
        [natField,
          recCall (.const 3 []) [natMotive, natMinorZ, natMinorS] natField] := rfl

theorem pin_iotaLhs_zero :
    iotaLhsOf wZero =
      recCall (.const 3 []) [natMotive, natMinorZ, natMinorS] (.const 1 []) := rfl

theorem pin_iotaRhs_zero : iotaRhsOf wZero = natMinorZ := rfl

/-- The reduct side, by evaluation on this environment (the universal
`iotaReductCert_of` is already sealed; this is the carrier instance). -/
theorem pin_iotaReductCert_succ :
    (iotaReductCert natEnv (iotaLhsOf wSucc)).isSome = true := rfl

theorem pin_iotaReductCert_zero :
    (iotaReductCert natEnv (iotaLhsOf wZero)).isSome = true := rfl

/-- The witness `iotaReductCert` RECONSTRUCTS from the redex contracts
to the same right-hand side as the hand-built witness. -/
theorem pin_iotaReduct_rhs_succ :
    (iotaReductCert natEnv (iotaLhsOf wSucc)).map (fun p => iotaRhsOf p.1)
      = some (iotaRhsOf wSucc) := rfl

theorem pin_iotaReduct_rhs_zero :
    (iotaReductCert natEnv (iotaLhsOf wZero)).map (fun p => iotaRhsOf p.1)
      = some (iotaRhsOf wZero) := rfl

/-! ### 1.2 The ∀-BUNDLE free-field control at Nat (`lsC` half)

`lsC` is a FREE witness field: no `IotaWitness` field type mentions it,
so a record update produces a second, equally valid witness with the
same recursor-side data. This is what makes an `IotaTyping` field that
mentions `lsC` unsound as a ∀-bundle (00 §20.5 RULE ∀-BUNDLE). -/

def wSuccBadLs : IotaWitness natEnv := { wSucc with lsC := [.param 7] }

theorem pin_free_field_lsC_moves :
    ctorMajor wSuccBadLs ≠ ctorMajor wSucc := by decide

theorem pin_free_field_recside_fixed :
    ctorMajorRec wSuccBadLs = ctorMajorRec wSucc := rfl

theorem pin_bundle_forall_safe_succ :
    (iotaTypingCert wSuccBadLs).isSome = true := rfl

/-- The left-hand side of `hminApply` is identical for the two
witnesses: same `rhsArgs`, same `mdom`. -/
theorem pin_bundle_rhs_agrees :
    rhsArgs (.const wSuccBadLs.recRef wSuccBadLs.ls) wSuccBadLs.preMajor
        wSuccBadLs.nparams wSuccBadLs.nMinors wSuccBadLs.fields
        wSuccBadLs.kinds wSuccBadLs.ctorAfterParams
      = rhsArgs (.const wSucc.recRef wSucc.ls) wSucc.preMajor
        wSucc.nparams wSucc.nMinors wSucc.fields wSucc.kinds
        wSucc.ctorAfterParams := rfl

theorem pin_bundle_mdom_agrees_lsC :
    iotaMdom wSuccBadLs natMotive = iotaMdom wSucc natMotive := rfl

/-! ### 1.3 Large elimination — the 00 §19.2 erratum 4 (E-lvl) carrier

05 §3/§11: the family's arity is `nU`, the AnySort recursor's is
`nU + 1` — the motive's level is a fresh suffix parameter. Every fixture
above has `famMember.arity = 0` and `ls = []`, so `ls.take arity = ls`
and the erratum-4 substitution is INVISIBLE to them. This group is the
fixture that exhibits it: the same `N` / `zero` / `succ` at the same
refs, with the recursor's motive codomain `Sort 1` replaced by
`Sort (param 0)` and `ls = [param 0]`. Nothing else moves — the minor
domains, the major domain and `recBody` are byte-identical to §1, and
`applyTel` discards the motive's own domain, so the forced `mdom` is
the §1 one.

On `main` — the four E-lvl sites reading the untruncated `ls` — this
witness is UNCONSTRUCTIBLE: `hmajorTy` demanded `.const 0 [param 0]`
where the recursor's own last domain is `.const 0 []`. Each pin below
therefore records a fact that was unconstructible or false before the
correction, and each could have come out the other way. -/

/-- `N.rec`'s stored type with an AnySort motive: `natRecType` with the
motive's codomain `Sort 1` replaced by `Sort (param 0)`. -/
def natRecTypeU : Expr Nat :=
  .pi (.pi (.const 0 []) (.sort (.param 0)))             -- d0  P     : N → Sort u
   (.pi (.app (.bvar 0) (.const 1 []))                    -- d1  mz    : P zero
    (.pi (.pi (.const 0 [])                               -- d2  ms    : Π n : N,
          (.pi (.app (.bvar 2) (.bvar 0))                 --              Π ih : P n,
            (.app (.bvar 3) (.app (.const 2 []) (.bvar 1)))))  --         P (succ n)
     (.pi (.const 0 [])                                   -- d3  major : N   ← hmajorTy
      (.app (.bvar 3) (.bvar 0)))))                       -- body : P major  ← hrecBody

/-- Arity 1: one level parameter, the 05 §11 motive level. The family
stays at arity 0, which is what makes `ls.take famMember.arity` bite. -/
def natRecMemberU : CheckedMember := ⟨.recursorM, 1, natRecTypeU, none⟩

def natEnvU : ResolvedEnv := extendEnv natEnvPrefix 3 natRecMemberU

def natRecDomsU : List (Expr Nat) :=
  [ .pi (.const 0 []) (.sort (.param 0))
  , .app (.bvar 0) (.const 1 [])
  , .pi (.const 0 []) (.pi (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 3) (.app (.const 2 []) (.bvar 1))))
  , .const 0 [] ]

/-- Witness A′: the `succ` redex at the large-eliminating recursor,
`N.rec.{u} P z s (succ n)`. Field-for-field `wSucc` except `recMember`,
`recDoms` and `ls`. `lsC` stays `[]` — the CONSTRUCTOR's arity is the
family's, not the recursor's, which is the whole content of erratum 4. -/
def wSuccU : IotaWitness natEnvU where
  recRef := 3
  ctorRef := 2
  ls := [.param 0]
  lsC := []
  recMember := natRecMemberU
  ctorMember := natSuccMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [natMotive, natMinorZ, natMinorS]
  fields := [natField]
  ctorParams := []
  kinds := [.directRec]
  minor := natMinorS
  hlen := rfl
  familyRef := 0
  famMember := natFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 2
  ctorIdx := 1
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.const 0 []]
  ctorResult := .const 0 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := natRecDomsU
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .pi (.const 0 []) (.const 0 [])
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- E-lvl SITE 3 (`hmajorTy`). The first conjunct IS the witness field:
the last recursor domain is the family head at the TRUNCATED list. The
second is `main`'s comparand — the untruncated `ls` — and it is false
here. `wSuccU` did not exist on `main`; this is why. -/
theorem pin_natU_hmajorTy_needs_take :
    (wSuccU.recDoms[wSuccU.nparams + 1 + wSuccU.nMinors + wSuccU.nindices]?
        = some (foldApps (.const wSuccU.familyRef
            (wSuccU.ls.take wSuccU.famMember.arity))
          ((List.range wSuccU.nparams).reverse.map
              (fun i => Expr.bvar (i + wSuccU.nindices + wSuccU.nMinors + 1)) ++
            (List.range wSuccU.nindices).reverse.map (fun i => Expr.bvar i)))) ∧
      (wSuccU.recDoms[wSuccU.nparams + 1 + wSuccU.nMinors + wSuccU.nindices]?
        ≠ some (foldApps (.const wSuccU.familyRef wSuccU.ls)
          ((List.range wSuccU.nparams).reverse.map
              (fun i => Expr.bvar (i + wSuccU.nindices + wSuccU.nMinors + 1)) ++
            (List.range wSuccU.nindices).reverse.map (fun i => Expr.bvar i)))) :=
  ⟨wSuccU.hmajorTy, by decide⟩

/-- E-lvl SITE 4 (`hfamSpineExact`). The `succ` DirectRec domain is
`.const 0 []`, so the comparand must be the family's level list. It was
`w.ls` on `main` — false at `[param 0]` — and is
`w.ls.take w.famMember.arity` now. -/
theorem pin_natU_famSpineExact_needs_take :
    (directRecFamilySpineExact wSuccU.familyRef
        (wSuccU.ls.take wSuccU.famMember.arity) wSuccU.nparams
        (wSuccU.preMajor.take wSuccU.nparams) wSuccU.kinds
        wSuccU.ctorAfterParams wSuccU.fields = true) ∧
      (directRecFamilySpineExact wSuccU.familyRef wSuccU.ls wSuccU.nparams
        (wSuccU.preMajor.take wSuccU.nparams) wSuccU.kinds
        wSuccU.ctorAfterParams wSuccU.fields = false) := ⟨rfl, rfl⟩

/-- E-lvl SITE 1 (`ctorMajorRec`). The recursor-side constructor head
carries the CONSTRUCTOR's levels, so it must not pick up the recursor's
motive level. On `main` this term was `.const 2 [param 0] natField`. -/
theorem pin_natU_ctorMajorRec_head :
    (ctorMajorRec wSuccU = foldApps (.const 2 []) [natField]) ∧
      (ctorMajorRec wSuccU ≠ foldApps (.const 2 wSuccU.ls) [natField]) :=
  ⟨rfl, by decide⟩

/-- E-lvl SITE 2 (`iotaMdom`'s `ctorAcc` seed) — and with it `hminTel`.
Truncated, the synthesized minor telescope at the large-eliminating
recursor is BYTE-IDENTICAL to the monomorphic one, hence equal to the
`hminDom`-forced minor domain. With `main`'s untruncated seed it is a
different term, so `hminTel` was false there as well as `hmajorTy`. -/
theorem pin_natU_iotaMdom_needs_take :
    (iotaMdom wSuccU natMotive = iotaMdom wSucc natMotive) ∧
      (iotaMdom wSuccU natMotive
        ≠ minorTel natMotive wSuccU.nparams
            (foldApps (.const wSuccU.ctorRef wSuccU.ls)
              (wSuccU.preMajor.take wSuccU.nparams))
            wSuccU.kinds wSuccU.ctorAfterParams) := ⟨rfl, by decide⟩

/-- E-lvl SITE 5, the level fact itself (00 §19.2 erratum 4's fifth
site). This pin used to read `LevelCoherent wSuccU ∧ …` and to be
evidence about an OBLIGATION; 00 §20.6 discharged that obligation
(`iotaLhs_ctorParams_levels_conv`, `RcicDTMeta`) and deleted the
premise, so what is pinned here is the discharged fact's CONCLUSION,
written out. `eqNList` is `False` on unequal lengths, so the untruncated
form — the second conjunct, `main`'s statement — is unsatisfiable for
any recursor that eliminates into more universes than its family has.
Both halves are `Prop`-level (`eqN` is a `∀ ρ`), so neither is
`decide`-able and neither uses it.

WHY THIS IS NOT `iotaLhs_ctorParams_levels_conv` APPLIED. The applied
form would want the derived fact at a TYPED lhs. No such lhs exists
here, for two independent reasons, both structural rather than
incidental. (i) `iotaLhs_ctorParams_levels_conv` lives in `RcicDTMeta`,
which IMPORTS this file (through `RcicParRed` → `RcicParRedCore` →
`RcicInvertFamily`, and directly); this file cannot name it without a
cycle. (ii) No fixture here carries a `HasTy` derivation at all — the
header says so and means it, and the theorem's hypotheses are the lhs
typing plus `EnvWf E n`.

THE INSTRUCTION THIS DOCSTRING CARRIED IS DISCHARGED, AND THE ANSWER IS
"STILL BLOCKED" (00 §20.7 CORRECTION SITE 13). It read: "when the
admission bundle (00 §20.7) lands, this pin is where the applied form
belongs". The bundle HAS landed — `natURecAdmitted` inhabits
`RecursorGroupIdxAdmitted natEnvPrefix 3 natRecMemberU` and
`natEnvUWfAt` inhabits `EnvWf natEnvU n` at every `n` (§7) — so the
half of reason (ii) that said the `EnvWf` premise was unsuppliable is
GONE, and with it the words "the still-uninhabited
`RecursorGroupIdxAdmitted`" this docstring used to carry. The applied
form is nevertheless NOT installed, for reasons the bundle does not
touch: reason (i), the import cycle, survives verbatim; and
`iotaLhs_ctorParams_levels_conv` additionally consumes a `HasTy`
derivation at the lhs, which no fixture here has, together with
`PiConvInj` / `FamAppConvInj` — two OPEN 00 §19.2 rows on F-05b's own
wall. That is the same wall 00 §20.7 D12 records for
`pin_vec_indexCoherentConv`'s tripwire (§4.1). The conclusion therefore
stays pinned directly, and the reason is now recorded rather than
deferred. -/
theorem pin_natU_levels_derived :
    eqNList wSuccU.lsC (wSuccU.ls.take wSuccU.famMember.arity) ∧
      ¬ eqNList wSuccU.lsC wSuccU.ls :=
  ⟨trivial, fun h => h⟩

/-- 00 §20.6 INSTANTIATION, exhibited. `natU` is the only member in this
file whose arity is not `0`, so it is the only one on which
`instantiateLevels` can do anything. Its own level list IS the canonical
vector `(List.range 1).map .param = [param 0]`, so instantiating the
stored type at it is the IDENTITY — which is why the §20.6 views
(`hminDom` and friends at `instantiateLevels w.ls X`) agree here with
the raw reading, and why every other pin in §1.3 survived the rule
change untouched. The second conjunct is the control: at a DIFFERENT
list the motive's `Sort (param 0)` moves, so the identity is a fact
about this list and not about `instantiateLevels`. -/
theorem pin_natU_instantiateLevels_identity :
    (instantiateLevels wSuccU.ls natRecTypeU = natRecTypeU) ∧
      (instantiateLevels [Level.zero] natRecTypeU ≠ natRecTypeU) :=
  ⟨rfl, by decide⟩

/-- 00 §20.6's three new `EnvWf.indMember` premises at the one
polymorphic member. Each conjunct could have come out the other way:
`hlvlB` at the FAMILY's arity `0` is false (the AnySort motive level is
genuinely bound by the recursor's own arity `1`); `harities` accepts
`nU + 1` by the 05 §11 AnySort branch and refuses `nU + 2`. -/
theorem pin_natU_envWf_checks :
    (exprLevelsBounded natRecMemberU.arity natRecMemberU.mtype = true) ∧
      (exprLevelsBounded natFamMember.arity natRecMemberU.mtype = false) ∧
      (exprFamCanonical natEnvPrefix natRecMemberU.mtype = true) ∧
      (groupArityCoherent natEnvPrefix natRecMemberU = true) ∧
      (groupArityCoherent natEnvPrefix
        { natRecMemberU with arity := 2 } = false) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- All four sites at once, by evaluation: the R-class recognizer
accepts the large-eliminating witness. `none` on `main`, and the
witness itself did not typecheck there. -/
theorem pin_natU_iotaTypingCert : (iotaTypingCert wSuccU).isSome = true := rfl

/-! ## 2. The List-shaped group (`nparams = 1`)

`L : Sort 1 → Sort 1`, `nil : Π A, L A`,
`cons : Π A, Π hd:A, Π tl:L A, L A`,
`L.rec : Π A (P : L A → Sort 1) (mn : P (nil A))
           (mc : Π hd:A, Π tl:L A, Π ih:P tl, P (cons A hd tl))
           (major : L A), P major`. -/

def listFamType : Expr Nat := .pi (.sort (.succ .zero)) (.sort (.succ .zero))
def listNilType : Expr Nat :=
  .pi (.sort (.succ .zero)) (.app (.const 0 []) (.bvar 0))
def listConsType : Expr Nat :=
  .pi (.sort (.succ .zero))
    (.pi (.bvar 0)
      (.pi (.app (.const 0 []) (.bvar 1)) (.app (.const 0 []) (.bvar 2))))
def listRecType : Expr Nat :=
  .pi (.sort (.succ .zero))                                       -- d0 A
   (.pi (.pi (.app (.const 0 []) (.bvar 0)) (.sort (.succ .zero))) -- d1 P
    (.pi (.app (.bvar 0) (.app (.const 1 []) (.bvar 1)))           -- d2 mn
     (.pi (.pi (.bvar 2) (.pi (.app (.const 0 []) (.bvar 3))       -- d3 mc
            (.pi (.app (.bvar 3) (.bvar 0))
              (.app (.bvar 4)
                (.app (.app (.app (.const 2 []) (.bvar 5)) (.bvar 2))
                  (.bvar 1))))))
      (.pi (.app (.const 0 []) (.bvar 3))                          -- d4 major
       (.app (.bvar 3) (.bvar 0))))))                              -- body

def listFamMember : CheckedMember := ⟨.inductiveM, 0, listFamType, none⟩
def listNilMember : CheckedMember := ⟨.constructorM, 0, listNilType, none⟩
def listConsMember : CheckedMember := ⟨.constructorM, 0, listConsType, none⟩
def listRecMember : CheckedMember := ⟨.recursorM, 0, listRecType, none⟩

def listEnvPrefix : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv emptyEnv 0 listFamMember) 1 listNilMember)
    2 listConsMember

def listEnv : ResolvedEnv := extendEnv listEnvPrefix 3 listRecMember

theorem pin_listEnv_piCounts :
    (piCount listFamMember.mtype, piCount listNilMember.mtype,
      piCount listConsMember.mtype, piCount listRecMember.mtype)
      = (1 + 0, 1 + 0, 1 + 2, 1 + 1 + 2 + 0 + 1) := rfl

theorem pin_listEnv_isArity : isArity listFamMember.mtype = true := rfl

def listParam : Expr Nat := .sort .zero
def listMotive : Expr Nat := .lam (.app (.const 0 []) listParam) (.sort .zero)
def listMinorN : Expr Nat := .const 1 []
def listMinorC : Expr Nat := .const 2 []
def listHead : Expr Nat := .const 1 []
def listTail : Expr Nat := .app (.const 1 []) listParam

def listRecDoms : List (Expr Nat) :=
  [ .sort (.succ .zero)
  , .pi (.app (.const 0 []) (.bvar 0)) (.sort (.succ .zero))
  , .app (.bvar 0) (.app (.const 1 []) (.bvar 1))
  , .pi (.bvar 2) (.pi (.app (.const 0 []) (.bvar 3))
      (.pi (.app (.bvar 3) (.bvar 0))
        (.app (.bvar 4)
          (.app (.app (.app (.const 2 []) (.bvar 5)) (.bvar 2)) (.bvar 1)))))
  , .app (.const 0 []) (.bvar 3) ]

def listPreMajor : List (Expr Nat) :=
  [listParam, listMotive, listMinorN, listMinorC]

/-- Witness C: `L.rec A P mn mc (cons A hd tl)`.
`kinds = [.plain, .directRec]` — the first non-trivial kind list. -/
def wCons : IotaWitness listEnv where
  recRef := 3
  ctorRef := 2
  ls := []
  lsC := []
  recMember := listRecMember
  ctorMember := listConsMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := listPreMajor
  fields := [listHead, listTail]
  ctorParams := [listParam]
  kinds := [.plain, .directRec]
  minor := listMinorC
  hlen := rfl
  familyRef := 0
  famMember := listFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 1
  nindices := 0
  nMinors := 2
  ctorIdx := 1
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.sort (.succ .zero), .bvar 0, .app (.const 0 []) (.bvar 1)]
  ctorResult := .app (.const 0 []) (.bvar 2)
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := listRecDoms
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams :=
    .pi (.sort .zero)
      (.pi (.app (.const 0 []) (.sort .zero)) (.app (.const 0 []) (.sort .zero)))
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- Witness D: `L.rec A P mn mc (nil A)`. -/
def wNil : IotaWitness listEnv where
  recRef := 3
  ctorRef := 1
  ls := []
  lsC := []
  recMember := listRecMember
  ctorMember := listNilMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := listPreMajor
  fields := []
  ctorParams := [listParam]
  kinds := []
  minor := listMinorN
  hlen := rfl
  familyRef := 0
  famMember := listFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 1
  nindices := 0
  nMinors := 2
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.sort (.succ .zero)]
  ctorResult := .app (.const 0 []) (.bvar 0)
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := listRecDoms
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .app (.const 0 []) (.sort .zero)
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-! ### 2.1 The List pins -/

theorem pin_iotaTypingCert_cons : (iotaTypingCert wCons).isSome = true := rfl

theorem pin_iotaTypingCert_nil : (iotaTypingCert wNil).isSome = true := rfl

/-- `L.rec A P mn mc (cons A hd tl)` contracts to
`mc hd tl (L.rec A P mn mc tl)`. -/
theorem pin_iotaRhs_cons :
    iotaRhsOf wCons =
      foldApps listMinorC
        [listHead, listTail, recCall (.const 3 []) listPreMajor listTail] := rfl

theorem pin_iotaRhs_nil : iotaRhsOf wNil = listMinorN := rfl

theorem pin_iotaReductCert_cons :
    (iotaReductCert listEnv (iotaLhsOf wCons)).isSome = true := rfl

theorem pin_iotaReductCert_nil :
    (iotaReductCert listEnv (iotaLhsOf wNil)).isSome = true := rfl

theorem pin_iotaReduct_rhs_cons :
    (iotaReductCert listEnv (iotaLhsOf wCons)).map (fun p => iotaRhsOf p.1)
      = some (iotaRhsOf wCons) := rfl

/-! ### 2.2 The ∀-BUNDLE free-field control at List (`ctorParams` half)

`ctorParams` is length-pinned (`hctorParams : ctorParams.length =
nparams`) and otherwise free; at `nparams = 1` it can be moved. -/

def wConsBadParams : IotaWitness listEnv :=
  { wCons with ctorParams := [.const 99 []], hctorParams := rfl }

def wConsBadLs : IotaWitness listEnv := { wCons with lsC := [.param 7] }

theorem pin_free_field_ctorParams_moves :
    ctorMajor wConsBadParams ≠ ctorMajor wCons := by decide

theorem pin_free_field_ctorParams_recside_fixed :
    ctorMajorRec wConsBadParams = ctorMajorRec wCons := rfl

theorem pin_free_field_cons_lsC_moves :
    ctorMajor wConsBadLs ≠ ctorMajor wCons := by decide

theorem pin_free_field_cons_lsC_recside_fixed :
    ctorMajorRec wConsBadLs = ctorMajorRec wCons := rfl

theorem pin_bundle_forall_safe_cons :
    (iotaTypingCert wConsBadParams).isSome = true := rfl

theorem pin_bundle_forall_safe_cons_lsC :
    (iotaTypingCert wConsBadLs).isSome = true := rfl

/-- The whole T-class payload the cert produces is unchanged by moving
either free field: same `motive`, same `mdom`, same `restMin`, same
`idxPositions`. This is the mechanical statement of 00 §20.5 RULE
∀-BUNDLE — `IotaTyping` is R-determined. -/
theorem pin_bundle_payload_agrees_ctorParams :
    ((iotaTypingCert wConsBadParams).map
        (fun ty => (ty.motive, ty.mdom, ty.restMin, ty.idxPositions)))
      = ((iotaTypingCert wCons).map
        (fun ty => (ty.motive, ty.mdom, ty.restMin, ty.idxPositions))) := rfl

theorem pin_bundle_payload_agrees_lsC :
    ((iotaTypingCert wConsBadLs).map
        (fun ty => (ty.motive, ty.mdom, ty.restMin, ty.idxPositions)))
      = ((iotaTypingCert wCons).map
        (fun ty => (ty.motive, ty.mdom, ty.restMin, ty.idxPositions))) := rfl

/-- The contractum is R-determined too: moving a free field does not
move `iotaRhsOf`, while it does move `iotaLhsOf`. -/
theorem pin_free_field_rhs_fixed :
    iotaRhsOf wConsBadParams = iotaRhsOf wCons := rfl

theorem pin_free_field_lhs_moves :
    iotaLhsOf wConsBadParams ≠ iotaLhsOf wCons := by decide

/-! ### 2.3 The `25c837507` defect, exhibited

Commit `25c837507` wrote `hminApply` with `ctorMajor w` (free `lsC` /
`ctorParams`) instead of the recursor-side `ctorMajorRec w`. Both
witnesses below have the SAME `mdom` and the SAME `rhsArgs` — those are
R-class — so the defective equation, read as a ∀-bundle over the
recursor's witnesses, would have to hold at both. It holds at `wCons`
and fails at `wConsBadParams`. A bundle asserting it is therefore
uninhabited, `RecursorGroupIdxAdmitted` with it is uninhabited, and
every `EnvWf`-conditioned theorem is vacuous exactly where iota
fires. -/

def defectiveMinApplyRhs (w : IotaWitness listEnv) : Expr Nat :=
  .app (foldApps listMotive (w.preMajor.drop (w.nparams + 1 + w.nMinors)))
    (ctorMajor w)

def listConsMdom : Expr Nat := iotaMdom wCons listMotive

def listConsRhsArgs : List (Expr Nat) :=
  rhsArgs (.const wCons.recRef wCons.ls) wCons.preMajor wCons.nparams
    wCons.nMinors wCons.fields wCons.kinds wCons.ctorAfterParams

/-- Both sides of the defective equation share their left-hand data. -/
theorem pin_defect_shared_lhs :
    (iotaMdom wConsBadParams listMotive = listConsMdom) ∧
      (rhsArgs (.const wConsBadParams.recRef wConsBadParams.ls)
          wConsBadParams.preMajor wConsBadParams.nparams
          wConsBadParams.nMinors wConsBadParams.fields wConsBadParams.kinds
          wConsBadParams.ctorAfterParams = listConsRhsArgs) := ⟨rfl, rfl⟩

theorem pin_defect_ctorMajor_holds_at_base :
    applyTel listConsRhsArgs listConsMdom
      = some (defectiveMinApplyRhs wCons) := rfl

theorem pin_defect_ctorMajor_fails_at_variant :
    applyTel listConsRhsArgs listConsMdom
      ≠ some (defectiveMinApplyRhs wConsBadParams) := by decide

/-- The repaired field is stable under the same record update. -/
theorem pin_repair_ctorMajorRec_holds_at_both :
    (applyTel listConsRhsArgs listConsMdom
        = some (.app (foldApps listMotive
            (wCons.preMajor.drop (wCons.nparams + 1 + wCons.nMinors)))
          (ctorMajorRec wCons))) ∧
      (applyTel listConsRhsArgs listConsMdom
        = some (.app (foldApps listMotive
            (wConsBadParams.preMajor.drop
              (wConsBadParams.nparams + 1 + wConsBadParams.nMinors)))
          (ctorMajorRec wConsBadParams))) := ⟨rfl, rfl⟩

/-! ### 2.4 The T-class walks are non-vacuous in the List group

`hparamAlign` and `hctorResShape` are vacuously `true` at `nparams = 0`.
At `nparams = 1` they discriminate: perturbing the compared data flips
them to `false`. -/

theorem pin_paramAlign_nonvacuous :
    (recCtorParamAlign listRecType listConsType [listParam] = true) ∧
      (recCtorParamAlign (.pi (.sort .zero) (.sort .zero)) listConsType
        [listParam] = false) := ⟨rfl, rfl⟩

theorem pin_ctorResShape_nonvacuous :
    (ctorResultParamShape 0 (.app (.const 0 []) (.bvar 2)) 0 1 2 = true) ∧
      (ctorResultParamShape 0 (.app (.const 0 []) (.bvar 1)) 0 1 2 = false) :=
  ⟨rfl, rfl⟩

theorem pin_famSpineExact_nonvacuous :
    (directRecFamilySpineExact 0 [] 1 [listParam] wCons.kinds
        wCons.ctorAfterParams wCons.fields = true) ∧
      (directRecFamilySpineExact 0 [] 1 [.sort (.succ .zero)] wCons.kinds
        wCons.ctorAfterParams wCons.fields = false) := ⟨rfl, rfl⟩

/- RETIRED from this file. Prefix `EnvWf` (`natEnvWfPrefix`,
`natEnvWfPrefixAt`, `pin_envWf_natPrefix`, `listEnvWfPrefix`,
`listEnvWfPrefixAt`, `pin_envWf_listPrefix`) is re-proved in
`RcicIndGroupFixtureWf` with `IndGroupAdmitted`.

`natEnvWfOfIdxAdm`, `natEnvWfAt`, `pin_envWf_nat`,
`pin_envWf_nat_reduces_to_idxAdm`, `listEnvWfOfIdxAdm`, `listEnvWfAt`,
`pin_envWf_list`, `pin_envWf_list_reduces_to_idxAdm` stated `EnvWf` of
a recursor whose motive is a fixed `Sort 1` at arity 0. 05 §11 does
not derive that signature.

`natUEnvWfOfIdxAdm` / `pin_envWf_natU_reduces_to_idxAdm` stay true and
are re-proved with `natEnvUWfAt`, not here: this file does not import
the admission inhabitant. -/

/-! ## 4. The `Vec`-shaped group — the indexed carrier (`nindices = 1`)

`hidxWalk` / `hidxPos` / `hidxTy` / `idxPositions` are vacuous in both
groups above because `nindices = 0`. This group makes them non-vacuous.
On `main` it was a NEGATIVE fixture, and it exhibited a §20.5 LATENT
HOLE:

  every `IotaWitness` field was satisfied by the honest 05 §11–§14
  encoding of `Vec`, every other `IotaTyping` guard passed INCLUDING
  `hminApply` and all four index walks — and `hminTel` was FALSE, so
  `IotaTyping vecEnv wVcons` was uninhabited and
  `RecursorGroupIdxAdmitted vecEnvPrefix 7 vecRecMember` with it.

The cause was `minorTel`'s conclusion. `iotaMdom` passed
`F := foldApps motive (w.preMajor.drop (w.nparams + 1 + w.nMinors))` —
the motive applied to the MAJOR's index arguments, a term of the redex's
scope, which `minorTel` then LIFTED past every minor binder. The
recursor's own minor domain concludes with the motive applied to the
CONSTRUCTOR's RESULT indices, expressed in the minor's own binders
(`P (succ n) (vcons A n hd tl)`, `n` bound). At `nindices = 0` both
collapse to `motive ctorAcc` and the divergence is invisible; at
`nindices ≥ 1` no choice of major index argument can reconcile them,
because a lifted redex term can never mention a minor binder.

00 §19.2 erratum 5 (E-idx) drops `F` and reads the conclusion off the
walk's own `T`, which at the base IS the constructor's result type
already transported into the expanded minor context. `hminTel` now
holds here EXACTLY — `pin_vec_hminTel`, `rfl`, not up to `Conv` — and
the encoding was NOT bent to get it (00 §18.3): the fixture is the same
honest `Vec` it always was, byte for byte, and the only line that moved
in this file for the Nat, List and Vec witnesses is `hresTel := rfl`.

The erratum's second half concerns the field that was RIGHT here,
`IotaTyping.hminApply`. It mentioned
`w.preMajor.drop (w.nparams + 1 + w.nMinors)` — a witness datum that no
`IotaWitness` field constrains beyond its length — so by 00 §20.5 RULE
∀-BUNDLE it could not be a bundle field at all: §4.1's `wVconsBadIdx`
is a legal witness of this same recursor, with the same `mdom` and the
same `rhsArgs`, on which it is false. Its content is now `hminTel`
(which implies it, via `applyTel_rhsArgs_minorTel`) plus a per-redex
fact at the iota site — no longer a PREMISE there either: 00 §19.2
erratum 6 restated it at the conversion layer (`IndexCoherentConv`)
and DISCHARGED it (`iotaLhs_ctorIdx_conv`). It once had a level
sibling, `LevelCoherent`; 00 §20.6 discharged that one first. Both
per-redex premises are now gone from `IotaPreserve`. That the ∀-bundle
survives junk major indices is the point of §4.1, not a defect of it.

Refs continue the Nat group: `Vec` 4, `vnil` 5, `vcons` 6, `Vec.rec` 7;
the index type is the Nat group's `N` at ref 0. -/

/-- `Vec : Sort 1 → N → Sort 1`. -/
def vecFamType : Expr Nat :=
  .pi (.sort (.succ .zero)) (.pi (.const 0 []) (.sort (.succ .zero)))

/-- `vnil : Π A, Vec A zero`. -/
def vecNilType : Expr Nat :=
  .pi (.sort (.succ .zero))
    (.app (.app (.const 4 []) (.bvar 0)) (.const 1 []))

/-- `vcons : Π A, Π n:N, Π hd:A, Π tl:Vec A n, Vec A (succ n)`. -/
def vecConsType : Expr Nat :=
  .pi (.sort (.succ .zero))                                   -- A
    (.pi (.const 0 [])                                         -- n  : N
      (.pi (.bvar 1)                                           -- hd : A
        (.pi (.app (.app (.const 4 []) (.bvar 2)) (.bvar 1))   -- tl : Vec A n
          (.app (.app (.const 4 []) (.bvar 3))                 -- Vec A (succ n)
            (.app (.const 2 []) (.bvar 2))))))

/-- `Vec.rec : Π A (P : Π n:N, Vec A n → Sort 1) (mn : P zero (vnil A))
      (mc : Π n hd tl (ih : P n tl), P (succ n) (vcons A n hd tl))
      (i : N) (v : Vec A i), P i v`. -/
def vecRecType : Expr Nat :=
  .pi (.sort (.succ .zero))                                        -- d0 A
   (.pi (.pi (.const 0 [])                                          -- d1 P
          (.pi (.app (.app (.const 4 []) (.bvar 1)) (.bvar 0))
            (.sort (.succ .zero))))
    (.pi (.app (.app (.bvar 0) (.const 1 []))                       -- d2 mn
           (.app (.const 5 []) (.bvar 1)))
     (.pi (.pi (.const 0 [])                                        -- d3 mc
            (.pi (.bvar 3)
              (.pi (.app (.app (.const 4 []) (.bvar 4)) (.bvar 1))
                (.pi (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0))
                  (.app (.app (.bvar 5) (.app (.const 2 []) (.bvar 3)))
                    (.app (.app (.app (.app (.const 6 []) (.bvar 6)) (.bvar 3))
                        (.bvar 2)) (.bvar 1)))))))
      (.pi (.const 0 [])                                            -- d4 i : N
       (.pi (.app (.app (.const 4 []) (.bvar 4)) (.bvar 0))         -- d5 v
        (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0)))))))            -- body

def vecFamMember : CheckedMember := ⟨.inductiveM, 0, vecFamType, none⟩
def vecNilMember : CheckedMember := ⟨.constructorM, 0, vecNilType, none⟩
def vecConsMember : CheckedMember := ⟨.constructorM, 0, vecConsType, none⟩
def vecRecMember : CheckedMember := ⟨.recursorM, 0, vecRecType, none⟩

def vecEnvPrefix : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv natEnv 4 vecFamMember) 5 vecNilMember)
    6 vecConsMember

def vecEnv : ResolvedEnv := extendEnv vecEnvPrefix 7 vecRecMember

theorem pin_vec_piCounts :
    (piCount vecFamType, piCount vecNilType, piCount vecConsType,
      piCount vecRecType) = (1 + 1, 1 + 0, 1 + 3, 1 + 1 + 2 + 1 + 1) := rfl

theorem pin_vec_isArity : isArity vecFamType = true := rfl

def vecParam : Expr Nat := .sort .zero
def vecMotiveArg : Expr Nat :=
  .lam (.const 0 [])
    (.lam (.app (.app (.const 4 []) vecParam) (.bvar 0)) (.sort .zero))
def vecMinorN : Expr Nat := .const 5 []
def vecMinorC : Expr Nat := .const 6 []
def vecFieldN : Expr Nat := .const 1 []
def vecFieldHd : Expr Nat := .sort (.succ .zero)
def vecFieldTl : Expr Nat := .app (.const 5 []) vecParam
/-- The major's index argument: `succ n`, i.e. the constructor's result
index at the actual field value (what `hminApply` demands). -/
def vecMajorIdx : Expr Nat := .app (.const 2 []) vecFieldN

def vecRecDoms : List (Expr Nat) :=
  [ .sort (.succ .zero)
  , .pi (.const 0 [])
      (.pi (.app (.app (.const 4 []) (.bvar 1)) (.bvar 0))
        (.sort (.succ .zero)))
  , .app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))
  , .pi (.const 0 [])
      (.pi (.bvar 3)
        (.pi (.app (.app (.const 4 []) (.bvar 4)) (.bvar 1))
          (.pi (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0))
            (.app (.app (.bvar 5) (.app (.const 2 []) (.bvar 3)))
              (.app (.app (.app (.app (.const 6 []) (.bvar 6)) (.bvar 3))
                  (.bvar 2)) (.bvar 1))))))
  , .const 0 []
  , .app (.app (.const 4 []) (.bvar 4)) (.bvar 0) ]

/-- Witness E: `Vec.rec A P mn mc (succ n) (vcons A n hd tl)`.
EVERY `IotaWitness` field is `rfl`-level — the honest encoding is a
witness. The obstruction is on `IotaTyping`, below. -/
def wVcons : IotaWitness vecEnv where
  recRef := 7
  ctorRef := 6
  ls := []
  lsC := []
  recMember := vecRecMember
  ctorMember := vecConsMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [vecParam, vecMotiveArg, vecMinorN, vecMinorC, vecMajorIdx]
  fields := [vecFieldN, vecFieldHd, vecFieldTl]
  ctorParams := [vecParam]
  kinds := [.plain, .plain, .directRec]
  minor := vecMinorC
  hlen := rfl
  familyRef := 4
  famMember := vecFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 1
  nindices := 1
  nMinors := 2
  ctorIdx := 1
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms :=
    [ .sort (.succ .zero)
    , .const 0 []
    , .bvar 1
    , .app (.app (.const 4 []) (.bvar 2)) (.bvar 1) ]
  ctorResult :=
    .app (.app (.const 4 []) (.bvar 3)) (.app (.const 2 []) (.bvar 2))
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := vecRecDoms
  recBody := .app (.app (.bvar 4) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams :=
    .pi (.const 0 [])
      (.pi (.sort .zero)
        (.pi (.app (.app (.const 4 []) (.sort .zero)) (.bvar 1))
          (.app (.app (.const 4 []) (.sort .zero))
            (.app (.const 2 []) (.bvar 2)))))
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- The kind list is genuinely mixed: two `plain` fields and one
`directRec`. -/
theorem pin_vec_kinds :
    wVcons.kinds = [RecKind.plain, RecKind.plain, RecKind.directRec] := rfl

/-- The reduct side is unaffected: iota FIRES on this redex. -/
theorem pin_vec_iotaReductCert :
    (iotaReductCert vecEnv (iotaLhsOf wVcons)).isSome = true := rfl

theorem pin_vec_iotaRhs :
    iotaRhsOf wVcons =
      foldApps vecMinorC
        [vecFieldN, vecFieldHd, vecFieldTl,
          foldApps (.const 7 [])
            [vecParam, vecMotiveArg, vecMinorN, vecMinorC, vecFieldN,
              vecFieldTl]] := rfl

/-- The four index walks are TRUE and, unlike at `nindices = 0`,
non-vacuous: `idxPositions = [[], [], [1]]` records the `directRec`
field's index at spine position 1 of `recParamsFields`. -/
theorem pin_vec_idxWalks_nonvacuous :
    (recIdxFromSpineWalk wVcons.familyRef wVcons.nparams wVcons.nindices
        (recParamsFields wVcons) wVcons.kinds wVcons.ctorAfterParams
        wVcons.fields = true) ∧
    (recIdxPosBuild wVcons.nparams (recParamsFields wVcons) wVcons.kinds
        wVcons.ctorAfterParams wVcons.fields = some [[], [], [1]]) ∧
    (recIdxPosWalk wVcons.nparams (recParamsFields wVcons) wVcons.kinds
        wVcons.ctorAfterParams wVcons.fields [[], [], [1]] = true) ∧
    (recIdxTyWalkPos wVcons.recMember.mtype wVcons.ctorMember.mtype
        wVcons.nparams (recPrefix wVcons.preMajor wVcons.nparams wVcons.nMinors)
        (recParamsFields wVcons) wVcons.kinds wVcons.ctorAfterParams
        wVcons.fields [[], [], [1]] = true) := ⟨rfl, rfl, rfl, rfl⟩

/-- The other T-class walks pass too. -/
theorem pin_vec_tclass_walks :
    (directRecFamilySpine wVcons.familyRef wVcons.ls wVcons.nparams
        (wVcons.preMajor.take wVcons.nparams) wVcons.kinds
        wVcons.ctorAfterParams wVcons.fields = true) ∧
    (recCtorParamAlign wVcons.recMember.mtype wVcons.ctorMember.mtype
        (wVcons.preMajor.take wVcons.nparams) = true) ∧
    (directRecFamilySpineExact wVcons.familyRef wVcons.ls wVcons.nparams
        (wVcons.preMajor.take wVcons.nparams) wVcons.kinds
        wVcons.ctorAfterParams wVcons.fields = true) ∧
    (ctorResultParamShape wVcons.familyRef wVcons.ctorResult
        wVcons.famMember.arity wVcons.nparams
        wVcons.kinds.length = true) := ⟨rfl, rfl, rfl, rfl⟩

/-- `mdom` is forced by `hminDom`: the recursor's actual minor domain. -/
def vecMdom : Expr Nat :=
  .pi (.const 0 [])
    (.pi (.sort .zero)
      (.pi (.app (.app (.const 4 []) (.sort .zero)) (.bvar 1))
        (.pi (.app (.app vecMotiveArg (.bvar 2)) (.bvar 0))
          (.app (.app vecMotiveArg (.app (.const 2 []) (.bvar 3)))
            (.app (.app (.app (.app (.const 6 []) (.sort .zero)) (.bvar 3))
                (.bvar 2)) (.bvar 1))))))

def vecRestMin : Expr Nat :=
  .pi (.const 0 [])
    (.pi (.app (.app (.const 4 []) (.sort .zero)) (.bvar 0))
      (.app (.app vecMotiveArg (.bvar 1)) (.bvar 0)))

theorem pin_vec_hminDom :
    applyTel (wVcons.preMajor.take (wVcons.nparams + 1 + wVcons.ctorIdx))
        wVcons.recMember.mtype = some (Expr.pi vecMdom vecRestMin) := rfl

/-- The INDEX AGREEMENT at the honest `Vec` redex, ON THE NOSE and
written out RAW: the constructor's result indices at the ACTUAL field
values ARE the major's index arguments.

00 §19.2 erratum 6 deleted the obligation this pin used to name
(`IndexCoherent`), because the SYNTACTIC equation is strictly stronger
than anything a redex's typing delivers. What the fixture always
carried is the equation itself, at this one witness, and that is
unchanged — only the name it was stated through is gone. The Conv-level
statement erratum 6 put in its place is satisfied here a fortiori;
`pin_vec_indexCoherentConv` below reads it off this pin. -/
theorem pin_vec_indexAlignment :
    (applyTel wVcons.fields wVcons.ctorAfterParams).map
        (familyIdx wVcons.nparams)
      = some (wVcons.preMajor.drop
          (wVcons.nparams + 1 + wVcons.nMinors)) := rfl

/-- The Conv-level pin: `IndexCoherentConv` HOLDS at the honest `Vec`
redex, at every `n` and every context, read off the syntactic alignment
by `convArgs_refl`.

This is the CHEAP direction, and it is the only one available at a
carrier. `iotaLhs_ctorIdx_conv` (`RcicDTMeta`) — the discharge — is
still NOT run here, and the TRIPWIRE this docstring carried is answered
rather than left standing (00 §20.7 D12 / CORRECTION SITE 10). It read:
"when that bundle lands, replace this pin's proof with the discharge
applied at a typed `iotaLhsOf wVcons`". The bundle HAS landed, and it
supplies TWO of that theorem's SIX inputs outright and a third only at
one context:

    hE : EnvWf E n                    SUPPLIED — pin_envWf_vec0 / _vec,
                                      and vecEnvWfAt at every n, which
                                      is why the exhibit is generic
    ty : IotaTyping E w               SUPPLIED — vecRecAdmitted.typing,
                                      i.e. iotaTyping_of_admitted
    hΓ : CtxWf E n Γ                  PARTLY — CtxWf.nil at Γ = [] is
                                      free; at the GENERIC Γ this pin
                                      binds it is NOT derivable, because
                                      CtxWf's .assumption / .letBinding
                                      arms demand HasTy derivations
    hpci : PiConvInj E n              NO — OPEN 00 §19.2 row, F-05b wall
    hfaci : FamAppConvInj E n         NO — OPEN 00 §19.2 row, same wall
    hT : HasTy E n Γ (iotaLhsOf w) T  NO — no such derivation in this file

So the admission bundle is NECESSARY BUT NOT SUFFICIENT for the
tripwire, the tripwire stays unfired, and that is now a MEASURED fact
with the missing inputs named rather than a deferral pointing at
`EnvWf`. A discharge table that said "five of six" would be the same
defect one level down as a census that says eleven of twelve. -/
def pin_vec_indexCoherentConv (n : Nat) (Γ : LCtx) :
    IndexCoherentConv (E := vecEnv) n Γ wVcons := by
  intro U hU
  have h := pin_vec_indexAlignment
  rw [hU, Option.map_some'] at h
  injection h with h'
  rw [h']
  exact convArgs_refl _

/-- `hminTel` HOLDS, and exactly: the corrected `minorTel` conclusion IS
the recursor's own minor domain, not merely convertible with it. On
`main` this pin read `vecMdom ≠ iotaMdom wVcons vecMotiveArg`, closed
`by decide`, and `pin_vec_hminTel_divergence` displayed the two sides;
the divergence is gone, so the display went with it. -/
theorem pin_vec_hminTel : vecMdom = iotaMdom wVcons vecMotiveArg := rfl

/-- The §20.5 carrier pin at `nindices = 1`: the R-class recognizer
accepts the honest indexed witness. On `main` this pin read
`(iotaTypingCert wVcons).isSome = false`. -/
theorem pin_vec_iotaTypingCert : (iotaTypingCert wVcons).isSome = true := rfl

/-! ### 4.1 The junk-index witness (00 §20.5 RULE ∀-BUNDLE, index half)

The MAJOR's index slots are unconstrained by every `IotaWitness` field:
`hpre` fixes only a length, `hminor` reads slot `nparams + 1 + ctorIdx`,
`hctorAfter` reads `take nparams`. So a witness may carry junk indices
and still be a legal witness of the same recursor — same `mdom`, same
`rhsArgs`, same left-hand side of the deleted `hminApply` — and kernel
iota still fires on it, because iota never inspects them.

That is why the index agreement is a PREMISE at the iota site and not
an `IotaTyping` field: as a field it made the ∀-bundle prove `False`,
the same defect class as `lsC` (§1.2) and `ctorParams` (§2.2). The
bundle now survives junk indices — `pin_vec_badIdx_iotaTypingCert` —
and the SYNTACTIC index alignment is what fails on them. -/

/-- `wVcons` with the major's index argument replaced by
`succ (succ zero)` — `succ` of something that is not the field. Only
`hpre`, `hminor` and `hctorAfter` mention `preMajor`, and all three
still hold. -/
def wVconsBadIdx : IotaWitness vecEnv :=
  { wVcons with
      preMajor := [vecParam, vecMotiveArg, vecMinorN, vecMinorC,
        .app (.const 2 []) (.app (.const 2 []) (.const 1 []))],
      hpre := rfl, hminor := rfl, hctorAfter := rfl }

/-- The forced minor domain is unmoved: `hminDom` reads
`preMajor.take (nparams + 1 + ctorIdx)`, which the update does not
touch. -/
theorem pin_vec_badIdx_mdom_agrees :
    applyTel (wVconsBadIdx.preMajor.take
        (wVconsBadIdx.nparams + 1 + wVconsBadIdx.ctorIdx))
      wVconsBadIdx.recMember.mtype = some (Expr.pi vecMdom vecRestMin) := rfl

/-- And `hminTel` holds at it, for the same reason it holds at `wVcons`:
the corrected `minorTel` never mentions the major's indices. -/
theorem pin_vec_badIdx_hminTel :
    vecMdom = iotaMdom wVconsBadIdx vecMotiveArg := rfl

/-- The ∀-bundle SURVIVES the junk index. This is exactly what the
pre-correction `hminApply` denied, and why it could not be a field. -/
theorem pin_vec_badIdx_iotaTypingCert :
    (iotaTypingCert wVconsBadIdx).isSome = true := rfl

/-- WHAT THIS PINS NOW (00 §19.2 erratum 6). What fails at the
junk-index witness is the SYNTACTIC alignment — the form the premise
had on `main` through #3811, and the form erratum 5 exhibited as
un-fieldable. That is exactly the §20.5 RULE ∀-BUNDLE content: a legal
witness of this same recursor, same `mdom`, same `rhsArgs`, on which
the equation is FALSE, so it could not be an `IotaTyping` field.

The CONV-LEVEL analogue is NOT refuted here, and is not refutable in
this tree. `¬ IndexCoherentConv 0 Γ wVconsBadIdx` unfolds to a
refutation of `Conv vecEnv 0 Γ (succ zero) (succ (succ zero))`, and
neither side has a redex (`natZeroMember` / `natSuccMember` have
`body = none`, so no delta; no beta / zeta / lit; the head is a
CONSTRUCTOR, not a recursor, so no iota) — so refuting it needs a
`Conv → Join` characterization whose `irr` arm is cut by typing, i.e.
the open F-05b row itself. `FamAppConvInj` does NOT apply: its head
must be `inductiveM` and `succ` is `constructorM`, and no
constructor-head no-confusion row exists on the §19.2 ledger.
Introducing one to keep a fixture refutation green would be growing a
rule out of one's own failure; it is not done.

Nor is the Conv-level statement decidable by `rfl` or `decide`: `Conv`
is a `Type`-valued 12-constructor judgment with an `irr` arm carrying
typing derivations, not a computable predicate. This pin is therefore
strictly the syntactic half, and says so. -/
theorem pin_vec_badIdx_indexAlignment_fails :
    ¬ ((applyTel wVconsBadIdx.fields wVconsBadIdx.ctorAfterParams).map
         (familyIdx wVconsBadIdx.nparams)
       = some (wVconsBadIdx.preMajor.drop
           (wVconsBadIdx.nparams + 1 + wVconsBadIdx.nMinors))) := by
  decide

/-! ### 4.2 What removing the refutation does NOT establish

`pin_vec_iotaTyping_refuted` and `pin_vec_recursorGroup_refuted` are
DELETED here, and deliberately NOT replaced by positive pins AT THIS
POINT IN THE FILE. Deleting a refutation is not producing an inhabitant:
after 00 §19.2 erratum 5,
`RecursorGroupIdxAdmitted vecEnvPrefix 7 vecRecMember` was no longer
refutable by the `hminTel` / `hminApply` route, and it was not inhabited
either. Its `typing` field is a Π over every witness of this recursor in
EVERY extension, and `pin_vec_iotaTypingCert` is a value at one `w` —
evaluation cannot discharge a Π over `w`.

WHAT INHABITS IT NOW (00 §20.7 CORRECTION SITES 11 and 12). §7.1's
`vecRecAdmitted` does, by `.ofAdmitted rfl` off the declared `Bool`
§6 pins, and `pin_envWf_vec0` / `pin_envWf_vec` (§7.3) are the `EnvWf`
values that follow — so the sentences above are the record of a state
this file has left, and the vacuity they end with is over. What closed
each named gate:

  `walks_of_declared`      CLOSED — the two-stage declared→instance
                           transport, 31 named lemmas (stage L in
                           `RcicLevelCalc.lean`, stage σ in
                           `RcicAdmit.lean`)
  ref freedom              CLOSED — conjunct 0 of
                           `recursorGroupAdmittedAt` looks the
                           constructor up at `familyRef + 1 + ctorIdx`
                           for every `ctorIdx`. §6's
                           `pin_vec_admitted_needs_ctor` /
                           `pin_vec_admitted_refuses_decoy` and §7.5's
                           `pin_vec_decoy_iotaTyping_refuted` are the
                           hazard exhibited from both sides
  `hparamAlign` / `hidxTy` NOT closed — RECLASSIFIED as NOT CONSULTED.
  declaration lemmas       `recCtorParamAlignGo` applies the SAME `pre`
                           to both stored types
                           (`RcicDeclarative.lean:605-613`), and
                           `recIdxTyWalkPos_instantiate`
                           (`RcicIota.lean:2262-2275`) maps BOTH
                           prefixes under one substitution, so neither
                           lemma is on the path to a field
  the level-arity premise  CLOSED — a FOURTH gate, absent from this
  `nU ≤ ls.length` of      comment because it postdates it: discovered
  `map_instLevel_canonical` and closed by the `IotaWitness` field
                           `hlsLen` together with conjunct c0b

What is NOT closed, and is not claimed to be: `SortConvChar` /
`PiConvInj` / `FamAppConvInj` stay open on F-05b's own wall,
`IotaPreserve` stays CONDITIONAL, and no 00 §19.2 row flips here.
(`LitPreserve` left that list in segment 7a — discharged VACUOUSLY,
00 §19.7 E-LitP, because `HasTy` then had no `lit` rule — and stays
off it: DT-017's `HasTy.lit` discharged it FOR REAL, `litPreserve`,
00 §20.11.) -/

/-- The extension transport a `RecursorGroupIdxAdmitted.typing` readout
is applied through. Kept: it is the bundle's `hext` argument, which
§4.2 names as unbuilt, not as unneeded. -/
def vecExt : ∀ r m, vecEnvPrefix.members r = some m →
    vecEnv.members r = some m := by
  intro r m h
  by_cases hr : r = 7
  · exact absurd (hr ▸ h) (fun hh => Option.noConfusion hh)
  · rw [vecEnv, members_extend_ne _ _ _ _ hr]
    exact h

/-! ## 5. The `listU` group — the UNIVERSE-POLYMORPHIC carrier
(family arity 1, 00 §20.7 D9)

THIS GROUP IS THE SEGMENT'S OWN ANTI-SELF-CERTIFICATION CONTROL. The
whole level half of the admission bundle — the canonical-vector
truncation `w.ls.take w.famMember.arity`, the `nU ≤ ls.length` premise
of `map_instLevel_canonical` (`RcicLevelCalc.lean:257-259`), conjunct
c0b, and the mixed-view routing of `ctorResultParamShape` — is INERT at
family arity 0, and every other carrier in this file has family arity 0
(`:75`, `:547`, `:1025`). A green admission pin on Nat / NatU / List /
Vec is therefore compatible with a declared form whose level side is
wrong: it is a green that carries no information about the thing being
built. At `nU = 1` with `recArity = 2` the recursor's `ls` has length
2, so `ls.take 1` is a GENUINE truncation — the first place in this
tree where `map_instLevel_canonical` is applied at a non-zero `k`, and
the first place where a short `ls` is refusable at all.

Refs 8–11 continue the file's convention, and the chain is rooted at
`natEnv` (refs 0–3), not at `vecEnvPrefix`: the group needs no `N` and
no `Vec`, and rooting it lower keeps `Vec`'s refs 4–7 out of it.

    ListU     8  .inductiveM,   arity 1,  Sort u → Sort u
    nilU      9  .constructorM, arity 1,  Π A : Sort u, ListU.{u} A
    consU    10  .constructorM, arity 1,  Π A : Sort u, A → ListU.{u} A →
                                          ListU.{u} A
    ListU.rec 11 .recursorM,    arity 2   (05 §11 AnySort: the motive's
                                          level is the suffix parameter,
                                          recArity ∈ {nU, nU+1} = {1,2})

`nparams = 1`, `nindices = 0`, `nMinors = 2`, `kinds = [.plain,
.directRec]`. Indices are already exercised by `Vec` at `nU = 0`; a
polymorphic INDEXED family would exercise both at once and cost roughly
twice as much, so it is not built.

NO `IotaWitness` LITERAL IS BUILT HERE. The carrier's own witness
`wConsU` and `pin_listU_iotaTypingCert` belong to the batch that
follows the `hlsLen` field (00 §20.7 B5); a witness literal introduced
now would make `hlsLen`'s §20.4 census THIRTEEN sites instead of
TWELVE, in the batch that is declared ATOMIC. What is pinned here is
declaration content only. -/

/-- `ListU : Sort u → Sort u`. The family's own arity is `1`: the
`param 0` occurrence IS its universe argument, which is what
`exprLevelsBounded 1` checks. -/
def listUFamType : Expr Nat := .pi (.sort (.param 0)) (.sort (.param 0))

/-- `nilU : Π A : Sort u, ListU.{u} A`. The family occurrence carries
05 §2's CANONICAL vector at the family's arity, `[param 0]` — the
condition `exprFamCanonical` checks and `ctorResultParamShape` reads. -/
def listUNilType : Expr Nat :=
  .pi (.sort (.param 0)) (.app (.const 8 [.param 0]) (.bvar 0))

/-- `consU : Π A : Sort u, Π hd : A, Π tl : ListU.{u} A, ListU.{u} A`. -/
def listUConsType : Expr Nat :=
  .pi (.sort (.param 0))
    (.pi (.bvar 0)
      (.pi (.app (.const 8 [.param 0]) (.bvar 1))
        (.app (.const 8 [.param 0]) (.bvar 2))))

/-- `ListU.rec.{u,v} : Π A (P : ListU.{u} A → Sort v) (mn : P (nilU A))
      (mc : Π hd tl (ih : P tl), P (consU A hd tl))
      (major : ListU.{u} A), P major`.

Arity 2: `param 0` is the family's universe, `param 1` the 05 §11
AnySort motive level. That is the whole point of the carrier — the
recursor's level list is STRICTLY LONGER than the family's arity, so
the family-side comparands are `ls.take 1` and not `ls`. -/
def listURecType : Expr Nat :=
  .pi (.sort (.param 0))                                              -- d0 A
   (.pi (.pi (.app (.const 8 [.param 0]) (.bvar 0))                   -- d1 P
          (.sort (.param 1)))
    (.pi (.app (.bvar 0) (.app (.const 9 [.param 0]) (.bvar 1)))      -- d2 mn
     (.pi (.pi (.bvar 2)                                              -- d3 mc
            (.pi (.app (.const 8 [.param 0]) (.bvar 3))
              (.pi (.app (.bvar 3) (.bvar 0))
                (.app (.bvar 4)
                  (.app (.app (.app (.const 10 [.param 0]) (.bvar 5))
                      (.bvar 2)) (.bvar 1))))))
      (.pi (.app (.const 8 [.param 0]) (.bvar 3))                     -- d4 major
       (.app (.bvar 3) (.bvar 0))))))                                 -- body

def listUFamMember : CheckedMember := ⟨.inductiveM, 1, listUFamType, none⟩
def listUNilMember : CheckedMember := ⟨.constructorM, 1, listUNilType, none⟩
def listUConsMember : CheckedMember := ⟨.constructorM, 1, listUConsType, none⟩
def listURecMember : CheckedMember := ⟨.recursorM, 2, listURecType, none⟩

/-- The family-and-constructors prefix, rooted at `natEnv`: the
environment at which `ListU.rec` is still fresh, and the one
`recursorGroupAdmitted` is evaluated over. -/
def listUEnvPrefix : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv natEnv 8 listUFamMember) 9 listUNilMember)
    10 listUConsMember

def listUEnv : ResolvedEnv := extendEnv listUEnvPrefix 11 listURecMember

/-- 05 §5/§6/§13 telescope arithmetic, by evaluation:
`piCount` 1 / 1 / 3 / 5, and `5 = 1 + 1 + 2 + 0 + 1`
(params · motive · minors · indices · major). -/
theorem pin_listU_piCounts :
    (piCount listUFamMember.mtype, piCount listUNilMember.mtype,
      piCount listUConsMember.mtype, piCount listURecMember.mtype)
      = (1, 1 + 0, 1 + 2, 1 + 1 + 2 + 0 + 1) := rfl

/-- 00 §19.2 erratum 3 (E-arity): the family's stored type is an arity.
`Sort u → Sort u` is one, at a PARAMETER level rather than a literal. -/
theorem pin_listU_isArity : isArity listUFamMember.mtype = true := rfl

/-- The three 00 §20.6 `EnvWf.indMember` premises across the whole
group, at the prefix each member is admitted over.

The first five conjuncts are the recursor's, the arity-1 sibling of
`pin_natU_envWf_checks` (`:506`): `hlvlB` at the FAMILY's arity `1` is
FALSE (the AnySort motive level `param 1` is genuinely bound by the
recursor's own arity `2`), and `harities` accepts `nU + 1 = 2` by the
05 §11 AnySort branch while refusing `nU + 2 = 3`. The remaining six
are the family / `nilU` / `consU` layers — the checks the `EnvWf`
value of a later batch will consume, pinned here as standalone `= true`
facts rather than discovered inside a structure term. -/
theorem pin_listU_envWf_checks :
    (exprLevelsBounded listURecMember.arity listURecMember.mtype = true) ∧
      (exprLevelsBounded listUFamMember.arity listURecMember.mtype = false) ∧
      (exprFamCanonical listUEnvPrefix listURecMember.mtype = true) ∧
      (groupArityCoherent listUEnvPrefix listURecMember = true) ∧
      (groupArityCoherent listUEnvPrefix
        { listURecMember with arity := 3 } = false) ∧
      (exprLevelsBounded listUFamMember.arity listUFamMember.mtype = true) ∧
      (exprFamCanonical natEnv listUFamMember.mtype = true) ∧
      (exprLevelsBounded listUNilMember.arity listUNilMember.mtype = true) ∧
      (exprFamCanonical (extendEnv natEnv 8 listUFamMember)
        listUNilMember.mtype = true) ∧
      (exprLevelsBounded listUConsMember.arity listUConsMember.mtype = true) ∧
      (exprFamCanonical
        (extendEnv (extendEnv natEnv 8 listUFamMember) 9 listUNilMember)
        listUConsMember.mtype = true) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- THE CANONICAL VECTOR AT A NON-ZERO `k` (00 §20.7 A4). This is the
CONCLUSION of `map_instLevel_canonical` (`RcicLevelCalc.lean:257-259`)
at `k := listUFamMember.arity = 1` and a two-element `ls`, i.e. the
first place in this tree where that lemma says anything at all: at
family arity 0 its conclusion is `[] = ls.take 0` for every `ls`, and
`hnU : k ≤ ls.length` is free.

The second conjunct is the control, and it is the arity-≥1 sibling of
`pin_natU_hmajorTy_needs_take` (`:409`): the UNTRUNCATED comparand is
FALSE here. `ls = [zero, succ zero]` is chosen with two DISTINCT
levels precisely so that it can be — at `ls = [param 0, param 0]` the
control would pass for the wrong reason. -/
theorem pin_listU_canonical_take :
    (((List.range listUFamMember.arity).map Level.param).map
          (instLevel [Level.zero, Level.succ Level.zero])
        = ([Level.zero, Level.succ Level.zero] : List Level).take
            listUFamMember.arity) ∧
      (((List.range listUFamMember.arity).map Level.param).map
          (instLevel [Level.zero, Level.succ Level.zero])
        ≠ ([Level.zero, Level.succ Level.zero] : List Level)) :=
  ⟨rfl, by decide⟩

/-- The `consU` parameter list and field values. Chosen for syntactic
shape, like every other redex argument in this file: nothing here
claims to be well-typed at its slot (the header says so and means it),
and neither `IotaWitness` nor `IotaTyping` mentions `HasTy`. -/
def listUParam : Expr Nat := .sort .zero
def listUParams : List (Expr Nat) := [listUParam]
def listUHead : Expr Nat := .const 9 [.param 0]
def listUTail : Expr Nat := .app (.const 9 [.param 0]) listUParam
def listUFields : List (Expr Nat) := [listUHead, listUTail]

/-- `consU`'s telescope after its parameter: `Π hd : A, Π tl : ListU A,
ListU A` at `A := listUParam`. -/
def listUConsAfterParams : Expr Nat :=
  .pi (.sort .zero)
    (.pi (.app (.const 8 [.param 0]) (.sort .zero))
      (.app (.const 8 [.param 0]) (.sort .zero)))

/-- The comparand objects of `pin_listU_shortLs_comparand` are the
CARRIER's, not hand-built: this is `IotaTyping.hctorAfter`'s own
`applyTel` at the declared parameter list. -/
theorem pin_listU_consAfterParams :
    applyTel listUParams listUConsType = some listUConsAfterParams := rfl

/-- THE PIN THAT MEASURES THE HOLE (00 §20.7 A5). `hfamSpineExact`
(`RcicDeclarative.lean:958-960`) compares the `.directRec` domain's
head universe list against `w.ls.take w.famMember.arity`. NOTHING in
`IotaWitness` constrains `w.ls` — not even its length — so a witness of
this carrier record-updated to `ls := []` has every other field intact
while this comparand becomes `[].take 1 = []` against a stored head
that still carries `[param 0]`.

BOTH conjuncts run on the RAW predicate, at family arity 1, with the
LEVEL LIST the only thing moving between them: the first is the short
`ls`, the second the honest two-element one. This is the only pin in
the segment that reaches the comparand itself; a recognizer pin
(`iotaReductCert … = none`) is the FIELD GUARD that closes the hole and
never evaluates an `IotaTyping` field, so the two are not the same
object and neither substitutes for the other.

`kinds` is `[.plain, .directRec]`, not `[.directRec]`: `consU` has
`nparams = 1`, `piCount = 3`, hence `nfields = 2`, and
`directRecFamilySpineExact` (`:695-708`) pairs the kind list with the
telescope's Π-domains POSITIONALLY, so at `[.directRec]` the first
domain it meets is the PLAIN field's type, whose `(appsSpine A).1` is
not a `.const`: both comparands would evaluate `false`, the second
conjunct would not close, and the first would pass for a SHAPE
mismatch rather than for the level list. The `List` group is the exact
precedent (`wCons.kinds := [.plain, .directRec]`, `:601`). -/
theorem pin_listU_shortLs_comparand :
    directRecFamilySpineExact 8 (([] : List Level).take 1) 1
        listUParams [.plain, .directRec] listUConsAfterParams
        listUFields = false
      ∧ directRecFamilySpineExact 8
          ([Level.param 0, Level.param 1].take 1) 1
          listUParams [.plain, .directRec] listUConsAfterParams
          listUFields = true :=
  ⟨by decide, by decide⟩

/-! ## 6. RECURSOR-GROUP ADMISSION, DECIDED (00 §20.7 batch B1)

`recursorGroupAdmitted` (`RcicAdmit.lean`) is the declared `Bool` that
05 §11–13 admission checks at recursor-add, from the prefix env, the
recursor's ref and its checked member — and from nothing else. This
section EVALUATES it at every carrier this file builds, positively and
negatively. It builds no `IotaWitness` and states no theorem about the
bundle: `RecursorGroupIdxAdmitted.ofAdmitted`, the five bundle values
and the `EnvWf` inhabitants they unlock are the batch after the
transport lemmas.

WHAT A GREEN HERE IS AND IS NOT EVIDENCE FOR. The Bool is a SUFFICIENT
condition for admission and not a required one (00 §20.7 D13), and
`= true` at a carrier says the declaration passes the check — not that
every honest 05 declaration would (00 §20.7 R-9, out of scope). The
two `= false` pins are the ones that show the check REFUSES, and they
are the reason conjunct 0 looks each constructor up by ref instead of
trusting the recursor's own type. -/

/-- The three 00 §20.6 `EnvWf.indMember` premises over the `Vec` triple,
each at the prefix its member is admitted over, plus the recursor's own
at `vecEnvPrefix`.

TRIPWIRE, DISCHARGED (00 §20.7 FIXTURE PINS): before this batch no pin
in this file exercised `hlvlB` / `hcanon` / `harities` on the `Vec`
members at all — `pin_natU_envWf_checks` (`:506`) covers `natRecMemberU`
and nothing else — so the `EnvWf vecEnvPrefix` term of a later batch
would have been the first place they were ever evaluated, inside a
structure whose failure mode is an opaque elaboration error. They are
standalone `= true` pins first, on purpose. `Vec`'s members are all
arity 0, so `hlvlB` is the statement that their stored types mention no
`param` at all. -/
theorem pin_vec_hlvlB :
    (exprLevelsBounded vecFamMember.arity vecFamMember.mtype = true) ∧
      (exprLevelsBounded vecNilMember.arity vecNilMember.mtype = true) ∧
      (exprLevelsBounded vecConsMember.arity vecConsMember.mtype = true) ∧
      (exprLevelsBounded vecRecMember.arity vecRecMember.mtype = true) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- 05 §2 canonicity of every already-admitted family occurrence, at each
`Vec` layer. At family arity 0 the canonical vector is `[]`, so this is
the statement that no `Vec` occurrence carries a universe argument. -/
theorem pin_vec_hcanon :
    (exprFamCanonical natEnv vecFamMember.mtype = true) ∧
      (exprFamCanonical (extendEnv natEnv 4 vecFamMember)
        vecNilMember.mtype = true) ∧
      (exprFamCanonical (extendEnv (extendEnv natEnv 4 vecFamMember) 5
        vecNilMember) vecConsMember.mtype = true) ∧
      (exprFamCanonical vecEnvPrefix vecRecMember.mtype = true) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- 05 §3 group arity coherence at each `Vec` layer. The recursor's
conjunct is the `nU`-branch of the AnySort disjunction (`Vec.rec` has
arity 0, like its family), the one `recursorGroupAdmitted`'s c0b
recomputes WITHOUT an env lookup. -/
theorem pin_vec_harities :
    (groupArityCoherent natEnv vecFamMember = true) ∧
      (groupArityCoherent (extendEnv natEnv 4 vecFamMember)
        vecNilMember = true) ∧
      (groupArityCoherent (extendEnv (extendEnv natEnv 4 vecFamMember) 5
        vecNilMember) vecConsMember = true) ∧
      (groupArityCoherent vecEnvPrefix vecRecMember = true) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `N.rec` is admitted: `nparams = 0`, `nindices = 0`, family arity 0.
The enumeration's arithmetic guard is a singleton here (`np + ni = 0`),
so the `majorTyExpr` comparison does no discriminating work at this
carrier and is not evidence that it can. -/
theorem pin_nat_groupAdmitted :
    recursorGroupAdmitted natEnvPrefix 3 natRecMember = true := rfl

/-- The LARGE-ELIMINATING recursor is admitted at the same family:
`m.arity = 1`, `nU = 0`, so c0b passes through its `nU + 1` branch —
the 05 §11 AnySort arm, and half of the level-arity fix. The family
half of the hole is closed by the head read alone: `nU` is
`lsF.length`, read off the last domain, so it cannot disagree with
`w.famMember.arity` for a legal witness. -/
theorem pin_natU_groupAdmitted :
    recursorGroupAdmitted natEnvPrefix 3 natRecMemberU = true := rfl

/-- `L.rec` is admitted: `nparams = 1`. The enumeration has TWO
candidates satisfying `np + ni = 1` and the `majorTyExpr` equality cuts
them to one — the first carrier at which it does any work. -/
theorem pin_list_groupAdmitted :
    recursorGroupAdmitted listEnvPrefix 3 listRecMember = true := rfl

/-- `Vec.rec` IS ADMITTED — the indexed carrier, `nparams = 1`,
`nindices = 1`, `nMinors = 2`.

This is the pin 00 §20.5's carrier work has been pointing at since
erratum 5: the declared conjunct 7 (`hminTel`'s declared form) holds AT
AN OPEN MOTIVE `Mtv = .bvar (nMinors + nfields)` on the re-based
identity spine, where `minorTel` emits `lift 0 1 M` / `lift 0 2 M` and
`applyTel` cancels one lift per consumed minor binder. Before this
batch that was an evaluation in an off-tree term model; here it is
`rfl`. Three of the enumeration's 49 candidates satisfy `np + ni = 2`
and the `majorTyExpr` equality cuts those three to one. -/
theorem pin_vec_groupAdmitted :
    recursorGroupAdmitted vecEnvPrefix 7 vecRecMember = true := rfl

/-- THE ARITY-≥1 PIN (00 §20.7 A3). This is the only one of the five
that can decide the level half: at `nU = 1` the canonical vector is
`[param 0]` and not `[]`, so c0a compares a non-empty list, c0b passes
through `m.arity = nU + 1 = 2`, conjunct 8b's `decide (lsA = ls)` reads
a level list that is genuinely there, and conjunct 10's
`decide (lvls = (List.range nU).map Level.param)` is discriminating
rather than indiscriminate. A green on the other four is compatible
with a declared form whose level side is wrong; this one is not. -/
theorem pin_listU_groupAdmitted :
    recursorGroupAdmitted listUEnvPrefix 11 listURecMember = true := rfl

/-- `vecEnvPrefix` with `vcons` REMOVED — literally `vecEnvPrefix`'s own
immediate sub-term (`:1030-1032`), which is already `none` at ref 6 and
agrees with `vecEnvPrefix` everywhere else by `extendEnv`'s definition
(`:211-212`). A member is removed by REBUILDING the chain, not by a
record update: `ResolvedEnv` has exactly one field (`:205-206`), so
`{ vecEnvPrefix with members := … }` would elaborate and buy nothing
the sub-term does not already give. -/
def vecEnvPrefixNoCons : ResolvedEnv :=
  extendEnv (extendEnv natEnv 4 vecFamMember) 5 vecNilMember

/-- REF FREEDOM, EXHIBITED (half 1). Conjunct 0 of
`recursorGroupAdmittedAt` looks the constructor up at
`familyRef + 1 + ctorIdx` for EVERY `ctorIdx ∈ List.range nMinors`, so
a recursor whose group is not fully present is REFUSED — here at
`ctorIdx = 1`, ref 6.

WITHOUT that per-constructor lookup the Bool would be `true` on this
environment, and that is derived rather than asserted: every conjunct
that mentions a constructor reads it through `m_c`, and the top level's
own conjuncts (c0a, c0b, c0c, c0e) read only `m` and `r` — so they
evaluate here exactly as they do at `vecEnvPrefix`, where
`pin_vec_groupAdmitted` says the whole Bool is `true`. A bundle
recorded on such an env would then be
REFUTABLE — a witness in an extension may supply ANY member at ref 6 —
and not merely unprovable. That is why conjunct 0 is the ref-freedom
fix and why a separate `groupCtorsPresent` conjunct is not needed: it
would refuse only earlier. -/
theorem pin_vec_admitted_needs_ctor :
    recursorGroupAdmitted vecEnvPrefixNoCons 7 vecRecMember = false := rfl

/-- A DECOY `vcons`: `Π A, Π n : N, Π hd : N, Π tl : Vec A n,
Vec A (succ n)`. Same `piCount` (4), same result head, same field
KINDS (`[.plain, .plain, .directRec]`), same parameter domain — only
the second field's type moved, from the parameter `A` to `N`. -/
def vecConsDecoyType : Expr Nat :=
  .pi (.sort (.succ .zero))                                   -- A
    (.pi (.const 0 [])                                         -- n  : N
      (.pi (.const 0 [])                                       -- hd : N  ← decoy
        (.pi (.app (.app (.const 4 []) (.bvar 2)) (.bvar 1))   -- tl : Vec A n
          (.app (.app (.const 4 []) (.bvar 3))                 -- Vec A (succ n)
            (.app (.const 2 []) (.bvar 2))))))

def vecConsDecoyMember : CheckedMember :=
  ⟨.constructorM, 0, vecConsDecoyType, none⟩

/-- `vecEnvPrefix` with the decoy at ref 6 in place of `vcons`. -/
def vecEnvPrefixDecoy : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv natEnv 4 vecFamMember) 5 vecNilMember)
    6 vecConsDecoyMember

/-- REF FREEDOM, EXHIBITED (half 2). The member at ref 6 is PRESENT and
well-shaped — same `piCount`, same result head, same kind list, so
conjuncts 0–5 all pass — and admission still refuses it.

MEASURED, not predicted: the first conjunct to refuse is CONJUNCT 7,
the declared `minorTel` equation, exactly as 00 §20.7 expected. Every
other conjunct of `recursorGroupAdmittedAt` evaluates `true` at this
decoy, including 9 (`recCtorParamAlign`, which compares the PARAMETER
domains and the decoy does not move) and 11d. Read at the honest
`vecConsType` the same eleven conjuncts are all `true`; the decoy flips
exactly one. That is the whole content of the ref-freedom hazard: a
constructor the recursor's stored type cannot distinguish, distinguished
by the minor telescope the recursor declares for it. -/
theorem pin_vec_admitted_refuses_decoy :
    recursorGroupAdmitted vecEnvPrefixDecoy 7 vecRecMember = false := rfl

/-! ### 6.1 The level-arity field `hlsLen` (00 §20.7 batch B2)

`IotaWitness` gained ONE field in this batch —
`hlsLen : ls.length = recMember.arity` (`RcicDeclarative.lean`) — and
the certifying ι recognizer (`iotaReductCertFillIdx`,
`RcicParRedSortWall.lean`) gained the matching decidable guard,
discharged inside `iotaReductCert_of` from `w.hlsLen`, so the
recognizer and the relation stay in step and completeness is preserved.

WHAT THE FIELD IS FOR. `IotaTyping.hfamSpineExact` and `hminTel` (the
latter through `iotaMdom`) read `w.ls.take w.famMember.arity`, and the
only route to that truncation is `map_instLevel_canonical`
(`RcicLevelCalc.lean`), whose premise is `famMember.arity ≤ ls.length`.
NOTHING in `IotaWitness` supplied it: before this batch `ls` occurred
at exactly two non-comment positions in the structure body — its own
declaration and inside `hctorAfter`, where it constrains
`ctorAfterParams` GIVEN `ls`, not `ls`. So at family arity ≥ 1 a
witness record-updated to a short `ls` kept every other field and
falsified `hfamSpineExact`, and `RecursorGroupIdxAdmitted` — a Π over
EVERY witness of the recursor — was uninhabitable for that reason
alone. `pin_listU_shortLs_comparand` (§5) is the measurement of that
hole; the two recognizer pins below are the GUARD that closes it, and
they are NOT the same object: a recognizer builds an `IotaWitness` and
never evaluates an `IotaTyping` field.

WHAT IT COSTS. Adding a required field to a `structure … : Type where`
strictly REMOVES inhabitants, so this narrows `DerivedIota`, hence
`Step.iota`, `ParRed.iotaSpine` and `Conv`. No 00 §19.2 row flips;
`IotaPreserve`'s SUBJECT narrows, and the redexes it loses are exactly
those whose recursor head carries the wrong number of universe
arguments — the ones 02 §8 `HasTy.const`'s `hlen` already rejects, so
the narrowing is 05-faithful. The JUDGMENT FOOTPRINT rows are recorded
with this batch in `RcicFoundationSeal.lean`'s comment block. -/

/-- THE COST MEASUREMENT, SEALED RATHER THAN LEFT IN PROSE (00 §20.7).
`hlsLen` holds by `rfl` at all SIX pre-existing `IotaWitness` literals:
five carry `ls := []` against an arity-0 recursor (`natRecMember`,
`listRecMember`, `vecRecMember`), and `wSuccU` carries `ls := [.param
0]` against `natRecMemberU`, whose arity is 1. No literal's `ls` was
adjusted to make the field hold — that is what `rfl` says here and
what a proof reading `w.hlsLen` back would not.

The four record-UPDATES in this file — `wSuccBadLs`, `wConsBadLs`
(`lsC`), `wConsBadParams` (`ctorParams`) and `wVconsBadIdx`
(`preMajor`) — touch neither `ls` nor `recMember`, so they inherit the
field with no edit. That is why the 00 §20.4 census of this field is
TWELVE literal sites and not sixteen. -/
theorem pin_hlsLen_witness_literals :
    (wSucc.ls.length = wSucc.recMember.arity) ∧
      (wZero.ls.length = wZero.recMember.arity) ∧
      (wSuccU.ls.length = wSuccU.recMember.arity) ∧
      (wCons.ls.length = wCons.recMember.arity) ∧
      (wNil.ls.length = wNil.recMember.arity) ∧
      (wVcons.ls.length = wVcons.recMember.arity) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `wSuccU` redex's argument list, named so that the recognizer
pin below can move the HEAD's level list and nothing else.
`iotaLhsOf w = recCall (.const w.recRef w.ls) w.preMajor (ctorMajor w)`
and `wSuccU.recRef = 3`, `wSuccU.ls = [.param 0]`, so
`foldApps (.const 3 [.param 0]) natURedexArgs` IS `iotaLhsOf wSuccU` —
measured `true` by `==` at the pre-field head, and the reason the pin
is stated on an explicit argument list rather than on
`{ wSuccU with ls := [] }`: after this batch that record update does
not elaborate at all, since the inherited `hlsLen` would have to read
`([] : List Level).length = natRecMemberU.arity`, i.e. `0 = 1`. That
impossibility is the point of the field, not an obstacle to pinning
it. -/
def natURedexArgs : List (Expr Nat) := wSuccU.preMajor ++ [ctorMajor wSuccU]

/-- THE FIELD GUARD AT FAMILY ARITY 0 (00 §20.7 A5). The `natU` group's
family has arity 0, so `map_instLevel_canonical` is free there and a
short `ls` falsifies no `IotaTyping` field: what this pin exhibits is
the NEW FIELD refusing a redex, and it is named what it is.

MEASURED, not predicted: at the head before this batch the same
expression evaluated `isSome = true` — every other recognizer guard
passes on it, because `instantiateLevels [] X = X` leaves `hminDom` and
`hctorAfter` intact and `hmajorTy` is read off the RAW recursor
domains. So the `none` here is the level-arity guard's doing and
nothing else's. -/
theorem pin_lsLen_refuses_shortLs :
    iotaReductCert natEnvU
        (foldApps (.const 3 ([] : List Level)) natURedexArgs) = none := rfl

/-- The `consU` redex over `listUEnv`: one parameter, a motive, two
minors, no indices, and the major `consU A hd tl`. Chosen for
syntactic shape like every other redex argument in this file — the
recognizer checks positions, lengths and telescope shapes, never
typing. The field values are the CARRIER's (`listUParams`,
`listUFields`, §5), so the pin below moves only the head's level
list. -/
def listUMotiveArg : Expr Nat :=
  .lam (.app (.const 8 [.param 0]) listUParam) (.sort .zero)
def listUMinorN : Expr Nat := .const 9 [.param 0]
def listUMinorC : Expr Nat := .const 10 [.param 0]
def listUMajor : Expr Nat :=
  foldApps (.const 10 [.param 0]) (listUParams ++ listUFields)
def listURedexArgs : List (Expr Nat) :=
  [listUParam, listUMotiveArg, listUMinorN, listUMinorC, listUMajor]

/-- THE FIELD GUARD AT THE ARITY WHERE THE HOLE BITES (00 §20.7 A5).
The same object as `pin_lsLen_refuses_shortLs` one arity up: an
`iotaReductCert … = none` pin, i.e. the recognizer, at a family of
arity 1 whose recursor has arity 2. Strictly more than the `natU` pin
gives — here a short `ls` really does falsify `hfamSpineExact`, which
`pin_listU_shortLs_comparand` measures — and strictly less than the
hole, which no recognizer evaluates.

MEASURED, not predicted, at the head before this batch: this same
expression evaluated `isSome = true`, and so did the honest
`foldApps (.const 11 [.param 0, .param 1]) listURedexArgs`. The second
still does after the field (`#eval` guard at the tail of this file), so
the `none` here separates the two by the LEVEL LIST alone and not by a
shape mismatch — the half-green failure mode 00 §20.7 names for the
comparand pin, checked for here too. -/
theorem pin_listU_shortLs_refused :
    iotaReductCert listUEnv
        (foldApps (.const 11 ([] : List Level)) listURedexArgs) = none := rfl

/-! ## 7. THE BUNDLE, INHABITED (00 §20.7 batch B5)

`RecursorGroupIdxAdmitted.typing` is a Π over `E'`, `hext`, `hrec`, `w`
and two equations. No `iotaTypingCert` pin above discharges it — a value
at ONE `w` cannot serve a Π over `w`, which is why §4.2 said what it
said and why removing a refutation was never producing an inhabitant.
What discharges it is `iotaTyping_of_admitted` (`RcicAdmit.lean`), a
THEOREM over every witness, and the five values below are it applied
through the smart constructor `.ofAdmitted` at the five carriers, each
`rfl` on the declared `Bool` §6 already pinned.

WHAT THIS SECTION CHANGES, AND WHAT IT DOES NOT. `EnvWf` gains
inhabitants over an INDEXED family (`vecEnv`) and over a
UNIVERSE-POLYMORPHIC one (`listUEnv`), so the `EnvWf`-conditioned
discharges of 00 §20.6 and of erratum 6 stop being vacuous AT A
CARRIER. No 00 §19.2 row flips: `IotaPreserve` stays CONDITIONAL on
`FamAppConvInj` + `CtxWf`, `SortConvChar` / `PiConvInj` /
`FamAppConvInj` stay open on F-05b's own wall, and `closure_claim`
stays `0`. (`LitPreserve` left that list in segment 7a — discharged
VACUOUSLY, 00 §19.7 E-LitP — and stays off it: DT-017's `HasTy.lit`
discharged it FOR REAL, `litPreserve`, 00 §20.11.) -/

/-! ### 7.1 The five bundles, from the declared Bool

Each is `.ofAdmitted rfl` — the `rfl` is §6's `= true` pin inlined, so
the value and the pin cannot drift apart. The `natU` line is the one
that answers the instruction in `pin_natU_levels_derived`'s docstring
(§1.3), and the `listU` line is the only one at family arity ≥ 1. -/

def natRecAdmitted : RecursorGroupIdxAdmitted natEnvPrefix 3 natRecMember :=
  .ofAdmitted rfl

def natURecAdmitted : RecursorGroupIdxAdmitted natEnvPrefix 3 natRecMemberU :=
  .ofAdmitted rfl

def listRecAdmitted : RecursorGroupIdxAdmitted listEnvPrefix 3 listRecMember :=
  .ofAdmitted rfl

def vecRecAdmitted : RecursorGroupIdxAdmitted vecEnvPrefix 7 vecRecMember :=
  .ofAdmitted rfl

def listURecAdmitted :
    RecursorGroupIdxAdmitted listUEnvPrefix 11 listURecMember :=
  .ofAdmitted rfl

/- RETIRED. `natEnvWfAt`, `pin_envWf_nat`, `listEnvWfAt`, `pin_envWf_list`,
`vecEnvWfPrefixAt`, `vecEnvWfAt`, `pin_envWf_vec0`, `pin_envWf_vec`,
`listUEnvWfPrefixAt`, `listUEnvWfAt`, `pin_envWf_listU0`, `pin_envWf_listU`
require `EnvWf` of `natRecMember` or of an environment that contains it.
05 §11 does not admit that fixed `Sort 1` motive. `natEnvUWfAt` and
`pin_envWf_natU` stay, and move to the module that has `natGroupRecursor`. -/

/-! ### 7.4 `wConsU` — the polymorphic carrier's own witness

The `listU` group's ONLY `IotaWitness` literal, and it could not land
earlier: a witness literal in batch B1 would have made `hlsLen`'s
§20.4 census THIRTEEN sites instead of TWELVE, in the batch that is
declared ATOMIC. It is written COMPLETE, with `hlsLen` already in it.

`ls := [.param 0, .param 1]` is the HONEST instance the recognizer pin
`pin_listU_shortLs_refused` (§6.1) contrasts its short-`ls` lhs with:
`ls.length = 2 = listURecMember.arity`, so `hlsLen` holds, and
`ls.take listUFamMember.arity = [.param 0]` is a GENUINE truncation of
a two-element list — the first witness in this file where
`map_instLevel_canonical` is read at a non-zero `k`. At this `ls` the
recursor-side view is the identity (`instantiateLevels [.param 0,
.param 1]` fixes every level these stored types mention), so
`ctorAfterParams` IS `listUConsAfterParams`, the object §5 already
pinned as `applyTel listUParams listUConsType`; the carrier's comparand
pin and its witness therefore name the same term rather than two
hand-built ones. -/
def listUPreMajor : List (Expr Nat) :=
  [listUParam, listUMotiveArg, listUMinorN, listUMinorC]

def listURecDoms : List (Expr Nat) :=
  [ .sort (.param 0)
  , .pi (.app (.const 8 [.param 0]) (.bvar 0)) (.sort (.param 1))
  , .app (.bvar 0) (.app (.const 9 [.param 0]) (.bvar 1))
  , .pi (.bvar 2) (.pi (.app (.const 8 [.param 0]) (.bvar 3))
      (.pi (.app (.bvar 3) (.bvar 0))
        (.app (.bvar 4)
          (.app (.app (.app (.const 10 [.param 0]) (.bvar 5)) (.bvar 2))
            (.bvar 1)))))
  , .app (.const 8 [.param 0]) (.bvar 3) ]

/-- Witness F: `ListU.rec.{u,v} A P mn mc (consU A hd tl)` — the
arity-1-family redex. `kinds = [.plain, .directRec]`, `nparams = 1`,
`nindices = 0`, `nMinors = 2`, and the recursor's level list is
STRICTLY LONGER than the family's arity. -/
def wConsU : IotaWitness listUEnv where
  recRef := 11
  ctorRef := 10
  ls := [.param 0, .param 1]
  lsC := [.param 0]
  recMember := listURecMember
  ctorMember := listUConsMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := listUPreMajor
  fields := listUFields
  ctorParams := listUParams
  kinds := [.plain, .directRec]
  minor := listUMinorC
  hlen := rfl
  familyRef := 8
  famMember := listUFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 1
  nindices := 0
  nMinors := 2
  ctorIdx := 1
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms :=
    [ .sort (.param 0)
    , .bvar 0
    , .app (.const 8 [.param 0]) (.bvar 1) ]
  ctorResult := .app (.const 8 [.param 0]) (.bvar 2)
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := listURecDoms
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := listUConsAfterParams
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- The redex `wConsU` names is the one §6.1's recognizer pin moves the
level list of: `iotaLhsOf wConsU` IS `foldApps (.const 11 ls)
listURedexArgs` at the honest `ls`. So `pin_listU_shortLs_refused`'s
`none` and this witness differ in the LEVEL LIST alone. -/
theorem pin_listU_redex_shape :
    iotaLhsOf wConsU
      = foldApps (.const 11 [Level.param 0, Level.param 1]) listURedexArgs :=
  rfl

/-- THE POLYMORPHIC CARRIER'S T-CLASS PIN (00 §20.7). The R-class
recognizer accepts the arity-1-family witness: every `IotaTyping` guard
evaluates at a carrier whose family arity is not `0`, so the level half
of the bundle is exercised by a cert and not only by a theorem. It is
evidence about ONE `w`; `listURecAdmitted` (§7.1) is the Π over all of
them, and neither substitutes for the other. -/
theorem pin_listU_iotaTypingCert : (iotaTypingCert wConsU).isSome = true := rfl

/-! ### 7.5 REF FREEDOM, EXHIBITED AT THE JUDGMENT (00 §20.7 D5)

§6's `pin_vec_admitted_refuses_decoy` shows the declared `Bool` refusing
the decoy environment. That is evidence about the BOOL. This subsection
is the other half, and the one D5 conditions its "EXHIBITED" verdict
on: over `vecEnvDecoy` the decoy constructor yields a LEGAL
`IotaWitness` — every one of its fifty-one fields discharged at the
literal, `rfl` but for `hidx` — whose `IotaTyping` is REFUTED, by
`hminTel` and by that field alone. So a bundle recorded against a prefix env whose
ref 6 the extension may re-fill is not merely unprovable but FALSE, and
conjunct 0 of `recursorGroupAdmittedAt` is what closes it.

This is the direct analogue of the DELETED `pin_vec_iotaTyping_refuted`
(§4.2), at the ref-freedom hazard instead of the erratum-5 one. -/

/-- `vecEnvPrefixDecoy` extended at ref 7 with the HONEST `Vec.rec`:
the recursor's stored type cannot tell the decoy from `vcons`, which is
the whole point. -/
def vecEnvDecoy : ResolvedEnv := extendEnv vecEnvPrefixDecoy 7 vecRecMember

/-- `wVcons` over a DIFFERENT environment, so it cannot be a record
update — a full literal, and the largest single item in this batch.
FIFTY-ONE
fields, because it is written after `hlsLen` (batch B2); `hlsLen` is
`rfl` here — `vecEnvDecoy` keeps `vecRecMember` at ref 7 (arity 0) and
the witness keeps `ls := []` — so the decoy is unaffected by that
field.

Only THREE fields differ from `wVcons`: `ctorMember` (the decoy),
`ctorDoms` (its second field domain is `N`, not the parameter `A`) and
`ctorAfterParams` (the same, after `applyTel`). The kind list, the
result, the arithmetic, the recursor side and every field VALUE are
`wVcons`'s. -/
def vecConsDecoyAfterParams : Expr Nat :=
  .pi (.const 0 [])
    (.pi (.const 0 [])
      (.pi (.app (.app (.const 4 []) (.sort .zero)) (.bvar 1))
        (.app (.app (.const 4 []) (.sort .zero))
          (.app (.const 2 []) (.bvar 2)))))

def wVconsDecoy : IotaWitness vecEnvDecoy where
  recRef := 7
  ctorRef := 6
  ls := []
  lsC := []
  recMember := vecRecMember
  ctorMember := vecConsDecoyMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [vecParam, vecMotiveArg, vecMinorN, vecMinorC, vecMajorIdx]
  fields := [vecFieldN, vecFieldHd, vecFieldTl]
  ctorParams := [vecParam]
  kinds := [.plain, .plain, .directRec]
  minor := vecMinorC
  hlen := rfl
  familyRef := 4
  famMember := vecFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 1
  nindices := 1
  nMinors := 2
  ctorIdx := 1
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms :=
    [ .sort (.succ .zero)
    , .const 0 []
    , .const 0 []
    , .app (.app (.const 4 []) (.bvar 2)) (.bvar 1) ]
  ctorResult :=
    .app (.app (.const 4 []) (.bvar 3)) (.app (.const 2 []) (.bvar 2))
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := vecRecDoms
  recBody := .app (.app (.bvar 4) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := vecConsDecoyAfterParams
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- THE PIN THAT TURNS "CONSTRUCTIBLE" INTO "EXHIBITED" (00 §20.7 D5).

`wVconsDecoy` is a LEGAL `IotaWitness` — all fifty-one fields hold, and
every one but the three named above is `wVcons`'s verbatim. Its
`IotaTyping` cannot exist: `hmotive` forces `motive = vecMotiveArg`,
`hminDom` forces `mdom` to the recursor's OWN minor domain `vecMdom`
(the recursor side is untouched by the decoy, so this is the very same
`applyTel` `pin_vec_hminDom` pins), and `hminTel` then asserts
`vecMdom = iotaMdom wVconsDecoy vecMotiveArg` — false, because
`iotaMdom` reads `ctorAfterParams`, which the decoy moved.

WHAT THIS SHOWS. The recursor's stored type does not determine its
group's constructors: an extension may supply a DIFFERENT member at
ref 6 and still produce a legal witness of the SAME recursor. A bundle
that did not look the constructor up would therefore be REFUTABLE, not
merely unprovable — the ∀ in `typing` ranges over this witness too.
Conjunct 0 of `recursorGroupAdmittedAt` is the fix, and
`pin_vec_admitted_refuses_decoy` (§6) is the same hazard seen from the
Bool's side. -/
theorem pin_vec_decoy_iotaTyping_refuted :
    IotaTyping vecEnvDecoy wVconsDecoy → False := by
  intro ty
  have hmot : ty.motive = vecMotiveArg := (Option.some.inj ty.hmotive).symm
  have hpi : Expr.pi vecMdom vecRestMin = Expr.pi ty.mdom ty.restMin :=
    Option.some.inj ty.hminDom
  injection hpi with hmd _
  have hmt := ty.hminTel
  rw [← hmd, hmot] at hmt
  exact absurd hmt (by decide)

/-! ## 8. `#eval` panic guards (house style, M-002)

A failing guard PANICS, and a panic fails the build ONLY under
`LEAN_ABORT_ON_PANIC=1` (00 §19.7 E-PANIC, measured 2026-09-06: without
it five red guards left a `lake build RcicFoundation` green, `rc=0`;
with it the panicking `lean` aborts, `rc=134`). The admission-path
build (`bootstrap-chain.yml`, the `chain` job) and every acceptance
harness set that variable; a build without it evaluates these guards
as prints, not as gates. These carry no axiom footprint and cannot
enter the seal; the theorems above are the sealable half, and a guard
that must gate WITHOUT the environment variable is written as an
`example : … = true := rfl`. -/

#eval (if (iotaTypingCert wSucc).isSome then 0
  else panic "pin: iotaTypingCert succ = none")
#eval (if (iotaTypingCert wZero).isSome then 0
  else panic "pin: iotaTypingCert zero = none")
#eval (if (iotaTypingCert wCons).isSome then 0
  else panic "pin: iotaTypingCert cons = none")
#eval (if (iotaTypingCert wNil).isSome then 0
  else panic "pin: iotaTypingCert nil = none")
#eval (if (iotaTypingCert wSuccBadLs).isSome then 0
  else panic "pin: iotaTypingCert succ[lsC:=param 7] = none")
#eval (if (iotaTypingCert wConsBadParams).isSome then 0
  else panic "pin: iotaTypingCert cons[ctorParams:=junk] = none")
#eval (if (iotaReductCert natEnv (iotaLhsOf wSucc)).isSome then 0
  else panic "pin: iotaReductCert succ = none")
#eval (if (iotaReductCert listEnv (iotaLhsOf wCons)).isSome then 0
  else panic "pin: iotaReductCert cons = none")
#eval (if ctorMajor wConsBadParams == ctorMajor wCons then
    panic "pin: free ctorParams did not move ctorMajor" else 0)
#eval (if ctorMajorRec wConsBadParams == ctorMajorRec wCons then 0
  else panic "pin: ctorMajorRec moved under a free-field update")
#eval (if (iotaReductCert vecEnv (iotaLhsOf wVcons)).isSome then 0
  else panic "pin: iotaReductCert vcons = none")
#eval (if (iotaTypingCert wVcons).isSome then 0
  else panic "pin: Vec iotaTypingCert = none (minorTel conclusion regressed?)")
#eval (if vecMdom == iotaMdom wVcons vecMotiveArg then 0
  else panic "pin: Vec hminTel does not hold")
#eval (if (iotaTypingCert wVconsBadIdx).isSome then 0
  else panic "pin: Vec[preMajor idx:=junk] iotaTypingCert = none")
#eval (if (applyTel wVconsBadIdx.fields wVconsBadIdx.ctorAfterParams).map
      (familyIdx wVconsBadIdx.nparams)
    == some (wVconsBadIdx.preMajor.drop
      (wVconsBadIdx.nparams + 1 + wVconsBadIdx.nMinors)) then
    panic "pin: junk major index unexpectedly aligned" else 0)
#eval (if (iotaTypingCert wSuccU).isSome then 0
  else panic "pin: large-eliminating iotaTypingCert = none")
#eval (if (iotaReductCert natEnvU
    (foldApps (.const 3 ([] : List Level)) natURedexArgs)).isSome then
    panic "pin: short-ls natU redex still recognized (hlsLen guard gone?)"
  else 0)
#eval (if (iotaReductCert listUEnv
    (foldApps (.const 11 ([] : List Level)) listURedexArgs)).isSome then
    panic "pin: short-ls listU redex still recognized (hlsLen guard gone?)"
  else 0)
#eval (if (iotaReductCert listUEnv
    (foldApps (.const 11 [Level.param 0, Level.param 1])
      listURedexArgs)).isSome then 0
  else panic "pin: honest-ls listU redex refused (guard too strong?)")
#eval (if ctorMajorRec wSuccU == foldApps (.const 2 wSuccU.ls) [natField] then
    panic "pin: ctorMajorRec picked up the recursor's motive level" else 0)

#eval (if recursorGroupAdmitted natEnvPrefix 3 natRecMember then 0
  else panic "pin: recursorGroupAdmitted N.rec = false")
#eval (if recursorGroupAdmitted natEnvPrefix 3 natRecMemberU then 0
  else panic "pin: recursorGroupAdmitted N.rec.{u} = false")
#eval (if recursorGroupAdmitted listEnvPrefix 3 listRecMember then 0
  else panic "pin: recursorGroupAdmitted L.rec = false")
#eval (if recursorGroupAdmitted vecEnvPrefix 7 vecRecMember then 0
  else panic "pin: recursorGroupAdmitted Vec.rec = false")
#eval (if recursorGroupAdmitted listUEnvPrefix 11 listURecMember then 0
  else panic "pin: recursorGroupAdmitted ListU.rec = false (level half?)")
#eval (if recursorGroupAdmitted vecEnvPrefixNoCons 7 vecRecMember then
    panic "pin: admission did not refuse the absent constructor" else 0)
#eval (if recursorGroupAdmitted vecEnvPrefixDecoy 7 vecRecMember then
    panic "pin: admission did not refuse the decoy constructor" else 0)
#eval (if applyTel listUParams listUConsType == some listUConsAfterParams then 0
  else panic "pin: listU ctorAfterParams is not the carrier's")
#eval (if directRecFamilySpineExact 8 (([] : List Level).take 1) 1
    listUParams [.plain, .directRec] listUConsAfterParams listUFields then
    panic "pin: the short-ls comparand did not refuse" else 0)
#eval (if (iotaTypingCert wConsU).isSome then 0
  else panic "pin: the arity-1-family witness lost its IotaTyping cert")
#eval (if iotaLhsOf wConsU ==
    foldApps (.const 11 [Level.param 0, Level.param 1]) listURedexArgs then 0
  else panic "pin: wConsU is not the redex the recognizer pins move")
#eval (if vecMdom == iotaMdom wVconsDecoy vecMotiveArg then
    panic "pin: the ref-6 decoy agreed with the recursor's minor telescope"
  else 0)

/-! ### IdxFamFree teeth — compound recursive indices without the family

`recIdxFromSpineWalk`'s `.directRec` conjunct used to require every index
argument to be a `paramsFields` MEMBER, which refused any compound index
(measured on the K3c table's slot-140 `vaPair` on branch
`devin/rcic-idx-main`). It now uses `idxFamFree`: the index may be compound,
provided every de Bruijn
variable it uses is a bound `paramsFields` element and it carries no
family constant. The two teeth below are the ACCEPT / REFUSE predictions.
-/

/-- Minimal family `I` (ref 7) whose recursive field's index is the
compound `c 42 ()` — NOT a `paramsFields` member (the spine is empty) and
not mentioning the family. ACCEPTED. -/
def toothIdx : Expr Nat := .app (.const 42 []) (.sort .zero)
def toothDomain : Expr Nat := .app (.const 7 []) toothIdx

theorem tooth_compound_index_accepted :
    occursConst 7 toothIdx = false ∧
    toothIdx ∉ ([] : List (Expr Nat)) ∧
    recIdxFromSpineWalk 7 0 1 [] [.directRec]
      (.pi toothDomain (.sort .zero)) [.sort .zero] = true :=
  ⟨rfl, by simp, rfl⟩

/-- Negative control: the same shape with the index itself a family
application is REFUSED. -/
def toothBadIdx : Expr Nat := .app (.const 7 []) (.sort .zero)
def toothBadDomain : Expr Nat := .app (.const 7 []) toothBadIdx

theorem tooth_family_index_refused :
    recIdxFromSpineWalk 7 0 1 [] [.directRec]
      (.pi toothBadDomain (.sort .zero)) [.sort .zero] = false := rfl

/-- The L-K1 `vaPair` (slot 140) shape: the recursive premise's index is
the compound `mkBound (mkRef 3 16 d) b (cctP ra rb ta tb ab b d)`, built
from the bound fields `d b ra rb ta tb ab` and family-free constructors,
and NOT mentioning `ValueAt` (ref 133). Before IDX-R2 this was refused
(measured on the K3c table's slot-140 `vaPair` on branch
`devin/rcic-idx-main`); `idxFamFree` accepts it, and `declaredIdxSrc`
sources it (IDX-R2). -/
def vaD : Expr Nat := .bvar 0
def vaB : Expr Nat := .bvar 1
def vaRa : Expr Nat := .bvar 2
def vaRb : Expr Nat := .bvar 3
def vaTa : Expr Nat := .bvar 4
def vaTb : Expr Nat := .bvar 5
def vaAb : Expr Nat := .bvar 6
def vaParamsFields : List (Expr Nat) := [vaD, vaB, vaRa, vaRb, vaTa, vaTb, vaAb]
def vaMkRef : Expr Nat :=
  .app (.app (.app (.const 41 []) (.const 3 [])) (.const 16 [])) vaD
def vaCctP : Expr Nat :=
  foldApps (.const 42 []) [vaRa, vaRb, vaTa, vaTb, vaAb, vaB, vaD]
def vaIdx : Expr Nat := .app (.app (.app (.const 40 []) vaMkRef) vaB) vaCctP
def vaDomain : Expr Nat := .app (.const 133 []) vaIdx

theorem vaPair_index_accepted :
    occursConst 133 vaIdx = false ∧
    vaIdx ∉ vaParamsFields ∧
    recIdxFromSpineWalk 133 0 1 vaParamsFields [.directRec]
      (.pi vaDomain (.sort .zero)) [.sort .zero] = true :=
  ⟨rfl, by decide, rfl⟩

#print axioms tooth_compound_index_accepted
#print axioms tooth_family_index_refused
#print axioms vaPair_index_accepted

/-! ### IDX-R2 Src-evidence controls

The `IdxSrc` supplier and checks must be STRICT: each theorem below is a
prediction that could have failed, discharged by kernel evaluation on
closed constants. The first is the back-compat direction — the old
simple `.pos` path still accepts a single-field index — and the rest are
refusals: wrong provenance, a family constant inside the index, a wrong
index count, a wrong `idxSrcTy` alignment, and an unsourced junk leaf. -/

/-- The old simple single-field index still travels the `.pos` path:
`recIdxSrcWalk` accepts `[[.pos 0]]`, the Src image of the Nat position. -/
theorem ctrl_src_pos_simple_accepted :
    recIdxSrcWalk 7 0 [(.bvar 0 : Expr Nat)] [.directRec]
      (.pi (.app (.const 7 []) (.bvar 0)) (.sort .zero)) [.bvar 1]
      [[.pos 0]] = true := rfl

/-- Wrong provenance: an index leaf that is NOT in `pf` is refused. -/
theorem ctrl_src_unsourced_bvar_refused :
    recIdxSrcBuild 7 0 [(.bvar 0 : Expr Nat)] [.directRec]
      (.pi (.app (.const 7 []) (.bvar 1)) (.sort .zero)) [.bvar 1] = none := rfl

/-- A family constant inside the index is refused. -/
theorem ctrl_src_family_inside_refused :
    recIdxSrcBuild 7 0 ([] : List (Expr Nat)) [.directRec]
      (.pi (.app (.const 7 []) (.app (.const 7 []) (.sort .zero)))
        (.sort .zero)) [.sort .zero] = none := rfl

/-- Wrong index count: a source list shorter than `familyIdx` is refused. -/
theorem ctrl_src_wrong_count_refused :
    recIdxSrcWalk 7 0 [(.bvar 0 : Expr Nat)] [.directRec]
      (.pi (.app (.const 7 []) (.bvar 0)) (.sort .zero)) [.bvar 1]
      [[]] = false := rfl

/-- Env for the alignment controls: ref 42 has arity 0 and type
`Π (_ : sort 0), sort 0`. -/
def ctrlSrcEnv : ResolvedEnv :=
  extendEnv emptyEnv 42 ⟨.definitionM, 0,
    .pi (.sort .zero) (.sort .zero), none⟩

/-- Wrong type alignment: the compound index `42 ()` has argument type
`sort 1` while `42`'s domain is `sort 0`, so `idxSrcTy` refuses the
application and the alignment is `false`. -/
theorem ctrl_src_ty_align_refused :
    idxSrcAlign 7 ctrlSrcEnv (.pi (.sort .zero) (.sort .zero))
      (.sort .zero) ([] : List (Expr Nat)) ([] : List (Expr Nat))
      [.app (.const 42 []) (.sort .zero)]
      [.app (.constNotFam 42) .sort] = false := rfl

/-- The same mismatch inside the full type walk is refused. -/
theorem ctrl_src_ty_walk_refused :
    recIdxTySrcWalk 7 ctrlSrcEnv (.pi (.sort .zero) (.sort .zero))
      (.sort .zero) 0 ([] : List (Expr Nat)) ([] : List (Expr Nat))
      [.directRec]
      (.pi (.app (.const 7 []) (.app (.const 42 []) (.sort .zero)))
        (.sort .zero)) [.sort .zero]
      [[.app (.constNotFam 42) .sort]] = false := rfl

/-- Junk leaves: an index that is an unsourced bvar is refused, so the
old junk witness does not silently become accepted. -/
theorem ctrl_src_junk_leaf_refused :
    recIdxSrcBuild 7 0 ([] : List (Expr Nat)) [.directRec]
      (.pi (.app (.const 7 []) (.bvar 0)) (.sort .zero)) [.sort .zero]
      = none := rfl

#print axioms ctrl_src_pos_simple_accepted
#print axioms ctrl_src_unsourced_bvar_refused
#print axioms ctrl_src_family_inside_refused
#print axioms ctrl_src_wrong_count_refused
#print axioms ctrl_src_ty_align_refused
#print axioms ctrl_src_ty_walk_refused
#print axioms ctrl_src_junk_leaf_refused


/-! ### IDX-R1 P1 — the recorded negative of the OLD predicate

The pre-IDX-R1 `idxFamFreeLegacy` skipped the binder BODY: the family
occurrence below is invisible to it, while `occursConst` (05 §8's full
scan) and the new depth-aware `idxFamFree` both see it. -/

theorem idxFamFreeLegacy_lam_body_true :
    idxFamFreeLegacy 7 [] (.lam (.sort .zero) (.const 7 [])) = true := rfl

theorem idxFamFreeLegacy_lam_body_occurs :
    occursConst 7 (.lam (.sort .zero) (.const 7 [])) = true := rfl

theorem idxFamFree_lam_body_refused :
    idxFamFree 7 [] (.lam (.sort .zero) (.const 7 [])) = false := rfl

/-! ### IDX-R1 controls -/

-- (a) an illegal family in each binder body (and in the Π domain / letE
-- type and value) is REJECTED.
theorem ctl_lam_body_family_refused :
    idxFamFree 7 [] (.lam (.sort .zero) (.const 7 [])) = false := rfl
theorem ctl_pi_body_family_refused :
    idxFamFree 7 [] (.pi (.sort .zero) (.const 7 [])) = false := rfl
theorem ctl_let_body_family_refused :
    idxFamFree 7 [] (.letE (.sort .zero) (.sort .zero) (.const 7 [])) = false := rfl
theorem ctl_pi_domain_family_refused :
    idxFamFree 7 [] (.pi (.const 7 []) (.sort .zero)) = false := rfl
theorem ctl_let_type_family_refused :
    idxFamFree 7 [] (.letE (.const 7 []) (.sort .zero) (.sort .zero)) = false := rfl
theorem ctl_let_value_family_refused :
    idxFamFree 7 [] (.letE (.sort .zero) (.const 7 []) (.sort .zero)) = false := rfl

-- (b) a legal local `bvar 0` (and `bvar 1` under two binders) is NOT
-- wrongly rejected.
theorem ctl_local_bvar_lam :
    idxFamFree 7 [] (.lam (.sort .zero) (.bvar 0)) = true := rfl
theorem ctl_local_bvar_pi :
    idxFamFree 7 [] (.pi (.sort .zero) (.bvar 0)) = true := rfl
theorem ctl_local_bvar_let :
    idxFamFree 7 [] (.letE (.sort .zero) (.sort .zero) (.bvar 0)) = true := rfl
theorem ctl_local_bvar_nested :
    idxFamFree 7 [] (.lam (.sort .zero) (.lam (.sort .zero) (.bvar 1))) = true := rfl

-- (c) an external variable with no provenance is rejected.
theorem ctl_external_bvar_refused :
    idxFamFree 7 [] (.bvar 0) = false := rfl
theorem ctl_external_bvar_lam_refused :
    idxFamFree 7 [] (.lam (.sort .zero) (.bvar 1)) = false := rfl

-- (d) atom provenance: a legal parameter substituted by a family-containing
-- complete atom is still accepted (the whole atom is in `pf`).
theorem ctl_atom_provenance :
    idxFamFree 7 [.const 7 []] (.const 7 []) = true := rfl
theorem ctl_atom_provenance_param :
    idxFamFree 7 [.bvar 0] (.bvar 0) = true := rfl
theorem ctl_atom_provenance_subst :
    idxFamFree 7 [.const 7 []]
      (instantiate 0 (.const 7 []) (.bvar 0)) = true := rfl
theorem ctl_atom_provenance_compound :
    idxFamFree 7 [.app (.const 42 []) (.const 7 [])]
      (.app (.const 42 []) (.const 7 [])) = true := rfl

-- (e) index counts / existing simple indices / compound applications keep
-- their prior conclusions.
theorem ctl_wrong_index_count_refused :
    recIdxFromSpineWalk 7 0 2 [] [.directRec]
      (.pi toothDomain (.sort .zero)) [.sort .zero] = false := rfl
theorem ctl_simple_param_index_accepted :
    recIdxFromSpineWalk 7 0 1 [.bvar 0] [.directRec]
      (.pi (.app (.const 7 []) (.bvar 0)) (.sort .zero)) [.sort .zero] = true := rfl

#print axioms idxFamFreeLegacy_lam_body_true
#print axioms idxFamFreeLegacy_lam_body_occurs
#print axioms idxFamFree_lam_body_refused
#print axioms ctl_lam_body_family_refused
#print axioms ctl_pi_body_family_refused
#print axioms ctl_let_body_family_refused
#print axioms ctl_pi_domain_family_refused
#print axioms ctl_let_type_family_refused
#print axioms ctl_let_value_family_refused
#print axioms ctl_local_bvar_lam
#print axioms ctl_local_bvar_pi
#print axioms ctl_local_bvar_let
#print axioms ctl_local_bvar_nested
#print axioms ctl_external_bvar_refused
#print axioms ctl_external_bvar_lam_refused
#print axioms ctl_atom_provenance
#print axioms ctl_atom_provenance_param
#print axioms ctl_atom_provenance_subst
#print axioms ctl_atom_provenance_compound
#print axioms ctl_wrong_index_count_refused
#print axioms ctl_simple_param_index_accepted

end Rcic.Declarative
