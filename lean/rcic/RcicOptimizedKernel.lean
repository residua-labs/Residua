/-
RM-024 (R1-B) — Constructive Lean `OptimizedKernel` (`docs/rcic/03_REFERENCE_MACHINE.md`
§1, §11, §14, §15: lines 12, 313, 362, 390; `research/rcic/rm/S0_RM024_025.md`;
cc ruling on #7058).

Owner text quoted before the Lean:
  - `03` §1 (`03:12`):
    "An optimized kernel may exist later only with a refinement proof to this
     machine."
  - `03` §11 (`03:303-313`):
    "The reference path is:
       check expected_type is a type
       infer expr
       ConvType(inferred_type, expected_type)
     An optimized bidirectional lambda rule may exist only in an implementation
     proven to refine this path."
  - `03` §14 (`03:350-362`):
    "An optimized q-index map is allowed only with a lookup-equivalence theorem."
  - `03` §15 (`03:390`):
    "RM-024 | optimized acceptance refines reference acceptance"
  - cc ruling on #7058 (R1 → R1-B):
    "build the Lean OptimizedKernel and prove refinement; the Wasm artifact
     becomes the named open `optimized_kernel_wasm_artifact`."

Contents:
  1. `03` §14 `QIndexMap` lookup-equivalence interface over `ResolvedEnv`
     (`QIndexMap.toEnv`, `QIndexMap.toEnv_eq`), concrete association-table
     implementation (`qTableLookup`, `QIndexMap.empty`, `QIndexMap.insert`), and
     byte-store `QByteIndexMap` lookup equivalence over `Rcic.LookupBytes.lookupBytes`
     (`RM024_qByteIndexMap_lookupBytes_equiv`).
  2. Optimized WHNF, conversion, and inference certifiers (`machineWhnfDoneOpt`,
     `whnfOptCert`, `convOptCert`, `inferOptCert_app`, `inferOptCert`) composed
     directly from canonical `machineWhnfDone`, `whnfCert`, `convCert`,
     `inferCert.inferCert_app`, `inferCert` (`RcicMachine.lean:173/186/238/412/324`)
     over `qmap.toEnv` (`members := qmap.lookup`) and transporting indexed results
     along `qmap.toEnv_eq` (`whnfOptCert_eq_whnfCert`, `convOptCert_eq_convCert`,
     `inferOptCert_app_eq_inferCert_app`, `inferOptCert_eq_inferCert`).
  3. `03` §11 bidirectional `.lam`/`.pi` check certifiers (`checkOptCert` and
     multi-binder `checkBiLamCert`), proving soundness (`RM024_checkOptCert_sound`,
     `RM024_checkBiLamCert_sound`), fuel monotonicity (`checkOptCert_mono`), and
     mutual refinement with reference `checkCert` (`checkOptCert_refines_checkCert`,
     `checkCert_refines_checkOptCert`).
  4. `OptimizedKernel` step and runner layer (`optStepRaw`, `runOptRaw`,
     `runOptRawR`, `OptEventuallyAccepts`, `OptTaskEventuallyAccepts`) and the
     RM-024 refinement theorems (`RM024_optStepRaw_accept_refines`,
     `RM024_optimized_accept_refines`, `RM024_optimized_runRaw_accept_refines`,
     `RM024_reference_accept_to_optimized`, `RM024_optimized_eventual_iff_reference`).
  5. Named open `optimized_kernel_wasm_artifact` stating in its type that the
     external compiled Wasm kernel artifact (`rcic_kernel_wasm_artifact_ref`)
     equals the WX lowering of this Lean `OptimizedKernel` into `Residua-Wasm-0`
     (`lowerOptimizedKernelModule`, `lowerOptimizedKernelBytes`,
     `lowerOptimizedKernelArtifactRef`, `LoweredOptimizedKernelCert`,
     `Rcic.WasmNorm.NormValidModule`) and executes under `Rcic.WasmNorm.NormSteps` /
     `Rcic.WasmNorm.normInit` with exact lowering equivalence to `runOptRawR K.qmap`
     (`RM024_wasm_artifact_lowering_identity`, `RM024_wasm_artifact_refines_reference`,
     `RM024_wasm_normSteps_accept_refines_reference`, `RM024_wasm_normSteps_no_trap`,
     `RM024_wasm_not_always_refused`), plus the additively preserved abstract
     runner bridge (`AbstractOptKernelRunner`, `RM024_abstract_runner_refines_reference`)
     and non-vacuity accepting/refused pins (`pin_RM024_lam_betaPi_accepts`,
     `pin_RM024_lam_fuel2_strict_gain`, `pin_RM024_qIndexMap_lookupDecl_accepts`,
     `pin_RM024_check_refused`).

`closure_claim = 0`.
-/
import rcic.RcicMachineEventual
import rcic.RcicLookupBytes
import rcic.RcicWasmNormValidate
import Residua.SHA256

namespace Rcic.Machine.Optimized

open Rcic.Declarative
open Rcic.Machine
open Rcic.Machine.Eventual
open Rcic.ScmRefinement

/-! ## 1. `03` §14 `QIndexMap` and Lookup-Equivalence Theorems (`03:362`) -/

/-- `03` §14 (`03:362`): An optimized `q`-index map for environment `E`,
    equipped with its mandatory lookup-equivalence theorem `lookupEquiv`. -/
structure QIndexMap (E : ResolvedEnv) where
  lookup : Nat → Option CheckedMember
  lookupEquiv : ∀ q : Nat, lookup q = E.members q

/-- Pointwise lookup-equivalence theorem for `QIndexMap` (`03:362`). -/
theorem RM024_qIndexMap_lookup_equiv {E : ResolvedEnv} (qmap : QIndexMap E) (q : Nat) :
    qmap.lookup q = E.members q :=
  qmap.lookupEquiv q

/-- `03` §14: The `ResolvedEnv` backed directly by `qmap.lookup`
    (`members := qmap.lookup`). Delegating canonical reference certifiers to
    `qmap.toEnv` executes `qmap.lookup` at every `.const` lookup site. -/
def QIndexMap.toEnv {E : ResolvedEnv} (qmap : QIndexMap E) : ResolvedEnv where
  members := qmap.lookup

/-- Environment equality derived from `qmap.lookupEquiv`:
    `qmap.toEnv = E`. -/
theorem QIndexMap.toEnv_eq {E : ResolvedEnv} (qmap : QIndexMap E) :
    qmap.toEnv = E := by
  cases E with
  | mk members =>
      simp only [QIndexMap.toEnv, ResolvedEnv.mk.injEq]
      funext q
      exact qmap.lookupEquiv q

/-- Proof-carrying lookup package over `QIndexMap`: returns `qmap.lookup r`
    together with the witness `qmap.lookup r = E.members r`. -/
def lookupOpt {E : ResolvedEnv} (qmap : QIndexMap E) (r : Nat) :
    Σ' (res : Option CheckedMember), res = E.members r :=
  ⟨qmap.lookup r, qmap.lookupEquiv r⟩

/-- Helper normalizing a dependent equality pair `⟨x, h⟩` to `⟨y, rfl⟩`. -/
theorem psigma_eq_rfl {α : Type} {x y : α} (h : x = y) :
    (⟨x, h⟩ : Σ' z : α, z = y) = ⟨y, rfl⟩ := by
  cases h
  rfl

/-- Helper normalizing a dependent equality pair `⟨x, h₁⟩` via `h₂ : y = z`. -/
theorem psigma_eq_of_eq {α : Type} {x y z : α} (h₁ : x = y) (h₂ : y = z) :
    (⟨x, h₁⟩ : Σ' w : α, w = y) = ⟨z, h₂.symm⟩ := by
  cases h₁
  cases h₂
  rfl

/-- Canonical normalization of `lookupOpt`: by `qmap.lookupEquiv r` and proof
    irrelevance of `=`, `lookupOpt qmap r` equals `⟨E.members r, rfl⟩`. -/
theorem lookupOpt_eq {E : ResolvedEnv} (qmap : QIndexMap E) (r : Nat) :
    lookupOpt qmap r = ⟨E.members r, rfl⟩ :=
  psigma_eq_rfl (qmap.lookupEquiv r)

/-- Specialization of `lookupOpt_eq` when `E.members r = some m`. -/
theorem lookupOpt_of_some {E : ResolvedEnv} (qmap : QIndexMap E) {r : Nat}
    {m : CheckedMember} (hm : E.members r = some m) :
    lookupOpt qmap r = ⟨some m, hm.symm⟩ :=
  psigma_eq_of_eq (qmap.lookupEquiv r) hm

/-- Specialization of `lookupOpt_eq` when `E.members r = none`. -/
theorem lookupOpt_of_none {E : ResolvedEnv} (qmap : QIndexMap E) {r : Nat}
    (hm : E.members r = none) :
    lookupOpt qmap r = ⟨none, hm.symm⟩ :=
  psigma_eq_of_eq (qmap.lookupEquiv r) hm

/-- Canonical `QIndexMap` directly wrapping `E.members`. -/
def QIndexMap.ofEnv (E : ResolvedEnv) : QIndexMap E where
  lookup := E.members
  lookupEquiv := fun _ => rfl

/-- Finite association-table lookup for `q`-indexed checked members. -/
def qTableLookup : List (Nat × CheckedMember) → Nat → Option CheckedMember
  | [], _ => none
  | (k, m) :: rest, q => if q = k then some m else qTableLookup rest q

/-- Resolved environment induced by a finite `q`-index table. -/
def envOfQTable (tbl : List (Nat × CheckedMember)) : ResolvedEnv where
  members := qTableLookup tbl

/-- `QIndexMap` for `envOfQTable tbl`. -/
def QIndexMap.ofTable (tbl : List (Nat × CheckedMember)) :
    QIndexMap (envOfQTable tbl) where
  lookup := qTableLookup tbl
  lookupEquiv := fun _ => rfl

/-- Empty `QIndexMap` over `emptyEnv`. -/
def QIndexMap.empty : QIndexMap emptyEnv where
  lookup := qTableLookup []
  lookupEquiv := fun _ => rfl

/-- Extending a `QIndexMap` when extending an environment via `extendEnv`. -/
def QIndexMap.insert {E : ResolvedEnv} (qmap : QIndexMap E)
    (r : Nat) (m : CheckedMember) : QIndexMap (extendEnv E r m) where
  lookup := fun q => if q = r then some m else qmap.lookup q
  lookupEquiv := fun q => by
    simp only [extendEnv]
    by_cases h : q = r
    · simp only [if_pos h]
    · simp only [if_neg h, qmap.lookupEquiv q]

/-- `qTableLookup ((r, m) :: tbl)` agrees pointwise with `extendEnv (envOfQTable tbl) r m`. -/
theorem RM024_qTableLookup_cons_eq_extendEnv
    (tbl : List (Nat × CheckedMember)) (r : Nat) (m : CheckedMember) (q : Nat) :
    qTableLookup ((r, m) :: tbl) q = (extendEnv (envOfQTable tbl) r m).members q :=
  rfl

/-- Byte-store `QByteIndexMap` over `Rcic.LookupBytes.StoreEntry` (`03:352-362`),
    indexing store slots by digest `ref` with a lookup-equivalence proof to
    `Rcic.LookupBytes.lookupEntry`. -/
structure QByteIndexMap (store : List Rcic.LookupBytes.StoreEntry) where
  lookupSlot : List Char → Option Rcic.LookupBytes.StoreEntry
  lookupSlotEquiv : ∀ ref : List Char,
    lookupSlot ref = Rcic.LookupBytes.lookupEntry store ref

/-- Canonical `QByteIndexMap` for any byte store `store`. -/
def QByteIndexMap.ofStore (store : List Rcic.LookupBytes.StoreEntry) :
    QByteIndexMap store where
  lookupSlot := Rcic.LookupBytes.lookupEntry store
  lookupSlotEquiv := fun _ => rfl

/-- Optimized byte-store lookup (`03` §14 + `04` §8 four-line check) using
    `qmap : QByteIndexMap store`. -/
def lookupBytesOpt (h : List Char → List Char)
    {store : List Rcic.LookupBytes.StoreEntry}
    (qmap : QByteIndexMap store) (ref : List Char) :
    Rcic.LookupBytes.LookupBytesResult :=
  match qmap.lookupSlot ref with
  | none => .refused "missing"
  | some e => Rcic.LookupBytes.lookupBytesFrom h e ref

/-- `03` §14 byte-store lookup-equivalence theorem: `lookupBytesOpt` is
    pointwise identical to the reference `Rcic.LookupBytes.lookupBytes`. -/
theorem RM024_qByteIndexMap_lookupBytes_equiv
    (h : List Char → List Char) {store : List Rcic.LookupBytes.StoreEntry}
    (qmap : QByteIndexMap store) (ref : List Char) :
    lookupBytesOpt h qmap ref = Rcic.LookupBytes.lookupBytes h store ref := by
  unfold lookupBytesOpt Rcic.LookupBytes.lookupBytes
  rw [qmap.lookupSlotEquiv ref]
  cases Rcic.LookupBytes.lookupEntry store ref <;> rfl

/-- Any member accepted by `lookupBytesOpt` satisfies the full 4-line
    `RM013_lookupBytes_accepted` rehash/decode/re-encode/profile specification. -/
def RM024_lookupBytesOpt_accepted
    (h : List Char → List Char) {store : List Rcic.LookupBytes.StoreEntry}
    (qmap : QByteIndexMap store) (ref : List Char)
    (m : Rcic.LookupBytes.LookupMember)
    (hacc : lookupBytesOpt h qmap ref = .accepted m) :
    Σ' (e : Rcic.LookupBytes.StoreEntry),
      (e ∈ store) ×' (e.ref = ref) ×'
      (h (Rcic.LookupBytes.bytesOf e) = ref) ×'
      (Rcic.LookupBytes.decodeTwo e.p0 e.p1 = some m) ×'
      (Rcic.LookupBytes.encodeMember m = Rcic.LookupBytes.bytesOf e) ×'
      (m.kind = e.kind) :=
  Rcic.LookupBytes.RM013_lookupBytes_accepted h store ref m
    ((RM024_qByteIndexMap_lookupBytes_equiv h qmap ref).symm.trans hacc)

/-! ## 2. Optimized WHNF, Conversion, and Inference Certifiers via `QIndexMap` Composition -/

/-- Optimized WHNF head-normal test (`03` §12 + §14): delegates directly to
    canonical `machineWhnfDone` (`RcicMachine.lean:173`) over `qmap.toEnv`
    (`members := qmap.lookup`). -/
def machineWhnfDoneOpt {E : ResolvedEnv} (qmap : QIndexMap E) (e : Expr Nat) : Bool :=
  machineWhnfDone qmap.toEnv e

/-- Lookup equivalence transports `machineWhnfDoneOpt` to `machineWhnfDone`. -/
theorem machineWhnfDoneOpt_eq_machineWhnfDone {E : ResolvedEnv}
    (qmap : QIndexMap E) (e : Expr Nat) :
    machineWhnfDoneOpt qmap e = machineWhnfDone E e := by
  unfold machineWhnfDoneOpt
  rw [qmap.toEnv_eq]

/-- Transport a `whnfCert E'` certificate along `heq : E' = E` inside `.ok`. -/
def whnfCertTrans {E' E : ResolvedEnv} (heq : E' = E) {n : Nat} {Γ : LCtx} {e : Expr Nat}
    (c : Cert (Σ' (w : Expr Nat), MachineRed E' n Γ e w)) :
    Cert (Σ' (w : Expr Nat), MachineRed E n Γ e w) :=
  match c with
  | .no msg => .no msg
  | .ok ⟨w, k⟩ => .ok ⟨w, heq ▸ k⟩

/-- Transporting `whnfCert E'` along `heq : E' = E` yields `whnfCert E`. -/
theorem whnfCertTrans_eq {E' E : ResolvedEnv} (heq : E' = E) (n fuel : Nat)
    (Γ : LCtx) (e : Expr Nat) :
    whnfCertTrans heq (whnfCert E' n fuel Γ e) = whnfCert E n fuel Γ e := by
  cases heq
  cases whnfCert E' n fuel Γ e with
  | no msg => rfl
  | ok c =>
      rcases c with ⟨w, k⟩
      rfl

/-- Optimized WHNF certifier (`03` §12 + §14): delegates to canonical
    `whnfCert` (`RcicMachine.lean:186`) over `qmap.toEnv` (`members := qmap.lookup`)
    and transports the indexed `MachineRed` derivation along `qmap.toEnv_eq`
    inside `.ok`. -/
def whnfOptCert {E : ResolvedEnv} (qmap : QIndexMap E) (n fuel : Nat)
    (Γ : LCtx) (e : Expr Nat) :
    Cert (Σ' (w : Expr Nat), MachineRed E n Γ e w) :=
  whnfCertTrans qmap.toEnv_eq (whnfCert qmap.toEnv n fuel Γ e)

/-- Lookup-equivalence theorem for WHNF: `whnfOptCert qmap` is identical to
    the reference `whnfCert E`. -/
theorem whnfOptCert_eq_whnfCert {E : ResolvedEnv} (qmap : QIndexMap E)
    (n : Nat) (fuel : Nat) (Γ : LCtx) (e : Expr Nat) :
    whnfOptCert qmap n fuel Γ e = whnfCert E n fuel Γ e :=
  whnfCertTrans_eq qmap.toEnv_eq n fuel Γ e

/-- Transport a `convCert E'` certificate along `heq : E' = E` inside `.ok`. -/
def convCertTrans {E' E : ResolvedEnv} (heq : E' = E) {n : Nat} {Γ : LCtx} {l r : Expr Nat}
    (c : Cert (Conv E' n Γ l r)) :
    Cert (Conv E n Γ l r) :=
  match c with
  | .no msg => .no msg
  | .ok hc => .ok (heq ▸ hc)

/-- Transporting `convCert E'` along `heq : E' = E` yields `convCert E`. -/
theorem convCertTrans_eq {E' E : ResolvedEnv} (heq : E' = E) (n fuel : Nat)
    (Γ : LCtx) (A l r : Expr Nat) :
    convCertTrans heq (convCert E' n fuel Γ A l r) = convCert E n fuel Γ A l r := by
  cases heq
  cases convCert E' n fuel Γ A l r with
  | no msg => rfl
  | ok hc => rfl

/-- Optimized conversion certifier (`03` §13 + §14): delegates to canonical
    `convCert` (`RcicMachine.lean:238`) over `qmap.toEnv` (`members := qmap.lookup`)
    and transports the indexed `Conv` derivation along `qmap.toEnv_eq`
    inside `.ok`. -/
def convOptCert {E : ResolvedEnv} (qmap : QIndexMap E) (n fuel : Nat)
    (Γ : LCtx) (A l r : Expr Nat) :
    Cert (Conv E n Γ l r) :=
  convCertTrans qmap.toEnv_eq (convCert qmap.toEnv n fuel Γ A l r)

/-- Lookup-equivalence theorem for conversion: `convOptCert qmap` is identical
    to the reference `convCert E`. -/
theorem convOptCert_eq_convCert {E : ResolvedEnv} (qmap : QIndexMap E)
    (n : Nat) (fuel : Nat) (Γ : LCtx) (A l r : Expr Nat) :
    convOptCert qmap n fuel Γ A l r = convCert E n fuel Γ A l r :=
  convCertTrans_eq qmap.toEnv_eq n fuel Γ A l r

/-- Transport a `HasTy E'` synthesis certificate along `heq : E' = E` inside `.ok`. -/
def inferCertTrans {E' E : ResolvedEnv} (heq : E' = E) {n : Nat} {Γ : LCtx} {e : Expr Nat}
    (c : Cert (Σ' (T : Expr Nat), HasTy E' n Γ e T)) :
    Cert (Σ' (T : Expr Nat), HasTy E n Γ e T) :=
  match c with
  | .no msg => .no msg
  | .ok ⟨T, hT⟩ => .ok ⟨T, heq ▸ hT⟩

/-- Transporting `inferCert.inferCert_app E'` along `heq : E' = E` yields
    `inferCert.inferCert_app E`. -/
theorem inferCertAppTrans_eq {E' E : ResolvedEnv} (heq : E' = E) (n f : Nat)
    (Γ : LCtx) (fn arg Tf : Expr Nat) (hfn : HasTy E n Γ fn Tf)
    (Targ : Expr Nat) (harg : HasTy E n Γ arg Targ) :
    inferCertTrans heq
      (inferCert.inferCert_app E' n f Γ fn arg Tf (heq.symm ▸ hfn) Targ (heq.symm ▸ harg)) =
      inferCert.inferCert_app E n f Γ fn arg Tf hfn Targ harg := by
  cases heq
  cases inferCert.inferCert_app E' n f Γ fn arg Tf hfn Targ harg with
  | no msg => rfl
  | ok c =>
      rcases c with ⟨T, hT⟩
      rfl

/-- Helper for the `.app` branch of `inferOptCert`: delegates to canonical
    `inferCert.inferCert_app` (`RcicMachine.lean:412`) over `qmap.toEnv`
    (`members := qmap.lookup`) and transports the indexed `HasTy` derivations
    along `qmap.toEnv_eq`. -/
def inferOptCert_app {E : ResolvedEnv} (qmap : QIndexMap E) (n f : Nat) (Γ : LCtx)
    (fn arg Tf : Expr Nat) (hfn : HasTy E n Γ fn Tf)
    (Targ : Expr Nat) (harg : HasTy E n Γ arg Targ) :
    Cert (Σ' (T : Expr Nat), HasTy E n Γ (.app fn arg) T) :=
  inferCertTrans qmap.toEnv_eq
    (inferCert.inferCert_app qmap.toEnv n f Γ fn arg Tf
      (qmap.toEnv_eq.symm ▸ hfn) Targ (qmap.toEnv_eq.symm ▸ harg))

/-- Lookup-equivalence theorem for `inferOptCert_app`. -/
theorem inferOptCert_app_eq_inferCert_app {E : ResolvedEnv} (qmap : QIndexMap E)
    (n f : Nat) (Γ : LCtx) (fn arg Tf : Expr Nat) (hfn : HasTy E n Γ fn Tf)
    (Targ : Expr Nat) (harg : HasTy E n Γ arg Targ) :
    inferOptCert_app qmap n f Γ fn arg Tf hfn Targ harg =
      inferCert.inferCert_app E n f Γ fn arg Tf hfn Targ harg :=
  inferCertAppTrans_eq qmap.toEnv_eq n f Γ fn arg Tf hfn Targ harg

/-- Transporting `inferCert E'` along `heq : E' = E` yields `inferCert E`. -/
theorem inferCertTrans_eq {E' E : ResolvedEnv} (heq : E' = E) (n fuel : Nat)
    (Γ : LCtx) (e : Expr Nat) :
    inferCertTrans heq (inferCert E' n fuel Γ e) = inferCert E n fuel Γ e := by
  cases heq
  cases inferCert E' n fuel Γ e with
  | no msg => rfl
  | ok c =>
      rcases c with ⟨T, hT⟩
      rfl

/-- Optimized inference certifier (`03` §10 + §14): delegates to canonical
    `inferCert` (`RcicMachine.lean:324`) over `qmap.toEnv` (`members := qmap.lookup`)
    and transports the indexed `HasTy` derivation along `qmap.toEnv_eq`
    inside `.ok`. -/
def inferOptCert {E : ResolvedEnv} (qmap : QIndexMap E) (n fuel : Nat)
    (Γ : LCtx) (e : Expr Nat) :
    Cert (Σ' (T : Expr Nat), HasTy E n Γ e T) :=
  inferCertTrans qmap.toEnv_eq (inferCert qmap.toEnv n fuel Γ e)

/-- Lookup-equivalence theorem for inference: `inferOptCert qmap` is identical
    to the reference `inferCert E`. -/
theorem inferOptCert_eq_inferCert {E : ResolvedEnv} (qmap : QIndexMap E)
    (n : Nat) (fuel : Nat) (Γ : LCtx) (e : Expr Nat) :
    inferOptCert qmap n fuel Γ e = inferCert E n fuel Γ e :=
  inferCertTrans_eq qmap.toEnv_eq n fuel Γ e

/-! ## 3. `03` §11 Bidirectional `.lam`/`.pi` Check (`checkOptCert` & `checkBiLamCert`) -/

/-- Exact characterization of `convCert` when the LHS is `.pi A B`:
    because `.pi A B` is already in WHNF (`machineWhnfDone E (.pi A B) = true`)
    and `convCert` has no `.pi` head arm in Steps 5–9, `convCert E n (f + 1) Γ A_ctx (.pi A B) T`
    succeeds if and only if `whnfCert E n f Γ T` reduces `T` to `.pi A B`. -/
theorem convCert_pi_left_ok_iff {E : ResolvedEnv} {n f : Nat} {Γ : LCtx}
    {A_ctx A B T : Expr Nat} :
    (∃ hc : Conv E n Γ (.pi A B) T, convCert E n (f + 1) Γ A_ctx (.pi A B) T = .ok hc) ↔
      ∃ kT : MachineRed E n Γ T (.pi A B),
        whnfCert E n f Γ T = .ok ⟨.pi A B, kT⟩ := by
  have hpi_done : machineWhnfDone E (.pi A B) = true := rfl
  have hpi_whnf : whnfCert E n f Γ (.pi A B) = .ok ⟨.pi A B, .refl Γ (.pi A B)⟩ :=
    whnfCert_of_machineWhnfDone E n f Γ (.pi A B) hpi_done
  constructor
  · rintro ⟨hc, hconv⟩
    rw [convCert] at hconv
    by_cases hlr : Expr.pi A B = T
    · subst hlr
      exact ⟨.refl Γ (.pi A B), hpi_whnf⟩
    · rw [dif_neg hlr] at hconv
      split at hconv
      · exact nomatch hconv
      · next wl kl hwl =>
          have hwl_eq : wl = .pi A B := by
            rw [hpi_whnf] at hwl
            injection hwl with h1
            exact (congrArg PSigma.fst h1).symm
          subst hwl_eq
          split at hconv
          · exact nomatch hconv
          · next wr kr hwr =>
              by_cases hwleq : Expr.pi A B = wr
              · subst hwleq
                exact ⟨kr, hwr⟩
              · rw [dif_neg hwleq] at hconv
                exact nomatch hconv
  · rintro ⟨kT, hwr⟩
    rw [convCert]
    by_cases hlr : Expr.pi A B = T
    · subst hlr
      rw [dif_pos rfl]
      exact ⟨.refl Γ (.pi A B), rfl⟩
    · rw [dif_neg hlr]
      split
      · next msg hno => rw [hpi_whnf] at hno; exact nomatch hno
      · next wl kl hwl =>
          have hwl_eq : wl = .pi A B := by
            rw [hpi_whnf] at hwl
            injection hwl with h1
            exact (congrArg PSigma.fst h1).symm
          subst hwl_eq
          split
          · next msg hno => rw [hwr] at hno; exact nomatch hno
          · next wr kr hwr₂ =>
              have hwr_eq : wr = .pi A B := by
                rw [hwr] at hwr₂
                injection hwr₂ with h1
                exact (congrArg PSigma.fst h1).symm
              subst hwr_eq
              simp only [dif_pos rfl]
              exact ⟨_, rfl⟩

/-- Non-lambda fallback arm of `checkOptCert` and `checkBiLamCert`:
    infer `Te` via `inferOptCert` and convert `Te` to `T` via `convOptCert`. -/
def checkFallbackCert {E : ResolvedEnv} (qmap : QIndexMap E) (n f : Nat)
    (Γ : LCtx) (e T : Expr Nat) : Cert (HasTy E n Γ e T) :=
  match inferOptCert qmap n f Γ e with
  | .no msg => Cert.no msg
  | .ok ⟨Te, he⟩ =>
      match convOptCert qmap n f Γ T Te T with
      | .no msg => Cert.no msg
      | .ok hc => Cert.ok (.conv Γ e Te T he hc)

/-- Constructor dispatch for `checkOptCert` after `T` is verified to be a sort:
    uses the `03` §11 bidirectional `.lam`/`.pi` rule on `.lam A body` and
    `checkFallbackCert` on the other 7 expression constructors. -/
def checkOptDispatch {E : ResolvedEnv} (qmap : QIndexMap E) (n f : Nat)
    (Γ : LCtx) (e T : Expr Nat) : Cert (HasTy E n Γ e T) :=
  match e with
  | .lam A body =>
      match whnfOptCert qmap n f Γ T with
      | .no msg => Cert.no msg
      | .ok ⟨Tw, kT⟩ =>
          match Tw with
          | .pi A' B =>
              if hdom : A = A' then
                match inferOptCert qmap n f Γ A with
                | .no msg => Cert.no msg
                | .ok ⟨TA, hA⟩ =>
                    match TA with
                    | .sort uA =>
                        match inferOptCert qmap n f (LocalDecl.assumption A :: Γ) body with
                        | .no msg => Cert.no msg
                        | .ok ⟨Tbody, hbody⟩ =>
                            if hcod : Tbody = B then
                              have kT' : MachineRed E n Γ T (.pi A B) := hdom ▸ kT
                              have hbody' : HasTy E n (LocalDecl.assumption A :: Γ) body B :=
                                hcod ▸ hbody
                              Cert.ok (.conv Γ (.lam A body) (.pi A B) T
                                (.lam Γ A uA body B hA hbody')
                                (.symm Γ T (.pi A B) (machineRed_toConv kT')))
                            else .no "[rcic_conv_mismatch]"
                    | _ => .no "[rcic_infer_not_a_sort]"
              else .no "[rcic_conv_mismatch]"
          | _ => .no "[rcic_conv_mismatch]"
  | .bvar i => checkFallbackCert qmap n f Γ (.bvar i) T
  | .sort l => checkFallbackCert qmap n f Γ (.sort l) T
  | .const r ls => checkFallbackCert qmap n f Γ (.const r ls) T
  | .app fn arg => checkFallbackCert qmap n f Γ (.app fn arg) T
  | .pi A B => checkFallbackCert qmap n f Γ (.pi A B) T
  | .letE A v b => checkFallbackCert qmap n f Γ (.letE A v b) T
  | .lit t => checkFallbackCert qmap n f Γ (.lit t) T

/-- `03` §11 (`03:313`) Optimized Check Certifier with the bidirectional
    lambda rule:
    - First checks that expected type `T` is a sort via `inferOptCert`.
    - Dispatches to `checkOptDispatch`, which applies the bidirectional
      `.lam`/`.pi` rule on `.lam A body` and `checkFallbackCert` on non-lambda
      expressions. -/
def checkOptCert {E : ResolvedEnv} (qmap : QIndexMap E) (n : Nat) :
    (fuel : Nat) → (Γ : LCtx) → (e T : Expr Nat) →
    Cert (HasTy E n Γ e T)
  | 0, _, _, _ => .no "[rcic_pi_check_fuel]"
  | f + 1, Γ, e, T =>
      match inferOptCert qmap n f Γ T with
      | .no msg => Cert.no msg
      | .ok ⟨TT, _hT⟩ =>
          match TT with
          | .sort _ => checkOptDispatch qmap n f Γ e T
          | _ => .no "[rcic_pi_check_not_a_sort]"

/-- Soundness of `checkOptCert`: every accepted certificate carries a declarative
    `HasTy E n Γ e T` derivation. -/
def RM024_checkOptCert_sound {E : ResolvedEnv} (qmap : QIndexMap E)
    (n fuel : Nat) (Γ : LCtx) (e T : Expr Nat)
    {c : HasTy E n Γ e T} (_hok : checkOptCert qmap n fuel Γ e T = .ok c) :
    HasTy E n Γ e T :=
  c

/-- Helper: for any `e`, when `inferCert E n f₀ Γ T = .ok ⟨.sort uT, hT⟩` and
    `checkFallbackCert qmap n f₀ Γ e T = .ok c`, the reference `checkCert`
    accepts at `f₀ + 1` and hence at `f₀ + 2`. -/
theorem checkFallbackCert_refines_checkCert {E : ResolvedEnv} (qmap : QIndexMap E)
    {n f₀ : Nat} {Γ : LCtx} {e T : Expr Nat} {uT : Level}
    {hT : HasTy E n Γ T (.sort uT)} {c : HasTy E n Γ e T}
    (hIT : inferCert E n f₀ Γ T = .ok ⟨.sort uT, hT⟩)
    (hok : checkFallbackCert qmap n f₀ Γ e T = .ok c) :
    ∃ c' : HasTy E n Γ e T, checkCert E n (f₀ + 2) Γ e T = .ok c' := by
  unfold checkFallbackCert at hok
  simp only [inferOptCert_eq_inferCert, convOptCert_eq_convCert] at hok
  have hcc : checkCert E n (f₀ + 1) Γ e T = .ok c := by
    rw [checkCert, hIT]
    exact hok
  exact checkCert_mono hcc (Nat.le_succ (f₀ + 1))

/-- **Core RM-024 Certifier Refinement (`03:313, 390`):**
    If the optimized bidirectional check certifier `checkOptCert qmap n f Γ e T`
    accepts at fuel `f`, then the reference `checkCert E n (f + 1) Γ e T` accepts
    at fuel `f + 1`. -/
theorem checkOptCert_refines_checkCert {E : ResolvedEnv} (qmap : QIndexMap E)
    {n f : Nat} {Γ : LCtx} {e T : Expr Nat} {c : HasTy E n Γ e T}
    (hok : checkOptCert qmap n f Γ e T = .ok c) :
    ∃ c' : HasTy E n Γ e T, checkCert E n (f + 1) Γ e T = .ok c' := by
  cases f with
  | zero => exact nomatch hok
  | succ f₀ =>
      have hle : f₀ ≤ f₀ + 1 := Nat.le_succ f₀
      rw [checkOptCert] at hok
      rw [inferOptCert_eq_inferCert] at hok
      cases hIT : inferCert E n f₀ Γ T with
      | no msg =>
          rw [hIT] at hok
          exact nomatch hok
      | ok cT =>
          rcases cT with ⟨TT, hT⟩
          simp only [hIT] at hok
          cases TT with
          | sort uT =>
              simp only [] at hok
              rcases inferCert_mono hIT hle with ⟨⟨TT', hT'⟩, hIT', hTT'⟩
              simp only at hTT'
              subst TT'
              cases e with
              | lam A body =>
                  simp only [checkOptDispatch, whnfOptCert_eq_whnfCert,
                    inferOptCert_eq_inferCert] at hok
                  cases hWT : whnfCert E n f₀ Γ T with
                  | no msg => rw [hWT] at hok; exact nomatch hok
                  | ok cW =>
                      rcases cW with ⟨Tw, kT⟩
                      simp only [hWT] at hok
                      cases Tw with
                      | pi A' B =>
                          simp only [] at hok
                          by_cases hdom : A = A'
                          · rw [dif_pos hdom] at hok
                            subst A'
                            cases hIA : inferCert E n f₀ Γ A with
                            | no msg => rw [hIA] at hok; exact nomatch hok
                            | ok cA =>
                                rcases cA with ⟨TA, hA⟩
                                simp only [hIA] at hok
                                cases TA with
                                | sort uA =>
                                    simp only [] at hok
                                    cases hIB : inferCert E n f₀ (LocalDecl.assumption A :: Γ) body with
                                    | no msg => rw [hIB] at hok; exact nomatch hok
                                    | ok cB =>
                                        rcases cB with ⟨Tbody, hbody⟩
                                        simp only [hIB] at hok
                                        by_cases hcod : Tbody = B
                                        · subst B
                                          rcases (convCert_pi_left_ok_iff (A_ctx := T)).mpr ⟨kT, hWT⟩ with
                                            ⟨hc_conv, hconv_ok⟩
                                          rw [checkCert, hIT']
                                          simp only [inferCert, hIA, hIB, hconv_ok]
                                          exact ⟨_, rfl⟩
                                        · rw [dif_neg hcod] at hok
                                          exact nomatch hok
                                | _ => exact nomatch hok
                          · rw [dif_neg hdom] at hok
                            exact nomatch hok
                      | _ => exact nomatch hok
              | bvar i => exact checkFallbackCert_refines_checkCert qmap hIT hok
              | sort l => exact checkFallbackCert_refines_checkCert qmap hIT hok
              | const r ls => exact checkFallbackCert_refines_checkCert qmap hIT hok
              | app fn arg => exact checkFallbackCert_refines_checkCert qmap hIT hok
              | pi A B => exact checkFallbackCert_refines_checkCert qmap hIT hok
              | letE A v b => exact checkFallbackCert_refines_checkCert qmap hIT hok
              | lit t => exact checkFallbackCert_refines_checkCert qmap hIT hok
          | _ => exact nomatch hok

/-- **Converse Certifier Completeness (`checkCert` → `checkOptCert` at the same fuel):**
    Every acceptance of the reference `checkCert E n f Γ e T` is accepted by
    `checkOptCert qmap n f Γ e T` at the exact same fuel `f`. -/
theorem checkCert_refines_checkOptCert {E : ResolvedEnv} (qmap : QIndexMap E)
    {n f : Nat} {Γ : LCtx} {e T : Expr Nat} {c : HasTy E n Γ e T}
    (hok : checkCert E n f Γ e T = .ok c) :
    ∃ c' : HasTy E n Γ e T, checkOptCert qmap n f Γ e T = .ok c' := by
  cases f with
  | zero => exact nomatch hok
  | succ f₀ =>
      rw [checkCert] at hok
      cases hIT : inferCert E n f₀ Γ T with
      | no msg => rw [hIT] at hok; exact nomatch hok
      | ok cT =>
          rcases cT with ⟨TT, hT⟩
          simp only [hIT] at hok
          cases TT with
          | sort uT =>
              simp only [] at hok
              cases e with
              | lam A body =>
                  cases f₀ with
                  | zero =>
                      simp only [inferCert] at hok
                      exact nomatch hok
                  | succ f₁ =>
                      have hle₁ : f₁ ≤ f₁ + 1 := Nat.le_succ f₁
                      simp only [inferCert] at hok
                      cases hIA : inferCert E n f₁ Γ A with
                      | no msg => rw [hIA] at hok; exact nomatch hok
                      | ok cA =>
                          rcases cA with ⟨TA, hA⟩
                          simp only [hIA] at hok
                          cases TA with
                          | sort uA =>
                              simp only [] at hok
                              cases hIB : inferCert E n f₁ (LocalDecl.assumption A :: Γ) body with
                              | no msg => rw [hIB] at hok; exact nomatch hok
                              | ok cB =>
                                  rcases cB with ⟨Tbody, hbody⟩
                                  simp only [hIB] at hok
                                  cases hCV : convCert E n (f₁ + 1) Γ T (.pi A Tbody) T with
                                  | no msg => rw [hCV] at hok; exact nomatch hok
                                  | ok hc =>
                                      rcases (convCert_pi_left_ok_iff (A_ctx := T)).mp ⟨hc, hCV⟩ with
                                        ⟨kT, hWT⟩
                                      rcases whnfCert_mono hWT hle₁ with ⟨⟨Tw', kT'⟩, hWT', hTw'⟩
                                      simp only at hTw'
                                      subst Tw'
                                      rcases inferCert_mono hIA hle₁ with ⟨⟨TA', hA'⟩, hIA', hTA'⟩
                                      simp only at hTA'
                                      subst TA'
                                      rcases inferCert_mono hIB hle₁ with ⟨⟨TB', hbody'⟩, hIB', hTB'⟩
                                      simp only at hTB'
                                      subst TB'
                                      rw [checkOptCert]
                                      simp only [inferOptCert_eq_inferCert, hIT, checkOptDispatch,
                                        whnfOptCert_eq_whnfCert, hWT', dif_pos rfl, hIA', hIB']
                                      exact ⟨_, rfl⟩
                          | _ => exact nomatch hok
              | bvar i =>
                  rw [checkOptCert]
                  simp only [inferOptCert_eq_inferCert, hIT, checkOptDispatch,
                    checkFallbackCert, convOptCert_eq_convCert]
                  exact ⟨c, hok⟩
              | sort l =>
                  rw [checkOptCert]
                  simp only [inferOptCert_eq_inferCert, hIT, checkOptDispatch,
                    checkFallbackCert, convOptCert_eq_convCert]
                  exact ⟨c, hok⟩
              | const r ls =>
                  rw [checkOptCert]
                  simp only [inferOptCert_eq_inferCert, hIT, checkOptDispatch,
                    checkFallbackCert, convOptCert_eq_convCert]
                  exact ⟨c, hok⟩
              | app fn arg =>
                  rw [checkOptCert]
                  simp only [inferOptCert_eq_inferCert, hIT, checkOptDispatch,
                    checkFallbackCert, convOptCert_eq_convCert]
                  exact ⟨c, hok⟩
              | pi A B =>
                  rw [checkOptCert]
                  simp only [inferOptCert_eq_inferCert, hIT, checkOptDispatch,
                    checkFallbackCert, convOptCert_eq_convCert]
                  exact ⟨c, hok⟩
              | letE A v b =>
                  rw [checkOptCert]
                  simp only [inferOptCert_eq_inferCert, hIT, checkOptDispatch,
                    checkFallbackCert, convOptCert_eq_convCert]
                  exact ⟨c, hok⟩
              | lit t =>
                  rw [checkOptCert]
                  simp only [inferOptCert_eq_inferCert, hIT, checkOptDispatch,
                    checkFallbackCert, convOptCert_eq_convCert]
                  exact ⟨c, hok⟩
          | _ => exact nomatch hok

/-- Inner-fuel monotonicity of `checkOptCert`: if `checkOptCert` succeeds at
    fuel `f`, it succeeds at every `f' ≥ f`. -/
theorem checkOptCert_mono {E : ResolvedEnv} (qmap : QIndexMap E)
    {n f f' : Nat} {Γ : LCtx} {e T : Expr Nat} {c : HasTy E n Γ e T}
    (hok : checkOptCert qmap n f Γ e T = .ok c) (hle : f ≤ f') :
    ∃ c' : HasTy E n Γ e T, checkOptCert qmap n f' Γ e T = .ok c' := by
  cases f with
  | zero => exact nomatch hok
  | succ f₀ =>
      cases f' with
      | zero => exact absurd hle (Nat.not_succ_le_zero f₀)
      | succ f'₀ =>
          have hle₀ : f₀ ≤ f'₀ := Nat.le_of_succ_le_succ hle
          rw [checkOptCert] at hok
          rw [checkOptCert]
          simp only [inferOptCert_eq_inferCert] at hok ⊢
          cases hIT : inferCert E n f₀ Γ T with
          | no msg => rw [hIT] at hok; exact nomatch hok
          | ok cT =>
              rcases cT with ⟨TT, hT⟩
              simp only [hIT] at hok
              rcases inferCert_mono hIT hle₀ with ⟨⟨TT', hT'⟩, hIT', hTT'⟩
              simp only at hTT'
              subst TT'
              simp only [hIT']
              cases TT with
              | sort uT =>
                  simp only [] at hok ⊢
                  have hfb : ∀ e₀ : Expr Nat, ∀ c₀ : HasTy E n Γ e₀ T,
                      checkFallbackCert qmap n f₀ Γ e₀ T = .ok c₀ →
                      ∃ c' : HasTy E n Γ e₀ T, checkFallbackCert qmap n f'₀ Γ e₀ T = .ok c' := by
                    intro e₀ c₀ hfb₀
                    unfold checkFallbackCert at hfb₀ ⊢
                    simp only [inferOptCert_eq_inferCert, convOptCert_eq_convCert] at hfb₀ ⊢
                    cases hIe : inferCert E n f₀ Γ e₀ with
                    | no msg => rw [hIe] at hfb₀; exact nomatch hfb₀
                    | ok ce =>
                        rcases ce with ⟨Te, he⟩
                        simp only [hIe] at hfb₀
                        rcases inferCert_mono hIe hle₀ with ⟨⟨Te', he'⟩, hIe', hTe'⟩
                        simp only at hTe'
                        subst Te'
                        simp only [hIe']
                        cases hCV : convCert E n f₀ Γ T Te T with
                        | no msg => rw [hCV] at hfb₀; exact nomatch hfb₀
                        | ok hc =>
                            rcases convCert_mono hCV hle₀ with ⟨hc', hCV'⟩
                            simp only [hCV']
                            exact ⟨_, rfl⟩
                  cases e with
                  | lam A body =>
                      simp only [checkOptDispatch, whnfOptCert_eq_whnfCert,
                        inferOptCert_eq_inferCert] at hok ⊢
                      cases hWT : whnfCert E n f₀ Γ T with
                      | no msg => rw [hWT] at hok; exact nomatch hok
                      | ok cW =>
                          rcases cW with ⟨Tw, kT⟩
                          simp only [hWT] at hok
                          rcases whnfCert_mono hWT hle₀ with ⟨⟨Tw', kT'⟩, hWT', hTw'⟩
                          simp only at hTw'
                          subst Tw'
                          simp only [hWT']
                          cases Tw with
                          | pi A' B =>
                              simp only [] at hok ⊢
                              by_cases hdom : A = A'
                              · rw [dif_pos hdom] at hok ⊢
                                cases hIA : inferCert E n f₀ Γ A with
                                | no msg => rw [hIA] at hok; exact nomatch hok
                                | ok cA =>
                                    rcases cA with ⟨TA, hA⟩
                                    simp only [hIA] at hok
                                    rcases inferCert_mono hIA hle₀ with ⟨⟨TA', hA'⟩, hIA', hTA'⟩
                                    simp only at hTA'
                                    subst TA'
                                    simp only [hIA']
                                    cases TA with
                                    | sort uA =>
                                        simp only [] at hok ⊢
                                        cases hIB : inferCert E n f₀ (LocalDecl.assumption A :: Γ) body with
                                        | no msg => rw [hIB] at hok; exact nomatch hok
                                        | ok cB =>
                                            rcases cB with ⟨Tbody, hbody⟩
                                            simp only [hIB] at hok
                                            rcases inferCert_mono hIB hle₀ with
                                              ⟨⟨Tbody', hbody'⟩, hIB', hTB'⟩
                                            simp only at hTB'
                                            subst Tbody'
                                            simp only [hIB']
                                            by_cases hcod : Tbody = B
                                            · rw [dif_pos hcod]
                                              exact ⟨_, rfl⟩
                                            · rw [dif_neg hcod] at hok
                                              exact nomatch hok
                                    | _ => exact nomatch hok
                              · rw [dif_neg hdom] at hok
                                exact nomatch hok
                          | _ => exact nomatch hok
                  | bvar i => exact hfb (.bvar i) c hok
                  | sort l => exact hfb (.sort l) c hok
                  | const r ls => exact hfb (.const r ls) c hok
                  | app fn arg => exact hfb (.app fn arg) c hok
                  | pi A B => exact hfb (.pi A B) c hok
                  | letE A v b => exact hfb (.letE A v b) c hok
                  | lit t => exact hfb (.lit t) c hok
              | _ => exact nomatch hok

/-- Multi-binder recursive bidirectional `.lam`/`.pi` check certifier:
    recurses through `checkBiLamCert` on nested `.lam` bodies against expected
    Π-codomains `B`. -/
def checkBiLamCert {E : ResolvedEnv} (qmap : QIndexMap E) (n : Nat) :
    (fuel : Nat) → (Γ : LCtx) → (e T : Expr Nat) →
    Cert (HasTy E n Γ e T)
  | 0, _, _, _ => .no "[rcic_pi_check_fuel]"
  | f + 1, Γ, e, T =>
      match inferOptCert qmap n f Γ T with
      | .no msg => Cert.no msg
      | .ok ⟨TT, _hT⟩ =>
          match TT with
          | .sort _ =>
              match e with
              | .lam A body =>
                  match whnfOptCert qmap n f Γ T with
                  | .no msg => Cert.no msg
                  | .ok ⟨Tw, kT⟩ =>
                      match Tw with
                      | .pi A' B =>
                          if hdom : A = A' then
                            match inferOptCert qmap n f Γ A with
                            | .no msg => Cert.no msg
                            | .ok ⟨TA, hA⟩ =>
                                match TA with
                                | .sort uA =>
                                    match checkBiLamCert qmap n f (LocalDecl.assumption A :: Γ) body B with
                                    | .no msg => Cert.no msg
                                    | .ok hbody =>
                                        have kT' : MachineRed E n Γ T (.pi A B) := hdom ▸ kT
                                        Cert.ok (.conv Γ (.lam A body) (.pi A B) T
                                          (.lam Γ A uA body B hA hbody)
                                          (.symm Γ T (.pi A B) (machineRed_toConv kT')))
                                | _ => .no "[rcic_infer_not_a_sort]"
                          else .no "[rcic_conv_mismatch]"
                      | _ => .no "[rcic_conv_mismatch]"
              | e' => checkFallbackCert qmap n f Γ e' T
          | _ => .no "[rcic_pi_check_not_a_sort]"

/-- Declarative soundness of the recursive multi-binder bidirectional certifier
    `checkBiLamCert`. -/
def RM024_checkBiLamCert_sound {E : ResolvedEnv} (qmap : QIndexMap E)
    (n fuel : Nat) (Γ : LCtx) (e T : Expr Nat)
    {c : HasTy E n Γ e T} (_hok : checkBiLamCert qmap n fuel Γ e T = .ok c) :
    HasTy E n Γ e T :=
  c

/-! ## 4. `OptimizedKernel` Step, Runner, and `RM024_optimized_accept_refines` (`03:390`) -/

/-- `03` §1, §11, §14 (`03:12, 313, 362`): Constructive Lean `OptimizedKernel`
    over a resolved environment `E`, packaging the validated `QIndexMap E` for
    declaration lookup, WHNF, conversion, inference, and the bidirectional
    `.lam`/`.pi` check certifier. -/
structure OptimizedKernel (E : ResolvedEnv) where
  qmap : QIndexMap E

/-- Single-step transition of the optimized kernel (`03` §11 + §14),
    dispatching `.lookupDeclaration`, `.whnfAt`, `.convAt`, `.infer`, and
    `.check` through `inferOptCert`, `whnfOptCert`, `convOptCert`, and
    `checkOptCert`. -/
def optStepRaw {E : ResolvedEnv} (qmap : QIndexMap E) (s : RawState) : StepOutcome :=
  match s.budget with
  | 0 => .result .suspended
  | _ + 1 =>
    match s.task with
    | .lookupDeclaration r ls =>
        match inferOptCert qmap s.ambient.univs s.budget
            s.ambient.ctx (.const r ls) with
        | .ok ⟨T, _⟩ => .result (.accepted (.inferredType T))
        | .no msg => .result (.refused msg)
    | .whnfAt A e =>
        match whnfOptCert qmap s.ambient.univs s.budget
            s.ambient.ctx e with
        | .ok ⟨w, _⟩ => .result (.accepted (.inferredWhnf A w))
        | .no msg => .result (.refused msg)
    | .convAt A l r =>
        match convOptCert qmap s.ambient.univs s.budget
            s.ambient.ctx A l r with
        | .ok _ => .result (.accepted .conversionConfirmed)
        | .no msg =>
            if msg = "[rcic_conv_mismatch]" then
              .result (.accepted .conversionMismatch)
            else .result (.refused msg)
    | .infer e =>
        match inferOptCert qmap s.ambient.univs s.budget
            s.ambient.ctx e with
        | .ok ⟨T, _⟩ => .result (.accepted (.inferredType T))
        | .no msg => .result (.refused msg)
    | .check e A =>
        match checkOptCert qmap s.ambient.univs s.budget
            s.ambient.ctx e A with
        | .ok _ => .result (.accepted .checked)
        | .no msg => .result (.refused msg)
    | _ => kernelStepRaw s

/-- Outer-step runner `runOptRaw` over `optStepRaw` (mirroring `runRaw`). -/
def runOptRaw {E : ResolvedEnv} (qmap : QIndexMap E) : Nat → RawState → RunResult
  | 0, _ => .suspended
  | k + 1, s =>
    match optStepRaw qmap s with
    | .step s' => runOptRaw qmap k s'
    | .result r => r

/-- Resumable outer-step runner `runOptRawR` over `optStepRaw` (mirroring `runRawR`). -/
def runOptRawR {E : ResolvedEnv} (qmap : QIndexMap E) : Nat → RawState → RunResumable
  | 0, s => .suspended s
  | k + 1, s =>
    match optStepRaw qmap s with
    | .step s' => runOptRawR qmap k s'
    | .result .suspended => .suspended s
    | .result r => .done r

/-- State-level eventual acceptance for the optimized kernel. -/
def OptEventuallyAccepts {E : ResolvedEnv} (qmap : QIndexMap E)
    (s : RawState) (p : AcceptedPayload) : Prop :=
  ∃ m : Nat, runOptRawR qmap m s = .done (.accepted p)

/-- Task-level eventual acceptance for the optimized kernel. -/
def OptTaskEventuallyAccepts {E : ResolvedEnv} (qmap : QIndexMap E)
    (amb : Ambient) (t : RawTask) (p : AcceptedPayload) : Prop :=
  ∃ b : Nat, OptEventuallyAccepts qmap ⟨amb, t, b⟩ p

/-- Like `kernelStepRaw`, `optStepRaw` is one-shot and never returns `.step`. -/
theorem optStepRaw_never_step {E : ResolvedEnv} (qmap : QIndexMap E)
    (s s' : RawState) :
    optStepRaw qmap s ≠ .step s' := by
  intro h
  cases hb : s.budget <;> cases ht : s.task <;>
    simp only [optStepRaw, kernelStepRaw, hb, ht] at h <;>
    (try split at h) <;> (try split at h) <;>
    exact nomatch h

/-- `optStepRaw` never produces an `.integrity` result. -/
theorem optStepRaw_no_integrity {E : ResolvedEnv} (qmap : QIndexMap E)
    (s : RawState) (res : String) :
    optStepRaw qmap s ≠ .result (.integrity res) := by
  intro h
  cases hb : s.budget <;> cases ht : s.task <;>
    simp only [optStepRaw, kernelStepRaw, hb, ht] at h <;>
    (try split at h) <;> (try split at h) <;>
    exact nomatch h

/-- Any positive outer step budget `m ≥ 1` immediately wraps a non-suspended
    `optStepRaw qmap s = .result r` into `.done r`. -/
theorem runOptRawR_pos_eq_of_result {E : ResolvedEnv} {qmap : QIndexMap E}
    {s : RawState} {r : RunResult}
    (h : optStepRaw qmap s = .result r) (hne : r ≠ .suspended)
    {m : Nat} (hm : 1 ≤ m) :
    runOptRawR qmap m s = .done r := by
  cases m with
  | zero => exact absurd hm (Nat.not_succ_le_zero 0)
  | succ k =>
      simp only [runOptRawR, h]

/-- Conversely, `runOptRawR qmap m s = .done r` implies `1 ≤ m` and
    `optStepRaw qmap s = .result r`. -/
theorem optStepRaw_of_runOptRawR_done {E : ResolvedEnv} {qmap : QIndexMap E}
    {m : Nat} {s : RawState} {r : RunResult}
    (h : runOptRawR qmap m s = .done r) :
    1 ≤ m ∧ optStepRaw qmap s = .result r := by
  cases m with
  | zero => exact nomatch h
  | succ k =>
      refine ⟨Nat.succ_le_succ (Nat.zero_le k), ?_⟩
      simp only [runOptRawR] at h
      cases hkr : optStepRaw qmap s with
      | step s' => exact (optStepRaw_never_step qmap s s' hkr).elim
      | result r' =>
          rw [hkr] at h
          cases r' with
          | suspended => exact nomatch h
          | accepted p =>
              injection h with hr'
              subst hr'
              rfl
          | refused msg =>
              injection h with hr'
              subst hr'
              rfl
          | integrity msg =>
              injection h with hr'
              subst hr'
              rfl

/-- Bridge between `runOptRawR` and `runOptRaw` on `.done r`. -/
theorem runOptRaw_of_runOptRawR_done {E : ResolvedEnv} {qmap : QIndexMap E}
    {m : Nat} {s : RawState} {r : RunResult}
    (h : runOptRawR qmap m s = .done r) :
    runOptRaw qmap m s = r := by
  have ⟨hm, hkr⟩ := optStepRaw_of_runOptRawR_done h
  cases m with
  | zero => exact absurd hm (Nat.not_succ_le_zero 0)
  | succ k =>
      simp only [runOptRaw, hkr]

/-- Conversely, any non-suspended `runOptRaw qmap m s = r` lifts to
    `runOptRawR qmap m s = .done r`. -/
theorem runOptRawR_of_runOptRaw {E : ResolvedEnv} {qmap : QIndexMap E}
    {m : Nat} {s : RawState} {r : RunResult}
    (h : runOptRaw qmap m s = r) (hne : r ≠ .suspended) :
    runOptRawR qmap m s = .done r := by
  cases m with
  | zero =>
      simp only [runOptRaw] at h
      exact (hne h.symm).elim
  | succ k =>
      simp only [runOptRaw] at h
      cases hkr : optStepRaw qmap s with
      | step s' => exact (optStepRaw_never_step qmap s s' hkr).elim
      | result r' =>
          rw [hkr] at h
          subst h
          exact runOptRawR_pos_eq_of_result hkr hne (Nat.succ_le_succ (Nat.zero_le k))

/-- For every task other than `.check`, `optStepRaw qmap s` is identical to
    `kernelStepRaw s` at the exact same budget `s.budget` whenever
    `s.ambient.env = E`. -/
theorem optStepRaw_nonCheck_eq_kernelStepRaw {E : ResolvedEnv} (qmap : QIndexMap E)
    (s : RawState) (henv : s.ambient.env = E)
    (hnotCheck : ∀ e A, s.task ≠ .check e A) :
    optStepRaw qmap s = kernelStepRaw s := by
  rcases s with ⟨⟨E', n, Γ⟩, t, b⟩
  simp only at henv hnotCheck
  subst E'
  cases b with
  | zero => rfl
  | succ f =>
      cases t with
      | syntaxEqual a b => rfl
      | levelEqual l₁ l₂ => rfl
      | lookupLocal i => rfl
      | lookupDeclaration r ls =>
          simp only [optStepRaw, kernelStepRaw, inferOptCert_eq_inferCert]
          cases inferCert E n (f + 1) Γ (Expr.const r ls) with
          | no msg => rfl
          | ok c => rcases c with ⟨T, _⟩; rfl
      | whnfAt A e =>
          simp only [optStepRaw, kernelStepRaw, whnfOptCert_eq_whnfCert]
          cases whnfCert E n (f + 1) Γ e with
          | no msg => rfl
          | ok c => rcases c with ⟨w, _⟩; rfl
      | convAt A l r =>
          simp only [optStepRaw, kernelStepRaw, convOptCert_eq_convCert]
          cases convCert E n (f + 1) Γ A l r with
          | no msg => rfl
          | ok _ => rfl
      | infer e =>
          simp only [optStepRaw, kernelStepRaw, inferOptCert_eq_inferCert]
          cases inferCert E n (f + 1) Γ e with
          | no msg => rfl
          | ok c => rcases c with ⟨T, _⟩; rfl
      | check e A =>
          exact (hnotCheck e A rfl).elim
      | convType A B => rfl

/-- Step-level inner-budget monotonicity of `kernelStepRaw` for
    `PositiveTaskPayload` (derived from `runRawR_accepted_budget_mono`). -/
theorem kernelStepRaw_accepted_mono {amb : Ambient} {t : RawTask}
    {p : AcceptedPayload} {b b' : Nat}
    (hpos : PositiveTaskPayload t p)
    (hkr : kernelStepRaw ⟨amb, t, b⟩ = .result (.accepted p))
    (hb : b ≤ b') :
    kernelStepRaw ⟨amb, t, b'⟩ = .result (.accepted p) := by
  have hrun := runRawR_pos_eq_of_result hkr (Nat.le_refl 1)
  have hrun' := runRawR_accepted_budget_mono hpos hrun hb (Nat.le_refl 1)
  exact (kernelStepRaw_of_runRawR_done hrun').2

/-- **Step-level RM-024 Refinement (`03:390`):**
    If `s.ambient.env = E` and `optStepRaw qmap s = .result (.accepted p)`:
    1. There is a budget `b' ≤ s.budget + 1` (specifically `s.budget` for
       non-`.check` tasks and `s.budget + 1` for `.check`) at which the
       reference `kernelStepRaw ⟨s.ambient, s.task, b'⟩ = .result (.accepted p)`.
    2. Whenever `PositiveTaskPayload s.task p` holds, the reference machine
       accepts at the uniform budget `s.budget + 1`:
       `kernelStepRaw ⟨s.ambient, s.task, s.budget + 1⟩ = .result (.accepted p)`. -/
theorem RM024_optStepRaw_accept_refines {E : ResolvedEnv} (qmap : QIndexMap E)
    {s : RawState} {p : AcceptedPayload}
    (henv : s.ambient.env = E)
    (hacc : optStepRaw qmap s = .result (.accepted p)) :
    (∃ b' : Nat, b' ≤ s.budget + 1 ∧
      kernelStepRaw ⟨s.ambient, s.task, b'⟩ = .result (.accepted p)) ∧
    (PositiveTaskPayload s.task p →
      kernelStepRaw ⟨s.ambient, s.task, s.budget + 1⟩ = .result (.accepted p)) := by
  rcases s with ⟨⟨E', n, Γ⟩, t, b⟩
  simp only at henv
  subst E'
  cases ht : t with
  | check e A =>
      subst ht
      cases b with
      | zero => exact nomatch hacc
      | succ f =>
          simp only [optStepRaw] at hacc
          cases hopt : checkOptCert qmap n (f + 1) Γ e A with
          | no msg =>
              rw [hopt] at hacc
              exact nomatch hacc
          | ok c =>
              rw [hopt] at hacc
              injection hacc with hres
              injection hres with hp
              subst hp
              rcases checkOptCert_refines_checkCert qmap hopt with ⟨c', href⟩
              have hkr :
                  kernelStepRaw ⟨⟨E, n, Γ⟩, .check e A, f + 2⟩ =
                    .result (.accepted .checked) := by
                simp only [kernelStepRaw, href]
              exact ⟨⟨f + 2, Nat.le_refl (f + 2), hkr⟩, fun _ => hkr⟩
  | _ =>
      have hnc : ∀ e A, t ≠ .check e A := by
        intro e A h; subst h; exact nomatch ht
      have heq := optStepRaw_nonCheck_eq_kernelStepRaw qmap ⟨⟨E, n, Γ⟩, t, b⟩ rfl hnc
      have hkr_b : kernelStepRaw ⟨⟨E, n, Γ⟩, t, b⟩ = .result (.accepted p) :=
        heq.symm.trans hacc
      rw [← ht]
      refine ⟨⟨b, Nat.le_succ b, hkr_b⟩, fun hpos => ?_⟩
      exact kernelStepRaw_accepted_mono hpos hkr_b (Nat.le_succ b)

/-- **RM-024 Main Theorem (`03:390` — "optimized acceptance refines reference acceptance"):**
    Whenever the optimized resumable runner `runOptRawR qmap m s` accepts with
    payload `p` (for `s.ambient.env = E`):
    1. There exists an inner budget `b' ≤ s.budget + 1` such that the reference
       runner `runRawR m ⟨s.ambient, s.task, b'⟩ = .done (.accepted p)`.
    2. Whenever `PositiveTaskPayload s.task p` holds, the reference runner
       accepts at the uniform budget `s.budget + 1`:
       `runRawR m ⟨s.ambient, s.task, s.budget + 1⟩ = .done (.accepted p)`.
    3. The reference machine eventually accepts `(s.ambient, s.task, p)`:
       `TaskEventuallyAccepts s.ambient s.task p`. -/
theorem RM024_optimized_accept_refines {E : ResolvedEnv} (qmap : QIndexMap E)
    {m : Nat} {s : RawState} {p : AcceptedPayload}
    (henv : s.ambient.env = E)
    (hacc : runOptRawR qmap m s = .done (.accepted p)) :
    (∃ b' : Nat, b' ≤ s.budget + 1 ∧
      runRawR m ⟨s.ambient, s.task, b'⟩ = .done (.accepted p)) ∧
    (PositiveTaskPayload s.task p →
      runRawR m ⟨s.ambient, s.task, s.budget + 1⟩ = .done (.accepted p)) ∧
    TaskEventuallyAccepts s.ambient s.task p := by
  have ⟨hm, hstep⟩ := optStepRaw_of_runOptRawR_done hacc
  have ⟨⟨b', hb', hkr_b'⟩, hkr_pos⟩ := RM024_optStepRaw_accept_refines qmap henv hstep
  have hrun_b' : runRawR m ⟨s.ambient, s.task, b'⟩ = .done (.accepted p) :=
    runRawR_pos_eq_of_result hkr_b' hm
  refine ⟨⟨b', hb', hrun_b'⟩, fun hpos => ?_, ⟨b', m, hrun_b'⟩⟩
  exact runRawR_pos_eq_of_result (hkr_pos hpos) hm

/-- **RM-024 Refinement over `runOptRaw` / `runRaw` (`03:390`):**
    If `s.ambient.env = E` and `runOptRaw qmap m s = .accepted p`, then
    there exists `b' ≤ s.budget + 1` with `runRaw m ⟨s.ambient, s.task, b'⟩ = .accepted p`,
    and under `PositiveTaskPayload s.task p`,
    `runRaw m ⟨s.ambient, s.task, s.budget + 1⟩ = .accepted p`. -/
theorem RM024_optimized_runRaw_accept_refines {E : ResolvedEnv} (qmap : QIndexMap E)
    {m : Nat} {s : RawState} {p : AcceptedPayload}
    (henv : s.ambient.env = E)
    (hacc : runOptRaw qmap m s = .accepted p) :
    (∃ b' : Nat, b' ≤ s.budget + 1 ∧
      runRaw m ⟨s.ambient, s.task, b'⟩ = .accepted p) ∧
    (PositiveTaskPayload s.task p →
      runRaw m ⟨s.ambient, s.task, s.budget + 1⟩ = .accepted p) := by
  have haccR : runOptRawR qmap m s = .done (.accepted p) :=
    runOptRawR_of_runOptRaw hacc (fun h => nomatch h)
  rcases RM024_optimized_accept_refines qmap henv haccR with
    ⟨⟨b', hb', hrun_b'⟩, hrun_pos, _⟩
  refine ⟨⟨b', hb', runRaw_of_runRawR_done m _ (.accepted p) hrun_b'⟩, fun hpos => ?_⟩
  exact runRaw_of_runRawR_done m _ (.accepted p) (hrun_pos hpos)

/-- **RM-024 Declarative Typing Soundness for Optimized Check:**
    Whenever `runOptRawR qmap m ⟨⟨E, n, Γ⟩, .check e A, b⟩ = .done (.accepted .checked)`,
    both `runRawR m ⟨⟨E, n, Γ⟩, .check e A, b + 1⟩ = .done (.accepted .checked)`
    and `HasTy E n Γ e A` hold. -/
def RM024_optimized_check_sound {E : ResolvedEnv} (qmap : QIndexMap E)
    {m n b : Nat} {Γ : LCtx} {e A : Expr Nat}
    (hacc : runOptRawR qmap m ⟨⟨E, n, Γ⟩, .check e A, b⟩ = .done (.accepted .checked)) :
    HasTy E n Γ e A := by
  have href :
      runRawR m ⟨⟨E, n, Γ⟩, .check e A, b + 1⟩ = .done (.accepted .checked) :=
    (RM024_optimized_accept_refines qmap rfl hacc).2.1 trivial
  have ⟨_, hkr⟩ := kernelStepRaw_of_runRawR_done href
  exact RM016_check_sound ⟨⟨E, n, Γ⟩, .check e A, b + 1⟩ e A rfl hkr

/-- **Converse Runner Completeness (`runRawR` → `runOptRawR` at the same budget):**
    If `s.ambient.env = E` and the reference runner `runRawR m s = .done (.accepted p)`,
    then the optimized runner `runOptRawR qmap m s = .done (.accepted p)` at the
    exact same outer budget `m` and inner budget `s.budget`. -/
theorem RM024_reference_accept_to_optimized {E : ResolvedEnv} (qmap : QIndexMap E)
    {m : Nat} {s : RawState} {p : AcceptedPayload}
    (henv : s.ambient.env = E)
    (hacc : runRawR m s = .done (.accepted p)) :
    runOptRawR qmap m s = .done (.accepted p) := by
  have ⟨hm, hkr⟩ := kernelStepRaw_of_runRawR_done hacc
  rcases s with ⟨⟨E', n, Γ⟩, t, b⟩
  simp only at henv
  subst E'
  cases ht : t with
  | check e A =>
      subst ht
      cases b with
      | zero => exact nomatch hkr
      | succ f =>
          simp only [kernelStepRaw] at hkr
          cases hcc : checkCert E n (f + 1) Γ e A with
          | no msg =>
              rw [hcc] at hkr
              exact nomatch hkr
          | ok c =>
              rw [hcc] at hkr
              injection hkr with hres
              injection hres with hp
              subst hp
              rcases checkCert_refines_checkOptCert qmap hcc with ⟨c', hopt⟩
              have hstep :
                  optStepRaw qmap ⟨⟨E, n, Γ⟩, .check e A, f + 1⟩ =
                    .result (.accepted .checked) := by
                simp only [optStepRaw, hopt]
              exact runOptRawR_pos_eq_of_result hstep (fun h => nomatch h) hm
  | _ =>
      have hnc : ∀ e A, t ≠ .check e A := by
        intro e A h; subst h; exact nomatch ht
      have heq := optStepRaw_nonCheck_eq_kernelStepRaw qmap ⟨⟨E, n, Γ⟩, t, b⟩ rfl hnc
      rw [← ht]
      have hstep : optStepRaw qmap ⟨⟨E, n, Γ⟩, t, b⟩ = .result (.accepted p) :=
        heq.trans hkr
      exact runOptRawR_pos_eq_of_result hstep (fun h => nomatch h) hm

/-- **Two-Way Eventuality Equivalence (`OptTaskEventuallyAccepts ↔ TaskEventuallyAccepts`):**
    For every task `t` and payload `p`, the optimized kernel eventually accepts
    `(⟨E, n, Γ⟩, t, p)` if and only if the reference machine eventually accepts
    `(⟨E, n, Γ⟩, t, p)`. -/
theorem RM024_optimized_eventual_iff_reference {E : ResolvedEnv} (qmap : QIndexMap E)
    (n : Nat) (Γ : LCtx) (t : RawTask) (p : AcceptedPayload) :
    OptTaskEventuallyAccepts qmap ⟨E, n, Γ⟩ t p ↔
      TaskEventuallyAccepts ⟨E, n, Γ⟩ t p := by
  constructor
  · rintro ⟨b, m, hm⟩
    exact (RM024_optimized_accept_refines qmap rfl hm).2.2
  · rintro ⟨b, m, hm⟩
    exact ⟨b, m, RM024_reference_accept_to_optimized qmap rfl hm⟩

/-! ## 5. Named Open `optimized_kernel_wasm_artifact` and Non-Vacuity Pins -/

/-- Abstract host-runner refinement bridge over `OptimizedKernel E`
    (preserved additively alongside the unresolved Wasm lowering open
    `optimized_kernel_wasm_artifact`). -/
structure AbstractOptKernelRunner {E : ResolvedEnv}
    (K : OptimizedKernel E) : Type where
  artifactTag : String
  artifactTag_nonempty : artifactTag ≠ ""
  hostRun : Nat → RawState → RunResumable
  hostAcceptRefinesOpt :
    ∀ {m : Nat} {s : RawState} {p : AcceptedPayload},
      s.ambient.env = E →
      hostRun m s = .done (.accepted p) →
      runOptRawR K.qmap m s = .done (.accepted p)

/-- Composition of `AbstractOptKernelRunner` with `RM024_optimized_accept_refines`. -/
theorem RM024_abstract_runner_refines_reference {E : ResolvedEnv}
    {K : OptimizedKernel E} (R : AbstractOptKernelRunner K)
    {m : Nat} {s : RawState} {p : AcceptedPayload}
    (henv : s.ambient.env = E)
    (hacc : R.hostRun m s = .done (.accepted p)) :
    (∃ b' : Nat, b' ≤ s.budget + 1 ∧
      runRawR m ⟨s.ambient, s.task, b'⟩ = .done (.accepted p)) ∧
    (PositiveTaskPayload s.task p →
      runRawR m ⟨s.ambient, s.task, s.budget + 1⟩ = .done (.accepted p)) ∧
    TaskEventuallyAccepts s.ambient s.task p :=
  RM024_optimized_accept_refines K.qmap henv (R.hostAcceptRefinesOpt henv hacc)

/-- Default empty `NormModule` witness for `Inhabited`. -/
instance instInhabitedNormModule : Inhabited Rcic.WasmNorm.NormModule :=
  ⟨{ funcs := [], memPages := 0, datas := [], entry := 0 }⟩

/-- Canonical SHA-256 hex digest of a raw Wasm binary byte sequence `bs : List UInt8`,
    composed directly from the public exact-byte helper
    `Residua.SHA256.sha256BytesHex`. -/
def wasmBytesSha256Hex (bs : List UInt8) : String :=
  Residua.SHA256.sha256BytesHex bs

/-- Canonical SHA-256 hex digest of a raw Wasm `ByteArray`, projecting the
    underlying byte list structurally and delegating to `wasmBytesSha256Hex`. -/
def wasmByteArraySha256Hex (ba : ByteArray) : String :=
  match ba with
  | ⟨⟨bs⟩⟩ => wasmBytesSha256Hex bs

/-- `wasmByteArraySha256Hex` on `⟨⟨bs⟩⟩` equals `wasmBytesSha256Hex bs`. -/
theorem wasmByteArraySha256Hex_mk (bs : List UInt8) :
    wasmByteArraySha256Hex ⟨⟨bs⟩⟩ = wasmBytesSha256Hex bs := rfl

/-- (V) Unresolved WX lowering of this Lean `OptimizedKernel E` to a
    `Residua-Wasm-0` `NormModule` (`08` §10/§14; R1-B ruling on #7058). -/
opaque lowerOptimizedKernelModule {E : ResolvedEnv}
    (K : OptimizedKernel E) : Rcic.WasmNorm.NormModule

/-- (V) Unresolved WX canonical Wasm binary byte encoding of the lowered
    `OptimizedKernel E` (`08` §3/§10). -/
opaque lowerOptimizedKernelBytes {E : ResolvedEnv}
    (K : OptimizedKernel E) : List UInt8

/-- (V) Unresolved WX `rcic_kernel_wasm_artifact_ref` digest produced by
    lowering this Lean `OptimizedKernel E` (`10:129`, `Rcic.Apex.wasmKeys`). -/
opaque lowerOptimizedKernelArtifactRef {E : ResolvedEnv}
    (K : OptimizedKernel E) : String

/-- (V) Unresolved WX compilation-occurrence / lowering certificate
    (`08:219-224`, `Rcic.Apex.CompilerImplementsCompileSpec` /
    `Rcic.Apex.CompiledWasmRefinesSource`) witnessing that
    `(wasmArtifactRef, wasmModule, wasmBytes)` is the verified Wasm lowering
    of this Lean `K : OptimizedKernel E`. Unassumed on `main`. -/
opaque LoweredOptimizedKernelCert {E : ResolvedEnv}
    (K : OptimizedKernel E) (wasmArtifactRef : String)
    (wasmModule : Rcic.WasmNorm.NormModule) (wasmBytes : List UInt8) : Prop

/-- (V) Canonical wire encoding of an outer step budget `m : Nat` and raw
    kernel state `s : RawState` as input bytes for `Rcic.WasmNorm.normInit`. -/
opaque encodeOptKernelCall (m : Nat) (s : RawState) : List UInt8

/-- (V) Canonical outcome-envelope decoder mapping a `NormFinal.returned`
    `(retI64, mem)` pair from `Rcic.WasmNorm.NormSteps` to `RunResumable`. -/
opaque decodeOptKernelOutcome (retI64 : Int)
    (mem : Rcic.WasmNorm.NormMemory) : Option RunResumable

section WasmArtifactOpen
attribute [local irreducible] wasmBytesSha256Hex

/-- **Named Open `optimized_kernel_wasm_artifact` (cc ruling on #7058, R1-B;
    restated per #7086 audit P2-1):**
    The external compiled Wasm kernel implementation artifact
    (`rcic_kernel_wasm_artifact_ref`, `10_AUTHORITY_HANDOFF.md:129`,
    `Rcic.Apex.wasmKeys`) equals the **lowering of this Lean kernel**
    `K : OptimizedKernel E` into `Residua-Wasm-0` (`Rcic.WasmNorm`), and its
    `NormSteps` execution realizes `runOptRawR K.qmap`:
    1. **Artifact / Lowering Identity:**
       - `wasmModule = lowerOptimizedKernelModule K`
       - `wasmBytes = lowerOptimizedKernelBytes K`
       - `wasmArtifactRef = lowerOptimizedKernelArtifactRef K`
       - `wasmArtifactRef = wasmBytesSha256Hex wasmBytes` and `wasmArtifactRef ≠ ""`
       - `LoweredOptimizedKernelCert K wasmArtifactRef wasmModule wasmBytes`
       - `Rcic.WasmNorm.NormValidModule wasmModule`
    2. **`NormSteps` Execution & Exact Lowering Equivalence:**
       - For every `m` and `s` with `s.ambient.env = E`, `NormSteps` on
         `normInit wasmModule (encodeOptKernelCall m s)` terminates in a
         `.returned retI64 mem` state whose envelope decodes via
         `decodeOptKernelOutcome` to `wasmRun m s`.
       - Every `.done f` outcome of `NormSteps` on
         `normInit wasmModule (encodeOptKernelCall m s)` is a non-trapping
         `.returned retI64 mem` decoding to `wasmRun m s`.
       - `wasmRun m s = runOptRawR K.qmap m s` for all `m` and `s` with
         `s.ambient.env = E` (ruling out both extra acceptances and vacuous
         always-refusing runners). -/
structure optimized_kernel_wasm_artifact {E : ResolvedEnv}
    (K : OptimizedKernel E) : Type where
  wasmArtifactRef : String
  wasmArtifactRef_nonempty : wasmArtifactRef ≠ ""
  wasmModule : Rcic.WasmNorm.NormModule
  wasmBytes : List UInt8
  module_eq_lowering : wasmModule = lowerOptimizedKernelModule K
  bytes_eq_lowering : wasmBytes = lowerOptimizedKernelBytes K
  artifact_eq_lowering : wasmArtifactRef = lowerOptimizedKernelArtifactRef K
  artifact_eq_sha256 : wasmArtifactRef = wasmBytesSha256Hex wasmBytes
  lowering_cert : LoweredOptimizedKernelCert K wasmArtifactRef wasmModule wasmBytes
  module_valid : Rcic.WasmNorm.NormValidModule wasmModule
  wasmRun : Nat → RawState → RunResumable
  wasmRun_normSteps :
    ∀ (m : Nat) (s : RawState),
      s.ambient.env = E →
      ∃ (fuel : Nat) (retI64 : Int) (mem : Rcic.WasmNorm.NormMemory),
        Rcic.WasmNorm.NormSteps fuel
          (Rcic.WasmNorm.normInit wasmModule (encodeOptKernelCall m s)) =
          .done (.returned retI64 mem) ∧
        decodeOptKernelOutcome retI64 mem = some (wasmRun m s)
  normSteps_reflects_wasmRun :
    ∀ {m fuel : Nat} {s : RawState} {f : Rcic.WasmNorm.NormFinal},
      s.ambient.env = E →
      Rcic.WasmNorm.NormSteps fuel
        (Rcic.WasmNorm.normInit wasmModule (encodeOptKernelCall m s)) = .done f →
      ∃ (retI64 : Int) (mem : Rcic.WasmNorm.NormMemory),
        f = .returned retI64 mem ∧
        decodeOptKernelOutcome retI64 mem = some (wasmRun m s)
  wasmRun_eq_runOptRawR :
    ∀ {m : Nat} {s : RawState},
      s.ambient.env = E →
      wasmRun m s = runOptRawR K.qmap m s
  wasmAcceptRefinesOpt :
    ∀ {m : Nat} {s : RawState} {p : AcceptedPayload},
      s.ambient.env = E →
      wasmRun m s = .done (.accepted p) →
      runOptRawR K.qmap m s = .done (.accepted p)

/-- Forgetful projection from `optimized_kernel_wasm_artifact K` to
    `AbstractOptKernelRunner K`. -/
def optimized_kernel_wasm_artifact.toAbstractRunner {E : ResolvedEnv}
    {K : OptimizedKernel E} (W : optimized_kernel_wasm_artifact K) :
    AbstractOptKernelRunner K where
  artifactTag := W.wasmArtifactRef
  artifactTag_nonempty := W.wasmArtifactRef_nonempty
  hostRun := W.wasmRun
  hostAcceptRefinesOpt := W.wasmAcceptRefinesOpt

/-- Exact artifact-to-lowering identity bundle extracted from
    `W : optimized_kernel_wasm_artifact K` (R1-B ruling on #7058). -/
theorem RM024_wasm_artifact_lowering_identity {E : ResolvedEnv}
    {K : OptimizedKernel E} (W : optimized_kernel_wasm_artifact K) :
    W.wasmArtifactRef = lowerOptimizedKernelArtifactRef K ∧
    W.wasmModule = lowerOptimizedKernelModule K ∧
    W.wasmBytes = lowerOptimizedKernelBytes K ∧
    W.wasmArtifactRef = wasmBytesSha256Hex (lowerOptimizedKernelBytes K) ∧
    LoweredOptimizedKernelCert K W.wasmArtifactRef W.wasmModule W.wasmBytes ∧
    Rcic.WasmNorm.NormValidModule W.wasmModule :=
  ⟨W.artifact_eq_lowering, W.module_eq_lowering, W.bytes_eq_lowering,
    W.artifact_eq_sha256.trans (congrArg wasmBytesSha256Hex W.bytes_eq_lowering),
    W.lowering_cert, W.module_valid⟩

end WasmArtifactOpen

/-- Composition of `optimized_kernel_wasm_artifact` with `RM024_optimized_accept_refines`:
    any acceptance of an `optimized_kernel_wasm_artifact` refines the reference
    machine `runRawR` and `TaskEventuallyAccepts`. -/
theorem RM024_wasm_artifact_refines_reference {E : ResolvedEnv}
    {K : OptimizedKernel E} (W : optimized_kernel_wasm_artifact K)
    {m : Nat} {s : RawState} {p : AcceptedPayload}
    (henv : s.ambient.env = E)
    (hacc : W.wasmRun m s = .done (.accepted p)) :
    (∃ b' : Nat, b' ≤ s.budget + 1 ∧
      runRawR m ⟨s.ambient, s.task, b'⟩ = .done (.accepted p)) ∧
    (PositiveTaskPayload s.task p →
      runRawR m ⟨s.ambient, s.task, s.budget + 1⟩ = .done (.accepted p)) ∧
    TaskEventuallyAccepts s.ambient s.task p :=
  RM024_optimized_accept_refines K.qmap henv (W.wasmAcceptRefinesOpt henv hacc)

/-- Direct `NormSteps` execution refinement for `optimized_kernel_wasm_artifact`:
    whenever `NormSteps fuel (normInit W.wasmModule (encodeOptKernelCall m s))`
    terminates in `.done f` and decodes to `.done (.accepted p)`, both
    `W.wasmRun m s = .done (.accepted p)` and `runOptRawR K.qmap m s = .done (.accepted p)`
    hold, and the reference machine `runRawR` accepts at `b' ≤ s.budget + 1`
    (and at `s.budget + 1` under `PositiveTaskPayload`). -/
theorem RM024_wasm_normSteps_accept_refines_reference {E : ResolvedEnv}
    {K : OptimizedKernel E} (W : optimized_kernel_wasm_artifact K)
    {m fuel : Nat} {s : RawState} {retI64 : Int} {mem : Rcic.WasmNorm.NormMemory}
    {p : AcceptedPayload}
    (henv : s.ambient.env = E)
    (hsteps :
      Rcic.WasmNorm.NormSteps fuel
        (Rcic.WasmNorm.normInit W.wasmModule (encodeOptKernelCall m s)) =
        .done (.returned retI64 mem))
    (hdec : decodeOptKernelOutcome retI64 mem = some (.done (.accepted p))) :
    W.wasmRun m s = .done (.accepted p) ∧
    runOptRawR K.qmap m s = .done (.accepted p) ∧
    (∃ b' : Nat, b' ≤ s.budget + 1 ∧
      runRawR m ⟨s.ambient, s.task, b'⟩ = .done (.accepted p)) ∧
    (PositiveTaskPayload s.task p →
      runRawR m ⟨s.ambient, s.task, s.budget + 1⟩ = .done (.accepted p)) ∧
    TaskEventuallyAccepts s.ambient s.task p := by
  rcases W.normSteps_reflects_wasmRun henv hsteps with ⟨ret', mem', hf, hdec'⟩
  injection hf with hret hmem
  subst hret hmem
  have hwasm : W.wasmRun m s = .done (.accepted p) :=
    Option.some.inj (hdec'.symm.trans hdec)
  have hopt : runOptRawR K.qmap m s = .done (.accepted p) :=
    (W.wasmRun_eq_runOptRawR henv).symm.trans hwasm
  exact ⟨hwasm, hopt, RM024_wasm_artifact_refines_reference W henv hwasm⟩

/-- No-trap guarantee for `optimized_kernel_wasm_artifact` under `NormSteps`:
    executing `W.wasmModule` on `encodeOptKernelCall m s` (for `s.ambient.env = E`)
    never terminates in a Wasm `.trapped` state. -/
theorem RM024_wasm_normSteps_no_trap {E : ResolvedEnv}
    {K : OptimizedKernel E} (W : optimized_kernel_wasm_artifact K)
    {m fuel : Nat} {s : RawState}
    (henv : s.ambient.env = E)
    (r : Rcic.WasmNorm.NormTrapReason) (st : Rcic.WasmNorm.NormState) :
    Rcic.WasmNorm.NormSteps fuel
      (Rcic.WasmNorm.normInit W.wasmModule (encodeOptKernelCall m s)) ≠
      .done (.trapped r st) := by
  intro htrap
  rcases W.normSteps_reflects_wasmRun henv htrap with ⟨_, _, hf, _⟩
  exact nomatch hf

/-- Negative control (refutes always-refusing runner inhabitants):
    for any `W : optimized_kernel_wasm_artifact K`, `W.wasmRun` cannot refuse
    all inputs with `s.ambient.env = E`, because on `.syntaxEqual (.sort .zero) (.sort .zero)`
    at budget `(1, 1)` it must accept `.conversionConfirmed` (and its `NormSteps`
    execution must return an envelope decoding to `.done (.accepted .conversionConfirmed)`). -/
theorem RM024_wasm_not_always_refused {E : ResolvedEnv}
    {K : OptimizedKernel E} (W : optimized_kernel_wasm_artifact K) :
    (W.wasmRun 1 ⟨⟨E, 0, []⟩, .syntaxEqual (.sort .zero) (.sort .zero), 1⟩ =
      .done (.accepted .conversionConfirmed)) ∧
    ¬ (∀ (m : Nat) (s : RawState),
        s.ambient.env = E → ∃ msg : String, W.wasmRun m s = .done (.refused msg)) := by
  have hacc :
      W.wasmRun 1 ⟨⟨E, 0, []⟩, .syntaxEqual (.sort .zero) (.sort .zero), 1⟩ =
        .done (.accepted .conversionConfirmed) :=
    W.wasmRun_eq_runOptRawR rfl
  refine ⟨hacc, fun hall => ?_⟩
  rcases hall 1 ⟨⟨E, 0, []⟩, .syntaxEqual (.sort .zero) (.sort .zero), 1⟩ rfl with ⟨msg, href⟩
  rw [hacc] at href
  exact nomatch href

/-- **Pin 1 (Accepting — bidirectional `.lam`/`.pi` with β-redex expected type):**
    Checking `λ (x : Sort 0). x` against the β-redex expected type
    `(λ (X : Sort (imax 1 1)). X) (Π (_ : Sort 0), Sort 0)` (which head-β-reduces
    via `whnfOptCert` to `Π (_ : Sort 0), Sort 0`) succeeds in `runOptRawR` and
    refines to `runRawR` and `TaskEventuallyAccepts`. -/
theorem pin_RM024_lam_betaPi_accepts :
    let u1 := Level.succ .zero
    let e := Expr.lam (.sort .zero) (.bvar 0)
    let T := Expr.app (.lam (.sort (.imax u1 u1)) (.bvar 0))
      (.pi (.sort .zero) (.sort .zero))
    runOptRawR QIndexMap.empty 1 ⟨⟨emptyEnv, 2, []⟩, .check e T, 4⟩ =
      .done (.accepted .checked) ∧
    runRawR 1 ⟨⟨emptyEnv, 2, []⟩, .check e T, 5⟩ =
      .done (.accepted .checked) ∧
    TaskEventuallyAccepts ⟨emptyEnv, 2, []⟩ (.check e T) .checked := by
  dsimp only
  have hopt :
      runOptRawR QIndexMap.empty 1
        ⟨⟨emptyEnv, 2, []⟩,
          .check (.lam (.sort .zero) (.bvar 0))
            (.app (.lam (.sort (.imax (.succ .zero) (.succ .zero))) (.bvar 0))
              (.pi (.sort .zero) (.sort .zero))), 4⟩ =
        .done (.accepted .checked) := rfl
  have href := RM024_optimized_accept_refines QIndexMap.empty rfl hopt
  exact ⟨hopt, href.2.1 trivial, href.2.2⟩

/-- **Pin 2 (Strict inner-fuel gain of the bidirectional `.lam`/`.pi` rule +
    refinement at `b + 1`):**
    With a transparent type alias `Endo0 : Sort (imax 1 1) := Π (_ : Sort 0), Sort 0`
    at index `0`, checking `e = λ (x : Sort 0). x` against `T = .const 0 []`
    at inner budget `b = 2`:
    - `runOptRawR` ACCEPTS at budget `2` (because `checkOptCert` unfolds `T` via
      `whnfOptCert` at fuel `1` and checks `body` at fuel `1`),
    - `runRawR` REFUSES with `"[rcic_infer_fuel]"` at budget `2` (because
      `checkCert` calls `inferCert` on `.lam`, which needs an extra fuel step),
    - `runRawR` ACCEPTS at budget `b + 1 = 3`, witnessing `RM024_optimized_accept_refines`. -/
theorem pin_RM024_lam_fuel2_strict_gain :
    let u1 := Level.succ .zero
    let m : CheckedMember :=
      ⟨.definitionM, 0, .sort (.imax u1 u1), some (.pi (.sort .zero) (.sort .zero))⟩
    let E := extendEnv emptyEnv 0 m
    let qmap : QIndexMap E := QIndexMap.insert QIndexMap.empty 0 m
    let e := Expr.lam (.sort .zero) (.bvar 0)
    let T := Expr.const 0 []
    runOptRawR qmap 1 ⟨⟨E, 2, []⟩, .check e T, 2⟩ =
      .done (.accepted .checked) ∧
    runRawR 1 ⟨⟨E, 2, []⟩, .check e T, 2⟩ =
      .done (.refused "[rcic_infer_fuel]") ∧
    runRawR 1 ⟨⟨E, 2, []⟩, .check e T, 3⟩ =
      .done (.accepted .checked) := by
  dsimp only
  exact ⟨rfl, rfl, rfl⟩

/-- **Pin 3 (Accepting — `QIndexMap.insert` declaration lookup & δ-WHNF):**
    A transparent definition `idSort0 : Sort 1 := Sort 0` registered in
    `QIndexMap.insert QIndexMap.empty 0 m` is accepted by `runOptRawR` on both
    `.lookupDeclaration 0 []` and `.whnfAt (.sort (.succ .zero)) (.const 0 [])`,
    and refines to `runRawR`. -/
theorem pin_RM024_qIndexMap_lookupDecl_accepts :
    let m : CheckedMember := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩
    let E := extendEnv emptyEnv 0 m
    let qmap : QIndexMap E := QIndexMap.insert QIndexMap.empty 0 m
    runOptRawR qmap 1 ⟨⟨E, 2, []⟩, .lookupDeclaration 0 [], 1⟩ =
      .done (.accepted (.inferredType (.sort (.succ .zero)))) ∧
    runRawR 1 ⟨⟨E, 2, []⟩, .lookupDeclaration 0 [], 1⟩ =
      .done (.accepted (.inferredType (.sort (.succ .zero)))) ∧
    runOptRawR qmap 1 ⟨⟨E, 2, []⟩, .whnfAt (.sort (.succ .zero)) (.const 0 []), 2⟩ =
      .done (.accepted (.inferredWhnf (.sort (.succ .zero)) (.sort .zero))) := by
  dsimp only
  exact ⟨rfl, rfl, rfl⟩

/-- **Pin 4 (Refused — ill-typed lambda body rejected by both `runOptRawR` and `runRawR`):**
    Checking `λ (x : Sort 0). Sort 0` (whose body has type `Sort 1`, not `Sort 0`)
    against `Π (_ : Sort 0), Sort 0` is refused with `"[rcic_conv_mismatch]"`
    by both `runOptRawR` and `runRawR`. -/
theorem pin_RM024_check_refused :
    let e := Expr.lam (.sort .zero) (.sort .zero)
    let T := Expr.pi (.sort .zero) (.sort .zero)
    runOptRawR QIndexMap.empty 1 ⟨⟨emptyEnv, 2, []⟩, .check e T, 3⟩ =
      .done (.refused "[rcic_conv_mismatch]") ∧
    runRawR 1 ⟨⟨emptyEnv, 2, []⟩, .check e T, 3⟩ =
      .done (.refused "[rcic_conv_mismatch]") := by
  dsimp only
  exact ⟨rfl, rfl⟩

/-- Mutant SHA-256 helper that maps each byte to a Unicode code point and calls
    the string SHA-256 helper (`Residua.SHA256.sha256Hex`), which re-encodes
    code points `≥ 0x80` as 2-byte UTF-8 sequences (`0xc2/0xc3 …`) instead of
    hashing the raw binary bytes. -/
def mutantUtf8RecodedSha256Hex (bs : List UInt8) : String :=
  Residua.SHA256.sha256Hex (String.mk (bs.map fun b => Char.ofNat b.toNat))

/-- Exact-byte artifact digest check matching `optimized_kernel_wasm_artifact.artifact_eq_sha256`. -/
def wasmArtifactDigestAccepts (artifactRef : String) (bs : List UInt8) : Bool :=
  artifactRef == wasmBytesSha256Hex bs

/-- Mutant UTF-8 recoded artifact digest check (wrongly accepts recoded UTF-8 digests
    and rejects raw binary SHA-256 digests whenever `bs` contains bytes `≥ 0x80`). -/
def mutantUtf8ArtifactDigestAccepts (artifactRef : String) (bs : List UInt8) : Bool :=
  artifactRef == mutantUtf8RecodedSha256Hex bs

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
/-- **Pin 5a (Single high-byte `[0x80]` exact-byte SHA-256 vs UTF-8 recoded mutant):**
    - `wasmBytesSha256Hex [0x80]` hashes the raw byte `0x80` to
      `"76be8b528d0075f7aae98d6fa57a6d3c83ae480a8469e668d7b0af968995ac71"`.
    - `mutantUtf8RecodedSha256Hex [0x80]` hashes the UTF-8 recoding `[0xc2, 0x80]` to
      `"ea0add9a514e94de9abd0ba721eed15b15aa0b3a0f09ebee5e54a9dfae943153"`.
    - `wasmArtifactDigestAccepts` accepts the raw digest and refuses the UTF-8 recoded
      digest, while `mutantUtf8ArtifactDigestAccepts` wrongly accepts the UTF-8 recoded
      digest and rejects the raw digest. -/
theorem pin_RM024_highByte_0x80_sha256_and_mutant :
    let rawHex := "76be8b528d0075f7aae98d6fa57a6d3c83ae480a8469e668d7b0af968995ac71"
    let utf8MutantHex := "ea0add9a514e94de9abd0ba721eed15b15aa0b3a0f09ebee5e54a9dfae943153"
    wasmBytesSha256Hex [0x80] = rawHex ∧
    wasmByteArraySha256Hex ⟨⟨[0x80]⟩⟩ = rawHex ∧
    mutantUtf8RecodedSha256Hex [0x80] = utf8MutantHex ∧
    wasmBytesSha256Hex [0x80] ≠ mutantUtf8RecodedSha256Hex [0x80] ∧
    wasmArtifactDigestAccepts rawHex [0x80] = true ∧
    wasmArtifactDigestAccepts utf8MutantHex [0x80] = false ∧
    mutantUtf8ArtifactDigestAccepts utf8MutantHex [0x80] = true ∧
    mutantUtf8ArtifactDigestAccepts rawHex [0x80] = false := by
  decide

/-- The 492-byte Wasm binary module produced by assembling the landed Wasm emitter's
    numeric fixture (`apps/scm2wasm/programs/boot_l3_num42.run.json`) with `42`
    changed to `128` (`i64.const 128` encoded as `[0x42, 0x80, 0x01]` at offset 437). -/
def wasmNum128ModuleBytes : List UInt8 :=
  [ 0, 97, 115, 109, 1, 0, 0, 0, 1, 34, 7, 96, 1, 127, 1, 127, 96, 2, 127, 127
  , 0, 96, 1, 127, 0, 96, 1, 126, 0, 96, 1, 126, 1, 127, 96, 2, 127, 127, 1, 126
  , 96, 0, 1, 127, 3, 11, 10, 0, 1, 0, 2, 1, 3, 4, 2, 5, 6, 5, 3, 1
  , 0, 64, 6, 14, 2, 127, 1, 65, 128, 128, 192, 0, 11, 127, 1, 65, 0, 11, 7, 40
  , 4, 6, 109, 101, 109, 111, 114, 121, 2, 0, 5, 97, 108, 108, 111, 99, 0, 0, 7, 100
  , 101, 97, 108, 108, 111, 99, 0, 1, 9, 101, 118, 97, 108, 95, 119, 105, 114, 101, 0, 8
  , 10, 192, 2, 10, 6, 0, 65, 128, 128, 4, 11, 2, 0, 11, 23, 1, 1, 127, 35, 0
  , 33, 1, 35, 0, 32, 0, 65, 7, 106, 106, 65, 120, 113, 36, 0, 32, 1, 11, 16, 0
  , 35, 1, 32, 0, 58, 0, 0, 35, 1, 65, 1, 106, 36, 1, 11, 40, 1, 1, 127, 65
  , 0, 33, 2, 2, 64, 3, 64, 32, 2, 32, 1, 78, 13, 1, 32, 0, 32, 2, 106, 45
  , 0, 0, 16, 3, 32, 2, 65, 1, 106, 33, 2, 12, 0, 11, 11, 11, 101, 2, 1, 126
  , 2, 127, 32, 0, 80, 4, 64, 65, 48, 16, 3, 15, 11, 32, 0, 66, 0, 83, 4, 64
  , 65, 45, 16, 3, 66, 0, 32, 0, 125, 33, 1, 5, 32, 0, 33, 1, 11, 65, 208, 0
  , 33, 2, 2, 64, 3, 64, 32, 1, 80, 13, 1, 32, 1, 66, 10, 130, 167, 33, 3, 32
  , 2, 65, 1, 107, 33, 2, 32, 2, 32, 3, 65, 48, 106, 58, 0, 0, 32, 1, 66, 10
  , 128, 33, 1, 12, 0, 11, 11, 32, 2, 65, 208, 0, 32, 2, 107, 16, 4, 11, 26, 1
  , 1, 127, 65, 16, 16, 2, 33, 1, 32, 1, 65, 0, 58, 0, 0, 32, 1, 32, 0, 55
  , 3, 8, 32, 1, 11, 32, 0, 32, 0, 45, 0, 0, 65, 0, 70, 4, 64, 65, 145
  , 32, 65, 17, 16, 4, 32, 0, 41, 3, 8, 16, 5, 65, 253, 0, 16, 3, 11, 11, 56
  , 1, 3, 127, 65, 128, 128, 192, 0, 36, 0, 16, 9, 33, 2, 35, 0, 33, 3, 32, 3
  , 36, 1, 65, 128, 32, 65, 17, 16, 4, 32, 2, 16, 7, 65, 253, 0, 16, 3, 35, 1
  , 32, 3, 107, 33, 4, 32, 3, 173, 66, 32, 134, 32, 4, 173, 132, 11, 7, 0, 66, 128
  , 1, 16, 6, 11, 11, 47, 2, 0, 65, 128, 32, 11, 17, 123, 34, 111, 107, 34, 58, 116
  , 114, 117, 101, 44, 34, 118, 97, 108, 34, 58, 0, 65, 145, 32, 11, 17, 123, 34, 116, 97
  , 103, 34, 58, 34, 105, 110, 116, 34, 44, 34, 110, 34, 58 ]

/-- `ByteArray` wrapper for `wasmNum128ModuleBytes`. -/
def wasmNum128ModuleByteArray : ByteArray :=
  ⟨⟨wasmNum128ModuleBytes⟩⟩

/-- Raw SHA-256 hex digest of the 492-byte `wasmNum128ModuleBytes` binary. -/
def wasmNum128RawSha256Hex : String :=
  "2c222e6b4ee212270ae98f23d56d8ba2dab3e0f5bcc072525e5fced8f8771361"

/-- Erroneous UTF-8 recoded SHA-256 hex digest of `wasmNum128ModuleBytes`. -/
def wasmNum128MutantUtf8Sha256Hex : String :=
  "4f2f41933365df60343c122ef5a83dc0938fb992cf8c1302c7692fb665dc7887"

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
/-- **Pin 5b (Real 492-byte Wasm module raw SHA-256 vs UTF-8 recoded mutant):**
    - `wasmNum128ModuleBytes` has length `492` and contains `[0x42, 0x80, 0x01]`
      at byte offset `437`.
    - `wasmBytesSha256Hex wasmNum128ModuleBytes` and `wasmByteArraySha256Hex wasmNum128ModuleByteArray`
      equal the exact raw binary SHA-256 digest `wasmNum128RawSha256Hex`
      (`"2c222e6b4ee212270ae98f23d56d8ba2dab3e0f5bcc072525e5fced8f8771361"`).
    - `mutantUtf8RecodedSha256Hex wasmNum128ModuleBytes` equals
      `wasmNum128MutantUtf8Sha256Hex`
      (`"4f2f41933365df60343c122ef5a83dc0938fb992cf8c1302c7692fb665dc7887"`).
    - `wasmArtifactDigestAccepts` accepts `wasmNum128RawSha256Hex` and refuses
      `wasmNum128MutantUtf8Sha256Hex`, whereas `mutantUtf8ArtifactDigestAccepts`
      wrongly accepts `wasmNum128MutantUtf8Sha256Hex` and rejects `wasmNum128RawSha256Hex`. -/
theorem pin_RM024_wasmNum128Module_sha256_and_mutant :
    wasmNum128ModuleBytes.length = 492 ∧
    (wasmNum128ModuleBytes.drop 437).take 3 = [0x42, 0x80, 0x01] ∧
    wasmBytesSha256Hex wasmNum128ModuleBytes = wasmNum128RawSha256Hex ∧
    wasmByteArraySha256Hex wasmNum128ModuleByteArray = wasmNum128RawSha256Hex ∧
    mutantUtf8RecodedSha256Hex wasmNum128ModuleBytes = wasmNum128MutantUtf8Sha256Hex ∧
    wasmBytesSha256Hex wasmNum128ModuleBytes ≠
      mutantUtf8RecodedSha256Hex wasmNum128ModuleBytes ∧
    wasmArtifactDigestAccepts wasmNum128RawSha256Hex wasmNum128ModuleBytes = true ∧
    wasmArtifactDigestAccepts wasmNum128MutantUtf8Sha256Hex wasmNum128ModuleBytes = false ∧
    mutantUtf8ArtifactDigestAccepts wasmNum128MutantUtf8Sha256Hex wasmNum128ModuleBytes = true ∧
    mutantUtf8ArtifactDigestAccepts wasmNum128RawSha256Hex wasmNum128ModuleBytes = false := by
  decide

/-- Direct consequence for `optimized_kernel_wasm_artifact`: any artifact bundle `W`
    whose `wasmBytes` equals `wasmNum128ModuleBytes` has `W.wasmArtifactRef` equal to
    the raw binary SHA-256 `wasmNum128RawSha256Hex` and never equal to the UTF-8
    recoded mutant digest `wasmNum128MutantUtf8Sha256Hex`. -/
theorem RM024_wasm_artifact_num128_digest_exact_not_utf8_mutant {E : ResolvedEnv}
    {K : OptimizedKernel E} (W : optimized_kernel_wasm_artifact K)
    (hbytes : W.wasmBytes = wasmNum128ModuleBytes) :
    W.wasmArtifactRef = wasmNum128RawSha256Hex ∧
    W.wasmArtifactRef ≠ wasmNum128MutantUtf8Sha256Hex := by
  have hraw : wasmBytesSha256Hex wasmNum128ModuleBytes = wasmNum128RawSha256Hex :=
    pin_RM024_wasmNum128Module_sha256_and_mutant.2.2.1
  have hmut : mutantUtf8RecodedSha256Hex wasmNum128ModuleBytes = wasmNum128MutantUtf8Sha256Hex :=
    pin_RM024_wasmNum128Module_sha256_and_mutant.2.2.2.2.1
  have hne :
      wasmBytesSha256Hex wasmNum128ModuleBytes ≠
        mutantUtf8RecodedSha256Hex wasmNum128ModuleBytes :=
    pin_RM024_wasmNum128Module_sha256_and_mutant.2.2.2.2.2.1
  have hart : W.wasmArtifactRef = wasmNum128RawSha256Hex :=
    W.artifact_eq_sha256.trans ((congrArg wasmBytesSha256Hex hbytes).trans hraw)
  refine ⟨hart, ?_⟩
  intro hbad
  exact hne (hraw.trans (hart.symm.trans (hbad.trans hmut.symm)))

end Rcic.Machine.Optimized

