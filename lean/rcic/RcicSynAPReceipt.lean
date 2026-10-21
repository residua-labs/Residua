import rcic.RcicSynLetInline

/-!
# W-COV-AP-NATIVE-REPLACEMENT — the general enriched AP `esub`/`lsub` transport receipt

Approved design: `research/rcic/sortrow/S2_AP_TRANSPORT_RECEIPTS.md` §1–3
(**ChatGPT**, J line; committed on `claude/chatgpt-s2-coverage`, PR #7311).
The pinned instance is `S2_AP_PREFIX_ALIGNMENT.md` §5, named
**W-COV-AP-SORT-EXPOSURE**. `closure_claim` stays `0`.

## §1 Two routes stay separate

A native origin keeps `SortTyTransport` and a real `HasTyT` replacement. A
general AP origin uses the new enriched receipts `EsubAPReceipt` /
`LsubAPReceipt` below: each stores the ACTUAL derivation `D`, the context
premise `hget`, and the two replacement typings `hv`/`hvT`, and `run` emits
only the original `TyP.esub` / `TyP.lsub` (`run_is_esub`, `run_is_lsub`).
No new `TyP` constructor is introduced, and `hv` is never restored to an
`HasTyT` that was never obtained. The output index is fixed:
`instantiate j (lift 0 j v) T`.

## §2 The general type and the sort-only subfamily are separate

`EsubSortReceipt` / `LsubSortReceipt` are the same receipts at a literally
sort-typed source `T = .sort u₀`; on them the transported output is still
`.sort u₀` (`esubSortReceipt_output`). The subfamily is a strict subset of
the general receipt — it neither narrows the AP domain nor accepts a wrong
input. §5's exposure instance is accepted by the general receipt and
refused by the subfamily (`APSortExposure.general_accepts`,
`APSortExposure.source_not_sort`, `APSortExposure.source_gate_none`).

## §3 AP, budget, and the native bridge stay separate obligations

`run_assumpPref`/`lrun_assumpPref` keep AP field by field from the original
constructor (`AssumptionPrefix Γ j`, `D.AssumpPref`, `hv.AssumpPref`,
`hvT.AssumpPref`). `run_atoms`/`run_wt` (and the `lsub` twins) keep main's
exact formulas (`D.atoms ++ hv.atoms ++ hvT.atoms`,
`1 + D.wt + hv.wt + hvT.wt`). The receipts change no accounts and supply no
changed-spine combined edge by themselves. A receipt is NOT native
lowering: nothing here produces `CtxWfT` or an `HasTyT` witness, and no
`enrich(native) = lazy TyP.esub` literal equality is claimed. When the
origin really is native, that correspondence is a separate proof.

## Teeth

- `run_is_esub` / `run_is_lsub`: `run` is definitionally the original
  constructor applied to the stored fields — a mutant `run` (any other
  production) breaks these.
- `hget`/`hv`/`hvT` are mandatory fields with the constructor's exact
  types: dropping one, or changing an index/type, fails to form the
  receipt.
- `APSortExposure.slot_is_assumption` / `slot_not_let`: the `esub`
  premise is pinned to the `.assumption` shape; the `.letBinding` shape
  (and symmetrically for `lsub`) is refused.
- `run_assumpPref` etc.: AP is required at EVERY layer (prefix at `j` plus
  all three children), matching the constructor's definition — the
  exposure pin `hA_is_AP` exercises `wk ∘ esub ∘ bvar ∘ sort`.
- `run_atoms`/`run_wt`: all three components, in the constructor's order
  and formula.
- `APSortExposure`: general receipt accepts, sort-only subfamily refuses —
  the "source already sort" contract is shown false on well-formed data.
- `sortReceipt`/`lsubReceipt`: both subfamilies/receipts are inhabited on
  honest data — the refusal is not vacuity.

## Residuals (S2 "not closable yet", unchanged)

Full prefix reflection for arbitrary ambient `hA`; working-spine budgets
of deep introduced forests; ι's complete typed-spine/mask/rhs
correspondence; full-domain compilation of relevant-result, erased-major
ι; the canonical δ body's level-erasure correspondence under general maps.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 The general enriched receipts -/

/-- S2 §1: a general AP-origin `esub` receipt. It stores the actual
    derivation `D`, the lookup premise `hget`, and the replacement typings
    `hv`/`hvT` — the exact premises of `TyP.esub`, nothing reconstructed. -/
structure EsubAPReceipt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (e T t v : Expr Nat) (j : Nat) (u : Level) where
  D : TyP E n Γ e T
  hget : Γ[j]? = some (.assumption t)
  hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)
  hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)

/-- `run` emits ONLY the original `TyP.esub`. -/
def EsubAPReceipt.run {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (R : EsubAPReceipt E n Γ e T t v j u) :
    TyP E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) T) :=
  TyP.esub E n Γ e T t v j u R.D R.hget R.hv R.hvT

/-- S2 §1's let twin: the same fields, `hget` pins a `.letBinding t v`
    slot, and `run` emits the original `TyP.lsub` at the actual stored
    value `v`. -/
structure LsubAPReceipt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (e T t v : Expr Nat) (j : Nat) (u : Level) where
  D : TyP E n Γ e T
  hget : Γ[j]? = some (.letBinding t v)
  hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)
  hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)

/-- `run` emits ONLY the original `TyP.lsub`. -/
def LsubAPReceipt.run {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (R : LsubAPReceipt E n Γ e T t v j u) :
    TyP E n (substRemove v j Γ)
      (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) T) :=
  TyP.lsub E n Γ e T t v j u R.D R.hget R.hv R.hvT

/-! ## §2 The sort-only subfamily -/

/-- The sort-preserving subfamily: the general receipt at a source type
    literally of the form `.sort u₀`. A strict subset — same data,
    narrower index. -/
abbrev EsubSortReceipt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (e t v : Expr Nat) (j : Nat) (u₀ u : Level) :=
  EsubAPReceipt E n Γ e (.sort u₀) t v j u

/-- The let twin's sort-only subfamily. -/
abbrev LsubSortReceipt (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (e t v : Expr Nat) (j : Nat) (u₀ u : Level) :=
  LsubAPReceipt E n Γ e (.sort u₀) t v j u

/-- The mechanical gate the subfamily applies to the source type:
    `some u₀` only when it is literally `.sort u₀`. -/
def sourceSortOf : Expr Nat → Option Level
  | .sort u => some u
  | _ => none

/-- S2 §2: on a sort-source receipt the transported output type is the
    same sort — `instantiate` is the identity on `.sort u₀`. -/
theorem esubSortReceipt_output {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e t v : Expr Nat} {j : Nat} {u₀ u : Level}
    (_R : EsubSortReceipt E n Γ e t v j u₀ u) :
    instantiate j (lift 0 j v) (.sort u₀) = .sort u₀ := rfl

theorem lsubSortReceipt_output {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e t v : Expr Nat} {j : Nat} {u₀ u : Level}
    (_R : LsubSortReceipt E n Γ e t v j u₀ u) :
    instantiate j (lift 0 j v) (.sort u₀) = .sort u₀ := rfl

/-! ## §3 The exact contracts: `run`, AP, atoms, wt -/

/-- `run` is definitionally the original `TyP.esub` applied to the stored
    fields — no new constructor, no other production. -/
theorem EsubAPReceipt.run_is_esub {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (R : EsubAPReceipt E n Γ e T t v j u) :
    R.run = TyP.esub E n Γ e T t v j u R.D R.hget R.hv R.hvT := rfl

theorem LsubAPReceipt.run_is_lsub {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (R : LsubAPReceipt E n Γ e T t v j u) :
    R.run = TyP.lsub E n Γ e T t v j u R.D R.hget R.hv R.hvT := rfl

/-- The receipt's output indices are functions of the stored data only —
    the "fixed output index" of S2 §2. -/
abbrev EsubAPReceipt.outTerm {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (_R : EsubAPReceipt E n Γ e T t v j u) : Expr Nat :=
  instantiate j (lift 0 j v) e

abbrev EsubAPReceipt.outType {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (_R : EsubAPReceipt E n Γ e T t v j u) : Expr Nat :=
  instantiate j (lift 0 j v) T

/-- `run` lands exactly at the fixed index — not at `T` itself, not at a
    recovered sort. -/
def EsubAPReceipt.run_at_fixed_index {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (R : EsubAPReceipt E n Γ e T t v j u) :
    TyP E n (substRemove v j Γ) R.outTerm R.outType := R.run

abbrev LsubAPReceipt.outTerm {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (_R : LsubAPReceipt E n Γ e T t v j u) : Expr Nat :=
  instantiate j (lift 0 j v) e

abbrev LsubAPReceipt.outType {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (_R : LsubAPReceipt E n Γ e T t v j u) : Expr Nat :=
  instantiate j (lift 0 j v) T

def LsubAPReceipt.run_at_fixed_index {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (R : LsubAPReceipt E n Γ e T t v j u) :
    TyP E n (substRemove v j Γ) R.outTerm R.outType := R.run

/-- AP is kept field by field from the original constructor:
    `AssumptionPrefix Γ j` at the substitution index, plus `AssumpPref` of
    all three children — at every layer, not only at the root. -/
theorem EsubAPReceipt.run_assumpPref {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (R : EsubAPReceipt E n Γ e T t v j u) :
    R.run.AssumpPref =
      (AssumptionPrefix Γ j ∧ R.D.AssumpPref ∧ R.hv.AssumpPref ∧
        R.hvT.AssumpPref) := rfl

theorem LsubAPReceipt.run_assumpPref {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (R : LsubAPReceipt E n Γ e T t v j u) :
    R.run.AssumpPref =
      (AssumptionPrefix Γ j ∧ R.D.AssumpPref ∧ R.hv.AssumpPref ∧
        R.hvT.AssumpPref) := rfl

/-- Atoms keep main's exact formula — all three components, in the
    constructor's order. -/
theorem EsubAPReceipt.run_atoms {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (Aw : Nat → Nat) (R : EsubAPReceipt E n Γ e T t v j u) :
    R.run.atoms Aw = R.D.atoms Aw ++ R.hv.atoms Aw ++ R.hvT.atoms Aw := rfl

theorem LsubAPReceipt.run_atoms {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (Aw : Nat → Nat) (R : LsubAPReceipt E n Γ e T t v j u) :
    R.run.atoms Aw = R.D.atoms Aw ++ R.hv.atoms Aw ++ R.hvT.atoms Aw := rfl

/-- Weight keeps main's exact formula `1 + D.wt + hv.wt + hvT.wt`. -/
theorem EsubAPReceipt.run_wt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (Aw : Nat → Nat) (R : EsubAPReceipt E n Γ e T t v j u) :
    R.run.wt Aw = 1 + R.D.wt Aw + R.hv.wt Aw + R.hvT.wt Aw := rfl

theorem LsubAPReceipt.run_wt {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T t v : Expr Nat} {j : Nat} {u : Level}
    (Aw : Nat → Nat) (R : LsubAPReceipt E n Γ e T t v j u) :
    R.run.wt Aw = 1 + R.D.wt Aw + R.hv.wt Aw + R.hvT.wt Aw := rfl

/-! ## §4 W-COV-AP-SORT-EXPOSURE (`S2_AP_PREFIX_ALIGNMENT` §5) -/

namespace APSortExposure

/-- `s₀`, `s₁`, `s₂` (emptyEnv, arity 0). -/
def s0 : Expr Nat := .sort .zero
def s1 : Expr Nat := .sort (.succ .zero)
def s2 : Expr Nat := .sort (.succ (.succ .zero))

/-- `Σ = [x : Y, Y : s₁]`, newest first: `x` stores `.bvar 0` (the slot of
    `Y`), `Y` stores `s₁`. -/
def SigmaC : LCtx := [.assumption (.bvar 0), .assumption s1]
/-- `Δ = [P : s₀]`. -/
def DeltaC : LCtx := [.assumption s0]
/-- `Γ = [z : P, P : s₀]`. -/
def GammaC : LCtx := [.assumption (.bvar 0), .assumption s0]

/-- `DY : Σ ⊢ bvar 1 : s₁`. -/
def DY : TyP emptyEnv 0 SigmaC (.bvar 1) s1 :=
  .bvar _ _ _ 1 s1 (.succ (.succ .zero)) rfl
    (.sort _ _ _ (.succ .zero) (.succ (.succ .zero)) (fun _ => rfl))

/-- `DX : Σ ⊢ bvar 0 : bvar 1` — `x : Y`. Its type is literally `bvar 1`,
    NOT a sort: this is the exposure. -/
def DX : TyP emptyEnv 0 SigmaC (.bvar 0) (.bvar 1) :=
  .bvar _ _ _ 0 (.bvar 1) (.succ .zero) rfl DY

/-- `hv : Δ ⊢ s₀ : s₁` — the actual replacement typing (stated in `Δ`;
    `substRemove s₀ 1 Σ` computes to `Δ`). -/
def hvexp : TyP emptyEnv 0 DeltaC s0 s1 :=
  .sort _ _ _ .zero (.succ .zero) (fun _ => rfl)

/-- `hvT : Δ ⊢ s₁ : s₂`. -/
def hvTexp : TyP emptyEnv 0 DeltaC s1 s2 :=
  .sort _ _ _ (.succ .zero) (.succ (.succ .zero)) (fun _ => rfl)

/-- The general receipt over the actual §5 data: substituting `s₀` for `Y`
    at `j = 1`. Accepted — all four fields are the real premises. -/
def qReceipt : EsubAPReceipt emptyEnv 0 SigmaC (.bvar 0) (.bvar 1)
    s1 s0 1 (.succ (.succ .zero)) where
  D := DX
  hget := rfl
  hv := hvexp
  hvT := hvTexp

/-- `Q := run` is `Δ ⊢ bvar 0 : s₀`. -/
def Qexp : TyP emptyEnv 0 DeltaC (.bvar 0) s0 := qReceipt.run

/-- `hA := wk` at cutoff `0`: `Γ ⊢ bvar 1 : s₀`. -/
def hAexp : TyP emptyEnv 0 GammaC (.bvar 1) s0 :=
  .wk _ _ DeltaC (.bvar 0) s0 (.assumption (.bvar 0)) 0 Qexp

/-- The public bvar `Γ ⊢ z : P`, carrying `hAexp` as its sort witness —
    an esub-transported child inside an ordinary derivation. -/
def publicZ : TyP emptyEnv 0 GammaC (.bvar 0) (.bvar 1) :=
  .bvar _ _ _ 0 (.bvar 1) .zero rfl hAexp

/-- §5 pin (i): the general receipt accepts — `run` is `Q`. -/
theorem general_accepts : qReceipt.run = Qexp := rfl

/-- §5 pin (ii): `DX`'s source type is not literally any sort — so the
    sort-only subfamily refuses this instance (its index `T` cannot be
    unified with `.sort u₀`). -/
theorem source_not_sort : ∀ u : Level, (.bvar 1 : Expr Nat) ≠ .sort u :=
  fun _ h => Expr.noConfusion h

/-- §5 pin (ii), executable: the subfamily's gate returns `none` on the
    instance's source type. -/
theorem source_gate_none : sourceSortOf (.bvar 1 : Expr Nat) = none := rfl

/-- §5 pin (iii): the actual output type is `s₀` — the final bit (entry
    sort, and `u`) is `0`; only the wrong source-recovery contract fails. -/
theorem output_is_s0 : instantiate 1 (lift 0 1 s0) (.bvar 1) = s0 := rfl

/-- The `esub` premise is honest about the slot kind: `Σ[1]` is an
    `.assumption`. -/
theorem slot_is_assumption :
    SigmaC[1]? = some (.assumption s1) := rfl

/-- …and never a `.letBinding` — an `lsub`-shaped `hget` on this slot
    cannot be formed. -/
theorem slot_not_let (t v : Expr Nat) :
    SigmaC[1]? ≠ some (.letBinding t v) := by
  rw [slot_is_assumption]
  intro h
  injection h with h'
  exact LocalDecl.noConfusion h'

/-- `Σ` satisfies `AssumptionPrefix` at the substitution index `1`. -/
theorem prefix_sigma1 : AssumptionPrefix SigmaC 1 := fun d hd =>
  ⟨.bvar 0, List.mem_singleton.mp (by
    have htake : SigmaC.take 1 = [.assumption (.bvar 0)] := rfl
    rwa [htake] at hd)⟩

/-- `Δ` satisfies `AssumptionPrefix` at `0` (vacuously). -/
theorem prefix_delta0 : AssumptionPrefix DeltaC 0 := fun _d hd => nomatch hd

/-- §5 pin (iv): `Q` is AP at every layer — prefix at `j` and all three
    children. -/
theorem Q_is_AP : Qexp.AssumpPref :=
  ⟨prefix_sigma1, trivial, trivial, trivial⟩

/-- §5 pin (iv): `hA` (`wk` over the esub) is AP. -/
theorem hA_is_AP : hAexp.AssumpPref := ⟨prefix_delta0, Q_is_AP⟩

/-- §5 pin (v): all three contexts are natively well-formed. -/
def wfSigma : CtxWfT emptyEnv 0 SigmaC :=
  .assumption _ (.bvar 0) (.succ .zero)
    (.assumption _ s1 (.succ (.succ .zero)) .nil (.sort _ (.succ .zero)))
    (.bvar _ 0 s1 rfl)

def wfDelta : CtxWfT emptyEnv 0 DeltaC :=
  .assumption _ s0 (.succ .zero) .nil (.sort _ .zero)

def wfGamma : CtxWfT emptyEnv 0 GammaC :=
  .assumption _ (.bvar 0) .zero
    (.assumption _ s0 (.succ .zero) .nil (.sort _ .zero))
    (.bvar _ 0 s0 rfl)

/-- The concrete accounts on the exposure: `Q` weighs `6` and carries
    atoms `[3, 1, 1]` for every `Aw` — `D` first, then `hv`, then `hvT`. -/
theorem exposure_wt (Aw : Nat → Nat) : Qexp.wt Aw = 6 := rfl

theorem exposure_atoms (Aw : Nat → Nat) : Qexp.atoms Aw = [3, 1, 1] := rfl

/-- A sort-source receipt in the same context family (substituting `s₀`
    for the `s₁`-typed variable at `j = 0`): here the source type `s₁` IS
    literally a sort, so the subfamily accepts — the refusal above is not
    vacuity. -/
def sortReceipt : EsubSortReceipt emptyEnv 0 [.assumption s1] (.bvar 0)
    s1 s0 0 (.succ .zero) (.succ (.succ .zero)) where
  D := .bvar _ _ _ 0 s1 (.succ (.succ .zero)) rfl
    (.sort _ _ _ (.succ .zero) (.succ (.succ .zero)) (fun _ => rfl))
  hget := rfl
  hv := .sort _ _ _ .zero (.succ .zero) (fun _ => rfl)
  hvT := .sort _ _ _ (.succ .zero) (.succ (.succ .zero)) (fun _ => rfl)

/-- On the sort-source receipt the output sort is preserved literally. -/
theorem sortReceipt_output :
    instantiate 0 (lift 0 0 s0) s1 = s1 := rfl

/-- The let twin on a real `.letBinding` slot: `z : s₁ := s₀` at `j = 0`
    inlines the stored value — `run` lands at `[] ⊢ s₀ : s₁`. -/
def lsubReceipt : LsubAPReceipt emptyEnv 0 [.letBinding s1 s0]
    (.bvar 0) s1 s1 s0 0 (.succ (.succ .zero)) where
  D := .bvar _ _ _ 0 s1 (.succ (.succ .zero)) rfl
    (.sort _ _ _ (.succ .zero) (.succ (.succ .zero)) (fun _ => rfl))
  hget := rfl
  hv := .sort _ _ _ .zero (.succ .zero) (fun _ => rfl)
  hvT := .sort _ _ _ (.succ .zero) (.succ (.succ .zero)) (fun _ => rfl)

/-- The `lsub` premise is honest about the slot kind: `Γ[0]` is a
    `.letBinding`, never an `.assumption`. -/
theorem lsub_slot_not_assumption (t : Expr Nat) :
    ([.letBinding s1 s0] : LCtx)[0]? ≠ some (.assumption t) := by
  intro h
  have hl : ([.letBinding s1 s0] : LCtx)[0]? = some (.letBinding s1 s0) := rfl
  rw [hl] at h
  injection h with h'
  exact LocalDecl.noConfusion h'

end APSortExposure

end Rcic.Syn
