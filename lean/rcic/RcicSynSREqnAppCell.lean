import rcic.RcicSynSREqnAlias

/-!
# RcicSynSREqnAppCell — row 14: `appCl` measured on-cone

cc 2026-10-21 11:30Z brief, lane glm/sr4-eqn (new draft PR). Cells
smallest-first: `appCl`'s port is ONLY the `shape` trichotomy (both-`★`
on `hf` / both-`★` on `ha` / all four non-`★`) — no `CL` content.

## Verdict

* `shape` is propositionally the conjunction of two `TagCoh`-star-iffs —
  `clAppPorts_of_tagCoh` (§1) is the exact reduction. The residual is the
  `W-COV-HETERO-PROOF-STATUS` wall in cell form: two derivations of one
  subject agree on erased proof-status iff their gate universes are `=ₙ`,
  which is sort-uniqueness — a forbidden input, semantically pinned,
  kernel-unprovable. **Not refutable**: every gate-`u` in a `TyP`
  derivation is pinned to a context/type universe modulo `eqN`
  (transports `esub`/`lsub`/`linst`/`wk`/`ewk`/`cctx`/`conv` re-pin
  through `hv`-inhabitability or `instantiate`-preimages — measured by
  exhaustive case analysis of the eps grammar, §4 note).
* The cell is **inhabited on-cone** (§3): `sr5_appCl_sat` realizes
  `ClAppPorts` at `σ = id` (a `LevelHom`), `ρ = []` (`DispFor`-routed at
  `[]`), with `hf₁` a `const`-node and `hf₂` an `esub`-headed second
  derivation of the same subject/type — two genuinely different
  derivations whose erasures agree (`= .const 2 [.one,one]`).
* `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative
open DispForPathPins (one two)

/-! ## §1 `shape` = two `TagCoh` star-iffs -/

/-- The `appCl` port is satisfied by star-status agreement on the two
    pairs. Propositional glue only: `hf₁★↔hf₂★` picks disjunct one or
    three; `ha₁★↔ha₂★` picks two or three. -/
theorem clAppPorts_of_iffs {tbl : List CRule} {σ : Level → Level} {ρ : List Disp}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat}
    {hf₁ : TyP E n Γ f (.pi A₁ B₁)} {ha₁ : TyP E n Γ a A₁}
    {hf₂ : TyP E n Γ f (.pi A₂ B₂)} {ha₂ : TyP E n Γ a A₂}
    (hf : hf₁.eps σ ρ = .star ↔ hf₂.eps σ ρ = .star)
    (ha : ha₁.eps σ ρ = .star ↔ ha₂.eps σ ρ = .star) :
    ClAppPorts tbl σ ρ hf₁ ha₁ hf₂ ha₂ :=
  ⟨by
    by_cases h₁ : hf₁.eps σ ρ = .star
    · exact .inl ⟨h₁, hf.mp h₁⟩
    · by_cases h₂ : ha₁.eps σ ρ = .star
      · exact .inr (.inl ⟨h₂, ha.mp h₂⟩)
      · exact .inr (.inr ⟨h₁, h₂, fun h => h₁ (hf.mpr h), fun h => h₂ (ha.mpr h)⟩)⟩

/-- The cell residual named: `appCl`'s port is `TagCoh × TagCoh` at
    identical `(σ, ρ)` — the heterogeneous proof-status wall in cell
    form. -/
theorem clAppPorts_of_tagCoh {tbl : List CRule} {σ : Level → Level} {ρ : List Disp}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A₁ B₁ A₂ B₂ : Expr Nat}
    {hf₁ : TyP E n Γ f (.pi A₁ B₁)} {ha₁ : TyP E n Γ a A₁}
    {hf₂ : TyP E n Γ f (.pi A₂ B₂)} {ha₂ : TyP E n Γ a A₂}
    (hf : TagCoh σ ρ σ ρ hf₁ hf₂) (ha : TagCoh σ ρ σ ρ ha₁ ha₂) :
    ClAppPorts tbl σ ρ hf₁ ha₁ hf₂ ha₂ :=
  clAppPorts_of_iffs hf ha

/-! ## §2 the fixture env -/

/-- `F : pi (const 0 [param 0]) (const 0 [param 1])`, arity 2 — a
    function-typed axiom member. -/
def sr5PiFun : CheckedMember :=
  { mclass := .axiomM, arity := 2,
    mtype := .pi (.const 0 [.param 0]) (.const 0 [.param 1]), body := none }

/-- `sr5Env` — `sr4AliasEnv` plus `sr5PiFun` at index 2. -/
def sr5Env : ResolvedEnv := extendEnv sr4AliasEnv 2 sr5PiFun

theorem sr5Env_members0 : sr5Env.members 0 = some sr3Mem := rfl

theorem sr5Env_members1 : sr5Env.members 1 = some sr4AliasMem := rfl

theorem sr5Env_members2 : sr5Env.members 2 = some sr5PiFun := rfl

/-- `c00 = const 0 [.zero]` (`: .sort .zero`); `c10 = const 0 [one]`
    (`: .sort one`). -/
def sr5C00 : Expr Nat := .const 0 [.zero]

def sr5C10 : Expr Nat := .const 0 [one]

/-- `c00 : .sort .zero` / `c10 : .sort one` in any context. -/
def sr5C00T (Γ : LCtx) : TyP sr5Env 2 Γ sr5C00 (.sort .zero) :=
  TyP.const sr5Env 2 Γ 0 [.zero] [.zero] sr3Mem one sr5Env_members0 rfl rfl
    (eqNList_refl _) (TyP.sort sr5Env 2 Γ .zero one (eqN_refl _))

def sr5C10T (Γ : LCtx) : TyP sr5Env 2 Γ sr5C10 (.sort one) :=
  TyP.const sr5Env 2 Γ 0 [one] [one] sr3Mem two sr5Env_members0 rfl rfl
    (eqNList_refl _) (TyP.sort sr5Env 2 Γ one two (eqN_refl _))

/-- `T₂ = pi c10 c10 : .sort (.imax one one)` — nonzero-gated, in any
    context. -/
def sr5T₂ : Expr Nat := .pi sr5C10 sr5C10

def sr5T₂T (Γ : LCtx) : TyP sr5Env 2 Γ sr5T₂ (.sort (.imax one one)) :=
  TyP.pi sr5Env 2 Γ sr5C10 one sr5C10 one (sr5C10T Γ)
    (sr5C10T (.assumption sr5C10 :: Γ))

/-! ## §3 the two `f`-typings, the `a`-typing, and the inhabited port -/

/-- `f = const 2 [.one,one] : T₂`, the direct `const`-head derivation —
    the gate `imax one one` is `levelIsZero`-false, so the eps is the
    const itself. -/
def sr5hf₁ : TyP sr5Env 2 [] (.const 2 [one, one]) sr5T₂ :=
  TyP.const sr5Env 2 [] 2 [one, one] [one, one] sr5PiFun
    (.imax one one) sr5Env_members2 rfl rfl (eqNList_refl _) (sr5T₂T [])

/-- The `esub`'s inner `bvar 0 : T₂` in `[assumption T₂]`. -/
def sr5D₂ : TyP sr5Env 2 [.assumption sr5T₂] (.bvar 0) sr5T₂ :=
  TyP.bvar sr5Env 2 [.assumption sr5T₂] 0 sr5T₂ (.imax one one) rfl
    (sr5T₂T [.assumption sr5T₂])

/-- `v = const 2 [.one,one] : T₂` — the substituted value. -/
def sr5hv : TyP sr5Env 2 [] (.const 2 [one, one]) sr5T₂ :=
  sr5hf₁

/-- `T₂ : .sort (.imax one one)` — the eliminated assumption's sort
    typing, in the outer context `[]` (`lift 0 0` fixes `T₂`). -/
def sr5hvT : TyP sr5Env 2 [] sr5T₂ (.sort (.imax one one)) :=
  sr5T₂T []

/-- `f = const 2 [.one,one] : T₂`, `esub`-headed: eliminate the sole
    assumption `T₂` at index 0 of `[assumption T₂]` by `v`. `substRemove
    v 0 [_] = []`, `instantiate 0 (lift 0 0 v) (bvar 0) = v`, and the
    erased side computes `inst 0 (.const 2 [1,1]) (bvar 0) =
    .const 2 [1,1]` — the `inst` substitution hits the kept slot and
    returns the value's own erasure. -/
def sr5hf₂ : TyP sr5Env 2 [] (.const 2 [one, one]) sr5T₂ :=
  TyP.esub sr5Env 2 [.assumption sr5T₂] (.bvar 0) sr5T₂ sr5T₂
    (.const 2 [one, one]) 0 (.imax one one) sr5D₂ rfl sr5hv sr5hvT

/-- `a = const 1 [one] : c10` — the landed alias member's instance. -/
def sr5ha : TyP sr5Env 2 [] (.const 1 [one]) sr5C10 :=
  TyP.const sr5Env 2 [] 1 [one] [one] sr4AliasMem one sr5Env_members1
    rfl rfl (eqNList_refl _) (sr5C10T [])

/-! ## §4 the eps values and the port -/

theorem sr5_hf₁_eps : sr5hf₁.eps id [] = .const 2 [one, one] := rfl

theorem sr5_hf₂_eps : sr5hf₂.eps id [] = .const 2 [one, one] := rfl

theorem sr5_ha_eps : sr5ha.eps id [] = .const 1 [one] := rfl

/-- On-cone: `id` is a `LevelHom`; `[]` is the `DispFor`-routed display
    of the empty context. -/
theorem sr5_disp : DispForHom id sr5Env 2 [] [] :=
  dispForHom_nil levelHom_id sr5Env 2

/-- `ClAppPorts` is INHABITED on-cone at the all-non-`★` disjunct: two
    different derivations (`const`-head vs `esub`-`inst`-hit) of one
    subject `const 2 [.one,one]` at one type `T₂` erase identically, and
    the argument's erasure is the non-`★` `const 1 [one]`. The `esub`
    instance is demand-shaped — its `hf₂` is exactly the kind of
    substitution-transport the `cl` case pairs against a head
    derivation. -/
theorem sr5_appCl_sat (tbl : List CRule) :
    ClAppPorts tbl id [] sr5hf₁ sr5ha sr5hf₂ sr5ha :=
  ⟨.inr (.inr
    ⟨fun h => by rw [sr5_hf₁_eps] at h; exact ETm.noConfusion h,
      fun h => by rw [sr5_ha_eps] at h; exact ETm.noConfusion h,
      fun h => by rw [sr5_hf₂_eps] at h; exact ETm.noConfusion h,
      fun h => by rw [sr5_ha_eps] at h; exact ETm.noConfusion h⟩)⟩

#print axioms sr5_appCl_sat
