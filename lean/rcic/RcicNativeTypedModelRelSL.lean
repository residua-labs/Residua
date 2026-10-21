import rcic.RcicNativeTypedModelRelS

/-!
# RcicNativeTypedModelRelSL — the spine clause with level facts recorded (`…SL` variants)

The landed `RcicNativeTypedModelRelS.SpineClauseS` records the spine's levels only up to
`eqNList`.  The item-2.1 ruling (Klaus/cc) calls for the level facts to be recorded at
construction time as well — `ls₁.length = m.arity`, `levelsBounded n ls₁ = true`,
`levelsBounded n ls₂ = true` — because they come from the derivation's `HasTyT.const`
(`hlen`/`hwf`) or `native_level_facts`, and the landed clause erases them.  A landed
definition is never edited (#7726 batch-218 refusal; cc 11:20Z correction), so the
strengthened clause and its generalised family premises live HERE under new names:

* `SpineClauseSL` — the landed clause plus the three level conjuncts (`ls₂.length = m.arity`
  follows by `eqNList_length`);
* `ConvArgsSymmSL`/`ConvArgsTransSL` — symmetry and
  transitivity of `ConvArgsT` along a member's declared type under a level change, with the
  clause's level facts as premises (no typing or saturation hypotheses);
* the clause algebra re-proved at `SpineClauseSL`: `spineClauseSL_idx`,
  `spineClauseSL_symm` (`ConvArgsSymmSL`), `spineClauseSL_trans` (`ConvArgsTransSL`);
* `spineClauseS_of_spineClauseSL` — the bridge to the landed clause (drop the level
  conjuncts), so every landed consumer composes with `SL`-shaped supplies.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §1 — the strengthened clause and the generalised family premises -/

/-- **The unified spine clause with level facts recorded** at head `r` with argument compacts
    `args`: the landed `SpineClauseS` plus `ls₁.length = m.arity`, `levelsBounded n ls₁ = true`
    and `levelsBounded n ls₂ = true` (the item-2.1 ruling; `ls₂.length = m.arity` follows by
    `eqNList_length`). -/
def SpineClauseSL (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) (r : Nat)
    (args : List CptT) : Prop :=
  ∃ (m : CheckedMember) (ls₁ ls₂ : List Level) (xs₁ xs₂ : List (Expr Nat)),
    E.members r = some m ∧
    RedR R Γ M (foldApps (.const r ls₁) xs₁) ∧ RedR R Γ M' (foldApps (.const r ls₂) xs₂) ∧
    NormalR R Γ (foldApps (.const r ls₁) xs₁) ∧ NormalR R Γ (foldApps (.const r ls₂) xs₂) ∧
    eqNList ls₁ ls₂ ∧ ls₁.length = m.arity ∧
    levelsBounded n ls₁ = true ∧ levelsBounded n ls₂ = true ∧
    args.length ≤ xs₁.length ∧ args.length ≤ xs₂.length ∧
    ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs₁ xs₂ ∧
    ((∃ l, RedR R Γ A (.sort l)) → m.mclass = .inductiveM →
      xs₁.length = (piDomsOf m.mtype).length ∧ xs₂.length = (piDomsOf m.mtype).length ∧
        (∃ w, Nonempty (HasTyT E n Γ (foldApps (.const r ls₁) xs₁) (.sort w))) ∧
        (∃ w', Nonempty (HasTyT E n Γ (foldApps (.const r ls₂) xs₂) (.sort w'))))

/-- Generalised family premises, level-fact form: symmetry of `ConvArgsT` along a member's
    declared type under a level change, with the clause's level facts as premises (no typing or
    saturation hypotheses). -/
def ConvArgsSymmSL (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}, E.members r = some m →
    ∀ {ls ls' : List Level} {xs xs' : List (Expr Nat)}, ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' →
    ConvArgsT E n Γ (instantiateLevels ls' m.mtype) xs' xs

/-- Generalised family premises, level-fact form: transitivity of `ConvArgsT` along a member's
    declared type under a level change, with the clause's level facts as premises. -/
def ConvArgsTransSL (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}, E.members r = some m →
    ∀ {ls ls' ls'' : List Level} {xs xs' xs'' : List (Expr Nat)}, ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → levelsBounded n ls'' = true →
    eqNList ls ls' → eqNList ls' ls'' →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' →
    ConvArgsT E n Γ (instantiateLevels ls' m.mtype) xs' xs'' →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs''

/-- The bridge to the landed clause: drop the level conjuncts. -/
theorem spineClauseS_of_spineClauseSL {Γ : LCtx} {M M' A : Expr Nat} {r : Nat} {args : List CptT}
    (h : SpineClauseSL R E n Γ M M' A r args) : SpineClauseS R E n Γ M M' A r args := by
  obtain ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, hn₁, hn₂, heq, _, _, _, hl₁, hl₂, hca, hty⟩ := h
  exact ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, hn₁, hn₂, heq, hl₁, hl₂, hca, hty⟩

/-! ### §2 — the clause algebra at `SpineClauseSL` -/

/-- The clause depends on the index only through "reads back to a sort". -/
theorem spineClauseSL_idx {Γ : LCtx} {M M' A A' : Expr Nat} {r : Nat} {args : List CptT}
    (h₁ : (∃ l, RedR R Γ A (.sort l)) → ∃ l, RedR R Γ A' (.sort l))
    (h₂ : (∃ l, RedR R Γ A' (.sort l)) → ∃ l, RedR R Γ A (.sort l))
    (h : SpineClauseSL R E n Γ M M' A r args) : SpineClauseSL R E n Γ M M' A' r args := by
  obtain ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, hn₁, hn₂, heq, hlen, hwf₁, hwf₂, hl₁, hl₂, hca, hty⟩ := h
  exact ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, hn₁, hn₂, heq, hlen, hwf₁, hwf₂, hl₁, hl₂, hca,
    fun hs => hty (h₂ hs)⟩

/-- Symmetry of the clause (`ConvArgsSymmSL`). -/
theorem spineClauseSL_symm (hCAs : ConvArgsSymmSL E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' A A' : Expr Nat} {r : Nat} {args : List CptT}
    (hidx : (∃ l, RedR R Γ A' (.sort l)) → ∃ l, RedR R Γ A (.sort l))
    (h : SpineClauseSL R E n Γ M M' A r args) : SpineClauseSL R E n Γ M' M A' r args := by
  obtain ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, hn₁, hn₂, heq, hlen, hwf₁, hwf₂, hl₁, hl₂, hca, hty⟩ := h
  have hlen' : ls₂.length = m.arity := (eqNList_length ls₁ ls₂ heq).symm.trans hlen
  have hca' : ConvArgsT E n Γ (instantiateLevels ls₂ m.mtype) xs₂ xs₁ :=
    hCAs hΓ hm hlen hwf₁ hwf₂ heq hca
  refine ⟨m, ls₂, ls₁, xs₂, xs₁, hm, h2, h1, hn₂, hn₁, eqNList_symm'' heq, hlen', hwf₂, hwf₁,
    hl₂, hl₁, hca', fun hs hind => ?_⟩
  obtain ⟨e₁, e₂, hw, hw'⟩ := hty (hidx hs) hind
  exact ⟨e₂, e₁, hw', hw⟩

/-- Transitivity of the clause: the middle term's two normal spines coincide. -/
theorem spineClauseSL_trans (hNU : NormalUniqueR R) (hCAt : ConvArgsTransSL E n) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {M M' M'' A : Expr Nat} {r : Nat} {args : List CptT}
    (h₁ : SpineClauseSL R E n Γ M M' A r args) (h₂ : SpineClauseSL R E n Γ M' M'' A r args) :
    SpineClauseSL R E n Γ M M'' A r args := by
  obtain ⟨m, ls₁, ls₂, xs₁, xs₂, hm, h1, h2, hn₁, hn₂, heq, hlen, hwf₁, hwf₂, hl₁, hl₂, hca, hty⟩ := h₁
  obtain ⟨m', ls₂', ls₃, xs₂', xs₃, hm', h2', h3, hn₂', hn₃, heq', _, hwf₂', hwf₃, _, hl₃, hca', hty'⟩ := h₂
  rw [hm] at hm'
  injection hm' with hm'
  subst hm'
  have e := hNU Γ h2 hn₂ h2' hn₂'
  obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
  injection hconst with _ hls
  subst hls; subst hxs
  have hca'' : ConvArgsT E n Γ (instantiateLevels ls₁ m.mtype) xs₁ xs₃ :=
    hCAt hΓ hm hlen hwf₁ hwf₂' hwf₃ heq heq' hca hca'
  refine ⟨m, ls₁, ls₃, xs₁, xs₃, hm, h1, h3, hn₁, hn₃, eqNList_trans'' heq heq', hlen, hwf₁, hwf₃,
    hl₁, hl₃, hca'', fun hs hind => ?_⟩
  obtain ⟨e₁, _, hw, _⟩ := hty hs hind
  obtain ⟨_, e₃, _, hw''⟩ := hty' hs hind
  exact ⟨e₁, e₃, hw, hw''⟩

-- BEGIN GLM RELSL SEAL (axiom queries; every public declaration)
#print axioms SpineClauseSL
#print axioms ConvArgsSymmSL
#print axioms ConvArgsTransSL
#print axioms spineClauseS_of_spineClauseSL
#print axioms spineClauseSL_idx
#print axioms spineClauseSL_symm
#print axioms spineClauseSL_trans
-- END GLM RELSL SEAL

end Rcic.Declarative.NativeValleys.TypedModelAudit
