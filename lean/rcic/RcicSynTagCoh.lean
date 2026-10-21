import rcic.RcicSynAppBvarPBit
import Lean

/-!
# Syntactic sortRow, S6 §6 / A7 — `W-COV-HETERO-PROOF-STATUS`: `TagCoh` as a
derived result target

`research/rcic/sortrow/S6_MIXED_TRANSPORT_STEPS.md` §6 (ChatGPT, S6 #7327):
two typings/views of the same displayed subject can ascribe different result
types, so a comparison layer needs a **proof-status** correspondence that `CL`
(erased conversion) does not supply.

- **§1 the target.** `displayEps σ ρ D := D.eps σ ρ` is one side's displayed
  erased image; `TagCoh σ₁ ρ₁ σ₂ ρ₂ D₁ D₂ := (displayEps σ₁ ρ₁ D₁ = .star ↔
  displayEps σ₂ ρ₂ D₂ = .star)` is the heterogeneous proof-status claim — same
  subject `e`, different envs/contexts/types/`σᵢ`/`ρᵢ` allowed. It is a `def`
  plus composition theorems, a derived result target; it is deliberately NOT a
  field of `Below`/`MixedAnswer` (§5's reflective guard refuses a `Below`
  field-count change).
- **§2 the λ row.** `eps_lam_star_iff` reduces a λ's star-status to its body's
  under the pushed binder disposition; `tagCoh_lam` composes domain bit
  alignment with the actual `TagCoh(hb₁, hb₂)`; `pbit_lam_reg` returns the
  proof bit to the whole λ's `imax` via `LevelHom.imax_bit`.
- **§3 the let row.** main's `letDisp`/`let_eps_eq`/`lsub_eps_eq` give the
  actual drop/inline disposition and its erasure equations; the `letE`/`lsub`
  compositions (`tagCoh_letE`, `tagCoh_lsub`) consume the bodies' `TagCoh`
  under each side's actual disposition, and `pbit_letE_reg` / `pbit_lsub_reg`
  keep the "real lsub regularity vs the original hTᵢ" bridge as an explicit
  premise.
- **§4 the app row.** `eps_app_star_iff` shows an application's star-status is
  exactly its function's; `tagCoh_app` composes `TagCoh(hf₁, hf₂)`; the `_row`
  bundles delegate the per-side result bit to the landed
  `pbit_app_reg_of_below_got`/`_readPi` with `hbit` kept explicit.
- **§5 controls/teeth.** The empty-table erased control `app (lam ★) (sort 0)
  → ★` holds under `ConvMod (EStep []) LvlEq` while its left side is not
  literally `★` — `CL` never yields star-status equality; `resolve_letDisp_zero`
  shows `drop`/`inline` dispositions resolve to the erased value itself (a
  value CL never equalizes them); `imax_bit_needs_levelHom` shows the λ row's
  `LevelHom` premise is load-bearing.

A7 stays `W-COV-HETERO-PROOF-STATUS` — the full-domain `TagCoh` producer and the
mixed-inline view correspondence remain OPEN (`closure_claim = 0`); what is
sealed here is the derived target, the per-row compositions, and the controls.
Premises NONE; axioms ⊆ [propext, Quot.sound].
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the derived result target -/

/-- One side's displayed erased image under its own pending `σ`/`ρ`. -/
abbrev displayEps (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) : ETm := D.eps σ ρ

/-- `TagCoh(D₁, D₂)` (S6 §6.1): proof-status agreement of two original
    typings/views of the same displayed subject `e`, allowing different
    ascribed types, envs, contexts, and different pending `σᵢ`/`ρᵢ`.

    A derived result target — produced by the composition theorems of this
    module and (eventually) by the recursive mixed producer; never a
    caller-filled field of an answer record. The full-domain supplier stays
    open under `W-COV-HETERO-PROOF-STATUS`. -/
def TagCoh {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx} {e T₁ : Expr Nat}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {T₂ : Expr Nat}
    (σ₁ : Level → Level) (ρ₁ : List Disp) (σ₂ : Level → Level) (ρ₂ : List Disp)
    (D₁ : TyP E₁ n₁ Γ₁ e T₁) (D₂ : TyP E₂ n₂ Γ₂ e T₂) : Prop :=
  displayEps σ₁ ρ₁ D₁ = .star ↔ displayEps σ₂ ρ₂ D₂ = .star

/-- A star-status iff on `D₁`/`D₂` is a genuine `TagCoh` once the second
    side's subject is identified with the first's by `hs`. This is how
    transport nodes whose subject is computed (e.g. `lsub`'s
    `instantiate j (lift 0 j v) e`) enter `TagCoh`. -/
theorem TagCoh.of_subject_eq {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {e₁ T₁ : Expr Nat} {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx}
    {e₂ T₂ : Expr Nat} {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (D₁ : TyP E₁ n₁ Γ₁ e₁ T₁) (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂) (hs : e₂ = e₁)
    (h : displayEps σ₁ ρ₁ D₁ = .star ↔ displayEps σ₂ ρ₂ D₂ = .star) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂ D₁ (hs ▸ D₂) := by
  subst hs
  exact h

/-! ## §2 the λ row -/

/-- The λ's star-status is exactly its body's under the pushed binder
    disposition `binderDisp (levelIsZero (σ u))`: `drop` when the domain is a
    proof sort, `keep` otherwise (`lam`'s erased body is wrapped in `ETm.lam`,
    which is never `★`). -/
theorem eps_lam_star_iff {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat}
    {u : Level} {body B : Expr Nat} {v : Level} {hA : TyP E n Γ A (.sort u)}
    {hbody : TyP E n (.assumption A :: Γ) body B}
    {hB : TyP E n (.assumption A :: Γ) B (.sort v)}
    {σ : Level → Level} {ρ : List Disp} :
    (TyP.lam E n Γ A u body B v hA hbody hB).eps σ ρ = .star ↔
      hbody.eps σ (binderDisp (levelIsZero (σ u)) :: ρ) = .star := by
  cases hb : levelIsZero (σ u) with
  | false =>
      rw [binderDisp_keep, eps_lam_keep_eq hA hbody hB ρ hb]
      cases hbody.eps σ (.keep :: ρ) <;>
        first
        | exact ⟨fun _ => rfl, fun _ => rfl⟩
        | exact ⟨fun h => ETm.noConfusion h, fun h => ETm.noConfusion h⟩
  | true =>
      rw [binderDisp_drop, eps_lam_drop hb]

/-- λ-row `TagCoh` (S6 §6.2): after domain bit alignment at the shared bit `b`,
    the actual `TagCoh(hb₁, hb₂)` under `binderDisp b` gives the two λs' proof
    status. Codomain typings `B₁ ≠ B₂` are allowed. -/
theorem tagCoh_lam {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx} {A body : Expr Nat}
    {u₁ v₁ : Level} {B₁ : Expr Nat} {hA₁ : TyP E₁ n₁ Γ₁ A (.sort u₁)}
    {hbody₁ : TyP E₁ n₁ (.assumption A :: Γ₁) body B₁}
    {hB₁ : TyP E₁ n₁ (.assumption A :: Γ₁) B₁ (.sort v₁)}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {u₂ v₂ : Level} {B₂ : Expr Nat}
    {hA₂ : TyP E₂ n₂ Γ₂ A (.sort u₂)}
    {hbody₂ : TyP E₂ n₂ (.assumption A :: Γ₂) body B₂}
    {hB₂ : TyP E₂ n₂ (.assumption A :: Γ₂) B₂ (.sort v₂)}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp} {b : Bool}
    (hb₁ : levelIsZero (σ₁ u₁) = b) (hb₂ : levelIsZero (σ₂ u₂) = b)
    (ht : TagCoh σ₁ (binderDisp b :: ρ₁) σ₂ (binderDisp b :: ρ₂)
      hbody₁ hbody₂) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂
      (TyP.lam E₁ n₁ Γ₁ A u₁ body B₁ v₁ hA₁ hbody₁ hB₁)
      (TyP.lam E₂ n₂ Γ₂ A u₂ body B₂ v₂ hA₂ hbody₂ hB₂) := by
  refine eps_lam_star_iff.trans (Iff.trans ?_ eps_lam_star_iff.symm)
  rw [hb₁, hb₂]
  exact ht

/-- λ result bit (S6 §6.2): the body's `PBit` at its own sort typing `hB`,
    pushed through the binder disposition, returns to the whole λ's regularity
    typing `TyP.pi` — `imax`'s bit equals the codomain bit by
    `LevelHom.imax_bit`. -/
theorem pbit_lam_reg {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat}
    {u : Level} {body B : Expr Nat} {v : Level} {hA : TyP E n Γ A (.sort u)}
    {hbody : TyP E n (.assumption A :: Γ) body B}
    {hB : TyP E n (.assumption A :: Γ) B (.sort v)}
    {σ : Level → Level} (hσ : LevelHom σ) {ρ : List Disp}
    (hpb : PBit σ (binderDisp (levelIsZero (σ u)) :: ρ) hbody hB) :
    PBit σ ρ (TyP.lam E n Γ A u body B v hA hbody hB)
      (TyP.pi E n Γ A u B v hA hB) :=
  eps_lam_star_iff.trans (hpb.trans (by rw [hσ.imax_bit u v]))

/-- The full λ row (S6 §6.2): domain bit alignment + the body's actual
    `TagCoh` under the pushed disposition + each side's body `PBit` at `hBᵢ`
    yield the λs' `TagCoh` and both whole-λ proof bits at their `TyP.pi`
    regularities (`Dᵢ.reg.2`). -/
theorem tagCoh_lam_row {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {A body : Expr Nat} {u₁ v₁ : Level} {B₁ : Expr Nat}
    {hA₁ : TyP E₁ n₁ Γ₁ A (.sort u₁)}
    {hbody₁ : TyP E₁ n₁ (.assumption A :: Γ₁) body B₁}
    {hB₁ : TyP E₁ n₁ (.assumption A :: Γ₁) B₁ (.sort v₁)}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {u₂ v₂ : Level} {B₂ : Expr Nat}
    {hA₂ : TyP E₂ n₂ Γ₂ A (.sort u₂)}
    {hbody₂ : TyP E₂ n₂ (.assumption A :: Γ₂) body B₂}
    {hB₂ : TyP E₂ n₂ (.assumption A :: Γ₂) B₂ (.sort v₂)}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp} {b : Bool}
    (hb₁ : levelIsZero (σ₁ u₁) = b) (hb₂ : levelIsZero (σ₂ u₂) = b)
    (ht : TagCoh σ₁ (binderDisp b :: ρ₁) σ₂ (binderDisp b :: ρ₂)
      hbody₁ hbody₂)
    (hσ₁ : LevelHom σ₁) (hσ₂ : LevelHom σ₂)
    (hpb₁ : PBit σ₁ (binderDisp b :: ρ₁) hbody₁ hB₁)
    (hpb₂ : PBit σ₂ (binderDisp b :: ρ₂) hbody₂ hB₂) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂
      (TyP.lam E₁ n₁ Γ₁ A u₁ body B₁ v₁ hA₁ hbody₁ hB₁)
      (TyP.lam E₂ n₂ Γ₂ A u₂ body B₂ v₂ hA₂ hbody₂ hB₂) ∧
      PBit σ₁ ρ₁ (TyP.lam E₁ n₁ Γ₁ A u₁ body B₁ v₁ hA₁ hbody₁ hB₁)
        (TyP.pi E₁ n₁ Γ₁ A u₁ B₁ v₁ hA₁ hB₁) ∧
      PBit σ₂ ρ₂ (TyP.lam E₂ n₂ Γ₂ A u₂ body B₂ v₂ hA₂ hbody₂ hB₂)
        (TyP.pi E₂ n₂ Γ₂ A u₂ B₂ v₂ hA₂ hB₂) := by
  refine ⟨tagCoh_lam hb₁ hb₂ ht, ?_, ?_⟩
  · rw [← hb₁] at hpb₁
    exact pbit_lam_reg hσ₁ hpb₁
  · rw [← hb₂] at hpb₂
    exact pbit_lam_reg hσ₂ hpb₂

/-! ## §3 the let row -/

/- The disposition a `letE`/`lsub` pushes is main's `letDisp`
   (`RcicSynTable`: `drop` on `★`, `inline ev` otherwise), and its erasure
   equations are the landed `let_eps_eq` / `lsub_eps_eq` — consumed, never
   re-stated. Two sides whose erased values differ keep different
   dispositions; a value `CL` never makes them equal. -/

/-- `letE`-row `TagCoh` (S6 §6.2): the bodies' `TagCoh` under the two sides'
    ACTUAL dispositions (`letDisp` of each value's own erasure — possibly
    `drop` on one side and `inline` on the other) gives the let's proof
    status. -/
theorem tagCoh_letE {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {A value body : Expr Nat} {B₁ : Expr Nat} {u₁ w₁ : Level}
    {hA₁ : TyP E₁ n₁ Γ₁ A (.sort u₁)} {hv₁ : TyP E₁ n₁ Γ₁ value A}
    {hb₁ : TyP E₁ n₁ (.letBinding A value :: Γ₁) body B₁}
    {hT₁ : TyP E₁ n₁ Γ₁ (instantiate0 value B₁) (.sort w₁)}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {B₂ : Expr Nat} {u₂ w₂ : Level}
    {hA₂ : TyP E₂ n₂ Γ₂ A (.sort u₂)} {hv₂ : TyP E₂ n₂ Γ₂ value A}
    {hb₂ : TyP E₂ n₂ (.letBinding A value :: Γ₂) body B₂}
    {hT₂ : TyP E₂ n₂ Γ₂ (instantiate0 value B₂) (.sort w₂)}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh σ₁ (letDisp (hv₁.eps σ₁ ρ₁) :: ρ₁)
      σ₂ (letDisp (hv₂.eps σ₂ ρ₂) :: ρ₂) hb₁ hb₂) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂
      (TyP.letE E₁ n₁ Γ₁ A u₁ value B₁ body w₁ hA₁ hv₁ hb₁ hT₁)
      (TyP.letE E₂ n₂ Γ₂ A u₂ value B₂ body w₂ hA₂ hv₂ hb₂ hT₂) := by
  unfold TagCoh displayEps
  rw [let_eps_eq, let_eps_eq]
  exact ht

/-- `lsub`-row `TagCoh` (S6 §6.2): same payment shape as `letE` at index `jᵢ`.
    The conclusion is stated as the raw star-status iff; when the two sides'
    displayed subjects coincide (`instantiate j₂ (lift 0 j₂ v₂) e₂ =
    instantiate j₁ (lift 0 j₁ v₁) e₁`), `TagCoh.of_subject_eq` re-presents it
    as `TagCoh`. -/
theorem tagCoh_lsub {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx} {e A₁ : Expr Nat}
    {t₁ v₁ : Expr Nat} {j₁ : Nat} {u₁ : Level} {D₁ : TyP E₁ n₁ Γ₁ e A₁}
    {hget₁ : Γ₁[j₁]? = some (.letBinding t₁ v₁)}
    {hv₁ : TyP E₁ n₁ (substRemove v₁ j₁ Γ₁) (lift 0 j₁ v₁) (lift 0 j₁ t₁)}
    {hvT₁ : TyP E₁ n₁ (substRemove v₁ j₁ Γ₁) (lift 0 j₁ t₁) (.sort u₁)}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {A₂ : Expr Nat}
    {t₂ v₂ : Expr Nat} {j₂ : Nat} {u₂ : Level} {D₂ : TyP E₂ n₂ Γ₂ e A₂}
    {hget₂ : Γ₂[j₂]? = some (.letBinding t₂ v₂)}
    {hv₂ : TyP E₂ n₂ (substRemove v₂ j₂ Γ₂) (lift 0 j₂ v₂) (lift 0 j₂ t₂)}
    {hvT₂ : TyP E₂ n₂ (substRemove v₂ j₂ Γ₂) (lift 0 j₂ t₂) (.sort u₂)}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh σ₁ (insertDisp (lsubDisp (countKeep (ρ₁.take j₁)) (hv₁.eps σ₁ ρ₁)) j₁ ρ₁)
      σ₂ (insertDisp (lsubDisp (countKeep (ρ₂.take j₂)) (hv₂.eps σ₂ ρ₂)) j₂ ρ₂) D₁ D₂) :
    (TyP.lsub E₁ n₁ Γ₁ e A₁ t₁ v₁ j₁ u₁ D₁ hget₁ hv₁ hvT₁).eps σ₁ ρ₁ = .star ↔
      (TyP.lsub E₂ n₂ Γ₂ e A₂ t₂ v₂ j₂ u₂ D₂ hget₂ hv₂ hvT₂).eps σ₂ ρ₂ = .star := by
  rw [lsub_eps_eq, lsub_eps_eq]
  exact ht

/-- `letE` result bit (S6 §6.2): the body's `PBit` at its own regularity
    `hb.reg.2` under the actual disposition, plus the real lsub regularity —
    the level bit of `hb.reg.1` against the node's own `hT`'s sort `w`,
    kept as an explicit premise — returns `PBit` on the whole `letE`. -/
theorem pbit_letE_reg {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat}
    {u : Level} {value B body : Expr Nat} {w : Level}
    {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    {hT : TyP E n Γ (instantiate0 value B) (.sort w)}
    {σ : Level → Level} {ρ : List Disp}
    (hpb : PBit σ (letDisp (hv.eps σ ρ) :: ρ) hb hb.reg.2)
    (hbit : levelIsZero (σ hb.reg.1) = levelIsZero (σ w)) :
    PBit σ ρ (TyP.letE E n Γ A u value B body w hA hv hb hT) hT := by
  refine Iff.trans ?_ (hpb.trans ?_)
  · rw [let_eps_eq]
  · rw [hbit]

/-- `lsub` result bit: the body's `PBit` at `D.reg.2` under the actual
    inserted disposition returns `PBit` on the whole `lsub` at its own
    regularity typing — `TyP.reg` sends the `lsub` node to a `lsub` of
    `D.reg.2`, whose sort is `D.reg.1`. -/
theorem pbit_lsub_reg {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat}
    {j : Nat} {u : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {σ : Level → Level} {ρ : List Disp}
    (hpb : PBit σ (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.eps σ ρ)) j ρ) D D.reg.2) :
    PBit σ ρ (TyP.lsub E n Γ e A t v j u D hget hv hvT)
      (TyP.lsub E n Γ A (.sort D.reg.1) t v j u D.reg.2 hget hv hvT) := by
  refine Iff.trans ?_ hpb
  rw [lsub_eps_eq]

/-- `lsub` result bit against an external sort typing `hT` of the same result
    type: the real lsub regularity vs `hT`'s sort `s` stays an explicit level
    premise. -/
theorem pbit_lsub_of_hT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat}
    {j : Nat} {u w : Level} {D : TyP E n Γ e A}
    {hget : Γ[j]? = some (.letBinding t v)}
    {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
    {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
    {hT : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) A) (.sort w)}
    {σ : Level → Level} {ρ : List Disp}
    (hpb : PBit σ (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.eps σ ρ)) j ρ) D D.reg.2)
    (hbit : levelIsZero (σ D.reg.1) = levelIsZero (σ w)) :
    PBit σ ρ (TyP.lsub E n Γ e A t v j u D hget hv hvT) hT := by
  refine Iff.trans ?_ (hpb.trans ?_)
  · rw [lsub_eps_eq]
  · rw [hbit]

/-! ## §4 the app row -/

/-- An application's star-status is exactly its function's: when `hf.eps`
    erases to `★` the whole app is `★`; otherwise the erased image is `ef` or
    `.app ef ea`, never `★`. -/
theorem eps_app_star_iff {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a A B : Expr Nat} {w : Level} {hf : TyP E n Γ f (.pi A B)}
    {ha : TyP E n Γ a A}
    {hT : TyP E n Γ (instantiate0 a B) (.sort w)}
    {σ : Level → Level} {ρ : List Disp} :
    (TyP.app E n Γ f a A B w hf ha hT).eps σ ρ = .star ↔
      hf.eps σ ρ = .star := by
  simp only [TyP.eps]
  generalize hf.eps σ ρ = ef
  generalize ha.eps σ ρ = ea
  cases ef <;> cases ea <;> simp

/-- app-row `TagCoh` (S6 §6.2): `TagCoh(hf₁, hf₂)` — the function's
    proof-status correspondence — is the whole application's. Different
    `B₁[a]`/`B₂[a]` result types are allowed. -/
theorem tagCoh_app {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {f a A₁ B₁ : Expr Nat} {w₁ : Level} {hf₁ : TyP E₁ n₁ Γ₁ f (.pi A₁ B₁)}
    {ha₁ : TyP E₁ n₁ Γ₁ a A₁}
    {hT₁ : TyP E₁ n₁ Γ₁ (instantiate0 a B₁) (.sort w₁)}
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {A₂ B₂ : Expr Nat} {w₂ : Level}
    {hf₂ : TyP E₂ n₂ Γ₂ f (.pi A₂ B₂)} {ha₂ : TyP E₂ n₂ Γ₂ a A₂}
    {hT₂ : TyP E₂ n₂ Γ₂ (instantiate0 a B₂) (.sort w₂)}
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh σ₁ ρ₁ σ₂ ρ₂ hf₁ hf₂) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂
      (TyP.app E₁ n₁ Γ₁ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E₂ n₂ Γ₂ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) :=
  eps_app_star_iff.trans (ht.trans eps_app_star_iff.symm)

/-- The full app row at the `_got` supplier (S6 §6.2): `TagCoh(hf₁, hf₂)` plus,
    per side, the bounded `PiGot`, `LevelHom`, `DispFor`, the `Below` seed, and
    the EXPLICIT `hbit` remainder
    `levelIsZero (σᵢ hfᵢ.reg.1) = levelIsZero (σᵢ (.imax gᵢ.u gᵢ.v))` —
    delegated to the landed `pbit_app_reg_of_below_got`. -/
theorem tagCoh_app_row_got
    {Aw₁ Aw₂ : Nat → Nat} {tbl₁ tbl₂ : List CRule}
    {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {f a A₁ B₁ : Expr Nat} {w₁ s₁ : Level}
    {hf₁ : TyP E₁ n₁ Γ₁ f (.pi A₁ B₁)} {ha₁ : TyP E₁ n₁ Γ₁ a A₁}
    {hT₁ : TyP E₁ n₁ Γ₁ (instantiate0 a B₁) (.sort w₁)}
    (g₁ : PiGot Aw₁ ((TyP.app E₁ n₁ Γ₁ f a A₁ B₁ w₁ hf₁ ha₁ hT₁).wt Aw₁)
      E₁ n₁ Γ₁ A₁ B₁)
    (DT₁ : TyP E₁ n₁ Γ₁ (instantiate0 a B₁) (.sort s₁))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {A₂ B₂ : Expr Nat} {w₂ s₂ : Level}
    {hf₂ : TyP E₂ n₂ Γ₂ f (.pi A₂ B₂)} {ha₂ : TyP E₂ n₂ Γ₂ a A₂}
    {hT₂ : TyP E₂ n₂ Γ₂ (instantiate0 a B₂) (.sort w₂)}
    (g₂ : PiGot Aw₂ ((TyP.app E₂ n₂ Γ₂ f a A₂ B₂ w₂ hf₂ ha₂ hT₂).wt Aw₂)
      E₂ n₂ Γ₂ A₂ B₂)
    (DT₂ : TyP E₂ n₂ Γ₂ (instantiate0 a B₂) (.sort s₂))
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh σ₁ ρ₁ σ₂ ρ₂ hf₁ hf₂)
    (hσ₁ : LevelHom σ₁) (hρ₁ : DispFor σ₁ E₁ n₁ Γ₁ ρ₁)
    (hbit₁ : levelIsZero (σ₁ hf₁.reg.1) = levelIsZero (σ₁ (.imax g₁.u g₁.v)))
    (Bel₁ : Below Aw₁ tbl₁
      (tyPairMeas Aw₁ (TyP.app E₁ n₁ Γ₁ f a A₁ B₁ w₁ hf₁ ha₁ hT₁) DT₁))
    (hσ₂ : LevelHom σ₂) (hρ₂ : DispFor σ₂ E₂ n₂ Γ₂ ρ₂)
    (hbit₂ : levelIsZero (σ₂ hf₂.reg.1) = levelIsZero (σ₂ (.imax g₂.u g₂.v)))
    (Bel₂ : Below Aw₂ tbl₂
      (tyPairMeas Aw₂ (TyP.app E₂ n₂ Γ₂ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) DT₂)) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂
      (TyP.app E₁ n₁ Γ₁ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E₂ n₂ Γ₂ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) ∧
      PBit σ₁ ρ₁ (TyP.app E₁ n₁ Γ₁ f a A₁ B₁ w₁ hf₁ ha₁ hT₁) hT₁ ∧
      PBit σ₂ ρ₂ (TyP.app E₂ n₂ Γ₂ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) hT₂ :=
  ⟨tagCoh_app ht,
    pbit_app_reg_of_below_got Aw₁ tbl₁ hf₁ ha₁ hT₁ g₁ DT₁ hσ₁ ρ₁ hρ₁ hbit₁ Bel₁,
    pbit_app_reg_of_below_got Aw₂ tbl₂ hf₂ ha₂ hT₂ g₂ DT₂ hσ₂ ρ₂ hρ₂ hbit₂ Bel₂⟩

/-- The full app row at the `_readPi` supplier (S6 §6.2): each side's
    `isSortOrPiHead`-true `hfᵢ.reg.2` plus a successful actual `readPi`
    supplies the `hbit` automatically; other branches stay open. Delegated to
    the landed `pbit_app_reg_of_below_readPi`. -/
theorem tagCoh_app_row_readPi
    {Aw₁ Aw₂ : Nat → Nat} {tbl₁ tbl₂ : List CRule}
    {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx}
    {f a A₁ B₁ : Expr Nat} {w₁ s₁ : Level}
    {hf₁ : TyP E₁ n₁ Γ₁ f (.pi A₁ B₁)} {ha₁ : TyP E₁ n₁ Γ₁ a A₁}
    {hT₁ : TyP E₁ n₁ Γ₁ (instantiate0 a B₁) (.sort w₁)}
    (DT₁ : TyP E₁ n₁ Γ₁ (instantiate0 a B₁) (.sort s₁))
    (hsp₁ : hf₁.reg.2.isSortOrPiHead = true)
    {g₁ : PiGot Aw₁ ((TyP.app E₁ n₁ Γ₁ f a A₁ B₁ w₁ hf₁ ha₁ hT₁).wt Aw₁)
      E₁ n₁ Γ₁ A₁ B₁}
    (hr₁ : readPi (envExt_refl E₁) Aw₁
      ((TyP.app E₁ n₁ Γ₁ f a A₁ B₁ w₁ hf₁ ha₁ hT₁).wt Aw₁)
      hf₁.reg.2 rfl (app_fun_reg_atom_src Aw₁ hf₁ ha₁ hT₁) = .yes g₁)
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {A₂ B₂ : Expr Nat} {w₂ s₂ : Level}
    {hf₂ : TyP E₂ n₂ Γ₂ f (.pi A₂ B₂)} {ha₂ : TyP E₂ n₂ Γ₂ a A₂}
    {hT₂ : TyP E₂ n₂ Γ₂ (instantiate0 a B₂) (.sort w₂)}
    (DT₂ : TyP E₂ n₂ Γ₂ (instantiate0 a B₂) (.sort s₂))
    (hsp₂ : hf₂.reg.2.isSortOrPiHead = true)
    {g₂ : PiGot Aw₂ ((TyP.app E₂ n₂ Γ₂ f a A₂ B₂ w₂ hf₂ ha₂ hT₂).wt Aw₂)
      E₂ n₂ Γ₂ A₂ B₂}
    (hr₂ : readPi (envExt_refl E₂) Aw₂
      ((TyP.app E₂ n₂ Γ₂ f a A₂ B₂ w₂ hf₂ ha₂ hT₂).wt Aw₂)
      hf₂.reg.2 rfl (app_fun_reg_atom_src Aw₂ hf₂ ha₂ hT₂) = .yes g₂)
    {σ₁ σ₂ : Level → Level} {ρ₁ ρ₂ : List Disp}
    (ht : TagCoh σ₁ ρ₁ σ₂ ρ₂ hf₁ hf₂)
    (hσ₁ : LevelHom σ₁) (hρ₁ : DispFor σ₁ E₁ n₁ Γ₁ ρ₁)
    (Bel₁ : Below Aw₁ tbl₁
      (tyPairMeas Aw₁ (TyP.app E₁ n₁ Γ₁ f a A₁ B₁ w₁ hf₁ ha₁ hT₁) DT₁))
    (hσ₂ : LevelHom σ₂) (hρ₂ : DispFor σ₂ E₂ n₂ Γ₂ ρ₂)
    (Bel₂ : Below Aw₂ tbl₂
      (tyPairMeas Aw₂ (TyP.app E₂ n₂ Γ₂ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) DT₂)) :
    TagCoh σ₁ ρ₁ σ₂ ρ₂
      (TyP.app E₁ n₁ Γ₁ f a A₁ B₁ w₁ hf₁ ha₁ hT₁)
      (TyP.app E₂ n₂ Γ₂ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) ∧
      PBit σ₁ ρ₁ (TyP.app E₁ n₁ Γ₁ f a A₁ B₁ w₁ hf₁ ha₁ hT₁) hT₁ ∧
      PBit σ₂ ρ₂ (TyP.app E₂ n₂ Γ₂ f a A₂ B₂ w₂ hf₂ ha₂ hT₂) hT₂ :=
  ⟨tagCoh_app ht,
    pbit_app_reg_of_below_readPi Aw₁ tbl₁ hf₁ ha₁ hT₁ DT₁ hsp₁ hr₁ hσ₁ ρ₁ hρ₁ Bel₁,
    pbit_app_reg_of_below_readPi Aw₂ tbl₂ hf₂ ha₂ hT₂ DT₂ hsp₂ hr₂ hσ₂ ρ₂ hρ₂ Bel₂⟩

/-! ## §5 controls and teeth -/

/-- The erased control (S6 §6): with an EMPTY rule table, pure erased β sends
    `app (lam ★) (sort 0)` to `★`, so `ConvMod (EStep []) LvlEq` relates a
    non-`★` term to `★`. `CL` therefore never yields the star-status equation
    `TagCoh` claims — the counterexample stays at the erased relation, per
    spec it does not claim both ends are current legal typed erasures. -/
theorem erased_beta_conv_not_star_status :
    ConvMod (EStep []) LvlEq (.app (.lam .star) (.sort .zero)) .star
      ∧ ¬((.app (.lam .star) (.sort .zero) : ETm) = .star) :=
  ⟨.fwd (.inl (RStep.beta .star (.sort .zero))), fun h => ETm.noConfusion h⟩

/-- `resolve` under the actual let disposition returns the erased value
    itself at slot 0: the `drop`/`inline` choice is fully determined by
    `hv.eps`; a value `CL` never makes the two dispositions resolve alike
    (S6 §6.2, let row). -/
theorem resolve_letDisp_zero (ev : ETm) (ρ : List Disp) :
    resolve (letDisp ev :: ρ) 0 = ev := by
  cases ev <;> rfl

/-- The mixed disposition case is genuinely different: `drop` resolves slot 0
    to `★`, `inline v` to `v` — distinct whenever `v ≠ ★`. -/
theorem resolve_drop_ne_inline (v : ETm) (ρ : List Disp) (hv : v ≠ .star) :
    resolve (.drop :: ρ) 0 ≠ resolve (.inline v :: ρ) 0 :=
  fun h => hv h.symm

/-- A non-`LevelHom` σ for the tooth below: it maps every `.imax` to
    `.succ .zero` regardless of its codomain. -/
def imaxToSucc : Level → Level
  | .imax _ _ => .succ .zero
  | _ => .zero

/-- `imax`'s bit law is a `LevelHom` law, not a lemma about `levelIsZero`
    alone: under `imaxToSucc`,
    `levelIsZero (σ (.imax .zero .zero)) = false` while the codomain bit is
    `levelIsZero (σ .zero) = true`. The `hσ : LevelHom σ` premise of
    `pbit_lam_reg` is load-bearing. -/
theorem imax_bit_needs_levelHom :
    levelIsZero (imaxToSucc (.imax .zero .zero)) ≠
      levelIsZero (imaxToSucc .zero) := by
  decide

/-! A7 guard (S6 §6.1): `Below` keeps its six original fields
    (`es`/`cl`/`eut`/`cts`/`pb`/`bitCoh`) — `TagCoh` is a derived result
    target, never a caller-filled field. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  match env.find? `Rcic.Syn.Below.mk with
  | some (.ctorInfo info) =>
    unless info.numFields = 6 do
      throwError "[rcic_tagcoh] Below.mk carries {info.numFields} fields, \
        expected 6 — TagCoh is derived, never a caller-filled field"
    logInfo "[rcic_tagcoh] Below keeps its 6 original fields; TagCoh is a derived target"
  | _ => throwError "[rcic_tagcoh] Below.mk not found"

#print axioms Rcic.Syn.tagCoh_lam
#print axioms Rcic.Syn.pbit_lam_reg
#print axioms Rcic.Syn.tagCoh_lam_row
#print axioms Rcic.Syn.tagCoh_letE
#print axioms Rcic.Syn.tagCoh_lsub
#print axioms Rcic.Syn.pbit_letE_reg
#print axioms Rcic.Syn.pbit_lsub_reg
#print axioms Rcic.Syn.pbit_lsub_of_hT
#print axioms Rcic.Syn.tagCoh_app
#print axioms Rcic.Syn.tagCoh_app_row_got
#print axioms Rcic.Syn.tagCoh_app_row_readPi
#print axioms Rcic.Syn.erased_beta_conv_not_star_status

end Rcic.Syn
