import rcic.RcicSynAppBvarPBit
import rcic.RcicSynPBitAll

/-!
# Syntactic sortRow, S16 §2.5 — the bvar final composition

`research/rcic/sortrow/S16_BVAR_CCTX_IOTA_STEPS.md` §2.5 (ChatGPT, S16 #7384).
The `TyP.bvar` `step` case's last consumer is a finite composition over three
already-supplied answers:

- `hresolve : resolve ρ i = .star ↔ b = true` — the slot's resolve status at
  the plan's `entryBit` (A6's `ResolvedEntry`, proven from `DispForC` or the
  real route's algebra, never manufactured here);
- `halign : b = levelIsZero (σ u)` — the entry's bit equals the target
  sort's bit (A6's `AlignedEntry` second layer);
- `hBit : BitCoh σ hA DT` — the regularity typing `hA` of the bvar rule and
  the requested typing `DT` agree on the proof bit (the strict `qBit`
  request, §2.1).

The composition pays nothing itself: the `levelIsZero (σ u) = true` branch is
`pbit_bvar_proof_reg` (zero hypotheses on `ρ`); the false branch rewrites the
bvar's `eps` by `eps_bvar_rel` and consumes `hresolve` under `halign`. The
outer `pbit_of_reg_and_bitCoh` repays `hA` to `DT` through `hBit`.

CONTROL (`pin_bvar_compose_consumes_not_supplies_align`): the composition
takes `halign` as a hypothesis — a resolved-but-misaligned slot exists, so no
instance of this theorem ever produces the alignment answer. The entry
alignment is an independent A6 demand, exactly as §2.5 states.

`closure_claim = 0`. Implementation lane `devin/ah816`; design credit
ChatGPT (S16 #7384).
-/

open Rcic.Declarative

namespace Rcic.Syn

/-- S16 §2.5 final composition, exactly as specified: `hresolve`, `halign`,
    `hBit` in; `PBit` of the `TyP.bvar` rule against `DT` out. -/
theorem pbit_bvar_from_resolve_align_bitCoh
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    {u s : Level} {σ : Level → Level} {ρ : List Disp}
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (DT : TyP E n Γ A (.sort s))
    (b : Bool)
    (hresolve : resolve ρ i = .star ↔ b = true)
    (halign : b = levelIsZero (σ u))
    (hBit : BitCoh σ hA DT) :
    PBit σ ρ (TyP.bvar E n Γ i A u hlook hA) DT := by
  have hReg : PBit σ ρ (TyP.bvar E n Γ i A u hlook hA) hA := by
    cases hz : levelIsZero (σ u) with
    | true => exact pbit_bvar_proof_reg σ ρ hlook hA hz
    | false =>
        unfold PBit
        rw [eps_bvar_rel hz]
        simpa only [halign] using hresolve
  exact pbit_of_reg_and_bitCoh _ DT hReg hBit

/-- CONTROL: `halign` is consumed, never supplied. `ρ := [.drop]` resolves
    index 0 to `.star` while `levelIsZero (id (.succ .zero)) = false`, so the
    `hresolve`-and-`hBit` side alone is satisfiable with `b = true` and yet
    `b = levelIsZero (σ u)` fails — the alignment duty is a separate payment
    (§2.5's last sentence). -/
theorem pin_bvar_compose_consumes_not_supplies_align :
    ∃ (σ : Level → Level) (ρ : List Disp) (i : Nat) (u : Level) (b : Bool),
      (resolve ρ i = .star ↔ b = true) ∧ b = true ∧
        ¬ (b = levelIsZero (σ u)) :=
  ⟨id, [.drop], 0, .succ .zero, true,
   ⟨fun _ => rfl, fun _ => rfl⟩, rfl, fun h => Bool.noConfusion h⟩

end Rcic.Syn

#print axioms Rcic.Syn.pbit_bvar_from_resolve_align_bitCoh
#print axioms Rcic.Syn.pin_bvar_compose_consumes_not_supplies_align
