import rcic.RcicIrrPostponeRefuted

/-!
# `pinLoopC2` — adversarial check C2 as a TYPED conversion fixture

Ruling check C2 (semantic-rows record on #6293, 00:50Z): at the closed
Loop environment `E₀ = eraseEnv pinLoopEnvA`, the closed recursor
partial `F = rec.{1} M̂ m̂` is convertible in `ConvT` to the η-lifted
self-arrow `λ t : Loop. (F t → F t)`. The erased witness pair does NOT
join under raw reduction — `F` is `const`-headed neutral (`|F| = F`, no
major fires) while the endpoint is `lam`-headed — which is exactly why
the rows moved to the semantic route: this file pins the *typed*
conversion as the fixture every r1b / domain model must validate.

Construction (`ConvT.trans` over the empty context):

* `ConvT.symm (ConvT.eta F)` — η reversed: `F ≡ λt. F t` at `F`'s type
  `Π (t : Loop). M̂ t`. `ConvT.eta`'s `lift 0 1 F` contracts to `F`
  because `F` is closed.
* `ConvT.lam` — λ-congruence lifting `pinLoopConv_erased`'s cyclic body
  conversion `F t ≡ F t → F t` under the `t : Loop` binder. The
  `lam`-index lands at `Π (t:Loop). sort 0`; `ConvT.tyConv` re-indexes to
  `Π (t:Loop). M̂ t` through the `pi`-congruence on the reversed motive
  β (`sort 0 ≡ M̂ t` under the binder).

The pin is `Nonempty`-stated: `ConvT` is `Type`-valued and the erasure
bridges `hasTyT_of_hasTyA`/`convT_of_convA` land in `Nonempty`; `obtain`
elimination into the `Prop` goal keeps the proof `Classical.choice`-free.
This is a fixture, not closure — `closure_claim` stays 0.
-/

namespace Rcic.Declarative

/-- `F` — the erased Loop recursor partial `rec.{1} M̂ m̂`. -/
private def loopC2F : Expr Nat := Ann.erase Ann.pinLoopF

/-- the erased Loop type `Loop` (the family constant `const 60`). -/
private def loopC2T : Expr Nat := .const 60 []

/-- the erased motive `M̂ = λ _ : Loop. Prop` applied at the bound `t`:
    `F`'s codomain under the `pi`. -/
private def loopC2Mt : Expr Nat := .app (Ann.erase Ann.pinLoopM) (.bvar 0)

/-- C2 (TYPED side): `F ≡ λ t : Loop. (F t → F t)` at
    `Π (t : Loop). M̂ t` — closed environment `eraseEnv pinLoopEnvA`,
    empty context, `ConvT`-level.

    Steps: reversed η gives `F ≡ λt. F t`; `lam`-congruence transports
    `pinLoopConv_erased` (the cyclic `F t ≡ F t → F t` conversion whose
    erased sides fail to join — the `ι★K` content) under the binder;
    `tyConv` moves the index `Π t:Loop. sort 0 → Π t:Loop. M̂ t` through
    the `pi`-congruence on the reversed motive β. -/
theorem pinLoopC2_conv {n : Nat} : Nonempty
    (ConvT (Ann.eraseEnv Ann.pinLoopEnvA) n []
      loopC2F (.lam loopC2T (Ann.erase Ann.pinLoopArrow))
      (Ann.erase Ann.pinLoopMajorM)) := by
  -- `F : Π (t : Loop). M̂ t` — the Ann-side recursor typing, erased.
  obtain ⟨hF⟩ := Ann.hasTyT_of_hasTyA Ann.pinLoop_wf
    Ann.pinLoopEnvA_iotaErases
    (Ann.pinLoopFTy (E := Ann.pinLoopEnvA)
      (I := Ann.iotaIfaceA Ann.pinLoopEnvA) (n := n) (Γ := []) rfl rfl rfl)
  -- `Loop : sort 0` at the empty context (the `refl`/`lam` domain legs).
  obtain ⟨hL⟩ := Ann.hasTyT_of_hasTyA Ann.pinLoop_wf
    Ann.pinLoopEnvA_iotaErases
    (Ann.pinLoopConstTy (E := Ann.pinLoopEnvA)
      (I := Ann.iotaIfaceA Ann.pinLoopEnvA) (n := n) (Γ := []) rfl)
  -- `Loop : sort 0` at `[t : Loop]` (the motive-β `hA` leg).
  obtain ⟨hLc⟩ := Ann.hasTyT_of_hasTyA Ann.pinLoop_wf
    Ann.pinLoopEnvA_iotaErases
    (Ann.pinLoopConstTy (E := Ann.pinLoopEnvA)
      (I := Ann.iotaIfaceA Ann.pinLoopEnvA) (n := n)
      (Γ := [.assumption (.const 60 [])]) rfl)
  -- `t : Loop` at `[t : Loop]` (the motive-β `harg` leg).
  obtain ⟨ht⟩ := Ann.hasTyT_of_hasTyA Ann.pinLoop_wf
    Ann.pinLoopEnvA_iotaErases
    (Ann.pinLoopVarTy (E := Ann.pinLoopEnvA)
      (I := Ann.iotaIfaceA Ann.pinLoopEnvA) (n := n)
      (Γ := [.assumption (.const 60 [])]) rfl 0 rfl)
  -- the cyclic body conversion `F t ≡ F t → F t` under `t : Loop`.
  obtain ⟨c⟩ := Ann.pinLoopConv_erased (n := n)
  -- reversed motive β under the binder: `sort 0 ≡ M̂ t` at `sort 1`.
  have hbeta : ConvT (Ann.eraseEnv Ann.pinLoopEnvA) n
      [.assumption (.const 60 [])] (.sort .zero) loopC2Mt
      (.sort (.succ .zero)) :=
    .symm _ _ _ _
      (.beta _ (.const 60 []) (.sort .zero) (.bvar 0)
        (.sort (.succ .zero)) .zero hLc (.sort _ .zero) ht)
  -- `Π (t:Loop). sort 0 ≡ Π (t:Loop). M̂ t` — the `tyConv` index bridge.
  have hPi : ConvT (Ann.eraseEnv Ann.pinLoopEnvA) n []
      (.pi loopC2T (.sort .zero)) (.pi loopC2T loopC2Mt)
      (.sort (.imax .zero (.succ .zero))) :=
    .pi _ _ _ _ _ .zero (.succ .zero) (.refl _ _ _ hL) hbeta
  -- `λt. F t ≡ λt. (F t → F t)` at `Π (t:Loop). sort 0`, re-indexed.
  have hlam : ConvT (Ann.eraseEnv Ann.pinLoopEnvA) n []
      (.lam loopC2T (Ann.erase Ann.pinLoopA))
      (.lam loopC2T (Ann.erase Ann.pinLoopArrow))
      (.pi loopC2T (.sort .zero)) :=
    .lam _ _ _ _ _ _ .zero (.refl _ _ _ hL) c
  -- reversed η composed with the re-indexed λ-lift: `F ≡ λt. F t → F t`.
  exact ⟨.trans _ _ _ _ _
    (.symm _ _ _ _ (.eta _ _ _ _ hF))
    (.tyConv _ _ _ _ _ _ hlam hPi)⟩

#print axioms pinLoopC2_conv

end Rcic.Declarative
