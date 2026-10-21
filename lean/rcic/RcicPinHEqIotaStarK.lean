import rcic.RcicPinHEqEraseWf
import rcic.RcicPinEqIotaStarK

set_option maxRecDepth 8192

/-!
# `pinHEqT` — the `iotaStarK` three-pin fixture at `HEq`

The `HEq` twin of `RcicPinEqIotaStarK` (F05b, cc on #6421). Same three
pins over `EnvWfT heqEnvT`, plain side:

* **(i) gate met** — `pinHEqGate_met` : `q : HEq α a α a` is a context
  lookup; `pinHEq_convK` : the derived `ConvT` join
  `rec α a M m α a q ⇒ m : M α a q` via `irr` at the shared
  `HEq α a α a` + `app`-congruence + `ConvT.iota` at `heqKWitness`
  (field-free `HEq.refl`-major `IotaWitness`) + `tyConv` index exchange.
  The typed gate `HasTyT q (HEq α a α a)` IS the `β≡α ∧ b≡a` side
  condition.
* **(ii) gate NOT met** — `pinHEq_stuck_neutral`/`pinHEq_gateNotMet` :
  at `q : HEq α a α b` with `b` a distinct bvar (`bvar 0 ≠ bvar 3` in
  the stored type), every `ParRedStar` reduct keeps the
  `const 65`-headed all-bvar spine — ordinary ι is stuck and there is
  no join with `m`.
* **(iii) the tooth** — `pinHEq_tooth` : `Nonempty ConvT` ∧
  `¬ Joinable` at `q : HEq α a α a` — the `irr + ι` conversion exists
  while the ordinary-ι `ParRedStar` join does not. One-shot, not
  cyclic.

The generic spine/normality machinery is shared from `RcicPinEqIotaStarK`'s
`EqPin` namespace (the recursor-spine inversion is env/member-
parameterized — same `const 65` head, instantiated at `heqRecT`'s
opacity facts). `closure_claim` stays 0.
-/

namespace Rcic.Declarative

/-! ## contexts and spine terms -/

/-- `p`'s stored type in the join context: `HEq α a α a` under
`[m, M, a, α]` — the `iotaStarK` gate premise `q : I ps (idx_c f)`
literally (indices `(β, b)` unified to `(α, a)`). -/
def heqPTy : Expr Nat :=
  foldApps (.const 63 []) [.bvar 3, .bvar 2, .bvar 3, .bvar 2]

/-- `HEq α a α a` at the use site `Γ = [p, m, M, a, α]`
(`lift 0 1 heqPTy`). -/
def heqPTyAt0 : Expr Nat :=
  foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 4, .bvar 3]

/-- the join context `[p : HEq α a α a, m : M α a (refl α a),
    M : Π β b, HEq α a β b → Sort (param 0), a : α, α : Sort 1]`. -/
def heqJoinCtx : LCtx :=
  [.assumption heqPTy, .assumption heqMinorT, .assumption heqMotT,
    .assumption (.bvar 0), .assumption (.sort (.succ .zero))]

/-- `m`'s looked-up type at the join context: `M α a (HEq.refl α a)`
(`lift 0 2 heqMinorT`). -/
def heqEqLhsJ : Expr Nat :=
  .app (.app (.app (.bvar 2) (.bvar 4)) (.bvar 3))
    (foldApps (.const 64 []) [.bvar 4, .bvar 3])

/-- `refl α a` at the join-context positions. -/
def heqReflApp : Expr Nat := foldApps (.const 64 []) [.bvar 4, .bvar 3]

/-- the recursor's pre-major spine `[α, a, M, m, α, a]` (`β := α`,
`b := a`). -/
def heqRecPreJ : List (Expr Nat) :=
  [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 4, .bvar 3]

/-- `rec α a M m α a` — the redex's function part. -/
def heqRecSix : Expr Nat := foldApps (.const 65 [.param 0]) heqRecPreJ

/-- `Π (p : HEq α a α a), M α a p` — the redex function's type. -/
def heqMotApPi : Expr Nat :=
  .pi heqPTyAt0 (.app (.app (.app (.bvar 3) (.bvar 5)) (.bvar 4)) (.bvar 0))

/-- `M α a p` — the join's type. -/
def heqMotAp : Expr Nat :=
  .app (.app (.app (.bvar 2) (.bvar 4)) (.bvar 3)) (.bvar 0)

/-- `p`'s stored type in the neutral context: `HEq α a α b` under
`[b, m, M, a, α]` — the type-index `β := α` matches but the
value-index `b` is `bvar 0` while `a` is `bvar 3`: DISTINCT bvars. -/
def heqNeutPTy : Expr Nat :=
  foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 4, .bvar 0]

/-- the neutral context `[p : HEq α a α b, b : α, m, M, a, α]`. -/
def heqNeutCtx : LCtx :=
  [.assumption heqNeutPTy, .assumption (.bvar 3), .assumption heqMinorT,
    .assumption heqMotT, .assumption (.bvar 0),
    .assumption (.sort (.succ .zero))]

/-- the all-bvar neutral spine `[α, a, M, m, α, b, p]`. -/
def heqNeutSpine : List (Expr Nat) :=
  [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 5, .bvar 1, .bvar 0]

/-- `rec α a M m α b p` — the gate-not-met redex. -/
def heqNeutRedex : Expr Nat := foldApps (.const 65 [.param 0]) heqNeutSpine

theorem heqJoinCtx_noLet (i : Nat) (A v : Expr Nat) :
    heqJoinCtx.get? i ≠ some (.letBinding A v) := by
  match i with
  | 0 => simp [heqJoinCtx]
  | 1 => simp [heqJoinCtx]
  | 2 => simp [heqJoinCtx]
  | 3 => simp [heqJoinCtx]
  | 4 => simp [heqJoinCtx]
  | n + 5 =>
      intro h
      have hle : heqJoinCtx.length ≤ n + 5 := by
        have : heqJoinCtx.length = 5 := rfl
        omega
      rw [List.get?_eq_none.mpr hle] at h
      exact Option.noConfusion h

theorem heqNeutCtx_noLet (i : Nat) (A v : Expr Nat) :
    heqNeutCtx.get? i ≠ some (.letBinding A v) := by
  match i with
  | 0 => simp [heqNeutCtx]
  | 1 => simp [heqNeutCtx]
  | 2 => simp [heqNeutCtx]
  | 3 => simp [heqNeutCtx]
  | 4 => simp [heqNeutCtx]
  | 5 => simp [heqNeutCtx]
  | n + 6 =>
      intro h
      have hle : heqNeutCtx.length ≤ n + 6 := by
        have : heqNeutCtx.length = 6 := rfl
        omega
      rw [List.get?_eq_none.mpr hle] at h
      exact Option.noConfusion h

theorem heqNeut_b_ne_a : (.bvar 0 : Expr Nat) ≠ .bvar 3 := by decide

/-! ## HasTyT leaves -/

def heqTyα : HasTyT heqEnvT 1 heqJoinCtx (.bvar 4) (.sort (.succ .zero)) :=
  HasTyT.bvar _ 4 _ rfl

def heqTya : HasTyT heqEnvT 1 heqJoinCtx (.bvar 3) (.bvar 4) :=
  HasTyT.bvar _ 3 _ rfl

def heqTyM : HasTyT heqEnvT 1 heqJoinCtx (.bvar 2) (lift 0 3 heqMotT) :=
  HasTyT.bvar _ 2 _ rfl

def heqTym : HasTyT heqEnvT 1 heqJoinCtx (.bvar 1) heqEqLhsJ :=
  HasTyT.bvar _ 1 _ rfl

/-- THE GATE, met: `q` types at the constructor's result `HEq α a α a`
(`I ps (idx_c f)`) by context lookup — `β ≡ α` AND `b ≡ a` at once. -/
def pinHEqGate_met : HasTyT heqEnvT 1 heqJoinCtx (.bvar 0) heqPTyAt0 :=
  HasTyT.bvar _ 0 _ rfl

/-- `refl α a : HEq α a α a` — the constructor application the gate
unifies the major with. -/
def heqReflTy0 : HasTyT heqEnvT 1 heqJoinCtx (.const 64 [])
    (instantiateLevels [] heqReflT.mtype) :=
  HasTyT.const _ 64 [] heqReflT rfl rfl rfl

def heqReflTy1 : HasTyT heqEnvT 1 heqJoinCtx (.app (.const 64 []) (.bvar 4))
    (.pi (.bvar 4) (foldApps (.const 63 []) [.bvar 5, .bvar 0, .bvar 5,
      .bvar 0])) :=
  HasTyT.app _ _ _ _ _ heqReflTy0 heqTyα

def heqReflTy2 : HasTyT heqEnvT 1 heqJoinCtx heqReflApp heqPTyAt0 :=
  HasTyT.app _ _ _ _ _ heqReflTy1 heqTya

/-- `HEq α a α a : Sort 0` — the `irr` Prop premise. -/
def heqFamTy0 : HasTyT heqEnvT 1 heqJoinCtx (.const 63 [])
    (instantiateLevels [] heqFamT.mtype) :=
  HasTyT.const _ 63 [] heqFamT rfl rfl rfl

def heqFamTy1 : HasTyT heqEnvT 1 heqJoinCtx (.app (.const 63 []) (.bvar 4))
    (.pi (.bvar 4) (.pi (.sort (.succ .zero)) (.pi (.bvar 0)
      (.sort .zero)))) :=
  HasTyT.app _ _ _ _ _ heqFamTy0 heqTyα

def heqFamTy2 : HasTyT heqEnvT 1 heqJoinCtx
    (.app (.app (.const 63 []) (.bvar 4)) (.bvar 3))
    (.pi (.sort (.succ .zero)) (.pi (.bvar 0) (.sort .zero))) :=
  HasTyT.app _ _ _ _ _ heqFamTy1 heqTya

def heqFamTy3 : HasTyT heqEnvT 1 heqJoinCtx
    (.app (.app (.app (.const 63 []) (.bvar 4)) (.bvar 3)) (.bvar 4))
    (.pi (.bvar 4) (.sort .zero)) :=
  HasTyT.app _ _ _ _ _ heqFamTy2 heqTyα

def heqFamTy4 : HasTyT heqEnvT 1 heqJoinCtx heqPTyAt0 (.sort .zero) :=
  HasTyT.app _ _ _ _ _ heqFamTy3 heqTya

/-- `irr` at the shared `HEq α a α a`: `q ≡ refl α a`. The gate is
`irr`'s `hp` premise. -/
def heqIrr : ConvT heqEnvT 1 heqJoinCtx (.bvar 0) heqReflApp heqPTyAt0 :=
  ConvT.irr _ heqPTyAt0 (.bvar 0) heqReflApp heqFamTy4 pinHEqGate_met
    heqReflTy2

/-- the recursor's spine typing:
`rec α a M m α a : Π p : HEq α a α a, M α a p`. -/
def heqRecTy0 : HasTyT heqEnvT 1 heqJoinCtx (.const 65 [.param 0])
    (instantiateLevels [.param 0] heqRecT.mtype) :=
  HasTyT.const _ 65 [.param 0] heqRecT rfl rfl rfl

def heqRecTy1 := HasTyT.app _ _ _ _ _ heqRecTy0 heqTyα
def heqRecTy2 := HasTyT.app _ _ _ _ _ heqRecTy1 heqTya
def heqRecTy3 := HasTyT.app _ _ _ _ _ heqRecTy2 heqTyM
def heqRecTy4 := HasTyT.app _ _ _ _ _ heqRecTy3 heqTym
def heqRecTy5 := HasTyT.app _ _ _ _ _ heqRecTy4 heqTyα

def heqRecTy6 : HasTyT heqEnvT 1 heqJoinCtx heqRecSix heqMotApPi :=
  HasTyT.app _ _ _ _ _ heqRecTy5 heqTya

/-- the iota lhs typing:
`rec α a M m α a (refl α a) : M α a (refl α a)`. -/
def heqRecLhsTy : HasTyT heqEnvT 1 heqJoinCtx (.app heqRecSix heqReflApp)
    heqEqLhsJ :=
  HasTyT.app _ _ _ _ _ heqRecTy6 heqReflTy2

/-- `M α a : Π p : HEq α a α a, Sort (param 0)` — for the `tyConv`
exchange. -/
def heqMaTy : HasTyT heqEnvT 1 heqJoinCtx
    (.app (.app (.bvar 2) (.bvar 4)) (.bvar 3))
    (.pi heqPTyAt0 (.sort (.param 0))) :=
  HasTyT.app _ _ _ _ _ (HasTyT.app _ _ _ _ _ heqTyM heqTyα) heqTya

/-! ## the `refl`-major iota witness -/

/-- The field-free `IotaWitness` at the `HEq.refl`-headed major
`HEq.refl α a` (ctor levels `[]`, recursor levels `[param 0]`). -/
def heqKWitness : IotaWitness heqEnvT where
  recRef := 65
  ctorRef := 64
  ls := [.param 0]
  lsC := []
  recMember := heqRecT
  ctorMember := heqReflT
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 4, .bvar 3]
  fields := []
  ctorParams := [.bvar 4, .bvar 3]
  kinds := []
  minor := .bvar 1
  hlen := rfl
  familyRef := 63
  famMember := heqFamT
  hfam := rfl
  hfamK := rfl
  nparams := 2
  nindices := 2
  nMinors := 1
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
  ctorDoms := [.sort (.succ .zero), .bvar 0]
  ctorResult := foldApps (.const 63 []) [.bvar 1, .bvar 0, .bvar 1, .bvar 0]
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.sort (.succ .zero), .bvar 0, heqMotT, heqMinorT,
    .sort (.succ .zero), .bvar 0,
    foldApps (.const 63 []) [.bvar 5, .bvar 4, .bvar 1, .bvar 0]]
  recBody := .app (.app (.app (.bvar 4) (.bvar 2)) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := by decide
  hctorClosed := by decide
  hlsLen := rfl
  ctorAfterParams := foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 4,
    .bvar 3]
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-! ## the three pins -/

/-- `app`-congruence: the `irr` conversion lifts the variable major to
the `refl`-headed major inside the redex, at type `M α a p`. -/
def heqAppCong : ConvT heqEnvT 1 heqJoinCtx (.app heqRecSix (.bvar 0))
    (.app heqRecSix heqReflApp) heqMotAp :=
  ConvT.app _ heqRecSix heqRecSix (.bvar 0) heqReflApp heqPTyAt0
    (.app (.app (.app (.bvar 3) (.bvar 5)) (.bvar 4)) (.bvar 0))
    (ConvT.refl _ _ _ heqRecTy6) heqIrr

/-- the type exchange: `M α a p ≡ M α a (refl α a)` at `Sort (param 0)`
— `irr` at the index, `refl` at `M α a`. -/
def heqTyX : ConvT heqEnvT 1 heqJoinCtx heqMotAp heqEqLhsJ
    (.sort (.param 0)) :=
  ConvT.app _ _ _ (.bvar 0) heqReflApp heqPTyAt0 (.sort (.param 0))
    (ConvT.refl _ _ _ heqMaTy) heqIrr

/-- honest iota: `rec α a M m α a (refl α a) ⇒ m` at `M α a (refl α a)`,
carried by `DerivedIota heqKWitness` and real `HasTyT` legs. -/
def heqIotaK : ConvT heqEnvT 1 heqJoinCtx
    (.app heqRecSix heqReflApp) (.bvar 1) heqEqLhsJ :=
  ConvT.iota _ _ _ _ (.of heqKWitness) heqRecLhsTy heqTym

/-- the iota conversion transported to `M α a p` by the index exchange. -/
def heqIotaAtP : ConvT heqEnvT 1 heqJoinCtx
    (.app heqRecSix heqReflApp) (.bvar 1) heqMotAp :=
  ConvT.tyConv _ _ _ _ _ (.param 0) heqIotaK (ConvT.symm _ _ _ _ heqTyX)

/-- PIN (i), the join: at `q : HEq α a α a` the typed-K gate is met and
`rec α a M m α a q ⇒ m : M α a q` exists as a `ConvT` — `irr` at the
shared `HEq α a α a` + `app`-congruence + `iota` + `tyConv`. -/
def pinHEq_convK :
    Nonempty (ConvT heqEnvT 1 heqJoinCtx (.app heqRecSix (.bvar 0))
      (.bvar 1) heqMotAp) :=
  ⟨ConvT.trans _ _ _ _ _ heqAppCong heqIotaAtP⟩

/-- PIN (ii) part 1: at `q : HEq α a α b` (`b` a distinct bvar) every
`ParRedStar` reduct of `rec α a M m α b q` keeps the `const 65`-headed
all-bvar spine — ordinary ι is stuck; the recursor is `⇒`-neutral. -/
def pinHEq_stuck_neutral {n : Nat} {c : Expr Nat}
    (hR : ParRedStar heqEnvT n heqNeutCtx heqNeutRedex c) :
    Σ' (ls' : List Level),
      c = foldApps (.const 65 ls') heqNeutSpine :=
  EqPin.parRedStar_rec_bvar_class heqRecT rfl rfl (xs := heqNeutSpine)
    heqNeutCtx_noLet
    (by
      intro x hx
      simp only [heqNeutSpine, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨5, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩)
    hR rfl

/-- PIN (ii) part 2, the gate refusal: `rec α a M m α b q` and `m` have
no common `ParRedStar` reduct. -/
theorem pinHEq_gateNotMet {n : Nat} :
    ¬ EqPin.Joinable heqEnvT n heqNeutCtx heqNeutRedex (.bvar 2) := by
  rintro ⟨c, ⟨hR⟩, ⟨hM⟩⟩
  obtain ⟨ls', hc⟩ := pinHEq_stuck_neutral hR
  have hc' : c = .bvar 2 :=
    EqPin.parRedStar_bvar_normal (heqNeutCtx_noLet 2) hM rfl
  rw [hc] at hc'
  exact EqPin.foldApps_const_ne_bvar _ hc'

/-- PIN (iii), the tooth: at `q : HEq α a α a` the `irr + ι` `ConvT`
exists while the `ParRedStar` join does not. -/
theorem pinHEq_tooth {n : Nat} :
    Nonempty (ConvT heqEnvT 1 heqJoinCtx (.app heqRecSix (.bvar 0))
        (.bvar 1) heqMotAp) ∧
    ¬ EqPin.Joinable heqEnvT n heqJoinCtx (.app heqRecSix (.bvar 0))
      (.bvar 1) :=
  ⟨pinHEq_convK, by
    rintro ⟨c, ⟨hR⟩, ⟨hM⟩⟩
    obtain ⟨ls', hc⟩ :=
      EqPin.parRedStar_rec_bvar_class heqRecT rfl rfl
        (xs := [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 4, .bvar 3,
          .bvar 0])
        heqJoinCtx_noLet (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact ⟨4, rfl⟩
          · exact ⟨3, rfl⟩
          · exact ⟨2, rfl⟩
          · exact ⟨1, rfl⟩
          · exact ⟨4, rfl⟩
          · exact ⟨3, rfl⟩
          · exact ⟨0, rfl⟩)
        hR (show (.app heqRecSix (.bvar 0)) =
          foldApps (.const 65 [.param 0])
            [.bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 4, .bvar 3,
              .bvar 0] from rfl)
    have hc' : c = .bvar 1 :=
      EqPin.parRedStar_bvar_normal (heqJoinCtx_noLet 1) hM rfl
    rw [hc] at hc'
    exact EqPin.foldApps_const_ne_bvar _ hc'⟩

#print axioms pinHEqGate_met
#print axioms heqKWitness
#print axioms pinHEq_convK
#print axioms pinHEq_stuck_neutral
#print axioms pinHEq_gateNotMet
#print axioms pinHEq_tooth

end Rcic.Declarative
