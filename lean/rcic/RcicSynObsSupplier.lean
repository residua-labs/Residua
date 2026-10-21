import rcic.RcicSynObsLevels
import rcic.RcicSynAdm

/-!
# T3 — the admission-observation supplier (`S7_ADMISSION_OBSERVATION_SUPPLIER`)

S4 (`RcicSynObsLevels`) gave the raw observation machinery: `TyP.outLevels`/`gateLevels`,
`obsLvlEq_eps_delta`, and the §3 supply table (`supplyOut_*`/`supplyGate_*`). What was missing
was the **supplier**: the record that binds an observation plan to the actual admission
identity, and the discipline that a plan may only hand `obsLvlEq_eps_delta` premises it has
genuinely supplied.

This module builds exactly that:

* **`ObsCert`** — per-observation certificates for the δ maps `φ l = instLevel (ls.map σ) l`
  and `ψ l = σ (instLevel ls l)`. Supplying ctors are the S7 §3 routes (bounded, eqN to a
  bounded representative, successor gate, uniform `Prop`/`Type` gates). `sameCtxOrigin`,
  `sameMemberOrigin`, and `pending` record *provenance or an open obligation* and supply
  nothing — a pointer to another position's certificate is not a proof, and
  `PendingActualObservation` is never an answer (§3, §5).

* **`AdmObsPlan`** — the supply plan bound to a real `DefAdm` selection (§1). `Db_eq` pins the
  observed derivation to the `hv` the actual admission selected: an arbitrary same-judgment
  `TyP` cannot be substituted. `outPositions`/`gatePositions` pin the plan's rows to `Db`'s
  own observer lists, preserving the original occurrence positions.

* **`AdmObsPlan.discharge`** — only a `Complete` plan (every out entry supplies `eqN`, every
  gate entry supplies the bit equation) may call `obsLvlEq_eps_delta`.

* **§6 controls** — the unread `hT` of `app`, the bvar context-entry certificate, linst
  observation positions, `u★` kept as original bytes, the weak gate-checker that wrongly
  accepts, the wrong-identity refusal, and the cycle refusal (`pending` blocks `Complete`;
  under `phiUStarZero` the `u★` gate is unsuppliable and the would-be conclusion is empty).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1–2 — observation certificates -/

/-- How one recorded level observation is supplied under the δ maps. The last three ctors
    supply nothing: they are bookkeeping (a pointer to a same-origin position's certificate,
    or an open `PendingActualObservation` cell), never proofs. -/
inductive ObsCert (σ : Level → Level) (ls : List Level) : Level → Type where
  /-- §3 row 1: `l` is bounded below `ls.length`, so `instLevel (ls.map σ) l` and
      `σ (instLevel ls l)` agree literally (`instLevel_map_of_levelHom`). -/
  | bounded {l} : levelBounded ls.length l = true → LevelHom σ → ObsCert σ ls l
  /-- §3 row 2: `l` transports by `eqN` to a bounded representative `l₀`. The `σ`-side
      equation `eqN (σ (instLevel ls l)) (σ (instLevel ls l₀))` is an explicit premise — a
      `LevelHom` does not preserve `eqN` on parameters. -/
  | eqNRep {l} (l₀ : Level) : eqN l l₀ → levelBounded ls.length l₀ = true →
      eqN (σ (instLevel ls l)) (σ (instLevel ls l₀)) → LevelHom σ → ObsCert σ ls l
  /-- §3 row 3: a successor gate — both bits are `false` under any `LevelHom`. -/
  | succGate (l₀ : Level) : LevelHom σ → ObsCert σ ls (.succ l₀)
  /-- §3 row 3′: a parameter-free `UniformType` gate — both bits are `false`. -/
  | uniformType {l} : levelBounded 0 l = true → UniformType l → LevelHom σ →
      ObsCert σ ls l
  /-- §3 row 4: a parameter-free `UniformProp` gate — both bits are `true`. -/
  | uniformProp {l} : levelBounded 0 l = true → UniformProp l → LevelHom σ →
      ObsCert σ ls l
  /-- §3 row 5: same recorded context-entry origin — a pointer to the position `pos`,
      carrying provenance only. -/
  | sameCtxOrigin {l} (pos : Nat) : ObsCert σ ls l
  /-- §3 row 5: same recorded member origin — a pointer to the position `pos`. -/
  | sameMemberOrigin {l} (pos : Nat) : ObsCert σ ls l
  /-- §3 row 5: `PendingActualObservation` — the unresolved obligation at derivation-node
      path `nodePath`, payload position `payPos`. It never counts as supplied. -/
  | pending {l} (nodePath payPos : Nat) : ObsCert σ ls l

/-- What a certificate actually yields for an OUT observation (`eqN` of the two maps).
    Bookkeeping ctors return `none`. (`PLift` because the payload is a `Prop`.) -/
def ObsCert.supplyOut {σ : Level → Level} {ls : List Level} {l : Level} :
    ObsCert σ ls l →
    Option (PLift (eqN (instLevel (ls.map σ) l) (σ (instLevel ls l))))
  | .bounded hb hσ => some ⟨supplyOut_eq_of_bounded hσ ls hb⟩
  | .eqNRep _l₀ hl hb hψ hσ =>
      some ⟨supplyOut_of_eqN_rep (φ := fun l => instLevel (ls.map σ) l)
        (ψ := fun l => σ (instLevel ls l))
        (eqN_instLevel_obs hl (ls.map σ)) hψ
        (supplyOut_eq_of_bounded hσ ls hb)⟩
  | _ => none

/-- What a certificate actually yields for a GATE observation (the `levelIsZero` bit
    equation). Bookkeeping ctors return `none`. -/
def ObsCert.supplyGate {σ : Level → Level} {ls : List Level} {l : Level} :
    ObsCert σ ls l →
    Option (PLift (levelIsZero (instLevel (ls.map σ) l) =
      levelIsZero (σ (instLevel ls l))))
  | .bounded hb hσ => some ⟨levelIsZero_congr (supplyOut_eq_of_bounded hσ ls hb)⟩
  | .eqNRep _l₀ hl hb hψ hσ =>
      some ⟨(levelIsZero_congr (eqN_instLevel_obs hl (ls.map σ))).trans
        ((levelIsZero_congr (supplyOut_eq_of_bounded hσ ls hb)).trans
          (levelIsZero_congr hψ).symm)⟩
  | .succGate l₀ hσ => some ⟨supplyGate_succ hσ ls l₀⟩
  | .uniformType hb hUT hσ => some ⟨supplyGate_uniformType_eq hσ ls hb hUT⟩
  | .uniformProp hb hUP hσ => some ⟨supplyGate_uniformProp_eq hσ ls hb hUP⟩
  | _ => none

/-- §1 — the observer-supply plan bound to a REAL admission selection. `Db_eq` pins `Db` to
    the `hv` the actual `DefAdm` selected; a same-judgment `TyP` cannot be substituted. The
    `*Positions` fields pin every plan row's observed level to `Db`'s own observer lists, so
    the plan covers exactly the original occurrence positions, in order. -/
structure AdmObsPlan {E : ResolvedEnv} {Aw : Nat → Nat} {r : Nat} {m : CheckedMember}
    {b : Expr Nat} (a : DefAdm E Aw r m b) (σ : Level → Level) (ls : List Level) : Type where
  Db : TyP a.E₀ 0 [] b m.mtype
  Db_eq : Db = a.hv
  outPlan : List (Σ l : Level, ObsCert σ ls l)
  gatePlan : List (Σ l : Level, ObsCert σ ls l)
  outPositions : outPlan.map (·.1) = Db.OutLevels
  gatePositions : gatePlan.map (·.1) = Db.GateLevels

/-- §5 — completeness: every recorded out observation supplies `eqN`, every recorded gate
    observation supplies its bit equation. `pending` and origin pointers never satisfy this. -/
def AdmObsPlan.Complete {E : ResolvedEnv} {Aw : Nat → Nat} {r : Nat} {m : CheckedMember}
    {b : Expr Nat} {a : DefAdm E Aw r m b} {σ : Level → Level} {ls : List Level}
    (p : AdmObsPlan a σ ls) : Prop :=
  (∀ e ∈ p.outPlan, (e.2.supplyOut).isSome = true) ∧
    (∀ e ∈ p.gatePlan, (e.2.supplyGate).isSome = true)

theorem AdmObsPlan.supply_out {E : ResolvedEnv} {Aw : Nat → Nat} {r : Nat} {m : CheckedMember}
    {b : Expr Nat} {a : DefAdm E Aw r m b} {σ : Level → Level} {ls : List Level}
    (p : AdmObsPlan a σ ls) (hc : p.Complete) {l : Level} (hl : l ∈ p.Db.OutLevels) :
    eqN (instLevel (ls.map σ) l) (σ (instLevel ls l)) := by
  rw [← p.outPositions] at hl
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
  obtain ⟨c, -⟩ := Option.isSome_iff_exists.mp (hc.1 e he)
  exact c.down

theorem AdmObsPlan.supply_gate {E : ResolvedEnv} {Aw : Nat → Nat} {r : Nat}
    {m : CheckedMember} {b : Expr Nat} {a : DefAdm E Aw r m b} {σ : Level → Level}
    {ls : List Level} (p : AdmObsPlan a σ ls) (hc : p.Complete) {l : Level}
    (hl : l ∈ p.Db.GateLevels) :
    levelIsZero (instLevel (ls.map σ) l) = levelIsZero (σ (instLevel ls l)) := by
  rw [← p.gatePositions] at hl
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
  obtain ⟨c, -⟩ := Option.isSome_iff_exists.mp (hc.2 e he)
  exact c.down

/-- §5 — the only entry point to the δ-exchange: a complete plan discharges the actual `Db`'s
    observation table and yields the erasure equality. An unresolved obligation keeps
    `Complete` false and this call unreachable. -/
theorem AdmObsPlan.discharge {E : ResolvedEnv} {Aw : Nat → Nat} {r : Nat} {m : CheckedMember}
    {b : Expr Nat} {a : DefAdm E Aw r m b} {σ : Level → Level} {ls : List Level}
    (p : AdmObsPlan a σ ls) (hc : p.Complete) :
    LvlEq (p.Db.eps (instLevel (ls.map σ)) [])
      (p.Db.eps (fun l => σ (instLevel ls l)) []) :=
  obsLvlEq_eps_delta p.Db (fun _ hl => p.supply_out hc hl)
    (fun _ hl => p.supply_gate hc hl)

/-- `Db_eq` is the load-bearing field — the observed derivation IS the selected one. -/
theorem AdmObsPlan.forces_actual {E : ResolvedEnv} {Aw : Nat → Nat} {r : Nat}
    {m : CheckedMember} {b : Expr Nat} (a : DefAdm E Aw r m b) {σ : Level → Level}
    {ls : List Level} (p : AdmObsPlan a σ ls) : p.Db = a.hv := p.Db_eq

/-! ## §6 controls -/

section AppUnreadH
/-- `Γ₂ = [f : s₀ → s₀][x : s₀]`-ish — `bvar 0` is the pi-typed entry, `bvar 1` the s₀-typed
    entry. -/
def t3Γ : LCtx := [.assumption (.pi s0Expr s0Expr), .assumption s0Expr]

def t3piCert : TyP emptyEnv 0 t3Γ (.pi s0Expr s0Expr)
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  TyP.pi emptyEnv 0 t3Γ s0Expr (.succ .zero) s0Expr (.succ .zero)
    (TyP.sort emptyEnv 0 t3Γ .zero (.succ .zero) (eqN_refl _))
    (TyP.sort emptyEnv 0 (.assumption s0Expr :: t3Γ) .zero (.succ .zero) (eqN_refl _))

def t3hf : TyP emptyEnv 0 t3Γ (.bvar 0) (.pi s0Expr s0Expr) :=
  TyP.bvar emptyEnv 0 t3Γ 0 (.pi s0Expr s0Expr) (.imax (.succ .zero) (.succ .zero)) rfl
    t3piCert

def t3ha : TyP emptyEnv 0 t3Γ (.bvar 1) s0Expr :=
  TyP.bvar emptyEnv 0 t3Γ 1 s0Expr (.succ .zero) rfl
    (TyP.sort emptyEnv 0 t3Γ .zero (.succ .zero) (eqN_refl _))

def t3hT1 : TyP emptyEnv 0 t3Γ s0Expr (.sort (.succ .zero)) :=
  TyP.sort emptyEnv 0 t3Γ .zero (.succ .zero) (eqN_refl _)

def t3cvS : CvP emptyEnv 0 t3Γ (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  CvP.sorts emptyEnv 0 t3Γ (.succ .zero) (.succ .zero) (eqN_refl _)
    (TyP.sort emptyEnv 0 t3Γ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))
    (TyP.sort emptyEnv 0 t3Γ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- A second, *different* `hT` at the same judgment, via a `conv` retyping. -/
def t3hT2 : TyP emptyEnv 0 t3Γ s0Expr (.sort (.succ .zero)) :=
  TyP.conv emptyEnv 0 t3Γ s0Expr (.sort (.succ .zero)) (.sort (.succ .zero))
    (.succ (.succ .zero)) t3hT1 t3cvS

def t3appF (hT : TyP emptyEnv 0 t3Γ s0Expr (.sort (.succ .zero))) :
    TyP emptyEnv 0 t3Γ (.app (.bvar 0) (.bvar 1)) s0Expr :=
  TyP.app emptyEnv 0 t3Γ (.bvar 0) (.bvar 1) s0Expr s0Expr (.succ .zero) t3hf t3ha hT

/-- §6.1 — the native app's observation reads only `hf` and `ha`; the freshly built `hT`
    contributes no observation at all. -/
theorem app_obs_reads_hf_ha :
    (t3appF t3hT1).OutLevels = [] ∧
      (t3appF t3hT1).GateLevels = [.imax (.succ .zero) (.succ .zero), .succ .zero] :=
  ⟨rfl, rfl⟩

/-- §6.1 — and the erasure itself never reads `hT`: two different `hT` derivations erase
    identically under any `σ`, `ρ`. -/
theorem app_hT_unread (σ : Level → Level) (ρ : List Disp) :
    LvlEq ((t3appF t3hT1).eps σ ρ) ((t3appF t3hT2).eps σ ρ) := by
  unfold t3appF
  rw [eps_app_eq, eps_app_eq]
  exact LvlEq.rfl' _
end AppUnreadH

/-- §6.2 — a native bvar node's gate IS the sort level of the current context entry's own
    certificate `hA`; it reads that certificate, not a rebuilt one. -/
theorem bvar_gate_is_entry_cert {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat}
    {A : Expr Nat} {u : Level} {hlook : lookupType Γ i = some A}
    (hA : TyP E n Γ A (.sort u)) :
    (TyP.bvar E n Γ i A u hlook hA).GateLevels = [u] := rfl

theorem bvar_entry_cert : t3ha.GateLevels = [.succ .zero] := rfl

section LinstPositions
/-- Arity-1 fixtures for the linst position controls. -/
def t3sortP : TyP emptyEnv 1 [] (.sort (.param 0)) (.sort (.succ (.param 0))) :=
  TyP.sort emptyEnv 1 [] (.param 0) (.succ (.param 0)) (eqN_refl _)

def t3bvarP : TyP emptyEnv 1 [.assumption (.sort (.param 0))] (.bvar 0)
    (.sort (.param 0)) :=
  TyP.bvar emptyEnv 1 [.assumption (.sort (.param 0))] 0 (.sort (.param 0))
    (.succ (.param 0)) rfl
    (TyP.sort emptyEnv 1 [.assumption (.sort (.param 0))] (.param 0)
      (.succ (.param 0)) (eqN_refl _))

/-- linst at `ls := [.zero]`: the out observation position maps through `instLevel ls`,
    landing at `.zero`. -/
def t3linstOut : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  TyP.linst emptyEnv 1 0 [] (.sort (.param 0)) (.sort (.succ (.param 0))) [.zero] rfl rfl
    t3sortP

/-- linst at `ls := [.succ .zero]`: the gate position maps through `instLevel ls`. -/
def t3linstGate : TyP emptyEnv 0 [.assumption (.sort (.succ .zero))] (.bvar 0)
    (.sort (.succ .zero)) :=
  TyP.linst emptyEnv 1 0 [.assumption (.sort (.param 0))] (.bvar 0) (.sort (.param 0))
    [.succ .zero] rfl rfl t3bvarP

/-- §6.3 — out positions are read through the actual `instLevel` map of the recorded `ls`,
    not re-derived. -/
theorem linst_out_map : t3linstOut.OutLevels = [.zero] := rfl

/-- §6.3 — the gate position carries the ORIGINAL `succ (param 0)` mapped by `instLevel ls`. -/
theorem linst_gate_map : t3linstGate.GateLevels = [.succ (.succ .zero)] := rfl

/-- §6.3 — the map is literally `instLevel ls` applied at the original position. -/
theorem linst_gate_is_instLevel :
    t3linstGate.GateLevels = [instLevel [.succ .zero] (.succ (.param 0))] := rfl
end LinstPositions

section UStarBytes
/-- §6.4 — `u★` keeps its original bytes: `succ (imax (param 0) zero)`, not `succ zero`. -/
theorem deltaStarU_ne_succZero : deltaStarU ≠ .succ .zero := fun h =>
  Level.noConfusion (Level.succ.inj h)

theorem ustar_bytes_kept : Dvstar.GateLevels.head? = some deltaStarU := rfl

theorem ustar_not_canonicalized : Dvstar.GateLevels ≠ [.succ .zero, .succ .zero] := by
  rw [gateLevels_Dvstar]
  exact fun h => deltaStarU_ne_succZero (List.cons.inj h).1
end UStarBytes

/-- §6.5 — the weak checker: it only tests the gates its own table recorded (`gateLevelsMissLam`
    drops the λ domain gate), never asking whether every gate is present. -/
def WeakGateCheck {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) (φ ψ : Level → Level) : Prop :=
  ∀ l ∈ D.gateLevelsMissLam id, levelIsZero (φ l) = levelIsZero (ψ l)

/-- §6.5 — the weak checker WRONGLY ACCEPTS: the buggy premise holds under `phiUStarZero`, yet
    the two erasures genuinely differ, so the "admitted" conclusion is false. The complete
    supplier refuses this because `u★` is still a recorded gate of `Dvstar`. -/
theorem weak_check_wrong_accept :
    WeakGateCheck Dvstar phiUStarZero id ∧
      ¬ LvlEq (Dvstar.eps phiUStarZero [.keep]) (Dvstar.eps id [.keep]) :=
  ⟨tooth_missing_gate_refuted.1, tooth_missing_gate_refuted.2.2.2⟩

/-- §6.6 — a same-judgment but different derivation: the λ domain annotated `.succ .zero`
    directly instead of `u★` via `conv`. -/
def Dvstar_plain : TyP emptyEnv 0 [] (.lam s0Expr (.bvar 0)) (.pi s0Expr s0Expr) :=
  TyP.lam emptyEnv 0 [] s0Expr (.succ .zero) (.bvar 0) s0Expr (.succ .zero)
    tyP_s0_succZero tyP_bvar0_s0
    (TyP.sort emptyEnv 0 [.assumption s0Expr] .zero (.succ .zero) (eqN_refl _))

theorem gateLevels_Dvstar_plain : Dvstar_plain.GateLevels = [.succ .zero, .succ .zero] := rfl

/-- §6.6 — wrong-identity refusal: the two derivations prove the same judgment but are
    different derivations with different observation records. `AdmObsPlan.Db_eq` makes the
    substitution ill-typed as a plan for the real admission. -/
theorem wrong_identity_obs : Dvstar_plain.GateLevels ≠ Dvstar.GateLevels := by
  rw [gateLevels_Dvstar_plain, gateLevels_Dvstar]
  exact fun h => deltaStarU_ne_succZero (List.cons.inj h).1.symm

theorem wrong_identity_ne : Dvstar_plain ≠ Dvstar := fun h =>
  wrong_identity_obs (congrArg TyP.GateLevels h)

/-- §6.6 — bookkeeping supplies nothing: `pending` and origin pointers return `none` in both
    channels. -/
theorem pending_supplies_nothing {σ : Level → Level} {ls : List Level} {l : Level}
    (i j : Nat) :
    (ObsCert.pending (σ := σ) (ls := ls) (l := l) i j).supplyGate = none ∧
      (ObsCert.pending (σ := σ) (ls := ls) (l := l) i j).supplyOut = none := ⟨rfl, rfl⟩

theorem pointer_supplies_nothing {σ : Level → Level} {ls : List Level} {l : Level}
    (i : Nat) :
    (ObsCert.sameCtxOrigin (σ := σ) (ls := ls) (l := l) i).supplyOut = none ∧
      (ObsCert.sameMemberOrigin (σ := σ) (ls := ls) (l := l) i).supplyGate = none := ⟨rfl, rfl⟩

/-- §6.6 — a pending cell blocks completeness: a plan still recording an unresolved actual
    observation can never call `discharge`. -/
theorem pending_blocks_complete {E : ResolvedEnv} {Aw : Nat → Nat} {r : Nat}
    {m : CheckedMember} {b : Expr Nat} {a : DefAdm E Aw r m b} {σ : Level → Level}
    {ls : List Level} (p : AdmObsPlan a σ ls) (e : Σ l : Level, ObsCert σ ls l)
    (he : e ∈ p.gatePlan) (hp : e.2.supplyGate = none) : ¬ p.Complete := by
  rintro ⟨_, hc⟩
  have h := hc e he
  rw [hp] at h
  exact Bool.noConfusion h

/-- §6.6 — the cycle refusal: under the `phiUStarZero` counter-map the `u★` gate is
    unsuppliable (true bit vs false bit), so no `Complete` plan exists there — the solver
    cannot be fed its own conclusion because that conclusion is empty. -/
theorem cycle_gate_unsupplyable :
    ¬ (levelIsZero (phiUStarZero deltaStarU) = levelIsZero (id deltaStarU)) := by
  rw [phiUStarZero_at_uStar]
  decide

theorem cycle_refuted :
    ¬ LvlEq (Dvstar.eps phiUStarZero [.keep]) (Dvstar.eps id [.keep]) :=
  tooth_missing_gate_refuted.2.2.2

#print axioms Rcic.Syn.AdmObsPlan.discharge
#print axioms Rcic.Syn.app_hT_unread
#print axioms Rcic.Syn.weak_check_wrong_accept
#print axioms Rcic.Syn.wrong_identity_ne
#print axioms Rcic.Syn.cycle_refuted
end Rcic.Syn
