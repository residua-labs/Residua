import rcic.RcicAnnLR3ContentJ

/-!
# Mutant: the J Ty arm needs the K-like operator

`ContentJ.rec_member` shows that every K-like operator (its six-fold
application is the minor premise) realizes the AnySort Eq recursor type.
The property is load-bearing: the operator that returns its last argument,
the major premise (`majorOp`), does not (`majorOp_not_member`).

All premises are constructed: `A := Prop` (the image of `univ 0`), the
motive `λ b h. Prop` (a constant legal graph, `motiveVal`), a motive
candidate that relates only the image of `Prop` (`pinFam`, saturated and
invariant), the minor `Prop`, and bottom for `a`, `b` and the proof `h`.
The minor lives in the motive's candidate; the major does not.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.ContentJMutant

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER
open TypeZeroTowerProbe (withBot)
open CandidateTowerProbe (REnv rcons Sat)
open CandidateTowerCoherence (applyValue_legalGraph_at)
open ContentCodes ContentJ

/-- The operator returning its last argument. -/
def majorOp : Value := denI EnvI.bot (IotaRecursor.lams 6 (.bvar 0))

theorem majorOp_apply (xs : List Value) (hn : xs.length = 6) (hb : ∀ x ∈ xs, x .bot) :
    IotaRecursor.applyAll majorOp xs = xs[5]'(by omega) := by
  rw [majorOp, IotaRecursor.lams_apply 6 _ _ xs hn]
  have hlook := IotaRecursor.pushAll_lookup xs EnvI.bot 5 (by omega)
  have h2 : xs.length - 1 - 5 = 0 := by omega
  rw [h2] at hlook
  have hbot : IotaRecursor.pushAll xs EnvI.bot 0 .bot := by
    rw [hlook]
    exact hb _ (List.getElem_mem _)
  rw [IotaRecursor.denI_bvar hbot, hlook]

/-- A constant function, as a legal graph. -/
def constGraph (W : Value) : Value := UnifiedPi.legalGraph (fun _ _ => True) (fun _ => W)

theorem constGraph_apply {W : Value} (hW : W .bot) (x : Value) :
    NeutralPi.applyValue (constGraph W) x = W :=
  NeutralCodes.valueEq_eq (applyValue_legalGraph_at (fun _ _ _ hc => ⟨[], by simp, fun _ _ _ => hc⟩)
    (x := x) hW)

/-- The image of `Prop`. -/
def V0 : Value := image σ0 (DCode.univ 0)

theorem V0_bot : V0 .bot := image_bot σ0 _

theorem V0_ne_bottom : V0 ≠ bottom := by
  intro h
  have hs : V0 (.spine 10 [.bot, .bot]) := nonvar_obs σ0 (DCode.univ 0) trivial
  rw [h] at hs
  cases hs

/-- The motive `λ b h. Prop`. -/
def motiveVal : Value := constGraph (constGraph V0)

/-- A candidate family that relates only the image of `Prop`. -/
def pinFam : Fam := fun _ x y => x = V0 ∧ y = V0

theorem pinFam_sat : SatFam pinFam := fun _ =>
  ⟨⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, _⟩ ⟨_, b⟩ => ⟨a, b⟩⟩, fun _ _ h => h.1 ▸ V0_bot⟩

def botFam : Fam := fun _ => botRel

theorem botFam_sat : SatFam botFam := fun _ => botRel_sat

theorem bottom_bot : bottom .bot := rfl

theorem univ0_wfc : WFc (DCode.univ 0) := ⟨trivial, trivial⟩

/-- The motive is related to itself by the motive type's reading. -/
theorem motive_el (r : Nat) (σ : REnv) (ρ : FEnv) :
    El σ ρ (motiveTy r 1) motiveVal motiveVal := by
  refine el_pi_intro (Or.inl rfl) (Or.inl rfl) (fun x y _ F _ _ z _ => ?_)
  unfold motiveVal
  rw [constGraph_apply (Or.inl rfl), constGraph_apply (Or.inl rfl)]
  refine el_pi_intro (Or.inl rfl) (Or.inl rfl) (fun h h' _ G _ _ z' _ => ?_)
  rw [constGraph_apply V0_bot, constGraph_apply V0_bot]
  exact ⟨DCode.univ 0, univ0_wfc, ValueEq.refl _, ValueEq.refl _⟩

/-- The pinned candidate is invariant along the motive type. -/
theorem pinFam_inv (r : Nat) (σ : REnv) (ρ : FEnv) : Inv σ ρ (motiveTy r 1) pinFam pinFam :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => fun _ _ => Iff.rfl

/-- **Mutant.** The operator returning the major premise does not realize
the AnySort Eq recursor type (motive level 1). -/
theorem majorOp_not_member (r : Nat) (rf : TImg) :
    ¬ El σ0 ρ0 (recCode r 1 rf) majorOp majorOp := by
  intro h0
  obtain ⟨_, _, h0⟩ := h0
  obtain ⟨⟨_, _, h1⟩, _⟩ := h0 V0 V0 ⟨DCode.univ 0, univ0_wfc, ValueEq.refl _, ValueEq.refl _⟩
    botFam botFam_sat (fun _ _ => Iff.rfl)
  obtain ⟨⟨_, _, h2⟩, _⟩ := h1 bottom bottom ⟨rfl, rfl⟩ botFam botFam_sat trivial
  obtain ⟨⟨_, _, h3⟩, _⟩ := h2 motiveVal motiveVal (motive_el r _ _) pinFam pinFam_sat
    (pinFam_inv r _ _)
  obtain ⟨⟨_, _, h4⟩, _⟩ := h3 V0 V0 ⟨rfl, rfl⟩ botFam botFam_sat trivial
  obtain ⟨⟨_, _, h5⟩, _⟩ := h4 bottom bottom ⟨rfl, rfl⟩ botFam botFam_sat trivial
  obtain ⟨h6, _⟩ := h5 bottom bottom ⟨rfl, rfl, Or.inl rfl, Or.inl rfl⟩ botFam botFam_sat trivial
  have e : IotaRecursor.applyAll majorOp [V0, bottom, motiveVal, V0, bottom, bottom] = bottom :=
    majorOp_apply [V0, bottom, motiveVal, V0, bottom, bottom] rfl (by
      intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact V0_bot
      · exact bottom_bot
      · exact Or.inl rfl
      · exact V0_bot
      · exact bottom_bot
      · exact bottom_bot)
  obtain ⟨h7, _⟩ := h6
  change IotaRecursor.applyAll majorOp [V0, bottom, motiveVal, V0, bottom, bottom] = V0 at h7
  rw [e] at h7
  exact V0_ne_bottom h7.symm

end Rcic.Declarative.Ann.LR3.ContentJMutant
