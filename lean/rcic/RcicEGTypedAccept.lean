import rcic.RcicTypedMachine
import rcic.RcicDTMetaTypedEnv
import rcic.RcicAnnEnvBridge

/-!
# EG-010 on the typed root, singleton half: machine acceptance gives the `EnvWfT` successor
(tymig segment E)

04 §17 EG-010: "accepted addGroup preserves environment well-formedness". On the typed root the
`EnvWfT` constructors ARE the accepted steps (`RcicTypedEnv`), so a theorem quoting a constructor
would be a conclusion built from its own premises. Here "accepted" means something independent: the
TYPED MACHINE accepted (`typedRun`, `RcicTypedMachine`). Each acceptance premise is a BOOL read of a
machine run's result (`inferSortAcceptedB`, `checkAcceptedB`) and carries no derivation. The
derivation is the one the machine computed, read off by unfolding the run to its arm and splitting
the certifier call (`sortTyping_of_inferAcceptedB`, `typing_of_checkAcceptedB`). Together with the
decidable side conditions (freshness, closedness as `lift 0 1 X = X`, level bounds), an accepted
singleton gives the `EnvWfT` successor:

* `EG010T_axiom_accepted` — `infer A` accepted at a sort;
* `EG010T_definition_accepted` / `EG010T_opaque_accepted` — `infer A` accepted at a sort, and
  `check v A` accepted;
* `EG010T_theorem_accepted` — `check A Prop` accepted (the type is a Prop), and `check p A`
  accepted.

The read-off is the one `RM015T_infer_sound` / `RM016T_run_check_sound` (`RcicTypedMachineAccept`)
perform from their `Σ'` premises. Those rows cannot be imported here: `RcicTypedMachineAccept` reaches
`RcicParRedSRTyped` through `RcicMachineSoundTyped`, and the seal cannot co-import that with
`RcicParRedSR` (the duplicated-helper collision recorded as `[DT007T_seal_collision]`). So the read-off
is restated from a Bool, which is the stronger premise form, and this module stays sealable.
Closedness of `∀ k` is reached from the single decidable equation through `lift_of_closed`.

Pins:
* `pinDefEnvUWfT_byMachine` — `pinDefEnvU` (the definition `Sort 0 : Sort 1` at `natEnvU`'s ref 4)
  rebuilt from two machine runs (each `= true` by evaluation). SECOND INSTRUMENT
  (`pin_EG010T_crosscheck_handBuilt`, `rfl`): the machine infers the hand-built universe (`Sort 2`),
  and the hand-built `pinDefEnvUWfT` IS the machine-built term with only the value derivation swapped.
  The machine's type derivation is definitionally the hand-built one. Its value derivation is a
  different term of the same judgment, so the two whole terms are not definitionally equal
  (measured).
* `machAxEnvUWfT` (an axiom `a : N`), `machThmEnvUWfT` (a theorem: the polymorphic identity at
  `Π (X : Prop), X → X`), `machOpqEnvUWfT` (an opaque `Sort 0 : Sort 1`) — all at `natEnvU`'s fresh
  ref 4, all from machine runs.

Tooth: `def bad : Prop := Type` is admitted by `main`'s legacy `EnvWf` (`envWf_badDef`,
`RcicAnnEnvBridge`). The typed machine REFUSES its value check, by evaluation
(`tooth_EG010T_badDef_refused`), so no acceptance witness exists and this route cannot admit it.

The group half (IA-028) is a WALL, reported and not attempted. No executable inductive-group
admission yields `GroupMembersT` evidence: every `IndGroupAdmitted` inhabitant is hand-built.

`closure_claim` 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Machine

open Rcic.Declarative

/-- the typed machine's state at admission's judgment form: environment `E`, level context `0`,
    empty local context, budget `k + 1`. -/
def admitState (E : ResolvedEnv) (t : TypedTask) (k : Nat) : TypedState :=
  ⟨⟨E, 0, []⟩, t, k + 1⟩

/-- the machine ACCEPTED `infer A` at admission's form with a SORT as the inferred type: a Bool read
    of the run's result. The hypothesis carries no derivation. -/
def inferSortAcceptedB (E : ResolvedEnv) (k : Nat) (A : Expr Nat) : Bool :=
  match typedRun (k + 1) (admitState E (.inferT A) k) with
  | .accepted (.inferred _ (.sort _) _) => true
  | _ => false

/-- the machine ACCEPTED `check v A` at admission's form: a Bool read of the run's result. -/
def checkAcceptedB (E : ResolvedEnv) (k : Nat) (v A : Expr Nat) : Bool :=
  match typedRun (k + 1) (admitState E (.checkT2 A v) k) with
  | .accepted (.checked _ _ _) => true
  | _ => false

/-- an accepted infer run at a sort yields the typing at that sort. The run is unfolded to its arm,
    the certifier call is split, and the derivation is the one the machine computed (the read-off
    `RM015T_infer_sound` performs, here from a Bool). -/
def sortTyping_of_inferAcceptedB {E : ResolvedEnv} {k : Nat} {A : Expr Nat}
    (h : inferSortAcceptedB E k A = true) : Σ' u, HasTyT E 0 [] A (.sort u) := by
  unfold inferSortAcceptedB typedRun typedStep admitState at h
  dsimp only at h
  cases hc : checkC E 0 (k + 1) [] A with
  | none => rw [hc] at h; simp at h
  | some p =>
      obtain ⟨T, d⟩ := p
      rw [hc] at h
      cases T with
      | sort u => exact ⟨u, d⟩
      | bvar _ => simp at h
      | const _ _ => simp at h
      | app _ _ => simp at h
      | lam _ _ => simp at h
      | pi _ _ => simp at h
      | letE _ _ _ => simp at h
      | lit _ => simp at h

/-- an accepted check run yields the typing (the read-off `RM016T_run_check_sound` performs, here
    from a Bool). -/
def typing_of_checkAcceptedB {E : ResolvedEnv} {k : Nat} {v A : Expr Nat}
    (h : checkAcceptedB E k v A = true) : HasTyT E 0 [] v A := by
  unfold checkAcceptedB typedRun typedStep admitState at h
  dsimp only at h
  cases hc : tyAtC E 0 (k + 1) [] v A with
  | none => rw [hc] at h; simp at h
  | some d => exact d

/-! ## the four singleton rows -/

/-- EG-010 typed, axiom: the machine accepts `infer A` at a sort ⟹ the `EnvWfT` successor. -/
def EG010T_axiom_accepted {E : ResolvedEnv} (hE : EnvWfT E) {r : Nat} {A : Expr Nat}
    {k : Nat} (hfresh : E.members r = none) (hA : inferSortAcceptedB E k A = true)
    (hcl : lift 0 1 A = A) (hlvl : exprLevelsBounded 0 A = true) :
    EnvWfT (extendEnv E r ⟨.axiomM, 0, A, none⟩) :=
  .axiom E r A (sortTyping_of_inferAcceptedB hA).1 hE hfresh (sortTyping_of_inferAcceptedB hA).2
    (fun c => lift_of_closed A hcl c 1) hlvl

/-- EG-010 typed, definition: the machine accepts `infer A` at a sort and `check v A` ⟹ the `EnvWfT`
    successor. -/
def EG010T_definition_accepted {E : ResolvedEnv} (hE : EnvWfT E) {r : Nat} {A v : Expr Nat}
    {k k' : Nat} (hfresh : E.members r = none) (hA : inferSortAcceptedB E k A = true)
    (hv : checkAcceptedB E k' v A = true)
    (hclA : lift 0 1 A = A) (hclv : lift 0 1 v = v)
    (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true) :
    EnvWfT (extendEnv E r ⟨.definitionM, 0, A, some v⟩) :=
  .definition E r A v (sortTyping_of_inferAcceptedB hA).1 hE hfresh (sortTyping_of_inferAcceptedB hA).2
    (typing_of_checkAcceptedB hv)
    (fun c => lift_of_closed A hclA c 1) (fun c => lift_of_closed v hclv c 1) hlvlA hlvlv

/-- EG-010 typed, theorem: the machine accepts `check A (Sort 0)` (the type is a Prop) and
    `check p A` ⟹ the `EnvWfT` successor. -/
def EG010T_theorem_accepted {E : ResolvedEnv} (hE : EnvWfT E) {r : Nat} {A p : Expr Nat}
    {k k' : Nat} (hfresh : E.members r = none) (hA : checkAcceptedB E k A (.sort .zero) = true)
    (hp : checkAcceptedB E k' p A = true)
    (hclA : lift 0 1 A = A) (hclp : lift 0 1 p = p)
    (hlvlA : exprLevelsBounded 0 A = true) (hlvlp : exprLevelsBounded 0 p = true) :
    EnvWfT (extendEnv E r ⟨.theoremM, 0, A, some p⟩) :=
  .thm E r A p hE hfresh (typing_of_checkAcceptedB hA) (typing_of_checkAcceptedB hp)
    (fun c => lift_of_closed A hclA c 1) (fun c => lift_of_closed p hclp c 1) hlvlA hlvlp

/-- EG-010 typed, opaque: as the definition, at the opaque class. -/
def EG010T_opaque_accepted {E : ResolvedEnv} (hE : EnvWfT E) {r : Nat} {A v : Expr Nat}
    {k k' : Nat} (hfresh : E.members r = none) (hA : inferSortAcceptedB E k A = true)
    (hv : checkAcceptedB E k' v A = true)
    (hclA : lift 0 1 A = A) (hclv : lift 0 1 v = v)
    (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true) :
    EnvWfT (extendEnv E r ⟨.opaqueM, 0, A, some v⟩) :=
  .opaque E r A v (sortTyping_of_inferAcceptedB hA).1 hE hfresh (sortTyping_of_inferAcceptedB hA).2
    (typing_of_checkAcceptedB hv)
    (fun c => lift_of_closed A hclA c 1) (fun c => lift_of_closed v hclv c 1) hlvlA hlvlv

/-! ## pins: machine runs at `natEnvU` -/

/-- RUN: `infer (Sort 1)` at `natEnvU` is accepted at a sort (by evaluation). -/
theorem pinRunInferSort1 : inferSortAcceptedB natEnvU 1 (.sort (.succ .zero)) = true := rfl

/-- RUN: `check (Sort 0) (Sort 1)` at `natEnvU` is accepted (by evaluation). -/
theorem pinRunCheckSort0 : checkAcceptedB natEnvU 1 (.sort .zero) (.sort (.succ .zero)) = true := rfl

/-- PIN (EG-010T, definition): `pinDefEnvU` rebuilt from the two machine runs. -/
def pinDefEnvUWfT_byMachine : EnvWfT pinDefEnvU :=
  EG010T_definition_accepted natEnvUWfT pinDefEnvU_fresh pinRunInferSort1 pinRunCheckSort0
    rfl rfl rfl rfl

/-- SECOND INSTRUMENT, against the hand-built `pinDefEnvUWfT`. The universe the machine infers for the
    type is the hand-built one (`Sort 2`), and the type derivation the machine computed is
    definitionally the hand-built `HasTyT.sort [] 1`. So the hand-built term IS the machine-built one
    with only the value derivation swapped (`rfl`). The machine's value derivation is a different term
    of the same judgment `Sort 0 : Sort 1` (the check arm returns its own derivation), so the two
    whole `EnvWfT` terms are not definitionally equal; measured, and recorded in the PR. -/
theorem pin_EG010T_crosscheck_handBuilt :
    (sortTyping_of_inferAcceptedB pinRunInferSort1).1 = .succ (.succ .zero) ∧
    EnvWfT.definition natEnvU 4 (.sort (.succ .zero)) (.sort .zero) (.succ (.succ .zero))
      natEnvUWfT pinDefEnvU_fresh (sortTyping_of_inferAcceptedB pinRunInferSort1).2
      (HasTyT.sort [] .zero) (fun _ => rfl) (fun _ => rfl) rfl rfl = pinDefEnvUWfT :=
  ⟨rfl, rfl⟩

/-- RUN: `infer N` (`natEnvU`'s family) is accepted at a sort. -/
theorem pinRunInferNat : inferSortAcceptedB natEnvU 1 (.const 0 []) = true := rfl

/-- PIN (EG-010T, axiom): `axiom a : N` at `natEnvU`'s fresh ref 4, from a machine run. -/
def machAxEnvUWfT : EnvWfT (extendEnv natEnvU 4 ⟨.axiomM, 0, .const 0 [], none⟩) :=
  EG010T_axiom_accepted natEnvUWfT pinDefEnvU_fresh pinRunInferNat rfl rfl

/-- `Π (X : Prop), X → X`. -/
def machPropId : Expr Nat := .pi (.sort .zero) (.pi (.bvar 0) (.bvar 1))

/-- `λ (X : Prop), λ (x : X), x`. -/
def machPropIdPf : Expr Nat := .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))

/-- RUN: `check (Π (X : Prop), X → X) Prop` at `natEnvU` is accepted. The type is a Prop by the
    impredicative `imax`. -/
theorem pinRunCheckPropId : checkAcceptedB natEnvU 1 machPropId (.sort .zero) = true := rfl

/-- RUN: `check (λ X x, x) (Π (X : Prop), X → X)` at `natEnvU` is accepted. -/
theorem pinRunCheckPropIdPf : checkAcceptedB natEnvU 1 machPropIdPf machPropId = true := rfl

/-- PIN (EG-010T, theorem): `theorem id : Π (X : Prop), X → X := λ X x, x` at `natEnvU`'s fresh ref
    4, from two machine runs. -/
def machThmEnvUWfT : EnvWfT (extendEnv natEnvU 4 ⟨.theoremM, 0, machPropId, some machPropIdPf⟩) :=
  EG010T_theorem_accepted natEnvUWfT pinDefEnvU_fresh pinRunCheckPropId pinRunCheckPropIdPf
    rfl rfl rfl rfl

/-- PIN (EG-010T, opaque): `opaque o : Sort 1 := Sort 0` at `natEnvU`'s fresh ref 4, from the same
    two machine runs as the definition. -/
def machOpqEnvUWfT :
    EnvWfT (extendEnv natEnvU 4 ⟨.opaqueM, 0, .sort (.succ .zero), some (.sort .zero)⟩) :=
  EG010T_opaque_accepted natEnvUWfT pinDefEnvU_fresh pinRunInferSort1 pinRunCheckSort0
    rfl rfl rfl rfl

/-! ## tooth: the legacy-admitted `def bad : Prop := Type` is refused by the machine -/

/-- TOOTH: `def bad : Prop := Type` IS admitted by the legacy `EnvWf` (`envWf_badDef`,
    `RcicAnnEnvBridge`). The typed machine REFUSES its value check at the empty environment, by
    evaluation, so `EG010T_definition_accepted`'s acceptance premise is false for it and this route
    cannot admit it. -/
theorem tooth_EG010T_badDef_refused :
    Nonempty (EnvWf Ann.badDefEnv 0) ∧
    typedRun 2 (admitState emptyEnv (.checkT2 (.sort .zero) (.sort (.succ .zero))) 1) =
      .refused "[rcic_typed_check_refused]" ∧
    checkAcceptedB emptyEnv 1 (.sort (.succ .zero)) (.sort .zero) = false :=
  ⟨⟨Ann.envWf_badDef 0⟩, rfl, rfl⟩

end Rcic.Machine

#print axioms Rcic.Machine.admitState
#print axioms Rcic.Machine.inferSortAcceptedB
#print axioms Rcic.Machine.checkAcceptedB
#print axioms Rcic.Machine.sortTyping_of_inferAcceptedB
#print axioms Rcic.Machine.typing_of_checkAcceptedB
#print axioms Rcic.Machine.EG010T_axiom_accepted
#print axioms Rcic.Machine.EG010T_definition_accepted
#print axioms Rcic.Machine.EG010T_theorem_accepted
#print axioms Rcic.Machine.EG010T_opaque_accepted
#print axioms Rcic.Machine.pinRunInferSort1
#print axioms Rcic.Machine.pinRunCheckSort0
#print axioms Rcic.Machine.pinDefEnvUWfT_byMachine
#print axioms Rcic.Machine.pin_EG010T_crosscheck_handBuilt
#print axioms Rcic.Machine.pinRunInferNat
#print axioms Rcic.Machine.machAxEnvUWfT
#print axioms Rcic.Machine.pinRunCheckPropId
#print axioms Rcic.Machine.pinRunCheckPropIdPf
#print axioms Rcic.Machine.machThmEnvUWfT
#print axioms Rcic.Machine.machOpqEnvUWfT
#print axioms Rcic.Machine.tooth_EG010T_badDef_refused
