import rcic.RcicAnnLR3EqTracer
import rcic.RcicAnnLR3SemanticMemberAdmissionReadback

/-!
# Arm 17 (Conv ι) on the Target, for the AnySort Eq environment

The skeleton's Target is `annSemantics C (view E) (hook hE F)`. Take the
fallback family hook `F := iotaHook E`. The admission reader reads no product
as a universe (`read_pi_none`), so for constructors and recursors whose types
are products (`CtorRecPi`) the admission hook falls back to `iotaHook E`.
The view keeps their classes, so the Target routes them to the native
recursor terms (`routes_target`). The landed recursor law then gives
`Conv_iota` and `Conv_structIota` on the Target for every code system
(`target_conv_iota`, `target_conv_structIota`), given first-order arity.

For the admitted AnySort Eq group (`EqLargeFixture.env`) both side
conditions hold (`eq_ctorRecPi`, `EqTracer.eq_firstOrderArity`). Hence
`eq_target_conv_iota`: every ι step there, including J at a motive in any
sort, is sound in the Target, for every code system and every admission
derivation (`eq_admitted` inhabits the latter). Since ι is a conversion
rule, J's typing (the `Ty` arms and the motive's membership) is a separate
obligation; `EqTracer.j_retype` is its candidate-design core.

Not claimed: arm 17 for environments outside these side conditions, or the
native-to-annotated lift for this environment. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EqTargetIota

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open IotaRecursor AdmissionUniverseReadback
open EnvironmentEval (definitionBody rigidTerm denote_rigid)

/-- The admission reader reads no product as a universe. -/
theorem read_pi_none {I : IotaIfaceA} {E : ResolvedEnvA} (hE : EnvWfA I E) (ν : Valuation)
    (A : ExprA) (u : Level) (B : ExprA) (v : Level) :
    (readerOf hE).read ν (.pi A u B v) = none := by
  induction hE <;>
    simp_all [readerOf, Reader.weaken, Reader.addTransparent, addRead, Reader.empty, emptyRead]

/-- Every constructor and recursor type is a product at every level
instantiation. -/
def CtorRecPi (E : ResolvedEnvA) : Prop :=
  ∀ (r : Nat) (m : CheckedMemberA), E.members r = some m →
    (m.mclass = .constructorM ∨ m.mclass = .recursorM) →
    ∀ ls, ∃ A u B v, instantiateLevelsA ls m.mtypeA = .pi A u B v

/-- The Target's view and admission hook route constructors and recursors
to the native recursor terms whenever the fallback family hook does. -/
theorem routes_target_of {I : IotaIfaceA} {E : ResolvedEnvA} (hE : EnvWfA I E)
    (hpi : CtorRecPi E) (F : EnvironmentEval.FamilySyntax)
    (hF : ∀ ν r ls (m : CheckedMemberA), E.members r = some m →
      (m.mclass = .constructorM ∨ m.mclass = .recursorM) → F ν r ls m = iotaTerm E r) :
    Routes E (SemanticMemberEval.view E) (hook hE F) := by
  intro ν ρ r ls m hm hc
  have hbody : definitionBody (SemanticMemberEval.view E) r ls = none := by
    rw [SemanticMemberEval.definitionBody_preserved]
    rcases hc with hc | hc <;> simp [definitionBody, hm, hc, transparent]
  obtain ⟨A, u, B, v, hT⟩ := hpi r m hm hc ls
  have hread : readAdmitted hE ν (instantiateLevelsA ls m.mtypeA) = none := by
    rw [hT]
    exact read_pi_none hE ν A u B v
  have hv : (SemanticMemberEval.view E).members r = some (SemanticMemberEval.route m) := by
    simp [SemanticMemberEval.view, hm]
  have hrigid : rigidTerm (SemanticMemberEval.view E) (hook hE F) ν r ls = iotaTerm E r := by
    rcases hc with hc | hc <;>
      simp [rigidTerm, hv, SemanticMemberEval.route, hc, hook, hm, hread, hF ν r ls m hm (by simp [hc])]
  rw [NeutralCodes.valueEq_eq (denote_rigid hbody _ ν ρ), hrigid]

/-- The Target's view and admission hook route constructors and recursors
to the native recursor terms when the fallback family hook is `iotaHook E`. -/
theorem routes_target {I : IotaIfaceA} {E : ResolvedEnvA} (hE : EnvWfA I E)
    (hpi : CtorRecPi E) :
    Routes E (SemanticMemberEval.view E) (hook hE (iotaHook E)) :=
  routes_target_of hE hpi (iotaHook E) (fun _ _ _ _ _ _ => rfl)

/-- Conv ι on the Target `annSemantics C (view E) (hook hE (iotaHook E))`. -/
theorem target_conv_iota (C : CodeSystem) {E : ResolvedEnvA}
    (hE : EnvWfA (iotaIfaceA E) E) (hpi : CtorRecPi E) (harity : FirstOrderArity E) (n : Nat) :
    PairedArms.Conv_iota
      (EnvironmentEval.annSemantics C (SemanticMemberEval.view E) (hook hE (iotaHook E)))
      E (iotaIfaceA E) n :=
  conv_iota_supplied C (routes_target hE hpi) harity n

theorem target_conv_structIota (C : CodeSystem) {E : ResolvedEnvA}
    (hE : EnvWfA (iotaIfaceA E) E) (hpi : CtorRecPi E) (harity : FirstOrderArity E) (n : Nat) :
    PairedArms.Conv_structIota
      (EnvironmentEval.annSemantics C (SemanticMemberEval.view E) (hook hE (iotaHook E)))
      E (iotaIfaceA E) n :=
  conv_structIota_supplied C (routes_target hE hpi) harity n

/-! ## The AnySort Eq environment -/

theorem eq_ctorRecPi : CtorRecPi EqLargeFixture.env := by
  intro r m hm hc ls
  rcases EqTracer.eq_members hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact absurd hc (by decide)
  · exact ⟨_, _, _, _, rfl⟩
  · exact ⟨_, _, _, _, rfl⟩

/-- **Arm 17 on the Target for AnySort Eq.** Every ι step of the admitted
AnySort Eq environment, including J at a motive in any sort, is sound in the
Target model, for every code system and every admission derivation. -/
theorem eq_target_conv_iota (C : CodeSystem)
    (hE : EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env) (n : Nat) :
    PairedArms.Conv_iota
      (EnvironmentEval.annSemantics C (SemanticMemberEval.view EqLargeFixture.env)
        (hook hE (iotaHook EqLargeFixture.env)))
      EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) n :=
  target_conv_iota C hE eq_ctorRecPi EqTracer.eq_firstOrderArity n

theorem eq_target_conv_structIota (C : CodeSystem)
    (hE : EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env) (n : Nat) :
    PairedArms.Conv_structIota
      (EnvironmentEval.annSemantics C (SemanticMemberEval.view EqLargeFixture.env)
        (hook hE (iotaHook EqLargeFixture.env)))
      EqLargeFixture.env (iotaIfaceA EqLargeFixture.env) n :=
  target_conv_structIota C hE eq_ctorRecPi EqTracer.eq_firstOrderArity n

/-- The admission premise is inhabited. -/
theorem eq_admitted : Nonempty (EnvWfA (iotaIfaceA EqLargeFixture.env) EqLargeFixture.env) :=
  EqLargeFixture.wf

end Rcic.Declarative.Ann.LR3.EqTargetIota
