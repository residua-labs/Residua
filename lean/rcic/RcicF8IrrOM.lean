import rcic.RcicF8EvPar
import rcic.RcicF8OM23

/-!
# J(irr) in the landed O-M contract
This is a terminal base-case adapter to the EXISTING DTile/OM2/OM3_edge,
not a replacement contract. Its step materializes the single owner EvPar
constructor. Every site is answered, and the three original children are
DM-below the exact original irr node. No general J recursion is supplied.
closure_claim=0.
-/
namespace Rcic.Declarative.F8Measure
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P p q : Expr Nat}

def literalIrrTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    DTile [Jd.cv (.irr Γ P p q hP hp hq)] where
  X := [Jd.cv (.irr Γ P p q hP hp hq)]
  step := (literalIrrProducer hP hp hq).val hcl hinst
  status := statusOfAnswered
    (R := [Jd.cv (.irr Γ P p q hP hp hq)])
    (EvPar.proofIndexRequests hcl hinst (literalIrrPayload hP hp hq))
    (EvPar.proofIndexAnswers hcl hinst (literalIrrPayload hP hp hq))
  om2 := om2_of_answered [Jd.cv (.irr Γ P p q hP hp hq)]
    (EvPar.proofIndexRequests hcl hinst (literalIrrPayload hP hp hq))
    (EvPar.proofIndexAnswers hcl hinst (literalIrrPayload hP hp hq))

theorem literalIrrTile_exact (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    (literalIrrTile hcl hinst hP hp hq).step =
      (literalIrrProducer hP hp hq).val hcl hinst := rfl

theorem literalIrrTile_edge (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    OM3_edge [Jd.cv (.irr Γ P p q hP hp hq)] (literalIrrProducer hP hp hq).leaves :=
  literalIrrProducer_dm hP hp hq

theorem literalIrrTile_om2 (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    OM2 (literalIrrTile hcl hinst hP hp hq).X
      (literalIrrTile hcl hinst hP hp hq).step
      (literalIrrTile hcl hinst hP hp hq).status :=
  (literalIrrTile hcl hinst hP hp hq).om2
end Rcic.Declarative.F8Measure
