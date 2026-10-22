import rcic.RcicAnnLR3StratifiedCandidates
import rcic.RcicAnnLR3NoneUniverseBoundary
import rcic.RcicAnnLR3EnvironmentEval

/-!
# Native-denotable typed neutral member values

These values use the actual native tagged syntax, including its partial
observations. They are not identified with the sparse legacy reification.
Their exact level, definedness and bottom observation are supplied. At a
defined level the explicit retained code and its universe membership are
constructed; the tagged undefined fragment is supplied separately.
No complete source CodeSystem or general member telescope is asserted.
`closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.Ann.LR3.NativeMemberValues

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedPER TypedStatements

def term (k : Option Nat) (name : Nat) : Expr Nat := taggedTerm k (.const name [])

def value (k : Option Nat) (name : Nat) : Value := denI EnvI.bot (term k name)

theorem environment (ρ : EnvI) (k : Option Nat) (name : Nat) :
    ValueEq (denI ρ (term k name)) (value k name) :=
  approxI_app_rel
    (approxI_app_rel (FunctionEval.constant_environment ρ EnvI.bot 10 [])
      (FunctionEval.constant_environment ρ EnvI.bot (levelRef k) []))
    (FunctionEval.constant_environment ρ EnvI.bot name [])

theorem value_level (k : Option Nat) (name : Nat) : SortMember k (value k name) :=
  tagged_member EnvI.bot k (.const name [])

theorem value_defined (k : Option Nat) (name : Nat) : TypeDefined (value k name) :=
  tagged_defined EnvI.bot k (.const name [])

theorem value_bot (k : Option Nat) (name : Nat) : value k name .bot := .bot _ _

/-- A visible partial tag distinguishes native denotation from the
sparse old value. The new representation is used explicitly. -/
theorem value_not_legacy (k : Option Nat) (name : Nat) :
    ¬ ValueEq (value k name) (NeutralCodes.neutralTypeValue k name) := by
  intro h
  have hc : value k name (.spine 10 [.bot, .bot]) :=
    approxI_famApp 10 [] (.cons (.bot _ _) (.cons (.bot _ _) .nil))
  have hs := (h _).mp hc
  simp [NeutralCodes.neutralTypeValue, NeutralCodes.fullTag] at hs

/-- Actual retained codes at every defined level. No relation is selected
from a proposition and no reflected membership is an input. -/
def neutralCode : (k : Nat) → Nat → StratifiedCandidates.Code k
  | 0, name =>
      ⟨value (some 0) name, CandidateUniverse.predicateCandidate (fun _ => False),
        value_level (some 0) name, value_defined (some 0) name⟩
  | k + 1, name => StratifiedCandidates.predicative k (value (some (k + 1)) name)
      (value_level (some (k + 1)) name) (value_defined (some (k + 1)) name)
      (fun _ _ => False) ⟨False.elim, fun h _ => False.elim h⟩

theorem neutralCode_value (k name : Nat) :
    (StratifiedCandidates.view k (neutralCode k name)).value = value (some k) name := by
  cases k <;> rfl

theorem neutralCode_bot (k name : Nat) :
    (StratifiedCandidates.view k (neutralCode k name)).value .bot := by
  rw [neutralCode_value]
  exact value_bot _ _

theorem universe_member (k name : Nat) :
    (StratifiedCandidates.universeCode k).relation
      (StratifiedCandidates.encode k (neutralCode k name))
      (StratifiedCandidates.encode k (neutralCode k name)) :=
  StratifiedCandidates.universe_member _ _

theorem universe_erasure (k name : Nat) :
    StratifiedCandidates.erase (k + 1)
      (StratifiedCandidates.encode k (neutralCode k name)) = value (some k) name :=
  neutralCode_value k name

theorem none_code (name : Nat) :
    NoneUniverseBoundary.NoneCode (value none name) (NoneUniverseBoundary.TaggedChaos none) :=
  ⟨value_level none name, value_defined none name, fun _ _ => Iff.rfl⟩

theorem none_member (name : Nat) :
    Member (NoneUniverseBoundary.TaggedChaos none) (value none name) :=
  ⟨⟨value_level none name, value_defined none name⟩,
    ⟨value_level none name, value_defined none name⟩⟩

end Rcic.Declarative.Ann.LR3.NativeMemberValues
