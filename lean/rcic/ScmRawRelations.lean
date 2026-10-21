/-
First-order (raw-layer) relations of the K2 machines — NOT the 06 §18 wire
execution predicates (#6029 K2 HOLD item 2).

These relations read the intrinsic machine through its erasure to the
first-order records of `ScmMachineRaw` (the carrier `rcic-scm-core`'s
`{ctl, k}` configurations) and through the core-wire value / program codec of
`ScmWire`:
  CoreWireValueAt T bytes := ∃ v : CoreVal T, encVal v.erase = bytes
                             (a `CoreTy`, not a `BoundCoreType`)
  CoreWireProgramAt p bytes := the core wire accepts the bytes (not a bound
                             object)
  RawConfigAt / RawOutcomeAt / RawStepAt / RawRunsAt / RawEntryRunsAt
                          := over `Raw.Config` records, not canonical bytes
They are the first-order half that `ScmSim` / `ScmBridge` simulate against.

NOT TRANSCRIBED (M-002b): 06 §18's `ProgramAt` `ValueAt` `ConfigAt` `OutcomeAt`
`SCMStepAt` `SCMRunsAt` `EntryRunsAt` ("R-CIC propositions over bound refs and
canonical bytes", 06:402), and §18's `BoundCoreType` / `CanonicalCoreTypeAt`,
`SemanticValue`, `BoundCoreProgram`. 06:402 states them over bound refs and
canonical bytes; the encoding is decided (#6029 K2 HOLD: the §17 core-wire
grammar family for values, types, configurations and outcomes), but no carrier
yet decides bound canonical core-wire objects (values, types, outcomes,
configurations with §13 frame-chain typing, bound under 01 §6). Per M-002b they
are mechanized only after that carrier exists: #6029 K3b (carrier) then K3c
(the predicates and the §19 bridge, SCM-016/017/018).
-/
import rcic.ScmWire
import rcic.ScmMachine

namespace Rcic.Scm.RawRel
open Rcic.Scm Rcic.Scm.Wire

def CoreWireValueAt (T : CoreTy) (bytes : String) : Prop := ∃ v : CoreVal T, encVal v.erase = bytes

def CoreWireProgramAt (profile bytes : String) : Prop :=
  ∃ fuel : Int, (scmWire 0 fuel bytes ⟨"", ⟨[], [], [], 0⟩⟩ profile).ok = 1

def RawConfigAt (S : Sig) (T : CoreTy) (r : Raw.Config) : Prop := ∃ c : Config S T, c.erase = r

def finalErase {S : Sig} {T : CoreTy} : Final S T → Int × Val × String
  | .returned v => (1, v.erase, "")
  | .raised r _ v => (2, v.erase, r)

def RawOutcomeAt (S : Sig) (T : CoreTy) (kind : Int) (v : Val) (r : String) : Prop :=
  ∃ o : Final S T, finalErase o = (kind, v, r)

def RawStepAt {S : Sig} {T : CoreTy} (prog : Bodies S S.fns) (r r' : Raw.Config) : Prop :=
  ∃ c c' : Config S T, c.erase = r ∧ c'.erase = r' ∧ SCMStep prog c c'

def RawRunsAt {S : Sig} {T : CoreTy} (prog : Bodies S S.fns) (n : Nat) (r r' : Raw.Config) : Prop :=
  ∃ c c' : Config S T, c.erase = r ∧ c'.erase = r' ∧ SCMRuns prog n c c'

def RawEntryRunsAt (fuel : Int) (p : RawProg) (args : List Val) (n : Int) (out : Raw.Out) : Prop :=
  entryI fuel p args n = out

/-! ## Instance witnesses (M-005) -/

namespace Witness
def five : CoreVal .i64 := .i64V 5 ⟨by decide, by decide⟩
def S0 : Sig := ⟨[], [], []⟩
def c0 : Config S0 .i64 := ⟨.i64, .evalC .nil (.lit five), .nil⟩
def c1 : Config S0 .i64 := ⟨.i64, .retC five, .nil⟩

example : CoreWireValueAt .i64 "I5;" := ⟨five, rfl⟩
example : RawConfigAt S0 .i64 ⟨.evalC [] (.lit (.i 5) .i64), []⟩ := ⟨c0, rfl⟩
example : RawOutcomeAt S0 .i64 1 (.i 5) "" := ⟨.returned five, rfl⟩
example : SCMStep (S := S0) .nil c0 c1 := ⟨rfl, trivial⟩
example : RawStepAt (S := S0) (T := .i64) .nil ⟨.evalC [] (.lit (.i 5) .i64), []⟩ ⟨.retC (.i 5), []⟩ :=
  ⟨c0, c1, rfl, rfl, ⟨rfl, trivial⟩⟩
example : RawRunsAt (S := S0) (T := .i64) .nil 1 ⟨.evalC [] (.lit (.i 5) .i64), []⟩ ⟨.retC (.i 5), []⟩ :=
  ⟨c0, c1, rfl, rfl, .step rfl (.refl c1)⟩
-- `ProgramAt` at the wire corpus' small program (row 2/3 bytes), decided by evaluation.
#guard (scmWire 0 256 "M10:SCM-Core-00;0;1;1;ii10;0;" ⟨"", ⟨[], [], [], 0⟩⟩ "SCM-Core-0").ok = 1
end Witness

end Rcic.Scm.RawRel
