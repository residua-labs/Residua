import Lean
import rcic.RcicF3PiProducerAttack

/-! All public declarations of the indexed semantic producer and its fixtures.
Only propext and Quot.sound are permitted. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PendAProducerSeal
open Lean Elab Command

def sealedTheorems : List Name := [
  ``Rcic.F3.PSet.RecSig,
  ``Rcic.F3.PSet.RecSig.Field,
  ``Rcic.F3.PSet.RecSig.Sh,
  ``Rcic.F3.PSet.RecSig.casesOn,
  ``Rcic.F3.PSet.RecSig.code,
  ``Rcic.F3.PSet.RecSig.code_congr,
  ``Rcic.F3.PSet.RecSig.code_tag,
  ``Rcic.F3.PSet.RecSig.depth,
  ``Rcic.F3.PSet.RecSig.mk,
  ``Rcic.F3.PSet.RecSig.mk.inj,
  ``Rcic.F3.PSet.RecSig.mk.injEq,
  ``Rcic.F3.PSet.RecSig.mk.sizeOf_spec,
  ``Rcic.F3.PSet.RecSig.noConfusion,
  ``Rcic.F3.PSet.RecSig.noConfusionType,
  ``Rcic.F3.PSet.RecSig.out,
  ``Rcic.F3.PSet.RecSig.rec,
  ``Rcic.F3.PSet.RecSig.recOn,
  ``Rcic.F3.PSet.RecSig.tag,
  ``Rcic.F3.PSet.RecSig.tag_congr,
  ``Rcic.F3.PSet.RecSig.tel,
  ``Rcic.F3.PSet.RecSig.toPiSig,
  ``Rcic.F3.PSet.RecSig.toPiSig.proof_1,
  ``Rcic.F3.PSet.RecSig.toPiSig.proof_2,
  ``Rcic.F3.PSet.RecSig.family,
  ``Rcic.F3.PSet.RecSig.Args,
  ``Rcic.F3.PSet.RecSig.Args.casesOn,
  ``Rcic.F3.PSet.RecSig.Args.indexed,
  ``Rcic.F3.PSet.RecSig.Args.mk,
  ``Rcic.F3.PSet.RecSig.Args.mk.inj,
  ``Rcic.F3.PSet.RecSig.Args.mk.injEq,
  ``Rcic.F3.PSet.RecSig.Args.mk.sizeOf_spec,
  ``Rcic.F3.PSet.RecSig.Args.noConfusion,
  ``Rcic.F3.PSet.RecSig.Args.noConfusionType,
  ``Rcic.F3.PSet.RecSig.Args.rec,
  ``Rcic.F3.PSet.RecSig.Args.recOn,
  ``Rcic.F3.PSet.RecSig.Args.trees,
  ``Rcic.F3.PSet.RecSig.Args.valid,
  ``Rcic.F3.PSet.RecSig.Args.values,
  ``Rcic.F3.PSet.RecSig.Args.related,
  ``Rcic.F3.PSet.RecSig.Args.values.eq_1,
  ``Rcic.F3.PSet.RecSig.produce,
  ``Rcic.F3.PSet.RecSig.toPiSig.eq_1,
  ``Rcic.F3.PSet.PiSig.induction_mem,
  ``Rcic.F3.PSet.PiSig.induction_mem.match_1,
  ``Rcic.F3.PSet.RecSig.produce_of_mem,
  ``Rcic.F3.PSet.RecSig.produce_of_mem.match_1,
  ``Rcic.F3.PSet.PiProducerFixture.accSig,
  ``Rcic.F3.PSet.PiProducerFixture.accSig.proof_1,
  ``Rcic.F3.PSet.PiProducerFixture.accSig.proof_2,
  ``Rcic.F3.PSet.PiProducerFixture.accSig.proof_3,
  ``Rcic.F3.PSet.PiProducerFixture.accTree,
  ``Rcic.F3.PSet.PiProducerFixture.accTree.proof_1,
  ``Rcic.F3.PSet.PiProducerFixture.accTree_index,
  ``Rcic.F3.PSet.PiProducerFixture.accTree_valid,
  ``Rcic.F3.PSet.PiProducerFixture.accArgs,
  ``Rcic.F3.PSet.PiProducerFixture.accArgs.proof_1,
  ``Rcic.F3.PSet.PiProducerFixture.accArgs.proof_2,
  ``Rcic.F3.PSet.PiProducerFixture.accArgs.proof_3,
  ``Rcic.F3.PSet.PiProducerFixture.acc_produced,
  ``Rcic.F3.PSet.PiProducerFixture.natLt_produced,
  ``Rcic.F3.PSet.PiProducerFixture.wSig,
  ``Rcic.F3.PSet.PiProducerFixture.wSig.match_1,
  ``Rcic.F3.PSet.PiProducerFixture.wSig.match_2,
  ``Rcic.F3.PSet.PiProducerFixture.wSig.proof_1,
  ``Rcic.F3.PSet.PiProducerFixture.wTree,
  ``Rcic.F3.PSet.PiProducerFixture.wTree.match_1,
  ``Rcic.F3.PSet.PiProducerFixture.wTree_decode,
  ``Rcic.F3.PSet.PiProducerFixture.wTree_valid,
  ``Rcic.F3.PSet.PiProducerFixture.wArgs,
  ``Rcic.F3.PSet.PiProducerFixture.wArgs.proof_1,
  ``Rcic.F3.PSet.PiProducerFixture.w_produced,
  ``Rcic.F3.PSet.PiProducerFixture.wrong_acc_index_refused,
  ``Rcic.F3.PSet.PiProducerAttack.deepField,
  ``Rcic.F3.PSet.PiProducerAttack.deepField.match_1,
  ``Rcic.F3.PSet.PiProducerAttack.deepSig,
  ``Rcic.F3.PSet.PiProducerAttack.deepSig.match_1,
  ``Rcic.F3.PSet.PiProducerAttack.deepSig.match_2,
  ``Rcic.F3.PSet.PiProducerAttack.deepSig.proof_1,
  ``Rcic.F3.PSet.PiProducerAttack.deepSig.proof_2,
  ``Rcic.F3.PSet.PiProducerAttack.deepSig.proof_3,
  ``Rcic.F3.PSet.PiProducerAttack.deepLeaf,
  ``Rcic.F3.PSet.PiProducerAttack.deepLeaf_valid,
  ``Rcic.F3.PSet.PiProducerAttack.deepArgs,
  ``Rcic.F3.PSet.PiProducerAttack.deepArgs.proof_1,
  ``Rcic.F3.PSet.PiProducerAttack.deepArgs.proof_2,
  ``Rcic.F3.PSet.PiProducerAttack.deep_produced,
  ``Rcic.F3.PSet.PiProducerAttack.hidden_w_produced,
  ``Rcic.F3.PSet.PiProducerAttack.shifted_acc_produced
]
def allowedAxioms : List Name := [``propext, ``Quot.sound]
run_cmd do
  let env ← getEnv
  for t in sealedTheorems do
    unless env.contains t do
      throwError "[penda_producer_seal] {t} is not declared"
    let (_, s) := ((CollectAxioms.collect t).run env).run {}
    for ax in s.axioms do
      unless allowedAxioms.contains ax do
        throwError "[penda_producer_seal] {t} depends on {ax}"
  logInfo m!"[penda_producer_seal] {sealedTheorems.length} declarations sealed"
end Rcic.F3.PendAProducerSeal
