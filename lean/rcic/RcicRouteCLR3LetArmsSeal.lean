import Lean
import rcic.RcicAnnLR3PairedLetArms

/-!
Seal for the glm-sr1 let-substitution paired arms: every public declaration
of `rcic.RcicAnnLR3PairedLetArms` is checked to depend on no axioms outside
`{propext, Quot.sound}`. `collectAxioms` traverses all dependencies of every
public root, including private proof dependencies. closure_claim = 0.
-/

set_option maxRecDepth 65536
set_option maxHeartbeats 0

-- BEGIN GLM_SR1_LETARMS_ROOTS
private def routeCLR3LetArmsModules : Array Lean.Name := #[
  `rcic.RcicAnnLR3PairedLetArms
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  let mut total := 0
  for mod in routeCLR3LetArmsModules do
    let some midx := env.getModuleIdx? mod
      | throwError "RouteCLR3LetArms: missing module {mod}"
    let mut count := 0
    for (root, _) in env.constants.toList do
      if env.getModuleIdxFor? root == some midx && !root.isInternal then
        let axioms ← collectAxioms root
        let forbidden := axioms.filter (fun ax => !allowed.contains ax)
        if !forbidden.isEmpty then
          throwError "RouteCLR3LetArms: {root} has forbidden axioms {forbidden}"
        let item := Json.mkObj [
          ("module", toJson mod.toString),
          ("name", toJson root.toString),
          ("axioms", toJson (axioms.map Name.toString))]
        logInfo m!"CHECKED_ROOT {item.compress}"
        count := count + 1
        total := total + 1
    if count == 0 then
      throwError "RouteCLR3LetArms: no public declarations in {mod}"
    logInfo m!"CHECKED_MODULE {mod} {count}"
  logInfo m!"RouteCLR3LetArms: {total} public declarations checked"
-- END GLM_SR1_LETARMS_ROOTS

open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms approxI_sortTerm_env
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms denI_sortTerm_env
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms denoteImage
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms denoteImage_sort
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms denoteSemantics
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms denote_instantiate0_cons
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms denote_letE_cons
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms neutral_valueEq
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms neutral_extensional
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms proofMember_valueEq
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms el_valueEq
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms code_valueEq
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms codeElement_valueEq
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms ty_letE_supplied
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms conv_zeta_supplied
open Rcic.Declarative.Ann.LR3.PairedLetRoute in
#print axioms conv_letE_supplied
