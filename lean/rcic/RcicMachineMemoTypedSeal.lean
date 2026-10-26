import rcic.RcicMachineMemoTyped

/-! # RcicMachineMemoTypedSeal — bounded seal of the memoized typed cert machine

Every theorem of `RcicMachineMemoTyped`; axioms within {propext, Quot.sound}. The same names
are in `RcicFoundationSeal`'s DEVIN KMEMO TYPED SEALED ROOTS block. closure_claim 0. -/

#print axioms Rcic.Machine.TMemo.TTable.empty_sound
#print axioms Rcic.Machine.TMemo.TTable.bucket_sound
#print axioms Rcic.Machine.TMemo.TTable.push_sound
#print axioms Rcic.Machine.TMemo.Agrees.pure'
#print axioms Rcic.Machine.TMemo.Agrees.bind
#print axioms Rcic.Machine.TMemo.Agrees.of_eq
#print axioms Rcic.Machine.TMemo.findTy_sound
#print axioms Rcic.Machine.TMemo.findAt_sound
#print axioms Rcic.Machine.TMemo.memoTy_agrees
#print axioms Rcic.Machine.TMemo.memoAt_agrees
#print axioms Rcic.Machine.TMemo.checkWithM_agrees
#print axioms Rcic.Machine.TMemo.tyAtWithM_agrees
#print axioms Rcic.Machine.TMemo.stepAtM_agrees
#print axioms Rcic.Machine.TMemo.appConvWithM_agrees
#print axioms Rcic.Machine.TMemo.litAtM_agrees
#print axioms Rcic.Machine.TMemo.irrAtM_agrees
#print axioms Rcic.Machine.TMemo.liftSpineWithM_agrees
#print axioms Rcic.Machine.TMemo.iotaStepWithM_agrees
#print axioms Rcic.Machine.TMemo.betaStepWithM_agrees
#print axioms Rcic.Machine.TMemo.iotaBetaStepM_agrees
#print axioms Rcic.Machine.TMemo.iotaMid?_eq
#print axioms Rcic.Machine.TMemo.iotaMidStepM_agrees
#print axioms Rcic.Machine.TMemo.iotaMidM_agrees
#print axioms Rcic.Machine.TMemo.domChainM_agrees
#print axioms Rcic.Machine.TMemo.piCongrM_agrees
#print axioms Rcic.Machine.TMemo.tyConv?_succ_eq
#print axioms Rcic.Machine.TMemo.convAt?_succ_eq
#print axioms Rcic.Machine.TMemo.tyMidM_agrees
#print axioms Rcic.Machine.TMemo.tyConvBodyM_agrees
#print axioms Rcic.Machine.TMemo.convStepM_agrees
#print axioms Rcic.Machine.TMemo.convFirstM_agrees
#print axioms Rcic.Machine.TMemo.convTailM_agrees
#print axioms Rcic.Machine.TMemo.convAtBodyM_agrees
#print axioms Rcic.Machine.TMemo.lvl_impl
#print axioms Rcic.Machine.TMemo.certWhnfM_agrees
#print axioms Rcic.Machine.TMemo.certStepT_agrees
#print axioms Rcic.Machine.TMemo.certStepMemo_eq
#print axioms Rcic.Machine.TMemo.certWhnfSMemo_eq
#print axioms Rcic.Machine.TMemo.certConvSMemo_eq
#print axioms Rcic.Machine.TMemo.certTyConvSMemo_eq
#print axioms Rcic.Machine.TMemo.certConvSMemo_sound
#print axioms Rcic.Machine.TMemo.cex_tyConv_ok_not_up
#print axioms Rcic.Machine.TMemo.cex_tyConv_no_not_up
#print axioms Rcic.Machine.TMemo.cex_certConvS_ok_not_up
#print axioms Rcic.Machine.TMemo.cex_certConvS_no_not_up
#print axioms Rcic.Machine.TMemo.cex_sound_entry_wrong_elsewhere
