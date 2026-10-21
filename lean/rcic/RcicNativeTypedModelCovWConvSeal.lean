import Lean
import rcic.RcicNativeTypedModelCovWConvAndK
import rcic.RcicNativeTypedModelCovWConvBohm
import rcic.RcicNativeTypedModelCovWConvCompact
import rcic.RcicNativeTypedModelCovWConvControls
import rcic.RcicNativeTypedModelCovWConvCore
import rcic.RcicNativeTypedModelCovWConvForget
import rcic.RcicNativeTypedModelCovWConvHo
import rcic.RcicNativeTypedModelCovWConvK
import rcic.RcicNativeTypedModelCovWConvLevels
import rcic.RcicNativeTypedModelCovWConvLocal
import rcic.RcicNativeTypedModelCovWConvLocalRealized
import rcic.RcicNativeTypedModelCovWConvPositive
import rcic.RcicNativeTypedModelCovWConvQuotientRows
import rcic.RcicNativeTypedModelCovWConvReduction
import rcic.RcicNativeTypedModelCovWConvUniverse
import rcic.RcicNativeTypedModelCovWConvUniverseFragment
import rcic.RcicNativeTypedModelCovWConvValley

/-! Bounded ConvT alignment / level-code seal. Every public declaration in
the new modules is listed below. No full Foundation import. closure_claim = 0. -/

private def covWConvRoots : Array Lean.Name := #[
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvAndField0,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvAndField1,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_field1_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_field0_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_call_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_target_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_data,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_conversion,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_rhs_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBohmBody,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBohmMinor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBohmPrefix,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBohmCall,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_body_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_minor_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_prefix_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_call_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_call_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_call_observation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_all_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_candidate_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvBohmNonconversionRemaining,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CptWConvR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRawErase,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRawEraseRows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRawEraseArgs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_args,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_rows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRawRowErase,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_bot_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.sortCodeWConvR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_sortCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.EnvWConvR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.EnvWConvR.bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.EnvWConvR.cons,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.demandWConvR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.EnvWConvR.pushArgs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRawEnvErase,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_env_erase_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_env_erase_cons,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_env_erase_push,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.curryStepWConvR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.fieldDemandVectorsWConvR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.ctorDemandWConvR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_curry,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_vectors,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_ctorDemand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvCodeRows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvCodeArgs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_code_args,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_code_rows,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_code_bot_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvCoarse,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.UniverseWConv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CTyWConvR,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_typing_forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CTySConv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvRealized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_realized_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_realized_nil,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_M_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_prop_demand_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_prop_demand_nonbottom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_guards_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_M_shared_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_RI_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvApartRetention,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_apart_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_apart_direct_K_blocked,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_beta_binder_tests,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_zeta_binder_tests,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.ApproxTKWConv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_iota_expand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_K_expand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvObservation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_observation_of,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.ApproxTKWConvStage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.ApproxTKWConvStage.mono,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvTypedInvariant,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvCodesDetermineTypes,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_forget,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_head_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_ctor_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_divergent_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_beta_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_let_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_fn_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_prefix_only_bot,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_observation_bot_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bottom_observations_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_ctor_observation_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_beta_all_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_zeta_all_observations,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_eta_functions_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_eta_app_function_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_irr_calls_equal,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_typed_cells,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_cells_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvKData,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_K_sound,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_K_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_K_bvar_data,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_etaIndex_K_data,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_etaIndex_sound,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBadMinor,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBadKSource,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBadKWitness,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bad_K_gates,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bad_K_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bad_minor_untyped,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_four_gates_do_not_imply_conversion,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.levelSetoid,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.ofLevel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.eval,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.succ,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.imax,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.eval_ofLevel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.succ_ofLevel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.imax_ofLevel,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.ofLevel_eq_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CptWConv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.sort_code_exact,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CTyU,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CTyU.pi_const,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.UniversePiFragmentObs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.SameUniversePiFragmentObs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.sort_fragment_obs_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.same_sort_fragment_obs_iff,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.sort_fragment_complete,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.levelOne,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.levelTwo,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.levelThree,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.levelOne_code_ne_levelTwo,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.imax_two_three,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.imax_three_three,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiA,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiB,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiACode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiBCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiA_CTyu,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiB_CTyu,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiA_has_obs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiB_has_obs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiB_lacks_A_obs,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePi_fragment_separated,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocalType,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocalValue,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocalCtx,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocalTypeCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocalDemand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_ctx_wf,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_type_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_variable_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_value_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_native_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_native_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_type_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_value_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_demand_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_demand_nonbottom,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_slot_demands_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bvar_bot_lacks_sort,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_variable_lacks_demand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_not_typed_invariant,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_not_observation_expansion,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_cell_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocalSubst,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_subst_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_realized,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_closed_endpoints_identical,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_realized_cell_inhabited,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_aligned_step,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_empty_pi_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_iota_observation_expand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_K_observation_expand,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_true_call_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueIota_left_ty,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueIota_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueK_data,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueK_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueK_conversion,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_eqIota_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_etaIndex_K_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andIota_rhs_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andIota_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueIota_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_eqIota_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andIota_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueK_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_etaIndex_K_positive,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_singleton_public_coverage,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_function_singleton_output,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvInputAlias,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_input_alias_eqN,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_input_alias_raw_distinct,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_alias_raw_distinct_but_covered,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_alias_row_output,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_reduction_sound,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_reduction_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvCK2Star,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvReductionStar,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_reductionStar_sound,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_reductionStar_native,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvEtaReduction,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_etaReduction_sound,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvEtaReductionStar,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_etaReductionStar_sound,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_sort_observation_exact,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_sort_complete,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiARaw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiBRaw,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiARaw_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiBRaw_code,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeA_formation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeB_formation,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeA_raw_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeB_raw_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeA_code_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeB_code_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeA_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeB_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeB_lacks_A,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universe_observations_differ,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeA_native_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeB_native_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universe_native_not_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universe_typed_separator,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvPiSortCode,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_pi_sort_observed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_pi_sort_observation_exact,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_pi_sort_observations_determine_levels,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_pi_sort_complete,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_pi_sort_native_typed,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_empty_raw_sort_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_empty_sort_observation_shape,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_empty_sort_invariant,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyDomain,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPiLeft,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPiRight,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyUniverse,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyDomain_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyDomain_conv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPiLeft_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPiRight_hasTy,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPi_nativeConv,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPi_distinct,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPi_actualNativeValley,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPi_noCK2Valley,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvCK2PiValleys,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.not_CovWConvCK2PiValleys,
  ``Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvCK2PiValleys_inhabited_counterexample
]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Quot.sound]
  for root in covWConvRoots do
    if !env.contains root then
      throwError "CovWConv seal: missing declaration {root}"
    let axioms ← collectAxioms root
    let forbidden := axioms.filter (fun ax => !allowed.contains ax)
    if !forbidden.isEmpty then
      throwError "CovWConv seal: {root} has forbidden axioms {forbidden}"
  logInfo m!"CovWConv seal: {covWConvRoots.size} public roots checked; allowed axioms = {allowed}"

#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvAndField0
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvAndField1
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_field1_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_field0_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_call_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_target_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_data
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_conversion
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_rhs_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andK_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBohmBody
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBohmMinor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBohmPrefix
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBohmCall
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_body_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_minor_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_prefix_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_call_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_call_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_call_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_all_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bohm_candidate_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvBohmNonconversionRemaining
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CptWConvR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRawErase
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRawEraseRows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRawEraseArgs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_args
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_rows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRawRowErase
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_bot_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.sortCodeWConvR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_sortCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.EnvWConvR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.EnvWConvR.bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.EnvWConvR.cons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.demandWConvR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.EnvWConvR.pushArgs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRawEnvErase
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_env_erase_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_env_erase_cons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_env_erase_push
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.curryStepWConvR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.fieldDemandVectorsWConvR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.ctorDemandWConvR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_curry
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_vectors
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvRaw_erase_ctorDemand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvCodeRows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvCodeArgs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_code_args
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_code_rows
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_code_bot_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvCoarse
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.UniverseWConv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CTyWConvR
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_typing_forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CTySConv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvRealized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_realized_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_realized_nil
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_M_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_prop_demand_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_prop_demand_nonbottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_guards_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_M_shared_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_RI_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvApartRetention
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_apart_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_apart_direct_K_blocked
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_beta_binder_tests
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_zeta_binder_tests
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.ApproxTKWConv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_iota_expand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_K_expand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvObservation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_observation_of
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.ApproxTKWConvStage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.ApproxTKWConvStage.mono
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvTypedInvariant
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvCodesDetermineTypes
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_forget
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_head_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_ctor_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_divergent_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_beta_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_let_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_fn_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_prefix_only_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_observation_bot_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bottom_observations_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_ctor_observation_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_beta_all_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_zeta_all_observations
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_eta_functions_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_eta_app_function_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_irr_calls_equal
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_typed_cells
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_Ho_cells_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvKData
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_K_sound
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_K_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_K_bvar_data
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_etaIndex_K_data
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_etaIndex_sound
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBadMinor
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBadKSource
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvBadKWitness
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bad_K_gates
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bad_K_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bad_minor_untyped
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_four_gates_do_not_imply_conversion
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.levelSetoid
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.ofLevel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.eval
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.succ
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.imax
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.eval_ofLevel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.succ_ofLevel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.imax_ofLevel
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.LevelCode.ofLevel_eq_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CptWConv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.sort_code_exact
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CTyU
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CTyU.pi_const
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.UniversePiFragmentObs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.SameUniversePiFragmentObs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.sort_fragment_obs_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.same_sort_fragment_obs_iff
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.sort_fragment_complete
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.levelOne
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.levelTwo
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.levelThree
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.levelOne_code_ne_levelTwo
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.imax_two_three
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.imax_three_three
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiA
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiB
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiACode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiBCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiA_CTyu
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiB_CTyu
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiA_has_obs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiB_has_obs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiB_lacks_A_obs
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePi_fragment_separated
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocalType
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocalValue
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocalCtx
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocalTypeCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocalDemand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_ctx_wf
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_type_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_variable_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_value_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_native_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_native_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_type_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_value_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_demand_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_demand_nonbottom
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_slot_demands_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_bvar_bot_lacks_sort
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_variable_lacks_demand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_not_typed_invariant
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_not_observation_expansion
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_cell_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocalSubst
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_subst_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_realized
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_closed_endpoints_identical
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_realized_cell_inhabited
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvLocal_aligned_step
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_empty_pi_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_iota_observation_expand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_K_observation_expand
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_true_call_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueIota_left_ty
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueIota_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueK_data
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueK_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueK_conversion
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_eqIota_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_etaIndex_K_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andIota_rhs_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andIota_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueIota_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_eqIota_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_andIota_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_trueK_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_etaIndex_K_positive
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_singleton_public_coverage
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_function_singleton_output
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvInputAlias
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_input_alias_eqN
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_input_alias_raw_distinct
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_alias_raw_distinct_but_covered
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_alias_row_output
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_reduction_sound
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_reduction_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvCK2Star
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvReductionStar
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_reductionStar_sound
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_reductionStar_native
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvEtaReduction
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_etaReduction_sound
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvEtaReductionStar
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_etaReductionStar_sound
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_sort_observation_exact
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_sort_complete
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiARaw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiBRaw
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiARaw_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.universePiBRaw_code
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeA_formation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeB_formation
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeA_raw_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeB_raw_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeA_code_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeB_code_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeA_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeB_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeB_lacks_A
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universe_observations_differ
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeA_native_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universeB_native_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universe_native_not_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_universe_typed_separator
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvPiSortCode
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_pi_sort_observed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_pi_sort_observation_exact
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_pi_sort_observations_determine_levels
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_pi_sort_complete
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_pi_sort_native_typed
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_empty_raw_sort_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_empty_sort_observation_shape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConv_empty_sort_invariant
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyDomain
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPiLeft
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPiRight
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyUniverse
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyDomain_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyDomain_conv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPiLeft_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPiRight_hasTy
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPi_nativeConv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPi_distinct
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPi_actualNativeValley
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.convValleyPi_noCK2Valley
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvCK2PiValleys
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.not_CovWConvCK2PiValleys
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvCK2PiValleys_inhabited_counterexample
