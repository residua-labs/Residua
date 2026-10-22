import rcic.RcicLeanImport
import rcic.RcicLeanImportQ

namespace Rcic.LeanImport

def sealedTheorems : List Lean.Name := [
``li_mdata_erased,
``li_lam_binder_erased,
``li_let_nondep_erased,
``li_level_mvar_refused,
``li_native_nat_lit,
``li_nat_expansion_landed,
``li_delta_class_realization,
``li_def_edge_realization,
``li_thm_edge_logical,
``li_stmtQ_type_levels,
``li_bodyQ_payload,
``li_enc_lit
]

end Rcic.LeanImport

#print axioms Rcic.LeanImport.li_mdata_erased
#print axioms Rcic.LeanImport.li_lam_binder_erased
#print axioms Rcic.LeanImport.li_let_nondep_erased
#print axioms Rcic.LeanImport.li_level_mvar_refused
#print axioms Rcic.LeanImport.li_native_nat_lit
#print axioms Rcic.LeanImport.li_nat_expansion_landed
#print axioms Rcic.LeanImport.li_delta_class_realization
#print axioms Rcic.LeanImport.li_def_edge_realization
#print axioms Rcic.LeanImport.li_thm_edge_logical
#print axioms Rcic.LeanImport.li_stmtQ_type_levels
#print axioms Rcic.LeanImport.li_bodyQ_payload
#print axioms Rcic.LeanImport.li_enc_lit
