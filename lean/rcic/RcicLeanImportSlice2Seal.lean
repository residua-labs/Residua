import rcic.RcicLeanImportSlice2Parse

namespace Rcic.LeanImport.Slice2

def sealedTheorems : List Lean.Name := [
  ``slice2_parse_sort_zero,
  ``slice2_parse_const_nolevel,
  ``slice2_parse_app
]

end Rcic.LeanImport.Slice2

#print axioms Rcic.LeanImport.Slice2.slice2_parse_sort_zero
#print axioms Rcic.LeanImport.Slice2.slice2_parse_const_nolevel
#print axioms Rcic.LeanImport.Slice2.slice2_parse_app
