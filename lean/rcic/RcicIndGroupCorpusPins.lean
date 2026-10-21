import rcic.RcicIndGroupAdmitted
namespace Rcic.Declarative

def pinField : List (Expr Nat) → Nat → Expr Nat
  | f :: _, 0 => f
  | _ :: fs, n + 1 => pinField fs n
  | [], _ => .sort .zero

/-! IA 010 accept nonrecursive fields: h:bvar0, n:const Nat  > rec0/rec0
carrier `` -/
def occ00_E : ResolvedEnv := emptyEnv
def occ00_fields : List (Expr Nat) := [(.bvar 0), (.const 1 [])]
def occ00_nuniv : Nat := 0
def occ00_nparams : Nat := 1
def occ00_nindices : Nat := 0
def occ00_kind : CorpusPinKind := .specAccept
theorem occ00_pin :
    occ00_kind = .specAccept ∧
    fieldShapesFuel occ00_E 80 0 occ00_nuniv occ00_nparams occ00_nindices
      occ00_nparams occ00_fields = some [.nonrecursive, .nonrecursive] := by
  constructor <;> rfl

/-! IA 010 accept direct recursion: Nat succ field local:0  > rec1 inner0
carrier `` -/
def occ01_E : ResolvedEnv := emptyEnv
def occ01_fields : List (Expr Nat) := [(.const 0 [])]
def occ01_nuniv : Nat := 0
def occ01_nparams : Nat := 0
def occ01_nindices : Nat := 0
def occ01_kind : CorpusPinKind := .specAccept
theorem occ01_pin :
    occ01_kind = .specAccept ∧
    fieldShapesFuel occ01_E 80 0 occ01_nuniv occ01_nparams occ01_nindices
      occ01_nparams occ01_fields = some [(.recursive 0)] := by
  constructor <;> rfl

/-! IA 010 accept List cons: h:bvar0 then t:local:0(bvar1)
carrier `` -/
def occ02_E : ResolvedEnv := emptyEnv
def occ02_fields : List (Expr Nat) := [(.bvar 0), (.app (.const 0 []) (.bvar 1))]
def occ02_nuniv : Nat := 0
def occ02_nparams : Nat := 1
def occ02_nindices : Nat := 0
def occ02_kind : CorpusPinKind := .specAccept
theorem occ02_pin :
    occ02_kind = .specAccept ∧
    fieldShapesFuel occ02_E 80 0 occ02_nuniv occ02_nparams occ02_nindices
      occ02_nparams occ02_fields = some [.nonrecursive, (.recursive 0)] := by
  constructor <;> rfl

/-! IA 010 accept function positive: f:Pi(n:Nat).local:0(bvar1)  > inner1
carrier `` -/
def occ03_E : ResolvedEnv := emptyEnv
def occ03_fields : List (Expr Nat) := [(.pi (.const 1 []) (.app (.const 0 []) (.bvar 1)))]
def occ03_nuniv : Nat := 0
def occ03_nparams : Nat := 1
def occ03_nindices : Nat := 0
def occ03_kind : CorpusPinKind := .specAccept
theorem occ03_pin :
    occ03_kind = .specAccept ∧
    fieldShapesFuel occ03_E 80 0 occ03_nuniv occ03_nparams occ03_nindices
      occ03_nparams occ03_fields = some [(.recursive 1)] := by
  constructor <;> rfl

/-! IA 010 accept indexed recursion: v:local:0(bvar1)(bvar0)  > ri=[bvar0]
carrier `` -/
def occ04_E : ResolvedEnv := emptyEnv
def occ04_fields : List (Expr Nat) := [(.const 1 []), (.app (.app (.const 0 []) (.bvar 1)) (.bvar 0))]
def occ04_nuniv : Nat := 0
def occ04_nparams : Nat := 1
def occ04_nindices : Nat := 1
def occ04_kind : CorpusPinKind := .specAccept
theorem occ04_pin :
    occ04_kind = .specAccept ∧
    fieldShapesFuel occ04_E 80 0 occ04_nuniv occ04_nparams occ04_nindices
      occ04_nparams occ04_fields = some [.nonrecursive, (.recursive 0)] := by
  constructor <;> rfl

/-! IA 009 refuse family in inner Pi domain: f:Pi(x:local:0 A).Nat
carrier `[rcic_ind_occurrence_not_permitted]` -/
def occ05_E : ResolvedEnv := emptyEnv
def occ05_fields : List (Expr Nat) := [(.pi (.app (.const 0 []) (.bvar 1)) (.const 1 []))]
def occ05_nuniv : Nat := 0
def occ05_nparams : Nat := 1
def occ05_nindices : Nat := 0
def occ05_kind : CorpusPinKind := .specRefuse
theorem occ05_pin :
    occ05_kind = .specRefuse ∧ fieldAnalyze occ05_E 80 0 occ05_nuniv occ05_nparams occ05_nindices (occ05_nparams + 0) (pinField occ05_fields 0) = .refused .negativeOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 009 refuse family in letE value (zeta erased): letE S1 local:0 Nat
carrier `[rcic_ind_occurrence_not_permitted]` -/
def occ06_E : ResolvedEnv := emptyEnv
def occ06_fields : List (Expr Nat) := [(.letE (.sort (.succ .zero)) (.const 0 []) (.const 1 []))]
def occ06_nuniv : Nat := 0
def occ06_nparams : Nat := 0
def occ06_nindices : Nat := 0
def occ06_kind : CorpusPinKind := .specRefuse
theorem occ06_pin :
    occ06_kind = .specRefuse ∧ fieldAnalyze occ06_E 80 0 occ06_nuniv occ06_nparams occ06_nindices (occ06_nparams + 0) (pinField occ06_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 009 refuse family in letE type: letE local:0 S1 Nat
carrier `[rcic_ind_occurrence_not_permitted]` -/
def occ07_E : ResolvedEnv := emptyEnv
def occ07_fields : List (Expr Nat) := [(.letE (.const 0 []) (.sort (.succ .zero)) (.const 1 []))]
def occ07_nuniv : Nat := 0
def occ07_nparams : Nat := 0
def occ07_nindices : Nat := 0
def occ07_kind : CorpusPinKind := .specRefuse
theorem occ07_pin :
    occ07_kind = .specRefuse ∧ fieldAnalyze occ07_E 80 0 occ07_nuniv occ07_nparams occ07_nindices (occ07_nparams + 0) (pinField occ07_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 009 refuse family in letE body: letE S1 Nat (lam S1 local:0)
carrier `[rcic_ind_occurrence_not_permitted]` -/
def occ08_E : ResolvedEnv := emptyEnv
def occ08_fields : List (Expr Nat) := [(.letE (.sort (.succ .zero)) (.const 1 []) (.lam (.sort (.succ .zero)) (.const 0 [])))]
def occ08_nuniv : Nat := 0
def occ08_nparams : Nat := 0
def occ08_nindices : Nat := 0
def occ08_kind : CorpusPinKind := .specRefuse
theorem occ08_pin :
    occ08_kind = .specRefuse ∧ fieldAnalyze occ08_E 80 0 occ08_nuniv occ08_nparams occ08_nindices (occ08_nparams + 0) (pinField occ08_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 009 refuse family under lam in app arg: F (lam S1 local:0)
carrier `[rcic_ind_occurrence_not_permitted]` -/
def occ09_m0 : CheckedMember := ⟨.definitionM, 0, (.pi (.sort (.succ .zero)) (.sort (.succ .zero))), some (.lam (.sort (.succ .zero)) (.const 1 []))⟩
def occ09_E : ResolvedEnv := (extendEnv emptyEnv 4 occ09_m0)
def occ09_fields : List (Expr Nat) := [(.app (.const 3 []) (.lam (.sort (.succ .zero)) (.const 0 [])))]
def occ09_nuniv : Nat := 0
def occ09_nparams : Nat := 0
def occ09_nindices : Nat := 0
def occ09_kind : CorpusPinKind := .specRefuse
theorem occ09_pin :
    occ09_kind = .specRefuse ∧ fieldAnalyze occ09_E 80 0 occ09_nuniv occ09_nparams occ09_nindices (occ09_nparams + 0) (pinField occ09_fields 0) = .refused .nestedInductiveOutOfProfile := by
  repeat (first | constructor | rfl)

/-! IA 009 refuse family as ctor arg: List local:0
carrier `[rcic_ind_occurrence_not_permitted]` -/
def occ10_E : ResolvedEnv := emptyEnv
def occ10_fields : List (Expr Nat) := [(.app (.const 2 []) (.const 0 []))]
def occ10_nuniv : Nat := 0
def occ10_nparams : Nat := 0
def occ10_nindices : Nat := 0
def occ10_kind : CorpusPinKind := .specRefuse
theorem occ10_pin :
    occ10_kind = .specRefuse ∧ fieldAnalyze occ10_E 80 0 occ10_nuniv occ10_nparams occ10_nindices (occ10_nparams + 0) (pinField occ10_fields 0) = .refused .nestedInductiveOutOfProfile := by
  repeat (first | constructor | rfl)

/-! IA 009 refuse family inside own index: local:0 A (local:0 A)
carrier `[rcic_ind_occurrence_not_permitted]` -/
def occ11_E : ResolvedEnv := emptyEnv
def occ11_fields : List (Expr Nat) := [(.app (.app (.const 0 []) (.bvar 0)) (.app (.const 0 []) (.bvar 0)))]
def occ11_nuniv : Nat := 0
def occ11_nparams : Nat := 1
def occ11_nindices : Nat := 1
def occ11_kind : CorpusPinKind := .specRefuse
theorem occ11_pin :
    occ11_kind = .specRefuse ∧ fieldAnalyze occ11_E 80 0 occ11_nuniv occ11_nparams occ11_nindices (occ11_nparams + 0) (pinField occ11_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 010 refuse non uniform param: field local:0 Nat
carrier `[rcic_ind_occurrence_not_permitted]` -/
def occ12_E : ResolvedEnv := emptyEnv
def occ12_fields : List (Expr Nat) := [(.app (.const 0 []) (.const 1 []))]
def occ12_nuniv : Nat := 0
def occ12_nparams : Nat := 1
def occ12_nindices : Nat := 0
def occ12_kind : CorpusPinKind := .specRefuse
theorem occ12_pin :
    occ12_kind = .specRefuse ∧ fieldAnalyze occ12_E 80 0 occ12_nuniv occ12_nparams occ12_nindices (occ12_nparams + 0) (pinField occ12_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 010 refuse wrong universe vector: local:0[] in nuniv1 family
carrier `[rcic_ind_occurrence_not_permitted]` -/
def occ13_E : ResolvedEnv := emptyEnv
def occ13_fields : List (Expr Nat) := [(.app (.const 0 []) (.bvar 0))]
def occ13_nuniv : Nat := 1
def occ13_nparams : Nat := 1
def occ13_nindices : Nat := 0
def occ13_kind : CorpusPinKind := .specRefuse
theorem occ13_pin :
    occ13_kind = .specRefuse ∧ fieldAnalyze occ13_E 80 0 occ13_nuniv occ13_nparams occ13_nindices (occ13_nparams + 0) (pinField occ13_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 009 refuse delta erased occurrence: K local:0 (K unfolds to lam.Nat)
carrier `[rcic_ind_occurrence_not_permitted]` -/
def occ14_m0 : CheckedMember := ⟨.definitionM, 0, (.pi (.sort (.succ .zero)) (.sort (.succ .zero))), some (.lam (.sort (.succ .zero)) (.const 1 []))⟩
def occ14_E : ResolvedEnv := (extendEnv emptyEnv 4 occ14_m0)
def occ14_fields : List (Expr Nat) := [(.app (.const 4 []) (.const 0 []))]
def occ14_nuniv : Nat := 0
def occ14_nparams : Nat := 0
def occ14_nindices : Nat := 0
def occ14_kind : CorpusPinKind := .specRefuse
theorem occ14_pin :
    occ14_kind = .specRefuse ∧ fieldAnalyze occ14_E 80 0 occ14_nuniv occ14_nparams occ14_nindices (occ14_nparams + 0) (pinField occ14_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! §8 refuse fuel: field pi chain depth 14 at fuel 12 (scan exhausts)
carrier `[rcic_expr_has_ref_fuel]` -/
def occ15_E : ResolvedEnv := emptyEnv
def occ15_fields : List (Expr Nat) := [(.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.sort (.succ .zero))))))))))))))))]
def occ15_nuniv : Nat := 0
def occ15_nparams : Nat := 1
def occ15_nindices : Nat := 0
def occ15_kind : CorpusPinKind := .notSpecRefusal
theorem occ15_pin :
    occ15_kind = .notSpecRefusal ∧
    fieldAnalyze occ15_E 12 0 occ15_nuniv occ15_nparams occ15_nindices
      occ15_nparams (pinField occ15_fields 0) = .unresolved := by
  constructor <;> rfl

/-! §8 accept same deep field with fuel 200  > rec0
carrier `` -/
def occ16_E : ResolvedEnv := emptyEnv
def occ16_fields : List (Expr Nat) := [(.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.sort (.succ .zero))))))))))))))))]
def occ16_nuniv : Nat := 0
def occ16_nparams : Nat := 1
def occ16_nindices : Nat := 0
def occ16_kind : CorpusPinKind := .specAccept
theorem occ16_pin :
    occ16_kind = .specAccept ∧
    fieldShapesFuel occ16_E 80 0 occ16_nuniv occ16_nparams occ16_nindices
      occ16_nparams occ16_fields = some [.nonrecursive] := by
  constructor <;> rfl

/-! §6 shape refusal propagates: mirror S2 vs fam S1
carrier `[rcic_ind_ctor_shape_mirror_mismatch]` -/
def occ17_E : ResolvedEnv := emptyEnv
def occ17_fields : List (Expr Nat) := []
def occ17_nuniv : Nat := 0
def occ17_nparams : Nat := 1
def occ17_nindices : Nat := 0
def occ17_kind : CorpusPinKind := .notSpecRefusal
theorem occ17_pin : occ17_kind = .notSpecRefusal := rfl

/-! refuse unknown form
carrier `[rcic_ind_occurrence_unknown_form]` -/
def occ18_E : ResolvedEnv := emptyEnv
def occ18_fields : List (Expr Nat) := []
def occ18_nuniv : Nat := 0
def occ18_nparams : Nat := 0
def occ18_nindices : Nat := 0
def occ18_kind : CorpusPinKind := .notSpecRefusal
theorem occ18_pin : occ18_kind = .notSpecRefusal := rfl

/-! IA 013/14 accept nonrecursive fields: h:bvar0, n:const Nat  > rec0/rec0
carrier `` -/
def pos00_E : ResolvedEnv := emptyEnv
def pos00_fields : List (Expr Nat) := [(.bvar 0), (.const 1 [])]
def pos00_nuniv : Nat := 0
def pos00_nparams : Nat := 1
def pos00_nindices : Nat := 0
def pos00_kind : CorpusPinKind := .specAccept
theorem pos00_pin :
    pos00_kind = .specAccept ∧
    fieldShapesFuel pos00_E 80 0 pos00_nuniv pos00_nparams pos00_nindices
      pos00_nparams pos00_fields = some [.nonrecursive, .nonrecursive] := by
  constructor <;> rfl

/-! IA 013/14 accept direct recursion: Nat succ field local:0  > rec1 inner0
carrier `` -/
def pos01_E : ResolvedEnv := emptyEnv
def pos01_fields : List (Expr Nat) := [(.const 0 [])]
def pos01_nuniv : Nat := 0
def pos01_nparams : Nat := 0
def pos01_nindices : Nat := 0
def pos01_kind : CorpusPinKind := .specAccept
theorem pos01_pin :
    pos01_kind = .specAccept ∧
    fieldShapesFuel pos01_E 80 0 pos01_nuniv pos01_nparams pos01_nindices
      pos01_nparams pos01_fields = some [(.recursive 0)] := by
  constructor <;> rfl

/-! IA 013/14 accept List cons direct: t:local:0(bvar1)  > rec1 inner0
carrier `` -/
def pos02_E : ResolvedEnv := emptyEnv
def pos02_fields : List (Expr Nat) := [(.bvar 0), (.app (.const 0 []) (.bvar 1))]
def pos02_nuniv : Nat := 0
def pos02_nparams : Nat := 1
def pos02_nindices : Nat := 0
def pos02_kind : CorpusPinKind := .specAccept
theorem pos02_pin :
    pos02_kind = .specAccept ∧
    fieldShapesFuel pos02_E 80 0 pos02_nuniv pos02_nparams pos02_nindices
      pos02_nparams pos02_fields = some [.nonrecursive, (.recursive 0)] := by
  constructor <;> rfl

/-! IA 013/14 accept function positive: f:Pi(n:Nat).local:0(bvar1)  > inner1
carrier `` -/
def pos03_E : ResolvedEnv := emptyEnv
def pos03_fields : List (Expr Nat) := [(.pi (.const 1 []) (.app (.const 0 []) (.bvar 1)))]
def pos03_nuniv : Nat := 0
def pos03_nparams : Nat := 1
def pos03_nindices : Nat := 0
def pos03_kind : CorpusPinKind := .specAccept
theorem pos03_pin :
    pos03_kind = .specAccept ∧
    fieldShapesFuel pos03_E 80 0 pos03_nuniv pos03_nparams pos03_nindices
      pos03_nparams pos03_fields = some [(.recursive 1)] := by
  constructor <;> rfl

/-! IA 013/14 accept indexed recursion: v:local:0 A n  > ri=[bvar0]
carrier `` -/
def pos04_E : ResolvedEnv := emptyEnv
def pos04_fields : List (Expr Nat) := [(.const 1 []), (.app (.app (.const 0 []) (.bvar 1)) (.bvar 0))]
def pos04_nuniv : Nat := 0
def pos04_nparams : Nat := 1
def pos04_nindices : Nat := 1
def pos04_kind : CorpusPinKind := .specAccept
theorem pos04_pin :
    pos04_kind = .specAccept ∧
    fieldShapesFuel pos04_E 80 0 pos04_nuniv pos04_nparams pos04_nindices
      pos04_nparams pos04_fields = some [.nonrecursive, (.recursive 0)] := by
  constructor <;> rfl

/-! IA 013 accept mixed ctor: rec0 + direct indexed + fn pos descs in order
carrier `` -/
def pos05_E : ResolvedEnv := emptyEnv
def pos05_fields : List (Expr Nat) := [(.const 1 []), (.app (.app (.const 0 []) (.bvar 1)) (.bvar 0)), (.pi (.const 1 []) (.app (.app (.const 0 []) (.bvar 3)) (.bvar 0)))]
def pos05_nuniv : Nat := 0
def pos05_nparams : Nat := 1
def pos05_nindices : Nat := 1
def pos05_kind : CorpusPinKind := .specAccept
theorem pos05_pin :
    pos05_kind = .specAccept ∧
    fieldShapesFuel pos05_E 80 0 pos05_nuniv pos05_nparams pos05_nindices
      pos05_nparams pos05_fields = some [.nonrecursive, (.recursive 0), (.recursive 1)] := by
  constructor <;> rfl

/-! IA 011 negative: field Pi(x:local:0 A).Nat  > negative
carrier `[rcic_ind_positivity_negative]` -/
def pos06_E : ResolvedEnv := emptyEnv
def pos06_fields : List (Expr Nat) := [(.pi (.app (.const 0 []) (.bvar 0)) (.const 1 []))]
def pos06_nuniv : Nat := 0
def pos06_nparams : Nat := 1
def pos06_nindices : Nat := 0
def pos06_kind : CorpusPinKind := .specRefuse
theorem pos06_pin :
    pos06_kind = .specRefuse ∧ fieldAnalyze pos06_E 80 0 pos06_nuniv pos06_nparams pos06_nindices (pos06_nparams + 0) (pinField pos06_fields 0) = .refused .negativeOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 011 deep negative: field Pi(g:Pi(y:local:0 A).Nat).Nat  > negative
carrier `[rcic_ind_positivity_negative]` -/
def pos07_E : ResolvedEnv := emptyEnv
def pos07_fields : List (Expr Nat) := [(.pi (.pi (.app (.const 0 []) (.bvar 0)) (.const 1 [])) (.const 1 []))]
def pos07_nuniv : Nat := 0
def pos07_nparams : Nat := 1
def pos07_nindices : Nat := 0
def pos07_kind : CorpusPinKind := .specRefuse
theorem pos07_pin :
    pos07_kind = .specRefuse ∧ fieldAnalyze pos07_E 80 0 pos07_nuniv pos07_nparams pos07_nindices (pos07_nparams + 0) (pinField pos07_fields 0) = .refused .negativeOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 012 nested: field List (local:0 A less)  > nested_out_of_profile
carrier `[rcic_ind_positivity_nested_out_of_profile]` -/
def pos08_E : ResolvedEnv := emptyEnv
def pos08_fields : List (Expr Nat) := [(.app (.const 2 []) (.const 0 []))]
def pos08_nuniv : Nat := 0
def pos08_nparams : Nat := 0
def pos08_nindices : Nat := 0
def pos08_kind : CorpusPinKind := .specRefuse
theorem pos08_pin :
    pos08_kind = .specRefuse ∧ fieldAnalyze pos08_E 80 0 pos08_nuniv pos08_nparams pos08_nindices (pos08_nparams + 0) (pinField pos08_fields 0) = .refused .nestedInductiveOutOfProfile := by
  repeat (first | constructor | rfl)

/-! IA 012 nested under lam arg: field F (lam S1 local:0)  > nested
carrier `[rcic_ind_positivity_nested_out_of_profile]` -/
def pos09_m0 : CheckedMember := ⟨.definitionM, 0, (.pi (.sort (.succ .zero)) (.sort (.succ .zero))), some (.lam (.sort (.succ .zero)) (.const 1 []))⟩
def pos09_E : ResolvedEnv := (extendEnv emptyEnv 4 pos09_m0)
def pos09_fields : List (Expr Nat) := [(.app (.const 3 []) (.lam (.sort (.succ .zero)) (.const 0 [])))]
def pos09_nuniv : Nat := 0
def pos09_nparams : Nat := 0
def pos09_nindices : Nat := 0
def pos09_kind : CorpusPinKind := .specRefuse
theorem pos09_pin :
    pos09_kind = .specRefuse ∧ fieldAnalyze pos09_E 80 0 pos09_nuniv pos09_nparams pos09_nindices (pos09_nparams + 0) (pinField pos09_fields 0) = .refused .nestedInductiveOutOfProfile := by
  repeat (first | constructor | rfl)

/-! IA 012 invalid positive: non uniform param local:0 Nat  > invalid
carrier `[rcic_ind_positivity_invalid_positive]` -/
def pos10_E : ResolvedEnv := emptyEnv
def pos10_fields : List (Expr Nat) := [(.app (.const 0 []) (.const 1 []))]
def pos10_nuniv : Nat := 0
def pos10_nparams : Nat := 1
def pos10_nindices : Nat := 0
def pos10_kind : CorpusPinKind := .specRefuse
theorem pos10_pin :
    pos10_kind = .specRefuse ∧ fieldAnalyze pos10_E 80 0 pos10_nuniv pos10_nparams pos10_nindices (pos10_nparams + 0) (pinField pos10_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 012 invalid positive: family inside own index  > invalid
carrier `[rcic_ind_positivity_invalid_positive]` -/
def pos11_E : ResolvedEnv := emptyEnv
def pos11_fields : List (Expr Nat) := [(.app (.app (.const 0 []) (.bvar 0)) (.app (.const 0 []) (.bvar 0)))]
def pos11_nuniv : Nat := 0
def pos11_nparams : Nat := 1
def pos11_nindices : Nat := 1
def pos11_kind : CorpusPinKind := .specRefuse
theorem pos11_pin :
    pos11_kind = .specRefuse ∧ fieldAnalyze pos11_E 80 0 pos11_nuniv pos11_nparams pos11_nindices (pos11_nparams + 0) (pinField pos11_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 012 invalid positive: wrong universe vector local:0[] nuniv1
carrier `[rcic_ind_positivity_invalid_positive]` -/
def pos12_E : ResolvedEnv := emptyEnv
def pos12_fields : List (Expr Nat) := [(.app (.const 0 []) (.bvar 0))]
def pos12_nuniv : Nat := 1
def pos12_nparams : Nat := 1
def pos12_nindices : Nat := 0
def pos12_kind : CorpusPinKind := .specRefuse
theorem pos12_pin :
    pos12_kind = .specRefuse ∧ fieldAnalyze pos12_E 80 0 pos12_nuniv pos12_nparams pos12_nindices (pos12_nparams + 0) (pinField pos12_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 012 invalid positive: bvar headed family app app(bvar0, local:0)
carrier `[rcic_ind_positivity_invalid_positive]` -/
def pos13_E : ResolvedEnv := emptyEnv
def pos13_fields : List (Expr Nat) := [(.app (.bvar 0) (.const 0 []))]
def pos13_nuniv : Nat := 0
def pos13_nparams : Nat := 0
def pos13_nindices : Nat := 0
def pos13_kind : CorpusPinKind := .specRefuse
theorem pos13_pin :
    pos13_kind = .specRefuse ∧ fieldAnalyze pos13_E 80 0 pos13_nuniv pos13_nparams pos13_nindices (pos13_nparams + 0) (pinField pos13_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 012 invalid positive: delta erased occurrence K local:0  > invalid
carrier `[rcic_ind_positivity_invalid_positive]` -/
def pos14_m0 : CheckedMember := ⟨.definitionM, 0, (.pi (.sort (.succ .zero)) (.sort (.succ .zero))), some (.lam (.sort (.succ .zero)) (.const 1 []))⟩
def pos14_E : ResolvedEnv := (extendEnv emptyEnv 4 pos14_m0)
def pos14_fields : List (Expr Nat) := [(.app (.const 4 []) (.const 0 []))]
def pos14_nuniv : Nat := 0
def pos14_nparams : Nat := 0
def pos14_nindices : Nat := 0
def pos14_kind : CorpusPinKind := .specRefuse
theorem pos14_pin :
    pos14_kind = .specRefuse ∧ fieldAnalyze pos14_E 80 0 pos14_nuniv pos14_nparams pos14_nindices (pos14_nparams + 0) (pinField pos14_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 012 invalid positive: letE value only occurrence  > invalid
carrier `[rcic_ind_positivity_invalid_positive]` -/
def pos15_E : ResolvedEnv := emptyEnv
def pos15_fields : List (Expr Nat) := [(.letE (.sort (.succ .zero)) (.const 0 []) (.const 1 []))]
def pos15_nuniv : Nat := 0
def pos15_nparams : Nat := 0
def pos15_nindices : Nat := 0
def pos15_kind : CorpusPinKind := .specRefuse
theorem pos15_pin :
    pos15_kind = .specRefuse ∧ fieldAnalyze pos15_E 80 0 pos15_nuniv pos15_nparams pos15_nindices (pos15_nparams + 0) (pinField pos15_fields 0) = .refused .invalidPositiveOccurrence := by
  repeat (first | constructor | rfl)

/-! IA 011 mixed field Pi(x:local:0).List(local:0): negative wins
carrier `[rcic_ind_positivity_negative]` -/
def pos16_E : ResolvedEnv := emptyEnv
def pos16_fields : List (Expr Nat) := [(.pi (.app (.const 0 []) (.bvar 0)) (.app (.const 2 []) (.app (.const 0 []) (.bvar 1))))]
def pos16_nuniv : Nat := 0
def pos16_nparams : Nat := 1
def pos16_nindices : Nat := 0
def pos16_kind : CorpusPinKind := .specRefuse
theorem pos16_pin :
    pos16_kind = .specRefuse ∧ fieldAnalyze pos16_E 80 0 pos16_nuniv pos16_nparams pos16_nindices (pos16_nparams + 0) (pinField pos16_fields 0) = .refused .negativeOccurrence := by
  repeat (first | constructor | rfl)

/-! §9 first failure order: field1 nested then field2 negative  > nested
carrier `[rcic_ind_positivity_nested_out_of_profile]` -/
def pos17_E : ResolvedEnv := emptyEnv
def pos17_fields : List (Expr Nat) := [(.app (.const 2 []) (.const 0 [])), (.pi (.const 0 []) (.const 1 []))]
def pos17_nuniv : Nat := 0
def pos17_nparams : Nat := 0
def pos17_nindices : Nat := 0
def pos17_kind : CorpusPinKind := .specRefuse
theorem pos17_pin :
    pos17_kind = .specRefuse ∧ fieldAnalyze pos17_E 80 0 pos17_nuniv pos17_nparams pos17_nindices (pos17_nparams + 0) (pinField pos17_fields 0) = .refused .nestedInductiveOutOfProfile ∧ fieldAnalyze pos17_E 80 0 pos17_nuniv pos17_nparams pos17_nindices (pos17_nparams + 1) (pinField pos17_fields 1) = .refused .negativeOccurrence := by
  repeat (first | constructor | rfl)

/-! §9 fuel: field pi chain depth 14 at fuel 12  > expr_has_ref_fuel
carrier `[rcic_expr_has_ref_fuel]` -/
def pos18_E : ResolvedEnv := emptyEnv
def pos18_fields : List (Expr Nat) := [(.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.pi (.sort (.succ .zero)) (.sort (.succ .zero))))))))))))))))]
def pos18_nuniv : Nat := 0
def pos18_nparams : Nat := 1
def pos18_nindices : Nat := 0
def pos18_kind : CorpusPinKind := .notSpecRefusal
theorem pos18_pin :
    pos18_kind = .notSpecRefusal ∧
    fieldAnalyze pos18_E 12 0 pos18_nuniv pos18_nparams pos18_nindices
      pos18_nparams (pinField pos18_fields 0) = .unresolved := by
  constructor <;> rfl

/-! §9 ctor shape refusal propagates: mirror S2 vs fam S1
carrier `[rcic_ind_ctor_shape_mirror_mismatch]` -/
def pos19_E : ResolvedEnv := emptyEnv
def pos19_fields : List (Expr Nat) := []
def pos19_nuniv : Nat := 0
def pos19_nparams : Nat := 1
def pos19_nindices : Nat := 0
def pos19_kind : CorpusPinKind := .notSpecRefusal
theorem pos19_pin : pos19_kind = .notSpecRefusal := rfl

/-! refuse unknown form
carrier `[rcic_ind_positivity_unknown_form]` -/
def pos20_E : ResolvedEnv := emptyEnv
def pos20_fields : List (Expr Nat) := []
def pos20_nuniv : Nat := 0
def pos20_nparams : Nat := 0
def pos20_nindices : Nat := 0
def pos20_kind : CorpusPinKind := .notSpecRefusal
theorem pos20_pin : pos20_kind = .notSpecRefusal := rfl

def occurrencePositivityPinNames : List String := [
"occ00", "occ01", "occ02", "occ03", "occ04", "occ05", "occ06", "occ07", "occ08", "occ09", "occ10", "occ11", "occ12", "occ13", "occ14", "occ15", "occ16", "occ17", "occ18", "pos00", "pos01", "pos02", "pos03", "pos04", "pos05", "pos06", "pos07", "pos08", "pos09", "pos10", "pos11", "pos12", "pos13", "pos14", "pos15", "pos16", "pos17", "pos18", "pos19", "pos20"
]
theorem occurrencePositivityPinCount :
    occurrencePositivityPinNames.length = 40 := rfl


theorem uniformProp_zero : UniformProp .zero := by
  intro ν
  rfl

theorem not_uniformProp_succ_zero : ¬ UniformProp (.succ .zero) := by
  intro h
  have := h (fun _ => 0)
  simp [evalTotal] at this

theorem not_uniformProp_succ_param0 : ¬ UniformProp (.succ (.param 0)) := by
  intro h
  have := h (fun _ => 0)
  simp [evalTotal] at this

theorem uniformType_succ_param0 : UniformType (.succ (.param 0)) := by
  intro ν
  have : evalTotal ν (.succ (.param 0)) = ν 0 + 1 := by simp [evalTotal]
  omega

theorem not_eqN_ssz_sz : ¬ eqN (.succ (.succ .zero)) (.succ .zero) := by
  intro h
  have := h (fun _ => none)
  simp [eval] at this

theorem not_leN_ssz_sz : ¬ leN (.succ (.succ .zero)) (.succ .zero) := by
  intro h
  have hx : eval (fun _ => none) (.succ (.succ .zero)) = some 2 := by simp [eval]
  have hy : eval (fun _ => none) (.succ .zero) = some 1 := by simp [eval]
  have := h (fun _ => none) 2 1 hx hy
  omega

theorem not_leN_succ3_param : ¬ leN (.succ (.succ (.succ (.param 0)))) (.succ (.param 0)) := by
  intro h
  let ρ : Nat → Option Nat := fun _ => some 0
  have hx : eval ρ (.succ (.succ (.succ (.param 0)))) = some 3 := by simp [eval, ρ]
  have hy : eval ρ (.succ (.param 0)) = some 1 := by simp [eval, ρ]
  have := h ρ 3 1 hx hy
  omega

theorem leN_of_eqN {a b : Level} (h : eqN a b) : leN a b := by
  intro ρ x y hx hy
  have hab := h ρ
  rw [hx, hy] at hab
  cases hab
  exact Nat.le_refl x

theorem eqN_succ_max_param0_zero :
    eqN (.succ (.max (.param 0) .zero)) (.succ (.param 0)) := by
  intro ρ
  cases hρ : ρ 0 with
  | none => simp [eval, hρ]
  | some n => simp [eval, hρ, Nat.max_zero]

def fu02Fam : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩
def fu02Ctor : CheckedMember :=
  ⟨.constructorM, 0, .pi (.sort (.succ .zero)) (.const 0 []), none⟩
def fu02Env : ResolvedEnv := extendEnv emptyEnv 0 fu02Fam

def fu02Family : PolicyFamilyView fu02Env where
  ref := 0
  member := fu02Fam
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def fu02FieldTy :
    HasTy fu02Env 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  HasTy.sort [] (.succ .zero)

def fu02View : PolicyConstructorView fu02Env fu02Family fu02Ctor where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.sort (.succ .zero)]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.succ .zero)
    bounded := fun _ => rfl
    hasType := fun j => by
      have hlen : ([] ++ [(.sort (.succ .zero) : Expr Nat)]).length = 1 := rfl
      have hlt : j.val < 1 := by have ht := j.isLt; simp only [hlen, List.length_append, List.length_cons, List.length_nil] at ht; exact ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp [hj, policyPrefixContext]
      exact fu02FieldTy
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

-- The refusal proof lives in `fu02_pin`, so deleting the 05 §7 level
-- test fails inside that pin rather than in a helper Lean can recover.

def fu04Fam : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
def fu04Ctor : CheckedMember :=
  ⟨.constructorM, 0, .pi (.const 0 []) (.const 0 []), none⟩
def fu04Env : ResolvedEnv := extendEnv emptyEnv 0 fu04Fam

def fu04Family : PolicyFamilyView fu04Env where
  ref := 0
  member := fu04Fam
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def fu04FieldTy :
    HasTy fu04Env 0 [] (.const 0 []) (.sort .zero) :=
  HasTy.const [] 0 [] fu04Fam rfl rfl (fun _ h => nomatch h)

def fu04View : PolicyConstructorView fu04Env fu04Family fu04Ctor where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.const 0 []]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hlen : ([] ++ [(.const 0 [] : Expr Nat)]).length = 1 := rfl
      have hlt : j.val < 1 := by have ht := j.isLt; simp only [hlen, List.length_append, List.length_cons, List.length_nil] at ht; exact ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp [hj, policyPrefixContext]
      exact fu04FieldTy
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

theorem fu04_ok : FieldUniverseAdmitted fu04View := by
  intro j
  exact Or.inl uniformProp_zero

theorem el04_sel : EliminationSelection .zero 2 True .propOnly :=
  .multipleProp uniformProp_zero (by decide)

theorem el09_safe :
    UniformProp (.succ .zero) ∨ Expr.bvar 0 ∈ [(.bvar 0 : Expr Nat)] :=
  Or.inr (List.Mem.head _)

def el07FieldLevel : Fin 2 → Level
  | ⟨0, _⟩ => .succ .zero
  | ⟨1, _⟩ => .zero

def el07Indices : List (Expr Nat) := [.bvar 3, .bvar 2]

def el07Safe : Prop :=
  ∀ j : Fin 2,
    UniformProp (el07FieldLevel j) ∨ Expr.bvar (2 - 1 - j.val) ∈ el07Indices

theorem el07_unsafe : ¬ el07Safe := by
  intro h
  have h0 := h ⟨0, by decide⟩
  rw [show el07FieldLevel ⟨0, by decide⟩ = .succ .zero from rfl] at h0
  rcases h0 with hp | hm
  · exact not_uniformProp_succ_zero hp
  · simp [el07Indices] at hm

def el10Index : Expr Nat :=
  .app (.lam (.const 1 []) (.bvar 0)) (.bvar 0)

def el10Safe : Prop :=
  UniformProp (.succ .zero) ∨ Expr.bvar 0 ∈ [el10Index]

theorem el10_unsafe : ¬ el10Safe := by
  intro h
  rcases h with hp | hm
  · exact not_uniformProp_succ_zero hp
  · simp [el10Index] at hm

def el12Safe : Prop :=
  ∀ j : Fin 2,
    UniformProp (.succ .zero) ∨ Expr.bvar (2 - 1 - j.val) ∈ [(.bvar 1 : Expr Nat)]

theorem el12_unsafe : ¬ el12Safe := by
  intro h
  have h1 := h ⟨1, by decide⟩
  rcases h1 with hp | hm
  · exact not_uniformProp_succ_zero hp
  · simp at hm

/-! fu05: parameter mirror, no fields. -/

def fu05Fam : CheckedMember :=
  ⟨.inductiveM, 0, .pi (.sort (.succ (.succ .zero))) (.sort (.succ .zero)), none⟩
def fu05Ctor : CheckedMember :=
  ⟨.constructorM, 0,
    .pi (.sort (.succ (.succ .zero))) (.app (.const 0 []) (.bvar 0)), none⟩
def fu05Env : ResolvedEnv := extendEnv emptyEnv 0 fu05Fam

def fu05FamTy :
    HasTy fu05Env 0 [] (.sort (.succ (.succ .zero)))
      (.sort (.succ (.succ (.succ .zero)))) :=
  HasTy.sort [] (.succ (.succ .zero))

def fu05Family : PolicyFamilyView fu05Env where
  ref := 0
  member := fu05Fam
  present := rfl
  hasClass := rfl
  parameters := [.sort (.succ (.succ .zero))]
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.succ (.succ .zero))
    bounded := fun _ => rfl
    hasType := fun j => by
      have hlen : [(.sort (.succ (.succ .zero)) : Expr Nat)].length = 1 := rfl
      have hlt : j.val < 1 := by have ht := j.isLt; simp only [hlen, List.length_append, List.length_cons, List.length_nil] at ht; exact ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp [hj, policyPrefixContext]
      exact fu05FamTy
  }

def fu05View : PolicyConstructorView fu05Env fu05Family fu05Ctor where
  hasClass := rfl
  arity := rfl
  parameters := [.sort (.succ (.succ .zero))]
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.succ (.succ .zero))
    bounded := fun _ => rfl
    hasType := fun j => by
      have ht := j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp [hj, policyPrefixContext]
      exact fu05FamTy
  }
  parameterMirrors := fun i => by
    have hlt : i.val < 1 := i.isLt
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    subst hi
    exact Conv.refl _ _
  noFamilyInIndices := fun _ h => nomatch h

theorem fu05_ok : FieldUniverseAdmitted fu05View :=
  fun j => j.elim0

/-! fu06: universe-poly field bvar 0, v = succ (param 0) = uI. -/

def fu06Fam : CheckedMember :=
  ⟨.inductiveM, 1,
    .pi (.sort (.succ (.param 0))) (.sort (.succ (.param 0))), none⟩
def fu06Ctor : CheckedMember :=
  ⟨.constructorM, 1,
    .pi (.sort (.succ (.param 0)))
      (.pi (.bvar 0) (.app (.const 0 [.param 0]) (.bvar 1))), none⟩
def fu06Env : ResolvedEnv := extendEnv emptyEnv 0 fu06Fam

def fu06ParamTy :
    HasTy fu06Env 1 [] (.sort (.succ (.param 0)))
      (.sort (.succ (.succ (.param 0)))) :=
  HasTy.sort [] (.succ (.param 0))

def fu06FieldTy :
    HasTy fu06Env 1 [LocalDecl.assumption (.sort (.succ (.param 0)))]
      (.bvar 0) (.sort (.succ (.param 0))) :=
  HasTy.bvar _ 0 (.sort (.succ (.param 0))) rfl

def fu06Levels : Fin 2 → Level
  | ⟨0, _⟩ => .succ (.succ (.param 0))
  | ⟨1, _⟩ => .succ (.param 0)

def fu06DomainsTyped : PolicyTelescopeTyping fu06Env 1
    [.sort (.succ (.param 0)), .bvar 0] where
  levels := fu06Levels
  bounded := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, by decide⟩ := Fin.ext h0
      subst hi
      rfl
    · have h1 : i.val = 1 := by omega
      have hi : i = ⟨1, by decide⟩ := Fin.ext h1
      subst hi
      rfl
  hasType := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, by decide⟩ := Fin.ext h0
      subst hi
      simp [policyPrefixContext]
      exact fu06ParamTy
    · have h1 : i.val = 1 := by omega
      have hi : i = ⟨1, by decide⟩ := Fin.ext h1
      subst hi
      simp [policyPrefixContext]
      exact fu06FieldTy

def fu06Family : PolicyFamilyView fu06Env where
  ref := 0
  member := fu06Fam
  present := rfl
  hasClass := rfl
  parameters := [.sort (.succ (.param 0))]
  indices := []
  resultLevel := .succ (.param 0)
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.succ (.param 0))
    bounded := fun _ => rfl
    hasType := fun j => by
      have hlt : j.val < 1 := j.isLt
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp [hj, policyPrefixContext]
      exact fu06ParamTy
  }

def fu06View : PolicyConstructorView fu06Env fu06Family fu06Ctor where
  hasClass := rfl
  arity := rfl
  parameters := [.sort (.succ (.param 0))]
  fields := [.bvar 0]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := fu06DomainsTyped
  parameterMirrors := fun i => by
    have hv : i.val = 0 := by
      have : i.val < 1 := i.isLt
      omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    subst hi
    exact Conv.refl _ _
  noFamilyInIndices := fun _ h => nomatch h

theorem fu06_ok : FieldUniverseAdmitted fu06View := by
  intro j
  have ht := j.isLt
  simp only [fu06View, List.length_cons, List.length_nil] at ht
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  subst hj
  have hlev : fu06View.fieldLevel ⟨0, by decide⟩ = .succ (.param 0) := by
    unfold PolicyConstructorView.fieldLevel PolicyConstructorView.fieldIndex
    simp [fu06View, fu06DomainsTyped, fu06Levels]
  have hres : fu06Family.resultLevel = .succ (.param 0) := rfl
  rw [hlev, hres]
  exact Or.inr ⟨uniformType_succ_param0, leN_refl _⟩

/-! fu17: monomorphic transparent alias, field const c2. -/

def fu17Fam : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩
def fu17G : CheckedMember :=
  ⟨.definitionM, 0, .sort (.succ (.succ .zero)), some (.sort (.succ .zero))⟩
def fu17C : CheckedMember := ⟨.axiomM, 0, .const 1 [], none⟩
def fu17Ctor : CheckedMember :=
  ⟨.constructorM, 0, .pi (.const 2 []) (.const 0 []), none⟩
def fu17Env : ResolvedEnv :=
  extendEnv (extendEnv (extendEnv emptyEnv 0 fu17Fam) 1 fu17G) 2 fu17C

def fu17Family : PolicyFamilyView fu17Env where
  ref := 0
  member := fu17Fam
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def fu17Delta : Conv fu17Env 0 [] (.const 1 []) (.sort (.succ .zero)) :=
  Conv.step [] (.const 1 []) (.sort (.succ .zero))
    (Step.delta [] 1 [] fu17G (.sort (.succ .zero)) rfl rfl rfl)

def fu17FieldTy : HasTy fu17Env 0 [] (.const 2 []) (.sort (.succ .zero)) :=
  HasTy.conv [] (.const 2 []) (.const 1 []) (.sort (.succ .zero))
    (HasTy.const [] 2 [] fu17C rfl rfl (fun _ h => nomatch h))
    fu17Delta

def fu17View : PolicyConstructorView fu17Env fu17Family fu17Ctor where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.const 2 []]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ .zero
    bounded := fun _ => rfl
    hasType := fun j => by
      have hv : j.val = 0 := by
        have : j.val < 1 := by have ht := j.isLt; simp only [List.length_cons, List.length_nil] at ht; exact ht
        omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp [hj, policyPrefixContext]
      exact fu17FieldTy
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

theorem fu17_ok : FieldUniverseAdmitted fu17View := by
  intro j
  have hv : j.val = 0 := by
    have : j.val < 1 := by have ht := j.isLt; simp only [List.length_cons, List.length_nil] at ht; exact ht
    omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  subst hj
  exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩



/-! ## Constructor-shape pins (24). properFamilyFuel is 05 section 6 landing. -/
/-! Nat zero landing -/
def sh00_E : ResolvedEnv := emptyEnv
def sh00_land : Expr Nat := (.const 0 [])
def sh00_kind : CorpusPinKind := .specAccept
theorem sh00_pin :
    sh00_kind = .specAccept ∧
    properFamilyFuel sh00_E 80 0 0 0 0 0 sh00_land = some true := by
  constructor <;> rfl

/-! Nat succ landing -/
def sh01_E : ResolvedEnv := emptyEnv
def sh01_land : Expr Nat := (.const 0 [])
def sh01_kind : CorpusPinKind := .specAccept
theorem sh01_pin :
    sh01_kind = .specAccept ∧
    properFamilyFuel sh01_E 80 0 0 0 0 0 sh01_land = some true := by
  constructor <;> rfl

/-! List nil landing -/
def sh02_E : ResolvedEnv := emptyEnv
def sh02_land : Expr Nat := (.app (.const 0 []) (.bvar 0))
def sh02_kind : CorpusPinKind := .specAccept
theorem sh02_pin :
    sh02_kind = .specAccept ∧
    properFamilyFuel sh02_E 80 0 0 1 0 0 sh02_land = some true := by
  constructor <;> rfl

/-! List cons landing -/
def sh03_E : ResolvedEnv := emptyEnv
def sh03_land : Expr Nat := (.app (.const 0 []) (.bvar 2))
def sh03_kind : CorpusPinKind := .specAccept
theorem sh03_pin :
    sh03_kind = .specAccept ∧
    properFamilyFuel sh03_E 80 0 0 1 0 2 sh03_land = some true := by
  constructor <;> rfl

/-! Vec nil landing -/
def sh04_E : ResolvedEnv := emptyEnv
def sh04_land : Expr Nat := (.app (.app (.const 0 []) (.bvar 0)) (.const 2 []))
def sh04_kind : CorpusPinKind := .specAccept
theorem sh04_pin :
    sh04_kind = .specAccept ∧
    properFamilyFuel sh04_E 80 0 0 1 1 0 sh04_land = some true := by
  constructor <;> rfl

/-! beta mirror; landing is the family application. The mirror reduces by whnf -/
def sh05_E : ResolvedEnv := emptyEnv
def sh05_land : Expr Nat := (.app (.const 0 []) (.bvar 2))
def sh05_kind : CorpusPinKind := .specAccept
theorem sh05_pin :
    sh05_kind = .specAccept ∧
    properFamilyFuel sh05_E 80 0 0 1 0 2 sh05_land = some true ∧
    whnfFuel sh05_E 2
      (.app (.lam (.sort (.succ (.succ .zero))) (.bvar 0)) (.sort (.succ .zero)))
      = some (.sort (.succ .zero)) := by
  repeat (first | constructor | rfl)

/-! landing accepts. Mirror Sort 2 is not eqN to parameter Sort 1, so Conv.sorts does not apply. Full negation of Conv is not claimed -/
def sh06_E : ResolvedEnv := emptyEnv
def sh06_land : Expr Nat := (.app (.const 0 []) (.bvar 0))
def sh06_kind : CorpusPinKind := .specRefuse
theorem sh06_pin :
    sh06_kind = .specRefuse ∧
    properFamilyFuel sh06_E 80 0 0 1 0 0 sh06_land = some true ∧ ¬ eqN (.succ (.succ .zero)) (.succ .zero) := by
  refine ⟨rfl, rfl, not_eqN_ssz_sz⟩

/-! no parameter telescope -/
def sh07_E : ResolvedEnv := emptyEnv
def sh07_land : Expr Nat := (.const 0 [])
def sh07_kind : CorpusPinKind := .specRefuse
theorem sh07_pin :
    sh07_kind = .specRefuse ∧
    properFamilyFuel sh07_E 80 0 0 1 0 0 sh07_land = some false := by
  constructor <;> rfl

/-! landing is a sort -/
def sh08_E : ResolvedEnv := emptyEnv
def sh08_land : Expr Nat := (.sort (.succ .zero))
def sh08_kind : CorpusPinKind := .specRefuse
theorem sh08_pin :
    sh08_kind = .specRefuse ∧
    properFamilyFuel sh08_E 80 0 0 1 0 0 sh08_land = some false := by
  constructor <;> rfl

/-! landing head is not the family -/
def sh09_E : ResolvedEnv := emptyEnv
def sh09_land : Expr Nat := (.const 1 [])
def sh09_kind : CorpusPinKind := .specRefuse
theorem sh09_pin :
    sh09_kind = .specRefuse ∧
    properFamilyFuel sh09_E 80 0 0 1 0 0 sh09_land = some false := by
  constructor <;> rfl

/-! family constant with no arguments -/
def sh10_E : ResolvedEnv := emptyEnv
def sh10_land : Expr Nat := (.const 0 [])
def sh10_kind : CorpusPinKind := .specRefuse
theorem sh10_pin :
    sh10_kind = .specRefuse ∧
    properFamilyFuel sh10_E 80 0 0 1 0 0 sh10_land = some false := by
  constructor <;> rfl

/-! over-applied family -/
def sh11_E : ResolvedEnv := emptyEnv
def sh11_land : Expr Nat := (.app (.const 0 []) (.sort .zero))
def sh11_kind : CorpusPinKind := .specRefuse
theorem sh11_pin :
    sh11_kind = .specRefuse ∧
    properFamilyFuel sh11_E 80 0 0 0 0 0 sh11_land = some false := by
  constructor <;> rfl

/-! parameter is a redex, not the exact local -/
def sh12_E : ResolvedEnv := emptyEnv
def sh12_land : Expr Nat := (.app (.const 0 []) (.app (.lam (.sort (.succ (.succ .zero))) (.bvar 0)) (.bvar 2)))
def sh12_kind : CorpusPinKind := .specRefuse
theorem sh12_pin :
    sh12_kind = .specRefuse ∧
    properFamilyFuel sh12_E 80 0 0 1 0 2 sh12_land = some false := by
  constructor <;> rfl

/-! parameter local is the wrong bvar -/
def sh13_E : ResolvedEnv := emptyEnv
def sh13_land : Expr Nat := (.app (.const 0 []) (.bvar 0))
def sh13_kind : CorpusPinKind := .specRefuse
theorem sh13_pin :
    sh13_kind = .specRefuse ∧
    properFamilyFuel sh13_E 80 0 0 1 0 2 sh13_land = some false := by
  constructor <;> rfl

/-! index contains the family under a Pi -/
def sh14_E : ResolvedEnv := emptyEnv
def sh14_land : Expr Nat := (.app (.const 0 []) (.pi (.sort .zero) (.app (.const 0 []) (.bvar 0))))
def sh14_kind : CorpusPinKind := .specRefuse
theorem sh14_pin :
    sh14_kind = .specRefuse ∧
    properFamilyFuel sh14_E 80 0 0 0 1 0 sh14_land = some false := by
  constructor <;> rfl

/-! index contains the family under a let -/
def sh15_E : ResolvedEnv := emptyEnv
def sh15_land : Expr Nat := (.app (.const 0 []) (.letE (.sort .zero) (.const 0 []) (.bvar 0)))
def sh15_kind : CorpusPinKind := .specRefuse
theorem sh15_pin :
    sh15_kind = .specRefuse ∧
    properFamilyFuel sh15_E 80 0 0 0 1 0 sh15_land = some false := by
  constructor <;> rfl

/-! canonical level vector -/
def sh16_E : ResolvedEnv := emptyEnv
def sh16_land : Expr Nat := (.app (.const 0 [(.param 0)]) (.bvar 0))
def sh16_kind : CorpusPinKind := .specAccept
theorem sh16_pin :
    sh16_kind = .specAccept ∧
    properFamilyFuel sh16_E 80 0 1 1 0 0 sh16_land = some true := by
  constructor <;> rfl

/-! empty level vector -/
def sh17_E : ResolvedEnv := emptyEnv
def sh17_land : Expr Nat := (.app (.const 0 []) (.bvar 0))
def sh17_kind : CorpusPinKind := .specRefuse
theorem sh17_pin :
    sh17_kind = .specRefuse ∧
    properFamilyFuel sh17_E 80 0 1 1 0 0 sh17_land = some false := by
  constructor <;> rfl

/-! max level is not the canonical param -/
def sh18_E : ResolvedEnv := emptyEnv
def sh18_land : Expr Nat := (.app (.const 0 [(.max (.param 0) (.param 0))]) (.bvar 0))
def sh18_kind : CorpusPinKind := .specRefuse
theorem sh18_pin :
    sh18_kind = .specRefuse ∧
    properFamilyFuel sh18_E 80 0 1 1 0 0 sh18_land = some false := by
  constructor <;> rfl

/-! level vector longer than nuniv -/
def sh19_E : ResolvedEnv := emptyEnv
def sh19_land : Expr Nat := (.app (.const 0 [(.param 0), (.param 0)]) (.bvar 0))
def sh19_kind : CorpusPinKind := .specRefuse
theorem sh19_pin :
    sh19_kind = .specRefuse ∧
    properFamilyFuel sh19_E 80 0 1 1 0 0 sh19_land = some false := by
  constructor <;> rfl

/-! mixed family is a telescope residue, not a section-6 landing refusal -/
def sh20_E : ResolvedEnv := emptyEnv
def sh20_land : Expr Nat := (.const 0 [])
def sh20_kind : CorpusPinKind := .notSpecRefusal
theorem sh20_pin :
    sh20_kind = .notSpecRefusal ∧
    properFamilyFuel sh20_E 80 0 1 0 0 0 sh20_land = some false := by
  constructor <;> rfl

/-! index scan ran out of bound -/
def sh21_E : ResolvedEnv := emptyEnv
def sh21_land : Expr Nat := (.app (.const 0 []) (.pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.pi (.sort .zero) (.sort .zero))))))))))))))))
def sh21_kind : CorpusPinKind := .notSpecRefusal
theorem sh21_pin :
    sh21_kind = .notSpecRefusal ∧
    properFamilyFuel sh21_E 12 0 0 0 1 0 sh21_land = none := by
  constructor <;> rfl

/-! the fuel bound is not a section-6 class; the landing is already determined -/
def sh22_E : ResolvedEnv := emptyEnv
def sh22_land : Expr Nat := (.app (.const 0 []) (.bvar 2))
def sh22_kind : CorpusPinKind := .notSpecRefusal
theorem sh22_pin :
    sh22_kind = .notSpecRefusal ∧
    properFamilyFuel sh22_E 2 0 0 1 0 2 sh22_land = some true := by
  constructor <;> rfl

/-! unknown_form is not a section-6 class -/
def sh23_E : ResolvedEnv := emptyEnv
def sh23_land : Expr Nat := (.const 0 [])
def sh23_kind : CorpusPinKind := .notSpecRefusal
theorem sh23_pin :
    sh23_kind = .notSpecRefusal ∧
    properFamilyFuel sh23_E 80 0 0 1 0 0 sh23_land = some false := by
  constructor <;> rfl


/-! ## Field-universe pins. The judgment is FieldUniverseAdmitted. -/

def fu03Fam : CheckedMember := ⟨.inductiveM, 0, .sort .zero, none⟩
def fu03Ctor : CheckedMember :=
  ⟨.constructorM, 0, .pi (.sort (.succ .zero)) (.const 0 []), none⟩
def fu03Env : ResolvedEnv := extendEnv emptyEnv 0 fu03Fam

def fu03Family : PolicyFamilyView fu03Env where
  ref := 0
  member := fu03Fam
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def fu03View : PolicyConstructorView fu03Env fu03Family fu03Ctor where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.sort (.succ .zero)]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.succ .zero)
    bounded := fun _ => rfl
    hasType := fun j => by
      have ht := j.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at ht
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp [hj, policyPrefixContext]
      exact HasTy.sort [] (.succ .zero)
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

theorem fu03_ok : FieldUniverseAdmitted fu03View :=
  fun _ => Or.inl uniformProp_zero

def fu07Field : Expr Nat := .sort (.max (.param 0) .zero)

def fu07Levels : Fin 2 → Level
  | ⟨0, _⟩ => .succ (.succ (.param 0))
  | ⟨1, _⟩ => .succ (.max (.param 0) .zero)

def fu07FieldTy :
    HasTy fu06Env 1 [LocalDecl.assumption (.sort (.succ (.param 0)))]
      fu07Field (.sort (.succ (.max (.param 0) .zero))) :=
  HasTy.sort _ (.max (.param 0) .zero)

def fu07DomainsTyped : PolicyTelescopeTyping fu06Env 1
    [.sort (.succ (.param 0)), fu07Field] where
  levels := fu07Levels
  bounded := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, by decide⟩ := Fin.ext h0
      subst hi; rfl
    · have h1 : i.val = 1 := by omega
      have hi : i = ⟨1, by decide⟩ := Fin.ext h1
      subst hi; rfl
  hasType := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, by decide⟩ := Fin.ext h0
      subst hi
      simp [policyPrefixContext]
      exact fu06ParamTy
    · have h1 : i.val = 1 := by omega
      have hi : i = ⟨1, by decide⟩ := Fin.ext h1
      subst hi
      simp [policyPrefixContext, fu07Field]
      exact fu07FieldTy

def fu07Ctor : CheckedMember :=
  ⟨.constructorM, 1,
    .pi (.sort (.succ (.param 0)))
      (.pi fu07Field (.app (.const 0 [.param 0]) (.bvar 1))), none⟩

def fu07View : PolicyConstructorView fu06Env fu06Family fu07Ctor where
  hasClass := rfl
  arity := rfl
  parameters := [.sort (.succ (.param 0))]
  fields := [fu07Field]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := fu07DomainsTyped
  parameterMirrors := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    subst hi
    exact Conv.refl _ _
  noFamilyInIndices := fun _ h => nomatch h

theorem fu07_ok : FieldUniverseAdmitted fu07View := by
  intro j
  have ht := j.isLt
  simp only [fu07View, List.length_cons, List.length_nil] at ht
  have hv : j.val = 0 := by omega
  have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
  subst hj
  have hlev : fu07View.fieldLevel ⟨0, by decide⟩ = .succ (.max (.param 0) .zero) := by
    unfold PolicyConstructorView.fieldLevel PolicyConstructorView.fieldIndex
    simp [fu07View, fu07DomainsTyped, fu07Levels]
  have hres : fu06Family.resultLevel = .succ (.param 0) := rfl
  rw [hlev, hres]
  exact Or.inr ⟨uniformType_succ_param0, leN_of_eqN eqN_succ_max_param0_zero⟩

def fu08Field : Expr Nat := .sort (.succ (.succ (.param 0)))

def fu08Levels : Fin 2 → Level
  | ⟨0, _⟩ => .succ (.succ (.param 0))
  | ⟨1, _⟩ => .succ (.succ (.succ (.param 0)))

def fu08FieldTy :
    HasTy fu06Env 1 [LocalDecl.assumption (.sort (.succ (.param 0)))]
      fu08Field (.sort (.succ (.succ (.succ (.param 0))))) :=
  HasTy.sort _ (.succ (.succ (.param 0)))

def fu08DomainsTyped : PolicyTelescopeTyping fu06Env 1
    [.sort (.succ (.param 0)), fu08Field] where
  levels := fu08Levels
  bounded := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, by decide⟩ := Fin.ext h0
      subst hi; rfl
    · have h1 : i.val = 1 := by omega
      have hi : i = ⟨1, by decide⟩ := Fin.ext h1
      subst hi; rfl
  hasType := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, by decide⟩ := Fin.ext h0
      subst hi
      simp [policyPrefixContext]
      exact fu06ParamTy
    · have h1 : i.val = 1 := by omega
      have hi : i = ⟨1, by decide⟩ := Fin.ext h1
      subst hi
      simp [policyPrefixContext, fu08Field]
      exact fu08FieldTy

def fu08Ctor : CheckedMember :=
  ⟨.constructorM, 1,
    .pi (.sort (.succ (.param 0)))
      (.pi fu08Field (.app (.const 0 [.param 0]) (.bvar 1))), none⟩

def fu08View : PolicyConstructorView fu06Env fu06Family fu08Ctor where
  hasClass := rfl
  arity := rfl
  parameters := [.sort (.succ (.param 0))]
  fields := [fu08Field]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := fu08DomainsTyped
  parameterMirrors := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    subst hi
    exact Conv.refl _ _
  noFamilyInIndices := fun _ h => nomatch h

-- The refusal proof lives in `fu08_pin`.

def fu01Fam : CheckedMember :=
  ⟨.inductiveM, 0, .pi (.sort (.succ .zero)) (.sort (.succ .zero)), none⟩
def fu01Ctor : CheckedMember :=
  ⟨.constructorM, 0,
    .pi (.sort (.succ .zero))
      (.pi (.bvar 0)
        (.pi (.app (.const 0 []) (.bvar 1))
          (.app (.const 0 []) (.bvar 2)))), none⟩
def fu01Env : ResolvedEnv := extendEnv emptyEnv 0 fu01Fam
def fu01Ctx : LCtx :=
  [LocalDecl.assumption (.bvar 0), LocalDecl.assumption (.sort (.succ .zero))]

def fu01AppTy :
    HasTy fu01Env 0 fu01Ctx (.app (.const 0 []) (.bvar 1)) (.sort (.succ .zero)) :=
  HasTy.app fu01Ctx (.const 0 []) (.bvar 1)
    (.sort (.succ .zero)) (.sort (.succ .zero))
    (HasTy.const fu01Ctx 0 [] fu01Fam rfl rfl (fun _ h => nomatch h))
    (HasTy.bvar fu01Ctx 1 (.sort (.succ .zero)) rfl)

def fu01BvarTy :
    HasTy fu01Env 0 [LocalDecl.assumption (.sort (.succ .zero))]
      (.bvar 0) (.sort (.succ .zero)) :=
  HasTy.bvar _ 0 (.sort (.succ .zero)) rfl

def fu01ParamTy :
    HasTy fu01Env 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  HasTy.sort [] (.succ .zero)

def fu01Domains : List (Expr Nat) :=
  [.sort (.succ .zero), .bvar 0, .app (.const 0 []) (.bvar 1)]

def fu01Levels : Fin 3 → Level
  | ⟨0, _⟩ => .succ (.succ .zero)
  | ⟨1, _⟩ => .succ .zero
  | ⟨2, _⟩ => .succ .zero

def fu01DomainsTyped : PolicyTelescopeTyping fu01Env 0 fu01Domains where
  levels := fu01Levels
  bounded := fun i => by
    have ht := i.isLt
    simp only [fu01Domains, List.length_cons, List.length_nil] at ht
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, by decide⟩ := Fin.ext h0
      subst hi; rfl
    · by_cases h1 : i.val = 1
      · have hi : i = ⟨1, by decide⟩ := Fin.ext h1
        subst hi; rfl
      · have h2 : i.val = 2 := by omega
        have hi : i = ⟨2, by decide⟩ := Fin.ext h2
        subst hi; rfl
  hasType := fun i => by
    have ht := i.isLt
    simp only [fu01Domains, List.length_cons, List.length_nil] at ht
    by_cases h0 : i.val = 0
    · have hi : i = ⟨0, by decide⟩ := Fin.ext h0
      subst hi
      simp [policyPrefixContext, fu01Domains]
      exact fu01ParamTy
    · by_cases h1 : i.val = 1
      · have hi : i = ⟨1, by decide⟩ := Fin.ext h1
        subst hi
        simp [policyPrefixContext, fu01Domains]
        exact fu01BvarTy
      · have h2 : i.val = 2 := by omega
        have hi : i = ⟨2, by decide⟩ := Fin.ext h2
        subst hi
        simp [policyPrefixContext, fu01Domains, fu01Ctx]
        exact fu01AppTy

def fu01Family : PolicyFamilyView fu01Env where
  ref := 0
  member := fu01Fam
  present := rfl
  hasClass := rfl
  parameters := [.sort (.succ .zero)]
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .succ (.succ .zero)
    bounded := fun _ => rfl
    hasType := fun j => by
      have hlt : j.val < 1 := j.isLt
      have hv : j.val = 0 := by omega
      have hj : j = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
      simp [hj, policyPrefixContext]
      exact fu01ParamTy
  }

def fu01View : PolicyConstructorView fu01Env fu01Family fu01Ctor where
  hasClass := rfl
  arity := rfl
  parameters := [.sort (.succ .zero)]
  fields := [.bvar 0, .app (.const 0 []) (.bvar 1)]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := fu01DomainsTyped
  parameterMirrors := fun i => by
    have ht := i.isLt
    simp only [List.length_cons, List.length_nil] at ht
    have hv : i.val = 0 := by omega
    have hi : i = ⟨0, Nat.lt_succ_self _⟩ := Fin.ext hv
    subst hi
    exact Conv.refl _ _
  noFamilyInIndices := fun _ h => nomatch h

theorem fu01_ok : FieldUniverseAdmitted fu01View := by
  intro j
  have ht := j.isLt
  simp only [fu01View, List.length_cons, List.length_nil] at ht
  have hc : j.val = 0 ∨ j.val = 1 := by omega
  have hres : fu01Family.resultLevel = .succ .zero := rfl
  rcases hc with h0 | h1
  · have hj : j = ⟨0, by decide⟩ := Fin.ext h0
    subst hj
    have hlev : fu01View.fieldLevel ⟨0, by decide⟩ = .succ .zero := by
      unfold PolicyConstructorView.fieldLevel PolicyConstructorView.fieldIndex
      simp [fu01View, fu01DomainsTyped, fu01Levels]
    rw [hlev, hres]
    exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩
  · have hj : j = ⟨1, by decide⟩ := Fin.ext h1
    subst hj
    have hlev : fu01View.fieldLevel ⟨1, by decide⟩ = .succ .zero := by
      unfold PolicyConstructorView.fieldLevel PolicyConstructorView.fieldIndex
      simp [fu01View, fu01DomainsTyped, fu01Levels]
    rw [hlev, hres]
    exact Or.inr ⟨uniformType_succ_zero, leN_refl _⟩

def fu00_kind : CorpusPinKind := .specAccept
theorem fu00_pin :
    fu00_kind = .specAccept ∧ FieldUniverseAdmitted natGroupSucc :=
  ⟨rfl, natSuccUniverse⟩

def fu01_kind : CorpusPinKind := .specAccept
theorem fu01_pin :
    fu01_kind = .specAccept ∧ FieldUniverseAdmitted fu01View :=
  ⟨rfl, fu01_ok⟩

def fu02_kind : CorpusPinKind := .specRefuse
theorem fu02_pin :
    fu02_kind = .specRefuse ∧ ¬ FieldUniverseAdmitted fu02View := by
  refine ⟨rfl, ?_⟩
  intro h
  have h0 := h ⟨0, by decide⟩
  have hlev : fu02View.fieldLevel ⟨0, by decide⟩ = .succ (.succ .zero) := rfl
  rw [hlev] at h0
  have hu : (fu02Family.resultLevel) = .succ .zero := rfl
  rw [hu] at h0
  rcases h0 with hp | ⟨_, hl⟩
  · exact not_uniformProp_succ_zero hp
  · exact not_leN_ssz_sz hl

theorem fu02_refused : ¬ FieldUniverseAdmitted fu02View :=
  fu02_pin.2

def fu03_kind : CorpusPinKind := .specAccept
theorem fu03_pin :
    fu03_kind = .specAccept ∧ FieldUniverseAdmitted fu03View :=
  ⟨rfl, fu03_ok⟩

def fu04_kind : CorpusPinKind := .specAccept
theorem fu04_pin :
    fu04_kind = .specAccept ∧ FieldUniverseAdmitted fu04View :=
  ⟨rfl, fu04_ok⟩

def fu05_kind : CorpusPinKind := .specAccept
theorem fu05_pin :
    fu05_kind = .specAccept ∧ FieldUniverseAdmitted fu05View :=
  ⟨rfl, fu05_ok⟩

def fu06_kind : CorpusPinKind := .specAccept
theorem fu06_pin :
    fu06_kind = .specAccept ∧ FieldUniverseAdmitted fu06View :=
  ⟨rfl, fu06_ok⟩

def fu07_kind : CorpusPinKind := .specAccept
theorem fu07_pin :
    fu07_kind = .specAccept ∧ FieldUniverseAdmitted fu07View :=
  ⟨rfl, fu07_ok⟩

def fu08_kind : CorpusPinKind := .specRefuse
theorem fu08_pin :
    fu08_kind = .specRefuse ∧ ¬ FieldUniverseAdmitted fu08View := by
  refine ⟨rfl, ?_⟩
  intro h
  have h0 := h ⟨0, by decide⟩
  have hlev : fu08View.fieldLevel ⟨0, by decide⟩ =
      .succ (.succ (.succ (.param 0))) := by
    unfold PolicyConstructorView.fieldLevel PolicyConstructorView.fieldIndex
    simp [fu08View, fu08DomainsTyped, fu08Levels]
  have hres : fu06Family.resultLevel = .succ (.param 0) := rfl
  rw [hlev, hres] at h0
  rcases h0 with hp | ⟨_, hl⟩
  · exact not_uniformProp_succ_param0 hp
  · exact not_leN_succ3_param hl

theorem fu08_refused : ¬ FieldUniverseAdmitted fu08View :=
  fu08_pin.2

/-- The field expression is a term. PolicyTelescopeTyping does not apply,
and no negation of HasTy at a sort is claimed. -/
def fu09_kind : CorpusPinKind := .notSpecRefusal
theorem fu09_pin : fu09_kind = .notSpecRefusal := rfl

def fu10_kind : CorpusPinKind := .notSpecRefusal
theorem fu10_pin : fu10_kind = .notSpecRefusal := rfl

def fu11_kind : CorpusPinKind := .notSpecRefusal
theorem fu11_pin : fu11_kind = .notSpecRefusal := rfl

def fu12_kind : CorpusPinKind := .notSpecRefusal
theorem fu12_pin :
    fu12_kind = .notSpecRefusal ∧ ¬ eqN (.succ (.succ .zero)) (.succ .zero) :=
  ⟨rfl, not_eqN_ssz_sz⟩

def fu13_kind : CorpusPinKind := .notSpecRefusal
theorem fu13_pin :
    fu13_kind = .notSpecRefusal ∧ FieldUniverseAdmitted fu01View :=
  ⟨rfl, fu01_ok⟩

def fu14_kind : CorpusPinKind := .notSpecRefusal
theorem fu14_pin : fu14_kind = .notSpecRefusal := rfl

def fu15_kind : CorpusPinKind := .notSpecRefusal
theorem fu15_pin : fu15_kind = .notSpecRefusal := rfl

/-- Same constructor as fu06. The unreachable polymorphic definition is
not an argument of FieldUniverseAdmitted. -/
def fu16_kind : CorpusPinKind := .specAccept
theorem fu16_pin :
    fu16_kind = .specAccept ∧ FieldUniverseAdmitted fu06View :=
  ⟨rfl, fu06_ok⟩

def fu17_kind : CorpusPinKind := .specAccept
theorem fu17_pin :
    fu17_kind = .specAccept ∧ FieldUniverseAdmitted fu17View :=
  ⟨rfl, fu17_ok⟩

def fu18_kind : CorpusPinKind := .notSpecRefusal
theorem fu18_pin : fu18_kind = .notSpecRefusal := rfl

/-! ## Elimination pins. The judgment is EliminationSelection. -/

def el06Safe : Prop :=
  ∀ j : Fin 2,
    UniformProp .zero ∨ Expr.bvar (2 - 1 - j.val) ∈ ([] : List (Expr Nat))

theorem el06_safe : el06Safe := fun _ => Or.inl uniformProp_zero

def el05Safe : Prop :=
  ∀ _ : Fin 0, UniformProp .zero ∨ Expr.bvar 0 ∈ ([] : List (Expr Nat))

theorem el05_safe : el05Safe := fun j => j.elim0

def el09Safe : Prop :=
  UniformProp (.succ .zero) ∨ Expr.bvar 0 ∈ [(.bvar 0 : Expr Nat)]

theorem el09_proved : el09Safe := el09_safe

def el11Index : Expr Nat := .app (.const 2 []) (.bvar 0)

def el11Safe : Prop :=
  UniformProp (.succ .zero) ∨ Expr.bvar 0 ∈ [el11Index]

theorem el11_unsafe : ¬ el11Safe := by
  intro h
  rcases h with hp | hm
  · exact not_uniformProp_succ_zero hp
  · simp [el11Index] at hm

theorem mixed_param0 : MixedUniverse (.param 0) := by
  constructor
  · intro h
    have := h (fun _ => 1)
    simp [evalTotal] at this
  · intro h
    have := h (fun _ => 0)
    simp [evalTotal] at this

def el00_kind : CorpusPinKind := .specAccept
theorem el00_pin :
    el00_kind = .specAccept ∧
    EliminationSelection (.succ .zero) 2 True .anySort :=
  ⟨rfl, .uniformType uniformType_succ_zero⟩

def el01_kind : CorpusPinKind := .specAccept
theorem el01_pin :
    el01_kind = .specAccept ∧
    EliminationSelection (.succ (.param 0)) 1 True .anySort :=
  ⟨rfl, .uniformType uniformType_succ_param0⟩

def el02_kind : CorpusPinKind := .specAccept
theorem el02_pin :
    el02_kind = .specAccept ∧
    EliminationSelection (.succ .zero) 0 True .anySort :=
  ⟨rfl, .uniformType uniformType_succ_zero⟩

def el03_kind : CorpusPinKind := .specAccept
theorem el03_pin :
    el03_kind = .specAccept ∧
    EliminationSelection .zero 0 True .anySort :=
  ⟨rfl, .emptyProp uniformProp_zero rfl⟩

def el04_kind : CorpusPinKind := .specAccept
theorem el04_pin :
    el04_kind = .specAccept ∧
    EliminationSelection .zero 2 True .propOnly :=
  ⟨rfl, .multipleProp uniformProp_zero (by decide)⟩

def el05_kind : CorpusPinKind := .specAccept
theorem el05_pin :
    el05_kind = .specAccept ∧
    EliminationSelection .zero 1 el05Safe .anySort :=
  ⟨rfl, .singletonProp uniformProp_zero rfl el05_safe⟩

def el06_kind : CorpusPinKind := .specAccept
theorem el06_pin :
    el06_kind = .specAccept ∧
    EliminationSelection .zero 1 el06Safe .anySort :=
  ⟨rfl, .singletonProp uniformProp_zero rfl el06_safe⟩

def el07_kind : CorpusPinKind := .specAccept
theorem el07_pin :
    el07_kind = .specAccept ∧
    EliminationSelection .zero 1 el07Safe .propOnly :=
  ⟨rfl, .hiddenDataProp uniformProp_zero rfl el07_unsafe⟩

def el08_kind : CorpusPinKind := .specAccept
theorem el08_pin :
    el08_kind = .specAccept ∧
    EliminationSelection .zero 1 el05Safe .anySort :=
  ⟨rfl, .singletonProp uniformProp_zero rfl el05_safe⟩

def el09_kind : CorpusPinKind := .specAccept
theorem el09_pin :
    el09_kind = .specAccept ∧
    EliminationSelection .zero 1 el09Safe .anySort :=
  ⟨rfl, .singletonProp uniformProp_zero rfl el09_proved⟩

def el10_kind : CorpusPinKind := .specAccept
theorem el10_pin :
    el10_kind = .specAccept ∧
    EliminationSelection .zero 1 el10Safe .propOnly :=
  ⟨rfl, .hiddenDataProp uniformProp_zero rfl el10_unsafe⟩

def el11_kind : CorpusPinKind := .specAccept
theorem el11_pin :
    el11_kind = .specAccept ∧
    EliminationSelection .zero 1 el11Safe .propOnly :=
  ⟨rfl, .hiddenDataProp uniformProp_zero rfl el11_unsafe⟩

def el12_kind : CorpusPinKind := .specAccept
theorem el12_pin :
    el12_kind = .specAccept ∧
    EliminationSelection .zero 1 el12Safe .propOnly :=
  ⟨rfl, .hiddenDataProp uniformProp_zero rfl el12_unsafe⟩

def el13_kind : CorpusPinKind := .notSpecRefusal
theorem el13_pin :
    el13_kind = .notSpecRefusal ∧
    EliminationSelection (.succ .zero) 1 True .anySort :=
  ⟨rfl, .uniformType uniformType_succ_zero⟩

def el14_kind : CorpusPinKind := .notSpecRefusal
theorem el14_pin :
    el14_kind = .notSpecRefusal ∧
    EliminationSelection (.succ .zero) 1 True .anySort :=
  ⟨rfl, .uniformType uniformType_succ_zero⟩

def el15_kind : CorpusPinKind := .notSpecRefusal
theorem el15_pin :
    el15_kind = .notSpecRefusal ∧
    EliminationSelection (.succ .zero) 1 True .anySort :=
  ⟨rfl, .uniformType uniformType_succ_zero⟩

def el16_kind : CorpusPinKind := .notSpecRefusal
theorem el16_pin :
    el16_kind = .notSpecRefusal ∧ MixedUniverse (.param 0) :=
  ⟨rfl, mixed_param0⟩

def el17_kind : CorpusPinKind := .notSpecRefusal
theorem el17_pin :
    el17_kind = .notSpecRefusal ∧
    EliminationSelection .zero 2 True .propOnly :=
  ⟨rfl, .multipleProp uniformProp_zero (by decide)⟩

def el18_kind : CorpusPinKind := .specAccept
theorem el18_pin :
    el18_kind = .specAccept ∧
    EliminationSelection .zero 2 True .propOnly :=
  ⟨rfl, .multipleProp uniformProp_zero (by decide)⟩

def el19_kind : CorpusPinKind := .notSpecRefusal
theorem el19_pin : el19_kind = .notSpecRefusal := rfl

def shapePinNames : List String := [
"sh00", "sh01", "sh02", "sh03", "sh04", "sh05", "sh06", "sh07", "sh08", "sh09", "sh10", "sh11", "sh12", "sh13", "sh14", "sh15", "sh16", "sh17", "sh18", "sh19", "sh20", "sh21", "sh22", "sh23"]
def fieldUniversePinNames : List String := [
"fu00", "fu01", "fu02", "fu03", "fu04", "fu05", "fu06", "fu07", "fu08", "fu09", "fu10", "fu11", "fu12", "fu13", "fu14", "fu15", "fu16", "fu17", "fu18"]
def elimPinNames : List String := [
"el00", "el01", "el02", "el03", "el04", "el05", "el06", "el07", "el08", "el09", "el10", "el11", "el12", "el13", "el14", "el15", "el16", "el17", "el18", "el19"]

theorem shapePinCount : shapePinNames.length = 24 := rfl
theorem fieldUniversePinCount : fieldUniversePinNames.length = 19 := rfl
theorem elimPinCount : elimPinNames.length = 20 := rfl

theorem corpusPinCount :
    (occurrencePositivityPinNames ++ shapePinNames ++
      fieldUniversePinNames ++ elimPinNames).length = 103 := rfl

/-! ## 04 §1 contiguity, outside the 103 carrier rows.

The carrier rows do not name `CtorContiguous`. These two pins are the
accept and the refusal of that clause: a constructor directly after its
family, and a non-constructor sitting in the open interval. -/

def contigFam : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩
def contigCtor : CheckedMember := ⟨.constructorM, 0, .const 0 [], none⟩
def contigGap : CheckedMember := ⟨.definitionM, 0, .sort .zero, none⟩
def contigOkEnv : ResolvedEnv := extendEnv emptyEnv 0 contigFam
def contigBadEnv : ResolvedEnv := extendEnv contigOkEnv 1 contigGap

def contigAccept_kind : CorpusPinKind := .specAccept
theorem contigAccept_pin :
    contigAccept_kind = .specAccept ∧ CtorContiguous contigOkEnv 1 contigCtor := by
  refine ⟨rfl, 0, rfl, by decide, ?_, ?_⟩
  · intro c hl hr
    cases c with
    | zero => exact (Nat.lt_irrefl 0 hl).elim
    | succ n =>
        cases hr with
        | step h => cases h
  · intro c hex
    rcases hex with ⟨cm, hm, hc, _⟩
    match c with
    | 0 =>
        simp [contigOkEnv, extendEnv, emptyEnv] at hm
        cases hm
        unfold contigFam at hc
        cases hc
    | _ + 1 =>
        simp [contigOkEnv, extendEnv, emptyEnv] at hm

def contigRefuse_kind : CorpusPinKind := .specRefuse
theorem contigRefuse_pin :
    contigRefuse_kind = .specRefuse ∧ ¬ CtorContiguous contigBadEnv 2 contigCtor := by
  refine ⟨rfl, ?_⟩
  intro h
  rcases h with ⟨f, hf, _, hmid, _⟩
  have hf0 : memberFamRef contigCtor = some 0 := rfl
  rw [hf0] at hf
  cases hf
  have h1 := hmid 1 (by decide) (by decide)
  rcases h1 with ⟨cm, hm, hc, _⟩
  have hm1 : contigBadEnv.members 1 = some contigGap := by
    simp [contigBadEnv, contigOkEnv, extendEnv]
  rw [hm1] at hm
  cases hm
  unfold contigGap at hc
  cases hc

end Rcic.Declarative
