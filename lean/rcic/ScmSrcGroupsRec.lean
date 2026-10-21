import rcic.ScmSrcGroupsAdm

/-! ## K3c regroup stage 1b-ii: recursor admissions

`inferSpine2` extends Adm's `inferSpine` with nonempty-level `.const`
arguments (`HasTy.const`'s arity + level-wellformedness premises) and
`.lam` (`HasTy.lam`), still returning derivations so it is sound by
construction. Kept separate from Adm so the recursor work iterates
without re-elaborating Adm's constructor batch. -/

namespace Rcic.Scm.SrcG
open Rcic.Declarative Rcic.Machine

set_option maxRecDepth 8192

/-- `HasTy.const`'s level-wellformedness premise, decided per level:
either the level mentions a `param` (fails the empty-ρ eval) or `n > 0`
supplies the bound witness. -/
theorem levelWf_const_of {n : Nat} {l : Level}
    (h : (decide (eval (fun _ => none) l = none) ||
        decide (0 < n)) = true) :
    ∃ k, eval (fun _ => none) l = none ∨ k < n := by
  cases he : decide (eval (fun _ => none) l = none) with
  | true => exact ⟨0, Or.inl (of_decide_eq_true he)⟩
  | false =>
      rw [he, Bool.false_or] at h
      exact ⟨0, Or.inr (of_decide_eq_true h)⟩

/-- Verified inference for the literal-bearing fragment. -/
def inferSpine2 {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc) :
    (e : Expr Nat) → Option (Σ' T, HasTy E n Γ e T)
  | .bvar i =>
      match h : lookupType Γ i with
      | some T => some ⟨T, .bvar Γ i T h⟩
      | none => none
  | .const r ls =>
      match hm : E.members r with
      | some m =>
          if hl : ls.length = m.arity then
            if hw : ls.all (fun l =>
                decide (eval (fun _ => none) l = none) ||
                  decide (0 < n)) then
              some ⟨instantiateLevels ls m.mtype,
                .const Γ r ls m hm hl (fun l hm' =>
                  levelWf_const_of ((List.all_eq_true.mp hw) l hm'))⟩
            else none
          else none
      | none => none
  | .lit t => some ⟨.const 0 [], hasTyLit h1 h2 t⟩
  | .pi A B =>
      match inferSpine2 h1 h2 A with
      | some ⟨.sort u, hA⟩ =>
          match inferSpine2 (Γ := LocalDecl.assumption A :: Γ) h1 h2 B with
          | some ⟨.sort v, hB⟩ =>
              some ⟨.sort (.imax u v), .pi Γ A u B v hA hB⟩
          | _ => none
      | _ => none
  | .lam A b =>
      match inferSpine2 h1 h2 A with
      | some ⟨.sort u, hA⟩ =>
          match inferSpine2 (Γ := LocalDecl.assumption A :: Γ) h1 h2 b with
          | some ⟨B, hb⟩ =>
              some ⟨.pi A B, .lam Γ A u b B hA hb⟩
          | none => none
      | _ => none
  | .app f a =>
      match inferSpine2 h1 h2 f with
      | some ⟨.pi A B, hf⟩ =>
          match inferSpine2 h1 h2 a with
          | some ⟨Ta, ha⟩ =>
              if heq : Ta = A then
                some ⟨instantiate0 a B, .app Γ f a A B hf (heq ▸ ha)⟩
              else none
          | none => none
      | _ => none
  | _ => none

/-- `inferSpine2`'s result is the derivation it carries. -/
def hasTy_of_inferSpine2_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (h1 : E.members 1 = some mZero) (h2 : E.members 2 = some mSucc)
    {e T : Expr Nat}
    (h : (inferSpine2 (n := n) (Γ := Γ) h1 h2 e).map (·.1) = some T) :
    HasTy E n Γ e T := by
  cases hs : inferSpine2 (n := n) (Γ := Γ) h1 h2 e with
  | none => rw [hs] at h; contradiction
  | some s =>
      rw [hs] at h
      change some s.1 = some T at h
      rw [← Option.some.inj h]
      exact s.2

/-- The `inferCert` result's declared type — `inferCert` carries the
`HasTy` derivation, so extraction is sound by construction. Used for
clauses whose right-hand side is too large for `inferSpine2`'s
`decide` in kernel `whnf`. -/
def inferCertTy (E : ResolvedEnv) (n : Nat) (B : Nat) (Γ : LCtx)
    (e : Expr Nat) : Option (Expr Nat) :=
  match inferCert E n B Γ e with
  | .ok ⟨T, _⟩ => some T
  | .no _ => none

def hasTy_of_inferCert_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} {B : Nat}
    (h : inferCertTy E n B Γ e = some T) : HasTy E n Γ e T := by
  unfold inferCertTy at h
  cases hs : inferCert E n B Γ e with
  | no r => rw [hs] at h; contradiction
  | ok s =>
      rw [hs] at h
      change some s.1 = some T at h
      rw [← Option.some.inj h]
      exact s.2

/-- `IotaEquationTyped` from computed `equationDoms`/`iotaSchemaAt`,
the literal profile at slots 1/2 of the extended env, and an
`inferSpine2` verdict matching `iotaLhsType` exactly. -/
def iotaEqTyped_of {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m}
    {i : Fin a.constructors.length} {fuel : Nat} {shapes : List FieldShape}
    {doms : List (Expr Nat)} {rhs : Expr Nat}
    (hd : equationDoms a i = some doms)
    (hs : iotaSchemaAt a i fuel shapes = some rhs)
    (h1 : (extendEnv E r m).members 1 = some mZero)
    (h2 : (extendEnv E r m).members 2 = some mSucc)
    (ht : (inferSpine2 (n := m.arity) (Γ := assumptionCtx doms) h1 h2 rhs).map
        (·.1) = some
          (iotaLhsType (a.family.ref + 1 + i.val) (policyFamilyLevels a.family)
            a.family.parameters.length a.constructors.length
            a.family.indices.length (a.constructorViews i).fields.length
            (a.constructorViews i).resultIndices)) :
    IotaEquationTyped a i fuel shapes := by
  unfold IotaEquationTyped
  rw [hd, hs]
  exact hasTy_of_inferSpine2_eq h1 h2 ht

/-! ## 05 §14 left-hand type (nparams = 0)

Before #6160 (b2221de20f), `iotaLhsType` (RcicIndGroupJudgment) puts the recursor's INDEX BINDERS in
the motive's index slot. 05 §14 types the right-hand side against
`rec params motive minors result_indices (ctor params fields)`, whose type
puts the constructor's RESULT INDICES there. For a family with indices the
two differ, and the judgment's obligation is then satisfiable only through
the collapsed untyped `Conv` (L-K1 fixture `devin/l-k1-idxfam-fixture`,
reported on #6084 / #6075). This section states and proves the 05 §14
obligation in the judgment's own context and with its own right-hand side;
only the motive's index arguments differ. With no parameters and no
indices the two types coincide (`iotaLhsType05_eq_of_noIdx`). Since #6160 the judgment states the motive at the result indices. With no parameters the two types coincide (`iotaLhsType_eq_05`, ScmSrcGroupsRecIdx), and the 19 indexed recursors are admitted in the judgment's own form there. -/

def iotaLhsType05 {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length) : Expr Nat :=
  let c := a.constructorViews i
  let nf := c.fields.length
  foldApps (.bvar (nf + a.family.indices.length + a.constructors.length))
    (c.resultIndices ++
      [foldApps (.const (a.family.ref + 1 + i.val) (policyFamilyLevels a.family)) (fieldBvars nf)])

def IotaEquationTyped05 {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    (fuel : Nat) (shapes : List FieldShape) : Type :=
  match equationDoms a i, iotaSchemaAt a i fuel shapes with
  | some doms, some rhs =>
      HasTy (extendEnv E r m) m.arity (assumptionCtx doms) rhs (iotaLhsType05 a i)
  | _, _ => Empty

/-- `IotaDescriptorClause` with the 05 §14 left-hand type. -/
structure IotaDescriptorClause05 (E : ResolvedEnv) {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : Type where
  signatureOnly : m.body = none
  shapesAt : Fin a.constructors.length → List FieldShape
  fuelAt : Fin a.constructors.length → Nat
  analyzed : ∀ i,
    fieldShapesFuel E (fuelAt i) a.family.ref a.family.member.arity
      a.family.parameters.length a.family.indices.length
      a.family.parameters.length (a.constructorViews i).fields = some (shapesAt i)
  typed : ∀ i, IotaEquationTyped05 a i (fuelAt i) (shapesAt i)

/-- The 05 §14 indexed-family evidence for one recursor: everything
`IndGroupAdmitted.recursor` asks for, with `IotaDescriptorClause05` in
place of `IotaDescriptorClause`. -/
structure RecursorAdmitted05 (E : ResolvedEnv) (r : Nat) (m : CheckedMember) : Type where
  a : RecursorEliminationAdmitted E r m
  hfresh : E.members r = none
  h04 : CtorCensus E a.family.ref r
  h07 : ∀ i, FieldUniverseAdmitted (a.constructorViews i)
  h08 : ∀ i, CtorFieldsPermitted (a.constructorViews i)
  h12 : MinorPremisesMatch a
  h14 : IotaDescriptorClause05 E a

/-- With no parameters and no indices the 05 §14 type coincides with
the judgment's `iotaLhsType`. Statement updated at the #6160 merge: `iotaLhsType` takes the result indices. -/
theorem iotaLhsType05_eq_of_noIdx {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} {a : RecursorEliminationAdmitted E r m}
    {i : Fin a.constructors.length}
    (hp : a.family.parameters = []) (hq : a.family.indices = []) :
    iotaLhsType05 a i =
      iotaLhsType (a.family.ref + 1 + i.val) (policyFamilyLevels a.family)
        a.family.parameters.length a.constructors.length
        a.family.indices.length (a.constructorViews i).fields.length
        (a.constructorViews i).resultIndices := by
  have hq' : (a.constructorViews i).resultIndices = [] := by
    have hlen := (a.constructorViews i).indexCount
    rw [hq] at hlen
    exact List.length_eq_zero.mp hlen
  have hql : a.family.indices.length = 0 := by rw [hq]; rfl
  have hpl : a.family.parameters.length = 0 := by rw [hp]; rfl
  unfold iotaLhsType05 iotaLhsType
  simp only [hql, hpl, hq', Nat.add_zero, List.range_zero, List.reverse_nil,
    List.map_nil, List.nil_append, policyParameterLocals]

/-- `IotaEquationTyped05` from computed `equationDoms`/`iotaSchemaAt`,
the literal profile at slots 1/2 of the extended env, and an
`inferSpine2` verdict matching `iotaLhsType05` exactly. -/
def iotaEqTyped05_of {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m}
    {i : Fin a.constructors.length} {fuel : Nat} {shapes : List FieldShape}
    {doms : List (Expr Nat)} {rhs : Expr Nat}
    (hd : equationDoms a i = some doms)
    (hs : iotaSchemaAt a i fuel shapes = some rhs)
    (h1 : (extendEnv E r m).members 1 = some mZero)
    (h2 : (extendEnv E r m).members 2 = some mSucc)
    (ht : (inferSpine2 (n := m.arity) (Γ := assumptionCtx doms) h1 h2 rhs).map
        (·.1) = some (iotaLhsType05 a i)) :
    IotaEquationTyped05 a i fuel shapes := by
  unfold IotaEquationTyped05
  rw [hd, hs]
  exact hasTy_of_inferSpine2_eq h1 h2 ht

/-- `IotaEquationTyped05` from computed `equationDoms`/`iotaSchemaAt`
and a `HasTy` derivation — the route for clauses whose right-hand
side is too large for `inferSpine2`'s `decide` (the typing then comes
from the machine's `infer` through `hasTyOfInfer`). -/
def iotaEqTyped05_of_hasTy {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m}
    {i : Fin a.constructors.length} {fuel : Nat} {shapes : List FieldShape}
    {doms : List (Expr Nat)} {rhs : Expr Nat}
    (hd : equationDoms a i = some doms)
    (hs : iotaSchemaAt a i fuel shapes = some rhs)
    (ht : HasTy (extendEnv E r m) m.arity (assumptionCtx doms) rhs
        (iotaLhsType05 a i)) :
    IotaEquationTyped05 a i fuel shapes := by
  unfold IotaEquationTyped05
  rw [hd, hs]
  exact ht

/-! ## §3 recursor pilot: `recN` at slot 3 -/

/-- `N`'s family view in `envPre 3`. -/
def famViewN3 : PolicyFamilyView (envPre 3) where
  ref := 0
  member := mN
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

/-- `zero`'s constructor view in `envPre 3`. -/
def ctorViewZero3 : PolicyConstructorView (envPre 3) famViewN3 mZero where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := []
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := by simp

/-- `succ`'s constructor view in `envPre 3`. -/
def ctorViewSucc3 : PolicyConstructorView (envPre 3) famViewN3 mSucc where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [.const 0 []]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 3) rfl rfl
    [.const 0 []]).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := by simp

/-- `N`'s recursor admission at slot 3. -/
def aRecN : RecursorEliminationAdmitted (envPre 3) 3 recN where
  family := famViewN3
  constructors := [mZero, mSucc]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewZero3
    | ⟨1, _⟩ => ctorViewSucc3
    | ⟨k+2, h⟩ => absurd h
        (by have : [mZero, mSucc].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mZero, mSucc].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorZero, minorSucc]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

/-- `recN` is admitted at slot 3. -/
def admRecN : IndGroupAdmitted (envPre 3) 3 recN :=
  .recursor aRecN rfl
    (ctorCensusB_sound (tbl := srcMembersG.take 3) (by decide) (by decide))
    (fun i => match i with
      | ⟨0, _⟩ => fun j => absurd j.isLt (Nat.not_lt_zero j.val)
      | ⟨1, _⟩ => fieldUniverseAdmitted_type_of_B ctorViewSucc3
          uniformType_succ_zero (by decide)
      | ⟨k+2, h⟩ => absurd h
          (by have : aRecN.constructors.length = 2 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => fun j => absurd j.isLt (Nat.not_lt_zero j.val)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewSucc3 96 (by decide)
      | ⟨k+2, h⟩ => absurd h
          (by have : aRecN.constructors.length = 2 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ⟨[], 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨[.recursive 0], 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h
          (by have : aRecN.constructors.length = 2 := rfl; omega))
    { signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => []
        | ⟨1, _⟩ => [.recursive 0]
        | ⟨k+2, h⟩ => absurd h
            (by have : aRecN.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h
            (by have : aRecN.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped_of (a := aRecN) (i := ⟨0, by decide⟩)
            (shapes := []) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped_of (a := aRecN) (i := ⟨1, by decide⟩)
            (shapes := [.recursive 0]) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h
            (by have : aRecN.constructors.length = 2 := rfl; omega) }

/-! ## §3 recursor admissions: non-indexed Type families -/

def famViewBytes7 : PolicyFamilyView (envPre 7) where
  ref := 4
  member := mBytes
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def ctorViewBnil7 : PolicyConstructorView (envPre 7)
    famViewBytes7 mBnil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBnil
  resultIndices := ctorIdx mBnil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 7) rfl rfl
    (ctorDom mBnil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewBcons7 : PolicyConstructorView (envPre 7)
    famViewBytes7 mBcons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBcons
  resultIndices := ctorIdx mBcons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 7) rfl rfl
    (ctorDom mBcons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecBytes : RecursorEliminationAdmitted (envPre 7) 7 recBytes where
  family := famViewBytes7
  constructors := [mBnil, mBcons]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewBnil7
    | ⟨1, _⟩ => ctorViewBcons7
    | ⟨k+2, h⟩ => absurd h
        (by have : [mBnil, mBcons].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mBnil, mBcons].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorBnil, minorBcons]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

def admRecBytes : IndGroupAdmitted (envPre 7) 7 recBytes :=
  .recursor aRecBytes rfl
    (ctorCensusB_sound (tbl := srcMembersG.take 7)
      (by decide) (by decide))
    (fun i => match i with
      | ⟨0, _⟩ => fieldUniverseAdmitted_type_of_B ctorViewBnil7
          uniformType_succ_zero (by decide)
      | ⟨1, _⟩ => fieldUniverseAdmitted_type_of_B ctorViewBcons7
          uniformType_succ_zero (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecBytes.constructors.length = 2 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewBnil7 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewBcons7 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecBytes.constructors.length = 2 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ⟨shapesBnil, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesBcons, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecBytes.constructors.length = 2 := rfl; omega))
    { signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesBnil
        | ⟨1, _⟩ => shapesBcons
        | ⟨k+2, h⟩ => absurd h (by have : aRecBytes.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecBytes.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped_of (a := aRecBytes) (i := ⟨0, by decide⟩)
            (shapes := shapesBnil) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped_of (a := aRecBytes) (i := ⟨1, by decide⟩)
            (shapes := shapesBcons) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecBytes.constructors.length = 2 := rfl; omega) }

def famViewRefT10 : PolicyFamilyView (envPre 10) where
  ref := 8
  member := mRefT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def ctorViewMkRef10 : PolicyConstructorView (envPre 10)
    famViewRefT10 mMkRef where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mMkRef
  resultIndices := ctorIdx mMkRef
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 10) rfl rfl
    (ctorDom mMkRef)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecRefT : RecursorEliminationAdmitted (envPre 10) 10 recRefT where
  family := famViewRefT10
  constructors := [mMkRef]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewMkRef10
    | ⟨k+1, h⟩ => absurd h
        (by have : [mMkRef].length = 1 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨k+1, h⟩ => absurd h
        (by have : [mMkRef].length = 1 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorMkRef]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

def admRecRefT : IndGroupAdmitted (envPre 10) 10 recRefT :=
  .recursor aRecRefT rfl
    (ctorCensusB_sound (tbl := srcMembersG.take 10)
      (by decide) (by decide))
    (fun i => match i with
      | ⟨0, _⟩ => fieldUniverseAdmitted_type_of_B ctorViewMkRef10
          uniformType_succ_zero (by decide)
      | ⟨k+1, h⟩ => absurd h (by have : aRecRefT.constructors.length = 1 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewMkRef10 96 (by decide)
      | ⟨k+1, h⟩ => absurd h (by have : aRecRefT.constructors.length = 1 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ⟨shapesMkRef, 96, rfl, rfl⟩
      | ⟨k+1, h⟩ => absurd h (by have : aRecRefT.constructors.length = 1 := rfl; omega))
    { signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesMkRef
        | ⟨k+1, h⟩ => absurd h (by have : aRecRefT.constructors.length = 1 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨k+1, h⟩ => absurd h (by have : aRecRefT.constructors.length = 1 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped_of (a := aRecRefT) (i := ⟨0, by decide⟩)
            (shapes := shapesMkRef) rfl rfl rfl rfl (by decide)
        | ⟨k+1, h⟩ => absurd h (by have : aRecRefT.constructors.length = 1 := rfl; omega) }

def famViewI33 : PolicyFamilyView (envPre 33) where
  ref := 30
  member := mI
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def ctorViewIPos33 : PolicyConstructorView (envPre 33)
    famViewI33 mIPos where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mIPos
  resultIndices := ctorIdx mIPos
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 33) rfl rfl
    (ctorDom mIPos)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewINegS33 : PolicyConstructorView (envPre 33)
    famViewI33 mINegS where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mINegS
  resultIndices := ctorIdx mINegS
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 33) rfl rfl
    (ctorDom mINegS)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecI : RecursorEliminationAdmitted (envPre 33) 33 recI where
  family := famViewI33
  constructors := [mIPos, mINegS]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewIPos33
    | ⟨1, _⟩ => ctorViewINegS33
    | ⟨k+2, h⟩ => absurd h
        (by have : [mIPos, mINegS].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mIPos, mINegS].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorIPos, minorINegS]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

def admRecI : IndGroupAdmitted (envPre 33) 33 recI :=
  .recursor aRecI rfl
    (ctorCensusB_sound (tbl := srcMembersG.take 33)
      (by decide) (by decide))
    (fun i => match i with
      | ⟨0, _⟩ => fieldUniverseAdmitted_type_of_B ctorViewIPos33
          uniformType_succ_zero (by decide)
      | ⟨1, _⟩ => fieldUniverseAdmitted_type_of_B ctorViewINegS33
          uniformType_succ_zero (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecI.constructors.length = 2 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewIPos33 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewINegS33 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecI.constructors.length = 2 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ⟨shapesIPos, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesINegS, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecI.constructors.length = 2 := rfl; omega))
    { signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesIPos
        | ⟨1, _⟩ => shapesINegS
        | ⟨k+2, h⟩ => absurd h (by have : aRecI.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecI.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped_of (a := aRecI) (i := ⟨0, by decide⟩)
            (shapes := shapesIPos) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped_of (a := aRecI) (i := ⟨1, by decide⟩)
            (shapes := shapesINegS) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecI.constructors.length = 2 := rfl; omega) }

def famViewBL37 : PolicyFamilyView (envPre 37) where
  ref := 34
  member := mBL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def ctorViewBlNil37 : PolicyConstructorView (envPre 37)
    famViewBL37 mBlNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBlNil
  resultIndices := ctorIdx mBlNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 37) rfl rfl
    (ctorDom mBlNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewBlCons37 : PolicyConstructorView (envPre 37)
    famViewBL37 mBlCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBlCons
  resultIndices := ctorIdx mBlCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 37) rfl rfl
    (ctorDom mBlCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecBL : RecursorEliminationAdmitted (envPre 37) 37 recBL where
  family := famViewBL37
  constructors := [mBlNil, mBlCons]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewBlNil37
    | ⟨1, _⟩ => ctorViewBlCons37
    | ⟨k+2, h⟩ => absurd h
        (by have : [mBlNil, mBlCons].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mBlNil, mBlCons].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorBlNil, minorBlCons]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

def admRecBL : IndGroupAdmitted (envPre 37) 37 recBL :=
  .recursor aRecBL rfl
    (ctorCensusB_sound (tbl := srcMembersG.take 37)
      (by decide) (by decide))
    (fun i => match i with
      | ⟨0, _⟩ => fieldUniverseAdmitted_type_of_B ctorViewBlNil37
          uniformType_succ_zero (by decide)
      | ⟨1, _⟩ => fieldUniverseAdmitted_type_of_B ctorViewBlCons37
          uniformType_succ_zero (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecBL.constructors.length = 2 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewBlNil37 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewBlCons37 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecBL.constructors.length = 2 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ⟨shapesBlNil, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesBlCons, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecBL.constructors.length = 2 := rfl; omega))
    { signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesBlNil
        | ⟨1, _⟩ => shapesBlCons
        | ⟨k+2, h⟩ => absurd h (by have : aRecBL.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecBL.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped_of (a := aRecBL) (i := ⟨0, by decide⟩)
            (shapes := shapesBlNil) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped_of (a := aRecBL) (i := ⟨1, by decide⟩)
            (shapes := shapesBlCons) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecBL.constructors.length = 2 := rfl; omega) }

def famViewFT41 : PolicyFamilyView (envPre 41) where
  ref := 38
  member := mFT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def ctorViewFtNil41 : PolicyConstructorView (envPre 41)
    famViewFT41 mFtNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mFtNil
  resultIndices := ctorIdx mFtNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 41) rfl rfl
    (ctorDom mFtNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewFtCons41 : PolicyConstructorView (envPre 41)
    famViewFT41 mFtCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mFtCons
  resultIndices := ctorIdx mFtCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 41) rfl rfl
    (ctorDom mFtCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecFT : RecursorEliminationAdmitted (envPre 41) 41 recFT where
  family := famViewFT41
  constructors := [mFtNil, mFtCons]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewFtNil41
    | ⟨1, _⟩ => ctorViewFtCons41
    | ⟨k+2, h⟩ => absurd h
        (by have : [mFtNil, mFtCons].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mFtNil, mFtCons].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorFtNil, minorFtCons]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

def admRecFT : IndGroupAdmitted (envPre 41) 41 recFT :=
  .recursor aRecFT rfl
    (ctorCensusB_sound (tbl := srcMembersG.take 41)
      (by decide) (by decide))
    (fun i => match i with
      | ⟨0, _⟩ => fieldUniverseAdmitted_type_of_B ctorViewFtNil41
          uniformType_succ_zero (by decide)
      | ⟨1, _⟩ => fieldUniverseAdmitted_type_of_B ctorViewFtCons41
          uniformType_succ_zero (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecFT.constructors.length = 2 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewFtNil41 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewFtCons41 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecFT.constructors.length = 2 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ⟨shapesFtNil, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesFtCons, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecFT.constructors.length = 2 := rfl; omega))
    { signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesFtNil
        | ⟨1, _⟩ => shapesFtCons
        | ⟨k+2, h⟩ => absurd h (by have : aRecFT.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecFT.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped_of (a := aRecFT) (i := ⟨0, by decide⟩)
            (shapes := shapesFtNil) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped_of (a := aRecFT) (i := ⟨1, by decide⟩)
            (shapes := shapesFtCons) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecFT.constructors.length = 2 := rfl; omega) }

def famViewBCT108 : PolicyFamilyView (envPre 108) where
  ref := 106
  member := mBCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def ctorViewMkBound108 : PolicyConstructorView (envPre 108)
    famViewBCT108 mMkBound where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mMkBound
  resultIndices := ctorIdx mMkBound
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 108) rfl rfl
    (ctorDom mMkBound)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecBCT : RecursorEliminationAdmitted (envPre 108) 108 recBCT where
  family := famViewBCT108
  constructors := [mMkBound]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewMkBound108
    | ⟨k+1, h⟩ => absurd h
        (by have : [mMkBound].length = 1 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨k+1, h⟩ => absurd h
        (by have : [mMkBound].length = 1 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorMkBound]
  minorCount := rfl
  policy := .anySort
  selected := .uniformType uniformType_succ_zero
  recursorArity := rfl
  recursorType := rfl

def admRecBCT : IndGroupAdmitted (envPre 108) 108 recBCT :=
  .recursor aRecBCT rfl
    (ctorCensusB_sound (tbl := srcMembersG.take 108)
      (by decide) (by decide))
    (fun i => match i with
      | ⟨0, _⟩ => fieldUniverseAdmitted_type_of_B ctorViewMkBound108
          uniformType_succ_zero (by decide)
      | ⟨k+1, h⟩ => absurd h (by have : aRecBCT.constructors.length = 1 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewMkBound108 96 (by decide)
      | ⟨k+1, h⟩ => absurd h (by have : aRecBCT.constructors.length = 1 := rfl; omega))
    (fun i => match i with
      | ⟨0, _⟩ => ⟨shapesMkBound, 96, rfl, rfl⟩
      | ⟨k+1, h⟩ => absurd h (by have : aRecBCT.constructors.length = 1 := rfl; omega))
    { signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesMkBound
        | ⟨k+1, h⟩ => absurd h (by have : aRecBCT.constructors.length = 1 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨k+1, h⟩ => absurd h (by have : aRecBCT.constructors.length = 1 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped_of (a := aRecBCT) (i := ⟨0, by decide⟩)
            (shapes := shapesMkBound) rfl rfl rfl rfl (by decide)
        | ⟨k+1, h⟩ => absurd h (by have : aRecBCT.constructors.length = 1 := rfl; omega) }

/-! ## §3 recursor admissions: indexed Prop families (05 §14 form) -/

def famViewDA29 : PolicyFamilyView (envPre 29) where
  ref := 23
  member := mDA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 29) rfl rfl
    [.const 0 [], .const 0 [], .const 4 [], .const 4 []]).get (by decide)

def ctorViewDaI29 : PolicyConstructorView (envPre 29)
    famViewDA29 mDaI where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDaI
  resultIndices := ctorIdx mDaI
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 29) rfl rfl
    (ctorDom mDaI)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewDaB29 : PolicyConstructorView (envPre 29)
    famViewDA29 mDaB where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDaB
  resultIndices := ctorIdx mDaB
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 29) rfl rfl
    (ctorDom mDaB)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewDaS29 : PolicyConstructorView (envPre 29)
    famViewDA29 mDaS where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDaS
  resultIndices := ctorIdx mDaS
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 29) rfl rfl
    (ctorDom mDaS)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewDaY29 : PolicyConstructorView (envPre 29)
    famViewDA29 mDaY where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDaY
  resultIndices := ctorIdx mDaY
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 29) rfl rfl
    (ctorDom mDaY)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewDaLB29 : PolicyConstructorView (envPre 29)
    famViewDA29 mDaLB where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDaLB
  resultIndices := ctorIdx mDaLB
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 29) rfl rfl
    (ctorDom mDaLB)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecDA : RecursorEliminationAdmitted (envPre 29) 29 recDA where
  family := famViewDA29
  constructors := [mDaI, mDaB, mDaS, mDaY, mDaLB]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewDaI29
    | ⟨1, _⟩ => ctorViewDaB29
    | ⟨2, _⟩ => ctorViewDaS29
    | ⟨3, _⟩ => ctorViewDaY29
    | ⟨4, _⟩ => ctorViewDaLB29
    | ⟨k+5, h⟩ => absurd h
        (by have : [mDaI, mDaB, mDaS, mDaY, mDaLB].length = 5 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨k+5, h⟩ => absurd h
        (by have : [mDaI, mDaB, mDaS, mDaY, mDaLB].length = 5 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorDaI, minorDaB, minorDaS, minorDaY, minorDaLB]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecDA05 : RecursorAdmitted05 (envPre 29) 29 recDA where
  a := aRecDA
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 29)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewDaI29 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewDaB29 96 (by decide)
      | ⟨2, _⟩ => ctorFieldsPermitted_of_B ctorViewDaS29 96 (by decide)
      | ⟨3, _⟩ => ctorFieldsPermitted_of_B ctorViewDaY29 96 (by decide)
      | ⟨4, _⟩ => ctorFieldsPermitted_of_B ctorViewDaLB29 96 (by decide)
      | ⟨k+5, h⟩ => absurd h (by have : aRecDA.constructors.length = 5 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesDaI, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesDaB, 96, rfl, rfl⟩
      | ⟨2, _⟩ => ⟨shapesDaS, 96, rfl, rfl⟩
      | ⟨3, _⟩ => ⟨shapesDaY, 96, rfl, rfl⟩
      | ⟨4, _⟩ => ⟨shapesDaLB, 96, rfl, rfl⟩
      | ⟨k+5, h⟩ => absurd h (by have : aRecDA.constructors.length = 5 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesDaI
        | ⟨1, _⟩ => shapesDaB
        | ⟨2, _⟩ => shapesDaS
        | ⟨3, _⟩ => shapesDaY
        | ⟨4, _⟩ => shapesDaLB
        | ⟨k+5, h⟩ => absurd h (by have : aRecDA.constructors.length = 5 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨2, _⟩ => rfl
        | ⟨3, _⟩ => rfl
        | ⟨4, _⟩ => rfl
        | ⟨k+5, h⟩ => absurd h (by have : aRecDA.constructors.length = 5 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecDA) (i := ⟨0, by decide⟩)
            (shapes := shapesDaI) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecDA) (i := ⟨1, by decide⟩)
            (shapes := shapesDaB) rfl rfl rfl rfl (by decide)
        | ⟨2, _⟩ => iotaEqTyped05_of (a := aRecDA) (i := ⟨2, by decide⟩)
            (shapes := shapesDaS) rfl rfl rfl rfl (by decide)
        | ⟨3, _⟩ => iotaEqTyped05_of (a := aRecDA) (i := ⟨3, by decide⟩)
            (shapes := shapesDaY) rfl rfl rfl rfl (by decide)
        | ⟨4, _⟩ => iotaEqTyped05_of (a := aRecDA) (i := ⟨4, by decide⟩)
            (shapes := shapesDaLB) rfl rfl rfl rfl (by decide)
        | ⟨k+5, h⟩ => absurd h (by have : aRecDA.constructors.length = 5 := rfl; omega) }

def famViewLt45 : PolicyFamilyView (envPre 45) where
  ref := 42
  member := mLt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 45) rfl rfl
    [.const 0 [], .const 0 []]).get (by decide)

def ctorViewLtBase45 : PolicyConstructorView (envPre 45)
    famViewLt45 mLtBase where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mLtBase
  resultIndices := ctorIdx mLtBase
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 45) rfl rfl
    (ctorDom mLtBase)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewLtStep45 : PolicyConstructorView (envPre 45)
    famViewLt45 mLtStep where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mLtStep
  resultIndices := ctorIdx mLtStep
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 45) rfl rfl
    (ctorDom mLtStep)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecLt : RecursorEliminationAdmitted (envPre 45) 45 recLt where
  family := famViewLt45
  constructors := [mLtBase, mLtStep]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewLtBase45
    | ⟨1, _⟩ => ctorViewLtStep45
    | ⟨k+2, h⟩ => absurd h
        (by have : [mLtBase, mLtStep].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mLtBase, mLtStep].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorLtBase, minorLtStep]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecLt05 : RecursorAdmitted05 (envPre 45) 45 recLt where
  a := aRecLt
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 45)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewLtBase45 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewLtStep45 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecLt.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesLtBase, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesLtStep, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecLt.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesLtBase
        | ⟨1, _⟩ => shapesLtStep
        | ⟨k+2, h⟩ => absurd h (by have : aRecLt.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecLt.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecLt) (i := ⟨0, by decide⟩)
            (shapes := shapesLtBase) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecLt) (i := ⟨1, by decide⟩)
            (shapes := shapesLtStep) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecLt.constructors.length = 2 := rfl; omega) }

/-- Judgment-form vs 05-form pin for `daI` (slot 24). Before #6160 the judgment's `iotaLhsType` put the index binders in the motive slot and the inferred type matched only the 05 form (`daI_judgmentForm_mismatch`, retired). Since #6160 both pins hold: the honest inferred type is the judgment's own type. -/
private def daI_i0 : Fin aRecDA.constructors.length := ⟨0, by decide⟩
private def judDA0 : Expr Nat :=
  iotaLhsType (aRecDA.family.ref + 1 + 0) (policyFamilyLevels aRecDA.family)
    aRecDA.family.parameters.length aRecDA.constructors.length
    aRecDA.family.indices.length (aRecDA.constructorViews daI_i0).fields.length
    (aRecDA.constructorViews daI_i0).resultIndices
private def inferredDA0 : Option (Expr Nat) :=
  match equationDoms aRecDA daI_i0, iotaSchemaAt aRecDA daI_i0 96 shapesDaI with
  | some doms, some rhs =>
      (inferSpine2 (E := extendEnv (envPre 29) 29 recDA) (n := recDA.arity)
        (Γ := assumptionCtx doms) rfl rfl rhs).map (·.1)
  | _, _ => none
/- RETIRED (#6160, R-Retire): iotaLhsType replaced by #6160 (b2221de20f): the judgment's ι type now puts the result indices in the motive's index slot, so the mismatch this pinned no longer exists; superseded by `daI_judgmentForm_match`. Not weakened.
theorem daI_judgmentForm_mismatch : inferredDA0 ≠ some judDA0 := by decide
-/
theorem daI_judgmentForm_match : inferredDA0 = some judDA0 := by decide
theorem daI_05Form_match : inferredDA0 = some (iotaLhsType05 aRecDA daI_i0) :=
  by decide

/-! ## §3 recursor admissions: indexed Prop families (cont.) -/


def famViewBC49 : PolicyFamilyView (envPre 49) where
  ref := 46
  member := mBC
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 49) rfl rfl
    [.const 4 [], .const 4 [], .const 4 []]).get (by decide)

def ctorViewCatNil49 : PolicyConstructorView (envPre 49)
    famViewBC49 mCatNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCatNil
  resultIndices := ctorIdx mCatNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 49) rfl rfl
    (ctorDom mCatNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewCatCons49 : PolicyConstructorView (envPre 49)
    famViewBC49 mCatCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCatCons
  resultIndices := ctorIdx mCatCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 49) rfl rfl
    (ctorDom mCatCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecBC : RecursorEliminationAdmitted (envPre 49) 49 recBC where
  family := famViewBC49
  constructors := [mCatNil, mCatCons]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewCatNil49
    | ⟨1, _⟩ => ctorViewCatCons49
    | ⟨k+2, h⟩ => absurd h
        (by have : [mCatNil, mCatCons].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mCatNil, mCatCons].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorCatNil, minorCatCons]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecBC05 : RecursorAdmitted05 (envPre 49) 49 recBC where
  a := aRecBC
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 49)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewCatNil49 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewCatCons49 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecBC.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesCatNil, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesCatCons, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecBC.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesCatNil
        | ⟨1, _⟩ => shapesCatCons
        | ⟨k+2, h⟩ => absurd h (by have : aRecBC.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecBC.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecBC) (i := ⟨0, by decide⟩)
            (shapes := shapesCatNil) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecBC) (i := ⟨1, by decide⟩)
            (shapes := shapesCatCons) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecBC.constructors.length = 2 := rfl; omega) }

def famViewDM1053 : PolicyFamilyView (envPre 53) where
  ref := 50
  member := mDM10
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 53) rfl rfl
    [.const 0 [], .const 0 [], .const 0 []]).get (by decide)

def ctorViewDmBase53 : PolicyConstructorView (envPre 53)
    famViewDM1053 mDmBase where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDmBase
  resultIndices := ctorIdx mDmBase
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 53) rfl rfl
    (ctorDom mDmBase)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewDmStep53 : PolicyConstructorView (envPre 53)
    famViewDM1053 mDmStep where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mDmStep
  resultIndices := ctorIdx mDmStep
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 53) rfl rfl
    (ctorDom mDmStep)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecDM10 : RecursorEliminationAdmitted (envPre 53) 53 recDM10 where
  family := famViewDM1053
  constructors := [mDmBase, mDmStep]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewDmBase53
    | ⟨1, _⟩ => ctorViewDmStep53
    | ⟨k+2, h⟩ => absurd h
        (by have : [mDmBase, mDmStep].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mDmBase, mDmStep].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorDmBase, minorDmStep]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecDM1005 : RecursorAdmitted05 (envPre 53) 53 recDM10 where
  a := aRecDM10
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 53)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewDmBase53 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewDmStep53 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecDM10.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesDmBase, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesDmStep, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecDM10.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesDmBase
        | ⟨1, _⟩ => shapesDmStep
        | ⟨k+2, h⟩ => absurd h (by have : aRecDM10.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecDM10.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecDM10) (i := ⟨0, by decide⟩)
            (shapes := shapesDmBase) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecDM10) (i := ⟨1, by decide⟩)
            (shapes := shapesDmStep) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecDM10.constructors.length = 2 := rfl; omega) }

def famViewND57 : PolicyFamilyView (envPre 57) where
  ref := 54
  member := mND
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 57) rfl rfl
    [.const 0 [], .const 4 []]).get (by decide)

def ctorViewNdBase57 : PolicyConstructorView (envPre 57)
    famViewND57 mNdBase where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNdBase
  resultIndices := ctorIdx mNdBase
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 57) rfl rfl
    (ctorDom mNdBase)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewNdStep57 : PolicyConstructorView (envPre 57)
    famViewND57 mNdStep where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNdStep
  resultIndices := ctorIdx mNdStep
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 57) rfl rfl
    (ctorDom mNdStep)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecND : RecursorEliminationAdmitted (envPre 57) 57 recND where
  family := famViewND57
  constructors := [mNdBase, mNdStep]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewNdBase57
    | ⟨1, _⟩ => ctorViewNdStep57
    | ⟨k+2, h⟩ => absurd h
        (by have : [mNdBase, mNdStep].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mNdBase, mNdStep].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorNdBase, minorNdStep]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecND05 : RecursorAdmitted05 (envPre 57) 57 recND where
  a := aRecND
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 57)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewNdBase57 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewNdStep57 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecND.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesNdBase, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesNdStep, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecND.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesNdBase
        | ⟨1, _⟩ => shapesNdStep
        | ⟨k+2, h⟩ => absurd h (by have : aRecND.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecND.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecND) (i := ⟨0, by decide⟩)
            (shapes := shapesNdBase) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecND) (i := ⟨1, by decide⟩)
            (shapes := shapesNdStep) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecND.constructors.length = 2 := rfl; omega) }

def famViewNEA60 : PolicyFamilyView (envPre 60) where
  ref := 58
  member := mNEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 60) rfl rfl
    [.const 0 [], .const 4 []]).get (by decide)

def ctorViewNeIntro60 : PolicyConstructorView (envPre 60)
    famViewNEA60 mNeIntro where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNeIntro
  resultIndices := ctorIdx mNeIntro
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 60) rfl rfl
    (ctorDom mNeIntro)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecNEA : RecursorEliminationAdmitted (envPre 60) 60 recNEA where
  family := famViewNEA60
  constructors := [mNeIntro]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewNeIntro60
    | ⟨k+1, h⟩ => absurd h
        (by have : [mNeIntro].length = 1 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨k+1, h⟩ => absurd h
        (by have : [mNeIntro].length = 1 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorNeIntro]
  minorCount := rfl
  policy := .propOnly
  selected := .hiddenDataProp (fun _ => rfl) rfl
      (fun hsafe => absurd (hsafe ⟨0, by decide⟩ ⟨1, by decide⟩)
        (fun hF => hF.elim
          (fun hP => absurd (hP (fun _ => 0)) (by decide))
          (fun hM => absurd hM (by decide))))
  recursorArity := rfl
  recursorType := rfl

def admRecNEA05 : RecursorAdmitted05 (envPre 60) 60 recNEA where
  a := aRecNEA
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 60)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewNeIntro60 96 (by decide)
      | ⟨k+1, h⟩ => absurd h (by have : aRecNEA.constructors.length = 1 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesNeIntro, 96, rfl, rfl⟩
      | ⟨k+1, h⟩ => absurd h (by have : aRecNEA.constructors.length = 1 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesNeIntro
        | ⟨k+1, h⟩ => absurd h (by have : aRecNEA.constructors.length = 1 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨k+1, h⟩ => absurd h (by have : aRecNEA.constructors.length = 1 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecNEA) (i := ⟨0, by decide⟩)
            (shapes := shapesNeIntro) rfl rfl rfl rfl (by decide)
        | ⟨k+1, h⟩ => absurd h (by have : aRecNEA.constructors.length = 1 := rfl; omega) }

def famViewIEA64 : PolicyFamilyView (envPre 64) where
  ref := 61
  member := mIEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 30 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 64) rfl rfl
    [.const 30 [], .const 4 []]).get (by decide)

def ctorViewIePos64 : PolicyConstructorView (envPre 64)
    famViewIEA64 mIePos where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mIePos
  resultIndices := ctorIdx mIePos
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 64) rfl rfl
    (ctorDom mIePos)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewIeNeg64 : PolicyConstructorView (envPre 64)
    famViewIEA64 mIeNeg where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mIeNeg
  resultIndices := ctorIdx mIeNeg
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 64) rfl rfl
    (ctorDom mIeNeg)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecIEA : RecursorEliminationAdmitted (envPre 64) 64 recIEA where
  family := famViewIEA64
  constructors := [mIePos, mIeNeg]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewIePos64
    | ⟨1, _⟩ => ctorViewIeNeg64
    | ⟨k+2, h⟩ => absurd h
        (by have : [mIePos, mIeNeg].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mIePos, mIeNeg].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorIePos, minorIeNeg]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecIEA05 : RecursorAdmitted05 (envPre 64) 64 recIEA where
  a := aRecIEA
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 64)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewIePos64 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewIeNeg64 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecIEA.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesIePos, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesIeNeg, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecIEA.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesIePos
        | ⟨1, _⟩ => shapesIeNeg
        | ⟨k+2, h⟩ => absurd h (by have : aRecIEA.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecIEA.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecIEA) (i := ⟨0, by decide⟩)
            (shapes := shapesIePos) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecIEA) (i := ⟨1, by decide⟩)
            (shapes := shapesIeNeg) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecIEA.constructors.length = 2 := rfl; omega) }

def famViewSL68 : PolicyFamilyView (envPre 68) where
  ref := 65
  member := mSL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 68) rfl rfl
    [.const 4 [], .const 0 []]).get (by decide)

def ctorViewSlNil68 : PolicyConstructorView (envPre 68)
    famViewSL68 mSlNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mSlNil
  resultIndices := ctorIdx mSlNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 68) rfl rfl
    (ctorDom mSlNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewSlCons68 : PolicyConstructorView (envPre 68)
    famViewSL68 mSlCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mSlCons
  resultIndices := ctorIdx mSlCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 68) rfl rfl
    (ctorDom mSlCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecSL : RecursorEliminationAdmitted (envPre 68) 68 recSL where
  family := famViewSL68
  constructors := [mSlNil, mSlCons]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewSlNil68
    | ⟨1, _⟩ => ctorViewSlCons68
    | ⟨k+2, h⟩ => absurd h
        (by have : [mSlNil, mSlCons].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mSlNil, mSlCons].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorSlNil, minorSlCons]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecSL05 : RecursorAdmitted05 (envPre 68) 68 recSL where
  a := aRecSL
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 68)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewSlNil68 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewSlCons68 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecSL.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesSlNil, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesSlCons, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecSL.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesSlNil
        | ⟨1, _⟩ => shapesSlCons
        | ⟨k+2, h⟩ => absurd h (by have : aRecSL.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecSL.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecSL) (i := ⟨0, by decide⟩)
            (shapes := shapesSlNil) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecSL) (i := ⟨1, by decide⟩)
            (shapes := shapesSlCons) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecSL.constructors.length = 2 := rfl; omega) }

def famViewBLL72 : PolicyFamilyView (envPre 72) where
  ref := 69
  member := mBLL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 72) rfl rfl
    [.const 34 [], .const 0 []]).get (by decide)

def ctorViewBllNil72 : PolicyConstructorView (envPre 72)
    famViewBLL72 mBllNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBllNil
  resultIndices := ctorIdx mBllNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 72) rfl rfl
    (ctorDom mBllNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewBllCons72 : PolicyConstructorView (envPre 72)
    famViewBLL72 mBllCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBllCons
  resultIndices := ctorIdx mBllCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 72) rfl rfl
    (ctorDom mBllCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecBLL : RecursorEliminationAdmitted (envPre 72) 72 recBLL where
  family := famViewBLL72
  constructors := [mBllNil, mBllCons]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewBllNil72
    | ⟨1, _⟩ => ctorViewBllCons72
    | ⟨k+2, h⟩ => absurd h
        (by have : [mBllNil, mBllCons].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mBllNil, mBllCons].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorBllNil, minorBllCons]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecBLL05 : RecursorAdmitted05 (envPre 72) 72 recBLL where
  a := aRecBLL
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 72)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewBllNil72 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewBllCons72 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecBLL.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesBllNil, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesBllCons, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecBLL.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesBllNil
        | ⟨1, _⟩ => shapesBllCons
        | ⟨k+2, h⟩ => absurd h (by have : aRecBLL.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecBLL.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecBLL) (i := ⟨0, by decide⟩)
            (shapes := shapesBllNil) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecBLL) (i := ⟨1, by decide⟩)
            (shapes := shapesBllCons) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecBLL.constructors.length = 2 := rfl; omega) }

def famViewFTL76 : PolicyFamilyView (envPre 76) where
  ref := 73
  member := mFTL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 76) rfl rfl
    [.const 38 [], .const 0 []]).get (by decide)

def ctorViewFtlNil76 : PolicyConstructorView (envPre 76)
    famViewFTL76 mFtlNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mFtlNil
  resultIndices := ctorIdx mFtlNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 76) rfl rfl
    (ctorDom mFtlNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewFtlCons76 : PolicyConstructorView (envPre 76)
    famViewFTL76 mFtlCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mFtlCons
  resultIndices := ctorIdx mFtlCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 76) rfl rfl
    (ctorDom mFtlCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecFTL : RecursorEliminationAdmitted (envPre 76) 76 recFTL where
  family := famViewFTL76
  constructors := [mFtlNil, mFtlCons]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewFtlNil76
    | ⟨1, _⟩ => ctorViewFtlCons76
    | ⟨k+2, h⟩ => absurd h
        (by have : [mFtlNil, mFtlCons].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mFtlNil, mFtlCons].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorFtlNil, minorFtlCons]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecFTL05 : RecursorAdmitted05 (envPre 76) 76 recFTL where
  a := aRecFTL
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 76)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewFtlNil76 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewFtlCons76 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecFTL.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesFtlNil, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesFtlCons, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecFTL.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesFtlNil
        | ⟨1, _⟩ => shapesFtlCons
        | ⟨k+2, h⟩ => absurd h (by have : aRecFTL.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecFTL.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecFTL) (i := ⟨0, by decide⟩)
            (shapes := shapesFtlNil) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecFTL) (i := ⟨1, by decide⟩)
            (shapes := shapesFtlCons) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecFTL.constructors.length = 2 := rfl; omega) }

def famViewBLC80 : PolicyFamilyView (envPre 80) where
  ref := 77
  member := mBLC
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 80) rfl rfl
    [.const 34 [], .const 4 []]).get (by decide)

def ctorViewBlcNil80 : PolicyConstructorView (envPre 80)
    famViewBLC80 mBlcNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBlcNil
  resultIndices := ctorIdx mBlcNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 80) rfl rfl
    (ctorDom mBlcNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewBlcCons80 : PolicyConstructorView (envPre 80)
    famViewBLC80 mBlcCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mBlcCons
  resultIndices := ctorIdx mBlcCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 80) rfl rfl
    (ctorDom mBlcCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecBLC : RecursorEliminationAdmitted (envPre 80) 80 recBLC where
  family := famViewBLC80
  constructors := [mBlcNil, mBlcCons]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewBlcNil80
    | ⟨1, _⟩ => ctorViewBlcCons80
    | ⟨k+2, h⟩ => absurd h
        (by have : [mBlcNil, mBlcCons].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mBlcNil, mBlcCons].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorBlcNil, minorBlcCons]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecBLC05 : RecursorAdmitted05 (envPre 80) 80 recBLC where
  a := aRecBLC
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 80)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewBlcNil80 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewBlcCons80 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecBLC.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesBlcNil, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesBlcCons, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecBLC.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesBlcNil
        | ⟨1, _⟩ => shapesBlcCons
        | ⟨k+2, h⟩ => absurd h (by have : aRecBLC.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecBLC.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecBLC) (i := ⟨0, by decide⟩)
            (shapes := shapesBlcNil) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecBLC) (i := ⟨1, by decide⟩)
            (shapes := shapesBlcCons) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecBLC.constructors.length = 2 := rfl; omega) }

/-! ## §3 recursor admissions: indexed Prop families (cont. 2) -/

def famViewSEA83 : PolicyFamilyView (envPre 83) where
  ref := 81
  member := mSEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 83) rfl rfl
    [.const 4 [], .const 4 []]).get (by decide)

def ctorViewSeIntro83 : PolicyConstructorView (envPre 83)
    famViewSEA83 mSeIntro where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mSeIntro
  resultIndices := ctorIdx mSeIntro
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 83) rfl rfl
    (ctorDom mSeIntro)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecSEA : RecursorEliminationAdmitted (envPre 83) 83 recSEA where
  family := famViewSEA83
  constructors := [mSeIntro]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewSeIntro83
    | ⟨k+1, h⟩ => absurd h
        (by have : [mSeIntro].length = 1 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨k+1, h⟩ => absurd h
        (by have : [mSeIntro].length = 1 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorSeIntro]
  minorCount := rfl
  policy := .propOnly
  selected := .hiddenDataProp (fun _ => rfl) rfl
      (fun hsafe => absurd (hsafe ⟨0, by decide⟩ ⟨1, by decide⟩)
        (fun hF => hF.elim
          (fun hP => absurd (hP (fun _ => 0)) (by decide))
          (fun hM => absurd hM (by decide))))
  recursorArity := rfl
  recursorType := rfl

def admRecSEA05 : RecursorAdmitted05 (envPre 83) 83 recSEA where
  a := aRecSEA
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 83)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewSeIntro83 96 (by decide)
      | ⟨k+1, h⟩ => absurd h (by have : aRecSEA.constructors.length = 1 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesSeIntro, 96, rfl, rfl⟩
      | ⟨k+1, h⟩ => absurd h (by have : aRecSEA.constructors.length = 1 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesSeIntro
        | ⟨k+1, h⟩ => absurd h (by have : aRecSEA.constructors.length = 1 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨k+1, h⟩ => absurd h (by have : aRecSEA.constructors.length = 1 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecSEA) (i := ⟨0, by decide⟩)
            (shapes := shapesSeIntro) rfl rfl rfl rfl (by decide)
        | ⟨k+1, h⟩ => absurd h (by have : aRecSEA.constructors.length = 1 := rfl; omega) }

def famViewFTE87 : PolicyFamilyView (envPre 87) where
  ref := 84
  member := mFTE
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 87) rfl rfl
    [.const 38 [], .const 4 []]).get (by decide)

def ctorViewFteNil87 : PolicyConstructorView (envPre 87)
    famViewFTE87 mFteNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mFteNil
  resultIndices := ctorIdx mFteNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 87) rfl rfl
    (ctorDom mFteNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewFteCons87 : PolicyConstructorView (envPre 87)
    famViewFTE87 mFteCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mFteCons
  resultIndices := ctorIdx mFteCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 87) rfl rfl
    (ctorDom mFteCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecFTE : RecursorEliminationAdmitted (envPre 87) 87 recFTE where
  family := famViewFTE87
  constructors := [mFteNil, mFteCons]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewFteNil87
    | ⟨1, _⟩ => ctorViewFteCons87
    | ⟨k+2, h⟩ => absurd h
        (by have : [mFteNil, mFteCons].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mFteNil, mFteCons].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorFteNil, minorFteCons]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecFTE05 : RecursorAdmitted05 (envPre 87) 87 recFTE where
  a := aRecFTE
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 87)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewFteNil87 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewFteCons87 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecFTE.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesFteNil, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesFteCons, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecFTE.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesFteNil
        | ⟨1, _⟩ => shapesFteCons
        | ⟨k+2, h⟩ => absurd h (by have : aRecFTE.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecFTE.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecFTE) (i := ⟨0, by decide⟩)
            (shapes := shapesFteNil) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecFTE) (i := ⟨1, by decide⟩)
            (shapes := shapesFteCons) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecFTE.constructors.length = 2 := rfl; omega) }

def famViewNthB91 : PolicyFamilyView (envPre 91) where
  ref := 88
  member := mNthB
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 91) rfl rfl
    [.const 34 [], .const 0 [], .const 4 []]).get (by decide)

def ctorViewNthBHere91 : PolicyConstructorView (envPre 91)
    famViewNthB91 mNthBHere where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNthBHere
  resultIndices := ctorIdx mNthBHere
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 91) rfl rfl
    (ctorDom mNthBHere)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewNthBNext91 : PolicyConstructorView (envPre 91)
    famViewNthB91 mNthBNext where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNthBNext
  resultIndices := ctorIdx mNthBNext
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 91) rfl rfl
    (ctorDom mNthBNext)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecNthB : RecursorEliminationAdmitted (envPre 91) 91 recNthB where
  family := famViewNthB91
  constructors := [mNthBHere, mNthBNext]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewNthBHere91
    | ⟨1, _⟩ => ctorViewNthBNext91
    | ⟨k+2, h⟩ => absurd h
        (by have : [mNthBHere, mNthBNext].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mNthBHere, mNthBNext].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorNthBHere, minorNthBNext]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecNthB05 : RecursorAdmitted05 (envPre 91) 91 recNthB where
  a := aRecNthB
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 91)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewNthBHere91 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewNthBNext91 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecNthB.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesNthBHere, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesNthBNext, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecNthB.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesNthBHere
        | ⟨1, _⟩ => shapesNthBNext
        | ⟨k+2, h⟩ => absurd h (by have : aRecNthB.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecNthB.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecNthB) (i := ⟨0, by decide⟩)
            (shapes := shapesNthBHere) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecNthB) (i := ⟨1, by decide⟩)
            (shapes := shapesNthBNext) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecNthB.constructors.length = 2 := rfl; omega) }

def famViewNthF95 : PolicyFamilyView (envPre 95) where
  ref := 92
  member := mNthF
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 95) rfl rfl
    [.const 38 [], .const 0 [], .const 4 [], .const 4 []]).get (by decide)

def ctorViewNthFHere95 : PolicyConstructorView (envPre 95)
    famViewNthF95 mNthFHere where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNthFHere
  resultIndices := ctorIdx mNthFHere
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 95) rfl rfl
    (ctorDom mNthFHere)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewNthFNext95 : PolicyConstructorView (envPre 95)
    famViewNthF95 mNthFNext where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNthFNext
  resultIndices := ctorIdx mNthFNext
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 95) rfl rfl
    (ctorDom mNthFNext)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecNthF : RecursorEliminationAdmitted (envPre 95) 95 recNthF where
  family := famViewNthF95
  constructors := [mNthFHere, mNthFNext]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewNthFHere95
    | ⟨1, _⟩ => ctorViewNthFNext95
    | ⟨k+2, h⟩ => absurd h
        (by have : [mNthFHere, mNthFNext].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mNthFHere, mNthFNext].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorNthFHere, minorNthFNext]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecNthF05 : RecursorAdmitted05 (envPre 95) 95 recNthF where
  a := aRecNthF
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 95)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewNthFHere95 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewNthFNext95 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecNthF.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesNthFHere, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesNthFNext, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecNthF.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesNthFHere
        | ⟨1, _⟩ => shapesNthFNext
        | ⟨k+2, h⟩ => absurd h (by have : aRecNthF.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecNthF.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecNthF) (i := ⟨0, by decide⟩)
            (shapes := shapesNthFHere) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecNthF) (i := ⟨1, by decide⟩)
            (shapes := shapesNthFNext) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecNthF.constructors.length = 2 := rfl; omega) }

def famViewNEL128 : PolicyFamilyView (envPre 128) where
  ref := 125
  member := mNEL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 128) rfl rfl
    [.const 4 [], .const 4 []]).get (by decide)

def ctorViewNelNil128 : PolicyConstructorView (envPre 128)
    famViewNEL128 mNelNil where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNelNil
  resultIndices := ctorIdx mNelNil
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 128) rfl rfl
    (ctorDom mNelNil)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewNelCons128 : PolicyConstructorView (envPre 128)
    famViewNEL128 mNelCons where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNelCons
  resultIndices := ctorIdx mNelCons
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 128) rfl rfl
    (ctorDom mNelCons)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecNEL : RecursorEliminationAdmitted (envPre 128) 128 recNEL where
  family := famViewNEL128
  constructors := [mNelNil, mNelCons]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewNelNil128
    | ⟨1, _⟩ => ctorViewNelCons128
    | ⟨k+2, h⟩ => absurd h
        (by have : [mNelNil, mNelCons].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mNelNil, mNelCons].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorNelNil, minorNelCons]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecNEL05 : RecursorAdmitted05 (envPre 128) 128 recNEL where
  a := aRecNEL
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 128)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewNelNil128 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewNelCons128 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecNEL.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesNelNil, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesNelCons, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecNEL.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesNelNil
        | ⟨1, _⟩ => shapesNelCons
        | ⟨k+2, h⟩ => absurd h (by have : aRecNEL.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecNEL.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecNEL) (i := ⟨0, by decide⟩)
            (shapes := shapesNelNil) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecNEL) (i := ⟨1, by decide⟩)
            (shapes := shapesNelCons) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecNEL.constructors.length = 2 := rfl; omega) }

def famViewNTB132 : PolicyFamilyView (envPre 132) where
  ref := 129
  member := mNTB
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 [], .const 106 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 132) rfl rfl
    [.const 34 [], .const 0 [], .const 106 []]).get (by decide)

def ctorViewNtbHere132 : PolicyConstructorView (envPre 132)
    famViewNTB132 mNtbHere where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNtbHere
  resultIndices := ctorIdx mNtbHere
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 132) rfl rfl
    (ctorDom mNtbHere)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewNtbNext132 : PolicyConstructorView (envPre 132)
    famViewNTB132 mNtbNext where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mNtbNext
  resultIndices := ctorIdx mNtbNext
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 132) rfl rfl
    (ctorDom mNtbNext)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecNTB : RecursorEliminationAdmitted (envPre 132) 132 recNTB where
  family := famViewNTB132
  constructors := [mNtbHere, mNtbNext]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewNtbHere132
    | ⟨1, _⟩ => ctorViewNtbNext132
    | ⟨k+2, h⟩ => absurd h
        (by have : [mNtbHere, mNtbNext].length = 2 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k+2, h⟩ => absurd h
        (by have : [mNtbHere, mNtbNext].length = 2 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorNtbHere, minorNtbNext]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

def admRecNTB05 : RecursorAdmitted05 (envPre 132) 132 recNTB where
  a := aRecNTB
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 132)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewNtbHere132 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewNtbNext132 96 (by decide)
      | ⟨k+2, h⟩ => absurd h (by have : aRecNTB.constructors.length = 2 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesNtbHere, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesNtbNext, 96, rfl, rfl⟩
      | ⟨k+2, h⟩ => absurd h (by have : aRecNTB.constructors.length = 2 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesNtbHere
        | ⟨1, _⟩ => shapesNtbNext
        | ⟨k+2, h⟩ => absurd h (by have : aRecNTB.constructors.length = 2 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨k+2, h⟩ => absurd h (by have : aRecNTB.constructors.length = 2 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecNTB) (i := ⟨0, by decide⟩)
            (shapes := shapesNtbHere) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecNTB) (i := ⟨1, by decide⟩)
            (shapes := shapesNtbNext) rfl rfl rfl rfl (by decide)
        | ⟨k+2, h⟩ => absurd h (by have : aRecNTB.constructors.length = 2 := rfl; omega) }

/-! ## §3 recursor admissions: CCT and ValueAt -/

def famViewCCT105 : PolicyFamilyView (envPre 105) where
  ref := 96
  member := mCCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 8 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 105) rfl rfl
    [.const 8 [], .const 4 []]).get (by decide)

def ctorViewCctI105 : PolicyConstructorView (envPre 105)
    famViewCCT105 mCctI where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctI
  resultIndices := ctorIdx mCctI
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 105) rfl rfl
    (ctorDom mCctI)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewCctB105 : PolicyConstructorView (envPre 105)
    famViewCCT105 mCctB where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctB
  resultIndices := ctorIdx mCctB
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 105) rfl rfl
    (ctorDom mCctB)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewCctStr105 : PolicyConstructorView (envPre 105)
    famViewCCT105 mCctStr where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctStr
  resultIndices := ctorIdx mCctStr
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 105) rfl rfl
    (ctorDom mCctStr)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewCctY105 : PolicyConstructorView (envPre 105)
    famViewCCT105 mCctY where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctY
  resultIndices := ctorIdx mCctY
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 105) rfl rfl
    (ctorDom mCctY)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewCctL105 : PolicyConstructorView (envPre 105)
    famViewCCT105 mCctL where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctL
  resultIndices := ctorIdx mCctL
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 105) rfl rfl
    (ctorDom mCctL)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewCctP105 : PolicyConstructorView (envPre 105)
    famViewCCT105 mCctP where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctP
  resultIndices := ctorIdx mCctP
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 105) rfl rfl
    (ctorDom mCctP)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewCctSum105 : PolicyConstructorView (envPre 105)
    famViewCCT105 mCctSum where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctSum
  resultIndices := ctorIdx mCctSum
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 105) rfl rfl
    (ctorDom mCctSum)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def ctorViewCctRec105 : PolicyConstructorView (envPre 105)
    famViewCCT105 mCctRec where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := ctorDom mCctRec
  resultIndices := ctorIdx mCctRec
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := (telTypingAuto (E := envPre 105) rfl rfl
    (ctorDom mCctRec)).get (by decide)
  parameterMirrors := fun i => absurd i.isLt (Nat.not_lt_zero i.val)
  noFamilyInIndices := noFamilyInIndicesB_of (by decide)

def aRecCCT : RecursorEliminationAdmitted (envPre 105) 105 recCCT where
  family := famViewCCT105
  constructors := [mCctI, mCctB, mCctStr, mCctY, mCctL, mCctP, mCctSum, mCctRec]
  constructorViews := fun i => match i with
    | ⟨0, _⟩ => ctorViewCctI105
    | ⟨1, _⟩ => ctorViewCctB105
    | ⟨2, _⟩ => ctorViewCctStr105
    | ⟨3, _⟩ => ctorViewCctY105
    | ⟨4, _⟩ => ctorViewCctL105
    | ⟨5, _⟩ => ctorViewCctP105
    | ⟨6, _⟩ => ctorViewCctSum105
    | ⟨7, _⟩ => ctorViewCctRec105
    | ⟨k+8, h⟩ => absurd h
        (by have : [mCctI, mCctB, mCctStr, mCctY, mCctL, mCctP, mCctSum, mCctRec].length = 8 := rfl; omega)
  constructorsPresent := fun i => match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl
    | ⟨4, _⟩ => rfl
    | ⟨5, _⟩ => rfl
    | ⟨6, _⟩ => rfl
    | ⟨7, _⟩ => rfl
    | ⟨k+8, h⟩ => absurd h
        (by have : [mCctI, mCctB, mCctStr, mCctY, mCctL, mCctP, mCctSum, mCctRec].length = 8 := rfl; omega)
  recursorRef := rfl
  minorTypes := [minorCctI, minorCctB, minorCctStr, minorCctY, minorCctL, minorCctP, minorCctSum, minorCctRec]
  minorCount := rfl
  policy := .propOnly
  selected := .multipleProp (fun _ => rfl) (by decide)
  recursorArity := rfl
  recursorType := rfl

set_option maxHeartbeats 12800000 in
def admRecCCT05 : RecursorAdmitted05 (envPre 105) 105 recCCT where
  a := aRecCCT
  hfresh := rfl
  h04 := ctorCensusB_sound (tbl := srcMembersG.take 105)
      (by decide) (by decide)
  h07 := fun _ _ => .inl (fun _ => rfl)
  h08 := fun i => match i with
      | ⟨0, _⟩ => ctorFieldsPermitted_of_B ctorViewCctI105 96 (by decide)
      | ⟨1, _⟩ => ctorFieldsPermitted_of_B ctorViewCctB105 96 (by decide)
      | ⟨2, _⟩ => ctorFieldsPermitted_of_B ctorViewCctStr105 96 (by decide)
      | ⟨3, _⟩ => ctorFieldsPermitted_of_B ctorViewCctY105 96 (by decide)
      | ⟨4, _⟩ => ctorFieldsPermitted_of_B ctorViewCctL105 96 (by decide)
      | ⟨5, _⟩ => ctorFieldsPermitted_of_B ctorViewCctP105 96 (by decide)
      | ⟨6, _⟩ => ctorFieldsPermitted_of_B ctorViewCctSum105 96 (by decide)
      | ⟨7, _⟩ => ctorFieldsPermitted_of_B ctorViewCctRec105 96 (by decide)
      | ⟨k+8, h⟩ => absurd h (by have : aRecCCT.constructors.length = 8 := rfl; omega)
  h12 := fun i => match i with
      | ⟨0, _⟩ => ⟨shapesCctI, 96, rfl, rfl⟩
      | ⟨1, _⟩ => ⟨shapesCctB, 96, rfl, rfl⟩
      | ⟨2, _⟩ => ⟨shapesCctStr, 96, rfl, rfl⟩
      | ⟨3, _⟩ => ⟨shapesCctY, 96, rfl, rfl⟩
      | ⟨4, _⟩ => ⟨shapesCctL, 96, rfl, rfl⟩
      | ⟨5, _⟩ => ⟨shapesCctP, 96, rfl, rfl⟩
      | ⟨6, _⟩ => ⟨shapesCctSum, 96, rfl, rfl⟩
      | ⟨7, _⟩ => ⟨shapesCctRec, 96, rfl, rfl⟩
      | ⟨k+8, h⟩ => absurd h (by have : aRecCCT.constructors.length = 8 := rfl; omega)
  h14 := {
      signatureOnly := rfl
      shapesAt := fun i => match i with
        | ⟨0, _⟩ => shapesCctI
        | ⟨1, _⟩ => shapesCctB
        | ⟨2, _⟩ => shapesCctStr
        | ⟨3, _⟩ => shapesCctY
        | ⟨4, _⟩ => shapesCctL
        | ⟨5, _⟩ => shapesCctP
        | ⟨6, _⟩ => shapesCctSum
        | ⟨7, _⟩ => shapesCctRec
        | ⟨k+8, h⟩ => absurd h (by have : aRecCCT.constructors.length = 8 := rfl; omega)
      fuelAt := fun _ => 96
      analyzed := fun i => match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
        | ⟨2, _⟩ => rfl
        | ⟨3, _⟩ => rfl
        | ⟨4, _⟩ => rfl
        | ⟨5, _⟩ => rfl
        | ⟨6, _⟩ => rfl
        | ⟨7, _⟩ => rfl
        | ⟨k+8, h⟩ => absurd h (by have : aRecCCT.constructors.length = 8 := rfl; omega)
      typed := fun i => match i with
        | ⟨0, _⟩ => iotaEqTyped05_of (a := aRecCCT) (i := ⟨0, by decide⟩)
            (shapes := shapesCctI) rfl rfl rfl rfl (by decide)
        | ⟨1, _⟩ => iotaEqTyped05_of (a := aRecCCT) (i := ⟨1, by decide⟩)
            (shapes := shapesCctB) rfl rfl rfl rfl (by decide)
        | ⟨2, _⟩ => iotaEqTyped05_of (a := aRecCCT) (i := ⟨2, by decide⟩)
            (shapes := shapesCctStr) rfl rfl rfl rfl (by decide)
        | ⟨3, _⟩ => iotaEqTyped05_of (a := aRecCCT) (i := ⟨3, by decide⟩)
            (shapes := shapesCctY) rfl rfl rfl rfl (by decide)
        | ⟨4, _⟩ => iotaEqTyped05_of (a := aRecCCT) (i := ⟨4, by decide⟩)
            (shapes := shapesCctL) rfl rfl rfl rfl (by decide)
        | ⟨5, _⟩ => iotaEqTyped05_of (a := aRecCCT) (i := ⟨5, by decide⟩)
            (shapes := shapesCctP) rfl rfl rfl rfl (by decide)
        | ⟨6, _⟩ => iotaEqTyped05_of (a := aRecCCT) (i := ⟨6, by decide⟩)
            (shapes := shapesCctSum) rfl rfl rfl rfl (by decide)
        | ⟨7, _⟩ => iotaEqTyped05_of (a := aRecCCT) (i := ⟨7, by decide⟩)
            (shapes := shapesCctRec) rfl rfl rfl rfl (by decide)
        | ⟨k+8, h⟩ => absurd h (by have : aRecCCT.constructors.length = 8 := rfl; omega) }

end Rcic.Scm.SrcG

#print axioms Rcic.Scm.SrcG.levelWf_const_of
#print axioms Rcic.Scm.SrcG.inferSpine2
#print axioms Rcic.Scm.SrcG.hasTy_of_inferSpine2_eq
#print axioms Rcic.Scm.SrcG.iotaEqTyped_of
#print axioms Rcic.Scm.SrcG.famViewN3
#print axioms Rcic.Scm.SrcG.ctorViewZero3
#print axioms Rcic.Scm.SrcG.ctorViewSucc3
#print axioms Rcic.Scm.SrcG.aRecN
#print axioms Rcic.Scm.SrcG.admRecN
#print axioms Rcic.Scm.SrcG.aRecBytes
#print axioms Rcic.Scm.SrcG.admRecBytes
#print axioms Rcic.Scm.SrcG.aRecRefT
#print axioms Rcic.Scm.SrcG.admRecRefT
#print axioms Rcic.Scm.SrcG.aRecI
#print axioms Rcic.Scm.SrcG.admRecI
#print axioms Rcic.Scm.SrcG.aRecBL
#print axioms Rcic.Scm.SrcG.admRecBL
#print axioms Rcic.Scm.SrcG.aRecFT
#print axioms Rcic.Scm.SrcG.admRecFT
#print axioms Rcic.Scm.SrcG.aRecBCT
#print axioms Rcic.Scm.SrcG.admRecBCT
#print axioms Rcic.Scm.SrcG.aRecDA
#print axioms Rcic.Scm.SrcG.admRecDA05
#print axioms Rcic.Scm.SrcG.aRecLt
#print axioms Rcic.Scm.SrcG.admRecLt05
#print axioms Rcic.Scm.SrcG.iotaLhsType05_eq_of_noIdx
#print axioms Rcic.Scm.SrcG.iotaEqTyped05_of
#print axioms Rcic.Scm.SrcG.daI_judgmentForm_match
#print axioms Rcic.Scm.SrcG.daI_05Form_match
#print axioms Rcic.Scm.SrcG.aRecBC
#print axioms Rcic.Scm.SrcG.admRecBC05
#print axioms Rcic.Scm.SrcG.aRecDM10
#print axioms Rcic.Scm.SrcG.admRecDM1005
#print axioms Rcic.Scm.SrcG.aRecND
#print axioms Rcic.Scm.SrcG.admRecND05
#print axioms Rcic.Scm.SrcG.aRecNEA
#print axioms Rcic.Scm.SrcG.admRecNEA05
#print axioms Rcic.Scm.SrcG.aRecIEA
#print axioms Rcic.Scm.SrcG.admRecIEA05
#print axioms Rcic.Scm.SrcG.aRecSL
#print axioms Rcic.Scm.SrcG.admRecSL05
#print axioms Rcic.Scm.SrcG.aRecBLL
#print axioms Rcic.Scm.SrcG.admRecBLL05
#print axioms Rcic.Scm.SrcG.aRecFTL
#print axioms Rcic.Scm.SrcG.admRecFTL05
#print axioms Rcic.Scm.SrcG.aRecBLC
#print axioms Rcic.Scm.SrcG.admRecBLC05
#print axioms Rcic.Scm.SrcG.aRecSEA
#print axioms Rcic.Scm.SrcG.admRecSEA05
#print axioms Rcic.Scm.SrcG.aRecFTE
#print axioms Rcic.Scm.SrcG.admRecFTE05
#print axioms Rcic.Scm.SrcG.aRecNthB
#print axioms Rcic.Scm.SrcG.admRecNthB05
#print axioms Rcic.Scm.SrcG.aRecNthF
#print axioms Rcic.Scm.SrcG.admRecNthF05
#print axioms Rcic.Scm.SrcG.aRecNEL
#print axioms Rcic.Scm.SrcG.admRecNEL05
#print axioms Rcic.Scm.SrcG.aRecNTB
#print axioms Rcic.Scm.SrcG.admRecNTB05
#print axioms Rcic.Scm.SrcG.aRecCCT
#print axioms Rcic.Scm.SrcG.admRecCCT05
