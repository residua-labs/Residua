import rcic.RcicTypedJ
import rcic.RcicEnv
import rcic.RcicTypedIdxAdmitted

/-!
# M3-e — R-CIC's environment judgment on the typed judgment

`main`'s `EnvWf` (`RcicEnv`) types its members with the untyped `HasTy`. That judgment's conversion is
the total relation (R-ConvCollapse: `totalConv`, `retypeAny`), so `EnvWf` admits every typable member at
every type: `def bad : Prop := Type` is well-formed in the empty environment at every level count
(`envWf_badDef`, `RcicAnnEnvBridge`). `EnvWf` also admits an inductive group one member at a time (`EnvWf.indMember`), so a
member can enter between a family and its constructors and name the family. 04 §1, §4 and §7 make a
group ATOMIC: the family, the constructors in candidate order and the derived recursor, with no
provisional member lookupable.

`EnvWfT` is the environment judgment the typed root lands with. It stands next to `EnvWf` as
`RcicTypedJ` stands next to the untyped judgment.
* Bodyless axiom steps type their stored type at the member's declared universe arity, preserving
  its parameters. The implicit arity is inferred from the supplied typing; old monomorphic calls
  infer `0`. Definitions, theorems, and opaque declarations still have arity `0` (R-TypedRules (6);
  00 §20.6, members with a body have arity `0`).
* An inductive group is ONE step (`group`). Its members come in 04 §4 order: the family, the
  constructors, the recursor. Each is admitted by `EnvWf.indMember`'s checks and L-K1's
  `IndGroupAdmitted` against the group built so far, with its stored type typed in the typed judgment
  and the typed content of its admission's views (`IndGroupTypedT`). The recursor's content includes
  each ι equation typed in the typed judgment (`IotaEquationTypedT`, R-NoFunRec-1 step 0). Admission
  types the equation in the untyped `HasTy`, where a typable term has every type (`retypeAny`), so that
  check does not refuse a right-hand side typable at some type. Before step 0 the typing was no premise:
  `main`'s ι reducts were typed in the copy's scope only, by ι subject reduction (`hasTyT_iota_sr`).
* M3-e-3: each constructor's stored type is also typed in 05 §4's ConstructorScope, the base and the
  family. The group built so far is the scope for the family (HeaderScope, the base) and for the
  recursor (DerivationScope, with the constructors). For a constructor it also holds the constructors
  before it, which 05 §4 leaves out.
-/

namespace Rcic.Declarative

/-! ## (1) the typed content of L-K1's admission -/

/-- every domain of a telescope typed, in the typed judgment, at its recorded level. -/
def TelTypedT (E : ResolvedEnv) (n : Nat) (ds : List (Expr Nat)) (levels : Fin ds.length → Level) :
    Prop :=
  ∀ i : Fin ds.length, Nonempty (HasTyT E n (policyPrefixContext ds i.val) ds[i.val] (.sort (levels i)))

/-- a family view's typed content: its parameters and indices typed at their recorded levels. -/
def FamilyTypedT {E : ResolvedEnv} (v : PolicyFamilyView E) : Prop :=
  TelTypedT E v.member.arity (v.parameters ++ v.indices) v.domainsTyped.levels

/-- a constructor view's typed content: its parameters and fields typed at their recorded levels, and
    each parameter a TYPE CONVERSION of the family's (05 §6's mirror check). -/
def CtorTypedT {E : ResolvedEnv} {fam : PolicyFamilyView E} {m : CheckedMember}
    (c : PolicyConstructorView E fam m) : Prop :=
  TelTypedT E fam.member.arity (c.parameters ++ c.fields) c.domainsTyped.levels ∧
  ∀ i : Fin c.parameters.length,
    Nonempty (TyConvT E fam.member.arity (policyPrefixContext c.parameters i.val) c.parameters[i.val]
      (fam.parameters[i.val]'(by rw [← c.parameterCount]; exact i.isLt)))

/-- 05 §14's ι equation at constructor `i`, typed in the typed judgment: the right-hand side admission
    derives at the bound `fuel`, at the equation's type, in the derivation scope (the recursor present as a
    signature). Admission's own clause (`IotaDescriptorClause.typed`) types the same equation in `HasTy`,
    where it cannot fail on a typable right-hand side (R-NoFunRec-1-0, item 4). -/
def IotaEquationTypedT {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length) (fuel : Nat)
    (shapes : List FieldShape) : Prop :=
  match equationDoms a i, iotaSchemaAt a i fuel shapes with
  | some doms, some rhs =>
      Nonempty (HasTyT (extendEnv E r m) m.arity (assumptionCtx doms) rhs (iotaEquationType a i))
  | _, _ => False

/-- the typed ι equation from a checker's answer, which carries its derivation. -/
theorem iotaEquationTypedT_of_check {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} {i : Fin a.constructors.length} {fuel : Nat}
    {shapes : List FieldShape}
    (check : (Γ : LCtx) → (e T : Expr Nat) → Option (HasTyT (extendEnv E r m) m.arity Γ e T))
    (h : (match equationDoms a i, iotaSchemaAt a i fuel shapes with
      | some doms, some rhs => (check (assumptionCtx doms) rhs (iotaEquationType a i)).isSome
      | _, _ => false) = true) :
    IotaEquationTypedT a i fuel shapes := by
  unfold IotaEquationTypedT
  revert h
  rcases equationDoms a i with _ | doms <;> rcases iotaSchemaAt a i fuel shapes with _ | rhs
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; exact ⟨(check _ _ _).get h⟩

/-- the typed content of a member's admission: the views it reads, typed, and at a recursor each ι
    equation typed, its right-hand side read at the shapes and bound admission's clause carries. -/
def IndGroupTypedT {E : ResolvedEnv} {r : Nat} {m : CheckedMember} : IndGroupAdmitted E r m → Prop
  | .family _ view _ _ _ => FamilyTypedT view
  | .constructor family view _ _ _ _ _ => FamilyTypedT family ∧ CtorTypedT view
  | .recursor a _ _ _ _ _ h14 => FamilyTypedT a.family ∧ (∀ i, CtorTypedT (a.constructorViews i)) ∧
      ∀ i, IotaEquationTypedT a i (h14.fuelAt i) (h14.shapesAt i)

/-! ## (2) the environment judgment -/

/-- every constant of `e` is a member of `E`. -/
def ConstsIn (E : ResolvedEnv) : Expr Nat → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const r _ => ∃ m, E.members r = some m
  | .app f x => ConstsIn E f ∧ ConstsIn E x
  | .lam a b => ConstsIn E a ∧ ConstsIn E b
  | .pi a b => ConstsIn E a ∧ ConstsIn E b
  | .letE a v b => ConstsIn E a ∧ ConstsIn E v ∧ ConstsIn E b
  | .lit t =>
      match t with
      | 0 => ∃ m, E.members 1 = some m
      | _ + 1 => (∃ m, E.members 1 = some m) ∧ ∃ m, E.members 2 = some m

/-- the constants a literal names are the constants of its expansion: `natExpand 0`
is `.const 1`, `natExpand (n+1)` is `.app (.const 2) (natExpand n)`. -/
theorem constsIn_of_natExpand {E : ResolvedEnv} : (t : Nat) →
    ConstsIn E (natExpand t) → ConstsIn E (.lit t)
  | 0, h => h
  | 1, h => ⟨h.2, h.1⟩
  | n + 2, h => ⟨(constsIn_of_natExpand (n + 1) h.2).1, h.1⟩

/-- a typed term names only members: every subterm is typed by a premise of its rule, and a constant
    only by the `const` rule. So a term naming a constant outside an environment has no typing there
    (M3-e-3's ConstructorScope). -/
theorem hasTyT_constsIn {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → HasTyT E n Γ e T → ConstsIn E e
  | _, _, _, .sort _ _ => trivial
  | _, _, _, .bvar _ _ _ _ => trivial
  | _, _, _, .const _ _ _ m hres _ _ => ⟨m, hres⟩
  | _, _, _, .pi _ _ _ _ _ hA hB => ⟨hasTyT_constsIn hA, hasTyT_constsIn hB⟩
  | _, _, _, .lam _ _ _ _ _ hA hb => ⟨hasTyT_constsIn hA, hasTyT_constsIn hb⟩
  | _, _, _, .app _ _ _ _ _ hf ha => ⟨hasTyT_constsIn hf, hasTyT_constsIn ha⟩
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb => ⟨hasTyT_constsIn hA, hasTyT_constsIn hv, hasTyT_constsIn hb⟩
  | _, _, _, .lit _ t _ hexp => constsIn_of_natExpand t (hasTyT_constsIn hexp)
  | _, _, _, .conv _ _ _ _ _ h _ => hasTyT_constsIn h

/-- the members of one inductive group, admitted one after another against the group built so far:
    `EnvWf.indMember`'s checks, L-K1's `IndGroupAdmitted`, the stored type typed, the admission's
    typed content. A constructor's stored type is ALSO typed in `S`, 05 §4's ConstructorScope (the base
    and the family, `EnvWfT.group`): a constructor is checked with the family alone present, so every
    constant it names is a member of `S` (`hasTyT_constsIn`), and an earlier constructor, fresh there, is
    not one. The family is checked in the base (HeaderScope) and the recursor
    in the group with its constructors (DerivationScope): for those two, the group built so far is the
    scope. R-NoFunRec-1 B2 (step 2d-2b): the recursor/index obligation `hidxAdmT` is the TYPED
    counterpart `IdxAdmittedT hadm` — at the `.recursor` admission it is
    `RecursorGroupIdxAdmittedT`, ranging over shape witnesses with coverage from admission's own
    descriptor (`IdxAdmittedT.recursor_cases` makes that non-vacuous). The legacy obligation
    `m.mclass = .recursorM → RecursorGroupIdxAdmitted E r m` is unchanged and still used by the
    legacy `EnvWf`. -/
inductive GroupMembersT (S : ResolvedEnv) : ResolvedEnv → List (Nat × CheckedMember) → ResolvedEnv → Type
  | nil (E : ResolvedEnv) : GroupMembersT S E [] E
  | cons (E : ResolvedEnv) (r : Nat) (m : CheckedMember) (rest : List (Nat × CheckedMember))
      (E' : ResolvedEnv) (hfresh : E.members r = none) (hnobody : m.body = none)
      (hclT : ∀ k, lift k 1 m.mtype = m.mtype)
      (harity : m.mclass = .inductiveM → isArity m.mtype = true)
      (hlvlB : exprLevelsBounded m.arity m.mtype = true)
      (hcanon : exprFamCanonical E m.mtype = true) (harities : groupArityCoherent E m = true)
      (hadm : IndGroupAdmitted E r m) (hidxAdmT : IdxAdmittedT hadm) (u : Level)
      (hT : HasTyT E m.arity [] m.mtype (.sort u))
      (hTc : m.mclass = .constructorM → Nonempty (HasTyT S m.arity [] m.mtype (.sort u)))
      (htyped : IndGroupTypedT hadm) (hrest : GroupMembersT S (extendEnv E r m) rest E') :
      GroupMembersT S E ((r, m) :: rest) E'

/-- R-CIC's environment judgment on the typed judgment (04 §6–§7). -/
inductive EnvWfT : ResolvedEnv → Type
  | empty : EnvWfT emptyEnv
  /-- Universe-polymorphic bodyless declaration. The implicit arity is inferred
      from `hA`; existing monomorphic calls still infer `0`. The stored type is
      checked at exactly that arity, closed in locals, and level-bounded. -/
  | axiom {arity : Nat} (E : ResolvedEnv) (r : Nat) (A : Expr Nat) (u : Level)
      (hE : EnvWfT E) (hfresh : E.members r = none) (hA : HasTyT E arity [] A (.sort u))
      (hcl : ∀ k, lift k 1 A = A) (hlvl : exprLevelsBounded arity A = true) :
      EnvWfT (extendEnv E r ⟨.axiomM, arity, A, none⟩)
  | definition (E : ResolvedEnv) (r : Nat) (A v : Expr Nat) (u : Level)
      (hE : EnvWfT E) (hfresh : E.members r = none)
      (hA : HasTyT E 0 [] A (.sort u)) (hv : HasTyT E 0 [] v A)
      (hclA : ∀ k, lift k 1 A = A) (hclv : ∀ k, lift k 1 v = v)
      (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true) :
      EnvWfT (extendEnv E r ⟨.definitionM, 0, A, some v⟩)
  | thm (E : ResolvedEnv) (r : Nat) (A p : Expr Nat)
      (hE : EnvWfT E) (hfresh : E.members r = none)
      (hA : HasTyT E 0 [] A (.sort .zero)) (hp : HasTyT E 0 [] p A)
      (hclA : ∀ k, lift k 1 A = A) (hclp : ∀ k, lift k 1 p = p)
      (hlvlA : exprLevelsBounded 0 A = true) (hlvlp : exprLevelsBounded 0 p = true) :
      EnvWfT (extendEnv E r ⟨.theoremM, 0, A, some p⟩)
  | opaque (E : ResolvedEnv) (r : Nat) (A v : Expr Nat) (u : Level)
      (hE : EnvWfT E) (hfresh : E.members r = none)
      (hA : HasTyT E 0 [] A (.sort u)) (hv : HasTyT E 0 [] v A)
      (hclA : ∀ k, lift k 1 A = A) (hclv : ∀ k, lift k 1 v = v)
      (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true) :
      EnvWfT (extendEnv E r ⟨.opaqueM, 0, A, some v⟩)
  /-- one inductive group, atomically (04 §4, §7): the family, its constructors, its recursor. Each
      constructor's stored type is also typed in ConstructorScope, `extendEnv E f fm` (05 §4). -/
  | group (E : ResolvedEnv) (f : Nat) (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
      (rr : Nat) (rm : CheckedMember) (E' : ResolvedEnv) (hE : EnvWfT E)
      (hfam : fm.mclass = .inductiveM) (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
      (hrec : rm.mclass = .recursorM)
      (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E') :
      EnvWfT E'

/-- an environment with no inductive group: every member a singleton (04 §6). -/
def NoGroupEnv (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m →
    m.mclass ≠ .inductiveM ∧ m.mclass ≠ .constructorM ∧ m.mclass ≠ .recursorM

end Rcic.Declarative

