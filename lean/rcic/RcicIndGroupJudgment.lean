/-
L-K1 (#6075). One inductive-group admission judgment: 04 §1 and
05 §§6–14, one clause per rule. It lives here, not in
`RcicIndGroupAdmitted`, because `EnvWf` has to import it and must not
import `RcicElimPolicy` (`RcicInvertFamily` imports `RcicEnv`).

`CtorCensus` / `CtorBeforeRecursors` / `NoRecursorFor` are the #6070
statements, moved with `memberFamRef` (`RcicFamRef`). Same predicates:
not a second copy, and not a weaker projection. Fixture inhabitants
stay in `RcicIndGroupAdmitted`.
-/
import rcic.RcicInductivePolicy
import rcic.RcicFamRef

namespace Rcic.Declarative

/-! ## Rule table

One constructor per rule in 04 §1 and 05 §§6–14. No other rule is
admitted from this module. -/

inductive SpecRule : Type
  | groupAtomic_04_1
  | ctorShape_05_6
  | fieldUniverse_05_7
  | occurrence_05_8
  | positivity_05_9
  | elimPolicy_05_10
  | motive_05_11
  | minorPremises_05_12
  | completeRecursor_05_13
  | iotaDescriptor_05_14
  deriving DecidableEq, Repr

/-! ## 05 §7 -/

/-- Field `T : Sort v` against family result `uI`.
Uniform Prop: impredicativity, no level test.
Uniform Type: `v ≤ₙ uI`.
A mixed result fails both arms. Parameters are not fields;
`PolicyConstructorView.fields` is already the non-parameter suffix. -/
def FieldUniverseAdmitted {E : ResolvedEnv} {family : PolicyFamilyView E}
    {member : CheckedMember} (c : PolicyConstructorView E family member) : Prop :=
  ∀ j : Fin c.fields.length,
    UniformProp family.resultLevel ∨
      (UniformType family.resultLevel ∧ leN (c.fieldLevel j) family.resultLevel)

/-! ## 04 §1 constructor contiguity

`CtorBeforeRecursors` only says no recursor for the family exists.
`CtorCensus` is stated at the recursor, not at the constructor being
added. A constructor at ref 43 whose family sits at ref 11 still
passes `CtorBeforeRecursors`. -/

def IsFamilyCtor (E : ResolvedEnv) (f c : Nat) : Prop :=
  ∃ cm, E.members c = some cm ∧ cm.mclass = .constructorM ∧
    memberFamRef cm = some f

def CtorContiguous (E : ResolvedEnv) (r : Nat) (m : CheckedMember) : Prop :=
  ∃ f, memberFamRef m = some f ∧ f < r ∧
    (∀ c, f < c → c < r → IsFamilyCtor E f c) ∧
    (∀ c, IsFamilyCtor E f c → f < c ∧ c < r)

def FieldPermitted (E : ResolvedEnv) (fam nuniv nparams nindices depth : Nat)
    (T : Expr Nat) (shape : FieldShape) : Prop :=
  ∃ fuel indices, fieldAnalyze E fuel fam nuniv nparams nindices depth T =
    .permitted shape indices

def FieldRefused (E : ResolvedEnv) (fam nuniv nparams nindices depth : Nat)
    (T : Expr Nat) (why : PositivityRefusal) : Prop :=
  ∃ fuel, fieldAnalyze E fuel fam nuniv nparams nindices depth T = .refused why

def CtorFieldsPermitted {E : ResolvedEnv} {family : PolicyFamilyView E}
    {member : CheckedMember} (c : PolicyConstructorView E family member) : Prop :=
  ∀ j : Fin c.fields.length,
    ∃ shape, FieldPermitted E family.ref family.member.arity
      family.parameters.length family.indices.length
      (family.parameters.length + j.val) c.fields[j.val] shape

/-! ## Decider stability

A concrete verdict (permitted or refused) at one bound is the verdict
at every larger bound. `unresolved` is running out of bound, not one
of the three positivity classes, and it is not evidence of
`FieldRefused`. -/

theorem whnfFuel_mono (E : ResolvedEnv) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') {e w : Expr Nat}
    (h : whnfFuel E fuel e = some w) : whnfFuel E fuel' e = some w := by
  induction fuel generalizing fuel' e w with
  | zero =>
      simp only [whnfFuel] at h
      cases h
  | succ fuel ih =>
      cases fuel' with
      | zero => omega
      | succ fuel' =>
          have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
          cases hsp : appsSpine e with
          | mk head args =>
              cases head with
              | lam A b =>
                  cases args with
                  | nil =>
                      simp only [whnfFuel, hsp] at h ⊢
                      exact h
                  | cons a rest =>
                      simp only [whnfFuel, hsp] at h ⊢
                      exact ih hle' h
              | letE A v b =>
                  simp only [whnfFuel, hsp] at h ⊢
                  exact ih hle' h
              | const r ls =>
                  cases hb : transparentBody E r ls with
                  | none =>
                      simp only [whnfFuel, hsp, hb] at h ⊢
                      exact h
                  | some body =>
                      simp only [whnfFuel, hsp, hb] at h ⊢
                      exact ih hle' h
              | bvar _ =>
                  simp only [whnfFuel, hsp] at h ⊢
                  exact h
              | sort _ =>
                  simp only [whnfFuel, hsp] at h ⊢
                  exact h
              | app _ _ =>
                  simp only [whnfFuel, hsp] at h ⊢
                  exact h
              | pi _ _ =>
                  simp only [whnfFuel, hsp] at h ⊢
                  exact h
              | lit _ =>
                  simp only [whnfFuel, hsp] at h ⊢
                  exact h

theorem containsFamilyFuel_mono (E : ResolvedEnv) (fam : Nat) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') {e : Expr Nat} {b : Bool}
    (h : containsFamilyFuel E fam fuel e = some b) :
    containsFamilyFuel E fam fuel' e = some b := by
  induction fuel generalizing fuel' e b with
  | zero =>
      simp only [containsFamilyFuel] at h
      cases h
  | succ fuel ih =>
      cases fuel' with
      | zero => omega
      | succ fuel' =>
          have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
          cases e with
          | bvar _ =>
              simp only [containsFamilyFuel] at h ⊢
              exact h
          | sort _ =>
              simp only [containsFamilyFuel] at h ⊢
              exact h
          | lit t =>
              cases t with
              | zero =>
                  simp only [containsFamilyFuel] at h ⊢
                  exact ih hle' h
              | succ n =>
                  rw [containsFamilyFuel.eq_5] at h
                  rw [containsFamilyFuel.eq_5]
                  cases h2 : containsFamilyFuel E fam fuel (.const 2 []) with
                  | none =>
                      simp only [h2] at h
                      cases h
                  | some b2 =>
                      have h2' := ih hle' h2
                      simp only [h2] at h
                      rw [h2']
                      cases b2 with
                      | false => exact ih hle' h
                      | true => exact h
          | const r ls =>
              simp only [containsFamilyFuel] at h ⊢
              by_cases hr : r = fam
              · simp only [hr, ite_true] at h ⊢
                exact h
              · simp only [hr, ite_false] at h ⊢
                cases hb : transparentBody E r ls with
                | none =>
                    simp only [hb] at h ⊢
                    exact h
                | some body =>
                    simp only [hb] at h ⊢
                    exact ih hle' h
          | app f x =>
              simp only [containsFamilyFuel] at h ⊢
              cases hf : containsFamilyFuel E fam fuel f with
              | none => simp [hf] at h
              | some bf =>
                  simp only [hf] at h ⊢
                  have hf' := ih hle' hf
                  simp only [hf']
                  cases bf
                  · exact ih hle' h
                  · exact h
          | lam a body =>
              simp only [containsFamilyFuel] at h ⊢
              cases ha : containsFamilyFuel E fam fuel a with
              | none => simp [ha] at h
              | some ba =>
                  simp only [ha] at h ⊢
                  have ha' := ih hle' ha
                  simp only [ha']
                  cases ba
                  · exact ih hle' h
                  · exact h
          | pi a body =>
              simp only [containsFamilyFuel] at h ⊢
              cases ha : containsFamilyFuel E fam fuel a with
              | none => simp [ha] at h
              | some ba =>
                  simp only [ha] at h ⊢
                  have ha' := ih hle' ha
                  simp only [ha']
                  cases ba
                  · exact ih hle' h
                  · exact h
          | letE a v body =>
              simp only [containsFamilyFuel] at h ⊢
              cases ha : containsFamilyFuel E fam fuel a with
              | none => simp [ha] at h
              | some ba =>
                  simp only [ha] at h ⊢
                  have ha' := ih hle' ha
                  simp only [ha']
                  cases ba
                  · cases hv : containsFamilyFuel E fam fuel v with
                    | none => simp [hv] at h
                    | some bv =>
                        simp only [hv] at h ⊢
                        have hv' := ih hle' hv
                        simp only [hv']
                        cases bv
                        · exact ih hle' h
                        · exact h
                  · exact h

theorem indicesCleanFuel_mono (E : ResolvedEnv) (fam : Nat) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') {es : List (Expr Nat)} {b : Bool}
    (h : indicesCleanFuel E fam fuel es = some b) :
    indicesCleanFuel E fam fuel' es = some b := by
  induction fuel generalizing fuel' es b with
  | zero =>
      cases es with
      | nil =>
          simp only [indicesCleanFuel] at h ⊢
          exact h
      | cons _ _ =>
          simp only [indicesCleanFuel] at h
          cases h
  | succ fuel ih =>
      cases fuel' with
      | zero => omega
      | succ fuel' =>
          have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
          cases es with
          | nil =>
              simp only [indicesCleanFuel] at h ⊢
              exact h
          | cons A As =>
              simp only [indicesCleanFuel] at h ⊢
              cases hA : containsFamilyFuel E fam fuel A with
              | none => simp [hA] at h
              | some bA =>
                  simp only [hA] at h ⊢
                  have hA' := containsFamilyFuel_mono E fam hle' hA
                  simp only [hA']
                  cases bA
                  · exact ih hle' h
                  · exact h

theorem domainsContainFuel_mono (E : ResolvedEnv) (fam : Nat) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') {es : List (Expr Nat)} {b : Bool}
    (h : domainsContainFuel E fam fuel es = some b) :
    domainsContainFuel E fam fuel' es = some b := by
  induction fuel generalizing fuel' es b with
  | zero =>
      cases es with
      | nil =>
          simp only [domainsContainFuel] at h ⊢
          exact h
      | cons _ _ =>
          simp only [domainsContainFuel] at h
          cases h
  | succ fuel ih =>
      cases fuel' with
      | zero => omega
      | succ fuel' =>
          have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
          cases es with
          | nil =>
              simp only [domainsContainFuel] at h ⊢
              exact h
          | cons A As =>
              simp only [domainsContainFuel] at h ⊢
              cases hA : containsFamilyFuel E fam fuel A with
              | none => simp [hA] at h
              | some bA =>
                  simp only [hA] at h ⊢
                  have hA' := containsFamilyFuel_mono E fam hle' hA
                  simp only [hA']
                  cases bA
                  · exact ih hle' h
                  · exact h

theorem piTelescopeFuel_mono (E : ResolvedEnv) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') {e : Expr Nat} {ds : List (Expr Nat)} {body : Expr Nat}
    (h : piTelescopeFuel E fuel e = some (ds, body)) :
    piTelescopeFuel E fuel' e = some (ds, body) := by
  induction fuel generalizing fuel' e ds body with
  | zero =>
      simp only [piTelescopeFuel] at h
      cases h
  | succ fuel ih =>
      cases fuel' with
      | zero => omega
      | succ fuel' =>
          have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
          simp only [piTelescopeFuel] at h ⊢
          cases hw : whnfFuel E fuel e with
          | none => simp [hw] at h
          | some w =>
              simp only [hw] at h
              have hw' := whnfFuel_mono E hle' hw
              simp only [hw']
              cases w with
              | pi A B =>
                  cases ht : piTelescopeFuel E fuel B with
                  | none => simp [ht] at h
                  | some pr =>
                      simp only [ht] at h
                      cases pr with
                      | mk ds' body' =>
                          have ht' := ih hle' ht
                          simp only [ht']
                          exact h
              | bvar _ => exact h
              | sort _ => exact h
              | const _ _ => exact h
              | app _ _ => exact h
              | lam _ _ => exact h
              | letE _ _ _ => exact h
              | lit _ => exact h

theorem properFamilyFuel_mono (E : ResolvedEnv)
    {fuel fuel' fam nuniv nparams nindices top : Nat}
    (hle : fuel ≤ fuel') {body : Expr Nat} {b : Bool}
    (h : properFamilyFuel E fuel fam nuniv nparams nindices top body = some b) :
    properFamilyFuel E fuel' fam nuniv nparams nindices top body = some b := by
  simp only [properFamilyFuel] at h ⊢
  cases hsp : appsSpine body with
  | mk head args =>
      simp only [hsp] at h ⊢
      cases head with
      | const r ls =>
          by_cases hshape : r = fam && args.length = nparams + nindices &&
              exactParamLocals (args.take nparams) top &&
              ls = (List.range nuniv).map Level.param
          · simp only [hshape, ite_true] at h ⊢
            cases hi : indicesCleanFuel E fam fuel (args.drop nparams) with
            | none => simp [hi] at h
            | some bi =>
                simp only [hi] at h ⊢
                have hi' := indicesCleanFuel_mono E fam hle hi
                simp only [hi']
                exact h
          · simp only [hshape, ite_false] at h ⊢
            exact h
      | bvar _ => exact h
      | sort _ => exact h
      | app _ _ => exact h
      | lam _ _ => exact h
      | pi _ _ => exact h
      | letE _ _ _ => exact h
      | lit _ => exact h

theorem fieldAnalyze_mono (E : ResolvedEnv)
    {fuel fuel' fam nuniv nparams nindices depth : Nat}
    (hle : fuel ≤ fuel') {T : Expr Nat} {v : FieldAnalyze}
    (h : fieldAnalyze E fuel fam nuniv nparams nindices depth T = v)
    (hv : v ≠ .unresolved) :
    fieldAnalyze E fuel' fam nuniv nparams nindices depth T = v := by
  cases fuel with
  | zero =>
      simp only [fieldAnalyze] at h
      exact absurd h.symm hv
  | succ fuel =>
      cases fuel' with
      | zero => omega
      | succ fuel' =>
          have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
          simp only [fieldAnalyze] at h ⊢
          cases ht : piTelescopeFuel E fuel T with
          | none =>
              simp only [ht] at h
              exact absurd h.symm hv
          | some pr =>
              cases pr with
              | mk doms body =>
                  simp only [ht] at h
                  have ht' := piTelescopeFuel_mono E hle' ht
                  simp only [ht']
                  cases hd : domainsContainFuel E fam fuel doms with
                  | none =>
                      simp only [hd] at h
                      exact absurd h.symm hv
                  | some bdom =>
                      simp only [hd] at h
                      have hd' := domainsContainFuel_mono E fam hle' hd
                      simp only [hd']
                      cases bdom
                      · cases hp : properFamilyFuel E fuel fam nuniv nparams nindices
                            (doms.length + depth - 1) body with
                        | none =>
                            simp only [hp] at h
                            exact absurd h.symm hv
                        | some bp =>
                            simp only [hp] at h
                            have hp' := properFamilyFuel_mono E hle' hp
                            simp only [hp']
                            cases bp
                            · cases hc : containsFamilyFuel E fam fuel T with
                              | none =>
                                  simp only [hc] at h
                                  exact absurd h.symm hv
                              | some bc =>
                                  simp only [hc] at h
                                  have hc' := containsFamilyFuel_mono E fam hle' hc
                                  simp only [hc']
                                  cases bc
                                  · exact h
                                  · cases hsp : appsSpine body with
                                    | mk head args =>
                                        simp only [hsp] at h ⊢
                                        cases head with
                                        | const r ls =>
                                            by_cases hr : r = fam
                                            · simp only [hr, ite_true] at h ⊢
                                              exact h
                                            · simp only [hr, ite_false] at h ⊢
                                              cases ha : domainsContainFuel E fam fuel args with
                                              | none =>
                                                  simp only [ha] at h
                                                  exact absurd h.symm hv
                                              | some ba =>
                                                  simp only [ha] at h ⊢
                                                  have ha' := domainsContainFuel_mono E fam hle' ha
                                                  simp only [ha']
                                                  exact h
                                        | bvar _ => exact h
                                        | sort _ => exact h
                                        | app _ _ => exact h
                                        | lam _ _ => exact h
                                        | pi _ _ => exact h
                                        | letE _ _ _ => exact h
                                        | lit _ => exact h
                            · exact h
                      · exact h

theorem fieldAnalyze_agree (E : ResolvedEnv) (fam nuniv nparams nindices depth : Nat)
    (T : Expr Nat) {fuel₁ fuel₂ : Nat} {v₁ v₂ : FieldAnalyze}
    (h₁ : fieldAnalyze E fuel₁ fam nuniv nparams nindices depth T = v₁)
    (h₂ : fieldAnalyze E fuel₂ fam nuniv nparams nindices depth T = v₂)
    (hv₁ : v₁ ≠ .unresolved) (hv₂ : v₂ ≠ .unresolved) : v₁ = v₂ := by
  rcases Nat.le_total fuel₁ fuel₂ with hle | hle
  · exact (fieldAnalyze_mono E hle h₁ hv₁).symm.trans h₂
  · exact h₁.symm.trans (fieldAnalyze_mono E hle h₂ hv₂)

theorem FieldPermitted.not_refused {E : ResolvedEnv}
    {fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    {shape : FieldShape} {why : PositivityRefusal}
    (hp : FieldPermitted E fam nuniv nparams nindices depth T shape)
    (hr : FieldRefused E fam nuniv nparams nindices depth T why) : False := by
  rcases hp with ⟨fuel₁, _, hp⟩
  rcases hr with ⟨fuel₂, hr⟩
  have hagree := fieldAnalyze_agree E fam nuniv nparams nindices depth T hp hr
    (fun h => by cases h) (fun h => by cases h)
  cases hagree

theorem FieldRefused.unique {E : ResolvedEnv}
    {fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    {why₁ why₂ : PositivityRefusal}
    (h₁ : FieldRefused E fam nuniv nparams nindices depth T why₁)
    (h₂ : FieldRefused E fam nuniv nparams nindices depth T why₂) : why₁ = why₂ := by
  rcases h₁ with ⟨fuel₁, h₁⟩
  rcases h₂ with ⟨fuel₂, h₂⟩
  have hagree := fieldAnalyze_agree E fam nuniv nparams nindices depth T h₁ h₂
    (fun h => by cases h) (fun h => by cases h)
  cases hagree
  rfl

theorem fieldShapesFuel_mono (E : ResolvedEnv)
    {fuel fuel' fam nuniv nparams nindices depth : Nat}
    (hle : fuel ≤ fuel') {Ts : List (Expr Nat)} {shapes : List FieldShape}
    (h : fieldShapesFuel E fuel fam nuniv nparams nindices depth Ts = some shapes) :
    fieldShapesFuel E fuel' fam nuniv nparams nindices depth Ts = some shapes := by
  induction Ts generalizing fuel fuel' depth shapes with
  | nil =>
      simp only [fieldShapesFuel] at h ⊢
      exact h
  | cons T Ts ih =>
      simp only [fieldShapesFuel] at h ⊢
      cases hv : fieldAnalyze E fuel fam nuniv nparams nindices depth T with
      | unresolved => simp [hv] at h
      | refused _ => simp [hv] at h
      | permitted shape _ =>
          simp only [hv] at h
          have hv' := fieldAnalyze_mono E hle hv (fun hneq => by cases hneq)
          simp only [hv']
          cases hrest : fieldShapesFuel E fuel fam nuniv nparams nindices (depth + 1) Ts with
          | none => simp [hrest] at h
          | some rest =>
              simp only [hrest, Option.map] at h ⊢
              have hrest' := ih hle hrest
              simp only [hrest']
              exact h

theorem fieldShapesFuel_agree (E : ResolvedEnv)
    {fuel₁ fuel₂ fam nuniv nparams nindices depth : Nat}
    {Ts : List (Expr Nat)} {shapes₁ shapes₂ : List FieldShape}
    (h₁ : fieldShapesFuel E fuel₁ fam nuniv nparams nindices depth Ts = some shapes₁)
    (h₂ : fieldShapesFuel E fuel₂ fam nuniv nparams nindices depth Ts = some shapes₂) :
    shapes₁ = shapes₂ := by
  rcases Nat.le_total fuel₁ fuel₂ with hle | hle
  · exact Option.some.inj ((fieldShapesFuel_mono E hle h₁).symm.trans h₂)
  · exact Option.some.inj (h₁.symm.trans (fieldShapesFuel_mono E hle h₂))

theorem funRecArg_mono (E : ResolvedEnv) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') {rec : Expr Nat} {preMajor : List (Expr Nat)}
    {nparams nMinors : Nat} {f A : Expr Nat} {inner : Nat} {call : Expr Nat}
    (h : funRecArg E fuel rec preMajor nparams nMinors f A inner = some call) :
    funRecArg E fuel' rec preMajor nparams nMinors f A inner = some call := by
  simp only [funRecArg] at h ⊢
  cases ht : piTelescopeFuel E fuel A with
  | none => simp [ht] at h
  | some pr =>
      cases pr with
      | mk doms famApp =>
          simp only [ht] at h
          have ht' := piTelescopeFuel_mono E hle ht
          simp only [ht']
          exact h

theorem iotaArgs_mono (E : ResolvedEnv) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') {rec : Expr Nat} {preMajor : List (Expr Nat)}
    {nparams nMinors : Nat} :
    ∀ {shapes fields tel args},
      iotaArgs E fuel rec preMajor nparams nMinors shapes fields tel = some args →
      iotaArgs E fuel' rec preMajor nparams nMinors shapes fields tel = some args := by
  intro shapes fields tel args h
  induction shapes generalizing fields tel args with
  | nil =>
      cases fields <;> cases tel <;> simp only [iotaArgs] at h ⊢ <;> exact h
  | cons shape shapes ih =>
      cases fields with
      | nil =>
          cases shape with
          | nonrecursive => cases tel <;> simp only [iotaArgs] at h <;> cases h
          | recursive inner =>
              cases inner <;> cases tel <;> simp only [iotaArgs] at h <;> cases h
      | cons f fs =>
          cases tel with
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              cases shape <;> simp only [iotaArgs] at h <;> cases h
          | pi A B =>
              cases shape with
              | nonrecursive =>
                  simp only [iotaArgs] at h ⊢
                  cases hr : iotaArgs E fuel rec preMajor nparams nMinors shapes fs
                      (instantiate0 f B) with
                  | none => simp [hr] at h
                  | some rest =>
                      simp only [hr, Option.map] at h
                      have hr' := ih hr
                      simp only [hr']
                      exact h
              | recursive inner =>
                  cases inner with
                  | zero =>
                      simp only [iotaArgs] at h ⊢
                      cases ht : piTelescopeFuel E fuel A with
                      | none => simp [ht] at h
                      | some pr =>
                          cases pr with
                          | mk doms famApp =>
                              have ht' := piTelescopeFuel_mono E hle ht
                              simp only [ht] at h
                              simp only [ht']
                              cases doms with
                              | nil =>
                                  cases hr : iotaArgs E fuel rec preMajor nparams nMinors shapes fs
                                      (instantiate0 f B) with
                                  | none => simp [hr] at h
                                  | some rest =>
                                      simp only [hr, Option.map] at h
                                      have hr' := ih hr
                                      simp only [hr']
                                      exact h
                              | cons d ds => simp at h
                  | succ inner =>
                      simp only [iotaArgs] at h ⊢
                      cases hc : funRecArg E fuel rec preMajor nparams nMinors f A (inner + 1) with
                      | none => simp [hc] at h
                      | some call =>
                          have hc' := funRecArg_mono E hle hc
                          simp only [hc] at h
                          simp only [hc']
                          cases hr : iotaArgs E fuel rec preMajor nparams nMinors shapes fs
                              (instantiate0 f B) with
                          | none => simp [hr] at h
                          | some rest =>
                              simp only [hr, Option.map] at h
                              have hr' := ih hr
                              simp only [hr']
                              exact h

theorem iotaOpenRhs_mono (E : ResolvedEnv) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') {rec minor : Expr Nat} {preMajor : List (Expr Nat)}
    {nparams nMinors : Nat} {shapes : List FieldShape}
    {fields : List (Expr Nat)} {tel rhs : Expr Nat}
    (h : iotaOpenRhs E fuel rec minor preMajor nparams nMinors shapes fields tel =
      some rhs) :
    iotaOpenRhs E fuel' rec minor preMajor nparams nMinors shapes fields tel =
      some rhs := by
  simp only [iotaOpenRhs] at h ⊢
  cases ha : iotaArgs E fuel rec preMajor nparams nMinors shapes fields tel with
  | none => simp [ha] at h
  | some args =>
      simp only [ha, Option.map] at h
      have ha' := iotaArgs_mono E hle ha
      simp only [ha']
      exact h

theorem iotaOpenRhs_agree (E : ResolvedEnv) {fuel₁ fuel₂ : Nat}
    {rec minor : Expr Nat} {preMajor : List (Expr Nat)} {nparams nMinors : Nat}
    {shapes : List FieldShape} {fields : List (Expr Nat)} {tel rhs₁ rhs₂ : Expr Nat}
    (h₁ : iotaOpenRhs E fuel₁ rec minor preMajor nparams nMinors shapes fields tel =
      some rhs₁)
    (h₂ : iotaOpenRhs E fuel₂ rec minor preMajor nparams nMinors shapes fields tel =
      some rhs₂) : rhs₁ = rhs₂ := by
  rcases Nat.le_total fuel₁ fuel₂ with hle | hle
  · exact Option.some.inj ((iotaOpenRhs_mono E hle h₁).symm.trans h₂)
  · exact Option.some.inj (h₁.symm.trans (iotaOpenRhs_mono E hle h₂))

/-! ## 05 §12

Walk the constructor's field telescope. A nonrecursive field is one
binder. A recursive field is that binder plus one IH binder, then the
remaining telescope is lifted across the IH (`lift 0 1`), which is
the `MinorContextMap` for later fields, result indices, and the
constructor accumulation. Direct recursion is `inner = 0`.

A recursive field is read as 05 §9 classifies it: its Π telescope and
its family application after β, ζ and δ at transparent heads
(`piTelescopeFuel`, the analysis's own reading), at a bound. The stored
type's spine is not read. With `Id := λ A, A`, a field `Id F` is directly
recursive and `F` is not one of its indices (R-NoFunRec-1-0, item 4).
On a field whose head is the family the two readings agree. The
telescope's length must be the shape's `inner`. -/

def funIHType (E : ResolvedEnv) (fuel nparams : Nat) (A M : Expr Nat) (inner : Nat) :
    Option (Expr Nat) :=
  match piTelescopeFuel E fuel (lift 0 1 A) with
  | none => none
  | some (doms, famApp) =>
      if doms.length = inner then
        let idx := familyIdx nparams famApp
        let fApp := foldApps (.bvar inner)
          ((List.range inner).reverse.map fun i => (Expr.bvar i : Expr Nat))
        let motive := lift 0 inner (lift 0 1 M)
        some (policyPi doms (foldApps motive (idx ++ [fApp])))
      else none

def minorFromTelescope (E : ResolvedEnv) (fuel nparams : Nat) (M ctorAcc : Expr Nat) :
    List FieldShape → Expr Nat → Option (Expr Nat)
  | [], T => some (.app (foldApps M (familyIdx nparams T)) ctorAcc)
  | .nonrecursive :: ss, .pi A B =>
      (minorFromTelescope E fuel nparams (lift 0 1 M)
        (.app (lift 0 1 ctorAcc) (.bvar 0)) ss B).map
        fun rest => .pi A rest
  | .recursive inner :: ss, .pi A B =>
      match funIHType E fuel nparams A M inner with
      | none => none
      | some ih =>
          (minorFromTelescope E fuel nparams (lift 0 2 M)
            (.app (lift 0 2 ctorAcc) (.bvar 1)) ss (lift 0 1 B)).map
            fun rest => .pi A (.pi ih rest)
  | _, _ => none

def ctorFieldTelescope {E : ResolvedEnv} {family : PolicyFamilyView E}
    {member : CheckedMember} (c : PolicyConstructorView E family member) : Expr Nat :=
  policyPi c.fields
    (foldApps (.const family.ref (policyFamilyLevels family))
      (policyParameterLocals c.parameters.length c.fields.length ++ c.resultIndices))

/-- Minor `i` in the context under parameters, the motive, and minors
`0 .. i-1`. Motive is `.bvar i`. The constructor head is
`family.ref + 1 + i` (05 §3 / `constructorsPresent`). Recursive fields
are read at the bound `fuel`. -/
def derivedMinor {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    (fuel : Nat) (shapes : List FieldShape) : Option (Expr Nat) :=
  let c := a.constructorViews i
  let shift := 1 + i.val
  let M := Expr.bvar i.val
  let ctorAcc := foldApps
    (.const (a.family.ref + 1 + i.val) (policyFamilyLevels a.family))
    (policyParameterLocals a.family.parameters.length shift)
  minorFromTelescope E fuel a.family.parameters.length M ctorAcc shapes
    (lift 0 shift (ctorFieldTelescope c))

def MinorPremisesMatch {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : Prop :=
  ∀ i : Fin a.constructors.length,
    ∃ shapes fuel,
      fieldShapesFuel E fuel a.family.ref a.family.member.arity
        a.family.parameters.length a.family.indices.length
        a.family.parameters.length (a.constructorViews i).fields = some shapes ∧
      derivedMinor a i fuel shapes = a.minorTypes[i.val]?

/-! ## 05 §14

The descriptor payload that is not already the member types is the
list of field shapes. The right-hand side applies the minor to the
fields and inserts a recursive call after each recursive field.
`inner = 0` reuses `recCallField`. A positive inner telescope is the
λ-wrapper 05 §14 writes for a function-recursive call. As in §12, the
call reads the field's telescope and indices as the analysis does
(`piTelescopeFuel`), not off the stored type's spine.

The equation is typed in the recursor telescope with the major
replaced by the constructor's field binders. The environment of that
typing is the prefix extended by a signature-only copy of the
recursor (05 §4 derivation scope). The recursor constant carries the
recursor's own level vector: family levels, plus the fresh motive
parameter when the policy is AnySort. `RecursorGroupIdxAdmitted` does
not discharge this obligation. -/

/-- The type of the equation: the motive at the constructor's RESULT INDICES `res` (in the
constructor's context, the parameters then the fields) and at the constructor application. `res` is
moved into the equation's context past the motive, the minors and the index binders. Before M3-e-5
the motive was applied to the index binders themselves, which are free in that context. That states
the reduct, of type `motive res (ctor …)`, at `motive i (ctor …)` with `i` unrelated to `res`. Untyped
conversion is total (R-ConvCollapse), so `main` accepted it. On a typed root the reduct has the
corrected type with no conversion step (`vecConsIotaTyT`); the old statement would also need the motive
at the free `i` convertible to the motive at `res`. Without indices both forms are the same term. -/
def iotaLhsType (ctorRef : Nat) (levels : List Level)
    (nparams nMinors nindices nfields : Nat) (res : List (Expr Nat)) : Expr Nat :=
  let motive := Expr.bvar (nfields + nindices + nMinors)
  let idx := res.map (lift nfields (1 + nMinors + nindices))
  let params := policyParameterLocals nparams (nfields + nindices + nMinors + 1)
  let ctorApp := foldApps (.const ctorRef levels) (params ++ fieldBvars nfields)
  foldApps motive (idx ++ [ctorApp])

def liftFields (extra : Nat) : List (Expr Nat) → Nat → List (Expr Nat)
  | [], _ => []
  | A :: As, j => lift j extra A :: liftFields extra As (j + 1)

def equationDoms {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length) :
    Option (List (Expr Nat)) :=
  match peelPis (piCount m.mtype) m.mtype with
  | some (doms, _) =>
      let extra := 1 + a.constructors.length + a.family.indices.length
      some (doms.dropLast ++
        liftFields extra (a.constructorViews i).fields 0)
  | none => none

def assumptionCtx (domsOuterFirst : List (Expr Nat)) : LCtx :=
  domsOuterFirst.reverse.map LocalDecl.assumption

/-- Level vector of the derived recursor. PropOnly reuses the family
arity, so this is the family vector. AnySort adds the motive
parameter at index `baseArity` (05 §3, §11). -/
def policyRecursorLevels (baseArity : Nat) (policy : EliminationPolicy) : List Level :=
  (List.range (policyRecursorArity baseArity policy)).map Level.param

def iotaSchemaAt {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    (fuel : Nat) (shapes : List FieldShape) : Option (Expr Nat) :=
  let c := a.constructorViews i
  let nf := c.fields.length
  let np := a.family.parameters.length
  let q := a.family.indices.length
  let k := a.constructors.length
  iotaOpenRhs E fuel
      (.const r (policyRecursorLevels a.family.member.arity a.policy))
      (.bvar (nf + q + (k - 1 - i.val)))
    (preMajorBvars np k q nf) np k shapes (fieldBvars nf)
    (lift 0 (nf + 1 + k + q) (ctorFieldTelescope c))

/-- The equation's type at constructor `i`: `iotaLhsType` at the views' data. -/
def iotaEquationType {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length) : Expr Nat :=
  iotaLhsType (a.family.ref + 1 + i.val) (policyFamilyLevels a.family)
    a.family.parameters.length a.constructors.length
    a.family.indices.length (a.constructorViews i).fields.length
    (a.constructorViews i).resultIndices

def IotaEquationTyped {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    (fuel : Nat) (shapes : List FieldShape) : Type :=
  match equationDoms a i, iotaSchemaAt a i fuel shapes with
  | some doms, some rhs =>
      HasTy (extendEnv E r m) m.arity (assumptionCtx doms) rhs (iotaEquationType a i)
  | _, _ => Empty

structure IotaDescriptorClause (E : ResolvedEnv) {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) : Type where
  /-- Derivation scope adds the recursor as a signature, not a δ body. -/
  signatureOnly : m.body = none
  shapesAt : Fin a.constructors.length → List FieldShape
  /-- The bound at which the analysis classifies the fields, and at which the schema reads them. -/
  fuelAt : Fin a.constructors.length → Nat
  analyzed : ∀ i,
    fieldShapesFuel E (fuelAt i) a.family.ref a.family.member.arity
      a.family.parameters.length a.family.indices.length
      a.family.parameters.length (a.constructorViews i).fields = some (shapesAt i)
  typed : ∀ i, IotaEquationTyped a i (fuelAt i) (shapesAt i)


/-- There is no previously admitted recursor for `f`. Reference order
is irrelevant: this scans every member already present in the prefix. -/
def NoRecursorFor (E : ResolvedEnv) (f : Nat) : Prop :=
  ∀ rr rm, E.members rr = some rm → rm.mclass = .recursorM →
    memberFamRef rm ≠ some f

/-- Constructor admission is refused after any recursor for its family.
A missing declared family is refused rather than vacuously accepted. -/
def CtorBeforeRecursors (E : ResolvedEnv) (m : CheckedMember) : Prop :=
  ∃ f, memberFamRef m = some f ∧ NoRecursorFor E f

/-- Both directions matter: no holes inside the complete group, and no
constructor for this family at an arbitrary reference outside it. -/
def CtorCensus (E : ResolvedEnv) (f r : Nat) : Prop :=
  f + 1 ≤ r ∧
  ∀ c, (∃ cm, E.members c = some cm ∧ cm.mclass = .constructorM ∧
      memberFamRef cm = some f) ↔ f < c ∧ c < r



/-! ## Group member

`RecursorEliminationAdmitted` already stores 05 §6 (`constructorViews`),
05 §10 (`selected`), 05 §11 (`recursorArity`, motive inside
`policyRecursorType`), and the 05 §13 skeleton (`recursorType`).
Those fields are the clauses; this inductive does not restate them. -/

inductive IndGroupAdmitted (E : ResolvedEnv) (r : Nat) (m : CheckedMember) : Type
  | family
      (hfresh : E.members r = none)
      (view : PolicyFamilyView (extendEnv E r m))
      (href : view.ref = r)
      (hm : view.member = m)
      (hProfile : UniformProp view.resultLevel ∨ UniformType view.resultLevel)
  | constructor
      (family : PolicyFamilyView E)
      (view : PolicyConstructorView E family m)
      (hfresh : E.members r = none)
      (h04 : CtorBeforeRecursors E m)
      (hContig : CtorContiguous E r m)
      (h07 : FieldUniverseAdmitted view)
      (h08 : CtorFieldsPermitted view)
  | recursor
      (a : RecursorEliminationAdmitted E r m)
      (hfresh : E.members r = none)
      (h04 : CtorCensus E a.family.ref r)
      (h07 : ∀ i, FieldUniverseAdmitted (a.constructorViews i))
      (h08 : ∀ i, CtorFieldsPermitted (a.constructorViews i))
      (h12 : MinorPremisesMatch a)
      (h14 : IotaDescriptorClause E a)

theorem uniformType_succ_zero : UniformType (.succ .zero) := by
  intro _
  exact Nat.succ_pos 0

theorem leN_refl (l : Level) : leN l l := by
  intro _ x y hx hy
  have hxy : x = y := Option.some.inj (hx.symm.trans hy)
  subst hxy
  exact Nat.le_refl x

end Rcic.Declarative
