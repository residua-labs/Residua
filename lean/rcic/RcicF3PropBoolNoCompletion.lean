import rcic.RcicF3PropIndexConversionGeneric
import rcic.RcicF3Layout
import rcic.RcicAnnEnvBridgeGroup

/-!
# The Bool conversion gadget has no admitted common completion

Every recursor installed by `EnvWfT` has an actual earlier admission
environment whose members remain in the final environment. This is
extracted by recursion on the admission derivation, without a scope,
normalization, semantic, boundedness, or consistency premise.

The gadget's recursor declares family 3. Preservation pins that family's
member to the gadget's literal `Sort 0` declaration. Its zero recursor
arity forces `propOnly`; its stored motive instead ends in `Sort 1`.
Consequently no `EnvWfT` environment contains even the gadget's family
and recursor together, and no arbitrary signature containing the gadget
has an admitted common completion. This blocks this specific attack from
the fixed-admitted-completion domain; it is not a semantic iota producer.

No `Premises4` instance is required by this syntactic exclusion, so it
holds in particular relative to every same `Premises4`. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.AdmittedCompletion
open Rcic.Declarative Rcic.Model.PS
open Rcic.Declarative.Ann (EnvSub)

/-- A recursor's admission prefix remains included in the final
environment; the admission record itself is actual constructor data. -/
def RecursorOrigins (F : ResolvedEnv) : Prop :=
  ∀ r m, F.members r = some m → m.mclass = .recursorM →
    ∃ E0 : ResolvedEnv, EnvSub E0 F ∧
      Nonempty (RecursorEliminationAdmitted E0 r m)

theorem recursorAdmission_of_indGroup {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (h : IndGroupAdmitted E r m)
    (hk : m.mclass = .recursorM) :
    Nonempty (RecursorEliminationAdmitted E r m) := by
  cases h with
  | family _ view _ hm _ =>
      have hc : m.mclass = .inductiveM := hm ▸ view.hasClass
      rw [hk] at hc
      cases hc
  | constructor _ view _ _ _ _ _ =>
      have hc := view.hasClass
      rw [hk] at hc
      cases hc
  | recursor a _ _ _ _ _ _ => exact ⟨a⟩

theorem recursorOrigins_extend {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (hfresh : E.members r = none)
    (hOld : RecursorOrigins E)
    (hNew : m.mclass = .recursorM →
      Nonempty (RecursorEliminationAdmitted E r m)) :
    RecursorOrigins (extendEnv E r m) := by
  intro q n hq hn
  by_cases hqr : q = r
  · subst q
    rw [members_extend_eq] at hq
    cases hq
    exact ⟨E, members_extend_preserved hfresh, hNew hn⟩
  · rw [members_extend_ne E r m q hqr] at hq
    obtain ⟨E0, hsub, ha⟩ := hOld q n hq hn
    exact ⟨E0, fun s t ht =>
      members_extend_preserved hfresh s t (hsub s t ht), ha⟩

theorem recursorOrigins_group {S : ResolvedEnv} :
    {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → RecursorOrigins E → RecursorOrigins E'
  | _, _, _, .nil _, h => h
  | _, _, _, .cons _E _r _m _rest _E' hfresh _hnobody _hclT _harity _hlvlB
      _hcanon _harities hadm _hidxAdmT _u _hT _hTc _htyped hrest, h =>
      recursorOrigins_group hrest
        (recursorOrigins_extend hfresh h (recursorAdmission_of_indGroup hadm))

/-- Admission origin extraction for every `EnvWfT`, including axiom
extensions. No class restriction or semantic soundness theorem is used. -/
theorem recursorOrigins_of_envWfT :
    {F : ResolvedEnv} → EnvWfT F → RecursorOrigins F
  | _, .empty => fun _ _ hm _ => by cases hm
  | _, .axiom E r A u hE hfresh hA hcl hlvl =>
      recursorOrigins_extend hfresh (recursorOrigins_of_envWfT hE)
        (fun hk => by cases hk)
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      recursorOrigins_extend hfresh (recursorOrigins_of_envWfT hE)
        (fun hk => by cases hk)
  | _, .thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp =>
      recursorOrigins_extend hfresh (recursorOrigins_of_envWfT hE)
        (fun hk => by cases hk)
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      recursorOrigins_extend hfresh (recursorOrigins_of_envWfT hE)
        (fun hk => by cases hk)
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem =>
      recursorOrigins_group hmem (recursorOrigins_of_envWfT hE)

/-- A literal sort declaration has no parameter or index telescope. -/
theorem family_sort_zero_info {E : ResolvedEnv} (fam : PolicyFamilyView E)
    (hm : fam.member.mtype = .sort .zero) :
    fam.parameters = [] ∧ fam.indices = [] ∧ fam.resultLevel = .zero := by
  have ht := fam.storedType
  rw [hm] at ht
  cases hpar : fam.parameters with
  | cons A As =>
      simp only [hpar, List.cons_append, policyPi] at ht
      cases ht
  | nil =>
      cases hind : fam.indices with
      | cons A As =>
          simp only [hpar, List.nil_append, hind, policyPi] at ht
          cases ht
      | nil =>
          refine ⟨rfl, rfl, ?_⟩
          simp only [hpar, hind, List.nil_append, policyPi] at ht
          exact (Expr.sort.inj ht).symm

/-- The gadget's family and recursor cannot occur in any admitted
environment. The two constructor lookups are not needed for this stronger
signature obstruction: the literal monomorphic large motive already
contradicts the existing admission arity and stored-type equations. -/
theorem no_bool_rec_pair {F : ResolvedEnv} (hF : EnvWfT F)
    (hBool : F.members 3 = some PropIndexConversionAttack.boolMember)
    (hRec : F.members 6 = some PropIndexConversionAttack.recMember) : False := by
  obtain ⟨E0, hsub, ⟨a⟩⟩ :=
    recursorOrigins_of_envWfT hF 6 PropIndexConversionAttack.recMember hRec rfl
  have href : a.family.ref = 3 := by
    have h := memberFamRef_recAdm a rfl
    change (some 3 : Option Nat) = some a.family.ref at h
    exact (Option.some.inj h).symm
  have hfm : a.family.member = PropIndexConversionAttack.boolMember := by
    have hp := hsub _ _ a.family.present
    rw [href] at hp
    exact Option.some.inj (hp.symm.trans hBool)
  have hshape := family_sort_zero_info a.family (by rw [hfm]; rfl)
  have hpolicy : a.policy = .propOnly := by
    cases hp : a.policy with
    | propOnly => rfl
    | anySort =>
        have ha := a.recursorArity
        rw [hp] at ha
        change 0 = a.family.member.arity + 1 at ha
        omega
  have hmotive : Expr.pi (.const 3 []) (.sort (.succ .zero)) =
      policyMotiveType a.family .propOnly := by
    have ht := a.recursorType
    rw [hpolicy] at ht
    unfold policyRecursorType at ht
    rw [hshape.1] at ht
    exact (Expr.pi.inj ht).1
  have hsort : (Expr.sort (.succ .zero) : Expr Nat) = .sort .zero := by
    unfold policyMotiveType at hmotive
    rw [hshape.2.1] at hmotive
    exact (Expr.pi.inj hmotive).2
  cases hsort

theorem no_admitted_lookups {F : ResolvedEnv} (hF : EnvWfT F)
    (L : PropIndexConversionGeneric.Lookups F) : False :=
  no_bool_rec_pair hF L.bool_lookup L.rec_lookup

/-- Any containing signature for the attack gadget has no admitted
completion. In particular this excludes a completion shared with an
independently admitted target group, without assuming target soundness. -/
theorem no_admitted_completion {S F : ResolvedEnv}
    (L : PropIndexConversionGeneric.Lookups S)
    (hF : EnvWfT F) (hsub : EnvSub S F) : False :=
  no_bool_rec_pair hF
    (hsub 3 _ L.bool_lookup) (hsub 6 _ L.rec_lookup)

theorem no_propIndexExtension_completion {F : ResolvedEnv}
    (hF : EnvWfT F)
    (hsub : EnvSub PropIndexConversionAttack.extension F) : False :=
  no_admitted_completion (⟨rfl, rfl, rfl, rfl⟩ :
    PropIndexConversionGeneric.Lookups PropIndexConversionAttack.extension) hF hsub

end Rcic.F3.PSet.AdmittedCompletion

#print axioms Rcic.F3.PSet.AdmittedCompletion.recursorOrigins_of_envWfT
#print axioms Rcic.F3.PSet.AdmittedCompletion.no_bool_rec_pair
#print axioms Rcic.F3.PSet.AdmittedCompletion.no_admitted_completion
#print axioms Rcic.F3.PSet.AdmittedCompletion.no_propIndexExtension_completion
