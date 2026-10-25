import rcic.RcicF3EnvModel

/-!
# F3: consistency over constructor-free, axiom-free admitted environments

The class `CtorFreeAxFree`: no axiom and no constructor member. It contains
every environment built from definitions, theorems and opaque members over
constructor-free inductive groups (such as `False`, or empty families with
parameters and indices), with arbitrary typed bodies (Π, λ, universes,
impredicative `Prop`).

- `EnvBound K hW`: the stored derivation of every body stays below level 4
  with instance bound `K` (the same bound the main derivation uses);
- `envSound_ctorFree`: a faithful table of such an environment satisfies
  `EnvSound` at every level valuation;
- `consistent4_ctorFree`: there is no closed proof of `False` (reference 0)
  in such an environment by a derivation below level 4.

Residual assumptions: `P : Premises4` (decidability + choice at Lean
universes 0 … 3); relative consistency in Lean with universes 0 … 4.
closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (groupMembersT_preserve)

namespace PSet

/-- No axiom and no constructor member. -/
def CtorFreeAxFree (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → m.mclass ≠ .constructorM ∧ m.mclass ≠ .axiomM

/-- The stored body derivations stay below level 4 with instance bound `K`. -/
def EnvBound (K : Nat → Nat) : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ hE _ _ _ _ => EnvBound K hE
  | _, .definition _ _ _ _ _ hE _ _ hv _ _ _ _ => EnvBound K hE ∧ LOKt (fun _ => 0) 4 K hv
  | _, .thm _ _ _ _ hE _ _ hp _ _ _ _ => EnvBound K hE ∧ LOKt (fun _ => 0) 4 K hp
  | _, .opaque _ _ _ _ _ hE _ _ hv _ _ _ _ => EnvBound K hE ∧ LOKt (fun _ => 0) 4 K hv
  | _, .group _ _ _ _ _ _ _ hE _ _ _ _ => EnvBound K hE

/-- What one member owes, at every level valuation. -/
def MemberSound (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (r : Nat)
    (m : CheckedMember) : Prop :=
  ∀ (σ : Nat → Nat) (ls : List Level) (ρ : Nat → PSet.{4}), ls.length = m.arity →
    LevelsOK σ (K r) ls →
    μ r (ls.map (evalTotal σ)) ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ (instantiateLevels ls m.mtype)) ∧
      ∀ b, m.body = some b →
        Equiv (μ r (ls.map (evalTotal σ))) (den (mkM P μ) σ ρ (instantiateLevels ls b))

/-- Every member owes its part. -/
def AllSound (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → MemberSound P μ K r m

theorem envSound_of_allSound (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat}
    {E : ResolvedEnv} (hA : AllSound P μ K E) (hC : CtorFreeAxFree E) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P μ) σ K E n where
  const := fun _ r ls m ρ hres hlen hl _ => (hA r m hres σ ls ρ hlen hl).1
  delta := fun _ r ls m b ρ hres hbody _ hlen hl _ => (hA r m hres σ ls ρ hlen hl).2 b hbody
  iota := by
    intro _ _ _ _ _ hι _ _ _ _ _ _ _ _
    cases hι with
    | of w => exact ((hC _ _ w.hctor).1 w.hctorK).elim

/-- The level valuation of an instance vector agrees with the instantiation's. -/
theorem σOf_agree (σ : Nat → Nat) (ls : List Level) :
    ∀ i, i < ls.length → σOf (ls.map (evalTotal σ)) i =
      ((ls.map (evalTotal σ))[i]?).getD (σ i) := by
  intro i hi
  have hi' : i < (ls.map (evalTotal σ)).length := by simpa using hi
  simp only [σOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]

/-- Transport of a statement about a closed, level-bounded type from the
canonical reading to any reading. -/
theorem den_inst_canon (M : Interp.{4}) (σ : Nat → Nat) (ls : List Level) (ρ : Nat → PSet.{4})
    (e : Expr Nat) (hcl : ∀ k, Rcic.Declarative.lift k 1 e = e)
    (hb : exprLevelsBounded ls.length e = true) :
    den M σ ρ (instantiateLevels ls e) = den M (σOf (ls.map (evalTotal σ))) ρ0 e := by
  rw [den_instantiateLevels, den_closed M _ e hcl ρ ρ0]
  exact (den_levels_agree M (k := ls.length) (fun i hi => (σOf_agree σ ls i hi).symm) e hb ρ0)

theorem tyv_pempty_mem_U4 (P : Premises4) : ∀ k, tyv pempty ∈ U W4 k
  | 0 => (mem_sImage_tyv).mpr ⟨pempty, mem_propSets.mpr fun _ h => (not_mem_pempty h).elim, Equiv.rfl⟩
  | k + 1 => by
      have hS : Stage (W4 (k + 1)) := by
        rcases k with _ | _ | _ | k
        · exact stage_univIn.{0, 4} P.c0
        · exact stage_univIn.{1, 4} P.c1
        · exact stage_univIn.{2, 4} P.c2
        · exact stage_univIn.{3, 4} P.c3
      obtain ⟨i, hi⟩ := hS.empty
      exact (mem_sImage_tyv).mpr ⟨pempty,
        mem_sep.mpr ⟨i, (dich_congr hi.symm).mp (Or.inl fun _ h => (not_mem_pempty h).elim), hi⟩, Equiv.rfl⟩

theorem U4_dich (k : Nat) : Dich (U W4 k) := Or.inr fun h => by
  have h' : pempty ∈ sImage tyv (match k with
      | 0 => propSets
      | k + 1 => sep Dich (W4 (k + 1))) := by
    cases k <;> exact h
  obtain ⟨S, _, he⟩ := mem_sImage_tyv.mp h'
  exact tyv_ne_pempty S he.symm

/-- The empty type value is an element of every sort. -/
theorem tyv_pempty_mem_sort (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (ρ : Nat → PSet.{4}) (l : Level) : tyv pempty ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ (.sort l)) :=
  mem_congr_right (ed_tyv (mkM P μ) (U4_dich _)).symm (tyv_pempty_mem_U4 P _)

theorem allSound_prefix {P : Premises4} {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat}
    {E E' : ResolvedEnv} (hsub : ∀ r m, E.members r = some m → E'.members r = some m)
    (h : AllSound P μ K E') : AllSound P μ K E :=
  fun r m hm => h r m (hsub r m hm)

theorem faithful_prefix {P : Premises4} {μ : Nat → List Nat → PSet.{4}} {E E' : ResolvedEnv}
    (hsub : ∀ r m, E.members r = some m → E'.members r = some m) (h : Faithful P μ E') :
    Faithful P μ E :=
  fun r m hm => h r m (hsub r m hm)

theorem class_prefix {E E' : ResolvedEnv}
    (hsub : ∀ r m, E.members r = some m → E'.members r = some m) (h : CtorFreeAxFree E') :
    CtorFreeAxFree E :=
  fun r m hm => h r m (hsub r m hm)

/-- A member whose value is a telescope abstraction owes only the end-value
obligation. -/
theorem memberSound_piLam {P : Premises4} {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat}
    {r : Nat} {m : CheckedMember} (hcl : ∀ k, Rcic.Declarative.lift k 1 m.mtype = m.mtype)
    (hb : exprLevelsBounded m.arity m.mtype = true) (hbody : m.body = none)
    {g : (Nat → PSet.{4}) → PSet.{4}} (hg : EnvResp g)
    (hval : ∀ vs, μ r vs = piLam (mkM P μ) (σOf vs) g ρ0 m.mtype)
    (hgood : ∀ σ1, PiGood (mkM P μ) σ1 g ρ0 m.mtype) : MemberSound P μ K r m := by
  intro σ ls ρ hlen _
  refine ⟨?_, fun b hb' => by rw [hbody] at hb'; cases hb'⟩
  rw [hval, den_inst_canon (mkM P μ) σ ls ρ m.mtype hcl (hlen ▸ hb)]
  exact piLam_mem _ _ hg _ _ (hgood _)

theorem length_policyArgs (np n q : Nat) :
    (policyParameterLocals np n ++ policyLocals q).length = np + q := by
  simp [policyParameterLocals, policyLocals]

/-- In a constructor-free environment every family application is empty. -/
theorem ed_den_famApp_empty {P : Premises4} {μ : Nat → List Nat → PSet.{4}} {E : ResolvedEnv}
    (hF : Faithful P μ E) (fam : PolicyFamilyView E) (σ1 : Nat → Nat) (ρ : Nat → PSet.{4})
    (n q : Nat) (hq : q = fam.indices.length) :
    Equiv (Ed (mkM P μ) (den (mkM P μ) σ1 ρ (foldApps (.const fam.ref (policyFamilyLevels fam))
      (policyParameterLocals fam.parameters.length n ++ policyLocals q)))) pempty := by
  rw [den_foldApps]
  show Equiv (Ed (mkM P μ) (fapps (μ fam.ref _) _)) pempty
  rw [hF fam.ref fam.member fam.present]
  have hcls : fam.member.mclass = .inductiveM := fam.hasClass
  unfold memberVal
  rw [hcls]
  show Equiv (Ed (mkM P μ) (fapps (piLam (mkM P μ) _ (fun _ => tyv pempty) ρ0 fam.member.mtype) _)) pempty
  rw [fam.storedType]
  refine ed_fapps_emptyFam (mkM P μ) _ _ ρ0 _ ?_
  rw [List.length_map, length_policyArgs, piArity_policyPi, List.length_append, hq]
  rfl

/-- No constructor in the environment: the recursor has no minor premise. -/
theorem constructors_nil_of_class {E E' : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m)
    (hsub : ∀ r m, E.members r = some m → E'.members r = some m) (hC : CtorFreeAxFree E') :
    a.constructors.length = 0 := by
  cases h : a.constructors.length with
  | zero => rfl
  | succ k =>
      have hi : 0 < a.constructors.length := by omega
      have hp := a.constructorsPresent ⟨0, hi⟩
      have hk := (a.constructorViews ⟨0, hi⟩).hasClass
      exact ((hC _ _ (hsub _ _ hp)).1 hk).elim

/-- The recursor of a constructor-free family: every end value is fine, the
major premise's domain is empty. -/
theorem piGood_ctorFree_recursor {P : Premises4} {μ : Nat → List Nat → PSet.{4}} {E : ResolvedEnv}
    (hF : Faithful P μ E) (fam : PolicyFamilyView E) (policy : EliminationPolicy)
    (σ1 : Nat → Nat) (g : (Nat → PSet.{4}) → PSet.{4}) (ρ : Nat → PSet.{4}) :
    PiGood (mkM P μ) σ1 g ρ (policyRecursorType fam [] policy) := by
  unfold policyRecursorType
  dsimp only
  apply piGood_policyPi
  intro ρ1 x _
  show PiGood _ _ _ _ (policyPi (List.mapIdx _ fam.indices) _)
  apply piGood_policyPi
  intro ρ2 y hy
  have he := ed_den_famApp_empty hF fam σ1 ρ2 (([] : List (Expr Nat)).length + 1 + fam.indices.length)
    fam.indices.length rfl
  exact (not_mem_pempty (mem_congr_right he hy)).elim

/-- The group walk owes nothing beyond the family and recursor obligations. -/
theorem allSound_groupμ (P : Premises4) (K : Nat → Nat) {μ : Nat → List Nat → PSet.{4}}
    {E' : ResolvedEnv} (hF : Faithful P μ E') (hC : CtorFreeAxFree E') {S : ResolvedEnv} :
    {E : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → (hmem : GroupMembersT S E ms E') →
    (∀ p, p ∈ ms → p.2.mclass = .inductiveM ∨ p.2.mclass = .constructorM ∨ p.2.mclass = .recursorM) →
    AllSound P μ K E → AllSound P μ K E'
  | _, _, .nil _, _, hA => hA
  | E, _, .cons _ r m rest _ hfresh hnobody hclT _ hlvlB _ _ hadm _ _ _ _ _ hrest, hcls, hA => by
      have hsubR := groupMembersT_preserve hrest
      have hsub : ∀ r' m', E.members r' = some m' → E'.members r' = some m' :=
        fun r' m' h => hsubR r' m' (members_extend_preserved hfresh r' m' h)
      have hmE' : E'.members r = some m := hsubR r m (members_extend_eq E r m)
      have hnew : MemberSound P μ K r m := by
        cases hadm with
        | family _ view _ hm _ =>
            have hcl : m.mclass = .inductiveM := by
              have h := view.hasClass; rw [hm] at h; exact h
            refine memberSound_piLam hclT hlvlB hnobody (envResp_const (tyv pempty)) ?_ ?_
            · intro vs; refine (hF r m hmE' vs).trans ?_; unfold memberVal; rw [hcl]
            · intro σ1
              have hst : m.mtype = policyPi (view.parameters ++ view.indices) (.sort view.resultLevel) := by
                have h := view.storedType; rw [hm] at h; exact h
              rw [hst]
              apply piGood_policyPi
              intro ρ
              exact tyv_pempty_mem_sort P μ σ1 ρ _
        | constructor _ view _ _ _ _ _ => exact ((hC r m hmE').1 view.hasClass).elim
        | recursor a _ _ _ _ _ _ =>
            have hk := constructors_nil_of_class a hsub hC
            have hmin : a.minorTypes = [] := List.eq_nil_of_length_eq_zero (a.minorCount.trans hk)
            have hty : m.mtype = policyRecursorType a.family [] a.policy := hmin ▸ a.recursorType
            have hfamF : Faithful P μ E := faithful_prefix hsub hF
            rcases hcls (r, m) (List.mem_cons_self _ _) with hc | hc | hc
            · refine memberSound_piLam hclT hlvlB hnobody (envResp_const (tyv pempty)) ?_ ?_
              · intro vs; refine (hF r m hmE' vs).trans ?_; unfold memberVal; rw [hc]
              · intro σ1; rw [hty]; exact piGood_ctorFree_recursor hfamF a.family a.policy σ1 _ ρ0
            · exact ((hC r m hmE').1 hc).elim
            · refine memberSound_piLam hclT hlvlB hnobody (envResp_const pempty) ?_ ?_
              · intro vs; refine (hF r m hmE' vs).trans ?_; unfold memberVal; rw [hc]
              · intro σ1; rw [hty]; exact piGood_ctorFree_recursor hfamF a.family a.policy σ1 _ ρ0
      have hA' : AllSound P μ K (extendEnv E r m) := by
        intro r' m' h
        by_cases hr : r' = r
        · subst hr; rw [members_extend_eq] at h; cases h; exact hnew
        · rw [members_extend_ne E r m r' hr] at h; exact hA r' m' h
      exact allSound_groupμ P K hF hC hrest (fun p hp => hcls p (List.mem_cons_of_mem _ hp)) hA'

/-- A singleton member with a closed, level-free body that is sound in the
prefix. -/
theorem memberSound_singleton {P : Premises4} {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat}
    {E : ResolvedEnv} {r : Nat} {k : MemberClass} {A v : Expr Nat}
    (hval : μ r [] = den (mkM P μ) (fun _ => 0) ρ0 v)
    (hclA : ∀ j, Rcic.Declarative.lift j 1 A = A) (hclv : ∀ j, Rcic.Declarative.lift j 1 v = v)
    (hlvlA : exprLevelsBounded 0 A = true) (hlvlv : exprLevelsBounded 0 v = true)
    (hv : HasTyT E 0 [] v A) (hl : LOKt (fun _ => 0) 4 K hv) (hA : AllSound P μ K E)
    (hC : CtorFreeAxFree E) : MemberSound P μ K r ⟨k, 0, A, some v⟩ := by
  intro σ ls ρ hlen _
  have hls : ls = [] := List.eq_nil_of_length_eq_zero hlen
  subst hls
  have hσ : σOf (([] : List Level).map (evalTotal σ)) = fun _ => 0 := rfl
  have hS := sound_ty (P.good (mkM P μ) rfl) (envSound_of_allSound P hA hC (fun _ => 0) 0) hv hl ρ0 trivial
  show μ r [] ∈ _ ∧ _
  refine ⟨?_, fun b hb => ?_⟩
  · rw [den_inst_canon (mkM P μ) σ [] ρ A hclA hlvlA, hσ, hval]
    exact hS
  · cases hb
    show Equiv (μ r []) _
    rw [den_inst_canon (mkM P μ) σ [] ρ v hclv hlvlv, hσ, hval]
    exact Equiv.rfl

theorem mem_memberVal_def {P : Premises4} {μ : Nat → List Nat → PSet.{4}} {k : MemberClass}
    (hk : k = .definitionM ∨ k = .theoremM ∨ k = .opaqueM) (A v : Expr Nat) (vs : List Nat) :
    memberVal P μ ⟨k, 0, A, some v⟩ vs = den (mkM P μ) (fun _ => 0) ρ0 v := by
  rcases hk with h | h | h <;> subst h <;> rfl

/-- Every member of a constructor-free, axiom-free admitted environment owes
its part, at any faithful table. -/
theorem allSound_ctorFree (P : Premises4) (K : Nat → Nat) : {E : ResolvedEnv} → (hW : EnvWfT E) →
    CtorFreeAxFree E → EnvBound K hW → ∀ μ, Faithful P μ E → AllSound P μ K E
  | _, .empty, _, _, _, _ => fun _ _ h => (Option.noConfusion h)
  | _, .axiom E r A u hE hfresh _ _ _, hC, _, _, _ => by
      exact ((hC r _ (members_extend_eq E r _)).2 rfl).elim
  | _, .definition E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, hC, hB, μ, hF => by
      have hsub := members_extend_preserved (m := ⟨.definitionM, 0, A, some v⟩) hfresh
      have hCE := class_prefix hsub hC
      have hAE := allSound_ctorFree P K hE hCE hB.1 μ (faithful_prefix hsub hF)
      intro r' m' h
      by_cases hr : r' = r
      · subst hr; rw [members_extend_eq] at h; cases h
        exact memberSound_singleton ((hF _ _ (members_extend_eq E r' _) []).trans
          (mem_memberVal_def (Or.inl rfl) A v [])) hclA hclv hlvlA hlvlv hv hB.2 hAE hCE
      · rw [members_extend_ne E r _ r' hr] at h; exact hAE r' m' h
  | _, .thm E r A p hE hfresh hA hp hclA hclp hlvlA hlvlp, hC, hB, μ, hF => by
      have hsub := members_extend_preserved (m := ⟨.theoremM, 0, A, some p⟩) hfresh
      have hCE := class_prefix hsub hC
      have hAE := allSound_ctorFree P K hE hCE hB.1 μ (faithful_prefix hsub hF)
      intro r' m' h
      by_cases hr : r' = r
      · subst hr; rw [members_extend_eq] at h; cases h
        exact memberSound_singleton ((hF _ _ (members_extend_eq E r' _) []).trans
          (mem_memberVal_def (Or.inr (Or.inl rfl)) A p [])) hclA hclp hlvlA hlvlp hp hB.2 hAE hCE
      · rw [members_extend_ne E r _ r' hr] at h; exact hAE r' m' h
  | _, .opaque E r A v u hE hfresh hA hv hclA hclv hlvlA hlvlv, hC, hB, μ, hF => by
      have hsub := members_extend_preserved (m := ⟨.opaqueM, 0, A, some v⟩) hfresh
      have hCE := class_prefix hsub hC
      have hAE := allSound_ctorFree P K hE hCE hB.1 μ (faithful_prefix hsub hF)
      intro r' m' h
      by_cases hr : r' = r
      · subst hr; rw [members_extend_eq] at h; cases h
        exact memberSound_singleton ((hF _ _ (members_extend_eq E r' _) []).trans
          (mem_memberVal_def (Or.inr (Or.inr rfl)) A v [])) hclA hclv hlvlA hlvlv hv hB.2 hAE hCE
      · rw [members_extend_ne E r _ r' hr] at h; exact hAE r' m' h
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hC, hB, μ, hF => by
      have hsub : ∀ r m, E.members r = some m → E'.members r = some m := fun r m h =>
        groupMembersT_preserve hmem r m h
      have hAE := allSound_ctorFree P K hE (class_prefix hsub hC) hB μ (faithful_prefix hsub hF)
      refine allSound_groupμ P K hF hC hmem ?_ hAE
      intro p hp
      rcases List.mem_cons.mp hp with h | h
      · subst h; exact Or.inl hfam
      · rcases List.mem_append.mp h with h | h
        · exact Or.inr (Or.inl (hctors p h))
        · rw [List.mem_singleton] at h; subst h; exact Or.inr (Or.inr hrec)

/-- **Consistency below level 4 over constructor-free, axiom-free admitted
environments.** No closed term has the type `False` (the family at
reference 0), by any derivation whose sort levels are at most 4 and whose
constant instances respect `K`, in any such environment whose stored body
derivations respect the same bounds. -/
theorem consistent4_ctorFree (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E)
    (hC : CtorFreeAxFree E) (hB : EnvBound K hW) (h0 : E.members 0 = some falseFamMember)
    (n : Nat) (e : Expr Nat) (h : HasTyT E n [] e (.const 0 []))
    (hl : LOKt (fun _ => 0) 4 K h) : False := by
  have hF := (faithful_envμ P hW).1
  have hA := allSound_ctorFree P K hW hC hB _ hF
  have hm := sound_ty (P.good (mkM P (envμ P hW)) rfl)
    (envSound_of_allSound P hA hC (fun _ => 0) n) h hl ρ0 trivial
  have hv : envμ P hW 0 [] = tyv pempty := hF 0 falseFamMember h0 []
  have e1 : Equiv (Ed (mkM P (envμ P hW)) (den (mkM P (envμ P hW)) (fun _ => 0) ρ0 (.const 0 [])))
      pempty := by
    show Equiv (Ed _ (envμ P hW 0 [])) pempty
    rw [hv]; exact ed_tyv_empty _
  exact not_mem_pempty (mem_congr_right e1 hm)

/-- The admitted `False` environment is in the class (sanity: the theorem's
hypotheses are inhabited). -/
theorem falseEnvU_in_class : CtorFreeAxFree falseEnvU ∧ EnvBound (fun _ => 0) falseEnvUWfT :=
  ⟨fun r m h => ⟨(falseEnvU_member_shape h).1, by
      match r, h with
      | 0, h => rw [falseEnvU_m0] at h; cases h; exact fun h => MemberClass.noConfusion h
      | 1, h => rw [falseEnvU_m1] at h; cases h; exact fun h => MemberClass.noConfusion h
      | r + 2, h => rw [falseEnvU_m2] at h; exact Option.noConfusion h⟩, trivial⟩

/-! ### A fixture with a definition: `idFalse : False → False := fun x => x` -/

def idFalseType : Expr Nat := .pi (.const 0 []) (.const 0 [])

def idFalseBody : Expr Nat := .lam (.const 0 []) (.bvar 0)

def idFalseMember : CheckedMember := ⟨.definitionM, 0, idFalseType, some idFalseBody⟩

def idFalseEnv : ResolvedEnv := extendEnv falseEnvU 2 idFalseMember

def falseTy (E : ResolvedEnv) (h : E.members 0 = some falseFamMember) (Γ : LCtx) :
    HasTyT E 0 Γ (.const 0 []) (.sort .zero) :=
  HasTyT.const Γ 0 [] falseFamMember h rfl rfl

def idFalseTypeTy : HasTyT falseEnvU 0 [] idFalseType (.sort (.imax .zero .zero)) :=
  HasTyT.pi [] _ .zero _ .zero (falseTy falseEnvU rfl []) (falseTy falseEnvU rfl _)

def idFalseBodyTy : HasTyT falseEnvU 0 [] idFalseBody idFalseType :=
  HasTyT.lam [] _ .zero (.bvar 0) (.const 0 []) (falseTy falseEnvU rfl [])
    (HasTyT.bvar _ 0 (.const 0 []) rfl)

def idFalseEnvWfT : EnvWfT idFalseEnv :=
  .definition falseEnvU 2 idFalseType idFalseBody (.imax .zero .zero) falseEnvUWfT (falseEnvU_m2 0)
    idFalseTypeTy idFalseBodyTy (fun _ => rfl) (fun _ => rfl) rfl rfl

/-- The fixture is in the class, at every instance bound. -/
theorem idFalseEnv_in_class (K : Nat → Nat) :
    CtorFreeAxFree idFalseEnv ∧ EnvBound K idFalseEnvWfT := by
  refine ⟨fun r m h => ?_, trivial, ⟨fun _ h => (List.not_mem_nil _ h).elim, trivial⟩⟩
  match r, h with
  | 2, h => cases h; exact ⟨fun h => MemberClass.noConfusion h, fun h => MemberClass.noConfusion h⟩
  | 0, h => cases h; exact ⟨fun h => MemberClass.noConfusion h, fun h => MemberClass.noConfusion h⟩
  | 1, h => cases h; exact ⟨fun h => MemberClass.noConfusion h, fun h => MemberClass.noConfusion h⟩
  | r + 3, h =>
      have h' : falseEnvU.members (r + 1 + 2) = some m := h
      rw [falseEnvU_m2] at h'; exact Option.noConfusion h'

/-- No closed proof of `False` in the fixture below level 4. -/
theorem idFalseEnv_consistent4 (P : Premises4) (K : Nat → Nat) (n : Nat) (e : Expr Nat)
    (h : HasTyT idFalseEnv n [] e (.const 0 [])) (hl : LOKt (fun _ => 0) 4 K h) : False :=
  consistent4_ctorFree P K idFalseEnvWfT (idFalseEnv_in_class K).1 (idFalseEnv_in_class K).2 rfl n e h hl

end PSet

end Rcic.F3
