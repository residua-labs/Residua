import rcic.RcicAnnSemTel

/-!
# M2-f (4b) — the families' clause, built at a group's family application

At the group step of the environment induction only the base's clauses are in hand, so the
fundamental theorem holds on the base's derivations (`BaseFundA`, `BaseFundConvA`). The families'
clause reads the group's views: the family's parameters and indices, each constructor's fields,
all typed in the base. This file builds `TyKA.fam` and `EqKA.fam` at an application of the group's
family to related arguments, from those base derivations under the substitutions the walks build.

Heights (M2-f (4b)-0): the clause lives at the height of the family's sort, where the parameters
need not be valid, so the fundamental theorem runs at any height above both the outer one and its
own threshold, and a domain's validity at its own sort's height comes down from there
(`LRRelA_sort_elim'`). Levels (M2-f (3d)): every datum is read at a bounded list `=ₙ` the
carrier's.

A function-recursive field's inner data (`hFldI`, `hFldIeq`, `hFldIRec`, `hXFldI`, `hXRecI`) are built as
the plain and recursive ones one telescope deeper (R-NoFunRec-1 step 1 (1c-δ)). `frecWalkA` reaches the
field: its domain is the field telescope at the inner binders read as plain fields, typed in the plain
context (`FieldsTyA.frec`). The inner walk is the field walk at the relation of the inner domains
(`fieldWalkRelA`), so the inner domains follow as `plainDomA` does (`frecInnerDomA`) and the codomain as
`recDomA` does (`frecInnerRecA`), at the composed world of the clause's world and the extension: the
walk weakens to it (`argsRelA_famRsA_wk`), and the clause's data are read there (`famFldIA`,
`famFldIeqA`, `famFldIRecA`, `famXFldIA`, `famXRecIA`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) levels -/

theorem ht_eq_evalTotal (ρ₀ : Nat → Nat) (l : Level) : ht ρ₀ l = evalTotal ρ₀ l :=
  Option.some.inj ((eval_total ρ₀ l).symm.trans (Rcic.Declarative.eval_total ρ₀ l))

/-- the height is monotone in `≤ₙ`. -/
theorem ht_le_of_leN {ρ₀ : Nat → Nat} {a b : Level} (h : leN a b) : ht ρ₀ a ≤ ht ρ₀ b :=
  h (fun i => some (ρ₀ i)) _ _ (eval_total ρ₀ a) (eval_total ρ₀ b)

theorem leN_instLevel {a b : Level} (h : leN a b) (ls : List Level) :
    leN (instLevel ls a) (instLevel ls b) := by
  intro ρ x y hx hy
  rw [eval_instLevel] at hx hy
  exact h _ x y hx hy

/-- a uniformly positive level is not syntactically zero. -/
theorem isZero_false_of_uniformType {l : Level} (h : UniformType l) : isZero l = false := by
  cases hz : isZero l with
  | false => rfl
  | true =>
      have h0 := (isZero_iff_eqN_zero l).1 hz (fun i => some ((fun _ => 0) i))
      rw [Rcic.Declarative.eval_total] at h0
      have h1 : evalTotal (fun _ => 0) l = 0 := Option.some.inj h0
      have h2 := h (fun _ => 0)
      rw [h1] at h2
      exact absurd h2 (Nat.lt_irrefl 0)

/-! ## (2) related argument lists: weakening, heights, the diagonal -/

section Args
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

theorem argsRelKA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) (hNC : EnvNormClosedA E) {k : Nat}
    {Γ : LCtxA} (ρ : WkSpecA)
    (hρ : WkOkA E I n ρ Γ) :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKA E I n ρ₀ k Γ T as as' →
    ArgsRelKA E I n ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ T) (as.map (wkExprA ρ)) (as'.map (wkExprA ρ))
  | _, _, _, .nil _ => .nil _
  | _, _, _, .cons A u B v f f' fs fs' h hs => by
      rw [wkExprA_pi_ub]
      refine .cons _ u _ v _ _ _ _ (LRRelA_wk hE hNC hI h ρ hρ) ?_
      have ih := argsRelKA_wk hE hI hNC ρ hρ hs
      rw [wkExprA_instantiate0A] at ih
      exact ih

/-- at a world that may be the identity. -/
theorem argsRelKA_wk₀ (hE : EnvClosedA E) (hI : IotaLiftA I) (hNC : EnvNormClosedA E) {k : Nat}
    {Γ : LCtxA} {ρ : WkSpecA}
    (hρ : WkOk₀A E I n ρ Γ) {T : ExprA} {as as' : List ExprA} (h : ArgsRelKA E I n ρ₀ k Γ T as as') :
    ArgsRelKA E I n ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ T) (as.map (wkExprA ρ)) (as'.map (wkExprA ρ)) := by
  rcases hρ with rfl | hρ
  · rw [map_wkExprA_nil, map_wkExprA_nil]; exact h
  · exact argsRelKA_wk hE hI hNC ρ hρ h

theorem argsRelKA_mono {j k : Nat} (hjk : j ≤ k) {Γ : LCtxA} :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKA E I n ρ₀ j Γ T as as' →
    ArgsRelKA E I n ρ₀ k Γ T as as'
  | _, _, _, .nil _ => .nil _
  | _, _, _, .cons A u B v f f' fs fs' h hs =>
      .cons A u B v f f' fs fs' (LRRelA_mono hjk h) (argsRelKA_mono hjk hs)

/-- related lists are self-related on the left. -/
theorem argsRelKA_refl_left (hEN : EnvNormCtorTypeA E) {k : Nat} {Γ : LCtxA} :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKA E I n ρ₀ k Γ T as as' →
    ArgsRelKA E I n ρ₀ k Γ T as as
  | _, _, _, .nil _ => .nil _
  | _, _, _, .cons A u B v f _ fs _ h hs =>
      .cons A u B v f f fs fs (LRRelA_refl_left hEN h) (argsRelKA_refl_left hEN hs)

/-- a world keeps a context well formed. -/
theorem ctxWfA_wk₀ {Γ : LCtxA} {ρ : WkSpecA} (hΓ : Nonempty (CtxWfA E I n Γ)) (hρ : WkOk₀A E I n ρ Γ) :
    Nonempty (CtxWfA E I n (wkCtxA ρ Γ)) := by
  rcases hρ with rfl | hρ
  · exact hΓ
  · exact hρ.2

end Args

/-! ## (3) the family's parameters as a valid substitution -/

section Params
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- the family's instantiated type, split at its parameters: the parameters' telescope over the
    instantiated index telescope. -/
theorem FamViewA.inst_split {fm : CheckedMemberA} (fv : FamViewA fm) (ls : List Level) :
    instantiateLevelsA ls fm.mtypeA =
      (piTelA (instDomsA ls fv.params) (instantiateLevelsA ls fv.idxTelA)
        (instLevel ls (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2)).1 := by
  have h := congrArg Prod.fst (instantiateLevelsA_piTelA ls fv.idxTelA
    (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2 fv.params)
  rw [fv.stored, piTelA_append]
  exact h

/-- the parameters' context is well formed in the base (the family's typing). -/
theorem FamViewA.paramsCtxWf {fm : CheckedMemberA} (fv : FamViewA fm) {a : Nat} {u : Level}
    (hT : HasTyA E₀ I a [] fm.mtypeA (.sort u)) : Nonempty (CtxWfA E₀ I a (telCtxA fv.params)) := by
  rw [fv.stored, piTelA_append] at hT
  have h := (ctxWfA_telA _ _ fv.params (Γ := []) .nil hT).1
  rw [List.append_nil] at h
  exact h

/-- THE PARAMETERS' VALID SUBSTITUTION IN A WORLD: parameters related along the family's type at
    its levels `ls`, carried into a world, are a valid pair for the parameters' context at any
    bounded list `=ₙ` `ls`, at every height above the outer one and a threshold. -/
theorem paramSubstA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {fm : CheckedMemberA} (fv : FamViewA fm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    {ls lsC : List Level} (hb : levelsBounded n ls = true) (hbC : levelsBounded n lsC = true)
    (hl : ls.length = fm.arity) (hlC : lsC.length = fm.arity) (heq : eqNList ls lsC) :
    ∃ K₀, ∀ K, K₀ ≤ K → ∀ {k : Nat} {Γ : LCtxA} (ps ps' is is' : List ExprA), k ≤ K →
      Nonempty (CtxWfA E I n Γ) → ps.length = fm.nparamsA → ps'.length = fm.nparamsA →
      ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is') →
      ∀ ρ, WkOk₀A E I n ρ Γ →
      ValidSubstA E I n ρ₀ K (wkCtxA ρ Γ) (consListA (ps.map (wkExprA ρ)) SubstA.id)
        (consListA (ps'.map (wkExprA ρ)) SubstA.id) (instCtxA lsC (telCtxA fv.params)) := by
  obtain ⟨hwf⟩ := fv.paramsCtxWf hT
  obtain ⟨K₀, hK₀⟩ := validSubstA_of_tel_lv hfund hfc hE₀ hI hEN hR₀ hEL₀ hIL hb hbC hl hlC heq fv.params hwf
  refine ⟨K₀, fun K hK k Γ ps ps' is is' hkK hΓ hps hps' hrel ρ hρ => ?_⟩
  have hpl : ps.length = ps'.length := hps.trans hps'.symm
  obtain ⟨_, _, h₀, _⟩ := argsRelKA_append_inv hpl hrel
  have hw := argsRelKA_mono hkK (argsRelKA_wk₀ hE hI hNC hρ h₀)
  rw [wkExprA_closed (liftA_instantiateLevelsA_closed hcl ls), fv.inst_split] at hw
  exact hK₀ K hK (wkCtxA ρ Γ) (ctxWfA_wk₀ hΓ hρ) _ _ _ _
    (by rw [List.length_map, hps, ← fv.nparams]) hw

end Params

/-! ## (4) the field datum (`hFld`) -/

theorem map_eq_append_cons {α β : Type} {g : α → β} : (l : List α) → (xs : List β) → (y : β) →
    (ys : List β) → l.map g = xs ++ y :: ys →
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.map g = xs ∧ g a = y ∧ l₂.map g = ys
  | [], [], _, _, h => nomatch h
  | [], _ :: _, _, _, h => nomatch h
  | a :: l, [], _, _, h => by
      injection h with h1 h2
      exact ⟨[], a, l, rfl, rfl, h1, h2⟩
  | a :: l, x :: xs, y, ys, h => by
      injection h with h1 h2
      obtain ⟨l₁, b, l₂, e, e1, e2, e3⟩ := map_eq_append_cons l xs y ys h2
      exact ⟨a :: l₁, b, l₂, by rw [e]; rfl, by rw [List.map_cons, h1, e1], e2, e3⟩

/-- the clause's height bounds a plain field's sort, at any `=ₙ` list (05 §7). -/
theorem plainSort_ht_le {ρ₀ : Nat → Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    (hUT : UniformType fv.sort) {u₀ : Level}
    (h : UniformProp fv.sort ∨ (UniformType fv.sort ∧ leN u₀ fv.sort))
    {ls lsC : List Level} (hlsC : eqNList ls lsC) :
    ht ρ₀ (instLevel lsC u₀) ≤ ht ρ₀ (instLevel ls fv.sort) := by
  rcases h with hP | ⟨_, hle⟩
  · have h1 := hUT (fun _ => 0)
    rw [hP (fun _ => 0)] at h1
    exact absurd h1 (Nat.lt_irrefl 0)
  · rw [ht_of_eqN (instLevel_eqNList hlsC fv.sort)]
    exact ht_le_of_leN (leN_instLevel hle lsC)

section FieldDatum
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a walk's left list walks against itself, when the position relations are self-related on the
    left (the recursive positions then carry nothing). -/
theorem argsRelA_diag (hEN : EnvNormCtorTypeA E) {R : Nat → List ExprA → ExprA → ExprA → Prop} {X : CRelA}
    {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} (hR : ∀ i prev a a', R i prev a a' → R i prev a a) :
    {i : Nat} → {prev : List ExprA} → {T : ExprA} → {ks : List FieldShape} → {fs fs' : List ExprA} →
    ArgsRelA R X F i prev T ks fs fs' → ArgsRelA R (fun _ _ _ => True) (fun _ _ _ _ _ _ => True) i prev T ks fs fs
  | _, _, _, _, _, _, .nil _ _ _ => .nil _ _ _
  | _, _, _, _, _, _, .plain i prev A u B v f _ ks fs _ h hs =>
      .plain i prev A u B v f f ks fs fs (hR _ _ _ _ h) (argsRelA_diag hEN hR hs)
  | _, _, _, _, _, _, .directRec i prev A u B v f _ ks fs _ _ hs =>
      .directRec i prev A u B v f f ks fs fs trivial (argsRelA_diag hEN hR hs)
  | _, _, _, _, _, _, .funRec i prev A u B v f _ j ks fs _ _ hs =>
      .funRec i prev A u B v f f j ks fs fs trivial (argsRelA_diag hEN hR hs)

/-- the canonical field relation is self-related on the left. -/
theorem famRsA_refl_left (hEN : EnvNormCtorTypeA E) {j : Nat} {Γ : LCtxA} {ρ : WkSpecA} {c : Nat}
    {lsC : List Level} :
    ∀ i prev a a', famRsA E I n ρ₀ j Γ ρ c lsC i prev a a' → famRsA E I n ρ₀ j Γ ρ c lsC i prev a a :=
  fun _ _ _ _ ⟨cm, D, uD, C, vC, hm, hT, hr⟩ => ⟨cm, D, uD, C, vC, hm, hT, LRRelA_refl_left hEN hr⟩

/-- THE PLAIN FIELD DOMAINS OF TWO INSTANCES. A constructor of the group, its telescope at
    parameters `ps` and at `ps'` (related along the family's type at the carrier's levels), at
    bounded level lists `lsC` and `lsC'` `=ₙ` the carrier's, a field walk `pre ~ pre'` with the
    canonical field relation reaching a plain field: the left domain (after `pre`, at `ps`, `lsC`)
    and the right one (after `pre'`, at `ps'`, `lsC'`) are equal at any height `j` above the family's
    sort, and valid there. The walk's plain arguments and the parameters are a valid pair at a large
    height (`fieldWalkA`, `paramSubstA`), where the domain's base derivation across the two lists
    relates the two instances at its sort (`fundLevelsA`); the sort is below the family's (05 §7). -/
theorem plainDomA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ρ : WkSpecA} (hρ : WkOk₀A E I n ρ Γ) {c : Nat}
    {cm : CheckedMemberA}
    {lsA lsC lsC' : List Level} {kinds ksPre ks : List FieldShape} {T T' : ExprA} {pre pre' : List ExprA}
    {D : ExprA} {uD : Level} {C : ExprA} {vC : Level} {D' : ExprA} {uD' : Level} {C' : ExprA}
    {vC' : Level}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds) (hsp : kinds = ksPre ++ FieldShape.nonrecursive :: ks)
    (hlA : eqNList ls lsA) (hlAC : eqNListB n lsA lsC) (hlCC : eqNListB n lsC lsC')
    (hTc : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hTc' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    (hw : ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) X F fm.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre')
    (hTD : applyTelA pre T = some (.pi D uD C vC)) (hTD' : applyTelA pre' T' = some (.pi D' uD' C' vC')) :
    LREqA E I n ρ₀ j (wkCtxA ρ Γ) D D' ∧ (∃ R, LRTyA E I n ρ₀ j (wkCtxA ρ Γ) D R) ∧
      (∃ R, LRTyA E I n ρ₀ j (wkCtxA ρ Γ) D' R) := by
  obtain ⟨gc, hgc, hgr, hgm⟩ := hcensus c cm hcm hk hfam
  subst hgr hgm
  have hlsC : eqNList ls lsC := eqNListA_trans hlA hlAC.1
  have hlsC' : eqNList ls lsC' := eqNListA_trans hlsC hlCC.1
  have hlC : lsC.length = fm.arity := (eqNListA_length hlsC).symm.trans hl
  have hlC' : lsC'.length = fm.arity := (eqNListA_length hlsC').symm.trans hl
  have hbC : levelsBounded n lsC = true := hlAC.2
  have hbC' : levelsBounded n lsC' = true := hlCC.2
  have hΓρ := ctxWfA_wk₀ hΓ hρ
  have hpsρ : (ps.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps]
  have hpsρ' : (ps'.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps']
  have hTv := gc.applyTel_params lsC hlC (ps.map (wkExprA ρ)) hpsρ
  rw [hTc] at hTv
  injection hTv with hTe
  subst hTe
  have hTv' := gc.applyTel_params lsC' hlC' (ps'.map (wkExprA ρ)) hpsρ'
  rw [hTc'] at hTv'
  injection hTv' with hTe'
  subst hTe'
  rw [gc.normA_getD] at hkinds
  rw [gc.view.shapes hfresh] at hkinds
  injection hkinds with hkinds
  rw [hsp] at hkinds
  obtain ⟨fsPre, F, fsRest, hfs, hpreK, hFK, -⟩ := map_eq_append_cons _ _ _ _ hkinds
  cases F with
  | drec _ => cases hFK
  | frec _ _ _ _ => cases hFK
  | drecD _ _ => cases hFK
  | plain D₀ u₀ =>
      have hmem : FieldA.plain D₀ u₀ ∈ gc.view.fields := by
        rw [hfs]; exact List.mem_append_right _ (List.mem_cons_self _ _)
      have hty := gc.view.typed
      rw [hfs] at hty
      obtain ⟨hwf⟩ := fv.paramsCtxWf hT
      obtain ⟨K₁, hK₁⟩ := fieldWalkA (f := f) (s := instLevel lsC fv.sort) (pl := ps.map (wkExprA ρ))
        (j := j) (Γ := Γ) (ρ := ρ) (X := X) (F := F) hfc hE₀ hI hEN hR₀ hEL₀ hIL hbC hlC hcm hΓρ fsPre hty hwf
      have hdrop := FieldsTyA.drop fsPre hty
      have hΓp := ctxWfA_plainCtx fsPre hty hwf
      cases hdrop with
      | plain _ _ _ _ _ _ hD _ =>
          obtain ⟨K₂, hK₂⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hbC hbC' hlC hlC' hlCC.1 hΓp hD
          obtain ⟨K₃, hK₃⟩ := paramSubstA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL fv hcl hT hb hbC hl hlC hlsC
          have hK1 : K₁ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
          have hK2 : K₂ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
          have hK3 : K₃ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
          have hKk : k ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
          have hKj : j ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
          have hV₀ := hK₃ _ hK3 ps ps' is is' hKk hΓ hps hps' hrel ρ hρ
          rw [hfs] at hTc hw hTD hTD'
          rw [← hpreK] at hw
          have hV₁ := hK₁ _ hK1 hKj _ _ fm.nparamsA (ps.map (wkExprA ρ)) pre pre' hV₀ hTc hw
          have hlen : pre.length = fsPre.length := by
            rw [(argsRelA_length hw).1, List.length_map]
          have hlen' : pre'.length = fsPre.length := by
            rw [(argsRelA_length hw).2, List.length_map]
          have hpfx := applyTelA_ctorFieldsA_prefix f lsC (instLevel lsC fv.sort)
            (gc.view.res.map (instantiateLevelsA lsC)) (((FieldA.plain D₀ u₀ :: fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
            ((fsPre.map FieldA.norm).map (FieldA.instLevels lsC)) pre (by rw [List.length_map, List.length_map, hlen])
            (ps.map (wkExprA ρ)) (consListA (ps.map (wkExprA ρ)) SubstA.id)
          rw [← List.map_append, ← List.map_append, plainArgsA_instLevels, plainArgsA_norm] at hpfx
          rw [hpfx] at hTD
          simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA] at hTD
          injection hTD with hTD
          injection hTD with hDe _
          have hpfx' := applyTelA_ctorFieldsA_prefix f lsC' (instLevel lsC' fv.sort)
            (gc.view.res.map (instantiateLevelsA lsC')) (((FieldA.plain D₀ u₀ :: fsRest).map FieldA.norm).map (FieldA.instLevels lsC'))
            ((fsPre.map FieldA.norm).map (FieldA.instLevels lsC')) pre' (by rw [List.length_map, List.length_map, hlen'])
            (ps'.map (wkExprA ρ)) (consListA (ps'.map (wkExprA ρ)) SubstA.id)
          rw [← List.map_append, ← List.map_append, plainArgsA_instLevels, plainArgsA_norm] at hpfx'
          rw [hpfx'] at hTD'
          simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA] at hTD'
          injection hTD' with hTD'
          injection hTD' with hDe' _
          obtain ⟨_, hDrel⟩ := hK₂ _ hK2 (wkCtxA ρ Γ) _ _ hΓρ hV₁
          have hht : ht ρ₀ (instLevel lsC u₀) ≤ j :=
            Nat.le_trans (plainSort_ht_le hUT (gc.view.univ D₀ u₀ hmem) hlsC) hj
          obtain ⟨heq, hva, hvb⟩ := (LRRelA_sort_elim' hDrel).1 j hht
          rw [hDe, hDe'] at heq
          rw [hDe] at hva
          rw [hDe'] at hvb
          exact ⟨heq, hva, hvb⟩

/-- the plain arguments of binders read as plain fields are all of them (R-NoFunRec-1 step 1 (1c-δ)). -/
theorem plainArgsA_plainA : (ds : List (ExprA × Level)) → (zs : List ExprA) → zs.length = ds.length →
    plainArgsA (ds.map plainA) zs = zs
  | [], [], _ => rfl
  | _ :: ds, z :: zs, h => by
      show z :: plainArgsA (ds.map plainA) zs = z :: zs
      rw [plainArgsA_plainA ds zs (Nat.succ.inj h)]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- binders read as plain fields count one each. -/
theorem plainIdxA_plainA : (ds : List (ExprA × Level)) → (c : Nat) →
    plainIdxA (ds.map plainA) c = c + ds.length
  | [], _ => rfl
  | _ :: ds, c => by
      show plainIdxA (ds.map plainA) (c + 1) = c + (ds.length + 1)
      rw [plainIdxA_plainA ds (c + 1)]
      omega

/-- binders read as plain fields are all `nonrecursive`. -/
theorem map_shape_plainA (ds : List (ExprA × Level)) :
    (ds.map plainA).map FieldA.shape = List.replicate ds.length FieldShape.nonrecursive := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [plainA, FieldA.shape, ih, List.replicate_succ]

/-- the position relation of a telescope's inner walk: at the domain reached in `T0` after the prefix. -/
def innerRelAtA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (j : Nat) (Δ : LCtxA)
    (T0 : ExprA) : Nat → List ExprA → ExprA → ExprA → Prop :=
  fun _ prev x x' => ∃ (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
    applyTelA prev T0 = some (.pi D uD C vC) ∧ LRRelA E I n ρ₀ j Δ D x x'

/-- a related list along a telescope is a walk with no recursive position, at the relation of the
    domain reached (`innerRelAtA`). -/
theorem argsRelA_of_argsRelKA (hEN : EnvNormCtorTypeA E) {j : Nat} {Δ : LCtxA} {T0 : ExprA}
    {X : CRelA}
    {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ {T : ExprA} {zs zs' : List ExprA} {i : Nat} {prev : List ExprA},
    ArgsRelKA E I n ρ₀ j Δ T zs zs' → applyTelA prev T0 = some T →
    ArgsRelA (innerRelAtA E I n ρ₀ j Δ T0) X F i prev T (zs.map (fun _ => FieldShape.nonrecursive)) zs zs'
  | _, _, _, _, _, .nil _, _ => .nil _ _ _
  | _, _, _, i, prev, .cons A u B v f f' fs fs' h hs, hT => by
      exact .plain i prev A u B v f f' _ fs fs' ⟨A, u, B, v, hT, h⟩
        (argsRelA_of_argsRelKA hEN hs (applyTelA_snoc prev T0 hT))

/-- a built telescope that is still a Π after the arguments has more fields than arguments. -/
theorem applyTelA_ctorFieldsA_lt (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (zs : List ExprA) → (pl : List ExprA) → (σ : SubstA) → {A : ExprA} → {u : Level} →
    {B : ExprA} → {v : Level} →
    applyTelA zs (ctorFieldsA f ls w pl σ fs res).1 = some (.pi A u B v) → zs.length < fs.length
  | [], zs, pl, σ, A, u, B, v, h => by
      exfalso
      have hne : ∀ A u B v, foldAppsA (.const f ls) (pl ++ res.map (substA σ)) ≠ .pi A u B v := by
        intro A u B v h1
        have h2 := foldAppsA_const_head f ls (pl ++ res.map (substA σ))
        rw [h1] at h2
        have h3 := congrArg Prod.fst h2
        exact ExprA.noConfusion h3
      cases zs with
      | nil =>
          have h1 : foldAppsA (.const f ls) (pl ++ res.map (substA σ)) = .pi A u B v :=
            Option.some.inj h
          exact hne _ _ _ _ h1
      | cons z zs =>
          cases hT : foldAppsA (.const f ls) (pl ++ res.map (substA σ)) with
          | pi A₀ u₀ B₀ v₀ => exact hne _ _ _ _ hT
          | _ => simp only [ctorFieldsA, hT, applyTelA] at h <;> exact Option.noConfusion h
  | .plain D u₀ :: fs, [], pl, σ, A, u, B, v, _ => Nat.succ_pos _
  | .drec idx :: fs, [], pl, σ, A, u, B, v, _ => Nat.succ_pos _
  | .frec _ _ _ _ :: fs, [], pl, σ, A, u, B, v, _ => Nat.succ_pos _
  | .drecD _ _ :: fs, [], pl, σ, A, u, B, v, _ => Nat.succ_pos _
  | .plain D u₀ :: fs, z :: zs, pl, σ, A, u, B, v, h => by
      simp only [ctorFieldsA, applyTelA] at h
      rw [instantiate0A_ctorFieldsA_plain] at h
      exact Nat.succ_lt_succ (applyTelA_ctorFieldsA_lt f ls w res fs zs pl (SubstA.cons z σ) h)
  | .drec idx :: fs, z :: zs, pl, σ, A, u, B, v, h => by
      simp only [ctorFieldsA, applyTelA] at h
      rw [instantiate0A_ctorFieldsA_drec] at h
      exact Nat.succ_lt_succ (applyTelA_ctorFieldsA_lt f ls w res fs zs pl σ h)
  | .frec _ _ _ _ :: fs, z :: zs, pl, σ, A, u, B, v, h => by
      simp only [ctorFieldsA, applyTelA] at h
      rw [instantiate0A_ctorFieldsA_drec] at h
      exact Nat.succ_lt_succ (applyTelA_ctorFieldsA_lt f ls w res fs zs pl σ h)
  | .drecD _ _ :: fs, z :: zs, pl, σ, A, u, B, v, h => by
      simp only [ctorFieldsA, applyTelA] at h
      rw [instantiate0A_ctorFieldsA_drec] at h
      exact Nat.succ_lt_succ (applyTelA_ctorFieldsA_lt f ls w res fs zs pl σ h)

/-- inner arguments related by the canonical inner relations (`innerRelsA` of `famRsIA`) along a
    field's weakened domain are related along it at the extended context (`innerRelsA_famRsIA`). -/
theorem argsRelKA_of_innerRelsA (hE : EnvClosedA E) (hNC : EnvNormClosedA E) {j : Nat} {Γ : LCtxA}
    {ρ ρ' : WkSpecA} {c : Nat}
    {cm : CheckedMemberA} {lsC : List Level} {i : Nat} {prev : List ExprA} {D : ExprA} {uD : Level}
    {C : ExprA} {vC : Level} (hm : E.members c = some cm)
    (hncl : ∀ k, liftA k 1 (cm.normA.getD cm.mtypeA) = (cm.normA.getD cm.mtypeA))
    (hT : applyTelA prev (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some (.pi D uD C vC)) :
    ∀ {ii : Nat} {iprev : List ExprA} {T : ExprA} {zs zs' : List ExprA},
    ArgsRelPA (innerRelsA (famRsIA E I n ρ₀ j Γ) ρ c lsC i prev ρ') ii iprev T zs zs' →
    applyTelA iprev (wkExprA ρ' D) = some T →
    ArgsRelKA E I n ρ₀ j (wkCtxA ρ' (wkCtxA ρ Γ)) T zs zs'
  | _, _, _, _, _, .nil _ _ _, _ => .nil _
  | _, iprev, _, _, _, .cons _ _ A u B v f f' fs fs' h hs, hD => by
      rw [innerRelsA_famRsIA hE hm hncl hT hD] at h
      exact .cons A u B v f f' fs fs' h (argsRelKA_of_innerRelsA hE hNC hm hncl hT hs (applyTelA_snoc iprev _ hD))

/-- a walk at the canonical field relation weakens to the composed world: each position's relation is
    the relation at the weakened domain (the constructor's type is closed, `LRRelA_wk`). -/
theorem argsRelA_famRsA_wk (hE : EnvClosedA E) (hI : IotaLiftA I) (hNC : EnvNormClosedA E) {j : Nat}
    {Γ : LCtxA} {ρ ρ' : WkSpecA}
    (hρ' : WkOkA E I n ρ' (wkCtxA ρ Γ)) {c : Nat} {lsC : List Level} {i : Nat} {pl : List ExprA}
    {T : ExprA} {ks : List FieldShape} {pre pre' : List ExprA} {X : CRelA}
    {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop}
    (hncl : ∀ cm, E.members c = some cm → ∀ k,
        liftA k 1 (cm.normA.getD cm.mtypeA) = (cm.normA.getD cm.mtypeA))
    (hw : ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) X F i pl T ks pre pre') :
    ArgsRelA (famRsA E I n ρ₀ j Γ (WkSpecA.comp ρ ρ') c lsC) (fun _ _ _ => True)
      (fun _ _ _ _ _ _ => True) i (pl.map (wkExprA ρ')) (wkExprA ρ' T) ks (pre.map (wkExprA ρ'))
      (pre'.map (wkExprA ρ')) :=
  argsRelA_wk (i₀ := i) (prev₀ := pl) (T₀ := T) ρ' ks (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
    (fun ksPre ks pre pre' D uD C vC f f' _ _ _ _ hr => by
      obtain ⟨cm, D₂, uD₂, C₂, vC₂, hm, hT, hr⟩ := hr
      have hcl := liftA_instantiateLevelsA_closed (hncl cm hm) lsC
      refine ⟨cm, wkExprA ρ' D₂, uD₂, wkExprA (WkSpecA.ub ρ') C₂, vC₂, hm, ?_, ?_⟩
      · rw [applyTelA_wk_closed ρ' _ hcl, hT, Option.map_some', wkExprA_pi_ub]
      · rw [wkCtxA_comp]
        exact LRRelA_wk hE hNC hI hr ρ' hρ')
    hw [] [] [] (by simp) (by simp) (by simp) rfl (.nil _ _ _) (.nil _ _ _)

/-- THE OUTER WALK TO A FUNCTION-RECURSIVE FIELD (R-NoFunRec-1 step 1 (1c-δ)). A field walk reaching a
    constructor's field of shape `recursive (jn + 1)`: the view's field there is `frec B uB Bs idx` with
    `jn` inner binders after the first, its domain after the walk is the field telescope at the inner
    binders read as plain fields (`frecDomA_eq`), typed in the plain context (`FieldsTyA.frec`), and the
    parameters' and the walk's plain arguments are a valid pair above a threshold (`paramSubstA`,
    `fieldWalkA`). Stated for a continuation, which reads the field's data. -/
theorem frecWalkA {Goal : Prop} (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat}
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ρ : WkSpecA}
    (hρ : WkOk₀A E I n ρ Γ) {c : Nat} {cm : CheckedMemberA}
    {lsA lsC lsC' : List Level} {kinds ksPre ks : List FieldShape} {jn : Nat} {T T' : ExprA}
    {pre pre' : List ExprA} {D : ExprA} {uD : Level} {C : ExprA} {vC : Level} {D' : ExprA}
    {uD' : Level} {C' : ExprA} {vC' : Level}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hsp : kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    (hlA : eqNList ls lsA) (hlAC : eqNListB n lsA lsC) (hlCC : eqNListB n lsC lsC')
    (hTc : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hTc' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    (hw : ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) X F fm.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre')
    (hTD : applyTelA pre T = some (.pi D uD C vC)) (hTD' : applyTelA pre' T' = some (.pi D' uD' C' vC'))
    (hcont : ∀ (fsPre : List FieldA) (B : ExprA) (uB : Level) (Bs : List (ExprA × Level)) (idx : List ExprA),
      Bs.length = jn → pre.length = fsPre.length → pre'.length = fsPre.length →
      FieldsTyA E₀ I fm.arity (fun k => liftA 0 k fv.idxTelA) (plainCtxA fsPre (telCtxA fv.params))
        (plainIdxA fsPre 0) (((B, uB) :: Bs).map plainA) idx →
      CtxWfA E₀ I fm.arity (plainCtxA fsPre (telCtxA fv.params)) →
      (∀ d ∈ (B, uB) :: Bs, UniformProp fv.sort ∨ (UniformType fv.sort ∧ leN d.2 fv.sort)) →
      (ctorFieldsA f lsC (instLevel lsC fv.sort) (ps.map (wkExprA ρ))
        (consListA (plainArgsA fsPre pre) (consListA (ps.map (wkExprA ρ)) SubstA.id))
        ((instDomsA lsC ((B, uB) :: Bs)).map plainA) (idx.map (instantiateLevelsA lsC))).1 = D →
      (ctorFieldsA f lsC' (instLevel lsC' fv.sort) (ps'.map (wkExprA ρ))
        (consListA (plainArgsA fsPre pre') (consListA (ps'.map (wkExprA ρ)) SubstA.id))
        ((instDomsA lsC' ((B, uB) :: Bs)).map plainA) (idx.map (instantiateLevelsA lsC'))).1 = D' →
      (∃ (fsRest : List FieldA) (res : List ExprA),
        Nonempty (FieldsTyA E₀ I fm.arity (fun k => liftA 0 k fv.idxTelA) (telCtxA fv.params) 0
          (fsPre ++ FieldA.frec B uB Bs idx :: fsRest) res)) →
      (∃ K₁, ∀ K, K₁ ≤ K → j ≤ K → k ≤ K →
        ValidSubstA E I n ρ₀ K (wkCtxA ρ Γ) (consListA (ps.map (wkExprA ρ)) SubstA.id)
          (consListA (ps'.map (wkExprA ρ)) SubstA.id) (instCtxA lsC (telCtxA fv.params)) ∧
        ValidSubstA E I n ρ₀ K (wkCtxA ρ Γ)
          (consListA (plainArgsA fsPre pre) (consListA (ps.map (wkExprA ρ)) SubstA.id))
          (consListA (plainArgsA fsPre pre') (consListA (ps'.map (wkExprA ρ)) SubstA.id))
          (instCtxA lsC (plainCtxA fsPre (telCtxA fv.params)))) → Goal) : Goal := by
  obtain ⟨gc, hgc, hgr, hgm⟩ := hcensus c cm hcm hk hfam
  subst hgr hgm
  have hlsC : eqNList ls lsC := eqNListA_trans hlA hlAC.1
  have hlsC' : eqNList ls lsC' := eqNListA_trans hlsC hlCC.1
  have hlC : lsC.length = fm.arity := (eqNListA_length hlsC).symm.trans hl
  have hlC' : lsC'.length = fm.arity := (eqNListA_length hlsC').symm.trans hl
  have hbC : levelsBounded n lsC = true := hlAC.2
  have hbC' : levelsBounded n lsC' = true := hlCC.2
  have hΓρ := ctxWfA_wk₀ hΓ hρ
  have hpsρ : (ps.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps]
  have hpsρ' : (ps'.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps']
  have hTv := gc.applyTel_params lsC hlC (ps.map (wkExprA ρ)) hpsρ
  rw [hTc] at hTv
  injection hTv with hTe
  subst hTe
  have hTv' := gc.applyTel_params lsC' hlC' (ps'.map (wkExprA ρ)) hpsρ'
  rw [hTc'] at hTv'
  injection hTv' with hTe'
  subst hTe'
  rw [gc.normA_getD] at hkinds
  rw [gc.view.shapes hfresh] at hkinds
  injection hkinds with hkinds
  rw [hsp] at hkinds
  obtain ⟨fsPre, F₀, fsRest, hfs, hpreK, hFK, -⟩ := map_eq_append_cons _ _ _ _ hkinds
  cases F₀ with
  | plain _ _ => cases hFK
  | drec _ => cases hFK
  | drecD _ _ => cases hFK
  | frec B uB Bs idx =>
      have hBs : Bs.length = jn := by
        have h1 : FieldShape.recursive (Bs.length + 1) = FieldShape.recursive (jn + 1) := hFK
        injection h1 with h2
        exact Nat.succ.inj h2
      have hmem : FieldA.frec B uB Bs idx ∈ gc.view.fields := by
        rw [hfs]; exact List.mem_append_right _ (List.mem_cons_self _ _)
      have hty := gc.view.typed
      rw [hfs] at hty
      obtain ⟨hwf⟩ := fv.paramsCtxWf hT
      obtain ⟨K₁, hK₁⟩ := fieldWalkA (f := f) (s := instLevel lsC fv.sort) (pl := ps.map (wkExprA ρ))
        (j := j) (Γ := Γ) (ρ := ρ) (X := X) (F := F) hfc hE₀ hI hEN hR₀ hEL₀ hIL hbC hlC hcm hΓρ fsPre hty hwf
      have hdrop := FieldsTyA.drop fsPre hty
      have hΓp := ctxWfA_plainCtx fsPre hty hwf
      cases hdrop with
      | frec _ _ _ _ _ _ _ _ hdom tl =>
          obtain ⟨K₃, hK₃⟩ := paramSubstA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL fv hcl hT hb hbC hl hlC hlsC
          rw [hfs] at hTc hw hTD hTD'
          rw [← hpreK] at hw
          have hlen : pre.length = fsPre.length := by
            rw [(argsRelA_length hw).1, List.length_map]
          have hlen' : pre'.length = fsPre.length := by
            have hwl := (argsRelA_length hw).2
            rw [List.length_map] at hwl
            exact hwl
          have hpfx := applyTelA_ctorFieldsA_prefix f lsC (instLevel lsC fv.sort)
            (gc.view.res.map (instantiateLevelsA lsC))
            (((FieldA.frec B uB Bs idx :: fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
            ((fsPre.map FieldA.norm).map (FieldA.instLevels lsC)) pre (by rw [List.length_map, List.length_map, hlen])
            (ps.map (wkExprA ρ)) (consListA (ps.map (wkExprA ρ)) SubstA.id)
          rw [← List.map_append, ← List.map_append, plainArgsA_instLevels, plainArgsA_norm] at hpfx
          rw [hpfx] at hTD
          simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA] at hTD
          injection hTD with hTD
          injection hTD with hDe _
          have hpfx' := applyTelA_ctorFieldsA_prefix f lsC' (instLevel lsC' fv.sort)
            (gc.view.res.map (instantiateLevelsA lsC'))
            (((FieldA.frec B uB Bs idx :: fsRest).map FieldA.norm).map (FieldA.instLevels lsC'))
            ((fsPre.map FieldA.norm).map (FieldA.instLevels lsC')) pre' (by rw [List.length_map, List.length_map, hlen'])
            (ps'.map (wkExprA ρ)) (consListA (ps'.map (wkExprA ρ)) SubstA.id)
          rw [← List.map_append, ← List.map_append, plainArgsA_instLevels, plainArgsA_norm] at hpfx'
          rw [hpfx'] at hTD'
          simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA] at hTD'
          injection hTD' with hTD'
          injection hTD' with hDe' _
          refine hcont fsPre B uB Bs idx hBs hlen hlen' hdom hΓp (gc.view.univI B uB Bs idx hmem)
            (by rw [← hDe, ← frecDomA_eq]; rfl) (by rw [← hDe', ← frecDomA_eq]; rfl)
            ⟨fsRest, gc.view.res, ⟨hty⟩⟩ ⟨max K₁ K₃, fun K hK hjK hkK => ?_⟩
          have hV₀ := hK₃ _ (Nat.le_trans (Nat.le_max_right _ _) hK) ps ps' is is' hkK hΓ hps hps' hrel ρ hρ
          have hV₁ := hK₁ _ (Nat.le_trans (Nat.le_max_left _ _) hK) hjK _ _ fm.nparamsA (ps.map (wkExprA ρ))
            pre pre' hV₀ hTc hw
          exact ⟨hV₀, hV₁⟩

/-- THE INNER DOMAINS OF TWO INSTANCES (R-NoFunRec-1 step 1 (1c-δ)). As `plainDomA`, a walk reaching a
    function-recursive field, then inner arguments related along its domain: the inner domain they reach,
    on the two sides, is equal at any height `j` above the family's sort and valid there. The inner
    binders are plain fields in the plain context (`FieldsTyA.frec`), so the inner walk is the field walk
    at the relation of the inner domains (`fieldWalkRelA`), and the domain's equality under the walk's
    pair is the base derivation's arm (`fundLevelsA`); the sort is below the family's (`univI`). -/
theorem frecInnerDomA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ρ : WkSpecA}
    (hρ : WkOk₀A E I n ρ Γ) {c : Nat} {cm : CheckedMemberA}
    {lsA lsC lsC' : List Level} {kinds ksPre ks : List FieldShape} {jn : Nat} {T T' : ExprA}
    {pre pre' : List ExprA} {D : ExprA} {uD : Level} {C : ExprA} {vC : Level} {D' : ExprA}
    {uD' : Level} {C' : ExprA} {vC' : Level}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hsp : kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    (hlA : eqNList ls lsA) (hlAC : eqNListB n lsA lsC) (hlCC : eqNListB n lsC lsC')
    (hTc : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hTc' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    (hw : ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) X F fm.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre')
    (hTD : applyTelA pre T = some (.pi D uD C vC)) (hTD' : applyTelA pre' T' = some (.pi D' uD' C' vC'))
    {zs zs' : List ExprA} {D₁ : ExprA} {u₁ : Level} {C₁ : ExprA} {v₁ : Level} {D₁' : ExprA}
    {u₁' : Level} {C₁' : ExprA} {v₁' : Level}
    (hz : ArgsRelKA E I n ρ₀ j (wkCtxA ρ Γ) D zs zs')
    (hD₁ : applyTelA zs D = some (.pi D₁ u₁ C₁ v₁)) (hD₁' : applyTelA zs' D' = some (.pi D₁' u₁' C₁' v₁')) :
    LREqA E I n ρ₀ j (wkCtxA ρ Γ) D₁ D₁' ∧ (∃ R, LRTyA E I n ρ₀ j (wkCtxA ρ Γ) D₁ R) ∧
      (∃ R, LRTyA E I n ρ₀ j (wkCtxA ρ Γ) D₁' R) := by
  refine frecWalkA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hb hl hΓ hps hps' hrel hρ
    hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' ?_
  intro fsPre B uB Bs idx hBs hlen hlen' hdom hΓp huniv hDe hDe' _ ⟨K₁, hK₁⟩
  have hlsC : eqNList ls lsC := eqNListA_trans hlA hlAC.1
  have hlsC' : eqNList ls lsC' := eqNListA_trans hlsC hlCC.1
  have hlC : lsC.length = fm.arity := (eqNListA_length hlsC).symm.trans hl
  have hlC' : lsC'.length = fm.arity := (eqNListA_length hlsC').symm.trans hl
  have hbC : levelsBounded n lsC = true := hlAC.2
  have hbC' : levelsBounded n lsC' = true := hlCC.2
  have hΓρ := ctxWfA_wk₀ hΓ hρ
  have hzl : zs.length = zs'.length := argsRelKA_length hz
  have hlt : zs.length < ((B, uB) :: Bs).length := by
    have h1 := applyTelA_ctorFieldsA_lt f lsC (instLevel lsC fv.sort) (idx.map (instantiateLevelsA lsC))
      ((instDomsA lsC ((B, uB) :: Bs)).map plainA) zs (ps.map (wkExprA ρ)) _ (by rw [hDe]; exact hD₁)
    simpa [instDomsA] using h1
  obtain ⟨dsPre, d, dsRest, hds, hdl⟩ : ∃ dsPre d dsRest,
      (B, uB) :: Bs = dsPre ++ d :: dsRest ∧ dsPre.length = zs.length := by
    refine ⟨((B, uB) :: Bs).take zs.length, ((B, uB) :: Bs)[zs.length],
      ((B, uB) :: Bs).drop (zs.length + 1), ?_, ?_⟩
    · rw [← List.drop_eq_getElem_cons hlt, List.take_append_drop]
    · simp only [List.length_take]
      omega
  rw [hds] at hdom hDe hDe' huniv
  have hdlI : (instDomsA lsC dsPre).length = zs.length := by simp [instDomsA, hdl]
  have hdlI' : (instDomsA lsC' dsPre).length = zs'.length := by simp [instDomsA, hdl, hzl]
  have e : (instDomsA lsC (dsPre ++ d :: dsRest)).map plainA =
      (instDomsA lsC dsPre).map plainA ++ (instDomsA lsC (d :: dsRest)).map plainA := by
    simp [instDomsA, List.map_append]
  have e' : (instDomsA lsC' (dsPre ++ d :: dsRest)).map plainA =
      (instDomsA lsC' dsPre).map plainA ++ (instDomsA lsC' (d :: dsRest)).map plainA := by
    simp [instDomsA, List.map_append]
  rw [e] at hDe
  rw [e'] at hDe'
  rw [← hDe] at hD₁
  rw [← hDe'] at hD₁'
  have hap := applyTelA_ctorFieldsA_prefix f lsC (instLevel lsC fv.sort) (idx.map (instantiateLevelsA lsC))
    ((instDomsA lsC (d :: dsRest)).map plainA) ((instDomsA lsC dsPre).map plainA) zs
    (by rw [List.length_map, hdlI]) (ps.map (wkExprA ρ))
    (consListA (plainArgsA fsPre pre) (consListA (ps.map (wkExprA ρ)) SubstA.id))
  rw [hap] at hD₁
  rw [plainArgsA_plainA _ _ hdlI.symm] at hD₁
  simp only [instDomsA, List.map, plainA, ctorFieldsA] at hD₁
  injection hD₁ with hD₁
  injection hD₁ with hD₁e _
  have hap' := applyTelA_ctorFieldsA_prefix f lsC' (instLevel lsC' fv.sort) (idx.map (instantiateLevelsA lsC'))
    ((instDomsA lsC' (d :: dsRest)).map plainA) ((instDomsA lsC' dsPre).map plainA) zs'
    (by rw [List.length_map, hdlI']) (ps'.map (wkExprA ρ))
    (consListA (plainArgsA fsPre pre') (consListA (ps'.map (wkExprA ρ)) SubstA.id))
  rw [hap'] at hD₁'
  rw [plainArgsA_plainA _ _ hdlI'.symm] at hD₁'
  simp only [instDomsA, List.map, plainA, ctorFieldsA] at hD₁'
  injection hD₁' with hD₁'
  injection hD₁' with hD₁e' _
  have hdom' : FieldsTyA E₀ I fm.arity (fun k => liftA 0 k fv.idxTelA)
      (plainCtxA fsPre (telCtxA fv.params)) (plainIdxA fsPre 0)
      (dsPre.map plainA ++ (d :: dsRest).map plainA) idx := by
    rw [← List.map_append]; exact hdom
  have hTD0 : (ctorFieldsA f lsC (instLevel lsC fv.sort) (ps.map (wkExprA ρ))
      (consListA (plainArgsA fsPre pre) (consListA (ps.map (wkExprA ρ)) SubstA.id))
      (((dsPre.map plainA ++ (d :: dsRest).map plainA).map FieldA.norm).map (FieldA.instLevels lsC))
      (idx.map (instantiateLevelsA lsC))).1 = D := by
    rw [← List.map_append, map_norm_plainA, List.map_append, List.map_append,
      plainA_instLevels, plainA_instLevels]; exact hDe
  have hnorm₀ : ((dsPre.map plainA ++ (d :: dsRest).map plainA).map FieldA.norm) =
      dsPre.map plainA ++ (d :: dsRest).map plainA := by
    rw [← List.map_append, map_norm_plainA, List.map_append]
  have hdrop := FieldsTyA.drop (dsPre.map plainA) hdom'
  have hΓq := ctxWfA_plainCtx (dsPre.map plainA) hdom' hΓp
  cases hdrop with
  | plain _ _ _ _ _ _ hD _ =>
      obtain ⟨K₂, hK₂⟩ := fieldWalkRelA (f := f) (s := instLevel lsC fv.sort) (pl := ps.map (wkExprA ρ))
        (j := j) (Δ := wkCtxA ρ Γ) (T0 := D) (R := innerRelAtA E I n ρ₀ j (wkCtxA ρ Γ) D)
        (X := fun _ _ _ => True) (F := fun _ _ _ _ _ _ => True) hfc hE₀ hI hEN hR₀ hEL₀ hIL hbC hlC
        (fun _ prev x x' D₂ u₂ C₂ v₂ hT hr => by
          obtain ⟨D₃, u₃, C₃, v₃, hT', hr'⟩ := hr
          rw [hT] at hT'
          cases Option.some.inj hT'
          exact hr')
        hΓρ (dsPre.map plainA) hdom' hΓp
      obtain ⟨K₃, hK₃⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hbC hbC' hlC hlC' hlCC.1 hΓq hD
      have hK1 : K₁ ≤ max (max K₁ K₂) (max K₃ (max k j)) := by omega
      have hK2 : K₂ ≤ max (max K₁ K₂) (max K₃ (max k j)) := by omega
      have hK3 : K₃ ≤ max (max K₁ K₂) (max K₃ (max k j)) := by omega
      have hKk : k ≤ max (max K₁ K₂) (max K₃ (max k j)) := by omega
      have hKj : j ≤ max (max K₁ K₂) (max K₃ (max k j)) := by omega
      have hV₁ := (hK₁ _ hK1 hKj hKk).2
      have hw₁ : ArgsRelA (innerRelAtA E I n ρ₀ j (wkCtxA ρ Γ) D) (fun _ _ _ => True)
          (fun _ _ _ _ _ _ => True) 0 []
          (ctorFieldsA f lsC (instLevel lsC fv.sort) (ps.map (wkExprA ρ))
            (consListA (plainArgsA fsPre pre) (consListA (ps.map (wkExprA ρ)) SubstA.id))
            (((dsPre.map plainA ++ (d :: dsRest).map plainA).map FieldA.norm).map (FieldA.instLevels lsC))
            (idx.map (instantiateLevelsA lsC))).1
          ((dsPre.map plainA).map FieldA.shape) zs zs' := by
        rw [← List.map_append, map_norm_plainA, List.map_append]
        have h1 := argsRelA_of_argsRelKA hEN (X := fun _ _ _ => True) (F := fun _ _ _ _ _ _ => True)
          (i := 0) (prev := []) hz rfl
        rw [List.map_const'] at h1
        have hTD0' : (ctorFieldsA f lsC (instLevel lsC fv.sort) (ps.map (wkExprA ρ))
            (consListA (plainArgsA fsPre pre) (consListA (ps.map (wkExprA ρ)) SubstA.id))
            ((dsPre.map plainA ++ (d :: dsRest).map plainA).map (FieldA.instLevels lsC))
            (idx.map (instantiateLevelsA lsC))).1 = D := by
          rw [hnorm₀] at hTD0; exact hTD0
        rw [hTD0', map_shape_plainA, hdl]
        exact h1
      have hV₂ := hK₂ _ hK2 hKj _ _ 0 [] zs zs' hV₁ (by exact congrArg some hTD0.symm) hw₁
      rw [plainArgsA_plainA _ _ hdl.symm, plainArgsA_plainA _ _ (hdl.trans hzl).symm] at hV₂
      have hht : ht ρ₀ (instLevel lsC d.snd) ≤ j :=
        Nat.le_trans (plainSort_ht_le hUT (huniv d (List.mem_append_right _ (List.mem_cons_self _ _))) hlsC) hj
      obtain ⟨_, hDrel⟩ := hK₃ _ hK3 (wkCtxA ρ Γ) _ _ hΓρ hV₂
      obtain ⟨heq, hva, hvb⟩ := (LRRelA_sort_elim' hDrel).1 j hht
      rw [← hD₁e, ← hD₁e']
      exact ⟨heq, hva, hvb⟩

/-- THE FIELD DATUM (`hFld`) at an application of a group's family to self-related arguments, at
    any height `j` above the family's sort: a plain field's domain after a field walk is valid at
    `j`, with the canonical relation (`plainDomA` on the walk's diagonal). -/
theorem famFldA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps is : List ExprA}
    (hps : ps.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps ++ is))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T : ExprA) (pre pre' : List ExprA)
      (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
      eqNList ls lsA → eqNListB n lsA lsC →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      LRTyA E I n ρ₀ j (wkCtxA ρ Γ) D
        (famRsA E I n ρ₀ j Γ ρ c lsC (fm.nparamsA + ksPre.length) (ps.map (wkExprA ρ) ++ pre)) := by
  intro ρ hρ c cm lsA lsC kinds ksPre ks T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlAC hTc hw
    hTD
  obtain ⟨_, ⟨R, hR⟩, _⟩ := plainDomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl
    hj hΓ hps hps hrel hρ hcm hk hfam hkinds hsp hlA hlAC (eqNListB_refl hlAC.2) hTc hTc
    (argsRelA_diag hEN (famRsA_refl_left hEN) hw) hTD hTD
  have hTfull : applyTelA (ps.map (wkExprA ρ) ++ pre) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (.pi D uD C vC) := by
    rw [applyTelA_append, hTc]; exact hTD
  rw [famRsA_eq hcm hTfull]
  exact LRTyA_rel_self hR

/-- THE INNER FIELD DATUM (`hFldI`) (R-NoFunRec-1 step 1 (1c-δ)): at an application of a group's family to
    self-related arguments, a function-recursive field's inner domain after a field walk and an inner
    walk is valid at `j`, with the canonical inner relation (`frecInnerDomA` on the diagonal). -/
theorem famFldIA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps is : List ExprA}
    (hps : ps.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps ++ is))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (jn : Nat) (T : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks →
      eqNList ls lsA → eqNListB n lsA lsC →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
        (u₁ : Level) (C₁ : ExprA) (v₁ : Level),
      ArgsRelPA (innerRelsA (famRsIA E I n ρ₀ j Γ) ρ c lsC (fm.nparamsA + ksPre.length)
        (ps.map (wkExprA ρ) ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' →
      applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
      LRTyA E I n ρ₀ j (wkCtxA ρ' (wkCtxA ρ Γ)) D₁
        (innerRelsA (famRsIA E I n ρ₀ j Γ) ρ c lsC (fm.nparamsA + ksPre.length)
          (ps.map (wkExprA ρ) ++ pre) ρ' zs.length zs) := by
  intro ρ hρ c cm lsA lsC kinds ksPre ks jn T pre pre' D uD C vC hcm hk hfam hkinds hsp hlA hlAC hTc hw
    hTD ρ' hρ' zs zs' D₁ u₁ C₁ v₁ hz hD₁
  have hTfull : applyTelA (ps.map (wkExprA ρ) ++ pre) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (.pi D uD C vC) := by
    rw [applyTelA_append, hTc]; exact hTD
  have hclC := liftA_instantiateLevelsA_closed (by
    obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam
    exact hgm ▸ gc.normA_getD_closed) lsC
  have hρc : WkOk₀A E I n (WkSpecA.comp ρ ρ') Γ := wkOk₀A_comp_ext hρ hρ'
  have hTc_c : applyTelA (ps.map (wkExprA (WkSpecA.comp ρ ρ'))) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (wkExprA ρ' T) := by
    rw [← map_wkExprA_comp, applyTelA_wk_closed ρ' _ hclC, hTc]; rfl
  have hw_c := argsRelA_famRsA_wk hE hI hNC hρ' (fun cm' hm' =>
    (Option.some.inj (hm'.symm.trans hcm)).symm ▸ (by
      obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam
      exact hgm ▸ gc.normA_getD_closed)) hw
  rw [map_wkExprA_comp] at hw_c
  have hTD_c : applyTelA (pre.map (wkExprA ρ')) (wkExprA ρ' T) =
      some (.pi (wkExprA ρ' D) uD (wkExprA (WkSpecA.ub ρ') C) vC) := by
    rw [applyTelA_wk, hTD, Option.map_some', wkExprA_pi_ub]
  have hz_c : ArgsRelKA E I n ρ₀ j (wkCtxA (WkSpecA.comp ρ ρ') Γ) (wkExprA ρ' D) zs zs := by
    rw [wkCtxA_comp]
    exact argsRelKA_refl_left hEN (argsRelKA_of_innerRelsA hE hNC hcm (by obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam; exact hgm ▸ gc.normA_getD_closed) hTfull hz rfl)
  obtain ⟨_, ⟨R, hR⟩, _⟩ := frecInnerDomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl
    hj hΓ hps hps hrel (ρ := WkSpecA.comp ρ ρ') hρc hcm hk hfam hkinds hsp hlA hlAC
    (eqNListB_refl hlAC.2) hTc_c hTc_c (argsRelA_diag hEN (famRsA_refl_left hEN) hw_c) hTD_c hTD_c hz_c hD₁ hD₁
  rw [innerRelsA_famRsIA hE hcm (by obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam; exact hgm ▸ gc.normA_getD_closed) hTfull hD₁, ← wkCtxA_comp]
  exact LRTyA_rel_self hR

/-- THE FIELD EQUALITY DATUM (`hFldeq`): the plain domains at two `=ₙ` level lists after the walk's
    two sides are equal at `j` (`plainDomA`). -/
theorem famFldeqA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps is : List ExprA}
    (hps : ps.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps ++ is))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
      eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      applyTelA pre' T' = some (.pi D' uD' C' vC') →
      LREqA E I n ρ₀ j (wkCtxA ρ Γ) D D' :=
  fun _ρ hρ _c _cm _lsA _lsC _lsC' _kinds _ksPre _ks _T _T' _pre _pre' _D _uD _C _vC _D' _uD' _C' _vC' hcm hk hfam
      hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' =>
    (plainDomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps hrel hρ
      hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD').1

/-- THE INNER FIELD EQUALITY DATUM (`hFldIeq`) (R-NoFunRec-1 step 1 (1c-δ)): the inner domains at two
    `=ₙ` level lists after the walks' two sides are equal at `j` (`frecInnerDomA`). -/
theorem famFldIeqA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps is : List ExprA}
    (hps : ps.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps ++ is))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (jn : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks →
      eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      applyTelA pre' T' = some (.pi D' uD' C' vC') →
      ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
        (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
      ArgsRelPA (innerRelsA (famRsIA E I n ρ₀ j Γ) ρ c lsC (fm.nparamsA + ksPre.length)
        (ps.map (wkExprA ρ) ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' →
      applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
      applyTelA zs' (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
      LREqA E I n ρ₀ j (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁' := by
  intro ρ hρ c cm lsA lsC lsC' kinds ksPre ks jn T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds
    hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' ρ' hρ' zs zs' D₁ u₁ C₁ v₁ D₁' u₁' C₁' v₁' hz hD₁ hD₁'
  have hTfull : applyTelA (ps.map (wkExprA ρ) ++ pre) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (.pi D uD C vC) := by
    rw [applyTelA_append, hTc]; exact hTD
  have hclC := liftA_instantiateLevelsA_closed (by
    obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam
    exact hgm ▸ gc.normA_getD_closed) lsC
  have hclC' := liftA_instantiateLevelsA_closed (by
    obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam
    exact hgm ▸ gc.normA_getD_closed) lsC'
  have hρc : WkOk₀A E I n (WkSpecA.comp ρ ρ') Γ := wkOk₀A_comp_ext hρ hρ'
  have hTc_c : applyTelA (ps.map (wkExprA (WkSpecA.comp ρ ρ'))) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (wkExprA ρ' T) := by
    rw [← map_wkExprA_comp, applyTelA_wk_closed ρ' _ hclC, hTc]; rfl
  have hTc'_c : applyTelA (ps.map (wkExprA (WkSpecA.comp ρ ρ'))) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) =
      some (wkExprA ρ' T') := by
    rw [← map_wkExprA_comp, applyTelA_wk_closed ρ' _ hclC', hTc']; rfl
  have hw_c := argsRelA_famRsA_wk hE hI hNC hρ' (fun cm' hm' =>
    (Option.some.inj (hm'.symm.trans hcm)).symm ▸ (by
      obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam
      exact hgm ▸ gc.normA_getD_closed)) hw
  rw [map_wkExprA_comp] at hw_c
  have hTD_c : applyTelA (pre.map (wkExprA ρ')) (wkExprA ρ' T) =
      some (.pi (wkExprA ρ' D) uD (wkExprA (WkSpecA.ub ρ') C) vC) := by
    rw [applyTelA_wk, hTD, Option.map_some', wkExprA_pi_ub]
  have hTD'_c : applyTelA (pre'.map (wkExprA ρ')) (wkExprA ρ' T') =
      some (.pi (wkExprA ρ' D') uD' (wkExprA (WkSpecA.ub ρ') C') vC') := by
    rw [applyTelA_wk, hTD', Option.map_some', wkExprA_pi_ub]
  have hz_c : ArgsRelKA E I n ρ₀ j (wkCtxA (WkSpecA.comp ρ ρ') Γ) (wkExprA ρ' D) zs zs' := by
    rw [wkCtxA_comp]
    exact argsRelKA_of_innerRelsA hE hNC hcm (by obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam; exact hgm ▸ gc.normA_getD_closed) hTfull hz rfl
  have h := (frecInnerDomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl
    hj hΓ hps hps hrel (ρ := WkSpecA.comp ρ ρ') hρc hcm hk hfam hkinds hsp hlA hlAC hlCC hTc_c hTc'_c
    hw_c hTD_c hTD'_c hz_c hD₁ hD₁').1
  rw [← wkCtxA_comp]
  exact h

end FieldDatum

/-! ## (5) the index datum (`hFldF`) -/

theorem telCtxA_append (xs ys : List (ExprA × Level)) : telCtxA (xs ++ ys) = telCtxA ys ++ telCtxA xs := by
  simp only [telCtxA, List.map_append, List.reverse_append]

theorem telCtxA_cons_append (d : ExprA × Level) (ds : List (ExprA × Level)) (Γ : LCtxA) :
    telCtxA (d :: ds) ++ Γ = telCtxA ds ++ (.assumption d.1 :: Γ) := by
  simp only [telCtxA, List.map, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem piDomLevelsA_piTelA (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → piDomLevelsA (piTelA ds B w).1 = ds.map Prod.snd ++ piDomLevelsA B
  | [] => rfl
  | (D, u) :: ds => by
      simp only [piTelA, piDomLevelsA, List.map, piDomLevelsA_piTelA B w ds, List.cons_append]

theorem ht_instLevel (ρ₀ : Nat → Nat) (ls : List Level) (l : Level) :
    ht ρ₀ (instLevel ls l) = ht (fun i => ht ρ₀ ((ls[i]?).getD (.param i))) l := by
  apply Option.some.inj
  rw [← eval_total, ← eval_total, eval_instLevel]
  exact eval_congr_val (fun i => eval_total ρ₀ _) l

/-- a telescope over a sort, applied to a list and reaching a Π: the list stops inside the
    telescope, and the Π is the next domain under the substitution the list extends. -/
theorem applyTelA_piTelA_pi (l : Level) (w : Level) :
    (ms : List (ExprA × Level)) → (τ : SubstA) → (pre : List ExprA) → {D : ExprA} → {uD : Level} →
    {C : ExprA} → {vC : Level} → applyTelA pre (substA τ (piTelA ms (.sort l) w).1) = some (.pi D uD C vC) →
    ∃ msPre M msRest, ms = msPre ++ M :: msRest ∧ msPre.length = pre.length ∧
      D = substA (consListA pre τ) M.1 ∧ uD = M.2
  | [], _, [], _, _, _, _, h => by cases h
  | [], _, _ :: _, _, _, _, _, h => by cases h
  | (M, u) :: ms, τ, [], _, _, _, _, h => by
      injection h with h
      simp only [piTelA, substA_pi] at h
      injection h with hD hu
      exact ⟨[], (M, u), ms, rfl, rfl, hD.symm, hu.symm⟩
  | (M, u) :: ms, τ, x :: pre, _, _, _, _, h => by
      simp only [piTelA, substA_pi, applyTelA] at h
      rw [instantiate0A_substA_up] at h
      obtain ⟨msPre, M', msRest, e, hl, hD, hu⟩ := applyTelA_piTelA_pi l w ms (SubstA.cons x τ) pre h
      exact ⟨(M, u) :: msPre, M', msRest, by rw [e]; rfl, by simp only [List.length_cons, hl], hD, hu⟩

section IdxDatum
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a typed telescope's domain at a split, at its annotation, over the earlier domains. -/
theorem piTelA_domTy {a : Nat} (B : ExprA) (w : Level) :
    (pre : List (ExprA × Level)) → {D : ExprA} → {u : Level} → {post : List (ExprA × Level)} →
    {Γ : LCtxA} → {T : ExprA} → HasTyA E₀ I a Γ (piTelA (pre ++ (D, u) :: post) B w).1 T →
    Nonempty (HasTyA E₀ I a (telCtxA pre ++ Γ) D (.sort u))
  | [], D, u, post, _, _, h => by
      have hpi : HasTyA E₀ I a _ (.pi D u (piTelA post B w).1 (piTelA post B w).2) _ := h
      exact (hasTyA_pi_inv hpi).1
  | (D', u') :: pre, _, _, post, Γ, _, h => by
      have hpi : HasTyA E₀ I a Γ (.pi D' u' (piTelA (pre ++ _ :: post) B w).1
        (piTelA (pre ++ _ :: post) B w).2) _ := h
      obtain ⟨_, ⟨hC⟩⟩ := hasTyA_pi_inv hpi
      have ih := piTelA_domTy B w pre (Γ := .assumption D' :: Γ) hC
      rw [telCtxA_cons_append]
      exact ih

/-- a typed telescope's prefix is a well-formed context. -/
theorem piTelA_prefixCtx {a : Nat} (B : ExprA) (w : Level) (pre post : List (ExprA × Level))
    {Γ : LCtxA} (hΓ : CtxWfA E₀ I a Γ) {T : ExprA} (h : HasTyA E₀ I a Γ (piTelA (pre ++ post) B w).1 T) :
    Nonempty (CtxWfA E₀ I a (telCtxA pre ++ Γ)) := by
  rw [piTelA_append] at h
  exact (ctxWfA_telA _ _ pre hΓ h).1

/-- a walk with the canonical index relation is a related list along the telescope it walks. -/
theorem argsRelPA_famRsFA_KA {j : Nat} {Γ : LCtxA} {fm : CheckedMemberA} {ρ : WkSpecA}
    {lsF : List Level} :
    {i : Nat} → {prev : List ExprA} → {T : ExprA} → {pre pre' : List ExprA} →
    ArgsRelPA (famRsFA E I n ρ₀ j Γ fm ρ lsF) i prev T pre pre' →
    applyTelA prev (instantiateLevelsA lsF fm.mtypeA) = some T →
    ArgsRelKA E I n ρ₀ j (wkCtxA ρ Γ) T pre pre'
  | _, _, _, _, _, .nil _ _ _, _ => .nil _
  | _, _, _, _, _, .cons _ _ A u B v f f' fs fs' h hs, hT => by
      rw [famRsFA_eq hT] at h
      refine .cons A u B v f f' fs fs' h (argsRelPA_famRsFA_KA hs ?_)
      rw [applyTelA_append, hT]; rfl

/-- RELATED ARGUMENTS EXTEND A VALID SUBSTITUTION along a base-typed telescope over its context:
    each argument related at the domain its prefix reaches (at `j`, carried up), each domain's
    equality under the pair from its base derivation (`fundLevelsA`). -/
theorem telExtA (hfc : BaseFundConvA E₀ E I n ρ₀) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {a : Nat}
    {lsF : List Level} (hb : levelsBounded n lsF = true) (hl : lsF.length = a) {j : Nat} {Δ : LCtxA}
    (hΔ : Nonempty (CtxWfA E I n Δ)) {Γp : LCtxA} :
    (ms : List (ExprA × Level)) → CtxWfA E₀ I a (telCtxA ms ++ Γp) →
    ∃ K₀, ∀ K, K₀ ≤ K → j ≤ K → ∀ (κ κ' : SubstA) (B : ExprA) (w : Level) (pre pre' : List ExprA),
      pre.length = ms.length →
      ValidSubstA E I n ρ₀ K Δ κ κ' (instCtxA lsF Γp) →
      ArgsRelKA E I n ρ₀ j Δ (substA κ (piTelA (instDomsA lsF ms) B w).1) pre pre' →
      ValidSubstA E I n ρ₀ K Δ (consListA pre κ) (consListA pre' κ') (instCtxA lsF (telCtxA ms ++ Γp)) := by
  refine snocInduction (P := fun ms => CtxWfA E₀ I a (telCtxA ms ++ Γp) → ∃ K₀, ∀ K, K₀ ≤ K → j ≤ K →
      ∀ (κ κ' : SubstA) (B : ExprA) (w : Level) (pre pre' : List ExprA), pre.length = ms.length →
      ValidSubstA E I n ρ₀ K Δ κ κ' (instCtxA lsF Γp) →
      ArgsRelKA E I n ρ₀ j Δ (substA κ (piTelA (instDomsA lsF ms) B w).1) pre pre' →
      ValidSubstA E I n ρ₀ K Δ (consListA pre κ) (consListA pre' κ') (instCtxA lsF (telCtxA ms ++ Γp)))
    ?_ ?_
  · intro _
    refine ⟨0, fun K _ _ κ κ' B w pre pre' hlen hV hrel => ?_⟩
    have hl' := argsRelKA_length hrel
    cases pre with
    | cons _ _ => cases hlen
    | nil =>
        cases pre' with
        | cons _ _ => cases hl'
        | nil => exact hV
  · intro ms M ih hwf
    rw [telCtxA_snoc, List.cons_append] at hwf
    cases hwf with
    | assumption hΓ hA =>
        obtain ⟨K₁, hK₁⟩ := ih hΓ
        obtain ⟨K₂, hK₂⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hb hb hl hl (eqNList_refl lsF) hΓ hA
        refine ⟨max K₁ K₂, fun K hK hjK κ κ' B w pre pre' hlen hV hrel => ?_⟩
        have hl' := argsRelKA_length hrel
        rw [List.length_append, List.length_singleton] at hlen
        have hne : pre ≠ [] := fun h => by
          subst h
          exact absurd hlen (Nat.succ_ne_zero _).symm
        have hne' : pre' ≠ [] := fun h => by
          subst h
          rw [hl'] at hlen
          exact absurd hlen (Nat.succ_ne_zero _).symm
        obtain ⟨as₀, x, rfl⟩ := list_eq_dropLast_snoc pre hne
        obtain ⟨as₀', x', rfl⟩ := list_eq_dropLast_snoc pre' hne'
        rw [List.length_append, List.length_singleton] at hlen
        have hlen₀ : as₀.length = ms.length := Nat.succ.inj hlen
        rw [List.length_append, List.length_singleton, List.length_append, List.length_singleton] at hl'
        have hll₀ : as₀.length = as₀'.length := Nat.succ.inj hl'
        obtain ⟨M₁, u⟩ := M
        rw [instDomsA_snoc, piTelA_append] at hrel
        obtain ⟨T', hT', h₀, h₁⟩ := argsRelKA_append_inv hll₀ hrel
        have hlenI : as₀.length = (instDomsA lsF ms).length := by
          rw [hlen₀]; simp [instDomsA]
        have happ := applyTelA_piTelA
          (piTelA [(instantiateLevelsA lsF M₁, instLevel lsF u)] B w).1
          (piTelA [(instantiateLevelsA lsF M₁, instLevel lsF u)] B w).2
          (instDomsA lsF ms) as₀ hlenI κ
        rw [happ] at hT'
        cases hT'
        have hV₁ := hK₁ K (Nat.le_trans (Nat.le_max_left _ _) hK) hjK κ κ' _ _ as₀ as₀' hlen₀ hV h₀
        obtain ⟨_, hD⟩ := hK₂ K (Nat.le_trans (Nat.le_max_right _ _) hK) Δ _ _ hΔ hV₁
        have hDeq := (LRRelA_sort_elim hD).1
        cases h₁ with
        | cons _ _ _ _ _ _ _ _ ha _ =>
            rw [consListA_snoc, consListA_snoc, telCtxA_snoc, List.cons_append, instCtxA_cons]
            exact ValidSubstA_cons hEN hV₁ hDeq (LRRelA_mono hjK ha)

/-- an index binder's sort, at any `=ₙ` list, is below the family's at the carrier's: the
    small-index profile (`SmallIndexProfileA`), at the valuation the list induces. -/
theorem idxSort_ht_le (hS : SmallIndexProfileA E) {f : Nat} {fm : CheckedMemberA}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (fv : FamViewA fm)
    (hUT : UniformType fv.sort) {M : ExprA × Level} (hM : M ∈ fv.indices) {ls lsF : List Level}
    (hlsF : eqNList ls lsF) :
    ht ρ₀ (instLevel lsF M.2) ≤ ht ρ₀ (instLevel ls fv.sort) := by
  rw [ht_of_eqN (instLevel_eqNList hlsF fv.sort), ht_instLevel, ht_instLevel]
  have hmem : M.2 ∈ (piDomLevelsA fm.mtypeA).drop fm.nparamsA := by
    rw [fv.stored, piDomLevelsA_piTelA, List.map_append, ← fv.nparams]
    have h0 : piDomLevelsA (ExprA.sort fv.sort) = [] := rfl
    rw [h0, List.append_nil, ← List.length_map fv.params Prod.snd, List.drop_left]
    exact List.mem_map_of_mem Prod.snd hM
  exact hS f fm fv.sort hfm hcls fv.piBody M.2 hmem _ _ _ (eval_total _ M.2) (eval_total _ fv.sort)
    (by rw [ht_eq_evalTotal]; exact hUT _)

/-- the canonical index relation is self-related on the left. -/
theorem famRsFA_refl_left (hEN : EnvNormCtorTypeA E) {j : Nat} {Γ : LCtxA} {fm : CheckedMemberA}
    {ρ : WkSpecA} {lsF : List Level} :
    ∀ i prev a a', famRsFA E I n ρ₀ j Γ fm ρ lsF i prev a a' → famRsFA E I n ρ₀ j Γ fm ρ lsF i prev a a :=
  fun _ _ _ _ ⟨D, uD, C, vC, hT, hr⟩ => ⟨D, uD, C, vC, hT, LRRelA_refl_left hEN hr⟩

/-- an index walk's left list walks against itself. -/
theorem argsRelPA_diag (hEN : EnvNormCtorTypeA E) {R : Nat → List ExprA → ExprA → ExprA → Prop}
    (hR : ∀ i prev a a', R i prev a a' → R i prev a a) :
    {i : Nat} → {prev : List ExprA} → {T : ExprA} → {fs fs' : List ExprA} →
    ArgsRelPA R i prev T fs fs' → ArgsRelPA R i prev T fs fs
  | _, _, _, _, _, .nil _ _ _ => .nil _ _ _
  | _, _, _, _, _, .cons i prev A u B v f _ fs _ h hs =>
      .cons i prev A u B v f f fs fs (hR _ _ _ _ h) (argsRelPA_diag hEN hR hs)

/-- THE INDEX DOMAINS OF TWO INSTANCES. The family's telescope at parameters `ps` and at `ps'`
    (related along its type at the carrier's levels), at bounded `=ₙ` lists `lsF`, `lsF'`, an index
    walk `pre ~ pre'` with the canonical index relation reaching an index binder: the left domain
    (after `pre`, at `ps`, `lsF`) and the right one (after `pre'`, at `ps'`, `lsF'`) are equal at any
    height `j` above the family's sort, and valid there. The walk extends the parameters' valid
    pair (`telExtA`); the domain's base derivation across the two lists relates the instances at its
    sort (`fundLevelsA`), which is below the family's by the small-index profile. -/
theorem idxDomA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {ρ : WkSpecA} (hρ : WkOk₀A E I n ρ Γ) {lsF lsF' : List Level} {TF TF' : ExprA}
    {pre pre' : List ExprA} {D : ExprA} {uD : Level} {C : ExprA} {vC : Level}
    {D' : ExprA} {uD' : Level} {C' : ExprA} {vC' : Level}
    (hlF : eqNListB n ls lsF) (hlFF : eqNListB n lsF lsF')
    (hTF : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF fm.mtypeA) = some TF)
    (hTF' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsF' fm.mtypeA) = some TF')
    (hw : ArgsRelPA (famRsFA E I n ρ₀ j Γ fm ρ lsF) fm.nparamsA (ps.map (wkExprA ρ)) TF pre pre')
    (hTD : applyTelA pre TF = some (.pi D uD C vC)) (hTD' : applyTelA pre' TF' = some (.pi D' uD' C' vC')) :
    LREqA E I n ρ₀ j (wkCtxA ρ Γ) D D' ∧ (∃ R, LRTyA E I n ρ₀ j (wkCtxA ρ Γ) D R) ∧
      (∃ R, LRTyA E I n ρ₀ j (wkCtxA ρ Γ) D' R) := by
  have hlsF : eqNList ls lsF := hlF.1
  have hbF : levelsBounded n lsF = true := hlF.2
  have hbF' : levelsBounded n lsF' = true := hlFF.2
  have hlF' : lsF.length = fm.arity := (eqNListA_length hlsF).symm.trans hl
  have hlF'' : lsF'.length = fm.arity := (eqNListA_length (eqNListA_trans hlsF hlFF.1)).symm.trans hl
  have hΓρ := ctxWfA_wk₀ hΓ hρ
  have hpsρ : (ps.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps]
  have hpsρ' : (ps'.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps']
  have hwlen := argsRelPA_length hw
  have hwK := argsRelPA_famRsFA_KA hw hTF
  -- the index telescopes at the parameters
  have hTv := fv.applyTel_params lsF (ps.map (wkExprA ρ)) hpsρ
  rw [hTF] at hTv
  injection hTv with hTe
  subst hTe
  have hTv' := fv.applyTel_params lsF' (ps'.map (wkExprA ρ)) hpsρ'
  rw [hTF'] at hTv'
  injection hTv' with hTe'
  subst hTe'
  have hidx := congrArg Prod.fst (instantiateLevelsA_piTelA lsF (.sort fv.sort) (.succ fv.sort) fv.indices)
  have hidx' := congrArg Prod.fst (instantiateLevelsA_piTelA lsF' (.sort fv.sort) (.succ fv.sort) fv.indices)
  simp only at hidx hidx'
  rw [FamViewA.idxTelA, hidx] at hTD hwK
  rw [FamViewA.idxTelA, hidx'] at hTD'
  obtain ⟨msPre, M, msRest, hsplit, hlenPre, hDe, -⟩ := applyTelA_piTelA_pi _ _ _ _ pre hTD
  obtain ⟨msPre', M', msRest', hsplit', hlenPre', hDe', -⟩ := applyTelA_piTelA_pi _ _ _ _ pre' hTD'
  obtain ⟨iPre, Mi, iRest, hisplit, hiPre, hMi, -⟩ := map_eq_append_cons _ _ _ _ hsplit
  obtain ⟨iPre', Mi', iRest', hisplit', hiPre', hMi', -⟩ := map_eq_append_cons _ _ _ _ hsplit'
  have hlenI : pre.length = iPre.length := by rw [← hlenPre, ← hiPre, List.length_map]
  have hlenI' : pre'.length = iPre'.length := by rw [← hlenPre', ← hiPre', List.length_map]
  obtain ⟨_, hcons⟩ := List.append_inj (hisplit.symm.trans hisplit')
    (by rw [← hlenI, ← hlenI', hwlen])
  injection hcons with hMM _
  subst hMM
  rw [← hMi] at hDe
  rw [← hMi'] at hDe'
  have hMmem : Mi ∈ fv.indices := by
    rw [hisplit]; exact List.mem_append_right _ (List.mem_cons_self _ _)
  -- the domain's base typing and context
  have hT' := hT
  rw [fv.stored, hisplit, ← List.append_assoc] at hT'
  obtain ⟨hMty⟩ := piTelA_domTy (.sort fv.sort) (.succ fv.sort) (fv.params ++ iPre) (post := iRest) hT'
  obtain ⟨hΓM⟩ := piTelA_prefixCtx (.sort fv.sort) (.succ fv.sort) (fv.params ++ iPre) (Mi :: iRest) .nil hT'
  rw [telCtxA_append, List.append_nil] at hMty hΓM
  obtain ⟨K₁, hK₁⟩ := telExtA hfc hEN hNC hE₀ hI hR₀ hEL₀ hIL hbF hlF' (j := j) hΓρ (Γp := telCtxA fv.params)
    iPre hΓM
  obtain ⟨K₂, hK₂⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hbF hbF' hlF' hlF'' hlFF.1 hΓM hMty
  obtain ⟨K₃, hK₃⟩ := paramSubstA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL fv hcl hT hb hbF hl hlF' hlsF
  have hK1 : K₁ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hK2 : K₂ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hK3 : K₃ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hKk : k ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
  have hKj : j ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
  have hV₀ := hK₃ _ hK3 ps ps' is is' hKk hΓ hps hps' hrel ρ hρ
  rw [hisplit, instDomsA, List.map_append, ← instDomsA, ← instDomsA, piTelA_append] at hwK
  have hV₁ := hK₁ _ hK1 hKj _ _ _ _ pre pre' hlenI hV₀ hwK
  obtain ⟨_, hDrel⟩ := hK₂ _ hK2 (wkCtxA ρ Γ) _ _ hΓρ hV₁
  have hht : ht ρ₀ (instLevel lsF Mi.2) ≤ j :=
    Nat.le_trans (idxSort_ht_le hS hfm hcls fv hUT hMmem hlsF) hj
  obtain ⟨heq, hva, hvb⟩ := (LRRelA_sort_elim' hDrel).1 j hht
  rw [← hDe, ← hDe'] at heq
  rw [← hDe] at hva
  rw [← hDe'] at hvb
  exact ⟨heq, hva, hvb⟩

/-- THE INDEX DATUM (`hFldF`) at an application of a group's family to self-related arguments, at
    any height `j` above the family's sort: an index domain after an index walk is valid at `j`, with
    the canonical relation (`idxDomA` on the walk's diagonal). -/
theorem famFldFA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps is : List ExprA}
    (hps : ps.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps ++ is)) :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level),
      eqNListB n ls lsF →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF fm.mtypeA) = some TF →
      ArgsRelPA (famRsFA E I n ρ₀ j Γ fm ρ lsF) fm.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
      applyTelA pre TF = some (.pi D uD C vC) →
      LRTyA E I n ρ₀ j (wkCtxA ρ Γ) D
        (famRsFA E I n ρ₀ j Γ fm ρ lsF (fm.nparamsA + pre.length) (ps.map (wkExprA ρ) ++ pre)) := by
  intro ρ hρ lsF TF pre pre' D uD C vC hlF hTF hw hTD
  obtain ⟨_, ⟨R, hR⟩, _⟩ := idxDomA (fv := fv) hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb
    hl hj hΓ hps hps hrel hρ hlF (eqNListB_refl hlF.2) hTF hTF (argsRelPA_diag hEN (famRsFA_refl_left hEN) hw)
    hTD hTD
  have hTfull : applyTelA (ps.map (wkExprA ρ) ++ pre) (instantiateLevelsA lsF fm.mtypeA) =
      some (.pi D uD C vC) := by
    rw [applyTelA_append, hTF]; exact hTD
  rw [famRsFA_eq hTfull]
  exact LRTyA_rel_self hR

/-- THE INDEX EQUALITY DATUM (`hFldFeq`): the index domains at two `=ₙ` lists after the walk's two
    sides are equal at `j` (`idxDomA`). -/
theorem famFldFeqA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps is : List ExprA}
    (hps : ps.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps ++ is)) :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF lsF' : List Level) (TF TF' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF → eqNListB n lsF lsF' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF fm.mtypeA) = some TF →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF' fm.mtypeA) = some TF' →
      ArgsRelPA (famRsFA E I n ρ₀ j Γ fm ρ lsF) fm.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
      applyTelA pre TF = some (.pi D uD C vC) →
      applyTelA pre' TF' = some (.pi D' uD' C' vC') →
      LREqA E I n ρ₀ j (wkCtxA ρ Γ) D D' :=
  fun _ρ hρ _lsF _lsF' _TF _TF' _pre _pre' _D _uD _C _vC _D' _uD' _C' _vC' hlF hlFF hTF hTF' hw hTD hTD' =>
    (idxDomA (fv := fv) hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hps hrel
      hρ hlF hlFF hTF hTF' hw hTD hTD').1

/-- ARGUMENTS RELATED ALONG THE FAMILY'S INDEX TELESCOPE, at any height, are related with the
    canonical index relation at `j`, at a world and a bounded `=ₙ` list: each domain is valid at `j`
    by the index datum on the prefix walk, and the relation comes to `j` (`LRRelA_height`). -/
theorem idxArgsA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps is : List ExprA}
    (hps : ps.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps ++ is))
    {ρ : WkSpecA} (hρ : WkOk₀A E I n ρ Γ) {lsF : List Level} (hlF : eqNListB n ls lsF) {TF : ExprA}
    (hTF : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF fm.mtypeA) = some TF) :
    {T : ExprA} → {rest rest' : List ExprA} → {K : Nat} → ArgsRelKA E I n ρ₀ K (wkCtxA ρ Γ) T rest rest' →
    ∀ (p p' : List ExprA), applyTelA p TF = some T →
      ArgsRelPA (famRsFA E I n ρ₀ j Γ fm ρ lsF) fm.nparamsA (ps.map (wkExprA ρ)) TF p p' →
      ArgsRelPA (famRsFA E I n ρ₀ j Γ fm ρ lsF) (fm.nparamsA + p.length) (ps.map (wkExprA ρ) ++ p) T
        rest rest'
  | _, _, _, _, .nil _, _, _, _, _ => .nil _ _ _
  | _, _, _, _, .cons A u' B v f f' fs fs' h hs, p, p', hTp, hp => by
      have hv := famFldFA (fv := fv) hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ
        hps hrel ρ hρ lsF TF p p' A u' B v hlF hTF hp hTp
      have hTfull : applyTelA (ps.map (wkExprA ρ) ++ p) (instantiateLevelsA lsF fm.mtypeA) =
          some (.pi A u' B v) := by
        rw [applyTelA_append, hTF]; exact hTp
      rw [famRsFA_eq hTfull] at hv
      have hR : famRsFA E I n ρ₀ j Γ fm ρ lsF (fm.nparamsA + p.length) (ps.map (wkExprA ρ) ++ p) f f' := by
        rw [famRsFA_eq hTfull]; exact LRRelA_height ⟨_, hv⟩ h
      have hTp' : applyTelA (p ++ [f]) TF = some (instantiate0A f B) := by
        rw [applyTelA_append, hTp]; rfl
      have hp' := argsRelPA_snoc hp hTp hR
      have ih := idxArgsA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hrel hρ hlF
        hTF hs (p ++ [f]) (p' ++ [f']) hTp' hp'
      rw [List.length_append, List.length_singleton, ← Nat.add_assoc, ← List.append_assoc] at ih
      exact .cons _ _ A u' B v f f' fs fs' hR ih

/-- THE DIAGONAL INDEX DATUM (`hxsD`, and with two lists `EqKA.fam`'s `hxs`): the carrier's indices,
    related along its telescope at the outer height, are related with the canonical index relation at
    `j` (`idxArgsA` from the empty prefix, at the identity world and the carrier's levels). -/
theorem famXsA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is')) :
    ∀ (TF : ExprA), applyTelA ps (instantiateLevelsA ls fm.mtypeA) = some TF →
      ArgsRelPA (famRsFA E I n ρ₀ j Γ fm [] ls) fm.nparamsA ps TF is is' := by
  intro TF hTF
  obtain ⟨TF₀, hTF₀, _, hrest⟩ := argsRelKA_append_inv (hps.trans hps'.symm) hrel
  rw [hTF₀] at hTF
  injection hTF with hTe
  subst hTe
  have h := idxArgsA (fv := fv) hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps
    (argsRelKA_refl_left hEN hrel) (wkOk₀A_nil E I n Γ) (eqNListB_refl hb) (by rw [map_wkExprA_nil]; exact hTF₀)
    hrest [] [] rfl (.nil _ _ _)
  rw [List.length_nil, Nat.add_zero, List.append_nil, map_wkExprA_nil] at h
  exact h

end IdxDatum

/-! ## (6) spines; related lists from valid pairs and from typed lists -/

theorem piTelA_snd_isZero (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → isZero (piTelA ds B w).2 = isZero w
  | [] => rfl
  | (D, u) :: ds => by
      show isZero (.imax u (piTelA ds B w).2) = isZero w
      rw [isZero_imax, piTelA_snd_isZero B w ds]

/-- a telescope built over a non-zero codomain sort has no propositional layer. -/
theorem isPiTelA_piTelA (B : ExprA) (w : Level) (hw : isZero w = false) :
    (ds : List (ExprA × Level)) → IsPiTelA ds.length (piTelA ds B w).1
  | [] => trivial
  | (D, u) :: ds => ⟨by rw [piTelA_snd_isZero, hw], isPiTelA_piTelA B w hw ds⟩

section Spine
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- RELATED ARGUMENTS ALONG A VALID TELESCOPE MAKE CONVERTIBLE SPINES (the step of `telIntroA`,
    at the identity world): two heads typed and convertible at a valid Π-telescope with no
    propositional layer, applied to related lists, are typed at the left instance and convertible
    there; the instance reached is valid. -/
theorem spineConvA (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E) {k : Nat}
    {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E I n Γ)) :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKA E I n ρ₀ k Γ T as as' →
    ∀ (len : Nat) {R : ExprA → ExprA → Prop} {f g : ExprA}, as.length ≤ len → IsPiTelA len T →
      LRTyA E I n ρ₀ k Γ T R → HasTyA E I n Γ f T → HasTyA E I n Γ g T → ConvA E I n Γ f g T →
      ∀ C, applyTelA as T = some C →
      Nonempty (HasTyA E I n Γ (foldAppsA f as) C) ∧ Nonempty (HasTyA E I n Γ (foldAppsA g as') C) ∧
        Nonempty (ConvA E I n Γ (foldAppsA f as) (foldAppsA g as') C) ∧ ∃ R', LRTyA E I n ρ₀ k Γ C R'
  | _, _, _, .nil _, _, R, _, _, _, _, hT, hf, hg, hc, C, hC => by
      injection hC with hC
      subst hC
      exact ⟨⟨hf⟩, ⟨hg⟩, ⟨hc⟩, R, hT⟩
  | _, _, _, .cons D u C₀ v a a' _ _ hrel hs, len, R, f, g, hlen, hpi, hT, hf, hg, hc, C, hC => by
      cases len with
      | zero => exact absurd hlen (Nat.not_succ_le_zero _)
      | succ len =>
          obtain ⟨hv, hpi'⟩ := hpi
          have hnp : ¬ IsPropTy E I Γ (.pi D u C₀ v) := fun h => by
            rw [(isPropTy_pi_iff E I Γ D u C₀ v).1 h] at hv
            cases hv
          rw [LRTyA_eq] at hT
          obtain ⟨_, ⟨hTty⟩⟩ := tyKA_hasTy hT
          obtain ⟨RD, RC, hD, hCc, hCeq, _⟩ := tyKA_pi_inv hT hnp
          have hρ : WkOkA E I n [] Γ := ⟨trivial, hΓ⟩
          have hDρ : LRTyA E I n ρ₀ k Γ D (RD []) := by rw [LRTyA_eq]; exact hD [] hρ
          have hr : RD [] a a' := by
            obtain ⟨R'', hR'', h''⟩ := hrel
            rw [LRTyA_unique hR'' hDρ] at h''
            exact h''
          have hr' : RD [] a' a := by
            obtain ⟨R'', hR'', h''⟩ := LRRelA_symm hEN hrel
            rw [LRTyA_unique hR'' hDρ] at h''
            exact h''
          have hTa := hCc [] hρ a a' hr
          have hTa' := hCc [] hρ a' a hr'
          obtain ⟨w, ⟨hInst⟩⟩ := tyKA_hasTy hTa
          obtain ⟨w', ⟨hInst'⟩⟩ := tyKA_hasTy hTa'
          obtain ⟨_, ⟨hCty⟩⟩ := hasTyA_pi_inv hTty
          obtain ⟨⟨ha⟩, ⟨ha'⟩⟩ := LRRelA_hasTy hrel
          obtain ⟨hca⟩ := LRRelA_conv hrel
          have hfa : HasTyA E I n Γ (.app f a) (instantiate0A a C₀) :=
            .app _ _ _ _ _ _ _ w hCty hInst hf ha
          have hga' : HasTyA E I n Γ (.app g a') (instantiate0A a' C₀) :=
            .app _ _ _ _ _ _ _ w' hCty hInst' hg ha'
          obtain ⟨hceq⟩ := eqKA_tyConv (hCeq [] hρ a a' hr)
          have hga : HasTyA E I n Γ (.app g a') (instantiate0A a C₀) := hasTyA_of_tyConvA hga' hceq.symm
          have hcapp : ConvA E I n Γ (.app f a) (.app g a') (instantiate0A a C₀) :=
            .app _ _ _ _ _ _ _ _ _ hc hca hCty hga
          have hTa₀ : LRTyA E I n ρ₀ k Γ (instantiate0A a C₀) (RC [] a) := by rw [LRTyA_eq]; exact hTa
          exact spineConvA hE hI hEN hΓ hs len (Nat.le_of_succ_le_succ hlen)
            (isPiTelA_instantiate len 0 a _ hpi') hTa₀ hfa hga hcapp C hC

theorem ValidSubstA_uncons (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} {σ σ' : SubstA} {Γ : LCtxA}
    {A a a' : ExprA}
    (h : ValidSubstA E I n ρ₀ k Δ (SubstA.cons a σ) (SubstA.cons a' σ') (.assumption A :: Γ)) :
    ValidSubstA E I n ρ₀ k Δ σ σ' Γ ∧ LRRelA E I n ρ₀ k Δ (substA σ A) a a' := by
  refine ⟨⟨fun i B hB => ?_, fun i B v hB hv => ?_⟩, ?_⟩
  · have h1 := h.1 (i + 1) (liftA 0 1 B) (by rw [lookupTypeA_cons_succ, hB]; rfl)
    rw [substA_cons_liftA, substA_cons_liftA] at h1
    exact h1
  · have h1 := h.2 (i + 1) (liftA 0 1 B) (liftA 0 1 v) (by rw [lookupTypeA_cons_succ, hB]; rfl)
      (by rw [lookupValueA_cons_succ, hv]; rfl)
    rw [substA_cons_liftA, substA_cons_liftA, substA_cons_liftA] at h1
    exact h1
  · have h1 := (h.1 0 (liftA 0 1 A) (lookupTypeA_cons_zero_assumption A Γ)).2
    rw [substA_cons_liftA] at h1
    exact h1

theorem argsRelKA_append {k : Nat} {Γ : LCtxA} :
    {T : ExprA} → {as as' bs bs' : List ExprA} → {T' : ExprA} → ArgsRelKA E I n ρ₀ k Γ T as as' →
    applyTelA as T = some T' → ArgsRelKA E I n ρ₀ k Γ T' bs bs' →
    ArgsRelKA E I n ρ₀ k Γ T (as ++ bs) (as' ++ bs')
  | _, _, _, _, _, _, .nil _, hT, hb => by
      injection hT with hT
      subst hT
      exact hb
  | _, _, _, _, _, _, .cons A u B v f f' _ _ h hs, hT, hb =>
      .cons A u B v f f' _ _ h (argsRelKA_append hs hT hb)

/-- THE CONVERSE OF `validSubstA_of_tel`: a valid pair for a telescope's context, built from two
    lists, relates the lists along the telescope. -/
theorem argsRelKA_of_validSubst (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} :
    (ms : List (ExprA × Level)) → ∀ (B : ExprA) (w : Level) (as as' : List ExprA),
      as.length = ms.length → as'.length = ms.length →
      ValidSubstA E I n ρ₀ k Δ (consListA as SubstA.id) (consListA as' SubstA.id) (telCtxA ms) →
      ArgsRelKA E I n ρ₀ k Δ (piTelA ms B w).1 as as' := by
  refine snocInduction (P := fun ms => ∀ (B : ExprA) (w : Level) (as as' : List ExprA),
      as.length = ms.length → as'.length = ms.length →
      ValidSubstA E I n ρ₀ k Δ (consListA as SubstA.id) (consListA as' SubstA.id) (telCtxA ms) →
      ArgsRelKA E I n ρ₀ k Δ (piTelA ms B w).1 as as') ?_ ?_
  · intro B w as as' hl hl' _
    cases as with
    | cons _ _ => cases hl
    | nil =>
        cases as' with
        | cons _ _ => cases hl'
        | nil => exact .nil _
  · intro ms M ih B w as as' hl hl' hV
    rw [List.length_append, List.length_singleton] at hl hl'
    have hne : as ≠ [] := fun h => by subst h; exact absurd hl (Nat.succ_ne_zero _).symm
    have hne' : as' ≠ [] := fun h => by subst h; exact absurd hl' (Nat.succ_ne_zero _).symm
    obtain ⟨as₀, x, rfl⟩ := list_eq_dropLast_snoc as hne
    obtain ⟨as₀', x', rfl⟩ := list_eq_dropLast_snoc as' hne'
    rw [List.length_append, List.length_singleton] at hl hl'
    rw [consListA_snoc, consListA_snoc, telCtxA_snoc] at hV
    obtain ⟨hV₀, hx⟩ := ValidSubstA_uncons hEN hV
    have h₀ := ih (piTelA [M] B w).1 (piTelA [M] B w).2 as₀ as₀' (Nat.succ.inj hl) (Nat.succ.inj hl') hV₀
    rw [piTelA_append]
    have happ := applyTelA_piTelA (piTelA [M] B w).1 (piTelA [M] B w).2 ms as₀ (Nat.succ.inj hl) SubstA.id
    rw [substA_id] at happ
    refine argsRelKA_append h₀ happ ?_
    obtain ⟨M₁, u⟩ := M
    exact .cons _ _ _ _ _ _ _ _ hx (.nil _)

/-- THE PARAMETER CONVERSIONS OF A VALID PAIR (M2-f (6)): a valid pair for a telescope's context,
    built from two lists, makes the lists pointwise convertible along the telescope, each domain
    instance convertible with its right one — escape at each variable. -/
theorem parConvA_of_validSubst (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} :
    (ms : List (ExprA × Level)) → ∀ (B : ExprA) (w : Level) (as as' : List ExprA),
      as.length = ms.length → as'.length = ms.length →
      ValidSubstA E I n ρ₀ k Δ (consListA as SubstA.id) (consListA as' SubstA.id) (telCtxA ms) →
      ParConvA E I n Δ (piTelA ms B w).1 (piTelA ms B w).1 as as' := by
  refine snocInduction (P := fun ms => ∀ (B : ExprA) (w : Level) (as as' : List ExprA),
      as.length = ms.length → as'.length = ms.length →
      ValidSubstA E I n ρ₀ k Δ (consListA as SubstA.id) (consListA as' SubstA.id) (telCtxA ms) →
      ParConvA E I n Δ (piTelA ms B w).1 (piTelA ms B w).1 as as') ?_ ?_
  · intro B w as as' hl hl' _
    cases as with
    | cons _ _ => cases hl
    | nil =>
        cases as' with
        | cons _ _ => cases hl'
        | nil => exact .nil _ _
  · intro ms M ih B w as as' hl hl' hV
    rw [List.length_append, List.length_singleton] at hl hl'
    have hne : as ≠ [] := fun h => by subst h; exact absurd hl (Nat.succ_ne_zero _).symm
    have hne' : as' ≠ [] := fun h => by subst h; exact absurd hl' (Nat.succ_ne_zero _).symm
    obtain ⟨as₀, x, rfl⟩ := list_eq_dropLast_snoc as hne
    obtain ⟨as₀', x', rfl⟩ := list_eq_dropLast_snoc as' hne'
    rw [List.length_append, List.length_singleton] at hl hl'
    rw [consListA_snoc, consListA_snoc, telCtxA_snoc] at hV
    have hx := hV.1 0 (liftA 0 1 M.1) (lookupTypeA_cons_zero_assumption M.1 _)
    rw [substA_cons_liftA, substA_cons_liftA] at hx
    obtain ⟨hV₀, _⟩ := ValidSubstA_uncons hEN hV
    have h₀ := ih (piTelA [M] B w).1 (piTelA [M] B w).2 as₀ as₀' (Nat.succ.inj hl) (Nat.succ.inj hl') hV₀
    rw [piTelA_append]
    have happ := applyTelA_piTelA (piTelA [M] B w).1 (piTelA [M] B w).2 ms as₀ (Nat.succ.inj hl) SubstA.id
    have happ' := applyTelA_piTelA (piTelA [M] B w).1 (piTelA [M] B w).2 ms as₀' (Nat.succ.inj hl')
      SubstA.id
    rw [substA_id] at happ happ'
    refine parConvA_append h₀ happ happ' ?_
    obtain ⟨M₁, u⟩ := M
    exact .cons _ _ _ _ _ _ _ _ x x' [] [] (LRRelA_conv hx.2) (LREqA_tyConv hx.1) (.nil _ _)

/-- TYPED LISTS ARE RELATED under a valid pair, across two `=ₙ` lists: a list typed in the base
    along a telescope over a context relates, substituted on each side, along the substituted
    telescope (`fundLevelsA` at each element). -/
theorem argsTyA_relLv (hfc : BaseFundConvA E₀ E I n ρ₀) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {a : Nat}
    {lsC lsC' : List Level} (hb : levelsBounded n lsC = true) (hb' : levelsBounded n lsC' = true)
    (hl : lsC.length = a) (hl' : lsC'.length = a) (heq : eqNList lsC lsC') {Γp : LCtxA}
    (hΓp : CtxWfA E₀ I a Γp) :
    {T : ExprA} → {xs : List ExprA} → ArgsTyA E₀ I a Γp T xs →
    ∃ K₀, ∀ K, K₀ ≤ K → ∀ (Δ : LCtxA) (σ σ' : SubstA), Nonempty (CtxWfA E I n Δ) →
      ValidSubstA E I n ρ₀ K Δ σ σ' (instCtxA lsC Γp) →
      ArgsRelKA E I n ρ₀ K Δ (substA σ (instantiateLevelsA lsC T))
        (xs.map (fun x => substA σ (instantiateLevelsA lsC x)))
        (xs.map (fun x => substA σ' (instantiateLevelsA lsC' x)))
  | _, _, .nil _ => ⟨0, fun _ _ _ _ _ _ _ => .nil _⟩
  | _, _, .cons A u B v x xs hx tl => by
      obtain ⟨K₁, hK₁⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hb hb' hl hl' heq hΓp hx
      obtain ⟨K₂, hK₂⟩ := argsTyA_relLv hfc hEN hNC hE₀ hI hR₀ hEL₀ hIL hb hb' hl hl' heq hΓp tl
      refine ⟨max K₁ K₂, fun K hK Δ σ σ' hΔ hV => ?_⟩
      obtain ⟨_, hrel⟩ := hK₁ K (Nat.le_trans (Nat.le_max_left _ _) hK) Δ σ σ' hΔ hV
      have ih := hK₂ K (Nat.le_trans (Nat.le_max_right _ _) hK) Δ σ σ' hΔ hV
      rw [instantiateLevelsA_instantiate0A, substA_instantiate0A] at ih
      exact .cons _ _ _ _ _ _ _ _ hrel ih

end Spine

/-! ## (7) the recursive datum (`hFldRec`) and the cross results -/

theorem substA_consListA_liftA : (xs : List ExprA) → (τ : SubstA) → (e : ExprA) →
    substA (consListA xs τ) (liftA 0 xs.length e) = substA τ e
  | [], τ, e => by rw [List.length_nil, liftA_zero]; rfl
  | x :: xs, τ, e => by
      show substA (consListA xs (SubstA.cons x τ)) (liftA 0 (xs.length + 1) e) = substA τ e
      rw [show xs.length + 1 = 1 + xs.length from Nat.add_comm _ _,
        ← liftA_liftA_merge xs.length 1 0 0 (Nat.le_refl 0) (Nat.zero_le _) e,
        substA_consListA_liftA xs (SubstA.cons x τ) (liftA 0 1 e), substA_cons_liftA]

theorem plainIdxA_length : (fs : List FieldA) → (as : List ExprA) → as.length = fs.length → (j : Nat) →
    plainIdxA fs j = j + (plainArgsA fs as).length
  | [], [], _, _ => rfl
  | .plain _ _ :: fs, _ :: as, h, j => by
      simp only [plainIdxA, plainArgsA, List.length_cons]
      rw [plainIdxA_length fs as (Nat.succ.inj h) (j + 1)]
      omega
  | .drec _ :: fs, _ :: as, h, j => by
      simp only [plainIdxA, plainArgsA]
      exact plainIdxA_length fs as (Nat.succ.inj h) j
  | .frec _ _ _ _ :: fs, _ :: as, h, j => by
      simp only [plainIdxA, plainArgsA]
      exact plainIdxA_length fs as (Nat.succ.inj h) j
  | .drecD _ _ :: fs, _ :: as, h, j => by
      simp only [plainIdxA, plainArgsA]
      exact plainIdxA_length fs as (Nat.succ.inj h) j
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h

/-- substitution and level instantiation follow a telescope's application. -/
theorem applyTelA_substA_inst (ls : List Level) : (xs : List ExprA) → (σ : SubstA) → {T C : ExprA} →
    applyTelA xs T = some C →
    applyTelA (xs.map (fun x => substA σ (instantiateLevelsA ls x))) (substA σ (instantiateLevelsA ls T)) =
      some (substA σ (instantiateLevelsA ls C))
  | [], _, _, _, h => by
      injection h with h
      subst h
      rfl
  | x :: xs, σ, .pi A u B v, _, h => by
      show applyTelA (xs.map (fun x => substA σ (instantiateLevelsA ls x)))
        (instantiate0A (substA σ (instantiateLevelsA ls x)) (substA σ.up (instantiateLevelsA ls B))) = _
      rw [← substA_instantiate0A, ← instantiateLevelsA_instantiate0A]
      exact applyTelA_substA_inst ls xs σ h
  | _ :: _, _, .bvar _, _, h => by cases h
  | _ :: _, _, .sort _, _, h => by cases h
  | _ :: _, _, .const _ _, _, h => by cases h
  | _ :: _, _, .app _ _, _, h => by cases h
  | _ :: _, _, .lam _ _ _, _, h => by cases h
  | _ :: _, _, .letE _ _ _, _, h => by cases h
  | _ :: _, _, .lit _, _, h => by cases h

theorem isPiTelA_mono : (L L' : Nat) → (T : ExprA) → L' ≤ L → IsPiTelA L T → IsPiTelA L' T
  | _, 0, _, _, _ => trivial
  | 0, _ + 1, _, h, _ => absurd h (Nat.not_succ_le_zero _)
  | L + 1, L' + 1, .pi _ _ C _, h, ⟨hv, hC⟩ =>
      ⟨hv, isPiTelA_mono L L' C (Nat.le_of_succ_le_succ h) hC⟩
  | _ + 1, _ + 1, .bvar _, _, h => h.elim
  | _ + 1, _ + 1, .sort _, _, h => h.elim
  | _ + 1, _ + 1, .const _ _, _, h => h.elim
  | _ + 1, _ + 1, .app _ _, _, h => h.elim
  | _ + 1, _ + 1, .lam _ _ _, _, h => h.elim
  | _ + 1, _ + 1, .letE _ _ _, _, h => h.elim
  | _ + 1, _ + 1, .lit _, _, h => h.elim

/-- a context of assumptions only: the telescopes' and the plain fields' contexts. -/
def AsmCtxA : LCtxA → Prop
  | [] => True
  | .assumption _ :: Γ => AsmCtxA Γ
  | .letBinding _ _ :: _ => False

theorem asmCtxA_telCtxA (ds : List (ExprA × Level)) : AsmCtxA (telCtxA ds) := by
  refine snocInduction (P := fun ds => AsmCtxA (telCtxA ds)) trivial ?_ ds
  intro ds d ih
  rw [telCtxA_snoc]
  exact ih

theorem asmCtxA_plainCtx : (fs : List FieldA) → {Γ : LCtxA} → AsmCtxA Γ → AsmCtxA (plainCtxA fs Γ)
  | [], _, h => h
  | .plain D _ :: fs, Γ, h => asmCtxA_plainCtx fs (Γ := .assumption D :: Γ) h
  | .drec _ :: fs, _, h => asmCtxA_plainCtx fs h
  | .frec _ _ _ _ :: fs, _, h => asmCtxA_plainCtx fs h
  | .drecD _ _ :: fs, _, h => asmCtxA_plainCtx fs h

section RecDatum
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a typed list fills its telescope up to a sort. -/
theorem argsTyA_applyTel {a : Nat} {Γ : LCtxA} : {T : ExprA} → {xs : List ExprA} →
    ArgsTyA E₀ I a Γ T xs → ∃ l, applyTelA xs T = some (.sort l)
  | _, _, .nil l => ⟨l, rfl⟩
  | _, _, .cons _ _ _ _ _ _ _ tl => by
      obtain ⟨l, h⟩ := argsTyA_applyTel tl
      exact ⟨l, h⟩

/-- a related list along a substituted telescope over a sort is no longer than the telescope. -/
theorem argsRelKA_length_le {K : Nat} {Γ : LCtxA} (l w : Level) :
    (ds : List (ExprA × Level)) → (σ : SubstA) → {as as' : List ExprA} →
    ArgsRelKA E I n ρ₀ K Γ (substA σ (piTelA ds (.sort l) w).1) as as' → as.length ≤ ds.length
  | [], _, _, _, h => by
      cases h with
      | nil _ => exact Nat.le_refl 0
  | (_, _) :: ds, σ, _, _, h => by
      cases h with
      | nil _ => exact Nat.zero_le _
      | cons _ _ _ _ x _ _ _ _ hs =>
          rw [instantiate0A_substA_up] at hs
          exact Nat.succ_le_succ (argsRelKA_length_le l w ds (SubstA.cons x σ) hs)

/-- valid pairs compose: the images' relations by transitivity, carried to the first pair's types. -/
theorem validSubstA_trans (hEN : EnvNormCtorTypeA E) {k : Nat} {Δ : LCtxA} {σ₁ σ₂ σ₃ : SubstA}
    {Γ : LCtxA}
    (h₁ : ValidSubstA E I n ρ₀ k Δ σ₁ σ₂ Γ) (h₂ : ValidSubstA E I n ρ₀ k Δ σ₂ σ₃ Γ) :
    ValidSubstA E I n ρ₀ k Δ σ₁ σ₃ Γ := by
  refine ⟨fun i A hA => ?_, fun i A v hA hv => ?_⟩
  · obtain ⟨he₁, hr₁⟩ := h₁.1 i A hA
    obtain ⟨he₂, hr₂⟩ := h₂.1 i A hA
    exact ⟨LREqA_trans hEN he₁ he₂, LRRelA_trans hEN hr₁ (LRRelA_transport' hEN (LREqA_symm hEN he₁) hr₂)⟩
  · obtain ⟨he₁, _⟩ := h₁.1 i A hA
    obtain ⟨hv1, hv2⟩ := h₁.2 i A v hA hv
    obtain ⟨_, hw2⟩ := h₂.2 i A v hA hv
    exact ⟨hv1, LRRelA_trans hEN hv2 (LRRelA_transport' hEN (LREqA_symm hEN he₁) hw2)⟩

/-- A VALID PAIR AT ANOTHER `=ₙ` LEVEL LIST: a pair valid for a base-well-formed context of
    assumptions instantiated at `ls` is valid for it at `ls'`, each image carried along its type's
    two instances (`fundLevelsA` at the left images, `LRRelA_transport'`). -/
theorem validSubstA_lvCtx (hfc : BaseFundConvA E₀ E I n ρ₀) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {a : Nat}
    {ls ls' : List Level} (hb : levelsBounded n ls = true) (hb' : levelsBounded n ls' = true)
    (hl : ls.length = a) (hl' : ls'.length = a) (heq : eqNList ls ls') :
    {Γ : LCtxA} → CtxWfA E₀ I a Γ → AsmCtxA Γ →
    ∃ K₀, ∀ K, K₀ ≤ K → ∀ (Δ : LCtxA) (σ σ' : SubstA), Nonempty (CtxWfA E I n Δ) →
      ValidSubstA E I n ρ₀ K Δ σ σ' (instCtxA ls Γ) → ValidSubstA E I n ρ₀ K Δ σ σ' (instCtxA ls' Γ)
  | _, .nil, _ => ⟨0, fun _ _ _ _ _ _ h => h⟩
  | _, .assumption (Γ := Γ) (A := A) hΓ hA, hasm => by
      obtain ⟨K₁, hK₁⟩ := validSubstA_lvCtx hfc hEN hNC hE₀ hI hR₀ hEL₀ hIL hb hb' hl hl' heq hΓ hasm
      obtain ⟨K₂, hK₂⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hb hb' hl hl' heq hΓ hA
      refine ⟨max K₁ K₂, fun K hK Δ σ σ' hΔ hV => ?_⟩
      obtain ⟨x, τ, rfl⟩ : ∃ x τ, σ = SubstA.cons x τ :=
        ⟨σ 0, fun i => σ (i + 1), funext fun i => by cases i <;> rfl⟩
      obtain ⟨x', τ', rfl⟩ : ∃ x τ, σ' = SubstA.cons x τ :=
        ⟨σ' 0, fun i => σ' (i + 1), funext fun i => by cases i <;> rfl⟩
      change ValidSubstA E I n ρ₀ K Δ (SubstA.cons x τ) (SubstA.cons x' τ')
        (.assumption (instantiateLevelsA ls A) :: instCtxA ls Γ) at hV
      change ValidSubstA E I n ρ₀ K Δ (SubstA.cons x τ) (SubstA.cons x' τ')
        (.assumption (instantiateLevelsA ls' A) :: instCtxA ls' Γ)
      obtain ⟨hV₀, hx⟩ := ValidSubstA_uncons hEN hV
      have hV₁ := hK₁ K (Nat.le_trans (Nat.le_max_left _ _) hK) Δ τ τ' hΔ hV₀
      obtain ⟨_, h1⟩ := hK₂ K (Nat.le_trans (Nat.le_max_right _ _) hK) Δ τ τ hΔ (ValidSubstA_refl_left hEN hV₀)
      obtain ⟨_, h2⟩ := hK₂ K (Nat.le_trans (Nat.le_max_right _ _) hK) Δ τ τ' hΔ hV₀
      have e1 := (LRRelA_sort_elim h1).1
      have e2 := (LRRelA_sort_elim h2).1
      exact ValidSubstA_cons hEN hV₁ (LREqA_trans hEN (LREqA_symm hEN e1) e2) (LRRelA_transport' hEN e1 hx)
  | _, .letBinding _ _ _, hasm => False.elim hasm

/-- THE FAMILY'S ARGUMENTS AT A SUBSTITUTED INDEX LIST. Under a valid pair whose parameter part is
    two parameter lists, an index list typed in the base along the family's index telescope gives,
    at two `=ₙ` lists, the indices related along the index telescope (`argsTyA_relLv`) and the two
    argument lists related along the family's type at the left list (the parameters by the pair,
    `argsRelKA_of_validSubst`). -/
theorem famAppArgsA (hfc : BaseFundConvA E₀ E I n ρ₀) (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E) (hE₀ : EnvClosedA E₀) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {fm : CheckedMemberA} (fv : FamViewA fm) {lsL lsR : List Level}
    (hbL : levelsBounded n lsL = true) (hbR : levelsBounded n lsR = true)
    (hlL : lsL.length = fm.arity) (hlR : lsR.length = fm.arity) (heq : eqNList lsL lsR)
    {Γp : LCtxA} (hΓp : CtxWfA E₀ I fm.arity Γp) {jc : Nat} {idx : List ExprA}
    (hidx : ArgsTyA E₀ I fm.arity Γp (liftA 0 jc fv.idxTelA) idx) :
    ∃ K₀, ∀ K, K₀ ≤ K → ∀ (Δ : LCtxA), Nonempty (CtxWfA E I n Δ) → ∀ (ps ps' xs xs' : List ExprA),
      ps.length = fm.nparamsA → ps'.length = fm.nparamsA → jc = xs.length →
      ValidSubstA E I n ρ₀ K Δ (consListA ps SubstA.id) (consListA ps' SubstA.id)
        (instCtxA lsL (telCtxA fv.params)) →
      ValidSubstA E I n ρ₀ K Δ (consListA xs (consListA ps SubstA.id))
        (consListA xs' (consListA ps' SubstA.id)) (instCtxA lsL Γp) →
      ArgsRelKA E I n ρ₀ K Δ (substA (consListA ps SubstA.id) (instantiateLevelsA lsL fv.idxTelA))
          (idx.map (fun x => substA (consListA xs (consListA ps SubstA.id)) (instantiateLevelsA lsL x)))
          (idx.map (fun x => substA (consListA xs' (consListA ps' SubstA.id)) (instantiateLevelsA lsR x))) ∧
      ArgsRelKA E I n ρ₀ K Δ (instantiateLevelsA lsL fm.mtypeA)
        (ps ++ idx.map (fun x => substA (consListA xs (consListA ps SubstA.id)) (instantiateLevelsA lsL x)))
        (ps' ++ idx.map (fun x => substA (consListA xs' (consListA ps' SubstA.id)) (instantiateLevelsA lsR x))) := by
  obtain ⟨K₂, hK₂⟩ := argsTyA_relLv hfc hEN hNC hE₀ hI hR₀ hEL₀ hIL hbL hbR hlL hlR heq hΓp hidx
  refine ⟨K₂, fun K hK Δ hΔ ps ps' xs xs' hps hps' hjc hV₀ hV₁ => ?_⟩
  have hrelI := hK₂ K hK Δ _ _ hΔ hV₁
  rw [instantiateLevelsA_liftA, hjc, substA_consListA_liftA] at hrelI
  have hTF₀ := fv.applyTel_params lsL ps hps
  have hV₀' := hV₀
  rw [← telCtxA_instDomsA] at hV₀'
  have hpar := argsRelKA_of_validSubst hEN (instDomsA lsL fv.params) (instantiateLevelsA lsL fv.idxTelA)
    (instLevel lsL (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2) ps ps'
    (by simp [instDomsA, hps, fv.nparams]) (by simp [instDomsA, hps', fv.nparams]) hV₀'
  rw [← fv.inst_split] at hpar
  exact ⟨hrelI, argsRelKA_append hpar hTF₀ hrelI⟩

/-- THE PARAMETER CONVERSIONS AT A FAMILY APPLICATION (M2-f (6), the `fam` clause's `hpar`): arguments
    related along the family's type give, at every world and every bounded list `=ₙ` the left, the two
    parameter lists pointwise convertible with the domain instances convertible — the parameters'
    valid pair (`paramSubstA`) read off at each variable. A conversion, so the height of the valid
    pair does not matter. -/
theorem famParConvA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) {fm : CheckedMemberA} (fv : FamViewA fm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is')) :
    ∀ ρ : WkSpecA, WkOk₀A E I n ρ Γ → ∀ lsX : List Level, eqNListB n ls lsX →
      ParConvA E I n (wkCtxA ρ Γ) (instantiateLevelsA lsX fm.mtypeA) (instantiateLevelsA lsX fm.mtypeA)
        (ps.map (wkExprA ρ)) (ps'.map (wkExprA ρ)) := by
  intro ρ hρ lsX hlX
  have hlXl : lsX.length = fm.arity := (eqNListA_length hlX.1).symm.trans hl
  obtain ⟨K₀, hK₀⟩ := paramSubstA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL fv hcl hT hb hlX.2 hl hlXl hlX.1
  have hV := hK₀ (max K₀ k) (Nat.le_max_left _ _) ps ps' is is' (Nat.le_max_right _ _) hΓ hps hps' hrel ρ hρ
  rw [← telCtxA_instDomsA] at hV
  have h := parConvA_of_validSubst hEN (instDomsA lsX fv.params) (instantiateLevelsA lsX fv.idxTelA)
    (instLevel lsX (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2) (ps.map (wkExprA ρ))
    (ps'.map (wkExprA ρ)) (by simp [instDomsA, hps, fv.nparams]) (by simp [instDomsA, hps', fv.nparams]) hV
  rwa [← fv.inst_split] at h

/-- THE FAMILY AT A SUBSTITUTED INDEX LIST, TWO INSTANCES. An index list typed in the base along the
    family's index telescope over a context of the parameters and plain fields, at two bounded `=ₙ`
    lists `lsL`, `lsR`, substituted by a valid pair whose parameter part is the two parameter lists:
    the family's two applications to the parameters and the substituted index lists are related as
    recursive domains — the indices related along the index telescope with the canonical index
    relation at `j` (`argsTyA_relLv`, `idxArgsA`), the applications convertible as types
    (`spineConvA` along the family's type, the heads by level irrelevance). The shared core of the
    recursive datum and of the results. -/
theorem famAppDomA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {ρ : WkSpecA} (hρ : WkOk₀A E I n ρ Γ) {lsL lsR : List Level}
    (hlL : eqNListB n ls lsL) (hLR : eqNListB n lsL lsR)
    {Γp : LCtxA} (hΓp : CtxWfA E₀ I fm.arity Γp) {jc : Nat} {idx : List ExprA}
    (hidx : ArgsTyA E₀ I fm.arity Γp (liftA 0 jc fv.idxTelA) idx) :
    ∃ K₀, ∀ K, K₀ ≤ K → ∀ (xs xs' : List ExprA), jc = xs.length →
      ValidSubstA E I n ρ₀ K (wkCtxA ρ Γ) (consListA (ps.map (wkExprA ρ)) SubstA.id)
        (consListA (ps'.map (wkExprA ρ)) SubstA.id) (instCtxA lsL (telCtxA fv.params)) →
      ValidSubstA E I n ρ₀ K (wkCtxA ρ Γ) (consListA xs (consListA (ps.map (wkExprA ρ)) SubstA.id))
        (consListA xs' (consListA (ps'.map (wkExprA ρ)) SubstA.id)) (instCtxA lsL Γp) →
      RecDomRelXA E I n (wkCtxA ρ Γ) f fm (famRsFA E I n ρ₀ j Γ fm ρ) ls (ps.map (wkExprA ρ))
        (ps'.map (wkExprA ρ))
        (foldAppsA (.const f lsL) (ps.map (wkExprA ρ) ++ (idx.map (instantiateLevelsA lsL)).map
          (substA (consListA xs (consListA (ps.map (wkExprA ρ)) SubstA.id)))))
        (foldAppsA (.const f lsR) (ps'.map (wkExprA ρ) ++ (idx.map (instantiateLevelsA lsR)).map
          (substA (consListA xs' (consListA (ps'.map (wkExprA ρ)) SubstA.id))))) := by
  have hlR : eqNList ls lsR := eqNListA_trans hlL.1 hLR.1
  have hlCL : lsL.length = fm.arity := (eqNListA_length hlL.1).symm.trans hl
  have hlCR : lsR.length = fm.arity := (eqNListA_length hlR).symm.trans hl
  have hbL : levelsBounded n lsL = true := hlL.2
  have hbR : levelsBounded n lsR = true := hLR.2
  have hΓρ := ctxWfA_wk₀ hΓ hρ
  have hpsρ : (ps.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps]
  have hpsρ' : (ps'.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps']
  obtain ⟨K₂, hK₂⟩ := famAppArgsA hfc hEN hNC hE₀ hI hR₀ hEL₀ hIL fv hbL hbR hlCL hlCR hLR.1 hΓp hidx
  obtain ⟨K₄, hK₄⟩ := fundLevelsA hfc hE₀ hI hR₀ hEL₀ hIL hbL hbR hlCL hlCR hLR.1 .nil hT
  refine ⟨max K₂ K₄, fun K hK xs xs' hjc hV₀ hV₁ => ?_⟩
  have hK2 : K₂ ≤ K := Nat.le_trans (Nat.le_max_left _ _) hK
  have hK4 : K₄ ≤ K := Nat.le_trans (Nat.le_max_right _ _) hK
  -- the index lists, related along the index telescope at the parameters
  obtain ⟨hrelI, hargs⟩ := hK₂ _ hK2 (wkCtxA ρ Γ) hΓρ _ _ _ _ hpsρ hpsρ' hjc hV₀ hV₁
  have hTF₀ := fv.applyTel_params lsL (ps.map (wkExprA ρ)) hpsρ
  have hTF₀' := fv.applyTel_params lsR (ps'.map (wkExprA ρ)) hpsρ'
  -- the family's type, at the two lists
  obtain ⟨_, hTrel⟩ := hK₄ _ hK4 (wkCtxA ρ Γ) SubstA.id SubstA.id hΓρ (ValidSubstA_nil _ _ _)
  rw [substA_id, substA_id, substA_id] at hTrel
  obtain ⟨_, ⟨RT, hRT⟩, _, ⟨hTty⟩, ⟨hTty'⟩, ⟨hTconv⟩⟩ := LRRelA_sort_elim hTrel
  have hf₁ : HasTyA E I n (wkCtxA ρ Γ) (.const f lsL) (instantiateLevelsA lsL fm.mtypeA) :=
    .const _ _ _ _ _ hfm hlCL hbL hTty
  have hf₂' : HasTyA E I n (wkCtxA ρ Γ) (.const f lsR) (instantiateLevelsA lsR fm.mtypeA) :=
    .const _ _ _ _ _ hfm hlCR hbR hTty'
  have hTc₂ : TyConvA E I n (wkCtxA ρ Γ) (instantiateLevelsA lsL fm.mtypeA)
      (instantiateLevelsA lsR fm.mtypeA) :=
    .of _ _ _ _ _ _ hTty (eqNA_refl _) hTty' (eqNA_refl _) hTconv
  have hf₂ := hasTyA_of_tyConvA hf₂' hTc₂.symm
  have hfc₁ : ConvA E I n (wkCtxA ρ Γ) (.const f lsL) (.const f lsR)
      (instantiateLevelsA lsL fm.mtypeA) :=
    .consts _ _ _ _ _ hfm hlCL hbL hbR hLR.1 hf₂
  -- the instance reached is a sort
  obtain ⟨l₀, hl₀⟩ := argsTyA_applyTel hidx
  have hsort := applyTelA_substA_inst lsL idx
    (consListA xs (consListA (ps.map (wkExprA ρ)) SubstA.id)) hl₀
  rw [instantiateLevelsA_liftA, hjc, substA_consListA_liftA] at hsort
  have hC₀ : applyTelA (ps.map (wkExprA ρ) ++
      idx.map (fun x => substA (consListA xs (consListA (ps.map (wkExprA ρ)) SubstA.id))
        (instantiateLevelsA lsL x))) (instantiateLevelsA lsL fm.mtypeA) =
      some (.sort (instLevel lsL l₀)) := by
    rw [applyTelA_append, hTF₀]; exact hsort
  -- no propositional layer, and the length
  have hidxT := congrArg Prod.fst (instantiateLevelsA_piTelA lsL (.sort fv.sort) (.succ fv.sort) fv.indices)
  simp only at hidxT
  have hlenI : (idx.map (fun x => substA (consListA xs
      (consListA (ps.map (wkExprA ρ)) SubstA.id)) (instantiateLevelsA lsL x))).length ≤
      (instDomsA lsL fv.indices).length := by
    have h2 := hrelI
    rw [FamViewA.idxTelA, hidxT] at h2
    exact argsRelKA_length_le _ _ _ _ h2
  have hTpi : instantiateLevelsA lsL fm.mtypeA =
      (piTelA (instDomsA lsL (fv.params ++ fv.indices)) (instantiateLevelsA lsL (.sort fv.sort))
        (instLevel lsL (.succ fv.sort))).1 := by
    rw [fv.stored]
    exact congrArg Prod.fst (instantiateLevelsA_piTelA lsL (.sort fv.sort) (.succ fv.sort) _)
  have hpiT : IsPiTelA (instDomsA lsL (fv.params ++ fv.indices)).length
      (instantiateLevelsA lsL fm.mtypeA) := by
    rw [hTpi]
    exact isPiTelA_piTelA (instantiateLevelsA lsL (.sort fv.sort)) (instLevel lsL (.succ fv.sort)) rfl _
  have hlenA : (ps.map (wkExprA ρ) ++ idx.map (fun x => substA (consListA xs
      (consListA (ps.map (wkExprA ρ)) SubstA.id)) (instantiateLevelsA lsL x))).length ≤
      (instDomsA lsL (fv.params ++ fv.indices)).length := by
    simp only [List.length_append, instDomsA, List.map_append, List.length_map] at hlenI ⊢
    rw [hps, ← fv.nparams]
    omega
  obtain ⟨⟨hDty⟩, ⟨hD'ty⟩, ⟨hDconv⟩, _⟩ := spineConvA hE hI hEN hΓρ hargs _ hlenA hpiT hRT hf₁ hf₂ hfc₁ _ hC₀
  have hidxRel := idxArgsA (fv := fv) hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ
    hps (argsRelKA_refl_left hEN hrel) hρ hlL hTF₀ hrelI [] [] rfl (.nil _ _ _)
  rw [List.length_nil, Nat.add_zero, List.append_nil] at hidxRel
  have e1 : (idx.map (instantiateLevelsA lsL)).map
      (substA (consListA xs (consListA (ps.map (wkExprA ρ)) SubstA.id))) =
      idx.map (fun x => substA (consListA xs (consListA (ps.map (wkExprA ρ)) SubstA.id))
        (instantiateLevelsA lsL x)) := by
    rw [List.map_map]; rfl
  have e2 : (idx.map (instantiateLevelsA lsR)).map
      (substA (consListA xs' (consListA (ps'.map (wkExprA ρ)) SubstA.id))) =
      idx.map (fun x => substA (consListA xs' (consListA (ps'.map (wkExprA ρ)) SubstA.id))
        (instantiateLevelsA lsR x)) := by
    rw [List.map_map]; rfl
  rw [e1, e2]
  exact ⟨lsL, lsR, _, _, _, _, rfl, rfl, hlL, hLR, hTF₀, hTF₀', hidxRel,
    ⟨.of _ _ _ _ _ _ hDty (eqNA_refl _) hD'ty (eqNA_refl _) hDconv⟩⟩

/-- THE RECURSIVE DOMAINS OF TWO INSTANCES. As `plainDomA`, a walk reaching a recursive field: the
    two domains are the family at `lsC` / `lsC'`, at the two parameter lists, at the field's index
    list substituted on each side by the walk's valid pair (`fieldWalkA`, `paramSubstA`), related as
    recursive domains (`famAppDomA`). -/
theorem recDomA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ρ : WkSpecA} (hρ : WkOk₀A E I n ρ Γ) {c : Nat}
    {cm : CheckedMemberA}
    {lsA lsC lsC' : List Level} {kinds ksPre ks : List FieldShape} {T T' : ExprA} {pre pre' : List ExprA}
    {D : ExprA} {uD : Level} {C : ExprA} {vC : Level} {D' : ExprA} {uD' : Level} {C' : ExprA}
    {vC' : Level}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hsp : kinds = ksPre ++ (FieldShape.recursive 0) :: ks)
    (hlA : eqNList ls lsA) (hlAC : eqNListB n lsA lsC) (hlCC : eqNListB n lsC lsC')
    (hTc : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hTc' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    (hw : ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) X F fm.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre')
    (hTD : applyTelA pre T = some (.pi D uD C vC)) (hTD' : applyTelA pre' T' = some (.pi D' uD' C' vC')) :
    RecDomRelXA E I n (wkCtxA ρ Γ) f fm (famRsFA E I n ρ₀ j Γ fm ρ) ls (ps.map (wkExprA ρ))
      (ps'.map (wkExprA ρ)) D D'  := by
  obtain ⟨gc, hgc, hgr, hgm⟩ := hcensus c cm hcm hk hfam
  subst hgr hgm
  have hlsC : eqNList ls lsC := eqNListA_trans hlA hlAC.1
  have hlsC' : eqNList ls lsC' := eqNListA_trans hlsC hlCC.1
  have hlC : lsC.length = fm.arity := (eqNListA_length hlsC).symm.trans hl
  have hlC' : lsC'.length = fm.arity := (eqNListA_length hlsC').symm.trans hl
  have hbC : levelsBounded n lsC = true := hlAC.2
  have hΓρ := ctxWfA_wk₀ hΓ hρ
  have hpsρ : (ps.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps]
  have hpsρ' : (ps'.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps']
  have hTv := gc.applyTel_params lsC hlC (ps.map (wkExprA ρ)) hpsρ
  rw [hTc] at hTv
  injection hTv with hTe
  subst hTe
  have hTv' := gc.applyTel_params lsC' hlC' (ps'.map (wkExprA ρ)) hpsρ'
  rw [hTc'] at hTv'
  injection hTv' with hTe'
  subst hTe'
  rw [gc.normA_getD] at hkinds
  rw [gc.view.shapes hfresh] at hkinds
  injection hkinds with hkinds
  rw [hsp] at hkinds
  obtain ⟨fsPre, F, fsRest, hfs, hpreK, hFK, -⟩ := map_eq_append_cons _ _ _ _ hkinds
  cases F with
  | plain _ _ => cases hFK
  | frec _ _ _ _ => cases hFK
  | drecD D₀ idx₀ =>
      have hty := gc.view.typed
      rw [hfs] at hty
      obtain ⟨hwf⟩ := fv.paramsCtxWf hT
      obtain ⟨K₁, hK₁⟩ := fieldWalkA (f := f) (s := instLevel lsC fv.sort) (pl := ps.map (wkExprA ρ))
        (j := j) (Γ := Γ) (ρ := ρ) (X := X) (F := F) hfc hE₀ hI hEN hR₀ hEL₀ hIL hbC hlC hcm hΓρ fsPre hty hwf
      have hdrop := FieldsTyA.drop fsPre hty
      have hΓp := ctxWfA_plainCtx fsPre hty hwf
      cases hdrop with
      | drecD _ _ _ _ _ _ hidx _ =>
          obtain ⟨K₂, hK₂⟩ := famAppDomA (fv := fv) hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT
            hb hl hj hΓ hps hps' hrel hρ ⟨hlsC, hbC⟩ hlCC hΓp hidx
          obtain ⟨K₃, hK₃⟩ := paramSubstA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL fv hcl hT hb hbC hl hlC hlsC
          have hK1 : K₁ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
          have hK2 : K₂ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
          have hK3 : K₃ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
          have hKk : k ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
          have hKj : j ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
          have hV₀ := hK₃ _ hK3 ps ps' is is' hKk hΓ hps hps' hrel ρ hρ
          rw [hfs] at hTc hw hTD hTD'
          rw [← hpreK] at hw
          have hV₁ := hK₁ _ hK1 hKj _ _ fm.nparamsA (ps.map (wkExprA ρ)) pre pre' hV₀ hTc hw
          have hlen : pre.length = fsPre.length := by
            rw [(argsRelA_length hw).1, List.length_map]
          have hlen' : pre'.length = fsPre.length := by
            rw [(argsRelA_length hw).2, List.length_map]
          have hpfx := applyTelA_ctorFieldsA_prefix f lsC (instLevel lsC fv.sort)
            (gc.view.res.map (instantiateLevelsA lsC))
            (((FieldA.drecD D₀ idx₀ :: fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
            ((fsPre.map FieldA.norm).map (FieldA.instLevels lsC)) pre (by rw [List.length_map, List.length_map, hlen])
            (ps.map (wkExprA ρ)) (consListA (ps.map (wkExprA ρ)) SubstA.id)
          rw [← List.map_append, ← List.map_append, plainArgsA_instLevels, plainArgsA_norm] at hpfx
          rw [hpfx] at hTD
          simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA] at hTD
          injection hTD with hTD
          injection hTD with hDe _
          have hpfx' := applyTelA_ctorFieldsA_prefix f lsC' (instLevel lsC' fv.sort)
            (gc.view.res.map (instantiateLevelsA lsC'))
            (((FieldA.drecD D₀ idx₀ :: fsRest).map FieldA.norm).map (FieldA.instLevels lsC'))
            ((fsPre.map FieldA.norm).map (FieldA.instLevels lsC')) pre' (by rw [List.length_map, List.length_map, hlen'])
            (ps'.map (wkExprA ρ)) (consListA (ps'.map (wkExprA ρ)) SubstA.id)
          rw [← List.map_append, ← List.map_append, plainArgsA_instLevels, plainArgsA_norm] at hpfx'
          rw [hpfx'] at hTD'
          simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA] at hTD'
          injection hTD' with hTD'
          injection hTD' with hDe' _
          subst hDe hDe'
          have hjc : plainIdxA fsPre 0 = (plainArgsA fsPre pre).length := by
            rw [plainIdxA_length fsPre pre hlen 0, Nat.zero_add]
          exact hK₂ _ hK2 _ _ hjc hV₀ hV₁
  | drec idx =>
      have hty := gc.view.typed
      rw [hfs] at hty
      obtain ⟨hwf⟩ := fv.paramsCtxWf hT
      obtain ⟨K₁, hK₁⟩ := fieldWalkA (f := f) (s := instLevel lsC fv.sort) (pl := ps.map (wkExprA ρ))
        (j := j) (Γ := Γ) (ρ := ρ) (X := X) (F := F) hfc hE₀ hI hEN hR₀ hEL₀ hIL hbC hlC hcm hΓρ fsPre hty hwf
      have hdrop := FieldsTyA.drop fsPre hty
      have hΓp := ctxWfA_plainCtx fsPre hty hwf
      cases hdrop with
      | drec _ _ _ _ _ hidx _ =>
          obtain ⟨K₂, hK₂⟩ := famAppDomA (fv := fv) hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT
            hb hl hj hΓ hps hps' hrel hρ ⟨hlsC, hbC⟩ hlCC hΓp hidx
          obtain ⟨K₃, hK₃⟩ := paramSubstA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL fv hcl hT hb hbC hl hlC hlsC
          have hK1 : K₁ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
          have hK2 : K₂ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
          have hK3 : K₃ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
          have hKk : k ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
          have hKj : j ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
            Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
          have hV₀ := hK₃ _ hK3 ps ps' is is' hKk hΓ hps hps' hrel ρ hρ
          rw [hfs] at hTc hw hTD hTD'
          rw [← hpreK] at hw
          have hV₁ := hK₁ _ hK1 hKj _ _ fm.nparamsA (ps.map (wkExprA ρ)) pre pre' hV₀ hTc hw
          have hlen : pre.length = fsPre.length := by
            rw [(argsRelA_length hw).1, List.length_map]
          have hlen' : pre'.length = fsPre.length := by
            rw [(argsRelA_length hw).2, List.length_map]
          have hpfx := applyTelA_ctorFieldsA_prefix f lsC (instLevel lsC fv.sort)
            (gc.view.res.map (instantiateLevelsA lsC)) (((FieldA.drec idx :: fsRest).map FieldA.norm).map (FieldA.instLevels lsC))
            ((fsPre.map FieldA.norm).map (FieldA.instLevels lsC)) pre (by rw [List.length_map, List.length_map, hlen])
            (ps.map (wkExprA ρ)) (consListA (ps.map (wkExprA ρ)) SubstA.id)
          rw [← List.map_append, ← List.map_append, plainArgsA_instLevels, plainArgsA_norm] at hpfx
          rw [hpfx] at hTD
          simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA] at hTD
          injection hTD with hTD
          injection hTD with hDe _
          have hpfx' := applyTelA_ctorFieldsA_prefix f lsC' (instLevel lsC' fv.sort)
            (gc.view.res.map (instantiateLevelsA lsC')) (((FieldA.drec idx :: fsRest).map FieldA.norm).map (FieldA.instLevels lsC'))
            ((fsPre.map FieldA.norm).map (FieldA.instLevels lsC')) pre' (by rw [List.length_map, List.length_map, hlen'])
            (ps'.map (wkExprA ρ)) (consListA (ps'.map (wkExprA ρ)) SubstA.id)
          rw [← List.map_append, ← List.map_append, plainArgsA_instLevels, plainArgsA_norm] at hpfx'
          rw [hpfx'] at hTD'
          simp only [List.map, FieldA.instLevels, FieldA.norm, ctorFieldsA] at hTD'
          injection hTD' with hTD'
          injection hTD' with hDe' _
          subst hDe hDe'
          have hjc : plainIdxA fsPre 0 = (plainArgsA fsPre pre).length := by
            rw [plainIdxA_length fsPre pre hlen 0, Nat.zero_add]
          exact hK₂ _ hK2 _ _ hjc hV₀ hV₁

/-- THE INNER CODOMAINS OF TWO INSTANCES (R-NoFunRec-1 step 1 (1c-δ)). As `recDomA`, a walk reaching a
    function-recursive field, then all its inner arguments: the two codomains are the family at the
    field's index list substituted on each side by the walks' valid pair, related as recursive domains
    (`famAppDomA`). -/
theorem frecInnerRecA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ρ : WkSpecA}
    (hρ : WkOk₀A E I n ρ Γ) {c : Nat} {cm : CheckedMemberA}
    {lsA lsC lsC' : List Level} {kinds ksPre ks : List FieldShape} {jn : Nat} {T T' : ExprA}
    {pre pre' : List ExprA} {D : ExprA} {uD : Level} {C : ExprA} {vC : Level} {D' : ExprA}
    {uD' : Level} {C' : ExprA} {vC' : Level}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hsp : kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    (hlA : eqNList ls lsA) (hlAC : eqNListB n lsA lsC) (hlCC : eqNListB n lsC lsC')
    (hTc : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hTc' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    (hw : ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) X F fm.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre')
    (hTD : applyTelA pre T = some (.pi D uD C vC)) (hTD' : applyTelA pre' T' = some (.pi D' uD' C' vC'))
    {zs zs' : List ExprA} {C₁ C₁' : ExprA}
    (hz : ArgsRelKA E I n ρ₀ j (wkCtxA ρ Γ) D zs zs') (hzn : zs.length = jn + 1)
    (hC₁ : applyTelA zs D = some C₁) (hC₁' : applyTelA zs' D' = some C₁') :
    RecDomRelXA E I n (wkCtxA ρ Γ) f fm (famRsFA E I n ρ₀ j Γ fm ρ) ls (ps.map (wkExprA ρ))
      (ps'.map (wkExprA ρ)) C₁ C₁' := by
  refine frecWalkA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hb hl hΓ hps hps' hrel hρ
    hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' ?_
  intro fsPre B uB Bs idx hBs hlen hlen' hdom hΓp huniv hDe hDe' _ ⟨K₁, hK₁⟩
  have hlsC : eqNList ls lsC := eqNListA_trans hlA hlAC.1
  have hlsC' : eqNList ls lsC' := eqNListA_trans hlsC hlCC.1
  have hlC : lsC.length = fm.arity := (eqNListA_length hlsC).symm.trans hl
  have hlC' : lsC'.length = fm.arity := (eqNListA_length hlsC').symm.trans hl
  have hbC : levelsBounded n lsC = true := hlAC.2
  have hΓρ := ctxWfA_wk₀ hΓ hρ
  have hzl : zs.length = zs'.length := argsRelKA_length hz
  have hdl : zs.length = ((B, uB) :: Bs).length := by rw [hzn, List.length_cons, hBs]
  have hdlI : (instDomsA lsC ((B, uB) :: Bs)).length = zs.length := by simp [instDomsA, hdl]
  have hdl' : zs'.length = ((B, uB) :: Bs).length := hzl.symm.trans hdl
  have hdlI' : (instDomsA lsC' ((B, uB) :: Bs)).length = zs'.length := by simp [instDomsA, hdl']
  have hap := applyTelA_ctorFieldsA_prefix f lsC (instLevel lsC fv.sort) (idx.map (instantiateLevelsA lsC))
    [] ((instDomsA lsC ((B, uB) :: Bs)).map plainA) zs
    (by rw [List.length_map, hdlI]) (ps.map (wkExprA ρ))
    (consListA (plainArgsA fsPre pre) (consListA (ps.map (wkExprA ρ)) SubstA.id))
  rw [List.append_nil, hDe, hC₁] at hap
  have hap' := applyTelA_ctorFieldsA_prefix f lsC' (instLevel lsC' fv.sort) (idx.map (instantiateLevelsA lsC'))
    [] ((instDomsA lsC' ((B, uB) :: Bs)).map plainA) zs'
    (by rw [List.length_map, hdlI']) (ps'.map (wkExprA ρ))
    (consListA (plainArgsA fsPre pre') (consListA (ps'.map (wkExprA ρ)) SubstA.id))
  rw [List.append_nil, hDe', hC₁'] at hap'
  have hC₁e := Option.some.inj hap
  have hC₁e' := Option.some.inj hap'
  rw [plainArgsA_plainA _ _ hdlI.symm] at hC₁e
  rw [plainArgsA_plainA _ _ hdlI'.symm] at hC₁e'
  simp only [ctorFieldsA] at hC₁e hC₁e'
  have hdom' : FieldsTyA E₀ I fm.arity (fun k => liftA 0 k fv.idxTelA)
      (plainCtxA fsPre (telCtxA fv.params)) (plainIdxA fsPre 0)
      (((B, uB) :: Bs).map plainA ++ []) idx := by
    rw [List.append_nil]; exact hdom
  have hTD0 : (ctorFieldsA f lsC (instLevel lsC fv.sort) (ps.map (wkExprA ρ))
      (consListA (plainArgsA fsPre pre) (consListA (ps.map (wkExprA ρ)) SubstA.id))
      (((((B, uB) :: Bs).map plainA ++ []).map FieldA.norm).map (FieldA.instLevels lsC))
      (idx.map (instantiateLevelsA lsC))).1 = D := by
    have hn : ((((B, uB) :: Bs).map plainA ++ []).map FieldA.norm) =
        ((B, uB) :: Bs).map plainA ++ [] := by
      rw [List.map_append, map_norm_plainA]; rfl
    rw [hn, List.append_nil, plainA_instLevels]; exact hDe
  have hdrop := FieldsTyA.drop (((B, uB) :: Bs).map plainA) hdom'
  have hΓq := ctxWfA_plainCtx (((B, uB) :: Bs).map plainA) hdom' hΓp
  cases hdrop with
  | nil _ _ _ hidx =>
      obtain ⟨K₂, hK₂⟩ := fieldWalkRelA (f := f) (s := instLevel lsC fv.sort) (pl := ps.map (wkExprA ρ))
        (j := j) (Δ := wkCtxA ρ Γ) (T0 := D) (R := innerRelAtA E I n ρ₀ j (wkCtxA ρ Γ) D)
        (X := fun _ _ _ => True) (F := fun _ _ _ _ _ _ => True) hfc hE₀ hI hEN hR₀ hEL₀ hIL hbC hlC
        (fun _ prev x x' D₂ u₂ C₂ v₂ hT hr => by
          obtain ⟨D₃, u₃, C₃, v₃, hT', hr'⟩ := hr
          rw [hT] at hT'
          cases Option.some.inj hT'
          exact hr')
        hΓρ (((B, uB) :: Bs).map plainA) hdom' hΓp
      obtain ⟨K₃, hK₃⟩ := famAppDomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ
        hps hps' hrel hρ ⟨hlsC, hbC⟩ hlCC hΓq hidx
      have hK1 : K₁ ≤ max (max K₁ K₂) (max K₃ (max k j)) := by omega
      have hK2 : K₂ ≤ max (max K₁ K₂) (max K₃ (max k j)) := by omega
      have hK3 : K₃ ≤ max (max K₁ K₂) (max K₃ (max k j)) := by omega
      have hKk : k ≤ max (max K₁ K₂) (max K₃ (max k j)) := by omega
      have hKj : j ≤ max (max K₁ K₂) (max K₃ (max k j)) := by omega
      obtain ⟨hV₀, hV₁⟩ := hK₁ _ hK1 hKj hKk
      have hnorm₀ : (((B, uB) :: Bs).map plainA ++ []).map FieldA.norm =
          ((B, uB) :: Bs).map plainA ++ [] := by
        rw [List.map_append, map_norm_plainA]; rfl
      have hw₁ : ArgsRelA (innerRelAtA E I n ρ₀ j (wkCtxA ρ Γ) D) (fun _ _ _ => True)
          (fun _ _ _ _ _ _ => True) 0 []
          (ctorFieldsA f lsC (instLevel lsC fv.sort) (ps.map (wkExprA ρ))
            (consListA (plainArgsA fsPre pre) (consListA (ps.map (wkExprA ρ)) SubstA.id))
            (((((B, uB) :: Bs).map plainA ++ []).map FieldA.norm).map (FieldA.instLevels lsC))
            (idx.map (instantiateLevelsA lsC))).1
          ((((B, uB) :: Bs).map plainA).map FieldA.shape) zs zs' := by
        rw [hnorm₀]
        have h1 := argsRelA_of_argsRelKA hEN (X := fun _ _ _ => True) (F := fun _ _ _ _ _ _ => True)
          (i := 0) (prev := []) hz rfl
        rw [List.map_const'] at h1
        have hTD0' : (ctorFieldsA f lsC (instLevel lsC fv.sort) (ps.map (wkExprA ρ))
            (consListA (plainArgsA fsPre pre) (consListA (ps.map (wkExprA ρ)) SubstA.id))
            ((((B, uB) :: Bs).map plainA ++ []).map (FieldA.instLevels lsC))
            (idx.map (instantiateLevelsA lsC))).1 = D := by
          rw [hnorm₀] at hTD0; exact hTD0
        rw [hTD0', map_shape_plainA, hdl.symm]
        exact h1
      have hV₂ := hK₂ _ hK2 hKj _ _ 0 [] zs zs' hV₁ (by exact congrArg some hTD0.symm) hw₁
      rw [plainArgsA_plainA _ _ hdl, plainArgsA_plainA _ _ hdl'] at hV₂
      have hjc : plainIdxA (((B, uB) :: Bs).map plainA) (plainIdxA fsPre 0) =
          (plainArgsA fsPre pre ++ zs).length := by
        rw [plainIdxA_plainA, plainIdxA_length fsPre pre hlen 0, List.length_append, hdl]
        omega
      have hV₂' : ValidSubstA E I n ρ₀ (max (max K₁ K₂) (max K₃ (max k j))) (wkCtxA ρ Γ)
          (consListA (plainArgsA fsPre pre ++ zs) (consListA (ps.map (wkExprA ρ)) SubstA.id))
          (consListA (plainArgsA fsPre pre' ++ zs') (consListA (ps'.map (wkExprA ρ)) SubstA.id))
          (instCtxA lsC (plainCtxA (((B, uB) :: Bs).map plainA) (plainCtxA fsPre (telCtxA fv.params)))) := by
        rw [consListA_append, consListA_append]; exact hV₂
      have hfin := hK₃ _ hK3 (plainArgsA fsPre pre ++ zs) (plainArgsA fsPre pre' ++ zs') hjc hV₀ hV₂'
      rw [← consListA_append] at hC₁e hC₁e'
      rw [hC₁e, hC₁e']
      exact hfin

/-- THE RESULTS OF TWO INSTANCES. As `recDomA`, a walk over all the fields: the two results are the
    family at the constructor's result indices substituted on each side by the walk's valid pair,
    related as recursive domains (`famAppDomA` at the fields' end). -/
theorem resDomA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ρ : WkSpecA} (hρ : WkOk₀A E I n ρ Γ) {c : Nat}
    {cm : CheckedMemberA}
    {lsA lsC lsC' : List Level} {kinds : List FieldShape} {T T' : ExprA} {pre pre' : List ExprA}
    {R R' : ExprA}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hlA : eqNList ls lsA) (hlAC : eqNListB n lsA lsC) (hlCC : eqNListB n lsC lsC')
    (hTc : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hTc' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    (hw : ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) X F fm.nparamsA (ps.map (wkExprA ρ)) T kinds pre pre')
    (hTD : applyTelA pre T = some R) (hTD' : applyTelA pre' T' = some R') :
    RecDomRelXA E I n (wkCtxA ρ Γ) f fm (famRsFA E I n ρ₀ j Γ fm ρ) ls (ps.map (wkExprA ρ))
      (ps'.map (wkExprA ρ)) R R' := by
  obtain ⟨gc, hgc, hgr, hgm⟩ := hcensus c cm hcm hk hfam
  subst hgr hgm
  have hlsC : eqNList ls lsC := eqNListA_trans hlA hlAC.1
  have hlsC' : eqNList ls lsC' := eqNListA_trans hlsC hlCC.1
  have hlC : lsC.length = fm.arity := (eqNListA_length hlsC).symm.trans hl
  have hlC' : lsC'.length = fm.arity := (eqNListA_length hlsC').symm.trans hl
  have hbC : levelsBounded n lsC = true := hlAC.2
  have hΓρ := ctxWfA_wk₀ hΓ hρ
  have hpsρ : (ps.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps]
  have hpsρ' : (ps'.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps']
  have hTv := gc.applyTel_params lsC hlC (ps.map (wkExprA ρ)) hpsρ
  rw [hTc] at hTv
  injection hTv with hTe
  subst hTe
  have hTv' := gc.applyTel_params lsC' hlC' (ps'.map (wkExprA ρ)) hpsρ'
  rw [hTc'] at hTv'
  injection hTv' with hTe'
  subst hTe'
  rw [gc.normA_getD] at hkinds
  rw [gc.view.shapes hfresh] at hkinds
  injection hkinds with hkinds
  rw [← hkinds] at hw
  have hfs : gc.view.fields = gc.view.fields ++ [] := (List.append_nil _).symm
  have hty := gc.view.typed
  rw [hfs] at hty
  obtain ⟨hwf⟩ := fv.paramsCtxWf hT
  obtain ⟨K₁, hK₁⟩ := fieldWalkA (f := f) (s := instLevel lsC fv.sort) (pl := ps.map (wkExprA ρ))
    (j := j) (Γ := Γ) (ρ := ρ) (X := X) (F := F) hfc hE₀ hI hEN hR₀ hEL₀ hIL hbC hlC hcm hΓρ gc.view.fields hty hwf
  have hdrop := FieldsTyA.drop gc.view.fields hty
  have hΓp := ctxWfA_plainCtx gc.view.fields hty hwf
  cases hdrop with
  | nil _ _ _ hres =>
      obtain ⟨K₂, hK₂⟩ := famAppDomA (fv := fv) hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT
        hb hl hj hΓ hps hps' hrel hρ ⟨hlsC, hbC⟩ hlCC hΓp hres
      obtain ⟨K₃, hK₃⟩ := paramSubstA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL fv hcl hT hb hbC hl hlC hlsC
      have hK1 : K₁ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      have hK2 : K₂ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
      have hK3 : K₃ ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      have hKk : k ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
      have hKj : j ≤ max (max K₁ K₂) (max K₃ (max k j)) :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
      have hV₀ := hK₃ _ hK3 ps ps' is is' hKk hΓ hps hps' hrel ρ hρ
      have hTc₀ := hTc
      rw [hfs] at hTc₀
      have hw₀ := hw
      rw [show List.map (FieldA.instLevels lsC) (List.map FieldA.norm gc.view.fields) =
        List.map (FieldA.instLevels lsC) (List.map FieldA.norm (gc.view.fields ++ []))
          by rw [List.append_nil]] at hw₀
      have hV₁ := hK₁ _ hK1 hKj _ _ fm.nparamsA (ps.map (wkExprA ρ)) pre pre' hV₀ hTc₀ hw₀
      have hlen : pre.length = gc.view.fields.length := by
        rw [(argsRelA_length hw).1, List.length_map]
      have hlen' : pre'.length = gc.view.fields.length := by
        rw [(argsRelA_length hw).2, List.length_map]
      have hpfx := applyTelA_ctorFieldsA_prefix f lsC (instLevel lsC fv.sort)
        (gc.view.res.map (instantiateLevelsA lsC)) [] ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels lsC)) pre
        (by rw [List.length_map, List.length_map, hlen]) (ps.map (wkExprA ρ)) (consListA (ps.map (wkExprA ρ)) SubstA.id)
      rw [List.append_nil, plainArgsA_instLevels, plainArgsA_norm] at hpfx
      rw [hpfx] at hTD
      simp only [ctorFieldsA] at hTD
      injection hTD with hRe
      have hpfx' := applyTelA_ctorFieldsA_prefix f lsC' (instLevel lsC' fv.sort)
        (gc.view.res.map (instantiateLevelsA lsC')) [] ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels lsC')) pre'
        (by rw [List.length_map, List.length_map, hlen']) (ps'.map (wkExprA ρ)) (consListA (ps'.map (wkExprA ρ)) SubstA.id)
      rw [List.append_nil, plainArgsA_instLevels, plainArgsA_norm] at hpfx'
      rw [hpfx'] at hTD'
      simp only [ctorFieldsA] at hTD'
      injection hTD' with hRe'
      subst hRe hRe'
      have hjc : plainIdxA gc.view.fields 0 = (plainArgsA gc.view.fields pre).length := by
        rw [plainIdxA_length gc.view.fields pre hlen 0, Nat.zero_add]
      exact hK₂ _ hK2 _ _ hjc hV₀ hV₁

/-- THE RESULTS OF A WALK'S RIGHT LIST AT THE TWO PARAMETER LISTS, at `lsC'`: the walk's right list
    is a valid pair with itself across the parameters at `lsC` (`validSubstA_trans` of the walk's two
    pairs), carried to `lsC'` (`validSubstA_lvCtx`), where `famAppDomA` relates the two results. -/
theorem resDomRA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ρ : WkSpecA} (hρ : WkOk₀A E I n ρ Γ) {c : Nat}
    {cm : CheckedMemberA}
    {lsA lsC lsC' : List Level} {kinds : List FieldShape} {T T' T'' : ExprA} {pre pre' : List ExprA}
    {R' R'' : ExprA}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hlA : eqNList ls lsA) (hlAC : eqNListB n lsA lsC) (hlCC : eqNListB n lsC lsC')
    (hTc : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hTc' : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    (hTc'' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T'')
    (hw : ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) X F fm.nparamsA (ps.map (wkExprA ρ)) T kinds pre pre')
    (hTD' : applyTelA pre' T' = some R') (hTD'' : applyTelA pre' T'' = some R'') :
    RecDomRelXA E I n (wkCtxA ρ Γ) f fm (famRsFA E I n ρ₀ j Γ fm ρ) ls (ps.map (wkExprA ρ))
      (ps'.map (wkExprA ρ)) R' R'' := by
  obtain ⟨gc, hgc, hgr, hgm⟩ := hcensus c cm hcm hk hfam
  subst hgr hgm
  have hlsC : eqNList ls lsC := eqNListA_trans hlA hlAC.1
  have hlsC' : eqNList ls lsC' := eqNListA_trans hlsC hlCC.1
  have hlC : lsC.length = fm.arity := (eqNListA_length hlsC).symm.trans hl
  have hlC' : lsC'.length = fm.arity := (eqNListA_length hlsC').symm.trans hl
  have hbC : levelsBounded n lsC = true := hlAC.2
  have hbC' : levelsBounded n lsC' = true := hlCC.2
  have hΓρ := ctxWfA_wk₀ hΓ hρ
  have hpsρ : (ps.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps]
  have hpsρ' : (ps'.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps']
  have hTv := gc.applyTel_params lsC hlC (ps.map (wkExprA ρ)) hpsρ
  rw [hTc] at hTv
  injection hTv with hTe
  subst hTe
  have hTv' := gc.applyTel_params lsC' hlC' (ps.map (wkExprA ρ)) hpsρ
  rw [hTc'] at hTv'
  injection hTv' with hTe'
  subst hTe'
  have hTv'' := gc.applyTel_params lsC' hlC' (ps'.map (wkExprA ρ)) hpsρ'
  rw [hTc''] at hTv''
  injection hTv'' with hTe''
  subst hTe''
  rw [gc.normA_getD] at hkinds
  rw [gc.view.shapes hfresh] at hkinds
  injection hkinds with hkinds
  rw [← hkinds] at hw
  have hfs : gc.view.fields = gc.view.fields ++ [] := (List.append_nil _).symm
  have hty := gc.view.typed
  rw [hfs] at hty
  obtain ⟨hwf⟩ := fv.paramsCtxWf hT
  obtain ⟨K₁, hK₁⟩ := fieldWalkA (f := f) (s := instLevel lsC fv.sort) (pl := ps.map (wkExprA ρ))
    (j := j) (Γ := Γ) (ρ := ρ) (X := X) (F := F) hfc hE₀ hI hEN hR₀ hEL₀ hIL hbC hlC hcm hΓρ gc.view.fields hty hwf
  have hdrop := FieldsTyA.drop gc.view.fields hty
  have hΓp := ctxWfA_plainCtx gc.view.fields hty hwf
  have hasm : AsmCtxA (plainCtxA gc.view.fields (telCtxA fv.params)) :=
    asmCtxA_plainCtx _ (asmCtxA_telCtxA _)
  cases hdrop with
  | nil _ _ _ hres =>
      obtain ⟨K₂, hK₂⟩ := famAppDomA (fv := fv) hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT
        hb hl hj hΓ hps hps' hrel hρ ⟨hlsC', hbC'⟩ (eqNListB_refl hbC') hΓp hres
      obtain ⟨K₃, hK₃⟩ := paramSubstA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL fv hcl hT hb hbC hl hlC hlsC
      obtain ⟨K₄, hK₄⟩ := paramSubstA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL fv hcl hT hb hbC' hl hlC' hlsC'
      obtain ⟨K₅, hK₅⟩ := validSubstA_lvCtx hfc hEN hNC hE₀ hI hR₀ hEL₀ hIL hbC hbC' hlC hlC' hlCC.1 hΓp hasm
      have hK1 : K₁ ≤ max (max (max K₁ K₂) (max K₃ K₄)) (max K₅ (max k j)) :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) (Nat.le_max_left _ _)
      have hK2 : K₂ ≤ max (max (max K₁ K₂) (max K₃ K₄)) (max K₅ (max k j)) :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) (Nat.le_max_left _ _)
      have hK3 : K₃ ≤ max (max (max K₁ K₂) (max K₃ K₄)) (max K₅ (max k j)) :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
      have hK4 : K₄ ≤ max (max (max K₁ K₂) (max K₃ K₄)) (max K₅ (max k j)) :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_left _ _)
      have hK5 : K₅ ≤ max (max (max K₁ K₂) (max K₃ K₄)) (max K₅ (max k j)) :=
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      have hKk : k ≤ max (max (max K₁ K₂) (max K₃ K₄)) (max K₅ (max k j)) :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
      have hKj : j ≤ max (max (max K₁ K₂) (max K₃ K₄)) (max K₅ (max k j)) :=
        Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) (Nat.le_max_right _ _)
      have hV₀ := hK₃ _ hK3 ps ps' is is' hKk hΓ hps hps' hrel ρ hρ
      have hV₀' := hK₄ _ hK4 ps ps' is is' hKk hΓ hps hps' hrel ρ hρ
      have hTc₀ := hTc
      rw [hfs] at hTc₀
      have hw₀ := hw
      rw [show List.map (FieldA.instLevels lsC) (List.map FieldA.norm gc.view.fields) =
        List.map (FieldA.instLevels lsC) (List.map FieldA.norm (gc.view.fields ++ []))
          by rw [List.append_nil]] at hw₀
      have hV₁ := hK₁ _ hK1 hKj _ _ fm.nparamsA (ps.map (wkExprA ρ)) pre pre' hV₀ hTc₀ hw₀
      have hV₂ := hK₁ _ hK1 hKj _ _ fm.nparamsA (ps.map (wkExprA ρ)) pre pre' (ValidSubstA_refl_left hEN hV₀)
        hTc₀ hw₀
      have hV₄ := hK₅ _ hK5 (wkCtxA ρ Γ) _ _ hΓρ (validSubstA_trans hEN (ValidSubstA_symm hEN hV₂) hV₁)
      have hlen' : pre'.length = gc.view.fields.length := by
        rw [(argsRelA_length hw).2, List.length_map]
      have hpfx' := applyTelA_ctorFieldsA_prefix f lsC' (instLevel lsC' fv.sort)
        (gc.view.res.map (instantiateLevelsA lsC')) [] ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels lsC')) pre'
        (by rw [List.length_map, List.length_map, hlen']) (ps.map (wkExprA ρ)) (consListA (ps.map (wkExprA ρ)) SubstA.id)
      rw [List.append_nil, plainArgsA_instLevels, plainArgsA_norm] at hpfx'
      rw [hpfx'] at hTD'
      simp only [ctorFieldsA] at hTD'
      injection hTD' with hRe'
      have hpfx'' := applyTelA_ctorFieldsA_prefix f lsC' (instLevel lsC' fv.sort)
        (gc.view.res.map (instantiateLevelsA lsC')) [] ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels lsC')) pre'
        (by rw [List.length_map, List.length_map, hlen']) (ps'.map (wkExprA ρ)) (consListA (ps'.map (wkExprA ρ)) SubstA.id)
      rw [List.append_nil, plainArgsA_instLevels, plainArgsA_norm] at hpfx''
      rw [hpfx''] at hTD''
      simp only [ctorFieldsA] at hTD''
      injection hTD'' with hRe''
      subst hRe' hRe''
      have hjc : plainIdxA gc.view.fields 0 = (plainArgsA gc.view.fields pre').length := by
        rw [plainIdxA_length gc.view.fields pre' hlen' 0, Nat.zero_add]
      exact hK₂ _ hK2 _ _ hjc hV₀' hV₄

/-- THE RECURSIVE DATUM (`hFldRec`): within the fiber, the two domains of a recursive position after
    the walk's two sides are related (`recDomA` at one parameter list). -/
theorem famFldRecA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps is : List ExprA}
    (hps : ps.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps ++ is))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
      eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      applyTelA pre' T' = some (.pi D' uD' C' vC') →
      RecDomRelA E I n (wkCtxA ρ Γ) f fm (famRsFA E I n ρ₀ j Γ fm ρ) ls (ps.map (wkExprA ρ)) D D' :=
  fun _ hρ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' =>
    recDomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps hrel
      hρ hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD'

/-- THE INNER RECURSIVE DATUM AT A WORLD, across two instances (R-NoFunRec-1 step 1 (1c-ε2d-L3b-2)): a walk
    at the world `ρ` reaching a function-recursive field, the two codomains after inner arguments related
    along the weakened domain at an extension `ρ'` — on the left at `ps`, `lsC`, on the right at `ps'`,
    `lsC'` — are related as recursive domains (`frecInnerRecA` at the composed world). Within a fiber
    (`ps' = ps`) it is `famFldIRecA`. -/
theorem frecInnerRecWorldA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (jn : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks →
      eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      applyTelA pre' T' = some (.pi D' uD' C' vC') →
      ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
      ArgsRelPA (innerRelsA (famRsIA E I n ρ₀ j Γ) ρ c lsC (fm.nparamsA + ksPre.length)
        (ps.map (wkExprA ρ) ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' → zs.length = jn + 1 →
      applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
      RecDomRelXA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) f fm (famRsFA E I n ρ₀ j Γ fm (WkSpecA.comp ρ ρ')) ls
        ((ps.map (wkExprA ρ)).map (wkExprA ρ')) ((ps'.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁' := by
  intro ρ hρ c cm lsA lsC lsC' kinds ksPre ks jn T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds
    hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' ρ' hρ' zs zs' C₁ C₁' hz hzn hC₁ hC₁'
  have hTfull : applyTelA (ps.map (wkExprA ρ) ++ pre) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (.pi D uD C vC) := by
    rw [applyTelA_append, hTc]; exact hTD
  have hclC := liftA_instantiateLevelsA_closed (by
    obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam
    exact hgm ▸ gc.normA_getD_closed) lsC
  have hclC' := liftA_instantiateLevelsA_closed (by
    obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam
    exact hgm ▸ gc.normA_getD_closed) lsC'
  have hρc : WkOk₀A E I n (WkSpecA.comp ρ ρ') Γ := wkOk₀A_comp_ext hρ hρ'
  have hTc_c : applyTelA (ps.map (wkExprA (WkSpecA.comp ρ ρ'))) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (wkExprA ρ' T) := by
    rw [← map_wkExprA_comp, applyTelA_wk_closed ρ' _ hclC, hTc]; rfl
  have hTc'_c : applyTelA (ps'.map (wkExprA (WkSpecA.comp ρ ρ'))) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) =
      some (wkExprA ρ' T') := by
    rw [← map_wkExprA_comp, applyTelA_wk_closed ρ' _ hclC', hTc']; rfl
  have hw_c := argsRelA_famRsA_wk hE hI hNC hρ' (fun cm' hm' =>
    (Option.some.inj (hm'.symm.trans hcm)).symm ▸ (by
      obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam
      exact hgm ▸ gc.normA_getD_closed)) hw
  rw [map_wkExprA_comp] at hw_c
  have hTD_c : applyTelA (pre.map (wkExprA ρ')) (wkExprA ρ' T) =
      some (.pi (wkExprA ρ' D) uD (wkExprA (WkSpecA.ub ρ') C) vC) := by
    rw [applyTelA_wk, hTD, Option.map_some', wkExprA_pi_ub]
  have hTD'_c : applyTelA (pre'.map (wkExprA ρ')) (wkExprA ρ' T') =
      some (.pi (wkExprA ρ' D') uD' (wkExprA (WkSpecA.ub ρ') C') vC') := by
    rw [applyTelA_wk, hTD', Option.map_some', wkExprA_pi_ub]
  have hz_c : ArgsRelKA E I n ρ₀ j (wkCtxA (WkSpecA.comp ρ ρ') Γ) (wkExprA ρ' D) zs zs' := by
    rw [wkCtxA_comp]
    exact argsRelKA_of_innerRelsA hE hNC hcm (by obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam; exact hgm ▸ gc.normA_getD_closed) hTfull hz rfl
  have h := frecInnerRecA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl
    hj hΓ hps hps' hrel (ρ := WkSpecA.comp ρ ρ') hρc hcm hk hfam hkinds hsp hlA hlAC hlCC hTc_c hTc'_c
    hw_c hTD_c hTD'_c hz_c hzn hC₁ hC₁'
  rw [map_wkExprA_comp, map_wkExprA_comp, ← wkCtxA_comp]
  exact h

/-- THE INNER RECURSIVE DATUM (`hFldIRec`) (R-NoFunRec-1 step 1 (1c-δ)): within the fiber, the two
    codomains of a function-recursive field after the inner walks are related (`frecInnerRecA` at one
    parameter list). -/
theorem famFldIRecA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps is : List ExprA}
    (hps : ps.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps ++ is))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (jn : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks →
      eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      applyTelA pre' T' = some (.pi D' uD' C' vC') →
      ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
      ArgsRelPA (innerRelsA (famRsIA E I n ρ₀ j Γ) ρ c lsC (fm.nparamsA + ksPre.length)
        (ps.map (wkExprA ρ) ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' → zs.length = jn + 1 →
      applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs' (wkExprA ρ' D') = some C₁' →
      RecDomRelA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) f fm (famRsFA E I n ρ₀ j Γ fm (WkSpecA.comp ρ ρ')) ls
        ((ps.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁' :=
  fun ρ hρ c cm lsA lsC lsC' kinds ksPre ks jn T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds
    hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' ρ' hρ' zs zs' C₁ C₁' hz hzn hC₁ hC₁' =>
  frecInnerRecWorldA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ
    hps hps hrel ρ hρ c cm lsA lsC lsC' kinds ksPre ks jn T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam
    hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' ρ' hρ' zs zs' C₁ C₁' hz hzn hC₁ hC₁'

/-- THE CROSS PLAIN DATUM (`hXFld`): the plain domains of the two parameter instances after one
    prefix are equal at `j` (`plainDomA` on the walk's diagonal). -/
theorem famXFldA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ FieldShape.nonrecursive :: ks →
      eqNList ls lsA → eqNListB n lsA lsC →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
      LREqA E I n ρ₀ j (wkCtxA ρ Γ) D D' :=
  fun _ hρ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk hfam hkinds hsp hlA hlAC hTc hTc' hw hTD hTD' =>
    (plainDomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps' hrel hρ
      hcm hk hfam hkinds hsp hlA hlAC (eqNListB_refl hlAC.2) hTc hTc' (argsRelA_diag hEN (famRsA_refl_left hEN) hw)
      hTD hTD').1

/-- THE CROSS INNER FIELD DATUM (`hXFldI`) (R-NoFunRec-1 step 1 (1c-δ)): the inner domains of the two
    parameter instances after one prefix and one inner walk are equal at `j` (`frecInnerDomA` on the
    diagonal). -/
theorem famXFldIA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (jn : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks →
      eqNList ls lsA → eqNListB n lsA lsC →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
      ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (D₁ : ExprA)
        (u₁ : Level) (C₁ : ExprA) (v₁ : Level) (D₁' : ExprA) (u₁' : Level) (C₁' : ExprA) (v₁' : Level),
      ArgsRelPA (innerRelsA (famRsIA E I n ρ₀ j Γ) ρ c lsC (fm.nparamsA + ksPre.length)
        (ps.map (wkExprA ρ) ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' →
      applyTelA zs (wkExprA ρ' D) = some (.pi D₁ u₁ C₁ v₁) →
      applyTelA zs (wkExprA ρ' D') = some (.pi D₁' u₁' C₁' v₁') →
      LREqA E I n ρ₀ j (wkCtxA ρ' (wkCtxA ρ Γ)) D₁ D₁' := by
  intro ρ hρ c cm lsA lsC kinds ksPre ks jn T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds
    hsp hlA hlAC hTc hTc' hw hTD hTD' ρ' hρ' zs zs' D₁ u₁ C₁ v₁ D₁' u₁' C₁' v₁' hz hD₁ hD₁'
  have hTfull : applyTelA (ps.map (wkExprA ρ) ++ pre) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (.pi D uD C vC) := by
    rw [applyTelA_append, hTc]; exact hTD
  have hclC := liftA_instantiateLevelsA_closed (by
    obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam
    exact hgm ▸ gc.normA_getD_closed) lsC
  have hρc : WkOk₀A E I n (WkSpecA.comp ρ ρ') Γ := wkOk₀A_comp_ext hρ hρ'
  have hTc_c : applyTelA (ps.map (wkExprA (WkSpecA.comp ρ ρ'))) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (wkExprA ρ' T) := by
    rw [← map_wkExprA_comp, applyTelA_wk_closed ρ' _ hclC, hTc]; rfl
  have hTc'_c : applyTelA (ps'.map (wkExprA (WkSpecA.comp ρ ρ'))) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (wkExprA ρ' T') := by
    rw [← map_wkExprA_comp, applyTelA_wk_closed ρ' _ hclC, hTc']; rfl
  have hw_c := argsRelA_famRsA_wk hE hI hNC hρ' (fun cm' hm' =>
    (Option.some.inj (hm'.symm.trans hcm)).symm ▸ (by
      obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam
      exact hgm ▸ gc.normA_getD_closed)) hw
  rw [map_wkExprA_comp] at hw_c
  have hTD_c : applyTelA (pre.map (wkExprA ρ')) (wkExprA ρ' T) =
      some (.pi (wkExprA ρ' D) uD (wkExprA (WkSpecA.ub ρ') C) vC) := by
    rw [applyTelA_wk, hTD, Option.map_some', wkExprA_pi_ub]
  have hTD'_c : applyTelA (pre.map (wkExprA ρ')) (wkExprA ρ' T') =
      some (.pi (wkExprA ρ' D') uD' (wkExprA (WkSpecA.ub ρ') C') vC') := by
    rw [applyTelA_wk, hTD', Option.map_some', wkExprA_pi_ub]
  have hz_c : ArgsRelKA E I n ρ₀ j (wkCtxA (WkSpecA.comp ρ ρ') Γ) (wkExprA ρ' D) zs zs := by
    rw [wkCtxA_comp]
    exact argsRelKA_refl_left hEN (argsRelKA_of_innerRelsA hE hNC hcm (by obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam; exact hgm ▸ gc.normA_getD_closed) hTfull hz rfl)
  have h := (frecInnerDomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hUT hb hl
    hj hΓ hps hps' hrel (ρ := WkSpecA.comp ρ ρ') hρc hcm hk hfam hkinds hsp hlA hlAC
    (eqNListB_refl hlAC.2) hTc_c hTc'_c (argsRelA_diag hEN (famRsA_refl_left hEN) hw_c) hTD_c hTD'_c hz_c hD₁ hD₁').1
  rw [← wkCtxA_comp]
  exact h

/-- THE CROSS RECURSIVE DATUM (`hXRec`): the recursive domains of the two parameter instances after
    one prefix are related (`recDomA` on the walk's diagonal). -/
theorem famXRecA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds → kinds = ksPre ++ (FieldShape.recursive 0) :: ks →
      eqNList ls lsA → eqNListB n lsA lsC →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
      RecDomRelXA E I n (wkCtxA ρ Γ) f fm (famRsFA E I n ρ₀ j Γ fm ρ) ls (ps.map (wkExprA ρ))
        (ps'.map (wkExprA ρ)) D D' :=
  fun _ hρ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk hfam hkinds hsp hlA hlAC hTc hTc' hw hTD hTD' =>
    recDomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps' hrel
      hρ hcm hk hfam hkinds hsp hlA hlAC (eqNListB_refl hlAC.2) hTc hTc'
      (argsRelA_diag hEN (famRsA_refl_left hEN) hw) hTD hTD'

/-- THE CROSS INNER RECURSIVE DATUM (`hXRecI`) (R-NoFunRec-1 step 1 (1c-δ)): the codomains of the two
    parameter instances after one prefix and the inner walks are related (`frecInnerRecA` on the
    diagonal). -/
theorem famXRecIA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (jn : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks →
      eqNList ls lsA → eqNListB n lsA lsC →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) → applyTelA pre T' = some (.pi D' uD' C' vC') →
      ∀ (ρ' : WkSpecA), WkOkA E I n ρ' (wkCtxA ρ Γ) → ∀ (zs zs' : List ExprA) (C₁ C₁' : ExprA),
      ArgsRelPA (innerRelsA (famRsIA E I n ρ₀ j Γ) ρ c lsC (fm.nparamsA + ksPre.length)
        (ps.map (wkExprA ρ) ++ pre) ρ') 0 [] (wkExprA ρ' D) zs zs' → zs.length = jn + 1 →
      applyTelA zs (wkExprA ρ' D) = some C₁ → applyTelA zs (wkExprA ρ' D') = some C₁' →
      RecDomRelXA E I n (wkCtxA ρ' (wkCtxA ρ Γ)) f fm (famRsFA E I n ρ₀ j Γ fm (WkSpecA.comp ρ ρ')) ls
        ((ps.map (wkExprA ρ)).map (wkExprA ρ')) ((ps'.map (wkExprA ρ)).map (wkExprA ρ')) C₁ C₁' := by
  intro ρ hρ c cm lsA lsC kinds ksPre ks jn T T' pre pre' D uD C vC D' uD' C' vC' hcm hk hfam hkinds
    hsp hlA hlAC hTc hTc' hw hTD hTD' ρ' hρ' zs zs' C₁ C₁' hz hzn hC₁ hC₁'
  have hTfull : applyTelA (ps.map (wkExprA ρ) ++ pre) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (.pi D uD C vC) := by
    rw [applyTelA_append, hTc]; exact hTD
  have hclC := liftA_instantiateLevelsA_closed (by
    obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam
    exact hgm ▸ gc.normA_getD_closed) lsC
  have hρc : WkOk₀A E I n (WkSpecA.comp ρ ρ') Γ := wkOk₀A_comp_ext hρ hρ'
  have hTc_c : applyTelA (ps.map (wkExprA (WkSpecA.comp ρ ρ'))) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (wkExprA ρ' T) := by
    rw [← map_wkExprA_comp, applyTelA_wk_closed ρ' _ hclC, hTc]; rfl
  have hTc'_c : applyTelA (ps'.map (wkExprA (WkSpecA.comp ρ ρ'))) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) =
      some (wkExprA ρ' T') := by
    rw [← map_wkExprA_comp, applyTelA_wk_closed ρ' _ hclC, hTc']; rfl
  have hw_c := argsRelA_famRsA_wk hE hI hNC hρ' (fun cm' hm' =>
    (Option.some.inj (hm'.symm.trans hcm)).symm ▸ (by
      obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam
      exact hgm ▸ gc.normA_getD_closed)) hw
  rw [map_wkExprA_comp] at hw_c
  have hTD_c : applyTelA (pre.map (wkExprA ρ')) (wkExprA ρ' T) =
      some (.pi (wkExprA ρ' D) uD (wkExprA (WkSpecA.ub ρ') C) vC) := by
    rw [applyTelA_wk, hTD, Option.map_some', wkExprA_pi_ub]
  have hTD'_c : applyTelA (pre.map (wkExprA ρ')) (wkExprA ρ' T') =
      some (.pi (wkExprA ρ' D') uD' (wkExprA (WkSpecA.ub ρ') C') vC') := by
    rw [applyTelA_wk, hTD', Option.map_some', wkExprA_pi_ub]
  have hz_c : ArgsRelKA E I n ρ₀ j (wkCtxA (WkSpecA.comp ρ ρ') Γ) (wkExprA ρ' D) zs zs := by
    rw [wkCtxA_comp]
    exact argsRelKA_refl_left hEN (argsRelKA_of_innerRelsA hE hNC hcm (by obtain ⟨gc, _, _, hgm⟩ := hcensus c cm hcm hk hfam; exact hgm ▸ gc.normA_getD_closed) hTfull hz rfl)
  have h := frecInnerRecA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl
    hj hΓ hps hps' hrel (ρ := WkSpecA.comp ρ ρ') hρc hcm hk hfam hkinds hsp hlA hlAC
    (eqNListB_refl hlAC.2) hTc_c hTc'_c (argsRelA_diag hEN (famRsA_refl_left hEN) hw_c) hTD_c hTD'_c hz_c hzn hC₁ hC₁'
  rw [map_wkExprA_comp, map_wkExprA_comp, ← wkCtxA_comp]
  exact h

/-- THE CROSS RESULTS (`hXRes`): the results of the two parameter instances after one walk's left list
    are related (`resDomA` on the walk's diagonal). -/
theorem famXResA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds : List FieldShape) (T T' : ExprA) (pre pre' : List ExprA)
      (R R' : ExprA),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      eqNList ls lsA → eqNListB n lsA lsC →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T kinds pre pre' →
      applyTelA pre T = some R → applyTelA pre T' = some R' →
      RecDomRelXA E I n (wkCtxA ρ Γ) f fm (famRsFA E I n ρ₀ j Γ fm ρ) ls (ps.map (wkExprA ρ))
        (ps'.map (wkExprA ρ)) R R' :=
  fun _ hρ _ _ _ _ _ _ _ _ _ _ _ hcm hk hfam hkinds hlA hlAC hTc hTc' hw hTD hTD' =>
    resDomA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps' hrel
      hρ hcm hk hfam hkinds hlA hlAC (eqNListB_refl hlAC.2) hTc hTc'
      (argsRelA_diag hEN (famRsA_refl_left hEN) hw) hTD hTD'

/-- THE CROSS RESULTS OF THE RIGHT LIST (`hXResR`) (`resDomRA`). -/
theorem famXResRA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds : List FieldShape) (T T' T'' : ExprA) (pre pre' : List ExprA)
      (R' R'' : ExprA),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T'' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T kinds pre pre' →
      applyTelA pre' T' = some R' → applyTelA pre' T'' = some R'' →
      RecDomRelXA E I n (wkCtxA ρ Γ) f fm (famRsFA E I n ρ₀ j Γ fm ρ) ls (ps.map (wkExprA ρ))
        (ps'.map (wkExprA ρ)) R' R'' :=
  fun _ hρ _ _ _ _ _ _ _ _ _ _ _ _ _ hcm hk hfam hkinds hlA hlAC hlCC hTc hTc' hTc'' hw hTD' hTD'' =>
    resDomRA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hfresh hcensus hcl hT hUT hb hl hj hΓ hps hps' hrel
      hρ hcm hk hfam hkinds hlA hlAC hlCC hTc hTc' hTc'' hw hTD' hTD''

/-- THE CROSS INDEX DATUM (`hXFeq`): the index domains of the two parameter instances after one
    prefix are equal at `j` (`idxDomA` on the walk's diagonal). -/
theorem famXFeqA (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hIL : IotaLevelsA I) (hS : SmallIndexProfileA E)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    (hfm : E.members f = some fm) (hcls : fm.mclass = .inductiveM)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u)) (hUT : UniformType fv.sort)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity)
    {j : Nat} (hj : ht ρ₀ (instLevel ls fv.sort) ≤ j)
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is')) :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (lsF : List Level) (TF TF' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level), eqNListB n ls lsF →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsF fm.mtypeA) = some TF →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsF fm.mtypeA) = some TF' →
      ArgsRelPA (famRsFA E I n ρ₀ j Γ fm ρ lsF) fm.nparamsA (ps.map (wkExprA ρ)) TF pre pre' →
      applyTelA pre TF = some (.pi D uD C vC) → applyTelA pre TF' = some (.pi D' uD' C' vC') →
      LREqA E I n ρ₀ j (wkCtxA ρ Γ) D D' :=
  fun _ hρ _ _ _ _ _ _ _ _ _ _ _ _ _ hlF hTF hTF' hw hTD hTD' =>
    (idxDomA (fv := fv) hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hS hfm hcls hcl hT hUT hb hl hj hΓ hps hps' hrel
      hρ hlF (eqNListB_refl hlF.2) hTF hTF' (argsRelPA_diag hEN (famRsFA_refl_left hEN) hw) hTD hTD').1

end RecDatum

#print axioms ht_le_of_leN
#print axioms leN_instLevel
#print axioms isZero_false_of_uniformType
#print axioms argsRelKA_wk
#print axioms argsRelKA_wk₀
#print axioms argsRelKA_mono
#print axioms argsRelKA_refl_left
#print axioms FamViewA.inst_split
#print axioms FamViewA.paramsCtxWf
#print axioms paramSubstA
#print axioms map_eq_append_cons
#print axioms plainSort_ht_le
#print axioms argsRelA_diag
#print axioms plainDomA
#print axioms plainArgsA_plainA
#print axioms plainIdxA_plainA
#print axioms map_shape_plainA
#print axioms argsRelA_of_argsRelKA
#print axioms applyTelA_ctorFieldsA_lt
#print axioms argsRelKA_of_innerRelsA
#print axioms argsRelA_famRsA_wk
#print axioms frecWalkA
#print axioms frecInnerDomA
#print axioms famFldA
#print axioms famFldIA
#print axioms famFldeqA
#print axioms famFldIeqA
#print axioms applyTelA_piTelA_pi
#print axioms piTelA_domTy
#print axioms argsRelPA_famRsFA_KA
#print axioms telExtA
#print axioms idxSort_ht_le
#print axioms argsRelPA_diag
#print axioms idxDomA
#print axioms famFldFA
#print axioms famFldFeqA
#print axioms idxArgsA
#print axioms famXsA
#print axioms isPiTelA_piTelA
#print axioms spineConvA
#print axioms ValidSubstA_uncons
#print axioms argsRelKA_append
#print axioms argsRelKA_of_validSubst
#print axioms parConvA_of_validSubst
#print axioms famParConvA
#print axioms argsTyA_relLv
#print axioms substA_consListA_liftA
#print axioms applyTelA_substA_inst
#print axioms argsRelKA_length_le
#print axioms asmCtxA_telCtxA
#print axioms asmCtxA_plainCtx
#print axioms validSubstA_trans
#print axioms validSubstA_lvCtx
#print axioms famAppArgsA
#print axioms famAppDomA
#print axioms recDomA
#print axioms frecInnerRecA
#print axioms resDomA
#print axioms resDomRA
#print axioms famFldRecA
#print axioms frecInnerRecWorldA
#print axioms famFldIRecA
#print axioms famXFldA
#print axioms famXFldIA
#print axioms famXRecA
#print axioms famXRecIA
#print axioms famXResA
#print axioms famXResRA
#print axioms famXFeqA

end Rcic.Declarative.Ann
