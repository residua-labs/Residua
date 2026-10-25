import rcic.RcicF3GroupFacts

/-!
# F3 S5a-14: soundness of a group's members, and ι

Transfer lemmas between tables that agree on a prefix; the semantic ι
property `IotaAt` (given the right-hand side's hereditarily sound typing and
the recursor instance's level bound) and the assembly of `EnvSound` from
member soundness and ι; the family's, a constructor's and (for groups whose
fields are family-free) the recursor's member soundness; ι at a group's
recursor (`iota_at`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs)

namespace PSet

theorem denRefs_instantiateLevels (ls : List Level) : (e : Expr Nat) →
    denRefs (instantiateLevels ls e) = denRefs e
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f a => by
      show denRefs (instantiateLevels ls f) ++ denRefs (instantiateLevels ls a) = _
      rw [denRefs_instantiateLevels ls f, denRefs_instantiateLevels ls a]; rfl
  | .lam A b => by
      show denRefs (instantiateLevels ls A) ++ denRefs (instantiateLevels ls b) = _
      rw [denRefs_instantiateLevels ls A, denRefs_instantiateLevels ls b]; rfl
  | .pi A B => by
      show denRefs (instantiateLevels ls A) ++ denRefs (instantiateLevels ls B) = _
      rw [denRefs_instantiateLevels ls A, denRefs_instantiateLevels ls B]; rfl
  | .letE A v b => by
      show denRefs (instantiateLevels ls A) ++ denRefs (instantiateLevels ls v) ++
        denRefs (instantiateLevels ls b) = _
      rw [denRefs_instantiateLevels ls A, denRefs_instantiateLevels ls v, denRefs_instantiateLevels ls b]; rfl
  | .lit _ => rfl

/-- Member soundness transfers to a table agreeing on the member's references. -/
theorem memberSound_transfer (P : Premises4) {μ μ' : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {S : Nat → Prop}
    (hag : AgreeOn μ' μ S) {r : Nat} {m : CheckedMember} (hr : S r)
    (hty : ∀ r', r' ∈ denRefs m.mtype → S r') (hb : ∀ b, m.body = some b → ∀ r', r' ∈ denRefs b → S r')
    (h : MemberSound P μ K r m) : MemberSound P μ' K r m := by
  intro σ ls ρ hlen hl
  obtain ⟨h1, h2⟩ := h σ ls ρ hlen hl
  have hμ : μ' r (ls.map (evalTotal σ)) = μ r (ls.map (evalTotal σ)) := hag r hr _
  have hd : ∀ e, (∀ r', r' ∈ denRefs e → S r') →
      den (mkM P μ') σ ρ (instantiateLevels ls e) = den (mkM P μ) σ ρ (instantiateLevels ls e) := fun e he =>
    den_agreeOn P hag σ _ (fun r' hr' => he r' (by rwa [denRefs_instantiateLevels] at hr')) ρ
  refine ⟨?_, fun b hbd => ?_⟩
  · rw [hμ, hd _ hty]; exact h1
  · rw [hμ, hd b (hb b hbd)]; exact h2 b hbd

/-- The semantic ι property at the recursor `r`, for witnesses in environments
below `Efin`, at the table `μ`, given a hereditarily sound typing of the
right-hand side and the recursor instance's level bound. -/
def IotaAt (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) (Efin : ResolvedEnv) (r : Nat) :
    Prop :=
  ∀ (E : ResolvedEnv), (∀ r' m', E.members r' = some m' → Efin.members r' = some m') →
    ∀ (w : IotaWitness E), w.recRef = r → ∀ (σ : Nat → Nat) (n : Nat) (Γ : LCtx) (T : Expr Nat)
      (ρ : Nat → PSet.{4}) (hl : HasTyT E n Γ (iotaLhsOf w) T), HSoundT (mkM P μ) σ hl →
      (∃ (N : Nat) (Lv : Nat → PSet.{4} → Prop), Good (mkM P μ) N Lv ∧ LOKt σ N K hl) →
      ∀ (hr : HasTyT E n Γ (iotaRhsOf w) T), HSoundT (mkM P μ) σ hr →
      LevelsOK σ (K r) w.ls → Fits (mkM P μ) σ Γ ρ →
      den (mkM P μ) σ ρ (iotaLhsOf w) ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ T) →
      den (mkM P μ) σ ρ (iotaRhsOf w) ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ T) →
      Equiv (den (mkM P μ) σ ρ (iotaLhsOf w)) (den (mkM P μ) σ ρ (iotaRhsOf w))

/-- `EnvSound` from member soundness and ι at every recursor. -/
theorem envSound_of (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {E Efin : ResolvedEnv}
    (hsub : ∀ r m, E.members r = some m → Efin.members r = some m)
    (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r) (σ : Nat → Nat) (n : Nat) :
    EnvSound (mkM P μ) σ K E n where
  const := fun _ r ls m ρ hres hlen hl _ => (hA r m hres σ ls ρ hlen hl).1
  delta := fun _ r ls m b ρ hres hbody _ hlen hl _ => (hA r m hres σ ls ρ hlen hl).2 b hbody
  iota := by
    intro Γ lhs rhs T ρ hι hl hr il ir ⟨N, Lv, hGd, hlok⟩ hf ml mr
    cases hι with
    | of w =>
        exact hI w.recRef w.recMember w.hrec w.hrecK E hsub w rfl σ n Γ T ρ hl il ⟨N, Lv, hGd, hlok⟩ hr ir
          (lok_spine_const σ N K w.recRef w.ls _ hl hlok) hf ml mr

/-- A family member is sound when its table entry is its family value. -/
theorem fam_member_sound (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {f : Nat}
    {fm : CheckedMember} (fd : FamData)
    (hF : ∀ vs, Equiv (μ f vs) (piLam (mkM P μ) (σOf vs) (famEnd (mkM P μ) W4 (σOf vs) fd) ρ0 fm.mtype))
    (hst : fm.mtype = famType fd) (hcl : ∀ k, Rcic.Declarative.lift k 1 fm.mtype = fm.mtype)
    (hlvl : exprLevelsBounded fm.arity fm.mtype = true) (hbody : fm.body = none) : MemberSound P μ K f fm := by
  intro σ ls ρ hlen _
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  rw [den_inst_canon (mkM P μ) σ ls ρ fm.mtype hcl (hlen ▸ hlvl)]
  refine mem_congr_left (hF _).symm ?_
  have := famVal_mem P (mkM P μ) rfl (σOf (ls.map (evalTotal σ))) fd ρ0
  rw [← hst] at this
  exact this

/-- A constructor member is sound, from the family's value, a sound typing of
its stored type and the smallness of its fields. -/
theorem ctor_member_sound (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {c : Nat}
    {cm : CheckedMember} (fd : FamData) (j : Nat) (cps fs ri : List (Expr Nat))
    (hj : fd.ctors[j]? = some (fs, ri)) (hnp : cps.length = fd.params.length) (hq : ri.length = fd.indices.length)
    (hst : cm.mtype = policyPi (cps ++ fs) (foldApps (.const fd.fref ((List.range cm.arity).map Level.param))
      (policyParameterLocals cps.length fs.length ++ ri)))
    (hcl : ∀ k, Rcic.Declarative.lift k 1 cm.mtype = cm.mtype)
    (hlvl : exprLevelsBounded cm.arity cm.mtype = true) (hbody : cm.body = none)
    (hF : ∀ vs, Equiv (μ c vs)
      (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) fd j (nfOf fd j)) ρ0 cm.mtype))
    (hfam : ∀ vs, vs.length = cm.arity → Equiv (μ fd.fref vs)
      (piLam (mkM P μ) (σOf vs) (famEnd (mkM P μ) W4 (σOf vs) fd) (fun _ => pempty) (famType fd)))
    (htyp : ∀ vs, vs.length = cm.arity → (∀ v, v ∈ vs → v ≤ K c) →
      ∀ zs, TelFits (mkM P μ) (σOf vs) (cps ++ fs) ρ0 zs → ∃ v,
      den (mkM P μ) (σOf vs) (push zs ρ0) (foldApps (.const fd.fref ((List.range vs.length).map Level.param))
        (policyParameterLocals cps.length fs.length ++ ri)) ∈
        Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push zs ρ0) (.sort v)))
    (hsmall : ∀ vs, vs.length = cm.arity → (∀ v, v ∈ vs → v ≤ K c) →
      evalTotal (σOf vs) fd.resLevel ≠ 0 → ∀ ps xs, TelFits (mkM P μ) (σOf vs) cps ρ0 ps →
      TelFits (mkM P μ) (σOf vs) fs (push ps ρ0) xs →
      SmallAlong (mkM P μ) (σOf vs) (W4 (evalTotal (σOf vs) fd.resLevel)) fs (push ps ρ0) xs) :
    MemberSound P μ K c cm := by
  intro σ ls ρ hlen hl
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  have hvl : (ls.map (evalTotal σ)).length = cm.arity := by rw [List.length_map, hlen]
  have hbd : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K c := by
    intro v hv
    obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hv
    exact hl l hl'
  rw [den_inst_canon (mkM P μ) σ ls ρ cm.mtype hcl (hlen ▸ hlvl)]
  refine mem_congr_left (hF _).symm ?_
  have hnf : nfOf fd j = fs.length := by unfold nfOf; rw [hj]
  rw [hnf, hst]
  have hst' : (List.range cm.arity).map Level.param = (List.range (ls.map (evalTotal σ)).length).map Level.param := by
    rw [hvl]
  rw [hst']
  exact ctorVal_mem rfl (ls.map (evalTotal σ)) fd j cps fs ri hj hnp hq (hfam _ hvl)
    (htyp _ hvl hbd) (hsmall _ hvl hbd)

theorem ExprsBounded_append {k : Nat} {xs ys : List (Expr Nat)} (h : ExprsBounded k (xs ++ ys)) :
    ExprsBounded k xs ∧ ExprsBounded k ys :=
  ⟨fun e he => h e (List.mem_append_left _ he), fun e he => h e (List.mem_append_right _ he)⟩

/-- A group's table entries are its values, at every instance. -/
structure GroupFaith (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {E E' : ResolvedEnv} {f rr : Nat}
    {rm : CheckedMember} (fm : CheckedMember) (node : RecNode E E' f rr rm) : Prop where
  fam : ∀ vs, Equiv (μ f vs) (piLam (mkM P μ) (σOf vs) (famEnd (mkM P μ) W4 (σOf vs) (famDataOf node.a)) ρ0 fm.mtype)
  ctor : ∀ (i : Fin node.a.constructors.length) vs, Equiv (μ (f + 1 + i.val) vs)
    (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf node.a) i.val (nfOf (famDataOf node.a) i.val))
      ρ0 (node.a.constructors[i.val]).mtype)
  recur : ∀ vs, Equiv (μ rr vs) (piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf node.a)) ρ0 rm.mtype)
  famTy : fm.mtype = famType (famDataOf node.a)
  bounded : FamBounded (famDataOf node.a) node.a.family.member.arity
  ctorBounded : ∀ i : Fin node.a.constructors.length,
    exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true

theorem nfOf_famDataOf {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (i : Fin a.constructors.length) : nfOf (famDataOf a) i.val = (a.constructorViews i).fields.length := by
  unfold nfOf; rw [famDataOf_ctor a i]

/-- The family's value at a recursor instance, from the table entry at the family instance. -/
theorem groupFaith_famAt (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {E E' : ResolvedEnv} {f rr : Nat}
    {rm fm : CheckedMember} {node : RecNode E E' f rr rm} (hG : GroupFaith P μ fm node) (vs : List Nat) :
    Equiv (μ node.a.family.ref ((policyFamilyLevels node.a.family).map (evalTotal (σOf vs))))
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)) := by
  rw [node.fam]
  refine (hG.fam _).trans ?_
  rw [hG.famTy]
  exact famVal_levels (mkM P μ) (k := node.a.family.member.arity) (σOf_policyFamilyLevels_agree _ vs) W4 _ hG.bounded

/-- A constructor's value at a recursor instance. -/
theorem groupFaith_ctorAt (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {E E' : ResolvedEnv} {f rr : Nat}
    {rm fm : CheckedMember} {node : RecNode E E' f rr rm} (hG : GroupFaith P μ fm node) (vs : List Nat)
    (i : Fin node.a.constructors.length) :
    Equiv (μ (node.a.family.ref + 1 + i.val) ((policyFamilyLevels node.a.family).map (evalTotal (σOf vs))))
      (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf node.a) i.val
        (node.a.constructorViews i).fields.length) ρ0 (node.a.constructors[i.val]).mtype) := by
  rw [node.fam]
  refine (hG.ctor i _).trans ?_
  rw [nfOf_famDataOf]
  have hst := (node.a.constructorViews i).storedType
  rw [hst]
  have hb := hG.ctorBounded i
  rw [hst] at hb
  obtain ⟨hD, _⟩ := levelsBounded_policyPi _ _ _ hb
  have hres := hG.bounded.res
  refine piLam_levels (mkM P μ) (k := node.a.family.member.arity) (σOf_policyFamilyLevels_agree _ vs)
    (ctorEnd_resp _ _ _ _ _) (fun ρ => ?_) _ (fun ρ => ?_) _ hD ρ0
  · unfold ctorEnd
    rw [evalTotal_agree (σOf_policyFamilyLevels_agree _ vs) _ hres]
    exact Equiv.rfl
  · rw [piLam_foldApps_const, piLam_foldApps_const]
    unfold ctorEnd
    rw [evalTotal_agree (σOf_policyFamilyLevels_agree _ vs) _ hres]
    exact Equiv.rfl

/-- The selection read at a recursor instance: `Prop` with large elimination is
uniformly `Prop`, and has at most one constructor. -/
theorem selection_prop {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (σ : Nat → Nat) (h0 : evalTotal σ a.family.resultLevel = 0) (hpol : a.policy = .anySort) :
    UniformProp a.family.resultLevel ∧ a.constructors.length ≤ 1 := by
  have hs : EliminationSelection a.family.resultLevel a.constructors.length
      (∀ i, (a.constructorViews i).AllFieldsSafe) .anySort := by rw [← hpol]; exact a.selected
  rcases (EliminationSelection.anySort_iff _ _ _).mp hs with ht | ⟨hp, hk0 | ⟨hk1, _⟩⟩
  · exact absurd h0 (Nat.pos_iff_ne_zero.mp (ht σ))
  · exact ⟨hp, by omega⟩
  · exact ⟨hp, by omega⟩

/-- The universe profile is uniform. -/
theorem selection_uniform {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) :
    UniformProp a.family.resultLevel ∨ UniformType a.family.resultLevel := by
  have hs := a.selected
  revert hs
  generalize a.policy = p
  intro hs
  cases hs with
  | uniformType h => exact Or.inr h
  | emptyProp h _ => exact Or.inl h
  | singletonProp h _ _ => exact Or.inl h
  | multipleProp h _ => exact Or.inl h
  | hiddenDataProp h _ _ => exact Or.inl h

/-- A recursor member is sound. -/
theorem rec_member_sound (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {E E' : ResolvedEnv}
    {f rr : Nat} {rm fm : CheckedMember} {node : RecNode E E' f rr rm} (hG : GroupFaith P μ fm node)
    (hcl : ∀ k, Rcic.Declarative.lift k 1 rm.mtype = rm.mtype)
    (hlvl : exprLevelsBounded rm.arity rm.mtype = true) (hbody : rm.body = none)
    (hnr : ∀ i fuel shapes, fieldShapesFuel node.E0 fuel node.a.family.ref node.a.family.member.arity
        node.a.family.parameters.length node.a.family.indices.length node.a.family.parameters.length
        (node.a.constructorViews i).fields = some shapes → ∀ s, s ∈ shapes → s = .nonrecursive)
    (hpf : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i : Fin node.a.constructors.length,
        (∀ k, k < (node.a.constructorViews i).fields.length →
          posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k)) (node.a.constructorViews i).resultIndices =
            none) ∧
        ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps, TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
          PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0))
    (hfree : ∀ (i : Fin node.a.constructors.length) T, T ∈ (node.a.constructorViews i).fields →
      occursConst node.a.family.ref T = false) :
    MemberSound P μ K rr rm := by
  intro σ ls ρ hlen hls
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
  refine mem_congr_left (hG.recur _).symm ?_
  refine recVal_mem rfl node.a (ls.map (evalTotal σ)) ?_ (groupFaith_famAt P hG _) (groupFaith_ctorAt P hG _) ?_ hfree
  · intro i
    obtain ⟨shapes, fuel, hfs, hdm⟩ := node.h12 i
    exact ⟨fuel, shapes, hnr i fuel shapes hfs,
      fieldShapesFuel_length _ _ _ _ _ _ _ _ _ hfs, hdm⟩
  · intro h0 hpol c hc ps is xs hps hcf
    obtain ⟨hup, hk⟩ := selection_prop node.a _ h0 hpol
    obtain ⟨c', hc', hxs, _⟩ := hcf
    rw [hc] at hc'
    simp at hc'
    subst hc'
    have hk1 : node.a.constructors.length = 1 := by
      have := famDataOf_ctors_length node.a
      rw [hc] at this
      simpa using this.symm
    have hc0 := famDataOf_ctor node.a ⟨0, by omega⟩
    rw [hc] at hc0
    simp at hc0
    obtain ⟨hnorev, hprop⟩ := hpf hup hpol ⟨0, by omega⟩
    rw [hc0] at hxs ⊢
    rw [recon_none _ is hnorev]
    have hL := propTel_fits _ _ _ _ xs (hprop _ (fun v hv => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
      exact hls l hl) ps hps) hxs
    have e : xs.map (fun _ => pempty) = (node.a.constructorViews ⟨0, by omega⟩).fields.map fun _ => pempty := by
      simp only [List.map_const', hxs.length]
    rw [e] at hL
    exact hL

/-- A recursor of an empty `Prop` family eliminating into any sort is sound:
every obligation is at a constructor that fits, and none does. -/
theorem rec_member_sound_empty (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {E E' : ResolvedEnv}
    {f rr : Nat} {rm fm : CheckedMember} {node : RecNode E E' f rr rm} (hG : GroupFaith P μ fm node)
    (hcl : ∀ k, Rcic.Declarative.lift k 1 rm.mtype = rm.mtype)
    (hlvl : exprLevelsBounded rm.arity rm.mtype = true) (hbody : rm.body = none)
    (hU : UniformProp node.a.family.resultLevel)
    (hemp : ∀ vs, PropEmpty (mkM P μ) (σOf vs) (famDataOf node.a)) :
    MemberSound P μ K rr rm := by
  intro σ ls ρ hlen _
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
  refine mem_congr_left (hG.recur _).symm ?_
  exact recVal_mem_gen rfl node.a (ls.map (evalTotal σ)) (groupFaith_famAt P hG _)
    (fun _ _ _ _ _ _ _ _ hcf => (hemp _ _ _ _ _ hcf).elim) (fun _ _ _ _ _ _ hcf => (hemp _ _ _ _ _ hcf).elim)
    (fun _ _ _ _ hcf => (hemp _ _ _ _ _ hcf).elim)
    (fun _ _ => pempty) (fun h0 => absurd (hU _) h0)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hcf => (hemp _ _ _ _ _ hcf).elim)

/-- ι at one redex of a group's recursor, from the large-elimination
condition at that redex (its witness, the left-hand side's typing, its
soundness and bound, the context's values). -/
theorem iota_at_gen_pt (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {E E' Efin : ResolvedEnv} {f rr : Nat}
    {rm fm : CheckedMember} {node : RecNode E E' f rr rm} (hG : GroupFaith P μ fm node)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m) (hrm : E'.members rr = some rm)
    (hrf : ∀ i : Fin node.a.constructors.length, RecFieldsDirect node.a.family.ref (policyFamilyLevels node.a.family)
      node.a.family.parameters.length node.a.family.indices.length (node.a.constructorViews i).fields 0)
    (hlvC : ∀ i : Fin node.a.constructors.length,
      exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true)
    {E'' : ResolvedEnv} (hsub : ∀ r m, E''.members r = some m → Efin.members r = some m)
    (w : IotaWitness E'') (hwr : w.recRef = rr) (σ : Nat → Nat) (n : Nat) (Γ : LCtx) (T : Expr Nat)
    (ρ : Nat → PSet.{4}) (hl : HasTyT E'' n Γ (iotaLhsOf w) T) (il : HSoundT (mkM P μ) σ hl)
    (hN : ∃ (N : Nat) (Lv : Nat → PSet.{4} → Prop), Good (mkM P μ) N Lv ∧ LOKt σ N K hl)
    (hr : HasTyT E'' n Γ (iotaRhsOf w) T) (hrs : HSoundT (mkM P μ) σ hr) (hls : LevelsOK σ (K rr) w.ls)
    (hfit : Fits (mkM P μ) σ Γ ρ)
    (ml : den (mkM P μ) σ ρ (iotaLhsOf w) ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ T))
    (mr : den (mkM P μ) σ ρ (iotaRhsOf w) ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ T))
    (hpf : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i : Fin node.a.constructors.length, w.ctorIdx = i.val → w.recMember = rm →
        w.ctorMember = node.a.constructors[i.val] → w.fields.length = (node.a.constructorViews i).fields.length →
        ((∀ T, T ∈ (node.a.constructorViews i).fields → occursConst node.a.family.ref T = false) ∧
        (((∀ k, k < (node.a.constructorViews i).fields.length →
          posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k)) (node.a.constructorViews i).resultIndices =
            none) ∧
        (∃ b, node.a.minorTypes[i.val]? = some (policyPi (liftFields (1 + i.val) (node.a.constructorViews i).fields 0) b)) ∧
        ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps, TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
          PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0)) ∨
        IotaAgree (mkM P μ) σ ρ node.a w i)) ∨
        ∀ vs, PropEmpty (mkM P μ) (σOf vs) (famDataOf node.a)) :
    Equiv (den (mkM P μ) σ ρ (iotaLhsOf w)) (den (mkM P μ) σ ρ (iotaRhsOf w)) := by
  have hm : w.recMember = rm := by
    have h1 := hsub _ _ w.hrec
    have h3 : Efin.members w.recRef = some rm := by rw [hwr]; exact hsubF _ _ hrm
    exact (Option.some.inj (h3.symm.trans h1)).symm
  obtain ⟨_, hnM, _, hfr⟩ := iota_align node.a w hwr hm
  have hjk : w.ctorIdx < node.a.constructors.length := by have := w.hidx; omega
  let j : Fin node.a.constructors.length := ⟨w.ctorIdx, hjk⟩
  have hcref : w.ctorRef = node.a.family.ref + 1 + j.val := by rw [w.hctorIdx, hfr]
  have hcm : w.ctorMember = node.a.constructors[j.val] := by
    have h1 := hsub _ _ w.hctor
    have h2 := node.a.constructorsPresent j
    have h3 := hsubF _ _ (node.sub _ _ (members_extend_preserved node.fresh _ _ h2))
    rw [hcref] at h1
    rw [h1] at h3
    exact Option.some.inj h3
  have huni : evalTotal (σOf (w.ls.map (evalTotal σ))) node.a.family.resultLevel = 0 ↔
      evalTotal (σOf (w.lsC.map (evalTotal σ))) node.a.family.resultLevel = 0 := by
    rcases selection_uniform node.a with hp | ht
    · exact ⟨fun _ => hp _, fun _ => hp _⟩
    · exact ⟨fun h => absurd h (Nat.pos_iff_ne_zero.mp (ht _)), fun h => absurd h (Nat.pos_iff_ne_zero.mp (ht _))⟩
  have hctor0 := hG.ctor j (w.lsC.map (evalTotal σ))
  rw [nfOf_famDataOf] at hctor0
  have e : w.ctorRef = f + 1 + j.val := by rw [hcref, node.fam]
  have hctor : Equiv (μ w.ctorRef (w.lsC.map (evalTotal σ)))
      (piLam (mkM P μ) (σOf (w.lsC.map (evalTotal σ))) (ctorEnd (mkM P μ) (σOf (w.lsC.map (evalTotal σ)))
        (famDataOf node.a) j.val (node.a.constructorViews j).fields.length) (fun _ => pempty)
        (node.a.constructors[j.val]).mtype) := by rw [e]; exact hctor0
  exact iota_group W4 node.a w hwr hm σ ρ (hG.recur _) (groupFaith_famAt P hG _) j rfl hcm hctor huni
    (hrf j) (hlvC j)
    (fun h0 hpol => by
      rcases hpf (selection_prop node.a _ h0 hpol).1 hpol j rfl hm hcm
        (witness_fields_length node.a w hwr hm j hcm) with
        ⟨h1, ⟨h2, h3, h4⟩ | hag⟩ | hemp
      · refine Or.inl ⟨h1, Or.inl ⟨h2, h3, h4 _ fun v hv => ?_⟩⟩
        obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hv
        exact hls l hl'
      · exact Or.inl ⟨h1, Or.inr hag⟩
      · exact Or.inr (hemp _))
    (spineFacts_of_hsound (mkM P μ) σ ρ hfit _ w.minor hr hrs) ml mr

/-- ι at a group's recursor, from a large-elimination condition that may read
the redex: the witness (its constructor, recursor member and fields), the
left-hand side's typing, its soundness and bound (`IotaAgree`). -/
theorem iota_at_gen (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {E E' Efin : ResolvedEnv} {f rr : Nat}
    {rm fm : CheckedMember} {node : RecNode E E' f rr rm} (hG : GroupFaith P μ fm node)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m) (hrm : E'.members rr = some rm)
    (hrf : ∀ i : Fin node.a.constructors.length, RecFieldsDirect node.a.family.ref (policyFamilyLevels node.a.family)
      node.a.family.parameters.length node.a.family.indices.length (node.a.constructorViews i).fields 0)
    (hlvC : ∀ i : Fin node.a.constructors.length,
      exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true)
    (hpf : ∀ (E'' : ResolvedEnv), (∀ r m, E''.members r = some m → Efin.members r = some m) →
      ∀ (w : IotaWitness E''), w.recRef = rr → ∀ (σ : Nat → Nat) (n : Nat) (Γ : LCtx) (T : Expr Nat)
        (ρ : Nat → PSet.{4}) (hl : HasTyT E'' n Γ (iotaLhsOf w) T), HSoundT (mkM P μ) σ hl →
        (∃ (N : Nat) (Lv : Nat → PSet.{4} → Prop), Good (mkM P μ) N Lv ∧ LOKt σ N K hl) →
        Fits (mkM P μ) σ Γ ρ → UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i : Fin node.a.constructors.length, w.ctorIdx = i.val → w.recMember = rm →
        w.ctorMember = node.a.constructors[i.val] → w.fields.length = (node.a.constructorViews i).fields.length →
        ((∀ T, T ∈ (node.a.constructorViews i).fields → occursConst node.a.family.ref T = false) ∧
        (((∀ k, k < (node.a.constructorViews i).fields.length →
          posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k)) (node.a.constructorViews i).resultIndices =
            none) ∧
        (∃ b, node.a.minorTypes[i.val]? = some (policyPi (liftFields (1 + i.val) (node.a.constructorViews i).fields 0) b)) ∧
        ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps, TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
          PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0)) ∨
        IotaAgree (mkM P μ) σ ρ node.a w i)) ∨
        ∀ vs, PropEmpty (mkM P μ) (σOf vs) (famDataOf node.a)) :
    IotaAt P μ K Efin rr := by
  intro E'' hsub w hwr σ n Γ T ρ hl il hN hr hrs hls hfit ml mr
  exact iota_at_gen_pt P hG hsubF hrm hrf hlvC hsub w hwr σ n Γ T ρ hl il hN hr hrs hls hfit ml mr
    (hpf E'' hsub w hwr σ n Γ T ρ hl il hN hfit)

/-- ι at a group's recursor (the large-elimination condition independent of the redex). -/
theorem iota_at (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {E E' Efin : ResolvedEnv} {f rr : Nat}
    {rm fm : CheckedMember} {node : RecNode E E' f rr rm} (hG : GroupFaith P μ fm node)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m) (hrm : E'.members rr = some rm)
    (hrf : ∀ i : Fin node.a.constructors.length, RecFieldsDirect node.a.family.ref (policyFamilyLevels node.a.family)
      node.a.family.parameters.length node.a.family.indices.length (node.a.constructorViews i).fields 0)
    (hlvC : ∀ i : Fin node.a.constructors.length,
      exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true)
    (hpf : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i : Fin node.a.constructors.length,
        ((∀ T, T ∈ (node.a.constructorViews i).fields → occursConst node.a.family.ref T = false) ∧
        (∀ k, k < (node.a.constructorViews i).fields.length →
          posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k)) (node.a.constructorViews i).resultIndices =
            none) ∧
        (∃ b, node.a.minorTypes[i.val]? = some (policyPi (liftFields (1 + i.val) (node.a.constructorViews i).fields 0) b)) ∧
        ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps, TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
          PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0)) ∨
        ∀ vs, PropEmpty (mkM P μ) (σOf vs) (famDataOf node.a)) :
    IotaAt P μ K Efin rr :=
  iota_at_gen P hG hsubF hrm hrf hlvC fun _ _ _ _ _ _ _ _ _ _ _ _ _ hU hpol i _ _ _ _ =>
    (hpf hU hpol i).imp (fun ⟨h1, h2, h3, h4⟩ => ⟨h1, Or.inl ⟨h2, h3, h4⟩⟩) id

end PSet

end Rcic.F3
