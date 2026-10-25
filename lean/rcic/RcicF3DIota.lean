import rcic.RcicF3DRec

/-!
# F3 D-8: ι and the group's table entries, with δ-hidden fields

`ConvT`'s ι fires on `DerivedIota`, whose witness classifies the constructor's
fields syntactically (`analyzeFields`: family-free or a literal family
application). A constructor with a δ-hidden field has no witness, so ι is
vacuous there; a constructor with a witness has literal fields, which
admission's shapes place in the direct class
(`recFieldsDirect_of_analyzeFields`), so `iota_group` applies unchanged.

The family's table entry is the normalized data's value; it is the original
data's value only at instances where the fields' typings are bounded, which
is what every use needs (`GroupFaithB`, the family clause bounded by the
recursor's instance bound). closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-! ### constructors with a witness have literal fields -/

theorem analyzeFields_mem {f : Nat} : (Fs : List (Expr Nat)) → {ks : List RecKind} → analyzeFields f Fs = some ks →
    ∀ A, A ∈ Fs → ∃ k, analyzeField f A = some k
  | [], _, _, _, hA => absurd hA (List.not_mem_nil _)
  | A :: Fs, ks, h, B, hB => by
      simp only [analyzeFields] at h
      cases ha : analyzeField f A with
      | none => rw [ha] at h; cases h
      | some k =>
          rw [ha] at h
          cases hr : analyzeFields f Fs with
          | none => rw [hr] at h; cases h
          | some ks' =>
              rcases List.mem_cons.mp hB with rfl | hB
              · exact ⟨k, ha⟩
              · exact analyzeFields_mem Fs hr B hB

/-- A field with a kind is family-free or a literal family application. -/
theorem analyzeField_cases {f : Nat} {A : Expr Nat} {k : RecKind} (h : analyzeField f A = some k) :
    occursConst f A = false ∨ isFamilyApp f A = true := by
  unfold analyzeField at h
  cases ho : occursConst f A with
  | false => exact Or.inl rfl
  | true =>
      rw [ho] at h
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hi : isFamilyApp f A with
      | true => exact Or.inr rfl
      | false =>
          rw [hi] at h
          simp only [Bool.false_eq_true, if_false] at h
          cases h

/-- A field with a kind is its own normal form. -/
theorem normField_eq_self_of_kind {E : ResolvedEnv} {f : Nat} (hop : ∀ ls, transparentBody E f ls = none)
    (fuel : Nat) {A : Expr Nat} {k : RecKind} (h : analyzeField f A = some k) : normField E fuel f A = A := by
  rcases analyzeField_cases h with ho | hi
  · exact normField_free ho
  · obtain ⟨ls, args, hsp, _⟩ := isFamilyApp_spine hi
    exact normField_eq_self_of_head hop fuel hsp

/-- **A constructor admitting an ι witness has literal fields**: under admission's
shapes, its fields are family-free or the family at the parameter locals and
family-free indices. -/
theorem recFieldsDirect_of_analyzeFields {E : ResolvedEnv} {f nu np nq fuel : Nat} (hFF : FamFreeBodies E f)
    (hop : ∀ ls, transparentBody E f ls = none) (Fs : List (Expr Nat)) (shapes : List FieldShape)
    (hs : fieldShapesFuel E fuel f nu np nq np Fs = some shapes)
    (hsh : ∀ s, s ∈ shapes → s = .nonrecursive ∨ s = .recursive 0)
    {ks : List RecKind} (hk : analyzeFields f Fs = some ks) :
    RecFieldsDirect f ((List.range nu).map Level.param) np nq Fs 0 := by
  have hdir := normFields_direct hFF Fs 0 shapes (by rw [Nat.add_zero]; exact hs) hsh
  have hmap : Fs.map (normField E fuel f) = Fs := by
    rw [List.map_congr_left (g := id) fun A hA => by
      obtain ⟨k, hk'⟩ := analyzeFields_mem Fs hk A hA
      exact normField_eq_self_of_kind hop fuel hk']
    exact List.map_id Fs
  rw [hmap] at hdir
  exact hdir

/-! ### the group's table entries, with the family at bounded instances -/

theorem σOf_le {vs : List Nat} {b : Nat} (hvs : ∀ v, v ∈ vs → v ≤ b) (i : Nat) : σOf vs i ≤ b := by
  unfold σOf
  rw [List.getD_eq_getElem?_getD]
  cases h : vs[i]? with
  | none => exact Nat.zero_le _
  | some v => exact hvs v (List.getElem?_mem h)

/-- The family instance of a bounded instance is bounded. -/
theorem famLevels_le {E : ResolvedEnv} (fam : PolicyFamilyView E) {vs : List Nat} {b : Nat}
    (hvs : ∀ v, v ∈ vs → v ≤ b) :
    ∀ v, v ∈ (policyFamilyLevels fam).map (evalTotal (σOf vs)) → v ≤ b := by
  intro v hv
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
  exact σOf_le hvs i

theorem famLevels_length {E : ResolvedEnv} (fam : PolicyFamilyView E) (vs : List Nat) :
    ((policyFamilyLevels fam).map (evalTotal (σOf vs))).length = fam.member.arity := by
  simp [policyFamilyLevels]

/-- A group's table entries are its values: constructors and recursor at every
instance, the family at instances within the recursor's bound `K rr`. -/
structure GroupFaithB (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) {E E' : ResolvedEnv}
    {f rr : Nat} {rm : CheckedMember} (fm : CheckedMember) (node : RecNode E E' f rr rm) : Prop where
  famB : ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → vs.length = node.a.family.member.arity →
    Equiv (μ f vs) (piLam (mkM P μ) (σOf vs) (famEnd (mkM P μ) W4 (σOf vs) (famDataOf node.a)) ρ0 fm.mtype)
  ctor : ∀ (i : Fin node.a.constructors.length) vs, Equiv (μ (f + 1 + i.val) vs)
    (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf node.a) i.val (nfOf (famDataOf node.a) i.val))
      ρ0 (node.a.constructors[i.val]).mtype)
  recur : ∀ vs, Equiv (μ rr vs) (piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf node.a)) ρ0 rm.mtype)
  famTy : fm.mtype = famType (famDataOf node.a)
  bounded : FamBounded (famDataOf node.a) node.a.family.member.arity
  ctorBounded : ∀ i : Fin node.a.constructors.length,
    exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true

/-- The family's value at a recursor instance within the bound. -/
theorem groupFaithB_famAt (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {E E' : ResolvedEnv}
    {f rr : Nat} {rm fm : CheckedMember} {node : RecNode E E' f rr rm} (hG : GroupFaithB P μ K fm node)
    (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr) :
    Equiv (μ node.a.family.ref ((policyFamilyLevels node.a.family).map (evalTotal (σOf vs))))
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)) := by
  rw [node.fam]
  refine (hG.famB _ (famLevels_le node.a.family hvs) (famLevels_length node.a.family vs)).trans ?_
  rw [hG.famTy]
  exact famVal_levels (mkM P μ) (k := node.a.family.member.arity) (σOf_policyFamilyLevels_agree _ vs) W4 _ hG.bounded

/-- A constructor's value at a recursor instance. -/
theorem groupFaithB_ctorAt (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {E E' : ResolvedEnv}
    {f rr : Nat} {rm fm : CheckedMember} {node : RecNode E E' f rr rm} (hG : GroupFaithB P μ K fm node)
    (vs : List Nat) (i : Fin node.a.constructors.length) :
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

/-! ### ι at the group's recursor -/

/-- **ι at a group's recursor with δ-hidden fields.** Only constructors with
literal fields have witnesses; for them `iota_group` applies. -/
theorem iota_at_D (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {E E' Efin : ResolvedEnv} {f rr : Nat}
    {rm fm : CheckedMember} {node : RecNode E E' f rr rm} (hG : GroupFaithB P μ K fm node)
    (hsubF : ∀ r m, E'.members r = some m → Efin.members r = some m) (hrm : E'.members rr = some rm)
    (hFF : FamFreeBodies node.E0 node.a.family.ref) (hop : ∀ ls, transparentBody node.E0 node.a.family.ref ls = none)
    (hsh : NoFunRec node)
    (hlvC : ∀ i : Fin node.a.constructors.length,
      exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true)
    (hpf : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i : Fin node.a.constructors.length,
        (∀ T, T ∈ (node.a.constructorViews i).fields → occursConst node.a.family.ref T = false) ∧
        (∀ k, k < (node.a.constructorViews i).fields.length →
          posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k)) (node.a.constructorViews i).resultIndices =
            none) ∧
        (∃ b, node.a.minorTypes[i.val]? = some (policyPi (liftFields (1 + i.val) (node.a.constructorViews i).fields 0) b)) ∧
        ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps, TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
          PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0)) :
    IotaAt P μ K Efin rr := by
  intro E'' hsub w hwr σ _ _ _ ρ _ _ _ hr hrs hls hfit ml mr
  have hm : w.recMember = rm := by
    have h1 := hsub _ _ w.hrec
    have h3 : Efin.members w.recRef = some rm := by rw [hwr]; exact hsubF _ _ hrm
    exact (Option.some.inj (h3.symm.trans h1)).symm
  obtain ⟨hnp, hnM, _, hfr⟩ := iota_align node.a w hwr hm
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
  -- the witness's constructor has literal fields
  have hrf : RecFieldsDirect node.a.family.ref (policyFamilyLevels node.a.family) node.a.family.parameters.length
      node.a.family.indices.length (node.a.constructorViews j).fields 0 := by
    have hst := (node.a.constructorViews j).storedType
    have hcpl := (node.a.constructorViews j).parameterCount
    have hctm : w.ctorMember.mtype = policyPi ((node.a.constructorViews j).parameters ++ (node.a.constructorViews j).fields)
        (foldApps (.const node.a.family.ref (policyFamilyLevels node.a.family))
          (policyParameterLocals (node.a.constructorViews j).parameters.length (node.a.constructorViews j).fields.length ++
            (node.a.constructorViews j).resultIndices)) := by rw [hcm]; exact hst
    have hnpar := w.hnpar
    rw [hctm, piCount_policyPi, piCount_foldApps _ (fun _ _ h => Expr.noConfusion h), List.length_append] at hnpar
    have hpeel := w.hpeel
    rw [hctm, show w.nparams + w.fields.length = ((node.a.constructorViews j).parameters ++
      (node.a.constructorViews j).fields).length by rw [List.length_append]; omega, peelPis_policyPi] at hpeel
    have hdoms : w.ctorDoms = (node.a.constructorViews j).parameters ++ (node.a.constructorViews j).fields :=
      (congrArg Prod.fst (Option.some.inj hpeel)).symm
    have hkinds := w.hkinds
    rw [hdoms, hnp, ← hcpl, List.drop_left, hfr] at hkinds
    exact recFieldsDirect_of_analyzeFields hFF hop _ _ (node.h14.analyzed j) (hsh j) hkinds
  have hbnd : ∀ v, v ∈ w.ls.map (evalTotal σ) → v ≤ K rr := by
    intro v hv
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
    exact hls l hl
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
  exact iota_group W4 node.a w hwr hm σ ρ (hG.recur _) (groupFaithB_famAt P hG _ hbnd) j rfl hcm hctor huni
    hrf (hlvC j)
    (fun h0 hpol => by
      obtain ⟨h1, h2, h3, h4⟩ := hpf (selection_prop node.a _ h0 hpol).1 hpol j
      exact Or.inl ⟨h1, Or.inl ⟨h2, h3, h4 _ hbnd⟩⟩)
    (spineFacts_of_hsound (mkM P μ) σ ρ hfit _ w.minor hr hrs) ml mr

end PSet

end Rcic.F3
