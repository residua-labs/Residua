import rcic.RcicAnnIotaWf

/-!
# M2-f (5a) — the concrete ι at a group's recursor

At an environment containing a group with its recursor (`groupRecEnvA`, the 05 §3 layout), the
concrete ι (`iotaFnA`, M2-f (2)) on the recursor's spine at its telescope arity, with a major headed
by the group's `j`-th constructor in candidate order, computes 05 §14's reduct
(`iotaFnA_groupRecA`): the `j`-th minor applied to the constructor's fields, a recursive call after
each directly recursive one and the λ-wrapped call after a function-recursive one (`rhsArgsA`), along the constructor telescope after the recursor-side
parameters at the constructor-side levels. Each check the two layers make is a law of the builders:
`iotaGroupA` reads the classes, the family from the recursor type's last domain, the layout and the
counts (`piCountA_recTypeA`, `piBodyA_recTypeA`, `piCountA` of the family view); `iotaReductA`
reads the arities, the shapes through erasure (`CtorViewA.shapes`), the minor's slot, and the field walk
(`fieldsTelA_ctorFieldsA`: every recursive domain of a built telescope passes `shapeGuardA`, a
function-recursive one included: R-NoFunRec-1 step 1 (1c-γ)).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) builder laws the layers read -/

theorem piCountA_ctorFieldsA (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (σ : SubstA) →
    piCountA (ctorFieldsA f ls w pl σ fs res).1 = fs.length
  | [], _, _ => piCountA_foldAppsA_of_not_pi _ _ (fun _ _ _ _ e => ExprA.noConfusion e)
  | .plain _ _ :: fs, pl, σ => by
      simp only [ctorFieldsA, piCountA, piCountA_ctorFieldsA f ls w res fs, List.length_cons]
  | .drec _ :: fs, pl, σ => by
      simp only [ctorFieldsA, piCountA, piCountA_ctorFieldsA f ls w res fs, List.length_cons]
  | .frec _ _ _ _ :: fs, pl, σ => by
      simp only [ctorFieldsA, piCountA, piCountA_ctorFieldsA f ls w res fs, List.length_cons]
  | .drecD _ _ :: fs, pl, σ => by
      simp only [ctorFieldsA, piCountA, piCountA_ctorFieldsA f ls w res fs, List.length_cons]

theorem piCountA_ctorTypeA (f : Nat) (ls : List Level) (w : Level) (mirrors : List (ExprA × Level))
    (fields : List FieldA) (res : List ExprA) :
    piCountA (ctorTypeA f ls w mirrors fields res) = mirrors.length + fields.length := by
  rw [ctorTypeA, piCountA_piTelA, piCountA_ctorFieldsA]

/-- the normalized read keeps the constructor's Π arity (R-NoDeltaRec-3b): `norm` preserves the
    field count. -/
theorem GroupCtorA.normA_getD_piCount {I : IotaIfaceA} {E : ResolvedEnvA} {f : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} (c : GroupCtorA I E f fm fv) :
    piCountA (c.member.normA.getD c.member.mtypeA) = piCountA c.member.mtypeA := by
  rw [c.normA_getD, c.view.stored, piCountA_ctorTypeA, piCountA_ctorTypeA, List.length_map]

/-- a function-recursive field's domain has exactly its inner binders' count. -/
theorem piCountA_frecDomA (f : Nat) (ls : List Level) (w : Level) (pl : List ExprA) (σ : SubstA)
    (ds : List (ExprA × Level)) (idx : List ExprA) :
    piCountA (frecDomA f ls w pl σ ds idx).1 = ds.length := by
  rw [frecDomA_eq, piCountA_ctorFieldsA, List.length_map]

/-- a function-recursive field's domain ends in the family: its body is constant-headed. -/
theorem spineHeadConstA_piBodyA_frecDomA (f : Nat) (ls : List Level) (w : Level) (idx : List ExprA) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (σ : SubstA) →
    spineHeadConstA (piBodyA (frecDomA f ls w pl σ ds idx).1) = true
  | [], pl, σ => by
      show spineHeadConstA (piBodyA (foldAppsA (.const f ls) (pl ++ idx.map (substA σ)))) = true
      rw [(piBodyA_of_const (e := foldAppsA (.const f ls) (pl ++ idx.map (substA σ))) (r := f) (ls := ls)
        (by simp only [foldAppsA_const_head])).1]
      simp only [spineHeadConstA, foldAppsA_const_head]
  | (D, u) :: ds, pl, σ => spineHeadConstA_piBodyA_frecDomA f ls w idx ds (pl.map (liftA 0 1)) σ.up

/-- the fields walk a built telescope: a Π at every field, every recursive domain passing
    `shapeGuardA` (05 §8, the guard under which `familyIdxA` commutes with substitution; a
    function-recursive field's a Π-telescope of exactly its inner binders over a constant-headed
    body). -/
theorem fieldsTelA_ctorFieldsA (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (∀ x ∈ fs, x.NoDelta) → (pl : List ExprA) → (σ : SubstA) → (xs : List ExprA) →
    xs.length = fs.length →
    fieldsTelA xs (fs.map FieldA.shape) (ctorFieldsA f ls w pl σ fs res).1 = true
  | [], _, _, _, [], _ => rfl
  | .drecD _ _ :: _, hnd, _, _, _ :: _, _ => (hnd _ (List.mem_cons_self _ _)).elim
  | .plain _ _ :: fs, hnd, pl, σ, x :: xs, h => by
      simp only [ctorFieldsA, List.map, FieldA.shape, fieldsTelA, shapeGuardA, Bool.true_and]
      rw [instantiate0A_ctorFieldsA_plain]
      exact fieldsTelA_ctorFieldsA f ls w res fs (fun y hy => hnd y (List.mem_cons_of_mem _ hy)) pl
        (SubstA.cons x σ) xs (Nat.succ.inj h)
  | .drec idx :: fs, hnd, pl, σ, x :: xs, h => by
      simp only [ctorFieldsA, List.map, FieldA.shape, fieldsTelA, shapeGuardA]
      rw [instantiate0A_ctorFieldsA_drec]
      have hc : spineHeadConstA (foldAppsA (.const f ls) (pl ++ idx.map (substA σ))) = true := by
        simp only [spineHeadConstA, foldAppsA_const_head]
      rw [hc, Bool.true_and]
      exact fieldsTelA_ctorFieldsA f ls w res fs (fun y hy => hnd y (List.mem_cons_of_mem _ hy)) pl σ xs
        (Nat.succ.inj h)
  | .frec B uB Bs idx :: fs, hnd, pl, σ, x :: xs, h => by
      have hg : shapeGuardA (frecDomA f ls w pl σ ((B, uB) :: Bs) idx).1 (.recursive (Bs.length + 1)) =
          true := by
        show ((piDomListA (frecDomA f ls w pl σ ((B, uB) :: Bs) idx).1).length == Bs.length + 1 &&
          spineHeadConstA (piBodyA (frecDomA f ls w pl σ ((B, uB) :: Bs) idx).1)) = true
        rw [piDomListA_length, piCountA_frecDomA, spineHeadConstA_piBodyA_frecDomA]
        simp
      show (shapeGuardA (frecDomA f ls w pl σ ((B, uB) :: Bs) idx).1 (.recursive (Bs.length + 1)) &&
        fieldsTelA xs (fs.map FieldA.shape)
          (instantiate0A x (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res).1)) = true
      rw [instantiate0A_ctorFieldsA_drec, hg, Bool.true_and]
      exact fieldsTelA_ctorFieldsA f ls w res fs (fun y hy => hnd y (List.mem_cons_of_mem _ hy)) pl σ xs
        (Nat.succ.inj h)
  | [], _, _, _, _ :: _, h => nomatch h
  | .plain _ _ :: _, _, _, _, [], h => nomatch h
  | .drec _ :: _, _, _, _, [], h => nomatch h
  | .frec _ _ _ _ :: _, _, _, _, [], h => nomatch h
  | .drecD _ _ :: _, _, _, _, [], h => nomatch h

theorem piCountA_famView {fm : CheckedMemberA} (fv : FamViewA fm) :
    piCountA fm.mtypeA = fv.params.length + fv.indices.length := by
  rw [fv.stored, piCountA_piTelA, List.length_append]
  rfl

theorem spineHeadRefA_foldAppsA_const (c : Nat) (ls : List Level) (xs : List ExprA) :
    spineHeadRefA (foldAppsA (.const c ls) xs) = some c := by
  simp only [spineHeadRefA, foldAppsA_const_head]

/-! ## (2) the group in `E` -/

section Group
variable {I : IotaIfaceA} {E E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
  {cs : List (GroupCtorA I E₀ f fm fv)}

/-- the layout: the `j`-th constructor in candidate order is member `f + 1 + j`. -/
theorem ref_of_layoutA (hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length)
    {j : Nat} {gc : GroupCtorA I E₀ f fm fv} (hgc : cs.reverse[j]? = some gc) :
    gc.ref = f + 1 + j ∧ j < cs.length := by
  have hj : j < cs.reverse.length := by
    rcases (List.getElem?_eq_some_iff.mp hgc) with ⟨hj, _⟩
    exact hj
  have hj' : j < cs.length := by simpa using hj
  have h1 : (cs.reverse.map GroupCtorA.ref)[j]? = some gc.ref := by
    rw [List.getElem?_map, hgc]; rfl
  rw [hlay, List.getElem?_eq_getElem (by simpa using hj'), List.getElem_range'] at h1
  injection h1 with h1
  exact ⟨by omega, hj'⟩

theorem mem_of_reverse_getElem? {j : Nat} {gc : GroupCtorA I E₀ f fm fv} (hgc : cs.reverse[j]? = some gc) :
    gc ∈ cs := by
  obtain ⟨h, he⟩ := List.getElem?_eq_some_iff.mp hgc
  exact List.mem_reverse.mp (he ▸ List.getElem_mem h)

/-- the group's members in `E`. -/
theorem members_groupRecA (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length) {rec : GroupRecA I E₀ f fm fv cs}
    (hpre : PrefixA (groupRecEnvA cs rec) E) :
    E.members (f + 1 + cs.length) = some rec.member ∧ E.members f = some fm ∧
    ∀ {j : Nat} {gc : GroupCtorA I E₀ f fm fv}, cs.reverse[j]? = some gc → E.members gc.ref = some gc.member := by
  refine ⟨hpre _ _ (members_groupRecEnvA cs rec), ?_, fun {j gc} hgc => ?_⟩
  · apply hpre
    unfold groupRecEnvA
    rw [members_extendEnvA_ne _ _ _ (by omega)]
    exact members_groupEnvA_family hfresh
  · obtain ⟨href, hj⟩ := ref_of_layoutA hlay hgc
    apply hpre
    unfold groupRecEnvA
    rw [members_extendEnvA_ne _ _ _ (by omega)]
    exact members_groupEnvA_ctor hfresh (mem_of_reverse_getElem? hgc)

/-- `iotaGroupA` at the group's recursor and its `j`-th constructor. -/
theorem iotaGroupA_groupRecA (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length) (hcls : fm.mclass = .inductiveM)
    {rec : GroupRecA I E₀ f fm fv cs} (hpre : PrefixA (groupRecEnvA cs rec) E)
    {j : Nat} {gc : GroupCtorA I E₀ f fm fv} (hgc : cs.reverse[j]? = some gc) :
    iotaGroupA E (f + 1 + cs.length) gc.ref =
      some ⟨rec.member, gc.member, fm, gc.ref, f, fv.params.length, fv.indices.length, cs.length, j⟩ := by
  obtain ⟨hr, hf, hc⟩ := members_groupRecA hfresh hlay hpre
  have hcm := hc hgc
  obtain ⟨href, hj⟩ := ref_of_layoutA hlay hgc
  have hlast := piDomsA_recTypeA_getLast f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
    (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData)
  have hbody := piBodyA_recTypeA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
    (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData)
  have hcnt := piCountA_recTypeA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
    (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData)
  simp only [List.length_map, List.length_reverse] at hlast hbody hcnt
  have hst : rec.member.mtypeA = groupRecTypeA fv cs rec.elim := rec.stored
  unfold groupRecTypeA at hst
  have hspine : (appsSpineA (piBodyA rec.member.mtypeA)).2.length = fv.indices.length + 1 := by
    rw [hst, hbody, appsSpineA_recBodyA]
  have hpc : piCountA rec.member.mtypeA = fv.params.length + 1 + cs.length + fv.indices.length + 1 := by
    rw [hst, hcnt]
  have hfc := piCountA_famView fv
  have hgcnt : groupCountsA rec.member fm (f + 1 + cs.length - f - 1) =
      some (fv.params.length, fv.indices.length) := by
    have hk : f + 1 + cs.length - f - 1 = cs.length := by omega
    have hp : piCountA fm.mtypeA - fv.indices.length = fv.params.length := by rw [hfc]; omega
    unfold groupCountsA
    rw [hspine]
    simp only
    rw [if_pos ⟨by rw [hfc]; exact Nat.le_add_left _ _, by rw [hk, hp, hpc]⟩, hp]
  unfold iotaGroupA
  rw [hr, hcm]
  simp only
  rw [if_pos ⟨rec.hcls, gc.hcls⟩, hst, hlast]
  simp only
  rw [appsSpineA_majorDom]
  simp only
  rw [hf]
  simp only
  rw [if_pos ⟨hcls, by omega, by omega⟩, hgcnt]
  have e1 : f + 1 + cs.length - f - 1 = cs.length := by omega
  have e2 : gc.ref - f - 1 = j := by omega
  rw [e1, e2]

/-- the group's recursor has a constructor, as the step reads it (`recHasCtorA`), exactly when the
    group does (O1-a). -/
theorem recHasCtorA_groupRecA (rec : GroupRecA I E₀ f fm fv cs) :
    recHasCtorA (f + 1 + cs.length) rec.member = true ↔ cs ≠ [] := by
  have hst : rec.member.mtypeA = groupRecTypeA fv cs rec.elim := rec.stored
  unfold groupRecTypeA at hst
  have hlast := piDomsA_recTypeA_getLast f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
    (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData)
  rw [← hst] at hlast
  unfold recHasCtorA
  rw [lastPiDomA_eq, hlast]
  show (match (appsSpineA _).1 with
    | .const f' _ => !(decide (f + 1 + cs.length = f' + 1))
    | _ => true) = true ↔ _
  rw [appsSpineA_majorDom]
  show (!(decide (f + 1 + cs.length = f + 1))) = true ↔ _
  constructor
  · intro h hcs
    subst hcs
    simp at h
  · intro hcs
    have hlen : cs.length ≠ 0 := fun h => hcs (List.eq_nil_of_length_eq_zero h)
    have hne : f + 1 + cs.length ≠ f + 1 := by omega
    simp [hne]


/-- a sort that is positive at every valuation is not zero. -/
theorem levelIsZero_false_of_uniformType {u : Level} (h : UniformType u) : levelIsZero u = false := by
  cases hz : levelIsZero u with
  | false => rfl
  | true =>
      exfalso
      have hp : UniformProp u := (levelUniformZero_iff u).1 hz
      have h0 := h (fun _ => 0)
      rw [hp (fun _ => 0)] at h0
      exact Nat.lt_irrefl 0 h0

/-- O1-b-1: the recursor of a `Type` family's group is no unit group: its major binder carries the
    family's sort. -/
theorem unitGroupA_groupRecA_of_type (rec : GroupRecA I E₀ f fm fv cs) (hUT : UniformType fv.sort) :
    unitGroupA (f + 1 + cs.length) rec.member = false := by
  have hst : rec.member.mtypeA = groupRecTypeA fv cs rec.elim := rec.stored
  unfold groupRecTypeA at hst
  exact unitGroupA_of_majorSort (by rw [hst, piDomListA_recTypeA_reverse])
    (levelIsZero_false_of_uniformType hUT)

/-- W-1 (a): the recursor of a `Type` family's group is no struct group: its major binder carries the
    family's sort. -/
theorem structGroupA_groupRecA_of_type (rec : GroupRecA I E₀ f fm fv cs) (hUT : UniformType fv.sort) :
    structGroupA (f + 1 + cs.length) rec.member = false := by
  have hst : rec.member.mtypeA = groupRecTypeA fv cs rec.elim := rec.stored
  unfold groupRecTypeA at hst
  exact structGroupA_of_majorSort (by rw [hst, piDomListA_recTypeA_reverse])
    (levelIsZero_false_of_uniformType hUT)

/-- a unit group is no struct group. -/
theorem structGroupA_false_of_unit {r : Nat} {m : CheckedMemberA} (h : unitGroupA r m = true) :
    structGroupA r m = false := by
  cases hs : structGroupA r m with
  | false => rfl
  | true => rw [unitGroupA_false_of_struct hs] at h; exact Bool.noConfusion h

/-- what the struct test reads, when it holds. -/
theorem structGroupA_true_inv {r : Nat} {m : CheckedMemberA} (h : structGroupA r m = true) :
    ∃ D uD Dm um Dmot umot rest,
      (piDomListA m.mtypeA).reverse = (D, uD) :: (Dm, um) :: (Dmot, umot) :: rest ∧
      (∃ f ls, (appsSpineA D).1 = .const f ls ∧ r = f + 2) ∧ levelIsZero uD = true ∧
      (∃ D' u w v, Dmot = .pi D' u (.sort w) v ∧ D = liftA 0 2 D' ∧ levelIsZero w = false) := by
  unfold structGroupA at h
  split at h
  next D uD Dm um Dmot umot rest hL =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, _⟩ := h
    refine ⟨D, uD, Dm, um, Dmot, umot, rest, hL, ?_, h2, ?_⟩
    · split at h1
      next f ls hf => exact ⟨f, ls, hf, of_decide_eq_true h1⟩
      next => exact absurd h1 (by decide)
    · split at h3
      next D' u w v =>
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at h3
        exact ⟨D', u, w, v, rfl, of_decide_eq_true h3.1, h3.2⟩
      next => exact absurd h3 (by decide)
  next => exact absurd h (by decide)

theorem paramLocalsA_snoc : (n : Nat) → ∃ L, paramLocalsA (n + 1) = L ++ [.bvar 0]
  | 0 => ⟨[], rfl⟩
  | n + 1 => by
      obtain ⟨L, hL⟩ := paramLocalsA_snoc n
      refine ⟨.bvar (n + 1) :: L, ?_⟩
      show ExprA.bvar (n + 1) :: paramLocalsA (n + 1) = _
      rw [hL]
      rfl

/-- a term lifted twice at `0` contains neither `bvar 0` nor `bvar 1` free: it is no application to
    `bvar 0`. -/
theorem app_bvar_zero_ne_liftA_two (G D' : ExprA) : ExprA.app G (.bvar 0) ≠ liftA 0 2 D' := by
  intro h
  cases D'
  case app g' x' =>
    injection h with _ hx
    cases x'
    case bvar j =>
      have hj : liftA 0 2 (.bvar j) = .bvar (j + 2) := if_pos (Nat.zero_le j)
      rw [hj] at hx
      injection hx with hx
      omega
    all_goals exact ExprA.noConfusion hx
  case bvar j =>
    have hj : liftA 0 2 (.bvar j) = .bvar (j + 2) := if_pos (Nat.zero_le j)
    rw [hj] at h
    exact ExprA.noConfusion h
  all_goals exact ExprA.noConfusion h

/-- the major's domain over at least one index ends in the last index, `bvar 0`: it is no domain lifted
    twice at `0`. -/
theorem famLocalsA_ne_liftA_two (f : Nat) (ls : List Level) (np ni a : Nat) (D' : ExprA) :
    liftA (ni + 1) a (famLocalsA f ls np (ni + 1)) ≠ liftA 0 2 D' := by
  obtain ⟨L, hL⟩ := paramLocalsA_snoc ni
  rw [famLocalsA, hL, ← List.append_assoc, foldAppsA_append]
  show ExprA.app (liftA (ni + 1) a (foldAppsA (.const f ls) ((paramLocalsA np).map (liftA 0 (ni + 1)) ++ L)))
    (liftA (ni + 1) a (.bvar 0)) ≠ _
  rw [show liftA (ni + 1) a (.bvar 0) = .bvar 0 from if_neg (Nat.not_succ_le_zero ni)]
  exact app_bvar_zero_ne_liftA_two _ D'

/-- W-1 (b′), THE SOUNDNESS OF THE STRUCT TEST at a group's recursor: one constructor, no index, and a
    motive whose sort is not zero (an AnySort recursor). -/
theorem structGroupA_groupRecA_true (rec : GroupRecA I E₀ f fm fv cs)
    (hb : structGroupA (f + 1 + cs.length) rec.member = true) :
    cs.length = 1 ∧ fv.indices = [] ∧ levelIsZero (rec.elim.motiveLevel fm.arity) = false := by
  obtain ⟨D, uD, Dm, um, Dmot, umot, rest, hL, ⟨f', ls', hD, hr⟩, _, ⟨D', u', w', v', hmot, hDD, hw⟩⟩ :=
    structGroupA_true_inv hb
  have hst : rec.member.mtypeA = groupRecTypeA fv cs rec.elim := rec.stored
  unfold groupRecTypeA at hst
  rw [hst, piDomListA_recTypeA_reverse] at hL
  injection hL with h1 hL'
  injection h1 with hD1 _
  subst hD1
  have hhead := appsSpineA_majorDom f (canonLevelsA fm.arity) fv.params.length fv.indices.length
    ((cs.reverse.map GroupCtorA.minorData).length + 1)
  rw [hD] at hhead
  injection hhead with hf _
  subst hf
  have hcs : cs.length = 1 := by omega
  have hni : fv.indices = [] := by
    cases hI : fv.indices with
    | nil => rfl
    | cons i is =>
        exfalso
        rw [hI] at hDD
        exact famLocalsA_ne_liftA_two f' _ _ is.length _ D' hDD
  refine ⟨hcs, hni, ?_⟩
  have hcds : (cs.reverse.map GroupCtorA.minorData).length = 1 := by
    rw [List.length_map, List.length_reverse, hcs]
  obtain ⟨cd, hcd⟩ : ∃ cd, cs.reverse.map GroupCtorA.minorData = [cd] := by
    match h : cs.reverse.map GroupCtorA.minorData, hcds with
    | [cd], _ => exact ⟨cd, rfl⟩
  rw [hcd, hni] at hL'
  simp only [liftDomsA, List.append_nil, minorDomsA, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append, List.cons_append] at hL'
  injection hL' with _ hL2
  injection hL2 with hm2 _
  simp only [motTyA, piTelA] at hm2
  injection hm2 with hm2 _
  rw [hmot] at hm2
  injection hm2 with _ _ hs _
  injection hs with hs
  rw [hs]
  exact hw

/-- W-1 (b′): the recursor of a group eliminating into `Prop` alone is no struct group. -/
theorem structGroupA_groupRecA_of_propOnly (rec : GroupRecA I E₀ f fm fv cs) (hpo : rec.elim = .propOnly) :
    structGroupA (f + 1 + cs.length) rec.member = false := by
  cases hb : structGroupA (f + 1 + cs.length) rec.member with
  | false => rfl
  | true =>
      have h := (structGroupA_groupRecA_true rec hb).2.2
      rw [hpo] at h
      change levelIsZero .zero = false at h
      exact absurd h (by decide)

/-- the profile's reading of a group's recursor: its last binder is the major's, its binder after the
    parameters the motive's; a `Prop`-valued motive makes the recursor PropOnly. -/
theorem elim_propOnly_of_profile {rec : GroupRecA I E₀ f fm fv cs} (hcs : cs ≠ [])
    (h : (piDomsA rec.member.mtypeA).getLast? =
        some (liftA fv.indices.length ((cs.reverse.map GroupCtorA.minorData).length + 1)
          (famLocalsA f (canonLevelsA fm.arity) fv.params.length fv.indices.length)) →
      (appsSpineA (liftA fv.indices.length ((cs.reverse.map GroupCtorA.minorData).length + 1)
          (famLocalsA f (canonLevelsA fm.arity) fv.params.length fv.indices.length))).1 =
        .const f (canonLevelsA fm.arity) →
      f + 1 + cs.length ≠ f + 1 →
      ∀ M, (piDomsA rec.member.mtypeA)[fm.nparamsA]? = some M → piBodyA M = .sort .zero) :
    rec.elim = .propOnly := by
  have hst : rec.member.mtypeA = groupRecTypeA fv cs rec.elim := rec.stored
  unfold groupRecTypeA at hst
  have hlast := piDomsA_recTypeA_getLast f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
    (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData)
  have hmot := piDomsA_recTypeA_motive f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
    (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData)
  rw [← hst] at hlast hmot
  rw [fv.nparams] at hmot
  have hlen : cs.length ≠ 0 := fun h => hcs (List.eq_nil_of_length_eq_zero h)
  have h' := h hlast (appsSpineA_majorDom _ _ _ _ _) (by omega) _ hmot
  rw [piBodyA_motTyA] at h'
  cases he : rec.elim with
  | propOnly => rfl
  | anySort => rw [he] at h'; cases h'

/-- under `PropElimOnlyA`, the recursor of a Prop-profile group with a constructor is PropOnly. -/
theorem elim_propOnly_of_propElimOnlyA (hPE : PropElimOnlyA E)
    (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length) (hcls : fm.mclass = .inductiveM)
    {rec : GroupRecA I E₀ f fm fv cs} (hpre : PrefixA (groupRecEnvA cs rec) E)
    (hprop : UniformProp fv.sort) (hcs : cs ≠ [])
    (hun : unitGroupA (f + 1 + cs.length) rec.member = false) : rec.elim = .propOnly := by
  obtain ⟨hr, hf, _⟩ := members_groupRecA hfresh hlay hpre
  exact elim_propOnly_of_profile hcs fun hlast hhead hne =>
    hPE _ _ _ f _ fm fv.sort hr rec.hcls hlast hhead hf hcls fv.piBody hprop hne hun

/-- W-1 (c): under `PropElimStructA`, the recursor of a Prop-profile group with a constructor, neither a
    unit nor a struct group, is PropOnly. -/
theorem elim_propOnly_of_propElimStructA (hPE : PropElimStructA E)
    (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length) (hcls : fm.mclass = .inductiveM)
    {rec : GroupRecA I E₀ f fm fv cs} (hpre : PrefixA (groupRecEnvA cs rec) E)
    (hprop : UniformProp fv.sort) (hcs : cs ≠ [])
    (hun : unitGroupA (f + 1 + cs.length) rec.member = false)
    (hns : structGroupA (f + 1 + cs.length) rec.member = false) : rec.elim = .propOnly := by
  obtain ⟨hr, hf, _⟩ := members_groupRecA hfresh hlay hpre
  exact elim_propOnly_of_profile hcs fun hlast hhead hne =>
    hPE _ _ _ f _ fm fv.sort hr rec.hcls hlast hhead hf hcls fv.piBody hprop hne hun hns

end Group

/-! ## (3) THE ι AT THE GROUP'S RECURSOR -/

section Reduct
variable {I : IotaIfaceA} {E E₀ : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
  {cs : List (GroupCtorA I E₀ f fm fv)}

/-- 05 §14's checks and contractum at a group's recursor spine, the major a full application of the
    group's `j`-th constructor: the `j`-th minor applied to the fields with the recursive calls
    (`rhsArgsA`) along the constructor telescope at the recursor-side parameters and the
    constructor-side levels. -/
theorem iotaReductA_groupRecA (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    {rec : GroupRecA I E₀ f fm fv cs}
    {j : Nat} {gc : GroupCtorA I E₀ f fm fv}
    {ls lsC : List Level} {pre ps₁ fs : List ExprA} {minor : ExprA}
    (hprel : pre.length = fv.params.length + 1 + cs.length + fv.indices.length)
    (hls : ls.length = rec.member.arity) (hps₁ : ps₁.length = fv.params.length)
    (hfs : fs.length = gc.view.fields.length)
    (hmin : pre[fv.params.length + 1 + j]? = some minor) :
    iotaReductA ⟨f + 1 + cs.length, ls, pre, foldAppsA (.const gc.ref lsC) (ps₁ ++ fs)⟩
      ⟨rec.member, gc.member, fm, gc.ref, f, fv.params.length, fv.indices.length, cs.length, j⟩ =
      some (foldAppsA minor (rhsArgsA (.const (f + 1 + cs.length) ls) pre fv.params.length cs.length fs
        (gc.view.fields.map FieldA.shape)
        (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort) (pre.take fv.params.length)
          (consListA (pre.take fv.params.length) SubstA.id)
          ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels (ls.take fm.arity)))
          (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).1)) := by
  have hnp : fv.params.length = fm.nparamsA := fv.nparams
  have hgar : gc.member.arity = fm.arity := gc.harity
  have hrar : rec.member.arity = fm.arity + rec.elim.extra := rec.harity
  have hshapes : ctorShapesA f fv.params.length (gc.member.normA.getD gc.member.mtypeA) =
      some (gc.view.fields.map FieldA.shape) := by
    rw [hnp, gc.normA_getD]; exact gc.view.shapes hfresh.base
  have htakeL : (ls.take fm.arity).length = fm.arity := by
    rw [List.length_take, hls, hrar]; omega
  have htakeP : (pre.take fv.params.length).length = fm.nparamsA := by
    rw [List.length_take, hprel, ← hnp]; omega
  have happ := gc.applyTel_params (ls.take fm.arity) htakeL (pre.take fv.params.length) htakeP
  have hcp : piCountA (gc.member.normA.getD gc.member.mtypeA) =
      fv.params.length + gc.view.fields.length := by
    rw [gc.normA_getD, piCountA_ctorTypeA, gc.view.mirrors_length, hnp, List.length_map]
  have hdrop : (appsSpineA (foldAppsA (.const gc.ref lsC) (ps₁ ++ fs))).2.drop fv.params.length = fs := by
    rw [foldAppsA_const_head]
    simp only
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
  have hwalk := fieldsTelA_ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort)
    (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))
    ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels (ls.take fm.arity)))
    (gc.view.norm_noDelta_instLevels _)
    (pre.take fv.params.length)
    (consListA (pre.take fv.params.length) SubstA.id) fs
    (by rw [List.length_map, List.length_map]; exact hfs)
  rw [map_shape_instLevels, map_shape_norm] at hwalk
  have hpc : piCountA rec.member.mtypeA = fv.params.length + 1 + cs.length + fv.indices.length + 1 := by
    rw [rec.stored]
    unfold groupRecTypeA
    rw [piCountA_recTypeA]
    simp only [List.length_map, List.length_reverse]
  have hcond : gc.ref = gc.ref ∧ pre.length + 1 = piCountA rec.member.mtypeA ∧
      ls.length = rec.member.arity ∧
      (appsSpineA (foldAppsA (.const gc.ref lsC) (ps₁ ++ fs))).2.length =
        piCountA (gc.member.normA.getD gc.member.mtypeA) ∧
      gc.member.arity ≤ ls.length := by
    refine ⟨rfl, by rw [hprel, hpc], hls, ?_, by rw [hgar, hls, hrar]; omega⟩
    rw [foldAppsA_const_head]
    simp only [List.length_append]
    rw [hps₁, hfs, hcp]
  unfold iotaReductA
  simp only [spineHeadRefA_foldAppsA_const, Option.some_bind]
  split
  · simp only [hshapes, Option.some_bind, hmin, hgar, happ, hdrop, hwalk, if_true]
  · rename_i hne
    exact absurd ⟨trivial, hcond.2⟩ hne

/-- 05 §14 ON THE COPY: the recursor's spine at its telescope arity, the major a full application of
    the group's `j`-th constructor (its own parameters `ps₁`, its fields `fs`), reduces to the `j`-th
    minor applied to the fields with the recursive calls (`rhsArgsA`) along the constructor telescope
    at the recursor-side parameters and the constructor-side levels — at every group, a struct group
    included (W-1 (e): `main`'s ι; there the head step is the struct arm's, `structPosA`). -/
theorem iotaFnA_groupRecA (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length) (hcls : fm.mclass = .inductiveM)
    {rec : GroupRecA I E₀ f fm fv cs} (hpre : PrefixA (groupRecEnvA cs rec) E)
    {j : Nat} {gc : GroupCtorA I E₀ f fm fv} (hgc : cs.reverse[j]? = some gc)
    {ls lsC : List Level} {pre ps₁ fs : List ExprA} {minor : ExprA}
    (hprel : pre.length = fv.params.length + 1 + cs.length + fv.indices.length)
    (hls : ls.length = rec.member.arity) (hps₁ : ps₁.length = fv.params.length)
    (hfs : fs.length = gc.view.fields.length)
    (hmin : pre[fv.params.length + 1 + j]? = some minor) :
    iotaFnA E (foldAppsA (.const (f + 1 + cs.length) ls) (pre ++ [foldAppsA (.const gc.ref lsC) (ps₁ ++ fs)])) =
      some (foldAppsA minor (rhsArgsA (.const (f + 1 + cs.length) ls) pre fv.params.length cs.length fs
        (gc.view.fields.map FieldA.shape)
        (ctorFieldsA f (ls.take fm.arity) (instLevel (ls.take fm.arity) fv.sort) (pre.take fv.params.length)
          (consListA (pre.take fv.params.length) SubstA.id)
          ((gc.view.fields.map FieldA.norm).map (FieldA.instLevels (ls.take fm.arity)))
          (gc.view.res.map (instantiateLevelsA (ls.take fm.arity)))).1)) := by
  have hg := iotaGroupA_groupRecA hfresh hlay hcls hpre hgc
  have hs : recSpineA (foldAppsA (.const (f + 1 + cs.length) ls)
      (pre ++ [foldAppsA (.const gc.ref lsC) (ps₁ ++ fs)])) =
      some ⟨f + 1 + cs.length, ls, pre, foldAppsA (.const gc.ref lsC) (ps₁ ++ fs)⟩ :=
    recSpineA_of_spine (foldAppsA_const_head _ _ _)
  rw [iotaFnA_of_layers hs (spineHeadRefA_foldAppsA_const _ _ _) hg]
  exact iotaReductA_groupRecA hfresh hprel hls hps₁ hfs hmin

/-- O1-b-1: 05 §14 at a UNIT group (one constructor, no field): wherever ι fires on the recursor's spine
    at its telescope arity, the reduct is the minor itself — the major is the constructor at its
    parameters, and there is no field to pass. -/
theorem iotaFnA_unitGroupA (hfresh : GroupFreshA E₀ f fm (cs.map GroupCtorA.entry))
    (hlay : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length) (hcls : fm.mclass = .inductiveM)
    {rec : GroupRecA I E₀ f fm fv cs} (hpre : PrefixA (groupRecEnvA cs rec) E)
    {gc : GroupCtorA I E₀ f fm fv} (hgc : cs.reverse = [gc]) (hnf : gc.view.fields = [])
    {ls : List Level} {pre : List ExprA} {x minor e' : ExprA}
    (hprel : pre.length = fv.params.length + 1 + cs.length + fv.indices.length)
    (hls : ls.length = rec.member.arity) (hmin : pre[fv.params.length + 1]? = some minor)
    (h : iotaFnA E (foldAppsA (.const (f + 1 + cs.length) ls) (pre ++ [x])) = some e') : e' = minor := by
  have hgc0 : cs.reverse[0]? = some gc := by rw [hgc]; rfl
  have hcs1 : cs.length = 1 := by rw [← List.length_reverse, hgc]; rfl
  obtain ⟨hr, _, hcm⟩ := members_groupRecA hfresh hlay hpre
  have hcg := hcm hgc0
  obtain ⟨href, _⟩ := ref_of_layoutA hlay hgc0
  obtain ⟨s, c, g, hs, hc, hg, hred⟩ := iotaFnA_some h
  rw [recSpineA_of_spine (foldAppsA_const_head _ _ _)] at hs
  injection hs with hs
  subst hs
  obtain ⟨hrm, _, hctm, _, _, _, _, hlt1, hlt2, _⟩ := iotaGroupA_some hg
  rw [hr] at hrm
  injection hrm with hrm
  -- the group's family is `f`: the recursor type's last domain is the major's, headed by `f`
  obtain ⟨D, lsD, hD, hhead⟩ := iotaGroupA_lastDom hg
  rw [← hrm] at hD
  have hst : rec.member.mtypeA = groupRecTypeA fv cs rec.elim := rec.stored
  unfold groupRecTypeA at hst
  rw [hst, piDomsA_recTypeA_getLast] at hD
  injection hD with hD
  rw [← hD, appsSpineA_majorDom] at hhead
  injection hhead with hfam _
  -- so the major's head lies strictly between the family and the recursor: the constructor
  have hcr : c = gc.ref := by
    have h1 : f < c := by rw [hfam]; exact hlt1
    have h2 : c < f + 1 + cs.length := hlt2
    rw [hcs1] at h2
    rw [href]
    omega
  subst hcr
  rw [hcg] at hctm
  injection hctm with hctm
  obtain ⟨_, _, _, _, _, hargs, _⟩ := iotaReductA_some hred
  rw [← hctm] at hargs
  have hcp : piCountA (ctorTypeA f (canonLevelsA fm.arity) fv.sort gc.view.mirrors
      (gc.view.fields.map FieldA.norm) gc.view.res) = fv.params.length := by
    rw [piCountA_ctorTypeA, gc.view.mirrors_length, fv.nparams, hnf]; rfl
  obtain ⟨lsx, hlsx⟩ := spineHeadRefA_some hc
  have hx : x = foldAppsA (.const gc.ref lsx) ((appsSpineA x).2 ++ []) := by
    rw [List.append_nil, ← hlsx, foldAppsA_appsSpineA]
  rw [hx, iotaFnA_groupRecA hfresh hlay hcls hpre hgc0 hprel hls (by rw [hargs, gc.normA_getD, hcp])
    (by rw [hnf]; rfl) hmin] at h
  injection h with h
  rw [← h]
  rfl

end Reduct

/-! ## (4) pins: the built Nat recursor, read by the concrete ι -/

/-- the Nat group's recursor type BUILT from its views (family `10`, no parameters or indices,
    sort `1`; `zero` at `11` with no field, `succ` at `12` with one directly recursive field; AnySort,
    motive universe `param 0`): `Π (motive : Nat → Sort u) (mz : motive zero)
    (ms : Π (n : Nat) (ih : motive n), motive (succ n)) (t : Nat), motive t`. -/
def pinNatRecBuiltA : ExprA :=
  recTypeA 10 [] [] [] (.succ .zero) (.param 0) [(11, [], []), (12, [.drec []], [])]

example : pinNatRecBuiltA =
    .pi (.pi (.const 10 []) (.succ .zero) (.sort (.param 0)) (.succ (.param 0)))
      (.imax (.succ .zero) (.succ (.param 0)))
      (.pi (.app (.bvar 0) (.const 11 [])) (.param 0)
        (.pi (.pi (.const 10 []) (.succ .zero)
            (.pi (.app (.bvar 2) (.bvar 0)) (.param 0) (.app (.bvar 3) (.app (.const 12 []) (.bvar 1)))
              (.param 0)) (.imax (.param 0) (.param 0)))
          (.imax (.succ .zero) (.imax (.param 0) (.param 0)))
          (.pi (.const 10 []) (.succ .zero) (.app (.bvar 3) (.bvar 0)) (.param 0))
          (.imax (.succ .zero) (.param 0)))
        (.imax (.imax (.succ .zero) (.imax (.param 0) (.param 0))) (.imax (.succ .zero) (.param 0))))
      (.imax (.param 0) (.imax (.imax (.succ .zero) (.imax (.param 0) (.param 0)))
        (.imax (.succ .zero) (.param 0)))) := rfl

example : piCountA pinNatRecBuiltA = 4 := rfl

/-- the Nat environment with the BUILT recursor at `13`. -/
def pinNatBuiltEnvA : ResolvedEnvA :=
  extendEnvA (extendEnvA (extendEnvA (extendEnvA emptyEnvA 10 pinNatFamA) 11 pinZeroA) 12 pinSuccA)
    13 ⟨.recursorM, 1, pinNatRecBuiltA, none, 0, none⟩

/-- `rec P mz ms (succ zero) ⇝ ms zero (rec P mz ms zero)` on the built recursor. -/
example : iotaFnA pinNatBuiltEnvA
    (.app (.app (.app (.app (.const 13 [.zero]) (.sort .zero)) (.sort (.succ .zero))) pinMsA)
      (.app (.const 12 []) (.const 11 []))) =
    some (.app (.app pinMsA (.const 11 []))
      (.app (.app (.app (.app (.const 13 [.zero]) (.sort .zero)) (.sort (.succ .zero))) pinMsA)
        (.const 11 []))) := by decide

#print axioms piCountA_ctorFieldsA
#print axioms piCountA_ctorTypeA
#print axioms piCountA_frecDomA
#print axioms spineHeadConstA_piBodyA_frecDomA
#print axioms fieldsTelA_ctorFieldsA
#print axioms piCountA_famView
#print axioms ref_of_layoutA
#print axioms members_groupRecA
#print axioms iotaGroupA_groupRecA
#print axioms recHasCtorA_groupRecA
#print axioms elim_propOnly_of_profile
#print axioms elim_propOnly_of_propElimOnlyA
#print axioms elim_propOnly_of_propElimStructA
#print axioms iotaReductA_groupRecA
#print axioms iotaFnA_groupRecA
#print axioms iotaFnA_unitGroupA
#print axioms structGroupA_groupRecA_of_type
#print axioms structGroupA_false_of_unit
#print axioms structGroupA_true_inv
#print axioms famLocalsA_ne_liftA_two
#print axioms structGroupA_groupRecA_true
#print axioms structGroupA_groupRecA_of_propOnly

end Rcic.Declarative.Ann
