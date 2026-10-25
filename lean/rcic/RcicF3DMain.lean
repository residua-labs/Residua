import rcic.RcicF3DRoles
import rcic.RcicF3DBoundBridge

/-!
# F3 D-11: consistency over environments of groups with δ-hidden fields

`consistent4_GD`: in an admitted environment in the class `ClassGD` (no
axioms; inductive groups without function-recursive shapes, every field
family-free, a literal family application, or one reaching a family application
through transparent definitions, β and ζ; under `Prop` large elimination only
family-free unrevealed fields) whose derivations respect the instance bound `K`
(`BoundG`, and the fields' typings at the recursor's instances, `BoundDG` of
`RcicF3DBoundDefs`; `consistent4_GD_of_boundG` derives the latter from `BoundG`
under `RecBelowCtors`), and whose member 1 is the recursor of the empty type at 0, no closed term has
the type at 0, by any derivation with sort levels at most 4 and constant
instances within `K`. Relative to `Premises4`.

The proof installs every family at the limit of its **normalized** data's
iterates (`envCtxD`), which the recursive-group model handles verbatim; the
original fields re-enter only at the final table, where they denote the same
types as their normal forms (`telAgree_of_typings`): per constructor at its own
instances (`ctor_member_sound_norm`), for the recursor and ι at the recursor's
instances (`GroupFaithB`, `recVal_mem_recD`, `iota_at_D`).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative
open Rcic.Model.PS (denRefs hasTyT_denRefs groupMembersT_preserve groupMembersT_installed)

namespace PSet

/-! ### the table entries of a group, from the roles -/

/-- The group's table entries are its values (as `groupFaith_of`), the family at
instances within the recursor's bound, from the normalized family's fixed point
and the transfer. -/
theorem groupFaithB_of (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {ctx ctx0 : Nat → Role}
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember} {ctors : List (Nat × CheckedMember)}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) (node : RecNode E E' f rr rm) (hF : FaithfulR P μ ctx E')
    (hctx : ∀ r, Dom E' r → ctx r = groupRoles (nodeFam node) f rr ctx0 r) (hTF : TypeFacts E')
    (hRD : RecDataAgree (famDataOf node.a) (nodeFam node))
    (hfix : ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) →
      Equiv (famLim P μ (nodeFam node) vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a))) :
    GroupFaithB P μ K fm node := by
  obtain ⟨_, _, hf', hr', _⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  have hfm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfm, node.a.family.storedType]; rfl
  refine ⟨fun vs hvs _ => ?_, fun i vs => ?_, fun vs => ?_, hty, famBounded_node node hTF, fun i => ?_⟩
  · have h := hF f fm hf' vs
    rw [hctx f (dom_of_members hf'), groupRoles_at_f] at h
    rw [hty]
    exact h.trans (hfix vs hvs)
  · have hc := node_ctor_member node i
    have h := hF _ _ hc vs
    rw [hctx _ (dom_of_members hc), groupRoles_at_ctor _ _ (by have := i.isLt; omega)] at h
    have e : memberValR P μ (.ctor (nodeFam node) i.val) (node.a.constructors[i.val]) vs =
        piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf node.a) i.val (nfOf (famDataOf node.a) i.val))
          ρ0 (node.a.constructors[i.val]).mtype := by
      show piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (nodeFam node) i.val (nfOf (nodeFam node) i.val)) ρ0 _ = _
      rw [hRD.nfOf_agree, hRD.ctorEnd_eq]
    rw [e] at h
    exact h
  · have h := hF rr rm hr' vs
    rw [hctx rr (dom_of_members hr'), groupRoles_at_rr _ (by omega)] at h
    have e : memberValR P μ (.recursor (nodeFam node)) rm vs =
        piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf node.a)) ρ0 rm.mtype := by
      show piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (nodeFam node)) ρ0 _ = _
      rw [hRD.recEnd_eq]
    rw [e] at h
    exact h
  · have hb' := (hTF _ _ (node_ctor_member node i)).2.1
    rw [(node.a.constructorViews i).arity] at hb'
    exact hb'

/-- A recursor member under `Prop` large elimination is sound (as `rec_member_sound`,
with the family's value at the instances within the bound). -/
theorem rec_member_soundB (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {E E' : ResolvedEnv}
    {f rr : Nat} {rm fm : CheckedMember} {node : RecNode E E' f rr rm} (hG : GroupFaithB P μ K fm node)
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
  have hbnd : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K rr := by
    intro v hv
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
    exact hls l hl
  refine recVal_mem rfl node.a (ls.map (evalTotal σ)) ?_ (groupFaithB_famAt P hG _ hbnd) (groupFaithB_ctorAt P hG _)
    ?_ hfree
  · intro i
    obtain ⟨shapes, fuel, hfs, hdm⟩ := node.h12 i
    exact ⟨fuel, shapes, hnr i fuel shapes hfs, fieldShapesFuel_length _ _ _ _ _ _ _ _ _ hfs, hdm⟩
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
    have hL := propTel_fits _ _ _ _ xs (hprop _ hbnd ps hps) hxs
    have e : xs.map (fun _ => pempty) = (node.a.constructorViews ⟨0, by omega⟩).fields.map fun _ => pempty := by
      simp only [List.map_const', hxs.length]
    rw [e] at hL
    exact hL

/-! ### the walk, with the base included -/

/-- The members of a group are sound in walk order (as `walk_sound`), the walk
environment known to contain the base. -/
theorem walk_soundD (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) {S E' Eb : ResolvedEnv}
    {f rr : Nat} {fm rm : CheckedMember} (full : List (Nat × CheckedMember)) (np : Nat)
    (hcl : ∀ c, c ∈ full → c.2.mclass = .inductiveM → c = (f, fm))
    (hrcl : ∀ c, c ∈ full → c.2.mclass = .recursorM → c = (rr, rm))
    (hfS : MemberSound P μ K f fm) (hrS : MemberSound P μ K rr rm)
    (hcS : ∀ (Ew : ResolvedEnv) (r : Nat) (m : CheckedMember) (famO : PolicyFamilyView Ew)
      (cv : PolicyConstructorView Ew famO m), (r, m) ∈ full → Ew.members r = none → FieldUniverseAdmitted cv →
      cv.parameters.length = np →
      (∀ vs : List Nat, vs.length = famO.member.arity → (∀ v, v ∈ vs → v ≤ K r) →
        ∀ k : Fin (cv.parameters ++ cv.fields).length,
          ∃ d : HasTyT Ew famO.member.arity (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
            ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)), LOKt (σOf vs) 4 K d) →
      (∀ r' m', Eb.members r' = some m' → Ew.members r' = some m') →
      (∀ r' m', (extendEnv Ew r m).members r' = some m' → E'.members r' = some m') →
      AllSound P μ K Ew → MemberSound P μ K r m) :
    {Ew E'' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → (hw : GroupMembersT S Ew ms E'') →
    (∀ c, c ∈ ms → c ∈ full) → (∀ r' m', Eb.members r' = some m' → Ew.members r' = some m') →
    (∀ r m, E''.members r = some m → E'.members r = some m) →
    WalkClass np hw → WalkB2 K hw → AllSound P μ K Ew → AllSound P μ K E''
  | _, _, _, .nil _, _, _, _, _, _, hA => hA
  | Ew, _, _, .cons _ r m _ _ hfresh _ _ _ _ _ _ hadm _ _ _ _ _ hrest, hms, hbase, hsub, hW, hWB, hA => by
      obtain ⟨hwc, hwcs⟩ := hW
      obtain ⟨hwb, hwbs⟩ := hWB
      have hin := hms (r, m) (List.mem_cons_self _ _)
      have hsubR : ∀ r' m', (extendEnv Ew r m).members r' = some m' → E'.members r' = some m' :=
        fun r' m' h => hsub r' m' (groupMembersT_preserve hrest r' m' h)
      have hnew : MemberSound P μ K r m := by
        cases hadm with
        | family _ view _ hm _ =>
            have hk : m.mclass = .inductiveM := hm ▸ view.hasClass
            have := hcl _ hin hk
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
            exact hfS
        | recursor _ _ _ _ _ _ _ =>
            have := hrcl _ hin hwc
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
            exact hrS
        | constructor famO view _ _ _ h07 _ =>
            exact hcS Ew r m famO view hin hfresh h07 hwc hwb hbase hsubR hA
      have hA' : AllSound P μ K (extendEnv Ew r m) := by
        intro r' m' h
        by_cases hr : r' = r
        · subst hr; rw [members_extend_eq] at h; cases h; exact hnew
        · rw [members_extend_ne Ew r m r' hr] at h; exact hA r' m' h
      exact walk_soundD P μ K full np hcl hrcl hfS hrS hcS hrest (fun c hc => hms c (List.mem_cons_of_mem _ hc))
        (fun r' m' h => members_extend_preserved hfresh r' m' (hbase r' m' h)) hsub hwcs hwbs hA'

/-! ### the transfer at an instance, from bounded typings -/

/-- The original and normalized constructor lists agree at the fitting parameter
environments, at an instance where every field's typing is bounded: the
typed source of the transfer. -/
theorem agreeAt_of_typings (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' S : ResolvedEnv} {f rr : Nat} {rm : CheckedMember} (node : RecNode E E' f rr rm) (vs : List Nat)
    (hES : EnvSound (mkM P μ) (σOf vs) K S node.a.family.member.arity) (hbodies : BodiesOK S (σOf vs) K)
    (hwhnf : ∀ fuel e, whnfFuel node.E0 fuel e = whnfFuel S fuel e)
    (hpar : ∀ i : Fin node.a.constructors.length, (node.a.constructorViews i).parameters = node.a.family.parameters)
    (hty : ∀ (i : Fin node.a.constructors.length) (k : Fin (node.a.constructorViews i).fields.length), ∃ l : Level,
      ∃ d : HasTyT S node.a.family.member.arity
        (policyPrefixContext ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields)
          ((node.a.constructorViews i).parameters.length + k.val))
        ((node.a.constructorViews i).fields[k]) (.sort l), LOKt (σOf vs) 4 K d) :
    AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs := by
  intro ps hps
  refine ⟨(nodeFam_ctors_length node).trans (famDataOf_ctors_length _).symm, fun j c c' hc hc' => ?_⟩
  have hj : j < node.a.constructors.length := by
    rw [← famDataOf_ctors_length]
    exact (List.getElem?_eq_some_iff.mp hc).1
  have e1 := famDataOf_ctor node.a ⟨j, hj⟩
  have e2 : (normFamData node.a node.h14.fuelAt).ctors[j]? = _ := nodeFam_ctor node ⟨j, hj⟩
  rw [hc] at e1
  rw [hc'] at e2
  cases Option.some.inj e1
  cases Option.some.inj e2
  refine ⟨?_, rfl⟩
  refine telAgree_of_typings P μ (σOf vs) K hES hbodies (node.a.constructorViews ⟨j, hj⟩).parameters ps
    (by rw [hpar ⟨j, hj⟩]; exact hps) _ _ (List.length_map _ _) (fun k hk => hty ⟨j, hj⟩ ⟨k, hk⟩) (fun k hk hk' => ?_)
  simp only [List.getElem_map]
  rcases normField_cases node.E0 (node.h14.fuelAt ⟨j, hj⟩) node.a.family.ref ((node.a.constructorViews ⟨j, hj⟩).fields[k])
    with he | ⟨fu, hw⟩
  · exact Or.inl he
  · exact Or.inr ⟨fu, by rw [← hwhnf]; exact hw⟩

/-! ### the induction -/

/-- What the induction carries (as `GInv`), at the roles with the normalized
families: at any table faithful to the roles, every member is sound and ι holds
at every recursor. -/
def GInvD (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) : Prop :=
  ∀ ctx : Nat → Role, (∀ r, Dom E r → ctx r = envCtxD hW r) → ∀ μ, FaithfulR P μ ctx E →
    AllSound P μ K E ∧ ∀ Efin, (∀ r m, E.members r = some m → Efin.members r = some m) →
      ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r

/-- The step of a definition, theorem or opaque constant, at the roles with the
normalized families (as `gInv_single`). -/
theorem gInv_singleD (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} {hE : EnvWfT E} {r : Nat}
    {k : MemberClass} {A v : Expr Nat} (hk : k = .definitionM ∨ k = .theoremM ∨ k = .opaqueM)
    (hfresh : E.members r = none) (hclA : ∀ j, Rcic.Declarative.lift j 1 A = A)
    (hclv : ∀ j, Rcic.Declarative.lift j 1 v = v) (hlvlA : exprLevelsBounded 0 A = true)
    (hlvlv : exprLevelsBounded 0 v = true) (hv : HasTyT E 0 [] v A) (hl : LOKt (fun _ => 0) 4 K hv)
    (hC : ClassGD hE) (IH : GInvD P K hE) (ctx : Nat → Role)
    (hctx : ∀ r', Dom (extendEnv E r ⟨k, 0, A, some v⟩) r' → ctx r' = envCtxD hE r') (μ : Nat → List Nat → PSet.{4})
    (hF : FaithfulR P μ ctx (extendEnv E r ⟨k, 0, A, some v⟩)) :
    AllSound P μ K (extendEnv E r ⟨k, 0, A, some v⟩) ∧
      ∀ Efin, (∀ r' m', (extendEnv E r ⟨k, 0, A, some v⟩).members r' = some m' → Efin.members r' = some m') →
        ∀ r' m', (extendEnv E r ⟨k, 0, A, some v⟩).members r' = some m' → m'.mclass = .recursorM →
          IotaAt P μ K Efin r' := by
  have hsub := members_extend_preserved (m := ⟨k, 0, A, some v⟩) hfresh
  have IHμ := IH ctx (fun r' h => hctx r' (dom_extend hfresh r' h)) μ (fun r' m' h => hF r' m' (hsub r' m' h))
  have hES : EnvSound (mkM P μ) (fun _ => 0) K E 0 := envSound_of P (Efin := E) (fun _ _ h => h) IHμ.1
    (fun r' m' h hk' => IHμ.2 E (fun _ _ h => h) r' m' h hk') _ 0
  have hr : ctx r = .plain := (hctx r dom_self).trans (envCtxD_fresh hE hC r hfresh)
  have hval : Equiv (μ r []) (den (mkM P μ) (fun _ => 0) ρ0 v) := by
    have h := hF r _ (members_extend_eq E r _) []
    have e : memberValR P μ .plain ⟨k, 0, A, some v⟩ [] = den (mkM P μ) (fun _ => 0) ρ0 v :=
      mem_memberVal_def hk A v []
    rw [hr, e] at h
    exact h
  refine ⟨fun r' m' h => ?_, fun Efin hsubF r' m' h hk' => ?_⟩
  · by_cases hr' : r' = r
    · subst hr'; rw [members_extend_eq] at h; cases h
      exact memberSound_singleton' hval hclA hclv hlvlA hlvlv hv hl hES
    · rw [members_extend_ne E r _ r' hr'] at h; exact IHμ.1 r' m' h
  · by_cases hr' : r' = r
    · subst hr'; rw [members_extend_eq] at h; cases h; rcases hk with rfl | rfl | rfl <;> cases hk'
    · rw [members_extend_ne E r _ r' hr'] at h
      exact IHμ.2 Efin (fun r m h => hsubF r m (hsub r m h)) r' m' h hk'


/-- The step of a group (as `gInv_group`), the family installed at its
normalized data's limit. -/
theorem gInv_groupD (P : Premises4) (K : Nat → Nat) {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)} (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hC : ClassGD (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hB : BoundG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (hD : BoundDG K (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem))
    (IH : GInvD P K hE) :
    ∀ ctx : Nat → Role, (∀ r, Dom E' r → ctx r = envCtxD (EnvWfT.group E f fm ctors rr rm E' hE hfam hctors hrec hmem) r) →
    ∀ μ, FaithfulR P μ ctx E' →
    AllSound P μ K E' ∧ ∀ Efin, (∀ r m, E'.members r = some m → Efin.members r = some m) →
      ∀ r m, E'.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r := by
  obtain ⟨hCE, hGn, hWC⟩ := hC
  obtain ⟨hL, hrr⟩ := group_layout_of_class hE hfam hctors hrec hmem hWC
  obtain ⟨hBG, hB1, hWB, hB3⟩ := hB
  obtain ⟨_, hDG⟩ := hD
  intro ctx hctx μ hF
  obtain ⟨node, hs⟩ := group_nodeD hE hfam hctors hrec hmem
  obtain ⟨hsh, hpf, hpar⟩ := hGn node
  obtain ⟨hf0, _, hf', hr', _⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m := groupMembersT_preserve hmem
  have hctxE : ∀ r, Dom E r → ctx r = envCtxD hE r := fun r h =>
    (hctx r (dom_groupMembersT hmem h)).trans (envCtxD_group_stable hE hfam hctors hrec hmem hL hrr r h)
  have hctxG : ∀ r, Dom E' r → ctx r = groupRoles (nodeFam node) f rr (envCtxD hE) r := fun r h =>
    (hctx r h).trans (congrFun (envCtxD_group_some hE hfam hctors hrec hmem _ hs) r)
  have hFE : FaithfulR P μ ctx E := fun r m h => hF r m (hsubE r m h)
  have IHμ := IH ctx hctxE μ hFE
  have hTF : TypeFacts E' := typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)
  have hbody := groupMembersT_body_none hmem
  have hSsub : ∀ r m, (extendEnv E f fm).members r = some m → E'.members r = some m := by
    intro r m h
    by_cases hr : r = f
    · subst hr; rw [members_extend_eq] at h; cases h; exact hf'
    · rw [members_extend_ne E f fm r hr] at h; exact hsubE r m h
  have hbf : fm.body = none := hbody f fm (List.mem_cons_self _ _)
  have hfmm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfmm, node.a.family.storedType]; rfl
  have hFF : FamFreeBodies node.E0 node.a.family.ref := by
    rw [node.fam]; exact famFreeBodies_node hE hf0 hmem node
  -- the family's entry is the normalized data's limit
  have hLimμ : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (nodeFam node) vs) := fun vs => by
    have h := hF f fm hf' vs
    rw [hctxG f (dom_of_members hf'), groupRoles_at_f] at h
    rw [node.fam]
    exact h
  have hpfF : ∀ e, e ∈ (famDataOf node.a).params ++ (famDataOf node.a).indices →
      occursConst (famDataOf node.a).fref e = false := by
    intro e he
    refine occurs_false_of_refs e fun r hr hrf => ?_
    have := groupMembersT_head_refs hmem r (by rw [hty]; exact refs_policyPi_dom _ _ e he hr)
    have hrf' : r = f := hrf.trans node.fam
    rw [hrf'] at this
    unfold Dom at this
    rw [hf0] at this
    exact absurd this (by decide)
  have hopq : ∀ ls, transparentBody node.E0 f ls = none := by
    intro ls
    have hp := node.a.family.present
    rw [node.fam] at hp
    unfold transparentBody
    rw [hp]
    show (if transparent node.a.family.member.mclass then _ else none) = none
    rw [node.a.family.hasClass]
    rfl
  have hopq' : ∀ ls, transparentBody node.E0 node.a.family.ref ls = none := by rw [node.fam]; exact hopq
  -- the recursive-group conditions on the normalized data
  have RG : RecGroupD node.a node.h14.fuelAt node.h14.shapesAt := by
    refine ⟨nodeFam_bounded node hTF (node_bodies_levelsBounded0 hE hmem node K hBG), hpfF,
      nodeFam_recApp node hFF hsh, fun i => fieldsClass_of_direct _ 0 (nodeFam_fields_direct node hFF hsh i),
      fun i e he => (node.a.constructorViews i).noFamilyInIndices e he, envClosed_node node hTF, fun i => ?_⟩
    obtain ⟨shapes', fuel', hfs', hdm'⟩ := node.h12 i
    have heq : shapes' = node.h14.shapesAt i := fieldShapesFuel_unique hfs' (node.h14.analyzed i)
    subst heq
    refine ⟨fuel', ?_, hdm'⟩
    have h0 := shapesNorm_of_fieldShapesFuel hFF _ _ _ hfs' (hsh i)
    rwa [normFields_fuel_eq hFF _ _ _ _ hfs' (node.h14.analyzed i) (hsh i) (hsh i)] at h0
  -- the family's entry is its normalized value, at every instance
  have hfix' : ∀ vs, Equiv (μ node.a.family.ref vs) (famVal (mkM P μ) W4 (σOf vs) (nodeFam node)) := fun vs =>
    (hLimμ vs).trans ((famLim_fix P μ (nodeFam node) node.a.family.member.arity RG.bounded RG.famFree RG.cls
      (RG.ri node.a) vs).symm.trans (famVal_tables P (tabLim_equivD P μ node.a hLimμ) _ _))
  have hfmS : MemberSound P μ K f fm := by
    refine fam_member_sound P (nodeFam node) (fun vs => ?_) hty (hTF f fm hf').1 (hTF f fm hf').2.1 hbf
    rw [hty]
    have h := hfix' vs
    rw [node.fam] at h
    exact h
  -- the constructor scope at the table
  have hES_S : ∀ σ n, EnvSound (mkM P μ) σ K (extendEnv E f fm) n := by
    intro σ n
    refine envSound_of P hSsub ?_ ?_ σ n
    · intro r m h
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; exact hfmS
      · rw [members_extend_ne E f fm r hr] at h; exact IHμ.1 r m h
    · intro r m h hk
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; rw [hfam] at hk; cases hk
      · rw [members_extend_ne E f fm r hr] at h; exact IHμ.2 E' hsubE r m h hk
  have hbodies_S : ∀ σ, BodiesOK (extendEnv E f fm) σ K := fun σ =>
    bodiesOK_of_envWfT K hE hBG (fun r m h => members_extend_preserved hf0 r m h) (fun r m hm h0 => by
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at hm; cases hm; exact hbf
      · rw [members_extend_ne E f fm r hr] at hm; rw [hm] at h0; cases h0) σ
  have hwhnf_S : ∀ fuel e, whnfFuel node.E0 fuel e = whnfFuel (extendEnv E f fm) fuel e :=
    whnfFuel_eq_along hmem node.base (node_sub' node) (fun r m h => members_extend_preserved hf0 r m h) hSsub
  -- the transfer at instances within the recursor's bound
  have hagR0 : ∀ vs, vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K rr) →
      AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs := fun vs hlen hvs =>
    agreeAt_of_typings P μ K node vs (hES_S (σOf vs) _) (hbodies_S (σOf vs)) hwhnf_S hpar
      (fun i k => hDG node i vs hlen hvs k)
  -- a recursor instance carries one more level under `anySort`: transport from the family's instance
  have hagR : ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs := fun vs hvs =>
    agreeAt_levels P μ node.a _ vs (σOf_policyFamilyLevels_agree node.a.family vs) (famBounded_node node hTF)
      (nodeFam_bounded node hTF (node_bodies_levelsBounded0 hE hmem node K hBG))
      (hagR0 _ (famLevels_length node.a.family vs) (famLevels_le node.a.family hvs))
  have hRD : RecDataAgree (famDataOf node.a) (nodeFam node) := nodeFam_recDataAgree node hFF hsh
  have hG : GroupFaithB P μ K fm node := by
    refine groupFaithB_of P hmem hL hrr node hF hctxG hTF hRD fun vs hvs => ?_
    exact ((hLimμ vs).symm.trans (hfix' vs)).trans
      (famVal_agree (mkM P μ) W4 (σOf vs) (famDataOf node.a) (nodeFam node).ctors (hagR vs hvs)).symm
  -- under large elimination of a `Prop` family: nonrecursive shapes, proof fields
  have hsh' : ∀ (i : Fin node.a.constructors.length) fuel shapes, UniformProp node.a.family.resultLevel →
      node.a.policy = .anySort →
      fieldShapesFuel node.E0 fuel f node.a.family.member.arity node.a.family.parameters.length
        node.a.family.indices.length node.a.family.parameters.length (node.a.constructorViews i).fields = some shapes →
      ShapesMatch f shapes (node.a.constructorViews i).fields := fun i fuel shapes hU hpol hfs =>
    shapesMatch_of_direct (famFreeBodies_node hE hf0 hmem node) hopq _ 0 _
      (recFieldsDirect_of_free (lsF := []) (np := 0) (nq := 0) _ 0 (hpf hU hpol i).1) shapes hfs
  have hnrec : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ (i : Fin node.a.constructors.length) fuel shapes, fieldShapesFuel node.E0 fuel node.a.family.ref
        node.a.family.member.arity node.a.family.parameters.length node.a.family.indices.length
        node.a.family.parameters.length (node.a.constructorViews i).fields = some shapes →
        ∀ s, s ∈ shapes → s = .nonrecursive := by
    intro hU hpol i fuel shapes hfs s hs
    have hnf := (hpf hU hpol i).1
    rw [node.fam] at hfs
    obtain ⟨_, hm⟩ := hsh' i fuel shapes hU hpol hfs
    obtain ⟨k, hk1, hk2⟩ := List.mem_iff_getElem.mp hs
    have hkF : k < (node.a.constructorViews i).fields.length := by
      rw [← (hsh' i fuel shapes hU hpol hfs).1]; exact hk1
    rcases hm k s _ (by rw [List.getElem?_eq_getElem hk1, hk2]) (List.getElem?_eq_getElem hkF) with
      ⟨h, _⟩ | ⟨_, _, ho⟩
    · exact h
    · rw [hnf _ (List.getElem_mem hkF)] at ho; cases ho
  have hPT : UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ (i : Fin node.a.constructors.length) vs, (∀ v, v ∈ vs → v ≤ K rr) → ∀ ps,
        TelFits (mkM P μ) (σOf vs) node.a.family.parameters ρ0 ps →
        PropTel (mkM P μ) (σOf vs) (node.a.constructorViews i).fields (push ps ρ0) := by
    intro hU hpol i vs hvs ps hps
    refine propTel_of_typings P μ K vs _ _ (hES_S (σOf vs) node.a.family.member.arity) (fun k => ?_) ps hps
    obtain ⟨l, hl, hd⟩ := hB3 node hU hpol i vs hvs k
    exact ⟨l, hl _, hd⟩
  have hlvC : ∀ i : Fin node.a.constructors.length,
      exprLevelsBounded node.a.family.member.arity (node.a.constructors[i.val]).mtype = true := fun i => by
    have h := (hTF _ _ (node_ctor_member node i)).2.1
    rw [(node.a.constructorViews i).arity] at h
    exact h
  -- ι at the group's recursor
  have hIrr : ∀ Efin, (∀ r m, E'.members r = some m → Efin.members r = some m) → IotaAt P μ K Efin rr :=
    fun Efin hsubF => iota_at_D P hG hsubF hr' hFF hopq' hsh hlvC (fun hU hpol i => by
      obtain ⟨shapes, fuel, hfs, hdm⟩ := node.h12 i
      have hmt := derivedMinor_nonrec node.a i fuel shapes (hnrec hU hpol i fuel shapes hfs)
        (fieldShapesFuel_length _ _ _ _ _ _ _ _ _ hfs)
      rw [hdm] at hmt
      exact ⟨fun T hT => by rw [node.fam]; exact (hpf hU hpol i).1 T hT, (hpf hU hpol i).2, ⟨_, hmt⟩,
        hPT hU hpol i⟩)
  -- every recursor of the extended environment
  have hIall : ∀ Efin, (∀ r m, E'.members r = some m → Efin.members r = some m) →
      ∀ r m, E'.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r := by
    intro Efin hsubF r m h hk
    rcases group_member_cases hmem hL hrr node h with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, rfl, rfl⟩
    · exact IHμ.2 Efin (fun r m h => hsubF r m (hsubE r m h)) r m h1 hk
    · rw [hfam] at hk; cases hk
    · exact hIrr Efin hsubF
    · rw [(node.a.constructorViews i).hasClass] at hk; cases hk
  -- the recursor
  have hrmS : MemberSound P μ K rr rm := by
    have hcl := (hTF _ _ hr').1
    have hlvl := (hTF _ _ hr').2.1
    have hrb : rm.body = none :=
      hbody _ _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
    rcases selection_uniform node.a with hU | hT
    · cases hpol : node.a.policy with
      | propOnly =>
          intro σ ls ρ hlen hls
          refine ⟨?_, fun b hb => by rw [hrb] at hb; cases hb⟩
          rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
          refine mem_congr_left (hG.recur _).symm ?_
          have hbnd : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K rr := by
            intro v hv
            obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
            exact hls l hl
          exact recVal_mem_recPD P μ node.a RG hLimμ _ (hagR _ hbnd) (groupFaithB_ctorAt P hG _) (hU _) hpol
      | anySort =>
          exact rec_member_soundB P hG hcl hlvl hrb (hnrec hU hpol)
            (fun hU' hpol' i => ⟨(hpf hU' hpol' i).2, hPT hU' hpol' i⟩)
            (fun i T hT => by rw [node.fam]; exact (hpf hU hpol i).1 T hT)
    · intro σ ls ρ hlen hls
      refine ⟨?_, fun b hb => by rw [hrb] at hb; cases hb⟩
      rw [den_inst_canon (mkM P μ) σ ls ρ rm.mtype hcl (hlen ▸ hlvl)]
      refine mem_congr_left (hG.recur _).symm ?_
      have hbnd : ∀ v, v ∈ ls.map (evalTotal σ) → v ≤ K rr := by
        intro v hv
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
        exact hls l hl
      exact recVal_mem_recD P μ node.a RG hLimμ _ (hagR _ hbnd) (groupFaithB_ctorAt P hG _)
        (Nat.pos_iff_ne_zero.mp (hT _))
  -- the constructors, along the walk
  have hcS : ∀ (Ew : ResolvedEnv) (r : Nat) (m : CheckedMember) (famO : PolicyFamilyView Ew)
      (cv : PolicyConstructorView Ew famO m), (r, m) ∈ (f, fm) :: ctors ++ [(rr, rm)] → Ew.members r = none →
      FieldUniverseAdmitted cv → cv.parameters.length = node.a.family.parameters.length →
      (∀ vs : List Nat, vs.length = famO.member.arity → (∀ v, v ∈ vs → v ≤ K r) →
        ∀ k : Fin (cv.parameters ++ cv.fields).length,
          ∃ d : HasTyT Ew famO.member.arity (policyPrefixContext (cv.parameters ++ cv.fields) k.val)
            ((cv.parameters ++ cv.fields)[k.val]) (.sort (cv.domainsTyped.levels k)), LOKt (σOf vs) 4 K d) →
      (∀ r' m', E.members r' = some m' → Ew.members r' = some m') →
      (∀ r' m', (extendEnv Ew r m).members r' = some m' → E'.members r' = some m') →
      AllSound P μ K Ew → MemberSound P μ K r m := by
    intro Ew r m famO cv hin hfresh h07 hnpO hB2w hbase hsubw hAw
    have hEw : ∀ r' m', Ew.members r' = some m' → E'.members r' = some m' := fun r' m' h =>
      hsubw r' m' (members_extend_preserved hfresh r' m' h)
    -- the member is one of the group's constructors
    have hkC : m.mclass = .constructorM := cv.hasClass
    have hctor : ∃ i : Fin node.a.constructors.length, r = f + 1 + i.val ∧ m = node.a.constructors[i.val] := by
      rcases group_member_cases hmem hL hrr node (groupMembersT_installed hmem hin) with
        h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h1
      · rcases List.mem_cons.mp hin with h2 | h2
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2; rw [hfam] at hkC; cases hkC
        · rcases List.mem_append.mp h2 with h3 | h3
          · have hr : r ∈ ctors.map Prod.fst := List.mem_map.mpr ⟨_, h3, rfl⟩
            rw [hL] at hr
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
            have hi' : i < node.a.constructors.length := by rw [hlen]; exact List.mem_range.mp hi
            exact ⟨⟨i, hi'⟩, rfl, Option.some.inj ((groupMembersT_installed hmem hin).symm.trans
              (node_ctor_member node ⟨i, hi'⟩))⟩
          · rw [List.mem_singleton] at h3
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3; rw [hrec] at hkC; cases hkC
      · rw [hfam] at hkC; cases hkC
      · rw [hrec] at hkC; cases hkC
      · exact h1
    obtain ⟨i, rfl, rfl⟩ := hctor
    -- the constructor's own view agrees with the recursor's
    have hstO := cv.storedType
    have hstR := (node.a.constructorViews i).storedType
    have hspl := policyPi_split_eq _ _ _ _ (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
      (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _) (hstO.symm.trans hstR)
    obtain ⟨hP, hFs⟩ := List.append_inj hspl.1 (by rw [hnpO, (node.a.constructorViews i).parameterCount])
    have href : famO.ref = node.a.family.ref := foldApps_const_head hspl.2
    have hfamO : famO.member = fm := by
      have h1 := famO.present
      rw [href, node.fam] at h1
      exact Option.some.inj ((hEw f _ h1).symm.trans hf')
    have hlvO : famO.resultLevel = node.a.family.resultLevel := by
      have e1 := famO.storedType
      have e2 := node.a.family.storedType
      rw [hfamO] at e1
      rw [hfmm] at e2
      have := (policyPi_split_eq _ _ _ _ (expr_not_pi_of_sort _) (expr_not_pi_of_sort _) (e1.symm.trans e2)).2
      injection this
    have harO : famO.member.arity = node.a.family.member.arity := by rw [hfamO, hfmm]
    have hES_w : ∀ vs, EnvSound (mkM P μ) (σOf vs) K Ew famO.member.arity := fun vs =>
      envSound_of P hEw hAw (fun r m h hk => hIall E' (fun _ _ h => h) r m (hEw r m h) hk) _ _
    have hbodies_w : ∀ σ, BodiesOK Ew σ K := fun σ =>
      bodiesOK_of_envWfT K hE hBG hbase (fun r m hm h0 => by
        rcases groupMembersT_cases hmem r m (hEw r m hm) with h1 | h1
        · rw [h1] at h0; cases h0
        · exact groupMembersT_body_none hmem r m h1) σ
    have hwhnf_w : ∀ fuel e, whnfFuel node.E0 fuel e = whnfFuel Ew fuel e :=
      whnfFuel_eq_along hmem node.base (node_sub' node) hbase hEw
    have hnf : nfOf (nodeFam node) i.val = (node.a.constructorViews i).fields.length := by
      rw [nfOf_eq, ctorFieldsOf_of_get (nodeFam_ctor node i), List.length_map]
    refine ctor_member_sound_norm P (nodeFam node) i.val (node.a.constructorViews i).parameters
      (node.a.constructorViews i).fields
      ((node.a.constructorViews i).fields.map (normField node.E0 (node.h14.fuelAt i) node.a.family.ref))
      (node.a.constructorViews i).resultIndices (nodeFam_ctor node i)
      (node.a.constructorViews i).parameterCount (node.a.constructorViews i).indexCount ?_
      (hTF _ _ (node_ctor_member node i)).1 (hTF _ _ (node_ctor_member node i)).2.1
      (hbody _ _ (node_ctor_mem hmem hL hrr node i)) hnf (fun vs => ?_) (fun vs _ => hfix' vs) ?_ ?_ ?_
    · rw [(node.a.constructorViews i).storedType, (node.a.constructorViews i).arity]
      rfl
    · have h := hG.ctor i vs
      rw [← hRD.nfOf_agree, ← hRD.ctorEnd_eq] at h
      exact h
    · intro vs hvl hbd ps hps
      have hvlO : vs.length = famO.member.arity := by rw [harO, ← (node.a.constructorViews i).arity]; exact hvl
      have hB2v := hB2w vs hvlO hbd
      have hagC : TelAgree (mkM P μ) (σOf vs) cv.fields
          (cv.fields.map (normField node.E0 (node.h14.fuelAt i) node.a.family.ref)) (push ps ρ0) := by
        refine telAgree_of_typings P μ (σOf vs) K (hES_w vs) (hbodies_w (σOf vs)) cv.parameters ps
          (by rw [hP]; exact hps) _ _ (List.length_map _ _) (fun k hk => ?_) (fun k hk hk' => ?_)
        · have hkk : cv.parameters.length + k < (cv.parameters ++ cv.fields).length := by
            rw [List.length_append]; omega
          obtain ⟨d, hd⟩ := hB2v ⟨cv.parameters.length + k, hkk⟩
          have hget : (cv.parameters ++ cv.fields)[cv.parameters.length + k]'hkk = cv.fields[k]'hk := by
            rw [List.getElem_append_right (Nat.le_add_right _ _)]
            congr 1
            omega
          exact ⟨_, lokt_cast (σOf vs) 4 K hget d hd⟩
        · simp only [List.getElem_map]
          rcases normField_cases node.E0 (node.h14.fuelAt i) node.a.family.ref (cv.fields[k]) with he | ⟨fu, hw⟩
          · exact Or.inl he
          · exact Or.inr ⟨fu, by rw [← hwhnf_w]; exact hw⟩
      rw [hFs] at hagC
      exact hagC
    · intro vs hvl hbd zs hz
      obtain ⟨u, d, hd⟩ := hB1 node i vs (hvl.trans (node.a.constructorViews i).arity) hbd
      have hsd := hsound_ty (P.good _ rfl) (hES_S (σOf vs) _) d hd
      have := tel_end_type' _ _ d (node.a.constructorViews i).storedType hsd ρ0 zs trivial hz
      have e : (List.range vs.length).map Level.param = policyFamilyLevels node.a.family := by
        rw [hvl, (node.a.constructorViews i).arity]; rfl
      rw [e]
      exact this
    · intro vs hvl hbd h0 ps xs hps hxs
      have hvlO : vs.length = famO.member.arity := by rw [harO, ← (node.a.constructorViews i).arity]; exact hvl
      have hB2v := hB2w vs hvlO hbd
      have hD : RefsIn (Dom Ew) (cv.parameters ++ cv.fields) := fun e he r hr => by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
        obtain ⟨d, _⟩ := hB2v ⟨k, hk⟩
        exact hasTyT_denRefs d r hr
      have h0O : evalTotal (σOf vs) famO.resultLevel ≠ 0 := by rw [hlvO]; exact h0
      have := field_small P μ μ K (Epre := Ew) cv vs h07 (hES_w vs) hB2v (fun _ _ _ => rfl) hD h0O ps xs
        (by rw [hP]; exact hps) (by rw [hFs]; exact hxs)
      rw [hFs, hlvO] at this
      exact this
  have hAll : AllSound P μ K E' := by
    refine walk_soundD P μ K ((f, fm) :: ctors ++ [(rr, rm)]) node.a.family.parameters.length ?_ ?_ hfmS hrmS hcS hmem
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h) (hWC node) hWB IHμ.1
    · intro c hc hk
      rcases List.mem_cons.mp hc with h | h
      · exact h
      · rcases List.mem_append.mp h with h | h
        · rw [hctors c h] at hk; cases hk
        · rw [List.mem_singleton] at h; subst h; rw [hrec] at hk; cases hk
    · intro c hc hk
      rcases List.mem_cons.mp hc with h | h
      · subst h; rw [hfam] at hk; cases hk
      · rcases List.mem_append.mp h with h | h
        · rw [hctors c h] at hk; cases hk
        · rw [List.mem_singleton] at h; exact h
  exact ⟨hAll, fun Efin hsubF r m h hk => hIall Efin hsubF r m h hk⟩

theorem gInvD (P : Premises4) (K : Nat → Nat) : {E : ResolvedEnv} → (hW : EnvWfT E) → ClassGD hW → BoundG K hW →
    BoundDG K hW → GInvD P K hW
  | _, .empty, _, _, _ => fun _ _ _ _ => ⟨fun _ _ h => (Option.noConfusion h), fun _ _ _ _ h => (Option.noConfusion h)⟩
  | _, .axiom _ _ _ _ _ _ _ _ _, hC, _, _ => hC.elim
  | _, .definition _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv, hC, hB, hD =>
      gInv_singleD P K (Or.inl rfl) hfresh hclA hclv hlvlA hlvlv hv hB.2 hC (gInvD P K hE hC hB.1 hD)
  | _, .thm _ _ _ _ hE hfresh _ hp hclA hclp hlvlA hlvlp, hC, hB, hD =>
      gInv_singleD P K (Or.inr (Or.inl rfl)) hfresh hclA hclp hlvlA hlvlp hp hB.2 hC (gInvD P K hE hC hB.1 hD)
  | _, .opaque _ _ _ _ _ hE hfresh _ hv hclA hclv hlvlA hlvlv, hC, hB, hD =>
      gInv_singleD P K (Or.inr (Or.inr rfl)) hfresh hclA hclv hlvlA hlvlv hv hB.2 hC (gInvD P K hE hC hB.1 hD)
  | _, .group _ _ _ _ _ _ _ hE hfam hctors hrec hmem, hC, hB, hD =>
      gInv_groupD P K hE hfam hctors hrec hmem hC hB hD (gInvD P K hE hC.1 hB.1 hD.1)

/-- **Consistency below level 4 over environments of inductive groups with
δ-hidden fields.** In an admitted environment in `ClassGD` (no axioms; inductive
groups without function-recursive shapes — every field family-free, a literal
family application, or one reaching a family application through transparent
definitions, β and ζ; under `Prop` large elimination only family-free fields,
none revealed in the result indices), whose constructor and field typings
respect the instance bound `K` (`BoundG`, and the fields' typings at the
recursor's instances, `BoundDG`), and whose member 1 is the recursor of the
empty type at 0, no closed term has the type at 0, by any derivation whose
sort levels are at most 4 and whose constant instances respect `K`. Relative to
`Premises4` (choice in Lean's universes 0..3, decidability). -/
theorem consistent4_GD (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) (hC : ClassGD hW)
    (hB : BoundG K hW) (hD : BoundDG K hW) (h1 : E.members 1 = some falseRecMemberU) (n : Nat) (e : Expr Nat)
    (h : HasTyT E n [] e (.const 0 [])) (hl : LOKt (fun _ => 0) 4 K h) : False := by
  have hRA := readsOKAlong_envCtxD hW hC (envCtxD hW) (fun _ _ => rfl)
  have hF := (faithfulR_envμR P (envCtxD hW) hW hRA).1
  have hI := gInvD P K hW hC hB hD (envCtxD hW) (fun _ _ => rfl) _ hF
  have hES := envSound_of P (Efin := E) (fun _ _ h => h) hI.1
    (fun r m hm hk => hI.2 E (fun _ _ h => h) r m hm hk) (fun _ => 0) n
  exact empty_of_falseRec P (hI.1 1 _ h1) (sound_ty (P.good _ rfl) hES h hl ρ0 trivial)

/-- The same with the numeric condition `RecBelowCtors K` (each recursor's bound
at most its constructors') in place of the second bound: `BoundDG` is derived
from `BoundG` (`boundDG_of_boundG`). -/
theorem consistent4_GD_of_boundG (P : Premises4) (K : Nat → Nat) {E : ResolvedEnv} (hW : EnvWfT E) (hC : ClassGD hW)
    (hR : RecBelowCtors K hW) (hB : BoundG K hW) (h1 : E.members 1 = some falseRecMemberU) (n : Nat) (e : Expr Nat)
    (h : HasTyT E n [] e (.const 0 [])) (hl : LOKt (fun _ => 0) 4 K h) : False :=
  consistent4_GD P K hW hC hB (boundDG_of_boundG K hW hR hB) h1 n e h hl

end PSet

end Rcic.F3
