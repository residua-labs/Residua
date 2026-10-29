import rcic.RcicF3EqDRoleBridge

/-!
# F3 D, group-granular: the raw chain controlled by an ORDER (no fixpoint first)

`closure_claim = 0`.

## The cycle, and where it actually closes

`RcicF3EqDRoleBridge` §7 recorded the general D group step as blocked by a
stage-table / `EnvSound` chicken-and-egg: to compare the raw family chain
(fields with δ-hidden family occurrences, the roles `envCtx` installs) with
the normalized chain (the one the landed fixed-point machinery controls) one
needs the constructor scope sound at every stage table, and the landed route
to the family member's soundness (`fam_member_sound`, used by
`gInv_groupD`/`gInv_group_ofAt`) takes the family **fixed point** as input.

But an inductive family member's `MemberSound` is only **membership** of its
table entry in the denotation of its (family-free) type — and every stage
entry is a family value (`famVal_mem`, at any table), as is the limit
(`famLim_mem`, §2). So the cycle is broken by an ORDER:

1. the base invariant (`GInv P K hE`) is applied **at each stage table**
   `tabIter P μ raw n` (the stage tables agree with `μ` on the base, and the
   base's reads stay in the base — `readsClosed_envCtx`, §1, no walk
   condition needed);
2. the family member is sound at the stage table by membership alone (§2);
3. hence the constructor scope is sound at the stage table (`envSound_scope`);
4. hence, at every instance where the fields' typings are bounded (`BoundDG`:
   the recursor's bound `K rr`), the raw and normalized constructor lists
   agree at the stage table (`agreeAt_of_typings`, landed);
5. the stage induction (§3): the raw and normalized iterates agree at every
   bounded instance — the normalized fields read the family only at the
   canonical instance (`famEnd_upd_equiv`), so the induction stays inside the
   bounded instances;
6. the limits agree at bounded instances, and the normalized limit is a fixed
   point (`famLim_fix`), so the raw-role table entry is the raw family value at
   every bounded instance (`famB_raw`, §4) — `GroupFaithB` in the **raw**
   roles, with no fixpoint assumed anywhere before step 6.

## What is and is not claimed

Compiled: §1–§4 (the order, the chain control, `groupFaithB_raw`), and the
family member's soundness in the raw roles at every instance
(`fam_member_sound_raw`). The measured boundary — the instances above the
recursor's bound — is §5.

Axioms of every sealed declaration ⊆ {`propext`, `Quot.sound`}.
-/

set_option autoImplicit false

namespace Rcic.F3.StepDGOrder

open Rcic.Declarative Rcic.Model.PS Rcic.F3 Rcic.F3.PSet Rcic.F3.TierGroup

/-! ## §1 the base's reads stay in the base, at every admitted environment -/

/-- Fresh references have the plain role at every admitted environment (the
landed `envCtx_freshW` asks for `WalkG`; only the group layout is read, and
`walkRec_of_group` supplies it from the membership derivation). -/
theorem envCtx_freshT : {E : ResolvedEnv} → (hW : EnvWfT E) → ∀ r, E.members r = none →
    envCtx hW r = .plain
  | _, .empty, _, _ => rfl
  | _, .axiom _ _ _ _ hE _ _ _ _, r, h => envCtx_freshT hE r (extendEnv_ne_none h).2
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, r, h => envCtx_freshT hE r (extendEnv_ne_none h).2
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, r, h => envCtx_freshT hE r (extendEnv_ne_none h).2
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, r, h => envCtx_freshT hE r (extendEnv_ne_none h).2
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, r, h => by
      obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
      have hrE : E.members r = none := groupMembersT_none hmem h
      show (match scanRec hmem with
        | some fd => groupRoles fd f rr (envCtx hE)
        | none => envCtx hE) r = _
      cases scanRec hmem with
      | none => exact envCtx_freshT hE r hrE
      | some fd =>
          obtain ⟨_, _, hf', hr', hbet⟩ := group_refs hmem hL hrr
          show groupRoles fd f rr (envCtx hE) r = _
          unfold groupRoles
          have h1 : r ≠ f := by intro he; subst he; rw [hf'] at h; cases h
          have h2 : r ≠ rr := by intro he; subst he; rw [hr'] at h; cases h
          have h3 : ¬ (f < r ∧ r < rr) := by
            intro ⟨a, b⟩
            obtain ⟨_, _, _, _, hm⟩ := hbet r a b
            rw [hm] at h; cases h
          rw [if_neg h1, if_neg h2, if_neg h3]
          exact envCtx_freshT hE r hrE

/-- Every member reads inside the environment before it, at the roles of the
environment — at every admitted environment (axioms included; no walk
condition). -/
theorem readsOKAlong_envCtxT : {E : ResolvedEnv} → (hW : EnvWfT E) → ∀ ctx : Nat → Role,
    (∀ r, Dom E r → ctx r = envCtx hW r) → ReadsOKAlong ctx hW
  | _, .empty, _, _ => trivial
  | _, .axiom E r A _ hE hfresh hA _ _, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxT hE ctx fun r' h => hctx r' (dom_extend hfresh r' h), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_freshT hE r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h, fun b hb => by cases hb⟩
  | _, .definition E r A v _ hE hfresh hA hv _ _ _ _, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxT hE ctx fun r' h => hctx r' (dom_extend hfresh r' h), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_freshT hE r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h, fun b hb r' h => by cases hb; exact hasTyT_denRefs hv r' h⟩
  | _, .thm E r A p hE hfresh hA hp _ _ _ _, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxT hE ctx fun r' h => hctx r' (dom_extend hfresh r' h), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_freshT hE r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h, fun b hb r' h => by cases hb; exact hasTyT_denRefs hp r' h⟩
  | _, .opaque E r A v _ hE hfresh hA hv _ _ _ _, ctx, hctx => by
      refine ⟨readsOKAlong_envCtxT hE ctx fun r' h => hctx r' (dom_extend hfresh r' h), ?_⟩
      have hr : ctx r = .plain := (hctx r dom_self).trans (envCtx_freshT hE r hfresh)
      rw [hr]
      exact ⟨fun r' h => hasTyT_denRefs hA r' h, fun b hb r' h => by cases hb; exact hasTyT_denRefs hv r' h⟩
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, ctx, hctx => by
      obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
      refine ⟨readsOKAlong_envCtxT hE ctx fun r' h => (hctx r' (dom_groupMembersT hmem h)).trans
        (envCtx_group_stable hE hfam hctors hrec hmem hL hrr r' h), ?_⟩
      obtain ⟨node, hs⟩ := group_node hE hfam hctors hrec hmem
      refine groupReadsOK_of ctx hmem (fun _ h => h) fun c hc fd hcf => ?_
      have hd : Dom E' c.1 := dom_of_members (groupMembersT_installed hmem hc)
      rw [hctx c.1 hd, envCtx_group_some hE hfam hctors hrec hmem _ hs] at hcf
      obtain ⟨_, rfl⟩ := groupRoles_fam hcf (envCtx_freshT hE c.1 (groupMembersT_fresh_base hmem c.1 c.2 hc))
      exact famReads_node hmem hL hrr node

/-- The base's reads stay in the base, at every admitted environment. -/
theorem readsClosed_envCtx (P : Premises4) {E : ResolvedEnv} (hW : EnvWfT E) (ctx : Nat → Role)
    (hctx : ∀ r, Dom E r → ctx r = envCtx hW r) : ReadsClosed ctx E :=
  (faithfulR_envμR P ctx hW (readsOKAlong_envCtxT hW ctx hctx)).2

/-- Faithfulness on the base survives overriding the table at a reference
fresh for the base (the stage tables). -/
theorem faithfulR_upd_fresh (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {ctx : Nat → Role}
    {E : ResolvedEnv} {f : Nat} (hF : FaithfulR P μ ctx E) (hR : ReadsClosed ctx E) (hf0 : E.members f = none)
    (X : List Nat → PSet.{4}) : FaithfulR P (upd μ f X) ctx E :=
  faithfulR_transfer P hF hR (fun r hr ls => upd_ne μ f X (fun he => by
    subst he; unfold Dom at hr; rw [hf0] at hr; exact absurd hr (by decide)) ls)

/-! ## §2 the family member is sound by membership alone -/

/-- The family's type mentions no reference at the family. -/
theorem famType_refs_ne (fd : FamData)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false) :
    ∀ r, r ∈ denRefs (famType fd) → r ≠ fd.fref :=
  famType_refs fd fun e he r hr => denRefs_ne_of_occurs e (hpf e he) r hr

/-- The family's type denotes the same at tables agreeing off the family. -/
theorem den_famType_upd (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false) (X : List Nat → PSet.{4})
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) :
    den (mkM P (upd μ fd.fref X)) σ ρ (famType fd) = den (mkM P μ) σ ρ (famType fd) :=
  den_agreeOn P (agreeOn_upd_off μ fd.fref X) σ _ (famType_refs_ne fd hpf) ρ

/-- The empty family is a member of the family's type. -/
theorem famZero_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (σ : Nat → Nat) :
    famZero P μ fd σ ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ0 (famType fd)) := by
  refine piLam_mem (mkM P μ) σ (envResp_const _) _ ρ0 ?_
  unfold famType
  apply piGood_policyPi
  intro ρ'
  show tyv pempty ∈ Ed (mkM P μ) (tyv ((mkM P μ).U (evalTotal σ fd.resLevel)))
  exact mem_congr_right (ed_tyv (mkM P μ) (U4_dich _)).symm (tyv_pempty_mem_U4 P _)

/-- **Every iterate is a member of the family's type**, read at the base
table: the stage-`0` entry is the empty family, the stage-`n+1` entry a family
value at the previous stage table (`famVal_mem`, at any table). -/
theorem famIter_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false) :
    ∀ n vs, famIter P μ fd n vs ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 (famType fd))
  | 0, vs => famZero_mem P μ fd (σOf vs)
  | n + 1, vs => by
      have h := famVal_mem P (mkM P (tabIter P μ fd n)) rfl (σOf vs) fd ρ0
      rw [ed_mkM P _ μ] at h
      rw [show tabIter P μ fd n = upd μ fd.fref (famIter P μ fd n) from rfl,
        den_famType_upd P μ fd hpf] at h
      exact h

/-- **The limit is a member of the family's type**: each end value of the
limit is the union of the iterates' end fibres, a code of the family's
universe (closure of the stage under countable unions, `stageN_W4`, and the
union's dichotomy, `dich_iUnion_famEnd`). -/
theorem famLim_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (vs : List Nat) :
    famLim P μ fd vs ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 (famType fd)) := by
  refine piLam_mem (mkM P μ) (σOf vs) (limEnd_resp P μ fd (σOf vs)) _ ρ0 ?_
  unfold famType
  apply piGood_policyPi
  intro ρ'
  show limEnd P μ fd (σOf vs) ρ' ∈ Ed (mkM P μ) (tyv ((mkM P μ).U (evalTotal (σOf vs) fd.resLevel)))
  refine mem_congr_right (ed_tyv (mkM P μ) (U4_dich _)).symm ?_
  show tyv _ ∈ U W4 (evalTotal (σOf vs) fd.resLevel)
  have hD := dich_iUnion_famEnd P μ fd (σOf vs) ρ'
  have hW : iUnionN (fun n => El (famEnd (mkM P (tabIter P μ fd n)) W4 (σOf vs) fd ρ')) ∈
      W4 (evalTotal (σOf vs) fd.resLevel) :=
    stageN_W4 P.c0 P.c1 P.c2 P.c3 _ _ fun n => el_famEnd_mem P _ (σOf vs) fd ρ'
  cases h0 : evalTotal (σOf vs) fd.resLevel with
  | zero =>
      refine (mem_sImage_tyv).mpr ⟨_, mem_propSets.mpr fun y hy => ?_, Equiv.rfl⟩
      obtain ⟨n, hn⟩ := mem_iUnionN.mp hy
      revert hn
      unfold famEnd Rcic.F3.PSet.cond
      dsimp only [mkM]
      cases P.dec (evalTotal (σOf vs) fd.resLevel = 0) with
      | isTrue _ => exact fun hn => (mem_tv.mp (mem_congr_right el_tyv hn)).2
      | isFalse hne => exact absurd h0 hne
  | succ k =>
      rw [h0] at hW
      show _ ∈ sImage tyv (sep Dich (W4 (k + 1)))
      obtain ⟨i, hi⟩ := hW
      exact (mem_sImage_tyv).mpr ⟨_, mem_sep.mpr ⟨i, (dich_congr hi.symm).mp hD, hi⟩, Equiv.rfl⟩

/-- A family member is sound when its table entry is a member of its type at
every instance (the landed `fam_member_sound` asks for the fixed point; only
this membership is read). -/
theorem fam_member_sound_of_mem (P : Premises4) {μ : Nat → List Nat → PSet.{4}} {K : Nat → Nat} {f : Nat}
    {fm : CheckedMember}
    (hM : ∀ vs, μ f vs ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 fm.mtype))
    (hcl : ∀ k, Rcic.Declarative.lift k 1 fm.mtype = fm.mtype)
    (hlvl : exprLevelsBounded fm.arity fm.mtype = true) (hbody : fm.body = none) : MemberSound P μ K f fm := by
  intro σ ls ρ hlen _
  refine ⟨?_, fun b hb => by rw [hbody] at hb; cases hb⟩
  rw [den_inst_canon (mkM P μ) σ ls ρ fm.mtype hcl (hlen ▸ hlvl)]
  exact hM _

/-! ## §3 the chain, controlled at the canonical instance -/

/-- The canonical universe vector, read at an instance of its length, is the
instance. -/
theorem canonL_map_σOf (vs : List Nat) : (canonL vs.length).map (evalTotal (σOf vs)) = vs := by
  refine List.ext_getElem (by simp [canonL]) fun i h1 h2 => ?_
  simp only [canonL, List.getElem_map, List.getElem_range, evalTotal, σOf, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some]

/-- **The fibres of data whose recursive fields are canonical family
applications read the family only at the canonical instance**: overriding the
family entry by two values that agree there gives `≈`-equal end values. -/
theorem famEnd_upd_equiv (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
    (hcls : ∀ c, c ∈ fd.ctors → ∀ A, A ∈ c.1 → occursConst fd.fref A = false ∨ RecApp fd ar A)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat)
    (hX : Equiv (X₁ ((canonL ar).map (evalTotal σ))) (X₂ ((canonL ar).map (evalTotal σ))))
    (hsm₁ : ∀ ρ args, (∀ e, e ∈ args → occursConst fd.fref e = false) →
      args.length = (fd.params ++ fd.indices).length →
      Ed (mkM P (upd μ fd.fref X₁)) (den (mkM P (upd μ fd.fref X₁)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)) ∈
        W4 (evalTotal σ fd.resLevel))
    (hsm₂ : ∀ ρ args, (∀ e, e ∈ args → occursConst fd.fref e = false) →
      args.length = (fd.params ++ fd.indices).length →
      Ed (mkM P (upd μ fd.fref X₂)) (den (mkM P (upd μ fd.fref X₂)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)) ∈
        W4 (evalTotal σ fd.resLevel))
    (ρ : Nat → PSet.{4}) :
    Equiv (famEnd (mkM P (upd μ fd.fref X₁)) W4 σ fd ρ) (famEnd (mkM P (upd μ fd.fref X₂)) W4 σ fd ρ) := by
  have hrec : ∀ Xa Xb : List Nat → PSet.{4},
      Equiv (Xa ((canonL ar).map (evalTotal σ))) (Xb ((canonL ar).map (evalTotal σ))) →
      ∀ ρ args, (∀ e, e ∈ args → occursConst fd.fref e = false) →
      args.length = (fd.params ++ fd.indices).length → ∀ z,
      z ∈ Ed (mkM P (upd μ fd.fref Xa)) (den (mkM P (upd μ fd.fref Xa)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)) →
      z ∈ Ed (mkM P (upd μ fd.fref Xb)) (den (mkM P (upd μ fd.fref Xb)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)) := by
    intro Xa Xb h ρ args hargs _ z hz
    rw [den_recApp P μ Xa σ ρ hargs, ed_mkM P _ μ] at hz
    rw [den_recApp P μ Xb σ ρ hargs, ed_mkM P _ μ]
    exact mem_congr_right (ed_congr _ (fapps_congr h _)) hz
  have h12 := famLE_upd P μ fd ar hcls hri X₁ X₂ σ (hrec X₁ X₂ hX) hsm₂
  have h21 := famLE_upd P μ fd ar hcls hri X₂ X₁ σ (hrec X₂ X₁ hX.symm) hsm₁
  unfold famEnd Rcic.F3.PSet.cond
  dsimp only [mkM]
  cases P.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue _ =>
      exact tyv_congr (ext fun _ => ⟨fun hz => PropFib_mono h12 hz, fun hz => PropFib_mono h21 hz⟩)
  | isFalse _ =>
      exact tyv_congr (ext fun _ => ⟨fun hz => TypeFib_mono h12 hz, fun hz => TypeFib_mono h21 hz⟩)

/-- Smallness of a canonical family application transfers along an entry
agreeing at the canonical instance. -/
theorem small_recApp_of_equiv (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
    (X₁ X₂ : List Nat → PSet.{4}) (σ : Nat → Nat) (W : PSet.{4})
    (hX : Equiv (X₁ ((canonL ar).map (evalTotal σ))) (X₂ ((canonL ar).map (evalTotal σ))))
    (ρ : Nat → PSet.{4}) (args : List (Expr Nat)) (hargs : ∀ e, e ∈ args → occursConst fd.fref e = false)
    (h : Ed (mkM P (upd μ fd.fref X₂)) (den (mkM P (upd μ fd.fref X₂)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)) ∈ W) :
    Ed (mkM P (upd μ fd.fref X₁)) (den (mkM P (upd μ fd.fref X₁)) σ ρ (foldApps (.const fd.fref (canonL ar)) args)) ∈ W := by
  rw [den_recApp P μ X₂ σ ρ hargs, ed_mkM P _ μ] at h
  rw [den_recApp P μ X₁ σ ρ hargs, ed_mkM P _ μ]
  exact mem_congr_left (ed_congr _ (fapps_congr hX _)).symm h

/-! ## §3b the stage induction at a D node -/

section Node

variable {P : Premises4} {K : Nat → Nat} {E E' : ResolvedEnv} {f rr : Nat} {rm : CheckedMember}

/-- What the stage induction reads at a node: the raw and normalized
constructor lists agree at every bounded instance, at every stage table of
the raw chain and at the table itself, and the normalized data is a
recursive group (`RecGroupD`). §4 (`dStage_of`) produces it from the base
invariant **in the order of the module header** — no fixed point assumed. -/
structure DStage (P : Premises4) (K : Nat → Nat) (node : RecNode E E' f rr rm)
    (μ : Nat → List Nat → PSet.{4}) : Prop where
  agreeT : ∀ n vs, (∀ v, v ∈ vs → v ≤ K rr) → vs.length = node.a.family.member.arity →
    AgreeAtD P (tabIter P μ (famDataOf node.a) n) node.a (fuelAt := node.h14.fuelAt) vs
  agree : ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → vs.length = node.a.family.member.arity →
    AgreeAtD P μ node.a (fuelAt := node.h14.fuelAt) vs
  RG : RecGroupD node.a node.h14.fuelAt node.h14.shapesAt

/-- The canonical instance of a bounded instance of the family's arity is
itself. -/
theorem canon_eq_of_length {ar : Nat} {vs : List Nat} (hlen : vs.length = ar) :
    (canonL ar).map (evalTotal (σOf vs)) = vs := by
  subst hlen
  exact canonL_map_σOf vs

/-- **The raw and normalized iterates agree at every bounded instance.** -/
theorem famIter_raw_norm {node : RecNode E E' f rr rm} {μ : Nat → List Nat → PSet.{4}}
    (D : DStage P K node μ) : ∀ n vs, (∀ v, v ∈ vs → v ≤ K rr) → vs.length = node.a.family.member.arity →
    Equiv (famIter P μ (famDataOf node.a) n vs) (famIter P μ (nodeFam node) n vs)
  | 0, _, _, _ => Equiv.rfl
  | n + 1, vs, hvs, hlen => by
      have hX : Equiv (famIter P μ (famDataOf node.a) n ((canonL node.a.family.member.arity).map (evalTotal (σOf vs))))
          (famIter P μ (nodeFam node) n ((canonL node.a.family.member.arity).map (evalTotal (σOf vs)))) := by
        rw [canon_eq_of_length hlen]
        exact famIter_raw_norm D n vs hvs hlen
      have hsm₂ := fun ρ args hargs hl =>
        small_rec_iter P μ (nodeFam node) node.a.family.member.arity D.RG.bounded D.RG.famFree n (σOf vs) ρ args
          hargs hl
      have hsm₁ := fun ρ args hargs hl =>
        small_recApp_of_equiv P μ (nodeFam node) node.a.family.member.arity _ _ (σOf vs) _ hX ρ args hargs
          (hsm₂ ρ args hargs hl)
      have h1 : Equiv (famIter P μ (famDataOf node.a) (n + 1) vs)
          (famVal (mkM P (tabIter P μ (famDataOf node.a) n)) W4 (σOf vs) (nodeFam node)) :=
        famVal_agree (mkM P (tabIter P μ (famDataOf node.a) n)) W4 (σOf vs) (famDataOf node.a)
          (nodeFam node).ctors (D.agreeT n vs hvs hlen)
      have hT : ∀ r, r ≠ (nodeFam node).fref → ∀ ls,
          Equiv (tabIter P μ (famDataOf node.a) n r ls) (tabIter P μ (nodeFam node) n r ls) := by
        intro r hr ls
        have e1 : tabIter P μ (famDataOf node.a) n r ls = μ r ls := upd_ne μ _ _ hr ls
        have e2 : tabIter P μ (nodeFam node) n r ls = μ r ls := upd_ne μ _ _ hr ls
        rw [e1, e2]
        exact Equiv.rfl
      have h2 : Equiv (famVal (mkM P (tabIter P μ (famDataOf node.a) n)) W4 (σOf vs) (nodeFam node))
          (famVal (mkM P (tabIter P μ (nodeFam node) n)) W4 (σOf vs) (nodeFam node)) :=
        piLam_tablesOn P hT (σOf vs) (famEnd_resp _ W4 _ _)
          (famEnd_upd_equiv P μ (nodeFam node) node.a.family.member.arity D.RG.cls (RecGroupD.ri node.a D.RG)
            _ _ (σOf vs) hX hsm₁ hsm₂) _ (famType_refs_ne (nodeFam node) D.RG.famFree) ρ0
      exact h1.trans h2

/-- **The raw and normalized limits agree at every bounded instance.** -/
theorem famLim_raw_norm {node : RecNode E E' f rr rm} {μ : Nat → List Nat → PSet.{4}}
    (D : DStage P K node μ) (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr)
    (hlen : vs.length = node.a.family.member.arity) :
    Equiv (famLim P μ (famDataOf node.a) vs) (famLim P μ (nodeFam node) vs) := by
  have hparR : RefsIn (fun r => r ≠ (famDataOf node.a).fref) (famDataOf node.a).params := fun e he r hr =>
    denRefs_ne_of_occurs e (D.RG.famFree e (List.mem_append_left _ he)) r hr
  have hstage : ∀ n (ps is : List PSet.{4}), TelFits (mkM P μ) (σOf vs) (famDataOf node.a).params ρ0 ps →
      is.length = (famDataOf node.a).indices.length →
      Equiv (famEnd (mkM P (tabIter P μ (famDataOf node.a) n)) W4 (σOf vs) (famDataOf node.a) (push (ps ++ is) ρ0))
        (famEnd (mkM P (tabIter P μ (nodeFam node) n)) W4 (σOf vs) (nodeFam node) (push (ps ++ is) ρ0)) := by
    intro n ps is hps hl
    have hX : Equiv (famIter P μ (famDataOf node.a) n ((canonL node.a.family.member.arity).map (evalTotal (σOf vs))))
        (famIter P μ (nodeFam node) n ((canonL node.a.family.member.arity).map (evalTotal (σOf vs)))) := by
      rw [canon_eq_of_length hlen]
      exact famIter_raw_norm D n vs hvs hlen
    have hsm₂ := fun ρ args hargs hl =>
      small_rec_iter P μ (nodeFam node) node.a.family.member.arity D.RG.bounded D.RG.famFree n (σOf vs) ρ args
        hargs hl
    have hsm₁ := fun ρ args hargs hl =>
      small_recApp_of_equiv P μ (nodeFam node) node.a.family.member.arity _ _ (σOf vs) _ hX ρ args hargs
        (hsm₂ ρ args hargs hl)
    have hps' : TelFits (mkM P (tabIter P μ (famDataOf node.a) n)) (σOf vs) (famDataOf node.a).params ρ0 ps :=
      (TelFits_agreeOn P (agreeOn_upd_off μ (famDataOf node.a).fref (famIter P μ (famDataOf node.a) n)) (σOf vs)
        _ hparR ρ0 ps).mpr hps
    have h1 : Equiv (famEnd (mkM P (tabIter P μ (famDataOf node.a) n)) W4 (σOf vs) (famDataOf node.a)
          (push (ps ++ is) ρ0))
        (famEnd (mkM P (tabIter P μ (famDataOf node.a) n)) W4 (σOf vs) (nodeFam node) (push (ps ++ is) ρ0)) := by
      refine famEnd_agree _ W4 (σOf vs) (famDataOf node.a) (nodeFam node).ctors _ ?_
      rw [push_append, ← hl, shiftρ_push]
      exact D.agreeT n vs hvs hlen ps hps'
    exact h1.trans (famEnd_upd_equiv P μ (nodeFam node) node.a.family.member.arity D.RG.cls
      (RecGroupD.ri node.a D.RG) _ _ (σOf vs) hX hsm₁ hsm₂ _)
  show Equiv (piLam (mkM P μ) (σOf vs) (limEnd P μ (famDataOf node.a) (σOf vs)) ρ0
      (policyPi ((famDataOf node.a).params ++ (famDataOf node.a).indices) (.sort (famDataOf node.a).resLevel)))
    (piLam (mkM P μ) (σOf vs) (limEnd P μ (nodeFam node) (σOf vs)) ρ0
      (policyPi ((famDataOf node.a).params ++ (famDataOf node.a).indices) (.sort (famDataOf node.a).resLevel)))
  refine piLam_congr_fits (mkM P μ) (σOf vs) (.sort (famDataOf node.a).resLevel)
    (fun _ _ h => Expr.noConfusion h) _ ρ0 fun xs hxs => ?_
  obtain ⟨ps, is, rfl, hps, his⟩ := TelFits_split (famDataOf node.a).params (famDataOf node.a).indices _ xs hxs
  have hl : is.length = (famDataOf node.a).indices.length := his.length
  refine tyv_congr (ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
  · obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
    exact mem_iUnionN.mpr ⟨n, mem_congr_right (el_congr (hstage n ps is hps hl)) hn⟩
  · obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
    exact mem_iUnionN.mpr ⟨n, mem_congr_right (el_congr (hstage n ps is hps hl)).symm hn⟩

/-- **The raw-role table entry is the raw family value at every bounded
instance**: the limit agreement, the normalized fixed point, the canonical
reading, and the agreement at the table itself. -/
theorem famB_raw {node : RecNode E E' f rr rm} {μ : Nat → List Nat → PSet.{4}} (D : DStage P K node μ)
    (hlim : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (famDataOf node.a) vs))
    (vs : List Nat) (hvs : ∀ v, v ∈ vs → v ≤ K rr) (hlen : vs.length = node.a.family.member.arity) :
    Equiv (μ node.a.family.ref vs) (famVal (mkM P μ) W4 (σOf vs) (famDataOf node.a)) := by
  have e1 : Equiv (μ node.a.family.ref vs) (famLim P μ (nodeFam node) vs) :=
    (hlim vs).trans (famLim_raw_norm D vs hvs hlen)
  have e2 := (famLim_fix P μ (nodeFam node) node.a.family.member.arity D.RG.bounded D.RG.famFree D.RG.cls
    (RecGroupD.ri node.a D.RG) vs).symm
  have hX : Equiv (famLim P μ (nodeFam node) ((canonL node.a.family.member.arity).map (evalTotal (σOf vs))))
      (μ (nodeFam node).fref ((canonL node.a.family.member.arity).map (evalTotal (σOf vs)))) := by
    rw [canon_eq_of_length hlen]
    exact e1.symm
  have hsm₁ := fun ρ args hargs hl =>
    small_rec_lim P μ (nodeFam node) node.a.family.member.arity D.RG.bounded D.RG.famFree (σOf vs) ρ args hargs hl
  have hsm₂ := fun ρ args hargs hl =>
    small_recApp_of_equiv P μ (nodeFam node) node.a.family.member.arity _ _ (σOf vs) _ hX.symm ρ args hargs
      (hsm₁ ρ args hargs hl)
  have hT : ∀ r, r ≠ (nodeFam node).fref → ∀ ls,
      Equiv (tabLim P μ (nodeFam node) r ls) (upd μ (nodeFam node).fref (μ (nodeFam node).fref) r ls) := by
    intro r hr ls
    have e1 : tabLim P μ (nodeFam node) r ls = μ r ls := upd_ne μ _ _ hr ls
    have e2 : upd μ (nodeFam node).fref (μ (nodeFam node).fref) r ls = μ r ls := upd_ne μ _ _ hr ls
    rw [e1, e2]
    exact Equiv.rfl
  have e3 := piLam_tablesOn P hT (σOf vs) (famEnd_resp _ W4 _ _)
    (famEnd_upd_equiv P μ (nodeFam node) node.a.family.member.arity D.RG.cls (RecGroupD.ri node.a D.RG)
      _ _ (σOf vs) hX hsm₁ hsm₂) _ (famType_refs_ne (nodeFam node) D.RG.famFree) ρ0
  have hμ : upd μ (nodeFam node).fref (μ (nodeFam node).fref) = μ := by
    funext r ls
    by_cases h : r = (nodeFam node).fref
    · subst h; exact upd_eq μ _ _ ls
    · exact upd_ne μ _ _ h ls
  rw [hμ] at e3
  have e4 := (famVal_agree (mkM P μ) W4 (σOf vs) (famDataOf node.a) (nodeFam node).ctors (D.agree vs hvs hlen)).symm
  exact e1.trans (e2.trans (e3.trans e4))

end Node

/-! ## §4 the order: the stage data from the base invariant, and the raw-role
group faithfulness -/

section Order

variable {P : Premises4} {K : Nat → Nat} {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
  {ctors : List (Nat × CheckedMember)}

/-- **The order, compiled.** At a group whose nodes have no
function-recursive shape (`NoFunRec` — exactly `¬ PendA`), whose
constructor views carry the family's parameters (`hpar`), within the bounds
(`BoundG` of the base, the fields' typings of `BoundDG`), from the base
invariant and faithfulness on the base at the raw roles, and the raw family
limit at the family: the stage data. The steps are those of the module
header: base invariant at each stage table (§1), the family member by
membership (§2), the constructor scope sound there, the landed
`agreeAt_of_typings`. No fixed point is assumed. -/
theorem dStage_of (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (hsh : NoFunRec node)
    (hpar : ∀ i : Fin node.a.constructors.length, (node.a.constructorViews i).parameters = node.a.family.parameters)
    (hBG : BoundG K hE)
    (hDG : ∀ (i : Fin node.a.constructors.length) (vs : List Nat),
        vs.length = node.a.family.member.arity → (∀ v, v ∈ vs → v ≤ K rr) →
        ∀ k : Fin (node.a.constructorViews i).fields.length, ∃ l : Level,
          ∃ d : HasTyT (extendEnv E f fm) node.a.family.member.arity
            (policyPrefixContext ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields)
              ((node.a.constructorViews i).parameters.length + k.val))
            ((node.a.constructorViews i).fields[k]) (.sort l), LOKt (σOf vs) 4 K d)
    (IH : GInv P K hE) (ctx : Nat → Role) (hctxE : ∀ r, Dom E r → ctx r = envCtx hE r)
    (μ : Nat → List Nat → PSet.{4}) (hFE : FaithfulR P μ ctx E)
    (hlim : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (famDataOf node.a) vs)) :
    DStage P K node μ := by
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  obtain ⟨hf0, _, hf', _, _⟩ := group_refs hmem hL hrr
  have hsubE : ∀ r m, E.members r = some m → E'.members r = some m := groupMembersT_preserve hmem
  have hTF : TypeFacts E' := typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)
  have hbody := PSet.groupMembersT_body_none hmem
  have hSsub : ∀ r m, (extendEnv E f fm).members r = some m → E'.members r = some m := by
    intro r m h
    by_cases hr : r = f
    · subst hr; rw [members_extend_eq] at h; cases h; exact hf'
    · rw [members_extend_ne E f fm r hr] at h; exact hsubE r m h
  have hbf : fm.body = none := hbody f fm (List.mem_cons_self _ _)
  have hfmm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfmm, node.a.family.storedType]; rfl
  have hfr : (famDataOf node.a).fref = f := node.fam
  have hFF : FamFreeBodies node.E0 node.a.family.ref := by
    rw [node.fam]; exact famFreeBodies_node hE hf0 hmem node
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
  have hR : ReadsClosed ctx E := readsClosed_envCtx P hE ctx hctxE
  have hcl := (hTF f fm hf').1
  have hlvl := (hTF f fm hf').2.1
  -- the constructor scope is sound at every table faithful on the base where the family member is sound
  have hES : ∀ T : Nat → List Nat → PSet.{4}, FaithfulR P T ctx E → MemberSound P T K f fm →
      ∀ σ n, EnvSound (mkM P T) σ K (extendEnv E f fm) n := by
    intro T hFT hfmS σ n
    have IHT := IH ctx hctxE T hFT
    refine envSound_of P hSsub ?_ ?_ σ n
    · intro r m h
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; exact hfmS
      · rw [members_extend_ne E f fm r hr] at h; exact IHT.1 r m h
    · intro r m h hk
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at h; cases h; rw [hfam] at hk; cases hk
      · rw [members_extend_ne E f fm r hr] at h; exact IHT.2 E' hsubE r m h hk
  have hbodies : ∀ σ, BodiesOK (extendEnv E f fm) σ K := fun σ =>
    bodiesOK_of_envWfT K hE hBG (fun r m h => members_extend_preserved hf0 r m h) (fun r m hm h0 => by
      by_cases hr : r = f
      · subst hr; rw [members_extend_eq] at hm; cases hm; exact hbf
      · rw [members_extend_ne E f fm r hr] at hm; rw [hm] at h0; cases h0) σ
  have hwhnf : ∀ fuel e, whnfFuel node.E0 fuel e = whnfFuel (extendEnv E f fm) fuel e :=
    whnfFuel_eq_along hmem node.base (node_sub' node) (fun r m h => members_extend_preserved hf0 r m h) hSsub
  have hag : ∀ T : Nat → List Nat → PSet.{4}, FaithfulR P T ctx E → MemberSound P T K f fm →
      ∀ vs, (∀ v, v ∈ vs → v ≤ K rr) → vs.length = node.a.family.member.arity →
      AgreeAtD P T node.a (fuelAt := node.h14.fuelAt) vs := fun T hFT hfmS vs hvs hlen =>
    agreeAt_of_typings P T K node vs (hES T hFT hfmS (σOf vs) _) (hbodies (σOf vs)) hwhnf hpar
      (fun i k => hDG i vs hlen hvs k)
  -- the stage tables: faithful on the base, the family member sound by membership
  have hf0' : E.members (famDataOf node.a).fref = none := by rw [hfr]; exact hf0
  have hFT : ∀ n, FaithfulR P (tabIter P μ (famDataOf node.a) n) ctx E := fun n =>
    faithfulR_upd_fresh P hFE hR hf0' _
  have hfmT : ∀ n, MemberSound P (tabIter P μ (famDataOf node.a) n) K f fm := by
    intro n
    refine fam_member_sound_of_mem P (fun vs => ?_) hcl hlvl hbf
    have hent : tabIter P μ (famDataOf node.a) n f vs = famIter P μ (famDataOf node.a) n vs := by
      exact if_pos hfr.symm
    rw [hent, hty, show tabIter P μ (famDataOf node.a) n = upd μ (famDataOf node.a).fref
      (famIter P μ (famDataOf node.a) n) from rfl, den_famType_upd P μ _ hpfF, ed_mkM P _ μ]
    exact famIter_mem P μ _ hpfF n vs
  have hfmμ : MemberSound P μ K f fm := by
    refine fam_member_sound_of_mem P (fun vs => ?_) hcl hlvl hbf
    rw [hty]
    have h := hlim vs
    rw [node.fam] at h
    exact mem_congr_left h.symm (famLim_mem P μ _ vs)
  exact ⟨fun n => hag _ (hFT n) (hfmT n), hag μ hFE hfmμ, RG⟩

/-- **The family member is sound in the raw roles**, at every instance, from
the raw limit at the family alone — no fixed point. -/
theorem fam_member_sound_raw (hE : EnvWfT E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM) (hrec : rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm) (μ : Nat → List Nat → PSet.{4})
    (hlim : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (famDataOf node.a) vs)) :
    MemberSound P μ K f fm := by
  obtain ⟨hL, hrr⟩ := group_layout_of_walkRec hE hfam hctors hrec hmem (walkRec_of_group hmem)
  obtain ⟨_, _, hf', _, _⟩ := group_refs hmem hL hrr
  have hTF : TypeFacts E' := typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)
  have hfmm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfmm, node.a.family.storedType]; rfl
  refine fam_member_sound_of_mem P (fun vs => ?_) (hTF f fm hf').1 (hTF f fm hf').2.1
    (PSet.groupMembersT_body_none hmem f fm (List.mem_cons_self _ _))
  rw [hty]
  have h := hlim vs
  rw [node.fam] at h
  exact mem_congr_left h.symm (famLim_mem P μ _ vs)

/-- **`GroupFaithB` in the raw roles.** At a table faithful to the raw group
roles (`groupRoles (famDataOf …)`, what `envCtx` installs), with the stage
data: the family at every instance within the recursor's bound, the
constructors and the recursor at every instance. -/
theorem groupFaithB_raw {ctx ctx0 : Nat → Role}
    (hmem : GroupMembersT (extendEnv E f fm) E ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (hL : ctors.map Prod.fst = (List.range ctors.length).map (fun i => f + 1 + i))
    (hrr : rr = f + 1 + ctors.length) (node : RecNode E E' f rr rm) {μ : Nat → List Nat → PSet.{4}}
    (hF : FaithfulR P μ ctx E')
    (hctx : ∀ r, Dom E' r → ctx r = groupRoles (famDataOf node.a) f rr ctx0 r) (hTF : TypeFacts E')
    (D : DStage P K node μ) : GroupFaithB P μ K fm node := by
  obtain ⟨_, _, hf', hr', _⟩ := group_refs hmem hL hrr
  have hlen := node_ctors_length node hrr
  have hfm : node.a.family.member = fm := Option.some.inj ((node_fam_member node).symm.trans hf')
  have hty : fm.mtype = famType (famDataOf node.a) := by rw [← hfm, node.a.family.storedType]; rfl
  have hlim : ∀ vs, Equiv (μ node.a.family.ref vs) (famLim P μ (famDataOf node.a) vs) := fun vs => by
    have h := hF f fm hf' vs
    rw [hctx f (dom_of_members hf'), groupRoles_at_f] at h
    rw [node.fam]
    exact h
  refine ⟨fun vs hvs hl => ?_, fun i vs => ?_, fun vs => ?_, hty, famBounded_node node hTF, fun i => ?_⟩
  · rw [hty]
    have h := famB_raw D hlim vs hvs hl
    rw [node.fam] at h
    exact h
  · have hc := node_ctor_member node i
    have h := hF _ _ hc vs
    rw [hctx _ (dom_of_members hc), groupRoles_at_ctor _ _ (by have := i.isLt; omega)] at h
    exact h
  · have h := hF rr rm hr' vs
    rw [hctx rr (dom_of_members hr'), groupRoles_at_rr _ (by omega)] at h
    exact h
  · have hb' := (hTF _ _ (node_ctor_member node i)).2.1
    rw [(node.a.constructorViews i).arity] at hb'
    exact hb'

end Order

/-! ## §5 the measured boundary (what the group step still owes)

`StepDG P K` (`RcicF3TierGroup`) owes `GroupStepAt` — `GInv hE → GInv group`
in the raw roles — at every group with a `PendD` node and no `PendA` node.
With §1–§4 the raw-role group step has, at every table faithful to the raw
roles: the family member's soundness at every instance
(`fam_member_sound_raw`), the constructor scope sound (`dStage_of`'s
`hES`), and `GroupFaithB` (`groupFaithB_raw`) — which is exactly what the
landed `iota_at_D` and `rec_member_soundB` consume. What remains:

* **The recursor's membership** (`Type` groups and `Prop` into `Prop`). The
  landed `recVal_mem_recD`/`recVal_mem_recPD` (through `minor_ok_groupD`,
  `rec_fields_okD`, `rec_stageD`) take the normalized limit at the family at
  *every* instance (`hLim`), but read it only at the recursor's own family
  instance: through `famμ_of_lim_fd` (supplied by `famB_raw`), through
  `tabLim_equivD` inside `famLE_tables` (the `CtorFits` of the normalized,
  canonical fields) and inside `den_tables` (a canonical family
  application). All three are canonical reads, which `famEnd_upd_equiv` and
  `den_recApp` perform at one instance. The bounded restatement is
  mechanical; it is not in this module.
* **The constructors' soundness at instances above the recursor's bound.**
  `ctor_member_sound_norm` reads the family value at the constructor's own
  instances (`≤ K c`); the raw chain is controlled at `≤ K rr`. Above `K rr`
  the other constructors' δ-hidden fields carry no bounded typing, their
  denotation need not be their normal form's, and the raw chain need not
  grow at that instance — the common-stage argument for a constructor with
  two recursive fields has nothing to stand on. The weakest checked side
  condition this route needs is the finite order check `K c ≤ K rr` for the
  group's constructors (the converse of the landed `RecBelowCtors`); under
  both, the constructors and the recursor share one bound.
* The `GroupClassD` corners outside `¬ PendA`: `hpar` (each constructor
  view's parameters are the family's — syntactic list equality, decidable)
  and the `Prop`/`anySort` clause (family-free, unrevealed fields — the
  B/C lanes' shapes), both read by the landed recursor/ι lemmas.
-/

end Rcic.F3.StepDGOrder
