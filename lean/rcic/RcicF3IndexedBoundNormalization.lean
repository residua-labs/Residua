import rcic.RcicF3IndexedFieldBounds
import rcic.RcicF3EvalPlanNormalTuple

/-!
# Ordinary bounded rows normalize without the all-Prop field clause

The transparent-body argument is generalized to the existing EnvBound
predicate: it uses the stored bounded definition derivation and the actual
predecessor member/iota soundness. It never needs any constructor field to
be a proof. BoundGIndexed supplies EnvBound by its checked admission fold.

The same body facts and each ordinary row of IndexedFieldBounds.Rows then
produce reverse normalization at an actual growing ordinary-field prefix.
The final theorem composes this with the existing guarded recursive slice
transport to reconstruct the complete original field tuple from the actual
normalized tuple. No comparator, normalization equation, BodiesRegular,
candidate closure, or completed-group soundness is an added premise.

This is a component for a separate broader bound. The original BoundG,
the current checked-tier producer and all check definitions are untouched.
closure_claim = 0; scope_closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.IndexedBoundNormalization

open Rcic.Declarative Rcic.Model.PS PiHereditary IndexedFieldBounds
open RawFamily PiValueRule

/-- Stored definition bounds suffice for both constant-instance validity
and hereditary regularity of transparent bodies. The body-free group case
passes the predecessor's EnvBound literally. -/
theorem transparent_facts (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) {S Efin : ResolvedEnv}
    (hAS : AllSound P μ K S)
    (hIS : ∀ r m, S.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r)
    (hSfin : ∀ r m, S.members r = some m → Efin.members r = some m) :
    {E : ResolvedEnv} → (hW : EnvWfT E) → EnvBound K hW →
    (∀ r m, E.members r = some m → S.members r = some m) →
    ∀ r m b, E.members r = some m → m.body = some b → transparent m.mclass = true →
      exprLevelsBounded 0 b = true ∧ InstOK S (fun _ => 0) K b ∧
        ∀ σ ρ, Regular (mkM P μ) σ b ρ
  | _, .empty, _, _, _, _, _, h, _, _ => Option.noConfusion h
  | _, .axiom E r0 _ _ hE hfresh _ _ _, hB, hsub, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        cases hb
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_facts P μ K hAS hIS hSfin hE hB
          (fun r' m' hm => hsub r' m' (members_extend_preserved hfresh r' m' hm))
          r m b h hb htr
  | _, .definition E r0 _ v _ hE hfresh _ hv _ _ _ hlvlv,
      hB, hsub, r, m, b, h, hb, htr => by
      have hpre : ∀ r' m', E.members r' = some m' → S.members r' = some m' :=
        fun r' m' hm => hsub r' m' (members_extend_preserved hfresh r' m' hm)
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        cases hb
        refine ⟨hlvlv, (instOK_of_lokt (fun _ => 0) 4 K hv hB.2).mono_env hpre, ?_⟩
        intro σ ρ
        have hES := envSound_of P (fun r' m' hm => hSfin r' m' (hpre r' m' hm))
          (allSound_prefix hpre hAS) (fun r' m' hm hk => hIS r' m' (hpre r' m' hm) hk)
          (fun _ => 0) 0
        have hs := hsound_ty (P.good _ rfl) hES hv hB.2
        exact (Regular.levelsClosed (mkM P μ) (fun _ => 0) σ v hlvlv ρ).mp
          (of_hsound (mkM P μ) (fun _ => 0) (fun k => pempty_not_mem_U4 P k)
            hv hs ρ True.intro)
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_facts P μ K hAS hIS hSfin hE hB.1 hpre r m b h hb htr
  | _, .thm E r0 _ _ hE hfresh _ _ _ _ _ _, hB, hsub, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact absurd htr Bool.false_ne_true
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_facts P μ K hAS hIS hSfin hE hB.1
          (fun r' m' hm => hsub r' m' (members_extend_preserved hfresh r' m' hm))
          r m b h hb htr
  | _, .opaque E r0 _ _ _ hE hfresh _ _ _ _ _ _, hB, hsub, r, m, b, h, hb, htr => by
      by_cases hr : r = r0
      · subst hr
        rw [members_extend_eq] at h
        cases h
        exact absurd htr Bool.false_ne_true
      · rw [members_extend_ne E r0 _ r hr] at h
        exact transparent_facts P μ K hAS hIS hSfin hE hB.1
          (fun r' m' hm => hsub r' m' (members_extend_preserved hfresh r' m' hm))
          r m b h hb htr
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem, hB, hsub, r, m, b, h, hb, htr => by
      rcases groupMembersT_cases hmem r m h with h1 | h1
      · exact transparent_facts P μ K hAS hIS hSfin hE hB
          (fun r' m' hm => hsub r' m' (groupMembersT_preserve hmem r' m' hm))
          r m b h1 hb htr
      · rw [groupMembersT_body_none hmem r m h1] at hb
        cases hb

/-- Both normalization conditions are produced in a body-free extension of
the predecessor, from EnvBound and that predecessor's actual soundness. -/
theorem bodies_conditions (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat) {E Efin E₁ : ResolvedEnv}
    (hW : EnvWfT E) (hB : EnvBound K hW) (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r)
    (hfin : ∀ r m, E.members r = some m → Efin.members r = some m)
    (hsub : ∀ r m, E.members r = some m → E₁.members r = some m)
    (hnew : ∀ r m, E₁.members r = some m → E.members r = none → m.body = none)
    (σ : Nat → Nat) : BodiesOK E₁ σ K ∧ BodiesRegular (mkM P μ) σ K E₁ := by
  have facts : ∀ r m b, E₁.members r = some m → m.body = some b →
      transparent m.mclass = true → exprLevelsBounded 0 b = true ∧
      InstOK E (fun _ => 0) K b ∧ ∀ τ ρ, Regular (mkM P μ) τ b ρ := by
    intro r m b hm hb htr
    cases h1 : E.members r with
    | none =>
        rw [hnew r m hm h1] at hb
        cases hb
    | some m' =>
        have h2 := hsub r m' h1
        rw [hm] at h2
        cases h2
        exact transparent_facts P μ K hA hI hfin hW hB
          (fun _ _ h => h) r m b h1 hb htr
  constructor
  · intro r m b ls hm hb htr _ _
    have hf := facts r m b hm hb htr
    exact (instOK_closed_inst (fun _ => 0) σ K hf.1 hf.2.1 ls).mono_env hsub
  · intro r m b ls hm hb htr _ _ ρ
    have hf := facts r m b hm hb htr
    rw [Ann.instantiateLevels_closed ls b hf.1]
    exact hf.2.2 σ ρ

/-- Generic typed normalization with only stored body bounds. -/
theorem den_piTelescope (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat) {E Efin E₁ : ResolvedEnv}
    (hW : EnvWfT E) (hB : EnvBound K hW) (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K Efin r)
    (hfin : ∀ r m, E.members r = some m → Efin.members r = some m)
    (hsub : ∀ r m, E.members r = some m → E₁.members r = some m)
    (hnew : ∀ r m, E₁.members r = some m → E.members r = none → m.body = none)
    {n : Nat} (hES : EnvSound (mkM P μ) σ K E₁ n)
    {Γ : LCtx} {T : Expr Nat} {l : Level} (d : HasTyT E₁ n Γ T (.sort l))
    (hd : LOKt σ 4 K d) {fuel : Nat} {ds : List (Expr Nat)} {b : Expr Nat}
    (hw : piTelescopeFuel E₁ fuel T = some (ds, b))
    (ρ : Nat → PSet.{4}) (hρ : Fits (mkM P μ) σ Γ ρ) :
    Equiv (den (mkM P μ) σ ρ (policyPi ds b)) (den (mkM P μ) σ ρ T) := by
  obtain ⟨hb, hR⟩ := bodies_conditions P μ K hW hB hA hI hfin hsub hnew σ
  exact den_piTelescope_typed4 P μ σ K hES hb hR d hd hw ρ hρ

/-- The actual family-only prefix gets both body conditions. New family
and constructor declarations cannot introduce a transparent body. -/
theorem family_prefix_bodies (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hB : BoundGIndexed K hE) (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (σ : Nat → Nat) :
    BodiesOK (extendEnv E f fm) σ K ∧
      BodiesRegular (mkM P μ) σ K (extendEnv E f fm) := by
  have hfresh : E.members f = none :=
    groupMembersT_fresh_base hmem f fm (List.mem_cons_self _ _)
  have hbody : fm.body = none :=
    groupMembersT_body_none hmem f fm (List.mem_cons_self _ _)
  apply bodies_conditions P μ K hE (IndexedFieldBounds.envBound K hE hB)
    hA hI (groupMembersT_preserve hmem)
    (fun r m hm => members_extend_preserved hfresh r m hm) ?_ σ
  intro r m hm hn
  by_cases hr : r = f
  · subst r
    rw [members_extend_eq] at hm
    cases Option.some.inj hm
    exact hbody
  · rw [members_extend_ne E f fm r hr] at hm
    rw [hn] at hm
    cases hm

/-- One ordinary row pays reverse normalization at its actual fitting
prefix. The row's level is arbitrary; no proof-field premise is used. -/
theorem original_field_normalized (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat)
    {E E' : ResolvedEnv} {f rr : Nat} {fm rm : CheckedMember}
    {ctors : List (Nat × CheckedMember)}
    (hE : EnvWfT E) (hB : BoundGIndexed K hE)
    (hA : AllSound P μ K E)
    (hI : ∀ r m, E.members r = some m → m.mclass = .recursorM → IotaAt P μ K E' r)
    (hmem : GroupMembersT (extendEnv E f fm) E
      ((f, fm) :: ctors ++ [(rr, rm)]) E')
    (node : RecNode E E' f rr rm)
    (hES : EnvSound (mkM P μ) σ K (extendEnv E f fm) node.a.family.member.arity)
    (j : Fin node.a.constructors.length)
    (hRows : Rows (extendEnv E f fm) node.a.family.member.arity σ K
      node.a.family.parameters (node.a.constructorViews j).fields
      (node.a.constructorViews j).resultIndices)
    (k : Fin (node.a.constructorViews j).fields.length)
    (ps pre : List PSet.{4})
    (hps : TelFits (mkM P μ) σ node.a.family.parameters ρ0 ps)
    (hpre : TelFits (mkM P μ) σ ((node.a.constructorViews j).fields.take k.val)
      (push ps ρ0) pre)
    {fuel : Nat} {ds : List (Expr Nat)} {b : Expr Nat}
    (hw : piTelescopeFuel node.E0 fuel ((node.a.constructorViews j).fields[k]) =
      some (ds, b)) :
    Equiv (den (mkM P μ) σ (push pre (push ps ρ0)) (policyPi ds b))
      (den (mkM P μ) σ (push pre (push ps ρ0)) ((node.a.constructorViews j).fields[k])) := by
  obtain ⟨l, d, hd⟩ := hRows.ordinary k
  obtain ⟨hb, hR⟩ := family_prefix_bodies P μ K hE hB hA hI hmem σ
  exact den_piTelescope_typed4 P μ σ K hES hb hR d hd
    (CandidateScope.recNode_read hmem node hw) (push pre (push ps ρ0))
    (CandidateScope.fits_original_prefix P μ σ node.a.family.parameters
      (node.a.constructorViews j).fields k ps pre hps hpre)

/-- The full normalized-to-original tuple bridge with the separate broader
bound. The recursive case uses the same full-key guarded slice and the
ordinary typed row just produced above, at every retained Pi depth. -/
theorem fields_to_raw_of_guarded (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (σ K : Nat → Nat) (p : EvalPlan.Plan)
    (fm : CheckedMember) (ctors : List (Nat × CheckedMember))
    (hE : EnvWfT p.E) (hfam : fm.mclass = .inductiveM)
    (hctors : ∀ c ∈ ctors, c.2.mclass = .constructorM)
    (hrec : p.rm.mclass = .recursorM)
    (hmem : GroupMembersT (extendEnv p.E p.f fm) p.E
      ((p.f, fm) :: ctors ++ [(p.rr, p.rm)]) p.E')
    (hB : BoundGIndexed K (EnvWfT.group p.E p.f fm ctors p.rr p.rm p.E'
      hE hfam hctors hrec hmem))
    (X D : Frame) (hX : Admissible (famDataOf p.node.a) X)
    (hD : Admissible (famDataOf p.node.a) D)
    (hA : AllSound P (table P μ (famDataOf p.node.a) D) K p.E)
    (hI : ∀ r m, p.E.members r = some m → m.mclass = .recursorM →
      IotaAt P (table P μ (famDataOf p.node.a) D) K p.E' r)
    (hES : EnvSound (mkM P (table P μ (famDataOf p.node.a) D)) σ K
      (extendEnv p.E p.f fm) p.node.a.family.member.arity)
    (h0 : evalTotal σ p.node.a.family.resultLevel = 0)
    (hpolicy : p.node.a.policy = .anySort)
    (vs : List Nat) (hσ : σ = σOf vs) (hvs : ∀ v, v ∈ vs → v ≤ K p.rr)
    (j : Fin p.node.a.constructors.length) (ps xs : List PSet.{4})
    (hps : TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      p.node.a.family.parameters ρ0 ps)
    (hsub : EvalPlanNormalSlice.GuardedSub p.node.a.family.member.arity
      p.node.a.family.parameters.length σ ps X D)
    (hxs : TelFits (mkM P (table P μ (famDataOf p.node.a) X)) σ
      (EvalPlanNormal.fields p j) (push ps ρ0) xs) :
    TelFits (mkM P (table P μ (famDataOf p.node.a) D)) σ
      (p.node.a.constructorViews j).fields (push ps ρ0) xs := by
  let MX := mkM P (table P μ (famDataOf p.node.a) X)
  let MD := mkM P (table P μ (famDataOf p.node.a) D)
  have hlen : (EvalPlanNormal.fields p j).length =
      (p.node.a.constructorViews j).fields.length :=
    (List.length_map _ _).trans (EvalPlanNormal.specs_length (p.constructors j).fields)
  have hRows : Rows (extendEnv p.E p.f fm) p.node.a.family.member.arity σ K
      p.node.a.family.parameters (p.node.a.constructorViews j).fields
      (p.node.a.constructorViews j).resultIndices := by
    rw [hσ]
    exact hB.2.2.2 p.node (selection_prop p.node.a σ h0 hpolicy).1 hpolicy j vs hvs
  apply EvalPlanNormal.tuple_transport MX MD σ (p.node.a.constructorViews j).fields
    (EvalPlanNormal.fields p j) hlen (push ps ρ0) ?_ xs hxs
  intro k hk pre hpre
  obtain ⟨prior, s, q, hprior, hq⟩ := EvalPlanNormal.field_at (p.constructors j).fields k hk
  have hkG : k < (EvalPlanNormal.fields p j).length := by rw [hlen]; exact hk
  have hget : (EvalPlanNormal.fields p j)[k]'hkG =
      fieldExpr p.node.a.family.ref (canonL p.node.a.family.member.arity)
        (EvalPlanNormal.fieldSpec q) :=
    Option.some.inj ((List.getElem?_eq_getElem hkG).symm.trans hq)
  have hpreLen : pre.length = prior := by
    have hl := hpre.length
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at hl
    exact hl.trans (by simpa only [Nat.zero_add] using hprior.symm)
  rw [hget]
  cases q with
  | plain hfree =>
      have he := PiIndependent.den_free P μ (famDataOf p.node.a).fref
        (ofFrame P μ (famDataOf p.node.a) X) (ofFrame P μ (famDataOf p.node.a) D)
        σ ((p.node.a.constructorViews j).fields[k]) hfree (push pre (push ps ρ0))
      intro x hx
      change x ∈ Ed MD (den MX σ (push pre (push ps ρ0))
        ((p.node.a.constructorViews j).fields[k])) at hx
      change den MX σ (push pre (push ps ρ0)) ((p.node.a.constructorViews j).fields[k]) =
        den MD σ (push pre (push ps ρ0)) ((p.node.a.constructorViews j).fields[k]) at he
      rw [he] at hx
      exact hx
  | recursive r =>
      intro x hx
      have hxN := EvalPlanNormalSlice.recursive_sub_of_guarded P μ (famDataOf p.node.a)
        X D hX hD σ r ps pre hps.length hpreLen hsub x hx
      have hn := original_field_normalized P (table P μ (famDataOf p.node.a) D)
        σ K hE hB.1 hA hI hmem p.node hES j hRows ⟨k, hk⟩ ps pre hps hpre r.read
      exact mem_congr_right (ed_congr MD hn) hxN

/-! ## Same-P component non-refutability on a concrete typed row -/

/-- Even the data-valued sort row has a bounded ordinary typing. Its
successful zero-domain reader composes with the produced body conditions
and the existing same-P sound prefix. -/
theorem sort_row_normalizes (P : Premises4) (K σ : Nat → Nat) :
    Equiv
      (den (mkM P PropEvalSafeIndex.witnessTable) σ ρ0
        (policyPi [] (.sort .zero)))
      (den (mkM P PropEvalSafeIndex.witnessTable) σ ρ0 (.sort .zero)) := by
  apply den_piTelescope P PropEvalSafeIndex.witnessTable σ K
    (E := emptyEnv) (Efin := emptyEnv) (E₁ := emptyEnv) EnvWfT.empty True.intro
    (fun _ _ h => by nomatch h) (fun _ _ h => by nomatch h)
    (fun _ _ h => h) (fun _ _ h => h) (fun _ _ h => by nomatch h)
    (PropEvalSafeIndex.witness_prefix_sound P K σ 0)
    (HasTyT.sort [] .zero) (by change 1 ≤ 4; decide)
    (fuel := 2) (by rfl) ρ0 True.intro

def Witness (P : Premises4) : Prop :=
  IndexedFieldBounds.Witness P ∧
  (∀ (K : Nat → Nat) σ, Equiv
    (den (mkM P PropEvalSafeIndex.witnessTable) σ ρ0 (policyPi [] (.sort .zero)))
    (den (mkM P PropEvalSafeIndex.witnessTable) σ ρ0 (.sort .zero)))

theorem component_witness (P : Premises4) : Witness P :=
  ⟨IndexedFieldBounds.component_witness P, sort_row_normalizes P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.IndexedBoundNormalization

#print axioms Rcic.F3.PSet.IndexedBoundNormalization.transparent_facts
#print axioms Rcic.F3.PSet.IndexedBoundNormalization.bodies_conditions
#print axioms Rcic.F3.PSet.IndexedBoundNormalization.den_piTelescope
#print axioms Rcic.F3.PSet.IndexedBoundNormalization.original_field_normalized
#print axioms Rcic.F3.PSet.IndexedBoundNormalization.fields_to_raw_of_guarded
#print axioms Rcic.F3.PSet.IndexedBoundNormalization.component_witness
#print axioms Rcic.F3.PSet.IndexedBoundNormalization.component_nonrefutable
