import rcic.RcicFamAppRevBack
import rcic.RcicFamAppTwinMetaOfPreds
import rcic.RcicTypedValidity

/-!
# RcicFamAppRevPiRow — THE Π ROW of ANY revealed singleton's environment, from its copy-only twin

`RcicFamAppPiRow` closed the Π row of the class-B fixture `riEnv`. This module is the same theorem for the
tier's generic B1 shape (`RevEnv`: an in-scope base, a closed level-free index type `I`, the family
`F : Π (i : I), Sort 0`, its constructor `mk : Π (x : I), F x`, its AnySort recursor), for EVERY such
environment — the obligation cc's 14:10Z addendum put on the closure path.

**Route.** The twin `R.twin₁` (the base, the family alone, the axiom `mk` at the constructor's own reference)
is admitted by the copy and has the three rows (`twin₁Rows`); its six metatheory facts come from its base
predicates (`TwinMeta.ofPreds`), which are proved here: closedness, substitution stability, sort-typing of
every member, level boundedness, and `IotaLevelsT` (the only non-vacuous one at a generic base: the twin's
recursors are the base's, so the landed `iotaLevelsT_of_envWfT` script runs through the base's arity window
`envWfT_group_arity`, and the legacy conjunct is read off `E`'s own witnesses through `bkWitness`). Then the
generic translation carries a chain between two Π's of `E` into the twin (`trTyConvW`), the twin's Π row
splits it, the identity transport brings the pieces back (`bkConv`, `bkTyConv`), and the round trip
`e ≡ tr e` (`trConv_self`, the K-like cell) identifies the ends with the originals.

**Results.** `RevEnv.revPiRow : PiRowField R.E n` and `RevEnv.revSortRow` (row 1) for every `n`, for every
`R : RevEnv`; axioms ⊆ {propext, Quot.sound}. The family row of `R.E` (the generic internal injectivity,
cc's item 2) is NOT here. closure_claim = 0.
-/

namespace Rcic.Syn.FamApp.Rev

open Rcic.Declarative
open Rcic.Syn.FamApp.RevTwin
open Rcic.Syn.FamApp (BasePreds TwinMeta tyConvT_ctx₀ piCompsTyped)

namespace RevEnv

variable (R : RevEnv)

/-! ## §1 the base predicates of the twin -/

theorem t1SubstStable : EnvMembersSubstStable R.twin₁ := fun r m hm =>
  let ⟨hclT, hclB⟩ := R.twin₁_closed r m hm
  ⟨fun ls s k =>
      lift_id_instantiate (instantiateLevels ls m.mtype) (instantiateLevels_closed hclT ls 0) k (Nat.zero_le k) s,
   fun b hb ls s k =>
      lift_id_instantiate (instantiateLevels ls b) (instantiateLevels_closed (hclB b hb) ls 0) k (Nat.zero_le k) s⟩

theorem t1Levels : EnvLevelsT R.twin₁ := by
  intro r m hm
  rcases R.twin₁_class hm with ⟨_, h0⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact envWfT_levels R.hW₀ r m h0
  · exact ⟨R.revFamTy_lvl, fun b hb => Option.noConfusion hb⟩
  · exact ⟨R.revCtorTy_lvl, fun b hb => Option.noConfusion hb⟩

theorem t1_body_lvl0 : ∀ r m b, R.twin₁.members r = some m → m.body = some b →
    exprLevelsBounded 0 b = true := by
  intro r m b hm hb
  rcases R.twin₁_class hm with ⟨_, h0⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact envWfT_body_lvl0 R.hW₀ r m b h0 hb
  · exact Option.noConfusion hb
  · exact Option.noConfusion hb

/-- the family-alone environment sits inside the twin. -/
theorem famEnv_sub : ∀ r m, R.famEnv.members r = some m → R.twin₁.members r = some m := fun r m h =>
  members_extendEnv_of_some R.famEnv (R.f + 1) (revAxM R.f R.I) (R.famEnv_fresh (R.f + 1) (by omega)) h

/-- every member of the twin is sort-typed at its arity: base members through the base's `EnvWfT`, the
    family and the axiom through their typings in the family-alone environment. -/
def t1SortTyped : EnvMembersSortTypedT R.twin₁ := fun r m hm => by
  by_cases h1 : r = R.f + 1
  · subst h1
    rw [R.twin₁_f1] at hm
    obtain rfl : revAxM R.f R.I = m := Option.some.inj hm
    exact ⟨.imax R.uI .zero, hasTyTExt R.famEnv_sub R.ctorTyT⟩
  · by_cases h0 : r = R.f
    · subst h0
      rw [R.twin₁_f] at hm
      obtain rfl : revFamM R.I = m := Option.some.inj hm
      exact ⟨.imax R.uI (.succ .zero), hasTyTExt R.famEnv_sub R.famTyT⟩
    · have h0' : R.E₀.members r = some m := by
        rw [twin₁_members, if_neg h1, if_neg h0] at hm; exact hm
      obtain ⟨u, hu⟩ := envWfT_mtypeSortTyped R.hW₀ r m h0'
      exact ⟨u, hasTyTExt R.twin₁_ext hu⟩

/-- a recursor of the twin, read in the base (the three member lookups). -/
theorem t1S_base (w : IotaWitnessS R.twin₁) :
    R.E₀.members w.recRef = some w.recMember ∧ R.E₀.members w.ctorRef = some w.ctorMember ∧
      R.E₀.members w.familyRef = some w.famMember := by
  have hrlt : w.recRef < R.f := by
    rcases R.twin₁_class w.hrec with ⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · have hk := w.hrecK; rw [h] at hk; exact MemberClass.noConfusion hk
    · have hk := w.hrecK; rw [h] at hk; exact MemberClass.noConfusion hk
  have hclt : w.ctorRef < R.f := by
    have h1 := w.hctorIdx; have h2 := w.hrecIdx; have h3 := w.hidx; omega
  have hflt : w.familyRef < R.f := by have h2 := w.hrecIdx; omega
  refine ⟨?_, ?_, ?_⟩
  · have h := w.hrec; rw [twin₁_members, if_neg (by omega), if_neg (by omega)] at h; exact h
  · have h := w.hctor; rw [twin₁_members, if_neg (by omega), if_neg (by omega)] at h; exact h
  · have h := w.hfam; rw [twin₁_members, if_neg (by omega), if_neg (by omega)] at h; exact h

/-- `IotaLevelsT` of the twin: the shape conjunct by the landed `iotaLevelsT_of_envWfT` script, the arity
    window read through the base; the legacy conjunct off `E`'s witnesses (`bkWitness`). -/
theorem t1IotaLevels : IotaLevelsT R.twin₁ :=
  ⟨fun w => by
      have hEL := R.t1Levels
      have hsup : ∀ r ls b, transparentBody R.twin₁ r ls = some b →
          exprLevelsBounded w.recMember.arity b = true :=
        fun _ _ _ htb => transparentBody_lvl0 R.t1_body_lvl0 htb
      obtain ⟨hrec0, hctor0, hfam0⟩ := R.t1S_base w
      have hctorA := (envWfT_group_arity R.hW₀ hctor0 (memberFamRef_ctorMemberS w) hfam0).1 w.hctorK
      have hrecA := (envWfT_group_arity R.hW₀ hrec0 (memberFamRef_recMemberS w) hfam0).2 w.hrecK
      have hle : w.ctorMember.arity ≤ w.recMember.arity := by
        rcases hrecA with h | h <;> omega
      have hbmt : exprLevelsBounded w.recMember.arity w.ctorMember.mtype = true :=
        exprLevelsBounded_mono hle _ (hEL w.ctorRef w.ctorMember w.hctor).1
      obtain ⟨hds, hres⟩ := peelPis_bounded _ _ w.hpeel hbmt
      have htel : exprLevelsBounded w.recMember.arity
          (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = true := by
        rw [exprLevelsBounded_lift]
        exact ctorFieldTelRaw_bounded hds hres
      have hrecB : exprLevelsBounded w.recMember.arity
          (.const w.recRef (canonRecLevels w.recMember.arity)) = true :=
        levelsBounded_canonRecLevels _
      have hminor : exprLevelsBounded w.recMember.arity
          (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx))) = true := rfl
      rw [w.hlsLen]
      exact iotaOpenRhs_bounded hsup hrecB hminor preMajorBvars_bounded fieldBvars_bounded htel w.hschema,
    fun w => (iotaLevelsT_of_envWfT R.hW).2 (R.bkWitness w)⟩

/-- **the twin's base predicates**, with its rows. -/
def t1Preds : BasePreds R.twin₁ :=
  ⟨R.twin₁_closed, R.t1SubstStable, R.t1SortTyped, R.t1Levels, R.t1IotaLevels, R.twin₁Rows⟩

/-- **the twin is a target of the generic translation.** -/
def twinTarget : RevTwinTarget R.sig R.twin₁ :=
  { toRevShape := R.shapeT, meta := TwinMeta.ofPreds R.t1Preds, rows := R.twin₁Rows }

/-! ## §2 THE Π ROW -/

section PiRow

variable {n : Nat}

/-- **THE Π ROW OF THE ENVIRONMENT OF ANY REVEALED SINGLETON.** A chain between two Π's of `E` is carried by `tr`
    into the twin, split there by the twin's Π row, and brought back by the identity transport; the ends are
    identified with the originals by the round trip `e ≡ tr e` (the K-like cell). The domain is collapsed in
    the twin at the left domain's sort, and the twin's sort uniqueness identifies the two domain sorts, which is
    what moves the right codomain under the left domain. -/
theorem revPiRow (n : Nat) : PiRowField R.E n := by
  intro Γ hΓ A B A' B' h
  by_cases heq : (Expr.pi A B : Expr Nat) = .pi A' B'
  · rcases Expr.pi.inj heq with ⟨rfl, rfl⟩
    exact ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩
  · obtain ⟨u, v, ⟨hA⟩, ⟨hB⟩⟩ := piCompsTyped R.hW hΓ h heq
    obtain ⟨u', v', ⟨hA'⟩, ⟨hB'⟩⟩ := piCompsTyped R.hW hΓ (TyConvT.symmT h) (Ne.symm heq)
    have hcl := envClosed_of_envWfT R.hW
    let W := R.twinTarget
    have hagree := R.twin₁_agree
    -- into the twin
    obtain ⟨hΓ'⟩ := trCtxWfW R W hagree hΓ
    obtain ⟨h'⟩ := trTyConvW R W hagree h hΓ'
    obtain ⟨⟨cA⟩, ⟨cB⟩⟩ := (R.twin₁Rows n).piRow hΓ' h'
    obtain ⟨htA⟩ := trTyW R W hagree hA hΓ'
    obtain ⟨htA'⟩ := trTyW R W hagree hA' hΓ'
    -- the domain, collapsed in the twin at `Sort u`; `u' =ₙ u` by the twin's sort uniqueness
    obtain ⟨dA⟩ := W.meta.collapse hΓ' htA cA
    have htA'u : HasTyT R.twin₁ n (trCtx R.f R.I Γ) (tr R.f R.I A') (.sort u) := (W.meta.ends hΓ' dA).2.1
    obtain ⟨cuu⟩ := W.meta.uniq hΓ' htA' htA'u
    have huu : eqN u' u := (R.twin₁Rows n).sortRow hΓ' cuu
    -- back to `E`
    obtain ⟨hcc⟩ := R.ctxConv_tr hΓ
    obtain ⟨hΓb⟩ := R.bkCtxWf hΓ'
    obtain ⟨dA'⟩ := R.bkConv dA hΓb
    have dA'' : ConvT R.E n Γ (tr R.f R.I A) (tr R.f R.I A') (.sort u) := convT_ctx hcl hcc dA'
    obtain ⟨eA⟩ := R.trConv_self hA
    obtain ⟨eA'⟩ := R.trConv_self hA'
    have eA'u : ConvT R.E n Γ A' (tr R.f R.I A') (.sort u) :=
      .tyConv _ _ _ _ _ (.succ u') eA' (.sorts _ u' u huu)
    have hA'u : HasTyT R.E n Γ A' (.sort u) := .conv _ _ _ _ (.succ u') hA' (.sorts _ u' u huu)
    have cAA' : ConvT R.E n Γ A A' (.sort u) :=
      .trans _ _ _ _ _ eA (.trans _ _ _ _ _ dA'' (.symm _ _ _ _ eA'u))
    refine ⟨⟨.of _ _ _ u cAA'⟩, ?_⟩
    -- the codomain: back under `tr A`, then under `A`; `B'` moved from `A' :: Γ` to `A :: Γ`
    have hΓ'A : CtxWfT R.twin₁ n (.assumption (tr R.f R.I A) :: trCtx R.f R.I Γ) :=
      .assumption _ (tr R.f R.I A) u hΓ' htA
    obtain ⟨hΓbA⟩ := R.bkCtxWf hΓ'A
    obtain ⟨cB'⟩ := R.bkTyConv cB hΓbA
    have hbA : HasTyT R.E n Γ (tr R.f R.I A) (.sort u) := (NativeValleys.convEnds R.hW hΓ eA).2.1
    have hccA : CtxConvT R.E n (.assumption (tr R.f R.I A) :: trCtx R.f R.I Γ) (.assumption A :: Γ) :=
      .assumption hcc hbA hA (.symm _ _ _ _ eA)
    have cB'' : TyConvT R.E n (.assumption A :: Γ) (tr R.f R.I B) (tr R.f R.I B') :=
      tyConvT_ctx₀ hcl hccA cB'
    have hccB : CtxConvT R.E n (.assumption A' :: Γ) (.assumption A :: Γ) :=
      .assumption (ctxConvT_refl Γ) hA'u hA (.symm _ _ _ _ cAA')
    have hB'A : HasTyT R.E n (.assumption A :: Γ) B' (.sort v') := hasTyT_ctx hcl hccB hB'
    obtain ⟨eB⟩ := R.trConv_self hB
    obtain ⟨eB'⟩ := R.trConv_self hB'A
    exact ⟨.trans _ _ _ _ (.of _ _ _ v eB)
      (.trans _ _ _ _ cB'' (.of _ _ _ v' (.symm _ _ _ _ eB')))⟩

/-- row 1 of `E`, read in the twin. -/
theorem revSortRow {Γ : LCtx} (hΓ : CtxWfT R.E n Γ) {u v : Level}
    (h : TyConvT R.E n Γ (.sort u) (.sort v)) : eqN u v := by
  obtain ⟨hΓ'⟩ := trCtxWfW R R.twinTarget R.twin₁_agree hΓ
  obtain ⟨c⟩ := trTyConvW R R.twinTarget R.twin₁_agree h hΓ'
  exact (R.twin₁Rows n).sortRow hΓ' c

end PiRow

end RevEnv

end Rcic.Syn.FamApp.Rev

#print axioms Rcic.Syn.FamApp.Rev.RevEnv.t1IotaLevels
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.twinTarget
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.revPiRow
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.revSortRow
