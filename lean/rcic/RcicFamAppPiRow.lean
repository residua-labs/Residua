import rcic.RcicFamAppCopyTwin
import rcic.RcicFamAppTwinMetaOfPreds
import rcic.RcicFamAppLiftBack
import rcic.RcicFamAppSortPiDisj
import rcic.RcicDT0709EnvWf
import rcic.RcicDT1011Rows
import rcic.RcicDTRowFields
import rcic.RcicIotaSRRowsLemmas

/-!
# RcicFamAppPiRow — the Π row of `riEnv` (class B), hence all three rows, unconditionally

`riEnv` is the class-B fixture (`RI : Sort 0 → Sort 0`, `mk : Π X, RI X`, AnySort recursor): it is in no
landed scope (`riPolicy_anySort`), and its family row was reduced to its Π row (`riTypedRowsWf_iff_piRow`,
`RcicFamAppLiftBack`; `riTypedRowsWf_of_piRow'`, `RcicFamAppSortPiDisj`). This module closes the Π row.

**Route.** `RcicFamAppCopyTwin` admits the twin `gEnv₀ = { RI₀ (inductive, NO constructors) @0 ; mk₀ (axiom,
`mk`'s type) @2 }` in the copy — no recursor, so no profile — and reads its three rows off the landed
supplier (`g0Rows`). `gEnv₀` is not an `EnvWfT`, so the six metatheory facts the translation consumes
(`TwinMeta`) are supplied here from the predicate-level cores (`regularT`, `endpoints3`, `convT_subst0S`,
`convT_substLetS`, `convT_of_tyConvT_sortN`, and the `DT012T_type_uniqueness_of_sortRow_piRow` /
`spineInvAux` proofs re-run at `gEnv₀`'s rows); its base predicates (`EnvClosed`, `EnvMembersSubstStable`,
`EnvMembersSortTypedT`, `EnvLevelsT`, `IotaLevelsT`, `SubstLetT`, `ConstsRightDataT`) are proved directly.
Then `g0Twin : TwinTarget gEnv₀`, and the landed generic translation `tr` (`mk ↦ mk₀`, `rec.{l} ↦ recT l`)
carries `riEnv`'s chains into `gEnv₀`. The way back (`bkTy₀`/`bkConv₀`) is `RcicFamAppLiftBack`'s `bk`
(`mk₀ ↦ mk`) on a twin that has NO ι (no recursor member — `IotaWitness gEnv₀` is empty) and NO δ: a
renaming, nothing is retyped. The round trip `e ≡ bk (tr e)` is the landed `trbkConv` (the K-like cell,
`recL_conv_rec`), and `ctxConv_bktr` moves the contexts.

**Results.** `riPiRow : PiRowField riEnv n` and `riTypedRowsWf : TypedRowsWf riEnv n` for every `n`,
axioms ⊆ {propext, Quot.sound}. `closure_claim = 0` for anything beyond the fixture.
-/

namespace Rcic.Syn.FamApp

open Rcic.Declarative
open Rcic.Syn
open Rcic.Syn.ClassC
open Rcic.Syn.FamApp.CopyTwin

/-! ## §1 the members of `gEnv₀`, read -/

theorem gEnv₀_class {r : Nat} {m : CheckedMember} (h : gEnv₀.members r = some m) :
    (r = 2 ∧ m = mkAx) ∨ (r = 0 ∧ m = riFam) := by
  rw [gEnv₀_members] at h
  by_cases h2 : r = 2
  · rw [if_pos h2] at h; exact Or.inl ⟨h2, (Option.some.inj h).symm⟩
  · rw [if_neg h2] at h
    by_cases h0 : r = 0
    · rw [if_pos h0] at h; exact Or.inr ⟨h0, (Option.some.inj h).symm⟩
    · rw [if_neg h0] at h; exact Option.noConfusion h

theorem gEnv₀_noRec {r : Nat} {m : CheckedMember} (h : gEnv₀.members r = some m) :
    m.mclass ≠ .recursorM := by
  rcases gEnv₀_class h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact fun h => MemberClass.noConfusion h

theorem gEnv₀_noBody {r : Nat} {m : CheckedMember} (h : gEnv₀.members r = some m) :
    m.body = none := by
  rcases gEnv₀_class h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- no ι in `gEnv₀`: every witness names a recursor member, and there is none. -/
theorem gEnv₀_noIota {lhs rhs : Expr Nat} (h : DerivedIota gEnv₀ lhs rhs) : False := by
  cases h with
  | of w => exact gEnv₀_noRec w.hrec w.hrecK

/-! ## §2 the base predicates of `gEnv₀` -/

theorem g0Closed : EnvClosed gEnv₀ := by
  intro r m hm
  rcases gEnv₀_class hm with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨fun _ => rfl, fun b hb => Option.noConfusion hb⟩
  · exact ⟨fun _ => rfl, fun b hb => Option.noConfusion hb⟩

theorem g0SubstStable : EnvMembersSubstStable gEnv₀ :=
  fun r m hm =>
    let ⟨hclT, hclB⟩ := g0Closed r m hm
    ⟨fun ls s k =>
        lift_id_instantiate (instantiateLevels ls m.mtype)
          (instantiateLevels_closed hclT ls 0) k (Nat.zero_le k) s,
     fun b hb ls s k =>
        lift_id_instantiate (instantiateLevels ls b)
          (instantiateLevels_closed (hclB b hb) ls 0) k (Nat.zero_le k) s⟩

theorem g0Levels : EnvLevelsT gEnv₀ := by
  intro r m hm
  rcases gEnv₀_class hm with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨rfl, fun b hb => Option.noConfusion hb⟩
  · exact ⟨rfl, fun b hb => Option.noConfusion hb⟩

/-- vacuous: a ι witness names a recursor member. -/
theorem g0IotaLevels : IotaLevelsT gEnv₀ :=
  ⟨fun w => absurd w.hrecK (gEnv₀_noRec w.hrec), fun w => absurd w.hrecK (gEnv₀_noRec w.hrec)⟩

/-- both member types are sort-typed in `gEnv₀` at arity `0`. -/
def g0SortTyped : EnvMembersSortTypedT gEnv₀ := fun r m hm => by
  rw [gEnv₀_members] at hm
  by_cases h2 : r = 2
  · rw [if_pos h2] at hm
    obtain rfl : mkAx = m := Option.some.inj hm
    exact ⟨.imax (.succ .zero) .zero,
      .pi [] (.sort .zero) (.succ .zero) (.app (.const 0 []) (.bvar 0)) .zero (.sort [] .zero)
        (.app _ (.const 0 []) (.bvar 0) (.sort .zero) (.sort .zero)
          (.const _ 0 [] riFam rfl rfl rfl) (.bvar _ 0 _ rfl))⟩
  · rw [if_neg h2] at hm
    by_cases h0 : r = 0
    · rw [if_pos h0] at hm
      obtain rfl : riFam = m := Option.some.inj hm
      exact ⟨.imax (.succ .zero) (.succ .zero),
        .pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero) (.sort [] .zero) (.sort _ .zero)⟩
    · rw [if_neg h0] at hm
      exact Option.noConfusion hm

/-! ## §3 the twin's metatheory, from the predicate-level cores (`TwinMeta.ofPreds`) -/

/-- **the twin's metatheory**, without an `EnvWfT` derivation: the six facts assembled generically
    (`TwinMeta.ofPreds`, `RcicFamAppTwinMetaOfPreds`) from `gEnv₀`'s base predicates and its rows. The
    `DT012T_type_uniqueness_of_sortRow_piRow` and `spineInvAux` proofs that session 4 inlined here now live
    once, in that module, shared with the generic revealed-singleton twin. -/
def g0Meta : TwinMeta gEnv₀ :=
  TwinMeta.ofPreds ⟨g0Closed, g0SubstStable, g0SortTyped, g0Levels, g0IotaLevels, g0Rows⟩

/-- **the copy-only twin is a target of `tr`.** -/
def g0Twin : TwinTarget gEnv₀ where
  meta := g0Meta
  rows := g0Rows
  h0 := rfl
  m₂ := mkAx
  h2 := rfl
  h2t := rfl
  h2a := rfl

/-! ## §4 the way back, `gEnv₀ → riEnv`: a renaming (`bk`: `mk₀ ↦ mk`), no ι, no δ -/

section Back

variable {n : Nat}

mutual
theorem bkTy₀ : {Γ : LCtx} → {e A : Expr Nat} → HasTyT gEnv₀ n Γ e A →
    CtxWfT riEnv n (bkCtx Γ) → Nonempty (HasTyT riEnv n (bkCtx Γ) (bk e) (bk A))
  | _, _, _, .sort Γ l, _ => ⟨.sort _ l⟩
  | _, _, _, .bvar Γ i A h, _ =>
      ⟨.bvar _ i (bk A) (by rw [lookupType_bkCtx, h]; rfl)⟩
  | _, _, _, .const Γ r ls m hres hlen hwf, _ => by
      rcases gEnv₀_class hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.const _ 1 ls riCtor rfl hlen hwf⟩
      · exact ⟨.const _ 0 ls riFam rfl hlen hwf⟩
  | _, _, _, .pi Γ A u B v hA hB, hΓ' => by
      obtain ⟨hA'⟩ := bkTy₀ hA hΓ'
      obtain ⟨hB'⟩ := bkTy₀ hB (.assumption _ (bk A) u hΓ' hA')
      exact ⟨.pi _ (bk A) u (bk B) v hA' hB'⟩
  | _, _, _, .lam Γ A u body B hA hbody, hΓ' => by
      obtain ⟨hA'⟩ := bkTy₀ hA hΓ'
      obtain ⟨hb'⟩ := bkTy₀ hbody (.assumption _ (bk A) u hΓ' hA')
      exact ⟨.lam _ (bk A) u (bk body) (bk B) hA' hb'⟩
  | _, _, _, .app Γ f a A B hf ha, hΓ' => by
      obtain ⟨hf'⟩ := bkTy₀ hf hΓ'
      obtain ⟨ha'⟩ := bkTy₀ ha hΓ'
      rw [bk_instantiate0]
      exact ⟨.app _ (bk f) (bk a) (bk A) (bk B) hf' ha'⟩
  | _, _, _, .letE Γ A u value B body hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := bkTy₀ hA hΓ'
      obtain ⟨hv'⟩ := bkTy₀ hv hΓ'
      obtain ⟨hb'⟩ := bkTy₀ hb (.letBinding _ (bk A) u (bk value) hΓ' hA' hv')
      rw [bk_instantiate0]
      exact ⟨.letE _ (bk A) u (bk value) (bk B) (bk body) hA' hv' hb'⟩
  | _, _, _, .lit Γ t T hexp, hΓ' => by
      obtain ⟨h⟩ := bkTy₀ hexp hΓ'
      rw [bk_natExpand] at h
      exact ⟨h⟩
  | _, _, _, .conv Γ e A B u h hc, hΓ' => by
      obtain ⟨h'⟩ := bkTy₀ h hΓ'
      obtain ⟨hc'⟩ := bkConv₀ hc hΓ'
      exact ⟨.conv _ (bk e) (bk A) (bk B) u h' hc'⟩

theorem bkConv₀ : {Γ : LCtx} → {a b A : Expr Nat} → ConvT gEnv₀ n Γ a b A →
    CtxWfT riEnv n (bkCtx Γ) → Nonempty (ConvT riEnv n (bkCtx Γ) (bk a) (bk b) (bk A))
  | _, _, _, _, .refl Γ a A h, hΓ' => by
      obtain ⟨h'⟩ := bkTy₀ h hΓ'
      exact ⟨.refl _ _ _ h'⟩
  | _, _, _, _, .symm Γ a b A h, hΓ' => by
      obtain ⟨h'⟩ := bkConv₀ h hΓ'
      exact ⟨.symm _ _ _ _ h'⟩
  | _, _, _, _, .trans Γ a b c A h1 h2, hΓ' => by
      obtain ⟨h1'⟩ := bkConv₀ h1 hΓ'
      obtain ⟨h2'⟩ := bkConv₀ h2 hΓ'
      exact ⟨.trans _ _ _ _ _ h1' h2'⟩
  | _, _, _, _, .beta Γ A body arg B u hA hbody harg, hΓ' => by
      obtain ⟨hA'⟩ := bkTy₀ hA hΓ'
      obtain ⟨hb'⟩ := bkTy₀ hbody (.assumption _ (bk A) u hΓ' hA')
      obtain ⟨ha'⟩ := bkTy₀ harg hΓ'
      rw [bk_instantiate0, bk_instantiate0]
      exact ⟨.beta _ (bk A) (bk body) (bk arg) (bk B) u hA' hb' ha'⟩
  | _, _, _, _, .zeta Γ A value body B u hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := bkTy₀ hA hΓ'
      obtain ⟨hv'⟩ := bkTy₀ hv hΓ'
      obtain ⟨hb'⟩ := bkTy₀ hb (.letBinding _ (bk A) u (bk value) hΓ' hA' hv')
      rw [bk_instantiate0, bk_instantiate0]
      exact ⟨.zeta _ (bk A) (bk value) (bk body) (bk B) u hA' hv' hb'⟩
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv, hΓ' => by
      obtain ⟨hv'⟩ := bkTy₀ hv hΓ'
      exact ⟨.zetaLocal _ i (bk A) (bk v) (by rw [lookupValue_bkCtx, hval]; rfl)
        (by rw [lookupType_bkCtx, hty]; rfl) hv'⟩
  | _, _, _, _, .delta Γ r ls m b hres hbody _ _ _ _, _ =>
      absurd hbody (by rw [gEnv₀_noBody hres]; exact Option.noConfusion)
  | _, _, _, _, .iota Γ lhs rhs T h hl hr, _ => (gEnv₀_noIota h).elim
  | _, _, _, _, .lit Γ t exp T h hexp, hΓ' => by
      obtain ⟨h'⟩ := bkTy₀ hexp hΓ'
      rw [litExp_eq h, bk_natExpand] at *
      exact ⟨.refl _ _ _ h'⟩
  | _, _, _, _, .app Γ f g a b A B h1 h2, hΓ' => by
      obtain ⟨h1'⟩ := bkConv₀ h1 hΓ'
      obtain ⟨h2'⟩ := bkConv₀ h2 hΓ'
      rw [bk_instantiate0]
      exact ⟨.app _ (bk f) (bk g) (bk a) (bk b) (bk A) (bk B) h1' h2'⟩
  | _, _, _, _, .lam Γ A A' b b' B u hA hb, hΓ' => by
      obtain ⟨hA'⟩ := bkConv₀ hA hΓ'
      obtain ⟨hb'⟩ := bkConv₀ hb (.assumption _ (bk A) u hΓ'
        (NativeValleys.convEnds riEnvWfT hΓ' hA').1)
      exact ⟨.lam _ (bk A) (bk A') (bk b) (bk b') (bk B) u hA' hb'⟩
  | _, _, _, _, .pi Γ A A' B B' u v hA hB, hΓ' => by
      obtain ⟨hA'⟩ := bkConv₀ hA hΓ'
      obtain ⟨hB'⟩ := bkConv₀ hB (.assumption _ (bk A) u hΓ'
        (NativeValleys.convEnds riEnvWfT hΓ' hA').1)
      exact ⟨.pi _ (bk A) (bk A') (bk B) (bk B') u v hA' hB'⟩
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb, hΓ' => by
      obtain ⟨hA'⟩ := bkConv₀ hA hΓ'
      obtain ⟨hv'⟩ := bkConv₀ hv hΓ'
      obtain ⟨hb'⟩ := bkConv₀ hb (.letBinding _ (bk A) u (bk v) hΓ'
        (NativeValleys.convEnds riEnvWfT hΓ' hA').1 (NativeValleys.convEnds riEnvWfT hΓ' hv').1)
      rw [bk_instantiate0]
      exact ⟨.letE _ (bk A) (bk A') (bk v) (bk v') (bk b) (bk b') (bk B) u hA' hv' hb'⟩
  | _, _, _, _, .sorts Γ l₁ l₂ h, _ => ⟨.sorts _ l₁ l₂ h⟩
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h, _ => by
      rcases gEnv₀_class hres with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.consts _ 1 ls ls' riCtor rfl hlen hwf hwf' h⟩
      · exact ⟨.consts _ 0 ls ls' riFam rfl hlen hwf hwf' h⟩
  | _, _, _, _, .eta Γ f A B h, hΓ' => by
      obtain ⟨h'⟩ := bkTy₀ h hΓ'
      show Nonempty (ConvT riEnv n (bkCtx Γ) (.lam (bk A) (.app (bk (lift 0 1 f)) (.bvar 0))) (bk f)
        (.pi (bk A) (bk B)))
      rw [bk_lift]
      exact ⟨.eta _ (bk f) (bk A) (bk B) h'⟩
  | _, _, _, _, .irr Γ P p q hP hp hq, hΓ' => by
      obtain ⟨hP'⟩ := bkTy₀ hP hΓ'
      obtain ⟨hp'⟩ := bkTy₀ hp hΓ'
      obtain ⟨hq'⟩ := bkTy₀ hq hΓ'
      exact ⟨.irr _ (bk P) (bk p) (bk q) hP' hp' hq'⟩
  | _, _, _, _, .tyConv Γ a b A A' u h hA, hΓ' => by
      obtain ⟨h'⟩ := bkConv₀ h hΓ'
      obtain ⟨hA'⟩ := bkConv₀ hA hΓ'
      exact ⟨.tyConv _ (bk a) (bk b) (bk A) (bk A') u h' hA'⟩
end

theorem bkTyConv₀ {Γ : LCtx} {a b : Expr Nat} (h : TyConvT gEnv₀ n Γ a b)
    (hΓ' : CtxWfT riEnv n (bkCtx Γ)) : Nonempty (TyConvT riEnv n (bkCtx Γ) (bk a) (bk b)) := by
  induction h with
  | refl A => exact ⟨.refl _ _⟩
  | of A B u h => obtain ⟨c⟩ := bkConv₀ h hΓ'; exact ⟨.of _ _ _ u c⟩
  | trans A B C h1 h2 ih1 ih2 =>
      obtain ⟨c1⟩ := ih1
      obtain ⟨c2⟩ := ih2
      exact ⟨.trans _ _ _ _ c1 c2⟩

theorem bkCtxWf₀ {Γ : LCtx} (h : CtxWfT gEnv₀ n Γ) : Nonempty (CtxWfT riEnv n (bkCtx Γ)) := by
  induction h with
  | nil => exact ⟨.nil⟩
  | assumption Γ A u hΓ hA ih =>
      obtain ⟨hΓ'⟩ := ih
      obtain ⟨hA'⟩ := bkTy₀ hA hΓ'
      exact ⟨.assumption _ (bk A) u hΓ' hA'⟩
  | letBinding Γ A u v hΓ hA hv ih =>
      obtain ⟨hΓ'⟩ := ih
      obtain ⟨hA'⟩ := bkTy₀ hA hΓ'
      obtain ⟨hv'⟩ := bkTy₀ hv hΓ'
      exact ⟨.letBinding _ (bk A) u (bk v) hΓ' hA' hv'⟩

end Back

/-! ## §5 THE Π ROW OF `riEnv`, and its three rows -/

section PiRow

variable {n : Nat}

/-! `tyConvT_ctx₀` and `piCompsTyped` (over any `EnvWfT`) live in `RcicFamAppTwinMetaOfPreds`, shared with the
generic revealed-singleton Π row. -/

/-- **THE Π ROW OF `riEnv`.** A chain between two Π's of `riEnv` is carried by `tr` into the copy-only
    twin `gEnv₀`, split there by the twin's Π row, and brought back by the renaming `bk`; the ends are
    identified with the originals by the round trip `e ≡ bk (tr e)` (`trbkConv`: the K-like cell). The
    domain is collapsed in the twin at the left domain's sort, and the twin's sort uniqueness identifies
    the two domain sorts, which is what moves the right codomain under the left domain. -/
theorem riPiRow (n : Nat) : PiRowField riEnv n := by
  intro Γ hΓ A B A' B' h
  by_cases heq : (Expr.pi A B : Expr Nat) = .pi A' B'
  · rcases Expr.pi.inj heq with ⟨rfl, rfl⟩
    exact ⟨⟨.refl _ _⟩, ⟨.refl _ _⟩⟩
  · obtain ⟨u, v, ⟨hA⟩, ⟨hB⟩⟩ := piCompsTyped riEnvWfT hΓ h heq
    obtain ⟨u', v', ⟨hA'⟩, ⟨hB'⟩⟩ := piCompsTyped riEnvWfT hΓ (TyConvT.symmT h) (Ne.symm heq)
    have hcl := envClosed_of_envWfT riEnvWfT
    -- into the twin
    obtain ⟨hΓ'⟩ := g0Twin.trCtxWfW hΓ
    obtain ⟨h'⟩ := g0Twin.trTyConvW h hΓ'
    obtain ⟨⟨cA⟩, ⟨cB⟩⟩ := (g0Rows n).piRow hΓ' h'
    obtain ⟨htA⟩ := g0Twin.trTyW hA hΓ'
    obtain ⟨htA'⟩ := g0Twin.trTyW hA' hΓ'
    -- the domain, collapsed in the twin at `Sort u`; `u' =ₙ u` by the twin's sort uniqueness
    obtain ⟨dA⟩ := g0Meta.collapse hΓ' htA cA
    have htA'u : HasTyT gEnv₀ n (trCtx Γ) (tr A') (.sort u) := (g0Meta.ends hΓ' dA).2.1
    obtain ⟨cuu⟩ := g0Meta.uniq hΓ' htA' htA'u
    have huu : eqN u' u := (g0Rows n).sortRow hΓ' cuu
    -- back to `riEnv`
    obtain ⟨hcc⟩ := ctxConv_bktr hΓ
    obtain ⟨hΓb⟩ := bkCtxWf₀ hΓ'
    obtain ⟨dA'⟩ := bkConv₀ dA hΓb
    have dA'' : ConvT riEnv n Γ (bk (tr A)) (bk (tr A')) (.sort u) := convT_ctx hcl hcc dA'
    obtain ⟨eA⟩ := trbkConv hA
    obtain ⟨eA'⟩ := trbkConv hA'
    have eA'u : ConvT riEnv n Γ A' (bk (tr A')) (.sort u) :=
      .tyConv _ _ _ _ _ (.succ u') eA' (.sorts _ u' u huu)
    have hA'u : HasTyT riEnv n Γ A' (.sort u) := .conv _ _ _ _ (.succ u') hA' (.sorts _ u' u huu)
    have cAA' : ConvT riEnv n Γ A A' (.sort u) :=
      .trans _ _ _ _ _ eA (.trans _ _ _ _ _ dA'' (.symm _ _ _ _ eA'u))
    refine ⟨⟨.of _ _ _ u cAA'⟩, ?_⟩
    -- the codomain: back under `bk (tr A)`, then under `A`; `B'` moved from `A' :: Γ` to `A :: Γ`
    have hΓ'A : CtxWfT gEnv₀ n (.assumption (tr A) :: trCtx Γ) := .assumption _ (tr A) u hΓ' htA
    obtain ⟨hΓbA⟩ := bkCtxWf₀ hΓ'A
    obtain ⟨cB'⟩ := bkTyConv₀ cB hΓbA
    have hbA : HasTyT riEnv n Γ (bk (tr A)) (.sort u) := (NativeValleys.convEnds riEnvWfT hΓ eA).2.1
    have hccA : CtxConvT riEnv n (.assumption (bk (tr A)) :: bkCtx (trCtx Γ)) (.assumption A :: Γ) :=
      .assumption hcc hbA hA (.symm _ _ _ _ eA)
    have cB'' : TyConvT riEnv n (.assumption A :: Γ) (bk (tr B)) (bk (tr B')) :=
      tyConvT_ctx₀ hcl hccA cB'
    have hccB : CtxConvT riEnv n (.assumption A' :: Γ) (.assumption A :: Γ) :=
      .assumption (ctxConvT_refl Γ) hA'u hA (.symm _ _ _ _ cAA')
    have hB'A : HasTyT riEnv n (.assumption A :: Γ) B' (.sort v') := hasTyT_ctx hcl hccB hB'
    obtain ⟨eB⟩ := trbkConv hB
    obtain ⟨eB'⟩ := trbkConv hB'A
    exact ⟨.trans _ _ _ _ (.of _ _ _ v eB)
      (.trans _ _ _ _ cB'' (.of _ _ _ v' (.symm _ _ _ _ eB')))⟩

/-- **THE THREE ROWS OF `riEnv`**, from its Π row (the landed reduction of `RcicFamAppLiftBack`). -/
theorem riTypedRowsWf (n : Nat) : TypedRowsWf riEnv n := riTypedRowsWf_of_piRow (riPiRow n)

/-- the same, through the second landed reduction (`RcicFamAppSortPiDisj`, cc-classc's
    `typedRowsWf_ri_of_rows12`): two bases agree. -/
theorem riTypedRowsWf' (n : Nat) : TypedRowsWf riEnv n := riTypedRowsWf_of_piRow' (riPiRow n)

end PiRow

end Rcic.Syn.FamApp

#print axioms Rcic.Syn.FamApp.g0Twin
#print axioms Rcic.Syn.FamApp.bkConv₀
#print axioms Rcic.Syn.FamApp.riPiRow
#print axioms Rcic.Syn.FamApp.riTypedRowsWf
#print axioms Rcic.Syn.FamApp.riTypedRowsWf'
