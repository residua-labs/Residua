import rcic.RcicStarStripUnitObstruction
import rcic.RcicTypedWeaken
import rcic.RcicEtaKHeadInvariant

set_option autoImplicit false
set_option maxRecDepth 16384

/-!
# A shorter partial recursor obstructs the full native relation

This is an admitted negative client of the concrete True environment's
finite sorting supplier.  It does not participate in construction of
Pi rows or native confluence.  The original reduction and old Certified
judgment are unchanged.  The invariants range over every raw ParRedT
constructor, including both K constructors, and every finite raw star.
The right invariant records a positive sorting of its outer domain, so
arbitrary domain conversions cannot turn its bound minor into a proof.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.NativeKPartialObstructionAudit

open StarStripUnitPeakAudit
open StarStripUnitObstructionAudit (RecSpine)

private abbrev two : Level := .succ (.succ .zero)

private theorem unitSortUnique : F8A2Support.SortUnique trueEnvU 0 :=
  sortUnique_of_inScope trueEnvUWfT trueEnvUWfT_inScope 0

/- The old fragment's corresponding proofhood and ordinary-iota facts are
private.  These local copies support induction on the unrestricted relation. -/
private theorem rec2_notProof {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ)
    (ls : List Level) (hls : eqNList [two] ls) :
    NotProof trueEnvU 0 Γ (.const 2 ls) := by
  cases ls with
  | nil => exact False.elim hls
  | cons u rest =>
      cases rest with
      | cons v vs => exact False.elim hls.2
      | nil =>
          intro P hp hP
          obtain ⟨m, hm, _, _, c⟩ := hasTyTInv_const hp rfl
          change some trueRecMemberU = some m at hm
          have hm' : m = trueRecMemberU := (Option.some.inj hm).symm
          subst m
          obtain ⟨h0⟩ := F8A2Support.sort_transport unitSortUnique trueEnvUWfT hΓ c.symmT hP
          obtain ⟨u0, ⟨a0⟩, ⟨h1⟩⟩ := F8A2Support.pi_zero_inv unitSortUnique trueEnvUWfT hΓ h0
          have g1 := CtxWfT.assumption Γ _ u0 hΓ a0
          obtain ⟨u1, ⟨a1⟩, ⟨h2⟩⟩ := F8A2Support.pi_zero_inv unitSortUnique trueEnvUWfT g1 h1
          have g2 := CtxWfT.assumption _ _ u1 g1 a1
          obtain ⟨u2, ⟨a2⟩, ⟨h3⟩⟩ := F8A2Support.pi_zero_inv unitSortUnique trueEnvUWfT g2 h2
          have g3 := CtxWfT.assumption _ _ u2 g2 a2
          let Δ : LCtx :=
            [.assumption (.const 0 []),
             .assumption (.app (.bvar 0) (.const 1 [])),
             .assumption (.pi (.const 0 []) (.sort u))] ++ Γ
          have gΔ : CtxWfT trueEnvU 0 Δ := g3
          have hBody0 : HasTyT trueEnvU 0 Δ
              (.app (.bvar 2) (.bvar 0)) (.sort .zero) := h3
          have hM : HasTyT trueEnvU 0 Δ (.bvar 2)
              (.pi (.const 0 []) (.sort u)) := .bvar Δ 2 _ rfl
          have ht : HasTyT trueEnvU 0 Δ (.bvar 0) (.const 0 []) := .bvar Δ 0 _ rfl
          have hBodyU : HasTyT trueEnvU 0 Δ
              (.app (.bvar 2) (.bvar 0)) (.sort u) := .app _ _ _ _ _ hM ht
          have h0u := unitSortUnique trueEnvUWfT gΔ hBody0 hBodyU
          have bad : eqN two .zero := fun ρ => (hls.1 ρ).trans (h0u ρ).symm
          have impossible := bad (fun _ => none)
          simp [two, eval] at impossible

private theorem recSpine_notProof {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ)
    {k : Nat} {e : Expr Nat} (hs : RecSpine k e) : NotProof trueEnvU 0 Γ e := by
  obtain ⟨ls, hh, hu, _⟩ := hs
  intro P hp hP
  have he : e = foldApps (.const 2 ls) (appsSpine e).2 := by
    rw [← hh]
    exact (foldApps_appsSpine e).symm
  have hpr : F8A2Support.IsProof trueEnvU 0 Γ
      (foldApps (.const 2 ls) (appsSpine e).2) := ⟨P, ⟨hP⟩, ⟨he ▸ hp⟩⟩
  obtain ⟨Q, ⟨hQ⟩, ⟨hq⟩⟩ := F8A2Support.proof_foldApps_head
    unitSortUnique trueEnvUWfT hΓ (appsSpine e).2 hpr
  exact rec2_notProof hΓ ls hu hq hQ

/-- Both ordinary iota formats require all three arguments of the actual
resolved recursor member.  A proper prefix cannot fire either format. -/
private theorem recSpine_no_iota {k : Nat} {e rhs : Expr Nat}
    (hk : k < 3) (hs : RecSpine k e) (hI : DerivedIotaU trueEnvU e rhs) : False := by
  obtain ⟨ls, hh, _, hlen⟩ := hs
  cases hI with
  | ofU w =>
      simp only [iotaLhsOf, recCall, appsSpine_foldApps_const] at hh hlen
      have hr : w.recRef = 2 := (Expr.const.inj hh).1
      have hm := w.hrec
      rw [hr] at hm
      change some trueRecMemberU = some w.recMember at hm
      have he : w.recMember = trueRecMemberU := (Option.some.inj hm).symm
      have hn := w.hnmin
      rw [he] at hn
      change w.nparams + 1 + w.nMinors + w.nindices + 1 = 3 at hn
      have hp := w.hpre
      simp only [List.length_append, List.length_singleton] at hlen
      omega

  | ofUS w =>
      simp only [iotaLhsOfS, recCall, appsSpine_foldApps_const] at hh hlen
      have hr : w.recRef = 2 := (Expr.const.inj hh).1
      have hm := w.hrec
      rw [hr] at hm
      change some trueRecMemberU = some w.recMember at hm
      have he : w.recMember = trueRecMemberU := (Option.some.inj hm).symm
      have hn := w.hnmin
      rw [he] at hn
      change w.nparams + 1 + w.nMinors + w.nindices + 1 = 3 at hn
      have hp := w.hpre
      simp only [List.length_append, List.length_singleton] at hlen
      omega

/-- Every legacy witness of the actual True recursor has three arguments. -/
private theorem rec2_witness_arity (w : IotaWitness trueEnvU) (href : w.recRef = 2) :
    w.preMajor.length + 1 = 3 := by
  have hm := w.hrec
  rw [href] at hm
  change some trueRecMemberU = some w.recMember at hm
  have he : w.recMember = trueRecMemberU := (Option.some.inj hm).symm
  have hn := w.hnmin
  rw [he] at hn
  change w.nparams + 1 + w.nMinors + w.nindices + 1 = 3 at hn
  rw [w.hpre]
  exact hn

/-- All raw steps preserve prefixes shorter than the eta-K source arity.
The induction follows only original function, preparation and conversion
children; arbitrary argument reductions, including K reductions, remain allowed. -/
theorem recSpine_step {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ) :
    {x j T : Expr Nat} →
    ParRedT (ProofLeaf trueEnvU 0) trueEnvU 0 Γ x j T →
    (k : Nat) → k < 2 → RecSpine k x → RecSpine k j
  | _, _, _, .refl .., _, _, hs => hs
  | _, _, _, .conv _ _ _ _ _ p _, k, hk, hs => recSpine_step hΓ p k hk hs
  | _, _, _, .peq _ _ _ _ h, _, _, hs =>
      (recSpine_notProof hΓ hs h.hp h.hT).elim
  | _, _, _, .consts _ r ls ls' _ hu _ _, _, _, hs => by
      obtain ⟨us, hh, h1, hlen⟩ := hs
      have hh' : r = 2 ∧ ls = us := Expr.const.inj hh
      obtain ⟨rfl, rfl⟩ := hh'
      exact ⟨ls', rfl, F8A2Support.eqNList_trans_local h1 hu, hlen⟩
  | _, _, _, .delta _ r _ m _ _ hr _ htr _ _ _ _, _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      have he : r = 2 := (Expr.const.inj hh).1
      rw [he] at hr
      change some trueRecMemberU = some m at hr
      have hm : m = trueRecMemberU := (Option.some.inj hr).symm
      rw [hm] at htr
      exact nomatch htr
  | _, _, _, .app _ f _ _ _ _ _ _ _ _ pf _ _ _ _ _, k, hk, hs => by
      obtain ⟨ls, hh, hu, hlen⟩ := hs
      have hn : (appsSpine f).2.length + 1 = k := by
        simpa only [appsSpine, List.length_append, List.length_singleton] using hlen
      have hsmall : (appsSpine f).2.length < 2 := by omega
      have hf : RecSpine (appsSpine f).2.length f := ⟨ls, hh, hu, rfl⟩
      obtain ⟨ls', hh', hu', hlen'⟩ := recSpine_step hΓ pf _ hsmall hf
      refine ⟨ls', hh', hu', ?_⟩
      simpa only [appsSpine, List.length_append, List.length_singleton, hlen'] using hn
  | _, _, _, .iotaSpine _ _ _ _ _ prep hI _ _, k, hk, hs =>
      (recSpine_no_iota (by omega) (recSpine_step hΓ prep k hk hs) hI).elim
  | _, _, _, .iotaStarK _ w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, k, hk, hs => by
      obtain ⟨_, hh, _, hlen⟩ := hs
      simp only [recCall, appsSpine_foldApps_const] at hh hlen
      have href : w.recRef = 2 := (Expr.const.inj hh).1
      have hfull := rec2_witness_arity w href
      simp only [List.length_append, List.length_singleton] at hlen
      have hk3 : k = 3 := hlen.symm.trans hfull
      exact ((Nat.ne_of_lt (Nat.lt_trans hk (by decide : 2 < 3))) hk3).elim
  | _, _, _, .iotaStarKEta _ w _ _ _ _ _ _ _ _ happ _ _ _ _ _ _ _ _ _ _ _ _, k, hk, hs => by
      obtain ⟨_, hh, _, hlen⟩ := hs
      have hhd := iotaStarKEta_head happ
      have href : w.recRef = 2 := (Expr.const.inj (hhd.1.symm.trans hh)).1
      have hfull := rec2_witness_arity w href
      have hsource := hhd.2.2
      have hlen' : w.preMajor.length = k :=
        w.hpre.trans (hsource.symm.trans hlen)
      have hk3 : k + 1 = 3 := hlen' ▸ hfull
      have hk2 : k = 2 := Nat.add_right_cancel hk3
      exact ((Nat.ne_of_lt hk) hk2).elim
  | _, _, _, .beta .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, .sortEq .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, .bvarZeta .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, .lam .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, .pi .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, .letE .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, .zeta .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, .lit .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, .eta .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh

/-- Literal-tail induction, with no fragment or step-bound assumption. -/
theorem recSpine_star {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ) :
    {x j T : Expr Nat} →
    ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 Γ x j T →
    (k : Nat) → k < 2 → RecSpine k x → RecSpine k j
  | _, _, _, .refl .., _, _, hs => hs
  | _, _, _, .tail p ps, k, hk, hs =>
      recSpine_star hΓ ps k hk (recSpine_step hΓ p k hk hs)

/-- The existing raw proof comparison preserves this positive recursor
spine in both directions. Only its original application-function child
is recursive. This is an invariant, not a symmetry or transitivity law
for the raw comparison itself. -/
theorem recSpine_peqT_iff {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ) :
    {x j : Expr Nat} → PEqT trueEnvU 0 Γ x j →
    (k : Nat) → (RecSpine k x ↔ RecSpine k j)
  | _, _, .const _ r ls ls' hu, _ => by
      constructor
      · rintro ⟨us, hh, h1, hlen⟩
        have hh' : r = 2 ∧ ls = us := Expr.const.inj hh
        obtain ⟨rfl, rfl⟩ := hh'
        exact ⟨ls', rfl, F8A2Support.eqNList_trans_local h1 hu, hlen⟩
      · rintro ⟨us, hh, h1, hlen⟩
        have hh' : r = 2 ∧ ls' = us := Expr.const.inj hh
        obtain ⟨rfl, rfl⟩ := hh'
        exact ⟨ls, rfl, F8A2Support.eqNList_trans_local h1 (eqNList_symm hu), hlen⟩
  | _, _, .app _ f f' _ _ pf _, k => by
      constructor
      · rintro ⟨ls, hh, hu, hlen⟩
        have hn : (appsSpine f).2.length + 1 = k := by
          simpa only [appsSpine, List.length_append, List.length_singleton] using hlen
        have hf : RecSpine (appsSpine f).2.length f := ⟨ls, hh, hu, rfl⟩
        obtain ⟨ls', hh', hu', hlen'⟩ := (recSpine_peqT_iff hΓ pf _).1 hf
        refine ⟨ls', hh', hu', ?_⟩
        simpa only [appsSpine, List.length_append, List.length_singleton, hlen'] using hn
      · rintro ⟨ls, hh, hu, hlen⟩
        have hn : (appsSpine f').2.length + 1 = k := by
          simpa only [appsSpine, List.length_append, List.length_singleton] using hlen
        have hf : RecSpine (appsSpine f').2.length f' := ⟨ls, hh, hu, rfl⟩
        obtain ⟨ls', hh', hu', hlen'⟩ := (recSpine_peqT_iff hΓ pf _).2 hf
        refine ⟨ls', hh', hu', ?_⟩
        simpa only [appsSpine, List.length_append, List.length_singleton, hlen'] using hn
  | _, _, .proof _ _ _ _ _ hP hQ hp hq, _ =>
      ⟨fun hs => (recSpine_notProof hΓ hs hp hP).elim,
       fun hs => (recSpine_notProof hΓ hs hq hQ).elim⟩
  | _, _, .bvar .., _ => by
      constructor <;> rintro ⟨_, hh, _, _⟩ <;> exact nomatch hh
  | _, _, .sort .., _ => by
      constructor <;> rintro ⟨_, hh, _, _⟩ <;> exact nomatch hh
  | _, _, .lam .., _ => by
      constructor <;> rintro ⟨_, hh, _, _⟩ <;> exact nomatch hh
  | _, _, .pi .., _ => by
      constructor <;> rintro ⟨_, hh, _, _⟩ <;> exact nomatch hh
  | _, _, .letE .., _ => by
      constructor <;> rintro ⟨_, hh, _, _⟩ <;> exact nomatch hh
  | _, _, .lit .., _ => by
      constructor <;> rintro ⟨_, hh, _, _⟩ <;> exact nomatch hh

private theorem bvar1_notProof {Γ : LCtx} {A B : Expr Nat}
    (hΓAB : CtxWfT trueEnvU 0 (.assumption B :: .assumption A :: Γ))
    (hA : HasTyT trueEnvU 0 Γ A (.sort two)) :
    NotProof trueEnvU 0 (.assumption B :: .assumption A :: Γ) (.bvar 1) := by
  intro P hp hP
  obtain ⟨X, hlookup, c⟩ := hasTyTInv_bvar hp rfl
  change some (lift 0 2 A) = some X at hlookup
  have hX : X = lift 0 2 A := (Option.some.inj hlookup).symm
  subst X
  have h1 : HasTyT trueEnvU 0 (.assumption A :: Γ)
      (lift 0 1 A) (.sort two) :=
    hasTyTWeaken (.assumption A) (envClosed_of_envWfT trueEnvUWfT) (c := 0) hA
  have h2 : HasTyT trueEnvU 0 (.assumption B :: .assumption A :: Γ)
      (lift 0 1 (lift 0 1 A)) (.sort two) :=
    hasTyTWeaken (.assumption B) (envClosed_of_envWfT trueEnvUWfT) (c := 0) h1
  have h2' : HasTyT trueEnvU 0 (.assumption B :: .assumption A :: Γ)
      (lift 0 2 A) (.sort two) := by
    simpa only [lift_shift_comp_idx] using h2
  obtain ⟨h0⟩ := F8A2Support.sort_transport unitSortUnique trueEnvUWfT hΓAB c.symmT hP
  have bad := unitSortUnique trueEnvUWfT hΓAB h2' h0 (fun _ => none)
  simp [two, eval] at bad

private theorem lamBvar_notProof {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ)
    {A : Expr Nat} (hA : HasTyT trueEnvU 0 Γ A (.sort two)) (B : Expr Nat) :
    NotProof trueEnvU 0 (.assumption A :: Γ) (.lam B (.bvar 1)) := by
  intro P hp hP
  have gA : CtxWfT trueEnvU 0 (.assumption A :: Γ) :=
    .assumption Γ A two hΓ hA
  obtain ⟨v, C, hB, hb, c⟩ := hasTyTInv_lam hp rfl
  obtain ⟨hpi0⟩ := F8A2Support.sort_transport unitSortUnique trueEnvUWfT gA c.symmT hP
  obtain ⟨_, _, ⟨hC0⟩⟩ := F8A2Support.pi_zero_inv unitSortUnique trueEnvUWfT gA hpi0
  exact bvar1_notProof (.assumption _ B v gA hB) hA hb hC0

private theorem doubleLam_notProof {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ)
    {A : Expr Nat} (hA : HasTyT trueEnvU 0 Γ A (.sort two)) (B : Expr Nat) :
    NotProof trueEnvU 0 Γ (.lam A (.lam B (.bvar 1))) := by
  intro P hp hP
  obtain ⟨_, C, _, hb, c⟩ := hasTyTInv_lam hp rfl
  obtain ⟨hpi0⟩ := F8A2Support.sort_transport unitSortUnique trueEnvUWfT hΓ c.symmT hP
  obtain ⟨_, _, ⟨hC0⟩⟩ := F8A2Support.pi_zero_inv unitSortUnique trueEnvUWfT hΓ hpi0
  exact lamBvar_notProof hΓ hA B hb hC0

/-- The positive minor is an assumption and remains that exact variable,
through every original preparation and index-conversion child. -/
private theorem boundMinor_step {Γ : LCtx} {A B : Expr Nat}
    (hΓAB : CtxWfT trueEnvU 0 (.assumption B :: .assumption A :: Γ))
    (hA : HasTyT trueEnvU 0 Γ A (.sort two)) :
    {x j T : Expr Nat} →
    ParRedT (ProofLeaf trueEnvU 0) trueEnvU 0
      (.assumption B :: .assumption A :: Γ) x j T →
    x = .bvar 1 → j = .bvar 1
  | _, _, _, .refl .., hx => hx
  | _, _, _, .conv _ _ _ _ _ p _, hx => boundMinor_step hΓAB hA p hx
  | _, _, _, .peq _ _ _ _ h, hx => by
      subst hx
      exact (bvar1_notProof hΓAB hA h.hp h.hT).elim
  | _, _, _, .bvarZeta _ _ _ _ _ _ hget _ _ _, hx => by
      injection hx with hi
      subst hi
      change some (LocalDecl.assumption A) = some (LocalDecl.letBinding _ _) at hget
      exact nomatch hget
  | _, _, _, .iotaSpine _ _ _ _ _ prep hI _ _, hx => by
      have he := boundMinor_step hΓAB hA prep hx
      exact (F8EtaK.derivedIotaU_bvar_source_false hI he).elim
  | _, _, _, .iotaStarK .., hx => by
      simp only [recCall, foldApps_snoc] at hx
      exact nomatch hx
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., hx => by
      have hhd := (iotaStarKEta_head happ).1
      rw [hx] at hhd
      exact nomatch hhd
  | _, _, _, .sortEq .., hx => nomatch hx
  | _, _, _, .consts .., hx => nomatch hx
  | _, _, _, .delta .., hx => nomatch hx
  | _, _, _, .app .., hx => nomatch hx
  | _, _, _, .beta .., hx => nomatch hx
  | _, _, _, .lam .., hx => nomatch hx
  | _, _, _, .pi .., hx => nomatch hx
  | _, _, _, .letE .., hx => nomatch hx
  | _, _, _, .zeta .., hx => nomatch hx
  | _, _, _, .lit .., hx => nomatch hx
  | _, _, _, .eta .., hx => nomatch hx

private theorem lamBvar_step {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ)
    {A : Expr Nat} (hA : HasTyT trueEnvU 0 Γ A (.sort two)) :
    {x j T : Expr Nat} →
    ParRedT (ProofLeaf trueEnvU 0) trueEnvU 0 (.assumption A :: Γ) x j T →
    (B : Expr Nat) → x = .lam B (.bvar 1) →
    ∃ B' : Expr Nat, j = .lam B' (.bvar 1)
  | _, _, _, .refl .., B, hx => ⟨B, hx⟩
  | _, _, _, .conv _ _ _ _ _ p _, B, hx => lamBvar_step hΓ hA p B hx
  | _, _, _, .peq _ _ _ _ h, B, hx => by
      subst hx
      exact (lamBvar_notProof hΓ hA B h.hp h.hT).elim
  | _, _, _, .lam _ B₀ B' _ _ _ v _ _ hB _ pb _, B, hx => by
      injection hx with _ hbody
      have gA : CtxWfT trueEnvU 0 (.assumption A :: Γ) :=
        .assumption Γ A two hΓ hA
      have he := boundMinor_step (.assumption _ B₀ v gA hB) hA pb hbody
      exact ⟨B', congrArg (Expr.lam B') he⟩
  | _, _, _, .iotaSpine _ _ _ _ _ prep hI _ _, B, hx => by
      obtain ⟨B', he⟩ := lamBvar_step hΓ hA prep B hx
      exact (F8EtaK.derivedIotaU_lam_source_false hI he).elim
  | _, _, _, .iotaStarK .., _, hx => by
      simp only [recCall, foldApps_snoc] at hx
      exact nomatch hx
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., _, hx => by
      have hhd := (iotaStarKEta_head happ).1
      rw [hx] at hhd
      exact nomatch hhd
  | _, _, _, .eta .., _, hx => by
      injection hx with _ hb
      exact nomatch hb
  | _, _, _, .sortEq .., _, hx => nomatch hx
  | _, _, _, .consts .., _, hx => nomatch hx
  | _, _, _, .bvarZeta .., _, hx => nomatch hx
  | _, _, _, .delta .., _, hx => nomatch hx
  | _, _, _, .app .., _, hx => nomatch hx
  | _, _, _, .beta .., _, hx => nomatch hx
  | _, _, _, .pi .., _, hx => nomatch hx
  | _, _, _, .letE .., _, hx => nomatch hx
  | _, _, _, .zeta .., _, hx => nomatch hx
  | _, _, _, .lit .., _, hx => nomatch hx

/-- Both lambda domains may drift. The outer domain's actual sorting
travels along its original domain conversion, and prevents proof leaves
at the roots or at the bound minor. -/
theorem doubleLam_step {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ) :
    {x j T : Expr Nat} →
    ParRedT (ProofLeaf trueEnvU 0) trueEnvU 0 Γ x j T →
    (A B : Expr Nat) → HasTyT trueEnvU 0 Γ A (.sort two) →
    x = .lam A (.lam B (.bvar 1)) →
    ∃ A' B' : Expr Nat, j = .lam A' (.lam B' (.bvar 1)) ∧
      Nonempty (HasTyT trueEnvU 0 Γ A' (.sort two))
  | _, _, _, .refl .., A, B, hA, hx => ⟨A, B, hx, ⟨hA⟩⟩
  | _, _, _, .conv _ _ _ _ _ p _, A, B, hA, hx => doubleLam_step hΓ p A B hA hx
  | _, _, _, .peq _ _ _ _ h, _, B, hA, hx => by
      subst hx
      exact (doubleLam_notProof hΓ hA B h.hp h.hT).elim
  | _, _, _, .lam _ A₀ A' _ _ _ _ _ hc _ _ pb _, A, B, hA, hx => by
      injection hx with hAA hbody
      subst hAA
      obtain ⟨B', he⟩ := lamBvar_step hΓ hA pb B hbody
      obtain ⟨hA'⟩ := F8A2Support.sort_transport unitSortUnique trueEnvUWfT hΓ
        (.of _ _ _ _ hc) hA
      exact ⟨A', B', congrArg (Expr.lam A') he, ⟨hA'⟩⟩
  | _, _, _, .iotaSpine _ _ _ _ _ prep hI _ _, A, B, hA, hx => by
      obtain ⟨A', B', he, _⟩ := doubleLam_step hΓ prep A B hA hx
      exact (F8EtaK.derivedIotaU_lam_source_false hI he).elim
  | _, _, _, .iotaStarK .., _, _, _, hx => by
      simp only [recCall, foldApps_snoc] at hx
      exact nomatch hx
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., _, _, _, hx => by
      have hhd := (iotaStarKEta_head happ).1
      rw [hx] at hhd
      exact nomatch hhd
  | _, _, _, .eta .., _, _, _, hx => by
      injection hx with _ hb
      exact nomatch hb
  | _, _, _, .sortEq .., _, _, _, hx => nomatch hx
  | _, _, _, .consts .., _, _, _, hx => nomatch hx
  | _, _, _, .bvarZeta .., _, _, _, hx => nomatch hx
  | _, _, _, .delta .., _, _, _, hx => nomatch hx
  | _, _, _, .app .., _, _, _, hx => nomatch hx
  | _, _, _, .beta .., _, _, _, hx => nomatch hx
  | _, _, _, .pi .., _, _, _, hx => nomatch hx
  | _, _, _, .letE .., _, _, _, hx => nomatch hx
  | _, _, _, .zeta .., _, _, _, hx => nomatch hx
  | _, _, _, .lit .., _, _, _, hx => nomatch hx

/-- Every finite raw star preserves the right shape and its positive
domain invariant. The recursive subject is the literal star tail. -/
theorem doubleLam_star {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ) :
    {x j T : Expr Nat} →
    ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 Γ x j T →
    (A B : Expr Nat) → HasTyT trueEnvU 0 Γ A (.sort two) →
    x = .lam A (.lam B (.bvar 1)) →
    ∃ A' B' : Expr Nat, j = .lam A' (.lam B' (.bvar 1)) ∧
      Nonempty (HasTyT trueEnvU 0 Γ A' (.sort two))
  | _, _, _, .refl .., A, B, hA, hx => ⟨A, B, hx, ⟨hA⟩⟩
  | _, _, _, .tail p ps, A, B, hA, hx => by
      obtain ⟨A', B', he, ⟨hA'⟩⟩ := doubleLam_step hΓ p A B hA hx
      exact doubleLam_star hΓ ps A' B' hA' he

/-- Admitted all-star nonjoinability for the full native relation.
The type indices may be unrelated. There is no remaining proofhood,
sort-coherence, type-uniqueness, Pi-row, or star restriction premise. -/
theorem admitted_partial_no_valley {j T₁ T₂ : Expr Nat}
    (s : ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 []
      (.app (.const 2 [two]) unitMotive) j T₁)
    (t : ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 []
      (.lam (.sort (.succ .zero)) (.lam unitDomain (.bvar 1))) j T₂) : False := by
  have hg : RecSpine 1 (.app (.const 2 [two]) unitMotive) :=
    ⟨[two], rfl, eqNList_refl [two], rfl⟩
  obtain ⟨_, hh, _, _⟩ := recSpine_star CtxWfT.nil s 1 (by decide) hg
  obtain ⟨A, B, ht, _⟩ := doubleLam_star CtxWfT.nil t
    (.sort (.succ .zero)) unitDomain (.sort [] (.succ .zero)) rfl
  rw [ht] at hh
  exact nomatch hh

/-- Even distinct reducts cannot have the same exact application-spine
head. This rules out a meeting modulo any relation only when that
relation actually preserves those heads; no modulo relation is invented. -/
theorem admitted_partial_heads_differ {j₁ j₂ T₁ T₂ : Expr Nat}
    (s : ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 []
      (.app (.const 2 [two]) unitMotive) j₁ T₁)
    (t : ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 []
      (.lam (.sort (.succ .zero)) (.lam unitDomain (.bvar 1))) j₂ T₂) :
    (appsSpine j₁).1 ≠ (appsSpine j₂).1 := by
  have hg : RecSpine 1 (.app (.const 2 [two]) unitMotive) :=
    ⟨[two], rfl, eqNList_refl [two], rfl⟩
  obtain ⟨_, hh, _, _⟩ := recSpine_star CtxWfT.nil s 1 (by decide) hg
  obtain ⟨A, B, ht, _⟩ := doubleLam_star CtxWfT.nil t
    (.sort (.succ .zero)) unitDomain (.sort [] (.succ .zero)) rfl
  intro heq
  rw [hh, ht] at heq
  exact nomatch heq

/-- Raw stars cannot meet through the published raw proof comparison,
even with arbitrary independent native indices. -/
theorem admitted_partial_no_peqT {j₁ j₂ T₁ T₂ : Expr Nat}
    (s : ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 []
      (.app (.const 2 [two]) unitMotive) j₁ T₁)
    (t : ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 []
      (.lam (.sort (.succ .zero)) (.lam unitDomain (.bvar 1))) j₂ T₂)
    (h : PEqT trueEnvU 0 [] j₁ j₂) : False := by
  have hg : RecSpine 1 (.app (.const 2 [two]) unitMotive) :=
    ⟨[two], rfl, eqNList_refl [two], rfl⟩
  have hj₁ := recSpine_star CtxWfT.nil s 1 (by decide) hg
  obtain ⟨_, hh, _, _⟩ := (recSpine_peqT_iff CtxWfT.nil h 1).1 hj₁
  obtain ⟨A, B, ht, _⟩ := doubleLam_star CtxWfT.nil t
    (.sort (.succ .zero)) unitDomain (.sort [] (.succ .zero)) rfl
  rw [ht] at hh
  exact nomatch hh

/-- The reverse comparison is excluded directly; raw PEqT symmetry is
neither assumed nor used. -/
theorem admitted_partial_no_peqT_reverse {j₁ j₂ T₁ T₂ : Expr Nat}
    (s : ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 []
      (.app (.const 2 [two]) unitMotive) j₁ T₁)
    (t : ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 []
      (.lam (.sort (.succ .zero)) (.lam unitDomain (.bvar 1))) j₂ T₂)
    (h : PEqT trueEnvU 0 [] j₂ j₁) : False := by
  have hg : RecSpine 1 (.app (.const 2 [two]) unitMotive) :=
    ⟨[two], rfl, eqNList_refl [two], rfl⟩
  have hj₁ := recSpine_star CtxWfT.nil s 1 (by decide) hg
  obtain ⟨_, hh, _, _⟩ := (recSpine_peqT_iff CtxWfT.nil h 1).2 hj₁
  obtain ⟨A, B, ht, _⟩ := doubleLam_star CtxWfT.nil t
    (.sort (.succ .zero)) unitDomain (.sort [] (.succ .zero)) rfl
  rw [ht] at hh
  exact nomatch hh

/-- The existing typed wrapper carries the same impossible comparison. -/
theorem admitted_partial_no_peqLeafT {j₁ j₂ T₁ T₂ U : Expr Nat}
    (s : ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 []
      (.app (.const 2 [two]) unitMotive) j₁ T₁)
    (t : ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 []
      (.lam (.sort (.succ .zero)) (.lam unitDomain (.bvar 1))) j₂ T₂)
    (h : PEqLeafT trueEnvU 0 [] j₁ j₂ U) : False :=
  admitted_partial_no_peqT s t h.1

/-- The typed reverse wrapper is excluded without a symmetry supplier. -/
theorem admitted_partial_no_peqLeafT_reverse {j₁ j₂ T₁ T₂ U : Expr Nat}
    (s : ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 []
      (.app (.const 2 [two]) unitMotive) j₁ T₁)
    (t : ParRedTStar (ProofLeaf trueEnvU 0) trueEnvU 0 []
      (.lam (.sort (.succ .zero)) (.lam unitDomain (.bvar 1))) j₂ T₂)
    (h : PEqLeafT trueEnvU 0 [] j₂ j₁ U) : False :=
  admitted_partial_no_peqT_reverse s t h.1

#print axioms unitSortUnique
#print axioms rec2_notProof
#print axioms recSpine_notProof
#print axioms recSpine_no_iota
#print axioms rec2_witness_arity
#print axioms recSpine_step
#print axioms recSpine_star
#print axioms recSpine_peqT_iff
#print axioms bvar1_notProof
#print axioms lamBvar_notProof
#print axioms doubleLam_notProof
#print axioms boundMinor_step
#print axioms lamBvar_step
#print axioms doubleLam_step
#print axioms doubleLam_star
#print axioms admitted_partial_no_valley
#print axioms admitted_partial_heads_differ
#print axioms admitted_partial_no_peqT
#print axioms admitted_partial_no_peqT_reverse
#print axioms admitted_partial_no_peqLeafT
#print axioms admitted_partial_no_peqLeafT_reverse

end Rcic.Declarative.NativeValleys.NativeKPartialObstructionAudit
