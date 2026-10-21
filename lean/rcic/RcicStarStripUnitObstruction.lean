import rcic.RcicStarStripUnitPeak
import rcic.RcicSortUniqueRows
import rcic.RcicNativeValleyDecoTransfer

/-!
# An admitted, closed countermodel to canonical certified StarStrip

The unchanged `trueEnvU` is admitted by `trueEnvUWfT` and its unit-group
profile is certified by `trueEnvUWfT_inScope`.  The existing finite-model
semantic supplier gives its actual sort-coherence theorem.  This is a
negative client of those independently constructed finite-model rows;
their implementation passes through rows-conditional type uniqueness.
No sort-coherence, type-uniqueness, Pi-row, negative-proofhood, diamond,
confluence, or retyping premise remains in the final counterexamples.

Every certified star from the two-argument `True.rec.{2}` prefix retains
constant head 2, two supplied arguments, and a universe list semantically
equal to `[2]`.  Every certified star from `fun _ : True => Prop` retains
a lambda with a sort body.  Arbitrary argument changes, arbitrary lambda
domain changes, arbitrary semantically equal sort levels, arbitrary type
indices, and both ordinary iota witness formats are covered.

The actual canonical source-coherent native peak and its native
conversion are constructed by `RcicStarStripUnitPeak`.  Their joining
stars are impossible by the all-length invariants below.  This refutes
the published certified `StarStrip` interface and a certified valley
for that native conversion.  This nonjoinability concerns certified
stars; `unitRawValley` supplies an unrestricted eta-K control for the
same endpoints.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.StarStripUnitObstructionAudit

open CoherentCanonicalAudit (nativeLeafIface)
open StarStripUnitPeakAudit

private abbrev two : Level := .succ (.succ .zero)

/-- The sorting supplier is concretely instantiated at the existing
admitted unit group.  It is not an argument to any result below. -/
private theorem unitSortUnique : F8A2Support.SortUnique trueEnvU 0 :=
  sortUnique_of_inScope trueEnvUWfT trueEnvUWfT_inScope 0

private theorem unitZeroSortCoherence : HostPropAudit.ZeroSortCoherence trueEnvU 0 := by
  intro hW Γ A u hΓ hA hP
  exact unitSortUnique hW hΓ hA hP

/-- At a universe semantically equal to 2, the actual recursor constant
cannot be a proof.  Its three Pi binders expose the motive application,
whose stored positive sort contradicts any hypothetical Prop sorting. -/
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

/-- Shape of an existing expression, recording the exact supplied
argument count and the universe equality.  This is not a reduction. -/
def RecSpine (k : Nat) (e : Expr Nat) : Prop :=
  ∃ ls : List Level,
    (appsSpine e).1 = .const 2 ls ∧
    eqNList [two] ls ∧ (appsSpine e).2.length = k

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

/-- Every certified step preserves a proper recursor prefix's head and
exact argument count.  Argument terms may change arbitrarily.  Only
original `conv`, `app`, and `iotaSpine` children are recursive subjects. -/
theorem recSpine_step {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ) :
    {x j T : Expr Nat} →
    {p : ParRedT (ProofLeaf trueEnvU 0) trueEnvU 0 Γ x j T} →
    Certified p → (k : Nat) → k < 3 → RecSpine k x → RecSpine k j
  | _, _, _, _, .refl _, _, _, hs => hs
  | _, _, _, _, .conv _ ch, k, hk, hs => recSpine_step hΓ ch k hk hs
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, _, _, hs =>
      (recSpine_notProof hΓ hs h.hp h.hT).elim
  | _, _, _, _, @Certified.consts _ _ _ _ r ls ls' _ hu _ _ _, _, _, hs => by
      obtain ⟨us, hh, h1, hlen⟩ := hs
      have hh' : r = 2 ∧ ls = us := Expr.const.inj hh
      obtain ⟨rfl, rfl⟩ := hh'
      exact ⟨ls', rfl, F8A2Support.eqNList_trans_local h1 hu, hlen⟩
  | _, _, _, _, @Certified.delta _ _ _ _ r ls m _ _ hr _ htr _ _ _ _ _, _, _, hs => by
      obtain ⟨us, hh, _, _⟩ := hs
      have he : r = 2 := (Expr.const.inj hh).1
      rw [he] at hr
      change some trueRecMemberU = some m at hr
      have hm : m = trueRecMemberU := (Option.some.inj hr).symm
      rw [hm] at htr
      exact nomatch htr
  | _, _, _, _, @Certified.app _ _ _ _ f f' a a' _ _ _ _ _ _ _ _ _ _ _ _ cf _, k, hk, hs => by
      obtain ⟨ls, hh, hu, hlen⟩ := hs
      have hn : (appsSpine f).2.length + 1 = k := by
        simpa only [appsSpine, List.length_append, List.length_singleton] using hlen
      have hsmall : (appsSpine f).2.length < 3 := by omega
      have hf : RecSpine (appsSpine f).2.length f := ⟨ls, hh, hu, rfl⟩
      obtain ⟨ls', hh', hu', hlen'⟩ := recSpine_step hΓ cf _ hsmall hf
      refine ⟨ls', hh', hu', ?_⟩
      simpa only [appsSpine, List.length_append, List.length_singleton, hlen'] using hn
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ _ _ cs, k, hk, hs =>
      (recSpine_no_iota hk (recSpine_step hΓ cs k hk hs) hI).elim
  | _, _, _, _, .beta .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, _, .sortEq .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, _, .bvarZeta .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, _, .lam .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, _, .pi .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, _, .letE .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, _, .zeta .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, _, .lit .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh
  | _, _, _, _, .eta .., _, _, hs => by
      obtain ⟨_, hh, _, _⟩ := hs
      exact nomatch hh

/-- Proper recursor prefixes keep their shape along every finite
certified star; recursion decreases the original star's literal tail. -/
theorem recSpine_star {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ) :
    {x j T : Expr Nat} →
    (s : CStar trueEnvU 0 (ProofLeaf trueEnvU 0) Γ x j T) →
    (k : Nat) → k < 3 → RecSpine k x → RecSpine k j
  | _, _, _, .refl .., _, _, hs => hs
  | _, _, _, .tail p ps, k, hk, hs =>
      recSpine_star hΓ ps k hk (recSpine_step hΓ p.cert k hk hs)

private theorem sort_notProof {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ) (u : Level) :
    NotProof trueEnvU 0 Γ (.sort u) := by
  intro P hp hP
  exact peq_sort_source_false trueEnvUWfT (nativeLeafIface trueEnvU 0)
    unitZeroSortCoherence hΓ
    (show ProofLeaf trueEnvU 0 Γ (.sort u) (.sort u) P from ⟨hP, hp, hp⟩)

/-- A lambda with a sort body cannot have a proof typing, regardless of
its domain annotation or the displayed sort level. -/
private theorem lamSort_notProof {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ)
    (A : Expr Nat) (u : Level) : NotProof trueEnvU 0 Γ (.lam A (.sort u)) := by
  intro P hp hP
  obtain ⟨v, B, hA, hb, c⟩ := hasTyTInv_lam hp rfl
  obtain ⟨hpi0⟩ := F8A2Support.sort_transport unitSortUnique trueEnvUWfT hΓ c.symmT hP
  obtain ⟨_, _, ⟨hB0⟩⟩ := F8A2Support.pi_zero_inv unitSortUnique trueEnvUWfT hΓ hpi0
  exact sort_notProof (.assumption _ A v hΓ hA) u hb hB0

/-- Every possible certified step from a lambda with a sort body keeps
that shape.  The domain annotation and sort level may both change. -/
theorem lamSort_step {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ) :
    {x j T : Expr Nat} →
    {p : ParRedT (ProofLeaf trueEnvU 0) trueEnvU 0 Γ x j T} →
    Certified p → (A : Expr Nat) → (u : Level) → x = .lam A (.sort u) →
    ∃ (A' : Expr Nat) (u' : Level), j = .lam A' (.sort u')
  | _, _, _, _, .refl _, A, u, hx => ⟨A, u, hx⟩
  | _, _, _, _, .conv _ ch, A, u, hx => lamSort_step hΓ ch A u hx
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, A, u, hx => by
      subst hx
      exact (lamSort_notProof hΓ A u h.hp h.hT).elim
  | _, _, _, _, @Certified.lam _ _ _ _ A A' _ _ _ v _ _ hA _ pb _ _ _, _, _, hx => by
      injection hx with _ hb
      have hΓA : CtxWfT trueEnvU 0 (.assumption A :: Γ) := .assumption _ A v hΓ hA
      obtain ⟨u', he, _⟩ := parRedT_sort_inv_of_zsc trueEnvUWfT
        (nativeLeafIface trueEnvU 0) unitZeroSortCoherence hΓA pb hb
      exact ⟨A', u', congrArg (Expr.lam A') he⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ _ _ _ _ hI _ _ _ cs, A, u, hx => by
      obtain ⟨A', u', he⟩ := lamSort_step hΓ cs A u hx
      subst he
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      simp [recCall, foldApps_snoc] at hl
  | _, _, _, _, .eta .., _, _, hx => by
      injection hx with _ hb
      exact nomatch hb
  | _, _, _, _, .sortEq .., _, _, hx => nomatch hx
  | _, _, _, _, .consts .., _, _, hx => nomatch hx
  | _, _, _, _, .bvarZeta .., _, _, hx => nomatch hx
  | _, _, _, _, .delta .., _, _, hx => nomatch hx
  | _, _, _, _, .app .., _, _, hx => nomatch hx
  | _, _, _, _, .beta .., _, _, hx => nomatch hx
  | _, _, _, _, .pi .., _, _, hx => nomatch hx
  | _, _, _, _, .letE .., _, _, hx => nomatch hx
  | _, _, _, _, .zeta .., _, _, hx => nomatch hx
  | _, _, _, _, .lit .., _, _, hx => nomatch hx

/-- Every finite star from a sort-returning lambda retains a lambda
with a sort body, with no restriction on intervening native certificates. -/
theorem lamSort_star {Γ : LCtx} (hΓ : CtxWfT trueEnvU 0 Γ) :
    {x j T : Expr Nat} →
    (s : CStar trueEnvU 0 (ProofLeaf trueEnvU 0) Γ x j T) →
    (A : Expr Nat) → (u : Level) → x = .lam A (.sort u) →
    ∃ (A' : Expr Nat) (u' : Level), j = .lam A' (.sort u')
  | _, _, _, .refl .., A, u, hx => ⟨A, u, hx⟩
  | _, _, _, .tail p ps, A, u, hx => by
      obtain ⟨A', u', hp⟩ := lamSort_step hΓ p.cert A u hx
      exact lamSort_star hΓ ps A' u' hp

theorem unitPartialRec_shape : RecSpine 2 unitPartialRec :=
  ⟨[two], rfl, eqNList_refl [two], rfl⟩

/-- Actual admitted all-star nonjoinability, with independent type
indices and no decoration restriction.  No negative premise is left. -/
theorem admitted_unit_no_valley {j T₁ T₂ : Expr Nat}
    (s : CStar trueEnvU 0 (ProofLeaf trueEnvU 0) [] unitPartialRec j T₁)
    (t : CStar trueEnvU 0 (ProofLeaf trueEnvU 0) [] unitContracted j T₂) : False := by
  obtain ⟨ls, hh, _, _⟩ := recSpine_star CtxWfT.nil s 2 (by decide) unitPartialRec_shape
  obtain ⟨A, u, ht⟩ := lamSort_star CtxWfT.nil t unitDomain .zero rfl
  rw [ht] at hh
  exact nomatch hh

/-- The real native conversion has no certified valley at its actual
index, even though the environment and empty context are admitted. -/
theorem admitted_unit_conversion_without_valley :
    Nonempty (EnvWfT trueEnvU) ∧
    Nonempty (CtxWfT trueEnvU 0 []) ∧
    Nonempty (ConvT trueEnvU 0 [] unitPartialRec unitContracted unitIndex) ∧
    ¬ Nonempty (CValley trueEnvU 0 (ProofLeaf trueEnvU 0) []
      unitPartialRec unitContracted unitIndex) := by
  refine ⟨⟨trueEnvUWfT⟩, ⟨.nil⟩, ⟨unitConversion⟩, ?_⟩
  rintro ⟨v⟩
  exact admitted_unit_no_valley v.left v.right

/-- The exact published canonical `StarStrip` is false in the admitted
unit environment.  Its source-decoration premise is met by the actual
native peak in `unitStarStripValley`; no local join approximation is used. -/
theorem admitted_unit_starStrip_false :
    Nonempty (EnvWfT trueEnvU) ∧
    ¬ Nonempty (CoherentStarStripAudit.StarStrip (nativeLeafIface trueEnvU 0)) := by
  refine ⟨⟨trueEnvUWfT⟩, ?_⟩
  rintro ⟨D⟩
  let v := unitStarStripValley D
  exact admitted_unit_no_valley v.left v.right

#print axioms unitSortUnique
#print axioms unitZeroSortCoherence
#print axioms rec2_notProof
#print axioms recSpine_step
#print axioms recSpine_star
#print axioms lamSort_step
#print axioms lamSort_star
#print axioms unitPartialRec_shape
#print axioms admitted_unit_no_valley
#print axioms admitted_unit_conversion_without_valley
#print axioms admitted_unit_starStrip_false

end Rcic.Declarative.NativeValleys.StarStripUnitObstructionAudit
