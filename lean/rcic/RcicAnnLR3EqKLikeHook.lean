import rcic.RcicAnnLR3EqReflectionChoice

/-!
# A K-like recursor hook for AnySort Eq on the Target

The landed recursor hook applies the major to its case selector, so a call
at a neutral major is stuck and a large elimination there has no type image
(`EqReflectionChoice.neutral_major_not_sort`). The source theory has K-like
reduction for Eq. The Target's family hook is a free parameter, so we can
evaluate the recursor of this K-like family (one constructor, no fields)
K-like: `kTerm = λ A a motive minor b major. minor`.

`eqKHook` is `kTerm` at the recursor `65` and `indexHook` elsewhere. On the
Target `annSemantics C (view env) (hook hE eqKHook)`:

- `kcall_image`: every call `Eq.rec A a motive minor b e` evaluates to its
  minor, whatever the major `e` is;
- `k_rawIota`: the raw ι law holds for every ι redex of the environment
  (each one is a call at a refl major, whose reduct is the minor);
- `k_conv_iota`: hence arm 17, for every code system;
- `k_large_elim_level`: consequently a large elimination into `Prop` with a
  level-zero type as minor is a level-zero sort member at every raw
  environment, including one binding the major to a neutral. The family
  images are still the index-retaining tagged ones of `indexHook`.

So the stuck-call obstruction of `EqReflectionChoice` and the inconsistent
context conflict between two large eliminations both disappear: every
large-elimination call is its minor. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EqKLikeHook

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements
open IotaRecursor AdmissionUniverseReadback EqTargetIota IndexFamilyHook EqLargeFixture
open EqReflectionChoice (jcall)

/-- `λ A a motive minor b major. minor`. -/
def kTerm : Expr Nat := lams 6 (.bvar 2)

def eqKHook : EnvironmentEval.FamilySyntax := fun ν r ls m =>
  if r = 65 then kTerm else indexHook env ν r ls m

theorem kTerm_apply (ρ : EnvI) (xs : List Value) (hn : xs.length = 6)
    (hb : ∀ x ∈ xs, x .bot) :
    applyAll (denI ρ kTerm) xs = xs[3]'(by omega) := by
  rw [kTerm, lams_apply 6 _ ρ xs hn]
  have hlook := pushAll_lookup xs ρ 3 (by omega)
  have h2 : xs.length - 1 - 3 = 2 := by omega
  rw [h2] at hlook
  have hbot : pushAll xs ρ 2 .bot := by
    rw [hlook]
    exact hb _ (List.getElem_mem _)
  rw [denI_bvar hbot, hlook]

theorem rec_const_image (hE : EnvWfA (iotaIfaceA env) env) (ν : Valuation) (ρ : EnvI)
    (ls : List Level) :
    EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ (.const 65 ls) =
      denI ρ kTerm := by
  have hm : env.members 65 = some recMember := rfl
  have hbody : EnvironmentEval.definitionBody (SemanticMemberEval.view env) 65 ls = none := by
    rw [SemanticMemberEval.definitionBody_preserved]
    simp [EnvironmentEval.definitionBody, hm, recMember, transparent]
  obtain ⟨A, u, B, v, hT⟩ := eq_ctorRecPi 65 recMember hm (Or.inr rfl) ls
  have hread : readAdmitted hE ν (instantiateLevelsA ls recMember.mtypeA) = none := by
    rw [hT]
    exact read_pi_none hE ν A u B v
  have hv : (SemanticMemberEval.view env).members 65 =
      some (SemanticMemberEval.route recMember) := by
    simp [SemanticMemberEval.view, hm]
  have hrigid : EnvironmentEval.rigidTerm (SemanticMemberEval.view env) (hook hE eqKHook)
      ν 65 ls = kTerm := by
    have hc : recMember.mclass = .recursorM := rfl
    simp [EnvironmentEval.rigidTerm, hv, SemanticMemberEval.route, hc, hook, hm, hread, eqKHook]
  rw [NeutralCodes.valueEq_eq (EnvironmentEval.denote_rigid hbody _ ν ρ), hrigid]

theorem denote_rec_spine (hE : EnvWfA (iotaIfaceA env) env) (ν : Valuation) (ρ : EnvI)
    (ls : List Level) (args : List ExprA) (hlen : args.length = 6) (minor : ExprA)
    (hminor : args[3]? = some minor) :
    EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ
        (foldAppsA (.const 65 ls) args) =
      EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ minor := by
  rw [denote_foldAppsA, rec_const_image hE ν ρ ls,
    kTerm_apply ρ _ (by simp [hlen]) (by
      intro x hx
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
      exact EnvironmentEval.denote_bot _ _ _ _ _)]
  have h3 : args[3]'(by omega) = minor := by
    have := List.getElem?_eq_getElem (l := args) (n := 3) (by omega)
    rw [this] at hminor
    exact Option.some.inj hminor
  simp [h3]

/-- Every call evaluates to its minor, whatever the major. -/
theorem kcall_image (hE : EnvWfA (iotaIfaceA env) env) (ν : Valuation) (ρ : EnvI)
    (u : Level) (A a motive minor b e : ExprA) :
    EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ
        (jcall u A a motive minor b e) =
      EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ minor :=
  denote_rec_spine hE ν ρ [u] [A, a, motive, minor, b, e] rfl minor rfl

theorem eq_rec_data :
    (iotaGroupA env 65 64).map (fun g => (g.nparams, g.nMinors, g.ctorIdx, piCountA g.recM.mtypeA)) =
      some (2, 1, 0, 6) := by
  decide

theorem rhsArgsA_no_fields (rec : ExprA) (pre : List ExprA) (np nm : Nat) (fs : List ExprA)
    (T : ExprA) : rhsArgsA rec pre np nm fs [] T = [] := by
  cases fs <;> cases T <;> rfl

/-- The raw ι law for the K-like hook. -/
theorem k_rawIota (hE : EnvWfA (iotaIfaceA env) env) {lhs rhs : ExprA}
    (h : iotaFnA env lhs = some rhs) (ν : Valuation) (ρ : EnvI) :
    EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ lhs =
      EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ rhs := by
  obtain ⟨s, c, g, hs, hc, hg, hred⟩ := iotaFnA_some h
  obtain ⟨c', shapes, minor, ctorAfter, hc', _, hplen, _, hshapes, hminor, _, _, hrhs⟩ :=
    IotaRecursor.iotaReductA_inv hred
  obtain ⟨hrecM, hrecC, hctorM, hctorC, _⟩ := iotaGroupA_some hg
  rcases EqTracer.eq_members hrecM with ⟨_, hm⟩ | ⟨_, hm⟩ | ⟨hr, _⟩ <;>
    try (rw [hm] at hrecC; exact absurd hrecC (by decide))
  rcases EqTracer.eq_members hctorM with ⟨_, hm⟩ | ⟨hcr, _⟩ | ⟨_, hm⟩ <;>
    try (rw [hm] at hctorC; exact absurd hctorC (by decide))
  rw [hr] at hg
  rw [hcr] at hg
  have hd := eq_rec_data
  rw [hg] at hd
  injection hd with hd
  simp only [Prod.mk.injEq] at hd
  obtain ⟨hnp, _, hidx, hpi⟩ := hd
  have hsh := EqTracer.eq_group_data
  rw [hg] at hsh
  injection hsh with hsh
  simp only [Prod.mk.injEq] at hsh
  obtain ⟨hnp', hfam, hty⟩ := hsh
  rw [hnp', hfam, hty, EqTracer.eq_shapes] at hshapes
  injection hshapes with hshapes
  subst hshapes
  have hlhs : lhs = foldAppsA (.const s.recRef s.ls) (s.preMajor ++ [s.major]) := by
    rw [← foldAppsA_appsSpineA lhs, recSpineA_some hs]
  have hrhs' : rhs = minor := by
    rw [hrhs, rhsArgsA_no_fields]
    rfl
  rw [hlhs, hrhs', hr]
  rw [hnp, hidx] at hminor
  refine denote_rec_spine hE ν ρ s.ls _ (by simp; omega) minor ?_
  rw [List.getElem?_append_left (by omega)]
  exact hminor

theorem k_conv_iota (C : CodeSystem) (hE : EnvWfA (iotaIfaceA env) env) (n : Nat) :
    PairedArms.Conv_iota
      (EnvironmentEval.annSemantics C (SemanticMemberEval.view env) (hook hE eqKHook))
      env (iotaIfaceA env) n :=
  conv_iota_of_rawIota (fun _ _ _ _ h _ ν ρ => k_rawIota hE h ν ρ)

/-- A large elimination into `Prop` whose minor is a level-zero type is a
level-zero sort member at every raw environment, whatever the major. -/
theorem k_large_elim_level (hE : EnvWfA (iotaIfaceA env) env) (ν : Valuation) (ρ : EnvI)
    (u : Level) (A a motive b e : ExprA) (T : ExprA)
    (hT : SortMember (some 0)
      (EnvironmentEval.denote (SemanticMemberEval.view env) (hook hE eqKHook) ν ρ T)) :
    SortMember (some 0) (EnvironmentEval.denote (SemanticMemberEval.view env)
      (hook hE eqKHook) ν ρ (jcall u A a motive T b e)) := by
  rw [kcall_image]
  exact hT

end Rcic.Declarative.Ann.LR3.EqKLikeHook
