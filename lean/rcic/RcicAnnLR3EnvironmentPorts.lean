import rcic.RcicAnnLR3EnvironmentEval
import rcic.RcicAnnLR3EnvironmentTelescopePorts
import rcic.RcicAnnLR3EnvironmentPortConditions
import rcic.RcicAnnAnnotate
import rcic.RcicAnnLevels

/-!
# EnvironmentEval ports: literal arms and constant level transport

Ports for the `PairedArms` contract family at the actual composed
EnvironmentEval interpretation
`annSemantics C (internalView E) (hook E neutralFamilySyntax)`:

* `Ty_lit` and `Conv_lit` consume the already-supplied expansion equation
  `denote_literal`. The two world images of `.lit t` and `natExpandA t`
  are literally equal values, so the child-IH relation transports without
  any extra premise.
* `Conv_consts` is the admitted-member / hook level-transport port. Its
  engine is `translation_evalAgree_transport`: a finite translation at an
  eval-agreeing source term yields one at the partner term with a
  pointwise denotation inclusion (`NativeBelow`). The raw law is stated
  for an arbitrary environment and family syntax, with exactly the named
  premises it consumes:

  - `HookEnvironmentIndependent`, `HookEqNCompatible` — the hook port
    conditions, discharged for the actual configuration by
    `EnvironmentTelescopePorts.default_hook_conditions` from `EnvWfA`
    (the source admission).
  - `BodyConstsArity` — every stored member body is hereditarily
    arity-correct (`ConstsArityA`). This is the admitted-body premise the
    transport recursion needs at the `constBody` step; it is discharged
    at `internalView E` by `internalView_bodyConstsArity` from
    `envWfA_memberBody` (member bodies are typed at their stored type)
    through `hasTyA_constsArity`. The stored closedness and
    level-boundedness supplied by
    `EnvironmentTelescopePorts.internalView_body_conditions` are not
    consumed by this conditional transport: it transports given
    translations rather than proving their existence or well-formedness.

Every `PairedArms` source premise and child-IH position is preserved in
the suppliers; the unused contract hypotheses (`hlen`, `hwf`, `hwf'`,
`hrt`) are kept in contract order. No Fundamental premise is added.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EnvironmentPorts

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements EnvironmentEval
open EnvironmentPortConditions

/-! ## Small level-list algebra (symmetry is missing from `RcicLevelCalc`) -/

theorem eqNList_symm_envPort {ls ls' : List Level} (h : eqNList ls ls') :
    eqNList ls' ls := by
  induction ls generalizing ls' with
  | nil =>
      cases ls' with
      | nil => exact True.intro
      | cons _ _ => exact False.elim h
  | cons _ _ ih =>
      cases ls' with
      | nil => exact False.elim h
      | cons _ _ => exact ⟨fun ρ => (h.1 ρ).symm, ih h.2⟩

/-! ## EvalAgree: structural pairing of eval-agreeing source terms

`EvalAgree ν e₁ e₂` pairs terms that differ only in level fields whose
`eval ν` values agree (and in constant argument lists related by
`eqNList`). The `lam`/level fields ignored by `Translation` are
unconstrained; `pi` universes are constrained because the translated
target is tagged by `eval ν (.imax u v)`. -/

inductive EvalAgree (ν : Valuation) : ExprA → ExprA → Prop
  | bvar (i : Nat) : EvalAgree ν (.bvar i) (.bvar i)
  | sort {l₁ l₂ : Level} (h : eval ν l₁ = eval ν l₂) :
      EvalAgree ν (.sort l₁) (.sort l₂)
  | const {r : Nat} {ls₁ ls₂ : List Level} (h : eqNList ls₁ ls₂) :
      EvalAgree ν (.const r ls₁) (.const r ls₂)
  | app {f₁ a₁ f₂ a₂ : ExprA} (hf : EvalAgree ν f₁ f₂) (ha : EvalAgree ν a₁ a₂) :
      EvalAgree ν (.app f₁ a₁) (.app f₂ a₂)
  | lam {A₁ A₂ b₁ b₂ : ExprA} {u₁ u₂ : Level}
      (hA : EvalAgree ν A₁ A₂) (hb : EvalAgree ν b₁ b₂) :
      EvalAgree ν (.lam A₁ u₁ b₁) (.lam A₂ u₂ b₂)
  | pi {A₁ A₂ B₁ B₂ : ExprA} {u₁ v₁ u₂ v₂ : Level}
      (hA : EvalAgree ν A₁ A₂) (hu : eval ν u₁ = eval ν u₂)
      (hB : EvalAgree ν B₁ B₂) (hv : eval ν v₁ = eval ν v₂) :
      EvalAgree ν (.pi A₁ u₁ B₁ v₁) (.pi A₂ u₂ B₂ v₂)
  | letE {A₁ v₁ b₁ A₂ v₂ b₂ : ExprA}
      (hA : EvalAgree ν A₁ A₂) (hv : EvalAgree ν v₁ v₂)
      (hb : EvalAgree ν b₁ b₂) :
      EvalAgree ν (.letE A₁ v₁ b₁) (.letE A₂ v₂ b₂)
  | lit (n : Nat) : EvalAgree ν (.lit n) (.lit n)

theorem evalAgree_instantiateLevels {ν : Valuation} {ks₁ ks₂ : List Level}
    (h : eqNList ks₁ ks₂) (b : ExprA) :
    EvalAgree ν (instantiateLevelsA ks₁ b) (instantiateLevelsA ks₂ b) := by
  induction b with
  | bvar i => exact .bvar i
  | sort l => exact .sort ((instLevel_eqNList h l) ν)
  | const r ms => exact .const (instLevel_eqNList_map h ms)
  | app f x ihf ihx => exact .app ihf ihx
  | lam a u b ihA ihb => exact .lam ihA ihb
  | pi a u b v ihA ihB =>
      exact .pi ihA ((instLevel_eqNList h u) ν) ihB ((instLevel_eqNList h v) ν)
  | letE a w b ihA ihW ihB => exact .letE ihA ihW ihB
  | lit n => exact .lit n

theorem eval_imax_agree {ν : Valuation} {u v u' v' : Level}
    (hu : eval ν u = eval ν u') (hv : eval ν v = eval ν v') :
    eval ν (.imax u v) = eval ν (.imax u' v') := by
  simp only [eval, hu, hv]

/-! ## definitionBody / member bookkeeping -/

/-- `definitionBody` reads only the member, its class and its stored body;
the argument list affects only the selected body's instantiation. -/
theorem definitionBody_none_preserved {E : ResolvedEnvA} {r : Nat}
    {ls ks : List Level}
    (h : definitionBody E r ls = none) : definitionBody E r ks = none := by
  cases hm : E.members r with
  | none => simp only [definitionBody, hm]
  | some m =>
      simp only [definitionBody, hm] at h ⊢
      cases ht : transparent m.mclass with
      | false => rfl
      | true =>
          cases hb : m.bodyA with
          | none => rfl
          | some b =>
              rw [ht, hb] at h
              exact Option.noConfusion h

/-- `internalView` members are double-routed source members; arity, body,
type and transparency all survive the two routes. -/
theorem internalView_member_data {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    (hm : E.members r = some m) :
    ∃ mv, (EnvironmentTelescopeInsertion.internalView E).members r = some mv ∧
      mv.arity = m.arity ∧ mv.bodyA = m.bodyA ∧ mv.mtypeA = m.mtypeA ∧
      transparent mv.mclass = transparent m.mclass := by
  refine ⟨EnvironmentMemberInsertion.route
      (EnvironmentTelescopeInsertion.route m), ?_, ?_, ?_, ?_, ?_⟩
  · simp [EnvironmentTelescopeInsertion.internalView,
      EnvironmentMemberInsertion.internalView,
      EnvironmentTelescopeInsertion.telescopeView, hm]
  · rw [EnvironmentMemberInsertion.route_arity,
      EnvironmentTelescopeInsertion.route_arity]
  · rw [EnvironmentMemberInsertion.route_body,
      EnvironmentTelescopeInsertion.route_body]
  · rw [EnvironmentMemberInsertion.route_type,
      EnvironmentTelescopeInsertion.route_type]
  · rw [EnvironmentMemberInsertion.route_transparent,
      EnvironmentTelescopeInsertion.route_transparent]

/-- The inverse direction: a view member comes from a source member with
the same arity, body and type. -/
theorem internalView_member_inv {E : ResolvedEnvA} {r : Nat} {mv : CheckedMemberA}
    (h : (EnvironmentTelescopeInsertion.internalView E).members r = some mv) :
    ∃ src, E.members r = some src ∧ mv.arity = src.arity ∧
      mv.bodyA = src.bodyA ∧ mv.mtypeA = src.mtypeA := by
  cases hs : E.members r with
  | none =>
      simp [EnvironmentTelescopeInsertion.internalView,
        EnvironmentMemberInsertion.internalView,
        EnvironmentTelescopeInsertion.telescopeView, hs] at h
  | some src =>
      have he : EnvironmentMemberInsertion.route
          (EnvironmentTelescopeInsertion.route src) = mv := by
        simpa [EnvironmentTelescopeInsertion.internalView,
          EnvironmentMemberInsertion.internalView,
          EnvironmentTelescopeInsertion.telescopeView, hs] using h
      subst he
      exact ⟨src, rfl,
        by rw [EnvironmentMemberInsertion.route_arity,
          EnvironmentTelescopeInsertion.route_arity],
        by rw [EnvironmentMemberInsertion.route_body,
          EnvironmentTelescopeInsertion.route_body],
        by rw [EnvironmentMemberInsertion.route_type,
          EnvironmentTelescopeInsertion.route_type]⟩

/-! ## ConstsArityA transport -/

/-- `ConstsArityA` is preserved by level instantiation: instantiation maps
argument lists but preserves their lengths. -/
theorem constsArityA_instantiateLevels {E : ResolvedEnvA} (ls : List Level)
    {b : ExprA} (h : ConstsArityA E b) :
    ConstsArityA E (instantiateLevelsA ls b) := by
  induction b with
  | bvar _ => trivial
  | sort _ => trivial
  | const r ms =>
      obtain ⟨m, hm, hlen⟩ := h
      show ConstsArityA E (.const r (ms.map (instLevel ls)))
      exact ⟨m, hm, by rw [List.length_map]; exact hlen⟩
  | app f x ihf ihx => exact ⟨ihf h.1, ihx h.2⟩
  | lam a u b ihA ihb => exact ⟨ihA h.1, ihb h.2⟩
  | pi a u b v ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | letE a w b ihA ihW ihB => exact ⟨ihA h.1, ihW h.2.1, ihB h.2.2⟩
  | lit _ => trivial

/-- Source arity correctness transports to the internal view because the
routes preserve arity. -/
theorem constsArityA_view {E : ResolvedEnvA} {e : ExprA}
    (h : ConstsArityA E e) :
    ConstsArityA (EnvironmentTelescopeInsertion.internalView E) e := by
  induction e with
  | bvar _ => trivial
  | sort _ => trivial
  | const r ms =>
      obtain ⟨m, hm, hlen⟩ := h
      obtain ⟨mv, hmv, har, _, _, _⟩ := internalView_member_data hm
      exact ⟨mv, hmv, hlen.trans har.symm⟩
  | app f x ihf ihx => exact ⟨ihf h.1, ihx h.2⟩
  | lam a u b ihA ihb => exact ⟨ihA h.1, ihb h.2⟩
  | pi a u b v ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | letE a w b ihA ihW ihB => exact ⟨ihA h.1, ihW h.2.1, ihB h.2.2⟩
  | lit _ => trivial

/-- The admitted-body premise the translation transport consumes: every
stored member body is hereditarily arity-correct at that environment.
Discharged from `EnvWfA` by `internalView_bodyConstsArity` below. -/
def BodyConstsArity (E : ResolvedEnvA) : Prop :=
  ∀ (r : Nat) (m : CheckedMemberA) (b : ExprA),
    E.members r = some m → m.bodyA = some b → ConstsArityA E b

/-- The view-level instance of the admitted-body premise, discharged from
source admission: view members come from source members whose bodies are
typed at the stored type (`envWfA_memberBody`), hence arity-correct
(`hasTyA_constsArity`), and arity correctness transports across the view
(`constsArityA_view`). -/
theorem internalView_bodyConstsArity {E : ResolvedEnvA} {I : IotaIfaceA}
    (hE : EnvWfA I E) :
    BodyConstsArity (EnvironmentTelescopeInsertion.internalView E) := by
  intro r mv b hmv hb
  obtain ⟨src, hsrc, _, hbo, _⟩ := internalView_member_inv hmv
  rw [hbo] at hb
  obtain ⟨hty⟩ := envWfA_memberBody hE r src b hsrc hb
  exact constsArityA_view (hasTyA_constsArity hty)

/-! ## The conditional translation transport -/

/-- At a hook-class member the rigid term is the family hook applied at
the stored member. -/
theorem rigidTerm_hook_eq {E : ResolvedEnvA} {F : FamilySyntax} {ν : Valuation}
    {r : Nat} {ls : List Level} {m : CheckedMemberA} (hm : E.members r = some m)
    (hcl : HookClass m) : rigidTerm E F ν r ls = F ν r ls m := by
  obtain hmc | hmc | hmc := hcl
  · simp only [rigidTerm, hm, hmc]
  · simp only [rigidTerm, hm, hmc]
  · simp only [rigidTerm, hm, hmc]

/-- Decidable `HookClass` split from `cases` on the member class — no
classical reasoning, so the transport stays inside the allowed axiom set. -/
theorem hookClass_or {m : CheckedMemberA} : HookClass m ∨ ¬ HookClass m := by
  cases hmc : m.mclass with
  | inductiveM => exact .inl (.inl hmc)
  | constructorM => exact .inl (.inr (.inl hmc))
  | recursorM => exact .inl (.inr (.inr hmc))
  | axiomM => exact .inr (by simp [HookClass, hmc])
  | definitionM => exact .inr (by simp [HookClass, hmc])
  | theoremM => exact .inr (by simp [HookClass, hmc])
  | opaqueM => exact .inr (by simp [HookClass, hmc])

/-- At a member outside the hook classes the rigid term is the neutral
`.const r []` fallback. -/
theorem rigidTerm_neutral_eq {E : ResolvedEnvA} {F : FamilySyntax} {ν : Valuation}
    {r : Nat} {ls : List Level} {m : CheckedMemberA} (hm : E.members r = some m)
    (hcl : ¬ HookClass m) : rigidTerm E F ν r ls = .const r [] := by
  cases hmc : m.mclass with
  | axiomM => simp only [rigidTerm, hm, hmc]
  | definitionM => simp only [rigidTerm, hm, hmc]
  | theoremM => simp only [rigidTerm, hm, hmc]
  | opaqueM => simp only [rigidTerm, hm, hmc]
  | inductiveM => exact absurd (.inl hmc) hcl
  | constructorM => exact absurd (.inr (.inl hmc)) hcl
  | recursorM => exact absurd (.inr (.inr hmc)) hcl

/-- The conditional evaluator transport: a finite translation of `e₁`
yields a translation of an `EvalAgree`-partner `e₂` whose denotation
includes the original's. Only the two hook port conditions and the
admitted-body arity premise are consumed; no closedness or `EnvWfA`
premise is needed because the theorem transports a given translation
rather than constructing one. -/
theorem translation_evalAgree_transport {E : ResolvedEnvA} {F : FamilySyntax}
    (hloc : HookEnvironmentIndependent E F) (hlev : HookEqNCompatible E F)
    (hbar : BodyConstsArity E) {ν : Valuation} {e₁ e₂ : ExprA}
    (ha : EvalAgree ν e₁ e₂) (har : ConstsArityA E e₁) {t : Expr Nat}
    (ht : Translation E F ν e₁ t) :
    ∃ t', Translation E F ν e₂ t' ∧ NativeBelow t t' := by
  revert ha har
  induction ht generalizing e₂ with
  | cut e => intro _ _; exact ⟨cutTerm, .cut _, NativeBelow.refl _⟩
  | bvar i =>
      intro hag _
      cases hag
      exact ⟨_, .bvar i, NativeBelow.refl _⟩
  | sort l =>
      intro hag _
      cases hag with
      | sort h =>
          rw [h]
          exact ⟨_, .sort _, NativeBelow.refl _⟩
  | constBody hbody htr ihtr =>
      intro hag har
      cases hag with
      | const hks =>
          obtain ⟨m, b0, hm, hb0, htm, hb⟩ := definitionBody_origin hbody
          subst hb
          obtain ⟨t', ht', hincl⟩ := ihtr
            (evalAgree_instantiateLevels hks b0)
            (constsArityA_instantiateLevels _ (hbar _ _ _ hm hb0))
          exact ⟨t', .constBody (definitionBody_of_member hm hb0 htm) ht', hincl⟩
  | constRigid hr =>
      intro hag har
      cases hag with
      | const hks =>
          obtain ⟨mv, hmv, hlen₁⟩ := har
          refine ⟨_, .constRigid (definitionBody_none_preserved hr), ?_⟩
          intro ρ c hden
          obtain hcl | hcl := hookClass_or (m := mv)
          · rw [rigidTerm_hook_eq hmv hcl] at hden
            rw [rigidTerm_hook_eq hmv hcl]
            exact ((hook_paired_compatible hloc hlev (ValuationRel.refl ν) hmv
              hcl hlen₁ ((eqNList_length _ _ hks).symm.trans hlen₁) hks ρ ρ) c).mp hden
          · rw [rigidTerm_neutral_eq hmv hcl] at hden
            rw [rigidTerm_neutral_eq hmv hcl]
            exact hden
  | app hf ha' ihf iha =>
      intro hag har
      cases hag with
      | app hf' ha'' =>
          obtain ⟨f'', tf, hinF⟩ := ihf hf' har.1
          obtain ⟨a'', ta, hinA⟩ := iha ha'' har.2
          exact ⟨_, .app tf ta, NativeBelow.app hinF hinA⟩
  | lam hA hb ihA ihb =>
      intro hag har
      cases hag with
      | lam hA' hb' =>
          obtain ⟨A'', tA, hinA⟩ := ihA hA' har.1
          obtain ⟨b'', tb, hinB⟩ := ihb hb' har.2
          exact ⟨_, .lam tA tb, NativeBelow.lam hinB⟩
  | pi hA hB ihA ihB =>
      intro hag har
      cases hag with
      | pi hA' hu hB' hv =>
          obtain ⟨A'', tA, hinA⟩ := ihA hA' har.1
          obtain ⟨B'', tB, hinB⟩ := ihB hB' har.2
          refine ⟨_, .pi tA tB, ?_⟩
          rw [eval_imax_agree hu hv]
          exact NativeBelow.tagged _ (NativeBelow.pi hinA hinB)
  | letE hA hv hb ihA ihv ihb =>
      intro hag har
      cases hag with
      | letE hA' hv' hb' =>
          obtain ⟨A'', tA, hinA⟩ := ihA hA' har.1
          obtain ⟨v'', tv, hinV⟩ := ihv hv' har.2.1
          obtain ⟨b'', tb, hinB⟩ := ihb hb' har.2.2
          exact ⟨_, .letE tA tv tb, NativeBelow.letE hinV hinB⟩
  | lit hexp _ =>
      intro hag _
      cases hag
      exact ⟨_, .lit hexp, NativeBelow.refl _⟩

/-- Instantiated bodies at `eqNList`-related level lists denote the same
value. The two inclusions are the conditional transport in each
direction. -/
theorem denote_instLevel_agree {E : ResolvedEnvA} {F : FamilySyntax}
    (hloc : HookEnvironmentIndependent E F) (hlev : HookEqNCompatible E F)
    (hbar : BodyConstsArity E) {ν : Valuation} {ρ : EnvI} {b : ExprA}
    (har : ConstsArityA E b) {ls ls' : List Level} (h : eqNList ls ls') :
    ValueEq (EnvironmentEval.denote E F ν ρ (instantiateLevelsA ls b))
      (EnvironmentEval.denote E F ν ρ (instantiateLevelsA ls' b)) := by
  intro c
  constructor
  · rintro ⟨t, ht, hc⟩
    obtain ⟨t', ht', hincl⟩ := translation_evalAgree_transport hloc hlev hbar
      (evalAgree_instantiateLevels h b) (constsArityA_instantiateLevels _ har) ht
    exact ⟨t', ht', hincl ρ c hc⟩
  · rintro ⟨t, ht, hc⟩
    obtain ⟨t', ht', hincl⟩ := translation_evalAgree_transport hloc hlev hbar
      (evalAgree_instantiateLevels (eqNList_symm_envPort h) b)
      (constsArityA_instantiateLevels _ har) ht
    exact ⟨t', ht', hincl ρ c hc⟩

/-! ## The literal arms

`denote_literal` is already supplied for EnvironmentEval; the arms only
transport the child-IH relation across the two world images. -/

theorem envEval_lit_image (C : CodeSystem) (E : ResolvedEnvA) (F : FamilySyntax)
    (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (t : Nat) :
    (annSemantics C E F).image ν Γ ρ (.lit t) =
      (annSemantics C E F).image ν Γ ρ (natExpandA t) :=
  NeutralCodes.valueEq_eq (denote_literal E F ν ρ t)

/-- The `Ty_lit` arm at the EnvironmentEval interpretation, for any family
syntax: the supplied expansion equation transports the child judgment. -/
theorem envEval_ty_lit_supplied (C : CodeSystem) (E : ResolvedEnvA)
    (F : FamilySyntax) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_lit (annSemantics C E F) E I n := by
  intro Γ t T hexp ih hΓ ν μ ρ σ hν hρ
  obtain ⟨k, R, S, hcodes, hrel⟩ := ih hΓ ν μ ρ σ hν hρ
  refine ⟨k, R, S, hcodes, ?_⟩
  rw [envEval_lit_image C E F ν Γ ρ t, envEval_lit_image C E F μ Γ σ t]
  exact hrel

/-- The `Conv_lit` arm: the expansion equation is needed at the left world
only; the right world already shows the expanded term. -/
theorem envEval_conv_lit_supplied (C : CodeSystem) (E : ResolvedEnvA)
    (F : FamilySyntax) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_lit (annSemantics C E F) E I n := by
  intro Γ t T hexp ih hΓ ν μ ρ σ hν hρ
  obtain ⟨k, R, S, hcodes, hrel⟩ := ih hΓ ν μ ρ σ hν hρ
  refine ⟨k, R, S, hcodes, ?_⟩
  rw [envEval_lit_image C E F ν Γ ρ t]
  exact hrel

/-! ## The `Conv_consts` arm at the actual composed interpretation

Instantiated at `internalView E` and `hook E neutralFamilySyntax`: the
five hook conditions come from `default_hook_conditions` and the
admitted-body arity premise from `internalView_bodyConstsArity`, both
discharged from `EnvWfA` (source admission). -/

/-- The `Conv_consts` arm. In the rigid case both sides translate to the
hook term at the same view member; the supplied hook conditions transport
`eqNList`-related argument lists inside each world and the neutral
fallback carries no level argument at all. In the transparent case both
sides unfold to the same stored body at `eqNList`-instantiated level
lists, and `denote_instLevel_agree` equalises the two instantiations.
Every source premise and the child-IH position are preserved; the unused
premises remain in contract order. -/
theorem envEval_conv_consts_supplied (C : CodeSystem) {E : ResolvedEnvA}
    {I : IotaIfaceA} (hE : EnvWfA I E) (n : Nat) :
    PairedArms.Conv_consts
      (annSemantics C (EnvironmentTelescopeInsertion.internalView E)
        (EnvironmentTelescopeInsertion.hook E neutralFamilySyntax)) E I n := by
  obtain ⟨hlift, hloc, heqN, hev, hlin⟩ :=
    EnvironmentTelescopePorts.default_hook_conditions hE
  have hbar := internalView_bodyConstsArity hE
  intro Γ r ls ls' m hres hlen hwf hwf' h hrt ih hΓ ν μ ρ σ hν hρ
  obtain ⟨k, R, S, hcodes, hrel⟩ := ih hΓ ν μ ρ σ hν hρ
  refine ⟨k, R, S, hcodes, ?_⟩
  change R
    (EnvironmentEval.denote (EnvironmentTelescopeInsertion.internalView E)
      (EnvironmentTelescopeInsertion.hook E neutralFamilySyntax) ν ρ (.const r ls))
    (EnvironmentEval.denote (EnvironmentTelescopeInsertion.internalView E)
      (EnvironmentTelescopeInsertion.hook E neutralFamilySyntax) μ σ (.const r ls'))
  cases hdef : definitionBody E r ls' with
  | none =>
      have hdl : definitionBody (EnvironmentTelescopeInsertion.internalView E) r ls =
          none := by
        rw [EnvironmentTelescopeInsertion.definitionBody_preserved]
        exact definitionBody_none_preserved hdef
      have hdr : definitionBody (EnvironmentTelescopeInsertion.internalView E) r ls' =
          none := by
        rw [EnvironmentTelescopeInsertion.definitionBody_preserved]
        exact hdef
      rw [NeutralCodes.valueEq_eq (denote_rigid hdl _ ν ρ),
        NeutralCodes.valueEq_eq (denote_rigid hdr _ μ σ)]
      have hrel' :
          R (denI ρ (rigidTerm (EnvironmentTelescopeInsertion.internalView E)
              (EnvironmentTelescopeInsertion.hook E neutralFamilySyntax) ν r ls'))
            (denI σ (rigidTerm (EnvironmentTelescopeInsertion.internalView E)
              (EnvironmentTelescopeInsertion.hook E neutralFamilySyntax) μ r ls')) := by
        have hr' :
            R (EnvironmentEval.denote (EnvironmentTelescopeInsertion.internalView E)
                (EnvironmentTelescopeInsertion.hook E neutralFamilySyntax) ν ρ
                (.const r ls'))
              (EnvironmentEval.denote (EnvironmentTelescopeInsertion.internalView E)
                (EnvironmentTelescopeInsertion.hook E neutralFamilySyntax) μ σ
                (.const r ls')) := hrel
        rwa [NeutralCodes.valueEq_eq (denote_rigid hdr _ ν ρ),
          NeutralCodes.valueEq_eq (denote_rigid hdr _ μ σ)] at hr'
      obtain ⟨mv, hmv, har, _, _, _⟩ := internalView_member_data hres
      have hlen₁ : ls.length = mv.arity := hlen.trans har.symm
      have hlen₂ : ls'.length = mv.arity :=
        (eqNList_length _ _ h).symm.trans hlen₁
      obtain hcl | hcl := hookClass_or (m := mv)
      · rw [rigidTerm_hook_eq hmv hcl, rigidTerm_hook_eq hmv hcl]
        rw [rigidTerm_hook_eq hmv hcl, rigidTerm_hook_eq hmv hcl] at hrel'
        rw [← NeutralCodes.valueEq_eq (hook_paired_compatible hloc heqN
          (ValuationRel.refl ν) hmv hcl hlen₁ hlen₂ h ρ ρ)] at hrel'
        exact hrel'
      · rw [rigidTerm_neutral_eq hmv hcl, rigidTerm_neutral_eq hmv hcl]
        rwa [rigidTerm_neutral_eq hmv hcl, rigidTerm_neutral_eq hmv hcl] at hrel'
  | some b' =>
      have hbv : definitionBody (EnvironmentTelescopeInsertion.internalView E) r ls' =
          some b' := by
        rw [EnvironmentTelescopeInsertion.definitionBody_preserved]
        exact hdef
      obtain ⟨mv, b0, hmv, hb0, htm, rfl⟩ := definitionBody_origin hbv
      have harB : ConstsArityA (EnvironmentTelescopeInsertion.internalView E) b0 := by
        obtain ⟨src, hsrc, _, hbo, _⟩ := internalView_member_inv hmv
        rw [hbo] at hb0
        obtain ⟨hty⟩ := envWfA_memberBody hE r src b0 hsrc hb0
        exact constsArityA_view (hasTyA_constsArity hty)
      rw [NeutralCodes.valueEq_eq (denote_delta (ls := ls) hmv hb0 htm _ ν ρ),
        NeutralCodes.valueEq_eq (denote_delta (ls := ls') hmv hb0 htm _ μ σ)]
      have hrel' :
          R (EnvironmentEval.denote (EnvironmentTelescopeInsertion.internalView E)
              (EnvironmentTelescopeInsertion.hook E neutralFamilySyntax) ν ρ
              (instantiateLevelsA ls' b0))
            (EnvironmentEval.denote (EnvironmentTelescopeInsertion.internalView E)
              (EnvironmentTelescopeInsertion.hook E neutralFamilySyntax) μ σ
              (instantiateLevelsA ls' b0)) := by
        have hr' :
            R (EnvironmentEval.denote (EnvironmentTelescopeInsertion.internalView E)
                (EnvironmentTelescopeInsertion.hook E neutralFamilySyntax) ν ρ
                (.const r ls'))
              (EnvironmentEval.denote (EnvironmentTelescopeInsertion.internalView E)
                (EnvironmentTelescopeInsertion.hook E neutralFamilySyntax) μ σ
                (.const r ls')) := hrel
        rwa [NeutralCodes.valueEq_eq (denote_delta (ls := ls') hmv hb0 htm _ ν ρ),
          NeutralCodes.valueEq_eq (denote_delta (ls := ls') hmv hb0 htm _ μ σ)] at hr'
      rw [NeutralCodes.valueEq_eq (denote_instLevel_agree hloc heqN hbar harB h)]
      exact hrel'

end Rcic.Declarative.Ann.LR3.EnvironmentPorts
