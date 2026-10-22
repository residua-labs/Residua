import rcic.RcicAnnLR3UnifiedPi
import rcic.RcicAnnLR3PairedArms

/-!
# Concrete native function evaluation and an evaluator-specific beta arm

Native lambda values are identified with the complete finite graph of
their bodies. Application to every raw argument is exactly evaluation of
the body in the extended environment. The inherited approximation and
translation lemmas then supply binary application/lambda laws, beta
equations, and eta at every bottom-containing legal argument.

The bottom premise for native eta is explicit: a native variable always
observes bottom. Every member of the existing NeutralCodes algebra is
proved to contain bottom, so the premise is supplied for those domains.
No equality between an unapplied neutral value and its lambda expansion
is asserted; eta is proved in the legal-domain function PER.

`annSemantics` attaches the actual inherited `UnitModel.denote` evaluator
to a supplied code algebra, deriving its sort equation. `conv_beta_supplied`
is the exact source arm for that concrete evaluator and consumes only its
specified child induction hypothesis. It is not an arm for a different
unspecified evaluator. The old descriptor grammar still has no Pi code;
Pi carrier identification, the other source function arms, and a unified
dependent code producer are not inferred from these operational laws.
No new paired substitution, lookup, or lifting interface is introduced.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.FunctionEval

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open UnitModel TypedPER TypedStatements PairedStatements

/-- The inherited native lambda already contains the complete graph of
its body on all raw arguments. This is a value equation, not a typing
certificate stored in a newly defined lambda operation. -/
theorem native_lambda_graph (ρ : EnvI) (A body : Expr Nat) :
    ValueEq (denI ρ (.lam A body))
      (UnifiedPi.legalGraph (fun _ _ => True)
        (fun x => denI (EnvI.cons x ρ) body)) := by
  intro c
  constructor
  · intro hc
    rcases approxI_lam_inv hc with hc | ⟨g, hc, hbody⟩
    · exact Or.inl hc
    · refine Or.inr ⟨g, hc, ?_⟩
      intro s hs x _ hx
      apply approxI_mono_env ?_ (hbody s hs)
      intro i u hu
      cases i with
      | zero => exact hx u hu
      | succ i => exact hu
  · intro hc
    rcases hc with hc | ⟨g, hc, hbody⟩
    · subst c
      exact ApproxI.bot ρ (.lam A body)
    · subst c
      exact ApproxI.lam (fun s hs =>
        hbody s hs (demand s.1) True.intro (fun _ hu => hu))

/-- Lambda application is exact for every raw argument value. It does
not restrict the argument to a selected finite approximation. -/
theorem native_lambda_application (ρ : EnvI) (A body : Expr Nat) (x : Value) :
    ValueEq (NeutralPi.applyValue (denI ρ (.lam A body)) x)
      (denI (EnvI.cons x ρ) body) :=
  (NeutralPi.applyValue_congr (native_lambda_graph ρ A body) (ValueEq.refl x)).trans
    (UnifiedPi.native_body_graph_application (fun _ _ => True) ρ body True.intro)

/-- The actual native lambdas satisfy the full binary function clause
when their bodies satisfy its pointwise clause at related arguments. -/
theorem native_lambdas_related {D : Relation} {C : Value → Relation}
    {ρ σ : EnvI} {A A' body body' : Expr Nat}
    (hbody : ∀ x y : Value, D x y →
      C x (denI (EnvI.cons x ρ) body) (denI (EnvI.cons y σ) body')) :
    FunctionPER NeutralPi.applyValue D C
      (denI ρ (.lam A body)) (denI σ (.lam A' body')) := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq (native_lambda_application ρ A body x),
    NeutralCodes.valueEq_eq (native_lambda_application σ A' body' y)]
  exact hbody x y hxy

theorem native_applications_related {D : Relation} {C : Value → Relation}
    {ρ σ : EnvI} {f g a b : Expr Nat}
    (hfg : FunctionPER NeutralPi.applyValue D C (denI ρ f) (denI σ g))
    (hab : D (denI ρ a) (denI σ b)) :
    C (denI ρ a) (denI ρ (.app f a)) (denI σ (.app g b)) := by
  have h := hfg _ _ hab
  rw [NeutralCodes.valueEq_eq (NeutralPi.applyValue_denI ρ f a),
    NeutralCodes.valueEq_eq (NeutralPi.applyValue_denI σ g b)] at h
  exact h

/-- Both beta computations are inherited value equations; no relation
between the two environments is needed to prove the computations. -/
theorem native_beta_equations (ρ σ : EnvI) (A body arg A' body' arg' : Expr Nat) :
    ValueEq (denI ρ (.app (.lam A body) arg)) (denI ρ (instantiate0 arg body)) ∧
    ValueEq (denI σ (.app (.lam A' body') arg'))
      (denI σ (instantiate0 arg' body')) :=
  ⟨approxI_beta ρ A body arg, approxI_beta σ A' body' arg'⟩

theorem native_beta_related {R : Relation} {ρ σ : EnvI}
    {A body arg A' body' arg' : Expr Nat}
    (h : R (denI ρ (instantiate0 arg body)) (denI σ (instantiate0 arg' body'))) :
    R (denI ρ (.app (.lam A body) arg)) (denI σ (.app (.lam A' body') arg')) := by
  have hleft : ValueEq (denI ρ (.app (.lam A body) arg))
      (denI ρ (instantiate0 arg body)) := approxI_beta ρ A body arg
  have hright : ValueEq (denI σ (.app (.lam A' body') arg'))
      (denI σ (instantiate0 arg' body')) := approxI_beta σ A' body' arg'
  rw [NeutralCodes.valueEq_eq hleft, NeutralCodes.valueEq_eq hright]
  exact h

/-- Native eta applications agree at all arguments containing bottom.
The only lifting step is the inherited `approxI_cons_lift0_iff`. -/
theorem native_eta_application (ρ : EnvI) (A f : Expr Nat) (x : Value)
    (hx : x .bot) :
    ValueEq
      (NeutralPi.applyValue (denI ρ (.lam A (.app (lift 0 1 f) (.bvar 0)))) x)
      (NeutralPi.applyValue (denI ρ f) x) := by
  apply (native_lambda_application ρ A (.app (lift 0 1 f) (.bvar 0)) x).trans
  apply (NeutralPi.applyValue_denI (EnvI.cons x ρ) (lift 0 1 f) (.bvar 0)).symm.trans
  apply NeutralPi.applyValue_congr
  · exact fun c => approxI_cons_lift0_iff ρ x f c
  · intro c
    constructor
    · intro hc
      rcases approxI_bvar_inv hc with hc | hc
      · subst c
        exact hx
      · exact hc
    · exact fun hc => ApproxI.bvar hc

/-- Native eta respects a binary function relation on the whole legal
domain. The domain's bottom property is stated where it is consumed. -/
theorem native_eta_related {D : Relation} (hD : Laws D)
    (hbot : ∀ x : Value, Member D x → x .bot)
    {C : Value → Relation} {ρ σ : EnvI} {A f g : Expr Nat}
    (hfg : FunctionPER NeutralPi.applyValue D C (denI ρ f) (denI σ g)) :
    FunctionPER NeutralPi.applyValue D C
      (denI ρ (.lam A (.app (lift 0 1 f) (.bvar 0)))) (denI σ g) := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq
    (native_eta_application ρ A f x (hbot x (left_member hD hxy)))]
  exact hfg x y hxy

theorem native_etas_related {D : Relation} (hD : Laws D)
    (hbot : ∀ x : Value, Member D x → x .bot)
    {C : Value → Relation} {ρ σ : EnvI} {A A' f g : Expr Nat}
    (hfg : FunctionPER NeutralPi.applyValue D C (denI ρ f) (denI σ g)) :
    FunctionPER NeutralPi.applyValue D C
      (denI ρ (.lam A (.app (lift 0 1 f) (.bvar 0))))
      (denI σ (.lam A' (.app (lift 0 1 g) (.bvar 0)))) := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq
      (native_eta_application ρ A f x (hbot x (left_member hD hxy))),
    NeutralCodes.valueEq_eq
      (native_eta_application σ A' g y (hbot y (right_member hD hxy)))]
  exact hfg x y hxy

theorem reify_bot (d : NeutralCodes.Descriptor) : NeutralCodes.reify d .bot := by
  cases d with
  | neutralType k name => exact Or.inl rfl
  | proof P => exact Or.inl rfl
  | univ k => exact ApproxI.bot EnvI.bot (sortTerm k)

theorem neutralProof_member_bot {P : Prop} {x : Value}
    (hx : Member (NeutralPER.ProofPER NeutralCodes.Neutral P) x) : x .bot := by
  rcases hx.1 with hx | ⟨name, hx⟩
  · exact (hx.2 .bot).mpr (ApproxI.bot EnvI.bot unitTerm)
  · exact (hx .bot).mpr (ApproxI.bot EnvI.bot (.const name []))

/-- Bottom containment is constructed for every existing descriptor,
including universe elements obtained through actual decoding. -/
theorem el_member_bot (d : NeutralCodes.Descriptor) {x : Value}
    (hx : Member (NeutralCodes.El d) x) : x .bot := by
  cases d with
  | neutralType k name => exact neutralProof_member_bot hx
  | proof P => exact neutralProof_member_bot hx
  | univ k =>
      obtain ⟨e, f, _, _, he, _⟩ := hx
      exact (he .bot).mpr (reify_bot e)

theorem code_member_bot {k : Option Nat} {V : Value} {D : Relation}
    (hcode : NeutralCodes.Code k V D) {x : Value} (hx : Member D x) : x .bot := by
  obtain ⟨d, _, _, hD⟩ := hcode
  exact el_member_bot d ((hD x x).mp hx)

/-- No extra bottom certificate is required at a domain coded by the
current concrete descriptor algebra. Pi code closure is not asserted. -/
theorem native_eta_at_code {k : Option Nat} {V : Value} {D : Relation}
    (hcode : NeutralCodes.Code k V D)
    {C : Value → Relation} {ρ σ : EnvI} {A f g : Expr Nat}
    (hfg : FunctionPER NeutralPi.applyValue D C (denI ρ f) (denI σ g)) :
    FunctionPER NeutralPi.applyValue D C
      (denI ρ (.lam A (.app (lift 0 1 f) (.bvar 0)))) (denI σ g) :=
  native_eta_related (NeutralCodes.code_lawful hcode)
    (fun _ hx => code_member_bot hcode hx) hfg

theorem denote_lambda_application (ν : Valuation) (ρ : EnvI)
    (A body : ExprA) (u : Level) (x : Value) :
    ValueEq (NeutralPi.applyValue (UnitModel.denote ν ρ (.lam A u body)) x)
      (UnitModel.denote ν (EnvI.cons x ρ) body) :=
  native_lambda_application ρ (translate ν A) (translate ν body) x

theorem denote_lambdas_related {D : Relation} {C : Value → Relation}
    {ν μ : Valuation} {ρ σ : EnvI} {A A' body body' : ExprA} {u u' : Level}
    (hbody : ∀ x y : Value, D x y →
      C x (UnitModel.denote ν (EnvI.cons x ρ) body) (UnitModel.denote μ (EnvI.cons y σ) body')) :
    FunctionPER NeutralPi.applyValue D C
      (UnitModel.denote ν ρ (.lam A u body)) (UnitModel.denote μ σ (.lam A' u' body')) :=
  native_lambdas_related hbody

theorem denote_applications_related {D : Relation} {C : Value → Relation}
    {ν μ : Valuation} {ρ σ : EnvI} {f g a b : ExprA}
    (hfg : FunctionPER NeutralPi.applyValue D C (UnitModel.denote ν ρ f) (UnitModel.denote μ σ g))
    (hab : D (UnitModel.denote ν ρ a) (UnitModel.denote μ σ b)) :
    C (UnitModel.denote ν ρ a) (UnitModel.denote ν ρ (.app f a)) (UnitModel.denote μ σ (.app g b)) :=
  native_applications_related hfg hab

theorem denote_beta_equations (ν μ : Valuation) (ρ σ : EnvI)
    (A body arg A' body' arg' : ExprA) (u u' : Level) :
    ValueEq (UnitModel.denote ν ρ (.app (.lam A u body) arg))
      (UnitModel.denote ν ρ (instantiate0A arg body)) ∧
    ValueEq (UnitModel.denote μ σ (.app (.lam A' u' body') arg'))
      (UnitModel.denote μ σ (instantiate0A arg' body')) :=
  ⟨beta_sound ν ρ A body arg u, beta_sound μ σ A' body' arg' u'⟩

theorem denote_beta_related {R : Relation} {ν μ : Valuation} {ρ σ : EnvI}
    {A body arg A' body' arg' : ExprA} {u u' : Level}
    (h : R (UnitModel.denote ν ρ (instantiate0A arg body))
      (UnitModel.denote μ σ (instantiate0A arg' body'))) :
    R (UnitModel.denote ν ρ (.app (.lam A u body) arg))
      (UnitModel.denote μ σ (.app (.lam A' u' body') arg')) := by
  rw [NeutralCodes.valueEq_eq (beta_sound ν ρ A body arg u),
    NeutralCodes.valueEq_eq (beta_sound μ σ A' body' arg' u')]
  exact h

theorem denote_eta_application (ν : Valuation) (ρ : EnvI)
    (A f : ExprA) (u : Level) (x : Value) (hx : x .bot) :
    ValueEq
      (NeutralPi.applyValue (UnitModel.denote ν ρ (.lam A u (.app (liftA 0 1 f) (.bvar 0)))) x)
      (NeutralPi.applyValue (UnitModel.denote ν ρ f) x) := by
  simpa only [UnitModel.denote, translate, translate_lift] using
    native_eta_application ρ (translate ν A) (translate ν f) x hx

theorem denote_eta_related {D : Relation} (hD : Laws D)
    (hbot : ∀ x : Value, Member D x → x .bot)
    {C : Value → Relation} {ν μ : Valuation} {ρ σ : EnvI}
    {A f g : ExprA} {u : Level}
    (hfg : FunctionPER NeutralPi.applyValue D C (UnitModel.denote ν ρ f) (UnitModel.denote μ σ g)) :
    FunctionPER NeutralPi.applyValue D C
      (UnitModel.denote ν ρ (.lam A u (.app (liftA 0 1 f) (.bvar 0)))) (UnitModel.denote μ σ g) := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq
    (denote_eta_application ν ρ A f u x (hbot x (left_member hD hxy)))]
  exact hfg x y hxy

theorem constant_environment (ρ σ : EnvI) (r : Nat) (ls : List Level) :
    ValueEq (denI ρ (.const r ls)) (denI σ (.const r ls)) := by
  intro c
  constructor
  · intro hc
    rcases approxI_const_inv hc with hc | hc
    · subst c
      exact ApproxI.bot σ (.const r ls)
    · subst c
      exact ApproxI.const σ r ls
  · intro hc
    rcases approxI_const_inv hc with hc | hc
    · subst c
      exact ApproxI.bot ρ (.const r ls)
    · subst c
      exact ApproxI.const ρ r ls

theorem sortTerm_environment (ρ σ : EnvI) (k : Option Nat) :
    ValueEq (denI ρ (sortTerm k)) (denI σ (sortTerm k)) :=
  approxI_app_rel
    (approxI_app_rel (constant_environment ρ σ 10 [])
      (constant_environment ρ σ (levelRef (k.map Nat.succ)) []))
    (approxI_app_rel (constant_environment ρ σ 11 [])
      (constant_environment ρ σ (levelRef k) []))

/-- A concrete evaluator attachment, independent of typing derivations.
Its constant interpretation remains the inherited scoped fixture's map;
this definition does not claim admitted-member soundness. -/
def annSemantics (C : CodeSystem) : AnnSemantics where
  toCodeSystem := C
  image := fun ν _ ρ e => UnitModel.denote ν ρ e
  sort_image := by
    intro ν _ ρ l
    exact NeutralCodes.valueEq_eq (sortTerm_environment ρ EnvI.bot (eval ν l))

/-- An actual exact paired beta arm for the evaluator above. The code
and cross-world relation come from the stipulated contractum child IH;
the left beta computation is supplied by the inherited evaluator. -/
theorem conv_beta_supplied (C : CodeSystem) (E : ResolvedEnvA) (I : IotaIfaceA)
    (n : Nat) : PairedArms.Conv_beta (annSemantics C) E I n := by
  intro Γ A u body arg B _ _ _ _ _ _ _ ih_red hΓ ν μ ρ σ hν hρ
  obtain ⟨k, R, S, hc, hr⟩ := ih_red hΓ ν μ ρ σ hν hρ
  refine ⟨k, R, S, hc, ?_⟩
  change R (UnitModel.denote ν ρ (.app (.lam A u body) arg))
    (UnitModel.denote μ σ (instantiate0A arg body))
  rw [NeutralCodes.valueEq_eq (beta_sound ν ρ A body arg u)]
  exact hr

/-- The beta arm specializes to the existing concrete code algebra.
This specialization does not enlarge that algebra's descriptor grammar. -/
theorem neutralCodes_conv_beta_supplied (E : ResolvedEnvA) (I : IotaIfaceA)
    (n : Nat) : PairedArms.Conv_beta (annSemantics NeutralCodes.codeSystem) E I n :=
  conv_beta_supplied NeutralCodes.codeSystem E I n

end Rcic.Declarative.Ann.LR3.FunctionEval
