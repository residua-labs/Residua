import rcic.RcicAnnLR3FunctionEval

/-!
# Finite environment-aware interpretation of transparent definitions

Finite translation trees unfold transparent members from the actual environment.
A cut is interpreted by a closed native term with exactly the bottom observation;
thus partial body information is retained without a normalization assumption.
All evaluation of the resulting native terms is the inherited `denI`.

Definitions unfold with level instantiation, and axioms, theorems and opaque
members are neutral constants. Family/constructor/recursor native meanings are
an explicit argument. The default hooks are neutral and are not a family-code
producer. Exact delta and its paired constructor arm are supplied for this new
evaluator, not for the inherited fixture evaluator.

The constant-free agreement theorem covers terms without constants or literals:
literals hide the constants of `natExpandA` and are interpreted through that
expansion. General paired substitution and family membership are still open.
No admission, Fundamental, reflection or universe-decoder premise is hidden in
the evaluator or delta supplier. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.EnvironmentEval

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements PairedStatements

/-- A closed native expression whose only compact observation is bottom. -/
def cutTerm : Expr Nat := .app (.sort .zero) (.sort .zero)

theorem cutTerm_only_bottom {ρ : EnvI} {c : CptI}
    (h : denI ρ cutTerm c) : c = .bot := by
  rcases approxI_app_inv h with hc | ⟨g, s, _, hf, _, _⟩ | ⟨r, args, u, _, hf, _⟩
  · exact hc
  · rcases approxI_sort_inv hf with h | h <;> cases h
  · rcases approxI_sort_inv hf with h | h <;> cases h

theorem cutTerm_denotes_bottom (ρ : EnvI) : ValueEq (denI ρ cutTerm) bottom :=
  fun _ => ⟨cutTerm_only_bottom, fun h => by cases h; exact .bot _ _⟩

/-- The family hooks are explicit native syntax, not alleged semantic supplies.
Only inductive, constructor and recursor classes consult this argument. -/
abbrev FamilySyntax := Valuation → Nat → List Level → CheckedMemberA → Expr Nat

def neutralFamilySyntax : FamilySyntax := fun _ r _ _ => .const r []

def rigidTerm (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation)
    (r : Nat) (ls : List Level) : Expr Nat :=
  match E.members r with
  | none => .const r []
  | some m =>
      match m.mclass with
      | .inductiveM | .constructorM | .recursorM => F ν r ls m
      | _ => .const r []

def definitionBody (E : ResolvedEnvA) (r : Nat) (ls : List Level) : Option ExprA :=
  match E.members r with
  | none => none
  | some m =>
      if transparent m.mclass then m.bodyA.map (instantiateLevelsA ls) else none

theorem definitionBody_of_member {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} {b : ExprA} (hm : E.members r = some m)
    (hb : m.bodyA = some b) (ht : transparent m.mclass = true) :
    definitionBody E r ls = some (instantiateLevelsA ls b) := by
  simp [definitionBody, hm, hb, ht]

/-- Positive, finite compilation evidence. Cuts are available at every source
subterm, so a complete transparent unfolding is never required. -/
inductive Translation (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation) :
    ExprA → Expr Nat → Prop
  | cut (e : ExprA) : Translation E F ν e cutTerm
  | bvar (i : Nat) : Translation E F ν (.bvar i) (.bvar i)
  | sort (l : Level) : Translation E F ν (.sort l) (sortTerm (eval ν l))
  | constBody {r : Nat} {ls : List Level} {b : ExprA} {t : Expr Nat}
      (body : definitionBody E r ls = some b)
      (translated : Translation E F ν b t) : Translation E F ν (.const r ls) t
  | constRigid {r : Nat} {ls : List Level}
      (rigid : definitionBody E r ls = none) :
      Translation E F ν (.const r ls) (rigidTerm E F ν r ls)
  | app {f a : ExprA} {f' a' : Expr Nat}
      (hf : Translation E F ν f f') (ha : Translation E F ν a a') :
      Translation E F ν (.app f a) (.app f' a')
  | lam {A b : ExprA} {u : Level} {A' b' : Expr Nat}
      (hA : Translation E F ν A A') (hb : Translation E F ν b b') :
      Translation E F ν (.lam A u b) (.lam A' b')
  | pi {A B : ExprA} {u v : Level} {A' B' : Expr Nat}
      (hA : Translation E F ν A A') (hB : Translation E F ν B B') :
      Translation E F ν (.pi A u B v)
        (taggedTerm (eval ν (.imax u v)) (.pi A' B'))
  | letE {A v b : ExprA} {A' v' b' : Expr Nat}
      (hA : Translation E F ν A A') (hv : Translation E F ν v v')
      (hb : Translation E F ν b b') :
      Translation E F ν (.letE A v b) (.letE A' v' b')
  | lit {n : Nat} {t : Expr Nat} (expanded : Translation E F ν (natExpandA n) t) :
      Translation E F ν (.lit n) t

def denote (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (e : ExprA) : Value :=
  fun c => ∃ t, Translation E F ν e t ∧ denI ρ t c

theorem denote_bot (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (e : ExprA) : denote E F ν ρ e .bot :=
  ⟨cutTerm, .cut e, .bot ρ cutTerm⟩

theorem denote_delta {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} {b : ExprA} (hm : E.members r = some m)
    (hb : m.bodyA = some b) (ht : transparent m.mclass = true)
    (F : FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (denote E F ν ρ (.const r ls))
      (denote E F ν ρ (instantiateLevelsA ls b)) := by
  have hd := definitionBody_of_member (ls := ls) hm hb ht
  intro c
  constructor
  · rintro ⟨t, htr, hc⟩
    cases htr with
    | cut =>
        have he := cutTerm_only_bottom hc
        cases he
        exact denote_bot E F ν ρ _
    | constBody hbody htr =>
        rw [hd] at hbody
        cases hbody
        exact ⟨_, htr, hc⟩
    | constRigid hr => rw [hd] at hr; cases hr
  · rintro ⟨t, htr, hc⟩
    exact ⟨t, .constBody hd htr, hc⟩

theorem denote_literal (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation)
    (ρ : EnvI) (n : Nat) :
    ValueEq (denote E F ν ρ (.lit n)) (denote E F ν ρ (natExpandA n)) := by
  intro c
  constructor
  · rintro ⟨t, ht, hc⟩
    cases ht with
    | cut =>
        have he := cutTerm_only_bottom hc
        cases he
        exact denote_bot E F ν ρ _
    | lit hx => exact ⟨_, hx, hc⟩
  · rintro ⟨t, ht, hc⟩
    exact ⟨t, .lit ht, hc⟩

theorem denote_rigid {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    (hr : definitionBody E r ls = none) (F : FamilySyntax)
    (ν : Valuation) (ρ : EnvI) :
    ValueEq (denote E F ν ρ (.const r ls)) (denI ρ (rigidTerm E F ν r ls)) := by
  intro c
  constructor
  · rintro ⟨t, ht, hc⟩
    cases ht with
    | cut =>
        have he := cutTerm_only_bottom hc
        cases he
        exact .bot _ _
    | constBody hb _ => rw [hr] at hb; cases hb
    | constRigid => exact hc
  · intro hc
    exact ⟨_, .constRigid hr, hc⟩

theorem denote_axiom {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (hm : E.members r = some m) (hc : m.mclass = .axiomM)
    (F : FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (denote E F ν ρ (.const r ls)) (NeutralPER.neutralAtom r) := by
  have hr : definitionBody E r ls = none := by simp [definitionBody, hm, hc, transparent]
  have ht : rigidTerm E F ν r ls = .const r [] := by simp [rigidTerm, hm, hc]
  exact (denote_rigid hr F ν ρ).trans
    (by rw [ht]; exact FunctionEval.constant_environment ρ EnvI.bot r [])

theorem denote_opaque {E : ResolvedEnvA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} (hm : E.members r = some m) (hc : m.mclass = .opaqueM)
    (F : FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ValueEq (denote E F ν ρ (.const r ls)) (NeutralPER.neutralAtom r) := by
  have hr : definitionBody E r ls = none := by simp [definitionBody, hm, hc, transparent]
  have ht : rigidTerm E F ν r ls = .const r [] := by simp [rigidTerm, hm, hc]
  exact (denote_rigid hr F ν ρ).trans
    (by rw [ht]; exact FunctionEval.constant_environment ρ EnvI.bot r [])

/-- Native approximation inclusion, uniformly in the local environment. -/
def NativeBelow (s t : Expr Nat) : Prop :=
  ∀ ρ c, denI ρ s c → denI ρ t c

theorem NativeBelow.refl (s : Expr Nat) : NativeBelow s s := fun _ _ h => h

theorem NativeBelow.cut (t : Expr Nat) : NativeBelow cutTerm t := by
  intro ρ c h
  have he := cutTerm_only_bottom h
  cases he
  exact .bot _ _

theorem NativeBelow.app {f g a b : Expr Nat} (hf : NativeBelow f g)
    (ha : NativeBelow a b) : NativeBelow (.app f a) (.app g b) := by
  intro ρ c h
  cases h with
  | bot => exact .bot _ _
  | app hfg hs harg => exact .app (hf _ _ hfg) hs (fun u hu => ha _ _ (harg u hu))
  | appSpine hfg harg => exact .appSpine (hf _ _ hfg) (ha _ _ harg)

theorem NativeBelow.lam {A A' b b' : Expr Nat} (hb : NativeBelow b b') :
    NativeBelow (.lam A b) (.lam A' b') := by
  intro ρ c h
  cases h with
  | bot => exact .bot _ _
  | lam hbody => exact .lam (fun s hs => hb _ _ (hbody s hs))

theorem NativeBelow.pi {A A' B B' : Expr Nat} (hA : NativeBelow A A')
    (hB : NativeBelow B B') : NativeBelow (.pi A B) (.pi A' B') := by
  intro ρ c h
  cases h with
  | bot => exact .bot _ _
  | pi ha hb => exact .pi (hA _ _ ha) (fun s hs => hB _ _ (hb s hs))

theorem NativeBelow.tagged {s t : Expr Nat} (k : Option Nat) (h : NativeBelow s t) :
    NativeBelow (taggedTerm k s) (taggedTerm k t) :=
  NativeBelow.app (NativeBelow.refl _) h

theorem NativeBelow.letE {A A' v v' b b' : Expr Nat}
    (hv : NativeBelow v v') (hb : NativeBelow b b') :
    NativeBelow (.letE A v b) (.letE A' v' b') := by
  intro ρ c h
  cases h with
  | bot => exact .bot _ _
  | letE hbody => exact .letE ((NativeBelow.app (NativeBelow.lam hb) hv) _ _ hbody)

/-- Constants in literal expansions count as constants of the fragment. -/
def CoreFree : ExprA → Prop
  | .bvar _ | .sort _ => True
  | .const _ _ | .lit _ => False
  | .app f a => CoreFree f ∧ CoreFree a
  | .lam A _ b => CoreFree A ∧ CoreFree b
  | .pi A _ B _ => CoreFree A ∧ CoreFree B
  | .letE A v b => CoreFree A ∧ CoreFree v ∧ CoreFree b

theorem translation_core_below {E : ResolvedEnvA} {F : FamilySyntax} {ν : Valuation}
    {e : ExprA} {t : Expr Nat} (ht : Translation E F ν e t) :
    CoreFree e → NativeBelow t (UnitModel.translate ν e) := by
  induction ht with
  | cut e => exact fun _ => NativeBelow.cut _
  | bvar i => exact fun _ => NativeBelow.refl _
  | sort l => exact fun _ => NativeBelow.refl _
  | constBody _ _ _ => exact fun h => False.elim h
  | constRigid _ => exact fun h => False.elim h
  | app _ _ ihf iha => exact fun h => NativeBelow.app (ihf h.1) (iha h.2)
  | lam _ _ _ ihb => exact fun h => NativeBelow.lam (ihb h.2)
  | pi _ _ ihA ihB => exact fun h => NativeBelow.tagged _ (NativeBelow.pi (ihA h.1) (ihB h.2))
  | letE _ _ _ _ ihv ihb => exact fun h => NativeBelow.letE (ihv h.2.1) (ihb h.2.2)
  | lit _ _ => exact fun h => False.elim h

theorem core_translation (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation)
    {e : ExprA} (he : CoreFree e) : Translation E F ν e (UnitModel.translate ν e) := by
  induction e with
  | bvar i => exact .bvar i
  | sort l => exact .sort l
  | const r ls => exact False.elim he
  | app f a ihf iha => exact .app (ihf he.1) (iha he.2)
  | lam A u b ihA ihb => exact .lam (ihA he.1) (ihb he.2)
  | pi A u B v ihA ihB => exact .pi (ihA he.1) (ihB he.2)
  | letE A v b ihA ihv ihb => exact .letE (ihA he.1) (ihv he.2.1) (ihb he.2.2)
  | lit n => exact False.elim he

theorem denote_core (E : ResolvedEnvA) (F : FamilySyntax) (ν : Valuation) (ρ : EnvI)
    {e : ExprA} (he : CoreFree e) :
    ValueEq (denote E F ν ρ e) (UnitModel.denote ν ρ e) := by
  intro c
  constructor
  · rintro ⟨t, ht, hc⟩
    exact translation_core_below ht he ρ c hc
  · intro hc
    exact ⟨_, core_translation E F ν he, hc⟩

def annSemantics (C : CodeSystem) (E : ResolvedEnvA) (F : FamilySyntax) : AnnSemantics where
  toCodeSystem := C
  image := fun ν _ ρ e => denote E F ν ρ e
  sort_image := by
    intro ν Γ ρ l
    change denote E F ν ρ (.sort l) = universeValue (eval ν l)
    rw [NeutralCodes.valueEq_eq (denote_core E F ν ρ (e := .sort l) True.intro)]
    exact (FunctionEval.annSemantics C).sort_image ν Γ ρ l

/-- Exact constructor contract for the new environment-aware image. Only
the stipulated body-typing IH is consumed. -/
theorem conv_delta_supplied (C : CodeSystem) (E : ResolvedEnvA) (F : FamilySyntax)
    (I : IotaIfaceA) (n : Nat) : PairedArms.Conv_delta (annSemantics C E F) E I n := by
  intro Γ r ls m b hm hb ht _ _ _ ih hΓ ν μ ρ σ hν hρ
  obtain ⟨k, R, S, hcodes, hbody⟩ := ih hΓ ν μ ρ σ hν hρ
  refine ⟨k, R, S, hcodes, ?_⟩
  change R (denote E F ν ρ (.const r ls))
    (denote E F μ σ (instantiateLevelsA ls b))
  rw [NeutralCodes.valueEq_eq (denote_delta hm hb ht F ν ρ)]
  exact hbody

/-- A definition's typing follows from its own body typing in this image.
This is not a supplier of the general member telescope or `Ty_const`. -/
theorem definition_typing (C : CodeSystem) {E : ResolvedEnvA} (F : FamilySyntax)
    {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {r : Nat} {ls : List Level}
    {m : CheckedMemberA} {b : ExprA} (hm : E.members r = some m)
    (hb : m.bodyA = some b) (ht : transparent m.mclass = true)
    (ih : PairedTyGoal (annSemantics C E F) E I n Γ
      (instantiateLevelsA ls b) (instantiateLevelsA ls m.mtypeA)) :
    PairedTyGoal (annSemantics C E F) E I n Γ
      (.const r ls) (instantiateLevelsA ls m.mtypeA) := by
  intro hΓ ν μ ρ σ hν hρ
  obtain ⟨k, R, S, hcodes, hbody⟩ := ih hΓ ν μ ρ σ hν hρ
  refine ⟨k, R, S, hcodes, ?_⟩
  change R (denote E F ν ρ (.const r ls)) (denote E F μ σ (.const r ls))
  rw [NeutralCodes.valueEq_eq (denote_delta hm hb ht F ν ρ),
    NeutralCodes.valueEq_eq (denote_delta hm hb ht F μ σ)]
  exact hbody

end Rcic.Declarative.Ann.LR3.EnvironmentEval
