import rcic.RcicAnnLR3IotaClosedTerms

/-!
# The lifting law of the EnvironmentEval image

For a view `V` whose transparent bodies are closed (`DefinitionBodiesClosed V`,
a consequence of source admission, `definitionBodiesClosed_of_envWfA`) and a family
hook fixed by lifting (`HookLiftFixed V H`, supplied for the recursor hook by
`iotaHook_liftFixed`):

* `translation_lift`: every finite translation of `e` lifts to one of `liftA c 1 e`;
* `translation_unlift`: every finite translation of `liftA c 1 e` **is** the lift of
  a translation of `e` (no representative is chosen; the witness is built by
  induction on the translation derivation);
* `denote_lift`: `denote (insert ρ c S) (liftA c 1 e) = denote ρ e`, and the iterated
  `denote_liftN` over any pushed list of raw values.

These are evaluator laws only, used for function-recursive recursor calls. They
are not a source variable/lifting arm. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.IotaRecursor

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER
open EnvironmentEval (FamilySyntax Translation cutTerm)
open EnvironmentPortConditions (HookLiftFixed DefinitionBodiesClosed)

section Lift

variable {V : ResolvedEnvA} {H : FamilySyntax} {ν : Valuation}

theorem translation_lift (hbody : DefinitionBodiesClosed V) (hhook : HookLiftFixed V H)
    {e : ExprA} {t : Expr Nat} (h : Translation V H ν e t) :
    ∀ c, Translation V H ν (liftA c 1 e) (lift c 1 t) := by
  induction h with
  | cut e => intro c; exact .cut _
  | bvar i =>
      intro c
      simp only [liftA, lift]
      split <;> exact .bvar _
  | sort l => intro c; exact .sort l
  | constBody hb _ ih =>
      intro c
      have h' := ih c
      rw [hbody _ _ _ hb c] at h'
      exact .constBody hb h'
  | constRigid hr =>
      intro c
      rw [EnvironmentPortConditions.rigidTerm_liftFixed hhook]
      exact .constRigid hr
  | app _ _ ihf iha => intro c; exact .app (ihf c) (iha c)
  | lam _ _ ihA ihb => intro c; exact .lam (ihA c) (ihb (c + 1))
  | pi _ _ ihA ihB => intro c; exact .pi (ihA c) (ihB (c + 1))
  | letE _ _ _ ihA ihv ihb => intro c; exact .letE (ihA c) (ihv c) (ihb (c + 1))
  | lit _ ih =>
      intro c
      have h' := ih c
      rw [liftA_natExpandA_closed] at h'
      exact .lit h'

theorem translation_unlift (hbody : DefinitionBodiesClosed V) (hhook : HookLiftFixed V H)
    {e' : ExprA} {t' : Expr Nat} (h : Translation V H ν e' t') :
    ∀ (e : ExprA) (c : Nat), e' = liftA c 1 e →
      ∃ t, Translation V H ν e t ∧ t' = lift c 1 t := by
  induction h with
  | cut _ => intro e c _; exact ⟨cutTerm, .cut e, rfl⟩
  | bvar i =>
      intro e c heq
      cases e with
      | bvar j =>
          refine ⟨.bvar j, .bvar j, ?_⟩
          simp only [liftA] at heq
          simp only [lift]
          split <;> rename_i hj <;> simp only [hj, if_true, if_false] at heq <;>
            (injection heq with heq; rw [heq])
      | _ => simp [liftA] at heq
  | sort l =>
      intro e c heq
      cases e with
      | sort l' =>
          simp only [liftA, ExprA.sort.injEq] at heq
          subst heq
          exact ⟨_, .sort l, rfl⟩
      | bvar j => simp only [liftA] at heq; split at heq <;> simp at heq
      | _ => simp [liftA] at heq
  | @constBody r ls b t hb _ ih =>
      intro e c heq
      cases e with
      | const r' ls' =>
          simp only [liftA, ExprA.const.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          obtain ⟨t0, ht0, rfl⟩ := ih b c (hbody _ _ _ hb c).symm
          exact ⟨t0, .constBody hb ht0, rfl⟩
      | bvar j => simp only [liftA] at heq; split at heq <;> simp at heq
      | _ => simp [liftA] at heq
  | @constRigid r ls hr =>
      intro e c heq
      cases e with
      | const r' ls' =>
          simp only [liftA, ExprA.const.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact ⟨_, .constRigid hr,
            (EnvironmentPortConditions.rigidTerm_liftFixed hhook ν r ls c).symm⟩
      | bvar j => simp only [liftA] at heq; split at heq <;> simp at heq
      | _ => simp [liftA] at heq
  | app _ _ ihf iha =>
      intro e c heq
      cases e with
      | app f a =>
          simp only [liftA, ExprA.app.injEq] at heq
          obtain ⟨tf, htf, rfl⟩ := ihf f c heq.1
          obtain ⟨ta, hta, rfl⟩ := iha a c heq.2
          exact ⟨.app tf ta, .app htf hta, rfl⟩
      | bvar j => simp only [liftA] at heq; split at heq <;> simp at heq
      | _ => simp [liftA] at heq
  | lam _ _ ihA ihb =>
      intro e c heq
      cases e with
      | lam A u b =>
          simp only [liftA, ExprA.lam.injEq] at heq
          obtain ⟨tA, htA, rfl⟩ := ihA A c heq.1
          obtain ⟨tb, htb, rfl⟩ := ihb b (c + 1) heq.2.2
          obtain rfl := heq.2.1
          exact ⟨.lam tA tb, .lam htA htb, rfl⟩
      | bvar j => simp only [liftA] at heq; split at heq <;> simp at heq
      | _ => simp [liftA] at heq
  | pi _ _ ihA ihB =>
      intro e c heq
      cases e with
      | pi A u B v =>
          simp only [liftA, ExprA.pi.injEq] at heq
          obtain ⟨tA, htA, rfl⟩ := ihA A c heq.1
          obtain ⟨tB, htB, rfl⟩ := ihB B (c + 1) heq.2.2.1
          obtain rfl := heq.2.1
          obtain rfl := heq.2.2.2
          exact ⟨_, .pi htA htB, rfl⟩
      | bvar j => simp only [liftA] at heq; split at heq <;> simp at heq
      | _ => simp [liftA] at heq
  | letE _ _ _ ihA ihv ihb =>
      intro e c heq
      cases e with
      | letE A w b =>
          simp only [liftA, ExprA.letE.injEq] at heq
          obtain ⟨tA, htA, rfl⟩ := ihA A c heq.1
          obtain ⟨tv, htv, rfl⟩ := ihv w c heq.2.1
          obtain ⟨tb, htb, rfl⟩ := ihb b (c + 1) heq.2.2
          exact ⟨.letE tA tv tb, .letE htA htv htb, rfl⟩
      | bvar j => simp only [liftA] at heq; split at heq <;> simp at heq
      | _ => simp [liftA] at heq
  | @lit n t _ ih =>
      intro e c heq
      cases e with
      | lit n' =>
          simp only [liftA, ExprA.lit.injEq] at heq
          subst heq
          obtain ⟨t0, ht0, rfl⟩ := ih (natExpandA n) c (liftA_natExpandA_closed n c).symm
          exact ⟨t0, .lit ht0, rfl⟩
      | bvar j => simp only [liftA] at heq; split at heq <;> simp at heq
      | _ => simp [liftA] at heq

/-- The exact one-binder lifting law of the image. -/
theorem denote_lift (hbody : DefinitionBodiesClosed V) (hhook : HookLiftFixed V H)
    (ρ : EnvI) (c : Nat) (S : Value) (e : ExprA) :
    EnvironmentEval.denote V H ν (EnvI.insert ρ c S) (liftA c 1 e) =
      EnvironmentEval.denote V H ν ρ e := by
  funext cpt
  apply propext
  constructor
  · rintro ⟨t', ht', hc⟩
    obtain ⟨t, ht, rfl⟩ := translation_unlift hbody hhook ht' e c rfl
    exact ⟨t, ht, approxI_lift_elim t hc⟩
  · rintro ⟨t, ht, hc⟩
    exact ⟨lift c 1 t, translation_lift hbody hhook ht c, approxI_lift_intro hc c S⟩

/-- Lifting past any pushed list of raw values. -/
theorem denote_liftN (hbody : DefinitionBodiesClosed V) (hhook : HookLiftFixed V H) :
    ∀ (xs : List Value) (ρ : EnvI) (e : ExprA),
      EnvironmentEval.denote V H ν (pushAll xs ρ) (liftA 0 xs.length e) =
        EnvironmentEval.denote V H ν ρ e
  | [], ρ, e => by
      show EnvironmentEval.denote V H ν ρ (liftA 0 0 e) = _
      rw [liftA_zero]
  | x :: xs, ρ, e => by
      show EnvironmentEval.denote V H ν (pushAll xs (EnvI.cons x ρ)) (liftA 0 (xs.length + 1) e) = _
      rw [Nat.add_comm xs.length 1, ← liftA_liftA_merge xs.length 1 0 0 (Nat.le_refl 0) (by omega) e,
        denote_liftN hbody hhook xs (EnvI.cons x ρ) (liftA 0 1 e), ← EnvI.insert_zero,
        denote_lift hbody hhook ρ 0 x e]

/-- The image of a variable is the native variable reading. -/
theorem denote_bvar (ρ : EnvI) (i : Nat) :
    EnvironmentEval.denote V H ν ρ (.bvar i) = denI ρ (.bvar i) := by
  funext cpt
  apply propext
  constructor
  · rintro ⟨t, ht, hc⟩
    cases ht with
    | cut =>
        rw [EnvironmentEval.cutTerm_only_bottom hc]
        exact denI_bot _ _
    | bvar => exact hc
  · intro hc
    exact ⟨_, .bvar i, hc⟩

end Lift

end Rcic.Declarative.Ann.LR3.IotaRecursor
