/- rcic: DT-025/A-6 S0-N M3 — the erased-step bridge.

A typed weak-head step (`TyHRedA`) erases to a `ParRedStar` on the
erased environment and context — EXCEPT at the unit/struct arms
(`kunit`/`kstruct`): they contract `app f a` at an arbitrary major,
while the erased `iotaSpine` needs a constructor-headed major — and a
constructor-headed major is exactly where `iota` takes the step
instead. At such a step the erased side stays at the step's source.

`StepHasKStop` marks steps containing a stop arm (possibly nested
under `.app`/`.major`/`.conv` wrappers); `tyHRedA_erase` returns, per
step `a → b`, an erased star `erase a →* erase X` with `X = b`
(followed) or `X = a` (stopped). `tmChainA_erase` iterates it: either
reaches `erase` of the chain's endpoint, or stops at the source of
the first step containing a stop arm — `ChainStepAt` returns that
step for the endpoint analysis (M4). No `sorry`. -/

import rcic.RcicAnnTyRed
import rcic.RcicAnnErase
import rcic.RcicParRedDevel

namespace Rcic.Declarative.NormalizingErase

open Rcic.Declarative
open Rcic.Declarative.Ann

variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- steps containing a STOP arm (`kunit`/`kstruct`, possibly nested
under `.app`/`.major`/`.conv`): the erased side cannot mirror the
contraction. -/
def StepHasKStop {Γ : LCtxA} {a b A : ExprA} : TyHRedA E I n Γ a b A → Prop
  | .app _ _ _ _ _ _ _ _ _ _ h _ _ _ _ => StepHasKStop h
  | .conv _ _ _ _ _ h _ => StepHasKStop h
  | .major _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ => StepHasKStop h
  | .kunit .. | .kstruct .. => True
  | _ => False

/-- M3-b: `iotaFnA` firing produces an erased `DerivedIota` at Type
level. `derivedIota_of_iotaFnA` is `Nonempty`-wrapped and cannot feed
Type-valued data (`ParRedStar`); instead the witness is recovered from
`iotaReductCert`'s Option output (a function — Type-extractable).
Firing (`iotaReductCert_of`) and rhs-agreement (`iotaReduct_of` +
determinism) are Prop-level facts inside `have`s, where the
`Nonempty`/`∃`-eliminations are legal. -/
def derivedIotaTy_of_iotaFnA {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfA I EA) (hnf : EnvNoFunA EA) (hn : EnvNormEraseA EA)
    {e e' : ExprA} (h : iotaFnA EA e = some e') :
    DerivedIota (eraseEnv EA) (erase e) (erase e') := by
  match hc : iotaReductCert (eraseEnv EA) (erase e) with
  | some ⟨w, hlhs⟩ =>
      have hrhs : iotaRhsOf w = erase e' := by
        obtain ⟨d⟩ := derivedIota_of_iotaFnA hW hnf hn h
        let ⟨w₀, hl₀, hr₀⟩ := derivedIota_unpack d
        have hred₀ : iotaReduct (eraseEnv EA) (erase e) = some (iotaRhsOf w₀) :=
          hl₀.symm ▸ iotaReduct_of w₀
        have := Option.some.inj (hred₀ ▸ iotaReductCert_some_reduct hc)
        exact this.symm.trans hr₀.symm
      exact hlhs ▸ hrhs ▸ DerivedIota.of w
  | none =>
      have hne : iotaReductCert (eraseEnv EA) (erase e) ≠ none := by
        obtain ⟨d⟩ := derivedIota_of_iotaFnA hW hnf hn h
        let ⟨w, hl, _⟩ := derivedIota_unpack d
        intro hnone
        have his := iotaReductCert_of w
        rw [hl] at hnone
        rw [hnone] at his
        exact Bool.noConfusion his
      exact absurd hc hne

/-- the `hI` premise discharged at the concrete oracle `iotaIfaceA`
(`.fn` is `iotaFnA` definitionally). -/
def derivedIotaTy_of_iface {EA : ResolvedEnvA}
    (hW : EnvWfA (iotaIfaceA EA) EA) (hnf : EnvNoFunA EA)
    (hn : EnvNormEraseA EA) :
    ∀ e e', (iotaIfaceA EA).fn e = some e' →
      DerivedIota (eraseEnv EA) (erase e) (erase e') :=
  fun _ _ h => derivedIotaTy_of_iotaFnA hW hnf hn h

/-- M3-a (per step): a typed weak-head step erases to a `ParRedStar`;
when the step contains a stop arm the erased side stays at the
step's source (`X = a`). The iota arm uses the erased-side
correspondence: `I.fn` firing gives a `DerivedIota` witness, and the
erased `ParRed.iotaSpine` takes exactly that step. -/
def tyHRedA_erase
    (hI : ∀ e e', I.fn e = some e' →
      DerivedIota (eraseEnv E) (erase e) (erase e')) :
    {Γ : LCtxA} → {a b A : ExprA} → (h : TyHRedA E I n Γ a b A) →
      Σ' X : ExprA,
        ParRedStar (eraseEnv E) n (eraseCtx Γ) (erase a) (erase X) ×'
        ((X = b) ⊕' ((X = a) ×' StepHasKStop h))
  | _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ =>
      ⟨_, by
        rw [erase_instantiate0A]
        exact (.tail (.beta _ _ _ _ _ _ _ (.refl _ _) (.refl _ _) (.refl _ _))
          (.refl _ _)),
        .inl rfl⟩
  | _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ =>
      ⟨_, by
        rw [erase_instantiate0A]
        exact (.tail (.zeta _ _ _ _ _ _ _ (.refl _ _) (.refl _ _) (.refl _ _))
          (.refl _ _)),
        .inl rfl⟩
  | _, _, _, _, .zetaLocal _ _ _ _ hval _ _ =>
      ⟨_, by
        obtain ⟨A0, stored, hget, hvl⟩ :=
          get?_of_lookupValue (lookupValue_eraseCtx_some hval)
        rw [hvl]
        exact (.tail (.bvarZeta _ _ _ _ _ hget (.refl _ _)) (.refl _ _)),
        .inl rfl⟩
  | _, _, _, _, .delta _ _ _ m b hres hbody htr _ _ _ =>
      ⟨_, by
        rw [erase_instantiateLevelsA]
        exact (.tail
          (.delta _ _ _ _ _ (members_eraseEnv_some hres)
            (by
              show m.bodyA.map erase = some (erase b)
              rw [hbody]
              rfl)
            htr)
          (.refl _ _)),
        .inl rfl⟩
  | _, _, _, _, .iota _ lhs rhs _ h _ _ =>
      let ⟨w, hl, hr⟩ := derivedIota_unpack (hI lhs rhs h.graph)
      ⟨rhs, by
        rw [hl, hr]
        exact (.tail (parRed_iota _ w) (.refl _ _)),
        .inl rfl⟩
  | _, _, _, _, .lit _ t _ _ =>
      ⟨_, by
        rw [erase_natExpandA]
        exact (.tail (.lit _ _) (.refl _ _)),
        .inl rfl⟩
  | _, _, _, _, .app _ f _ a _ _ _ _ _ _ h _ _ _ _ =>
      match tyHRedA_erase hI h with
      | ⟨X_i, st, .inl hX⟩ =>
          ⟨.app X_i a, by
            subst hX
            exact parRedStar_app_fun st,
            .inl (congrArg (·.app a) hX)⟩
      | ⟨_, _, .inr ⟨_, hk⟩⟩ =>
          ⟨.app f a, .refl _ _, .inr ⟨rfl, hk⟩⟩
  | _, _, _, _, .conv _ _ _ _ _ h _ =>
      match tyHRedA_erase hI h with
      | ⟨X_i, st, .inl hX⟩ => ⟨X_i, hX ▸ st, .inl hX⟩
      | ⟨_, _, .inr ⟨_, hk⟩⟩ => ⟨_, .refl _ _, .inr ⟨rfl, hk⟩⟩
  | _, _, _, _, .major _ f a _ _ _ _ _ _ _ _ _ _ _ h _ _ _ _ =>
      match tyHRedA_erase hI h with
      | ⟨X_i, st, .inl hX⟩ =>
          ⟨.app f X_i, by
            subst hX
            exact parRedStar_app_arg st,
            .inl (congrArg (ExprA.app f) hX)⟩
      | ⟨_, _, .inr ⟨_, hk⟩⟩ =>
          ⟨.app f a, .refl _ _, .inr ⟨rfl, hk⟩⟩
  | _, _, _, _, .kunit _ f a _ _ _ _ _ _ _ _ =>
      ⟨.app f a, .refl _ _, .inr ⟨rfl, True.intro⟩⟩
  | _, _, _, _, .kstruct _ f a _ _ _ _ _ _ _ =>
      ⟨.app f a, .refl _ _, .inr ⟨rfl, True.intro⟩⟩

/-- `s` is the one step `t` takes at `X` (the step whose source is
`X`). -/
inductive ChainStepAt {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {A : ExprA} : {a N : ExprA} → TmChainA E I n Γ A a N →
      (X b : ExprA) → TyHRedA E I n Γ X b A → Prop
  | head {a a' N : ExprA} (ha : HasTyA E I n Γ a A)
      (s : TyHRedA E I n Γ a a' A) (t : TmChainA E I n Γ A a' N) :
      ChainStepAt (.cons a a' N ha s t) a a' s
  | tail {a a' N : ExprA} (ha : HasTyA E I n Γ a A)
      (s : TyHRedA E I n Γ a a' A) (t : TmChainA E I n Γ A a' N)
      {X b : ExprA} {s' : TyHRedA E I n Γ X b A}
      (h : ChainStepAt t X b s') :
      ChainStepAt (.cons a a' N ha s t) X b s'

/-- M3 (the erased-step bridge, chain level): a typed weak-head chain
`a →* N` erases to a `ParRedStar` reaching `erase` of either the
endpoint `N`, or the source of the chain's first step containing a
stop arm — that step is returned (for M4's endpoint analysis). -/
def tmChainA_erase
    (hI : ∀ e e', I.fn e = some e' →
      DerivedIota (eraseEnv E) (erase e) (erase e')) :
    {Γ : LCtxA} → {A a N : ExprA} → (t : TmChainA E I n Γ A a N) →
      Σ' X : ExprA,
        ParRedStar (eraseEnv E) n (eraseCtx Γ) (erase a) (erase X) ×'
        ((X = N) ⊕'
          (Σ' (b : ExprA) (s : TyHRedA E I n Γ X b A),
            StepHasKStop s ×' Nonempty (ChainStepAt t X b s)))
  | _, _, _, _, .refl a _ => ⟨a, .refl _ _, .inl rfl⟩
  | _, _, _, _, .cons a a' N ha s t =>
      match tyHRedA_erase hI s with
      | ⟨X_i, st, .inl hX⟩ =>
          let ⟨Y, sty, fl⟩ := tmChainA_erase hI t
          ⟨Y, by rw [hX] at st; exact parRedStar_trans st sty,
            match fl with
            | .inl hN => .inl hN
            | .inr w =>
                .inr ⟨w.1, w.2.1, w.2.2.1,
                  w.2.2.2.elim fun q => ⟨ChainStepAt.tail ha s t q⟩⟩⟩
      | ⟨_, _, .inr ⟨_, hk⟩⟩ =>
          ⟨a, .refl _ _, .inr ⟨a', s, hk, ⟨ChainStepAt.head ha s t⟩⟩⟩
