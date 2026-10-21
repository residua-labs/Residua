import rcic.RcicAnnEnvWf

/-!
# M2-f (4b) — the Kripke telescope lemma on the copy

L-RING C6's `telIntro`, on the copy's relation. A head `f` is related to `g` at a Π-telescope
`T` of `len` binders, none of them a proposition, as soon as, at EVERY well-formed world and for
EVERY related argument list of that length along the weakened telescope, the two full
applications are related at the codomain instance. Induction on `len`: the pi clause opens a world
`ρ` and a related pair `(a, a')` at the domain; the induction hypothesis runs at `wkCtxA ρ Γ` for
the heads `f a`, `g a'` and the instantiated codomain, its own full-application hypothesis paid
from the given one at the COMPOSED world `ρ ∘ ρ'` with the argument list `wk ρ' a :: bs` (the
domain pair weakened along `ρ'`, `LRRelA_wk`).

On the copy the pi clause's relation also carries the two heads' typings and their conversion, so
each step builds the typed applications: the left at the left instance of the codomain, the right
retyped there along the codomain equality the clause carries (`eqKA_tyConv`).

Its converse, iterated elimination (`LRRelA_apps`: related heads, at the identity world, give related
full applications), is here too, below the constructors' clause that reads it at a function-recursive
field (R-NoFunRec-1 step 1 (1c-δ)).

Consumers: the families' clause (M2-f (4b), at the family's telescope) and the constructors'
(M2-f (4c)).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- a Π-telescope of at least `len` binders whose codomain annotations are not zero: no layer is
    a proposition (`isPropTy_pi_iff`). -/
def IsPiTelA : Nat → ExprA → Prop
  | 0, _ => True
  | n + 1, .pi _ _ C v => isZero v = false ∧ IsPiTelA n C
  | _ + 1, _ => False

theorem isPiTelA_liftA : (len c a : Nat) → (T : ExprA) → IsPiTelA len T → IsPiTelA len (liftA c a T)
  | 0, _, _, _, _ => trivial
  | n + 1, c, a, .pi _ _ C _, ⟨hv, h⟩ => ⟨hv, isPiTelA_liftA n (c + 1) a C h⟩
  | _ + 1, _, _, .bvar _, h => h.elim
  | _ + 1, _, _, .sort _, h => h.elim
  | _ + 1, _, _, .const _ _, h => h.elim
  | _ + 1, _, _, .app _ _, h => h.elim
  | _ + 1, _, _, .lam _ _ _, h => h.elim
  | _ + 1, _, _, .letE _ _ _, h => h.elim
  | _ + 1, _, _, .lit _, h => h.elim

theorem isPiTelA_wk : (ρ : WkSpecA) → (len : Nat) → (T : ExprA) → IsPiTelA len T →
    IsPiTelA len (wkExprA ρ T)
  | [], _, _, h => h
  | (_, c) :: ρ, len, T, h => isPiTelA_wk ρ len (liftA c 1 T) (isPiTelA_liftA len c 1 T h)

theorem isPiTelA_instantiate : (len j : Nat) → (x T : ExprA) → IsPiTelA len T →
    IsPiTelA len (instantiateA j x T)
  | 0, _, _, _, _ => trivial
  | n + 1, j, x, .pi _ _ C _, ⟨hv, h⟩ => ⟨hv, isPiTelA_instantiate n (j + 1) (liftA 0 1 x) C h⟩
  | _ + 1, _, _, .bvar _, h => h.elim
  | _ + 1, _, _, .sort _, h => h.elim
  | _ + 1, _, _, .const _ _, h => h.elim
  | _ + 1, _, _, .app _ _, h => h.elim
  | _ + 1, _, _, .lam _ _ _, h => h.elim
  | _ + 1, _, _, .letE _ _ _, h => h.elim
  | _ + 1, _, _, .lit _, h => h.elim

section TelIntro
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- related argument lists along a telescope: each pair at the relation of its domain,
    instantiated with the LEFT arguments so far. -/
inductive ArgsRelKA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (Γ : LCtxA) : ExprA → List ExprA → List ExprA → Prop
  | nil (T : ExprA) : ArgsRelKA E I n ρ₀ k Γ T [] []
  | cons (A : ExprA) (u : Level) (B : ExprA) (v : Level) (f f' : ExprA) (fs fs' : List ExprA)
      (h : LRRelA E I n ρ₀ k Γ A f f')
      (hs : ArgsRelKA E I n ρ₀ k Γ (instantiate0A f B) fs fs') :
      ArgsRelKA E I n ρ₀ k Γ (.pi A u B v) (f :: fs) (f' :: fs')

/-- at every well-formed world, every related argument list of length `len` along the weakened
    telescope relates the two full applications at the codomain instance. -/
def FullAppsRelA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (ρ₀ : Nat → Nat) (k : Nat)
    (Γ : LCtxA) (T : ExprA) (len : Nat) (f g : ExprA) : Prop :=
  ∀ (ρ : WkSpecA), WkOkA E I n ρ Γ → ∀ (as as' : List ExprA),
    ArgsRelKA E I n ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ T) as as' → as.length = len →
    ∀ C : ExprA, applyTelA as (wkExprA ρ T) = some C →
      LRRelA E I n ρ₀ k (wkCtxA ρ Γ) C (foldAppsA (wkExprA ρ f) as) (foldAppsA (wkExprA ρ g) as')

/-- THE KRIPKE TELESCOPE LEMMA: full applications related ⇒ heads related. -/
theorem telIntroA (hE : EnvClosedA E) (hI : IotaLiftA I) (hEN : EnvNormCtorTypeA E)
    (hNC : EnvNormClosedA E) {k : Nat} :
    ∀ (len : Nat) {Γ : LCtxA} {T : ExprA} {R : ExprA → ExprA → Prop} {f g : ExprA},
      Nonempty (CtxWfA E I n Γ) → IsPiTelA len T → LRTyA E I n ρ₀ k Γ T R →
      Nonempty (HasTyA E I n Γ f T) → Nonempty (HasTyA E I n Γ g T) →
      Nonempty (ConvA E I n Γ f g T) → FullAppsRelA E I n ρ₀ k Γ T len f g → R f g
  | 0, Γ, T, R, f, g, hΓ, _, hT, _, _, _, H => by
      obtain ⟨R', hR', hfg⟩ := H [] ⟨trivial, hΓ⟩ [] [] (.nil _) rfl T rfl
      rw [LRTyA_unique hR' hT] at hfg
      exact hfg
  | len + 1, Γ, .pi D u C v, R, f, g, hΓ, ⟨hv, hpi⟩, hT, hf, hg, hc, H => by
      have hnp : ¬ IsPropTy E I Γ (.pi D u C v) := fun h => by
        rw [(isPropTy_pi_iff E I Γ D u C v).1 h] at hv
        cases hv
      rw [LRTyA_eq] at hT
      obtain ⟨sT, ⟨hTty⟩⟩ := tyKA_hasTy hT
      obtain ⟨RD, RC, hD, hC, hCeq, hReq⟩ := tyKA_pi_inv hT hnp
      subst hReq
      refine ⟨fun ρ hρ a a' hr => ?_, hf, hg, hc⟩
      have hDρ : LRTyA E I n ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ D) (RD ρ) := by
        rw [LRTyA_eq]; exact hD ρ hρ
      have hrel : LRRelA E I n ρ₀ k (wkCtxA ρ Γ) (wkExprA ρ D) a a' := ⟨RD ρ, hDρ, hr⟩
      have hr' : RD ρ a' a := by
        obtain ⟨R'', hR'', h''⟩ := LRRelA_symm hEN hrel
        rw [LRTyA_unique hR'' hDρ] at h''
        exact h''
      have hTa := hC ρ hρ a a' hr
      have hTa' := hC ρ hρ a' a hr'
      obtain ⟨w, ⟨hInst⟩⟩ := tyKA_hasTy hTa
      obtain ⟨w', ⟨hInst'⟩⟩ := tyKA_hasTy hTa'
      have hCty := hasTyA_wk_ne_binder hE hI ρ hρ.1 (hasTyA_pi_inv hTty).2
      obtain ⟨⟨ha⟩, ⟨ha'⟩⟩ := LRRelA_hasTy hrel
      obtain ⟨hca⟩ := LRRelA_conv hrel
      obtain ⟨hCtyρ⟩ := hCty
      obtain ⟨hf₀⟩ := hf
      obtain ⟨hg₀⟩ := hg
      obtain ⟨hc₀⟩ := hc
      have hfρ := hasTyA_wk hE hI Γ ρ hρ.1 hf₀
      have hgρ := hasTyA_wk hE hI Γ ρ hρ.1 hg₀
      have hcρ := convA_wk hE hI Γ ρ hρ.1 hc₀
      rw [wkExprA_pi_ub] at hfρ hgρ hcρ
      have hfa : HasTyA E I n (wkCtxA ρ Γ) (.app (wkExprA ρ f) a)
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) :=
        .app _ _ _ _ _ _ _ w hCtyρ hInst hfρ ha
      have hga' : HasTyA E I n (wkCtxA ρ Γ) (.app (wkExprA ρ g) a')
          (instantiate0A a' (wkExprA (WkSpecA.ub ρ) C)) :=
        .app _ _ _ _ _ _ _ w' hCtyρ hInst' hgρ ha'
      obtain ⟨hceq⟩ := eqKA_tyConv (hCeq ρ hρ a a' hr)
      have hga : HasTyA E I n (wkCtxA ρ Γ) (.app (wkExprA ρ g) a')
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) :=
        hasTyA_of_tyConvA hga' hceq.symm
      have hcapp : ConvA E I n (wkCtxA ρ Γ) (.app (wkExprA ρ f) a) (.app (wkExprA ρ g) a')
          (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) :=
        .app _ _ _ _ _ _ _ _ _ hcρ hca hCtyρ hga
      have hpi' : IsPiTelA len (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) :=
        isPiTelA_instantiate len 0 a _ (isPiTelA_wk (WkSpecA.ub ρ) len C hpi)
      have hTa₀ : LRTyA E I n ρ₀ k (wkCtxA ρ Γ) (instantiate0A a (wkExprA (WkSpecA.ub ρ) C))
          (RC ρ a) := by
        rw [LRTyA_eq]; exact hTa
      refine telIntroA hE hI hEN hNC len hρ.2 hpi' hTa₀ ⟨hfa⟩ ⟨hga⟩ ⟨hcapp⟩ ?_
      intro ρ' hρ' bs bs' hbs hlen C' hC'
      have e : instantiate0A (wkExprA ρ' a) (wkExprA (WkSpecA.ub (WkSpecA.comp ρ ρ')) C) =
          wkExprA ρ' (instantiate0A a (wkExprA (WkSpecA.ub ρ) C)) := by
        rw [wkExprA_instantiate0A, WkSpecA.ub_comp, wkExprA_comp]
      have hK : ArgsRelKA E I n ρ₀ k (wkCtxA (WkSpecA.comp ρ ρ') Γ)
          (wkExprA (WkSpecA.comp ρ ρ') (.pi D u C v)) (wkExprA ρ' a :: bs) (wkExprA ρ' a' :: bs') := by
        rw [wkExprA_pi_ub]
        refine .cons _ _ _ _ _ _ _ _ ?_ ?_
        · have h2 := LRRelA_wk hE hNC hI hrel ρ' hρ'
          rw [← wkCtxA_comp, ← wkExprA_comp] at h2
          exact h2
        · rw [e, wkCtxA_comp]; exact hbs
      have hlen' : (wkExprA ρ' a :: bs).length = len + 1 := by simp [hlen]
      have hC'' : applyTelA (wkExprA ρ' a :: bs) (wkExprA (WkSpecA.comp ρ ρ') (.pi D u C v)) =
          some C' := by
        rw [wkExprA_pi_ub]
        show applyTelA bs (instantiate0A (wkExprA ρ' a) (wkExprA (WkSpecA.ub (WkSpecA.comp ρ ρ')) C)) =
          some C'
        rw [e]; exact hC'
      have hres := H (WkSpecA.comp ρ ρ') (wkOkA_comp hρ hρ') (wkExprA ρ' a :: bs)
        (wkExprA ρ' a' :: bs') hK hlen' C' hC''
      rw [wkCtxA_comp] at hres
      show LRRelA E I n ρ₀ k (wkCtxA ρ' (wkCtxA ρ Γ)) C'
        (foldAppsA (wkExprA ρ' (.app (wkExprA ρ f) a)) bs)
        (foldAppsA (wkExprA ρ' (.app (wkExprA ρ g) a')) bs')
      rw [wkExprA_app, wkExprA_app, ← wkExprA_comp, ← wkExprA_comp]
      exact hres
  | _ + 1, _, .bvar _, _, _, _, _, h, _, _, _, _, _ => h.elim
  | _ + 1, _, .sort _, _, _, _, _, h, _, _, _, _, _ => h.elim
  | _ + 1, _, .const _ _, _, _, _, _, h, _, _, _, _, _ => h.elim
  | _ + 1, _, .app _ _, _, _, _, _, h, _, _, _, _, _ => h.elim
  | _ + 1, _, .lam _ _ _, _, _, _, _, h, _, _, _, _, _ => h.elim
  | _ + 1, _, .letE _ _ _, _, _, _, _, h, _, _, _, _, _ => h.elim
  | _ + 1, _, .lit _, _, _, _, _, h, _, _, _, _, _ => h.elim

/-- ITERATED ELIMINATION: related functions at a telescope with no propositional layer, applied to
    related argument lists, are related at the instance (`LRRelA_pi_elim` at the identity world). -/
theorem LRRelA_apps {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) :
    {T : ExprA} → {as as' : List ExprA} → ArgsRelKA E I n ρ₀ k Γ T as as' → ∀ (len : Nat), as.length ≤ len →
    IsPiTelA len T → ∀ {f g : ExprA}, LRRelA E I n ρ₀ k Γ T f g → ∀ C, applyTelA as T = some C →
    LRRelA E I n ρ₀ k Γ C (foldAppsA f as) (foldAppsA g as')
  | _, _, _, .nil _, _, _, _, _, _, hfg, C, hC => by
      injection hC with hC
      subst hC
      exact hfg
  | _, _, _, .cons D u B v a a' as as' hr hs, len, hlen, hpi, f, g, hfg, C, hC => by
      cases len with
      | zero => exact absurd hlen (Nat.not_succ_le_zero _)
      | succ len =>
          obtain ⟨hv, hpi'⟩ := hpi
          have hnp : ¬ IsPropTy E I Γ (.pi D u B v) := fun h => by
            rw [(isPropTy_pi_iff E I Γ D u B v).1 h] at hv
            cases hv
          have hρ : WkOkA E I n [] Γ := ⟨trivial, hΓ⟩
          have h1 : LRRelA E I n ρ₀ k Γ (instantiate0A a B) (.app f a) (.app g a') :=
            LRRelA_pi_elim hfg hnp [] hρ a a' hr
          exact LRRelA_apps hΓ hs len (Nat.le_of_succ_le_succ hlen) (isPiTelA_instantiate len 0 a B hpi') h1 C hC

end TelIntro

#print axioms isPiTelA_wk
#print axioms isPiTelA_instantiate
#print axioms telIntroA
#print axioms LRRelA_apps

end Rcic.Declarative.Ann
