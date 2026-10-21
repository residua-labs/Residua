import rcic.RcicNativeTypedModelIota

/-!
# RcicNativeTypedModelTyping — the model typing lemma: statement, the collapse controls, what
remains

Item 3 of the ruling after segment 5.  The model typing lemma is the statement that every
compact of a well-typed term is an element of its type's interpretation:

```
TypingLemmaT E n := ∀ Γ a A, CtxWfT E n Γ → HasTyT E n Γ a A →
  ∀ u, ApproxT E (ctxEnvT E Γ) a u → ElT E (ctxEnvT E Γ) A u
```
(`ElT`, not "typed at every approximant": `pi ⊥ []` is a code of every Π-type and a proposition
code, so nothing but `⊥` is typed at it — `not_ctyS_lam_at_pi_bot_nil`.)

**History (segment 6, commit `0f4c1b362f`).**  Against the pre-amendment `ApproxT` the lemma was
refuted at every environment: the proof `λ (P : Sort 0) (p : P). p` had the non-`⊥` compact
`lam [([], lam [([], ⊥)])]`, while every code of its type `Π (P : Sort 0), P → P` is a
proposition code.  The ruling amended `ApproxT` in place (segment 3): a λ compact must have a
non-`⊥` output (`λ⊥ = ⊥`), a constructor of a family declared into `Sort 0` denotes `⊥`
(`PropCtorT`), and `IsPropCT.pi` carries a type-code domain.  This module now records the
**positive controls** of that collapse (T1 of #7689 at the pins): the proof `polyIdProof`
denotes `⊥` only (`approxT_polyIdProof_bot`), the λ compact with only `⊥` outputs is no compact
of any λ (`not_approxT_lam_botStep`), `True.intro` denotes `⊥` only (`approxT_trueIntro_bot`),
every code of `Π (P : Sort 0), P → P` is a proposition code (`isPropCT_of_approxT_polyIdProp`),
and `IsPropCT → TyCodeCT` (`tyCodeCT_of_isPropCT`, segment 3).

**What remains** is the lemma itself, by the simultaneous induction with the model soundness of
conversion: β from the `ApproxT` substitution lemma (swe-zeta), ι from `IotaSoundT`
(swe-iotaret), `irr` from the collapse, η from `λ⊥ = ⊥`.  It is not provable before them in any
fragment: the `conv` case of the typing lemma is conversion soundness, and the `irr` case of
conversion soundness is the typing lemma at propositions.

Also here: the **recursive proposition families** answer — `recursorProp` is a model clause and
assumes nothing about the readback; at a recursive field the schema's recursive call meets
`recursorProp` again with a `⊥` major, derivations are finite, so the denotation is the finite
unrolling (the least fixpoint, the proof ignored).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys

/-! ### §1 — the statement -/

/-- A model environment typed by a context: every compact of a variable is an element of its
    type's interpretation. -/
def EnvTypedT (E : ResolvedEnv) (Γ : LCtx) (ρ : EnvT) : Prop :=
  ∀ (i : Nat) (A : Expr Nat), lookupType Γ i = some A → ∀ u, ρ i u → ElT E ρ A u

/-- **The model typing lemma** (statement): every compact of a well-typed term is an element of
    its type's interpretation, at the context environment. -/
def TypingLemmaT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {a A : Expr Nat}, HasTyT E n Γ a A →
    ∀ u, ApproxT E (ctxEnvT E Γ) a u → ElT E (ctxEnvT E Γ) A u

/-- Why `ElT` and not "typed at every approximant": nothing but `⊥` is typed at `pi ⊥ []`, which
    is a code of every Π-type. -/
theorem not_ctyS_lam_at_pi_bot_nil (E : ResolvedEnv) (g : List (List CptT × CptT)) :
    ¬ CTyS E (.lam g) (.pi .bot []) := by
  intro h
  rcases ctyS_pi_inv h with h0 | ⟨_, _, hnp, _⟩
  · exact CptT.noConfusion h0
  · exact hnp (.pi .bot (fun _ ht => (List.not_mem_nil _ ht).elim))

/-! ### §2 — the collapse at the pins (T1 controls) -/

/-- `λ (P : Sort 0) (p : P). p`. -/
def polyIdProof : Expr Nat := .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))

/-- `Π (P : Sort 0), P → P`. -/
def polyIdProp : Expr Nat := .pi (.sort .zero) (.pi (.bvar 0) (.bvar 1))

def hasTyT_polyIdProof (E : ResolvedEnv) (n : Nat) : HasTyT E n [] polyIdProof polyIdProp :=
  .lam [] (.sort .zero) (.succ .zero) (.lam (.bvar 0) (.bvar 0)) (.pi (.bvar 0) (.bvar 1))
    (.sort [] .zero)
    (.lam [.assumption (.sort .zero)] (.bvar 0) .zero (.bvar 0) (.bvar 1)
      (.bvar _ 0 _ rfl)
      (.bvar _ 0 _ rfl))

/-- `λ⊥ = ⊥`: the λ compact with only `⊥` outputs is no compact of any λ. -/
theorem not_approxT_lam_botStep (E : ResolvedEnv) (ρ : EnvT) (A b : Expr Nat) :
    ¬ ApproxT E ρ (.lam A b) (.lam [([], .bot)]) := by
  intro h
  rcases approxT_lam_inv h with h0 | ⟨_, g, e, _, ⟨s, hs, hne⟩, _⟩
  · exact CptT.noConfusion h0
  · injection e with eg
    subst eg
    have := List.mem_singleton.mp hs
    subst this
    exact hne rfl

/-- The elements of a proposition demand are `⊥`: a variable whose environment entry is a demand
    typed at `⊥` or `prop` denotes `⊥` only. -/
theorem approxT_bvar_propDemand_bot {E : ResolvedEnv} {ρ : EnvT} {d : List CptT} {a : CptT}
    (ha : a = .bot ∨ a = .prop) (hd : ∀ u ∈ d, CTyS E u a) {c : CptT}
    (h : ApproxT E (EnvT.cons (demandT d) ρ) (.bvar 0) c) : c = .bot ∨ IsPropCT E c := by
  rcases approxT_bvar_inv h with h0 | h0
  · exact Or.inl h0
  · have hmem : c ∈ d := h0
    rcases ha with rfl | rfl
    · exact Or.inl (ctyS_bot_inv (hd c hmem))
    · exact ctyS_prop_inv (hd c hmem)

/-- **T1 at the pin**: the proof `λ (P : Sort 0) (p : P). p` denotes `⊥` only. -/
theorem approxT_polyIdProof_bot (E : ResolvedEnv) (ρ : EnvT) {c : CptT}
    (h : ApproxT E ρ polyIdProof c) : c = .bot := by
  rcases approxT_lam_inv h with h0 | ⟨a, g, rfl, hA, ⟨s, hs, hne⟩, hg⟩
  · exact h0
  · exfalso
    obtain ⟨hdem, hb⟩ := hg s hs
    have ha : a = .bot ∨ a = .prop := by
      rcases approxT_sort_inv hA with rfl | rfl
      · exact Or.inl rfl
      · rw [sortCode_zero]; exact Or.inr rfl
    rcases approxT_lam_inv hb with h1 | ⟨a', g', e', hA', ⟨t, ht, hne'⟩, hg'⟩
    · exact hne h1
    · obtain ⟨hdem', hb'⟩ := hg' t ht
      -- the inner domain code `a'` is an element of `P`'s demand: `⊥` or a proposition code
      have ha' : a' = .bot ∨ IsPropCT E a' := approxT_bvar_propDemand_bot ha hdem hA'
      -- so every demand on `p` is `⊥`, and `p` denotes `⊥`
      rcases approxT_bvar_inv hb' with h2 | h2
      · exact hne' h2
      · have hmem : t.2 ∈ t.1 := h2
        have hty := hdem' t.2 hmem
        rcases ha' with rfl | hP
        · exact hne' (ctyS_bot_inv hty)
        · exact hne' (ctyS_prop_bot hP hty)

/-- Every code of `Π (P : Sort 0), P → P` is a proposition code: its outputs are codes of
    `P → P`, whose outputs are elements of `P`'s demand, which is typed at `prop` (or `⊥`). -/
theorem isPropCT_of_approxT_polyIdProp {E : ResolvedEnv} {ρ : EnvT} {c : CptT}
    (h : ApproxT E ρ polyIdProp c) : IsPropCT E c := by
  rcases approxT_pi_inv h with rfl | ⟨a, f, rfl, hA, hf⟩
  · exact .bot
  · have ha : a = .bot ∨ a = .prop := by
      rcases approxT_sort_inv hA with rfl | rfl
      · exact Or.inl rfl
      · rw [sortCode_zero]; exact Or.inr rfl
    have hta : TyCodeCT a := by rcases ha with rfl | rfl <;> constructor
    refine .pi hta (fun s hs => ?_)
    obtain ⟨hdem, hB⟩ := hf s hs
    rcases approxT_pi_inv hB with h0 | ⟨a', f', e, hA', hf'⟩
    · rw [h0]; exact .bot
    · rw [e]
      have ha' : a' = .bot ∨ IsPropCT E a' := approxT_bvar_propDemand_bot ha hdem hA'
      have hta' : TyCodeCT a' := by
        rcases ha' with rfl | hP
        · exact .bot
        · exact tyCodeCT_of_isPropCT hP
      refine .pi hta' (fun t ht => ?_)
      obtain ⟨_, hB'⟩ := hf' t ht
      rcases approxT_bvar_inv hB' with h1 | h1
      · rw [h1]; exact .bot
      · have hmem : t.2 ∈ s.1 := h1
        have hty := hdem t.2 hmem
        rcases ha with rfl | rfl
        · rw [ctyS_bot_inv hty]; exact .bot
        · rcases ctyS_prop_inv hty with h2 | h2
          · rw [h2]; exact .bot
          · exact h2

/-- Hence the elements of `Π (P : Sort 0), P → P` are `⊥`, and the proof's only compact is one. -/
theorem elT_polyIdProp_bot (E : ResolvedEnv) (ρ : EnvT) {u : CptT} (h : ElT E ρ polyIdProp u) :
    u = .bot :=
  elT_bot_of_propIdeal (fun _ ha => isPropCT_of_approxT_polyIdProp ha) h

/-- The typing lemma's instance at the pin holds. -/
theorem typingLemma_at_polyIdProof (E : ResolvedEnv) (ρ : EnvT) (u : CptT)
    (h : ApproxT E ρ polyIdProof u) : ElT E ρ polyIdProp u := by
  rw [approxT_polyIdProof_bot E ρ h]
  exact elT_bot _ _ _

/-- `True.intro` is a proof constant. -/
theorem propCtorT_trueIntro : PropCtorT trueEnvU 1 :=
  ⟨trueIntroMember, 0, trueFamMember, rfl, rfl, rfl, rfl, rfl⟩

/-- **T1 at the constructor pin**: `True.intro` denotes `⊥` only. -/
theorem approxT_trueIntro_bot (ρ : EnvT) {c : CptT} (h : ApproxT trueEnvU ρ (.const 1 []) c) :
    c = .bot := by
  rcases approxT_const_inv h with h0 | ⟨_, hnp, _⟩ | ⟨m, b, hd, _⟩ | ⟨w, _, _, _, hw, _⟩
    | ⟨w, _, _, hw, _⟩
  · exact h0
  · exact (hnp propCtorT_trueIntro).elim
  · obtain ⟨hm, _, _, hnc⟩ := hd
    have e : trueIntroMember = m := Option.some.inj hm
    subst e
    exact (hnc rfl).elim
  · have hm := w.hrec
    rw [hw] at hm
    have e : trueIntroMember = w.recMember := Option.some.inj hm
    have hrecK := w.hrecK
    rw [← e] at hrecK
    exact MemberClass.noConfusion hrecK
  · have hm := w.hrec
    rw [hw] at hm
    have e : trueIntroMember = w.recMember := Option.some.inj hm
    have hrecK := w.hrecK
    rw [← e] at hrecK
    exact MemberClass.noConfusion hrecK

/-- `λ⊥ ≠ ⊥` in `CptT`: the identification is made by the model's λ clause, not by the compacts. -/
theorem lam_botStep_ne_bot : (CptT.lam [([], .bot)]) ≠ .bot := fun h => CptT.noConfusion h

#print axioms EnvTypedT
#print axioms TypingLemmaT
#print axioms not_ctyS_lam_at_pi_bot_nil
#print axioms polyIdProof
#print axioms polyIdProp
#print axioms hasTyT_polyIdProof
#print axioms not_approxT_lam_botStep
#print axioms approxT_bvar_propDemand_bot
#print axioms approxT_polyIdProof_bot
#print axioms isPropCT_of_approxT_polyIdProp
#print axioms elT_polyIdProp_bot
#print axioms typingLemma_at_polyIdProof
#print axioms propCtorT_trueIntro
#print axioms approxT_trueIntro_bot
#print axioms lam_botStep_ne_bot

end Rcic.Declarative.NativeValleys.TypedModelAudit
