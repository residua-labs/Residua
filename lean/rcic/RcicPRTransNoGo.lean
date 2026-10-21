import rcic.RcicKGateNoGo

/-! `RcicPRTransNoGo` — proof-relevant translation no-go (cc ruling on
#6293, 06:30Z; adversarial check #11 on PROOF_RELEVANT_TRANSLATION.md,
#6608). r1b teeth item; `closure_claim = 0`.

Contents:

* `pinIrrLam` — tree pin: the K rule `irr` λ-closed over the proof `q`,
  `λ q. q ≡ λ q. refl α a : Π (q : Eq α a a). Eq α a a` at
  `eqJoinCtx.tail`.
* `proofs_denote_bot` — soundness of that λ-pair forces every proof
  denotation `p u` (and `ref★`) to `⊥`, given injective `lam` and
  `p ⊥ = ⊥`.
* `proofRelevant_refutes_sound` — a proper `ref★ ≠ ⊥` is inconsistent
  with soundness of `pinIrrLam`'s image.
* `canonRec_not_monotone` — the "fires on `ref★` only" canonical
  eliminator is not monotone in the major.
* `every_monotone_major_fires` — every monotone recursor validating
  the sealed diagonal (`G ⊥ = piM`) fires at a neutral major.
* `transported_iff_row` — P1 ∧ P2 transport: Π-injectivity on the
  source side iff Π-injectivity on the T★ side.
* `closureStar_implies_piInj` — check #10's implication verbatim in
  T★ shape: conv-closure + Π-clause + Π-self-relatedness ⟹ Π-inj.
-/

namespace Rcic

open Rcic.Declarative

/-! ## (a) tree pin: the K rule, λ-closed over the proof

`eqIrr : q ≡ refl α a : Eq α a a` at `eqJoinCtx = [q, m, M, a, α]`
(RcicPinEqIotaStarK.lean:362). One `ConvT.lam` over `q` gives
`λ q. q ≡ λ q. refl α a : Π (q : Eq α a a). Eq α a a` at `[m, M, a, α]`.
By P1 this is a `≈`-equation of T★: `λ q̂. q̂ ≈ λ q̂. ref★ â`. -/
def pinIrrLam :
    ConvT eqEnvT 1 eqJoinCtx.tail (.lam eqPTy (.bvar 0)) (.lam eqPTy eqReflApp)
      (.pi eqPTy eqPTyAt0) :=
  ConvT.lam _ eqPTy eqPTy (.bvar 0) eqReflApp eqPTyAt0 .zero
    (ConvT.refl _ _ _ kgPTyTy) eqIrr

/-! ## (b) soundness of (a) forces proofs to denote ⊥

Paper (2607.13662) Fig.: `⟦λx:A. M⟧ρ = lam (u ↦ ⟦M⟧(ρ, x ↦ p u))`, Bot
(`p ⊥ = ⊥`), `lam` injective (coalesced sum). Thm 2.31 applied to (a)
gives `lam (u ↦ p u) = lam (u ↦ ⟦ref★ a⟧ρ)`. -/
theorem proofs_denote_bot {D : Type} (bot : D) (lam : (D → D) → D)
    (hlam : ∀ f g, lam f = lam g → f = g)
    (p : D → D) (hp : p bot = bot) (r : D)
    (hsound : lam (fun u => p u) = lam (fun _ => r)) :
    r = bot ∧ ∀ u, p u = bot := by
  have h := hlam _ _ hsound
  have hr : r = bot := by
    have := congrFun h bot
    simp only at this
    rw [hp] at this
    exact this.symm
  exact ⟨hr, fun u => by have := congrFun h u; simp only at this; rw [this, hr]⟩

/-- F3 refuted: a proof-relevant `ref★` (a proper element, `≠ ⊥`) is
inconsistent with soundness of `pinIrrLam`'s T★ image. (The paper's Thm
3.1 separation, `ρ = (q ↦ ref ⊥)` vs `ref U`, is the same fact read the
other way.) -/
theorem proofRelevant_refutes_sound {D : Type} (bot : D) (lam : (D → D) → D)
    (hlam : ∀ f g, lam f = lam g → f = g) (p : D → D) (hp : p bot = bot)
    (refW : D) (hproper : refW ≠ bot)
    (hsound : lam (fun u => p u) = lam (fun _ => refW)) : False :=
  hproper (proofs_denote_bot bot lam hlam p hp refW hsound).1

/-! ## (c) the doc's canonical-ι recursor ("fires on `ref★` only") vs
monotonicity

`pinEq_convK_diag` (sealed) λ-binds the major `p`; the Lam clause
evaluates at `p ↦ ⊥`, so any sound monotone model has
`G(major := ⊥) = m̂` with `m̂` a Π code. -/
inductive Qt | bot | refS | nuQ | piM | neut
  deriving DecidableEq

def Qt.le : Qt → Qt → Prop
  | .bot, _ => True
  | x, y => x = y

def Qt.isPi : Qt → Prop
  | .piM => True
  | _ => False

/-- The doc's T★ eliminator: canonical ι, fires on `ref★` only. -/
def canonRec (x : Qt) : Qt := if x = .refS then .piM else .neut

theorem canonRec_not_monotone :
    ¬ (∀ {x y : Qt}, Qt.le x y → Qt.le (canonRec x) (canonRec y)) := by
  intro h
  have := @h .bot .refS trivial
  simp [canonRec, Qt.le] at this

/-- Every monotone recursor that validates the sealed diagonal fires at
a neutral major: the proof's (relevant) denotation is never read. -/
theorem every_monotone_major_fires (G : Qt → Qt)
    (hmono : ∀ {x y}, Qt.le x y → Qt.le (G x) (G y)) (hdiag : G .bot = .piM) :
    G .nuQ = .piM := by
  have h := kgate_nogo Qt.le .bot (fun _ => trivial) Qt.isPi
    (fun {x y} hxy hx => by cases x <;> cases y <;> simp_all [Qt.le, Qt.isPi])
    (fun a _ => G a) (fun ha _ => hmono ha) .piM trivial hdiag .nuQ .nuQ
  revert h
  cases G .nuQ <;> simp [Qt.isPi]

/-! ## (d) the transported theorem is the row restated (P1 ∧ P2)

Contexts/types elided: this is the shape of §2 P4. -/
theorem transported_iff_row {Tm TmS : Type}
    (Conv : Tm → Tm → Prop) (ConvS : TmS → TmS → Prop)
    (tr : Tm → TmS) (pi : Tm → Tm → Tm) (piS : TmS → TmS → TmS)
    (hpi : ∀ A B, tr (pi A B) = piS (tr A) (tr B))
    (P1 : ∀ a b, Conv a b → ConvS (tr a) (tr b))
    (P2 : ∀ a b, ConvS (tr a) (tr b) → Conv a b) :
    (∀ A B A' B', ConvS (piS (tr A) (tr B)) (piS (tr A') (tr B')) →
        ConvS (tr A) (tr A') ∧ ConvS (tr B) (tr B')) ↔
    (∀ A B A' B', Conv (pi A B) (pi A' B') → Conv A A' ∧ Conv B B') := by
  constructor
  · intro h A B A' B' hc
    have hc' := P1 _ _ hc
    rw [hpi, hpi] at hc'
    have := h A B A' B' hc'
    exact ⟨P2 _ _ this.1, P2 _ _ this.2⟩
  · intro h A B A' B' hc
    rw [← hpi, ← hpi] at hc
    have := h A B A' B' (P2 _ _ hc)
    exact ⟨P1 _ _ this.1, P1 _ _ this.2⟩

/-! ## (e) check #10's closure ⟹ injectivity, verbatim in T★

`closure` is `LR★.convClosed_idx`; `hrefl` is FL★ at a well-typed Π;
`hclause` is the LR's Π clause at the universe witness `Π(⊥,⊥)` plus
escape. -/
theorem closureStar_implies_piInj {TmS W : Type}
    (ConvS : TmS → TmS → Prop) (LR : TmS → TmS → W → Prop)
    (piW : W) (piS : TmS → TmS → TmS)
    (hrefl : ∀ A B, LR (piS A B) (piS A B) piW)
    (hclause : ∀ A B A' B', LR (piS A B) (piS A' B') piW → ConvS A A' ∧ ConvS B B')
    (closure : ∀ a b b' w, ConvS a b → LR b b' w → LR a b' w) :
    ∀ A B A' B', ConvS (piS A B) (piS A' B') → ConvS A A' ∧ ConvS B B' :=
  fun A B A' B' h => hclause _ _ _ _ (closure _ _ _ _ h (hrefl A' B'))

#print axioms pinIrrLam
#print axioms proofs_denote_bot
#print axioms proofRelevant_refutes_sound
#print axioms canonRec_not_monotone
#print axioms every_monotone_major_fires
#print axioms transported_iff_row
#print axioms closureStar_implies_piInj

end Rcic
