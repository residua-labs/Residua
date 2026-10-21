import rcic.RcicAnnLRCum
import rcic.RcicAnnLRWkG
/-!
# M1-d (vi) — cumulativity: the relation of a type does not depend on the height

With every element relation fixed by its sort (`sortT` at `ht l`, `sortP`
level-free, the prop and stuck triples, the pi clause's Kripke data built from
those), a validity or an equality at height `j` is one at every height `j' ≥ j`,
with the SAME term relation: `LRTyA_monog`, `LREqA_monog`, `LRRelA_monog`. This is
what the fundamental theorem's `pi` arm uses to bring its domain's and
codomain's hypotheses (at their own sorts' heights) to the pi's height, and what
R-PropOutOfTower bought: on the M1-d (iv) heights it was false for pis over
`Prop` (README M2-e (0)).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

section Cum
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- both knotted relations, from height `j` to any `j' ≥ j`. -/
theorem LR_mono_allg {j j' : Nat} (hjj : j ≤ j') :
    (∀ {Γ : LCtxA} {A B : ExprA}, LREqAg E I n ρ₀ j Γ A B → LREqAg E I n ρ₀ j' Γ A B) ∧
    (∀ {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop},
      LRTyAg E I n ρ₀ j Γ A R → LRTyAg E I n ρ₀ j' Γ A R) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [LREqA_eqg] at h ⊢
    exact EqKAg.rec
      (motive_1 := fun Γ A B _ =>
        EqKAg E I n ρ₀ j' (fun i _ => LREqAg E I n ρ₀ i) (fun i _ => LRTyAg E I n ρ₀ i) Γ A B)
      (motive_2 := fun Γ A R _ =>
        TyKAg E I n ρ₀ j' (fun i _ => LREqAg E I n ρ₀ i) (fun i _ => LRTyAg E I n ρ₀ i) Γ A R)
      (fun hA hB hk hl hc => .sort hA hB (Nat.lt_of_lt_of_le hk hjj) hl hc)
      (fun hA hB hu hv hDty hCty hD'ty hC'ty RD _ _ _ hc ihD ihDeq ihC =>
        .pi hA hB hu hv hDty hCty hD'ty hC'ty RD ihD ihDeq ihC hc)
      (fun hA hB hnA hnB hm hind hsh hls hps hps' Rs RsF RsI _ _ _ hFldRec _ _ hXRec hXRes hXResR _ hxs hc hpar
          _ _ hFldIRec _ hXRecI hFldIdom hXFldIdom ihFld ihFldF ihFldeq ihFldFeq ihXFld ihXFeq ihFldI ihFldIeq ihXFldI =>
        .fam hA hB hnA hnB hm hind hsh hls hps hps' Rs RsF RsI ihFld ihFldF ihFldeq hFldRec ihFldFeq ihXFld hXRec
          hXRes hXResR ihXFeq hxs hc hpar ihFldI ihFldIeq hFldIRec ihXFldI hXRecI hFldIdom hXFldIdom)
      (fun hA hB hN hN' hc => .stuck hA hB hN hN' hc)
      (fun hA hn hP => .prop hA hn hP)
      (fun hA hz hk => .sortT hA hz (Nat.lt_of_lt_of_le hk hjj))
      (fun hA hz => .sortP hA hz)
      (fun hA hnp hDty hCty RD _ RC _ _ ihD ihC ihCeq => .pi hA hnp hDty hCty RD ihD RC ihC ihCeq)
      (fun hA hn hnp hm hind hsh hps hu hz Rs RsF RsI _ _ _ hFldRec _ hxsD _ _ hFldIRec hFldIdom ihFld ihFldF ihFldeq
          ihFldFeq ihFldI ihFldIeq =>
        .fam hA hn hnp hm hind hsh hps hu hz Rs RsF RsI ihFld ihFldF ihFldeq hFldRec ihFldFeq hxsD ihFldI ihFldIeq
          hFldIRec hFldIdom)
      (fun hA hN => .stuck hA hN)
      h
  · rw [LRTyA_eqg] at h ⊢
    exact TyKAg.rec
      (motive_1 := fun Γ A B _ =>
        EqKAg E I n ρ₀ j' (fun i _ => LREqAg E I n ρ₀ i) (fun i _ => LRTyAg E I n ρ₀ i) Γ A B)
      (motive_2 := fun Γ A R _ =>
        TyKAg E I n ρ₀ j' (fun i _ => LREqAg E I n ρ₀ i) (fun i _ => LRTyAg E I n ρ₀ i) Γ A R)
      (fun hA hB hk hl hc => .sort hA hB (Nat.lt_of_lt_of_le hk hjj) hl hc)
      (fun hA hB hu hv hDty hCty hD'ty hC'ty RD _ _ _ hc ihD ihDeq ihC =>
        .pi hA hB hu hv hDty hCty hD'ty hC'ty RD ihD ihDeq ihC hc)
      (fun hA hB hnA hnB hm hind hsh hls hps hps' Rs RsF RsI _ _ _ hFldRec _ _ hXRec hXRes hXResR _ hxs hc hpar
          _ _ hFldIRec _ hXRecI hFldIdom hXFldIdom ihFld ihFldF ihFldeq ihFldFeq ihXFld ihXFeq ihFldI ihFldIeq ihXFldI =>
        .fam hA hB hnA hnB hm hind hsh hls hps hps' Rs RsF RsI ihFld ihFldF ihFldeq hFldRec ihFldFeq ihXFld hXRec
          hXRes hXResR ihXFeq hxs hc hpar ihFldI ihFldIeq hFldIRec ihXFldI hXRecI hFldIdom hXFldIdom)
      (fun hA hB hN hN' hc => .stuck hA hB hN hN' hc)
      (fun hA hn hP => .prop hA hn hP)
      (fun hA hz hk => .sortT hA hz (Nat.lt_of_lt_of_le hk hjj))
      (fun hA hz => .sortP hA hz)
      (fun hA hnp hDty hCty RD _ RC _ _ ihD ihC ihCeq => .pi hA hnp hDty hCty RD ihD RC ihC ihCeq)
      (fun hA hn hnp hm hind hsh hps hu hz Rs RsF RsI _ _ _ hFldRec _ hxsD _ _ hFldIRec hFldIdom ihFld ihFldF ihFldeq
          ihFldFeq ihFldI ihFldIeq =>
        .fam hA hn hnp hm hind hsh hps hu hz Rs RsF RsI ihFld ihFldF ihFldeq hFldRec ihFldFeq hxsD ihFldI ihFldIeq
          hFldIRec hFldIdom)
      (fun hA hN => .stuck hA hN)
      h

theorem LREqA_monog {j j' : Nat} (hjj : j ≤ j') {Γ : LCtxA} {A B : ExprA}
    (h : LREqAg E I n ρ₀ j Γ A B) : LREqAg E I n ρ₀ j' Γ A B := (LR_mono_allg hjj).1 h

theorem LRTyA_monog {j j' : Nat} (hjj : j ≤ j') {Γ : LCtxA} {A : ExprA} {R : ExprA → ExprA → Prop}
    (h : LRTyAg E I n ρ₀ j Γ A R) : LRTyAg E I n ρ₀ j' Γ A R := (LR_mono_allg hjj).2 h

/-- the SAME relation, so relatedness lifts too. -/
theorem LRRelA_monog {j j' : Nat} (hjj : j ≤ j') {Γ : LCtxA} {A a b : ExprA}
    (h : LRRelAg E I n ρ₀ j Γ A a b) : LRRelAg E I n ρ₀ j' Γ A a b := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨R, LRTyA_monog hjj hR, hab⟩

end Cum

#print axioms LR_mono_allg
#print axioms LRRelA_monog

end Rcic.Declarative.Ann
