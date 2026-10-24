import rcic.RcicF3DBoundDefs

/-!
# F3 class D: `BoundDG` from `BoundG` under `RecBelowCtors`

`BoundG`'s first group clause bounds a typing of each constructor's stored type
`policyPi (parameters ++ fields) (F …)` in the constructor scope, at the
constructor's own instances. Inverting the Π-telescope of that typing gives a
bounded typing of every domain in its prefix context; the domains after the
parameters are the fields, and their prefix context is the constructor's own
telescope context. When the recursor's bound is at most the constructor's
(`RecBelowCtors`), the recursor's instances are among the constructor's, so the
field typings are bounded there: `BoundDG`.

- `pi_inv_lokt`: a bounded typing of `pi A B` at any type has bounded typings
  of `A` and of `B` (under `A`) at sorts, through `conv`.
- `policyPi_inv_lokt`, `policyPi_inv_lokt_nil`: the same along a telescope.
- `boundDG_of_boundG`: `RecBelowCtors K hW → BoundG K hW → BoundDG K hW`.

What is not here: without `RecBelowCtors` the implication fails at the bound
itself; `BoundG` constrains `K rr` only under `Prop` large elimination, while
`BoundDG` forces `K rr ≤ K c` for every constant `c` heading a field at a
parameter level (`boundDG_rec_le_head`, in the class-D model).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- Transport of a bounded typing along an equation of subjects. -/
theorem lokt_cast {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' T : Expr Nat} (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (h : A = A') (d : HasTyT E n Γ A T) (hd : LOKt σ N K d) : ∃ d' : HasTyT E n Γ A' T, LOKt σ N K d' :=
  h ▸ ⟨d, hd⟩

/-- Transport of a bounded typing along an equation of contexts. -/
theorem lokt_cast_ctx {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx} {A T : Expr Nat} (σ : Nat → Nat) (N : Nat)
    (K : Nat → Nat) (h : Γ = Γ') (d : HasTyT E n Γ A T) (hd : LOKt σ N K d) :
    ∃ d' : HasTyT E n Γ' A T, LOKt σ N K d' :=
  h ▸ ⟨d, hd⟩

/-- A bounded typing of `pi A B` (at any type) has bounded typings of its
domain and of its codomain at sorts. -/
theorem pi_inv_lokt {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    {Γ : LCtx} → {A B T : Expr Nat} → (d : HasTyT E n Γ (.pi A B) T) → LOKt σ N K d →
    ∃ (u v : Level) (hA : HasTyT E n Γ A (.sort u)) (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)),
      LOKt σ N K hA ∧ LOKt σ N K hB
  | _, _, _, _, .pi _ _ u _ v hA hB, hl => ⟨u, v, hA, hB, hl.2.2.1, hl.2.2.2⟩
  | _, _, _, _, .conv _ _ _ _ _ h _, hl => pi_inv_lokt σ N K h hl.1

/-- Along a telescope: every domain is typed at a sort in its prefix context
(the earlier domains, innermost first, over the ambient context), bounded. -/
theorem policyPi_inv_lokt {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) (N : Nat) (K : Nat → Nat) :
    (doms : List (Expr Nat)) → (body : Expr Nat) → (Γ : LCtx) → {T : Expr Nat} →
    (d : HasTyT E n Γ (policyPi doms body) T) → LOKt σ N K d → ∀ (k : Nat) (hk : k < doms.length),
    ∃ (l : Level) (d' : HasTyT E n (((doms.take k).reverse.map LocalDecl.assumption) ++ Γ) (doms[k]'hk) (.sort l)),
      LOKt σ N K d'
  | [], _, _, _, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | A :: rest, body, Γ, _, d, hl, k, hk => by
      obtain ⟨u, _, hA, hB, lA, lB⟩ := pi_inv_lokt σ N K d hl
      cases k with
      | zero => exact ⟨u, hA, lA⟩
      | succ k =>
          obtain ⟨l, d', hd'⟩ :=
            policyPi_inv_lokt σ N K rest body (.assumption A :: Γ) hB lB k (Nat.lt_of_succ_lt_succ hk)
          have e : ((rest.take k).reverse.map LocalDecl.assumption) ++ (.assumption A :: Γ) =
              (((A :: rest).take (k + 1)).reverse.map LocalDecl.assumption) ++ Γ := by
            simp [List.take_succ_cons, List.reverse_cons, List.map_append, List.append_assoc]
          exact ⟨l, lokt_cast_ctx σ N K e d' hd'⟩

/-- The telescope inversion in the empty ambient context: the prefix context is
`policyPrefixContext`. -/
theorem policyPi_inv_lokt_nil {E : ResolvedEnv} {n : Nat} (σ : Nat → Nat) (N : Nat) (K : Nat → Nat)
    (doms : List (Expr Nat)) (body : Expr Nat) {T : Expr Nat} (d : HasTyT E n [] (policyPi doms body) T)
    (hl : LOKt σ N K d) (k : Nat) (hk : k < doms.length) :
    ∃ (l : Level) (d' : HasTyT E n (policyPrefixContext doms k) (doms[k]'hk) (.sort l)), LOKt σ N K d' := by
  obtain ⟨l, d', hd'⟩ := policyPi_inv_lokt σ N K doms body [] d hl k hk
  have e : ((doms.take k).reverse.map LocalDecl.assumption) ++ [] = policyPrefixContext doms k := by
    unfold policyPrefixContext
    exact List.append_nil _
  exact ⟨l, lokt_cast_ctx σ N K e d' hd'⟩

/-- **`BoundDG` from `BoundG`** when the recursor's bound is at most each
constructor's: the field typings are the domains of the constructor's stored
type's typing (`BoundG`'s first group clause), inverted along its telescope. -/
theorem boundDG_of_boundG (K : Nat → Nat) : {E : ResolvedEnv} → (hW : EnvWfT E) → RecBelowCtors K hW →
    BoundG K hW → BoundDG K hW
  | _, .empty, _, _ => trivial
  | _, .axiom _ _ _ _ hE _ _ _ _, hR, hB => boundDG_of_boundG K hE hR hB
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _, hR, hB => boundDG_of_boundG K hE hR hB.1
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _, hR, hB => boundDG_of_boundG K hE hR hB.1
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _, hR, hB => boundDG_of_boundG K hE hR hB.1
  | _, .group E f fm ctors rr rm E' hE hfam hctors hrec hmem, hR, hB => by
      obtain ⟨hR, hRC⟩ := hR
      obtain ⟨hBE, hB1, _, _⟩ := hB
      refine ⟨boundDG_of_boundG K hE hR hBE, fun node i vs hlen hvs k => ?_⟩
      · have hrr : rr = f + 1 + node.a.constructors.length := by
          have h := node.a.recursorRef
          rw [node.fam] at h
          exact h
        have hle : K rr ≤ K (f + 1 + i.val) := hRC _ (by omega) (by have := i.isLt; omega)
        obtain ⟨u, d, hd⟩ := hB1 node i vs hlen (fun v hv => Nat.le_trans (hvs v hv) hle)
        obtain ⟨d', hd'⟩ := lokt_cast (σOf vs) 4 K (node.a.constructorViews i).storedType d hd
        have hk : (node.a.constructorViews i).parameters.length + k.val <
            ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields).length := by
          rw [List.length_append]
          have := k.isLt
          omega
        obtain ⟨l, d'', hd''⟩ := policyPi_inv_lokt_nil (σOf vs) 4 K _ _ d' hd' _ hk
        have hg : ((node.a.constructorViews i).parameters ++ (node.a.constructorViews i).fields)[
            (node.a.constructorViews i).parameters.length + k.val]'hk = (node.a.constructorViews i).fields[k] := by
          rw [List.getElem_append_right (Nat.le_add_right _ _)]
          simp only [Nat.add_sub_cancel_left, Fin.getElem_fin]
        exact ⟨l, lokt_cast (σOf vs) 4 K hg d'' hd''⟩

end PSet

end Rcic.F3
