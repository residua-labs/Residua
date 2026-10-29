import rcic.RcicF3FamLim
import rcic.RcicF3KTWFamKT

/-!
# F3 S7 KT-2e: the union-of-iterates / least-fixed-point bridge (class A)

`famLim` (the F3 lane's union-of-iterates family limit) agrees with `famLfp`
(= `famOfD DStar`, the KT lane's least fixed point of `PhiF`) at every
Type-level instance for class-A families whose recursive fields are all
directly recursive — `famLim_famLfp`, then `famLim_famKT_type` for the
combined entry (`famKT` dispatches to `famLfpP` at Prop-reads; that twin
stays the named residue below).

The proof spine (each link a separate declaration):

* §1 the `≈`-valued table-congruence layer (`TelFits_den_congr` …
  `famVal_den_congr`) — keyed to den-`=` at telescope expressions;
* §2 `den_upd_congr` — `den` at two `upd`-tables whose family entries are
  `≈` at every level vector is `≈` (kept for the record; the alignment
  chain below does NOT use it — an all-level `≈` hypothesis is unsatisfiable
  for real iterates, which is the first refutation measured in §5);
* §3 `iterPhi` — the `PhiF`-iterates from `∅`, with the `hD1`–`hD4` side
  conditions `famVal_famOfD` needs (`iterPhi_env`/`levels`/`ne`/`mem`),
  `iterPhi_mono`/`iterPhi_le'` (iterates grow, stay below the lfp);
* §4 `InPhi_witness_noFn` — the finitary witness extraction for guard lists
  without `.fn` arms, giving pre-fixedness of the union `iterPhiUnion` and
  hence `Sub DStar (union)` by leastness;
* §5 the alignment cell `FibAlign` (defined for the premised `≤` direction
  `limEnd_sub`) and the two measured refutations that forced the §6 shape;
* §6 the alignment chain, all proved: the entry induction
  `famIter_famOfD` (via `famVal_den_congr` + `famVal_famOfD` at the
  level-dispatched iterate `iterPhiD`, with the table congruence keyed to
  the canonical entry only — `den_upd_eq_famFree` / `den_upd_congr_rec` /
  `famFields_den_of_entry`), the fibre cell `famEnd_famEndD_iter` (the §5
  `FibAlign`, discharged), the two directions `limEnd_sub_classA` /
  `fibAt_sub_limEnd_classA`, the fibre equivalence `limEnd_famEndD_classA`,
  and the bridges `famLim_famLfp` / `famLim_famKT_type` under `hnoFn`.

**Residue** `[rcic-f3-famkt-bridge-fn-cont]` (`FnContUnion`) — **CLOSED (refuted)**:
the `.fn`-field analogue of the ≥ direction is FALSE, not merely unrouted.
`Rcic.F3.FamKTFnReal.fnContUnion_false` exhibits a height-`N+1`-branching
witness family at the `PsiF` level: `fxZW ∈ PsiF (iterPhiUnion)` yet
`fxZW ∉ iterPhiUnion`, so `hnoFn` is witness-NECESSARY for this bridge
(not a proof debt).  The refutation fixture and its axiom audit live in
`RcicF3FamKTFnReal.lean`.

**Residue** `[rcic-f3-famkt-bridge-prop-twin]` — **CLOSED**: the Prop-read
half of the bridge is routed in `RcicF3FamKTPropTwin.lean`: `limEnd_famEndP`
(`limEnd ≈ famEndP` pointwise at a split env), `famLim_famLfpP`, and
`famLim_famKT_prop` (the `= 0` branch of `famKT`'s `if`-dispatch, the
Prop-twin of `famLim_famKT_type`).  Axioms ⊆ {propext, Quot.sound}.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe T w

namespace PSet

open Rcic.Declarative

/-! ### §0 small helpers -/

/-- A separation over the empty set is empty. -/
theorem sep_pempty {p : PSet.{T} → Prop} : Equiv (sep p pempty) pempty := by
  apply ext; intro z; constructor
  · rintro ⟨⟨a, _⟩, _⟩
    exact a.elim
  · intro hz
    exact (not_mem_pempty hz).elim

/-- `Ed` of `≈`-related denotations transfers membership across tables that
share `dec` (`Ed` only reads `M.dec`). -/
theorem ed_den_congr (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4}) {σ : Nat → Nat} {e : Expr Nat}
    (h : ∀ ρ, Equiv (den (mkM P μ₁) σ ρ e) (den (mkM P μ₂) σ ρ e)) (ρ : Nat → PSet.{4}) :
    Equiv (Ed (mkM P μ₁) (den (mkM P μ₁) σ ρ e)) (Ed (mkM P μ₂) (den (mkM P μ₂) σ ρ e)) :=
  ed_congr (mkM P μ₂) (h ρ)

/-! ### §1 the `≈`-valued table-congruence layer -/

/-- `TelFits` at tables with `≈`-related field domains. -/
theorem TelFits_den_congr (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (Ds : List (Expr Nat)) (hden : ∀ e, e ∈ Ds → ∀ ρ,
      Equiv (den (mkM P μ₁) σ ρ e) (den (mkM P μ₂) σ ρ e)) :
    ∀ ρ xs, TelFits (mkM P μ₁) σ Ds ρ xs ↔ TelFits (mkM P μ₂) σ Ds ρ xs := by
  induction Ds with
  | nil => intro ρ xs; cases xs <;> exact Iff.rfl
  | cons A rest ih =>
      intro ρ xs
      have hA := hden A (List.mem_cons_self _ _)
      have hrest := ih (fun e he => hden e (List.mem_cons_of_mem _ he))
      cases xs with
      | nil => exact Iff.rfl
      | cons x xs' =>
          constructor
          · rintro ⟨hm, hT⟩
            exact ⟨mem_congr_right (ed_den_congr P μ₁ μ₂ hA ρ) hm,
              (hrest (vcons x ρ) xs').mp hT⟩
          · rintro ⟨hm, hT⟩
            exact ⟨mem_congr_right (ed_den_congr P μ₂ μ₁ (fun ρ => (hA ρ).symm) ρ) hm,
              (hrest (vcons x ρ) xs').mpr hT⟩

/-- `FitSetT` at tables with `≈`-related field domains. -/
theorem FitSetT_den_congr (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (k : Nat) (Ds : List (Expr Nat)) (hden : ∀ e, e ∈ Ds → ∀ ρ,
      Equiv (den (mkM P μ₁) σ ρ e) (den (mkM P μ₂) σ ρ e)) :
    ∀ ρ, Equiv (FitSetT (mkM P μ₁) W4 k σ Ds ρ) (FitSetT (mkM P μ₂) W4 k σ Ds ρ) := by
  induction Ds with
  | nil => intro ρ; exact Equiv.rfl
  | cons A rest ih =>
      intro ρ
      have hA := hden A (List.mem_cons_self _ _)
      have hrest := ih (fun e he => hden e (List.mem_cons_of_mem _ he))
      refine sUnion_congr (sImage_congr (fun x x' hx => sImage_congr
        (fun t t' ht => ordPair_congr hx ht) ?_) ?_)
      · exact (hrest (vcons x ρ)).trans
          (FitSetT_congr (mkM P μ₂) W4 k σ rest (vcons_congr hx (fun _ => Equiv.rfl)))
      exact truncW_congr (mkM P μ₁) W4 k (ed_den_congr P μ₁ μ₂ hA ρ)

/-- `BoundT` at tables with `≈`-related field domains. -/
theorem BoundT_den_congr (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (k : Nat) (cs : List (List (Expr Nat) × List (Expr Nat)))
    (hden : ∀ c, c ∈ cs → ∀ e, e ∈ c.1 → ∀ ρ,
      Equiv (den (mkM P μ₁) σ ρ e) (den (mkM P μ₂) σ ρ e)) (ρp : Nat → PSet.{4}) :
    Equiv (BoundT (mkM P μ₁) W4 k σ ρp 0 cs) (BoundT (mkM P μ₂) W4 k σ ρp 0 cs) := by
  suffices ∀ j, Equiv (BoundT (mkM P μ₁) W4 k σ ρp j cs) (BoundT (mkM P μ₂) W4 k σ ρp j cs) from this 0
  induction cs with
  | nil => intro j; exact Equiv.rfl
  | cons c rest ih =>
      intro j
      refine sUnion_congr (pair_congr (sImage_congr (fun _ _ ht => dataOfTup_congr j ht)
        (FitSetT_den_congr P μ₁ μ₂ σ k c.1
          (fun e he => hden c (List.mem_cons_self _ _) e he) ρp)) ?_)
      exact ih (fun c' hc => hden c' (List.mem_cons_of_mem _ hc)) (j + 1)

/-- `CtorFits` at tables with `≈`-related field domains. -/
theorem CtorFits_den_congr (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (cs : List (List (Expr Nat) × List (Expr Nat)))
    (hden : ∀ c, c ∈ cs → (∀ e, e ∈ c.1 → ∀ ρ,
        Equiv (den (mkM P μ₁) σ ρ e) (den (mkM P μ₂) σ ρ e)) ∧
      (∀ e, e ∈ c.2 → ∀ ρ, Equiv (den (mkM P μ₁) σ ρ e) (den (mkM P μ₂) σ ρ e))) :
    ∀ ρp is j xs, CtorFits (mkM P μ₁) σ cs ρp is j xs ↔ CtorFits (mkM P μ₂) σ cs ρp is j xs := by
  intro ρp is j xs
  constructor
  · rintro ⟨c, hc, htf, hle⟩
    have hcm := List.getElem?_mem hc
    exact ⟨c, hc,
      (TelFits_den_congr P μ₁ μ₂ σ c.1 (fun e he => (hden c hcm).1 e he) ρp xs).mp htf,
      LEq.trans (LEq.symm
        (LEq_map_of c.2 (fun e he => (hden c hcm).2 e he (push xs ρp)))) hle⟩
  · rintro ⟨c, hc, htf, hle⟩
    have hcm := List.getElem?_mem hc
    exact ⟨c, hc,
      (TelFits_den_congr P μ₁ μ₂ σ c.1 (fun e he => (hden c hcm).1 e he) ρp xs).mpr htf,
      LEq.trans (LEq_map_of c.2 (fun e he => (hden c hcm).2 e he (push xs ρp))) hle⟩

/-- `famEnd` at tables with `≈`-related field domains. -/
theorem famEnd_den_congr (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (fd : FamData)
    (hden : ∀ c, c ∈ fd.ctors → (∀ e, e ∈ c.1 → ∀ ρ,
        Equiv (den (mkM P μ₁) σ ρ e) (den (mkM P μ₂) σ ρ e)) ∧
      (∀ e, e ∈ c.2 → ∀ ρ, Equiv (den (mkM P μ₁) σ ρ e) (den (mkM P μ₂) σ ρ e))) :
    ∀ ρ, Equiv (famEnd (mkM P μ₁) W4 σ fd ρ) (famEnd (mkM P μ₂) W4 σ fd ρ) := by
  intro ρ
  refine cond_congr Iff.rfl (tyv_congr ?_) (tyv_congr ?_)
  · refine tv_congr ⟨fun ⟨j, xs, h⟩ => ⟨j, xs, ?_⟩, fun ⟨j, xs, h⟩ => ⟨j, xs, ?_⟩⟩
    · exact (CtorFits_den_congr P μ₁ μ₂ σ fd.ctors hden _ _ j xs).mp h
    · exact (CtorFits_den_congr P μ₂ μ₁ σ fd.ctors
        (fun c hc => ⟨fun e he ρ => ((hden c hc).1 e he ρ).symm,
          fun e he ρ => ((hden c hc).2 e he ρ).symm⟩) _ _ j xs).mp h
  · refine sep_congr
      (fun a b hab ⟨j, xs, hcf, he⟩ => ⟨j, xs,
        (CtorFits_den_congr P μ₁ μ₂ σ fd.ctors hden _ _ j xs).mp hcf, hab.symm.trans he⟩)
      (fun a b hab ⟨j, xs, hcf, he⟩ => ⟨j, xs,
        (CtorFits_den_congr P μ₂ μ₁ σ fd.ctors
          (fun c hc => ⟨fun e he ρ => ((hden c hc).1 e he ρ).symm,
            fun e he ρ => ((hden c hc).2 e he ρ).symm⟩) _ _ j xs).mp hcf, hab.symm.trans he⟩)
      (BoundT_den_congr P μ₁ μ₂ σ (evalTotal σ fd.resLevel) fd.ctors
        (fun c hc e he => (hden c hc).1 e he) _)

/-- `famVal` at tables with `≈`-related field domains and `=`-related
telescope domains. -/
theorem famVal_den_congr (P : Premises4) (μ₁ μ₂ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (fd : FamData)
    (hdenC : ∀ c, c ∈ fd.ctors → (∀ e, e ∈ c.1 → ∀ ρ,
        Equiv (den (mkM P μ₁) σ ρ e) (den (mkM P μ₂) σ ρ e)) ∧
      (∀ e, e ∈ c.2 → ∀ ρ, Equiv (den (mkM P μ₁) σ ρ e) (den (mkM P μ₂) σ ρ e)))
    (hdenT : ∀ e, e ∈ fd.params ++ fd.indices → ∀ ρ,
      den (mkM P μ₁) σ ρ e = den (mkM P μ₂) σ ρ e) :
    Equiv (famVal (mkM P μ₁) W4 σ fd) (famVal (mkM P μ₂) W4 σ fd) :=
  piLam_congr_fits₂ (mkM P μ₁) (mkM P μ₂) rfl σ
    (famEnd_resp (mkM P μ₁) W4 σ fd) (famEnd_resp (mkM P μ₂) W4 σ fd)
    (.sort fd.resLevel) (fun A B h => Expr.noConfusion h)
    (fd.params ++ fd.indices) ρ0 (fun ρ A hA => hdenT A hA ρ)
    (fun xs _ => famEnd_den_congr P μ₁ μ₂ σ fd hdenC (push xs ρ0))

/-! ### §2 `den` at `≈`-related family entries -/

/-- `denLit` at two `upd`-tables that keep the literal entries. -/
theorem denLit_upd_eq (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (hf : f ≠ 1 ∧ f ≠ 2) {X₁ X₂ : List Nat → PSet.{4}} :
    ∀ t, denLit (mkM P (upd μ f X₁)) t = denLit (mkM P (upd μ f X₂)) t
  | 0 => by
      show (upd μ f X₁) 1 [] = (upd μ f X₂) 1 []
      rw [upd_ne μ f X₁ hf.1.symm, upd_ne μ f X₂ hf.1.symm]
  | t + 1 => by
      show fapp ((upd μ f X₁) 2 []) (denLit _ t) = fapp ((upd μ f X₂) 2 []) (denLit _ t)
      rw [upd_ne μ f X₁ hf.2.symm, upd_ne μ f X₂ hf.2.symm, denLit_upd_eq P μ f hf t]

/-- `den` at two `upd`-tables whose family entries are `≈` at every level
vector.  No canonicity premise — the hypothesis is quantified over all `ls`. -/
theorem den_upd_congr (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (hf : f ≠ 1 ∧ f ≠ 2) {X₁ X₂ : List Nat → PSet.{4}} (σ : Nat → Nat)
    (hX : ∀ ls : List Level, Equiv (X₁ (ls.map (evalTotal σ))) (X₂ (ls.map (evalTotal σ)))) :
    (e : Expr Nat) → ∀ ρ,
      Equiv (den (mkM P (upd μ f X₁)) σ ρ e) (den (mkM P (upd μ f X₂)) σ ρ e)
  | .bvar i, ρ => Equiv.rfl
  | .sort l, ρ => Equiv.rfl
  | .const r ls, ρ => by
      show Equiv ((upd μ f X₁) r (ls.map (evalTotal σ))) ((upd μ f X₂) r (ls.map (evalTotal σ)))
      by_cases hr : r = f
      · rw [hr, upd_eq μ f X₁ (ls.map (evalTotal σ)), upd_eq μ f X₂ (ls.map (evalTotal σ))]
        exact hX ls
      · rw [upd_ne μ f X₁ hr, upd_ne μ f X₂ hr]
        exact Equiv.rfl
  | .app a b, ρ =>
      fapp_congr (den_upd_congr P μ f hf σ hX a ρ) (den_upd_congr P μ f hf σ hX b ρ)
  | .lam A b, ρ => by
      refine lamVal_congr (mkM P (upd μ f X₁)) (den_upd_congr P μ f hf σ hX A ρ)
        (fun x x' hx => ?_)
      exact (den_upd_congr P μ f hf σ hX b (vcons x ρ)).trans
        (den_congr (mkM P (upd μ f X₂)) σ b (vcons_congr hx (fun _ => Equiv.rfl)))
  | .pi A B, ρ => by
      refine piVal_congr (mkM P (upd μ f X₁)) (den_upd_congr P μ f hf σ hX A ρ)
        (fun x x' hx => ?_)
      exact (den_upd_congr P μ f hf σ hX B (vcons x ρ)).trans
        (den_congr (mkM P (upd μ f X₂)) σ B (vcons_congr hx (fun _ => Equiv.rfl)))
  | .letE _ v b, ρ => by
      refine (den_upd_congr P μ f hf σ hX b
        (vcons (den (mkM P (upd μ f X₁)) σ ρ v) ρ)).trans ?_
      refine den_congr (mkM P (upd μ f X₂)) σ b ?_
      exact vcons_congr (den_upd_congr P μ f hf σ hX v ρ) (fun _ => Equiv.rfl)
  | .lit t, ρ => by
      have h := denLit_upd_eq (X₁ := X₁) (X₂ := X₂) P μ f hf t
      show Equiv (denLit (mkM P (upd μ f X₁)) t) (denLit (mkM P (upd μ f X₂)) t)
      rw [h]
      exact Equiv.rfl

section Iter

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)

/-! ### §3 the `PhiF`-iterates -/

/-- The `PhiF`-iterates from `∅`. -/
def iterPhi : Nat → (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4}
  | 0 => fun σ ρp => pempty
  | n + 1 => PhiF P μ fd (iterPhi n)

variable {P μ fd}

/-- Members of `iterPhi` are nonempty. -/
theorem iterPhi_ne (n : Nat) (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (z : PSet.{4})
    (hz : z ∈ iterPhi P μ fd n σ ρp) : ¬ Equiv z pempty := by
  cases n with
  | zero => exact absurd hz not_mem_pempty
  | succ n =>
      have hz' : z ∈ PsiF P μ fd σ ρp (iterPhi P μ fd n σ ρp) := hz
      obtain ⟨i, ⟨j, c, xs, hcj, hiz, hIn⟩, hi⟩ := mem_sep.mp hz'
      exact fun hp => dataVal_ne_pempty j xs (hiz.symm.trans (hi.trans hp))

/-- `iterPhi` respects level valuations agreeing below `ar`. -/
theorem iterPhi_levels (ar : Nat) (hB : FamBounded fd ar) : ∀ (n : Nat) {σ σ' : Nat → Nat},
    (∀ i, i < ar → σ i = σ' i) → ∀ ρ, Equiv (iterPhi P μ fd n σ ρ) (iterPhi P μ fd n σ' ρ)
  | 0, _, _, _, _ => Equiv.rfl
  | n + 1, σ, σ', hσ, ρ =>
      (PsiF_levels P μ fd hB hσ ρ (iterPhi P μ fd n σ ρ)).trans
        (PsiF_env P μ fd σ' (fun _ => Equiv.rfl) (iterPhi_levels ar hB n hσ ρ))

/-- Iterates grow. -/
theorem iterPhi_mono (n : Nat) (σ : Nat → Nat) (ρp : Nat → PSet.{4}) :
    Sub (iterPhi P μ fd n σ ρp) (iterPhi P μ fd (n + 1) σ ρp) := by
  cases n with
  | zero => intro z hz; exact absurd hz not_mem_pempty
  | succ n => exact PsiF_mono P μ fd σ ρp (iterPhi_mono n σ ρp)

/-- Iterates below any later iterate. -/
theorem iterPhi_le' (σ : Nat → Nat) (ρp : Nat → PSet.{4}) : ∀ {m n : Nat}, m ≤ n →
    Sub (iterPhi P μ fd m σ ρp) (iterPhi P μ fd n σ ρp)
  | 0, 0, _ => fun z hz => absurd hz not_mem_pempty
  | 0, n + 1, _ => fun z hz => absurd hz not_mem_pempty
  | m + 1, 0, h => absurd h (Nat.not_succ_le_zero m)
  | m + 1, n + 1, h => by
      rcases Nat.lt_or_ge (m + 1) (n + 1) with hlt | hge
      · exact fun z hz =>
          (iterPhi_mono n σ ρp) z ((iterPhi_le' σ ρp (Nat.le_of_lt_succ hlt)) z hz)
      · obtain hmn : m = n := by omega
        subst hmn
        exact fun _ hz => hz

/-- Every iterate stays below the least fixed point (Type levels). -/
theorem iterPhi_le (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (hk : evalTotal σ fd.resLevel ≠ 0) :
    ∀ n, Sub (iterPhi P μ fd n σ ρp) (DStar P μ fd σ ρp)
  | 0 => fun z hz => absurd hz not_mem_pempty
  | n + 1 => fun z hz =>
      ((DStar_lfp P μ fd σ ρp hk (hN σ ρp)).1).1 z
        (PsiF_mono P μ fd σ ρp (iterPhi_le hN σ ρp hk n) z hz)

/-- The iterates lie in the `W4` bound (by subset-closure from `DStar`). -/
theorem iterPhi_mem (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (hk : evalTotal σ fd.resLevel ≠ 0) (n : Nat) :
    iterPhi P μ fd n σ ρp ∈ W4 (evalTotal σ fd.resLevel) :=
  (stageW4 P (evalTotal σ fd.resLevel)).subset (DStar_mem P μ fd hN σ ρp)
    (fun z hz => iterPhi_le hN σ ρp hk n z hz)

/-- `iterPhi` respects `≈` in the parameter environment. -/
theorem iterPhi_env :
    ∀ (n : Nat) (σ : Nat → Nat) {ρp ρp' : Nat → PSet.{4}}, (∀ i, Equiv (ρp i) (ρp' i)) →
      Equiv (iterPhi P μ fd n σ ρp) (iterPhi P μ fd n σ ρp')
  | 0, _, _, _, _ => Equiv.rfl
  | n + 1, σ, ρp, ρp', hρ => PsiF_env P μ fd σ hρ (iterPhi_env n σ hρ)

end Iter

/-! ### §4 the finitary guard rebuild (no `.fn` arms) -/

/-- A guard derivation without `.fn` arms uses the candidate set only at
finitely many values, and rebuilds at any candidate containing them. -/
theorem InPhi_witness_noFn (Sm : Sem.{w}) :
    (ps : List PKind) → (hnoFn : ∀ p, p ∈ ps → p ≠ .fn) →
    (xs : List PSet.{w}) → (k : Nat) → (pre : List PSet.{w}) →
    ∀ {X : PSet.{w}}, Sm.InPhi X ps xs k pre →
    ∃ vals : List PSet.{w}, (∀ v, v ∈ vals → v ∈ X) ∧
      ∀ {Y : PSet.{w}}, (∀ v, v ∈ vals → v ∈ Y) → Sm.InPhi Y ps xs k pre
  | [], _, [], _, _, _, h => ⟨[], fun v hv => absurd hv (List.not_mem_nil v), fun _ => h⟩
  | .plain :: ps, hnoFn, x :: xs, k, pre, X, ⟨hp, h⟩ => by
      obtain ⟨vals, hmem, hrec⟩ := InPhi_witness_noFn Sm ps
        (fun p hp => hnoFn p (List.mem_cons_of_mem _ hp)) xs (k + 1) (pre ++ [x]) h
      exact ⟨vals, hmem, fun hY => ⟨hp, hrec hY⟩⟩
  | .direct :: ps, hnoFn, x :: xs, k, pre, X, ⟨⟨hx, hr⟩, h⟩ => by
      obtain ⟨vals, hmem, hrec⟩ := InPhi_witness_noFn Sm ps
        (fun p hp => hnoFn p (List.mem_cons_of_mem _ hp)) xs (k + 1) (pre ++ [x]) h
      refine ⟨x :: vals, ?_, fun hY => ⟨⟨hY x (List.mem_cons_self _ _), hr⟩, hrec (fun v hv =>
        hY v (List.mem_cons_of_mem _ hv))⟩⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hx
      · exact hmem v hv
  | .fn :: _, hnoFn, _, _, _, _, _ => absurd rfl (hnoFn _ (List.mem_cons_self _ _))
  | p :: _, _, [], _, _, _, h => by cases p <;> exact False.elim h
  | [], _, _ :: _, _, _, _, h => False.elim h

/-- A finite list of union members sits below one iterate. -/
theorem stages_bounded {F : Nat → (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4}}
    (hmono : ∀ m n, m ≤ n → ∀ σ ρp, Sub (F m σ ρp) (F n σ ρp))
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) :
    (vals : List PSet.{4}) → (∀ v, v ∈ vals → ∃ n, v ∈ F n σ ρp) →
    ∃ N, ∀ v, v ∈ vals → v ∈ F N σ ρp
  | [], _ => ⟨0, fun v hv => absurd hv (List.not_mem_nil v)⟩
  | v :: vals, h => by
      obtain ⟨n₁, hn₁⟩ := h v (List.mem_cons_self _ _)
      obtain ⟨N₂, hN₂⟩ := stages_bounded hmono σ ρp vals
        (fun v' hv' => h v' (List.mem_cons_of_mem _ hv'))
      refine ⟨max n₁ N₂, fun v' hv' => ?_⟩
      rcases List.mem_cons.mp hv' with rfl | hv'
      · exact hmono n₁ (max n₁ N₂) (Nat.le_max_left _ _) σ ρp v' hn₁
      · exact hmono N₂ (max n₁ N₂) (Nat.le_max_right _ _) σ ρp v' (hN₂ v' hv')

section Union

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)

/-- The union of the nonempty iterates. -/
def iterPhiUnion (σ : Nat → Nat) (ρp : Nat → PSet.{4}) : PSet.{4} :=
  iUnionN fun n => iterPhi P μ fd (n + 1) σ ρp

variable {P μ fd}

/-- **Residue** `[rcic-f3-famkt-bridge-fn-cont]` — **CLOSED (refuted, session 25)**:
`FnContUnion` is FALSE in general — `Rcic.F3.FamKTFnReal.fnContUnion_false`
builds a witness family where `fxZW ∈ PsiF … (iterPhiUnion …)` yet
`fxZW ∉ iterPhiUnion …` (height-unbounded `.fn` graph).  The statement is
kept as the refuted analogue; `iterPhiUnion_prefixed` shows `hnoFn` suffices.
At `.fn` fields the guard reads `x ∈ piSet (domBig) (fib X)`, whose graph
values may sit in `fib X` at unboundedly many stages — no finite `N`
rebuilds the guard, which is exactly what the counter-model realizes. -/
def FnContUnion (σ : Nat → Nat) (ρp : Nat → PSet.{4}) : Prop :=
  Sub (PsiF P μ fd σ ρp (iterPhiUnion P μ fd σ ρp)) (iterPhiUnion P μ fd σ ρp)

/-- The union of iterates is pre-fixed, absent `.fn`-kinded fields. -/
theorem iterPhiUnion_prefixed (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hnoFn : ∀ c, c ∈ fd.ctors → ∀ p, p ∈ kindsOf fd.fref c.1 → p ≠ .fn) :
    Sub (PsiF P μ fd σ ρp (iterPhiUnion P μ fd σ ρp)) (iterPhiUnion P μ fd σ ρp) := by
  intro z hz
  obtain ⟨i, ⟨j, c, xs, hcj, hiz, hIn⟩, hi⟩ := mem_sep.mp hz
  have hcm := List.getElem?_mem hcj
  obtain ⟨vals, hmem, hrec⟩ := InPhi_witness_noFn (semF P μ fd σ ρp c.1)
    (kindsOf fd.fref c.1) (fun p hp => hnoFn c hcm p hp) xs 0 [] hIn
  obtain ⟨N, hN⟩ := stages_bounded
    (F := fun n σ' ρp' => iterPhi P μ fd (n + 1) σ' ρp')
    (fun m n hle σ' ρp' => iterPhi_le' σ' ρp' (Nat.succ_le_succ hle)) σ ρp vals
    (fun v hv => by obtain ⟨n, hn⟩ := mem_iUnionN.mp (hmem v hv); exact ⟨n, hn⟩)
  have hP : z ∈ PsiF P μ fd σ ρp (iterPhi P μ fd (N + 1) σ ρp) :=
    mem_sep.mpr ⟨i, ⟨j, c, xs, hcj, hiz, hrec hN⟩, hi⟩
  have hzI : z ∈ iterPhi P μ fd (N + 2) σ ρp := by
    show z ∈ PsiF P μ fd σ ρp (iterPhi P μ fd (N + 1) σ ρp)
    exact hP
  exact mem_iUnionN.mpr ⟨N + 1, hzI⟩

/-- By leastness, `DStar` sits below the union (absent `.fn` fields). -/
theorem DStar_sub_union (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (hk : evalTotal σ fd.resLevel ≠ 0)
    (hnoFn : ∀ c, c ∈ fd.ctors → ∀ p, p ∈ kindsOf fd.fref c.1 → p ≠ .fn) :
    Sub (DStar P μ fd σ ρp) (iterPhiUnion P μ fd σ ρp) :=
  DStar_least P μ fd hN σ ρp hk (iterPhiUnion_prefixed σ ρp hnoFn)

end Union

/-! ### §5 the alignment cell and the `≤` direction

**Two refutations measured before this restatement** (2026-10-31 session):

* The in-tree `famOfD` glue (`famVal_famOfD`, `TypeFib_famOfD`,
  `telFitsT_iff_InPhi`) requires `hD4 : ∀ σ ρ, D σ ρ ∈ W4 (evalTotal σ
  fd.resLevel)` — and its proof consumes `hD4` as *set membership* (see
  `truncW_direct_field`, RcicF3KTWFamField: `hW := (stageW4 _).subset
  (hD4 σ _) (fun _ => mem_sep_subset)`). For `D := iterPhi n` this premise is
  not available: `PsiF`-iterates are separations over `W4 k` directly, and
  `sep p (W4 k) ∈ W4 k` would need `W4 k ∈ W4 k`. The KT lane only ever
  instantiates the glue at `DStar` (whose membership comes from the `gSet`
  construction), so the alignment cannot be routed through it.
* An unconditional per-entry induction (`famIter n ls-entry ≈ …` for ALL
  level vectors) is ill-formed: the entry guard `evalTotal (σOf vs')
  fd.resLevel ≠ 0` fails at Prop-reading entries of the table (the F3 side
  dispatches to `PropFib` there; the Type-level `PsiF`-story does not apply).

The honest residual was the **fibre-level alignment cell** `FibAlign` below:
per `σ` with a Type-reading result level, the `n`-th F3 iterate's fibre is
the `(n+1)`-st `PhiF`-iterate's `fibAt`.  **Discharged in §6** as
`famEnd_famEndD_iter` (the refutations forced the `iterPhiD` dispatch and
the canonical-entry table congruence); the def stays for `limEnd_sub`'s
premise shape. -/

section Bridge

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)

/-- **Residue** `[rcic-f3-famkt-bridge-fib-align]`: at every `σ` whose result
level reads nonzero, the `n`-th F3 iterate's end fibre is the `(n+1)`-st
`PhiF`-iterate's `fibAt` fibre. -/
def FibAlign (n : Nat) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) : Prop :=
  Equiv (famEnd (mkM P (upd μ fd.fref (famIter P μ fd n))) W4 σ fd ρ)
    (famEndD P μ fd (iterPhi P μ fd (n + 1)) σ ρ)

variable {P μ fd}

/-- The unconditional `≤` direction at the fibre level, conditional on the
alignment cell: every element of the union of iterates' fibres is in the
lfp's `fibAt`. -/
theorem limEnd_sub (σ : Nat → Nat) (ps is : List PSet.{4})
    (hps : ps.length = fd.params.length) (his : is.length = fd.indices.length)
    (hk : evalTotal σ fd.resLevel ≠ 0)
    (halign : ∀ n, FibAlign P μ fd n σ (push (ps ++ is) ρ0))
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1) :
    ∀ z, z ∈ iUnionN (fun n => El (famEnd (mkM P (upd μ fd.fref (famIter P μ fd n))) W4 σ fd
        (push (ps ++ is) ρ0))) →
      z ∈ fibAt P μ fd (DStar P μ fd) σ (push ps ρ0) is := by
  intro z hz
  obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
  have hA : Equiv (famEnd (mkM P (upd μ fd.fref (famIter P μ fd n))) W4 σ fd
      (push (ps ++ is) ρ0))
    (famEndD P μ fd (iterPhi P μ fd (n + 1)) σ (push (ps ++ is) ρ0)) := halign n
  have h1 : z ∈ El (famEndD P μ fd (iterPhi P μ fd (n + 1)) σ (push (ps ++ is) ρ0)) :=
    mem_congr_right (el_congr hA) hn
  have hstep : z ∈ fibAt P μ fd (iterPhi P μ fd (n + 1)) σ
      (shiftρ fd.indices.length (push (ps ++ is) ρ0))
      (lastVals fd.indices.length (push (ps ++ is) ρ0)) :=
    mem_congr_right (el_tyv (S := fibAt P μ fd (iterPhi P μ fd (n + 1)) σ
      (shiftρ fd.indices.length (push (ps ++ is) ρ0))
      (lastVals fd.indices.length (push (ps ++ is) ρ0)))) h1
  rw [push_append, ← his, shiftρ_push, lastVals_push] at hstep
  obtain ⟨i, hiP, hie⟩ := mem_sep.mp hstep
  have hzI : z ∈ iterPhi P μ fd (n + 1) σ (push ps ρ0) := ⟨i, hie⟩
  have hzD : z ∈ DStar P μ fd σ (push ps ρ0) :=
    iterPhi_le hN σ (push ps ρ0) hk (n + 1) z hzI
  obtain ⟨i', hi'⟩ := hzD
  refine mem_sep.mpr ⟨i', ?_, hi'⟩
  exact (resTupF_congr P μ fd σ (push ps ρ0) hi').trans
    ((resTupF_congr P μ fd σ (push ps ρ0) hie.symm).trans hiP)

end Bridge

/-! ### §6 the alignment chain (2026-10-31 session)

The §5 refutations are superseded in the DIRECT-RECURSIVE case: the hD4
premise is manufactured by *dispatching* the iterates (`iterPhiD` — empty at
Prop-reads, the raw operator at Type-reads; `DStar_zero` is the landed
precedent for exactly this dispatch), and the table congruence is keyed to
the **canonical entry only** — `DirectRec` fields read the family at
`canonL ar` (RcicF3RecValRec:86), so `den` never reads a Prop-reading entry.
The chain: `famIter_famOfD` (entry level, induction on `n`) →
`famEnd_famEndD_iter` (fibre level = the §5 cell `FibAlign`, discharged) →
`limEnd_sub` drops its `halign` premise. -/

open Rcic.Model.PS (denRefs denRefsLit)

section Align

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)

/-- Literals only contribute `1`/`2` to `denRefs`. -/
theorem not_mem_denRefsLit {f : Nat} (hf : f ≠ 1 ∧ f ≠ 2) : (t : Nat) → f ∈ denRefsLit t → False
  | 0, h => by
      simp only [denRefsLit, List.mem_singleton] at h
      exact hf.1 h
  | t + 1, h => by
      simp only [denRefsLit, List.mem_cons] at h
      rcases h with rfl | h
      · exact hf.2 rfl
      · exact not_mem_denRefsLit hf t h

/-- A family-free expression does not mention `fref` in `denRefs` —
literals only contribute `1`/`2`, excluded by `hf`. -/
theorem not_mem_denRefs_of_occursConst {f : Nat} (hf : f ≠ 1 ∧ f ≠ 2) :
    (e : Expr Nat) → occursConst f e = false → f ∈ denRefs e → False
  | .bvar _, _, hm => by simp only [denRefs] at hm; exact absurd hm (List.not_mem_nil f)
  | .sort _, _, hm => by simp only [denRefs] at hm; exact absurd hm (List.not_mem_nil f)
  | .const r _, hocc, hm => by
      simp only [denRefs, List.mem_singleton] at hm
      subst hm
      simp only [occursConst] at hocc
      simp at hocc
  | .app a b, hocc, hm => by
      simp only [denRefs] at hm
      simp only [occursConst, Bool.or_eq_false_iff] at hocc
      rcases List.mem_append.mp hm with h | h
      · exact not_mem_denRefs_of_occursConst hf a hocc.1 h
      · exact not_mem_denRefs_of_occursConst hf b hocc.2 h
  | .lam a b, hocc, hm => by
      simp only [denRefs] at hm
      simp only [occursConst, Bool.or_eq_false_iff] at hocc
      rcases List.mem_append.mp hm with h | h
      · exact not_mem_denRefs_of_occursConst hf a hocc.1 h
      · exact not_mem_denRefs_of_occursConst hf b hocc.2 h
  | .pi a b, hocc, hm => by
      simp only [denRefs] at hm
      simp only [occursConst, Bool.or_eq_false_iff] at hocc
      rcases List.mem_append.mp hm with h | h
      · exact not_mem_denRefs_of_occursConst hf a hocc.1 h
      · exact not_mem_denRefs_of_occursConst hf b hocc.2 h
  | .letE a v b, hocc, hm => by
      simp only [denRefs] at hm
      simp only [occursConst, Bool.or_eq_false_iff] at hocc
      rcases List.mem_append.mp hm with h | h
      · rcases List.mem_append.mp h with h | h
        · exact not_mem_denRefs_of_occursConst hf a hocc.1.1 h
        · exact not_mem_denRefs_of_occursConst hf v hocc.1.2 h
      · exact not_mem_denRefs_of_occursConst hf b hocc.2 h
  | .lit t, _, hm => not_mem_denRefsLit hf t (by simpa only [denRefs] using hm)

/-- `den` at two `upd`-tables agrees (with `=`) at family-free expressions. -/
theorem den_upd_eq_famFree {X₁ X₂ : List Nat → PSet.{4}} (σ : Nat → Nat)
    (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2)
    (e : Expr Nat) (he : occursConst fd.fref e = false) (ρ : Nat → PSet.{4}) :
    den (mkM P (upd μ fd.fref X₁)) σ ρ e = den (mkM P (upd μ fd.fref X₂)) σ ρ e := by
  refine den_agreeOn P (μ₁ := upd μ fd.fref X₁) (μ₂ := upd μ fd.fref X₂)
    (S := fun r => r ≠ fd.fref) ?_ σ e ?_ ρ
  · intro r hr ls
    rw [upd_ne μ fd.fref X₁ hr, upd_ne μ fd.fref X₂ hr]
  · intro r hr hrc
    subst hrc
    exact not_mem_denRefs_of_occursConst hf e he hr

/-- `den` at two `upd`-tables is `≈` at a directly recursive field: the
family is read only at the canonical instance. -/
theorem den_upd_congr_rec {X₁ X₂ : List Nat → PSet.{4}} (σ : Nat → Nat)
    (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2)
    (hX : Equiv (X₁ ((canonL ar).map (evalTotal σ))) (X₂ ((canonL ar).map (evalTotal σ))))
    (np nq d : Nat) (idx : List (Expr Nat))
    (hidx : ∀ e, e ∈ idx → occursConst fd.fref e = false) (ρ : Nat → PSet.{4}) :
    Equiv (den (mkM P (upd μ fd.fref X₁)) σ ρ
        (foldApps (.const fd.fref (canonL ar)) (policyParameterLocals np d ++ idx)))
      (den (mkM P (upd μ fd.fref X₂)) σ ρ
        (foldApps (.const fd.fref (canonL ar)) (policyParameterLocals np d ++ idx))) := by
  have hmap : ((policyParameterLocals np d ++ idx).map
        (fun e => den (mkM P (upd μ fd.fref X₁)) σ ρ e)) =
      ((policyParameterLocals np d ++ idx).map
        (fun e => den (mkM P (upd μ fd.fref X₂)) σ ρ e)) := by
    refine List.map_congr_left fun e he => ?_
    rcases List.mem_append.mp he with h | h
    · exact den_upd_eq_famFree P μ fd σ hf e (by
        simp only [policyParameterLocals, List.mem_map, List.mem_range] at h
        rcases h with ⟨i, _, rfl⟩
        simp [occursConst]) ρ
    · exact den_upd_eq_famFree P μ fd σ hf e (hidx e h) ρ
  rw [den_foldApps, den_foldApps, hmap]
  refine fapps_congr ?_ _
  · show Equiv ((upd μ fd.fref X₁) fd.fref ((canonL ar).map (evalTotal σ)))
      ((upd μ fd.fref X₂) fd.fref ((canonL ar).map (evalTotal σ)))
    rw [upd_eq μ fd.fref X₁, upd_eq μ fd.fref X₂]
    exact hX

/-- The §1 `famEnd_den_congr` premise, from an entry `≈` at the canonical
instance (direct-recursive fields only). -/
theorem famFields_den_of_entry {X₁ X₂ : List Nat → PSet.{4}} (σ : Nat → Nat)
    (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2)
    (hcls : ∀ c, c ∈ fd.ctors →
      FieldsClass fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hX : Equiv (X₁ ((canonL ar).map (evalTotal σ))) (X₂ ((canonL ar).map (evalTotal σ)))) :
    ∀ c, c ∈ fd.ctors → (∀ e, e ∈ c.1 → ∀ ρ,
        Equiv (den (mkM P (upd μ fd.fref X₁)) σ ρ e) (den (mkM P (upd μ fd.fref X₂)) σ ρ e)) ∧
      (∀ e, e ∈ c.2 → ∀ ρ,
        Equiv (den (mkM P (upd μ fd.fref X₁)) σ ρ e) (den (mkM P (upd μ fd.fref X₂)) σ ρ e)) := by
  intro c hc
  refine ⟨?_, fun e he ρ => by
    have h := den_upd_eq_famFree (X₁ := X₁) (X₂ := X₂) P μ fd σ hf e (hri c hc e he) ρ
    rw [h]
    exact Equiv.rfl⟩
  have hwalk : ∀ (Fs : List (Expr Nat)) (d : Nat),
      FieldsClass fd.fref ar fd.params.length fd.indices.length Fs d →
      ∀ e, e ∈ Fs → ∀ ρ,
        Equiv (den (mkM P (upd μ fd.fref X₁)) σ ρ e) (den (mkM P (upd μ fd.fref X₂)) σ ρ e) := by
    intro Fs d hcl
    induction Fs generalizing d with
    | nil => intro e he; exact absurd he (List.not_mem_nil e)
    | cons A Fs ih =>
        intro e he ρ
        obtain ⟨hA, hFs⟩ := hcl
        rcases List.mem_cons.mp he with rfl | he
        · rcases hA with h | h
          · rw [den_upd_eq_famFree P μ fd σ hf e h ρ]; exact Equiv.rfl
          · obtain ⟨idx, rfl, _, hidx⟩ := h
            exact den_upd_congr_rec P μ fd ar σ hf hX fd.params.length fd.indices.length _ idx hidx ρ
        · exact ih (d + 1) hFs e he ρ
  exact hwalk c.1 0 (hcls c hc)

variable {P μ fd ar}

/-- The level-dispatched `n`-th iterate: the raw `PhiF`-operator at
Type-reads, `∅` at Prop-reads.  `DStar_zero` is the landed precedent; the
dispatch manufactures the `hD1`–`hD4` pack the landed `famOfD`-glue needs
(raw iterates satisfy it only at Type-reads). -/
def iterPhiD (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (n : Nat)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) : PSet.{4} :=
  if evalTotal σ fd.resLevel = 0 then pempty else iterPhi P μ fd n σ ρp

/-- `FieldsClass` ⇒ `FieldsClassA` (the raw-field branch of the class-A
view), by recursion on the field list. -/
theorem fieldsClassA_lift (f ar np nq : Nat) :
    ∀ (Fs : List (Expr Nat)) (d : Nat),
    FieldsClass f ar np nq Fs d → FieldsClassA f ar np nq Fs d
  | [], _, _ => trivial
  | A :: Fs, d, hcl => by
      obtain ⟨hA, hFs⟩ := hcl
      exact ⟨hA.elim Or.inl (fun h => Or.inr (Or.inl h)),
        fieldsClassA_lift f ar np nq Fs (d + 1) hFs⟩

variable {n : Nat}

theorem iterPhiD_env (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) :
    ∀ (n : Nat) (σ : Nat → Nat) (ρ ρ' : Nat → PSet.{4}), (∀ i, Equiv (ρ i) (ρ' i)) →
      Equiv (iterPhiD P μ fd n σ ρ) (iterPhiD P μ fd n σ ρ') := by
  intro n σ ρ ρ' hρ
  by_cases hk : evalTotal σ fd.resLevel = 0
  · simp only [iterPhiD, if_pos hk]
    exact Equiv.rfl
  · simp only [iterPhiD, if_neg hk]
    exact iterPhi_env n σ hρ

theorem iterPhiD_levels (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (ar : Nat) (hB : FamBounded fd ar) :
    ∀ (n : Nat) (σ σ' : Nat → Nat), (∀ i, i < ar → σ i = σ' i) → ∀ ρ,
      Equiv (iterPhiD P μ fd n σ ρ) (iterPhiD P μ fd n σ' ρ) := by
  intro n σ σ' hσ ρ
  have hlv : evalTotal σ fd.resLevel = evalTotal σ' fd.resLevel :=
    evalTotal_agree hσ fd.resLevel hB.res
  by_cases hk : evalTotal σ fd.resLevel = 0
  · have hk' : evalTotal σ' fd.resLevel = 0 := by rw [← hlv]; exact hk
    simp only [iterPhiD, if_pos hk, if_pos hk']
    exact Equiv.rfl
  · have hk' : evalTotal σ' fd.resLevel ≠ 0 := by rw [← hlv]; exact hk
    simp only [iterPhiD, if_neg hk, if_neg hk']
    exact iterPhi_levels ar hB n hσ ρ

theorem iterPhiD_ne (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) :
    ∀ (n : Nat) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (z : PSet.{4}),
      z ∈ iterPhiD P μ fd n σ ρ → ¬ Equiv z pempty := by
  intro n σ ρ z hz
  by_cases hk : evalTotal σ fd.resLevel = 0
  · rw [iterPhiD, if_pos hk] at hz
    exact absurd hz not_mem_pempty
  · rw [iterPhiD, if_neg hk] at hz
    exact iterPhi_ne n σ ρ z hz

theorem iterPhiD_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1) :
    ∀ (n : Nat) (σ : Nat → Nat) (ρ : Nat → PSet.{4}),
      iterPhiD P μ fd n σ ρ ∈ W4 (evalTotal σ fd.resLevel) := by
  intro n σ ρ
  by_cases hk : evalTotal σ fd.resLevel = 0
  · rw [iterPhiD, if_pos hk]
    exact (stageW4 P _).empty
  · rw [iterPhiD, if_neg hk]
    exact iterPhi_mem hN σ ρ hk n

/-- The dispatched iterate is the raw one at Type-reads. -/
theorem iterPhiD_eq (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (n : Nat) (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (hk : evalTotal σ fd.resLevel ≠ 0) :
    iterPhiD P μ fd n σ ρp = iterPhi P μ fd n σ ρp := by
  simp only [iterPhiD, if_neg hk]

/-- `famOfD` reads its data-set only at the family instance's own `σ`. -/
theorem famOfD_ext (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (D₁ D₂ : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4}) (vs : List Nat)
    (hD : ∀ ρp, D₁ (σOf vs) ρp = D₂ (σOf vs) ρp) :
    famOfD P μ fd D₁ vs = famOfD P μ fd D₂ vs := by
  have hE : famEndD P μ fd D₁ (σOf vs) = famEndD P μ fd D₂ (σOf vs) := by
    funext ρ
    unfold famEndD fibAt
    rw [funext hD]
  unfold famOfD
  rw [hE]

/-- The canonical entry of a Type-read `σ` is a Type-read. -/
theorem canonEntry_typeRead (fd : FamData)
    (ar : Nat) (hB : FamBounded fd ar) (σ : Nat → Nat) (hk : evalTotal σ fd.resLevel ≠ 0) :
    evalTotal (σOf ((canonL ar).map (evalTotal σ))) fd.resLevel ≠ 0 := by
  rw [evalTotal_agree (σOf_canon σ ar) fd.resLevel hB.res]
  exact hk

/-- The stage step: `famIter (n+1)` at a Type-read instance equals
`famOfD (iterPhi (n+1))`, given the entry alignment at stage `n` (the
canonical instance's entry only). -/
theorem famIter_succ_famOfD (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (ar : Nat) (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2) (hB : FamBounded fd ar)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hcls : ∀ c, c ∈ fd.ctors →
      FieldsClass fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    {n : Nat} (vs : List Nat) (hk : evalTotal (σOf vs) fd.resLevel ≠ 0)
    (hEnt : Equiv (famIter P μ fd n ((canonL ar).map (evalTotal (σOf vs))))
        (famOfD P μ fd (iterPhi P μ fd n) ((canonL ar).map (evalTotal (σOf vs))))) :
    Equiv (famIter P μ fd (n + 1) vs) (famOfD P μ fd (iterPhi P μ fd (n + 1)) vs) := by
  have hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0 :=
    fun c hc => fieldsClassA_lift fd.fref ar fd.params.length fd.indices.length c.1 0 (hcls c hc)
  have hkC := canonEntry_typeRead fd ar hB (σOf vs) hk
  have hED : famOfD P μ fd (iterPhi P μ fd n) ((canonL ar).map (evalTotal (σOf vs)))
      = famOfD P μ fd (iterPhiD P μ fd n) ((canonL ar).map (evalTotal (σOf vs))) :=
    famOfD_ext P μ fd _ _ _ fun ρp => (iterPhiD_eq P μ fd n _ ρp hkC).symm
  have hdenT1 : ∀ e, e ∈ fd.params ++ fd.indices → ∀ ρ,
      den (mkM P (tabIter P μ fd n)) (σOf vs) ρ e
        = den (mkM P (upd μ fd.fref (famOfD P μ fd (iterPhi P μ fd n)))) (σOf vs) ρ e :=
    fun e he ρ => den_upd_eq_famFree P μ fd (σOf vs) hf e (hpf e he) ρ
  have hdenT2 : ∀ e, e ∈ fd.params ++ fd.indices → ∀ ρ,
      den (mkM P (upd μ fd.fref (famOfD P μ fd (iterPhi P μ fd n)))) (σOf vs) ρ e
        = den (mkM P (upd μ fd.fref (famOfD P μ fd (iterPhiD P μ fd n)))) (σOf vs) ρ e :=
    fun e he ρ => den_upd_eq_famFree P μ fd (σOf vs) hf e (hpf e he) ρ
  have hden2 := famFields_den_of_entry P μ fd ar (σOf vs) hf hcls hri
    (X₁ := famOfD P μ fd (iterPhi P μ fd n)) (X₂ := famOfD P μ fd (iterPhiD P μ fd n))
    (by rw [hED]; exact Equiv.rfl)
  have e1 : Equiv (famVal (mkM P (tabIter P μ fd n)) W4 (σOf vs) fd)
      (famVal (mkM P (upd μ fd.fref (famOfD P μ fd (iterPhi P μ fd n)))) W4 (σOf vs) fd) :=
    famVal_den_congr P (tabIter P μ fd n)
      (upd μ fd.fref (famOfD P μ fd (iterPhi P μ fd n))) (σOf vs) fd
      (famFields_den_of_entry P μ fd ar (σOf vs) hf hcls hri hEnt) hdenT1
  have e2 : Equiv (famVal (mkM P (upd μ fd.fref (famOfD P μ fd (iterPhi P μ fd n)))) W4 (σOf vs) fd)
      (famVal (mkM P (upd μ fd.fref (famOfD P μ fd (iterPhiD P μ fd n)))) W4 (σOf vs) fd) :=
    famVal_den_congr P _ _ (σOf vs) fd hden2 hdenT2
  have e3 : Equiv (famVal (mkM P (upd μ fd.fref (famOfD P μ fd (iterPhiD P μ fd n)))) W4 (σOf vs) fd)
      (famOfD P μ fd (PhiF P μ fd (iterPhiD P μ fd n)) vs) :=
    famVal_famOfD P μ fd ar (iterPhiD P μ fd n) hB hpf
      (iterPhiD_env P μ fd n) (iterPhiD_levels P μ fd ar hB n)
      (iterPhiD_ne P μ fd n) (iterPhiD_mem P μ fd hN n) hclsA hri hres vs hk
  have e4 : famOfD P μ fd (PhiF P μ fd (iterPhiD P μ fd n)) vs
      = famOfD P μ fd (iterPhi P μ fd (n + 1)) vs :=
    famOfD_ext P μ fd _ _ vs fun ρp => by
      show PsiF P μ fd (σOf vs) ρp (iterPhiD P μ fd n (σOf vs) ρp)
        = PsiF P μ fd (σOf vs) ρp (iterPhi P μ fd n (σOf vs) ρp)
      rw [iterPhiD_eq P μ fd n _ ρp hk]
  show Equiv (famVal (mkM P (tabIter P μ fd n)) W4 (σOf vs) fd) _
  exact ((e1.trans e2).trans e3).trans (e4 ▸ Equiv.rfl)

/-- `famZero` is `famOfD` of the empty (`0`-th) iterate: both are the
all-empty family. -/
theorem famZero_famOfD_zero (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (vs : List Nat) :
    Equiv (famZero P μ fd (σOf vs)) (famOfD P μ fd (iterPhi P μ fd 0) vs) := by
  show Equiv (piLam (mkM P μ) (σOf vs) (fun _ => tyv pempty) ρ0 (famType fd))
    (piLam (mkM P μ) (σOf vs) (famEndD P μ fd (iterPhi P μ fd 0) (σOf vs)) ρ0 (famType fd))
  unfold famType famEndD fibAt
  refine piLam_congr_fits₂ (mkM P μ) (mkM P μ) rfl (σOf vs) (envResp_const _)
    (famEndD_envResp P μ fd (iterPhi P μ fd 0)
      (fun σ' ρ ρ' hρ => iterPhi_env 0 σ' hρ) (σOf vs))
    (.sort fd.resLevel) (fun A B e => Expr.noConfusion e)
    (fd.params ++ fd.indices) ρ0 (fun _ _ _ => rfl) ?_
  intro xs _
  unfold famEndD fibAt
  have h0 : iterPhi P μ fd 0 (σOf vs) (shiftρ fd.indices.length (push xs ρ0)) = pempty := rfl
  rw [h0]
  exact (tyv_congr sep_pempty).symm

/-- **The entry-level alignment** (`Z` at `0`, the step above after): at
every Type-read instance, the `n`-th F3 iterate is the `n`-th KT
`famOfD`-iterate. -/
theorem famIter_famOfD (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (ar : Nat) (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2) (hB : FamBounded fd ar)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hcls : ∀ c, c ∈ fd.ctors →
      FieldsClass fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1) :
    ∀ (n : Nat) (vs : List Nat), evalTotal (σOf vs) fd.resLevel ≠ 0 →
      Equiv (famIter P μ fd n vs) (famOfD P μ fd (iterPhi P μ fd n) vs) := by
  intro n
  induction n with
  | zero =>
      intro vs _
      exact famZero_famOfD_zero P μ fd vs
  | succ n ih =>
      intro vs hk
      exact famIter_succ_famOfD P μ fd ar hf hB hpf hcls hri hres hN vs hk
        (ih ((canonL ar).map (evalTotal (σOf vs)))
          (canonEntry_typeRead fd ar hB (σOf vs) hk))

/-- **The fibre-level alignment** — the §5 cell `FibAlign`, discharged: at
Type-read `σ`, the `n`-th F3 iterate's end fibre is the `(n+1)`-st
`PhiF`-iterate's `fibAt`. -/
theorem famEnd_famEndD_iter (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (ar : Nat) (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2) (hB : FamBounded fd ar)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hcls : ∀ c, c ∈ fd.ctors →
      FieldsClass fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (n : Nat) (σ : Nat → Nat) (hk : evalTotal σ fd.resLevel ≠ 0)
    (ps is : List PSet.{4}) (hps : ps.length = fd.params.length)
    (his : is.length = fd.indices.length) :
    Equiv (famEnd (mkM P (tabIter P μ fd n)) W4 σ fd (push (ps ++ is) ρ0))
      (famEndD P μ fd (iterPhi P μ fd (n + 1)) σ (push (ps ++ is) ρ0)) := by
  have hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0 :=
    fun c hc => fieldsClassA_lift fd.fref ar fd.params.length fd.indices.length c.1 0 (hcls c hc)
  have hkC := canonEntry_typeRead fd ar hB σ hk
  have hEnt := famIter_famOfD P μ fd ar hf hB hpf hcls hri hres hN n
    ((canonL ar).map (evalTotal σ)) hkC
  have hED : famOfD P μ fd (iterPhi P μ fd n) ((canonL ar).map (evalTotal σ))
      = famOfD P μ fd (iterPhiD P μ fd n) ((canonL ar).map (evalTotal σ)) :=
    famOfD_ext P μ fd _ _ _ fun ρp =>
      (iterPhiD_eq P μ fd n (σOf ((canonL ar).map (evalTotal σ))) ρp hkC).symm
  have hdenC1 := famFields_den_of_entry P μ fd ar σ hf hcls hri hEnt
  have hdenC2 := famFields_den_of_entry P μ fd ar σ hf hcls hri
    (X₁ := famOfD P μ fd (iterPhi P μ fd n)) (X₂ := famOfD P μ fd (iterPhiD P μ fd n))
    (by rw [hED]; exact Equiv.rfl)
  refine (famEnd_den_congr P (tabIter P μ fd n)
      (upd μ fd.fref (famOfD P μ fd (iterPhi P μ fd n))) σ fd hdenC1 _).trans ?_
  refine (famEnd_den_congr P (upd μ fd.fref (famOfD P μ fd (iterPhi P μ fd n)))
      (upd μ fd.fref (famOfD P μ fd (iterPhiD P μ fd n))) σ fd hdenC2 _).trans ?_
  -- unfold both ends at the Type branch
  have hfun : ∀ ρp, PhiF P μ fd (iterPhiD P μ fd n) σ ρp = iterPhi P μ fd (n + 1) σ ρp :=
    fun ρp => by
      show PsiF P μ fd σ ρp (iterPhiD P μ fd n σ ρp) = PsiF P μ fd σ ρp (iterPhi P μ fd n σ ρp)
      rw [iterPhiD_eq P μ fd n σ ρp hk]
  unfold famEnd famEndD
  rw [cond_neg hk, push_append, ← his, shiftρ_push, lastVals_push]
  have hset : fibAt P μ fd (PhiF P μ fd (iterPhiD P μ fd n)) σ (push ps ρ0) is
      = fibAt P μ fd (iterPhi P μ fd (n + 1)) σ (push ps ρ0) is := by
    unfold fibAt
    rw [hfun (push ps ρ0)]
  have hEq : Equiv (fibAt P μ fd (PhiF P μ fd (iterPhiD P μ fd n)) σ (push ps ρ0) is)
      (fibAt P μ fd (iterPhi P μ fd (n + 1)) σ (push ps ρ0) is) := by
    rw [hset]
    exact Equiv.rfl
  exact tyv_congr ((TypeFib_famOfD P μ fd ar (iterPhiD P μ fd n) hB hpf
    (iterPhiD_env P μ fd n) (iterPhiD_levels P μ fd ar hB n)
    (iterPhiD_ne P μ fd n) (iterPhiD_mem P μ fd hN n) hclsA hri hres σ ps hps is his).trans hEq)

/-- `limEnd_sub` with the alignment premise discharged in the
direct-recursive class-A case: the union of the F3 iterates' fibres sits
inside the lfp's fibre. -/
theorem limEnd_sub_classA (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (ar : Nat) (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2) (hB : FamBounded fd ar)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hcls : ∀ c, c ∈ fd.ctors →
      FieldsClass fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (σ : Nat → Nat) (ps is : List PSet.{4}) (hps : ps.length = fd.params.length)
    (his : is.length = fd.indices.length) (hk : evalTotal σ fd.resLevel ≠ 0) :
    ∀ z, z ∈ iUnionN (fun n => El (famEnd (mkM P (upd μ fd.fref (famIter P μ fd n))) W4 σ fd
        (push (ps ++ is) ρ0))) →
      z ∈ fibAt P μ fd (DStar P μ fd) σ (push ps ρ0) is :=
  limEnd_sub σ ps is hps his hk
    (fun n => famEnd_famEndD_iter P μ fd ar hf hB hpf hcls hri hres hN n σ hk ps is hps his) hN

/-- The reverse direction (absent `.fn`-kinded fields): every element of the
lfp's fibre is in the union of the iterates' fibres. -/
theorem fibAt_sub_limEnd_classA (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (ar : Nat) (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2) (hB : FamBounded fd ar)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hcls : ∀ c, c ∈ fd.ctors →
      FieldsClass fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
    (σ : Nat → Nat) (ps is : List PSet.{4}) (hps : ps.length = fd.params.length)
    (his : is.length = fd.indices.length) (hk : evalTotal σ fd.resLevel ≠ 0)
    (hnoFn : ∀ c, c ∈ fd.ctors → ∀ p, p ∈ kindsOf fd.fref c.1 → p ≠ .fn) :
    ∀ z, z ∈ fibAt P μ fd (DStar P μ fd) σ (push ps ρ0) is →
      z ∈ iUnionN (fun n => El (famEnd (mkM P (upd μ fd.fref (famIter P μ fd n))) W4 σ fd
          (push (ps ++ is) ρ0))) := by
  intro z hz
  obtain ⟨i, hiP, hi'⟩ := mem_sep.mp hz
  have hu : z ∈ iterPhiUnion P μ fd σ (push ps ρ0) :=
    DStar_sub_union hN σ (push ps ρ0) hk hnoFn z ⟨i, hi'⟩
  obtain ⟨m, hm⟩ := mem_iUnionN.mp hu
  have hfa : z ∈ fibAt P μ fd (iterPhi P μ fd (m + 1)) σ (push ps ρ0) is := by
    obtain ⟨j, hj⟩ := hm
    refine mem_sep.mpr ⟨j, ?_, hj⟩
    exact (resTupF_congr P μ fd σ (push ps ρ0) hj).trans
      ((resTupF_congr P μ fd σ (push ps ρ0) hi').symm.trans hiP)
  have hfa' : z ∈ fibAt P μ fd (iterPhi P μ fd (m + 1)) σ
      (shiftρ fd.indices.length (push (ps ++ is) ρ0))
      (lastVals fd.indices.length (push (ps ++ is) ρ0)) := by
    rw [push_append, ← his, shiftρ_push, lastVals_push]
    exact hfa
  have h1 : z ∈ El (famEndD P μ fd (iterPhi P μ fd (m + 1)) σ (push (ps ++ is) ρ0)) :=
    mem_congr_right (el_tyv (S := fibAt P μ fd (iterPhi P μ fd (m + 1)) σ
      (shiftρ fd.indices.length (push (ps ++ is) ρ0))
      (lastVals fd.indices.length (push (ps ++ is) ρ0)))).symm hfa'
  exact mem_iUnionN.mpr ⟨m,
    mem_congr_right (el_congr (famEnd_famEndD_iter P μ fd ar hf hB hpf hcls hri hres hN
      m σ hk ps is hps his)).symm h1⟩

/-- The fibre-level equivalence (direct-recursive class-A, absent `.fn`
fields): the union of the F3 iterates' fibres IS the lfp's fibre, at every
fitting telescope value. -/
theorem limEnd_famEndD_classA (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (ar : Nat) (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2) (hB : FamBounded fd ar)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hcls : ∀ c, c ∈ fd.ctors →
      FieldsClass fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (hnoFn : ∀ c, c ∈ fd.ctors → ∀ p, p ∈ kindsOf fd.fref c.1 → p ≠ .fn)
    (σ : Nat → Nat) (xs : List PSet.{4})
    (hx : TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0 xs)
    (hk : evalTotal σ fd.resLevel ≠ 0) :
    Equiv (limEnd P μ fd σ (push xs ρ0)) (famEndD P μ fd (DStar P μ fd) σ (push xs ρ0)) := by
  obtain ⟨ps, is, rfl, hpsT, hisT⟩ := TelFits_split fd.params fd.indices ρ0 xs hx
  have hps : ps.length = fd.params.length := TelFits.length hpsT
  have his : is.length = fd.indices.length := TelFits.length hisT
  unfold limEnd famEndD
  rw [push_append, ← his, shiftρ_push, lastVals_push]
  refine tyv_congr ?_
  apply ext
  intro z
  constructor
  · intro hz
    refine limEnd_sub_classA P μ fd ar hf hB hpf hcls hri hres hN σ ps is hps his hk z ?_
    rw [push_append]
    exact hz
  · intro hz
    have h := fibAt_sub_limEnd_classA P μ fd hN ar hf hB hpf hcls hri hres σ ps is hps his hk hnoFn z hz
    rw [push_append] at h
    exact h

/-- **The entry-level bridge** (direct-recursive class-A, absent `.fn`
fields): at every Type-read instance, the limit of the F3 iterates is the
KT lfp. -/
theorem famLim_famLfp (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (ar : Nat) (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2) (hB : FamBounded fd ar)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hcls : ∀ c, c ∈ fd.ctors →
      FieldsClass fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (hnoFn : ∀ c, c ∈ fd.ctors → ∀ p, p ∈ kindsOf fd.fref c.1 → p ≠ .fn)
    (vs : List Nat) (hk : evalTotal (σOf vs) fd.resLevel ≠ 0) :
    Equiv (famLim P μ fd vs) (famLfp P μ fd vs) := by
  show Equiv (piLam (mkM P μ) (σOf vs) (limEnd P μ fd (σOf vs)) ρ0 (famType fd))
    (piLam (mkM P μ) (σOf vs) (famEndD P μ fd (DStar P μ fd) (σOf vs)) ρ0 (famType fd))
  unfold famType
  exact piLam_congr_fits₂ (mkM P μ) (mkM P μ) rfl (σOf vs)
    (limEnd_resp P μ fd (σOf vs))
    (famEndD_envResp P μ fd (DStar P μ fd)
      (fun σ' ρ ρ' hρ => DStar_env P μ fd hN σ' hρ) (σOf vs))
    (.sort fd.resLevel) (fun A B e => Expr.noConfusion e)
    (fd.params ++ fd.indices) ρ0 (fun _ _ _ => rfl)
    (fun xs hxs => limEnd_famEndD_classA P μ fd ar hf hB hpf hcls hri hres hN hnoFn
      (σOf vs) xs hxs hk)

/-- The class-A `FamKTBridgeA` cell at Type-reads: `famLim ≈ famKT`.  The
Prop twin (`famLfpP`) remains the named residue
`[rcic-f3-famkt-bridge-prop-twin]`. -/
theorem famLim_famKT_type (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (ar : Nat) (hf : fd.fref ≠ 1 ∧ fd.fref ≠ 2) (hB : FamBounded fd ar)
    (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
    (hcls : ∀ c, c ∈ fd.ctors →
      FieldsClass fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
    (hN : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1)
    (hnoFn : ∀ c, c ∈ fd.ctors → ∀ p, p ∈ kindsOf fd.fref c.1 → p ≠ .fn)
    (vs : List Nat) (hk : evalTotal (σOf vs) fd.resLevel ≠ 0) :
    Equiv (famLim P μ fd vs) (famKT P μ fd vs) := by
  have hkt : famKT P μ fd vs = famLfp P μ fd vs := by
    unfold famKT
    rw [if_neg hk]
  rw [hkt]
  exact famLim_famLfp P μ fd ar hf hB hpf hcls hri hres hN hnoFn vs hk

end Align


end PSet

end Rcic.F3

#print axioms Rcic.F3.PSet.famLim_famKT_type
#print axioms Rcic.F3.PSet.famLim_famLfp
#print axioms Rcic.F3.PSet.famIter_famOfD
#print axioms Rcic.F3.PSet.famEnd_famEndD_iter
