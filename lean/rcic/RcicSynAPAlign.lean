import rcic.RcicSynAppBvarPBit
import rcic.RcicSynEnrich
import rcic.RcicSynEtaMeet
import rcic.RcicSynLetInline

/-!
# Syntactic sortRow, build step — AP prefix alignment (ChatGPT S2, #7311)

Spec: `research/rcic/sortrow/S2_AP_PREFIX_ALIGNMENT.md` §1, §3.1, §5
(approved ChatGPT S2, measured at main `e7fb7751`). `closure_claim = 0`.

1. **§1 `lookupProvider_entrySort`**: the provider `ctxP_lookupType_sort C hlook`
   returns the sort level of **this `C`'s actual stored field** at index `i`
   (`wkAtZero`/`wkLetAtZero` + index equations), so it agrees with
   `C.entrySort i`. Never another same-type provider; never `hA = P`,
   `uEntry = u`, or a caller-supplied `SortCoh σ P hA`.
   - `resolve_eq_star_iff_lookupProvider` binds `resolve ρ i = .star` to the
     provider's entry bit under `DispForC σ C ρ` + `SpineLetPBit`.
   - `pbit_bvar_reg_of_lookupProvider` is the bvar-erasure consequence
     (`PBit` on the **original** `Dvar`/`hA`) given the exact target
     `levelIsZero (σ uEntry) = levelIsZero (σ u)` as a bare bit equation — the
     shape `pbit_bvar_reg_of_dispEntry` already consumes.

2. **§3.1 `intro_align_pair_below{,_pi,_letE}`**: the immediate body use at the
   introducing node `N`. With `ΓI = .assumption A₀ :: Γ`, `CI = .assumption C hI`,
   `PI = wkAtZero hI`, and `hA` a real body bvar's sort-typing (every atom
   strictly below `N.wt Aw`):
   `LexDM (combMeas Aw CI (tyPairMeas Aw PI hA)) (combMeas Aw C (tyPairMeas Aw N D₂))`
   with the concrete DM decomposition **kept** `C.atoms Aw`,
   **removed** `[N.wt Aw] ++ D₂.atoms Aw`,
   **added** `hI.atoms Aw ++ hI.atoms Aw ++ hA.atoms Aw` (for `letE`, `hv`'s real
   atoms join the new spine). The one larger atom `N.wt Aw` pays for the finite
   duplicates. No `hA = P`, no reverse weakening, no ancestor-rank reset.

3. The refuted `(P, hA)` same-rank `BitCoh` edge stays refused: main's
   `not_combLexDM_pbit_bvar` (caller atoms `[6,2,1]` → callee `[6,6,1]`) is
   unchanged and re-pinned in `RcicSynAPAlignPins`.

Remaining gap (S2 §4/§7): general ambient prefix reflection, mixed-history
alignment, and deep introduced forests stay **W-COV-AP-PREFIX-REFLECTION**.
This module is not the coverage entry; coverage routes through #7307's
environment rebase (ct001).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 The provider is bound to `C`'s own stored field -/

/-- The first component of `ctxP_lookupType_sort C hlook` — the sort level of the
    provider rebuilt from `C`'s stored field — agrees with `C.entrySort i`.
    (S2 §1: the provider is read out of *this* `C`, never a same-type stand-in.) -/
theorem lookupProvider_entrySort {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → (C : CtxP E n Γ) → {i : Nat} → {A : Expr Nat} →
    (hlook : lookupType Γ i = some A) →
    C.entrySort i = some (ctxP_lookupType_sort C hlook).1
  | _, .nil _ _, i, _, h => by
      cases i <;> simp [lookupType] at h
  | _, .assumption _ _ _ _ _ _ _, 0, _, _ => rfl
  | _, .assumption _ _ _ _ _ hC _, i + 1, _, h => by
      dsimp only [ctxP_lookupType_sort]
      cases lookupType_cons_succ_inv h with
      | mk _ hlt _ => exact lookupProvider_entrySort hC hlt
  | _, .letBinding _ _ _ _ _ _ _ _ _, 0, _, _ => rfl
  | _, .letBinding _ _ _ _ _ _ hC _ _, i + 1, _, h => by
      dsimp only [ctxP_lookupType_sort]
      cases lookupType_cons_succ_inv h with
      | mk _ hlt _ => exact lookupProvider_entrySort hC hlt

/-- Along `DispForC σ C ρ`, `resolve ρ i = .star` iff the provider's entry bit
    `levelIsZero (σ uEntry)` holds — `uEntry` being read from `C`'s stored field. -/
theorem resolve_eq_star_iff_lookupProvider {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    {i : Nat} {A : Expr Nat}
    (hC : DispForC σ C ρ) (hlet : SpineLetPBit σ C ρ i)
    (hlook : lookupType Γ i = some A) :
    resolve ρ i = .star ↔
      levelIsZero (σ (ctxP_lookupType_sort C hlook).1) = true :=
  resolve_eq_star_iff_of_dispForC hC hlet (lookupProvider_entrySort C hlook)

/-- `PBit` on the **original** `Dvar`/`hA` from `DispForC σ C ρ`, `SpineLetPBit`,
    and the exact S2-§1 target `levelIsZero (σ uEntry) = levelIsZero (σ u)` as a
    bare bit equation (not `hA = P`, not `uEntry = u`, not a caller-supplied
    `SortCoh σ P hA`). -/
theorem pbit_bvar_reg_of_lookupProvider {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    {i : Nat} {A : Expr Nat} {u : Level}
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (hC : DispForC σ C ρ) (hlet : SpineLetPBit σ C ρ i)
    (hbit : levelIsZero (σ (ctxP_lookupType_sort C hlook).1) = levelIsZero (σ u)) :
    PBit σ ρ (TyP.bvar E n Γ i A u hlook hA) hA := by
  cases hzu : levelIsZero (σ u) with
  | true => exact pbit_bvar_proof_reg σ ρ hlook hA hzu
  | false =>
      unfold PBit
      rw [eps_bvar_rel hzu]
      have hres := resolve_eq_star_iff_lookupProvider hC hlet hlook
      rw [hbit] at hres
      exact hres

/-! ## §3.1 Immediate-body alignment at the introducing node is payable -/

/-- At the introducing node `N = TyP.lam … hI hbody hB`, the real `BitCoh` query
    `BitCoh σ PI hA` for the **immediate body use** — `PI = wkAtZero hI` in the
    introduced spine `CI = .assumption C hI`, `hA` the original body bvar's
    sort-typing of the same `lift 0 1 A₀` — is strictly `LexDM`-below any parent
    query `(N, D₂)`: keep `C.atoms Aw`, remove `[N.wt Aw] ++ D₂.atoms Aw`, add
    `hI.atoms Aw ++ hI.atoms Aw ++ hA.atoms Aw`, every added atom `< N.wt Aw`
    (the one larger atom pays for the finite duplicates). -/
theorem intro_align_pair_below (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₀ body B : Expr Nat} {u v : Level}
    (C : CtxP E n Γ)
    (hI : TyP E n Γ A₀ (.sort u))
    (hbody : TyP E n (.assumption A₀ :: Γ) body B)
    (hB : TyP E n (.assumption A₀ :: Γ) B (.sort v))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    {uA : Level} (hA : TyP E n (.assumption A₀ :: Γ) (lift 0 1 A₀) (.sort uA))
    (hhA : hA.wt Aw < (TyP.lam E n Γ A₀ u body B v hI hbody hB).wt Aw) :
    LexDM
      (combMeas Aw (.assumption E n Γ A₀ u C hI)
        (tyPairMeas Aw (wkAtZero (A := A₀) hI) hA))
      (combMeas Aw C
        (tyPairMeas Aw (TyP.lam E n Γ A₀ u body B v hI hbody hB) D₂)) := by
  have hNat : (TyP.lam E n Γ A₀ u body B v hI hbody hB).atoms Aw =
      [(TyP.lam E n Γ A₀ u body B v hI hbody hB).wt Aw] := by
    simp only [TyP.atoms]
  have hIlt : hI.wt Aw < (TyP.lam E n Γ A₀ u body B v hI hbody hB).wt Aw := by
    simp only [TyP.wt]; omega
  refine lex_of_dm ?_
  simp only [combMeas, tyPairMeas, CtxP.atoms, atoms_wkAtZero, hNat]
  refine ⟨[(TyP.lam E n Γ A₀ u body B v hI hbody hB).wt Aw] ++ D₂.atoms Aw,
    hI.atoms Aw ++ hI.atoms Aw ++ hA.atoms Aw, C.atoms Aw,
    by simp, List.perm_append_comm, ?_, ?_⟩
  · rw [List.append_assoc]
    refine List.Perm.trans (List.Perm.append_left _ List.perm_append_comm) ?_
    rw [← List.append_assoc, ← List.append_assoc]
  · intro y hy
    refine ⟨(TyP.lam E n Γ A₀ u body B v hI hbody hB).wt Aw,
      List.mem_append.mpr (Or.inl (List.mem_singleton_self _)), ?_⟩
    rcases List.mem_append.mp hy with hy | hy
    · rcases List.mem_append.mp hy with hy | hy
      · exact atoms_lt_of_wt_lt Aw hI hIlt y hy
      · exact atoms_lt_of_wt_lt Aw hI hIlt y hy
    · exact atoms_lt_of_wt_lt Aw hA hhA y hy

/-- At the introducing node `N = TyP.pi … hI hB`, the immediate body use under
    `.assumption A₀ :: Γ` is payable by the same decomposition (`hB` is the
    body's sort-typing, a real child of `N`). -/
theorem intro_align_pair_below_pi (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₀ B : Expr Nat} {u v : Level}
    (C : CtxP E n Γ)
    (hI : TyP E n Γ A₀ (.sort u))
    (hB : TyP E n (.assumption A₀ :: Γ) B (.sort v))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    {uA : Level} (hA : TyP E n (.assumption A₀ :: Γ) (lift 0 1 A₀) (.sort uA))
    (hhA : hA.wt Aw < (TyP.pi E n Γ A₀ u B v hI hB).wt Aw) :
    LexDM
      (combMeas Aw (.assumption E n Γ A₀ u C hI)
        (tyPairMeas Aw (wkAtZero (A := A₀) hI) hA))
      (combMeas Aw C
        (tyPairMeas Aw (TyP.pi E n Γ A₀ u B v hI hB) D₂)) := by
  have hNat : (TyP.pi E n Γ A₀ u B v hI hB).atoms Aw =
      [(TyP.pi E n Γ A₀ u B v hI hB).wt Aw] := by
    simp only [TyP.atoms]
  have hIlt : hI.wt Aw < (TyP.pi E n Γ A₀ u B v hI hB).wt Aw := by
    simp only [TyP.wt]; omega
  refine lex_of_dm ?_
  simp only [combMeas, tyPairMeas, CtxP.atoms, atoms_wkAtZero, hNat]
  refine ⟨[(TyP.pi E n Γ A₀ u B v hI hB).wt Aw] ++ D₂.atoms Aw,
    hI.atoms Aw ++ hI.atoms Aw ++ hA.atoms Aw, C.atoms Aw,
    by simp, List.perm_append_comm, ?_, ?_⟩
  · rw [List.append_assoc]
    refine List.Perm.trans (List.Perm.append_left _ List.perm_append_comm) ?_
    rw [← List.append_assoc, ← List.append_assoc]
  · intro y hy
    refine ⟨(TyP.pi E n Γ A₀ u B v hI hB).wt Aw,
      List.mem_append.mpr (Or.inl (List.mem_singleton_self _)), ?_⟩
    rcases List.mem_append.mp hy with hy | hy
    · rcases List.mem_append.mp hy with hy | hy
      · exact atoms_lt_of_wt_lt Aw hI hIlt y hy
      · exact atoms_lt_of_wt_lt Aw hI hIlt y hy
    · exact atoms_lt_of_wt_lt Aw hA hhA y hy

/-- At the introducing node `N = TyP.letE … hI hv hbody hT`, the immediate body
    use under `.letBinding A₀ v₀ :: Γ` is payable by the same decomposition,
    keeping the real `hv`'s atoms in the new spine (`PI = wkLetAtZero hI`). -/
theorem intro_align_pair_below_letE (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₀ v₀ body B : Expr Nat} {u w : Level}
    (C : CtxP E n Γ)
    (hI : TyP E n Γ A₀ (.sort u))
    (hv : TyP E n Γ v₀ A₀)
    (hbody : TyP E n (.letBinding A₀ v₀ :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 v₀ B) (.sort w))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    {uA : Level} (hA : TyP E n (.letBinding A₀ v₀ :: Γ) (lift 0 1 A₀) (.sort uA))
    (hhA : hA.wt Aw < (TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).wt Aw) :
    LexDM
      (combMeas Aw (.letBinding E n Γ A₀ u v₀ C hI hv)
        (tyPairMeas Aw (wkLetAtZero (A := A₀) (v := v₀) hI) hA))
      (combMeas Aw C
        (tyPairMeas Aw (TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT) D₂)) := by
  have hNat : (TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).atoms Aw =
      [(TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).wt Aw] := by
    simp only [TyP.atoms]
  have hIlt : hI.wt Aw < (TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).wt Aw := by
    simp only [TyP.wt]; omega
  have hvlt : hv.wt Aw < (TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).wt Aw := by
    simp only [TyP.wt]; omega
  have hPI : (wkLetAtZero (A := A₀) (v := v₀) hI).atoms Aw = hI.atoms Aw := by
    unfold wkLetAtZero; rw [atoms_tyCastCtx]; simp only [TyP.atoms]
  refine lex_of_dm ?_
  simp only [combMeas, tyPairMeas, CtxP.atoms, hPI, hNat]
  refine ⟨[(TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).wt Aw] ++ D₂.atoms Aw,
    hI.atoms Aw ++ hA.atoms Aw ++ hI.atoms Aw ++ hv.atoms Aw, C.atoms Aw,
    by simp, List.perm_append_comm, ?_, ?_⟩
  · rw [show (hI.atoms Aw ++ hA.atoms Aw ++ hI.atoms Aw ++ hv.atoms Aw) ++ C.atoms Aw =
        (hI.atoms Aw ++ hA.atoms Aw) ++ ((hI.atoms Aw ++ hv.atoms Aw) ++ C.atoms Aw) from
        by simp only [← List.append_assoc]]
    exact List.perm_append_comm
  · intro y hy
    refine ⟨(TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).wt Aw,
      List.mem_append.mpr (Or.inl (List.mem_singleton_self _)), ?_⟩
    rcases List.mem_append.mp hy with hy | hy
    · rcases List.mem_append.mp hy with hy | hy
      · rcases List.mem_append.mp hy with hy | hy
        · exact atoms_lt_of_wt_lt Aw hI hIlt y hy
        · exact atoms_lt_of_wt_lt Aw hA hhA y hy
      · exact atoms_lt_of_wt_lt Aw hI hIlt y hy
    · exact atoms_lt_of_wt_lt Aw hv hvlt y hy

end Rcic.Syn

#print axioms Rcic.Syn.lookupProvider_entrySort
#print axioms Rcic.Syn.resolve_eq_star_iff_lookupProvider
#print axioms Rcic.Syn.pbit_bvar_reg_of_lookupProvider
#print axioms Rcic.Syn.intro_align_pair_below
#print axioms Rcic.Syn.intro_align_pair_below_pi
#print axioms Rcic.Syn.intro_align_pair_below_letE
