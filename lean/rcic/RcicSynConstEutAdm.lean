import rcic.RcicSynDeltaBeta
import rcic.RcicSynLetTransportCL
import rcic.RcicSynAdm
import rcic.RcicSynRegStep
import rcic.RcicSynSortPBit

/-!
# Syntactic sortRow — `RcicSynConstEutAdm`: BelowC Wall 1, const `EUT` through one admission

`research/rcic/sortrow/BELOWC_SEMANTIC_WALLS.md` Part I. Two same-`r`
`TyP.const` nodes `Dᵢ = TyP.const … r ls aliasᵢ m uᵢ … hEqᵢ Hᵢ` share the
displayed `ls`, `E`, `Γ`, `n`, and erasure view `(σ, ρ)`. The `EUT` between
them — `ConvMod (EStep tbl) LvlEq` on the ascription typings `Hᵢ.eps σ ρ` —
reduces to two actual MixedCL answers `q₁`, `q₂`, each reaching the **same**
selected admission's `P := A.hT` under its alias view `μᵢ := σ ∘ instLevel
aliasᵢ` and the same literal weakening continuation.

1. **`contextLift` / `contextLift_lvlEq`**: the cutoff-`0` weakening
   continuation — one `lift 0 1` per `.keep` in a display prefix — and its
   `LvlEq` congruence.
2. **`eps_wkClosed_contextLift`**: the `wkClosed` erasure readout with **no
   length hypothesis** — `(wkClosed … Γ Q).eps σ ρ` applies the kept prefix
   `ρ.take Γ.length` to `Q.eps σ (ρ.drop Γ.length)`, by structural induction
   on `Γ` generalizing `ρ`.
3. **`eut_const_of_admission_views`**: the Part-I composition through
   `eut_const_nodes` — `eqNList` round-trips the two recorded aliases,
   `instLevel_eqNList` + `LevelHom.eqN_map` give the all-level middle,
   `lvlEq_eps` + `contextLift_lvlEq` transport it through the continuation.
   `q₁`, `q₂` arrive as hypotheses; no `AssumpPref`/`ClosedWf`/bound premise
   is added.
4. **`dmStep_constEutAdm_view` / `dmStep_constEutAdm_pair`**: the payment —
   the caller's const atom `wt Dᵢ = 1 + wt Hᵢ + Aw r` dominates every atom of
   `Sᵢ = at Hᵢ ++ at P` (`≤ wt Hᵢ < wt Dᵢ` or `≤ wt P < Aw r < wt Dᵢ`), so
   `K ++ [wt Dᵢ] >DM K ++ Sᵢ`; each sibling call drops the other's unread
   const atom.

`closure_claim = 0`: this module is the mechanical reduction; `q₁`, `q₂`
remain genuine observation answers (MixedCL at the two admission views).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The cutoff-`0` weakening continuation on a display prefix: one `lift 0 1`
    per `.keep`; `.drop` and `.inline` pass through untouched. -/
def contextLift : List Disp → ETm → ETm
  | [], t => t
  | .keep :: ρ, t => (contextLift ρ t).lift 0 1
  | .drop :: ρ, t => contextLift ρ t
  | .inline _ :: ρ, t => contextLift ρ t

/-- `contextLift` is `LvlEq`-congruent. -/
theorem contextLift_lvlEq (ρ : List Disp) {t t' : ETm} (h : LvlEq t t') :
    LvlEq (contextLift ρ t) (contextLift ρ t') := by
  induction ρ with
  | nil => exact h
  | cons d ρ ih => cases d with
    | keep => exact ih.lift' 0 1
    | drop => exact ih
    | inline v => exact ih

/-- The `wkClosed` erasure readout **without a length hypothesis**: weakening
    a closed typing into `Γ` and erasing at `ρ` equals erasing the original
    closed typing at the tail `ρ.drop Γ.length`, then applying the literal
    continuation `ρ.take Γ.length`. Structural induction on `Γ` generalizing
    `ρ`. -/
theorem eps_wkClosed_contextLift {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    (hcle : lift 0 1 e = e) (hclT : lift 0 1 T = T) :
    (Γ : LCtx) → (Q : TyP E n [] e T) → (σ : Level → Level) → (ρ : List Disp) →
      (wkClosed hcle hclT Γ Q).eps σ ρ =
        contextLift (ρ.take Γ.length) (Q.eps σ (ρ.drop Γ.length))
  | [], _, _, _ => rfl
  | _ :: Γ₀, Q, σ, ρ => by
      have ih : ∀ ρ₀ : List Disp, (wkClosed hcle hclT Γ₀ Q).eps σ ρ₀ =
          contextLift (ρ₀.take Γ₀.length) (Q.eps σ (ρ₀.drop Γ₀.length)) :=
        fun ρ₀ => eps_wkClosed_contextLift hcle hclT Γ₀ Q σ ρ₀
      rw [wkClosed, eps_tyCast, eps_tyCastCtx]
      cases ρ with
      | nil =>
          have ih0 := ih []
          simp only [List.take_nil, List.drop_nil, contextLift] at ih0 ⊢
          simp only [TyP.eps, List.getElem?_nil, removeAt]
          exact ih0
      | cons d ρ₀ =>
          cases d <;>
            simp only [TyP.eps, List.getElem?_cons_zero, List.get?_cons_zero,
              removeAt_zero, List.take_zero, List.length_cons,
              List.take_succ_cons, List.drop_succ_cons, countKeep, contextLift,
              ih]

/-- BelowC Wall 1, Part I main theorem. `EUT` on two same-`r` `TyP.const`
    nodes composes from the two admission-view answers `q₁`, `q₂`: each side's
    ascription erasure `Hᵢ.eps σ ρ` is `ConvMod`-related to the chosen
    admission's `A.hT` read through that side's composed level map
    `σ ∘ instLevel aliasᵢ` and the shared weakening continuation. The middle
    step is `LvlEq` of the two `A.hT` erasures (same `P`, `eqN` of the two
    aliases through `σ ∘ instLevel`), lifted by `contextLift_lvlEq`. -/
theorem eut_const_of_admission_views (tbl : List CRule) {E : ResolvedEnv}
    {Aw : Nat → Nat} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls alias₁ alias₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (A : TypeAdm E Aw r m)
    (hres₁ : E.members r = some m) (hlen₁ : ls.length = m.arity)
    (hwf₁ : levelsBounded n ls = true) (hEq₁ : eqNList ls alias₁)
    (H₁ : TyP E n Γ (instantiateLevels alias₁ m.mtype) (.sort u₁))
    (hres₂ : E.members r = some m) (hlen₂ : ls.length = m.arity)
    (hwf₂ : levelsBounded n ls = true) (hEq₂ : eqNList ls alias₂)
    (H₂ : TyP E n Γ (instantiateLevels alias₂ m.mtype) (.sort u₂))
    {σ : Level → Level} (hσ : LevelHom σ) (ρ : List Disp)
    (q₁ : ConvMod (EStep tbl) LvlEq (H₁.eps σ ρ)
      (contextLift (ρ.take Γ.length)
        (A.hT.eps (fun l => σ (instLevel alias₁ l)) (ρ.drop Γ.length))))
    (q₂ : ConvMod (EStep tbl) LvlEq (H₂.eps σ ρ)
      (contextLift (ρ.take Γ.length)
        (A.hT.eps (fun l => σ (instLevel alias₂ l)) (ρ.drop Γ.length)))) :
    EUT tbl σ ρ (TyP.const E n Γ r ls alias₁ m u₁ hres₁ hlen₁ hwf₁ hEq₁ H₁)
                (TyP.const E n Γ r ls alias₂ m u₂ hres₂ hlen₂ hwf₂ hEq₂ H₂) := by
  have hAliases : eqNList alias₁ alias₂ := eqNList_trans (eqNList_symm hEq₁) hEq₂
  have hμ : ∀ l, eqN (σ (instLevel alias₁ l)) (σ (instLevel alias₂ l)) :=
    fun l => hσ.eqN_map (instLevel_eqNList hAliases l)
  have hP := lvlEq_eps A.hT hμ (DispLvlEq.refl (ρ.drop Γ.length))
  have hMiddle := contextLift_lvlEq (ρ.take Γ.length) hP
  exact eut_const_nodes tbl σ ρ hres₁ hlen₁ hwf₁ hEq₁ H₁ hres₂ hlen₂ hwf₂ hEq₂ H₂
    (q₁.trans ((ConvMod.eqv hMiddle).trans (ConvMod.symm' LvlEq.symm' q₂)))

/-- Wall-1 payment, one side: the two smaller answers `at Hᵢ ++ at P` are
    dominated by the caller's const atom `wt Dᵢ = 1 + wt Hᵢ + Aw r` —
    `at Hᵢ` atoms are `≤ wt Hᵢ < wt Dᵢ`, `at P` atoms are
    `≤ wt P < Aw r < wt Dᵢ`. `dmStep_of_below` plus `dmStep_append_left`
    keeps the genuinely retained ledger `K`. -/
theorem dmStep_constEutAdm_view (Aw : Nat → Nat) (K : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls ali : List Level} {m : CheckedMember} {u : Level}
    (A : TypeAdm E Aw r m)
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hEq : eqNList ls ali)
    (H : TyP E n Γ (instantiateLevels ali m.mtype) (.sort u)) :
    DMStep (K ++ (H.atoms Aw ++ A.hT.atoms Aw))
      (K ++ [(TyP.const E n Γ r ls ali m u hres hlen hwf hEq H).wt Aw]) := by
  have hbound : ∀ y ∈ H.atoms Aw ++ A.hT.atoms Aw,
      y < (TyP.const E n Γ r ls ali m u hres hlen hwf hEq H).wt Aw := by
    intro y hy
    have hwtc : (TyP.const E n Γ r ls ali m u hres hlen hwf hEq H).wt Aw =
        1 + H.wt Aw + Aw r := rfl
    rw [hwtc]
    rcases List.mem_append.mp hy with hy | hy
    · have := TyP.atoms_le Aw H y hy; omega
    · have := TyP.atoms_le Aw A.hT y hy; have := A.lt; omega
  have h0 := dmStep_of_below (Z := []) hbound
  simp only [List.append_nil] at h0
  exact dmStep_append_left h0 K

/-- Wall-1 payment, the pair: against the parent multiset `K ++ [N₁, N₂]`
    carrying **both** const atoms, each sibling's call is charged only its own
    smaller answers and drops the other's unread const atom
    (`dmStep_drop_right` / `dmStep_drop_left`). Each call counts `P` once —
    the S21 control `[8,8] → [3,3]` per side. -/
theorem dmStep_constEutAdm_pair (Aw : Nat → Nat) (K : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls alias₁ alias₂ : List Level} {m : CheckedMember} {u₁ u₂ : Level}
    (A : TypeAdm E Aw r m)
    (hres₁ : E.members r = some m) (hlen₁ : ls.length = m.arity)
    (hwf₁ : levelsBounded n ls = true) (hEq₁ : eqNList ls alias₁)
    (H₁ : TyP E n Γ (instantiateLevels alias₁ m.mtype) (.sort u₁))
    (hres₂ : E.members r = some m) (hlen₂ : ls.length = m.arity)
    (hwf₂ : levelsBounded n ls = true) (hEq₂ : eqNList ls alias₂)
    (H₂ : TyP E n Γ (instantiateLevels alias₂ m.mtype) (.sort u₂)) :
    DMStep (K ++ (H₁.atoms Aw ++ A.hT.atoms Aw))
        (K ++ [(TyP.const E n Γ r ls alias₁ m u₁ hres₁ hlen₁ hwf₁ hEq₁ H₁).wt Aw,
               (TyP.const E n Γ r ls alias₂ m u₂ hres₂ hlen₂ hwf₂ hEq₂ H₂).wt Aw]) ∧
    DMStep (K ++ (H₂.atoms Aw ++ A.hT.atoms Aw))
        (K ++ [(TyP.const E n Γ r ls alias₁ m u₁ hres₁ hlen₁ hwf₁ hEq₁ H₁).wt Aw,
               (TyP.const E n Γ r ls alias₂ m u₂ hres₂ hlen₂ hwf₂ hEq₂ H₂).wt Aw]) := by
  have s₁ := dmStep_constEutAdm_view Aw K A hres₁ hlen₁ hwf₁ hEq₁ H₁
  have s₂ := dmStep_constEutAdm_view Aw K A hres₂ hlen₂ hwf₂ hEq₂ H₂
  refine ⟨?_, ?_⟩
  · exact dmStep_perm_right
      (List.Perm.of_eq (List.append_assoc K [_] [_])) (dmStep_drop_right s₁ [_])
  · exact dmStep_perm_right List.perm_middle.symm (dmStep_drop_left s₂ [_])

end Rcic.Syn

#print axioms Rcic.Syn.contextLift_lvlEq
#print axioms Rcic.Syn.eps_wkClosed_contextLift
#print axioms Rcic.Syn.eut_const_of_admission_views
#print axioms Rcic.Syn.dmStep_constEutAdm_view
#print axioms Rcic.Syn.dmStep_constEutAdm_pair
