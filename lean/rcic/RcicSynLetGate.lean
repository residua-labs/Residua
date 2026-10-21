import rcic.RcicSynLetTraceShift

/-!
# Wall 2 (changed-declaration letRight), step 3 — the gate proof for the chain and the base
alignments

`research/rcic/sortrow/BELOWC_SEMANTIC_WALLS.md` Part III, "Gate proof" and "Where gates
change: only in `finishBvarL`".

The only places where the transported derivation reads a gate that is not the original
bvar's own provider are the three finishers of `finishBvarL`: a surviving slot hit
(`retypeLetBVarSlot`, the slot's `uSlot`), a surviving non-slot `.retype` (`chainSort`, the
first link's level), and a substitution hit (the stored replacement, no gate read). This module

* computes the erasure of each finisher (`eps_finishBvarL_*`);
* composes the junction answers `MixedBit[cᵢ.dr, cᵢ₊₁.dl]` and the terminal answer
  `MixedBit[cₘ.dr, H]` into `chainSort`'s gate equality (`chain_gate`, `chainSort_fst`) —
  comparing `H` with `c₁.dl` would compare `T` with `A₀`, so the composition runs along the
  chain, never across it;
* assembles the bvar case (`rel_finishBvarL`): the left gate-and-resolve against the finished
  variable's erasure, from the trace relation and the three base alignments (`BvarGate`:
  slot provider, replacement `W` through its site gate, chain junctions + end).

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the gate clause -/

/-- The head gate of `TyP.eps`: a true gate erases to ★. -/
def gateOut : Bool → ETm → ETm
  | true, _ => .star
  | false, t => t

theorem gateOut_true (t : ETm) : gateOut true t = .star := rfl

theorem gateOut_false (t : ETm) : gateOut false t = t := rfl

theorem eps_bvar_gateOut {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    {u : Level} {h : lookupType Γ i = some A} {hA : TyP E n Γ A (.sort u)}
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.bvar E n Γ i A u h hA).eps σ ρ = gateOut (levelIsZero (σ u)) (resolve ρ i) := by
  cases hu : levelIsZero (σ u)
  · exact eps_bvar_rel hu
  · exact eps_bvar_proof hu

theorem applyActs_gateOut (as : List EAct) (b : Bool) (t : ETm) :
    applyActs as (gateOut b t) = gateOut b (applyActs as t) := by
  cases b
  · rfl
  · exact applyActs_star as

/-! ## §2 the chain gate -/

/-- Adjacent links agree on the gate (`MixedBit[cᵢ.dr, cᵢ₊₁.dl]`, consumed form). -/
def ChainJunctionBits (μ' : Level → Level) : List Level → Prop
  | [] => True
  | [_] => True
  | w₁ :: w₂ :: ws => levelIsZero (μ' w₁) = levelIsZero (μ' w₂) ∧ ChainJunctionBits μ' (w₂ :: ws)

/-- The last link agrees with the provider `H` (`MixedBit[cₘ.dr, H]`, consumed form). -/
def ChainEndBit (μ' : Level → Level) (u0 : Level) : List Level → Prop
  | [] => True
  | [w] => levelIsZero (μ' w) = levelIsZero (μ' u0)
  | _ :: w :: ws => ChainEndBit μ' u0 (w :: ws)

/-- Along the chain: the first link's gate is `H`'s gate. -/
theorem chain_gate (μ' : Level → Level) : (ws : List Level) → (u0 : Level) →
    ChainJunctionBits μ' ws → ChainEndBit μ' u0 ws →
    levelIsZero (μ' (ws.headD u0)) = levelIsZero (μ' u0)
  | [], _, _, _ => rfl
  | [w], u0, _, hend => hend
  | w₁ :: w₂ :: ws, u0, hj, hend =>
      hj.1.trans (chain_gate μ' (w₂ :: ws) u0 hj.2 hend)

/-- `chainSort` reads the first link's level, or `H`'s on an empty chain. -/
theorem chainSort_fst {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ty : Expr Nat} {u0 : Level}
    (hA : TyP E n Γ ty (.sort u0)) : {B : Expr Nat} → (hc : ConvChain E n Γ B ty) →
      (chainSort hA hc).1 = (convChainLevels hc).headD u0
  | _, .nil => rfl
  | _, .cons _ _ _ => rfl

/-! ## §3 the finishers' erasures -/

theorem eps_convChain_apply {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e a : Expr Nat}
    (h : TyP E n Γ e a) : {c : Expr Nat} → (hc : ConvChain E n Γ a c) →
      (σ : Level → Level) → (ρ : List Disp) → (ConvChain.apply h hc).eps σ ρ = h.eps σ ρ
  | _, .nil, _, _ => rfl
  | _, .cons u hc' rest, σ, ρ => by
      simp only [ConvChain.apply]
      rw [eps_convChain_apply _ rest, eps_conv]

/-- The retyped slot variable erases through the slot's gate `uSlot`. -/
theorem eps_retypeLetBVarSlot {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {k : Nat}
    {Dom Val Dom' Val' : Expr Nat} {u : Level}
    (h : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort u))
    (hget : Γ.get? k = some (.letBinding Dom Val)) (μ' : Level → Level) (ρ' : List Disp) :
    (retypeLetBVarSlot (Val' := Val') h hget).eps μ' ρ' =
      gateOut (levelIsZero (μ' u)) (resolve ρ' k) := by
  unfold retypeLetBVarSlot
  rw [eps_conv]
  exact eps_bvar_gateOut μ' ρ'

theorem eps_finishBvarL_repl {E : ResolvedEnv} {n k : Nat} {Γpre : LCtx}
    {Dom Val Dom' Val' : Expr Nat} {uSlot u : Level} {term ty : Expr Nat}
    (hget : Γpre.get? k = some (.letBinding Dom Val))
    (hslot : CvP E n (Γpre.drop (k + 1)) Dom Dom' (.sort uSlot))
    (hA : TyP E n (setLetB k Dom' Val' Γpre) ty (.sort u))
    (hv : TyP E n (setLetB k Dom' Val' Γpre) term ty) (μ' : Level → Level) (ρ' : List Disp) :
    (finishBvarL hget hslot hA (.repl hv)).eps μ' ρ' = hv.eps μ' ρ' := rfl

theorem eps_finishBvarL_keep_slot {E : ResolvedEnv} {n k : Nat} {Γpre : LCtx}
    {Dom Val Dom' Val' : Expr Nat} {uSlot u : Level} {term ty : Expr Nat}
    (hget : Γpre.get? k = some (.letBinding Dom Val))
    (hslot : CvP E n (Γpre.drop (k + 1)) Dom Dom' (.sort uSlot))
    (hA : TyP E n (setLetB k Dom' Val' Γpre) ty (.sort u))
    {j : Nat} (hterm : term = .bvar j) (hlook : lookupType Γpre j = some ty) (hj : j = k)
    (μ' : Level → Level) (ρ' : List Disp) :
    (finishBvarL hget hslot hA (.keep j hterm hlook)).eps μ' ρ' =
      gateOut (levelIsZero (μ' uSlot)) (resolve ρ' k) := by
  unfold finishBvarL
  dsimp only
  rw [dif_pos hj, eps_tyCast, eps_retypeLetBVarSlot]

theorem eps_finishBvarL_keep_ne {E : ResolvedEnv} {n k : Nat} {Γpre : LCtx}
    {Dom Val Dom' Val' : Expr Nat} {uSlot u : Level} {term ty : Expr Nat}
    (hget : Γpre.get? k = some (.letBinding Dom Val))
    (hslot : CvP E n (Γpre.drop (k + 1)) Dom Dom' (.sort uSlot))
    (hA : TyP E n (setLetB k Dom' Val' Γpre) ty (.sort u))
    {j : Nat} (hterm : term = .bvar j) (hlook : lookupType Γpre j = some ty) (hj : j ≠ k)
    (μ' : Level → Level) (ρ' : List Disp) :
    (finishBvarL hget hslot hA (.keep j hterm hlook)).eps μ' ρ' =
      gateOut (levelIsZero (μ' u)) (resolve ρ' j) := by
  unfold finishBvarL
  dsimp only
  rw [dif_neg hj, eps_tyCast]
  exact eps_bvar_gateOut μ' ρ'

theorem eps_finishBvarL_retype_slot {E : ResolvedEnv} {n k : Nat} {Γpre : LCtx}
    {Dom Val Dom' Val' : Expr Nat} {uSlot u : Level} {term ty : Expr Nat}
    (hget : Γpre.get? k = some (.letBinding Dom Val))
    (hslot : CvP E n (Γpre.drop (k + 1)) Dom Dom' (.sort uSlot))
    (hA : TyP E n (setLetB k Dom' Val' Γpre) ty (.sort u))
    {j : Nat} {B : Expr Nat} (hterm : term = .bvar j) (hlook : lookupType Γpre j = some B)
    (hc : ConvChain E n (setLetB k Dom' Val' Γpre) B ty) (hj : j = k)
    (μ' : Level → Level) (ρ' : List Disp) :
    (finishBvarL hget hslot hA (.retype j B hterm hlook hc)).eps μ' ρ' =
      gateOut (levelIsZero (μ' uSlot)) (resolve ρ' k) := by
  unfold finishBvarL
  dsimp only
  rw [dif_pos hj, eps_convChain_apply, eps_tyCast, eps_retypeLetBVarSlot]

theorem eps_finishBvarL_retype_ne {E : ResolvedEnv} {n k : Nat} {Γpre : LCtx}
    {Dom Val Dom' Val' : Expr Nat} {uSlot u : Level} {term ty : Expr Nat}
    (hget : Γpre.get? k = some (.letBinding Dom Val))
    (hslot : CvP E n (Γpre.drop (k + 1)) Dom Dom' (.sort uSlot))
    (hA : TyP E n (setLetB k Dom' Val' Γpre) ty (.sort u))
    {j : Nat} {B : Expr Nat} (hterm : term = .bvar j) (hlook : lookupType Γpre j = some B)
    (hc : ConvChain E n (setLetB k Dom' Val' Γpre) B ty) (hj : j ≠ k)
    (μ' : Level → Level) (ρ' : List Disp) :
    (finishBvarL hget hslot hA (.retype j B hterm hlook hc)).eps μ' ρ' =
      gateOut (levelIsZero (μ' (chainSort hA hc).1)) (resolve ρ' j) := by
  unfold finishBvarL
  dsimp only
  rw [dif_neg hj]
  generalize hcs : chainSort hA hc = cs
  cases cs with
  | mk u' hB =>
      dsimp only
      rw [eps_convChain_apply, eps_tyCast]
      exact eps_bvar_gateOut μ' ρ'

/-! ## §4 the base alignments and the bvar assembly -/

/-- The gate answers a finished variable needs, by the shape of its walk: a surviving slot
    hit compares the original provider with the slot's domain (`uSlot`); a replacement
    compares it with the hit site's formation gate; a non-slot bridge chain supplies its
    junction and terminal bits. -/
def BvarGate (μ' : Level → Level) (b : Bool) (uSlot : Level) (k : Nat) (u' : Level)
    (site : Option ((Level → Level) × Level)) {E : ResolvedEnv} {n : Nat} {pre fin : LCtx}
    {term ty : Expr Nat} : BHit E n pre fin term ty → Prop
  | .keep j _ _ => j = k → b = levelIsZero (μ' uSlot)
  | .repl _ => ∀ σo uo, site = some (σo, uo) → b = levelIsZero (σo uo)
  | .retype j _ _ _ hc =>
      (j = k → b = levelIsZero (μ' uSlot)) ∧
      (j ≠ k → ChainJunctionBits μ' (convChainLevels hc) ∧ ChainEndBit μ' u' (convChainLevels hc))

/-- The bvar case: the original gate-and-resolve, under the pending actions, against the
    finished variable's erasure. `b` is the original provider's gate, which is `H`'s gate
    (`hb`) because `H` is the original provider transported. -/
theorem rel_finishBvarL {tbl : List CRule} {μ' : Level → Level} {ρ' : List Disp}
    {E : ResolvedEnv} {n k : Nat} {Γpre : LCtx} {Dom Val Dom' Val' : Expr Nat}
    {uSlot u' : Level} {term ty : Expr Nat}
    (hget : Γpre.get? k = some (.letBinding Dom Val))
    (hslot : CvP E n (Γpre.drop (k + 1)) Dom Dom' (.sort uSlot))
    (hA : TyP E n (setLetB k Dom' Val' Γpre) ty (.sort u'))
    (w : BHit E n Γpre (setLetB k Dom' Val' Γpre) term ty)
    {L : ETm} {site : Option ((Level → Level) × Level)} (b : Bool)
    (hb : b = levelIsZero (μ' u'))
    (hrel : BHitRel tbl μ' ρ' L site w) (hgate : BvarGate μ' b uSlot k u' site w) :
    Rel tbl (gateOut b L) ((finishBvarL hget hslot hA w).eps μ' ρ') := by
  cases w with
  | keep j hterm hlook =>
      obtain ⟨-, hr⟩ := hrel
      by_cases hj : j = k
      · rw [eps_finishBvarL_keep_slot hget hslot hA hterm hlook hj, ← hgate hj]
        subst hj
        cases b
        · exact hr
        · exact Rel.star tbl
      · rw [eps_finishBvarL_keep_ne hget hslot hA hterm hlook hj, ← hb]
        cases b
        · exact hr
        · exact Rel.star tbl
  | repl hv =>
      obtain ⟨σo, uo, hsite, hst, hr⟩ := hrel
      rw [eps_finishBvarL_repl]
      have hbo : b = levelIsZero (σo uo) := hgate σo uo hsite
      cases b
      · exact hr
      · rw [hst.mpr hbo.symm]
        exact Rel.star tbl
  | retype j B hterm hlook hc =>
      obtain ⟨-, hr⟩ := hrel
      by_cases hj : j = k
      · rw [eps_finishBvarL_retype_slot hget hslot hA hterm hlook hc hj, ← hgate.1 hj]
        subst hj
        cases b
        · exact hr
        · exact Rel.star tbl
      · rw [eps_finishBvarL_retype_ne hget hslot hA hterm hlook hc hj, chainSort_fst]
        obtain ⟨hjun, hend⟩ := hgate.2 hj
        rw [chain_gate μ' _ u' hjun hend, ← hb]
        cases b
        · exact hr
        · exact Rel.star tbl

end Rcic.Syn

#print axioms Rcic.Syn.eps_bvar_gateOut
#print axioms Rcic.Syn.chain_gate
#print axioms Rcic.Syn.chainSort_fst
#print axioms Rcic.Syn.eps_convChain_apply
#print axioms Rcic.Syn.eps_retypeLetBVarSlot
#print axioms Rcic.Syn.eps_finishBvarL_keep_slot
#print axioms Rcic.Syn.eps_finishBvarL_keep_ne
#print axioms Rcic.Syn.eps_finishBvarL_retype_slot
#print axioms Rcic.Syn.eps_finishBvarL_retype_ne
#print axioms Rcic.Syn.rel_finishBvarL
