import rcic.RcicIota
import rcic.RcicSynLetTransportCL
import rcic.RcicSynLetRel

/-!
# BelowC mixed interpreter, part 2 — §7 ordinary lets and the const middle

`research/rcic/sortrow/BELOWC_MIXED_INTERPRETER.md` §7 (docs PR #7477), as standalone
compositions over the landed objects. Mixed means: the two sides carry their own
`(E, n, Γ)` and their own erased route `(σ, ρ)`; they are linked only by the displayed
requests, never by a shared context.

**Ordinary lets.** `I_N := letSub hb hv hA` and **(L)** `e[N] = e[I_N]` is the landed
`letSub_eps_eq_letE` (R2's `localize 0 r = r` is inside it). Two matching displayed lets
therefore compare exactly when their `letSub` normalizations compare, at each side's own
route (`mixedCL_letE_iff_letSub`, `mixedTag_letE_iff_letSub`, `mixedRel_letE_iff_letSub`);
the MEUT of the two lets is the three-link chain `MCL[hT_L, Reg I_L]`, `MEUT[I_L, I_R]`,
`MCL[Reg I_R, hT_R]` (`mixedEUT_letE_of_letSub`; a let's regularity is its `hT`, by `rfl`).
Not for changed-value `CvP.letE` reducts (those are Wall 2, `RcicSynMixedUSurface`).

**The const middle.** A native list action on a displayed constant erases to the mapped
level vector (`eps_linst_const`). The canonical-list common subject: starting at a recorded
list `L` of the member's arity, every native list action `vs` is one
`instantiateLevels_compose` step — bounded inner expression, unrestricted outer list — so a
word of actions is a `foldl` on the list (`instantiateLevels_foldl`), and two sides whose
final vectors agree have the same `Y` subject (`common_subject_of_final_vectors`,
`common_mtype_subject` through `EnvLevelsT`). Within one side, `eqNList a ls` (alias vs
recorded) gives `eqN (μ (instLevel a ℓ)) (μ (instLevel ls ℓ))` for every `ℓ`, and `lvlEq_eps`
on the same `P`, display and continuation gives `e[X] ≈ e[Y]`
(`convMod_eps_alias_canonical`, `convMod_linst_alias_canonical`). The six-link chain
`e[H_L] ≈ e[X_L] ≈ e[Y_L] ≈ e[Y_R] ≈ e[X_R] ≈ e[H_R]` composes the three requests **(C)**
with the two within-side congruences transported through each side's erased outer word
(`mixedEUT_const_middle`, via `rel_applyActs`). The const/const MCL and Tag rows read the
gates: same bit, and at a relevant bit the common displayed vector (`mixedCL_const_nodes`,
`mixedTag_const_nodes`).

Not here: the gate itself (it is the landed `mixedBit_finish` on the SN services and the
regularity-level MEUT — no new lemma), the δ observation exchange (its own request family),
and the payments `wt(P) < Aw(r)` (part 1, the measure). `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 ordinary lets: (L) at both routes -/

/-- §7 (L), MCL: two displayed lets compare iff their `letSub` normalizations compare, each
    at its own erased route. -/
theorem mixedCL_letE_iff_letSub {tbl : List CRule}
    {EL : ResolvedEnv} {nL : Nat} {ΓL : LCtx} {AL vL bL BL : Expr Nat} {uL wL : Level}
    (hAL : TyP EL nL ΓL AL (.sort uL)) (hvL : TyP EL nL ΓL vL AL)
    (hbL : TyP EL nL (.letBinding AL vL :: ΓL) bL BL)
    (hTL : TyP EL nL ΓL (instantiate0 vL BL) (.sort wL))
    {ER : ResolvedEnv} {nR : Nat} {ΓR : LCtx} {AR vR bR BR : Expr Nat} {uR wR : Level}
    (hAR : TyP ER nR ΓR AR (.sort uR)) (hvR : TyP ER nR ΓR vR AR)
    (hbR : TyP ER nR (.letBinding AR vR :: ΓR) bR BR)
    (hTR : TyP ER nR ΓR (instantiate0 vR BR) (.sort wR))
    (σL : Level → Level) (ρL : List Disp) (σR : Level → Level) (ρR : List Disp) :
    ConvMod (EStep tbl) LvlEq
        ((TyP.letE EL nL ΓL AL uL vL BL bL wL hAL hvL hbL hTL).eps σL ρL)
        ((TyP.letE ER nR ΓR AR uR vR BR bR wR hAR hvR hbR hTR).eps σR ρR) ↔
      ConvMod (EStep tbl) LvlEq
        ((letSub hbL hvL hAL).eps σL ρL) ((letSub hbR hvR hAR).eps σR ρR) := by
  rw [letSub_eps_eq_letE hAL hvL hbL hTL σL ρL, letSub_eps_eq_letE hAR hvR hbR hTR σR ρR]

/-- §7 (L), Tag: the star status of two displayed lets is that of their `letSub`
    normalizations. -/
theorem mixedTag_letE_iff_letSub
    {EL : ResolvedEnv} {nL : Nat} {ΓL : LCtx} {AL vL bL BL : Expr Nat} {uL wL : Level}
    (hAL : TyP EL nL ΓL AL (.sort uL)) (hvL : TyP EL nL ΓL vL AL)
    (hbL : TyP EL nL (.letBinding AL vL :: ΓL) bL BL)
    (hTL : TyP EL nL ΓL (instantiate0 vL BL) (.sort wL))
    {ER : ResolvedEnv} {nR : Nat} {ΓR : LCtx} {AR vR bR BR : Expr Nat} {uR wR : Level}
    (hAR : TyP ER nR ΓR AR (.sort uR)) (hvR : TyP ER nR ΓR vR AR)
    (hbR : TyP ER nR (.letBinding AR vR :: ΓR) bR BR)
    (hTR : TyP ER nR ΓR (instantiate0 vR BR) (.sort wR))
    (σL : Level → Level) (ρL : List Disp) (σR : Level → Level) (ρR : List Disp) :
    ((TyP.letE EL nL ΓL AL uL vL BL bL wL hAL hvL hbL hTL).eps σL ρL = .star ↔
        (TyP.letE ER nR ΓR AR uR vR BR bR wR hAR hvR hbR hTR).eps σR ρR = .star) ↔
      ((letSub hbL hvL hAL).eps σL ρL = .star ↔ (letSub hbR hvR hAR).eps σR ρR = .star) := by
  rw [letSub_eps_eq_letE hAL hvL hbL hTL σL ρL, letSub_eps_eq_letE hAR hvR hbR hTR σR ρR]

/-- §7 (L), MCL and Tag together: `Rel` of two displayed lets is `Rel` of their `letSub`
    normalizations. -/
theorem mixedRel_letE_iff_letSub {tbl : List CRule}
    {EL : ResolvedEnv} {nL : Nat} {ΓL : LCtx} {AL vL bL BL : Expr Nat} {uL wL : Level}
    (hAL : TyP EL nL ΓL AL (.sort uL)) (hvL : TyP EL nL ΓL vL AL)
    (hbL : TyP EL nL (.letBinding AL vL :: ΓL) bL BL)
    (hTL : TyP EL nL ΓL (instantiate0 vL BL) (.sort wL))
    {ER : ResolvedEnv} {nR : Nat} {ΓR : LCtx} {AR vR bR BR : Expr Nat} {uR wR : Level}
    (hAR : TyP ER nR ΓR AR (.sort uR)) (hvR : TyP ER nR ΓR vR AR)
    (hbR : TyP ER nR (.letBinding AR vR :: ΓR) bR BR)
    (hTR : TyP ER nR ΓR (instantiate0 vR BR) (.sort wR))
    (σL : Level → Level) (ρL : List Disp) (σR : Level → Level) (ρR : List Disp) :
    Rel tbl ((TyP.letE EL nL ΓL AL uL vL BL bL wL hAL hvL hbL hTL).eps σL ρL)
        ((TyP.letE ER nR ΓR AR uR vR BR bR wR hAR hvR hbR hTR).eps σR ρR) ↔
      Rel tbl ((letSub hbL hvL hAL).eps σL ρL) ((letSub hbR hvR hAR).eps σR ρR) := by
  rw [letSub_eps_eq_letE hAL hvL hbL hTL σL ρL, letSub_eps_eq_letE hAR hvR hbR hTR σR ρR]

/-- §7 (L), MEUT: `e[hT_L] ≈ r[I_L] ≈ r[I_R] ≈ e[hT_R]` — the three requests
    `MCL[hT_L, Reg I_L]`, `MEUT[I_L, I_R]`, `MCL[Reg I_R, hT_R]`; a let's regularity is its
    `hT` (definitional). -/
theorem mixedEUT_letE_of_letSub {tbl : List CRule}
    {EL : ResolvedEnv} {nL : Nat} {ΓL : LCtx} {AL vL bL BL : Expr Nat} {uL wL : Level}
    (hAL : TyP EL nL ΓL AL (.sort uL)) (hvL : TyP EL nL ΓL vL AL)
    (hbL : TyP EL nL (.letBinding AL vL :: ΓL) bL BL)
    (hTL : TyP EL nL ΓL (instantiate0 vL BL) (.sort wL))
    {ER : ResolvedEnv} {nR : Nat} {ΓR : LCtx} {AR vR bR BR : Expr Nat} {uR wR : Level}
    (hAR : TyP ER nR ΓR AR (.sort uR)) (hvR : TyP ER nR ΓR vR AR)
    (hbR : TyP ER nR (.letBinding AR vR :: ΓR) bR BR)
    (hTR : TyP ER nR ΓR (instantiate0 vR BR) (.sort wR))
    {σL : Level → Level} {ρL : List Disp} {σR : Level → Level} {ρR : List Disp}
    (q₁ : ConvMod (EStep tbl) LvlEq (hTL.eps σL ρL) ((letSub hbL hvL hAL).reg.2.eps σL ρL))
    (q₂ : ConvMod (EStep tbl) LvlEq
      ((letSub hbL hvL hAL).reg.2.eps σL ρL) ((letSub hbR hvR hAR).reg.2.eps σR ρR))
    (q₃ : ConvMod (EStep tbl) LvlEq ((letSub hbR hvR hAR).reg.2.eps σR ρR) (hTR.eps σR ρR)) :
    ConvMod (EStep tbl) LvlEq
      ((TyP.letE EL nL ΓL AL uL vL BL bL wL hAL hvL hbL hTL).reg.2.eps σL ρL)
      ((TyP.letE ER nR ΓR AR uR vR BR bR wR hAR hvR hbR hTR).reg.2.eps σR ρR) :=
  q₁.trans (q₂.trans q₃)

/-! ## §2 the const middle -/

/-- A native list action on a displayed constant, erased: the level vector is mapped by the
    action, then by the map. -/
theorem eps_linst_const {E : ResolvedEnv} {a n : Nat} {Γ : LCtx} {r : Nat} {ls ls₀ : List Level}
    {m : CheckedMember} {u : Level} {hres : E.members r = some m} {hlen : ls.length = m.arity}
    {hwf : levelsBounded a ls = true} {hls : eqNList ls ls₀}
    {hT : TyP E a Γ (instantiateLevels ls₀ m.mtype) (.sort u)}
    {vs : List Level} {hvs : levelsBounded n vs = true} {hlenv : vs.length = a}
    {σ : Level → Level} {ρ : List Disp} (hu : levelIsZero (σ (instLevel vs u)) = false) :
    (TyP.linst E a n Γ (.const r ls) (instantiateLevels ls₀ m.mtype) vs hvs hlenv
      (TyP.const E a Γ r ls ls₀ m u hres hlen hwf hls hT)).eps σ ρ =
      .const r ((ls.map (instLevel vs)).map σ) := by
  rw [eps_linst, eps_const_rel (σ := fun l => σ (instLevel vs l)) hu, List.map_map]
  rfl

/-- The canonical-list common subject, one word of native list actions at a time: with the
    inner expression bounded at the list's length (the outer list unrestricted), a word of
    actions on `instantiateLevels L e` is the same word folded on the list. -/
theorem instantiateLevels_foldl (e : Expr Nat) :
    (vss : List (List Level)) → (L : List Level) → exprLevelsBounded L.length e = true →
    vss.foldl (fun t vs => instantiateLevels vs t) (instantiateLevels L e) =
      instantiateLevels (vss.foldl (fun L vs => L.map (instLevel vs)) L) e
  | [], _, _ => rfl
  | vs :: vss, L, hb => by
      simp only [List.foldl]
      rw [instantiateLevels_compose vs L e hb]
      exact instantiateLevels_foldl e vss (L.map (instLevel vs))
        (by rw [List.length_map]; exact hb)

/-- Two sides whose final vectors are identified with one `L` have the same `Y` subject. -/
theorem common_subject_of_final_vectors (e : Expr Nat)
    (vssL vssR : List (List Level)) (LL LR : List Level)
    (hbL : exprLevelsBounded LL.length e = true) (hbR : exprLevelsBounded LR.length e = true)
    (hfin : vssL.foldl (fun L vs => L.map (instLevel vs)) LL =
      vssR.foldl (fun L vs => L.map (instLevel vs)) LR) :
    vssL.foldl (fun t vs => instantiateLevels vs t) (instantiateLevels LL e) =
      vssR.foldl (fun t vs => instantiateLevels vs t) (instantiateLevels LR e) := by
  rw [instantiateLevels_foldl e vssL LL hbL, instantiateLevels_foldl e vssR LR hbR, hfin]

/-- The same for a member's type: the boundedness is `EnvLevelsT` at the member's arity
    (the recorded lists have that length). -/
theorem common_mtype_subject {E : ResolvedEnv} (hEL : EnvLevelsT E) {r : Nat}
    {m : CheckedMember} (hres : E.members r = some m) {LL LR : List Level}
    (hlL : LL.length = m.arity) (hlR : LR.length = m.arity)
    (vssL vssR : List (List Level))
    (hfin : vssL.foldl (fun L vs => L.map (instLevel vs)) LL =
      vssR.foldl (fun L vs => L.map (instLevel vs)) LR) :
    vssL.foldl (fun t vs => instantiateLevels vs t) (instantiateLevels LL m.mtype) =
      vssR.foldl (fun t vs => instantiateLevels vs t) (instantiateLevels LR m.mtype) :=
  common_subject_of_final_vectors m.mtype vssL vssR LL LR
    (by rw [hlL]; exact (hEL r m hres).1) (by rw [hlR]; exact (hEL r m hres).1) hfin

/-- Within one side: `eqNList a ls` makes the alias map and the recorded map pointwise `eqN`
    under any `eqN`-preserving `μ`; `lvlEq_eps` on the same `P` and display gives `≈`. -/
theorem convMod_eps_alias_canonical {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} (P : TyP E n Γ e T) {μ : Level → Level}
    (hμ : ∀ {l l' : Level}, eqN l l' → eqN (μ l) (μ l')) {a ls : List Level}
    (h : eqNList a ls) (ρ : List Disp) :
    ConvMod (EStep tbl) LvlEq
      (P.eps (fun l => μ (instLevel a l)) ρ) (P.eps (fun l => μ (instLevel ls l)) ρ) :=
  .eqv (lvlEq_eps P (fun l => hμ (instLevel_eqNList h l)) (DispLvlEq.refl ρ))

/-- The same at the two `linst` views of `P` (alias list vs recorded list), same map, display
    and continuation, as a `Rel` (`≈` is shape-preserving): `e[X] ≈ e[Y]` with the same star
    status. -/
theorem rel_linst_alias_canonical {tbl : List CRule} {E : ResolvedEnv} {a' n : Nat}
    {Γ : LCtx} {e T : Expr Nat} (P : TyP E a' Γ e T) {a ls : List Level}
    (ha : levelsBounded n a = true) (hla : a.length = a')
    (hls : levelsBounded n ls = true) (hll : ls.length = a') (h : eqNList a ls)
    {μ : Level → Level} (hμ : ∀ {l l' : Level}, eqN l l' → eqN (μ l) (μ l')) (ρ : List Disp) :
    Rel tbl
      ((TyP.linst E a' n Γ e T a ha hla P).eps μ ρ)
      ((TyP.linst E a' n Γ e T ls hls hll P).eps μ ρ) := by
  rw [eps_linst, eps_linst]
  exact Rel.of_lvlEq tbl (lvlEq_eps P (fun l => hμ (instLevel_eqNList h l)) (DispLvlEq.refl ρ))

/-- The conversion half of `rel_linst_alias_canonical`. -/
theorem convMod_linst_alias_canonical {tbl : List CRule} {E : ResolvedEnv} {a' n : Nat}
    {Γ : LCtx} {e T : Expr Nat} (P : TyP E a' Γ e T) {a ls : List Level}
    (ha : levelsBounded n a = true) (hla : a.length = a')
    (hls : levelsBounded n ls = true) (hll : ls.length = a') (h : eqNList a ls)
    {μ : Level → Level} (hμ : ∀ {l l' : Level}, eqN l l' → eqN (μ l) (μ l')) (ρ : List Disp) :
    ConvMod (EStep tbl) LvlEq
      ((TyP.linst E a' n Γ e T a ha hla P).eps μ ρ)
      ((TyP.linst E a' n Γ e T ls hls hll P).eps μ ρ) :=
  (rel_linst_alias_canonical P ha hla hls hll h hμ ρ).conv

/-- §7 (C), the six-link chain `e[H_L] ≈ e[X_L] ≈ e[Y_L] ≈ e[Y_R] ≈ e[X_R] ≈ e[H_R]`: the three
    requests `Mixed[H_L, X_L]`, `Mixed[Y_L, Y_R]`, `Mixed[H_R, X_R]` (as `q₁`, `q₂`, `q₃`, each
    side's view of the one admission `P` taken through its erased outer word `applyActs acts`)
    and the two within-side congruences, transported through the words by `rel_applyActs`. -/
theorem mixedEUT_const_middle {tbl : List CRule} (hcl : TableClosed tbl)
    {E : ResolvedEnv} {ar : Nat} {Γ₀ : LCtx} {e T : Expr Nat} (P : TyP E ar Γ₀ e T)
    {nL : Nat} {aL lsL : List Level}
    (haL : levelsBounded nL aL = true) (hlaL : aL.length = ar)
    (hlsL : levelsBounded nL lsL = true) (hllL : lsL.length = ar) (hL : eqNList aL lsL)
    {μL : Level → Level} (hμL : ∀ {l l' : Level}, eqN l l' → eqN (μL l) (μL l')) (ρL : List Disp)
    (actsL : List EAct) (hnsL : EActsNonStar actsL)
    {nR : Nat} {aR lsR : List Level}
    (haR : levelsBounded nR aR = true) (hlaR : aR.length = ar)
    (hlsR : levelsBounded nR lsR = true) (hllR : lsR.length = ar) (hR : eqNList aR lsR)
    {μR : Level → Level} (hμR : ∀ {l l' : Level}, eqN l l' → eqN (μR l) (μR l')) (ρR : List Disp)
    (actsR : List EAct) (hnsR : EActsNonStar actsR)
    {eHL eHR : ETm}
    (q₁ : ConvMod (EStep tbl) LvlEq eHL
      (applyActs actsL ((TyP.linst E ar nL Γ₀ e T aL haL hlaL P).eps μL ρL)))
    (q₂ : ConvMod (EStep tbl) LvlEq
      (applyActs actsL ((TyP.linst E ar nL Γ₀ e T lsL hlsL hllL P).eps μL ρL))
      (applyActs actsR ((TyP.linst E ar nR Γ₀ e T lsR hlsR hllR P).eps μR ρR)))
    (q₃ : ConvMod (EStep tbl) LvlEq
      (applyActs actsR ((TyP.linst E ar nR Γ₀ e T aR haR hlaR P).eps μR ρR)) eHR) :
    ConvMod (EStep tbl) LvlEq eHL eHR := by
  have cL := rel_linst_alias_canonical (tbl := tbl) P haL hlaL hlsL hllL hL hμL ρL
  have cR := rel_linst_alias_canonical (tbl := tbl) P haR hlaR hlsR hllR hR hμR ρR
  exact q₁.trans ((rel_applyActs hcl actsL hnsL cL).conv.trans
    (q₂.trans ((rel_applyActs hcl actsR hnsR cR.symm).conv.trans q₃)))

/-- §5 const/const, MCL: equal gates, and at a relevant bit the common displayed vector
    (`eqNList` of the two mapped level lists). -/
theorem mixedCL_const_nodes {tbl : List CRule}
    {EL : ResolvedEnv} {nL : Nat} {ΓL : LCtx} {r : Nat} {lsL ls₀L : List Level}
    {mL : CheckedMember} {uL : Level} (hresL : EL.members r = some mL)
    (hlenL : lsL.length = mL.arity) (hwfL : levelsBounded nL lsL = true) (hlsL : eqNList lsL ls₀L)
    (hTL : TyP EL nL ΓL (instantiateLevels ls₀L mL.mtype) (.sort uL))
    {ER : ResolvedEnv} {nR : Nat} {ΓR : LCtx} {lsR ls₀R : List Level}
    {mR : CheckedMember} {uR : Level} (hresR : ER.members r = some mR)
    (hlenR : lsR.length = mR.arity) (hwfR : levelsBounded nR lsR = true) (hlsR : eqNList lsR ls₀R)
    (hTR : TyP ER nR ΓR (instantiateLevels ls₀R mR.mtype) (.sort uR))
    {σL : Level → Level} {ρL : List Disp} {σR : Level → Level} {ρR : List Disp}
    (hgate : levelIsZero (σL uL) = levelIsZero (σR uR))
    (hvec : levelIsZero (σL uL) = false → eqNList (lsL.map σL) (lsR.map σR)) :
    ConvMod (EStep tbl) LvlEq
      ((TyP.const EL nL ΓL r lsL ls₀L mL uL hresL hlenL hwfL hlsL hTL).eps σL ρL)
      ((TyP.const ER nR ΓR r lsR ls₀R mR uR hresR hlenR hwfR hlsR hTR).eps σR ρR) := by
  cases hb : levelIsZero (σL uL) with
  | true =>
      rw [eps_const_proof hb, eps_const_proof (hgate.symm.trans hb)]
      exact .refl _
  | false =>
      rw [eps_const_rel hb, eps_const_rel (hgate.symm.trans hb)]
      exact .eqv (.const r (hvec hb))

/-- §5 const/const, Tag: the same gates. -/
theorem mixedTag_const_nodes
    {EL : ResolvedEnv} {nL : Nat} {ΓL : LCtx} {r : Nat} {lsL ls₀L : List Level}
    {mL : CheckedMember} {uL : Level} (hresL : EL.members r = some mL)
    (hlenL : lsL.length = mL.arity) (hwfL : levelsBounded nL lsL = true) (hlsL : eqNList lsL ls₀L)
    (hTL : TyP EL nL ΓL (instantiateLevels ls₀L mL.mtype) (.sort uL))
    {ER : ResolvedEnv} {nR : Nat} {ΓR : LCtx} {lsR ls₀R : List Level}
    {mR : CheckedMember} {uR : Level} (hresR : ER.members r = some mR)
    (hlenR : lsR.length = mR.arity) (hwfR : levelsBounded nR lsR = true) (hlsR : eqNList lsR ls₀R)
    (hTR : TyP ER nR ΓR (instantiateLevels ls₀R mR.mtype) (.sort uR))
    {σL : Level → Level} {ρL : List Disp} {σR : Level → Level} {ρR : List Disp}
    (hgate : levelIsZero (σL uL) = levelIsZero (σR uR)) :
    ((TyP.const EL nL ΓL r lsL ls₀L mL uL hresL hlenL hwfL hlsL hTL).eps σL ρL = .star ↔
      (TyP.const ER nR ΓR r lsR ls₀R mR uR hresR hlenR hwfR hlsR hTR).eps σR ρR = .star) := by
  cases hb : levelIsZero (σL uL) with
  | true =>
      rw [eps_const_proof hb, eps_const_proof (hgate.symm.trans hb)]
  | false =>
      rw [eps_const_rel hb, eps_const_rel (hgate.symm.trans hb)]
      exact Iff.intro (fun h => by cases h) (fun h => by cases h)

end Rcic.Syn

#print axioms Rcic.Syn.mixedCL_letE_iff_letSub
#print axioms Rcic.Syn.mixedTag_letE_iff_letSub
#print axioms Rcic.Syn.mixedRel_letE_iff_letSub
#print axioms Rcic.Syn.mixedEUT_letE_of_letSub
#print axioms Rcic.Syn.eps_linst_const
#print axioms Rcic.Syn.instantiateLevels_foldl
#print axioms Rcic.Syn.common_subject_of_final_vectors
#print axioms Rcic.Syn.common_mtype_subject
#print axioms Rcic.Syn.convMod_eps_alias_canonical
#print axioms Rcic.Syn.rel_linst_alias_canonical
#print axioms Rcic.Syn.convMod_linst_alias_canonical
#print axioms Rcic.Syn.mixedEUT_const_middle
#print axioms Rcic.Syn.mixedCL_const_nodes
#print axioms Rcic.Syn.mixedTag_const_nodes
