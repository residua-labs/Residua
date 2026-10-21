import rcic.RcicSynStepCore4
import rcic.RcicSynPbBvarFrame
import rcic.RcicSynSortPBit

/-!
# `StepSuppliers.pb_case` — assembled, `closure_claim = 0`

The conclusion is `CaseStep Aw tbl (.pb D DT S σ ρ)`. This is not unconditional
`pb_case` and not `AllBelowScoped`.

`TyP.bvar` calls landed #7615 `pb_bvar_caseStep_frame` (`RcicSynPbBvarFrame`)
at every frame. The only data that call still takes is `PbBvarSpinePorts`
(`DispForC`, `entrySort`, `SpineLetPBit`): no `Issues` row produces them.
`PbFrame` and `PrefixBvarBit` are not re-declared. `pb_issued_letValue` is not
re-aliased (it answers a tail entry, not `PBit σ ρ D DT`).

Every other head discharges an induction-hypothesis answer by an `Issues` row
plus `Before`, or proves it outright:

* `const` — `occ_bitCoh` at `(0,[0])×(1,[])`, then `pbit_const_of_bitCoh`. No port.
* `lit` — `occ_pb` at `(0,[0])×(1,[])`, then `pbit_lit_iff`. No port.
* `sort`, `pi` — `pbit_reg_of_isSortOrPiHead` from `Demand.hom`. The port is
  `BitCoh σ D.reg.2 DT` only. Regularity is not a port.
* `app`, `letE` — `occ_bitCoh` at `[2]` / `[3]` against `DT`. The port is
  `PBit σ ρ D hT` only. The issued `BitCoh` is not a port.
* `esub` — `PBit σ ρ hv hvT` is `occ_pb` at `[1]×[2]` on the relevant-hole
  branch. The port is the inner `PBit` at `insertDisp` (different context)
  plus the cross-context level bit.

`CvP.fsub` is not a `TyP` head, so it is not a `pb` case. `TyP.wk` is a head
and its inner `PBit` lives in the pre-insert context, so it is not an
`occ_pb` at this site; that residual stays. The other residuals (`lam`,
`lsub`, `linst`, `ewk`, `cctx`, `conv`) are the same kind of fact: a different
context, a fresh regularity node, or a path that depends on the conversion
constructor. None of them is `PbPorts`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- Left payload strictly lighter, right payload unchanged. The parent must be
a single atom (`sort` / `bvar` / `const` / `pi` / `lam` / `app` / `letE` /
`lit` / `conv`). -/
private theorem pb_left_lex (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {eX TX e T : Expr Nat}
    (X : TyP E n Γ eX TX) (D : TyP E n Γ e T)
    {s : Level} {T₂ : Expr Nat} (DT : TyP E n Γ T₂ (.sort s))
    (hat : D.atoms Aw = [D.wt Aw]) (hw : X.wt Aw < D.wt Aw) :
    LexDM (tyPairMeas Aw X DT) (tyPairMeas Aw D DT) :=
  lex_of_dm (dmStep_append_right (dmStep_wt_lt_singleton Aw X D hat hw) (DT.atoms Aw))

private theorem pb_frame_lex (Aw : Nat → Nat)
    {Eₐ E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) {m' m : List Nat × Nat} (h : LexDM m' m) :
    LexDM (combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) m')
      (combMeas Aw (enrichCtxWfT_of_envWfT S.env S.ctx) m) :=
  lexDM_combMeas_mono Aw (enrichCtxWfT_of_envWfT S.env S.ctx) h

/-- What `pb_case` still has to be given, per head. A `bvar` value carries only
`PbBvarSpinePorts`. `const` and `lit` carry nothing. No constructor carries
`PbPorts`. -/
inductive PbHead :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → {s : Level} →
    TyP E n Γ e T → TyP E n Γ T (.sort s) → (Level → Level) → List Disp → Type where
  | bvar {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat} {u s : Level}
      {hlook : lookupType Γ i = some A} {hA : TyP E n Γ A (.sort u)}
      {DT : TyP E n Γ A (.sort s)} {σ : Level → Level} {ρ : List Disp}
      (spine : PbBvarSpinePorts hlook hA σ ρ) :
      PbHead (TyP.bvar E n Γ i A u hlook hA) DT σ ρ
  | const {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {r : Nat} {ls ls₀ : List Level} {m : CheckedMember} {u s : Level}
      {hres : E.members r = some m} {hlen : ls.length = m.arity}
      {hwf : levelsBounded n ls = true} {hls : eqNList ls ls₀}
      {hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)}
      {DT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort s)}
      {σ : Level → Level} {ρ : List Disp} :
      PbHead (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT) DT σ ρ
  | lit {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat} {T : Expr Nat} {s : Level}
      {hexp : TyP E n Γ (natExpand t) T}
      {DT : TyP E n Γ T (.sort s)} {σ : Level → Level} {ρ : List Disp} :
      PbHead (TyP.lit E n Γ t T hexp) DT σ ρ
  | sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l k s : Level} {h : eqN k (.succ l)}
      {DT : TyP E n Γ (.sort k) (.sort s)} {σ : Level → Level} {ρ : List Disp}
      (coh : BitCoh σ (TyP.sort E n Γ l k h).reg.2 DT) :
      PbHead (TyP.sort E n Γ l k h) DT σ ρ
  | pi {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} {u v s : Level}
      {hA : TyP E n Γ A (.sort u)} {hB : TyP E n (.assumption A :: Γ) B (.sort v)}
      {DT : TyP E n Γ (.sort (.imax u v)) (.sort s)}
      {σ : Level → Level} {ρ : List Disp}
      (coh : BitCoh σ (TyP.pi E n Γ A u B v hA hB).reg.2 DT) :
      PbHead (TyP.pi E n Γ A u B v hA hB) DT σ ρ
  | lam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A body B : Expr Nat} {u v s : Level}
      {hA : TyP E n Γ A (.sort u)}
      {hbody : TyP E n (.assumption A :: Γ) body B}
      {hB : TyP E n (.assumption A :: Γ) B (.sort v)}
      {DT : TyP E n Γ (.pi A B) (.sort s)} {σ : Level → Level} {ρ : List Disp}
      (pbody : PBit σ (binderDisp (levelIsZero (σ u)) :: ρ) hbody hB)
      (hbit : levelIsZero (σ v) = levelIsZero (σ s)) :
      PbHead (TyP.lam E n Γ A u body B v hA hbody hB) DT σ ρ
  | app {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f a A B : Expr Nat} {w s : Level}
      {hf : TyP E n Γ f (.pi A B)} {ha : TyP E n Γ a A}
      {hT : TyP E n Γ (instantiate0 a B) (.sort w)}
      {DT : TyP E n Γ (instantiate0 a B) (.sort s)}
      {σ : Level → Level} {ρ : List Disp}
      (pbit : PBit σ ρ (TyP.app E n Γ f a A B w hf ha hT) hT) :
      PbHead (TyP.app E n Γ f a A B w hf ha hT) DT σ ρ
  | letE {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {A value B body : Expr Nat} {u w s : Level}
      {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ value A}
      {hb : TyP E n (.letBinding A value :: Γ) body B}
      {hT : TyP E n Γ (instantiate0 value B) (.sort w)}
      {DT : TyP E n Γ (instantiate0 value B) (.sort s)}
      {σ : Level → Level} {ρ : List Disp}
      (pbit : PBit σ ρ (TyP.letE E n Γ A u value B body w hA hv hb hT) hT) :
      PbHead (TyP.letE E n Γ A u value B body w hA hv hb hT) DT σ ρ
  | conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A B : Expr Nat} {u s : Level}
      {h : TyP E n Γ e A} {hc : CvP E n Γ A B (.sort u)}
      {DT : TyP E n Γ B (.sort s)} {σ : Level → Level} {ρ : List Disp}
      (inner : PBit σ ρ h hc.dl) (coh : BitCoh σ hc.dr DT) :
      PbHead (TyP.conv E n Γ e A B u h hc) DT σ ρ
  | wk {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {e A : Expr Nat} {d : LocalDecl} {c : Nat} {s : Level}
      {D₀ : TyP E n Γ e A}
      {DT : TyP E n (insertAt d c Γ) (lift c 1 A) (.sort s)}
      {σ : Level → Level} {ρ : List Disp}
      (inner : PBit σ (removeAt ρ c) D₀ D₀.reg.2)
      (hbit : levelIsZero (σ D₀.reg.1) = levelIsZero (σ s)) :
      PbHead (TyP.wk E n Γ e A d c D₀) DT σ ρ
  | esub {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {e A t v : Expr Nat} {j : Nat} {u s : Level}
      {D₀ : TyP E n Γ e A} {hget : Γ[j]? = some (.assumption t)}
      {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
      {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
      {DT : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) A) (.sort s)}
      {σ : Level → Level} {ρ : List Disp}
      (inner : PBit σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ) D₀ D₀.reg.2)
      (hbit : levelIsZero (σ D₀.reg.1) = levelIsZero (σ s)) :
      PbHead (TyP.esub E n Γ e A t v j u D₀ hget hv hvT) DT σ ρ
  | lsub {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {e A t v : Expr Nat} {j : Nat} {u s : Level}
      {D₀ : TyP E n Γ e A} {hget : Γ[j]? = some (.letBinding t v)}
      {hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)}
      {hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)}
      {DT : TyP E n (substRemove v j Γ) (instantiate j (lift 0 j v) A) (.sort s)}
      {σ : Level → Level} {ρ : List Disp}
      (inner : PBit σ (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.eps σ ρ)) j ρ)
        D₀ D₀.reg.2)
      (hbit : levelIsZero (σ D₀.reg.1) = levelIsZero (σ s)) :
      PbHead (TyP.lsub E n Γ e A t v j u D₀ hget hv hvT) DT σ ρ
  | linst {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {a : Nat} {e A : Expr Nat} {ls : List Level} {s : Level}
      {hls : levelsBounded n ls = true} {hlen : ls.length = a}
      {D₀ : TyP E a Γ e A}
      {DT : TyP E n (instLvlsCtx ls Γ) (instantiateLevels ls A) (.sort s)}
      {σ : Level → Level} {ρ : List Disp}
      (inner : PBit (fun l => σ (instLevel ls l)) ρ D₀ D₀.reg.2)
      (coh : BitCoh σ (TyP.linst E a n Γ e A ls hls hlen D₀).reg.2 DT) :
      PbHead (TyP.linst E a n Γ e A ls hls hlen D₀) DT σ ρ
  | ewk {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {E₀ : ResolvedEnv} {e A : Expr Nat} {s : Level} {hext : EnvExt E₀ E}
      {D₀ : TyP E₀ n Γ e A} {DT : TyP E n Γ A (.sort s)}
      {σ : Level → Level} {ρ : List Disp}
      (inner : PBit σ ρ D₀ D₀.reg.2)
      (coh : BitCoh σ (TyP.ewk E₀ E n Γ e A hext D₀).reg.2 DT) :
      PbHead (TyP.ewk E₀ E n Γ e A hext D₀) DT σ ρ
  | cctx {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
      {e T A A' : Expr Nat} {u s : Level}
      {D₀ : TyP E n (.assumption A :: Γ) e T} {hA : CvP E n Γ A A' (.sort u)}
      {DT : TyP E n (.assumption A' :: Γ) T (.sort s)}
      {σ : Level → Level} {ρ : List Disp}
      (inner : PBit σ ρ D₀ D₀.reg.2)
      (coh : BitCoh σ (TyP.cctx E n Γ e T A A' u D₀ hA).reg.2 DT) :
      PbHead (TyP.cctx E n Γ e T A A' u D₀ hA) DT σ ρ

/-- `StepSuppliers.pb_case`, modulo `PbHead`. -/
theorem pb_case {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T : Expr Nat} {s : Level}
    {D : TyP E n Γ e T} {DT : TyP E n Γ T (.sort s)}
    {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    (head : PbHead D DT σ ρ) :
    CaseStep Aw tbl (.pb D DT S σ ρ) := by
  intro hq ih
  cases head with
  | bvar spine =>
      exact pb_bvar_caseStep_frame Aw tbl spine.C spine.dispC spine.sortAt spine.spineLet hq ih
  | @const Γ r ls ls₀ m u _s hres hlen hwf hls hT DT σ ρ =>
      have hw : hT.wt Aw < (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT).wt Aw := by
        simp only [TyP.wt]; omega
      have hcoh : BitCoh σ hT DT :=
        ih_local Aw tbl hq ih (.bitCoh hT DT S σ ρ)
          (Issues.occ_bitCoh (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := []) rfl rfl
            hq.ap.1 hq.ap.2) rfl
          (pb_frame_lex Aw S (pb_left_lex Aw hT
            (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT) DT rfl hw))
      exact pbit_const_of_bitCoh σ ρ hres hlen hwf hls hT DT hcoh
  | @lit Γ t T _s hexp DT σ ρ =>
      have hw : hexp.wt Aw < (TyP.lit E n Γ t T hexp).wt Aw := by
        simp only [TyP.wt]; omega
      have hpb : PBit σ ρ hexp DT :=
        ih_local Aw tbl hq ih (.pb hexp DT S σ ρ)
          (Issues.occ_pb (k₁ := 0) (p₁ := [0]) (k₂ := 1) (p₂ := []) rfl rfl
            hq.ap.1 hq.ap.2) rfl
          (pb_frame_lex Aw S (pb_left_lex Aw hexp (TyP.lit E n Γ t T hexp) DT rfl hw))
      exact (pbit_lit_iff σ ρ hexp DT).mpr hpb
  | @sort Γ l k _s h DT σ ρ coh =>
      exact pbit_of_reg_and_bitCoh (TyP.sort E n Γ l k h) DT
        (pbit_reg_of_isSortOrPiHead (D := TyP.sort E n Γ l k h) rfl hq.hom.levelSub ρ) coh
  | @pi Γ A B u v _s hA hB DT σ ρ coh =>
      exact pbit_of_reg_and_bitCoh (TyP.pi E n Γ A u B v hA hB) DT
        (pbit_reg_of_isSortOrPiHead (D := TyP.pi E n Γ A u B v hA hB) rfl hq.hom.levelSub ρ) coh
  | @lam Γ A body B u v _s hA hbody hB DT σ ρ pbody hbit =>
      exact pbit_lam_of_body σ ρ hA hbody hB DT pbody hbit
  | @app Γ f a A B w _s hf ha hT DT σ ρ pbit =>
      have hw : hT.wt Aw < (TyP.app E n Γ f a A B w hf ha hT).wt Aw := by
        simp only [TyP.wt]; omega
      have hcoh : BitCoh σ hT DT :=
        ih_local Aw tbl hq ih (.bitCoh hT DT S σ ρ)
          (Issues.occ_bitCoh (k₁ := 0) (p₁ := [2]) (k₂ := 1) (p₂ := []) rfl rfl
            hq.ap.1.2.2 hq.ap.2) rfl
          (pb_frame_lex Aw S (pb_left_lex Aw hT
            (TyP.app E n Γ f a A B w hf ha hT) DT rfl hw))
      exact pbit_of_reg_and_bitCoh (TyP.app E n Γ f a A B w hf ha hT) DT pbit hcoh
  | @letE Γ A value B body u w _s hA hv hb hT DT σ ρ pbit =>
      have hw : hT.wt Aw < (TyP.letE E n Γ A u value B body w hA hv hb hT).wt Aw := by
        simp only [TyP.wt]; omega
      have hcoh : BitCoh σ hT DT :=
        ih_local Aw tbl hq ih (.bitCoh hT DT S σ ρ)
          (Issues.occ_bitCoh (k₁ := 0) (p₁ := [3]) (k₂ := 1) (p₂ := []) rfl rfl
            hq.ap.1.2.2.2 hq.ap.2) rfl
          (pb_frame_lex Aw S (pb_left_lex Aw hT
            (TyP.letE E n Γ A u value B body w hA hv hb hT) DT rfl hw))
      exact pbit_of_reg_and_bitCoh (TyP.letE E n Γ A u value B body w hA hv hb hT) DT pbit hcoh
  | @conv Γ e A B u _s h hc DT σ ρ inner coh =>
      exact pbit_conv_of_inner σ ρ h hc DT inner coh
  | @wk Γ e A d c _s D₀ DT σ ρ inner hbit =>
      exact pbit_wk_of_inner σ ρ D₀ D₀.reg.2 DT inner hbit
  | @esub Γ e A t v j u _s D₀ hget hv hvT DT σ ρ inner hbit =>
      cases hu : levelIsZero (σ u) with
      | true =>
          have inner' : PBit σ (insertDisp .drop j ρ) D₀ D₀.reg.2 := by
            simpa [hu, binderDisp_drop] using inner
          exact pbit_esub_drop_of_inner σ ρ D₀ hget hv hvT D₀.reg.2 DT hu inner' hbit
      | false =>
          have inner' : PBit σ (insertDisp .keep j ρ) D₀ D₀.reg.2 := by
            simpa [hu, binderDisp_keep] using inner
          have hpv : PBit σ ρ hv hvT :=
            ih_local Aw tbl hq ih (.pb hv hvT S σ ρ)
              (Issues.occ_pb (k₁ := 0) (p₁ := [1]) (k₂ := 0) (p₂ := [2]) rfl rfl
                hq.ap.1.2.2.1 hq.ap.1.2.2.2) rfl
              (pb_frame_lex Aw S (lexDM_esub_val_pair Aw D₀ hget hv hvT DT))
          exact pbit_esub_keep_of_inner σ ρ D₀ hget hv hvT D₀.reg.2 DT hu hpv inner' hbit
  | @lsub Γ e A t v j u _s D₀ hget hv hvT DT σ ρ inner hbit =>
      exact pbit_lsub_of_inner σ ρ D₀ hget hv hvT D₀.reg.2 DT inner hbit
  | @linst Γ a e A ls _s hls hlen D₀ DT σ ρ inner coh =>
      exact pbit_of_reg_and_bitCoh (TyP.linst E a n Γ e A ls hls hlen D₀) DT
        (pbit_linst_reg_of_inner σ ρ hls hlen D₀ inner) coh
  | @ewk Γ E₀ e A _s hext D₀ DT σ ρ inner coh =>
      exact pbit_of_reg_and_bitCoh (TyP.ewk E₀ E n Γ e T hext D₀) DT
        ((pbit_ewk_reg_iff σ ρ hext D₀).mpr inner) coh
  | @cctx Γ e T A A' u _s D₀ hA DT σ ρ inner coh =>
      exact pbit_of_reg_and_bitCoh (TyP.cctx E n Γ e T A A' u D₀ hA) DT
        ((pbit_cctx_reg_iff σ ρ D₀ hA).mpr inner) coh

/-- A `TyP.bvar` goal, closed from `PbBvarSpinePorts` alone by landed
`pb_bvar_caseStep_frame` (design point B, every frame). -/
example {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {i : Nat} {A : Expr Nat} {u s : Level}
    {hlook : lookupType Γ i = some A} {hA : TyP E n Γ A (.sort u)}
    {DT : TyP E n Γ A (.sort s)}
    (Aw : Nat → Nat) (tbl : List CRule)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (spine : PbBvarSpinePorts hlook hA σ ρ) :
    CaseStep Aw tbl (.pb (TyP.bvar E n Γ i A u hlook hA) DT S σ ρ) :=
  pb_bvar_caseStep_frame Aw tbl spine.C spine.dispC spine.sortAt spine.spineLet

/-- A `TyP.const` goal, closed by `pb_case` with no residual port. -/
example {Eₐ E₀ E : ResolvedEnv} {n₀ n : Nat} {Γ₀ Γ : LCtx}
    {r : Nat} {ls ls₀ : List Level} {m : CheckedMember} {u s : Level}
    {hres : E.members r = some m} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true} {hls : eqNList ls ls₀}
    {hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)}
    {DT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort s)}
    (Aw : Nat → Nat) (tbl : List CRule)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    CaseStep Aw tbl
      (.pb (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT) DT S σ ρ) :=
  pb_case Aw tbl PbHead.const

end Rcic.Syn
