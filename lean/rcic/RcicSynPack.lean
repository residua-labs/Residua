import rcic.RcicSynBelow

/-!
# Syntactic sortRow, build step 3s — the mutual pack's induction hypothesis

`research/rcic/semantic/S3_ES_ARMS.md` §18. The six claims of `S0` §4 are
proved together by `WellFounded.fix` on `lexDM_wf`. This module is the
hypothesis that fix will supply, and the rule-node arms whose only
recursive calls are `ES`, `CL` and `PBit` (S0's PB).

`Below Aw tbl bound` says each claim holds at every derivation whose
measure is strictly `lexDM` below `bound`. A rule node passes the
`DMStep`s of `RcicSynBelow` through `lex_of_dm`; the summed weight is
not consulted (`Prod.Lex.left`).

`GenSpine` is not a field. An unrestricted pair of typings does not have
convertible erasures (`sort 0` against `sort 1`). The iota arm has to
name the spine premises (`S0` §4) before that claim can be quantified.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The order of the mutual induction (`lexDM_wf`). -/
abbrev LexDM := Prod.Lex DMStep (fun a b : Nat => a < b)

/-! ## §1 measures -/

/-- A conversion, as a point of `LexDM`. -/
def cvMeas (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T) : List Nat × Nat :=
  (h.atoms Aw, h.wt Aw)

/-- A typing, as a point of `LexDM`. -/
def tyMeas (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) : List Nat × Nat :=
  (D.atoms Aw, D.wt Aw)

/-- Two typings. `CL` and `PB` both use this multiset: each typing's atoms
    sit under the removed rule-node atom, and copies are a `DMStep`. -/
def tyPairMeas (Aw : Nat → Nat)
    {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx} {e₁ T₁ : Expr Nat}
    (D₁ : TyP E₁ n₁ Γ₁ e₁ T₁)
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂) : List Nat × Nat :=
  (D₁.atoms Aw ++ D₂.atoms Aw, D₁.wt Aw + D₂.wt Aw)

/-- A conversion together with one typing. `CTS` uses this multiset. -/
def cvTyMeas (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e T' : Expr Nat}
    (D : TyP E' n' Γ' e T') : List Nat × Nat :=
  (h.atoms Aw ++ D.atoms Aw, h.wt Aw + D.wt Aw)

/-! ## §2 the claims `ES` and `CL` do not already state -/

/-- Erased unique typing (`S0` §4). Two typings of one term have convertible
    erasures of their types. The type's erasure is `reg`: that derivation
    types the ascribed type at a sort, so its `eps` is the erasure of the
    type, not of the term. -/
def EUT (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T T' : Expr Nat}
    (D₁ : TyP E n Γ e T) (D₂ : TyP E n Γ e T') : Prop :=
  ConvMod (EStep tbl) LvlEq (D₁.reg.2.eps σ ρ) (D₂.reg.2.eps σ ρ)

/-- Sort agreement (`S0` §4). A conversion at `sort w` whose left endpoint
    is typed at `sort s` forces `eqN s w`. The conclusion is the
    object-language level, before `σ`. -/
def CTS {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (_h : CvP E n Γ X Y (.sort w)) (_DX : TyP E n Γ X (.sort s)) : Prop :=
  eqN s w

/-- The head proof-bit, after `σ` (`S0` §4, `S1` §3.4). `eps` computes the
    bit with `levelIsZero (σ s)`, so the claim is stated at `σ s` rather
    than at `s`. The name `PB` is the β parallel reduction in `RcicSynBeta`. -/
def PBit (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (_DT : TyP E n Γ T (.sort s)) : Prop :=
  D.eps σ ρ = .star ↔ levelIsZero (σ s) = true

/-- `true` is a proof domain (`drop`). `false` keeps an erased slot. -/
def binderDisp : Bool → Disp
  | true => .drop
  | false => .keep

theorem binderDisp_drop : binderDisp true = .drop := rfl

theorem binderDisp_keep : binderDisp false = .keep := rfl

/-- `linst` rebuilds `σ` as `σ ∘ instLevel`. Zero is fixed by `instLevel`,
    so a caller that already knows the outer bit of `sort 0` keeps it. -/
theorem levelIsZero_pres_inst {σ : Level → Level} {ls : List Level}
    (hz : levelIsZero (σ .zero) = true) :
    levelIsZero (σ (instLevel ls .zero)) = true := by
  rw [instLevel_zero]
  exact hz

/-- A level map produced from `id` by `linst` compositions (`S3` §40).
    It preserves `eqN` and keeps the proof bits of `.zero` (`true`) and
    `.succ l` (`false`). Without `succ_bit`, `σ := fun _ => .zero` falsifies
    `PBit` on `pinSortP` even in `[]` at `ρ = []` (`not_pbit_const_zero`). -/
structure LevelSub (σ : Level → Level) : Prop where
  eqN_map : ∀ {l l' : Level}, eqN l l' → eqN (σ l) (σ l')
  zero_bit : levelIsZero (σ .zero) = true
  succ_bit : ∀ l : Level, levelIsZero (σ (.succ l)) = false

theorem levelSub_id : LevelSub id where
  eqN_map := fun h => h
  zero_bit := rfl
  succ_bit := fun _ => rfl

theorem LevelSub.linst {σ : Level → Level} (hσ : LevelSub σ) (ls : List Level) :
    LevelSub (fun l => σ (instLevel ls l)) where
  eqN_map := fun h => hσ.eqN_map (eqN_instLevel h ls)
  zero_bit := levelIsZero_pres_inst hσ.zero_bit
  succ_bit := fun l => hσ.succ_bit (instLevel ls l)

/-- Sort coherence of two sort typings of one type (`S3` §40, Q10). -/
def SortCoh (σ : Level → Level)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (_D₁ : TyP E n Γ T (.sort u)) (_D₂ : TyP E n Γ T (.sort v)) : Prop :=
  eqN (σ u) (σ v)

/-- Bit coherence of two sort typings of one type (`S3` §40, Q10). -/
def BitCoh (σ : Level → Level)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (_D₁ : TyP E n Γ T (.sort u)) (_D₂ : TyP E n Γ T (.sort v)) : Prop :=
  levelIsZero (σ u) = levelIsZero (σ v)

theorem bitCoh_of_sortCoh {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    {D₁ : TyP E n Γ T (.sort u)} {D₂ : TyP E n Γ T (.sort v)}
    (h : SortCoh σ D₁ D₂) : BitCoh σ D₁ D₂ :=
  levelIsZero_congr h

/-! ## §2b reachable dispositions (`DispFor`, Q9) -/

/-- Dispositions that respect `Γ` at `σ` (`S3` §38, §40; Q9).
    `letDrop` and `letInline` cover both `letE` / `lsub` (`drop` on `★`,
    `inline` otherwise) and `CtxP.disp` (`inline` unconditionally). -/
inductive DispFor (σ : Level → Level) (E : ResolvedEnv) (n : Nat) : LCtx → List Disp → Prop
  | nil (hσ : LevelSub σ) : DispFor σ E n [] []
  | assumption {Γ : LCtx} {ρ : List Disp} {A : Expr Nat} {u : Level}
      (hΓ : DispFor σ E n Γ ρ) (hA : TyP E n Γ A (.sort u)) :
      DispFor σ E n (.assumption A :: Γ) (binderDisp (levelIsZero (σ u)) :: ρ)
  | letDrop {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {u : Level}
      (hΓ : DispFor σ E n Γ ρ) (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A)
      (hstar : hv.eps σ ρ = .star) :
      DispFor σ E n (.letBinding A v :: Γ) (.drop :: ρ)
  | letInline {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {u : Level}
      (hΓ : DispFor σ E n Γ ρ) (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A) :
      DispFor σ E n (.letBinding A v :: Γ) (.inline (hv.eps σ ρ) :: ρ)

theorem DispFor.levelSub {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} (h : DispFor σ E n Γ ρ) : LevelSub σ := by
  induction h with
  | nil hσ => exact hσ
  | assumption _ _ ih => exact ih
  | letDrop _ _ _ _ ih => exact ih
  | letInline _ _ _ ih => exact ih

theorem DispFor.length_eq {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} (h : DispFor σ E n Γ ρ) : ρ.length = Γ.length := by
  induction h with
  | nil => rfl
  | assumption _ _ ih => simp only [List.length_cons, ih]
  | letDrop _ _ _ _ ih => simp only [List.length_cons, ih]
  | letInline _ _ _ ih => simp only [List.length_cons, ih]

/-- Entry (Q9.2): `CtxP.disp` produces a `DispFor` at every `LevelSub` map. -/
theorem dispFor_of_ctxP {σ : Level → Level} (hσ : LevelSub σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hΓ : CtxP E n Γ) :
    DispFor σ E n Γ (hΓ.disp σ) := by
  induction hΓ with
  | nil => exact .nil hσ
  | assumption Γ₀ A u hΓ₀ hA ih =>
      have hd : CtxP.disp σ (.assumption E n Γ₀ A u hΓ₀ hA) =
          binderDisp (levelIsZero (σ u)) :: hΓ₀.disp σ := by
        cases hzu : levelIsZero (σ u) <;> simp only [CtxP.disp, binderDisp, hzu]
      rw [hd]
      exact .assumption ih hA
  | letBinding _ _ _ _ _ hA hv ih =>
      exact .letInline ih hA hv

/-- Entry at `σ = id` (Q9.2). -/
theorem dispFor_ctxP_id {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hΓ : CtxP E n Γ) :
    DispFor id E n Γ (hΓ.disp id) :=
  dispFor_of_ctxP levelSub_id hΓ

/-- Closure under `binderDisp` (Q9.1). -/
theorem dispFor_binderDisp {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {A : Expr Nat} {u : Level}
    (hρ : DispFor σ E n Γ ρ) (hA : TyP E n Γ A (.sort u)) :
    DispFor σ E n (.assumption A :: Γ) (binderDisp (levelIsZero (σ u)) :: ρ) :=
  .assumption hρ hA

theorem dispFor_assumption_drop {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {A : Expr Nat} {u : Level}
    (hρ : DispFor σ E n Γ ρ) (hA : TyP E n Γ A (.sort u))
    (hu : levelIsZero (σ u) = true) :
    DispFor σ E n (.assumption A :: Γ) (.drop :: ρ) := by
  have h := dispFor_binderDisp hρ hA
  rw [hu, binderDisp_drop] at h
  exact h

theorem dispFor_assumption_keep {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {A : Expr Nat} {u : Level}
    (hρ : DispFor σ E n Γ ρ) (hA : TyP E n Γ A (.sort u))
    (hu : levelIsZero (σ u) = false) :
    DispFor σ E n (.assumption A :: Γ) (.keep :: ρ) := by
  have h := dispFor_binderDisp hρ hA
  rw [hu, binderDisp_keep] at h
  exact h

/-- Closure under the `letE` / `lsub` value clause (Q9.1). -/
theorem dispFor_letClause {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {u : Level}
    (hρ : DispFor σ E n Γ ρ) (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A) :
    DispFor σ E n (.letBinding A v :: Γ)
      ((match hv.eps σ ρ with | .star => .drop | ev => .inline ev) :: ρ) := by
  cases h : hv.eps σ ρ with
  | star => exact .letDrop hρ hA hv h
  | bvar _ | sort _ | const _ _ | app _ _ | lam _ | pi _ _ =>
      simpa only [h] using DispFor.letInline hρ hA hv

/-- Closure under `insertDisp` at index `0` (`instEnd`, Q9.1). -/
theorem dispFor_insertDisp_zero {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {u : Level}
    (hρ : DispFor σ E n (substRemove v 0 (.assumption A :: Γ)) ρ)
    (hA : TyP E n Γ A (.sort u)) :
    DispFor σ E n (.assumption A :: Γ) (insertDisp (binderDisp (levelIsZero (σ u))) 0 ρ) :=
  .assumption hρ hA

theorem dispFor_insertDisp_zero_drop {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {u : Level}
    (hρ : DispFor σ E n (substRemove v 0 (.assumption A :: Γ)) ρ)
    (hA : TyP E n Γ A (.sort u)) (hu : levelIsZero (σ u) = true) :
    DispFor σ E n (.assumption A :: Γ) (insertDisp .drop 0 ρ) :=
  dispFor_assumption_drop hρ hA hu

theorem dispFor_insertDisp_zero_keep {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {u : Level}
    (hρ : DispFor σ E n (substRemove v 0 (.assumption A :: Γ)) ρ)
    (hA : TyP E n Γ A (.sort u)) (hu : levelIsZero (σ u) = false) :
    DispFor σ E n (.assumption A :: Γ) (insertDisp .keep 0 ρ) :=
  dispFor_assumption_keep hρ hA hu

/-- Closure under `insertDisp` at index `0` for a let-binding (`letSub`, Q9.1). -/
theorem dispFor_insertDisp_zero_let {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} {A v : Expr Nat} {u : Level}
    (hρ : DispFor σ E n (substRemove v 0 (.letBinding A v :: Γ)) ρ)
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A) :
    DispFor σ E n (.letBinding A v :: Γ)
      (insertDisp (match hv.eps σ ρ with | .star => .drop | ev => .inline ev) 0 ρ) :=
  dispFor_letClause hρ hA hv

/-- Closure under `removeAt` at index `0` (Q9.1). -/
theorem dispFor_removeAt_zero {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {d : LocalDecl} {disp : Disp} {ρ : List Disp}
    (hρ : DispFor σ E n (insertAt d 0 Γ) (disp :: ρ)) :
    DispFor σ E n Γ (removeAt (disp :: ρ) 0) := by
  cases hρ with
  | assumption hΓ _ => exact hΓ
  | letDrop hΓ _ _ _ => exact hΓ
  | letInline hΓ _ _ => exact hΓ

/-- Closure under environment extension (`ewk`, Q9.1). -/
theorem dispFor_ewk {σ : Level → Level} {E₀ E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} (hext : EnvExt E₀ E) (hρ : DispFor σ E₀ n Γ ρ) :
    DispFor σ E n Γ ρ := by
  induction hρ with
  | nil hσ => exact .nil hσ
  | assumption _ hA ih => exact .assumption ih (.ewk _ _ _ _ _ _ hext hA)
  | letDrop _ hA hv hstar ih =>
      exact .letDrop ih (.ewk _ _ _ _ _ _ hext hA) (.ewk _ _ _ _ _ _ hext hv) hstar
  | letInline _ hA hv ih =>
      exact .letInline ih (.ewk _ _ _ _ _ _ hext hA) (.ewk _ _ _ _ _ _ hext hv)

/-- Closure under `instLvlsCtx` (`linst`, Q9.1). -/
theorem dispFor_instLvlsCtx {σ : Level → Level} (hσ : LevelSub σ)
    {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx} {ρ : List Disp} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a')
    (hρ : DispFor (fun l => σ (instLevel ls l)) E a' Γ ρ) :
    DispFor σ E n (instLvlsCtx ls Γ) ρ := by
  induction hρ with
  | nil _ => exact .nil hσ
  | assumption _ hA ih =>
      exact .assumption ih (.linst _ _ _ _ _ _ ls hls hlen hA)
  | letDrop _ hA hv hstar ih =>
      exact .letDrop ih (.linst _ _ _ _ _ _ ls hls hlen hA)
        (.linst _ _ _ _ _ _ ls hls hlen hv) hstar
  | letInline _ hA hv ih =>
      exact .letInline ih (.linst _ _ _ _ _ _ ls hls hlen hA)
        (.linst _ _ _ _ _ _ ls hls hlen hv)

/-! ## §3 the hypothesis -/

/-- Every claim at measures strictly below `bound`, restricted to `DispFor`
    (Q9) and carrying `bitCoh` (Q10; S3 §38, §40). -/
structure Below (Aw : Nat → Nat) (tbl : List CRule) (bound : List Nat × Nat) : Prop where
  es : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T) (σ : Level → Level) (ρ : List Disp),
    DispFor σ E n Γ ρ → LexDM (cvMeas Aw h) bound → ES tbl σ ρ h
  cl : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T₁ T₂ : Expr Nat}
    (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂) (σ : Level → Level) (ρ : List Disp),
    DispFor σ E n Γ ρ → LexDM (tyPairMeas Aw D₁ D₂) bound → CL tbl σ ρ D₁ D₂
  eut : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T T' : Expr Nat}
    (D₁ : TyP E n Γ e T) (D₂ : TyP E n Γ e T') (σ : Level → Level) (ρ : List Disp),
    DispFor σ E n Γ ρ → LexDM (tyPairMeas Aw D₁ D₂) bound → EUT tbl σ ρ D₁ D₂
  cts : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat} {w s : Level}
    (h : CvP E n Γ X Y (.sort w)) (DX : TyP E n Γ X (.sort s)),
    LexDM (cvTyMeas Aw h DX) bound → CTS h DX
  pb : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)) (σ : Level → Level) (ρ : List Disp),
    DispFor σ E n Γ ρ → LexDM (tyPairMeas Aw D DT) bound → PBit σ ρ D DT
  bitCoh : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {T : Expr Nat} {u v : Level}
    (D₁ : TyP E n Γ T (.sort u)) (D₂ : TyP E n Γ T (.sort v)) (σ : Level → Level) (ρ : List Disp),
    DispFor σ E n Γ ρ → LexDM (tyPairMeas Aw D₁ D₂) bound → BitCoh σ D₁ D₂

/-! ## §4 structural `ES` arms -/

/-- `refl` is `CL` of the two endpoint typings (`below_refl`). -/
theorem es_of_below_refl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat}
    (ht : TyP E n Γ a A) (dl dr : TyP E n Γ a A)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (B : Below Aw tbl (cvMeas Aw (CvP.refl E n Γ a A ht dl dr))) :
    ES tbl σ ρ (CvP.refl E n Γ a A ht dl dr) := by
  refine es_refl ht dl dr ?_
  exact B.cl dl dr σ ρ hρ (lex_of_dm (below_refl Aw ht dl dr))

/-- `symm` is `ES` of the inner conversion and `CL` at each stored endpoint. -/
theorem es_of_below_symm (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A : Expr Nat}
    (h : CvP E n Γ a b A) (dl : TyP E n Γ b A) (dr : TyP E n Γ a A)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (B : Below Aw tbl (cvMeas Aw (CvP.symm E n Γ a b A h dl dr))) :
    ES tbl σ ρ (CvP.symm E n Γ a b A h dl dr) := by
  have steps := below_symm Aw h dl dr
  refine es_symm h dl dr ?_ ?_ ?_
  · exact B.es h σ ρ hρ (lex_of_dm steps.1)
  · exact B.cl dl h.dr σ ρ hρ (lex_of_dm steps.2.1)
  · exact B.cl h.dl dr σ ρ hρ (lex_of_dm steps.2.2)

/-- `trans` is `ES` of both links and `CL` across the three joints, including
    the stored endpoints (`S3` §7). -/
theorem es_of_below_trans (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b c A : Expr Nat}
    (h1 : CvP E n Γ a b A) (h2 : CvP E n Γ b c A)
    (dl : TyP E n Γ a A) (dr : TyP E n Γ c A)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (B : Below Aw tbl (cvMeas Aw (CvP.trans E n Γ a b c A h1 h2 dl dr))) :
    ES tbl σ ρ (CvP.trans E n Γ a b c A h1 h2 dl dr) := by
  have steps := below_trans Aw h1 h2 dl dr
  refine es_trans h1 h2 dl dr ?_ ?_ ?_ ?_ ?_
  · exact B.es h1 σ ρ hρ (lex_of_dm steps.1)
  · exact B.es h2 σ ρ hρ (lex_of_dm steps.2.1)
  · exact B.cl dl h1.dl σ ρ hρ (lex_of_dm steps.2.2.1)
  · exact B.cl h1.dr h2.dl σ ρ hρ (lex_of_dm steps.2.2.2.1)
  · exact B.cl h2.dr dr σ ρ hρ (lex_of_dm steps.2.2.2.2)

/-- `tyConv` reads `ES` of the inner conversion. The type conversion is not a call. -/
theorem es_of_below_tyConv (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A A' : Expr Nat} {u : Level}
    (h : CvP E n Γ a b A) (hA : CvP E n Γ A A' (.sort u))
    (dl : TyP E n Γ a A') (dr : TyP E n Γ b A')
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (B : Below Aw tbl (cvMeas Aw (CvP.tyConv E n Γ a b A A' u h hA dl dr))) :
    ES tbl σ ρ (CvP.tyConv E n Γ a b A A' u h hA dl dr) := by
  have steps := below_tyConv Aw h hA dl dr
  refine es_tyConv h hA dl dr ?_ ?_ ?_
  · exact B.es h σ ρ hρ (lex_of_dm steps.1)
  · exact B.cl dl h.dl σ ρ hρ (lex_of_dm steps.2.1)
  · exact B.cl h.dr dr σ ρ hρ (lex_of_dm steps.2.2)

/-- `irr` is `PB` on the two endpoints at the `Prop` typing. `DispFor.levelSub`
    supplies `levelIsZero (σ .zero) = true`. -/
theorem es_of_below_irr (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P p q : Expr Nat}
    (hP : TyP E n Γ P (.sort .zero)) (hp : TyP E n Γ p P) (hq : TyP E n Γ q P)
    (dl : TyP E n Γ p P) (dr : TyP E n Γ q P)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (B : Below Aw tbl (cvMeas Aw (CvP.irr E n Γ P p q hP hp hq dl dr))) :
    ES tbl σ ρ (CvP.irr E n Γ P p q hP hp hq dl dr) := by
  have steps := below_irr Aw hP hp hq dl dr
  have hz := hρ.levelSub.zero_bit
  refine es_irr_star hP hp hq dl dr ?_ ?_
  · exact (B.pb dl hP σ ρ hρ (lex_of_dm steps.1)).mpr hz
  · exact (B.pb dr hP σ ρ hρ (lex_of_dm steps.2.1)).mpr hz

end Rcic.Syn

#print axioms Rcic.Syn.binderDisp_drop
#print axioms Rcic.Syn.binderDisp_keep
#print axioms Rcic.Syn.levelIsZero_pres_inst
#print axioms Rcic.Syn.levelSub_id
#print axioms Rcic.Syn.LevelSub.linst
#print axioms Rcic.Syn.bitCoh_of_sortCoh
#print axioms Rcic.Syn.DispFor.levelSub
#print axioms Rcic.Syn.DispFor.length_eq
#print axioms Rcic.Syn.dispFor_of_ctxP
#print axioms Rcic.Syn.dispFor_ctxP_id
#print axioms Rcic.Syn.dispFor_binderDisp
#print axioms Rcic.Syn.dispFor_assumption_drop
#print axioms Rcic.Syn.dispFor_assumption_keep
#print axioms Rcic.Syn.dispFor_letClause
#print axioms Rcic.Syn.dispFor_insertDisp_zero
#print axioms Rcic.Syn.dispFor_insertDisp_zero_drop
#print axioms Rcic.Syn.dispFor_insertDisp_zero_keep
#print axioms Rcic.Syn.dispFor_insertDisp_zero_let
#print axioms Rcic.Syn.dispFor_removeAt_zero
#print axioms Rcic.Syn.dispFor_ewk
#print axioms Rcic.Syn.dispFor_instLvlsCtx
#print axioms Rcic.Syn.es_of_below_refl
#print axioms Rcic.Syn.es_of_below_symm
#print axioms Rcic.Syn.es_of_below_trans
#print axioms Rcic.Syn.es_of_below_tyConv
#print axioms Rcic.Syn.es_of_below_irr

