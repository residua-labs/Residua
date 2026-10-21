import rcic.RcicSynAdm
import rcic.RcicSynErase
import rcic.RcicSynInst

/-!
# Syntactic sortRow, build step 3d — erasure soundness, transport prefix

`research/rcic/semantic/S3_ES_ARMS.md` §7. `ES` is
`CvP.dl.eps ↔*_{E ∪ ≈} CvP.dr.eps`. The five transports (`wk`, `esub`, `linst`, `ewk`,
`cctx`) do not need `WellFounded.fix`: `eps` of a transported endpoint is `eps` of the
inner endpoint, renamed (`S1` §3.4). `es_transports` is that fold, by structural recursion.
What it leaves is one obligation per rule node (`isTransport = false`): the 18 `ConvT` arms
and `fsub`. Those are where the mutual induction spends its measure.

The rule-node lemmas here are the rewrite content of an arm. Each takes the coherence
facts the mutual induction will supply (`CL` of a stored endpoint against the child it
came from) and returns `ES`. A stored endpoint is its own derivation, not definitionally
the premise's endpoint (`CvP.trans` carries `dl` beside `h1`), so the call is
`CL(dl, h1.dl)` as well as `CL(h1.dr, h2.dl)`. Both sit strictly below the node
(`CvP.wt_dl_lt`, `CvP.wt_dr_lt`).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `↔*` along `lift` -/

theorem convMod_lift {tbl : List CRule} (hcl : TableClosed tbl) {M M' : ETm}
    (h : ConvMod (EStep tbl) LvlEq M M') (c k : Nat) :
    ConvMod (EStep tbl) LvlEq (M.lift c k) (M'.lift c k) := by
  induction h generalizing c with
  | refl => exact .refl _
  | fwd hs => exact .fwd (eStep_lift hcl hs c k)
  | bwd hs => exact .bwd (eStep_lift hcl hs c k)
  | eqv hs => exact .eqv (hs.lift' c k)
  | trans _ _ ih1 ih2 => exact .trans (ih1 c) (ih2 c)

/-- `σ` preserves `eqN`, so it preserves `eqNList`. The `σ` of an erasure is `id` or a
    tower of `instLevel`, both of which do (`eqN_instLevel`). -/
theorem eqNList_map_congr {σ : Level → Level}
    (hσ : ∀ {l l' : Level}, eqN l l' → eqN (σ l) (σ l')) {ls ls' : List Level}
    (h : eqNList ls ls') : eqNList (ls.map σ) (ls'.map σ) := by
  induction ls generalizing ls' with
  | nil =>
      cases ls' with
      | nil => exact h
      | cons _ _ => nomatch h
  | cons l ls ih =>
      cases ls' with
      | nil => nomatch h
      | cons l' ls' =>
          dsimp only [eqNList, List.map] at h ⊢
          exact ⟨hσ h.1, ih h.2⟩

/-! ## §2 the statement -/

/-- Erasure soundness at one pending level map and one erased context. -/
def ES (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (h : CvP E n Γ a b T) : Prop :=
  ConvMod (EStep tbl) LvlEq (h.dl.eps σ ρ) (h.dr.eps σ ρ)

/-- A transport node. The rule nodes are what the mutual induction owes. -/
def CvP.isTransport {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} :
    CvP E n Γ a b T → Bool
  | .wk .. => true
  | .esub .. => true
  | .linst .. => true
  | .ewk .. => true
  | .cctx .. => true
  | .refl .. => false
  | .symm .. => false
  | .trans .. => false
  | .beta .. => false
  | .zeta .. => false
  | .zetaLocal .. => false
  | .delta .. => false
  | .iota .. => false
  | .lit .. => false
  | .app .. => false
  | .lam .. => false
  | .pi .. => false
  | .letE .. => false
  | .sorts .. => false
  | .consts .. => false
  | .eta .. => false
  | .irr .. => false
  | .tyConv .. => false
  | .fsub .. => false

/-! ## §3 one transport -/

theorem es_cctx {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T A A' : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E n (.assumption A :: Γ) a b T) (hA : CvP E n Γ A A' (.sort u))
    (ih : ES tbl σ ρ h) :
    ES tbl σ ρ (CvP.cctx E n Γ a b T A A' u h hA) := by
  simpa [ES, CvP.dl, CvP.dr] using ih

theorem es_ewk {tbl : List CRule} {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {hext : EnvExt E₀ E} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E₀ n Γ a b T) (ih : ES tbl σ ρ h) :
    ES tbl σ ρ (CvP.ewk E₀ E n Γ a b T hext h) := by
  simpa [ES, CvP.dl, CvP.dr] using ih

theorem es_linst {tbl : List CRule} {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {ls : List Level} {hls : levelsBounded n ls = true}
    {hlen : ls.length = a'} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E a' Γ a b T)
    (ih : ES tbl (fun l => σ (instLevel ls l)) ρ h) :
    ES tbl σ ρ (CvP.linst E a' n Γ a b T ls hls hlen h) := by
  simpa [ES, CvP.dl, CvP.dr] using ih

theorem es_esub_drop {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T t v : Expr Nat} {j : Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E n Γ a b T) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hu : levelIsZero (σ u) = true)
    (ih : ES tbl σ (insertDisp .drop j ρ) h) :
    ES tbl σ ρ (CvP.esub E n Γ a b T t v j u h hget hv hvT) := by
  simpa [ES, CvP.dl, CvP.dr, eps_esub_drop (D := h.dl) hu, eps_esub_drop (D := h.dr) hu]
    using ih

theorem es_esub_keep {tbl : List CRule} (hcl : TableClosed tbl) {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {a b T t v : Expr Nat} {j : Nat} {u : Level}
    {σ : Level → Level} {ρ : List Disp} (h : CvP E n Γ a b T)
    (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (hu : levelIsZero (σ u) = false)
    (ih : ES tbl σ (insertDisp .keep j ρ) h) :
    ES tbl σ ρ (CvP.esub E n Γ a b T t v j u h hget hv hvT) := by
  have ih' : ConvMod (EStep tbl) LvlEq
      (h.dl.eps σ (insertDisp .keep j ρ)) (h.dr.eps σ (insertDisp .keep j ρ)) := ih
  simpa [ES, CvP.dl, CvP.dr, eps_esub_keep (D := h.dl) hu, eps_esub_keep (D := h.dr) hu]
    using convMod_inst_body hcl ih' (countKeep (ρ.take j)) (hv.eps σ ρ)

theorem es_wk_not_keep {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} {d : LocalDecl} {c : Nat} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E n Γ a b T)
    (hk : ρ[c]? = none ∨ ρ[c]? = some .drop ∨ ∃ v, ρ[c]? = some (.inline v))
    (ih : ES tbl σ (removeAt ρ c) h) :
    ES tbl σ ρ (CvP.wk E n Γ a b T d c h) := by
  simpa [ES, CvP.dl, CvP.dr, eps_wk_not_keep (D := h.dl) hk, eps_wk_not_keep (D := h.dr) hk]
    using ih

theorem es_wk_keep {tbl : List CRule} (hcl : TableClosed tbl) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {a b T : Expr Nat} {d : LocalDecl} {c : Nat} {σ : Level → Level}
    {ρ : List Disp} (h : CvP E n Γ a b T) (hk : ρ[c]? = some .keep)
    (ih : ES tbl σ (removeAt ρ c) h) :
    ES tbl σ ρ (CvP.wk E n Γ a b T d c h) := by
  have ih' : ConvMod (EStep tbl) LvlEq
      (h.dl.eps σ (removeAt ρ c)) (h.dr.eps σ (removeAt ρ c)) := ih
  simpa [ES, CvP.dl, CvP.dr, eps_wk_keep (D := h.dl) hk, eps_wk_keep (D := h.dr) hk]
    using convMod_lift hcl ih' (countKeep (ρ.take c)) 1

/-- `ewk` adds no atoms and one to the weight, as `wk` and `linst` do. -/
theorem cvp_strip_ewk (Aw : Nat → Nat) {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (hext : EnvExt E₀ E) (h : CvP E₀ n Γ a b T) :
    Prod.Lex DMStep (fun x y : Nat => x < y) (h.atoms Aw, h.wt Aw)
      ((CvP.ewk E₀ E n Γ a b T hext h).atoms Aw,
        (CvP.ewk E₀ E n Γ a b T hext h).wt Aw) := by
  have e1 : (CvP.ewk E₀ E n Γ a b T hext h).atoms Aw = h.atoms Aw := by simp only [CvP.atoms]
  have e2 : (CvP.ewk E₀ E n Γ a b T hext h).wt Aw = 1 + h.wt Aw := by simp only [CvP.wt]
  rw [e1, e2]
  exact Prod.Lex.right _ (by omega)

/-! ## §4 the transport prefix is structural -/

/-- `ES` of any derivation follows from `ES` of its rule nodes, at the `(σ, ρ)` the
    transports compute. No measure: each transport is a subderivation. -/
theorem es_transports (tbl : List CRule) (hcl : TableClosed tbl)
    (k : ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      (h : CvP E n Γ a b T), h.isTransport = false →
        ∀ (σ : Level → Level) (ρ : List Disp), ES tbl σ ρ h) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
      (h : CvP E n Γ a b T) → (σ : Level → Level) → (ρ : List Disp) →
        ES tbl σ ρ h
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ c h, σ, ρ =>
      match hρ : ρ[c]? with
      | none => es_wk_not_keep h (Or.inl hρ) (es_transports tbl hcl k h σ (removeAt ρ c))
      | some .keep =>
          es_wk_keep hcl h hρ (es_transports tbl hcl k h σ (removeAt ρ c))
      | some .drop =>
          es_wk_not_keep h (Or.inr (Or.inl hρ)) (es_transports tbl hcl k h σ (removeAt ρ c))
      | some (.inline v) =>
          es_wk_not_keep h (Or.inr (Or.inr ⟨v, hρ⟩))
            (es_transports tbl hcl k h σ (removeAt ρ c))
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ j u h hget hv hvT, σ, ρ =>
      match hu : levelIsZero (σ u) with
      | true => es_esub_drop h hget hv hvT hu
          (es_transports tbl hcl k h σ (insertDisp .drop j ρ))
      | false => es_esub_keep hcl h hget hv hvT hu
          (es_transports tbl hcl k h σ (insertDisp .keep j ρ))
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ ls _ _ h, σ, ρ =>
      es_linst h (es_transports tbl hcl k h (fun l => σ (instLevel ls l)) ρ)
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h, σ, ρ =>
      es_ewk h (es_transports tbl hcl k h σ ρ)
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h hA, σ, ρ =>
      es_cctx h hA (es_transports tbl hcl k h σ ρ)
  | _, _, _, _, _, _, .refl E n Γ a A ht dl dr, σ, ρ =>
      k (CvP.refl E n Γ a A ht dl dr) rfl σ ρ
  | _, _, _, _, _, _, .symm E n Γ a b A h dl dr, σ, ρ =>
      k (CvP.symm E n Γ a b A h dl dr) rfl σ ρ
  | _, _, _, _, _, _, .trans E n Γ a b c A h1 h2 dl dr, σ, ρ =>
      k (CvP.trans E n Γ a b c A h1 h2 dl dr) rfl σ ρ
  | _, _, _, _, _, _, .beta E n Γ A body arg B u hA hbody harg dl dr, σ, ρ =>
      k (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) rfl σ ρ
  | _, _, _, _, _, _, .zeta E n Γ A value body B u hA hv hb dl dr, σ, ρ =>
      k (CvP.zeta E n Γ A value body B u hA hv hb dl dr) rfl σ ρ
  | _, _, _, _, _, _, .zetaLocal E n Γ i A v hval hty hv dl dr, σ, ρ =>
      k (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) rfl σ ρ
  | _, _, _, _, _, _, .delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr, σ, ρ =>
      k (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) rfl σ ρ
  | _, _, _, _, _, _, .iota E n Γ lhs rhs T h hlhs hrhs dl dr, σ, ρ =>
      k (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr) rfl σ ρ
  | _, _, _, _, _, _, .lit E n Γ t exp T h hexp dl dr, σ, ρ =>
      k (CvP.lit E n Γ t exp T h hexp dl dr) rfl σ ρ
  | _, _, _, _, _, _, .app E n Γ f g a b A B h1 h2 dl dr, σ, ρ =>
      k (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl σ ρ
  | _, _, _, _, _, _, .lam E n Γ A A' b b' B u hA hb dl dr, σ, ρ =>
      k (CvP.lam E n Γ A A' b b' B u hA hb dl dr) rfl σ ρ
  | _, _, _, _, _, _, .pi E n Γ A A' B B' u v hA hB dl dr, σ, ρ =>
      k (CvP.pi E n Γ A A' B B' u v hA hB dl dr) rfl σ ρ
  | _, _, _, _, _, _, .letE E n Γ A A' v v' b b' B u hA hv hb dl dr, σ, ρ =>
      k (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) rfl σ ρ
  | _, _, _, _, _, _, .sorts E n Γ l₁ l₂ h dl dr, σ, ρ =>
      k (CvP.sorts E n Γ l₁ l₂ h dl dr) rfl σ ρ
  | _, _, _, _, _, _, .consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr, σ, ρ =>
      k (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr) rfl σ ρ
  | _, _, _, _, _, _, .eta E n Γ f A B h dl dr, σ, ρ =>
      k (CvP.eta E n Γ f A B h dl dr) rfl σ ρ
  | _, _, _, _, _, _, .irr E n Γ P p q hP hp hq dl dr, σ, ρ =>
      k (CvP.irr E n Γ P p q hP hp hq dl dr) rfl σ ρ
  | _, _, _, _, _, _, .tyConv E n Γ a b A A' u h hA dl dr, σ, ρ =>
      k (CvP.tyConv E n Γ a b A A' u h hA dl dr) rfl σ ρ
  | _, _, _, _, _, _, .fsub E n Γ A B S a b u hB hA hab dl dr, σ, ρ =>
      k (CvP.fsub E n Γ A B S a b u hB hA hab dl dr) rfl σ ρ

/-! ## §5 rule nodes, given the coherence the mutual induction supplies -/

theorem es_refl {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a A : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (ht : TyP E n Γ a A) (dl dr : TyP E n Γ a A)
    (hcl : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.refl E n Γ a A ht dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using hcl

theorem es_symm {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b A : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E n Γ a b A) (dl : TyP E n Γ b A) (dr : TyP E n Γ a A)
    (ih : ES tbl σ ρ h)
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (h.dr.eps σ ρ))
    (hR : ConvMod (EStep tbl) LvlEq (h.dl.eps σ ρ) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.symm E n Γ a b A h dl dr) := by
  have ih' : ConvMod (EStep tbl) LvlEq (h.dl.eps σ ρ) (h.dr.eps σ ρ) := ih
  simpa [ES, CvP.dl, CvP.dr] using
    (hL.trans ((ConvMod.symm' LvlEq.symm' ih').trans hR))

theorem es_trans {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b c A : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (h1 : CvP E n Γ a b A) (h2 : CvP E n Γ b c A)
    (dl : TyP E n Γ a A) (dr : TyP E n Γ c A)
    (ih1 : ES tbl σ ρ h1) (ih2 : ES tbl σ ρ h2)
    (cL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (h1.dl.eps σ ρ))
    (cM : ConvMod (EStep tbl) LvlEq (h1.dr.eps σ ρ) (h2.dl.eps σ ρ))
    (cR : ConvMod (EStep tbl) LvlEq (h2.dr.eps σ ρ) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.trans E n Γ a b c A h1 h2 dl dr) := by
  have ih1' : ConvMod (EStep tbl) LvlEq (h1.dl.eps σ ρ) (h1.dr.eps σ ρ) := ih1
  have ih2' : ConvMod (EStep tbl) LvlEq (h2.dl.eps σ ρ) (h2.dr.eps σ ρ) := ih2
  simpa [ES, CvP.dl, CvP.dr] using
    (cL.trans (ih1'.trans (cM.trans (ih2'.trans cR))))

theorem es_tyConv {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b A A' : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (h : CvP E n Γ a b A) (hA : CvP E n Γ A A' (.sort u))
    (dl : TyP E n Γ a A') (dr : TyP E n Γ b A')
    (ih : ES tbl σ ρ h)
    (cL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (h.dl.eps σ ρ))
    (cR : ConvMod (EStep tbl) LvlEq (h.dr.eps σ ρ) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.tyConv E n Γ a b A A' u h hA dl dr) := by
  have ih' : ConvMod (EStep tbl) LvlEq (h.dl.eps σ ρ) (h.dr.eps σ ρ) := ih
  simpa [ES, CvP.dl, CvP.dr] using (cL.trans (ih'.trans cR))

theorem es_irr_star {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {P p q : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (hP : TyP E n Γ P (.sort .zero)) (hp : TyP E n Γ p P) (hq : TyP E n Γ q P)
    (dl : TyP E n Γ p P) (dr : TyP E n Γ q P)
    (hl : dl.eps σ ρ = .star) (hr : dr.eps σ ρ = .star) :
    ES tbl σ ρ (CvP.irr E n Γ P p q hP hp hq dl dr) := by
  simp only [ES, CvP.dl, CvP.dr, hl, hr]
  exact .refl _

theorem es_sorts {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {l₁ l₂ : Level} {σ : Level → Level} {ρ : List Disp}
    (hσ : ∀ {l l' : Level}, eqN l l' → eqN (σ l) (σ l'))
    (h : eqN l₁ l₂) (dl : TyP E n Γ (.sort l₁) (.sort (.succ l₁)))
    (dr : TyP E n Γ (.sort l₂) (.sort (.succ l₁)))
    (hL : LvlEq (dl.eps σ ρ) (.sort (σ l₁)))
    (hR : LvlEq (.sort (σ l₂)) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.sorts E n Γ l₁ l₂ h dl dr) := by
  have hmid : LvlEq (.sort (σ l₁)) (.sort (σ l₂)) := .sort (hσ h)
  simpa [ES, CvP.dl, CvP.dr] using
    ((ConvMod.eqv hL).trans ((ConvMod.eqv hmid).trans (ConvMod.eqv hR)))

theorem es_consts {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember} {σ : Level → Level} {ρ : List Disp}
    (hσ : ∀ {l l' : Level}, eqN l l' → eqN (σ l) (σ l'))
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (h : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (hL : LvlEq (dl.eps σ ρ) (.const r (ls.map σ)))
    (hR : LvlEq (.const r (ls'.map σ)) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr) := by
  have hmid : LvlEq (.const r (ls.map σ)) (.const r (ls'.map σ)) :=
    .const r (eqNList_map_congr hσ h)
  simpa [ES, CvP.dl, CvP.dr] using
    ((ConvMod.eqv hL).trans ((ConvMod.eqv hmid).trans (ConvMod.eqv hR)))

theorem es_consts_star {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {m : CheckedMember} {σ : Level → Level} {ρ : List Disp}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
    (h : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype))
    (hL : dl.eps σ ρ = .star) (hR : dr.eps σ ρ = .star) :
    ES tbl σ ρ (CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr) := by
  simp only [ES, CvP.dl, CvP.dr, hL, hR]
  exact .refl _

theorem es_beta_drop {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (hbody.eps σ (.drop :: ρ)))
    (hR : ConvMod (EStep tbl) LvlEq (hbody.eps σ (.drop :: ρ)) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans hR)

theorem es_beta_rel {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B))
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (.app (.lam (hbody.eps σ (.keep :: ρ))) (harg.eps σ ρ)))
    (hR : ConvMod (EStep tbl) LvlEq
      (ETm.inst 0 (harg.eps σ ρ) (hbody.eps σ (.keep :: ρ))) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.beta E n Γ A body arg B u hA hbody harg dl dr) := by
  have step : ConvMod (EStep tbl) LvlEq
      (.app (.lam (hbody.eps σ (.keep :: ρ))) (harg.eps σ ρ))
      (ETm.inst 0 (harg.eps σ ρ) (hbody.eps σ (.keep :: ρ))) :=
    .fwd (.inl (.beta _ _))
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans (step.trans hR))

theorem es_eta {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {σ : Level → Level} {ρ : List Disp} {F : ETm}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (.lam (.app (F.lift 0 1) (.bvar 0))))
    (hR : ConvMod (EStep tbl) LvlEq F (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.eta E n Γ f A B h dl dr) := by
  have step : ConvMod (EStep tbl) LvlEq
      (.lam (.app (F.lift 0 1) (.bvar 0))) F :=
    .fwd (.inr (.eta F))
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans (step.trans hR))

theorem es_lit {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t : Nat} {exp T : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (h : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T)
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (hexp.eps σ ρ))
    (hR : ConvMod (EStep tbl) LvlEq (hexp.eps σ ρ) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.lit E n Γ t exp T h hexp dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans hR)

theorem es_fsub_drop {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S a b : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (hB : TyP E n (.assumption A :: Γ) B S) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a S))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a S))
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (hB.eps σ (.drop :: ρ)))
    (hR : ConvMod (EStep tbl) LvlEq (hB.eps σ (.drop :: ρ)) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.fsub E n Γ A B S a b u hB hA hab dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans hR)

theorem es_app {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    {ef eg ea eb : ETm}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (hf : ConvMod (EStep tbl) LvlEq ef eg) (ha : ConvMod (EStep tbl) LvlEq ea eb)
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (.app ef ea))
    (hR : ConvMod (EStep tbl) LvlEq (.app eg eb) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.app E n Γ f g a b A B h1 h2 dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans ((convMod_app hf ha).trans hR))

/-- An application whose argument (or whose function) erases to `★` deletes that
    argument. Both sides are then the function's erasure. -/
theorem es_app_star {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat} {σ : Level → Level} {ρ : List Disp} {ef eg : ETm}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (hf : ConvMod (EStep tbl) LvlEq ef eg)
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) ef)
    (hR : ConvMod (EStep tbl) LvlEq eg (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.app E n Γ f g a b A B h1 h2 dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans (hf.trans hR))

theorem es_lam_drop {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp} {eB eB' : ETm}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (hB : ConvMod (EStep tbl) LvlEq eB eB')
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) eB)
    (hR : ConvMod (EStep tbl) LvlEq eB' (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.lam E n Γ A A' b b' B u hA hb dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans (hB.trans hR))

theorem es_lam_keep {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp} {eB eB' : ETm}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (hB : ConvMod (EStep tbl) LvlEq eB eB')
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (.lam eB))
    (hR : ConvMod (EStep tbl) LvlEq (.lam eB') (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.lam E n Γ A A' b b' B u hA hb dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans ((convMod_lam hB).trans hR))

theorem es_lam_star {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))
    (hL : dl.eps σ ρ = .star) (hR : dr.eps σ ρ = .star) :
    ES tbl σ ρ (CvP.lam E n Γ A A' b b' B u hA hb dl dr) := by
  simp only [ES, CvP.dl, CvP.dr, hL, hR]
  exact .refl _

theorem es_pi {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level} {σ : Level → Level} {ρ : List Disp}
    {eA eA' eB eB' : ETm}
    (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (hAd : ConvMod (EStep tbl) LvlEq eA eA') (hBd : ConvMod (EStep tbl) LvlEq eB eB')
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (.pi eA eB))
    (hR : ConvMod (EStep tbl) LvlEq (.pi eA' eB') (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.pi E n Γ A A' B B' u v hA hB dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans ((convMod_pi hAd hBd).trans hR))

theorem es_letE {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp}
    {eB eB' : ETm}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (hB : ConvMod (EStep tbl) LvlEq eB eB')
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) eB)
    (hR : ConvMod (EStep tbl) LvlEq eB' (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans (hB.trans hR))

theorem es_zeta {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level} {σ : Level → Level} {ρ : List Disp} {mid : ETm}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) mid)
    (hR : ConvMod (EStep tbl) LvlEq mid (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.zeta E n Γ A value body B u hA hv hb dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans hR)

theorem es_zetaLocal {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A v : Expr Nat} {σ : Level → Level} {ρ : List Disp}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.zetaLocal E n Γ i A v hval hty hv dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using hL

/-- One erased root step between the two endpoints' erasures. δ and ι both land here:
    the root is a constant rule of `tbl`, and the two `ConvMod`s are coherence against
    the constant and against the rule's right-hand side. -/
theorem es_delta {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    {σ : Level → Level} {ρ : List Disp} {lhs rhs : ETm}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) lhs)
    (hstep : EStep tbl lhs rhs)
    (hR : ConvMod (EStep tbl) LvlEq rhs (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans ((ConvMod.fwd hstep).trans hR))

theorem es_iota {tbl : List CRule} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {lhs rhs T : Expr Nat} {σ : Level → Level} {ρ : List Disp} {el er : ETm}
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) el)
    (hstep : EStep tbl el er)
    (hR : ConvMod (EStep tbl) LvlEq er (dr.eps σ ρ)) :
    ES tbl σ ρ (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using (hL.trans ((ConvMod.fwd hstep).trans hR))

theorem es_fsub_keep {tbl : List CRule} (hcl : TableClosed tbl) {E : ResolvedEnv}
    {n : Nat} {Γ : LCtx} {A B S a b : Expr Nat} {u : Level}
    {σ : Level → Level} {ρ : List Disp} {ea eb : ETm}
    (hB : TyP E n (.assumption A :: Γ) B S) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a S))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a S))
    (hL : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (ETm.inst 0 ea (hB.eps σ (.keep :: ρ))))
    (hR : ConvMod (EStep tbl) LvlEq
      (ETm.inst 0 eb (hB.eps σ (.keep :: ρ))) (dr.eps σ ρ))
    (hv : ConvMod (EStep tbl) LvlEq ea eb) :
    ES tbl σ ρ (CvP.fsub E n Γ A B S a b u hB hA hab dl dr) := by
  simpa [ES, CvP.dl, CvP.dr] using
    (hL.trans ((convMod_inst_repl hcl hv (hB.eps σ (.keep :: ρ)) 0).trans hR))

end Rcic.Syn

#print axioms Rcic.Syn.convMod_lift
#print axioms Rcic.Syn.eqNList_map_congr
#print axioms Rcic.Syn.es_cctx
#print axioms Rcic.Syn.es_ewk
#print axioms Rcic.Syn.es_linst
#print axioms Rcic.Syn.es_esub_drop
#print axioms Rcic.Syn.es_esub_keep
#print axioms Rcic.Syn.es_wk_not_keep
#print axioms Rcic.Syn.es_wk_keep
#print axioms Rcic.Syn.cvp_strip_ewk
#print axioms Rcic.Syn.es_transports
#print axioms Rcic.Syn.es_refl
#print axioms Rcic.Syn.es_symm
#print axioms Rcic.Syn.es_trans
#print axioms Rcic.Syn.es_tyConv
#print axioms Rcic.Syn.es_irr_star
#print axioms Rcic.Syn.es_sorts
#print axioms Rcic.Syn.es_consts
#print axioms Rcic.Syn.es_consts_star
#print axioms Rcic.Syn.es_beta_drop
#print axioms Rcic.Syn.es_beta_rel
#print axioms Rcic.Syn.es_eta
#print axioms Rcic.Syn.es_lit
#print axioms Rcic.Syn.es_fsub_drop
#print axioms Rcic.Syn.es_fsub_keep
#print axioms Rcic.Syn.es_app
#print axioms Rcic.Syn.es_app_star
#print axioms Rcic.Syn.es_lam_drop
#print axioms Rcic.Syn.es_lam_keep
#print axioms Rcic.Syn.es_lam_star
#print axioms Rcic.Syn.es_pi
#print axioms Rcic.Syn.es_letE
#print axioms Rcic.Syn.es_zeta
#print axioms Rcic.Syn.es_zetaLocal
#print axioms Rcic.Syn.es_delta
#print axioms Rcic.Syn.es_iota
