import rcic.RcicSynSortRow
import rcic.RcicSynWalkLet

/-!
# Syntactic sortRow, build step 4b — Plain-to-`⁺` Enrichment (O6) and Q7 Totality

`research/rcic/semantic/S3_ES_ARMS.md` §51 and `S1_ORDER_ENRICHED_LEVELS.md` §4.4.
Closes Obligation 2 of cc's 05:25Z ruling (`issuecomment-6161495965` on PR #6938) and the
plain-to-`⁺` enrichment link (`O6`) for Step 4 (`sortRow`):

1. **§1 Unconditional `IotaPack E` (`iotaPack_of_envWfT`) and `AssumpPref`-preserving `PiGen`
   (`cctxAtOne`, `piInvP`, `assumpPref_piInvP`)**:
   - `iotaPack_of_envWfT` packages `iotaLift`, `iotaSubst`, and `derivedIota_instLevels`
     from `EnvWfT E`, discharging `IotaPack E` for `tyCctxAt_of_envWfT` and `piInv_of_envWfT`.
   - `cctxAtOne` converts the assumption at index `1` in `.assumption A :: .assumption Dom :: Γ`
     in 3 primitive steps (`wk` at cutoff `2`, `bvar 0` + `conv` + `wkAtZero`, `esub` at cutoff `1`),
     requiring neither `IotaPack E` nor `EnvWfT E` and preserving `AssumpPref`.
   - `piInvP` uses `cctxAtOne` in the `.cctx` case to invert any `TyP E n Γ (.pi A B) T` into
     `PiGen E n Γ A B` with zero `EnvWfT E` / `IotaPack E` hypotheses and full `AssumpPref`
     preservation (`assumpPref_piInvP`).

2. **§2 Enriched context lookup (`ctxP_lookupType_sort`, `ctxP_lookupValue_ty`) and closed member
   instantiation (`MemberSortP`, `instMemberSortP`)**:
   - Weakens `CtxP E n Γ` entries across arbitrary context prefixes (handling both `.assumption`
     via `wkAtZero` and `.letBinding` via `wkLetAtZero`), preserving `AssumpPref`.
   - Instantiates closed member sort derivations (`TyP E m.arity [] m.mtype (.sort u)`) at
     arbitrary contexts `Γ` and level lists `ls` via `TyP.linst` in `[]` and `wkClosed`,
     preserving `AssumpPref`.

3. **§3 Endpoint constructors for `CvP` (`betaLeftP`, `appRightP`, `lamRightP`, `piRightP`,
   `sortsRightP`, `constsRightP`, `etaLeftP`, `cvP_inst0_sortCongrLet`, `letRightP`, `cvpLetInline0`)**:
   - Constructs the explicit left/right endpoint typing witnesses required by `CvP` from
     enriched premises, each accompanied by its `AssumpPref` preservation theorem.

4. **§4 Plain-to-`⁺` enrichment (`enrichHasTyT`, `enrichConvT`, `enrichTyConvT`, `enrichCtxWfT`,
   `enrichGroupMembersT`, `enrichEnvWfT`), Q7 totality (`assumpPref_enrichHasTyT`,
   `assumpPref_enrichConvT`), and plain `sortRow` bridges (`sortRow_of_tyConvT_esChain_id`,
   `sortRow_of_convT_es_cl_id`)**:
   - Mutually translates plain derivations `HasTyT E₁ n Γ e T` and `ConvT E₁ n Γ a b T`
     into `TyP E n Γ e T` and `CvP E n Γ a b T`, and `TyConvT E₁ n Γ A B` into `TyCvP E n Γ A B`.
   - Proves as Lean theorems (`assumpPref_enrichHasTyT`, `assumpPref_enrichConvT`) that every
     enriched derivation satisfies `AssumpPref` (every `.wk`, `.esub`, and `.lsub` in the
     translated derivation tree satisfies `AssumptionPrefix`).

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 Unconditional `IotaPack E` and `AssumpPref`-Preserving `PiGen` (`cctxAtOne`, `piInvP`) -/

/-- Any well-formed environment `EnvWfT E` unconditionally induces an `IotaPack E`. -/
def iotaPack_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) : IotaPack E :=
  ⟨iotaLift E, iotaSubst E, fun ls _ _ h => derivedIota_instLevels (iotaLevelsT_of_envWfT hW) h ls⟩

/-- Context conversion at arbitrary depth `k` discharged from `EnvWfT E`. -/
noncomputable def tyCctxAt_of_envWfT {Ei E : ResolvedEnv} (hW : EnvWfT E) (hext : EnvExt Ei E)
    {n : Nat} {Γ : LCtx} {k : Nat} {Dom Dom' : Expr Nat} {uSlot : Level} {e T : Expr Nat}
    (hget : Γ.get? k = some (.assumption Dom))
    (hslot : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort uSlot))
    (D : TyP Ei n Γ e T) :
    TyP E n (setAssump k Dom' Γ) e T :=
  tyCctxAt (cvWalkHyp_of_envWfT hW) (iotaPack_of_cvWalkHyp (cvWalkHyp_of_envWfT hW))
    (fun hext' h => derivedIotaExt hext' h) hext hget hslot D

/-- Π-inversion (`PiGen`) discharged from `EnvWfT E`. -/
noncomputable def piInv_of_envWfT {Ei E : ResolvedEnv} (hW : EnvWfT E) (hext : EnvExt Ei E)
    {n : Nat} {Γ : LCtx} {e T : Expr Nat} (D : TyP Ei n Γ e T) {A B : Expr Nat}
    (he : e = .pi A B) : PiGen E n Γ A B :=
  piInv (cvWalkHyp_of_envWfT hW) (iotaPack_of_cvWalkHyp (cvWalkHyp_of_envWfT hW))
    (fun hext' h => derivedIotaExt hext' h) hext D he

/-- Specialization of `piInv_of_envWfT` to `Ei = E` and `e = .pi A B`. -/
noncomputable def piInv_here_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx} {A B T : Expr Nat}
    (D : TyP E n Γ (.pi A B) T) : PiGen E n Γ A B :=
  piInv_of_envWfT hW (envExt_refl E) D rfl

/-- Weaken a conversion `h : CvP E n Γ a b T` into `.assumption A :: Γ` at cutoff `0`. -/
def cvWkAtZero {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T A : Expr Nat}
    (h : CvP E n Γ a b T) :
    CvP E n (.assumption A :: Γ) (lift 0 1 a) (lift 0 1 b) (lift 0 1 T) :=
  cvCastCtx (insertAt_zero (.assumption A) Γ)
    (CvP.wk E n Γ a b T (.assumption A) 0 h)

theorem assumpPref_cvWkAtZero {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T A : Expr Nat} {h : CvP E n Γ a b T} (hh : h.AssumpPref) :
    (cvWkAtZero (A := A) h).AssumpPref :=
  assumpPref_cvCastCtx _ ⟨assumptionPrefix_zero Γ, hh⟩

theorem assumptionPrefix_two_assumptions (A B : Expr Nat) (Γ : LCtx) :
    AssumptionPrefix (.assumption A :: .assumption B :: Γ) 2 :=
  assumptionPrefix_succ_assumption A (.assumption B :: Γ) 1
    (assumptionPrefix_succ_assumption B Γ 0 (assumptionPrefix_zero Γ))

/-- Direct 3-step conversion of the assumption at index `1` in
    `.assumption A :: .assumption Dom :: Γtail` to `.assumption A :: .assumption Dom' :: Γtail`,
    using only `wk` at cutoff `2` (or `0`) and `esub` at cutoff `1`.
    Requires neither `IotaPack E` nor `EnvWfT E`, and preserves `AssumpPref`. -/
def cctxAtOne {E : ResolvedEnv} {n : Nat} {Γtail : LCtx} {A Dom Dom' B S : Expr Nat} {uDom : Level}
    (D : TyP E n (.assumption A :: .assumption Dom :: Γtail) B S)
    (hDom : CvP E n Γtail Dom Dom' (.sort uDom)) :
    TyP E n (.assumption A :: .assumption Dom' :: Γtail) B S :=
  let D₁ := TyP.wk E n (.assumption A :: .assumption Dom :: Γtail) B S (.assumption Dom') 2 D
  let hDom_symm := CvP.symm E n Γtail Dom Dom' (.sort uDom) hDom hDom.dr hDom.dl
  let hb0_raw := TyP.bvar E n (.assumption Dom' :: Γtail) 0 (lift 0 1 Dom') uDom
    (lookup_assumption_zero Dom' Γtail) (wkAtZero (A := Dom') hDom.dr)
  let hb0 := TyP.conv E n (.assumption Dom' :: Γtail) (.bvar 0)
    (lift 0 1 Dom') (lift 0 1 Dom) uDom hb0_raw (cvWkAtZero (A := Dom') hDom_symm)
  let hv : TyP E n (.assumption A :: .assumption Dom' :: Γtail)
      (lift 0 1 (.bvar 0)) (lift 0 1 (lift 0 1 Dom)) :=
    wkAtZero (A := A) hb0
  let hvT : TyP E n (.assumption A :: .assumption Dom' :: Γtail)
      (lift 0 1 (lift 0 1 Dom)) (.sort uDom) :=
    wkAtZero (A := A) (wkAtZero (A := Dom') hDom.dl)
  have hG : substRemove (.bvar 0) 1
      (.assumption (lift 1 1 A) :: .assumption (lift 0 1 Dom) :: .assumption Dom' :: Γtail) =
      .assumption A :: .assumption Dom' :: Γtail := by
    show LocalDecl.assumption (instantiate 0 (.bvar 0) (lift 1 1 A)) :: .assumption Dom' :: Γtail =
      .assumption A :: .assumption Dom' :: Γtail
    rw [instantiate_bvar_lift_id 0 A]
  let Desub := TyP.esub E n
    (.assumption (lift 1 1 A) :: .assumption (lift 0 1 Dom) :: .assumption Dom' :: Γtail)
    (lift 2 1 B) (lift 2 1 S) (lift 0 1 Dom) (.bvar 0) 1 uDom D₁ rfl
    (tyCastCtx hG.symm hv) (tyCastCtx hG.symm hvT)
  tyCastCtx hG (tyCast (instantiate_bvar_lift_id 1 B) (instantiate_bvar_lift_id 1 S) Desub)

/-- `cctxAtOne` preserves `TyP.AssumpPref`. -/
theorem assumpPref_cctxAtOne {E : ResolvedEnv} {n : Nat} {Γtail : LCtx}
    {A Dom Dom' B S : Expr Nat} {uDom : Level}
    {D : TyP E n (.assumption A :: .assumption Dom :: Γtail) B S}
    {hDom : CvP E n Γtail Dom Dom' (.sort uDom)}
    (hD : D.AssumpPref) (hC : hDom.AssumpPref) :
    (cctxAtOne D hDom).AssumpPref := by
  unfold cctxAtOne
  refine assumpPref_tyCastCtx _ (assumpPref_tyCast _ _ ⟨?_, ?_, ?_, ?_⟩)
  · exact assumptionPrefix_succ_assumption (lift 1 1 A) _ 0 (assumptionPrefix_zero _)
  · exact ⟨assumptionPrefix_two_assumptions A Dom Γtail, hD⟩
  · refine assumpPref_tyCastCtx _ (assumpPref_wkAtZero ⟨assumpPref_wkAtZero (assumpPref_dr hC), ?_⟩)
    exact assumpPref_cvWkAtZero ⟨hC, assumpPref_dr hC, assumpPref_dl hC⟩
  · exact assumpPref_tyCastCtx _ (assumpPref_wkAtZero (assumpPref_wkAtZero (assumpPref_dl hC)))

/-- Context-conversion action on `PiGen` using `cctxAtOne` for `.assumption` at index `1`
    (no `IotaPack E` or `EnvWfT E` needed, and `AssumpPref`-preserving). -/
def piCctxP {E : ResolvedEnv} {n : Nat} {Γtail : LCtx} {A B Dom Dom' : Expr Nat} {uDom : Level}
    (R : PiGen E n (.assumption Dom :: Γtail) A B)
    (hDom : CvP E n Γtail Dom Dom' (.sort uDom)) :
    PiGen E n (.assumption Dom' :: Γtail) A B :=
  ⟨R.u, R.v,
    TyP.cctx E n Γtail A (.sort R.u) Dom Dom' uDom R.hA hDom,
    cctxAtOne R.hB hDom⟩

theorem assumpPref_piCctxP {E : ResolvedEnv} {n : Nat} {Γtail : LCtx}
    {A B Dom Dom' : Expr Nat} {uDom : Level}
    {R : PiGen E n (.assumption Dom :: Γtail) A B}
    {hDom : CvP E n Γtail Dom Dom' (.sort uDom)}
    (hRA : R.hA.AssumpPref) (hRB : R.hB.AssumpPref) (hC : hDom.AssumpPref) :
    (piCctxP R hDom).hA.AssumpPref ∧ (piCctxP R hDom).hB.AssumpPref :=
  ⟨⟨hRA, hC⟩, assumpPref_cctxAtOne hRB hC⟩

theorem assumpPref_piWk {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {A₀ B₀ : Expr Nat}
    (d : LocalDecl) (c : Nat) (R : PiGen E n Γ₀ A₀ B₀)
    {A B : Expr Nat} (hAe : lift c 1 A₀ = A) (hBe : lift (c + 1) 1 B₀ = B)
    (hc : AssumptionPrefix Γ₀ c)
    (hRA : R.hA.AssumpPref) (hRB : R.hB.AssumpPref) :
    (piWk d c R hAe hBe).hA.AssumpPref ∧ (piWk d c R hAe hBe).hB.AssumpPref := by
  dsimp [piWk]
  refine ⟨assumpPref_tyCast _ _ ⟨hc, hRA⟩, ?_⟩
  exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _
    ⟨assumptionPrefix_succ_assumption A₀ Γ₀ c hc, hRB⟩)

theorem assumpPref_piLinst {E : ResolvedEnv} {a n : Nat} {Γ₀ : LCtx} {A₀ B₀ : Expr Nat}
    (ls : List Level) (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (R : PiGen E a Γ₀ A₀ B₀) {A B : Expr Nat}
    (hAe : instantiateLevels ls A₀ = A) (hBe : instantiateLevels ls B₀ = B)
    (hRA : R.hA.AssumpPref) (hRB : R.hB.AssumpPref) :
    (piLinst ls hls hlen R hAe hBe).hA.AssumpPref ∧
      (piLinst ls hls hlen R hAe hBe).hB.AssumpPref := by
  dsimp [piLinst]
  refine ⟨assumpPref_tyCast _ _ hRA, ?_⟩
  exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _ hRB)

theorem assumpPref_piEsub {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {A₀ B₀ : Expr Nat}
    (t repl : Expr Nat) (j : Nat) (uE : Level)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    (R : PiGen E n Γ₀ A₀ B₀) {A B : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) B₀ = B)
    (hj : AssumptionPrefix Γ₀ j)
    (hRA : R.hA.AssumpPref) (hRB : R.hB.AssumpPref)
    (hvP : hv.AssumpPref) (hvTP : hvT.AssumpPref) :
    (piEsub t repl j uE hget hv hvT R hAe hBe).hA.AssumpPref ∧
      (piEsub t repl j uE hget hv hvT R hAe hBe).hB.AssumpPref := by
  dsimp [piEsub]
  refine ⟨assumpPref_tyCast _ _ ⟨hj, hRA, hvP, hvTP⟩, ?_⟩
  refine assumpPref_tyCastCtx _ (assumpPref_tyCast _ _ ⟨?_, hRB, ?_, ?_⟩)
  · exact assumptionPrefix_succ_assumption A₀ Γ₀ j hj
  · exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _
      ⟨assumptionPrefix_zero (substRemove repl j Γ₀), hvP⟩)
  · exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _
      ⟨assumptionPrefix_zero (substRemove repl j Γ₀), hvTP⟩)

theorem assumpPref_piLsub {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {A₀ B₀ : Expr Nat}
    (t repl : Expr Nat) (j : Nat) (uE : Level)
    (hget : Γ₀[j]? = some (.letBinding t repl))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    (R : PiGen E n Γ₀ A₀ B₀) {A B : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) B₀ = B)
    (hj : AssumptionPrefix Γ₀ j)
    (hRA : R.hA.AssumpPref) (hRB : R.hB.AssumpPref)
    (hvP : hv.AssumpPref) (hvTP : hvT.AssumpPref) :
    (piLsub t repl j uE hget hv hvT R hAe hBe).hA.AssumpPref ∧
      (piLsub t repl j uE hget hv hvT R hAe hBe).hB.AssumpPref := by
  dsimp [piLsub]
  refine ⟨assumpPref_tyCast _ _ ⟨hj, hRA, hvP, hvTP⟩, ?_⟩
  refine assumpPref_tyCastCtx _ (assumpPref_tyCast _ _ ⟨?_, hRB, ?_, ?_⟩)
  · exact assumptionPrefix_succ_assumption A₀ Γ₀ j hj
  · exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _
      ⟨assumptionPrefix_zero (substRemove repl j Γ₀), hvP⟩)
  · exact assumpPref_tyCastCtx _ (assumpPref_tyCast _ _
      ⟨assumptionPrefix_zero (substRemove repl j Γ₀), hvTP⟩)

/-- Unconditional, `AssumpPref`-preserving Π-inversion (`PiGen`) for `TyP Ei n Γ e T`
    when `e = .pi A B`. Uses `piCctxP` (`cctxAtOne`) in the `.cctx` case, so neither
    `IotaPack E` nor `EnvWfT E` is required. -/
def piInvP {Ei E : ResolvedEnv} (hext : EnvExt Ei E) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP Ei n Γ e T → {A B : Expr Nat} → e = .pi A B → PiGen E n Γ A B
  | _, _, _, _, .sort .., _, _, he => by cases he
  | _, _, _, _, .bvar .., _, _, he => by cases he
  | _, _, _, _, .const .., _, _, he => by cases he
  | n, Γ, _, _, .pi _ _ _ A₀ u B₀ v hA hB, _, _, he => by
      cases he
      exact PiGen.mk u v
        (TyP.ewk Ei E n Γ A₀ (.sort u) hext hA)
        (TyP.ewk Ei E n (.assumption A₀ :: Γ) B₀ (.sort v) hext hB)
  | _, _, _, _, .lam .., _, _, he => by cases he
  | _, _, _, _, .app .., _, _, he => by cases he
  | _, _, _, _, .letE .., _, _, he => by cases he
  | _, _, _, _, .lit .., _, _, he => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ h _, _, _, he =>
      piInvP hext h he
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, he =>
      match lift_eq_pi he with
      | .mk _ _ he₀ hAe hBe =>
          piWk d c (piInvP hext inner he₀) hAe hBe
  | n, _, _, _, .esub _ _ Γ₀ _ _ t repl j uE inner hget hv hvT, _, _, he =>
      match instantiate_eq_pi he with
      | .under _ _ he₀ hAe hBe =>
          piEsub t repl j uE hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT)
            (piInvP hext inner he₀) hAe hBe
      | .here _ hr =>
          piInvP hext hv hr
  | n, _, _, _, .lsub _ _ Γ₀ _ _ t repl j uE inner hget hv hvT, _, _, he =>
      match instantiate_eq_pi he with
      | .under _ _ he₀ hAe hBe =>
          piLsub t repl j uE hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT)
            (piInvP hext inner he₀) hAe hBe
      | .here _ hr =>
          piInvP hext hv hr
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, he =>
      match instantiateLevels_eq_pi he with
      | .mk _ _ he₀ hAe hBe =>
          piLinst ls hls hlen (piInvP hext inner he₀) hAe hBe
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' inner, _, _, he =>
      piInvP (envExt_trans hext' hext) inner he
  | _, _, _, _, .cctx _ _ Γtail _ _ Dom Dom' uDom inner hDom, _, _, he =>
      piCctxP
        (piInvP hext inner he)
        (CvP.ewk Ei E _ Γtail Dom Dom' (.sort uDom) hext hDom)

/-- Specialization of `piInvP` to `Ei = E` and `e = .pi A B`. -/
def piInvP_here {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B T : Expr Nat}
    (D : TyP E n Γ (.pi A B) T) : PiGen E n Γ A B :=
  piInvP (envExt_refl E) D rfl

/-- `piInvP` preserves `AssumpPref` on both `hA` and `hB`. -/
theorem assumpPref_piInvP {Ei E : ResolvedEnv} (hext : EnvExt Ei E) :
    ∀ {n : Nat} {Γ : LCtx} {e T : Expr Nat} (D : TyP Ei n Γ e T)
      {A B : Expr Nat} (he : e = .pi A B),
      D.AssumpPref →
      (piInvP hext D he).hA.AssumpPref ∧ (piInvP hext D he).hB.AssumpPref
  | _, _, _, _, .sort .., _, _, he, _ => by cases he
  | _, _, _, _, .bvar .., _, _, he, _ => by cases he
  | _, _, _, _, .const .., _, _, he, _ => by cases he
  | _, _, _, _, .pi .., _, _, he, hD => by
      cases he
      exact ⟨hD.1, hD.2⟩
  | _, _, _, _, .lam .., _, _, he, _ => by cases he
  | _, _, _, _, .app .., _, _, he, _ => by cases he
  | _, _, _, _, .letE .., _, _, he, _ => by cases he
  | _, _, _, _, .lit .., _, _, he, _ => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ h _, _, _, he, hD =>
      assumpPref_piInvP hext h he hD.1
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, he, hD => by
      dsimp only [piInvP]
      cases lift_eq_pi he with
      | mk A₀ B₀ he₀ hAe hBe =>
          have ih := assumpPref_piInvP hext inner he₀ hD.2
          exact assumpPref_piWk d c (piInvP hext inner he₀) hAe hBe hD.1 ih.1 ih.2
  | n, _, _, _, .esub _ _ Γ₀ _ _ t repl j uE inner hget hv hvT, _, _, he, hD => by
      dsimp only [piInvP]
      cases instantiate_eq_pi he with
      | under A₀ B₀ he₀ hAe hBe =>
          have ih := assumpPref_piInvP hext inner he₀ hD.2.1
          exact assumpPref_piEsub t repl j uE hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT)
            (piInvP hext inner he₀) hAe hBe hD.1 ih.1 ih.2 hD.2.2.1 hD.2.2.2
      | here _ hr =>
          exact assumpPref_piInvP hext hv hr hD.2.2.1
  | n, _, _, _, .lsub _ _ Γ₀ _ _ t repl j uE inner hget hv hvT, _, _, he, hD => by
      dsimp only [piInvP]
      cases instantiate_eq_pi he with
      | under A₀ B₀ he₀ hAe hBe =>
          have ih := assumpPref_piInvP hext inner he₀ hD.2.1
          exact assumpPref_piLsub t repl j uE hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT)
            (piInvP hext inner he₀) hAe hBe hD.1 ih.1 ih.2 hD.2.2.1 hD.2.2.2
      | here _ hr =>
          exact assumpPref_piInvP hext hv hr hD.2.2.1
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, he, hAi => by
      dsimp only [piInvP]
      cases instantiateLevels_eq_pi he with
      | mk A₀ B₀ he₀ hAe hBe =>
          have ih := assumpPref_piInvP hext inner he₀ hAi
          exact assumpPref_piLinst ls hls hlen (piInvP hext inner he₀) hAe hBe ih.1 ih.2
  | _, _, _, _, .ewk _ _ _ _ _ _ hext' inner, _, _, he, hAi =>
      assumpPref_piInvP (envExt_trans hext' hext) inner he hAi
  | _, _, _, _, .cctx _ _ _ _ _ _ _ _ inner _, _, _, he, hD =>
      let ih := assumpPref_piInvP hext inner he hD.1
      assumpPref_piCctxP ih.1 ih.2 hD.2

theorem assumpPref_piInvP_here {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B T : Expr Nat}
    {D : TyP E n Γ (.pi A B) T} (hD : D.AssumpPref) :
    (piInvP_here D).hA.AssumpPref ∧ (piInvP_here D).hB.AssumpPref :=
  assumpPref_piInvP (envExt_refl E) D rfl hD

/-! ## §2 Context Lookup (`ctxP_lookupType_sort`, `ctxP_lookupValue_ty`) and Member Instantiation -/

/-- Every derivation in `CtxP E n Γ` satisfies `AssumpPref`. -/
def CtxP.AssumpPref {E : ResolvedEnv} {n : Nat} : {Γ : LCtx} → CtxP E n Γ → Prop
  | _, .nil _ _ => True
  | _, .assumption _ _ _ _ _ hC hA => hC.AssumpPref ∧ hA.AssumpPref
  | _, .letBinding _ _ _ _ _ _ hC hA hv => hC.AssumpPref ∧ hA.AssumpPref ∧ hv.AssumpPref

inductive LookupTypeConsSucc (y : LocalDecl) (Δ : LCtx) (i : Nat) (A : Expr Nat) : Type where
  | mk (B : Expr Nat) (hlt : lookupType Δ i = some B) (hA : lift 0 1 B = A)

def lookupType_cons_succ_inv {y : LocalDecl} {Δ : LCtx} {i : Nat} {A : Expr Nat}
    (h : lookupType (y :: Δ) (i + 1) = some A) : LookupTypeConsSucc y Δ i A := by
  rw [lookupType_cons_succ] at h
  cases hlt : lookupType Δ i with
  | none => rw [hlt] at h; cases h
  | some B =>
      rw [hlt] at h
      exact ⟨B, hlt, Option.some.inj h⟩

inductive LookupValueConsSucc (y : LocalDecl) (Δ : LCtx) (i : Nat) (v : Expr Nat) : Type where
  | mk (v₀ : Expr Nat) (hlv : lookupValue Δ i = some v₀) (hv : lift 0 1 v₀ = v)

def lookupValue_cons_succ_inv {y : LocalDecl} {Δ : LCtx} {i : Nat} {v : Expr Nat}
    (h : lookupValue (y :: Δ) (i + 1) = some v) : LookupValueConsSucc y Δ i v := by
  rw [lookupValue_cons_succ] at h
  cases hlv : lookupValue Δ i with
  | none => rw [hlv] at h; cases h
  | some v₀ =>
      rw [hlv] at h
      exact ⟨v₀, hlv, Option.some.inj h⟩

theorem lookupType_cons_zero_assumption {A₀ : Expr Nat} {Δ : LCtx} {A : Expr Nat}
    (h : lookupType (.assumption A₀ :: Δ) 0 = some A) : lift 0 1 A₀ = A := by
  simpa [lookupType] using h

theorem lookupType_cons_zero_letBinding {A₀ v₀ : Expr Nat} {Δ : LCtx} {A : Expr Nat}
    (h : lookupType (.letBinding A₀ v₀ :: Δ) 0 = some A) : lift 0 1 A₀ = A := by
  simpa [lookupType] using h

theorem lookupValue_cons_zero_letBinding {A₀ v₀ : Expr Nat} {Δ : LCtx} {v : Expr Nat}
    (h : lookupValue (.letBinding A₀ v₀ :: Δ) 0 = some v) : lift 0 1 v₀ = v := by
  simpa [lookupValue] using h

/-- From `CtxP E n Γ` and `lookupType Γ i = some A`, construct `(u : Level) × TyP E n Γ A (.sort u)`.
    Uses `wkAtZero` for `.assumption` heads and `wkLetAtZero` for `.letBinding` heads. -/
def ctxP_lookupType_sort {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → CtxP E n Γ → {i : Nat} → {A : Expr Nat} →
    lookupType Γ i = some A → (u : Level) × TyP E n Γ A (.sort u)
  | _, .nil _ _, i, _, h => by
      cases i <;> simp [lookupType] at h
  | _, .assumption _ _ _ A₀ u₀ _ hA₀, 0, _, h =>
      ⟨u₀, tyCast (lookupType_cons_zero_assumption h) rfl (wkAtZero (A := A₀) hA₀)⟩
  | _, .assumption _ _ _ A₀ _ hC _, i + 1, _, h =>
      match lookupType_cons_succ_inv h with
      | .mk _ hlt hA_eq =>
          let ⟨u, hB_ty⟩ := ctxP_lookupType_sort hC hlt
          ⟨u, tyCast hA_eq rfl (wkAtZero (A := A₀) hB_ty)⟩
  | _, .letBinding _ _ _ A₀ u₀ v₀ _ hA₀ _, 0, _, h =>
      ⟨u₀, tyCast (lookupType_cons_zero_letBinding h) rfl (wkLetAtZero (A := A₀) (v := v₀) hA₀)⟩
  | _, .letBinding _ _ _ A₀ _ v₀ hC _ _, i + 1, _, h =>
      match lookupType_cons_succ_inv h with
      | .mk _ hlt hA_eq =>
          let ⟨u, hB_ty⟩ := ctxP_lookupType_sort hC hlt
          ⟨u, tyCast hA_eq rfl (wkLetAtZero (A := A₀) (v := v₀) hB_ty)⟩

/-- `ctxP_lookupType_sort` preserves `AssumpPref`. -/
theorem assumpPref_ctxP_lookupType_sort {E : ResolvedEnv} {n : Nat} :
    ∀ {Γ : LCtx} (C : CtxP E n Γ) {i : Nat} {A : Expr Nat}
      (h : lookupType Γ i = some A),
      C.AssumpPref → (ctxP_lookupType_sort C h).2.AssumpPref
  | _, .nil _ _, i, _, h, _ => by
      cases i <;> simp [lookupType] at h
  | _, .assumption _ _ _ _ _ _ _, 0, _, _, hAC =>
      assumpPref_tyCast _ rfl (assumpPref_wkAtZero hAC.2)
  | _, .assumption _ _ _ _ _ hC _, i + 1, _, h, hAC => by
      dsimp only [ctxP_lookupType_sort]
      cases lookupType_cons_succ_inv h with
      | mk _ hlt _ =>
          exact assumpPref_tyCast _ rfl
            (assumpPref_wkAtZero (assumpPref_ctxP_lookupType_sort hC hlt hAC.1))
  | _, .letBinding _ _ _ _ _ _ _ _ _, 0, _, _, hAC =>
      assumpPref_tyCast _ rfl (assumpPref_wkLetAtZero hAC.2.1)
  | _, .letBinding _ _ _ _ _ _ hC _ _, i + 1, _, h, hAC => by
      dsimp only [ctxP_lookupType_sort]
      cases lookupType_cons_succ_inv h with
      | mk _ hlt _ =>
          exact assumpPref_tyCast _ rfl
            (assumpPref_wkLetAtZero (assumpPref_ctxP_lookupType_sort hC hlt hAC.1))

/-- From `CtxP E n Γ`, `lookupValue Γ i = some v`, and `lookupType Γ i = some A`,
    construct `TyP E n Γ v A`. Uses `wkAtZero` and `wkLetAtZero`, preserving `AssumpPref`. -/
def ctxP_lookupValue_ty {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → CtxP E n Γ → {i : Nat} → {v A : Expr Nat} →
    lookupValue Γ i = some v → lookupType Γ i = some A → TyP E n Γ v A
  | _, .nil _ _, i, _, _, hv, _ => by
      cases i <;> simp [lookupValue] at hv
  | _, .assumption _ _ _ _ _ _ _, 0, _, _, hv, _ => by
      simp [lookupValue] at hv
  | _, .assumption _ _ _ A₀ _ hC _, i + 1, _, _, hv, hA =>
      match lookupValue_cons_succ_inv hv, lookupType_cons_succ_inv hA with
      | .mk _ hlv hv_eq, .mk _ hlt hA_eq =>
          tyCast hv_eq hA_eq (wkAtZero (A := A₀) (ctxP_lookupValue_ty hC hlv hlt))
  | _, .letBinding _ _ _ A₀ _ v₀ _ _ hv₀, 0, _, _, hv, hA =>
      tyCast (lookupValue_cons_zero_letBinding hv) (lookupType_cons_zero_letBinding hA)
        (wkLetAtZero (A := A₀) (v := v₀) hv₀)
  | _, .letBinding _ _ _ A₀ _ v₀ hC _ _, i + 1, _, _, hv, hA =>
      match lookupValue_cons_succ_inv hv, lookupType_cons_succ_inv hA with
      | .mk _ hlv hv_eq, .mk _ hlt hA_eq =>
          tyCast hv_eq hA_eq
            (wkLetAtZero (A := A₀) (v := v₀) (ctxP_lookupValue_ty hC hlv hlt))

/-- `ctxP_lookupValue_ty` preserves `AssumpPref`. -/
theorem assumpPref_ctxP_lookupValue_ty {E : ResolvedEnv} {n : Nat} :
    ∀ {Γ : LCtx} (C : CtxP E n Γ) {i : Nat} {v A : Expr Nat}
      (hv : lookupValue Γ i = some v) (hA : lookupType Γ i = some A),
      C.AssumpPref → (ctxP_lookupValue_ty C hv hA).AssumpPref
  | _, .nil _ _, i, _, _, hv, _, _ => by
      cases i <;> simp [lookupValue] at hv
  | _, .assumption _ _ _ _ _ _ _, 0, _, _, hv, _, _ => by
      simp [lookupValue] at hv
  | _, .assumption _ _ _ _ _ hC _, i + 1, _, _, hv, hA, hAC => by
      dsimp only [ctxP_lookupValue_ty]
      cases lookupValue_cons_succ_inv hv with
      | mk _ hlv _ =>
          cases lookupType_cons_succ_inv hA with
          | mk _ hlt _ =>
              exact assumpPref_tyCast _ _
                (assumpPref_wkAtZero (assumpPref_ctxP_lookupValue_ty hC hlv hlt hAC.1))
  | _, .letBinding _ _ _ _ _ _ _ _ _, 0, _, _, _, _, hAC =>
      assumpPref_tyCast _ _ (assumpPref_wkLetAtZero hAC.2.2)
  | _, .letBinding _ _ _ _ _ _ hC _ _, i + 1, _, _, hv, hA, hAC => by
      dsimp only [ctxP_lookupValue_ty]
      cases lookupValue_cons_succ_inv hv with
      | mk _ hlv _ =>
          cases lookupType_cons_succ_inv hA with
          | mk _ hlt _ =>
              exact assumpPref_tyCast _ _
                (assumpPref_wkLetAtZero (assumpPref_ctxP_lookupValue_ty hC hlv hlt hAC.1))

/-- Environment member sort witness in `TyP`: every resolved member `m` of `E` has an
    enriched sort derivation `TyP E m.arity [] m.mtype (.sort u)` in the empty context. -/
@[reducible] def MemberSortP (E : ResolvedEnv) : Type :=
  ∀ (r : Nat) (m : CheckedMember), E.members r = some m →
    (u : Level) × TyP E m.arity [] m.mtype (.sort u)

/-- Every member sort witness in `hm : MemberSortP E` satisfies `AssumpPref`. -/
def MemberSortP.AssumpPref {E : ResolvedEnv} (hm : MemberSortP E) : Prop :=
  ∀ r m hres, (hm r m hres).2.AssumpPref

/-- `EnvWfP E` immediately supplies `MemberSortP E` via `EnvWfP.typeAdm` and `TyP.ewk`. -/
def memberSortP_of_envWfP {E : ResolvedEnv} (hEP : EnvWfP E) : MemberSortP E :=
  fun _ m hres =>
    let adm := hEP.typeAdm hres
    ⟨adm.u, TyP.ewk adm.E₀ E m.arity [] m.mtype (.sort adm.u) adm.ext adm.hT⟩

/-- Instantiate a closed member sort witness `hm` at context `Γ` and level list `ls`,
    producing `(u : Level) × TyP E n Γ (instantiateLevels ls m.mtype) (.sort u)`.
    Applies `TyP.linst` in `[]` first, then `wkClosed` across `Γ`. -/
def instMemberSortP {E : ResolvedEnv} (hcl : EnvClosed E) (hm : MemberSortP E)
    {n : Nat} (Γ : LCtx) {r : Nat} {m : CheckedMember} {ls : List Level}
    (hres : E.members r = some m)
    (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) :
    (u : Level) × TyP E n Γ (instantiateLevels ls m.mtype) (.sort u) :=
  let ⟨u₀, hm_ty⟩ := hm r m hres
  have hcl_m : lift 0 1 m.mtype = m.mtype := (hcl r m hres).1 0
  have hcl_inst : lift 0 1 (instantiateLevels ls m.mtype) = instantiateLevels ls m.mtype := by
    rw [lift_instantiateLevels, hcl_m]
  let hm_linst : TyP E n [] (instantiateLevels ls m.mtype) (.sort (instLevel ls u₀)) :=
    TyP.linst E m.arity n [] m.mtype (.sort u₀) ls hwf hlen hm_ty
  ⟨instLevel ls u₀, wkClosed hcl_inst rfl Γ hm_linst⟩

/-- `instMemberSortP` preserves `AssumpPref`. -/
theorem assumpPref_instMemberSortP {E : ResolvedEnv} (hcl : EnvClosed E) (hm : MemberSortP E)
    (hAm : hm.AssumpPref) {n : Nat} (Γ : LCtx) {r : Nat} {m : CheckedMember} {ls : List Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true) :
    (instMemberSortP hcl hm Γ hres hlen hwf).2.AssumpPref :=
  assumpPref_wkClosed _ rfl Γ (hAm r m hres)

/-! ## §3 Endpoint Constructors for `CvP` and Their `AssumpPref` Preservation -/

/-- Left endpoint typing `(λ A, body) arg : instantiate0 arg B` for `CvP.beta`. -/
def betaLeftP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A body arg B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B)
    (harg : TyP E n Γ arg A) :
    TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B) :=
  let ⟨v, hB⟩ := hbody.reg
  let hlam := TyP.lam E n Γ A u body B v hA hbody hB
  TyP.app E n Γ (.lam A body) arg A B v hlam harg (instEnd hB harg hA)

theorem assumpPref_betaLeftP {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level}
    {hA : TyP E n Γ A (.sort u)}
    {hbody : TyP E n (.assumption A :: Γ) body B}
    {harg : TyP E n Γ arg A}
    (hAA : hA.AssumpPref) (hAbody : hbody.AssumpPref) (hAarg : harg.AssumpPref) :
    (betaLeftP hA hbody harg).AssumpPref :=
  ⟨⟨hAA, hAbody, assumpPref_reg hAbody⟩, hAarg,
    assumpPref_instEnd (assumpPref_reg hAbody) hAarg hAA⟩

/-- Right endpoint typing `g b : instantiate0 a B` for `CvP.app` from
    `h1 : CvP E n Γ f g (.pi A B)` and `h2 : CvP E n Γ a b A`.
    Uses `piInvP_here` (no `IotaPack E` or `EnvWfT E` needed). -/
def appRightP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g A B a b : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B))
    (h2 : CvP E n Γ a b A) :
    TyP E n Γ (.app g b) (instantiate0 a B) :=
  let P := piInvP_here h1.dl.reg.2
  let hBa := instEnd P.hB h2.dl P.hA
  let hBb := instEnd P.hB h2.dr P.hA
  let happ_gb := TyP.app E n Γ g b A B P.v h1.dr h2.dr hBb
  let hfsub := CvP.fsub E n Γ A B (.sort P.v) a b P.u P.hB P.hA h2 hBa hBb
  let hfsub_symm := CvP.symm E n Γ (instantiate0 a B) (instantiate0 b B) (.sort P.v) hfsub hBb hBa
  TyP.conv E n Γ (.app g b) (instantiate0 b B) (instantiate0 a B) P.v happ_gb hfsub_symm

theorem assumpPref_appRightP {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g A B a b : Expr Nat}
    {h1 : CvP E n Γ f g (.pi A B)}
    {h2 : CvP E n Γ a b A}
    (hA1 : h1.AssumpPref) (hA2 : h2.AssumpPref) :
    (appRightP h1 h2).AssumpPref := by
  have ⟨hPA, hPB⟩ := assumpPref_piInvP_here (assumpPref_reg (assumpPref_dl hA1))
  have hABa := assumpPref_instEnd hPB (assumpPref_dl hA2) hPA
  have hABb := assumpPref_instEnd hPB (assumpPref_dr hA2) hPA
  exact ⟨⟨assumpPref_dr hA1, assumpPref_dr hA2, hABb⟩,
    ⟨⟨hPB, hPA, hA2, hABa, hABb⟩, hABb, hABa⟩⟩

/-- Right endpoint typing `λ A', b' : Π A, B` for `CvP.lam` from
    `h1 : CvP E n Γ A A' (.sort u)` and `h2 : CvP E n (.assumption A :: Γ) b b' B`. -/
def lamRightP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' b b' B : Expr Nat} {u : Level}
    (h1 : CvP E n Γ A A' (.sort u))
    (h2 : CvP E n (.assumption A :: Γ) b b' B) :
    TyP E n Γ (.lam A' b') (.pi A B) :=
  let ⟨v, hB⟩ := h2.dl.reg
  let hb'_A' := TyP.cctx E n Γ b' B A A' u h2.dr h1
  let hB_A' := TyP.cctx E n Γ B (.sort v) A A' u hB h1
  let hlam_A' := TyP.lam E n Γ A' u b' B v h1.dr hb'_A' hB_A'
  let hpi_A := TyP.pi E n Γ A u B v h1.dl hB
  let hpi_A' := TyP.pi E n Γ A' u B v h1.dr hB_A'
  let hcv_B := CvP.refl E n (.assumption A :: Γ) B (.sort v) hB hB hB
  let hcv_pi := CvP.pi E n Γ A A' B B u v h1 hcv_B hpi_A hpi_A'
  let hcv_pi_symm := CvP.symm E n Γ (.pi A B) (.pi A' B) (.sort (.imax u v)) hcv_pi hpi_A' hpi_A
  TyP.conv E n Γ (.lam A' b') (.pi A' B) (.pi A B) (.imax u v) hlam_A' hcv_pi_symm

theorem assumpPref_lamRightP {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level}
    {h1 : CvP E n Γ A A' (.sort u)}
    {h2 : CvP E n (.assumption A :: Γ) b b' B}
    (hA1 : h1.AssumpPref) (hA2 : h2.AssumpPref) :
    (lamRightP h1 h2).AssumpPref := by
  have hAB := assumpPref_reg (assumpPref_dl hA2)
  have hAb'_A' : (TyP.cctx E n Γ b' B A A' u h2.dr h1).AssumpPref := ⟨assumpPref_dr hA2, hA1⟩
  have hAB_A' : (TyP.cctx E n Γ B (.sort h2.dl.reg.1) A A' u h2.dl.reg.2 h1).AssumpPref :=
    ⟨hAB, hA1⟩
  have hApi_A : (TyP.pi E n Γ A u B h2.dl.reg.1 h1.dl h2.dl.reg.2).AssumpPref :=
    ⟨assumpPref_dl hA1, hAB⟩
  have hApi_A' : (TyP.pi E n Γ A' u B h2.dl.reg.1 h1.dr
      (TyP.cctx E n Γ B (.sort h2.dl.reg.1) A A' u h2.dl.reg.2 h1)).AssumpPref :=
    ⟨assumpPref_dr hA1, hAB_A'⟩
  exact ⟨⟨assumpPref_dr hA1, hAb'_A', hAB_A'⟩,
    ⟨⟨hA1, ⟨hAB, hAB, hAB⟩, hApi_A, hApi_A'⟩, hApi_A', hApi_A⟩⟩

/-- Right endpoint typing `Π A', B' : .sort (.imax u v)` for `CvP.pi` from
    `h1 : CvP E n Γ A A' (.sort u)` and `h2 : CvP E n (.assumption A :: Γ) B B' (.sort v)`. -/
def piRightP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (h1 : CvP E n Γ A A' (.sort u))
    (h2 : CvP E n (.assumption A :: Γ) B B' (.sort v)) :
    TyP E n Γ (.pi A' B') (.sort (.imax u v)) :=
  let hB'_A' := TyP.cctx E n Γ B' (.sort v) A A' u h2.dr h1
  TyP.pi E n Γ A' u B' v h1.dr hB'_A'

theorem assumpPref_piRightP {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level}
    {h1 : CvP E n Γ A A' (.sort u)}
    {h2 : CvP E n (.assumption A :: Γ) B B' (.sort v)}
    (hA1 : h1.AssumpPref) (hA2 : h2.AssumpPref) :
    (piRightP h1 h2).AssumpPref :=
  ⟨assumpPref_dr hA1, ⟨assumpPref_dr hA2, hA1⟩⟩

/-- Right endpoint typing `.sort l₂ : .sort (.succ l₁)` for `CvP.sorts`, in one `TyP.sort` node
    via `eqN` slack (`S1` §4.1). -/
def sortsRightP {E : ResolvedEnv} {n : Nat} (Γ : LCtx) {l₁ l₂ : Level}
    (h : eqN l₁ l₂) :
    TyP E n Γ (.sort l₂) (.sort (.succ l₁)) :=
  TyP.sort E n Γ l₂ (.succ l₁) (fun ρ => congrArg (Option.map (· + 1)) (h ρ))

theorem assumpPref_sortsRightP {E : ResolvedEnv} {n : Nat} (Γ : LCtx) {l₁ l₂ : Level}
    (h : eqN l₁ l₂) :
    (sortsRightP (E := E) (n := n) Γ h).AssumpPref :=
  trivial

/-- Symmetry of `eqNList`. -/
theorem eqNList_symm_of : {ls ls' : List Level} → eqNList ls ls' → eqNList ls' ls
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨ fun ρ => (h ρ).symm, eqNList_symm_of hs ⟩

/-- Right endpoint typing `.const r ls' : instantiateLevels ls m.mtype` for `CvP.consts`,
    in one `TyP.const` node via `eqNList` slack (`S1` §4.1). -/
def constsRightP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {u : Level}
    (hres : E.members r = some m)
    (hlen : ls.length = m.arity)
    (hwf' : levelsBounded n ls' = true)
    (h : eqNList ls ls')
    (hT : TyP E n Γ (instantiateLevels ls m.mtype) (.sort u)) :
    TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype) :=
  TyP.const E n Γ r ls' ls m u hres ((eqNList_length ls ls' h).symm.trans hlen)
    hwf' (eqNList_symm_of h) hT

theorem assumpPref_constsRightP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {m : CheckedMember} {ls ls' : List Level} {u : Level}
    (hres : E.members r = some m)
    (hlen : ls.length = m.arity)
    (hwf' : levelsBounded n ls' = true)
    (h : eqNList ls ls')
    {hT : TyP E n Γ (instantiateLevels ls m.mtype) (.sort u)}
    (hAT : hT.AssumpPref) :
    (constsRightP hres hlen hwf' h hT).AssumpPref :=
  hAT

/-- Left endpoint typing `λ A, f↑ 0 : Π A, B` for `CvP.eta` from `hf : TyP E n Γ f (.pi A B)`. -/
def etaLeftP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (hf : TyP E n Γ f (.pi A B)) :
    TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B) :=
  let P := piInvP_here hf.reg.2
  etaLam hf P.hA P.hB

theorem assumpPref_etaLam {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f A B : Expr Nat} {u v : Level}
    {h : TyP E n Γ f (.pi A B)}
    {hA : TyP E n Γ A (.sort u)}
    {hB : TyP E n (.assumption A :: Γ) B (.sort v)}
    (hAh : h.AssumpPref) (hAA : hA.AssumpPref) (hAB : hB.AssumpPref) :
    (etaLam h hA hB).AssumpPref :=
  ⟨hAA,
    assumpPref_tyCast _ _
      ⟨assumpPref_wkAtZero hAh, assumpPref_wkAtZero hAA, assumpPref_tyCast _ _ hAB⟩,
    hAB⟩

theorem assumpPref_etaLeftP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    {hf : TyP E n Γ f (.pi A B)} (hAf : hf.AssumpPref) :
    (etaLeftP hf).AssumpPref := by
  have ⟨hPA, hPB⟩ := assumpPref_piInvP_here (assumpPref_reg hAf)
  exact assumpPref_etaLam hAf hPA hPB

/-- Congruence `CvP E n Γ (instantiate0 v B) (instantiate0 v' B) (.sort w)` under a `.letBinding`
    binder via the ζ-roundtrip `instantiate0 v B ←ζ (.letE A v B) ≡ (.letE A' v' B) →ζ instantiate0 v' B`. -/
def cvP_inst0_sortCongrLet {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' B : Expr Nat} {u w : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hv : CvP E n Γ v v' A)
    (hB : TyP E n (.letBinding A v :: Γ) B (.sort w))
    (hB' : TyP E n (.letBinding A' v' :: Γ) B (.sort w)) :
    CvP E n Γ (instantiate0 v B) (instantiate0 v' B) (.sort w) :=
  let hv'_A' := TyP.conv E n Γ v' A A' u hv.dr hA
  let hzetaL := trZeta hA.dl hv.dl hB
  let hzetaL_symm := CvP.symm E n Γ (.letE A v B) (instantiate0 v B) (.sort w)
    hzetaL hzetaL.dr hzetaL.dl
  let hzetaR := trZeta hA.dr hv'_A' hB'
  let hletB := CvP.letE E n Γ A A' v v' B B (.sort w) u
    hA hv (CvP.refl E n (.letBinding A v :: Γ) B (.sort w) hB hB hB)
    hzetaL.dl hzetaR.dl
  let hstep := CvP.trans E n Γ (instantiate0 v B) (.letE A v B) (.letE A' v' B) (.sort w)
    hzetaL_symm hletB hzetaL.dr hzetaR.dl
  CvP.trans E n Γ (instantiate0 v B) (.letE A' v' B) (instantiate0 v' B) (.sort w)
    hstep hzetaR hzetaL.dr hzetaR.dr

theorem assumpPref_cvP_inst0_sortCongrLet {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' B : Expr Nat} {u w : Level}
    {hA : CvP E n Γ A A' (.sort u)}
    {hv : CvP E n Γ v v' A}
    {hB : TyP E n (.letBinding A v :: Γ) B (.sort w)}
    {hB' : TyP E n (.letBinding A' v' :: Γ) B (.sort w)}
    (hAA : hA.AssumpPref) (hAv : hv.AssumpPref)
    (hAB : hB.AssumpPref) (hAB' : hB'.AssumpPref) :
    (cvP_inst0_sortCongrLet hA hv hB hB').AssumpPref := by
  have hv'P : (TyP.conv E n Γ v' A A' u hv.dr hA).AssumpPref := ⟨assumpPref_dr hAv, hAA⟩
  have hzetaL := assumpPref_trZeta (assumpPref_dl hAA) (assumpPref_dl hAv) hAB
  have hzetaR := assumpPref_trZeta (assumpPref_dr hAA) hv'P hAB'
  have hdlL := assumpPref_dl hzetaL
  have hdrL := assumpPref_dr hzetaL
  have hdlR := assumpPref_dl hzetaR
  have hdrR := assumpPref_dr hzetaR
  exact ⟨⟨⟨hzetaL, hdrL, hdlL⟩,
      ⟨hAA, hAv, ⟨hAB, hAB, hAB⟩, hdlL, hdlR⟩, hdrL, hdlR⟩,
    hzetaR, hdrL, hdrR⟩

/-- Option L-inline-at-0 (`issuecomment-6161495965` Obligation 1): when both endpoints of
    `ConvT.letE` are `letSub`-normalised at `j = 0` (`instantiate0 v b` and `instantiate0 v' b'`),
    the `j = 0` substituted body conversion `hb_sub` and `CvP.fsub` connect them directly in `Γ`
    with **zero** let-binding `cctx`. -/
def cvpLetInline0 {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hv : CvP E n Γ v v' A)
    (hb_assump : TyP E n (.assumption A :: Γ) b' B)
    (hb_sub : CvP E n Γ (instantiate0 v b) (instantiate0 v b') (instantiate0 v B)) :
    CvP E n Γ (instantiate0 v b) (instantiate0 v' b') (instantiate0 v B) :=
  let ⟨w, hB_assump⟩ := hb_assump.reg
  let hBv := instEnd hB_assump hv.dl hA.dl
  let hBv' := instEnd hB_assump hv.dr hA.dl
  let hfsubB := CvP.fsub E n Γ A B (.sort w) v v' u hB_assump hA.dl hv hBv hBv'
  let hfsubB_symm := CvP.symm E n Γ (instantiate0 v B) (instantiate0 v' B) (.sort w)
    hfsubB hBv' hBv
  let hb'_v' := TyP.conv E n Γ (instantiate0 v' b') (instantiate0 v' B) (instantiate0 v B) w
    (instEnd hb_assump hv.dr hA.dl) hfsubB_symm
  let stepFsub := CvP.fsub E n Γ A b' B v v' u hb_assump hA.dl hv hb_sub.dr hb'_v'
  CvP.trans E n Γ (instantiate0 v b) (instantiate0 v b') (instantiate0 v' b') (instantiate0 v B)
    hb_sub stepFsub hb_sub.dl hb'_v'

theorem assumpPref_cvpLetInline0 {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    {hA : CvP E n Γ A A' (.sort u)}
    {hv : CvP E n Γ v v' A}
    {hb_assump : TyP E n (.assumption A :: Γ) b' B}
    {hb_sub : CvP E n Γ (instantiate0 v b) (instantiate0 v b') (instantiate0 v B)}
    (hAA : hA.AssumpPref) (hAv : hv.AssumpPref)
    (hAba : hb_assump.AssumpPref) (hAbs : hb_sub.AssumpPref) :
    (cvpLetInline0 hA hv hb_assump hb_sub).AssumpPref := by
  have hAB := assumpPref_reg hAba
  have hABv := assumpPref_instEnd hAB (assumpPref_dl hAv) (assumpPref_dl hAA)
  have hABv' := assumpPref_instEnd hAB (assumpPref_dr hAv) (assumpPref_dl hAA)
  have hb'_v'P : (TyP.conv E n Γ (instantiate0 v' b') (instantiate0 v' B) (instantiate0 v B)
      hb_assump.reg.1 (instEnd hb_assump hv.dr hA.dl)
      (CvP.symm E n Γ (instantiate0 v B) (instantiate0 v' B) (.sort hb_assump.reg.1)
        (CvP.fsub E n Γ A B (.sort hb_assump.reg.1) v v' u hb_assump.reg.2 hA.dl hv
          (instEnd hb_assump.reg.2 hv.dl hA.dl) (instEnd hb_assump.reg.2 hv.dr hA.dl))
        (instEnd hb_assump.reg.2 hv.dr hA.dl) (instEnd hb_assump.reg.2 hv.dl hA.dl))).AssumpPref :=
    ⟨assumpPref_instEnd hAba (assumpPref_dr hAv) (assumpPref_dl hAA),
      ⟨⟨hAB, assumpPref_dl hAA, hAv, hABv, hABv'⟩, hABv', hABv⟩⟩
  exact ⟨hAbs, ⟨hAba, assumpPref_dl hAA, hAv, assumpPref_dr hAbs, hb'_v'P⟩,
    assumpPref_dl hAbs, hb'_v'P⟩

/-- Enriched counterpart of `hasTyTConvLet` (`RcicParRedSRTyped.lean:1161`), used only when
    constructing the un-inlined surface right endpoint `.letE A' v' b'` of `CvP.letE`. -/
@[reducible] def LetCtxConvP (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx} {A A' v v' e T : Expr Nat} {u : Level},
    CvP E n Γ A A' (.sort u) →
    CvP E n Γ v v' A →
    TyP E n (.letBinding A v :: Γ) e T →
    TyP E n (.letBinding A' v' :: Γ) e T

/-- `AssumpPref`-preservation contract for `hlet : LetCtxConvP E n`. -/
def LetCtxConvP.AssumpPref {E : ResolvedEnv} {n : Nat} (hlet : LetCtxConvP E n) : Prop :=
  ∀ {Γ : LCtx} {A A' v v' e T : Expr Nat} {u : Level}
    {hA : CvP E n Γ A A' (.sort u)} {hv : CvP E n Γ v v' A}
    {D : TyP E n (.letBinding A v :: Γ) e T},
    hA.AssumpPref → hv.AssumpPref → D.AssumpPref → (hlet hA hv D).AssumpPref

/-- `LetCtxConvP` discharged by the let-binding-slot walk: `tyCctxLetAt` at
    `k = 0` transports the body derivation through the slot's domain and
    value conversions while keeping the ascribed type `T` — so the sort
    `letRightP` pins survives unchanged. A `CvWalkHyp E` suffices: the
    group-intermediate environments never carry an `EnvWfT`, and the walk
    only reads member closedness, level bounds, and arity certificates. -/
def letCtxConvP_of_cvWalkHyp {E : ResolvedEnv} (w : CvWalkHyp E) {n : Nat} :
    LetCtxConvP E n :=
  fun {Γ A A' v v' e T u} (hA : CvP E n Γ A A' (.sort u))
      (hv : CvP E n Γ v v' A) (hb : TyP E n (.letBinding A v :: Γ) e T) =>
    tyCctxLetAt (Ei := E) w (iotaPack_of_cvWalkHyp w)
      (fun hext' h => derivedIotaExt hext' h) (envExt_refl E)
      (rfl : List.get? (.letBinding A v :: Γ) 0 = some (.letBinding A v)) hA hv hb

/-- `EnvWfT`-fronted `LetCtxConvP`. -/
noncomputable def letCtxConvP_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} :
    LetCtxConvP E n :=
  letCtxConvP_of_cvWalkHyp (cvWalkHyp_of_envWfT hW)

/-- Surface right endpoint typing `.letE A' v' b' : instantiate0 v B` for `CvP.letE`. -/
def letRightP {E : ResolvedEnv} {n : Nat} (hlet : LetCtxConvP E n)
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B) :
    TyP E n Γ (.letE A' v' b') (instantiate0 v B) :=
  let ⟨w, hB⟩ := hb.dl.reg
  let hB' := hlet hA hv hB
  let hb_r' := hlet hA hv hb.dr
  let hcongr := cvP_inst0_sortCongrLet hA hv hB hB'
  let hcongr_symm := CvP.symm E n Γ (instantiate0 v B) (instantiate0 v' B) (.sort w)
    hcongr hcongr.dr hcongr.dl
  letSurfR hA hv hb_r' hcongr_symm

theorem assumpPref_letRightP {E : ResolvedEnv} {n : Nat}
    {hlet : LetCtxConvP E n} (hAlet : LetCtxConvP.AssumpPref hlet)
    {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
    {hA : CvP E n Γ A A' (.sort u)}
    {hv : CvP E n Γ v v' A}
    {hb : CvP E n (.letBinding A v :: Γ) b b' B}
    (hAA : hA.AssumpPref) (hAv : hv.AssumpPref) (hAb : hb.AssumpPref) :
    (letRightP hlet hA hv hb).AssumpPref := by
  have hAB := assumpPref_reg (assumpPref_dl hAb)
  have hAB' := hAlet hAA hAv hAB
  have hAbr' := hAlet hAA hAv (assumpPref_dr hAb)
  have hAcongr := assumpPref_cvP_inst0_sortCongrLet hAA hAv hAB hAB'
  have hAcongr_symm : (CvP.symm E n Γ (instantiate0 v B) (instantiate0 v' B)
      (.sort hb.dl.reg.1) (cvP_inst0_sortCongrLet hA hv hb.dl.reg.2 (hlet hA hv hb.dl.reg.2))
      (cvP_inst0_sortCongrLet hA hv hb.dl.reg.2 (hlet hA hv hb.dl.reg.2)).dr
      (cvP_inst0_sortCongrLet hA hv hb.dl.reg.2 (hlet hA hv hb.dl.reg.2)).dl).AssumpPref :=
    ⟨hAcongr, assumpPref_dr hAcongr, assumpPref_dl hAcongr⟩
  exact assumpPref_letSurfR hAA hAv hAbr' hAcongr_symm

/-! ## §4 Plain-to-`⁺` Enrichment (`enrichHasTyT`, `enrichConvT`, `enrichTyConvT`, `enrichCtxWfT`)
    and Q7 Totality (`assumpPref_enrichHasTyT`, `assumpPref_enrichConvT`) -/

mutual

/-- Enrich a plain typing derivation `HasTyT E₁ n Γ e T` into `TyP E n Γ e T`. -/
def enrichHasTyT {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n) :
    {Γ : LCtx} → CtxP E n Γ → {e T : Expr Nat} → HasTyT E₁ n Γ e T → TyP E n Γ e T
  | Γ, _, _, _, .sort _ l =>
      TyP.sort E n Γ l (.succ l) (eqN_refl _)
  | Γ, C, _, _, .bvar _ i A hlook =>
      let ⟨u, hA⟩ := ctxP_lookupType_sort C hlook
      TyP.bvar E n Γ i A u hlook hA
  | Γ, _, _, _, .const _ r ls m hres hlen hwf =>
      let hresE := hext r m hres
      let ⟨u, hT⟩ := instMemberSortP hcl hm Γ hresE hlen hwf
      TyP.const E n Γ r ls ls m u hresE hlen hwf (eqNList_refl ls) hT
  | Γ, C, _, _, .pi _ A u B v hA hB =>
      let hAP := enrichHasTyT hcl hext hm hlet C hA
      let CA := CtxP.assumption E n Γ A u C hAP
      let hBP := enrichHasTyT hcl hext hm hlet CA hB
      TyP.pi E n Γ A u B v hAP hBP
  | Γ, C, _, _, .lam _ A u body B hA hbody =>
      let hAP := enrichHasTyT hcl hext hm hlet C hA
      let CA := CtxP.assumption E n Γ A u C hAP
      let hbodyP := enrichHasTyT hcl hext hm hlet CA hbody
      let ⟨v, hBP⟩ := hbodyP.reg
      TyP.lam E n Γ A u body B v hAP hbodyP hBP
  | Γ, C, _, _, .app _ f a A B hf ha =>
      let hfP := enrichHasTyT hcl hext hm hlet C hf
      let haP := enrichHasTyT hcl hext hm hlet C ha
      let P := piInvP_here hfP.reg.2
      TyP.app E n Γ f a A B P.v hfP haP (instEnd P.hB haP P.hA)
  | Γ, C, _, _, .letE _ A u value B body hA hv hb =>
      let hAP := enrichHasTyT hcl hext hm hlet C hA
      let hvP := enrichHasTyT hcl hext hm hlet C hv
      let CLet := CtxP.letBinding E n Γ A u value C hAP hvP
      let hbP := enrichHasTyT hcl hext hm hlet CLet hb
      trLetE hAP hvP hbP
  | Γ, C, _, _, .lit _ t T hexp =>
      TyP.lit E n Γ t T (enrichHasTyT hcl hext hm hlet C hexp)
  | Γ, C, _, _, .conv _ e A B u h hc =>
      TyP.conv E n Γ e A B u
        (enrichHasTyT hcl hext hm hlet C h)
        (enrichConvT hcl hext hm hlet C hc)

/-- Enrich a plain conversion derivation `ConvT E₁ n Γ a b T` into `CvP E n Γ a b T`. -/
def enrichConvT {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n) :
    {Γ : LCtx} → CtxP E n Γ → {a b T : Expr Nat} → ConvT E₁ n Γ a b T → CvP E n Γ a b T
  | Γ, C, _, _, _, .refl _ a A h =>
      let hP := enrichHasTyT hcl hext hm hlet C h
      CvP.refl E n Γ a A hP hP hP
  | Γ, C, _, _, _, .symm _ a b A h =>
      let hP := enrichConvT hcl hext hm hlet C h
      CvP.symm E n Γ a b A hP hP.dr hP.dl
  | Γ, C, _, _, _, .trans _ a b c A h1 h2 =>
      let h1P := enrichConvT hcl hext hm hlet C h1
      let h2P := enrichConvT hcl hext hm hlet C h2
      CvP.trans E n Γ a b c A h1P h2P h1P.dl h2P.dr
  | Γ, C, _, _, _, .beta _ A body arg B u hA hbody harg =>
      let hAP := enrichHasTyT hcl hext hm hlet C hA
      let CA := CtxP.assumption E n Γ A u C hAP
      let hbodyP := enrichHasTyT hcl hext hm hlet CA hbody
      let hargP := enrichHasTyT hcl hext hm hlet C harg
      CvP.beta E n Γ A body arg B u hAP hbodyP hargP
        (betaLeftP hAP hbodyP hargP) (instEnd hbodyP hargP hAP)
  | Γ, C, _, _, _, .zeta _ A value body B u hA hv hb =>
      let hAP := enrichHasTyT hcl hext hm hlet C hA
      let hvP := enrichHasTyT hcl hext hm hlet C hv
      let CLet := CtxP.letBinding E n Γ A u value C hAP hvP
      let hbP := enrichHasTyT hcl hext hm hlet CLet hb
      trZeta hAP hvP hbP
  | Γ, C, _, _, _, .zetaLocal _ i A v hval hty hv =>
      let hvP := enrichHasTyT hcl hext hm hlet C hv
      let ⟨u, hAP⟩ := ctxP_lookupType_sort C hty
      let hdl := TyP.bvar E n Γ i A u hty hAP
      CvP.zetaLocal E n Γ i A v hval hty hvP hdl hvP
  | Γ, C, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb =>
      let hresE := hext r m hres
      let hbP := enrichHasTyT hcl hext hm hlet C hb
      let ⟨u, hT⟩ := instMemberSortP hcl hm Γ hresE hlen hwf
      let hdl := TyP.const E n Γ r ls ls m u hresE hlen hwf (eqNList_refl ls) hT
      CvP.delta E n Γ r ls m b hresE hbody htr hlen hwf hbP hdl hbP
  | Γ, C, _, _, _, .iota _ lhs rhs T h hlhs hrhs =>
      let hlhsP := enrichHasTyT hcl hext hm hlet C hlhs
      let hrhsP := enrichHasTyT hcl hext hm hlet C hrhs
      CvP.iota E n Γ lhs rhs T (derivedIotaExt hext h) hlhsP hrhsP hlhsP hrhsP
  | Γ, C, _, _, _, .lit _ t _ T (.of _) hexp =>
      let hexpP := enrichHasTyT hcl hext hm hlet C hexp
      CvP.lit E n Γ t (natExpand t) T (.of t) hexpP (TyP.lit E n Γ t T hexpP) hexpP
  | Γ, C, _, _, _, .app _ f g a b A B h1 h2 =>
      let h1P := enrichConvT hcl hext hm hlet C h1
      let h2P := enrichConvT hcl hext hm hlet C h2
      let P := piInvP_here h1P.dl.reg.2
      let hdl := TyP.app E n Γ f a A B P.v h1P.dl h2P.dl (instEnd P.hB h2P.dl P.hA)
      CvP.app E n Γ f g a b A B h1P h2P hdl (appRightP h1P h2P)
  | Γ, C, _, _, _, .lam _ A A' b b' B u hA hb =>
      let hAP := enrichConvT hcl hext hm hlet C hA
      let CA := CtxP.assumption E n Γ A u C hAP.dl
      let hbP := enrichConvT hcl hext hm hlet CA hb
      let ⟨v, hBP⟩ := hbP.dl.reg
      let hdl := TyP.lam E n Γ A u b B v hAP.dl hbP.dl hBP
      CvP.lam E n Γ A A' b b' B u hAP hbP hdl (lamRightP hAP hbP)
  | Γ, C, _, _, _, .pi _ A A' B B' u v hA hB =>
      let hAP := enrichConvT hcl hext hm hlet C hA
      let CA := CtxP.assumption E n Γ A u C hAP.dl
      let hBP := enrichConvT hcl hext hm hlet CA hB
      let hdl := TyP.pi E n Γ A u B v hAP.dl hBP.dl
      CvP.pi E n Γ A A' B B' u v hAP hBP hdl (piRightP hAP hBP)
  | Γ, C, _, _, _, .letE _ A A' v v' b b' B u hA hv hb =>
      let hAP := enrichConvT hcl hext hm hlet C hA
      let hvP := enrichConvT hcl hext hm hlet C hv
      let CLet := CtxP.letBinding E n Γ A u v C hAP.dl hvP.dl
      let hbP := enrichConvT hcl hext hm hlet CLet hb
      CvP.letE E n Γ A A' v v' b b' B u hAP hvP hbP
        (letSurfL hAP hvP hbP.dl) (letRightP hlet hAP hvP hbP)
  | Γ, _, _, _, _, .sorts _ l₁ l₂ h =>
      let hdl := TyP.sort E n Γ l₁ (.succ l₁) (eqN_refl _)
      CvP.sorts E n Γ l₁ l₂ h hdl (sortsRightP Γ h)
  | Γ, _, _, _, _, .consts _ r ls ls' m hres hlen hwf hwf' h =>
      let hresE := hext r m hres
      let ⟨u, hT⟩ := instMemberSortP hcl hm Γ hresE hlen hwf
      let hdl := TyP.const E n Γ r ls ls m u hresE hlen hwf (eqNList_refl ls) hT
      CvP.consts E n Γ r ls ls' m hresE hlen hwf hwf' h hdl
        (constsRightP hresE hlen hwf' h hT)
  | Γ, C, _, _, _, .eta _ f A B h =>
      let hP := enrichHasTyT hcl hext hm hlet C h
      CvP.eta E n Γ f A B hP (etaLeftP hP) hP
  | Γ, C, _, _, _, .irr _ P p q hP hp hq =>
      let hPP := enrichHasTyT hcl hext hm hlet C hP
      let hpP := enrichHasTyT hcl hext hm hlet C hp
      let hqP := enrichHasTyT hcl hext hm hlet C hq
      CvP.irr E n Γ P p q hPP hpP hqP hpP hqP
  | Γ, C, _, _, _, .tyConv _ a b A A' u h hA =>
      let hP := enrichConvT hcl hext hm hlet C h
      let hAP := enrichConvT hcl hext hm hlet C hA
      let hdl := TyP.conv E n Γ a A A' u hP.dl hAP
      let hdr := TyP.conv E n Γ b A A' u hP.dr hAP
      CvP.tyConv E n Γ a b A A' u hP hAP hdl hdr

end

mutual

/-- **Q7 Obligation 2 (`issuecomment-6161495965`)**: Every `TyP` derivation produced by
    `enrichHasTyT` satisfies `TyP.AssumpPref` (every `.wk`, `.esub`, and `.lsub` transport
    in the enriched derivation tree satisfies `AssumptionPrefix` at its cutoff/index). -/
theorem assumpPref_enrichHasTyT {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E)
    {hm : MemberSortP E} (hAm : MemberSortP.AssumpPref hm)
    {hlet : LetCtxConvP E n} (hAlet : LetCtxConvP.AssumpPref hlet) :
    ∀ {Γ : LCtx} (C : CtxP E n Γ) {e T : Expr Nat} (D : HasTyT E₁ n Γ e T),
      C.AssumpPref → (enrichHasTyT hcl hext hm hlet C D).AssumpPref
  | _, _, _, _, .sort _ _, _ => trivial
  | _, C, _, _, .bvar _ _ _ hlook, hAC =>
      assumpPref_ctxP_lookupType_sort C hlook hAC
  | Γ, _, _, _, .const _ _ _ _ hres hlen hwf, _ =>
      assumpPref_instMemberSortP hcl hm hAm Γ (hext _ _ hres) hlen hwf
  | Γ, C, _, _, .pi _ A u _ _ hA hB, hAC => by
      unfold enrichHasTyT
      have hAAP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hA hAC
      have hCA : (CtxP.assumption E n Γ A u C (enrichHasTyT hcl hext hm hlet C hA)).AssumpPref :=
        ⟨hAC, hAAP⟩
      exact ⟨hAAP, assumpPref_enrichHasTyT hcl hext hAm hAlet _ hB hCA⟩
  | Γ, C, _, _, .lam _ A u _ _ hA hbody, hAC => by
      unfold enrichHasTyT
      have hAAP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hA hAC
      have hCA : (CtxP.assumption E n Γ A u C (enrichHasTyT hcl hext hm hlet C hA)).AssumpPref :=
        ⟨hAC, hAAP⟩
      have hAbodyP := assumpPref_enrichHasTyT hcl hext hAm hAlet _ hbody hCA
      exact ⟨hAAP, hAbodyP, assumpPref_reg hAbodyP⟩
  | _, C, _, _, .app _ _ _ _ _ hf ha, hAC => by
      unfold enrichHasTyT
      have hAfP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hf hAC
      have hAaP := assumpPref_enrichHasTyT hcl hext hAm hAlet C ha hAC
      have ⟨hPA, hPB⟩ := assumpPref_piInvP_here (assumpPref_reg hAfP)
      exact ⟨hAfP, hAaP, assumpPref_instEnd hPB hAaP hPA⟩
  | Γ, C, _, _, .letE _ A u value _ _ hA hv hb, hAC => by
      unfold enrichHasTyT
      have hAAP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hA hAC
      have hAvP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hv hAC
      have hCLet : (CtxP.letBinding E n Γ A u value C
          (enrichHasTyT hcl hext hm hlet C hA)
          (enrichHasTyT hcl hext hm hlet C hv)).AssumpPref :=
        ⟨hAC, hAAP, hAvP⟩
      have hAbP := assumpPref_enrichHasTyT hcl hext hAm hAlet _ hb hCLet
      exact assumpPref_trLetE hAAP hAvP hAbP
  | _, C, _, _, .lit _ _ _ hexp, hAC =>
      assumpPref_enrichHasTyT hcl hext hAm hAlet C hexp hAC
  | _, C, _, _, .conv _ _ _ _ _ h hc, hAC => by
      unfold enrichHasTyT
      exact ⟨assumpPref_enrichHasTyT hcl hext hAm hAlet C h hAC,
        assumpPref_enrichConvT hcl hext hAm hAlet C hc hAC⟩

/-- **Q7 Obligation 2 (`issuecomment-6161495965`)**: Every `CvP` derivation produced by
    `enrichConvT` satisfies `CvP.AssumpPref`. -/
theorem assumpPref_enrichConvT {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E)
    {hm : MemberSortP E} (hAm : MemberSortP.AssumpPref hm)
    {hlet : LetCtxConvP E n} (hAlet : LetCtxConvP.AssumpPref hlet) :
    ∀ {Γ : LCtx} (C : CtxP E n Γ) {a b T : Expr Nat} (h : ConvT E₁ n Γ a b T),
      C.AssumpPref → (enrichConvT hcl hext hm hlet C h).AssumpPref
  | _, C, _, _, _, .refl _ _ _ h, hAC => by
      unfold enrichConvT
      have hAhP := assumpPref_enrichHasTyT hcl hext hAm hAlet C h hAC
      exact ⟨hAhP, hAhP, hAhP⟩
  | _, C, _, _, _, .symm _ _ _ _ h, hAC => by
      unfold enrichConvT
      have hAhP := assumpPref_enrichConvT hcl hext hAm hAlet C h hAC
      exact ⟨hAhP, assumpPref_dr hAhP, assumpPref_dl hAhP⟩
  | _, C, _, _, _, .trans _ _ _ _ _ h1 h2, hAC => by
      unfold enrichConvT
      have hA1P := assumpPref_enrichConvT hcl hext hAm hAlet C h1 hAC
      have hA2P := assumpPref_enrichConvT hcl hext hAm hAlet C h2 hAC
      exact ⟨hA1P, hA2P, assumpPref_dl hA1P, assumpPref_dr hA2P⟩
  | Γ, C, _, _, _, .beta _ A _ _ _ u hA hbody harg, hAC => by
      unfold enrichConvT
      have hAAP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hA hAC
      have hCA : (CtxP.assumption E n Γ A u C (enrichHasTyT hcl hext hm hlet C hA)).AssumpPref :=
        ⟨hAC, hAAP⟩
      have hAbodyP := assumpPref_enrichHasTyT hcl hext hAm hAlet _ hbody hCA
      have hAargP := assumpPref_enrichHasTyT hcl hext hAm hAlet C harg hAC
      exact ⟨hAAP, hAbodyP, hAargP,
        assumpPref_betaLeftP hAAP hAbodyP hAargP,
        assumpPref_instEnd hAbodyP hAargP hAAP⟩
  | Γ, C, _, _, _, .zeta _ A value _ _ u hA hv hb, hAC => by
      unfold enrichConvT
      have hAAP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hA hAC
      have hAvP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hv hAC
      have hCLet : (CtxP.letBinding E n Γ A u value C
          (enrichHasTyT hcl hext hm hlet C hA)
          (enrichHasTyT hcl hext hm hlet C hv)).AssumpPref :=
        ⟨hAC, hAAP, hAvP⟩
      have hAbP := assumpPref_enrichHasTyT hcl hext hAm hAlet _ hb hCLet
      exact assumpPref_trZeta hAAP hAvP hAbP
  | _, C, _, _, _, .zetaLocal _ _ _ _ _ hty hv, hAC => by
      unfold enrichConvT
      have hAvP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hv hAC
      exact ⟨hAvP, assumpPref_ctxP_lookupType_sort C hty hAC, hAvP⟩
  | Γ, C, _, _, _, .delta _ _ _ _ _ hres _ _ hlen hwf hb, hAC => by
      unfold enrichConvT
      have hAbP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hb hAC
      exact ⟨hAbP, assumpPref_instMemberSortP hcl hm hAm Γ (hext _ _ hres) hlen hwf, hAbP⟩
  | _, C, _, _, _, .iota _ _ _ _ _ hlhs hrhs, hAC => by
      unfold enrichConvT
      have hAlhsP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hlhs hAC
      have hArhsP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hrhs hAC
      exact ⟨hAlhsP, hArhsP, hAlhsP, hArhsP⟩
  | _, C, _, _, _, .lit _ _ _ _ (.of _) hexp, hAC => by
      unfold enrichConvT
      have hAexpP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hexp hAC
      exact ⟨hAexpP, hAexpP, hAexpP⟩
  | _, C, _, _, _, .app _ _ _ _ _ _ _ h1 h2, hAC => by
      unfold enrichConvT
      have hA1P := assumpPref_enrichConvT hcl hext hAm hAlet C h1 hAC
      have hA2P := assumpPref_enrichConvT hcl hext hAm hAlet C h2 hAC
      have ⟨hPA, hPB⟩ := assumpPref_piInvP_here (assumpPref_reg (assumpPref_dl hA1P))
      exact ⟨hA1P, hA2P,
        ⟨assumpPref_dl hA1P, assumpPref_dl hA2P,
          assumpPref_instEnd hPB (assumpPref_dl hA2P) hPA⟩,
        assumpPref_appRightP hA1P hA2P⟩
  | Γ, C, _, _, _, .lam _ A _ _ _ _ u hA hb, hAC => by
      unfold enrichConvT
      have hAAP := assumpPref_enrichConvT hcl hext hAm hAlet C hA hAC
      have hCA : (CtxP.assumption E n Γ A u C (enrichConvT hcl hext hm hlet C hA).dl).AssumpPref :=
        ⟨hAC, assumpPref_dl hAAP⟩
      have hAbP := assumpPref_enrichConvT hcl hext hAm hAlet _ hb hCA
      exact ⟨hAAP, hAbP,
        ⟨assumpPref_dl hAAP, assumpPref_dl hAbP, assumpPref_reg (assumpPref_dl hAbP)⟩,
        assumpPref_lamRightP hAAP hAbP⟩
  | Γ, C, _, _, _, .pi _ A _ _ _ u _ hA hB, hAC => by
      unfold enrichConvT
      have hAAP := assumpPref_enrichConvT hcl hext hAm hAlet C hA hAC
      have hCA : (CtxP.assumption E n Γ A u C (enrichConvT hcl hext hm hlet C hA).dl).AssumpPref :=
        ⟨hAC, assumpPref_dl hAAP⟩
      have hABP := assumpPref_enrichConvT hcl hext hAm hAlet _ hB hCA
      exact ⟨hAAP, hABP, ⟨assumpPref_dl hAAP, assumpPref_dl hABP⟩,
        assumpPref_piRightP hAAP hABP⟩
  | Γ, C, _, _, _, .letE _ A _ v _ _ _ _ u hA hv hb, hAC => by
      unfold enrichConvT
      have hAAP := assumpPref_enrichConvT hcl hext hAm hAlet C hA hAC
      have hAvP := assumpPref_enrichConvT hcl hext hAm hAlet C hv hAC
      have hCLet : (CtxP.letBinding E n Γ A u v C
          (enrichConvT hcl hext hm hlet C hA).dl
          (enrichConvT hcl hext hm hlet C hv).dl).AssumpPref :=
        ⟨hAC, assumpPref_dl hAAP, assumpPref_dl hAvP⟩
      have hAbP := assumpPref_enrichConvT hcl hext hAm hAlet _ hb hCLet
      exact ⟨hAAP, hAvP, hAbP,
        assumpPref_letSurfL hAAP hAvP (assumpPref_dl hAbP),
        assumpPref_letRightP hAlet hAAP hAvP hAbP⟩
  | Γ, _, _, _, _, .sorts _ _ _ h, _ => by
      unfold enrichConvT
      exact ⟨trivial, assumpPref_sortsRightP Γ h⟩
  | Γ, _, _, _, _, .consts _ _ _ _ _ hres hlen hwf hwf' h, _ => by
      unfold enrichConvT
      have hAT := assumpPref_instMemberSortP hcl hm hAm Γ (hext _ _ hres) hlen hwf
      exact ⟨hAT, assumpPref_constsRightP (hext _ _ hres) hlen hwf' h hAT⟩
  | _, C, _, _, _, .eta _ _ _ _ h, hAC => by
      unfold enrichConvT
      have hAhP := assumpPref_enrichHasTyT hcl hext hAm hAlet C h hAC
      exact ⟨hAhP, assumpPref_etaLeftP hAhP, hAhP⟩
  | _, C, _, _, _, .irr _ _ _ _ hP hp hq, hAC => by
      unfold enrichConvT
      have hAPP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hP hAC
      have hApP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hp hAC
      have hAqP := assumpPref_enrichHasTyT hcl hext hAm hAlet C hq hAC
      exact ⟨hAPP, hApP, hAqP, hApP, hAqP⟩
  | _, C, _, _, _, .tyConv _ _ _ _ _ _ h hA, hAC => by
      unfold enrichConvT
      have hAhP := assumpPref_enrichConvT hcl hext hAm hAlet C h hAC
      have hAAP := assumpPref_enrichConvT hcl hext hAm hAlet C hA hAC
      exact ⟨hAhP, hAAP, ⟨assumpPref_dl hAhP, hAAP⟩, ⟨assumpPref_dr hAhP, hAAP⟩⟩

end

/-- Enrich a plain `TyConvT E₁ n Γ A B` chain into a heterogeneous `TyCvP E n Γ A B` chain
    (`RcicSynSortRow.lean:336`). -/
def enrichTyConvT {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n)
    {Γ : LCtx} (C : CtxP E n Γ) :
    {A B : Expr Nat} → TyConvT E₁ n Γ A B → TyCvP E n Γ A B
  | A, _, .refl _ _ => .refl Γ A
  | A, B, .of _ _ _ u h => .of Γ A B u (enrichConvT hcl hext hm hlet C h)
  | A, C', .trans _ _ B _ h1 h2 =>
      .trans Γ A B C'
        (enrichTyConvT hcl hext hm hlet C h1)
        (enrichTyConvT hcl hext hm hlet C h2)

/-- Enrich a plain context `CtxWfT E₁ n Γ` into `CtxP E n Γ`. -/
def enrichCtxWfT {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n) :
    {Γ : LCtx} → CtxWfT E₁ n Γ → CtxP E n Γ
  | _, .nil => .nil E n
  | _, .assumption Γ A u hΓ hA =>
      let C := enrichCtxWfT hcl hext hm hlet hΓ
      .assumption E n Γ A u C (enrichHasTyT hcl hext hm hlet C hA)
  | _, .letBinding Γ A u v hΓ hA hv =>
      let C := enrichCtxWfT hcl hext hm hlet hΓ
      .letBinding E n Γ A u v C
        (enrichHasTyT hcl hext hm hlet C hA)
        (enrichHasTyT hcl hext hm hlet C hv)

/-- `enrichCtxWfT` produces a context spine satisfying `CtxP.AssumpPref`. -/
theorem assumpPref_enrichCtxWfT {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E)
    {hm : MemberSortP E} (hAm : MemberSortP.AssumpPref hm)
    {hlet : LetCtxConvP E n} (hAlet : LetCtxConvP.AssumpPref hlet) :
    ∀ {Γ : LCtx} (hΓ : CtxWfT E₁ n Γ),
      (enrichCtxWfT hcl hext hm hlet hΓ).AssumpPref
  | _, .nil => trivial
  | _, .assumption _ _ _ hΓ hA => by
      unfold enrichCtxWfT
      have hAC := assumpPref_enrichCtxWfT hcl hext hAm hAlet hΓ
      exact ⟨hAC, assumpPref_enrichHasTyT hcl hext hAm hAlet _ hA hAC⟩
  | _, .letBinding _ _ _ _ hΓ hA hv => by
      unfold enrichCtxWfT
      have hAC := assumpPref_enrichCtxWfT hcl hext hAm hAlet hΓ
      exact ⟨hAC,
        assumpPref_enrichHasTyT hcl hext hAm hAlet _ hA hAC,
        assumpPref_enrichHasTyT hcl hext hAm hAlet _ hv hAC⟩

/-- Plain `TyConvT` sort-injectivity bridge (`TypedRowsWf.sortRow` via `enrichTyConvT`):
    any plain `h : TyConvT E₁ n Γ (.sort u) (.sort v)` whose enriched `TyCvP` chain
    satisfies `TyCvP.ESChain` under a `TableWF` table yields `eqN u v` (with zero `hUniq`). -/
theorem sortRow_of_tyConvT_esChain_id {tbl : List CRule} (hW : TableWF tbl)
    {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n)
    {Γ : LCtx} (C : CtxP E n Γ) {u v : Level}
    (h : TyConvT E₁ n Γ (.sort u) (.sort v))
    (ρ : List Disp)
    (hc : TyCvP.ESChain tbl id ρ (enrichTyConvT hcl hext hm hlet C h)
      (TyP.sort E n Γ u (.succ u) (eqN_refl _))
      (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    eqN u v :=
  sortRow_of_tyCvP_esChain_id hW (enrichTyConvT hcl hext hm hlet C h) ρ hc

/-- Single-step plain `ConvT` sort-injectivity bridge: any `h : ConvT E₁ n Γ (.sort u) (.sort v) (.sort w)`
    whose enriched conversion `hP := enrichConvT hcl hext hm hlet C h` satisfies `ES` and
    endpoint `CL` under a `TableWF` table yields `eqN u v`. -/
theorem sortRow_of_convT_es_cl_id {tbl : List CRule} (hW : TableWF tbl)
    {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n)
    {Γ : LCtx} (C : CtxP E n Γ) {u v w : Level}
    (h : ConvT E₁ n Γ (.sort u) (.sort v) (.sort w))
    (ρ : List Disp)
    (hL : CL tbl id ρ (TyP.sort E n Γ u (.succ u) (eqN_refl _))
      (enrichConvT hcl hext hm hlet C h).dl)
    (hes : ES tbl id ρ (enrichConvT hcl hext hm hlet C h))
    (hR : CL tbl id ρ (enrichConvT hcl hext hm hlet C h).dr
      (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    eqN u v :=
  sortRow_of_tyConvT_esChain_id hW hcl hext hm hlet C
    (.of Γ (.sort u) (.sort v) w h) ρ
    (.of (enrichConvT hcl hext hm hlet C h) _ _ hL hes hR)

/-- Extend `MemberSortP E` across a fresh member `r₀ ↦ m₀` with `hT : TyP E m₀.arity [] m₀.mtype (.sort u₀)`. -/
def memberSortP_extendEnv {E : ResolvedEnv} {r₀ : Nat} {m₀ : CheckedMember} {u₀ : Level}
    (hm : MemberSortP E) (hfresh : E.members r₀ = none)
    (hT : TyP E m₀.arity [] m₀.mtype (.sort u₀)) :
    MemberSortP (extendEnv E r₀ m₀) :=
  fun r m hres => by
    have hext := members_extend_preserved (m := m₀) hfresh
    by_cases hrr : r = r₀
    · subst hrr
      simp only [extendEnv, if_pos rfl] at hres
      cases hres
      exact ⟨u₀, TyP.ewk E (extendEnv E r m₀) m₀.arity [] m₀.mtype (.sort u₀) hext hT⟩
    · simp only [extendEnv, if_neg hrr] at hres
      let ⟨u, h₀⟩ := hm r m hres
      exact ⟨u, TyP.ewk E (extendEnv E r₀ m₀) m.arity [] m.mtype (.sort u) hext h₀⟩

/-- Enrich an inductive group's member chain `GroupMembersT S E₁ ms E'` into `GroupMembersP E₁ ms E'`.
    The stage environments `E₁` never carry an `EnvWfT`, so the per-stage `hlet` is discharged
    from a carried `CvWalkHyp E₁`, extended member-by-member by `cvWalkHyp_cons`. -/
def enrichGroupMembersT {S : ResolvedEnv} :
    {E₁ : ResolvedEnv} → {ms : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    CvWalkHyp E₁ → MemberSortP E₁ → GroupMembersT S E₁ ms E' → GroupMembersP E₁ ms E'
  | E₁, _, _, _, _, .nil _ => .nil E₁
  | E₁, _, _, hw₁, hm₁,
      .cons _ r m rest E' hfresh hnobody hclT _ hlvlB _ harities _ _ u hT _ _ hrest =>
      let hTP := enrichHasTyT hw₁.closed (envExt_refl E₁) hm₁
        (letCtxConvP_of_cvWalkHyp hw₁) (.nil E₁ m.arity) hT
      let hw₂ : CvWalkHyp (extendEnv E₁ r m) :=
        cvWalkHyp_cons hw₁ hfresh hnobody hclT hlvlB harities
      let hm₂ : MemberSortP (extendEnv E₁ r m) :=
        memberSortP_extendEnv hm₁ hfresh hTP
      .cons E₁ r m rest E' hfresh hnobody u hTP
        (enrichGroupMembersT hw₂ hm₂ hrest)

/-- Enrich a plain environment derivation `EnvWfT E` into `EnvWfP E`. -/
noncomputable def enrichEnvWfT :
    {E : ResolvedEnv} → EnvWfT E → EnvWfP E
  | _, .empty => .empty
  | _, .axiom (arity := arity) E r A u hE hfresh hA _ _ =>
      let hEP := enrichEnvWfT hE
      let hclE := envClosed_of_envWfT hE
      let hmE := memberSortP_of_envWfP hEP
      let hAP := enrichHasTyT hclE (envExt_refl E) hmE
        (letCtxConvP_of_envWfT hE) (.nil E arity) hA
      .axiom E r A u hEP hfresh hAP
  | _, .definition E r A v u hE hfresh hA hv _ _ _ _ =>
      let hEP := enrichEnvWfT hE
      let hclE := envClosed_of_envWfT hE
      let hmE := memberSortP_of_envWfP hEP
      let hAP := enrichHasTyT hclE (envExt_refl E) hmE
        (letCtxConvP_of_envWfT hE) (.nil E 0) hA
      let hvP := enrichHasTyT hclE (envExt_refl E) hmE
        (letCtxConvP_of_envWfT hE) (.nil E 0) hv
      .definition E r A v u hEP hfresh hAP hvP
  | _, .thm E r A p hE hfresh hA hp _ _ _ _ =>
      let hEP := enrichEnvWfT hE
      let hclE := envClosed_of_envWfT hE
      let hmE := memberSortP_of_envWfP hEP
      let hAP := enrichHasTyT hclE (envExt_refl E) hmE
        (letCtxConvP_of_envWfT hE) (.nil E 0) hA
      let hpP := enrichHasTyT hclE (envExt_refl E) hmE
        (letCtxConvP_of_envWfT hE) (.nil E 0) hp
      .thm E r A p hEP hfresh hAP hpP
  | _, .opaque E r A v u hE hfresh hA hv _ _ _ _ =>
      let hEP := enrichEnvWfT hE
      let hclE := envClosed_of_envWfT hE
      let hmE := memberSortP_of_envWfP hEP
      let hAP := enrichHasTyT hclE (envExt_refl E) hmE
        (letCtxConvP_of_envWfT hE) (.nil E 0) hA
      let hvP := enrichHasTyT hclE (envExt_refl E) hmE
        (letCtxConvP_of_envWfT hE) (.nil E 0) hv
      .opaque E r A v u hEP hfresh hAP hvP
  | _, .group E _ _ _ _ _ E' hE _ _ _ hmem =>
      let hEP := enrichEnvWfT hE
      let hmE := memberSortP_of_envWfP hEP
      .group E _ E' hEP
        (enrichGroupMembersT (cvWalkHyp_of_envWfT hE) hmE hmem)

/-- `EnvWfT E` supplies `MemberSortP E` via `enrichEnvWfT` and `memberSortP_of_envWfP`. -/
noncomputable def memberSortP_of_envWfT {E : ResolvedEnv} (hEnv : EnvWfT E) : MemberSortP E :=
  memberSortP_of_envWfP (enrichEnvWfT hEnv)

/-- `EnvWfT`-fronted context enrichment `CtxWfT E n Γ → CtxP E n Γ`. -/
noncomputable def enrichCtxWfT_of_envWfT
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    CtxP E n Γ :=
  enrichCtxWfT (envClosed_of_envWfT hEnv) (envExt_refl E)
    (memberSortP_of_envWfT hEnv) (letCtxConvP_of_envWfT hEnv) hΓ

/-- `EnvWfT`-fronted typing enrichment `HasTyT E n Γ e T → TyP E n Γ e T`. -/
noncomputable def enrichHasTyT_of_envWfT
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e T : Expr Nat} (D : HasTyT E n Γ e T) : TyP E n Γ e T :=
  enrichHasTyT (envClosed_of_envWfT hEnv) (envExt_refl E)
    (memberSortP_of_envWfT hEnv) (letCtxConvP_of_envWfT hEnv)
    (enrichCtxWfT_of_envWfT hEnv hΓ) D

/-- `EnvWfT`-fronted conversion enrichment `ConvT E n Γ a b T → CvP E n Γ a b T`. -/
noncomputable def enrichConvT_of_envWfT
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (h : ConvT E n Γ a b T) : CvP E n Γ a b T :=
  enrichConvT (envClosed_of_envWfT hEnv) (envExt_refl E)
    (memberSortP_of_envWfT hEnv) (letCtxConvP_of_envWfT hEnv)
    (enrichCtxWfT_of_envWfT hEnv hΓ) h

/-- `EnvWfT`-fronted type-conversion enrichment `TyConvT E n Γ A B → TyCvP E n Γ A B`. -/
noncomputable def enrichTyConvT_of_envWfT
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A B : Expr Nat} (h : TyConvT E n Γ A B) : TyCvP E n Γ A B :=
  enrichTyConvT (envClosed_of_envWfT hEnv) (envExt_refl E)
    (memberSortP_of_envWfT hEnv) (letCtxConvP_of_envWfT hEnv)
    (enrichCtxWfT_of_envWfT hEnv hΓ) h

/-- `EnvWfT`-fronted `TypedRowsWf.sortRow` bridge (`TyConvT E n Γ (.sort u) (.sort v) → eqN u v`)
    via `enrichTyConvT_of_envWfT` and `sortRow_of_tyCvP_esChain_id`, with zero `hUniq` / `DT012T`. -/
theorem sortRow_of_tyConvT_envWfT {tbl : List CRule} (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} (hEnv : EnvWfT E) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u v : Level} (h : TyConvT E n Γ (.sort u) (.sort v))
    (ρ : List Disp)
    (hc : TyCvP.ESChain tbl id ρ (enrichTyConvT_of_envWfT hEnv hΓ h)
      (TyP.sort E n Γ u (.succ u) (eqN_refl _))
      (TyP.sort E n Γ v (.succ v) (eqN_refl _))) :
    eqN u v :=
  sortRow_of_tyCvP_esChain_id hW (enrichTyConvT_of_envWfT hEnv hΓ h) ρ hc

end Rcic.Syn

#print axioms Rcic.Syn.iotaPack_of_envWfT
#print axioms Rcic.Syn.tyCctxAt_of_envWfT
#print axioms Rcic.Syn.piInv_of_envWfT
#print axioms Rcic.Syn.piInv_here_of_envWfT
#print axioms Rcic.Syn.cctxAtOne
#print axioms Rcic.Syn.assumpPref_cctxAtOne
#print axioms Rcic.Syn.piCctxP
#print axioms Rcic.Syn.assumpPref_piCctxP
#print axioms Rcic.Syn.assumpPref_piWk
#print axioms Rcic.Syn.assumpPref_piLinst
#print axioms Rcic.Syn.assumpPref_piEsub
#print axioms Rcic.Syn.assumpPref_piLsub
#print axioms Rcic.Syn.piInvP
#print axioms Rcic.Syn.piInvP_here
#print axioms Rcic.Syn.assumpPref_piInvP
#print axioms Rcic.Syn.assumpPref_piInvP_here
#print axioms Rcic.Syn.ctxP_lookupType_sort
#print axioms Rcic.Syn.assumpPref_ctxP_lookupType_sort
#print axioms Rcic.Syn.ctxP_lookupValue_ty
#print axioms Rcic.Syn.assumpPref_ctxP_lookupValue_ty
#print axioms Rcic.Syn.memberSortP_of_envWfP
#print axioms Rcic.Syn.instMemberSortP
#print axioms Rcic.Syn.assumpPref_instMemberSortP
#print axioms Rcic.Syn.betaLeftP
#print axioms Rcic.Syn.assumpPref_betaLeftP
#print axioms Rcic.Syn.appRightP
#print axioms Rcic.Syn.assumpPref_appRightP
#print axioms Rcic.Syn.lamRightP
#print axioms Rcic.Syn.assumpPref_lamRightP
#print axioms Rcic.Syn.piRightP
#print axioms Rcic.Syn.assumpPref_piRightP
#print axioms Rcic.Syn.sortsRightP
#print axioms Rcic.Syn.assumpPref_sortsRightP
#print axioms Rcic.Syn.constsRightP
#print axioms Rcic.Syn.assumpPref_constsRightP
#print axioms Rcic.Syn.etaLeftP
#print axioms Rcic.Syn.assumpPref_etaLeftP
#print axioms Rcic.Syn.cvP_inst0_sortCongrLet
#print axioms Rcic.Syn.assumpPref_cvP_inst0_sortCongrLet
#print axioms Rcic.Syn.cvpLetInline0
#print axioms Rcic.Syn.assumpPref_cvpLetInline0
#print axioms Rcic.Syn.letRightP
#print axioms Rcic.Syn.assumpPref_letRightP
#print axioms Rcic.Syn.enrichHasTyT
#print axioms Rcic.Syn.enrichConvT
#print axioms Rcic.Syn.assumpPref_enrichHasTyT
#print axioms Rcic.Syn.assumpPref_enrichConvT
#print axioms Rcic.Syn.enrichTyConvT
#print axioms Rcic.Syn.enrichCtxWfT
#print axioms Rcic.Syn.assumpPref_enrichCtxWfT
#print axioms Rcic.Syn.sortRow_of_tyConvT_esChain_id
#print axioms Rcic.Syn.sortRow_of_convT_es_cl_id
#print axioms Rcic.Syn.memberSortP_extendEnv
#print axioms Rcic.Syn.enrichGroupMembersT
#print axioms Rcic.Syn.enrichEnvWfT
#print axioms Rcic.Syn.memberSortP_of_envWfT
#print axioms Rcic.Syn.enrichCtxWfT_of_envWfT
#print axioms Rcic.Syn.enrichHasTyT_of_envWfT
#print axioms Rcic.Syn.enrichConvT_of_envWfT
#print axioms Rcic.Syn.enrichTyConvT_of_envWfT
#print axioms Rcic.Syn.sortRow_of_tyConvT_envWfT

