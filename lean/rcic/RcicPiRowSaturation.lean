/-
  RcicPiRowSaturation.lean — piRow wall, piece E
  (research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md §7.1–§7.2):
  a full application of an admitted inductive family is *saturated* —
  its argument count equals the stored telescope arity.

  Route (the scoped one the task names, not the global `AllBelow`):
  `AllBelowScoped` + `ScopedCtx` + the guarded extractors
  `es_of_allBelowScoped` / `cl_of_allBelowScoped` of
  `RcicSynBelowScoped.lean`. The chain query `ESChain` is supplied by
  the landed `esChain_of_allBelowScoped` (`RcicSynBelowCToRows`, #7491)
  over the landed `TyCvP.AllAP` receipt — itself discharged by the
  landed `enrichTyConvT_of_envWfT_allAP` + `memberSortP_of_envWfT_ap`
  (`RcicSynMSAP`, L-MSAP). This module adds no AP predicate, no
  ESChain producer, and no enrich-AP wrappers of its own.

  New layers, all composition-only:

    * `TyCvP.endpoints_assumpPref` — the `endpoints` (RcicSynSepUnique)
      derivations' `TyP.AssumpPref` receipts under `c.AllAP`. Needed for
      the *left* endpoint (`pi ≁ sort`); the landed `endpointsR`
      exposes only the right endpoint.
    * `not_tyCvP_sort_pi`/`not_tyCvP_pi_sort`/`not_tyConvT_sort_pi`/
      `not_tyConvT_pi_sort` under `AllBelowScoped`, built on the landed
      `esChain_of_allBelowScoped`.
    * `famApp_saturated_of_piRow_scoped`: for a real member lookup
      `E.members r = some m` at `m.mclass = .inductiveM` whose stored
      type is `policyPi doms (.sort u)`, any typing of
      `foldApps (.const r ls) xs` at `.sort w` has `xs.length =
      doms.length` — under- and over-application are each killed by the
      scoped sort–Π separation.

  `spineInvAux`/`hasTyT_spineInv_rows` (RcicIotaSRRowsLemmas)
  take the standalone `PiRowField E n` — the theorem's
  `hprow : PiRowField E n` hypothesis *is* the explicit `piRow`
  hypothesis of the brief — the standalone field, not the
  `TypedRowsWf` bundle (whose `famAppRow` is the downstream goal this
  theorem constructs), matching spec §7.1's shape.

  No sorry; axioms ⊆ {propext, Quot.sound}.
-/

import rcic.RcicSynBelowScoped
import rcic.RcicSynWalkLetAP
import rcic.RcicSynBelowCToRows
import rcic.RcicSynMSAP
import rcic.RcicIotaSRRowsLemmas
import rcic.RcicTypedInvert

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 — `endpoints` AP under `AllAP` -/

/-- `endpoints`' output derivations are AP when the chain is `AllAP`
    (landed `RcicSynBelowCToRows`): the `of` case's endpoints are the
    `CvP`'s own dl/dr; the `trans` case routes through the IHs. The two
    mixed casts (`h₁ ▸ dL`, `h₂ ▸ dR`) are discharged by casing the
    index equation. Same `revert`/`cases`/`intro`/`injection` idiom as
    `eqN_of_tyCvP_endpoints`. `endpointsR` covers the right endpoint;
    this supplies the left one `pi ≁ sort` needs. -/
theorem TyCvP.endpoints_assumpPref {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    ∀ {A B : Expr Nat} (c : TyCvP E n Γ A B), c.AllAP →
      ∀ {uL uR : Level} {dL : TyP E n Γ A (.sort uL)} {dR : TyP E n Γ B (.sort uR)},
        c.endpoints = .inr ⟨uL, uR, dL, dR⟩ → dL.AssumpPref ∧ dR.AssumpPref := by
  intro A B c
  induction c with
  | refl A =>
      intro hAP uL uR dL dR he
      exact PSum.noConfusion he
  | of A B u h =>
      intro hAP uL uR dL dR he
      injection he with hsig
      cases hsig
      exact ⟨assumpPref_dl hAP, assumpPref_dr hAP⟩
  | trans A B C c₁ c₂ ih₁ ih₂ =>
      intro hAP uL uR dL dR he
      unfold TyCvP.endpoints at he
      revert he
      cases he₁ : c₁.endpoints with
      | inl h₁ =>
          cases he₂ : c₂.endpoints with
          | inl h₂ =>
              intro he
              exact PSum.noConfusion he
          | inr p₂ =>
              rcases p₂ with ⟨uL₂, uR₂, dL₂, dR₂⟩
              intro he
              injection he with hsig
              cases hsig
              cases h₁
              obtain ⟨hAdL₂, hAdR₂⟩ := ih₂ hAP.2 he₂
              exact ⟨hAdL₂, hAdR₂⟩
      | inr p₁ =>
          rcases p₁ with ⟨uL₁, uR₁, dL₁, dR₁⟩
          cases he₂ : c₂.endpoints with
          | inl h₂ =>
              intro he
              injection he with hsig
              cases hsig
              cases h₂
              obtain ⟨hAdL₁, hAdR₁⟩ := ih₁ hAP.1 he₁
              exact ⟨hAdL₁, hAdR₁⟩
          | inr p₂ =>
              rcases p₂ with ⟨uL₂, uR₂, dL₂, dR₂⟩
              intro he
              injection he with hsig
              cases hsig
              obtain ⟨hAdL₁, _⟩ := ih₁ hAP.1 he₁
              obtain ⟨_, hAdR₂⟩ := ih₂ hAP.2 he₂
              exact ⟨hAdL₁, hAdR₂⟩


/-! ## §2 — scoped sort–Π separation -/

/-- `sort ≁ pi` on `TyCvP` under `AllBelowScoped`: identical to
    `not_tyCvP_sort_pi_of_allBelow` with the scoped `ESChain`/`ConvMod`
    supply — the landed `AllAP` on the chain and the `endpoints`
    derivations is what makes the guarded extractor route go through. -/
theorem not_tyCvP_sort_pi_of_allBelowScoped {Eₐ E : ResolvedEnv}
    {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped Eₐ Aw tbl) (hW : TableWF tbl)
    {n : Nat} {Γ : LCtx} {σ : Level → Level}
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ)
    {u : Level} {A B : Expr Nat} {c : TyCvP E n Γ (.sort u) (.pi A B)}
    (hc : c.AllAP) : False := by
  cases he : c.endpoints with
  | inl h => exact Expr.noConfusion h
  | inr p =>
      rcases p with ⟨uL, uR, dL, dR⟩
      obtain ⟨hAdL, hAdR⟩ := c.endpoints_assumpPref hc he
      let P := piInvP_here dR
      let dPi := canonPiOfTyP dR
      let dSort := TyP.sort E n Γ u (.succ u) (eqN_refl _)
      have hAdPi : (canonPiOfTyP dR).AssumpPref := assumpPref_piInvP_here hAdR
      have hchain := esChain_of_allBelowScoped hBel S hσ c hc dSort trivial dPi hAdPi
      have hconv : ConvMod (EStep tbl) LvlEq (.sort (σ u))
          (.pi (P.hA.eps σ (S.can σ))
            (piSlot (levelIsZero (σ P.u)) (P.hB.eps σ (binderDisp (levelIsZero (σ P.u)) :: (S.can σ))))) := by
        simpa only [dSort, dPi, canonPiOfTyP, eps_sort, eps_pi_clause] using
          convMod_of_tyCvP_esChain hchain
      exact not_convE_sort_pi_wf hW (σ u) (P.hA.eps σ (S.can σ))
        (piSlot (levelIsZero (σ P.u)) (P.hB.eps σ (binderDisp (levelIsZero (σ P.u)) :: (S.can σ)))) hconv

/-- `pi ≁ sort` on `TyCvP` under `AllBelowScoped` — the mirror image. -/
theorem not_tyCvP_pi_sort_of_allBelowScoped {Eₐ E : ResolvedEnv}
    {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped Eₐ Aw tbl) (hW : TableWF tbl)
    {n : Nat} {Γ : LCtx} {σ : Level → Level}
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ)
    {u : Level} {A B : Expr Nat} {c : TyCvP E n Γ (.pi A B) (.sort u)}
    (hc : c.AllAP) : False := by
  cases he : c.endpoints with
  | inl h => exact Expr.noConfusion h
  | inr p =>
      rcases p with ⟨uL, uR, dL, dR⟩
      obtain ⟨hAdL, hAdR⟩ := c.endpoints_assumpPref hc he
      let P := piInvP_here dL
      let dPi := canonPiOfTyP dL
      let dSort := TyP.sort E n Γ u (.succ u) (eqN_refl _)
      have hAdPi : (canonPiOfTyP dL).AssumpPref := assumpPref_piInvP_here hAdL
      have hchain := esChain_of_allBelowScoped hBel S hσ c hc dPi hAdPi dSort trivial
      have hconv : ConvMod (EStep tbl) LvlEq
          (.pi (P.hA.eps σ (S.can σ))
            (piSlot (levelIsZero (σ P.u)) (P.hB.eps σ (binderDisp (levelIsZero (σ P.u)) :: (S.can σ)))))
          (.sort (σ u)) := by
        simpa only [dPi, dSort, canonPiOfTyP, eps_sort, eps_pi_clause] using
          convMod_of_tyCvP_esChain hchain
      exact not_convE_pi_sort_wf hW (P.hA.eps σ (S.can σ))
        (piSlot (levelIsZero (σ P.u)) (P.hB.eps σ (binderDisp (levelIsZero (σ P.u)) :: (S.can σ))))
        (σ u) hconv

/-- `sort ≁ pi` on plain `TyConvT` under `AllBelowScoped` — enrich the
    conversion, discharge its `AllAP` via the landed
    `enrichTyConvT_of_envWfT_allAP` + `memberSortP_of_envWfT_ap`
    (L-MSAP), apply the `TyCvP` lemma. -/
theorem not_tyConvT_sort_pi_of_allBelowScoped {Eₐ E : ResolvedEnv}
    {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped Eₐ Aw tbl) (hW : TableWF tbl)
    {n : Nat} {Γ : LCtx} {σ : Level → Level}
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ)
    {u : Level} {A B : Expr Nat} (hc : TyConvT E n Γ (.sort u) (.pi A B)) : False :=
  not_tyCvP_sort_pi_of_allBelowScoped hBel hW S hσ
    (c := enrichTyConvT_of_envWfT S.env S.ctx hc)
    (enrichTyConvT_of_envWfT_allAP S.env (memberSortP_of_envWfT_ap S.env) S.ctx hc)

/-- `pi ≁ sort` on plain `TyConvT` under `AllBelowScoped`. -/
theorem not_tyConvT_pi_sort_of_allBelowScoped {Eₐ E : ResolvedEnv}
    {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped Eₐ Aw tbl) (hW : TableWF tbl)
    {n : Nat} {Γ : LCtx} {σ : Level → Level}
    (S : ScopedCtx Eₐ E n Γ) (hσ : LevelHom σ)
    {u : Level} {A B : Expr Nat} (hc : TyConvT E n Γ (.pi A B) (.sort u)) : False :=
  not_tyCvP_pi_sort_of_allBelowScoped hBel hW S hσ
    (c := enrichTyConvT_of_envWfT S.env S.ctx hc)
    (enrichTyConvT_of_envWfT_allAP S.env (memberSortP_of_envWfT_ap S.env) S.ctx hc)


/-! ## §3 — application-spine helpers -/

/-- A typed application spine peels back to a typing of its head
    function: `hasTyTInv_app` at each `.app` layer. -/
theorem hasTyT_foldApps_right {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    ∀ {f : Expr Nat} {bs : List (Expr Nat)} {T : Expr Nat},
      HasTyT E n Γ (foldApps f bs) T → ∃ T', Nonempty (HasTyT E n Γ f T')
  | f, [], _, h => ⟨_, ⟨h⟩⟩
  | f, b :: bs, _, h => by
      obtain ⟨T', ⟨hT'⟩⟩ := hasTyT_foldApps_right (f := .app f b) h
      obtain ⟨A, B, hf, _, _⟩ := hasTyTInv_app hT' rfl
      exact ⟨.pi A B, ⟨hf⟩⟩

/-- A strict suffix of a typed spine's arguments peels to a typing of
    the strict prefix's head at a Π. Used in the over-application arm:
    `xs = take k xs ++ x' :: rest`, and `foldApps const xs` types
    `foldApps (const-prefix) x'` — invert once for the `.app`'s function. -/
theorem hasTyT_foldApps_prefix_pi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f : Expr Nat} {bs : List (Expr Nat)} {T : Expr Nat}
    (h : HasTyT E n Γ (foldApps f bs) T)
    {x' : Expr Nat} {rest : List (Expr Nat)}
    (hrest : bs = x' :: rest) :
    ∃ A B, Nonempty (HasTyT E n Γ f (.pi A B)) := by
  subst hrest
  obtain ⟨T', ⟨hT'⟩⟩ := hasTyT_foldApps_right (f := .app f x') h
  obtain ⟨A, B, hf, _, _⟩ := hasTyTInv_app hT' rfl
  exact ⟨A, B, ⟨hf⟩⟩


/-! ## §4 — famAppRow saturation under the scoped route -/

/-- **Piece E**: given the explicit `piRow` hypothesis as the standalone
    `PiRowField E n` (`hasTyT_spineInv_rows` reads only that field —
    spec §7.1; the full `TypedRowsWf` bundle would circularly include
    `famAppRow`, the very component this theorem builds) and
    the guarded scoped sort–Π separation route
    (`AllBelowScoped`/`ScopedCtx`/`es_of_allBelowScoped`), a full
    application of an admitted `.inductiveM` family typed at a sort is
    saturated: `xs.length = doms.length`.

    *Under-application* (`xs.length < doms.length`): `spineInvAux` at
    `doms.take xs.length` leaves a residual `policyPi (doms.drop
    xs.length) (.sort u)` — a real `.pi` — convertible to `.sort w`,
    killed by `not_tyConvT_pi_sort_of_allBelowScoped`.
    *Over-application* (`xs.length > doms.length`): the strict prefix
    `take doms.length xs` types at `.pi A B` while `spineInvAux`
    converts it to `instPrefix … (.sort u) = .sort u` — killed by
    `not_tyConvT_sort_pi_of_allBelowScoped`. -/
theorem famApp_saturated_of_piRow_scoped {Eₐ E : ResolvedEnv}
    {Aw : Nat → Nat} {tbl : List CRule}
    (hBel : AllBelowScoped Eₐ Aw tbl) (hW : TableWF tbl)
    {n : Nat} {Γ : LCtx} (S : ScopedCtx Eₐ E n Γ)
    (hprow : PiRowField E n)
    {r : Nat} {m : CheckedMember} {ls : List Level}
    (hm : E.members r = some m) (_hind : m.mclass = .inductiveM)
    {doms : List (Expr Nat)} {u : Level}
    (hpi : instantiateLevels ls m.mtype = policyPi doms (.sort u))
    {xs : List (Expr Nat)} {w : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) :
    xs.length = doms.length := by
  rcases Nat.lt_trichotomy xs.length doms.length with hlt | heq | hgt
  · -- under-application: residual Π convertible to a sort
    exfalso
    have hne : doms.drop xs.length ≠ [] := fun hnil =>
      Nat.not_le_of_gt hlt (List.drop_eq_nil_iff.mp hnil)
    obtain ⟨D, rest, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hpi' : instantiateLevels ls m.mtype =
        policyPi (doms.take xs.length) (policyPi (doms.drop xs.length) (.sort u)) := by
      rw [← List.take_append_drop xs.length doms] at hpi
      rw [hpi, policyPi_append]
    have hlen' : (doms.take xs.length).length = xs.length := by
      rw [List.length_take]
      first
        | exact Nat.min_eq_right (Nat.le_of_lt hlt)
        | exact Nat.min_eq_left (Nat.le_of_lt hlt)
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows S.env hprow S.ctx hm hpi' xs hlen' hty
    rw [hrest] at hconv
    simp only [policyPi] at hconv
    rw [instPrefix_pi] at hconv
    exact not_tyConvT_pi_sort_of_allBelowScoped hBel hW S levelHom_id hconv
  · exact heq
  · -- over-application: the prefix types at a sort but is used at a Π
    exfalso
    have hne : xs.drop doms.length ≠ [] := fun hnil =>
      Nat.not_le_of_gt hgt (List.drop_eq_nil_iff.mp hnil)
    obtain ⟨x', rest, hrest⟩ := List.exists_cons_of_ne_nil hne
    have hsplit : foldApps (.const r ls) xs =
        foldApps (foldApps (.const r ls) (xs.take doms.length)) (xs.drop doms.length) :=
      calc foldApps (.const r ls) xs
          = foldApps (.const r ls) (xs.take doms.length ++ xs.drop doms.length) := by
              rw [List.take_append_drop]
        _ = foldApps (foldApps (.const r ls) (xs.take doms.length)) (xs.drop doms.length) :=
            foldApps_append _ _ _
    obtain ⟨A, B, ⟨hf⟩⟩ := hasTyT_foldApps_prefix_pi
      (f := foldApps (.const r ls) (xs.take doms.length))
      (hsplit ▸ hty) hrest
    have hlen' : doms.length = (xs.take doms.length).length := by
      rw [List.length_take]
      first
        | exact (Nat.min_eq_right (Nat.le_of_lt hgt)).symm
        | exact (Nat.min_eq_left (Nat.le_of_lt hgt)).symm
    obtain ⟨_, _, _, hconv⟩ := hasTyT_spineInv_rows S.env hprow S.ctx hm hpi
      (xs.take doms.length) hlen' hf
    rw [instPrefix_sort] at hconv
    exact not_tyConvT_sort_pi_of_allBelowScoped hBel hW S levelHom_id hconv

end Rcic.Syn

#print axioms Rcic.Syn.TyCvP.endpoints_assumpPref
#print axioms Rcic.Syn.not_tyCvP_sort_pi_of_allBelowScoped
#print axioms Rcic.Syn.not_tyCvP_pi_sort_of_allBelowScoped
#print axioms Rcic.Syn.not_tyConvT_sort_pi_of_allBelowScoped
#print axioms Rcic.Syn.not_tyConvT_pi_sort_of_allBelowScoped
#print axioms Rcic.Syn.hasTyT_foldApps_right
#print axioms Rcic.Syn.hasTyT_foldApps_prefix_pi
#print axioms Rcic.Syn.famApp_saturated_of_piRow_scoped
