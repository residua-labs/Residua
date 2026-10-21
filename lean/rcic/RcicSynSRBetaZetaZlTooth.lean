import rcic.RcicSynSRBetaZetaLocal
import rcic.RcicSynP2Shared
import rcic.RcicERScope1

/-!
# The `zetaLocal_res_conv` tooth: on-cone σ, off-cone ρ — a supply-route artifact

Census row 4's `zetaLocal_res_conv` wall (`ZetaLocalResConvWall`,
`RcicSynSRBetaZetaLocal`) was refuted at the `zetaCtx` fixture with
`σ := id`, `ρ := [.keep]`. Classification, kernel-checked:

* **σ-side ON-CONE:** the refutation's `σ = id` IS a `LevelHom`, and the wall
  restated with `σ` restricted to `LevelHom σ` (`ZetaLocalResConvWallHom`)
  is still refuted at the same fixture — the tooth does not die under the
  cone's own σ-restriction (`zl_res_conv_refuted_hom`).
* **ρ-side OFF the routed cone:** the failing display `[.keep]` has a `.keep`
  at the let-binding position of `zetaCtx`. Every display the cone
  (`Demand` → `RoutedDisp`) can route at a context has no `.keep` at any
  let-binding position (`routedDisp_let_noKeep`, by derivation induction);
  `zetaCtx`'s single entry is a let-binding, so `¬ RoutedDisp id emptyEnv 0
  zetaCtx [.keep]` (`zl_rho_not_routed`) — the refutation site is a
  supply-route (arbitrary-ρ port) artifact.
* **The cone's own disposition holds:** at the canonical Entry disposition
  `(zetaCtxP emptyEnv 0).disp id = [.inline (.sort .zero)]` the wall's
  `ConvMod` goal holds (`zl_res_conv_canon`), so at this fixture the
  value-is-a-sort tooth vanishes exactly where the field's demand evaluates.
  `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 position helpers -/

theorem removeAt_getElem?_lt :
    ∀ (c : Nat) (ρ : List Disp) (j : Nat), j < c → (removeAt ρ c)[j]? = ρ[j]?
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | _ + 1, [], _, _ => rfl
  | _ + 1, x :: ρ', 0, _ => by
      show (x :: removeAt ρ' _)[0]? = (x :: ρ')[0]?
      simp only [List.getElem?_cons_zero]
  | c + 1, x :: ρ', j + 1, hj => by
      show (x :: removeAt ρ' c)[j + 1]? = (x :: ρ')[j + 1]?
      simp only [List.getElem?_cons_succ]
      exact removeAt_getElem?_lt c ρ' j (Nat.lt_of_succ_lt_succ hj)

theorem removeAt_getElem?_ge :
    ∀ (c : Nat) (ρ : List Disp) (j : Nat), c ≤ j → (removeAt ρ c)[j]? = ρ[j + 1]?
  | _, [], _, _ => rfl
  | 0, x :: ρ', j, _ => by
      show ρ'[j]? = (x :: ρ')[j + 1]?
      simp only [List.getElem?_cons_succ]
  | _ + 1, _ :: _, 0, hj => absurd hj (Nat.not_succ_le_zero _)
  | c + 1, x :: ρ', j + 1, hj => by
      show (x :: removeAt ρ' c)[j + 1]? = (x :: ρ')[j + 1 + 1]?
      simp only [List.getElem?_cons_succ, Nat.add_assoc]
      exact removeAt_getElem?_ge c ρ' j (Nat.le_of_succ_le_succ hj)

theorem insertDisp_getElem?_lt {d : Disp} :
    ∀ (ρ : List Disp) (j j' : Nat), j' < j → j ≤ ρ.length →
      (insertDisp d j ρ)[j']? = ρ[j']?
  | [], 0, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | [], _ + 1, _, _, hlen => absurd hlen (by simp)
  | _ :: _, 0, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | x :: ρ', _ + 1, 0, _, _ => by
      simp only [insertDisp, List.getElem?_cons_zero]
  | x :: ρ', j + 1, j' + 1, hj, hlen => by
      show (x :: insertDisp _ j ρ')[j' + 1]? = (x :: ρ')[j' + 1]?
      simp only [List.getElem?_cons_succ]
      exact insertDisp_getElem?_lt ρ' j j' (Nat.lt_of_succ_lt_succ hj)
        (by simp only [List.length_cons] at hlen; omega)

theorem insertDisp_getElem?_ge {d : Disp} :
    ∀ (ρ : List Disp) (j k : Nat), j ≤ k → j < ρ.length →
      (insertDisp d j ρ)[k + 1]? = ρ[k]?
  | [], _, _, _, hlen => absurd hlen (by simp)
  | x :: ρ', 0, k, _, _ => by
      show (d :: x :: ρ')[k + 1]? = (x :: ρ')[k]?
      simp only [List.getElem?_cons_succ]
  | _ :: _, _ + 1, 0, hj, _ => absurd hj (Nat.not_succ_le_zero _)
  | x :: ρ', j + 1, k + 1, hj, hlen => by
      show (x :: insertDisp d j ρ')[k + 2]? = (x :: ρ')[k + 1]?
      simp only [List.getElem?_cons_succ]
      exact insertDisp_getElem?_ge ρ' j k (Nat.le_of_succ_le_succ hj)
        (by simp only [List.length_cons] at hlen; omega)

/-! ## §2 context-side helpers: length coherence of `CtxP.disp` -/

/-- The canonical disposition is exactly as long as its context. -/
theorem ctxP_disp_length {σ : Level → Level} {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → (C : CtxP E n Γ) → (C.disp σ).length = Γ.length
  | _, .nil _ _ => rfl
  | _, .assumption _ _ _ _ u hC _ => by
      simp only [CtxP.disp]
      cases levelIsZero (σ u) <;>
        exact congrArg Nat.succ (ctxP_disp_length hC)
  | _, .letBinding _ _ _ _ _ _ hC _ _ =>
      congrArg Nat.succ (ctxP_disp_length hC)

/-! ## §3 context-kind helpers -/

theorem removeAt_length_drop :
    ∀ (c : Nat) (ρ : List Disp), ρ.length ≤ (removeAt ρ c).length + 1
  | _, [] => by simp
  | 0, x :: ρ => by
      show (x :: ρ).length ≤ ρ.length + 1
      simp only [List.length_cons]
      omega
  | c + 1, x :: ρ => by
      show (x :: ρ).length ≤ (x :: removeAt ρ c).length + 1
      have ih := removeAt_length_drop c ρ
      simp only [List.length_cons] at ih ⊢
      omega

theorem insertDisp_length (d : Disp) :
    ∀ (j : Nat) (ρ : List Disp), (insertDisp d j ρ).length = ρ.length + 1
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | j + 1, x :: ρ => by
      show (x :: insertDisp d j ρ).length = (x :: ρ).length + 1
      simp only [List.length_cons]
      exact congrArg Nat.succ (insertDisp_length d j ρ)

theorem substRemove_length_drop (v : Expr Nat) :
    ∀ (j : Nat) (Γ : LCtx), Γ.length ≤ (substRemove v j Γ).length + 1
  | _, [] => by simp
  | 0, x :: Γ => by
      show (x :: Γ).length ≤ Γ.length + 1
      simp only [List.length_cons]
      omega
  | j + 1, x :: Γ => by
      show (x :: Γ).length ≤ (_ :: substRemove v j Γ).length + 1
      have ih := substRemove_length_drop v j Γ
      simp only [List.length_cons] at ih ⊢
      omega

theorem insertAt_letBinding_lt {d : LocalDecl} :
    ∀ (c j : Nat) (Γ : LCtx) (A v : Expr Nat), j < c → Γ[j]? = some (.letBinding A v) →
      ∃ A' v', (insertAt d c Γ)[j]? = some (.letBinding A' v')
  | 0, _, _, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | _ + 1, _, [], _, _, _, hget => by simp at hget
  | c + 1, 0, x :: _, _, _, _, hget => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp only [insertAt, List.getElem?_cons_zero]
      exact ⟨_, _, rfl⟩
  | c + 1, j + 1, x :: Γ, _, _, hj, hget => by
      simp only [List.getElem?_cons_succ] at hget
      simp only [insertAt, List.getElem?_cons_succ]
      exact insertAt_letBinding_lt c j Γ _ _ (Nat.lt_of_succ_lt_succ hj) hget

theorem insertAt_letBinding_ge {d : LocalDecl} :
    ∀ (c j : Nat) (Γ : LCtx) (A v : Expr Nat), c ≤ j → Γ[j]? = some (.letBinding A v) →
      ∃ A' v', (insertAt d c Γ)[j + 1]? = some (.letBinding A' v')
  | 0, _, [], _, _, _, hget => by simp at hget
  | 0, j, x :: _, A, v, _, hget => by
      refine ⟨A, v, ?_⟩
      simp only [insertAt, List.getElem?_cons_succ]
      exact hget
  | c + 1, _, [], _, _, _, hget => by simp at hget
  | c + 1, 0, x :: _, _, _, hj, hget => absurd hj (Nat.not_succ_le_zero _)
  | c + 1, j + 1, x :: Γ, _, _, hj, hget => by
      simp only [List.getElem?_cons_succ] at hget
      simp only [insertAt, List.getElem?_cons_succ]
      exact insertAt_letBinding_ge c j Γ _ _ (Nat.le_of_succ_le_succ hj) hget

theorem substRemove_letBinding_lt {v' : Expr Nat} :
    ∀ (j j' : Nat) (Γ : LCtx) (A v : Expr Nat), j' < j → Γ[j']? = some (.letBinding A v) →
      ∃ A' v'', (substRemove v' j Γ)[j']? = some (.letBinding A' v'')
  | _, _, [], _, _, _, hget => by simp at hget
  | 0, _, _, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | j + 1, 0, x :: _, _, _, _, hget => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp only [substRemove, List.getElem?_cons_zero]
      exact ⟨_, _, rfl⟩
  | j + 1, j' + 1, x :: Γ, _, _, hj, hget => by
      simp only [List.getElem?_cons_succ] at hget
      simp only [substRemove, List.getElem?_cons_succ]
      exact substRemove_letBinding_lt j j' Γ _ _ (Nat.lt_of_succ_lt_succ hj) hget

theorem substRemove_letBinding_ge {v' : Expr Nat} :
    ∀ (j k : Nat) (Γ : LCtx) (A v : Expr Nat), j ≤ k → Γ[k + 1]? = some (.letBinding A v) →
      ∃ A' v'', (substRemove v' j Γ)[k]? = some (.letBinding A' v'')
  | _, _, [], _, _, _, hget => by simp at hget
  | 0, k, x :: Γ, A, v, _, hget => by
      simp only [List.getElem?_cons_succ] at hget
      exact ⟨A, v, hget⟩
  | j + 1, 0, _, _, _, hj, _ => absurd hj (Nat.not_succ_le_zero _)
  | j + 1, k + 1, x :: Γ, _, _, hj, hget => by
      simp only [List.getElem?_cons_succ] at hget
      simp only [substRemove, List.getElem?_cons_succ]
      exact substRemove_letBinding_ge j k Γ _ _ (Nat.le_of_succ_le_succ hj) hget

/-! ## §4 the routed-display invariant -/

/-- Canonical dispositions never carry a `.keep` at a let-binding position. -/
theorem ctxP_disp_let_noKeep {σ : Level → Level} {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → (C : CtxP E n Γ) →
      ∀ (j : Nat) (A v : Expr Nat), Γ[j]? = some (.letBinding A v) →
        (C.disp σ)[j]? ≠ some .keep
  | _, .nil _ _ => by
      intro j A v h
      cases j <;> simp at h
  | _, .assumption _ _ _ _ u hC _ => by
      intro j A v h
      cases j with
      | zero => simp at h
      | succ j =>
          simp only [List.getElem?_cons_succ] at h
          cases hb : levelIsZero (σ u) with
          | true =>
              simp only [CtxP.disp, hb, List.getElem?_cons_succ]
              exact ctxP_disp_let_noKeep hC j A v h
          | false =>
              simp only [CtxP.disp, hb, List.getElem?_cons_succ]
              exact ctxP_disp_let_noKeep hC j A v h
  | _, .letBinding _ _ _ _ _ _ hC _ _ => by
      intro j A v h
      cases j with
      | zero => simp [CtxP.disp]
      | succ j =>
          simp only [List.getElem?_cons_succ] at h
          simp only [CtxP.disp, List.getElem?_cons_succ]
          exact ctxP_disp_let_noKeep hC j A v h

/-- Every display the demand cone routes has no `.keep` at any let-binding
    position of its context (and is at least as long as the context). -/
theorem routedDisp_let_noKeep {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} (h : RoutedDisp σ E n Γ ρ) :
    Γ.length ≤ ρ.length ∧
    ∀ (j : Nat) (A v : Expr Nat), Γ[j]? = some (.letBinding A v) → ρ[j]? ≠ some .keep := by
  induction h with
  | @canon σ _ _ Γ C =>
      refine ⟨Nat.le_of_eq (ctxP_disp_length (σ := σ) C).symm, ctxP_disp_let_noKeep (σ := σ) C⟩
  | @assumption σ _ _ _ _ _ _ h _ ih =>
      refine ⟨?_, ?_⟩
      · simp only [List.length_cons]; omega
      · intro j A v hj
        cases j with
        | zero => simp at hj
        | succ j =>
            simp only [List.getElem?_cons_succ] at hj
            simp only [binderDisp]
            cases levelIsZero (σ _) with
            | true => simpa only [List.getElem?_cons_succ] using ih.2 j A v hj
            | false => simpa only [List.getElem?_cons_succ] using ih.2 j A v hj
  | letDrop _ _ _ _ ih =>
      refine ⟨?_, ?_⟩
      · simp only [List.length_cons]; omega
      · intro j A v hj
        cases j with
        | zero => simp
        | succ j =>
            simp only [List.getElem?_cons_succ] at hj
            simpa only [List.getElem?_cons_succ] using ih.2 j A v hj
  | letInline _ _ _ ih =>
      refine ⟨?_, ?_⟩
      · simp only [List.length_cons]; omega
      · intro j A v hj
        cases j with
        | zero => simp
        | succ j =>
            simp only [List.getElem?_cons_succ] at hj
            simpa only [List.getElem?_cons_succ] using ih.2 j A v hj
  | @wk σ _ _ Γ ρ d c _ ih =>
      refine ⟨?_, ?_⟩
      · have h1 := insertAt_length d c Γ
        have h2 := removeAt_length_drop c ρ
        omega
      · intro j A v hj
        have hΓj : j < Γ.length :=
          if hlt : j < Γ.length then hlt
          else by
            have hn : Γ[j]? = none :=
              List.getElem?_eq_none_iff.mpr (Nat.not_lt.mp hlt)
            rw [hn] at hj
            exact Option.noConfusion hj
        have hlen : Γ.length ≤ ρ.length := by
          have h1 := insertAt_length d c Γ
          have h2 := removeAt_length_drop c ρ
          omega
        rcases Nat.lt_or_ge j c with hjl | hjg
        · obtain ⟨A', v', hck⟩ := insertAt_letBinding_lt c j Γ A v hjl hj
          rw [removeAt_getElem?_lt c ρ j hjl]
          exact ih.2 j A' v' hck
        · obtain ⟨A', v', hck⟩ := insertAt_letBinding_ge c j Γ A v hjg hj
          rw [removeAt_getElem?_ge c ρ j hjg]
          exact ih.2 (j + 1) A' v' hck
  | @esub σ _ _ Γ ρl t v j u hget _ _ _ ih =>
      refine ⟨?_, ?_⟩
      · rw [insertDisp_length]
        have h1 := substRemove_length_drop v j Γ
        have := ih.1
        omega
      · intro j' A' v'' hj'
        have hΓj : j < Γ.length := (List.getElem?_eq_some_iff.mp hget).1
        rcases Nat.lt_trichotomy j' j with hlt | heq | hgt
        · obtain ⟨Al, vl, hcl⟩ := substRemove_letBinding_lt j j' Γ A' v'' hlt hj'
          have hρlen : j ≤ ρl.length := by
            have h1 := substRemove_length_drop v j Γ
            have := ih.1
            omega
          rw [insertDisp_getElem?_lt _ j j' hlt hρlen]
          exact ih.2 j' Al vl hcl
        · subst heq
          rw [hget] at hj'
          simp at hj'
        · have hj2 : Γ[(j' - 1) + 1]? = some (.letBinding A' v'') := by
            rw [show j' - 1 + 1 = j' from by omega]
            exact hj'
          obtain ⟨Al, vl, hcl⟩ :=
            substRemove_letBinding_ge j (j' - 1) Γ A' v'' (by omega) hj2
          rcases Nat.lt_or_ge j ρl.length with hjl | hjg2
          · have hje : j' = (j' - 1) + 1 := by omega
            rw [hje, insertDisp_getElem?_ge _ j (j' - 1) (by omega) hjl]
            exact ih.2 (j' - 1) Al vl hcl
          · have hlen2 := insertDisp_length
              (binderDisp (levelIsZero (σ u))) j ρl
            have hnone : (insertDisp (binderDisp (levelIsZero (σ u))) j ρl)[j']? = none :=
              List.getElem?_eq_none_iff.mpr (by omega)
            rw [hnone]
            simp
  | @linst σ E a' n Γ ρ ls _ _ _ ih =>
      refine ⟨?_, ?_⟩
      · have hmaplen : (instLvlsCtx ls Γ).length = Γ.length := by
          unfold instLvlsCtx
          simp
        omega
      · intro j A v hj
        have hmap : (instLvlsCtx ls Γ)[j]? =
            some (.letBinding (instantiateLevels ls A) (instantiateLevels ls v)) := by
          unfold instLvlsCtx
          simp only [List.getElem?_map, hj, instLvlsDecl]
          rfl
        exact ih.2 j _ _ hmap

  | ewk _ _ ih => exact ih
  | cctx _ _ ih =>
      refine ⟨?_, ?_⟩
      · have h0 := ih.1
        simp only [List.length_cons] at h0 ⊢
        omega
      · intro j A v hj
        cases j with
        | zero => simp at hj
        | succ j =>
            simp only [List.getElem?_cons_succ] at hj
            exact ih.2 (j + 1) A v (by
              simp only [List.getElem?_cons_succ]
              exact hj)

/-! ## §5 the classification -/

/-- The refutation site is OFF the routed cone: `[.keep]` puts a `.keep` at
    `zetaCtx`'s let-binding position, which no `RoutedDisp` derivation can
    ever route. -/
theorem zl_rho_not_routed : ¬ RoutedDisp id emptyEnv 0 zetaCtx [.keep] := by
  intro h
  exact (routedDisp_let_noKeep h).2 0 (.sort (.succ .zero)) (.sort .zero)
    (rfl : zetaCtx[0]? = some (.letBinding (.sort (.succ .zero)) (.sort .zero)))
    rfl

/-- The wall restated with `σ` restricted to the cone's own `LevelHom σ`
    (`P2Query.Hom` of an `.es` query): the (d)-port's only strengthening the
    demand cone actually carries. -/
def ZetaLocalResConvWallHom (tbl : List CRule) : Prop :=
  ∀ {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A v : Expr Nat}
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A)
    (σ : Level → Level) (hσ : LevelHom σ) (ρ : List Disp),
    levelIsZero (σ dl.reg.1) = false →
    ConvMod (EStep tbl) LvlEq (resolve ρ i) (hv.eps σ ρ)

/-- **σ-side ON-CONE:** the wall restricted to `LevelHom σ` is still refuted
    at the same fixture (`σ := id` is a `LevelHom` by `levelHom_id`) — the
    value-is-a-sort tooth does not die under the cone's σ-restriction. -/
theorem zl_res_conv_refuted_hom :
    ¬ ZetaLocalResConvWallHom (tableOfI EnvWfT.empty) := by
  intro h
  have hc : levelIsZero (id zrDl.reg.1) = false →
      ConvMod (EStep (tableOfI EnvWfT.empty)) LvlEq
        (resolve [.keep] 0) (zrHv.eps id [.keep]) :=
    h (rfl : lookupValue zetaCtx 0 = some (.sort .zero))
      (rfl : lookupType zetaCtx 0 = some (.sort (.succ .zero)))
      zrHv zrDl zrDr id levelHom_id [.keep]
  exact not_res_conv_zetaLocal_tableWF _ (tableWF_tableOfI_full EnvWfT.empty) hc

/-- **The cone's own disposition holds:** at the canonical Entry disposition
    of `zetaCtx` the routed display is the inline of the stored value's
    erasure, `resolve` returns exactly it, and the wall's `ConvMod` goal is
    reflexivity. -/
theorem zl_res_conv_canon :
    ConvMod (EStep (tableOfI EnvWfT.empty)) LvlEq
      (resolve ((zetaCtxP emptyEnv 0).disp id) 0)
      (zrHv.eps id ((zetaCtxP emptyEnv 0).disp id)) :=
  ConvMod.refl _

theorem zl_canon_disp : (zetaCtxP emptyEnv 0).disp id = [.inline (.sort .zero)] := rfl

end Rcic.Syn

#print axioms Rcic.Syn.removeAt_getElem?_lt
#print axioms Rcic.Syn.removeAt_getElem?_ge
#print axioms Rcic.Syn.insertDisp_getElem?_lt
#print axioms Rcic.Syn.insertDisp_getElem?_ge
#print axioms Rcic.Syn.ctxP_disp_length
#print axioms Rcic.Syn.removeAt_length_drop
#print axioms Rcic.Syn.insertDisp_length
#print axioms Rcic.Syn.substRemove_length_drop
#print axioms Rcic.Syn.insertAt_letBinding_lt
#print axioms Rcic.Syn.insertAt_letBinding_ge
#print axioms Rcic.Syn.substRemove_letBinding_lt
#print axioms Rcic.Syn.substRemove_letBinding_ge
#print axioms Rcic.Syn.ctxP_disp_let_noKeep
#print axioms Rcic.Syn.routedDisp_let_noKeep
#print axioms Rcic.Syn.zl_rho_not_routed
#print axioms Rcic.Syn.ZetaLocalResConvWallHom
#print axioms Rcic.Syn.zl_res_conv_refuted_hom
#print axioms Rcic.Syn.zl_res_conv_canon
#print axioms Rcic.Syn.zl_canon_disp
