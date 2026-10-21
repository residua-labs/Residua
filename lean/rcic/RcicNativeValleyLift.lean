import rcic.RcicNativeValleyRows
import rcic.RcicParRedTSubst

/-!
# RcicNativeValleyLift — certified weakening (Wall 1, `NativeConvValleys`, piece 5)

The certified twin of the landed `parRedT_lift` / `parRedT_lift_lctx` / `parRedT_lift_n`
(`RcicParRedTSubst.lean`): a certified step transports under one-declaration insertion
(`cstep_lift`) and under a context prefix (`cstep_lift_lctx`), the certificate of every node
moving by the landed `convTWeaken`, the `conv` chains by `tyConvTWeaken`, the typings by
`hasTyTWeaken`. The recursion is the landed one (the arms are the landed arms, now producing
the node's certificate alongside); the two K arms are absent because certified steps are
K-free (`Certified.noK`). The leaf transports under weakening by the same hypothesis `hPEqL`
the landed theorem takes.

`certLift_of` discharges `CertLift` (`RcicNativeValleyRows`), the transport the
`bvarZeta × bvarZeta` row consumes.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Certified one-declaration weakening: the landed `parRedT_lift` with the certificate of
    every node carried (`convTWeaken`). -/
def cstep_lift (d : LocalDecl) (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T)) :
    {c : Nat} → {Γ : LCtx} → {a b T : Expr Nat} → {p : ParRedT PEq E n Γ a b T} →
    Certified p →
    CStep E n PEq (insertAt d c Γ) (lift c 1 a) (lift c 1 b) (lift c 1 T)
  | _, _, _, _, _, _, @Certified.refl _ _ _ _ _ _ h c₀ =>
      ⟨.refl _ _ _ (hasTyTWeaken d hcl h), .refl (convTWeaken d hcl c₀)⟩
  | c, _, _, _, _, _, @Certified.sortEq _ _ _ _ l₁ l₂ _ h hl hr c₀ => by
      have hc' := convTWeaken d hcl (c := c) c₀
      simp only [lift] at hc' ⊢
      exact ⟨.sortEq _ _ _ _ h (hasTyTWeaken d hcl hl) (hasTyTWeaken d hcl hr), .sortEq hc'⟩
  | c, _, _, _, _, _, @Certified.consts _ _ _ _ r ls ls' _ h hl hr c₀ => by
      have hc' := convTWeaken d hcl (c := c) c₀
      simp only [lift] at hc' ⊢
      exact ⟨.consts _ _ _ _ _ h (hasTyTWeaken d hcl hl) (hasTyTWeaken d hcl hr), .consts hc'⟩
  | c, _, _, _, _, _, @Certified.bvarZeta _ _ _ Γ i A v v' T h hv hl hr c₀ cv => by
      by_cases hic : i < c
      · simp only [lift, if_neg (Nat.not_le_of_gt hic)]
        have hlen := get?_some_lt h
        have hg := insertAt_get?_lt d (Γ := Γ) hic h
        have hdrop := insertAt_drop_lt d (Γ := Γ) hic hlen
        have hv' := cstep_lift d hcl hPEqL (c := c - i - 1) cv
        rw [← hdrop] at hv'
        have htgt :
            lift 0 (i + 1) (lift (c - i - 1) 1 v') =
              lift (i + 1 + (c - i - 1)) 1 (lift 0 (i + 1) v') :=
          lift_lift_permute (i + 1) 1 (c - i - 1) 0 (Nat.zero_le _) v'
        have hsum : i + 1 + (c - i - 1) = c := by omega
        rw [hsum] at htgt
        simp only [liftDecl] at hg
        have hl' := hasTyTWeaken d hcl (c := c) hl
        have hr' := hasTyTWeaken d hcl (c := c) hr
        have hc' := convTWeaken d hcl (c := c) c₀
        simp only [lift, if_neg (Nat.not_le_of_gt hic)] at hl' hr' hc'
        rw [← htgt] at hr' hc' ⊢
        exact ⟨.bvarZeta (insertAt d c Γ) i
          (lift (c - i - 1) 1 A) (lift (c - i - 1) 1 v) (lift (c - i - 1) 1 v')
          (lift c 1 T) hg hv'.step hl' hr', .bvarZeta hc' hv'.cert⟩
      · have hge : c ≤ i := Nat.le_of_not_lt hic
        simp only [lift, if_pos hge]
        have hg := insertAt_get?_ge d (Γ := Γ) hge
        rw [h] at hg
        have hdrop := insertAt_drop_ge d (Γ := Γ) hge
        have htgt : lift 0 (i + 2) v' =
            lift c 1 (lift 0 (i + 1) v') :=
          (lift_lift_merge 1 (i + 1) 0 c (Nat.zero_le c)
            (by omega : c ≤ i + 1) v').symm
        have hl' := hasTyTWeaken d hcl (c := c) hl
        have hr' := hasTyTWeaken d hcl (c := c) hr
        have hc' := convTWeaken d hcl (c := c) c₀
        simp only [lift, if_pos hge] at hl' hc'
        rw [← htgt] at hr' hc' ⊢
        have hv' : CStep E n PEq ((insertAt d c Γ).drop (i + 1 + 1)) v v' A := hdrop ▸ ⟨hv, cv⟩
        exact ⟨.bvarZeta (insertAt d c Γ) (i + 1) A v v' (lift c 1 T)
          hg hv'.step hl' hr', .bvarZeta hc' hv'.cert⟩
  | c, _, _, _, _, _, @Certified.delta _ _ _ Γ r ls m b T hres hbody htr hlen hwf hl hr c₀ => by
      have hbc : lift c 1 b = b := (hcl r m hres).2 b hbody c
      have hl' := hasTyTWeaken d hcl (c := c) hl
      have hr' := hasTyTWeaken d hcl (c := c) hr
      have hc' := convTWeaken d hcl (c := c) c₀
      simp only [lift, lift_instantiateLevels, hbc] at hr' hc' ⊢
      exact ⟨.delta _ _ _ _ _ _ hres hbody htr hlen hwf hl' hr', .delta hc'⟩
  | c, _, _, _, _, _, @Certified.app _ _ _ Γ f f' a a' A B T₀ v w hf hc hB hTy ha hr c₀ cf ca => by
      have h := lift_instantiate_low 1 c 0 a (by omega) B
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      have hTy' := hasTyTWeaken d hcl (c := c) hTy
      have hr' := hasTyTWeaken d hcl (c := c) hr
      have hc' := convTWeaken d hcl (c := c) c₀
      simp only [lift, instantiate0] at hTy' hr' hc' ⊢
      rw [h] at hTy' hr' hc' ⊢
      have ihf := cstep_lift d hcl hPEqL (c := c) cf
      have iha := cstep_lift d hcl hPEqL (c := c) ca
      exact ⟨.app _ _ _ _ _ _ _ _ _ _ ihf.step (tyConvTWeaken d hcl hc) hB' hTy' iha.step hr',
        .app hc' ihf.cert iha.cert⟩
  | c, _, _, _, _, _, @Certified.beta _ _ _ Γ A body body' arg arg' B u v w hA hB hTy hb ha hred
      c₀ cb ca => by
      have h := lift_instantiate_low 1 c 0 arg (by omega) B
      have h' := lift_instantiate_low 1 c 0 arg' (by omega) body'
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      have hTy' := hasTyTWeaken d hcl (c := c) hTy
      have hred' := hasTyTWeaken d hcl (c := c) hred
      have hc' := convTWeaken d hcl (c := c) c₀
      have ihb := cstep_lift d hcl hPEqL (c := c + 1) cb
      simp only [insertAt_succ_cons, liftDecl] at ihb
      have iha := cstep_lift d hcl hPEqL (c := c) ca
      simp only [lift, instantiate0] at hTy' hred' hc' ⊢
      rw [h] at hTy' hred' hc' ⊢
      rw [h'] at hred' hc' ⊢
      exact ⟨.beta _ _ _ _ _ _ _ _ _ _
        (hasTyTWeaken d hcl hA) hB' hTy' ihb.step iha.step hred', .beta hc' ihb.cert iha.cert⟩
  | c, _, _, _, _, _, @Certified.lam _ _ _ Γ A A' body body' B u v hc hA hB hb hrt c₀ cb => by
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      have ihb := cstep_lift d hcl hPEqL (c := c + 1) cb
      simp only [insertAt_succ_cons, liftDecl] at ihb
      have hrt' := hasTyTWeaken d hcl (c := c) hrt
      have hc' := convTWeaken d hcl (c := c) c₀
      simp only [lift] at hrt' hc' ⊢
      exact ⟨.lam _ _ _ _ _ _ _ _
        (convTWeaken d hcl hc) (hasTyTWeaken d hcl hA) hB' ihb.step hrt', .lam hc' ihb.cert⟩
  | c, _, _, _, _, _, @Certified.pi _ _ _ Γ A A' B B' u v hA hc hB hcB hrt c₀ => by
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      have hcB' := convTWeaken d hcl (c := c + 1) hcB
      simp only [insertAt_succ_cons, liftDecl] at hcB'
      have hrt' := hasTyTWeaken d hcl (c := c) hrt
      have hc' := convTWeaken d hcl (c := c) c₀
      simp only [lift] at hrt' hc' ⊢
      exact ⟨.pi _ _ _ _ _ _ _
        (hasTyTWeaken d hcl hA) (convTWeaken d hcl hc) hB' hcB' hrt', .pi hc'⟩
  | c, _, _, _, _, _, @Certified.letE _ _ _ Γ A A' value value' body body' B u w hc hA hv hB hTy hb
      hrt c₀ cv cb => by
      have h := lift_instantiate_low 1 c 0 value (by omega) B
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      have hTy' := hasTyTWeaken d hcl (c := c) hTy
      have hrt' := hasTyTWeaken d hcl (c := c) hrt
      have hc' := convTWeaken d hcl (c := c) c₀
      have ihb := cstep_lift d hcl hPEqL (c := c + 1) cb
      simp only [insertAt_succ_cons, liftDecl] at ihb
      have ihv := cstep_lift d hcl hPEqL (c := c) cv
      simp only [lift, instantiate0] at hTy' hrt' hc' ⊢
      rw [h] at hTy' hrt' hc' ⊢
      exact ⟨.letE _ _ _ _ _ _ _ _ _ _
        (convTWeaken d hcl hc) (hasTyTWeaken d hcl hA)
        ihv.step hB' hTy' ihb.step hrt', .letE hc' ihv.cert ihb.cert⟩
  | c, _, _, _, _, _, @Certified.zeta _ _ _ Γ A value value' body body' B u w hA hv hB hTy hb hred
      c₀ cv cb => by
      have h := lift_instantiate_low 1 c 0 value (by omega) B
      have h' := lift_instantiate_low 1 c 0 value' (by omega) body'
      have hB' := hasTyTWeaken d hcl (c := c + 1) hB
      simp only [insertAt_succ_cons, liftDecl] at hB'
      have hTy' := hasTyTWeaken d hcl (c := c) hTy
      have hred' := hasTyTWeaken d hcl (c := c) hred
      have hc' := convTWeaken d hcl (c := c) c₀
      have ihb := cstep_lift d hcl hPEqL (c := c + 1) cb
      simp only [insertAt_succ_cons, liftDecl] at ihb
      have ihv := cstep_lift d hcl hPEqL (c := c) cv
      simp only [lift, instantiate0] at hTy' hred' hc' ⊢
      rw [h] at hTy' hred' hc' ⊢
      rw [h'] at hred' hc' ⊢
      exact ⟨.zeta _ _ _ _ _ _ _ _ _
        (hasTyTWeaken d hcl hA) ihv.step hB' hTy' ihb.step hred', .zeta hc' ihv.cert ihb.cert⟩
  | c, _, _, _, _, _, @Certified.iotaSpine _ _ _ Γ lhs lhs' rhs T hstep hI hred hrhs c₀ cs =>
      let ihs := cstep_lift d hcl hPEqL (c := c) cs
      ⟨.iotaSpine _ _ _ _ _ ihs.step (derivedIotaU_lift c hI)
        (hasTyTWeaken d hcl hred) (hasTyTWeaken d hcl hrhs),
        .iotaSpine (convTWeaken d hcl c₀) ihs.cert⟩
  | c, _, _, _, _, _, @Certified.lit _ _ _ Γ t T hexp c₀ => by
      have hexp' := hasTyTWeaken d hcl (c := c) hexp
      have hc' := convTWeaken d hcl (c := c) c₀
      rw [natExpand_lift c 1 t] at hexp'
      simp only [lift] at hc' ⊢
      rw [natExpand_lift c 1 t] at hc' ⊢
      exact ⟨.lit _ _ _ hexp', .lit hc'⟩
  | c, _, _, _, _, _, @Certified.eta _ _ _ Γ f f' A B hf hl c₀ cf => by
      have ihf := cstep_lift d hcl hPEqL (c := c) cf
      have hl' := hasTyTWeaken d hcl (c := c) hl
      have hc' := convTWeaken d hcl (c := c) c₀
      simp only [lift,
        if_neg (Nat.not_le_of_gt (Nat.succ_pos c) : ¬ c + 1 ≤ 0)]
        at ihf hl' hc' ⊢
      have e2 : lift (c + 1) 1 (lift 0 1 f) = lift 0 1 (lift c 1 f) := by
        rw [show c + 1 = 1 + c from by omega,
          ← lift_lift_permute 1 1 c 0 (Nat.zero_le c) f]
      rw [e2] at hl' hc' ⊢
      exact ⟨.eta _ _ _ _ _ ihf.step hl', .eta hc' ihf.cert⟩
  | _, _, _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h c₀ =>
      ⟨.peq _ _ _ _ (hPEqL h), .peq (convTWeaken d hcl c₀)⟩
  | c, _, _, _, _, _, @Certified.conv _ _ _ _ _ _ _ _ h hc c₀ ch =>
      let ih := cstep_lift d hcl hPEqL (c := c) ch
      ⟨.conv _ _ _ _ _ ih.step (tyConvTWeaken d hcl hc), .conv (convTWeaken d hcl c₀) ih.cert⟩

/-- Certified prefix weakening: `Δ` fresh declarations at the top (the landed
    `parRedT_lift_lctx`, certificates carried). -/
def cstep_lift_lctx (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T)) :
    (Δ : LCtx) → {Γ : LCtx} → {a b T : Expr Nat} →
    CStep E n PEq Γ a b T →
    CStep E n PEq (Δ ++ Γ) (lift 0 Δ.length a) (lift 0 Δ.length b) (lift 0 Δ.length T)
  | [], _, _, _, _, s => by
      simp only [List.nil_append, List.length_nil, lift_zero]
      exact s
  | d :: Δ, Γ, a, b, T, s => by
      have ih := cstep_lift_lctx hcl hPEqL Δ s
      have hw := cstep_lift d hcl hPEqL (c := 0) ih.cert
      simp only [List.cons_append, List.length_cons, insertAt_zero]
      have ha : lift 0 1 (lift 0 Δ.length a) = lift 0 (Δ.length + 1) a :=
        lift_zero_succ Δ.length a
      have hb : lift 0 1 (lift 0 Δ.length b) = lift 0 (Δ.length + 1) b :=
        lift_zero_succ Δ.length b
      have hT : lift 0 1 (lift 0 Δ.length T) = lift 0 (Δ.length + 1) T :=
        lift_zero_succ Δ.length T
      rw [← ha, ← hb, ← hT]
      exact hw

/-- `CertLift` discharged: the certified weakening of `RcicNativeValleyRows` holds under the
    landed fronts `EnvClosed` and leaf weakening. -/
def certLift_of (hcl : EnvClosed E)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T)) :
    CertLift E n PEq :=
  fun {_} Δ {_ _ _} s => cstep_lift_lctx hcl hPEqL Δ s

end Rcic.Declarative.NativeValleys
