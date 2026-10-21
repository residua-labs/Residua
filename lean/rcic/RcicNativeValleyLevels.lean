import rcic.RcicNativeValleyAssemble

/-!
# RcicNativeValleyLevels — the `consts × delta` row closed
(Wall 1, `NativeConvValleys`, piece 9)

`OpenRows.consts_delta` (`RcicNativeValleyAssemble`) is the pair `const r ls ⇒ const r ls'`
(`eqNList ls ls'`) against `const r ls ⇒ instantiateLevels ls b` (δ). The join is
`instantiateLevels ls' b`:

* the `consts` side unfolds at the new levels — a `ParRedT.delta` node at `ls'`, certified by
  `ConvT.delta` moved to the node's index through the inversion of the constant's typing
  (`hasTyTInv_const`), the body typing from the environment (`envWfT_bodyTyped`);
* the δ side needs the ONE-STEP certified level-instantiation congruence on an arbitrary
  typed body, `instantiateLevels ls b ⇒ instantiateLevels ls' b` — `cstep_instLevels`, the
  `ParRedT` twin of the landed `convT_instantiateLevels` (`RcicTypedLevelsCongr.lean`): a
  recursion on the typing derivation of the INSTANTIATED term (the index is whatever that
  derivation ends at, so no re-typing of the body is ever needed), the pre-image `b`
  reconstructed at every node, every certificate the matching `ConvT` congruence, every right
  endpoint an endpoint of that certificate (`convEnds`). The `const` node needs that
  boundedness of `ms.map (instLevel ls)` transfers to `ms.map (instLevel ls')`
  (`levelsBounded_map_instLevel_swap`, syntactic).

`consts_delta_of` has exactly the field's statement; `OpenRows.consts_delta` is discharged.
(Under the landed `EnvWfT`, members with bodies are monomorphic — `envWfT_bodyTypedRaw` gives
`m.arity = 0`, so `ls = ls' = []` — and the row would also close by `refl` on the δ side; the
congruence is kept general so the row does not depend on that restriction.)

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### boundedness transfers between two level lists of the same length -/

/-- A level bounded after instantiation at `ls` is bounded after instantiation at any `ls'` of
    the same length that is itself bounded: the parameters `ls` covers are replaced by bounded
    levels on both sides, the others are untouched on both sides. -/
theorem levelBounded_instLevel_swap {k : Nat} {ls ls' : List Level}
    (hlen : ls.length = ls'.length) (hls' : levelsBounded k ls' = true) :
    (l : Level) → levelBounded k (instLevel ls l) = true →
      levelBounded k (instLevel ls' l) = true
  | .zero, _ => rfl
  | .succ l, h => by
      rw [instLevel_succ] at h ⊢
      exact levelBounded_instLevel_swap hlen hls' l h
  | .max a b, h => by
      rw [instLevel_max] at h ⊢
      simp only [levelBounded, Bool.and_eq_true] at h ⊢
      exact ⟨levelBounded_instLevel_swap hlen hls' a h.1,
        levelBounded_instLevel_swap hlen hls' b h.2⟩
  | .imax a b, h => by
      rw [instLevel_imax] at h ⊢
      simp only [levelBounded, Bool.and_eq_true] at h ⊢
      exact ⟨levelBounded_instLevel_swap hlen hls' a h.1,
        levelBounded_instLevel_swap hlen hls' b h.2⟩
  | .param i, h => by
      rw [instLevel_param] at h ⊢
      by_cases hi : i < ls'.length
      · rw [List.getElem?_eq_getElem hi]
        exact levelsBounded_getElem ls' hls' i hi
      · have hi' : ¬ i < ls.length := by rw [hlen]; exact hi
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hi)]
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hi')] at h
        exact h

/-- The list form. -/
theorem levelsBounded_map_instLevel_swap {k : Nat} {ls ls' : List Level}
    (hlen : ls.length = ls'.length) (hls' : levelsBounded k ls' = true) :
    (ms : List Level) → levelsBounded k (ms.map (instLevel ls)) = true →
      levelsBounded k (ms.map (instLevel ls')) = true
  | [], _ => rfl
  | m :: t, h => by
      simp only [List.map, levelsBounded, Bool.and_eq_true] at h ⊢
      exact ⟨levelBounded_instLevel_swap hlen hls' m h.1,
        levelsBounded_map_instLevel_swap hlen hls' t h.2⟩

/-! ### the one-step certified level-instantiation congruence -/

/-- `instantiateLevels ls b ⇒ instantiateLevels ls' b`, certified, at any type the
    instantiated term is derived at: recursion on that derivation, the pre-image `b` read off
    at each node (`instantiateLevels` is a constructor homomorphism), certificates the `ConvT`
    congruences (`sorts` / `consts` at the leaves), right endpoints from `convEnds`. -/
def cstep_instLevels (hW : EnvWfT E) (L : LeafIface E n PEq) {ls ls' : List Level}
    (heq : eqNList ls ls') (hls' : levelsBounded n ls' = true) :
    {Γ : LCtx} → {e T : Expr Nat} → HasTyT E n Γ e T → CtxWfT E n Γ → (b : Expr Nat) →
    e = instantiateLevels ls b → CStep E n PEq Γ e (instantiateLevels ls' b) T
  | _, _, _, .sort Γ l, hΓ, b, hb => by
      cases b <;> simp [instantiateLevels] at hb
      case sort l₀ =>
      subst hb
      simp only [instantiateLevels]
      have c : ConvT E n Γ (.sort (instLevel ls l₀)) (.sort (instLevel ls' l₀))
          (.sort (.succ (instLevel ls l₀))) :=
        .sorts _ _ _ (instLevel_eqNList heq l₀)
      exact ⟨.sortEq _ _ _ _ (instLevel_eqNList heq l₀) (.sort _ _) (convEnds hW hΓ c).2.1,
        .sortEq c⟩
  | _, _, _, .bvar Γ i A h, _, b, hb => by
      cases b <;> simp [instantiateLevels] at hb
      case bvar i₀ =>
      subst hb
      simp only [instantiateLevels]
      exact ⟨.refl _ _ _ (.bvar Γ _ A h), .refl (.refl _ _ _ (.bvar Γ _ A h))⟩
  | _, _, _, .const Γ r ms m hres hlen hwf, hΓ, b, hb => by
      cases b <;> simp [instantiateLevels] at hb
      case const r₀ ms₀ =>
      obtain ⟨rfl, rfl⟩ := hb
      simp only [instantiateLevels]
      have hwf' : levelsBounded n (ms₀.map (instLevel ls')) = true :=
        levelsBounded_map_instLevel_swap (eqNList_length _ _ heq) hls' ms₀ hwf
      have c : ConvT E n Γ (.const r (ms₀.map (instLevel ls))) (.const r (ms₀.map (instLevel ls')))
          (instantiateLevels (ms₀.map (instLevel ls)) m.mtype) :=
        .consts Γ r _ _ m hres hlen hwf hwf' (instLevel_eqNList_map heq ms₀)
      exact ⟨.consts Γ r _ _ _ (instLevel_eqNList_map heq ms₀) (.const Γ r _ m hres hlen hwf)
        (convEnds hW hΓ c).2.1, .consts c⟩
  | _, _, _, .pi Γ A u B v hA hB, hΓ, b, hb => by
      cases b <;> simp [instantiateLevels] at hb
      case pi A₀ B₀ =>
      obtain ⟨hA₀, hB₀⟩ := hb
      simp only [instantiateLevels]
      have sA := cstep_instLevels hW L heq hls' hA hΓ A₀ hA₀
      have sB := cstep_instLevels hW L heq hls' hB (.assumption Γ A u hΓ hA) B₀ hB₀
      have c : ConvT E n Γ (.pi A B) (.pi (instantiateLevels ls' A₀) (instantiateLevels ls' B₀))
          (.sort (.imax u v)) :=
        .pi Γ _ _ _ _ u v sA.toConvT sB.toConvT
      exact ⟨.pi Γ _ _ _ _ u v hA sA.toConvT hB sB.toConvT (convEnds hW hΓ c).2.1, .pi c⟩
  | _, _, _, .lam Γ A u body B hA hbody, hΓ, b, hb => by
      cases b <;> simp [instantiateLevels] at hb
      case lam A₀ body₀ =>
      obtain ⟨hA₀, hbody₀⟩ := hb
      simp only [instantiateLevels]
      have hΓ' : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A u hΓ hA
      have sA := cstep_instLevels hW L heq hls' hA hΓ A₀ hA₀
      have sb := cstep_instLevels hW L heq hls' hbody hΓ' body₀ hbody₀
      have ⟨w, hBw⟩ := tySort hW hΓ' hbody
      have c : ConvT E n Γ (.lam A body)
          (.lam (instantiateLevels ls' A₀) (instantiateLevels ls' body₀)) (.pi A B) :=
        .lam Γ _ _ _ _ B u sA.toConvT sb.toConvT
      exact ⟨.lam Γ _ _ _ _ B u w sA.toConvT hA hBw sb.step (convEnds hW hΓ c).2.1,
        .lam c sb.cert⟩
  | _, _, _, .app Γ f a A B hf ha, hΓ, b, hb => by
      cases b <;> simp [instantiateLevels] at hb
      case app f₀ a₀ =>
      obtain ⟨hf₀, ha₀⟩ := hb
      simp only [instantiateLevels]
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have sf := cstep_instLevels hW L heq hls' hf hΓ f₀ hf₀
      have sa := cstep_instLevels hW L heq hls' ha hΓ a₀ ha₀
      have ⟨_, v, _, hBv, _⟩ := hasTyTInv_pi (tySort hW hΓ hf).2 rfl
      have hTy := hasTyT_subst0S hcl hinst hBv ha
      have c : ConvT E n Γ (.app f a)
          (.app (instantiateLevels ls' f₀) (instantiateLevels ls' a₀)) (instantiate0 a B) :=
        .app Γ _ _ _ _ A B sf.toConvT sa.toConvT
      exact ⟨.app Γ _ _ _ _ A B (.pi A B) v v sf.step (.refl _ _) hBv hTy sa.step
        (convEnds hW hΓ c).2.1, .app c sf.cert sa.cert⟩
  | _, _, _, .letE Γ A u value B body hA hv hbody, hΓ, b, hb => by
      cases b <;> simp [instantiateLevels] at hb
      case letE A₀ v₀ body₀ =>
      obtain ⟨hA₀, hv₀, hbody₀⟩ := hb
      simp only [instantiateLevels]
      have hΓ' : CtxWfT E n (.letBinding A value :: Γ) := .letBinding Γ A u value hΓ hA hv
      have sA := cstep_instLevels hW L heq hls' hA hΓ A₀ hA₀
      have sv := cstep_instLevels hW L heq hls' hv hΓ v₀ hv₀
      have sb := cstep_instLevels hW L heq hls' hbody hΓ' body₀ hbody₀
      have ⟨w, hBw⟩ := tySort hW hΓ' hbody
      have hTy : HasTyT E n Γ (instantiate0 value B) (.sort w) := by
        have h0 := hasTyT_substLet0_of_envWfT hW hBw hv
        simpa only [instantiate0, instantiate] using h0
      have c : ConvT E n Γ (.letE A value body)
          (.letE (instantiateLevels ls' A₀) (instantiateLevels ls' v₀)
            (instantiateLevels ls' body₀))
          (instantiate0 value B) :=
        .letE Γ _ _ _ _ _ _ B u sA.toConvT sv.toConvT sb.toConvT
      exact ⟨.letE Γ _ _ _ _ _ _ B u w sA.toConvT hA sv.step hBw hTy sb.step
        (convEnds hW hΓ c).2.1, .letE c sv.cert sb.cert⟩
  | _, _, _, .lit Γ t T hexp, _, b, hb => by
      cases b <;> simp [instantiateLevels] at hb
      case lit t₀ =>
      subst hb
      simp only [instantiateLevels]
      exact ⟨.refl _ _ _ (.lit Γ _ T hexp), .refl (.refl _ _ _ (.lit Γ _ T hexp))⟩
  | _, _, _, .conv Γ e A B u h hc, hΓ, b, hb =>
      (cstep_instLevels hW L heq hls' h hΓ b hb).reindex (.of _ _ _ u hc)
  termination_by _ _ _ h _ _ _ => sizeOf h
  decreasing_by all_goals (simp; omega)

/-! ### the row -/

/-- `consts × delta`: join at `instantiateLevels ls' b` — δ at the new levels on the `consts`
    side (certificate `ConvT.delta` moved to the node's index), the certified
    level-instantiation congruence on the δ side. Exactly `OpenRows.consts_delta`'s
    statement. -/
def consts_delta_of (hW : EnvWfT E) (L : LeafIface E n PEq) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {ls ls' : List Level}
    {T₁ T₂ : Expr Nat} {m : CheckedMember} {b : Expr Nat} {h : eqNList ls ls'}
    {hl₁ : HasTyT E n Γ (.const r ls) T₁} {hr₁ : HasTyT E n Γ (.const r ls') T₁}
    {hres : E.members r = some m} {hbody : m.body = some b}
    {htr : transparent m.mclass = true} {hlen : ls.length = m.arity}
    {hwf : levelsBounded n ls = true}
    {hl₂ : HasTyT E n Γ (.const r ls) T₂} {hr₂ : HasTyT E n Γ (instantiateLevels ls b) T₂},
    Certified (ParRedT.consts (PEq := PEq) Γ r ls ls' T₁ h hl₁ hr₁) →
    Certified (ParRedT.delta (PEq := PEq) Γ r ls m b T₂ hres hbody htr hlen hwf hl₂ hr₂) →
    Join E n PEq Γ (.const r ls') (instantiateLevels ls b) T₁ T₂ :=
  fun {Γ} hΓ {r ls ls' T₁ _ m b h _ hr₁ hres hbody htr hlen _ _ hr₂} _ _ => by
    have hlen' : ls'.length = m.arity := (eqNList_length _ _ h).symm.trans hlen
    obtain ⟨m', hres', _, hwf', hcv⟩ := hasTyTInv_const hr₁ rfl
    cases hres.symm.trans hres'
    have hb' : HasTyT E n Γ (instantiateLevels ls' b) (instantiateLevels ls' m.mtype) :=
      envWfT_bodyTyped hW hres hbody hlen'
    have cδ : ConvT E n Γ (.const r ls') (instantiateLevels ls' b) T₁ :=
      convT_of_tyConv (.delta Γ r ls' m b hres hbody htr hlen' hwf' hb') hcv
    exact ⟨instantiateLevels ls' b,
      ⟨.delta Γ r ls' m b T₁ hres hbody htr hlen' hwf' hr₁ (convEnds hW hΓ cδ).2.1, .delta cδ⟩,
      cstep_instLevels hW L h hwf' hr₂ hΓ b rfl⟩

end Rcic.Declarative.NativeValleys
