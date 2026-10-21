import rcic.RcicConvPlus

/-!
# Syntactic sortRow, build step 1d — O1's admission rows and transport strips

`research/rcic/semantic/S1_ORDER_ENRICHED_LEVELS.md` §3.3 and §3.5. δ, and PB/CTS at a constant,
compare an in-context enriched derivation with a member's ADMISSION derivation. That derivation is
not a subderivation. O1 pays for it through the const node's admission weight `Aw r` (`TyP.wt`).
This module proves the inequality end to end, in the whole environment:
* `TyP.wt_congr`: a derivation's weight depends on `Aw` only at members of its environment;
* `EnvWfP.typeAdm`: any member's stored-type derivation, in a prefix, lighter than `admW r`;
* `EnvWfP.defAdm`: a transparent member's body derivation, likewise. Group members have no body
  (`GroupMembersP`'s `hnobody`), so δ never reaches a group;
* `TyP.admW_lt_of_const`: every typing of `const r ls` is heavier than `Aw r`, through every
  transport;
* `delta_adm_below`, `const_adm_below`: the call rows. Every atom of the admission derivation lies
  below the δ node (resp. the const node), so the call is a `DMStep` (`dmStep_of_below`).

Transport strips (`S1` §3.5):
* stripping a parameterless transport (`wk`, `linst`, `ewk`) leaves the atoms literally equal and
  lowers the summed weight. That is a `Prod.Lex` step of `lexDM_wf`;
* stripping an `esub` drops its parameters' atoms. That is a `DMStep` (`dmStep_drop`).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 weights depend on `Aw` only at members -/

/-- two admission-weight functions agree at the members of `E`. -/
def AgreeOn (E : ResolvedEnv) (Aw Aw' : Nat → Nat) : Prop :=
  ∀ r m, E.members r = some m → Aw r = Aw' r

theorem agreeOn_mono {E₀ E : ResolvedEnv} {Aw Aw' : Nat → Nat} (hext : EnvExt E₀ E)
    (h : AgreeOn E Aw Aw') : AgreeOn E₀ Aw Aw' := fun r m hr => h r m (hext r m hr)

theorem agreeOn_setW {E : ResolvedEnv} {r : Nat} (Aw : Nat → Nat) (w : Nat)
    (hfresh : E.members r = none) : AgreeOn E (setW Aw r w) Aw := by
  intro c m hc
  have hne : c ≠ r := by
    intro h; subst h; rw [hfresh] at hc; exact Option.noConfusion hc
  exact setW_ne Aw w hne

mutual

theorem TyP.wt_congr {Aw Aw' : Nat → Nat} : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → (D : TyP E n Γ e T) → AgreeOn E Aw Aw' → D.wt Aw = D.wt Aw'
  | _, _, _, _, _, .sort .., _ => rfl
  | _, _, _, _, _, .bvar (hA := hA) .., hag => by simp only [TyP.wt, TyP.wt_congr hA hag]
  | _, _, _, _, _, .const (r := r) (m := m) (hres := hres) (hT := hT) .., hag => by
      simp only [TyP.wt, TyP.wt_congr hT hag, hag r m hres]
  | _, _, _, _, _, .pi (hA := hA) (hB := hB) .., hag => by
      simp only [TyP.wt, TyP.wt_congr hA hag, TyP.wt_congr hB hag]
  | _, _, _, _, _, .lam (hA := hA) (hbody := hbody) (hB := hB) .., hag => by
      simp only [TyP.wt, TyP.wt_congr hA hag, TyP.wt_congr hbody hag, TyP.wt_congr hB hag]
  | _, _, _, _, _, .app (hf := hf) (ha := ha) (hT := hT) .., hag => by
      simp only [TyP.wt, TyP.wt_congr hf hag, TyP.wt_congr ha hag, TyP.wt_congr hT hag]
  | _, _, _, _, _, .letE (hA := hA) (hv := hv) (hb := hb) (hT := hT) .., hag => by
      simp only [TyP.wt, TyP.wt_congr hA hag, TyP.wt_congr hv hag, TyP.wt_congr hb hag,
        TyP.wt_congr hT hag]
  | _, _, _, _, _, .lit (hexp := hexp) .., hag => by simp only [TyP.wt, TyP.wt_congr hexp hag]
  | _, _, _, _, _, .conv (h := h) (hc := hc) .., hag => by
      simp only [TyP.wt, TyP.wt_congr h hag, CvP.wt_congr hc hag]
  | _, _, _, _, _, .wk (D := D) .., hag => by simp only [TyP.wt, TyP.wt_congr D hag]
  | _, _, _, _, _, .esub (D := D) (hv := hv) (hvT := hvT) .., hag => by
      simp only [TyP.wt, TyP.wt_congr D hag, TyP.wt_congr hv hag, TyP.wt_congr hvT hag]
  | _, _, _, _, _, .lsub (D := D) (hv := hv) (hvT := hvT) .., hag => by
      simp only [TyP.wt, TyP.wt_congr D hag, TyP.wt_congr hv hag, TyP.wt_congr hvT hag]
  | _, _, _, _, _, .linst (D := D) .., hag => by simp only [TyP.wt, TyP.wt_congr D hag]
  | _, _, _, _, _, .ewk (hext := hext) (D := D) .., hag => by
      simp only [TyP.wt, TyP.wt_congr D (agreeOn_mono hext hag)]
  | _, _, _, _, _, .cctx (D := D) (hA := hA) .., hag => by
      simp only [TyP.wt, TyP.wt_congr D hag, CvP.wt_congr hA hag]

theorem CvP.wt_congr {Aw Aw' : Nat → Nat} : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} → (h : CvP E n Γ a b T) → AgreeOn E Aw Aw' → h.wt Aw = h.wt Aw'
  | _, _, _, _, _, _, .refl (h := h) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, TyP.wt_congr h hag, TyP.wt_congr dl hag, TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .symm (h := h) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, CvP.wt_congr h hag, TyP.wt_congr dl hag, TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .trans (h1 := h1) (h2 := h2) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, CvP.wt_congr h1 hag, CvP.wt_congr h2 hag, TyP.wt_congr dl hag,
        TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .beta (hA := hA) (hbody := hbody) (harg := harg) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, TyP.wt_congr hA hag, TyP.wt_congr hbody hag, TyP.wt_congr harg hag,
        TyP.wt_congr dl hag, TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .zeta (hA := hA) (hv := hv) (hb := hb) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, TyP.wt_congr hA hag, TyP.wt_congr hv hag, TyP.wt_congr hb hag,
        TyP.wt_congr dl hag, TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .zetaLocal (hv := hv) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, TyP.wt_congr hv hag, TyP.wt_congr dl hag, TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .delta (hb := hb) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, TyP.wt_congr hb hag, TyP.wt_congr dl hag, TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .iota (hlhs := hl) (hrhs := hr) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, TyP.wt_congr hl hag, TyP.wt_congr hr hag, TyP.wt_congr dl hag,
        TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .lit (hexp := hexp) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, TyP.wt_congr hexp hag, TyP.wt_congr dl hag, TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .app (h1 := h1) (h2 := h2) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, CvP.wt_congr h1 hag, CvP.wt_congr h2 hag, TyP.wt_congr dl hag,
        TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .lam (hA := hA) (hb := hb) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, CvP.wt_congr hA hag, CvP.wt_congr hb hag, TyP.wt_congr dl hag,
        TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .pi (hA := hA) (hB := hB) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, CvP.wt_congr hA hag, CvP.wt_congr hB hag, TyP.wt_congr dl hag,
        TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .letE (hA := hA) (hv := hv) (hb := hb) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, CvP.wt_congr hA hag, CvP.wt_congr hv hag, CvP.wt_congr hb hag,
        TyP.wt_congr dl hag, TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .sorts (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, TyP.wt_congr dl hag, TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .consts (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, TyP.wt_congr dl hag, TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .eta (h := h) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, TyP.wt_congr h hag, TyP.wt_congr dl hag, TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .irr (hP := hP) (hp := hp) (hq := hq) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, TyP.wt_congr hP hag, TyP.wt_congr hp hag, TyP.wt_congr hq hag,
        TyP.wt_congr dl hag, TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .tyConv (h := h) (hA := hA) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, CvP.wt_congr h hag, CvP.wt_congr hA hag, TyP.wt_congr dl hag,
        TyP.wt_congr dr hag]
  | _, _, _, _, _, _, .wk (h := h) .., hag => by simp only [CvP.wt, CvP.wt_congr h hag]
  | _, _, _, _, _, _, .esub (h := h) (hv := hv) (hvT := hvT) .., hag => by
      simp only [CvP.wt, CvP.wt_congr h hag, TyP.wt_congr hv hag, TyP.wt_congr hvT hag]
  | _, _, _, _, _, _, .linst (h := h) .., hag => by simp only [CvP.wt, CvP.wt_congr h hag]
  | _, _, _, _, _, _, .ewk (hext := hext) (h := h) .., hag => by
      simp only [CvP.wt, CvP.wt_congr h (agreeOn_mono hext hag)]
  | _, _, _, _, _, _, .cctx (h := h) (hA := hA) .., hag => by
      simp only [CvP.wt, CvP.wt_congr h hag, CvP.wt_congr hA hag]
  | _, _, _, _, _, _, .fsub (hB := hB) (hA := hA) (hab := hab) (dl := dl) (dr := dr) .., hag => by
      simp only [CvP.wt, TyP.wt_congr hB hag, TyP.wt_congr hA hag, CvP.wt_congr hab hag,
        TyP.wt_congr dl hag, TyP.wt_congr dr hag]

end

/-! ## §2 every typing of a constant is heavier than its admission weight -/

theorem lift_eq_const_k {c k : Nat} {e : Expr Nat} {r : Nat} {ls : List Level}
    (h : lift c k e = .const r ls) : e = .const r ls := by
  cases e with
  | bvar i =>
      unfold lift at h
      split at h
      · exact Expr.noConfusion h
      · exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

theorem instantiate_eq_const_or {j : Nat} {v e : Expr Nat} {r : Nat} {ls : List Level}
    (h : instantiate j v e = .const r ls) : e = .const r ls ∨ v = .const r ls := by
  cases e with
  | bvar i =>
      unfold instantiate at h
      split at h
      · exact Or.inr h
      · split at h
        · exact Expr.noConfusion h
        · exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Or.inl h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

theorem instantiateLevels_eq_const_ex {ls' : List Level} {e : Expr Nat} {r : Nat}
    {ls : List Level} (h : instantiateLevels ls' e = .const r ls) : ∃ ms, e = .const r ms := by
  cases e with
  | bvar _ => exact Expr.noConfusion h
  | sort _ => exact Expr.noConfusion h
  | const r' ms =>
      have h' : Expr.const r' (ms.map (instLevel ls')) = .const r ls := h
      injection h' with hr _
      exact ⟨ms, hr ▸ rfl⟩
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

/-- every typing of `const r ls` weighs more than `Aw r`, through `conv` and every transport. At
    `esub` the constant may be the replacement itself; then the replacement's typing `hv` pays. -/
theorem TyP.admW_lt_of_const (Aw : Nat → Nat) {r : Nat} : {E : ResolvedEnv} → {n : Nat} →
    {Γ : LCtx} → {e T : Expr Nat} → (D : TyP E n Γ e T) → (∃ ls, e = .const r ls) →
    Aw r < D.wt Aw
  | _, _, _, _, _, .sort .., ⟨_, h⟩ => Expr.noConfusion h
  | _, _, _, _, _, .bvar .., ⟨_, h⟩ => Expr.noConfusion h
  | _, _, _, _, _, .const .., ⟨_, h⟩ => by
      injection h with hr _
      subst hr
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .pi .., ⟨_, h⟩ => Expr.noConfusion h
  | _, _, _, _, _, .lam .., ⟨_, h⟩ => Expr.noConfusion h
  | _, _, _, _, _, .app .., ⟨_, h⟩ => Expr.noConfusion h
  | _, _, _, _, _, .letE .., ⟨_, h⟩ => Expr.noConfusion h
  | _, _, _, _, _, .lit .., ⟨_, h⟩ => Expr.noConfusion h
  | _, _, _, _, _, .conv (h := D) .., hc => by
      have := TyP.admW_lt_of_const Aw D hc
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .wk (D := D) .., ⟨ls, h⟩ => by
      have := TyP.admW_lt_of_const Aw D ⟨ls, lift_eq_const_k h⟩
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .esub (D := D) (hv := hv) .., ⟨ls, h⟩ => by
      rcases instantiate_eq_const_or h with h1 | h2
      · have := TyP.admW_lt_of_const Aw D ⟨ls, h1⟩
        simp only [TyP.wt]; omega
      · have := TyP.admW_lt_of_const Aw hv ⟨ls, h2⟩
        simp only [TyP.wt]; omega
  | _, _, _, _, _, .lsub (D := D) (hv := hv) .., ⟨ls, h⟩ => by
      rcases instantiate_eq_const_or h with h1 | h2
      · have := TyP.admW_lt_of_const Aw D ⟨ls, h1⟩
        simp only [TyP.wt]; omega
      · have := TyP.admW_lt_of_const Aw hv ⟨ls, h2⟩
        simp only [TyP.wt]; omega
  | _, _, _, _, _, .linst (D := D) .., ⟨_, h⟩ => by
      have := TyP.admW_lt_of_const Aw D (instantiateLevels_eq_const_ex h)
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .ewk (D := D) .., hc => by
      have := TyP.admW_lt_of_const Aw D hc
      simp only [TyP.wt]; omega
  | _, _, _, _, _, .cctx (D := D) .., hc => by
      have := TyP.admW_lt_of_const Aw D hc
      simp only [TyP.wt]; omega

/-! ## §3 admission lookups in the whole environment -/

theorem members_extend_self (E : ResolvedEnv) (r : Nat) (m : CheckedMember) :
    (extendEnv E r m).members r = some m := if_pos rfl

theorem members_extend_ne (E : ResolvedEnv) {r r' : Nat} (m : CheckedMember) (h : r ≠ r') :
    (extendEnv E r' m).members r = E.members r := if_neg h

/-- a member's stored type, typed (enriched) in a prefix `E₀` at the member's level arity, and
    lighter than its admission weight. -/
structure TypeAdm (E : ResolvedEnv) (Aw : Nat → Nat) (r : Nat) (m : CheckedMember) : Type where
  E₀ : ResolvedEnv
  ext : EnvExt E₀ E
  u : Level
  hT : TyP E₀ m.arity [] m.mtype (.sort u)
  lt : hT.wt Aw < Aw r

/-- a transparent member's body, typed (enriched) in a prefix `E₀`, and lighter than its admission
    weight. Transparent members have level arity 0. -/
structure DefAdm (E : ResolvedEnv) (Aw : Nat → Nat) (r : Nat) (m : CheckedMember) (b : Expr Nat) :
    Type where
  E₀ : ResolvedEnv
  ext : EnvExt E₀ E
  arity : m.arity = 0
  hv : TyP E₀ 0 [] b m.mtype
  lt : hv.wt Aw < Aw r

def TypeAdm.lift' {E E₁ : ResolvedEnv} {Aw Aw₁ : Nat → Nat} {r : Nat} {m : CheckedMember}
    (a : TypeAdm E Aw r m) (hext : EnvExt E E₁) (hag : AgreeOn E Aw₁ Aw) (hr : Aw₁ r = Aw r) :
    TypeAdm E₁ Aw₁ r m :=
  ⟨a.E₀, envExt_trans a.ext hext, a.u, a.hT, by
    rw [TyP.wt_congr a.hT (agreeOn_mono a.ext hag), hr]; exact a.lt⟩

def DefAdm.lift' {E E₁ : ResolvedEnv} {Aw Aw₁ : Nat → Nat} {r : Nat} {m : CheckedMember}
    {b : Expr Nat} (a : DefAdm E Aw r m b) (hext : EnvExt E E₁) (hag : AgreeOn E Aw₁ Aw)
    (hr : Aw₁ r = Aw r) : DefAdm E₁ Aw₁ r m b :=
  ⟨a.E₀, envExt_trans a.ext hext, a.arity, a.hv, by
    rw [TyP.wt_congr a.hv (agreeOn_mono a.ext hag), hr]; exact a.lt⟩

/-- an old member survives a fresh extension, with its weight. -/
def TypeAdm.step {E : ResolvedEnv} {Aw : Nat → Nat} {r r' : Nat} {m : CheckedMember}
    (m' : CheckedMember) (w : Nat) (hfresh : E.members r' = none) (hr : r ≠ r')
    (a : TypeAdm E Aw r m) : TypeAdm (extendEnv E r' m') (setW Aw r' w) r m :=
  a.lift' (envExt_extendEnv m' hfresh) (agreeOn_setW Aw w hfresh) (setW_ne Aw w hr)

def DefAdm.step {E : ResolvedEnv} {Aw : Nat → Nat} {r r' : Nat} {m : CheckedMember}
    {b : Expr Nat} (m' : CheckedMember) (w : Nat) (hfresh : E.members r' = none) (hr : r ≠ r')
    (a : DefAdm E Aw r m b) : DefAdm (extendEnv E r' m') (setW Aw r' w) r m b :=
  a.lift' (envExt_extendEnv m' hfresh) (agreeOn_setW Aw w hfresh) (setW_ne Aw w hr)

/-- the fresh member's own admission: its derivation, weighed before it, is below `1 + w + …`. -/
theorem fresh_lt {E : ResolvedEnv} {r : Nat} {n : Nat} {e T : Expr Nat} (Aw : Nat → Nat)
    (hfresh : E.members r = none) (D : TyP E n [] e T) (k : Nat) :
    D.wt (setW Aw r (1 + D.wt Aw + k)) < setW Aw r (1 + D.wt Aw + k) r := by
  rw [TyP.wt_congr D (agreeOn_setW Aw _ hfresh), setW_self]; omega

theorem GroupMembersP.ext' : {E : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    {E' : ResolvedEnv} → GroupMembersP E ms E' → EnvExt E E'
  | _, _, _, .nil _ => envExt_refl _
  | _, _, _, .cons (m := m) (hfresh := hfresh) (hrest := hrest) .. =>
      envExt_trans (envExt_extendEnv m hfresh) hrest.ext'

/-- a member with a body is not a group member. -/
theorem GroupMembersP.body_old : {E : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    {E' : ResolvedEnv} → GroupMembersP E ms E' → ∀ {r : Nat} {m : CheckedMember} {b : Expr Nat},
    E'.members r = some m → m.body = some b → E.members r = some m
  | _, _, _, .nil _, _, _, _, h, _ => h
  | _, _, _, .cons (E := E) (r := r') (m := m') (hnobody := hnb) (hrest := hrest) .., r, _, _, h,
      hb => by
      have h' := hrest.body_old h hb
      cases Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm := (members_extend_self E r m').symm.trans h'
          injection hm with hm
          subst hm
          rw [hnb] at hb; exact Option.noConfusion hb
      | isFalse hr => exact (members_extend_ne E m' hr).symm.trans h'

/-- a group keeps the weights of the members before it. -/
theorem GroupMembersP.admW_old : {E : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    {E' : ResolvedEnv} → (g : GroupMembersP E ms E') → (Aw : Nat → Nat) → AgreeOn E (g.admW Aw) Aw
  | _, _, _, .nil _, _ => fun _ _ _ => rfl
  | _, _, _, .cons (r := r') (m := m') (hfresh := hfresh) (hT := hT) (hrest := hrest) .., Aw => by
      intro c mc hc
      have h1 := hrest.admW_old (setW Aw r' (1 + hT.wt Aw)) c mc (envExt_extendEnv m' hfresh c mc hc)
      simp only [GroupMembersP.admW]
      rw [h1]
      exact agreeOn_setW Aw _ hfresh c mc hc

/-- the stored-type derivation of a group member, or of a member before the group (`old`). -/
def GroupMembersP.typeAdm : {E : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    {E' : ResolvedEnv} → (g : GroupMembersP E ms E') → (Aw : Nat → Nat) → {r : Nat} →
    {m : CheckedMember} → E'.members r = some m → (E.members r = some m → TypeAdm E Aw r m) →
    TypeAdm E' (g.admW Aw) r m
  | _, _, _, .nil _, _, _, _, h, old => old h
  | _, _, _, .cons E r' m' _ _ hfresh _ u hT hrest, Aw, r, m, h, old =>
      hrest.typeAdm (setW Aw r' (1 + hT.wt Aw)) h (fun h' => by
        cases Nat.decEq r r' with
        | isTrue hr =>
            subst hr
            have hm := (members_extend_self E r m').symm.trans h'
            injection hm with hm
            subst hm
            exact ⟨E, envExt_extendEnv _ hfresh, u, hT, by
              have := fresh_lt Aw hfresh hT 0
              simp only [Nat.add_zero] at this
              exact this⟩
        | isFalse hr =>
            exact (old ((members_extend_ne E m' hr).symm.trans h')).step m' _ hfresh hr)

/-- `EnvWfP.typeAdm`: every member's stored type has an enriched admission derivation, in a prefix,
    lighter than the member's admission weight. -/
def EnvWfP.typeAdm : {E : ResolvedEnv} → (hE : EnvWfP E) → {r : Nat} → {m : CheckedMember} →
    E.members r = some m → TypeAdm E hE.admW r m
  | _, .empty, _, _, h => Option.noConfusion h
  | _, .axiom E r' A u hE hfresh hA, r, m, h => by
      cases Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm := (members_extend_self E r _).symm.trans h
          injection hm with hm
          subst hm
          exact ⟨E, envExt_extendEnv _ hfresh, u, hA, by
            have := fresh_lt hE.admW hfresh hA 0
            simp only [Nat.add_zero] at this
            exact this⟩
      | isFalse hr =>
          exact (hE.typeAdm ((members_extend_ne E _ hr).symm.trans h)).step _ _ hfresh hr
  | _, .definition E r' A v u hE hfresh hA hv, r, m, h => by
      cases Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm := (members_extend_self E r _).symm.trans h
          injection hm with hm
          subst hm
          exact ⟨E, envExt_extendEnv _ hfresh, u, hA, by
            have := fresh_lt hE.admW hfresh hA (hv.wt hE.admW)
            exact this⟩
      | isFalse hr =>
          exact (hE.typeAdm ((members_extend_ne E _ hr).symm.trans h)).step _ _ hfresh hr
  | _, .thm E r' A p hE hfresh hA hp, r, m, h => by
      cases Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm := (members_extend_self E r _).symm.trans h
          injection hm with hm
          subst hm
          exact ⟨E, envExt_extendEnv _ hfresh, .zero, hA, by
            have := fresh_lt hE.admW hfresh hA (hp.wt hE.admW)
            exact this⟩
      | isFalse hr =>
          exact (hE.typeAdm ((members_extend_ne E _ hr).symm.trans h)).step _ _ hfresh hr
  | _, .opaque E r' A v u hE hfresh hA hv, r, m, h => by
      cases Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm := (members_extend_self E r _).symm.trans h
          injection hm with hm
          subst hm
          exact ⟨E, envExt_extendEnv _ hfresh, u, hA, by
            have := fresh_lt hE.admW hfresh hA (hv.wt hE.admW)
            exact this⟩
      | isFalse hr =>
          exact (hE.typeAdm ((members_extend_ne E _ hr).symm.trans h)).step _ _ hfresh hr
  | _, .group _ _ _ hE hmem, _, _, h => hmem.typeAdm hE.admW h (fun h' => hE.typeAdm h')

/-- `EnvWfP.defAdm`: a transparent member's body has an enriched admission derivation, in a prefix,
    lighter than the member's admission weight. Only `definition` steps are transparent. -/
def EnvWfP.defAdm : {E : ResolvedEnv} → (hE : EnvWfP E) → {r : Nat} → {m : CheckedMember} →
    {b : Expr Nat} → E.members r = some m → m.body = some b → transparent m.mclass = true →
    DefAdm E hE.admW r m b
  | _, .empty, _, _, _, h, _, _ => Option.noConfusion h
  | _, .axiom E r' A u hE hfresh hA, r, m, b, h, hb, htr => by
      cases Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm := (members_extend_self E r _).symm.trans h
          injection hm with hm
          subst hm
          exact Bool.noConfusion htr
      | isFalse hr =>
          exact (hE.defAdm ((members_extend_ne E _ hr).symm.trans h) hb htr).step _ _ hfresh hr
  | _, .definition E r' A v u hE hfresh hA hv, r, m, b, h, hb, htr => by
      cases Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm := (members_extend_self E r _).symm.trans h
          injection hm with hm
          subst hm
          injection hb with hb
          subst hb
          exact ⟨E, envExt_extendEnv _ hfresh, rfl, hv, by
            have := fresh_lt hE.admW hfresh hv (hA.wt hE.admW)
            have e : 1 + hv.wt hE.admW + hA.wt hE.admW = 1 + hA.wt hE.admW + hv.wt hE.admW := by
              omega
            rw [e] at this
            exact this⟩
      | isFalse hr =>
          exact (hE.defAdm ((members_extend_ne E _ hr).symm.trans h) hb htr).step _ _ hfresh hr
  | _, .thm E r' A p hE hfresh hA hp, r, m, b, h, hb, htr => by
      cases Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm := (members_extend_self E r _).symm.trans h
          injection hm with hm
          subst hm
          exact Bool.noConfusion htr
      | isFalse hr =>
          exact (hE.defAdm ((members_extend_ne E _ hr).symm.trans h) hb htr).step _ _ hfresh hr
  | _, .opaque E r' A v u hE hfresh hA hv, r, m, b, h, hb, htr => by
      cases Nat.decEq r r' with
      | isTrue hr =>
          subst hr
          have hm := (members_extend_self E r _).symm.trans h
          injection hm with hm
          subst hm
          exact Bool.noConfusion htr
      | isFalse hr =>
          exact (hE.defAdm ((members_extend_ne E _ hr).symm.trans h) hb htr).step _ _ hfresh hr
  | _, .group _ _ _ hE hmem, r, m, _, h, hb, htr =>
      let h₀ := hmem.body_old h hb
      (hE.defAdm h₀ hb htr).lift' hmem.ext' (hmem.admW_old hE.admW) (hmem.admW_old hE.admW r m h₀)

/-! ## §4 the call rows -/

/-- THE δ ROW (`S1` §3.3). Every atom of the body's admission derivation lies below the δ node, at
    the environment's own admission weights. With `dmStep_of_below`, ES(δ)'s call on the transported
    admission derivation (`linst`/`wk`/`ewk` add no atoms) is a `DMStep`. -/
theorem delta_adm_below {E : ResolvedEnv} (hE : EnvWfP E) {n : Nat} {Γ : LCtx} {r : Nat}
    {ls : List Level} {m : CheckedMember} {b : Expr Nat} (hres : E.members r = some m)
    (hbody : m.body = some b) (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)) :
    ∀ y ∈ (hE.defAdm hres hbody htr).hv.atoms hE.admW,
      y < (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).wt hE.admW := by
  intro y hy
  have h1 := TyP.atoms_le hE.admW _ y hy
  have h2 := (hE.defAdm hres hbody htr).lt
  have h3 := TyP.admW_lt_of_const hE.admW dl ⟨ls, rfl⟩
  simp only [CvP.wt]; omega

/-- THE CONST ROW (`S1` §3.3). Every atom of the stored type's admission derivation lies below the
    const node. PB(const) and CTS consume it. -/
theorem const_adm_below {E : ResolvedEnv} (hE : EnvWfP E) {n : Nat} {Γ : LCtx} {r : Nat}
    {ls ls₀ : List Level} {m : CheckedMember} {u : Level} (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true) (hls : eqNList ls ls₀)
    (hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)) :
    ∀ y ∈ (hE.typeAdm hres).hT.atoms hE.admW,
      y < (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT).wt hE.admW := by
  intro y hy
  have h1 := TyP.atoms_le hE.admW _ y hy
  have h2 := (hE.typeAdm hres).lt
  simp only [TyP.wt]; omega

/-! ## §5 transport strips -/

theorem TyP.atoms_ne_nil (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → (D : TyP E n Γ e T) → D.atoms Aw ≠ []
  | _, _, _, _, _, .wk (D := D) .. => by simp only [TyP.atoms]; exact TyP.atoms_ne_nil Aw D
  | _, _, _, _, _, .esub (D := D) .. => by
      simp only [TyP.atoms]
      intro h
      exact TyP.atoms_ne_nil Aw D (List.append_eq_nil.mp (List.append_eq_nil.mp h).1).1
  | _, _, _, _, _, .lsub (D := D) .. => by
      simp only [TyP.atoms]
      intro h
      exact TyP.atoms_ne_nil Aw D (List.append_eq_nil.mp (List.append_eq_nil.mp h).1).1
  | _, _, _, _, _, .linst (D := D) .. => by simp only [TyP.atoms]; exact TyP.atoms_ne_nil Aw D
  | _, _, _, _, _, .ewk (D := D) .. => by simp only [TyP.atoms]; exact TyP.atoms_ne_nil Aw D
  | _, _, _, _, _, .cctx (D := D) .. => by
      simp only [TyP.atoms]
      intro h
      exact TyP.atoms_ne_nil Aw D (List.append_eq_nil.mp h).1
  | _, _, _, _, _, .sort .. | _, _, _, _, _, .bvar .. | _, _, _, _, _, .const ..
  | _, _, _, _, _, .pi .. | _, _, _, _, _, .lam .. | _, _, _, _, _, .app ..
  | _, _, _, _, _, .letE .. | _, _, _, _, _, .lit .. | _, _, _, _, _, .conv .. => by
      simp only [TyP.atoms]; exact List.cons_ne_nil _ _

/-- a conversion's atom multiset is never empty: a rule node is one atom, and a transport keeps
    its inner derivation's atoms. -/
theorem CvP.atoms_ne_nil (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} → (h : CvP E n Γ a b T) → h.atoms Aw ≠ []
  | _, _, _, _, _, _, .wk (h := h) .. => by simp only [CvP.atoms]; exact CvP.atoms_ne_nil Aw h
  | _, _, _, _, _, _, .esub (h := h) .. => by
      simp only [CvP.atoms]
      intro hn
      exact CvP.atoms_ne_nil Aw h (List.append_eq_nil.mp (List.append_eq_nil.mp hn).1).1
  | _, _, _, _, _, _, .linst (h := h) .. => by simp only [CvP.atoms]; exact CvP.atoms_ne_nil Aw h
  | _, _, _, _, _, _, .ewk (h := h) .. => by simp only [CvP.atoms]; exact CvP.atoms_ne_nil Aw h
  | _, _, _, _, _, _, .cctx (h := h) .. => by
      simp only [CvP.atoms]
      intro hn
      exact CvP.atoms_ne_nil Aw h (List.append_eq_nil.mp hn).1
  | _, _, _, _, _, _, .refl .. | _, _, _, _, _, _, .symm .. | _, _, _, _, _, _, .trans ..
  | _, _, _, _, _, _, .beta .. | _, _, _, _, _, _, .zeta .. | _, _, _, _, _, _, .zetaLocal ..
  | _, _, _, _, _, _, .delta .. | _, _, _, _, _, _, .iota .. | _, _, _, _, _, _, .lit ..
  | _, _, _, _, _, _, .app .. | _, _, _, _, _, _, .lam .. | _, _, _, _, _, _, .pi ..
  | _, _, _, _, _, _, .letE .. | _, _, _, _, _, _, .sorts .. | _, _, _, _, _, _, .consts ..
  | _, _, _, _, _, _, .eta .. | _, _, _, _, _, _, .irr .. | _, _, _, _, _, _, .tyConv ..
  | _, _, _, _, _, _, .fsub .. => by
      simp only [CvP.atoms]; exact List.cons_ne_nil _ _

/-- stripping `wk` from a conversion: the atoms are literally equal and the weight drops by one. -/
theorem cvp_strip_wk (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (d : LocalDecl) (c : Nat) (h : CvP E n Γ a b T) :
    Prod.Lex DMStep (fun x y : Nat => x < y) (h.atoms Aw, h.wt Aw)
      ((CvP.wk E n Γ a b T d c h).atoms Aw, (CvP.wk E n Γ a b T d c h).wt Aw) := by
  have e1 : (CvP.wk E n Γ a b T d c h).atoms Aw = h.atoms Aw := by simp only [CvP.atoms]
  have e2 : (CvP.wk E n Γ a b T d c h).wt Aw = 1 + h.wt Aw := by simp only [CvP.wt]
  rw [e1, e2]
  exact Prod.Lex.right _ (by omega)

/-- stripping `linst` from a conversion, likewise. -/
theorem cvp_strip_linst (Aw : Nat → Nat) {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (ls : List Level) (hls : levelsBounded n ls = true) (hlen : ls.length = a')
    (h : CvP E a' Γ a b T) :
    Prod.Lex DMStep (fun x y : Nat => x < y) (h.atoms Aw, h.wt Aw)
      ((CvP.linst E a' n Γ a b T ls hls hlen h).atoms Aw,
        (CvP.linst E a' n Γ a b T ls hls hlen h).wt Aw) := by
  have e1 : (CvP.linst E a' n Γ a b T ls hls hlen h).atoms Aw = h.atoms Aw := by
    simp only [CvP.atoms]
  have e2 : (CvP.linst E a' n Γ a b T ls hls hlen h).wt Aw = 1 + h.wt Aw := by simp only [CvP.wt]
  rw [e1, e2]
  exact Prod.Lex.right _ (by omega)

/-- stripping `esub` from a conversion drops the parameters' atoms: a `DMStep`. -/
theorem cvp_strip_esub (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T t v : Expr Nat} {j : Nat} {u : Level} (h : CvP E n Γ a b T)
    (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    DMStep (h.atoms Aw) ((CvP.esub E n Γ a b T t v j u h hget hv hvT).atoms Aw) := by
  have e1 : (CvP.esub E n Γ a b T t v j u h hget hv hvT).atoms Aw =
      h.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw := by simp only [CvP.atoms]
  rw [e1]
  refine ⟨hv.atoms Aw ++ hvT.atoms Aw, [], h.atoms Aw, ?_, ?_, List.Perm.refl _, ?_⟩
  · intro hn
    exact TyP.atoms_ne_nil Aw hv (List.append_eq_nil.mp hn).1
  · rw [List.append_assoc]; exact List.perm_append_comm
  · intro y hy; exact absurd hy (List.not_mem_nil _)

/-- stripping `cctx` from a conversion drops the domain conversion's atoms: a `DMStep`. -/
theorem cvp_strip_cctx (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T A A' : Expr Nat} {u : Level} (h : CvP E n (.assumption A :: Γ) a b T)
    (hA : CvP E n Γ A A' (.sort u)) :
    DMStep (h.atoms Aw) ((CvP.cctx E n Γ a b T A A' u h hA).atoms Aw) := by
  have e1 : (CvP.cctx E n Γ a b T A A' u h hA).atoms Aw = h.atoms Aw ++ hA.atoms Aw := by
    simp only [CvP.atoms]
  rw [e1]
  refine ⟨hA.atoms Aw, [], h.atoms Aw, ?_, ?_, List.Perm.refl _, ?_⟩
  · exact CvP.atoms_ne_nil Aw hA
  · exact List.perm_append_comm
  · intro y hy; exact absurd hy (List.not_mem_nil _)

/-- stripping `cctx` from a typing, likewise. -/
theorem typ_strip_cctx (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T A A' : Expr Nat} {u : Level} (D : TyP E n (.assumption A :: Γ) e T)
    (hA : CvP E n Γ A A' (.sort u)) :
    DMStep (D.atoms Aw) ((TyP.cctx E n Γ e T A A' u D hA).atoms Aw) := by
  have e1 : (TyP.cctx E n Γ e T A A' u D hA).atoms Aw = D.atoms Aw ++ hA.atoms Aw := by
    simp only [TyP.atoms]
  rw [e1]
  refine ⟨hA.atoms Aw, [], D.atoms Aw, ?_, ?_, List.Perm.refl _, ?_⟩
  · exact CvP.atoms_ne_nil Aw hA
  · exact List.perm_append_comm
  · intro y hy; exact absurd hy (List.not_mem_nil _)

/-- a `fsub` child is strictly lighter, so a call on it is a `DMStep` off the node's one atom. -/
theorem fsub_child_below (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a S))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a S)) :
    let hnode := CvP.fsub E n Γ A B S a b u hB hA hab dl dr
    DMStep (hB.atoms Aw) (hnode.atoms Aw) ∧ DMStep (hab.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.fsub E n Γ A B S a b u hB hA hab dl dr
  have hwB : hB.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwA : hab.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hat : hnode.atoms Aw = [hnode.wt Aw] := by simp only [CvP.atoms]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hat, ← List.append_nil (hB.atoms Aw)]; exact dmStep_of_below (atoms_lt_of_wt_lt Aw hB hwB)
  · rw [hat, ← List.append_nil (hab.atoms Aw)]; exact dmStep_of_below (cvp_atoms_lt_of_wt_lt Aw hab hwA)
  · rw [hat, ← List.append_nil (dl.atoms Aw)]; exact dmStep_of_below (atoms_lt_of_wt_lt Aw dl hwl)
  · rw [hat, ← List.append_nil (dr.atoms Aw)]; exact dmStep_of_below (atoms_lt_of_wt_lt Aw dr hwr)

/-- stripping `esub` from a typing, likewise (CL's same-substitution pairs). -/
theorem typ_strip_esub (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A t v : Expr Nat} {j : Nat} {u : Level} (D : TyP E n Γ e A)
    (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    DMStep (D.atoms Aw) ((TyP.esub E n Γ e A t v j u D hget hv hvT).atoms Aw) := by
  have e1 : (TyP.esub E n Γ e A t v j u D hget hv hvT).atoms Aw =
      D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw := by simp only [TyP.atoms]
  rw [e1]
  refine ⟨hv.atoms Aw ++ hvT.atoms Aw, [], D.atoms Aw, ?_, ?_, List.Perm.refl _, ?_⟩
  · intro hn
    exact TyP.atoms_ne_nil Aw hv (List.append_eq_nil.mp hn).1
  · rw [List.append_assoc]; exact List.perm_append_comm
  · intro y hy; exact absurd hy (List.not_mem_nil _)

/-! ## §6 pins -/

/-- PIN: the empty environment, extended by one axiom `P : Prop`. -/
def pinAxEnv : EnvWfP (extendEnv emptyEnv 7 ⟨.axiomM, 0, .sort .zero, none⟩) :=
  .axiom emptyEnv 7 (.sort .zero) (.succ .zero) .empty rfl pinSortP

/-- PIN: the axiom's admission weight is its type derivation's weight plus one. -/
theorem pinAxEnv_admW : pinAxEnv.admW 7 = 2 := rfl

/-- PIN (the const row, non-vacuously): the stored-type admission derivation of the axiom is found,
    and it weighs less than the axiom's admission weight. -/
theorem pinAxEnv_typeAdm_lt :
    (pinAxEnv.typeAdm (r := 7) (members_extend_self _ _ _)).hT.wt pinAxEnv.admW < 2 :=
  (pinAxEnv.typeAdm (r := 7) (members_extend_self _ _ _)).lt

end Rcic.Syn

#print axioms Rcic.Syn.agreeOn_mono
#print axioms Rcic.Syn.agreeOn_setW
#print axioms Rcic.Syn.TyP.wt_congr
#print axioms Rcic.Syn.CvP.wt_congr
#print axioms Rcic.Syn.lift_eq_const_k
#print axioms Rcic.Syn.instantiate_eq_const_or
#print axioms Rcic.Syn.instantiateLevels_eq_const_ex
#print axioms Rcic.Syn.TyP.admW_lt_of_const
#print axioms Rcic.Syn.members_extend_self
#print axioms Rcic.Syn.members_extend_ne
#print axioms Rcic.Syn.TypeAdm.lift'
#print axioms Rcic.Syn.DefAdm.lift'
#print axioms Rcic.Syn.fresh_lt
#print axioms Rcic.Syn.GroupMembersP.ext'
#print axioms Rcic.Syn.GroupMembersP.body_old
#print axioms Rcic.Syn.GroupMembersP.admW_old
#print axioms Rcic.Syn.GroupMembersP.typeAdm
#print axioms Rcic.Syn.EnvWfP.typeAdm
#print axioms Rcic.Syn.EnvWfP.defAdm
#print axioms Rcic.Syn.delta_adm_below
#print axioms Rcic.Syn.const_adm_below
#print axioms Rcic.Syn.TyP.atoms_ne_nil
#print axioms Rcic.Syn.CvP.atoms_ne_nil
#print axioms Rcic.Syn.cvp_strip_cctx
#print axioms Rcic.Syn.typ_strip_cctx
#print axioms Rcic.Syn.fsub_child_below
#print axioms Rcic.Syn.cvp_strip_wk
#print axioms Rcic.Syn.cvp_strip_linst
#print axioms Rcic.Syn.cvp_strip_esub
#print axioms Rcic.Syn.typ_strip_esub
#print axioms Rcic.Syn.pinAxEnv_admW
#print axioms Rcic.Syn.pinAxEnv_typeAdm_lt
