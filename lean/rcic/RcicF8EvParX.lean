import rcic.RcicF8DTileStep
import rcic.RcicF8JEndpoints

/-!
# `RcicF8EvParX` — W-J-STEP-EMBED on a separate carrier (cc 10:10Z, case B)

`DProcWf` (`RcicF8DTileBase.lean`) is a total `Σ'`, and `DOpt` is only `stay | step`.
The five step kinds therefore do not become `EvPar` constructors: that would make the
landed total diamond non-exhaustive. They live here. `embed` is the landed carrier.
Landed `dProcWf` / `evParDiamondWf` are not modified and take no `X`.

`BVarZetaPayload.substVal` keeps its dropped-context `hvt` (cc 05:30: removing it is
prefix strengthening of `HasTyT`). `substLetVal` is the same surface. Neither calls
`PEqT.instantiate_pair`. The stored-ζ entry (`storedZeta`, cc 11:41Z) reads that
typing with `ctxWfTLookupValueAtDrop` and consumes `JEndpoints.zetaLocalPacket`.
Its context origin is `StoredCtxOrigin`, not an `EvTy.lit`. Pairs the new diamond
cannot join return a named `none`
(`consts×delta`, `delta×consts`, `lam` when both bodies move or the codomain indices
differ). A diagonal app×app or letE×letE stays at the common target via `rightTy`.
An identity app or letE against a different target replays one of the two
inputs inside their leaves. Identity first (`source = first target`) replays
the second input (`.step` of that input, `.stay` of its `rightTy`). Identity
second (`source = second target`, targets unequal) replays the first input
(`.stay` of its `rightTy`, `.step` of that input). Neither replay calls
`XProc`. The remaining app pair is `evParAppGenJoinX`. Equal `T₀` builds
`c₀` by reflexivity and reads the second function step with `readConv`.
The centre is `appCornerJoin`. `outerLeft` and `outerRight` apply that
side's component legs, so the centre is `app f⋆ a⋆` and both outer legs
may step. `.stay` is the endpoint typing; `.step` is the diamond's own
forward `DStep`. No `ParRedT` is reversed. A right-staying pair still
closes an `EvParX` at `app f₂ a₂`, a left-staying pair at `app f₁ a₁`.
A mixed centre is those outer legs and is not an `EvParX` at the original
app index (`evParXAppCentre`). Unequal `T₀` is `evParXAppT0`. An
instantiation that is neither definitional nor an `=ₙ` sort is
`evParXAppInst`.
The remaining letE pair is `evParLetEGenJoinX`, and only when the first
binder and value stay put. A moved binder or value keeps the body step in
the source let context and returns `evParXLetECentre` or `evParXLetENoSrc`.
Not a `some` for every unequal pair. Star closure is #7156.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- Let-substituted materializer for `BVarZetaPayload`. `hvt` is the substitutend's
    typing in `Γ.drop (j + 1)`, the premise cc 05:30 keeps explicit. -/
def BVarZetaPayload.substLetVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {i : Nat} {v' T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hvty : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    (hvt : HasTyT E n (Γ.drop (j + 1)) w t)
    (p : BVarZetaPayload R Γ i v' T) :
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) (.bvar i))
      (instantiate j (lift 0 j w) (lift 0 (i + 1) v'))
      (instantiate j (lift 0 j w) T) :=
  match p with
  | .mk A v T₀ h hv hl hr idx => by
    have idx' := tyConvT_substLetS hcl hinst t w (idx.val hcl hinst) hget hvty
    by_cases hij : i = j
    · subst hij
      have h' : Γ[i]? = some (.letBinding A v) :=
        (List.get?_eq_getElem? Γ i).symm ▸ h
      rw [hget] at h'
      injection h' with hge
      injection hge with hA hv0
      subst hA hv0
      simp only [instantiate, if_pos rfl]
      rw [instantiate_lift_cancel (i + 1) 0 i (lift 0 i w)
        (Nat.zero_le i) (Nat.lt_succ_self i)]
      have hdrop : (substRemove w i Γ).drop i = Γ.drop (i + 1) := by
        rw [substRemove_drop, if_pos (Nat.le_refl i), Nat.sub_self]
        have hd : substRemove w 0 (Γ.drop i) = (Γ.drop i).drop 1 := by
          cases Γ.drop i <;> simp [substRemove]
        rw [hd, List.drop_drop]
      have hpre : (substRemove w i Γ).take i ++ Γ.drop (i + 1) = substRemove w i Γ := by
        rw [← hdrop]; exact List.take_append_drop _ _
      have hlt0 : i < Γ.length := (List.getElem?_eq_some_iff.mp hget).1
      have hlen : ((substRemove w i Γ).take i).length = i := by
        rw [List.length_take, substRemove_length, if_pos hlt0]
        omega
      have hvL := parRedT_lift_lctx hcl
        (fun {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat}
            (h : PEqLeafT E n Γ p q T) =>
          show PEqLeafT E n (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T) from
            ⟨PEqT.liftT (c := c) hcl d' h.1,
             hasTyTWeaken (c := c) d' hcl h.2.1,
             hasTyTWeaken (c := c) d' hcl h.2.2⟩)
        ((substRemove w i Γ).take i) (hv.val hcl hinst)
      rw [hlen] at hvL
      obtain ⟨A0, hlk0, hcv⟩ := hasTyTInv_bvar (hl.val hcl hinst) rfl
      have hlk : lookupType Γ i = some (lift 0 (i + 1) t) := lookupType_get_letBinding hget
      rw [hlk] at hlk0
      injection hlk0 with hA0
      subst hA0
      have hcvT := TyConvT.trans Γ (lift 0 (i + 1) t) T₀ T hcv (idx.val hcl hinst)
      have hcv' := tyConvT_substLetS hcl hinst t w hcvT hget hvty
      rw [instantiate_lift_cancel (i + 1) 0 i (lift 0 i w)
        (Nat.zero_le i) (Nat.lt_succ_self i)] at hcv'
      rw [← hpre] at hcv'
      rw [← hpre]
      exact .conv _ _ _ _ _ hvL hcv'
    · by_cases hlt : i < j
      · simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)]
        have hlkV := lookupValue_of_get?_let h
        have hmap := lookupValue_substRemove_lt (v := w) hlt hlkV
        obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
        have hsΓ : lift 0 (i + 1) (lift 0 (j - i - 1) w) = lift 0 j w := by
          have hc := lift_zero_comp (i + 1) (j - i - 1) w
          rw [show i + 1 + (j - i - 1) = j from by omega] at hc
          exact hc
        have hcomm (e : Expr Nat) :
            instantiate j (lift 0 j w) (lift 0 (i + 1) e) =
              lift 0 (i + 1) (instantiate (j - i - 1) (lift 0 (j - i - 1) w) e) := by
          have h1 := lift_instantiate_high (i + 1) 0 (j - i - 1)
            (lift 0 (j - i - 1) w) (Nat.zero_le _) e
          rw [show i + 1 + (j - i - 1) = j from by omega, hsΓ] at h1
          exact h1.symm
        have hstored : stored = instantiate (j - i - 1) (lift 0 (j - i - 1) w) v :=
          lift_zero_amount_inj (i + 1) (heq.symm.trans (hcomm v))
        have hdrop : (substRemove w j Γ).drop (i + 1) =
            substRemove w (j - i - 1) (Γ.drop (i + 1)) := by
          rw [substRemove_drop, if_pos (by omega : i + 1 ≤ j)]
          congr 1
        have hgetD : (Γ.drop (i + 1))[j - i - 1]? = some (.letBinding t w) := by
          rw [← List.get?_eq_getElem?, get?_drop, show j - i - 1 + (i + 1) = j from by omega]
          exact (List.get?_eq_getElem? Γ j).symm ▸ hget
        have hvtD : HasTyT E n ((Γ.drop (i + 1)).drop (j - i - 1 + 1)) w t := by
          have hd : (Γ.drop (i + 1)).drop (j - i - 1 + 1) = Γ.drop (j + 1) := by
            rw [List.drop_drop]; congr 1; omega
          rw [hd]; exact hvt
        have hvtyD := subst_hvty_of_drop_let hcl hgetD hvtD
        have hv' := hv.substLetVal0 hcl hinst (j - i - 1) hgetD hvtyD
        rw [← hdrop] at hv'
        have hA' : A' = instantiate (j - i - 1) (lift 0 (j - i - 1) w) A := by
          have hsrc : lookupType Γ i = some (lift 0 (i + 1) A) := by simp only [lookupType, h]
          have hltTy := lookupType_substRemove_lt (v := w) hlt hsrc
          have hsrcTy : lookupType (substRemove w j Γ) i = some (lift 0 (i + 1) A') := by
            simp only [lookupType, hg']
          rw [hsrcTy] at hltTy
          exact lift_zero_amount_inj (i + 1) ((Option.some.inj hltTy).trans (hcomm A))
        rw [← hstored, ← hA'] at hv'
        have hl' := hasTyT_substLetS hcl hinst t w (hl.val hcl hinst) hget hvty
        have hr' := hasTyT_substLetS hcl hinst t w (hr.val hcl hinst) hget hvty
        simp only [instantiate, if_neg hij, if_neg (by omega : ¬ j < i)] at hl' hr'
        rw [hcomm v'] at hr'
        exact (hcomm v') ▸ bvarZetaStep hg' hv' hl' hr' idx'
      · have hgt : j < i := by omega
        simp only [instantiate, if_neg hij, if_pos hgt]
        have hlkV := lookupValue_of_get?_let h
        have hmap := lookupValue_substRemove_gt (v := w) hgt hlkV
        obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
        have hcan (e : Expr Nat) :
            instantiate j (lift 0 j w) (lift 0 (i + 1) e) = lift 0 i e :=
          instantiate_lift_cancel (i + 1) 0 j (lift 0 j w) (Nat.zero_le j) (by omega) e
        have hi1 : i - 1 + 1 = i := by omega
        have hstored : stored = v := by
          have heq' : lift 0 i stored = lift 0 i v := by
            have h1 := heq.symm.trans (hcan v); rwa [hi1] at h1
          exact lift_zero_amount_inj i heq'
        have hA' : A' = A := by
          have hsrc : lookupType Γ i = some (lift 0 (i + 1) A) := by simp only [lookupType, h]
          have hltTy := lookupType_substRemove_gt (v := w) hgt hsrc
          have hsrcTy : lookupType (substRemove w j Γ) (i - 1) =
              some (lift 0 ((i - 1) + 1) A') := by simp only [lookupType, hg']
          rw [hsrcTy] at hltTy
          have heq' : lift 0 i A' = lift 0 i A := by
            have h1 := (Option.some.inj hltTy).trans (hcan A); rwa [hi1] at h1
          exact lift_zero_amount_inj i heq'
        have hdrop : (substRemove w j Γ).drop i = Γ.drop (i + 1) := by
          rw [substRemove_drop, if_neg (by omega : ¬ i ≤ j)]
        have hv' : ParRedT (PEqLeafT E n) E n
            ((substRemove w j Γ).drop (i - 1 + 1)) v v' A := by
          rw [hi1]; exact hdrop ▸ (hv.val hcl hinst)
        have hl' := hasTyT_substLetS hcl hinst t w (hl.val hcl hinst) hget hvty
        have hr' := hasTyT_substLetS hcl hinst t w (hr.val hcl hinst) hget hvty
        simp only [instantiate, if_neg hij, if_pos hgt] at hl' hr'
        rw [hcan v'] at hr'
        have hr'' : HasTyT E n (substRemove w j Γ)
            (lift 0 (i - 1 + 1) v') (instantiate j (lift 0 j w) T₀) := by
          rw [hi1]; exact hr'
        have htgt : lift 0 i v' = instantiate j (lift 0 j w) (lift 0 (i + 1) v') :=
          (hcan v').symm
        rw [← hstored, ← hA'] at hv'
        exact htgt ▸ (hi1 ▸ bvarZetaStep hg' hv' hl' hr'' idx')

/-! ### the carrier -/

inductive EvParX (R : List (Jd E n)) : LCtx → Expr Nat → Expr Nat → Expr Nat → Type where
  | embed {Γ a b T} (D : EvPar R Γ a b T) : EvParX R Γ a b T
  | delta {Γ r ls body T} (p : DeltaPayload R Γ r ls body T) :
      EvParX R Γ (.const r ls) (instantiateLevels ls body) T
  | bvarZeta {Γ i v' T} (p : BVarZetaPayload R Γ i v' T) :
      EvParX R Γ (.bvar i) (lift 0 (i + 1) v') T
  | lam {Γ A body A' body' T} (p : LamPayload R Γ A body A' body' T) :
      EvParX R Γ (.lam A body) (.lam A' body') T
  | app {Γ f a f' a' T} (p : AppPayload R Γ f a f' a' T) :
      EvParX R Γ (.app f a) (.app f' a') T
  | letE {Γ A value body A' value' body' T}
      (p : LetEPayload R Γ A value body A' value' body' T) :
      EvParX R Γ (.letE A value body) (.letE A' value' body') T

def EvParX.castR {Γ : LCtx} {a b b' T : Expr Nat} (hb : b = b') (h : EvParX R Γ a b T) :
    EvParX R Γ a b' T := by
  subst hb; exact h

def EvParX.dcast {Γ Γ' : LCtx} {a a' b b' T T' : Expr Nat}
    (hΓ : Γ = Γ') (ha : a = a') (hb : b = b') (hT : T = T') (h : EvParX R Γ a b T) :
    EvParX R Γ' a' b' T' := by
  subst hΓ; subst ha; subst hb; subst hT; exact h

def EvParX.leaves : {Γ : LCtx} → {a b T : Expr Nat} → EvParX R Γ a b T → List (Jd E n)
  | _, _, _, _, .embed D => D.leaves
  | _, _, _, _, .delta p => p.leaves
  | _, _, _, _, .bvarZeta p => p.leaves
  | _, _, _, _, .lam p => p.leaves
  | _, _, _, _, .app p => p.leaves
  | _, _, _, _, .letE p => p.leaves

def EvParX.rightTy : {Γ : LCtx} → {a b T : Expr Nat} → EvParX R Γ a b T → EvTy R Γ b T
  | _, _, _, _, .embed D => D.rightTy
  | _, _, _, _, .delta p => p.rightTy
  | _, _, _, _, .bvarZeta p => p.rightTy
  | _, _, _, _, .lam p => p.rightTy
  | _, _, _, _, .app p => p.rightTy
  | _, _, _, _, .letE p => p.rightTy

theorem EvParX.rightTy_leaves : {Γ : LCtx} → {a b T : Expr Nat} → (D : EvParX R Γ a b T) →
    ∀ ℓ ∈ D.rightTy.leaves, ℓ ∈ D.leaves
  | _, _, _, _, .embed D => D.rightTy_leaves
  | _, _, _, _, .delta p => p.rightTy_leaves
  | _, _, _, _, .bvarZeta p => p.rightTy_leaves
  | _, _, _, _, .lam p => p.rightTy_leaves
  | _, _, _, _, .app p => p.rightTy_leaves
  | _, _, _, _, .letE p => p.rightTy_leaves

def EvParX.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {a b T : Expr Nat} → EvParX R Γ a b T →
      ParRedT (PEqLeafT E n) E n Γ a b T
  | _, _, _, _, .embed D => D.val hcl hinst
  | _, _, _, _, .delta p => p.val hcl hinst
  | _, _, _, _, .bvarZeta p => p.val hcl hinst
  | _, _, _, _, .lam p => p.val hcl hinst
  | _, _, _, _, .app p => p.val hcl hinst
  | _, _, _, _, .letE p => p.val hcl hinst

/-- `hvt` is used only by `bvarZeta` (cc 05:30). The other arms are `hcl`/`hinst`. -/
def EvParX.substVal0 (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hvty : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    (hvt : HasTyT E n (Γ.drop (j + 1)) w t) :
    EvParX R Γ a b T →
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) a) (instantiate j (lift 0 j w) b)
      (instantiate j (lift 0 j w) T)
  | .embed D => D.substVal0 hcl hinst j hget hvty
  | .delta p => p.substVal hcl hinst j hget hvty
  | .bvarZeta p => p.substVal hcl hinst j hget hvty hvt
  | .lam p => p.substVal hcl hinst j hget hvty
  | .app p => p.substVal hcl hinst j hget hvty
  | .letE p => p.substVal hcl hinst j hget hvty

def EvParX.substLetVal0 (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {a b T t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hvty : HasTyT E n (substRemove w j Γ) (lift 0 j w) (lift 0 j t))
    (hvt : HasTyT E n (Γ.drop (j + 1)) w t) :
    EvParX R Γ a b T →
    ParRedT (PEqLeafT E n) E n (substRemove w j Γ)
      (instantiate j (lift 0 j w) a) (instantiate j (lift 0 j w) b)
      (instantiate j (lift 0 j w) T)
  | .embed D => D.substLetVal0 hcl hinst j hget hvty
  | .delta p => p.substLetVal hcl hinst j hget hvty
  | .bvarZeta p => p.substLetVal hcl hinst j hget hvty hvt
  | .lam p => p.substLetVal hcl hinst j hget hvty
  | .app p => p.substLetVal hcl hinst j hget hvty
  | .letE p => p.substLetVal hcl hinst j hget hvty

def EvParX.widen (hr : ∀ x ∈ R, x ∈ R') :
    {Γ : LCtx} → {a b T : Expr Nat} → EvParX R Γ a b T → EvParX R' Γ a b T
  | _, _, _, _, .embed D => .embed (D.widen hr)
  | _, _, _, _, .delta p => .delta (p.widen hr)
  | _, _, _, _, .bvarZeta p => .bvarZeta (p.widen hr)
  | _, _, _, _, .lam p => .lam (p.widen hr)
  | _, _, _, _, .app p => .app (p.widen hr)
  | _, _, _, _, .letE p => .letE (p.widen hr)

/-! ### readers -/

def EvParX.readConv {Γ : LCtx} {a b T T' : Expr Nat} :
    EvParX R Γ a b T → EvTc R Γ T T' → EvParX R Γ a b T'
  | .embed D, c => .embed (D.readConv c)
  | .delta p, c => .delta (p.readConv c)
  | .bvarZeta p, c => .bvarZeta (p.readConv c)
  | .lam p, c => .lam (p.readConv c)
  | .app p, c => .app (p.readConv c)
  | .letE p, c => .letE (p.readConv c)

/-- Insert sits in the tail of a `bvarZeta` (`i < k`). -/
def bvarZetaReadWkLt (d : LocalDecl) (k : Nat) {Γ : LCtx} {i : Nat}
    {v' T : Expr Nat} (hic : i < k)
    (A v T₀ : Expr Nat) (h : Γ.get? i = some (.letBinding A v))
    (hv' : EvPar R (insertAt d (k - i - 1) (Γ.drop (i + 1)))
      (lift (k - i - 1) 1 v) (lift (k - i - 1) 1 v') (lift (k - i - 1) 1 A))
    (hl : EvTy R Γ (.bvar i) T₀)
    (hr : EvTy R Γ (lift 0 (i + 1) v') T₀)
    (idx : EvTc R Γ T₀ T) :
    EvParX R (insertAt d k Γ) (lift k 1 (.bvar i))
      (lift k 1 (lift 0 (i + 1) v')) (lift k 1 T) := by
  have hlen := get?_some_lt h
  have hg := insertAt_get?_lt d (Γ := Γ) hic h
  simp only [liftDecl] at hg
  have hdrop := insertAt_drop_lt d (Γ := Γ) hic hlen
  have hv'' := EvPar.dcast hdrop.symm rfl rfl rfl hv'
  have hbvar : lift k 1 (.bvar i : Expr Nat) = (.bvar i : Expr Nat) := by
    simp only [lift, if_neg (Nat.not_le_of_gt hic)]
  have htgt : lift 0 (i + 1) (lift (k - i - 1) 1 v') = lift k 1 (lift 0 (i + 1) v') := by
    have hperm := lift_lift_permute (i + 1) 1 (k - i - 1) 0 (Nat.zero_le _) v'
    have hsum : (i + 1) + (k - i - 1) = k := by omega
    simpa only [hsum] using hperm
  have hl' := EvTy.cast rfl hbvar rfl (.wk d k hl)
  have hr' := EvTy.cast rfl htgt.symm rfl (.wk d k hr)
  exact EvParX.dcast rfl hbvar.symm htgt rfl
    (.bvarZeta {
      A := lift (k - i - 1) 1 A
      v := lift (k - i - 1) 1 v
      T₀ := lift k 1 T₀
      h := hg
      hv := hv''
      hl := hl'
      hr := hr'
      idx := .wk d k idx })

/-- Insert sits in the prefix of a `bvarZeta` (`k ≤ i`). -/
def bvarZetaReadWkGe (d : LocalDecl) (k : Nat) {Γ : LCtx} {i : Nat}
    {v' T : Expr Nat} (hge : k ≤ i)
    (A v T₀ : Expr Nat) (h : Γ.get? i = some (.letBinding A v))
    (hv : EvPar R (Γ.drop (i + 1)) v v' A)
    (hl : EvTy R Γ (.bvar i) T₀)
    (hr : EvTy R Γ (lift 0 (i + 1) v') T₀)
    (idx : EvTc R Γ T₀ T) :
    EvParX R (insertAt d k Γ) (lift k 1 (.bvar i))
      (lift k 1 (lift 0 (i + 1) v')) (lift k 1 T) := by
  have hg : (insertAt d k Γ).get? (i + 1) = some (.letBinding A v) := by
    simpa only [h] using insertAt_get?_ge d (Γ := Γ) hge
  have hdrop := insertAt_drop_ge d (Γ := Γ) hge
  have hv' := EvPar.dcast hdrop.symm rfl rfl rfl hv
  have hbvar : lift k 1 (.bvar i : Expr Nat) = (.bvar (i + 1) : Expr Nat) := by
    simp only [lift, if_pos hge]
  have htgt : lift 0 (i + 2) v' = lift k 1 (lift 0 (i + 1) v') :=
    (lift_lift_merge 1 (i + 1) 0 k (Nat.zero_le k) (by omega) v').symm
  have hl' : EvTy R (insertAt d k Γ) (.bvar (i + 1)) (lift k 1 T₀) :=
    EvTy.cast rfl hbvar rfl (.wk d k hl)
  have hr' : EvTy R (insertAt d k Γ) (lift 0 (i + 2) v') (lift k 1 T₀) :=
    EvTy.cast rfl htgt.symm rfl (.wk d k hr)
  exact EvParX.dcast rfl hbvar.symm htgt rfl
    (.bvarZeta {
      A := A
      v := v
      T₀ := lift k 1 T₀
      h := hg
      hv := hv'
      hl := hl'
      hr := hr'
      idx := .wk d k idx })

def EvParX.readWk (hcl : EnvClosed E) (d : LocalDecl) (k : Nat) {Γ : LCtx}
    {a b T : Expr Nat} :
    EvParX R Γ a b T →
      EvParX R (insertAt d k Γ) (lift k 1 a) (lift k 1 b) (lift k 1 T)
  | .embed D => .embed (D.readWk d k)
  | .delta (r := r) (ls := ls) (body := body) p =>
      let htgt : lift k 1 (instantiateLevels ls body) = instantiateLevels ls body :=
        instantiateLevels_closed ((hcl r p.m p.hres).2 body p.hbody) ls k
      EvParX.castR htgt.symm
        (.delta {
          m := p.m
          T₀ := lift k 1 p.T₀
          hres := p.hres
          hbody := p.hbody
          htr := p.htr
          hlen := p.hlen
          hwf := p.hwf
          hl := .wk d k p.hl
          hr := EvTy.cast rfl htgt rfl (.wk d k p.hr)
          idx := .wk d k p.idx })
  | .bvarZeta (i := i) p =>
      if hic : i < k then
        bvarZetaReadWkLt d k hic p.A p.v p.T₀ p.h (p.hv.readWk d (k - i - 1)) p.hl p.hr p.idx
      else
        bvarZetaReadWkGe d k (Nat.le_of_not_lt hic) p.A p.v p.T₀ p.h p.hv p.hl p.hr p.idx
  | .lam p => .lam (p.readWk d k)
  | .app p => .app (p.readWk d k)
  | .letE p => .letE (p.readWk d k)

def EvParX.requests (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {a b T : Expr Nat} → (D : EvParX R Γ a b T) →
      F8Occurrences.Requests (D.val hcl hinst)
  | _, _, _, _, .embed D => D.requests hcl hinst
  | _, _, _, _, .delta _ => fun o => nomatch o
  | _, _, _, _, .bvarZeta p => p.requests hcl hinst
  | _, _, _, _, .lam p => p.requests hcl hinst
  | _, _, _, _, .app p => p.requests hcl hinst
  | _, _, _, _, .letE p => p.requests hcl hinst

def EvParX.answers (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {a b T : Expr Nat} → (D : EvParX R Γ a b T) →
      F8Occurrences.AnsweredOrigins (D.val hcl hinst) (D.requests hcl hinst)
  | _, _, _, _, .embed D => D.answers hcl hinst
  | _, _, _, _, .delta _ => fun o => nomatch o
  | _, _, _, _, .bvarZeta p => p.answers hcl hinst
  | _, _, _, _, .lam p => p.answers hcl hinst
  | _, _, _, _, .app p => p.answers hcl hinst
  | _, _, _, _, .letE p => p.answers hcl hinst

def EvParX.toDTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} :
    EvParX R Γ a b T → DTile R
  | .embed D => D.toDTile hcl hinst X
  | .delta p => p.toDTile hcl hinst X
  | .bvarZeta p => p.toDTile hcl hinst X
  | .lam p => p.toDTile hcl hinst X
  | .app p => p.toDTile hcl hinst X
  | .letE p => p.toDTile hcl hinst X

/-- Named `none`: `readSubst0` does not carry the dropped-context `hvt`. -/
def evParXDroppedHvt {α : Type} : Option α := none

/-- Assumption-substitution reader. `bvarZeta` at `i < j` is `evParXDroppedHvt`: the outer `hv`
    types the substitutend after `substRemove`, not in `Γ.drop (j + 1)`, and that
    dropped typing is the `hvt` cc 05:30 keeps on `substVal` rather than on this reader.
    `i = j` is `nomatch` (an assumption is not the zeta's `letBinding`). -/
def EvParX.readSubst0 (hcl : EnvClosed E) {Γ : LCtx} {a b T t v : Expr Nat}
    (j : Nat) (u : Level) :
    EvParX R Γ a b T →
    (hget : Γ[j]? = some (.assumption t)) →
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) →
    (hvT : EvTy R (substRemove v j Γ) (lift 0 j t) (.sort u)) →
    Option (EvParX R (substRemove v j Γ)
      (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
      (instantiate j (lift 0 j v) T))
  | .embed D, hget, hv, hvT =>
      some (.embed (D.readEsub0 j u hget hv hvT))
  | .delta (r := r) (ls := ls) (body := body) p, hget, hv, hvT =>
      let hid : instantiate j (lift 0 j v) (instantiateLevels ls body) =
          instantiateLevels ls body :=
        instantiate_of_closed _
          (instantiateLevels_closed ((hcl r p.m p.hres).2 body p.hbody) ls 0)
          j (lift 0 j v)
      some (EvParX.castR hid.symm
        (.delta {
          m := p.m
          T₀ := instantiate j (lift 0 j v) p.T₀
          hres := p.hres
          hbody := p.hbody
          htr := p.htr
          hlen := p.hlen
          hwf := p.hwf
          hl := .esub j u p.hl hget hv hvT
          hr := EvTy.cast rfl hid rfl (.esub j u p.hr hget hv hvT)
          idx := .subst0 j p.idx hget hv }))
  | .bvarZeta (i := i) (v' := v') p, hget, hv, hvT =>
      if hij : i = j then by
        subst hij
        have h' : Γ[i]? = some (.letBinding p.A p.v) :=
          (List.get?_eq_getElem? Γ i).symm ▸ p.h
        rw [h'] at hget
        exact nomatch hget
      else if hgt : j < i then by
        have hlkV := lookupValue_of_get?_let p.h
        have hmap := lookupValue_substRemove_gt (v := v) hgt hlkV
        obtain ⟨A', stored, hg', heq⟩ := get?_of_lookupValue hmap
        have hcan (e : Expr Nat) :
            instantiate j (lift 0 j v) (lift 0 (i + 1) e) = lift 0 i e :=
          instantiate_lift_cancel (i + 1) 0 j (lift 0 j v) (Nat.zero_le j) (by omega) e
        have hi1 : (i - 1) + 1 = i := by omega
        have hstored : stored = p.v := by
          have heq' : lift 0 i stored = lift 0 i p.v := by
            have h1 := heq.symm.trans (hcan p.v); rwa [hi1] at h1
          exact lift_zero_amount_inj i heq'
        have hA' : A' = p.A := by
          have hsrc : lookupType Γ i = some (lift 0 (i + 1) p.A) := by simp only [lookupType, p.h]
          have hltTy := lookupType_substRemove_gt (v := v) hgt hsrc
          have hsrcTy : lookupType (substRemove v j Γ) (i - 1) =
              some (lift 0 ((i - 1) + 1) A') := by simp only [lookupType, hg']
          rw [hsrcTy] at hltTy
          have heq' : lift 0 i A' = lift 0 i p.A := by
            have h1 := (Option.some.inj hltTy).trans (hcan p.A); rwa [hi1] at h1
          exact lift_zero_amount_inj i heq'
        have hdrop : (substRemove v j Γ).drop i = Γ.drop (i + 1) := by
          rw [substRemove_drop, if_neg (by omega : ¬ i ≤ j)]
        have hvStep : EvPar R ((substRemove v j Γ).drop i) stored v' A' :=
          EvPar.dcast hdrop.symm hstored.symm rfl hA'.symm p.hv
        have hl' := EvTy.esub j u p.hl hget hv hvT
        have hr' := EvTy.esub j u p.hr hget hv hvT
        have idx' := EvTc.subst0 j p.idx hget hv
        have hbvar : instantiate j (lift 0 j v) (.bvar i) = .bvar (i - 1) := by
          simp only [instantiate, if_neg hij, if_pos hgt]
        have hrEq : instantiate j (lift 0 j v) (lift 0 (i + 1) v') =
            lift 0 ((i - 1) + 1) v' :=
          (hcan v').trans (congrArg (fun k => lift 0 k v') hi1.symm)
        exact some (EvParX.dcast rfl hbvar.symm hrEq.symm rfl
          (.bvarZeta {
            A := A'
            v := stored
            T₀ := instantiate j (lift 0 j v) p.T₀
            h := hg'
            hv := EvPar.dcast (by rw [hi1]) rfl rfl rfl hvStep
            hl := EvTy.cast rfl hbvar rfl hl'
            hr := EvTy.cast rfl hrEq rfl hr'
            idx := idx' }))
      else
        evParXDroppedHvt
  | .lam (A := A) p, hget, hv, hvT =>
      let hget' : (.assumption A :: Γ)[j + 1]? = some (.assumption t) :=
        subst_arg_get_succ (.assumption A) hget
      let hv' : EvTy R (substRemove v (j + 1) (.assumption A :: Γ))
          (lift 0 (j + 1) v) (lift 0 (j + 1) t) :=
        EvTy.cast (by simp [substRemove_succ_cons, instDecl])
          (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v)
          (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t)
          (.wk (.assumption (instantiate j (lift 0 j v) A)) 0 hv)
      let hvT' : EvTy R (substRemove v (j + 1) (.assumption A :: Γ))
          (lift 0 (j + 1) t) (.sort u) :=
        EvTy.cast (by simp [substRemove_succ_cons, instDecl])
          (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t)
          rfl (.wk (.assumption (instantiate j (lift 0 j v) A)) 0 hvT)
      let hll : lift 0 (j + 1) v = lift 0 1 (lift 0 j v) :=
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v).symm
      some (EvParX.dcast rfl (by simp only [instantiate, hll])
        (by simp only [instantiate, hll]) rfl
        (.lam {
          B := instantiate (j + 1) (lift 0 (j + 1) v) p.B
          u := p.u
          v := p.v
          hc := .esub j u p.hc hget hv hvT
          hA := .esub j u p.hA hget hv hvT
          hB := EvTy.cast (by simp [substRemove_succ_cons, instDecl]) rfl rfl
            (.esub (j + 1) u p.hB hget' hv' hvT')
          hb := p.hb.readEsub0 (j + 1) u hget' hv' hvT'
          hrt := EvTy.cast rfl (by simp only [instantiate, hll])
            (by simp only [instantiate, hll]) (.esub j u p.hrt hget hv hvT)
          idx := EvTc.cast rfl (by simp only [instantiate, hll]) rfl
            (.subst0 j p.idx hget hv) }))
  | .app (f := f) (a := arg) (f' := f') (a' := a') p, hget, hv, hvT =>
      let hget' : (.assumption p.A :: Γ)[j + 1]? = some (.assumption t) :=
        subst_arg_get_succ (.assumption p.A) hget
      let hv' : EvTy R (substRemove v (j + 1) (.assumption p.A :: Γ))
          (lift 0 (j + 1) v) (lift 0 (j + 1) t) :=
        EvTy.cast (by simp [substRemove_succ_cons, instDecl])
          (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v)
          (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t)
          (.wk (.assumption (instantiate j (lift 0 j v) p.A)) 0 hv)
      let hvT' : EvTy R (substRemove v (j + 1) (.assumption p.A :: Γ))
          (lift 0 (j + 1) t) (.sort u) :=
        EvTy.cast (by simp [substRemove_succ_cons, instDecl])
          (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t)
          rfl (.wk (.assumption (instantiate j (lift 0 j v) p.A)) 0 hvT)
      let hll : lift 0 (j + 1) v = lift 0 1 (lift 0 j v) :=
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v).symm
      let hcomm : instantiate j (lift 0 j v) (instantiate0 arg p.B) =
          instantiate0 (instantiate j (lift 0 j v) arg)
            (instantiate (j + 1) (lift 0 (j + 1) v) p.B) := by
        simpa only [instantiate0, hll] using
          instantiate_instantiate 0 j arg (lift 0 j v) (Nat.zero_le j) p.B
      some (EvParX.dcast rfl (by simp only [instantiate]) (by simp only [instantiate]) rfl
        (.app {
          T₀ := instantiate j (lift 0 j v) p.T₀
          A := instantiate j (lift 0 j v) p.A
          B := instantiate (j + 1) (lift 0 (j + 1) v) p.B
          u := p.u
          v := p.v
          w := p.w
          hf := p.hf.readEsub0 j u hget hv hvT
          hc := EvTc.cast rfl rfl (by simp only [instantiate, hll]) (.subst0 j p.hc hget hv)
          hPi := EvTy.cast rfl (by simp only [instantiate, hll]) rfl
            (.esub j u p.hPi hget hv hvT)
          hB := EvTy.cast (by simp [substRemove_succ_cons, instDecl]) rfl rfl
            (.esub (j + 1) u p.hB hget' hv' hvT')
          hTy := EvTy.cast rfl hcomm rfl (.esub j u p.hTy hget hv hvT)
          ha := p.ha.readEsub0 j u hget hv hvT
          hr := EvTy.cast rfl (by simp only [instantiate]) hcomm (.esub j u p.hr hget hv hvT)
          idx := EvTc.cast rfl hcomm rfl (.subst0 j p.idx hget hv) }))
  | .letE (A := A) (value := value) p, hget, hv, hvT =>
      let hget' : (.letBinding A value :: Γ)[j + 1]? = some (.assumption t) :=
        subst_arg_get_succ (.letBinding A value) hget
      let hv' : EvTy R (substRemove v (j + 1) (.letBinding A value :: Γ))
          (lift 0 (j + 1) v) (lift 0 (j + 1) t) :=
        EvTy.cast (by simp [substRemove_succ_cons, instDecl])
          (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v)
          (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t)
          (.wk (.letBinding (instantiate j (lift 0 j v) A)
            (instantiate j (lift 0 j v) value)) 0 hv)
      let hvT' : EvTy R (substRemove v (j + 1) (.letBinding A value :: Γ))
          (lift 0 (j + 1) t) (.sort u) :=
        EvTy.cast (by simp [substRemove_succ_cons, instDecl])
          (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t)
          rfl
          (.wk (.letBinding (instantiate j (lift 0 j v) A)
            (instantiate j (lift 0 j v) value)) 0 hvT)
      let hll : lift 0 (j + 1) v = lift 0 1 (lift 0 j v) :=
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v).symm
      let hcomm : instantiate j (lift 0 j v) (instantiate0 value p.B) =
          instantiate0 (instantiate j (lift 0 j v) value)
            (instantiate (j + 1) (lift 0 (j + 1) v) p.B) := by
        simpa only [instantiate0, hll] using
          instantiate_instantiate 0 j value (lift 0 j v) (Nat.zero_le j) p.B
      some (EvParX.dcast rfl (by simp only [instantiate, hll])
        (by simp only [instantiate, hll]) rfl
        (.letE {
          B := instantiate (j + 1) (lift 0 (j + 1) v) p.B
          u := p.u
          w := p.w
          hc := .esub j u p.hc hget hv hvT
          hA := .esub j u p.hA hget hv hvT
          hv := p.hv.readEsub0 j u hget hv hvT
          hB := EvTy.cast (by simp [substRemove_succ_cons, instDecl]) rfl rfl
            (.esub (j + 1) u p.hB hget' hv' hvT')
          hTy := EvTy.cast rfl hcomm rfl (.esub j u p.hTy hget hv hvT)
          hb := p.hb.readEsub0 (j + 1) u hget' hv' hvT'
          hrt := EvTy.cast rfl (by simp only [instantiate, hll]) hcomm
            (.esub j u p.hrt hget hv hvT)
          idx := EvTc.cast rfl hcomm rfl (.subst0 j p.idx hget hv) }))

/-! ### tooth: an index leaf is not covered by the endpoint typings alone -/

def coversIdx (L : List (Jd E n)) {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) : Prop :=
  ∀ ℓ ∈ p.idx.leaves, ℓ ∈ L

def BadLeaves {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) : List (Jd E n) :=
  p.hl.leaves ++ p.hr.leaves

/-- The mutant drops `idx` and still accepts that shorter list. -/
def MutantCover (L : List (Jd E n)) {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) : Prop :=
  ∀ ℓ ∈ p.hl.leaves ++ p.hr.leaves, ℓ ∈ L

theorem coversIdx_of_delta {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) : coversIdx p.leaves p := by
  intro ℓ hℓ
  simp only [DeltaPayload.leaves, List.mem_append]
  exact .inr hℓ

theorem mutant_accepts_dropped_idx {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) : MutantCover (BadLeaves p) p :=
  fun _ h => h

theorem coversIdx_rejects_dropped {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) {ℓ : Jd E n}
    (h : ℓ ∈ p.idx.leaves) (hnot : ℓ ∉ BadLeaves p) : ¬ coversIdx (BadLeaves p) p :=
  fun hc => hnot (hc ℓ h)

/-! ### diamond over `EvParX` -/

inductive EvParXOpt (R : List (Jd E n)) : LCtx → Expr Nat → Expr Nat → Expr Nat → Type where
  | stay {Γ b T} (h : EvTy R Γ b T) : EvParXOpt R Γ b b T
  | step {Γ b d T} (s : EvParX R Γ b d T) : EvParXOpt R Γ b d T

def EvParXOpt.leaves : {Γ : LCtx} → {b d T : Expr Nat} → EvParXOpt R Γ b d T → List (Jd E n)
  | _, _, _, _, .stay h => h.leaves
  | _, _, _, _, .step s => s.leaves

structure EvParXJoin (R : List (Jd E n)) (Γ : LCtx) (b c T : Expr Nat) (L : List (Jd E n)) where
  d : Expr Nat
  left : EvParXOpt R Γ b d T
  right : EvParXOpt R Γ c d T
  sound : ∀ ℓ ∈ left.leaves ++ right.leaves, ∃ ℓ' ∈ L, SubEq ℓ ℓ'

def DOpt.asEvParX {Γ : LCtx} {b d T : Expr Nat} : DOpt R Γ b d T → EvParXOpt R Γ b d T
  | .stay h => .stay h
  | .step s => .step (.embed s.read)

theorem DOpt.asEvParX_leaves {Γ : LCtx} {b d T : Expr Nat} (o : DOpt R Γ b d T) :
    ∀ ℓ ∈ o.asEvParX.leaves, ℓ ∈ o.leaves := by
  cases o with
  | stay _ => intro _ h; exact h
  | step s =>
      intro ℓ hℓ
      simpa only [DOpt.asEvParX, EvParXOpt.leaves, EvParX.leaves] using s.read_leaves ℓ hℓ

def ofLanded {Γ : LCtx} {b c T : Expr Nat} {L : List (Jd E n)}
    (J : DOptJoin R Γ b c T L) : EvParXJoin R Γ b c T L where
  d := J.d
  left := J.left.asEvParX
  right := J.right.asEvParX
  sound := fun ℓ hℓ => by
    rcases List.mem_append.mp hℓ with hℓ | hℓ
    · exact J.sound ℓ (List.mem_append.mpr (.inl (J.left.asEvParX_leaves ℓ hℓ)))
    · exact J.sound ℓ (List.mem_append.mpr (.inr (J.right.asEvParX_leaves ℓ hℓ)))

/-- Named refusals. Each is `none`. `evParXAppApart` and `evParXLetEApart`
    stay named; the general join does not return them. Unequal `T₀`, a
    non-sort instantiation, and a mixed app centre are `evParXAppT0`,
    `evParXAppInst`, and `evParXAppCentre`. A letE whose binder or value
    moved is `evParXLetECentre` or `evParXLetENoSrc`. -/
def evParXConstsDelta {α : Type} : Option α := none
def evParXDeltaConsts {α : Type} : Option α := none
def evParXLamIndex {α : Type} : Option α := none
def evParXLamBothMove {α : Type} : Option α := none
def evParXAppApart {α : Type} : Option α := none
def evParXLetEApart {α : Type} : Option α := none
def evParXCross {α : Type} : Option α := none
/-- No `EvTc` between the two function indices is supplied by the join.
    `SortUnique` compares sorts, not these `T₀`s. Not `evParXAppApart`. -/
def evParXAppT0 {α : Type} : Option α := none
/-- The instantiations are not definitionally equal and not `=ₙ` sorts.
    General `B[a₁] ≡ B[a]` needs a provenance constructor. Not `evParXAppApart`. -/
def evParXAppInst {α : Type} : Option α := none
/-- The component centres are not one common endpoint, so `app f⋆ a⋆` has no `hr`. -/
def evParXAppCentre {α : Type} : Option α := none
/-- The letE centre moved the binder or the value. The body step stays in the
    source let context; it is not cast into the new binder. -/
def evParXLetECentre {α : Type} : Option α := none
/-- The value step has no source typing, so the source let context is not built. -/
def evParXLetENoSrc {α : Type} : Option α := none

/-- A typing of the source, when the step carries one. `.structPi` types the
    target Π. `.lit` types the expansion. Neither is packed back as `.lit`. -/
def EvPar.sourceTy : {Γ : LCtx} → {a b T : Expr Nat} →
    EvPar R Γ a b T → Option (EvTy R Γ a T)
  | _, _, _, _, .proofIndex p => some p.leftTy
  | _, _, _, _, .refl p => some (.rety p.h p.idx)
  | _, _, _, _, .sortEq p => some (.rety p.hl p.idx)
  | _, _, _, _, .consts p => some (.rety p.hl p.idx)
  | _, _, _, _, .structPi _ => none
  | _, _, _, _, .lit _ => none

theorem EvPar.sourceTy_leaves : {Γ : LCtx} → {a b T : Expr Nat} →
    (D : EvPar R Γ a b T) → (h : EvTy R Γ a T) → D.sourceTy = some h →
    ∀ ℓ ∈ h.leaves, ℓ ∈ D.leaves
  | _, _, _, _, .proofIndex p, _, hh => fun ℓ hℓ => by
      simp only [EvPar.sourceTy] at hh
      cases hh
      simp only [EvPar.leaves, ProofIndexPayload.leaves, List.mem_append]
      exact .inl (.inr hℓ)
  | _, _, _, _, .refl p, _, hh => fun ℓ hℓ => by
      simp only [EvPar.sourceTy] at hh
      cases hh
      simpa only [EvPar.leaves, ReflPayload.leaves, EvTy.leaves] using hℓ
  | _, _, _, _, .sortEq p, _, hh => fun ℓ hℓ => by
      simp only [EvPar.sourceTy] at hh
      cases hh
      simp only [EvTy.leaves, List.mem_append] at hℓ
      simp only [EvPar.leaves, SortEqPayload.leaves, List.mem_append]
      rcases hℓ with hℓ | hℓ
      · exact .inl (.inl hℓ)
      · exact .inr hℓ
  | _, _, _, _, .consts p, _, hh => fun ℓ hℓ => by
      simp only [EvPar.sourceTy] at hh
      cases hh
      simp only [EvTy.leaves, List.mem_append] at hℓ
      simp only [EvPar.leaves, ConstsPayload.leaves, List.mem_append]
      rcases hℓ with hℓ | hℓ
      · exact .inl (.inl hℓ)
      · exact .inr hℓ
  | _, _, _, _, .structPi _, _, hh => by
      simp only [EvPar.sourceTy] at hh
      cases hh
  | _, _, _, _, .lit _, _, hh => by
      simp only [EvPar.sourceTy] at hh
      cases hh

/-- One outer closing leg `app f a → app f⋆ a⋆`. `.stay` is the endpoint
    typing. `.stepFun`, `.stepArg`, and `.stepBoth` store the component
    `DStep`s forward. `Tf` and `Ta` are those components' indices. Not an
    `EvParX` at the app's index. -/
inductive AppOuterLeg (R : List (Jd E n)) :
    LCtx → Expr Nat → Expr Nat → Expr Nat → Expr Nat → Type where
  | stay {Γ : LCtx} {f a Tf Ta : Expr Nat}
      (hf : EvTy R Γ f Tf) (ha : EvTy R Γ a Ta) :
      AppOuterLeg R Γ (.app f a) (.app f a) Tf Ta
  | stepFun {Γ : LCtx} {f f' a Tf Ta : Expr Nat}
      (sf : DStep R Γ f f' Tf) (ha : EvTy R Γ a Ta) :
      AppOuterLeg R Γ (.app f a) (.app f' a) Tf Ta
  | stepArg {Γ : LCtx} {f a a' Tf Ta : Expr Nat}
      (hf : EvTy R Γ f Tf) (sa : DStep R Γ a a' Ta) :
      AppOuterLeg R Γ (.app f a) (.app f a') Tf Ta
  | stepBoth {Γ : LCtx} {f f' a a' Tf Ta : Expr Nat}
      (sf : DStep R Γ f f' Tf) (sa : DStep R Γ a a' Ta) :
      AppOuterLeg R Γ (.app f a) (.app f' a') Tf Ta

def AppOuterLeg.leaves : {Γ : LCtx} → {src tgt Tf Ta : Expr Nat} →
    AppOuterLeg R Γ src tgt Tf Ta → List (Jd E n)
  | _, _, _, _, _, .stay hf ha => hf.leaves ++ ha.leaves
  | _, _, _, _, _, .stepFun sf ha => sf.leaves ++ ha.leaves
  | _, _, _, _, _, .stepArg hf sa => hf.leaves ++ sa.leaves
  | _, _, _, _, _, .stepBoth sf sa => sf.leaves ++ sa.leaves

def AppOuterLeg.src {Γ : LCtx} {src tgt Tf Ta : Expr Nat}
    (_ : AppOuterLeg R Γ src tgt Tf Ta) : Expr Nat := src

def AppOuterLeg.tgt {Γ : LCtx} {src tgt Tf Ta : Expr Nat}
    (_ : AppOuterLeg R Γ src tgt Tf Ta) : Expr Nat := tgt

/-- Function component, read the way `DOpt.toEvPar` reads it. -/
def AppOuterLeg.funRead : {Γ : LCtx} → {src tgt Tf Ta : Expr Nat} →
    AppOuterLeg R Γ src tgt Tf Ta → Σ' (f f' : Expr Nat), EvPar R Γ f f' Tf
  | _, _, _, _, _, .stay (f := f) hf _ => ⟨f, f, EvPar.ofTy hf⟩
  | _, _, _, _, _, .stepFun (f := f) (f' := f') sf _ => ⟨f, f', sf.read⟩
  | _, _, _, _, _, .stepArg (f := f) hf _ => ⟨f, f, EvPar.ofTy hf⟩
  | _, _, _, _, _, .stepBoth (f := f) (f' := f') sf _ => ⟨f, f', sf.read⟩

/-- Argument component, read the way `DOpt.toEvPar` reads it. -/
def AppOuterLeg.argRead : {Γ : LCtx} → {src tgt Tf Ta : Expr Nat} →
    AppOuterLeg R Γ src tgt Tf Ta → Σ' (a a' : Expr Nat), EvPar R Γ a a' Ta
  | _, _, _, _, _, .stay (a := a) _ ha => ⟨a, a, EvPar.ofTy ha⟩
  | _, _, _, _, _, .stepFun (a := a) _ ha => ⟨a, a, EvPar.ofTy ha⟩
  | _, _, _, _, _, .stepArg (a := a) (a' := a') _ sa => ⟨a, a', sa.read⟩
  | _, _, _, _, _, .stepBoth (a := a) (a' := a') _ sa => ⟨a, a', sa.read⟩

/-- Apply the two component legs. A `DStep` here is that component's own
    forward step, never a reversed `ParRedT`. -/
def appOuterLeg {Γ : LCtx} {f f' a a' Tf Ta : Expr Nat}
    (hf : DOpt R Γ f f' Tf) (ha : DOpt R Γ a a' Ta) :
    AppOuterLeg R Γ (.app f a) (.app f' a') Tf Ta :=
  match hf with
  | .stay hF =>
    match ha with
    | .stay hA => .stay hF hA
    | .step sA => .stepArg hF sA
  | .step sF =>
    match ha with
    | .stay hA => .stepFun sF hA
    | .step sA => .stepBoth sF sA

theorem appOuterLeg_leaves {Γ : LCtx} {f f' a a' Tf Ta : Expr Nat}
    (hf : DOpt R Γ f f' Tf) (ha : DOpt R Γ a a' Ta) :
    (appOuterLeg hf ha).leaves = hf.leaves ++ ha.leaves := by
  cases hf <;> cases ha <;> rfl

theorem appOuterLeg_stay {Γ : LCtx} {f a Tf Ta : Expr Nat}
    (hf : EvTy R Γ f Tf) (ha : EvTy R Γ a Ta) :
    appOuterLeg (.stay hf) (.stay ha) = .stay hf ha := rfl

theorem appOuterLeg_stepFun {Γ : LCtx} {f f' a Tf Ta : Expr Nat}
    (sf : DStep R Γ f f' Tf) (ha : EvTy R Γ a Ta) :
    appOuterLeg (.step sf) (.stay ha) = .stepFun sf ha := rfl

theorem appOuterLeg_stepArg {Γ : LCtx} {f a a' Tf Ta : Expr Nat}
    (hf : EvTy R Γ f Tf) (sa : DStep R Γ a a' Ta) :
    appOuterLeg (.stay hf) (.step sa) = .stepArg hf sa := rfl

theorem appOuterLeg_stepBoth {Γ : LCtx} {f f' a a' Tf Ta : Expr Nat}
    (sf : DStep R Γ f f' Tf) (sa : DStep R Γ a a' Ta) :
    appOuterLeg (.step sf) (.step sa) = .stepBoth sf sa := rfl

theorem appOuterLeg_funRead {Γ : LCtx} {f f' a a' Tf Ta : Expr Nat}
    (hf : DOpt R Γ f f' Tf) (ha : DOpt R Γ a a' Ta) :
    (appOuterLeg hf ha).funRead = ⟨f, f', hf.toEvPar⟩ := by
  cases hf <;> cases ha <;> rfl

theorem appOuterLeg_argRead {Γ : LCtx} {f f' a a' Tf Ta : Expr Nat}
    (hf : DOpt R Γ f f' Tf) (ha : DOpt R Γ a a' Ta) :
    (appOuterLeg hf ha).argRead = ⟨a, a', ha.toEvPar⟩ := by
  cases hf <;> cases ha <;> rfl

theorem appOuterLeg_funTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {f f' a a' Tf Ta : Expr Nat}
    (hf : DOpt R Γ f f' Tf) (ha : DOpt R Γ a a' Ta) :
    (appOuterLeg hf ha).funRead.2.2.toDTile hcl hinst X =
      hf.toEvPar.toDTile hcl hinst X := by
  cases hf <;> cases ha <;> rfl

theorem appOuterLeg_argTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {f f' a a' Tf Ta : Expr Nat}
    (hf : DOpt R Γ f f' Tf) (ha : DOpt R Γ a a' Ta) :
    (appOuterLeg hf ha).argRead.2.2.toDTile hcl hinst X =
      ha.toEvPar.toDTile hcl hinst X := by
  cases hf <;> cases ha <;> rfl

theorem appOuterLeg_funStepTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {f f' a a' Tf Ta : Expr Nat}
    (sf : DStep R Γ f f' Tf) (ha : DOpt R Γ a a' Ta) :
    (appOuterLeg (.step sf) ha).funRead.2.2.toDTile hcl hinst X =
      sf.toDTile hcl hinst X := by
  cases ha <;> rfl

theorem appOuterLeg_argStepTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {f f' a a' Tf Ta : Expr Nat}
    (hf : DOpt R Γ f f' Tf) (sa : DStep R Γ a a' Ta) :
    (appOuterLeg hf (.step sa)).argRead.2.2.toDTile hcl hinst X =
      sa.toDTile hcl hinst X := by
  cases hf <;> rfl

/-- The two component diamonds, and the two outer legs to `app f⋆ a⋆`.
    Directions and support are the components'. No `ParRedT` is reversed.
    `c₀` and the instantiation chain are not fields. The outer legs are not
    an `EvParX` at the app index. -/
structure AppCornerJoin (R : List (Jd E n)) (Γ : LCtx)
    (f₁ a₁ f₂ a₂ Tf Ta : Expr Nat) where
  fStar : Expr Nat
  aStar : Expr Nat
  centre : Expr Nat
  centre_app : centre = Expr.app fStar aStar
  funLeft : DOpt R Γ f₁ fStar Tf
  funRight : DOpt R Γ f₂ fStar Tf
  argLeft : DOpt R Γ a₁ aStar Ta
  argRight : DOpt R Γ a₂ aStar Ta
  outerLeft : AppOuterLeg R Γ (.app f₁ a₁) (.app fStar aStar) Tf Ta
  outerRight : AppOuterLeg R Γ (.app f₂ a₂) (.app fStar aStar) Tf Ta

def appCornerJoin {Γ : LCtx} {f₁ a₁ f₂ a₂ Tf Ta : Expr Nat} {Lf La : List (Jd E n)}
    (Jf : DOptJoin R Γ f₁ f₂ Tf Lf) (Ja : DOptJoin R Γ a₁ a₂ Ta La) :
    AppCornerJoin R Γ f₁ a₁ f₂ a₂ Tf Ta where
  fStar := Jf.d
  aStar := Ja.d
  centre := Expr.app Jf.d Ja.d
  centre_app := rfl
  funLeft := Jf.left
  funRight := Jf.right
  argLeft := Ja.left
  argRight := Ja.right
  outerLeft := appOuterLeg Jf.left Ja.left
  outerRight := appOuterLeg Jf.right Ja.right

theorem appCornerJoin_fields {Γ : LCtx} {f₁ a₁ f₂ a₂ Tf Ta : Expr Nat}
    {Lf La : List (Jd E n)}
    (Jf : DOptJoin R Γ f₁ f₂ Tf Lf) (Ja : DOptJoin R Γ a₁ a₂ Ta La) :
    let c := appCornerJoin Jf Ja
    c.fStar = Jf.d ∧ c.aStar = Ja.d ∧ c.funLeft = Jf.left ∧ c.funRight = Jf.right ∧
      c.argLeft = Ja.left ∧ c.argRight = Ja.right ∧
      c.centre = Expr.app Jf.d Ja.d ∧
      c.outerLeft = appOuterLeg Jf.left Ja.left ∧
      c.outerRight = appOuterLeg Jf.right Ja.right := by
  simp [appCornerJoin]

theorem appCornerJoin_support {Γ : LCtx} {f₁ a₁ f₂ a₂ Tf Ta : Expr Nat}
    {Lf La : List (Jd E n)}
    (Jf : DOptJoin R Γ f₁ f₂ Tf Lf) (Ja : DOptJoin R Γ a₁ a₂ Ta La) :
    (∀ ℓ ∈ (appCornerJoin Jf Ja).funLeft.leaves ++
        (appCornerJoin Jf Ja).funRight.leaves, ∃ ℓ' ∈ Lf, SubEq ℓ ℓ') ∧
    (∀ ℓ ∈ (appCornerJoin Jf Ja).argLeft.leaves ++
        (appCornerJoin Jf Ja).argRight.leaves, ∃ ℓ' ∈ La, SubEq ℓ ℓ') := by
  refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
  · simpa only [appCornerJoin] using Jf.sound ℓ hℓ
  · simpa only [appCornerJoin] using Ja.sound ℓ hℓ

/-- Outer-leg leaves are the component leaves, so they stay inside `Lf ++ La`. -/
theorem appCornerJoin_outer_support {Γ : LCtx} {f₁ a₁ f₂ a₂ Tf Ta : Expr Nat}
    {Lf La : List (Jd E n)}
    (Jf : DOptJoin R Γ f₁ f₂ Tf Lf) (Ja : DOptJoin R Γ a₁ a₂ Ta La) :
    (∀ ℓ ∈ (appCornerJoin Jf Ja).outerLeft.leaves,
      ∃ ℓ' ∈ Lf ++ La, SubEq ℓ ℓ') ∧
    (∀ ℓ ∈ (appCornerJoin Jf Ja).outerRight.leaves,
      ∃ ℓ' ∈ Lf ++ La, SubEq ℓ ℓ') := by
  refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
  · have hL : (appCornerJoin Jf Ja).outerLeft = appOuterLeg Jf.left Ja.left := rfl
    rw [hL, appOuterLeg_leaves] at hℓ
    rcases List.mem_append.mp hℓ with hℓ | hℓ
    · obtain ⟨k, hk, hs⟩ := Jf.sound ℓ (List.mem_append.mpr (.inl hℓ))
      exact ⟨k, List.mem_append.mpr (.inl hk), hs⟩
    · obtain ⟨k, hk, hs⟩ := Ja.sound ℓ (List.mem_append.mpr (.inl hℓ))
      exact ⟨k, List.mem_append.mpr (.inr hk), hs⟩
  · have hR : (appCornerJoin Jf Ja).outerRight = appOuterLeg Jf.right Ja.right := rfl
    rw [hR, appOuterLeg_leaves] at hℓ
    rcases List.mem_append.mp hℓ with hℓ | hℓ
    · obtain ⟨k, hk, hs⟩ := Jf.sound ℓ (List.mem_append.mpr (.inr hℓ))
      exact ⟨k, List.mem_append.mpr (.inl hk), hs⟩
    · obtain ⟨k, hk, hs⟩ := Ja.sound ℓ (List.mem_append.mpr (.inr hℓ))
      exact ⟨k, List.mem_append.mpr (.inr hk), hs⟩

theorem appCornerJoin_outer_target {Γ : LCtx} {f₁ a₁ f₂ a₂ Tf Ta : Expr Nat}
    {Lf La : List (Jd E n)}
    (Jf : DOptJoin R Γ f₁ f₂ Tf Lf) (Ja : DOptJoin R Γ a₁ a₂ Ta La) :
    let c := appCornerJoin Jf Ja
    c.outerLeft.src = Expr.app f₁ a₁ ∧ c.outerRight.src = Expr.app f₂ a₂ ∧
      c.outerLeft.tgt = c.centre ∧ c.outerRight.tgt = c.centre := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `symm p₁.hc ; c₀ ; p₂.hc`. `c₀` is an argument, not a subderivation of either `hc`. -/
def appIndexChain {Γ : LCtx} {f a f₁ a₁ f₂ a₂ T : Expr Nat}
    (p₁ : AppPayload R Γ f a f₁ a₁ T) (p₂ : AppPayload R Γ f a f₂ a₂ T)
    (c₀ : EvTc R Γ p₁.T₀ p₂.T₀) :
    EvTc R Γ (.pi p₁.A p₁.B) (.pi p₂.A p₂.B) :=
  .trans (.symm p₁.hc) (.trans c₀ p₂.hc)

theorem appIndexChain_leaves {Γ : LCtx} {f a f₁ a₁ f₂ a₂ T : Expr Nat}
    (p₁ : AppPayload R Γ f a f₁ a₁ T) (p₂ : AppPayload R Γ f a f₂ a₂ T)
    (c₀ : EvTc R Γ p₁.T₀ p₂.T₀) :
    ∀ ℓ ∈ (appIndexChain p₁ p₂ c₀).leaves,
      ℓ ∈ p₁.hc.leaves ++ c₀.leaves ++ p₂.hc.leaves := by
  intro ℓ hℓ
  simp only [appIndexChain, EvTc.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with hℓ | hℓ
  · exact .inl (.inl hℓ)
  · rcases hℓ with hℓ | hℓ
    · exact .inl (.inr hℓ)
    · exact .inr hℓ

/-- Read `p₂.hf` at `p₁.T₀` along `symm c₀`. The owner-side reader, not `dcast`. -/
def appFunRead {Γ : LCtx} {f f₂ T₀₁ T₀₂ : Expr Nat}
    (hf : EvPar R Γ f f₂ T₀₂) (c₀ : EvTc R Γ T₀₁ T₀₂) :
    EvPar R Γ f f₂ T₀₁ :=
  hf.readConv (.symm c₀)

theorem appFunRead_leaves {Γ : LCtx} {f f₂ T₀₁ T₀₂ : Expr Nat}
    (hf : EvPar R Γ f f₂ T₀₂) (c₀ : EvTc R Γ T₀₁ T₀₂) :
    ∀ ℓ ∈ (appFunRead hf c₀).leaves, ℓ ∈ hf.leaves ++ c₀.leaves := by
  intro ℓ hℓ
  have hmem := hf.readConv_leaves (.symm c₀) ℓ hℓ
  simpa only [EvTc.leaves, List.mem_append] using hmem

/-- Body diamond of a letE whose centre may change the value, still in the
    original `.letBinding A value`. The outer centre is `letE A v⋆ body⋆`. -/
structure LetECorner (R : List (Jd E n)) (Γ : LCtx)
    (A value value₁ value₂ body₁ body₂ B : Expr Nat) where
  vStar : Expr Nat
  bodyStar : Expr Nat
  centre : Expr Nat
  centre_let : centre = Expr.letE A vStar bodyStar
  valLeft : DOpt R Γ value₁ vStar A
  valRight : DOpt R Γ value₂ vStar A
  bodyLeft : DOpt R (.letBinding A value :: Γ) body₁ bodyStar B
  bodyRight : DOpt R (.letBinding A value :: Γ) body₂ bodyStar B

def letECornerJoin {Γ : LCtx} {A value value₁ value₂ body₁ body₂ B : Expr Nat}
    {Lv Lb : List (Jd E n)}
    (Jv : DOptJoin R Γ value₁ value₂ A Lv)
    (Jb : DOptJoin R (.letBinding A value :: Γ) body₁ body₂ B Lb) :
    LetECorner R Γ A value value₁ value₂ body₁ body₂ B where
  vStar := Jv.d
  bodyStar := Jb.d
  centre := Expr.letE A Jv.d Jb.d
  centre_let := rfl
  valLeft := Jv.left
  valRight := Jv.right
  bodyLeft := Jb.left
  bodyRight := Jb.right

theorem letECornerJoin_fields {Γ : LCtx}
    {A value value₁ value₂ body₁ body₂ B : Expr Nat} {Lv Lb : List (Jd E n)}
    (Jv : DOptJoin R Γ value₁ value₂ A Lv)
    (Jb : DOptJoin R (.letBinding A value :: Γ) body₁ body₂ B Lb) :
    let c := letECornerJoin Jv Jb
    c.vStar = Jv.d ∧ c.bodyStar = Jb.d ∧ c.valLeft = Jv.left ∧ c.valRight = Jv.right ∧
      c.bodyLeft = Jb.left ∧ c.bodyRight = Jb.right ∧
      c.centre = Expr.letE A Jv.d Jb.d := by
  simp [letECornerJoin]

theorem letECornerJoin_support {Γ : LCtx}
    {A value value₁ value₂ body₁ body₂ B : Expr Nat} {Lv Lb : List (Jd E n)}
    (Jv : DOptJoin R Γ value₁ value₂ A Lv)
    (Jb : DOptJoin R (.letBinding A value :: Γ) body₁ body₂ B Lb) :
    (∀ ℓ ∈ (letECornerJoin Jv Jb).valLeft.leaves ++
        (letECornerJoin Jv Jb).valRight.leaves, ∃ ℓ' ∈ Lv, SubEq ℓ ℓ') ∧
    (∀ ℓ ∈ (letECornerJoin Jv Jb).bodyLeft.leaves ++
        (letECornerJoin Jv Jb).bodyRight.leaves, ∃ ℓ' ∈ Lb, SubEq ℓ ℓ') := by
  refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
  · simpa only [letECornerJoin] using Jv.sound ℓ hℓ
  · simpa only [letECornerJoin] using Jb.sound ℓ hℓ

/-- The refused unconditional answer: `none` with no look at the two steps.
    The dispatcher does not return this on an app or letE diagonal. -/
def mutantAppLetERefuse {α : Type} : Option α := none

def proofIndexLeftJoinX {Γ : LCtx} {a b c T : Expr Nat}
    (p₁ : ProofIndexPayload R Γ a b T) (D₂ : EvParX R Γ a c T) :
    EvParXJoin R Γ b c T ((EvPar.proofIndex p₁).leaves ++ D₂.leaves) where
  d := c
  left := .step (.embed (proofIndexJoin p₁ D₂.rightTy))
  right := .stay D₂.rightTy
  sound := fun ℓ hℓ => by
    simp only [EvParXOpt.leaves, EvParX.leaves, List.mem_append] at hℓ
    refine dSubEq_of_mem ?_
    rcases hℓ with h | h
    · rcases proofIndexJoin_leaves p₁ D₂.rightTy ℓ h with h' | h'
      · exact List.mem_append.mpr (.inl h')
      · exact List.mem_append.mpr (.inr (D₂.rightTy_leaves ℓ h'))
    · exact List.mem_append.mpr (.inr (D₂.rightTy_leaves ℓ h))

def proofIndexRightJoinX {Γ : LCtx} {a b c T : Expr Nat}
    (D₁ : EvParX R Γ a b T) (p₂ : ProofIndexPayload R Γ a c T) :
    EvParXJoin R Γ b c T (D₁.leaves ++ (EvPar.proofIndex p₂).leaves) where
  d := b
  left := .stay D₁.rightTy
  right := .step (.embed (proofIndexJoin p₂ D₁.rightTy))
  sound := fun ℓ hℓ => by
    simp only [EvParXOpt.leaves, EvParX.leaves, List.mem_append] at hℓ
    refine dSubEq_of_mem ?_
    rcases hℓ with h | h
    · exact List.mem_append.mpr (.inl (D₁.rightTy_leaves ℓ h))
    · rcases proofIndexJoin_leaves p₂ D₁.rightTy ℓ h with h' | h'
      · exact List.mem_append.mpr (.inr h')
      · exact List.mem_append.mpr (.inl (D₁.rightTy_leaves ℓ h'))

/-- `refl` against any `EvParX`, using the other side's right-endpoint typing. -/
def reflLeftJoinX {Γ : LCtx} {a c T : Expr Nat}
    (_p₁ : ReflPayload R Γ a T) (D₂ : EvParX R Γ a c T) :
    EvParXJoin R Γ a c T ((EvPar.refl _p₁).leaves ++ D₂.leaves) where
  d := c
  left := .step D₂
  right := .stay D₂.rightTy
  sound := fun ℓ hℓ => by
    simp only [EvParXOpt.leaves, List.mem_append] at hℓ
    refine dSubEq_of_mem (List.mem_append.mpr (.inr ?_))
    rcases hℓ with h | h
    · exact h
    · exact D₂.rightTy_leaves ℓ h

def reflRightJoinX {Γ : LCtx} {a b T : Expr Nat}
    (D₁ : EvParX R Γ a b T) (_p₂ : ReflPayload R Γ a T) :
    EvParXJoin R Γ b a T (D₁.leaves ++ (EvPar.refl _p₂).leaves) where
  d := b
  left := .stay D₁.rightTy
  right := .step D₁
  sound := fun ℓ hℓ => by
    simp only [EvParXOpt.leaves, List.mem_append] at hℓ
    refine dSubEq_of_mem (List.mem_append.mpr (.inl ?_))
    rcases hℓ with h | h
    · exact D₁.rightTy_leaves ℓ h
    · exact h

section Diamond
variable (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)

private def lamHbIn {Γ : LCtx} {A body A' body' T : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) {z : Jd E n} (hz : z ∈ p.hb.leaves) :
    z ∈ p.leaves :=
  List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hz)))))

/-- `lam × lam` when the body codomain indices agree and the child diamond's right
    leg stays, so `lamForwardJoin` gets a forward `EvPar` and actually uses `X`.
    Both bodies moving, or unequal `B`, is a named `none` (no `EvTy` lam congruence). -/
def evParLamStayJoinX (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A body A₁ body₁ A₂ body₂ T : Expr Nat}
    (p₁ : LamPayload R Γ A body A₁ body₁ T) (p₂ : LamPayload R Γ A body A₂ body₂ T) :
    Option (EvParXJoin R Γ (.lam A₁ body₁) (.lam A₂ body₂) T (p₁.leaves ++ p₂.leaves)) := by
  by_cases hB : p₁.B = p₂.B
  · let hb₂ : EvPar R (.assumption A :: Γ) body body₂ p₁.B :=
      EvPar.dcast rfl rfl rfl hB.symm p₂.hb
    let hcl := envClosed_of_envWfT hW
    let hinst := envMembersSubstStable_of_envWfT hW
    have hΓA : CtxWfT E n (.assumption A :: Γ) :=
      .assumption Γ A p₁.u hΓ (p₁.hA.val hcl hinst)
    obtain ⟨d, left, right, hsnd⟩ := evParDiamondWf hW su hΓA p₁.hb hb₂
    cases right with
    | step _ => exact evParXLamBothMove
    | stay _ =>
        let hb12 := left.toEvPar
        let q := lamForwardJoin hW su X hΓ p₁ p₂ hb12
        refine some ?_
        exact {
          d := .lam A₂ body₂
          left := .step (.lam q)
          right := .stay q.rightTy
          sound := by
            intro ℓ hℓ
            have coverQ : ∀ x ∈ q.leaves, ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq x ℓ' := by
              intro x hx
              obtain ⟨ℓ₁, hm, hs⟩ := lamForwardJoin_sound hW su X hX hΓ p₁ p₂ hb12 x hx
              rcases List.mem_append.mp hm with hm | hm
              · exact ⟨ℓ₁, hm, hs⟩
              · have hmem : ℓ₁ ∈ left.leaves := left.toEvPar_leaves ℓ₁ hm
                obtain ⟨k, hk, hs2⟩ := hsnd ℓ₁ (List.mem_append.mpr (.inl hmem))
                have hkL : k ∈ p₁.leaves ++ p₂.leaves := by
                  rcases List.mem_append.mp hk with hk | hk
                  · exact List.mem_append.mpr (.inl (lamHbIn p₁ hk))
                  · have hkHb : k ∈ p₂.hb.leaves :=
                      (EvPar.dcast_leaves rfl rfl rfl hB.symm p₂.hb) ▸ hk
                    exact List.mem_append.mpr (.inr (lamHbIn p₂ hkHb))
                exact ⟨k, hkL, dSubEq_trans hs hs2⟩
            simp only [EvParXOpt.leaves, EvParX.leaves, List.mem_append] at hℓ
            rcases hℓ with hℓ | hℓ
            · exact coverQ ℓ hℓ
            · exact coverQ ℓ (q.rightTy_leaves ℓ hℓ) }
  · exact evParXLamIndex

/-- Forward lam join supplied with the body step. This is the `X`-using answer when
    the diamond's stay case does not apply. -/
def evParLamJoinX (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A body A₁ body₁ A₂ body₂ T : Expr Nat}
    (p₁ : LamPayload R Γ A body A₁ body₁ T) (p₂ : LamPayload R Γ A body A₂ body₂ T)
    (hb12 : EvPar R (.assumption A :: Γ) body₁ body₂ p₁.B) :
    EvParXJoin R Γ (.lam A₁ body₁) (.lam A₂ body₂) T
      (p₁.leaves ++ p₂.leaves ++ hb12.leaves) :=
  let q := lamForwardJoin hW su X hΓ p₁ p₂ hb12
  { d := .lam A₂ body₂
    left := .step (.lam q)
    right := .stay q.rightTy
    sound := fun ℓ hℓ => by
      simp only [EvParXOpt.leaves, EvParX.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact lamForwardJoin_sound hW su X hX hΓ p₁ p₂ hb12 ℓ hℓ
      · exact lamForwardJoin_sound hW su X hX hΓ p₁ p₂ hb12 ℓ (q.rightTy_leaves ℓ hℓ) }

def evParAppJoinX {Γ : LCtx} {f a f₁ a₁ f₂ a₂ T : Expr Nat}
    (p₁ : AppPayload R Γ f a f₁ a₁ T) (p₂ : AppPayload R Γ f a f₂ a₂ T)
    (hf12 : EvPar R Γ f₁ f₂ p₂.T₀) (ha12 : EvPar R Γ a₁ a₂ p₂.A)
    (cA : EvTc R Γ p₁.A p₂.A)
    (cInst : EvTc R Γ (instantiate0 a p₂.B) (instantiate0 a₁ p₂.B)) :
    EvParXJoin R Γ (.app f₁ a₁) (.app f₂ a₂) T
      (p₁.leaves ++ p₂.leaves ++ hf12.leaves ++ ha12.leaves ++ cA.leaves ++ cInst.leaves) :=
  let q := appForwardJoin p₁ p₂ hf12 ha12 cA cInst
  { d := .app f₂ a₂
    left := .step (.app q)
    right := .stay q.rightTy
    sound := fun ℓ hℓ => by
      simp only [EvParXOpt.leaves, EvParX.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact appForwardJoin_sound p₁ p₂ hf12 ha12 cA cInst ℓ hℓ
      · exact appForwardJoin_sound p₁ p₂ hf12 ha12 cA cInst ℓ (q.rightTy_leaves ℓ hℓ) }

def evParLetEJoinX {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A value body A₁ value₁ body₁ A₂ value₂ body₂ T : Expr Nat}
    (p₁ : LetEPayload R Γ A value body A₁ value₁ body₁ T)
    (p₂ : LetEPayload R Γ A value body A₂ value₂ body₂ T)
    (hv12 : EvPar R Γ value₁ value₂ A₁)
    (hB₁ : EvTy R (.letBinding A₁ value₁ :: Γ) p₂.B (.sort p₂.w))
    (hTy₁ : EvTy R Γ (instantiate0 value₁ p₂.B) (.sort p₂.w))
    (hb12 : EvPar R (.letBinding A₁ value₁ :: Γ) body₁ body₂ p₂.B)
    (cInst : EvTc R Γ (instantiate0 value p₂.B) (instantiate0 value₁ p₂.B)) :
    EvParXJoin R Γ (.letE A₁ value₁ body₁) (.letE A₂ value₂ body₂) T
      (p₁.leaves ++ p₂.leaves ++ hv12.leaves ++ hB₁.leaves ++ hTy₁.leaves ++
        hb12.leaves ++ cInst.leaves) :=
  let q := letEForwardJoin hW su hΓ p₁ p₂ hv12 hB₁ hTy₁ hb12 cInst
  { d := .letE A₂ value₂ body₂
    left := .step (.letE q)
    right := .stay q.rightTy
    sound := fun ℓ hℓ => by
      simp only [EvParXOpt.leaves, EvParX.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact letEForwardJoin_sound hW su hΓ p₁ p₂ hv12 hB₁ hTy₁ hb12 cInst ℓ hℓ
      · exact letEForwardJoin_sound hW su hΓ p₁ p₂ hv12 hB₁ hTy₁ hb12 cInst ℓ
          (q.rightTy_leaves ℓ hℓ) }

/-- Both legs stay at one common target. Leaves come from `rightTy_leaves`, so the
    budget is exactly `L` as supplied by the caller (the two inputs' leaves). -/
def evParXDiagStay {Γ : LCtx} {b T : Expr Nat} {L : List (Jd E n)}
    (h₁ h₂ : EvTy R Γ b T)
    (cover : ∀ ℓ ∈ h₁.leaves ++ h₂.leaves, ∃ ℓ' ∈ L, SubEq ℓ ℓ') :
    EvParXJoin R Γ b b T L where
  d := b
  left := .stay h₁
  right := .stay h₂
  sound := cover

def evParAppDiagJoin {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p₁ p₂ : AppPayload R Γ f a f' a' T) :
    EvParXJoin R Γ (.app f' a') (.app f' a') T
      ((EvParX.app p₁).leaves ++ (EvParX.app p₂).leaves) :=
  evParXDiagStay (EvParX.app p₁).rightTy (EvParX.app p₂).rightTy fun ℓ hℓ => by
    rcases List.mem_append.mp hℓ with h | h
    · exact dSubEq_of_mem (List.mem_append.mpr
        (.inl ((EvParX.app p₁).rightTy_leaves ℓ h)))
    · exact dSubEq_of_mem (List.mem_append.mpr
        (.inr ((EvParX.app p₂).rightTy_leaves ℓ h)))

def evParLetEDiagJoin {Γ : LCtx} {A value body A' value' body' T : Expr Nat}
    (p₁ p₂ : LetEPayload R Γ A value body A' value' body' T) :
    EvParXJoin R Γ (.letE A' value' body') (.letE A' value' body') T
      ((EvParX.letE p₁).leaves ++ (EvParX.letE p₂).leaves) :=
  evParXDiagStay (EvParX.letE p₁).rightTy (EvParX.letE p₂).rightTy fun ℓ hℓ => by
    rcases List.mem_append.mp hℓ with h | h
    · exact dSubEq_of_mem (List.mem_append.mpr
        (.inl ((EvParX.letE p₁).rightTy_leaves ℓ h)))
    · exact dSubEq_of_mem (List.mem_append.mpr
        (.inr ((EvParX.letE p₂).rightTy_leaves ℓ h)))

/-- Read the forward `EvPar` when the diamond's right leg stays.
    The join index is a binder here, so `.stay` refines it. Matching the
    projection `J.right` would not refine the sibling fields. -/
private def stayRead {Γ : LCtx} {b c d T : Expr Nat}
    (left : DOpt R Γ b d T) (right : DOpt R Γ c d T) :
    Option (EvPar R Γ b c T) :=
  match right with
  | .stay _ => some left.toEvPar
  | .step _ => none

private theorem stayRead_leaves {Γ : LCtx} {b c d T : Expr Nat}
    (left : DOpt R Γ b d T) (right : DOpt R Γ c d T)
    {h : EvPar R Γ b c T} (hh : stayRead left right = some h) :
    ∀ ℓ ∈ h.leaves, ℓ ∈ left.leaves := by
  cases right with
  | stay _ =>
      simp only [stayRead] at hh
      cases hh
      intro ℓ hℓ
      exact left.toEvPar_leaves ℓ hℓ
  | step _ =>
      simp only [stayRead] at hh
      nomatch hh

/-- A staying right leg means the diamond's join term is that leg's endpoint. -/
private theorem stayRead_centre {Γ : LCtx} {b c d T : Expr Nat}
    (left : DOpt R Γ b d T) (right : DOpt R Γ c d T)
    {h : EvPar R Γ b c T} (hh : stayRead left right = some h) : d = c := by
  cases right with
  | stay _ => rfl
  | step _ =>
      simp only [stayRead] at hh
      nomatch hh

private theorem appCorner_at_right {Γ : LCtx} {f₁ a₁ f₂ a₂ Tf Ta : Expr Nat}
    {Lf La : List (Jd E n)}
    (Jf : DOptJoin R Γ f₁ f₂ Tf Lf) (Ja : DOptJoin R Γ a₁ a₂ Ta La)
    {hf : EvPar R Γ f₁ f₂ Tf} {ha : EvPar R Γ a₁ a₂ Ta}
    (hF : stayRead Jf.left Jf.right = some hf)
    (hA : stayRead Ja.left Ja.right = some ha) :
    (appCornerJoin Jf Ja).centre = Expr.app f₂ a₂ := by
  have hfd : Jf.d = f₂ := stayRead_centre Jf.left Jf.right hF
  have had : Ja.d = a₂ := stayRead_centre Ja.left Ja.right hA
  simp only [appCornerJoin, hfd, had]

private theorem appCorner_at_left {Γ : LCtx} {f₁ a₁ f₂ a₂ Tf Ta : Expr Nat}
    {Lf La : List (Jd E n)}
    (Jf : DOptJoin R Γ f₁ f₂ Tf Lf) (Ja : DOptJoin R Γ a₁ a₂ Ta La)
    {hf : EvPar R Γ f₂ f₁ Tf} {ha : EvPar R Γ a₂ a₁ Ta}
    (hF : stayRead Jf.right Jf.left = some hf)
    (hA : stayRead Ja.right Ja.left = some ha) :
    (appCornerJoin Jf Ja).centre = Expr.app f₁ a₁ := by
  have hfd : Jf.d = f₁ := stayRead_centre Jf.right Jf.left hF
  have had : Ja.d = a₁ := stayRead_centre Ja.right Ja.left hA
  simp only [appCornerJoin, hfd, had]

/-- Value and body diamonds in the source let context. The body step is not
    cast into `.letBinding A₁ value₁`. -/
private def letECornerOf {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A value body A₁ value₁ body₁ A₂ value₂ body₂ T : Expr Nat}
    (p₁ : LetEPayload R Γ A value body A₁ value₁ body₁ T)
    (p₂ : LetEPayload R Γ A value body A₂ value₂ body₂ T)
    (hB : p₁.B = p₂.B) (hvSrc : EvTy R Γ value A)
    (_hS : p₁.hv.sourceTy = some hvSrc) :
    LetECorner R Γ A value value₁ value₂ body₁ body₂ p₁.B :=
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  let hΓB : CtxWfT E n (.letBinding A value :: Γ) :=
    .letBinding Γ A p₁.u value hΓ (p₁.hA.val hcl hinst) (hvSrc.val hcl hinst)
  let Jv := evParDiamondWf hW su hΓ p₁.hv p₂.hv
  let hb₂ : EvPar R (.letBinding A value :: Γ) body body₂ p₁.B :=
    EvPar.dcast (h := p₂.hb) rfl rfl rfl hB.symm
  let Jb := evParDiamondWf hW su hΓB p₁.hb hb₂
  letECornerJoin Jv Jb

private def evParXLetEMove {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A value body A₁ value₁ body₁ A₂ value₂ body₂ T : Expr Nat}
    (p₁ : LetEPayload R Γ A value body A₁ value₁ body₁ T)
    (p₂ : LetEPayload R Γ A value body A₂ value₂ body₂ T) :
    Option (EvParXJoin R Γ (.letE A₁ value₁ body₁) (.letE A₂ value₂ body₂) T
      (p₁.leaves ++ p₂.leaves)) :=
  if hB : p₁.B = p₂.B then
    match hS : p₁.hv.sourceTy with
    | none => evParXLetENoSrc
    | some hvSrc =>
        have _corner : LetECorner R Γ A value value₁ value₂ body₁ body₂ p₁.B :=
          letECornerOf hW su hΓ p₁ p₂ hB hvSrc hS
        evParXLetECentre
  else
    evParXLetEApart

private theorem mem_hf_app {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) {ℓ : Jd E n} (h : ℓ ∈ p.hf.leaves) :
    ℓ ∈ p.leaves := by
  simp only [AppPayload.leaves, List.mem_append]
  exact .inl (.inl (.inl (.inl (.inl (.inl (.inl h))))))

private theorem mem_hc_app {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) {ℓ : Jd E n} (h : ℓ ∈ p.hc.leaves) :
    ℓ ∈ p.leaves := by
  simp only [AppPayload.leaves, List.mem_append]
  exact .inl (.inl (.inl (.inl (.inl (.inl (.inr h))))))

private theorem mem_ha_app {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) {ℓ : Jd E n} (h : ℓ ∈ p.ha.leaves) :
    ℓ ∈ p.leaves := by
  simp only [AppPayload.leaves, List.mem_append]
  exact .inl (.inl (.inr h))

private theorem mem_hv_letE {Γ : LCtx}
    {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) {ℓ : Jd E n}
    (h : ℓ ∈ p.hv.leaves) : ℓ ∈ p.leaves := by
  simp only [LetEPayload.leaves, List.mem_append]
  exact .inl (.inl (.inl (.inl (.inl (.inr h)))))

private theorem mem_hB_letE {Γ : LCtx}
    {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) {ℓ : Jd E n}
    (h : ℓ ∈ p.hB.leaves) : ℓ ∈ p.leaves := by
  simp only [LetEPayload.leaves, List.mem_append]
  exact .inl (.inl (.inl (.inl (.inr h))))

private theorem mem_hTy_letE {Γ : LCtx}
    {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) {ℓ : Jd E n}
    (h : ℓ ∈ p.hTy.leaves) : ℓ ∈ p.leaves := by
  simp only [LetEPayload.leaves, List.mem_append]
  exact .inl (.inl (.inl (.inr h)))

private theorem mem_hb_letE {Γ : LCtx}
    {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) {ℓ : Jd E n}
    (h : ℓ ∈ p.hb.leaves) : ℓ ∈ p.leaves := by
  simp only [LetEPayload.leaves, List.mem_append]
  exact .inl (.inl (.inr h))

set_option maxHeartbeats 4000000 in
/-- The app pair that is not a diagonal and not an identity replay.
    Equal `T₀` is `c₀ = refl`, then `appIndexChain` and `appFunRead`.
    Both component diamonds staying on the right close at `app f₂ a₂`;
    both staying on the left close at `app f₁ a₁`, using the step the
    diamond returned. A mixed centre is `evParXAppCentre`. Unequal `T₀`
    is `evParXAppT0`: this join has no U call edge. An instantiation that
    is not definitional and not an `=ₙ` sort is `evParXAppInst`. The leaf
    budget is the two inputs. Not a `some` for every unequal pair. -/
def evParAppGenJoinX (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f a f₁ a₁ f₂ a₂ T : Expr Nat}
    (p₁ : AppPayload R Γ f a f₁ a₁ T) (p₂ : AppPayload R Γ f a f₂ a₂ T) :
    Option (EvParXJoin R Γ (.app f₁ a₁) (.app f₂ a₂) T (p₁.leaves ++ p₂.leaves)) :=
  if hT : p₁.T₀ = p₂.T₀ then
    let c₀ : EvTc R Γ p₁.T₀ p₂.T₀ :=
      EvTc.cast rfl rfl hT (EvTc.refl Γ p₁.T₀)
    have hc0 : c₀.leaves = [] := by
      simp only [c₀, EvTc.cast_leaves, EvTc.leaves]
    let cPi : EvTc R Γ (.pi p₁.A p₁.B) (.pi p₂.A p₂.B) :=
      appIndexChain p₁ p₂ c₀
    let cA : EvTc R Γ p₁.A p₂.A := (X R cPi).1
    let ha₁ : EvPar R Γ a a₁ p₂.A := p₁.ha.readConv cA
    let hf₂ : EvPar R Γ f f₂ p₁.T₀ := appFunRead p₂.hf c₀
    let Jf := evParDiamondWf hW su hΓ p₁.hf hf₂
    let Ja := evParDiamondWf hW su hΓ ha₁ p₂.ha
    have hcPi : ∀ x ∈ cPi.leaves, x ∈ p₁.leaves ++ p₂.leaves := by
      intro x hx
      have hx' := appIndexChain_leaves p₁ p₂ c₀ x hx
      rcases List.mem_append.mp hx' with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append.mpr (.inl (mem_hc_app p₁ hx))
        · rw [hc0] at hx
          cases hx
      · exact List.mem_append.mpr (.inr (mem_hc_app p₂ hx))
    have hcA : ∀ x ∈ cA.leaves,
        ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq x ℓ' := by
      intro x hx
      obtain ⟨k, hk, hs⟩ := hX R cPi x (List.mem_append.mpr (.inl hx))
      exact ⟨k, hcPi k hk, hs⟩
    match hF : stayRead Jf.left Jf.right with
    | none =>
      match hFr : stayRead Jf.right Jf.left with
      | none => evParXAppCentre
      | some hf₂to₁ =>
        match hAr : stayRead Ja.right Ja.left with
        | none => evParXAppCentre
        | some ha₂to₁ =>
          let ha₂₁ : EvPar R Γ a₂ a₁ p₁.A := ha₂to₁.readConv (EvTc.symm cA)
          let cA' : EvTc R Γ p₂.A p₁.A := EvTc.symm cA
          let corner := appCornerJoin Jf Ja
          let finish
              (cInst : EvTc R Γ (instantiate0 a p₁.B) (instantiate0 a₂ p₁.B))
              (hcInst : cInst.leaves = []) :
              Option (EvParXJoin R Γ (.app f₁ a₁) (.app f₂ a₂) T
                (p₁.leaves ++ p₂.leaves)) :=
            let q := appForwardJoin p₂ p₁ hf₂to₁ ha₂₁ cA' cInst
            some {
              d := .app f₁ a₁
              left := .stay q.rightTy
              right := .step (.app q)
              sound := fun ℓ hℓ => by
                have hCentre : corner.centre = Expr.app f₁ a₁ :=
                  appCorner_at_left Jf Ja hFr hAr
                simp only [EvParXOpt.leaves, EvParX.leaves, List.mem_append] at hℓ
                have hJfS : ∀ x ∈ hf₂to₁.leaves,
                    ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq x ℓ' := by
                  intro x hx
                  have hxL := stayRead_leaves Jf.right Jf.left hFr x hx
                  obtain ⟨k, hk, hs⟩ := Jf.sound x (List.mem_append.mpr (.inr hxL))
                  rcases List.mem_append.mp hk with hk | hk
                  · exact ⟨k, List.mem_append.mpr (.inl (mem_hf_app p₁ hk)), hs⟩
                  · have hkR := appFunRead_leaves p₂.hf c₀ k hk
                    rw [hc0, List.append_nil] at hkR
                    exact ⟨k, List.mem_append.mpr (.inr (mem_hf_app p₂ hkR)), hs⟩
                have hJaS : ∀ x ∈ ha₂to₁.leaves,
                    ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq x ℓ' := by
                  intro x hx
                  have hxL := stayRead_leaves Ja.right Ja.left hAr x hx
                  obtain ⟨k, hk, hs⟩ := Ja.sound x (List.mem_append.mpr (.inr hxL))
                  rcases List.mem_append.mp hk with hk | hk
                  · have hsplit := p₁.ha.readConv_leaves cA k hk
                    rcases List.mem_append.mp hsplit with hk | hk
                    · exact ⟨k, List.mem_append.mpr (.inl (mem_ha_app p₁ hk)), hs⟩
                    · obtain ⟨m, hm, hs2⟩ := hcA k hk
                      exact ⟨m, hm, dSubEq_trans hs hs2⟩
                  · exact ⟨k, List.mem_append.mpr (.inr (mem_ha_app p₂ hk)), hs⟩
                have coverQ : ∀ x ∈ q.leaves,
                    ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq x ℓ' := by
                  intro x hx
                  obtain ⟨ℓ₀, hm, hs⟩ :=
                    appForwardJoin_sound p₂ p₁ hf₂to₁ ha₂₁ cA' cInst x hx
                  rcases List.mem_append.mp hm with hm | hm
                  · rcases List.mem_append.mp hm with hm | hm
                    · rcases List.mem_append.mp hm with hm | hm
                      · rcases List.mem_append.mp hm with hm | hm
                        · rcases List.mem_append.mp hm with hm | hm
                          · exact ⟨ℓ₀, List.mem_append.mpr (.inr hm), hs⟩
                          · exact ⟨ℓ₀, List.mem_append.mpr (.inl hm), hs⟩
                        · obtain ⟨k, hk, hs2⟩ := hJfS ℓ₀ hm
                          exact ⟨k, hk, dSubEq_trans hs hs2⟩
                      · have hsplit := ha₂to₁.readConv_leaves (EvTc.symm cA) ℓ₀ hm
                        rcases List.mem_append.mp hsplit with hm | hm
                        · obtain ⟨k, hk, hs2⟩ := hJaS ℓ₀ hm
                          exact ⟨k, hk, dSubEq_trans hs hs2⟩
                        · have hm' : ℓ₀ ∈ cA.leaves := by
                            simpa only [EvTc.leaves] using hm
                          obtain ⟨k, hk, hs2⟩ := hcA ℓ₀ hm'
                          exact ⟨k, hk, dSubEq_trans hs hs2⟩
                    · have hm' : ℓ₀ ∈ cA.leaves := by
                        simpa only [cA', EvTc.leaves] using hm
                      obtain ⟨k, hk, hs2⟩ := hcA ℓ₀ hm'
                      exact ⟨k, hk, dSubEq_trans hs hs2⟩
                  · rw [hcInst] at hm
                    cases hm
                have _used := hCentre
                rcases hℓ with hℓ | hℓ
                · exact coverQ ℓ (q.rightTy_leaves ℓ hℓ)
                · exact coverQ ℓ hℓ }
          if hI : instantiate0 a₂ p₁.B = instantiate0 a p₁.B then
            let cInst : EvTc R Γ (instantiate0 a p₁.B) (instantiate0 a₂ p₁.B) :=
              EvTc.cast rfl hI rfl (EvTc.refl Γ (instantiate0 a₂ p₁.B))
            finish cInst (by simp only [cInst, EvTc.cast_leaves, EvTc.leaves])
          else
            match hL : instantiate0 a p₁.B, hR : instantiate0 a₂ p₁.B with
            | .sort u, .sort v =>
              if hN : decEqN u v = true then
                let cInst : EvTc R Γ (instantiate0 a p₁.B) (instantiate0 a₂ p₁.B) :=
                  EvTc.cast rfl hL.symm hR.symm
                    (.ofCv (.succ u) (.sorts u v (decEqN_sound u v hN)))
                finish cInst (by
                  simp only [cInst, EvTc.cast_leaves, EvTc.leaves, EvCv.leaves])
              else
                evParXAppInst
            | _, _ => evParXAppInst
    | some hf₁to₂ =>
      match hArg : stayRead Ja.left Ja.right with
      | none => evParXAppCentre
      | some ha₁to₂ =>
        let hf12 : EvPar R Γ f₁ f₂ p₂.T₀ := EvPar.dcast rfl rfl rfl hT hf₁to₂
        let ha12 : EvPar R Γ a₁ a₂ p₂.A := ha₁to₂
        let corner := appCornerJoin Jf Ja
        let finish
            (cInst : EvTc R Γ (instantiate0 a p₂.B) (instantiate0 a₁ p₂.B))
            (hcInst : cInst.leaves = []) :
            Option (EvParXJoin R Γ (.app f₁ a₁) (.app f₂ a₂) T
              (p₁.leaves ++ p₂.leaves)) :=
          let q := appForwardJoin p₁ p₂ hf12 ha12 cA cInst
          some {
            d := .app f₂ a₂
            left := .step (.app q)
            right := .stay q.rightTy
            sound := fun ℓ hℓ => by
              have hCentre : corner.centre = Expr.app f₂ a₂ :=
                appCorner_at_right Jf Ja hF hArg
              simp only [EvParXOpt.leaves, EvParX.leaves, List.mem_append] at hℓ
              have hJf : ∀ x ∈ hf₁to₂.leaves,
                  ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq x ℓ' := by
                intro x hx
                have hxL := stayRead_leaves Jf.left Jf.right hF x hx
                obtain ⟨k, hk, hs⟩ := Jf.sound x (List.mem_append.mpr (.inl hxL))
                rcases List.mem_append.mp hk with hk | hk
                · exact ⟨k, List.mem_append.mpr (.inl (mem_hf_app p₁ hk)), hs⟩
                · have hkR := appFunRead_leaves p₂.hf c₀ k hk
                  rw [hc0, List.append_nil] at hkR
                  exact ⟨k, List.mem_append.mpr (.inr (mem_hf_app p₂ hkR)), hs⟩
              have hJa : ∀ x ∈ ha₁to₂.leaves,
                  ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq x ℓ' := by
                intro x hx
                have hxL := stayRead_leaves Ja.left Ja.right hArg x hx
                obtain ⟨k, hk, hs⟩ := Ja.sound x (List.mem_append.mpr (.inl hxL))
                rcases List.mem_append.mp hk with hk | hk
                · have hsplit := p₁.ha.readConv_leaves cA k hk
                  rcases List.mem_append.mp hsplit with hk | hk
                  · exact ⟨k, List.mem_append.mpr (.inl (mem_ha_app p₁ hk)), hs⟩
                  · obtain ⟨m, hm, hs2⟩ := hcA k hk
                    exact ⟨m, hm, dSubEq_trans hs hs2⟩
                · exact ⟨k, List.mem_append.mpr (.inr (mem_ha_app p₂ hk)), hs⟩
              have coverQ : ∀ x ∈ q.leaves,
                  ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq x ℓ' := by
                intro x hx
                obtain ⟨ℓ₀, hm, hs⟩ :=
                  appForwardJoin_sound p₁ p₂ hf12 ha12 cA cInst x hx
                rcases List.mem_append.mp hm with hm | hm
                · rcases List.mem_append.mp hm with hm | hm
                  · rcases List.mem_append.mp hm with hm | hm
                    · rcases List.mem_append.mp hm with hm | hm
                      · rcases List.mem_append.mp hm with hm | hm
                        · exact ⟨ℓ₀, List.mem_append.mpr (.inl hm), hs⟩
                        · exact ⟨ℓ₀, List.mem_append.mpr (.inr hm), hs⟩
                      · have hm' : ℓ₀ ∈ hf₁to₂.leaves := by
                          simpa only [hf12, EvPar.dcast_leaves] using hm
                        obtain ⟨k, hk, hs2⟩ := hJf ℓ₀ hm'
                        exact ⟨k, hk, dSubEq_trans hs hs2⟩
                    · obtain ⟨k, hk, hs2⟩ := hJa ℓ₀ hm
                      exact ⟨k, hk, dSubEq_trans hs hs2⟩
                  · obtain ⟨k, hk, hs2⟩ := hcA ℓ₀ hm
                    exact ⟨k, hk, dSubEq_trans hs hs2⟩
                · rw [hcInst] at hm
                  cases hm
              have _used := hCentre
              rcases hℓ with hℓ | hℓ
              · exact coverQ ℓ hℓ
              · exact coverQ ℓ (q.rightTy_leaves ℓ hℓ) }
        if hI : instantiate0 a₁ p₂.B = instantiate0 a p₂.B then
          let cInst : EvTc R Γ (instantiate0 a p₂.B) (instantiate0 a₁ p₂.B) :=
            EvTc.cast rfl hI rfl (EvTc.refl Γ (instantiate0 a₁ p₂.B))
          finish cInst (by simp only [cInst, EvTc.cast_leaves, EvTc.leaves])
        else
          match hL : instantiate0 a p₂.B, hR : instantiate0 a₁ p₂.B with
          | .sort u, .sort v =>
            if hN : decEqN u v = true then
              let cInst : EvTc R Γ (instantiate0 a p₂.B) (instantiate0 a₁ p₂.B) :=
                EvTc.cast rfl hL.symm hR.symm
                  (.ofCv (.succ u) (.sorts u v (decEqN_sound u v hN)))
              finish cInst (by
                simp only [cInst, EvTc.cast_leaves, EvTc.leaves, EvCv.leaves])
            else
              evParXAppInst
          | _, _ => evParXAppInst
  else
    evParXAppT0

set_option maxHeartbeats 1000000 in
/-- The letE pair that is not a diagonal and not an identity replay.
    The first binder and the value stay put, the body indices agree, and both
    of those diamonds stay on the right. LetE has no Π, so `X` is received and
    not applied. A body-index mismatch or a right-stepping component on that
    path is `evParXLetEApart`. A moved binder or value is `evParXLetEMove`:
    the body diamond stays in the source let context. -/
def evParLetEGenJoinX (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A value body A₁ value₁ body₁ A₂ value₂ body₂ T : Expr Nat}
    (p₁ : LetEPayload R Γ A value body A₁ value₁ body₁ T)
    (p₂ : LetEPayload R Γ A value body A₂ value₂ body₂ T) :
    Option (EvParXJoin R Γ (.letE A₁ value₁ body₁) (.letE A₂ value₂ body₂) T
      (p₁.leaves ++ p₂.leaves)) :=
  if hA : A = A₁ then
    if hV : value = value₁ then
      if hB : p₁.B = p₂.B then
        let Jv := evParDiamondWf hW su hΓ p₁.hv p₂.hv
        match hVs : stayRead Jv.left Jv.right with
        | none => evParXLetEApart
        | some hv₁to₂ =>
          let hctx : (.letBinding A value :: Γ) = (.letBinding A₁ value₁ :: Γ) :=
            hA ▸ hV ▸ rfl
          let hb₁ := EvPar.dcast hctx rfl rfl hB p₁.hb
          let hb₂ := EvPar.dcast hctx rfl rfl rfl p₂.hb
          let hcl := envClosed_of_envWfT hW
          let hinst := envMembersSubstStable_of_envWfT hW
          let hA₁ := EvTy.cast rfl hA rfl p₁.hA
          let hvTy := EvTy.cast rfl rfl hA p₁.hv.rightTy
          let hΓB := CtxWfT.letBinding Γ A₁ p₁.u value₁ hΓ
            (hA₁.val hcl hinst) (hvTy.val hcl hinst)
          let Jb := evParDiamondWf hW su hΓB hb₁ hb₂
          match hBs : stayRead Jb.left Jb.right with
          | none => evParXLetEApart
          | some hb12 =>
            let hv12 := EvPar.dcast rfl rfl rfl hA hv₁to₂
            let hB₁ := EvTy.cast hctx rfl rfl p₂.hB
            let hInst := congrArg (fun v => instantiate0 v p₂.B) hV
            let hTy₁ := EvTy.cast rfl hInst rfl p₂.hTy
            let cInst := EvTc.cast rfl rfl hInst
              (EvTc.refl Γ (instantiate0 value p₂.B))
            let q := letEForwardJoin hW su hΓ p₁ p₂ hv12 hB₁ hTy₁ hb12 cInst
            some {
              d := .letE A₂ value₂ body₂
              left := .step (.letE q)
              right := .stay q.rightTy
              sound := fun ℓ hℓ => by
                simp only [EvParXOpt.leaves, EvParX.leaves, List.mem_append] at hℓ
                have hVal : ∀ x ∈ hv₁to₂.leaves,
                    ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq x ℓ' := by
                  intro x hx
                  have hxL := stayRead_leaves Jv.left Jv.right hVs x hx
                  obtain ⟨k, hk, hs⟩ := Jv.sound x (List.mem_append.mpr (.inl hxL))
                  refine ⟨k, ?_, hs⟩
                  rcases List.mem_append.mp hk with hk | hk
                  · exact List.mem_append.mpr (.inl (mem_hv_letE p₁ hk))
                  · exact List.mem_append.mpr (.inr (mem_hv_letE p₂ hk))
                have hBody : ∀ x ∈ hb12.leaves,
                    ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq x ℓ' := by
                  intro x hx
                  have hxL := stayRead_leaves Jb.left Jb.right hBs x hx
                  obtain ⟨k, hk, hs⟩ := Jb.sound x (List.mem_append.mpr (.inl hxL))
                  have hkEq : k ∈ p₁.hb.leaves ++ p₂.hb.leaves := by
                    simpa only [hb₁, hb₂, EvPar.dcast_leaves] using hk
                  refine ⟨k, ?_, hs⟩
                  rcases List.mem_append.mp hkEq with hk | hk
                  · exact List.mem_append.mpr (.inl (mem_hb_letE p₁ hk))
                  · exact List.mem_append.mpr (.inr (mem_hb_letE p₂ hk))
                have coverQ : ∀ x ∈ q.leaves,
                    ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq x ℓ' := by
                  intro x hx
                  obtain ⟨ℓ₀, hm, hs⟩ :=
                    letEForwardJoin_sound hW su hΓ p₁ p₂ hv12 hB₁ hTy₁ hb12 cInst x hx
                  rcases List.mem_append.mp hm with hm | hm
                  · rcases List.mem_append.mp hm with hm | hm
                    · rcases List.mem_append.mp hm with hm | hm
                      · rcases List.mem_append.mp hm with hm | hm
                        · rcases List.mem_append.mp hm with hm | hm
                          · rcases List.mem_append.mp hm with hm | hm
                            · exact ⟨ℓ₀, List.mem_append.mpr (.inl hm), hs⟩
                            · exact ⟨ℓ₀, List.mem_append.mpr (.inr hm), hs⟩
                          · have hm' : ℓ₀ ∈ hv₁to₂.leaves := by
                              simpa only [hv12, EvPar.dcast_leaves] using hm
                            obtain ⟨k, hk, hs2⟩ := hVal ℓ₀ hm'
                            exact ⟨k, hk, dSubEq_trans hs hs2⟩
                        · have hm' : ℓ₀ ∈ p₂.hB.leaves := by
                            simpa only [hB₁, EvTy.cast_leaves] using hm
                          exact ⟨ℓ₀, List.mem_append.mpr (.inr (mem_hB_letE p₂ hm')), hs⟩
                      · have hm' : ℓ₀ ∈ p₂.hTy.leaves := by
                          simpa only [hTy₁, EvTy.cast_leaves] using hm
                        exact ⟨ℓ₀, List.mem_append.mpr (.inr (mem_hTy_letE p₂ hm')), hs⟩
                    · obtain ⟨k, hk, hs2⟩ := hBody ℓ₀ hm
                      exact ⟨k, hk, dSubEq_trans hs hs2⟩
                  · simp only [cInst, EvTc.cast_leaves, EvTc.leaves] at hm
                    cases hm
                rcases hℓ with hℓ | hℓ
                · exact coverQ ℓ hℓ
                · exact coverQ ℓ (q.rightTy_leaves ℓ hℓ) }
      else
        evParXLetEApart
    else
      evParXLetEMove hW su hΓ p₁ p₂
  else
    evParXLetEMove hW su hΓ p₁ p₂

/-- `app × app` inside the X-fed dispatcher. Equal targets stay via `rightTy`.
    An identity first input (`source = target`) against a different target replays
    the second input: `.step` of that input and `.stay` of its `rightTy`.
    An identity second input against a different target replays the first input:
    `.stay` of its `rightTy` and `.step` of that input. None of those branches
    calls `XProc`. The remaining pair is `evParAppGenJoinX`: equal `T₀`,
    `appCornerJoin`, and a definitional or `=ₙ`-sort instantiation. Anything
    that pair refuses stays a named `none`.
    This is not a `some` for every unequal pair. Star closure and supplying `X`
    from piRow remain #7156. -/
def evParAppStayCast {Γ : LCtx} {f a f₁ a₁ f₂ a₂ T : Expr Nat}
    (h : Expr.app f₁ a₁ = Expr.app f₂ a₂)
    (p₁ : AppPayload R Γ f a f₁ a₁ T) (p₂ : AppPayload R Γ f a f₂ a₂ T) :
    EvParXJoin R Γ (Expr.app f₁ a₁) (Expr.app f₂ a₂) T
      ((EvParX.app p₁).leaves ++ (EvParX.app p₂).leaves) :=
  match f₁, a₁, f₂, a₂, h with
  | _, _, _, _, rfl => evParAppDiagJoin p₁ p₂

/-- Identity app against any second app with the same source. The join is the
    second input itself, so its leaves sit in `p₁.leaves ++ p₂.leaves`. -/
def evParAppIdReplay {Γ : LCtx} {f a f₁ a₁ f₂ a₂ T : Expr Nat}
    (h : Expr.app f a = Expr.app f₁ a₁)
    (p₁ : AppPayload R Γ f a f₁ a₁ T) (p₂ : AppPayload R Γ f a f₂ a₂ T) :
    EvParXJoin R Γ (Expr.app f₁ a₁) (Expr.app f₂ a₂) T
      ((EvParX.app p₁).leaves ++ (EvParX.app p₂).leaves) :=
  match f, a, f₁, a₁, h with
  | _, _, _, _, rfl =>
    { d := Expr.app f₂ a₂
      left := .step (.app p₂)
      right := .stay (EvParX.app p₂).rightTy
      sound := fun ℓ hℓ => by
        simp only [EvParXOpt.leaves, List.mem_append] at hℓ
        refine dSubEq_of_mem (List.mem_append.mpr (.inr ?_))
        rcases hℓ with h | h
        · exact h
        · exact (EvParX.app p₂).rightTy_leaves ℓ h }

/-- Identity second app against a non-identity first app with the same source.
    The join is the first input: stay at its `rightTy`, step that input.
    Both closing leaves sit in `p₁.leaves ++ p₂.leaves`. Not an `XProc` call. -/
def evParAppRevReplay {Γ : LCtx} {f a f₁ a₁ f₂ a₂ T : Expr Nat}
    (h : Expr.app f a = Expr.app f₂ a₂)
    (p₁ : AppPayload R Γ f a f₁ a₁ T) (p₂ : AppPayload R Γ f a f₂ a₂ T) :
    EvParXJoin R Γ (Expr.app f₁ a₁) (Expr.app f₂ a₂) T
      ((EvParX.app p₁).leaves ++ (EvParX.app p₂).leaves) :=
  match f, a, f₂, a₂, h with
  | _, _, _, _, rfl =>
    { d := Expr.app f₁ a₁
      left := .stay (EvParX.app p₁).rightTy
      right := .step (.app p₁)
      sound := fun ℓ hℓ => by
        simp only [EvParXOpt.leaves, List.mem_append] at hℓ
        refine dSubEq_of_mem (List.mem_append.mpr (.inl ?_))
        rcases hℓ with h | h
        · exact (EvParX.app p₁).rightTy_leaves ℓ h
        · exact h }

def evParAppStayJoinX (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f a f₁ a₁ f₂ a₂ T : Expr Nat}
    (p₁ : AppPayload R Γ f a f₁ a₁ T) (p₂ : AppPayload R Γ f a f₂ a₂ T) :
    Option (EvParXJoin R Γ (.app f₁ a₁) (.app f₂ a₂) T
      ((EvParX.app p₁).leaves ++ (EvParX.app p₂).leaves)) :=
  if h : Expr.app f₁ a₁ = Expr.app f₂ a₂ then
    some (evParAppStayCast h p₁ p₂)
  else if hId : Expr.app f a = Expr.app f₁ a₁ then
    some (evParAppIdReplay hId p₁ p₂)
  else if hRev : Expr.app f a = Expr.app f₂ a₂ then
    some (evParAppRevReplay hRev p₁ p₂)
  else
    evParAppGenJoinX hW su X hX hΓ p₁ p₂

def evParLetEStayCast {Γ : LCtx}
    {A value body A₁ value₁ body₁ A₂ value₂ body₂ T : Expr Nat}
    (h : Expr.letE A₁ value₁ body₁ = Expr.letE A₂ value₂ body₂)
    (p₁ : LetEPayload R Γ A value body A₁ value₁ body₁ T)
    (p₂ : LetEPayload R Γ A value body A₂ value₂ body₂ T) :
    EvParXJoin R Γ (Expr.letE A₁ value₁ body₁) (Expr.letE A₂ value₂ body₂) T
      ((EvParX.letE p₁).leaves ++ (EvParX.letE p₂).leaves) :=
  match A₁, value₁, body₁, A₂, value₂, body₂, h with
  | _, _, _, _, _, _, rfl => evParLetEDiagJoin p₁ p₂

/-- Identity letE against any second letE with the same source. Same join shape
    as `evParAppIdReplay`. -/
def evParLetEIdReplay {Γ : LCtx}
    {A value body A₁ value₁ body₁ A₂ value₂ body₂ T : Expr Nat}
    (h : Expr.letE A value body = Expr.letE A₁ value₁ body₁)
    (p₁ : LetEPayload R Γ A value body A₁ value₁ body₁ T)
    (p₂ : LetEPayload R Γ A value body A₂ value₂ body₂ T) :
    EvParXJoin R Γ (Expr.letE A₁ value₁ body₁) (Expr.letE A₂ value₂ body₂) T
      ((EvParX.letE p₁).leaves ++ (EvParX.letE p₂).leaves) :=
  match A, value, body, A₁, value₁, body₁, h with
  | _, _, _, _, _, _, rfl =>
    { d := Expr.letE A₂ value₂ body₂
      left := .step (.letE p₂)
      right := .stay (EvParX.letE p₂).rightTy
      sound := fun ℓ hℓ => by
        simp only [EvParXOpt.leaves, List.mem_append] at hℓ
        refine dSubEq_of_mem (List.mem_append.mpr (.inr ?_))
        rcases hℓ with h | h
        · exact h
        · exact (EvParX.letE p₂).rightTy_leaves ℓ h }

/-- Identity second letE against a non-identity first letE with the same source.
    Same join shape as `evParAppRevReplay`. -/
def evParLetERevReplay {Γ : LCtx}
    {A value body A₁ value₁ body₁ A₂ value₂ body₂ T : Expr Nat}
    (h : Expr.letE A value body = Expr.letE A₂ value₂ body₂)
    (p₁ : LetEPayload R Γ A value body A₁ value₁ body₁ T)
    (p₂ : LetEPayload R Γ A value body A₂ value₂ body₂ T) :
    EvParXJoin R Γ (Expr.letE A₁ value₁ body₁) (Expr.letE A₂ value₂ body₂) T
      ((EvParX.letE p₁).leaves ++ (EvParX.letE p₂).leaves) :=
  match A, value, body, A₂, value₂, body₂, h with
  | _, _, _, _, _, _, rfl =>
    { d := Expr.letE A₁ value₁ body₁
      left := .stay (EvParX.letE p₁).rightTy
      right := .step (.letE p₁)
      sound := fun ℓ hℓ => by
        simp only [EvParXOpt.leaves, List.mem_append] at hℓ
        refine dSubEq_of_mem (List.mem_append.mpr (.inl ?_))
        rcases hℓ with h | h
        · exact (EvParX.letE p₁).rightTy_leaves ℓ h
        · exact h }

/-- `letE × letE`. The diagonal and either identity replay do not call `XProc`.
    The remaining pair is `evParLetEGenJoinX`. -/
def evParLetEStayJoinX (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A value body A₁ value₁ body₁ A₂ value₂ body₂ T : Expr Nat}
    (p₁ : LetEPayload R Γ A value body A₁ value₁ body₁ T)
    (p₂ : LetEPayload R Γ A value body A₂ value₂ body₂ T) :
    Option (EvParXJoin R Γ (.letE A₁ value₁ body₁) (.letE A₂ value₂ body₂) T
      ((EvParX.letE p₁).leaves ++ (EvParX.letE p₂).leaves)) :=
  if h : Expr.letE A₁ value₁ body₁ = Expr.letE A₂ value₂ body₂ then
    some (evParLetEStayCast h p₁ p₂)
  else if hId : Expr.letE A value body = Expr.letE A₁ value₁ body₁ then
    some (evParLetEIdReplay hId p₁ p₂)
  else if hRev : Expr.letE A value body = Expr.letE A₂ value₂ body₂ then
    some (evParLetERevReplay hRev p₁ p₂)
  else
    evParLetEGenJoinX hW su X hX hΓ p₁ p₂

/-- Single-step diamond on `EvParX`. `embed × embed` reuses the landed total diamond.
    `X` is consumed by the lam stay arm (`lamForwardJoin`). The app and letE arms
    receive the same `X` and `hX`. Their diagonal is a stay. An identity on one
    side replays the other input (the second if the first is the identity, the
    first if the second is). Neither replay calls `XProc`. The remaining pair
    is the forward join (`evParAppGenJoinX` uses `X`; letE has no Π to apply
    it to). -/
def evParDiamondWfX (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat} :
    (D₁ : EvParX R Γ a b T) → (D₂ : EvParX R Γ a c T) →
    Option (EvParXJoin R Γ b c T (D₁.leaves ++ D₂.leaves))
  | .embed D₁, .embed D₂ => some (ofLanded (evParDiamondWf hW su hΓ D₁ D₂))
  | .embed (.proofIndex p₁), D₂ => some (proofIndexLeftJoinX p₁ D₂)
  | D₁, .embed (.proofIndex p₂) => some (proofIndexRightJoinX D₁ p₂)
  | .embed (.refl p₁), D₂ => some (reflLeftJoinX p₁ D₂)
  | D₁, .embed (.refl p₂) => some (reflRightJoinX D₁ p₂)
  | .embed (.consts _), .delta _ => evParXConstsDelta
  | .delta _, .embed (.consts _) => evParXDeltaConsts
  | .delta p₁, .delta p₂ => some (ofLanded (deltaJoin p₁ p₂))
  | .bvarZeta p₁, .bvarZeta p₂ => some (ofLanded (bvarZetaJoin hW su hΓ p₁ p₂))
  | .lam p₁, .lam p₂ => evParLamStayJoinX hW su X hX hΓ p₁ p₂
  | .app p₁, .app p₂ => evParAppStayJoinX hW su X hX hΓ p₁ p₂
  | .letE p₁, .letE p₂ => evParLetEStayJoinX hW su X hX hΓ p₁ p₂
  -- Cross-kind pairs (lam×delta, bvar×app, …) are index-disjoint: the shared
  -- source forces the same head. Lean rejects them as unreachable, so there is
  -- no catch-all. consts×delta stays the named `none` above.

/-- One-step `dProcWf` over `EvParX`. Star closure stays on #7156. -/
def dProcWfX (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (D₁ : EvParX R Γ a b T) (D₂ : EvParX R Γ a c T) :
    Option (EvParXJoin R Γ b c T (D₁.leaves ++ D₂.leaves)) :=
  evParDiamondWfX hW su X hX hΓ D₁ D₂

end Diamond

/-! ### diagonal app/app and letE/letE (sol3 Q102)
The X-fed dispatcher is called on `pinAppPayload []` and `pinLetEPayload []`
paired with themselves. Both legs stay at that common target. The leaf budget
is the two inputs' leaves. `mutantAppLetERefuse` is the old unconditional `none`. -/

private def pinAppD : EvParX (DTilePins.pinAppRoots []) []
    (.app DTilePins.pinAppFun (.sort (.max .zero .zero)))
    (.app DTilePins.pinAppFun (.sort .zero)) DTilePins.pinAppCod :=
  .app (DTilePins.pinAppPayload [])

private def pinLetED : EvParX [DTilePins.pinLetERoot []] []
    (.letE DTilePins.pinAppDom (.sort (.max .zero .zero)) (.sort (.max .zero .zero)))
    (.letE DTilePins.pinAppDom (.sort .zero) (.sort .zero)) DTilePins.pinAppDom :=
  .letE (DTilePins.pinLetEPayload [])

private def pinAppJ : EvParXJoin (DTilePins.pinAppRoots []) []
    (.app DTilePins.pinAppFun (.sort .zero))
    (.app DTilePins.pinAppFun (.sort .zero)) DTilePins.pinAppCod
    (pinAppD.leaves ++ pinAppD.leaves) :=
  evParAppDiagJoin (DTilePins.pinAppPayload []) (DTilePins.pinAppPayload [])

private def pinLetEJ : EvParXJoin [DTilePins.pinLetERoot []] []
    (.letE DTilePins.pinAppDom (.sort .zero) (.sort .zero))
    (.letE DTilePins.pinAppDom (.sort .zero) (.sort .zero)) DTilePins.pinAppDom
    (pinLetED.leaves ++ pinLetED.leaves) :=
  evParLetEDiagJoin (DTilePins.pinLetEPayload []) (DTilePins.pinLetEPayload [])

private theorem pinAppStayEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParAppStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil (DTilePins.pinAppPayload []) (DTilePins.pinAppPayload []) =
      some pinAppJ := by
  unfold evParAppStayJoinX evParAppStayCast pinAppJ
  rfl

theorem pinAppDiag
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppD pinAppD = some pinAppJ ∧
      dProcWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppD pinAppD = some pinAppJ ∧
      pinAppJ.d = .app DTilePins.pinAppFun (.sort .zero) ∧
      ∀ ℓ ∈ pinAppJ.left.leaves ++ pinAppJ.right.leaves,
        ∃ ℓ' ∈ pinAppD.leaves ++ pinAppD.leaves, SubEq ℓ ℓ' := by
  refine ⟨?_, ?_, rfl, pinAppJ.sound⟩
  · unfold evParDiamondWfX pinAppD
    exact pinAppStayEq X hX su
  · unfold dProcWfX evParDiamondWfX pinAppD
    exact pinAppStayEq X hX su

private theorem pinLetEStayEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParLetEStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil (DTilePins.pinLetEPayload []) (DTilePins.pinLetEPayload []) =
      some pinLetEJ := by
  unfold evParLetEStayJoinX evParLetEStayCast pinLetEJ
  rfl

theorem pinLetEDiag
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetED pinLetED = some pinLetEJ ∧
      dProcWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetED pinLetED = some pinLetEJ ∧
      pinLetEJ.d = .letE DTilePins.pinAppDom (.sort .zero) (.sort .zero) ∧
      ∀ ℓ ∈ pinLetEJ.left.leaves ++ pinLetEJ.right.leaves,
        ∃ ℓ' ∈ pinLetED.leaves ++ pinLetED.leaves, SubEq ℓ ℓ' := by
  refine ⟨?_, ?_, rfl, pinLetEJ.sound⟩
  · unfold evParDiamondWfX pinLetED
    exact pinLetEStayEq X hX su
  · unfold dProcWfX evParDiamondWfX pinLetED
    exact pinLetEStayEq X hX su

/-- The old unconditional refusal does not match the repaired app diagonal. -/
theorem pinAppMutant
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    mutantAppLetERefuse ≠
      evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppD pinAppD := by
  intro h
  have hsome := (pinAppDiag X hX su).1
  rw [hsome] at h
  exact Option.noConfusion h

/-! ### unequal identity × widened pin (sol3 Q113)
The first input is an identity payload whose `hr` is the source typing literal.
The second is `pinAppPayload` / `pinLetEPayload`, widened only so that literal
is in `R`. Targets differ. The join steps the second input and stays at its
`rightTy`. `su`, `X`, and `hX` stay abstract. `mutantAppLetEIdRefuse` is the
old constant `none` on that unequal pair; `mutantAppLetERefuse` is not this tooth. -/

def pinAppSrcTy :
    HasTyT emptyEnv 0 []
      (.app DTilePins.pinAppFun (.sort (.max .zero .zero))) DTilePins.pinAppCod :=
  .app [] DTilePins.pinAppFun (.sort (.max .zero .zero))
    DTilePins.pinAppDom DTilePins.pinAppCod
    (DTilePins.pinAppFunTy [])
    (.sort [] (.max .zero .zero))

def pinAppIdRoots : List (Jd emptyEnv 0) :=
  .ty pinAppSrcTy :: DTilePins.pinAppRoots []

def pinAppIdPayload :
    AppPayload pinAppIdRoots []
      DTilePins.pinAppFun (.sort (.max .zero .zero))
      DTilePins.pinAppFun (.sort (.max .zero .zero))
      DTilePins.pinAppCod where
  T₀ := .pi DTilePins.pinAppDom DTilePins.pinAppCod
  A := DTilePins.pinAppDom
  B := DTilePins.pinAppCod
  u := .succ (.succ (.max .zero .zero))
  v := .succ (.succ .zero)
  w := .succ (.succ .zero)
  hf := .ofTy (.lit (DTilePins.pinAppFunTy [])
    ⟨_, List.Mem.tail _ (List.Mem.head _), .inl rfl⟩)
  hc := .refl [] (.pi DTilePins.pinAppDom DTilePins.pinAppCod)
  hPi := .lit (DTilePins.pinAppPiTy [])
    ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), .inl rfl⟩
  hB := .sort (.succ .zero)
  hTy := .sort (.succ .zero)
  ha := .ofTy (.sort (.max .zero .zero))
  hr := .lit pinAppSrcTy ⟨_, List.Mem.head _, .inl rfl⟩
  idx := .refl [] DTilePins.pinAppCod

def pinAppWide :
    AppPayload pinAppIdRoots []
      DTilePins.pinAppFun (.sort (.max .zero .zero))
      DTilePins.pinAppFun (.sort .zero) DTilePins.pinAppCod :=
  (DTilePins.pinAppPayload []).widen (fun _ hx => List.Mem.tail _ hx)

def pinAppIdD : EvParX pinAppIdRoots []
    (.app DTilePins.pinAppFun (.sort (.max .zero .zero)))
    (.app DTilePins.pinAppFun (.sort (.max .zero .zero))) DTilePins.pinAppCod :=
  .app pinAppIdPayload

def pinAppWideD : EvParX pinAppIdRoots []
    (.app DTilePins.pinAppFun (.sort (.max .zero .zero)))
    (.app DTilePins.pinAppFun (.sort .zero)) DTilePins.pinAppCod :=
  .app pinAppWide

private def pinAppUnequalJ : EvParXJoin pinAppIdRoots []
    (.app DTilePins.pinAppFun (.sort (.max .zero .zero)))
    (.app DTilePins.pinAppFun (.sort .zero)) DTilePins.pinAppCod
    (pinAppIdD.leaves ++ pinAppWideD.leaves) :=
  evParAppIdReplay rfl pinAppIdPayload pinAppWide

private theorem pinAppIdReplayEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParAppStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil pinAppIdPayload pinAppWide = some pinAppUnequalJ := by
  unfold evParAppStayJoinX evParAppIdReplay pinAppUnequalJ
  rfl

theorem pinAppUnequal
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    Expr.app DTilePins.pinAppFun (.sort (.max .zero .zero)) ≠
        Expr.app DTilePins.pinAppFun (.sort .zero) ∧
      evParAppStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil pinAppIdPayload pinAppWide = some pinAppUnequalJ ∧
      evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppIdD pinAppWideD = some pinAppUnequalJ ∧
      dProcWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppIdD pinAppWideD = some pinAppUnequalJ ∧
      pinAppUnequalJ.left = .step pinAppWideD ∧
      pinAppUnequalJ.right = .stay pinAppWideD.rightTy ∧
      ∀ ℓ ∈ pinAppUnequalJ.left.leaves ++ pinAppUnequalJ.right.leaves,
        ∃ ℓ' ∈ pinAppIdD.leaves ++ pinAppWideD.leaves, SubEq ℓ ℓ' := by
  refine ⟨?_, pinAppIdReplayEq X hX su, ?_, ?_, rfl, rfl, pinAppUnequalJ.sound⟩
  · decide
  · unfold evParDiamondWfX pinAppIdD
    exact pinAppIdReplayEq X hX su
  · unfold dProcWfX evParDiamondWfX pinAppIdD
    exact pinAppIdReplayEq X hX su

def pinLetESrcTy :
    HasTyT emptyEnv 0 []
      (.letE DTilePins.pinAppDom (.sort (.max .zero .zero))
        (.sort (.max .zero .zero))) DTilePins.pinAppDom :=
  .letE [] DTilePins.pinAppDom (.succ (.succ (.max .zero .zero)))
    (.sort (.max .zero .zero)) DTilePins.pinAppDom (.sort (.max .zero .zero))
    (.sort [] (.succ (.max .zero .zero)))
    (.sort [] (.max .zero .zero))
    (.sort [.letBinding DTilePins.pinAppDom (.sort (.max .zero .zero))]
      (.max .zero .zero))

def pinLetEIdRoots : List (Jd emptyEnv 0) :=
  [.ty pinLetESrcTy, DTilePins.pinLetERoot []]

def pinLetEIdPayload :
    LetEPayload pinLetEIdRoots []
      DTilePins.pinAppDom (.sort (.max .zero .zero)) (.sort (.max .zero .zero))
      DTilePins.pinAppDom (.sort (.max .zero .zero)) (.sort (.max .zero .zero))
      DTilePins.pinAppDom where
  B := DTilePins.pinAppDom
  u := .succ (.succ (.max .zero .zero))
  w := .succ (.succ (.max .zero .zero))
  hc := .refl (.sort (.succ (.max .zero .zero)))
  hA := .sort (.succ (.max .zero .zero))
  hv := .ofTy (.sort (.max .zero .zero))
  hB := .sort (.succ (.max .zero .zero))
  hTy := .sort (.succ (.max .zero .zero))
  hb := .ofTy (.sort (.max .zero .zero))
  hrt := .lit pinLetESrcTy ⟨_, List.Mem.head _, .inl rfl⟩
  idx := .refl [] DTilePins.pinAppDom

def pinLetEWide :
    LetEPayload pinLetEIdRoots []
      DTilePins.pinAppDom (.sort (.max .zero .zero)) (.sort (.max .zero .zero))
      DTilePins.pinAppDom (.sort .zero) (.sort .zero) DTilePins.pinAppDom :=
  (DTilePins.pinLetEPayload []).widen (fun _ hx => List.Mem.tail _ hx)

def pinLetEIdD : EvParX pinLetEIdRoots []
    (.letE DTilePins.pinAppDom (.sort (.max .zero .zero)) (.sort (.max .zero .zero)))
    (.letE DTilePins.pinAppDom (.sort (.max .zero .zero)) (.sort (.max .zero .zero)))
    DTilePins.pinAppDom :=
  .letE pinLetEIdPayload

def pinLetEWideD : EvParX pinLetEIdRoots []
    (.letE DTilePins.pinAppDom (.sort (.max .zero .zero)) (.sort (.max .zero .zero)))
    (.letE DTilePins.pinAppDom (.sort .zero) (.sort .zero)) DTilePins.pinAppDom :=
  .letE pinLetEWide

private def pinLetEUnequalJ : EvParXJoin pinLetEIdRoots []
    (.letE DTilePins.pinAppDom (.sort (.max .zero .zero)) (.sort (.max .zero .zero)))
    (.letE DTilePins.pinAppDom (.sort .zero) (.sort .zero)) DTilePins.pinAppDom
    (pinLetEIdD.leaves ++ pinLetEWideD.leaves) :=
  evParLetEIdReplay rfl pinLetEIdPayload pinLetEWide

private theorem pinLetEIdReplayEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParLetEStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil pinLetEIdPayload pinLetEWide = some pinLetEUnequalJ := by
  unfold evParLetEStayJoinX evParLetEIdReplay pinLetEUnequalJ
  rfl

theorem pinLetEUnequal
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    Expr.letE DTilePins.pinAppDom (.sort (.max .zero .zero)) (.sort (.max .zero .zero)) ≠
        Expr.letE DTilePins.pinAppDom (.sort .zero) (.sort .zero) ∧
      evParLetEStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil pinLetEIdPayload pinLetEWide = some pinLetEUnequalJ ∧
      evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEIdD pinLetEWideD = some pinLetEUnequalJ ∧
      dProcWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEIdD pinLetEWideD = some pinLetEUnequalJ ∧
      pinLetEUnequalJ.left = .step pinLetEWideD ∧
      pinLetEUnequalJ.right = .stay pinLetEWideD.rightTy ∧
      ∀ ℓ ∈ pinLetEUnequalJ.left.leaves ++ pinLetEUnequalJ.right.leaves,
        ∃ ℓ' ∈ pinLetEIdD.leaves ++ pinLetEWideD.leaves, SubEq ℓ ℓ' := by
  refine ⟨?_, pinLetEIdReplayEq X hX su, ?_, ?_, rfl, rfl, pinLetEUnequalJ.sound⟩
  · decide
  · unfold evParDiamondWfX pinLetEIdD
    exact pinLetEIdReplayEq X hX su
  · unfold dProcWfX evParDiamondWfX pinLetEIdD
    exact pinLetEIdReplayEq X hX su

/-- Old constant `none` on the unequal identity×pin pair. The diagonal tooth
    `mutantAppLetERefuse` is a different witness. -/
def mutantAppLetEIdRefuse {α : Type} : Option α := none

theorem pinAppUnequalMutant
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    mutantAppLetEIdRefuse ≠
      evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppIdD pinAppWideD := by
  intro h
  have hsome := (pinAppUnequal X hX su).2.2.1
  rw [hsome] at h
  exact Option.noConfusion h

/-! ### reverse: widened pin × identity (audit 20:57Z)
The first input is the widened moving pin. The second is the identity payload.
Targets differ. The join stays at the first input's `rightTy` and steps that
same input. `su`, `X`, and `hX` stay abstract. `mutantAppLetERevRefuse` is the
old constant `none` on that swapped pair. The diagonal tooth and
`mutantAppLetEIdRefuse` are not this tooth. Other unequal pairs stay `none`. -/

private theorem mem_hr_app {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) {ℓ : Jd E n} (h : ℓ ∈ p.hr.leaves) :
    ℓ ∈ p.leaves := by
  unfold AppPayload.leaves
  exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))

private theorem mem_hrt_letE {Γ : LCtx}
    {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) {ℓ : Jd E n}
    (h : ℓ ∈ p.hrt.leaves) : ℓ ∈ p.leaves := by
  unfold LetEPayload.leaves
  exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))

private theorem ne_of_mem {α : Type} {a : α} {l : List α} (h : a ∈ l) : l ≠ [] := by
  rintro rfl
  cases h

private theorem pinAppId_leaves_ne : pinAppIdD.leaves ≠ [] := by
  have hleaf : .ty pinAppSrcTy ∈ pinAppIdPayload.hr.leaves := by
    unfold pinAppIdPayload EvTy.leaves
    exact List.mem_cons_self _ _
  exact ne_of_mem <| by
    simpa only [pinAppIdD, EvParX.leaves] using mem_hr_app pinAppIdPayload hleaf

private theorem pinAppWide_leaves_ne : pinAppWideD.leaves ≠ [] := by
  have hleaf : .ty (DTilePins.pinAppResTy []) ∈ pinAppWide.hr.leaves := by
    simp only [pinAppWide, AppPayload.widen, DTilePins.pinAppPayload,
      EvTy.widen, EvTy.leaves]
    exact List.mem_cons_self _ _
  exact ne_of_mem <| by
    simpa only [pinAppWideD, EvParX.leaves] using mem_hr_app pinAppWide hleaf

private theorem pinLetEId_leaves_ne : pinLetEIdD.leaves ≠ [] := by
  have hleaf : .ty pinLetESrcTy ∈ pinLetEIdPayload.hrt.leaves := by
    unfold pinLetEIdPayload EvTy.leaves
    exact List.mem_cons_self _ _
  exact ne_of_mem <| by
    simpa only [pinLetEIdD, EvParX.leaves] using mem_hrt_letE pinLetEIdPayload hleaf

private theorem pinLetEWide_leaves_ne : pinLetEWideD.leaves ≠ [] := by
  have hleaf : .ty (DTilePins.pinTargetLetE []) ∈ pinLetEWide.hrt.leaves := by
    simp only [pinLetEWide, LetEPayload.widen, DTilePins.pinLetEPayload,
      EvTy.widen, EvTy.leaves, EvTc.leaves]
    exact List.mem_append.mpr (.inl (List.mem_cons_self _ _))
  exact ne_of_mem <| by
    simpa only [pinLetEWideD, EvParX.leaves] using mem_hrt_letE pinLetEWide hleaf

def pinAppRevJ : EvParXJoin pinAppIdRoots []
    (.app DTilePins.pinAppFun (.sort .zero))
    (.app DTilePins.pinAppFun (.sort (.max .zero .zero))) DTilePins.pinAppCod
    (pinAppWideD.leaves ++ pinAppIdD.leaves) :=
  evParAppRevReplay rfl pinAppWide pinAppIdPayload

private theorem pinAppRevReplayEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParAppStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil pinAppWide pinAppIdPayload = some pinAppRevJ := by
  unfold evParAppStayJoinX evParAppRevReplay pinAppRevJ
  rfl

private theorem pinAppRevDiaEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppWideD pinAppIdD = some pinAppRevJ := by
  unfold evParDiamondWfX pinAppWideD
  exact pinAppRevReplayEq X hX su

private theorem pinAppRevProcEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    dProcWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppWideD pinAppIdD = some pinAppRevJ := by
  unfold dProcWfX
  exact pinAppRevDiaEq X hX su

theorem pinAppRev
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    Expr.app DTilePins.pinAppFun (.sort (.max .zero .zero)) ≠
        Expr.app DTilePins.pinAppFun (.sort .zero) ∧
      evParAppStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil pinAppWide pinAppIdPayload = some pinAppRevJ ∧
      evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppWideD pinAppIdD = some pinAppRevJ ∧
      dProcWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppWideD pinAppIdD = some pinAppRevJ ∧
      pinAppRevJ.d = .app DTilePins.pinAppFun (.sort .zero) ∧
      pinAppRevJ.left = .stay pinAppWideD.rightTy ∧
      pinAppRevJ.right = .step pinAppWideD ∧
      (∀ ℓ ∈ pinAppRevJ.left.leaves ++ pinAppRevJ.right.leaves,
        ∃ ℓ' ∈ pinAppWideD.leaves ++ pinAppIdD.leaves, SubEq ℓ ℓ') ∧
      pinAppWideD.leaves ≠ [] ∧
      pinAppIdD.leaves ≠ [] := by
  exact ⟨by decide, pinAppRevReplayEq X hX su, pinAppRevDiaEq X hX su,
    pinAppRevProcEq X hX su, rfl, rfl, rfl, pinAppRevJ.sound,
    pinAppWide_leaves_ne, pinAppId_leaves_ne⟩

def pinLetERevJ : EvParXJoin pinLetEIdRoots []
    (.letE DTilePins.pinAppDom (.sort .zero) (.sort .zero))
    (.letE DTilePins.pinAppDom (.sort (.max .zero .zero))
      (.sort (.max .zero .zero))) DTilePins.pinAppDom
    (pinLetEWideD.leaves ++ pinLetEIdD.leaves) :=
  evParLetERevReplay rfl pinLetEWide pinLetEIdPayload

private theorem pinLetERevReplayEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParLetEStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil pinLetEWide pinLetEIdPayload = some pinLetERevJ := by
  unfold evParLetEStayJoinX evParLetERevReplay pinLetERevJ
  rfl

private theorem pinLetERevDiaEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEWideD pinLetEIdD = some pinLetERevJ := by
  unfold evParDiamondWfX pinLetEWideD
  exact pinLetERevReplayEq X hX su

private theorem pinLetERevProcEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    dProcWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEWideD pinLetEIdD = some pinLetERevJ := by
  unfold dProcWfX
  exact pinLetERevDiaEq X hX su

theorem pinLetERev
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    Expr.letE DTilePins.pinAppDom (.sort (.max .zero .zero))
        (.sort (.max .zero .zero)) ≠
        Expr.letE DTilePins.pinAppDom (.sort .zero) (.sort .zero) ∧
      evParLetEStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil pinLetEWide pinLetEIdPayload = some pinLetERevJ ∧
      evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEWideD pinLetEIdD = some pinLetERevJ ∧
      dProcWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEWideD pinLetEIdD = some pinLetERevJ ∧
      pinLetERevJ.d = .letE DTilePins.pinAppDom (.sort .zero) (.sort .zero) ∧
      pinLetERevJ.left = .stay pinLetEWideD.rightTy ∧
      pinLetERevJ.right = .step pinLetEWideD ∧
      (∀ ℓ ∈ pinLetERevJ.left.leaves ++ pinLetERevJ.right.leaves,
        ∃ ℓ' ∈ pinLetEWideD.leaves ++ pinLetEIdD.leaves, SubEq ℓ ℓ') ∧
      pinLetEWideD.leaves ≠ [] ∧
      pinLetEIdD.leaves ≠ [] := by
  exact ⟨by decide, pinLetERevReplayEq X hX su, pinLetERevDiaEq X hX su,
    pinLetERevProcEq X hX su, rfl, rfl, rfl, pinLetERevJ.sound,
    pinLetEWide_leaves_ne, pinLetEId_leaves_ne⟩

/-- Old constant `none` on the reversed widened-pin × identity pair.
    `mutantAppLetERefuse` is the diagonal tooth. `mutantAppLetEIdRefuse` is the
    forward identity-first tooth. -/
def mutantAppLetERevRefuse {α : Type} : Option α := none

theorem pinAppRevMutant
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    mutantAppLetERevRefuse ≠
      evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppWideD pinAppIdD := by
  intro h
  rw [pinAppRevDiaEq X hX su] at h
  exact Option.noConfusion h

/-! ### general app/app and letE/letE (audit 03:25Z)
Both inputs move, neither is the identity, and the targets differ. The
function (resp. the let binder and value) stays; the argument (resp. the
body) is two different `ofSorts` from one source. Component diamonds stay
on the right. The app arm consumes `X` on the Π chain. `mutantAppLetEGenRefuse`
is the constant `none` on that pair. -/

def pinAppGenImaxTy :
    HasTyT emptyEnv 0 [] (.sort (.imax .zero .zero)) DTilePins.pinAppDom :=
  .conv [] (.sort (.imax .zero .zero))
    (.sort (.succ (.imax .zero .zero))) DTilePins.pinAppDom
    (.succ (.succ (.imax .zero .zero)))
    (.sort [] (.imax .zero .zero))
    (.sorts [] (.succ (.imax .zero .zero)) (.succ (.max .zero .zero)) (fun _ => rfl))

def pinAppGenImaxAppTy :
    HasTyT emptyEnv 0 []
      (.app DTilePins.pinAppFun (.sort (.imax .zero .zero))) DTilePins.pinAppCod :=
  .app [] DTilePins.pinAppFun (.sort (.imax .zero .zero))
    DTilePins.pinAppDom DTilePins.pinAppCod
    (DTilePins.pinAppFunTy [])
    pinAppGenImaxTy

def pinAppGenRoots : List (Jd emptyEnv 0) :=
  [.ty (DTilePins.pinAppFunTy []), .ty (DTilePins.pinAppPiTy []),
   .ty (DTilePins.pinAppResTy []), .ty pinAppGenImaxAppTy]

def pinAppGenP1 :
    AppPayload pinAppGenRoots []
      DTilePins.pinAppFun (.sort (.max .zero .zero))
      DTilePins.pinAppFun (.sort .zero) DTilePins.pinAppCod where
  T₀ := .pi DTilePins.pinAppDom DTilePins.pinAppCod
  A := DTilePins.pinAppDom
  B := DTilePins.pinAppCod
  u := .succ (.succ (.max .zero .zero))
  v := .succ (.succ .zero)
  w := .succ (.succ .zero)
  hf := .ofTy (.lit (DTilePins.pinAppFunTy []) ⟨_, List.Mem.head _, .inl rfl⟩)
  hc := .refl [] (.pi DTilePins.pinAppDom DTilePins.pinAppCod)
  hPi := .lit (DTilePins.pinAppPiTy [])
    ⟨_, List.Mem.tail _ (List.Mem.head _), .inl rfl⟩
  hB := .sort (.succ .zero)
  hTy := .sort (.succ .zero)
  ha := .ofSorts [] (.max .zero .zero) .zero (fun _ => rfl)
  hr := .lit (DTilePins.pinAppResTy [])
    ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), .inl rfl⟩
  idx := .refl [] DTilePins.pinAppCod

def pinAppGenP2 :
    AppPayload pinAppGenRoots []
      DTilePins.pinAppFun (.sort (.max .zero .zero))
      DTilePins.pinAppFun (.sort (.imax .zero .zero)) DTilePins.pinAppCod where
  T₀ := .pi DTilePins.pinAppDom DTilePins.pinAppCod
  A := DTilePins.pinAppDom
  B := DTilePins.pinAppCod
  u := .succ (.succ (.max .zero .zero))
  v := .succ (.succ .zero)
  w := .succ (.succ .zero)
  hf := .ofTy (.lit (DTilePins.pinAppFunTy []) ⟨_, List.Mem.head _, .inl rfl⟩)
  hc := .refl [] (.pi DTilePins.pinAppDom DTilePins.pinAppCod)
  hPi := .lit (DTilePins.pinAppPiTy [])
    ⟨_, List.Mem.tail _ (List.Mem.head _), .inl rfl⟩
  hB := .sort (.succ .zero)
  hTy := .sort (.succ .zero)
  ha := .ofSorts [] (.max .zero .zero) (.imax .zero .zero) (fun _ => rfl)
  hr := .lit pinAppGenImaxAppTy
    ⟨_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))), .inl rfl⟩
  idx := .refl [] DTilePins.pinAppCod

def pinAppGenD1 : EvParX pinAppGenRoots []
    (.app DTilePins.pinAppFun (.sort (.max .zero .zero)))
    (.app DTilePins.pinAppFun (.sort .zero)) DTilePins.pinAppCod :=
  .app pinAppGenP1

def pinAppGenD2 : EvParX pinAppGenRoots []
    (.app DTilePins.pinAppFun (.sort (.max .zero .zero)))
    (.app DTilePins.pinAppFun (.sort (.imax .zero .zero))) DTilePins.pinAppCod :=
  .app pinAppGenP2

private theorem pinAppGenD1_leaves_ne : pinAppGenD1.leaves ≠ [] := by
  have hleaf : .ty (DTilePins.pinAppResTy []) ∈ pinAppGenP1.hr.leaves := by
    unfold pinAppGenP1 EvTy.leaves
    exact List.mem_cons_self _ _
  exact ne_of_mem <| by
    simpa only [pinAppGenD1, EvParX.leaves] using mem_hr_app pinAppGenP1 hleaf

private theorem pinAppGenD2_leaves_ne : pinAppGenD2.leaves ≠ [] := by
  have hleaf : .ty pinAppGenImaxAppTy ∈ pinAppGenP2.hr.leaves := by
    unfold pinAppGenP2 EvTy.leaves
    exact List.mem_cons_self _ _
  exact ne_of_mem <| by
    simpa only [pinAppGenD2, EvParX.leaves] using mem_hr_app pinAppGenP2 hleaf

private theorem pinAppGenStayEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParAppStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppGenP1 pinAppGenP2 =
      evParAppGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppGenP1 pinAppGenP2 := by
  unfold evParAppStayJoinX
  rfl

set_option maxHeartbeats 1000000 in
private theorem pinAppGenSome
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    (evParAppGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
      pinAppGenP1 pinAppGenP2).isSome = true := by
  unfold evParAppGenJoinX
  rfl

set_option maxHeartbeats 1000000 in
private theorem pinAppGenTarget
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    (evParAppGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
      pinAppGenP1 pinAppGenP2).map (fun j => j.d) =
      some (.app DTilePins.pinAppFun (.sort (.imax .zero .zero))) := by
  unfold evParAppGenJoinX
  rfl

private theorem pinAppGenDiaEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppGenD1 pinAppGenD2 =
      evParAppGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppGenP1 pinAppGenP2 := by
  unfold evParDiamondWfX pinAppGenD1
  exact pinAppGenStayEq X hX su

private theorem pinAppGenProcEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    dProcWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppGenD1 pinAppGenD2 =
      evParAppGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppGenP1 pinAppGenP2 := by
  unfold dProcWfX
  exact pinAppGenDiaEq X hX su

theorem pinAppGen
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    Expr.app DTilePins.pinAppFun (.sort (.max .zero .zero)) ≠
        Expr.app DTilePins.pinAppFun (.sort .zero) ∧
      Expr.app DTilePins.pinAppFun (.sort (.max .zero .zero)) ≠
        Expr.app DTilePins.pinAppFun (.sort (.imax .zero .zero)) ∧
      Expr.app DTilePins.pinAppFun (.sort .zero) ≠
        Expr.app DTilePins.pinAppFun (.sort (.imax .zero .zero)) ∧
      evParAppStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
          pinAppGenP1 pinAppGenP2 =
        evParAppGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
          pinAppGenP1 pinAppGenP2 ∧
      evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
          pinAppGenD1 pinAppGenD2 =
        evParAppGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
          pinAppGenP1 pinAppGenP2 ∧
      dProcWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
          pinAppGenD1 pinAppGenD2 =
        evParAppGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
          pinAppGenP1 pinAppGenP2 ∧
      (evParAppGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppGenP1 pinAppGenP2).isSome = true ∧
      (evParAppGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppGenP1 pinAppGenP2).map (fun j => j.d) =
        some (.app DTilePins.pinAppFun (.sort (.imax .zero .zero))) ∧
      pinAppGenD1.leaves ≠ [] ∧
      pinAppGenD2.leaves ≠ [] := by
  exact ⟨by decide, by decide, by decide, pinAppGenStayEq X hX su,
    pinAppGenDiaEq X hX su, pinAppGenProcEq X hX su, pinAppGenSome X hX su,
    pinAppGenTarget X hX su, pinAppGenD1_leaves_ne, pinAppGenD2_leaves_ne⟩

def pinLetEGenCtx : LCtx :=
  [.letBinding DTilePins.pinAppDom (.sort .zero)]

def pinLetEGenZeroTy :
    HasTyT emptyEnv 0 [] (.sort .zero) DTilePins.pinAppDom :=
  .conv [] (.sort .zero) (.sort (.succ .zero)) DTilePins.pinAppDom
    (.succ (.succ .zero))
    (.sort [] .zero)
    (.sorts [] (.succ .zero) (.succ (.max .zero .zero)) (fun _ => rfl))

def pinLetEGenMidTy :
    HasTyT emptyEnv 0 []
      (.letE DTilePins.pinAppDom (.sort .zero) (.sort .zero)) DTilePins.pinAppDom :=
  .letE [] DTilePins.pinAppDom (.succ (.succ (.max .zero .zero)))
    (.sort .zero) DTilePins.pinAppDom (.sort .zero)
    (.sort [] (.succ (.max .zero .zero)))
    pinLetEGenZeroTy
    (.conv pinLetEGenCtx (.sort .zero) (.sort (.succ .zero)) DTilePins.pinAppDom
      (.succ (.succ .zero))
      (.sort pinLetEGenCtx .zero)
      (.sorts pinLetEGenCtx (.succ .zero) (.succ (.max .zero .zero)) (fun _ => rfl)))

def pinLetEGenImaxTy :
    HasTyT emptyEnv 0 []
      (.letE DTilePins.pinAppDom (.sort .zero) (.sort (.imax .zero .zero)))
      DTilePins.pinAppDom :=
  .letE [] DTilePins.pinAppDom (.succ (.succ (.max .zero .zero)))
    (.sort .zero) DTilePins.pinAppDom (.sort (.imax .zero .zero))
    (.sort [] (.succ (.max .zero .zero)))
    pinLetEGenZeroTy
    (.conv pinLetEGenCtx (.sort (.imax .zero .zero))
      (.sort (.succ (.imax .zero .zero))) DTilePins.pinAppDom
      (.succ (.succ (.imax .zero .zero)))
      (.sort pinLetEGenCtx (.imax .zero .zero))
      (.sorts pinLetEGenCtx (.succ (.imax .zero .zero))
        (.succ (.max .zero .zero)) (fun _ => rfl)))

def pinLetEGenRoots : List (Jd emptyEnv 0) :=
  [.ty pinLetEGenMidTy, .ty pinLetEGenImaxTy]

def pinLetEGenP1 :
    LetEPayload pinLetEGenRoots []
      DTilePins.pinAppDom (.sort .zero) (.sort (.max .zero .zero))
      DTilePins.pinAppDom (.sort .zero) (.sort .zero) DTilePins.pinAppDom where
  B := DTilePins.pinAppDom
  u := .succ (.succ (.max .zero .zero))
  w := .succ (.succ (.max .zero .zero))
  hc := .refl (.sort (.succ (.max .zero .zero)))
  hA := .sort (.succ (.max .zero .zero))
  hv := .ofTy (.rety (.sort .zero)
    (sortsTc (.succ .zero) (.succ (.max .zero .zero)) (fun _ => rfl)))
  hB := .sort (.succ (.max .zero .zero))
  hTy := .sort (.succ (.max .zero .zero))
  hb := .ofSorts pinLetEGenCtx (.max .zero .zero) .zero (fun _ => rfl)
  hrt := .lit pinLetEGenMidTy ⟨_, List.Mem.head _, .inl rfl⟩
  idx := .refl [] DTilePins.pinAppDom

def pinLetEGenP2 :
    LetEPayload pinLetEGenRoots []
      DTilePins.pinAppDom (.sort .zero) (.sort (.max .zero .zero))
      DTilePins.pinAppDom (.sort .zero) (.sort (.imax .zero .zero))
      DTilePins.pinAppDom where
  B := DTilePins.pinAppDom
  u := .succ (.succ (.max .zero .zero))
  w := .succ (.succ (.max .zero .zero))
  hc := .refl (.sort (.succ (.max .zero .zero)))
  hA := .sort (.succ (.max .zero .zero))
  hv := .ofTy (.rety (.sort .zero)
    (sortsTc (.succ .zero) (.succ (.max .zero .zero)) (fun _ => rfl)))
  hB := .sort (.succ (.max .zero .zero))
  hTy := .sort (.succ (.max .zero .zero))
  hb := .ofSorts pinLetEGenCtx (.max .zero .zero) (.imax .zero .zero) (fun _ => rfl)
  hrt := .lit pinLetEGenImaxTy ⟨_, List.Mem.tail _ (List.Mem.head _), .inl rfl⟩
  idx := .refl [] DTilePins.pinAppDom

def pinLetEGenD1 : EvParX pinLetEGenRoots []
    (.letE DTilePins.pinAppDom (.sort .zero) (.sort (.max .zero .zero)))
    (.letE DTilePins.pinAppDom (.sort .zero) (.sort .zero)) DTilePins.pinAppDom :=
  .letE pinLetEGenP1

def pinLetEGenD2 : EvParX pinLetEGenRoots []
    (.letE DTilePins.pinAppDom (.sort .zero) (.sort (.max .zero .zero)))
    (.letE DTilePins.pinAppDom (.sort .zero) (.sort (.imax .zero .zero)))
    DTilePins.pinAppDom :=
  .letE pinLetEGenP2

private theorem pinLetEGenD1_leaves_ne : pinLetEGenD1.leaves ≠ [] := by
  have hleaf : .ty pinLetEGenMidTy ∈ pinLetEGenP1.hrt.leaves := by
    unfold pinLetEGenP1 EvTy.leaves
    exact List.mem_cons_self _ _
  exact ne_of_mem <| by
    simpa only [pinLetEGenD1, EvParX.leaves] using mem_hrt_letE pinLetEGenP1 hleaf

private theorem pinLetEGenD2_leaves_ne : pinLetEGenD2.leaves ≠ [] := by
  have hleaf : .ty pinLetEGenImaxTy ∈ pinLetEGenP2.hrt.leaves := by
    unfold pinLetEGenP2 EvTy.leaves
    exact List.mem_cons_self _ _
  exact ne_of_mem <| by
    simpa only [pinLetEGenD2, EvParX.leaves] using mem_hrt_letE pinLetEGenP2 hleaf

private theorem pinLetEGenStayEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParLetEStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEGenP1 pinLetEGenP2 =
      evParLetEGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEGenP1 pinLetEGenP2 := by
  unfold evParLetEStayJoinX
  rfl

set_option maxHeartbeats 1000000 in
private theorem pinLetEGenSome
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    (evParLetEGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
      pinLetEGenP1 pinLetEGenP2).isSome = true := by
  unfold evParLetEGenJoinX
  rfl

set_option maxHeartbeats 1000000 in
private theorem pinLetEGenTarget
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    (evParLetEGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
      pinLetEGenP1 pinLetEGenP2).map (fun j => j.d) =
      some (.letE DTilePins.pinAppDom (.sort .zero)
        (.sort (.imax .zero .zero))) := by
  unfold evParLetEGenJoinX
  rfl

private theorem pinLetEGenDiaEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEGenD1 pinLetEGenD2 =
      evParLetEGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEGenP1 pinLetEGenP2 := by
  unfold evParDiamondWfX pinLetEGenD1
  exact pinLetEGenStayEq X hX su

private theorem pinLetEGenProcEq
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    dProcWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEGenD1 pinLetEGenD2 =
      evParLetEGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEGenP1 pinLetEGenP2 := by
  unfold dProcWfX
  exact pinLetEGenDiaEq X hX su

theorem pinLetEGen
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    Expr.letE DTilePins.pinAppDom (.sort .zero) (.sort (.max .zero .zero)) ≠
        Expr.letE DTilePins.pinAppDom (.sort .zero) (.sort .zero) ∧
      Expr.letE DTilePins.pinAppDom (.sort .zero) (.sort (.max .zero .zero)) ≠
        Expr.letE DTilePins.pinAppDom (.sort .zero) (.sort (.imax .zero .zero)) ∧
      Expr.letE DTilePins.pinAppDom (.sort .zero) (.sort .zero) ≠
        Expr.letE DTilePins.pinAppDom (.sort .zero) (.sort (.imax .zero .zero)) ∧
      evParLetEStayJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
          pinLetEGenP1 pinLetEGenP2 =
        evParLetEGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
          pinLetEGenP1 pinLetEGenP2 ∧
      evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
          pinLetEGenD1 pinLetEGenD2 =
        evParLetEGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
          pinLetEGenP1 pinLetEGenP2 ∧
      dProcWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
          pinLetEGenD1 pinLetEGenD2 =
        evParLetEGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
          pinLetEGenP1 pinLetEGenP2 ∧
      (evParLetEGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEGenP1 pinLetEGenP2).isSome = true ∧
      (evParLetEGenJoinX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEGenP1 pinLetEGenP2).map (fun j => j.d) =
        some (.letE DTilePins.pinAppDom (.sort .zero)
          (.sort (.imax .zero .zero))) ∧
      pinLetEGenD1.leaves ≠ [] ∧
      pinLetEGenD2.leaves ≠ [] := by
  exact ⟨by decide, by decide, by decide, pinLetEGenStayEq X hX su,
    pinLetEGenDiaEq X hX su, pinLetEGenProcEq X hX su, pinLetEGenSome X hX su,
    pinLetEGenTarget X hX su, pinLetEGenD1_leaves_ne, pinLetEGenD2_leaves_ne⟩

/-- Constant `none` on the general moving app and letE pair. The diagonal,
    identity-first, and reverse-identity mutants are different teeth. -/
def mutantAppLetEGenRefuse {α : Type} : Option α := none

theorem pinAppGenMutant
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    mutantAppLetEGenRefuse ≠
      evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinAppGenD1 pinAppGenD2 := by
  intro h
  rw [pinAppGenDiaEq X hX su] at h
  have hs := pinAppGenSome X hX su
  rw [← h] at hs
  simp [mutantAppLetEGenRefuse] at hs

theorem pinLetEGenMutant
    (X : ∀ R : List (Jd emptyEnv 0), XProc R) (hX : XContract X)
    (su : F8A2Support.SortUnique emptyEnv 0) :
    mutantAppLetEGenRefuse ≠
      evParDiamondWfX (E := emptyEnv) (n := 0) EnvWfT.empty su X hX CtxWfT.nil
        pinLetEGenD1 pinLetEGenD2 := by
  intro h
  rw [pinLetEGenDiaEq X hX su] at h
  have hs := pinLetEGenSome X hX su
  rw [← h] at hs
  simp [mutantAppLetEGenRefuse] at hs

/-- consts×delta, delta×consts, and the lam limits stay the named `none`. -/
theorem namedRefusalsStillNone :
    (evParXConstsDelta : Option Unit) = none ∧
    (evParXDeltaConsts : Option Unit) = none ∧
    (evParXLamIndex : Option Unit) = none ∧
    (evParXLamBothMove : Option Unit) = none ∧
    (evParXAppApart : Option Unit) = none ∧
    (evParXLetEApart : Option Unit) = none ∧
    (evParXAppT0 : Option Unit) = none ∧
    (evParXAppInst : Option Unit) = none ∧
    (evParXAppCentre : Option Unit) = none ∧
    (evParXLetECentre : Option Unit) = none ∧
    (evParXLetENoSrc : Option Unit) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### stored ζ (cc 11:41Z)

The dropped typing is the `CtxWfT` field at `Γ.drop (i + 1)`, not a premise
the caller presents and not an `EvTy.lit`. The J2 packet stays the original
literal budget. `StoredCtxOrigin` records the context read beside that packet. -/

structure StoredLetTyping (hΓ : CtxWfT E n Γ) (i : Nat) (A₀ v₀ : Expr Nat)
    (entry : Γ.get? i = some (.letBinding A₀ v₀)) where
  hvt : HasTyT E n (Γ.drop (i + 1)) v₀ A₀
  hvt_exact : hvt = ctxWfTLookupValueAtDrop hΓ i entry

/-- Built by the lookup. `hvt` is not a parameter. -/
def StoredLetTyping.read (hΓ : CtxWfT E n Γ) (i : Nat) {A₀ v₀ : Expr Nat}
    (entry : Γ.get? i = some (.letBinding A₀ v₀)) :
    StoredLetTyping hΓ i A₀ v₀ entry where
  hvt := ctxWfTLookupValueAtDrop hΓ i entry
  hvt_exact := rfl

theorem StoredLetTyping.read_exact (hΓ : CtxWfT E n Γ) (i : Nat) {A₀ v₀ : Expr Nat}
    (entry : Γ.get? i = some (.letBinding A₀ v₀)) :
    (StoredLetTyping.read hΓ i entry).hvt = ctxWfTLookupValueAtDrop hΓ i entry :=
  rfl

/-- Context provenance. Not an `EvTy`: there is no literal `SubEq` certificate. -/
structure StoredCtxOrigin (hΓ : CtxWfT E n Γ) (i : Nat) (A₀ v₀ : Expr Nat)
    (entry : Γ.get? i = some (.letBinding A₀ v₀)) where
  typing : StoredLetTyping hΓ i A₀ v₀ entry

def StoredCtxOrigin.ofTyping {hΓ : CtxWfT E n Γ} {i : Nat} {A₀ v₀ : Expr Nat}
    {entry : Γ.get? i = some (.letBinding A₀ v₀)}
    (t : StoredLetTyping hΓ i A₀ v₀ entry) : StoredCtxOrigin hΓ i A₀ v₀ entry where
  typing := t

theorem StoredCtxOrigin.hvt_is_lookup {hΓ : CtxWfT E n Γ} {i : Nat}
    {A₀ v₀ : Expr Nat} {entry : Γ.get? i = some (.letBinding A₀ v₀)}
    (o : StoredCtxOrigin hΓ i A₀ v₀ entry) :
    o.typing.hvt = ctxWfTLookupValueAtDrop hΓ i entry :=
  o.typing.hvt_exact

structure StoredZeta (R : List (Jd E n)) (hΓ : CtxWfT E n Γ) (i : Nat)
    (A v : Expr Nat) (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A)
    (hs : ∃ r ∈ R, SubEq (.cv (.zetaLocal Γ i A v hval hty hv)) r) where
  storedType : Expr Nat
  storedValue : Expr Nat
  entry : Γ.get? i = some (.letBinding storedType storedValue)
  origin : StoredCtxOrigin hΓ i storedType storedValue entry
  packet : JEndpoints.Packet R (.zetaLocal Γ i A v hval hty hv)
  step : ParRedT (PEqLeafT E n) E n Γ (.bvar i) (lift 0 (i + 1) storedValue) A

/-- The constructed entry. The child step is `ParRedT.refl` on the lookup
    field; both endpoints are the existing J2 packet's original typings. -/
def storedZeta (hΓ : CtxWfT E n Γ) (i : Nat) (A v : Expr Nat)
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A)
    (hs : ∃ r ∈ R, SubEq (.cv (.zetaLocal Γ i A v hval hty hv)) r) :
    StoredZeta R hΓ i A v hval hty hv hs :=
  let found := get?_of_lookupValue hval
  let A₀ := found.1
  let v₀ := found.2.1
  let entry := found.2.2.1
  let valueEq := found.2.2.2
  let typing := StoredLetTyping.read hΓ i entry
  let packet := JEndpoints.zetaLocalPacket i A v hval hty hv hs
  { storedType := A₀
    storedValue := v₀
    entry := entry
    origin := { typing := typing }
    packet := packet
    step := .bvarZeta Γ i A₀ v₀ v₀ A entry
      (.refl (Γ.drop (i + 1)) v₀ A₀ typing.hvt)
      (.bvar Γ i A hty)
      (Eq.mp (congrArg (fun w => HasTyT E n Γ w A) valueEq) hv) }

theorem storedZeta_hvt_exact (hΓ : CtxWfT E n Γ) (i : Nat) (A v : Expr Nat)
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A)
    (hs : ∃ r ∈ R, SubEq (.cv (.zetaLocal Γ i A v hval hty hv)) r) :
    (storedZeta hΓ i A v hval hty hv hs).origin.typing.hvt =
      ctxWfTLookupValueAtDrop hΓ i (storedZeta hΓ i A v hval hty hv hs).entry :=
  (storedZeta hΓ i A v hval hty hv hs).origin.typing.hvt_exact

theorem storedZeta_packet (hΓ : CtxWfT E n Γ) (i : Nat) (A v : Expr Nat)
    (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : HasTyT E n Γ v A)
    (hs : ∃ r ∈ R, SubEq (.cv (.zetaLocal Γ i A v hval hty hv)) r) :
    (storedZeta hΓ i A v hval hty hv hs).packet =
      JEndpoints.zetaLocalPacket i A v hval hty hv hs :=
  rfl

/-- A witness list is inside the original-literal budget only when every
    member is a strict child of the original conversion. -/
def originalLeafBudget {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) (L : List (Jd E n)) : Prop :=
  ∀ ℓ ∈ L, SubOf ℓ (.cv h)

/-- The mutant drops the `SubOf` test and accepts every member. -/
def mutantLeafBudget {Γ : LCtx} {a b T : Expr Nat}
    (_h : ConvT E n Γ a b T) (L : List (Jd E n)) : Prop :=
  ∀ _ℓ ∈ L, True

def droppedWitness (hvt : HasTyT E n Δ w B) (L : List (Jd E n)) : List (Jd E n) :=
  .ty hvt :: L

theorem stored_leaf_rejects_dropped {Γ : LCtx} {a b T : Expr Nat}
    {Δ : LCtx} {w B : Expr Nat} (h : ConvT E n Γ a b T)
    (hvt : HasTyT E n Δ w B) (hnot : ¬ SubOf (.ty hvt) (.cv h))
    (L : List (Jd E n)) :
    ¬ originalLeafBudget h (droppedWitness hvt L) :=
  fun hc => hnot (hc (.ty hvt) (List.mem_cons.mpr (.inl rfl)))

theorem mutant_accepts_dropped_hvt {Γ : LCtx} {a b T : Expr Nat}
    {Δ : LCtx} {w B : Expr Nat} (h : ConvT E n Γ a b T)
    (hvt : HasTyT E n Δ w B) (L : List (Jd E n)) :
    mutantLeafBudget h (droppedWitness hvt L) :=
  fun _ _ => trivial

/-! Concrete tooth. `Γ = [let _ : Sort 1 := Sort 0]`. The stored typing is
`HasTyT.sort [] 0`; the original literal's only typing child is
`HasTyT.sort Γ 0`. They are not the same leaf. -/

def pinSort0 : Expr Nat := .sort .zero
def pinSort1 : Expr Nat := .sort (.succ .zero)
def pinΓ : LCtx := [.letBinding pinSort1 pinSort0]

def pinHvt : HasTyT E n [] pinSort0 pinSort1 := .sort [] .zero

def pinHA : HasTyT E n [] pinSort1 (.sort (.succ (.succ .zero))) :=
  .sort [] (.succ .zero)

def pinHΓ : CtxWfT E n pinΓ :=
  .letBinding [] pinSort1 (.succ (.succ .zero)) pinSort0 .nil pinHA pinHvt

def pinHv : HasTyT E n pinΓ pinSort0 pinSort1 := .sort pinΓ .zero

def pinHval : lookupValue pinΓ 0 = some pinSort0 := rfl
def pinHty : lookupType pinΓ 0 = some pinSort1 := rfl

def pinConv : ConvT E n pinΓ (.bvar 0) pinSort0 pinSort1 :=
  .zetaLocal pinΓ 0 pinSort1 pinSort0 pinHval pinHty pinHv

def pinRoots : List (Jd E n) := [.cv pinConv]

def pinHs : ∃ (r : Jd E n), r ∈ pinRoots ∧ SubEq (Jd.cv pinConv) r :=
  ⟨Jd.cv pinConv, List.mem_singleton.mpr rfl, .inl rfl⟩

def pinEntry : pinΓ.get? 0 = some (.letBinding pinSort1 pinSort0) := rfl

def pinTyping : StoredLetTyping (E := E) (n := n) pinHΓ 0 pinSort1 pinSort0 pinEntry :=
  StoredLetTyping.read pinHΓ 0 pinEntry

def pinZeta : StoredZeta (E := E) (n := n) pinRoots pinHΓ 0 pinSort1 pinSort0 pinHval pinHty pinHv pinHs :=
  storedZeta pinHΓ 0 pinSort1 pinSort0 pinHval pinHty pinHv pinHs

/-- The lookup at this one-binder context is the field the context was built with. -/
theorem pin_lookup_eq :
    ctxWfTLookupValueAtDrop (E := E) (n := n) pinHΓ 0 pinEntry = pinHvt :=
  rfl

/-- Discriminate the empty-context sort from the same sort under `pinΓ`. -/
def hasTySortCtxLen {Γ : LCtx} {e T : Expr Nat} : HasTyT E n Γ e T → Nat
  | .sort Γ _ => Γ.length
  | .bvar _ _ _ _ => 0
  | .const _ _ _ _ _ _ _ => 0
  | .pi _ _ _ _ _ _ _ => 0
  | .lam _ _ _ _ _ _ _ => 0
  | .app _ _ _ _ _ _ _ => 0
  | .letE _ _ _ _ _ _ _ _ _ => 0
  | .lit _ _ _ _ => 0
  | .conv _ _ _ _ _ _ _ => 0

def jdTySortLen : Jd E n → Nat
  | .ty d => hasTySortCtxLen d
  | .cv _ => 0
  | .tc _ => 0
  | .pr _ => 0
  | .pe _ => 0

theorem pin_ty_ne (h : Jd.ty (E := E) (n := n) pinHvt = Jd.ty (E := E) (n := n) pinHv) : False := by
  have hlen := congrArg jdTySortLen h
  simp only [jdTySortLen, hasTySortCtxLen, pinHvt, pinHv, pinΓ, pinSort0, pinSort1,
    List.length_cons, List.length_nil, Nat.zero_add] at hlen
  cases hlen

theorem pin_hv_no_sub {x : Jd E n} (h : SubOf x (.ty pinHv)) : False :=
  SubOf.rec (motive := fun _ y _ => y = .ty pinHv → False)
    (fun hc heq => by
      cases heq
      simp only [Child, Jd.children, Jd.tyChildren, pinHv] at hc
      cases hc)
    (fun _ _ _ ihyz heq => ihyz heq)
    h rfl

theorem pin_sub_eq_hv {x : Jd E n} (h : SubOf x (.cv pinConv)) : x = .ty pinHv :=
  SubOf.rec (motive := fun a b _ => b = .cv pinConv → a = .ty pinHv)
    (fun hc heq => by
      cases heq
      simp only [Child, Jd.children, Jd.cvChildren, pinConv, List.mem_singleton] at hc
      exact hc)
    (fun hxy _ _ ihyz heq => by
      have hy := ihyz heq
      subst hy
      exact False.elim (pin_hv_no_sub hxy))
    h rfl

theorem pin_dropped_not_sub :
    ¬ SubOf (Jd.ty (E := E) (n := n) (pinTyping (E := E) (n := n)).hvt)
        (Jd.cv (E := E) (n := n) (pinConv (E := E) (n := n))) := by
  intro h
  have hx := pin_sub_eq_hv h
  have he := (pinTyping (E := E) (n := n)).hvt_exact.trans pin_lookup_eq
  rw [he] at hx
  exact pin_ty_ne hx

/-- The same witness: packet leaves plus the dropped typing. The tooth rejects it. -/
theorem pin_tooth :
    ¬ originalLeafBudget (E := E) (n := n) (pinConv (E := E) (n := n))
        (droppedWitness (E := E) (n := n)
          (pinTyping (E := E) (n := n)).hvt
          (pinZeta (E := E) (n := n)).packet.leaves) :=
  stored_leaf_rejects_dropped (pinConv (E := E) (n := n))
    (pinTyping (E := E) (n := n)).hvt pin_dropped_not_sub _

/-- The mutant accepts that witness. -/
theorem pin_mutant :
    mutantLeafBudget (E := E) (n := n) (pinConv (E := E) (n := n))
      (droppedWitness (E := E) (n := n)
        (pinTyping (E := E) (n := n)).hvt
        (pinZeta (E := E) (n := n)).packet.leaves) :=
  mutant_accepts_dropped_hvt (pinConv (E := E) (n := n))
    (pinTyping (E := E) (n := n)).hvt _

theorem pin_origin_outside_budget :
    Jd.ty (E := E) (n := n) (pinZeta (E := E) (n := n)).origin.typing.hvt ∉
      (pinZeta (E := E) (n := n)).packet.leaves := by
  have hleaves : (pinZeta (E := E) (n := n)).packet.leaves =
      [Jd.ty (E := E) (n := n) pinHv] := by
    rw [show (pinZeta (E := E) (n := n)).packet =
        JEndpoints.zetaLocalPacket (E := E) (n := n) 0 pinSort1 pinSort0
          pinHval pinHty pinHv pinHs
      from storedZeta_packet (E := E) (n := n) pinHΓ 0 pinSort1 pinSort0
        pinHval pinHty pinHv pinHs]
    exact JEndpoints.zetaLocalPacket_leaves (E := E) (n := n) 0 pinSort1 pinSort0
      pinHval pinHty pinHv pinHs
  rw [hleaves]
  intro hin
  have he := List.mem_singleton.mp hin
  have hvt := (pinZeta (E := E) (n := n)).origin.typing.hvt_exact.trans
    (by
      simpa only [pinZeta, storedZeta, StoredLetTyping.read] using pin_lookup_eq)
  rw [hvt] at he
  exact pin_ty_ne he

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.BVarZetaPayload.substLetVal
#print axioms Rcic.Declarative.F8Measure.coversIdx_of_delta
#print axioms Rcic.Declarative.F8Measure.mutant_accepts_dropped_idx
#print axioms Rcic.Declarative.F8Measure.coversIdx_rejects_dropped
#print axioms Rcic.Declarative.F8Measure.evParLamStayJoinX
#print axioms Rcic.Declarative.F8Measure.evParXDiagStay
#print axioms Rcic.Declarative.F8Measure.evParAppDiagJoin
#print axioms Rcic.Declarative.F8Measure.evParLetEDiagJoin
#print axioms Rcic.Declarative.F8Measure.evParAppStayJoinX
#print axioms Rcic.Declarative.F8Measure.evParLetEStayJoinX
#print axioms Rcic.Declarative.F8Measure.evParDiamondWfX
#print axioms Rcic.Declarative.F8Measure.dProcWfX
#print axioms Rcic.Declarative.F8Measure.pinAppDiag
#print axioms Rcic.Declarative.F8Measure.pinLetEDiag
#print axioms Rcic.Declarative.F8Measure.pinAppMutant
#print axioms Rcic.Declarative.F8Measure.mutantAppLetERefuse
#print axioms Rcic.Declarative.F8Measure.evParAppIdReplay
#print axioms Rcic.Declarative.F8Measure.evParLetEIdReplay
#print axioms Rcic.Declarative.F8Measure.pinAppUnequal
#print axioms Rcic.Declarative.F8Measure.pinLetEUnequal
#print axioms Rcic.Declarative.F8Measure.mutantAppLetEIdRefuse
#print axioms Rcic.Declarative.F8Measure.pinAppUnequalMutant
#print axioms Rcic.Declarative.F8Measure.evParAppRevReplay
#print axioms Rcic.Declarative.F8Measure.evParLetERevReplay
#print axioms Rcic.Declarative.F8Measure.pinAppRev
#print axioms Rcic.Declarative.F8Measure.pinLetERev
#print axioms Rcic.Declarative.F8Measure.mutantAppLetERevRefuse
#print axioms Rcic.Declarative.F8Measure.pinAppRevMutant
#print axioms Rcic.Declarative.F8Measure.evParAppGenJoinX
#print axioms Rcic.Declarative.F8Measure.evParLetEGenJoinX
#print axioms Rcic.Declarative.F8Measure.pinAppGen
#print axioms Rcic.Declarative.F8Measure.pinLetEGen
#print axioms Rcic.Declarative.F8Measure.mutantAppLetEGenRefuse
#print axioms Rcic.Declarative.F8Measure.pinAppGenMutant
#print axioms Rcic.Declarative.F8Measure.pinLetEGenMutant
#print axioms Rcic.Declarative.F8Measure.namedRefusalsStillNone
#print axioms Rcic.Declarative.F8Measure.evParXAppT0
#print axioms Rcic.Declarative.F8Measure.evParXAppInst
#print axioms Rcic.Declarative.F8Measure.evParXAppCentre
#print axioms Rcic.Declarative.F8Measure.evParXLetECentre
#print axioms Rcic.Declarative.F8Measure.evParXLetENoSrc
#print axioms Rcic.Declarative.F8Measure.EvPar.sourceTy
#print axioms Rcic.Declarative.F8Measure.EvPar.sourceTy_leaves
#print axioms Rcic.Declarative.F8Measure.appCornerJoin
#print axioms Rcic.Declarative.F8Measure.appCornerJoin_fields
#print axioms Rcic.Declarative.F8Measure.appCornerJoin_support
#print axioms Rcic.Declarative.F8Measure.AppOuterLeg.leaves
#print axioms Rcic.Declarative.F8Measure.AppOuterLeg.src
#print axioms Rcic.Declarative.F8Measure.AppOuterLeg.tgt
#print axioms Rcic.Declarative.F8Measure.AppOuterLeg.funRead
#print axioms Rcic.Declarative.F8Measure.AppOuterLeg.argRead
#print axioms Rcic.Declarative.F8Measure.appOuterLeg
#print axioms Rcic.Declarative.F8Measure.appOuterLeg_leaves
#print axioms Rcic.Declarative.F8Measure.appOuterLeg_stay
#print axioms Rcic.Declarative.F8Measure.appOuterLeg_stepFun
#print axioms Rcic.Declarative.F8Measure.appOuterLeg_stepArg
#print axioms Rcic.Declarative.F8Measure.appOuterLeg_stepBoth
#print axioms Rcic.Declarative.F8Measure.appOuterLeg_funRead
#print axioms Rcic.Declarative.F8Measure.appOuterLeg_argRead
#print axioms Rcic.Declarative.F8Measure.appOuterLeg_funTile
#print axioms Rcic.Declarative.F8Measure.appOuterLeg_argTile
#print axioms Rcic.Declarative.F8Measure.appOuterLeg_funStepTile
#print axioms Rcic.Declarative.F8Measure.appOuterLeg_argStepTile
#print axioms Rcic.Declarative.F8Measure.appCornerJoin_outer_support
#print axioms Rcic.Declarative.F8Measure.appCornerJoin_outer_target
#print axioms Rcic.Declarative.F8Measure.appIndexChain
#print axioms Rcic.Declarative.F8Measure.appIndexChain_leaves
#print axioms Rcic.Declarative.F8Measure.appFunRead
#print axioms Rcic.Declarative.F8Measure.appFunRead_leaves
#print axioms Rcic.Declarative.F8Measure.letECornerJoin
#print axioms Rcic.Declarative.F8Measure.letECornerJoin_fields
#print axioms Rcic.Declarative.F8Measure.letECornerJoin_support
#print axioms Rcic.Declarative.F8Measure.storedZeta
#print axioms Rcic.Declarative.F8Measure.storedZeta_hvt_exact
#print axioms Rcic.Declarative.F8Measure.storedZeta_packet
#print axioms Rcic.Declarative.F8Measure.stored_leaf_rejects_dropped
#print axioms Rcic.Declarative.F8Measure.mutant_accepts_dropped_hvt
#print axioms Rcic.Declarative.F8Measure.pin_lookup_eq
#print axioms Rcic.Declarative.F8Measure.pin_dropped_not_sub
#print axioms Rcic.Declarative.F8Measure.pin_tooth
#print axioms Rcic.Declarative.F8Measure.pin_mutant
#print axioms Rcic.Declarative.F8Measure.pin_origin_outside_budget
#check Rcic.Declarative.F8Measure.BVarZetaPayload.substVal
#check Rcic.Declarative.F8Measure.BVarZetaPayload.substLetVal
#check Rcic.Declarative.F8Measure.dProcWf
#check Rcic.Declarative.F8Measure.evParDiamondWf
