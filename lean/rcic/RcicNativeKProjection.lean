import rcic.RcicCoherentCanonical
import rcic.RcicNativeValleyDecoTransfer

/-!
# Native valley projection for relations retaining K and eta-K

The existing `NativeValley` stores unrestricted `ParRedTStar` legs at
the canonical proof leaf. The existing raw star inversion therefore
projects these valleys without passing through the K-free `CStar`.

`NativeConvValleyData` below is an explicit Type-valued producer premise.
The consumer constructs full `PiInj` from that producer, `SortRetype`, and
`ZeroSortCoherence`. The weaker `PiConvValleyData` suffices: only native
conversions between two written Pi terms at a sort need valleys. The
consumer first homogenizes the original `TyConvT` chain
as one native `ConvT`, then projects the producer's actual valley.

The proposition `NativeConvValleys` only gives `Nonempty` valleys. Its
separate consumer returns the proposition-valued Pi row, without choosing
data from `Nonempty`. Neither producer is constructed here. No confluence,
diamond, type uniqueness, Pi row, or retyping theorem is assumed silently.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.NativeKProjectionAudit

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Project two actual unrestricted stars to component conversion data.
The legs may have different sorting indices; the shared centre is what
identifies the two projected Pi heads. -/
def rawStars_pi_inv_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ B₁ A₂ B₂ c T₁ T₂ : Expr Nat}
    (left : ParRedTStar PEq E n Γ (.pi A₁ B₁) c T₁)
    (right : ParRedTStar PEq E n Γ (.pi A₂ B₂) c T₂) :
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂ := by
  obtain ⟨A_c, B_c, h₁, hcA₁, hcB₁⟩ :=
    parRedTStar_pi_inv_of_zsc hW L zsc hΓ left rfl
  obtain ⟨A_c', B_c', h₂, hcA₂, hcB₂⟩ :=
    parRedTStar_pi_inv_of_zsc hW L zsc hΓ right rfl
  have heq : Expr.pi A_c B_c = Expr.pi A_c' B_c' := h₁.symm.trans h₂
  injection heq with hAeq hBeq
  subst hAeq
  subst hBeq
  let hcA : TyConvT E n Γ A₁ A₂ := .trans Γ A₁ A_c A₂ hcA₁ hcA₂.symmT
  exact (hcA, .trans (.assumption A₁ :: Γ) B₁ B_c B₂ hcB₁
    (tyConvT_assump_dom hW hΓ hcA hcB₂.symmT))

/-- The same raw projection gives sort coherence for two stars meeting at
one centre, independently of their sorting indices. -/
theorem rawStars_sort_inv_of_zsc (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {u₁ u₂ : Level} {c T₁ T₂ : Expr Nat}
    (left : ParRedTStar PEq E n Γ (.sort u₁) c T₁)
    (right : ParRedTStar PEq E n Γ (.sort u₂) c T₂) : eqN u₁ u₂ := by
  obtain ⟨u_c, h₁, hu₁⟩ := parRedTStar_sort_inv_of_zsc hW L zsc hΓ left rfl
  obtain ⟨u_c', h₂, hu₂⟩ := parRedTStar_sort_inv_of_zsc hW L zsc hΓ right rfl
  have heq : Expr.sort u_c = Expr.sort u_c' := h₁.symm.trans h₂
  injection heq with hueq
  subst hueq
  exact eqN_trans hu₁ (eqN_symm hu₂)

/-- Project the existing native valley, whose legs permit both K nodes. -/
def nativeValley_pi_inv_of_zsc (hW : EnvWfT E)
    (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ B₁ A₂ B₂ T : Expr Nat}
    (V : NativeValley E n Γ (.pi A₁ B₁) (.pi A₂ B₂) T) :
    TyConvT E n Γ A₁ A₂ × TyConvT E n (.assumption A₁ :: Γ) B₁ B₂ :=
  rawStars_pi_inv_of_zsc hW (CoherentCanonicalAudit.nativeLeafIface E n)
    zsc hΓ V.left V.right

/-- Sort coherence projected from an existing native valley. -/
theorem nativeValley_sort_inv_of_zsc (hW : EnvWfT E)
    (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u₁ u₂ : Level} {T : Expr Nat}
    (V : NativeValley E n Γ (.sort u₁) (.sort u₂) T) : eqN u₁ u₂ :=
  rawStars_sort_inv_of_zsc hW (CoherentCanonicalAudit.nativeLeafIface E n)
    zsc hΓ V.left V.right

/-- Homogenize a native type-conversion chain at a supplied source sort.
At each `.of`, `SortRetype` aligns the edge's source sorting with the
retained sorting; `convT_of_tyConv` moves the edge to that index. -/
def convT_of_tyConvT_of_sortRetype (hW : EnvWfT E) (sr : SortRetype E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {X Y : Expr Nat} → {w : Level} → HasTyT E n Γ X (.sort w) →
    TyConvT E n Γ X Y → ConvT E n Γ X Y (.sort w)
  | _, _, _, hX, .refl _ _ => .refl _ _ _ hX
  | _, _, _, hX, .of _ _ _ _ hc =>
      convT_of_tyConv hc (sr hΓ (convEnds hW hΓ hc).1 hX)
  | X, Y, _, hX, .trans _ _ M _ c₁ c₂ =>
      let hc₁ := convT_of_tyConvT_of_sortRetype hW sr hΓ hX c₁
      let hM := (convEnds hW hΓ hc₁).2.1
      let hc₂ := convT_of_tyConvT_of_sortRetype hW sr hΓ hM c₂
      .trans Γ X M Y _ hc₁ hc₂

/-- An actual data-valued producer on the existing raw native carrier.
This premise is stronger in elimination power than `NativeConvValleys`,
whose output is only `Nonempty (NativeValley ...)`. -/
def NativeConvValleyData (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {a b T : Expr Nat},
    ConvT E n Γ a b T → NativeValley E n Γ a b T

/-- The restricted producer interface used by Pi injectivity:
only two written Pi endpoints, at a sorting index. This is an exact
remaining premise, not a construction or an asserted inhabited type. -/
def PiConvValleyData (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ B₁ A₂ B₂ : Expr Nat} {u : Level},
    ConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort u) →
    NativeValley E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort u)

/-- A Type-valued producer can be forgotten into the existing supplier
proposition without choice. -/
theorem nativeConvValleys_of_data (join : NativeConvValleyData E n) :
    NativeConvValleys E n :=
  fun {_} hΓ {_ _ _} c => ⟨join hΓ c⟩

/-- Produce a raw native valley for the full original `TyConvT` chain.
The producer is applied once, after native sorting alignment. -/
def nativeValley_of_tyConvT_of_sortRetype (hW : EnvWfT E)
    (join : NativeConvValleyData E n) (sr : SortRetype E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {X Y : Expr Nat} {w : Level}
    (hX : HasTyT E n Γ X (.sort w)) (c : TyConvT E n Γ X Y) :
    NativeValley E n Γ X Y (.sort w) :=
  join hΓ (convT_of_tyConvT_of_sortRetype hW sr hΓ hX c)

/-- The restricted Pi-endpoint producer yields full Type-valued Pi
injectivity. Sorting alignment and zero-sort coherence remain explicit;
no valley for a non-Pi endpoint is requested. -/
def piInj_of_piValleyData_sortRetype (hW : EnvWfT E)
    (join : PiConvValleyData E n) (sr : SortRetype E n)
    (zsc : HostPropAudit.ZeroSortCoherence E n) : PiInj E n :=
  fun {Γ} hΓ {A₁ B₁ A₂ B₂} c =>
    match tyConvT_firstOf_data c with
    | .inl heq => by
        injection heq with hA hB
        subst hA
        subst hB
        exact (.refl Γ A₁, .refl (.assumption A₁ :: Γ) B₁)
    | .inr ⟨_, _, hc₀, _⟩ =>
        let hPi := (convEnds hW hΓ hc₀).1
        let V := join hΓ (convT_of_tyConvT_of_sortRetype hW sr hΓ hPi c)
        nativeValley_pi_inv_of_zsc hW zsc hΓ V

/-- The unrestricted data supplier specializes to the narrower Pi
consumer. This is conditional and does not construct either supplier. -/
def piInj_of_nativeValleyData_sortRetype (hW : EnvWfT E)
    (join : NativeConvValleyData E n) (sr : SortRetype E n)
    (zsc : HostPropAudit.ZeroSortCoherence E n) : PiInj E n :=
  piInj_of_piValleyData_sortRetype hW
    (fun {_} hΓ {_ _ _ _ _} c => join hΓ c) sr zsc

/-- The same producer gives full sort coherence. -/
theorem sortCoh_of_nativeValleyData_sortRetype (hW : EnvWfT E)
    (join : NativeConvValleyData E n) (sr : SortRetype E n)
    (zsc : HostPropAudit.ZeroSortCoherence E n) : SortCoh E n :=
  fun {Γ} hΓ {u _} c =>
    nativeValley_sort_inv_of_zsc hW zsc hΓ
      (nativeValley_of_tyConvT_of_sortRetype hW join sr hΓ (.sort Γ u) c)

/-- The proposition-only supplier yields the proposition-only Pi row.
The `Nonempty` valley is eliminated solely into this proposition; this
does not construct a value of `PiInj`. -/
theorem piRow_of_nativeConvValleys_sortRetype (hW : EnvWfT E)
    (join : NativeConvValleys E n) (sr : SortRetype E n)
    (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A₁ B₁ A₂ B₂ : Expr Nat}
    (c : TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂)) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧
      Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  cases tyConvT_firstOf_data c with
  | inl heq =>
      injection heq with hA hB
      subst hA
      subst hB
      exact ⟨⟨.refl Γ A₁⟩, ⟨.refl (.assumption A₁ :: Γ) B₁⟩⟩
  | inr first =>
      obtain ⟨_, _, hc₀, _⟩ := first
      let hPi := (convEnds hW hΓ hc₀).1
      obtain ⟨V⟩ := join hΓ (convT_of_tyConvT_of_sortRetype hW sr hΓ hPi c)
      let row := nativeValley_pi_inv_of_zsc hW zsc hΓ V
      exact ⟨⟨row.1⟩, ⟨row.2⟩⟩

#print axioms rawStars_pi_inv_of_zsc
#print axioms rawStars_sort_inv_of_zsc
#print axioms nativeValley_pi_inv_of_zsc
#print axioms nativeValley_sort_inv_of_zsc
#print axioms convT_of_tyConvT_of_sortRetype
#print axioms NativeConvValleyData
#print axioms PiConvValleyData
#print axioms nativeConvValleys_of_data
#print axioms nativeValley_of_tyConvT_of_sortRetype
#print axioms piInj_of_nativeValleyData_sortRetype
#print axioms piInj_of_piValleyData_sortRetype
#print axioms sortCoh_of_nativeValleyData_sortRetype
#print axioms piRow_of_nativeConvValleys_sortRetype

end Rcic.Declarative.NativeValleys.NativeKProjectionAudit
