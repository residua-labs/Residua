import rcic.RcicF8XValley
import rcic.RcicF8JTransport
import rcic.RcicF8JEndpoints
import rcic.RcicF8DTileStep
import rcic.RcicF8JEndpointRefutation
import rcic.RcicEtaKDecide
import rcic.RcicTypedWeaken
import rcic.RcicParRedTSubst
import rcic.RcicDTMetaTypedSR

open Rcic.Syn

/-! # RcicF8CtxWfVia — WK-1a of W-X-WK (#7128 ruling)

`CtxWfVia Γ₀` = `Γ₀` is the preimage of a well-formed context under a
premise-free context morphism of the CLOSED class actually used —
weakenings (`insertAt`) in WK-1; WK-2 adds a typed `subst0`.

`CtxWfVia Γ₀ → CtxWfT Γ₀` would be local-context strengthening (not on
the tree, not claimed): the premise is not a weakening of the theory but
of the obligation on the CALLER (X can build it from the segment
context's `CtxWfT`). Consumers use it only through `eqN` and `False`,
after transporting plain premises to the target.

J1/J2/J3 get `Via` front-end twins beside their landed `JProcWf` fronts
(unchanged); D1's `structPiJoin` is re-proved under `Via` (same data:
`_ofWf` is `rfl`); teeth: `illCtx` has no `Via` witness, and the mutant
that drops the morphism (an arbitrary context map carrying the target's
well-formedness and the map's sort-preservation) wrongly accepts it.

`Wk.ext`/`CtxWfVia.ext` cover `.assumption` binders only (what D1 and
the J fronts use); a `.letBinding` extension is needed by no landed
consumer and is left to WK-2 if one appears.

`closure_claim = 0`. -/

namespace Rcic.Declarative.F8Measure

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### §1 the closed morphism class: weakenings, inside-out -/

/-- a weakening morphism `Γ₀ → Γ'`: `Γ'` is `Γ₀` with declarations
    inserted at cutoffs, inside-out. Closed under composition by
    construction (each `ins` nests). -/
inductive Wk : LCtx → LCtx → Type where
  | id (Γ : LCtx) : Wk Γ Γ
  | ins {Γ₀ Γ' : LCtx} (d : LocalDecl) (k : Nat)
      (ρ : Wk (insertAt d k Γ₀) Γ') : Wk Γ₀ Γ'

/-- the term translation induced by the weakening: `lift` at each
    insertion cutoff, outermost first. -/
def Wk.map : {Γ₀ Γ' : LCtx} → Wk Γ₀ Γ' → Expr Nat → Expr Nat
  | _, _, .id _, e => e
  | _, _, .ins _ k ρ, e => ρ.map (lift k 1 e)

/-- weakening preserves sorts. -/
theorem Wk.map_sort : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') → (l : Level) →
    ρ.map (.sort l) = .sort l
  | _, _, .id _, _ => rfl
  | _, _, .ins _ _ ρ, l => ρ.map_sort l

/-- weakening preserves constants. -/
theorem Wk.map_const : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') → (r : Nat) →
    (ls : List Level) → ρ.map (.const r ls) = .const r ls
  | _, _, .id _, _, _ => rfl
  | _, _, .ins _ _ ρ, r, ls => ρ.map_const r ls

/-- typing transports along a weakening (one `hasTyTWeaken` per
    insertion). -/
def Wk.hasTy (hcl : EnvClosed E) : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {a T : Expr Nat} → HasTyT E n Γ₀ a T →
    HasTyT E n Γ' (ρ.map a) (ρ.map T)
  | _, _, .id _, _, _, h => h
  | _, _, .ins d k ρ, _, _, h => ρ.hasTy hcl (hasTyTWeaken d hcl h)

/-- conversions transport along a weakening. -/
def Wk.conv (hcl : EnvClosed E) : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {a b T : Expr Nat} → ConvT E n Γ₀ a b T →
    ConvT E n Γ' (ρ.map a) (ρ.map b) (ρ.map T)
  | _, _, .id _, _, _, _, h => h
  | _, _, .ins d k ρ, _, _, _, h => ρ.conv hcl (convTWeaken d hcl h)

/-- index-conversion chains transport along a weakening. -/
def Wk.tyConv (hcl : EnvClosed E) : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {A B : Expr Nat} → TyConvT E n Γ₀ A B →
    TyConvT E n Γ' (ρ.map A) (ρ.map B)
  | _, _, .id _, _, _, h => h
  | _, _, .ins d k ρ, _, _, h => ρ.tyConv hcl (tyConvTWeaken d hcl h)

/-- extension under an assumption binder:
    `insertAt d (k+1) (.assumption A :: Γ₀) =
      .assumption (lift k 1 A) :: insertAt d k Γ₀` is `rfl`. -/
def Wk.ext : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') → (A : Expr Nat) →
    Wk (.assumption A :: Γ₀) (.assumption (ρ.map A) :: Γ')
  | _, _, .id _, _ => .id _
  | _, _, .ins d k ρ, A => .ins d (k+1) (ρ.ext (lift k 1 A))

/-! ### §2 the premise -/

/-- `CtxWfVia E n Γ₀`: `Γ₀` is the preimage of a well-formed target under
    a weakening. Weaker than `CtxWfT Γ₀` — every `CtxWfT` is a `Via` by
    `.id`, and a `Via` survives `insertAt` at the source. -/
structure CtxWfVia (E : ResolvedEnv) (n : Nat) (Γ₀ : LCtx) where
  target : LCtx
  ρ : Wk Γ₀ target
  wf : CtxWfT E n target

/-- every well-formed context is trivially `Via` (the identity
    weakening). -/
def CtxWfVia.ofWf {Γ₀ : LCtx} (hΓ : CtxWfT E n Γ₀) :
    CtxWfVia E n Γ₀ := ⟨Γ₀, .id Γ₀, hΓ⟩

/-- source-side weakening: if `insertAt d k Γ₀` is `Via`, so is `Γ₀`. -/
def CtxWfVia.wk {Γ₀ : LCtx} (d : LocalDecl) (k : Nat)
    (v : CtxWfVia E n (insertAt d k Γ₀)) : CtxWfVia E n Γ₀ :=
  ⟨v.target, .ins d k v.ρ, v.wf⟩

/-- extension under an assumption binder whose type is well-formed at
    the source. -/
def CtxWfVia.ext (hcl : EnvClosed E) {Γ₀ : LCtx} (v : CtxWfVia E n Γ₀)
    {A : Expr Nat} {u : Level} (hA : HasTyT E n Γ₀ A (.sort u)) :
    CtxWfVia E n (.assumption A :: Γ₀) :=
  ⟨.assumption (v.ρ.map A) :: v.target, v.ρ.ext A,
    .assumption _ _ _ v.wf (v.ρ.map_sort u ▸ v.ρ.hasTy hcl hA)⟩

/-! ### §3 the Prop-level consequences, re-proved under `Via` -/

/-- sort uniqueness at the source, through the morphism: transport both
    typings to the target and apply `SortUnique` there. -/
theorem CtxWfVia.sortUnique (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ₀ : LCtx} (v : CtxWfVia E n Γ₀) {T : Expr Nat} {u u' : Level}
    (h₁ : HasTyT E n Γ₀ T (.sort u)) (h₂ : HasTyT E n Γ₀ T (.sort u')) :
    eqN u u' :=
  su hW v.wf
    (v.ρ.map_sort u ▸ v.ρ.hasTy (envClosed_of_envWfT hW) h₁)
    (v.ρ.map_sort u' ▸ v.ρ.hasTy (envClosed_of_envWfT hW) h₂)

/-- sort-vs-Prop separation at the source, through the morphism. -/
theorem CtxWfVia.separation (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ₀ : LCtx} (v : CtxWfVia E n Γ₀) {P : Expr Nat} {l : Level}
    (hP : HasTyT E n Γ₀ P (.sort .zero)) (hc : TyConvT E n Γ₀ (.sort l) P) :
    False :=
  F8EtaK.separationAt_of_sortUniq hW (su hW) v.wf
    (v.ρ.map_sort .zero ▸ v.ρ.hasTy (envClosed_of_envWfT hW) hP)
    (v.ρ.map_sort l ▸ v.ρ.tyConv (envClosed_of_envWfT hW) hc)

/-- endpoint typings transport to the target: `convT_endpoints` applied
    to the transported conversion. -/
theorem CtxWfVia.endpoints (hW : EnvWfT E) {Γ₀ : LCtx} (v : CtxWfVia E n Γ₀)
    {a b T : Expr Nat} (c : ConvT E n Γ₀ a b T) :
    Nonempty (HasTyT E n v.target (v.ρ.map a) (v.ρ.map T)) ∧
      Nonempty (HasTyT E n v.target (v.ρ.map b) (v.ρ.map T)) :=
  convT_endpoints hW v.wf (v.ρ.conv (envClosed_of_envWfT hW) c)

/-! ### §4 D1 re-proved under `Via`

Same construction as `structPiJoin` (RcicF8DTileStep): the four `CtxWfT`
sites (`hΓ`, `hΓA`, `hΓA₁`, and the two `convT_endpoints` calls) are
replaced by `v.sortUnique`/`v.ext`/`v.endpoints`. The data is
identical — `structPiJoinVia_ofWf` below is `rfl` by proof
irrelevance. -/

/-- `structPi p₁ × structPi p₂` under `Via`: the forward closing step
    `Π A₁ B₁ ⇒ Π A₂ B₂`. -/
def structPiJoinVia (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfVia E n Γ) {A B A₁ B₁ A₂ B₂ T : Expr Nat}
    (p₁ : StructPiPayload R Γ A B A₁ B₁ T)
    (p₂ : StructPiPayload R Γ A B A₂ B₂ T) :
    StructPiPayload R Γ A₁ B₁ A₂ B₂ T :=
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  -- levels of the two inputs agree on the shared source
  have hu : eqN p₁.u p₂.u :=
    v.sortUnique hW su (p₁.hA.val hcl hinst) (p₂.hA.val hcl hinst)
  let vA : CtxWfVia E n (.assumption A :: Γ) :=
    v.ext hcl (p₁.hA.val hcl hinst)
  have hv : eqN p₁.v p₂.v :=
    vA.sortUnique hW su (p₁.hB.val hcl hinst) (p₂.hB.val hcl hinst)
  -- the domain and codomain chains at `p₂`'s levels
  let hc : EvCv R Γ A₁ A₂ (.sort p₂.u) :=
    .trans (.symm (.rety p₁.hc (sortsTc p₁.u p₂.u hu))) p₂.hc
  let hcB₀ : EvCv R (.assumption A :: Γ) B₁ B₂ (.sort p₂.v) :=
    .trans (.symm (.rety p₁.hcB (sortsTc p₁.v p₂.v hv))) p₂.hcB
  let hcB : EvCv R (.assumption A₁ :: Γ) B₁ B₂ (.sort p₂.v) :=
    cvCtxConvVar (.ofCv p₁.u (.symm p₁.hc)) p₁.hA hcB₀
  -- the target's own pieces, from the inverted root typing of `Π A₁ B₁`
  let inv := (EvTy.rety p₁.hrt p₁.idx).invPiT rfl
  have hu' : eqN inv.u p₂.u := by
    obtain ⟨_, ⟨hA₁⟩⟩ := v.endpoints hW (p₁.hc.val hcl hinst)
    have hA₁' : HasTyT E n v.target (v.ρ.map A₁) (.sort p₁.u) :=
      v.ρ.map_sort _ ▸ hA₁
    have hinv : HasTyT E n v.target (v.ρ.map A₁) (.sort inv.u) :=
      v.ρ.map_sort _ ▸ v.ρ.hasTy hcl (inv.hA.val hcl hinst)
    exact eqN_trans' (su hW v.wf hinv hA₁') hu
  let vA₁ : CtxWfVia E n (.assumption A₁ :: Γ) :=
    v.ext hcl (inv.hA.val hcl hinst)
  have hv' : eqN inv.v p₂.v := by
    obtain ⟨⟨hB₁⟩, _⟩ := vA₁.endpoints hW (hcB.val hcl hinst)
    have hB₁' : HasTyT E n vA₁.target (vA₁.ρ.map B₁) (.sort p₂.v) :=
      vA₁.ρ.map_sort _ ▸ hB₁
    have hinv : HasTyT E n vA₁.target (vA₁.ρ.map B₁) (.sort inv.v) :=
      vA₁.ρ.map_sort _ ▸ vA₁.ρ.hasTy hcl (inv.hB.val hcl hinst)
    exact su hW vA₁.wf hinv hB₁'
  { u := p₂.u, v := p₂.v
    hA := .rety inv.hA (sortsTc inv.u p₂.u hu')
    hc := hc
    hB := .rety inv.hB (sortsTc inv.v p₂.v hv')
    hcB := hcB
    hrt := p₂.hrt
    idx := p₂.idx }

/-- on `.ofWf` the Via construction is the landed one — the morphisms
    reduce to identities and only Prop arguments differ (proof
    irrelevance). -/
theorem structPiJoinVia_ofWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B A₁ B₁ A₂ B₂ T : Expr Nat}
    (p₁ : StructPiPayload R Γ A B A₁ B₁ T)
    (p₂ : StructPiPayload R Γ A B A₂ B₂ T) :
    structPiJoinVia hW su (.ofWf hΓ) p₁ p₂ = structPiJoin hW su hΓ p₁ p₂ :=
  rfl

/-- every leaf of the closing step is `SubEq` a leaf of the two inputs —
    the same argument as `structPiJoin_sound`, on identical data. -/
theorem structPiJoinVia_sound (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfVia E n Γ) {A B A₁ B₁ A₂ B₂ T : Expr Nat}
    (p₁ : StructPiPayload R Γ A B A₁ B₁ T)
    (p₂ : StructPiPayload R Γ A B A₂ B₂ T) :
    ∀ ℓ ∈ (structPiJoinVia hW su v p₁ p₂).leaves,
      ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq ℓ ℓ' := by
  intro ℓ hℓ
  have hinv := (EvTy.rety p₁.hrt p₁.idx).invPiT_leaves (A := A₁) (B := B₁) rfl
  have h₁ : ∀ x, x ∈ p₁.hrt.leaves ∨ x ∈ p₁.idx.leaves →
      x ∈ p₁.leaves ++ p₂.leaves := by
    intro x hx
    simp only [StructPiPayload.leaves, List.mem_append]
    rcases hx with h | h
    · exact .inl (.inl (.inr h))
    · exact .inl (.inr h)
  have hroot : ∀ x ∈ (EvTy.rety p₁.hrt p₁.idx).leaves,
      x ∈ p₁.leaves ++ p₂.leaves := by
    intro x hx
    simp only [EvTy.leaves, List.mem_append] at hx
    exact h₁ x hx
  have m1 : ∀ x ∈ p₁.leaves, x ∈ p₁.leaves ++ p₂.leaves :=
    fun x hx => List.mem_append.mpr (.inl hx)
  have m2 : ∀ x ∈ p₂.leaves, x ∈ p₁.leaves ++ p₂.leaves :=
    fun x hx => List.mem_append.mpr (.inr hx)
  simp only [structPiJoinVia, StructPiPayload.leaves, cvCtxConvVar_leaves,
    EvTy.leaves, EvCv.leaves, EvTc.leaves, sortsTc_leaves, List.append_nil,
    List.mem_append] at hℓ
  rcases hℓ with (((((hA | hc) | hB) | hcB) | hrt) | hidx)
  · obtain ⟨k, hk, hs⟩ := hinv ℓ (by
      simp only [EvInvPi.leaves, List.mem_append]; exact .inl (.inl hA))
    exact ⟨k, hroot k hk, hs⟩
  · rcases hc with (h | h)
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [StructPiPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inr h))))))
    · exact dSubEq_of_mem (m2 ℓ (by
        simp only [StructPiPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inr h))))))
  · obtain ⟨k, hk, hs⟩ := hinv ℓ (by
      simp only [EvInvPi.leaves, List.mem_append]; exact .inl (.inr hB))
    exact ⟨k, hroot k hk, hs⟩
  · rcases hcB with ((h | h) | h) | h
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [StructPiPayload.leaves, List.mem_append]
        exact .inl (.inl (.inr h))))
    · exact dSubEq_of_mem (m2 ℓ (by
        simp only [StructPiPayload.leaves, List.mem_append]
        exact .inl (.inl (.inr h))))
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [StructPiPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inr h))))))
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [StructPiPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inl h))))))
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [StructPiPayload.leaves, List.mem_append]
      exact .inl (.inr hrt)))
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [StructPiPayload.leaves, List.mem_append]
      exact .inr hidx))

/-! ### §5 the J twins, beside the landed fronts -/

namespace J1

/-- the `Via` front twin of `dispatchWf`: same three arms, the premise
    is a `CtxWfVia` (unused — the base cases never inspect it, exactly
    like `dispatchWf`'s `hΓ`). -/
def dispatchVia (hW : EnvWfT E) (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → CtxWfVia E n Γ →
    (h : ConvT E n Γ a b T) → (∃ r ∈ R, SubEq (Jd.cv h) r) →
    Option (Result hW R h)
  | _, _, _, _, _, .refl _ _ _ ha, hsub => some (reflResult hW ha hsub)
  | _, _, _, _, _, .irr _ _ _ _ hP hp hq, hsub =>
      some (irrResult hW hP hp hq hsub)
  | _, _, _, _, _, _, _ => none

/-- on `.ofWf` the twin is the landed front. -/
theorem dispatchVia_ofWf (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hsub : ∃ r ∈ R, SubEq (Jd.cv h) r) :
    dispatchVia hW R (.ofWf hΓ) h hsub = dispatchWf hW R hΓ h hsub := by
  cases h <;> rfl

/-- the twin accepts exactly the landed base domain. -/
theorem dispatchVia_coverage (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hsub : ∃ r ∈ R, SubEq (Jd.cv h) r) :
    (dispatchVia hW R v h hsub).isSome = isBase h := by
  cases h <;> rfl

end J1

namespace JEndpoints

/-- the `Via` front twin of `extractWf`: the premise is a `CtxWfVia`
    (unused — `extract` is structural). -/
def extractVia (_hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (_v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    Option (Packet R h) := extract h hs

/-- on `.ofWf` the twin is the landed front. -/
theorem extractVia_ofWf (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    extractVia hW R (.ofWf hΓ) h hs = extractWf hW R hΓ h hs := rfl

/-- the twin accepts exactly the landed supported domain. -/
theorem extractVia_coverage (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    (extractVia hW R v h hs).isSome = supported h := extract_coverage h hs

end JEndpoints

namespace J3

/-- the `Via` front twin of `dispatchWf`: the same recursion, `v`
    carried where the landed front carries `hΓ`. -/
def dispatchVia (hW : EnvWfT E) (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → CtxWfVia E n Γ →
    (h : ConvT E n Γ a b T) → (∃ r ∈ R, SubEq (.cv h) r) →
    Option (Result hW R h)
  | _, _, _, _, _, .refl _ _ _ ha, hs => some (reflResult hW ha hs)
  | _, _, _, _, _, .irr _ _ _ _ hP hp hq, hs =>
      some (irrResult hW hP hp hq hs)
  | Γ, _, _, _, v, .symm _ a b T h, hs =>
      match dispatchVia hW R v h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs) with
      | none => none
      | some p => some p.swap
  | Γ, _, _, _, v, .tyConv _ a b T U u h hT, hs =>
      match dispatchVia hW R v h
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs) with
      | none => none
      | some p => some (p.reindex u hT hs)
  | _, _, _, _, _, .trans .., _ => none
  | _, _, _, _, _, .beta .., _ => none
  | _, _, _, _, _, .zeta .., _ => none
  | _, _, _, _, _, .zetaLocal .., _ => none
  | _, _, _, _, _, .delta .., _ => none
  | _, _, _, _, _, .iota .., _ => none
  | _, _, _, _, _, .lit .., _ => none
  | _, _, _, _, _, .app .., _ => none
  | _, _, _, _, _, .lam .., _ => none
  | _, _, _, _, _, .pi .., _ => none
  | _, _, _, _, _, .letE .., _ => none
  | _, _, _, _, _, .sorts .., _ => none
  | _, _, _, _, _, .consts .., _ => none
  | _, _, _, _, _, .eta .., _ => none

/-- on `.ofWf` the twin is the landed front, by recursion. -/
theorem dispatchVia_ofWf (hW : EnvWfT E) (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → (hΓ : CtxWfT E n Γ) →
    (h : ConvT E n Γ a b T) → (hs : ∃ r ∈ R, SubEq (.cv h) r) →
    dispatchVia hW R (.ofWf hΓ) h hs = dispatchWf hW R hΓ h hs
  | _, _, _, _, _, .refl .., _ => rfl
  | _, _, _, _, _, .irr .., _ => rfl
  | Γ, _, _, _, hΓ, .symm _ a b T h, hs => by
      simp only [dispatchVia, dispatchWf]
      rw [dispatchVia_ofWf hW R hΓ h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs)]
      rfl
  | Γ, _, _, _, hΓ, .tyConv _ a b T U u h hT, hs => by
      simp only [dispatchVia, dispatchWf]
      rw [dispatchVia_ofWf hW R hΓ h
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs)]
      rfl
  | _, _, _, _, _, .trans .., _ => rfl
  | _, _, _, _, _, .beta .., _ => rfl
  | _, _, _, _, _, .zeta .., _ => rfl
  | _, _, _, _, _, .zetaLocal .., _ => rfl
  | _, _, _, _, _, .delta .., _ => rfl
  | _, _, _, _, _, .iota .., _ => rfl
  | _, _, _, _, _, .lit .., _ => rfl
  | _, _, _, _, _, .app .., _ => rfl
  | _, _, _, _, _, .lam .., _ => rfl
  | _, _, _, _, _, .pi .., _ => rfl
  | _, _, _, _, _, .letE .., _ => rfl
  | _, _, _, _, _, .sorts .., _ => rfl
  | _, _, _, _, _, .consts .., _ => rfl
  | _, _, _, _, _, .eta .., _ => rfl

/-- the twin accepts exactly the landed supported domain. -/
theorem dispatchVia_coverage (hW : EnvWfT E) (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → (v : CtxWfVia E n Γ) →
    (h : ConvT E n Γ a b T) → (hs : ∃ r ∈ R, SubEq (.cv h) r) →
    (dispatchVia hW R v h hs).isSome = supported h
  | _, _, _, _, _, .refl .., _ => rfl
  | _, _, _, _, _, .irr .., _ => rfl
  | Γ, _, _, _, v, .symm _ a b T h, hs => by
      have ih := dispatchVia_coverage hW R v h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs)
      simp only [dispatchVia, supported]
      cases he : dispatchVia hW R v h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs) <;>
        simpa only [he, Option.isSome] using ih
  | Γ, _, _, _, v, .tyConv _ a b T U u h hT, hs => by
      have ih := dispatchVia_coverage hW R v h
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs)
      simp only [dispatchVia, supported]
      cases he : dispatchVia hW R v h
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs) <;>
        simpa only [he, Option.isSome] using ih
  | _, _, _, _, _, .trans .., _ => rfl
  | _, _, _, _, _, .beta .., _ => rfl
  | _, _, _, _, _, .zeta .., _ => rfl
  | _, _, _, _, _, .zetaLocal .., _ => rfl
  | _, _, _, _, _, .delta .., _ => rfl
  | _, _, _, _, _, .iota .., _ => rfl
  | _, _, _, _, _, .lit .., _ => rfl
  | _, _, _, _, _, .app .., _ => rfl
  | _, _, _, _, _, .lam .., _ => rfl
  | _, _, _, _, _, .pi .., _ => rfl
  | _, _, _, _, _, .letE .., _ => rfl
  | _, _, _, _, _, .sorts .., _ => rfl
  | _, _, _, _, _, .consts .., _ => rfl
  | _, _, _, _, _, .eta .., _ => rfl

end J3

/-! ### §6 the X-facing supplier shape -/

/-- H-J under `Via`, partial: a join for a bare `ConvT` literal
    certified into `R`, where the context is well-formed only up to a
    weakening — or a refusal. Sibling of `JProcWfP` /
    `JContractWfP`. -/
abbrev JProcViaP (R : List (Jd E n)) : Type :=
  ∀ {Γ₀ : LCtx} {M₁ M₂ T : Expr Nat}, CtxWfVia E n Γ₀ →
    (h : ConvT E n Γ₀ M₁ M₂ T) → (∃ r ∈ R, SubEq (.cv h) r) →
    Option (Valley R Γ₀ M₁ M₂ T)

/-- the strict leaf contract on `Via`-front answers — same clause as
    `JContractWfP`. -/
def JContractViaP (J : ∀ R : List (Jd E n), JProcViaP R) : Prop :=
  ∀ R {Γ₀ : LCtx} {M₁ M₂ T : Expr Nat} (v : CtxWfVia E n Γ₀)
    (h : ConvT E n Γ₀ M₁ M₂ T) (hsub : ∃ r ∈ R, SubEq (.cv h) r)
    (V : Valley R Γ₀ M₁ M₂ T), J R v h hsub = some V →
    ∀ ℓ ∈ V.leaves, SubOf ℓ (.cv h)

/-- a `Via` supplier restricts to a `Wf` supplier through `ofWf`. -/
def JProcViaP.toWfP (J : ∀ R : List (Jd E n), JProcViaP R) :
    ∀ R : List (Jd E n), JProcWfP R :=
  fun R {_ _ _ _} hΓ h hs => J R (.ofWf hΓ) h hs

/-- the strict clause is preserved under `ofWf` restriction. -/
theorem JContractViaP.toWfP {J : ∀ R : List (Jd E n), JProcViaP R}
    (hJ : JContractViaP J) : JContractWfP (JProcViaP.toWfP J) := by
  intro R Γ M₁ M₂ T hΓ h hsub V hV
  exact hJ R (.ofWf hΓ) h hsub V hV

/-- a premise-free (unconditional) partial supplier is trivially a `Via`
    supplier. -/
def JProcViaP.ofUncond (J : ∀ R : List (Jd E n),
    ∀ {Γ : LCtx} {M₁ M₂ T : Expr Nat}, (h : ConvT E n Γ M₁ M₂ T) →
      (∃ r ∈ R, SubEq (.cv h) r) → Option (Valley R Γ M₁ M₂ T)) :
    ∀ R : List (Jd E n), JProcViaP R :=
  fun R {_ _ _ _} _v h hs => J R h hs

/-- J1 as a `Via` supplier. -/
def j1Via (hW : EnvWfT E) : ∀ R : List (Jd E n), JProcViaP R :=
  fun R {_ _ _ _} v h hs => (J1.dispatchVia hW R v h hs).map (·.valley)

/-- J1's `Via` supplier satisfies the strict leaf contract — the
    `Result`'s `strict` field. -/
theorem j1Via_contract (hW : EnvWfT E) : JContractViaP (j1Via (n := n) hW) := by
  intro R Γ₀ M₁ M₂ T v h hsub V hV
  have hV' : (J1.dispatchVia hW R v h hsub).map (·.valley) = some V := hV
  obtain ⟨r, _, rfl⟩ := Option.map_eq_some'.mp hV'
  exact r.strict

/-- J3 as a `Via` supplier. -/
def j3Via (hW : EnvWfT E) : ∀ R : List (Jd E n), JProcViaP R :=
  fun R {_ _ _ _} v h hs => (J3.dispatchVia hW R v h hs).map (·.valley)

/-- J3's `Via` supplier satisfies the strict leaf contract. -/
theorem j3Via_contract (hW : EnvWfT E) : JContractViaP (j3Via (n := n) hW) := by
  intro R Γ₀ M₁ M₂ T v h hsub V hV
  have hV' : (J3.dispatchVia hW R v h hsub).map (·.valley) = some V := hV
  obtain ⟨r, _, rfl⟩ := Option.map_eq_some'.mp hV'
  exact r.strict

/-! ### §7 teeth -/

/-- the invariant the tooth rides on: an entry `.assumption (.const 0 [])`
    survives every insertion (`lift` never touches a `const`). -/
def HasConst0Entry (Γ : LCtx) : Prop :=
  ∃ Δ Γ₁ : LCtx, Γ = Δ ++ .assumption (.const 0 []) :: Γ₁

/-- insertion preserves a `const 0` entry: the inserted declaration goes
    above or below it, and `liftDecl` leaves the `const` entry
    unchanged. -/
theorem hasConst0Entry_insertAt (d : LocalDecl) : (k : Nat) → (Γ : LCtx) →
    HasConst0Entry Γ → HasConst0Entry (insertAt d k Γ)
  | 0, _, ⟨Δ, Γ₁, rfl⟩ => ⟨d :: Δ, Γ₁, rfl⟩
  | _+1, [], h => by
      obtain ⟨Δ, _, hΔ⟩ := h
      cases Δ with
      | nil => exact List.noConfusion hΔ
      | cons _ _ => exact List.noConfusion hΔ
  | k+1, x :: Γ', h => by
      obtain ⟨Δ, Γ₁, hΔ⟩ := h
      cases Δ with
      | nil =>
          simp only [List.nil_append] at hΔ
          injection hΔ with hx hΓ'
          subst hx; subst hΓ'
          exact ⟨[], insertAt d k Γ', rfl⟩
      | cons y Δ' =>
          simp only [List.cons_append] at hΔ
          injection hΔ with hx hΓ'
          subst hx; subst hΓ'
          obtain ⟨Δ₂, Γ₁', hrec⟩ :=
            hasConst0Entry_insertAt d k _ ⟨Δ', Γ₁, rfl⟩
          exact ⟨liftDecl k x :: Δ₂, Γ₁', by
            rw [insertAt_succ_cons, hrec]; rfl⟩

/-- a weakening morphism preserves a `const 0` entry. -/
theorem Wk.hasConst0Entry : {Γ₀ Γ' : LCtx} → Wk Γ₀ Γ' →
    HasConst0Entry Γ₀ → HasConst0Entry Γ'
  | _, _, .id _, h => h
  | _, _, .ins d k ρ, h => ρ.hasConst0Entry (hasConst0Entry_insertAt d k _ h)

/-- a prefix of declarations can be dropped from a well-formed context:
    induction on the prefix with `ctxWfT_tail`. -/
theorem ctxWfT_drop : (Δ : LCtx) → {Γ : LCtx} →
    CtxWfT E n (Δ ++ Γ) → Nonempty (CtxWfT E n Γ)
  | [], _, h => ⟨h⟩
  | _ :: Δ', _, h => ctxWfT_drop Δ' (ctxWfT_tail h)

/-- TOOTH: the ill-formed `XTileQ1.illCtx` has no `Via` witness — no
    weakening of it is well-formed, because the `const 0` entry survives
    every insertion and a well-formed target would type it in the tail. -/
theorem illCtx_no_via : ¬ Nonempty (CtxWfVia emptyEnv 0 XTileQ1.illCtx) := by
  rintro ⟨⟨Γ', ρ, wf⟩⟩
  obtain ⟨Δ, Γ₁, hΓ'⟩ := ρ.hasConst0Entry ⟨[], _, rfl⟩
  obtain ⟨hwf⟩ := ctxWfT_drop Δ (hΓ' ▸ wf)
  cases hwf with
  | assumption _ _ _ _ hA =>
      obtain ⟨m, hm, _, _, _⟩ := hasTyTInv_const hA rfl
      exact Option.noConfusion hm

/-- MUTANT (tooth): the morphism derivation dropped — an arbitrary
    context map carrying the target's well-formedness AND the map's
    sort-preservation — everything a consumer reads off `Wk.map_sort`.
    It still accepts `illCtx` (send it to `[]`): what makes `CtxWfVia`
    sound is not a property of the map but that the map IS a weakening —
    that the transport `Wk.hasTy` exists (and `illCtx_no_via` shows no
    weakening of `illCtx` has a well-formed target). -/
structure CtxWfViaMut (E : ResolvedEnv) (n : Nat) (Γ₀ : LCtx) where
  target : LCtx
  map : Expr Nat → Expr Nat
  map_sort : ∀ l : Level, map (.sort l) = .sort l
  wf : CtxWfT E n target

/-- the mutant accepts `illCtx` (the empty target is well-formed and the
    identity preserves sorts; no entry survives because the map need not
    be a weakening). -/
theorem mutant_accepts_illCtx :
    Nonempty (CtxWfViaMut emptyEnv 0 XTileQ1.illCtx) :=
  ⟨⟨[], fun e => e, fun _ => rfl, .nil⟩⟩

/-! ### §8 non-vacuity pins -/

section Pins

/-- `[x : Sort 0]` — a well-formed context. -/
def pinCtx : LCtx := [.assumption (.sort .zero)]

/-- `pinCtx` is well-formed: `sort 0 : sort 1` at `[]`. -/
def pinCtxWf : CtxWfT emptyEnv 0 pinCtx :=
  .assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)

/-- `pinCtx` weakened by one `sort 0` assumption at cutoff 1. -/
def pinTarget : LCtx := insertAt (.assumption (.sort .zero)) 1 pinCtx

/-- `pinTarget` is well-formed. -/
def pinTargetWf : CtxWfT emptyEnv 0 pinTarget :=
  .assumption pinCtx (.sort .zero) (.succ .zero) pinCtxWf
    (.sort pinCtx .zero)

/-- a `Via` witness that is NOT an `ofWf`: `pinCtx` seen through a
    cutoff-1 weakening. -/
def pinVia : CtxWfVia emptyEnv 0 pinCtx :=
  .wk (.assumption (.sort .zero)) 1 (.ofWf pinTargetWf)

/-- the `Via` witness's target is the inserted context. -/
theorem pinVia_target : pinVia.target = pinTarget := rfl

/-- the weakening's map sends `bvar 0` to itself — `bvar 0` is below the
    insertion cutoff 1. -/
theorem pinVia_map_bvar0 : pinVia.ρ.map (.bvar 0) = .bvar 0 := rfl

/-- a typing transports: `bvar 0 : sort 0` at `pinCtx` lands at
    `pinTarget`. -/
theorem pinVia_hasTy :
    Nonempty (HasTyT emptyEnv 0 pinTarget
      (pinVia.ρ.map (.bvar 0)) (pinVia.ρ.map (.sort .zero))) :=
  ⟨pinVia.ρ.hasTy (envClosed_of_envWfT EnvWfT.empty)
    (show HasTyT emptyEnv 0 pinCtx (.bvar 0) (.sort .zero) from
      .bvar _ 0 _ rfl)⟩

/-- one real literal for the J pins: `sort 0 ≡ sort 0` at `sort 1`. -/
private def pinReflCv :
    ConvT emptyEnv 0 [] (.sort .zero) (.sort .zero)
      (.sort (.succ .zero)) :=
  .refl [] (.sort .zero) (.sort (.succ .zero)) (.sort [] .zero)

private def pinReflRoot : Jd emptyEnv 0 := .cv pinReflCv
private def pinReflR : List (Jd emptyEnv 0) := [pinReflRoot]
private def pinReflSub :
    ∃ r ∈ pinReflR, SubEq (.cv pinReflCv) r :=
  ⟨pinReflRoot, .head _, .inl rfl⟩

/-- `symm` of the literal. -/
private def pinSymmCv :
    ConvT emptyEnv 0 [] (.sort .zero) (.sort .zero)
      (.sort (.succ .zero)) :=
  .symm _ _ _ _ pinReflCv

private def pinSymmRoot : Jd emptyEnv 0 := .cv pinSymmCv
private def pinSymmR : List (Jd emptyEnv 0) := [pinSymmRoot]
private def pinSymmSub :
    ∃ r ∈ pinSymmR, SubEq (.cv pinSymmCv) r :=
  ⟨pinSymmRoot, .head _, .inl rfl⟩

/-- J1's `Via` supplier answers the real `refl` literal. -/
theorem pin_j1Via_refl :
    (j1Via EnvWfT.empty pinReflR (.ofWf CtxWfT.nil) pinReflCv
      pinReflSub).isSome = true := rfl

/-- `symm` of the literal is answered by J3's `Via` supplier. -/
theorem pin_j3Via_symm_refl :
    (j3Via EnvWfT.empty pinSymmR (.ofWf CtxWfT.nil) pinSymmCv
      pinSymmSub).isSome = true := rfl

/-- J1's `Via` supplier restricted through `ofWf` is the landed
    `dispatchWf` front, pointwise. -/
theorem pin_j1Via_ofWf (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (hΓ : CtxWfT E n Γ) (h : ConvT E n Γ a b T)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    JProcViaP.toWfP (j1Via hW) R hΓ h hs =
      (J1.dispatchWf hW R hΓ h hs).map (·.valley) := by
  show (J1.dispatchVia hW R (.ofWf hΓ) h hs).map (·.valley) = _
  rw [J1.dispatchVia_ofWf]

/-- a literal conversion at `pinCtx`: `bvar 0 ≡ bvar 0 : sort 0`. -/
private def pinVarRefl :
    ConvT emptyEnv 0 pinCtx (.bvar 0) (.bvar 0) (.sort .zero) :=
  .refl pinCtx (.bvar 0) (.sort .zero) (.bvar _ 0 _ rfl)

private def pinVarReflRoot : Jd emptyEnv 0 := .cv pinVarRefl
private def pinVarReflR : List (Jd emptyEnv 0) := [pinVarReflRoot]
private def pinVarReflSub :
    ∃ r ∈ pinVarReflR, SubEq (.cv pinVarRefl) r :=
  ⟨pinVarReflRoot, .head _, .inl rfl⟩

/-- `symm` of the `pinCtx` literal. -/
private def pinVarSymmCv :
    ConvT emptyEnv 0 pinCtx (.bvar 0) (.bvar 0) (.sort .zero) :=
  .symm _ _ _ _ pinVarRefl

private def pinVarSymmRoot : Jd emptyEnv 0 := .cv pinVarSymmCv
private def pinVarSymmR : List (Jd emptyEnv 0) := [pinVarSymmRoot]
private def pinVarSymmSub :
    ∃ r ∈ pinVarSymmR, SubEq (.cv pinVarSymmCv) r :=
  ⟨pinVarSymmRoot, .head _, .inl rfl⟩

/-- the twins answer a literal whose context is known well-formed only
    through a cutoff-1 weakening (`pinVia`), which `JProcWfP` could not
    even be asked. -/
theorem pin_j1Via_via :
    (j1Via EnvWfT.empty pinVarReflR pinVia pinVarRefl
      pinVarReflSub).isSome = true := rfl

/-- `symm` of the literal under the same non-`ofWf` premise. -/
theorem pin_j3Via_via :
    (j3Via EnvWfT.empty pinVarSymmR pinVia pinVarSymmCv
      pinVarSymmSub).isSome = true := rfl

end Pins

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.Wk
#print axioms Rcic.Declarative.F8Measure.Wk.map
#print axioms Rcic.Declarative.F8Measure.Wk.map_sort
#print axioms Rcic.Declarative.F8Measure.Wk.map_const
#print axioms Rcic.Declarative.F8Measure.Wk.hasTy
#print axioms Rcic.Declarative.F8Measure.Wk.conv
#print axioms Rcic.Declarative.F8Measure.Wk.tyConv
#print axioms Rcic.Declarative.F8Measure.Wk.ext
#print axioms Rcic.Declarative.F8Measure.CtxWfVia
#print axioms Rcic.Declarative.F8Measure.CtxWfVia.ofWf
#print axioms Rcic.Declarative.F8Measure.CtxWfVia.wk
#print axioms Rcic.Declarative.F8Measure.CtxWfVia.ext
#print axioms Rcic.Declarative.F8Measure.CtxWfVia.sortUnique
#print axioms Rcic.Declarative.F8Measure.CtxWfVia.separation
#print axioms Rcic.Declarative.F8Measure.CtxWfVia.endpoints
#print axioms Rcic.Declarative.F8Measure.structPiJoinVia
#print axioms Rcic.Declarative.F8Measure.structPiJoinVia_ofWf
#print axioms Rcic.Declarative.F8Measure.structPiJoinVia_sound
#print axioms Rcic.Declarative.F8Measure.J1.dispatchVia
#print axioms Rcic.Declarative.F8Measure.J1.dispatchVia_ofWf
#print axioms Rcic.Declarative.F8Measure.J1.dispatchVia_coverage
#print axioms Rcic.Declarative.F8Measure.JEndpoints.extractVia
#print axioms Rcic.Declarative.F8Measure.JEndpoints.extractVia_ofWf
#print axioms Rcic.Declarative.F8Measure.JEndpoints.extractVia_coverage
#print axioms Rcic.Declarative.F8Measure.J3.dispatchVia
#print axioms Rcic.Declarative.F8Measure.J3.dispatchVia_ofWf
#print axioms Rcic.Declarative.F8Measure.J3.dispatchVia_coverage
#print axioms Rcic.Declarative.F8Measure.JProcViaP
#print axioms Rcic.Declarative.F8Measure.JContractViaP
#print axioms Rcic.Declarative.F8Measure.JProcViaP.toWfP
#print axioms Rcic.Declarative.F8Measure.JContractViaP.toWfP
#print axioms Rcic.Declarative.F8Measure.JProcViaP.ofUncond
#print axioms Rcic.Declarative.F8Measure.j1Via
#print axioms Rcic.Declarative.F8Measure.j1Via_contract
#print axioms Rcic.Declarative.F8Measure.j3Via
#print axioms Rcic.Declarative.F8Measure.j3Via_contract
#print axioms Rcic.Declarative.F8Measure.HasConst0Entry
#print axioms Rcic.Declarative.F8Measure.hasConst0Entry_insertAt
#print axioms Rcic.Declarative.F8Measure.Wk.hasConst0Entry
#print axioms Rcic.Declarative.F8Measure.ctxWfT_drop
#print axioms Rcic.Declarative.F8Measure.illCtx_no_via
#print axioms Rcic.Declarative.F8Measure.CtxWfViaMut
#print axioms Rcic.Declarative.F8Measure.mutant_accepts_illCtx
#print axioms Rcic.Declarative.F8Measure.pinCtx
#print axioms Rcic.Declarative.F8Measure.pinCtxWf
#print axioms Rcic.Declarative.F8Measure.pinTarget
#print axioms Rcic.Declarative.F8Measure.pinTargetWf
#print axioms Rcic.Declarative.F8Measure.pinVia
#print axioms Rcic.Declarative.F8Measure.pinVia_target
#print axioms Rcic.Declarative.F8Measure.pinVia_map_bvar0
#print axioms Rcic.Declarative.F8Measure.pinVia_hasTy
#print axioms Rcic.Declarative.F8Measure.pin_j1Via_refl
#print axioms Rcic.Declarative.F8Measure.pin_j3Via_symm_refl
#print axioms Rcic.Declarative.F8Measure.pin_j1Via_ofWf
#print axioms Rcic.Declarative.F8Measure.pin_j1Via_via
#print axioms Rcic.Declarative.F8Measure.pin_j3Via_via
