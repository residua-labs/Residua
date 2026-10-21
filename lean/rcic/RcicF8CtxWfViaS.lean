import rcic.RcicF8CtxWfVia
import rcic.RcicCtxMorphStack
import rcic.RcicDT0709EnvWf
import rcic.RcicTypedValidity

open Rcic.Syn

/-! # RcicF8CtxWfViaS — WK-2 of W-X-WK (#7128 ruling Q2; #7148 design, cc-approved 03:25Z)

WK-1a's J context premise widened from the weakening class `Wk` to PR-A's
`CtxMorph` (ins / sub / subLet stacks, `RcicCtxMorphStack`): `CtxWfViaS Γ₀` is
`⟨target, σ : CtxMorph E n Γ₀ target, wf⟩`. WK-1a's `Wk`/`CtxWfVia` stay as the
`ins` specialization (`Wk.toCtxMorph`, `CtxWfVia.toS`); the inner literals of an
`esub j`/`subst0 j`/`substLet j` link get
`⟨substRemove v j Γ, .sub j hget hv.val .nil, hΓ⟩` at every `j` (closes
W-X-SUBST-DEPTH's J half; #7107 §3's j=0 regularity rebuild unnecessary). The
converse (`CtxWfT (substRemove v j Γ) → hv → CtxWfT Γ`) is NOT claimed and is
recorded as the named open `W-X-SUBST-DEPTH-CONVERSE-REFUTED-UNSEALED`
(S1 §5.1); no statement here asserts it false.

D1's `structPiJoin` is re-proved under `ViaS` (`structPiJoinViaS`); J1/J2/J3 get
`ViaS` twins; the X-facing `JProcViaSP`/`JContractViaSP` sit one level above
WK-1a's `ViaP`. Teeth: `illCtx` has no `ViaS` witness — a `sub` AT the `const 0`
entry is refuted by transporting its `hv` along the rest of the stack to the
well-formed target and applying regularity there (`const0_stack_refuted`); two
mutants — the `sub` arm without `hv`, and `hv` typed at the source context —
accept `illCtx`. `closure_claim = 0`. -/

namespace Rcic.Declarative.F8Measure

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### §1 the bridge from WK-1a's class -/

/-- a weakening is an `ins`-only stack. -/
def Wk.toCtxMorph : {Γ₀ Γ' : LCtx} → Wk Γ₀ Γ' → CtxMorph E n Γ₀ Γ'
  | _, _, .id _ => .nil
  | _, _, .ins d k ρ => .ins d k ρ.toCtxMorph

/-- the stack's action agrees with `Wk.map` entry-wise. -/
theorem Wk.toCtxMorph_apply : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    (e : Expr Nat) → (ρ.toCtxMorph (E := E) (n := n)).apply e = ρ.map e
  | _, _, .id _, _ => rfl
  | _, _, .ins _ _ ρ, _ => ρ.toCtxMorph_apply _

/-! ### §2 the premise -/

/-- `CtxWfViaS E n Γ₀`: `Γ₀` is the preimage of a well-formed target under a
    `CtxMorph` stack (insertions and TYPED substitutions). Weaker than
    `CtxWfT Γ₀` — every `CtxWfT` is a `ViaS` by `.nil`, a `ViaS` survives
    `insertAt` at the source, and — new in WK-2 — it survives `substRemove`
    when the substituting value is typed just after the removal. -/
structure CtxWfViaS (E : ResolvedEnv) (n : Nat) (Γ₀ : LCtx) where
  target : LCtx
  σ : CtxMorph E n Γ₀ target
  wf : CtxWfT E n target

/-- every well-formed context is trivially `ViaS` (the empty stack). -/
def CtxWfViaS.ofWf {Γ₀ : LCtx} (hΓ : CtxWfT E n Γ₀) :
    CtxWfViaS E n Γ₀ := ⟨Γ₀, .nil, hΓ⟩

/-- source-side insertion. -/
def CtxWfViaS.ins {Γ₀ : LCtx} (d : LocalDecl) (k : Nat)
    (v : CtxWfViaS E n (insertAt d k Γ₀)) : CtxWfViaS E n Γ₀ :=
  ⟨v.target, .ins d k v.σ, v.wf⟩

/-- source-side substitution of an assumption entry at depth `j`: the inner
    literal of an `esub j`/`subst0 j` link, answered from the OUTER context's
    well-formedness and `hv` alone — no `CtxWfT Γ₀` is built. -/
def CtxWfViaS.sub {Γ₀ : LCtx} {t v : Expr Nat} (j : Nat)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t))
    (w : CtxWfViaS E n (substRemove v j Γ₀)) : CtxWfViaS E n Γ₀ :=
  ⟨w.target, .sub j hget hv w.σ, w.wf⟩

/-- source-side substitution of a let-binding entry at depth `j`. -/
def CtxWfViaS.subLet {Γ₀ : LCtx} {t w₀ : Expr Nat} (j : Nat)
    (hget : Γ₀[j]? = some (.letBinding t w₀))
    (hv : HasTyT E n (substRemove w₀ j Γ₀) (lift 0 j w₀) (lift 0 j t))
    (v : CtxWfViaS E n (substRemove w₀ j Γ₀)) : CtxWfViaS E n Γ₀ :=
  ⟨v.target, .subLet j hget hv v.σ, v.wf⟩

/-- a stack plus a well-formed target is a witness. -/
def CtxWfViaS.ofStack {Γ₀ Γ' : LCtx} (σ : CtxMorph E n Γ₀ Γ')
    (hΓ : CtxWfT E n Γ') : CtxWfViaS E n Γ₀ := ⟨Γ', σ, hΓ⟩

/-- WK-1a's premise embeds: the weakening becomes its `ins`-only stack. -/
def CtxWfVia.toS {Γ₀ : LCtx} (v : CtxWfVia E n Γ₀) : CtxWfViaS E n Γ₀ :=
  ⟨v.target, v.ρ.toCtxMorph, v.wf⟩

/-- `toS` maps `ofWf` to `ofWf`. -/
theorem CtxWfVia.toS_ofWf {Γ₀ : LCtx} (hΓ : CtxWfT E n Γ₀) :
    (CtxWfVia.ofWf hΓ).toS = CtxWfViaS.ofWf hΓ := rfl

/-- extension under an assumption binder whose type is well-formed at the
    source: the stack shifts entry-wise (`CtxMorph.under`). -/
def CtxWfViaS.ext (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ₀ : LCtx} (v : CtxWfViaS E n Γ₀) {A : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ₀ A (.sort u)) :
    CtxWfViaS E n (.assumption A :: Γ₀) :=
  ⟨.assumption (v.σ.apply A) :: v.target, v.σ.under hcl A,
    .assumption _ _ _ v.wf (v.σ.apply_sort u ▸ v.σ.hasTyT hcl hinst hA)⟩

/-! ### §3 the Prop-level consequences, re-proved under `ViaS` -/

/-- sort uniqueness at the source, through the stack: transport both typings
    to the target and apply `SortUnique` there. -/
theorem CtxWfViaS.sortUnique (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ₀ : LCtx} (v : CtxWfViaS E n Γ₀) {T : Expr Nat} {u u' : Level}
    (h₁ : HasTyT E n Γ₀ T (.sort u)) (h₂ : HasTyT E n Γ₀ T (.sort u')) :
    eqN u u' :=
  su hW v.wf
    (v.σ.apply_sort u ▸
      v.σ.hasTyT (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) h₁)
    (v.σ.apply_sort u' ▸
      v.σ.hasTyT (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) h₂)

/-- sort-vs-Prop separation at the source, through the stack. -/
theorem CtxWfViaS.separation (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ₀ : LCtx} (v : CtxWfViaS E n Γ₀) {P : Expr Nat} {l : Level}
    (hP : HasTyT E n Γ₀ P (.sort .zero)) (hc : TyConvT E n Γ₀ (.sort l) P) :
    False :=
  F8EtaK.separationAt_of_sortUniq hW (su hW) v.wf
    (v.σ.apply_sort .zero ▸
      v.σ.hasTyT (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) hP)
    (v.σ.apply_sort l ▸
      v.σ.tyConvT (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) hc)

/-- endpoint typings transport to the target: `convT_endpoints` applied to
    the transported conversion. -/
theorem CtxWfViaS.endpoints (hW : EnvWfT E) {Γ₀ : LCtx} (v : CtxWfViaS E n Γ₀)
    {a b T : Expr Nat} (c : ConvT E n Γ₀ a b T) :
    Nonempty (HasTyT E n v.target (v.σ.apply a) (v.σ.apply T)) ∧
      Nonempty (HasTyT E n v.target (v.σ.apply b) (v.σ.apply T)) :=
  convT_endpoints hW v.wf
    (v.σ.convT (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW) c)

/-! ### §4 D1 re-proved under `ViaS`

Same construction as `structPiJoinVia` (which is `structPiJoin` under `Via`):
the four premise sites are `v.sortUnique`/`v.ext`/`v.endpoints` over the stack,
with `v.σ.apply`/`v.σ.apply_sort`/`v.σ.hasTyT` in place of `v.ρ.map`/
`v.ρ.map_sort`/`v.ρ.hasTy`. -/

/-- `structPi p₁ × structPi p₂` under `ViaS`: the forward closing step
    `Π A₁ B₁ ⇒ Π A₂ B₂`. -/
def structPiJoinViaS (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfViaS E n Γ) {A B A₁ B₁ A₂ B₂ T : Expr Nat}
    (p₁ : StructPiPayload R Γ A B A₁ B₁ T)
    (p₂ : StructPiPayload R Γ A B A₂ B₂ T) :
    StructPiPayload R Γ A₁ B₁ A₂ B₂ T :=
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  -- levels of the two inputs agree on the shared source
  have hu : eqN p₁.u p₂.u :=
    v.sortUnique hW su (p₁.hA.val hcl hinst) (p₂.hA.val hcl hinst)
  let vA : CtxWfViaS E n (.assumption A :: Γ) :=
    v.ext hcl hinst (p₁.hA.val hcl hinst)
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
    have hA₁' : HasTyT E n v.target (v.σ.apply A₁) (.sort p₁.u) :=
      v.σ.apply_sort _ ▸ hA₁
    have hinv : HasTyT E n v.target (v.σ.apply A₁) (.sort inv.u) :=
      v.σ.apply_sort _ ▸ v.σ.hasTyT hcl hinst (inv.hA.val hcl hinst)
    exact eqN_trans' (su hW v.wf hinv hA₁') hu
  let vA₁ : CtxWfViaS E n (.assumption A₁ :: Γ) :=
    v.ext hcl hinst (inv.hA.val hcl hinst)
  have hv' : eqN inv.v p₂.v := by
    obtain ⟨⟨hB₁⟩, _⟩ := vA₁.endpoints hW (hcB.val hcl hinst)
    have hB₁' : HasTyT E n vA₁.target (vA₁.σ.apply B₁) (.sort p₂.v) :=
      vA₁.σ.apply_sort _ ▸ hB₁
    have hinv : HasTyT E n vA₁.target (vA₁.σ.apply B₁) (.sort inv.v) :=
      vA₁.σ.apply_sort _ ▸ vA₁.σ.hasTyT hcl hinst (inv.hB.val hcl hinst)
    exact su hW vA₁.wf hinv hB₁'
  { u := p₂.u, v := p₂.v
    hA := .rety inv.hA (sortsTc inv.u p₂.u hu')
    hc := hc
    hB := .rety inv.hB (sortsTc inv.v p₂.v hv')
    hcB := hcB
    hrt := p₂.hrt
    idx := p₂.idx }

/-- on `v.toS` the ViaS construction is WK-1a's Via construction — the actions
    agree (`Wk.toCtxMorph_apply`) and only Prop arguments differ (proof
    irrelevance). -/
theorem structPiJoinViaS_ofVia (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfVia E n Γ) {A B A₁ B₁ A₂ B₂ T : Expr Nat}
    (p₁ : StructPiPayload R Γ A B A₁ B₁ T)
    (p₂ : StructPiPayload R Γ A B A₂ B₂ T) :
    structPiJoinViaS hW su v.toS p₁ p₂ = structPiJoinVia hW su v p₁ p₂ :=
  rfl

/-- on `.ofWf` the ViaS construction is the landed one. -/
theorem structPiJoinViaS_ofWf (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B A₁ B₁ A₂ B₂ T : Expr Nat}
    (p₁ : StructPiPayload R Γ A B A₁ B₁ T)
    (p₂ : StructPiPayload R Γ A B A₂ B₂ T) :
    structPiJoinViaS hW su (.ofWf hΓ) p₁ p₂ = structPiJoin hW su hΓ p₁ p₂ :=
  rfl

/-- every leaf of the closing step is `SubEq` a leaf of the two inputs —
    the same argument as `structPiJoinVia_sound`, on identical data. -/
theorem structPiJoinViaS_sound (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    {Γ : LCtx} (v : CtxWfViaS E n Γ) {A B A₁ B₁ A₂ B₂ T : Expr Nat}
    (p₁ : StructPiPayload R Γ A B A₁ B₁ T)
    (p₂ : StructPiPayload R Γ A B A₂ B₂ T) :
    ∀ ℓ ∈ (structPiJoinViaS hW su v p₁ p₂).leaves,
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
  simp only [structPiJoinViaS, StructPiPayload.leaves, cvCtxConvVar_leaves,
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

/-- the `ViaS` front twin of `dispatchVia`/`dispatchWf`: same three arms, the
    premise is a `CtxWfViaS` (unused — the base cases never inspect it). -/
def dispatchViaS (hW : EnvWfT E) (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → CtxWfViaS E n Γ →
    (h : ConvT E n Γ a b T) → (∃ r ∈ R, SubEq (Jd.cv h) r) →
    Option (Result hW R h)
  | _, _, _, _, _, .refl _ _ _ ha, hsub => some (reflResult hW ha hsub)
  | _, _, _, _, _, .irr _ _ _ _ hP hp hq, hsub =>
      some (irrResult hW hP hp hq hsub)
  | _, _, _, _, _, _, _ => none

/-- on `v.toS` the twin is WK-1a's Via front. -/
theorem dispatchViaS_ofVia (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hsub : ∃ r ∈ R, SubEq (Jd.cv h) r) :
    dispatchViaS hW R v.toS h hsub = dispatchVia hW R v h hsub := by
  cases h <;> rfl

/-- the twin accepts exactly the landed base domain. -/
theorem dispatchViaS_coverage (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfViaS E n Γ)
    (h : ConvT E n Γ a b T) (hsub : ∃ r ∈ R, SubEq (Jd.cv h) r) :
    (dispatchViaS hW R v h hsub).isSome = isBase h := by
  cases h <;> rfl

end J1

namespace JEndpoints

/-- the `ViaS` front twin of `extractVia`/`extractWf`: the premise is a
    `CtxWfViaS` (unused — `extract` is structural). -/
def extractViaS (_hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (_v : CtxWfViaS E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    Option (Packet R h) := extract h hs

/-- on `v.toS` the twin is WK-1a's Via front. -/
theorem extractViaS_ofVia (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    extractViaS hW R v.toS h hs = extractVia hW R v h hs := rfl

/-- the twin accepts exactly the landed supported domain. -/
theorem extractViaS_coverage (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfViaS E n Γ)
    (h : ConvT E n Γ a b T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    (extractViaS hW R v h hs).isSome = supported h := extract_coverage h hs

end JEndpoints

namespace J3

/-- the `ViaS` front twin of `dispatchVia`/`dispatchWf`: the same recursion,
    `v` carried where the landed front carries `hΓ`. -/
def dispatchViaS (hW : EnvWfT E) (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → CtxWfViaS E n Γ →
    (h : ConvT E n Γ a b T) → (∃ r ∈ R, SubEq (.cv h) r) →
    Option (Result hW R h)
  | _, _, _, _, _, .refl _ _ _ ha, hs => some (reflResult hW ha hs)
  | _, _, _, _, _, .irr _ _ _ _ hP hp hq, hs =>
      some (irrResult hW hP hp hq hs)
  | Γ, _, _, _, v, .symm _ a b T h, hs =>
      match dispatchViaS hW R v h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs) with
      | none => none
      | some p => some p.swap
  | Γ, _, _, _, v, .tyConv _ a b T U u h hT, hs =>
      match dispatchViaS hW R v h
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

/-- on `v.toS` the twin is WK-1a's Via front, by recursion. -/
theorem dispatchViaS_ofVia (hW : EnvWfT E) (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → (v : CtxWfVia E n Γ) →
    (h : ConvT E n Γ a b T) → (hs : ∃ r ∈ R, SubEq (.cv h) r) →
    dispatchViaS hW R v.toS h hs = dispatchVia hW R v h hs
  | _, _, _, _, _, .refl .., _ => rfl
  | _, _, _, _, _, .irr .., _ => rfl
  | Γ, _, _, _, v, .symm _ a b T h, hs => by
      simp only [dispatchViaS, dispatchVia]
      rw [dispatchViaS_ofVia hW R v h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs)]
      rfl
  | Γ, _, _, _, v, .tyConv _ a b T U u h hT, hs => by
      simp only [dispatchViaS, dispatchVia]
      rw [dispatchViaS_ofVia hW R v h
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
theorem dispatchViaS_coverage (hW : EnvWfT E) (R : List (Jd E n)) :
    {Γ : LCtx} → {a b T : Expr Nat} → (v : CtxWfViaS E n Γ) →
    (h : ConvT E n Γ a b T) → (hs : ∃ r ∈ R, SubEq (.cv h) r) →
    (dispatchViaS hW R v h hs).isSome = supported h
  | _, _, _, _, _, .refl .., _ => rfl
  | _, _, _, _, _, .irr .., _ => rfl
  | Γ, _, _, _, v, .symm _ a b T h, hs => by
      have ih := dispatchViaS_coverage hW R v h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs)
      simp only [dispatchViaS, supported]
      cases he : dispatchViaS hW R v h
        (certOfChild (y := .cv (.symm Γ a b T h)) (.head _) hs) <;>
        simpa only [he, Option.isSome] using ih
  | Γ, _, _, _, v, .tyConv _ a b T U u h hT, hs => by
      have ih := dispatchViaS_coverage hW R v h
        (certOfChild (y := .cv (.tyConv Γ a b T U u h hT)) (.head _) hs)
      simp only [dispatchViaS, supported]
      cases he : dispatchViaS hW R v h
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

/-- H-J under `ViaS`, partial: a join for a bare `ConvT` literal certified
    into `R`, where the context is well-formed only up to a `CtxMorph` stack —
    or a refusal. Sibling of `JProcViaP` / `JContractViaP`. -/
abbrev JProcViaSP (R : List (Jd E n)) : Type :=
  ∀ {Γ₀ : LCtx} {M₁ M₂ T : Expr Nat}, CtxWfViaS E n Γ₀ →
    (h : ConvT E n Γ₀ M₁ M₂ T) → (∃ r ∈ R, SubEq (.cv h) r) →
    Option (Valley R Γ₀ M₁ M₂ T)

/-- the strict leaf contract on `ViaS`-front answers — same clause as
    `JContractViaP`. -/
def JContractViaSP (J : ∀ R : List (Jd E n), JProcViaSP R) : Prop :=
  ∀ R {Γ₀ : LCtx} {M₁ M₂ T : Expr Nat} (v : CtxWfViaS E n Γ₀)
    (h : ConvT E n Γ₀ M₁ M₂ T) (hsub : ∃ r ∈ R, SubEq (.cv h) r)
    (V : Valley R Γ₀ M₁ M₂ T), J R v h hsub = some V →
    ∀ ℓ ∈ V.leaves, SubOf ℓ (.cv h)

/-- a `ViaS` supplier restricts to a `Via` supplier through `toS`. -/
def JProcViaSP.toViaP (J : ∀ R : List (Jd E n), JProcViaSP R) :
    ∀ R : List (Jd E n), JProcViaP R :=
  fun R {_ _ _ _} v h hs => J R v.toS h hs

/-- the strict clause is preserved under `toS` restriction. -/
theorem JContractViaSP.toViaP {J : ∀ R : List (Jd E n), JProcViaSP R}
    (hJ : JContractViaSP J) : JContractViaP (JProcViaSP.toViaP J) := by
  intro R Γ₀ M₁ M₂ T v h hsub V hV
  exact hJ R v.toS h hsub V hV

/-- a `ViaS` supplier restricts to a `Wf` supplier through `ofWf`. -/
def JProcViaSP.toWfP (J : ∀ R : List (Jd E n), JProcViaSP R) :
    ∀ R : List (Jd E n), JProcWfP R :=
  fun R {_ _ _ _} hΓ h hs => J R (.ofWf hΓ) h hs

/-- the strict clause is preserved under `ofWf` restriction. -/
theorem JContractViaSP.toWfP {J : ∀ R : List (Jd E n), JProcViaSP R}
    (hJ : JContractViaSP J) : JContractWfP (JProcViaSP.toWfP J) := by
  intro R Γ M₁ M₂ T hΓ h hsub V hV
  exact hJ R (.ofWf hΓ) h hsub V hV

/-- a premise-free (unconditional) partial supplier is trivially a `ViaS`
    supplier. -/
def JProcViaSP.ofUncond (J : ∀ R : List (Jd E n),
    ∀ {Γ : LCtx} {M₁ M₂ T : Expr Nat}, (h : ConvT E n Γ M₁ M₂ T) →
      (∃ r ∈ R, SubEq (.cv h) r) → Option (Valley R Γ M₁ M₂ T)) :
    ∀ R : List (Jd E n), JProcViaSP R :=
  fun R {_ _ _ _} _v h hs => J R h hs

/-- J1 as a `ViaS` supplier. -/
def j1ViaS (hW : EnvWfT E) : ∀ R : List (Jd E n), JProcViaSP R :=
  fun R {_ _ _ _} v h hs => (J1.dispatchViaS hW R v h hs).map (·.valley)

/-- J1's `ViaS` supplier satisfies the strict leaf contract. -/
theorem j1ViaS_contract (hW : EnvWfT E) :
    JContractViaSP (j1ViaS (n := n) hW) := by
  intro R Γ₀ M₁ M₂ T v h hsub V hV
  have hV' : (J1.dispatchViaS hW R v h hsub).map (·.valley) = some V := hV
  obtain ⟨r, _, rfl⟩ := Option.map_eq_some'.mp hV'
  exact r.strict

/-- J3 as a `ViaS` supplier. -/
def j3ViaS (hW : EnvWfT E) : ∀ R : List (Jd E n), JProcViaSP R :=
  fun R {_ _ _ _} v h hs => (J3.dispatchViaS hW R v h hs).map (·.valley)

/-- J3's `ViaS` supplier satisfies the strict leaf contract. -/
theorem j3ViaS_contract (hW : EnvWfT E) :
    JContractViaSP (j3ViaS (n := n) hW) := by
  intro R Γ₀ M₁ M₂ T v h hsub V hV
  have hV' : (J3.dispatchViaS hW R v h hsub).map (·.valley) = some V := hV
  obtain ⟨r, _, rfl⟩ := Option.map_eq_some'.mp hV'
  exact r.strict

/-! ### §7 teeth -/

/-- `substRemove` at a position OTHER than the `const 0` entry keeps the entry:
    below it the entries are `instDecl`-instantiated (`instantiate` fixes a
    `const`), above it they are untouched. -/
theorem hasConst0Entry_substRemove (v : Expr Nat) : (j : Nat) → (Δ Γ₁ : LCtx) →
    j ≠ Δ.length →
    HasConst0Entry (substRemove v j (Δ ++ .assumption (.const 0 []) :: Γ₁))
  | 0, [], _, hj => absurd rfl hj
  | j+1, [], Γ₁, _ => ⟨[], substRemove v j Γ₁, rfl⟩
  | 0, _ :: Δ', Γ₁, _ => ⟨Δ', Γ₁, rfl⟩
  | j+1, x :: Δ', Γ₁, hj => by
      obtain ⟨Δ₂, Γ₂, h⟩ := hasConst0Entry_substRemove v j Δ' Γ₁ (by
        intro h; exact hj (by simp [h]))
      exact ⟨instDecl j v x :: Δ₂, Γ₂, by
        show instDecl j v x :: substRemove v j (Δ' ++ _) = _
        rw [h]; rfl⟩

/-- the entry at the `const 0` position. -/
theorem getElem?_const0 (Δ Γ₁ : LCtx) :
    (Δ ++ .assumption (.const 0 []) :: Γ₁)[Δ.length]? =
      some (.assumption (.const 0 [])) := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero]

private def cl0 : EnvClosed emptyEnv := fun _ _ h => Option.noConfusion h
private def ss0 : EnvMembersSubstStable emptyEnv :=
  fun _ _ h => Option.noConfusion h

/-- no term is typed at `const 0 []` in a WELL-FORMED context under `emptyEnv`:
    regularity types the `const` at a sort, and `hasTyTInv_const` then demands
    a member. -/
theorem no_const0_typing {Γ : LCtx} (wf : CtxWfT emptyEnv 0 Γ) {e : Expr Nat}
    (h : HasTyT emptyEnv 0 Γ e (.const 0 [])) : False := by
  obtain ⟨_, _, _, hT⟩ := endpoints3_of_envWfT .empty (substLetT_of_envWfT .empty)
    (constsRightDataT_of_envWfT .empty) wf (ConvT.refl _ _ _ h)
  obtain ⟨_, hm, _, _, _⟩ := hasTyTInv_const hT rfl
  exact Option.noConfusion hm

/-- THE WK-2 TOOTH CORE: no stack from a context with a `const 0` entry reaches
    a well-formed target. `ins` and off-entry `sub`/`subLet` keep the entry; a
    `sub` AT the entry needs `hv` typed at `const 0 []` just after the removal —
    transported along the rest of the stack to the target, that typing is
    refuted there by regularity. -/
theorem const0_stack_refuted : {Γ Γ' : LCtx} → (σ : CtxMorph emptyEnv 0 Γ Γ') →
    HasConst0Entry Γ → CtxWfT emptyEnv 0 Γ' → False
  | _, _, .nil, ⟨Δ, _, hΓ⟩, wf => by
      subst hΓ
      obtain ⟨hwf⟩ := ctxWfT_drop Δ wf
      cases hwf with
      | assumption _ _ _ _ hA =>
          obtain ⟨_, hm, _, _, _⟩ := hasTyTInv_const hA rfl
          exact Option.noConfusion hm
  | _, _, .ins d c σ, h, wf =>
      const0_stack_refuted σ (hasConst0Entry_insertAt d c _ h) wf
  | _, _, @CtxMorph.sub _ _ _ _ t v j hget hv σ, ⟨Δ, Γ₁, hΓ⟩, wf => by
      rw [hΓ] at hget
      by_cases hj : j = Δ.length
      · subst hj
        rw [getElem?_const0] at hget
        have ht : t = .const 0 [] := by
          injection hget with h1
          injection h1 with h2
          exact h2.symm
        subst ht
        have hv' : HasTyT emptyEnv 0 _ (lift 0 Δ.length v) (.const 0 []) := hv
        have hT := σ.hasTyT cl0 ss0 hv'
        rw [CtxMorph.apply_const] at hT
        exact no_const0_typing wf hT
      · exact const0_stack_refuted σ
          (hΓ.symm ▸ hasConst0Entry_substRemove v j Δ Γ₁ hj) wf
  | _, _, @CtxMorph.subLet _ _ _ _ _ w j hget _ σ, ⟨Δ, Γ₁, hΓ⟩, wf => by
      rw [hΓ] at hget
      have hj : j ≠ Δ.length := by
        intro hj
        subst hj
        rw [getElem?_const0] at hget
        injection hget with h1
        exact LocalDecl.noConfusion h1
      exact const0_stack_refuted σ
        (hΓ.symm ▸ hasConst0Entry_substRemove w j Δ Γ₁ hj) wf
termination_by _ _ σ _ _ => sizeOf σ
decreasing_by all_goals (simp_wf; omega)

/-- TOOTH: `illCtx` has no `ViaS` witness either — its `const 0` entry can only
    be removed by a `sub` AT it, which needs a `const 0 []`-typed value, and no
    well-formed target admits such a typing. -/
theorem illCtx_no_viaS : ¬ Nonempty (CtxWfViaS emptyEnv 0 XTileQ1.illCtx) := by
  rintro ⟨⟨_, σ, wf⟩⟩
  exact const0_stack_refuted σ ⟨[], _, rfl⟩ wf

/-! ### the two WK-2 mutants -/

/-- MUTANT 1: the `sub` arm WITHOUT its typing premise (`subLet` not needed to
    break it). -/
inductive CtxMorphU : LCtx → LCtx → Type where
  | nil {Γ : LCtx} : CtxMorphU Γ Γ
  | sub {Γ Γ' : LCtx} {t : Expr Nat} (v : Expr Nat) (j : Nat)
      (hget : Γ[j]? = some (.assumption t))
      (σ : CtxMorphU (substRemove v j Γ) Γ') : CtxMorphU Γ Γ'
  | ins {Γ Γ' : LCtx} (d : LocalDecl) (c : Nat)
      (σ : CtxMorphU (insertAt d c Γ) Γ') : CtxMorphU Γ Γ'

/-- the premise over the untyped-substitution mutant class. -/
structure CtxWfViaSMutU (E : ResolvedEnv) (n : Nat) (Γ₀ : LCtx) where
  target : LCtx
  σ : CtxMorphU Γ₀ target
  wf : CtxWfT E n target

/-- untyped substitution removes both ill-formed entries of `illCtx` and
    reaches `[]`. -/
theorem mutantU_accepts_illCtx :
    Nonempty (CtxWfViaSMutU emptyEnv 0 XTileQ1.illCtx) :=
  ⟨⟨[], .sub (.sort .zero) 0 rfl (.sub (.sort .zero) 0 rfl .nil), .nil⟩⟩

/-- MUTANT 2: `hv` typed at the SOURCE context (before the removal) instead of
    at `substRemove v j Γ`. -/
inductive CtxMorphW (E : ResolvedEnv) (n : Nat) : LCtx → LCtx → Type where
  | nil {Γ : LCtx} : CtxMorphW E n Γ Γ
  | sub {Γ Γ' : LCtx} {t v : Expr Nat} (j : Nat)
      (hget : Γ[j]? = some (.assumption t)) (hv : HasTyT E n Γ v t)
      (σ : CtxMorphW E n (substRemove v j Γ) Γ') : CtxMorphW E n Γ Γ'
  | ins {Γ Γ' : LCtx} (d : LocalDecl) (c : Nat)
      (σ : CtxMorphW E n (insertAt d c Γ) Γ') : CtxMorphW E n Γ Γ'

/-- the premise over the source-typed-`hv` mutant class. -/
structure CtxWfViaSMutW (E : ResolvedEnv) (n : Nat) (Γ₀ : LCtx) where
  target : LCtx
  σ : CtxMorphW E n Γ₀ target
  wf : CtxWfT E n target

/-- an ill-formed source types its own garbage (`HasTyT.bvar` carries no
    `CtxWfT`): `x : const 0 []` is substituted by `x` itself, then `f` by
    `f`. -/
theorem mutantW_accepts_illCtx :
    Nonempty (CtxWfViaSMutW emptyEnv 0 XTileQ1.illCtx) :=
  ⟨⟨[], .sub (v := .bvar 0) 0 rfl (.bvar _ 0 _ rfl)
      (.sub (v := .bvar 0) 0 rfl (.bvar _ 0 _ rfl) .nil), .nil⟩⟩

/-! ### §8 non-vacuity pins -/

section Pins

/-- `[y : x, x : Sort 1]` — the inner context of a `subst0 1 (x := Sort 0)`
    link. -/
def depthCtx : LCtx := [.assumption (.bvar 0), .assumption (.sort (.succ .zero))]

/-- `[y : Sort 0]` — the outer (segment) context. -/
def depthTarget : LCtx := [.assumption (.sort .zero)]

/-- the substitution removes entry 1 and instantiates `y`'s type: rfl. -/
theorem depth_substRemove : substRemove (.sort .zero) 1 depthCtx = depthTarget :=
  rfl

/-- the outer context is well-formed. -/
def depthTargetWf : CtxWfT emptyEnv 0 depthTarget :=
  .assumption [] _ _ .nil (.sort [] .zero)

/-- `Sort 0 : Sort 1` at the outer context, lifted past `j = 1` entries (the
    lifts are `rfl`). -/
def depthHv : HasTyT emptyEnv 0 (substRemove (.sort .zero) 1 depthCtx)
    (lift 0 1 (.sort .zero)) (lift 0 1 (.sort (.succ .zero))) := .sort _ _

/-- the WK-2 witness for the inner context, from the OUTER context's
    well-formedness and `hv` alone — no `CtxWfT depthCtx` is built (this is
    what `W-X-SUBST-DEPTH` said could not be built). -/
def depthViaS : CtxWfViaS emptyEnv 0 depthCtx :=
  ⟨depthTarget, .sub (t := .sort (.succ .zero)) (v := .sort .zero) 1 rfl depthHv
    .nil, depthTargetWf⟩

/-- `y : x` at the source. -/
def depthSrcTy : HasTyT emptyEnv 0 depthCtx (.bvar 0) (.bvar 1) :=
  .bvar _ 0 _ rfl

/-- `x` (index 1) is replaced by `Sort 0` — the `sub` entry's own action. -/
theorem depthViaS_apply_x : depthViaS.σ.apply (.bvar 1) = .sort .zero := rfl

/-- `y` (index 0) is untouched. -/
theorem depthViaS_apply_y : depthViaS.σ.apply (.bvar 0) = .bvar 0 := rfl

/-- transported to the target: `y : Sort 0`. -/
def depth_transport : HasTyT emptyEnv 0 depthTarget (.bvar 0) (.sort .zero) :=
  depthViaS.σ.hasTyT cl0 ss0 depthSrcTy

/-- the K shape (`RcicF8CtxConvVar.lean:66`): `wk (.assumption A) 1 ∘ subst0 0`,
    identity action. The inner literals of K live at `A' :: Γ`; X holds
    `CtxWfT (A :: Γ)` and K's `hv : x : A'` at `A :: Γ`. The stack is
    `ins (.assumption A) 1` then `sub 0 (bvar 0)`. -/
def kShapeS {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat}
    (hΓA : CtxWfT E n (.assumption A :: Γ))
    (hv : HasTyT E n (.assumption A :: Γ) (.bvar 0) (lift 0 1 A')) :
    CtxWfViaS E n (.assumption A' :: Γ) :=
  ⟨.assumption A :: Γ,
    .ins (.assumption A) 1 (.sub (t := lift 0 1 A') (v := .bvar 0) 0 rfl
      (hasTyT_castE (lift_zero_idx 0 (lift 0 1 A')).symm hv) .nil), hΓA⟩

/-- the composite action is the identity:
    `instantiate 0 (bvar 0) (lift 1 1 e) = e`. -/
theorem kShapeS_apply {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat}
    (hΓA : CtxWfT E n (.assumption A :: Γ))
    (hv : HasTyT E n (.assumption A :: Γ) (.bvar 0) (lift 0 1 A'))
    (e : Expr Nat) :
    (kShapeS hΓA hv).σ.apply e = e :=
  Rcic.Declarative.F8EtaK.instantiate_bvar_lift_succ 0 e

/-- `depthCtx` seen through an insertion at cutoff 1 (`z : Sort 0` below `y`)
    and then the `x := Sort 0` substitution at index 2: target
    `[y : Sort 0, z : Sort 0]`. -/
def twoDecl : LocalDecl := .assumption (.sort .zero)

/-- the two-entry stack's target. -/
def twoTarget : LCtx := [.assumption (.sort .zero), .assumption (.sort .zero)]

/-- the target is well-formed. -/
def twoTargetWf : CtxWfT emptyEnv 0 twoTarget :=
  .assumption _ _ _ (.assumption _ _ _ .nil (.sort _ .zero)) (.sort _ .zero)

/-- `insertAt twoDecl 1 depthCtx = [.assumption (.bvar 1), twoDecl,
    .assumption (.sort 1)]` and `substRemove (.sort 0) 2 … = twoTarget` are
    rfl; the `hv` type `HasTyT twoTarget (lift 0 2 (.sort 0)) (lift 0 2
    (.sort 1))` reduces to `.sort`. -/
def twoViaS : CtxWfViaS emptyEnv 0 depthCtx :=
  ⟨twoTarget, .ins twoDecl 1
    (.sub (t := .sort (.succ .zero)) (v := .sort .zero) 2 rfl (.sort _ _) .nil),
    twoTargetWf⟩

/-- `x` through both entries: lifted to index 2 by the insertion, substituted
    by `Sort 0` there. -/
theorem twoViaS_apply_x : twoViaS.σ.apply (.bvar 1) = .sort .zero := rfl

/-- `y` is untouched by both entries. -/
theorem twoViaS_apply_y : twoViaS.σ.apply (.bvar 0) = .bvar 0 := rfl

/-- a literal conversion at `depthCtx`: `y ≡ y : x`. -/
private def depthRefl :
    ConvT emptyEnv 0 depthCtx (.bvar 0) (.bvar 0) (.bvar 1) :=
  .refl _ _ _ depthSrcTy

private def depthReflRoot : Jd emptyEnv 0 := .cv depthRefl
private def depthReflR : List (Jd emptyEnv 0) := [depthReflRoot]
private def depthReflSub :
    ∃ r ∈ depthReflR, SubEq (.cv depthRefl) r :=
  ⟨depthReflRoot, .head _, .inl rfl⟩

/-- `symm` of the `depthCtx` literal. -/
private def depthSymm :
    ConvT emptyEnv 0 depthCtx (.bvar 0) (.bvar 0) (.bvar 1) :=
  .symm _ _ _ _ depthRefl

private def depthSymmRoot : Jd emptyEnv 0 := .cv depthSymm
private def depthSymmR : List (Jd emptyEnv 0) := [depthSymmRoot]
private def depthSymmSub :
    ∃ r ∈ depthSymmR, SubEq (.cv depthSymm) r :=
  ⟨depthSymmRoot, .head _, .inl rfl⟩

/-- the J1 ViaS supplier answers a literal whose context is well-formed only
    through a typed substitution (`depthViaS`) — which `JProcWfP` could not
    even be asked, and WK-1a's `JProcViaP` cannot reach (no weakening maps
    `depthCtx` onto its tail). -/
theorem pin_j1ViaS_sub :
    (j1ViaS EnvWfT.empty depthReflR depthViaS depthRefl
      depthReflSub).isSome = true := rfl

/-- `symm` of the literal under the same `sub`-built premise. -/
theorem pin_j3ViaS_sub :
    (j3ViaS EnvWfT.empty depthSymmR depthViaS depthSymm
      depthSymmSub).isSome = true := rfl

/-- the J1 ViaS supplier restricted through `toS` is WK-1a's Via supplier,
    pointwise. -/
theorem pin_j1ViaS_ofVia (hW : EnvWfT E) (R : List (Jd E n))
    {Γ : LCtx} {a b T : Expr Nat} (v : CtxWfVia E n Γ) (h : ConvT E n Γ a b T)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    JProcViaSP.toViaP (j1ViaS hW) R v h hs = j1Via hW R v h hs := by
  show (J1.dispatchViaS hW R v.toS h hs).map (·.valley) =
    (J1.dispatchVia hW R v h hs).map (·.valley)
  rw [J1.dispatchViaS_ofVia]

end Pins

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.CtxMorph.apply_const
#print axioms Rcic.Declarative.F8Measure.Wk.toCtxMorph
#print axioms Rcic.Declarative.F8Measure.Wk.toCtxMorph_apply
#print axioms Rcic.Declarative.F8Measure.CtxWfViaS
#print axioms Rcic.Declarative.F8Measure.CtxWfViaS.ofWf
#print axioms Rcic.Declarative.F8Measure.CtxWfViaS.ins
#print axioms Rcic.Declarative.F8Measure.CtxWfViaS.sub
#print axioms Rcic.Declarative.F8Measure.CtxWfViaS.subLet
#print axioms Rcic.Declarative.F8Measure.CtxWfViaS.ofStack
#print axioms Rcic.Declarative.F8Measure.CtxWfVia.toS
#print axioms Rcic.Declarative.F8Measure.CtxWfVia.toS_ofWf
#print axioms Rcic.Declarative.F8Measure.CtxWfViaS.ext
#print axioms Rcic.Declarative.F8Measure.CtxWfViaS.sortUnique
#print axioms Rcic.Declarative.F8Measure.CtxWfViaS.separation
#print axioms Rcic.Declarative.F8Measure.CtxWfViaS.endpoints
#print axioms Rcic.Declarative.F8Measure.structPiJoinViaS
#print axioms Rcic.Declarative.F8Measure.structPiJoinViaS_ofVia
#print axioms Rcic.Declarative.F8Measure.structPiJoinViaS_ofWf
#print axioms Rcic.Declarative.F8Measure.structPiJoinViaS_sound
#print axioms Rcic.Declarative.F8Measure.J1.dispatchViaS
#print axioms Rcic.Declarative.F8Measure.J1.dispatchViaS_ofVia
#print axioms Rcic.Declarative.F8Measure.J1.dispatchViaS_coverage
#print axioms Rcic.Declarative.F8Measure.JEndpoints.extractViaS
#print axioms Rcic.Declarative.F8Measure.JEndpoints.extractViaS_ofVia
#print axioms Rcic.Declarative.F8Measure.JEndpoints.extractViaS_coverage
#print axioms Rcic.Declarative.F8Measure.J3.dispatchViaS
#print axioms Rcic.Declarative.F8Measure.J3.dispatchViaS_ofVia
#print axioms Rcic.Declarative.F8Measure.J3.dispatchViaS_coverage
#print axioms Rcic.Declarative.F8Measure.JProcViaSP
#print axioms Rcic.Declarative.F8Measure.JContractViaSP
#print axioms Rcic.Declarative.F8Measure.JProcViaSP.toViaP
#print axioms Rcic.Declarative.F8Measure.JContractViaSP.toViaP
#print axioms Rcic.Declarative.F8Measure.JProcViaSP.toWfP
#print axioms Rcic.Declarative.F8Measure.JContractViaSP.toWfP
#print axioms Rcic.Declarative.F8Measure.JProcViaSP.ofUncond
#print axioms Rcic.Declarative.F8Measure.j1ViaS
#print axioms Rcic.Declarative.F8Measure.j1ViaS_contract
#print axioms Rcic.Declarative.F8Measure.j3ViaS
#print axioms Rcic.Declarative.F8Measure.j3ViaS_contract
#print axioms Rcic.Declarative.F8Measure.hasConst0Entry_substRemove
#print axioms Rcic.Declarative.F8Measure.getElem?_const0
#print axioms Rcic.Declarative.F8Measure.no_const0_typing
#print axioms Rcic.Declarative.F8Measure.const0_stack_refuted
#print axioms Rcic.Declarative.F8Measure.illCtx_no_viaS
#print axioms Rcic.Declarative.F8Measure.CtxMorphU
#print axioms Rcic.Declarative.F8Measure.CtxWfViaSMutU
#print axioms Rcic.Declarative.F8Measure.mutantU_accepts_illCtx
#print axioms Rcic.Declarative.F8Measure.CtxMorphW
#print axioms Rcic.Declarative.F8Measure.CtxWfViaSMutW
#print axioms Rcic.Declarative.F8Measure.mutantW_accepts_illCtx
#print axioms Rcic.Declarative.F8Measure.depthCtx
#print axioms Rcic.Declarative.F8Measure.depthTarget
#print axioms Rcic.Declarative.F8Measure.depth_substRemove
#print axioms Rcic.Declarative.F8Measure.depthTargetWf
#print axioms Rcic.Declarative.F8Measure.depthHv
#print axioms Rcic.Declarative.F8Measure.depthViaS
#print axioms Rcic.Declarative.F8Measure.depthSrcTy
#print axioms Rcic.Declarative.F8Measure.depthViaS_apply_x
#print axioms Rcic.Declarative.F8Measure.depthViaS_apply_y
#print axioms Rcic.Declarative.F8Measure.depth_transport
#print axioms Rcic.Declarative.F8Measure.kShapeS
#print axioms Rcic.Declarative.F8Measure.kShapeS_apply
#print axioms Rcic.Declarative.F8Measure.twoDecl
#print axioms Rcic.Declarative.F8Measure.twoTarget
#print axioms Rcic.Declarative.F8Measure.twoTargetWf
#print axioms Rcic.Declarative.F8Measure.twoViaS
#print axioms Rcic.Declarative.F8Measure.twoViaS_apply_x
#print axioms Rcic.Declarative.F8Measure.twoViaS_apply_y
#print axioms Rcic.Declarative.F8Measure.pin_j1ViaS_sub
#print axioms Rcic.Declarative.F8Measure.pin_j3ViaS_sub
#print axioms Rcic.Declarative.F8Measure.pin_j1ViaS_ofVia
