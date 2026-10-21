import rcic.RcicF8DViaSSupply
import rcic.RcicF8XStructViaS

/-!
Conditional ViaS bundle above the single landed D interface (#7277).
RcicF8DViaSSupply imports RcicF8XValleyVia for its Wf front. The common
worker stays in that lower module and receives only J and context-specific
operations. This layer consumes DProcViaSP/DContractViaSP and their toWfP
adapters, with no duplicate declarations or import cycle. closure_claim=0.
-/

set_option autoImplicit false
namespace Rcic.Declarative.F8Measure
open Rcic.Syn
variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)} {Γ Γ' : LCtx}

/-- a landed Wf-front D lifts to the ViaS front only PARTIALLY:
    matching `σ = .nil` forces `target = Γ`, so it answers the empty
    stack alone and refuses any real morphism. -/
def DProcWfP.toViaSP (D : ∀ R : List (Jd E n), DProcWfP R) :
    ∀ R : List (Jd E n), DProcViaSP R :=
  fun R {_ _ _ _ _} v h₁ h₂ =>
    match v with
    | ⟨_, .nil, wf⟩ => D R wf h₁ h₂
    | _ => none

/-- the strict clause survives the partial lift: answers come only
    from the `.nil` arm. -/
theorem DContractWfP.toViaSP {D : ∀ R : List (Jd E n), DProcWfP R}
    (hD : DContractWfP D) : DContractViaSP (DProcWfP.toViaSP D) := by
  intro R Γ a b c T v h₁ h₂ r hr
  obtain ⟨target, σ, wf⟩ := v
  cases σ <;> first
    | exact Option.noConfusion hr
    | exact hD R wf h₁ h₂ r hr

/-- the `ofWf` route is answered exactly as the landed Wf front. -/
theorem DProcWfP.toViaSP_ofWf (D : ∀ R : List (Jd E n), DProcWfP R)
    {Γ : LCtx} {a b c T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h₁ : EvParStar R Γ a b T) (h₂ : EvParStar R Γ a c T) :
    DProcWfP.toViaSP D R (.ofWf hΓ) h₁ h₂ = D R hΓ h₁ h₂ := rfl

/-- the ViaS supplier bundle: same fields, J/D re-fronted on the
    `CtxWfViaS` premise. -/
structure SuppliersViaS (E : ResolvedEnv) (n : Nat) where
  K : ∀ R : List (Jd E n), CtxConvProc R
  hK : CtxConvContract K
  hsep : SepAllViaS E n
  J : ∀ R : List (Jd E n), JProcViaSP R
  hJ : JContractViaSP J
  D : ∀ R : List (Jd E n), DProcViaSP R
  hD : DContractViaSP D
  U : ∀ R : List (Jd E n), UProcP R
  hU : UContractP U
  S : ∀ R : List (Jd E n), StructPiProcP R
  hS : StructPiContractP S


/-- a Via bundle lifts to a ViaS bundle PARTIALLY: J through
    `toViaSP`'s `ins`-only lift, D through the empty-stack lift. -/
def SuppliersVia.toS (X : SuppliersVia E n) : SuppliersViaS E n where
  K := X.K
  hK := X.hK
  hsep := fun _ => X.hsep
  J := JProcViaP.toViaSP X.J
  hJ := JContractViaP.toViaSP X.hJ
  D := DProcWfP.toViaSP X.D
  hD := DContractWfP.toViaSP X.hD
  U := X.U
  hU := X.hU
  S := X.S
  hS := X.hS

/-- With explicit global separation, restrict J through `toViaP` and D
    through `toWfP`, preserving all operational answers and refusals. -/
def SuppliersViaS.toViaWithSep (X : SuppliersViaS E n) (hsep : SepAll E n) : SuppliersVia E n where
  K := X.K
  hK := X.hK
  hsep := hsep
  J := JProcViaSP.toViaP X.J
  hJ := JContractViaSP.toViaP X.hJ
  D := DProcViaSP.toWfP X.D
  hD := DContractViaSP.toWfP X.hD
  U := X.U
  hU := X.hU
  S := X.S
  hS := X.hS

theorem SuppliersVia.toS_toViaWithSep (X : SuppliersVia E n) :
    X.toS.toViaWithSep X.hsep = X := by
  have hj : JProcViaSP.toViaP (JProcViaP.toViaSP X.J) = X.J := by
    funext R Γ a b T v h hs
    rcases v with ⟨target, ρ, wf⟩
    simp only [JProcViaSP.toViaP, CtxWfVia.toS, JProcViaP.toViaSP,
      Wk.toCtxMorph_toWk?]
  have hd : DProcViaSP.toWfP (DProcWfP.toViaSP X.D) = X.D := rfl
  cases X
  dsimp only [SuppliersVia.toS, SuppliersViaS.toViaWithSep]
  simp_all only []

/-- Operations at the segment context: D forwards the stored witness only
    after checking the actual context; K/U/S and their contracts are retained. -/
def SuppliersViaS.atOps (X : SuppliersViaS E n) {Γ' : LCtx}
    (v : CtxWfViaS E n Γ') : ValleyOps E n where
  K := X.K
  hK := X.hK
  D := fun R {Γ} {_ _ _ _} h₁ h₂ =>
    if h : Γ = Γ' then X.D R (h.symm ▸ v) h₁ h₂ else none
  hD := by
    intro R Γ a b c T h₁ h₂ r hr
    dsimp only at hr
    split at hr
    · next h =>
        subst h
        exact X.hD R v h₁ h₂ r hr
    · next h => exact Option.noConfusion hr
  U := X.U
  hU := X.hU
  S := X.S
  hS := X.hS

/-- at the segment context itself `atOps`'s D is `X.D` at `v`. -/
theorem SuppliersViaS.atOps_D_eq (X : SuppliersViaS E n)
    (v : CtxWfViaS E n Γ') {a b c T : Expr Nat} (h₁ : EvParStar R Γ' a b T)
    (h₂ : EvParStar R Γ' a c T) :
    (X.atOps v).D R h₁ h₂ = X.D R v h₁ h₂ := by
  show (if h : Γ' = Γ' then X.D R (h.symm ▸ v) h₁ h₂ else none) =
    X.D R v h₁ h₂
  exact dif_pos rfl

/-- `atOps`'s D is answered only where the carried witness sits —
    elsewhere it refuses. -/
theorem SuppliersViaS.atOps_D_ne (X : SuppliersViaS E n)
    (v : CtxWfViaS E n Γ') {Γ : LCtx} (hne : Γ ≠ Γ') {a b c T : Expr Nat}
    (h₁ : EvParStar R Γ a b T) (h₂ : EvParStar R Γ a c T) :
    (X.atOps v).D R h₁ h₂ = none := by
  show (if h : Γ = Γ' then X.D R (h.symm ▸ v) h₁ h₂ else none) = none
  exact dif_neg hne

/-- Forget separation and the D interface after constructing the context view. -/
def SuppliersViaS.core (X : SuppliersViaS E n) : ViaSCore E n where
  J := X.J
  hJ := X.hJ
  atOps := X.atOps

/-- The lower adapter is exactly the high-layer partial lift, at every witness. -/
theorem SuppliersVia.core_eq_toS_core (X : SuppliersVia E n) :
    X.core = X.toS.core := rfl

/-- the lifted bundle at the `ofWf` witness is `atSeg` at `hΓ` — for
    the D field; J/U/S/K are pointwise equal already. -/
theorem SuppliersVia.toS_atOps_D (X : SuppliersVia E n)
    (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat} (h₁ : EvParStar R Γ a b T)
    (h₂ : EvParStar R Γ a c T) :
    (X.toS.atOps (.ofWf hΓ)).D R h₁ h₂ = (X.atSeg hΓ).D R h₁ h₂ := by
  rw [SuppliersViaS.atOps_D_eq, SuppliersVia.atSeg_D_eq]
  exact DProcWfP.toViaSP_ofWf X.D hΓ h₁ h₂

/-- Conditional bundle with honest refusal of every operational request. -/
def SuppliersViaS.declining (hsep : SepAllViaS E n) : SuppliersViaS E n where
  K := fun _ {_ _ _ _ _} cA e => ctxConvVar cA e
  hK := fun _ {_ _ _ _ _} cA e => ctxConvVar_contract cA e
  hsep := hsep
  J := fun _ {_ _ _ _} _ _ _ => none
  hJ := fun _ {_ _ _ _} _ _ _ _ h => nomatch h
  D := fun _ {_ _ _ _ _} _ _ _ => none
  hD := fun _ {_ _ _ _ _} _ _ _ _ h => nomatch h
  U := fun _ {_ _ _ _} _ _ => none
  hU := fun _ {_ _ _ _} _ _ _ h => nomatch h
  S := fun _ {_ _ _ _ _} _ => none
  hS := fun _ {_ _ _ _ _} _ _ h => nomatch h

def SuppliersViaS.structRunner (hW : EnvWfT E) (X : SuppliersViaS E n) : XStructRunnerViaS E n :=
  fun _ {_ _ _ _ _ _ _} v c hp ha hb =>
    ⟨xStructTcViaS hW X.K X.hK X.hsep v c hp ha hb,
      xStructTcViaS_leaves hW X.K X.hK X.hsep v c hp ha hb⟩

/-- With explicit global separation, restrict J through `toViaP` and D
    through `toWfP`, preserving all operational answers and refusals. -/
def SuppliersViaS.toVia (X : SuppliersViaS E n) (hsep : SepAll E n) : SuppliersVia E n :=
  X.toViaWithSep hsep

/-- the ViaS bundle AT a segment context: J through `.ofWf` of the
    Wf premise the `Suppliers` interface hands it; D answers only at
    `Γ'`, carrying the whole witness `v`, and refuses elsewhere; U/S/K
    as is. After forgetting separation, this is exactly the conditional worker's
    `atOps v`; global separation is an explicit compatibility premise. -/
def SuppliersViaS.atCtx (X : SuppliersViaS E n) (hsep : SepAll E n) {Γ' : LCtx}
    (v : CtxWfViaS E n Γ') : Suppliers E n where
  K := X.K
  hK := X.hK
  hsep := hsep
  J := JProcViaSP.toWfP X.J
  hJ := JContractViaSP.toWfP X.hJ
  D := fun R {Γ} {_ _ _ _} h₁ h₂ =>
    if h : Γ = Γ' then X.D R (h.symm ▸ v) h₁ h₂ else none
  hD := by
    intro R Γ a b c T h₁ h₂ r hr
    dsimp only at hr
    split at hr
    · next h =>
        subst h
        exact X.hD R v h₁ h₂ r hr
    · next h => exact Option.noConfusion hr
  U := X.U
  hU := X.hU
  S := X.S
  hS := X.hS

/-- at the segment context itself `atCtx`'s D is `X.D` at `v`. -/
theorem SuppliersViaS.atCtx_D_eq (X : SuppliersViaS E n) (hsep : SepAll E n) {Γ' : LCtx}
    (v : CtxWfViaS E n Γ') {a b c T : Expr Nat} (h₁ : EvParStar R Γ' a b T)
    (h₂ : EvParStar R Γ' a c T) :
    (X.atCtx hsep v).D R h₁ h₂ = X.D R v h₁ h₂ := by
  show (if h : Γ' = Γ' then X.D R (h.symm ▸ v) h₁ h₂ else none) =
    X.D R v h₁ h₂
  exact dif_pos rfl

/-- `atCtx`'s D is answered only where the carried witness sits —
    elsewhere it refuses. -/
theorem SuppliersViaS.atCtx_D_ne (X : SuppliersViaS E n) (hsep : SepAll E n) {Γ' : LCtx}
    (v : CtxWfViaS E n Γ') {Γ : LCtx} (hne : Γ ≠ Γ') {a b c T : Expr Nat}
    (h₁ : EvParStar R Γ a b T) (h₂ : EvParStar R Γ a c T) :
    (X.atCtx hsep v).D R h₁ h₂ = none := by
  show (if h : Γ = Γ' then X.D R (h.symm ▸ v) h₁ h₂ else none) = none
  exact dif_neg hne

/-- the lifted bundle at the `ofWf` witness is `atSeg` at `hΓ` — for
    the D field; J/U/S/K are pointwise equal already. -/
theorem SuppliersVia.toS_atCtx_D (X : SuppliersVia E n)
    (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat} (h₁ : EvParStar R Γ a b T)
    (h₂ : EvParStar R Γ a c T) :
    (X.toS.atCtx X.hsep (.ofWf hΓ)).D R h₁ h₂ = (X.atSeg hΓ).D R h₁ h₂ := by
  rw [SuppliersViaS.atCtx_D_eq, SuppliersVia.atSeg_D_eq]
  exact DProcWfP.toViaSP_ofWf X.D hΓ h₁ h₂

def SepAllViaS.svalleyCvViaS (hW : EnvWfT E) (X : SuppliersViaS E n) : {Γ₀ Γ' : LCtx} →
    {a b T : Expr Nat} → (c : EvCv R Γ₀ a b T) →
    (ρ : Wk Γ₀ Γ') → (v : CtxWfViaS E n Γ') → bCvW c = true →
    Option (SOutB R Γ' (ρ.map a) (ρ.map b) (ρ.map T) c.leaves) :=
  fun c ρ v hb => ViaSEngine.svalleyCvViaS (X.atOps v) X.J X.hJ (X.structRunner hW) c ρ v hb

def SepAllViaS.slinkValleyViaS (hW : EnvWfT E) (X : SuppliersViaS E n) : {Γ₀ Γ' : LCtx} →
    {A B : Expr Nat} → (l : EvTc R Γ₀ A B) →
    (ρ : Wk Γ₀ Γ') → (v : CtxWfViaS E n Γ') → bLinkW l = true →
    Option (Σ T : Expr Nat, SOutB R Γ' (ρ.map A) (ρ.map B) T l.leaves) :=
  fun l ρ v hb => ViaSEngine.slinkValleyViaS (X.atOps v) X.J X.hJ (X.structRunner hW) l ρ v hb

def SepAllViaS.sprefixValleyViaS (hW : EnvWfT E) (X : SuppliersViaS E n) (v : CtxWfViaS E n Γ) :
    {P M B : Expr Nat} → (l : EvTc R Γ P M) → bLinkW l = true →
    (rest : Flat R Γ M B) → rest.bPrefixW = true →
    Option (Σ T : Expr Nat, SOutB R Γ P B T (l.leaves ++ rest.leaves)) :=
  ViaSEngine.sprefixValleyViaS (X.atOps v) X.J X.hJ (X.structRunner hW) v

def SepAllViaS.xSegSViaS (hW : EnvWfT E) (X : SuppliersViaS E n) (v : CtxWfViaS E n Γ) :
    {P M : Expr Nat} → (p : Flat R Γ P M) → p.segAdmW = true →
    ∀ {A B A' B' : Expr Nat}, P = .pi A B → M = .pi A' B' →
    Option (SegOut R Γ A B A' B' p.leaves) :=
  ViaSEngine.xSegSViaS (X.atOps v) X.J X.hJ (X.structRunner hW) v

def SepAllViaS.xSegsViaS (hW : EnvWfT E) (X : SuppliersViaS E n) (v : CtxWfViaS E n Γ) :
    {P Q : Expr Nat} → (s : Segs R Γ P Q) → s.admW = true →
    ∀ {A B A' B' : Expr Nat}, P = .pi A B → Q = .pi A' B' →
    Option (SegOut R Γ A B A' B' s.leaves) :=
  ViaSEngine.xSegsViaS (X.atOps v) X.J X.hJ (X.structRunner hW) v

def SepAllViaS.xValleySViaS? (hW : EnvWfT E) (X : SuppliersViaS E n) (v : CtxWfViaS E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) :
    Option (SegOut R Γ A B A' B' c.leaves) :=
  ViaSEngine.xValleySViaS? (X.atOps v) X.J X.hJ (X.structRunner hW) v c hadm

/-- `atSeg` of the landed bundle IS `atCtx` of its lift at the `ofWf`
    witness: K/hsep/U/S identical, J pointwise (the `nil` stack
    recovers `Wk.id`), D pointwise (both conditional on `Γ = Γ'`), the
    proof fields by irrelevance. -/
theorem SuppliersVia.atSeg_eq_toS_atCtx (X : SuppliersVia E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    X.atSeg hΓ = X.toS.atCtx X.hsep (.ofWf hΓ) := by
  obtain ⟨K, hK, hsep, J, hJ, D, hD, U, hU, S, hS⟩ := X
  simp only [SuppliersVia.atSeg, SuppliersVia.toS, SuppliersViaS.atCtx]
  congr 1
  · funext R' Γ' a b c T h₁ h₂
    by_cases h : Γ' = Γ
    · subst h
      rfl
    · rw [dif_neg h, dif_neg h]

theorem svalleyCvVia_eq_toS (hW : EnvWfT E) (X : SuppliersVia E n) {Γ₀ Γ' : LCtx}
    {a b T : Expr Nat} (c : EvCv R Γ₀ a b T) (ρ : Wk Γ₀ Γ')
    (hΓ' : CtxWfT E n Γ') (hb : bCvW c = true) :
    svalleyCvVia X c ρ hΓ' hb = SepAllViaS.svalleyCvViaS hW X.toS c ρ (.ofWf hΓ') hb :=
  by
  rw [svalleyCvVia_eq, SuppliersVia.atSeg_eq_toS_atCtx]
  rfl

theorem slinkValleyVia_eq_toS (hW : EnvWfT E) (X : SuppliersVia E n) {Γ₀ Γ' : LCtx}
    {A B : Expr Nat} (l : EvTc R Γ₀ A B) (ρ : Wk Γ₀ Γ')
    (hΓ' : CtxWfT E n Γ') (hb : bLinkW l = true) :
    slinkValleyVia X l ρ hΓ' hb = SepAllViaS.slinkValleyViaS hW X.toS l ρ (.ofWf hΓ') hb :=
  by
  rw [slinkValleyVia_eq, SuppliersVia.atSeg_eq_toS_atCtx]
  rfl

theorem sprefixValleyVia_eq_toS (hW : EnvWfT E) (X : SuppliersVia E n)
    (hΓ : CtxWfT E n Γ) {P M B : Expr Nat} (l : EvTc R Γ P M)
    (hb : bLinkW l = true) (rest : Flat R Γ M B)
    (hb' : rest.bPrefixW = true) :
    sprefixValleyVia X hΓ l hb rest hb' =
      SepAllViaS.sprefixValleyViaS hW X.toS (.ofWf hΓ) l hb rest hb' := by
  rw [sprefixValleyVia_eq, SuppliersVia.atSeg_eq_toS_atCtx]
  rfl

theorem xSegSVia_eq_toS (hW : EnvWfT E) (X : SuppliersVia E n) (hΓ : CtxWfT E n Γ)
    {P M : Expr Nat} (p : Flat R Γ P M) (hadm : p.segAdmW = true)
    {A B A' B' : Expr Nat} (hP : P = .pi A B) (hM : M = .pi A' B') :
    xSegSVia X hΓ p hadm hP hM = SepAllViaS.xSegSViaS hW X.toS (.ofWf hΓ) p hadm hP hM :=
  by
  rw [xSegSVia_eq, SuppliersVia.atSeg_eq_toS_atCtx]
  rfl

theorem xSegsSVia_eq_toS (hW : EnvWfT E) (X : SuppliersVia E n) (hΓ : CtxWfT E n Γ)
    {P Q : Expr Nat} (s : Segs R Γ P Q) (hadm : s.admW = true)
    {A B A' B' : Expr Nat} (hP : P = .pi A B) (hQ : Q = .pi A' B') :
    xSegsSVia X hΓ s hadm hP hQ = SepAllViaS.xSegsViaS hW X.toS (.ofWf hΓ) s hadm hP hQ :=
  by
  rw [xSegsSVia_eq, SuppliersVia.atSeg_eq_toS_atCtx]
  rfl

theorem xValleySVia?_eq_toS (hW : EnvWfT E) (X : SuppliersVia E n) (hΓ : CtxWfT E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) :
    xValleySVia? X hΓ c hadm = SepAllViaS.xValleySViaS? hW X.toS (.ofWf hΓ) c hadm := by
  rw [xValleySVia?_eq, SuppliersVia.atSeg_eq_toS_atCtx]
  rfl

/-- `XContractWf`'s clause for every answer of the ViaS route. -/
theorem SepAllViaS.xValleySViaS_contract (hW : EnvWfT E) (X : SuppliersViaS E n)
    (v : CtxWfViaS E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) (r : SegOut R Γ A B A' B' c.leaves)
    (_ : SepAllViaS.xValleySViaS? hW X v c hadm = some r) :
    ∀ ℓ ∈ r.1.1.leaves ++ r.1.2.leaves, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  r.2.2.2.1

/-- the ViaS route's answers carry a lex-edge census — the census
    shape, `EdgeContractLex` and the measure are #7142's, unchanged. -/
theorem SepAllViaS.xValleySViaS_edges (hW : EnvWfT E) (X : SuppliersViaS E n)
    (v : CtxWfViaS E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) (r : SegOut R Γ A B A' B' c.leaves)
    (_ : SepAllViaS.xValleySViaS? hW X v c hadm = some r) (Z : List (Jd E n)) :
    EdgeContractLex (census c r Z) :=
  census_edges c r Z

theorem SepAllViaS.xSegSViaS_isSome_of_spined (hW : EnvWfT E) (X : SuppliersViaS E n)
    (v : CtxWfViaS E n Γ) {P M : Expr Nat} (l : EvTc R Γ P M)
    (hl : isLink l = true)
    (hadm : (Flat.cons l hl (Flat.nil M)).segAdmW = true)
    (hp : piSpinedTc l = true) {A B A' B' : Expr Nat}
    (hP : P = .pi A B) (hM : M = .pi A' B') :
    (SepAllViaS.xSegSViaS hW X v (Flat.cons l hl (Flat.nil M)) hadm hP hM).isSome =
      true :=
  ViaSEngine.xSegSViaS_isSome_of_spined (X.atOps v) X.J X.hJ (X.structRunner hW) v l hl hadm hp hP hM

theorem SepAllViaS.xSegsViaS_isSome_of_stratumA (hW : EnvWfT E) (X : SuppliersViaS E n)
    (v : CtxWfViaS E n Γ) : {P Q : Expr Nat} → (s : Segs R Γ P Q) →
    (hadm : s.admW = true) → s.stratumA = true →
    ∀ {A B A' B' : Expr Nat} (hP : P = .pi A B) (hQ : Q = .pi A' B'),
    (SepAllViaS.xSegsViaS hW X v s hadm hP hQ).isSome = true :=
  ViaSEngine.xSegsViaS_isSome_of_stratumA (X.atOps v) X.J X.hJ (X.structRunner hW) v

theorem SepAllViaS.xValleySViaS?_isSome_of_piSpined (hW : EnvWfT E) (X : SuppliersViaS E n)
    (v : CtxWfViaS E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hp : piSpinedTc c = true) :
    (SepAllViaS.xValleySViaS? hW X v c
      (xAdmW_of_xAdm c (xAdm_of_piSpined c hp))).isSome = true :=
  ViaSEngine.xValleySViaS?_isSome_of_piSpined (X.atOps v) X.J X.hJ (X.structRunner hW) v c hp

/-- the generalized worker on the `ofWf` witness IS the landed route —
    the full dependent option agrees, including refusal and census. -/
theorem pin_viaS_ofWf_route_toS (X : SuppliersVia emptyEnv 0) :
    SepAllViaS.xValleySViaS? EnvWfT.empty X.toS (.ofWf pinWkCtxWf) pinWkInput pin_wk_xAdmW_true =
      xValleySVia? X pinWkCtxWf pinWkInput pin_wk_xAdmW_true :=
  (xValleySVia?_eq_toS EnvWfT.empty X pinWkCtxWf pinWkInput pin_wk_xAdmW_true).symm

/-- Conditional bundle route through the single worker. -/
def SuppliersViaS.xValleyS? (X : SuppliersViaS E n) (hW : EnvWfT E)
    (v : CtxWfViaS E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hadm : xAdmW c = true) :
    Option (SegOut R Γ A B A' B' c.leaves) :=
  SepAllViaS.xValleySViaS? hW X v c hadm

/-- `XContractWf`'s clause for every answer of the bundle-level ViaS
    route. -/
theorem SuppliersViaS.xValleyS?_contract (X : SuppliersViaS E n) (hW : EnvWfT E)
    (v : CtxWfViaS E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) (r : SegOut R Γ A B A' B' c.leaves)
    (_ : X.xValleyS? hW v c hadm = some r) :
    ∀ ℓ ∈ r.1.1.leaves ++ r.1.2.leaves, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  SepAllViaS.xValleySViaS_contract hW X v c hadm r ‹_›

/-- the bundle-level route's answers carry the lex-edge census. -/
theorem SuppliersViaS.xValleyS?_edges (X : SuppliersViaS E n) (hW : EnvWfT E)
    (v : CtxWfViaS E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) (r : SegOut R Γ A B A' B' c.leaves)
    (_ : X.xValleyS? hW v c hadm = some r) (Z : List (Jd E n)) :
    EdgeContractLex (census c r Z) :=
  SepAllViaS.xValleySViaS_edges hW X v c hadm r ‹_› Z

/-- the bundle-level route on a lifted bundle at the `ofWf` witness is
    the landed route. -/
theorem SuppliersViaS.xValleyS?_toS_ofWf (X : SuppliersVia E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hadm : xAdmW c = true) :
    X.toS.xValleyS? hW (.ofWf hΓ) c hadm = xValleySVia? X hΓ c hadm :=
  (xValleySVia?_eq_toS hW X hΓ c hadm).symm

/-- swap in the landed D1 ViaS supplier (#7277's `d1ViaSP`); every
    other field is carried over. -/
def SuppliersViaS.withD1 (X : SuppliersViaS E n) (hW : EnvWfT E)
    (su : F8A2Support.SortUnique E n) : SuppliersViaS E n :=
  { X with D := d1ViaSP hW su, hD := d1ViaSP_contract hW su }

/-- at `v`, `withD1`'s conditioned D answers with `dProcViaS`. -/
theorem SuppliersViaS.withD1_atCtx_D (X : SuppliersViaS E n) (hsep : SepAll E n)
    (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) {Γ' : LCtx}
    (v : CtxWfViaS E n Γ') {a b c T : Expr Nat}
    (h₁ : EvParStar R Γ' a b T) (h₂ : EvParStar R Γ' a c T) :
    ((X.withD1 hW su).atCtx hsep v).D R h₁ h₂ =
      some (dProcViaS hW su v h₁ h₂) := by
  rw [SuppliersViaS.atCtx_D_eq]
  exact d1ViaSP_some hW su R v h₁ h₂

/-- the generalized worker on the `ofWf` witness IS the landed route —
    through the bundle-level `xValleyS?` on `X.toS`. -/
theorem pin_viaS_ofWf_route (X : SuppliersVia emptyEnv 0) :
    X.toS.xValleyS? EnvWfT.empty (.ofWf pinWkCtxWf) pinWkInput pin_wk_xAdmW_true =
      xValleySVia? X pinWkCtxWf pinWkInput pin_wk_xAdmW_true :=
  SuppliersViaS.xValleyS?_toS_ofWf X EnvWfT.empty pinWkCtxWf pinWkInput
    pin_wk_xAdmW_true

/-- The global compatibility view forgets to exactly the conditional operations. -/
theorem SuppliersViaS.atCtx_toValleyOps (X : SuppliersViaS E n)
    (hsep : SepAll E n) (v : CtxWfViaS E n Γ) :
    (X.atCtx hsep v).toValleyOps = X.atOps v := rfl

/-- D1 forwarding also works without a global separation premise. -/
theorem SuppliersViaS.withD1_atOps_D (X : SuppliersViaS E n)
    (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)
    (v : CtxWfViaS E n Γ) {a b c T : Expr Nat}
    (h₁ : EvParStar R Γ a b T) (h₂ : EvParStar R Γ a c T) :
    ((X.withD1 hW su).atOps v).D R h₁ h₂ =
      some (dProcViaS hW su v h₁ h₂) := by
  rw [SuppliersViaS.atOps_D_eq]
  exact d1ViaSP_some hW su R v h₁ h₂

/-- Both public fronts return the same complete dependent Option when a
    global separation premise is explicitly supplied. -/
theorem SuppliersViaS.xValleyS?_atCtx_eq (X : SuppliersViaS E n)
    (hW : EnvWfT E) (hsep : SepAll E n) (v : CtxWfViaS E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) :
    X.xValleyS? hW v c hadm = xValleySViaS? (X.atCtx hsep v) X.J X.hJ v c hadm := rfl

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.DProcWfP.toViaSP
#print axioms Rcic.Declarative.F8Measure.DContractWfP.toViaSP
#print axioms Rcic.Declarative.F8Measure.DProcWfP.toViaSP_ofWf
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS
#print axioms Rcic.Declarative.F8Measure.SuppliersVia.toS
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.toViaWithSep
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.atOps_D_eq
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.atOps_D_ne
#print axioms Rcic.Declarative.F8Measure.SuppliersVia.toS_atOps_D
#print axioms Rcic.Declarative.F8Measure.SepAllViaS.svalleyCvViaS
#print axioms Rcic.Declarative.F8Measure.svalleyCvVia_eq_toS
#print axioms Rcic.Declarative.F8Measure.SepAllViaS.slinkValleyViaS
#print axioms Rcic.Declarative.F8Measure.slinkValleyVia_eq_toS
#print axioms Rcic.Declarative.F8Measure.SepAllViaS.sprefixValleyViaS
#print axioms Rcic.Declarative.F8Measure.sprefixValleyVia_eq_toS
#print axioms Rcic.Declarative.F8Measure.SepAllViaS.xSegSViaS
#print axioms Rcic.Declarative.F8Measure.xSegSVia_eq_toS
#print axioms Rcic.Declarative.F8Measure.SepAllViaS.xSegsViaS
#print axioms Rcic.Declarative.F8Measure.xSegsSVia_eq_toS
#print axioms Rcic.Declarative.F8Measure.SepAllViaS.xValleySViaS?
#print axioms Rcic.Declarative.F8Measure.xValleySVia?_eq_toS
#print axioms Rcic.Declarative.F8Measure.SepAllViaS.xValleySViaS_contract
#print axioms Rcic.Declarative.F8Measure.SepAllViaS.xValleySViaS_edges
#print axioms Rcic.Declarative.F8Measure.SepAllViaS.xSegSViaS_isSome_of_spined
#print axioms Rcic.Declarative.F8Measure.SepAllViaS.xSegsViaS_isSome_of_stratumA
#print axioms Rcic.Declarative.F8Measure.SepAllViaS.xValleySViaS?_isSome_of_piSpined
#print axioms Rcic.Declarative.F8Measure.pin_viaS_ofWf_route_toS
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.core
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.atOps

#print axioms Rcic.Declarative.F8Measure.SuppliersVia.core_eq_toS_core

#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.toVia
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.atCtx
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.atCtx_D_eq
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.atCtx_D_ne
#print axioms Rcic.Declarative.F8Measure.SuppliersVia.toS_atCtx_D
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.xValleyS?
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.xValleyS?_contract
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.xValleyS?_edges
#print axioms Rcic.Declarative.F8Measure.SuppliersVia.atSeg_eq_toS_atCtx
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.xValleyS?_toS_ofWf
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.withD1
#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.withD1_atCtx_D
#print axioms Rcic.Declarative.F8Measure.pin_viaS_ofWf_route

#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.atCtx_toValleyOps

#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.withD1_atOps_D

#print axioms Rcic.Declarative.F8Measure.SuppliersViaS.xValleyS?_atCtx_eq
