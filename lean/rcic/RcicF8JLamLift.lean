import rcic.RcicF8EvParStar
import rcic.RcicF8EvInv
import rcic.RcicF8EvInvT
import rcic.RcicA2SortSupport

/-!
# `RcicF8JLamLift` — J-LAM-FIXED, the pre-#7150 slice (supply-map §4.7)

ChatGPT's `research/rcic/j-tile/JT1_OPEN_ROWS_SUPPLY_MAP.md` (#7213) assigns the
`lam` literal row its first slice: **`A' = A`, `B` an explicit sort, the actual
body Valley's two multi-step paths lifted step by step through the `λ`
congruence, centre `lam A N`**. Since #7150 (`EvTy` introduction arms) and the
D2b extended carrier have not landed, this module ships exactly the
pre-#7150 halves of the slice:

* §1 `StepFam`/`LamLiftOps` — the three operations an eventual supplier must
  provide (step/typing/index lifters under one binder), each with its exact
  leaf and size law so the lifted path's accounting is checkable independently
  of any supplier. Every operation takes the domain's FORMATION evidence
  `hA : EvTy R Γ' A' (.sort u)` first — the premise `HasTyT.lam`,
  `EvTc.piCod`, and `LamPayload.hA` (#7131) all carry. Without it the kit
  types `lam (bvar 0) (sort 0)` in the empty context; the refused contract
  is kept as `LamLiftOpsMut` with its in-tree refutation (§8).
  **The lifted step lands in the kit's producer family `F` — the slot the
  D2b/X owner's extended carrier fills (supply-map §2 EX) — never in the
  preserved old `EvPar`.** No `EvPar` constructor can produce a `lam ⇝ lam`
  step at a `pi` index (the lane-3 audit refuted exactly that promise even
  with a fully formed domain and a genuine nonidentity body step); the
  old-carrier instantiation is kept refuted in-tree as
  `lamLiftOps_evParCarrier_absurd` (§8b). `EvStarG`/`ValleyG` are the
  extended-interface star/Valley the lifted output actually lives in, with
  the authorized one-directional `EvPar → F` embedding the map requires —
  `evStarG_of_evParStar` and `evStarG_map`; there is deliberately no
  `F.Step → EvPar` direction anywhere.
* §2 `lamLiftSafeB` — the lift domain, an independent syntactic condition on
  the child's OWN star: every lazy `.wk` inside must insert strictly below the
  binder and within the child's context. A `wk` at cutoff `0` moves the `λ`'s
  domain — out of the fixed-domain slice; a past-the-end insertion has no
  binder at all.
* §3 `LamFrame`/`LamDom` — `LamFrame` is a Type-valued traversal certificate
  recording each node's binder decomposition AND (at `refl`/`tail`/`conv`,
  the nodes whose kit calls need it) that node's domain formation `hdom`.
  `LamDom` is the caller's supply spine: non-`wk` nodes reuse the ambient
  binder's formation; a `wk` node supplies the CHILD binder's formation —
  inside information the node's own data cannot recover — the formation
  carried through lazy weakening.
* §4 `mkFrame`/`liftFrame`/`evStarG_lam` — the lifter itself, landing in the
  extended star `EvStarG F` (never the preserved old `EvPar`).
* §5 `lamLeavesF`/`lamSizeF`/`lamExtrasF` and the exact leaf/size equations for
  the lifted star, plus the leaf split into child leaves and kit costs
  (including the supplied formation leaves — they are not free).
* §6 `valleyGLam` — both actual legs of a child `Valley` lifted, centre
  `lam A N`, endpoint typings through `tyLift`, output in the extended valley
  `ValleyG F`, with exact leaf/size equations.
* §7 `lamFixedB`/`LamFixedPacket`/`lamFixedExtract` — the §5.2 formation-
  evidence extractor along the ORIGINAL `ConvT.lam` introduction path: its
  domain is the syntactic condition "`.lam` node, `A' = A`, `B` an explicit
  `.sort`"; it returns the literal's own two conversion children as provenance
  literals plus the leaf-free `sort v : sort (succ v)` typing the explicit-sort
  codomain supplies directly (the λ producer's `hB`, §4.7). It never invents
  `hA`/`hPi`/`hTy` — the strict `hA` the domain call yields is the recursive
  fragment's job (§4.7), not a fabricable leaf.
* §8 mutants per §7 ("the wrong λ left Π index", the path-domain guard, the
  refused domain-free kit, and the leaf-accounting stand-in).
* §8b `lamLiftOps_evParCarrier_absurd` — the lane-3 audit's refutation landed
  in-tree: even with formed domains, the kit instantiated at the preserved
  old carrier `evParFam` is uninhabitable in EVERY root (all five `EvPar`
  constructors eliminated; `proofIndex` needs the Prop-typing/index-chain
  fields plus sort uniqueness — supplied as an explicit `SortUnique`
  hypothesis, per the circularity guard; the pins discharge it at `emptyEnv`).

What deliberately waits for #7150/D2b: a concrete `LamLiftOps` supplier (the
`StepFam`/`FamHom` instance for the extended carrier is the owner's slot —
`EvParX` plugs in as `F`), the `Result`/DirectTiles assembly, and the
materialization certificate (the lifted star's `val` is the stepwise
`ParRedT.lam` congruence once the producer lands). `closure_claim = 0`.
-/

set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.JLam

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### §0 the step-family slot and the extended carriers

Supply-map §2 (EX): the lifted λ-steps are D2b producer steps, which the map
assigns to the extended carrier — **the preserved old `EvPar` is not widened**
(never a lambda constructor added to it) and the embedding runs only
`EvPar → F`, never back. The owner's concrete `EvParX` has not landed; this
slice parameterizes over its slot shape instead of inventing names: -/

/-- a producer-step family with its accounting: the slot the owner's extended
    carrier instantiates. `Step` is the family; `leaves`/`size` are the per-step
    literal accounting; `leaves_root` is the O-M3(a) discipline — every step
    leaf is certified into the same root bundle. The kit's `stepLift` (§1)
    promises its output in `F.Step`; `EvPar` itself is one instance
    (`evParFam`), and §8b proves it is precisely the instance that cannot
    supply `stepLift`. -/
structure StepFam (R : List (Jd E n)) where
  Step : LCtx → Expr Nat → Expr Nat → Expr Nat → Type
  leaves : {Γ : LCtx} → {a b T : Expr Nat} → Step Γ a b T → List (Jd E n)
  size : {Γ : LCtx} → {a b T : Expr Nat} → Step Γ a b T → Nat
  leaves_root : ∀ {Γ : LCtx} {a b T : Expr Nat} (s : Step Γ a b T) (ℓ : Jd E n),
    ℓ ∈ leaves s → ∃ r ∈ R, SubEq ℓ r

/-- the preserved old carrier as a `StepFam` — the instance the audit's
    `∀ R, LamLiftOps R → False` control lives at (§8b). -/
def evParFam (R : List (Jd E n)) : StepFam R where
  Step := EvPar R
  leaves := EvPar.leaves
  size := EvPar.size
  leaves_root := fun s _ h => s.leaves_root _ h

/-- the projections reduce to the old carrier's own accounting — `rfl` lemmas
    so simp sets can fire through the `StepFam` projection. -/
theorem evParFam_leaves {Γ : LCtx} {a b T : Expr Nat} (s : EvPar R Γ a b T) :
    (evParFam R).leaves s = s.leaves := rfl

theorem evParFam_size {Γ : LCtx} {a b T : Expr Nat} (s : EvPar R Γ a b T) :
    (evParFam R).size s = s.size := rfl

/-- the extended star: `EvParStar`'s discipline over the producer family `F`
    — `refl`/`conv`/`wk`/`trans`/`subst0`/`substLet` unchanged, `.tail` carries
    `F.Step`. When the owner lands `EvParX` with its `leaves`/`size`/
    `leaves_root`, its `StepFam` instance makes this the map's extended
    star. -/
inductive EvStarG (R : List (Jd E n)) (F : StepFam R) :
    LCtx → Expr Nat → Expr Nat → Expr Nat → Type where
  | refl {Γ : LCtx} {a T : Expr Nat} (h : EvTy R Γ a T) : EvStarG R F Γ a a T
  | tail {Γ : LCtx} {a b c T : Expr Nat} (s : F.Step Γ a b T)
      (hs : EvStarG R F Γ b c T) : EvStarG R F Γ a c T
  | conv {Γ : LCtx} {a b T T' : Expr Nat} (hs : EvStarG R F Γ a b T)
      (c : EvTc R Γ T T') : EvStarG R F Γ a b T'
  | wk {Γ : LCtx} {a b T : Expr Nat} (d : LocalDecl) (c : Nat)
      (hs : EvStarG R F Γ a b T) :
      EvStarG R F (insertAt d c Γ) (lift c 1 a) (lift c 1 b) (lift c 1 T)
  | trans {Γ : LCtx} {a b c T : Expr Nat} (h₁ : EvStarG R F Γ a b T)
      (h₂ : EvStarG R F Γ b c T) : EvStarG R F Γ a c T
  /-- lazy assumption-substitution — `EvParStar.subst0`'s generic twin. -/
  | subst0 {Γ : LCtx} {a b T t v : Expr Nat} (j : Nat)
      (hs : EvStarG R F Γ a b T)
      (hget : Γ[j]? = some (.assumption t))
      (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
      EvStarG R F (substRemove v j Γ) (instantiate j (lift 0 j v) a)
        (instantiate j (lift 0 j v) b) (instantiate j (lift 0 j v) T)
  /-- lazy let-substitution — `EvParStar.substLet`'s generic twin. -/
  | substLet {Γ : LCtx} {a b T t w : Expr Nat} (j : Nat)
      (hs : EvStarG R F Γ a b T)
      (hget : Γ[j]? = some (.letBinding t w))
      (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) :
      EvStarG R F (substRemove w j Γ) (instantiate j (lift 0 j w) a)
        (instantiate j (lift 0 j w) b) (instantiate j (lift 0 j w) T)

/-- literal leaves, with multiplicity, in constructor order — `EvParStar.leaves`
    with the step's leaves read through `F`. -/
def EvStarG.leaves {F : StepFam R} : {Γ : LCtx} → {a b T : Expr Nat} →
    EvStarG R F Γ a b T → List (Jd E n)
  | _, _, _, _, .refl h => h.leaves
  | _, _, _, _, .tail s hs => F.leaves s ++ hs.leaves
  | _, _, _, _, .conv hs c => hs.leaves ++ c.leaves
  | _, _, _, _, .wk _ _ hs => hs.leaves
  | _, _, _, _, .trans h₁ h₂ => h₁.leaves ++ h₂.leaves
  | _, _, _, _, .subst0 _ hs _ hv => hs.leaves ++ hv.leaves
  | _, _, _, _, .substLet _ hs _ hv => hs.leaves ++ hv.leaves

/-- constructor count. -/
def EvStarG.size {F : StepFam R} : {Γ : LCtx} → {a b T : Expr Nat} →
    EvStarG R F Γ a b T → Nat
  | _, _, _, _, .refl h => 1 + h.size
  | _, _, _, _, .tail s hs => 1 + F.size s + hs.size
  | _, _, _, _, .conv hs c => 1 + hs.size + c.size
  | _, _, _, _, .wk _ _ hs => 1 + hs.size
  | _, _, _, _, .trans h₁ h₂ => 1 + h₁.size + h₂.size
  | _, _, _, _, .subst0 _ hs _ hv => 1 + hs.size + hv.size
  | _, _, _, _, .substLet _ hs _ hv => 1 + hs.size + hv.size

/-- O-M3(a) for the extended star: every leaf is certified into the bundle,
    `F.leaves_root` covering the `.tail` steps. -/
theorem EvStarG.leaves_root {F : StepFam R} : {Γ : LCtx} → {a b T : Expr Nat} →
    (hs : EvStarG R F Γ a b T) → ∀ ℓ ∈ hs.leaves, ∃ r ∈ R, SubEq ℓ r
  | _, _, _, _, .refl h => h.leaves_root
  | _, _, _, _, .tail s hs => fun ℓ hℓ => by
      simp only [EvStarG.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact F.leaves_root s ℓ hℓ
      · exact hs.leaves_root ℓ hℓ
  | _, _, _, _, .conv hs c => fun ℓ hℓ => by
      simp only [EvStarG.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact hs.leaves_root ℓ hℓ
      · exact c.leaves_root ℓ hℓ
  | _, _, _, _, .wk _ _ hs => hs.leaves_root
  | _, _, _, _, .trans h₁ h₂ => fun ℓ hℓ => by
      simp only [EvStarG.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact h₁.leaves_root ℓ hℓ
      · exact h₂.leaves_root ℓ hℓ
  | _, _, _, _, .subst0 _ hs _ hv => fun ℓ hℓ => by
      simp only [EvStarG.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact hs.leaves_root ℓ hℓ
      · exact hv.leaves_root ℓ hℓ
  | _, _, _, _, .substLet _ hs _ hv => fun ℓ hℓ => by
      simp only [EvStarG.leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact hs.leaves_root ℓ hℓ
      · exact hv.leaves_root ℓ hℓ

/-- the exact embedding of the old interface into the generic star at the old
    carrier — the first half of the map's "exact embedding of the old
    interface" requirement. -/
def evStarG_of_evParStar : {Γ : LCtx} → {a b T : Expr Nat} →
    EvParStar R Γ a b T → EvStarG R (evParFam R) Γ a b T
  | _, _, _, _, .refl h => .refl h
  | _, _, _, _, .tail s hs => .tail s (evStarG_of_evParStar hs)
  | _, _, _, _, .conv hs c => .conv (evStarG_of_evParStar hs) c
  | _, _, _, _, .wk d c hs => .wk d c (evStarG_of_evParStar hs)
  | _, _, _, _, .trans h₁ h₂ =>
      .trans (evStarG_of_evParStar h₁) (evStarG_of_evParStar h₂)
  | _, _, _, _, .subst0 j hs hget hv =>
      .subst0 j (evStarG_of_evParStar hs) hget hv
  | _, _, _, _, .substLet j hs hget hv =>
      .substLet j (evStarG_of_evParStar hs) hget hv

theorem evStarG_of_evParStar_leaves : {Γ : LCtx} → {a b T : Expr Nat} →
    (hs : EvParStar R Γ a b T) →
    (evStarG_of_evParStar hs).leaves = hs.leaves := by
  intro Γ a b T hs
  induction hs with
  | refl _ => rfl
  | tail _ _ ih =>
      simp only [evStarG_of_evParStar, EvStarG.leaves, EvParStar.leaves,
        evParFam_leaves, ih]
  | conv _ _ ih =>
      simp only [evStarG_of_evParStar, EvStarG.leaves, EvParStar.leaves, ih]
  | wk _ _ _ ih => exact ih
  | trans _ _ ih₁ ih₂ =>
      simp only [evStarG_of_evParStar, EvStarG.leaves, EvParStar.leaves,
        ih₁, ih₂]
  | subst0 _ _ _ _ ih =>
      simp only [evStarG_of_evParStar, EvStarG.leaves, EvParStar.leaves, ih]
  | substLet _ _ _ _ ih =>
      simp only [evStarG_of_evParStar, EvStarG.leaves, EvParStar.leaves, ih]

theorem evStarG_of_evParStar_size : {Γ : LCtx} → {a b T : Expr Nat} →
    (hs : EvParStar R Γ a b T) →
    (evStarG_of_evParStar hs).size = hs.size := by
  intro Γ a b T hs
  induction hs with
  | refl _ => rfl
  | tail _ _ ih =>
      simp only [evStarG_of_evParStar, EvStarG.size, EvParStar.size,
        evParFam_size, ih]
  | conv _ _ ih =>
      simp only [evStarG_of_evParStar, EvStarG.size, EvParStar.size, ih]
  | wk _ _ _ ih =>
      simp only [evStarG_of_evParStar, EvStarG.size, EvParStar.size, ih]
  | trans _ _ ih₁ ih₂ =>
      simp only [evStarG_of_evParStar, EvStarG.size, EvParStar.size,
        ih₁, ih₂]
  | subst0 _ _ _ _ ih =>
      simp only [evStarG_of_evParStar, EvStarG.size, EvParStar.size, ih]
  | substLet _ _ _ _ ih =>
      simp only [evStarG_of_evParStar, EvStarG.size, EvParStar.size, ih]

/-- a producer-family morphism preserving the accounting — the authorized
    `EvPar → F` direction the D/X owner's `EvPar → EvParX` fills. The map's
    forbidden direction is structurally absent: there is no `F.Step → EvPar`
    field anywhere in this module. -/
structure FamHom (R : List (Jd E n)) (F G : StepFam R) where
  map : {Γ : LCtx} → {a b T : Expr Nat} → F.Step Γ a b T → G.Step Γ a b T
  map_leaves : ∀ {Γ : LCtx} {a b T : Expr Nat} (s : F.Step Γ a b T),
    G.leaves (map s) = F.leaves s
  map_size : ∀ {Γ : LCtx} {a b T : Expr Nat} (s : F.Step Γ a b T),
    G.size (map s) = F.size s

/-- transport a star along a producer morphism, stepwise. -/
def evStarG_map {F G : StepFam R} (ι : FamHom R F G) :
    {Γ : LCtx} → {a b T : Expr Nat} →
    EvStarG R F Γ a b T → EvStarG R G Γ a b T
  | _, _, _, _, .refl h => .refl h
  | _, _, _, _, .tail s hs => .tail (ι.map s) (evStarG_map ι hs)
  | _, _, _, _, .conv hs c => .conv (evStarG_map ι hs) c
  | _, _, _, _, .wk d c hs => .wk d c (evStarG_map ι hs)
  | _, _, _, _, .trans h₁ h₂ => .trans (evStarG_map ι h₁) (evStarG_map ι h₂)
  | _, _, _, _, .subst0 j hs hget hv =>
      .subst0 j (evStarG_map ι hs) hget hv
  | _, _, _, _, .substLet j hs hget hv =>
      .substLet j (evStarG_map ι hs) hget hv

theorem evStarG_map_leaves {F G : StepFam R} (ι : FamHom R F G) :
    {Γ : LCtx} → {a b T : Expr Nat} → (hs : EvStarG R F Γ a b T) →
    (evStarG_map ι hs).leaves = hs.leaves := by
  intro Γ a b T hs
  induction hs with
  | refl _ => rfl
  | tail s _ ih =>
      simp only [evStarG_map, EvStarG.leaves, ι.map_leaves s, ih]
  | conv _ _ ih =>
      simp only [evStarG_map, EvStarG.leaves, ih]
  | wk _ _ _ ih => exact ih
  | trans _ _ ih₁ ih₂ =>
      simp only [evStarG_map, EvStarG.leaves, ih₁, ih₂]
  | subst0 _ _ _ _ ih =>
      simp only [evStarG_map, EvStarG.leaves, ih]
  | substLet _ _ _ _ ih =>
      simp only [evStarG_map, EvStarG.leaves, ih]

theorem evStarG_map_size {F G : StepFam R} (ι : FamHom R F G) :
    {Γ : LCtx} → {a b T : Expr Nat} → (hs : EvStarG R F Γ a b T) →
    (evStarG_map ι hs).size = hs.size := by
  intro Γ a b T hs
  induction hs with
  | refl _ => rfl
  | tail s _ ih =>
      simp only [evStarG_map, EvStarG.size, ι.map_size s, ih]
  | conv _ _ ih =>
      simp only [evStarG_map, EvStarG.size, ih]
  | wk _ _ _ ih =>
      simp only [evStarG_map, EvStarG.size, ih]
  | trans _ _ ih₁ ih₂ =>
      simp only [evStarG_map, EvStarG.size, ih₁, ih₂]
  | subst0 _ _ _ _ ih =>
      simp only [evStarG_map, EvStarG.size, ih]
  | substLet _ _ _ _ ih =>
      simp only [evStarG_map, EvStarG.size, ih]

/-- the extended valley: `Valley`'s shape over `EvStarG` — two legs at one
    index plus both endpoint typings. -/
structure ValleyG (R : List (Jd E n)) (F : StepFam R) (Γ : LCtx)
    (M₁ M₂ T : Expr Nat) where
  N : Expr Nat
  left : EvStarG R F Γ M₁ N T
  right : EvStarG R F Γ M₂ N T
  ty₁ : EvTy R Γ M₁ T
  ty₂ : EvTy R Γ M₂ T

variable {F : StepFam R} {Γ : LCtx} {M₁ M₂ T : Expr Nat}

def ValleyG.leaves (V : ValleyG R F Γ M₁ M₂ T) : List (Jd E n) :=
  V.left.leaves ++ V.right.leaves ++ V.ty₁.leaves ++ V.ty₂.leaves

theorem ValleyG.leaves_root (V : ValleyG R F Γ M₁ M₂ T) :
    ∀ ℓ ∈ V.leaves, ∃ r ∈ R, SubEq ℓ r := by
  intro ℓ hℓ
  simp only [ValleyG.leaves, List.mem_append] at hℓ
  rcases hℓ with ((hℓ | hℓ) | hℓ) | hℓ
  · exact V.left.leaves_root ℓ hℓ
  · exact V.right.leaves_root ℓ hℓ
  · exact V.ty₁.leaves_root ℓ hℓ
  · exact V.ty₂.leaves_root ℓ hℓ

/-- swapping the two legs. -/
def ValleyG.symm (V : ValleyG R F Γ M₁ M₂ T) : ValleyG R F Γ M₂ M₁ T :=
  ⟨V.N, V.right, V.left, V.ty₂, V.ty₁⟩

/-- index alignment: both legs by `conv`, both typings by `rety`. -/
def ValleyG.conv {T' : Expr Nat} (V : ValleyG R F Γ M₁ M₂ T)
    (c : EvTc R Γ T T') : ValleyG R F Γ M₁ M₂ T' :=
  ⟨V.N, .conv V.left c, .conv V.right c, .rety V.ty₁ c, .rety V.ty₂ c⟩

/-- weakening. -/
def ValleyG.wk (d : LocalDecl) (k : Nat) (V : ValleyG R F Γ M₁ M₂ T) :
    ValleyG R F (insertAt d k Γ) (lift k 1 M₁) (lift k 1 M₂) (lift k 1 T) :=
  ⟨lift k 1 V.N, .wk d k V.left, .wk d k V.right, .wk d k V.ty₁, .wk d k V.ty₂⟩

/-- the old valley embeds at the old carrier. -/
def valleyG_of_valley (V : Valley R Γ M₁ M₂ T) :
    ValleyG R (evParFam R) Γ M₁ M₂ T :=
  ⟨V.N, evStarG_of_evParStar V.left, evStarG_of_evParStar V.right, V.ty₁, V.ty₂⟩

theorem valleyG_of_valley_leaves (V : Valley R Γ M₁ M₂ T) :
    (valleyG_of_valley V).leaves = V.leaves := by
  simp only [valleyG_of_valley, ValleyG.leaves, Valley.leaves,
    evStarG_of_evParStar_leaves]

/-- transport a valley along a producer morphism. -/
def valleyG_map {F G : StepFam R} (ι : FamHom R F G)
    (V : ValleyG R F Γ M₁ M₂ T) : ValleyG R G Γ M₁ M₂ T :=
  ⟨V.N, evStarG_map ι V.left, evStarG_map ι V.right, V.ty₁, V.ty₂⟩

theorem valleyG_map_leaves {F G : StepFam R} (ι : FamHom R F G)
    (V : ValleyG R F Γ M₁ M₂ T) :
    (valleyG_map ι V).leaves = V.leaves := by
  simp only [valleyG_map, ValleyG.leaves, evStarG_map_leaves]

/-! ### §1 the lift kit -/

/-- The three binder-lift operations an eventual supplier must provide to move
    an actual child star through `λ`-congruence, each charged with its exact
    leaf and size accounting.

    EVERY operation's first argument is the domain's formation evidence
    `hA : EvTy R Γ' A' (.sort u)` — the premise `HasTyT.lam`, `EvTc.piCod`,
    and #7131's `LamPayload.hA` all carry. This is what makes the kit
    inhabitable-honestly: the λ's domain must be actually formed in the
    ambient context, never an unbound term (the audit's counterexample —
    `lam (bvar 0) (sort 0)` typed in `[]` — is §8's `lamLiftOpsMut_absurd`,
    landed in-tree). The formation evidence's own leaves and size are charged
    explicitly in the laws — supplied evidence is not free. `pre`/`post` name
    the leaves the lifted node adds before/after the child's own leaves; for
    the eventual `LamPayload`-based instance these are the domain-conversion
    leaves and the right-typing/index leaves. Nothing here assumes a supplier
    exists — but nothing unformed can be lifted either.

    `stepLift`'s output lands in the kit's producer family `F` — the §0 slot
    the D2b/X owner's extended carrier fills — never in the preserved old
    `EvPar`: no `EvPar` constructor produces a `lam ⇝ lam` step at a `pi`
    index, and that promise is refuted in-tree
    (`lamLiftOps_evParCarrier_absurd`, §8b — the lane-3 audit's
    `∀ R, LamLiftOps R → False` at `evParFam`). `tyLift`/`convLift` stay on
    `EvTy`/`EvTc`: both are inhabited by real suppliers (#7150's
    λ-introduction arm for `tyLift`; `EvTc.piCod` already landed for
    `convLift`). -/
structure LamLiftOps (R : List (Jd E n)) (F : StepFam R) where
  stepLift : {Γ' : LCtx} → {A' B' x y : Expr Nat} → {u : Level} →
    (hA : EvTy R Γ' A' (.sort u)) →
    EvPar R (.assumption A' :: Γ') x y B' →
    F.Step Γ' (.lam A' x) (.lam A' y) (.pi A' B')
  stepPre : {Γ' : LCtx} → {A' B' x y : Expr Nat} → {u : Level} →
    EvTy R Γ' A' (.sort u) →
    EvPar R (.assumption A' :: Γ') x y B' → List (Jd E n)
  stepPost : {Γ' : LCtx} → {A' B' x y : Expr Nat} → {u : Level} →
    EvTy R Γ' A' (.sort u) →
    EvPar R (.assumption A' :: Γ') x y B' → List (Jd E n)
  step_leaves : {Γ' : LCtx} → {A' B' x y : Expr Nat} → {u : Level} →
    (hA : EvTy R Γ' A' (.sort u)) →
    (s : EvPar R (.assumption A' :: Γ') x y B') →
    F.leaves (stepLift hA s) =
      stepPre hA s ++ hA.leaves ++ s.leaves ++ stepPost hA s
  stepAdd : {Γ' : LCtx} → {A' B' x y : Expr Nat} → {u : Level} →
    EvTy R Γ' A' (.sort u) →
    EvPar R (.assumption A' :: Γ') x y B' → Nat
  step_size : {Γ' : LCtx} → {A' B' x y : Expr Nat} → {u : Level} →
    (hA : EvTy R Γ' A' (.sort u)) →
    (s : EvPar R (.assumption A' :: Γ') x y B') →
    F.size (stepLift hA s) = stepAdd hA s + hA.size + s.size
  tyLift : {Γ' : LCtx} → {A' B' a : Expr Nat} → {u : Level} →
    (hA : EvTy R Γ' A' (.sort u)) →
    EvTy R (.assumption A' :: Γ') a B' →
    EvTy R Γ' (.lam A' a) (.pi A' B')
  tyPre : {Γ' : LCtx} → {A' B' a : Expr Nat} → {u : Level} →
    EvTy R Γ' A' (.sort u) →
    EvTy R (.assumption A' :: Γ') a B' → List (Jd E n)
  tyPost : {Γ' : LCtx} → {A' B' a : Expr Nat} → {u : Level} →
    EvTy R Γ' A' (.sort u) →
    EvTy R (.assumption A' :: Γ') a B' → List (Jd E n)
  ty_leaves : {Γ' : LCtx} → {A' B' a : Expr Nat} → {u : Level} →
    (hA : EvTy R Γ' A' (.sort u)) →
    (D : EvTy R (.assumption A' :: Γ') a B') →
    (tyLift hA D).leaves = tyPre hA D ++ hA.leaves ++ D.leaves ++ tyPost hA D
  tyAdd : {Γ' : LCtx} → {A' B' a : Expr Nat} → {u : Level} →
    EvTy R Γ' A' (.sort u) →
    EvTy R (.assumption A' :: Γ') a B' → Nat
  ty_size : {Γ' : LCtx} → {A' B' a : Expr Nat} → {u : Level} →
    (hA : EvTy R Γ' A' (.sort u)) →
    (D : EvTy R (.assumption A' :: Γ') a B') →
    (tyLift hA D).size = tyAdd hA D + hA.size + D.size
  convLift : {Γ' : LCtx} → {A' T T' : Expr Nat} → {u : Level} →
    (hA : EvTy R Γ' A' (.sort u)) →
    EvTc R (.assumption A' :: Γ') T T' →
    EvTc R Γ' (.pi A' T) (.pi A' T')
  convPre : {Γ' : LCtx} → {A' T T' : Expr Nat} → {u : Level} →
    EvTy R Γ' A' (.sort u) →
    EvTc R (.assumption A' :: Γ') T T' → List (Jd E n)
  convPost : {Γ' : LCtx} → {A' T T' : Expr Nat} → {u : Level} →
    EvTy R Γ' A' (.sort u) →
    EvTc R (.assumption A' :: Γ') T T' → List (Jd E n)
  conv_leaves : {Γ' : LCtx} → {A' T T' : Expr Nat} → {u : Level} →
    (hA : EvTy R Γ' A' (.sort u)) →
    (c : EvTc R (.assumption A' :: Γ') T T') →
    (convLift hA c).leaves =
      convPre hA c ++ hA.leaves ++ c.leaves ++ convPost hA c
  convAdd : {Γ' : LCtx} → {A' T T' : Expr Nat} → {u : Level} →
    EvTy R Γ' A' (.sort u) →
    EvTc R (.assumption A' :: Γ') T T' → Nat
  conv_size : {Γ' : LCtx} → {A' T T' : Expr Nat} → {u : Level} →
    (hA : EvTy R Γ' A' (.sort u)) →
    (c : EvTc R (.assumption A' :: Γ') T T') →
    (convLift hA c).size = convAdd hA c + hA.size + c.size

/-! ### §2 the lift domain and the `insertAt` inversions -/

/-- length of an inserted context. -/
theorem insertAt_len (d : LocalDecl) : (c : Nat) → (Γ : LCtx) →
    (insertAt d c Γ).length = Γ.length + 1
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | c + 1, _ :: Γ => congrArg Nat.succ (insertAt_len d c Γ)

/-- a `.wk` node at cutoff `c+1` whose result context is binder-headed comes
    from a binder-headed child context, with the components shifted by one. -/
theorem insertAt_wk_eq (d : LocalDecl) (k : Nat) {Δ' : LCtx} {A₀ : Expr Nat}
    {Γ' : LCtx} (e : Δ' = .assumption A₀ :: Γ') :
    insertAt d (k + 1) Δ' = .assumption (lift k 1 A₀) :: insertAt d k Γ' := by
  subst e; rfl

/-- the decomposition data of an `insertAt` landing strictly inside the
    binder: a Type-valued structure (so it can be consumed by `mkFrame`),
    recording the cutoff shift and the binder/context split. -/
structure InsertDecomp (d : LocalDecl) (c : Nat) (Δ' Γ : LCtx)
    (A : Expr Nat) where
  A₀ : Expr Nat
  Γ' : LCtx
  k : Nat
  c_eq : c = k + 1
  ctx_eq : Δ' = .assumption A₀ :: Γ'
  dom_eq : A = lift k 1 A₀
  res_eq : Γ = insertAt d k Γ'

/-- the converse inversion for `mkFrame`: if an insertion strictly inside the
    child context lands on a binder-headed context, the child context is
    binder-headed and the pieces decompose by one cutoff. Term-mode so the
    `mkFrame` wk arm whnf-reduces under `rfl` (the `evStarG_lam_wk`
    wrapper-level equation). -/
def insertAt_assumption_inv {d : LocalDecl} :
    (c : Nat) → (Δ' : LCtx) → {Γ : LCtx} → {A : Expr Nat} →
    insertAt d c Δ' = .assumption A :: Γ → 1 ≤ c → c ≤ Δ'.length →
    InsertDecomp d c Δ' Γ A
  | 0, _, _, _, _, hc, _ => absurd hc (Nat.not_succ_le_zero 0)
  | k + 1, [], _, _, _, _, hl => absurd hl (Nat.not_succ_le_zero k)
  | k + 1, .assumption A₀ :: Γ', _, _, h, _, _ =>
      List.noConfusion h fun eA eΓ =>
        LocalDecl.noConfusion eA fun eA' =>
          ⟨A₀, Γ', k, rfl, rfl, eA'.symm, eΓ.symm⟩
  | _ + 1, .letBinding _ _ :: _, _, _, h, _, _ =>
      List.noConfusion h fun eA _ => LocalDecl.noConfusion eA

/-- the host context of a star, exposed as data (its index is implicit, so a
    match arm cannot otherwise name it). -/
def starCtx : {Δ : LCtx} → {a b T : Expr Nat} → EvParStar R Δ a b T → LCtx
  | Δ, _, _, _, _ => Δ

/-- the lift domain, checked syntactically on the child's OWN star: every lazy
    `.wk` inside must insert strictly below the binder (`1 ≤ c`) and within the
    child's context (`c ≤ Γ₀.length`, equivalent to `c < (insertAt d c Γ₀).length`).
    A `wk` at cutoff `0` would move the λ's domain — the fixed-domain slice
    refuses it rather than producing a `lam` with the wrong domain. Lazy
    substitutions (`.subst0`/`.substLet`, W-X-SUBST S0 §5) are refused
    outright here: a substitution into the child context can consume or
    re-type the binder, and this slice does not claim them. -/
def lamLiftSafeB : {Δ : LCtx} → {a b T : Expr Nat} → EvParStar R Δ a b T → Bool
  | _, _, _, _, .refl _ => true
  | _, _, _, _, .tail _ hs => lamLiftSafeB hs
  | _, _, _, _, .conv hs _ => lamLiftSafeB hs
  | _, _, _, _, .wk _ c hs =>
      decide (1 ≤ c) && decide (c ≤ (starCtx hs).length) && lamLiftSafeB hs
  | _, _, _, _, .trans h₁ h₂ => lamLiftSafeB h₁ && lamLiftSafeB h₂
  | _, _, _, _, .subst0 .. => false
  | _, _, _, _, .substLet .. => false

theorem lamLiftSafeB_tail {Δ : LCtx} {a b c T : Expr Nat}
    {s : EvPar R Δ a b T} {hs : EvParStar R Δ b c T} :
    lamLiftSafeB (.tail s hs) = lamLiftSafeB hs := by
  simp only [lamLiftSafeB]

theorem lamLiftSafeB_conv {Δ : LCtx} {a b T T' : Expr Nat}
    {hs : EvParStar R Δ a b T} {c : EvTc R Δ T T'} :
    lamLiftSafeB (.conv hs c) = lamLiftSafeB hs := by
  simp only [lamLiftSafeB]

theorem lamLiftSafeB_trans {Δ : LCtx} {a b c T : Expr Nat}
    {h₁ : EvParStar R Δ a b T} {h₂ : EvParStar R Δ b c T}
    (ok : lamLiftSafeB (.trans h₁ h₂) = true) :
    lamLiftSafeB h₁ = true ∧ lamLiftSafeB h₂ = true := by
  cases e₁ : lamLiftSafeB h₁ <;> cases e₂ : lamLiftSafeB h₂ <;>
    simp_all [lamLiftSafeB]

/-- unpacking the `wk` clause: guards plus the child's safety. -/
theorem lamLiftSafeB_wk {d : LocalDecl} {c : Nat} {Δ' : LCtx}
    {a b T : Expr Nat} {hs : EvParStar R Δ' a b T}
    (ok : lamLiftSafeB (.wk d c hs) = true) :
    1 ≤ c ∧ c ≤ Δ'.length ∧ lamLiftSafeB hs = true := by
  simp only [lamLiftSafeB, starCtx, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨h1, h2⟩, h3⟩ := ok
  exact ⟨h1, h2, h3⟩

/-- lazy substitutions are refused at this slice — the arm is a hard `false`,
    so any safety hypothesis at a `subst0` node is empty. -/
theorem lamLiftSafeB_subst0 {Δ : LCtx} {a b T t v : Expr Nat} {j : Nat}
    {hs : EvParStar R Δ a b T} {hget : Δ[j]? = some (.assumption t)}
    {hv : EvTy R (substRemove v j Δ) (lift 0 j v) (lift 0 j t)} :
    lamLiftSafeB (.subst0 j hs hget hv) = false := rfl

theorem lamLiftSafeB_substLet {Δ : LCtx} {a b T t w : Expr Nat} {j : Nat}
    {hs : EvParStar R Δ a b T} {hget : Δ[j]? = some (.letBinding t w)}
    {hv : EvTy R (substRemove w j Δ) (lift 0 j w) (lift 0 j t)} :
    lamLiftSafeB (.substLet j hs hget hv) = false := rfl

/-! ### §3 the binder frame -/

/-- a Type-valued traversal certificate for a safe star: each node records its
    context's binder decomposition `Δ = .assumption A :: Γ`; `refl`/`tail`/
    `conv` — the nodes whose kit call needs it — also store that node's domain
    formation `hdom : EvTy R Γ A (.sort u)`; and `wk` nodes carry the child's
    decomposition `e` with the node's own decomposition fixed by
    `insertAt_wk_eq`. The lift consumes the frame, never re-inverting
    `insertAt`. -/
inductive LamFrame (R : List (Jd E n)) : {Δ : LCtx} → {a b T : Expr Nat} →
    (hs : EvParStar R Δ a b T) → (Γ : LCtx) → (A : Expr Nat) → Type where
  | refl {Δ Γ : LCtx} {A a T : Expr Nat} {u : Level}
      (hdom : EvTy R Γ A (.sort u)) (h : EvTy R Δ a T)
      (hΔ : Δ = .assumption A :: Γ) : LamFrame R (.refl h) Γ A
  | tail {Δ Γ : LCtx} {A a b c T : Expr Nat} {u : Level}
      (hdom : EvTy R Γ A (.sort u)) (s : EvPar R Δ a b T)
      {hs : EvParStar R Δ b c T} (hΔ : Δ = .assumption A :: Γ)
      (fr : LamFrame R hs Γ A) : LamFrame R (.tail s hs) Γ A
  | conv {Δ Γ : LCtx} {A a b T T' : Expr Nat} {u : Level}
      (hdom : EvTy R Γ A (.sort u)) {hs : EvParStar R Δ a b T}
      (hΔ : Δ = .assumption A :: Γ) (fr : LamFrame R hs Γ A)
      (c : EvTc R Δ T T') : LamFrame R (.conv hs c) Γ A
  | wk {Δ' Γ' : LCtx} {A₀ a b T : Expr Nat} (d : LocalDecl) (k : Nat)
      {hs' : EvParStar R Δ' a b T} (e : Δ' = .assumption A₀ :: Γ')
      (fr : LamFrame R hs' Γ' A₀) :
      LamFrame R (.wk d (k + 1) hs') (insertAt d k Γ') (lift k 1 A₀)
  | trans {Δ Γ : LCtx} {A a b c T : Expr Nat} {h₁ : EvParStar R Δ a b T}
      {h₂ : EvParStar R Δ b c T} (hΔ : Δ = .assumption A :: Γ)
      (fr₁ : LamFrame R h₁ Γ A) (fr₂ : LamFrame R h₂ Γ A) :
      LamFrame R (.trans h₁ h₂) Γ A

/-- the formation supply a safe star needs — computed from the star's shape.
    Non-`wk` nodes reuse the ambient binder's formation (no data); a `wk`
    node packages the CHILD binder's formation `hdom₀` and a proof `he` that
    the child's context really is `assumption A₀ :: Γ'` — inside information
    no parent data can recover — together with the child's residual supply.
    A function (not an inductive family) so callers never fight dependent
    elimination: matching on the star's CTOR is enough. -/
noncomputable def LamDomT : {Δ : LCtx} → {a b T : Expr Nat} →
    EvParStar R Δ a b T → Type
  | _, _, _, _, .refl _ => PUnit
  | _, _, _, _, .tail _ hs => LamDomT hs
  | _, _, _, _, .conv hs _ => LamDomT hs
  | _, _, _, _, .wk _ _ hs' =>
      Σ' (Γ' : LCtx) (A₀ : Expr Nat) (u : Level)
        (_he : starCtx hs' = .assumption A₀ :: Γ'),
        EvTy R Γ' A₀ (.sort u) × LamDomT hs'
  | _, _, _, _, .trans h₁ h₂ => LamDomT h₁ × LamDomT h₂
  -- refused by `lamLiftSafeB` before a frame can consume them: no supply.
  | _, _, _, _, .subst0 .. => PUnit
  | _, _, _, _, .substLet .. => PUnit

/-- build the frame: structural recursion on the star; the `wk` arm is the one
    place the `insertAt` inversion is needed, and the safety hypothesis
    supplies its premises. `hdom` is the current binder's formation; `dom`
    supplies the child binders `wk` descents reach. -/
noncomputable def mkFrame {Δ : LCtx} {a b T : Expr Nat} (hs : EvParStar R Δ a b T)
    {Γ : LCtx} {A : Expr Nat} (hΔ : Δ = .assumption A :: Γ)
    (ok : lamLiftSafeB hs = true) {u : Level} (hdom : EvTy R Γ A (.sort u))
    (dom : LamDomT hs) : LamFrame R hs Γ A := by
  induction hs generalizing Γ A u with
  | refl h => exact .refl hdom h hΔ
  | tail s _ ih =>
      exact .tail hdom s hΔ (ih hΔ (lamLiftSafeB_tail ▸ ok) hdom dom)
  | conv _ c ih =>
      exact .conv hdom hΔ (ih hΔ (lamLiftSafeB_conv ▸ ok) hdom dom) c
  | wk d c hs' ih =>
      obtain ⟨A₀, Γ', k, hc, hctx, hAe, hΓe⟩ :=
        insertAt_assumption_inv c _ hΔ
          (lamLiftSafeB_wk ok).1 (lamLiftSafeB_wk ok).2.1
      obtain ⟨Γ₀', A₀₀, u₀, he₀, hdom₀, ch⟩ :=
        (dom : Σ' (Γ₀' : LCtx) (A₀₀ : Expr Nat) (u₀ : Level)
          (_ : starCtx hs' = .assumption A₀₀ :: Γ₀'),
          EvTy R Γ₀' A₀₀ (.sort u₀) × LamDomT hs')
      subst hc hctx hAe hΓe
      injection he₀ with eA' eΓ'
      injection eA' with eA''
      subst eΓ'
      subst eA''
      exact .wk d k rfl (ih rfl (lamLiftSafeB_wk ok).2.2 hdom₀ ch)
  | trans _ _ ih₁ ih₂ =>
      exact .trans hΔ (ih₁ hΔ (lamLiftSafeB_trans ok).1 hdom dom.1)
        (ih₂ hΔ (lamLiftSafeB_trans ok).2 hdom dom.2)
  | subst0 j hs' hget hv _ih =>
      exact absurd ok (lamLiftSafeB_subst0 ▸ (by decide))
  | substLet j hs' hget hv _ih =>
      exact absurd ok (lamLiftSafeB_substLet ▸ (by decide))

/-! ### §4 the lift -/

/-- the per-node lift: each node's own `hΔ` casts its step/typing/index data
    into the binder context for the kit, and its stored `hdom` feeds the kit's
    formed-domain premise; `wk` nodes drop one insertion level (`lift` through
    `λ` adds one to the cutoff). -/
noncomputable def liftFrame (K : LamLiftOps R F) :
    {Δ : LCtx} → {a b T : Expr Nat} → {hs : EvParStar R Δ a b T} →
    {Γ : LCtx} → {A : Expr Nat} →
    LamFrame R hs Γ A → EvStarG R F Γ (.lam A a) (.lam A b) (.pi A T)
  | _, _, _, _, _, _, _, .refl hdom h hΔ => .refl (K.tyLift hdom (hΔ ▸ h))
  | _, _, _, _, _, _, _, .tail hdom s hΔ fr =>
      .tail (K.stepLift hdom (hΔ ▸ s)) (liftFrame K fr)
  | _, _, _, _, _, _, _, .conv hdom hΔ fr c =>
      .conv (liftFrame K fr) (K.convLift hdom (hΔ ▸ c))
  | _, _, _, _, _, _, _, .wk d k _e fr => .wk d k (liftFrame K fr)
  | _, _, _, _, _, _, _, .trans _ fr₁ fr₂ =>
      .trans (liftFrame K fr₁) (liftFrame K fr₂)

/-- per-arm equations, proved by kernel reduction: the matcher's generated
    equation lemmas collide when regenerated inside `induction` forks, so the
    simp sets below use these instead of `liftFrame` itself. -/
theorem liftFrame_rfl (K : LamLiftOps R F) {Δ Γ : LCtx} {A a T : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (h : EvTy R Δ a T)
    (hΔ : Δ = .assumption A :: Γ) :
    liftFrame K (.refl hdom h hΔ) = .refl (K.tyLift hdom (hΔ ▸ h)) := rfl

theorem liftFrame_tail' (K : LamLiftOps R F) {Δ Γ : LCtx} {A a b c T : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (s : EvPar R Δ a b T)
    {hs : EvParStar R Δ b c T}
    (hΔ : Δ = .assumption A :: Γ) (fr : LamFrame R hs Γ A) :
    liftFrame K (.tail hdom s hΔ fr) =
      .tail (K.stepLift hdom (hΔ ▸ s)) (liftFrame K fr) := rfl

theorem liftFrame_conv' (K : LamLiftOps R F) {Δ Γ : LCtx} {A a b T T' : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) {hs : EvParStar R Δ a b T}
    (hΔ : Δ = .assumption A :: Γ)
    (fr : LamFrame R hs Γ A) (c : EvTc R Δ T T') :
    liftFrame K (.conv hdom hΔ fr c) =
      .conv (liftFrame K fr) (K.convLift hdom (hΔ ▸ c)) := rfl

theorem liftFrame_wk' (K : LamLiftOps R F) {Δ' Γ' : LCtx} {A₀ a b T : Expr Nat}
    (d : LocalDecl) (k : Nat) {hs' : EvParStar R Δ' a b T}
    (e : Δ' = .assumption A₀ :: Γ') (fr : LamFrame R hs' Γ' A₀) :
    liftFrame K (.wk d k e fr) = .wk d k (liftFrame K fr) := rfl

theorem liftFrame_trans' (K : LamLiftOps R F) {Δ Γ : LCtx} {A a b c T : Expr Nat}
    {h₁ : EvParStar R Δ a b T} {h₂ : EvParStar R Δ b c T}
    (hΔ : Δ = .assumption A :: Γ) (fr₁ : LamFrame R h₁ Γ A)
    (fr₂ : LamFrame R h₂ Γ A) :
    liftFrame K (.trans hΔ fr₁ fr₂) =
      .trans (liftFrame K fr₁) (liftFrame K fr₂) := rfl

/-- the child-path lift through `λ A` congruence: a safe star under binder
    `A` over `Γ` becomes a multi-step `lam`-star at `pi A T` in `Γ` — provided
    `hdom` forms `A` in `Γ` and `dom` supplies the inner binders `wk` descents
    reach. The output lives in the extended star `EvStarG F`: the lifted steps
    are `F.Step` nodes, never the preserved old `EvPar`. -/
noncomputable def evStarG_lam (K : LamLiftOps R F) {Δ : LCtx} {a b T : Expr Nat}
    (hs : EvParStar R Δ a b T) {Γ : LCtx} {A : Expr Nat}
    (hΔ : Δ = .assumption A :: Γ) (ok : lamLiftSafeB hs = true)
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (dom : LamDomT hs) :
    EvStarG R F Γ (.lam A a) (.lam A b) (.pi A T) :=
  liftFrame K (mkFrame hs hΔ ok hdom dom)

/-- the public `wk` equation: a lazy weakening inside the binder descends one
    cutoff and re-enters at the child's OWN binder formation — the wrapper
    level, not just `liftFrame` internals. -/
theorem evStarG_lam_wk (K : LamLiftOps R F) {Γ' : LCtx} {A₀ a b T : Expr Nat}
    {d : LocalDecl} {k : Nat} {hs' : EvParStar R (.assumption A₀ :: Γ') a b T}
    (ok : lamLiftSafeB (.wk d (k + 1) hs') = true) {u u' : Level}
    (hdom : EvTy R (insertAt d k Γ') (lift k 1 A₀) (.sort u))
    (hdom₀ : EvTy R Γ' A₀ (.sort u')) (dom : LamDomT hs') :
    evStarG_lam K (.wk d (k + 1) hs') rfl ok hdom
        (⟨Γ', A₀, u', rfl, hdom₀, dom⟩ : LamDomT (.wk d (k + 1) hs')) =
      .wk d k (evStarG_lam K hs' rfl (lamLiftSafeB_wk ok).2.2 hdom₀ dom) :=
  rfl

/-! ### §5 exact leaf and size equations -/

/-- the lifted star's leaves, exactly: per-node kit costs flank the child's own
    leaves in traversal order. -/
noncomputable def lamLeavesF (K : LamLiftOps R F) :
    {Δ : LCtx} → {a b T : Expr Nat} → {hs : EvParStar R Δ a b T} →
    {Γ : LCtx} → {A : Expr Nat} →
    LamFrame R hs Γ A → List (Jd E n)
  | _, _, _, _, _, _, _, .refl hdom h hΔ =>
      K.tyPre hdom (hΔ ▸ h) ++ hdom.leaves ++ (hΔ ▸ h).leaves ++
        K.tyPost hdom (hΔ ▸ h)
  | _, _, _, _, _, _, _, .tail hdom s hΔ fr =>
      K.stepPre hdom (hΔ ▸ s) ++ hdom.leaves ++ (hΔ ▸ s).leaves ++
        K.stepPost hdom (hΔ ▸ s) ++ lamLeavesF K fr
  | _, _, _, _, _, _, _, .conv hdom hΔ fr c =>
      lamLeavesF K fr ++ (K.convPre hdom (hΔ ▸ c) ++ hdom.leaves ++
        (hΔ ▸ c).leaves ++ K.convPost hdom (hΔ ▸ c))
  | _, _, _, _, _, _, _, .wk _ _ _ fr => lamLeavesF K fr
  | _, _, _, _, _, _, _, .trans _ fr₁ fr₂ =>
      lamLeavesF K fr₁ ++ lamLeavesF K fr₂

/-- the kit costs alone — what the lift adds beyond the child's leaves,
    including the supplied formation leaves. -/
noncomputable def lamExtrasF (K : LamLiftOps R F) :
    {Δ : LCtx} → {a b T : Expr Nat} → {hs : EvParStar R Δ a b T} →
    {Γ : LCtx} → {A : Expr Nat} →
    LamFrame R hs Γ A → List (Jd E n)
  | _, _, _, _, _, _, _, .refl hdom h hΔ =>
      K.tyPre hdom (hΔ ▸ h) ++ hdom.leaves ++ K.tyPost hdom (hΔ ▸ h)
  | _, _, _, _, _, _, _, .tail hdom s hΔ fr =>
      K.stepPre hdom (hΔ ▸ s) ++ hdom.leaves ++ K.stepPost hdom (hΔ ▸ s) ++
        lamExtrasF K fr
  | _, _, _, _, _, _, _, .conv hdom hΔ fr c =>
      lamExtrasF K fr ++ (K.convPre hdom (hΔ ▸ c) ++ hdom.leaves ++
        K.convPost hdom (hΔ ▸ c))
  | _, _, _, _, _, _, _, .wk _ _ _ fr => lamExtrasF K fr
  | _, _, _, _, _, _, _, .trans _ fr₁ fr₂ =>
      lamExtrasF K fr₁ ++ lamExtrasF K fr₂

/-- the lifted star's size, exactly: constructor counts plus the kit adds and
    the formation evidence's size. -/
noncomputable def lamSizeF (K : LamLiftOps R F) :
    {Δ : LCtx} → {a b T : Expr Nat} → {hs : EvParStar R Δ a b T} →
    {Γ : LCtx} → {A : Expr Nat} →
    LamFrame R hs Γ A → Nat
  | _, _, _, _, _, _, _, .refl hdom h hΔ =>
      1 + (K.tyAdd hdom (hΔ ▸ h) + hdom.size + (hΔ ▸ h).size)
  | _, _, _, _, _, _, _, .tail hdom s hΔ fr =>
      1 + (K.stepAdd hdom (hΔ ▸ s) + hdom.size + (hΔ ▸ s).size) +
        lamSizeF K fr
  | _, _, _, _, _, _, _, .conv hdom hΔ fr c =>
      1 + lamSizeF K fr + (K.convAdd hdom (hΔ ▸ c) + hdom.size + (hΔ ▸ c).size)
  | _, _, _, _, _, _, _, .wk _ _ _ fr => 1 + lamSizeF K fr
  | _, _, _, _, _, _, _, .trans _ fr₁ fr₂ =>
      1 + lamSizeF K fr₁ + lamSizeF K fr₂

/-- per-arm equations for the leaf function (same reason as `liftFrame_*`). -/
theorem lamLeavesF_rfl (K : LamLiftOps R F) {Δ Γ : LCtx} {A a T : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (h : EvTy R Δ a T)
    (hΔ : Δ = .assumption A :: Γ) :
    lamLeavesF K (.refl hdom h hΔ) =
      K.tyPre hdom (hΔ ▸ h) ++ hdom.leaves ++ (hΔ ▸ h).leaves ++
        K.tyPost hdom (hΔ ▸ h) := rfl

theorem lamLeavesF_tail' (K : LamLiftOps R F) {Δ Γ : LCtx} {A a b c T : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (s : EvPar R Δ a b T)
    {hs : EvParStar R Δ b c T}
    (hΔ : Δ = .assumption A :: Γ) (fr : LamFrame R hs Γ A) :
    lamLeavesF K (.tail hdom s hΔ fr) =
      K.stepPre hdom (hΔ ▸ s) ++ hdom.leaves ++ (hΔ ▸ s).leaves ++
        K.stepPost hdom (hΔ ▸ s) ++ lamLeavesF K fr := rfl

theorem lamLeavesF_conv' (K : LamLiftOps R F) {Δ Γ : LCtx} {A a b T T' : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) {hs : EvParStar R Δ a b T}
    (hΔ : Δ = .assumption A :: Γ)
    (fr : LamFrame R hs Γ A) (c : EvTc R Δ T T') :
    lamLeavesF K (.conv hdom hΔ fr c) =
      lamLeavesF K fr ++ (K.convPre hdom (hΔ ▸ c) ++ hdom.leaves ++
        (hΔ ▸ c).leaves ++ K.convPost hdom (hΔ ▸ c)) := rfl

theorem lamLeavesF_wk' (K : LamLiftOps R F) {Δ' Γ' : LCtx} {A₀ a b T : Expr Nat}
    (d : LocalDecl) (k : Nat) {hs' : EvParStar R Δ' a b T}
    (e : Δ' = .assumption A₀ :: Γ') (fr : LamFrame R hs' Γ' A₀) :
    lamLeavesF K (.wk d k e fr) = lamLeavesF K fr := rfl

theorem lamLeavesF_trans' (K : LamLiftOps R F) {Δ Γ : LCtx} {A a b c T : Expr Nat}
    {h₁ : EvParStar R Δ a b T} {h₂ : EvParStar R Δ b c T}
    (hΔ : Δ = .assumption A :: Γ) (fr₁ : LamFrame R h₁ Γ A)
    (fr₂ : LamFrame R h₂ Γ A) :
    lamLeavesF K (.trans hΔ fr₁ fr₂) =
      lamLeavesF K fr₁ ++ lamLeavesF K fr₂ := rfl

/-- per-arm equations for the extras function. -/
theorem lamExtrasF_rfl (K : LamLiftOps R F) {Δ Γ : LCtx} {A a T : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (h : EvTy R Δ a T)
    (hΔ : Δ = .assumption A :: Γ) :
    lamExtrasF K (.refl hdom h hΔ) =
      K.tyPre hdom (hΔ ▸ h) ++ hdom.leaves ++ K.tyPost hdom (hΔ ▸ h) := rfl

theorem lamExtrasF_tail' (K : LamLiftOps R F) {Δ Γ : LCtx} {A a b c T : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (s : EvPar R Δ a b T)
    {hs : EvParStar R Δ b c T}
    (hΔ : Δ = .assumption A :: Γ) (fr : LamFrame R hs Γ A) :
    lamExtrasF K (.tail hdom s hΔ fr) =
      K.stepPre hdom (hΔ ▸ s) ++ hdom.leaves ++ K.stepPost hdom (hΔ ▸ s) ++
        lamExtrasF K fr := rfl

theorem lamExtrasF_conv' (K : LamLiftOps R F) {Δ Γ : LCtx} {A a b T T' : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) {hs : EvParStar R Δ a b T}
    (hΔ : Δ = .assumption A :: Γ)
    (fr : LamFrame R hs Γ A) (c : EvTc R Δ T T') :
    lamExtrasF K (.conv hdom hΔ fr c) =
      lamExtrasF K fr ++ (K.convPre hdom (hΔ ▸ c) ++ hdom.leaves ++
        K.convPost hdom (hΔ ▸ c)) := rfl

theorem lamExtrasF_wk' (K : LamLiftOps R F) {Δ' Γ' : LCtx} {A₀ a b T : Expr Nat}
    (d : LocalDecl) (k : Nat) {hs' : EvParStar R Δ' a b T}
    (e : Δ' = .assumption A₀ :: Γ') (fr : LamFrame R hs' Γ' A₀) :
    lamExtrasF K (.wk d k e fr) = lamExtrasF K fr := rfl

theorem lamExtrasF_trans' (K : LamLiftOps R F) {Δ Γ : LCtx} {A a b c T : Expr Nat}
    {h₁ : EvParStar R Δ a b T} {h₂ : EvParStar R Δ b c T}
    (hΔ : Δ = .assumption A :: Γ) (fr₁ : LamFrame R h₁ Γ A)
    (fr₂ : LamFrame R h₂ Γ A) :
    lamExtrasF K (.trans hΔ fr₁ fr₂) =
      lamExtrasF K fr₁ ++ lamExtrasF K fr₂ := rfl

/-- per-arm equations for the size function. -/
theorem lamSizeF_rfl (K : LamLiftOps R F) {Δ Γ : LCtx} {A a T : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (h : EvTy R Δ a T)
    (hΔ : Δ = .assumption A :: Γ) :
    lamSizeF K (.refl hdom h hΔ) =
      1 + (K.tyAdd hdom (hΔ ▸ h) + hdom.size + (hΔ ▸ h).size) := rfl

theorem lamSizeF_tail' (K : LamLiftOps R F) {Δ Γ : LCtx} {A a b c T : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (s : EvPar R Δ a b T)
    {hs : EvParStar R Δ b c T}
    (hΔ : Δ = .assumption A :: Γ) (fr : LamFrame R hs Γ A) :
    lamSizeF K (.tail hdom s hΔ fr) =
      1 + (K.stepAdd hdom (hΔ ▸ s) + hdom.size + (hΔ ▸ s).size) +
        lamSizeF K fr := rfl

theorem lamSizeF_conv' (K : LamLiftOps R F) {Δ Γ : LCtx} {A a b T T' : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) {hs : EvParStar R Δ a b T}
    (hΔ : Δ = .assumption A :: Γ)
    (fr : LamFrame R hs Γ A) (c : EvTc R Δ T T') :
    lamSizeF K (.conv hdom hΔ fr c) =
      1 + lamSizeF K fr +
        (K.convAdd hdom (hΔ ▸ c) + hdom.size + (hΔ ▸ c).size) := rfl

theorem lamSizeF_wk' (K : LamLiftOps R F) {Δ' Γ' : LCtx} {A₀ a b T : Expr Nat}
    (d : LocalDecl) (k : Nat) {hs' : EvParStar R Δ' a b T}
    (e : Δ' = .assumption A₀ :: Γ') (fr : LamFrame R hs' Γ' A₀) :
    lamSizeF K (.wk d k e fr) = 1 + lamSizeF K fr := rfl

theorem lamSizeF_trans' (K : LamLiftOps R F) {Δ Γ : LCtx} {A a b c T : Expr Nat}
    {h₁ : EvParStar R Δ a b T} {h₂ : EvParStar R Δ b c T}
    (hΔ : Δ = .assumption A :: Γ) (fr₁ : LamFrame R h₁ Γ A)
    (fr₂ : LamFrame R h₂ Γ A) :
    lamSizeF K (.trans hΔ fr₁ fr₂) =
      1 + lamSizeF K fr₁ + lamSizeF K fr₂ := rfl

theorem evTy_cast_leaves {Δ Δ' : LCtx} {a T : Expr Nat} (e : Δ = Δ')
    (h : EvTy R Δ a T) : (e ▸ h).leaves = h.leaves := by subst e; rfl

theorem evTy_cast_size {Δ Δ' : LCtx} {a T : Expr Nat} (e : Δ = Δ')
    (h : EvTy R Δ a T) : (e ▸ h).size = h.size := by subst e; rfl

theorem evPar_cast_leaves {Δ Δ' : LCtx} {a b T : Expr Nat} (e : Δ = Δ')
    (s : EvPar R Δ a b T) : (e ▸ s).leaves = s.leaves := by subst e; rfl

theorem evPar_cast_size {Δ Δ' : LCtx} {a b T : Expr Nat} (e : Δ = Δ')
    (s : EvPar R Δ a b T) : (e ▸ s).size = s.size := by subst e; rfl

theorem evTc_cast_leaves {Δ Δ' : LCtx} {T T' : Expr Nat} (e : Δ = Δ')
    (c : EvTc R Δ T T') : (e ▸ c).leaves = c.leaves := by subst e; rfl

theorem evTc_cast_size {Δ Δ' : LCtx} {T T' : Expr Nat} (e : Δ = Δ')
    (c : EvTc R Δ T T') : (e ▸ c).size = c.size := by subst e; rfl

/-- exact leaf equation for the lifted star. -/
theorem liftFrame_leaves (K : LamLiftOps R F) {Δ : LCtx} {a b T : Expr Nat}
    {hs : EvParStar R Δ a b T} {Γ : LCtx} {A : Expr Nat}
    (fr : LamFrame R hs Γ A) :
    (liftFrame K fr).leaves = lamLeavesF K fr := by
  induction fr with
  | refl hdom h hΔ => simp only [liftFrame_rfl, EvStarG.leaves,
      lamLeavesF_rfl, K.ty_leaves, List.append_assoc]
  | tail hdom s hΔ fr ih =>
      simp only [liftFrame_tail', EvStarG.leaves, lamLeavesF_tail',
        K.step_leaves, ih, List.append_assoc]
  | conv hdom hΔ fr c ih => simp only [liftFrame_conv', EvStarG.leaves,
      lamLeavesF_conv', K.conv_leaves, ih, List.append_assoc]
  | wk d k e fr ih =>
      simp only [liftFrame_wk', EvStarG.leaves, lamLeavesF_wk', ih]
  | trans hΔ fr₁ fr₂ ih₁ ih₂ =>
      simp only [liftFrame_trans', EvStarG.leaves, lamLeavesF_trans',
        ih₁, ih₂]

/-- exact size equation for the lifted star. -/
theorem liftFrame_size (K : LamLiftOps R F) {Δ : LCtx} {a b T : Expr Nat}
    {hs : EvParStar R Δ a b T} {Γ : LCtx} {A : Expr Nat}
    (fr : LamFrame R hs Γ A) :
    (liftFrame K fr).size = lamSizeF K fr := by
  induction fr with
  | refl hdom h hΔ => simp only [liftFrame_rfl, EvStarG.size, lamSizeF_rfl,
      K.ty_size]
  | tail hdom s hΔ fr ih =>
      simp only [liftFrame_tail', EvStarG.size, lamSizeF_tail',
        K.step_size, ih]
  | conv hdom hΔ fr c ih => simp only [liftFrame_conv', EvStarG.size,
      lamSizeF_conv', K.conv_size, ih]
  | wk d k e fr ih =>
      simp only [liftFrame_wk', EvStarG.size, lamSizeF_wk', ih]
  | trans hΔ fr₁ fr₂ ih₁ ih₂ =>
      simp only [liftFrame_trans', EvStarG.size, lamSizeF_trans',
        ih₁, ih₂]

/-- the leaf split: every lifted leaf is either a child leaf or a kit cost —
    the strictness-transfer shape `JContractWf` needs. -/
theorem lamLeavesF_sub (K : LamLiftOps R F) {Δ : LCtx} {a b T : Expr Nat}
    {hs : EvParStar R Δ a b T} {Γ : LCtx} {A : Expr Nat}
    (fr : LamFrame R hs Γ A) :
    ∀ ℓ ∈ lamLeavesF K fr, ℓ ∈ hs.leaves ++ lamExtrasF K fr := by
  induction fr with
  | refl hdom h hΔ =>
      intro ℓ hℓ
      simp only [lamLeavesF_rfl, lamExtrasF_rfl, EvParStar.leaves,
        List.mem_append, List.append_assoc] at hℓ ⊢
      rcases hℓ with h | h | h | h
      · simp_all
      · simp_all
      · rw [evTy_cast_leaves] at h; simp_all
      · simp_all
  | tail hdom s hΔ fr ih =>
      intro ℓ hℓ
      have ih' := ih ℓ
      simp only [lamLeavesF_tail', lamExtrasF_tail', EvParStar.leaves,
        List.mem_append, List.append_assoc] at hℓ ih' ⊢
      rcases hℓ with h | h | h | h | h
      · simp_all
      · simp_all
      · rw [evPar_cast_leaves] at h; simp_all
      · simp_all
      · rcases ih' h with h | h <;> simp_all
  | conv hdom hΔ fr c ih =>
      intro ℓ hℓ
      have ih' := ih ℓ
      simp only [lamLeavesF_conv', lamExtrasF_conv', EvParStar.leaves,
        List.mem_append, List.append_assoc] at hℓ ih' ⊢
      rcases hℓ with h | h | h | h | h
      · rcases ih' h with h | h <;> simp_all
      · simp_all
      · simp_all
      · rw [evTc_cast_leaves] at h; simp_all
      · simp_all
  | wk d k e fr ih =>
      intro ℓ hℓ
      have ih' := ih ℓ
      simp only [lamLeavesF_wk', lamExtrasF_wk', EvParStar.leaves,
        List.mem_append, List.append_assoc] at hℓ ih' ⊢
      rcases ih' hℓ with h | h <;> simp_all
  | trans hΔ fr₁ fr₂ ih₁ ih₂ =>
      intro ℓ hℓ
      have ih₁' := ih₁ ℓ; have ih₂' := ih₂ ℓ
      simp only [lamLeavesF_trans', lamExtrasF_trans', EvParStar.leaves,
        List.mem_append, List.append_assoc] at hℓ ih₁' ih₂' ⊢
      rcases hℓ with h | h
      · rcases ih₁' h with h | h <;> simp_all
      · rcases ih₂' h with h | h <;> simp_all

/-- the star-level exact leaf equation. -/
theorem evStarG_lam_leaves (K : LamLiftOps R F) {Δ : LCtx} {a b T : Expr Nat}
    (hs : EvParStar R Δ a b T) {Γ : LCtx} {A : Expr Nat}
    (hΔ : Δ = .assumption A :: Γ) (ok : lamLiftSafeB hs = true)
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (dom : LamDomT hs) :
    (evStarG_lam K hs hΔ ok hdom dom).leaves =
      lamLeavesF K (mkFrame hs hΔ ok hdom dom) :=
  liftFrame_leaves K _

/-- the star-level exact size equation. -/
theorem evStarG_lam_size (K : LamLiftOps R F) {Δ : LCtx} {a b T : Expr Nat}
    (hs : EvParStar R Δ a b T) {Γ : LCtx} {A : Expr Nat}
    (hΔ : Δ = .assumption A :: Γ) (ok : lamLiftSafeB hs = true)
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (dom : LamDomT hs) :
    (evStarG_lam K hs hΔ ok hdom dom).size =
      lamSizeF K (mkFrame hs hΔ ok hdom dom) :=
  liftFrame_size K _

/-- the star-level split: every output leaf is a child leaf or a kit cost
    (kit costs include the supplied formation leaves). -/
theorem evStarG_lam_sub (K : LamLiftOps R F) {Δ : LCtx} {a b T : Expr Nat}
    (hs : EvParStar R Δ a b T) {Γ : LCtx} {A : Expr Nat}
    (hΔ : Δ = .assumption A :: Γ) (ok : lamLiftSafeB hs = true)
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (dom : LamDomT hs) :
    ∀ ℓ ∈ (evStarG_lam K hs hΔ ok hdom dom).leaves,
      ℓ ∈ hs.leaves ++ lamExtrasF K (mkFrame hs hΔ ok hdom dom) := by
  intro ℓ hℓ
  rw [evStarG_lam_leaves] at hℓ
  exact lamLeavesF_sub K _ ℓ hℓ

/-! ### §6 the valley lift -/

/-- lift an actual child valley: both legs stepwise under `λ A`, centre
    `lam A N`, both endpoint typings through `tyLift`. The one ambient `hdom`
    is the domain's formation in `Γ` — it feeds both leg frames and both
    `tyLift`s; `doml`/`domr` supply the inner binders each leg's `wk` descents
    reach. Output in `ValleyG F` — the extended valley, not the old one. -/
noncomputable def valleyGLam (K : LamLiftOps R F) {Γ : LCtx} {A B M₁ M₂ : Expr Nat}
    (V : Valley R (.assumption A :: Γ) M₁ M₂ B)
    (okl : lamLiftSafeB V.left = true) (okr : lamLiftSafeB V.right = true)
    {u : Level} (hdom : EvTy R Γ A (.sort u))
    (doml : LamDomT V.left) (domr : LamDomT V.right) :
    ValleyG R F Γ (.lam A M₁) (.lam A M₂) (.pi A B) :=
  ⟨.lam A V.N, evStarG_lam K V.left rfl okl hdom doml,
    evStarG_lam K V.right rfl okr hdom domr,
    K.tyLift hdom V.ty₁, K.tyLift hdom V.ty₂⟩

/-- the lifted valley's leaves, exactly. -/
theorem valleyGLam_leaves (K : LamLiftOps R F) {Γ : LCtx} {A B M₁ M₂ : Expr Nat}
    (V : Valley R (.assumption A :: Γ) M₁ M₂ B)
    (okl : lamLiftSafeB V.left = true) (okr : lamLiftSafeB V.right = true)
    {u : Level} (hdom : EvTy R Γ A (.sort u))
    (doml : LamDomT V.left) (domr : LamDomT V.right) :
    (valleyGLam K V okl okr hdom doml domr).leaves =
      lamLeavesF K (mkFrame V.left rfl okl hdom doml) ++
        lamLeavesF K (mkFrame V.right rfl okr hdom domr) ++
        (K.tyPre hdom V.ty₁ ++ hdom.leaves ++ V.ty₁.leaves ++
          K.tyPost hdom V.ty₁) ++
        (K.tyPre hdom V.ty₂ ++ hdom.leaves ++ V.ty₂.leaves ++
          K.tyPost hdom V.ty₂) := by
  simp only [valleyGLam, ValleyG.leaves, evStarG_lam_leaves, K.ty_leaves,
    List.append_assoc]

/-- the lifted valley's leaf split. -/
theorem valleyGLam_sub (K : LamLiftOps R F) {Γ : LCtx} {A B M₁ M₂ : Expr Nat}
    (V : Valley R (.assumption A :: Γ) M₁ M₂ B)
    (okl : lamLiftSafeB V.left = true) (okr : lamLiftSafeB V.right = true)
    {u : Level} (hdom : EvTy R Γ A (.sort u))
    (doml : LamDomT V.left) (domr : LamDomT V.right) :
    ∀ ℓ ∈ (valleyGLam K V okl okr hdom doml domr).leaves,
      ℓ ∈ V.leaves ++
        (lamExtrasF K (mkFrame V.left rfl okl hdom doml) ++
          lamExtrasF K (mkFrame V.right rfl okr hdom domr) ++
          (K.tyPre hdom V.ty₁ ++ hdom.leaves ++ K.tyPost hdom V.ty₁) ++
          (K.tyPre hdom V.ty₂ ++ hdom.leaves ++ K.tyPost hdom V.ty₂)) := by
  intro ℓ hℓ
  rw [valleyGLam_leaves] at hℓ
  have hL := lamLeavesF_sub K (mkFrame V.left rfl okl hdom doml) ℓ
  have hR := lamLeavesF_sub K (mkFrame V.right rfl okr hdom domr) ℓ
  simp only [Valley.leaves, List.mem_append, List.append_assoc] at hℓ hL hR ⊢
  rcases hℓ with h | h | h | h | h | h | h | h | h | h
  · rcases hL h with h | h <;> simp_all
  · rcases hR h with h | h <;> simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all

/-! ### §7 the formation-evidence extractor along the original introduction path -/

/-- the literal-side domain of J-LAM-FIXED: a `ConvT.lam` node with `A' = A`
    syntactically and `B` an explicit `.sort`. Independent of any supplied
    evidence — the §5.2 condition. -/
def lamFixedB : {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → Bool
  | _, _, _, _, .lam _ A A' _ _ (.sort _) _ _ _ => decide (A = A')
  | _, _, _, _, _ => false

/-- the packet read off the ORIGINAL `ConvT.lam` introduction path: the
    literal's own domain/body conversion children certified into `R`, plus the
    leaf-free sort typing an explicit-sort codomain supplies directly — the λ
    producer's `hB` (§4.7). `hdom` records the fixed-domain condition. -/
structure LamFixedPacket (R : List (Jd E n)) {Γ : LCtx} {A A' b b' : Expr Nat}
    {v u : Level} (hA : ConvT E n Γ A A' (.sort u))
    (hb : ConvT E n (.assumption A :: Γ) b b' (.sort v)) (hdom : A = A') where
  dom : EvCv R Γ A A' (.sort u)
  bod : EvCv R (.assumption A :: Γ) b b' (.sort v)
  codTy : EvTy R (.assumption A :: Γ) (.sort v) (.sort (.succ v))
  dom_leaves : dom.leaves = [.cv hA]
  bod_leaves : bod.leaves = [.cv hb]
  codTy_leaves : codTy.leaves = []

/-- the extractor: `some` exactly on `lamFixedB`, carrying the literal's own
    child evidence — never a fabricated `hB`/`hPi`/`hTy`. `hsub` stays an
    argument (not a scrutinee) so the function whnf-reduces on every literal
    shape. -/
noncomputable def lamFixedExtract :
    {Γ : LCtx} → {a b T : Expr Nat} → (h : ConvT E n Γ a b T) →
    (∃ r ∈ R, SubEq (Jd.cv h) r) →
    Option (Σ' (A A' bl br : Expr Nat) (v u : Level)
      (hA : ConvT E n Γ A A' (.sort u))
      (hb : ConvT E n (.assumption A :: Γ) bl br (.sort v)) (hdom : A = A'),
      LamFixedPacket R hA hb hdom)
  | _, _, _, _, .lam _ A A' bl br (.sort v) u hA hb => fun hsub =>
      if hdom : A = A' then
        some ⟨A, A', bl, br, v, u, hA, hb, hdom,
          { dom := .lit hA (certOfChild
                (y := Jd.cv (.lam _ A A' bl br (.sort v) u hA hb))
                (.head _) hsub)
            bod := .lit hb (certOfChild
                (y := Jd.cv (.lam _ A A' bl br (.sort v) u hA hb))
                (.tail _ (.head _)) hsub)
            codTy := .sort v
            dom_leaves := rfl
            bod_leaves := rfl
            codTy_leaves := rfl }⟩
      else none
  | _, _, _, _, _ => fun _ => none

/-- the extractor succeeds exactly on the syntactic domain. -/
theorem lamFixedExtract_isSome {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) (hsub : ∃ r ∈ R, SubEq (Jd.cv h) r) :
    (lamFixedExtract h hsub).isSome = lamFixedB h := by
  cases h <;> try rfl
  case lam =>
    rename_i A A' bl br B u hA hb
    cases B <;> try rfl
    case sort v =>
      by_cases hAA : A = A' <;> simp_all [lamFixedExtract, lamFixedB]

/-- every packet leaf is a real child of the original literal — strict. -/
theorem lamFixedPacket_strict {Γ : LCtx} {A A' b b' : Expr Nat} {v u : Level}
    {hA : ConvT E n Γ A A' (.sort u)}
    {hb : ConvT E n (.assumption A :: Γ) b b' (.sort v)} {hdom : A = A'}
    (p : LamFixedPacket R hA hb hdom) :
    ∀ ℓ ∈ p.dom.leaves ++ p.bod.leaves ++ p.codTy.leaves,
      SubOf ℓ (Jd.cv (.lam Γ A A' b b' (.sort v) u hA hb)) := by
  intro ℓ hℓ
  rw [p.dom_leaves, p.bod_leaves, p.codTy_leaves] at hℓ
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    false_or] at hℓ
  rcases hℓ with rfl | rfl
  · exact .child (.head _)
  · exact .child (.tail _ (.head _))

/-! ### §8 mutants (§7: the wrong λ left Π index; the path-domain guard) -/

/-- MUTANT: drops the `wk` cutoff guards — accepts a weakening that swallows
    the binder, i.e. would move the λ's domain — and it accepts lazy
    substitutions too, while `lamLiftSafeB` refuses them outright. -/
def lamLiftSafeBMut : {Δ : LCtx} → {a b T : Expr Nat} →
    EvParStar R Δ a b T → Bool
  | _, _, _, _, .refl _ => true
  | _, _, _, _, .tail _ hs => lamLiftSafeBMut hs
  | _, _, _, _, .conv hs _ => lamLiftSafeBMut hs
  | _, _, _, _, .wk _ _ hs => lamLiftSafeBMut hs
  | _, _, _, _, .trans h₁ h₂ => lamLiftSafeBMut h₁ && lamLiftSafeBMut h₂
  | _, _, _, _, .subst0 _ hs _ _ => lamLiftSafeBMut hs
  | _, _, _, _, .substLet _ hs _ _ => lamLiftSafeBMut hs

/-- MUTANT: accepts any `.lam` literal — neither `A' = A` nor `B` an explicit
    sort is checked; the extracted "packet" then has no codTy. This is §7's
    "wrong λ left Π index" row: a body index that is not the fixed sort is
    silently accepted. -/
def lamFixedBMut : {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T → Bool
  | _, _, _, _, .lam .. => true
  | _, _, _, _, _ => false

/-- MUTANT: leaf accounting that forgets the kit's per-node costs — claims the
    lifted star's leaves are exactly the child's. -/
noncomputable def lamLeavesMutF (K : LamLiftOps R F) :
    {Δ : LCtx} → {a b T : Expr Nat} → {hs : EvParStar R Δ a b T} →
    {Γ : LCtx} → {A : Expr Nat} →
    LamFrame R hs Γ A → List (Jd E n)
  | _, _, _, _, _, _, _, .refl _ h hΔ => (hΔ ▸ h).leaves
  | _, _, _, _, _, _, _, .tail _ s hΔ fr =>
      (hΔ ▸ s).leaves ++ lamLeavesMutF K fr
  | _, _, _, _, _, _, _, .conv _ _ fr c =>
      lamLeavesMutF K fr ++ c.leaves
  | _, _, _, _, _, _, _, .wk _ _ _ fr => lamLeavesMutF K fr
  | _, _, _, _, _, _, _, .trans _ fr₁ fr₂ =>
      lamLeavesMutF K fr₁ ++ lamLeavesMutF K fr₂

/-- per-arm equation for the mutant leaf function (refl arm — the divergence
    witness below consumes it). -/
theorem lamLeavesMutF_rfl (K : LamLiftOps R F) {Δ Γ : LCtx} {A a T : Expr Nat}
    {u : Level} (hdom : EvTy R Γ A (.sort u)) (h : EvTy R Δ a T)
    (hΔ : Δ = .assumption A :: Γ) :
    lamLeavesMutF K (.refl hdom h hΔ) = (hΔ ▸ h).leaves := rfl

/-- the divergence the leaf mutant hides, as a REAL inequality: whenever the
    node's charged costs are nonempty — kit flanks plus the supplied
    formation's own leaves — the mutant's report differs from the real
    accounting's. Pins discharges `hkit` concretely with lit-rooted formation
    evidence (whose leaves are nonempty by definition). -/
theorem lamLeavesMutF_refl_diverges (K : LamLiftOps R F) {Δ Γ : LCtx}
    {A a T : Expr Nat} {u : Level} (hdom : EvTy R Γ A (.sort u))
    (h : EvTy R Δ a T) (hΔ : Δ = .assumption A :: Γ)
    (hkit : K.tyPre hdom (hΔ ▸ h) ++ hdom.leaves ++
      K.tyPost hdom (hΔ ▸ h) ≠ []) :
    lamLeavesMutF K (.refl hdom h hΔ) ≠ lamLeavesF K (.refl hdom h hΔ) := by
  intro heq
  apply hkit
  rw [lamLeavesMutF_rfl, lamLeavesF_rfl] at heq
  have hlen := congrArg List.length heq
  simp only [List.length_append] at hlen
  have hz : (K.tyPre hdom (hΔ ▸ h) ++ hdom.leaves ++
      K.tyPost hdom (hΔ ▸ h)).length = 0 := by
    simp only [List.length_append]; omega
  exact List.eq_nil_of_length_eq_zero hz

/-! ### §8b the refused contract, in-tree (audit tooth) -/

/-- MUTANT — the refused domain-free contract verbatim: the lift operations
    WITHOUT the domain-formation premise. Any body typing under
    `assumption A' :: Γ'` yields a λ/Π typing — so an unbound `bvar` can stand
    as a Π domain. This is exactly the signature the independent audit refuted;
    it is kept here with its in-tree refutation as the contract's tooth. The
    accounting fields are omitted: they are orthogonal to the unsoundness
    (`tyLift` alone is already absurd). -/
structure LamLiftOpsMut (R : List (Jd E n)) where
  stepLift : {Γ' : LCtx} → {A' B' x y : Expr Nat} →
    EvPar R (.assumption A' :: Γ') x y B' →
    EvPar R Γ' (.lam A' x) (.lam A' y) (.pi A' B')
  tyLift : {Γ' : LCtx} → {A' B' a : Expr Nat} →
    EvTy R (.assumption A' :: Γ') a B' →
    EvTy R Γ' (.lam A' a) (.pi A' B')
  convLift : {Γ' : LCtx} → {A' T T' : Expr Nat} →
    EvTc R (.assumption A' :: Γ') T T' →
    EvTc R Γ' (.pi A' T) (.pi A' T')

/-- the refused kit is uninhabitable in EVERY root: its `tyLift` types
    `lam (bvar 0) (sort 0)` at `pi (bvar 0) (sort 1)` in the EMPTY context
    (body `EvTy.sort` under the unbound `bvar 0` binder). Total `lam`-
    inversion then yields `hA : EvTy R [] (bvar 0) (sort _)`; `bvar`-inversion
    of THAT demands `lookupType [] 0 = some _`, impossible — the audit's
    `∀ R, LamLiftOps R → False` control, landed against the actual
    constructors. -/
theorem lamLiftOpsMut_absurd (K : LamLiftOpsMut R) : False := by
  have hlam : EvTy R [] (.lam (.bvar 0) (.sort .zero))
      (.pi (.bvar 0) (.sort (.succ .zero))) :=
    K.tyLift (EvTy.sort .zero)
  have s := hlam.invLamT rfl
  have sb := s.hA.invBvarT rfl
  -- sb.hlk : lookupType [] 0 = some sb.A — but lookupType [] 0 ≡ none
  exact Option.noConfusion sb.hlk

/-! ### §8c the refused OLD-CARRIER contract, in-tree (lane-3 audit tooth)

The second refusal is sharper than the domain-free one: even WITH the
domain-formation premise and a genuine nonidentity body step, `stepLift`
cannot land in the preserved old `EvPar` — none of its five constructors
produces `lam ⇝ lam` at a `pi` index. This is the lane-3 audit's
`∀ R : List (Jd emptyEnv 0), LamLiftOps R → False` control, landed against
the actual constructors and the actual inputs the audit used: `A' := sort 0`
formed by `EvTy.sort`; body step the real `EvPar.ofSorts` producer
`sort 1 ⇝ sort (max 1 0)` under `[assumption (sort 0)]` at index `sort 2`
(the committed nonidentity levels). `cases` on the promised output
auto-eliminates `structPi`/`sortEq`/`consts`/`lit` — their endpoint heads are
`pi`/`sort`/`const`/`lit`, never `lam`. The arbitrary-endpoint `proofIndex`
is eliminated through its actual fields: `chain`'s left endpoint is the fixed
`pi (sort 0) (sort 2)`, so `sort_transport` moves `propTy`'s Prop typing onto
the Pi, `pi_zero_inv` forces `sort 2 : sort 0` under the domain binder (the
audit's "codomain Sort 2 typed in Sort 0"), and `SortUnique` against the real
`sort 2 : sort 3` yields `some 3 = some 0`. `su` stays an explicit hypothesis
— the `RcicSortUniqueRows` circularity guard bars importing its supplier
into the J construction; the pins discharge it at `emptyEnv` (where
`EnvWfT.empty.InScope` is `True`), reproducing the auditor's `∀ R` verbatim. -/

/-- the repaired contract is still uninhabitable in EVERY root bundle — the
    obstruction is the carrier, not the premises. -/
theorem lamLiftOps_evParCarrier_absurd
    (su : F8A2Support.SortUnique emptyEnv 0)
    (R' : List (Jd emptyEnv 0)) (K : LamLiftOps R' (evParFam R')) : False := by
  have hcl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
  have hinst : EnvMembersSubstStable emptyEnv :=
    envMembersSubstStable_of_envWfT EnvWfT.empty
  -- the committed nonidentity levels `1 =ₙ max 1 0`, `1 ≠ max 1 0`
  -- syntactically; formation and the body producer are the audit's exact
  -- fixture.
  have hA : EvTy R' [] (.sort .zero) (.sort (.succ .zero)) := .sort .zero
  have hs : EvPar R' [.assumption (.sort .zero)]
      (.sort (.succ .zero)) (.sort (.max (.succ .zero) .zero))
      (.sort (.succ (.succ .zero))) :=
    EvPar.ofSorts _ _ _ (fun _ => rfl)
  have out : EvPar R' []
      (.lam (.sort .zero) (.sort (.succ .zero)))
      (.lam (.sort .zero) (.sort (.max (.succ .zero) .zero)))
      (.pi (.sort .zero) (.sort (.succ (.succ .zero)))) :=
    K.stepLift hA hs
  cases out with
  | proofIndex p =>
      -- `chain : pi (sort 0) (sort 2) ⟶ prop`, `propTy : prop : sort 0`;
      -- transport puts the Pi itself in Prop.
      have hpropT : HasTyT emptyEnv 0 [] p.proposition (.sort .zero) :=
        p.propTy.val hcl hinst
      have hchain : TyConvT emptyEnv 0 [] p.proposition
          (.pi (.sort .zero) (.sort (.succ (.succ .zero)))) :=
        (p.chain.val hcl hinst).symmT
      obtain ⟨hpi⟩ := F8A2Support.sort_transport su EnvWfT.empty CtxWfT.nil
        hchain hpropT
      obtain ⟨_, _, ⟨hB0⟩⟩ :=
        F8A2Support.pi_zero_inv su EnvWfT.empty CtxWfT.nil hpi
      -- hB0 : sort 2 : sort 0 under the domain binder — but the real typing
      -- is sort 2 : sort 3.
      have hB3 : HasTyT emptyEnv 0 [.assumption (.sort .zero)]
          (.sort (.succ (.succ .zero)))
          (.sort (.succ (.succ (.succ .zero)))) :=
        .sort _ _
      have bad := su EnvWfT.empty
        (CtxWfT.assumption [] (.sort .zero) (.succ .zero) .nil
          (.sort [] .zero)) hB0 hB3 (fun _ => none)
      simp [eval] at bad

end Rcic.Declarative.F8Measure.JLam
