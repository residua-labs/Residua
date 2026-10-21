import rcic.RcicSynBelowScoped

/-!
# T12 (4c): `SlotKindSource` — the slot kind's bit from actual domain provenance

`research/rcic/sortrow/S6_IOTA_SLOT_KIND_SOURCE.md` (ChatGPT's approved S6,
PR #7327). T7 asks whether the actual argument of an original ι application
erases to `★`; the target is two steps (`S6` §1):

* `qa.eps σ ρ = .star ↔ naturalBit = true` — the real `PBit qa pN` query, and
* `naturalBit = declarationBit` — this module's layer,

where `qa : TyP E n Γ a A` is the argument typing, `pN := qa.reg.2` the
natural domain typing, and `pD : TyP E n Γ D (.sort uD)` the real
declaration-domain typing produced by the same admission, level instance
and parameter transport. `naturalBit = levelIsZero (σ uN)`,
`declarationBit = levelIsZero (σ uD)`.

`SlotKindSource` is a **provenance-indexed view** (`S6` §3): it records HOW
the bit's source is supplied, never the conclusion. No field states
`naturalBit = declarationBit`. K1 retains the original conversion's
occurrence: the `domainConv` constructor stores the original node `orig`,
a child-index `path`, the receipt `occ` (`DNode.subAt` resolves `path` to
`c`), and the atom bound `hb` against `orig.wt` — Q198/P2's repair; §7
executes the control refusing a fresh same-judgment `CvP`. Each of the
three supply routes has a
conditional consumption theorem: the smaller A6 results are hypotheses
(this module asserts no producer), and each call carries the `S6` §4
per-atom payment — a `DMStep` off the bound `C ++ [N]` that removes the
original atom `N` and adds only real atoms dominated by `N` (never the
derivations' total `wt`).

The control (`S6` §2, §5) is executed at the end: a legal native
environment `P : sort 0`, `U : sort 1`, `Γ = [x : P]`, and the single
structural `TableWF` rule `P → U` yield a full erased Π correspondence while
`naturalBit = true` and `declarationBit = false`. The mutant view
`SlotKindSourceMut`, which keys on that erased correspondence alone,
is inhabited there — the wrong acceptance the bit-equality field would
hide. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the two bits (`S6` §1) -/

/-- The natural side's bit: the argument-domain sort's zero tag after `σ`. -/
def naturalBit (σ : Level → Level) (uN : Level) : Bool := levelIsZero (σ uN)

/-- The declaration side's bit: the declared-domain sort's zero tag after `σ`. -/
def declarationBit (σ : Level → Level) (uD : Level) : Bool := levelIsZero (σ uD)

/-! ## §1b the derivation-forest occurrence path (`S6` §3 K1 provenance)

`S6` §3 requires K1 to keep `c` **with its exact position in the original
ι/prefix** — a caller must not be able to mint a fresh same-judgment
conversion and pass it for the original. The path is a list of child
indices into the `TyP`/`CvP` derivation forest; `DNode.subAt` resolves it.
`DNode` is unindexed on `E`, `n`, `Γ` and the end types because transports
(`wk`, `esub`, `linst`, `ewk`, `cctx`) cross all of those boundaries. -/

/-- A node of the `TyP`/`CvP` derivation forest. -/
inductive DNode : Type where
  | ty {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
      (D : TyP E n Γ e T) : DNode
  | cv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
      (c : CvP E n Γ a b T) : DNode

mutual

/-- The immediate derivation children of a `TyP` node, in declaration
    order — the positions a path indexes. -/
def TyP.dchildren : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → TyP E n Γ e T → List DNode
  | _, _, _, _, _, .sort .. => []
  | _, _, _, _, _, .bvar _ _ _ _ _ _ _ hA => [.ty hA]
  | _, _, _, _, _, .const _ _ _ _ _ _ _ _ _ _ _ _ hT => [.ty hT]
  | _, _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => [.ty hA, .ty hB]
  | _, _, _, _, _, .lam _ _ _ _ _ _ _ _ hA hb hB => [.ty hA, .ty hb, .ty hB]
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha hT => [.ty hf, .ty ha, .ty hT]
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hT =>
      [.ty hA, .ty hv, .ty hb, .ty hT]
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => [.ty hexp]
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h hc => [.ty h, .cv hc]
  | _, _, _, _, _, .wk _ _ _ _ _ _ _ D => [.ty D]
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ hv hvT => [.ty D, .ty hv, .ty hvT]
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ D _ hv hvT => [.ty D, .ty hv, .ty hvT]
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => [.ty D]
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => [.ty D]
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D hA => [.ty D, .cv hA]

/-- The immediate derivation children of a `CvP` node, in declaration
    order. -/
def CvP.dchildren : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} → CvP E n Γ a b T → List DNode
  | _, _, _, _, _, _, .refl _ _ _ _ _ h dl dr => [.ty h, .ty dl, .ty dr]
  | _, _, _, _, _, _, .symm _ _ _ _ _ _ h dl dr => [.cv h, .ty dl, .ty dr]
  | _, _, _, _, _, _, .trans _ _ _ _ _ _ _ h1 h2 dl dr =>
      [.cv h1, .cv h2, .ty dl, .ty dr]
  | _, _, _, _, _, _, .beta _ _ _ _ _ _ _ _ hA hb harg dl dr =>
      [.ty hA, .ty hb, .ty harg, .ty dl, .ty dr]
  | _, _, _, _, _, _, .zeta _ _ _ _ _ _ _ _ hA hv hb dl dr =>
      [.ty hA, .ty hv, .ty hb, .ty dl, .ty dr]
  | _, _, _, _, _, _, .zetaLocal _ _ _ _ _ _ _ _ hv dl dr =>
      [.ty hv, .ty dl, .ty dr]
  | _, _, _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ hb dl dr =>
      [.ty hb, .ty dl, .ty dr]
  | _, _, _, _, _, _, .iota _ _ _ _ _ _ _ hl hr dl dr =>
      [.ty hl, .ty hr, .ty dl, .ty dr]
  | _, _, _, _, _, _, .lit _ _ _ _ _ _ _ hexp dl dr => [.ty hexp, .ty dl, .ty dr]
  | _, _, _, _, _, _, .app _ _ _ _ _ _ _ _ _ h1 h2 dl dr =>
      [.cv h1, .cv h2, .ty dl, .ty dr]
  | _, _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ hA hb dl dr =>
      [.cv hA, .cv hb, .ty dl, .ty dr]
  | _, _, _, _, _, _, .pi _ _ _ _ _ _ _ _ _ hA hB dl dr =>
      [.cv hA, .cv hB, .ty dl, .ty dr]
  | _, _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ hA hv hb dl dr =>
      [.cv hA, .cv hv, .cv hb, .ty dl, .ty dr]
  | _, _, _, _, _, _, .sorts _ _ _ _ _ _ dl dr => [.ty dl, .ty dr]
  | _, _, _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ _ _ dl dr => [.ty dl, .ty dr]
  | _, _, _, _, _, _, .eta _ _ _ _ _ _ h dl dr => [.ty h, .ty dl, .ty dr]
  | _, _, _, _, _, _, .irr _ _ _ _ _ _ hP hp hq dl dr =>
      [.ty hP, .ty hp, .ty hq, .ty dl, .ty dr]
  | _, _, _, _, _, _, .tyConv _ _ _ _ _ _ _ _ h hA dl dr =>
      [.cv h, .cv hA, .ty dl, .ty dr]
  | _, _, _, _, _, _, .wk _ _ _ _ _ _ _ _ h => [.cv h]
  | _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ _ h _ hv hvT =>
      [.cv h, .ty hv, .ty hvT]
  | _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ _ h => [.cv h]
  | _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ _ h => [.cv h]
  | _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ _ h hA => [.cv h, .cv hA]
  | _, _, _, _, _, _, .fsub _ _ _ _ _ _ _ _ _ hB hA hab dl dr =>
      [.ty hB, .ty hA, .cv hab, .ty dl, .ty dr]

end

/-- The children of a forest node. -/
def DNode.children : DNode → List DNode
  | .ty D => D.dchildren
  | .cv c => c.dchildren

/-- Resolve a child-index path inside a forest node; `[]` is the node
    itself. The occurrence receipt of `S6` §3 K1 is an equation on this
    function. -/
def DNode.subAt : DNode → List Nat → Option DNode
  | d, [] => some d
  | d, i :: rest => (d.children[i]?).bind fun d' => d'.subAt rest

/-! ## §2 the provenance-indexed view (`S6` §3) -/

/-- How the slot's kind is sourced — indexed by the argument typing `qa`,
    its natural sort typing `pN` (the regularity `qa.reg.2` the reader
    actually produced), and the declaration-domain sort typing `pD`.
    Three real supply routes; none stores the conclusion
    `naturalBit = declarationBit` — that bit equality is only ever the
    OUTPUT of `SlotKindSource.consume`, from the smaller A6 results the
    source's `queries` names. -/
inductive SlotKindSource {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a A : Expr Nat} {uN : Level}
    (qa : TyP E n Γ a A) (pN : TyP E n Γ A (.sort uN))
    {D : Expr Nat} {uD : Level} (pD : TyP E n Γ D (.sort uD)) : Type where
  /-- **K0**: the displayed domain is the same actual term. The real
      equation `A = D` is kept; consumption transports `pD`'s index along
      it and calls `BitCoh pN pD` — the exact same-subject A6 query, no new
      canonical typing (`S6` §3 K0). -/
  | sameDomain (hAD : A = D) : SlotKindSource qa pN pD
  /-- **K1**: a real bounded original domain conversion `c : A ≡ D` at
      `sort w`, RETAINED WITH its provenance (`S6` §3 K1, Q198/P2):
      `orig` is the original conversion of the original ι/prefix it
      occurred in, `path` its exact child-index position inside `orig`,
      `occ` the occurrence receipt (`DNode.subAt` resolves `path` to
      `c` itself), and `hb` the per-atom bound against `orig`'s own
      weight — the original `N = Hι.wt` of `S6` §4. A caller cannot
      present a fresh same-judgment conversion here: it would fail the
      `occ` equation. Never the target's Π-injectivity output repackaged. -/
  | domainConv {w : Level} {Γ₀ : LCtx} {a₀ b₀ T₀ : Expr Nat}
      (Aw : Nat → Nat)
      (orig : CvP E n Γ₀ a₀ b₀ T₀)
      (path : List Nat)
      (c : CvP E n Γ A D (.sort w))
      (occ : DNode.subAt (.cv orig) path = some (.cv c))
      (hb : ∀ x ∈ c.atoms Aw, x < orig.wt Aw) :
      SlotKindSource qa pN pD
  /-- **K2**: both sides are real `linst` views of ONE declaration-domain
      source `src : D₀ : sort u` at the same term-parameter instance —
      `Γ`, `A`, `D` are the `ls₁`-instantiated and `ls₂`-instantiated
      faces, and `eqNList ls₁ ls₂` is the original level-list correspondence
      (`S6` §3 K2). -/
  | levelViews {a' : Nat} {Γ₀ : LCtx} {D₀ : Expr Nat} {u : Level}
      {ls₁ ls₂ : List Level}
      (src : TyP E a' Γ₀ D₀ (.sort u)) (hls : eqNList ls₁ ls₂)
      (hb₁ : levelsBounded n ls₁ = true) (hb₂ : levelsBounded n ls₂ = true)
      (hl₁ : ls₁.length = a') (hl₂ : ls₂.length = a')
      (hΓ₁ : instLvlsCtx ls₁ Γ₀ = Γ) (hΓ₂ : instLvlsCtx ls₂ Γ₀ = Γ)
      (hD₁ : instantiateLevels ls₁ D₀ = A) (hD₂ : instantiateLevels ls₂ D₀ = D) :
      SlotKindSource qa pN pD

/-! ## §3 the lazy linst view and the three conditional consumption theorems -/

/-- The K2 view actually built by a real reader: `src`'s lazy `linst`
    instance at `ls`, transported to the displayed context and domain by
    the provenance equations. `instantiateLevels ls (.sort u)` reduces to
    `.sort (instLevel ls u)` by `rfl`. -/
def slotKindLinstView {E : ResolvedEnv} {a' n : Nat} {Γ₀ Γ : LCtx}
    {D₀ A : Expr Nat} {u : Level} {ls : List Level}
    (src : TyP E a' Γ₀ D₀ (.sort u))
    (hb : levelsBounded n ls = true) (hl : ls.length = a')
    (hΓ : instLvlsCtx ls Γ₀ = Γ) (hD : instantiateLevels ls D₀ = A) :
    TyP E n Γ A (.sort (instLevel ls u)) :=
  hΓ ▸ hD ▸ TyP.linst E a' n Γ₀ D₀ (.sort u) ls hb hl src

/-- **K0 consumption** (`S6` §3): `A = D` is the actual term equation; the
    transported `pD` shares `pN`'s subject, so `BitCoh σ pN (hAD ▸ pD)` — a
    smaller same-subject A6 result — IS the bit equality. Conditional: the
    `BitCoh` hypothesis is the query a producer must supply. -/
theorem slotKind_consume_k0 {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A D : Expr Nat} {uN uD : Level}
    (hAD : A = D) (pN : TyP E n Γ A (.sort uN)) (pD : TyP E n Γ D (.sort uD))
    (h : BitCoh σ pN (hAD ▸ pD)) :
    naturalBit σ uN = declarationBit σ uD :=
  h

/-- **K1 consumption** (`S6` §3): a real bounded `c : CvP E n Γ A D (sort w)`
    gives two same-subject A6s — `SortCoh σ pN c.dl : eqN (σ uN) (σ w)` and
    `SortCoh σ c.dr pD : eqN (σ w) (σ uD)` — hence the bit. No repackaging
    of the argument as `a : D`, no generated `c`; conditional on both
    `SortCoh` results. -/
theorem slotKind_consume_k1 {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A D : Expr Nat} {uN uD w : Level}
    (pN : TyP E n Γ A (.sort uN)) (pD : TyP E n Γ D (.sort uD))
    (c : CvP E n Γ A D (.sort w))
    (h₁ : SortCoh σ pN c.dl) (h₂ : SortCoh σ c.dr pD) :
    naturalBit σ uN = declarationBit σ uD :=
  levelIsZero_congr (eqN_trans h₁ h₂)

/-- **K2 consumption** (`S6` §3): the same declaration-domain source at
    `eqNList` level lists. `h₁` aligns `pN` with the `ls₁`-view on the
    displayed domain `A`, `h₂` aligns the `ls₂`-view on `D` with `pD`, and
    `instLevel_eqNList hls` pushed through `σ` (`hσ.eqN_map`) is the level
    congruence joining the two instantiated sorts. -/
theorem slotKind_consume_k2 {σ : Level → Level} (hσ : LevelSub σ)
    {E : ResolvedEnv} {a' n : Nat} {Γ₀ Γ : LCtx} {A D D₀ : Expr Nat}
    {uN uD u : Level} {ls₁ ls₂ : List Level}
    (pN : TyP E n Γ A (.sort uN)) (pD : TyP E n Γ D (.sort uD))
    (src : TyP E a' Γ₀ D₀ (.sort u)) (hls : eqNList ls₁ ls₂)
    (hb₁ : levelsBounded n ls₁ = true) (hb₂ : levelsBounded n ls₂ = true)
    (hl₁ : ls₁.length = a') (hl₂ : ls₂.length = a')
    (hΓ₁ : instLvlsCtx ls₁ Γ₀ = Γ) (hΓ₂ : instLvlsCtx ls₂ Γ₀ = Γ)
    (hD₁ : instantiateLevels ls₁ D₀ = A) (hD₂ : instantiateLevels ls₂ D₀ = D)
    (h₁ : SortCoh σ pN (slotKindLinstView src hb₁ hl₁ hΓ₁ hD₁))
    (h₂ : SortCoh σ (slotKindLinstView src hb₂ hl₂ hΓ₂ hD₂) pD) :
    naturalBit σ uN = declarationBit σ uD :=
  levelIsZero_congr
    (eqN_trans h₁ (eqN_trans (hσ.eqN_map (instLevel_eqNList hls u)) h₂))

/-- The smaller A6 queries a source consumes — the conditional inputs, by
    supply route (`S6` §3). -/
def SlotKindSource.queries (σ : Level → Level)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat} {uN : Level}
    {qa : TyP E n Γ a A} {pN : TyP E n Γ A (.sort uN)}
    {D : Expr Nat} {uD : Level} {pD : TyP E n Γ D (.sort uD)} :
    SlotKindSource qa pN pD → Prop
  | .sameDomain hAD => BitCoh σ pN (hAD ▸ pD)
  | .domainConv _Aw _orig _path c _occ _hb =>
      SortCoh σ pN c.dl ∧ SortCoh σ c.dr pD
  | .levelViews src _hls hb₁ hb₂ hl₁ hl₂ hΓ₁ hΓ₂ hD₁ hD₂ =>
      SortCoh σ pN (slotKindLinstView src hb₁ hl₁ hΓ₁ hD₁) ∧
      SortCoh σ (slotKindLinstView src hb₂ hl₂ hΓ₂ hD₂) pD

/-- The consumption entry point: a provenance source plus ITS named queries
    (the conditional A6 results) yields `naturalBit = declarationBit`.
    `LevelSub σ` is required only by the K2 arm's level congruence; it is a
    uniform premise here. -/
theorem SlotKindSource.consume {σ : Level → Level} (hσ : LevelSub σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat} {uN : Level}
    {qa : TyP E n Γ a A} {pN : TyP E n Γ A (.sort uN)}
    {D : Expr Nat} {uD : Level} {pD : TyP E n Γ D (.sort uD)}
    (src : SlotKindSource qa pN pD) (q : src.queries σ) :
    naturalBit σ uN = declarationBit σ uD := by
  cases src with
  | sameDomain hAD => exact q
  | domainConv _ _ _ c _ _ => exact levelIsZero_congr (eqN_trans q.1 q.2)
  | levelViews src₀ hls hb₁ hb₂ hl₁ hl₂ hΓ₁ hΓ₂ hD₁ hD₂ =>
      exact levelIsZero_congr
        (eqN_trans q.1 (eqN_trans (hσ.eqN_map (instLevel_eqNList hls _)) q.2))

/-- The full two-step target (`S6` §1): the real `PBit qa pN` query plus a
    source's queries give `qa.eps σ ρ = .star ↔ declarationBit = true`.
    The first step is never skipped; the second is never replaced by an
    erased domain conversion. -/
theorem slotEps_iff_declarationBit {σ : Level → Level} (hσ : LevelSub σ)
    (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat} {uN : Level}
    {qa : TyP E n Γ a A} {pN : TyP E n Γ A (.sort uN)}
    {D : Expr Nat} {uD : Level} {pD : TyP E n Γ D (.sort uD)}
    (src : SlotKindSource qa pN pD) (q : src.queries σ)
    (hbit : PBit σ ρ qa pN) :
    qa.eps σ ρ = .star ↔ declarationBit σ uD = true :=
  Iff.trans hbit (iff_of_eq (congrArg (· = true) (src.consume hσ q)))

/-! ## §4 the per-atom payments (`S6` §4)

Every consumed call is paid by atoms, never by the lazy derivations' total
`wt`: the bound is `C ++ [N]` with `N` the original ι node's atom, and each
query's real atoms all descend from it. -/

/-- The §4 step itself: keep `C`, remove the original atom `N`, add the
    query's real atoms `Y`, all dominated by `N`. -/
theorem dmStep_slotAtom (C Y : List Nat) {N : Nat} (h : ∀ y ∈ Y, y < N) :
    DMStep (C ++ Y) (C ++ [N]) :=
  dmStep_perm_left List.perm_append_comm
    (dmStep_perm_right (List.perm_append_singleton N C).symm
      (dmStep_of_below h))

/-- A two-derivation call (the A6 pairs) pays per-atom off `C ++ [N]`. -/
theorem slotKind_paid_pair (C X Y : List Nat) {N : Nat}
    (hX : ∀ y ∈ X, y < N) (hY : ∀ y ∈ Y, y < N) :
    DMStep (C ++ X ++ Y) (C ++ [N]) :=
  List.append_assoc C X Y ▸
    dmStep_slotAtom C (X ++ Y) fun y hy => by
      rcases List.mem_append.mp hy with hy | hy
      · exact hX y hy
      · exact hY y hy

/-- `c.dl`'s and `c.dr`'s atoms are bounded by `c`'s own — `dmStep_cvp_*`
    transports the original `c`'s bound to its endpoints, never a rebuilt
    conversion (`S6` §4). -/
theorem slotKind_cvp_atoms_lt (Aw : Nat → Nat) {N : Nat}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A D : Expr Nat} {w : Level}
    (c : CvP E n Γ A D (.sort w))
    (hc : ∀ y ∈ c.atoms Aw, y < N) :
    (∀ y ∈ c.dl.atoms Aw, y < N) ∧ (∀ y ∈ c.dr.atoms Aw, y < N) := by
  have hd := dmStep_cvp_dl Aw c
  have hr := dmStep_cvp_dr Aw c
  constructor <;> intro y hy
  · obtain ⟨X, Y, Z, _, hM, hM', hdom⟩ := hd
    have hyY : y ∈ Y ++ Z := hM'.subset hy
    rcases List.mem_append.mp hyY with hy | hy
    · obtain ⟨x, hxX, hyx⟩ := hdom y hy
      have hxM : x ∈ c.atoms Aw := hM.symm.subset (List.mem_append_left Z hxX)
      exact Nat.lt_trans hyx (hc x hxM)
    · exact hc y (hM.symm.subset (List.mem_append_right X hy))
  · obtain ⟨X, Y, Z, _, hM, hM', hdom⟩ := hr
    have hyY : y ∈ Y ++ Z := hM'.subset hy
    rcases List.mem_append.mp hyY with hy | hy
    · obtain ⟨x, hxX, hyx⟩ := hdom y hy
      have hxM : x ∈ c.atoms Aw := hM.symm.subset (List.mem_append_left Z hxX)
      exact Nat.lt_trans hyx (hc x hxM)
    · exact hc y (hM.symm.subset (List.mem_append_right X hy))

/-- K0's `BitCoh` pair is paid off `C ++ [N]`. -/
theorem slotKind_k0_paid (Aw : Nat → Nat) (C : List Nat) {N : Nat}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {uN uD : Level}
    {pN : TyP E n Γ A (.sort uN)} {pD' : TyP E n Γ A (.sort uD)}
    (hpN : ∀ y ∈ pN.atoms Aw, y < N) (hpD : ∀ y ∈ pD'.atoms Aw, y < N) :
    DMStep (C ++ pN.atoms Aw ++ pD'.atoms Aw) (C ++ [N]) :=
  slotKind_paid_pair C _ _ hpN hpD

/-- K1's left call `C ++ pN.atoms ++ c.dl.atoms` descends from
    `C ++ [N]` with `N = orig.wt Aw` — the RETAINED original's weight.
    The caller must present the `domainConv` certificate: `occ` pins `c`
    to `orig`'s `path` and `hb` is `c`'s atom bound; `c.dl`'s bound is
    derived by `slotKind_cvp_atoms_lt`, never accepted separately
    (`S6` §4's first example, certificate-reading). -/
theorem slotKind_k1_left_paid (Aw : Nat → Nat) (C : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A D : Expr Nat} {uN w : Level}
    {pN : TyP E n Γ A (.sort uN)}
    {Γ₀ : LCtx} {a₀ b₀ T₀ : Expr Nat} {orig : CvP E n Γ₀ a₀ b₀ T₀}
    {path : List Nat} {c : CvP E n Γ A D (.sort w)}
    (_occ : DNode.subAt (.cv orig) path = some (.cv c))
    (hb : ∀ x ∈ c.atoms Aw, x < orig.wt Aw)
    (hpN : ∀ y ∈ pN.atoms Aw, y < orig.wt Aw) :
    DMStep (C ++ pN.atoms Aw ++ c.dl.atoms Aw) (C ++ [orig.wt Aw]) :=
  slotKind_paid_pair C _ _ hpN (slotKind_cvp_atoms_lt Aw c hb).1

/-- K1's right call `C ++ c.dr.atoms ++ pD.atoms` descends from
    `C ++ [orig.wt Aw]` on the same certificate (`S6` §4's second
    example). -/
theorem slotKind_k1_right_paid (Aw : Nat → Nat) (C : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A D : Expr Nat} {uD w : Level}
    {pD : TyP E n Γ D (.sort uD)}
    {Γ₀ : LCtx} {a₀ b₀ T₀ : Expr Nat} {orig : CvP E n Γ₀ a₀ b₀ T₀}
    {path : List Nat} {c : CvP E n Γ A D (.sort w)}
    (_occ : DNode.subAt (.cv orig) path = some (.cv c))
    (hb : ∀ x ∈ c.atoms Aw, x < orig.wt Aw)
    (hpD : ∀ y ∈ pD.atoms Aw, y < orig.wt Aw) :
    DMStep (C ++ c.dr.atoms Aw ++ pD.atoms Aw) (C ++ [orig.wt Aw]) :=
  slotKind_paid_pair C _ _ (slotKind_cvp_atoms_lt Aw c hb).2 hpD

/-- K2's left call (pN against the `ls₁`-view) is paid per-atom. -/
theorem slotKind_k2_left_paid (Aw : Nat → Nat) (C : List Nat) {N : Nat}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {uN u₁ : Level}
    {pN : TyP E n Γ A (.sort uN)} {v₁ : TyP E n Γ A (.sort u₁)}
    (hpN : ∀ y ∈ pN.atoms Aw, y < N) (hv : ∀ y ∈ v₁.atoms Aw, y < N) :
    DMStep (C ++ pN.atoms Aw ++ v₁.atoms Aw) (C ++ [N]) :=
  slotKind_paid_pair C _ _ hpN hv

/-- K2's right call (the `ls₂`-view against pD) is paid per-atom. -/
theorem slotKind_k2_right_paid (Aw : Nat → Nat) (C : List Nat) {N : Nat}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {D : Expr Nat} {u₂ uD : Level}
    {v₂ : TyP E n Γ D (.sort u₂)} {pD : TyP E n Γ D (.sort uD)}
    (hv : ∀ y ∈ v₂.atoms Aw, y < N) (hpD : ∀ y ∈ pD.atoms Aw, y < N) :
    DMStep (C ++ v₂.atoms Aw ++ pD.atoms Aw) (C ++ [N]) :=
  slotKind_paid_pair C _ _ hv hpD

/-- The `PBit qa pN` step is paid by the original argument occurrence and
    its actual regularity (`S6` §4). -/
theorem slotKind_pbit_paid (Aw : Nat → Nat) (C : List Nat) {N : Nat}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat} {uN : Level}
    {qa : TyP E n Γ a A} {pN : TyP E n Γ A (.sort uN)}
    (hqa : ∀ y ∈ qa.atoms Aw, y < N) (hpN : ∀ y ∈ pN.atoms Aw, y < N) :
    DMStep (C ++ qa.atoms Aw ++ pN.atoms Aw) (C ++ [N]) :=
  slotKind_paid_pair C _ _ hqa hpN

/-! ## §5 the control (`S6` §2): an erased Π correspondence with distinct bits -/

/-- `P : sort 0` — a legal native axiom member. -/
def slotP : CheckedMember := ⟨.axiomM, 0, .sort .zero, none⟩

/-- `U : sort 1` — a second legal native axiom member. -/
def slotU : CheckedMember := ⟨.axiomM, 0, .sort (.succ .zero), none⟩

/-- The control environment: exactly `P : sort 0` at `0`, `U : sort 1` at `1`. -/
def slotEnv : ResolvedEnv := extendEnv (extendEnv emptyEnv 0 slotP) 1 slotU

/-- `Γ = [x : P]`. -/
def slotCtx : LCtx := [.assumption (.const 0 [])]

/-- `pN`: `P`'s actual sort typing — `const P [] : sort 0`. -/
def slotPN (n : Nat) : TyP slotEnv n slotCtx (.const 0 []) (.sort .zero) :=
  TyP.const slotEnv n slotCtx 0 [] [] slotP (.succ .zero) rfl rfl rfl
    (eqNList_refl [])
    (TyP.sort slotEnv n slotCtx .zero (.succ .zero) (eqN_refl _))

/-- `pD`: `U`'s actual sort typing — `const U [] : sort 1`. -/
def slotPD (n : Nat) : TyP slotEnv n slotCtx (.const 1 []) (.sort (.succ .zero)) :=
  TyP.const slotEnv n slotCtx 1 [] [] slotU (.succ (.succ .zero)) rfl rfl rfl
    (eqNList_refl [])
    (TyP.sort slotEnv n slotCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- `qa`: the actual argument typing `x : P`. -/
def slotQA (n : Nat) : TyP slotEnv n slotCtx (.bvar 0) (.const 0 []) :=
  TyP.bvar slotEnv n slotCtx 0 (.const 0 []) .zero
    (lookup_assumption_zero _ _) (slotPN n)

/-- `pN` really is `qa`'s regularity — the S6 §1 reader's `pN := qa.reg.2`. -/
theorem slotPN_is_reg (n : Nat) : (slotQA n).reg = ⟨.zero, slotPN n⟩ := rfl

/-- The single erased rule (`S6` §2): `head = P`, no major, no arguments,
    `rhs = const U []` — `P ↦ U` as an `ETm` step. -/
def slotRule : CRule where
  head := 0
  nargs := fun _ => 0
  major := none
  rhs := fun _ _ => .const 1 []

/-- `slotRule` satisfies structural `TableWF`: rhs is constant (congruence,
    closedness), the only rule (uniqueness), major-free (rigidity,
    disjointness, nullity). It never binds a native declaration's typing —
    that is exactly the point. -/
theorem slotTable_wf : TableWF [slotRule] where
  congr :=
    { rhs := by
        intro ρ hρ ls ls₂ ms ms₂ _ _
        simp only [List.mem_singleton] at hρ; subst hρ
        exact .const 1 (eqNList_refl [])
      nargs := by
        intro ρ hρ _ _ _
        simp only [List.mem_singleton] at hρ; subst hρ; rfl
      marity := by
        intro ρ hρ _ _ hm
        simp only [List.mem_singleton] at hρ; subst hρ; cases hm }
  closed := by
    intro ρ hρ ls ms
    simp only [List.mem_singleton] at hρ; subst hρ
    exact trivial
  rigid := by
    intro ρ hρ _ _ hm
    simp only [List.mem_singleton] at hρ; subst hρ; cases hm
  bare_unique := by
    intro ρ hρ _ σ hσ _
    simp only [List.mem_singleton] at hρ hσ; subst hρ; subst hσ; rfl
  ctor_disjoint := by
    intro ρ hρ _ _ _ _ _ _ _ hm
    simp only [List.mem_singleton] at hρ; subst hρ; cases hm
  bare_nullary := by
    intro ρ hρ _ ls
    simp only [List.mem_singleton] at hρ; subst hρ; rfl

/-- The rule fires: `const P [] → const U []` is one `EStep`. -/
theorem slotRule_step :
    EStep [slotRule] (.const 0 []) (.const 1 []) :=
  .inl (.cr (.bare (List.mem_singleton_self _) rfl [] [] rfl))

/-- The erased domain correspondence: `pN.eps`/`pD.eps` — the actual erased
    faces of the two domain typings — are `const P []` and `const U []`,
    joined by the rule. -/
theorem slot_erased_domains (n : Nat) :
    ConvMod (EStep [slotRule]) LvlEq ((slotPN n).eps id []) ((slotPD n).eps id []) := by
  have h1 : (slotPN n).eps id [] = .const 0 [] := rfl
  have h2 : (slotPD n).eps id [] = .const 1 [] := rfl
  rw [h1, h2]
  exact .fwd slotRule_step

/-- A full erased Π correspondence on the two domains (`S6` §2): under the
    rule, `Π P. X` steps to `Π U. X` for every erased codomain `X`. -/
theorem slot_erased_pi (X : ETm) :
    ConvMod (EStep [slotRule]) LvlEq (.pi (.const 0 []) X) (.pi (.const 1 []) X) :=
  .fwd (.inl (.piL X (.cr (.bare (List.mem_singleton_self _) rfl [] [] rfl))))

/-- The control's bits genuinely differ: `naturalBit = true` — `qa.reg.1`
    is `uN = sort 0`, P's domain being a proposition — and
    `declarationBit = false` (`uD = sort 1`). -/
theorem slot_bits_differ (n : Nat) :
    naturalBit id (slotQA n).reg.1 = true ∧
      declarationBit id (.succ .zero) = false ∧
        naturalBit id (slotQA n).reg.1 ≠ declarationBit id (.succ .zero) :=
  ⟨rfl, rfl, fun h => Bool.noConfusion h⟩

/-! ## §6 the mutant (`S6` §2, §5) — the erased-only view wrongly accepts -/

/-- **MUTANT.** The interface `S6` §2 refuses: keep only the erased domain
    conversion and the two legal typings. `SlotKindSourceMut` is inhabited
    whenever `ConvMod (EStep tbl) LvlEq (pN.eps σ ρ) (pD.eps σ ρ)` — which
    `convE_pi_inv_wf` supplies from any erased Π correspondence — and asks
    nothing about provenance. It is an input view, not a theorem: no field
    states `naturalBit = declarationBit` there either, but its `queries`
    are empty — it "consumes" nothing, so nothing constrains when it may
    be built. -/
structure SlotKindSourceMut (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {uN : Level}
    (pN : TyP E n Γ A (.sort uN))
    {D : Expr Nat} {uD : Level} (pD : TyP E n Γ D (.sort uD)) : Prop where
  /-- the only evidence asked for: the erased correspondence -/
  erased : ConvMod (EStep tbl) LvlEq (pN.eps σ ρ) (pD.eps σ ρ)

/-- The mutant consumes nothing: the bit equality it would have to produce
    is simply unavailable — on the control it is **false**. `S6` §2: an
    interface keeping only an erased conversion, two legal domain typings
    and the argument typing has already lost the provenance needed to tell
    the cases apart. -/
theorem slotKindMut_wrongly_accepts (n : Nat) :
    SlotKindSourceMut [slotRule] id [] (slotPN n) (slotPD n) ∧
      ¬ (naturalBit id .zero = declarationBit id (.succ .zero)) :=
  ⟨⟨slot_erased_domains n⟩, fun h => Bool.noConfusion h⟩

/-- Against the real view: `SlotKindSource` needs `A = D` (it is not:
    `const 0 [] ≠ const 1 []`), a `CvP` between them at a sort (none exists
    across `sort 0`/`sort 1` distinct members in this env), or one shared
    declaration source (there is none) — the mutant's instance supplies
    none of these. This pin records the first clause concretely. -/
theorem slotKind_k0_needs_real_eq : (.const 0 []) ≠ (.const 1 [] : Expr Nat) :=
  fun h => Expr.noConfusion h fun h01 _ => Nat.noConfusion h01

/-! ## §7 the K1 occurrence receipt and the foreign-`CvP` refusal (Q198/P2)

The audit's mutant, made concrete: a **fixed** reflexive conversion `c₀`
(the original) and a fresh `.symm` node wrapped around it — the two share
the judgment `sort 0 ≡ sort 0 : sort 1`. The `domainConv` receipt pins
`c₀` to its path inside the retained original; the foreign node fails the
receipt at every position it is tried. -/

/-- `Γ₀ = [x : sort 0]` — the fixture context. -/
def occCtx : LCtx := [.assumption (.sort .zero)]

/-- `sort 0 : sort 1` in an arbitrary context — the fixture's TyP leaf. -/
def occSortH (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    TyP E n Γ (.sort .zero) (.sort (.succ .zero)) :=
  .sort E n Γ .zero (.succ .zero) (eqN_refl _)

/-- The fixed original: `refl` proving `sort 0 ≡ sort 0 : sort 1`. -/
def occC0 (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CvP E n Γ (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .refl E n Γ (.sort .zero) (.sort (.succ .zero))
    (occSortH E n Γ) (occSortH E n Γ) (occSortH E n Γ)

/-- The foreign node — a fresh `.symm` around the fixed original, with
    the SAME judgment `sort 0 ≡ sort 0 : sort 1`. -/
def occOrig (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    CvP E n Γ (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .symm E n Γ (.sort .zero) (.sort .zero) (.sort (.succ .zero))
    (occC0 E n Γ) (occSortH E n Γ) (occSortH E n Γ)

/-- The original's own receipt at the root position: `[]` resolves to
    `c₀` itself — the fixed original singleton. -/
theorem occ_self_path (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    DNode.subAt (.cv (occC0 E n Γ)) [] = some (.cv (occC0 E n Γ)) := rfl

/-- A deeper position still pins the same original: inside the `symm`
    wrapper, child `0` resolves to `c₀`. -/
theorem occ_child_path (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    DNode.subAt (.cv (occOrig E n Γ)) [0] = some (.cv (occC0 E n Γ)) := rfl

/-- The two nodes are distinct despite the shared judgment — `refl`'s
    weight `4` vs the wrapper's `7`; the receipt relies on this. -/
theorem occC0_ne_occOrig (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    occC0 E n Γ ≠ occOrig E n Γ := by
  intro he
  have hw : (occC0 E n Γ).wt (fun _ => 0) = (occOrig E n Γ).wt (fun _ => 0) :=
    congrArg (fun c => c.wt (fun _ => 0)) he
  have h4 : (occC0 E n Γ).wt (fun _ => 0) = 4 := rfl
  have h7 : (occOrig E n Γ).wt (fun _ => 0) = 7 := rfl
  rw [h4, h7] at hw
  exact absurd hw (by decide)

/-- **CONTROL (Q198/P2)**: the foreign same-judgment `CvP` is refused at
    the original's own path — `subAt` resolves `[]` to `c₀`, never to the
    `symm` wrapper. -/
theorem occ_foreign_refused (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    DNode.subAt (.cv (occC0 E n Γ)) [] ≠ some (.cv (occOrig E n Γ)) := by
  intro h
  rw [occ_self_path E n Γ] at h
  have h2 : DNode.cv (occC0 E n Γ) = DNode.cv (occOrig E n Γ) := Option.some.inj h
  obtain ⟨_, _, _, _, _, _, hheq⟩ := DNode.cv.inj h2
  exact occC0_ne_occOrig E n Γ (eq_of_heq hheq)

/-- The receipt is position-sensitive too: inside `orig`, path `[0]`
    resolves to `c₀`; presenting `orig` there is refused. -/
theorem occ_wrong_path_refused (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    DNode.subAt (.cv (occOrig E n Γ)) [0] ≠ some (.cv (occOrig E n Γ)) := by
  rw [occ_child_path E n Γ]
  intro h
  have h2 : DNode.cv (occC0 E n Γ) = DNode.cv (occOrig E n Γ) := Option.some.inj h
  obtain ⟨_, _, _, _, _, _, hheq⟩ := DNode.cv.inj h2
  exact occC0_ne_occOrig E n Γ (eq_of_heq hheq)

/-- `qa` for the certificate fixture: `x : sort 0` in `occCtx`. -/
def occQA (n : Nat) : TyP emptyEnv n occCtx (.bvar 0) (.sort .zero) :=
  .bvar emptyEnv n occCtx 0 (.sort .zero) (.succ .zero)
    (lookup_assumption_zero _ _) (occSortH emptyEnv n occCtx)

/-- `pN`/`pD` for the fixture: `sort 0 : sort 1` in `occCtx`. -/
def occSortTy (n : Nat) : TyP emptyEnv n occCtx (.sort .zero) (.sort (.succ .zero)) :=
  occSortH emptyEnv n occCtx

/-- A full `domainConv` source built on the retained certificate: `orig`
    is the `symm` wrapper, `c₀` sits at its path `[0]`, and `hb` is
    `c₀`'s atom bound against `orig.wt` (`[4] ⊂ [7]` — every atom of the
    reflexive node is its weight `4 < 7`). -/
def occSourceEx (n : Nat) :
    SlotKindSource (occQA n) (occSortTy n) (occSortTy n) :=
  .domainConv (fun _ => 0)
    (occOrig emptyEnv n occCtx) [0] (occC0 emptyEnv n occCtx)
    rfl (fun x hx => by
      have h4 : x = 4 := List.mem_singleton.mp hx
      have h7 : (occOrig emptyEnv n occCtx).wt (fun _ => 0) = 7 := rfl
      rw [h7]; omega)

/-- The K1 queries of that source name the CERTIFIED `c`'s endpoints —
    `c.dl`/`c.dr`, the endpoints of the node `occ` pins at path `[0]`. -/
theorem occSource_queries (σ : Level → Level) (n : Nat) :
    (occSourceEx n).queries σ =
      (SortCoh σ (occSortTy n) (occC0 emptyEnv n occCtx).dl ∧
        SortCoh σ (occC0 emptyEnv n occCtx).dr (occSortTy n)) := rfl

end Rcic.Syn

#print axioms Rcic.Syn.naturalBit
#print axioms Rcic.Syn.declarationBit
#print axioms Rcic.Syn.DNode
#print axioms Rcic.Syn.TyP.dchildren
#print axioms Rcic.Syn.CvP.dchildren
#print axioms Rcic.Syn.DNode.children
#print axioms Rcic.Syn.DNode.subAt
#print axioms Rcic.Syn.SlotKindSource
#print axioms Rcic.Syn.slotKindLinstView
#print axioms Rcic.Syn.slotKind_consume_k0
#print axioms Rcic.Syn.slotKind_consume_k1
#print axioms Rcic.Syn.slotKind_consume_k2
#print axioms Rcic.Syn.SlotKindSource.queries
#print axioms Rcic.Syn.SlotKindSource.consume
#print axioms Rcic.Syn.slotEps_iff_declarationBit
#print axioms Rcic.Syn.dmStep_slotAtom
#print axioms Rcic.Syn.slotKind_paid_pair
#print axioms Rcic.Syn.slotKind_k0_paid
#print axioms Rcic.Syn.slotKind_k1_left_paid
#print axioms Rcic.Syn.slotKind_k1_right_paid
#print axioms Rcic.Syn.slotKind_k2_left_paid
#print axioms Rcic.Syn.slotKind_k2_right_paid
#print axioms Rcic.Syn.slotKind_pbit_paid
#print axioms Rcic.Syn.slotKind_cvp_atoms_lt
#print axioms Rcic.Syn.slotP
#print axioms Rcic.Syn.slotU
#print axioms Rcic.Syn.slotEnv
#print axioms Rcic.Syn.slotCtx
#print axioms Rcic.Syn.slotPN
#print axioms Rcic.Syn.slotPD
#print axioms Rcic.Syn.slotQA
#print axioms Rcic.Syn.slotPN_is_reg
#print axioms Rcic.Syn.slotRule
#print axioms Rcic.Syn.slotTable_wf
#print axioms Rcic.Syn.slotRule_step
#print axioms Rcic.Syn.slot_erased_domains
#print axioms Rcic.Syn.slot_erased_pi
#print axioms Rcic.Syn.slot_bits_differ
#print axioms Rcic.Syn.SlotKindSourceMut
#print axioms Rcic.Syn.slotKindMut_wrongly_accepts
#print axioms Rcic.Syn.slotKind_k0_needs_real_eq
#print axioms Rcic.Syn.occCtx
#print axioms Rcic.Syn.occSortH
#print axioms Rcic.Syn.occC0
#print axioms Rcic.Syn.occOrig
#print axioms Rcic.Syn.occ_self_path
#print axioms Rcic.Syn.occ_child_path
#print axioms Rcic.Syn.occC0_ne_occOrig
#print axioms Rcic.Syn.occ_foreign_refused
#print axioms Rcic.Syn.occ_wrong_path_refused
#print axioms Rcic.Syn.occQA
#print axioms Rcic.Syn.occSortTy
#print axioms Rcic.Syn.occSourceEx
#print axioms Rcic.Syn.occSource_queries
