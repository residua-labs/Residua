import rcic.RcicSynSlotKind
import rcic.RcicSynLetSub
import rcic.RcicSynAppBvarPBit

/-!
# T12 (K4): `SlotKindSourceK4` — SameLetTemplateSort

`research/rcic/sortrow/S8_REDEX_KIND_VIEWS.md` §4 (the T12 K-stage plan;
the ζ-under row's "let template" kind source). For ζ/let paths sharing an
**original Π domain template**, the template's domain sort transports
through the **real `lsub`** — never `.esub`: `.letBinding` is never turned
into `.assumption` to reuse the β helper (`S8` §4, verbatim constraint):

* the real template `pTpl : TyP E n (.letBinding t v :: Γ) A₀ (.sort α)`,
* `hT : TyP E n Γ t (.sort γ)` and the stored-value typings `hv`, `hw`,
* the two original lazy `lsub` instances `pV : A₀[v] : sort α`,
  `pW : A₀[w] : sort α` — both at sort **literally** `α`,

so `naturalBit = declarationBit` follows through the shared `α` as two
same-subject A6 queries, exactly K3's consumption shape. Even when
`A₀[v] ≠ A₀[w]` the kind equation holds — **K4 is not a constructor for
arbitrary let-context conversions**: without an actual `v ≡ w` it only
says two legal `lsub` instances share a sort kind.

Like the K1/K3 repairs (Q198/Q199/P2), every retained input carries its
**occurrence receipt** into the retained original `orig`: `DNode.subAt`
resolves each input's own child-index `path` to the node itself, and the
atom bounds are against `orig.wt` — the original `N` of `S6` §4 / `S8`
§4's "the original `hb` domain, the real `hv`/`hA`". A caller cannot
present a fresh same-judgment node for any field. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the K4 lazy instance and the SameLetTemplateSort source (`S8` §4) -/

/-- The K4 lazy instance built from the retained fields: `letSub` —
    `lsub` at binder `0` through the `castLift0`/`sortLift0`/`tyCast`
    transport stack — gives `A₀[v] : sort α`, one of the "two original
    lazy `lsub` instances" of `S8` §4. `SlotKindSourceK4.letTemplate`'s
    instances ARE this construction over the retained fields — never
    free-standing typings, and never `.esub`: the `.letBinding` identity
    is kept. -/
def slotK4Inst {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {t v A₀ : Expr Nat} {α γ : Level}
    (pTpl : TyP E n (.letBinding t v :: Γ) A₀ (.sort α))
    (hv : TyP E n Γ v t) (hT : TyP E n Γ t (.sort γ)) :
    TyP E n Γ (instantiate0 v A₀) (.sort α) :=
  letSub pTpl hv hT

/-- `lsub` flattens atoms exactly like `esub`: the node's atom list is
    its three real fields'. -/
theorem atoms_lsub (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e A t v : Expr Nat} {j : Nat} {u : Level}
    (D : TyP E n Γ e A) (hget : Γ[j]? = some (.letBinding t v))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).atoms Aw
      = D.atoms Aw ++ hv.atoms Aw ++ hvT.atoms Aw := rfl

/-- `S8` §4's atom count, literally: the `tyCast` transports preserve
    atoms (`atoms_tyCast`), so the instance's atom list is exactly
    `pTpl.atoms ++ hv.atoms ++ hT.atoms` — the `hb`-domain, the stored
    value typing, and the binder-type sort, the three real fields. -/
theorem slotK4Inst_atoms (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {t v A₀ : Expr Nat} {α γ : Level}
    (pTpl : TyP E n (.letBinding t v :: Γ) A₀ (.sort α))
    (hv : TyP E n Γ v t) (hT : TyP E n Γ t (.sort γ)) :
    (slotK4Inst pTpl hv hT).atoms Aw =
      pTpl.atoms Aw ++ hv.atoms Aw ++ hT.atoms Aw := by
  have h : slotK4Inst pTpl hv hT = letSub pTpl hv hT := rfl
  rw [h]
  simp only [letSub, atoms_tyCast, atoms_lsub, atoms_castLift0,
    atoms_sortLift0]

/-- The same for weight: `1 + pTpl.wt + hv.wt + hT.wt`. -/
theorem slotK4Inst_wt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {t v A₀ : Expr Nat} {α γ : Level}
    (pTpl : TyP E n (.letBinding t v :: Γ) A₀ (.sort α))
    (hv : TyP E n Γ v t) (hT : TyP E n Γ t (.sort γ)) :
    (slotK4Inst pTpl hv hT).wt Aw =
      1 + pTpl.wt Aw + hv.wt Aw + hT.wt Aw := by
  have h : slotK4Inst pTpl hv hT = letSub pTpl hv hT := rfl
  rw [h, letSub_wt]

/-- The K4 provenance view — indexed by `qa`, its natural sort typing
    `pN`, and the declaration-domain sort typing `pD`, exactly like
    `SlotKindSource`. `letTemplate` retains both let-context templates,
    both stored-value typings, and the shared binder-type sort, each with
    its own occurrence path and receipt into `orig`, the displayed-domain
    equations, and the per-side atom bounds of `S8` §4 — never the
    conclusion `naturalBit = declarationBit`. -/
inductive SlotKindSourceK4 {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a A : Expr Nat} {uN : Level}
    (qa : TyP E n Γ a A) (pN : TyP E n Γ A (.sort uN))
    {D : Expr Nat} {uD : Level} (pD : TyP E n Γ D (.sort uD)) : Type where
  /-- **K4 — SameLetTemplateSort**: `A` and `D` are two `lsub` instances
      of ONE original template `A₀` — under `.letBinding t v` and
      `.letBinding t w` respectively (`S8` §4). `orig` is the original
      ζ/application-path conversion; each retained field (`pTpl`, `hv`,
      `hT`, `pTpl₂`, `hw`) is pinned inside `orig` by its own
      `DNode.subAt` receipt. The two lazy instances are NOT fields —
      they are `slotK4Inst pTpl hv hT` / `slotK4Inst pTpl₂ hw hT`, the
      `letSub`/`lsub` construction over the retained templates, linked
      to it definitionally; `slotK4Inst_atoms` shows the construction's
      atom list is exactly `S8` §4's `pTpl.atoms ++ hv.atoms ++
      hT.atoms`, and `hbnd`/`hbnd'` bound those lists by `orig.wt`. -/
  | letTemplate {t v w A₀ : Expr Nat} {α γ : Level}
      {Γ₀ : LCtx} {x₀ y₀ T₀ : Expr Nat}
      (Aw : Nat → Nat)
      (orig : CvP E n Γ₀ x₀ y₀ T₀)
      (pTpl : TyP E n (.letBinding t v :: Γ) A₀ (.sort α))
      (hv : TyP E n Γ v t) (hT : TyP E n Γ t (.sort γ))
      (pTpl₂ : TyP E n (.letBinding t w :: Γ) A₀ (.sort α))
      (hw : TyP E n Γ w t)
      (pathT pathV pathS pathT₂ pathW : List Nat)
      (occT : DNode.subAt (.cv orig) pathT = some (.ty pTpl))
      (occV : DNode.subAt (.cv orig) pathV = some (.ty hv))
      (occS : DNode.subAt (.cv orig) pathS = some (.ty hT))
      (occT₂ : DNode.subAt (.cv orig) pathT₂ = some (.ty pTpl₂))
      (occW : DNode.subAt (.cv orig) pathW = some (.ty hw))
      (hA : instantiate0 v A₀ = A) (hD : instantiate0 w A₀ = D)
      (hbnd : ∀ x ∈ pTpl.atoms Aw ++ hv.atoms Aw ++ hT.atoms Aw,
          x < orig.wt Aw)
      (hbnd' : ∀ x ∈ pTpl₂.atoms Aw ++ hw.atoms Aw ++ hT.atoms Aw,
          x < orig.wt Aw) :
      SlotKindSourceK4 qa pN pD

/-- The smaller A6 queries a K4 source consumes: `pN` against the `v`-
    instance transported to `A`, and the `w`-instance transported to `D`
    against `pD` — two same-subject `SortCoh`s through the shared `α`
    (`S8` §4). -/
def SlotKindSourceK4.queries (σ : Level → Level)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat} {uN : Level}
    {qa : TyP E n Γ a A} {pN : TyP E n Γ A (.sort uN)}
    {D : Expr Nat} {uD : Level} {pD : TyP E n Γ D (.sort uD)} :
    SlotKindSourceK4 qa pN pD → Prop
  | .letTemplate _ _ pTpl hv hT pTpl₂ hw _ _ _ _ _ _ _ _ _ _ hA hD _ _ =>
      SortCoh σ pN (hA ▸ slotK4Inst pTpl hv hT) ∧
        SortCoh σ (hD ▸ slotK4Inst pTpl₂ hw hT) pD

/-- **K4 consumption** (`S8` §4): the two `slotK4Inst` instances share
    the template sort `α`, so `SortCoh σ pN (hA ▸ slotK4Inst pTpl hv hT)`
    and `SortCoh σ (hD ▸ slotK4Inst pTpl₂ hw hT) pD` join `uN` to `uD`
    through `α`. Conditional: the `SortCoh`s are the queries a producer
    must supply. -/
theorem slotKind_consume_k4 {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A D t v w A₀ : Expr Nat}
    {uN uD α γ : Level}
    (pN : TyP E n Γ A (.sort uN)) (pD : TyP E n Γ D (.sort uD))
    (pTpl : TyP E n (.letBinding t v :: Γ) A₀ (.sort α))
    (hv : TyP E n Γ v t) (hT : TyP E n Γ t (.sort γ))
    (pTpl₂ : TyP E n (.letBinding t w :: Γ) A₀ (.sort α))
    (hw : TyP E n Γ w t)
    (hA : instantiate0 v A₀ = A) (hD : instantiate0 w A₀ = D)
    (h₁ : SortCoh σ pN (hA ▸ slotK4Inst pTpl hv hT))
    (h₂ : SortCoh σ (hD ▸ slotK4Inst pTpl₂ hw hT) pD) :
    naturalBit σ uN = declarationBit σ uD :=
  levelIsZero_congr (eqN_trans h₁ h₂)

/-- The consumption entry point: a K4 provenance source plus ITS named
    queries yields `naturalBit = declarationBit`. `LevelSub σ` is a
    uniform premise, unused here. -/
theorem SlotKindSourceK4.consume {σ : Level → Level} (_hσ : LevelSub σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat} {uN : Level}
    {qa : TyP E n Γ a A} {pN : TyP E n Γ A (.sort uN)}
    {D : Expr Nat} {uD : Level} {pD : TyP E n Γ D (.sort uD)}
    (src : SlotKindSourceK4 qa pN pD) (q : src.queries σ) :
    naturalBit σ uN = declarationBit σ uD := by
  cases src with
  | letTemplate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact levelIsZero_congr (eqN_trans q.1 q.2)

/-- The two-step target on a K4 source (`S6` §1): the real `PBit qa pN`
    query plus the source's queries give `qa.eps σ ρ = .star ↔
    declarationBit = true`. -/
theorem slotK4Eps_iff_declarationBit {σ : Level → Level} (hσ : LevelSub σ)
    (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat} {uN : Level}
    {qa : TyP E n Γ a A} {pN : TyP E n Γ A (.sort uN)}
    {D : Expr Nat} {uD : Level} {pD : TyP E n Γ D (.sort uD)}
    (src : SlotKindSourceK4 qa pN pD) (q : src.queries σ)
    (hbit : PBit σ ρ qa pN) :
    qa.eps σ ρ = .star ↔ declarationBit σ uD = true :=
  Iff.trans hbit (iff_of_eq (congrArg (· = true) (src.consume hσ q)))

/-! ## §2 the per-atom payments (`S8` §4, `S6` §4)

K4's calls are paid per-atom off `C ++ [N]` with `N = orig.wt Aw` — the
retained original's weight. The receipt is a premise: the caller must
present the `occ` equation pinning the instance to `orig`'s path. -/

/-- K4's left call `C ++ pN.atoms ++ (slotK4Inst pTpl hv hT).atoms`
    descends from `C ++ [orig.wt Aw]`: the three receipts pin `pTpl`,
    `hv`, `hT` — the construction's exact atom-list components — into
    `orig`, and `hbnd` is the S8 §4 bound on that list (`S8` §4, `S6` §4). -/
theorem slotKind_k4_left_paid (Aw : Nat → Nat) (C : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A t v A₀ : Expr Nat}
    {uN α γ : Level} {pN : TyP E n Γ A (.sort uN)}
    {pTpl : TyP E n (.letBinding t v :: Γ) A₀ (.sort α)}
    {hv : TyP E n Γ v t} {hT : TyP E n Γ t (.sort γ)}
    {Γ₀ : LCtx} {x₀ y₀ T₀ : Expr Nat} {orig : CvP E n Γ₀ x₀ y₀ T₀}
    {pathT pathV pathS : List Nat}
    (_occT : DNode.subAt (.cv orig) pathT = some (.ty pTpl))
    (_occV : DNode.subAt (.cv orig) pathV = some (.ty hv))
    (_occS : DNode.subAt (.cv orig) pathS = some (.ty hT))
    (hbnd : ∀ x ∈ pTpl.atoms Aw ++ hv.atoms Aw ++ hT.atoms Aw,
        x < orig.wt Aw)
    (hpN : ∀ y ∈ pN.atoms Aw, y < orig.wt Aw) :
    DMStep (C ++ pN.atoms Aw ++ (slotK4Inst pTpl hv hT).atoms Aw)
      (C ++ [orig.wt Aw]) := by
  rw [slotK4Inst_atoms]
  exact slotKind_paid_pair C _ _ hpN hbnd

/-- K4's right call `C ++ (slotK4Inst pTpl₂ hw hT).atoms ++ pD.atoms`
    descends from `C ++ [orig.wt Aw]` on the same certificate. -/
theorem slotKind_k4_right_paid (Aw : Nat → Nat) (C : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {D t w A₀ : Expr Nat}
    {uD α γ : Level} {pD : TyP E n Γ D (.sort uD)}
    {pTpl₂ : TyP E n (.letBinding t w :: Γ) A₀ (.sort α)}
    {hw : TyP E n Γ w t} {hT : TyP E n Γ t (.sort γ)}
    {Γ₀ : LCtx} {x₀ y₀ T₀ : Expr Nat} {orig : CvP E n Γ₀ x₀ y₀ T₀}
    {pathT₂ pathW pathS : List Nat}
    (_occT₂ : DNode.subAt (.cv orig) pathT₂ = some (.ty pTpl₂))
    (_occW : DNode.subAt (.cv orig) pathW = some (.ty hw))
    (_occS : DNode.subAt (.cv orig) pathS = some (.ty hT))
    (hbnd' : ∀ x ∈ pTpl₂.atoms Aw ++ hw.atoms Aw ++ hT.atoms Aw,
        x < orig.wt Aw)
    (hpD : ∀ y ∈ pD.atoms Aw, y < orig.wt Aw) :
    DMStep (C ++ (slotK4Inst pTpl₂ hw hT).atoms Aw ++ pD.atoms Aw)
      (C ++ [orig.wt Aw]) := by
  rw [slotK4Inst_atoms]
  exact slotKind_paid_pair C _ _ hbnd' hpD

/-! ## §3 the K4 fixture and the foreign-template refusal

A concrete `CvP.zeta` original — `S8` §4's own "the original `hb` domain,
the real `hv`/`hA`" shape — whose children are literally the K4 fields:
`hA` the binder-type sort at child `[0]`, `hv` the stored-value typing at
`[1]`, `hb` the let-context template at `[2]` — `pTpl` IS `hb`.
`v = w = .bvar 0`, so the `w`-side fields (`pTpl₂`, `hw`)
are the same retained nodes — the degenerate `A = D` instance of the
general `v`/`w` view. -/

/-- `Γlet = [x := sort 0 := bvar 0]` — the let-binding context. -/
def k4LetCtx : LCtx := .letBinding (.sort .zero) (.bvar 0) :: occCtx

/-- The shared template `A₀ = sort 0 : sort 1` under the `sort 0`-valued
    let binder — the zeta's `hb` field itself (`pTpl = hb`), so the
    fixture keeps `body = sort 0` and never normalizes an `imax`. -/
def k4Tpl (n : Nat) :
    TyP emptyEnv n k4LetCtx (.sort .zero) (.sort (.succ .zero)) :=
  occSortH emptyEnv n k4LetCtx

/-- `sort 1 : sort 2` under `occCtx` — the `letE`'s `hT` leaf. -/
def k4SortS1 (n : Nat) :
    TyP emptyEnv n occCtx (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sort emptyEnv n occCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- The `zeta`'s `dl` — a `letE` typing `letE (sort 0) (bvar 0)
    (sort 0) : sort 1`. -/
def k4Dl (n : Nat) :
    TyP emptyEnv n occCtx
      (.letE (.sort .zero) (.bvar 0) (.sort .zero))
      (.sort (.succ .zero)) :=
  .letE emptyEnv n occCtx (.sort .zero) (.succ .zero) (.bvar 0)
    (.sort (.succ .zero)) (.sort .zero) (.succ (.succ .zero))
    (occSortH emptyEnv n occCtx) (occQA n) (k4Tpl n) (k4SortS1 n)

/-- The `zeta`'s `dr` — `instantiate0 (bvar 0) (sort 0) = sort 0 : sort 1`
    in `occCtx`. -/
def k4Dr (n : Nat) :
    TyP emptyEnv n occCtx (instantiate0 (.bvar 0) (.sort .zero))
      (.sort (.succ .zero)) :=
  occSortH emptyEnv n occCtx

/-- The retained original: a `zeta` over `letE (sort 0) (bvar 0)
    (sort 0)` — its `dchildren` are
    `[.ty hA, .ty hv, .ty k4Tpl, .ty k4Dl, .ty k4Dr]`; the let-context
    template `pTpl` IS `hb` at child `[2]`. -/
def k4Orig (n : Nat) :
    CvP emptyEnv n occCtx
      (.letE (.sort .zero) (.bvar 0) (.sort .zero))
      (instantiate0 (.bvar 0) (.sort .zero))
      (instantiate0 (.bvar 0) (.sort (.succ .zero))) :=
  .zeta emptyEnv n occCtx (.sort .zero) (.bvar 0)
    (.sort .zero) (.sort (.succ .zero)) (.succ .zero)
    (occSortH emptyEnv n occCtx) (occQA n) (k4Tpl n) (k4Dl n) (k4Dr n)

/-- The template receipt: `pTpl` IS the `zeta`'s `hb` — child `[2]` of
    `k4Orig`. -/
theorem k4Tpl_path (n : Nat) :
    DNode.subAt (.cv (k4Orig n)) [2] = some (.ty (k4Tpl n)) := rfl

/-- The value/binder-sort receipts: `hv` at `[1]`, `hT` at `[0]` — the
    `zeta`'s own `hv`/`hA` fields. -/
theorem k4Hv_path (n : Nat) :
    DNode.subAt (.cv (k4Orig n)) [1] = some (.ty (occQA n)) := rfl

theorem k4HT_path (n : Nat) :
    DNode.subAt (.cv (k4Orig n)) [0] =
      some (.ty (occSortH emptyEnv n occCtx)) := rfl

/-- A full `letTemplate` source built on the retained certificate: the
    degenerate `v = w = .bvar 0` case, so `pTpl₂ = pTpl`/`hw = hv`/`A =
    D = sort 0` and all `instantiate0` equations are `rfl`. Kernel
    values: `k4Orig.wt = 12` (`1 + 1 + 2 + 1 + 6 + 1`: `hA` 1, `hv` 2,
    `k4Tpl` 1, `k4Dl` 6, `k4Dr` 1); the S8 atom list `k4Tpl.atoms ++
    occQA.atoms ++ occSortH.atoms = [1,2,1]`; `slotK4Inst`'s wt
    `1 + 1 + 2 + 1 = 5`. -/
def k4SourceEx (n : Nat) :
    SlotKindSourceK4 (occQA n) (occSortTy n) (occSortTy n) :=
  .letTemplate (fun _ => 0)
    (k4Orig n)
    (k4Tpl n) (occQA n) (occSortH emptyEnv n occCtx)
    (k4Tpl n) (occQA n)
    [2] [1] [0] [2] [1]
    rfl rfl rfl rfl rfl rfl rfl
    (fun x hx => by
      have hw : (k4Orig n).wt (fun _ => 0) = 12 := rfl
      rw [hw]
      change x ∈ [1, 2, 1] at hx
      simp at hx
      omega)
    (fun x hx => by
      have hw : (k4Orig n).wt (fun _ => 0) = 12 := rfl
      rw [hw]
      change x ∈ [1, 2, 1] at hx
      simp at hx
      omega)

/-- The K4 queries of that source name the CONSTRUCTED instances —
    `slotK4Inst` over the retained fields — transported to the displayed
    domains. -/
theorem k4Source_queries (σ : Level → Level) (n : Nat) :
    (k4SourceEx n).queries σ =
      (SortCoh σ (occSortTy n)
        (slotK4Inst (k4Tpl n) (occQA n) (occSortH emptyEnv n occCtx)) ∧
        SortCoh σ (slotK4Inst (k4Tpl n) (occQA n) (occSortH emptyEnv n occCtx))
          (occSortTy n)) := rfl

/-- `sort 1 : sort 2` under the let context — the conv's `h`/`dl`/`dr`
    leaf for the foreign template. -/
def k4TplS1Let (n : Nat) :
    TyP emptyEnv n k4LetCtx (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sort emptyEnv n k4LetCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- The conv's certificate: `sort 1 ≡ sort 1 : sort 2` in the let ctx. -/
def k4TplConvC (n : Nat) :
    CvP emptyEnv n k4LetCtx (.sort (.succ .zero)) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) :=
  .refl emptyEnv n k4LetCtx (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) (k4TplS1Let n) (k4TplS1Let n) (k4TplS1Let n)

/-- **Foreign template**: a `.conv` node typing `sort 0 : sort 1` in
    `k4LetCtx` — the SAME judgment as `k4Tpl`, but a different node
    (`wt 6 ≠ 1`). -/
def k4TplForeign (n : Nat) :
    TyP emptyEnv n k4LetCtx (.sort .zero) (.sort (.succ .zero)) :=
  .conv emptyEnv n k4LetCtx (.sort .zero) (.sort (.succ .zero))
    (.sort (.succ .zero)) (.succ (.succ .zero)) (k4Tpl n) (k4TplConvC n)

/-- The retained template is lighter than the conv-wrapper — the
    discrimination the receipt relies on. -/
theorem k4Tpl_ne_foreign (n : Nat) : k4Tpl n ≠ k4TplForeign n := by
  intro he
  have hw : (k4Tpl n).wt (fun _ => 0) = (k4TplForeign n).wt (fun _ => 0) :=
    congrArg (fun D => D.wt (fun _ => 0)) he
  have h1 : (k4Tpl n).wt (fun _ => 0) = 1 := rfl
  have h6 : (k4TplForeign n).wt (fun _ => 0) = 6 := rfl
  rw [h1, h6] at hw
  exact absurd hw (by decide)

/-- **CONTROL (`S8` §4)**: the foreign same-judgment let-context template
    is refused at the template's path — `subAt` resolves `[2]` to
    `k4Tpl`, never to the conv-wrapper. -/
theorem k4_template_foreign_refused (n : Nat) :
    DNode.subAt (.cv (k4Orig n)) [2] ≠ some (.ty (k4TplForeign n)) := by
  intro h
  rw [k4Tpl_path n] at h
  have h2 : DNode.ty (k4Tpl n) = DNode.ty (k4TplForeign n) := Option.some.inj h
  obtain ⟨_, _, _, _, _, hheq⟩ := DNode.ty.inj h2
  exact k4Tpl_ne_foreign n (eq_of_heq hheq)

end Rcic.Syn

#print axioms Rcic.Syn.slotK4Inst
#print axioms Rcic.Syn.atoms_lsub
#print axioms Rcic.Syn.slotK4Inst_atoms
#print axioms Rcic.Syn.slotK4Inst_wt
#print axioms Rcic.Syn.SlotKindSourceK4
#print axioms Rcic.Syn.SlotKindSourceK4.queries
#print axioms Rcic.Syn.slotKind_consume_k4
#print axioms Rcic.Syn.SlotKindSourceK4.consume
#print axioms Rcic.Syn.slotK4Eps_iff_declarationBit
#print axioms Rcic.Syn.slotKind_k4_left_paid
#print axioms Rcic.Syn.slotKind_k4_right_paid
#print axioms Rcic.Syn.k4LetCtx
#print axioms Rcic.Syn.k4Tpl
#print axioms Rcic.Syn.k4SortS1
#print axioms Rcic.Syn.k4Dl
#print axioms Rcic.Syn.k4Dr
#print axioms Rcic.Syn.k4Orig
#print axioms Rcic.Syn.k4Tpl_path
#print axioms Rcic.Syn.k4Hv_path
#print axioms Rcic.Syn.k4HT_path
#print axioms Rcic.Syn.k4SourceEx
#print axioms Rcic.Syn.k4Source_queries
#print axioms Rcic.Syn.k4TplS1Let
#print axioms Rcic.Syn.k4TplConvC
#print axioms Rcic.Syn.k4TplForeign
#print axioms Rcic.Syn.k4Tpl_ne_foreign
#print axioms Rcic.Syn.k4_template_foreign_refused
