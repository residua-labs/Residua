import rcic.RcicSynSlotKind
import rcic.RcicSynInstEnd
import rcic.RcicSynRedex

/-!
# T12 (K3): `SlotKindSourceK3` — SameTemplateSort

`research/rcic/sortrow/S7_ORIGINAL_DOMAIN_KIND_TRACE.md` §5 (the T12
K-stage plan; K3 proposed there). For β paths sharing an **original Π
template**, the template's domain sort transports directly — no typed
domain conversion is synthesized and no Π-injectivity is invoked:

* the real template `pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α)`,
* `hC : TyP E n Γ C (.sort γ)` and the argument typings `ha`, `hb`,
* the two original lazy substitutions `pA : A₀[a] : sort α`,
  `pB : A₀[b] : sort α` — both at sort **literally** `α`,

so `naturalBit = declarationBit` follows through the shared `α` as two
same-subject A6 queries, exactly K1's consumption shape. Even when
`A₀[a] ≠ A₀[b]` the kind equation holds — **K3 is not a constructor for
arbitrary domain conversions**: without an actual `a ≡ b` it only says
two legal instances share a sort kind (`S7` §5, verbatim constraint).

Like the K1 repair (Q198/P2), every retained input carries its
**occurrence receipt** into the retained original `orig`: `DNode.subAt`
resolves each input's own child-index `path` to the node itself, and the
atom bounds are against `orig.wt` — the original `N` of `S6` §4 / `S7`
§5's "fields inside a real β/application path of `Hι`, `N` pays per
atom". A caller cannot present a fresh same-judgment node for any field.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the K3 lazy instance and the SameTemplateSort source (`S7` §5) -/

/-- The K3 lazy instance built from the retained fields: `instEnd` —
    `esub` at binder `0` through the `castLift0`/`sortLift0`/`tyCast`
    transport stack — gives `A₀[a] : sort α`, one of the "two original
    lazy substitutions" of `S7` §5. `SlotKindSourceK3.sameTemplate`'s
    instances ARE this construction over the retained fields — never
    free-standing typings. -/
def slotK3Inst {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {C A₀ a : Expr Nat} {α γ : Level}
    (pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α))
    (hC : TyP E n Γ C (.sort γ)) (ha : TyP E n Γ a C) :
    TyP E n Γ (instantiate0 a A₀) (.sort α) :=
  instEnd pTpl ha hC

/-- `S7` §5's atom count, literally: the `tyCast` transports preserve
    atoms (`atoms_tyCast`), so the instance's atom list is exactly
    `pTpl.atoms ++ argument.atoms ++ hC.atoms`. -/
theorem slotK3Inst_atoms (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {C A₀ a : Expr Nat} {α γ : Level}
    (pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α))
    (hC : TyP E n Γ C (.sort γ)) (ha : TyP E n Γ a C) :
    (slotK3Inst pTpl hC ha).atoms Aw =
      pTpl.atoms Aw ++ ha.atoms Aw ++ hC.atoms Aw := by
  have h : slotK3Inst pTpl hC ha = instEnd pTpl ha hC := rfl
  rw [h]
  simp only [instEnd, atoms_tyCast, atoms_esub, castLift0, sortLift0]

/-- The same for weight: `1 + pTpl.wt + ha.wt + hC.wt`. -/
theorem slotK3Inst_wt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {C A₀ a : Expr Nat} {α γ : Level}
    (pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α))
    (hC : TyP E n Γ C (.sort γ)) (ha : TyP E n Γ a C) :
    (slotK3Inst pTpl hC ha).wt Aw =
      1 + pTpl.wt Aw + ha.wt Aw + hC.wt Aw := by
  have h : slotK3Inst pTpl hC ha = instEnd pTpl ha hC := rfl
  rw [h, instEnd_wt]

/-- The K3 provenance view — indexed by `qa`, its natural sort typing
    `pN`, and the declaration-domain sort typing `pD`, exactly like
    `SlotKindSource`. `sameTemplate` retains the template, the binder
    sort, and both argument typings, each with its own occurrence path
    and receipt into `orig`, the displayed-domain equations, and the
    per-side atom bounds of `S7` §5 — never the conclusion
    `naturalBit = declarationBit`. -/
inductive SlotKindSourceK3 {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a A : Expr Nat} {uN : Level}
    (qa : TyP E n Γ a A) (pN : TyP E n Γ A (.sort uN))
    {D : Expr Nat} {uD : Level} (pD : TyP E n Γ D (.sort uD)) : Type where
  /-- **K3 — SameTemplateSort**: `A` and `D` are two instances of ONE
      original template `A₀` under `.assumption C`, at arguments `a`/`b`
      (`S7` §5). `orig` is the original β/application-path conversion;
      each retained field (`pTpl`, `hC`, `ha`, `hb`) is pinned inside
      `orig` by its own `DNode.subAt` receipt. The two lazy instances are
      NOT fields — they are `slotK3Inst pTpl hC ha` / `slotK3Inst pTpl hC
      hb`, the `instEnd`/`esub` construction over the retained template,
      linked to it definitionally (Q199/P2); `slotK3Inst_atoms` shows the
      construction's atom list is exactly `S7` §5's
      `pTpl.atoms ++ argument.atoms ++ hC.atoms`, and `hbnd`/`hbnd'` bound
      those lists by `orig.wt`. -/
  | sameTemplate {C A₀ a' b' : Expr Nat} {α γ : Level}
      {Γ₀ : LCtx} {x₀ y₀ T₀ : Expr Nat}
      (Aw : Nat → Nat)
      (orig : CvP E n Γ₀ x₀ y₀ T₀)
      (pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α))
      (hC : TyP E n Γ C (.sort γ))
      (ha : TyP E n Γ a' C) (hb : TyP E n Γ b' C)
      (pathT pathA pathB pathC : List Nat)
      (occT : DNode.subAt (.cv orig) pathT = some (.ty pTpl))
      (occA : DNode.subAt (.cv orig) pathA = some (.ty ha))
      (occB : DNode.subAt (.cv orig) pathB = some (.ty hb))
      (occC : DNode.subAt (.cv orig) pathC = some (.ty hC))
      (hA : instantiate0 a' A₀ = A) (hD : instantiate0 b' A₀ = D)
      (hbnd : ∀ x ∈ pTpl.atoms Aw ++ ha.atoms Aw ++ hC.atoms Aw,
          x < orig.wt Aw)
      (hbnd' : ∀ x ∈ pTpl.atoms Aw ++ hb.atoms Aw ++ hC.atoms Aw,
          x < orig.wt Aw) :
      SlotKindSourceK3 qa pN pD

/-- The smaller A6 queries a K3 source consumes: `pN` against the `a`-
    instance transported to `A`, and the `b`-instance transported to `D`
    against `pD` — two same-subject `SortCoh`s through the shared `α`
    (`S7` §5). -/
def SlotKindSourceK3.queries (σ : Level → Level)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat} {uN : Level}
    {qa : TyP E n Γ a A} {pN : TyP E n Γ A (.sort uN)}
    {D : Expr Nat} {uD : Level} {pD : TyP E n Γ D (.sort uD)} :
    SlotKindSourceK3 qa pN pD → Prop
  | .sameTemplate _ _ pTpl hC ha hb _ _ _ _ _ _ _ _ hA hD _ _ =>
      SortCoh σ pN (hA ▸ slotK3Inst pTpl hC ha) ∧
        SortCoh σ (hD ▸ slotK3Inst pTpl hC hb) pD

/-- **K3 consumption** (`S7` §5): the two `slotK3Inst` instances share
    the template sort `α`, so `SortCoh σ pN (hA ▸ slotK3Inst pTpl hC ha)`
    and `SortCoh σ (hD ▸ slotK3Inst pTpl hC hb) pD` join `uN` to `uD`
    through `α`. Conditional: the `SortCoh`s are the queries a producer
    must supply. -/
theorem slotKind_consume_k3 {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A D C A₀ a' b' : Expr Nat}
    {uN uD α γ : Level}
    (pN : TyP E n Γ A (.sort uN)) (pD : TyP E n Γ D (.sort uD))
    (pTpl : TyP E n (.assumption C :: Γ) A₀ (.sort α))
    (hC : TyP E n Γ C (.sort γ))
    (ha : TyP E n Γ a' C) (hb : TyP E n Γ b' C)
    (hA : instantiate0 a' A₀ = A) (hD : instantiate0 b' A₀ = D)
    (h₁ : SortCoh σ pN (hA ▸ slotK3Inst pTpl hC ha))
    (h₂ : SortCoh σ (hD ▸ slotK3Inst pTpl hC hb) pD) :
    naturalBit σ uN = declarationBit σ uD :=
  levelIsZero_congr (eqN_trans h₁ h₂)

/-- The consumption entry point: a K3 provenance source plus ITS named
    queries yields `naturalBit = declarationBit`. `LevelSub σ` is a
    uniform premise, unused here. -/
theorem SlotKindSourceK3.consume {σ : Level → Level} (_hσ : LevelSub σ)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat} {uN : Level}
    {qa : TyP E n Γ a A} {pN : TyP E n Γ A (.sort uN)}
    {D : Expr Nat} {uD : Level} {pD : TyP E n Γ D (.sort uD)}
    (src : SlotKindSourceK3 qa pN pD) (q : src.queries σ) :
    naturalBit σ uN = declarationBit σ uD := by
  cases src with
  | sameTemplate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      exact levelIsZero_congr (eqN_trans q.1 q.2)

/-- The two-step target on a K3 source (`S6` §1): the real `PBit qa pN`
    query plus the source's queries give `qa.eps σ ρ = .star ↔
    declarationBit = true`. -/
theorem slotK3Eps_iff_declarationBit {σ : Level → Level} (hσ : LevelSub σ)
    (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat} {uN : Level}
    {qa : TyP E n Γ a A} {pN : TyP E n Γ A (.sort uN)}
    {D : Expr Nat} {uD : Level} {pD : TyP E n Γ D (.sort uD)}
    (src : SlotKindSourceK3 qa pN pD) (q : src.queries σ)
    (hbit : PBit σ ρ qa pN) :
    qa.eps σ ρ = .star ↔ declarationBit σ uD = true :=
  Iff.trans hbit (iff_of_eq (congrArg (· = true) (src.consume hσ q)))

/-! ## §2 the per-atom payments (`S7` §5, `S6` §4)

K3's calls are paid per-atom off `C ++ [N]` with `N = orig.wt Aw` — the
retained original's weight. The receipt is a premise: the caller must
present the `occ` equation pinning the instance to `orig`'s path. -/

/-- K3's left call `C ++ pN.atoms ++ (slotK3Inst pTpl hC ha).atoms`
    descends from `C ++ [orig.wt Aw]`: the three receipts pin `pTpl`,
    `ha`, `hC` — the construction's exact atom-list components — into
    `orig`, and `hb` is the S7 §5 bound on that list (`S7` §5, `S6` §4). -/
theorem slotKind_k3_left_paid (Aw : Nat → Nat) (C : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A D₀ A₀ a' : Expr Nat}
    {uN α γ : Level} {pN : TyP E n Γ A (.sort uN)}
    {pTpl : TyP E n (.assumption D₀ :: Γ) A₀ (.sort α)}
    {hC : TyP E n Γ D₀ (.sort γ)} {ha : TyP E n Γ a' D₀}
    {Γ₀ : LCtx} {x₀ y₀ T₀ : Expr Nat} {orig : CvP E n Γ₀ x₀ y₀ T₀}
    {pathT pathA pathC : List Nat}
    (_occT : DNode.subAt (.cv orig) pathT = some (.ty pTpl))
    (_occA : DNode.subAt (.cv orig) pathA = some (.ty ha))
    (_occC : DNode.subAt (.cv orig) pathC = some (.ty hC))
    (hb : ∀ x ∈ pTpl.atoms Aw ++ ha.atoms Aw ++ hC.atoms Aw,
        x < orig.wt Aw)
    (hpN : ∀ y ∈ pN.atoms Aw, y < orig.wt Aw) :
    DMStep (C ++ pN.atoms Aw ++ (slotK3Inst pTpl hC ha).atoms Aw)
      (C ++ [orig.wt Aw]) := by
  rw [slotK3Inst_atoms]
  exact slotKind_paid_pair C _ _ hpN hb

/-- K3's right call `C ++ (slotK3Inst pTpl hC hb).atoms ++ pD.atoms`
    descends from `C ++ [orig.wt Aw]` on the same certificate. -/
theorem slotKind_k3_right_paid (Aw : Nat → Nat) (C : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {D D₀ A₀ b' : Expr Nat}
    {uD α γ : Level} {pD : TyP E n Γ D (.sort uD)}
    {pTpl : TyP E n (.assumption D₀ :: Γ) A₀ (.sort α)}
    {hC : TyP E n Γ D₀ (.sort γ)} {hb : TyP E n Γ b' D₀}
    {Γ₀ : LCtx} {x₀ y₀ T₀ : Expr Nat} {orig : CvP E n Γ₀ x₀ y₀ T₀}
    {pathT pathB pathC : List Nat}
    (_occT : DNode.subAt (.cv orig) pathT = some (.ty pTpl))
    (_occB : DNode.subAt (.cv orig) pathB = some (.ty hb))
    (_occC : DNode.subAt (.cv orig) pathC = some (.ty hC))
    (hbnd : ∀ x ∈ pTpl.atoms Aw ++ hb.atoms Aw ++ hC.atoms Aw,
        x < orig.wt Aw)
    (hpD : ∀ y ∈ pD.atoms Aw, y < orig.wt Aw) :
    DMStep (C ++ (slotK3Inst pTpl hC hb).atoms Aw ++ pD.atoms Aw)
      (C ++ [orig.wt Aw]) := by
  rw [slotK3Inst_atoms]
  exact slotKind_paid_pair C _ _ hbnd hpD

/-! ## §3 the K3 fixture and the foreign-template refusal

A concrete `CvP.fsub` original — `S7` §5's own "the real path also
carries `hab`" shape — whose children are literally the K3 fields:
`hB` the template at child `[0]`, `hA` the binder sort at `[1]`, `dl`/`dr`
the lazy instances at `[3]`/`[4]`, and `hab`'s `refl` children the two
argument typings at `[2, i]`. -/

/-- `ctx = [y : sort 0, x : sort 0]` — the template's context. -/
def k3Ctx : LCtx := .assumption (.sort .zero) :: occCtx

/-- The shared template `A₀ = sort 0 : sort 1` under the `sort 0`
    binder — `α = succ zero` in this fixture. -/
def k3Tpl (n : Nat) : TyP emptyEnv n k3Ctx (.sort .zero) (.sort (.succ .zero)) :=
  occSortH emptyEnv n k3Ctx

/-- The `hab : .bvar 0 ≡ .bvar 0 : sort 0` inside the fixture's `fsub`. -/
def k3Hab (n : Nat) :
    CvP emptyEnv n occCtx (.bvar 0) (.bvar 0) (.sort .zero) :=
  .refl emptyEnv n occCtx (.bvar 0) (.sort .zero)
    (occQA n) (occQA n) (occQA n)

/-- The retained original: an `fsub` over the `sort 0` binder —
    `B = sort 0`, `S = sort 1`, `a = b = .bvar 0`. Its judgment is
    `sort 0 ≡ sort 0 : sort 1`; its `dchildren` are
    `[.ty k3Tpl, .ty hC, .cv k3Hab, .ty inst, .ty inst]` where `inst` is
    literally `slotK3Inst (k3Tpl n) (occSortTy n) (occQA n)` — the lazy
    instances inside the original ARE the `instEnd`/`esub` construction
    over the retained fields. -/
def k3Orig (n : Nat) :
    CvP emptyEnv n occCtx (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .fsub emptyEnv n occCtx (.sort .zero) (.sort .zero) (.sort (.succ .zero))
    (.bvar 0) (.bvar 0) (.succ .zero)
    (k3Tpl n) (occSortTy n) (k3Hab n)
    (slotK3Inst (k3Tpl n) (occSortTy n) (occQA n))
    (slotK3Inst (k3Tpl n) (occSortTy n) (occQA n))

/-- The template receipt: child `[0]` of `k3Orig` is `.ty k3Tpl`. -/
theorem k3Tpl_path (n : Nat) :
    DNode.subAt (.cv (k3Orig n)) [0] = some (.ty (k3Tpl n)) := rfl

/-- The instance receipts: `dl`/`dr` at `[3]`/`[4]` are the
    `slotK3Inst` construction itself. -/
theorem k3InstA_path (n : Nat) :
    DNode.subAt (.cv (k3Orig n)) [3] =
      some (.ty (slotK3Inst (k3Tpl n) (occSortTy n) (occQA n))) := rfl

theorem k3InstB_path (n : Nat) :
    DNode.subAt (.cv (k3Orig n)) [4] =
      some (.ty (slotK3Inst (k3Tpl n) (occSortTy n) (occQA n))) := rfl

/-- A full `sameTemplate` source built on the retained certificate:
    `A = D = sort 0`, `a = b = .bvar 0`, both `instantiate0` equations
    `rfl`. Kernel values: `k3Orig.wt = 20` (`1 + 1 + 1 + 7 + 5 + 5`, the
    two `slotK3Inst`s weighing `1 + 1 + 2 + 1 = 5` each); the S7 §5 atom
    list `k3Tpl.atoms ++ occQA.atoms ++ occSortTy.atoms = [1,2,1]`. -/
def k3SourceEx (n : Nat) :
    SlotKindSourceK3 (occQA n) (occSortTy n) (occSortTy n) :=
  .sameTemplate (fun _ => 0)
    (k3Orig n)
    (k3Tpl n) (occSortTy n) (occQA n) (occQA n)
    [0] [2, 0] [2, 1] [1]
    rfl rfl rfl rfl rfl rfl
    (fun x hx => by
      have hw : (k3Orig n).wt (fun _ => 0) = 20 := by
        show 1 + (k3Tpl n).wt _ + (occSortTy n).wt _ + (k3Hab n).wt _ +
          (slotK3Inst (k3Tpl n) (occSortTy n) (occQA n)).wt _ +
          (slotK3Inst (k3Tpl n) (occSortTy n) (occQA n)).wt _ = 20
        rw [slotK3Inst_wt]
        rfl
      rw [hw]
      change x ∈ [1, 2, 1] at hx
      simp at hx
      omega)
    (fun x hx => by
      have hw : (k3Orig n).wt (fun _ => 0) = 20 := by
        show 1 + (k3Tpl n).wt _ + (occSortTy n).wt _ + (k3Hab n).wt _ +
          (slotK3Inst (k3Tpl n) (occSortTy n) (occQA n)).wt _ +
          (slotK3Inst (k3Tpl n) (occSortTy n) (occQA n)).wt _ = 20
        rw [slotK3Inst_wt]
        rfl
      rw [hw]
      change x ∈ [1, 2, 1] at hx
      simp at hx
      omega)

/-- The K3 queries of that source name the CONSTRUCTED instances —
    `slotK3Inst` over the retained fields — transported to the displayed
    domains. -/
theorem k3Source_queries (σ : Level → Level) (n : Nat) :
    (k3SourceEx n).queries σ =
      (SortCoh σ (occSortTy n)
        (slotK3Inst (k3Tpl n) (occSortTy n) (occQA n)) ∧
        SortCoh σ (slotK3Inst (k3Tpl n) (occSortTy n) (occQA n))
          (occSortTy n)) := rfl

/-- `sort 0 : sort 2` under the fixture context — the conv's `h`/`dl`/`dr`
    leaf for the foreign template. -/
def k3TplS1 (n : Nat) :
    TyP emptyEnv n k3Ctx (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sort emptyEnv n k3Ctx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- The conv's certificate: `sort 1 ≡ sort 1 : sort 2`. -/
def k3TplConvC (n : Nat) :
    CvP emptyEnv n k3Ctx (.sort (.succ .zero)) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) :=
  .refl emptyEnv n k3Ctx (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
    (k3TplS1 n) (k3TplS1 n) (k3TplS1 n)

/-- **Foreign template**: a `.conv` node typing `sort 0 : sort 1` in
    `k3Ctx` — the SAME judgment as `k3Tpl`, but a different node
    (`wt 6 ≠ 1`). -/
def k3TplForeign (n : Nat) :
    TyP emptyEnv n k3Ctx (.sort .zero) (.sort (.succ .zero)) :=
  .conv emptyEnv n k3Ctx (.sort .zero) (.sort (.succ .zero))
    (.sort (.succ .zero)) (.succ (.succ .zero)) (k3Tpl n) (k3TplConvC n)

/-- The retained template is lighter than the conv-wrapper — the
    discrimination the receipt relies on. -/
theorem k3Tpl_ne_foreign (n : Nat) : k3Tpl n ≠ k3TplForeign n := by
  intro he
  have hw : (k3Tpl n).wt (fun _ => 0) = (k3TplForeign n).wt (fun _ => 0) :=
    congrArg (fun D => D.wt (fun _ => 0)) he
  have h1 : (k3Tpl n).wt (fun _ => 0) = 1 := rfl
  have h6 : (k3TplForeign n).wt (fun _ => 0) = 6 := rfl
  rw [h1, h6] at hw
  exact absurd hw (by decide)

/-- **CONTROL (`S7` §5)**: the foreign same-judgment template is refused
    at the template's path — `subAt` resolves `[0]` to `k3Tpl`, never to
    the conv-wrapper. -/
theorem k3_template_foreign_refused (n : Nat) :
    DNode.subAt (.cv (k3Orig n)) [0] ≠ some (.ty (k3TplForeign n)) := by
  intro h
  rw [k3Tpl_path n] at h
  have h2 : DNode.ty (k3Tpl n) = DNode.ty (k3TplForeign n) := Option.some.inj h
  obtain ⟨_, _, _, _, _, hheq⟩ := DNode.ty.inj h2
  exact k3Tpl_ne_foreign n (eq_of_heq hheq)

end Rcic.Syn

#print axioms Rcic.Syn.slotK3Inst
#print axioms Rcic.Syn.slotK3Inst_atoms
#print axioms Rcic.Syn.slotK3Inst_wt
#print axioms Rcic.Syn.SlotKindSourceK3
#print axioms Rcic.Syn.SlotKindSourceK3.queries
#print axioms Rcic.Syn.slotKind_consume_k3
#print axioms Rcic.Syn.SlotKindSourceK3.consume
#print axioms Rcic.Syn.slotK3Eps_iff_declarationBit
#print axioms Rcic.Syn.slotKind_k3_left_paid
#print axioms Rcic.Syn.slotKind_k3_right_paid
#print axioms Rcic.Syn.k3Ctx
#print axioms Rcic.Syn.k3Tpl
#print axioms Rcic.Syn.k3Hab
#print axioms Rcic.Syn.k3Orig
#print axioms Rcic.Syn.k3Tpl_path
#print axioms Rcic.Syn.k3InstA_path
#print axioms Rcic.Syn.k3InstB_path
#print axioms Rcic.Syn.k3SourceEx
#print axioms Rcic.Syn.k3Source_queries
#print axioms Rcic.Syn.k3TplS1
#print axioms Rcic.Syn.k3TplConvC
#print axioms Rcic.Syn.k3TplForeign
#print axioms Rcic.Syn.k3Tpl_ne_foreign
#print axioms Rcic.Syn.k3_template_foreign_refused
