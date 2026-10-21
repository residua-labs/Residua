import rcic.RcicF8JLamLift
import rcic.RcicSortUniqueRows

/-!
# `RcicF8JLamLiftPins` — concrete fixtures and teeth for J-LAM-FIXED (§7)

Concrete stars/literals on `emptyEnv` exercising: the lift-domain predicate
(both directions on `wk`), the frame/lift on an actual multi-step child path
built from GENUINE `sortEq` producer moves (nonidentity level pairs — the
audit controls asked for no `trans(refl, refl)` stand-ins), the extractor
accept/reject boundary, and the §7/§8 mutants diverging where they must —
including the refused domain-free kit (`LamLiftOpsMut`), uninhabitable
in-tree, and the leaf-mutant's REAL inequality discharged against lit-rooted
formation evidence.

This repair lands the audit's second refusal too: `PinLamStep`/`pinFam` is a
concrete pre-`EvParX` producer family the kit's `F` instantiates at — the
lift's output then lives in `EvStarG`/`ValleyG`, never in the preserved old
`EvPar`. `pinStepLift`/`pinConvLift` demonstrate the two contract halves that
ARE inhabitable pointwise today (`stepLift`'s λ-step node inside `pinFam`'s
own carrier; `convLift` by the landed `EvTc.piCod`), and
`refused_evParCarrier_uninhabitable` reproduces the auditor's
`∀ R, LamLiftOps R → False` on the old carrier VERBATIM — `SortUnique`
discharged unconditionally at `emptyEnv` (`EnvWfT.empty.InScope` is `True`),
specializing to the committed `litRoots` fixture.
-/

set_option autoImplicit false
namespace Rcic.Declarative.F8Measure.JLam.Pins

/-- `S₀ : S₁` in the empty context. -/
def tyS0 : HasTyT emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  .sort [] .zero

/-- the original `ConvT.lam` introduction this slice reads: domain `S₀ ↔ S₀`,
    body `x₀ ↔ x₀`, codomain index the explicit sort `S₀`. -/
def lamLit : ConvT emptyEnv 0 [] (.lam (.sort .zero) (.bvar 0))
    (.lam (.sort .zero) (.bvar 0)) (.pi (.sort .zero) (.sort .zero)) :=
  .lam [] (.sort .zero) (.sort .zero) (.bvar 0) (.bvar 0) (.sort .zero)
    (.succ .zero) (.refl [] _ _ tyS0)
    (.refl _ _ _ (.bvar _ 0 (.sort .zero) rfl))

/-- a `.lam` literal whose body index is a Π, not a sort — the §7 "wrong λ
    left Π index" shape. -/
def litBadB : ConvT emptyEnv 0 []
    (.lam (.sort .zero) (.lam (.sort .zero) (.bvar 0)))
    (.lam (.sort .zero) (.lam (.sort .zero) (.bvar 0)))
    (.pi (.sort .zero) (.pi (.sort .zero) (.sort .zero))) :=
  .lam [] (.sort .zero) (.sort .zero) (.lam (.sort .zero) (.bvar 0))
    (.lam (.sort .zero) (.bvar 0)) (.pi (.sort .zero) (.sort .zero))
    (.succ .zero) (.refl [] _ _ tyS0)
    (.refl _ _ _ (.lam _ (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
      (.sort _ .zero) (.bvar _ 0 (.sort .zero) rfl)))

/-- a `.lam` literal whose domain conversion is legitimate but CHANGES the
    domain syntax (`S₀ ↔ sort (max 0 0)`) — `lamFixedB` requires `A' = A`
    syntactically, so this is the changed-domain reject. -/
def litDomChg : ConvT emptyEnv 0 []
    (.lam (.sort .zero) (.bvar 0))
    (.lam (.sort (.max .zero .zero)) (.bvar 0))
    (.pi (.sort .zero) (.sort .zero)) :=
  .lam [] (.sort .zero) (.sort (.max .zero .zero)) (.bvar 0) (.bvar 0)
    (.sort .zero) (.succ .zero)
    (.sorts _ _ _ (fun _ => rfl))
    (.refl _ _ _ (.bvar _ 0 (.sort .zero) rfl))

def litRoots : List (Jd emptyEnv 0) := [.cv lamLit]
def badRoots : List (Jd emptyEnv 0) := [.cv litBadB]
def chgRoots : List (Jd emptyEnv 0) := [.cv litDomChg]
def tyRoots : List (Jd emptyEnv 0) := [.ty tyS0]

def litSub : ∃ r ∈ litRoots, SubEq (.cv lamLit) r := ⟨_, .head _, .inl rfl⟩
def badSub : ∃ r ∈ badRoots, SubEq (.cv litBadB) r := ⟨_, .head _, .inl rfl⟩
def chgSub : ∃ r ∈ chgRoots, SubEq (.cv litDomChg) r := ⟨_, .head _, .inl rfl⟩
def tySub : ∃ r ∈ tyRoots, SubEq (.ty tyS0) r := ⟨_, .head _, .inl rfl⟩

/-! ### the domain-formation supplies (the audit's `hA` premise) -/

/-- the binder's domain formation `S₀ : S₁` in the EMPTY ambient context —
    the premise `HasTyT.lam`/`EvTc.piCod`/`LamPayload.hA` all carry; leaf-free
    here (`EvTy.sort`). -/
def domS0 : EvTy litRoots [] (.sort .zero) (.sort (.succ .zero)) :=
  .sort .zero

/-- the same domain formation inside a one-decl ambient context — the `hdom`
    the `wkOkStar` lift needs (there `Γ = [x₀ : S₀]`). -/
def domS0_ctx : EvTy litRoots [.assumption (.sort .zero)]
    (.sort .zero) (.sort (.succ .zero)) :=
  .sort .zero

/-- the child binder's own formation inside `wkOkStar` — the `.wk` supply
    component `LamDomT` demands: `S₀ : S₁` in the child's `Γ₀' = []`. -/
def domS0_child : EvTy litRoots [] (.sort .zero) (.sort (.succ .zero)) :=
  .sort .zero

/-- lit-rooted formation at `tyRoots`: identical typing, but `leaves =
    [.ty tyS0]` — the visible cost the leaf-mutant drops. -/
def domS0_lit : EvTy tyRoots [] (.sort .zero) (.sort (.succ .zero)) :=
  .lit tyS0 tySub

/-- the binder-context variable typing used by the fixtures. -/
def bodyVar : EvTy litRoots [.assumption (.sort .zero)] (.bvar 0)
    (.sort .zero) :=
  .var 0 (.sort .zero) rfl

/-- the same point rooted at `tyRoots` — the carrier for the lit-rooted
    leaf-divergence tooth. -/
def tyBodyVar : EvTy tyRoots [.assumption (.sort .zero)] (.bvar 0)
    (.sort .zero) :=
  .var 0 (.sort .zero) rfl

/-- a single-point child star under the binder: `x₀ ⇝ x₀` at `x₀ : S₀`. -/
def bodyStar : EvParStar litRoots [.assumption (.sort .zero)]
    (.bvar 0) (.bvar 0) (.sort .zero) :=
  .refl bodyVar

/-- a single-point child star rooted at `tyRoots`. -/
def tyBodyStar : EvParStar tyRoots [.assumption (.sort .zero)]
    (.bvar 0) (.bvar 0) (.sort .zero) :=
  .refl tyBodyVar

/-! ### genuine nonidentity `sortEq` moves (audit control) -/

/-- four pairwise-distinct levels, all evaluating to `1` — the nonidentity
    sort moves (`pin_l₁`/`pin_l₂` idiom, kept local). -/
def lvA : Level := .succ .zero
def lvB : Level := .max (.succ .zero) .zero
def lvC : Level := .max .zero (.succ .zero)
def lvD : Level := .max (.succ .zero) (.succ .zero)

def lvAB_eqN : eqN lvA lvB := fun _ => rfl
def lvAC_eqN : eqN lvA lvC := fun _ => rfl
def lvAD_eqN : eqN lvA lvD := fun _ => rfl
def lvBC_eqN : eqN lvB lvC := fun _ => rfl
def lvBD_eqN : eqN lvB lvD := fun _ => rfl
def lvDC_eqN : eqN lvD lvC := fun _ => rfl
theorem lvAB_ne : lvA ≠ lvB := by decide
theorem lvAC_ne : lvA ≠ lvC := by decide
theorem lvBC_ne : lvB ≠ lvC := by decide
theorem lvBD_ne : lvB ≠ lvD := by decide
theorem lvDC_ne : lvD ≠ lvC := by decide

/-- genuine `sortEq` producer move `sort lvA ⇝ sort lvB` at `sort (succ lvA)`
    under the binder (`ofSorts` idiom, leaf-free). -/
def stepAB : EvPar litRoots [.assumption (.sort .zero)]
    (.sort lvA) (.sort lvB) (.sort (.succ lvA)) :=
  EvPar.ofSorts _ lvA lvB lvAB_eqN

/-- `sort lvB ⇝ sort lvC` at the COMMON valley index `sort (succ lvA)` —
    `T₀ = sort (succ lvA)` with a `refl` re-index and both endpoints typed by
    `sortsRight`. -/
def stepBC : EvPar litRoots [.assumption (.sort .zero)]
    (.sort lvB) (.sort lvC) (.sort (.succ lvA)) :=
  .sortEq { T₀ := .sort (.succ lvA), h := lvBC_eqN,
            hl := .sortsRight lvA lvB lvAB_eqN,
            hr := .sortsRight lvA lvC lvAC_eqN,
            idx := .refl _ _ }

/-- `sort lvB ⇝ sort lvD` at `sort (succ lvA)` (right leg, first move). -/
def stepBD : EvPar litRoots [.assumption (.sort .zero)]
    (.sort lvB) (.sort lvD) (.sort (.succ lvA)) :=
  .sortEq { T₀ := .sort (.succ lvA), h := lvBD_eqN,
            hl := .sortsRight lvA lvB lvAB_eqN,
            hr := .sortsRight lvA lvD lvAD_eqN,
            idx := .refl _ _ }

/-- `sort lvD ⇝ sort lvC` at `sort (succ lvA)` (right leg, second move). -/
def stepDC : EvPar litRoots [.assumption (.sort .zero)]
    (.sort lvD) (.sort lvC) (.sort (.succ lvA)) :=
  .sortEq { T₀ := .sort (.succ lvA), h := lvDC_eqN,
            hl := .sortsRight lvA lvD lvAD_eqN,
            hr := .sortsRight lvA lvC lvAC_eqN,
            idx := .refl _ _ }

/-- a two-move child path — `.trans` over two `tail`-legs of genuine sortEq
    producer moves `lvA ⇝ lvB ⇝ lvC`; no `refl`-only stand-ins. -/
def bodyStar2 : EvParStar litRoots [.assumption (.sort .zero)]
    (.sort lvA) (.sort lvC) (.sort (.succ lvA)) :=
  .trans (.tail stepAB (.refl (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvB lvAB_eqN)))
         (.tail stepBC (.refl (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvC lvAC_eqN)))

/-- the right valley leg — two genuine moves `lvB ⇝ lvD ⇝ lvC`. -/
def legStarR : EvParStar litRoots [.assumption (.sort .zero)]
    (.sort lvB) (.sort lvC) (.sort (.succ lvA)) :=
  .trans (.tail stepBD (.refl (.sortsRight lvA lvD lvAD_eqN)))
         (.tail stepDC (.refl (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvC lvAC_eqN)))

/-- a lazy `wk` at cutoff 0 under the binder — the domain-moving shape the
    lift must refuse: its insertion point IS the binder itself. -/
def wkBadStar : EvParStar tyRoots [.assumption (.sort .zero)]
    (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .wk (.assumption (.sort .zero)) 0 (.refl (.lit tyS0 tySub))

/-- insertion PAST the child's context end (`c = 2` against a length-1 child
    context) — the lift must refuse; the cutoff guard catches it. -/
def wkPastStar : EvParStar litRoots
    [.assumption (.sort .zero), .assumption (.sort .zero)]
    (.bvar 0) (.bvar 0) (.sort .zero) :=
  .wk (.assumption (.sort .zero)) 2 bodyStar

/-- the legitimate shape: child at `[x₁ : S₀]`, insertion at cutoff 1 —
    strictly below the binder, within the child context. -/
def wkOkStar : EvParStar litRoots
    [.assumption (.sort .zero), .assumption (.sort .zero)]
    (.bvar 0) (.bvar 0) (.sort .zero) :=
  .wk (.assumption (.sort .zero)) 1 bodyStar

/-- the `wkOkStar` supply: the child's context decomposes as
    `assumption S₀ :: []`, whose binder formation is `domS0_child`; the
    residual supply is trivial (the child is a `refl`). -/
def wkOkDom : LamDomT wkOkStar :=
  ⟨[], .sort .zero, .succ .zero, rfl, domS0_child, ⟨⟩⟩

/-- a lazy `subst0` at index 0 — substitutes into the (only) assumption
    `x : S₁` by `v = S₀`, so the result context is `[]` and the binder is
    gone: exactly the binder-consuming shape this slice refuses. The
    `lamLiftSafeB` arm on `.subst0`/`.substLet` is a hard `false` — lazy
    substitutions are the W-X-SUBST lane's family, not the fixed-domain
    λ-lift's. -/
def subst0Star : EvParStar litRoots []
    (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .subst0 (v := .sort .zero) 0
    (.refl (EvTy.sort .zero :
        EvTy litRoots [.assumption (.sort (.succ .zero))]
          (.sort .zero) (.sort (.succ .zero))))
    rfl
    (EvTy.sort .zero :
      EvTy litRoots [] (.sort .zero) (.sort (.succ .zero)))

/-- the real predicate refuses the lazy-subst shape outright. -/
theorem subst0Star_refused : lamLiftSafeB subst0Star = false := rfl

/-- the guard-dropping mutant ACCEPTS it — the divergence tooth for the
    `subst0`/`substLet` coverage: this slice's hard refusal is what keeps
    the λ's domain fixed when a lazy substitution would consume it. -/
theorem subst0Star_mut_accepts : lamLiftSafeBMut subst0Star = true := rfl

/-! ### a concrete pre-`EvParX` producer family for the pin world

The kit is parameterized by `F : StepFam R`; the pins instantiate it at a
real λ-congruence carrier — the lifted step carries the original body step
inside, exactly the shape the D2b `LamPayload` lands in the owner's
`EvParX`. -/

/-- the pin-side extended producer: `lam`-congruence carrying the body step —
    the `F.Step` shape `stepLift`'s contract needs (and `EvPar` cannot
    supply). -/
inductive PinLamStep (R : List (Jd emptyEnv 0)) :
    LCtx → Expr Nat → Expr Nat → Expr Nat → Type where
  | lam {Γ : LCtx} {A B' x y : Expr Nat}
      (s : EvPar R (.assumption A :: Γ) x y B') :
      PinLamStep R Γ (.lam A x) (.lam A y) (.pi A B')

def PinLamStep.leaves {R : List (Jd emptyEnv 0)} :
    {Γ : LCtx} → {a b T : Expr Nat} →
    PinLamStep R Γ a b T → List (Jd emptyEnv 0)
  | _, _, _, _, .lam s => s.leaves

def PinLamStep.size {R : List (Jd emptyEnv 0)} :
    {Γ : LCtx} → {a b T : Expr Nat} →
    PinLamStep R Γ a b T → Nat
  | _, _, _, _, .lam s => 1 + s.size

theorem PinLamStep.leaves_root {R : List (Jd emptyEnv 0)} :
    {Γ : LCtx} → {a b T : Expr Nat} →
    (s : PinLamStep R Γ a b T) → ∀ ℓ ∈ s.leaves, ∃ r ∈ R, SubEq ℓ r
  | _, _, _, _, .lam s' => fun ℓ hℓ => s'.leaves_root ℓ hℓ

/-- the pin carrier as a `StepFam`. -/
def pinFam (R : List (Jd emptyEnv 0)) : StepFam R where
  Step := PinLamStep R
  leaves := PinLamStep.leaves
  size := PinLamStep.size
  leaves_root := fun s _ h => s.leaves_root _ h

/-- the `stepLift` CONTRACT is inhabited pointwise at `pinFam` — the λ-step
    node exists in the extended carrier. (The full kit stays a parameter:
    `tyLift` waits for #7150's introduction arm.) -/
def pinStepLift {Γ : LCtx} {A B' x y : Expr Nat} {u : Level}
    (_hA : EvTy litRoots Γ A (.sort u))
    (s : EvPar litRoots (.assumption A :: Γ) x y B') :
    (pinFam litRoots).Step Γ (.lam A x) (.lam A y) (.pi A B') :=
  .lam s

/-- `convLift` is inhabited TODAY by the landed `EvTc.piCod`. -/
def pinConvLift {Γ : LCtx} {A T T' : Expr Nat} {u : Level}
    (hA : EvTy litRoots Γ A (.sort u))
    (c : EvTc litRoots (.assumption A :: Γ) T T') :
    EvTc litRoots Γ (.pi A T) (.pi A T') :=
  .piCod _ hA c

/-! ### domain predicate teeth -/

theorem lamFixed_accepts_lit : lamFixedB lamLit = true := rfl
theorem lamFixed_rejects_nonSort : lamFixedB litBadB = false := rfl
theorem lamFixed_rejects_domChg : lamFixedB litDomChg = false := rfl
theorem lamFixedMut_accepts_bad : lamFixedBMut litBadB = true := rfl
theorem lamFixedMut_accepts_domChg : lamFixedBMut litDomChg = true := rfl

theorem lamLiftSafe_refl : lamLiftSafeB bodyStar = true := rfl
theorem lamLiftSafe_multi : lamLiftSafeB bodyStar2 = true := rfl
theorem lamLiftSafe_wk_ok : lamLiftSafeB wkOkStar = true := rfl
theorem lamLiftSafe_wk_bad : lamLiftSafeB wkBadStar = false := rfl
theorem lamLiftSafe_wk_past : lamLiftSafeB wkPastStar = false := rfl
theorem lamLiftSafeMut_wk_bad : lamLiftSafeBMut wkBadStar = true := rfl
theorem lamLiftSafeMut_wk_past : lamLiftSafeBMut wkPastStar = true := rfl

/-! ### lift teeth -/

variable (K : LamLiftOps litRoots (pinFam litRoots))

/-- the lifted single-point star has the exact endpoints §4.7 fixes:
    `lam S₀ x₀ ⇝ lam S₀ x₀` at `pi S₀ S₀` in the empty context — output in
    the GENERIC star `EvStarG` over the pin carrier, never the preserved
    `EvParStar`. -/
noncomputable def lift_refl_type :
    EvStarG litRoots (pinFam litRoots) []
      (.lam (.sort .zero) (.bvar 0)) (.lam (.sort .zero) (.bvar 0))
      (.pi (.sort .zero) (.sort .zero)) :=
  evStarG_lam K bodyStar rfl rfl domS0 ⟨⟩

/-- the `wk` inside the binder is re-based one level down — the lifted star
    sits at `[x₁ : S₀]` with the insertion now at cutoff 0. -/
noncomputable def lift_wk_type :
    EvStarG litRoots (pinFam litRoots) [.assumption (.sort .zero)]
      (.lam (.sort .zero) (.bvar 0)) (.lam (.sort .zero) (.bvar 0))
      (.pi (.sort .zero) (.sort .zero)) :=
  evStarG_lam K wkOkStar rfl rfl domS0_ctx wkOkDom

/-- the multi-step child lifts to a multi-step star — the `.trans` spine and
    both `tail` moves are preserved; kit adds AND the supplied formation's
    size are charged at every node. -/
theorem lift_multi_size :
    (evStarG_lam K bodyStar2 rfl rfl domS0 ⟨⟨⟩, ⟨⟩⟩).size =
      1 + (1 + (K.stepAdd domS0 stepAB + domS0.size + stepAB.size) +
            (1 + (K.tyAdd domS0 (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvB lvAB_eqN) +
                  domS0.size + (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvB lvAB_eqN).size))) +
          (1 + (K.stepAdd domS0 stepBC + domS0.size + stepBC.size) +
            (1 + (K.tyAdd domS0 (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvC lvAC_eqN) +
                  domS0.size + (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvC lvAC_eqN).size))) := by
  rw [evStarG_lam_size]; rfl

/-- the multi-step leaf equation — each move's kit flanks plus the supplied
    formation leaves appear in traversal order; the `[]` tails are the
    leaf-free payloads'. -/
theorem lift_multi_leaves :
    (evStarG_lam K bodyStar2 rfl rfl domS0 ⟨⟨⟩, ⟨⟩⟩).leaves =
      (K.stepPre domS0 stepAB ++ domS0.leaves ++ stepAB.leaves ++
          K.stepPost domS0 stepAB ++
        (K.tyPre domS0 (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvB lvAB_eqN) ++ domS0.leaves ++
          (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvB lvAB_eqN).leaves ++
          K.tyPost domS0 (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvB lvAB_eqN))) ++
      (K.stepPre domS0 stepBC ++ domS0.leaves ++ stepBC.leaves ++
          K.stepPost domS0 stepBC ++
        (K.tyPre domS0 (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvC lvAC_eqN) ++ domS0.leaves ++
          (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvC lvAC_eqN).leaves ++
          K.tyPost domS0 (EvTy.sortsRight (R := litRoots) (Γ := [.assumption (.sort .zero)]) lvA lvC lvAC_eqN))) := by
  rw [evStarG_lam_leaves]; rfl

/-- a full valley under the binder with TWO genuine producer moves on EACH
    leg — left `lvA ⇝ lvB ⇝ lvC`, right `lvB ⇝ lvD ⇝ lvC`, centre
    `sort lvC`, index `sort (succ lvA)`. -/
def bodyValley : Valley litRoots [.assumption (.sort .zero)]
    (.sort lvA) (.sort lvB) (.sort (.succ lvA)) :=
  ⟨.sort lvC, bodyStar2, legStarR,
    .sort lvA, .sortsRight lvA lvB lvAB_eqN⟩

/-- residual supplies for the valley's legs (both are refl-terminated
    producer chains). -/
def valleyDomL : LamDomT bodyValley.left := ⟨⟨⟩, ⟨⟩⟩
def valleyDomR : LamDomT bodyValley.right := ⟨⟨⟩, ⟨⟩⟩

theorem valleyGLam_centre :
    (valleyGLam K bodyValley rfl rfl domS0 valleyDomL valleyDomR).N =
      .lam (.sort .zero) (.sort lvC) := rfl

noncomputable def valleyGLam_left_type :
      EvStarG litRoots (pinFam litRoots) []
        (.lam (.sort .zero) (.sort lvA)) (.lam (.sort .zero) (.sort lvC))
        (.pi (.sort .zero) (.sort (.succ lvA))) :=
  (valleyGLam K bodyValley rfl rfl domS0 valleyDomL valleyDomR).left

/-- the valley's leaf split — output leaves are child leaves or kit costs
    (which now include the supplied formation's own leaves). -/
theorem valleyGLam_sub_pin (ℓ : Jd emptyEnv 0)
    (h : ℓ ∈ (valleyGLam K bodyValley rfl rfl domS0 valleyDomL
        valleyDomR).leaves) :
    ℓ ∈ bodyValley.leaves ++
      (lamExtrasF K (mkFrame bodyValley.left rfl rfl domS0 valleyDomL) ++
        lamExtrasF K (mkFrame bodyValley.right rfl rfl domS0 valleyDomR) ++
        (K.tyPre domS0 bodyValley.ty₁ ++ domS0.leaves ++
          K.tyPost domS0 bodyValley.ty₁) ++
        (K.tyPre domS0 bodyValley.ty₂ ++ domS0.leaves ++
          K.tyPost domS0 bodyValley.ty₂)) :=
  valleyGLam_sub K bodyValley rfl rfl domS0 valleyDomL valleyDomR ℓ h

/-! ### the authorized direction — old star → extended star, never reversed -/

/-- embedding a genuine two-move old star into `EvStarG` at the old carrier
    preserves its leaf set exactly (the kit's output accounting then adds
    only kit costs). -/
theorem embed_bodyStar2_leaves :
    (evStarG_of_evParStar bodyStar2).leaves = bodyStar2.leaves :=
  evStarG_of_evParStar_leaves _

/-- and its size exactly. -/
theorem embed_bodyStar2_size :
    (evStarG_of_evParStar bodyStar2).size = bodyStar2.size :=
  evStarG_of_evParStar_size _

/-- the valley embedding preserves the leaf split on both legs. -/
theorem embed_bodyValley_leaves :
    (valleyG_of_valley bodyValley).leaves = bodyValley.leaves :=
  valleyG_of_valley_leaves _

/-! ### extractor teeth -/

/-- the extractor returns a packet on the good literal — its coverage is the
    syntactic domain exactly. -/
theorem extract_lit_isSome :
    (lamFixedExtract lamLit litSub).isSome = true :=
  (lamFixedExtract_isSome lamLit litSub).trans lamFixed_accepts_lit

theorem extract_badB_none : lamFixedExtract litBadB badSub = none := rfl

/-- a changed-domain `.lam` literal yields no packet either — the extractor's
    `hdom` branch refuses it. -/
theorem extract_domChg_none : lamFixedExtract litDomChg chgSub = none := rfl

/-- a non-`lam` literal is refused. -/
def reflLit : ConvT emptyEnv 0 [] (.sort .zero) (.sort .zero)
    (.sort (.succ .zero)) := .refl [] _ _ tyS0
def reflRoots : List (Jd emptyEnv 0) := [.cv reflLit]
def reflSub : ∃ r ∈ reflRoots, SubEq (.cv reflLit) r :=
  ⟨_, .head _, .inl rfl⟩

theorem extract_rejects_nonLam :
    lamFixedExtract reflLit reflSub = none := rfl

/-- the extracted packet's leaves are exactly the literal's own two conversion
    children — provenance literals — plus the leaf-free codomain sort typing. -/
theorem extract_packet_leaves {Γ : LCtx} {a b T : Expr Nat}
    (h : ConvT emptyEnv 0 Γ a b T)
    (hsub : ∃ r ∈ [.cv h], SubEq (.cv h) r) :
    ∀ s, lamFixedExtract h hsub = some s →
      let p := s.2.2.2.2.2.2.2.2.2
      p.dom.leaves ++ p.bod.leaves ++ p.codTy.leaves =
        [.cv s.2.2.2.2.2.2.1, .cv s.2.2.2.2.2.2.2.1] := by
  intro s _ p
  simp only [p.dom_leaves, p.bod_leaves, p.codTy_leaves, List.append_nil,
    List.singleton_append]

/-- the extracted packet's leaves are strictly below the original literal —
    the §5.2 provenance discipline. -/
theorem extract_packet_strict :
    ∀ ℓ ∈ [.cv (.refl [] _ _ tyS0 : ConvT emptyEnv 0 [] _ _ _),
            .cv (.refl [.assumption (.sort .zero)] _ _
              (.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl) :
              ConvT emptyEnv 0 [.assumption (.sort .zero)] _ _ _)],
      SubOf ℓ (.cv lamLit) := by
  intro ℓ hℓ
  simp only [List.mem_cons, List.not_mem_nil, or_false, false_or] at hℓ
  rcases hℓ with rfl | rfl
  · exact .child (.head _)
  · exact .child (.tail _ (.head _))

/-! ### mutant teeth, discharged concretely -/

/-- the leaf-accounting mutant vs the real equation at a `refl` node —
    exhibited concretely: with lit-rooted formation evidence (`domS0_lit`,
    leaves `[.ty tyS0]`) the mutant reports `[]` while the real accounting
    charges the formation leaf in the middle segment. -/
theorem leaf_mutant_divergence (K' : LamLiftOps tyRoots (pinFam tyRoots)) :
    lamLeavesMutF K' (mkFrame tyBodyStar rfl rfl domS0_lit ⟨⟩) = [] ∧
      .ty tyS0 ∈
        lamLeavesF K' (mkFrame tyBodyStar rfl rfl domS0_lit ⟨⟩) := by
  refine ⟨rfl, ?_⟩
  have hred : lamLeavesF K' (mkFrame tyBodyStar rfl rfl domS0_lit ⟨⟩) =
      K'.tyPre domS0_lit tyBodyVar ++ [.ty tyS0] ++ [] ++
        K'.tyPost domS0_lit tyBodyVar := rfl
  rw [hred]
  simp

/-- the REAL inequality: the leaf mutant's report differs from the real
    accounting whenever the charged costs are nonempty — discharged by the
    lit-rooted formation leaf (the `.ty tyS0` cons makes the kit segment
    nonempty for ANY kit). -/
theorem leaf_mutant_diverges_ne (K' : LamLiftOps tyRoots (pinFam tyRoots)) :
    lamLeavesMutF K' (mkFrame tyBodyStar rfl rfl domS0_lit ⟨⟩) ≠
      lamLeavesF K' (mkFrame tyBodyStar rfl rfl domS0_lit ⟨⟩) := by
  intro heq
  have hmut : lamLeavesMutF K' (mkFrame tyBodyStar rfl rfl domS0_lit ⟨⟩) = [] :=
    rfl
  have hmem : .ty tyS0 ∈
      lamLeavesF K' (mkFrame tyBodyStar rfl rfl domS0_lit ⟨⟩) :=
    (leaf_mutant_divergence K').2
  rw [← heq, hmut] at hmem
  exact absurd hmem (List.not_mem_nil _)

/-- the refused domain-free kit is uninhabitable in EVERY root — the audit's
    `∀ R, LamLiftOps R → False` control, against the actual constructors:
    its `tyLift` types `lam (bvar 0) (sort 0)` in `[]`, `lam`-inversion
    yields `EvTy R [] (bvar 0) _`, and `bvar`-inversion contradicts
    `lookupType [] 0`. -/
theorem refused_kit_uninhabitable (K' : LamLiftOpsMut tyRoots) : False :=
  lamLiftOpsMut_absurd K'

/-- the audit's second control, discharged VERBATIM at `emptyEnv`:
    `∀ R : List (Jd emptyEnv 0), LamLiftOps R (evParFam R) → False` — the
    old-carrier instantiation is uninhabitable in EVERY root bundle,
    `litRoots` included. `SortUnique` holds at `emptyEnv` unconditionally
    (`InScope` is `True` there), so the premise closes by the row supplier —
    the J module only keeps it hypothetical because the circularity guard
    bars importing `RcicSortUniqueRows` into the construction path. -/
theorem refused_evParCarrier_uninhabitable
    (R' : List (Jd emptyEnv 0))
    (K' : LamLiftOps R' (evParFam R')) : False :=
  lamLiftOps_evParCarrier_absurd
    (sortUnique_of_inScope EnvWfT.empty trivial 0) R' K'

/-- specializing the verbatim control to the committed fixture — changing the
    root bundle cannot repair the old carrier. -/
theorem refused_evParCarrier_litRoots
    (K' : LamLiftOps litRoots (evParFam litRoots)) : False :=
  refused_evParCarrier_uninhabitable litRoots K'

end Rcic.Declarative.F8Measure.JLam.Pins
