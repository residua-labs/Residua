import rcic.RcicF8EvParStar
import rcic.RcicTypedWeaken
import rcic.RcicSubstT

/-!
J-ETA-INTRO (supply-map §4.6, design: ChatGPT JT-1) — the pre-#7150 slice of
the η literal `ConvT.eta Γ f A B hf : ConvT _ (lam A (app (lift 0 1 f) (bvar 0)))
f (pi A B)`.

Two additive pieces, both strictly pre-#7150:

* path lifting: `parRedTStar_etaLift` lifts an ACTUAL child `ParRedTStar`
  `f →* f'` through the η congruence — the first step goes through
  `ParRedT.eta`, the tail is the child's own remaining path, never a
  single-step stand-in. `etaLiftStar`/`etaLiftValleyVal` apply it to the
  materialized paths of an actual child `EvParStar`/`Valley`, with exact
  `leaves`/`size`/`steps` equations.

* formation evidence: `etaIntroEvidence?` succeeds iff the original `hf` is
  literally a `HasTyT.lam` node — `hA`/`hbody` are its real children, the
  domain is fixed by the independent syntactic condition `f = .lam A body`
  for the η annotation `A` itself. `EtaIntroEvidence.leftTy` builds the
  η-expansion's left typing `hl` from the extracted `hA` plus the existing
  weakening of `hf` — nothing is read from `Γ`, and no caller `hB`/`hPi`/`hTy`
  is accepted.

Mutant per §7 (`etaIntroDomainMut?`): a weak extractor that accepts a
caller-forged domain typing for a variable-typed `f` — the real extractor
returns `none`, and the forged leaf is proved unreachable inside both the
original `hf` node and the η conversion root.

Open and explicitly NOT built here: the `EvPar`/`EvTy` η, λ, app producers
(EX+ / #7150), the endpoint `Valley`/`Result` assembly, general `hf`
formation provenance. closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.F8Measure.JEtaIntro

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}
variable {Γ : LCtx} {f f' A B : Expr Nat}

/-! ## §1 formation evidence along the original introduction path (§4.6, §5.2) -/

/-- Evidence extracted along the ORIGINAL introduction path of the η literal's
    `hf : HasTyT Γ f (pi A B)`: `hA`/`hbody` are the actual children of a real
    `HasTyT.lam` node — `f_eq` fixes the domain syntactically (the λ binder IS
    the η annotation `A`), `hf_heq` ties the children to `hf` itself. -/
structure EtaIntroEvidence {Γ : LCtx} {f A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) where
  u : Level
  body : Expr Nat
  hA : HasTyT E n Γ A (.sort u)
  hbody : HasTyT E n (.assumption A :: Γ) body B
  f_eq : f = .lam A body
  hf_heq : HEq hf (HasTyT.lam Γ A u body B hA hbody)

/-- The extractor: succeeds iff `hf` is literally a `HasTyT.lam` node at the
    η index `pi A B`. Matching `f` together with `hf` pins the term index to
    the λ ctor, so the arm needs no index transport and the definition
    reduces on constructor input. Index unification is the independent
    syntactic condition — no `hB`/`hPi`/`hTy` is accepted from the caller,
    and the domain is not read from the context. -/
def etaIntroEvidence? {Γ : LCtx} {f A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) : Option (EtaIntroEvidence hf) :=
  match f, hf with
  | Expr.lam _ body', HasTyT.lam _ _ u _ _ hA hbody =>
      some ⟨u, body', hA, hbody, rfl, HEq.rfl⟩
  | _, _ => none

/-- the independent syntactic gate on the domain: `f` is an actual λ whose
    binder is the η annotation `A` itself — a property of the term, not of
    any supplied typing premise. -/
def etaIntroDomainOk (f A : Expr Nat) : Bool :=
  match f with | .lam A' _ => decide (A' = A) | _ => false

theorem etaIntroEvidence?_lam {Γ : LCtx} {A B : Expr Nat} {u : Level}
    {body : Expr Nat} (hA : HasTyT E n Γ A (.sort u))
    (hbody : HasTyT E n (.assumption A :: Γ) body B) :
    etaIntroEvidence? (.lam Γ A u body B hA hbody) =
      some ⟨u, body, hA, hbody, rfl, HEq.rfl⟩ := rfl

theorem EtaIntroEvidence.domainOk {Γ : LCtx} {f A B : Expr Nat}
    {hf : HasTyT E n Γ f (.pi A B)} (e : EtaIntroEvidence hf) :
    etaIntroDomainOk f A = true := by
  obtain ⟨u, body, hA, hbody, rfl, _⟩ := e
  simp [etaIntroDomainOk]

/-- §4.6: `hA` is a real child of the original `hf`, lifted strictly through
    the η root — `ty hA ∈ tyChildren hf` and `ty hf ∈ cvChildren (eta hf)`. -/
theorem EtaIntroEvidence.hA_strict {Γ : LCtx} {f A B : Expr Nat}
    {hf : HasTyT E n Γ f (.pi A B)} (e : EtaIntroEvidence hf) :
    SubOf (.ty e.hA) (.cv (.eta Γ f A B hf)) := by
  obtain ⟨u, body, hA, hbody, rfl, hheq⟩ := e
  cases hheq
  exact .trans (y := .ty (HasTyT.lam Γ A u body B hA hbody))
    (.child (.head _)) (.child (.head _))

/-- the body typing is likewise a real child of the original `hf`. -/
theorem EtaIntroEvidence.hbody_strict {Γ : LCtx} {f A B : Expr Nat}
    {hf : HasTyT E n Γ f (.pi A B)} (e : EtaIntroEvidence hf) :
    SubOf (.ty e.hbody) (.cv (.eta Γ f A B hf)) := by
  obtain ⟨u, body, hA, hbody, rfl, hheq⟩ := e
  cases hheq
  exact .trans (y := .ty (HasTyT.lam Γ A u body B hA hbody))
    (.child (.tail _ (.head _))) (.child (.head _))

/-- the η-expansion's left typing `hl`, built only from the extracted
    evidence: `e.hA` (a real child of `hf`) plus the existing weakening of
    `hf` itself and the `bvar 0` lookup. `instantiate0 (bvar 0)
    (lift 1 1 B) = B` is the syntactic identity closing the app. -/
def EtaIntroEvidence.leftTy (hcl : EnvClosed E) {Γ : LCtx} {f A B : Expr Nat}
    {hf : HasTyT E n Γ f (.pi A B)} (e : EtaIntroEvidence hf) :
    HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B) := by
  obtain ⟨u, body, hA, hbody, rfl, _⟩ := e
  have hb0 : HasTyT E n (.assumption A :: Γ) (.bvar 0) (lift 0 1 A) :=
    .bvar _ _ _ rfl
  have hwk : HasTyT E n (.assumption A :: Γ) (lift 0 1 (.lam A body))
      (.pi (lift 0 1 A) (lift 1 1 B)) :=
    hasTyTWeaken (.assumption A) hcl (c := 0) hf
  have happ := HasTyT.app _ _ _ _ _ hwk hb0
  rw [instantiate0_bvar0_lift1] at happ
  exact .lam Γ A u _ B hA happ

/-! ## §2 path lifting through the η congruence — actual multi-step paths -/

variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- lift an actual child `ParRedTStar` `f →* f'` through the η congruence:
    `ParRedT.eta` carries the child's own first step to `lam-exp f → b`, and
    every remaining step is the child's own tail — `tail s rest` maps to
    `tail (eta s hl) rest`, never a single-step stand-in. -/
def parRedTStar_etaLift {Γ : LCtx} {f f' A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B)) :
    ParRedTStar PEq E n Γ f f' (.pi A B) →
    ParRedTStar PEq E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f' (.pi A B)
  | .refl _ _ _ h => .tail (.eta Γ f f A B (.refl Γ f _ h) hl) (.refl Γ f _ h)
  | .tail s rest => .tail (.eta Γ f _ A B s hl) rest

/-- step count of a materialized path — the exact size equations for the
    lift are stated against the child's own count. -/
def parRedTStarSteps {Γ : LCtx} {a b T : Expr Nat} :
    ParRedTStar PEq E n Γ a b T → Nat
  | .refl _ _ _ _ => 0
  | .tail _ hs => 1 + parRedTStarSteps hs

theorem parRedTStar_etaLift_refl {Γ : LCtx} {f A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (h : HasTyT E n Γ f (.pi A B)) :
    parRedTStar_etaLift (PEq := PEq) hl (.refl Γ f (.pi A B) h) =
      .tail (.eta Γ f f A B (.refl Γ f (.pi A B) h) hl)
        (.refl Γ f (.pi A B) h) := rfl

theorem parRedTStar_etaLift_tail {Γ : LCtx} {f b f' A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (s : ParRedT PEq E n Γ f b (.pi A B))
    (rest : ParRedTStar PEq E n Γ b f' (.pi A B)) :
    parRedTStar_etaLift hl (.tail s rest) =
      .tail (.eta Γ f b A B s hl) rest := rfl

/-- a multi-step child is not collapsed: the lifted path still contains every
    one of the child's actual steps — the head through η, the rest verbatim. -/
theorem parRedTStar_etaLift_twoStep {Γ : LCtx} {f b₁ b₂ f' A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (s₁ : ParRedT PEq E n Γ f b₁ (.pi A B))
    (s₂ : ParRedT PEq E n Γ b₁ b₂ (.pi A B))
    (rest : ParRedTStar PEq E n Γ b₂ f' (.pi A B)) :
    parRedTStar_etaLift hl (.tail s₁ (.tail s₂ rest)) =
      .tail (.eta Γ f b₁ A B s₁ hl) (.tail s₂ rest) := rfl

/-- exact size equation, nonempty child: the lifted path has the child's
    exact step count — the child's first step became the η head step. -/
theorem parRedTStar_etaLift_steps_tail {Γ : LCtx} {f b f' A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (s : ParRedT PEq E n Γ f b (.pi A B))
    (rest : ParRedTStar PEq E n Γ b f' (.pi A B)) :
    parRedTStarSteps (parRedTStar_etaLift hl (.tail s rest)) =
      parRedTStarSteps (.tail s rest) := rfl

/-- exact size equation, empty child: the η contraction of a reflexive path
    contributes exactly the single η step. -/
theorem parRedTStar_etaLift_steps_refl {Γ : LCtx} {f A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (h : HasTyT E n Γ f (.pi A B)) :
    parRedTStarSteps
      (parRedTStar_etaLift (PEq := PEq) hl (.refl Γ f (.pi A B) h)) = 1 := rfl

/-- η-lift of an actual child `EvParStar`'s materialized path — the child's
    own `ParRedTStar` is lifted, so every emitted step is the child's own. -/
def etaLiftStar (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {f f' A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (s : EvParStar R Γ f f' (.pi A B)) :
    ParRedTStar (PEqLeafT E n) E n Γ
      (.lam A (.app (lift 0 1 f) (.bvar 0))) f' (.pi A B) :=
  parRedTStar_etaLift hl (s.val hcl hinst)

theorem etaLiftStar_val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {f f' A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (s : EvParStar R Γ f f' (.pi A B)) :
    etaLiftStar hcl hinst hl s = parRedTStar_etaLift hl (s.val hcl hinst) := rfl

/-- `tail`-headed child: the lifted path's tail is the child's own `hs.val` —
    each remaining step is literally the child's step. -/
theorem etaLiftStar_tail (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {f b f' A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (h : EvPar R Γ f b (.pi A B)) (hs : EvParStar R Γ b f' (.pi A B)) :
    etaLiftStar hcl hinst hl (.tail h hs) =
      .tail (.eta Γ f b A B (h.val hcl hinst) hl) (hs.val hcl hinst) := rfl

/-- reflexive child: the lifted path is the single η step on
    `ParRedT.refl` — §4.6's base case, centre `f`. -/
theorem etaLiftStar_refl (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {f A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (ty : EvTy R Γ f (.pi A B)) :
    etaLiftStar hcl hinst hl (.refl ty) =
      .tail (.eta Γ f f A B (.refl Γ f (.pi A B) (ty.val hcl hinst)) hl)
        (.refl Γ f (.pi A B) (ty.val hcl hinst)) := rfl

/-- exact leaf equation for a `tail`-headed child: the eventual
    `EvParStar.tail evparEta hs` leg's tail contribution is `hs`'s own leaf
    list — the child's actual tail, not a rebuilt path. -/
theorem etaLiftTail_leaves {Γ : LCtx} {f b f' A B : Expr Nat}
    (h : EvPar R Γ f b (.pi A B)) (hs : EvParStar R Γ b f' (.pi A B)) :
    (EvParStar.tail h hs).leaves = h.leaves ++ hs.leaves := rfl

/-- exact size equation for a `tail`-headed child. -/
theorem etaLiftTail_size {Γ : LCtx} {f b f' A B : Expr Nat}
    (h : EvPar R Γ f b (.pi A B)) (hs : EvParStar R Γ b f' (.pi A B)) :
    (EvParStar.tail h hs).size = 1 + h.size + hs.size := rfl

/-- exact leaf equation for the reflexive child of the first slice. -/
theorem etaLiftRefl_leaves {Γ : LCtx} {f A B : Expr Nat}
    (ty : EvTy R Γ f (.pi A B)) :
    (EvParStar.refl ty).leaves = ty.leaves := rfl

/-- exact size equation for the reflexive child of the first slice. -/
theorem etaLiftRefl_size {Γ : LCtx} {f A B : Expr Nat}
    (ty : EvTy R Γ f (.pi A B)) :
    (EvParStar.refl ty).size = 1 + ty.size := rfl

/-- lift an actual child Valley's two materialized paths through the η
    congruence: the left leg `f →* V.N` lifts to `lam-exp f →* V.N` per
    actual step; the right leg `f' →* V.N` is the child's own right path —
    `f'` is not η-expanded. -/
def etaLiftValleyVal (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {f f' A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (V : Valley R Γ f f' (.pi A B)) :
    (ParRedTStar (PEqLeafT E n) E n Γ
      (.lam A (.app (lift 0 1 f) (.bvar 0))) V.N (.pi A B)) ×
      (ParRedTStar (PEqLeafT E n) E n Γ f' V.N (.pi A B)) :=
  ⟨etaLiftStar hcl hinst hl V.left, V.right.val hcl hinst⟩

theorem etaLiftValleyVal_left (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} {f f' A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (V : Valley R Γ f f' (.pi A B)) :
    (etaLiftValleyVal hcl hinst hl V).1 =
      parRedTStar_etaLift hl (V.left.val hcl hinst) := rfl

theorem etaLiftValleyVal_right (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} {f f' A B : Expr Nat}
    (hl : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (V : Valley R Γ f f' (.pi A B)) :
    (etaLiftValleyVal hcl hinst hl V).2 = V.right.val hcl hinst := rfl

/-- leaf accounting on the child's own Valley: the lifted answer reuses the
    child's actual legs and typings, so its leaf budget decomposes exactly
    into the child's leaves (the η payload's own leaves come from the future
    `EvPar.eta` producer, EX+). -/
theorem etaLiftValley_leaves {Γ : LCtx} {f f' A B : Expr Nat}
    (V : Valley R Γ f f' (.pi A B)) :
    V.leaves = V.left.leaves ++ V.right.leaves ++ V.ty₁.leaves ++ V.ty₂.leaves :=
  rfl

/-- §4.6 first slice: the direct-λ literal's left leg materialization — the
    function child is reflexive, the η step is the whole left leg, the centre
    is `f`. -/
def etaIntroLeft (hcl : EnvClosed E) {Γ : LCtx} {f A B : Expr Nat}
    {hf : HasTyT E n Γ f (.pi A B)} (e : EtaIntroEvidence hf) :
    ParRedTStar (PEqLeafT E n) E n Γ
      (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) :=
  parRedTStar_etaLift (e.leftTy hcl) (.refl Γ f (.pi A B) hf)

theorem etaIntroLeft_eq (hcl : EnvClosed E) {Γ : LCtx} {f A B : Expr Nat}
    {hf : HasTyT E n Γ f (.pi A B)} (e : EtaIntroEvidence hf) :
    etaIntroLeft hcl e =
      .tail (.eta Γ f f A B (.refl Γ f (.pi A B) hf) (e.leftTy hcl))
        (.refl Γ f (.pi A B) hf) := rfl

/-! ## §3 mutant (§7): η forging domain formation provenance -/

section Mutant

/-- MUTANT — supply-map §7 η tooth: the weak extractor accepts ANY
    caller-supplied `hA` and never requires the original `hf` to be a
    `HasTyT.lam` node — a variable-typed `f` passes with forged domain
    provenance that is not a child of `hf`. -/
def etaIntroDomainMut? {Γ : LCtx} {f A B : Expr Nat} {u : Level}
    (_hf : HasTyT E n Γ f (.pi A B)) (hA : HasTyT E n Γ A (.sort u)) :
    Option (HasTyT E n Γ A (.sort u)) :=
  some hA

/-- a variable-typed `f : pi (sort 0) (sort 0)` — the general-`hf` shape the
    first slice excludes. -/
def etaBvarCtx : LCtx := [.assumption (.pi (.sort .zero) (.sort .zero))]

def etaBvarHf :
    HasTyT E n etaBvarCtx (.bvar 0) (.pi (.sort .zero) (.sort .zero)) :=
  .bvar _ _ _ rfl

/-- the forged domain typing the mutant accepts — `sort 0 : sort 1`, no
    relation to `etaBvarHf`. -/
def etaForgedHA :
    HasTyT E n etaBvarCtx (.sort .zero) (.sort (.succ .zero)) :=
  .sort _ _

/-- the η conversion root over the variable-typed fixture. -/
def etaCvNode :
    ConvT E n etaBvarCtx
      (.lam (.sort .zero) (.app (lift 0 1 (.bvar 0)) (.bvar 0)))
      (.bvar 0) (.pi (.sort .zero) (.sort .zero)) :=
  .eta _ _ _ _ (etaBvarHf (E := E) (n := n))

/-- the real extractor refuses: a variable function's `hf` is not a
    `HasTyT.lam` introduction, so there is no domain child to extract. -/
theorem etaIntroEvidence?_rejects_bvar :
    etaIntroEvidence? (etaBvarHf (E := E) (n := n)) = none := rfl

/-- the syntactic gate likewise refuses: `bvar 0` is not a λ. -/
theorem etaIntroDomainOk_bvar :
    etaIntroDomainOk (.bvar 0) (.sort .zero) = false := rfl

/-- the syntactic gate accepts when the λ binder IS the η annotation. -/
theorem etaIntroDomainOk_lam :
    etaIntroDomainOk (.lam (.sort .zero) (.bvar 0)) (.sort .zero) = true := rfl

/-- and refuses a λ whose binder is a different domain (`sort 1` ≠ `sort 0`). -/
theorem etaIntroDomainOk_wrongBinder :
    etaIntroDomainOk (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero) =
      false := rfl

/-- the mutant wrongly accepts the forged domain typing. -/
theorem etaIntroDomainMut?_accepts_forged :
    (etaIntroDomainMut? (etaBvarHf (E := E) (n := n))
      (etaForgedHA (E := E) (n := n))).isSome = true := rfl

/-- plumbing: a `bvar` typing node has `tyChildren = []`, so nothing is a
    strict subderivation of `.ty etaBvarHf`. -/
private theorem etaMut_subOf_bvarTy_absurd {x z : Jd E n} (h : SubOf x z)
    (hz : z = .ty (etaBvarHf (E := E) (n := n))) : False := by
  induction h with
  | child hc =>
      subst hz
      cases hc
  | trans _ _ _ ih₂ => exact ih₂ hz

/-- plumbing: the η `cv` root's only immediate child is the fixture's own
    `ty hf` leaf, which itself has no children — so every strict
    subderivation of the root equals that leaf. -/
private theorem etaMut_subOf_cv_eta_only {x z : Jd E n} (h : SubOf x z)
    (hz : z = .cv (etaCvNode (E := E) (n := n))) :
    x = .ty (etaBvarHf (E := E) (n := n)) := by
  induction h with
  | child hc =>
      subst hz
      cases hc with
      | head => rfl
      | tail _ h' => cases h'
  | trans h₁ _ _ ih₂ =>
      have hy := ih₂ hz
      subst hy
      exact False.elim (etaMut_subOf_bvarTy_absurd h₁ rfl)

/-- the forged leaf is not even below `hf`: a `bvar` node has no children. -/
theorem etaMut_forged_not_subOf_ty :
    ¬ SubOf (.ty (etaForgedHA (E := E) (n := n)))
      (.ty (etaBvarHf (E := E) (n := n))) :=
  fun h => etaMut_subOf_bvarTy_absurd h rfl

/-- nor is it below the η literal's `cv` root — the mutant's accepted leaf is
    unreachable by the strict-leaf contract: every strict subderivation of the
    root equals `.ty etaBvarHf`, and the forged `sort`-node is not that leaf. -/
theorem etaMut_forged_not_subOf_cv :
    ¬ SubOf (.ty (etaForgedHA (E := E) (n := n)))
      (.cv (etaCvNode (E := E) (n := n))) := fun h => by
  have hx := etaMut_subOf_cv_eta_only h rfl
  cases hx

end Mutant

#print axioms Rcic.Declarative.F8Measure.JEtaIntro.etaIntroEvidence?
#print axioms Rcic.Declarative.F8Measure.JEtaIntro.EtaIntroEvidence.leftTy
#print axioms Rcic.Declarative.F8Measure.JEtaIntro.parRedTStar_etaLift
#print axioms Rcic.Declarative.F8Measure.JEtaIntro.etaLiftStar
#print axioms Rcic.Declarative.F8Measure.JEtaIntro.etaLiftValleyVal
#print axioms Rcic.Declarative.F8Measure.JEtaIntro.etaIntroLeft
#print axioms Rcic.Declarative.F8Measure.JEtaIntro.etaMut_forged_not_subOf_cv

end Rcic.Declarative.F8Measure.JEtaIntro
