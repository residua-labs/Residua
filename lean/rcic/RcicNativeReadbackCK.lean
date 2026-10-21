import rcic.RcicNativeFamModelLRS
import rcic.RcicNativeFamModelLRSPER
import rcic.RcicNativeTypedModelRel
import rcic.RcicNativeSpineHeadRoots
import rcic.RcicNativeCertifiedKRows

/-!
# RcicNativeReadbackCK — one repaired readback: context-aware, K-aware, deterministic core,
certified K steps, and the laws `LRSCore` needs from it

**Stacked on** `#7673` (`LRSCore` over the `Readback` interface; itself on `#7670`/`#7666`) and
`#7665` (the certified head step `NativeSpineHead.Step` with `Step.toConv`, the plain-K boundary
`IotaKMajorAlign` and the schema-ι object `SchemaIotaConv`).  Composition only.

**§1 The untyped deterministic core `WhStepCK E Γ`** = the landed context-aware step `WhStepCtx`
(`RcicNativeFamModel`: β, ζ, ζ-local, δ, ι, lit, appHead) **plus**
* `kStar` — field-free K at a NON-constructor major of a field-free proposition-singleton recursor
  (the contractum is the witness's minor; ordinary ι keeps the constructor majors);
* `kProj` — fieldful K at a NON-constructor major of a fieldful proposition singleton with
  large elimination (first-order recursive fields included: one K step = one unfolding, the
  recursive call stays in argument position), with the canon `intro params c₀ … c_{k-1}`: an
  index-revealed field is the matching index argument of the redex, any other field its
  projection `prᵢ x` = the recursor at a proposition motive (`canonField`; binder types read off
  the stored family and constructor types, the minor's telescope from the landed `minorTel`).
  A function of the redex, so no existential choice;
* both K arms fire only when the redex's index arguments equal the canon constructor's result
  indices (`redexIdx = resultIdxAt …`, syntactically): otherwise the canon is not of the major's
  type and the step would change the type (Lean's K checks this by defeq);
* `recMajor` — reduction of the major at the saturated major position of every OTHER recursor
  (a K recursor never reduces its major: K fires at every non-constructor major);
* `appHead`.
`readbackLaws_whStepCK` makes it an instance of `#7673`'s `ReadbackLaws`; `detR_whStepCK` is EXACT
determinism under `EnvWfT` (`#7673` segment 2's `DetR`), hence `diamondR_whStepCK` and
`normalUniqueR_whStepCK` — the law `LRSCore` transitivity needs (`#7673` §1).  (`#7668`'s
`WhStepRecCtx` reduces the major of EVERY recursor, which overlaps K at reducible proof majors;
the core reduces majors only of recursors that are not field-free proposition singletons.)

**§2 The certified K steps** on `#7665`'s `Step`: the plain-K certificate is irrelevance on the major
plus ι; `#7665` needs a global alignment `IotaKMajorAlign` (type uniqueness) for it.  At a VARIABLE
major the alignment is free (`tyConvT_bvar_align`, `hasTyTInv_bvar` twice), so
`convT_iotaStarK_bvar` / `cstepK_iotaStarK_bvar` / `stepK_bvar` are unconditional — field-free AND
fieldful (`ParRedT.iotaStarK` takes any witness: the canon of the same proposition, its typing
carried by the certificate).  Legacy ι arm only; the schema arm is `#7665`'s `SchemaIotaConv`.

**§3 Positive controls and teeth.**  `trueEnvU` K (`.sort`) and its Π-side analogue
`True.rec.{2} (λ_. Sort 1) (Sort 0 → Sort 0) h` at every compact of `Sort 0 → Sort 0` (incl. the
`piRow` probe `pi ⊥ []`), both directions, with `WhStepCK`; the same Π point refutes the chain form
for the K-blind `WhStepCtx`.  `andEnvU` fieldful: the core reaches `Sort 0 → Sort 0`
deterministically (`redR_whStepCK_mixAndRedex`, `lrSCore_whStepCK_mixAnd`/`_symm`); the certified
step `stepK_mixAnd` (existential canon) stays as a certificate.

**§4 Fieldful proof majors: the single-step diamond fails.**  The existential fieldful step
(`WhStepK`'s `pmajor`) is neither deterministic (`not_detR_whStepK_andEnvU`) nor single-step
confluent (`not_diamondR_whStepK_andEnvU`: two choices differing in the second field meet only
after two steps).  Every choice at `mixAnd` does join at `Sort 0 → Sort 0`
(`fieldfulK_join_mixAnd`) — multi-step joinability, which does not discharge `NormalUniqueR`
without termination.  Hence the core's fieldful step is the projection canon (§1), not an
existential one.

**§5 The app case at proposition-typed arguments.**  At `trueEnvU`,
`(λp:True. Sort 0) intro ≡ True.rec M (Sort 0) h` (η-K + irr under `ConvT.app`).  In the UNTYPED
models the proof `intro` has the compact `spine 1 []`, at which the λ clause demands
`LRSCore intro h True (spine 1 [])` — false (`not_lrSCore_intro_var`); hence `#7673`'s
`AppPropArgs` is false over `ApproxI` and over `ApproxDI` (`not_appPropArgs_ctxModel{I,DI}_trueEnvU`).
A typed-demand model where proofs denote only `⊥` dissolves that demand.  What remains is
model-independent and holds with the K readback: the clause instance at every pair of proofs
(`lrSCore_whStepK_kConstFn_app_all`) and the app-case conclusion (`lrSCore_whStep{K,CK}_appIrr`).
The model obligation `link_pmajor_K` needs — `ReadbackModelInv` for K steps — fails over
`ApproxI` and over `ApproxDI` (`not_readbackModelInv_*`: `Sort 0` has the compact `sort`,
`kRec h` does not), so a typed model must give a recursor at a proposition major a denotation that
does not inspect the major.

**§6 Substitution.**  The projection canon is not substitution-stable syntactically: when a
substitution makes the major a constructor, the redex takes ι (actual fields) while the K reduct
carries projections of the constructor.  The two are bridged by: the projection of a constructor
reads back to the field (`redR_projField_ctorMajor`); in the typed relation the λ clause at a
proposition domain has `⊥` demands, so any typed convertible proof arguments relate the
applications (`lrSCoreT_app_botDemand` — the proposition collapse); in the untyped relation the
argument premise follows from the field's diagonal along that readback (`lrSCore_app_of_redR_arg`).
Control: `lrSCore_whStepCK_mixAnd_kι`.  The readback half is for projection (non-revealed) fields;
for an index-revealed field the canon field is the index argument, related to the actual field by
the conversion the constructor's typing forces (family-application injectivity strength).

**§7 The index premise's gap.**  Syntactic agreement misses indices that are convertible but not
equal: at the admitted `Eq` (`eqEnvT`), `h : Eq α a ((λx.x) a)` gives a K redex convertible to
`Sort 0` on which the core is stuck (`not_fundamentalLRST_whStepCK_eqEnvT`).  The alternative
premise (a common type of major and canon) would make `NormalR` of a stuck K redex a negative
typing statement — family-application injectivity — so the syntactic check stays and this is the
named gap.

**§8 Higher-order recursive fields** (`Acc.intro`'s `Π y, r y x → Acc r y`): no ι witness
(`not_iotaWitness_of_higherOrderField`), so no legacy ι and no W-K point.

**§9 First-order recursive singletons** at the admitted `Loop`: `redR_whStepCK_loopKRedex`,
`loopK_conv`, `lrSCore_whStepCK_loop`/`_symm`.

`closure_claim = 0`.  No `sorry`, axioms ⊆ `{propext, Quot.sound}`.
-/

namespace Rcic.Declarative.NativeValleys.ReadbackCKAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit

variable {E : ResolvedEnv} {n : Nat}

/-! ### §1 — the untyped deterministic core `WhStepCK` -/

/-- `x` is a constructor-headed spine. -/
def IsCtorSpine (E : ResolvedEnv) (x : Expr Nat) : Prop :=
  ∃ (c : Nat) (us : List Level) (ys : List (Expr Nat)) (m : CheckedMember),
    x = foldApps (.const c us) ys ∧ E.members c = some m ∧ m.mclass = .constructorM

/-- A field-free proposition-singleton witness: K's domain. -/
def KFreeW {E : ResolvedEnv} (w : IotaWitness E) : Prop :=
  w.fields = [] ∧ w.nMinors = 1 ∧ piBody w.famMember.mtype = .sort .zero

/-- `r` is the recursor of a field-free proposition singleton. -/
def KFreeRec (E : ResolvedEnv) (r : Nat) : Prop :=
  ∃ w : IotaWitness E, w.recRef = r ∧ KFreeW w

/-! #### the projection canon (fieldful, non-recursive proposition singletons) -/

/-- A λ-telescope. -/
def lamTel : List (Expr Nat) → Expr Nat → Expr Nat
  | [], b => b
  | A :: As, b => .lam A (lamTel As b)

/-- The head Π-domain of an optional type (`Sort 0` if there is none). -/
def piDomOr : Option (Expr Nat) → Expr Nat
  | some (.pi A _) => A
  | _ => .sort .zero

/-- `applyTel`, defaulting to `Sort 0`. -/
def applyTelOr (xs : List (Expr Nat)) (T : Expr Nat) : Expr Nat := (applyTel xs T).getD (.sort .zero)

/-- The first `k` Π-domains of a type (`[]` if it has fewer). -/
def peelDomsOr (k : Nat) (T : Expr Nat) : List (Expr Nat) :=
  match peelPis k T with
  | some (ds, _) => ds
  | none => []

/-- The recursor's levels at a proposition motive: the motive universe `param famArity` set to `0`. -/
def projLevels {E : ResolvedEnv} (w : IotaWitness E) : List Level :=
  w.ls.set w.famMember.arity .zero

/-- The family's levels at the redex. -/
def famLevels {E : ResolvedEnv} (w : IotaWitness E) : List Level :=
  w.ls.take w.famMember.arity

/-- The number of constructor fields. -/
def fieldCount {E : ResolvedEnv} (w : IotaWitness E) : Nat :=
  piCount w.ctorMember.mtype - w.nparams

/-- The motive's index variables, seen from inside the motive (`idx₁ … idx_q`; the major is
    `bvar 0`). -/
def motIdx (q : Nat) : List (Expr Nat) := (List.range q).reverse.map (fun j => .bvar (j + 1))

/-- The redex's index arguments. -/
def redexIdx {E : ResolvedEnv} (w : IotaWitness E) : List (Expr Nat) :=
  w.preMajor.drop (w.nparams + 1 + w.nMinors)

/-- The constructor's result indices at `params` and `fields` (the stored constructor type
    applied through `applyTel`, its result spine after the parameters). -/
def resultIdxAt {E : ResolvedEnv} (w : IotaWitness E) (params fields : List (Expr Nat)) :
    List (Expr Nat) :=
  ((appsSpine (applyTelOr (params ++ fields)
    (instantiateLevels w.ls w.ctorMember.mtype))).2).drop w.nparams

/-- The position of field `j`'s local among the constructor's stored result indices, if the field
    is revealed there (`FieldSafe`'s second arm). -/
def revealedPos? {E : ResolvedEnv} (w : IotaWitness E) (j : Nat) : Option Nat :=
  ((appsSpine w.ctorResult).2.drop w.nparams).findIdx?
    (fun e => decide (e = Expr.bvar (fieldCount w - 1 - j)))

/-- The number of recursive fields. -/
def recCountOf : List RecKind → Nat
  | [] => 0
  | .plain :: ks => recCountOf ks
  | .directRec :: ks => recCountOf ks + 1

/-- The binder position of field `i` in the minor: an IH binder follows each recursive field. -/
def minorPosOf : List RecKind → Nat → Nat
  | _, 0 => 0
  | [], i + 1 => i + 1
  | .plain :: ks, i + 1 => minorPosOf ks i + 1
  | .directRec :: ks, i + 1 => minorPosOf ks i + 2

/-- **One projection**: field `i` of `x` is the recursor at the proposition motive
    `λ idx (t : I params idx). Dᵢ[params, pr₀ t, …, pr_{i-1} t]` with the minor
    `λ (f₀ : D₀) … (f_{k-1} : D_{k-1}). fᵢ`.  `prevM` are the earlier projections of the motive's
    major `bvar 0`, inside the motive.  Every binder type is read off a stored declaration: the
    family type (motive binders), the constructor type (field types, minor binders). -/
def projOne {E : ResolvedEnv} (w : IotaWitness E) (i : Nat) (params idxs prevM : List (Expr Nat))
    (x : Expr Nat) : Expr Nat :=
  let q := w.nindices
  let ctorTy := instantiateLevels w.ls w.ctorMember.mtype
  let famTy := instantiateLevels (famLevels w) w.famMember.mtype
  let ft := piDomOr (applyTel (params.map (lift 0 (q + 1)) ++ prevM) ctorTy)
  let motDoms := peelDomsOr q (applyTelOr params famTy) ++
    [foldApps (.const w.familyRef (famLevels w))
      (params.map (lift 0 q) ++ (List.range q).reverse.map Expr.bvar)]
  let mot := lamTel motDoms ft
  let nb := fieldCount w + recCountOf w.kinds
  let mn := lamTel (peelDomsOr nb (minorTel mot w.nparams
      (foldApps (.const w.ctorRef (famLevels w)) params) w.kinds (applyTelOr params ctorTy)))
    (.bvar (nb - 1 - minorPosOf w.kinds i))
  recCall (.const w.recRef (projLevels w)) (params ++ [mot, mn] ++ idxs) x

/-- **One canon field**: an index-revealed field is the matching index argument of the redex (the
    canon's constructor must have the redex's type); any other field is its projection. -/
def canonField {E : ResolvedEnv} (w : IotaWitness E) (j : Nat) (params idxs prevM : List (Expr Nat))
    (x : Expr Nat) : Expr Nat :=
  match revealedPos? w j with
  | some p => idxs.getD p (.sort .zero)
  | none => projOne w j params idxs prevM x

/-- The first `i` canon fields of `x`. -/
def projAll {E : ResolvedEnv} (w : IotaWitness E) :
    Nat → List (Expr Nat) → List (Expr Nat) → Expr Nat → List (Expr Nat)
  | 0, _, _, _ => []
  | i + 1, params, idxs, x =>
      projAll w i params idxs x ++
        [canonField w i params idxs
          (projAll w i (params.map (lift 0 (w.nindices + 1))) (motIdx w.nindices) (.bvar 0)) x]

/-- **The projection canon's fields** at the major `x` of a redex with witness data `w`:
    `canon x = intro params (pr₀ x) … (pr_{k-1} x)`. -/
def projFields {E : ResolvedEnv} (w : IotaWitness E) (x : Expr Nat) : List (Expr Nat) :=
  projAll w (fieldCount w) (w.preMajor.take w.nparams)
    (w.preMajor.drop (w.nparams + 1 + w.nMinors)) x

/-- A fieldful, non-recursive proposition-singleton witness: the projection canon's domain. -/
def KFieldW {E : ResolvedEnv} (w : IotaWitness E) : Prop :=
  w.fields ≠ [] ∧ w.nMinors = 1 ∧ piBody w.famMember.mtype = .sort .zero ∧
    w.recMember.arity = w.famMember.arity + 1

/-- `r` is the recursor of a fieldful, non-recursive proposition singleton. -/
def KProjRec (E : ResolvedEnv) (r : Nat) : Prop :=
  ∃ w : IotaWitness E, w.recRef = r ∧ KFieldW w

/-- **The unified readback core.** -/
inductive WhStepCK (E : ResolvedEnv) (Γ : LCtx) : Expr Nat → Expr Nat → Prop
  | ctx {a b : Expr Nat} (h : WhStepCtx E Γ a b) : WhStepCK E Γ a b
  | kStar {w : IotaWitness E} {x : Expr Nat} (hK : KFreeW w) (hnc : ¬ IsCtorSpine E x)
      (hidx : redexIdx w = resultIdxAt w (w.preMajor.take w.nparams) []) :
      WhStepCK E Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w)
  | kProj {w : IotaWitness E} {x : Expr Nat} (hK : KFieldW w) (hnc : ¬ IsCtorSpine E x)
      (hf : w.fields = projFields w x)
      (hidx : redexIdx w = resultIdxAt w (w.preMajor.take w.nparams) (projFields w x)) :
      WhStepCK E Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w)
  | recMajor {r : Nat} {m : CheckedMember} {ls : List Level} {pre : List (Expr Nat)}
      {x x' : Expr Nat}
      (hm : E.members r = some m) (hrec : m.mclass = .recursorM)
      (hlen : pre.length + 1 = piCount m.mtype) (hnK : ¬ KFreeRec E r) (hnP : ¬ KProjRec E r)
      (h : WhStepCK E Γ x x') :
      WhStepCK E Γ (recCall (.const r ls) pre x) (recCall (.const r ls) pre x')
  | appHead {f f' a : Expr Nat} (h : WhStepCK E Γ f f') :
      WhStepCK E Γ (.app f a) (.app f' a)

/-- Field-free contractum determinism: two field-free witnesses of one recursor with one
    pre-major spine have the same contractum (the minor). -/
theorem iotaRhsOf_kfree_eq {w₁ w₂ : IotaWitness E} (h₁ : KFreeW w₁) (h₂ : KFreeW w₂)
    (hr : w₁.recRef = w₂.recRef) (hp : w₁.preMajor = w₂.preMajor) :
    iotaRhsOf w₁ = iotaRhsOf w₂ := by
  obtain ⟨hf1, hnm1, _⟩ := h₁
  obtain ⟨hf2, hnm2, _⟩ := h₂
  have hfam : w₁.familyRef = w₂.familyRef := by
    have e1 := w₁.hrecIdx; have e2 := w₂.hrecIdx; omega
  have hctorI1 : w₁.ctorIdx = 0 := by have e := w₁.hidx; omega
  have hctorI2 : w₂.ctorIdx = 0 := by have e := w₂.hidx; omega
  have hctorR : w₁.ctorRef = w₂.ctorRef := by
    have e1 := w₁.hctorIdx; have e2 := w₂.hctorIdx; omega
  have hcm : w₁.ctorMember = w₂.ctorMember :=
    Option.some.inj (by rw [← w₁.hctor, ← w₂.hctor, hctorR])
  have hnpar : w₁.nparams = w₂.nparams := by
    have e1 := w₁.hnpar; have e2 := w₂.hnpar
    rw [hf1] at e1; rw [hf2] at e2
    simp only [List.length_nil, Nat.add_zero] at e1 e2
    rw [hcm] at e1; omega
  have hminor : w₁.minor = w₂.minor := by
    have e1 := w₁.hminor; have e2 := w₂.hminor
    rw [hctorI1, hnpar, hp] at e1
    rw [hctorI2] at e2
    simp only [Nat.add_zero] at e1 e2
    exact Option.some.inj (e1.symm.trans e2)
  have hr1 : iotaRhsOf w₁ = w₁.minor := by
    unfold iotaRhsOf; rw [hf1]; rfl
  have hr2 : iotaRhsOf w₂ = w₂.minor := by
    unfold iotaRhsOf; rw [hf2]; rfl
  rw [hr1, hr2, hminor]

/-- Two witnesses of one recursor at one pre-major spine, both with one minor, have the
    same number of fields (the recursor fixes `nparams` and the constructor member). -/
theorem fields_length_eq_of_same_lhs {w₁ w₂ : IotaWitness E}
    (hnm1 : w₁.nMinors = 1) (hnm2 : w₂.nMinors = 1)
    (hr : w₁.recRef = w₂.recRef) (hp : w₁.preMajor = w₂.preMajor) :
    w₁.fields.length = w₂.fields.length := by
  have hci1 : w₁.ctorIdx = 0 := by have e := w₁.hidx; omega
  have hci2 : w₂.ctorIdx = 0 := by have e := w₂.hidx; omega
  have hcr : w₁.ctorRef = w₂.ctorRef := by
    have e1 := w₁.hctorIdx; have e2 := w₂.hctorIdx
    have f1 := w₁.hrecIdx; have f2 := w₂.hrecIdx; omega
  have hlen : w₁.preMajor.length = w₂.preMajor.length := congrArg _ hp
  obtain ⟨_, hcm, _, _, _, hnp, _, _⟩ := iotaWitness_env_of_same_refs hr hcr hlen
  have e1 := w₁.hnpar; have e2 := w₂.hnpar
  rw [hcm, hnp] at e1
  omega

/-- Auxiliary induction for `whStepCtx` at a partial `r`-spine (`r` a recursor): no context
    step has a `foldApps (.const r ls) xs` source with fewer args than the major position. -/
theorem whStepCtx_recPrefix_false_aux {Γ : LCtx} {r : Nat} {m : CheckedMember}
    (hW : EnvWfT E) (hm : E.members r = some m) (hrec : m.mclass = .recursorM)
    {a e : Expr Nat} (h : WhStepCtx E Γ a e) :
    ∀ {ls : List Level} {xs : List (Expr Nat)}, a = foldApps (.const r ls) xs →
      xs.length + 1 ≤ piCount m.mtype → False := by
  induction h with
  | beta A body arg =>
      intro ls xs heq hlen
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        injection heq with hf _
        exact F8EtaK.foldApps_const_ne_lam_any hf.symm
  | zeta A v b =>
      intro ls xs heq hlen
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        exact Expr.noConfusion heq
  | zetaLocal _ =>
      intro ls xs heq hlen
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        exact Expr.noConfusion heq
  | delta hres hbody =>
      intro ls xs heq hlen
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · injection heq with hrr _
        rw [hrr] at hres
        obtain ⟨hd, _⟩ := PiModelDeltaIotaAudit.envWfT_member_body_closed hW _ _ _ hres hbody
        have hm' : _ = m := Option.some.inj (hres.symm.trans hm)
        subst hm'
        exact hd.2.2.1 hrec
      · rw [foldApps_snoc] at heq
        exact Expr.noConfusion heq
  | iota hI =>
      intro ls xs heq hlen
      cases hI with
      | ofU w' =>
          rw [iotaLhsOf_eq_app, ← foldApps_snoc] at heq
          obtain ⟨hconst, hargs⟩ := foldApps_const_inj heq
          injection hconst with hrr _
          have hm' : w'.recMember = m :=
            Option.some.inj (w'.hrec.symm.trans (hrr.symm ▸ hm))
          have h1 := w'.hpre; have h2 := w'.hnmin
          rw [hm'] at h2
          have hlenEq := congrArg List.length hargs
          simp only [List.length_append, List.length_singleton] at hlenEq
          omega
      | ofUS w' =>
          unfold iotaLhsOfS at heq
          rw [recCall_eq_app, ← foldApps_snoc] at heq
          obtain ⟨hconst, hargs⟩ := foldApps_const_inj heq
          injection hconst with hrr _
          have hm' : w'.recMember = m :=
            Option.some.inj (w'.hrec.symm.trans (hrr.symm ▸ hm))
          have h1 := w'.hpre; have h2 := w'.hnmin
          rw [hm'] at h2
          have hlenEq := congrArg List.length hargs
          simp only [List.length_append, List.length_singleton] at hlenEq
          omega
  | lit t =>
      intro ls xs heq hlen
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        exact Expr.noConfusion heq
  | appHead hf ih =>
      intro ls xs heq hlen
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        injection heq with hf' _
        exact ih hf' (by
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen
          omega)

/-- Auxiliary induction for `whStepCK_recPrefix_false`. -/
theorem whStepCK_recPrefix_false_aux {Γ : LCtx} {r : Nat} {m : CheckedMember}
    (hW : EnvWfT E) (hm : E.members r = some m) (hrec : m.mclass = .recursorM)
    {a e : Expr Nat} (h : WhStepCK E Γ a e) :
    ∀ {ls : List Level} {xs : List (Expr Nat)}, a = foldApps (.const r ls) xs →
      xs.length + 1 ≤ piCount m.mtype → False := by
  induction h with
  | ctx hs =>
      intro ls xs heq hlen
      exact whStepCtx_recPrefix_false_aux hW hm hrec hs heq hlen
  | kStar hK hnc _ =>
      rename_i w x hidx
      intro ls xs heq hlen
      rw [recCall_eq_app, ← foldApps_snoc] at heq
      obtain ⟨hconst, hargs⟩ := foldApps_const_inj heq
      injection hconst with hrr _
      have hm' : w.recMember = m := Option.some.inj (w.hrec.symm.trans (hrr.symm ▸ hm))
      have h1 := w.hpre; have h2 := w.hnmin
      rw [hm'] at h2
      have hlenEq := congrArg List.length hargs
      simp only [List.length_append, List.length_singleton] at hlenEq
      omega
  | kProj hK hnc hf _ =>
      rename_i w x hidx
      intro ls xs heq hlen
      rw [recCall_eq_app, ← foldApps_snoc] at heq
      obtain ⟨hconst, hargs⟩ := foldApps_const_inj heq
      injection hconst with hrr _
      have hm' : w.recMember = m := Option.some.inj (w.hrec.symm.trans (hrr.symm ▸ hm))
      have h1 := w.hpre; have h2 := w.hnmin
      rw [hm'] at h2
      have hlenEq := congrArg List.length hargs
      simp only [List.length_append, List.length_singleton] at hlenEq
      omega
  | recMajor hm' hrec' hlen' hnK hnP hs' =>
      intro ls xs heq hlen
      rw [recCall_eq_app, ← foldApps_snoc] at heq
      obtain ⟨hconst, hargs⟩ := foldApps_const_inj heq
      injection hconst with hrr _
      have hm'' : _ = m := Option.some.inj (hm'.symm.trans (hrr.symm ▸ hm))
      subst hm''
      have hlenEq := congrArg List.length hargs
      simp only [List.length_append, List.length_singleton] at hlenEq
      omega
  | appHead hf ih =>
      intro ls xs heq hlen
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, x, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        injection heq with hf' _
        exact ih hf' (by
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen
          omega)

/-- Partial recursor spines (fewer arguments than the major position) take no `WhStepCK` step. -/
theorem whStepCK_recPrefix_false (hW : EnvWfT E) {Γ : LCtx} {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hrec : m.mclass = .recursorM) {ls : List Level} :
    ∀ (xs : List (Expr Nat)), xs.length + 1 ≤ piCount m.mtype →
      ∀ e, ¬ WhStepCK E Γ (foldApps (.const r ls) xs) e :=
  fun xs hlen e h => whStepCK_recPrefix_false_aux hW hm hrec h rfl hlen

/-- Auxiliary induction for `whStepCK_ctorSpine_false`. -/
theorem whStepCK_ctorSpine_false_aux {Γ : LCtx} {c : Nat} {m : CheckedMember}
    (hW : EnvWfT E) (hm : E.members c = some m) (hctor : m.mclass = .constructorM)
    {us : List Level} {a e : Expr Nat} (h : WhStepCK E Γ a e) :
    ∀ (ys : List (Expr Nat)), a = foldApps (.const c us) ys → False := by
  induction h with
  | ctx hs =>
      intro ys heq
      exact whStepCtx_ctorApp_false_aux hW hm hctor hs ys heq
  | kStar hK hnc _ =>
      rename_i w x hidx
      intro ys heq
      rw [recCall_eq_app, ← foldApps_snoc] at heq
      obtain ⟨hconst, _⟩ := foldApps_const_inj heq
      injection hconst with hrr _
      have hm' : w.recMember = m := Option.some.inj (w.hrec.symm.trans (hrr.symm ▸ hm))
      subst hm'
      exact MemberClass.noConfusion (w.hrecK.symm.trans hctor)
  | kProj hK hnc hf _ =>
      rename_i w x hidx
      intro ys heq
      rw [recCall_eq_app, ← foldApps_snoc] at heq
      obtain ⟨hconst, _⟩ := foldApps_const_inj heq
      injection hconst with hrr _
      have hm' : w.recMember = m := Option.some.inj (w.hrec.symm.trans (hrr.symm ▸ hm))
      subst hm'
      exact MemberClass.noConfusion (w.hrecK.symm.trans hctor)
  | recMajor hm' hrec' hlen' hnK hnP hs' =>
      intro ys heq
      rw [recCall_eq_app, ← foldApps_snoc] at heq
      obtain ⟨hconst, _⟩ := foldApps_const_inj heq
      injection hconst with hrr _
      have hm'' : _ = m := Option.some.inj (hm'.symm.trans (hrr.symm ▸ hm))
      subst hm''
      exact MemberClass.noConfusion (hrec'.symm.trans hctor)
  | appHead hf ih =>
      intro ys heq
      rcases list_eq_nil_or_snoc ys with rfl | ⟨pre, y, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        injection heq with hf' _
        exact ih pre hf'

/-- Constructor spines take no `WhStepCK` step. -/
theorem whStepCK_ctorSpine_false (hW : EnvWfT E) {Γ : LCtx} {c : Nat} {m : CheckedMember}
    (hm : E.members c = some m) (hctor : m.mclass = .constructorM) {us : List Level} :
    ∀ (ys : List (Expr Nat)) (e : Expr Nat), ¬ WhStepCK E Γ (foldApps (.const c us) ys) e :=
  fun ys e h => whStepCK_ctorSpine_false_aux hW hm hctor h ys rfl

/-- A context step at a `kStar` source (`preMajor` of a witness, non-constructor major)
    cannot exist: ι wants a constructor major, every other arm fails by shape or arity. -/
theorem whStepCtx_recCall_nonCtorMajor_aux {Γ : LCtx} {a b : Expr Nat}
    (hW : EnvWfT E) (hs : WhStepCtx E Γ a b) :
    ∀ {w : IotaWitness E} {x : Expr Nat},
      a = recCall (.const w.recRef w.ls) w.preMajor x → ¬ IsCtorSpine E x → False := by
  induction hs with
  | beta A body arg =>
      intro w x heq hnc
      rw [recCall_eq_app] at heq
      injection heq with hf _
      exact F8EtaK.foldApps_const_ne_lam_any hf.symm
  | zeta A v b =>
      intro w x heq hnc
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | zetaLocal _ =>
      intro w x heq hnc
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | delta hres hbody =>
      intro w x heq hnc
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | iota hI =>
      intro w x heq hnc
      cases hI with
      | ofU w' =>
          rw [iotaLhsOf_eq_app, recCall_eq_app] at heq
          injection heq with hf hx'
          exact hnc ⟨w'.ctorRef, w'.lsC, w'.ctorParams ++ w'.fields, w'.ctorMember,
            hx'.symm, w'.hctor, w'.hctorK⟩
      | ofUS w' =>
          unfold iotaLhsOfS at heq
          rw [recCall_eq_app, recCall_eq_app] at heq
          injection heq with hf hx'
          exact hnc ⟨w'.ctorRef, w'.lsC, w'.ctorParams ++ w'.fields, w'.ctorMember,
            hx'.symm, w'.hctor, w'.hctorK⟩
  | lit t =>
      intro w x heq hnc
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | appHead hf ih =>
      intro w x heq hnc
      rw [recCall_eq_app] at heq
      injection heq with hf' _
      exact whStepCtx_recPrefix_false_aux hW w.hrec w.hrecK hf hf'
        (by have h1 := w.hpre; have h2 := w.hnmin; omega)

/-- A context step at a saturated `recMajor` source cannot coexist with a core step of its
    major: ι forces the major to be a constructor spine (no `WhStepCK` step), the rest fail
    by shape or arity. -/
theorem whStepCtx_recCall_innerCK_aux {Γ : LCtx} {a b : Expr Nat}
    (hW : EnvWfT E) (hs : WhStepCtx E Γ a b) :
    ∀ {r : Nat} {ls : List Level} {pre : List (Expr Nat)} {x : Expr Nat} {m : CheckedMember},
      a = recCall (.const r ls) pre x → E.members r = some m →
      m.mclass = .recursorM → pre.length + 1 = piCount m.mtype →
      ∀ {x' : Expr Nat}, WhStepCK E Γ x x' → False := by
  induction hs with
  | beta A body arg =>
      intro r ls pre x m heq hm hrec hlen x' hsx
      rw [recCall_eq_app] at heq
      injection heq with hf _
      exact F8EtaK.foldApps_const_ne_lam_any hf.symm
  | zeta A v b =>
      intro r ls pre x m heq hm hrec hlen x' hsx
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | zetaLocal _ =>
      intro r ls pre x m heq hm hrec hlen x' hsx
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | delta hres hbody =>
      intro r ls pre x m heq hm hrec hlen x' hsx
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | iota hI =>
      intro r ls pre x m heq hm hrec hlen x' hsx
      cases hI with
      | ofU w' =>
          rw [iotaLhsOf_eq_app, recCall_eq_app] at heq
          injection heq with hf hx
          subst hx
          exact whStepCK_ctorSpine_false_aux hW w'.hctor w'.hctorK hsx _ rfl
      | ofUS w' =>
          unfold iotaLhsOfS at heq
          rw [recCall_eq_app, recCall_eq_app] at heq
          injection heq with hf hx
          subst hx
          exact whStepCK_ctorSpine_false_aux hW w'.hctor w'.hctorK hsx _ rfl
  | lit t =>
      intro r ls pre x m heq hm hrec hlen x' hsx
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | appHead hf ih =>
      intro r ls pre x m heq hm hrec hlen x' hsx
      rw [recCall_eq_app] at heq
      injection heq with hf' _
      exact whStepCtx_recPrefix_false_aux hW hm hrec hf hf' (by omega)

/-- No `WhStepCtx` step has a `.lam` source. -/
theorem whStepCtx_lam_false_aux {Γ : LCtx} {a e : Expr Nat} (h : WhStepCtx E Γ a e) :
    ∀ {A b : Expr Nat}, a = .lam A b → False := by
  induction h with
  | beta A b arg => intro A' b' heq; exact Expr.noConfusion heq
  | zeta A v b => intro A' b' heq; exact Expr.noConfusion heq
  | zetaLocal _ => intro A' b' heq; exact Expr.noConfusion heq
  | delta _ _ => intro A' b' heq; exact Expr.noConfusion heq
  | iota hI =>
      intro A' b' heq
      obtain ⟨r, ls, pre, major, _, hl, _, _⟩ := derivedIotaU_recHead hI
      rw [heq] at hl
      exact F8EtaK.foldApps_const_ne_lam_any hl.symm
  | lit t => intro A' b' heq; exact Expr.noConfusion heq
  | appHead _ _ => intro A' b' heq; exact Expr.noConfusion heq

/-- No `WhStepCK` step has a `.lam` source. -/
theorem whStepCK_lam_false_aux {Γ : LCtx} {a e : Expr Nat} (h : WhStepCK E Γ a e) :
    ∀ {A b : Expr Nat}, a = .lam A b → False := by
  induction h with
  | ctx hs => intro A b heq; exact whStepCtx_lam_false_aux hs heq
  | kStar hK hnc _ =>
      intro A b heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | kProj hK hnc hf _ =>
      intro A b heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | recMajor hm hrec hlen hnK hnP hs =>
      intro A b heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | appHead _ _ => intro A b heq; exact Expr.noConfusion heq

/-- No `WhStepCK` step has a `.sort` source. -/
theorem whStepCK_sort_false_aux {Γ : LCtx} {a e : Expr Nat} (h : WhStepCK E Γ a e) :
    ∀ {u : Level}, a = .sort u → False := by
  induction h with
  | ctx hs => intro u heq; exact whStepCtx_sort_false (heq ▸ hs)
  | kStar hK hnc _ =>
      intro u heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | kProj hK hnc hf _ =>
      intro u heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | recMajor hm hrec hlen hnK hnP hs =>
      intro u heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | appHead _ _ => intro u heq; exact Expr.noConfusion heq

/-- No `WhStepCK` step has a `.pi` source. -/
theorem whStepCK_pi_false_aux {Γ : LCtx} {a e : Expr Nat} (h : WhStepCK E Γ a e) :
    ∀ {A B : Expr Nat}, a = .pi A B → False := by
  induction h with
  | ctx hs => intro A B heq; exact whStepCtx_pi_false (heq ▸ hs)
  | kStar hK hnc _ =>
      intro A B heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | kProj hK hnc hf _ =>
      intro A B heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | recMajor hm hrec hlen hnK hnP hs =>
      intro A B heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | appHead _ _ => intro A B heq; exact Expr.noConfusion heq

/-- Auxiliary induction for `WhStepCK` at an admitted-family head: an `.inductiveM` spine
    takes no step (K steps and `recMajor` are recursor-headed). -/
theorem whStepCK_famApp_false_aux {Γ : LCtx} {r : Nat} {m : CheckedMember}
    (hW : EnvWfT E) (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {a e : Expr Nat} (h : WhStepCK E Γ a e) :
    ∀ {ls : List Level} {xs : List (Expr Nat)}, a = foldApps (.const r ls) xs → False := by
  induction h with
  | ctx hs =>
      intro ls xs heq
      exact whStepCtx_famApp_false_aux hW hm hind hs xs heq
  | kStar hK hnc _ =>
      rename_i w x hidx
      intro ls xs heq
      rw [recCall_eq_app, ← foldApps_snoc] at heq
      obtain ⟨hconst, _⟩ := foldApps_const_inj heq
      injection hconst with hrr _
      have hm' : w.recMember = m := Option.some.inj (w.hrec.symm.trans (hrr.symm ▸ hm))
      subst hm'
      exact MemberClass.noConfusion (w.hrecK.symm.trans hind)
  | kProj hK hnc hf _ =>
      rename_i w x hidx
      intro ls xs heq
      rw [recCall_eq_app, ← foldApps_snoc] at heq
      obtain ⟨hconst, _⟩ := foldApps_const_inj heq
      injection hconst with hrr _
      have hm' : w.recMember = m := Option.some.inj (w.hrec.symm.trans (hrr.symm ▸ hm))
      subst hm'
      exact MemberClass.noConfusion (w.hrecK.symm.trans hind)
  | recMajor hm' hrec' hlen' hnK hnP hs' =>
      intro ls xs heq
      rw [recCall_eq_app, ← foldApps_snoc] at heq
      obtain ⟨hconst, _⟩ := foldApps_const_inj heq
      injection hconst with hrr _
      have hm'' : _ = m := Option.some.inj (hm'.symm.trans (hrr.symm ▸ hm))
      subst hm''
      exact MemberClass.noConfusion (hrec'.symm.trans hind)
  | appHead hf ih =>
      intro ls xs heq
      rcases list_eq_nil_or_snoc xs with rfl | ⟨pre, y, rfl⟩
      · exact Expr.noConfusion heq
      · rw [foldApps_snoc] at heq
        injection heq with hf' _
        exact ih hf'

/-- **`WhStepCK` is an instance of `#7673`'s `ReadbackLaws`.** -/
theorem readbackLaws_whStepCK (E : ResolvedEnv) : ReadbackLaws E (WhStepCK E) where
  sort_normal := fun _ _ _ h => whStepCK_sort_false_aux h rfl
  pi_normal := fun _ _ _ _ h => whStepCK_pi_false_aux h rfl
  famApp_normal := fun hW _ _ _ hm hind _ xs _ h =>
    whStepCK_famApp_false_aux hW hm hind h rfl
  appHead := fun _ _ _ _ h => .appHead h
  beta := fun _ A b a => .ctx (.beta A b a)

/-- Decomposing a `DerivedIotaU` at an `.app`-headed source: the app head is the witness's
    recursor spine, one arm per witness kind. -/
theorem derivedIotaU_app_head {E : ResolvedEnv} {lhs rhs f a : Expr Nat}
    (hI : DerivedIotaU E lhs rhs) (hl : lhs = .app f a) :
    (∃ w : IotaWitness E,
      f = foldApps (.const w.recRef w.ls) w.preMajor ∧
      w.preMajor.length + 1 ≤ piCount w.recMember.mtype) ∨
    (∃ w : IotaWitnessS E,
      f = foldApps (.const w.recRef w.ls) w.preMajor ∧
      w.preMajor.length + 1 ≤ piCount w.recMember.mtype) := by
  cases hI with
  | ofU w =>
      rw [iotaLhsOf_eq_app] at hl
      injection hl with hf _
      exact Or.inl ⟨w, hf.symm, by have h1 := w.hpre; have h2 := w.hnmin; omega⟩
  | ofUS w =>
      unfold iotaLhsOfS at hl
      rw [recCall_eq_app] at hl
      injection hl with hf _
      exact Or.inr ⟨w, hf.symm, by have h1 := w.hpre; have h2 := w.hnmin; omega⟩

/-- A context step and a core step at one source coincide (context-side analysis). -/
theorem whStepCK_ctx_det (hW : EnvWfT E) {Γ : LCtx} {a b : Expr Nat}
    (hs₁ : WhStepCtx E Γ a b) {c : Expr Nat} (h₂ : WhStepCK E Γ a c) : b = c := by
  induction h₂ generalizing b with
  | ctx s₂ =>
      exact whDetCtx_of_whDet Γ (PiModelDeltaIotaAudit.whDet_of_envWfT hW) hs₁ s₂
  | kStar hK hnc _ =>
      exact (whStepCtx_recCall_nonCtorMajor_aux hW hs₁ rfl hnc).elim
  | kProj hK hnc hf _ =>
      exact (whStepCtx_recCall_nonCtorMajor_aux hW hs₁ rfl hnc).elim
  | recMajor hm' hrec' hlen' hnK hnP hs' =>
      exact (whStepCtx_recCall_innerCK_aux hW hs₁ rfl hm' hrec' hlen' hs').elim
  | appHead s₂ ih =>
      cases hs₁ with
      | beta A body arg => exact (whStepCK_lam_false_aux s₂ rfl).elim
      | iota hI =>
          rcases derivedIotaU_app_head hI rfl with ⟨w', hf', hlen⟩ | ⟨w', hf', hlen⟩
          · subst hf'
            exact (whStepCK_recPrefix_false_aux hW w'.hrec w'.hrecK s₂ rfl hlen).elim
          · subst hf'
            exact (whStepCK_recPrefix_false_aux hW w'.hrec w'.hrecK s₂ rfl hlen).elim
      | appHead hf => exact congrArg (fun g => Expr.app g _) (ih hf)

/-! #### the projection canon: determinism of the contractum, existence of the step -/

/-- `projOne` reads a witness only through the recursor-side data `iotaRhsOf` reads;
    two witnesses that agree there give the same projection. -/
theorem projOne_eq_of {w₁ w₂ : IotaWitness E} (hr : w₁.recRef = w₂.recRef)
    (hls : w₁.ls = w₂.ls) (hfr : w₁.familyRef = w₂.familyRef)
    (hfm : w₁.famMember = w₂.famMember) (hcm : w₁.ctorMember = w₂.ctorMember)
    (hcrf : w₁.ctorRef = w₂.ctorRef)
    (hni : w₁.nindices = w₂.nindices) (hnp : w₁.nparams = w₂.nparams)
    (hk : w₁.kinds = w₂.kinds)
    (i : Nat) (params idxs prevM : List (Expr Nat)) (x : Expr Nat) :
    projOne w₁ i params idxs prevM x = projOne w₂ i params idxs prevM x := by
  unfold projOne projLevels famLevels fieldCount
  rw [hr, hls, hfr, hfm, hcm, hcrf, hni, hnp, hk]

/-- `revealedPos?` reads only `ctorResult`, `nparams` and the ctor member. -/
theorem revealedPos?_eq_of {w₁ w₂ : IotaWitness E}
    (hcm : w₁.ctorMember = w₂.ctorMember) (hnp : w₁.nparams = w₂.nparams)
    (hcr : w₁.ctorResult = w₂.ctorResult) (j : Nat) :
    revealedPos? w₁ j = revealedPos? w₂ j := by
  unfold revealedPos? fieldCount
  rw [hcm, hnp, hcr]

/-- The same invariance for `canonField`. -/
theorem canonField_eq_of {w₁ w₂ : IotaWitness E} (hr : w₁.recRef = w₂.recRef)
    (hls : w₁.ls = w₂.ls) (hfr : w₁.familyRef = w₂.familyRef)
    (hfm : w₁.famMember = w₂.famMember) (hcm : w₁.ctorMember = w₂.ctorMember)
    (hcrf : w₁.ctorRef = w₂.ctorRef)
    (hni : w₁.nindices = w₂.nindices) (hnp : w₁.nparams = w₂.nparams)
    (hk : w₁.kinds = w₂.kinds) (hcr : w₁.ctorResult = w₂.ctorResult)
    (i : Nat) (params idxs prevM : List (Expr Nat)) (x : Expr Nat) :
    canonField w₁ i params idxs prevM x = canonField w₂ i params idxs prevM x := by
  unfold canonField
  rw [revealedPos?_eq_of hcm hnp hcr i]
  cases revealedPos? w₂ i with
  | some p => rfl
  | none => exact projOne_eq_of hr hls hfr hfm hcm hcrf hni hnp hk i params idxs prevM x

/-- The same invariance for the projection list, by recursion on its length. -/
theorem projAll_eq_of {w₁ w₂ : IotaWitness E} (hr : w₁.recRef = w₂.recRef)
    (hls : w₁.ls = w₂.ls) (hfr : w₁.familyRef = w₂.familyRef)
    (hfm : w₁.famMember = w₂.famMember) (hcm : w₁.ctorMember = w₂.ctorMember)
    (hcrf : w₁.ctorRef = w₂.ctorRef)
    (hni : w₁.nindices = w₂.nindices) (hnp : w₁.nparams = w₂.nparams)
    (hk : w₁.kinds = w₂.kinds) (hcr : w₁.ctorResult = w₂.ctorResult) :
    ∀ (i : Nat) (params idxs : List (Expr Nat)) (x : Expr Nat),
      projAll w₁ i params idxs x = projAll w₂ i params idxs x := by
  intro i
  induction i with
  | zero => intro params idxs x; rfl
  | succ i ih =>
      intro params idxs x
      show projAll w₁ i params idxs x ++
            [canonField w₁ i params idxs
              (projAll w₁ i (params.map (lift 0 (w₁.nindices + 1)))
                (motIdx w₁.nindices) (.bvar 0)) x] =
          projAll w₂ i params idxs x ++
            [canonField w₂ i params idxs
              (projAll w₂ i (params.map (lift 0 (w₂.nindices + 1)))
                (motIdx w₂.nindices) (.bvar 0)) x]
      simp only [ih, hni, canonField_eq_of hr hls hfr hfm hcm hcrf hni hnp hk hcr]

/-- The projection fields of two witnesses that agree on every `projFields` input coincide. -/
theorem projFields_eq_of {w₁ w₂ : IotaWitness E} (hr : w₁.recRef = w₂.recRef)
    (hls : w₁.ls = w₂.ls) (hfr : w₁.familyRef = w₂.familyRef)
    (hfm : w₁.famMember = w₂.famMember) (hcm : w₁.ctorMember = w₂.ctorMember)
    (hcrf : w₁.ctorRef = w₂.ctorRef)
    (hni : w₁.nindices = w₂.nindices) (hnp : w₁.nparams = w₂.nparams)
    (hk : w₁.kinds = w₂.kinds) (hcr : w₁.ctorResult = w₂.ctorResult)
    (hnm : w₁.nMinors = w₂.nMinors) (hp : w₁.preMajor = w₂.preMajor) (x : Expr Nat) :
    projFields w₁ x = projFields w₂ x := by
  unfold projFields fieldCount
  rw [hcm, hnp, hnm, hp]
  exact projAll_eq_of hr hls hfr hfm hcm hcrf hni hnp hk hcr _ _ _ _

/-- Two fieldful witnesses of one recursor at one pre-major spine have the same projection fields
    at one major, hence the same contractum. -/
theorem iotaRhsOf_kfield_eq {w₁ w₂ : IotaWitness E} (h₁ : KFieldW w₁) (h₂ : KFieldW w₂)
    (hr : w₁.recRef = w₂.recRef) (hls : w₁.ls = w₂.ls) (hp : w₁.preMajor = w₂.preMajor)
    {x : Expr Nat} (hf₁ : w₁.fields = projFields w₁ x) (hf₂ : w₂.fields = projFields w₂ x) :
    iotaRhsOf w₁ = iotaRhsOf w₂ := by
  obtain ⟨hf1, hnm1, _, _⟩ := h₁
  obtain ⟨hf2, hnm2, _, _⟩ := h₂
  have hnm : w₁.nMinors = w₂.nMinors := hnm1.trans hnm2.symm
  have hfam : w₁.familyRef = w₂.familyRef := by
    have e1 := w₁.hrecIdx; have e2 := w₂.hrecIdx; omega
  have hci1 : w₁.ctorIdx = 0 := by have e := w₁.hidx; omega
  have hci2 : w₂.ctorIdx = 0 := by have e := w₂.hidx; omega
  have hcr : w₁.ctorRef = w₂.ctorRef := by
    have e1 := w₁.hctorIdx; have e2 := w₂.hctorIdx; omega
  have hlen : w₁.preMajor.length = w₂.preMajor.length := congrArg _ hp
  obtain ⟨_, hcm, _, _, hni, hnp, hci, hk⟩ := iotaWitness_env_of_same_refs hr hcr hlen
  have hfm : w₁.famMember = w₂.famMember := by
    have a := w₁.hfam; have b := w₂.hfam
    rw [hfam] at a
    exact Option.some.inj (a.symm.trans b)
  have hminor : w₁.minor = w₂.minor := by
    have e1 := w₁.hminor; have e2 := w₂.hminor
    rw [hnp, hci, hp] at e1
    exact Option.some.inj (e1.symm.trans e2)
  have hca : w₁.ctorAfterParams = w₂.ctorAfterParams := by
    have e1 := w₁.hctorAfter; have e2 := w₂.hctorAfter
    rw [hnp, hp, hls, hcm] at e1
    exact Option.some.inj (e1.symm.trans e2)
  have hfl : w₁.fields.length = w₂.fields.length := by
    have e1 := w₁.hnpar; have e2 := w₂.hnpar; rw [hcm, hnp] at e1; omega
  have hcr2 : w₁.ctorResult = w₂.ctorResult := by
    have e1 := w₁.hpeel; have e2 := w₂.hpeel
    rw [hnp, hfl, hcm] at e1
    exact congrArg Prod.snd (Option.some.inj (e1.symm.trans e2))
  have hfields : w₁.fields = w₂.fields := by
    rw [hf₁, hf₂]
    exact projFields_eq_of hr hls hfam hfm hcm hcr hni hnp hk hcr2 hnm hp x
  unfold iotaRhsOf
  rw [hminor, hr, hls, hp, hnp, hnm, hfields, hk, hca]

/-- **Exact determinism of the core (`WhDetCK`)** under `EnvWfT` — `#7673`'s `DetR`. -/
theorem detR_whStepCK (hW : EnvWfT E) : DetR (WhStepCK E) := by
  intro Γ a b c h₁ h₂
  induction h₁ generalizing c with
  | ctx s₁ =>
      exact whStepCK_ctx_det hW s₁ h₂
  | kStar hK hnc _ =>
      rename_i w x hidx
      generalize ha : recCall (.const w.recRef w.ls) w.preMajor x = a₀ at h₂
      induction h₂ with
      | ctx s₂ =>
          exact (whStepCtx_recCall_nonCtorMajor_aux hW (ha.symm ▸ s₂) rfl hnc).elim
      | kStar hK' hnc' _ =>
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          obtain ⟨hconst, hpre⟩ := foldApps_const_inj hf
          injection hconst with hr _
          exact iotaRhsOf_kfree_eq hK hK' hr hpre
      | kProj hK' hnc' hf' _ =>
          rename_i w' x' hidx'
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          obtain ⟨hconst, hpre⟩ := foldApps_const_inj hf
          injection hconst with hr _
          have e := fields_length_eq_of_same_lhs hK'.2.1 hK.2.1 hr.symm hpre.symm
          rw [hK.1] at e
          exact (hK'.1 (List.length_eq_zero.mp e)).elim
      | recMajor hm' hrec' hlen' hnK' hnP' hs' =>
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          obtain ⟨hconst, _⟩ := foldApps_const_inj hf
          injection hconst with hr _
          exact (hnK' ⟨w, hr, hK⟩).elim
      | appHead s₂ =>
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          subst hf
          exact (whStepCK_recPrefix_false_aux hW w.hrec w.hrecK s₂ rfl
            (by have h1 := w.hpre; have h2 := w.hnmin; omega)).elim
  | kProj hK hnc hf _ =>
      rename_i w x hidx
      generalize ha : recCall (.const w.recRef w.ls) w.preMajor x = a₀ at h₂
      induction h₂ with
      | ctx s₂ =>
          exact (whStepCtx_recCall_nonCtorMajor_aux hW (ha.symm ▸ s₂) rfl hnc).elim
      | kStar hK' hnc' _ =>
          rename_i w' x' hidx'
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          obtain ⟨hconst, hpre⟩ := foldApps_const_inj hf
          injection hconst with hr _
          have e := fields_length_eq_of_same_lhs hK.2.1 hK'.2.1 hr hpre
          rw [hK'.1] at e
          exact (hK.1 (List.length_eq_zero.mp e)).elim
      | kProj hK' hnc' hf' _ =>
          rename_i w' x' hidx'
          simp only [recCall_eq_app] at ha
          injection ha with hfa hx
          obtain ⟨hconst, hpre⟩ := foldApps_const_inj hfa
          injection hconst with hr hls
          subst hx
          exact iotaRhsOf_kfield_eq hK hK' hr hls hpre hf hf'
      | recMajor hm' hrec' hlen' hnK' hnP' hs' =>
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          obtain ⟨hconst, _⟩ := foldApps_const_inj hf
          injection hconst with hr _
          exact (hnP' ⟨w, hr, hK⟩).elim
      | appHead s₂ =>
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          subst hf
          exact (whStepCK_recPrefix_false_aux hW w.hrec w.hrecK s₂ rfl
            (by have h1 := w.hpre; have h2 := w.hnmin; omega)).elim
  | recMajor hm hrec hlen hnK hnP hsub ih =>
      rename_i r m ls pre x x'
      generalize ha : recCall (.const r ls) pre x = a₀ at h₂
      induction h₂ with
      | ctx s₂ =>
          exact (whStepCtx_recCall_innerCK_aux hW (ha.symm ▸ s₂) rfl hm hrec hlen hsub).elim
      | kStar hK' hnc' _ =>
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          obtain ⟨hconst, _⟩ := foldApps_const_inj hf
          injection hconst with hr _
          exact (hnK ⟨_, hr.symm, hK'⟩).elim
      | kProj hK' hnc' hf' _ =>
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          obtain ⟨hconst, _⟩ := foldApps_const_inj hf
          injection hconst with hr _
          exact (hnP ⟨_, hr.symm, hK'⟩).elim
      | recMajor hm' hrec' hlen' hnK' hnP' hs' =>
          simp only [recCall_eq_app] at ha
          injection ha with hf hx
          obtain ⟨hconst, hpre⟩ := foldApps_const_inj hf
          injection hconst with hr hls
          subst hls; subst hr; subst hpre; subst hx
          exact congrArg (recCall (.const r ls) pre ·) (ih hs')
      | appHead s₂ =>
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          subst hf
          exact (whStepCK_recPrefix_false_aux hW hm hrec s₂ rfl (by omega)).elim
  | appHead s₁ ih =>
      rename_i f f' a'
      generalize ha : Expr.app f a' = a₀ at h₂
      induction h₂ with
      | ctx s₂ =>
          exact (whStepCK_ctx_det hW (ha.symm ▸ s₂) (.appHead s₁)).symm
      | kStar hK' hnc' _ =>
          rename_i w x hidx
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          subst hf
          exact (whStepCK_recPrefix_false_aux hW w.hrec w.hrecK s₁ rfl
            (by have h1 := w.hpre; have h2 := w.hnmin; omega)).elim
      | kProj hK' hnc' hf' _ =>
          rename_i w x hidx
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          subst hf
          exact (whStepCK_recPrefix_false_aux hW w.hrec w.hrecK s₁ rfl
            (by have h1 := w.hpre; have h2 := w.hnmin; omega)).elim
      | recMajor hm' hrec' hlen' hnK' hnP' hs' =>
          simp only [recCall_eq_app] at ha
          injection ha with hf _
          subst hf
          exact (whStepCK_recPrefix_false_aux hW hm' hrec' s₁ rfl (by omega)).elim
      | appHead s₂ =>
          injection ha with hf ha2
          subst hf
          subst ha2
          exact congrArg (fun g => Expr.app g _) (ih s₂)

/-- The single-step diamond holds trivially for the deterministic core. -/
theorem diamondR_whStepCK (hW : EnvWfT E) : DiamondR (WhStepCK E) :=
  fun Γ _ _ _ h₁ h₂ => Or.inl (detR_whStepCK hW Γ h₁ h₂)

/-- **The law `LRSCore` transitivity needs (`#7673` §1), for the core**: two normal readbacks of one
    term coincide. -/
theorem normalUniqueR_whStepCK (hW : EnvWfT E) : NormalUniqueR (WhStepCK E) :=
  normalUniqueR_of_det (detR_whStepCK hW)

theorem length_projFields (w : IotaWitness E) (x : Expr Nat) :
    (projFields w x).length = fieldCount w := by
  suffices h : ∀ i ps ix x, (projAll w i ps ix x).length = i by
    exact h (fieldCount w) _ _ x
  intro i
  induction i with
  | zero => intro ps ix x; rfl
  | succ i ih =>
      intro ps ix x
      show (projAll w i ps ix x ++ [_]).length = i + 1
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [ih]

/-- The projection-canon witness at a major `x`, built from any witness `w` of the recursor at the
    same spine (only the fields change). -/
def kProjWitness (w : IotaWitness E) (x : Expr Nat) : IotaWitness E :=
  { w with
    fields := projFields w x
    hlen := by
      rw [length_projFields]
      unfold fieldCount
      have h := w.hlen; have h2 := w.hnpar; omega
    hnpar := by
      rw [length_projFields]; unfold fieldCount
      have h := w.hnpar; omega
    hpeel := by
      have h : w.nparams + (projFields w x).length = w.nparams + w.fields.length := by
        rw [length_projFields]; unfold fieldCount
        have e := w.hnpar; omega
      rw [h]; exact w.hpeel }

theorem kProjWitness_eq (w : IotaWitness E) (x : Expr Nat) :
    (kProjWitness w x).recRef = w.recRef ∧ (kProjWitness w x).ls = w.ls ∧
      (kProjWitness w x).preMajor = w.preMajor ∧ (kProjWitness w x).minor = w.minor ∧
      (kProjWitness w x).fields = projFields w x :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem kfieldW_kProjWitness {w : IotaWitness E} (hK : KFieldW w) (x : Expr Nat) :
    KFieldW (kProjWitness w x) := by
  obtain ⟨hf, hnM, hpb, hpk⟩ := hK
  refine ⟨?_, hnM, hpb, hpk⟩
  intro hem
  have hlen : (projFields w x).length = 0 := congrArg List.length hem
  rw [length_projFields] at hlen
  have e := w.hnpar
  unfold fieldCount at hlen
  have hf0 : w.fields.length = 0 := by omega
  exact hf (List.length_eq_zero.mp hf0)

/-- **The projection-canon K step exists** at every non-constructor major of a fieldful,
    non-recursive proposition-singleton recursor. -/
theorem whStepCK_kProj_of {Γ : LCtx} {w : IotaWitness E} (hK : KFieldW w) {x : Expr Nat}
    (hnc : ¬ IsCtorSpine E x)
    (hidx : redexIdx w = resultIdxAt w (w.preMajor.take w.nparams) (projFields w x)) :
    WhStepCK E Γ (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf (kProjWitness w x)) := by
  have hpf : projFields (kProjWitness w x) x = projFields w x :=
    projFields_eq_of (w₁ := kProjWitness w x) (w₂ := w)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl x
  have htk : (kProjWitness w x).preMajor.take (kProjWitness w x).nparams =
      w.preMajor.take w.nparams := rfl
  have hred : redexIdx (kProjWitness w x) = redexIdx w := rfl
  have hres : ∀ (ps fs : List (Expr Nat)),
      resultIdxAt (kProjWitness w x) ps fs = resultIdxAt w ps fs := fun _ _ => rfl
  refine .kProj (kfieldW_kProjWitness hK x) hnc ?_ ?_
  · show (kProjWitness w x).fields = projFields (kProjWitness w x) x
    rw [hpf]
    rfl
  · show redexIdx (kProjWitness w x) = resultIdxAt (kProjWitness w x)
        ((kProjWitness w x).preMajor.take (kProjWitness w x).nparams)
        (projFields (kProjWitness w x) x)
    rw [hred, hres, htk, hpf]
    exact hidx

/-! ### §2 — certified K steps on `#7665`'s `Step` at variable majors -/

/-- Two types of a variable convert: both are reached from its declared type. -/
def tyConvT_bvar_align {Γ : LCtx} {i : Nat} {A₀ Tm : Expr Nat}
    (h₁ : HasTyT E n Γ (.bvar i) A₀) (h₂ : HasTyT E n Γ (.bvar i) Tm) : TyConvT E n Γ A₀ Tm := by
  obtain ⟨A, hlkA, cvA⟩ := hasTyTInv_bvar h₁ rfl
  obtain ⟨B, hlkB, cvB⟩ := hasTyTInv_bvar h₂ rfl
  have e : A = B := Option.some.inj (hlkA.symm.trans hlkB)
  subst e
  exact TyConvT.trans _ _ _ _ cvA.symmT cvB

/-- The plain K certificate from an alignment AT THIS MAJOR only (irrelevance on the major at
    the head's domain, application congruence, ι). -/
def convT_iotaStarK_alignAt {Γ : LCtx} {w : IotaWitness E} {major Tm rhs T : Expr Nat}
    (al : ∀ {A₀ : Expr Nat}, HasTyT E n Γ major A₀ → TyConvT E n Γ A₀ Tm)
    (hmajor : HasTyT E n Γ major Tm) (hmk : HasTyT E n Γ (ctorMajor w) Tm)
    (hTm0 : HasTyT E n Γ Tm (.sort .zero))
    (ciota : ConvT E n Γ (iotaLhsOf w) rhs T)
    (hlhs : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) T) :
    ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor major) rhs T :=
  let inv := hasTyTInv_app hlhs (recCall_eq_app _ _ _)
  let chain : TyConvT E n Γ inv.1 Tm := al inv.2.2.2.1
  let cirr : ConvT E n Γ major (ctorMajor w) inv.1 :=
    convT_of_tyConv (.irr _ Tm _ _ hTm0 hmajor hmk) chain.symmT
  let capp : ConvT E n Γ (.app (foldApps (.const w.recRef w.ls) w.preMajor) major)
      (.app (foldApps (.const w.recRef w.ls) w.preMajor) (ctorMajor w))
      (instantiate0 major inv.2.1) :=
    .app _ _ _ major (ctorMajor w) inv.1 inv.2.1 (.refl _ _ _ inv.2.2.1) cirr
  let capp' : ConvT E n Γ (.app (foldApps (.const w.recRef w.ls) w.preMajor) major)
      (iotaLhsOf w) T :=
    (iotaLhsOf_eq_app w).symm ▸ convT_of_tyConv capp inv.2.2.2.2
  (recCall_eq_app _ _ _).symm ▸ ConvT.trans _ _ _ _ _ capp' ciota

/-- **The plain K certificate at a variable major — unconditional** (legacy ι arm). -/
def convT_iotaStarK_bvar {Γ : LCtx} {w : IotaWitness E} {i : Nat} {Tm T : Expr Nat}
    (hmajor : HasTyT E n Γ (.bvar i) Tm) (hmk : HasTyT E n Γ (ctorMajor w) Tm)
    (hTm0 : HasTyT E n Γ Tm (.sort .zero))
    (hlι : HasTyT E n Γ (iotaLhsOf w) T) (hrhs : HasTyT E n Γ (iotaRhsOf w) T)
    (hlhs : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor (.bvar i)) T) :
    ConvT E n Γ (recCall (.const w.recRef w.ls) w.preMajor (.bvar i)) (iotaRhsOf w) T :=
  convT_iotaStarK_alignAt (fun h => tyConvT_bvar_align h hmajor) hmajor hmk hTm0
    (.iota _ _ _ _ (.of w) hlι hrhs) hlhs

/-- The plain K node with its unconditional certificate at a variable major (any fields). -/
def cstepK_iotaStarK_bvar {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type} {Γ : LCtx}
    (w : IotaWitness E) (i : Nat) (Tm T : Expr Nat) (rl : Level) (afs : Prop)
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n Γ (.bvar i) Tm) (hmk : HasTyT E n Γ (ctorMajor w) Tm)
    (hTm0 : HasTyT E n Γ Tm (.sort .zero))
    (hlι : HasTyT E n Γ (iotaLhsOf w) T)
    (hlhs : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor (.bvar i)) T)
    (hrhs : HasTyT E n Γ (iotaRhsOf w) T) :
    CStepK E n PEq Γ (recCall (.const w.recRef w.ls) w.preMajor (.bvar i)) (iotaRhsOf w) T :=
  ⟨.iotaStarK Γ w (.bvar i) Tm (iotaRhsOf w) T rl afs hrl hsel hfam hmajor hmk hTm0 (.ofU w) hlι
      hlhs hrhs,
    .iotaStarK (convT_iotaStarK_bvar hmajor hmk hTm0 hlι hrhs hlhs)⟩

/-- **A certified K step of `#7665`'s `Step` family** at a variable major. -/
def stepK_bvar {Γ : LCtx}
    (w : IotaWitness E) (i : Nat) (Tm T : Expr Nat) (rl : Level) (afs : Prop)
    (hrl : piBody w.famMember.mtype = .sort rl)
    (hsel : EliminationSelection rl w.nMinors afs .anySort)
    (hfam : ∃ lsF, (appsSpine Tm).1 = .const w.familyRef lsF)
    (hmajor : HasTyT E n Γ (.bvar i) Tm) (hmk : HasTyT E n Γ (ctorMajor w) Tm)
    (hTm0 : HasTyT E n Γ Tm (.sort .zero))
    (hlι : HasTyT E n Γ (iotaLhsOf w) T)
    (hlhs : HasTyT E n Γ (recCall (.const w.recRef w.ls) w.preMajor (.bvar i)) T)
    (hrhs : HasTyT E n Γ (iotaRhsOf w) T) :
    NativeSpineHead.Step E n Γ (recCall (.const w.recRef w.ls) w.preMajor (.bvar i))
      (iotaRhsOf w) T :=
  .kRoot (cstepK_iotaStarK_bvar w i Tm T rl afs hrl hsel hfam hmajor hmk hTm0 hlι hlhs hrhs)
    trivial

/-- A variable is never a constructor-headed spine. -/
theorem not_isCtorSpine_bvar {i : Nat} : ¬ IsCtorSpine E (.bvar i) :=
  fun ⟨c, us, ys, _, heq, _, _⟩ => foldApps_const_ne_bvar ys i heq.symm

/-- A field-free certified K step at a variable major has a core shadow, when the redex's
    index arguments agree with the canon constructor's result indices. -/
theorem whStepCK_of_kfree_bvar {Γ : LCtx} {w : IotaWitness E} (hK : KFreeW w) (i : Nat)
    (hidx : redexIdx w = resultIdxAt w (w.preMajor.take w.nparams) []) :
    WhStepCK E Γ (recCall (.const w.recRef w.ls) w.preMajor (.bvar i)) (iotaRhsOf w) :=
  .kStar hK not_isCtorSpine_bvar hidx

/-! ### §3 — positive controls and teeth -/

/-- The field-free K point is a certified step of `#7665`'s family (`trueEnvU`, `h : True`). -/
def stepK_kRec_var (n : Nat) :
    NativeSpineHead.Step trueEnvU n kVarCtx (kRec (.bvar 0)) (.sort .zero) (.sort (.succ .zero)) :=
  stepK_bvar wTrueRecU 0 (.const 0 []) (.sort (.succ .zero)) .zero True
    rfl (.singletonProp (fun _ => rfl) rfl True.intro) ⟨[], rfl⟩
    (kVar_ty n) trueEnvUtt_ty trueEnvUF_ty
    trueEnvUL_tyS1
    (.conv _ _ _ _ (.succ (.succ .zero))
      (.app _ _ _ _ _ kRecHead_ty (kVar_ty n))
      (.beta _ _ _ _ _ .zero trueEnvUF_ty (.sort _ (.succ .zero)) (kVar_ty n)))
    (.sort _ .zero)

/-- The fieldful K point is a certified step of `#7665`'s family (`andEnvU`, canon `intro a b x y`). -/
def stepK_mixAnd :
    NativeSpineHead.Step andEnvU 0 mixAndCtx mixAndRedex mixAndRhs (.app mixAndMot mixAndMkApp) :=
  stepK_bvar mixAndW 0 mixAndFamApp (.app mixAndMot mixAndMkApp) .zero True
    rfl (.singletonProp (fun _ => rfl) rfl True.intro) ⟨[], rfl⟩
    mixTyH mixAndMkTy mixAndFamTy
    mixAndLhsTy
    (.conv _ _ _ _ (.succ (.succ .zero))
      (.app _ _ _ _ _ mixAndRecTy mixTyH)
      (.app _ _ _ _ _ _ _ (.refl _ _ _ mixAndMotTy) mixAndIrr))
    mixAndRhsTy

/-- The core takes the field-free K step at every non-constructor proof. -/
theorem whStepCK_kRec {Γ : LCtx} {x : Expr Nat} (hnc : ¬ IsCtorSpine trueEnvU x) :
    WhStepCK trueEnvU Γ (kRec x) (.sort .zero) :=
  .kStar (w := wTrueRecU) ⟨rfl, rfl, rfl⟩ hnc rfl

theorem lrSCore_whStepCK_kRec {Γ : LCtx} {x : Expr Nat} (hnc : ¬ IsCtorSpine trueEnvU x)
    (c : CptI) (hc : ApproxI (ctxEnvI Γ) (.sort .zero) c) :
    LRSCore (WhStepCK trueEnvU) trueEnvU n Γ (.sort .zero) (kRec x) (.sort (.succ .zero)) c := by
  rcases approxI_sort_inv hc with rfl | rfl
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    exact ⟨⟨_, .refl _⟩, _, _, .refl _, redR_single (whStepCK_kRec hnc)⟩

theorem lrSCore_whStepCK_kRec_symm {Γ : LCtx} {x : Expr Nat}
    (hnc : ¬ IsCtorSpine trueEnvU x) (c : CptI) (hc : ApproxI (ctxEnvI Γ) (kRec x) c) :
    LRSCore (WhStepCK trueEnvU) trueEnvU n Γ (kRec x) (.sort .zero) (.sort (.succ .zero)) c := by
  have hc' : ApproxI (ctxEnvI Γ)
      (foldApps (.const 2 [.succ (.succ .zero)]) [kMot, .sort .zero, x]) c := hc
  rcases approxI_foldApps_const_inv hc' with rfl | ⟨us, rfl, _⟩
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    refine Or.inl ⟨⟨_, .refl _⟩, Or.inr ⟨fun m hm hind => ?_, .sort .zero, .sort .zero,
      redR_single (whStepCK_kRec hnc), .refl _, ⟨.refl _ _⟩⟩⟩
    have e' : trueRecMemberU = m := Option.some.inj hm
    subst e'
    exact MemberClass.noConfusion hind

/-- The Π-side analogue: `True.rec.{2} (λ_. Sort 1) (Sort 0 → Sort 0)`. -/
def kRecPiHead : Expr Nat := .app (.app (.const 2 [.succ (.succ .zero)]) kMot) mixPi

def kRecPi (x : Expr Nat) : Expr Nat := .app kRecPiHead x

/-- The ι witness of the Π-side analogue (minor `Sort 0 → Sort 0`). -/
def wTrueRecPi : IotaWitness trueEnvU :=
  { wTrueRecU with
    preMajor := [kMot, mixPi]
    minor := mixPi
    hpre := rfl
    hminor := rfl }

theorem iotaLhsOf_wTrueRecPi : iotaLhsOf wTrueRecPi = kRecPi (.const 1 []) := rfl

theorem iotaRhsOf_wTrueRecPi : iotaRhsOf wTrueRecPi = mixPi := rfl

theorem kfreeW_wTrueRecPi : KFreeW wTrueRecPi := ⟨rfl, rfl, rfl⟩

/-- `Sort 0 → Sort 0 ≡ True.rec.{2} (λ_. Sort 1) (Sort 0 → Sort 0) x : Sort 1` for every proof `x`. -/
def kRecPi_conv {Γ : LCtx} {x : Expr Nat} (hx : HasTyT trueEnvU n Γ x (.const 0 [])) :
    ConvT trueEnvU n Γ mixPi (kRecPi x) (.sort (.succ .zero)) := by
  have mixPiS1 : HasTyT trueEnvU n Γ mixPi (.sort (.succ .zero)) :=
    .conv _ _ _ _ _
      (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))
      (ConvT.sorts _ _ _ (fun _ => rfl))
  have mixPiAt : HasTyT trueEnvU n Γ mixPi (.app kMot (.const 1 [])) :=
    .conv _ _ _ _ (.succ (.succ .zero)) mixPiS1 (.symm _ _ _ _ trueEnvU_betaK)
  have kRecPiHead_ty : HasTyT trueEnvU n Γ kRecPiHead
      (.pi (.const 0 []) (.app kMot (.bvar 0))) :=
    .app _ _ _ _ _
      (.app _ _ _ _ _
        (.const _ 2 [.succ (.succ .zero)] trueRecMemberU rfl rfl rfl)
        trueEnvUM_ty)
      mixPiAt
  have ciPi : ConvT trueEnvU n Γ (kRecPi (.const 1 [])) mixPi (.sort (.succ .zero)) :=
    .iota _ _ _ _ (.of wTrueRecPi)
      (.conv _ _ _ _ (.succ (.succ .zero))
        (.app _ _ _ _ _ kRecPiHead_ty trueEnvUtt_ty)
        trueEnvU_betaK)
      mixPiS1
  exact .trans _ _ _ _ _ (.symm _ _ _ _ ciPi)
    (.tyConv _ _ _ _ _ _
      (.app _ _ _ _ _ _ _ (.refl _ _ _ kRecPiHead_ty)
        (.irr _ _ _ _ trueEnvUF_ty trueEnvUtt_ty hx))
      trueEnvU_betaK)

theorem whStepCK_kRecPi {Γ : LCtx} {x : Expr Nat} (hnc : ¬ IsCtorSpine trueEnvU x) :
    WhStepCK trueEnvU Γ (kRecPi x) mixPi :=
  .kStar (w := wTrueRecPi) kfreeW_wTrueRecPi hnc rfl

/-- **Π-side analogue, positive** at every compact of `Sort 0 → Sort 0` (incl. `pi ⊥ []`). -/
theorem lrSCore_whStepCK_kRecPi {Γ : LCtx} (hΓ : CtxWfT trueEnvU n Γ) {x : Expr Nat}
    (hnc : ¬ IsCtorSpine trueEnvU x) (u : Level) (c : CptI) (hc : ApproxI (ctxEnvI Γ) mixPi c) :
    LRSCore (WhStepCK trueEnvU) trueEnvU n Γ mixPi (kRecPi x) (.sort u) c := by
  rcases approxI_pi_inv hc with rfl | ⟨a, f, rfl, hA, hB⟩
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    refine ⟨⟨_, .refl _⟩, .sort .zero, .sort .zero, .sort .zero, .sort .zero, .refl _,
      redR_single (whStepCK_kRecPi hnc),
      ⟨.assumption _ _ _ hΓ (.sort _ .zero)⟩,
      ⟨.refl _ _⟩, ⟨.refl _ _⟩, ⟨.succ .zero, ?_⟩, fun s hs _ _ _ _ _ _ => ⟨.succ .zero, ?_⟩⟩
    · rcases approxI_sort_inv hA with rfl | rfl
      · exact lrSCore_bot _ _ _ _
      · rw [LRSCore.eq_def]
        exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩
    · show LRSCore (WhStepCK trueEnvU) trueEnvU n Γ (.sort .zero) (.sort .zero)
        (.sort (.succ .zero)) s.2
      rcases approxI_sort_inv (hB s hs) with h0 | h0
      · rw [h0]; exact lrSCore_bot _ _ _ _
      · rw [h0, LRSCore.eq_def]
        exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩

theorem lrSCore_whStepCK_kRecPi_symm {Γ : LCtx} {x : Expr Nat}
    (hnc : ¬ IsCtorSpine trueEnvU x) (u : Level)
    (c : CptI) (hc : ApproxI (ctxEnvI Γ) (kRecPi x) c) :
    LRSCore (WhStepCK trueEnvU) trueEnvU n Γ (kRecPi x) mixPi (.sort u) c := by
  have hc' : ApproxI (ctxEnvI Γ)
      (foldApps (.const 2 [.succ (.succ .zero)]) [kMot, mixPi, x]) c := hc
  rcases approxI_foldApps_const_inv hc' with rfl | ⟨us, rfl, _⟩
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    refine Or.inl ⟨⟨_, .refl _⟩, Or.inr ⟨fun m hm hind => ?_, mixPi, mixPi,
      redR_single (whStepCK_kRecPi hnc), .refl _, ⟨.refl _ _⟩⟩⟩
    have e' : trueRecMemberU = m := Option.some.inj hm
    subst e'
    exact MemberClass.noConfusion hind

/-- **Π-side analogue, tooth**: the K-blind `WhStepCtx` misses it at the `piRow` probe. -/
theorem not_lrSCore_whStepCtx_kRecPi_piBotNil (u : Level) :
    ¬ LRSCore (WhStepCtx trueEnvU) trueEnvU n kVarCtx mixPi (kRecPi (.bvar 0)) (.sort u)
      (.pi .bot []) := by
  intro h
  rw [LRSCore.eq_def] at h
  obtain ⟨_, A₁, B₁, A₂, B₂, h1, h2, _⟩ := h
  have e2 := whRedCtx_constSpine_eq (r := 2) (ls := [.succ (.succ .zero)])
    (m := trueRecMemberU) rfl rfl
    (xs := [kMot, mixPi, .bvar 0]) (by
      intro x hx c us ys heq
      have hx' : x = kMot ∨ x = mixPi ∨ x = .bvar 0 := by
        simpa using hx
      rcases hx' with rfl | rfl | rfl
      · exact F8EtaK.foldApps_const_ne_lam_any heq.symm
      · exact foldApps_const_ne_pi _ _ _ _ _ heq.symm
      · exact foldApps_const_ne_bvar _ _ heq.symm)
    (whRedCtx_of_redR h2)
  exact foldApps_const_ne_pi _ _ _ _ _ e2.symm

theorem not_fundamentalLRST_whStepCtx_trueEnvU_piBotNil (n : Nat) :
    ¬ FundamentalLRST (WhStepCtx trueEnvU) trueEnvU n := by
  intro F
  have h := F (kVarCtx_wf n)
    (.conv _ _ _ _ _
      (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))
      (ConvT.sorts _ _ _ (fun _ => rfl)))
    (.of _ _ _ _ (kRecPi_conv (kVar_ty n))) (.pi .bot [])
    (approxI_pi_bot_nil _ _ _)
  exact not_lrSCore_whStepCtx_kRecPi_piBotNil _ h

/-- No `andEnvU` witness of `And.rec` is field-free. -/
theorem not_kfreeW_andEnvU (w : IotaWitness andEnvU) (hr : w.recRef = 2) : ¬ KFreeW w := by
  rintro ⟨hf, hnM, -⟩
  have hfr : w.familyRef = 0 := by have h := w.hrecIdx; omega
  have hci : w.ctorIdx = 0 := by have h := w.hidx; omega
  have hcr : w.ctorRef = 1 := by have h := w.hctorIdx; omega
  have hcm : w.ctorMember = andIntroMember := by
    have a := w.hctor; rw [hcr] at a; exact (Option.some.inj a).symm
  have hpar : w.nparams + w.fields.length = 4 := by
    have h := w.hnpar; rw [hcm] at h; exact h
  have hfl : w.fields.length = 0 := congrArg List.length hf
  have hfm : w.famMember = andFamMember := by
    have a := w.hfam; rw [hfr] at a; exact (Option.some.inj a).symm
  have hn2 : w.nparams + w.nindices = 2 := by
    have h := w.hnidx; rw [hfm] at h; exact h
  omega

/-- A bound variable with no stored value takes no `WhStepCK` step. -/
theorem whStepCK_bvar_none_false {Γ : LCtx} {i : Nat} {e : Expr Nat}
    (h0 : lookupValue Γ i = none) {a : Expr Nat} (h : WhStepCK E Γ a e) :
    a = .bvar i → False := by
  induction h with
  | ctx hs => intro heq; subst heq; exact whStepCtx_bvar_none_false h0 hs
  | kStar _ _ _ =>
      intro heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | kProj _ _ _ _ =>
      intro heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | recMajor _ _ _ _ _ _ =>
      intro heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | appHead _ _ => intro heq; exact Expr.noConfusion heq

/-! #### the fieldful point in the core (projection canon) -/

theorem kfieldW_mixAndW : KFieldW mixAndW :=
  ⟨fun h => List.cons_ne_nil _ _ h, rfl, rfl, rfl⟩

/-- **The core reaches the fieldful point deterministically**: `mixAnd ↝ (λ x y. Sort 0 → Sort 0)
    (pr₁ h) (pr₂ h) ↝ ↝ Sort 0 → Sort 0`. -/
theorem redR_whStepCK_mixAndRedex :
    RedR (WhStepCK andEnvU) mixAndCtx mixAndRedex mixPi := by
  refine .step (whStepCK_kProj_of kfieldW_mixAndW not_isCtorSpine_bvar rfl)
    (.step (.ctx (.appHead (.beta _ _ _)))
      (.step (.ctx (.beta _ _ _)) (.refl _)))

/-- The fieldful K point at every compact of `Sort 0 → Sort 0` (incl. `pi ⊥ []`), with the core. -/
theorem lrSCore_whStepCK_mixAnd (u : Level) (c : CptI) (hc : ApproxI (ctxEnvI mixAndCtx) mixPi c) :
    LRSCore (WhStepCK andEnvU) andEnvU 0 mixAndCtx mixPi mixAndRedex (.sort u) c := by
  rcases approxI_pi_inv hc with rfl | ⟨a, f, rfl, hA, hB⟩
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    refine ⟨⟨_, .refl _⟩, .sort .zero, .sort .zero, .sort .zero, .sort .zero, .refl _,
      redR_whStepCK_mixAndRedex,
      ⟨.assumption _ _ _ Rcic.Domain.Model.PiInversion.mixAndCtx_wf (.sort _ .zero)⟩,
      ⟨.refl _ _⟩, ⟨.refl _ _⟩, ⟨.succ .zero, ?_⟩, fun s hs _ _ _ _ _ _ => ⟨.succ .zero, ?_⟩⟩
    · rcases approxI_sort_inv hA with rfl | rfl
      · exact lrSCore_bot _ _ _ _
      · rw [LRSCore.eq_def]
        exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩
    · show LRSCore (WhStepCK andEnvU) andEnvU 0 mixAndCtx (.sort .zero) (.sort .zero)
        (.sort (.succ .zero)) s.2
      rcases approxI_sort_inv (hB s hs) with h0 | h0
      · rw [h0]; exact lrSCore_bot _ _ _ _
      · rw [h0, LRSCore.eq_def]
        exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩

theorem lrSCore_whStepCK_mixAnd_symm (u : Level) (c : CptI)
    (hc : ApproxI (ctxEnvI mixAndCtx) mixAndRedex c) :
    LRSCore (WhStepCK andEnvU) andEnvU 0 mixAndCtx mixAndRedex mixPi (.sort u) c := by
  have hc' : ApproxI (ctxEnvI mixAndCtx)
      (foldApps (.const 2 [.succ (.succ .zero)])
        [.bvar 4, .bvar 3, mixAndMot, mixAndMin, .bvar 0]) c := hc
  rcases approxI_foldApps_const_inv hc' with rfl | ⟨us, rfl, _⟩
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    refine Or.inl ⟨⟨_, .refl _⟩, Or.inr ⟨fun m hm hind => ?_, mixPi, mixPi,
      redR_whStepCK_mixAndRedex, .refl _, ⟨.refl _ _⟩⟩⟩
    have e' : andRecMemberU = m := Option.some.inj hm
    subst e'
    exact MemberClass.noConfusion hind

/-! ### §4 — the fieldful existential step: no determinism, joinability at the control -/

/-- A second canon of the same proposition: `intro a b ((λ z : a. z) x) y`. -/
def mixAndCanon2 : Expr Nat :=
  foldApps (.const 1 []) [.bvar 4, .bvar 3, .app (.lam (.bvar 4) (.bvar 0)) (.bvar 2), .bvar 1]

/-- The ι witness at the second canon. -/
def mixAndW2 : IotaWitness andEnvU :=
  { mixAndW with
    fields := [.app (.lam (.bvar 4) (.bvar 0)) (.bvar 2), .bvar 1]
    hlen := rfl
    hnpar := rfl }

theorem ctorMajor_mixAndW2 : ctorMajor mixAndW2 = mixAndCanon2 := rfl

/-- `(λ z : a. z) x : a` — the third constructor field of `mixAndCanon2`. -/
def mixAndCanon2Field3 : HasTyT andEnvU 0 mixAndCtx
    (.app (.lam (.bvar 4) (.bvar 0)) (.bvar 2)) (.bvar 4) :=
  .app _ _ _ _ _
    (.lam _ _ .zero _ _ mixTyA (.bvar _ 0 _ rfl))
    mixTyX

/-- `intro a b ((λ z : a. z) x) y : And a b` — `mixAndCanon2`'s typing. -/
def mixAndCanon2Ty : HasTyT andEnvU 0 mixAndCtx mixAndCanon2 mixAndFamApp :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.const _ 1 [] andIntroMember rfl rfl rfl) mixTyA)
        mixTyB)
      mixAndCanon2Field3)
    mixTyY

/-- Two fieldful K choices at `mixAnd` with distinct contracta. -/
theorem whStepK_mixAndRedex_fork :
    WhStepK andEnvU 0 mixAndCtx mixAndRedex mixAndRhs ∧
      WhStepK andEnvU 0 mixAndCtx mixAndRedex (iotaRhsOf mixAndW2) ∧
      mixAndRhs ≠ iotaRhsOf mixAndW2 := by
  refine ⟨.pmajor (.ofU mixAndW) ⟨mixAndFamTy⟩ ⟨mixAndMkTy⟩ ⟨mixTyH⟩,
    .pmajor (.ofU mixAndW2) ⟨mixAndFamTy⟩ ⟨mixAndCanon2Ty⟩ ⟨mixTyH⟩,
    ?_⟩
  intro h
  have h' : Expr.app (Expr.app mixAndMin (.bvar 2)) (.bvar 1) =
      Expr.app (Expr.app mixAndMin (.app (.lam (.bvar 4) (.bvar 0)) (.bvar 2))) (.bvar 1) := h
  injection h' with h1 _
  injection h1 with _ h2
  exact Expr.noConfusion h2

theorem not_detR_whStepK_andEnvU : ¬ DetR (WhStepK andEnvU 0) := by
  intro h
  obtain ⟨h1, h2, hne⟩ := whStepK_mixAndRedex_fork
  exact hne (h mixAndCtx h1 h2)

/-- A canon differing in the SECOND field: `intro a b x ((λ z : b. z) y)`. -/
def mixAndCanon3 : Expr Nat :=
  foldApps (.const 1 []) [.bvar 4, .bvar 3, .bvar 2, .app (.lam (.bvar 3) (.bvar 0)) (.bvar 1)]

def mixAndW3 : IotaWitness andEnvU :=
  { mixAndW with
    fields := [.bvar 2, .app (.lam (.bvar 3) (.bvar 0)) (.bvar 1)]
    hlen := rfl
    hnpar := rfl }

theorem ctorMajor_mixAndW3 : ctorMajor mixAndW3 = mixAndCanon3 := rfl

theorem iotaRhsOf_mixAndW3 :
    iotaRhsOf mixAndW3 = .app (.app mixAndMin (.bvar 2)) (.app (.lam (.bvar 3) (.bvar 0)) (.bvar 1)) :=
  rfl

/-- `(λ z : b. z) y : b` — the fourth constructor field of `mixAndCanon3`. -/
def mixAndCanon3Field4 : HasTyT andEnvU 0 mixAndCtx
    (.app (.lam (.bvar 3) (.bvar 0)) (.bvar 1)) (.bvar 3) :=
  .app _ _ _ _ _
    (.lam _ _ .zero _ _ mixTyB (.bvar _ 0 _ rfl))
    mixTyY

/-- `intro a b x ((λ z : b. z) y) : And a b` — `mixAndCanon3`'s typing. -/
def mixAndCanon3Ty : HasTyT andEnvU 0 mixAndCtx mixAndCanon3 mixAndFamApp :=
  .app _ _ _ _ _
    (.app _ _ _ _ _
      (.app _ _ _ _ _
        (.app _ _ _ _ _
          (.const _ 1 [] andIntroMember rfl rfl rfl) mixTyA)
        mixTyB)
      mixTyX)
    mixAndCanon3Field4

/-- A λ-headed term takes no `WhStepK` step (auxiliary induction). -/
theorem whStepK_lam_false_aux {n : Nat} {Γ : LCtx} {a e : Expr Nat}
    (h : WhStepK E n Γ a e) : ∀ {A b : Expr Nat}, a = .lam A b → False := by
  induction h with
  | ctx hs =>
      intro A b heq; subst heq
      cases hs with
      | iota hI =>
          obtain ⟨_, _, _, _, _, hlhs, _, _⟩ := derivedIotaU_recHead hI
          exact F8EtaK.foldApps_const_ne_lam_any hlhs.symm
  | pmajor _ _ _ _ =>
      intro A b heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | recArg _ _ _ _ =>
      intro A b heq
      rw [foldApps_snoc] at heq
      exact Expr.noConfusion heq
  | appHead _ _ => intro A b heq; exact Expr.noConfusion heq

/-- An `app (lam ..) x₀` source takes only the `ctx`-β step under `WhStepK`. -/
theorem whStepK_lamApp_eq_aux {n : Nat} {Γ : LCtx} {a e : Expr Nat}
    (h : WhStepK E n Γ a e) :
    ∀ {A b x : Expr Nat}, a = .app (.lam A b) x → e = instantiate0 x b := by
  induction h with
  | ctx hs =>
      intro A b x ha; subst ha
      cases hs with
      | beta => rfl
      | iota hI =>
          obtain ⟨r, ls, pre, major, _, hlhs, _, _⟩ := derivedIotaU_recHead hI
          rw [foldApps_snoc] at hlhs
          injection hlhs with hf _
          exact (F8EtaK.foldApps_const_ne_lam_any hf.symm).elim
      | appHead s =>
          cases s with
          | iota hI =>
              obtain ⟨r, ls, pre, major, _, hlhs, _, _⟩ := derivedIotaU_recHead hI
              exact (F8EtaK.foldApps_const_ne_lam_any hlhs.symm).elim
  | pmajor _ _ _ _ =>
      intro A b x ha
      rw [recCall_eq_app] at ha
      injection ha with hf _
      exact (F8EtaK.foldApps_const_ne_lam_any hf).elim
  | recArg _ _ _ _ =>
      intro A b x ha
      rw [foldApps_snoc] at ha
      injection ha with hf _
      exact (F8EtaK.foldApps_const_ne_lam_any hf).elim
  | appHead hh _ =>
      intro A b x ha
      injection ha with hf _
      subst hf
      exact (whStepK_lam_false_aux hh rfl).elim

/-- The contractum `mixAndMin x₀ y₀` has exactly one `WhStepK` step, which keeps `y₀`. -/
theorem whStepK_mixAndMin_app_eq {x₀ y₀ e : Expr Nat}
    (h : WhStepK andEnvU 0 mixAndCtx (.app (.app mixAndMin x₀) y₀) e) :
    e = .app (.lam (.bvar 3) mixPi) y₀ := by
  generalize ha : Expr.app (Expr.app mixAndMin x₀) y₀ = a₀ at h
  induction h with
  | ctx hs =>
      subst ha
      cases hs with
      | iota hI =>
          obtain ⟨r, ls, pre, major, _, hlhs, _, _⟩ := derivedIotaU_recHead hI
          rw [foldApps_snoc] at hlhs
          injection hlhs with hf _
          exact (lamApp_ne_foldApps_const _ hf).elim
      | appHead s =>
          cases s with
          | beta => rfl
          | iota hI =>
              obtain ⟨r, ls, pre, major, _, hlhs, _, _⟩ := derivedIotaU_recHead hI
              rw [foldApps_snoc] at hlhs
              injection hlhs with hf _
              exact (F8EtaK.foldApps_const_ne_lam_any
                (show foldApps (.const r ls) pre =
                  .lam (.bvar 4) (.lam (.bvar 4) mixPi) from hf.symm)).elim
          | appHead s' =>
              cases s' with
              | iota hI =>
                  obtain ⟨r, ls, pre, major, _, hlhs, _, _⟩ := derivedIotaU_recHead hI
                  exact (F8EtaK.foldApps_const_ne_lam_any
                    (show foldApps (.const r ls) (pre ++ [major]) =
                      .lam (.bvar 4) (.lam (.bvar 4) mixPi) from hlhs.symm)).elim
  | pmajor _ _ _ _ =>
      rw [recCall_eq_app] at ha
      injection ha with hf _
      exact (lamApp_ne_foldApps_const _ hf).elim
  | recArg _ _ _ _ =>
      rw [foldApps_snoc] at ha
      injection ha with hf _
      exact (lamApp_ne_foldApps_const _ hf).elim
  | appHead hh _ =>
      injection ha with hf ha'
      subst hf; subst ha'
      have hf' := whStepK_lamApp_eq_aux hh rfl
      rw [hf']
      rfl

/-- **The single-step diamond fails for the fieldful existential step** (`#7673`'s `DiamondR`):
    two fieldful K choices at `mixAnd` differing in the second field have one-step reducts
    `(λ _. Sort 0 → Sort 0) y` and `(λ _. Sort 0 → Sort 0) ((λ z. z) y)` with no common
    one-step reduct (they meet only after a second step). -/
theorem not_diamondR_whStepK_andEnvU : ¬ DiamondR (WhStepK andEnvU 0) := by
  intro hd
  have h₁ : WhStepK andEnvU 0 mixAndCtx mixAndRedex mixAndRhs :=
    .pmajor (.ofU mixAndW) ⟨mixAndFamTy⟩ ⟨mixAndMkTy⟩ ⟨mixTyH⟩
  have h₂ : WhStepK andEnvU 0 mixAndCtx mixAndRedex (iotaRhsOf mixAndW3) :=
    .pmajor (.ofU mixAndW3) ⟨mixAndFamTy⟩ ⟨mixAndCanon3Ty⟩ ⟨mixTyH⟩
  rcases hd mixAndCtx h₁ h₂ with hbc | ⟨d, hd₁, hd₂⟩
  · have h' : Expr.app (Expr.app mixAndMin (.bvar 2)) (.bvar 1) =
        Expr.app (Expr.app mixAndMin (.bvar 2))
          (.app (.lam (.bvar 3) (.bvar 0)) (.bvar 1)) := hbc
    injection h' with _ hg
    exact Expr.noConfusion hg
  · rw [iotaRhsOf_mixAndW3] at hd₂
    have heq₁ := whStepK_mixAndMin_app_eq hd₁
    have heq₂ := whStepK_mixAndMin_app_eq hd₂
    rw [heq₁] at heq₂
    injection heq₂ with _ hb
    exact Expr.noConfusion hb

/-- **Every fieldful K choice at `mixAnd` joins at `Sort 0 → Sort 0`** (legacy witnesses). -/
theorem fieldfulK_join_mixAnd (w : IotaWitness andEnvU) (hr : w.recRef = 2)
    (hp : w.preMajor = mixAndSpine) :
    RedR (WhStepK andEnvU 0) mixAndCtx (iotaRhsOf w) mixPi := by
  have hrm : w.recMember = andRecMemberU := by
    have a := w.hrec; rw [hr] at a; exact (Option.some.inj a).symm
  have hfr : w.familyRef = 0 := by
    have h := w.hrecIdx; have h2 := w.hidx; omega
  have hnM : w.nMinors = 1 := by
    have h := w.hrecIdx; have h2 := w.hidx; omega
  have hci : w.ctorIdx = 0 := by have h := w.hidx; omega
  have hcr : w.ctorRef = 1 := by have h := w.hctorIdx; omega
  have hcm : w.ctorMember = andIntroMember := by
    have a := w.hctor; rw [hcr] at a; exact (Option.some.inj a).symm
  have hfm : w.famMember = andFamMember := by
    have a := w.hfam; rw [hfr] at a; exact (Option.some.inj a).symm
  have hcnt5 : w.nparams + 1 + w.nMinors + w.nindices + 1 = 5 := by
    have h := w.hnmin; rw [hrm] at h; exact h
  have hn2 : w.nparams + w.nindices = 2 := by
    have h := w.hnidx; rw [hfm] at h; exact h
  have hpeel := w.hpeelRec
  rw [hrm, hcnt5] at hpeel
  have hpeel5 : peelPis 5 andRecMemberU.mtype =
      some ([.sort .zero, .sort .zero, andMotTy, andMinorTy,
        andApp (.bvar 3) (.bvar 2)], .app (.bvar 2) (.bvar 0)) := rfl
  rw [hpeel5] at hpeel
  have hrb : w.recBody = .app (.bvar 2) (.bvar 0) :=
    (Prod.mk.inj (Option.some.inj hpeel)).2.symm
  have hni : w.nindices = 0 := by
    have hb := w.hrecBody
    rw [hrb, hnM] at hb
    rcases h0 : w.nindices with _ | ni
    · rfl
    · exfalso
      rw [h0, foldApps_snoc] at hb
      injection hb with hf _
      have hne : ((List.range (ni + 1)).reverse.map
          (fun i => (.bvar (i + 1) : Expr Nat))) ≠ [] := by
        intro hnil
        have hl := congrArg List.length hnil
        rw [List.length_map, List.length_reverse, List.length_range, List.length_nil] at hl
        omega
      obtain ⟨pre, z, hpz⟩ := (list_eq_nil_or_snoc
        ((List.range (ni + 1)).reverse.map
          (fun i => (.bvar (i + 1) : Expr Nat)))).resolve_left hne
      rw [hpz, foldApps_snoc] at hf
      exact Expr.noConfusion hf
  have hnp : w.nparams = 2 := by omega
  have hfl : w.fields.length = 2 := by
    have h := w.hnpar; rw [hcm] at h
    have h4 : piCount andIntroMember.mtype = 4 := rfl
    omega
  have hpeelC := w.hpeel
  rw [hcm, hnp, hfl] at hpeelC
  have hpeel4 : peelPis 4 andIntroMember.mtype =
      some ([.sort .zero, .sort .zero, .bvar 1, .bvar 1],
        andApp (.bvar 3) (.bvar 2)) := rfl
  rw [hpeel4] at hpeelC
  have hds : w.ctorDoms = [.sort .zero, .sort .zero, .bvar 1, .bvar 1] :=
    (Prod.mk.inj (Option.some.inj hpeelC)).1.symm
  have hkr : w.kinds = [.plain, .plain] := by
    have h := w.hkinds
    rw [hfr, hds, hnp] at h
    exact (Option.some.inj h).symm
  have hcap : w.ctorAfterParams =
      .pi (.bvar 4) (.pi (.bvar 4) (andApp (.bvar 6) (.bvar 5))) := by
    have h := w.hctorAfter
    rw [hp, hnp, hcm] at h
    exact (Option.some.inj h).symm
  have hmi : w.minor = mixAndMin := by
    have h := w.hminor
    rw [hp, hnp, hci] at h
    exact (Option.some.inj h).symm
  obtain ⟨f1, f2, hf12⟩ : ∃ f1 f2, w.fields = [f1, f2] := by
    generalize hwf : w.fields = fs at hfl
    rcases fs with _ | ⟨f1, fs⟩
    · simp only [List.length_nil] at hfl; exfalso; omega
    · rcases fs with _ | ⟨f2, fs'⟩
      · simp only [List.length_cons, List.length_nil] at hfl; exfalso; omega
      · rcases fs' with _ | ⟨f3, fs''⟩
        · exact ⟨f1, f2, rfl⟩
        · simp only [List.length_cons] at hfl; exfalso; omega
  have hrhs : iotaRhsOf w = .app (.app mixAndMin f1) f2 := by
    show foldApps w.minor
        (rhsArgs (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors w.fields w.kinds
          w.ctorAfterParams) = _
    rw [hmi, hp, hnp, hnM, hf12, hkr, hcap]
    rfl
  rw [hrhs]
  exact .step (.ctx (.appHead (.beta (.bvar 4) (.lam (.bvar 4) mixPi) f1)))
    (.step (.ctx (.beta (.bvar 3) mixPi f2)) (.refl _))

/-! ### §5 — the app case at proposition-typed arguments, against `#7673`'s λ clause -/

/-- `λ p : True. Sort 0`. -/
def kConstFn : Expr Nat := .lam (.const 0 []) (.sort .zero)

/-- The step compact demanding `intro`'s compact on the proof argument. -/
def kDemandCpt : CptI := .lam [([.spine 1 []], .sort)]

theorem approxI_kConstFn_app_sort :
    ApproxI (ctxEnvI kVarCtx) (.app kConstFn (.const 1 [])) .sort :=
  .app (g := [([.spine 1 []], .sort)]) (s := ([.spine 1 []], .sort))
    (.lam (fun s' hs => by
      rcases List.mem_singleton.mp hs with rfl
      exact .sort _ _))
    (List.mem_singleton.mpr rfl)
    (fun u hu => by
      rcases List.mem_singleton.mp hu with rfl
      exact .const _ _ _)

/-- (i) The conversion the app case meets: η-K on the function, irrelevance on the argument. -/
def appIrr_conv (n : Nat) :
    ConvT trueEnvU n kVarCtx (.app kConstFn (.const 1 [])) (.app kRecHead (.bvar 0))
      (.app kMot (.const 1 [])) :=
  .app _ _ _ _ _ _ _ (etaK_conv n)
    (.irr _ _ _ _ trueEnvUF_ty trueEnvUtt_ty (kVar_ty n))

/-- (ii) The function's relation at the demanding compact holds (`WhStepK`). -/
theorem lrSCore_whStepK_kConstFn_kRecHead (n : Nat) :
    LRSCore (WhStepK trueEnvU n) trueEnvU n kVarCtx kConstFn kRecHead
      (.pi (.const 0 []) (.app kMot (.bvar 0))) kDemandCpt := by
  rw [LRSCore.eq_def]
  refine ⟨.const 0 [], .app kMot (.bvar 0), .succ (.succ .zero), .refl _,
    ⟨.assumption _ _ _ (kVarCtx_wf n) trueEnvUF_ty⟩,
    ⟨.app _ _ _ _ _ trueEnvUM_ty
      (.bvar _ 0 _
        (rfl : lookupType (.assumption (.const 0 []) :: kVarCtx) 0 = some (.const 0 [])))⟩, ?_⟩
  intro s hs N N' _ hN' _ _
  rcases List.mem_singleton.mp hs with rfl
  refine Or.inr ?_
  show LRSCore (WhStepK trueEnvU n) trueEnvU n kVarCtx
    (.app kConstFn N) (.app kRecHead N') (.app kMot N) .sort
  rw [LRSCore.eq_def]
  exact ⟨⟨_, redR_single (.ctx (.beta _ _ _))⟩, _, _,
    redR_single (.ctx (.beta _ _ _)),
    redR_of_whRedK (whRedK_kRec hN')⟩

/-- (iii) The argument's relation holds — as the collapse — for every readback with the laws. -/
theorem lrS_intro_var {R : Readback} (hL : ReadbackLaws trueEnvU R) (n : Nat) :
    LRS R trueEnvU n kVarCtx (.const 1 []) (.bvar 0) (.const 0 []) (.spine 1 []) :=
  lrS_prop_total ⟨trueEnvUF_ty⟩
    (fun l h => by
      have e := redR_famApp_eq hL trueEnvUWfT (r := 0) (m := trueFamMember) rfl rfl
        (ls := []) (xs := []) h
      exact Expr.noConfusion e)
    (.spine 1 [])

/-- (iv) **The premise the λ clause needs is false**, for every readback with the laws under which
    the assumption `h` is normal. -/
theorem not_lrSCore_intro_var {R : Readback} (hL : ReadbackLaws trueEnvU R)
    (hb : ∀ e, ¬ R kVarCtx (.bvar 0) e) (n : Nat) :
    ¬ LRSCore R trueEnvU n kVarCtx (.const 1 []) (.bvar 0) (.const 0 []) (.spine 1 []) := by
  intro h
  rw [LRSCore.eq_def] at h
  have hbvar : ∀ {e : Expr Nat}, RedR R kVarCtx (.bvar 0) e → e = .bvar 0 := fun h' => by
    cases h' with
    | refl => rfl
    | step hs _ => exact (hb _ hs).elim
  rcases h with ⟨⟨l, hl⟩, _⟩ | ⟨_, _, ls₂, _, args₂, _, h2, _, _, _, _, _, _, _, _⟩
  · have e := redR_famApp_eq hL trueEnvUWfT (r := 0) (m := trueFamMember) rfl rfl
      (ls := []) (xs := []) hl
    exact Expr.noConfusion e
  · exact foldApps_const_ne_bvar _ _ (hbvar h2)

/-- A bound variable with no stored value takes no `WhStepK` step (auxiliary induction). -/
theorem whStepK_bvar_none_false_aux {n : Nat} {Γ : LCtx} {i : Nat}
    (h0 : lookupValue Γ i = none) {a e : Expr Nat} (h : WhStepK E n Γ a e) :
    a = .bvar i → False := by
  induction h with
  | ctx hs => intro heq; subst heq; exact whStepCtx_bvar_none_false h0 hs
  | pmajor _ _ _ _ =>
      intro heq
      rw [recCall_eq_app] at heq
      exact Expr.noConfusion heq
  | recArg _ _ _ _ =>
      intro heq
      rw [foldApps_snoc] at heq
      exact Expr.noConfusion heq
  | appHead _ _ => intro heq; exact Expr.noConfusion heq

theorem whStepK_bvar0_false {n : Nat} {e : Expr Nat} : ¬ WhStepK trueEnvU n kVarCtx (.bvar 0) e :=
  fun h => whStepK_bvar_none_false_aux (rfl : lookupValue kVarCtx 0 = none) h rfl

theorem whStepCK_bvar0_false {e : Expr Nat} : ¬ WhStepCK trueEnvU kVarCtx (.bvar 0) e :=
  fun h => whStepCK_bvar_none_false (rfl : lookupValue kVarCtx 0 = none) h rfl

/-- (v) **The app-case conclusion holds** (`WhStepK`). -/
theorem lrSCore_whStepK_appIrr (n : Nat) :
    LRSCore (WhStepK trueEnvU n) trueEnvU n kVarCtx (.app kConstFn (.const 1 []))
      (.app kRecHead (.bvar 0)) (.app kMot (.const 1 [])) .sort := by
  rw [LRSCore.eq_def]
  exact ⟨⟨_, redR_single (.ctx (.beta _ _ _))⟩, _, _,
    redR_single (.ctx (.beta _ _ _)),
    redR_of_whRedK (whRedK_kRec (kVar_ty n))⟩

/-- ... and with the core `WhStepCK`. -/
theorem lrSCore_whStepCK_appIrr (n : Nat) :
    LRSCore (WhStepCK trueEnvU) trueEnvU n kVarCtx (.app kConstFn (.const 1 []))
      (.app kRecHead (.bvar 0)) (.app kMot (.const 1 [])) .sort := by
  have hnc : ¬ IsCtorSpine trueEnvU (.bvar 0) := by
    rintro ⟨c, us, ys, m, hx, _, _⟩
    exact foldApps_const_ne_bvar _ _ hx.symm
  rw [LRSCore.eq_def]
  exact ⟨⟨_, redR_single (.ctx (.beta _ _ _))⟩, _, _,
    redR_single (.ctx (.beta _ _ _)),
    redR_single (whStepCK_kRec hnc)⟩

/-- (vi) **With collapse-related arguments the λ clause instance holds at every pair of proofs** —
    the K step reads `True.rec M (Sort 0) N'` back to `Sort 0` whatever the proof `N'`. -/
theorem lrSCore_whStepK_kConstFn_app_all {N N' : Expr Nat}
    (hN : HasTyT trueEnvU n kVarCtx N (.const 0 [])) (hN' : HasTyT trueEnvU n kVarCtx N' (.const 0 [])) :
    LRSCore (WhStepK trueEnvU n) trueEnvU n kVarCtx (.app kConstFn N) (.app kRecHead N')
      (.app kMot N) .sort := by
  rw [LRSCore.eq_def]
  exact ⟨⟨_, redR_single (.ctx (.beta _ _ _))⟩, _, _,
    redR_single (.ctx (.beta _ _ _)),
    redR_of_whRedK (whRedK_kRec hN')⟩

/-! #### §5.1 — `#7673`'s `AppPropArgs` and the model's K-invariance, measured -/

/-- `True` is a non-universe proposition for every readback with the laws. -/
theorem isPropTyR_true {R : Readback} (hL : ReadbackLaws trueEnvU R) (n : Nat) :
    IsPropTyR R trueEnvU n kVarCtx (.const 0 []) :=
  ⟨⟨trueEnvUF_ty⟩, fun l h => by
    have e := redR_famApp_eq hL trueEnvUWfT (r := 0) (m := trueFamMember) rfl rfl
      (ls := []) (xs := []) h
    exact Expr.noConfusion e⟩

/-- `#7673`'s interface for the app case at proposition-typed arguments, verbatim from the
    segment-2 comment (stated there as not to be assumed). -/
def AppPropArgs (M : CtxModel) (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {A a b : Expr Nat}, CtxWfT E n Γ → IsPropTyR R E n Γ A →
    HasTyT E n Γ a A → HasTyT E n Γ b A → Nonempty (ConvT E n Γ a b A) →
    ∀ u, M.at Γ a u → LRSCore R E n Γ a b A u

/-- **`AppPropArgs` is false over `ApproxI`** at `trueEnvU` (`intro` vs the proof variable `h`, at
    `intro`'s compact `spine 1 []`), for every readback with the laws under which `h` is normal —
    in particular `WhStepCK` and `WhStepK`. -/
theorem not_appPropArgs_ctxModelI_trueEnvU {R : Readback} (hL : ReadbackLaws trueEnvU R)
    (hb : ∀ e, ¬ R kVarCtx (.bvar 0) e) (n : Nat) : ¬ AppPropArgs ctxModelI R trueEnvU n := by
  intro hA
  exact not_lrSCore_intro_var hL hb n
    (hA (kVarCtx_wf n) (isPropTyR_true hL n) trueEnvUtt_ty (kVar_ty n)
      ⟨.irr _ _ _ _ trueEnvUF_ty trueEnvUtt_ty (kVar_ty n)⟩ (.spine 1 [])
      (ApproxI.const _ 1 []))

/-- ... and over `ApproxDI` (a constructor is rigid, so `intro` has the compact `spine 1 []`). -/
theorem not_appPropArgs_ctxModelDI_trueEnvU {R : Readback} (hL : ReadbackLaws trueEnvU R)
    (hb : ∀ e, ¬ R kVarCtx (.bvar 0) e) (n : Nat) :
    ¬ AppPropArgs (ctxModelDI trueEnvU) R trueEnvU n := by
  intro hA
  exact not_lrSCore_intro_var hL hb n
    (hA (kVarCtx_wf n) (isPropTyR_true hL n) trueEnvUtt_ty (kVar_ty n)
      ⟨.irr _ _ _ _ trueEnvUF_ty trueEnvUtt_ty (kVar_ty n)⟩ (.spine 1 [])
      (PiModelDeltaIotaAudit.ApproxDI.const _ 1 []
        (PiModelDeltaIotaAudit.rigidConst_of_ctor rfl rfl)))

/-- **The K step is not model-invariant over `ApproxI`**: `kRec h ↝ Sort 0`, and `Sort 0` has the
    compact `sort` that `kRec h` lacks — so `link_pmajor_K`'s `hinv` fails there. -/
theorem not_readbackModelInv_whStepCK_ctxModelI :
    ¬ ReadbackModelInv (WhStepCK trueEnvU) ctxModelI := by
  intro hI
  have hiff := hI kVarCtx
    (whStepCK_kRec (x := .bvar 0) not_isCtorSpine_bvar) .sort
  have hk : ApproxI (ctxEnvI kVarCtx) (kRec (.bvar 0)) .sort :=
    hiff.mpr (ApproxI.sort _ _)
  have hk' : ApproxI (ctxEnvI kVarCtx)
      (foldApps (.const 2 [.succ (.succ .zero)]) [kMot, .sort .zero, .bvar 0]) .sort := hk
  rcases approxI_foldApps_const_inv hk' with hbot | ⟨us, hsp, _⟩
  · exact CptI.noConfusion hbot
  · exact CptI.noConfusion hsp

theorem not_readbackModelInv_whStepK_ctxModelI (n : Nat) :
    ¬ ReadbackModelInv (WhStepK trueEnvU n) ctxModelI := by
  intro hI
  have hstep : WhStepK trueEnvU n kVarCtx (kRec (.bvar 0)) (.sort .zero) :=
    .pmajor (.ofU wTrueRecU) ⟨trueEnvUF_ty⟩ ⟨trueEnvUtt_ty⟩ ⟨kVar_ty n⟩
  have hiff := hI kVarCtx hstep .sort
  have hk : ApproxI (ctxEnvI kVarCtx) (kRec (.bvar 0)) .sort :=
    hiff.mpr (ApproxI.sort _ _)
  have hk' : ApproxI (ctxEnvI kVarCtx)
      (foldApps (.const 2 [.succ (.succ .zero)]) [kMot, .sort .zero, .bvar 0]) .sort := hk
  rcases approxI_foldApps_const_inv hk' with hbot | ⟨us, hsp, _⟩
  · exact CptI.noConfusion hbot
  · exact CptI.noConfusion hsp

/-- Over `ApproxDI` the recursor's ι semantics demands a constructor compact at the major, which
    the assumption `h` does not supply: `kRec h` has no `sort` compact. -/
theorem not_approxDI_kRec_var_sort :
    ¬ PiModelDeltaIotaAudit.ApproxDI trueEnvU (ctxEnvDI trueEnvU kVarCtx)
      (kRec (.bvar 0)) .sort := by
  intro h
  have h' : PiModelDeltaIotaAudit.ApproxDI trueEnvU (ctxEnvDI trueEnvU kVarCtx)
      (foldApps (.const 2 [.succ (.succ .zero)]) [kMot, .sort .zero, .bvar 0]) .sort := h
  obtain ⟨d, hd, hfold⟩ :=
    (PiModelDeltaIotaAudit.approxDI_foldApps_iff trueEnvU _ _ _ _).mp h'
  rcases PiModelDeltaIotaAudit.approxDI_recursor_const_inv
      (m := trueRecMemberU) rfl rfl hd with hdbot |
      ⟨w, us_pre, us_fields, c₀, hrr, hpreS, _, _, hd'⟩
  · subst hdbot
    exact CptI.noConfusion (PiModelDeltaIotaAudit.foldAppCpt_bot_inv hfold)
  · subst hd'
    have hrm : w.recMember = trueRecMemberU := by
      have a := w.hrec; rw [hrr] at a; exact (Option.some.inj a).symm
    have hni3 : w.nparams + 1 + w.nMinors + w.nindices + 1 = 3 := by
      have a := w.hnmin; rw [hrm] at a; exact a
    have hnp : w.nparams = 0 := by have a := w.hidx; omega
    have hnM : w.nMinors = 1 := by have a := w.hidx; omega
    have hni : w.nindices = 0 := by have a := w.hidx; omega
    have hprel : w.preMajor.length = 2 := by
      have a := w.hpre; rw [hnp, hnM, hni] at a; omega
    have hlen2 : us_pre.length = 2 := hpreS.trans hprel
    have hlen3 : (us_pre ++
        [PiModelDeltaIotaAudit.ctorDemand w.ctorRef w.nparams us_fields]).length =
        [kMot, .sort .zero, .bvar 0].length := by
      simp only [List.length_append, List.length_singleton, List.length_cons,
        List.length_nil]; omega
    obtain ⟨u0, u1, hup⟩ : ∃ u0 u1, us_pre = [u0, u1] := by
      rcases us_pre with _ | ⟨u0, s⟩
      · simp only [List.length_nil] at hlen2; exfalso; omega
      · rcases s with _ | ⟨u1, s'⟩
        · simp only [List.length_cons, List.length_nil] at hlen2; exfalso; omega
        · rcases s' with _ | ⟨u2, s''⟩
          · exact ⟨u0, u1, rfl⟩
          · simp only [List.length_cons] at hlen2; exfalso; omega
    subst hup
    rcases (PiModelDeltaIotaAudit.foldAppCpt_curryStep_iff hlen3).mp hfold with hsb |
        ⟨hargs, _⟩
    · exact CptI.noConfusion hsb
    · cases hargs with
      | cons _ h₂ =>
          cases h₂ with
          | cons _ h₃ =>
              cases h₃ with
              | cons ha₃ _ =>
                  have hmem : CptI.spine w.ctorRef
                        (List.replicate w.nparams CptI.bot ++
                          List.replicate us_fields.length CptI.bot) ∈
                      PiModelDeltaIotaAudit.ctorDemand w.ctorRef w.nparams us_fields :=
                    List.mem_cons_self _ _
                  rcases PiModelDeltaIotaAudit.approxDI_bvar_inv (ha₃ _ hmem) with hbot | hρ
                  · exact CptI.noConfusion hbot
                  · have heq : CptI.spine w.ctorRef
                        (List.replicate w.nparams CptI.bot ++
                          List.replicate us_fields.length CptI.bot) = .bot := hρ
                    exact CptI.noConfusion heq

/-- **The K step is not model-invariant over `ApproxDI` either.** -/
theorem not_readbackModelInv_whStepCK_ctxModelDI :
    ¬ ReadbackModelInv (WhStepCK trueEnvU) (ctxModelDI trueEnvU) := by
  intro hI
  have hiff := hI kVarCtx
    (whStepCK_kRec (x := .bvar 0) not_isCtorSpine_bvar) .sort
  exact not_approxDI_kRec_var_sort
    (hiff.mpr (PiModelDeltaIotaAudit.ApproxDI.sort _ _))

theorem not_readbackModelInv_whStepK_ctxModelDI (n : Nat) :
    ¬ ReadbackModelInv (WhStepK trueEnvU n) (ctxModelDI trueEnvU) := by
  intro hI
  have hstep : WhStepK trueEnvU n kVarCtx (kRec (.bvar 0)) (.sort .zero) :=
    .pmajor (.ofU wTrueRecU) ⟨trueEnvUF_ty⟩ ⟨trueEnvUtt_ty⟩ ⟨kVar_ty n⟩
  have hiff := hI kVarCtx hstep .sort
  exact not_approxDI_kRec_var_sort
    (hiff.mpr (PiModelDeltaIotaAudit.ApproxDI.sort _ _))

/-! ### §6 — substitution: the K reduct at a constructor major vs the ι reduct -/

/-! #### generic projection readback: the β machinery -/

/-- `instantiate` under a λ-telescope: the body is substituted at the shifted index with
    the shifted replacement; the binder domains are re-bound by name only. -/
theorem instantiate_lamTel_body (n : Nat) (r : Expr Nat) :
    ∀ (ds : List (Expr Nat)) (b : Expr Nat),
      ∃ ds' : List (Expr Nat), ds'.length = ds.length ∧
        instantiate n r (lamTel ds b) =
          lamTel ds' (instantiate (n + ds.length) (lift 0 ds.length r) b)
  | [], b => ⟨[], rfl, by simp only [lamTel, List.length_nil, lift_zero, Nat.add_zero]⟩
  | d :: ds, b => by
      obtain ⟨ds', hdl, ih⟩ := instantiate_lamTel_body (n + 1) (lift 0 1 r) ds b
      refine ⟨instantiate n r d :: ds', by simp only [List.length_cons, hdl], ?_⟩
      show instantiate n r (.lam d (lamTel ds b)) =
        lamTel (instantiate n r d :: ds')
          (instantiate (n + (d :: ds).length) (lift 0 (d :: ds).length r) b)
      show Expr.lam (instantiate n r d) (instantiate (n + 1) (lift 0 1 r) (lamTel ds b)) =
        Expr.lam (instantiate n r d)
          (lamTel ds' (instantiate (n + (d :: ds).length) (lift 0 (d :: ds).length r) b))
      congr 1
      have hidx : n + (d :: ds).length = n + 1 + ds.length := by
        simp only [List.length_cons]; omega
      have hrep : lift 0 (d :: ds).length r = lift 0 ds.length (lift 0 1 r) := by
        show lift 0 (ds.length + 1) r = lift 0 ds.length (lift 0 1 r)
        rw [lift_lift_merge ds.length 1 0 0 (Nat.le_refl 0) (Nat.zero_le _) r,
          Nat.add_comm (1 : Nat) ds.length]
      rw [ih, hidx, hrep]

/-- A `WhStepCtx` at a `foldApps` spine head, lifted into the core. -/
theorem whStepCtx_foldApps_head {Γ : LCtx} {a b : Expr Nat} (h : WhStepCtx E Γ a b) :
    ∀ xs, WhStepCK E Γ (foldApps a xs) (foldApps b xs)
  | [] => .ctx h
  | _ :: xs => whStepCtx_foldApps_head (.appHead h) xs

/-- A λ-telescope with a body lifted over its own binders, applied to a same-length
    spine, β-reads back the un-lifted body (each β consumes one lift unit). -/
theorem whRed_lamTel_lift {Γ : LCtx} :
    ∀ (fs ds : List (Expr Nat)) (hlen : ds.length = fs.length) (e : Expr Nat),
      RedR (WhStepCK E) Γ (foldApps (lamTel ds (lift 0 ds.length e)) fs) e
  | [], ds, hlen, e => by
      cases ds with
      | nil =>
          show RedR (WhStepCK E) Γ (lift 0 (0 : Nat) e) e
          rw [lift_zero]
          exact .refl _
      | cons _ _ =>
          simp only [List.length_cons, List.length_nil] at hlen
          cases hlen
  | f :: fs, ds, hlen, e => by
      cases ds with
      | nil =>
          simp only [List.length_nil, List.length_cons] at hlen
          cases hlen
      | cons d ds =>
          have hlen' : ds.length = fs.length := Nat.succ.inj hlen
          refine .step (whStepCtx_foldApps_head
            (.beta _ (lamTel ds (lift 0 (ds.length + 1) e)) f) fs) ?_
          obtain ⟨ds', hdl, hb⟩ := instantiate_lamTel_body 0 f ds (lift 0 (ds.length + 1) e)
          show RedR (WhStepCK E) Γ
            (foldApps (instantiate 0 f (lamTel ds (lift 0 (ds.length + 1) e))) fs) e
          rw [hb, Nat.zero_add]
          show RedR (WhStepCK E) Γ
            (foldApps (lamTel ds'
              (instantiate ds.length (lift 0 ds.length f) (lift 0 (ds.length + 1) e))) fs) e
          rw [instantiate_lift_cancel (ds.length + 1) 0 ds.length (lift 0 ds.length f)
            (Nat.zero_le _) (by omega) e]
          show RedR (WhStepCK E) Γ (foldApps (lamTel ds' (lift 0 (ds.length + 1 - 1) e)) fs) e
          rw [show ds.length + 1 - 1 = ds'.length by omega]
          exact whRed_lamTel_lift fs ds' (hdl.trans hlen') e

/-- A λ-telescope selecting `bvar j`, applied to a same-length spine, β-reads back the
    `ds.length - 1 - j`-th argument (the field the projection's minor selects). -/
theorem whRed_lamTel_bvar {Γ : LCtx} (dflt : Expr Nat) :
    ∀ (fs ds : List (Expr Nat)) (hlen : ds.length = fs.length) (j : Nat) (hj : j < ds.length),
      RedR (WhStepCK E) Γ (foldApps (lamTel ds (.bvar j)) fs)
        (fs.getD (fs.length - 1 - j) dflt)
  | [], ds, hlen, j, hj => by
      cases ds with
      | nil => simp at hj
      | cons _ _ =>
          simp only [List.length_cons, List.length_nil] at hlen
          cases hlen
  | f :: fs, ds, hlen, j, hj => by
      cases ds with
      | nil => simp at hj
      | cons d ds =>
          have hlen' : ds.length = fs.length := Nat.succ.inj hlen
          have hj' : j < ds.length + 1 := hj
          refine .step (whStepCtx_foldApps_head (.beta _ (lamTel ds (.bvar j)) f) fs) ?_
          obtain ⟨ds', hdl, hb⟩ := instantiate_lamTel_body 0 f ds (.bvar j)
          show RedR (WhStepCK E) Γ (foldApps (instantiate 0 f (lamTel ds (.bvar j))) fs) _
          rw [hb, Nat.zero_add]
          rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj') with rfl | hlt
          · have hfire : instantiate ds.length (lift 0 ds.length f) (.bvar ds.length) =
                lift 0 ds.length f := by
              simp only [instantiate]
              rw [if_pos trivial]
            rw [hfire, ← hdl]
            have hidx : (f :: fs).length - 1 - ds'.length = 0 := by
              simp only [List.length_cons]
              have := hdl.trans hlen'
              omega
            rw [hidx]
            show RedR (WhStepCK E) Γ
              (foldApps (lamTel ds' (lift 0 ds'.length f)) fs) f
            exact whRed_lamTel_lift fs ds' (hdl.trans hlen') f
          · have hfire : instantiate ds.length (lift 0 ds.length f) (.bvar j) = .bvar j := by
              simp only [instantiate]
              rw [if_neg (by omega : ¬ (j = ds.length)),
                if_neg (by omega : ¬ (ds.length < j))]
            rw [hfire]
            have hidx : (f :: fs).length - 1 - j = (fs.length - 1 - j) + 1 := by
              simp only [List.length_cons]; omega
            rw [hidx]
            exact whRed_lamTel_bvar dflt fs ds' (hdl.trans hlen') j
              (by rw [hdl]; exact hlt)

/-- `(projAll w k …)` has length `k`. -/
theorem projAll_length {w : IotaWitness E} :
    ∀ (k : Nat) (ps ix : List (Expr Nat)) (x : Expr Nat),
      (projAll w k ps ix x).length = k
  | 0, _, _, _ => rfl
  | k + 1, ps, ix, x => by
      show (projAll w k ps ix x ++ [_]).length = k + 1
      rw [List.length_append, projAll_length k ps ix x]
      rfl

/-- Entry `j` of `projAll w k` is the `j`-th canon field (with the earlier canon fields
    of `bvar 0` as its `prevM`). -/
theorem projAll_getElem? {w : IotaWitness E} :
    ∀ (k j : Nat) (hj : j < k) (ps ix : List (Expr Nat)) (x : Expr Nat),
      (projAll w k ps ix x)[j]? =
        some (canonField w j ps ix
          (projAll w j (ps.map (lift 0 (w.nindices + 1))) (motIdx w.nindices) (.bvar 0)) x)
  | 0, j, hj, _, _, _ => absurd hj (by simp)
  | k + 1, j, hj, ps, ix, x => by
      show (projAll w k ps ix x ++
          [canonField w k ps ix
            (projAll w k (ps.map (lift 0 (w.nindices + 1))) (motIdx w.nindices)
              (.bvar 0)) x])[j]? = _
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hlt
      · rw [List.getElem?_append_right
          (by rw [projAll_length]; exact Nat.le_refl _), projAll_length, Nat.sub_self]
        rfl
      · rw [List.getElem?_append_left (by rw [projAll_length]; exact hlt)]
        exact projAll_getElem? k j hlt ps ix x

/-- `rhsArgs` with all-plain kinds keeps exactly the fields. -/
theorem rhsArgs_plain (rec : Expr Nat) (pre : List (Expr Nat)) (np nm : Nat) :
    ∀ (fs : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat),
      (∀ k ∈ ks, k = .plain) → rhsArgs rec pre np nm fs ks T = fs
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => by
      show _ = _ :: _
      exact congrArg _ (rhsArgs_plain rec pre np nm _ [] _ (fun _ hk => by cases hk))
  | _ :: fs, k :: ks, T, h => by
      obtain rfl := h k (List.mem_cons_self _ _)
      have ih : ∀ T', rhsArgs rec pre np nm fs ks T' = fs :=
        fun T' => rhsArgs_plain rec pre np nm fs ks T'
          (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
      cases T with
      | pi A B =>
          show _ :: rhsArgs rec pre np nm fs ks (instantiate0 _ B) = _
          exact congrArg _ (ih _)
      | bvar i =>
          show _ :: rhsArgs rec pre np nm fs ks (.bvar i) = _
          exact congrArg _ (ih _)
      | sort l =>
          show _ :: rhsArgs rec pre np nm fs ks (.sort l) = _
          exact congrArg _ (ih _)
      | const r' ls =>
          show _ :: rhsArgs rec pre np nm fs ks (.const r' ls) = _
          exact congrArg _ (ih _)
      | app f' x =>
          show _ :: rhsArgs rec pre np nm fs ks (.app f' x) = _
          exact congrArg _ (ih _)
      | lam a b =>
          show _ :: rhsArgs rec pre np nm fs ks (.lam a b) = _
          exact congrArg _ (ih _)
      | letE a v b =>
          show _ :: rhsArgs rec pre np nm fs ks (.letE a v b) = _
          exact congrArg _ (ih _)
      | lit t =>
          show _ :: rhsArgs rec pre np nm fs ks (.lit t) = _
          exact congrArg _ (ih _)

/-- `isPiTel n T` gives the first `n` Π-domains of `T`. -/
theorem peelPis_of_isPiTel :
    ∀ (n : Nat) (T : Expr Nat), isPiTel n T = true →
      ∃ ds r, peelPis n T = some (ds, r) ∧ ds.length = n
  | 0, _, _ => ⟨[], _, rfl, rfl⟩
  | n + 1, .pi A B, h => by
      obtain ⟨ds, r, hp, hl⟩ := peelPis_of_isPiTel n B h
      exact ⟨A :: ds, r, by simp only [peelPis, hp], by simp only [List.length_cons, hl]⟩
  | n + 1, .bvar _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .sort _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .const _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .app _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .lam _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .letE _ _ _, h => by simp only [isPiTel] at h; nomatch h
  | n + 1, .lit _, h => by simp only [isPiTel] at h; nomatch h

/-- `minorTel`'s binder count is `ks.length + recCountOf ks` whenever the remaining
    constructor tail is a `ks.length`-Π telescope (one IH binder per `directRec` field). -/
theorem isPiTel_minorTel (np : Nat) :
    ∀ (M acc : Expr Nat) (ks : List RecKind) (T : Expr Nat),
      isPiTel ks.length T = true →
      isPiTel (ks.length + recCountOf ks) (minorTel M np acc ks T) = true
  | _, _, [], _, _ => rfl
  | M, acc, k :: ks, T, h => by
      cases T with
      | pi A B =>
          cases k with
          | plain =>
              rw [show (RecKind.plain :: ks).length + recCountOf (RecKind.plain :: ks) =
                  ks.length + recCountOf ks + 1 by
                simp only [List.length_cons, recCountOf]; omega]
              show isPiTel _ (.pi A
                  (minorTel (lift 0 1 M) np (.app (lift 0 1 acc) (.bvar 0)) ks B)) = true
              exact isPiTel_minorTel np (lift 0 1 M)
                (.app (lift 0 1 acc) (.bvar 0)) ks B h
          | directRec =>
              rw [show (RecKind.directRec :: ks).length + recCountOf
                  (RecKind.directRec :: ks) = ks.length + recCountOf ks + 2 by
                simp only [List.length_cons, recCountOf]; omega]
              show isPiTel _ (.pi A
                  (.pi (.app (lift 0 1 (foldApps M (familyIdx np A))) (.bvar 0))
                    (minorTel (lift 0 2 M) np (.app (lift 0 2 acc) (.bvar 1)) ks
                      (lift 0 1 B)))) = true
              exact isPiTel_minorTel np (lift 0 2 M)
                (.app (lift 0 2 acc) (.bvar 1)) ks (lift 0 1 B)
                (isPiTel_lift 0 1 ks.length B h)
      | bvar i' => nomatch h
      | sort l => nomatch h
      | const r' ls' => nomatch h
      | app f' x' => nomatch h
      | lam a' b' => nomatch h
      | letE a' v' b' => nomatch h
      | lit t' => nomatch h

/-- `rhsArgs` feeds `fs.length + recCountOf ks` arguments to the minor: the fields,
    interleaved with one recursive call after each `directRec` field. -/
theorem rhsArgs_length (rec : Expr Nat) (pre : List (Expr Nat)) (np nm : Nat) :
    ∀ (fs : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat),
      ks.length = fs.length → isPiTel ks.length T = true →
      (rhsArgs rec pre np nm fs ks T).length = fs.length + recCountOf ks := by
  intro fs
  induction fs with
  | nil =>
      intro ks T hlen _
      cases ks with
      | nil => rfl
      | cons k ks =>
          simp only [List.length_cons, List.length_nil] at hlen
          cases hlen
  | cons f fs ih =>
      intro ks T hlen htel
      cases ks with
      | nil =>
          simp only [List.length_nil, List.length_cons] at hlen
          cases hlen
      | cons k ks =>
          cases T with
          | pi A B =>
              cases k with
              | plain =>
                  show (f :: rhsArgs rec pre np nm fs ks (instantiate0 f B)).length = _
                  rw [List.length_cons,
                    ih ks (instantiate0 f B) (Nat.succ.inj hlen)
                      (isPiTel_instantiate 0 f ks.length B htel)]
                  simp only [List.length_cons, recCountOf]
                  omega
              | directRec =>
                  show (f :: recCallField rec pre np nm f A ::
                      rhsArgs rec pre np nm fs ks (instantiate0 f B)).length = _
                  rw [List.length_cons, List.length_cons,
                    ih ks (instantiate0 f B) (Nat.succ.inj hlen)
                      (isPiTel_instantiate 0 f ks.length B htel)]
                  simp only [List.length_cons, recCountOf]
                  omega
          | bvar i' => nomatch htel
          | sort l => nomatch htel
          | const r' ls' => nomatch htel
          | app f' x' => nomatch htel
          | lam a' b' => nomatch htel
          | letE a' v' b' => nomatch htel
          | lit t' => nomatch htel

/-- `rhsArgs` inserts the recursive call AFTER its field, so field `i` stays at binder
    position `minorPosOf ks i`. -/
theorem rhsArgs_getD_minorPos (rec : Expr Nat) (pre : List (Expr Nat)) (np nm : Nat)
    (dflt : Expr Nat) :
    ∀ (fs : List (Expr Nat)) (ks : List RecKind) (T : Expr Nat) (i : Nat),
      ks.length = fs.length → isPiTel ks.length T = true → i < fs.length →
      (rhsArgs rec pre np nm fs ks T).getD (minorPosOf ks i) dflt = fs.getD i dflt := by
  intro fs
  induction fs with
  | nil => intro ks T i _ _ hi; exact absurd hi (Nat.not_lt_zero _)
  | cons f fs ih =>
      intro ks T i hlen htel hi
      cases ks with
      | nil =>
          simp only [List.length_nil, List.length_cons] at hlen
          cases hlen
      | cons k ks =>
          cases i with
          | zero =>
              cases T with
              | pi A B => cases k <;> rfl
              | bvar i' => nomatch htel
              | sort l => nomatch htel
              | const r' ls' => nomatch htel
              | app f' x' => nomatch htel
              | lam a' b' => nomatch htel
              | letE a' v' b' => nomatch htel
              | lit t' => nomatch htel
          | succ i =>
              cases T with
              | pi A B =>
                  cases k <;>
                    exact ih ks (instantiate0 f B) i (Nat.succ.inj hlen)
                      (isPiTel_instantiate 0 f ks.length B htel)
                      (Nat.lt_of_succ_lt_succ hi)
              | bvar i' => nomatch htel
              | sort l => nomatch htel
              | const r' ls' => nomatch htel
              | app f' x' => nomatch htel
              | lam a' b' => nomatch htel
              | letE a' v' b' => nomatch htel
              | lit t' => nomatch htel

/-- `minorPosOf` selects field `i` inside the `ks.length + recCountOf ks` minor binders. -/
theorem minorPosOf_lt :
    ∀ (ks : List RecKind) (i : Nat), i < ks.length →
      minorPosOf ks i < ks.length + recCountOf ks
  | ks, 0, hi => by
      cases ks with
      | nil => exact absurd hi (Nat.not_lt_zero _)
      | cons k ks =>
          have h0 : minorPosOf (k :: ks) 0 = 0 := by simp only [minorPosOf]
          rw [h0]; omega
  | [], i + 1, hi => absurd hi (Nat.not_lt_zero _)
  | .plain :: ks, i + 1, hi => by
      show minorPosOf ks i + 1 < ks.length + 1 + recCountOf ks
      have h' := minorPosOf_lt ks i (Nat.lt_of_succ_lt_succ hi)
      omega
  | .directRec :: ks, i + 1, hi => by
      show minorPosOf ks i + 2 < ks.length + 1 + (recCountOf ks + 1)
      have h' := minorPosOf_lt ks i (Nat.lt_of_succ_lt_succ hi)
      omega

/-- **Readback half (generic)**: the `i`-th projection of the constructor major of a fieldful,
    non-recursive proposition-singleton redex reads back, in the core, to the `i`-th field
    (ι at the projection's proposition motive, then `k` β steps through its minor). -/
theorem redR_projField_ctorMajor (hW : EnvWfT E) {Γ : LCtx} {w : IotaWitness E} (hK : KFieldW w)
    {i : Nat} (hi : i < w.fields.length) (hnr : revealedPos? w i = none) :
    RedR (WhStepCK E) Γ ((projFields w (ctorMajor w)).getD i (.sort .zero))
      (w.fields.getD i (.sort .zero)) := by
  obtain ⟨_, hnm1, _, hpk⟩ := hK
  have hflen : w.fields.length = fieldCount w := by
    have hp := w.hnpar
    show w.fields.length = piCount w.ctorMember.mtype - w.nparams
    omega
  have hilen : i < fieldCount w := hflen ▸ hi
  have hpos : 0 < fieldCount w := by omega
  let params := w.preMajor.take w.nparams
  let idxs := w.preMajor.drop (w.nparams + 1 + w.nMinors)
  have hpdef : params = w.preMajor.take w.nparams := rfl
  have hdef : idxs = w.preMajor.drop (w.nparams + 1 + w.nMinors) := rfl
  have hplen : params.length = w.nparams := by
    have hp := w.hpre
    rw [hpdef, List.length_take]
    omega
  have hxlen : idxs.length = w.nindices := by
    have hp := w.hpre
    rw [hdef, List.length_drop]
    omega
  -- entry `i` of the projection list is its canon field — not index-revealed, so a projection
  have hcf : canonField w i params idxs
        (projAll w i (params.map (lift 0 (w.nindices + 1))) (motIdx w.nindices) (.bvar 0))
        (ctorMajor w) =
      projOne w i params idxs
        (projAll w i (params.map (lift 0 (w.nindices + 1))) (motIdx w.nindices) (.bvar 0))
        (ctorMajor w) := by
    unfold canonField
    rw [hnr]
  have helt : (projFields w (ctorMajor w)).getD i (.sort .zero) =
      projOne w i params idxs
        (projAll w i (params.map (lift 0 (w.nindices + 1))) (motIdx w.nindices) (.bvar 0))
        (ctorMajor w) := by
    show (projAll w (fieldCount w) _ _ _).getD i _ = _
    rw [List.getD_eq_getElem?_getD,
      projAll_getElem? (fieldCount w) i hilen _ _ _]
    exact hcf
  -- the stored constructor type does not mention the motive level
  have hlb : exprLevelsBounded w.famMember.arity w.ctorMember.mtype = true := by
    rw [← envWfT_ctorArity hW w]
    exact (envWfT_levels hW w.ctorRef w.ctorMember w.hctor).1
  have hlv : instantiateLevels (projLevels w) w.ctorMember.mtype =
      instantiateLevels w.ls w.ctorMember.mtype := by
    rw [instantiateLevels_take w.famMember.arity (projLevels w) w.ctorMember.mtype hlb,
      instantiateLevels_take w.famMember.arity w.ls w.ctorMember.mtype hlb]
    show instantiateLevels ((w.ls.set w.famMember.arity .zero).take w.famMember.arity)
        w.ctorMember.mtype = instantiateLevels (w.ls.take w.famMember.arity) w.ctorMember.mtype
    rw [Ann.take_set_of_le w.ls w.famMember.arity w.famMember.arity (Nat.le_refl _) _]
  have hci : w.ctorIdx = 0 := by have := w.hidx; omega
  -- the ι witness of the projection redex: same recursor at `projLevels`, same major
  let motᵢ := lamTel
    (peelDomsOr w.nindices
      (applyTelOr params (instantiateLevels (famLevels w) w.famMember.mtype)) ++
      [foldApps (.const w.familyRef (famLevels w))
        (params.map (lift 0 w.nindices) ++ (List.range w.nindices).reverse.map Expr.bvar)])
    (piDomOr (applyTel (params.map (lift 0 (w.nindices + 1)) ++
      projAll w i (params.map (lift 0 (w.nindices + 1))) (motIdx w.nindices) (.bvar 0))
      (instantiateLevels w.ls w.ctorMember.mtype)))
  let mnᵢ := lamTel
    (peelDomsOr (fieldCount w + recCountOf w.kinds)
      (minorTel motᵢ w.nparams (foldApps (.const w.ctorRef (famLevels w)) params) w.kinds
        (applyTelOr params (instantiateLevels w.ls w.ctorMember.mtype))))
    (.bvar (fieldCount w + recCountOf w.kinds - 1 - minorPosOf w.kinds i))
  let wᵢ : IotaWitness E :=
    { w with
      ls := projLevels w
      preMajor := params ++ [motᵢ, mnᵢ] ++ idxs
      minor := mnᵢ
      hlsLen := by
        show (w.ls.set w.famMember.arity .zero).length = w.recMember.arity
        rw [List.length_set]; exact w.hlsLen
      hpre := by
        simp only [List.length_append, List.length_cons, List.length_nil, hplen, hxlen]
        omega
      hminor := by
        rw [hci]
        rw [List.getElem?_append_left
          (by simp only [List.length_append, List.length_cons, List.length_nil, hplen]; omega)]
        rw [List.getElem?_append_right (by omega), hplen,
          show w.nparams + 1 + 0 - w.nparams = 1 by omega]
        rfl
      hctorAfter := by
        rw [List.take_append_of_le_length
          (by simp only [List.length_append, List.length_cons, List.length_nil, hplen]; omega),
          List.take_left' hplen, hlv]
        exact w.hctorAfter }
  -- `projOne` unfolds to exactly this redex
  have hpo : projOne w i params idxs
        (projAll w i (params.map (lift 0 (w.nindices + 1))) (motIdx w.nindices) (.bvar 0))
        (ctorMajor w) =
      recCall (.const w.recRef (projLevels w)) (params ++ [motᵢ, mnᵢ] ++ idxs)
        (ctorMajor w) := rfl
  -- ι's contractum is `mnᵢ` applied to `rhsArgs`: the fields interleaved with one recursive
  -- call after each `directRec` field (`nb = fieldCount + recCountOf` arguments)
  have hrhs : iotaRhsOf wᵢ = foldApps mnᵢ
      (rhsArgs (.const w.recRef (projLevels w)) (params ++ [motᵢ, mnᵢ] ++ idxs)
        w.nparams w.nMinors w.fields w.kinds w.ctorAfterParams) := rfl
  -- the minor is `λ (minorTel binders). bvar (nb-1-minorPosOf i)`; its binder count is `nb`
  have hAT : applyTelOr params (instantiateLevels w.ls w.ctorMember.mtype) =
      w.ctorAfterParams := by
    show (applyTel params (instantiateLevels w.ls w.ctorMember.mtype)).getD _ = _
    rw [hpdef, w.hctorAfter]
    rfl
  have hkl : w.kinds.length = fieldCount w := by
    have h1 := w.hlen
    rw [hflen] at h1
    exact h1
  obtain ⟨ds, _, hpl, hdl⟩ := peelPis_of_isPiTel
      (w.kinds.length + recCountOf w.kinds)
      (minorTel motᵢ w.nparams (foldApps (.const w.ctorRef (famLevels w)) params) w.kinds
        (applyTelOr params (instantiateLevels w.ls w.ctorMember.mtype)))
      (isPiTel_minorTel w.nparams motᵢ
        (foldApps (.const w.ctorRef (famLevels w)) params) w.kinds _
        (by rw [hAT]; exact w.hctorTel))
  rw [hkl] at hpl hdl
  have hmn : mnᵢ = lamTel ds
      (.bvar (fieldCount w + recCountOf w.kinds - 1 - minorPosOf w.kinds i)) := by
    show lamTel (peelDomsOr _ _) _ = _
    unfold peelDomsOr
    rw [hpl]
  rw [helt, hpo]
  refine .step (.ctx (.iota (.ofU wᵢ))) ?_
  rw [hrhs]
  conv => arg 3; arg 1; rw [hmn]
  have harglen : (rhsArgs (.const w.recRef (projLevels w)) (params ++ [motᵢ, mnᵢ] ++ idxs)
        w.nparams w.nMinors w.fields w.kinds w.ctorAfterParams).length =
      fieldCount w + recCountOf w.kinds := by
    rw [rhsArgs_length _ _ _ _ w.fields w.kinds w.ctorAfterParams w.hlen w.hctorTel, hflen]
  have hpm : minorPosOf w.kinds i < w.kinds.length + recCountOf w.kinds :=
    minorPosOf_lt w.kinds i (by rw [hkl]; exact hilen)
  refine redR_trans (whRed_lamTel_bvar (E := E) (Γ := Γ) (.sort .zero)
      (rhsArgs (.const w.recRef (projLevels w)) (params ++ [motᵢ, mnᵢ] ++ idxs)
        w.nparams w.nMinors w.fields w.kinds w.ctorAfterParams)
      ds (hdl.trans harglen.symm)
      (fieldCount w + recCountOf w.kinds - 1 - minorPosOf w.kinds i) (by omega)) ?_
  have hix : (rhsArgs (.const w.recRef (projLevels w)) (params ++ [motᵢ, mnᵢ] ++ idxs)
        w.nparams w.nMinors w.fields w.kinds w.ctorAfterParams).length - 1 -
        (fieldCount w + recCountOf w.kinds - 1 - minorPosOf w.kinds i) =
      minorPosOf w.kinds i := by
    rw [harglen]
    have hpm' := hpm
    rw [hkl] at hpm'
    omega
  rw [hix]
  show RedR (WhStepCK E) Γ
      ((rhsArgs _ _ _ _ w.fields w.kinds w.ctorAfterParams).getD (minorPosOf w.kinds i)
        (.sort .zero)) _
  rw [rhsArgs_getD_minorPos _ _ _ _ _ w.fields w.kinds w.ctorAfterParams i w.hlen w.hctorTel hi]
  exact .refl _

/-- **Relation half, typed model (`#7673` segment 4's `LRSCoreT`)**: at a λ compact whose step has
    `⊥` demands — every step at a proposition domain of an `ApproxT` compact
    (`approxT_lam_prop_dom_botDemand`) — ANY two typed, convertible arguments relate the
    applications.  This is the proposition collapse at the argument: the K reduct's projection
    `prᵢ (intro ps fs)` and the ι reduct's field `fᵢ` are such a pair. -/
theorem lrSCoreT_app_botDemand {R : Readback} (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    {Γ : LCtx} {M M' A A₁ B₁ : Expr Nat} {g : List (List TypedModelAudit.CptT × TypedModelAudit.CptT)}
    (h : TypedModelAudit.LRSCoreT R E n Γ M M' A (.lam g))
    {s : List TypedModelAudit.CptT × TypedModelAudit.CptT} (hs : s ∈ g)
    (hbd : TypedModelAudit.BotDemandT s.1) (hA : RedR R Γ A (.pi A₁ B₁))
    {N N' : Expr Nat} (hN : HasTyT E n Γ N A₁) (hN' : HasTyT E n Γ N' A₁)
    (hc : Nonempty (ConvT E n Γ N N' A₁)) :
    TypedModelAudit.LRSCoreT R E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2 := by
  rw [TypedModelAudit.LRSCoreT.eq_def] at h
  obtain ⟨A₁₀, B₁₀, hpi₀, _hctx, hfn⟩ := h
  obtain ⟨eA, eB⟩ := TypedModelAudit.redR_pi_unique hL hNU hpi₀ hA
  subst eA; subst eB
  exact hfn s hs N N' hN hN' hc fun u hu => by
    rw [hbd u hu]; exact TypedModelAudit.lrSCoreT_bot _ _ _ _

/-- **Relation half, untyped relation (`LRSCore`)**: when the left argument reads back to the right
    one (the projection of a constructor to its field, `redR_projField_ctorMajor`), the λ clause's
    argument premise follows from the right argument's own diagonal at the step's demands. -/
theorem lrSCore_app_of_redR_arg {R : Readback} (hL : ReadbackLaws E R) (hNU : NormalUniqueR R)
    {Γ : LCtx} {M M' A A₁ B₁ : Expr Nat} {g : List (List CptI × CptI)}
    (h : LRSCore R E n Γ M M' A (.lam g)) {s : List CptI × CptI} (hs : s ∈ g)
    (hA : RedR R Γ A (.pi A₁ B₁))
    {N N' : Expr Nat} (hN : HasTyT E n Γ N A₁) (hN' : HasTyT E n Γ N' A₁)
    (hc : Nonempty (ConvT E n Γ N N' A₁)) (hred : RedR R Γ N N')
    (hdiag : ∀ u ∈ s.1, LRSCore R E n Γ N' N' A₁ u) :
    IsPropTyR R E n Γ (instantiate0 N B₁) ∨
      LRSCore R E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2 := by
  rw [LRSCore.eq_def] at h
  obtain ⟨A₁₀, B₁₀, _w, hpi₀, _hctx, _hB, hfn⟩ := h
  have e := hNU Γ hpi₀ (fun _ hs => hL.pi_normal _ _ _ _ hs) hA
    (fun _ hs => hL.pi_normal _ _ _ _ hs)
  injection e with eA eB
  subst eA; subst eB
  exact hfn s hs N N' hN hN' hc fun u hu =>
    lrSCore_expand hL hred (.refl _) u (hdiag u hu)

/-- The K reduct of `mixAnd` after the substitution `h ↦ intro a b x y`:
    `(λ x y. Sort 0 → Sort 0) (pr₁ (intro a b x y)) (pr₂ (intro a b x y))`. -/
def mixAndKRedSubst : Expr Nat := iotaRhsOf (kProjWitness mixAndW mixAndMkApp)

/-- Compacts of `mixAndMin x y` are `⊥` or `Π`-compacts whose parts are `⊥`/`sort`:
    two `approxI_app_inv` layers reach `mixAndMin`'s `lam` compact, whose body is the closed
    `mixPi`.  Used for both the K reduct and the ι reduct of the `mixAnd` control. -/
theorem approxI_mixAndMinApp_inv {ρ : EnvI} {x y : Expr Nat} {c : CptI}
    (h : ApproxI ρ (.app (.app mixAndMin x) y) c) :
    c = .bot ∨ ∃ a f, c = .pi a f ∧ (a = .bot ∨ a = .sort) ∧
      ∀ s ∈ f, s.2 = .bot ∨ s.2 = .sort := by
  rcases approxI_app_inv h with h0 | ⟨g, s, heq, hf, hsg, _⟩ | ⟨r, args, u, heq, hf, _⟩
  · exact Or.inl h0
  · subst heq
    rcases approxI_app_inv hf with h0 | ⟨g', s', heq', hf', hsg', _⟩ | ⟨r, args, u, heq', hf', _⟩
    · exact CptI.noConfusion h0
    · rcases approxI_lam_inv hf' with h0 | ⟨f', heq'', hb⟩
      · exact CptI.noConfusion h0
      · injection heq'' with hg'
        subst hg'
        have h2 := hb s' hsg'
        rw [← heq'] at h2
        rcases approxI_lam_inv h2 with h0 | ⟨f'', heq3, hb2⟩
        · exact CptI.noConfusion h0
        · injection heq3 with hf''
          subst hf''
          have h3 := hb2 s hsg
          rcases approxI_pi_inv h3 with h0 | ⟨a, f, heq4, hA, hB⟩
          · exact Or.inl h0
          · refine Or.inr ⟨a, f, heq4, ?_, ?_⟩
            · rcases approxI_sort_inv hA with h | h
              · exact Or.inl h
              · exact Or.inr h
            · intro s2 hs2
              rcases approxI_sort_inv (hB s2 hs2) with h | h
              · exact Or.inl h
              · exact Or.inr h
    · exact CptI.noConfusion heq'
  · rcases approxI_app_inv hf with h0 | ⟨g', s', heq', hf', hsg', _⟩ | ⟨r', args', u', heq', hf', _⟩
    · exact CptI.noConfusion h0
    · rcases approxI_lam_inv hf' with h0 | ⟨f', heq'', hb⟩
      · exact CptI.noConfusion h0
      · injection heq'' with hg'
        subst hg'
        have h2 := hb s' hsg'
        rw [← heq'] at h2
        rcases approxI_lam_inv h2 with h0 | ⟨f'', heq3, _⟩
        · exact CptI.noConfusion h0
        · exact CptI.noConfusion heq3
    · rcases approxI_lam_inv hf' with h0 | ⟨f', heq'', _⟩
      · exact CptI.noConfusion h0
      · exact CptI.noConfusion heq''

/-- **The bridge at the control**: the K reduct after the substitution and the ι reduct
    `(λ x y. Sort 0 → Sort 0) x y` are related at every compact of either, with the core. -/
theorem lrSCore_whStepCK_mixAnd_kι (c : CptI)
    (hc : ApproxI (ctxEnvI mixAndCtx) mixAndKRedSubst c ∨ ApproxI (ctxEnvI mixAndCtx) mixAndRhs c) :
    LRSCore (WhStepCK andEnvU) andEnvU 0 mixAndCtx mixAndKRedSubst mixAndRhs
      (.app mixAndMot mixAndMkApp) c := by
  have hredL : RedR (WhStepCK andEnvU) mixAndCtx mixAndKRedSubst mixPi :=
    .step (.ctx (.appHead (.beta _ _ _))) (.step (.ctx (.beta _ _ _)) (.refl _))
  have hredR : RedR (WhStepCK andEnvU) mixAndCtx mixAndRhs mixPi :=
    .step (.ctx (.appHead (.beta _ _ _))) (.step (.ctx (.beta _ _ _)) (.refl _))
  rcases hc with hc | hc <;>
    (have h2 : ApproxI (ctxEnvI mixAndCtx) (.app (.app mixAndMin _) _) c := hc
     rcases approxI_mixAndMinApp_inv h2 with rfl | ⟨a, f, rfl, ha, hf⟩
     · exact lrSCore_bot _ _ _ _
     · rw [LRSCore.eq_def]
       refine ⟨⟨.succ .zero, .step (.ctx (.beta _ _ _)) (.refl _)⟩,
         .sort .zero, .sort .zero, .sort .zero, .sort .zero, hredL, hredR,
         ⟨.assumption _ _ _ Rcic.Domain.Model.PiInversion.mixAndCtx_wf (.sort _ .zero)⟩,
         ⟨.refl _ _⟩, ⟨.refl _ _⟩, ⟨.succ .zero, ?_⟩, fun s hs _ _ _ _ _ _ => ⟨.zero, ?_⟩⟩
       · rcases ha with rfl | rfl
         · exact lrSCore_bot _ _ _ _
         · rw [LRSCore.eq_def]
           exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩
       · rcases hf s hs with h0 | h0
         · rw [h0]; exact lrSCore_bot _ _ _ _
         · rw [h0]
           show LRSCore (WhStepCK andEnvU) andEnvU 0 mixAndCtx
             (.sort .zero) (.sort .zero) (.sort .zero) .sort
           rw [LRSCore.eq_def]
           exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩)

/-- The `i`-th projection's motive at the `mixAnd` control (`projOne`'s `mot` subterm, so the
    ι-witness `preMajor` below is definitional). -/
def mixAndProjMotive (i : Nat) : Expr Nat :=
  let q := mixAndW.nindices
  let params := mixAndW.preMajor.take mixAndW.nparams
  let ctorTy := instantiateLevels mixAndW.ls mixAndW.ctorMember.mtype
  let famTy := instantiateLevels (famLevels mixAndW) mixAndW.famMember.mtype
  let prevM := projAll mixAndW i (params.map (lift 0 (q + 1))) (motIdx q) (.bvar 0)
  let ft := piDomOr (applyTel (params.map (lift 0 (q + 1)) ++ prevM) ctorTy)
  let motDoms := peelDomsOr q (applyTelOr params famTy) ++
    [foldApps (.const mixAndW.familyRef (famLevels mixAndW))
      (params.map (lift 0 q) ++ (List.range q).reverse.map Expr.bvar)]
  lamTel motDoms ft

/-- The `i`-th projection's minor at the `mixAnd` control (`projOne`'s `mn` subterm). -/
def mixAndProjMinor (i : Nat) : Expr Nat :=
  lamTel (peelDomsOr (fieldCount mixAndW)
    (applyTelOr (mixAndW.preMajor.take mixAndW.nparams)
      (instantiateLevels mixAndW.ls mixAndW.ctorMember.mtype)))
    (.bvar (fieldCount mixAndW - 1 - i))

/-- The ι witness of the `i`-th projection at the `mixAnd` control: the recursor at the
    proposition levels `[0]`, spine `params ++ [motᵢ, mnᵢ]`, minor `mnᵢ`, at the constructor
    major.  `iotaLhsOf` is `projOne`-shaped; `iotaRhsOf` is `mnᵢ` applied to the fields. -/
def mixAndProjW (i : Nat) : IotaWitness andEnvU :=
  { mixAndW with
    ls := projLevels mixAndW
    preMajor := mixAndW.preMajor.take mixAndW.nparams ++
      [mixAndProjMotive i, mixAndProjMinor i] ++
      mixAndW.preMajor.drop (mixAndW.nparams + 1 + mixAndW.nMinors)
    minor := mixAndProjMinor i
    hlsLen := rfl
    hpre := rfl
    hminor := rfl
    hctorAfter := rfl }

/-- ... and the projections of the constructor read back to its fields (the generic readback half
    at the control). -/
theorem redR_mixAnd_projs :
    RedR (WhStepCK andEnvU) mixAndCtx ((projFields mixAndW mixAndMkApp).getD 0 (.sort .zero)) (.bvar 2) ∧
      RedR (WhStepCK andEnvU) mixAndCtx ((projFields mixAndW mixAndMkApp).getD 1 (.sort .zero))
        (.bvar 1) := by
  refine ⟨?_, ?_⟩
  · exact .step (.ctx (.iota (.ofU (mixAndProjW 0))))
      (.step (.ctx (.appHead (.beta _ _ _))) (.step (.ctx (.beta _ _ _)) (.refl _)))
  · exact .step (.ctx (.iota (.ofU (mixAndProjW 1))))
      (.step (.ctx (.appHead (.beta _ _ _))) (.step (.ctx (.beta _ _ _)) (.refl _)))

/-! ### §7 — the index-agreement premise and its gap (admitted `Eq`, `eqEnvT`) -/

/-- `[h : Eq α a ((λ x : α. x) a), a : α, α : Sort 1]`: the index is convertible to the canon's
    (`a`) but not syntactically equal to it. -/
def eqGapCtx : LCtx :=
  [.assumption (foldApps (.const 63 []) [.bvar 1, .bvar 0, .app (.lam (.bvar 1) (.bvar 0)) (.bvar 0)]),
   .assumption (.bvar 0), .assumption (.sort (.succ .zero))]

/-- The motive `λ (b : α) (e : Eq α a b). Sort 1`, in `eqGapCtx`. -/
def eqGapMot : Expr Nat :=
  .lam (.bvar 2) (.lam (foldApps (.const 63 []) [.bvar 3, .bvar 2, .bvar 0]) (.sort (.succ .zero)))

/-- `Eq.rec.{2} α a (λ b e. Sort 1) (Sort 0) ((λ x. x) a) h`. -/
def eqGapRedex : Expr Nat :=
  recCall (.const 65 [.succ (.succ .zero)])
    [.bvar 2, .bvar 1, eqGapMot, .sort .zero, .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)] (.bvar 0)

/-- The legacy ι witness whose `preMajor` carries the redex's own index argument
    `(λ x. x) a` — a "junk" index `IotaWitness` allows, since nothing in the witness
    identifies it with the constructor's computed indices. -/
def eqGapW : IotaWitness eqEnvT where
  recRef := 65
  ctorRef := 64
  ls := [.succ (.succ .zero)]
  lsC := []
  recMember := eqRecT
  ctorMember := eqReflT
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.bvar 2, .bvar 1, eqGapMot, .sort .zero,
    .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)]
  fields := []
  ctorParams := [.bvar 2, .bvar 1]
  kinds := []
  minor := .sort .zero
  hlen := rfl
  familyRef := 63
  famMember := eqFamT
  hfam := rfl
  hfamK := rfl
  nparams := 2
  nindices := 1
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.sort (.succ .zero), .bvar 0]
  ctorResult := foldApps (.const 63 []) [.bvar 1, .bvar 0, .bvar 0]
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.sort (.succ .zero), .bvar 0, eqMotT, eqMinorT, .bvar 3,
    foldApps (.const 63 []) [.bvar 4, .bvar 3, .bvar 0]]
  recBody := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 1]
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

theorem eqGapCtx_wf (n : Nat) : Nonempty (CtxWfT eqEnvT n eqGapCtx) := by
  have hAα : HasTyT eqEnvT n [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort _ _
  have hΓα : CtxWfT eqEnvT n [.assumption (.sort (.succ .zero))] :=
    .assumption _ _ _ .nil hAα
  have hAa : HasTyT eqEnvT n [.assumption (.sort (.succ .zero))] (.bvar 0)
      (.sort (.succ .zero)) :=
    .bvar _ 0 _ rfl
  have hΓa : CtxWfT eqEnvT n [.assumption (.bvar 0), .assumption (.sort (.succ .zero))] :=
    .assumption _ _ _ hΓα hAa
  have hα : HasTyT eqEnvT n [.assumption (.bvar 0), .assumption (.sort (.succ .zero))]
      (.bvar 1) (.sort (.succ .zero)) := .bvar _ 1 _ rfl
  have ha : HasTyT eqEnvT n [.assumption (.bvar 0), .assumption (.sort (.succ .zero))]
      (.bvar 0) (.bvar 1) := .bvar _ 0 _ rfl
  have tIdx : HasTyT eqEnvT n [.assumption (.bvar 0), .assumption (.sort (.succ .zero))]
      (.app (.lam (.bvar 1) (.bvar 0)) (.bvar 0)) (.bvar 1) :=
    .app _ _ _ _ _
      (.lam _ _ _ _ _
        (.bvar [.assumption (.bvar 0), .assumption (.sort (.succ .zero))] 1 _ rfl)
        (.bvar (.assumption (.bvar 1) :: [.assumption (.bvar 0),
            .assumption (.sort (.succ .zero))]) 0 _ rfl))
      (.bvar [.assumption (.bvar 0), .assumption (.sort (.succ .zero))] 0 _ rfl)
  have hAh : HasTyT eqEnvT n [.assumption (.bvar 0), .assumption (.sort (.succ .zero))]
      (foldApps (.const 63 []) [.bvar 1, .bvar 0,
        .app (.lam (.bvar 1) (.bvar 0)) (.bvar 0)]) (.sort .zero) :=
    .app _ _ _ _ _ (.app _ _ _ _ _ (.app _ _ _ _ _
      (.const _ 63 [] eqFamT rfl rfl rfl) hα) ha) tIdx
  exact ⟨.assumption _ _ _ hΓa hAh⟩

/-- The conversion exists: `Eq α a ((λx.x) a) ≡ Eq α a a`, so `h ≡ refl α a` by irrelevance, then ι
    (the legacy witness at the redex's own index argument). -/
theorem eqGap_conv (n : Nat) :
    Nonempty (ConvT eqEnvT n eqGapCtx (.sort .zero) eqGapRedex (.sort (.succ .zero))) := by
  have hα : HasTyT eqEnvT n eqGapCtx (.bvar 2) (.sort (.succ .zero)) :=
    .bvar eqGapCtx 2 _ rfl
  have ha : HasTyT eqEnvT n eqGapCtx (.bvar 1) (.bvar 2) := .bvar eqGapCtx 1 _ rfl
  have tH : HasTyT eqEnvT n eqGapCtx (.bvar 0)
      (foldApps (.const 63 []) [.bvar 2, .bvar 1,
        .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)]) := .bvar eqGapCtx 0 _ rfl
  have tIdx : HasTyT eqEnvT n eqGapCtx
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) (.bvar 2) :=
    .app _ _ _ _ _ (.lam _ _ _ _ _ hα
      (.bvar (.assumption (.bvar 2) :: eqGapCtx) 0 _ rfl)) ha
  have hX : HasTyT eqEnvT n eqGapCtx
      (foldApps (.const 63 []) [.bvar 2, .bvar 1,
        .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)]) (.sort .zero) :=
    .app _ _ _ _ _ (.app _ _ _ _ _ (.app _ _ _ _ _
      (.const _ 63 [] eqFamT rfl rfl rfl) hα) ha) tIdx
  have hAA : HasTyT eqEnvT n eqGapCtx
      (foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 1]) (.sort .zero) :=
    .app _ _ _ _ _ (.app _ _ _ _ _ (.app _ _ _ _ _
      (.const _ 63 [] eqFamT rfl rfl rfl) hα) ha) ha
  have hAx : HasTyT eqEnvT n (.assumption (.bvar 2) :: eqGapCtx)
      (foldApps (.const 63 []) [.bvar 3, .bvar 2, .bvar 0]) (.sort .zero) :=
    .app _ _ _ _ _ (.app _ _ _ _ _ (.app _ _ _ _ _
      (.const _ 63 [] eqFamT rfl rfl rfl)
      (.bvar (.assumption (.bvar 2) :: eqGapCtx) 3 _ rfl))
      (.bvar (.assumption (.bvar 2) :: eqGapCtx) 2 _ rfl))
      (.bvar (.assumption (.bvar 2) :: eqGapCtx) 0 _ rfl)
  have tyInner : HasTyT eqEnvT n (.assumption (.bvar 2) :: eqGapCtx)
      (.lam (foldApps (.const 63 []) [.bvar 3, .bvar 2, .bvar 0]) (.sort (.succ .zero)))
      (.pi (foldApps (.const 63 []) [.bvar 3, .bvar 2, .bvar 0])
        (.sort (.succ (.succ .zero)))) :=
    .lam _ _ _ _ _ hAx (.sort _ _)
  have tyMot : HasTyT eqEnvT n eqGapCtx eqGapMot
      (.pi (.bvar 2) (.pi (foldApps (.const 63 []) [.bvar 3, .bvar 2, .bvar 0])
        (.sort (.succ (.succ .zero))))) :=
    .lam _ _ _ _ _ hα tyInner
  have tRefl : HasTyT eqEnvT n eqGapCtx
      (foldApps (.const 64 []) [.bvar 2, .bvar 1])
      (foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 1]) :=
    .app _ _ _ _ _ (.app _ _ _ _ _
      (.const _ 64 [] eqReflT rfl rfl rfl) hα) ha
  have cIdx : ConvT eqEnvT n eqGapCtx
      (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)) (.bvar 1) (.bvar 2) :=
    .beta _ _ _ _ _ _ hα
      (.bvar (.assumption (.bvar 2) :: eqGapCtx) 0 _ rfl) ha
  have cEq : ConvT eqEnvT n eqGapCtx
      (foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 1])
      (foldApps (.const 63 []) [.bvar 2, .bvar 1,
        .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)]) (.sort .zero) := by
    refine .app _ _ _ _ _ _ _
      (.app _ _ _ _ _ _ _ (.app _ _ _ _ _ _ _
        (.refl _ _ _ (.const _ 63 [] eqFamT rfl rfl rfl)) (.refl _ _ _ hα))
        (.refl _ _ _ ha)) ?_
    exact .symm _ _ _ _ cIdx
  have tyMajorR : HasTyT eqEnvT n eqGapCtx
      (foldApps (.const 64 []) [.bvar 2, .bvar 1])
      (foldApps (.const 63 []) [.bvar 2, .bvar 1,
        .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)]) :=
    .conv _ _ _ _ _ tRefl cEq
  have cIrr : ConvT eqEnvT n eqGapCtx (.bvar 0)
      (foldApps (.const 64 []) [.bvar 2, .bvar 1])
      (foldApps (.const 63 []) [.bvar 2, .bvar 1,
        .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)]) :=
    .irr _ _ _ _ hX tH tyMajorR
  have cMin1 : ConvT eqEnvT n eqGapCtx
      (.app eqGapMot (.bvar 1))
      (.lam (foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 1]) (.sort (.succ .zero)))
      (.pi (foldApps (.const 63 []) [.bvar 2, .bvar 1, .bvar 1])
        (.sort (.succ (.succ .zero)))) :=
    .beta _ _ _ _ _ _ hα tyInner ha
  have cMinR : ConvT eqEnvT n eqGapCtx
      (.app (.app eqGapMot (.bvar 1)) (foldApps (.const 64 []) [.bvar 2, .bvar 1]))
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := by
    refine .trans _ _ _ _ _
      (.app _ _ _ _ _ _ _ cMin1 (.refl _ _ _ tRefl)) ?_
    exact .beta _ _ _ _ _ _ hAA (.sort _ _) tRefl
  have tyMin : HasTyT eqEnvT n eqGapCtx (.sort .zero)
      (.app (.app eqGapMot (.bvar 1)) (foldApps (.const 64 []) [.bvar 2, .bvar 1])) :=
    .conv _ _ _ _ _ (.sort _ _) (.symm _ _ _ _ cMinR)
  have cMin2 : ConvT eqEnvT n eqGapCtx
      (.app eqGapMot (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)))
      (.lam (foldApps (.const 63 []) [.bvar 2, .bvar 1,
        .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)]) (.sort (.succ .zero)))
      (.pi (foldApps (.const 63 []) [.bvar 2, .bvar 1,
        .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)])
        (.sort (.succ (.succ .zero)))) :=
    .beta _ _ _ _ _ _ hα tyInner tIdx
  have cRes : ConvT eqEnvT n eqGapCtx
      (.app (.app eqGapMot (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1))) (.bvar 0))
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := by
    refine .trans _ _ _ _ _
      (.app _ _ _ _ _ _ _ cMin2 (.refl _ _ _ tH)) ?_
    exact .beta _ _ _ _ _ _ hX (.sort _ _) tH
  have cResR : ConvT eqEnvT n eqGapCtx
      (.app (.app eqGapMot (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)))
        (foldApps (.const 64 []) [.bvar 2, .bvar 1]))
      (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := by
    refine .trans _ _ _ _ _
      (.app _ _ _ _ _ _ _ cMin2 (.refl _ _ _ tyMajorR)) ?_
    exact .beta _ _ _ _ _ _ hX (.sort _ _) tyMajorR
  have t5 : HasTyT eqEnvT n eqGapCtx
      (foldApps (.const 65 [.succ (.succ .zero)])
        [.bvar 2, .bvar 1, eqGapMot, .sort .zero,
          .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)]) _ :=
    .app _ _ _ _ _ (.app _ _ _ _ _ (.app _ _ _ _ _ (.app _ _ _ _ _
      (.app _ _ _ _ _ (.const _ 65 [.succ (.succ .zero)] eqRecT rfl rfl rfl) hα)
      ha) tyMot) tyMin) tIdx
  have hlι : HasTyT eqEnvT n eqGapCtx (iotaLhsOf eqGapW) (.sort (.succ .zero)) :=
    .conv _ _ _ _ _ (.app _ _ _ _ _ t5 tyMajorR) cResR
  have cAp : ConvT eqEnvT n eqGapCtx eqGapRedex (iotaLhsOf eqGapW)
      (.app (.app eqGapMot (.app (.lam (.bvar 2) (.bvar 0)) (.bvar 1))) (.bvar 0)) := by
    refine .app _ _ _ _ _ _ _ (.refl _ _ _ t5) ?_
    exact cIrr
  have cApT : ConvT eqEnvT n eqGapCtx eqGapRedex (iotaLhsOf eqGapW) (.sort (.succ .zero)) :=
    .tyConv _ _ _ _ _ _ cAp cRes
  have ciota : ConvT eqEnvT n eqGapCtx (iotaLhsOf eqGapW) (.sort .zero)
      (.sort (.succ .zero)) :=
    .iota _ _ _ _ (.of eqGapW) hlι (.sort _ _)
  exact ⟨.symm _ _ _ _ (.trans _ _ _ _ _ cApT ciota)⟩

/-- Auxiliary induction for `whStepCK_eqGapRedex_false`: pins the witness arithmetic of any
    `WhStepCK` step whose source is the Eq-gap redex, then discharges the `hidx` premise by
    `decide`. -/
theorem whStepCK_eqGapRedex_false_aux {Γ : LCtx} {a e : Expr Nat}
    (h : WhStepCK eqEnvT Γ a e) : a = eqGapRedex → False := by
  induction h with
  | ctx hs =>
      intro heq; subst heq
      exact whStepCtx_recCall_nonCtorMajor_aux pinEqGroupWfT hs (w := eqGapW) rfl
        not_isCtorSpine_bvar
  | kStar hK hnc hidx =>
      rename_i w x
      intro heq
      rw [eqGapRedex, recCall_eq_app] at heq
      injection heq with hf _
      have hf2 : foldApps (.const w.recRef w.ls) w.preMajor =
          foldApps (.const 65 [.succ (.succ .zero)])
            [.bvar 2, .bvar 1, eqGapMot, .sort .zero,
              .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)] := hf
      obtain ⟨hconst, hargs⟩ := foldApps_const_inj hf2
      injection hconst with hrr hll
      have hnM : w.nMinors = 1 := hK.2.1
      have hrecM : w.recMember = eqRecT :=
        Option.some.inj (w.hrec.symm.trans (hrr.symm ▸ (rfl : eqEnvT.members 65 = some eqRecT)))
      have hfr : w.familyRef = 63 := by
        have := w.hrecIdx; rw [hrr, hnM] at this; omega
      have hfamM : w.famMember = eqFamT :=
        Option.some.inj (w.hfam.symm.trans (hfr.symm ▸ (rfl : eqEnvT.members 63 = some eqFamT)))
      have hcIdx : w.ctorIdx = 0 := Nat.lt_one_iff.mp (hnM ▸ w.hidx)
      have hcr : w.ctorRef = 64 := by
        have := w.hctorIdx; rw [hfr, hcIdx] at this; omega
      have hctorM : w.ctorMember = eqReflT :=
        Option.some.inj (w.hctor.symm.trans (hcr.symm ▸ (rfl : eqEnvT.members 64 = some eqReflT)))
      have hnp : w.nparams = 2 := by
        have e2 := w.hnpar; rw [hctorM, hK.1, List.length_nil] at e2
        rw [show piCount eqReflT.mtype = 2 from rfl] at e2
        omega
      have hidx' := hidx
      unfold redexIdx resultIdxAt at hidx'
      rw [hargs, hnp, hnM, hctorM, hll] at hidx'
      exact absurd hidx' (by decide)
  | kProj hK hnc hf hidx =>
      rename_i w x
      intro heq
      rw [eqGapRedex, recCall_eq_app] at heq
      injection heq with hf3 hx
      subst hx
      have hf2 : foldApps (.const w.recRef w.ls) w.preMajor =
          foldApps (.const 65 [.succ (.succ .zero)])
            [.bvar 2, .bvar 1, eqGapMot, .sort .zero,
              .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)] := hf3
      obtain ⟨hconst, hargs⟩ := foldApps_const_inj hf2
      injection hconst with hrr hll
      have hnM : w.nMinors = 1 := hK.2.1
      have hrecM : w.recMember = eqRecT :=
        Option.some.inj (w.hrec.symm.trans (hrr.symm ▸ (rfl : eqEnvT.members 65 = some eqRecT)))
      have hfr : w.familyRef = 63 := by
        have := w.hrecIdx; rw [hrr, hnM] at this; omega
      have hfamM : w.famMember = eqFamT :=
        Option.some.inj (w.hfam.symm.trans (hfr.symm ▸ (rfl : eqEnvT.members 63 = some eqFamT)))
      have hcIdx : w.ctorIdx = 0 := Nat.lt_one_iff.mp (hnM ▸ w.hidx)
      have hcr : w.ctorRef = 64 := by
        have := w.hctorIdx; rw [hfr, hcIdx] at this; omega
      have hctorM : w.ctorMember = eqReflT :=
        Option.some.inj (w.hctor.symm.trans (hcr.symm ▸ (rfl : eqEnvT.members 64 = some eqReflT)))
      have hpf : w.nparams + w.fields.length = 2 := by
        have e2 := w.hnpar; rw [hctorM] at e2
        rw [show piCount eqReflT.mtype = 2 from rfl] at e2
        exact e2
      have hlit : peelPis 2 eqReflT.mtype =
          some ([.sort (.succ .zero), .bvar 0],
            foldApps (.const 63 []) [.bvar 1, .bvar 0, .bvar 0]) := rfl
      obtain ⟨hd, hr⟩ := Prod.mk.inj (Option.some.inj
        (hlit.symm.trans (hctorM ▸ hpf ▸ w.hpeel)))
      have hpos : 1 ≤ w.fields.length :=
        Nat.pos_iff_ne_zero.mpr
          (fun h0 => hK.1 (List.length_eq_zero.mp h0))
      have hnp01 : w.nparams = 0 ∨ w.nparams = 1 := by omega
      rcases hnp01 with hnp | hnp
      · have hfc : fieldCount w = 2 := by
          unfold fieldCount; rw [hctorM, hnp]; decide
        have hrv0 : revealedPos? w 0 = some 0 := by
          unfold revealedPos? fieldCount
          rw [← hr, hctorM, hnp]; decide
        have hrv1 : revealedPos? w 1 = some 1 := by
          unfold revealedPos? fieldCount
          rw [← hr, hctorM, hnp]; decide
        have hproj : projFields w (.bvar 0) = [eqGapMot, .sort .zero] := by
          unfold projFields
          rw [hfc]
          simp only [projAll, canonField]
          rw [hargs, hnp, hnM, hrv0, hrv1]
          rfl
        have hidx' := hidx
        unfold redexIdx resultIdxAt at hidx'
        rw [hargs, hnp, hnM, hctorM, hll, hproj] at hidx'
        exact absurd hidx' (by decide)
      · have hfc : fieldCount w = 1 := by
          unfold fieldCount; rw [hctorM, hnp]; decide
        have hrv0 : revealedPos? w 0 = some 0 := by
          unfold revealedPos? fieldCount
          rw [← hr, hctorM, hnp]; decide
        have hproj : projFields w (.bvar 0) = [.sort .zero] := by
          unfold projFields
          rw [hfc]
          simp only [projAll, canonField]
          rw [hargs, hnp, hnM, hrv0]
          rfl
        have hidx' := hidx
        unfold redexIdx resultIdxAt at hidx'
        rw [hargs, hnp, hnM, hctorM, hll, hproj] at hidx'
        exact absurd hidx' (by decide)
  | recMajor hm' hrec' hlen' hnK hnP hs' =>
      intro heq
      rw [eqGapRedex, recCall_eq_app] at heq
      injection heq with hf' _
      have hf2 : foldApps (.const _ _) _ =
          foldApps (.const 65 [.succ (.succ .zero)])
            [.bvar 2, .bvar 1, eqGapMot, .sort .zero,
              .app (.lam (.bvar 2) (.bvar 0)) (.bvar 1)] := hf'
      obtain ⟨hconst, _⟩ := foldApps_const_inj hf2
      injection hconst with hrr _
      exact hnK (hrr.symm ▸ ⟨eqGapW, rfl, rfl, rfl, rfl⟩)
  | appHead hf ih =>
      intro heq
      rw [eqGapRedex, recCall_eq_app] at heq
      injection heq with hf' _
      rename_i f g y
      exact whStepCK_recPrefix_false pinEqGroupWfT
        (rfl : eqEnvT.members 65 = some eqRecT) rfl _
        (by decide) _ (hf' ▸ hf)

/-- ... but the core is stuck: the index-agreement premise fails syntactically, the K recursor
    does not reduce its major, and no other arm applies. -/
theorem whStepCK_eqGapRedex_false {e : Expr Nat} :
    ¬ WhStepCK eqEnvT eqGapCtx eqGapRedex e :=
  fun h => whStepCK_eqGapRedex_false_aux h rfl

/-- Every `RedR`-reduct of the gap redex is the redex itself. -/
theorem whRedCK_eqGapRedex_eq {e : Expr Nat}
    (h : RedR (WhStepCK eqEnvT) eqGapCtx eqGapRedex e) : e = eqGapRedex := by
  cases h with
  | refl => rfl
  | step hs _ => exact (whStepCK_eqGapRedex_false hs).elim

/-- **The convertible-indices gap, kernel-real**: the chain form fails for the core at the admitted
    `Eq` environment.  (The alternative premise — a common type of major and canon in `Γ` — closes
    this point but makes `NormalR` of a stuck K redex a negative typing statement, i.e. family-
    application injectivity, the `famAppRow` being proved; so the core keeps the syntactic check
    and this is the named gap.) -/
theorem not_fundamentalLRST_whStepCK_eqEnvT (n : Nat) :
    ¬ FundamentalLRST (WhStepCK eqEnvT) eqEnvT n := by
  intro F
  obtain ⟨ctx⟩ := eqGapCtx_wf n
  obtain ⟨cv⟩ := eqGap_conv n
  have h := F ctx (.sort _ .zero) (.of _ _ _ _ cv) .sort (.sort _ .zero)
  rw [LRSCore.eq_def] at h
  obtain ⟨_, _, u', _, hr⟩ := h
  exact Expr.noConfusion (whRedCK_eqGapRedex_eq hr)

/-- Control: at syntactically agreeing indices (`h : Eq α a a`) the K step fires. -/
def eqAgreeCtx : LCtx :=
  [.assumption (foldApps (.const 63 []) [.bvar 1, .bvar 0, .bvar 0]),
   .assumption (.bvar 0), .assumption (.sort (.succ .zero))]

/-- The agreeing-index sibling of `eqGapW`: same witness, index argument `a`. -/
def eqAgreeW : IotaWitness eqEnvT :=
  { eqGapW with
    preMajor := [.bvar 2, .bvar 1, eqGapMot, .sort .zero, .bvar 1]
    hpre := rfl
    hminor := rfl }

theorem whStepCK_eqAgree :
    WhStepCK eqEnvT eqAgreeCtx
      (recCall (.const 65 [.succ (.succ .zero)]) [.bvar 2, .bvar 1, eqGapMot, .sort .zero, .bvar 1]
        (.bvar 0))
      (.sort .zero) := by
  have hidx : redexIdx eqAgreeW =
      resultIdxAt eqAgreeW (eqAgreeW.preMajor.take eqAgreeW.nparams) [] := rfl
  exact .kStar (w := eqAgreeW) ⟨rfl, rfl, rfl⟩ not_isCtorSpine_bvar hidx

/-! ### §8 — higher-order recursive fields (Acc-like): no ι witness, hence no K point -/

/-- `analyzeFields` succeeds pointwise: each field domain has an `analyzeField` verdict. -/
theorem analyzeFields_some_elem {fam : Nat} {Ts : List (Expr Nat)} {ks : List RecKind}
    {j : Nat} {T : Expr Nat} (h : analyzeFields fam Ts = some ks) (hj : Ts[j]? = some T) :
    ∃ k, analyzeField fam T = some k := by
  induction Ts generalizing ks j with
  | nil => exact Option.noConfusion hj
  | cons T0 Ts ih =>
      unfold analyzeFields at h
      cases ha : analyzeField fam T0 with
      | none => rw [ha] at h; exact Option.noConfusion h
      | some k0 =>
          cases hrest : analyzeFields fam Ts with
          | none => rw [ha, hrest] at h; exact Option.noConfusion h
          | some ks' =>
              rw [ha, hrest] at h
              obtain rfl := (Option.some.inj h).symm
              cases j with
              | zero =>
                  rw [List.getElem?_cons_zero] at hj
                  obtain rfl := Option.some.inj hj
                  exact ⟨k0, ha⟩
              | succ j =>
                  rw [List.getElem?_cons_succ] at hj
                  exact ih hrest hj

/-- A successful `peelPis` has every shorter peel successful at the domain prefix. -/
theorem peelPis_prefix : ∀ {n : Nat} {T : Expr Nat} {ds : List (Expr Nat)} {r : Expr Nat}
    {n' : Nat}, peelPis n T = some (ds, r) → n' ≤ n →
    ∃ r', peelPis n' T = some (ds.take n', r') := by
  intro n
  induction n with
  | zero =>
      intro T ds r n' h hn
      obtain rfl : n' = 0 := Nat.eq_zero_of_le_zero hn
      exact ⟨T, rfl⟩
  | succ m ih =>
      intro T ds r n' h hn
      cases n' with
      | zero => exact ⟨T, rfl⟩
      | succ n' =>
          cases T with
          | pi A B =>
              unfold peelPis at h
              cases hB : peelPis m B with
              | none => rw [hB] at h; exact Option.noConfusion h
              | some p =>
                  obtain ⟨ds0, r0⟩ := p
                  rw [hB] at h
                  obtain ⟨hd, hr⟩ := Prod.mk.inj (Option.some.inj h)
                  subst hd; subst hr
                  obtain ⟨r', h'⟩ := ih hB (Nat.le_of_succ_le_succ hn)
                  refine ⟨r', ?_⟩
                  rw [List.take_succ_cons]
                  unfold peelPis
                  rw [h']
          | bvar i => exact Option.noConfusion h
          | sort l => exact Option.noConfusion h
          | const r0 ls => exact Option.noConfusion h
          | app f x => exact Option.noConfusion h
          | lam A b => exact Option.noConfusion h
          | letE A v b => exact Option.noConfusion h
          | lit t => exact Option.noConfusion h

/-- **Every ι witness has first-order fields**: a field domain mentioning the family is a family
    application (`analyzeField` refuses anything else, `hkinds`). -/
theorem iotaWitness_fields_firstOrder (w : IotaWitness E) {j : Nat} {T : Expr Nat}
    (hj : (w.ctorDoms.drop w.nparams)[j]? = some T) (hocc : occursConst w.familyRef T = true) :
    isFamilyApp w.familyRef T = true := by
  obtain ⟨k, hk⟩ := analyzeFields_some_elem w.hkinds hj
  unfold analyzeField at hk
  split at hk
  · rename_i hC
    rw [hocc] at hC
    exact Bool.noConfusion hC
  · rename_i hC
    split at hk
    · rename_i h2
      exact h2
    · exact Option.noConfusion hk

/-- Hence a constructor with a higher-order recursive field (as `Acc.intro`'s
    `Π y, r y x → Acc r y`) is the constructor of no ι witness: neither legacy ι nor `kStar`/`kProj`
    ever fires for it, and `ConvT.iota` (legacy witnesses only) never unfolds its recursor — so
    there is no W-K point to cover. -/
theorem not_iotaWitness_of_higherOrderField {c fam : Nat} {cm : CheckedMember}
    (hc : E.members c = some cm) {p : Nat} {T : Expr Nat}
    (hT : (peelDomsOr (p + 1) cm.mtype)[p]? = some T)
    (hocc : occursConst fam T = true) (hfam : isFamilyApp fam T = false) :
    ∀ w : IotaWitness E, w.ctorRef = c → w.familyRef = fam → w.nparams ≤ p →
      p < w.nparams + w.fields.length → False := by
  intro w hcr hfr hle hlt
  have hm : cm = w.ctorMember :=
    Option.some.inj (hc.symm.trans (hcr ▸ w.hctor))
  have hpeel : peelPis (w.nparams + w.fields.length) cm.mtype =
      some (w.ctorDoms, w.ctorResult) := hm ▸ w.hpeel
  obtain ⟨r', hpeel'⟩ := peelPis_prefix hpeel (Nat.succ_le_of_lt hlt)
  have hdom : peelDomsOr (p + 1) cm.mtype = w.ctorDoms.take (p + 1) := by
    unfold peelDomsOr; rw [hpeel']
  rw [hdom, List.getElem?_take, if_pos (Nat.lt_succ_self p)] at hT
  have hj : (w.ctorDoms.drop w.nparams)[p - w.nparams]? = some T := by
    rw [List.getElem?_drop, Nat.add_sub_cancel' hle]
    exact hT
  rw [← hfr] at hocc
  have hr := iotaWitness_fields_firstOrder w hj hocc
  rw [hfr] at hr
  rw [hr] at hfam
  exact Bool.noConfusion hfam

/-- The hypotheses are met by a higher-order recursive proposition singleton's constructor,
    `mk : (Prop → W) → W` (the field `Π (_ : Sort 0), W` mentions `W` and is not a `W`
    application; positivity admits it as `FieldShape.recursive 1`, and it is `FieldSafe` as a
    proposition, so the family would get large elimination). -/
def hoMkTy : Expr Nat := .pi (.pi (.sort .zero) (.const 0 [])) (.const 0 [])

theorem hoMkTy_field :
    (peelDomsOr 1 hoMkTy)[0]? = some (.pi (.sort .zero) (.const 0 [])) ∧
      occursConst 0 (.pi (.sort .zero) (.const 0 [])) = true ∧
      isFamilyApp 0 (.pi (.sort .zero) (.const 0 [])) = false :=
  ⟨rfl, rfl, rfl⟩

/-! ### §9 — first-order recursive proposition singletons: the admitted `Loop` -/

/-- The `Loop` ι witness (`Loop : Prop`, `mk : Loop → Loop`, the AnySort recursor at 62) at
    major `x`, motive `λ _. Sort 1`, minor `λ (y : Loop) (ih : Sort 1). Sort 0`. -/
def loopMot : Expr Nat := .lam (.const 60 []) (.sort (.succ .zero))

def loopMin : Expr Nat := .lam (.const 60 []) (.lam (.sort (.succ .zero)) (.sort .zero))

def loopKRedex (x : Expr Nat) : Expr Nat :=
  recCall (.const 62 [.succ (.succ .zero)]) [loopMot, loopMin] x

/-- `[h : Loop]`. -/
def loopCtx : LCtx := [.assumption (.const 60 [])]

def loopW : IotaWitness pinLoopEnvT where
  recRef := 62
  ctorRef := 61
  ls := [.succ (.succ .zero)]
  lsC := []
  recMember := pinLoopRecT
  ctorMember := pinLoopMkT
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [loopMot, loopMin]
  fields := [.bvar 0]
  ctorParams := []
  kinds := [.directRec]
  minor := loopMin
  hlen := rfl
  familyRef := 60
  famMember := pinLoopFamT
  hfam := rfl
  hfamK := rfl
  nparams := 0
  nindices := 0
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.const 60 []]
  ctorResult := .const 60 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.pi (.const 60 []) (.sort (.param 0)),
    .pi (.const 60 [])
      (.pi (.app (.bvar 1) (.bvar 0))
        (.app (.bvar 2) (.app (.const 61 []) (.bvar 1)))),
    .const 60 []]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .pi (.const 60 []) (.const 60 [])
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

theorem kfieldW_loopW : KFieldW loopW :=
  ⟨fun h => List.noConfusion h, rfl, rfl, rfl⟩

/-- **One K step = one unfolding**: `Loop.rec M m h ↝ m (pr h) (Loop.rec M m (pr h)) ↝↝ Sort 0`,
    the recursive call in argument position. -/
theorem redR_whStepCK_loopKRedex :
    RedR (WhStepCK pinLoopEnvT) loopCtx (loopKRedex (.bvar 0)) (.sort .zero) := by
  exact .step (whStepCK_kProj_of kfieldW_loopW not_isCtorSpine_bvar rfl)
    (.step (.ctx (.appHead (.beta _ _ _)))
      (.step (.ctx (.beta _ _ _)) (.refl _)))

/-- The conversion: `h ≡ mk h` by irrelevance, ι, two β. -/
theorem loopK_conv (n : Nat) :
    Nonempty (ConvT pinLoopEnvT n loopCtx (.sort .zero) (loopKRedex (.bvar 0)) (.sort (.succ .zero))) := by
  have hL : HasTyT pinLoopEnvT n loopCtx (.const 60 []) (.sort .zero) :=
    .const _ 60 [] pinLoopFamT rfl rfl rfl
  have tyH : HasTyT pinLoopEnvT n loopCtx (.bvar 0) (.const 60 []) := .bvar _ 0 _ rfl
  have tyMkH : HasTyT pinLoopEnvT n loopCtx (.app (.const 61 []) (.bvar 0)) (.const 60 []) :=
    .app _ _ _ _ _ (.const _ 61 [] pinLoopMkT rfl rfl rfl) tyH
  have tMot : HasTyT pinLoopEnvT n loopCtx loopMot
      (.pi (.const 60 []) (.sort (.succ (.succ .zero)))) :=
    .lam _ _ _ _ _ hL (.sort _ _)
  have tMinD : HasTyT pinLoopEnvT n loopCtx loopMin
      (.pi (.const 60 []) (.pi (.sort (.succ .zero)) (.sort (.succ .zero)))) :=
    .lam _ _ _ _ _ hL (.lam _ _ _ _ _ (.sort _ _) (.sort _ _))
  have hLy : HasTyT pinLoopEnvT n (.assumption (.const 60 []) :: loopCtx)
      (.const 60 []) (.sort .zero) := .const _ 60 [] pinLoopFamT rfl rfl rfl
  have cMy : ConvT pinLoopEnvT n (.assumption (.const 60 []) :: loopCtx)
      (.sort (.succ .zero)) (.app loopMot (.bvar 0)) (.sort (.succ (.succ .zero))) :=
    .symm _ _ _ _ (.beta _ _ _ _ _ _ hLy (.sort _ _) (.bvar _ 0 _ rfl))
  have hLi : HasTyT pinLoopEnvT n
      (.assumption (.sort (.succ .zero)) :: .assumption (.const 60 []) :: loopCtx)
      (.const 60 []) (.sort .zero) := .const _ 60 [] pinLoopFamT rfl rfl rfl
  have tyMkY : HasTyT pinLoopEnvT n
      (.assumption (.sort (.succ .zero)) :: .assumption (.const 60 []) :: loopCtx)
      (.app (.const 61 []) (.bvar 1)) (.const 60 []) :=
    .app _ _ _ _ _ (.const _ 61 [] pinLoopMkT rfl rfl rfl) (.bvar _ 1 _ rfl)
  have cMmk : ConvT pinLoopEnvT n
      (.assumption (.sort (.succ .zero)) :: .assumption (.const 60 []) :: loopCtx)
      (.sort (.succ .zero)) (.app loopMot (.app (.const 61 []) (.bvar 1)))
      (.sort (.succ (.succ .zero))) :=
    .symm _ _ _ _ (.beta _ _ _ _ _ _ hLi (.sort _ _) tyMkY)
  have cMinT : ConvT pinLoopEnvT n loopCtx
      (.pi (.const 60 []) (.pi (.sort (.succ .zero)) (.sort (.succ .zero))))
      (.pi (.const 60 [])
        (.pi (.app loopMot (.bvar 0)) (.app loopMot (.app (.const 61 []) (.bvar 1)))))
      (.sort _) :=
    .pi _ _ _ _ _ _ _ (.refl _ _ _ hL) (.pi _ _ _ _ _ _ _ cMy cMmk)
  have tMin : HasTyT pinLoopEnvT n loopCtx loopMin
      (.pi (.const 60 [])
        (.pi (.app loopMot (.bvar 0)) (.app loopMot (.app (.const 61 []) (.bvar 1))))) :=
    .conv _ _ _ _ _ tMinD cMinT
  have t2 : HasTyT pinLoopEnvT n loopCtx
      (foldApps (.const 62 [.succ (.succ .zero)]) [loopMot, loopMin])
      (.pi (.const 60 []) (.app loopMot (.bvar 0))) :=
    .app _ _ _ _ _ (.app _ _ _ _ _
      (.const _ 62 [.succ (.succ .zero)] pinLoopRecT rfl rfl rfl) tMot) tMin
  have cRes : ConvT pinLoopEnvT n loopCtx (.app loopMot (.bvar 0)) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) :=
    .beta _ _ _ _ _ _ hL (.sort _ _) tyH
  have cResMk : ConvT pinLoopEnvT n loopCtx
      (.app loopMot (.app (.const 61 []) (.bvar 0))) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) :=
    .beta _ _ _ _ _ _ hL (.sort _ _) tyMkH
  have hlhs : HasTyT pinLoopEnvT n loopCtx (loopKRedex (.bvar 0)) (.sort (.succ .zero)) :=
    .conv _ _ _ _ _ (.app _ _ _ _ _ t2 tyH) cRes
  have hlι : HasTyT pinLoopEnvT n loopCtx (iotaLhsOf loopW) (.sort (.succ .zero)) :=
    .conv _ _ _ _ _ (.app _ _ _ _ _ t2 tyMkH) cResMk
  have tMinIh : HasTyT pinLoopEnvT n (.assumption (.const 60 []) :: loopCtx)
      (.lam (.sort (.succ .zero)) (.sort .zero))
      (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .lam _ _ _ _ _ (.sort _ _) (.sort _ _)
  have hrhs : HasTyT pinLoopEnvT n loopCtx (iotaRhsOf loopW) (.sort (.succ .zero)) := by
    show HasTyT pinLoopEnvT n loopCtx
      (.app (.app loopMin (.bvar 0)) (loopKRedex (.bvar 0))) (.sort (.succ .zero))
    exact .app _ _ _ _ _ (.app _ _ _ _ _ tMinD tyH) hlhs
  have cAp : ConvT pinLoopEnvT n loopCtx (loopKRedex (.bvar 0)) (iotaLhsOf loopW)
      (.app loopMot (.bvar 0)) :=
    .app _ _ _ _ _ _ _ (.refl _ _ _ t2) (.irr _ _ _ _ hL tyH tyMkH)
  have cApT : ConvT pinLoopEnvT n loopCtx (loopKRedex (.bvar 0)) (iotaLhsOf loopW)
      (.sort (.succ .zero)) :=
    .tyConv _ _ _ _ _ _ cAp cRes
  have ciota : ConvT pinLoopEnvT n loopCtx (iotaLhsOf loopW) (iotaRhsOf loopW)
      (.sort (.succ .zero)) :=
    .iota _ _ _ _ (.of loopW) hlι hrhs
  have cββ : ConvT pinLoopEnvT n loopCtx (iotaRhsOf loopW) (.sort .zero)
      (.sort (.succ .zero)) := by
    show ConvT pinLoopEnvT n loopCtx
      (.app (.app loopMin (.bvar 0)) (loopKRedex (.bvar 0))) (.sort .zero)
      (.sort (.succ .zero))
    refine .trans _ _ _ _ _ (.app _ _ _ _ _ _ _
      (.beta _ _ _ _ _ _ hL tMinIh tyH) (.refl _ _ _ hlhs)) ?_
    exact .beta _ _ _ _ _ _ (.sort _ _) (.sort _ _) hlhs
  exact ⟨.symm _ _ _ _ (.trans _ _ _ _ _ cApT (.trans _ _ _ _ _ ciota cββ))⟩

/-- The recursive K point at every compact of `Sort 0`, both directions, with the core, at the
    admitted `Loop` environment (`pinLoopGroupRecWfT`). -/
theorem lrSCore_whStepCK_loop (c : CptI) (hc : ApproxI (ctxEnvI loopCtx) (.sort .zero) c) :
    LRSCore (WhStepCK pinLoopEnvT) pinLoopEnvT n loopCtx (.sort .zero) (loopKRedex (.bvar 0))
      (.sort (.succ .zero)) c := by
  rcases approxI_sort_inv hc with rfl | rfl
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    exact ⟨⟨_, .refl _⟩, _, _, .refl _, redR_whStepCK_loopKRedex⟩

theorem lrSCore_whStepCK_loop_symm (c : CptI) (hc : ApproxI (ctxEnvI loopCtx) (loopKRedex (.bvar 0)) c) :
    LRSCore (WhStepCK pinLoopEnvT) pinLoopEnvT n loopCtx (loopKRedex (.bvar 0)) (.sort .zero)
      (.sort (.succ .zero)) c := by
  have hc' : ApproxI (ctxEnvI loopCtx)
      (foldApps (.const 62 [.succ (.succ .zero)]) [loopMot, loopMin, .bvar 0]) c := hc
  rcases approxI_foldApps_const_inv hc' with rfl | ⟨us, rfl, _⟩
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    refine Or.inl ⟨⟨_, .refl _⟩, Or.inr ⟨fun m hm hind => ?_, .sort .zero, .sort .zero,
      redR_whStepCK_loopKRedex, .refl _, ⟨.refl _ _⟩⟩⟩
    have e' : pinLoopRecT = m := Option.some.inj hm
    subst e'
    exact MemberClass.noConfusion hind

/-! ### AXIOM QUERIES -/

#print axioms AppPropArgs
#print axioms IsCtorSpine
#print axioms KFieldW
#print axioms KFreeRec
#print axioms KFreeW
#print axioms KProjRec
#print axioms WhStepCK
#print axioms analyzeFields_some_elem
#print axioms appIrr_conv
#print axioms applyTelOr
#print axioms approxI_kConstFn_app_sort
#print axioms approxI_mixAndMinApp_inv
#print axioms canonField
#print axioms canonField_eq_of
#print axioms convT_iotaStarK_alignAt
#print axioms convT_iotaStarK_bvar
#print axioms cstepK_iotaStarK_bvar
#print axioms ctorMajor_mixAndW2
#print axioms ctorMajor_mixAndW3
#print axioms derivedIotaU_app_head
#print axioms detR_whStepCK
#print axioms diamondR_whStepCK
#print axioms eqAgreeCtx
#print axioms eqAgreeW
#print axioms eqGapCtx
#print axioms eqGapCtx_wf
#print axioms eqGapMot
#print axioms eqGapRedex
#print axioms eqGapW
#print axioms eqGap_conv
#print axioms famLevels
#print axioms fieldCount
#print axioms fieldfulK_join_mixAnd
#print axioms fields_length_eq_of_same_lhs
#print axioms hoMkTy
#print axioms hoMkTy_field
#print axioms instantiate_lamTel_body
#print axioms iotaLhsOf_wTrueRecPi
#print axioms iotaRhsOf_kfield_eq
#print axioms iotaRhsOf_kfree_eq
#print axioms iotaRhsOf_mixAndW3
#print axioms iotaRhsOf_wTrueRecPi
#print axioms iotaWitness_fields_firstOrder
#print axioms isPiTel_minorTel
#print axioms isPropTyR_true
#print axioms kConstFn
#print axioms kDemandCpt
#print axioms kProjWitness
#print axioms kProjWitness_eq
#print axioms kRecPi
#print axioms kRecPiHead
#print axioms kRecPi_conv
#print axioms kfieldW_kProjWitness
#print axioms kfieldW_loopW
#print axioms kfieldW_mixAndW
#print axioms kfreeW_wTrueRecPi
#print axioms lamTel
#print axioms length_projFields
#print axioms loopCtx
#print axioms loopKRedex
#print axioms loopK_conv
#print axioms loopMin
#print axioms loopMot
#print axioms loopW
#print axioms lrSCoreT_app_botDemand
#print axioms lrSCore_app_of_redR_arg
#print axioms lrSCore_whStepCK_appIrr
#print axioms lrSCore_whStepCK_kRec
#print axioms lrSCore_whStepCK_kRecPi
#print axioms lrSCore_whStepCK_kRecPi_symm
#print axioms lrSCore_whStepCK_kRec_symm
#print axioms lrSCore_whStepCK_loop
#print axioms lrSCore_whStepCK_loop_symm
#print axioms lrSCore_whStepCK_mixAnd
#print axioms lrSCore_whStepCK_mixAnd_kι
#print axioms lrSCore_whStepCK_mixAnd_symm
#print axioms lrSCore_whStepK_appIrr
#print axioms lrSCore_whStepK_kConstFn_app_all
#print axioms lrSCore_whStepK_kConstFn_kRecHead
#print axioms lrS_intro_var
#print axioms minorPosOf
#print axioms minorPosOf_lt
#print axioms mixAndCanon2
#print axioms mixAndCanon2Field3
#print axioms mixAndCanon2Ty
#print axioms mixAndCanon3
#print axioms mixAndCanon3Field4
#print axioms mixAndCanon3Ty
#print axioms mixAndKRedSubst
#print axioms mixAndProjMinor
#print axioms mixAndProjMotive
#print axioms mixAndProjW
#print axioms mixAndW2
#print axioms mixAndW3
#print axioms motIdx
#print axioms normalUniqueR_whStepCK
#print axioms not_appPropArgs_ctxModelDI_trueEnvU
#print axioms not_appPropArgs_ctxModelI_trueEnvU
#print axioms not_approxDI_kRec_var_sort
#print axioms not_detR_whStepK_andEnvU
#print axioms not_diamondR_whStepK_andEnvU
#print axioms not_fundamentalLRST_whStepCK_eqEnvT
#print axioms not_fundamentalLRST_whStepCtx_trueEnvU_piBotNil
#print axioms not_iotaWitness_of_higherOrderField
#print axioms not_isCtorSpine_bvar
#print axioms not_kfreeW_andEnvU
#print axioms not_lrSCore_intro_var
#print axioms not_lrSCore_whStepCtx_kRecPi_piBotNil
#print axioms not_readbackModelInv_whStepCK_ctxModelDI
#print axioms not_readbackModelInv_whStepCK_ctxModelI
#print axioms not_readbackModelInv_whStepK_ctxModelDI
#print axioms not_readbackModelInv_whStepK_ctxModelI
#print axioms peelDomsOr
#print axioms peelPis_of_isPiTel
#print axioms peelPis_prefix
#print axioms piDomOr
#print axioms projAll
#print axioms projAll_eq_of
#print axioms projAll_getElem?
#print axioms projAll_length
#print axioms projFields
#print axioms projFields_eq_of
#print axioms projLevels
#print axioms projOne
#print axioms projOne_eq_of
#print axioms readbackLaws_whStepCK
#print axioms recCountOf
#print axioms redR_mixAnd_projs
#print axioms redR_projField_ctorMajor
#print axioms redR_whStepCK_loopKRedex
#print axioms redR_whStepCK_mixAndRedex
#print axioms redexIdx
#print axioms resultIdxAt
#print axioms revealedPos?
#print axioms revealedPos?_eq_of
#print axioms rhsArgs_getD_minorPos
#print axioms rhsArgs_length
#print axioms rhsArgs_plain
#print axioms stepK_bvar
#print axioms stepK_kRec_var
#print axioms stepK_mixAnd
#print axioms tyConvT_bvar_align
#print axioms wTrueRecPi
#print axioms whRedCK_eqGapRedex_eq
#print axioms whRed_lamTel_bvar
#print axioms whRed_lamTel_lift
#print axioms whStepCK_bvar0_false
#print axioms whStepCK_bvar_none_false
#print axioms whStepCK_ctorSpine_false
#print axioms whStepCK_ctorSpine_false_aux
#print axioms whStepCK_ctx_det
#print axioms whStepCK_eqAgree
#print axioms whStepCK_eqGapRedex_false
#print axioms whStepCK_eqGapRedex_false_aux
#print axioms whStepCK_famApp_false_aux
#print axioms whStepCK_kProj_of
#print axioms whStepCK_kRec
#print axioms whStepCK_kRecPi
#print axioms whStepCK_lam_false_aux
#print axioms whStepCK_of_kfree_bvar
#print axioms whStepCK_pi_false_aux
#print axioms whStepCK_recPrefix_false
#print axioms whStepCK_recPrefix_false_aux
#print axioms whStepCK_sort_false_aux
#print axioms whStepCtx_foldApps_head
#print axioms whStepCtx_lam_false_aux
#print axioms whStepCtx_recCall_innerCK_aux
#print axioms whStepCtx_recCall_nonCtorMajor_aux
#print axioms whStepCtx_recPrefix_false_aux
#print axioms whStepK_bvar0_false
#print axioms whStepK_bvar_none_false_aux
#print axioms whStepK_lamApp_eq_aux
#print axioms whStepK_lam_false_aux
#print axioms whStepK_mixAndMin_app_eq
#print axioms whStepK_mixAndRedex_fork

end Rcic.Declarative.NativeValleys.ReadbackCKAudit
