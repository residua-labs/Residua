import rcic.RcicNativeValleyCert
import rcic.RcicIota
import rcic.RcicA2SortSupport

/-!
# Wall 2(a): native family projection along certified steps/stars

Brief `~/.residua-lean/briefs/wall2-famproj.md`, spec
`research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md` §§7.3–7.5,
stacked on `fable/native-valleys` (#7527).

`FamHeaded E a` packages a term whose spine head is an ADMITTED family
head: a real environment lookup `E.members r = some m` with member class
`.inductiveM`.  This is where the erased argument
(`convE_appN_const_inv_wf`, `RcicSynFamRigid`) meets the native
certified-step world: `.inductiveM` members are not `transparent`
(`transparent` is `true` only for `.definitionM`), so no δ rule applies —
the piece-F `NoHeadRule` route of #7524, discharged directly by class
discrimination rather than by a table sweep.

`HeadPathPeqFree p` is the honest premise: no `peq` node sits on the
head path of `p` — the chain formed by `app`'s function child, `conv`'s
inner step, and `iotaSpine`'s spine step.  A `peq` leaf is only the
abstract `PEq` relation, which does not constrain heads (e.g.
`PEqLeafT`'s `proof` leaf relates arbitrary proofs of possibly distinct
propositions), so a `peq` root genuinely can re-head a spine; every
other constructor cannot.  K constructors are already excluded from
`Certified` by design; here they are shown vacuous for `.inductiveM`-
headed sources anyway (their gates pin the head to the recursor member,
class `.recursorM`).

`famHead_step` / `famHead_cstep` / `famHead_star`: head rigidity — the
target of a head-peq-free (certified) step/star from a family-headed
source keeps the same member reference, an `eqNList`-related level list,
and the same spine length.

`FamArgCStep`, `famArgSteps`: per-argument projection — each spine
argument contributes its child `CStep`, sitting at the `app` node's own
carried domain `A` (the domain of the `Π` that the node's
`hc : TyConvT T₀ (pi A B)` selects).

`famLeftDomain`, `FamLeftDomainAlign`: the residual obligation, STATED
NOT PROVED — each projected argument `CStep` sits at its node's own
domain `Aᵢ`, while §7.4's target is `ConvT` at the LEFT instantiated
domain `Aᵢᴸ` read off the stored family telescope
(`T₀ := instantiateLevels ls m.mtype`, `Tᵢ = Π Aᵢ Bᵢ`,
`Tᵢ₊₁ := instantiate0 xs[i] Bᵢ`).  The missing piece is the `TyConvT`
index alignment `Aᵢ ~ Aᵢᴸ` per spine slot — the `retype` row of #7527
specialised to spine arguments; with it, `convT_of_tyConv` /
`CStep.reindex` transports each child's certificate to `ConvT` at
`Aᵢᴸ`.  See `research/rcic/sortrow/PIROW_STATUS_wall2-famproj.md`.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- A term whose application spine is headed by an admitted family member:
    a real lookup `E.members r = some m` with `m.mclass = .inductiveM`,
    `appsSpine a = (.const r ls, xs)`. -/
structure FamHeaded (E : ResolvedEnv) (a : Expr Nat) : Type where
  r : Nat
  ls : List Level
  xs : List (Expr Nat)
  m : CheckedMember
  hres : E.members r = some m
  hclass : m.mclass = .inductiveM
  hspine : appsSpine a = (.const r ls, xs)

/-- The head path of a step carries no `peq` node: `peq` may re-head a
    spine through its abstract leaf, so rigidity is stated off it.  The
    head path descends through `app`'s function child, `conv`'s inner
    step, and `iotaSpine`'s spine step; all other constructors are
    leaves for this purpose. -/
def HeadPathPeqFree {Γ : LCtx} {a b T : Expr Nat} :
    ParRedT PEq E n Γ a b T → Prop
  | .app _ _ _ _ _ _ _ _ _ _ hf _ _ _ _ _ => HeadPathPeqFree hf
  | .conv _ _ _ _ _ h _ => HeadPathPeqFree h
  | .iotaSpine _ _ _ _ _ hstep _ _ _ => HeadPathPeqFree hstep
  | .peq .. => False
  | _ => True

/-- A `CStar` with no `peq` on any step's head path — an inductive so
    `cases` exposes the per-step premises directly (the recursive `def`
    leaves a stuck `match` under `brecOn`). -/
inductive CStar.headPeqFree : {Γ : LCtx} → {a b A : Expr Nat} →
    CStar E n PEq Γ a b A → Prop where
  | refl {Γ : LCtx} {a A : Expr Nat} {h : HasTyT E n Γ a A} :
      CStar.headPeqFree (.refl Γ a A h)
  | tail {Γ : LCtx} {a b c A : Expr Nat} {s : CStep E n PEq Γ a b A}
        {hs : CStar E n PEq Γ b c A} :
      HeadPathPeqFree s.step → CStar.headPeqFree hs →
        CStar.headPeqFree (.tail s hs)

/-! ### small spine/head facts -/

/-- The spine head of a family-headed term, projected out. -/
theorem FamHeaded.head_eq {a : Expr Nat} (hf : FamHeaded E a)
    {e : Expr Nat} {xs' : List (Expr Nat)}
    (hsp : appsSpine a = (e, xs')) : e = .const hf.r hf.ls :=
  ((Prod.mk.inj (hf.hspine.symm.trans hsp)).1).symm

/-- Spine decomposition at an `app` node: if `app f x` is family-headed
    then `f` is family-headed at the same member, and the source spine is
    `f`'s spine extended by `x`. -/
def FamHeaded.ofApp {f x : Expr Nat} (hf : FamHeaded E (.app f x)) :
    FamHeaded E f := by
  have hsp : ((appsSpine f).1, (appsSpine f).2 ++ [x]) =
      (.const hf.r hf.ls, hf.xs) := hf.hspine
  obtain ⟨hhd, _⟩ := Prod.mk.inj hsp
  exact ⟨hf.r, hf.ls, (appsSpine f).2, hf.m, hf.hres, hf.hclass,
    Prod.ext hhd rfl⟩

/-- The source spine of a family-headed `app` is the function's spine
    with the last argument appended. -/
theorem FamHeaded.spine_app {f x : Expr Nat} (hf : FamHeaded E (.app f x)) :
    hf.xs = (appsSpine f).2 ++ [x] := by
  have hsp : ((appsSpine f).1, (appsSpine f).2 ++ [x]) =
      (.const hf.r hf.ls, hf.xs) := hf.hspine
  exact ((Prod.mk.inj hsp).2).symm

/-- `.inductiveM` members are rigid: `transparent` only fires for
    `.definitionM`, so `transparent m'.mclass = true` contradicts the
    admitted-family class.  The delta-side content of piece F's
    `NoHeadRule` (#7524) for an admitted `.inductiveM` head — discharged
    by class discrimination on the member, no table induction needed. -/
theorem FamHeaded.not_transparent {a : Expr Nat} (hf : FamHeaded E a)
    {m' : CheckedMember} (hres' : E.members hf.r = some m') :
    transparent m'.mclass = false := by
  have hm : m' = hf.m := Option.some.inj (hres'.symm.trans hf.hres)
  cases hm
  rw [hf.hclass]
  rfl

/-- A member looked up at a family head's reference has class
    `.inductiveM`, not `.recursorM` — the iota/K-side contradiction. -/
theorem FamHeaded.not_recursor {a : Expr Nat} (hf : FamHeaded E a)
    {m' : CheckedMember} (hres' : E.members hf.r = some m') :
    m'.mclass ≠ .recursorM := by
  have hm : m' = hf.m := Option.some.inj (hres'.symm.trans hf.hres)
  cases hm
  rw [hf.hclass]
  intro h
  exact MemberClass.noConfusion h

/-- `iotaLhsOf w` is recursor-headed. -/
theorem iotaLhsOf_head (w : IotaWitness E) :
    appsSpine (iotaLhsOf w) =
      (.const w.recRef w.ls, w.preMajor ++ [ctorMajor w]) := by
  unfold iotaLhsOf recCall
  rw [appsSpine_foldApps_const]

/-- `iotaLhsOfS w` is recursor-headed. -/
theorem iotaLhsOfS_head (w : IotaWitnessS E) :
    appsSpine (iotaLhsOfS w) =
      (.const w.recRef w.ls,
        w.preMajor ++ [foldApps (.const w.ctorRef w.lsC)
          (w.ctorParams ++ w.fields)]) := by
  unfold iotaLhsOfS recCall
  rw [appsSpine_foldApps_const]

/-! ### deliverable 1: head rigidity -/

/-- One-step head rigidity, over ALL `ParRedT` constructors.  A
    head-peq-free step from a family-headed source lands family-headed at
    the same member reference, with `eqNList`-related levels and equal
    spine length.

    - `refl` keeps the term; `consts` moves only the level list.
    - `app` descends the function child (the head path).
    - `conv` descends the inner step; `iotaSpine` descends its `hstep`
      and then dies: the reduct's `DerivedIotaU` gate pins `lhs'` to the
      recursor member, contradicting `.inductiveM`.
    - `delta` dies by transparency; `iotaStarK` by the recursor head;
      `iotaStarKEta` by `iotaStarKEta_head`'s pinned spine head.
    - sort/bvar/lam/pi/letE/lit/eta sources are not `.const`-headed.
    - `peq` is excluded by `HeadPathPeqFree`. -/
theorem famHead_step {Γ : LCtx} {a b T : Expr Nat}
    (p : ParRedT PEq E n Γ a b T) :
    HeadPathPeqFree p → ∀ hf : FamHeaded E a,
      ∃ hf' : FamHeaded E b, hf'.r = hf.r ∧ eqNList hf.ls hf'.ls ∧
        hf'.xs.length = hf.xs.length := by
  induction p with
  | refl Γ a A _ =>
      intro _ hf
      exact ⟨hf, rfl, eqNList_refl _, rfl⟩
  | sortEq Γ l₁ l₂ T _ _ _ =>
      intro _ hf
      have hsp : (Expr.sort l₁, []) = (.const hf.r hf.ls, hf.xs) := hf.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | consts Γ r' ls ls' T h _ _ =>
      intro _ hf
      have hsp : (Expr.const r' ls, []) = (.const hf.r hf.ls, hf.xs) := hf.hspine
      obtain ⟨hc, hxs⟩ := Prod.mk.inj hsp
      obtain ⟨hr', hls⟩ := Expr.const.inj hc
      refine ⟨⟨r', ls', [], hf.m, ?_, hf.hclass, rfl⟩,
        hr', hls ▸ h, congrArg List.length hxs⟩
      · exact (congrArg E.members hr').trans hf.hres
  | bvarZeta Γ i A v v' T _ _ _ _ _ih =>
      intro _ hf
      have hsp : (Expr.bvar i, []) = (.const hf.r hf.ls, hf.xs) := hf.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | delta Γ r' ls m b T hres _ htr _ _ _ _ =>
      intro _ hf
      have hsp : (Expr.const r' ls, []) = (.const hf.r hf.ls, hf.xs) := hf.hspine
      obtain ⟨hc, _⟩ := Prod.mk.inj hsp
      obtain ⟨hr', _⟩ := Expr.const.inj hc
      have hb := hf.not_transparent ((congrArg E.members hr').symm.trans hres)
      rw [hb] at htr
      exact Bool.noConfusion htr
  | app Γ f f' a a' A B T₀ _ _ hfstep _ _ _ hastep _ ihf _ =>
      intro hnp hfam
      have hsp' : ((appsSpine f).1, (appsSpine f).2 ++ [a]) =
          (.const hfam.r hfam.ls, hfam.xs) := hfam.hspine
      obtain ⟨hhd_src, htl_src⟩ := Prod.mk.inj hsp'
      obtain ⟨hf', hr_eq, hlv, hln⟩ := ihf hnp
        ⟨hfam.r, hfam.ls, (appsSpine f).2, hfam.m, hfam.hres, hfam.hclass,
          Prod.ext hhd_src rfl⟩
      refine ⟨⟨hf'.r, hf'.ls, hf'.xs ++ [a'], hf'.m, hf'.hres, hf'.hclass, ?_⟩,
        hr_eq, hlv, ?_⟩
      · show appsSpine (.app f' a') = _
        rw [show appsSpine (.app f' a') =
          ((appsSpine f').1, (appsSpine f').2 ++ [a']) from rfl,
          congrArg Prod.fst hf'.hspine, congrArg Prod.snd hf'.hspine]
      · have e : ((appsSpine f).2 ++ [a]).length = hfam.xs.length :=
          congrArg List.length htl_src
        rw [List.length_append, List.length_cons, List.length_nil] at e
        have hln' : hf'.xs.length = (appsSpine f).2.length := hln
        show (hf'.xs ++ [a']).length = hfam.xs.length
        rw [List.length_append, List.length_cons, List.length_nil]
        omega
  | beta Γ A _ _ arg _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro _ hf
      have hsp : (Expr.lam A _, [arg]) = (.const hf.r hf.ls, hf.xs) := hf.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | lam Γ A _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro _ hf
      have hsp : (Expr.lam A _, []) = (.const hf.r hf.ls, hf.xs) := hf.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | pi Γ A _ _ _ _ _ _ _ _ _ _ =>
      intro _ hf
      have hsp : (Expr.pi A _, []) = (.const hf.r hf.ls, hf.xs) := hf.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | letE Γ A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro _ hf
      have hsp : (Expr.letE A _ _, []) = (.const hf.r hf.ls, hf.xs) := hf.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | zeta Γ A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro _ hf
      have hsp : (Expr.letE A _ _, []) = (.const hf.r hf.ls, hf.xs) := hf.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | iotaSpine Γ lhs lhs' rhs T hstep hI _ _ ih =>
      intro hnp hf
      obtain ⟨hf', _, _, _⟩ := ih hnp hf
      cases hI with
      | ofU w =>
          have hsp := hf'.hspine
          rw [iotaLhsOf_head] at hsp
          obtain ⟨hc, _⟩ := Prod.mk.inj hsp
          obtain ⟨hrr, _⟩ := Expr.const.inj hc
          exact absurd w.hrecK
            (hf'.not_recursor ((congrArg E.members hrr).symm.trans w.hrec))
      | ofUS w =>
          have hsp := hf'.hspine
          rw [iotaLhsOfS_head] at hsp
          obtain ⟨hc, _⟩ := Prod.mk.inj hsp
          obtain ⟨hrr, _⟩ := Expr.const.inj hc
          exact absurd w.hrecK
            (hf'.not_recursor ((congrArg E.members hrr).symm.trans w.hrec))
  | iotaStarK Γ w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro _ hf
      have hsp := hf.hspine
      unfold recCall at hsp
      rw [appsSpine_foldApps_const] at hsp
      obtain ⟨hc, _⟩ := Prod.mk.inj hsp
      obtain ⟨hrr, _⟩ := Expr.const.inj hc
      exact absurd w.hrecK
        (hf.not_recursor ((congrArg E.members hrr).symm.trans w.hrec))
  | iotaStarKEta Γ w f _ _ _ _ _ _ _ happ _ _ _ _ _ _ _ _ _ _ _ _ =>
      intro _ hf
      obtain ⟨hhead, _, _⟩ := iotaStarKEta_head happ
      have h1 : (appsSpine f).1 = .const hf.r hf.ls :=
        congrArg Prod.fst hf.hspine
      obtain ⟨hrr, _⟩ := Expr.const.inj (h1.symm.trans hhead)
      exact absurd w.hrecK
        (hf.not_recursor ((congrArg E.members hrr).trans w.hrec))
  | lit Γ t T _ =>
      intro _ hf
      have hsp : (Expr.lit t, []) = (.const hf.r hf.ls, hf.xs) := hf.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | eta Γ _ _ A _ _ _ _ =>
      intro _ hf
      have hsp : (Expr.lam A _, []) = (.const hf.r hf.ls, hf.xs) := hf.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | peq Γ _ _ _ _ =>
      intro hnp _
      exact False.elim hnp
  | conv Γ _ _ _ _ _ _ ih =>
      intro hnp hf
      exact ih hnp hf

/-- The `CStep` form of `famHead_step`. -/
theorem famHead_cstep {Γ : LCtx} {a b T : Expr Nat}
    (s : CStep E n PEq Γ a b T) (hnp : HeadPathPeqFree s.step)
    (hf : FamHeaded E a) :
    ∃ hf' : FamHeaded E b, hf'.r = hf.r ∧ eqNList hf.ls hf'.ls ∧
      hf'.xs.length = hf.xs.length :=
  famHead_step s.step hnp hf

/-- Star-level head rigidity: a certified star with peq-free head paths
    keeps the member reference, composes the `eqNList` relations, and
    preserves spine length. -/
theorem famHead_star {Γ : LCtx} {a b A : Expr Nat}
    (s : CStar E n PEq Γ a b A) :
    s.headPeqFree → ∀ hf : FamHeaded E a,
      ∃ hf' : FamHeaded E b, hf'.r = hf.r ∧ eqNList hf.ls hf'.ls ∧
        hf'.xs.length = hf.xs.length := by
  induction s with
  | refl _ _ _ =>
      intro _ hf
      exact ⟨hf, rfl, eqNList_refl _, rfl⟩
  | tail s hs ih =>
      intro hnp hf
      cases hnp with
      | tail h1 h2 =>
          obtain ⟨hm, hrm, hlm, hnm⟩ := famHead_step s.step h1 hf
          obtain ⟨hf', hr', hlv', hln'⟩ := ih h2 hm
          exact ⟨hf', hr'.trans hrm, F8A2Support.eqNList_trans_local hlm hlv',
            hln'.trans hnm⟩

/-! ### deliverable 2: per-argument projection -/

/-- A projected argument child: a certified step `x ⇒ x'` at the node's
    own carried domain `A` — the argument's type in the source spine. -/
structure FamArgCStep (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (Γ : LCtx) where
  x : Expr Nat
  x' : Expr Nat
  A : Expr Nat
  step : CStep E n PEq Γ x x' A

/-- Argument typings along an application spine: peeling `HasTyT.app`
    nodes (through `conv` index movers), each slot's argument typing at
    that node's domain. -/
def argTys {Γ : LCtx} {a T : Expr Nat} :
    HasTyT E n Γ a T → List (Σ' (x A : Expr Nat), HasTyT E n Γ x A)
  | .app _ _ _ _ _ hf ha => argTys hf ++ [⟨_, _, ha⟩]
  | .conv _ _ _ _ _ h _ => argTys h
  | _ => []

/-- The collected arguments are exactly the spine arguments.
    `HasTyT` is in a `mutual` block (`induction` unsupported), so this is
    structural recursion on `h` — the `app`/`conv` children are direct
    subterms; every leaf closes by `rfl`. -/
theorem argTys_fst : {Γ : LCtx} → {a T : Expr Nat} → (h : HasTyT E n Γ a T) →
    (argTys h).map (·.1) = (appsSpine a).2
  | _, _, _, .app Γ f a A B hf ha => by
      have e : argTys (.app Γ f a A B hf ha) = argTys hf ++ [⟨a, A, ha⟩] := rfl
      rw [e, List.map_append, List.map_cons, List.map_nil, argTys_fst hf]
      rfl
  | _, _, _, .conv _ _ _ _ _ h _ => argTys_fst h
  | _, _, _, .sort _ _ => rfl
  | _, _, _, .bvar _ _ _ _ => rfl
  | _, _, _, .const _ _ _ _ _ _ _ => rfl
  | _, _, _, .pi _ _ _ _ _ _ _ => rfl
  | _, _, _, .lam _ _ _ _ _ _ _ => rfl
  | _, _, _, .letE _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, .lit _ _ _ _ => rfl

/-- Per-argument projection: from a head-peq-free certified step out of a
    family-headed source, the list of certified child steps — one per
    source-spine argument, each at its node's own carried domain.

    - `app` peels the tail argument's `ca` and recurses into `cf`.
    - `conv` unwraps; `refl` manufactures reflexive children from the
      carried endpoint typing via `argTys`.
    - `consts` has an empty spine; `delta`/`beta`/`iotaSpine` and the
      leaf-shape constructors are vacuous under `FamHeaded`; `peq` is
      excluded by `HeadPathPeqFree`. -/
theorem famArgSteps {Γ : LCtx} {a b T : Expr Nat}
    {p : ParRedT PEq E n Γ a b T}
    (cp : Certified p) :
    HeadPathPeqFree p → FamHeaded E a →
    ∃ args : List (FamArgCStep E n PEq Γ),
      args.map (·.x) = (appsSpine a).2 ∧
      args.map (·.x') = (appsSpine b).2 := by
  induction cp with
  | refl c =>
      rename_i Γ₂ a₂ A₂ h₂
      intro _ _
      refine ⟨(argTys h₂).map (fun t => (⟨t.1, t.1, t.2.1,
          ⟨ParRedT.refl _ _ _ t.2.2,
            Certified.refl (ConvT.refl _ _ _ t.2.2)⟩⟩ :
            FamArgCStep E n PEq Γ₂)), ?_, ?_⟩
      · rw [List.map_map]; exact argTys_fst h₂
      · rw [List.map_map]; exact argTys_fst h₂
  | sortEq c =>
      rename_i Γ₂ l₁ l₂ T₂ h₂ hl₂ hr₂
      intro _ hfam
      have hsp : (Expr.sort l₁, []) = (.const hfam.r hfam.ls, hfam.xs) :=
        hfam.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | consts c =>
      intro _ _
      exact ⟨[], rfl, rfl⟩
  | bvarZeta c cv ih =>
      rename_i Γ₂ i A₂ v v' T₂ h₂ hv₂ hl₂ hr₂
      intro _ hfam
      have hsp : (Expr.bvar i, []) = (.const hfam.r hfam.ls, hfam.xs) :=
        hfam.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | delta c =>
      rename_i Γ₂ r ls m b₂ T₂ hres hbody htr hlen hwf hl₂ hr₂
      intro _ hfam
      have hsp : (Expr.const r ls, []) = (.const hfam.r hfam.ls, hfam.xs) :=
        hfam.hspine
      obtain ⟨hc, _⟩ := Prod.mk.inj hsp
      obtain ⟨hrr, _⟩ := Expr.const.inj hc
      have hb := hfam.not_transparent ((congrArg E.members hrr).symm.trans hres)
      rw [hb] at htr
      exact Bool.noConfusion htr
  | app c cf ca ihf iha =>
      rename_i Γ₂ f f' a a' A B T₀ v w hf hc hB hTy ha hr
      intro hnp hfam
      obtain ⟨ps, hpx, hpx'⟩ := ihf hnp hfam.ofApp
      refine ⟨ps ++ [⟨a, a', A, ⟨ha, ca⟩⟩], ?_, ?_⟩
      · rw [List.map_append, List.map_cons, List.map_nil, hpx]
        rfl
      · rw [List.map_append, List.map_cons, List.map_nil, hpx']
        rfl
  | beta c cb ca ihb iha =>
      rename_i Γ₂ A body body' arg arg' B u v w hA hB hTy hb ha hred
      intro _ hfam
      have hsp : (Expr.lam A body, [arg]) =
          (.const hfam.r hfam.ls, hfam.xs) := hfam.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | lam c cb ih =>
      rename_i Γ₂ A A' body body' B u v hc hA hB hb hrt
      intro _ hfam
      have hsp : (Expr.lam A body, []) =
          (.const hfam.r hfam.ls, hfam.xs) := hfam.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | pi c =>
      rename_i Γ₂ A A' B B' u v hA hc hB hcB hrt
      intro _ hfam
      have hsp : (Expr.pi A B, []) = (.const hfam.r hfam.ls, hfam.xs) :=
        hfam.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | letE c cv cb ihv ihb =>
      rename_i Γ₂ A A' value value' body body' B u w hc hA hv hB hTy hb hrt
      intro _ hfam
      have hsp : (Expr.letE A value body, []) =
          (.const hfam.r hfam.ls, hfam.xs) := hfam.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | zeta c cv cb ihv ihb =>
      rename_i Γ₂ A value value' body body' B u w hA hv hB hTy hb hred
      intro _ hfam
      have hsp : (Expr.letE A value body, []) =
          (.const hfam.r hfam.ls, hfam.xs) := hfam.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | iotaSpine c cs ih =>
      rename_i Γ₂ lhs lhs' rhs T₂ hstep hI hred hrhs
      intro hnp hfam
      obtain ⟨hf', _, _, _⟩ := famHead_step hstep hnp hfam
      cases hI with
      | ofU w =>
          have hsp := hf'.hspine
          rw [iotaLhsOf_head] at hsp
          obtain ⟨hc, _⟩ := Prod.mk.inj hsp
          obtain ⟨hrr, _⟩ := Expr.const.inj hc
          exact absurd w.hrecK
            (hf'.not_recursor ((congrArg E.members hrr).symm.trans w.hrec))
      | ofUS w =>
          have hsp := hf'.hspine
          rw [iotaLhsOfS_head] at hsp
          obtain ⟨hc, _⟩ := Prod.mk.inj hsp
          obtain ⟨hrr, _⟩ := Expr.const.inj hc
          exact absurd w.hrecK
            (hf'.not_recursor ((congrArg E.members hrr).symm.trans w.hrec))
  | lit c =>
      rename_i Γ₂ t T₂ hexp
      intro _ hfam
      have hsp : (Expr.lit t, []) = (.const hfam.r hfam.ls, hfam.xs) :=
        hfam.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | eta c cf ih =>
      rename_i Γ₂ f f' A B hf₂ hl₂
      intro _ hfam
      have hsp : (Expr.lam A (.app (lift 0 1 f) (.bvar 0)), []) =
          (.const hfam.r hfam.ls, hfam.xs) := hfam.hspine
      exact Expr.noConfusion (Prod.mk.inj hsp).1
  | peq c =>
      intro hnp _
      exact False.elim hnp
  | conv c ch ih =>
      intro hnp hfam
      exact ih hnp hfam

/-! ### deliverable 3: the retained left-domain obligation -/

/-- The §7.4 left-instantiated domain: `Aᵢᴸ` is the domain of the Π
    reached by peeling the stored family telescope `T₀ :=
    instantiateLevels ls m.mtype` under the first `i` source arguments
    (`Tⱼ = Π Aⱼ Bⱼ`, `Tⱼ₊₁ = instantiate0 xs[j] Bⱼ`).
    `famLeftDomain T (xs.take i) = some Aᵢᴸ` when the residual is a Π. -/
def famLeftDomain : Expr Nat → List (Expr Nat) → Option (Expr Nat)
  | .pi A _, [] => some A
  | .pi _ B, x :: xs => famLeftDomain (instantiate0 x B) xs
  | _, _ => none

/-- The retained §7.4 obligation, STATED NOT PROVED — the exact premise
    `famArgSteps`' output would consume for `ConvT` at the LEFT domain.
    Parameterized over the produced `args : List (FamArgCStep …)`: for
    each slot `i`, the child's OWN carried domain `(args.get i).A` (the
    `app` node's domain, where the source argument is `args.get i .x`)
    is `TyConvT`-aligned to the left-instantiated telescope domain
    `Aᵢᴸ = famLeftDomain (instantiateLevels ls m.mtype) (xs.take i)`
    with `xs := args.map (·.x)` — the `retype` row of #7527 instantiated
    at spine arguments.  That alignment is where `sortRow`/`piRow`
    saturation and scoped sort–Π separation (`AllBelowScoped`) enter;
    see `research/rcic/sortrow/PIROW_STATUS_wall2-famproj.md`. -/
def FamLeftDomainAlign (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) (Γ : LCtx)
    (m : CheckedMember) (ls : List Level)
    (args : List (FamArgCStep E n PEq Γ)) : Prop :=
  ∀ i : Fin args.length, ∀ AL : Expr Nat,
    famLeftDomain (instantiateLevels ls m.mtype)
      ((args.map (·.x)).take i.val) = some AL →
    Nonempty (TyConvT E n Γ (args.get i).A AL)

/-- The bridge the retained premise buys: under `FamLeftDomainAlign`,
    each produced argument child upgrades to a certified step at the
    left-instantiated domain `Aᵢᴸ` via `CStep.reindex` — the
    `convT_of_tyConv` transport along the slot's `TyConvT`. -/
theorem FamLeftDomainAlign.cstep_left {Γ : LCtx}
    {m : CheckedMember} {ls : List Level}
    {args : List (FamArgCStep E n PEq Γ)}
    (h : FamLeftDomainAlign E n PEq Γ m ls args)
    (i : Fin args.length) {AL : Expr Nat}
    (hdom : famLeftDomain (instantiateLevels ls m.mtype)
      ((args.map (·.x)).take i.val) = some AL) :
    Nonempty (CStep E n PEq Γ (args.get i).x (args.get i).x' AL) := by
  obtain ⟨ht⟩ := h i AL hdom
  exact ⟨(args.get i).step.reindex ht⟩

/-- The `ConvT` corollary — the child's certificate root re-sorted at
    `Aᵢᴸ` (`CStep.toConvT` on the reindexed step). -/
theorem FamLeftDomainAlign.conv_left {Γ : LCtx}
    {m : CheckedMember} {ls : List Level}
    {args : List (FamArgCStep E n PEq Γ)}
    (h : FamLeftDomainAlign E n PEq Γ m ls args)
    (i : Fin args.length) {AL : Expr Nat}
    (hdom : famLeftDomain (instantiateLevels ls m.mtype)
      ((args.map (·.x)).take i.val) = some AL) :
    Nonempty (ConvT E n Γ (args.get i).x (args.get i).x' AL) := by
  obtain ⟨s⟩ := h.cstep_left i hdom
  exact ⟨s.toConvT⟩

#print axioms famHead_step
#print axioms famHead_star
#print axioms famArgSteps
#print axioms argTys_fst
