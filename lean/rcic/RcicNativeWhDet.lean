import rcic.RcicNativePiModelLRTermD
import rcic.RcicNativePiModelDeltaIota
import rcic.RcicTypedGroupPins
import rcic.RcicCensusWallsForall

/-!
# RcicNativeWhDet — the `piRow_of_fundamentalTermD` side premises

`piRow_of_fundamentalTermD` asks for `EnvClosed E`, `EnvWfT E` and `WhDet E`.  This
module discharges the first and reduces the second to a single named premise:

* `EnvClosed`: already derivable, `envClosed_of_envWfT` (`RcicTypedEnvEntry`).
* `WhDet`: weak-head determinism.  `WhStep` has six constructors; cross-constructor
  collisions on one source are impossible by shape EXCEPT two:
  - `iota × appHead`: an ι redex `foldApps (const r ls) (pre ++ [major])` could also
    step inside its head `foldApps (const r ls) pre`.  A head step is δ (needs a body
    on the recursor member) or a shorter ι on the same head (needs spine length =
    `piCount recMember.mtype`, pinned by `IotaWitness(S).hpre`/`hnmin`), or deeper
    `appHead`.  Under `RecursorsOpaque` — every `recursorM` member has `body = none`,
    which `EnvWfT` supplies through `GroupMembersT.cons`'s `hnobody` — every head step
    is impossible (`whStep_foldApps_const_bounded`), so `DerivedIotaU`-headed sources
    have no `appHead` reduct (`derivedIotaU_no_head_step`).
  - `iota × iota`: two derived-ι derivations of one redex.  This is exactly the named
    premise `IotaDetU` (`RcicNativeValleyFronts`); its legacy arm is landed
    (`iotaDetU_ofU`) and — FCD14 — the full union is now discharged upstream:
    `PiModelDeltaIotaAudit.iotaDetU_of_envWfT` (#7656) lifts every `.ofU` witness to
    a typed-root `DerivedIotaT` at the same endpoints
    (`derivedIotaT_of_iotaWitness_envWfT`, via the admitted recursor cell's
    constructor data) and closes both arms by `iotaDetT`.
  All remaining pairs close by constructor-mismatch (`beta`/`zeta`/`lit`/`delta`
  sources are `lam`-headed/`letE`/`lit`/`const`, and δ's member lookup is unique).

  Hence `whDet_of_envWfT_iotaDet : EnvWfT E → IotaDetU E → WhDet E`, and — with the
  premise now discharged — `whDet_of_envWfT : EnvWfT E → WhDet E` and the restated
  consumer `piRow_of_fundamentalTermD_of_envWfT`, whose premises are
  `EnvWfT ∧ TypeSoundnessI ∧ FundamentalTermD`.

* The counterexample `whDet_detEnv_false`: `detEnv` is `trueEnvU` with `True.rec`
  carrying a δ body — NOT `EnvWfT`-admissible (group members must be body-less) — and
  `WhDet detEnv` is kernel-false: the `True.rec` redex steps by ι to `Sort 0` and by
  `appHead`-δ to `(lit 7) M S0 tt`.  The premise is load-bearing: without opacity the
  ι×appHead collision is real.  (η-K plays no role here: `WhStep` has no η case —
  #7608's obstruction lives in `ParRedT`, not in weak-head reduction.)
-/

namespace Rcic.Declarative.NativeValleys.PiModelIdealAudit

/-- Recursor members carry no δ body — the condition `EnvWfT.group` supplies via
`GroupMembersT.cons`'s `hnobody`.  This is what blocks the δ arm of a head step under
an ι redex. -/
def RecursorsOpaque (E : ResolvedEnv) : Prop :=
  ∀ {r : Nat} {m : CheckedMember}, E.members r = some m → m.mclass = .recursorM →
    m.body = none

/-- Opacity is preserved when a body-less member is adjoined. -/
theorem recursorsOpaque_of_extend {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hE : RecursorsOpaque E) (hb : m.body = none) :
    RecursorsOpaque (extendEnv E r m) := by
  intro r' m' hmem' hk'
  have hmem'' : (if r' = r then some m else E.members r') = some m' := hmem'
  split at hmem''
  · rename_i hr
    subst hr
    have hmm : m = m' := Option.some.inj hmem''
    subst hmm
    exact hb
  · exact hE hmem'' hk'

/-- Opacity is preserved when a NON-recursor member is adjoined. -/
theorem recursorsOpaque_of_extend_nonRec {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (hE : RecursorsOpaque E) (hne : m.mclass ≠ .recursorM) :
    RecursorsOpaque (extendEnv E r m) := by
  intro r' m' hmem' hk'
  have hmem'' : (if r' = r then some m else E.members r') = some m' := hmem'
  split at hmem''
  · rename_i hr
    subst hr
    have hmm : m = m' := Option.some.inj hmem''
    rw [← hmm] at hk'
    exact absurd hk' hne
  · exact hE hmem'' hk'

/-- Group members are added one by one, each with `hnobody : m.body = none`, so
opacity propagates through the whole `GroupMembersT` chain. -/
theorem recursorsOpaque_of_groupMembersT {S E : ResolvedEnv}
    {lst : List (Nat × CheckedMember)} {E' : ResolvedEnv}
    (h : GroupMembersT S E lst E') :
    RecursorsOpaque E → RecursorsOpaque E' := by
  induction h with
  | nil => exact fun hE => hE
  | cons E r m rest E' hfresh hnobody _ _ _ _ _ _ _ _ _ _ _ hrest ih =>
    exact fun hE => ih (recursorsOpaque_of_extend hE hnobody)

/-- **The `EnvWfT` side**: recursor opacity is derivable from `EnvWfT` — group members
are forced body-less, and singleton members are never `recursorM`. -/
theorem recursorsOpaque_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) :
    RecursorsOpaque E := by
  induction hW with
  | empty => intro r m hmem _; exact Option.noConfusion hmem
  | «axiom» _ _ _ _ _ _ _ _ _ ih =>
    exact recursorsOpaque_of_extend_nonRec ih (fun h => MemberClass.noConfusion h)
  | definition _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact recursorsOpaque_of_extend_nonRec ih (fun h => MemberClass.noConfusion h)
  | thm _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact recursorsOpaque_of_extend_nonRec ih (fun h => MemberClass.noConfusion h)
  | «opaque» _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact recursorsOpaque_of_extend_nonRec ih (fun h => MemberClass.noConfusion h)
  | group E f fm ctors rr rm E' hE hfam hctors hrec hmem ih =>
    exact recursorsOpaque_of_groupMembersT hmem ih

/-- The ι-redex head package: a `DerivedIotaU` left side is `foldApps (const r ls)` at
a full spine whose length is pinned to `piCount` of the recursor member's stored type,
and the head member is a `recursorM`.  (A strengthened `derivedIotaU_source`.) -/
theorem derivedIotaU_head {E : ResolvedEnv} {l rhs : Expr Nat}
    (hI : DerivedIotaU E l rhs) :
    ∃ (r : Nat) (ls : List Level) (m : CheckedMember) (pre : List (Expr Nat))
      (major : Expr Nat),
      l = foldApps (.const r ls) (pre ++ [major]) ∧ E.members r = some m ∧
      m.mclass = .recursorM ∧ (pre ++ [major]).length = piCount m.mtype := by
  cases hI with
  | ofU w =>
    exact ⟨w.recRef, w.ls, w.recMember, w.preMajor, ctorMajor w, rfl, w.hrec,
      w.hrecK, by
        rw [List.length_append, List.length_singleton, w.hpre]; exact w.hnmin⟩
  | ofUS w =>
    refine ⟨w.recRef, w.ls, w.recMember, w.preMajor,
      foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields), rfl, w.hrec,
      w.hrecK, ?_⟩
    rw [List.length_append, List.length_singleton, w.hpre]; exact w.hnmin

/-- Head decomposition of a const-headed spine equality: the heads and spines agree. -/
theorem foldApps_const_inj {r r' : Nat} {ls ls' : List Level}
    {xs ys : List (Expr Nat)}
    (h : foldApps (.const r ls) xs = foldApps (.const r' ls') ys) :
    r = r' ∧ ls = ls' ∧ xs = ys := by
  have hs := congrArg appsSpine h
  rw [appsSpine_foldApps_const, appsSpine_foldApps_const] at hs
  rw [Prod.mk.injEq] at hs
  obtain ⟨hc, hsp⟩ := hs
  rw [Expr.const.injEq] at hc
  exact ⟨hc.1, hc.2, hsp⟩

/-- A const-headed spine is never a `lam`. -/
theorem foldApps_const_ne_lam {r : Nat} {ls : List Level} {xs : List (Expr Nat)}
    {A B : Expr Nat} : foldApps (.const r ls) xs ≠ .lam A B := by
  intro h
  have hs := congrArg appsSpine h
  rw [appsSpine_foldApps_const] at hs
  have hs' : (Expr.const r ls, xs) = (Expr.lam A B, []) := hs
  rw [Prod.mk.injEq] at hs'
  exact Expr.noConfusion hs'.1

/-- No weak-head step leaves a `lam` (the `beta` redex is the `app`, not the `lam`;
the ι arm is excluded by head shape). -/
theorem whStep_lam_false {E : ResolvedEnv} {A B c : Expr Nat}
    (h : WhStep E (.lam A B) c) : False := by
  cases h with
  | iota hI =>
    obtain ⟨r, ls, m, pre, maj, hshape, _, _, _⟩ := derivedIotaU_head hI
    rw [foldApps_snoc] at hshape
    exact Expr.noConfusion hshape

/-- **Head stability, the non-local half of `WhDet`.**  A const-headed spine of a
recursor member cannot weak-head step while its length is below the pinned ι arity:
δ is blocked by opacity, β/ζ/lit by shape, ι by the length pin (a shorter ι on the
same head would need `length = piCount mtype`), and `appHead` recurses on a strictly
shorter prefix.  Termination by spine length. -/
theorem whStep_foldApps_const_bounded {E : ResolvedEnv} (hO : RecursorsOpaque E)
    {r : Nat} {m : CheckedMember} (hmem : E.members r = some m)
    (hk : m.mclass = .recursorM) {ls : List Level} {xs : List (Expr Nat)}
    (hlt : xs.length < piCount m.mtype) {y : Expr Nat}
    (h : WhStep E (foldApps (.const r ls) xs) y) : False := by
  generalize hgen : foldApps (.const r ls) xs = s at h
  cases h with
  | beta A b a =>
    -- s = app (lam A b) a : the spine head would have to be a lam
    have hs := congrArg appsSpine hgen
    rw [appsSpine_foldApps_const] at hs
    have hs' : (Expr.const r ls, xs) = (Expr.lam A b, [a]) := hs
    rw [Prod.mk.injEq] at hs'
    exact Expr.noConfusion hs'.1
  | zeta A v b =>
    have hs := congrArg appsSpine hgen
    rw [appsSpine_foldApps_const] at hs
    have hs' : (Expr.const r ls, xs) = (Expr.letE A v b, []) := hs
    rw [Prod.mk.injEq] at hs'
    exact Expr.noConfusion hs'.1
  | delta hres hbody =>
    rename_i r₂ ls₂ m₂ b₂
    -- hgen : foldApps (const r ls) xs = const r₂ ls₂ — spine injection
    have hs := congrArg appsSpine hgen
    rw [appsSpine_foldApps_const] at hs
    have hs' : (Expr.const r ls, xs) = (Expr.const r₂ ls₂, []) := hs
    rw [Prod.mk.injEq, Expr.const.injEq] at hs'
    obtain ⟨⟨hrr, _⟩, _⟩ := hs'
    subst hrr
    have hmm : m = m₂ := Option.some.inj (hmem.symm.trans hres)
    subst hmm
    have hb := hO hmem hk
    rw [hb] at hbody
    exact Option.noConfusion hbody
  | lit t =>
    have hs := congrArg appsSpine hgen
    rw [appsSpine_foldApps_const] at hs
    have hs' : (Expr.const r ls, xs) = (Expr.lit t, []) := hs
    rw [Prod.mk.injEq] at hs'
    exact Expr.noConfusion hs'.1
  | iota hI =>
    -- hgen : foldApps (const r ls) xs = lhs, hI : DerivedIotaU E lhs y
    obtain ⟨r', ls', m', pre', maj', hshape, hmem', hk', hlen'⟩ :=
      derivedIotaU_head hI
    obtain ⟨hrr, _, hsp⟩ := foldApps_const_inj (hgen.trans hshape)
    subst hrr
    have hmm : m = m' := Option.some.inj (hmem.symm.trans hmem')
    subst hmm
    rw [hsp] at hlt
    exact absurd (hlen' ▸ hlt) (Nat.lt_irrefl _)
  | appHead h' =>
    rename_i f f' a
    -- hgen : foldApps (const r ls) xs = app f a ; h' : WhStep f f'
    have hs := congrArg appsSpine hgen
    rw [appsSpine_foldApps_const] at hs
    simp only [appsSpine] at hs
    rw [Prod.mk.injEq] at hs
    obtain ⟨hc, hsp⟩ := hs
    -- f = foldApps (const r ls) (appsSpine f).2 and xs = (appsSpine f).2 ++ [a]
    have hf : f = foldApps (.const r ls) (appsSpine f).2 := by
      rw [hc]; exact (foldApps_appsSpine f).symm
    have hlt' : (appsSpine f).2.length < piCount m.mtype := by
      rw [hsp, List.length_append, List.length_singleton] at hlt; omega
    exact whStep_foldApps_const_bounded hO hmem hk hlt' (hf ▸ h')
  termination_by xs.length
  decreasing_by rw [hsp]; simp only [List.length_append, List.length_singleton]; omega

/-- An ι redex's head takes no weak-head step under opacity — the `iota × appHead`
collision is impossible. -/
theorem derivedIotaU_no_head_step {E : ResolvedEnv} (hO : RecursorsOpaque E)
    {f a rhs f' : Expr Nat} (hI : DerivedIotaU E (.app f a) rhs) :
    ¬ WhStep E f f' := by
  intro h
  obtain ⟨r, ls, m, pre, maj, hshape, hmem, hk, hlen⟩ := derivedIotaU_head hI
  rw [foldApps_snoc, Expr.app.injEq] at hshape
  obtain ⟨hF, _⟩ := hshape
  have hlt : pre.length < piCount m.mtype := by
    rw [List.length_append, List.length_singleton] at hlen; omega
  exact whStep_foldApps_const_bounded hO hmem hk hlt (hF ▸ h)

/-- **WhDet under opacity**: `WhStep` is deterministic when recursor members are
body-less and derived ι is a partial function. -/
theorem whDet_of_opaque_iotaDet {E : ResolvedEnv} (hO : RecursorsOpaque E)
    (hD : IotaDetU E) : WhDet E := by
  intro a b c h1
  induction h1 generalizing c with
  | beta A b x =>
    intro h2
    cases h2 with
    | beta => rfl
    | appHead h' => exact (whStep_lam_false h').elim
    | iota hI =>
      obtain ⟨r, ls, m, pre, maj, hshape, _, _, _⟩ := derivedIotaU_head hI
      rw [foldApps_snoc, Expr.app.injEq] at hshape
      exact (foldApps_const_ne_lam hshape.1.symm).elim
  | zeta A v b =>
    intro h2
    cases h2 with
    | zeta => rfl
    | iota hI =>
      obtain ⟨r, ls, m, pre, maj, hshape, _, _, _⟩ := derivedIotaU_head hI
      rw [foldApps_snoc] at hshape
      exact Expr.noConfusion hshape
  | delta hres hbody =>
    intro h2
    cases h2 with
    | delta hres' hbody' =>
      have hmm := Option.some.inj (hres.symm.trans hres')
      subst hmm
      have hbb := Option.some.inj (hbody.symm.trans hbody')
      subst hbb
      rfl
    | iota hI =>
      obtain ⟨r, ls, m, pre, maj, hshape, _, _, _⟩ := derivedIotaU_head hI
      exact (foldApps_snoc_ne_const _ _ _ hshape.symm).elim
  | lit t =>
    intro h2
    cases h2 with
    | lit => rfl
    | iota hI =>
      obtain ⟨r, ls, m, pre, maj, hshape, _, _, _⟩ := derivedIotaU_head hI
      rw [foldApps_snoc] at hshape
      exact Expr.noConfusion hshape
  | iota hI =>
    intro h2
    cases h2 with
    | iota hI' => exact hD hI hI'
    | appHead h' => exact (derivedIotaU_no_head_step hO hI h').elim
    | beta =>
      obtain ⟨r, ls, m, pre, maj, hshape, _, _, _⟩ := derivedIotaU_head hI
      rw [foldApps_snoc, Expr.app.injEq] at hshape
      exact (foldApps_const_ne_lam hshape.1.symm).elim
    | zeta =>
      obtain ⟨r, ls, m, pre, maj, hshape, _, _, _⟩ := derivedIotaU_head hI
      rw [foldApps_snoc] at hshape
      exact Expr.noConfusion hshape
    | delta =>
      obtain ⟨r, ls, m, pre, maj, hshape, _, _, _⟩ := derivedIotaU_head hI
      exact (foldApps_snoc_ne_const _ _ _ hshape.symm).elim
    | lit =>
      obtain ⟨r, ls, m, pre, maj, hshape, _, _, _⟩ := derivedIotaU_head hI
      rw [foldApps_snoc] at hshape
      exact Expr.noConfusion hshape
  | appHead h ih =>
    intro h2
    cases h2 with
    | appHead h'' => rw [ih h'']
    | iota hI => exact (derivedIotaU_no_head_step hO hI h).elim
    | beta => exact (whStep_lam_false h).elim

/-- **The side-premise theorem**: `EnvWfT` supplies opacity; the only remaining
content of `WhDet` is `IotaDetU`. -/
theorem whDet_of_envWfT_iotaDet {E : ResolvedEnv} (hW : EnvWfT E)
    (hD : IotaDetU E) : WhDet E :=
  whDet_of_opaque_iotaDet (recursorsOpaque_of_envWfT hW) hD

/-- Minimal restatement of `piRow_of_fundamentalTermD`: `EnvClosed` is free under
`EnvWfT`, and `WhDet` costs exactly `IotaDetU`. -/
theorem piRow_of_fundamentalTermD_of_iotaDet {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hD : IotaDetU E)
    (hS : TypeSoundnessI E n) (F : FundamentalTermD E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
    TyConvT E n Γ (.pi A B) (.pi A' B') →
    Nonempty (TyConvT E n Γ A A') ∧
      Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  piRow_of_fundamentalTermD (envClosed_of_envWfT hW) hW
    (whDet_of_envWfT_iotaDet hW hD) hS F

/-- `whDet_of_envWfT_iotaDet` instantiated at the concrete `True` group. -/
theorem whDet_trueEnvU (hD : IotaDetU trueEnvU) : WhDet trueEnvU :=
  whDet_of_envWfT_iotaDet trueEnvUWfT hD

/-! ### The kernel counterexample: opacity is load-bearing

`detEnv` is `trueEnvU` with the `True.rec` member carrying a δ body `lit 7`.
`EnvWfT` can never produce it — `GroupMembersT.cons` requires `body = none` — but the
member lookup/ι machinery works regardless, and `WhStep detEnv` sends the `True.rec`
redex to two different reducts. -/

/-- `trueRecMemberU` plus a δ body. -/
def trueRecMemberD : CheckedMember :=
  ⟨.recursorM, 1, trueRecTypeU, some (.lit 7)⟩

/-- `trueEnvU` with `trueRecMemberD` in place of `trueRecMemberU`. -/
def detEnv : ResolvedEnv := extendEnv truePrefix 2 trueRecMemberD

/-- The `wTrueRecU` witness transplanted to `detEnv` (all member lookups still
`rfl`-resolve; the witness never inspects `body`). -/
def wTrueRecD : IotaWitness detEnv where
  recRef := 2
  ctorRef := 1
  ls := [.succ (.succ .zero)]
  lsC := []
  recMember := trueRecMemberD
  ctorMember := trueIntroMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.lam (.const 0 []) (.sort (.succ .zero)), .sort .zero]
  fields := []
  ctorParams := []
  kinds := []
  minor := .sort .zero
  hlen := rfl
  familyRef := 0
  famMember := trueFamMember
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
  ctorDoms := []
  ctorResult := .const 0 []
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.pi (.const 0 []) (.sort (.param 0)),
    .app (.bvar 0) (.const 1 []), .const 0 []]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .const 0 []
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- The ι redex `True.rec M S0 tt` in `detEnv` steps by δ-through-`appHead` to
`(lit 7) M S0 tt`. -/
theorem whStep_detEnv_delta :
    WhStep detEnv (iotaLhsOf wTrueRecD)
      (.app (.app (.app (.lit 7)
        (.lam (.const 0 []) (.sort (.succ .zero)))) (.sort .zero))
        (.const 1 [])) := by
  show WhStep detEnv (.app (.app (.app (.const 2 [.succ (.succ .zero)])
      (.lam (.const 0 []) (.sort (.succ .zero)))) (.sort .zero))
      (.const 1 [])) _
  exact .appHead (.appHead (.appHead
    (.delta (rfl : detEnv.members 2 = some trueRecMemberD)
      (rfl : trueRecMemberD.body = some (.lit 7)))))

/-- `WhDet detEnv` is kernel-false: the same redex also steps by ι to `Sort 0`, and
`Sort 0 ≠ (lit 7) M S0 tt`.  So `WhDet` is NOT derivable for arbitrary `ResolvedEnv`;
the opacity consequence of `EnvWfT` is exactly what rules this out. -/
theorem whDet_detEnv_false : ¬ WhDet detEnv := by
  intro h
  have hι : WhStep detEnv (iotaLhsOf wTrueRecD) (iotaRhsOf wTrueRecD) :=
    .iota (.ofU wTrueRecD)
  have heq := h whStep_detEnv_delta hι
  have hrhs : iotaRhsOf wTrueRecD = .sort .zero := rfl
  rw [hrhs] at heq
  exact Expr.noConfusion heq

/-! ## FCD14 — `IotaDetU` discharged: `WhDet` from `EnvWfT` alone

#7656 (`RcicNativePiModelDeltaIota`, landed at `origin/main` before this branch)
proves `PiModelDeltaIotaAudit.iotaDetU_of_envWfT : EnvWfT E → IotaDetU E`: every
`.ofU` (legacy) witness adapts to a `DerivedIotaT` at the same endpoints
(`derivedIotaT_of_iotaWitness_envWfT`, whose proof opens the admitted recursor
cell — the ctor's field data is the analysis the schema witness stores, so legacy
and schema right-hand sides agree), and `iotaDetT` closes both `DerivedIotaT`
derivations on one redex.  The remaining named premise of FCD13's theorems is
therefore discharged; `WhDet E` needs only `EnvWfT E`. -/

/-- `WhDet` in full: weak-head reduction is deterministic at every admitted
environment.  `EnvWfT` supplies recursor opacity (`recursorsOpaque_of_envWfT`)
and union-ι determinism (`iotaDetU_of_envWfT`); together the two load-bearing
premises close (`whDet_detEnv_false` shows opacity is not dispensable). -/
theorem whDet_of_envWfT {E : ResolvedEnv} (hW : EnvWfT E) : WhDet E :=
  whDet_of_envWfT_iotaDet hW (PiModelDeltaIotaAudit.iotaDetU_of_envWfT hW)

/-- `piRow` at `EnvWfT` alone: the two semantic premises that remain are
`TypeSoundnessI` and `FundamentalTermD`; `EnvClosed`, `WhDet`, and `IotaDetU`
are all discharged. -/
theorem piRow_of_fundamentalTermD_of_envWfT {E : ResolvedEnv} {n : Nat}
    (hW : EnvWfT E) (hS : TypeSoundnessI E n) (F : FundamentalTermD E n) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
    TyConvT E n Γ (.pi A B) (.pi A' B') →
    Nonempty (TyConvT E n Γ A A') ∧
      Nonempty (TyConvT E n (.assumption A :: Γ) B B') :=
  piRow_of_fundamentalTermD_of_iotaDet hW
    (PiModelDeltaIotaAudit.iotaDetU_of_envWfT hW) hS F

/-- Concrete pin: the union ι relation is deterministic at `natEnvU`. -/
theorem iotaDetU_natEnvU : IotaDetU natEnvU :=
  PiModelDeltaIotaAudit.iotaDetU_of_envWfT natEnvUWfT

/-- Concrete pin: `WhDet` holds at `natEnvU` with no further premises. -/
theorem whDet_natEnvU : WhDet natEnvU :=
  whDet_of_envWfT natEnvUWfT

/-- Concrete pin: `WhDet` holds at `trueEnvU` with no further premises. -/
theorem whDet_trueEnvU_closed : WhDet trueEnvU :=
  whDet_of_envWfT trueEnvUWfT

end Rcic.Declarative.NativeValleys.PiModelIdealAudit
