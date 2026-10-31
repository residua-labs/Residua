import rcic.RcicTypedInst0Congr
import rcic.RcicTypedInvert
import rcic.RcicTypedWeaken
import rcic.RcicTypedLevels
import rcic.RcicTypedEnvEntry
import rcic.RcicParRedSRTyped
import rcic.RcicDTMetaTyped
import rcic.RcicDTMetaTypedSR
import rcic.RcicCtxMorph
import rcic.RcicEnv
import rcic.RcicIota

/-!
# DT-009 L3 — the typed validity/regularity package at `EnvWfT`

The S0 plan's L3: a two-part mutual giving, inside a well-formed context and
under named fronts only,

* `regularT` — R-2 regularity: `HasTyT Γ e T → Σ' w, HasTyT Γ T (.sort w)`;
* `endpoints3` — `ConvT Γ a b T → (a : T) ×' (b : T) ×' (Σ' w, T : .sort w)`.

Everything is DATA (`HasTyT`, `Σ'`, `×'`): the package's own recursive calls
feed context transports and inversions, which need the derivation itself —
`Nonempty`/`∃` results cannot eliminate into `Type`, so the data level is the
only level the internals can live at. The `Nonempty`-shaped supply props are
produced at the boundary by `⟨·⟩`-wrapping (`*_of_*` adapters below).

The `.3` index field is what breaks the circularity the arm table on #6326
records: `app`/`lam`/`pi`/`letE` need a sort-typing for the codomain (resp. the
domain/value side) to build recursive calls into extended contexts, and that
sort-typing is exactly what `.3` supplies — every recursive call is on a
STRUCTURAL subderivation of the arm's own `ConvT`/`HasTyT` node, never through
DT-009.

FRONTS (all `EnvWfT`-dischargeable except the two named debts):

* `EnvClosed`, `EnvMembersSubstStable` — `envClosed_of_envWfT` /
  `envMembersSubstStable_of_envWfT` (`RcicTypedEnvEntry`).
* `EnvLevelsT`, `IotaLevelsT` — `envWfT_levels` / `iotaLevelsT_of_envWfT`
  (`RcicTypedLevels`).
* `EnvMembersSortTypedT` — every member's stored type is sort-typed at its own
  arity in the empty context; `envWfT_mtypeSortTyped` below walks `EnvWfT`
  (singleton `hA`s, `GroupMembersT.cons`'s `hT`).
* `SubstLetT` — the letBinding head-substitution hole. **Named debt, dttyped
  lane** (`hasTyT_substLet`, S0's L1): consumed by `regularT.letE` and by
  `endpoints3.{zeta, letE}`. Never assumed silently.
* `ConstsRightDataT` — the consts retype, at the data shape the package needs
  (`ConvTConstsRightT`'s `Nonempty` version follows by `⟨·⟩`). **Named debt,
  tymig lane** (`convT_instantiateLevels`): consumed by `endpoints3.consts`'s
  right end only.

WALLS (`W-F05b-PiRow`): Pi/sort-INJECTIVITY is never assumed — every `pi`/`sort`
index fact used here comes from `hasTyTInv_pi` (which inverts a TYPING of a pi,
not a conversion between pis) or from the recursive package itself.

`closure_claim = 0`.
-/

namespace Rcic.Declarative

/-- the letBinding head-substitution hole, as a named front — the data shape
    `hasTyT_substLet` discharges on the dttyped lane (L1). -/
@[reducible] def SubstLetT (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx} {A v e B : Expr Nat},
    HasTyT E n Γ v A →
    HasTyT E n (LocalDecl.letBinding A v :: Γ) e B →
    HasTyT E n Γ (instantiate0 v e) (instantiate0 v B)

/-- `ConvTConstsRightT`'s data-level twin — the shape the package consumes
    (`Nonempty` cannot eliminate into `Type`); the prop supply follows by
    `⟨·⟩`-wrapping, `constsRightDataT_to_prop` below. Named debt, tymig lane. -/
@[reducible] def ConstsRightDataT (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}
    {ls ls' : List Level},
    E.members r = some m → ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true →
    eqNList ls ls' →
    HasTyT E n Γ (.const r ls') (instantiateLevels ls m.mtype)

/-- the debt at the data shape implies the named `ConvTConstsRightT` supply. -/
def convTConstsRightT_of_data (h : ConstsRightDataT E n) :
    ConvTConstsRightT E n :=
  fun {_} hΓ {_ _ _ _} hres hlen hwf hwf' heq =>
    ⟨h hΓ hres hlen hwf hwf' heq⟩

/-- every member's stored type is sort-typed at its own arity, empty context —
    the `EnvWfT` member judgments' face the `const`/`delta`/`consts` arms'
    `.3`s consume. -/
@[reducible] def EnvMembersSortTypedT (E : ResolvedEnv) : Type :=
  ∀ (r : Nat) (m : CheckedMember), E.members r = some m →
    Σ' u, HasTyT E m.arity [] m.mtype (.sort u)

/-- in a well-formed context, every looked-up type is sort-typed — the
    `bvar` arm's regularity fact. -/
def ctxWfT_lookupType_sort (hcl : EnvClosed E) {n : Nat} :
    {Γ : LCtx} → CtxWfT E n Γ → {i : Nat} → {A : Expr Nat} →
    lookupType Γ i = some A →
    Σ' u, HasTyT E n Γ A (.sort u)
  | _, .assumption _ A₀ u hΓ hA, i, A, h => by
      cases i with
      | zero =>
          simp only [lookupType, List.get?_cons_zero] at h
          cases h
          have hw := hasTyTWeaken (.assumption A₀) hcl (c := 0) hA
          simp only [insertAt_zero] at hw
          exact ⟨u, hw⟩
      | succ i =>
          rw [lookupType_cons_succ] at h
          cases hlt : lookupType _ i with
          | none => rw [hlt] at h; cases h
          | some Aᵢ =>
              rw [hlt] at h
              simp only [Option.map_some', Option.some.injEq] at h
              subst h
              have ⟨w, hw⟩ := ctxWfT_lookupType_sort hcl hΓ hlt
              have hw' := hasTyTWeaken (.assumption A₀) hcl (c := 0) hw
              simp only [insertAt_zero] at hw'
              exact ⟨w, hw'⟩
  | _, .letBinding _ A₀ u v hΓ hA hv, i, A, h => by
      cases i with
      | zero =>
          simp only [lookupType, List.get?_cons_zero] at h
          cases h
          have hw := hasTyTWeaken (.letBinding A₀ v) hcl (c := 0) hA
          simp only [insertAt_zero] at hw
          exact ⟨u, hw⟩
      | succ i =>
          rw [lookupType_cons_succ] at h
          cases hlt : lookupType _ i with
          | none => rw [hlt] at h; cases h
          | some Aᵢ =>
              rw [hlt] at h
              simp only [Option.map_some', Option.some.injEq] at h
              subst h
              have ⟨w, hw⟩ := ctxWfT_lookupType_sort hcl hΓ hlt
              have hw' := hasTyTWeaken (.letBinding A₀ v) hcl (c := 0) hw
              simp only [insertAt_zero] at hw'
              exact ⟨w, hw'⟩

/-- the group walk: each cons'd member's `hT` pushes forward through the rest
    of the group's extensions (`hasTyTExt` along `members_extend_preserved`),
    older members defer to the accumulated base. Mirrors
    `envWfT_bodyTypedWalk` (`RcicDTMetaTypedSR`). -/
def envWfT_mtypeSortWalk {E : ResolvedEnv}
    (hbase : ∀ (r : Nat) (m : CheckedMember),
      E.members r = some m →
      Σ' u, HasTyT E m.arity [] m.mtype (.sort u))
    {S : ResolvedEnv} :
    {list : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E list E' →
    ∀ (r : Nat) (m : CheckedMember), E'.members r = some m →
      Σ' u, HasTyT E' m.arity [] m.mtype (.sort u)
  | _, _, .nil _, r, m, hm => hbase r m hm
  | _, _, .cons E₁ r₁ m₁ rest E' hfresh hnobody _ _ _ _ _ _ _ u hT _ _ hrest,
      r, m, hm => by
      have hbase' : ∀ (r : Nat) (m : CheckedMember),
          (extendEnv E₁ r₁ m₁).members r = some m →
          Σ' u, HasTyT (extendEnv E₁ r₁ m₁) m.arity []
            m.mtype (.sort u) := by
        intro r m hmr
        by_cases hrr : r = r₁
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hmr
          cases hmr
          exact ⟨u, hasTyTExt (members_extend_preserved hfresh) hT⟩
        · simp only [extendEnv, if_neg hrr] at hmr
          have ⟨u₀, h₀⟩ := hbase r m hmr
          exact ⟨u₀, hasTyTExt (members_extend_preserved hfresh) h₀⟩
      exact envWfT_mtypeSortWalk hbase' hrest r m hm

/-- `EnvWfT` discharges `EnvMembersSortTypedT`: singletons carry `hA` at
    arity 0; group members carry `hT` inside `GroupMembersT.cons`. -/
def envWfT_mtypeSortTyped {E : ResolvedEnv} (hW : EnvWfT E) :
    EnvMembersSortTypedT E :=
  match hW with
  | .empty => fun r m hm => by simp only [emptyEnv] at hm; cases hm
  | .axiom (arity := arity) E r₀ A u hE hfresh hA hcl hlvl =>
      fun r m hm => by
        have hext := members_extend_preserved
          (m := ⟨.axiomM, arity, A, none⟩) hfresh
        by_cases hrr : r = r₀
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          exact ⟨u, hasTyTExt hext hA⟩
        · simp only [extendEnv, if_neg hrr] at hm
          have ⟨u₀, h₀⟩ := envWfT_mtypeSortTyped hE r m hm
          exact ⟨u₀, hasTyTExt hext h₀⟩
  | .definition E r₀ A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      fun r m hm => by
        have hext := members_extend_preserved
          (m := ⟨.definitionM, 0, A, some v⟩) hfresh
        by_cases hrr : r = r₀
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          exact ⟨u, hasTyTExt hext hA⟩
        · simp only [extendEnv, if_neg hrr] at hm
          have ⟨u₀, h₀⟩ := envWfT_mtypeSortTyped hE r m hm
          exact ⟨u₀, hasTyTExt hext h₀⟩
  | .thm E r₀ A p hE hfresh hA hp hclA hclp hlvlA hlvlp =>
      fun r m hm => by
        have hext := members_extend_preserved
          (m := ⟨.theoremM, 0, A, some p⟩) hfresh
        by_cases hrr : r = r₀
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          exact ⟨.zero, hasTyTExt hext hA⟩
        · simp only [extendEnv, if_neg hrr] at hm
          have ⟨u₀, h₀⟩ := envWfT_mtypeSortTyped hE r m hm
          exact ⟨u₀, hasTyTExt hext h₀⟩
  | .opaque E r₀ A v u hE hfresh hA hv hclA hclv hlvlA hlvlv =>
      fun r m hm => by
        have hext := members_extend_preserved
          (m := ⟨.opaqueM, 0, A, some v⟩) hfresh
        by_cases hrr : r = r₀
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          exact ⟨u, hasTyTExt hext hA⟩
        · simp only [extendEnv, if_neg hrr] at hm
          have ⟨u₀, h₀⟩ := envWfT_mtypeSortTyped hE r m hm
          exact ⟨u₀, hasTyTExt hext h₀⟩
  | .group _ _ _ _ _ _ _ hE _ _ _ hmem =>
      envWfT_mtypeSortWalk (envWfT_mtypeSortTyped hE) hmem

/-- the gap-corner companion of `instantiate_lift_id`: instantiating slot `j`
    by `.bvar j` itself inside a `lift (j+1) 1` gap leaves the term unchanged —
    the replacement re-fills the unshifted `bvar j`, the shifted tail
    decrements back. The `eta` arm's `inst0 (bvar 0) (lift 1 1 B) = B` is the
    `j = 0` corner. -/
private theorem instantiate_bvar_lift_gap (j : Nat) (e : Expr Nat) :
    instantiate j (.bvar j) (lift (j+1) 1 e) = e := by
  induction e generalizing j with
  | bvar i =>
      simp only [lift]
      split
      · simp only [instantiate]
        rw [if_neg (by omega : ¬ i + 1 = j), if_pos (by omega : j < i + 1)]
        exact congrArg Expr.bvar (Nat.add_sub_cancel i 1)
      · simp only [instantiate]
        by_cases h2 : i = j
        · subst h2; rw [if_pos rfl]
        · rw [if_neg (by omega : ¬ i = j), if_neg (by omega : ¬ j < i)]
  | sort l => rfl
  | const r ls => rfl
  | lit t => rfl
  | app f x ihf ihx => simp only [lift, instantiate, ihf, ihx]
  | lam a b iha ihb =>
      simp only [lift, instantiate, iha]
      rw [if_pos (Nat.zero_le j)]
      exact congrArg (Expr.lam a) (ihb (j+1))
  | pi a b iha ihb =>
      simp only [lift, instantiate, iha]
      rw [if_pos (Nat.zero_le j)]
      exact congrArg (Expr.pi a) (ihb (j+1))
  | letE a v b iha ihv ihb =>
      simp only [lift, instantiate, iha, ihv]
      rw [if_pos (Nat.zero_le j)]
      exact congrArg (Expr.letE a v) (ihb (j+1))

/-- the member `mtype`, instantiated at `ls`, is sort-typed at `(n, Γ)` — the
    `const`/`delta`/`consts` `.3` leg, in front form. -/
def instMtypeSort (hcl : EnvClosed E) (hms : EnvMembersSortTypedT E)
    (hEL : EnvLevelsT E) (hIL : IotaLevelsT E) {n : Nat} {Γ : LCtx}
    {r : Nat} {m : CheckedMember} {ls : List Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) :
    Σ' w, HasTyT E n Γ (instantiateLevels ls m.mtype) (.sort w) := by
  have ⟨u, hT⟩ := hms r m hres
  have hclm := (hcl r m hres).1
  have hti := hasTyT_instLevels hEL hIL hwf hlen hT
  have hw := hasTyTLiftPrefix hcl Γ hti
  simp only [List.append_nil, instLvlsCtx, List.map_nil,
    lift_instantiateLevels, lift] at hw
  rw [lift_of_closed _ (hclm 0)] at hw
  exact ⟨instLevel ls u, hw⟩

/- The typed validity/regularity package: `regularT` on `HasTyT`,
   `endpoints3` on `ConvT`, mutually recursive over the derivations. -/
mutual

def regularT {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hSL : SubstLetT E n) (hms : EnvMembersSortTypedT E)
    (hEL : EnvLevelsT E) (hIL : IotaLevelsT E)
    (hconst : ConstsRightDataT E n) :
    {Γ : LCtx} → {e T : Expr Nat} → HasTyT E n Γ e T →
    CtxWfT E n Γ → Σ' w, HasTyT E n Γ T (.sort w)
  | _, _, _, .sort Γ l, _ =>
      ⟨.succ (.succ l), .sort Γ (.succ l)⟩
  | _, _, _, .bvar Γ i A h, hΓ => ctxWfT_lookupType_sort hcl hΓ h
  | _, _, _, .const Γ r ls m hres hlen hwf, _ =>
      instMtypeSort hcl hms hEL hIL hres hlen hwf
  | _, _, _, .pi Γ A u B v hA hB, _ =>
      ⟨.succ (.imax u v), .sort Γ (.imax u v)⟩
  | _, _, _, .lam Γ A u body B hA hbody, hΓ => by
      have ⟨v, hB⟩ := regularT hcl hinst hSL hms hEL hIL hconst
        hbody (.assumption Γ A u hΓ hA)
      exact ⟨.imax u v, .pi Γ A u B v hA hB⟩
  | _, _, _, .app Γ f a A B hf ha, hΓ => by
      have ⟨w, hpi⟩ := regularT hcl hinst hSL hms hEL hIL hconst hf hΓ
      have ⟨u, v, hA, hB, _⟩ := hasTyTInv_pi hpi rfl
      exact ⟨v, hasTyT_subst0S hcl hinst hB ha⟩
  | _, _, _, .letE Γ A u v B body hA hv hb, hΓ => by
      have ⟨w, hB⟩ := regularT hcl hinst hSL hms hEL hIL hconst
        hb (.letBinding Γ A u v hΓ hA hv)
      exact ⟨w, hSL hv hB⟩
  | _, _, _, .lit Γ t T hexp, hΓ =>
      regularT hcl hinst hSL hms hEL hIL hconst hexp hΓ
  | _, _, _, .conv Γ e A B u h hc, hΓ =>
      ⟨u, (endpoints3 hcl hinst hSL hms hEL hIL hconst hc hΓ).2.1⟩

def endpoints3 {E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hSL : SubstLetT E n) (hms : EnvMembersSortTypedT E)
    (hEL : EnvLevelsT E) (hIL : IotaLevelsT E)
    (hconst : ConstsRightDataT E n) :
    {Γ : LCtx} → {a b T : Expr Nat} → ConvT E n Γ a b T →
    CtxWfT E n Γ →
    HasTyT E n Γ a T ×' HasTyT E n Γ b T ×'
    (Σ' w, HasTyT E n Γ T (.sort w))
  | Γ, _, _, _, .refl _ _ _ h, hΓ =>
      ⟨h, h, regularT hcl hinst hSL hms hEL hIL hconst h hΓ⟩
  | Γ, _, _, _, .symm _ _ _ _ h, hΓ =>
      let ⟨ha, hb, hi⟩ := endpoints3 hcl hinst hSL hms hEL hIL hconst h hΓ
      ⟨hb, ha, hi⟩
  | Γ, _, _, _, .trans _ _ _ _ _ h1 h2, hΓ =>
      let ⟨ha, _, hi⟩ := endpoints3 hcl hinst hSL hms hEL hIL hconst h1 hΓ
      let ⟨_, hb, _⟩ := endpoints3 hcl hinst hSL hms hEL hIL hconst h2 hΓ
      ⟨ha, hb, hi⟩
  | Γ, _, _, _, .beta _ A body arg B u hA hbody harg, hΓ =>
      let hΓA : CtxWfT E n (.assumption A :: Γ) :=
        .assumption Γ A u hΓ hA
      let ⟨w, hBw⟩ := regularT hcl hinst hSL hms hEL hIL hconst hbody hΓA
      ⟨.app Γ (.lam A body) arg A B (.lam Γ A u body B hA hbody) harg,
        hasTyT_subst0S hcl hinst hbody harg,
        ⟨w, hasTyT_subst0S hcl hinst hBw harg⟩⟩
  | Γ, _, _, _, .zeta _ A value body B u hA hv hb, hΓ =>
      let hΓl : CtxWfT E n (.letBinding A value :: Γ) :=
        .letBinding Γ A u value hΓ hA hv
      let ⟨w, hBw⟩ := regularT hcl hinst hSL hms hEL hIL hconst hb hΓl
      ⟨.letE Γ A u value B body hA hv hb,
        hSL hv hb,
        ⟨w, hSL hv hBw⟩⟩
  | Γ, _, _, _, .zetaLocal _ i A v hval hty hv, hΓ =>
      ⟨.bvar Γ i A hty, hv,
        regularT hcl hinst hSL hms hEL hIL hconst hv hΓ⟩
  | Γ, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb, _ =>
      ⟨.const Γ r ls m hres hlen hwf, hb,
        instMtypeSort hcl hms hEL hIL hres hlen hwf⟩
  | Γ, _, _, _, .iota _ _ _ _ _ hlhs hrhs, hΓ =>
      ⟨hlhs, hrhs,
        regularT hcl hinst hSL hms hEL hIL hconst hlhs hΓ⟩
  | Γ, _, _, _, .lit _ t _ _ (.of _) hexp, hΓ =>
      ⟨.lit Γ t _ hexp, hexp,
        regularT hcl hinst hSL hms hEL hIL hconst hexp hΓ⟩
  | Γ, _, _, _, .app _ f g a b A B h1 h2, hΓ =>
      let ⟨hf, hg, hpiw⟩ :=
        endpoints3 hcl hinst hSL hms hEL hIL hconst h1 hΓ
      let ⟨ha, hb, _⟩ := endpoints3 hcl hinst hSL hms hEL hIL hconst h2 hΓ
      let ⟨w, hpi⟩ := hpiw
      let ⟨u, v, hA, hB, _⟩ := hasTyTInv_pi hpi rfl
      let hcBA : ConvT E n Γ b a A := .symm _ _ _ _ h2
      let hcongr : ConvT E n Γ (instantiate0 b B) (instantiate0 a B)
          (.sort v) :=
        convT_inst0_sortCongr hA hB hb ha hcBA
      let happ : HasTyT E n Γ (.app g b) (instantiate0 b B) :=
        .app Γ g b A B hg hb
      ⟨.app Γ f a A B hf ha,
        .conv Γ _ _ _ _ happ hcongr,
        ⟨v, hasTyT_subst0S hcl hinst hB ha⟩⟩
  | Γ, _, _, _, .lam _ A A' b b' B u hA hb, hΓ =>
      let ⟨hAdom, hAdom', _⟩ :=
        endpoints3 hcl hinst hSL hms hEL hIL hconst hA hΓ
      let hΓA : CtxWfT E n (.assumption A :: Γ) :=
        .assumption Γ A u hΓ hAdom
      let ⟨hbl, hbr, hBw⟩ :=
        endpoints3 hcl hinst hSL hms hEL hIL hconst hb hΓA
      let hsymm : ConvT E n Γ A' A (.sort u) := .symm _ _ _ _ hA
      let hbr' := hasTyTConvAssump hcl hsymm hbr
      let ⟨w, hBw'⟩ := hBw
      let hBw'' := hasTyTConvAssump hcl hsymm hBw'
      ⟨.lam Γ A u b B hAdom hbl,
        .conv Γ _ _ _ _ (.lam Γ A' u b' B hAdom' hbr')
          (.pi Γ A' A B B u w hsymm (.refl _ _ _ hBw'')),
        ⟨.imax u w, .pi Γ A u B w hAdom hBw'⟩⟩
  | Γ, _, _, _, .pi _ A A' B B' u v hA hB, hΓ =>
      let ⟨hAl, hAr, _⟩ := endpoints3 hcl hinst hSL hms hEL hIL hconst hA hΓ
      let hΓA : CtxWfT E n (.assumption A :: Γ) :=
        .assumption Γ A u hΓ hAl
      let ⟨hBl, hBr, _⟩ :=
        endpoints3 hcl hinst hSL hms hEL hIL hconst hB hΓA
      let hsymm : ConvT E n Γ A' A (.sort u) := .symm _ _ _ _ hA
      let hBr' := hasTyTConvAssump hcl hsymm hBr
      ⟨.pi Γ A u B v hAl hBl,
        .pi Γ A' u B' v hAr hBr',
        ⟨.succ (.imax u v), .sort Γ (.imax u v)⟩⟩
  | Γ, _, _, _, .letE _ A A' v v' b b' B u hA hv hb, hΓ =>
      let ⟨hAl, hAr, _⟩ := endpoints3 hcl hinst hSL hms hEL hIL hconst hA hΓ
      let ⟨hvl, hvr, _⟩ := endpoints3 hcl hinst hSL hms hEL hIL hconst hv hΓ
      let hΓA : CtxWfT E n (.letBinding A v :: Γ) :=
        .letBinding Γ A u v hΓ hAl hvl
      let ⟨hbl, hbr, hBw⟩ :=
        endpoints3 hcl hinst hSL hms hEL hIL hconst hb hΓA
      -- right end: letE A' v' b' typed at inst0 v' B, retype to inst0 v B
      let hsA : ConvT E n Γ A' A (.sort u) := .symm _ _ _ _ hA
      let hsv : ConvT E n Γ v' v A := .symm _ _ _ _ hv
      -- v' at the NEW domain A': transport its typing along hA
      let hvrA' : HasTyT E n Γ v' A' := .conv Γ _ _ _ _ hvr hA
      let hbr' := hasTyTConvLet hcl hsA hsv hvrA' hbr
      let ⟨w, hBw'⟩ := hBw
      -- B's sort-typing under letBinding A v' — transport with A fixed (refl)
      let hBw'' : HasTyT E n (.letBinding A v' :: Γ) B (.sort w) :=
        hasTyTConvLet hcl (.refl _ _ _ hAl) hsv hvr hBw'
      let hcongr : ConvT E n Γ (instantiate0 v B) (instantiate0 v' B)
          (.sort w) :=
        convT_inst0_sortCongrLet hAl hBw' hBw'' hvl hvr hv
      let hlet : HasTyT E n Γ (.letE A' v' b') (instantiate0 v' B) :=
        .letE Γ A' u v' B b' hAr hvrA' hbr'
      -- .3: inst0 v B sort-typed, via the named SubstLetT debt
      let hsub := hSL hvl hBw'
      ⟨.letE Γ A u v B b hAl hvl hbl,
        .conv Γ _ _ _ _ hlet (.symm _ _ _ _ hcongr),
        ⟨w, hsub⟩⟩
  | Γ, _, _, _, .sorts _ l₁ l₂ h, hΓ =>
      ⟨.sort Γ l₁,
        .conv Γ _ _ _ _ (.sort Γ l₂)
          (.sorts Γ (.succ l₂) (.succ l₁)
            fun ρ => congrArg (Option.map (· + 1)) (h ρ).symm),
        ⟨.succ (.succ l₁), .sort Γ (.succ l₁)⟩⟩
  | Γ, _, _, _, .consts _ r ls ls' m hres hlen hwf hwf' h, hΓ =>
      ⟨.const Γ r ls m hres hlen hwf,
        hconst hΓ hres hlen hwf hwf' h,
        instMtypeSort hcl hms hEL hIL hres hlen hwf⟩
  | Γ, _, _, _, .eta _ f A B h, hΓ => by
      have ⟨w, hpi⟩ := regularT hcl hinst hSL hms hEL hIL hconst h hΓ
      have ⟨u, v, hA, hB, _⟩ := hasTyTInv_pi hpi rfl
      have hf' := hasTyTWeaken (.assumption A) hcl (c := 0) h
      simp only [insertAt_zero] at hf'
      have hb0 : HasTyT E n (.assumption A :: Γ) (.bvar 0) (lift 0 1 A) :=
        .bvar _ 0 _ rfl
      have happ : HasTyT E n (.assumption A :: Γ)
          (.app (lift 0 1 f) (.bvar 0)) (instantiate0 (.bvar 0) (lift 1 1 B)) :=
        .app _ _ _ _ _ hf' hb0
      rw [show instantiate0 (.bvar 0) (lift 1 1 B) = B from
        instantiate_bvar_lift_gap 0 B] at happ
      have hlam : HasTyT E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0)))
          (.pi A B) := .lam Γ A u _ B hA happ
      exact ⟨hlam, h, ⟨w, hpi⟩⟩
  | Γ, _, _, _, .irr _ P p q hP hp hq, _ =>
      ⟨hp, hq, ⟨.zero, hP⟩⟩
  | Γ, _, _, _, .tyConv _ a b A A' u h hA, hΓ =>
      let ⟨ha, hb, _⟩ := endpoints3 hcl hinst hSL hms hEL hIL hconst h hΓ
      let ⟨_, hA', _⟩ := endpoints3 hcl hinst hSL hms hEL hIL hconst hA hΓ
      ⟨.conv Γ _ _ _ _ ha hA, .conv Γ _ _ _ _ hb hA, ⟨u, hA'⟩⟩

end

/-- the EnvWfT-fronted regularity: R-2 paid at the typed entry, the two named
    debts still explicit. -/
def regularT_of_envWfT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e T : Expr Nat}
    (h : HasTyT E n Γ e T) :
    Σ' w, HasTyT E n Γ T (.sort w) :=
  regularT (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
    hSL (envWfT_mtypeSortTyped hW) (envWfT_levels hW)
    (iotaLevelsT_of_envWfT hW) hconst h hΓ

/-- the EnvWfT-fronted three-part endpoint package. -/
def endpoints3_of_envWfT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b T : Expr Nat}
    (h : ConvT E n Γ a b T) :
    HasTyT E n Γ a T ×' HasTyT E n Γ b T ×'
    (Σ' w, HasTyT E n Γ T (.sort w)) :=
  endpoints3 (envClosed_of_envWfT hW) (envMembersSubstStable_of_envWfT hW)
    hSL (envWfT_mtypeSortTyped hW) (envWfT_levels hW)
    (iotaLevelsT_of_envWfT hW) hconst h hΓ

/-! ## L4 — six supply projections

Each supply is an endpoint read off the corresponding `ConvT` rule through
`endpoints3_of_envWfT` — left for `eta`, right for the rest — wrapped into the
`Nonempty`-shaped prop. The two named fronts stay explicit arguments:
`SubstLetT` (dttyped lane, L1 `hasTyT_substLet`) and `ConstsRightDataT`
(tymig lane, `convT_instantiateLevels`). `ConvTConstsRightT` itself stays OPEN:
its prop adapter `convTConstsRightT_of_data` is above, but the data front is
the tymig debt. -/

/-- `eta`'s left endpoint — the lam side typed at the rule's own `pi A B`. -/
def convTEtaLeftT_of_envWfT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n) :
    ConvTEtaLeftT E n :=
  fun {_} hΓ {_ _ _} hf =>
    ⟨(endpoints3_of_envWfT hW hSL hconst hΓ (.eta _ _ _ _ hf)).1⟩

/-- `app`'s right endpoint at the left argument's instantiation. -/
def convTAppRightT_of_envWfT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n) :
    ConvTAppRightT E n :=
  fun {_} hΓ {_ _ _ _ _ _} h1 h2 =>
    ⟨(endpoints3_of_envWfT hW hSL hconst hΓ
        (.app _ _ _ _ _ _ _ h1 h2)).2.1⟩

/-- `lam`'s right endpoint at the rule's index `pi A B`. -/
def convTLamRightT_of_envWfT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n) :
    ConvTLamRightT E n :=
  fun {_} hΓ {_ _ _ _ _ _} hA hb =>
    ⟨(endpoints3_of_envWfT hW hSL hconst hΓ
        (.lam _ _ _ _ _ _ _ hA hb)).2.1⟩

/-- `pi`'s right endpoint at `sort (imax u v)`. -/
def convTPiRightT_of_envWfT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n) :
    ConvTPiRightT E n :=
  fun {_} hΓ {_ _ _ _ _ _} hA hB =>
    ⟨(endpoints3_of_envWfT hW hSL hconst hΓ
        (.pi _ _ _ _ _ _ _ hA hB)).2.1⟩

/-- `letE`'s right endpoint at `instantiate0 v B`. -/
def convTLetRightT_of_envWfT {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    (hSL : SubstLetT E n) (hconst : ConstsRightDataT E n) :
    ConvTLetRightT E n :=
  fun {_} hΓ {_ _ _ _ _ _ _ _} hA hv hb =>
    ⟨(endpoints3_of_envWfT hW hSL hconst hΓ
        (.letE _ _ _ _ _ _ _ _ _ hA hv hb)).2.1⟩

/-- the zeta supply IS the L1 debt read at prop level — it is paid the moment
    the dttyped lane lands `hasTyT_substLet`; the `A : sort u` premise the
    supply carries is not needed by the debt's own shape. -/
def convTZetaRightT_of_substLet {E : ResolvedEnv} {n : Nat}
    (hSL : SubstLetT E n) : ConvTZetaRightT E n :=
  fun {_} _ {_ _ _ _ _} _ hv hb => ⟨hSL hv hb⟩

/-! ## pins -/

/-- PIN (front leg, concrete): `instMtypeSort` discharges the `.3` leg at
    `pinDefEnvU`'s definition member (ref 4, `Sort 0 : Sort 1`, arity 0) —
    `instantiateLevels []` is the identity, so the result is the member's type
    sort-typed at `[]`. -/
def pin_instMtypeSort_pinDefEnvU {n : Nat} :
    Σ' w, HasTyT pinDefEnvU n [] (instantiateLevels [] (.sort (.succ .zero)))
      (.sort w) :=
  instMtypeSort (envClosed_of_envWfT pinDefEnvUWfT)
    (envWfT_mtypeSortTyped pinDefEnvUWfT) (envWfT_levels pinDefEnvUWfT)
    (iotaLevelsT_of_envWfT pinDefEnvUWfT)
    (r := 4) (m := ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩)
    (ls := []) rfl rfl rfl

/-- PIN (member sort-typing front): the same member's stored type reads back
    its own sort-typing at its own arity, empty context — the walk over
    `EnvWfT.definition`'s `hA`. -/
def pin_envWfT_mtypeSortTyped_pinDefEnvU :
    Σ' u, HasTyT pinDefEnvU 0 [] (.sort (.succ .zero)) (.sort u) :=
  envWfT_mtypeSortTyped pinDefEnvUWfT 4
    ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩ rfl

/-- PIN (debt shape): the named `SubstLetT` front is exactly the letBinding
    head-substitution hole — a definitional `rfl` pin so the debt boundary
    cannot silently drift. -/
theorem pin_SubstLetT_shape (E : ResolvedEnv) (n : Nat) :
    SubstLetT E n =
      (∀ {Γ : LCtx} {A v e B : Expr Nat},
        HasTyT E n Γ v A →
        HasTyT E n (LocalDecl.letBinding A v :: Γ) e B →
        HasTyT E n Γ (instantiate0 v e) (instantiate0 v B)) := rfl

/-- PIN (debt shape): `ConstsRightDataT` is exactly the consts-right data
    shape — the tymig lane's `convT_instantiateLevels` target. -/
theorem pin_ConstsRightDataT_shape (E : ResolvedEnv) (n : Nat) :
    ConstsRightDataT E n =
      (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}
        {ls ls' : List Level},
        E.members r = some m → ls.length = m.arity →
        levelsBounded n ls = true → levelsBounded n ls' = true →
        eqNList ls ls' →
        HasTyT E n Γ (.const r ls') (instantiateLevels ls m.mtype)) := rfl

end Rcic.Declarative
