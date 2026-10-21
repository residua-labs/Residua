import rcic.RcicSynStepFields5

/-!
# `es_app` closed-lane discharge (`RcicSynClosedEsapp`)

The swe-esapp lane of the sortRow supplier batch: `StepSuppliers.es_app`,
whose landed conditional filler is `es_app_field` (`RcicSynStepFields5`) over
the explicit `AppPorts` residue.

## Measurement (per `BELOWC_FAILED_READERS_AND_LET_BODY` §3.3/§4.1)

`AppPorts` lists twelve residual fields. Revised census after audit:

* `occH1`, `occH2` — `∃ p, q.subAt 0 p = some (.ty hᵢ.dr)`. `CvP.dr` is a
  stored `dchildren` field for every non-transport `CvP`
  (`cv_dr_subAt`), so the receipt is **discharged whenever
  `hᵢ.isTransport = false`** (`es_app_occH1_closed`, `es_app_occH2_closed`).
  Residue: transport-headed `hᵢ` (`CvP.dr` re-wraps; not a forest member).
* `occF`, `occA` — `∃ p, q.subAt 0 p = some (.ty (appSource dr rfl).h·)`.
  `appSource`/`TyP.appSrc` peels `.conv` and otherwise re-wraps along the
  transport spine. **Discharged whenever `dr` is `TyP.app`-headed at depth 0
  or under one `.conv`** (`DrAppHead`): the decoded sources are the stored
  `hf`/`ha` at `[3,0]`/`[3,1]` (depth 0) or `[3,0,0]`/`[3,0,1]` (under the
  conv wrapper) — `drAppHead_occF`, `drAppHead_occA`. Residue: deeper
  transport spines (`wk`/`esub`/`lsub`/`linst`/`ewk`/`cctx`).
* `leftCl` — `CL[dl, appLeftSurface]`. The fresh surface sits at no `subAt`
  path and `occ_cl` cannot reach it; in general it needs the §4.1
  `AppClauseNeed(dl)` worker. **Discharged when `dl` is literally the surface
  node** (`es_app_leftCl_self_closed`); open in general.
* `pbFunL`, `pbFunR`, `pbArgL`, `pbArgR` — `PB[·, ·.reg.2]`. `D.reg.2` IS a
  stored `dchildren` child whenever `D`'s head is `bvar` (`[0]`), `const`
  (`[0]`), `app` (`[2]`), `letE` (`[3]`), or `conv` over a rule-headed `CvP`
  (`1 :: p`, `ty_reg_subAt_conv`), and `hᵢ.dl` is a stored `dchildren` child
  for every non-transport `hᵢ` (`cv_dl_subAt`). Composing the two paths
  (`DNode.subAt_append`, `es_app_occReg{1,2}`) gives `subAt` receipts for
  both `PBit` arguments, so **`occ_pb` + `StepIH` discharges all four**
  (`es_issued_occ_pb`) on the `RegSubAt` sub-domain. Residue: `hᵢ.dl` headed
  by `sort`/`pi`/`lam`/`lit`/transport ctors (whose `reg` output is a fresh
  re-wrap, not a child) and transport-headed `hᵢ`.
* `funTag`, `argTag` — `TagCoh[hᵢ.dr, cast ▸ R.h·]`. When additionally
  `(appSource dr rfl).A = A` (and `.B = B` for the function side), the decoded
  source's ascribed type is the shared `.pi A B`/`A`, so `occ_pb` issues
  `PB[R.h·, hᵢ.dl.reg.2]` and `PB[hᵢ.dr, hᵢ.dl.reg.2]` against the SAME sort
  typing — the `Iff` chain gives `TagCoh` (`displayEps = eps`). **Discharged
  on the same `RegSubAt` sub-domain plus the decoded-`pi` equation**; open
  otherwise (no `tagCoh` row exists).
* `drClause` — `dr.eps = appClause (R.hf.eps) (R.ha.eps)`. `TyP.eps` peels
  `.conv`, so on `DrAppHead` it reduces to `eps_app_appClause` on the inner
  `TyP.app` — **discharged** (`drAppHead_clause`); open for transport spines.

## `EsAppClosedPorts` is strictly weaker than `AppPorts`

Every field is the original `AppPorts` field **`∨` its discharge receipt**
(shape condition or `subAt` occurrence data), so `AppPorts →
EsAppClosedPorts` pointwise (`esAppClosedPorts_of_appPorts`) — the premise is
weakened, never strengthened. `es_app_field_closed` discharges the receipts
through `StepIH` and re-enters `es_app_field`. The `esappFixture` block shows
all twelve fields inhabited from shape data alone (zero `PBit`/`TagCoh`
hypotheses).

`closure_claim` stays 0: residues are the `RegSubAt`/`DrAppHead`/`isTransport`
sub-domain boundaries and the `a ≠ b`-indexed `leftCl` worker case.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `dl`/`dr`/`reg` occurrence receipts -/

/-- For a non-transport `CvP` node, `CvP.dl` is the stored `dl` field — a
    `dchildren` member at the index its constructor fixes. -/
theorem cv_dl_subAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : CvP E n Γ a b T) (hc : c.isTransport = false) :
    ∃ p, (DNode.cv c).subAt p = some (.ty c.dl) := by
  cases c with
  | wk => simp [CvP.isTransport] at hc
  | esub => simp [CvP.isTransport] at hc
  | linst => simp [CvP.isTransport] at hc
  | ewk => simp [CvP.isTransport] at hc
  | cctx => simp [CvP.isTransport] at hc
  | refl => exact ⟨[1], rfl⟩
  | symm => exact ⟨[1], rfl⟩
  | trans => exact ⟨[2], rfl⟩
  | beta => exact ⟨[3], rfl⟩
  | zeta => exact ⟨[3], rfl⟩
  | zetaLocal => exact ⟨[1], rfl⟩
  | delta => exact ⟨[1], rfl⟩
  | iota => exact ⟨[2], rfl⟩
  | lit => exact ⟨[1], rfl⟩
  | app => exact ⟨[2], rfl⟩
  | lam => exact ⟨[2], rfl⟩
  | pi => exact ⟨[2], rfl⟩
  | letE => exact ⟨[3], rfl⟩
  | sorts => exact ⟨[0], rfl⟩
  | consts => exact ⟨[0], rfl⟩
  | eta => exact ⟨[1], rfl⟩
  | irr => exact ⟨[3], rfl⟩
  | tyConv => exact ⟨[2], rfl⟩
  | fsub => exact ⟨[3], rfl⟩

/-- For a non-transport `CvP` node, `CvP.dr` is the stored `dr` field. -/
theorem cv_dr_subAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : CvP E n Γ a b T) (hc : c.isTransport = false) :
    ∃ p, (DNode.cv c).subAt p = some (.ty c.dr) := by
  cases c with
  | wk => simp [CvP.isTransport] at hc
  | esub => simp [CvP.isTransport] at hc
  | linst => simp [CvP.isTransport] at hc
  | ewk => simp [CvP.isTransport] at hc
  | cctx => simp [CvP.isTransport] at hc
  | refl => exact ⟨[2], rfl⟩
  | symm => exact ⟨[2], rfl⟩
  | trans => exact ⟨[3], rfl⟩
  | beta => exact ⟨[4], rfl⟩
  | zeta => exact ⟨[4], rfl⟩
  | zetaLocal => exact ⟨[2], rfl⟩
  | delta => exact ⟨[2], rfl⟩
  | iota => exact ⟨[3], rfl⟩
  | lit => exact ⟨[2], rfl⟩
  | app => exact ⟨[3], rfl⟩
  | lam => exact ⟨[3], rfl⟩
  | pi => exact ⟨[3], rfl⟩
  | letE => exact ⟨[4], rfl⟩
  | sorts => exact ⟨[1], rfl⟩
  | consts => exact ⟨[1], rfl⟩
  | eta => exact ⟨[2], rfl⟩
  | irr => exact ⟨[4], rfl⟩
  | tyConv => exact ⟨[3], rfl⟩
  | fsub => exact ⟨[4], rfl⟩

/-- `D.reg.2` sits at a `dchildren` path of `D` — true exactly on the heads
    where `TyP.reg` returns a stored field: `bvar`/`const`/`app`/`letE`, and
    `conv` whose conversion is rule-headed (then `reg.2 = hc.dr`, one step
    inside the `.cv hc` child). -/
def TyP.RegSubAt {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) : Prop :=
  ∃ p, (DNode.ty D).subAt p = some (.ty D.reg.2)

/-- `bvar`'s regularity is its stored type-sort `hA` — child `[0]`. -/
theorem ty_reg_subAt_bvar {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {A : Expr Nat} {u : Level}
    (h : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u)) :
    TyP.RegSubAt (TyP.bvar E n Γ i A u h hA) :=
  ⟨[0], rfl⟩

/-- `const`'s regularity is its stored sort typing `hT` — child `[0]`. -/
theorem ty_reg_subAt_const {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls ls₀ : List Level} {m : CheckedMember} {u : Level}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hls : eqNList ls ls₀)
    (hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)) :
    TyP.RegSubAt (TyP.const E n Γ r ls ls₀ m u hres hlen hwf hls hT) :=
  ⟨[0], rfl⟩

/-- `app`'s regularity is its stored `hT` — child `[2]`. -/
theorem ty_reg_subAt_app {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a A B : Expr Nat} {w : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w)) :
    TyP.RegSubAt (TyP.app E n Γ f a A B w hf ha hT) :=
  ⟨[2], rfl⟩

/-- `letE`'s regularity is its stored `hT` — child `[3]`. -/
theorem ty_reg_subAt_letE {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {value B body : Expr Nat} {w : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w)) :
    TyP.RegSubAt (TyP.letE E n Γ A u value B body w hA hv hb hT) :=
  ⟨[3], rfl⟩

/-- `conv`'s regularity is `hc.dr` — one step inside the `.cv hc` child when
    `hc` is rule-headed (`cv_dr_subAt`). -/
theorem ty_reg_subAt_conv {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e A B : Expr Nat} {u : Level}
    (h : TyP E n Γ e A) (hc : CvP E n Γ A B (.sort u))
    (ht : hc.isTransport = false) :
    TyP.RegSubAt (TyP.conv E n Γ e A B u h hc) := by
  obtain ⟨p, hp⟩ := cv_dr_subAt hc ht
  exact ⟨1 :: p, hp⟩

/-! ## §2 `occ_pb` issuance (mirror of `es_issued_occ_cl`) -/

/-- `PBit σ ρ D DT` for two `subAt`-reachable derivations of an `es c` query
    at a non-transport conversion node: `Issues.occ_pb` +
    `DNode.subAt_wt_lt` + `dmStep_pair_below`. -/
theorem es_issued_occ_pb (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : CvP E n Γ a b T) (hc : c.isTransport = false)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    {e T' : Expr Nat} {u : Level}
    (D : TyP E n Γ e T') (DT : TyP E n Γ T' (.sort u))
    (p₁ p₂ : List Nat)
    (hocc₁ : P2Query.subAt (.es c S σ ρ) 0 p₁ = some (.ty D))
    (hocc₂ : P2Query.subAt (.es c S σ ρ) 0 p₂ = some (.ty DT))
    (hap₁ : D.AssumpPref) (hap₂ : DT.AssumpPref)
    (hq : Demand (.es c S σ ρ)) (ih : StepIH Aw tbl (.es c S σ ρ)) :
    PBit σ ρ D DT := by
  have hp₁ : p₁ ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hocc₁
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hocc₁
    exact DNode.noConfusion (Option.some.inj hocc₁)
  have hp₂ : p₂ ≠ [] := by
    rintro rfl
    rw [P2Query.subAt] at hocc₂
    simp only [P2Query.payload, List.getElem?_cons_zero, Option.some_bind,
      DNode.subAt] at hocc₂
    exact DNode.noConfusion (Option.some.inj hocc₂)
  have hw₁ : D.wt Aw < c.wt Aw :=
    DNode.subAt_wt_lt Aw p₁ hp₁ _ _ hocc₁
  have hw₂ : DT.wt Aw < c.wt Aw :=
    DNode.subAt_wt_lt Aw p₂ hp₂ _ _ hocc₂
  exact ih_issue Aw tbl hq ih (.pb D DT S σ ρ)
    (Issues.occ_pb hocc₁ hocc₂ hap₁ hap₂)
    (before_of_same_prefix Aw rfl (lexDM_combMeas_mono Aw _
      (lex_of_dm (dmStep_pair_below Aw c hc D DT hw₁ hw₂))))

/-! ## §3 the `dr` application head (`DrAppHead`) -/

/-- `dr` headed by a literal `TyP.app`, either directly or under one outer
    `.conv` — the canonical right endpoint `conv (TyP.app g b A' B' w hf ha hT) hc`
    of a `CvP.app` with `a ≠ b` is the `.inr` branch. On this shape
    `appSource`/`TyP.appSrc` peel the conv and return the stored `hf`/`ha`
    unchanged (`feq`/`aeq` are `rfl`).

    The bare branch carries the type-index cast `hTe : inst b B' = T` — the
    `TyP.app` node's own index is `inst b B'` while `dr`'s is `T` (at the
    `es_app` query `T = inst a B`; the reflexive `a ≡ b` case makes `hTe`
    `rfl`). -/
def DrAppHead {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {g b T : Expr Nat} (dr : TyP E n Γ (.app g b) T) : Prop :=
  ∃ (A' B' : Expr Nat) (w : Level)
    (hf : TyP E n Γ g (.pi A' B')) (ha : TyP E n Γ b A')
    (hT : TyP E n Γ (instantiate0 b B') (.sort w)),
    (∃ (hTe : instantiate0 b B' = T),
        dr = hTe ▸ TyP.app E n Γ g b A' B' w hf ha hT) ∨
    ∃ (u : Level) (hc : CvP E n Γ (instantiate0 b B') T (.sort u)),
      dr = TyP.conv E n Γ (.app g b) (instantiate0 b B') T u
        (TyP.app E n Γ g b A' B' w hf ha hT) hc

/-- `appSource` is index-insensitive: a type-index cast on `D` leaves the
    decoded `AppSource` unchanged. -/
theorem appSource_castT {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {e T T' f a : Expr Nat} (h : T = T') (D : TyP E n Γ e T)
    (he : e = .app f a) :
    appSource (h ▸ D) he = appSource D he := by
  cases h
  rfl

/-- `es_app` `occF` under `DrAppHead`: the decoded `hf` is the stored field —
    `[3,0]` for a bare `TyP.app` `dr`, `[3,0,0]` under one `.conv`. -/
theorem drAppHead_occF {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    {dr : TyP E n Γ (.app g b) (instantiate0 a B)} (hd : DrAppHead dr)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ∃ p, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty (appSource dr rfl).hf) := by
  obtain ⟨A', B', w, hf, ha, hT, hn⟩ := hd
  rcases hn with ⟨hTe, hdr⟩ | ⟨u, hc, hdr⟩
  · subst dr
    refine ⟨[3, 0], ?_⟩
    rw [appSource_castT hTe]
    simp only [P2Query.subAt, P2Query.payload, DNode.subAt, DNode.children,
      CvP.dchildren, TyP.dchildren, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some_bind, Option.none_bind,
      dnode_ty_castT, appSource, TyP.appSrc]
  · subst dr; exact ⟨[3, 0, 0], rfl⟩

/-- `es_app` `occA` under `DrAppHead`: `[3,1]` bare, `[3,0,1]` under `.conv`. -/
theorem drAppHead_occA {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    {dr : TyP E n Γ (.app g b) (instantiate0 a B)} (hd : DrAppHead dr)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    ∃ p, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty (appSource dr rfl).ha) := by
  obtain ⟨A', B', w, hf, ha, hT, hn⟩ := hd
  rcases hn with ⟨hTe, hdr⟩ | ⟨u, hc, hdr⟩
  · subst dr
    refine ⟨[3, 1], ?_⟩
    rw [appSource_castT hTe]
    simp only [P2Query.subAt, P2Query.payload, DNode.subAt, DNode.children,
      CvP.dchildren, TyP.dchildren, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some_bind, Option.none_bind,
      dnode_ty_castT, appSource, TyP.appSrc]
  · subst dr; exact ⟨[3, 0, 1], rfl⟩

/-- `es_app` `drClause` under `DrAppHead`: `TyP.eps` peels `.conv`, and on
    the bare `TyP.app` the decoder returns the stored `hf`/`ha`, so both
    branches reduce to `eps_app_appClause`. -/
theorem drAppHead_clause {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {g b T : Expr Nat} {dr : TyP E n Γ (.app g b) T} (hd : DrAppHead dr)
    (σ : Level → Level) (ρ : List Disp) :
    dr.eps σ ρ = appClause ((appSource dr rfl).hf.eps σ ρ)
      ((appSource dr rfl).ha.eps σ ρ) := by
  obtain ⟨A', B', w, hf, ha, hT, hn⟩ := hd
  rcases hn with ⟨hTe, hdr⟩ | ⟨u, hc, hdr⟩
  · subst dr
    rw [TyP.eps_castT, appSource_castT]
    exact eps_app_appClause hf ha hT σ ρ
  · subst dr; exact eps_app_appClause hf ha hT σ ρ

/-! ## §4 composed query-level receipts -/

/-- `h1.dr`'s occurrence in the `.es (CvP.app ..)` query: `.cv h1` is payload
    child `0`. -/
theorem es_app_occH1_closed {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ht : h1.isTransport = false) :
    ∃ p, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty h1.dr) := by
  obtain ⟨p, hp⟩ := cv_dr_subAt h1 ht
  exact ⟨0 :: p, hp⟩

/-- `h2.dr`'s occurrence: `.cv h2` is payload child `1`. -/
theorem es_app_occH2_closed {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ht : h2.isTransport = false) :
    ∃ p, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty h2.dr) := by
  obtain ⟨p, hp⟩ := cv_dr_subAt h2 ht
  exact ⟨1 :: p, hp⟩

/-- `h1.dl`'s occurrence under the `.cv h1` payload subtree. -/
theorem es_app_occDl1 {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ht : h1.isTransport = false) :
    ∃ p, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty h1.dl) := by
  obtain ⟨p, hp⟩ := cv_dl_subAt h1 ht
  exact ⟨0 :: p, hp⟩

/-- `h2.dl`'s occurrence under the `.cv h2` payload subtree. -/
theorem es_app_occDl2 {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ht : h2.isTransport = false) :
    ∃ p, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty h2.dl) := by
  obtain ⟨p, hp⟩ := cv_dl_subAt h2 ht
  exact ⟨1 :: p, hp⟩

/-- `h1.dl.reg.2`'s occurrence: the `cv_dl_subAt` path into `.cv h1` composed
    (`DNode.subAt_append`) with the `RegSubAt` path inside `.ty h1.dl`. -/
theorem es_app_occReg1 {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ht : h1.isTransport = false) (hreg : TyP.RegSubAt h1.dl) :
    ∃ p, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty h1.dl.reg.2) := by
  obtain ⟨pD, hpD⟩ := cv_dl_subAt h1 ht
  obtain ⟨pR, hpR⟩ := hreg
  refine ⟨0 :: (pD ++ pR), ?_⟩
  change (DNode.cv h1).subAt (pD ++ pR) = _
  rw [DNode.subAt_append, hpD]
  exact hpR

/-- `h2.dl.reg.2`'s occurrence, mirrored at payload child `1`. -/
theorem es_app_occReg2 {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ht : h2.isTransport = false) (hreg : TyP.RegSubAt h2.dl) :
    ∃ p, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
      0 p = some (.ty h2.dl.reg.2) := by
  obtain ⟨pD, hpD⟩ := cv_dl_subAt h2 ht
  obtain ⟨pR, hpR⟩ := hreg
  refine ⟨1 :: (pD ++ pR), ?_⟩
  change (DNode.cv h2).subAt (pD ++ pR) = _
  rw [DNode.subAt_append, hpD]
  exact hpR

/-- The `pbFunL` receipt `(h1.dl, h1.dl.reg.2)` from the two shape
    conditions. -/
theorem es_app_occPb_funL {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ht : h1.isTransport = false) (hreg : TyP.RegSubAt h1.dl) :
    ∃ pD pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h1.dl) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h1.dl.reg.2) := by
  obtain ⟨pD, hpD⟩ := es_app_occDl1 h1 h2 dl dr S σ ρ ht
  obtain ⟨pT, hpT⟩ := es_app_occReg1 h1 h2 dl dr S σ ρ ht hreg
  exact ⟨pD, pT, hpD, hpT⟩

/-- The `pbFunR` receipt `(h1.dr, h1.dl.reg.2)`. -/
theorem es_app_occPb_funR {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ht : h1.isTransport = false) (hreg : TyP.RegSubAt h1.dl) :
    ∃ pD pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h1.dr) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h1.dl.reg.2) := by
  obtain ⟨pD, hpD⟩ := es_app_occH1_closed h1 h2 dl dr S σ ρ ht
  obtain ⟨pT, hpT⟩ := es_app_occReg1 h1 h2 dl dr S σ ρ ht hreg
  exact ⟨pD, pT, hpD, hpT⟩

/-- The `pbArgL` receipt `(h2.dl, h2.dl.reg.2)`. -/
theorem es_app_occPb_argL {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ht : h2.isTransport = false) (hreg : TyP.RegSubAt h2.dl) :
    ∃ pD pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h2.dl) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h2.dl.reg.2) := by
  obtain ⟨pD, hpD⟩ := es_app_occDl2 h1 h2 dl dr S σ ρ ht
  obtain ⟨pT, hpT⟩ := es_app_occReg2 h1 h2 dl dr S σ ρ ht hreg
  exact ⟨pD, pT, hpD, hpT⟩

/-- The `pbArgR` receipt `(h2.dr, h2.dl.reg.2)`. -/
theorem es_app_occPb_argR {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ht : h2.isTransport = false) (hreg : TyP.RegSubAt h2.dl) :
    ∃ pD pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h2.dr) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h2.dl.reg.2) := by
  obtain ⟨pD, hpD⟩ := es_app_occH2_closed h1 h2 dl dr S σ ρ ht
  obtain ⟨pT, hpT⟩ := es_app_occReg2 h1 h2 dl dr S σ ρ ht hreg
  exact ⟨pD, pT, hpD, hpT⟩

/-- The `funTag` receipt `(h1.dr, feq ▸ R.hf, h1.dl.reg.2)` plus the decoded
    `pi` equation. The `feq ▸ R.hf` occurrence is the `occF` path bridged by
    `dnode_ty_castS`. -/
theorem es_app_occTag_fun {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ht : h1.isTransport = false) (hreg : TyP.RegSubAt h1.dl)
    (hd : DrAppHead dr)
    (hAA : A = (appSource dr rfl).A) (hBB : B = (appSource dr rfl).B) :
    ∃ pD pF pT,
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h1.dr) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pF = some (.ty ((appSource dr rfl).feq ▸ (appSource dr rfl).hf)) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h1.dl.reg.2) ∧
      A = (appSource dr rfl).A ∧ B = (appSource dr rfl).B := by
  obtain ⟨pD, hpD⟩ := es_app_occH1_closed h1 h2 dl dr S σ ρ ht
  obtain ⟨pF, hpF⟩ := drAppHead_occF h1 h2 dl hd S σ ρ
  obtain ⟨pT, hpT⟩ := es_app_occReg1 h1 h2 dl dr S σ ρ ht hreg
  refine ⟨pD, pF, pT, hpD, ?_, hpT, hAA, hBB⟩
  rw [dnode_ty_castS]
  exact hpF

/-- The `argTag` receipt `(h2.dr, aeq ▸ R.ha, h2.dl.reg.2)` plus the decoded
    domain equation. -/
theorem es_app_occTag_arg {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat}
    {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ht : h2.isTransport = false) (hreg : TyP.RegSubAt h2.dl)
    (hd : DrAppHead dr)
    (hAA : A = (appSource dr rfl).A) :
    ∃ pD pA pT,
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h2.dr) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pA = some (.ty ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha)) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h2.dl.reg.2) ∧
      A = (appSource dr rfl).A := by
  obtain ⟨pD, hpD⟩ := es_app_occH2_closed h1 h2 dl dr S σ ρ ht
  obtain ⟨pA, hpA⟩ := drAppHead_occA h1 h2 dl hd S σ ρ
  obtain ⟨pT, hpT⟩ := es_app_occReg2 h1 h2 dl dr S σ ρ ht hreg
  refine ⟨pD, pA, pT, hpD, ?_, hpT, hAA⟩
  rw [dnode_ty_castS]
  exact hpA

/-- `es_app` `leftCl` closed when `dl` is literally the canonical surface
    node: `appLeftSurface h1 h2 dl` then coincides with `dl`, so `CL` holds
    by `ConvMod` reflexivity. The general case stays the §4.1 worker
    residue. -/
theorem es_app_leftCl_self_closed (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    {w : Level} (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    CL tbl σ ρ (TyP.app E n Γ f a A B w h1.dl h2.dl hT)
      (appLeftSurface h1 h2 (TyP.app E n Γ f a A B w h1.dl h2.dl hT)) :=
  .refl _

/-! ## §5 `EsAppClosedPorts`: the weakened residue -/

/-- The `es_app` residue after this lane's discharges — **strictly weaker
    than `AppPorts`**: every field is the original port `∨` the receipt that
    discharges it through `StepIH`/reflexivity. `AppPorts` gives the `.inl`
    of each field (`esAppClosedPorts_of_appPorts`).

    * `occH1`/`occH2`: `∃`-path receipt `∨ hᵢ.isTransport = false`.
    * `occF`/`occA`/`drClause`: `∃`-path/equation `∨ DrAppHead dr`
      (bare `TyP.app` or one `.conv` over it — no `a = b` required).
    * `pbFun{L,R}`/`pbArg{L,R}`: the `PBit` `∨` the two `subAt` occurrences
      `occ_pb` needs (`hᵢ.d·` and `hᵢ.dl.reg.2`).
    * `funTag`/`argTag`: the `TagCoh` `∨` the three occurrences plus the
      decoded-`pi`/`domain` equation the chained `PB`s need.
    * `leftCl`: the `CL` `∨ dl` being literally the `appLeftSurface` node. -/
structure EsAppClosedPorts (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) : Prop where
  /-- `CL[dl, leftSurface]` or `dl` being literally the surface node. -/
  leftCl : CL tbl σ ρ dl (appLeftSurface h1 h2 dl) ∨
    ∃ (w : Level) (hT : TyP E n Γ (instantiate0 a B) (.sort w)),
      dl = TyP.app E n Γ f a A B w h1.dl h2.dl hT
  /-- `h1.dr`'s occurrence, or `h1` rule-headed (then it is a stored field). -/
  occH1 : (∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty h1.dr)) ∨ h1.isTransport = false
  /-- `h2.dr`'s occurrence, or `h2` rule-headed. -/
  occH2 : (∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty h2.dr)) ∨ h2.isTransport = false
  /-- the decoded `hf` occurrence, or `dr` application-headed. -/
  occF : (∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty (appSource dr rfl).hf)) ∨ DrAppHead dr
  /-- the decoded `ha` occurrence, or `dr` application-headed. -/
  occA : (∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty (appSource dr rfl).ha)) ∨ DrAppHead dr
  /-- `PB[h1.dl, h1.dl.reg.2]` or the two occurrences `occ_pb` needs. -/
  pbFunL : PBit σ ρ h1.dl h1.dl.reg.2 ∨
    ∃ pD pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h1.dl) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h1.dl.reg.2)
  /-- `PB[h1.dr, h1.dl.reg.2]` or the two occurrences. -/
  pbFunR : PBit σ ρ h1.dr h1.dl.reg.2 ∨
    ∃ pD pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h1.dr) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h1.dl.reg.2)
  /-- `PB[h2.dl, h2.dl.reg.2]` or the two occurrences. -/
  pbArgL : PBit σ ρ h2.dl h2.dl.reg.2 ∨
    ∃ pD pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h2.dl) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h2.dl.reg.2)
  /-- `PB[h2.dr, h2.dl.reg.2]` or the two occurrences. -/
  pbArgR : PBit σ ρ h2.dr h2.dl.reg.2 ∨
    ∃ pD pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h2.dr) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h2.dl.reg.2)
  /-- `Tag[h1.dr, feq ▸ R.hf]` or the three occurrences plus the decoded-`pi`
      equation (`R.A = A`, `R.B = B`) the shared `reg.2` gate needs. -/
  funTag : TagCoh σ ρ σ ρ h1.dr ((appSource dr rfl).feq ▸ (appSource dr rfl).hf) ∨
    ∃ pD pF pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h1.dr) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pF = some (.ty ((appSource dr rfl).feq ▸ (appSource dr rfl).hf)) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h1.dl.reg.2) ∧
      A = (appSource dr rfl).A ∧ B = (appSource dr rfl).B
  /-- `Tag[h2.dr, aeq ▸ R.ha]` or the three occurrences plus `R.A = A`. -/
  argTag : TagCoh σ ρ σ ρ h2.dr ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha) ∨
    ∃ pD pA pT, P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pD = some (.ty h2.dr) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pA = some (.ty ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha)) ∧
      P2Query.subAt (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ)
        0 pT = some (.ty h2.dl.reg.2) ∧
      A = (appSource dr rfl).A
  /-- `AppClauseNeed(dr)` or `dr` application-headed. -/
  drClause : dr.eps σ ρ = appClause ((appSource dr rfl).hf.eps σ ρ)
      ((appSource dr rfl).ha.eps σ ρ) ∨ DrAppHead dr

/-- `AppPorts → EsAppClosedPorts` pointwise — the premise is weakened, never
    strengthened: every field of `EsAppClosedPorts` is `.inl`-fillable from
    the corresponding `AppPorts` field. -/
theorem esAppClosedPorts_of_appPorts (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (ports : AppPorts Aw tbl h1 h2 dl dr S σ ρ) :
    EsAppClosedPorts Aw tbl h1 h2 dl dr S σ ρ where
  leftCl := .inl ports.leftCl
  occH1 := .inl ports.occH1
  occH2 := .inl ports.occH2
  occF := .inl ports.occF
  occA := .inl ports.occA
  pbFunL := .inl ports.pbFunL
  pbFunR := .inl ports.pbFunR
  pbArgL := .inl ports.pbArgL
  pbArgR := .inl ports.pbArgR
  funTag := .inl ports.funTag
  argTag := .inl ports.argTag
  drClause := .inl ports.drClause

/-- `es_app` under `EsAppClosedPorts`: every receipt disjunct is discharged
    — `occH1`/`occH2` by `cv_dr_subAt`, `occF`/`occA`/`drClause` by
    `DrAppHead`, the four `PB`s by `Issues.occ_pb` + `StepIH`
    (`es_issued_occ_pb`), the two `TagCoh`s by the same `occ_pb` pair chained
    through their shared `reg.2` sort typing — then `es_app_field`. -/
theorem es_app_field_closed (Aw : Nat → Nat) (tbl : List CRule)
    {Eₐ : ResolvedEnv} {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (c : EsAppClosedPorts Aw tbl h1 h2 dl dr S σ ρ) :
    CaseStep Aw tbl (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) := by
  intro hq ih
  obtain ⟨hap1, hap2, hapdl, hapdr⟩ := hq.ap
  have hleftCl : CL tbl σ ρ dl (appLeftSurface h1 h2 dl) := by
    rcases c.leftCl with h | ⟨w, hT, hdl⟩
    · exact h
    · subst dl; exact es_app_leftCl_self_closed tbl h1 h2 hT σ ρ
  have hoccH1 : ∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty h1.dr) := by
    rcases c.occH1 with h | ht
    · exact h
    · exact es_app_occH1_closed h1 h2 dl dr S σ ρ ht
  have hoccH2 : ∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty h2.dr) := by
    rcases c.occH2 with h | ht
    · exact h
    · exact es_app_occH2_closed h1 h2 dl dr S σ ρ ht
  have hoccF : ∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty (appSource dr rfl).hf) := by
    rcases c.occF with h | hd
    · exact h
    · exact drAppHead_occF h1 h2 dl hd S σ ρ
  have hoccA : ∃ p, P2Query.subAt
      (.es (CvP.app E n Γ f g a b A B h1 h2 dl dr) S σ ρ) 0 p =
        some (.ty (appSource dr rfl).ha) := by
    rcases c.occA with h | hd
    · exact h
    · exact drAppHead_occA h1 h2 dl hd S σ ρ
  have hpbFunL : PBit σ ρ h1.dl h1.dl.reg.2 := by
    rcases c.pbFunL with h | ⟨pD, pT, hD, hT'⟩
    · exact h
    · exact es_issued_occ_pb Aw tbl
        (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
        h1.dl h1.dl.reg.2 pD pT hD hT' (assumpPref_dl hap1)
        (assumpPref_reg (assumpPref_dl hap1)) hq ih
  have hpbFunR : PBit σ ρ h1.dr h1.dl.reg.2 := by
    rcases c.pbFunR with h | ⟨pD, pT, hD, hT'⟩
    · exact h
    · exact es_issued_occ_pb Aw tbl
        (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
        h1.dr h1.dl.reg.2 pD pT hD hT' (assumpPref_dr hap1)
        (assumpPref_reg (assumpPref_dl hap1)) hq ih
  have hpbArgL : PBit σ ρ h2.dl h2.dl.reg.2 := by
    rcases c.pbArgL with h | ⟨pD, pT, hD, hT'⟩
    · exact h
    · exact es_issued_occ_pb Aw tbl
        (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
        h2.dl h2.dl.reg.2 pD pT hD hT' (assumpPref_dl hap2)
        (assumpPref_reg (assumpPref_dl hap2)) hq ih
  have hpbArgR : PBit σ ρ h2.dr h2.dl.reg.2 := by
    rcases c.pbArgR with h | ⟨pD, pT, hD, hT'⟩
    · exact h
    · exact es_issued_occ_pb Aw tbl
        (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
        h2.dr h2.dl.reg.2 pD pT hD hT' (assumpPref_dr hap2)
        (assumpPref_reg (assumpPref_dl hap2)) hq ih
  have hfunTag : TagCoh σ ρ σ ρ h1.dr
      ((appSource dr rfl).feq ▸ (appSource dr rfl).hf) := by
    rcases c.funTag with h | ⟨pD, pF, pT, hD, hF, hT', hAA, hBB⟩
    · exact h
    · have hPi : Expr.pi A B =
          Expr.pi (appSource dr rfl).A (appSource dr rfl).B :=
        congr (congrArg Expr.pi hAA) hBB
      have pbR : PBit σ ρ h1.dr h1.dl.reg.2 :=
        es_issued_occ_pb Aw tbl (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
          h1.dr h1.dl.reg.2 pD pT hD hT' (assumpPref_dr hap1)
          (assumpPref_reg (assumpPref_dl hap1)) hq ih
      have pbF : PBit σ ρ ((appSource dr rfl).feq ▸ (appSource dr rfl).hf)
          (hPi ▸ h1.dl.reg.2 : TyP E n Γ
            (.pi (appSource dr rfl).A (appSource dr rfl).B)
            (.sort h1.dl.reg.1)) :=
        es_issued_occ_pb Aw tbl (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
          ((appSource dr rfl).feq ▸ (appSource dr rfl).hf)
          (hPi ▸ h1.dl.reg.2 : TyP E n Γ
            (.pi (appSource dr rfl).A (appSource dr rfl).B)
            (.sort h1.dl.reg.1))
          pF pT hF
          (hT'.trans (congrArg some (dnode_ty_castS hPi h1.dl.reg.2).symm))
          (Eq.mpr (TyP.ap_castS (appSource dr rfl).feq (appSource dr rfl).hf)
            (appSource_ap dr rfl hapdr).1)
          (Eq.mpr (TyP.ap_castS hPi h1.dl.reg.2)
            (assumpPref_reg (assumpPref_dl hap1))) hq ih
      exact pbR.trans pbF.symm
  have hargTag : TagCoh σ ρ σ ρ h2.dr
      ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha) := by
    rcases c.argTag with h | ⟨pD, pA, pT, hD, hA', hT', hAA⟩
    · exact h
    · have pbR : PBit σ ρ h2.dr h2.dl.reg.2 :=
        es_issued_occ_pb Aw tbl (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
          h2.dr h2.dl.reg.2 pD pT hD hT' (assumpPref_dr hap2)
          (assumpPref_reg (assumpPref_dl hap2)) hq ih
      have pbA : PBit σ ρ ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha)
          (hAA ▸ h2.dl.reg.2 : TyP E n Γ (appSource dr rfl).A
            (.sort h2.dl.reg.1)) :=
        es_issued_occ_pb Aw tbl (CvP.app E n Γ f g a b A B h1 h2 dl dr) rfl S σ ρ
          ((appSource dr rfl).aeq ▸ (appSource dr rfl).ha)
          (hAA ▸ h2.dl.reg.2 : TyP E n Γ (appSource dr rfl).A
            (.sort h2.dl.reg.1))
          pA pT hA'
          (hT'.trans (congrArg some (dnode_ty_castS hAA h2.dl.reg.2).symm))
          (Eq.mpr (TyP.ap_castS (appSource dr rfl).aeq (appSource dr rfl).ha)
            (appSource_ap dr rfl hapdr).2)
          (Eq.mpr (TyP.ap_castS hAA h2.dl.reg.2)
            (assumpPref_reg (assumpPref_dl hap2))) hq ih
      exact pbR.trans pbA.symm
  have hdrClause : dr.eps σ ρ = appClause ((appSource dr rfl).hf.eps σ ρ)
      ((appSource dr rfl).ha.eps σ ρ) := by
    rcases c.drClause with h | hd
    · exact h
    · exact drAppHead_clause hd σ ρ
  exact es_app_field Aw tbl h1 h2 dl dr S σ ρ
    { leftCl := hleftCl
      occH1 := hoccH1
      occH2 := hoccH2
      occF := hoccF
      occA := hoccA
      pbFunL := hpbFunL
      pbFunR := hpbFunR
      pbArgL := hpbArgL
      pbArgR := hpbArgR
      funTag := hfunTag
      argTag := hargTag
      drClause := hdrClause } hq ih

/-! ## §6 non-vacuity witnesses and the closed fixture

`PBit`/`TagCoh` remain inhabited (the `.inl` branches are satisfiable), and
`EsAppClosedPorts` is inhabited at a small kernel-checkable fixture entirely
from `.inr` receipts — so every port's discharge path is exercised, and the
residue records only the genuine sub-domain boundaries. -/

/-- `PBit` is inhabited: a `sort` node is never `★` while its recorded
    sort is a `succ`, whose bit is `false` under any `LevelSub`. -/
theorem es_app_pbit_satisfies (σ : Level → Level) (hσ : LevelSub σ)
    (ρ : List Disp) :
    ∃ (D : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)))
      (DT : TyP emptyEnv 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))),
      PBit σ ρ D DT := by
  refine ⟨TyP.sort emptyEnv 0 [] .zero (.succ .zero) (fun _ => rfl),
    TyP.sort emptyEnv 0 [] (.succ .zero) (.succ (.succ .zero)) (fun _ => rfl),
    ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [eps_sort] at h
    exact ETm.noConfusion h
  · rw [hσ.succ_bit (.succ .zero)] at h
    exact Bool.noConfusion h

/-- `TagCoh` is inhabited: reflexivity on any typing derivation. -/
theorem es_app_tagCoh_satisfies (σ : Level → Level) (ρ : List Disp) :
    ∃ D : TyP emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)),
      TagCoh σ ρ σ ρ D D :=
  ⟨TyP.sort emptyEnv 0 [] .zero (.succ .zero) (fun _ => rfl), Iff.rfl⟩

/-- The fixture context: `bvar 0 : sort 0` under a `pi (sort 0) (sort 0)`
    binder — the argument and function legs of `es_app`'s smallest
    reflexive instance. -/
def esappFixtureΓ : LCtx :=
  [.assumption (.sort .zero), .assumption (.pi (.sort .zero) (.sort .zero))]

/-- `sort 0 : sort 1` in the fixture context. -/
def esappS0 : TyP emptyEnv 0 esappFixtureΓ (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort emptyEnv 0 _ .zero (.succ .zero) (fun _ => rfl)

/-- `pi (sort 0) (sort 0) : sort (imax 1 1)` in the fixture context. -/
def esappPiT : TyP emptyEnv 0 esappFixtureΓ (.pi (.sort .zero) (.sort .zero))
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  TyP.pi emptyEnv 0 _ (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    esappS0
    (TyP.sort emptyEnv 0 _ .zero (.succ .zero) (fun _ => rfl))

/-- The function's endpoint typing: `bvar 1 : pi (sort 0) (sort 0)`. -/
def esappHf : TyP emptyEnv 0 esappFixtureΓ (.bvar 1)
    (.pi (.sort .zero) (.sort .zero)) :=
  TyP.bvar emptyEnv 0 _ 1 _ (.imax (.succ .zero) (.succ .zero)) rfl esappPiT

/-- The argument's endpoint typing: `bvar 0 : sort 0`. -/
def esappHa : TyP emptyEnv 0 esappFixtureΓ (.bvar 0) (.sort .zero) :=
  TyP.bvar emptyEnv 0 _ 0 (.sort .zero) (.succ .zero) rfl esappS0

/-- The function conversion: reflexive on `bvar 1`. -/
def esappH1 : CvP emptyEnv 0 esappFixtureΓ (.bvar 1) (.bvar 1)
    (.pi (.sort .zero) (.sort .zero)) :=
  CvP.refl emptyEnv 0 _ _ _ esappHf esappHf esappHf

/-- The argument conversion: reflexive on `bvar 0`. -/
def esappH2 : CvP emptyEnv 0 esappFixtureΓ (.bvar 0) (.bvar 0) (.sort .zero) :=
  CvP.refl emptyEnv 0 _ _ _ esappHa esappHa esappHa

/-- The application endpoint: `app (bvar 1) (bvar 0) : sort 0`. -/
def esappDl : TyP emptyEnv 0 esappFixtureΓ (.app (.bvar 1) (.bvar 0))
    (instantiate0 (.bvar 0) (.sort .zero)) :=
  TyP.app emptyEnv 0 _ (.bvar 1) (.bvar 0) (.sort .zero) (.sort .zero)
    (.succ .zero) esappHf esappHa esappS0

/-- `esappDl` is `DrAppHead`-shaped (the bare-`TyP.app` branch, `hTe = rfl`
    since the reflexive `a ≡ b` case makes `inst b B'` and `T` identical). -/
def esappDrHead : DrAppHead esappDl :=
  ⟨.sort .zero, .sort .zero, .succ .zero, esappHf, esappHa, esappS0,
    .inl ⟨rfl, rfl⟩⟩

/-- `EsAppClosedPorts` is inhabited at the fixture with **every** field's
    `.inr` receipt: the `occ`/`clause` ports come from
    `isTransport`/`DrAppHead`/`dl`-surface shape, and all four `PB`s plus
    both `TagCoh`s carry their `subAt` receipts — `hᵢ.dl`/`hᵢ.dr`/`reg` at
    `[i,1]`/`[i,2]`/`[i,1,0]`, the decoded `hf`/`ha` at `[3,0]`/`[3,1]`, and
    `A = R.A`, `B = R.B` by `rfl`. No `PBit`/`TagCoh` hypothesis remains. -/
theorem es_app_closedPorts_fixture :
    EsAppClosedPorts (fun _ => 0) [] esappH1 esappH2 esappDl esappDl
      nilScope id [.keep, .keep] where
  leftCl := .inr ⟨.succ .zero, esappS0, rfl⟩
  occH1 := .inr rfl
  occH2 := .inr rfl
  occF := .inr esappDrHead
  occA := .inr esappDrHead
  pbFunL := .inr ⟨[0, 1], [0, 1, 0], rfl, rfl⟩
  pbFunR := .inr ⟨[0, 2], [0, 1, 0], rfl, rfl⟩
  pbArgL := .inr ⟨[1, 1], [1, 1, 0], rfl, rfl⟩
  pbArgR := .inr ⟨[1, 2], [1, 1, 0], rfl, rfl⟩
  funTag := .inr ⟨[0, 2], [3, 0], [0, 1, 0], rfl, rfl, rfl, rfl, rfl⟩
  argTag := .inr ⟨[1, 2], [3, 1], [1, 1, 0], rfl, rfl, rfl, rfl⟩
  drClause := .inr esappDrHead

/-- The assembled `CaseStep` at the fixture: the complete `es_app` answer
    discharged through `StepIH` alone — `es_app_field_closed` issues every
    `PB`/`CL` it needs from the `.inr` occurrence receipts. -/
theorem es_app_field_closed_fixture :
    CaseStep (fun _ => 0) []
      (.es (CvP.app emptyEnv 0 esappFixtureΓ (.bvar 1) (.bvar 1) (.bvar 0)
        (.bvar 0) (.sort .zero) (.sort .zero) esappH1 esappH2 esappDl esappDl)
        nilScope id [.keep, .keep]) :=
  es_app_field_closed (fun _ => 0) [] esappH1 esappH2 esappDl esappDl
    nilScope id [.keep, .keep] es_app_closedPorts_fixture

end Rcic.Syn

#print axioms Rcic.Syn.cv_dl_subAt
#print axioms Rcic.Syn.cv_dr_subAt
#print axioms Rcic.Syn.TyP.RegSubAt
#print axioms Rcic.Syn.ty_reg_subAt_bvar
#print axioms Rcic.Syn.ty_reg_subAt_const
#print axioms Rcic.Syn.ty_reg_subAt_app
#print axioms Rcic.Syn.ty_reg_subAt_letE
#print axioms Rcic.Syn.ty_reg_subAt_conv
#print axioms Rcic.Syn.es_issued_occ_pb
#print axioms Rcic.Syn.DrAppHead
#print axioms Rcic.Syn.appSource_castT
#print axioms Rcic.Syn.drAppHead_occF
#print axioms Rcic.Syn.drAppHead_occA
#print axioms Rcic.Syn.drAppHead_clause
#print axioms Rcic.Syn.es_app_occH1_closed
#print axioms Rcic.Syn.es_app_occH2_closed
#print axioms Rcic.Syn.es_app_occDl1
#print axioms Rcic.Syn.es_app_occDl2
#print axioms Rcic.Syn.es_app_occReg1
#print axioms Rcic.Syn.es_app_occReg2
#print axioms Rcic.Syn.es_app_occPb_funL
#print axioms Rcic.Syn.es_app_occPb_funR
#print axioms Rcic.Syn.es_app_occPb_argL
#print axioms Rcic.Syn.es_app_occPb_argR
#print axioms Rcic.Syn.es_app_occTag_fun
#print axioms Rcic.Syn.es_app_occTag_arg
#print axioms Rcic.Syn.es_app_leftCl_self_closed
#print axioms Rcic.Syn.EsAppClosedPorts
#print axioms Rcic.Syn.esAppClosedPorts_of_appPorts
#print axioms Rcic.Syn.es_app_field_closed
#print axioms Rcic.Syn.es_app_pbit_satisfies
#print axioms Rcic.Syn.es_app_tagCoh_satisfies
#print axioms Rcic.Syn.esappFixtureΓ
#print axioms Rcic.Syn.esappS0
#print axioms Rcic.Syn.esappPiT
#print axioms Rcic.Syn.esappHf
#print axioms Rcic.Syn.esappHa
#print axioms Rcic.Syn.esappH1
#print axioms Rcic.Syn.esappH2
#print axioms Rcic.Syn.esappDl
#print axioms Rcic.Syn.esappDrHead
#print axioms Rcic.Syn.es_app_closedPorts_fixture
#print axioms Rcic.Syn.es_app_field_closed_fixture
