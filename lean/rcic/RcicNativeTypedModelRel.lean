import rcic.RcicNativeTypedModel

/-!
# RcicNativeTypedModelRel — the relation over `CptT` and its typed PER (irrelevance, symmetry,
transitivity by induction on the type code)

Item 1 of the ruling after segment 3.  Two design decisions, each forced by the proof and each
kernel-checked here:

* **Strict semantic typing `CTyS`.**  The landed `CTyT.lam` (and `RcicNativePiModelIrr.CTy`)
  types a λ's outputs at every *compatible* codomain step, universally — so a step with no
  compatible codomain step is unconstrained.  That types a constant universe-valued function at
  a Π code whose codomain is proposition-valued (`ctyT_permissive`), and it leaves the irrelevance
  recursion with no code to recurse on at such a step.  `CTyS` is `CTyT` plus coverage (every
  non-`⊥` output has a compatible codomain step): `ctyT_of_ctyS`, `not_ctyS_permissive`,
  `ctyS_prop_bot`.  Segment 3's `ApproxT` should type its demands by `CTyS` (one field) — see the
  PR body.
* **The λ clause has no collapse disjunct.**  `LRSCore`'s λ clause ends in
  `IsPropTyR Γ (B₁[N]) ∨ Core`; transporting that disjunct across a convertible binder needs type
  uniqueness (`B₁[M] : Sort 0` to `B₂[M] : Sort 0`), which is not available.  In the typed model
  it is unnecessary: an output at a proposition codomain code is `⊥` (`ctyS_prop_bot`), where
  `Core` is trivial.  So `LRSCoreT`'s λ clause is pure `Core`, and the proposition collapse lives
  at the top level only (`LRST`).  The fundamental lemma's λ case will therefore need the model
  typing lemma at proposition codomains (named in the PR).

Other differences from `LRSCore`: the Π clause's steps are **guarded by typing** of their demands
at the domain code (`(∀ u ∈ s.1, CTyS E u a) →`), the type-level spine clause carries
`TyConvT M M'` and its `otherSpine` reading requires normal constant-headed reducts with the
same head, and the data-spine clause relates only the spines (no per-argument relation).  The
two universe codes have the same clause (`lrSCoreT_prop_iff_sort`) — the audit's question:
`sortCode`'s level collapse cannot make a conversion true, because the relation reads sorts
only from the syntactic readback (`sortClauseT` mentions `RedR` and nothing else; for the
`CptI` relation, `lrSCore_sort_iff`).

**The typed PER** (`typedPER`), by strong induction on `sizeOf` (type code for the term-level
statements, with the element compact added; the relation's compact for the type-level ones):
`IrrelAt a u` (`LRSCoreT Γ A₁ A₂ (sort) a → CTyS u a → LRSCoreT N N' A₁ u → LRSCoreT N N' A₂ u`),
`SymmTyAt c`, `TransTyAt c`, `SymmTmAt a u`, `TransTmAt a u`.  Hypotheses: the readback laws,
unique normal forms, `EnvWfT`, and the symmetry/transitivity of `ConvArgsT` along a family's
stored telescope (`ConvArgsSymmT`, `ConvArgsTransT` — witnessed under `PiRowField` by §8's
`convArgs_symm_instMtype`/`convArgs_trans_instMtype`; discharging them without `piRow` is the
named obligation that decouples the family row from the Π row).  Corollaries: `lrSCoreT_symm`,
`lrSCoreT_trans`, `lrSCoreT_irrel` at every compact — the reversed single links beyond
`BotPiCpt` are unblocked.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

/-! ### §0 — the audit lemma for the `CptI` relation: the sort clause reads only the readback -/

theorem lrSCore_sort_iff (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCore R E n Γ M M' A .sort ↔
      (∃ l, RedR R Γ A (.sort l)) ∧ ∃ u u', RedR R Γ M (.sort u) ∧ RedR R Γ M' (.sort u') := by
  rw [LRSCore.eq_def]

/-! ### §2 — the relation over `CptT` -/

/-- The sort clause: reads only the readback. -/
def SortClauseT (R : Readback) (Γ : LCtx) (M M' A : Expr Nat) : Prop :=
  (∃ l, RedR R Γ A (.sort l)) ∧ ∃ u u', RedR R Γ M (.sort u) ∧ RedR R Γ M' (.sort u')

/-- Type-code reading of a spine compact with head `r`: a saturated family spine (`eqNList`,
    `ConvArgsT` along the left stored telescope), or stuck constant-headed normal reducts with the
    same non-family head. -/
def TypeSpineT (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' : Expr Nat) (r : Nat) :
    Prop :=
  (∃ (m : CheckedMember) (ls ls' : List Level) (xs xs' : List (Expr Nat)) (w w' : Level),
      E.members r = some m ∧ m.mclass = .inductiveM ∧
      RedR R Γ M (foldApps (.const r ls) xs) ∧ RedR R Γ M' (foldApps (.const r ls') xs') ∧
      Nonempty (HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) ∧
      Nonempty (HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w')) ∧
      eqNList ls ls' ∧
      xs.length = (piDomsOf m.mtype).length ∧ xs'.length = (piDomsOf m.mtype).length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs') ∨
  ((∀ m, E.members r = some m → m.mclass ≠ .inductiveM) ∧
    ∃ (ls ls' : List Level) (xs xs' : List (Expr Nat)),
      RedR R Γ M (foldApps (.const r ls) xs) ∧ RedR R Γ M' (foldApps (.const r ls') xs') ∧
      NormalR R Γ (foldApps (.const r ls) xs) ∧ NormalR R Γ (foldApps (.const r ls') xs'))

/-- **The relation over `CptT`.** -/
def LRSCoreT (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) :
    CptT → Prop
  | .bot => True
  | .prop => SortClauseT R Γ M M' A
  | .sort => SortClauseT R Γ M M' A
  | .pi a f => (∃ l, RedR R Γ A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ : Expr Nat, RedR R Γ M (.pi A₁ B₁) ∧ RedR R Γ M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        (∃ u₁, LRSCoreT R E n Γ A₁ A₂ (.sort u₁) a) ∧
        ∀ s ∈ f, (∀ u ∈ s.1, CTyS E u a) →
          ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          Nonempty (ConvT E n Γ N N' A₁) → (∀ u ∈ s.1, LRSCoreT R E n Γ N N' A₁ u) →
          ∃ v, LRSCoreT R E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort v) s.2
  | .lam g =>
      ∃ A₁ B₁ : Expr Nat, RedR R Γ A (.pi A₁ B₁) ∧ Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          Nonempty (ConvT E n Γ N N' A₁) → (∀ u ∈ s.1, LRSCoreT R E n Γ N N' A₁ u) →
          LRSCoreT R E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2
  | .spine r args =>
      ((∃ l, RedR R Γ A (.sort l)) ∧ Nonempty (TyConvT E n Γ M M') ∧ TypeSpineT R E n Γ M M' r) ∨
      ((∀ l, ¬ RedR R Γ A (.sort l)) ∧
        ∃ ls₁ ls₂ args₁ args₂,
          RedR R Γ M (foldApps (.const r ls₁) args₁) ∧
          RedR R Γ M' (foldApps (.const r ls₂) args₂) ∧
          NormalR R Γ (foldApps (.const r ls₁) args₁) ∧
          NormalR R Γ (foldApps (.const r ls₂) args₂) ∧
          Nonempty (ConvT E n Γ (foldApps (.const r ls₁) args₁)
            (foldApps (.const r ls₂) args₂) A) ∧
          args.length ≤ args₁.length ∧ args.length ≤ args₂.length)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have h₃ := sizeOfT_fst_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have h₃ := sizeOfT_snd_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
       have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have h₃ := sizeOfT_fst_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
       have h₃ := sizeOfT_snd_lt s
       omega)

/-- The relation with the top-level proposition collapse. -/
def LRST (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) (c : CptT) : Prop :=
  IsPropTyR R E n Γ A ∨ LRSCoreT R E n Γ M M' A c

theorem lrSCoreT_bot (Γ : LCtx) (M M' A : Expr Nat) : LRSCoreT R E n Γ M M' A .bot := by
  rw [LRSCoreT.eq_def]; trivial

theorem lrSCoreT_prop_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreT R E n Γ M M' A .prop ↔ SortClauseT R Γ M M' A := by
  rw [LRSCoreT.eq_def]

theorem lrSCoreT_sort_iff (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreT R E n Γ M M' A .sort ↔ SortClauseT R Γ M M' A := by
  rw [LRSCoreT.eq_def]

/-- **The audit lemma**: the two universe codes have the same clause, and it mentions the
    readback only.  `sortCode`'s level collapse can change which compact a universe *has*, never
    what the relation *asserts* at it. -/
theorem lrSCoreT_prop_iff_sort (Γ : LCtx) (M M' A : Expr Nat) :
    LRSCoreT R E n Γ M M' A .prop ↔ LRSCoreT R E n Γ M M' A .sort :=
  (lrSCoreT_prop_iff Γ M M' A).trans (lrSCoreT_sort_iff Γ M M' A).symm

/-! #### readback facts -/

theorem foldApps_const_ne_sort {r : Nat} {ls : List Level} (xs : List (Expr Nat)) (l : Level) :
    foldApps (.const r ls) xs ≠ .sort l := fun h => by
  have hs := congrArg appsSpine h
  rw [appsSpine_foldApps_const] at hs
  exact Expr.noConfusion (congrArg Prod.fst hs)

theorem foldApps_const_ne_pi {r : Nat} {ls : List Level} (xs : List (Expr Nat)) (A B : Expr Nat) :
    foldApps (.const r ls) xs ≠ .pi A B := fun h => by
  have hs := congrArg appsSpine h
  rw [appsSpine_foldApps_const] at hs
  exact Expr.noConfusion (congrArg Prod.fst hs)

/-- A term with a normal non-sort readback does not read back to a sort. -/
theorem not_redR_sort_of_normal (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {Γ : LCtx}
    {A X : Expr Nat} (hX : RedR R Γ A X) (hXn : NormalR R Γ X) (hXs : ∀ l, X ≠ .sort l) :
    ∀ l, ¬ RedR R Γ A (.sort l) :=
  fun l h => hXs l (hNU Γ hX hXn h (fun _ hs => hL.sort_normal _ _ _ hs))

/-- A term that reads back to a sort does not read back to a Π. -/
theorem not_redR_pi_of_redR_sort (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {Γ : LCtx}
    {A : Expr Nat} {l : Level} (hs : RedR R Γ A (.sort l)) (A₁ B₁ : Expr Nat) :
    ¬ RedR R Γ A (.pi A₁ B₁) :=
  fun h => Expr.noConfusion (hNU Γ hs (fun _ hs => hL.sort_normal _ _ _ hs) h
    (fun _ hs => hL.pi_normal _ _ _ _ hs))

/-- The two Π readbacks of one term coincide. -/
theorem redR_pi_unique (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {Γ : LCtx}
    {A A₁ B₁ A₂ B₂ : Expr Nat} (h₁ : RedR R Γ A (.pi A₁ B₁)) (h₂ : RedR R Γ A (.pi A₂ B₂)) :
    A₁ = A₂ ∧ B₁ = B₂ := by
  have e := hNU Γ h₁ (fun _ hs => hL.pi_normal _ _ _ _ hs) h₂ (fun _ hs => hL.pi_normal _ _ _ _ hs)
  injection e with eA eB
  exact ⟨eA, eB⟩

/-- The type-level reducts of `TypeSpineT` are normal and are not sorts. -/
theorem typeSpineT_not_sort (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    {Γ : LCtx} {M M' : Expr Nat} {r : Nat} (h : TypeSpineT R E n Γ M M' r) :
    (∀ l, ¬ RedR R Γ M (.sort l)) ∧ (∀ l, ¬ RedR R Γ M' (.sort l)) := by
  rcases h with ⟨m, ls, ls', xs, xs', _, _, hm, hind, h1, h2, _⟩ | ⟨_, ls, ls', xs, xs', h1, h2, hn1, hn2⟩
  · exact ⟨not_redR_sort_of_normal hL hNU h1 (fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs)
        (foldApps_const_ne_sort xs),
      not_redR_sort_of_normal hL hNU h2 (fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs)
        (foldApps_const_ne_sort xs')⟩
  · exact ⟨not_redR_sort_of_normal hL hNU h1 hn1 (foldApps_const_ne_sort xs),
      not_redR_sort_of_normal hL hNU h2 hn2 (foldApps_const_ne_sort xs')⟩

/-- Among indices that read back to sorts, the index is irrelevant (every clause reads of the
    index only whether it reads back to a sort). -/
theorem lrSCoreT_sortIdx_irrel (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {Γ : LCtx}
    {N N' A A' : Expr Nat} (hA : ∃ l, RedR R Γ A (.sort l)) (hA' : ∃ l, RedR R Γ A' (.sort l)) :
    (c : CptT) → LRSCoreT R E n Γ N N' A c → LRSCoreT R E n Γ N N' A' c
  | .bot, _ => lrSCoreT_bot _ _ _ _
  | .prop, h => by
      rw [lrSCoreT_prop_iff] at h
      rw [lrSCoreT_prop_iff]
      exact ⟨hA', h.2⟩
  | .sort, h => by
      rw [lrSCoreT_sort_iff] at h
      rw [lrSCoreT_sort_iff]
      exact ⟨hA', h.2⟩
  | .pi a f, h => by
      rw [LRSCoreT.eq_def] at h
      rw [LRSCoreT.eq_def]
      exact ⟨hA', h.2⟩
  | .lam g, h => by
      rw [LRSCoreT.eq_def] at h
      obtain ⟨A₁, B₁, hr, _⟩ := h
      obtain ⟨l, hl⟩ := hA
      exact (not_redR_pi_of_redR_sort hL hNU hl A₁ B₁ hr).elim
  | .spine r args, h => by
      rw [LRSCoreT.eq_def] at h
      rw [LRSCoreT.eq_def]
      rcases h with ⟨_, hc, hT⟩ | ⟨hns, _⟩
      · exact Or.inl ⟨hA', hc, hT⟩
      · obtain ⟨l, hl⟩ := hA
        exact (hns l hl).elim

/-! ### §3 — the typed PER package -/

/-- Symmetry of `ConvArgsT` along a family's stored telescope (with the level change). -/
def ConvArgsSymmT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}, E.members r = some m →
    m.mclass = .inductiveM → ∀ {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w w' : Level},
    HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w) →
    HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w') →
    eqNList ls ls' → xs.length = (piDomsOf m.mtype).length → xs'.length = (piDomsOf m.mtype).length →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' →
    ConvArgsT E n Γ (instantiateLevels ls' m.mtype) xs' xs

/-- Transitivity of `ConvArgsT` along a family's stored telescope. -/
def ConvArgsTransT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}, E.members r = some m →
    m.mclass = .inductiveM →
    ∀ {ls ls' ls'' : List Level} {xs xs' xs'' : List (Expr Nat)} {w w' w'' : Level},
    HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w) →
    HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w') →
    HasTyT E n Γ (foldApps (.const r ls'') xs'') (.sort w'') →
    eqNList ls ls' → eqNList ls' ls'' →
    xs.length = (piDomsOf m.mtype).length → xs'.length = (piDomsOf m.mtype).length →
    xs''.length = (piDomsOf m.mtype).length →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' →
    ConvArgsT E n Γ (instantiateLevels ls' m.mtype) xs' xs'' →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs''

theorem eqN_symm' {l l' : Level} (h : eqN l l') : eqN l' l := fun ρ => (h ρ).symm
theorem eqN_trans' {l l' l'' : Level} (h : eqN l l') (h' : eqN l' l'') : eqN l l'' :=
  fun ρ => (h ρ).trans (h' ρ)

theorem eqNList_symm'' : ∀ {ls ls' : List Level}, eqNList ls ls' → eqNList ls' ls
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨eqN_symm' h, eqNList_symm'' hs⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem eqNList_trans'' : ∀ {ls ls' ls'' : List Level}, eqNList ls ls' → eqNList ls' ls'' →
    eqNList ls ls''
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h, hs⟩, ⟨h', hs'⟩ => ⟨eqN_trans' h h', eqNList_trans'' hs hs'⟩
  | [], [], _ :: _, _, h' => h'.elim
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h' => h'.elim

/-- The package's statements. -/
def IrrelAt (R : Readback) (E : ResolvedEnv) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ A₂ : Expr Nat} {w : Level},
    LRSCoreT R E n Γ A₁ A₂ (.sort w) a → CTyS E u a →
    ∀ {N N' : Expr Nat}, LRSCoreT R E n Γ N N' A₁ u → LRSCoreT R E n Γ N N' A₂ u

def SymmTmAt (R : Readback) (E : ResolvedEnv) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {w : Level},
    LRSCoreT R E n Γ A A (.sort w) a → CTyS E u a →
    ∀ {N N' : Expr Nat}, LRSCoreT R E n Γ N N' A u → LRSCoreT R E n Γ N' N A u

def TransTmAt (R : Readback) (E : ResolvedEnv) (n : Nat) (a u : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A : Expr Nat} {w : Level},
    LRSCoreT R E n Γ A A (.sort w) a → CTyS E u a →
    ∀ {N N' N'' : Expr Nat}, LRSCoreT R E n Γ N N' A u → LRSCoreT R E n Γ N' N'' A u →
      LRSCoreT R E n Γ N N'' A u

def SymmTyAt (R : Readback) (E : ResolvedEnv) (n : Nat) (c : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ A₂ : Expr Nat} {w : Level},
    LRSCoreT R E n Γ A₁ A₂ (.sort w) c → LRSCoreT R E n Γ A₂ A₁ (.sort w) c

def TransTyAt (R : Readback) (E : ResolvedEnv) (n : Nat) (c : CptT) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A₁ A₂ A₃ : Expr Nat} {w : Level},
    LRSCoreT R E n Γ A₁ A₂ (.sort w) c → LRSCoreT R E n Γ A₂ A₃ (.sort w) c →
      LRSCoreT R E n Γ A₁ A₃ (.sort w) c

/-! #### size facts for the induction -/

theorem sizeOf_dom_lt_pi (a : CptT) (g : List (List CptT × CptT)) : sizeOf a < sizeOf (CptT.pi a g) := by
  simp; omega

theorem sizeOf_out_lt_pi {a : CptT} {g : List (List CptT × CptT)} {t : List CptT × CptT} (ht : t ∈ g) :
    sizeOf t.2 < sizeOf (CptT.pi a g) := by
  have h₁ := List.sizeOf_lt_of_mem ht
  have h₂ := sizeOfT_snd_lt t
  simp; omega

theorem sizeOf_dem_lt_lam {f : List (List CptT × CptT)} {s : List CptT × CptT} (hs : s ∈ f) {v : CptT}
    (hv : v ∈ s.1) : sizeOf v < sizeOf (CptT.lam f) := by
  have h₁ := List.sizeOf_lt_of_mem hs
  have h₂ := List.sizeOf_lt_of_mem hv
  have h₃ := sizeOfT_fst_lt s
  simp; omega

theorem sizeOf_out_lt_lam {f : List (List CptT × CptT)} {s : List CptT × CptT} (hs : s ∈ f) :
    sizeOf s.2 < sizeOf (CptT.lam f) := by
  have h₁ := List.sizeOf_lt_of_mem hs
  have h₂ := sizeOfT_snd_lt s
  simp; omega

theorem sizeOf_dem_lt_pi {a : CptT} {f : List (List CptT × CptT)} {s : List CptT × CptT} (hs : s ∈ f)
    {v : CptT} (hv : v ∈ s.1) : sizeOf v < sizeOf (CptT.pi a f) := by
  have h₁ := List.sizeOf_lt_of_mem hs
  have h₂ := List.sizeOf_lt_of_mem hv
  have h₃ := sizeOfT_fst_lt s
  simp; omega

/-! #### the step lemmas -/

/-- Symmetry of the type-level spine reading. -/
theorem typeSpineT_symm (hCAs : ConvArgsSymmT E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M M' : Expr Nat}
    {r : Nat} (h : TypeSpineT R E n Γ M M' r) : TypeSpineT R E n Γ M' M r := by
  rcases h with ⟨m, ls, ls', xs, xs', w, w', hm, hind, h1, h2, ⟨hty⟩, ⟨hty'⟩, heqN, hlen, hlen', hargs⟩
    | ⟨hnot, ls, ls', xs, xs', h1, h2, hn1, hn2⟩
  · exact Or.inl ⟨m, ls', ls, xs', xs, w', w, hm, hind, h2, h1, ⟨hty'⟩, ⟨hty⟩, eqNList_symm'' heqN,
      hlen', hlen, hCAs hΓ hm hind hty hty' heqN hlen hlen' hargs⟩
  · exact Or.inr ⟨hnot, ls', ls, xs', xs, h2, h1, hn2, hn1⟩

/-- Transitivity of the type-level spine reading: the middle term's two normal reducts coincide. -/
theorem typeSpineT_trans (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (hCAt : ConvArgsTransT E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {M M' M'' : Expr Nat} {r : Nat} (h₁ : TypeSpineT R E n Γ M M' r) (h₂ : TypeSpineT R E n Γ M' M'' r) :
    TypeSpineT R E n Γ M M'' r := by
  rcases h₁ with ⟨m, ls, ls', xs, xs', w, w', hm, hind, h1, h2, hty, hty', heqN, hlen, hlen', hargs⟩
    | ⟨hnot, ls, ls', xs, xs', h1, h2, hn1, hn2⟩
  · rcases h₂ with ⟨m', ls₂, ls'', xs₂, xs'', _, w'', hm', _, h2', h3, _, hty'', heqN', hlen₂, hlen'', hargs'⟩
      | ⟨hnot, _⟩
    · rw [hm] at hm'
      injection hm' with hm'
      subst hm'
      have e := hNU Γ h2 (fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs) h2'
        (fun _ hs => hL.famApp_normal hW _ hm hind _ _ _ hs)
      obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
      injection hconst with _ hls
      subst hls; subst hxs
      obtain ⟨hty⟩ := hty; obtain ⟨hty'⟩ := hty'; obtain ⟨hty''⟩ := hty''
      exact Or.inl ⟨m, ls, ls'', xs, xs'', w, w'', hm, hind, h1, h3, ⟨hty⟩, ⟨hty''⟩,
        eqNList_trans'' heqN heqN', hlen, hlen'',
        hCAt hΓ hm hind hty hty' hty'' heqN heqN' hlen hlen' hlen'' hargs hargs'⟩
    · exact (hnot m hm hind).elim
  · rcases h₂ with ⟨m, _, _, _, _, _, _, hm, hind, _⟩ | ⟨_, ls₂, ls'', xs₂, xs'', h2', h3, hn2', hn3⟩
    · exact (hnot m hm hind).elim
    · have e := hNU Γ h2 hn2 h2' hn2'
      obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
      injection hconst with _ hls
      subst hls; subst hxs
      exact Or.inr ⟨hnot, ls, ls'', xs, xs'', h1, h3, hn1, hn3⟩

/-- `SymmTyAt c` from the package below `c`. -/
theorem symmTy_step (hL : ReadbackLaws E R) (hW : EnvWfT E) (hCAs : ConvArgsSymmT E n) (c : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf c → SymmTyAt R E n c' ∧ TransTyAt R E n c')
    (ihP : ∀ a u, sizeOf a + sizeOf u < sizeOf c →
      IrrelAt R E n a u ∧ SymmTmAt R E n a u ∧ TransTmAt R E n a u) :
    SymmTyAt R E n c := by
  intro Γ hΓ A₁ A₂ w h
  cases c with
  | bot => exact lrSCoreT_bot _ _ _ _
  | prop =>
      rw [lrSCoreT_prop_iff] at h
      rw [lrSCoreT_prop_iff]
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u', u, h2, h1⟩
  | sort =>
      rw [lrSCoreT_sort_iff] at h
      rw [lrSCoreT_sort_iff]
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u', u, h2, h1⟩
  | lam g =>
      rw [LRSCoreT.eq_def] at h
      obtain ⟨A₁', B₁', hr, _⟩ := h
      exact Expr.noConfusion (redR_sort_eq hL hr)
  | spine r args =>
      rw [LRSCoreT.eq_def] at h
      rw [LRSCoreT.eq_def]
      rcases h with ⟨hA, ⟨hc⟩, hT⟩ | ⟨hns, _⟩
      · exact Or.inl ⟨hA, ⟨hc.symmT⟩, typeSpineT_symm hCAs hΓ hT⟩
      · exact (hns w (.refl _)).elim
  | pi a f =>
      rw [LRSCoreT.eq_def] at h
      rw [LRSCoreT.eq_def]
      obtain ⟨hA, A₁', B₁', A₂', B₂', h1, h2, ⟨hΓ₁⟩, ⟨hdom⟩, ⟨hcod⟩, ⟨u₁, hra⟩, hrf⟩ := h
      obtain ⟨hsa, hta⟩ := ihQ a (sizeOf_dom_lt_pi a f)
      have hra' : LRSCoreT R E n Γ A₂' A₁' (.sort u₁) a := hsa hΓ hra
      have hself₂ : LRSCoreT R E n Γ A₂' A₂' (.sort u₁) a := hta hΓ hra' hra
      cases hΓ₁ with
      | assumption _ _ u _ hA₁ =>
          obtain ⟨v, hA₂⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ hdom hA₁
          refine ⟨hA, A₂', B₂', A₁', B₁', h2, h1, ⟨.assumption Γ A₂' v hΓ hA₂⟩, ⟨hdom.symmT⟩,
            ⟨tyConvT_assump_dom hW hΓ hdom.symmT hcod.symmT⟩, ⟨u₁, hra'⟩, ?_⟩
          intro s hs hty N N' hN hN' hcN hrel
          obtain ⟨hcN⟩ := hcN
          have hN₁ : HasTyT E n Γ N A₁' := hasTyT_of_tyConvT hN hdom.symmT
          have hN'₁ : HasTyT E n Γ N' A₁' := hasTyT_of_tyConvT hN' hdom.symmT
          have hc₁ : ConvT E n Γ N' N A₁' := convT_of_tyConv (.symm _ _ _ _ hcN) hdom.symmT
          have hrel₁ : ∀ u ∈ s.1, LRSCoreT R E n Γ N' N A₁' u := fun u hu =>
            (ihP a u (by
              have h₁ := List.sizeOf_lt_of_mem hs
              have h₂ := List.sizeOf_lt_of_mem hu
              have h₃ := sizeOfT_fst_lt s
              simp; omega)).1 hΓ hra' (hty u hu)
              ((ihP a u (by
              have h₁ := List.sizeOf_lt_of_mem hs
              have h₂ := List.sizeOf_lt_of_mem hu
              have h₃ := sizeOfT_fst_lt s
              simp; omega)).2.1 hΓ hself₂ (hty u hu) (hrel u hu))
          obtain ⟨v', hv'⟩ := hrf s hs hty N' N hN'₁ hN₁ ⟨hc₁⟩ hrel₁
          exact ⟨v', (ihQ s.2 (sizeOf_out_lt_pi hs)).1 hΓ hv'⟩

/-- `TransTyAt c` from the package below `c`. -/
theorem transTy_step (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (hCAt : ConvArgsTransT E n) (c : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf c → SymmTyAt R E n c' ∧ TransTyAt R E n c')
    (ihP : ∀ a u, sizeOf a + sizeOf u < sizeOf c →
      IrrelAt R E n a u ∧ SymmTmAt R E n a u ∧ TransTmAt R E n a u) :
    TransTyAt R E n c := by
  intro Γ hΓ A₁ A₂ A₃ w h₁ h₂
  cases c with
  | bot => exact lrSCoreT_bot _ _ _ _
  | prop =>
      rw [lrSCoreT_prop_iff] at h₁ h₂
      rw [lrSCoreT_prop_iff]
      obtain ⟨hA, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hA, u, u'', h1, h3⟩
  | sort =>
      rw [lrSCoreT_sort_iff] at h₁ h₂
      rw [lrSCoreT_sort_iff]
      obtain ⟨hA, u, _, h1, _⟩ := h₁
      obtain ⟨_, _, u'', _, h3⟩ := h₂
      exact ⟨hA, u, u'', h1, h3⟩
  | lam g =>
      rw [LRSCoreT.eq_def] at h₁
      obtain ⟨A₁', B₁', hr, _⟩ := h₁
      exact Expr.noConfusion (redR_sort_eq hL hr)
  | spine r args =>
      rw [LRSCoreT.eq_def] at h₁ h₂
      rw [LRSCoreT.eq_def]
      rcases h₁ with ⟨hA, ⟨hc₁⟩, hT₁⟩ | ⟨hns, _⟩
      · rcases h₂ with ⟨_, ⟨hc₂⟩, hT₂⟩ | ⟨hns, _⟩
        · exact Or.inl ⟨hA, ⟨TyConvT.trans _ _ _ _ hc₁ hc₂⟩, typeSpineT_trans hL hNU hW hCAt hΓ hT₁ hT₂⟩
        · exact (hns w (.refl _)).elim
      · exact (hns w (.refl _)).elim
  | pi a f =>
      rw [LRSCoreT.eq_def] at h₁ h₂
      rw [LRSCoreT.eq_def]
      obtain ⟨hA, A₁', B₁', A₂', B₂', h1, h2, ⟨hΓ₁⟩, ⟨hdom₁⟩, ⟨hcod₁⟩, ⟨u₁, hra₁⟩, hrf₁⟩ := h₁
      obtain ⟨_, A₂'', B₂'', A₃', B₃', h2', h3, _, ⟨hdom₂⟩, ⟨hcod₂⟩, ⟨u₂, hra₂⟩, hrf₂⟩ := h₂
      obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU h2 h2'
      subst eA; subst eB
      obtain ⟨hsa, hta⟩ := ihQ a (sizeOf_dom_lt_pi a f)
      have hra₂' : LRSCoreT R E n Γ A₂' A₃' (.sort u₁) a :=
        lrSCoreT_sortIdx_irrel hL hNU ⟨_, .refl _⟩ ⟨_, .refl _⟩ a hra₂
      have hself₁ : LRSCoreT R E n Γ A₁' A₁' (.sort u₁) a := hta hΓ hra₁ (hsa hΓ hra₁)
      refine ⟨hA, A₁', B₁', A₃', B₃', h1, h3, ⟨hΓ₁⟩, ⟨TyConvT.trans _ _ _ _ hdom₁ hdom₂⟩,
        ⟨TyConvT.trans _ _ _ _ hcod₁ (tyConvT_assump_dom hW hΓ hdom₁ hcod₂)⟩, ⟨u₁, hta hΓ hra₁ hra₂'⟩, ?_⟩
      intro s hs hty N N' hN hN' hcN hrel
      obtain ⟨hcN⟩ := hcN
      have hrelNN : ∀ u ∈ s.1, LRSCoreT R E n Γ N N A₁' u := fun u hu =>
        (ihP a u (by
              have h₁ := List.sizeOf_lt_of_mem hs
              have h₂ := List.sizeOf_lt_of_mem hu
              have h₃ := sizeOfT_fst_lt s
              simp; omega)).2.2 hΓ hself₁ (hty u hu) (hrel u hu)
          ((ihP a u (by
              have h₁ := List.sizeOf_lt_of_mem hs
              have h₂ := List.sizeOf_lt_of_mem hu
              have h₃ := sizeOfT_fst_lt s
              simp; omega)).2.1 hΓ hself₁ (hty u hu) (hrel u hu))
      obtain ⟨v, hv⟩ := hrf₁ s hs hty N N hN hN ⟨.refl _ _ _ hN⟩ hrelNN
      have hN₂ : HasTyT E n Γ N A₂' := hasTyT_of_tyConvT hN hdom₁
      have hN'₂ : HasTyT E n Γ N' A₂' := hasTyT_of_tyConvT hN' hdom₁
      have hrel₂ : ∀ u ∈ s.1, LRSCoreT R E n Γ N N' A₂' u := fun u hu =>
        (ihP a u (by
              have h₁ := List.sizeOf_lt_of_mem hs
              have h₂ := List.sizeOf_lt_of_mem hu
              have h₃ := sizeOfT_fst_lt s
              simp; omega)).1 hΓ hra₁ (hty u hu) (hrel u hu)
      obtain ⟨v', hv'⟩ := hrf₂ s hs hty N N' hN₂ hN'₂ ⟨convT_of_tyConv hcN hdom₁⟩ hrel₂
      exact ⟨v, (ihQ s.2 (sizeOf_out_lt_pi hs)).2 hΓ hv
        (lrSCoreT_sortIdx_irrel hL hNU ⟨_, .refl _⟩ ⟨_, .refl _⟩ s.2 hv')⟩

/-- The data-spine reading at a spine-coded index: the index does not read back to a sort. -/
theorem lrSCoreT_spine_data_of_tyIdx (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) {Γ : LCtx} {A : Expr Nat} {w : Level} {r' : Nat} {args' : List CptT}
    {A₂ : Expr Nat} (h : LRSCoreT R E n Γ A A₂ (.sort w) (.spine r' args')) :
    (∀ l, ¬ RedR R Γ A (.sort l)) ∧ (∀ l, ¬ RedR R Γ A₂ (.sort l)) ∧ Nonempty (TyConvT E n Γ A A₂) := by
  rw [LRSCoreT.eq_def] at h
  rcases h with ⟨_, hc, hT⟩ | ⟨hns, _⟩
  · obtain ⟨h1, h2⟩ := typeSpineT_not_sort hL hNU hW hT
    exact ⟨h1, h2, hc⟩
  · exact (hns w (.refl _)).elim

/-- `IrrelAt a u` from the package below. -/
theorem irrel_step (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (a u : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAt R E n c' ∧ TransTyAt R E n c')
    (ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
      IrrelAt R E n a' u' ∧ SymmTmAt R E n a' u' ∧ TransTmAt R E n a' u') :
    IrrelAt R E n a u := by
  intro Γ hΓ A₁ A₂ w hAA hu N N' h
  cases a with
  | bot => rw [ctyS_bot_inv hu]; exact lrSCoreT_bot _ _ _ _
  | prop =>
      rw [lrSCoreT_prop_iff] at hAA
      obtain ⟨_, l₁, l₂, h1, h2⟩ := hAA
      exact lrSCoreT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨_, h2⟩ u h
  | sort =>
      rw [lrSCoreT_sort_iff] at hAA
      obtain ⟨_, l₁, l₂, h1, h2⟩ := hAA
      exact lrSCoreT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨_, h2⟩ u h
  | lam g => rw [ctyS_lam_inv hu]; exact lrSCoreT_bot _ _ _ _
  | spine r' args' =>
      rcases ctyS_spine_inv hu with rfl | ⟨⟨r, args, rfl⟩, _⟩
      · exact lrSCoreT_bot _ _ _ _
      · obtain ⟨hns₁, hns₂, ⟨hc₁₂⟩⟩ := lrSCoreT_spine_data_of_tyIdx hL hNU hW hAA
        rw [LRSCoreT.eq_def] at h
        rw [LRSCoreT.eq_def]
        rcases h with ⟨⟨l, hl⟩, _⟩ | ⟨_, ls₁, ls₂, args₁, args₂, hM, hM', hn₁, hn₂, ⟨hconv⟩, hl₁, hl₂⟩
        · exact (hns₁ l hl).elim
        · exact Or.inr ⟨hns₂, ls₁, ls₂, args₁, args₂, hM, hM', hn₁, hn₂,
            ⟨convT_of_tyConv hconv hc₁₂⟩, hl₁, hl₂⟩
  | pi a' g =>
      rcases ctyS_pi_inv hu with rfl | ⟨f, rfl, _, hdom, hcod, hcov⟩
      · exact lrSCoreT_bot _ _ _ _
      · rw [LRSCoreT.eq_def] at h
        obtain ⟨A₁₁, B₁₁, hr₁, ⟨hΓ₁₁⟩, hclause⟩ := h
        rw [LRSCoreT.eq_def] at hAA
        obtain ⟨_, A₁₁', B₁₁', A₂₁, B₂₁, hr₁', hr₂, _, ⟨hdomT⟩, ⟨hcodT⟩, ⟨u₁, hra⟩, hrf⟩ := hAA
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr₁ hr₁'
        subst eA; subst eB
        have hlt_a' : sizeOf a' < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
          have := sizeOf_dom_lt_pi a' g; omega
        obtain ⟨hsa, hta⟩ := ihQ a' hlt_a'
        have hra' : LRSCoreT R E n Γ A₂₁ A₁₁ (.sort u₁) a' := hsa hΓ hra
        have hself₁ : LRSCoreT R E n Γ A₁₁ A₁₁ (.sort u₁) a' := hta hΓ hra hra'
        rw [LRSCoreT.eq_def]
        cases hΓ₁₁ with
        | assumption _ _ u₀ _ hA₁₁ =>
            obtain ⟨v₀, hA₂₁⟩ := PiModelIdealAudit.tyConvT_endTyped hW hΓ hdomT hA₁₁
            refine ⟨A₂₁, B₂₁, hr₂, ⟨.assumption Γ A₂₁ v₀ hΓ hA₂₁⟩, ?_⟩
            intro s hs M M' hM hM' hcM hrel
            obtain ⟨hcM⟩ := hcM
            have hM₁ : HasTyT E n Γ M A₁₁ := hasTyT_of_tyConvT hM hdomT.symmT
            have hM'₁ : HasTyT E n Γ M' A₁₁ := hasTyT_of_tyConvT hM' hdomT.symmT
            have hc₁ : ConvT E n Γ M M' A₁₁ := convT_of_tyConv hcM hdomT.symmT
            have hltP : ∀ v ∈ s.1, sizeOf a' + sizeOf v < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) :=
              fun v hv => by
                have := sizeOf_dom_lt_pi a' g
                have := sizeOf_dem_lt_lam hs hv
                omega
            have hrel₁ : ∀ v ∈ s.1, LRSCoreT R E n Γ M M' A₁₁ v := fun v hv =>
              (ihP a' v (hltP v hv)).1 hΓ hra' (hdom s hs v hv) (hrel v hv)
            have hcore := hclause s hs M M' hM₁ hM'₁ ⟨hc₁⟩ hrel₁
            rcases hcov s hs with h0 | ⟨t, ht, hcomp⟩
            · rw [h0]; exact lrSCoreT_bot _ _ _ _
            · have htyt : ∀ v ∈ t.1, CTyS E v a' := fun v hv => hdom s hs v (hcomp v hv)
              have hrelMM : ∀ v ∈ t.1, LRSCoreT R E n Γ M M A₁₁ v := fun v hv =>
                (ihP a' v (hltP v (hcomp v hv))).2.2 hΓ hself₁ (htyt v hv) (hrel₁ v (hcomp v hv))
                  ((ihP a' v (hltP v (hcomp v hv))).2.1 hΓ hself₁ (htyt v hv) (hrel₁ v (hcomp v hv)))
              obtain ⟨v₁, hv₁⟩ := hrf t ht htyt M M hM₁ hM₁ ⟨.refl _ _ _ hM₁⟩ hrelMM
              have hlt_t : sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
                have := sizeOf_out_lt_pi (a := a') ht
                have := sizeOf_out_lt_lam hs
                omega
              exact (ihP t.2 s.2 hlt_t).1 hΓ hv₁ (hcod s hs t ht hcomp) hcore

/-- `SymmTmAt a u` from the package below. -/
theorem symmTm_step (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (a u : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAt R E n c' ∧ TransTyAt R E n c')
    (ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
      IrrelAt R E n a' u' ∧ SymmTmAt R E n a' u' ∧ TransTmAt R E n a' u') :
    SymmTmAt R E n a u := by
  intro Γ hΓ A w hAA hu N N' h
  cases a with
  | bot => rw [ctyS_bot_inv hu]; exact lrSCoreT_bot _ _ _ _
  | prop =>
      rw [lrSCoreT_prop_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.prop + sizeOf u := by have := CptT.sizeOf_pos CptT.prop; omega
      have h' := lrSCoreT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h
      exact lrSCoreT_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).1 hΓ h')
  | sort =>
      rw [lrSCoreT_sort_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.sort + sizeOf u := by have := CptT.sizeOf_pos CptT.sort; omega
      have h' := lrSCoreT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h
      exact lrSCoreT_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).1 hΓ h')
  | lam g => rw [ctyS_lam_inv hu]; exact lrSCoreT_bot _ _ _ _
  | spine r' args' =>
      rcases ctyS_spine_inv hu with rfl | ⟨⟨r, args, rfl⟩, _⟩
      · exact lrSCoreT_bot _ _ _ _
      · obtain ⟨hns, _, _⟩ := lrSCoreT_spine_data_of_tyIdx hL hNU hW hAA
        rw [LRSCoreT.eq_def] at h
        rw [LRSCoreT.eq_def]
        rcases h with ⟨⟨l, hl⟩, _⟩ | ⟨_, ls₁, ls₂, args₁, args₂, hM, hM', hn₁, hn₂, ⟨hconv⟩, hl₁, hl₂⟩
        · exact (hns l hl).elim
        · exact Or.inr ⟨hns, ls₂, ls₁, args₂, args₁, hM', hM, hn₂, hn₁, ⟨.symm _ _ _ _ hconv⟩, hl₂, hl₁⟩
  | pi a' g =>
      rcases ctyS_pi_inv hu with rfl | ⟨f, rfl, _, hdom, hcod, hcov⟩
      · exact lrSCoreT_bot _ _ _ _
      · rw [LRSCoreT.eq_def] at h
        obtain ⟨A₁, B₁, hr, ⟨hΓ₁⟩, hclause⟩ := h
        rw [LRSCoreT.eq_def] at hAA
        obtain ⟨_, A₁', B₁', A₁'', B₁'', hr', hr'', _, _, _, ⟨u₁, hra⟩, hrf⟩ := hAA
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr'
        subst eA; subst eB
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr''
        subst eA; subst eB
        have hltP : ∀ {s : List CptT × CptT}, s ∈ f → ∀ v ∈ s.1,
            sizeOf a' + sizeOf v < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) :=
          fun {s} hs v hv => by
            have := sizeOf_dom_lt_pi a' g
            have := sizeOf_dem_lt_lam hs hv
            omega
        rw [LRSCoreT.eq_def]
        refine ⟨A₁, B₁, hr, ⟨hΓ₁⟩, ?_⟩
        intro s hs M M' hM hM' hcM hrel
        obtain ⟨hcM⟩ := hcM
        have hrel' : ∀ v ∈ s.1, LRSCoreT R E n Γ M' M A₁ v := fun v hv =>
          (ihP a' v (hltP hs v hv)).2.1 hΓ hra (hdom s hs v hv) (hrel v hv)
        have hcore := hclause s hs M' M hM' hM ⟨.symm _ _ _ _ hcM⟩ hrel'
        rcases hcov s hs with h0 | ⟨t, ht, hcomp⟩
        · rw [h0]; exact lrSCoreT_bot _ _ _ _
        · have htyt : ∀ v ∈ t.1, CTyS E v a' := fun v hv => hdom s hs v (hcomp v hv)
          have hrelM'M : ∀ v ∈ t.1, LRSCoreT R E n Γ M' M A₁ v := fun v hv => hrel' v (hcomp v hv)
          have hrelMM : ∀ v ∈ t.1, LRSCoreT R E n Γ M M A₁ v := fun v hv =>
            (ihP a' v (hltP hs v (hcomp v hv))).2.2 hΓ hra (htyt v hv) (hrel v (hcomp v hv))
              (hrelM'M v hv)
          obtain ⟨v₁, hv₁⟩ := hrf t ht htyt M' M hM' hM ⟨.symm _ _ _ _ hcM⟩ hrelM'M
          obtain ⟨v₂, hv₂⟩ := hrf t ht htyt M M hM hM ⟨.refl _ _ _ hM⟩ hrelMM
          have hlt_t : sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
            have := sizeOf_out_lt_pi (a := a') ht
            have := sizeOf_out_lt_lam hs
            omega
          have hmoved := (ihP t.2 s.2 hlt_t).1 hΓ hv₁ (hcod s hs t ht hcomp) hcore
          exact (ihP t.2 s.2 hlt_t).2.1 hΓ hv₂ (hcod s hs t ht hcomp) hmoved

/-- `TransTmAt a u` from the package below. -/
theorem transTm_step (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) (a u : CptT)
    (ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAt R E n c' ∧ TransTyAt R E n c')
    (ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
      IrrelAt R E n a' u' ∧ SymmTmAt R E n a' u' ∧ TransTmAt R E n a' u') :
    TransTmAt R E n a u := by
  intro Γ hΓ A w hAA hu N N' N'' h₁ h₂
  cases a with
  | bot => rw [ctyS_bot_inv hu]; exact lrSCoreT_bot _ _ _ _
  | prop =>
      rw [lrSCoreT_prop_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.prop + sizeOf u := by have := CptT.sizeOf_pos CptT.prop; omega
      have h₁' := lrSCoreT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₁
      have h₂' := lrSCoreT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₂
      exact lrSCoreT_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).2 hΓ h₁' h₂')
  | sort =>
      rw [lrSCoreT_sort_iff] at hAA
      obtain ⟨_, l₁, _, h1, _⟩ := hAA
      have hlt : sizeOf u < sizeOf CptT.sort + sizeOf u := by have := CptT.sizeOf_pos CptT.sort; omega
      have h₁' := lrSCoreT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₁
      have h₂' := lrSCoreT_sortIdx_irrel hL hNU ⟨_, h1⟩ ⟨w, .refl _⟩ u h₂
      exact lrSCoreT_sortIdx_irrel hL hNU ⟨w, .refl _⟩ ⟨_, h1⟩ u ((ihQ u hlt).2 hΓ h₁' h₂')
  | lam g => rw [ctyS_lam_inv hu]; exact lrSCoreT_bot _ _ _ _
  | spine r' args' =>
      rcases ctyS_spine_inv hu with rfl | ⟨⟨r, args, rfl⟩, _⟩
      · exact lrSCoreT_bot _ _ _ _
      · obtain ⟨hns, _, _⟩ := lrSCoreT_spine_data_of_tyIdx hL hNU hW hAA
        rw [LRSCoreT.eq_def] at h₁ h₂
        rw [LRSCoreT.eq_def]
        rcases h₁ with ⟨⟨l, hl⟩, _⟩ | ⟨_, ls₁, ls₂, args₁, args₂, hM, hM', hn₁, hn₂, ⟨hconv⟩, hl₁, _⟩
        · exact (hns l hl).elim
        · rcases h₂ with ⟨⟨l, hl⟩, _⟩ | ⟨_, ls₂', ls₃, args₂', args₃, hM'', hM''', hn₂', hn₃, ⟨hconv'⟩, _, hl₃⟩
          · exact (hns l hl).elim
          · have e := hNU Γ hM' hn₂ hM'' hn₂'
            obtain ⟨hconst, hxs⟩ := foldApps_const_inj e
            injection hconst with _ hls
            subst hls; subst hxs
            exact Or.inr ⟨hns, ls₁, ls₃, args₁, args₃, hM, hM''', hn₁, hn₃,
              ⟨.trans _ _ _ _ _ hconv hconv'⟩, hl₁, hl₃⟩
  | pi a' g =>
      rcases ctyS_pi_inv hu with rfl | ⟨f, rfl, _, hdom, hcod, hcov⟩
      · exact lrSCoreT_bot _ _ _ _
      · rw [LRSCoreT.eq_def] at h₁ h₂
        obtain ⟨A₁, B₁, hr, ⟨hΓ₁⟩, hcl₁⟩ := h₁
        obtain ⟨A₁', B₁', hr', _, hcl₂⟩ := h₂
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr'
        subst eA; subst eB
        rw [LRSCoreT.eq_def] at hAA
        obtain ⟨_, A₁', B₁', A₁'', B₁'', hr', hr'', _, _, _, ⟨u₁, hra⟩, hrf⟩ := hAA
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr'
        subst eA; subst eB
        obtain ⟨eA, eB⟩ := redR_pi_unique hL hNU hr hr''
        subst eA; subst eB
        have hltP : ∀ {s : List CptT × CptT}, s ∈ f → ∀ v ∈ s.1,
            sizeOf a' + sizeOf v < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) :=
          fun {s} hs v hv => by
            have := sizeOf_dom_lt_pi a' g
            have := sizeOf_dem_lt_lam hs hv
            omega
        rw [LRSCoreT.eq_def]
        refine ⟨A₁, B₁, hr, ⟨hΓ₁⟩, ?_⟩
        intro s hs M M' hM hM' hcM hrel
        obtain ⟨hcM⟩ := hcM
        have hrelMM : ∀ v ∈ s.1, LRSCoreT R E n Γ M M A₁ v := fun v hv =>
          (ihP a' v (hltP hs v hv)).2.2 hΓ hra (hdom s hs v hv) (hrel v hv)
            ((ihP a' v (hltP hs v hv)).2.1 hΓ hra (hdom s hs v hv) (hrel v hv))
        have hc₁ := hcl₁ s hs M M hM hM ⟨.refl _ _ _ hM⟩ hrelMM
        have hc₂ := hcl₂ s hs M M' hM hM' ⟨hcM⟩ hrel
        rcases hcov s hs with h0 | ⟨t, ht, hcomp⟩
        · rw [h0]; exact lrSCoreT_bot _ _ _ _
        · have htyt : ∀ v ∈ t.1, CTyS E v a' := fun v hv => hdom s hs v (hcomp v hv)
          obtain ⟨v₂, hv₂⟩ := hrf t ht htyt M M hM hM ⟨.refl _ _ _ hM⟩ (fun v hv => hrelMM v (hcomp v hv))
          have hlt_t : sizeOf t.2 + sizeOf s.2 < sizeOf (CptT.pi a' g) + sizeOf (CptT.lam f) := by
            have := sizeOf_out_lt_pi (a := a') ht
            have := sizeOf_out_lt_lam hs
            omega
          exact (ihP t.2 s.2 hlt_t).2.2 hΓ hv₂ (hcod s hs t ht hcomp) hc₁ hc₂

/-- **The typed PER**, by strong induction on size. -/
theorem typedPER (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmT E n) (hCAt : ConvArgsTransT E n) :
    ∀ k : Nat,
      (∀ c : CptT, sizeOf c ≤ k → SymmTyAt R E n c ∧ TransTyAt R E n c) ∧
      (∀ a u : CptT, sizeOf a + sizeOf u ≤ k →
        IrrelAt R E n a u ∧ SymmTmAt R E n a u ∧ TransTmAt R E n a u) := by
  intro k
  induction k with
  | zero =>
      refine ⟨fun c hc => ?_, fun a u hau => ?_⟩
      · exact absurd hc (Nat.not_le_of_gt (CptT.sizeOf_pos c))
      · exact absurd hau (Nat.not_le_of_gt (Nat.add_pos_left (CptT.sizeOf_pos a) _))
  | succ k ih =>
      refine ⟨fun c hc => ?_, fun a u hau => ?_⟩
      · by_cases hk : sizeOf c ≤ k
        · exact ih.1 c hk
        · have ihQ : ∀ c', sizeOf c' < sizeOf c → SymmTyAt R E n c' ∧ TransTyAt R E n c' :=
            fun c' hc' => ih.1 c' (by omega)
          have ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf c →
              IrrelAt R E n a' u' ∧ SymmTmAt R E n a' u' ∧ TransTmAt R E n a' u' :=
            fun a' u' h => ih.2 a' u' (by omega)
          exact ⟨symmTy_step hL hW hCAs c ihQ ihP, transTy_step hL hNU hW hCAt c ihQ ihP⟩
      · by_cases hk : sizeOf a + sizeOf u ≤ k
        · exact ih.2 a u hk
        · have ihQ : ∀ c', sizeOf c' < sizeOf a + sizeOf u → SymmTyAt R E n c' ∧ TransTyAt R E n c' :=
            fun c' hc' => ih.1 c' (by omega)
          have ihP : ∀ a' u', sizeOf a' + sizeOf u' < sizeOf a + sizeOf u →
              IrrelAt R E n a' u' ∧ SymmTmAt R E n a' u' ∧ TransTmAt R E n a' u' :=
            fun a' u' h => ih.2 a' u' (by omega)
          exact ⟨irrel_step hL hNU hW a u ihQ ihP, symmTm_step hL hNU hW a u ihQ ihP,
            transTm_step hL hNU hW a u ihQ ihP⟩

/-! #### the corollaries -/

/-- **Irrelevance**: a demand typed at the domain code transports across the domain relation. -/
theorem lrSCoreT_irrel (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmT E n) (hCAt : ConvArgsTransT E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ A₂ : Expr Nat} {w : Level} {a u : CptT}
    (hAA : LRSCoreT R E n Γ A₁ A₂ (.sort w) a) (hu : CTyS E u a) {N N' : Expr Nat}
    (h : LRSCoreT R E n Γ N N' A₁ u) : LRSCoreT R E n Γ N N' A₂ u :=
  ((typedPER hL hNU hW hCAs hCAt _).2 a u (Nat.le_refl _)).1 hΓ hAA hu h

/-- **Symmetry of the type-level relation at every compact.** -/
theorem lrSCoreT_symm (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmT E n) (hCAt : ConvArgsTransT E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ A₂ : Expr Nat} {w : Level} {c : CptT} (h : LRSCoreT R E n Γ A₁ A₂ (.sort w) c) :
    LRSCoreT R E n Γ A₂ A₁ (.sort w) c :=
  ((typedPER hL hNU hW hCAs hCAt _).1 c (Nat.le_refl _)).1 hΓ h

/-- **Transitivity of the type-level relation at every compact.** -/
theorem lrSCoreT_trans (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmT E n) (hCAt : ConvArgsTransT E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A₁ A₂ A₃ : Expr Nat} {w : Level} {c : CptT}
    (h₁ : LRSCoreT R E n Γ A₁ A₂ (.sort w) c) (h₂ : LRSCoreT R E n Γ A₂ A₃ (.sort w) c) :
    LRSCoreT R E n Γ A₁ A₃ (.sort w) c :=
  ((typedPER hL hNU hW hCAs hCAt _).1 c (Nat.le_refl _)).2 hΓ h₁ h₂

/-- **Symmetry of the term-level relation** at a demand typed at a self-related type code. -/
theorem lrSCoreT_symm_tm (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmT E n) (hCAt : ConvArgsTransT E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A : Expr Nat} {w : Level} {a u : CptT} (hAA : LRSCoreT R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' : Expr Nat} (h : LRSCoreT R E n Γ N N' A u) : LRSCoreT R E n Γ N' N A u :=
  ((typedPER hL hNU hW hCAs hCAt _).2 a u (Nat.le_refl _)).2.1 hΓ hAA hu h

theorem lrSCoreT_trans_tm (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E)
    (hCAs : ConvArgsSymmT E n) (hCAt : ConvArgsTransT E n) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A : Expr Nat} {w : Level} {a u : CptT} (hAA : LRSCoreT R E n Γ A A (.sort w) a) (hu : CTyS E u a)
    {N N' N'' : Expr Nat} (h₁ : LRSCoreT R E n Γ N N' A u) (h₂ : LRSCoreT R E n Γ N' N'' A u) :
    LRSCoreT R E n Γ N N'' A u :=
  ((typedPER hL hNU hW hCAs hCAt _).2 a u (Nat.le_refl _)).2.2 hΓ hAA hu h₁ h₂

/-- The `ConvArgsT` premises are witnessed under `PiRowField` by §8. -/
theorem convArgsSymmT_of_piRow (hW : EnvWfT E) (hpi : PiRowField E n) : ConvArgsSymmT E n := by
  intro Γ hΓ r m hm hind ls ls' xs xs' w w' hty hty' heqN hlen hlen' h
  exact FamModelAudit.convArgs_symm_instMtype hW hpi hΓ hm hind hty hty' heqN hlen hlen' h

theorem convArgsTransT_of_piRow (hW : EnvWfT E) (hpi : PiRowField E n) : ConvArgsTransT E n := by
  intro Γ hΓ r m hm hind ls ls' ls'' xs xs' xs'' w w' w'' hty hty' hty'' heqN heqN' hlen hlen' hlen'' h h'
  exact FamModelAudit.convArgs_trans_instMtype hW hpi hΓ hm hty hty' heqN h h'

#print axioms lrSCore_sort_iff
#print axioms SortClauseT
#print axioms TypeSpineT
#print axioms LRSCoreT
#print axioms LRST
#print axioms lrSCoreT_bot
#print axioms lrSCoreT_prop_iff
#print axioms lrSCoreT_sort_iff
#print axioms lrSCoreT_prop_iff_sort
#print axioms foldApps_const_ne_sort
#print axioms foldApps_const_ne_pi
#print axioms not_redR_sort_of_normal
#print axioms not_redR_pi_of_redR_sort
#print axioms redR_pi_unique
#print axioms typeSpineT_not_sort
#print axioms lrSCoreT_sortIdx_irrel
#print axioms ConvArgsSymmT
#print axioms ConvArgsTransT
#print axioms eqN_symm'
#print axioms eqN_trans'
#print axioms eqNList_symm''
#print axioms eqNList_trans''
#print axioms IrrelAt
#print axioms SymmTmAt
#print axioms TransTmAt
#print axioms SymmTyAt
#print axioms TransTyAt
#print axioms sizeOf_dom_lt_pi
#print axioms sizeOf_out_lt_pi
#print axioms sizeOf_dem_lt_lam
#print axioms sizeOf_out_lt_lam
#print axioms sizeOf_dem_lt_pi
#print axioms typeSpineT_symm
#print axioms typeSpineT_trans
#print axioms symmTy_step
#print axioms transTy_step
#print axioms lrSCoreT_spine_data_of_tyIdx
#print axioms irrel_step
#print axioms symmTm_step
#print axioms transTm_step
#print axioms typedPER
#print axioms lrSCoreT_irrel
#print axioms lrSCoreT_symm
#print axioms lrSCoreT_trans
#print axioms lrSCoreT_symm_tm
#print axioms lrSCoreT_trans_tm
#print axioms convArgsSymmT_of_piRow
#print axioms convArgsTransT_of_piRow

end Rcic.Declarative.NativeValleys.TypedModelAudit
