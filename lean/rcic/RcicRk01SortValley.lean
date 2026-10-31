import rcic.RcicF3StepWEqW
import rcic.RcicHostPropTransfer

/-!
# RK-01 sessions 4–5 — the sort-valley decomposition of `SortUnique`/`ZeroSortCoherence`

Session-2 measurements (`research/rcic/rk01/SESSION2_MEASUREMENTS.md`): both RK-01
rows at `eqEnvT` reduce to `{LeafIface (free), CDiamond, SortUniq}`, and `SortUniq eqEnvT`
is the linchpin with four consumers. The membership/AP routes are measured dead at the
fixture (`RcicAnnLR3ModelMembershipBoundary`; `AllBelowScoped` has no producer). This
module is the syntactic route's first slice — the DECOMPOSITION, not the cells:

- §1 `Bodyless E` — every member carries no body. Both fixture environments
  (`eqEnvT`, `eqWEnv`) are bodyless, so every *reverse-delta excursion* in a valley
  walk is dead there before it starts (`delta` needs `m.body = some b`).
- §2 head-shape facts: a `foldApps` of a never-sort head is never a sort
  (`foldApps_ne_sort`), hence `natExpand t` and `iotaLhsOf w` are never sorts —
  the *iota* and *lit* primitive arms of a sort-LHS link die by shape alone.
- §3 the single-step sort-LHS classification `convT_sortLhs_cases`: under
  `NoSortAtProp E n` (no `irr` step has a sort on its left — the one primitive arm
  head shape cannot refute), every conversion link whose LHS is a sort either lands
  on a sort with `eqN` levels (`sorts`, `refl`) or is a structural wrapper
  (`symm`/`trans`/`tyConv`). Every other primitive constructor is refuted by the
  LHS head; `iota` by §2. This is the tool the valley induction (session 5) cites
  per link.
- §4 the skeleton `SortValleyFix E n`: five named cells — `chain` (V1: sort↔sort
  `TyConvT` chains respect levels, THE linchpin), `lamChain`/`appChain`/`letChain`/
  `litChain` (V2–V5: two typings of the same subterm connect the two inversion
  chains' left endpoints, the DT-012-shaped cells) — and the reduction theorem:
  `sortUnique_of_sortValleyFix : SortValleyFix E n → F8A2Support.SortUnique E n`
  (an 8-arm worker on the subject's head, recursion only under `pi`, where both
  domain and codomain are themselves sort-typed), hence
  `zeroSortCoherence_of_sortValleyFix : SortValleyFix E n → ZeroSortCoherence E n`
  by the landed `zeroSortCoherence_of_sortUnique`.

- §5 session 5 adds `litChain`-support and the fixture pins for the dead cells
  (`litChain_eqEnvT`). The session-4 skeleton's remaining cells
  (`lamChain`/`appChain`/`letChain`, `chain`) are measured CIRCULAR as stated:
  `EqGapShapeCR` derives them from `SortUniq` via PiInj — the skeleton is a
  bookkeeping reduction, not a weakening; the content is `chain` (V1).
- §6 the single-step sort-RHS classification `convT_sortRhs_cases`: under
  `Bodyless E` (kills `delta`, §1) and `NoSortAtProp E n` (kills `irr`), a
  conversion link whose RHS is a sort either comes from a sort with `eqN`
  levels, is a structural wrapper, or is a REDEx FACE (`IsRedexFace`, positive
  def-match: beta/zeta/zetaLocal/iota/eta).
- §7 the chain-arm exclusions at the fixture: all three `eqEnvT` members are
  Π-headed (`eqEnvT_mtype_pi`), so a sort-typed chain step at the fixture is
  never delta/const/lam/eta (`chainStep_liveArm`).
- §8 flattening: every `ConvT`/`TyConvT` chain is a `PrimSeq` — a wrapper-free
  spine of directed primitive steps (`primSeq_of_convT`, `primSeq_of_tyConvT`).
- §9 the excursion: `chain` (V1) is EQUIVALENT to the absence of SORT
  EXCURSIONS (`SortExcursion`: two non-sort terms with directed primitive steps
  INTO sorts, joined by a `PrimSeq`). `primSeq_sortSort` is the constructive
  disjunction (coherent OR excursion); `chainCell_of_noExcursion` discharges
  the `chain` cell at any bodyless environment with no excursion. This is the
  V1 reduction: the remaining open object at the fixture is
  `SortExcursionEqEnvT n := ∃ u v, Nonempty (SortExcursion eqEnvT n u v)`.

Nothing here constructs any cell and nothing about rows is claimed; the fixture pins
`SortValleyEqEnvT n := SortValleyFix eqEnvT n` (residue `[rcic-rk01-sortvalley-eqenvt]`)
and `SortExcursionEqEnvT` name the exact open objects. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Rk01SortValley

/-! ## §1 bodyless environments -/

/-- every member of `E` carries no body — the reverse-delta excursions of a
    valley walk are dead before they start. -/
structure Bodyless (E : ResolvedEnv) : Prop where
  body : ∀ r m, E.members r = some m → m.body = none

/-- the `Eq` prefix is bodyless: three members, all `none`. -/
theorem bodyless_eqEnvT : Bodyless eqEnvT :=
  ⟨fun r m h => by
    rw [eqEnvT_mem] at h
    by_cases h65 : r = 65
    · rw [if_pos h65] at h; cases h; rfl
    · by_cases h64 : r = 64
      · rw [if_neg h65, if_pos h64] at h; cases h; rfl
      · by_cases h63 : r = 63
        · rw [if_neg h65, if_neg h64, if_pos h63] at h; cases h; rfl
        · rw [if_neg h65, if_neg h64, if_neg h63] at h
          exact Option.noConfusion h⟩

theorem eqWEnv_mem (c : Nat) :
    eqWEnv.members c =
      if c = 68 then some eqWRec else eqWPrefix.members c := rfl

/-- the W-class fixture env is bodyless: three more members, all `none`. -/
theorem bodyless_eqWEnv : Bodyless eqWEnv :=
  ⟨fun r m h => by
    rw [eqWEnv_mem] at h
    by_cases h68 : r = 68
    · rw [if_pos h68] at h; cases h; rfl
    · rw [if_neg h68, eqWPrefix_mem] at h
      by_cases h67 : r = 67
      · rw [if_pos h67] at h; cases h; rfl
      · by_cases h66 : r = 66
        · rw [if_neg h67, if_pos h66] at h; cases h; rfl
        · rw [if_neg h67, if_neg h66, eqEnvT_mem] at h
          by_cases h65 : r = 65
          · rw [if_pos h65] at h; cases h; rfl
          · by_cases h64 : r = 64
            · rw [if_neg h65, if_pos h64] at h; cases h; rfl
            · by_cases h63 : r = 63
              · rw [if_neg h65, if_neg h64, if_pos h63] at h; cases h; rfl
              · rw [if_neg h65, if_neg h64, if_neg h63] at h
                exact Option.noConfusion h⟩

/-! ## §2 head-shape facts -/

/-- a fold of a never-sort head is never a sort. -/
theorem foldApps_ne_sort :
    ∀ {h : Expr Nat}, (∀ l, h ≠ Expr.sort l) →
    ∀ (args : List (Expr Nat)) (l : Level), foldApps h args ≠ Expr.sort l := by
  intro h hh args
  induction args generalizing h with
  | nil => intro l he; exact hh l he
  | cons x xs ih =>
      intro l he
      exact ih (fun _ he' => Expr.noConfusion he') l he

/-- a literal expansion is a const-headed spine, never a sort. -/
theorem natExpand_ne_sort (t : Nat) (l : Level) : natExpand t ≠ Expr.sort l := by
  cases t with
  | zero =>
      intro he
      exact Expr.noConfusion
        (show Expr.const 1 [] = Expr.sort l from he)
  | succ t =>
      intro he
      exact Expr.noConfusion
        (show Expr.app (Expr.const 2 []) (natExpand t) = Expr.sort l from he)

/-- a derived-iota LHS is a recursor spine (`iotaLhsOf w = recCall (.const …)`),
    never a sort. -/
theorem iotaLhsOf_ne_sort {E : ResolvedEnv} (w : IotaWitness E) (l : Level) :
    iotaLhsOf w ≠ Expr.sort l :=
  fun he =>
    foldApps_ne_sort (h := Expr.const w.recRef w.ls)
      (fun _ he' => Expr.noConfusion he')
      (w.preMajor ++ [ctorMajor w]) l
      (show foldApps (Expr.const w.recRef w.ls) (w.preMajor ++ [ctorMajor w])
          = Expr.sort l from he)

/-! ## §3 the single-step sort-LHS classification -/

/-- no sort term is typed at a Prop-sorted host — refutes the `irr` arm's leak
    (an `irr` link with a sort on the left carries exactly such a typing). Named
    open at the fixture; discharged inside the valley induction (session 5). -/
def NoSortAtProp (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {w : Level} {P : Expr Nat},
    HasTyT E n Γ P (Expr.sort Level.zero) →
    ¬ Nonempty (HasTyT E n Γ (Expr.sort w) P)

/-- the structural wrappers of `ConvT`: `refl`, `symm`, `trans`, `tyConv` —
    `True` exactly there, `False` at every primitive constructor. -/
def IsConvWrap {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : ConvT E n Γ a b T) : Prop :=
  match c with
  | .refl _ _ _ _ => True
  | .symm _ _ _ _ _ => True
  | .trans _ _ _ _ _ _ _ => True
  | .tyConv _ _ _ _ _ _ _ _ => True
  | _ => False

/-- SINGLE-STEP SORT-LHS CLASSIFICATION: under `NoSortAtProp`, every conversion
    link whose LHS is a sort either lands on a sort with `eqN` levels (`sorts`,
    `refl`) or is a structural wrapper. The primitive arms die by the LHS head
    (`beta`/`zeta`/`zetaLocal`/`delta`/`consts`/`lit`/`app`/`lam`/`pi`/`letE`/
    `eta`), `iota` by §2, and `irr` by the named premise. -/
theorem convT_sortLhs_cases {E : ResolvedEnv} {n : Nat} (hNP : NoSortAtProp E n) :
    ∀ {Γ : LCtx} {a b T : Expr Nat} (c : ConvT E n Γ a b T) (w : Level),
    a = Expr.sort w →
    (∃ l : Level, b = Expr.sort l ∧ eqN w l) ∨ IsConvWrap c := by
  intro Γ a b T c w ha
  cases c with
  | refl _ _ A h => exact Or.inl ⟨w, ha, fun _ => rfl⟩
  | symm _ _ _ _ _ => exact Or.inr trivial
  | trans _ _ _ _ _ _ _ => exact Or.inr trivial
  | tyConv _ _ _ _ _ _ _ _ => exact Or.inr trivial
  | beta _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion ha
  | zeta _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion ha
  | zetaLocal _ _ _ _ _ _ _ => exact Expr.noConfusion ha
  | delta _ _ _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion ha
  | iota _ lhs rhs _ h _ _ =>
      cases h with
      | of w' => exact absurd ha (iotaLhsOf_ne_sort w' w)
  | lit _ _ _ _ _ _ => exact Expr.noConfusion ha
  | app _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion ha
  | lam _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion ha
  | pi _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion ha
  | letE _ _ _ _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion ha
  | sorts _ l₁ l₂ h =>
      injection ha with hl
      subst hl
      exact Or.inl ⟨l₂, rfl, h⟩
  | consts _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion ha
  | eta _ _ _ _ _ => exact Expr.noConfusion ha
  | irr _ P p q hP hp _ =>
      subst ha
      exact absurd ⟨hp⟩ (hNP hP)

/-! ## §4 the skeleton: `SortUnique`/`ZeroSortCoherence` from five named cells -/

private theorem eqN_symm0 {u v : Level} (h : eqN u v) : eqN v u := fun ρ => (h ρ).symm

private theorem eqN_trans0 {u v w : Level} (h₁ : eqN u v) (h₂ : eqN v w) : eqN u w :=
  fun ρ => (h₁ ρ).trans (h₂ ρ)

private theorem eqN_imax_congr {u₁ u₂ v₁ v₂ : Level}
    (h₁ : eqN u₁ u₂) (h₂ : eqN v₁ v₂) : eqN (.imax u₁ v₁) (.imax u₂ v₂) := by
  intro ρ
  have e₁ := h₁ ρ
  have e₂ := h₂ ρ
  simp only [eval, e₁, e₂]

/-- the session-5 open cells, exactly as the worker consumes them. `chain` (V1)
    is THE linchpin (four consumers: row 1, `EqGapShapeCR`, the 76-series tile
    removal, the A-2 classification); `lamChain`/`appChain`/`letChain`/`litChain`
    are the DT-012-shaped per-head cells connecting two inversion chains' left
    endpoints. -/
structure SortValleyFix (E : ResolvedEnv) (n : Nat) : Prop where
  chain : ∀ {Γ : LCtx} {u v : Level},
    TyConvT E n Γ (Expr.sort u) (Expr.sort v) → eqN u v
  lamChain : ∀ {Γ : LCtx} {A body : Expr Nat} {B₁ B₂ : Expr Nat},
    HasTyT E n (LocalDecl.assumption A :: Γ) body B₁ →
    HasTyT E n (LocalDecl.assumption A :: Γ) body B₂ →
    Nonempty (TyConvT E n Γ (Expr.pi A B₁) (Expr.pi A B₂))
  appChain : ∀ {Γ : LCtx} {f a : Expr Nat} {A₁ B₁ A₂ B₂ : Expr Nat},
    HasTyT E n Γ f (Expr.pi A₁ B₁) → HasTyT E n Γ a A₁ →
    HasTyT E n Γ f (Expr.pi A₂ B₂) → HasTyT E n Γ a A₂ →
    Nonempty (TyConvT E n Γ (instantiate0 a B₁) (instantiate0 a B₂))
  letChain : ∀ {Γ : LCtx} {A value body : Expr Nat} {B₁ B₂ : Expr Nat},
    HasTyT E n Γ value A →
    HasTyT E n (LocalDecl.letBinding A value :: Γ) body B₁ →
    HasTyT E n (LocalDecl.letBinding A value :: Γ) body B₂ →
    Nonempty (TyConvT E n Γ (instantiate0 value B₁) (instantiate0 value B₂))
  litChain : ∀ {Γ : LCtx} {t : Nat} {T₁ T₂ : Expr Nat},
    HasTyT E n Γ (natExpand t) T₁ → HasTyT E n Γ (natExpand t) T₂ →
    Nonempty (TyConvT E n Γ T₁ T₂)

/-- the 8-arm worker on the subject's head. Each head's two typings invert to
    two `TyConvT` chains sharing (or connectable to) a left endpoint; only `pi`
    recurses (domain and codomain are themselves sort-typed). No `EnvWfT`, no
    context premise, no scope. -/
private def zscWorker {E : ResolvedEnv} {n : Nat} (V : SortValleyFix E n) :
    (e : Expr Nat) → {Γ : LCtx} → {u v : Level} →
    HasTyT E n Γ e (Expr.sort u) → HasTyT E n Γ e (Expr.sort v) → eqN u v
  | Expr.sort _, _, _, _, h1, h2 => by
      exact V.chain
        (.trans _ _ _ _ (.symmT (hasTyTInv_sortT h1 rfl)) (hasTyTInv_sortT h2 rfl))
  | Expr.pi A B, _, _, _, h1, h2 =>
      let ⟨u₁, v₁, hA₁, hB₁, c₁⟩ := hasTyTInv_pi h1 rfl
      let ⟨u₂, v₂, hA₂, hB₂, c₂⟩ := hasTyTInv_pi h2 rfl
      eqN_trans0 (eqN_symm0 (V.chain c₁))
        (eqN_trans0 (eqN_imax_congr (zscWorker V A hA₁ hA₂)
          (zscWorker V B hB₁ hB₂)) (V.chain c₂))
  | Expr.lam _ _, _, _, _, h1, h2 => by
      obtain ⟨_, B₁, _, hb₁, c₁⟩ := hasTyTInv_lam h1 rfl
      obtain ⟨_, B₂, _, hb₂, c₂⟩ := hasTyTInv_lam h2 rfl
      obtain ⟨c⟩ := V.lamChain hb₁ hb₂
      exact V.chain (.trans _ _ _ _ (.trans _ _ _ _ (.symmT c₁) c) c₂)
  | Expr.app _ _, _, _, _, h1, h2 => by
      obtain ⟨A₁, B₁, hf₁, ha₁, c₁⟩ := hasTyTInv_app h1 rfl
      obtain ⟨A₂, B₂, hf₂, ha₂, c₂⟩ := hasTyTInv_app h2 rfl
      obtain ⟨c⟩ := V.appChain hf₁ ha₁ hf₂ ha₂
      exact V.chain (.trans _ _ _ _ (.trans _ _ _ _ (.symmT c₁) c) c₂)
  | Expr.letE _ value _, _, _, _, h1, h2 => by
      obtain ⟨_, B₁, _, hv₁, hb₁, c₁⟩ := hasTyTInv_letE h1 rfl
      obtain ⟨_, B₂, _, hv₂, hb₂, c₂⟩ := hasTyTInv_letE h2 rfl
      obtain ⟨c⟩ := V.letChain hv₁ hb₁ hb₂
      exact V.chain (.trans _ _ _ _ (.trans _ _ _ _ (.symmT c₁) c) c₂)
  | Expr.bvar _, _, _, _, h1, h2 => by
      obtain ⟨A₁, hlk₁, c₁⟩ := hasTyTInv_bvar h1 rfl
      obtain ⟨A₂, hlk₂, c₂⟩ := hasTyTInv_bvar h2 rfl
      have hA : A₁ = A₂ := Option.some.inj (hlk₁.symm.trans hlk₂)
      subst hA
      exact V.chain (.trans _ _ _ _ (.symmT c₁) c₂)
  | Expr.const _ _, _, _, _, h1, h2 => by
      obtain ⟨m₁, hres₁, _, _, c₁⟩ := hasTyTInv_const h1 rfl
      obtain ⟨m₂, hres₂, _, _, c₂⟩ := hasTyTInv_const h2 rfl
      have hm : m₁ = m₂ := Option.some.inj (hres₁.symm.trans hres₂)
      subst hm
      exact V.chain (.trans _ _ _ _ (.symmT c₁) c₂)
  | Expr.lit _, _, _, _, h1, h2 => by
      obtain ⟨T₁, hex₁, c₁⟩ := hasTyTInv_lit h1 rfl
      obtain ⟨T₂, hex₂, c₂⟩ := hasTyTInv_lit h2 rfl
      obtain ⟨c⟩ := V.litChain hex₁ hex₂
      exact V.chain (.trans _ _ _ _ (.trans _ _ _ _ (.symmT c₁) c) c₂)
termination_by e _ _ _ _ _ => sizeOf e
decreasing_by all_goals simp; omega

/-- THE SKELETON: `SortUnique` reduces to the five cells. -/
theorem sortUnique_of_sortValleyFix {E : ResolvedEnv} {n : Nat} (V : SortValleyFix E n) :
    F8A2Support.SortUnique E n :=
  fun hW {_Γ} {_T} {_u} {_v} hΓ h1 h2 => zscWorker V _ h1 h2

/-- … and so does the zero fragment, by the landed restriction. -/
theorem zeroSortCoherence_of_sortValleyFix {E : ResolvedEnv} {n : Nat}
    (V : SortValleyFix E n) : HostProp.ZeroSortCoherence E n :=
  HostProp.zeroSortCoherence_of_sortUnique (sortUnique_of_sortValleyFix V)

/-- the named residue at the `Eq` prefix: the five cells at `eqEnvT`, `chain`
    the linchpin. No cell is constructed here. -/
def SortValleyEqEnvT (n : Nat) : Prop := SortValleyFix eqEnvT n

/-! ## §5 fixture-local cell discharges (cheapest first)

`litChain` at `eqEnvT` is VACUOUS: `natExpand t` mentions `const 1 []` /
`const 2 []`, and `eqEnvT` has members only at 63–65. Both the zero and the
succ expansion die at the const lookup — no `PiConvInj`, no `EnvWfT`. -/

theorem eqEnvT_members_one : eqEnvT.members 1 = none := by
  have h65 : ¬ (1:Nat) = 65 := by decide
  have h64 : ¬ (1:Nat) = 64 := by decide
  have h63 : ¬ (1:Nat) = 63 := by decide
  rw [eqEnvT_mem, if_neg h65, if_neg h64, if_neg h63]

theorem eqEnvT_members_two : eqEnvT.members 2 = none := by
  have h65 : ¬ (2:Nat) = 65 := by decide
  have h64 : ¬ (2:Nat) = 64 := by decide
  have h63 : ¬ (2:Nat) = 63 := by decide
  rw [eqEnvT_mem, if_neg h65, if_neg h64, if_neg h63]

/-- no literal expansion is typable at `eqEnvT` at all. -/
theorem noLitAt_eqEnvT (n : Nat) :
    ∀ (t : Nat) {Γ : LCtx} {T : Expr Nat}, HasTyT eqEnvT n Γ (natExpand t) T → False := by
  intro t Γ T h
  cases t with
  | zero =>
      have h' : HasTyT eqEnvT n Γ (Expr.const 1 []) T := h
      obtain ⟨m, hres, _, _, _⟩ := hasTyTInv_const h' rfl
      rw [eqEnvT_members_one] at hres
      exact Option.noConfusion hres
  | succ t' =>
      have h' : HasTyT eqEnvT n Γ (Expr.app (Expr.const 2 []) (natExpand t')) T := h
      obtain ⟨A, B, hf, _, _⟩ := hasTyTInv_app h' rfl
      have hf' : HasTyT eqEnvT n Γ (Expr.const 2 []) (Expr.pi A B) := hf
      obtain ⟨m, hres, _, _, _⟩ := hasTyTInv_const hf' rfl
      rw [eqEnvT_members_two] at hres
      exact Option.noConfusion hres

/-- CELL V5 DISCHARGED at the fixture (vacuously): two typings of a literal
    expansion at `eqEnvT` are convertible, because there are none. -/
theorem litChain_eqEnvT (n : Nat) : ∀ {Γ : LCtx} {t : Nat} {T₁ T₂ : Expr Nat},
    HasTyT eqEnvT n Γ (natExpand t) T₁ → HasTyT eqEnvT n Γ (natExpand t) T₂ →
    Nonempty (TyConvT eqEnvT n Γ T₁ T₂) := by
  intro Γ t T₁ T₂ hex₁ _
  exact (noLitAt_eqEnvT n t hex₁).elim

/-! ## §8 flattening: `TyConvT` chains to directed primitive sequences

A `TyConvT` chain composes `of` steps, each a `ConvT` that may itself be a
stack of wrappers (`refl`/`symm`/`trans`/`tyConv`). The excursion analysis
(§9) needs the wrapper-free reading: a sequence of DIRECTED PRIMITIVE steps
(`fwd`/`bwd`), each at its own (arbitrary) type — `tyConv` inners are
flattened through, so a step's recorded type need not be a sort even though
the enclosing `of` step was sort-typed. The induction is at a VARIABLE type:
a fixed sort index breaks `cases` on the stuck arms (measured this session). -/

/-- the primitives, positively (the def-match's negative direction does not
    iota-reduce at elaboration — measured this session). -/
def IsPrim {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : ConvT E n Γ a b T) : Prop :=
  match c with
  | .refl _ _ _ _ => False
  | .symm _ _ _ _ _ => False
  | .trans _ _ _ _ _ _ _ => False
  | .tyConv _ _ _ _ _ _ _ _ => False
  | _ => True

/-- a primitive step is not a wrapper. -/
theorem isPrim_notWrap {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} :
    ∀ (c : ConvT E n Γ a b T), IsPrim c → ¬ IsConvWrap c := by
  intro c
  cases c with
  | refl _ _ _ _ => intro hp _; exact hp
  | symm _ _ _ _ _ => intro hp _; exact hp
  | trans _ _ _ _ _ _ _ => intro hp _; exact hp
  | tyConv _ _ _ _ _ _ _ _ => intro hp _; exact hp
  | beta _ _ _ _ _ _ _ _ _ => intro _ hw; exact hw
  | zeta _ _ _ _ _ _ _ _ _ => intro _ hw; exact hw
  | zetaLocal _ _ _ _ _ _ _ => intro _ hw; exact hw
  | delta _ _ _ _ _ _ _ _ _ _ _ => intro _ hw; exact hw
  | iota _ _ _ _ _ _ _ => intro _ hw; exact hw
  | lit _ _ _ _ _ _ => intro _ hw; exact hw
  | app _ _ _ _ _ _ _ _ _ => intro _ hw; exact hw
  | lam _ _ _ _ _ _ _ _ _ => intro _ hw; exact hw
  | pi _ _ _ _ _ _ _ _ _ => intro _ hw; exact hw
  | letE _ _ _ _ _ _ _ _ _ _ _ _ => intro _ hw; exact hw
  | sorts _ _ _ _ => intro _ hw; exact hw
  | consts _ _ _ _ _ _ _ _ _ _ => intro _ hw; exact hw
  | eta _ _ _ _ _ => intro _ hw; exact hw
  | irr _ _ _ _ _ _ _ => intro _ hw; exact hw

/-- the wrapper-free reading of a conversion: a sequence of directed
    primitive steps. -/
inductive PrimSeq (E : ResolvedEnv) (n : Nat) : LCtx → Expr Nat → Expr Nat → Type
  | refl (Γ : LCtx) (a : Expr Nat) : PrimSeq E n Γ a a
  | fwd (Γ : LCtx) (a b T : Expr Nat) (c : ConvT E n Γ a b T) (h : IsPrim c) :
      PrimSeq E n Γ a b
  | bwd (Γ : LCtx) (a b T : Expr Nat) (c : ConvT E n Γ b a T) (h : IsPrim c) :
      PrimSeq E n Γ a b
  | trans (Γ : LCtx) (a b c : Expr Nat) (s₁ : PrimSeq E n Γ a b) (s₂ : PrimSeq E n Γ b c) :
      PrimSeq E n Γ a c

/-- flips a sequence (mutual with `primSeq_of_convT`). -/
def primSeqFlip {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b : Expr Nat} :
    PrimSeq E n Γ a b → PrimSeq E n Γ b a
  | .refl _ _ => .refl _ _
  | .fwd _ _ _ _ c h => .bwd _ _ _ _ c h
  | .bwd _ _ _ _ c h => .fwd _ _ _ _ c h
  | .trans _ _ _ _ s₁ s₂ => .trans _ _ _ _ (primSeqFlip s₂) (primSeqFlip s₁)

/-- FLATTEN: every conversion is a directed primitive sequence. The `symm`
    case flips the inner sequence; the `tyConv` case drops the type-mover (it
    is type-side bookkeeping — the term chain is the inner one); `trans`
    composes. -/
def primSeq_of_convT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat} :
    (c : ConvT E n Γ a b T) → PrimSeq E n Γ a b
  | .refl _ _ _ _ => .refl _ _
  | .symm _ _ _ _ h => primSeqFlip (primSeq_of_convT h)
  | .trans _ _ _ _ _ h₁ h₂ => .trans _ _ _ _ (primSeq_of_convT h₁) (primSeq_of_convT h₂)
  | .beta Γ A body arg B u hA hbody harg => .fwd Γ _ _ _ (.beta Γ A body arg B u hA hbody harg) trivial
  | .zeta Γ A value body B u hA hv hb => .fwd Γ _ _ _ (.zeta Γ A value body B u hA hv hb) trivial
  | .zetaLocal Γ i A v hval hty hv => .fwd Γ _ _ _ (.zetaLocal Γ i A v hval hty hv) trivial
  | .delta Γ r ls m b hres hbody htr hlen hwf hb => .fwd Γ _ _ _ (.delta Γ r ls m b hres hbody htr hlen hwf hb) trivial
  | .iota Γ lhs rhs T h hlhs hrhs => .fwd Γ _ _ _ (.iota Γ lhs rhs T h hlhs hrhs) trivial
  | .lit Γ t exp T h hexp => .fwd Γ _ _ _ (.lit Γ t exp T h hexp) trivial
  | .app Γ f g a b A B h1 h2 => .fwd Γ _ _ _ (.app Γ f g a b A B h1 h2) trivial
  | .lam Γ A A' b b' B u hA hb => .fwd Γ _ _ _ (.lam Γ A A' b b' B u hA hb) trivial
  | .pi Γ A A' B B' u v hA hB => .fwd Γ _ _ _ (.pi Γ A A' B B' u v hA hB) trivial
  | .letE Γ A A' v v' b b' B u hA hv hb => .fwd Γ _ _ _ (.letE Γ A A' v v' b b' B u hA hv hb) trivial
  | .sorts Γ l₁ l₂ h => .fwd Γ _ _ _ (.sorts Γ l₁ l₂ h) trivial
  | .consts Γ r ls ls' m hres hlen hwf hwf' h => .fwd Γ _ _ _ (.consts Γ r ls ls' m hres hlen hwf hwf' h) trivial
  | .eta Γ f A B h => .fwd Γ _ _ _ (.eta Γ f A B h) trivial
  | .irr Γ P p q hP hp hq => .fwd Γ _ _ _ (.irr Γ P p q hP hp hq) trivial
  | .tyConv _ _ _ _ _ _ h _ => primSeq_of_convT h

/-- `TyConvT` chains flatten the same way (each `of` step is a conversion at
    its own sort). NOTE the absence of a reverse reading: through `tyConv`
    inners a sequence's steps may sit at NON-sort types, which `TyConvT.of`
    cannot re-absorb — the excursion mid-chain (§9) is therefore carried as a
    `PrimSeq`, not a `TyConvT`. -/
def primSeq_of_tyConvT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat} :
    TyConvT E n Γ A B → PrimSeq E n Γ A B
  | .refl _ _ => .refl _ _
  | .of _ _ _ _ h => primSeq_of_convT h
  | .trans _ _ _ _ h₁ h₂ => .trans _ _ _ _ (primSeq_of_tyConvT h₁) (primSeq_of_tyConvT h₂)


/-! ## §6 the mirror classification: sort-RHS steps

`convT_sortLhs_cases` (§3) classifies steps whose LEFT end is a sort. The
valley induction also needs the mirror: steps whose RIGHT end is a sort. The
arms split three ways — lands on a sort with `eqN` (`sorts`, `refl`), a
structural wrapper, or a CONTRACTION FACE whose contractum is the sort
(`beta`/`zeta`/`zetaLocal`/`iota`, and `eta`, whose contractum side is the bare
`f`). `delta` dies at bodyless environments; `lit` dies because
`LiteralExpansion` pins the expansion to `natExpand t` (never a sort, §2);
`consts`/`app`/`lam`/`pi`/`letE` die by the RHS head; `irr` dies by
`NoSortAtProp` (same leak as §3). -/

/-- the contraction faces: primitive steps whose contractum side can be an
    arbitrary term (the sort appears as the contractum). -/
def IsRedexFace {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : ConvT E n Γ a b T) : Prop :=
  match c with
  | .beta _ _ _ _ _ _ _ _ _ => True
  | .zeta _ _ _ _ _ _ _ _ _ => True
  | .zetaLocal _ _ _ _ _ _ _ => True
  | .iota _ _ _ _ _ _ _ => True
  | .eta _ _ _ _ _ => True
  | _ => False

/-- SINGLE-STEP SORT-RHS CLASSIFICATION (the §3 mirror): under `Bodyless` and
    `NoSortAtProp`, every conversion link whose RHS is a sort either leaves a
    sort LHS with `eqN` levels, is a structural wrapper, or is a contraction
    face. -/
theorem convT_sortRhs_cases {E : ResolvedEnv} {n : Nat} (hB : Bodyless E)
    (hNP : NoSortAtProp E n) :
    ∀ {Γ : LCtx} {a b T : Expr Nat} (c : ConvT E n Γ a b T) (l : Level),
    b = Expr.sort l →
    (∃ l' : Level, a = Expr.sort l' ∧ eqN l' l) ∨ IsConvWrap c ∨ IsRedexFace c := by
  intro Γ a b T c l hb
  cases c with
  | refl _ _ A h => exact Or.inl ⟨l, hb, fun _ => rfl⟩
  | symm _ _ _ _ _ => exact Or.inr (Or.inl trivial)
  | trans _ _ _ _ _ _ _ => exact Or.inr (Or.inl trivial)
  | tyConv _ _ _ _ _ _ _ _ => exact Or.inr (Or.inl trivial)
  | beta _ _ _ _ _ _ _ _ _ => exact Or.inr (Or.inr trivial)
  | zeta _ _ _ _ _ _ _ _ _ => exact Or.inr (Or.inr trivial)
  | zetaLocal _ _ _ _ _ _ _ => exact Or.inr (Or.inr trivial)
  | delta _ r _ m b' hres hbody _ _ _ _ =>
      rw [hB.body r m hres] at hbody
      exact Option.noConfusion hbody
  | iota _ _ _ _ _ _ _ => exact Or.inr (Or.inr trivial)
  | lit _ t exp _ h _ =>
      cases h with
      | of => exact absurd hb (natExpand_ne_sort t l)
  | app _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion hb
  | lam _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion hb
  | pi _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion hb
  | letE _ _ _ _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion hb
  | sorts _ l₁ l₂ h =>
      injection hb with hl
      subst hl
      exact Or.inl ⟨l₁, rfl, h⟩
  | consts _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion hb
  | eta _ _ _ _ _ => exact Or.inr (Or.inr trivial)
  | irr _ P _ q hP _ hq =>
      subst hb
      exact absurd ⟨hq⟩ (hNP hP)

/-! ## §7 the dead chain arms at the `Eq` fixture

A `TyConvT` chain composes `of` steps, each a `ConvT` whose type index is a
sort. At a BODYLESS environment whose members all carry Π-headed `mtype`s
(the `Eq` fixture is exactly this), four primitive arms can never be such a
step: `lam`/`eta` are typed at `.pi A B` (index clash), `delta` needs a body,
and `consts` is typed at `instantiateLevels ls m.mtype`, which is Π-headed
hence never a sort. Stated at a variable type with the sort-typedness as an
equation (a fixed sort index would break `cases` on the stuck arms — measured
this session). The atoms reachable through `tyConv` inners may still carry
these arms at NON-sort types; the excursion mid-chain (§9) is where that
matters, and this section only constrains the direct `of` composition. -/

/-- `instantiateLevels` never turns a Π-headed term into a sort. -/
theorem instantiateLevels_ne_sort_of_pi {ls : List Level} {a b : Expr Nat} {w : Level} :
    instantiateLevels ls (Expr.pi a b) ≠ Expr.sort w := by
  intro h
  exact Expr.noConfusion h

/-- every `eqEnvT` member's stored type is Π-headed. -/
theorem eqEnvT_mtype_pi (r : Nat) (m : CheckedMember) (hres : eqEnvT.members r = some m) :
    ∃ a b : Expr Nat, m.mtype = Expr.pi a b := by
  rw [eqEnvT_mem] at hres
  by_cases h65 : r = 65
  · rw [if_pos h65] at hres; cases hres; exact ⟨_, _, rfl⟩
  · by_cases h64 : r = 64
    · rw [if_neg h65, if_pos h64] at hres; cases hres; exact ⟨_, _, rfl⟩
    · rw [if_neg h65, if_neg h64] at hres
      by_cases h63 : r = 63
      · rw [if_pos h63] at hres; cases hres; exact ⟨_, _, rfl⟩
      · rw [if_neg h63] at hres; exact Option.noConfusion hres

/-- the arms that CAN be a sort-typed chain step (positive form: the def-
    match's negative direction does not iota-reduce, measured this session). -/
def IsLiveChainArm {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : ConvT E n Γ a b T) : Prop :=
  match c with
  | .refl _ _ _ _ => True
  | .symm _ _ _ _ _ => True
  | .trans _ _ _ _ _ _ _ => True
  | .tyConv _ _ _ _ _ _ _ _ => True
  | .beta _ _ _ _ _ _ _ _ _ => True
  | .zeta _ _ _ _ _ _ _ _ _ => True
  | .zetaLocal _ _ _ _ _ _ _ => True
  | .iota _ _ _ _ _ _ _ => True
  | .lit _ _ _ _ _ _ => True
  | .app _ _ _ _ _ _ _ _ _ => True
  | .pi _ _ _ _ _ _ _ _ _ => True
  | .letE _ _ _ _ _ _ _ _ _ _ _ _ => True
  | .sorts _ _ _ _ => True
  | .irr _ _ _ _ _ _ _ => True
  | _ => False

/-- at a bodyless Π-headed-mtype environment (the `Eq` fixture qualifies), every
    sort-TYPED conversion step is a live arm — no `delta` (no bodies), no
    `consts` (Π-headed `mtype` instantiation is never a sort), no `lam`/`eta`
    (their type index is `.pi A B`, clashing with the sort). -/
theorem chainStep_liveArm {E : ResolvedEnv} {n : Nat} (hB : Bodyless E)
    (hPi : ∀ r m, E.members r = some m → ∃ a b, m.mtype = Expr.pi a b) :
    ∀ {Γ : LCtx} {a b T : Expr Nat} (c : ConvT E n Γ a b T) {w : Level},
    T = Expr.sort w → IsLiveChainArm c := by
  intro Γ a b T c w hT
  cases c with
  | delta _ r _ m _ hres hbody _ _ _ _ =>
      rw [hB.body r m hres] at hbody
      exact Option.noConfusion hbody
  | consts _ r ls _ m hres _ _ _ _ =>
      obtain ⟨a', b', hm⟩ := hPi r m hres
      rw [hm] at hT
      exact absurd hT (instantiateLevels_ne_sort_of_pi (a := a') (b := b'))
  | lam _ _ _ _ _ _ _ _ _ => exact Expr.noConfusion hT
  | eta _ _ _ _ _ => exact Expr.noConfusion hT
  | refl _ _ _ _ => trivial
  | symm _ _ _ _ _ => trivial
  | trans _ _ _ _ _ _ _ => trivial
  | tyConv _ _ _ _ _ _ _ _ => trivial
  | beta _ _ _ _ _ _ _ _ _ => trivial
  | zeta _ _ _ _ _ _ _ _ _ => trivial
  | zetaLocal _ _ _ _ _ _ _ => trivial
  | iota _ _ _ _ _ _ _ => trivial
  | lit _ _ _ _ _ _ => trivial
  | app _ _ _ _ _ _ _ _ _ => trivial
  | pi _ _ _ _ _ _ _ _ _ => trivial
  | letE _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | sorts _ _ _ _ => trivial
  | irr _ _ _ _ _ _ _ => trivial

/-- the fixture qualifies. -/
theorem chainStep_liveArm_eqEnvT {n : Nat} :
    ∀ {Γ : LCtx} {a b T : Expr Nat} (c : ConvT eqEnvT n Γ a b T) {w : Level},
    T = Expr.sort w → IsLiveChainArm c :=
  chainStep_liveArm bodyless_eqEnvT eqEnvT_mtype_pi

/-! ## §9 the excursion: the exact obstruction shape for V1

`chain` (V1) says sort↔sort `TyConvT` chains respect `eqN`. Flattening (§8)
plus the two classifications (§3/§6) pin the obstruction EXACTLY: a chain
either is `eqN`-coherent all the way, or it contains a SORT EXCURSION — two
NON-sort terms `X`/`Y`, each with a directed PRIMITIVE step INTO a sort (the
contraction faces, §6), joined by a wrapper-free mid-chain. `delta` faces die
at bodyless environments inside §6 itself; `iota` faces carry the recursor
spine shape (§2). No badness field is carried: the consumer direction is
constructive (the disjunction); at a `¬eqN` chain the right disjunct is forced,
and under `eqN`-coherent prefixes the excursion's levels transfer
(`eqN u u'`, `eqN v v'`), making it genuinely level-incompatible. -/

/-- a redex face's LHS is never a sort (the contraction shapes all have
    constructor-headed LHSes; `iota`'s is the recursor spine, §2). -/
theorem redexFace_lhs_ne_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (c : ConvT E n Γ a b T) (hF : IsRedexFace c) (l : Level) : a ≠ Expr.sort l := by
  cases c with
  | beta Γ A body arg B u hA hbody harg =>
      intro he; exact Expr.noConfusion he
  | zeta Γ A value body B u hA hv hb =>
      intro he; exact Expr.noConfusion he
  | zetaLocal Γ i A v hval hty hv =>
      intro he; exact Expr.noConfusion he
  | iota Γ lhs rhs T h hlhs hrhs =>
      cases h with
      | of w => intro he; exact absurd he (iotaLhsOf_ne_sort w l)
  | eta Γ f A B h =>
      intro he; exact Expr.noConfusion he
  | refl _ _ _ _ => exact (hF : False).elim
  | symm _ _ _ _ _ => exact (hF : False).elim
  | trans _ _ _ _ _ _ _ => exact (hF : False).elim
  | tyConv _ _ _ _ _ _ _ _ => exact (hF : False).elim
  | delta _ _ _ _ _ _ _ _ _ _ _ => exact (hF : False).elim
  | lit _ _ _ _ _ _ => exact (hF : False).elim
  | app _ _ _ _ _ _ _ _ _ => exact (hF : False).elim
  | lam _ _ _ _ _ _ _ _ _ => exact (hF : False).elim
  | pi _ _ _ _ _ _ _ _ _ => exact (hF : False).elim
  | letE _ _ _ _ _ _ _ _ _ _ _ _ => exact (hF : False).elim
  | sorts _ _ _ _ => exact (hF : False).elim
  | consts _ _ _ _ _ _ _ _ _ _ => exact (hF : False).elim
  | irr _ _ _ _ _ _ _ => exact (hF : False).elim

/-- constructive case split on whether a term is a sort. -/
theorem expr_sort_cases (p : Expr Nat) :
    (∃ l : Level, p = Expr.sort l) ∨ (∀ l : Level, p ≠ Expr.sort l) := by
  cases p with
  | sort l => exact Or.inl ⟨l, rfl⟩
  | bvar _ => exact Or.inr fun _ he => Expr.noConfusion he
  | const _ _ => exact Or.inr fun _ he => Expr.noConfusion he
  | app _ _ => exact Or.inr fun _ he => Expr.noConfusion he
  | lam _ _ => exact Or.inr fun _ he => Expr.noConfusion he
  | pi _ _ => exact Or.inr fun _ he => Expr.noConfusion he
  | letE _ _ _ => exact Or.inr fun _ he => Expr.noConfusion he
  | lit _ => exact Or.inr fun _ he => Expr.noConfusion he

/-- A SORT EXCURSION at `E n`, at levels `u v`: two non-sort terms, each with
    a directed primitive step INTO the respective sort (the contraction
    faces), joined by a wrapper-free mid-chain. -/
def SortExcursion (E : ResolvedEnv) (n : Nat) (u v : Level) : Prop :=
  ∃ (Γ : LCtx) (X Y T₁ T₂ : Expr Nat),
    (∀ l, X ≠ Expr.sort l) ∧ (∀ l, Y ≠ Expr.sort l) ∧
    (∃ c₁ : ConvT E n Γ X (Expr.sort u) T₁, IsPrim c₁) ∧
    (∃ c₂ : ConvT E n Γ Y (Expr.sort v) T₂, IsPrim c₂) ∧
    Nonempty (PrimSeq E n Γ X Y)

/-- FROM A SORT: a sequence starting at a sort either lands on a sort
    `eqN`-compatibly, or has a LAST entry face — a directed primitive step
    `X → sort u'` with `X` non-sort, the suffix chain from `X`, and the
    prefix compatibility (`eqN u u'`, or an excursion already inside the
    prefix). -/
theorem primSeq_fromSort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hB : Bodyless E) (hNP : NoSortAtProp E n) :
    ∀ {a m : Expr Nat} (s : PrimSeq E n Γ a m) (u : Level), a = Expr.sort u →
    (∃ l, m = Expr.sort l ∧ eqN u l) ∨
    (∃ (u' : Level) (T₁ X : Expr Nat), (∀ l, X ≠ Expr.sort l) ∧
      (∃ c₁ : ConvT E n Γ X (Expr.sort u') T₁, IsPrim c₁) ∧
      Nonempty (PrimSeq E n Γ X m) ∧
      (eqN u u' ∨ ∃ u₀ v₀, Nonempty (SortExcursion E n u₀ v₀))) := by
  intro a m s
  induction s with
  | refl =>
      intro u ha
      exact Or.inl ⟨u, ha, fun _ => rfl⟩
  | fwd =>
      rename_i a'' b T c h
      intro u ha
      rcases convT_sortLhs_cases hNP c u ha with hL | hW
      · exact Or.inl hL
      · exact absurd hW (isPrim_notWrap c h)
  | bwd =>
      rename_i a'' b T c h
      intro u ha
      subst ha
      rcases convT_sortRhs_cases hB hNP c u rfl with hL | hW | hF
      · obtain ⟨l', hl', hu'⟩ := hL
        exact Or.inl ⟨l', hl', eqN_symm0 hu'⟩
      · exact absurd hW (isPrim_notWrap c h)
      · exact Or.inr ⟨u, T, _, redexFace_lhs_ne_sort c hF, ⟨c, h⟩,
          ⟨PrimSeq.refl _ _⟩, Or.inl (fun _ => rfl)⟩
  | trans =>
      rename_i a'' p c s₁ s₂ ih₁ ih₂
      intro u ha
      rcases expr_sort_cases p with ⟨l, hl⟩ | hns
      · subst hl
        rcases ih₁ u ha with ⟨l', hl', hu⟩ | hR
        · have hll : l = l' := by injection hl'
          rcases ih₂ l rfl with ⟨l₂, hc, hl₂⟩ | hR2
          · exact Or.inl ⟨l₂, hc, eqN_trans0 hu (hll ▸ hl₂)⟩
          · obtain ⟨v', T₂, Y, hY, hc₂, ⟨suffix⟩, hd⟩ := hR2
            refine Or.inr ⟨v', T₂, Y, hY, hc₂, ⟨suffix⟩, ?_⟩
            rcases hd with hd | hex
            · exact Or.inl (eqN_trans0 hu (hll ▸ hd))
            · exact Or.inr hex
        · obtain ⟨u', T₁, X, hX, hc₁, ⟨suffix⟩, hd⟩ := hR
          exact Or.inr ⟨u', T₁, X, hX, hc₁,
            ⟨PrimSeq.trans _ _ _ _ suffix s₂⟩, hd⟩
      · rcases ih₁ u ha with ⟨l', hl', _⟩ | hR
        · exact absurd hl' (hns l')
        · obtain ⟨u', T₁, X, hX, hc₁, ⟨suffix⟩, hd⟩ := hR
          exact Or.inr ⟨u', T₁, X, hX, hc₁,
            ⟨PrimSeq.trans _ _ _ _ suffix s₂⟩, hd⟩

/-- TO A SORT (the mirror): a sequence ending at a sort either starts at a
    sort `eqN`-compatibly, or has a FIRST exit face — a directed primitive
    step `Y → sort v'` with `Y` non-sort, the prefix chain into `Y`, and the
    suffix compatibility (`eqN v v'`, or an excursion already inside the
    suffix). -/
theorem primSeq_toSort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hB : Bodyless E) (hNP : NoSortAtProp E n) :
    ∀ {m b : Expr Nat} (s : PrimSeq E n Γ m b) (v : Level), b = Expr.sort v →
    (∃ l, m = Expr.sort l ∧ eqN l v) ∨
    (∃ (v' : Level) (T₂ Y : Expr Nat), (∀ l, Y ≠ Expr.sort l) ∧
      (∃ c₂ : ConvT E n Γ Y (Expr.sort v') T₂, IsPrim c₂) ∧
      Nonempty (PrimSeq E n Γ m Y) ∧
      (eqN v v' ∨ ∃ u₀ v₀, Nonempty (SortExcursion E n u₀ v₀))) := by
  intro m b s
  induction s with
  | refl =>
      intro v hv
      exact Or.inl ⟨v, hv, fun _ => rfl⟩
  | fwd =>
      rename_i a'' b T c h
      intro v hv
      subst hv
      rcases convT_sortRhs_cases hB hNP c v rfl with hL | hW | hF
      · exact Or.inl hL
      · exact absurd hW (isPrim_notWrap c h)
      · exact Or.inr ⟨v, T, _, redexFace_lhs_ne_sort c hF, ⟨c, h⟩,
          ⟨PrimSeq.refl _ _⟩, Or.inl (fun _ => rfl)⟩
  | bwd =>
      rename_i a'' b T c h
      intro v hv
      rcases convT_sortLhs_cases hNP c v hv with hL | hW
      · obtain ⟨l, hl, hv''⟩ := hL
        exact Or.inl ⟨l, hl, eqN_symm0 hv''⟩
      · exact absurd hW (isPrim_notWrap c h)
  | trans =>
      rename_i a'' p c s₁ s₂ ih₁ ih₂
      intro v hv
      rcases expr_sort_cases p with ⟨l, hl⟩ | hns
      · subst hl
        rcases ih₂ v hv with ⟨l', hl', hv'⟩ | hR2
        · have hll : l = l' := by injection hl'
          rcases ih₁ l rfl with ⟨l₂, hm, hl₂⟩ | hR
          · exact Or.inl ⟨l₂, hm, eqN_trans0 hl₂ (hll ▸ hv')⟩
          · obtain ⟨v'', T₂, Y, hY, hc₂, ⟨pref⟩, hd⟩ := hR
            refine Or.inr ⟨v'', T₂, Y, hY, hc₂, ⟨pref⟩, ?_⟩
            rcases hd with hd | hex
            · exact Or.inl (eqN_trans0 (eqN_symm0 (hll ▸ hv')) hd)
            · exact Or.inr hex
        · obtain ⟨v', T₂, Y, hY, hc₂, ⟨pref⟩, hd⟩ := hR2
          exact Or.inr ⟨v', T₂, Y, hY, hc₂,
            ⟨PrimSeq.trans _ _ _ _ s₁ pref⟩, hd⟩
      · rcases ih₂ v hv with ⟨l', hl', _⟩ | hR2
        · exact absurd hl' (hns l')
        · obtain ⟨v', T₂, Y, hY, hc₂, ⟨pref⟩, hd⟩ := hR2
          exact Or.inr ⟨v', T₂, Y, hY, hc₂,
            ⟨PrimSeq.trans _ _ _ _ s₁ pref⟩, hd⟩

/-- THE V1 REDUCTION: every sort↔sort chain is `eqN`-coherent or contains an
    excursion. -/
theorem primSeq_sortSort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (hB : Bodyless E) (hNP : NoSortAtProp E n) :
    ∀ {u v : Level} (s : PrimSeq E n Γ (Expr.sort u) (Expr.sort v)),
    eqN u v ∨ ∃ u₀ v₀, Nonempty (SortExcursion E n u₀ v₀) := by
  intro u v s
  rcases primSeq_fromSort hB hNP s u rfl with hL | hR
  · obtain ⟨l, hl, hu⟩ := hL
    have hlv : l = v := by injection hl with hq; exact hq.symm
    exact Or.inl (hlv ▸ hu)
  · obtain ⟨u', T₁, X, hX, hc₁, ⟨sfx⟩, _⟩ := hR
    rcases primSeq_toSort hB hNP sfx v rfl with ⟨l, hl, _⟩ | hR2
    · exact absurd hl (hX l)
    · obtain ⟨v', T₂, Y, hY, hc₂, pref, _⟩ := hR2
      exact Or.inr ⟨u', v', Γ, X, Y, T₁, T₂, hX, hY, hc₁, hc₂, pref⟩

/-- the `TyConvT` reading of the reduction. -/
theorem sortChain_eqN_or_excursion {E : ResolvedEnv} {n : Nat}
    (hB : Bodyless E) (hNP : NoSortAtProp E n) :
    ∀ {Γ : LCtx} {u v : Level},
    TyConvT E n Γ (Expr.sort u) (Expr.sort v) →
    eqN u v ∨ ∃ u₀ v₀, Nonempty (SortExcursion E n u₀ v₀) :=
  fun h => primSeq_sortSort hB hNP (primSeq_of_tyConvT h)

/-- the consumer direction, constructive: no excursion anywhere ⇒ V1 (the
    `chain` cell of `SortValleyFix`) at every bodyless environment. -/
theorem chainCell_of_noExcursion {E : ResolvedEnv} {n : Nat}
    (hB : Bodyless E) (hNP : NoSortAtProp E n)
    (hNo : ∀ u v : Level, ¬ Nonempty (SortExcursion E n u v)) :
    ∀ {Γ : LCtx} {u v : Level},
    TyConvT E n Γ (Expr.sort u) (Expr.sort v) → eqN u v :=
  fun h => (sortChain_eqN_or_excursion hB hNP h).elim id
    (fun ⟨u₀, v₀, hex⟩ => absurd hex (hNo u₀ v₀))

/-- the residue at the `Eq` prefix, renamed: V1 there is exactly the absence
    of sort excursions (plus the named `NoSortAtProp` leak). -/
def SortExcursionEqEnvT (n : Nat) : Prop :=
  ∃ u v : Level, Nonempty (SortExcursion eqEnvT n u v)


#print axioms bodyless_eqEnvT
#print axioms bodyless_eqWEnv
#print axioms foldApps_ne_sort
#print axioms natExpand_ne_sort
#print axioms iotaLhsOf_ne_sort
#print axioms convT_sortLhs_cases
#print axioms sortUnique_of_sortValleyFix
#print axioms zeroSortCoherence_of_sortValleyFix
#print axioms noLitAt_eqEnvT
#print axioms litChain_eqEnvT
#print axioms convT_sortRhs_cases
#print axioms chainStep_liveArm
#print axioms chainStep_liveArm_eqEnvT
#print axioms isPrim_notWrap
#print axioms primSeq_of_convT
#print axioms primSeqFlip
#print axioms primSeq_of_tyConvT
#print axioms redexFace_lhs_ne_sort
#print axioms expr_sort_cases
#print axioms primSeq_fromSort
#print axioms primSeq_toSort
#print axioms primSeq_sortSort
#print axioms sortChain_eqN_or_excursion
#print axioms chainCell_of_noExcursion

end Rcic.Declarative.Rk01SortValley
