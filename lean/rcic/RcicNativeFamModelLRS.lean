import rcic.RcicNativeFamModelK
import rcic.RcicNativePiModelTermDFund
import rcic.RcicNativePiModelDeltaIotaTerm
import rcic.RcicNativePiModelLRTermDSubst
import rcic.RcicTypedWeaken

/-!
# RcicNativeFamModelLRS — the substitution-style family relation over a parametric readback

The relation the three walls force (`#7666` W-DEMAND / W-ZETALOCAL, `#7670` W-K), built on the
landed context-aware machinery (`RcicNativeFamModel` §6/§8: `WhStepCtx`, `WhRedCtx`, `ctxEnvI`)
and against the readback *interface* rather than one readback, so that `WhStepCtx` (main),
`WhStepK` (#7670) and the unified `WhStepCK` (devin-desktop/readback-ck, not yet pushed) are
instances of one definition.

* **§0 Readback interface.**  `Readback := LCtx → Expr Nat → Expr Nat → Prop`; `RedR R Γ` its
  reflexive-transitive closure; `ReadbackLaws E R` the five facts the relation's lemmas use
  (sorts, Π-types and admitted family spines are normal; head congruence; β).  `WhStepCtx E` and
  `WhStepK E n` satisfy them (`readbackLaws_whStepCtx`, `readbackLaws_whStepK`).
* **§1 The relation.**  ONE relation `LRSCore R E n Γ M M' A c` on terms at a type index, by
  well-founded recursion on the compact (as `LRTermDCore`); the type level is the sort-indexed
  instance, so type and term levels are mutual by construction.
  - `sort` / `pi` / `spine` at a type index read back with `RedR R Γ` (W-ZETALOCAL, W-K are
    readback facts, not relation facts);
  - the **Π codomain is substitution-style** (point 2): for every pair of typed, *convertible*
    arguments related at the step's demand, the instantiated codomains are related at the step's
    output.  This answers W-DEMAND (`lrSCore_idPiProp_both`: the unrealisable demand `sort` on
    `P : Sort 0` is a hypothesis on the arguments, not a demand on the open variable), and the
    syntactic `ConvT` on the arguments is what `#7657` §6 showed `LRTermDCore.lam` lacks
    (`lrSCore_polyPi_diag`: the `polyPi` instance holds, so nothing forces
    `TyConvT (Π (Sort 0) (Sort 0)) (Sort 0)`);
  - the spine clause splits by the type's readback: at a sort, `TypeSpineR` (the `famSpine` /
    `otherSpine` readings of `LRTypeFamIN`/`LRTypeFamK`, so `famAppRow` reads off the same
    relation as `piRow`); otherwise the data-spine reading of `LRTermDCore`;
  - `LRS := IsPropTyR ∨ LRSCore` is the proposition collapse with a readback-aware guard.
* **§2 Structural lemmas** (`lrSCore_expand`, read-offs `lrSCore_pi_components`,
  `lrSCore_famApp_components`), **§3 the two statements** — `FundamentalLRST` (typed type-level
  chain form; consumers `piRowField_of_fundamentalLRST`, `famAppRow_of_fundamentalLRST`) and
  `FundamentalS` (the related-substitution form, point 3, over `RelSubst`/`envOfSubst` with
  `RcicSubstT`'s `substT`), with `FundamentalSCtx` its identity-substitution corollary
  (`fundamentalSCtx_of_fundamentalS`, under `RelSubstId`, witnessed on let-free contexts by
  `relSubst_id_of_noLet`).
* **§4 One positive lemma per wall**, each the point where the old statements were refuted:
  W-ZETALOCAL (`lrSCore_zetaSortCtx`/`_symm`, `lrSCore_zetaLocalPiCtx`/`_symm` at `pi ⊥ []`),
  W-DEMAND (`lrSCore_idPiProp_both`, at every compact including `idPiPropSortStep`, for EVERY
  readback), W-K (`lrSCore_whStepK_kRec`/`_symm`, `lrSCore_whStepK_mixAnd`/`_symm` at `pi ⊥ []`,
  `lrSCore_whStepK_etaK_app`); and the tooth that the parametrisation is load-bearing
  (`not_fundamentalLRST_whStepCtx_trueEnvU`).
* **§5 Point 5.**  `TypeSoundnessICtx` (`SemEqI (ctxEnvI Γ)`) is **refuted** for every `E, n` by
  the landed closed `irr`-under-Π pair at `Γ = []` (`not_typeSoundnessICtx`); the `zetaLocal`
  instances hold (`semEqI_ctxEnvI_zetaLocalPiCtx`).  Model soundness is not the replacement for
  `TypeSoundnessI`; the relation carries its own transport.
* **§6 For the family lane.**  W-DEMAND refutes `FundamentalLRFamINT` and `FundamentalLRFamIN`
  for EVERY `E, n` (`not_fundamentalLRFamINT_idPiProp`, `not_fundamentalLRFamIN_idPiProp`) —
  independently of W-K's `trueEnvU` instance.  W-ZETALOCAL does not (§8's `zetaSortCtx` lemmas).

**Not claimed.**  Neither `FundamentalLRST` nor `FundamentalS` is derived; the bridge between them
(`trans` of chains with compact transport across the middle type) and every case of the
induction are the named remainder.  `closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.FamModelLRSAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaTermAudit
open Rcic.Declarative.NativeValleys.PiModelTermDFundAudit
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit

/-! ### §0 — the readback interface -/

/-- A readback: a context-indexed one-step weak-head relation. -/
abbrev Readback : Type := LCtx → Expr Nat → Expr Nat → Prop

/-- Reflexive-transitive closure of a readback. -/
inductive RedR (R : Readback) (Γ : LCtx) : Expr Nat → Expr Nat → Prop
  | refl (e : Expr Nat) : RedR R Γ e e
  | step {a b c : Expr Nat} (h : R Γ a b) (hs : RedR R Γ b c) : RedR R Γ a c

/-- Normal for a readback. -/
def NormalR (R : Readback) (Γ : LCtx) (X : Expr Nat) : Prop := ∀ Y, ¬ R Γ X Y

theorem redR_trans {R : Readback} {Γ : LCtx} {a b c : Expr Nat}
    (h₁ : RedR R Γ a b) (h₂ : RedR R Γ b c) : RedR R Γ a c := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem redR_single {R : Readback} {Γ : LCtx} {a b : Expr Nat} (h : R Γ a b) : RedR R Γ a b :=
  .step h (.refl _)

/-- What the relation's lemmas use of a readback. -/
structure ReadbackLaws (E : ResolvedEnv) (R : Readback) : Prop where
  sort_normal : ∀ (Γ : LCtx) (u : Level) (e : Expr Nat), ¬ R Γ (.sort u) e
  pi_normal : ∀ (Γ : LCtx) (A B e : Expr Nat), ¬ R Γ (.pi A B) e
  famApp_normal : EnvWfT E → ∀ (Γ : LCtx) {r : Nat} {m : CheckedMember},
    E.members r = some m → m.mclass = .inductiveM →
    ∀ (ls : List Level) (xs : List (Expr Nat)) (e : Expr Nat), ¬ R Γ (foldApps (.const r ls) xs) e
  appHead : ∀ (Γ : LCtx) {f f' : Expr Nat} (a : Expr Nat), R Γ f f' → R Γ (.app f a) (.app f' a)
  beta : ∀ (Γ : LCtx) (A b a : Expr Nat), R Γ (.app (.lam A b) a) (instantiate0 a b)

variable {R : Readback} {E : ResolvedEnv} {n : Nat}

theorem redR_sort_eq (hL : ReadbackLaws E R) {Γ : LCtx} {u : Level} {e : Expr Nat}
    (h : RedR R Γ (.sort u) e) : e = .sort u := by
  cases h with
  | refl => rfl
  | step hs _ => exact (hL.sort_normal _ _ _ hs).elim

theorem redR_pi_eq (hL : ReadbackLaws E R) {Γ : LCtx} {A B e : Expr Nat}
    (h : RedR R Γ (.pi A B) e) : e = .pi A B := by
  cases h with
  | refl => rfl
  | step hs _ => exact (hL.pi_normal _ _ _ _ hs).elim

theorem redR_famApp_eq (hL : ReadbackLaws E R) (hW : EnvWfT E) {Γ : LCtx}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls : List Level} {xs : List (Expr Nat)} {e : Expr Nat}
    (h : RedR R Γ (foldApps (.const r ls) xs) e) : e = foldApps (.const r ls) xs := by
  cases h with
  | refl => rfl
  | step hs _ => exact (hL.famApp_normal hW _ hm hind _ _ _ hs).elim

theorem redR_appHead (hL : ReadbackLaws E R) {Γ : LCtx} {f f' a : Expr Nat}
    (h : RedR R Γ f f') : RedR R Γ (.app f a) (.app f' a) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (hL.appHead _ _ hs) ih

/-! #### the two landed readbacks are instances -/

theorem redR_of_whRedCtx {Γ : LCtx} {a b : Expr Nat} (h : WhRedCtx E Γ a b) :
    RedR (WhStepCtx E) Γ a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step hs ih

theorem whRedCtx_of_redR {Γ : LCtx} {a b : Expr Nat} (h : RedR (WhStepCtx E) Γ a b) :
    WhRedCtx E Γ a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step hs ih

theorem redR_of_whRedK {Γ : LCtx} {a b : Expr Nat} (h : WhRedK E n Γ a b) :
    RedR (WhStepK E n) Γ a b := by
  induction h with
  | refl e => exact .refl e
  | step hs _ ih => exact .step hs ih

theorem readbackLaws_whStepCtx (E : ResolvedEnv) : ReadbackLaws E (WhStepCtx E) where
  sort_normal := fun _ _ _ h => whStepCtx_sort_false h
  pi_normal := fun _ _ _ _ h => whStepCtx_pi_false h
  famApp_normal := fun hW _ _ _ hm hind _ xs _ h => whStepCtx_famApp_false hW hm hind xs h
  appHead := fun _ _ _ _ h => .appHead h
  beta := fun _ A b a => .beta A b a

theorem readbackLaws_whStepK (E : ResolvedEnv) (n : Nat) : ReadbackLaws E (WhStepK E n) where
  sort_normal := fun _ _ _ h => whStepK_sort_false h
  pi_normal := fun _ _ _ _ h => whStepK_pi_false h
  famApp_normal := fun hW _ _ _ hm hind _ xs _ h => whStepK_famApp_false hW hm hind xs h
  appHead := fun _ _ _ _ h => .appHead h
  beta := fun _ A b a => .ctx (.beta A b a)

/-! ### §1 — the relation -/

/-- The type is a proposition and does not read back to a universe. -/
def IsPropTyR (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A : Expr Nat) : Prop :=
  Nonempty (HasTyT E n Γ A (.sort .zero)) ∧ ∀ l, ¬ RedR R Γ A (.sort l)

/-- The type-code reading of a spine compact with head `r`: the `famSpine` reading for an
    admitted inductive family (saturated spines, `eqNList`, `ConvArgsT` along the left stored
    telescope — exactly `LRTypeFamIN.famSpine`), or the `otherSpine` reading (convertible
    reducts — `LRTypeFamK.otherSpine`). -/
def TypeSpineR (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' : Expr Nat) (r : Nat) :
    Prop :=
  (∃ (m : CheckedMember) (ls ls' : List Level) (xs xs' : List (Expr Nat)) (w w' : Level),
      E.members r = some m ∧ m.mclass = .inductiveM ∧
      RedR R Γ M (foldApps (.const r ls) xs) ∧ RedR R Γ M' (foldApps (.const r ls') xs') ∧
      Nonempty (HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w)) ∧
      Nonempty (HasTyT E n Γ (foldApps (.const r ls') xs') (.sort w')) ∧
      Nonempty (TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) ∧
      eqNList ls ls' ∧
      xs.length = (piDomsOf m.mtype).length ∧ xs'.length = (piDomsOf m.mtype).length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs') ∨
  ((∀ m, E.members r = some m → m.mclass ≠ .inductiveM) ∧
    ∃ X X', RedR R Γ M X ∧ RedR R Γ M' X' ∧ Nonempty (TyConvT E n Γ X X'))

theorem typeSpineR_expand {Γ : LCtx} {M M' X X' : Expr Nat} {r : Nat}
    (hX : RedR R Γ M X) (hX' : RedR R Γ M' X') (h : TypeSpineR R E n Γ X X' r) :
    TypeSpineR R E n Γ M M' r := by
  rcases h with ⟨m, ls, ls', xs, xs', w, w', hm, hind, h1, h2, rest⟩ | ⟨hnot, Y, Y', h1, h2, hc⟩
  · exact Or.inl ⟨m, ls, ls', xs, xs', w, w', hm, hind, redR_trans hX h1, redR_trans hX' h2, rest⟩
  · exact Or.inr ⟨hnot, Y, Y', redR_trans hX h1, redR_trans hX' h2, hc⟩

/-- **The substitution-style family relation**, by well-founded recursion on the compact.
    `LRSCore R E n Γ M M' A c`: `M`, `M'` of type `A` are related at `c`, in context `Γ`, for
    readback `R`.  The type level is the sort-indexed instance. -/
def LRSCore (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) :
    CptI → Prop
  | .bot => True
  | .sort => (∃ l, RedR R Γ A (.sort l)) ∧ ∃ u u', RedR R Γ M (.sort u) ∧ RedR R Γ M' (.sort u')
  | .pi a f => (∃ l, RedR R Γ A (.sort l)) ∧
      ∃ A₁ B₁ A₂ B₂ : Expr Nat, RedR R Γ M (.pi A₁ B₁) ∧ RedR R Γ M' (.pi A₂ B₂) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) ∧
        (∃ u₁, LRSCore R E n Γ A₁ A₂ (.sort u₁) a) ∧
        ∀ s ∈ f, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          Nonempty (ConvT E n Γ N N' A₁) → (∀ u ∈ s.1, LRSCore R E n Γ N N' A₁ u) →
          ∃ v, LRSCore R E n Γ (instantiate0 N B₁) (instantiate0 N' B₂) (.sort v) s.2
  | .lam g =>
      ∃ A₁ B₁ : Expr Nat, ∃ w : Level, RedR R Γ A (.pi A₁ B₁) ∧
        Nonempty (CtxWfT E n (.assumption A₁ :: Γ)) ∧
        Nonempty (HasTyT E n (.assumption A₁ :: Γ) B₁ (.sort w)) ∧
        ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N A₁ → HasTyT E n Γ N' A₁ →
          Nonempty (ConvT E n Γ N N' A₁) → (∀ u ∈ s.1, LRSCore R E n Γ N N' A₁ u) →
          (IsPropTyR R E n Γ (instantiate0 N B₁) ∨
            LRSCore R E n Γ (.app M N) (.app M' N') (instantiate0 N B₁) s.2)
  | .spine r args =>
      ((∃ l, RedR R Γ A (.sort l)) ∧ TypeSpineR R E n Γ M M' r) ∨
      ((∀ l, ¬ RedR R Γ A (.sort l)) ∧
        ∃ ls₁ ls₂ args₁ args₂,
          RedR R Γ M (foldApps (.const r ls₁) args₁) ∧
          RedR R Γ M' (foldApps (.const r ls₂) args₂) ∧
          NormalR R Γ (foldApps (.const r ls₁) args₁) ∧
          NormalR R Γ (foldApps (.const r ls₂) args₂) ∧
          Nonempty (ConvT E n Γ (foldApps (.const r ls₁) args₁)
            (foldApps (.const r ls₂) args₂) A) ∧
          ∃ (Ts : List (Expr Nat)) (hb1 : args.length ≤ args₁.length)
            (hb2 : args.length ≤ args₂.length) (hl : args.length = Ts.length),
            ∀ i : Fin args.length,
              IsPropTyR R E n Γ (Ts.get (i.cast hl)) ∨
              LRSCore R E n Γ (args₁.get (i.castLE hb1)) (args₂.get (i.castLE hb2))
                (Ts.get (i.cast hl)) (args.get i))
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have h₃ := sizeOfD_fst_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ f from ‹_›)
       have h₃ := sizeOfD_snd_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
       have h₂ := List.sizeOf_lt_of_mem (show u ∈ s.1 from ‹_›)
       have h₃ := sizeOfD_fst_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
       have h₃ := sizeOfD_snd_lt s
       omega)
    | (have h₁ := List.sizeOf_lt_of_mem (List.getElem_mem i.isLt)
       omega)

/-- The relation with the proposition collapse. -/
def LRS (R : Readback) (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (M M' A : Expr Nat) (c : CptI) :
    Prop :=
  IsPropTyR R E n Γ A ∨ LRSCore R E n Γ M M' A c

theorem lrSCore_bot (Γ : LCtx) (M M' A : Expr Nat) : LRSCore R E n Γ M M' A .bot := by
  rw [LRSCore.eq_def]; trivial

theorem lrS_bot (Γ : LCtx) (M M' A : Expr Nat) : LRS R E n Γ M M' A .bot :=
  Or.inr (lrSCore_bot _ _ _ _)

/-- Totality at propositions (the `irr` interface). -/
theorem lrS_prop_total {Γ : LCtx} {A M M' : Expr Nat}
    (hA : Nonempty (HasTyT E n Γ A (.sort .zero))) (hns : ∀ l, ¬ RedR R Γ A (.sort l))
    (c : CptI) : LRS R E n Γ M M' A c :=
  Or.inl ⟨hA, hns⟩

/-- A readback-sorted index is never a proposition index. -/
theorem not_isPropTyR_of_redR_sort {Γ : LCtx} {A : Expr Nat} {u : Level}
    (h : RedR R Γ A (.sort u)) : ¬ IsPropTyR R E n Γ A :=
  fun hP => hP.2 u h

/-! ### §2 — structural lemmas -/

/-- Closure under readback expansion on both sides, by recursion on the compact. -/
theorem lrSCore_expand (hL : ReadbackLaws E R) {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : RedR R Γ M X) (hX' : RedR R Γ M' X') :
    (c : CptI) → LRSCore R E n Γ X X' A c → LRSCore R E n Γ M M' A c
  | .bot, _ => lrSCore_bot _ _ _ _
  | .sort, h => by
      rw [LRSCore.eq_def] at h
      rw [LRSCore.eq_def]
      obtain ⟨hA, u, u', h1, h2⟩ := h
      exact ⟨hA, u, u', redR_trans hX h1, redR_trans hX' h2⟩
  | .pi a f, h => by
      rw [LRSCore.eq_def] at h
      rw [LRSCore.eq_def]
      obtain ⟨hA, A₁, B₁, A₂, B₂, h1, h2, rest⟩ := h
      exact ⟨hA, A₁, B₁, A₂, B₂, redR_trans hX h1, redR_trans hX' h2, rest⟩
  | .spine r args, h => by
      rw [LRSCore.eq_def] at h
      rw [LRSCore.eq_def]
      rcases h with ⟨hA, hT⟩ | ⟨hns, ls₁, ls₂, args₁, args₂, h1, h2, rest⟩
      · exact Or.inl ⟨hA, typeSpineR_expand hX hX' hT⟩
      · exact Or.inr ⟨hns, ls₁, ls₂, args₁, args₂, redR_trans hX h1, redR_trans hX' h2, rest⟩
  | .lam g, h => by
      rw [LRSCore.eq_def] at h
      rw [LRSCore.eq_def]
      obtain ⟨A₁, B₁, w, hA, hΓ₁, hB₁, happ⟩ := h
      refine ⟨A₁, B₁, w, hA, hΓ₁, hB₁, fun s hs N N' hN hN' hc hrel => ?_⟩
      rcases happ s hs N N' hN hN' hc hrel with hP | hcore
      · exact Or.inl hP
      · exact Or.inr (lrSCore_expand hL (redR_appHead hL hX) (redR_appHead hL hX') s.2 hcore)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  have h₁ := List.sizeOf_lt_of_mem (show s ∈ g from ‹_›)
  have h₃ := sizeOfD_snd_lt s
  omega

theorem lrS_expand (hL : ReadbackLaws E R) {Γ : LCtx} {M M' X X' A : Expr Nat}
    (hX : RedR R Γ M X) (hX' : RedR R Γ M' X') (c : CptI) (h : LRS R E n Γ X X' A c) :
    LRS R E n Γ M M' A c := by
  rcases h with hP | h
  · exact Or.inl hP
  · exact Or.inr (lrSCore_expand hL hX hX' c h)

/-- A type is never a step function. -/
theorem lrSCore_lam_at_sort_false (hL : ReadbackLaws E R) {Γ : LCtx} {M M' : Expr Nat}
    {u : Level} {g : List (List CptI × CptI)}
    (h : LRSCore R E n Γ M M' (.sort u) (.lam g)) : False := by
  rw [LRSCore.eq_def] at h
  obtain ⟨A₁, B₁, _, hA, _, _, _⟩ := h
  exact Expr.noConfusion (redR_sort_eq hL hA)

/-- Reading the Π clause at `pi ⊥ []` for two syntactic Π-types: the component conversions. -/
theorem lrSCore_pi_components (hL : ReadbackLaws E R) {Γ : LCtx} {A₁ B₁ A₂ B₂ : Expr Nat}
    {u : Level} (h : LRSCore R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort u) (.pi .bot [])) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  rw [LRSCore.eq_def] at h
  obtain ⟨_, A₁', B₁', A₂', B₂', h1, h2, _, hdom, hcod, _, _⟩ := h
  have e₁ := redR_pi_eq hL h1
  have e₂ := redR_pi_eq hL h2
  injection e₁ with eA₁ eB₁
  injection e₂ with eA₂ eB₂
  subst eA₁; subst eB₁; subst eA₂; subst eB₂
  exact ⟨hdom, hcod⟩

/-- Reading the spine clause at a sort for two admitted family spines: levels, lengths,
    pointwise argument conversion (the `famAppRow` data). -/
theorem lrSCore_famApp_components (hL : ReadbackLaws E R) (hW : EnvWfT E) {Γ : LCtx}
    {r : Nat} {m : CheckedMember} (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {u : Level} {args : List CptI}
    (h : LRSCore R E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')
      (.sort u) (.spine r args)) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' := by
  rw [LRSCore.eq_def] at h
  rcases h with ⟨_, hT⟩ | ⟨hns, _⟩
  · rcases hT with ⟨m', ls₁, ls₁', xs₁, xs₁', _, _, hm', _, h1, h2, _, _, _, heqN, hlen, hlen', hargs⟩
      | ⟨hnot, _⟩
    · rw [hm] at hm'
      injection hm' with hm_eq
      subst hm_eq
      have e₁ := redR_famApp_eq hL hW hm hind h1
      have e₂ := redR_famApp_eq hL hW hm hind h2
      obtain ⟨hconst₁, hxs₁⟩ := foldApps_const_inj e₁
      obtain ⟨hconst₂, hxs₂⟩ := foldApps_const_inj e₂
      injection hconst₁ with _ hls₁
      injection hconst₂ with _ hls₂
      subst hls₁; subst hxs₁; subst hls₂; subst hxs₂
      exact ⟨heqN, hlen.trans hlen'.symm, hargs⟩
    · exact (hnot m hm hind).elim
  · exact (hns u (.refl _)).elim

/-! ### §3 — the two statements and their consumers -/

/-- **Typed type-level chain form** (what `piRow` / `famAppRow` consume): at every compact of
    the left type in the context's environment. -/
def FundamentalLRST (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A A' : Expr Nat} {u : Level},
    HasTyT E n Γ A (.sort u) → TyConvT E n Γ A A' →
    ∀ c, ApproxI (ctxEnvI Γ) A c → LRSCore R E n Γ A A' (.sort u) c

theorem piRowField_of_fundamentalLRST (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (F : FundamentalLRST R E n) : PiRowField E n := by
  intro Γ hΓ A B A' B' hc
  rcases tyConvT_firstOf_data hc with heq | ⟨_, u, hc₀, _⟩
  · injection heq with hA hB
    subst hA; subst hB
    exact ⟨⟨.refl Γ A⟩, ⟨.refl (.assumption A :: Γ) B⟩⟩
  · have hPi : HasTyT E n Γ (.pi A B) (.sort u) := (convEnds hW hΓ hc₀).1
    exact lrSCore_pi_components hL (F hΓ hPi hc (.pi .bot []) (approxI_pi_bot_nil (ctxEnvI Γ) A B))

theorem famAppRow_of_fundamentalLRST (hL : ReadbackLaws E R) (hW : EnvWfT E)
    (F : FundamentalLRST R E n) : Rcic.Syn.FamAppRowLink E n :=
  fun {Γ} hΓ {r _ ls _ xs _ _} hm hind hty hc =>
    lrSCore_famApp_components hL hW hm hind
      (F hΓ hty hc (.spine r (botVecI xs)) (approxI_famApp_botVecI (ctxEnvI Γ) r ls xs))

/-- The model environment of a substitution into `Δ`: variable `i` denotes the full approximation
    set of `σ i` in `Δ`'s context environment. -/
def envOfSubst (Δ : LCtx) (σ : SubstT) : EnvI := fun i c => ApproxI (ctxEnvI Δ) (σ i) c

/-- **Related substitutions** `Δ ⊢ σ ≡ σ' : Γ`: typed, convertible, related at every compact of
    the left substituent; let-bound variables of `Γ` are sent to terms convertible to their
    substituted values. -/
def RelSubst (R : Readback) (E : ResolvedEnv) (n : Nat) (Δ : LCtx) (σ σ' : SubstT) (Γ : LCtx) :
    Prop :=
  (∀ (i : Nat) (A : Expr Nat), lookupType Γ i = some A →
    Nonempty (HasTyT E n Δ (σ i) (substT σ A)) ∧ Nonempty (HasTyT E n Δ (σ' i) (substT σ A)) ∧
    Nonempty (ConvT E n Δ (σ i) (σ' i) (substT σ A)) ∧
    ∀ c, ApproxI (ctxEnvI Δ) (σ i) c → LRS R E n Δ (σ i) (σ' i) (substT σ A) c) ∧
  (∀ (i : Nat) (v : Expr Nat), lookupValue Γ i = some v →
    ∃ A, lookupType Γ i = some A ∧ Nonempty (ConvT E n Δ (σ i) (substT σ v) (substT σ A)))

/-- **The fundamental lemma in related-substitution form** (point 3): typing gives the diagonal
    under `σ, σ'`; conversion gives the relation, from a compact of either side. -/
def FundamentalS (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ Δ : LCtx} {σ σ' : SubstT}, CtxWfT E n Γ → CtxWfT E n Δ → RelSubst R E n Δ σ σ' Γ →
    ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
    ∀ c, ApproxI (envOfSubst Δ σ) M c →
      LRS R E n Δ (substT σ M) (substT σ' M) (substT σ A) c) ∧
  (∀ {Γ Δ : LCtx} {σ σ' : SubstT}, CtxWfT E n Γ → CtxWfT E n Δ → RelSubst R E n Δ σ σ' Γ →
    ∀ {M M' A : Expr Nat}, ConvT E n Γ M M' A →
    ∀ c, (ApproxI (envOfSubst Δ σ) M c ∨ ApproxI (envOfSubst Δ σ') M' c) →
      LRS R E n Δ (substT σ M) (substT σ' M') (substT σ A) c)

/-- The identity-substitution corollary form, at the context's own environment. -/
def FundamentalSCtx (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M A : Expr Nat}, HasTyT E n Γ M A →
    ∀ c, ApproxI (ctxEnvI Γ) M c → LRS R E n Γ M M A c) ∧
  (∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {M M' A : Expr Nat}, ConvT E n Γ M M' A →
    ∀ c, (ApproxI (ctxEnvI Γ) M c ∨ ApproxI (ctxEnvI Γ) M' c) → LRS R E n Γ M M' A c)

/-- The identity substitution is related to itself (the premise the corollary needs; it is the
    diagonal at variables, which for a let-bound variable is the diagonal of its value). -/
def RelSubstId (R : Readback) (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → RelSubst R E n Γ SubstT.id SubstT.id Γ

theorem envOfSubst_id_le (Γ : LCtx) : EnvI.le (ctxEnvI Γ) (envOfSubst Γ SubstT.id) :=
  fun _ _ h => ApproxI.bvar h

theorem fundamentalSCtx_of_fundamentalS (hid : RelSubstId R E n) (F : FundamentalS R E n) :
    FundamentalSCtx R E n := by
  refine ⟨fun {Γ} hΓ {M A} hM c hc => ?_, fun {Γ} hΓ {M M' A} hc c hcc => ?_⟩
  · have h := F.1 hΓ hΓ (hid hΓ) hM c (approxI_mono_env (envOfSubst_id_le Γ) hc)
    rwa [substT_id, substT_id] at h
  · have h := F.2 hΓ hΓ (hid hΓ) hc c
      (hcc.elim (fun h => Or.inl (approxI_mono_env (envOfSubst_id_le Γ) h))
        (fun h => Or.inr (approxI_mono_env (envOfSubst_id_le Γ) h)))
    rwa [substT_id, substT_id, substT_id] at h

/-- Let-free contexts. -/
def NoLetCtx (Γ : LCtx) : Prop := ∀ i, lookupValue Γ i = none

theorem noLetCtx_tail {d : LocalDecl} {Γ : LCtx} (h : NoLetCtx (d :: Γ)) : NoLetCtx Γ := by
  intro i
  have := h (i + 1)
  rw [Rcic.Declarative.lookupValue_cons_succ] at this
  cases hv : lookupValue Γ i with
  | none => rfl
  | some v => rw [hv] at this; exact Option.noConfusion this

/-- In a let-free context the context environment is degenerate. -/
theorem ctxEnvI_noLet : ∀ (Γ : LCtx), NoLetCtx Γ → ∀ (i : Nat) (c : CptI), ctxEnvI Γ i c → c = .bot
  | [], _, _, _, h => h
  | .assumption _ :: Γ, hnl, i, c, h => by
      cases i with
      | zero => exact h
      | succ i => exact ctxEnvI_noLet Γ (noLetCtx_tail hnl) i c h
  | .letBinding _ _ :: _, hnl, _, _, _ => by
      have := hnl 0
      exact Option.noConfusion this

/-- **Witness for `RelSubstId`**: on a let-free context the identity substitution is related to
    itself (every variable denotes `⊥` only). -/
theorem relSubst_id_of_noLet {Γ : LCtx} (hnl : NoLetCtx Γ) :
    RelSubst R E n Γ SubstT.id SubstT.id Γ := by
  refine ⟨fun i A hA => ?_, fun i v hv => ?_⟩
  · rw [substT_id]
    refine ⟨⟨.bvar Γ i A hA⟩, ⟨.bvar Γ i A hA⟩, ⟨.refl _ _ _ (.bvar Γ i A hA)⟩, fun c hc => ?_⟩
    rcases approxI_bvar_inv hc with h0 | h0
    · subst h0; exact lrS_bot _ _ _ _
    · have := ctxEnvI_noLet Γ hnl i c h0
      subst this; exact lrS_bot _ _ _ _
  · have := hnl i
    rw [this] at hv
    exact Option.noConfusion hv

/-! ### §4 — one positive lemma per wall -/

/-! #### W-ZETALOCAL — the readback is the context's -/

/-- `zetaSortCtx`, forward: `Sort 0 ≡ X` at every compact of `Sort 0`. -/
theorem lrSCore_zetaSortCtx (E : ResolvedEnv) (n : Nat) (c : CptI)
    (hc : ApproxI (ctxEnvI zetaSortCtx) (.sort .zero) c) :
    LRSCore (WhStepCtx E) E n zetaSortCtx (.sort .zero) (.bvar 0) (.sort (.succ .zero)) c := by
  rcases approxI_sort_inv hc with rfl | rfl
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    exact ⟨⟨_, .refl _⟩, _, _, .refl _, redR_of_whRedCtx (whRedCtx_zetaSortCtx_bvar0 E)⟩

/-- `zetaSortCtx`, reverse: `X ≡ Sort 0` at every compact of `X` (which are those of `Sort 0`). -/
theorem lrSCore_zetaSortCtx_symm (E : ResolvedEnv) (n : Nat) (c : CptI)
    (hc : ApproxI (ctxEnvI zetaSortCtx) (.bvar 0) c) :
    LRSCore (WhStepCtx E) E n zetaSortCtx (.bvar 0) (.sort .zero) (.sort (.succ .zero)) c := by
  have hc' : ApproxI (ctxEnvI zetaSortCtx) (.sort .zero) c := (semEqI_ctxEnvI_zetaSortCtx c).mp hc
  rcases approxI_sort_inv hc' with rfl | rfl
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    exact ⟨⟨_, .refl _⟩, _, _, redR_of_whRedCtx (whRedCtx_zetaSortCtx_bvar0 E), .refl _⟩

/-- The let-bound variable of `zetaLocalPiCtx` reads back to its value `Π (P : Sort 0), P`. -/
theorem whRedCtx_zetaLocalPiCtx_bvar0 (E : ResolvedEnv) :
    WhRedCtx E zetaLocalPiCtx (.bvar 0) idPiProp :=
  .step (.zetaLocal rfl) (.refl _)

theorem semEqI_ctxEnvI_zetaLocalPiCtx : SemEqI (ctxEnvI zetaLocalPiCtx) (.bvar 0) idPiProp :=
  semEqI_zetaLocal (ctxEnvI_respects zetaLocalPiCtx) rfl

/-! #### W-DEMAND — the Π codomain is substitution-style -/

/-- **W-DEMAND answered for EVERY readback**: both sides reading back to `Π (P : Sort 0), P` are
    related at every compact of it in any context — including `idPiPropSortStep`, whose step
    demands `sort` on the bound variable.  The codomain clause asks for related *arguments*
    `N ≡ N' : Sort 0` at that demand, and then relates `N`, `N'` themselves at `Sort 0`. -/
theorem lrSCore_idPiProp_both {Γ : LCtx} (hΓ : CtxWfT E n Γ) {M M' : Expr Nat}
    (hM : RedR R Γ M idPiProp) (hM' : RedR R Γ M' idPiProp) (c : CptI)
    (hc : ApproxI (ctxEnvI Γ) idPiProp c) :
    LRSCore R E n Γ M M' (.sort idPiPropSort) c := by
  rcases approxI_pi_inv hc with rfl | ⟨a, f, rfl, hA, hB⟩
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    refine ⟨⟨_, .refl _⟩, .sort .zero, .bvar 0, .sort .zero, .bvar 0, hM, hM',
      ⟨.assumption Γ (.sort .zero) (.succ .zero) hΓ (.sort Γ .zero)⟩,
      ⟨.refl _ _⟩, ⟨.refl _ _⟩, ⟨.succ .zero, ?_⟩, fun s hs N N' _ _ _ hrel => ?_⟩
    · rcases approxI_sort_inv hA with rfl | rfl
      · exact lrSCore_bot _ _ _ _
      · rw [LRSCore.eq_def]
        exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩
    · refine ⟨.zero, ?_⟩
      show LRSCore R E n Γ N N' (.sort .zero) s.2
      rcases approxI_bvar_inv (hB s hs) with h0 | hmem
      · rw [h0]; exact lrSCore_bot _ _ _ _
      · exact hrel s.2 hmem

/-- The W-DEMAND point itself: `idPiProp` at `idPiPropSortStep`, every `E, n`, every readback. -/
theorem lrSCore_idPiProp_sortStep (R : Readback) (E : ResolvedEnv) (n : Nat) :
    LRSCore R E n [] idPiProp idPiProp (.sort idPiPropSort) idPiPropSortStep :=
  lrSCore_idPiProp_both .nil (.refl _) (.refl _) idPiPropSortStep approxI_idPiProp_sortStep

/-- **W-ZETALOCAL at the `piRow` compact**: `Π (P : Sort 0), P ≡ X` under
    `let X := Π (P : Sort 0), P`, at every compact of the value, both directions. -/
theorem lrSCore_zetaLocalPiCtx (E : ResolvedEnv) (n : Nat) (c : CptI)
    (hc : ApproxI (ctxEnvI zetaLocalPiCtx) idPiProp c) :
    LRSCore (WhStepCtx E) E n zetaLocalPiCtx idPiProp (.bvar 0) (.sort idPiPropSort) c :=
  lrSCore_idPiProp_both (zetaLocalPiCtx_wf E n) (.refl _)
    (redR_of_whRedCtx (whRedCtx_zetaLocalPiCtx_bvar0 E)) c hc

theorem lrSCore_zetaLocalPiCtx_symm (E : ResolvedEnv) (n : Nat) (c : CptI)
    (hc : ApproxI (ctxEnvI zetaLocalPiCtx) (.bvar 0) c) :
    LRSCore (WhStepCtx E) E n zetaLocalPiCtx (.bvar 0) idPiProp (.sort idPiPropSort) c :=
  lrSCore_idPiProp_both (zetaLocalPiCtx_wf E n)
    (redR_of_whRedCtx (whRedCtx_zetaLocalPiCtx_bvar0 E)) (.refl _) c
    ((semEqI_ctxEnvI_zetaLocalPiCtx c).mp hc)

/-- `#7657` §6's tooth does not transfer: the `polyPi` diagonal holds, because the step clause
    requires `N ≡ N'` (so the codomain conversion is a weakening of it), where `LRTermDCore.lam`
    forced `TyConvT (Π (Sort 0) (Sort 0)) (Sort 0)`. -/
theorem lrSCore_polyPi_diag (hL : ReadbackLaws E R) (hcl : EnvClosed E) :
    LRSCore R E n [] polyPi polyPi (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) polyPiCpt := by
  unfold polyPiCpt
  rw [LRSCore.eq_def]
  refine ⟨.sort (.succ .zero), .sort (.succ .zero), .succ (.succ .zero), .refl _,
    ⟨.assumption [] _ _ .nil (.sort [] _)⟩, ⟨.sort _ _⟩, fun s hs N N' hN hN' hc _ => ?_⟩
  have hs' := List.mem_singleton.mp hs
  subst hs'
  refine Or.inr ?_
  show LRSCore R E n [] (.app polyPi N) (.app polyPi N') (.sort (.succ .zero)) (.pi .bot [])
  rw [LRSCore.eq_def]
  obtain ⟨hcN⟩ := hc
  refine ⟨⟨_, .refl _⟩, N, lift 0 1 N, N', lift 0 1 N',
    .step (hL.beta _ _ _ _) (.refl _), .step (hL.beta _ _ _ _) (.refl _),
    ⟨.assumption [] N (.succ .zero) .nil hN⟩, ⟨.of _ _ _ _ hcN⟩,
    ⟨.of _ _ _ _ (convTWeaken (.assumption N) hcl (c := 0) hcN)⟩,
    ⟨.succ .zero, lrSCore_bot _ _ _ _⟩, fun _ hs => (List.not_mem_nil _ hs).elim⟩

/-! #### W-K — the readback takes the proposition-major step -/

/-- `Sort 0 ≡ True.rec.{2} (λ_.Sort 1) (Sort 0) x` at every compact of `Sort 0`, every proof `x`,
    every context, with the K-aware readback `WhStepK`. -/
theorem lrSCore_whStepK_kRec {Γ : LCtx} {x : Expr Nat}
    (hx : HasTyT trueEnvU n Γ x (.const 0 [])) (c : CptI)
    (hc : ApproxI (ctxEnvI Γ) (.sort .zero) c) :
    LRSCore (WhStepK trueEnvU n) trueEnvU n Γ (.sort .zero) (kRec x) (.sort (.succ .zero)) c := by
  rcases approxI_sort_inv hc with rfl | rfl
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    exact ⟨⟨_, .refl _⟩, _, _, .refl _, redR_of_whRedK (whRedK_kRec hx)⟩

/-- ... and in the reverse direction: the compacts of `kRec x` are `⊥` or recursor spines, read as
    type codes through the `otherSpine` reading (the recursor is not an inductive family). -/
theorem lrSCore_whStepK_kRec_symm {Γ : LCtx} {x : Expr Nat}
    (hx : HasTyT trueEnvU n Γ x (.const 0 [])) (c : CptI)
    (hc : ApproxI (ctxEnvI Γ) (kRec x) c) :
    LRSCore (WhStepK trueEnvU n) trueEnvU n Γ (kRec x) (.sort .zero) (.sort (.succ .zero)) c := by
  have hc' : ApproxI (ctxEnvI Γ)
      (foldApps (.const 2 [.succ (.succ .zero)]) [kMot, .sort .zero, x]) c := hc
  rcases approxI_foldApps_const_inv hc' with rfl | ⟨us, rfl, _⟩
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    refine Or.inl ⟨⟨_, .refl _⟩, Or.inr ⟨fun m hm hind => ?_, .sort .zero, .sort .zero,
      redR_of_whRedK (whRedK_kRec hx), .refl _, ⟨.refl _ _⟩⟩⟩
    have e' : trueRecMemberU = m := Option.some.inj hm
    subst e'
    exact MemberClass.noConfusion hind

/-- The fieldful K point: `Sort 0 → Sort 0 ≡ And.rec … h` at every compact of the Π-type
    (including `pi ⊥ []`, the `piRow` probe), with `WhStepK`. -/
theorem lrSCore_whStepK_mixAnd (c : CptI) (hc : ApproxI (ctxEnvI mixAndCtx) mixPi c) :
    LRSCore (WhStepK andEnvU 0) andEnvU 0 mixAndCtx mixPi mixAndRedex
      (.sort (.imax (.succ .zero) (.succ .zero))) c := by
  rcases approxI_pi_inv hc with rfl | ⟨a, f, rfl, hA, hB⟩
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    refine ⟨⟨_, .refl _⟩, .sort .zero, .sort .zero, .sort .zero, .sort .zero, .refl _,
      redR_of_whRedK whRedK_mixAndRedex,
      ⟨.assumption _ _ _ Rcic.Domain.Model.PiInversion.mixAndCtx_wf (.sort _ .zero)⟩,
      ⟨.refl _ _⟩, ⟨.refl _ _⟩, ⟨.succ .zero, ?_⟩, fun s hs _ _ _ _ _ _ => ⟨.succ .zero, ?_⟩⟩
    · rcases approxI_sort_inv hA with rfl | rfl
      · exact lrSCore_bot _ _ _ _
      · rw [LRSCore.eq_def]
        exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩
    · show LRSCore (WhStepK andEnvU 0) andEnvU 0 mixAndCtx (.sort .zero) (.sort .zero)
        (.sort (.succ .zero)) s.2
      rcases approxI_sort_inv (hB s hs) with h0 | h0
      · rw [h0]; exact lrSCore_bot _ _ _ _
      · rw [h0, LRSCore.eq_def]
        exact ⟨⟨_, .refl _⟩, _, _, .refl _, .refl _⟩

theorem lrSCore_whStepK_mixAnd_symm (c : CptI) (hc : ApproxI (ctxEnvI mixAndCtx) mixAndRedex c) :
    LRSCore (WhStepK andEnvU 0) andEnvU 0 mixAndCtx mixAndRedex mixPi
      (.sort (.imax (.succ .zero) (.succ .zero))) c := by
  have hc' : ApproxI (ctxEnvI mixAndCtx)
      (foldApps (.const 2 [.succ (.succ .zero)])
        [.bvar 4, .bvar 3, mixAndMot, mixAndMin, .bvar 0]) c := hc
  rcases approxI_foldApps_const_inv hc' with rfl | ⟨us, rfl, _⟩
  · exact lrSCore_bot _ _ _ _
  · rw [LRSCore.eq_def]
    refine Or.inl ⟨⟨_, .refl _⟩, Or.inr ⟨fun m hm hind => ?_, mixPi, mixPi,
      redR_of_whRedK whRedK_mixAndRedex, .refl _, ⟨.refl _ _⟩⟩⟩
    have e' : andRecMemberU = m := Option.some.inj hm
    subst e'
    exact MemberClass.noConfusion hind

/-- The η-K output demands: `(λ p : True. Sort 0) N ~ True.rec M (Sort 0) N'` at every compact of
    the left, every proof `N'` (β on the left, the proposition-major step on the right). -/
theorem lrSCore_whStepK_etaK_app {Γ : LCtx} {N N' : Expr Nat}
    (hN' : HasTyT trueEnvU n Γ N' (.const 0 [])) (c : CptI)
    (hc : ApproxI (ctxEnvI Γ) (.app (.lam (.const 0 []) (.sort .zero)) N) c) :
    LRSCore (WhStepK trueEnvU n) trueEnvU n Γ (.app (.lam (.const 0 []) (.sort .zero)) N)
      (.app kRecHead N') (.sort (.succ .zero)) c := by
  rcases approxI_app_inv hc with rfl | ⟨g, s, rfl, hf, hsf, _⟩ | ⟨r, args, u, rfl, hf, _⟩
  · exact lrSCore_bot _ _ _ _
  · rcases approxI_lam_inv hf with hbot | ⟨f', hg, hbody⟩
    · exact CptI.noConfusion hbot
    · injection hg with hg'
      subst hg'
      rcases approxI_sort_inv (hbody s hsf) with hs2 | hs2
      · rw [hs2]; exact lrSCore_bot _ _ _ _
      · rw [hs2, LRSCore.eq_def]
        exact ⟨⟨_, .refl _⟩, _, _, .step (.ctx (.beta _ _ _)) (.refl _),
          redR_of_whRedK (whRedK_kRec hN')⟩
  · exact nomatch hf

/-- **The parametrisation is load-bearing**: with the context-aware but K-blind readback
    `WhStepCtx`, the chain form is refuted at `trueEnvU` by the K point (`#7670`'s wall). -/
theorem not_fundamentalLRST_whStepCtx_trueEnvU (n : Nat) :
    ¬ FundamentalLRST (WhStepCtx trueEnvU) trueEnvU n := by
  intro F
  have h := F (kVarCtx_wf n) (.sort kVarCtx .zero) (kRec_tyConvT (kVar_ty n)) .sort
    (.sort _ .zero)
  rw [LRSCore.eq_def] at h
  obtain ⟨_, _, u', _, h2⟩ := h
  have := whRedCtx_kRec_bvar_eq (whRedCtx_of_redR h2)
  exact Expr.noConfusion this

/-! ### §5 — point 5: context-relative model soundness is refuted; the `zetaLocal` control holds -/

/-- Model soundness for type conversions at the context's environment — the natural replacement
    for the refuted `TypeSoundnessI`. -/
def TypeSoundnessICtx (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B : Expr Nat} {u : Level}, ConvT E n Γ A B (.sort u) →
    SemEqI (ctxEnvI Γ) A B

/-- **Refuted for every `E, n`** by the landed closed `irr`-under-Π pair in `Γ = []`
    (`ctxEnvI [] = EnvI.bot`): untyped demands distinguish two proofs of one proposition, so the
    model is not sound for `irr` under a binder at any environment. -/
theorem not_typeSoundnessICtx (E : ResolvedEnv) (n : Nat) : ¬ TypeSoundnessICtx E n :=
  fun hS => not_semEqI_closedIrrPi (hS .nil (closedIrrPi_conv E n))

/-! ### §6 — for the family lane: W-DEMAND refutes the landed family statements for every `E, n` -/

/-- An assumption-bound (or out-of-range) variable takes no `WhStepCtx` step. -/
theorem whStepCtx_bvar_none_false {Γ : LCtx} {i : Nat} {e : Expr Nat}
    (h0 : lookupValue Γ i = none) (h : WhStepCtx E Γ (.bvar i) e) : False := by
  cases h with
  | zetaLocal hv => rw [h0] at hv; exact Option.noConfusion hv
  | iota hI =>
      obtain ⟨r, ls, pre, major, _, hlhs, _, _⟩ := derivedIotaU_recHead hI
      exact foldApps_const_ne_bvar (pre ++ [major]) i hlhs.symm

theorem whRedCtx_bvar_none_eq {Γ : LCtx} {i : Nat} {e : Expr Nat}
    (h0 : lookupValue Γ i = none) (h : WhRedCtx E Γ (.bvar i) e) : e = .bvar i := by
  cases h with
  | refl => rfl
  | step hs _ => exact (whStepCtx_bvar_none_false h0 hs).elim

/-- `LRTypeFamIN` at `idPiProp`, `idPiPropSortStep`: the codomain clause under the binder asks the
    assumption `P : Sort 0` to read back to a sort. -/
theorem not_lrTypeFamIN_idPiProp_sortStep (E : ResolvedEnv) (n : Nat) :
    ¬ LRTypeFamIN E n [] idPiProp idPiProp idPiPropSortStep := by
  intro h
  cases h with
  | pi h₁ _ _ _ _ _ rf =>
      have hEq := whRedCtx_pi_eq h₁
      injection hEq with hA₁ hB₁
      subst hA₁; subst hB₁
      have hsort := rf ([.sort], .sort) (List.mem_singleton.mpr rfl)
      cases hsort with
      | sort hs _ =>
          exact Expr.noConfusion (whRedCtx_bvar_none_eq (Γ := .assumption (.sort .zero) :: []) (i := 0) rfl hs)

theorem not_fundamentalLRFamINT_idPiProp (E : ResolvedEnv) (n : Nat) :
    ¬ FundamentalLRFamINT E n :=
  fun F => not_lrTypeFamIN_idPiProp_sortStep E n
    (F .nil (hasTyT_idPiProp E n) (.refl [] idPiProp) idPiPropSortStep approxI_idPiProp_sortStep)

theorem not_fundamentalLRFamIN_idPiProp (E : ResolvedEnv) (n : Nat) :
    ¬ FundamentalLRFamIN E n :=
  fun F => not_lrTypeFamIN_idPiProp_sortStep E n
    (F .nil (.refl [] idPiProp) idPiPropSortStep approxI_idPiProp_sortStep)

#print axioms Readback
#print axioms RedR
#print axioms NormalR
#print axioms redR_trans
#print axioms redR_single
#print axioms ReadbackLaws
#print axioms redR_sort_eq
#print axioms redR_pi_eq
#print axioms redR_famApp_eq
#print axioms redR_appHead
#print axioms redR_of_whRedCtx
#print axioms whRedCtx_of_redR
#print axioms redR_of_whRedK
#print axioms readbackLaws_whStepCtx
#print axioms readbackLaws_whStepK
#print axioms IsPropTyR
#print axioms TypeSpineR
#print axioms typeSpineR_expand
#print axioms LRSCore
#print axioms LRS
#print axioms lrSCore_bot
#print axioms lrS_bot
#print axioms lrS_prop_total
#print axioms not_isPropTyR_of_redR_sort
#print axioms lrSCore_expand
#print axioms lrS_expand
#print axioms lrSCore_lam_at_sort_false
#print axioms lrSCore_pi_components
#print axioms lrSCore_famApp_components
#print axioms FundamentalLRST
#print axioms piRowField_of_fundamentalLRST
#print axioms famAppRow_of_fundamentalLRST
#print axioms envOfSubst
#print axioms RelSubst
#print axioms FundamentalS
#print axioms FundamentalSCtx
#print axioms RelSubstId
#print axioms envOfSubst_id_le
#print axioms fundamentalSCtx_of_fundamentalS
#print axioms NoLetCtx
#print axioms noLetCtx_tail
#print axioms ctxEnvI_noLet
#print axioms relSubst_id_of_noLet
#print axioms lrSCore_zetaSortCtx
#print axioms lrSCore_zetaSortCtx_symm
#print axioms whRedCtx_zetaLocalPiCtx_bvar0
#print axioms semEqI_ctxEnvI_zetaLocalPiCtx
#print axioms lrSCore_idPiProp_both
#print axioms lrSCore_idPiProp_sortStep
#print axioms lrSCore_zetaLocalPiCtx
#print axioms lrSCore_zetaLocalPiCtx_symm
#print axioms lrSCore_polyPi_diag
#print axioms lrSCore_whStepK_kRec
#print axioms lrSCore_whStepK_kRec_symm
#print axioms lrSCore_whStepK_mixAnd
#print axioms lrSCore_whStepK_mixAnd_symm
#print axioms lrSCore_whStepK_etaK_app
#print axioms not_fundamentalLRST_whStepCtx_trueEnvU
#print axioms TypeSoundnessICtx
#print axioms not_typeSoundnessICtx
#print axioms whStepCtx_bvar_none_false
#print axioms whRedCtx_bvar_none_eq
#print axioms not_lrTypeFamIN_idPiProp_sortStep
#print axioms not_fundamentalLRFamINT_idPiProp
#print axioms not_fundamentalLRFamIN_idPiProp

end Rcic.Declarative.NativeValleys.FamModelLRSAudit
