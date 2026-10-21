import rcic.RcicNativeReadbackCK2ModelObstruction
import rcic.RcicNativeReadbackCK2NativeControls

/-!
# RcicNativeTypedModelKG — the index-guarded typed model `ApproxTK`

#7749 kernel-refuted the global `FundamentalSAtT` for both `WhStepCK2` candidates
(`not_fundamentalSAtT_whStepCK2_eqEnv`): the landed `ApproxT.recursorProp` clause
reads an `Eq.rec` spine as its minor unconditionally, so the typed neutral fixture
`apartRec` (whose two proposition indices do not fire the native K gate) still
observes `.prop`.  No readback repair can close that; the model has to change.

## Why the guard is reduction-witnessed, not `KIndexConvAt`

The brief's candidate shape (i) guards the model's K clause by `KIndexConvAt`
itself.  That guard cannot deliver the first acceptance criterion: at the apart
fixture, `¬ KIndexConvAt` is exactly the native nonconvertibility of the two
proposition indices, and #7749's own boundary states that nonconvertibility is
never inferred from distinct syntax — the separation there goes through the
*hypothetical* Fundamental.  A `Nonempty (ConvT …)` premise is neither provable
nor refutable at the fixture, so `ApproxTK … apartRec c → c = .bot` would be
unprovable.  A monotone compact model cannot refute an equality; the guard has to
track *witnessed* native agreement instead.  `KIdxAgree` below is that witness:
weak-head joinability through the readback's own `RedR`, plus head-δ unfolding
and η on either side.  It is provable at every positive control of #7749 that
reaches K through head reduction (the β gap, the η control, δ at the index head),
and it is *refutable* at the apart fixture, at the under-binder β control, and at
δ under a binder — each by unique normal forms plus syntactic head disjointness.

## The model

`ApproxTK E R n Γ` keeps every `ApproxT` clause except `recursorProp`, which is
replaced by two clauses:

* `recursorPropK` fires **non-compositionally at the exact pre-major prefix**
  `foldApps (.const w.recRef w.ls) w.preMajor`, under the `KGateAt` certificate,
  with the per-argument demand realisation (`ApproxArgsDemandT`, reused from the
  landed model) and the same schema reading as the old clause.  Its compact is
  the one remaining major step `.lam [([], c)]`, so the saturated spine reads
  `c`, and the minor-tying is exactly the old demand machinery's.
* `recursorPropIdxFree` keeps the old compositional shortcut verbatim for
  proposition families with `w.nindices = 0` — natively, K needs no index
  agreement there (the computed and actual index lists are both empty), so the
  old clause already agrees with the native rule for them.

The `app` inversion of the guarded model gains a fourth case (the guarded prefix
itself is application-headed); the old three-case `CtxModelTLaws.app_inv` is
refuted for `ApproxTK` at the eqGap prefix — that interface obstruction, the
transport `approxTK_to_approxT`, and the per-lemma consumer status list live in
`RcicNativeTypedModelKGInterface`.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKAudit.KG

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.ReadbackCKAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ConvAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2Audit
open Rcic.Declarative.NativeValleys.ReadbackCK2IndexAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2NativeControlAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2InputsAudit
open Rcic.Declarative.NativeValleys.ReadbackCK2ModelObstructionAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat} {Γ : LCtx}

/-! ## §1 — witnessed index agreement -/

/-- Reduction-witnessed agreement of two index arguments: weak-head joinability
through the readback's own `RedR`, head-δ unfolding on either side, or η on
either side.  Each constructor mirrors the shape of one native conversion rule
(`red` for β/ι/wh reduction, `deltaL`/`deltaR` for `ConvT.delta`, `etaL`/`etaR`
for `ConvT.eta`), but the relation carries no irrelevance, no binder
congruence and no transitivity, so it stays refutable where those rules do not
apply. -/
inductive KIdxAgree (E : ResolvedEnv) (R : Readback) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Prop
  | red {a b : Expr Nat} (h : ∃ N, RedR R Γ a N ∧ RedR R Γ b N) :
      KIdxAgree E R n Γ a b
  | deltaL {r : Nat} {ls : List Level} {m : CheckedMember} {b b' : Expr Nat}
      (hd : DeltaConst E r m b)
      (h : KIdxAgree E R n Γ (instantiateLevels ls b) b') :
      KIdxAgree E R n Γ (.const r ls) b'
  | deltaR {r : Nat} {ls : List Level} {m : CheckedMember} {a b : Expr Nat}
      (hd : DeltaConst E r m b)
      (h : KIdxAgree E R n Γ a (instantiateLevels ls b)) :
      KIdxAgree E R n Γ a (.const r ls)
  | etaL {A B f : Expr Nat} (hf : HasTyT E n Γ f (.pi A B)) :
      KIdxAgree E R n Γ f (.lam A (.app (lift 0 1 f) (.bvar 0)))
  | etaR {A B f : Expr Nat} (hf : HasTyT E n Γ f (.pi A B)) :
      KIdxAgree E R n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f

/-- Agreement is reflexive at every term: both sides weak-head reduce to
themselves. -/
theorem kIdxAgree_refl (E : ResolvedEnv) (R : Readback) (n : Nat) (Γ : LCtx)
    (a : Expr Nat) : KIdxAgree E R n Γ a a :=
  .red ⟨a, .refl a, .refl a⟩

/-- A lifting is never the variable `#0`: the cut variable shifts up. -/
theorem lift01_ne_bvar0 {X : Expr Nat} (h : lift 0 1 X = .bvar 0) : False := by
  cases X with
  | bvar i =>
      simp only [lift, Nat.zero_le, if_pos] at h
      injection h with h
      omega
  | sort _ => exact Expr.noConfusion h
  | const _ _ => exact Expr.noConfusion h
  | app _ _ => exact Expr.noConfusion h
  | lam _ _ => exact Expr.noConfusion h
  | pi _ _ => exact Expr.noConfusion h
  | letE _ _ _ => exact Expr.noConfusion h
  | lit _ => exact Expr.noConfusion h

/-- Pointwise `KIdxAgree` along the computed and actual index lists. -/
def KIdxJoinListAt (E : ResolvedEnv) (R : Readback) (n : Nat) (Γ : LCtx) :
    List (Expr Nat) → List (Expr Nat) → Prop
  | [], [] => True
  | a :: as, b :: bs => KIdxAgree E R n Γ a b ∧ KIdxJoinListAt E R n Γ as bs
  | _, _ => False

/-- The model-side K gate: a legacy `IotaWitness` matching the structured
witness's reference, levels and pre-major spine, whose computed and actual index
lists are reduction-witnessed to agree.  The legacy witness is exactly #7749's
`eqConvW` shape, so the gate composes with the fixtures `KIndexConvAt` uses
without redefining any of them. -/
def KGateAt (E : ResolvedEnv) (R : Readback) (n : Nat) (Γ : LCtx)
    (w : IotaWitnessS E) : Prop :=
  ∃ w' : IotaWitness E, w'.recRef = w.recRef ∧ w'.ls = w.ls ∧
    w'.preMajor = w.preMajor ∧
    KIdxJoinListAt E R n Γ
      (resultIdxAt w' (w'.preMajor.take w'.nparams) w'.fields) (redexIdx w')

/-! ## §2 — the guarded model -/

/-- **The index-guarded typed model.**  `ApproxT`'s clauses with the
proposition-family recursor clause split into the non-compositional gated
`recursorPropK` (indexed Prop families; K gate from witnessed native index
agreement) and the unchanged compositional shortcut `recursorPropIdxFree`
(index-free proposition families, where the native K rule needs no index
agreement). -/
inductive ApproxTK (E : ResolvedEnv) (R : Readback) (n : Nat) (Γ : LCtx) :
    EnvT → Expr Nat → CptT → Prop
  | bot (ρ : EnvT) (e : Expr Nat) : ApproxTK E R n Γ ρ e .bot
  | bvar {ρ : EnvT} {i : Nat} {c : CptT} (h : ρ i c) : ApproxTK E R n Γ ρ (.bvar i) c
  | sort (ρ : EnvT) (l : Level) : ApproxTK E R n Γ ρ (.sort l) (sortCode l)
  | pi {ρ : EnvT} {A B : Expr Nat} {a : CptT} {f : List (List CptT × CptT)}
      (hA : ApproxTK E R n Γ ρ A a)
      (hT : ∀ s ∈ f, ∀ u ∈ s.1, CTyS E u a)
      (hf : ∀ s ∈ f, ApproxTK E R n Γ (EnvT.cons (demandT s.1) ρ) B s.2) :
      ApproxTK E R n Γ ρ (.pi A B) (.pi a f)
  | lam {ρ : EnvT} {A b : Expr Nat} {a : CptT} {g : List (List CptT × CptT)}
      (hA : ApproxTK E R n Γ ρ A a)
      (hT : ∀ s ∈ g, ∀ u ∈ s.1, CTyS E u a)
      (hnt : ∃ s ∈ g, s.2 ≠ .bot)
      (hb : ∀ s ∈ g, ApproxTK E R n Γ (EnvT.cons (demandT s.1) ρ) b s.2) :
      ApproxTK E R n Γ ρ (.lam A b) (.lam g)
  | app {ρ : EnvT} {f a : Expr Nat} {g : List (List CptT × CptT)} {s : List CptT × CptT}
      (hf : ApproxTK E R n Γ ρ f (.lam g)) (hs : s ∈ g)
      (ha : ∀ u ∈ s.1, ApproxTK E R n Γ ρ a u) :
      ApproxTK E R n Γ ρ (.app f a) s.2
  | const (ρ : EnvT) (r : Nat) (ls : List Level) (hrigid : RigidConst E r)
      (hnp : ¬ PropCtorT E r) :
      ApproxTK E R n Γ ρ (.const r ls) (.spine r [])
  | delta {ρ : EnvT} {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
      {c : CptT}
      (hdelta : DeltaConst E r m b)
      (h : ApproxTK E R n Γ EnvT.bot (instantiateLevels ls b) c) :
      ApproxTK E R n Γ ρ (.const r ls) c
  | recursor {ρ : EnvT} {w : IotaWitnessS E} (ls : List Level) (hnp : ¬ PropFamilyS w)
      {us_pre : List (List CptT)} {us_fields : List (List CptT)} {c : CptT}
      (hpre : us_pre.length = w.preMajor.length)
      (hflds : us_fields.length = w.fields.length)
      (h : ApproxTK E R n Γ (EnvT.pushArgs ((us_pre ++ us_fields).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c) :
      ApproxTK E R n Γ ρ (.const w.recRef ls)
        (curryStepT (us_pre ++ [ctorDemandT w.ctorRef w.nparams us_fields]) c)
  | recursorPropK {ρ : EnvT} {w : IotaWitnessS E} (hP : PropFamilyS w)
      {us : List (List CptT)} {c : CptT}
      (hgate : KGateAt E R n Γ w)
      (hpre : us.length = w.preMajor.length)
      (hargs : ApproxArgsDemandT E ρ w.preMajor us)
      (h : ApproxTK E R n Γ
          (EnvT.pushArgs ((us ++ w.fields.map (fun _ => [])).map demandT) EnvT.bot)
          (instantiateLevels w.ls w.schema) c) :
      ApproxTK E R n Γ ρ (foldApps (.const w.recRef w.ls) w.preMajor) (.lam [([], c)])
  | recursorPropIdxFree {ρ : EnvT} {w : IotaWitnessS E} (ls : List Level)
      (hP : PropFamilyS w) (hnidx : w.nindices = 0)
      {us_pre : List (List CptT)} {c : CptT}
      (hpre : us_pre.length = w.preMajor.length)
      (h : ApproxTK E R n Γ
          (EnvT.pushArgs ((us_pre ++ w.fields.map (fun _ => [])).map demandT) EnvT.bot)
          (instantiateLevels ls w.schema) c) :
      ApproxTK E R n Γ ρ (.const w.recRef ls) (curryStepT (us_pre ++ [[]]) c)
  | appSpine {ρ : EnvT} {f a : Expr Nat} {r : Nat} {args : List CptT} {u : CptT}
      (hf : ApproxTK E R n Γ ρ f (.spine r args)) (ha : ApproxTK E R n Γ ρ a u) :
      ApproxTK E R n Γ ρ (.app f a) (.spine r (args ++ [u]))
  | letE {ρ : EnvT} {A v b : Expr Nat} {c : CptT}
      (h : ApproxTK E R n Γ ρ (.app (.lam A b) v) c) :
      ApproxTK E R n Γ ρ (.letE A v b) c
  | lit {ρ : EnvT} {t : Nat} {c : CptT}
      (h : ApproxTK E R n Γ ρ (natExpand t) c) :
      ApproxTK E R n Γ ρ (.lit t) c

/-! ## §3 — the master case analysis and structural inversions -/

/-- A structured witness's pre-major spine is never empty, by its own telescope
count. -/
theorem iotaWitnessS_preMajor_ne_nil (w : IotaWitnessS E) : w.preMajor ≠ [] := by
  intro h
  have hlen := w.hpre
  rw [h, List.length_nil] at hlen
  omega

/-- The exact guarded prefix is application-headed. -/
theorem foldApps_preMajor_is_app (w : IotaWitnessS E) :
    ∃ f x, foldApps (.const w.recRef w.ls) w.preMajor = .app f x := by
  rcases list_eq_nil_or_snoc w.preMajor with hnil | ⟨pre, x, hsnoc⟩
  · exact (iotaWitnessS_preMajor_ne_nil w hnil).elim
  · rw [hsnoc, foldApps_snoc]
    exact ⟨_, x, rfl⟩

/-- The master case analysis of the guarded model, stated over variable indices
so every clause of the inductive is reachable by `cases`. -/
theorem approxTK_cases {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTK E R n Γ ρ e c) :
    c = .bot ∨
    (∃ i, e = .bvar i ∧ ρ i c) ∨
    (∃ l, e = .sort l ∧ c = sortCode l) ∨
    (∃ A B a f, e = .pi A B ∧ c = .pi a f ∧ ApproxTK E R n Γ ρ A a ∧
      ∀ s ∈ f, (∀ u ∈ s.1, CTyS E u a) ∧
        ApproxTK E R n Γ (EnvT.cons (demandT s.1) ρ) B s.2) ∨
    (∃ A b a g, e = .lam A b ∧ c = .lam g ∧ ApproxTK E R n Γ ρ A a ∧
      (∃ s ∈ g, s.2 ≠ .bot) ∧
      ∀ s ∈ g, (∀ u ∈ s.1, CTyS E u a) ∧
        ApproxTK E R n Γ (EnvT.cons (demandT s.1) ρ) b s.2) ∨
    (∃ f a g s, e = .app f a ∧ c = s.2 ∧ ApproxTK E R n Γ ρ f (.lam g) ∧ s ∈ g ∧
      ∀ u ∈ s.1, ApproxTK E R n Γ ρ a u) ∨
    (∃ r ls, e = .const r ls ∧ RigidConst E r ∧ ¬ PropCtorT E r ∧ c = .spine r []) ∨
    (∃ r ls m b, e = .const r ls ∧ DeltaConst E r m b ∧
      ApproxTK E R n Γ EnvT.bot (instantiateLevels ls b) c) ∨
    (∃ w : IotaWitnessS E, ∃ ls us_pre us_fields c₀, e = .const w.recRef ls ∧ ¬ PropFamilyS w ∧
      us_pre.length = w.preMajor.length ∧ us_fields.length = w.fields.length ∧
      ApproxTK E R n Γ (EnvT.pushArgs ((us_pre ++ us_fields).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c₀ ∧
      c = curryStepT (us_pre ++ [ctorDemandT w.ctorRef w.nparams us_fields]) c₀) ∨
    (∃ w : IotaWitnessS E, ∃ c₀, PropFamilyS w ∧ KGateAt E R n Γ w ∧
      e = foldApps (.const w.recRef w.ls) w.preMajor ∧ c = .lam [([], c₀)]) ∨
    (∃ w : IotaWitnessS E, ∃ ls us_pre c₀, PropFamilyS w ∧ w.nindices = 0 ∧ e = .const w.recRef ls ∧
      us_pre.length = w.preMajor.length ∧
      ApproxTK E R n Γ
        (EnvT.pushArgs ((us_pre ++ w.fields.map (fun _ => [])).map demandT) EnvT.bot)
        (instantiateLevels ls w.schema) c₀ ∧
      c = curryStepT (us_pre ++ [[]]) c₀) ∨
    (∃ f a r args u, e = .app f a ∧ c = .spine r (args ++ [u]) ∧
      ApproxTK E R n Γ ρ f (.spine r args) ∧ ApproxTK E R n Γ ρ a u) ∨
    (∃ A v b, e = .letE A v b ∧
      ApproxTK E R n Γ ρ (.app (.lam A b) v) c) ∨
    (∃ t, e = .lit t ∧ ApproxTK E R n Γ ρ (natExpand t) c) := by
  cases h with
  | bot =>
      exact Or.inl rfl
  | bvar hb =>
      exact Or.inr (Or.inl ⟨_, rfl, hb⟩)
  | sort =>
      exact Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))
  | pi hA hT hf =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, hA, fun s hs => ⟨hT s hs, hf s hs⟩⟩)))
  | lam hA hT hnt hb =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, hA, hnt, fun s hs => ⟨hT s hs, hb s hs⟩⟩))))
  | app hf hs ha =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, hf, hs, ha⟩)))))
  | const _ _ _ hrigid hnp =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, hrigid, hnp, rfl⟩))))))
  | delta hd h =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, rfl, hd, h⟩)))))))
  | @recursor ρ w ls hnp us_pre us_fields c₀ hpre hflds h =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨w, ls, us_pre, us_fields, c₀, rfl, hnp, hpre, hflds, h, rfl⟩))))))))
  | @recursorPropK ρ w hP us c hgate hpre hargs hinner =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨w, c, hP, hgate, rfl, rfl⟩)))))))))
  | recursorPropIdxFree ls hP hnidx hpre h =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, hP, hnidx, rfl, hpre, h, rfl⟩))))))))))
  | appSpine hf ha =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl, hf, ha⟩)))))))))))
  | letE h =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, h⟩))))))))))))
  | @lit ρ t c h =>
      have key : ∃ t' : Nat, @Expr.lit Nat t = @Expr.lit Nat t' ∧
        ApproxTK E R n Γ ρ (natExpand t') c := by
        refine ⟨t, ?_, ?_⟩
        · rfl
        · exact h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key)))))))))))))

/-- The guarded prefix is never a variable. -/
theorem recursorPropK_source_ne_bvar (w : IotaWitnessS E) (i : Nat) :
    foldApps (.const w.recRef w.ls) w.preMajor ≠ .bvar i := by
  obtain ⟨f, x, hx⟩ := foldApps_preMajor_is_app w
  rw [hx]
  exact fun h => Expr.noConfusion h

theorem approxTK_bvar_inv {ρ : EnvT} {i : Nat} {c : CptT}
    (h : ApproxTK E R n Γ ρ (.bvar i) c) : c = .bot ∨ ρ i c := by
  rcases approxTK_cases h with h0 | ⟨j, he, hj⟩ | ⟨l, he, _⟩
    | ⟨A, B, _, _, he, _, _, _⟩ | ⟨A, b, _, _, he, _, _, _⟩
    | ⟨f, a, _, _, he, _, _, _⟩ | ⟨r, ls, he, _, _, _⟩ | ⟨r, ls, _, _, he, _, _⟩
    | ⟨w, ls, _, _, _, he, _, _, _, _⟩ | ⟨w, c₀, _, _, he, _⟩
    | ⟨w, ls, _, _, _, _, he, _, _, _⟩ | ⟨f, a, _, _, _, he, _, _, _⟩
    | ⟨A, v, b, he, _⟩ | ⟨t, he, _⟩
  · exact Or.inl h0
  · obtain rfl := Expr.bvar.inj he
    exact Or.inr hj
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact (recursorPropK_source_ne_bvar w i he.symm).elim
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he

theorem approxTK_sort_inv {ρ : EnvT} {l : Level} {c : CptT}
    (h : ApproxTK E R n Γ ρ (.sort l) c) : c = .bot ∨ c = sortCode l := by
  rcases approxTK_cases h with h0 | ⟨i, he, _⟩ | ⟨l', he, hc⟩
    | ⟨A, B, _, _, he, _, _, _⟩ | ⟨A, b, _, _, he, _, _, _⟩
    | ⟨f, a, _, _, he, _, _, _⟩ | ⟨r, ls, he, _, _, _⟩ | ⟨r, ls, _, _, he, _, _⟩
    | ⟨w, ls, _, _, _, he, _, _, _, _⟩ | ⟨w, c₀, _, _, he, _⟩
    | ⟨w, ls, _, _, _, _, he, _, _, _⟩ | ⟨f, a, _, _, _, he, _, _, _⟩
    | ⟨A, v, b, he, _⟩ | ⟨t, he, _⟩
  · exact Or.inl h0
  · exact Expr.noConfusion he
  · obtain rfl := Expr.sort.inj he
    exact Or.inr hc
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · obtain ⟨f, x, hx⟩ := foldApps_preMajor_is_app w
    rw [hx] at he
    exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he

theorem approxTK_pi_inv {ρ : EnvT} {A B : Expr Nat} {c : CptT}
    (h : ApproxTK E R n Γ ρ (.pi A B) c) :
    c = .bot ∨ ∃ a f, c = .pi a f ∧ ApproxTK E R n Γ ρ A a ∧
      ∀ s ∈ f, (∀ u ∈ s.1, CTyS E u a) ∧
        ApproxTK E R n Γ (EnvT.cons (demandT s.1) ρ) B s.2 := by
  rcases approxTK_cases h with h0 | ⟨i, he, _⟩ | ⟨l, he, _⟩
    | ⟨A', B', a, f, he, hc, hA, hf⟩ | ⟨A', b, _, _, he, _, _, _⟩
    | ⟨f', a', _, _, he, _, _, _⟩ | ⟨r, ls, he, _, _, _⟩ | ⟨r, ls, _, _, he, _, _⟩
    | ⟨w, ls, _, _, _, he, _, _, _, _⟩ | ⟨w, c₀, _, _, he, _⟩
    | ⟨w, ls, _, _, _, _, he, _, _, _⟩ | ⟨f, a, _, _, _, he, _, _, _⟩
    | ⟨A', v, b, he, _⟩ | ⟨t, he, _⟩
  · exact Or.inl h0
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · obtain ⟨rfl, rfl⟩ := Expr.pi.inj he
    exact Or.inr ⟨_, _, hc, hA, hf⟩
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · obtain ⟨f, x, hx⟩ := foldApps_preMajor_is_app w
    rw [hx] at he
    exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he

theorem approxTK_lam_inv {ρ : EnvT} {A b : Expr Nat} {c : CptT}
    (h : ApproxTK E R n Γ ρ (.lam A b) c) :
    c = .bot ∨ ∃ a g, c = .lam g ∧ ApproxTK E R n Γ ρ A a ∧ (∃ s ∈ g, s.2 ≠ .bot) ∧
      ∀ s ∈ g, (∀ u ∈ s.1, CTyS E u a) ∧
        ApproxTK E R n Γ (EnvT.cons (demandT s.1) ρ) b s.2 := by
  rcases approxTK_cases h with h0 | ⟨i, he, _⟩ | ⟨l, he, _⟩
    | ⟨A', B', _, _, he, _, _, _⟩ | ⟨A', b', a, g, he, hc, hA, hnt, hb⟩
    | ⟨f', a', _, _, he, _, _, _⟩ | ⟨r, ls, he, _, _, _⟩ | ⟨r, ls, _, _, he, _, _⟩
    | ⟨w, ls, _, _, _, he, _, _, _, _⟩ | ⟨w, c₀, _, _, he, _⟩
    | ⟨w, ls, _, _, _, _, he, _, _, _⟩ | ⟨f, a, _, _, _, he, _, _, _⟩
    | ⟨A', v, b', he, _⟩ | ⟨t, he, _⟩
  · exact Or.inl h0
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · obtain ⟨rfl, rfl⟩ := Expr.lam.inj he
    exact Or.inr ⟨_, _, hc, hA, hnt, hb⟩
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · obtain ⟨f, x, hx⟩ := foldApps_preMajor_is_app w
    rw [hx] at he
    exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he

/-- The `app` inversion of the guarded model: the old three cases of `ApproxT`
plus the guarded prefix itself, which is application-headed and carries the
remaining major step as its compact. -/
theorem approxTK_app_inv {ρ : EnvT} {f a : Expr Nat} {c : CptT}
    (h : ApproxTK E R n Γ ρ (.app f a) c) :
    c = .bot ∨
    (∃ g s, c = s.2 ∧ ApproxTK E R n Γ ρ f (.lam g) ∧ s ∈ g ∧
      ∀ u ∈ s.1, ApproxTK E R n Γ ρ a u) ∨
    (∃ r args u, c = .spine r (args ++ [u]) ∧ ApproxTK E R n Γ ρ f (.spine r args) ∧
      ApproxTK E R n Γ ρ a u) ∨
    (∃ (w : IotaWitnessS E) (c₀ : CptT), PropFamilyS w ∧ KGateAt E R n Γ w ∧
      .app f a = foldApps (.const w.recRef w.ls) w.preMajor ∧ c = .lam [([], c₀)]) := by
  rcases approxTK_cases h with h0 | ⟨i, he, _⟩ | ⟨l, he, _⟩
    | ⟨A, B, _, _, he, _, _, _⟩ | ⟨A, b, _, _, he, _, _, _⟩
    | ⟨f', a', g, s, he, hc, hf', hs, ha⟩ | ⟨r, ls, he, _, _, _⟩
    | ⟨r, ls, _, _, he, _, _⟩ | ⟨w, ls, _, _, _, he, _, _, _, _⟩
    | ⟨w, c₀, hP, hgate, he, hc⟩
    | ⟨w, ls, _, _, _, _, he, _, _, _⟩ | ⟨f', a', r, args, u, he, hc, hf', ha⟩
    | ⟨A, v, b, he, _⟩ | ⟨t, he, _⟩
  · exact Or.inl h0
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · obtain ⟨rfl, rfl⟩ := Expr.app.inj he
    exact Or.inr (Or.inl ⟨_, _, hc, hf', hs, ha⟩)
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Or.inr (Or.inr (Or.inr ⟨w, c₀, hP, hgate, he, hc⟩))
  · exact Expr.noConfusion he
  · obtain ⟨rfl, rfl⟩ := Expr.app.inj he
    exact Or.inr (Or.inr (Or.inl ⟨_, _, _, hc, hf', ha⟩))
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he

theorem approxTK_letE_inv {ρ : EnvT} {A v b : Expr Nat} {c : CptT}
    (h : ApproxTK E R n Γ ρ (.letE A v b) c) :
    ApproxTK E R n Γ ρ (.app (.lam A b) v) c := by
  rcases approxTK_cases h with h0 | ⟨i, he, _⟩ | ⟨l, he, _⟩
    | ⟨A', B', _, _, he, _, _, _⟩ | ⟨A', b', _, _, he, _, _, _⟩
    | ⟨f, a, _, _, he, _, _, _⟩ | ⟨r, ls, he, _, _, _⟩ | ⟨r, ls, _, _, he, _, _⟩
    | ⟨w, ls, _, _, _, he, _, _, _, _⟩ | ⟨w, c₀, _, _, he, _⟩
    | ⟨w, ls, _, _, _, _, he, _, _, _⟩ | ⟨f, a, _, _, _, he, _, _, _⟩
    | ⟨A', v', b', he, h⟩ | ⟨t, he, _⟩
  · exact h0 ▸ .bot ρ _
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · obtain ⟨f, x, hx⟩ := foldApps_preMajor_is_app w
    rw [hx] at he
    exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · exact Expr.noConfusion he
  · obtain ⟨rfl, rfl, rfl⟩ := Expr.letE.inj he
    exact h
  · exact Expr.noConfusion he

theorem approxTK_sort_code (E : ResolvedEnv) (R : Readback) (n : Nat) (Γ : LCtx)
    (ρ : EnvT) (l : Level) : ApproxTK E R n Γ ρ (.sort l) (sortCode l) :=
  .sort ρ l

theorem approxTK_bot (E : ResolvedEnv) (R : Readback) (n : Nat) (Γ : LCtx)
    (ρ : EnvT) (e : Expr Nat) : ApproxTK E R n Γ ρ e .bot :=
  .bot ρ e

/-! ## §4 — the transport into the landed model -/

/-- Peeling a curried step function across an argument prefix, leaving the
curried rest.  The landed `foldAppCptT_curryStepT_iff` is the total-consumption
shape; this is the append form its own proof pattern induces. -/
theorem foldAppCptT_curryStepT_app {E : ResolvedEnv} {ρ : EnvT}
    {xs : List (Expr Nat)} {us rest : List (List CptT)} {c₀ : CptT}
    (hargs : ApproxArgsDemandT E ρ xs us) :
    FoldAppCptT E ρ (curryStepT (us ++ rest) c₀) xs (curryStepT rest c₀) := by
  induction xs generalizing us with
  | nil =>
      cases us with
      | nil => exact .nil _
      | cons _ _ => exact absurd hargs (fun h => by cases h)
  | cons x xss ih =>
      cases us with
      | nil => exact absurd hargs (fun h => by cases h)
      | cons u uss =>
          cases hargs with
          | cons ha hass =>
              simp only [List.cons_append, curryStepT]
              exact .cons (.app (List.mem_singleton.mpr rfl) ha) (ih hass)

/-- Every `ApproxTK` observation is an `ApproxT` observation: the guarded model
is a conservative refinement of the landed one.  The `recursorPropK` case
reproduces the old compositional clause from the same demand realisation, so the
transport needs no gate. -/
theorem approxTK_to_approxT {ρ : EnvT} {e : Expr Nat} {c : CptT}
    (h : ApproxTK E R n Γ ρ e c) : ApproxT E ρ e c := by
  induction h with
  | bot => exact .bot _ _
  | bvar hb => exact .bvar hb
  | sort => exact .sort _ _
  | pi _ hT _ ihA ihf => exact .pi ihA hT ihf
  | lam _ hT hnt _ ihA ihb => exact .lam ihA hT hnt ihb
  | app _ hs _ ihf iha => exact .app ihf hs iha
  | const _ _ _ hrigid hnp => exact .const _ _ _ hrigid hnp
  | delta hd _ ih => exact .delta hd ih
  | recursor ls hnp hpre hflds h ih => exact .recursor ls hnp hpre hflds ih
  | @recursorPropK ρ w hP us c hgate hpre hargs hinner ih =>
      refine (approxT_foldApps_iff E ρ (.const w.recRef w.ls) w.preMajor _).mpr
        ⟨curryStepT (us ++ [[]]) c, .recursorProp w.ls hP hpre ih, ?_⟩
      exact foldAppCptT_curryStepT_app (us := us) (xs := w.preMajor)
        (rest := [[]]) (c₀ := c) hargs
  | recursorPropIdxFree ls hP hnidx hpre h ih => exact .recursorProp ls hP hpre ih
  | appSpine _ _ ihf iha => exact .appSpine ihf iha
  | letE _ ih => exact .letE ih
  | lit _ ih => exact .lit ih

/-! ## §5 — the K-free fragment -/

/-- Syntactic fragment predicate: the term mentions no recursor constant at
all.  On this fragment the guarded model and the landed model coincide, given
that the environment's transparent bodies and literal expansions stay in the
fragment too; the disagreement is exactly the gated K prefixes, the recursor
constants, and the recursor/schema readings. -/
def PropRecAppFree (E : ResolvedEnv) : Expr Nat → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const r _ => ¬ ∃ w : IotaWitnessS E, w.recRef = r
  | .app f a => PropRecAppFree E f ∧ PropRecAppFree E a
  | .lam A b => PropRecAppFree E A ∧ PropRecAppFree E b
  | .pi A B => PropRecAppFree E A ∧ PropRecAppFree E B
  | .letE A v b => PropRecAppFree E A ∧ PropRecAppFree E v ∧ PropRecAppFree E b
  | .lit _ => True

/-- A literal's expansion is fragment whenever neither literal head constant is
a recursor of the environment. -/
theorem propRecAppFree_natExpand (h1 : ¬ ∃ w : IotaWitnessS E, w.recRef = 1)
    (h2 : ¬ ∃ w : IotaWitnessS E, w.recRef = 2) :
    ∀ t : Nat, PropRecAppFree E (natExpand t) := by
  intro t
  induction t with
  | zero => exact h1
  | succ n ih => exact ⟨h2, ih⟩

/-- On the K-free fragment the landed model's observations all lift into the
guarded model, provided the environment's transparent bodies and literal
expansions stay in the fragment: the only clauses that differ are unreachable
there. -/
theorem approxTK_of_approxT
    (hδ : ∀ (r : Nat) (ls : List Level) (m : CheckedMember) (b : Expr Nat),
      DeltaConst E r m b → PropRecAppFree E (instantiateLevels ls b))
    (hlit : ∀ t : Nat, PropRecAppFree E (natExpand t)) :
    ∀ {ρ : EnvT} {e : Expr Nat} {c : CptT},
    ApproxT E ρ e c → PropRecAppFree E e → ApproxTK E R n Γ ρ e c := by
  intro ρ e c h
  induction h with
  | bot => intro _; exact .bot _ _
  | bvar hb => intro _; exact .bvar hb
  | sort => intro _; exact .sort _ _
  | @pi ρ A B a f hA hT hf ihA ihf =>
      intro hfree
      rcases hfree with ⟨hfA, hfB⟩
      exact .pi (ihA hfA) hT (fun s hs => ihf s hs hfB)
  | @lam ρ A b a g hA hT hnt hb ihA ihb =>
      intro hfree
      rcases hfree with ⟨hfA, hfb⟩
      exact .lam (ihA hfA) hT hnt (fun s hs => ihb s hs hfb)
  | @app ρ f a g s hf hs ha ihf iha =>
      intro hfree
      rcases hfree with ⟨hff, hfa⟩
      exact .app (ihf hff) hs (fun u hu => iha u hu hfa)
  | const _ _ _ hrigid hnp => intro _; exact .const _ _ _ hrigid hnp
  | delta hd h ih =>
      intro hfree
      exact .delta hd (ih (hδ _ _ _ _ hd))
  | recursor ls hnp hpre hflds h ih =>
      intro hfree
      exact absurd ⟨_, rfl⟩ hfree
  | @recursorProp ρ w ls us_pre c hP hpre h ih =>
      intro hfree
      exact absurd ⟨w, rfl⟩ hfree
  | appSpine _ _ ihf iha =>
      intro hfree
      rcases hfree with ⟨hff, hfa⟩
      exact .appSpine (ihf hff) (iha hfa)
  | letE _ ih =>
      intro hfree
      exact .letE (ih ⟨⟨hfree.1, hfree.2.2⟩, hfree.2.1⟩)
  | lit _ ih => intro _; exact .lit (ih (hlit _))

/-- The guarded model as a `CtxModelT` at a fixed readback, level bound and
context. -/
def ctxModelTApproxTK (E : ResolvedEnv) (R : Readback) (n : Nat) (Γ : LCtx) :
    CtxModelT E := ⟨ApproxTK E R n Γ⟩

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_ROOTS
#print axioms KIdxAgree
#print axioms KIdxAgree.red
#print axioms KIdxAgree.deltaL
#print axioms KIdxAgree.deltaR
#print axioms KIdxAgree.etaL
#print axioms KIdxAgree.etaR
#print axioms kIdxAgree_refl
#print axioms lift01_ne_bvar0
#print axioms KIdxJoinListAt
#print axioms KGateAt
#print axioms ApproxTK
#print axioms ApproxTK.bot
#print axioms ApproxTK.bvar
#print axioms ApproxTK.sort
#print axioms ApproxTK.pi
#print axioms ApproxTK.lam
#print axioms ApproxTK.app
#print axioms ApproxTK.const
#print axioms ApproxTK.delta
#print axioms ApproxTK.recursor
#print axioms ApproxTK.recursorPropK
#print axioms ApproxTK.recursorPropIdxFree
#print axioms ApproxTK.appSpine
#print axioms ApproxTK.letE
#print axioms ApproxTK.lit
#print axioms iotaWitnessS_preMajor_ne_nil
#print axioms foldApps_preMajor_is_app
#print axioms approxTK_cases
#print axioms recursorPropK_source_ne_bvar
#print axioms approxTK_bvar_inv
#print axioms approxTK_sort_inv
#print axioms approxTK_pi_inv
#print axioms approxTK_lam_inv
#print axioms approxTK_app_inv
#print axioms approxTK_letE_inv
#print axioms approxTK_sort_code
#print axioms approxTK_bot
#print axioms foldAppCptT_curryStepT_app
#print axioms approxTK_to_approxT
#print axioms PropRecAppFree
#print axioms propRecAppFree_natExpand
#print axioms approxTK_of_approxT
#print axioms ctxModelTApproxTK
-- END RCIC_NATIVE_TYPED_MODEL_K_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKAudit.KG
