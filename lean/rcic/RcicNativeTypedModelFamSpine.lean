import rcic.RcicNativeTypedModelFund

/-!
# RcicNativeTypedModelFamSpine — W-FAMSPINE measured: the derivation-domain restatement

The ruling after segment 7 asked whether comparing a family spine's arguments at the
DERIVATION's own domains (what `recCall_typed_data` gives without Π-injectivity) (a) closes the
`app` case at a family spine, (b) removes the `ConvArgsSymmS`/`ConvArgsTransS` premises of
`typedPERS`, and (c) keeps the `famAppRow` read-off provable from `PiRowField`.

**Result: (a) yes, (b) symmetry yes, transitivity no — it needs type uniqueness; and at the
declared telescope the situation is the mirror image.**  Kernel-checked here:

* `ConvArgsD Γ xs xs' doms` — pairwise convertible at common domains at which both are typed.
  `convArgsD_symm` is a swap (no premise).  `convArgsD_of_spine` extracts it from a typed
  application spine and pointwise conversions at the node domains (the `app` case's instrument:
  (a) holds for the clause so stated).
* `convArgsD_trans_of_tyUniq`: transitivity follows from type uniqueness `TyUniqT` — and only
  from it: the shared middle spine is typed at two independent domain lists, and `ConvT.trans`
  needs one type.  `TyUniqT` is a row-strength statement (not on main), so (b) fails for
  transitivity.
* At the declared telescope (the current clause, `ConvArgsT (instantiateLevels ls m.mtype)`),
  the premises of `typedPERS` need the alignment of `d_i[ls][x<i]` with `d_i[ls'][x'<i]`, which is
  **congruence** — level instantiation (`LevelCongrT`, stated here; `hasTyT_instLevels` /
  `convT_instLevels` are the one-instantiation template) plus substitution
  (`convT_substT_pointwise`, landed in segment 7) — not Π-injectivity.  That is the decoupling
  for the `ConvArgsT` owner: `convArgsSymmT_of_levelCongr`'s shape is given in the PR.  (a) fails
  there, as measured in segment 7.

**§4 — what breaks the class: strong induction on the derivation (ruling (b)).**  The alignment
of a head's node domain with its declared domain is a chain of `conv` nodes INSIDE the head's
typing derivation (`convChainBelow_const`: every link is a sub-derivation, `sizeOf`-smaller), and
the fundamental lemma's conversion conjunct at the probe `pi ⊥ []`, applied to those links, reads
the alignment off (`lrSCoreS_pi_components`, `domAlign_of_chain`).  So the Π-injectivity
instances W-FAMSPINE and NodeDeclAlign need are at strictly smaller derivations than the one
being proved, and a fundamental lemma by strong induction on `sizeOf` of the derivation pays
them with its own conversion conjunct — given the readback laws, unique normal forms, and
backward compact transport along readback steps (`ReadbackModelInv`'s direction the route already
needs).  Ruling (a) separately: the Π row's read-off consumes no soundness of any readback step
as a conversion (`ReadbackLaws` has no such field; `lrSCoreS_expand` is pure readback; the `iota`
case's typings are premises of `ConvT.iota`), so NodeDeclAlign is not on the Π row's path at all
and can be discharged from `PiRowField` afterwards.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit

/-! ### §1 — the derivation-domain pairwise conversion -/

/-- Pairwise convertible at common domains at which both sides are typed. -/
def ConvArgsD (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    List (Expr Nat) → List (Expr Nat) → List (Expr Nat) → Prop
  | [], [], [] => True
  | x :: xs, x' :: xs', A :: As =>
      Nonempty (HasTyT E n Γ x A) ∧ Nonempty (HasTyT E n Γ x' A) ∧ Nonempty (ConvT E n Γ x x' A) ∧
      ConvArgsD E n Γ xs xs' As
  | _, _, _ => False

/-- **Symmetry is a swap** — no premise. -/
theorem convArgsD_symm {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    ∀ {xs xs' doms : List (Expr Nat)}, ConvArgsD E n Γ xs xs' doms → ConvArgsD E n Γ xs' xs doms
  | [], [], [], _ => trivial
  | x :: xs, x' :: xs', A :: As, ⟨hx, hx', ⟨hc⟩, hrest⟩ =>
      ⟨hx', hx, ⟨.symm _ _ _ _ hc⟩, convArgsD_symm hrest⟩
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

theorem convArgsD_append {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    ∀ {xs xs' doms : List (Expr Nat)}, ConvArgsD E n Γ xs xs' doms →
      ∀ {y y' A : Expr Nat}, Nonempty (HasTyT E n Γ y A) → Nonempty (HasTyT E n Γ y' A) →
      Nonempty (ConvT E n Γ y y' A) →
      ConvArgsD E n Γ (xs ++ [y]) (xs' ++ [y']) (doms ++ [A])
  | [], [], [], _, _, _, _, hy, hy', hc => ⟨hy, hy', hc, trivial⟩
  | x :: xs, x' :: xs', A₀ :: As, ⟨hx, hx', hcx, hrest⟩, _, _, _, hy, hy', hc =>
      ⟨hx, hx', hcx, convArgsD_append hrest hy hy' hc⟩
  | [], [], _ :: _, h, _, _, _, _, _, _ => h.elim
  | [], _ :: _, _, h, _, _, _, _, _, _ => h.elim
  | _ :: _, [], _, h, _, _, _, _, _, _ => h.elim
  | _ :: _, _ :: _, [], h, _, _, _, _, _, _ => h.elim

/-- **(a) at the clause so stated**: a typed application spine whose arguments are pairwise
    convertible at the node domains yields `ConvArgsD` — from `recSpineTypedAt_of_hasTyT`, no
    Π-injectivity.  (`hconv` is what the fundamental lemma's `app` case has for each argument
    from the pointwise substitution conversion.) -/
theorem convArgsD_of_spine {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    ∀ {xs xs' doms : List (Expr Nat)}, RecSpineTypedAt E n Γ xs doms →
      doms.length = xs.length → xs'.length = xs.length →
      (∀ i (hi : i < xs.length) (hi' : i < xs'.length) (hd : i < doms.length),
        Nonempty (HasTyT E n Γ (xs'.get ⟨i, hi'⟩) (doms.get ⟨i, hd⟩)) ∧
        Nonempty (ConvT E n Γ (xs.get ⟨i, hi⟩) (xs'.get ⟨i, hi'⟩) (doms.get ⟨i, hd⟩))) →
      ConvArgsD E n Γ xs xs' doms
  | [], [], [], _, _, _, _ => trivial
  | x :: xs, x' :: xs', A :: As, ⟨hx, hrest⟩, hl, hl', hconv => by
      obtain ⟨hx', hc⟩ := hconv 0 (Nat.succ_pos _) (Nat.succ_pos _) (Nat.succ_pos _)
      refine ⟨hx, hx', hc, convArgsD_of_spine hrest (Nat.succ.inj hl) (Nat.succ.inj hl') ?_⟩
      intro i hi hi' hd
      exact hconv (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hi') (Nat.succ_lt_succ hd)
  | [], [], _ :: _, _, hl, _, _ => Nat.noConfusion hl
  | [], _ :: _, _, _, _, hl', _ => Nat.noConfusion hl'
  | _ :: _, [], _, _, _, hl', _ => Nat.noConfusion hl'
  | _ :: _, _ :: _, [], _, hl, _, _ => Nat.noConfusion hl

/-! ### §2 — transitivity needs type uniqueness -/

/-- Type uniqueness up to conversion (a row-strength statement, not on main). -/
def TyUniqT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {x A A' : Expr Nat}, HasTyT E n Γ x A → HasTyT E n Γ x A' →
    ∃ w, Nonempty (ConvT E n Γ A A' (.sort w))

/-- **Transitivity of `ConvArgsD` from type uniqueness**: the shared middle spine is typed at both
    domain lists; uniqueness aligns them, then `ConvT.trans` applies at the left domains. -/
theorem convArgsD_trans_of_tyUniq {E : ResolvedEnv} {n : Nat} (hU : TyUniqT E n) {Γ : LCtx} :
    ∀ {xs xs' xs'' doms doms' : List (Expr Nat)},
      ConvArgsD E n Γ xs xs' doms → ConvArgsD E n Γ xs' xs'' doms' → ConvArgsD E n Γ xs xs'' doms
  | [], [], [], [], [], _, _ => trivial
  | x :: xs, x' :: xs', x'' :: xs'', A :: As, A' :: As', ⟨hx, ⟨hx'⟩, ⟨hc⟩, hrest⟩,
      ⟨⟨hx'₂⟩, ⟨hx''⟩, ⟨hc'⟩, hrest'⟩ => by
      obtain ⟨w, ⟨hAA'⟩⟩ := hU hx' hx'₂
      refine ⟨hx, ⟨.conv _ _ _ _ w hx'' (.symm _ _ _ _ hAA')⟩,
        ⟨.trans _ _ _ _ _ hc (.tyConv _ _ _ _ _ w hc' (.symm _ _ _ _ hAA'))⟩,
        convArgsD_trans_of_tyUniq hU hrest hrest'⟩
  | [], [], [], [], _ :: _, _, h => h.elim
  | [], [], [], _ :: _, _, h, _ => h.elim
  | [], [], _ :: _, _, _, _, h => by
      cases ‹List (Expr Nat)› <;> simp [ConvArgsD] at h
  | [], _ :: _, _, _, _, h, _ => by
      cases ‹List (Expr Nat)› <;> simp [ConvArgsD] at h
  | _ :: _, [], _, _, _, h, _ => by
      cases ‹List (Expr Nat)› <;> simp [ConvArgsD] at h
  | _ :: _, _ :: _, [], _, _, _, h => by
      cases ‹List (Expr Nat)› <;> simp [ConvArgsD] at h
  | _ :: _, _ :: _, _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, h => h.elim

/-! ### §3 — the declared-telescope premises are congruence, not Π-injectivity -/

/-- Level-instantiation congruence of conversion (not on main; the one-instantiation
    `convT_instLevels` is its template).  This is what `ConvArgsSymmS`/`ConvArgsTransS` need
    at the declared telescope, together with `convT_substT_pointwise`. -/
def LevelCongrT (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {a : Nat} {ls ls' : List Level}, levelsBounded n ls = true → levelsBounded n ls' = true →
    ls.length = a → ls'.length = a → eqNList ls ls' →
    ∀ {Γ : LCtx} {T : Expr Nat} {u : Level}, HasTyT E a Γ T (.sort u) →
      Nonempty (ConvT E n (instLvlsCtx ls Γ) (instantiateLevels ls T) (instantiateLevels ls' T)
        (.sort (instLevel ls u)))

/-- The one-level instance: a sort's two instantiations are convertible by `ConvT.sorts`. -/
theorem levelCongr_sort_instance (E : ResolvedEnv) (n : Nat) (Γ : LCtx) {ls ls' : List Level}
    (h : eqNList ls ls') (l : Level) (hl : eqN (instLevel ls l) (instLevel ls' l)) :
    Nonempty (ConvT E n Γ (.sort (instLevel ls l)) (.sort (instLevel ls' l))
      (.sort (.succ (instLevel ls l)))) :=
  ⟨.sorts Γ _ _ hl⟩

/-! ### §4 — (b): the alignment is a chain of smaller conversions, paid by the fundamental lemma -/

/-- A chain of conversions at sorts, each a derivation of `sizeOf` below `h`. -/
inductive ConvChainBelow (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (h : Nat) : Expr Nat → Expr Nat → Prop
  | refl (X : Expr Nat) : ConvChainBelow E n Γ h X X
  | step {X Y Z : Expr Nat} {u : Level} (hc : ConvT E n Γ X Y (.sort u)) (hlt : sizeOf hc < h)
      (rest : ConvChainBelow E n Γ h Y Z) : ConvChainBelow E n Γ h X Z

theorem ConvChainBelow.mono {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {h h' : Nat} (hh : h ≤ h')
    {X Y : Expr Nat} : ConvChainBelow E n Γ h X Y → ConvChainBelow E n Γ h' X Y := by
  intro hch
  induction hch with
  | refl X => exact .refl X
  | step hc hlt rest ih => exact .step hc (Nat.lt_of_lt_of_le hlt hh) ih

/-- **The node type of a constant head is its declared type through a chain of `conv` nodes of
    the derivation itself** — each link strictly smaller than the derivation. -/
theorem convChainBelow_const {E : ResolvedEnv} {n : Nat} :
    ∀ {Γ : LCtx} {r : Nat} {ls : List Level} {T : Expr Nat} (d : HasTyT E n Γ (.const r ls) T),
      ∃ m : CheckedMember, E.members r = some m ∧
        ConvChainBelow E n Γ (sizeOf d) (instantiateLevels ls m.mtype) T
  | _, _, _, _, .const Γ r ls m hres hlen hwf => ⟨m, hres, .refl _⟩
  | _, _, _, _, .conv Γ (.const r ls) A B u h hc => by
      have chainAppend : ∀ {h' : Nat} {X Y Z : Expr Nat},
          ConvChainBelow E n Γ h' X Y → ConvChainBelow E n Γ h' Y Z →
            ConvChainBelow E n Γ h' X Z := by
        intro h' X Y Z c₁
        induction c₁ with
        | refl X => exact fun c₂ => c₂
        | step hc hlt rest ih => exact fun c₂ => .step hc hlt (ih c₂)
      obtain ⟨m, hm, chain⟩ := convChainBelow_const h
      refine ⟨m, hm, ?_⟩
      have hlt₁ : sizeOf h < sizeOf (HasTyT.conv Γ (.const r ls) A B u h hc) := by simp; omega
      have hlt₂ : sizeOf hc < sizeOf (HasTyT.conv Γ (.const r ls) A B u h hc) := by simp; omega
      exact chainAppend (chain.mono (Nat.le_of_lt hlt₁)) (.step hc hlt₂ (.refl _))

/-- The probe read-off over `CptT`: at `pi ⊥ []` the relation of two Π-types gives the domain and
    codomain conversions. -/
theorem lrSCoreS_pi_components {R : Readback} {E : ResolvedEnv} {n : Nat} (hL : ReadbackLaws E R)
    {Γ : LCtx} {A₁ B₁ A₂ B₂ : Expr Nat} {u : Level}
    (h : LRSCoreS R E n Γ (.pi A₁ B₁) (.pi A₂ B₂) (.sort u) (.pi .bot [])) :
    Nonempty (TyConvT E n Γ A₁ A₂) ∧ Nonempty (TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) := by
  rw [LRSCoreS.eq_def] at h
  obtain ⟨_, A₁', B₁', A₂', B₂', h1, h2, _, hdom, hcod, _, _⟩ := h
  have e₁ := redR_pi_eq hL h1
  have e₂ := redR_pi_eq hL h2
  injection e₁ with eA₁ eB₁
  injection e₂ with eA₂ eB₂
  subst eA₁; subst eB₁; subst eA₂; subst eB₂
  exact ⟨hdom, hcod⟩

/-- The probe's readbacks: at `pi ⊥ []` both sides read back to Π-types with convertible domains. -/
theorem lrSCoreS_pi_probe {R : Readback} {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {X Y : Expr Nat}
    {u : Level} (h : LRSCoreS R E n Γ X Y (.sort u) (.pi .bot [])) :
    ∃ X₁ X₂ Y₁ Y₂, RedR R Γ X (.pi X₁ X₂) ∧ RedR R Γ Y (.pi Y₁ Y₂) ∧ Nonempty (TyConvT E n Γ X₁ Y₁) := by
  rw [LRSCoreS.eq_def] at h
  obtain ⟨_, X₁, X₂, Y₁, Y₂, h1, h2, _, hdom, _⟩ := h
  exact ⟨X₁, X₂, Y₁, Y₂, h1, h2, hdom⟩

/-- Backward compact transport along a readback sequence. -/
theorem approxT_of_redR {R : Readback} {E : ResolvedEnv} {ρ : EnvT} {Γ : LCtx}
    (hinv : ∀ {a b : Expr Nat} {c : CptT}, R Γ a b → ApproxT E ρ b c → ApproxT E ρ a c)
    {a b : Expr Nat} (hr : RedR R Γ a b) {c : CptT} (h : ApproxT E ρ b c) : ApproxT E ρ a c := by
  induction hr with
  | refl => exact h
  | step hs _ ih => exact hinv hs (ih h)

/-- **(b), the payoff**: given the fundamental lemma's conversion conjunct (identity-substitution
    form, at one environment) for every conversion of `sizeOf` below `h`, a `ConvChainBelow h`
    from a Π-type aligns the domains: the start's domain is convertible to the domain of the end's
    Π readback.  Hypotheses: the readback laws, unique normal forms, and backward compact transport
    along readback steps. -/
theorem domAlign_of_chain {R : Readback} {E : ResolvedEnv} {n : Nat} (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) {Γ : LCtx} {ρ : EnvT} {h : Nat}
    (hF : ∀ {X Y : Expr Nat} {u : Level} (hc : ConvT E n Γ X Y (.sort u)), sizeOf hc < h →
      ∀ c, ApproxT E ρ X c ∨ ApproxT E ρ Y c → LRSCoreS R E n Γ X Y (.sort u) c)
    (hinv : ∀ {a b : Expr Nat} {c : CptT}, R Γ a b → ApproxT E ρ b c → ApproxT E ρ a c) :
    ∀ {X Y : Expr Nat}, ConvChainBelow E n Γ h X Y →
      ∀ {X₁ X₂ : Expr Nat}, RedR R Γ X (.pi X₁ X₂) → ApproxT E ρ X (.pi .bot []) →
      ∀ {Y₁ Y₂ : Expr Nat}, RedR R Γ Y (.pi Y₁ Y₂) → Nonempty (TyConvT E n Γ X₁ Y₁) := by
  intro X Y hch
  induction hch with
  | refl X =>
      intro X₁ X₂ hX _ Y₁ Y₂ hY
      obtain ⟨eA, _⟩ := redR_pi_unique hL hNU hX hY
      subst eA
      exact ⟨.refl _ _⟩
  | step hc hlt rest ih =>
      intro X₁ X₂ hX hmem Y₁ Y₂ hY
      have hrel := hF hc hlt (.pi .bot []) (Or.inl hmem)
      obtain ⟨A₁, A₂, B₁, B₂, hXr, hMr, ⟨hd⟩⟩ := lrSCoreS_pi_probe hrel
      obtain ⟨eA, _⟩ := redR_pi_unique hL hNU hX hXr
      subst eA
      have hmem' : ApproxT E ρ _ (.pi .bot []) :=
        approxT_of_redR hinv hMr (approxT_pi_bot_nil E ρ B₁ B₂)
      obtain ⟨hrest⟩ := ih hMr hmem' hY
      exact ⟨.trans _ _ _ _ hd hrest⟩

/-- **The alignment of a constant head's first node domain with its declared first domain**, from
    the fundamental lemma below the head's derivation: the Π-injectivity instance W-FAMSPINE and
    NodeDeclAlign need, at a strictly smaller measure. -/
theorem nodeDeclAlign_const_of_fundBelow {R : Readback} {E : ResolvedEnv} {n : Nat}
    (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) {Γ : LCtx} {ρ : EnvT} {r : Nat} {ls : List Level}
    {A B : Expr Nat} (d : HasTyT E n Γ (.const r ls) (.pi A B))
    (hF : ∀ {X Y : Expr Nat} {u : Level} (hc : ConvT E n Γ X Y (.sort u)), sizeOf hc < sizeOf d →
      ∀ c, ApproxT E ρ X c ∨ ApproxT E ρ Y c → LRSCoreS R E n Γ X Y (.sort u) c)
    (hinv : ∀ {a b : Expr Nat} {c : CptT}, R Γ a b → ApproxT E ρ b c → ApproxT E ρ a c)
    {m : CheckedMember} {dA dB : Expr Nat} (hm : E.members r = some m)
    (hdecl : instantiateLevels ls m.mtype = .pi dA dB) :
    Nonempty (TyConvT E n Γ dA A) := by
  obtain ⟨m', hm', chain⟩ := convChainBelow_const d
  rw [hm] at hm'
  injection hm' with hm'
  subst hm'
  rw [hdecl] at chain
  exact domAlign_of_chain hL hNU hF hinv chain (.refl _) (approxT_pi_bot_nil E ρ dA dB) (.refl _)

#print axioms ConvArgsD
#print axioms convArgsD_symm
#print axioms convArgsD_append
#print axioms convArgsD_of_spine
#print axioms TyUniqT
#print axioms convArgsD_trans_of_tyUniq
#print axioms LevelCongrT
#print axioms levelCongr_sort_instance
#print axioms ConvChainBelow
#print axioms ConvChainBelow.mono
#print axioms convChainBelow_const
#print axioms lrSCoreS_pi_components
#print axioms lrSCoreS_pi_probe
#print axioms approxT_of_redR
#print axioms domAlign_of_chain
#print axioms nodeDeclAlign_const_of_fundBelow

end Rcic.Declarative.NativeValleys.TypedModelAudit
