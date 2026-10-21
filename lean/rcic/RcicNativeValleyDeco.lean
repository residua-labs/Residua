import rcic.RcicNativeValleyFronts
import rcic.RcicTypedSubstLet

/-!
# RcicNativeValleyDeco — the `retype` wall on decoration-sharing pairs
(Wall 1, `NativeConvValleys`; ITEM 8 of the fable-let lane, `NATIVE_VALLEYS_STATUS.md` §9)

`OpenRows.retype` (`Retype`, `RcicNativeValleyFronts`) is Siles–Herbelin's *Type Exchange*
(LICS 2010, Lemma III.6: `Γ ⊢ M ▷ N : A` and `Γ ⊢ M ▷ P : B` give `Γ ⊢ M ▷ N : B`), which is
"by induction, no difficult cases" in their system ONLY because every application there is
annotated with its codomain, `M (x)B N`; Adams's TPOSR annotates likewise and studies the
necessity of the annotation. In the unannotated `Expr Nat`, the annotation is not in the
term: it is in the typing derivation — the codomain `B` chosen at every `HasTyT.app` node
and the sorts `u v` chosen at every `HasTyT.pi` node. This module makes that choice an
explicit object, the **decoration** `Deco e` of a term, extracts it from a derivation
(`decoOf`), and proves the annotated system's lemma in its exact form:

* `uniqD` — **decorated uniqueness**: two typings of one term with the same decoration have
  convertible types. The recursion is on the two derivations; `conv` layers are peeled,
  `app` nodes compare their indices SYNTACTICALLY (`instantiate0 a B` with the shared `B`,
  whatever the two domains), `pi` nodes their shared sorts, `lam` / `letE` / `lit` nodes
  recurse on the body. No Π-injectivity, no sort front, no leaf front enters: the whole of
  §2b's "same-term type uniqueness" is absorbed by the hypothesis that the decorations agree.
* `retypeD` / `exchangeD` — `retype` on decoration-sharing pairs (and Lemma III.6 itself):
  decorated uniqueness followed by `CStep.reindex`.
* `retype_of_uniq` — the other reduction, `Retype` from DT-012's shape `Uniq`.

What this does NOT give: two typings of a term produced by two DIFFERENT derivations (the
two app nodes out of one `app f a` at `ConvT.trans`) need not share the decoration; relating
two decorations of one term ("decoration transfer") is exactly where Π-injectivity is
needed, and in the annotated literature it is proved AFTER the annotated Church–Rosser
theorem. §9 of the status document lays out that route (the decorated same-index diamond)
and the measure question.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-! ### decorations -/

/-- The decoration of a term: the codomain chosen at every application node, the sorts
    chosen at every Π / λ / let node, recursively through all children and literal
    expansions — exactly the data of a typing derivation that the term's syntax does not fix
    (TPOSR's `M (x)B N` annotation, plus the sorts a functional specification would
    determine). `uniqD` reads only the root's `B` / sorts and the binder bodies; the children
    are carried so that two steps sharing the decoration of `app f a` share the decorations
    of `f` and `a` (the invariant of the decorated diamond, status §9c). -/
inductive Deco : Expr Nat → Type
  | sort (l : Level) : Deco (.sort l)
  | bvar (i : Nat) : Deco (.bvar i)
  | const (r : Nat) (ls : List Level) : Deco (.const r ls)
  | pi (A B : Expr Nat) (u v : Level) (dA : Deco A) (dB : Deco B) : Deco (.pi A B)
  | lam (A body : Expr Nat) (u : Level) (dA : Deco A) (db : Deco body) : Deco (.lam A body)
  | app (f a B : Expr Nat) (df : Deco f) (da : Deco a) : Deco (.app f a)
  | letE (A value body : Expr Nat) (u : Level) (dA : Deco A) (dv : Deco value) (db : Deco body) :
      Deco (.letE A value body)
  | lit (t : Nat) (d : Deco (natExpand t)) : Deco (.lit t)

/-- The decoration a typing derivation chose (`conv` layers choose nothing). -/
def decoOf : {Γ : LCtx} → {e T : Expr Nat} → HasTyT E n Γ e T → Deco e
  | _, _, _, .sort _ l => .sort l
  | _, _, _, .bvar _ i _ _ => .bvar i
  | _, _, _, .const _ r ls _ _ _ _ => .const r ls
  | _, _, _, .pi _ A u B v hA hB => .pi A B u v (decoOf hA) (decoOf hB)
  | _, _, _, .lam _ A u body _ hA hbody => .lam A body u (decoOf hA) (decoOf hbody)
  | _, _, _, .app _ f a _ B hf ha => .app f a B (decoOf hf) (decoOf ha)
  | _, _, _, .letE _ A u value _ body hA hv hb =>
      .letE A value body u (decoOf hA) (decoOf hv) (decoOf hb)
  | _, _, _, .lit _ t _ hexp => .lit t (decoOf hexp)
  | _, _, _, .conv _ _ _ _ _ h _ => decoOf h

/-! ### two chain transports -/

/-- A codomain chain under `A` lifts to a chain of Π types (the domain fixed, its sort
    from any typing of `A`). -/
def tyConvT_pi_codom {Γ : LCtx} {A : Expr Nat} {u : Level} (hA : HasTyT E n Γ A (.sort u)) :
    {B B' : Expr Nat} → TyConvT E n (.assumption A :: Γ) B B' →
    TyConvT E n Γ (.pi A B) (.pi A B')
  | _, _, .refl _ _ => .refl _ _
  | _, _, .of _ B B' v hc => .of _ _ _ (.imax u v) (.pi _ A A B B' u v (.refl _ A _ hA) hc)
  | _, _, .trans _ _ _ _ h₁ h₂ =>
      .trans _ _ _ _ (tyConvT_pi_codom hA h₁) (tyConvT_pi_codom hA h₂)

/-- A chain under a let binding substitutes the stored value (the `Type`-valued twin of
    `convT_substLet0_tyConvT`; same links, no `Nonempty`). -/
noncomputable def tyConvT_substLet0 (hW : EnvWfT E) {Γ : LCtx} {t w0 : Expr Nat}
    (hv : HasTyT E n Γ w0 t) :
    {X Y : Expr Nat} → TyConvT E n (.letBinding t w0 :: Γ) X Y →
    TyConvT E n Γ (instantiate0 w0 X) (instantiate0 w0 Y)
  | _, _, .refl _ _ => .refl _ _
  | _, _, .of _ _ _ _ hc => by
      have hc' := convT_substLet_of_envWfT hW t w0 (j := 0) hc (by simp)
        (by rw [lift_zero, lift_zero]; exact hv)
      rw [lift_zero] at hc'
      exact .of _ _ _ _ hc'
  | _, _, .trans _ _ _ _ h₁ h₂ =>
      .trans _ _ _ _ (tyConvT_substLet0 hW hv h₁) (tyConvT_substLet0 hW hv h₂)

/-! ### decorated uniqueness -/

/-- Two typings of one term with the same decoration have convertible types. `conv` layers
    are peeled on either side; at `app` the two indices are `instantiate0 a B` with the
    SHARED `B` (the domains may differ — they are not compared); at `pi` the shared sorts;
    `lam` / `letE` / `lit` recurse on the body and transport the chain (`tyConvT_pi_codom`,
    `tyConvT_substLet0`). No Π-injectivity and no sort uniqueness is consulted. -/
noncomputable def uniqD (hW : EnvWfT E) : {Γ : LCtx} → {e T₁ T₂ : Expr Nat} →
    (h₁ : HasTyT E n Γ e T₁) → (h₂ : HasTyT E n Γ e T₂) → decoOf h₁ = decoOf h₂ →
    TyConvT E n Γ T₁ T₂
  | _, _, _, _, .conv _ _ _ _ u h hc, h₂, hd =>
      .trans _ _ _ _ (.of _ _ _ u (.symm _ _ _ _ hc)) (uniqD hW h h₂ hd)
  | _, _, _, _, h₁, .conv _ _ _ _ u h hc, hd =>
      .trans _ _ _ _ (uniqD hW h₁ h hd) (.of _ _ _ u hc)
  | _, _, _, _, .sort _ _, .sort _ _, _ => .refl _ _
  | _, _, _, _, .bvar _ _ _ h, .bvar _ _ _ h', _ => by
      have hA := Option.some.inj (h.symm.trans h')
      subst hA; exact .refl _ _
  | _, _, _, _, .const _ _ _ _ hres _ _, .const _ _ _ _ hres' _ _, _ => by
      have hm := Option.some.inj (hres.symm.trans hres')
      subst hm; exact .refl _ _
  | _, _, _, _, .pi _ _ _ _ _ _ _, .pi _ _ _ _ _ _ _, hd => by
      simp only [decoOf] at hd
      injection hd with hA hB hu hv hdA hdB
      subst hu; subst hv; exact .refl _ _
  | _, _, _, _, .lam _ _ _ _ _ hA hb, .lam _ _ _ _ _ _ hb', hd => by
      simp only [decoOf] at hd
      injection hd with hA' hbody hu hdA hd'
      exact tyConvT_pi_codom hA (uniqD hW hb hb' hd')
  | _, _, _, _, .app _ _ _ _ _ _ _, .app _ _ _ _ _ _ _, hd => by
      simp only [decoOf] at hd
      injection hd with hf ha hB hdf hda
      subst hB; exact .refl _ _
  | _, _, _, _, .letE _ _ _ _ _ _ _ hv hb, .letE _ _ _ _ _ _ _ _ hb', hd => by
      simp only [decoOf] at hd
      injection hd with hA' hvalue hbody hu hdA hdv hd'
      exact tyConvT_substLet0 hW hv (uniqD hW hb hb' hd')
  | _, _, _, _, .lit _ _ _ hexp, .lit _ _ _ hexp', hd => by
      simp only [decoOf] at hd
      injection hd with ht hd'
      exact uniqD hW hexp hexp' hd'
termination_by _ _ _ _ h₁ h₂ _ => sizeOf h₁ + sizeOf h₂
decreasing_by all_goals (first | assumption | (simp_wf; assumption) | (simp <;> omega) | (simp_wf; simp <;> omega))

/-! ### `retype` on decoration-sharing pairs -/

/-- `OpenRows.retype` restricted to a step whose source typing shares the decoration of the
    target typing: decorated uniqueness, then `CStep.reindex`. -/
noncomputable def retypeD (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {b e T₁ T₂ : Expr Nat} (hb : HasTyT E n Γ b T₁) (s : CStep E n PEq Γ b e T₂)
    (hd : decoOf (s.leftTyped L hΓ) = decoOf hb) : CStep E n PEq Γ b e T₁ :=
  s.reindex (uniqD hW (s.leftTyped L hΓ) hb hd)

/-- Siles–Herbelin's Type Exchange (LICS 2010, Lemma III.6) for two certified steps out of
    one term whose source typings share the decoration: each step at the other's index. -/
noncomputable def exchangeD (hW : EnvWfT E) (L : LeafIface E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {b d e T₁ T₂ : Expr Nat}
    (p : CStep E n PEq Γ b d T₁) (q : CStep E n PEq Γ b e T₂)
    (hd : decoOf (p.leftTyped L hΓ) = decoOf (q.leftTyped L hΓ)) :
    CStep E n PEq Γ b d T₂ × CStep E n PEq Γ b e T₁ :=
  (p.reindex (uniqD hW (p.leftTyped L hΓ) (q.leftTyped L hΓ) hd),
   q.reindex (uniqD hW (q.leftTyped L hΓ) (p.leftTyped L hΓ) hd.symm))

/-! ### the other reduction: `Retype` from DT-012's shape -/

/-- DT-012's shape: two types of one term are convertible. -/
def Uniq (E : ResolvedEnv) (n : Nat) : Type :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {b T₁ T₂ : Expr Nat},
    HasTyT E n Γ b T₁ → HasTyT E n Γ b T₂ → TyConvT E n Γ T₁ T₂

/-- `Retype` from `Uniq`: reindex the step along the two types of its source. -/
def retype_of_uniq (L : LeafIface E n PEq) (U : Uniq E n) : Retype E n PEq :=
  fun {_} hΓ {_ _ _ _} hb s => s.reindex (U hΓ (s.leftTyped L hΓ) hb)

end Rcic.Declarative.NativeValleys
