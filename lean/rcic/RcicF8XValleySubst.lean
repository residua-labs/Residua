import rcic.RcicF8XValleyViaS

/-!
# `RcicF8XValleySubst` — the W-X-SUBST slice-2 route: re-entry at the source

The strict/W routes refuse `EvCv.esub` / `EvTc.subst0` / `EvTc.substLet`
(W-X-SUBST): any transport of a valley across the link's substitution cites
the kept substituent typing `hv`, breaking `Strict` (E-X-MULT's shape). This
module is the cc-ruled route (B) of `S1_W_X_SUBST_2.md`: the substituted link
re-enters the SEGMENT route at its SOURCE context under the `CtxWfViaS`
premise, and the `CtxMorph` stack is applied once at EXPOSURE, to the
component pair (`XOut`), never to a valley.

**The forced asymmetry (S1 §4, verbatim — ruling Q1):**

> Context transport runs in OPPOSITE orders for weakening and for
> substitution, and the asymmetry is forced, not chosen. A weakening carries
> no leaf: `Valley.thinDeep`/`EvPar.wk` move a valley citing nothing
> (`thinDeep_leaves`), so WK-1b transports J's answer FIRST and runs U/D/S at
> the segment context, where the caller's `CtxWfT` lives. A substitution link
> carries its substituent typing `hv`, whose atoms are atoms of the X input
> (`SubEq`, never `SubOf`); every crossing of the link — `Valley.subst0`,
> `EvPar.readSubst0`, `EvTc.subst0` — cites `hv`, so a U/D/S bundle taken
> after a crossing holds a kept atom and `SOut.Bound`'s `Strict` clause fails
> (E-X-MULT's shape: `DMStep` keeps an atom only at multiplicity ≤ the
> caller's). Hence a substituted fragment runs its calls FIRST, at the
> fragment's source context under the `CtxWfViaS` premise (J via
> `JProcViaSP`, D via `DProcViaSP`, U/S premise-free), and applies the stack
> LAST, once, to the exposed component pair (`XOut.subst0`/`substLet`), which
> enters no call. The disciplines compose: a weakening inside a substituted
> fragment is pushed to the fragment's call context (WK-1b, leaf-free); a
> substitution inside a weakened fragment re-enters at its own source and is
> exposed before the weakening is applied to the pair. A join of a
> substituted link with another link would need the pair as a valley at the
> outer context, i.e. a transport before a call; it is refused by admission
> and named `W-X-SUBST-JOIN`.

**W-X-SUBST-JOIN** is reachable on main: `om_etaK_annot_request` applies X to
`om_etaK_annot_piChain`'s output, which flattens to a three-link segment
`[ofCv (symm lit-β), subst0, ofCv lit-β]` whenever the inverted typing carries
a conversion (the sealed fixture `RcicF8XJoinA2` pins exactly that: `a2_three_
links`, `a2_xAdmW_false`, `a2_bLinkWs = [true, false, true]`). The named
refusal covers both shapes: (1) a ≥2-link segment containing a substitution
link, (2) a `trans` conversion with a substituted child inside one link.

**Why `size`/`sizeOf` alone cannot be the measure.** The recursion at a
substitution node re-enters through `flattenCv`/`flattenTc` + `Flat.segment`,
and `sizeOf` is NOT monotone under flattening: `linkSymm` pushes `EvCv.symm`
into every link, `flattenTc (.wk d k c) = (flattenTc c).wk d k` pushes
`EvTc.wk` into every link, and nested `symm`/`wk` wrappers can make the flat
chain heavier than the tree. The custom weight `wt` (§1) puts 0 on exactly the
nodes flattening pushes or drops (`refl`, `symm`, `trans`, `wk`, `castIdx`;
`EvTc.lit d` ↦ the `TyConvT.of` count) and `1 + child` on the rest, so
flattening and segmentation PRESERVE `wt` exactly (`flattenCv_wt`,
`flattenT_wt`, `flattenTc_wt`, `Flat.splitPi_wt`, `Flat.segment_wt`), while
the substitution node contributes `1 + c.wt` and the re-entry drops `wt`
strictly. Admission and the route both recurse on `(wt, sizeOf)`
lexicographically; the `reentryCv`/`reentryTc` helpers pay `+1` on `wt` so
the node→helper edge drops `sizeOf` and the helper→`admS`/`xSegsS` edge drops
`wt` (flattening can grow `sizeOf`, so `+1` is needed — without it the second
edge is stuck at equal first components).

**Named refusals inside `xAdmS = false`** (besides W-X-SUBST-JOIN):
`[x_read_subst_var]` — the substituted variable is itself the Π (the inner
source endpoint `a₀`/`b₀` fails `isPi` while the outer instantiated endpoint
is Π; raised at ADMISSION here, where PR-B raised it in `readStarC`'s arm);
`W-X-SUBST-IDX` — the inner index `T₀` is not a literal sort (`flattenCv`
needs it); and W-X-LEVELS (`sorts`/`consts`).

**Dev note — `reentryCv` carries a BOTH-directions check.** `xCvS`'s `symm`
spine is deferred to the re-entry point by a `flag : Bool` (K is not
call-free for the census — a pair-level `XOut.symm` would spend a K call
inside a link); under `flag = true` the route re-enters on the `symm`'d inner
chain, whose `admS` premise is not derivable from the forward one without a
segment-symm lemma. Rather than prove `Segs.admS` invariant under
`Flat.symm` + `segment`, admission checks both directions — the two are
semantically equal anyway, and a fragment admissible in only one direction
could not be served under a `symm` wrapper, so refusing is honest.

Named opens: `Rcic.Syn`, `Rcic.Declarative.F8EtaK` is NOT needed here (the
A.2 reachability fixture lives in `RcicF8XJoinA2`); opened: `Rcic.Syn`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)} {Γ : LCtx}

/-! ### §1 the flattening-invariant weight -/

/-- weight of a plain `TyConvT` chain: `refl` drops, `trans` splits, `of` is
    one link. -/
def tcWt : {Γ : LCtx} → {A B : Expr Nat} → TyConvT E n Γ A B → Nat
  | _, _, _, .refl _ _ => 0
  | _, _, _, .of _ _ _ _ _ => 1
  | _, _, _, .trans _ _ _ _ d₁ d₂ => tcWt d₁ + tcWt d₂

/-- the flattening weight of a provenance conversion: 0 on `refl`/`symm`/
    `trans`/`wk` (the nodes flattening drops or pushes), the node itself
    otherwise. `tyConv`/`rety`/`esub` keep only the first conversion child's
    weight — flattening wraps the whole node opaquely in one link, so any
    assignment summing to the node's own weight is correct; `1 + c.wt` is
    what the re-entry needs.

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def EvCv.wt : {Γ : LCtx} → {a b T : Expr Nat} → EvCv R Γ a b T → Nat
  | _, _, _, _, .lit _ _ => 1
  | _, _, _, _, .refl _ => 0
  | _, _, _, _, .symm c => c.wt
  | _, _, _, _, .trans c₁ c₂ => c₁.wt + c₂.wt
  | _, _, _, _, .tyConv _ c _ => 1 + c.wt
  | _, _, _, _, .rety c _ => 1 + c.wt
  | _, _, _, _, .wk _ _ c => c.wt
  | _, _, _, _, .esub _ _ c _ _ _ => 1 + c.wt
  | _, _, _, _, .subst0 _ c _ _ => 1 + c.wt
  | _, _, _, _, .substLet _ c _ _ => 1 + c.wt
  | _, _, _, _, .sorts .. => 1
  | _, _, _, _, .consts .. => 1

/-- the flattening weight of a provenance type-conversion chain.

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def EvTc.wt : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → Nat
  | _, _, _, .lit d _ => tcWt d
  | _, _, _, .ofCv _ c => c.wt
  | _, _, _, .refl _ _ => 0
  | _, _, _, .symm c => c.wt
  | _, _, _, .trans c₁ c₂ => c₁.wt + c₂.wt
  | _, _, _, .piCod .. => 1
  | _, _, _, .subst0 _ c _ _ => 1 + c.wt
  | _, _, _, .substLet _ c _ _ => 1 + c.wt
  | _, _, _, .wk _ _ c => c.wt

/-- the weight of a flat chain: the links' weights. -/
def Flat.wt : {A B : Expr Nat} → Flat R Γ A B → Nat
  | _, _, .nil _ => 0
  | _, _, .cons l _ rest => l.wt + rest.wt

/-- the weight of a segmented chain: the segments' weights. -/
def Segs.wt : {P Q : Expr Nat} → Segs R Γ P Q → Nat
  | _, _, .nil _ => 0
  | _, _, .cons p _ rest => p.wt + rest.wt

/-! the flattening preserves `wt` exactly -/

/-- `castIdx` is index-only: weight-free. -/
theorem EvCv.castIdx_wt {Γ : LCtx} {a b T T' : Expr Nat} (h : T = T')
    (c : EvCv R Γ a b T) : (EvCv.castIdx h c).wt = c.wt := by
  subst h; rfl

/-- `linkSymm` is weight-free: the pushed `symm` nodes weigh 0.

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
theorem linkSymm_wt : {Γ : LCtx} → {A B : Expr Nat} → (l : EvTc R Γ A B) →
    (hl : isLink l = true) → (linkSymm l hl).wt = l.wt
  | _, _, _, .ofCv _ _, _ => rfl
  | _, _, _, .piCod .., _ => rfl
  | _, _, _, .subst0 .., _ => rfl
  | _, _, _, .substLet .., _ => rfl
  | _, _, _, .wk d k l, hl => by
      simp only [linkSymm, EvTc.wt]
      exact linkSymm_wt l (by simpa only [isLink] using hl)
  | _, _, _, .lit .., hl => nomatch hl
  | _, _, _, .refl .., hl => nomatch hl
  | _, _, _, .symm .., hl => nomatch hl
  | _, _, _, .trans .., hl => nomatch hl

/-- `Flat.append` splits the weight. -/
theorem Flat.append_wt : {A M B : Expr Nat} → (f : Flat R Γ A M) →
    (g : Flat R Γ M B) → (f.append g).wt = f.wt + g.wt
  | _, _, _, .nil _, g => by simp only [Flat.append, Flat.wt, Nat.zero_add]
  | _, _, _, .cons l hl rest, g => by
      simp only [Flat.append, Flat.wt, rest.append_wt g, Nat.add_assoc]

/-- `Flat.symm` preserves the weight. -/
theorem Flat.symm_wt : {A B : Expr Nat} → (f : Flat R Γ A B) →
    f.symm.wt = f.wt
  | _, _, .nil _ => rfl
  | _, _, .cons l hl rest => by
      simp only [Flat.symm, Flat.append_wt, Flat.wt, linkSymm_wt, rest.symm_wt,
        Nat.add_zero]
      omega

/-- `Flat.wk` preserves the weight. -/
theorem Flat.wk_wt (d : LocalDecl) (k : Nat) : {A B : Expr Nat} →
    (f : Flat R Γ A B) → (f.wk d k).wt = f.wt
  | _, _, .nil _ => rfl
  | _, _, .cons l hl rest => by
      simp only [Flat.wk, Flat.wt, EvTc.wt, rest.wk_wt d k]

/-- `flattenCv` preserves the weight exactly.

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
theorem flattenCv_wt (u : Level) : {Γ : LCtx} → {a b T : Expr Nat} →
    (c : EvCv R Γ a b T) → (hT : T = .sort u) → (flattenCv u c hT).wt = c.wt
  | _, _, _, _, .trans c₁ c₂, hT => by
      simp only [flattenCv, Flat.append_wt, flattenCv_wt u c₁ hT,
        flattenCv_wt u c₂ hT, EvCv.wt]
  | _, _, _, _, .symm c, hT => by
      simp only [flattenCv, Flat.symm_wt, flattenCv_wt u c hT, EvCv.wt]
  | _, _, _, _, .refl _, _ => rfl
  | _, _, _, _, .lit h hsub, hT => by
      simp only [flattenCv, Flat.wt, EvTc.wt, EvCv.castIdx_wt, EvCv.wt,
        Nat.add_zero]
  | _, _, _, _, .tyConv u' c cA, hT => by
      simp only [flattenCv, Flat.wt, EvTc.wt, EvCv.castIdx_wt, EvCv.wt,
        Nat.add_zero]
  | _, _, _, _, .wk d k c, hT => by
      simp only [flattenCv, Flat.wt, EvTc.wt, EvCv.castIdx_wt, EvCv.wt,
        Nat.add_zero]
  | _, _, _, _, .esub .., hT => by
      simp only [flattenCv, Flat.wt, EvTc.wt, EvCv.castIdx_wt, EvCv.wt,
        Nat.add_zero]
  | _, _, _, _, .subst0 .., hT => by
      simp only [flattenCv, Flat.wt, EvTc.wt, EvCv.castIdx_wt, EvCv.wt,
        Nat.add_zero]
  | _, _, _, _, .substLet .., hT => by
      simp only [flattenCv, Flat.wt, EvTc.wt, EvCv.castIdx_wt, EvCv.wt,
        Nat.add_zero]
  | _, _, _, _, .sorts .., hT => by
      simp only [flattenCv, Flat.wt, EvTc.wt, EvCv.castIdx_wt, EvCv.wt,
        Nat.add_zero]
  | _, _, _, _, .consts .., hT => by
      simp only [flattenCv, Flat.wt, EvTc.wt, EvCv.castIdx_wt, EvCv.wt,
        Nat.add_zero]
  | _, _, _, _, .rety c cA, hT => by
      simp only [flattenCv, Flat.wt, EvTc.wt, EvCv.castIdx_wt, EvCv.wt,
        Nat.add_zero]

/-- `flattenT` preserves the weight exactly. -/
theorem flattenT_wt : {Γ : LCtx} → {A B : Expr Nat} →
    (d : TyConvT E n Γ A B) →
    (hsub : ∃ r ∈ R, SubEq (.tc d) r) → (flattenT d hsub).wt = tcWt d
  | _, _, _, .refl _ _, _ => by simp only [flattenT, Flat.wt, tcWt]
  | _, _, _, .of _ _ _ u h, _ => by
      simp only [flattenT, Flat.wt, EvTc.wt, EvCv.wt, tcWt, Nat.add_zero]
  | _, _, _, .trans _ _ _ _ d₁ d₂, hsub => by
      simp only [flattenT, Flat.append_wt, flattenT_wt d₁, flattenT_wt d₂,
        tcWt]

/-- `flattenTc` preserves the weight exactly.

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
theorem flattenTc_wt : {Γ : LCtx} → {A B : Expr Nat} → (c : EvTc R Γ A B) →
    (flattenTc c).wt = c.wt
  | _, _, _, .lit d hsub => flattenT_wt d hsub
  | _, _, _, .ofCv u c => flattenCv_wt u c rfl
  | _, _, _, .refl _ _ => rfl
  | _, _, _, .symm c => by
      simp only [flattenTc, Flat.symm_wt, flattenTc_wt c, EvTc.wt]
  | _, _, _, .trans c₁ c₂ => by
      simp only [flattenTc, Flat.append_wt, flattenTc_wt c₁, flattenTc_wt c₂,
        EvTc.wt]
  | _, _, _, .piCod .. => by
      simp only [flattenTc, Flat.wt, EvTc.wt, Nat.add_zero]
  | _, _, _, .subst0 .. => by
      simp only [flattenTc, Flat.wt, EvTc.wt, Nat.add_zero]
  | _, _, _, .substLet .. => by
      simp only [flattenTc, Flat.wt, EvTc.wt, Nat.add_zero]
  | _, _, _, .wk d k c => by
      simp only [flattenTc, Flat.wk_wt, flattenTc_wt c, EvTc.wt]

/-- `splitPi` splits the weight between the cut prefix and the rest. -/
theorem Flat.splitPi_wt : {A₀ C : Expr Nat} → (f : Flat R Γ A₀ C) →
    (hC : isPi C = true) →
    (f.splitPi hC).2.2.1.wt + (f.splitPi hC).2.2.2.wt = f.wt
  | _, _, .nil _, _ => rfl
  | _, _, @Flat.cons _ _ _ _ A M B l hl rest, hC => by
      have ih := rest.splitPi_wt hC
      cases M <;> simp only [Flat.splitPi, Flat.wt] <;> omega

/-- `segmentF` preserves the weight. -/
theorem Flat.segmentF_wt : (N : Nat) → {P Q : Expr Nat} → (f : Flat R Γ P Q) →
    (hQ : isPi Q = true) → (Flat.segmentF N f hQ).wt = f.wt
  | _, _, _, .nil _, _ => by simp only [Flat.segmentF, Segs.wt, Flat.wt]
  | 0, _, _, .cons l hl rest, hQ => by
      simp only [Flat.segmentF, Segs.wt, Nat.add_zero]
  | N + 1, _, _, .cons l hl rest, hQ => by
      have ih := Flat.segmentF_wt N ((Flat.cons l hl rest).splitPi hQ).2.2.2 hQ
      have hs := (Flat.cons l hl rest).splitPi_wt hQ
      simp only [Flat.segmentF, Segs.wt, ih]
      exact hs

/-- `segment` preserves the weight. -/
theorem Flat.segment_wt {P Q : Expr Nat} (f : Flat R Γ P Q)
    (hQ : isPi Q = true) : (f.segment hQ).wt = f.wt :=
  Flat.segmentF_wt _ f hQ

/-! ### §2 the admission `xAdmS` -/

mutual

/-- `bCvW` with the W-X-SUBST re-entry: an `esub` re-flattens, re-segments and
    re-checks its inner chain; a `trans` is a JOIN — checked W-only, no
    substitution on either side (W-X-SUBST-JOIN).

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def bCvS : {Γ : LCtx} → {a b T : Expr Nat} → EvCv R Γ a b T → Bool
  | _, _, _, _, .lit _ _ => true
  | _, _, _, _, .refl _ => true
  | _, _, _, _, .symm c => bCvS c
  | _, _, _, _, .trans c₁ c₂ => bCvW c₁ && bCvW c₂
  | _, _, _, _, .tyConv _ c _ => bCvS c
  | _, _, _, _, .rety c _ => bCvS c
  | _, _, _, _, .wk _ _ c => bCvS c
  | _, _, _, _, .esub _ _ c _ _ _ => reentryCv c
  | _, _, _, _, .subst0 _ c _ _ => reentryCv c
  | _, _, _, _, .substLet _ c _ _ => reentryCv c
  | _, _, _, _, .sorts .. => false
  | _, _, _, _, .consts .. => false
termination_by Γ a b T c => (c.wt, sizeOf c)
decreasing_by
  all_goals (simp only [EvCv.wt, EvTc.wt, Flat.wt, Segs.wt] at *; simp_wf; try omega)
  all_goals (first | (exact Prod.Lex.right _ (by omega)) | (exact Prod.Lex.left _ _ (by omega)))

/-- the cv re-entry: the inner index must be a literal sort and both inner
    endpoints Π; the inner chain is re-flattened and re-segmented and its
    segments checked — in BOTH directions (the route's `symm` flag defers the
    direction choice to this point; the two checks are semantically equal —
    `Flat.symm` swaps the link list, not the per-link data).
    Refusals: `[x_read_subst_var]` (an inner endpoint fails `isPi`),
    `W-X-SUBST-IDX` (`T₀` not a literal sort).

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def reentryCv : {Γ : LCtx} → {a b T : Expr Nat} → EvCv R Γ a b T → Bool
  | _, a, b, T, c =>
      match T with
      | .sort u =>
          if hb : isPi b then
            if ha : isPi a then
              ((flattenCv u c rfl).segment hb).admS &&
              ((flattenCv u (.symm c) rfl).segment ha).admS
            else false
          else false
      | _ => false
termination_by Γ a b T c => (c.wt + 1, sizeOf c)
decreasing_by
  · rw [Flat.segment_wt, flattenCv_wt]
    exact Prod.Lex.left _ _ (Nat.lt_succ_self _)
  · rw [Flat.segment_wt, flattenCv_wt]
    exact Prod.Lex.left _ _ (Nat.lt_succ_self _)

/-- `bLinkW` with the W-X-SUBST re-entry: a `subst0`/`substLet` link re-flattens,
    re-segments and re-checks its inner chain; a `wk` wrapper descends.

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def bLinkS : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → Bool
  | _, _, _, .lit _ _ => false
  | _, _, _, .ofCv _ c => bCvS c
  | _, _, _, .refl _ _ => false
  | _, _, _, .symm _ => false
  | _, _, _, .trans _ _ => false
  | _, _, _, .piCod .. => false
  | _, _, _, .subst0 _ c _ _ => reentryTc c
  | _, _, _, .substLet _ c _ _ => reentryTc c
  | _, _, _, .wk _ _ l => bLinkS l
termination_by Γ A B l => (l.wt, sizeOf l)
decreasing_by
  all_goals (simp only [EvCv.wt, EvTc.wt, Flat.wt, Segs.wt] at *; simp_wf; try omega)
  all_goals (first | (exact Prod.Lex.right _ (by omega)) | (exact Prod.Lex.left _ _ (by omega)))

/-- the link re-entry: both inner endpoints Π, the inner chain re-flattened,
    re-segmented and its segments checked.

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def reentryTc : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → Bool
  | _, A, B, c =>
      if hB : isPi B then
        if isPi A then
          ((flattenTc c).segment hB).admS
        else false
      else false
termination_by Γ A B c => (c.wt + 1, sizeOf c)
decreasing_by
  all_goals (rw [Flat.segment_wt, flattenTc_wt]; exact Prod.Lex.left _ _ (by omega))

/-- `Flat.segAdmW` with the substitution link admitted on its own: a single
    link is Stratum-A `piSpinedTc` or a `bLinkS`; a join segment keeps the
    W-free predicates (W-X-SUBST-JOIN — no substitution re-enters under a
    join).

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def Flat.segAdmS : {Γ : LCtx} → {P M : Expr Nat} → Flat R Γ P M → Bool
  | _, _, _, .nil _ => true
  | _, _, _, .cons l _ (.nil _) => piSpinedTc l || bLinkS l
  | _, _, _, .cons l _ (.cons l' hl' rest') =>
      bLinkW l && (Flat.cons l' hl' rest').bPrefixW
termination_by Γ P M f => (f.wt, sizeOf f)
decreasing_by
  simp only [EvCv.wt, EvTc.wt, Flat.wt, Segs.wt] at *; simp_wf
  first | (exact Prod.Lex.right _ (by omega)) | (exact Prod.Lex.left _ _ (by omega))

/-- `Segs.admW` over `segAdmS`. -/
def Segs.admS : {Γ : LCtx} → {P Q : Expr Nat} → Segs R Γ P Q → Bool
  | _, _, _, .nil _ => true
  | _, _, _, .cons p _ rest => p.segAdmS && rest.admS
termination_by Γ P Q s => (s.wt, sizeOf s)
decreasing_by
  all_goals (simp only [EvCv.wt, EvTc.wt, Flat.wt, Segs.wt] at *; simp_wf; try omega)
  all_goals (first | (exact Prod.Lex.left _ _ (by omega)) | (exact Prod.Lex.right _ (by omega)))

end

/-- the segment-level admission entry point (slice 2's `admS`). -/
def admS {Γ : LCtx} {P Q : Expr Nat} (s : Segs R Γ P Q) : Bool := s.admS

/-- admissibility of an X input under the W-X-SUBST slice-2 fragment:
    every segment is Stratum-A, a valley prefix, or a lone substitution
    link re-entered at its source (`false` = W-X-SUBST-JOIN /
    `[x_read_subst_var]` / `W-X-SUBST-IDX` / W-X-LEVELS, reported). -/
def xAdmS {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B')) :
    Bool :=
  ((flattenTc c).segment rfl).admS

/-! the fragment only grows: the W fragment is inside the S fragment
    (monotonicity) -/

theorem bCvS_of_bCvW : {Γ : LCtx} → {a b T : Expr Nat} →
    (c : EvCv R Γ a b T) → bCvW c = true → bCvS c = true
  | _, _, _, _, .lit _ _, _ => by simp only [bCvS]
  | _, _, _, _, .refl _, _ => by simp only [bCvS]
  | _, _, _, _, .symm c, h => by
      simp only [bCvS]
      exact bCvS_of_bCvW c (by simpa only [bCvW] using h)
  | _, _, _, _, .trans _ _, h => by
      simpa only [bCvS, bCvW] using h
  | _, _, _, _, .tyConv _ c _, h => by
      simp only [bCvS]
      exact bCvS_of_bCvW c (by simpa only [bCvW] using h)
  | _, _, _, _, .rety c _, h => by
      simp only [bCvS]
      exact bCvS_of_bCvW c (by simpa only [bCvW] using h)
  | _, _, _, _, .wk _ _ c, h => by
      simp only [bCvS]
      exact bCvS_of_bCvW c (by simpa only [bCvW] using h)
  | _, _, _, _, .esub .., h => nomatch h
  | _, _, _, _, .sorts .., h => nomatch h
  | _, _, _, _, .consts .., h => nomatch h

theorem bLinkS_of_bLinkW : {Γ : LCtx} → {A B : Expr Nat} →
    (l : EvTc R Γ A B) → bLinkW l = true → bLinkS l = true
  | _, _, _, .ofCv _ c, h => by
      simp only [bLinkS]
      exact bCvS_of_bCvW c (by simpa only [bLinkW] using h)
  | _, _, _, .wk _ _ l, h => by
      simp only [bLinkS]
      exact bLinkS_of_bLinkW l (by simpa only [bLinkW] using h)
  | _, _, _, .piCod .., h => nomatch h
  | _, _, _, .subst0 .., h => nomatch h
  | _, _, _, .substLet .., h => nomatch h
  | _, _, _, .lit .., h => nomatch h
  | _, _, _, .refl .., h => nomatch h
  | _, _, _, .symm .., h => nomatch h
  | _, _, _, .trans .., h => nomatch h

theorem Flat.segAdmS_of_segAdmW : {P M : Expr Nat} → (p : Flat R Γ P M) →
    p.segAdmW = true → p.segAdmS = true
  | _, _, .nil _, _ => by simp only [Flat.segAdmS]
  | _, _, .cons l _ (.nil _), h => by
      have h' : (piSpinedTc l || bLinkW l) = true := by
        simpa only [Flat.segAdmW] using h
      cases hp : piSpinedTc l with
      | true => simp only [Flat.segAdmS, hp, Bool.true_or]
      | false =>
          rw [hp, Bool.false_or] at h'
          simp only [Flat.segAdmS, hp, Bool.false_or]
          exact bLinkS_of_bLinkW l h'
  | _, _, .cons l _ (.cons l' hl' rest'), h => by
      simpa only [Flat.segAdmS, Flat.segAdmW] using h

theorem Segs.admS_of_admW : {P Q : Expr Nat} → (s : Segs R Γ P Q) →
    s.admW = true → s.admS = true
  | _, _, .nil _, _ => by simp only [Segs.admS]
  | _, _, .cons p _ rest, h => by
      have h' : p.segAdmW = true ∧ rest.admW = true := by
        simpa only [Segs.admW, Bool.and_eq_true] using h
      simp only [Segs.admS, Bool.and_eq_true]
      exact ⟨p.segAdmS_of_segAdmW h'.1, rest.admS_of_admW h'.2⟩

theorem xAdmS_of_xAdmW {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) :
    xAdmW c = true → xAdmS c = true :=
  Segs.admS_of_admW _

/-- the `esub` arm unfolds to the cv re-entry (`bCvW`'s refusal,
    complement). -/
theorem bCvS_esub {Γ : LCtx} {a b T t v : Expr Nat} (j : Nat) (u : Level)
    (h : EvCv R Γ a b T) (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : EvTy R (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    bCvS (EvCv.esub j u h hget hv hvT) = reentryCv h := by
  simp only [bCvS]

/-- the `subst0` arm unfolds to the link re-entry (`bLinkW`'s refusal,
    complement). -/
theorem bLinkS_subst0 {Γ : LCtx} {A A' t v : Expr Nat} (j : Nat)
    (c : EvTc R Γ A A') (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
    bLinkS (EvTc.subst0 j c hget hv) = reentryTc c := by
  simp only [bLinkS]

theorem bLinkS_substLet {Γ : LCtx} {A A' t w0 : Expr Nat} (j : Nat)
    (c : EvTc R Γ A A') (hget : Γ[j]? = some (.letBinding t w0))
    (hv : EvTy R (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t)) :
    bLinkS (EvTc.substLet j c hget hv) = reentryTc c := by
  simp only [bLinkS]

/-- and the W fragment still refuses a substitution link. -/
theorem bLinkW_subst0 {Γ : LCtx} {A A' t v : Expr Nat} (j : Nat)
    (c : EvTc R Γ A A') (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
    bLinkW (EvTc.subst0 j c hget hv) = false := rfl

theorem bLinkW_substLet {Γ : LCtx} {A A' t w0 : Expr Nat} (j : Nat)
    (c : EvTc R Γ A A') (hget : Γ[j]? = some (.letBinding t w0))
    (hv : EvTy R (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t)) :
    bLinkW (EvTc.substLet j c hget hv) = false := rfl

/-! #### the admission witnesses the re-entry's `isPi`/sort conditions

`reentryCv`/`reentryTc` fold the index-sort test and the two `isPi`
tests into a Bool; the route needs the content back as hypotheses. -/

/-- the cv re-entry forces a sort index; a `true` verdict exposes both
    `isPi` proofs and the flattened/segmented inner chain admissible in
    BOTH directions (the route's `symm` flag picks between them). -/
theorem reentryCv_spec {Γ : LCtx} {a b T : Expr Nat}
    (c : EvCv R Γ a b T) (h : reentryCv c = true) :
    ∃ (u : Level) (hT : T = .sort u) (hb : isPi b = true) (ha : isPi a = true),
      ((flattenCv u (EvCv.castIdx hT c) rfl).segment hb).admS = true ∧
      ((flattenCv u ((EvCv.castIdx hT c).symm) rfl).segment ha).admS = true := by
  induction T generalizing a b with
  | sort u =>
      simp only [reentryCv] at h
      split at h
      · case isTrue hb =>
          split at h
          · case isTrue ha => exact ⟨u, rfl, hb, ha, Bool.and_eq_true_iff.mp h⟩
          · case isFalse ha => exact absurd h (by decide)
      · case isFalse hb => exact absurd h (by decide)
  | bvar i => simp [reentryCv] at h
  | const r ls => simp [reentryCv] at h
  | app f x => simp [reentryCv] at h
  | lam A' b' => simp [reentryCv] at h
  | pi A' B' => simp [reentryCv] at h
  | letE A' v b' => simp [reentryCv] at h
  | lit t => simp [reentryCv] at h

/-- the link re-entry disassembled: a `true` verdict exposes both `isPi`
    proofs and the flattened/segmented inner chain's admissibility. -/
theorem reentryTc_spec {Γ : LCtx} {A B : Expr Nat} (c : EvTc R Γ A B)
    (h : reentryTc c = true) :
    ∃ (hB : isPi B = true) (_ : isPi A = true),
      ((flattenTc c).segment hB).admS = true := by
  simp only [reentryTc] at h
  split at h
  · case isTrue hB =>
      split at h
      · case isTrue hA => exact ⟨hB, hA, h⟩
      · case isFalse hA => exact absurd h (by decide)
  · case isFalse hB => exact absurd h (by decide)

/-! ### §3 the exposure transports on the component pair

Both components of `XOut` are `EvTc` chains, so the W-X-SUBST exposures
are the `xStructTc` `wk`/`subst0`/`substLet` arms (RcicF8XStruct.lean)
factored into standalone transports — the worker in §4 calls them at the
moment the component pair crosses the context stack.

The forced asymmetry, one more time.  `wk` is leaf-free, so weakening
waits until after the supplier/J answers are in hand and is applied to
the PAIR at the segment context — the valley itself was deep-thinned by
the source witness.  A substitution carries the kept substituent atom
`hv`, so it cannot ride a lazy valley: the stack is applied ONCE, at
exposure, to the pair the source-context re-entry produced. -/

/-- one weakening at depth `k` exposes through both components (the
    second weakened one binder deeper, under the binder `lift k 1 P₁`
    it opens). -/
def XOut.wk (d : LocalDecl) (k : Nat) {Γ₀ : LCtx} {P₁ P₂ Q₁ Q₂ : Expr Nat}
    (o : XOut R Γ₀ P₁ P₂ Q₁ Q₂) :
    XOut R (insertAt d k Γ₀) (lift k 1 P₁) (lift (k + 1) 1 P₂)
      (lift k 1 Q₁) (lift (k + 1) 1 Q₂) :=
  (.wk d k o.1, .wk d (k + 1) o.2)

/-- `subst0` at `j` with substituent typing `hv`: the first component at
    `j`, the second at `j + 1` under the newly exposed binder —
    `substBinderArg` weakens `hv` into the binder slot and
    `lift_lift_merge` re-associates `lift 0 1 (lift 0 j v)` into
    `lift 0 (j + 1) v` (the `xStructTc` `subst0` arm). -/
def XOut.subst0 {Γ₀ : LCtx} {P₁ P₂ Q₁ Q₂ t v : Expr Nat} (j : Nat)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t))
    (o : XOut R Γ₀ P₁ P₂ Q₁ Q₂) :
    XOut R (substRemove v j Γ₀)
      (instantiate j (lift 0 j v) P₁)
      (instantiate (j + 1) (lift 0 1 (lift 0 j v)) P₂)
      (instantiate j (lift 0 j v) Q₁)
      (instantiate (j + 1) (lift 0 1 (lift 0 j v)) Q₂) :=
  (.subst0 j o.1 hget hv,
   EvTc.cast rfl
     (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
     (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
     (.subst0 (j + 1) o.2 (by simpa using hget)
       (substBinderArg (d := .assumption P₁) hv)))

/-- `substLet` at `j`: the let-binding counterpart, same shape. -/
def XOut.substLet {Γ₀ : LCtx} {P₁ P₂ Q₁ Q₂ t w₀ : Expr Nat} (j : Nat)
    (hget : Γ₀[j]? = some (.letBinding t w₀))
    (hv : EvTy R (substRemove w₀ j Γ₀) (lift 0 j w₀) (lift 0 j t))
    (o : XOut R Γ₀ P₁ P₂ Q₁ Q₂) :
    XOut R (substRemove w₀ j Γ₀)
      (instantiate j (lift 0 j w₀) P₁)
      (instantiate (j + 1) (lift 0 1 (lift 0 j w₀)) P₂)
      (instantiate j (lift 0 j w₀) Q₁)
      (instantiate (j + 1) (lift 0 1 (lift 0 j w₀)) Q₂) :=
  (.substLet j o.1 hget hv,
   EvTc.cast rfl
     (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w₀])
     (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w₀])
     (.substLet (j + 1) o.2 (by simpa using hget)
       (substBinderArg (d := .assumption P₁) hv)))

/-- `wk` is leaf-free: the exposed pair's leaves are the pair's leaves. -/
theorem XOut.wk_leaves (d : LocalDecl) (k : Nat) {Γ₀ : LCtx}
    {P₁ P₂ Q₁ Q₂ : Expr Nat} (o : XOut R Γ₀ P₁ P₂ Q₁ Q₂) :
    XOut.leaves (o.wk d k) = XOut.leaves o := by
  simp only [XOut.wk, XOut.leaves, EvTc.leaves]

/-- `subst0` carries the kept atom: every output leaf is an original pair
    leaf or a substituent leaf (`hv`'s atom appears once per component —
    `substBinderArg_leaves` keeps it a `leaf`, the `EvTc.cast` is
    leaf-invariant). -/
theorem XOut.subst0_leaves {Γ₀ : LCtx} {P₁ P₂ Q₁ Q₂ t v : Expr Nat}
    (j : Nat) (hget : Γ₀[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t))
    (o : XOut R Γ₀ P₁ P₂ Q₁ Q₂) {ℓ : Jd E n}
    (hℓ : ℓ ∈ XOut.leaves (XOut.subst0 j hget hv o)) :
    ℓ ∈ XOut.leaves o ∨ ℓ ∈ hv.leaves := by
  simp only [XOut.subst0, XOut.leaves, EvTc.leaves, EvTc.cast_leaves,
    substBinderArg_leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
  · exact .inl (.inl hℓ)
  · exact .inr hℓ
  · exact .inl (.inr hℓ)
  · exact .inr hℓ

/-- the `substLet` counterpart. -/
theorem XOut.substLet_leaves {Γ₀ : LCtx} {P₁ P₂ Q₁ Q₂ t w₀ : Expr Nat}
    (j : Nat) (hget : Γ₀[j]? = some (.letBinding t w₀))
    (hv : EvTy R (substRemove w₀ j Γ₀) (lift 0 j w₀) (lift 0 j t))
    (o : XOut R Γ₀ P₁ P₂ Q₁ Q₂) {ℓ : Jd E n}
    (hℓ : ℓ ∈ XOut.leaves (XOut.substLet j hget hv o)) :
    ℓ ∈ XOut.leaves o ∨ ℓ ∈ hv.leaves := by
  simp only [XOut.substLet, XOut.leaves, EvTc.leaves, EvTc.cast_leaves,
    substBinderArg_leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with (hℓ | hℓ) | (hℓ | hℓ)
  · exact .inl (.inl hℓ)
  · exact .inr hℓ
  · exact .inl (.inr hℓ)
  · exact .inr hℓ

/-! §3b — bound transport on `SegOut`/`SOut`: a leaf bound may widen
    (weakened leaves are the same leaves; substituted leaves add the
    substituent's). -/

/-- `Below` widens under `++` on the bound list. -/
theorem Below_of_subset {ℓ : Jd E n} {L L' : List (Jd E n)}
    (h : Below ℓ L) (hs : ∀ x ∈ L, x ∈ L') : Below ℓ L' := by
  obtain ⟨x, hx, h⟩ := h
  exact ⟨x, hs x hx, h⟩

/-- a `SegOut` answer whose leaves bound is replaced by a super-list. -/
def SegOut.weaken {Γ : LCtx} {A B A' B' : Expr Nat} {L L' : List (Jd E n)}
    (hsub : ∀ x ∈ L, x ∈ L')
    (r : SegOut R Γ A B A' B' L) : SegOut R Γ A B A' B' L' :=
  ⟨r.1, r.2.1, r.2.2.1,
   fun ℓ hℓ => Below_of_subset (r.2.2.2.1 ℓ hℓ) hsub,
   fun C hC ℓ hℓ => strict_of_strict_below (r.2.2.2.2.1 C hC ℓ hℓ)
     (fun _ hx => Below_of_subset (below_of_mem hx) hsub),
   fun j hj => Below_of_subset (r.2.2.2.2.2.1 j hj) hsub,
   r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2⟩

/-- the `Below`-form bound widening (through `flattenCv_leaves`-style
    citation edges, not just membership). -/
def SegOut.weakenBelow {Γ : LCtx} {A B A' B' : Expr Nat}
    {L L' : List (Jd E n)} (hsub : ∀ x ∈ L, Below x L')
    (r : SegOut R Γ A B A' B' L) : SegOut R Γ A B A' B' L' :=
  ⟨r.1, r.2.1, r.2.2.1,
   fun ℓ hℓ => below_trans (r.2.2.2.1 ℓ hℓ) hsub,
   fun C hC ℓ hℓ => strict_of_strict_below (r.2.2.2.2.1 C hC ℓ hℓ) hsub,
   fun j hj => below_trans (r.2.2.2.2.2.1 j hj) hsub,
   r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2⟩

/-- weakening at depth `k` exposes through the whole segment output:
    the components by `XOut.wk`, the bound list unchanged (`wk` is
    leaf-free). -/
def SegOut.wk (d : LocalDecl) (k : Nat) {Γ₀ : LCtx}
    {P₁ P₂ Q₁ Q₂ : Expr Nat} {L : List (Jd E n)}
    (r : SegOut R Γ₀ P₁ P₂ Q₁ Q₂ L) :
    SegOut R (insertAt d k Γ₀) (lift k 1 P₁) (lift (k + 1) 1 P₂)
      (lift k 1 Q₁) (lift (k + 1) 1 Q₂) L := by
  obtain ⟨o, cs, js, h1, h2, h3, h4, h5⟩ := r
  exact ⟨o.wk d k, cs, js,
    fun ℓ hℓ => h1 ℓ (XOut.wk_leaves d k o ▸ hℓ), h2, h3, h4, h5⟩

/-- `subst0` at `j` exposes through the whole segment output: the
    components by `XOut.subst0`; every output leaf is a bound leaf or a
    substituent leaf (`XOut.subst0_leaves`), and the substituent's
    leaves are bound by `hhv` — the `+ hv.leaves` the esub link
    carries. -/
def SegOut.subst0 {Γ₀ : LCtx} {P₁ P₂ Q₁ Q₂ t v : Expr Nat} (j : Nat)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t))
    {L L' : List (Jd E n)} (hsub : ∀ x ∈ L, Below x L')
    (hhv : ∀ x ∈ hv.leaves, Below x L')
    (r : SegOut R Γ₀ P₁ P₂ Q₁ Q₂ L) :
    SegOut R (substRemove v j Γ₀)
      (instantiate j (lift 0 j v) P₁)
      (instantiate (j + 1) (lift 0 1 (lift 0 j v)) P₂)
      (instantiate j (lift 0 j v) Q₁)
      (instantiate (j + 1) (lift 0 1 (lift 0 j v)) Q₂) L' := by
  obtain ⟨o, cs, js, h1, h2, h3, h4, h5⟩ := r
  refine ⟨XOut.subst0 j hget hv o, cs, js, ?_,
    fun C hC ℓ hℓ => strict_of_strict_below (h2 C hC ℓ hℓ) hsub,
    fun j hj => below_trans (h3 j hj) hsub, h4, h5⟩
  intro ℓ hℓ
  rcases XOut.subst0_leaves j hget hv o hℓ with hℓ | hℓ
  · exact below_trans (h1 ℓ hℓ) hsub
  · exact hhv ℓ hℓ

/-- the `substLet` counterpart. -/
def SegOut.substLet {Γ₀ : LCtx} {P₁ P₂ Q₁ Q₂ t w₀ : Expr Nat} (j : Nat)
    (hget : Γ₀[j]? = some (.letBinding t w₀))
    (hv : EvTy R (substRemove w₀ j Γ₀) (lift 0 j w₀) (lift 0 j t))
    {L L' : List (Jd E n)} (hsub : ∀ x ∈ L, Below x L')
    (hhv : ∀ x ∈ hv.leaves, Below x L')
    (r : SegOut R Γ₀ P₁ P₂ Q₁ Q₂ L) :
    SegOut R (substRemove w₀ j Γ₀)
      (instantiate j (lift 0 j w₀) P₁)
      (instantiate (j + 1) (lift 0 1 (lift 0 j w₀)) P₂)
      (instantiate j (lift 0 j w₀) Q₁)
      (instantiate (j + 1) (lift 0 1 (lift 0 j w₀)) Q₂) L' := by
  obtain ⟨o, cs, js, h1, h2, h3, h4, h5⟩ := r
  refine ⟨XOut.substLet j hget hv o, cs, js, ?_,
    fun C hC ℓ hℓ => strict_of_strict_below (h2 C hC ℓ hℓ) hsub,
    fun j hj => below_trans (h3 j hj) hsub, h4, h5⟩
  intro ℓ hℓ
  rcases XOut.substLet_leaves j hget hv o hℓ with hℓ | hℓ
  · exact below_trans (h1 ℓ hℓ) hsub
  · exact hhv ℓ hℓ

/-! ### §4 the re-entry route

The global separation formerly stored in `X.hsep` is now the explicit
`hsep : SepAll E n` premise of this slice's route. It is passed unchanged
through recursive re-entry; no context or admission condition is weakened.
One invocation's supplier bundle is `X.atCtx hsep v` — the premise-free
`Suppliers` at the CURRENT context (J/D conditioned on `v` inside the
`…ViaSP` fronts).  Every W-admissible segment is #7257's route verbatim
(`xSegSViaS`); only a lone `bLinkS`-but-not-`bLinkW` link takes the new
arm.  The `symm` flag on `xCvS` defers the direction choice to the
`esub` node, where `reentryCv`'s both-directions check lets either
orientation re-enter; `reenterCvS`/`reenterTcS` re-run the whole
segment route on the re-flattened inner chain, at its SOURCE context
(`v.sub`/`v.subLet`).  Mutual recursion on `(wt, sizeOf)` of the
structural argument; the re-entry helpers pay `+1` on `wt` exactly as
the admission helpers do.

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/

/-- lex decrease for the route: first component `≤`, second `<`. -/
theorem lexNat_of_le {a c : Nat} {b d : Nat} (h : a ≤ c) (h2 : b < d) :
    Prod.Lex (fun x y => x < y) (fun x y => x < y) (a, b) (c, d) := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact Prod.Lex.left _ _ h
  · subst h; exact Prod.Lex.right _ h2

set_option maxHeartbeats 800000 in
mutual

/-- X on the segments under the S fragment — `xSegsViaS` with the S
    admissions and the substitution re-entries.

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def xSegsSS (X : SuppliersViaS E n) (hsep : SepAll E n) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ' : LCtx} (v : CtxWfViaS E n Γ') :
    {P Q : Expr Nat} → (s : Segs R Γ' P Q) → s.admS = true →
    ∀ {A B A' B' : Expr Nat}, P = .pi A B → Q = .pi A' B' →
    Option (SegOut R Γ' A B A' B' s.leaves)
  | _, _, .nil _, _, A, B, A', B', hP, hQ =>
      have e : (Expr.pi A B : Expr Nat) = .pi A' B' := hP.symm.trans hQ
      some (SegOut.ofA (EvTc.cast rfl rfl (Expr.pi.inj e).1 (.refl _ _),
        EvTc.cast rfl rfl (Expr.pi.inj e).2 (.refl _ _)) (fun ℓ hℓ => by
          simp only [XOut.leaves, EvTc.cast_leaves, EvTc.leaves,
            List.append_nil, List.not_mem_nil] at hℓ))
  | _, _, @Segs.cons _ _ _ _ P M Q p hM rest, hadm, A, B, A', B', hP, hQ =>
      have h' : p.segAdmS = true ∧ rest.admS = true := by
        simpa only [Segs.admS, Bool.and_eq_true] using hadm
      match isPiD M hM with
      | ⟨A₁, B₁, hM'⟩ =>
          match xSegSS X hsep hcl hinst v p h'.1 hP hM',
              xSegsSS X hsep hcl hinst v rest h'.2 hM' hQ with
          | some r₁, some r₂ =>
              some (SegOut.cast rfl (SegOut.comp (X.atCtx hsep v) r₁ r₂))
          | _, _ => none
termination_by P Q s hadm A B A' B' hP hQ => (s.wt, sizeOf s)
decreasing_by
  all_goals (try subst_vars)
  all_goals simp only [EvCv.wt, EvTc.wt, Flat.wt, Segs.wt, EvCv.castIdx_wt,
      Flat.symm_wt, flattenCv_wt, flattenTc_wt, Flat.segment_wt]
  all_goals (simp_wf; try omega)
  all_goals (first
    | (exact Prod.Lex.left _ _ (by omega))
    | (exact Prod.Lex.right _ (by omega))
    | (exact lexNat_of_le (by omega) (by omega)))

/-- X on one segment under the S fragment: a W-admissible segment is
    #7257's route verbatim; only a lone `bLinkS`-but-not-`bLinkW` link
    re-enters (`xLinkS`).

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def xSegSS (X : SuppliersViaS E n) (hsep : SepAll E n) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ' : LCtx} (v : CtxWfViaS E n Γ') :
    {P M : Expr Nat} → (p : Flat R Γ' P M) → p.segAdmS = true →
    ∀ {A B A' B' : Expr Nat}, P = .pi A B → M = .pi A' B' →
    Option (SegOut R Γ' A B A' B' p.leaves)
  | _, _, .nil _, _, A, B, A', B', hP, hM =>
      have e : (Expr.pi A B : Expr Nat) = .pi A' B' := hP.symm.trans hM
      some (SegOut.ofA (EvTc.cast rfl rfl (Expr.pi.inj e).1 (.refl _ _),
        EvTc.cast rfl rfl (Expr.pi.inj e).2 (.refl _ _)) (fun ℓ hℓ => by
          simp only [XOut.leaves, EvTc.cast_leaves, EvTc.leaves,
            List.append_nil, List.not_mem_nil] at hℓ))
  | _, _, .cons l hl (.nil _), hadm, A, B, A', B', hP, hM => by
      if hW : (Flat.cons l hl (.nil _)).segAdmW = true then
        exact xSegSViaS (X.atCtx hsep v) X.J X.hJ v _ hW hP hM
      else
        have hWf : piSpinedTc l = false ∧ bLinkW l = false := by
          have h' := hW
          simp only [Flat.segAdmW] at h'
          cases hh : piSpinedTc l with
          | true => simp_all
          | false =>
              cases hh2 : bLinkW l with
              | true => simp_all
              | false => exact ⟨rfl, rfl⟩
        have hbS : bLinkS l = true := by
          have h' : (piSpinedTc l || bLinkS l) = true := by
            simpa only [Flat.segAdmS] using hadm
          simpa only [hWf.1, Bool.false_or] using h'
        match xLinkS X hsep hcl hinst l v hbS hWf.2 hP hM with
        | none => exact none
        | some r =>
            exact some (SegOut.cast (by simp only [Flat.leaves,
              List.append_nil]) r)
  | _, _, .cons l hl (.cons l' hl' rest'), hadm, A, B, A', B', hP, hM => by
      have hW : (Flat.cons l hl (Flat.cons l' hl' rest')).segAdmW = true := by
        simpa only [Flat.segAdmS, Flat.segAdmW] using hadm
      exact xSegSViaS (X.atCtx hsep v) X.J X.hJ v _ hW hP hM
termination_by P M p hadm A B A' B' hP hM => (p.wt, sizeOf p)
decreasing_by
  all_goals (try subst_vars)
  all_goals simp only [EvCv.wt, EvTc.wt, Flat.wt, Segs.wt, EvCv.castIdx_wt,
      Flat.symm_wt, flattenCv_wt, flattenTc_wt, Flat.segment_wt]
  all_goals (simp_wf; try omega)
  all_goals (first
    | (exact Prod.Lex.left _ _ (by omega))
    | (exact Prod.Lex.right _ (by omega))
    | (exact lexNat_of_le (by omega) (by omega)))

/-- one non-W link: `ofCv` goes to `xCvS`; `wk` descends under
    `v.ins` and exposes through `SegOut.wk`; `subst0`/`substLet`
    re-enter the inner chain at the source context (`v.sub`/`v.subLet`)
    and expose through `SegOut.subst0`/`SegOut.substLet` — the context
    morphism is applied exactly once, to the exposed `XOut`, after the
    calls ran at the source.

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def xLinkS (X : SuppliersViaS E n) (hsep : SepAll E n) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) :
    {Γ' : LCtx} → {A B : Expr Nat} → (l : EvTc R Γ' A B) →
    (v : CtxWfViaS E n Γ') → bLinkS l = true → bLinkW l = false →
    ∀ {P₁ P₂ Q₁ Q₂ : Expr Nat}, A = .pi P₁ P₂ → B = .pi Q₁ Q₂ →
    Option (SegOut R Γ' P₁ P₂ Q₁ Q₂ l.leaves)
  | _, _, _, .ofCv u c, v, hbS, hbW, _, _, _, _, hP, hM =>
      xCvS X hsep hcl hinst false c v (by simpa only [bLinkS] using hbS)
        (by simpa only [bLinkW] using hbW) hP hM
  | _, _, _, @EvTc.wk _ _ _ Γ₀ A₀ B₀ d k l₀, v, hbS, hbW,
      P₁, P₂, Q₁, Q₂, hP, hM => by
      have hbS' : bLinkS l₀ = true := by simpa only [bLinkS] using hbS
      have hbW' : bLinkW l₀ = false := by simpa only [bLinkW] using hbW
      have hpiA : isPi A₀ = true := by
        rw [← isPi_lift k 1 A₀, hP]; rfl
      have hpiB : isPi B₀ = true := by
        rw [← isPi_lift k 1 B₀, hM]; rfl
      obtain ⟨a₁, a₂, hA₀⟩ := isPiD A₀ hpiA
      obtain ⟨b₁, b₂, hB₀⟩ := isPiD B₀ hpiB
      have eP : Expr.pi (lift k 1 a₁) (lift (k + 1) 1 a₂) = .pi P₁ P₂ :=
        (congrArg (lift k 1) hA₀).symm.trans hP
      have eM : Expr.pi (lift k 1 b₁) (lift (k + 1) 1 b₂) = .pi Q₁ Q₂ :=
        (congrArg (lift k 1) hB₀).symm.trans hM
      obtain ⟨e₁, e₂⟩ := Expr.pi.inj eP
      obtain ⟨e₃, e₄⟩ := Expr.pi.inj eM
      subst e₁; subst e₂; subst e₃; subst e₄
      exact (xLinkS X hsep hcl hinst l₀ (v.ins d k) hbS' hbW' hA₀ hB₀).map
        (fun r => SegOut.cast rfl (SegOut.wk d k r))
  | _, _, _, @EvTc.subst0 _ _ _ Γ₀ A₀ A₀' t v' j c hget hv, v, hbS, _,
      P₁, P₂, Q₁, Q₂, hP, hM => by
      have hr : reentryTc c = true := by simpa only [bLinkS] using hbS
      match reenterTcS X hsep hcl hinst
          (v.sub j hget (hv.val hcl hinst)) c hr with
      | none => exact none
      | some ⟨a₁, a₂, b₁, b₂, hA₀, hB₀, r⟩ =>
          have eP : Expr.pi (instantiate j (lift 0 j v') a₁)
              (instantiate (j + 1) (lift 0 1 (lift 0 j v')) a₂)
              = .pi P₁ P₂ :=
            (congrArg (instantiate j (lift 0 j v')) hA₀).symm.trans hP
          have eM : Expr.pi (instantiate j (lift 0 j v') b₁)
              (instantiate (j + 1) (lift 0 1 (lift 0 j v')) b₂)
              = .pi Q₁ Q₂ :=
            (congrArg (instantiate j (lift 0 j v')) hB₀).symm.trans hM
          obtain ⟨e₁, e₂⟩ := Expr.pi.inj eP
          obtain ⟨e₃, e₄⟩ := Expr.pi.inj eM
          subst e₁; subst e₂; subst e₃; subst e₄
          exact some (SegOut.subst0 j hget hv
            (fun x hx => below_left (below_of_mem hx))
            (fun x hx => below_right (below_of_mem hx)) r)
  | _, _, _, @EvTc.substLet _ _ _ Γ₀ A₀ A₀' t w₀ j c hget hv, v, hbS, _,
      P₁, P₂, Q₁, Q₂, hP, hM => by
      have hr : reentryTc c = true := by simpa only [bLinkS] using hbS
      match reenterTcS X hsep hcl hinst
          (v.subLet j hget (hv.val hcl hinst)) c hr with
      | none => exact none
      | some ⟨a₁, a₂, b₁, b₂, hA₀, hB₀, r⟩ =>
          have eP : Expr.pi (instantiate j (lift 0 j w₀) a₁)
              (instantiate (j + 1) (lift 0 1 (lift 0 j w₀)) a₂)
              = .pi P₁ P₂ :=
            (congrArg (instantiate j (lift 0 j w₀)) hA₀).symm.trans hP
          have eM : Expr.pi (instantiate j (lift 0 j w₀) b₁)
              (instantiate (j + 1) (lift 0 1 (lift 0 j w₀)) b₂)
              = .pi Q₁ Q₂ :=
            (congrArg (instantiate j (lift 0 j w₀)) hB₀).symm.trans hM
          obtain ⟨e₁, e₂⟩ := Expr.pi.inj eP
          obtain ⟨e₃, e₄⟩ := Expr.pi.inj eM
          subst e₁; subst e₂; subst e₃; subst e₄
          exact some (SegOut.substLet j hget hv
            (fun x hx => below_left (below_of_mem hx))
            (fun x hx => below_right (below_of_mem hx)) r)
  | _, _, _, .lit .., _, hbS, _, _, _, _, _, _, _ => by
      exact absurd hbS (by simp only [bLinkS]; decide)
  | _, _, _, .refl .., _, hbS, _, _, _, _, _, _, _ => by
      exact absurd hbS (by simp only [bLinkS]; decide)
  | _, _, _, .symm .., _, hbS, _, _, _, _, _, _, _ => by
      exact absurd hbS (by simp only [bLinkS]; decide)
  | _, _, _, .trans .., _, hbS, _, _, _, _, _, _, _ => by
      exact absurd hbS (by simp only [bLinkS]; decide)
  | _, _, _, .piCod .., _, hbS, _, _, _, _, _, _, _ => by
      exact absurd hbS (by simp only [bLinkS]; decide)
termination_by Γ' A B l v hbS hbW P₁ P₂ Q₁ Q₂ hP hM => (l.wt, sizeOf l)
decreasing_by
  all_goals (try subst_vars)
  all_goals simp only [EvCv.wt, EvTc.wt, Flat.wt, Segs.wt, EvCv.castIdx_wt,
      Flat.symm_wt, flattenCv_wt, flattenTc_wt, Flat.segment_wt]
  all_goals (simp_wf; try omega)
  all_goals (try trace_state)
  all_goals (first
    | (exact Prod.Lex.left _ _ (by omega))
    | (exact Prod.Lex.right _ (by omega))
    | (exact lexNat_of_le (by omega) (by omega)))

/-- a cv chain under the S fragment, with the `symm` parity deferred:
    under `flag = true` the output is for the swapped problem, realized
    at the `esub` node by re-entering on the backward-checked direction
    (K is not call-free for the census, so `symm` may not post-swap).

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def xCvS (X : SuppliersViaS E n) (hsep : SepAll E n) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) (flag : Bool) :
    {Γ' : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ' a b T) →
    (v : CtxWfViaS E n Γ') → bCvS c = true → bCvW c = false →
    ∀ {P₁ P₂ Q₁ Q₂ : Expr Nat}, a = .pi P₁ P₂ → b = .pi Q₁ Q₂ →
    Option (SegOut R Γ'
      (if flag then Q₁ else P₁) (if flag then Q₂ else P₂)
      (if flag then P₁ else Q₁) (if flag then P₂ else Q₂) c.leaves)
  | _, _, _, _, .lit .., _, _, hbW, _, _, _, _, _, _ => by
      exact absurd hbW (by simp only [bCvW]; decide)
  | _, _, _, _, .refl .., _, _, hbW, _, _, _, _, _, _ => by
      exact absurd hbW (by simp only [bCvW]; decide)
  | _, _, _, _, .symm c₀, v, hbS, hbW, P₁, P₂, Q₁, Q₂, hP, hM => by
      cases flag with
      | true =>
          exact xCvS X hsep hcl hinst false c₀ v
            (by simpa only [bCvS] using hbS)
            (by simpa only [bCvW] using hbW) hM hP
      | false =>
          exact xCvS X hsep hcl hinst true c₀ v
            (by simpa only [bCvS] using hbS)
            (by simpa only [bCvW] using hbW) hM hP
  | _, _, _, _, .trans c₁ c₂, _, hbS, hbW, _, _, _, _, _, _ => by
      have h' : bCvW (EvCv.trans c₁ c₂) = true := by
        simpa only [bCvS, bCvW] using hbS
      rw [h'] at hbW
      exact Bool.noConfusion hbW
  | _, _, _, _, .tyConv u' c₀ cA, v, hbS, hbW, _, _, _, _, hP, hM => by
      exact (xCvS X hsep hcl hinst flag c₀ v
        (by simpa only [bCvS] using hbS)
        (by simpa only [bCvW] using hbW) hP hM).map
        (fun r => SegOut.weakenBelow
          (fun x hx => below_left (below_of_mem hx)) r)
  | _, _, _, _, .rety c₀ cA, v, hbS, hbW, _, _, _, _, hP, hM => by
      exact (xCvS X hsep hcl hinst flag c₀ v
        (by simpa only [bCvS] using hbS)
        (by simpa only [bCvW] using hbW) hP hM).map
        (fun r => SegOut.weakenBelow
          (fun x hx => below_left (below_of_mem hx)) r)
  | _, _, _, _, @EvCv.wk _ _ _ Γ₀ a₀ b₀ T₀ d k c₀, v, hbS, hbW,
      P₁, P₂, Q₁, Q₂, hP, hM => by
      have hbS' : bCvS c₀ = true := by simpa only [bCvS] using hbS
      have hbW' : bCvW c₀ = false := by simpa only [bCvW] using hbW
      have hpiA : isPi a₀ = true := by
        rw [← isPi_lift k 1 a₀, hP]; rfl
      have hpiB : isPi b₀ = true := by
        rw [← isPi_lift k 1 b₀, hM]; rfl
      obtain ⟨a₁, a₂, hA₀⟩ := isPiD a₀ hpiA
      obtain ⟨b₁, b₂, hB₀⟩ := isPiD b₀ hpiB
      have eP : Expr.pi (lift k 1 a₁) (lift (k + 1) 1 a₂) = .pi P₁ P₂ :=
        (congrArg (lift k 1) hA₀).symm.trans hP
      have eM : Expr.pi (lift k 1 b₁) (lift (k + 1) 1 b₂) = .pi Q₁ Q₂ :=
        (congrArg (lift k 1) hB₀).symm.trans hM
      obtain ⟨e₁, e₂⟩ := Expr.pi.inj eP
      obtain ⟨e₃, e₄⟩ := Expr.pi.inj eM
      subst e₁; subst e₂; subst e₃; subst e₄
      cases flag with
      | false =>
          exact (xCvS X hsep hcl hinst false c₀ (v.ins d k) hbS' hbW' hA₀ hB₀).map
            (fun r => SegOut.cast rfl (SegOut.wk d k r))
      | true =>
          exact (xCvS X hsep hcl hinst true c₀ (v.ins d k) hbS' hbW' hA₀ hB₀).map
            (fun r => SegOut.cast rfl (SegOut.wk d k r))
  | _, _, _, _, @EvCv.esub _ _ _ Γ₀ a₀ b₀ T₀ t v' j u ci hget hv hvT,
      v, hbS, _, P₁, P₂, Q₁, Q₂, hP, hM => by
      have hr : reentryCv ci = true := by simpa only [bCvS] using hbS
      match reenterCvS X hsep hcl hinst
          (v.sub j hget (hv.val hcl hinst)) flag ci hr with
      | none => exact none
      | some ⟨a₁, a₂, b₁, b₂, hA₀, hB₀, r⟩ =>
          have eP : Expr.pi (instantiate j (lift 0 j v') a₁)
              (instantiate (j + 1) (lift 0 1 (lift 0 j v')) a₂)
              = .pi P₁ P₂ :=
            (congrArg (instantiate j (lift 0 j v')) hA₀).symm.trans hP
          have eM : Expr.pi (instantiate j (lift 0 j v') b₁)
              (instantiate (j + 1) (lift 0 1 (lift 0 j v')) b₂)
              = .pi Q₁ Q₂ :=
            (congrArg (instantiate j (lift 0 j v')) hB₀).symm.trans hM
          obtain ⟨e₁, e₂⟩ := Expr.pi.inj eP
          obtain ⟨e₃, e₄⟩ := Expr.pi.inj eM
          subst e₁; subst e₂; subst e₃; subst e₄
          cases flag <;>
            exact some (SegOut.subst0 j hget hv
              (fun x hx => below_left (below_left (below_of_mem hx)))
              (fun x hx => below_left (below_right (below_of_mem hx)))
              r)
  | _, _, _, _, @EvCv.subst0 _ _ _ Γ₀ a₀ b₀ T₀ t v' j ci hget hv,
      v, hbS, _, P₁, P₂, Q₁, Q₂, hP, hM => by
      have hr : reentryCv ci = true := by simpa only [bCvS] using hbS
      match reenterCvS X hsep hcl hinst
          (v.sub j hget (hv.val hcl hinst)) flag ci hr with
      | none => exact none
      | some ⟨a₁, a₂, b₁, b₂, hA₀, hB₀, r⟩ =>
          have eP : Expr.pi (instantiate j (lift 0 j v') a₁)
              (instantiate (j + 1) (lift 0 1 (lift 0 j v')) a₂)
              = .pi P₁ P₂ :=
            (congrArg (instantiate j (lift 0 j v')) hA₀).symm.trans hP
          have eM : Expr.pi (instantiate j (lift 0 j v') b₁)
              (instantiate (j + 1) (lift 0 1 (lift 0 j v')) b₂)
              = .pi Q₁ Q₂ :=
            (congrArg (instantiate j (lift 0 j v')) hB₀).symm.trans hM
          obtain ⟨e₁, e₂⟩ := Expr.pi.inj eP
          obtain ⟨e₃, e₄⟩ := Expr.pi.inj eM
          subst e₁; subst e₂; subst e₃; subst e₄
          cases flag <;>
            exact some (SegOut.subst0 j hget hv
              (fun x hx => below_left (below_of_mem hx))
              (fun x hx => below_right (below_of_mem hx)) r)
  | _, _, _, _, @EvCv.substLet _ _ _ Γ₀ a₀ b₀ T₀ t w₀ j ci hget hv,
      v, hbS, _, P₁, P₂, Q₁, Q₂, hP, hM => by
      have hr : reentryCv ci = true := by simpa only [bCvS] using hbS
      match reenterCvS X hsep hcl hinst
          (v.subLet j hget (hv.val hcl hinst)) flag ci hr with
      | none => exact none
      | some ⟨a₁, a₂, b₁, b₂, hA₀, hB₀, r⟩ =>
          have eP : Expr.pi (instantiate j (lift 0 j w₀) a₁)
              (instantiate (j + 1) (lift 0 1 (lift 0 j w₀)) a₂)
              = .pi P₁ P₂ :=
            (congrArg (instantiate j (lift 0 j w₀)) hA₀).symm.trans hP
          have eM : Expr.pi (instantiate j (lift 0 j w₀) b₁)
              (instantiate (j + 1) (lift 0 1 (lift 0 j w₀)) b₂)
              = .pi Q₁ Q₂ :=
            (congrArg (instantiate j (lift 0 j w₀)) hB₀).symm.trans hM
          obtain ⟨e₁, e₂⟩ := Expr.pi.inj eP
          obtain ⟨e₃, e₄⟩ := Expr.pi.inj eM
          subst e₁; subst e₂; subst e₃; subst e₄
          cases flag <;>
            exact some (SegOut.substLet j hget hv
              (fun x hx => below_left (below_of_mem hx))
              (fun x hx => below_right (below_of_mem hx)) r)
  | _, _, _, _, .sorts .., _, hbS, _, _, _, _, _, _, _ => by
      exact absurd hbS (by simp only [bCvS]; decide)
  | _, _, _, _, .consts .., _, hbS, _, _, _, _, _, _, _ => by
      exact absurd hbS (by simp only [bCvS]; decide)
termination_by Γ' a b T c v hbS hbW P₁ P₂ Q₁ Q₂ hP hM => (c.wt, sizeOf c)
decreasing_by
  all_goals (try subst_vars)
  all_goals simp only [EvCv.wt, EvTc.wt, Flat.wt, Segs.wt, EvCv.castIdx_wt,
      Flat.symm_wt, flattenCv_wt, flattenTc_wt, Flat.segment_wt]
  all_goals (simp_wf; try omega)
  all_goals (first
    | (exact Prod.Lex.left _ _ (by omega))
    | (exact Prod.Lex.right _ (by omega))
    | (exact lexNat_of_le (by omega) (by omega)))

/-- the cv re-entry: the inner index's `.sort u` shape, both `isPi`
    checks, and the two directions' segment admissions extracted from
    the admission's own tests; `flag` picks the forward (`hb`-segment)
    or the backward (`ha`-segment) direction.

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def reenterCvS (X : SuppliersViaS E n) (hsep : SepAll E n) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ₀ : LCtx} (v₀ : CtxWfViaS E n Γ₀)
    (flag : Bool) :
    {a₀ b₀ T₀ : Expr Nat} → (ci : EvCv R Γ₀ a₀ b₀ T₀) →
    reentryCv ci = true →
    Option (Σ' (P₁ P₂ Q₁ Q₂ : Expr Nat) (_ : a₀ = .pi P₁ P₂)
      (_ : b₀ = .pi Q₁ Q₂), SegOut R Γ₀
        (if flag then Q₁ else P₁) (if flag then Q₂ else P₂)
        (if flag then P₁ else Q₁) (if flag then P₂ else Q₂)
        ci.leaves)
  | a₀, b₀, .sort u, ci, hadm => by
      have hb : isPi b₀ = true := by
        obtain ⟨_, _, hb, _, _, _⟩ := reentryCv_spec ci hadm; exact hb
      have ha : isPi a₀ = true := by
        obtain ⟨_, _, _, ha, _, _⟩ := reentryCv_spec ci hadm; exact ha
      have hF : ((flattenCv u (EvCv.castIdx rfl ci) rfl).segment hb).admS
          = true := by
        obtain ⟨u', hT', hb', _, hs1, _⟩ := reentryCv_spec ci hadm
        injection hT' with hu
        subst u'
        have e1 : EvCv.castIdx hT' ci = EvCv.castIdx rfl ci := by
          rw [Subsingleton.elim hT' rfl]
        have e2 : (flattenCv u (EvCv.castIdx hT' ci) rfl).segment hb' =
            (flattenCv u (EvCv.castIdx rfl ci) rfl).segment hb := by
          rw [e1, Subsingleton.elim hb' hb]
        rwa [e2] at hs1
      have hB : ((flattenCv u ((EvCv.castIdx rfl ci).symm) rfl).segment ha).admS
          = true := by
        obtain ⟨u', hT', _, ha', _, hs2⟩ := reentryCv_spec ci hadm
        injection hT' with hu
        subst u'
        have e1 : EvCv.castIdx hT' ci = EvCv.castIdx rfl ci := by
          rw [Subsingleton.elim hT' rfl]
        have e2 : (flattenCv u ((EvCv.castIdx hT' ci).symm) rfl).segment ha' =
            (flattenCv u ((EvCv.castIdx rfl ci).symm) rfl).segment ha := by
          rw [e1, Subsingleton.elim ha' ha]
        rwa [e2] at hs2
      obtain ⟨P₁, P₂, hP⟩ := isPiD a₀ ha
      obtain ⟨Q₁, Q₂, hQ⟩ := isPiD b₀ hb
      cases flag with
      | true =>
          match xSegsSS X hsep hcl hinst v₀
              ((flattenCv u ((EvCv.castIdx rfl ci).symm) rfl).segment ha)
              hB hQ hP with
          | none => exact none
          | some r =>
              refine some ⟨P₁, P₂, Q₁, Q₂, hP, hQ, SegOut.weakenBelow ?_ r⟩
              intro x hx
              apply below_of_mem
              have hx' := flattenCv_leaves u ((EvCv.castIdx rfl ci).symm) rfl x
                (Flat.segment_leaves _ ha ▸ hx)
              rw [← EvCv.castIdx_leaves rfl ci]
              exact hx'
      | false =>
          match xSegsSS X hsep hcl hinst v₀
              ((flattenCv u (EvCv.castIdx rfl ci) rfl).segment hb)
              hF hP hQ with
          | none => exact none
          | some r =>
              refine some ⟨P₁, P₂, Q₁, Q₂, hP, hQ, SegOut.weakenBelow ?_ r⟩
              intro x hx
              apply below_of_mem
              have hx' := flattenCv_leaves u (EvCv.castIdx rfl ci) rfl x
                (Flat.segment_leaves _ hb ▸ hx)
              rw [← EvCv.castIdx_leaves rfl ci]
              exact hx'
  | _, _, .bvar _, ci, hadm => by
      exact absurd hadm (by
        intro h; obtain ⟨_, hT, _, _, _, _⟩ := reentryCv_spec ci h
        exact Expr.noConfusion hT)
  | _, _, .const _ _, ci, hadm => by
      exact absurd hadm (by
        intro h; obtain ⟨_, hT, _, _, _, _⟩ := reentryCv_spec ci h
        exact Expr.noConfusion hT)
  | _, _, .app _ _, ci, hadm => by
      exact absurd hadm (by
        intro h; obtain ⟨_, hT, _, _, _, _⟩ := reentryCv_spec ci h
        exact Expr.noConfusion hT)
  | _, _, .lam _ _, ci, hadm => by
      exact absurd hadm (by
        intro h; obtain ⟨_, hT, _, _, _, _⟩ := reentryCv_spec ci h
        exact Expr.noConfusion hT)
  | _, _, .pi _ _, ci, hadm => by
      exact absurd hadm (by
        intro h; obtain ⟨_, hT, _, _, _, _⟩ := reentryCv_spec ci h
        exact Expr.noConfusion hT)
  | _, _, .letE _ _ _, ci, hadm => by
      exact absurd hadm (by
        intro h; obtain ⟨_, hT, _, _, _, _⟩ := reentryCv_spec ci h
        exact Expr.noConfusion hT)
  | _, _, .lit _, ci, hadm => by
      exact absurd hadm (by
        intro h; obtain ⟨_, hT, _, _, _, _⟩ := reentryCv_spec ci h
        exact Expr.noConfusion hT)
termination_by a₀ b₀ T₀ ci hadm => (1 + ci.wt, sizeOf ci)
decreasing_by
  all_goals (try subst_vars)
  all_goals simp only [EvCv.wt, EvTc.wt, Flat.wt, Segs.wt, EvCv.castIdx_wt, Flat.symm_wt, flattenCv_wt, Flat.segment_wt]
  all_goals (simp_wf; try omega)
  all_goals (first | (exact Prod.Lex.left _ _ (by omega)) | (exact Prod.Lex.right _ (by omega)) | (exact lexNat_of_le (by omega) (by omega)))

/-- the link re-entry: the inner chain's `isPi` endpoints extracted,
    re-segmented, run by `xSegsSS` at the source context.

    PR-B fold-in (#7145): EvCv.subst0/substLet arms = the esub arm;
    EvParStar/Valley.subst0 wrappers in thinDeep wrap lazily -/
def reenterTcS (X : SuppliersViaS E n) (hsep : SepAll E n) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ₀ : LCtx} (v₀ : CtxWfViaS E n Γ₀) :
    {A B : Expr Nat} → (c : EvTc R Γ₀ A B) → reentryTc c = true →
    Option (Σ' (P₁ P₂ Q₁ Q₂ : Expr Nat) (_ : A = .pi P₁ P₂)
      (_ : B = .pi Q₁ Q₂), SegOut R Γ₀ P₁ P₂ Q₁ Q₂ c.leaves)
  | A, B, c, hadm => by
    have hB : isPi B = true := by
      obtain ⟨hB, _, _⟩ := reentryTc_spec c hadm; exact hB
    have hA : isPi A = true := by
      obtain ⟨_, hA, _⟩ := reentryTc_spec c hadm; exact hA
    have hs : ((flattenTc c).segment hB).admS = true := by
      obtain ⟨hB', _, hs'⟩ := reentryTc_spec c hadm
      have e : (flattenTc c).segment hB' = (flattenTc c).segment hB := by
        rw [Subsingleton.elim hB' hB]
      rwa [e] at hs'
    obtain ⟨P₁, P₂, hP⟩ := isPiD A hA
    obtain ⟨Q₁, Q₂, hQ⟩ := isPiD B hB
    exact (xSegsSS X hsep hcl hinst v₀ ((flattenTc c).segment hB) hs hP hQ).map
      (fun r => ⟨P₁, P₂, Q₁, Q₂, hP, hQ, SegOut.weakenBelow (fun x hx =>
        below_trans (flattenTc_leaves c x (Flat.segment_leaves _ hB ▸ hx))
          (fun y hy => below_of_mem hy)) r⟩)
termination_by A B c hadm => (1 + c.wt, sizeOf c)
decreasing_by
  all_goals (try subst_vars)
  all_goals simp only [EvCv.wt, EvTc.wt, Flat.wt, Segs.wt, flattenTc_wt, Flat.segment_wt]
  all_goals (simp_wf; try omega)
  all_goals (first | (exact Prod.Lex.left _ _ (by omega)) | (exact Prod.Lex.right _ (by omega)) | (exact lexNat_of_le (by omega) (by omega)))

end

/-- the W-X-SUBST slice-2 entry point: `flattenTc`-segment the input,
    admit each segment under `admS`, run the segment route, and weaken
    the segment census bound to the input's own leaves (the flattened
    segment's leaves are a sub-census of `c`'s by `flattenTc_leaves`
    and `Flat.segment_leaves`). -/
def xValleySS? (X : SuppliersViaS E n) (hsep : SepAll E n) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} (v : CtxWfViaS E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmS c = true) :
    Option (SegOut R Γ A B A' B' c.leaves) :=
  (xSegsSS X hsep hcl hinst v ((flattenTc c).segment rfl) hadm rfl rfl).map
    (fun r => by
      obtain ⟨o, calls, jcalls, h1, h2, h3, h4, h5⟩ := r
      rw [Flat.segment_leaves] at h1 h2 h3
      exact ⟨o, calls, jcalls, fun ℓ hℓ =>
          below_trans (h1 ℓ hℓ) (flattenTc_leaves c),
        fun C hC ℓ hℓ =>
          strict_of_strict_below (h2 C hC ℓ hℓ) (flattenTc_leaves c),
        fun j hj => below_trans (h3 j hj) (flattenTc_leaves c), h4, h5⟩)

/-- `XContractWf`'s clause for every answer of the slice-2 route. -/
theorem xValleySS_contract (X : SuppliersViaS E n) (hsep : SepAll E n) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} (v : CtxWfViaS E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmS c = true) (r : SegOut R Γ A B A' B' c.leaves)
    (_ : xValleySS? X hsep hcl hinst v c hadm = some r) :
    ∀ ℓ ∈ r.1.1.leaves ++ r.1.2.leaves, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  r.2.2.2.1

/-- the slice-2 route's answers carry the same lex-edge census as
    #7142's — `SegOut` is unchanged. -/
theorem xValleySS_edges (X : SuppliersViaS E n) (hsep : SepAll E n) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} (v : CtxWfViaS E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmS c = true) (r : SegOut R Γ A B A' B' c.leaves)
    (_ : xValleySS? X hsep hcl hinst v c hadm = some r) (Z : List (Jd E n)) :
    EdgeContractLex (census c r Z) :=
  census_edges c r Z

/-- on a W-admissible segment the S fragment's single-segment route
    IS #7257's ViaS route (the `segAdmW` branch). -/
theorem xSegSS_of_segAdmW (X : SuppliersViaS E n) (hsep : SepAll E n) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ' : LCtx} (v : CtxWfViaS E n Γ')
    {P M : Expr Nat} (p : Flat R Γ' P M) (hadmS : p.segAdmS = true)
    (hadmW : p.segAdmW = true) {A B A' B' : Expr Nat}
    (hP : P = .pi A B) (hM : M = .pi A' B') :
    xSegSS X hsep hcl hinst v p hadmS hP hM =
      xSegSViaS (X.atCtx hsep v) X.J X.hJ v p hadmW hP hM := by
  cases p with
  | nil _ => simp only [xSegSS, xSegSViaS, ViaSEngine.xSegSViaS]
  | cons l hl rest =>
      cases rest with
      | nil => simp only [xSegSS, dif_pos hadmW]
      | cons l' hl' rest' => simp only [xSegSS]

/-- on a W-admissible segmentation the S-fragment segment route IS
    #7257's ViaS route — every segment takes the `segAdmW` branch. -/
theorem xSegsSS_of_admW (X : SuppliersViaS E n) (hsep : SepAll E n) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ' : LCtx} (v : CtxWfViaS E n Γ') :
    {P Q : Expr Nat} → (s : Segs R Γ' P Q) → (hadmS : s.admS = true) →
    (hadmW : s.admW = true) →
    ∀ {A B A' B' : Expr Nat} (hP : P = .pi A B) (hQ : Q = .pi A' B'),
    xSegsSS X hsep hcl hinst v s hadmS hP hQ =
      xSegsViaS (X.atCtx hsep v) X.J X.hJ v s hadmW hP hQ
  | _, _, .nil _, _, _, A, B, A', B', hP, hQ => by
      rw [xSegsSS.eq_1, xSegsViaS, ViaSEngine.xSegsViaS.eq_1]
  | _, _, @Segs.cons _ _ _ _ P M Q p hM rest, hadmS, hadmW,
      A, B, A', B', hP, hQ => by
      obtain ⟨hp, hrest⟩ : p.segAdmW = true ∧ rest.admW = true := by
        simpa only [Segs.admW, Bool.and_eq_true] using hadmW
      rw [xSegsSS.eq_2, xSegsViaS, ViaSEngine.xSegsViaS.eq_2]
      generalize isPiD M hM = d
      cases d with
      | mk A₁ pB =>
          cases pB with
          | mk B₁ hM' =>
              dsimp only
              rw [xSegSS_of_segAdmW X hsep hcl hinst v p _ hp hP hM',
                xSegsSS_of_admW X hsep hcl hinst v rest _ hrest hM' hQ]
              rfl

/-- the W fragment is inside the S fragment at the route level too: on
    a W-admissible input the slice-2 route agrees with #7257's. -/
theorem xValleySS?_of_admW (X : SuppliersViaS E n) (hsep : SepAll E n) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) {Γ : LCtx} (v : CtxWfViaS E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hW : xAdmW c = true) :
    xValleySS? X hsep hcl hinst v c (xAdmS_of_xAdmW c hW) =
      xValleySViaS? (X.atCtx hsep v) X.J X.hJ v c hW := by
  simp only [xValleySS?, xValleySViaS?, ViaSEngine.xValleySViaS?]
  rw [xSegsSS_of_admW X hsep hcl hinst v _ _ hW rfl rfl]
  rfl

/-! ### §5 fixtures

The leaf/census teeth (T1, T3) run on `t1Chain`: a `subst0 0` link whose
inner chain is the `refl` literal at `piX` weakened into `[y : Sort 1]`
with `v := Sort 0` for `y` — leaf-level material identical to the
A1 probe's.  The admission teeth need the W route to *refuse*, which a
`refl` inner cannot do (`piSpinedTc` descends through `subst0` and
`refl` is spined), so `pin_subst0_beta_adm` and the nested/J pins run
on `betaSubChain`: the same `subst0` shape but with the probe's β
`trans`-through-`betaRedex` literal as the inner chain — Stratum-B under
W (not Π-spined), S-admitted via the `reentryTc` re-entry.  `subTyD`
(weight 7) is `conv`-padded so `subOf_wt_lt` alone refutes `Strict` for
T3 against every fixture leaf; `dBig` (weight 19) is T1's decoy typing
of the same type, heavier than every fixture atom and therefore never
`Below` the input's leaves. -/

/-- the depth-0 substitution target `[y : Sort 1]` of the fixtures. -/
abbrev ΓSub : LCtx := [.assumption (.sort (.succ .zero))]

/-- the substituent `v := Sort 0`. -/
abbrev subV : Expr Nat := .sort .zero

/-- the inner literal: `piX ≡ piX` at `sX` by `refl` of `pinPiTy` — its
    atom `.cv subConvRefl` has a single child `.ty pinPiTy`, so a J
    answer built from the literal has every leaf certified into any
    bundle containing the root. -/
def subConvRefl : ConvT emptyEnv 0 [] piX piX sX := .refl [] piX sX pinPiTy

/-- `Sort 1 ≡ Sort 1` at `Sort 2` — the conv child used to pad the
    stored typing's derivation (keeps `subTyD`'s atom off the literal's
    own sub-derivations). -/
def subConv11 : ConvT emptyEnv 0 [] (.sort (.succ .zero))
    (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .refl [] _ _ (.sort [] (.succ .zero))

/-- the stored substituent typing `Sort 0 : Sort 1`, `conv`-wrapped
    twice — weight `7`, at least as heavy as every other leaf of the
    fixtures, so `subOf_wt_lt` alone refutes `Strict` (T3); the `conv`
    nodes also keep the atom off `pinPiTy`'s own sub-derivations. -/
def subTyD : HasTyT emptyEnv 0 [] subV (.sort (.succ .zero)) :=
  .conv [] _ _ _ _ (.conv [] _ _ _ _ (.sort [] .zero) subConv11) subConv11

/-- T1's decoy: another typing of `subV` at `Sort 1`, six `conv`
    wrappers deep — weight `19`, heavier than every other leaf. -/
def dBig : HasTyT emptyEnv 0 [] subV (.sort (.succ .zero)) :=
  .conv [] _ _ _ _ (.conv [] _ _ _ _ (.conv [] _ _ _ _
    (.conv [] _ _ _ _ (.conv [] _ _ _ _ (.conv [] _ _ _ _
      (.sort [] .zero) subConv11) subConv11) subConv11) subConv11)
    subConv11) subConv11

/-- the fixture bundle: the inner literal's atom, the stored `hv` atom,
    and the decoy atom. -/
abbrev Rt1 : List (Jd emptyEnv 0) := [.cv subConvRefl, .ty subTyD, .ty dBig]

theorem mem_cv_subConvRefl : ∃ r ∈ Rt1, SubEq (.cv subConvRefl) r :=
  ⟨.cv subConvRefl, .head _, .inl rfl⟩

theorem mem_ty_subTyD : ∃ r ∈ Rt1, SubEq (.ty subTyD) r :=
  ⟨.ty subTyD, .tail _ (.head _), .inl rfl⟩

theorem mem_ty_dBig : ∃ r ∈ Rt1, SubEq (.ty dBig) r :=
  ⟨.ty dBig, .tail _ (.tail _ (.head _)), .inl rfl⟩

/-- the inner chain: the `refl` literal weakened into `[y : Sort 1]` —
    one `ofCv` link `piX ≡ piX`. -/
def t1Inner : EvTc Rt1 ΓSub piX piX :=
  .ofCv _ (.wk (.assumption (.sort (.succ .zero))) 0
    (.lit subConvRefl mem_cv_subConvRefl))

/-- the stored substituent typing, kept as a literal leaf. -/
def t1Hv : EvTy Rt1 [] subV (.sort (.succ .zero)) := .lit subTyD mem_ty_subTyD

/-- the decoy typing at the same type (T1's mutant writes this one). -/
def t1HvMut : EvTy Rt1 [] subV (.sort (.succ .zero)) := .lit dBig mem_ty_dBig

/-- the headline chain: one `subst0 0` link `piX ≡ piX` at `[]`. -/
def t1Chain : EvTc Rt1 [] piX piX := .subst0 (v := subV) 0 t1Inner rfl t1Hv

/-- the mutant writes the decoy typing where `hv` stood (T1's
    substitution exposure must take the stored one, not this). -/
def t1ChainMut : EvTc Rt1 [] piX piX :=
  .subst0 (v := subV) 0 t1Inner rfl t1HvMut

/-- the β fixture's bundle: the probe's `trans`-of-`β` literal atom, the
    stored `hv` atom, the decoy — the probe's `Rt1` verbatim. -/
abbrev RBeta : List (Jd emptyEnv 0) := [.tc betaMiddleT, .ty subTyD, .ty dBig]

/-- `piX ≡ betaRedex` (symm-β) and `betaRedex ≡ piX` (β) as literals,
    certified under the `betaMiddleT` root — the probe's certifications
    verbatim. -/
def betaSubCv₁ : EvCv RBeta [] piX betaRedex sX :=
  .lit (.symm [] betaRedex piX sX betaRedexConv)
    ⟨.tc betaMiddleT, .head _, .inr (.trans (.child (tcChildOf _))
      (.child (tcChildFst betaD₁ betaD₂)))⟩

def betaSubCv₂ : EvCv RBeta [] betaRedex piX sX :=
  .lit betaRedexConv ⟨.tc betaMiddleT, .head _,
    .inr (.trans (.child (tcChildOf _)) (.child (tcChildSnd betaD₁ betaD₂)))⟩

/-- the inner chain: the β `trans` weakened into `[y : Sort 1]` —
    `flattenCv` stops at the `wk` boundary (one link
    `ofCv (wk (trans lit lit))`), so the re-entry's segment is a single
    `bCvS`-checked link. -/
def betaSubInner : EvTc RBeta ΓSub piX piX :=
  .ofCv _ (.wk (.assumption (.sort (.succ .zero))) 0
    (.trans betaSubCv₁ betaSubCv₂))

/-- the stored substituent typing, kept as a literal leaf. -/
def betaSubHv : EvTy RBeta [] subV (.sort (.succ .zero)) :=
  .lit subTyD ⟨.ty subTyD, .tail _ (.head _), .inl rfl⟩

/-- the decoy typing at the same type (T1's mutant writes this one). -/
def betaSubHvMut : EvTy RBeta [] subV (.sort (.succ .zero)) :=
  .lit dBig ⟨.ty dBig, .tail _ (.tail _ (.head _)), .inl rfl⟩

/-- the discriminating fixture: `y : Sort 1 ↦ Sort 0` over the
    non-Π-spined inner — under W the lone link is refused; under S it
    re-enters at the source. -/
def betaSubChain : EvTc RBeta [] piX piX :=
  .subst0 (v := subV) 0 betaSubInner rfl betaSubHv

/-- the β fixture's leaf census: the two literal atoms, then the kept
    `hv` atom. -/
theorem pin_beta_leaves : betaSubChain.leaves =
    [.cv (.symm [] betaRedex piX sX betaRedexConv), .cv betaRedexConv,
      .ty subTyD] := rfl

/-- the headline pin: a substitution link is S-admitted (lone link,
    `reentryTc` passes on the inner segment) exactly where the W route
    refused it (`xAdmW` — not `bLinkW`, not Π-spined). -/
theorem pin_subst0_beta_adm :
    xAdmS betaSubChain = true ∧ xAdmW betaSubChain = false := by
  refine ⟨?_, by decide⟩
  simp only [xAdmS, admS, betaSubChain, betaSubInner, betaSubCv₁,
    betaSubCv₂, flattenTc, flattenCv, EvCv.castIdx, Flat.wk, Flat.append,
    Flat.symm, Flat.segment, Flat.segmentF, Flat.splitPi, Segs.admS,
    Flat.segAdmS, piSpinedTc, piSpinedCv, piSpinedConv, bLinkS,
    reentryTc, bCvS, bLinkW, bCvW, isPi]
  rfl

/-- a trivial `XOut` at the source context of the fixture — both
    components `refl` at `Sort 0`, so every exposed leaf is `hv`'s. -/
def oReflSub : XOut Rt1 ΓSub (.sort .zero) (.sort .zero) (.sort .zero)
    (.sort .zero) := (.refl _ _, .refl _ _)

/-! #### T1 — the exposure takes the stored `hv` -/

/-- the fixture's leaf census: the inner literal's atom, then the kept
    substituent's. -/
theorem pin_T1_leaves :
    t1Chain.leaves = [.cv subConvRefl, .ty subTyD] := rfl

/-- the stored typing's atom IS in the exposure — `XOut.subst0` cites
    `hv` once per component. -/
theorem pin_T1_kept_in_exposure :
    .ty subTyD ∈ XOut.leaves (XOut.subst0 (v := subV) 0 rfl t1Hv
      oReflSub) := by
  simp only [XOut.subst0, XOut.leaves, EvTc.leaves, EvTc.cast_leaves,
    substBinderArg_leaves, List.mem_append, t1Hv, EvTy.leaves,
    List.not_mem_nil, or_false, false_or, List.mem_singleton]
  exact Or.inl trivial

/-- the mutant stores the decoy and exposes its atom. -/
theorem pin_T1_mutant_exposes_decoy :
    .ty dBig ∈ XOut.leaves (XOut.subst0 (v := subV) 0 rfl t1HvMut
      oReflSub) := by
  simp only [XOut.subst0, XOut.leaves, EvTc.leaves, EvTc.cast_leaves,
    substBinderArg_leaves, List.mem_append, t1HvMut, EvTy.leaves,
    List.not_mem_nil, or_false, false_or, List.mem_singleton]
  exact Or.inl trivial

/-- the weights, computed: the decoy outweighs every fixture leaf. -/
theorem pin_T1_wts : Jd.wt (.cv subConvRefl) = 4 ∧ Jd.wt (.ty subTyD) = 7 ∧
    Jd.wt (.ty dBig) = 19 := ⟨rfl, rfl, rfl⟩

/-- the decoy atom is not below the input's leaves: `19 ≤ 4` fails for
    both — the mutant's exposure cannot satisfy the `Below` clause. -/
theorem pin_T1_mutant_wrong_hv_not_below :
    ¬ Below (.ty dBig) t1Chain.leaves := by
  rintro ⟨x, hx, hsub⟩
  have hle := subEq_wt_le hsub
  simp only [pin_T1_leaves, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact absurd hle (by decide)

/-- the contract clause the mutant violates: its exposure carries
    `.ty dBig`, which is not below the input. -/
theorem pin_T1_mutant_breaks_contract :
    ∃ ℓ ∈ XOut.leaves (XOut.subst0 (v := subV) 0 rfl t1HvMut oReflSub),
      ¬ ∃ ℓ' ∈ t1Chain.leaves, SubEq ℓ ℓ' :=
  ⟨.ty dBig, pin_T1_mutant_exposes_decoy, pin_T1_mutant_wrong_hv_not_below⟩

/-- while the honest exposure's kept atom IS below the input (it is an
    element of `t1Chain.leaves`). -/
theorem pin_T1_kept_below :
    Below (.ty subTyD) t1Chain.leaves :=
  ⟨.ty subTyD, by simp only [pin_T1_leaves, List.mem_cons,
      List.mem_singleton]; exact Or.inr (Or.inl trivial), .inl rfl⟩

/-! #### T3 — the kept atom is real -/

/-- the kept atom is in the SECOND component's leaves too — the codomain
    component's `substBinderArg` keeps `hv`'s leaves. -/
theorem pin_T3_kept_in_codomain :
    .ty subTyD ∈ ((XOut.subst0 (v := subV) 0 rfl t1Hv oReflSub).2).leaves := by
  simp only [XOut.subst0, EvTc.leaves, EvTc.cast_leaves,
    substBinderArg_leaves, List.mem_append, t1Hv, EvTy.leaves,
    List.not_mem_nil, or_false, List.mem_singleton]
  exact Or.inr trivial

/-- but the kept atom is not `Strict`: it is not `SubOf` any input leaf
    (`subOf_wt_lt` — `4 < 4` fails against both, and `SubOf` is
    irreflexive). -/
theorem pin_T3_kept_not_strict :
    ¬ Strict (.ty subTyD) t1Chain.leaves := by
  rintro ⟨x, hx, hsub⟩
  have hlt := subOf_wt_lt hsub
  simp only [pin_T1_leaves, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact absurd hlt (by decide)

/-! #### T4 — `[x_read_subst_var]`, decided at admission -/

/-- T4's bundle: `piX`'s typing atom for the stored `hv`. -/
abbrev Rt4 : List (Jd emptyEnv 0) := [.ty pinPiTy]

/-- the substituent for T4 is `piX` itself; its `sX` typing is `pinPiTy`
    (`lift 0 0 sX` and `sX` are the same closed term). -/
def varHv : EvTy Rt4 [] piX sX :=
  .lit pinPiTy ⟨.ty pinPiTy, .head _, .inl rfl⟩

/-- T4's context: `[x : sX]` — the stored type of the substituted
    variable (`lift 0 0 sX` is `sX`). -/
abbrev ΓSubT4 : LCtx := [.assumption sX]

/-- T4's link: the substituted VARIABLE `bvar 0` is the inner chain's
    endpoint (a bare `refl`), while the outer instantiated endpoints are
    `piX` — admission must look at the SOURCE endpoints, and refuse. -/
def varChain : EvTc Rt4 [] piX piX :=
  .subst0 (v := piX) 0 (.refl ΓSubT4 (.bvar 0)) rfl varHv

/-- refused: `reentryTc`'s `isPi` test on the INNER source endpoint
    `bvar 0` fails — `[x_read_subst_var]`, decided before any call. -/
theorem pin_T4_var_refused : bLinkS varChain = false := by
  simp only [bLinkS, varChain, reentryTc, isPi]
  rfl

/-- at the admission level the whole input is refused the same way. -/
theorem pin_T4_xAdmS_refused : xAdmS varChain = false := by
  simp only [xAdmS, admS, varChain, flattenTc, Flat.segment,
    Flat.segmentF, Flat.splitPi, Segs.admS, Flat.segAdmS, piSpinedTc,
    bLinkS, reentryTc, isPi]
  rfl

/-- the mutant re-entry: `reentryTc` without the inner `isPi` tests —
    the guard's necessity.  Structural (kernel-reducible) so the
    acceptance pin below evaluates by `decide`. -/
def reentryTcMut {Γ : LCtx} {A B : Expr Nat} (c : EvTc R Γ A B) : Bool :=
  if hB : isPi B then ((flattenTc c).segment hB).admS else true

/-- the mutant link check: substitution links ask `reentryTcMut`. -/
def bLinkSMut : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → Bool
  | _, _, _, .lit _ _ => false
  | _, _, _, .ofCv _ c => bCvS c
  | _, _, _, .refl _ _ => false
  | _, _, _, .symm _ => false
  | _, _, _, .trans _ _ => false
  | _, _, _, .piCod .. => false
  | _, _, _, .subst0 _ c _ _ => reentryTcMut c
  | _, _, _, .substLet _ c _ _ => reentryTcMut c
  | _, _, _, .wk _ _ l => bLinkSMut l

/-- the mutant single-segment admission. -/
def Flat.segAdmSMut : {Γ : LCtx} → {P M : Expr Nat} → Flat R Γ P M → Bool
  | _, _, _, .nil _ => true
  | _, _, _, .cons l _ (.nil _) => piSpinedTc l || bLinkSMut l
  | _, _, _, .cons l _ (.cons l' hl' rest') =>
      bLinkW l && (Flat.cons l' hl' rest').bPrefixW

/-- the mutant segment admission. -/
def Segs.admSMut : {Γ : LCtx} → {P Q : Expr Nat} → Segs R Γ P Q → Bool
  | _, _, _, .nil _ => true
  | _, _, _, .cons p _ rest => p.segAdmSMut && rest.admSMut

/-- the mutant admission. -/
def xAdmSMut {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B')) :
    Bool := ((flattenTc c).segment rfl).admSMut

/-- the mutant ACCEPTS the T4 input: without the inner `isPi` test the
    substituted variable is never inspected. -/
theorem pin_T4_mutant_accepts : xAdmSMut varChain = true := by
  simp only [xAdmSMut, varChain, flattenTc, Flat.segment, Flat.segmentF,
    Flat.splitPi, Segs.admSMut, Flat.segAdmSMut, piSpinedTc,
    piSpinedCv, piSpinedConv, bLinkSMut, reentryTcMut, isPi]
  rfl

/-- the refusal is at admission, so no call of the route can be formed:
    the `xAdmS varChain = true` premise type is empty. -/
theorem pin_T4_route_unreachable (h : xAdmS varChain = true) : False := by
  rw [pin_T4_xAdmS_refused] at h; exact Bool.noConfusion h

/-! #### W-X-SUBST-JOIN teeth -/

/-- the probe's leaf-free `subst0` link over the β bundle: inner `refl`
    at `piX`, `y : Sort 1` ↦ `Sort 0`. -/
def subLink : EvTc [Jd.tc betaMiddleT] [] piX piX :=
  .subst0 (v := subV) 0 (.refl ΓSub piX) rfl (.sort .zero)

/-- a two-link segment joining the substitution link across a non-Π
    middle (`betaRedex`): `[subst0-link, ofCv lit-β]`. -/
def joinSeg : Flat [Jd.tc betaMiddleT] [] piX betaRedex :=
  .cons subLink rfl (.cons betaLink₁ rfl (.nil betaRedex))

/-- W-X-SUBST-JOIN: a segment of ≥ 2 links containing a substitution is
    refused — the multi-link arm asks `bLinkW` of the head, which is
    `false` for `subst0`. -/
theorem pin_join_refused : joinSeg.segAdmS = false := by
  simp only [joinSeg, Flat.segAdmS, subLink, bLinkW]
  rfl

/-- a minimal `esub` node: a `refl` conversion of `Sort 0` at
    `[y : Sort 1]`, then the `y ↦ Sort 0` substitution. -/
def esubProbe : EvCv Rt1 [] subV subV (.sort (.succ .zero)) :=
  .esub (v := subV) 0 _
    (.refl (EvTy.sort .zero : EvTy Rt1 ΓSub subV (.sort (.succ .zero))))
    rfl (.sort .zero) (.sort (.succ .zero))

/-- the cv-level JOIN: an `esub` inside a `trans` is refused — the
    `trans` arm of `bCvS` demands W-admissible children and `bCvW` is
    `false` on `esub`. -/
theorem pin_join_inner_trans_refused :
    bCvS (EvCv.trans esubProbe esubProbe) = false := by
  simp only [bCvS, bCvW, esubProbe]
  rfl

/-! #### the depth-1 shape (#7148 §3) -/

/-- the two-entry inner context `[x : Sort 0, y : Sort 1]` — the
    substitution removes index `1` (`y`), leaving `[x]`. -/
abbrev ΓSub2 : LCtx :=
  [.assumption (.sort .zero), .assumption (.sort (.succ .zero))]

/-- the inner chain for depth 1: the β `trans` literals weakened twice
    into `ΓSub2` (the non-spined inner, so the pin exercises the
    re-entry rather than the spined shortcut). -/
def t2Inner : EvTc RBeta ΓSub2 piX piX :=
  .ofCv _ (.wk (.assumption (.sort .zero)) 0
    (.wk (.assumption (.sort (.succ .zero))) 0
      (.trans betaSubCv₁ betaSubCv₂)))

/-- the depth-1 chain: `subst0 1` over `t2Inner`, at the one-entry
    context `substRemove subV 1 ΓSub2`. -/
def t2Chain :
    EvTc RBeta (substRemove subV 1 ΓSub2) piX piX :=
  .subst0 (v := subV) 1 t2Inner rfl (.sort .zero)

/-- at depth `j = 1` the premise is still `.sub 1` on the stack — no
    regularity rebuild, and admission goes through. -/
theorem pin_depth1 : xAdmS t2Chain = true := by
  simp only [xAdmS, admS, t2Chain, t2Inner, betaSubCv₁, betaSubCv₂,
    flattenTc, flattenCv, EvCv.castIdx, Flat.wk, Flat.append, Flat.symm,
    Flat.segment, Flat.segmentF, Flat.splitPi, Segs.admS, Flat.segAdmS,
    piSpinedTc, piSpinedCv, piSpinedConv, bLinkS, reentryTc, bCvS,
    bLinkW, bCvW, isPi]
  rfl

/-- the stack test: a `CtxMorph` carries a `.sub`/`.subLet` entry. -/
def σHasSub : {Γ Γ' : LCtx} → CtxMorph E n Γ Γ' → Bool
  | _, _, .nil => false
  | _, _, .sub .. => true
  | _, _, .subLet .. => true
  | _, _, .ins _ _ σ => σHasSub σ

/-- the one-entry outer context of the depth-1 substitution, as a
    `ViaS` witness (empty stack over its own well-formedness). -/
def vSub1Base : CtxWfViaS emptyEnv 0 (substRemove subV 1 ΓSub2) :=
  .ofWf (show CtxWfT emptyEnv 0 (substRemove subV 1 ΓSub2) from
    .assumption _ _ _ .nil (.sort _ .zero))

/-- the source-side witness the route would build for `t2Chain`: a
    `.sub 1` entry over the one-entry outer context. -/
def vSub1 : CtxWfViaS emptyEnv 0 ΓSub2 :=
  vSub1Base.sub (v := subV) 1 rfl (HasTyT.sort _ .zero)

/-- the depth-1 stack's head is the `.sub` entry. -/
theorem pin_depth1_stack : σHasSub vSub1.σ = true := rfl

/-! #### the K shape and nesting -/

/-- `ctxConvVar`'s own shape as an X input (`RcicF8CtxConvVar`): the
    domain-conversion `cA := refl piX`, the body chain `e` the `refl`
    literal weakened under the binder — admitted exactly because `e`
    is, by one `subst0` re-entry under a `wk`. -/
def eK : EvTc Rt1 [.assumption piX] piX piX :=
  .ofCv _ (.wk (.assumption piX) 0 (.lit subConvRefl mem_cv_subConvRefl))

def kChain : EvTc Rt1 [.assumption piX] piX piX :=
  ctxConvVar (.refl [] piX) eK

/-- the K shape is admitted: `ctxConvVar` is an `EvTc.cast`-wrapped
    `subst0 0` over a `wk`-lifted body — the `cast` is index-only
    (`instantiate_bvar_lift_succ`, both sides `piX` here), the `subst0`
    re-enters, and the `refl` literal's one-link segment is S-admissible. -/
theorem pin_K_shape : xAdmS kChain = true := by
  simp only [xAdmS, admS, kChain, ctxConvVar, EvTc.cast, EvTy.cast,
    eK, flattenTc, flattenCv, EvCv.castIdx, Flat.wk, Flat.append,
    Flat.symm, Flat.segment, Flat.segmentF, Flat.splitPi, Segs.admS,
    Flat.segAdmS, piSpinedTc, piSpinedCv, piSpinedConv, bLinkS,
    reentryTc, bCvS, bLinkW, bCvW, isPi, instantiate_bvar_lift_succ,
    lift, instantiate, substRemove]
  rfl

/-- two re-entries, one census: `subst0 0` over a `wk`'d
    `betaSubChain` — the outer `subst0` re-enters on the `wk` link,
    which descends and re-enters again on the inner `subst0`. -/
def nestChain : EvTc RBeta [] piX piX :=
  .subst0 (v := subV) 0
    (.wk (.assumption (.sort (.succ .zero))) 0 betaSubChain) rfl betaSubHv

/-- nested substitution is admitted: the outer re-entry sees a `wk`'d
    `subst0` link, which re-enters again. -/
theorem pin_nested : xAdmS nestChain = true := by
  simp only [xAdmS, admS, nestChain, betaSubChain, betaSubInner,
    betaSubCv₁, betaSubCv₂, flattenTc, flattenCv, EvCv.castIdx, Flat.wk,
    Flat.append, Flat.symm, Flat.segment, Flat.segmentF, Flat.splitPi,
    Segs.admS, Flat.segAdmS, piSpinedTc, piSpinedCv, piSpinedConv,
    bLinkS, reentryTc, bCvS, bLinkW, bCvW, isPi]
  rfl

/-! #### T2 — J sees the `sub` stack -/

/-- `hty`'s atom is a strict child of the `refl` node it sits under —
    the certification `jSub` uses for its trivial answer. -/
theorem litSubEq_of_refl {R : List (Jd E n)} {Γ : LCtx} {a A : Expr Nat}
    {hty : HasTyT E n Γ a A}
    (hsub : ∃ r ∈ R, SubEq (.cv (.refl Γ a A hty)) r) :
    ∃ r ∈ R, SubEq (.ty hty) r := by
  obtain ⟨r, hr, hs⟩ := hsub
  exact ⟨r, hr, subEq_trans (Or.inr (SubOf.child
    (y := .cv (.refl Γ a A hty))
    (show (Jd.ty hty : Jd E n) ∈ Jd.cvChildren (ConvT.refl Γ a A hty) from
      List.Mem.head _))) hs⟩

/-- any immediate child `x` of the `β` leg is a strict descendant of the
    `trans`-of-`β` root — `jSub`'s second arm certifies `hA`, `hbody`
    and `harg` this way (the β node is the trans's second `cvChild`). -/
theorem litSubEq_trans_beta_child {R : List (Jd E n)} {Γ : LCtx}
    {a A body arg B : Expr Nat} {u : Level}
    (h1 : ConvT E n Γ a (.app (.lam A body) arg) (instantiate0 arg B))
    {hA : HasTyT E n Γ A (.sort u)}
    {hbody : HasTyT E n (.assumption A :: Γ) body B}
    {harg : HasTyT E n Γ arg A} {x : Jd E n}
    (hx : x ∈ Jd.cvChildren (ConvT.beta Γ A body arg B u hA hbody harg))
    (hsub : ∃ r ∈ R, SubEq
      (.cv (.trans Γ a (.app (.lam A body) arg) (instantiate0 arg body)
        (instantiate0 arg B) h1
        (.beta Γ A body arg B u hA hbody harg))) r) :
    ∃ r ∈ R, SubEq x r := by
  obtain ⟨r, hr, hs⟩ := hsub
  exact ⟨r, hr, subEq_trans (.inr (.trans
    (.child (y := .cv (.beta Γ A body arg B u hA hbody harg)) hx)
    (.child (y := .cv (.trans Γ a (.app (.lam A body) arg)
        (instantiate0 arg body) (instantiate0 arg B) h1
        (.beta Γ A body arg B u hA hbody harg)))
      (show (Jd.cv (.beta Γ A body arg B u hA hbody harg) : Jd E n) ∈
        Jd.cvChildren (ConvT.trans Γ a (.app (.lam A body) arg)
          (instantiate0 arg body) (instantiate0 arg B) h1
          (.beta Γ A body arg B u hA hbody harg))
        from .tail _ (.head _))))) hs⟩

/-- end-cast for a star leg; `castB_leaves` keeps `leaves` computing
    through the cast for the contract proof. -/
def EvParStar.castB {a b b' T : Expr Nat} (hs : EvParStar R Γ a b T)
    (h : b = b') : EvParStar R Γ a b' T := h ▸ hs

theorem EvParStar.castB_leaves {a b b' T : Expr Nat}
    (hs : EvParStar R Γ a b T) (h : b = b') :
    (hs.castB h).leaves = hs.leaves := by subst h; rfl

/-- T2's J: answers a literal it can self-certify ONLY when the
    witness's stack carries a `.sub` entry — a positive answer proves
    the call ran at a substitution's source context; `pin_J_nil_stack`
    shows the same J refuses the `ofWf` stack.  Two arms: the `refl`
    literal (its single `.ty` child certifies the valley's typing leaf)
    and the `trans`-through-`β` literal — the shape the route actually
    asks about (`refl` inners are Π-spined and never reach J).  The β
    leg's `harg` typing serves as BOTH endpoint typings under the guards
    `a = arg`, `A = inst0 arg B`, `a = inst0 arg body`; `hbody`'s typing
    is substituted to get the right endpoint's typing via `EvTy.esub`. -/
def jSub (R : List (Jd emptyEnv 0)) : JProcViaSP R :=
  fun {Γ₀ _ _ _} v h hsub =>
    match h with
    | .refl _ a _ hty =>
        if σHasSub v.σ then
          let ht := EvTy.lit hty (litSubEq_of_refl hsub)
          some ⟨a, .refl ht, .refl ht, ht, ht⟩
        else none
    | .trans _ a m c A h1 h2 =>
        match m, c, A, h2 with
        | _, _, _, .refl .. => none
        | _, _, _, .symm .. => none
        | _, _, _, .trans .. => none
        | _, _, _, .beta _ A' body arg B' u hA hbody harg =>
            if hEq : a = arg then
              if hT : A' = instantiate0 arg B' then
                if hE : a = instantiate0 arg body then
                  if σHasSub v.σ then
                    let cA := litSubEq_trans_beta_child h1 (.head _) hsub
                    let cB := litSubEq_trans_beta_child h1
                      (.tail _ (.head _)) hsub
                    let cG := litSubEq_trans_beta_child h1
                      (.tail _ (.tail _ (.head _))) hsub
                    let ht : EvTy R _ a (instantiate0 arg B') :=
                      EvTy.cast rfl hEq.symm hT (EvTy.lit harg cG)
                    let hv : EvTy R _ (lift 0 0 arg) (lift 0 0 A') :=
                      EvTy.cast rfl (lift_zero_idx 0 arg).symm
                        (lift_zero_idx 0 A').symm (EvTy.lit harg cG)
                    let hAu : EvTy R _ (lift 0 0 A') (.sort u) :=
                      EvTy.cast rfl (lift_zero_idx 0 A').symm rfl
                        (EvTy.lit hA cA)
                    let hb : EvTy R _ (instantiate0 arg body)
                        (instantiate0 arg B') :=
                      EvTy.cast rfl (by rw [lift_zero_idx]; rfl)
                        (by rw [lift_zero_idx]; rfl)
                        (EvTy.esub (v := arg) (t := A') 0 u
                          (EvTy.lit hbody cB)
                          (List.getElem?_cons_zero :
                            (LocalDecl.assumption A' :: Γ₀)[0]? =
                              some (.assumption A')) hv hAu)
                    some ⟨a, .refl ht, (EvParStar.refl hb).castB hE.symm,
                      ht, hb⟩
                  else none
                else none
              else none
            else none
        | _, _, _, .zeta .. => none
        | _, _, _, .zetaLocal .. => none
        | _, _, _, .delta .. => none
        | _, _, _, .iota .. => none
        | _, _, _, .lit .. => none
        | _, _, _, .app .. => none
        | _, _, _, .lam .. => none
        | _, _, _, .pi .. => none
        | _, _, _, .letE .. => none
        | _, _, _, .sorts .. => none
        | _, _, _, .consts .. => none
        | _, _, _, .eta .. => none
        | _, _, _, .irr .. => none
        | _, _, _, .tyConv .. => none
    | .symm _ _ _ _ _ => none
    | .beta _ _ _ _ _ _ _ _ _ => none
    | .zeta _ _ _ _ _ _ _ _ _ => none
    | .zetaLocal _ _ _ _ _ _ _ => none
    | .delta _ _ _ _ _ _ _ _ _ _ _ => none
    | .iota _ _ _ _ _ _ _ => none
    | .lit _ _ _ _ _ _ => none
    | .app _ _ _ _ _ _ _ _ _ => none
    | .lam _ _ _ _ _ _ _ _ _ => none
    | .pi _ _ _ _ _ _ _ _ _ => none
    | .letE _ _ _ _ _ _ _ _ _ _ _ _ => none
    | .sorts _ _ _ _ => none
    | .consts _ _ _ _ _ _ _ _ _ _ => none
    | .eta _ _ _ _ _ => none
    | .irr _ _ _ _ _ _ _ => none
    | .tyConv _ _ _ _ _ _ _ _ => none

/-- `jSub`'s strict contract: each answering arm's valley's leaves are
    children of the asked conversion's node — `.ty hty` under `refl`;
    `.ty hA`/`.ty hbody`/`.ty harg` (one step deeper) under `trans`-`β`. -/
theorem jSub_contract : JContractViaSP jSub := by
  intro R Γ₀ M₁ M₂ T v h hsub V hV ℓ hℓ
  unfold jSub at hV
  split at hV
  all_goals first
    | exact Option.noConfusion hV
    | skip
  all_goals try (split at hV)
  all_goals first
    | exact Option.noConfusion hV
    | skip
  all_goals try (split at hV)
  all_goals first
    | exact Option.noConfusion hV
    | skip
  all_goals try (split at hV)
  all_goals first
    | exact Option.noConfusion hV
    | skip
  all_goals try (split at hV)
  all_goals first
    | exact Option.noConfusion hV
    | skip
  all_goals try (split at hV)
  all_goals first
    | exact Option.noConfusion hV
    | skip
  · -- `refl` arm: the valley's leaf copies are all `.ty hty`, a
    -- direct child of the asked `refl` node.
    try dsimp only at hV
    obtain rfl := Option.some.inj hV
    simp only [Valley.leaves, EvParStar.leaves, EvTy.leaves,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      false_or, or_self] at hℓ
    obtain rfl := hℓ
    exact .child (.head _)
  · -- `trans`-`β` arm: the leaves are `.ty harg` / `.ty hbody` /
    -- `.ty hA`, each a `β`-child under the `trans`.  The `trans`
    -- membership is given first so its `.child` fixes the middle
    -- node (`h2`'s literal `β` value); each leaf's `β`-child
    -- membership is then fully determined.
    try dsimp only at hV
    obtain rfl := Option.some.inj hV
    simp only [Valley.leaves, EvParStar.leaves,
      EvParStar.castB_leaves, EvTy.cast_leaves, EvTy.leaves,
      List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, false_or, or_assoc] at hℓ
    rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine SubOf.trans ?_ (.child (.tail _ (.head _))) <;>
      first
        | exact .child (.head _)
        | exact .child (.tail _ (.head _))
        | exact .child (.tail _ (.tail _ (.head _)))

/-- the always-refusing J (declining). -/
def jNil (R : List (Jd emptyEnv 0)) : JProcViaSP R :=
  fun _ _ _ => none

theorem jNil_contract : JContractViaSP jNil :=
  fun _ _ _ _ _ _ _ _ _ hV _ _ => Option.noConfusion hV

/-- the fixture bundles: `declining` lifted to `ViaS`, with the J front
    overridden by `jSub` / `jNil`. -/
def XSub (hsep : SepAll emptyEnv 0) : SuppliersViaS emptyEnv 0 :=
  { (SuppliersVia.declining hsep).toS with J := jSub, hJ := jSub_contract }

def XNil (hsep : SepAll emptyEnv 0) : SuppliersViaS emptyEnv 0 :=
  (SuppliersVia.declining hsep).toS

/-- `emptyEnv` carries no members: the env hypotheses discharge. -/
def clSub : EnvClosed emptyEnv := fun _ _ h => Option.noConfusion h

def ssSub : EnvMembersSubstStable emptyEnv :=
  fun _ _ h => Option.noConfusion h

/-- the empty-context `ViaS` witness. -/
def vNil : CtxWfViaS emptyEnv 0 [] := .ofWf .nil

/-- the witness the route's `subst0` arm passes to the re-entry on
    `t1Chain`: the `.sub 0` entry over `vNil` — T2's point is that the
    inner literal is asked under THIS stack, not under `nil`. -/
def vSub0 : CtxWfViaS emptyEnv 0 ΓSub :=
  vNil.sub (v := subV) 0 rfl subTyD

/-- the witness the route's cv-`wk` arm passes to the inner literal:
    `vSub0` peeled once — σ = `.ins y 0 (.sub 0 …)`, whose head-inside
    `.sub` entry is what `jSub` checks. -/
def vSub0Ins : CtxWfViaS emptyEnv 0 [] :=
  vSub0.ins (.assumption (.sort (.succ .zero))) 0

/-- the J invocation shape at the fixture's source: `σ` carries a
    `.sub`, so `jSub` answers. -/
theorem pin_J_sees_sub_stack :
    (jSub Rt1 vSub0Ins subConvRefl mem_cv_subConvRefl).isSome = true := rfl

/-- the same literal under the `ofWf` (`.nil`) stack is refused — J
    really does see the `sub` entry, not just any witness. -/
theorem pin_J_nil_stack : jSub Rt1 vNil subConvRefl mem_cv_subConvRefl =
    none := rfl

/-! #### the J-control route fixture

A `refl` inner never reaches J (it is Π-spined, handled inside the
valley step), so the route-level pins run on `tJChain`: the lone
`subst0` link over a `wk`'d `lit` whose conversion is the `trans`-
through-`betaRedex` shape — W-admissible as a literal (`bCvW` holds)
but NOT Π-spined (`piSpinedConv` fails on the `betaRedex` middle), so
the route really does call J — and `jSub` answers only because the
witness stack carries the `.sub` entry the `subst0` arm installed. -/

/-- `piX ≡ piX` at `sX` through the non-Π `betaRedex` middle:
    `symm`-β then β — `jSub`'s second arm supplies its valley. -/
def jTransConv : ConvT emptyEnv 0 [] piX piX sX :=
  .trans [] piX betaRedex piX sX
    (.symm [] betaRedex piX sX betaRedexConv) betaRedexConv

/-- the J fixture's bundle: the literal's atom and the kept `hv` atom. -/
abbrev RJ : List (Jd emptyEnv 0) := [.cv jTransConv, .ty subTyD]

/-- the literal of `jTransConv`, certified under its own atom. -/
def tJCv : EvCv RJ [] piX piX sX :=
  .lit jTransConv ⟨.cv jTransConv, .head _, .inl rfl⟩

/-- the inner chain: the literal weakened into `[y : Sort 1]` —
    `flattenCv` keeps it one link, so the re-entry asks J about the
    `trans` conversion at the source context. -/
def tJInner : EvTc RJ ΓSub piX piX :=
  .ofCv _ (.wk (.assumption (.sort (.succ .zero))) 0 tJCv)

/-- the stored substituent typing, kept as a literal leaf. -/
def tJHv : EvTy RJ [] subV (.sort (.succ .zero)) :=
  .lit subTyD ⟨.ty subTyD, .tail _ (.head _), .inl rfl⟩

/-- the route-level fixture: `y : Sort 1 ↦ Sort 0` over the
    non-spined inner. -/
def tJChain : EvTc RJ [] piX piX :=
  .subst0 (v := subV) 0 tJInner rfl tJHv

/-- admitted under S: the lone `subst0` re-enters on the inner segment,
    which is a single `bCvS`-passing `wk`'d literal. -/
theorem tJChain_admS : xAdmS tJChain = true := by
  simp only [xAdmS, admS, tJChain, tJInner, tJCv, jTransConv,
    flattenTc, flattenCv, EvCv.castIdx, Flat.wk, Flat.append, Flat.symm,
    Flat.segment, Flat.segmentF, Flat.splitPi, Segs.admS, Flat.segAdmS,
    piSpinedTc, piSpinedCv, piSpinedConv, bLinkS, reentryTc, bCvS,
    bLinkW, bCvW, isPi]
  rfl

/- NOTE (deferred, named): the route-level J-control pins
    `xValleySS? (XSub hsep) hsep clSub ssSub vNil tJChain tJChain_admS = some _`
    and its `XNil` refusal are not stated.  `xValleySS?` is
    `termination_by`-recursive (`WellFounded.fix`), so the call does not
    kernel-reduce (`decide`/`rfl` fail) and the equation-lemma trace
    through `xSegsSS`/`xLinkS`/`reenterTcS`/`svalleyCvViaS` is the
    expensive path.  The worker-level content is proved:
    `pin_J_sees_sub_stack`/`pin_J_nil_stack` show `jSub` answers iff the
    witness stack carries `.sub`, and `pin_subst0_beta_contract`/
    `pin_subst0_beta_edges` give the conditional route lemmas. -/

/-- every answer of the route on the fixture satisfies the leaf
    contract. -/
theorem pin_subst0_beta_contract (hsep : SepAll emptyEnv 0)
    (r : SegOut RJ [] _ _ _ _ tJChain.leaves)
    (hr : xValleySS? (XSub hsep) hsep clSub ssSub vNil tJChain
      tJChain_admS = some r) :
    ∀ ℓ ∈ r.1.1.leaves ++ r.1.2.leaves,
      ∃ ℓ' ∈ tJChain.leaves, SubEq ℓ ℓ' :=
  xValleySS_contract _ _ _ _ _ _ _ r hr

/-- every answer of the route on the fixture carries lex-edge census
    bounds. -/
theorem pin_subst0_beta_edges (hsep : SepAll emptyEnv 0)
    (r : SegOut RJ [] _ _ _ _ tJChain.leaves)
    (hr : xValleySS? (XSub hsep) hsep clSub ssSub vNil tJChain
      tJChain_admS = some r) (Z : List (Jd emptyEnv 0)) :
    EdgeContractLex (census tJChain r Z) :=
  xValleySS_edges _ _ _ _ _ _ _ r hr Z

/-! ### §8 documentation notes

The `wt`/`sizeOf` pair (not `sizeOf` alone) is required because
`flattenTc` PRESERVES `wt` exactly while growing the `sizeOf`
arbitrarily: `flattenTc (.wk d k c)` pushes `EvTc.wk` into every
flattened link, and `linkSymm`/`Flat.symm` push `symm` into every link —
`sizeOf` of the flattened chain exceeds `sizeOf c`, so a `sizeOf`-only
measure would not decrease under re-entry; `wt` counts links once, under
weakening, symmetry and flattening (`flattenTc_wt` etc.).

`W-X-SUBST-JOIN` remains an open (named) refusal at two levels:
`bCvS .trans` requires both children W-admitted (a join inside one
link), and `segAdmS`'s multi-link arm asks `bLinkW`/`bPrefixW` (a join
across links).  The A.2 measurement (`RcicF8XJoinA2`, #7301 §5) shows a
reachable JOIN-shaped input.

`pin_S_at_source` is intentionally not stated: under `CtxWfViaS`, S's
premise-free front sees the TARGET context by construction (`atCtx`); a
meaningful "S only at source" pin needs PR-B's per-step `EvParStar`
substitution wrappers (#7145) to express.  Deferred, named. -/

#print axioms tcWt
#print axioms EvCv.wt
#print axioms EvTc.wt
#print axioms Flat.wt
#print axioms Segs.wt
#print axioms EvCv.castIdx_wt
#print axioms linkSymm_wt
#print axioms Flat.append_wt
#print axioms Flat.symm_wt
#print axioms Flat.wk_wt
#print axioms flattenCv_wt
#print axioms flattenT_wt
#print axioms flattenTc_wt
#print axioms Flat.splitPi_wt
#print axioms Flat.segmentF_wt
#print axioms Flat.segment_wt
#print axioms bCvS
#print axioms reentryCv
#print axioms bLinkS
#print axioms reentryTc
#print axioms Flat.segAdmS
#print axioms Segs.admS
#print axioms admS
#print axioms xAdmS
#print axioms bCvS_of_bCvW
#print axioms bLinkS_of_bLinkW
#print axioms Flat.segAdmS_of_segAdmW
#print axioms Segs.admS_of_admW
#print axioms xAdmS_of_xAdmW
#print axioms bCvS_esub
#print axioms bLinkS_subst0
#print axioms bLinkS_substLet
#print axioms bLinkW_subst0
#print axioms bLinkW_substLet
#print axioms reentryCv_spec
#print axioms reentryTc_spec
#print axioms XOut.wk
#print axioms XOut.subst0
#print axioms XOut.substLet
#print axioms XOut.wk_leaves
#print axioms XOut.subst0_leaves
#print axioms XOut.substLet_leaves
#print axioms Below_of_subset
#print axioms SegOut.weaken
#print axioms SegOut.weakenBelow
#print axioms SegOut.wk
#print axioms SegOut.subst0
#print axioms SegOut.substLet
#print axioms lexNat_of_le
#print axioms xSegsSS
#print axioms xSegSS
#print axioms xLinkS
#print axioms xCvS
#print axioms reenterCvS
#print axioms reenterTcS
#print axioms xValleySS?
#print axioms xValleySS_contract
#print axioms xValleySS_edges
#print axioms xSegSS_of_segAdmW
#print axioms xSegsSS_of_admW
#print axioms xValleySS?_of_admW
#print axioms ΓSub
#print axioms subV
#print axioms subConvRefl
#print axioms subConv11
#print axioms subTyD
#print axioms dBig
#print axioms Rt1
#print axioms mem_cv_subConvRefl
#print axioms mem_ty_subTyD
#print axioms mem_ty_dBig
#print axioms t1Inner
#print axioms t1Hv
#print axioms t1HvMut
#print axioms t1Chain
#print axioms t1ChainMut
#print axioms RBeta
#print axioms betaSubCv₁
#print axioms betaSubCv₂
#print axioms betaSubInner
#print axioms betaSubHv
#print axioms betaSubHvMut
#print axioms betaSubChain
#print axioms pin_beta_leaves
#print axioms pin_subst0_beta_adm
#print axioms oReflSub
#print axioms pin_T1_leaves
#print axioms pin_T1_kept_in_exposure
#print axioms pin_T1_mutant_exposes_decoy
#print axioms pin_T1_wts
#print axioms pin_T1_mutant_wrong_hv_not_below
#print axioms pin_T1_mutant_breaks_contract
#print axioms pin_T1_kept_below
#print axioms pin_T3_kept_in_codomain
#print axioms pin_T3_kept_not_strict
#print axioms Rt4
#print axioms varHv
#print axioms ΓSubT4
#print axioms varChain
#print axioms pin_T4_var_refused
#print axioms pin_T4_xAdmS_refused
#print axioms reentryTcMut
#print axioms bLinkSMut
#print axioms Flat.segAdmSMut
#print axioms Segs.admSMut
#print axioms xAdmSMut
#print axioms pin_T4_mutant_accepts
#print axioms pin_T4_route_unreachable
#print axioms subLink
#print axioms joinSeg
#print axioms pin_join_refused
#print axioms esubProbe
#print axioms pin_join_inner_trans_refused
#print axioms ΓSub2
#print axioms t2Inner
#print axioms t2Chain
#print axioms pin_depth1
#print axioms σHasSub
#print axioms vSub1Base
#print axioms vSub1
#print axioms pin_depth1_stack
#print axioms eK
#print axioms kChain
#print axioms pin_K_shape
#print axioms nestChain
#print axioms pin_nested
#print axioms litSubEq_of_refl
#print axioms litSubEq_trans_beta_child
#print axioms EvParStar.castB
#print axioms EvParStar.castB_leaves
#print axioms jSub
#print axioms jSub_contract
#print axioms jNil
#print axioms jNil_contract
#print axioms XSub
#print axioms XNil
#print axioms clSub
#print axioms ssSub
#print axioms vNil
#print axioms vSub0
#print axioms vSub0Ins
#print axioms pin_J_sees_sub_stack
#print axioms pin_J_nil_stack
#print axioms jTransConv
#print axioms RJ
#print axioms tJCv
#print axioms tJInner
#print axioms tJHv
#print axioms tJChain
#print axioms tJChain_admS
#print axioms pin_subst0_beta_contract
#print axioms pin_subst0_beta_edges

end Rcic.Declarative.F8Measure
