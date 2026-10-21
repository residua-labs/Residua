import rcic.RcicSynTable
import rcic.RcicSynDeltaBeta

/-!
# S11 §1 — T11-δ: the δ kept-result ES composition, conditional

`research/rcic/sortrow/S11_DELTA_IOTA_ES_CONSTRUCTION.md` §1 (main `699071f8ca`).
Fix `cδ := CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr` and the
retained-result condition `hu : levelIsZero (σ hb.reg.1) = false`.

`es_of_below_delta_crule` discharges `ES` for this case from a `Below` supply.
This module seals the same composition as a **conditional lemma**: the
premises are exactly the actual bounded payments

* `hmem : deltaRule r D_b ∈ tbl` — the same `D_b` as the admission body;
* `hDb_cl : D_b.ClosedWf` — Db's closedness certificate;
* `hObs : LvlEq (D_b.eps φ []) (D_b.eps ψ [])` — T3's finite certificate at
  `φ := instLevel (ls.map σ)`, `ψ := fun l => σ (instLevel ls l)`;
* `hL : CL dl canonL`, `hB : CL DbΓ hb`, `hR : CL hb dr` — the three strict
  requests of §1.3, on the same actual `Γ`, `σ`, `ρ`.

The five-link chain of §1.5 —

```text
dl.eps ↔ canonL.eps = const r (ls.map σ) → Db.eps φ [] ≈ Db.eps ψ [] = DbΓ.eps ↔ hb.eps ↔ dr.eps
```

— is assembled by `es_delta` from `CRoot.bare hmem rfl (ls.map σ) [] rfl` and
`eps_deltaBodyInst_closed`; every link is one of the premises or a main lemma,
never an external "already ES" field and never a re-derivation.

Control (§1.4): the all-level `∀ l, eqN (φ l) (ψ l)` premise of
`es_of_below_delta_crule_eqN` is NOT required — `es_delta_kept` consumes the
finite `hObs` alone and is stated *without* the `eqN`-at-all-levels variant.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## the two bounded objects (§1.2) -/

/-- §1.2 `canonL` — the canonical left endpoint typing, a `TyP.const` built
    from `hb.reg` (`hb.reg.1` the original domain level, `hb.reg.2` its sort
    typing). It shares the body's own `ls`, `m`, and environment — never a
    regenerated chain. -/
noncomputable def deltaCanonL {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)) :
    TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype) :=
  TyP.const E n Γ r ls ls m hb.reg.1 hres hlen hwf (eqNList_refl ls) hb.reg.2

/-- §1.2 `DbΓ` — the level-instantiated closed member body typing
    `D_b : TyP E m.arity [] b m.mtype` weakened to `Γ` by `deltaBodyInst`.
    `Γ` is explicit: `D_b` lives in the empty context, so `Γ` cannot be
    inferred from the arguments. -/
noncomputable def deltaDbΓ {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E)
    (Γ : LCtx) {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (D_b : TyP E m.arity [] b m.mtype) :
    TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype) :=
  deltaBodyInst hE hres hbody hlen hwf Γ D_b

/-! ## the five-link composition (§1.5) -/

/-- The δ kept-result ES as a conditional lemma. Premises are exactly the
    actual bounded payments: the actual table position of `deltaRule r D_b`,
    `D_b`'s closedness, T3's finite `hObs`, and the three strict CLs. The
    chain: `dl.eps ↔ canonL.eps = const r (ls.map σ) → Db.eps φ []`
    (`eps_const_rel` + `CRoot.bare`), `≈ Db.eps ψ []` (`hObs`),
    `= DbΓ.eps` (`eps_deltaBodyInst_closed`), `↔ hb.eps ↔ dr.eps` (CLs). -/
theorem es_delta_kept (tbl : List CRule) (σ : Level → Level) (ρ : List Disp)
    {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E) {Γ : LCtx} {r : Nat}
    {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (D_b : TyP E m.arity [] b m.mtype) (hDb_cl : D_b.ClosedWf)
    (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hmem : deltaRule r D_b ∈ tbl)
    (hObs : LvlEq (D_b.eps (instLevel (ls.map σ)) [])
      (D_b.eps (fun l => σ (instLevel ls l)) []))
    (hL : CL tbl σ ρ dl (deltaCanonL hres hlen hwf hb))
    (hB : CL tbl σ ρ (deltaDbΓ hE Γ hres hbody hlen hwf D_b) hb)
    (hR : CL tbl σ ρ hb dr) :
    ES tbl σ ρ (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr) := by
  -- link 1: `dl.eps ↔ canonL.eps = const r (ls.map σ)` (`eps_const_rel`, `hu`)
  have hdl : ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (.const r (ls.map σ)) := by
    have h := hL
    unfold CL deltaCanonL at h
    rw [eps_const_rel hu] at h
    exact h
  -- link 2: the actual root step — `const r (ls.map σ) → Db.eps φ []`
  have hcroot : CRoot tbl (.const r (ls.map σ))
      ((deltaRule r D_b).rhs (ls.map σ) []) :=
    CRoot.bare (tbl := tbl) hmem rfl (ls.map σ) [] rfl
  -- links 3–5: `rhs = Db.eps φ [] ≈ Db.eps ψ [] = DbΓ.eps ↔ hb.eps ↔ dr.eps`
  have hmid : ConvMod (EStep tbl) LvlEq
      ((deltaRule r D_b).rhs (ls.map σ) []) (hb.eps σ ρ) := by
    have h := hB
    unfold CL deltaDbΓ at h
    rw [eps_deltaBodyInst_closed hE hres hbody hlen hwf Γ hDb_cl σ ρ hρ] at h
    exact (ConvMod.eqv hObs).trans h
  exact es_delta hres hbody htr hlen hwf hb dl dr hdl
    (.inl (.cr hcroot)) (hmid.trans hR)

/-! ## the atom facts (§1.2) -/

/-- `canonL.wt < cδ.wt`: the canonical left endpoint is strictly below the
    original node — `hb.reg.2.wt ≤ hb.wt` (`wt_reg_le`), `Aw r < dl.wt`
    (`admW_lt_of_const`), `N = 1 + hb.wt + dl.wt + dr.wt`. -/
theorem deltaCanonL_wt_lt (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)) :
    (deltaCanonL hres hlen hwf hb).wt Aw <
      (CvP.delta E n Γ r ls m b hres hbody htr hlen hwf hb dl dr).wt Aw := by
  have hreg := TyP.wt_reg_le Aw hb
  have hAw : Aw r < dl.wt Aw := TyP.admW_lt_of_const Aw dl ⟨ls, rfl⟩
  have hpos := TyP.wt_pos Aw dr
  simp only [deltaCanonL, TyP.wt, CvP.wt]
  omega

/-- `DbΓ.atoms = Db.atoms`: context weakening adds no atoms — the total weight
    added is never mistaken for new atoms (§1.2). -/
theorem deltaDbΓ_atoms (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E) {Γ : LCtx} {r : Nat}
    {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (D_b : TyP E m.arity [] b m.mtype) :
    (deltaDbΓ hE Γ hres hbody hlen hwf D_b).atoms Aw = D_b.atoms Aw :=
  atoms_deltaBodyInst Aw hE hres hbody hlen hwf Γ D_b

/-! ## kernel-value pins -/

/-- PIN: the instantiated rule RHS's kernel value is exactly `D_b.eps φ []` —
    the boundary across which T3's `hObs` is stated. -/
theorem deltaRule_rhs_eps_val {E : ResolvedEnv} {a : Nat} {b T : Expr Nat}
    {r : Nat} (D_b : TyP E a [] b T) (ms : List Level) :
    (deltaRule r D_b).rhs ms [] = D_b.eps (instLevel ms) [] := rfl

/-- PIN: the rule is bare (no major) — `CRoot.bare`'s premise `major = none`
    is `rfl` for `deltaRule`. -/
theorem deltaRule_major_none {E : ResolvedEnv} {a : Nat} {b T : Expr Nat}
    {r : Nat} (D_b : TyP E a [] b T) :
    (deltaRule r D_b).major = none := rfl

/-- PIN: the rule is nullary at every level list — `nargs = 0` makes
    `args := []` the only call arity. -/
theorem deltaRule_nargs_zero {E : ResolvedEnv} {a : Nat} {b T : Expr Nat}
    {r : Nat} (D_b : TyP E a [] b T) (ms : List Level) :
    (deltaRule r D_b).nargs ms = 0 := rfl

/-- PIN: `CRoot.bare`'s endpoints on `args := []` collapse to the bare
    constant head and the unapplied RHS — the root step's two ends. -/
theorem cRoot_bare_ends {E : ResolvedEnv} {a : Nat} {b T : Expr Nat}
    {r : Nat} (D_b : TyP E a [] b T) (ms : List Level) :
    ETm.appN (.const (deltaRule r D_b).head ms) [] = .const r ms := rfl

#print axioms Rcic.Syn.deltaCanonL
#print axioms Rcic.Syn.deltaDbΓ
#print axioms Rcic.Syn.es_delta_kept
#print axioms Rcic.Syn.deltaCanonL_wt_lt
#print axioms Rcic.Syn.deltaDbΓ_atoms
#print axioms Rcic.Syn.deltaRule_rhs_eps_val
#print axioms Rcic.Syn.deltaRule_major_none
#print axioms Rcic.Syn.deltaRule_nargs_zero
#print axioms Rcic.Syn.cRoot_bare_ends
