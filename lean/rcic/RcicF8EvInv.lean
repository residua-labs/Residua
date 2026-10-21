import Lean
import rcic.RcicF8Ev
import rcic.RcicTypedInvert
import rcic.RcicDTMetaTypedSR
import rcic.RcicParRedSRTyped

/-! # RcicF8EvInv — lazy inversion on provenance (O-M1a, part a)

O-M1a part (a) (S2 §2, `research/rcic/semantic/S2_OM_OBLIGATIONS.md` on PR
#6792): typing inversion performed ON PROVENANCE, never by materializing — the
inverted pieces enter later calls as `Ev` with leaves traced into the input's
leaves, strictly below the literal root. Part (a) covers inputs whose root is
`lit`, possibly under `rety` wrappers (`EvTy.litRooted`); part (b) extends to
`wk`/`esub` roots. `closure_claim = 0`.

For each of the eight plain inversion lemmas — `hasTyTInv_app`, `_lam`, `_pi`,
`_letE` (`RcicTypedInvert.lean`), `hasTyTInv_bvar`, `_const`, `_lit`
(`RcicDTMetaTypedSR.lean`), `hasTyTInv_sortT` (`RcicParRedSRTyped.lean`) — this
module defines an `Ev` twin: the plain lemma's output with `HasTyT` replaced by
`EvTy R` and `TyConvT` by `EvTc R`, non-judgment payload (levels, lookup
equations, member equations, `hlen`, `hwf`) unchanged. The input is
`(D : EvTy R Γ e T) (hD : D.litRooted = true) (heq : e = <shape>)`.

Construction: at `lit d`, recurse on `d` exactly as the plain lemma does; a
premise `d'` of `d` becomes `EvTy.lit d'` certified by `certOfChild`
(`SubOf`-through-`SubEq`); a `conv` node's `hc : ConvT … (sort u)` becomes the
chain link `EvTc.ofCv u (EvCv.lit hc …)`; `.trans`/`.refl` chains become
`EvTc.trans`/`EvTc.refl`. At `rety D c`, invert `D` and append `c` to the
residual chain with `EvTc.trans`. `wk`/`esub` roots are excluded by `hD`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- root is a literal, possibly under retyping. -/
def EvTy.litRooted : {Γ : LCtx} → {e T : Expr Nat} → EvTy R Γ e T → Bool
  | _, _, _, .lit _ _ => true
  | _, _, _, .wk _ _ _ => false
  | _, _, _, .esub _ _ _ _ _ _ => false
  | _, _, _, .subst0 _ _ _ _ => false
  | _, _, _, .substLet _ _ _ _ => false
  | _, _, _, .var _ _ _ => false
  | _, _, _, .sort _ => false
  | _, _, _, .const _ _ _ _ _ _ => false
  | _, _, _, .rety D _ => D.litRooted

/-- a child's leaf inherits its parent's root certification. -/
def certOfChild {x y : Jd E n} (hc : Child x y)
    (hsub : ∃ r ∈ R, SubEq y r) : ∃ r ∈ R, SubEq x r :=
  hsub.elim fun r hr => ⟨r, hr.1, Or.inr (subOf_trans_subEq (.child hc) hr.2)⟩

/-! ### immediate-premise witnesses, named per constructor arm so the
inversion auxiliaries and their strict-leaf proofs produce the same witness
term at a `.conv` (or matching) node. -/

def convChildFst {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (h : HasTyT E n Γ e A) (hc : ConvT E n Γ A B (.sort u)) :
    Child (.ty h) (.ty (.conv Γ e A B u h hc)) := by
  show (Jd.ty h : Jd E n) ∈ ([Jd.ty h, Jd.cv hc] : List (Jd E n))
  exact .head _

def convChildSnd {Γ : LCtx} {e A B : Expr Nat} {u : Level}
    (h : HasTyT E n Γ e A) (hc : ConvT E n Γ A B (.sort u)) :
    Child (.cv hc) (.ty (.conv Γ e A B u h hc)) := by
  show (Jd.cv hc : Jd E n) ∈ ([Jd.ty h, Jd.cv hc] : List (Jd E n))
  exact .tail _ (.head _)

private def appChildFst {Γ : LCtx} {f a A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A) :
    Child (.ty hf) (.ty (.app Γ f a A B hf ha)) := by
  show (Jd.ty hf : Jd E n) ∈ ([Jd.ty hf, Jd.ty ha] : List (Jd E n))
  exact .head _

private def appChildSnd {Γ : LCtx} {f a A B : Expr Nat}
    (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A) :
    Child (.ty ha) (.ty (.app Γ f a A B hf ha)) := by
  show (Jd.ty ha : Jd E n) ∈ ([Jd.ty hf, Jd.ty ha] : List (Jd E n))
  exact .tail _ (.head _)

def lamChildFst {Γ : LCtx} {A body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hb : HasTyT E n (.assumption A :: Γ) body B) :
    Child (.ty hA) (.ty (.lam Γ A u body B hA hb)) := by
  show (Jd.ty hA : Jd E n) ∈ ([Jd.ty hA, Jd.ty hb] : List (Jd E n))
  exact .head _

def lamChildSnd {Γ : LCtx} {A body B : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hb : HasTyT E n (.assumption A :: Γ) body B) :
    Child (.ty hb) (.ty (.lam Γ A u body B hA hb)) := by
  show (Jd.ty hb : Jd E n) ∈ ([Jd.ty hA, Jd.ty hb] : List (Jd E n))
  exact .tail _ (.head _)

private def piChildFst {Γ : LCtx} {A B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)) :
    Child (.ty hA) (.ty (.pi Γ A u B v hA hB)) := by
  show (Jd.ty hA : Jd E n) ∈ ([Jd.ty hA, Jd.ty hB] : List (Jd E n))
  exact .head _

private def piChildSnd {Γ : LCtx} {A B : Expr Nat} {u v : Level}
    (hA : HasTyT E n Γ A (.sort u))
    (hB : HasTyT E n (.assumption A :: Γ) B (.sort v)) :
    Child (.ty hB) (.ty (.pi Γ A u B v hA hB)) := by
  show (Jd.ty hB : Jd E n) ∈ ([Jd.ty hA, Jd.ty hB] : List (Jd E n))
  exact .tail _ (.head _)

private def letEChildFst {Γ : LCtx} {A value B body : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B) :
    Child (.ty hA) (.ty (.letE Γ A u value B body hA hv hb)) := by
  show (Jd.ty hA : Jd E n) ∈ ([Jd.ty hA, Jd.ty hv, Jd.ty hb] : List (Jd E n))
  exact .head _

def letEChildSnd {Γ : LCtx} {A value B body : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B) :
    Child (.ty hv) (.ty (.letE Γ A u value B body hA hv hb)) := by
  show (Jd.ty hv : Jd E n) ∈ ([Jd.ty hA, Jd.ty hv, Jd.ty hb] : List (Jd E n))
  exact .tail _ (.head _)

def letEChildThd {Γ : LCtx} {A value B body : Expr Nat} {u : Level}
    (hA : HasTyT E n Γ A (.sort u)) (hv : HasTyT E n Γ value A)
    (hb : HasTyT E n (.letBinding A value :: Γ) body B) :
    Child (.ty hb) (.ty (.letE Γ A u value B body hA hv hb)) := by
  show (Jd.ty hb : Jd E n) ∈ ([Jd.ty hA, Jd.ty hv, Jd.ty hb] : List (Jd E n))
  exact .tail _ (.tail _ (.head _))

private def litChild {Γ : LCtx} {t : Nat} {T : Expr Nat}
    (hexp : HasTyT E n Γ (natExpand t) T) :
    Child (.ty hexp) (.ty (.lit Γ t T hexp)) := by
  show (Jd.ty hexp : Jd E n) ∈ ([Jd.ty hexp] : List (Jd E n))
  exact .head _

/-! ### output structures (the plain `Σ'`/`×'` tuples as named records, each
with a `.leaves`) -/

/-- `app`-inversion output at provenance level. -/
structure EvInvApp (R : List (Jd E n)) (Γ : LCtx) (f a T : Expr Nat) where
  A : Expr Nat
  B : Expr Nat
  hf : EvTy R Γ f (.pi A B)
  ha : EvTy R Γ a A
  hc : EvTc R Γ (instantiate0 a B) T

/-- `lam`-inversion output at provenance level. -/
structure EvInvLam (R : List (Jd E n)) (Γ : LCtx) (A body T : Expr Nat) where
  u : Level
  B : Expr Nat
  hA : EvTy R Γ A (.sort u)
  hb : EvTy R (.assumption A :: Γ) body B
  hc : EvTc R Γ (.pi A B) T

/-- `pi`-inversion output at provenance level. -/
structure EvInvPi (R : List (Jd E n)) (Γ : LCtx) (A B T : Expr Nat) where
  u : Level
  v : Level
  hA : EvTy R Γ A (.sort u)
  hB : EvTy R (.assumption A :: Γ) B (.sort v)
  hc : EvTc R Γ (.sort (.imax u v)) T

/-- `letE`-inversion output at provenance level. -/
structure EvInvLetE (R : List (Jd E n)) (Γ : LCtx) (A value body T : Expr Nat)
    where
  u : Level
  B : Expr Nat
  hA : EvTy R Γ A (.sort u)
  hv : EvTy R Γ value A
  hb : EvTy R (.letBinding A value :: Γ) body B
  hc : EvTc R Γ (instantiate0 value B) T

/-- `bvar`-inversion output at provenance level (no judgment fields; the chain
    is the only Ev). -/
structure EvInvBvar (R : List (Jd E n)) (Γ : LCtx) (i : Nat) (T : Expr Nat)
    where
  A : Expr Nat
  hlk : lookupType Γ i = some A
  hc : EvTc R Γ A T

/-- `const`-inversion output at provenance level (non-judgment payload
    unchanged; the chain is the only Ev). -/
structure EvInvConst (E : ResolvedEnv) (n : Nat) (R : List (Jd E n))
    (Γ : LCtx) (r : Nat) (ls : List Level) (T : Expr Nat) where
  m : CheckedMember
  hres : E.members r = some m
  hlen : ls.length = m.arity
  hwf : levelsBounded n ls = true
  hc : EvTc R Γ (instantiateLevels ls m.mtype) T

/-- `lit`-inversion output at provenance level. -/
structure EvInvLit (R : List (Jd E n)) (Γ : LCtx) (t : Nat) (T : Expr Nat) where
  T' : Expr Nat
  hnat : EvTy R Γ (natExpand t) T'
  hc : EvTc R Γ T' T

def EvInvApp.leaves (x : EvInvApp R Γ f a T) : List (Jd E n) :=
  x.hf.leaves ++ x.ha.leaves ++ x.hc.leaves

def EvInvLam.leaves (x : EvInvLam R Γ A body T) : List (Jd E n) :=
  x.hA.leaves ++ x.hb.leaves ++ x.hc.leaves

def EvInvPi.leaves (x : EvInvPi R Γ A B T) : List (Jd E n) :=
  x.hA.leaves ++ x.hB.leaves ++ x.hc.leaves

def EvInvLetE.leaves (x : EvInvLetE R Γ A value body T) : List (Jd E n) :=
  x.hA.leaves ++ x.hv.leaves ++ x.hb.leaves ++ x.hc.leaves

def EvInvBvar.leaves (x : EvInvBvar R Γ i T) : List (Jd E n) := x.hc.leaves

def EvInvConst.leaves (x : EvInvConst E n R Γ r ls T) : List (Jd E n) :=
  x.hc.leaves

def EvInvLit.leaves (x : EvInvLit R Γ t T) : List (Jd E n) :=
  x.hnat.leaves ++ x.hc.leaves

/-! ### inversion auxiliaries — the plain match on the `lit` payload,
premises re-wrapped as `lit`s certified by `certOfChild` -/

private def EvTy.invAppAux {f a : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (∃ r ∈ R, SubEq (.ty d) r) → e = .app f a → EvInvApp R Γ f a T
  | _, _, _, .app _ _ _ _ _ hf ha, hsub, heq => by
      injection heq with h1 h2
      subst h1; subst h2
      exact ⟨_, _, .lit hf (certOfChild (appChildFst hf ha) hsub),
        .lit ha (certOfChild (appChildSnd hf ha) hsub), .refl _ _⟩
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq =>
      let r := EvTy.invAppAux h (certOfChild (convChildFst h hc) hsub) heq
      ⟨r.A, r.B, r.hf, r.ha,
        .trans r.hc (.ofCv u (.lit hc (certOfChild (convChildSnd h hc) hsub)))⟩
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def EvTy.invLamAux {A body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (∃ r ∈ R, SubEq (.ty d) r) → e = .lam A body → EvInvLam R Γ A body T
  | _, _, _, .lam _ _ _ _ _ hA hb, hsub, heq => by
      injection heq with h1 h2
      subst h1; subst h2
      exact ⟨_, _, .lit hA (certOfChild (lamChildFst hA hb) hsub),
        .lit hb (certOfChild (lamChildSnd hA hb) hsub), .refl _ _⟩
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq =>
      let r := EvTy.invLamAux h (certOfChild (convChildFst h hc) hsub) heq
      ⟨r.u, r.B, r.hA, r.hb,
        .trans r.hc (.ofCv u (.lit hc (certOfChild (convChildSnd h hc) hsub)))⟩
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def EvTy.invPiAux {A B : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (∃ r ∈ R, SubEq (.ty d) r) → e = .pi A B → EvInvPi R Γ A B T
  | _, _, _, .pi _ _ _ _ _ hA hB, hsub, heq => by
      injection heq with h1 h2
      subst h1; subst h2
      exact ⟨_, _, .lit hA (certOfChild (piChildFst hA hB) hsub),
        .lit hB (certOfChild (piChildSnd hA hB) hsub), .refl _ _⟩
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq =>
      let r := EvTy.invPiAux h (certOfChild (convChildFst h hc) hsub) heq
      ⟨r.u, r.v, r.hA, r.hB,
        .trans r.hc (.ofCv u (.lit hc (certOfChild (convChildSnd h hc) hsub)))⟩
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def EvTy.invLetEAux {A value body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (∃ r ∈ R, SubEq (.ty d) r) → e = .letE A value body →
    EvInvLetE R Γ A value body T
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb, hsub, heq => by
      injection heq with h1 h2 h3
      subst h1; subst h2; subst h3
      exact ⟨_, _, .lit hA (certOfChild (letEChildFst hA hv hb) hsub),
        .lit hv (certOfChild (letEChildSnd hA hv hb) hsub),
        .lit hb (certOfChild (letEChildThd hA hv hb) hsub), .refl _ _⟩
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq =>
      let r := EvTy.invLetEAux h (certOfChild (convChildFst h hc) hsub) heq
      ⟨r.u, r.B, r.hA, r.hv, r.hb,
        .trans r.hc (.ofCv u (.lit hc (certOfChild (convChildSnd h hc) hsub)))⟩
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def EvTy.invBvarAux {i : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (∃ r ∈ R, SubEq (.ty d) r) → e = .bvar i → EvInvBvar R Γ i T
  | _, _, _, .bvar _ _ _ h, _, heq => by
      injection heq with heq'
      subst heq'
      exact ⟨_, h, .refl _ _⟩
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq =>
      let r := EvTy.invBvarAux h (certOfChild (convChildFst h hc) hsub) heq
      ⟨r.A, r.hlk,
        .trans r.hc (.ofCv u (.lit hc (certOfChild (convChildSnd h hc) hsub)))⟩
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def EvTy.invConstAux {r : Nat} {ls : List Level} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (∃ r' ∈ R, SubEq (.ty d) r') → e = .const r ls →
    EvInvConst E n R Γ r ls T
  | _, _, _, .const _ _ _ m hres hlen hwf, _, heq => by
      injection heq with h1 h2
      subst h2; subst h1
      exact ⟨m, hres, hlen, hwf, .refl _ _⟩
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq =>
      let ri := EvTy.invConstAux h (certOfChild (convChildFst h hc) hsub) heq
      ⟨ri.m, ri.hres, ri.hlen, ri.hwf,
        .trans ri.hc (.ofCv u (.lit hc (certOfChild (convChildSnd h hc) hsub)))⟩
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def EvTy.invLitAux {t : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (∃ r ∈ R, SubEq (.ty d) r) → e = .lit t → EvInvLit R Γ t T
  | _, _, _, .lit _ _ _ hexp, hsub, heq => by
      injection heq with heq'
      subst heq'
      exact ⟨_, .lit hexp (certOfChild (litChild hexp) hsub), .refl _ _⟩
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq =>
      let r := EvTy.invLitAux h (certOfChild (convChildFst h hc) hsub) heq
      ⟨r.T', r.hnat,
        .trans r.hc (.ofCv u (.lit hc (certOfChild (convChildSnd h hc) hsub)))⟩
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq

private def EvTy.invSortTAux {l : Level} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (∃ r ∈ R, SubEq (.ty d) r) → e = .sort l →
    EvTc R Γ (.sort (.succ l)) T
  | _, _, _, .sort _ _, _, heq => by
      injection heq with hl
      subst hl
      exact .refl _ _
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq =>
      .trans (EvTy.invSortTAux h (certOfChild (convChildFst h hc) hsub) heq)
        (.ofCv u (.lit hc (certOfChild (convChildSnd h hc) hsub)))
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

/-! ### strict-leaf theorems for the auxiliaries: every output leaf is a
strict sub-derivation of the literal root. -/

private def EvTy.invAppAuxStrict {f a : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (hsub : ∃ r ∈ R, SubEq (.ty d) r) → (heq : e = .app f a) →
    ∀ ℓ ∈ (EvTy.invAppAux d hsub heq).leaves, SubOf ℓ (.ty d)
  | _, _, _, .app _ _ _ _ _ hf ha, _, heq => fun ℓ hℓ => by
      injection heq with h1 h2
      subst h1; subst h2
      simp only [EvTy.invAppAux, EvInvApp.leaves, EvTy.leaves, EvTc.leaves,
        List.append_assoc, List.nil_append, List.cons_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, false_or] at hℓ
      rcases hℓ with rfl | rfl
      · exact .child (appChildFst hf ha)
      · exact .child (appChildSnd hf ha)
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq => fun ℓ hℓ => by
      simp only [EvTy.invAppAux, EvInvApp.leaves, EvTc.leaves, EvCv.leaves,
        EvTy.leaves, List.mem_append, or_assoc] at hℓ
      rcases hℓ with hm | hm | hm | hm
      · exact .trans
          (EvTy.invAppAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvApp.leaves, List.mem_append, or_assoc]
                exact .inl hm))
          (.child (convChildFst h hc))
      · exact .trans
          (EvTy.invAppAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvApp.leaves, List.mem_append, or_assoc]
                exact .inr (.inl hm)))
          (.child (convChildFst h hc))
      · exact .trans
          (EvTy.invAppAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvApp.leaves, List.mem_append, or_assoc]
                exact .inr (.inr hm)))
          (.child (convChildFst h hc))
      · rcases (List.mem_cons.mp hm) with rfl | hm
        · exact .child (convChildSnd h hc)
        · exact absurd hm (List.not_mem_nil _)
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def EvTy.invLamAuxStrict {A body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (hsub : ∃ r ∈ R, SubEq (.ty d) r) → (heq : e = .lam A body) →
    ∀ ℓ ∈ (EvTy.invLamAux d hsub heq).leaves, SubOf ℓ (.ty d)
  | _, _, _, .lam _ _ _ _ _ hA hb, _, heq => fun ℓ hℓ => by
      injection heq with h1 h2
      subst h1; subst h2
      simp only [EvTy.invLamAux, EvInvLam.leaves, EvTy.leaves, EvTc.leaves,
        List.append_assoc, List.nil_append, List.cons_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, false_or] at hℓ
      rcases hℓ with rfl | rfl
      · exact .child (lamChildFst hA hb)
      · exact .child (lamChildSnd hA hb)
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq => fun ℓ hℓ => by
      simp only [EvTy.invLamAux, EvInvLam.leaves, EvTc.leaves, EvCv.leaves,
        EvTy.leaves, List.mem_append, or_assoc] at hℓ
      rcases hℓ with hm | hm | hm | hm
      · exact .trans
          (EvTy.invLamAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvLam.leaves, List.mem_append, or_assoc]
                exact .inl hm))
          (.child (convChildFst h hc))
      · exact .trans
          (EvTy.invLamAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvLam.leaves, List.mem_append, or_assoc]
                exact .inr (.inl hm)))
          (.child (convChildFst h hc))
      · exact .trans
          (EvTy.invLamAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvLam.leaves, List.mem_append, or_assoc]
                exact .inr (.inr hm)))
          (.child (convChildFst h hc))
      · rcases (List.mem_cons.mp hm) with rfl | hm
        · exact .child (convChildSnd h hc)
        · exact absurd hm (List.not_mem_nil _)
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def EvTy.invPiAuxStrict {A B : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (hsub : ∃ r ∈ R, SubEq (.ty d) r) → (heq : e = .pi A B) →
    ∀ ℓ ∈ (EvTy.invPiAux d hsub heq).leaves, SubOf ℓ (.ty d)
  | _, _, _, .pi _ _ _ _ _ hA hB, _, heq => fun ℓ hℓ => by
      injection heq with h1 h2
      subst h1; subst h2
      simp only [EvTy.invPiAux, EvInvPi.leaves, EvTy.leaves, EvTc.leaves,
        List.append_assoc, List.nil_append, List.cons_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, false_or] at hℓ
      rcases hℓ with rfl | rfl
      · exact .child (piChildFst hA hB)
      · exact .child (piChildSnd hA hB)
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq => fun ℓ hℓ => by
      simp only [EvTy.invPiAux, EvInvPi.leaves, EvTc.leaves, EvCv.leaves,
        EvTy.leaves, List.mem_append, or_assoc] at hℓ
      rcases hℓ with hm | hm | hm | hm
      · exact .trans
          (EvTy.invPiAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvPi.leaves, List.mem_append, or_assoc]
                exact .inl hm))
          (.child (convChildFst h hc))
      · exact .trans
          (EvTy.invPiAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvPi.leaves, List.mem_append, or_assoc]
                exact .inr (.inl hm)))
          (.child (convChildFst h hc))
      · exact .trans
          (EvTy.invPiAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvPi.leaves, List.mem_append, or_assoc]
                exact .inr (.inr hm)))
          (.child (convChildFst h hc))
      · rcases (List.mem_cons.mp hm) with rfl | hm
        · exact .child (convChildSnd h hc)
        · exact absurd hm (List.not_mem_nil _)
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def EvTy.invLetEAuxStrict {A value body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (hsub : ∃ r ∈ R, SubEq (.ty d) r) → (heq : e = .letE A value body) →
    ∀ ℓ ∈ (EvTy.invLetEAux d hsub heq).leaves, SubOf ℓ (.ty d)
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb, _, heq => fun ℓ hℓ => by
      injection heq with h1 h2 h3
      subst h1; subst h2; subst h3
      simp only [EvTy.invLetEAux, EvInvLetE.leaves, EvTy.leaves, EvTc.leaves,
        List.append_assoc, List.nil_append, List.cons_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, false_or] at hℓ
      rcases hℓ with rfl | rfl | rfl
      · exact .child (letEChildFst hA hv hb)
      · exact .child (letEChildSnd hA hv hb)
      · exact .child (letEChildThd hA hv hb)
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq => fun ℓ hℓ => by
      simp only [EvTy.invLetEAux, EvInvLetE.leaves, EvTc.leaves, EvCv.leaves,
        EvTy.leaves, List.mem_append, or_assoc] at hℓ
      rcases hℓ with hm | hm | hm | hm | hm
      · exact .trans
          (EvTy.invLetEAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvLetE.leaves, List.mem_append, or_assoc]
                exact .inl hm))
          (.child (convChildFst h hc))
      · exact .trans
          (EvTy.invLetEAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvLetE.leaves, List.mem_append, or_assoc]
                exact .inr (.inl hm)))
          (.child (convChildFst h hc))
      · exact .trans
          (EvTy.invLetEAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvLetE.leaves, List.mem_append, or_assoc]
                exact .inr (.inr (.inl hm))))
          (.child (convChildFst h hc))
      · exact .trans
          (EvTy.invLetEAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvLetE.leaves, List.mem_append, or_assoc]
                exact .inr (.inr (.inr hm))))
          (.child (convChildFst h hc))
      · rcases (List.mem_cons.mp hm) with rfl | hm
        · exact .child (convChildSnd h hc)
        · exact absurd hm (List.not_mem_nil _)
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def EvTy.invBvarAuxStrict {i : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (hsub : ∃ r ∈ R, SubEq (.ty d) r) → (heq : e = .bvar i) →
    ∀ ℓ ∈ (EvTy.invBvarAux d hsub heq).leaves, SubOf ℓ (.ty d)
  | _, _, _, .bvar _ _ _ _, _, heq => fun _ hℓ => by
      injection heq with heq'
      subst heq'
      simp only [EvTy.invBvarAux, EvInvBvar.leaves, EvTc.leaves,
        List.not_mem_nil] at hℓ
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq => fun ℓ hℓ => by
      simp only [EvTy.invBvarAux, EvInvBvar.leaves, EvTc.leaves, EvCv.leaves,
        EvTy.leaves, List.mem_append, or_assoc] at hℓ
      rcases hℓ with hm | hm
      · exact .trans
          (EvTy.invBvarAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            hm)
          (.child (convChildFst h hc))
      · rcases (List.mem_cons.mp hm) with rfl | hm
        · exact .child (convChildSnd h hc)
        · exact absurd hm (List.not_mem_nil _)
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def EvTy.invConstAuxStrict {r : Nat} {ls : List Level} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (hsub : ∃ r' ∈ R, SubEq (.ty d) r') → (heq : e = .const r ls) →
    ∀ ℓ ∈ (EvTy.invConstAux d hsub heq).leaves, SubOf ℓ (.ty d)
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => fun _ hℓ => by
      injection heq with h1 h2
      subst h2; subst h1
      simp only [EvTy.invConstAux, EvInvConst.leaves, EvTc.leaves,
        List.not_mem_nil] at hℓ
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq => fun ℓ hℓ => by
      simp only [EvTy.invConstAux, EvInvConst.leaves, EvTc.leaves, EvCv.leaves,
        EvTy.leaves, List.mem_append, or_assoc] at hℓ
      rcases hℓ with hm | hm
      · exact .trans
          (EvTy.invConstAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            hm)
          (.child (convChildFst h hc))
      · rcases (List.mem_cons.mp hm) with rfl | hm
        · exact .child (convChildSnd h hc)
        · exact absurd hm (List.not_mem_nil _)
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def EvTy.invLitAuxStrict {t : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (hsub : ∃ r ∈ R, SubEq (.ty d) r) → (heq : e = .lit t) →
    ∀ ℓ ∈ (EvTy.invLitAux d hsub heq).leaves, SubOf ℓ (.ty d)
  | _, _, _, .lit _ _ _ hexp, _, heq => fun ℓ hℓ => by
      injection heq with heq'
      subst heq'
      simp only [EvTy.invLitAux, EvInvLit.leaves, EvTy.leaves, EvTc.leaves,
        List.append_assoc, List.nil_append, List.cons_append, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, false_or] at hℓ
      subst hℓ
      exact .child (litChild hexp)
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq => fun ℓ hℓ => by
      simp only [EvTy.invLitAux, EvInvLit.leaves, EvTc.leaves, EvCv.leaves,
        EvTy.leaves, List.mem_append, or_assoc] at hℓ
      rcases hℓ with hm | hm | hm
      · exact .trans
          (EvTy.invLitAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvLit.leaves, List.mem_append, or_assoc]
                exact .inl hm))
          (.child (convChildFst h hc))
      · exact .trans
          (EvTy.invLitAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            (by simp only [EvInvLit.leaves, List.mem_append, or_assoc]
                exact .inr hm))
          (.child (convChildFst h hc))
      · rcases (List.mem_cons.mp hm) with rfl | hm
        · exact .child (convChildSnd h hc)
        · exact absurd hm (List.not_mem_nil _)
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq

private def EvTy.invSortTAuxStrict {l : Level} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (hsub : ∃ r ∈ R, SubEq (.ty d) r) → (heq : e = .sort l) →
    ∀ ℓ ∈ (EvTy.invSortTAux d hsub heq).leaves, SubOf ℓ (.ty d)
  | _, _, _, .sort _ _, _, heq => fun _ hℓ => by
      injection heq with hl
      subst hl
      simp only [EvTy.invSortTAux, EvTc.leaves, List.not_mem_nil] at hℓ
  | _, _, _, .conv _ _ _ _ u h hc, hsub, heq => fun ℓ hℓ => by
      simp only [EvTy.invSortTAux, EvTc.leaves, EvCv.leaves, EvTy.leaves,
        List.mem_append, or_assoc] at hℓ
      rcases hℓ with hm | hm
      · exact .trans
          (EvTy.invSortTAuxStrict h (certOfChild (convChildFst h hc) hsub) heq ℓ
            hm)
          (.child (convChildFst h hc))
      · rcases (List.mem_cons.mp hm) with rfl | hm
        · exact .child (convChildSnd h hc)
        · exact absurd hm (List.not_mem_nil _)
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

/-! ### the inversions themselves: `lit` calls the auxiliary, `rety`
recurses and appends the chain, `wk`/`esub` are excluded by `hD`. -/

/-- `app`-inversion on provenance (lit-rooted inputs). -/
def EvTy.invApp {f a : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    D.litRooted = true → e = .app f a → EvInvApp R Γ f a T
  | _, _, _, .lit d hsub, _, heq => EvTy.invAppAux d hsub heq
  | _, _, _, .rety D c, hD, heq =>
      let r := D.invApp hD heq
      ⟨r.A, r.B, r.hf, r.ha, .trans r.hc c⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-- `lam`-inversion on provenance (lit-rooted inputs). -/
def EvTy.invLam {A body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    D.litRooted = true → e = .lam A body → EvInvLam R Γ A body T
  | _, _, _, .lit d hsub, _, heq => EvTy.invLamAux d hsub heq
  | _, _, _, .rety D c, hD, heq =>
      let r := D.invLam hD heq
      ⟨r.u, r.B, r.hA, r.hb, .trans r.hc c⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-- `pi`-inversion on provenance (lit-rooted inputs). -/
def EvTy.invPi {A B : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    D.litRooted = true → e = .pi A B → EvInvPi R Γ A B T
  | _, _, _, .lit d hsub, _, heq => EvTy.invPiAux d hsub heq
  | _, _, _, .rety D c, hD, heq =>
      let r := D.invPi hD heq
      ⟨r.u, r.v, r.hA, r.hB, .trans r.hc c⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-- `letE`-inversion on provenance (lit-rooted inputs). -/
def EvTy.invLetE {A value body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    D.litRooted = true → e = .letE A value body → EvInvLetE R Γ A value body T
  | _, _, _, .lit d hsub, _, heq => EvTy.invLetEAux d hsub heq
  | _, _, _, .rety D c, hD, heq =>
      let r := D.invLetE hD heq
      ⟨r.u, r.B, r.hA, r.hv, r.hb, .trans r.hc c⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-- `bvar`-inversion on provenance (lit-rooted inputs). -/
def EvTy.invBvar {i : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    D.litRooted = true → e = .bvar i → EvInvBvar R Γ i T
  | _, _, _, .lit d hsub, _, heq => EvTy.invBvarAux d hsub heq
  | _, _, _, .rety D c, hD, heq =>
      let r := D.invBvar hD heq
      ⟨r.A, r.hlk, .trans r.hc c⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-- `const`-inversion on provenance (lit-rooted inputs). -/
def EvTy.invConst {r : Nat} {ls : List Level} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    D.litRooted = true → e = .const r ls → EvInvConst E n R Γ r ls T
  | _, _, _, .lit d hsub, _, heq => EvTy.invConstAux d hsub heq
  | _, _, _, .rety D c, hD, heq =>
      let r := D.invConst hD heq
      ⟨r.m, r.hres, r.hlen, r.hwf, .trans r.hc c⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-- `lit`-inversion on provenance (lit-rooted inputs). -/
def EvTy.invLit {t : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    D.litRooted = true → e = .lit t → EvInvLit R Γ t T
  | _, _, _, .lit d hsub, _, heq => EvTy.invLitAux d hsub heq
  | _, _, _, .rety D c, hD, heq =>
      let r := D.invLit hD heq
      ⟨r.T', r.hnat, .trans r.hc c⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-- `sort`-inversion on provenance (lit-rooted inputs): a `TyConvT`-shaped
    output is an `EvTc`. -/
def EvTy.invSortT {l : Level} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    D.litRooted = true → e = .sort l → EvTc R Γ (.sort (.succ l)) T
  | _, _, _, .lit d hsub, _, heq => EvTy.invSortTAux d hsub heq
  | _, _, _, .rety D c, hD, heq => .trans (D.invSortT hD heq) c
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-! ### leaf tracing: every output leaf sits at-or-below an input leaf -/

def EvTy.invApp_leaves {f a : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .app f a) →
    ∀ ℓ ∈ (D.invApp hD heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, _, heq => fun ℓ hℓ =>
      ⟨.ty d, by
        show (Jd.ty d : Jd E n) ∈ ([Jd.ty d] : List (Jd E n)); exact .head _,
        Or.inr (EvTy.invAppAuxStrict d hsub heq ℓ hℓ)⟩
  | _, _, _, .rety D c, hD, heq => fun ℓ hℓ => by
      have hnorm : ((EvTy.rety D c).invApp hD heq).leaves =
          (D.invApp hD heq).leaves ++ c.leaves := by
        show EvInvApp.leaves ⟨(D.invApp hD heq).A, (D.invApp hD heq).B, (D.invApp hD heq).hf, (D.invApp hD heq).ha, .trans (D.invApp hD heq).hc c⟩ = _
        simp only [EvInvApp.leaves, EvTc.leaves, List.append_assoc]
      rw [hnorm] at hℓ
      rcases (List.mem_append.mp hℓ) with hm | hm
      · obtain ⟨ℓ', hℓ', s⟩ := EvTy.invApp_leaves D hD heq ℓ hm
        exact ⟨ℓ', List.mem_append.mpr (.inl hℓ'), s⟩
      · exact ⟨ℓ, List.mem_append.mpr (.inr hm), Or.inl rfl⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

def EvTy.invLam_leaves {A body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .lam A body) →
    ∀ ℓ ∈ (D.invLam hD heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, _, heq => fun ℓ hℓ =>
      ⟨.ty d, by
        show (Jd.ty d : Jd E n) ∈ ([Jd.ty d] : List (Jd E n)); exact .head _,
        Or.inr (EvTy.invLamAuxStrict d hsub heq ℓ hℓ)⟩
  | _, _, _, .rety D c, hD, heq => fun ℓ hℓ => by
      have hnorm : ((EvTy.rety D c).invLam hD heq).leaves =
          (D.invLam hD heq).leaves ++ c.leaves := by
        show EvInvLam.leaves ⟨(D.invLam hD heq).u, (D.invLam hD heq).B, (D.invLam hD heq).hA, (D.invLam hD heq).hb, .trans (D.invLam hD heq).hc c⟩ = _
        simp only [EvInvLam.leaves, EvTc.leaves, List.append_assoc]
      rw [hnorm] at hℓ
      rcases (List.mem_append.mp hℓ) with hm | hm
      · obtain ⟨ℓ', hℓ', s⟩ := EvTy.invLam_leaves D hD heq ℓ hm
        exact ⟨ℓ', List.mem_append.mpr (.inl hℓ'), s⟩
      · exact ⟨ℓ, List.mem_append.mpr (.inr hm), Or.inl rfl⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

def EvTy.invPi_leaves {A B : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .pi A B) →
    ∀ ℓ ∈ (D.invPi hD heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, _, heq => fun ℓ hℓ =>
      ⟨.ty d, by
        show (Jd.ty d : Jd E n) ∈ ([Jd.ty d] : List (Jd E n)); exact .head _,
        Or.inr (EvTy.invPiAuxStrict d hsub heq ℓ hℓ)⟩
  | _, _, _, .rety D c, hD, heq => fun ℓ hℓ => by
      have hnorm : ((EvTy.rety D c).invPi hD heq).leaves =
          (D.invPi hD heq).leaves ++ c.leaves := by
        show EvInvPi.leaves ⟨(D.invPi hD heq).u, (D.invPi hD heq).v, (D.invPi hD heq).hA, (D.invPi hD heq).hB, .trans (D.invPi hD heq).hc c⟩ = _
        simp only [EvInvPi.leaves, EvTc.leaves, List.append_assoc]
      rw [hnorm] at hℓ
      rcases (List.mem_append.mp hℓ) with hm | hm
      · obtain ⟨ℓ', hℓ', s⟩ := EvTy.invPi_leaves D hD heq ℓ hm
        exact ⟨ℓ', List.mem_append.mpr (.inl hℓ'), s⟩
      · exact ⟨ℓ, List.mem_append.mpr (.inr hm), Or.inl rfl⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

def EvTy.invLetE_leaves {A value body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .letE A value body) →
    ∀ ℓ ∈ (D.invLetE hD heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, _, heq => fun ℓ hℓ =>
      ⟨.ty d, by
        show (Jd.ty d : Jd E n) ∈ ([Jd.ty d] : List (Jd E n)); exact .head _,
        Or.inr (EvTy.invLetEAuxStrict d hsub heq ℓ hℓ)⟩
  | _, _, _, .rety D c, hD, heq => fun ℓ hℓ => by
      have hnorm : ((EvTy.rety D c).invLetE hD heq).leaves =
          (D.invLetE hD heq).leaves ++ c.leaves := by
        show EvInvLetE.leaves ⟨(D.invLetE hD heq).u, (D.invLetE hD heq).B, (D.invLetE hD heq).hA, (D.invLetE hD heq).hv, (D.invLetE hD heq).hb, .trans (D.invLetE hD heq).hc c⟩ = _
        simp only [EvInvLetE.leaves, EvTc.leaves, List.append_assoc]
      rw [hnorm] at hℓ
      rcases (List.mem_append.mp hℓ) with hm | hm
      · obtain ⟨ℓ', hℓ', s⟩ := EvTy.invLetE_leaves D hD heq ℓ hm
        exact ⟨ℓ', List.mem_append.mpr (.inl hℓ'), s⟩
      · exact ⟨ℓ, List.mem_append.mpr (.inr hm), Or.inl rfl⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

def EvTy.invBvar_leaves {i : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .bvar i) →
    ∀ ℓ ∈ (D.invBvar hD heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, _, heq => fun ℓ hℓ =>
      ⟨.ty d, by
        show (Jd.ty d : Jd E n) ∈ ([Jd.ty d] : List (Jd E n)); exact .head _,
        Or.inr (EvTy.invBvarAuxStrict d hsub heq ℓ hℓ)⟩
  | _, _, _, .rety D c, hD, heq => fun ℓ hℓ => by
      have hnorm : ((EvTy.rety D c).invBvar hD heq).leaves =
          (D.invBvar hD heq).leaves ++ c.leaves := by
        show EvInvBvar.leaves ⟨(D.invBvar hD heq).A, (D.invBvar hD heq).hlk, .trans (D.invBvar hD heq).hc c⟩ = _
        simp only [EvInvBvar.leaves, EvTc.leaves, List.append_assoc]
      rw [hnorm] at hℓ
      rcases (List.mem_append.mp hℓ) with hm | hm
      · obtain ⟨ℓ', hℓ', s⟩ := EvTy.invBvar_leaves D hD heq ℓ hm
        exact ⟨ℓ', List.mem_append.mpr (.inl hℓ'), s⟩
      · exact ⟨ℓ, List.mem_append.mpr (.inr hm), Or.inl rfl⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

def EvTy.invConst_leaves {r : Nat} {ls : List Level} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .const r ls) →
    ∀ ℓ ∈ (D.invConst hD heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, _, heq => fun ℓ hℓ =>
      ⟨.ty d, by
        show (Jd.ty d : Jd E n) ∈ ([Jd.ty d] : List (Jd E n)); exact .head _,
        Or.inr (EvTy.invConstAuxStrict d hsub heq ℓ hℓ)⟩
  | _, _, _, .rety D c, hD, heq => fun ℓ hℓ => by
      have hnorm : ((EvTy.rety D c).invConst hD heq).leaves =
          (D.invConst hD heq).leaves ++ c.leaves := by
        show EvInvConst.leaves ⟨(D.invConst hD heq).m, (D.invConst hD heq).hres, (D.invConst hD heq).hlen, (D.invConst hD heq).hwf, .trans (D.invConst hD heq).hc c⟩ = _
        simp only [EvInvConst.leaves, EvTc.leaves, List.append_assoc]
      rw [hnorm] at hℓ
      rcases (List.mem_append.mp hℓ) with hm | hm
      · obtain ⟨ℓ', hℓ', s⟩ := EvTy.invConst_leaves D hD heq ℓ hm
        exact ⟨ℓ', List.mem_append.mpr (.inl hℓ'), s⟩
      · exact ⟨ℓ, List.mem_append.mpr (.inr hm), Or.inl rfl⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

def EvTy.invLit_leaves {t : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .lit t) →
    ∀ ℓ ∈ (D.invLit hD heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, _, heq => fun ℓ hℓ =>
      ⟨.ty d, by
        show (Jd.ty d : Jd E n) ∈ ([Jd.ty d] : List (Jd E n)); exact .head _,
        Or.inr (EvTy.invLitAuxStrict d hsub heq ℓ hℓ)⟩
  | _, _, _, .rety D c, hD, heq => fun ℓ hℓ => by
      have hnorm : ((EvTy.rety D c).invLit hD heq).leaves =
          (D.invLit hD heq).leaves ++ c.leaves := by
        show EvInvLit.leaves ⟨(D.invLit hD heq).T', (D.invLit hD heq).hnat, .trans (D.invLit hD heq).hc c⟩ = _
        simp only [EvInvLit.leaves, EvTc.leaves, List.append_assoc]
      rw [hnorm] at hℓ
      rcases (List.mem_append.mp hℓ) with hm | hm
      · obtain ⟨ℓ', hℓ', s⟩ := EvTy.invLit_leaves D hD heq ℓ hm
        exact ⟨ℓ', List.mem_append.mpr (.inl hℓ'), s⟩
      · exact ⟨ℓ, List.mem_append.mpr (.inr hm), Or.inl rfl⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

def EvTy.invSortT_leaves {l : Level} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .sort l) →
    ∀ ℓ ∈ (D.invSortT hD heq).leaves, ∃ ℓ' ∈ D.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub, _, heq => fun ℓ hℓ =>
      ⟨.ty d, by
        show (Jd.ty d : Jd E n) ∈ ([Jd.ty d] : List (Jd E n)); exact .head _,
        Or.inr (EvTy.invSortTAuxStrict d hsub heq ℓ hℓ)⟩
  | _, _, _, .rety D c, hD, heq => fun ℓ hℓ => by
      have hnorm : ((EvTy.rety D c).invSortT hD heq).leaves =
          (D.invSortT hD heq).leaves ++ c.leaves := by
        show EvTc.leaves (.trans (D.invSortT hD heq) c) = _
        simp only [EvTc.leaves]
      rw [hnorm] at hℓ
      rcases (List.mem_append.mp hℓ) with hm | hm
      · obtain ⟨ℓ', hℓ', s⟩ := EvTy.invSortT_leaves D hD heq ℓ hm
        exact ⟨ℓ', List.mem_append.mpr (.inl hℓ'), s⟩
      · exact ⟨ℓ, List.mem_append.mpr (.inr hm), Or.inl rfl⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-! ### strict at a literal root: every output leaf is a strict
sub-derivation of the removed atom. -/

theorem EvTy.invApp_strict {f a : Expr Nat} {Γ : LCtx} {e T : Expr Nat}
    (d : HasTyT E n Γ e T) (hsub : ∃ r ∈ R, SubEq (.ty d) r)
    (heq : e = .app f a) :
    ∀ ℓ ∈ ((EvTy.lit d hsub).invApp rfl heq).leaves, SubOf ℓ (.ty d) :=
  EvTy.invAppAuxStrict d hsub heq

theorem EvTy.invLam_strict {A body : Expr Nat} {Γ : LCtx} {e T : Expr Nat}
    (d : HasTyT E n Γ e T) (hsub : ∃ r ∈ R, SubEq (.ty d) r)
    (heq : e = .lam A body) :
    ∀ ℓ ∈ ((EvTy.lit d hsub).invLam rfl heq).leaves, SubOf ℓ (.ty d) :=
  EvTy.invLamAuxStrict d hsub heq

theorem EvTy.invPi_strict {A B : Expr Nat} {Γ : LCtx} {e T : Expr Nat}
    (d : HasTyT E n Γ e T) (hsub : ∃ r ∈ R, SubEq (.ty d) r)
    (heq : e = .pi A B) :
    ∀ ℓ ∈ ((EvTy.lit d hsub).invPi rfl heq).leaves, SubOf ℓ (.ty d) :=
  EvTy.invPiAuxStrict d hsub heq

theorem EvTy.invLetE_strict {A value body : Expr Nat} {Γ : LCtx}
    {e T : Expr Nat}
    (d : HasTyT E n Γ e T) (hsub : ∃ r ∈ R, SubEq (.ty d) r)
    (heq : e = .letE A value body) :
    ∀ ℓ ∈ ((EvTy.lit d hsub).invLetE rfl heq).leaves, SubOf ℓ (.ty d) :=
  EvTy.invLetEAuxStrict d hsub heq

theorem EvTy.invBvar_strict {i : Nat} {Γ : LCtx} {e T : Expr Nat}
    (d : HasTyT E n Γ e T) (hsub : ∃ r ∈ R, SubEq (.ty d) r)
    (heq : e = .bvar i) :
    ∀ ℓ ∈ ((EvTy.lit d hsub).invBvar rfl heq).leaves, SubOf ℓ (.ty d) :=
  EvTy.invBvarAuxStrict d hsub heq

theorem EvTy.invConst_strict {r : Nat} {ls : List Level} {Γ : LCtx}
    {e T : Expr Nat}
    (d : HasTyT E n Γ e T) (hsub : ∃ r ∈ R, SubEq (.ty d) r)
    (heq : e = .const r ls) :
    ∀ ℓ ∈ ((EvTy.lit d hsub).invConst rfl heq).leaves, SubOf ℓ (.ty d) :=
  EvTy.invConstAuxStrict d hsub heq

theorem EvTy.invLit_strict {t : Nat} {Γ : LCtx} {e T : Expr Nat}
    (d : HasTyT E n Γ e T) (hsub : ∃ r ∈ R, SubEq (.ty d) r)
    (heq : e = .lit t) :
    ∀ ℓ ∈ ((EvTy.lit d hsub).invLit rfl heq).leaves, SubOf ℓ (.ty d) :=
  EvTy.invLitAuxStrict d hsub heq

theorem EvTy.invSortT_strict {l : Level} {Γ : LCtx} {e T : Expr Nat}
    (d : HasTyT E n Γ e T) (hsub : ∃ r ∈ R, SubEq (.ty d) r)
    (heq : e = .sort l) :
    ∀ ℓ ∈ ((EvTy.lit d hsub).invSortT rfl heq).leaves, SubOf ℓ (.ty d) :=
  EvTy.invSortTAuxStrict d hsub heq

/-! ### non-vacuity pins -/

private def pinΓ : LCtx :=
  [.assumption (.pi (.sort (.succ .zero)) (.sort (.succ (.succ .zero))))]

/-- `app (bvar 0) (sort 0)` typed in `pinΓ`, wrapped in one `.conv` node —
    the inversion's residual chain is a nontrivial `ofCv (lit …)` link. -/
private def pinAppConvT : HasTyT emptyEnv 0 pinΓ (.app (.bvar 0) (.sort .zero))
    (.sort (.succ (.succ .zero))) :=
  .conv pinΓ _ _ _ (.succ (.succ (.succ .zero)))
    (.app pinΓ (.bvar 0) (.sort .zero) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero)))
      (.bvar pinΓ 0 _ rfl)
      (.sort pinΓ .zero))
    (.refl pinΓ _ _ (.sort pinΓ (.succ (.succ .zero))))

private def pinAppLit : EvTy [.ty pinAppConvT] pinΓ
    (.app (.bvar 0) (.sort .zero)) (.sort (.succ (.succ .zero))) :=
  .lit pinAppConvT ⟨.ty pinAppConvT, .head _, .inl rfl⟩

/-- `_strict` at the conv-wrapped app: the residual chain's `ofCv (lit …)`
    leaf is a strict sub-derivation of the conv atom. -/
theorem pin_invApp_strict :
    ∀ ℓ ∈ (pinAppLit.invApp rfl rfl).leaves, SubOf ℓ (.ty pinAppConvT) :=
  EvTy.invApp_strict pinAppConvT ⟨.ty pinAppConvT, .head _, .inl rfl⟩ rfl

/-- a real Π typing of `pi (sort 0) (sort 0)`, at `emptyEnv`. -/
private def pinPiT : HasTyT emptyEnv 0 [] (.pi (.sort .zero) (.sort .zero))
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (pinSortT emptyEnv 0) (.sort [.assumption (.sort .zero)] .zero)

private def pinPiCv : ConvT emptyEnv 0 []
    (.sort (.imax (.succ .zero) (.succ .zero)))
    (.sort (.imax (.succ .zero) (.succ .zero)))
    (.sort (.succ (.imax (.succ .zero) (.succ .zero)))) :=
  .refl [] _ _ (.sort [] (.imax (.succ .zero) (.succ .zero)))

private def pinPiR : List (Jd emptyEnv 0) := [.ty pinPiT, .cv pinPiCv]

/-- the Π typing under one `rety`: the appended chain is exercised. -/
private def pinEvPi : EvTy pinPiR [] (.pi (.sort .zero) (.sort .zero))
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .rety (.lit pinPiT ⟨.ty pinPiT, .head _, .inl rfl⟩)
    (.ofCv _ (.lit pinPiCv ⟨.cv pinPiCv, .tail _ (.head _), .inl rfl⟩))

/-- `_leaves` at the rety-wrapped pi: output leaves trace into the bundle. -/
theorem pin_invPi_leaves :
    ∀ ℓ ∈ (pinEvPi.invPi rfl rfl).leaves, ∃ ℓ' ∈ pinEvPi.leaves, SubEq ℓ ℓ' :=
  EvTy.invPi_leaves pinEvPi rfl rfl

/-- the U→U edge shape of S2 §4: the inverted app typing's leaves are all
    strict sub-derivations of the removed literal atom. -/
theorem pin_inv_dm :
    DMStep ((pinAppLit.invApp rfl rfl).leaves.map Jd.wt ++
        ([] : List (Jd emptyEnv 0)).map Jd.wt)
      (([Jd.ty pinAppConvT] : List (Jd emptyEnv 0)).map Jd.wt ++
        ([] : List (Jd emptyEnv 0)).map Jd.wt) :=
  dm_of_strictLeaves (X := [Jd.ty pinAppConvT]) (Z := [])
    (L := (pinAppLit.invApp rfl rfl).leaves) (List.cons_ne_nil _ _)
    (fun ℓ hℓ => ⟨.ty pinAppConvT, .head _, pin_invApp_strict ℓ hℓ⟩)

#print axioms EvTy.litRooted
#print axioms EvInvApp
#print axioms EvInvLam
#print axioms EvInvPi
#print axioms EvInvLetE
#print axioms EvInvBvar
#print axioms EvInvConst
#print axioms EvInvLit
#print axioms EvInvApp.leaves
#print axioms EvInvLam.leaves
#print axioms EvInvPi.leaves
#print axioms EvInvLetE.leaves
#print axioms EvInvBvar.leaves
#print axioms EvInvConst.leaves
#print axioms EvInvLit.leaves
#print axioms EvTy.invApp
#print axioms EvTy.invLam
#print axioms EvTy.invPi
#print axioms EvTy.invLetE
#print axioms EvTy.invBvar
#print axioms EvTy.invConst
#print axioms EvTy.invLit
#print axioms EvTy.invSortT
#print axioms EvTy.invApp_leaves
#print axioms EvTy.invLam_leaves
#print axioms EvTy.invPi_leaves
#print axioms EvTy.invLetE_leaves
#print axioms EvTy.invBvar_leaves
#print axioms EvTy.invConst_leaves
#print axioms EvTy.invLit_leaves
#print axioms EvTy.invSortT_leaves
#print axioms EvTy.invApp_strict
#print axioms EvTy.invLam_strict
#print axioms EvTy.invPi_strict
#print axioms EvTy.invLetE_strict
#print axioms EvTy.invBvar_strict
#print axioms EvTy.invConst_strict
#print axioms EvTy.invLit_strict
#print axioms EvTy.invSortT_strict
#print axioms pin_invApp_strict
#print axioms pin_invPi_leaves
#print axioms pin_inv_dm

end Rcic.Declarative.F8Measure
