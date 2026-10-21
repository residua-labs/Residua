import rcic.RcicSynDomPathPins
import rcic.RcicSynRedexKind

/-!
# T13 pins — redex kind views over original fields (ChatGPT S8, #7338)

Spec: `research/rcic/sortrow/S8_REDEX_KIND_VIEWS.md`. `closure_claim = 0`.

Fixtures reuse the S7 §4 nodes (`dpB` is the original beta `R ≡ P`, `dpC` the
`trans (symm b) b` control). New: `rkB`, a β node whose original body is the
literal `bvar 0` (`(λ (sort s_U). #0) P ≡ P`) — the §2 **β-hit** route —
and `rkZ`, a ζ node whose stored body is already Π — the §4 **ζ-under** route.

Controls pinned:
- `redexDom dpB` — β-under: view comes out of the original `hbody` + the lazy
  `k3DomInst` instantiation; never a fresh β/Π node.
- `redexDom rkB` — β-hit: `piInvP` of the original `harg`, never `hbody` forced
  to be a Π.
- `redexDom rkZ` — ζ-under: the real `lsub` at `j = 0`, `.letBinding` never
  swapped for `.assumption`.
- `redexDom dpC` — `trans` is not a redex: the read stays an `.arm`
  obligation, the demand kept.
- `iotaPlan`/`arm` exist as records — the ι RHS plan keeps the original `h`
  field rather than evaluating the recursive rhs.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `(λ (sort s_U). #0) P` — β redex whose original body is the literal
    `bvar 0`: the substituted variable exposes `P`'s Π directly. -/
abbrev rkApp : Expr Nat := .app (.lam (.sort dpU) (.bvar 0)) dpP

/-- `sort s_U : sort (succ s_U)` at any `Γ`. -/
def rkTyU {Γ : LCtx} : TyP emptyEnv 0 Γ (.sort dpU) (.sort (.succ dpU)) :=
  .sort _ _ _ dpU (.succ dpU) (eqN_refl _)

/-- `#0 : sort s_U` under the `assumption (sort s_U)` binder. -/
def rkTyVar : TyP emptyEnv 0 [.assumption (.sort dpU)] (.bvar 0) (.sort dpU) :=
  .bvar _ _ _ _ _ _ rfl rkTyU

/-- `λ (sort s_U). #0 : Π (sort s_U). sort s_U`. -/
def rkTyLamId : TyP emptyEnv 0 [] (.lam (.sort dpU) (.bvar 0))
    (.pi (.sort dpU) (.sort dpU)) :=
  .lam _ _ _ _ _ _ _ _ rkTyU rkTyVar rkTyU

/-- `rkApp : sort s_U` — the original `dl` field of `rkB`. -/
def rkTyApp : TyP emptyEnv 0 [] rkApp (.sort dpU) :=
  .app _ _ _ _ _ _ _ _ rkTyLamId dpTyPIn rkTyU

/-- `rkB : rkApp ≡ P : sort s_U` — the original β node of the β-hit fixture. -/
def rkB : CvP emptyEnv 0 [] rkApp dpP (.sort dpU) :=
  .beta _ _ _ (.sort dpU) (.bvar 0) dpP (.sort dpU) _
    rkTyU rkTyVar dpTyPIn rkTyApp dpTyPIn

/-- β-under: `dpB`'s original body `P` is literally Π — the view is the
    original `hbody` read + `k3DomInst` at `harg`/`hA`. -/
theorem redexDom_dpB :
    redexDom dpB .root = .view (.betaUnder rfl) .root := rfl

/-- β-hit: `rkB`'s original body is `bvar 0` and `arg = P` is literally Π —
    the view is `piInvP` of the original `harg`. -/
theorem redexDom_rkB :
    redexDom rkB .root = .view (.betaHit rfl rfl) .root := rfl

/-- `letE (sort s_U) P P` — ζ redex whose stored body is already Π. -/
abbrev rkLet : Expr Nat := .letE (.sort dpU) dpP dpP

/-- `rkLet : sort s_U` — the original `dl` field of `rkZ`. -/
def rkTyLet : TyP emptyEnv 0 [] rkLet (.sort dpU) :=
  .letE _ _ _ _ _ _ _ _ _ rkTyU dpTyPIn dpTyPIn rkTyU

/-- `rkZ : rkLet ≡ P : sort s_U` — the original ζ node of the ζ-under
    fixture. -/
def rkZ : CvP emptyEnv 0 [] rkLet dpP (.sort dpU) :=
  .zeta _ _ _ (.sort dpU) dpP dpP (.sort dpU) _
    rkTyU dpTyPIn dpTyPIn rkTyLet dpTyPIn

/-- ζ-under: `rkZ`'s original body `P` is literally Π — the view is `piInvP`
    of the original `hb` in the `letBinding` context, transported by the real
    `lsub` at `j = 0`. -/
theorem redexDom_rkZ :
    redexDom rkZ .root = .view (.zetaUnder rfl) .root := rfl

/-- `trans` is not a redex: `dpC` keeps its own route — the `.arm` obligation
    records the demand, never a forced view. -/
theorem redexDom_dpC :
    redexDom dpC .root = .obligation (.arm dpC) .root := rfl

end Rcic.Syn

#print axioms Rcic.Syn.redexDom_dpB
#print axioms Rcic.Syn.redexDom_rkB
#print axioms Rcic.Syn.redexDom_rkZ
#print axioms Rcic.Syn.redexDom_dpC
#print axioms Rcic.Syn.rkB
#print axioms Rcic.Syn.rkZ
