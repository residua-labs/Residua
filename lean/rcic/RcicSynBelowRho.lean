import rcic.RcicSynPack
import rcic.RcicSynEtaLam

/-!
# Syntactic sortRow, build step 3am — `Below` at a context-disrespecting `ρ` is refutable, given that `ρ`'s `DispFor`

`research/rcic/semantic/S3_ES_ARMS.md` §38. `Below` (§18) quantifies `ES`,
`CL`, `EUT` and `PBit` over every `σ` and every disposition list `ρ`,
in every environment and context ("one derivation is erased at every
pending level map and every erased context"). Two of those claims are
false at a `ρ` that does not respect the context, on derivations of
weight at most `5`. Each sits under every rule node heavier than it, so
`Below` at that node's measure conjoined with a `DispFor` of the
offending `ρ` is `False` — the `DispFor` is an explicit premise of the
refutation theorems below, not something `Below` supplies. The
`es_of_below_*` arms (§18–§37) as first stated (unquantified `ρ`) are
therefore not vacuously refutable here, but are unsound unless the
`ρ`-quantification is constrained to reachable dispositions (§40).

1. `PBit` at a `drop`. In `x : Prop`, the variable `x` is relevant
   (`Prop : sort 1`) and erases to `resolve [.drop] 0 = ★`; its sort bit
   is `false` (`not_pbit_drop`). Weight `2` against `1`.
2. `ES` at a wrong `inline`. In `x : sort 1 := sort 0`, `zetaLocal` is
   `x ≡ sort 0`. At `ρ = [.inline (sort 1)]` the left endpoint erases to
   `sort 1` and the right to `sort 0`, and `eqN_of_convE_sort_wf` at the
   empty table refutes `sort 1 ↔* sort 0` (`not_es_inline`). Weight `5`.

`below_false_of_pb` / `below_false_of_es` turn each into
`Below → DispFor id _ _ ctx [bad disp] → False` at any rule node heavier
than `2` / `5`; both `DispFor` premises are non-canonical (see below).
`refl_wt_gt_two` is that bound for every `refl` node.

What it does not say. Both counterexamples use a `ρ` the erasure of an
admitted context never produces: a `drop` at a relevant position, and an
`inline` whose value is not the let value's erasure. `DispFor`'s own
constructors never produce those `ρ`s at these contexts either —
`DispFor.assumption` on `pbitCtx` emits `binderDisp false = .keep`, not
`.drop`, and `DispFor.letInline` on `zetaCtx` inlines the value's own
erasure `.sort .zero`, not `.sort (.succ .zero)` — so each `DispFor`
premise of `below_false_of_pb` / `below_false_of_es` is uninhabited, and
what is refuted is the conjunction `Below ∧ DispFor`, not `Below` alone.
The unconditional `Below → False` at an inhabited `DispFor` is
`below_false_pinBetaP` (`RcicSynInlineRefute`, at `CtxP.disp id` via
`dispFor_ctxP_id`). Every recursive call the arms make extends or edits
`ρ` by the binder's own bit (`binderDisp`, `insertDisp` at the
substitution's sort, `removeAt`, the `lsub` value). The repair is a
premise on `Below`'s quantifiers (and on `ES`'s final use) that `ρ`
respects the context at `σ`, not a change to an arm. That is a ruling.
`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the empty table -/

theorem tableWF_nil : TableWF [] where
  congr :=
    { rhs := fun _ h => nomatch h
      nargs := fun _ h => nomatch h
      marity := fun _ h => nomatch h }
  closed := fun _ h => nomatch h
  rigid := fun _ h => nomatch h
  bare_unique := fun _ h => nomatch h
  ctor_disjoint := fun _ h => nomatch h
  bare_nullary := fun _ h => nomatch h

theorem not_eqN_one_zero : ¬ eqN (.succ .zero) .zero := by
  intro h
  exact absurd (h (fun _ => some 0)) (by decide)

/-! ## §2 `PBit` at a `drop` -/

/-- `x : Prop` at position 0. -/
def pbitCtx : LCtx := [.assumption (.sort .zero)]

/-- `Prop : sort 1`. -/
def pbitSort (E : ResolvedEnv) (n : Nat) :
    TyP E n pbitCtx (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort E n pbitCtx .zero (.succ .zero) (eqN_refl _)

theorem pbit_lookup : lookupType pbitCtx 0 = some (.sort .zero) := by
  unfold pbitCtx
  rw [lookup_assumption_zero]
  rfl

/-- `x : Prop`, a relevant variable: its type lives at `sort 1`. -/
def pbitVar (E : ResolvedEnv) (n : Nat) : TyP E n pbitCtx (.bvar 0) (.sort .zero) :=
  TyP.bvar E n pbitCtx 0 (.sort .zero) (.succ .zero) pbit_lookup (pbitSort E n)

theorem pbitVar_wt (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (pbitVar E n).wt Aw = 2 := rfl

theorem pbitSort_wt (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (pbitSort E n).wt Aw = 1 := rfl

theorem pbitVar_eps_drop (E : ResolvedEnv) (n : Nat) :
    (pbitVar E n).eps id [.drop] = .star := by
  unfold pbitVar
  rw [eps_bvar_rel (σ := id) (ρ := [.drop])
    (show levelIsZero (id (Level.succ .zero)) = false from rfl)]
  rfl

theorem not_pbit_drop (E : ResolvedEnv) (n : Nat) :
    ¬ PBit id [.drop] (pbitVar E n) (pbitSort E n) := by
  intro h
  have hz : levelIsZero (id (Level.succ .zero)) = true := h.mp (pbitVar_eps_drop E n)
  exact Bool.noConfusion hz

/-! ## §3 `ES` at a wrong `inline` -/

/-- `x : sort 1 := sort 0` at position 0. -/
def zetaCtx : LCtx := [.letBinding (.sort (.succ .zero)) (.sort .zero)]

theorem zeta_lookupType : lookupType zetaCtx 0 = some (.sort (.succ .zero)) := rfl

theorem zeta_lookupValue : lookupValue zetaCtx 0 = some (.sort .zero) := rfl

/-- `sort 0 : sort 1`, the value. -/
def zetaVal (E : ResolvedEnv) (n : Nat) :
    TyP E n zetaCtx (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort E n zetaCtx .zero (.succ .zero) (eqN_refl _)

/-- `x : sort 1`, relevant: `sort 1 : sort 2`. -/
def zetaVar (E : ResolvedEnv) (n : Nat) :
    TyP E n zetaCtx (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar E n zetaCtx 0 (.sort (.succ .zero)) (.succ (.succ .zero)) zeta_lookupType
    (TyP.sort E n zetaCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- `x ≡ sort 0`, by `zetaLocal`. -/
def zetaNode (E : ResolvedEnv) (n : Nat) :
    CvP E n zetaCtx (.bvar 0) (.sort .zero) (.sort (.succ .zero)) :=
  CvP.zetaLocal E n zetaCtx 0 (.sort (.succ .zero)) (.sort .zero)
    zeta_lookupValue zeta_lookupType (zetaVal E n) (zetaVar E n) (zetaVal E n)

theorem zetaNode_wt (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (zetaNode E n).wt Aw = 5 := rfl

theorem not_es_inline (tbl : List CRule) (hW : TableWF tbl) (E : ResolvedEnv) (n : Nat) :
    ¬ ES tbl id [.inline (.sort (.succ .zero))] (zetaNode E n) := by
  intro h
  have hl : (zetaVar E n).eps id [.inline (.sort (.succ .zero))] = .sort (.succ .zero) := by
    unfold zetaVar
    rw [eps_bvar_rel (σ := id) (ρ := [.inline (.sort (.succ .zero))])
      (show levelIsZero (id (Level.succ (.succ .zero))) = false from rfl)]
    rfl
  have hr : (zetaVal E n).eps id [.inline (.sort (.succ .zero))] = .sort .zero := rfl
  unfold ES at h
  have h' : ConvMod (EStep tbl) LvlEq (.sort (.succ .zero)) (.sort .zero) := by
    have hdl : (zetaNode E n).dl = zetaVar E n := rfl
    have hdr : (zetaNode E n).dr = zetaVal E n := rfl
    rw [hdl, hdr, hl, hr] at h
    exact h
  exact not_eqN_one_zero (eqN_of_convE_sort_wf hW h')

/-! ## §4 `Below` at a heavy rule node -/

theorem below_false_of_pb (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (hnode : CvP E n Γ a b T) (ht : hnode.isTransport = false)
    (hw : 2 < hnode.wt Aw) (B : Below Aw tbl (cvMeas Aw hnode))
    (E' : ResolvedEnv) (n' : Nat)
    (hdrop : DispFor id E' n' pbitCtx [.drop]) : False := by
  have h₁ : (pbitVar E' n').wt Aw < hnode.wt Aw := by
    rw [pbitVar_wt]
    exact hw
  have h₂ : (pbitSort E' n').wt Aw < hnode.wt Aw := by
    rw [pbitSort_wt]
    exact Nat.lt_trans (Nat.lt_succ_self 1) hw
  exact not_pbit_drop E' n'
    (B.pb (pbitVar E' n') (pbitSort E' n') id [.drop] hdrop
      (lex_of_dm (dmStep_pair_below Aw hnode ht (pbitVar E' n') (pbitSort E' n') h₁ h₂)))

theorem below_false_of_es (Aw : Nat → Nat) (tbl : List CRule) (hW : TableWF tbl)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (hnode : CvP E n Γ a b T) (ht : hnode.isTransport = false)
    (hw : 5 < hnode.wt Aw) (B : Below Aw tbl (cvMeas Aw hnode))
    (E' : ResolvedEnv) (n' : Nat)
    (hinline : DispFor id E' n' zetaCtx [.inline (.sort (.succ .zero))]) : False := by
  have hY : ∀ y ∈ (zetaNode E' n').atoms Aw, y < hnode.wt Aw := by
    intro y hy
    rw [CvP.atoms_rule Aw (zetaNode E' n') rfl, zetaNode_wt] at hy
    rw [List.mem_singleton.mp hy]
    exact hw
  exact not_es_inline tbl hW E' n'
    (B.es (zetaNode E' n') id [.inline (.sort (.succ .zero))] hinline
      (lex_of_dm (dmStep_under_rule Aw hnode ht hY)))

/-- Every `refl` node: three typings, each of weight at least `1`. -/
theorem refl_wt_gt_two (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat}
    (ht : TyP E n Γ a A) (dl dr : TyP E n Γ a A) :
    2 < (CvP.refl E n Γ a A ht dl dr).wt Aw := by
  have h1 := TyP.wt_pos Aw ht
  have h2 := TyP.wt_pos Aw dl
  have h3 := TyP.wt_pos Aw dr
  simp only [CvP.wt]
  omega

theorem below_false_refl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat}
    (ht : TyP E n Γ a A) (dl dr : TyP E n Γ a A)
    (B : Below Aw tbl (cvMeas Aw (CvP.refl E n Γ a A ht dl dr)))
    (hdrop : DispFor id E n pbitCtx [.drop]) : False :=
  below_false_of_pb Aw tbl (CvP.refl E n Γ a A ht dl dr) rfl (refl_wt_gt_two Aw ht dl dr) B E n hdrop

end Rcic.Syn

#print axioms Rcic.Syn.tableWF_nil
#print axioms Rcic.Syn.not_eqN_one_zero
#print axioms Rcic.Syn.pbitCtx
#print axioms Rcic.Syn.pbitSort
#print axioms Rcic.Syn.pbit_lookup
#print axioms Rcic.Syn.pbitVar
#print axioms Rcic.Syn.pbitVar_wt
#print axioms Rcic.Syn.pbitSort_wt
#print axioms Rcic.Syn.pbitVar_eps_drop
#print axioms Rcic.Syn.not_pbit_drop
#print axioms Rcic.Syn.zetaCtx
#print axioms Rcic.Syn.zeta_lookupType
#print axioms Rcic.Syn.zeta_lookupValue
#print axioms Rcic.Syn.zetaVal
#print axioms Rcic.Syn.zetaVar
#print axioms Rcic.Syn.zetaNode
#print axioms Rcic.Syn.zetaNode_wt
#print axioms Rcic.Syn.not_es_inline
#print axioms Rcic.Syn.below_false_of_pb
#print axioms Rcic.Syn.below_false_of_es
#print axioms Rcic.Syn.refl_wt_gt_two
#print axioms Rcic.Syn.below_false_refl
