import rcic.RcicSynInlineRefute
import rcic.RcicSynAllBelow
import rcic.RcicSynStarLift
import rcic.RcicSynZetaMeasureRefute
import rcic.RcicSynTable
import rcic.RcicSynLetInline
import rcic.RcicSynSpineComb
import rcic.RcicSynCR

/-!
# S15 boundary controls — `W3-FIT-NOT-SEMANTIC`, the old `AllBelow` refusal, and
the SCOPE-1 out-of-range `wk` positive pin

`research/rcic/sortrow/S15_BELOWC_DISPLAY_FIXPOINT.md` §2–§3 and
`research/rcic/sortrow/S15_OUT_OF_RANGE_WK_PIN.md`.

1. **§1 `DisplayFits`**: S14's weak structural fit, defined here (main has only
   the exact-length `DispShape`). `nil` accepts ANY display tail beyond the
   context, because `TyP.wk` allows a cutoff past `Γ.length` and AP does not
   include `c ≤ Γ.length`.

2. **§2 `W3-FIT-NOT-SEMANTIC` part 1** (`S15` §2.1): at `Γ = [A : sort 0]`,
   `D : bvar 0 : sort 0`, `DT : sort 0 : sort 1`, the wrong display
   `ρbad = [.drop]` fits structurally while `D.eps` erases to `★`, making
   `PBit` false (`levelIsZero (succ 0) = false`). The canonical display is
   `[.keep]`, where the bit is honest.

3. **§3 `W3-FIT-NOT-SEMANTIC` part 2** (`S15` §2.2): at
   `Γ = [x : A, A : sort 1 := sort 0]` with the real `zetaLocal` conversion
   `c : bvar 1 ≡ sort 0 : sort 1`, the wrong display `ρbad = [.keep, .drop]`
   gives `D₁.reg.2.eps = ★` vs `D₂.reg.2.eps = sort 0`, so `EUT` fails under
   every `TableWF` table — supplying only EUT does not rescue the wrong
   display either.

4. **§4 `no_legacy_allBelow`** (`S15` §3): verbatim from the spec — the old
   scope-free `AllBelow` is already refuted by `below_false_pinBetaP`; the new
   scoped design must never supply it again.

5. **§5 the SCOPE-1 out-of-range `wk` pin** (`S15_OUT_OF_RANGE_WK_PIN`): the
   legal `wk` at cutoff `2` over `Γ = []` is AP-true while `AssumpCut [] 2`
   is false, and under the canonical display `ρ = [.keep]` all three typings
   erase to `sort 0` — the same output under both the current and the R2
   repaired erasure, since the term is only a sort. `DisplayFits` holds while
   the exact-length `DispShape` fails; equal atom table `[1]` with weight
   `2 → 1` gives the wrapper-strip `LexDM` edge.

These are boundary controls: they pin where `DisplayFits` is only structural
and where `AssumpCut` must not be substituted for public AP. `closure_claim`
stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `DisplayFits` (S14's weak structural fit) -/

/-- S14's structural fit (`S14_SHIFTED_VALUE_SCOPE` §1): keeps/drops/inlines
    aligned entry-by-entry, with the display allowed a tail beyond `Γ` —
    `nil ρ` accepts any `ρ` on `[]`, matching `TyP.wk`'s out-of-range cutoff.
    Never the semantic premises (`EUT`/`PBit`/entry-bit alignment). -/
inductive DisplayFits : LCtx → List Disp → Prop where
  | nil (ρ : List Disp) : DisplayFits [] ρ
  | assumptionKeep {A : Expr Nat} {Γ : LCtx} {ρ : List Disp} :
      DisplayFits Γ ρ → DisplayFits (.assumption A :: Γ) (.keep :: ρ)
  | assumptionDrop {A : Expr Nat} {Γ : LCtx} {ρ : List Disp} :
      DisplayFits Γ ρ → DisplayFits (.assumption A :: Γ) (.drop :: ρ)
  | letDrop {A v : Expr Nat} {Γ : LCtx} {ρ : List Disp} :
      DisplayFits Γ ρ → DisplayFits (.letBinding A v :: Γ) (.drop :: ρ)
  | letInline {A v : Expr Nat} {w : ETm} {Γ : LCtx} {ρ : List Disp} :
      DisplayFits Γ ρ → DisplayFits (.letBinding A v :: Γ) (.inline w :: ρ)

/-- `DispShape` is the exact-length strengthening. -/
theorem DisplayFits.of_dispShape {Γ : LCtx} {ρ : List Disp} (h : DispShape Γ ρ) :
    DisplayFits Γ ρ := by
  induction h with
  | nil => exact .nil []
  | assumptionKeep _ ih => exact .assumptionKeep ih
  | assumptionDrop _ ih => exact .assumptionDrop ih
  | letDrop _ ih => exact .letDrop ih
  | letInline _ ih => exact .letInline ih

/-- The display covers the context; the tail beyond `Γ.length` is the
    out-of-range part (`S14` §1's preservation input). -/
theorem DisplayFits.length_le {Γ : LCtx} {ρ : List Disp} (h : DisplayFits Γ ρ) :
    Γ.length ≤ ρ.length := by
  induction h with
  | nil ρ => exact Nat.zero_le _
  | assumptionKeep _ ih => exact Nat.succ_le_succ ih
  | assumptionDrop _ ih => exact Nat.succ_le_succ ih
  | letDrop _ ih => exact Nat.succ_le_succ ih
  | letInline _ ih => exact Nat.succ_le_succ ih

/-! ## §2 `W3-FIT-NOT-SEMANTIC` part 1 (`S15` §2.1) -/

/-- `Γ = [A : sort 0]`. -/
def fitCtx : LCtx := [.assumption (.sort .zero)]

/-- The context is natively well formed: `sort 0 : sort 1`. -/
def fitCtx_wf (E : ResolvedEnv) (n : Nat) : CtxWfT E n fitCtx :=
  .assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)

/-- `D : bvar 0 : sort 0` — the assumption, directly. -/
def fitD (E : ResolvedEnv) (n : Nat) : TyP E n fitCtx (.bvar 0) (.sort .zero) :=
  .bvar E n fitCtx 0 (.sort .zero) (.succ .zero) rfl
    (.sort E n fitCtx .zero (.succ .zero) (eqN_refl _))

/-- `DT : sort 0 : sort 1`. -/
def fitDT (E : ResolvedEnv) (n : Nat) :
    TyP E n fitCtx (.sort .zero) (.sort (.succ .zero)) :=
  .sort E n fitCtx .zero (.succ .zero) (eqN_refl _)

/-- The structurally fitting, semantically wrong display `ρbad = [.drop]`. -/
def fitBad : List Disp := [.drop]

/-- `ρbad` fits structurally — assumption/drop under both `DispShape` and
    `DisplayFits`. -/
def fitBad_shape : DispShape fitCtx fitBad := .assumptionDrop .nil

def fitBad_fits : DisplayFits fitCtx fitBad := .assumptionDrop (.nil [])

/-- Under `ρbad`, `D` erases `bvar 0` to `★`. -/
theorem fitD_eps_bad (E : ResolvedEnv) (n : Nat) :
    (fitD E n).eps id fitBad = .star := rfl

/-- Under the canonical display `[.keep]`, the slot is kept: `bvar 0`. -/
theorem fitD_eps_keep (E : ResolvedEnv) (n : Nat) :
    (fitD E n).eps id [.keep] = .bvar 0 := rfl

/-- `W3-FIT-NOT-SEMANTIC` part 1: structural fit does not imply `PBit` —
    `D.eps = ★` while the declaration bit `levelIsZero (succ 0)` is `false`. -/
theorem fit_not_pbit (E : ResolvedEnv) (n : Nat) :
    ¬ PBit id fitBad (fitD E n) (fitDT E n) := fun h =>
  Bool.noConfusion (h.1 rfl)

/-- At the canonical `[.keep]` the iff holds vacuously both ways. -/
theorem fit_pbit_canonical (E : ResolvedEnv) (n : Nat) :
    PBit id [.keep] (fitD E n) (fitDT E n) :=
  ⟨fun h => ETm.noConfusion h, fun h => Bool.noConfusion h⟩

/-- The wrong display's typing is still AP (every transport node is prefix-safe;
    there are none). -/
theorem fitD_ap (E : ResolvedEnv) (n : Nat) : (fitD E n).AssumpPref := trivial

/-! ## §3 `W3-FIT-NOT-SEMANTIC` part 2 (`S15` §2.2) -/

/-- `Γ = [x : A, A : sort 1 := sort 0]` — newest-first: `x`'s stored type is
    `bvar 0` (the let entry one step below), and lookup lifts by `i + 1`, so
    `x`'s ascribed type is `bvar 1` and `bvar 1`'s is `sort 1`. -/
def zetaBadCtx : LCtx :=
  [.assumption (.bvar 0), .letBinding (.sort (.succ .zero)) (.sort .zero)]

/-- `Γ` is natively well formed: `A : sort 1 := sort 0` with `sort 0 : sort 1`,
    `sort 1 : sort 2`, and `x`'s type `bvar 0` typing `bvar 1` in the tail. -/
def zetaBadCtx_wf (E : ResolvedEnv) (n : Nat) : CtxWfT E n zetaBadCtx :=
  .assumption [.letBinding (.sort (.succ .zero)) (.sort .zero)] (.bvar 0)
    (.succ .zero)
    (.letBinding [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.sort .zero)
      .nil
      (.sort [] (.succ .zero))
      (.sort [] .zero))
    (.bvar [.letBinding (.sort (.succ .zero)) (.sort .zero)] 0
      (.sort (.succ .zero)) rfl)

/-- `hA : bvar 1 : sort 1` — `A`'s stored type. -/
def zetaH (E : ResolvedEnv) (n : Nat) :
    TyP E n zetaBadCtx (.bvar 1) (.sort (.succ .zero)) :=
  .bvar E n zetaBadCtx 1 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
    (.sort E n zetaBadCtx (.succ .zero) (.succ (.succ .zero)) (eqN_refl _))

/-- `D₁ : bvar 0 : bvar 1` — `x` at `A`. -/
def zetaD1 (E : ResolvedEnv) (n : Nat) : TyP E n zetaBadCtx (.bvar 0) (.bvar 1) :=
  .bvar E n zetaBadCtx 0 (.bvar 1) (.succ .zero) rfl (zetaH E n)

/-- The real `zetaLocal`: `bvar 1` (`A`) converts to its stored value `sort 0`,
    at its stored type `sort 1`. -/
def zetaCv (E : ResolvedEnv) (n : Nat) :
    CvP E n zetaBadCtx (.bvar 1) (.sort .zero) (.sort (.succ .zero)) :=
  .zetaLocal E n zetaBadCtx 1 (.sort (.succ .zero)) (.sort .zero) rfl rfl
    (.sort E n zetaBadCtx .zero (.succ .zero) (eqN_refl _))
    (zetaH E n)
    (.sort E n zetaBadCtx .zero (.succ .zero) (eqN_refl _))

/-- `D₂ := TyP.conv D₁ c : bvar 0 : sort 0`. -/
def zetaD2 (E : ResolvedEnv) (n : Nat) : TyP E n zetaBadCtx (.bvar 0) (.sort .zero) :=
  .conv E n zetaBadCtx (.bvar 0) (.bvar 1) (.sort .zero) (.succ .zero)
    (zetaD1 E n) (zetaCv E n)

/-- The structurally legal, semantically wrong display `ρbad = [.keep, .drop]`:
    `x` kept, `A` dropped. -/
def zetaBad : List Disp := [.keep, .drop]

/-- `ρbad` fits structurally. -/
def zetaBad_shape : DispShape zetaBadCtx zetaBad := .assumptionKeep (.letDrop .nil)

def zetaBad_fits : DisplayFits zetaBadCtx zetaBad := .assumptionKeep (.letDrop (.nil []))

/-- `D₁.reg.2` is `hA`'s `bvar 1` node; under `ρbad` the `A` slot is dropped:
    `resolve [.keep, .drop] 1 = (resolve [.drop] 0).lift 0 1 = ★`. -/
theorem zeta_eps_left (E : ResolvedEnv) (n : Nat) :
    (zetaD1 E n).reg.2.eps id zetaBad = .star := rfl

/-- `D₂.reg.2` is the `sort 0 : sort 1` typing — `sort` erases to itself. -/
theorem zeta_eps_right (E : ResolvedEnv) (n : Nat) :
    (zetaD2 E n).reg.2.eps id zetaBad = .sort .zero := rfl

/-- `W3-FIT-NOT-SEMANTIC` part 2: EUT cannot be rescued by display choice —
    for every `TableWF` table the wrong display gives `★` vs `sort 0`, and
    `not_convMod_star_sort` (already on main) refuses the join. -/
theorem zeta_not_eut (tbl : List CRule) (hW : TableWF tbl) (E : ResolvedEnv) (n : Nat) :
    ¬ EUT tbl id zetaBad (zetaD1 E n) (zetaD2 E n) := fun h =>
  not_convMod_star_sort hW .zero h

/-- Every derivation in the control is AP. -/
theorem zetaH_ap (E : ResolvedEnv) (n : Nat) : (zetaH E n).AssumpPref := trivial

theorem zetaD1_ap (E : ResolvedEnv) (n : Nat) : (zetaD1 E n).AssumpPref := trivial

theorem zetaCv_ap (E : ResolvedEnv) (n : Nat) : (zetaCv E n).AssumpPref :=
  ⟨trivial, trivial, trivial⟩

theorem zetaD2_ap (E : ResolvedEnv) (n : Nat) : (zetaD2 E n).AssumpPref :=
  ⟨trivial, trivial, trivial, trivial⟩

/-! ## §4 the old `AllBelow` stays refuted (`S15` §3) -/

/-- The old scope-free `AllBelow` is refuted on main (`below_false_pinBetaP`);
    the scoped fixpoint design must never supply it — verbatim `S15` §3. -/
theorem no_legacy_allBelow (Aw : Nat → Nat) (tbl : List CRule) (hW : TableWF tbl) :
    ¬ AllBelow Aw tbl := by
  intro h
  exact below_false_pinBetaP Aw tbl hW (h (cvMeas Aw pinBetaP))

/-! ## §5 the SCOPE-1 out-of-range `wk` pin (`S15_OUT_OF_RANGE_WK_PIN`) -/

/-- `wkS0`. -/
abbrev wkS0 : Expr Nat := .sort .zero

/-- `wkS1`. -/
abbrev wkS1 : Expr Nat := .sort (.succ .zero)

/-- `sort 0 : sort 1` in the empty context. -/
def wkSource : TyP emptyEnv 0 [] wkS0 wkS1 :=
  .sort _ _ _ _ _ (eqN_refl _)

/-- `sort 0 : sort 1` weakened at `c = 2` — PAST the empty source context.
    Legal: `insertAt (.assumption wkS0) 2 [] = [.assumption wkS0]` and `lift`
    fixes closed terms. -/
def wkOut : TyP emptyEnv 0 [.assumption wkS0] wkS0 wkS1 :=
  .wk emptyEnv 0 [] wkS0 wkS1 (.assumption wkS0) 2 wkSource

/-- The direct typing in the weakened context. -/
def wkDirect : TyP emptyEnv 0 [.assumption wkS0] wkS0 wkS1 :=
  .sort _ _ _ _ _ (eqN_refl _)

/-- The three pure index equations. -/
theorem wkPin_insertAt : insertAt (.assumption wkS0) 2 [] = [.assumption wkS0] := rfl

theorem wkPin_lift_s0 : lift 2 1 wkS0 = wkS0 := rfl

theorem wkPin_lift_s1 : lift 2 1 wkS1 = wkS1 := rfl

/-- Native `CtxWfT` of the target context. -/
def wkTarget_wf (E : ResolvedEnv) (n : Nat) : CtxWfT E n [.assumption wkS0] :=
  .assumption [] wkS0 (.succ .zero) .nil (.sort [] .zero)

/-- Public AP at the out-of-range cutoff holds: the source prefix `take 2 []`
    is empty. -/
theorem wkPin_ap_prefix : AssumptionPrefix [] 2 := fun d hd =>
  (List.not_mem_nil d hd).elim

/-- `wkSource` is AP. -/
theorem wkSource_ap : wkSource.AssumpPref := trivial

/-- `wkOut` is AP: the wk node's cutoff `2` only needs `AssumptionPrefix []`,
    never `AssumpCut`. -/
theorem wkOut_ap : wkOut.AssumpPref := ⟨wkPin_ap_prefix, trivial⟩

/-- `AssumpCut [] 2` is FALSE — it is not a synonym of public AP; SCOPE-1
    never uses it in place of AP. -/
theorem wkPin_not_assumpCut : ¬ AssumpCut [] 2 := fun h =>
  absurd h.le_length (Nat.not_succ_le_zero 1)

/-- Exact display values at `ρ = [.keep]`: `ρ[2]? = none`, so `eps_wk`'s
    none-branch applies with no outer lift. All three erase to `sort 0` —
    the same under both the current and the repaired R2 erasure, since the
    term is only a sort. -/
theorem wkPin_eps_source : wkSource.eps id (removeAt [.keep] 2) = .sort .zero := rfl

theorem wkPin_eps_out : wkOut.eps id [.keep] = .sort .zero := rfl

theorem wkPin_eps_direct : wkDirect.eps id [.keep] = .sort .zero := rfl

/-- The atom table is untouched by the out-of-range `wk`; only the weight
    grows — the real wrapper-strip edge `([1], 1) < ([1], 2)`. -/
theorem wkPin_atoms (Aw : Nat → Nat) :
    wkSource.atoms Aw = wkOut.atoms Aw ∧ wkSource.atoms Aw = [1] :=
  ⟨rfl, rfl⟩

theorem wkPin_weight (Aw : Nat → Nat) :
    wkOut.wt Aw = 2 ∧ wkSource.wt Aw = 1 := ⟨rfl, rfl⟩

/-- The wrapper-strip edge: same atoms, smaller weight. -/
theorem wkPin_edge (Aw : Nat → Nat) :
    LexDM (tyMeas Aw wkSource) (tyMeas Aw wkOut) := by
  show Prod.Lex DMStep (fun a b : Nat => a < b)
    (wkSource.atoms Aw, wkSource.wt Aw) (wkOut.atoms Aw, wkOut.wt Aw)
  exact Prod.Lex.right _ Nat.le.refl

/-- `DisplayFits` allows the display tail `ρ = [.keep]` on the empty source
    context — the exact call this real `wk` makes. -/
theorem wkPin_fits : DisplayFits [] [.keep] := .nil _

/-- The exact-length `DispShape` fails — the structural predicate that would
    reject this legal display is the wrong one for SCOPE-1. -/
theorem wkPin_not_dispShape : ¬ DispShape [] [.keep] := fun h =>
  Nat.noConfusion (DispShape.length_eq h)

end Rcic.Syn

#print axioms Rcic.Syn.DisplayFits
#print axioms Rcic.Syn.DisplayFits.of_dispShape
#print axioms Rcic.Syn.DisplayFits.length_le
#print axioms Rcic.Syn.fitCtx
#print axioms Rcic.Syn.fitCtx_wf
#print axioms Rcic.Syn.fitD
#print axioms Rcic.Syn.fitDT
#print axioms Rcic.Syn.fitBad
#print axioms Rcic.Syn.fitBad_shape
#print axioms Rcic.Syn.fitBad_fits
#print axioms Rcic.Syn.fitD_eps_bad
#print axioms Rcic.Syn.fitD_eps_keep
#print axioms Rcic.Syn.fit_not_pbit
#print axioms Rcic.Syn.fit_pbit_canonical
#print axioms Rcic.Syn.fitD_ap
#print axioms Rcic.Syn.zetaBadCtx
#print axioms Rcic.Syn.zetaBadCtx_wf
#print axioms Rcic.Syn.zetaH
#print axioms Rcic.Syn.zetaD1
#print axioms Rcic.Syn.zetaCv
#print axioms Rcic.Syn.zetaD2
#print axioms Rcic.Syn.zetaBad
#print axioms Rcic.Syn.zetaBad_shape
#print axioms Rcic.Syn.zetaBad_fits
#print axioms Rcic.Syn.zeta_eps_left
#print axioms Rcic.Syn.zeta_eps_right
#print axioms Rcic.Syn.zeta_not_eut
#print axioms Rcic.Syn.zetaH_ap
#print axioms Rcic.Syn.zetaD1_ap
#print axioms Rcic.Syn.zetaCv_ap
#print axioms Rcic.Syn.zetaD2_ap
#print axioms Rcic.Syn.no_legacy_allBelow
#print axioms Rcic.Syn.wkS0
#print axioms Rcic.Syn.wkS1
#print axioms Rcic.Syn.wkSource
#print axioms Rcic.Syn.wkOut
#print axioms Rcic.Syn.wkDirect
#print axioms Rcic.Syn.wkPin_insertAt
#print axioms Rcic.Syn.wkPin_lift_s0
#print axioms Rcic.Syn.wkPin_lift_s1
#print axioms Rcic.Syn.wkTarget_wf
#print axioms Rcic.Syn.wkPin_ap_prefix
#print axioms Rcic.Syn.wkSource_ap
#print axioms Rcic.Syn.wkOut_ap
#print axioms Rcic.Syn.wkPin_not_assumpCut
#print axioms Rcic.Syn.wkPin_eps_source
#print axioms Rcic.Syn.wkPin_eps_out
#print axioms Rcic.Syn.wkPin_eps_direct
#print axioms Rcic.Syn.wkPin_atoms
#print axioms Rcic.Syn.wkPin_weight
#print axioms Rcic.Syn.wkPin_edge
#print axioms Rcic.Syn.wkPin_fits
#print axioms Rcic.Syn.wkPin_not_dispShape
