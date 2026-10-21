import rcic.RcicSynStepFieldsDeltaIota
import rcic.RcicSynIotaRoutePlan
import rcic.RcicSynNatSuccIota
import rcic.RcicSynListConsIota
import rcic.RcicSynP2Iota

/-!
# `es_iota_retained` — the general decoder case (StepSuppliers field 6)

The field (`RcicSynStepSkeleton.lean:424`): the retained-result `ι` leg
(`levelIsZero (σ hlhs.reg.1) = false`) owes the original T6 spine, the slot
kind and its source, the rule match, the RHS β* and the endpoint `CL`s —
`CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ)`.

The landed closures (`RcicSynStepFieldsDeltaIota`) already discharge the four
outer queries `qCLL`/`qCLR`/`qPL`/`qPR` from `StepIH` — `qCLL`/`qCLR`
unconditionally (`Issues.occ_cl`), `qPL`/`qPR` whenever `hlhs.reg.2` sits at a
`P2Query.subAt` payload path (`Issues.occ_pb`).  What remains is the
`IotaRetainedSimulation`: the admission→`CRule`/template bridge of
`BELOWC_DEMAND_GRAMMAR_CONTINUATION.md` §7.4.

## Port classification (per `IotaRetainedPorts` field)

| port | class | disposition |
|---|---|---|
| `qPL`, `qPR` | (a) issuable | `StepIH` answers them under `regOcc`
  (`iota_issued_pb_hlhs/hrhs_of_reg_occ`), or unconditionally when
  `dl = hlhs ∧ dr = hrhs` (`iota_issued_pbL/R`); `regOcc` itself is
  class (c) on an `.app`-headed `hlhs` (`iota_regOcc_app`, path `[0,2]`). |
| `el`, `erhs`, `er`, `matchL`, `croot`, `beta`, `matchR` | (d) | the
  general decoder residual `IotaRetainedSimulation`: `hlhs.eps σ ρ` is only
  `ConvMod (EStep tbl) LvlEq`-convertible (`matchL`) to the syntactic `CRoot`
  redex `el` — `RStep tbl` has neither `LvlEq` universe congruence, `EtaStep`,
  nor backward `EStep`s, and under wrappers/conversions `hlhs`/`hrhs` are
  independent derivations whose endpoint erasures need not be syntactically
  the redex/`er`.  Reflexive collapse of `matchL`/`matchR` is the
  specialization `IotaRetainedRulePorts` (used by the Nat/List pins through
  the `*_of_rulePorts` wrappers).  The `croot`/`beta` core is not issuable
  and not descending: it needs the general
  `DerivedIota → CRule ∈ tbl` generator (W-IOTA-GENERATED-CHAIN-BOUND);
  `CRule` has function fields (`nargs`, `rhs`), so no decidable selection,
  and `tbl` is arbitrary in the field. |

## §7.4 enumeration (the decoder's front half)

`IotaExpectedSlotPos` is already landed; this module adds its *total read*:
`IotaSite.readExpectedSlot` resolves every expected position —
`recArg j`, `major`, `ctorParam j`, `ctorField j`, `rhsRecResult j` —
against the original spines, returning `originalApp` / `wrappedNeed` /
`missingExpectedSlot`.  Positions are enumerated BEFORE reading
(`IotaExpectedSlotPos.all`), so a failed read can never remove the slot —
the `planIota` drops (constructor parameters; filterMapped RHS rec-results)
are named, not silent.  `IotaSite.readExpectedSlot_occ_below` extends the
site bound to every returned occurrence, including the constructor-parameter
family `planIota` omits.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {Eₐ : ResolvedEnv} (Aw : Nat → Nat) (tbl : List CRule)

/-! ## §1 The rule/template bridge as the residual port -/

/-- The **reflexive specialization** of the `es_iota_retained` residual:
    `el`/`er` fixed at the endpoint erasures (so `matchL`/`matchR` collapse
    to `ConvMod.refl`).  Valid only when `hlhs.eps σ ρ` is already
    syntactically a `CRoot` redex of `tbl` and the template β*-reduces to
    `hrhs.eps σ ρ` directly — no `LvlEq`, `EtaStep`, or `CL` alignment legs.
    The general form is `IotaRetainedSimulation`; the primary field theorems
    take it, and `*_of_rulePorts` wrappers recover this specialization. -/
structure IotaRetainedRulePorts (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) : Type where
  /-- The rule's RHS template instantiated at the matched arguments. -/
  erhs : ETm
  /-- `hlhs.eps σ ρ` is a `CRoot` redex of `tbl`, reducing to `erhs`. -/
  croot : CRoot tbl (hlhs.eps σ ρ) erhs
  /-- `erhs →* hrhs.eps σ ρ` under `RStep tbl` (the finite β* run). -/
  beta : RStar (RStep tbl) erhs (hrhs.eps σ ρ)

/-- `IotaRetainedRulePorts` packages to a full `IotaRetainedSimulation`
    (`el := hlhs.eps σ ρ`, `erhs := p.erhs`, `er := hrhs.eps σ ρ`, both
    endpoint legs reflexive). -/
def IotaRetainedRulePorts.toSimulation {tbl : List CRule}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    {hlhs : TyP E n Γ lhs T} {hrhs : TyP E n Γ rhs T}
    {σ : Level → Level} {ρ : List Disp}
    (p : IotaRetainedRulePorts tbl hlhs hrhs σ ρ) :
    IotaRetainedSimulation tbl hlhs hrhs σ ρ :=
  ⟨_, _, _, .refl _, p.croot, p.beta, .refl _⟩

/-- `StepSuppliers.es_iota_retained`, exact binder telescope, on arbitrary
    `dl`/`dr`: the residual hypotheses are the `hlhs.reg.2` occurrence
    receipt (`pReg`/`regOcc`) and the general decoder simulation `sim`
    (`matchL`/`matchR` are real `ConvMod (EStep tbl) LvlEq` legs — the
    erased endpoint needs only be convertible, not syntactically the
    `CRoot` redex). -/
theorem es_iota_retained_field
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (pReg : List Nat)
    (regOcc : (P2Query.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ).subAt
      0 pReg = some (.ty hlhs.reg.2))
    (sim : IotaRetainedSimulation tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) :=
  iota_retained_caseStep_of_reg_occ_ports Aw tbl w hlhs hrhs dl dr S σ ρ hrel
    ⟨pReg, regOcc, sim⟩

/-- `es_iota_retained_field` specialized to the reflexive-match residual
    `IotaRetainedRulePorts` (`matchL = matchR = ConvMod.refl`). -/
theorem es_iota_retained_field_of_rulePorts
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (pReg : List Nat)
    (regOcc : (P2Query.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ).subAt
      0 pReg = some (.ty hlhs.reg.2))
    (ports : IotaRetainedRulePorts tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) :=
  es_iota_retained_field Aw tbl w hlhs hrhs dl dr S σ ρ hrel pReg regOcc
    ports.toSimulation

/-- `StepSuppliers.es_iota_retained` when the stored endpoints coincide with
    the premise typings (`dl = hlhs`, `dr = hrhs` — every `enrichConvT` ι node
    and every landed instance): all four outer queries come from `StepIH`
    unconditionally; the sole residual is the general decoder simulation
    `sim` (`matchL`/`matchR` as `ConvMod (EStep tbl) LvlEq` legs). -/
theorem es_iota_retained_field_same_endpoints
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (hdl : dl = hlhs) (hdr : dr = hrhs)
    (sim : IotaRetainedSimulation tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) :=
  iota_retained_caseStep_same_endpoints Aw tbl w hlhs hrhs dl dr S σ ρ hrel
    hdl hdr sim.matchL sim.croot sim.beta sim.matchR

/-- `es_iota_retained_field_same_endpoints` specialized to the
    reflexive-match residual `IotaRetainedRulePorts`. -/
theorem es_iota_retained_field_same_endpoints_of_rulePorts
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ hlhs.reg.1) = false)
    (hdl : dl = hlhs) (hdr : dr = hrhs)
    (ports : IotaRetainedRulePorts tbl hlhs hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ lhs rhs T w hlhs hrhs dl dr) S σ ρ) :=
  es_iota_retained_field_same_endpoints Aw tbl w hlhs hrhs dl dr S σ ρ hrel
    hdl hdr ports.toSimulation

/-- On an `.app`-headed `hlhs` — the canonical ι-site shape (the recursor
    application) — `hlhs.reg.2` is the node's own `hT` field, so payload
    path `[0, 2]` resolves to it outright: `regOcc` is class (c). -/
theorem iota_regOcc_app
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f a A B rhs : Expr Nat} {u : Level}
    (w : DerivedIota E (.app f a) rhs)
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort u))
    (hrhs : TyP E n Γ rhs (instantiate0 a B))
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ rhs (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    (P2Query.es (CvP.iota E n Γ (.app f a) rhs (instantiate0 a B) w
        (TyP.app E n Γ f a A B u hf ha hT) hrhs dl dr) S σ ρ).subAt
      0 [0, 2] = some (.ty hT) :=
  rfl

/-- `es_iota_retained` on an `.app`-headed `hlhs`: the `regOcc` receipt is
    proved (`iota_regOcc_app`), so only the general decoder simulation `sim`
    remains. -/
theorem es_iota_retained_field_of_app
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f a A B rhs : Expr Nat} {u : Level}
    (w : DerivedIota E (.app f a) rhs)
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort u))
    (hrhs : TyP E n Γ rhs (instantiate0 a B))
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ rhs (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ u) = false)
    (sim : IotaRetainedSimulation tbl (TyP.app E n Γ f a A B u hf ha hT)
      hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ (.app f a) rhs (instantiate0 a B) w
        (TyP.app E n Γ f a A B u hf ha hT) hrhs dl dr) S σ ρ) :=
  es_iota_retained_field Aw tbl w (TyP.app E n Γ f a A B u hf ha hT) hrhs
    dl dr S σ ρ hrel [0, 2]
    (iota_regOcc_app w hf ha hT hrhs dl dr S σ ρ) sim

/-- `es_iota_retained_field_of_app` specialized to the reflexive-match
    residual `IotaRetainedRulePorts`. -/
theorem es_iota_retained_field_of_app_of_rulePorts
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {f a A B rhs : Expr Nat} {u : Level}
    (w : DerivedIota E (.app f a) rhs)
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort u))
    (hrhs : TyP E n Γ rhs (instantiate0 a B))
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ rhs (instantiate0 a B))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp)
    (hrel : levelIsZero (σ u) = false)
    (ports : IotaRetainedRulePorts tbl (TyP.app E n Γ f a A B u hf ha hT)
      hrhs σ ρ) :
    CaseStep Aw tbl (.es (CvP.iota E n Γ (.app f a) rhs (instantiate0 a B) w
        (TyP.app E n Γ f a A B u hf ha hT) hrhs dl dr) S σ ρ) :=
  es_iota_retained_field_of_app Aw tbl w hf ha hT hrhs dl dr S σ ρ hrel
    ports.toSimulation

/-! ## §2 The §7.4 expected-slot enumeration -/

/-- The §7.4 three-way read of one expected ι slot position against the
    original spines.  `originalApp`: the position's read returned an
    original `SpineOcc` whose path is empty — its views sit at the query's
    own context, issuable by the `occ_*` rows.  `wrappedNeed`: the read
    returned an occurrence reachable only through crossed transport/conv
    edges (`occ.path ≠ []` — e.g. the #7451 `esub`-hit continuation or the
    `esub`/`lsub` head-hit of #7584) — the need is real but its answers
    ride the wrapper route, not a same-site occurrence row.
    `missingExpectedSlot`: the position is expected by the witness but the
    spine read is out of range — reported, never dropped. -/
inductive IotaSlotRead where
  | originalApp (occ : SpineOcc)
  | wrappedNeed (occ : SpineOcc)
  | missingExpectedSlot

/-- A decidable tag for read classification (`decide`-friendly pins). -/
def IotaSlotRead.tag : IotaSlotRead → Nat
  | .originalApp _ => 0
  | .wrappedNeed _ => 1
  | .missingExpectedSlot => 2

/-- The occurrence a read returned, if any. -/
def IotaSlotRead.occ? : IotaSlotRead → Option SpineOcc
  | .originalApp occ => some occ
  | .wrappedNeed occ => some occ
  | _ => none

/-- Turn a spine read into the §7.4 verdict: present with empty path →
    `originalApp`; present behind crossed edges → `wrappedNeed`; absent →
    `missingExpectedSlot`. -/
def IotaSlotRead.ofOption : Option SpineOcc → IotaSlotRead
  | some occ => if occ.path.isEmpty then .originalApp occ else .wrappedNeed occ
  | none => .missingExpectedSlot

/-- The outermost (last-applied) occurrence of `hlhs`'s spine — the app
    node whose argument is the major. -/
def IotaSite.majorOcc (s : IotaSite E n Γ) : Option SpineOcc :=
  (s.hlhs.spineViews []).head?

/-- Read the major's constructor-argument spine at absolute index `i`
    (`ctorParams` occupy `0 ..< nparams`, the fields `nparams ..` — the
    constructor side keeps `lsC`/`ctorParams`, never the recursor-side
    prefix).  Each hit is re-wrapped in `occM`'s own path, so a major read
    through a transport marks the slot `wrappedNeed` too. -/
def IotaSite.readCtorSlot (s : IotaSite E n Γ) (i : Nat) : IotaSlotRead :=
  match s.majorOcc with
  | some occM =>
      IotaSlotRead.ofOption
        ((occM.ha.spineViewsInOrder[i]?).map
          fun o => { o with path := occM.path ++ o.path })
  | none => .missingExpectedSlot

/-- §7.4's total read: one expected position of `s` resolved against the
    ORIGINAL spines — `recArg j` and `major` on the recursor spine,
    `ctorParam j`/`ctorField j` on the major's constructor spine,
    `rhsRecResult j` on the rhs spine at the `j`-th `directRec` result
    index.  No `filterMap`: a failed read reports `missingExpectedSlot`. -/
def IotaSite.readExpectedSlot (s : IotaSite E n Γ) :
    IotaExpectedSlotPos s.w → IotaSlotRead
  | .recArg j => IotaSlotRead.ofOption (s.hlhs.spineViewsInOrder[j.val]?)
  | .major =>
      IotaSlotRead.ofOption (s.hlhs.spineViewsInOrder[s.w.preMajor.length]?)
  | .ctorParam j => s.readCtorSlot j.val
  | .ctorField j => s.readCtorSlot (s.w.nparams + j.val)
  | .rhsRecResult j =>
      IotaSlotRead.ofOption
        (s.hrhs.spineViewsInOrder[(recResultIdxs s.w.kinds 0).get j]?)

/-- `Fin n` enumerated in order (this toolchain has no `List.finRange`;
    built from `range` + `attach`). -/
def finsAll (n : Nat) : List (Fin n) :=
  (List.range n).attach.map fun i => ⟨i.1, List.mem_range.mp i.2⟩

/-- `finsAll n` has `n` elements. -/
theorem finsAll_length (n : Nat) : (finsAll n).length = n := by
  simp [finsAll, List.length_attach]

/-- The §7.4 expected positions of `w`, enumerated BEFORE reading:
    `recArg`s, then `major`, then `ctorParam`s, then `ctorField`s, then
    `rhsRecResult`s. -/
def IotaExpectedSlotPos.all {E : ResolvedEnv} (w : IotaWitness E) :
    List (IotaExpectedSlotPos w) :=
  (finsAll w.preMajor.length).map .recArg ++ [.major] ++
    (finsAll w.ctorParams.length).map .ctorParam ++
    (finsAll w.fields.length).map .ctorField ++
    (finsAll (recResultIdxs w.kinds 0).length).map .rhsRecResult

/-- The enumeration's cardinality is the §7.4 expected count —
    `w.preMajor.length + 1 + w.ctorParams.length + w.fields.length +
    (recResultIdxs w.kinds 0).length`, i.e. `planSlotCount w +
    w.ctorParams.length`. -/
theorem IotaExpectedSlotPos.all_length {E : ResolvedEnv} (w : IotaWitness E) :
    (IotaExpectedSlotPos.all w).length = expectedIotaSlotCount w := by
  simp only [IotaExpectedSlotPos.all, expectedIotaSlotCount, List.length_append,
    List.length_map, finsAll_length, List.length_cons, List.length_nil]

/-- Read every expected position — the §7.4 slot family in full. -/
def IotaSite.expectedReads (s : IotaSite E n Γ) : List IotaSlotRead :=
  (IotaExpectedSlotPos.all s.w).map s.readExpectedSlot

/-- `expectedReads` has exactly `expectedIotaSlotCount s.w` entries — the
    enumeration is total whether or not reads succeed. -/
theorem IotaSite.expectedReads_length (s : IotaSite E n Γ) :
    s.expectedReads.length = expectedIotaSlotCount s.w := by
  simp only [IotaSite.expectedReads, List.length_map,
    IotaExpectedSlotPos.all_length]



/-- `occ?` of an `ofOption` read is the option itself. -/
theorem IotaSlotRead.occ?_ofOption (o : Option SpineOcc) :
    (IotaSlotRead.ofOption o).occ? = o := by
  cases o with
  | none => rfl
  | some a =>
      show (if a.path.isEmpty then IotaSlotRead.originalApp a
        else IotaSlotRead.wrappedNeed a).occ? = some a
      split <;> rfl

/-- `head?` membership (the outermost spine view belongs to the list). -/
private theorem mem_of_head?_eq_some {α : Type} {l : List α} {a : α}
    (hm : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => simp at hm
  | cons x xs =>
      simp only [List.head?_cons, Option.some.injEq] at hm
      subst hm; exact .head _

/-- Constructor-spine reads (`ctorParam`/`ctorField`): the returned
    occurrence is a member of the major argument's own spine, re-wrapped
    in the major occurrence's path — everything bounded by `hlhs.wt`. -/
private theorem IotaSite.readCtorSlot_occ_below (Aw : Nat → Nat)
    (s : IotaSite E n Γ) (i : Nat) {occ : SpineOcc}
    (hocc : (s.readCtorSlot i).occ? = some occ) :
    ∃ W, W < s.N Aw ∧
      occ.hf.wt Aw < W ∧ occ.ha.wt Aw < W ∧ occ.hT.wt Aw < W ∧
      (∀ c, occ.argConv = some c → c.wt Aw < W) ∧
      (∀ e ∈ occ.path, e.view.wt Aw ≤ W ∧ e.source.wt Aw < W ∧
        (∀ c, e.cvp = some c → c.wt Aw < W)) := by
  simp only [IotaSite.readCtorSlot, IotaSite.majorOcc] at hocc
  cases hm : (s.hlhs.spineViews []).head? with
  | none =>
      rw [hm] at hocc
      exact Option.noConfusion hocc
  | some occM =>
      rw [hm, IotaSlotRead.occ?_ofOption] at hocc
      -- hocc : Option.map (· path-wrap) (occM.ha.spineViewsInOrder[i]?)
      --        = some occ
      cases hget : occM.ha.spineViewsInOrder[i]? with
      | none => rw [hget] at hocc; simp at hocc
      | some o =>
          rw [hget] at hocc
          simp only [Option.map_some', Option.some.injEq] at hocc
          subst hocc
          -- goals mention {o with path := occM.path ++ o.path}
          have hoccM : occM ∈ s.hlhs.spineViews [] :=
            mem_of_head?_eq_some hm
          obtain ⟨_hMhf, hMha, _hMhT, _hMarg, hMpath⟩ :=
            TyP.spineViews_wt_le Aw s.hlhs [] _ (Nat.le_refl _)
              (by intro e he; simp at he) occM hoccM
          have ho_in : o ∈ occM.ha.spineViews [] :=
            List.mem_reverse.mp (List.getElem?_mem hget)
          obtain ⟨hohf, hoha, hohT, hoarg, hopath⟩ :=
            TyP.spineViews_wt_le Aw occM.ha [] _ (Nat.le_refl _)
              (by intro e he; simp at he) o ho_in
          refine ⟨s.hlhs.wt Aw, s.hlhs_lt_N Aw, ?_, ?_, ?_, ?_, ?_⟩
          · exact Nat.lt_trans hohf hMha
          · exact Nat.lt_trans hoha hMha
          · exact Nat.lt_trans hohT hMha
          · intro c hc
            exact Nat.lt_trans (hoarg c hc) hMha
          · intro e he
            rcases List.mem_append.mp he with hout | hin
            · exact hMpath e hout
            · obtain ⟨hv, hs2, hcvp2⟩ := hopath e hin
              exact ⟨Nat.le_trans hv (Nat.le_of_lt hMha),
                     Nat.lt_trans hs2 hMha,
                     fun c hc => Nat.lt_trans (hcvp2 c hc) hMha⟩

/-- Every occurrence a §7.4 read returns is bounded strictly below the
    site's caller budget `N` — the bound covers the full expected family
    (constructor parameters included), not only `planIota`'s returned
    slots. -/
theorem IotaSite.readExpectedSlot_occ_below (Aw : Nat → Nat)
    (s : IotaSite E n Γ) {pos : IotaExpectedSlotPos s.w} {occ : SpineOcc}
    (h : s.readExpectedSlot pos = .originalApp occ ∨
         s.readExpectedSlot pos = .wrappedNeed occ) :
    ∃ W, W < s.N Aw ∧
      occ.hf.wt Aw < W ∧ occ.ha.wt Aw < W ∧ occ.hT.wt Aw < W ∧
      (∀ c, occ.argConv = some c → c.wt Aw < W) ∧
      (∀ e ∈ occ.path, e.view.wt Aw ≤ W ∧ e.source.wt Aw < W ∧
        (∀ c, e.cvp = some c → c.wt Aw < W)) := by
  have hocc : (s.readExpectedSlot pos).occ? = some occ := by
    rcases h with h | h <;> rw [h] <;> rfl
  cases pos with
  | recArg j =>
      simp only [IotaSite.readExpectedSlot, IotaSlotRead.occ?_ofOption] at hocc
      refine ⟨s.hlhs.wt Aw, s.hlhs_lt_N Aw, ?_⟩
      exact TyP.spineViews_wt_le Aw s.hlhs [] _ (Nat.le_refl _)
        (by intro e he; simp at he) _
        (List.mem_reverse.mp (List.getElem?_mem hocc))
  | major =>
      simp only [IotaSite.readExpectedSlot, IotaSlotRead.occ?_ofOption] at hocc
      refine ⟨s.hlhs.wt Aw, s.hlhs_lt_N Aw, ?_⟩
      exact TyP.spineViews_wt_le Aw s.hlhs [] _ (Nat.le_refl _)
        (by intro e he; simp at he) _
        (List.mem_reverse.mp (List.getElem?_mem hocc))
  | ctorParam j =>
      exact IotaSite.readCtorSlot_occ_below Aw s j.val hocc
  | ctorField j =>
      exact IotaSite.readCtorSlot_occ_below Aw s (s.w.nparams + j.val) hocc
  | rhsRecResult j =>
      simp only [IotaSite.readExpectedSlot, IotaSlotRead.occ?_ofOption] at hocc
      refine ⟨s.hrhs.wt Aw, s.hrhs_lt_N Aw, ?_⟩
      exact TyP.spineViews_wt_le Aw s.hrhs [] _ (Nat.le_refl _)
        (by intro e he; simp at he) _
        (List.mem_reverse.mp (List.getElem?_mem hocc))

/-! ## §3 Pins on the landed fixtures -/

/-- The `List.cons` ι site — `s18H`'s own four occurrences. -/
noncomputable def listConsIotaSite : IotaSite listEnvUT 0 [] where
  T := .const 0 []
  w := wConsNat
  d := DerivedIota.of wConsNat
  hlhs := s18hL
  hrhs := s18hR
  dl := s18hL
  dr := s18hR

/-- PIN (§7.4): the enumeration on `wConsNat` has `9` positions — one more
    than `planIota`'s `8` slots; the extra is `ctorParam 0` (the `A` of the
    `cons` major). -/
theorem listConsIotaSite_all_length :
    (IotaExpectedSlotPos.all wConsNat).length = 9 := rfl

/-- PIN (§7.4): `expectedReads` on the List.cons site reads all nine
    expected positions, one per enumerated slot — the `ctorParam` family is
    no longer silently absent. -/
theorem listConsIotaSite_expectedReads_length :
    listConsIotaSite.expectedReads.length = 9 :=
  IotaSite.expectedReads_length listConsIotaSite

/-- PIN (§7.4 gap, exhibited): `planIota` still returns `8` slots on the
    same site — the dropped `ctorParam` is named, not silently closed. -/
theorem listConsIotaSite_plan_slots :
    (planIota listConsIotaSite).slots.length = 8 := by
  decide

/-- PIN (§7.4): on the Nat site the five lhs-side reads (`recArg`s,
    `major`, `ctorField`) report `wrappedNeed` — the enriched `s16hL`
    natively carries a wrapper edge, so `originalApp` (an occurrence at
    the query's own context) is narrower than the spine's raw coverage —
    while the rhs `directRec` read on unwrapped `s16hR` is `originalApp`. -/
theorem natIotaSite_expectedReads_tags :
    natIotaSite.expectedReads.map IotaSlotRead.tag =
      [1, 1, 1, 1, 1, 0] := by
  decide

/-- PIN (§7.4 wrapped route): on the #7451 `esub`-hit site, the five
    lhs-side reads (`recArg`s, `major`, `ctorField`) report `wrappedNeed` —
    the spine is present but the occurrences cross the `esub` edge — while
    the rhs `directRec` read stays `originalApp` (`hrhs = s16hR` is
    unwrapped). -/
theorem natIotaSiteEsub_expectedReads_tags :
    natIotaSiteEsub.expectedReads.map IotaSlotRead.tag =
      [1, 1, 1, 1, 1, 0] := by
  decide

/-- PIN (§7.4 wrapped route, both sides): on the identity-`ewk` site every
    read — lhs and rhs — crosses the `ewk` edge; all six report
    `wrappedNeed`. -/
theorem natIotaSiteEwk_expectedReads_tags :
    natIotaSiteEwk.expectedReads.map IotaSlotRead.tag =
      [1, 1, 1, 1, 1, 1] := by
  decide

/-- PIN (§7.4 provenance): `ctorParam 0` on the List.cons site resolves to
    the `A` argument occurrence (`listConsA`) — the slot `planIota` drops
    is a real spine occurrence of the constructor prefix. -/
theorem listConsIotaSite_ctorParam0 :
    (listConsIotaSite.readExpectedSlot (.ctorParam ⟨0, by decide⟩)).occ?.map
      (·.a) = some listConsA := by
  decide

/-- PIN (§7.4 enumeration): `wVcons`'s expected positions number `11`
    (the `ctorParam` included) — `planSlotCount` remains `10`. -/
theorem wVcons_all_length :
    (IotaExpectedSlotPos.all wVcons).length = 11 := rfl

/-- The general decoder field instantiated on the Nat fixture via the
    reflexive specialization: the same `natSucc_croot`/`s17_beta_witness`
    evidence packaged as `IotaRetainedRulePorts`. -/
theorem natSucc_es_iota_retained_via_field
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) :
    CaseStep Aw natSuccTable (.es H S id []) :=
  es_iota_retained_field_same_endpoints_of_rulePorts Aw natSuccTable
    (DerivedIota.of wSuccU1) hL hR hL hR S id [] (by rw [s17_hL_reg1]; rfl)
    rfl rfl ⟨_, natSucc_croot, s17_beta_witness⟩

/-- The general decoder field instantiated on the List.cons fixture via the
    reflexive specialization. -/
theorem listCons_es_iota_retained_via_field
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) :
    CaseStep Aw listConsTable (.es s18H S id []) :=
  es_iota_retained_field_same_endpoints_of_rulePorts Aw listConsTable
    (DerivedIota.of wConsNat) s18hL s18hR s18hL s18hR
    S id [] rfl rfl rfl ⟨_, listCons_croot, s18_beta_witness⟩

/-- PIN: no expected slot on the Nat site is `missingExpectedSlot` — the
    enumeration's coverage is total on the landed fixture. -/
theorem natIotaSite_expectedReads_no_missing :
    natIotaSite.expectedReads.map IotaSlotRead.tag |>.all (· < 2) := by
  decide

/-- PIN (§7.4 missing route, definitional): an absent slot read classifies
    as `missingExpectedSlot` — out-of-range expected slots are reported,
    not silently omitted. -/
theorem iotaSlotRead_ofOption_none :
    IotaSlotRead.ofOption (none : Option SpineOcc) =
      .missingExpectedSlot := rfl

end Rcic.Syn

#print axioms Rcic.Syn.IotaRetainedRulePorts
#print axioms Rcic.Syn.IotaRetainedRulePorts.toSimulation
#print axioms Rcic.Syn.es_iota_retained_field
#print axioms Rcic.Syn.es_iota_retained_field_of_rulePorts
#print axioms Rcic.Syn.es_iota_retained_field_same_endpoints
#print axioms Rcic.Syn.es_iota_retained_field_same_endpoints_of_rulePorts
#print axioms Rcic.Syn.iota_regOcc_app
#print axioms Rcic.Syn.es_iota_retained_field_of_app
#print axioms Rcic.Syn.es_iota_retained_field_of_app_of_rulePorts
#print axioms Rcic.Syn.IotaSlotRead
#print axioms Rcic.Syn.IotaSlotRead.tag
#print axioms Rcic.Syn.IotaSlotRead.occ?
#print axioms Rcic.Syn.IotaSlotRead.ofOption
#print axioms Rcic.Syn.IotaSlotRead.occ?_ofOption
#print axioms Rcic.Syn.finsAll
#print axioms Rcic.Syn.finsAll_length
#print axioms Rcic.Syn.IotaSite.majorOcc
#print axioms Rcic.Syn.IotaSite.readCtorSlot
#print axioms Rcic.Syn.IotaSite.readExpectedSlot
#print axioms Rcic.Syn.IotaExpectedSlotPos.all
#print axioms Rcic.Syn.IotaExpectedSlotPos.all_length
#print axioms Rcic.Syn.IotaSite.expectedReads
#print axioms Rcic.Syn.IotaSite.expectedReads_length
#print axioms Rcic.Syn.IotaSite.readExpectedSlot_occ_below
#print axioms Rcic.Syn.listConsIotaSite
#print axioms Rcic.Syn.listConsIotaSite_all_length
#print axioms Rcic.Syn.listConsIotaSite_expectedReads_length
#print axioms Rcic.Syn.listConsIotaSite_plan_slots
#print axioms Rcic.Syn.natIotaSite_expectedReads_tags
#print axioms Rcic.Syn.natIotaSiteEsub_expectedReads_tags
#print axioms Rcic.Syn.natIotaSiteEwk_expectedReads_tags
#print axioms Rcic.Syn.listConsIotaSite_ctorParam0
#print axioms Rcic.Syn.wVcons_all_length
#print axioms Rcic.Syn.natIotaSite_expectedReads_no_missing
#print axioms Rcic.Syn.iotaSlotRead_ofOption_none
#print axioms Rcic.Syn.natSucc_es_iota_retained_via_field
#print axioms Rcic.Syn.listCons_es_iota_retained_via_field
