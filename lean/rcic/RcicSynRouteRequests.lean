import rcic.RcicSynDisplayRoute

/-!
# S16 — `CallPlan` and `routeOfCall` (§6, with §4's subject roles)

`research/rcic/sortrow/S16_DISPLAY_ROUTE_DATATYPE.md` §6: every internal
request has a route. `CallPlan F p` is the request-code grammar indexed by the
parent place (the index carries the place equality, so `routeOfCall` produces
routes literally ending in real edges — no cast edges, no `.same` loops).

- Same-context calls (`originalField`/`reg`/`dl`/`dr`) answer with the same
  route `r` — sibling, reg and dl/dr requests reuse it.
- Body calls (`assumeBody`/`letBody`) append the real body edge.
- Transport calls (`wkSource`–`cctxSource`) append the transport's source edge.
- `tail`/`admission` append their real edges.
- Replacements `replacementHV`/`replacementHVT` return the **target** route —
  `hv`/`hvT` are read under the target, never the freshly generated source.
- `cctxBridge` appends the target's `tail` edge — the bridge sits at the tail,
  not in the source context with the new head.

This covers route generation only: no semantic validity, no rank descent, and
`eval` still calls no P2/`hcoh`/`CL`/`PBit`. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- §4's `ParentRole`: which role of the parent expression the callee compares. -/
inductive ParentRole : Type where
  | term | ascribedType | lhs | rhs | binderDomain | binderBody
  | storedValue | memberType | memberBody | actualArgument (j : Nat)
  deriving DecidableEq, Repr

/-- §4's exact native relation, per edge — forward maps only, no inversion:
    `wk` lifts, `esub`/`lsub` instantiate, `linst` instantiates levels,
    `ewk`/`cctx`/bodies/tails/admissions keep the role expression itself. -/
def RouteEdge.subject {F : RawForest} {p q : Place} :
    RouteEdge F p q → Expr Nat → Expr Nat → Prop
  | .wkSource s => fun eP eC => eP = lift s.c 1 eC
  | .esubSource s => fun eP eC => eP = instantiate s.j (lift 0 s.j s.v) eC
  | .lsubSource s => fun eP eC => eP = instantiate s.j (lift 0 s.j s.v) eC
  | .linstSource s => fun eP eC => eP = instantiateLevels s.ls eC
  | _ => fun eP eC => eP = eC

/-- §6's request codes, indexed by the parent place. The constructor's index
    is the real `Site`'s parent/target/caller place, so a `CallPlan F p` at a
    route's destination is exactly a call that route's parent can issue. -/
inductive CallPlan (F : RawForest) : Place → Type where
  | originalField {p : Place} : CallPlan F p
  | reg {p : Place} : CallPlan F p
  | dl {p : Place} : CallPlan F p
  | dr {p : Place} : CallPlan F p
  | assumeBody (s : AssumeBodySite F) : CallPlan F s.parent
  | letBody (s : LetBodySite F) : CallPlan F s.parent
  | wkSource (s : WkSite F) : CallPlan F s.target
  | esubSource (s : EsubSite F) : CallPlan F s.target
  | lsubSource (s : LsubSite F) : CallPlan F s.target
  | linstSource (s : LinstSite F) : CallPlan F s.target
  | ewkSource (s : EwkSite F) : CallPlan F s.target
  | cctxSource (s : CctxSite F) : CallPlan F s.target
  | tail (s : TailSite F) : CallPlan F s.parent
  | cctxBridge (t : TailSite F) : CallPlan F t.parent
  | admission (s : AdmissionSite F) : CallPlan F s.caller
  | replacementHV {p : Place} : CallPlan F p
  | replacementHVT {p : Place} : CallPlan F p

/-- The place the call's answer route must land at. -/
def CallPlan.place {F : RawForest} {p : Place} : CallPlan F p → Place
  | .originalField | .reg | .dl | .dr | .replacementHV | .replacementHVT => p
  | .assumeBody s | .letBody s | .tail s | .cctxBridge s => s.child
  | .wkSource s | .esubSource s | .lsubSource s | .linstSource s
  | .ewkSource s | .cctxSource s => s.source
  | .admission s => s.stored

/-- §6: every internal request has a route. Same-context calls return `r`;
    real calls append the site's real edge; replacements return the target
    route; `cctxBridge` steps to the target's tail. -/
def routeOfCall {F : RawForest} {p : Place} (r : DisplayRoute F p) :
    (c : CallPlan F p) → DisplayRoute F c.place
  | .originalField => r
  | .reg => r
  | .dl => r
  | .dr => r
  | .replacementHV => r
  | .replacementHVT => r
  | .assumeBody s => r.step (.assumeBody s)
  | .letBody s => r.step (.letBody s)
  | .wkSource s => r.step (.wkSource s)
  | .esubSource s => r.step (.esubSource s)
  | .lsubSource s => r.step (.lsubSource s)
  | .linstSource s => r.step (.linstSource s)
  | .ewkSource s => r.step (.ewkSource s)
  | .cctxSource s => r.step (.cctxSource s)
  | .tail s => r.step (.tail s)
  | .cctxBridge t => r.step (.tail t)
  | .admission s => r.step (.admission s)

/-- The route's destination place — its own index. -/
def DisplayRoute.dest {F : RawForest} {p : Place} (_ : DisplayRoute F p) : Place := p

/-- The level map the call leaves: `linstSource`/`admission` compose the
    stored `ls`; every other call keeps `σ`. -/
def CallPlan.mapOf {F : RawForest} {p : Place} (c : CallPlan F p)
    (σ : Level → Level) : Level → Level :=
  match c with
  | .linstSource s | .admission s => fun l => σ (instLevel s.ls l)
  | _ => σ

/-- The display `ρ` the call leaves, computed per the §3 table. -/
def CallPlan.dispOf {F : RawForest} {p : Place} (c : CallPlan F p)
    (σ : Level → Level) (ρ : List Disp) : List Disp :=
  match c with
  | .assumeBody s => binderDisp (levelIsZero (σ s.payload.u)) :: ρ
  | .letBody s =>
      (if s.hv.eps σ ρ = .star then .drop else .inline (s.hv.eps σ ρ)) :: ρ
  | .wkSource s => removeAt ρ s.c
  | .esubSource s => insertDisp (binderDisp (levelIsZero (σ s.u))) s.j ρ
  | .lsubSource s =>
      insertDisp (if s.hv.eps σ ρ = .star then .drop
        else .inline (localize (countKeep (ρ.take s.j)) (s.hv.eps σ ρ))) s.j ρ
  | .tail s | .cctxBridge s => ρ.drop s.k
  | .admission _ => []
  | _ => ρ

/-- The edge a call appends, for the subject/original-references readout. -/
def CallPlan.edgeRefs {F : RawForest} {p : Place} : CallPlan F p → List (FieldPath F)
  | .originalField | .reg | .dl | .dr | .replacementHV | .replacementHVT => []
  | .assumeBody s | .letBody s | .wkSource s | .esubSource s | .lsubSource s
  | .linstSource s | .ewkSource s | .cctxSource s | .tail s | .cctxBridge s
  | .admission s => [s.owner]

/-- §4's subject relation of the edge the call appends (`none` when the call
    keeps the same route). -/
def CallPlan.subject {F : RawForest} {p : Place} :
    CallPlan F p → Option (Expr Nat → Expr Nat → Prop)
  | .assumeBody s => some (RouteEdge.assumeBody s).subject
  | .letBody s => some (RouteEdge.letBody s).subject
  | .wkSource s => some (RouteEdge.wkSource s).subject
  | .esubSource s => some (RouteEdge.esubSource s).subject
  | .lsubSource s => some (RouteEdge.lsubSource s).subject
  | .linstSource s => some (RouteEdge.linstSource s).subject
  | .ewkSource s => some (RouteEdge.ewkSource s).subject
  | .cctxSource s => some (RouteEdge.cctxSource s).subject
  | .tail s => some (RouteEdge.tail s).subject
  | .cctxBridge t => some (RouteEdge.tail t).subject
  | .admission s => some (RouteEdge.admission s).subject
  | _ => none

/-- The subject relation of a route's last edge (`none` at the root). -/
def DisplayRoute.lastSubject {F : RawForest} {p : Place} :
    DisplayRoute F p → Option (Expr Nat → Expr Nat → Prop)
  | .root _ => none
  | .step _ e => some e.subject

/-- The original `FieldPath`s a route's sites reference, in route order. -/
def RouteEdge.refs {F : RawForest} {p q : Place} : RouteEdge F p q → List (FieldPath F)
  | .assumeBody s => [s.owner]
  | .letBody s => [s.owner]
  | .wkSource s => [s.owner]
  | .esubSource s => [s.owner]
  | .lsubSource s => [s.owner]
  | .linstSource s => [s.owner]
  | .ewkSource s => [s.owner]
  | .cctxSource s => [s.owner]
  | .tail s => [s.owner]
  | .admission s => [s.owner]

/-- The original `FieldPath`s referenced along a route. -/
def DisplayRoute.refs {F : RawForest} {p : Place} : DisplayRoute F p → List (FieldPath F)
  | .root s => [s.owner]
  | .step r e => r.refs ++ e.refs

/-- `routeOfCall` lands where the call asks. -/
theorem routeOfCall_place {F : RawForest} {p : Place} (r : DisplayRoute F p)
    (c : CallPlan F p) : (routeOfCall r c).dest = c.place := by
  cases c <;> rfl

/-- `routeOfCall` carries the level map the §3 table computes. -/
theorem routeOfCall_map {F : RawForest} {p : Place} (r : DisplayRoute F p)
    (c : CallPlan F p) :
    (eval (routeOfCall r c)).map = c.mapOf (eval r).map := by
  cases c <;> rfl

/-- `routeOfCall` carries the display `ρ` the §3 table computes. -/
theorem routeOfCall_rho {F : RawForest} {p : Place} (r : DisplayRoute F p)
    (c : CallPlan F p) :
    (eval (routeOfCall r c)).disp = c.dispOf (eval r).map (eval r).disp := by
  cases c <;> rfl

/-- `routeOfCall` leaves the appended edge's §4 subject relation; same-route
    calls keep the route's own last relation. -/
theorem routeOfCall_subject {F : RawForest} {p : Place} (r : DisplayRoute F p)
    (c : CallPlan F p) :
    (routeOfCall r c).lastSubject = c.subject.orElse fun _ => r.lastSubject := by
  cases c <;> rfl

/-- `routeOfCall` extends the original-references ledger by exactly the
    appended edge's owner. -/
theorem routeOfCall_originalRefs {F : RawForest} {p : Place} (r : DisplayRoute F p)
    (c : CallPlan F p) :
    (routeOfCall r c).refs = r.refs ++ c.edgeRefs := by
  cases c <;> simp [routeOfCall, DisplayRoute.refs, CallPlan.edgeRefs, RouteEdge.refs]

end Rcic.Syn
