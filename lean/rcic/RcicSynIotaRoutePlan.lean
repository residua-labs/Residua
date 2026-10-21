import rcic.RcicSynEnrich
import rcic.RcicSynDomPath
import rcic.RcicDTMetaTypedSR
import rcic.RcicTypedGroupPins
import rcic.RcicFixtures

/-!
# S16 §4.4 / §4.6 rows 1–3 — the ι request-plan layer

`research/rcic/sortrow/S16_BVAR_CCTX_IOTA_STEPS.md` (§4.4 "Real slot
requests are never replaced by a same-rank 'spine ready'"; §4.6 rows
1–3). An `IotaSite` packages the ORIGINAL ι conversion node's data: the
witness `w`, its `DerivedIota`, and the four stored premise typings
(`hlhs`/`hrhs`/`dl`/`dr` — the "hlhs forest" the spec's plan reads
from). The admission origin is `w`'s own member lookups
(`w.hrec`/`w.hctor`/`w.hfam`), never re-derived.

`planIota` computes the finite slot set from that forest alone: every
real argument typing of the original recursor application (`hlhs`'s
spine, in original argument order — `.spine j`), every constructor-field
typing inside the major argument's own spine after the ctor's `nparams`
parameter args (`.majorField j`), and every directRec-result argument of
the original rhs's spine (`.rhsDirectRec r`, positions read off
`w.kinds`).

Each slot is a `SpineOcc`: the `.app` node's own fields at its own
context — `hf : TyP _ _ _ f (.pi A B)` (the admission receipt — `pD`
is derived from its regularity: `TyP.piDomSrc` walks `hf.reg.2` to the
innermost `.pi` node, takes its stored domain field
`hA : TyP _ _ _ A₀ (.sort v)`, and re-displays it through the SAME
`wk`/`esub`/`lsub`/`linst`/`ewk`/`cctx` frames carrying those nodes'
own stored fields — the original admission-domain sort typing
re-instantiated, strictly lighter than `hf`, typing the domain as
displayed at `hf`'s context so `BIT[pN, pD]` is same-subject,
same-context), `ha` is the argument typing `qa`, `hT` the result
sort-typing — plus the
wrapper `path` from the forest root (`PathEdge` per crossed
`wk`/`esub`/`lsub`/`linst`/`ewk`/`cctx`/`conv`, outermost first, storing
the wrapper node, its source child, and the crossed conversion). `pN`
is derived (`qa.reg.2`), never stored. Pending views are boxed
(`TyPAny`/`CvPAny`) so an occurrence under a transport keeps the
derivation at the context where it actually lives — a demand is never
dropped: wrapping `hlhs`/`hrhs` in an identity `ewk` still yields every
slot (`natIotaPlan_ewk_*` controls). There are no success-answer fields
anywhere — `IotaRequestPlan` is class-(a) structural data.

`request_of_iota_slot plan j` emits the slot's §4.4 request set —
`PB[qa, pN]` and `BIT[pN, pD]` always; the conv-K1 pair
(`BIT[pN, c.dl]`, `BIT[c.dr, pD]`, `ES[c]`) when the argument typing is
itself `.conv`-headed (`argConv`); and per crossed path edge the row's
other shapes where they apply — `ES[c]` + endpoint `CL` + subject
`EUT`/`CL`/`TagCoh` for a `.conv` edge, the same-subject `CL`/`TagCoh`
for subject-preserving transports (`ewk`/`cctx`), the two-views `BIT`
for `linst`, `TagCoh` for `wk`/`esub`/`lsub`.

`iota_slot_request_below` is the real edge from real fields: every
derivation any emitted request stores is strictly below the site's node
weight `N = node.wt Aw` — occurrence fields are genuine subderivations
(`TyP.spineViews_wt_le`), path-edge views are bounded by the forest
root, `pN`'s bound is `qa`'s by `TyP.wt_reg_le`, `pD`'s is `hf`'s
(`TyP.piDomSrc_wt_lt` ∘ `TyP.wt_reg_le` — the view re-applies the
original frames on their own stored fields, strictly lighter than the
nodes it mirrors), and conv endpoints
by `CvP.wt_dl_lt`/`wt_dr_lt`. A request whose effective input still
contains H's whole active N can never satisfy this edge — the bound is
strict, so a same-rank "spine ready" supplier is excluded by
construction.

First users: the Nat-successor instance (`natIotaSite` over `wSuccU1` —
all four forest typings built from main's `pinIota*` producers, never
`pin_iotaPreserveT`/`InScope`; six slots, one per §4's table row) and
ct001's List-cons instance over `wCons` (its typed lhs is still open;
its below edge is the same theorem over any `wCons` site, and the plan's
slot shape is pinned at the witness level: `listCons_slotCount = 8`).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## boxed derivation views -/

/-- A typing derivation boxed over its own env/level/context — the
    pending-view currency: an occurrence reached through transports keeps
    the derivation at the context where it actually lives. -/
structure TyPAny where
  E : ResolvedEnv
  n : Nat
  Γ : LCtx
  e : Expr Nat
  T : Expr Nat
  der : TyP E n Γ e T

/-- The boxed conversion's left endpoint typing, boxed at the same
    env/level/context (`CvPAny` itself is declared once in
    `RcicSynDomPath`). -/
def CvPAny.dl : CvPAny → TyPAny
  | .mk c => ⟨_, _, _, _, _, c.dl⟩

/-- The boxed conversion's right endpoint typing, boxed. -/
def CvPAny.dr : CvPAny → TyPAny
  | .mk c => ⟨_, _, _, _, _, c.dr⟩

/-- The stored derivation's weight. -/
def TyPAny.wt (Aw : Nat → Nat) (D : TyPAny) : Nat := D.der.wt Aw

/-- The boxed conversion's weight. -/
def CvPAny.wt (Aw : Nat → Nat) : CvPAny → Nat
  | .mk c => c.wt Aw

/-- The stored derivation's atom multiset. -/
def TyPAny.atoms (Aw : Nat → Nat) (D : TyPAny) : List Nat := D.der.atoms Aw

/-- The boxed conversion's atom multiset. -/
def CvPAny.atoms (Aw : Nat → Nat) : CvPAny → List Nat
  | .mk c => c.atoms Aw

/-- `dl` is strictly lighter than the boxed conversion. -/
theorem CvPAny.wt_dl_lt (Aw : Nat → Nat) : (c : CvPAny) → c.dl.wt Aw < c.wt Aw
  | .mk c => CvP.wt_dl_lt Aw c

/-- `dr` is strictly lighter than the boxed conversion. -/
theorem CvPAny.wt_dr_lt (Aw : Nat → Nat) : (c : CvPAny) → c.dr.wt Aw < c.wt Aw
  | .mk c => CvP.wt_dr_lt Aw c

/-- The original domain-sort view inside a `pi A B` typing: the
    innermost `.pi` node's own stored `hA`, re-displayed through the
    SAME transport frames the original derivation crossed — each
    `wk`/`esub`/`lsub`/`linst`/`ewk`/`cctx` node is re-applied to the
    extracted view carrying that node's OWN stored fields, so nothing
    is re-derived and the result types the same displayed domain at the
    input's context (the `esub`/`lsub` `.here` branch reads the
    replacement `hv` — already at the outer context — so the frame is
    not re-applied there; `conv` only re-types the `pi`'s sort index,
    the domain view passes through). This is the §4.4 admission-domain
    view `pD`: the domain's stored sort typing whose display is the
    transported domain — `BIT[pN, pD]`'s two operands are same-subject,
    same-context `domain : sort` typings (S16 §5/§6 SubjectLink). -/
def TyP.piDomSrc : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T A B : Expr Nat} → TyP E n Γ e T → e = .pi A B →
    Σ' (e' T' : Expr Nat), TyP E n Γ e' T'
  | _, _, _, _, _, _, _, .sort .., he => by cases he
  | _, _, _, _, _, _, _, .bvar .., he => by cases he
  | _, _, _, _, _, _, _, .const .., he => by cases he
  | _, _, _, _, _, _, _, .pi _ _ _ _ _ _ _ hA _, _ =>
      ⟨_, _, hA⟩
  | _, _, _, _, _, _, _, .lam .., he => by cases he
  | _, _, _, _, _, _, _, .app .., he => by cases he
  | _, _, _, _, _, _, _, .letE .., he => by cases he
  | _, _, _, _, _, _, _, .lit .., he => by cases he
  | _, _, _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, he =>
      TyP.piDomSrc h he
  | _, _, _, _, _, _, _, .wk _ _ _ _ _ d c inner, he =>
      match lift_eq_pi he with
      | .mk _ _ he₀ _ _ =>
          let r := TyP.piDomSrc inner he₀
          ⟨_, _, .wk _ _ _ _ _ d c r.2.2⟩
  | _, _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ inner hget hv hvT, he =>
      match instantiate_eq_pi he with
      | .under _ _ he₀ _ _ =>
          let r := TyP.piDomSrc inner he₀
          ⟨_, _, .esub _ _ _ _ _ _ _ _ _ r.2.2 hget hv hvT⟩
      | .here _ hr => TyP.piDomSrc hv hr
  | _, _, _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ inner hget hv hvT, he =>
      match instantiate_eq_pi he with
      | .under _ _ he₀ _ _ =>
          let r := TyP.piDomSrc inner he₀
          ⟨_, _, .lsub _ _ _ _ _ _ _ _ _ r.2.2 hget hv hvT⟩
      | .here _ hr => TyP.piDomSrc hv hr
  | _, _, _, _, _, _, _, .linst _ _ _ _ _ _ _ hls hlen inner, he =>
      match instantiateLevels_eq_pi he with
      | .mk _ _ he₀ _ _ =>
          let r := TyP.piDomSrc inner he₀
          ⟨_, _, .linst _ _ _ _ _ _ _ hls hlen r.2.2⟩
  | _, _, _, _, _, _, _, .ewk _ _ _ _ _ _ hext inner, he =>
      let r := TyP.piDomSrc inner he
      ⟨_, _, .ewk _ _ _ _ _ _ hext r.2.2⟩
  | _, _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ inner hconv, he =>
      let r := TyP.piDomSrc inner he
      ⟨_, _, .cctx _ _ _ _ _ _ _ _ r.2.2 hconv⟩

/-- The displayed domain view is strictly lighter than the `pi` typing
    it is read from: the `.pi` step descends into the stored `hA`, and
    each re-applied wrapper is lighter than the node it mirrors — the
    extracted view is `< inner`, the crossed `hv`/`hvT`/`hconv` fields
    are reused verbatim (nothing is re-derived, no `ewk` is invented —
    unlike `piInvP`, whose `esub` rebuild weakens the replacement
    pair). -/
theorem TyP.piDomSrc_wt_lt (Aw : Nat → Nat) : {E : ResolvedEnv} →
    {n : Nat} → {Γ : LCtx} → {e T A B : Expr Nat} →
    (D : TyP E n Γ e T) → (he : e = .pi A B) →
    (TyP.piDomSrc D he).2.2.wt Aw < D.wt Aw
  | _, _, _, _, _, _, _, .sort .., he => by cases he
  | _, _, _, _, _, _, _, .bvar .., he => by cases he
  | _, _, _, _, _, _, _, .const .., he => by cases he
  | _, _, _, _, _, _, _, .pi _ _ _ _ _ _ _ hA hB, _ => by
      simp only [TyP.piDomSrc, TyP.wt]; omega
  | _, _, _, _, _, _, _, .lam .., he => by cases he
  | _, _, _, _, _, _, _, .app .., he => by cases he
  | _, _, _, _, _, _, _, .letE .., he => by cases he
  | _, _, _, _, _, _, _, .lit .., he => by cases he
  | _, _, _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, he =>
      Nat.lt_of_lt_of_le (TyP.piDomSrc_wt_lt Aw h he)
        (by simp only [TyP.wt]; omega)
  | _, _, _, _, _, _, _, .wk _ _ _ _ _ _ _ inner, he => by
      dsimp only [TyP.piDomSrc]
      cases lift_eq_pi he with
      | mk _ _ he₀ _ _ =>
          have ih := TyP.piDomSrc_wt_lt Aw inner he₀
          simp only [TyP.wt]; omega
  | _, _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ inner _ hv _, he => by
      dsimp only [TyP.piDomSrc]
      cases instantiate_eq_pi he with
      | under _ _ he₀ _ _ =>
          have ih := TyP.piDomSrc_wt_lt Aw inner he₀
          simp only [TyP.wt]; omega
      | here _ hr =>
          have ih := TyP.piDomSrc_wt_lt Aw hv hr
          simp only [TyP.wt]; omega
  | _, _, _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ inner _ hv _, he => by
      dsimp only [TyP.piDomSrc]
      cases instantiate_eq_pi he with
      | under _ _ he₀ _ _ =>
          have ih := TyP.piDomSrc_wt_lt Aw inner he₀
          simp only [TyP.wt]; omega
      | here _ hr =>
          have ih := TyP.piDomSrc_wt_lt Aw hv hr
          simp only [TyP.wt]; omega
  | _, _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ inner, he => by
      dsimp only [TyP.piDomSrc]
      cases instantiateLevels_eq_pi he with
      | mk _ _ he₀ _ _ =>
          have ih := TyP.piDomSrc_wt_lt Aw inner he₀
          simp only [TyP.wt]; omega
  | _, _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ inner, he => by
      have ih := TyP.piDomSrc_wt_lt Aw inner he
      simp only [TyP.piDomSrc, TyP.wt]; omega
  | _, _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ inner _, he => by
      have ih := TyP.piDomSrc_wt_lt Aw inner he
      simp only [TyP.piDomSrc, TyP.wt]; omega

/-- The domain view's displayed type is always a `.sort` — transports
    preserve the sort head (`lift`/`instantiate` fix `.sort`;
    `instantiateLevels` maps it to another `.sort`) — so both
    `BIT[pN, pD]` operands are `domain : sort` typings. -/
theorem TyP.piDomSrc_isSort : {E : ResolvedEnv} → {n : Nat} →
    {Γ : LCtx} → {e T A B : Expr Nat} →
    (D : TyP E n Γ e T) → (he : e = .pi A B) →
    ∃ u, (TyP.piDomSrc D he).2.1 = .sort u
  | _, _, _, _, _, _, _, .sort .., he => by cases he
  | _, _, _, _, _, _, _, .bvar .., he => by cases he
  | _, _, _, _, _, _, _, .const .., he => by cases he
  | _, _, _, _, _, _, _, .pi _ _ _ _ _ _ _ hA _, _ => ⟨_, rfl⟩
  | _, _, _, _, _, _, _, .lam .., he => by cases he
  | _, _, _, _, _, _, _, .app .., he => by cases he
  | _, _, _, _, _, _, _, .letE .., he => by cases he
  | _, _, _, _, _, _, _, .lit .., he => by cases he
  | _, _, _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, he =>
      TyP.piDomSrc_isSort h he
  | _, _, _, _, _, _, _, .wk _ _ _ _ _ _ _ inner, he => by
      dsimp only [TyP.piDomSrc]
      cases lift_eq_pi he with
      | mk _ _ he₀ _ _ =>
          have ⟨u, hu⟩ := TyP.piDomSrc_isSort inner he₀
          refine ⟨u, ?_⟩; simp only [TyP.piDomSrc]; rw [hu]; rfl
  | _, _, _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ inner _ hv _, he => by
      dsimp only [TyP.piDomSrc]
      cases instantiate_eq_pi he with
      | under _ _ he₀ _ _ =>
          have ⟨u, hu⟩ := TyP.piDomSrc_isSort inner he₀
          refine ⟨u, ?_⟩; simp only [TyP.piDomSrc]; rw [hu]; rfl
      | here _ hr => exact TyP.piDomSrc_isSort hv hr
  | _, _, _, _, _, _, _, .lsub _ _ _ _ _ _ _ _ _ inner _ hv _, he => by
      dsimp only [TyP.piDomSrc]
      cases instantiate_eq_pi he with
      | under _ _ he₀ _ _ =>
          have ⟨u, hu⟩ := TyP.piDomSrc_isSort inner he₀
          refine ⟨u, ?_⟩; simp only [TyP.piDomSrc]; rw [hu]; rfl
      | here _ hr => exact TyP.piDomSrc_isSort hv hr
  | _, _, _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ inner, he => by
      dsimp only [TyP.piDomSrc]
      cases instantiateLevels_eq_pi he with
      | mk _ _ he₀ _ _ =>
          have ⟨u, hu⟩ := TyP.piDomSrc_isSort inner he₀
          exact ⟨_, by simp only [TyP.piDomSrc]; rw [hu]; rfl⟩
  | _, _, _, _, _, _, _, .ewk _ _ _ _ _ _ _ inner, he => by
      simpa only [TyP.piDomSrc] using TyP.piDomSrc_isSort inner he
  | _, _, _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ inner _, he => by
      simpa only [TyP.piDomSrc] using TyP.piDomSrc_isSort inner he

/-- A real derivation stored by a request — a boxed typing or
    conversion; the request's atom/weight footprint source. -/
inductive IotaDerivation : Type where
  | ty (D : TyPAny)
  | cv (c : CvPAny)

/-- The stored derivation's weight. -/
def IotaDerivation.wt (Aw : Nat → Nat) : IotaDerivation → Nat
  | .ty D => D.wt Aw
  | .cv c => c.wt Aw

/-- The stored derivation's atom multiset. -/
def IotaDerivation.atoms (Aw : Nat → Nat) : IotaDerivation → List Nat
  | .ty D => D.atoms Aw
  | .cv c => c.atoms Aw

/-- §4.4's allowed semantic-request shapes, raw (no `QueryC` packing).
    Every constructor stores only the real fields the request is about;
    none stores a `Goal`/`ES`-style success answer. Operands are boxed
    (`TyPAny`/`CvPAny`): a request about a transported occurrence
    carries the derivations at the context where they actually live. -/
inductive RawQuery : Type where
  /-- the argument's real proof status: `PB[qa, pN]` -/
  | pb (qa pN : TyPAny)
  /-- `BIT[d₁, d₂]` — covers `BIT[pN, pD]`, the conv pair
      `BIT[pN, c.dl]`/`BIT[c.dr, pD]`, and the same-declaration two-views
      BIT of the level row -/
  | bit (d₁ d₂ : TyPAny)
  /-- `ES[c]` — an original conversion read on the path -/
  | es (c : CvPAny)
  /-- the real same-subject `CL` / endpoint comparison -/
  | cl (d₁ d₂ : TyPAny)
  /-- the needed smaller `EUT` -/
  | eut (d₁ d₂ : TyPAny)
  /-- `TagCoh` — proof-status agreement of two views of one displayed
      subject across transports -/
  | tagCoh (d₁ d₂ : TyPAny)

/-- The real derivations a request stores. -/
def RawQuery.derivations : RawQuery → List IotaDerivation
  | .pb a b => [.ty a, .ty b]
  | .bit a b => [.ty a, .ty b]
  | .es c => [.cv c]
  | .cl a b => [.ty a, .ty b]
  | .eut a b => [.ty a, .ty b]
  | .tagCoh a b => [.ty a, .ty b]

/-- The request's stored-derivation weight. -/
def RawQuery.wt (Aw : Nat → Nat) (q : RawQuery) : Nat :=
  (q.derivations.map (·.wt Aw)).sum

/-- The request's stored-derivation atom multiset. -/
def RawQuery.atoms (Aw : Nat → Nat) (q : RawQuery) : List Nat :=
  (q.derivations.map (·.atoms Aw)).flatten

/-- The request is a `PB` — the always-emitted proof-status request. -/
def RawQuery.isPb : RawQuery → Bool
  | .pb _ _ => true
  | _ => false

/-! ## the original ι site -/

/-- The original ι site: the witness, its `DerivedIota` (typed at the
    witness's own endpoints — a node derived from a different witness's
    redex cannot sit here), and the four stored premise typings — the
    original `hlhs` forest the plan reads from. -/
structure IotaSite (E : ResolvedEnv) (n : Nat) (Γ : LCtx) where
  T : Expr Nat
  w : IotaWitness E
  d : DerivedIota E (iotaLhsOf w) (iotaRhsOf w)
  hlhs : TyP E n Γ (iotaLhsOf w) T
  hrhs : TyP E n Γ (iotaRhsOf w) T
  dl : TyP E n Γ (iotaLhsOf w) T
  dr : TyP E n Γ (iotaRhsOf w) T

/-- The site's conversion node — the real `CvP.iota` its fields form. -/
def IotaSite.node (s : IotaSite E n Γ) :
    CvP E n Γ (iotaLhsOf s.w) (iotaRhsOf s.w) s.T :=
  .iota _ _ _ _ _ _ s.d s.hlhs s.hrhs s.dl s.dr

/-- The caller budget: the node's own weight
    `1 + hlhs.wt + hrhs.wt + dl.wt + dr.wt`. -/
def IotaSite.N (Aw : Nat → Nat) (s : IotaSite E n Γ) : Nat :=
  s.node.wt Aw

/-- The admission origin — the recursor member lookup that admitted the
    head; the constructor/family lookups ride with the same `w`. -/
def IotaSite.origin (s : IotaSite E n Γ) :
    E.members s.w.recRef = some s.w.recMember := s.w.hrec

/-! ## §4.4's slot extraction -/

/-- The transport/conv wrapper kinds a path edge can cross. -/
inductive TransportKind where
  | wk | esub | lsub | linst | ewk | cctx | conv
  deriving DecidableEq, Repr

/-- One wrapper edge crossed on the way from a forest root to an
    occurrence — the original occurrence/transport receipt: the wrapper
    node itself (`view`, the transported typing), its immediate source
    child (`source`), and — where the edge carries a real conversion
    (`.conv`, `.cctx`) — that conversion (`cvp`). -/
structure PathEdge where
  kind : TransportKind
  view : TyPAny
  source : TyPAny
  cvp : Option CvPAny

/-- A real argument occurrence inside a typing forest: the `.app` node's
    own fields at its own context — `hf : TyP _ _ _ f (.pi A B)` is the
    admission receipt (`pD`, its regularity's stored domain sort-typing,
    is derived by `TyP.piDomSrc`), `ha` is the argument typing `qa`, `hT`
    the result sort-typing — plus the wrapper `path` from the forest
    root, outermost edge first, and `argConv`, the domain conversion when
    the argument typing is itself `.conv`-headed. Repeated occurrences
    of one derivation are distinguished by `path`. -/
structure SpineOcc where
  path : List PathEdge
  E : ResolvedEnv
  n : Nat
  Γ : LCtx
  f : Expr Nat
  a : Expr Nat
  A : Expr Nat
  B : Expr Nat
  w : Level
  hf : TyP E n Γ f (.pi A B)
  ha : TyP E n Γ a A
  hT : TyP E n Γ (instantiate0 a B) (.sort w)
  argConv : Option CvPAny

/-- The argument typing, boxed — the slot's original `qa`. -/
def SpineOcc.qa (o : SpineOcc) : TyPAny := ⟨_, _, _, _, _, o.ha⟩

/-- `pN = qa.reg.2` — the slot's natural-type view, derived. -/
def SpineOcc.pN (o : SpineOcc) : TyPAny :=
  ⟨_, _, _, o.A, .sort o.ha.reg.1, o.ha.reg.2⟩

/-- `pD` — the original admission-domain sort-typing, re-displayed
    through the original transport frames: the innermost `.pi` node's
    own domain field `hA` inside `hf`'s regularity
    (`hf.reg.2 : TyP _ _ _ (.pi A B) (.sort _)` — the declaration-side
    `pi` typing), re-wrapped in the same `wk`/`esub`/`lsub`/`linst`/
    `ewk`/`cctx` constructors carrying those nodes' own stored fields.
    The view types the domain as displayed at `o.Γ` — `pD`'s context
    is `pN`'s and its subject is the admitted domain — so `BIT[pN, pD]`
    is a same-subject, same-context `domain : sort` request (S16
    §5/§6 SubjectLink). Nothing is re-derived; every crossed frame is
    re-instantiated from original evidence. -/
def SpineOcc.pD (o : SpineOcc) : TyPAny :=
  let r := TyP.piDomSrc o.hf.reg.2 rfl
  ⟨o.E, o.n, o.Γ, r.1, r.2.1, r.2.2⟩

/-- `pD` is strictly below `hf`'s own weight: the extracted domain view
    re-applied through the original frames is lighter than `hf`'s
    regularity (each re-wrap is a strict-subderivation head + the
    node's own fields), hence `< hf.wt` by `TyP.wt_reg_le`. -/
theorem SpineOcc.pD_wt_lt (Aw : Nat → Nat) (o : SpineOcc) :
    o.pD.wt Aw < o.hf.wt Aw :=
  Nat.lt_of_lt_of_le (TyP.piDomSrc_wt_lt Aw o.hf.reg.2 rfl)
    (TyP.wt_reg_le Aw o.hf)

/-- `pD`'s displayed type is a `.sort` — the BIT operand is
    `domain : sort`, never `f : .pi A B`. -/
theorem SpineOcc.pD_is_sort (o : SpineOcc) : ∃ u, o.pD.T = .sort u :=
  TyP.piDomSrc_isSort o.hf.reg.2 rfl

/-- The app node's result sort-typing, boxed. -/
def SpineOcc.resultTy (o : SpineOcc) : TyPAny := ⟨_, _, _, _, _, o.hT⟩

/-- The occurrence's real atom footprint (its `qa`'s atoms). -/
def SpineOcc.footprint (Aw : Nat → Nat) (o : SpineOcc) : List Nat :=
  o.ha.atoms Aw

/-- The real argument occurrences of a typing derivation, outermost
    application first. `.app` contributes its argument occurrence (the
    full app-node receipt) and recurses into the function part. `.conv`
    rides through its typed child and records the crossed conversion.
    The transport wrappers `wk`/`esub`/`lsub`/`linst`/`ewk`/`cctx` are
    traversed too — each records a `PathEdge` receipt (the wrapper node,
    its source child, an optional conversion) so a transported spine
    loses no demand: the collected `qa` lives at its own context, boxed
    (`S16` §1's pending-view discipline). Rule constructors
    (`sort`/`bvar`/`const`/`pi`/`lam`/`letE`/`lit`) end the walk — they
    carry no spine arguments of this application. When an `esub`/`lsub`'s
    own child is the hit bvar (`e = .bvar j` — the displayed subject is
    `instantiate j _ (.bvar j) = lift 0 j v`, born from the replacement,
    never from the substituted-away child), the walk continues into the
    original replacement `hv` at the same packet route; re-following the
    hit child would end at its `.bvar` leaf and the displayed spine would
    disappear (A6 §11's missed-ι control). Every returned
    derivation is a strict subderivation of the forest root
    (`spineViews_wt_le`). -/
def TyP.spineViews (path : List PathEdge) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → List SpineOcc
  | _, _, _, _, _, .sort .. => []
  | _, _, _, _, _, .bvar .. => []
  | _, _, _, _, _, .const .. => []
  | _, _, _, _, _, .pi .. => []
  | _, _, _, _, _, .lam .. => []
  | _, _, _, _, _, .app E n Γ f a A B w hf ha hT =>
      ⟨path.reverse, E, n, Γ, f, a, A, B, w, hf, ha, hT,
        (match ha with
         | .conv _ _ _ _ _ _ _ _ c => some (.mk c)
         | _ => none)⟩ ::
        hf.spineViews path
  | _, _, _, _, _, .letE .. => []
  | _, _, _, _, _, .lit .. => []
  | _, _, _, _, _, .conv E n Γ e A B u h hc =>
      h.spineViews (⟨.conv, ⟨_, _, _, _, _, .conv E n Γ e A B u h hc⟩,
        ⟨_, _, _, _, _, h⟩, some (.mk hc)⟩ :: path)
  | _, _, _, _, _, .wk E n Γ e A d c D =>
      D.spineViews (⟨.wk, ⟨_, _, _, _, _, .wk E n Γ e A d c D⟩,
        ⟨_, _, _, _, _, D⟩, none⟩ :: path)
  | _, _, _, _, _, .esub E n Γ e A t v j u D hget hv hvT =>
      if e = .bvar j then
        hv.spineViews (⟨.esub,
          ⟨_, _, _, _, _, .esub E n Γ e A t v j u D hget hv hvT⟩,
          ⟨_, _, _, _, _, hv⟩, none⟩ :: path)
      else
        D.spineViews (⟨.esub,
          ⟨_, _, _, _, _, .esub E n Γ e A t v j u D hget hv hvT⟩,
          ⟨_, _, _, _, _, D⟩, none⟩ :: path)
  | _, _, _, _, _, .lsub E n Γ e A t v j u D hget hv hvT =>
      if e = .bvar j then
        hv.spineViews (⟨.lsub,
          ⟨_, _, _, _, _, .lsub E n Γ e A t v j u D hget hv hvT⟩,
          ⟨_, _, _, _, _, hv⟩, none⟩ :: path)
      else
        D.spineViews (⟨.lsub,
          ⟨_, _, _, _, _, .lsub E n Γ e A t v j u D hget hv hvT⟩,
          ⟨_, _, _, _, _, D⟩, none⟩ :: path)
  | _, _, _, _, _, .linst E a' n Γ e A ls hls hlen D =>
      D.spineViews (⟨.linst,
        ⟨_, _, _, _, _, .linst E a' n Γ e A ls hls hlen D⟩,
        ⟨_, _, _, _, _, D⟩, none⟩ :: path)
  | _, _, _, _, _, .ewk E₀ E n Γ e A hext D =>
      D.spineViews (⟨.ewk, ⟨_, _, _, _, _, .ewk E₀ E n Γ e A hext D⟩,
        ⟨_, _, _, _, _, D⟩, none⟩ :: path)
  | _, _, _, _, _, .cctx E n Γ e T A A' u D hA =>
      D.spineViews (⟨.cctx, ⟨_, _, _, _, _, .cctx E n Γ e T A A' u D hA⟩,
        ⟨_, _, _, _, _, D⟩, some (.mk hA)⟩ :: path)

/-- Spine occurrences in original application order (first-applied
    first). -/
def TyP.spineViewsInOrder (D : TyP E n Γ e T) : List SpineOcc :=
  (D.spineViews []).reverse

/-- Frozen copy of `spineViews` before the A6 §11 fix: the `esub`/`lsub`
    arms follow the substituted-away child unconditionally, so a hit-bvar
    crossing collapses the displayed spine to `[]` — kept verbatim as the
    control's counterfactual (`s16hL_esub_frozen_nil`). -/
def TyP.spineViewsFrozen (path : List PathEdge) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → List SpineOcc
  | _, _, _, _, _, .sort .. => []
  | _, _, _, _, _, .bvar .. => []
  | _, _, _, _, _, .const .. => []
  | _, _, _, _, _, .pi .. => []
  | _, _, _, _, _, .lam .. => []
  | _, _, _, _, _, .app E n Γ f a A B w hf ha hT =>
      ⟨path.reverse, E, n, Γ, f, a, A, B, w, hf, ha, hT,
        (match ha with
         | .conv _ _ _ _ _ _ _ _ c => some (.mk c)
         | _ => none)⟩ ::
        hf.spineViewsFrozen path
  | _, _, _, _, _, .letE .. => []
  | _, _, _, _, _, .lit .. => []
  | _, _, _, _, _, .conv E n Γ e A B u h hc =>
      h.spineViewsFrozen (⟨.conv, ⟨_, _, _, _, _, .conv E n Γ e A B u h hc⟩,
        ⟨_, _, _, _, _, h⟩, some (.mk hc)⟩ :: path)
  | _, _, _, _, _, .wk E n Γ e A d c D =>
      D.spineViewsFrozen (⟨.wk, ⟨_, _, _, _, _, .wk E n Γ e A d c D⟩,
        ⟨_, _, _, _, _, D⟩, none⟩ :: path)
  | _, _, _, _, _, .esub E n Γ e A t v j u D hget hv hvT =>
      D.spineViewsFrozen (⟨.esub,
        ⟨_, _, _, _, _, .esub E n Γ e A t v j u D hget hv hvT⟩,
        ⟨_, _, _, _, _, D⟩, none⟩ :: path)
  | _, _, _, _, _, .lsub E n Γ e A t v j u D hget hv hvT =>
      D.spineViewsFrozen (⟨.lsub,
        ⟨_, _, _, _, _, .lsub E n Γ e A t v j u D hget hv hvT⟩,
        ⟨_, _, _, _, _, D⟩, none⟩ :: path)
  | _, _, _, _, _, .linst E a' n Γ e A ls hls hlen D =>
      D.spineViewsFrozen (⟨.linst,
        ⟨_, _, _, _, _, .linst E a' n Γ e A ls hls hlen D⟩,
        ⟨_, _, _, _, _, D⟩, none⟩ :: path)
  | _, _, _, _, _, .ewk E₀ E n Γ e A hext D =>
      D.spineViewsFrozen (⟨.ewk, ⟨_, _, _, _, _, .ewk E₀ E n Γ e A hext D⟩,
        ⟨_, _, _, _, _, D⟩, none⟩ :: path)
  | _, _, _, _, _, .cctx E n Γ e T A A' u D hA =>
      D.spineViewsFrozen (⟨.cctx, ⟨_, _, _, _, _, .cctx E n Γ e T A A' u D hA⟩,
        ⟨_, _, _, _, _, D⟩, some (.mk hA)⟩ :: path)

/-- Every stored derivation of a collected occurrence is bounded by any
    bound of the forest root: the app-node fields are strict
    subderivations, path-edge views are subderivations-or-equal of the
    root (the first edge crossed may be the root node itself), edge
    sources and crossed conversions are strictly lighter, and an
    `argConv` conversion is strictly lighter than its `ha`. The
    accumulated `path` is universally bounded — the caller's own
    receipts carry over unchanged. -/
theorem TyP.spineViews_wt_le (Aw : Nat → Nat) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → (path : List PathEdge) → (W : Nat) →
    D.wt Aw ≤ W →
    (∀ e ∈ path, e.view.wt Aw ≤ W ∧ e.source.wt Aw < W ∧
      (∀ c, e.cvp = some c → c.wt Aw < W)) →
    ∀ o ∈ D.spineViews path,
      o.hf.wt Aw < W ∧ o.ha.wt Aw < W ∧ o.hT.wt Aw < W ∧
      (∀ c, o.argConv = some c → c.wt Aw < W) ∧
      (∀ e ∈ o.path, e.view.wt Aw ≤ W ∧ e.source.wt Aw < W ∧
        (∀ c, e.cvp = some c → c.wt Aw < W))
  | _, _, _, _, _, .app _ _ _ _ _ _ _ w hf ha hT => by
      intro path W hDW hpath o ho
      simp only [TyP.spineViews, List.mem_cons] at ho
      rcases ho with rfl | hmem
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show hf.wt Aw < W
          simp only [TyP.wt] at hDW; omega
        · show ha.wt Aw < W
          simp only [TyP.wt] at hDW; omega
        · show hT.wt Aw < W
          simp only [TyP.wt] at hDW; omega
        · intro c hc
          split at hc
          · simp only [Option.some.injEq] at hc; subst hc
            simp only [CvPAny.wt]
            simp only [TyP.wt] at hDW
            omega
          · simp at hc
        · intro e he
          exact hpath e (List.mem_reverse.mp he)
      · have hlt : hf.wt Aw < W := by
          simp only [TyP.wt] at hDW; omega
        exact TyP.spineViews_wt_le Aw hf path W
          (Nat.le_of_lt hlt) hpath o hmem
  | _, _, _, _, _, .conv E n Γ e A B u h hc => by
      intro path W hDW hpath o ho
      simp only [TyP.spineViews] at ho
      apply TyP.spineViews_wt_le Aw h
        (⟨.conv, ⟨_, _, _, _, _, .conv E n Γ e A B u h hc⟩,
          ⟨_, _, _, _, _, h⟩, some (.mk hc)⟩ :: path) W
      · simp only [TyP.wt] at hDW; omega
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · refine ⟨hDW, ?_, ?_⟩
          · show h.wt Aw < W
            simp only [TyP.wt] at hDW; omega
          · intro c hc2
            simp only [Option.some.injEq] at hc2; subst hc2
            show hc.wt Aw < W
            simp only [TyP.wt] at hDW; omega
        · exact hpath e he
      · exact ho
  | _, _, _, _, _, .wk E n Γ e A d c D' => by
      intro path W hDW hpath o ho
      simp only [TyP.spineViews] at ho
      apply TyP.spineViews_wt_le Aw D'
        (⟨.wk, ⟨_, _, _, _, _, .wk E n Γ e A d c D'⟩,
          ⟨_, _, _, _, _, D'⟩, none⟩ :: path) W
      · simp only [TyP.wt] at hDW; omega
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · refine ⟨hDW, ?_, ?_⟩
          · show D'.wt Aw < W
            simp only [TyP.wt] at hDW; omega
          · intro c hc; simp at hc
        · exact hpath e he
      · exact ho
  | _, _, _, _, _, .esub E n Γ e A t v j u D' hget hv hvT => by
      intro path W hDW hpath o ho
      simp only [TyP.spineViews] at ho
      split at ho
      · apply TyP.spineViews_wt_le Aw hv
          (⟨.esub, ⟨_, _, _, _, _, .esub E n Γ e A t v j u D' hget hv hvT⟩,
            ⟨_, _, _, _, _, hv⟩, none⟩ :: path) W
        · simp only [TyP.wt] at hDW; omega
        · intro ed hed
          simp only [List.mem_cons] at hed
          rcases hed with rfl | hed
          · refine ⟨hDW, ?_, ?_⟩
            · show hv.wt Aw < W
              simp only [TyP.wt] at hDW; omega
            · intro c hc; simp at hc
          · exact hpath ed hed
        · exact ho
      · apply TyP.spineViews_wt_le Aw D'
          (⟨.esub, ⟨_, _, _, _, _, .esub E n Γ e A t v j u D' hget hv hvT⟩,
            ⟨_, _, _, _, _, D'⟩, none⟩ :: path) W
        · simp only [TyP.wt] at hDW; omega
        · intro ed hed
          simp only [List.mem_cons] at hed
          rcases hed with rfl | hed
          · refine ⟨hDW, ?_, ?_⟩
            · show D'.wt Aw < W
              simp only [TyP.wt] at hDW; omega
            · intro c hc; simp at hc
          · exact hpath ed hed
        · exact ho
  | _, _, _, _, _, .lsub E n Γ e A t v j u D' hget hv hvT => by
      intro path W hDW hpath o ho
      simp only [TyP.spineViews] at ho
      split at ho
      · apply TyP.spineViews_wt_le Aw hv
          (⟨.lsub, ⟨_, _, _, _, _, .lsub E n Γ e A t v j u D' hget hv hvT⟩,
            ⟨_, _, _, _, _, hv⟩, none⟩ :: path) W
        · simp only [TyP.wt] at hDW; omega
        · intro ed hed
          simp only [List.mem_cons] at hed
          rcases hed with rfl | hed
          · refine ⟨hDW, ?_, ?_⟩
            · show hv.wt Aw < W
              simp only [TyP.wt] at hDW; omega
            · intro c hc; simp at hc
          · exact hpath ed hed
        · exact ho
      · apply TyP.spineViews_wt_le Aw D'
          (⟨.lsub, ⟨_, _, _, _, _, .lsub E n Γ e A t v j u D' hget hv hvT⟩,
            ⟨_, _, _, _, _, D'⟩, none⟩ :: path) W
        · simp only [TyP.wt] at hDW; omega
        · intro ed hed
          simp only [List.mem_cons] at hed
          rcases hed with rfl | hed
          · refine ⟨hDW, ?_, ?_⟩
            · show D'.wt Aw < W
              simp only [TyP.wt] at hDW; omega
            · intro c hc; simp at hc
          · exact hpath ed hed
        · exact ho
  | _, _, _, _, _, .linst E a' n Γ e A ls hls hlen D' => by
      intro path W hDW hpath o ho
      simp only [TyP.spineViews] at ho
      apply TyP.spineViews_wt_le Aw D'
        (⟨.linst, ⟨_, _, _, _, _, .linst E a' n Γ e A ls hls hlen D'⟩,
          ⟨_, _, _, _, _, D'⟩, none⟩ :: path) W
      · simp only [TyP.wt] at hDW; omega
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · refine ⟨hDW, ?_, ?_⟩
          · show D'.wt Aw < W
            simp only [TyP.wt] at hDW; omega
          · intro c hc; simp at hc
        · exact hpath e he
      · exact ho
  | _, _, _, _, _, .ewk E₀ E n Γ e A hext D' => by
      intro path W hDW hpath o ho
      simp only [TyP.spineViews] at ho
      apply TyP.spineViews_wt_le Aw D'
        (⟨.ewk, ⟨_, _, _, _, _, .ewk E₀ E n Γ e A hext D'⟩,
          ⟨_, _, _, _, _, D'⟩, none⟩ :: path) W
      · simp only [TyP.wt] at hDW; omega
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · refine ⟨hDW, ?_, ?_⟩
          · show D'.wt Aw < W
            simp only [TyP.wt] at hDW; omega
          · intro c hc; simp at hc
        · exact hpath e he
      · exact ho
  | _, _, _, _, _, .cctx E n Γ e T A A' u D' hA => by
      intro path W hDW hpath o ho
      simp only [TyP.spineViews] at ho
      apply TyP.spineViews_wt_le Aw D'
        (⟨.cctx, ⟨_, _, _, _, _, .cctx E n Γ e T A A' u D' hA⟩,
          ⟨_, _, _, _, _, D'⟩, some (.mk hA)⟩ :: path) W
      · simp only [TyP.wt] at hDW; omega
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · refine ⟨hDW, ?_, ?_⟩
          · show D'.wt Aw < W
            simp only [TyP.wt] at hDW; omega
          · intro c hc2
            simp only [Option.some.injEq] at hc2; subst hc2
            show hA.wt Aw < W
            simp only [TyP.wt] at hDW; omega
        · exact hpath e he
      · exact ho
  | _, _, _, _, _, .sort .. => by
      intro _ _ _ _ o ho
      simp only [TyP.spineViews] at ho
      exact absurd ho (List.not_mem_nil _)
  | _, _, _, _, _, .bvar .. => by
      intro _ _ _ _ o ho
      simp only [TyP.spineViews] at ho
      exact absurd ho (List.not_mem_nil _)
  | _, _, _, _, _, .const .. => by
      intro _ _ _ _ o ho
      simp only [TyP.spineViews] at ho
      exact absurd ho (List.not_mem_nil _)
  | _, _, _, _, _, .pi .. => by
      intro _ _ _ _ o ho
      simp only [TyP.spineViews] at ho
      exact absurd ho (List.not_mem_nil _)
  | _, _, _, _, _, .lam .. => by
      intro _ _ _ _ o ho
      simp only [TyP.spineViews] at ho
      exact absurd ho (List.not_mem_nil _)
  | _, _, _, _, _, .letE .. => by
      intro _ _ _ _ o ho
      simp only [TyP.spineViews] at ho
      exact absurd ho (List.not_mem_nil _)
  | _, _, _, _, _, .lit .. => by
      intro _ _ _ _ o ho
      simp only [TyP.spineViews] at ho
      exact absurd ho (List.not_mem_nil _)

/-- Where a slot's occurrence sits in the original forest — the original
    occurrence tag: a recursor-application argument (`.spine`, original
    argument order), a constructor field inside the major
    (`.majorField`), or a directRec-result argument of the rhs
    (`.rhsDirectRec`, index in application order). -/
inductive IotaSlotOrigin where
  | spine (j : Nat)
  | majorField (j : Nat)
  | rhsDirectRec (j : Nat)
  deriving DecidableEq, Repr

/-- One real argument slot: its forest position and the original
    occurrence — the `.app`-node receipt (`qa`/`pD`/path) the §4.4 row
    demands. `pN` is derived (`qa.reg.2`), never stored. -/
structure IotaSlotPlan where
  origin : IotaSlotOrigin
  occ : SpineOcc

/-- The slot's original `qa`, boxed. -/
def IotaSlotPlan.qa (s : IotaSlotPlan) : TyPAny := s.occ.qa

/-- `pN = qa.reg.2` — the slot's natural-type view, derived. -/
def IotaSlotPlan.pN (s : IotaSlotPlan) : TyPAny := s.occ.pN

/-- The original admission-domain view — the app node's function part. -/
def IotaSlotPlan.pD (s : IotaSlotPlan) : TyPAny := s.occ.pD

/-- The original occurrence/transport path, outermost edge first. -/
def IotaSlotPlan.path (s : IotaSlotPlan) : List PathEdge := s.occ.path

/-- The slot's real atom footprint (its own `qa`'s atoms). -/
def IotaSlotPlan.footprint (Aw : Nat → Nat) (s : IotaSlotPlan) :
    List Nat := s.occ.footprint Aw

/-- The §4.4 requests one crossed path edge emits, where they apply:
    a crossed conversion emits `ES[c]` plus the endpoint `CL`; a `.conv`
    edge additionally emits the smaller same-subject `EUT`/`CL`/`TagCoh`;
    `linst` emits the two-views `BIT`; subject-preserving transports
    (`ewk`/`cctx`) emit the same-subject `CL`; every transport emits the
    `TagCoh` pair between the transported view and its source. -/
def PathEdge.requests (e : PathEdge) : List RawQuery :=
  (match e.cvp with
   | some c => [.es c, .cl c.dl c.dr]
   | none => []) ++
  (match e.kind with
   | .conv => [.eut e.source e.view, .cl e.source e.view,
       .tagCoh e.view e.source]
   | .linst => [.bit e.source e.view]
   | .ewk | .cctx => [.cl e.source e.view, .tagCoh e.view e.source]
   | _ => [.tagCoh e.view e.source])

/-- The §4.4 request set of one slot: `PB[qa, pN]` and `BIT[pN, pD]`
    always; the conv-K1 pair `BIT[pN, c.dl]`/`BIT[c.dr, pD]` and `ES[c]`
    when the argument typing is `.conv`-headed; then each crossed path
    edge's own requests in occurrence order. -/
def IotaSlotPlan.requests (s : IotaSlotPlan) : List RawQuery :=
  let o := s.occ
  [.pb o.qa o.pN, .bit o.pN o.pD] ++
    (match o.argConv with
     | some c => [.bit o.pN c.dl, .bit c.dr o.pD, .es c]
     | none => []) ++
    (o.path.flatMap PathEdge.requests)

/-- Tag each occurrence of a list with its position, from `i`. -/
def tagSlots (tag : Nat → IotaSlotOrigin) :
    List SpineOcc → Nat → List IotaSlotPlan
  | [], _ => []
  | o :: os, i => ⟨tag i, o⟩ :: tagSlots tag os (i + 1)

/-- Membership in a tagged slot list is membership of the source list. -/
theorem occ_mem_of_mem_tagSlots (tag : Nat → IotaSlotOrigin)
    (l : List SpineOcc) (i : Nat) {s : IotaSlotPlan}
    (h : s ∈ tagSlots tag l i) : s.occ ∈ l := by
  induction l generalizing i with
  | nil => simp [tagSlots] at h
  | cons a l ih =>
      simp only [tagSlots, List.mem_cons] at h
      rcases h with h | h
      · subst h; exact .head _
      · exact .tail _ (ih _ h)

/-- Application-order indices of the directRec-result arguments in a
    `rhsArgs` spine: `.plain` contributes one argument, `.directRec`
    contributes the field then the recursive call — the result sits at
    offset 1 of its block. -/
def recResultIdxs : List RecKind → Nat → List Nat
  | [], _ => []
  | .plain :: ks, i => recResultIdxs ks (i + 1)
  | .directRec :: ks, i => (i + 1) :: recResultIdxs ks (i + 2)

/-- The request plan — site plus its finite slot list. No
    success-answer fields: the plan is traversable structural data only. -/
structure IotaRequestPlan (E : ResolvedEnv) (n : Nat) (Γ : LCtx) where
  site : IotaSite E n Γ
  slots : List IotaSlotPlan

/-- §4.6 row 1 — `planIota`: the finite request plan built from the
    original `w`, the original `hlhs`/`hrhs` forest and the actual
    admission origin (inside `site`). Slots: every real argument
    occurrence of the recursor application; every constructor-field
    occurrence inside the major argument; every directRec-result
    occurrence of the rhs. -/
def planIota (site : IotaSite E n Γ) : IotaRequestPlan E n Γ where
  site := site
  slots :=
    tagSlots .spine site.hlhs.spineViewsInOrder 0 ++
      (match (site.hlhs.spineViews []).head? with
       | some occM =>
           tagSlots .majorField
             ((occM.ha.spineViewsInOrder.drop site.w.nparams).map
               fun o => { o with path := occM.path ++ o.path }) 0
       | none => []) ++
      (recResultIdxs site.w.kinds 0).filterMap fun r =>
        (site.hrhs.spineViewsInOrder[r]?).map
          fun occ => ⟨.rhsDirectRec r, occ⟩

/-- §4.6 row 2 — the requests of slot j: the slot's §4.4 request set
    (`PB`/`BIT`/`ES`/`CL`/`EUT`/`TagCoh` where they apply). Out of range
    gives `none`. -/
def request_of_iota_slot (plan : IotaRequestPlan E n Γ) (j : Nat) :
    Option (List RawQuery) :=
  (plan.slots[j]?).map IotaSlotPlan.requests

/-- The site's forest roots bound the node strictly. -/
theorem IotaSite.hlhs_lt_N (Aw : Nat → Nat) (s : IotaSite E n Γ) :
    s.hlhs.wt Aw < s.N Aw := by
  have h : s.N Aw =
      1 + s.hlhs.wt Aw + s.hrhs.wt Aw + s.dl.wt Aw + s.dr.wt Aw := rfl
  rw [h]; omega

theorem IotaSite.hrhs_lt_N (Aw : Nat → Nat) (s : IotaSite E n Γ) :
    s.hrhs.wt Aw < s.N Aw := by
  have h : s.N Aw =
      1 + s.hlhs.wt Aw + s.hrhs.wt Aw + s.dl.wt Aw + s.dr.wt Aw := rfl
  rw [h]; omega

/-- The plan's slots are billed below the site node — the §4.4 "live
    atoms of the callee < N" half, on the real fields: every occurrence
    stores a strict forest bound `W < N` bounding its app-node fields
    strictly, its path views by `≤`, and its edge sources/conversions
    strictly. -/
theorem planIota_slots_below (Aw : Nat → Nat) (site : IotaSite E n Γ)
    {s : IotaSlotPlan} (hs : s ∈ (planIota site).slots) :
    ∃ W, W < site.N Aw ∧
      s.occ.hf.wt Aw < W ∧ s.occ.ha.wt Aw < W ∧ s.occ.hT.wt Aw < W ∧
      (∀ c, s.occ.argConv = some c → c.wt Aw < W) ∧
      (∀ e ∈ s.occ.path, e.view.wt Aw ≤ W ∧ e.source.wt Aw < W ∧
        (∀ c, e.cvp = some c → c.wt Aw < W)) := by
  unfold planIota at hs
  rcases List.mem_append.mp hs with h | hrr
  · rcases List.mem_append.mp h with hspine | hmaj
    · refine ⟨site.hlhs.wt Aw, site.hlhs_lt_N Aw, ?_⟩
      have hq := occ_mem_of_mem_tagSlots _ _ _ hspine
      exact TyP.spineViews_wt_le Aw site.hlhs [] _
        (Nat.le_refl _)
        (by intro e he; simp at he) _
        (List.mem_reverse.mp hq)
    · cases hm : (site.hlhs.spineViews []).head? with
      | none => rw [hm] at hmaj; simp [tagSlots] at hmaj
      | some occM =>
          rw [hm] at hmaj
          have hmem2 := occ_mem_of_mem_tagSlots _ _ _ hmaj
          obtain ⟨o2, ho2, hseq⟩ := List.mem_map.mp hmem2
          have ho2in : o2 ∈ occM.ha.spineViews [] :=
            List.mem_reverse.mp (List.mem_of_mem_drop ho2)
          have hMmem : occM ∈ site.hlhs.spineViews [] := by
              cases l0 : site.hlhs.spineViews [] with
              | nil => rw [l0] at hm; simp at hm
              | cons a t =>
                  rw [l0] at hm
                  simp only [List.head?_cons, Option.some.injEq] at hm
                  subst hm; exact .head _
          obtain ⟨_hMhf, hMha, _hMhT, _hMarg, hMpath⟩ :=
            TyP.spineViews_wt_le Aw site.hlhs [] _ (Nat.le_refl _)
              (by intro e he; simp at he) occM hMmem
          obtain ⟨h2hf, h2ha, h2hT, h2arg, h2path⟩ :=
            TyP.spineViews_wt_le Aw occM.ha [] _ (Nat.le_refl _)
              (by intro e he; simp at he) o2 ho2in
          refine ⟨site.hlhs.wt Aw, site.hlhs_lt_N Aw, ?_, ?_, ?_, ?_, ?_⟩
          · rw [← hseq]; show o2.hf.wt Aw < site.hlhs.wt Aw
            exact Nat.lt_trans h2hf hMha
          · rw [← hseq]; show o2.ha.wt Aw < site.hlhs.wt Aw
            exact Nat.lt_trans h2ha hMha
          · rw [← hseq]; show o2.hT.wt Aw < site.hlhs.wt Aw
            exact Nat.lt_trans h2hT hMha
          · intro c hc; rw [← hseq] at hc
            exact Nat.lt_trans (h2arg c hc) hMha
          · intro e he; rw [← hseq] at he
            rcases List.mem_append.mp he with hout | hin
            · exact hMpath e hout
            · obtain ⟨hv, hs2, hcvp2⟩ := h2path e hin
              exact ⟨Nat.le_trans hv (Nat.le_of_lt hMha),
                     Nat.lt_trans hs2 hMha,
                     fun c hc => Nat.lt_trans (hcvp2 c hc) hMha⟩
  · rcases List.mem_filterMap.mp hrr with ⟨r, _hr, hreq⟩
    cases hget : site.hrhs.spineViewsInOrder[r]? with
    | none => rw [hget] at hreq; simp at hreq
    | some occ =>
        rw [hget] at hreq
        simp only [Option.map_some', Option.some.injEq] at hreq
        subst hreq
        refine ⟨site.hrhs.wt Aw, site.hrhs_lt_N Aw, ?_⟩
        have hmem : occ ∈ site.hrhs.spineViews [] :=
          List.mem_reverse.mp (List.getElem?_mem hget)
        exact TyP.spineViews_wt_le Aw site.hrhs [] _
          (Nat.le_refl _) (by intro e he; simp at he) _ hmem

/-- Every derivation stored by one path edge's requests is bounded by
    the edge's own bound `W`. -/
theorem PathEdge.requests_wt_le (Aw : Nat → Nat) (e : PathEdge) (W : Nat)
    (hview : e.view.wt Aw ≤ W) (hsrc : e.source.wt Aw < W)
    (hcvp : ∀ c, e.cvp = some c → c.wt Aw < W) :
    ∀ q ∈ e.requests, ∀ d ∈ q.derivations, d.wt Aw ≤ W := by
  intro q hq d hd
  unfold PathEdge.requests at hq
  rcases List.mem_append.mp hq with hc | hk
  · cases hcvp_eq : e.cvp with
    | none => rw [hcvp_eq] at hc; simp at hc
    | some c =>
        rw [hcvp_eq] at hc
        have hcW := hcvp c hcvp_eq
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · simp only [RawQuery.derivations, List.mem_cons,
            List.not_mem_nil, or_false] at hd
          rcases hd with rfl
          exact Nat.le_of_lt hcW
        · simp only [RawQuery.derivations, List.mem_cons,
            List.mem_singleton, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl
          · exact Nat.le_trans
              (Nat.le_of_lt (c.wt_dl_lt Aw)) (Nat.le_of_lt hcW)
          · exact Nat.le_trans
              (Nat.le_of_lt (c.wt_dr_lt Aw)) (Nat.le_of_lt hcW)
  · cases hkind : e.kind <;> rw [hkind] at hk <;>
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hk <;>
      (first
        | (rcases hk with rfl | rfl | rfl)
        | (rcases hk with rfl | rfl)
        | (rcases hk with rfl)) <;>
      simp only [RawQuery.derivations, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at hd <;>
      rcases hd with rfl | rfl <;>
      first | exact hview | exact Nat.le_of_lt hsrc

/-- §4.6 row 3 — the real edge from real fields / admission source:
    every derivation a slot's emitted requests store is strictly below
    the site's node weight. `PB[qa, pN]` stores `qa` (a subderivation,
    hence `< N`) and `pN = qa.reg.2` (`≤ qa.wt` by `TyP.wt_reg_le`);
    `BIT[pN, pD]` adds the admission-domain sort typing `pD`
    (`< hf.wt` by `SpineOcc.pD_wt_lt`); the conv-K1 derivations are
    bounded by `CvP.wt_dl_lt`/`wt_dr_lt` under `ha`; each path edge's
    stored derivations by the edge bound. -/
theorem iota_slot_request_below (Aw : Nat → Nat) (site : IotaSite E n Γ)
    (j : Nat) {qs : List RawQuery}
    (hq : request_of_iota_slot (planIota site) j = some qs) :
    ∀ q ∈ qs, ∀ d ∈ q.derivations, d.wt Aw < site.N Aw := by
  intro q hqin d hd
  unfold request_of_iota_slot at hq
  cases hget : (planIota site).slots[j]? with
  | none => rw [hget] at hq; simp at hq
  | some s =>
      rw [hget] at hq
      simp only [Option.map_some', Option.some.injEq] at hq
      subst hq
      have hsmem : s ∈ (planIota site).slots := List.getElem?_mem hget
      obtain ⟨W, hW, hhf, hha, hhT, harg, hedges⟩ :=
        planIota_slots_below Aw site hsmem
      have ltN : ∀ x, x ≤ W → x < site.N Aw :=
        fun _ hx => Nat.lt_of_le_of_lt hx hW
      have ltNW : ∀ x, x < W → x < site.N Aw :=
        fun _ hx => Nat.lt_trans hx hW
      unfold IotaSlotPlan.requests at hqin
      rcases List.mem_append.mp hqin with hcore | hedge
      · rcases List.mem_append.mp hcore with hpb | hconv
        · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hpb
          rcases hpb with rfl | rfl
          · simp only [RawQuery.derivations, List.mem_cons,
              List.mem_singleton, List.not_mem_nil, or_false] at hd
            rcases hd with rfl | rfl
            · exact ltNW _ hha
            · exact ltN _ (Nat.le_trans (TyP.wt_reg_le Aw s.occ.ha)
                (Nat.le_of_lt hha))
          · simp only [RawQuery.derivations, List.mem_cons,
              List.mem_singleton, List.not_mem_nil, or_false] at hd
            rcases hd with rfl | rfl
            · exact ltN _ (Nat.le_trans (TyP.wt_reg_le Aw s.occ.ha)
                (Nat.le_of_lt hha))
            · exact ltNW _ (Nat.lt_trans (s.occ.pD_wt_lt Aw) hhf)
        · cases harg2 : s.occ.argConv with
          | none =>
              rw [harg2] at hconv
              simp at hconv
          | some c =>
              rw [harg2] at hconv
              have hcW := harg c harg2
              simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hconv
              rcases hconv with rfl | rfl | rfl
              · simp only [RawQuery.derivations, List.mem_cons,
                  List.mem_singleton, List.not_mem_nil, or_false] at hd
                rcases hd with rfl | rfl
                · exact ltN _ (Nat.le_trans (TyP.wt_reg_le Aw s.occ.ha)
                    (Nat.le_of_lt hha))
                · exact ltN _ (Nat.le_trans
                    (Nat.le_of_lt (c.wt_dl_lt Aw))
                    (Nat.le_of_lt hcW))
              · simp only [RawQuery.derivations, List.mem_cons,
                  List.mem_singleton, List.not_mem_nil, or_false] at hd
                rcases hd with rfl | rfl
                · exact ltN _ (Nat.le_trans
                    (Nat.le_of_lt (c.wt_dr_lt Aw))
                    (Nat.le_of_lt hcW))
                · exact ltNW _ (Nat.lt_trans (s.occ.pD_wt_lt Aw) hhf)
              · simp only [RawQuery.derivations, List.mem_cons,
                    List.not_mem_nil, or_false] at hd
                rcases hd with rfl
                exact ltNW _ hcW
      · rcases List.mem_flatMap.mp hedge with ⟨e, he, hq2⟩
        obtain ⟨hview, hsrc, hcvp⟩ := hedges e he
        exact ltN _ (PathEdge.requests_wt_le Aw e W hview hsrc hcvp q hq2
          d hd)

/-! ## first user 1 — the Nat-successor instance (`wSuccU1`) -/

/-- `R(a) = rec P mz ms a` — the recursor spine at `ls = [.succ .zero]`
    as a raw term (sibling of the `pinIotaLhsTy` spine). -/
def s16RecApp (a : Expr Nat) : Expr Nat :=
  .app (.app (.app (.app (.const 3 [.succ .zero]) natMotive) natMinorZ)
    natMinorS) a

/-- The `h0–h3` spine of `pinIotaLhsTy` extracted: `rec P mz ms`
    itself, at `Π n:N. P n`. -/
noncomputable def s16PrefixTy :
    HasTyT natEnvU 1 [] (.app (.app (.app (.const 3 [.succ .zero])
      natMotive) natMinorZ) natMinorS)
      (.pi (.const 0 []) (.app natMotive (.bvar 0))) :=
  have h0 : HasTyT natEnvU 1 [] (.const 3 [.succ .zero]) _ :=
    HasTyT.const [] 3 [.succ .zero] natRecMemberU rfl rfl rfl
  have h1 : HasTyT natEnvU 1 [] (.app (.const 3 [.succ .zero]) natMotive)
      (.pi (.app natMotive (.const 1 []))
        (.pi (.pi (.const 0 []) (.pi (.app natMotive (.bvar 0))
            (.app natMotive (.app (.const 2 []) (.bvar 1)))))
          (.pi (.const 0 []) (.app natMotive (.bvar 0))))) :=
    HasTyT.app [] _ _ _ _ h0 pinIotaMotiveTy
  have h2 : HasTyT natEnvU 1 []
      (.app (.app (.const 3 [.succ .zero]) natMotive) natMinorZ)
      (.pi (.pi (.const 0 []) (.pi (.app natMotive (.bvar 0))
          (.app natMotive (.app (.const 2 []) (.bvar 1)))))
        (.pi (.const 0 []) (.app natMotive (.bvar 0)))) :=
    HasTyT.app [] _ _ _ _ h1 pinIotaMinorZTy
  HasTyT.app [] _ _ _ _ h2 pinIotaMinorSTy

/-- `R a : N` — the spine applied to `ha : a : N`, riding the original
    β conversion `pinIotaMotiveApp` (never `iotaPreserveT`). -/
noncomputable def s16RecAtN (a : Expr Nat)
    (ha : HasTyT natEnvU 1 [] a (.const 0 [])) :
    HasTyT natEnvU 1 [] (s16RecApp a) (.const 0 []) :=
  HasTyT.conv _ _ (.app natMotive a) (.const 0 []) (.succ .zero)
    (HasTyT.app [] _ _ _ _ s16PrefixTy ha) (pinIotaMotiveApp [] a ha)

/-- `ms : Π n:N. Π ih:N. N` — the rhs's own minor typing (the plain-N
    view, two λs over `N` and `zero : N`). -/
noncomputable def s16MinorTy :
    HasTyT natEnvU 1 [] natMinorS
      (.pi (.const 0 []) (.pi (.const 0 []) (.const 0 []))) :=
  have hN1 : CtxWfT natEnvU 1 [.assumption (.const 0 [])] :=
    .assumption [] _ _ .nil pinIotaFamTy
  HasTyT.lam [] (.const 0 []) (.succ .zero) (.lam (.const 0 []) (.const 1 []))
    (.pi (.const 0 []) (.const 0 [])) pinIotaFamTy
    (HasTyT.lam _ (.const 0 []) (.succ .zero) (.const 1 []) (.const 0 [])
      (pinIotaNSortTy _ hN1) (HasTyT.const _ 1 [] natZeroMember rfl rfl rfl))

/-- `iotaRhsOf wSuccU1` is literally `ms zero (R zero)`. -/
theorem s16Rhs_term : iotaRhsOf wSuccU1 =
    .app (.app natMinorS natField) (s16RecApp natField) := rfl

/-- `hRᵀ` — the original rhs typing, built from the real producers. -/
noncomputable def s16RhsTy :
    HasTyT natEnvU 1 [] (iotaRhsOf wSuccU1) (.const 0 []) := by
  rw [s16Rhs_term]
  exact HasTyT.app [] _ _ _ _
    (HasTyT.app [] _ _ _ _ s16MinorTy pinIotaZeroTy)
    (s16RecAtN _ pinIotaZeroTy)

/-- The enriched lhs typing. -/
noncomputable def s16hL : TyP natEnvU 1 [] (iotaLhsOf wSuccU1) (.const 0 []) :=
  enrichHasTyT_of_envWfT natEnvUWfT CtxWfT.nil pinIotaLhsTy

/-- The enriched rhs typing. -/
noncomputable def s16hR : TyP natEnvU 1 [] (iotaRhsOf wSuccU1) (.const 0 []) :=
  enrichHasTyT_of_envWfT natEnvUWfT CtxWfT.nil s16RhsTy

/-- The Nat-successor ι site — `hlhs`/`hrhs`/`dl`/`dr` keep the node's
    four original occurrences, never de-duplicated. -/
noncomputable def natIotaSite : IotaSite natEnvU 1 [] where
  T := .const 0 []
  w := wSuccU1
  d := DerivedIota.of wSuccU1
  hlhs := s16hL
  hrhs := s16hR
  dl := s16hL
  dr := s16hR

/-- The audit's counterexample control: `hlhs`/`hrhs` wrapped in an
    identity `TyP.ewk` (environment extension by reflexivity). The old
    `spineArgs` silently dropped every demand here; `spineViews` crosses
    the wrapper as a pending `ewk` edge and the six slots still appear. -/
noncomputable def natIotaSiteEwk : IotaSite natEnvU 1 [] where
  T := .const 0 []
  w := wSuccU1
  d := DerivedIota.of wSuccU1
  hlhs := .ewk _ _ _ _ _ _ (envExt_refl _) s16hL
  hrhs := .ewk _ _ _ _ _ _ (envExt_refl _) s16hR
  dl := s16hL
  dr := s16hR

/-- The real admission weight at the Nat environment. -/
noncomputable def s16AwNat : Nat → Nat := (enrichEnvWfT natEnvUWfT).admW

/-- A6 §11's hit-bvar control: `s16hL` re-derived as
    `esub (bvar₀ (wk₀ W)) s16hL W` at `Γs = assumption (.const 0 []) :: []`
    — the esub's child is literally `bvar 0` at the hit index, so the
    displayed subject `instantiate 0 _ (.bvar 0) = iotaLhsOf wSuccU1` is
    born from the replacement `s16hL` itself (zero-hit instantiate and
    `substRemove`/`lift` cancellations; same subject, type and witness).
    Under the pre-fix walk (`spineViewsFrozen`) the spine vanishes; the
    repaired `spineViews` continues into the replacement. -/
noncomputable def s16hL_esub : TyP natEnvU 1 [] (iotaLhsOf wSuccU1) (.const 0 []) :=
  .esub natEnvU 1 [.assumption (.const 0 [])]
    (.bvar 0) (.const 0 []) (.const 0 []) (iotaLhsOf wSuccU1) 0 s16hL.reg.1
    (.bvar _ _ _ 0 (.const 0 []) _ rfl
      (.wk _ _ _ _ _ (.assumption (.const 0 [])) 0 s16hL.reg.2))
    rfl s16hL s16hL.reg.2

/-- PIN: the control's displayed lhs keeps `s16hL`'s full real spine —
    the replacement's occurrences survive the hit-bvar crossing. -/
theorem s16hL_esub_spine_count :
    (s16hL_esub.spineViews []).length = (s16hL.spineViews []).length := by
  decide

/-- PIN: the spine is non-empty after the fix — the displayed lhs spine
    does not disappear (A6 §11's missed-ι coverage). -/
theorem s16hL_esub_spine_nonempty :
    0 < (s16hL_esub.spineViews []).length := by
  decide

/-- PIN: every collected occurrence's outermost crossed wrapper is the
    `.esub` edge — the packet route records the hit-bvar crossing. -/
theorem s16hL_esub_path_esub :
    ∀ o ∈ s16hL_esub.spineViews [], o.path.head?.map (·.kind) = some .esub := by
  decide

/-- PIN: the frozen pre-fix function still collapses the control's spine
    to `[]` — the repaired traversal is what carries the occurrences. -/
theorem s16hL_esub_frozen_nil :
    s16hL_esub.spineViewsFrozen [] = [] := rfl

/-- The Nat plan — the six §4 slots. -/
noncomputable def natIotaPlan : IotaRequestPlan natEnvU 1 [] :=
  planIota natIotaSite

/-- PIN: exactly the six §4 slots — `P`, `mz`, `ms`, the major, the
    major's field, the rhs's directRec result — in §4's row order. -/
theorem natIotaPlan_origins :
    natIotaPlan.slots.map (·.origin) =
      [.spine 0, .spine 1, .spine 2, .spine 3, .majorField 0,
       .rhsDirectRec 1] := by
  decide

/-- PIN: the identity-`ewk`-wrapped site keeps all six slots — the
    transport wrapper records a pending `ewk` edge, never a dropped
    demand (the REFUSE's exact counterexample). -/
theorem natIotaPlan_ewk_origins :
    (planIota natIotaSiteEwk).slots.map (·.origin) =
      [.spine 0, .spine 1, .spine 2, .spine 3, .majorField 0,
       .rhsDirectRec 1] := by
  decide

/-- PIN: every ewk-wrapped slot carries its transport receipt — an
    `.ewk` edge appears in each slot's path. -/
theorem natIotaPlan_ewk_path :
    (planIota natIotaSiteEwk).slots.map
      (fun s => decide (.ewk ∈ s.occ.path.map (·.kind))) =
      List.replicate 6 true := by
  decide

/-- the same edge instantiated at the Nat site. -/
theorem nat_slot_request_below (j : Nat) {qs : List RawQuery}
    (hq : request_of_iota_slot natIotaPlan j = some qs) :
    ∀ q ∈ qs, ∀ d ∈ q.derivations,
      d.wt s16AwNat < natIotaSite.N s16AwNat :=
  iota_slot_request_below s16AwNat natIotaSite j hq

/-- PIN: every Nat slot emits at least the always-on `PB`/`BIT` pair —
    `request_of_iota_slot` is never PB-only and never empty. -/
theorem natIotaPlan_request_minimum :
    natIotaPlan.slots.map (fun s => decide (2 ≤ s.requests.length)) =
      List.replicate 6 true := by
  decide

/-- PIN: every Nat slot's first request is the `PB` proof-status row. -/
theorem natIotaPlan_pb_first :
    natIotaPlan.slots.map
      (fun s => (s.requests.head?).map RawQuery.isPb) =
      List.replicate 6 (some true) := by
  decide

/-- PIN: every Nat slot's `pD` types the SAME subject `occ.A` at a
    `.sort` — the re-displayed view lands on the admitted domain, so
    `BIT[pN, pD]`'s two operands are same-subject `domain : sort`
    typings at `occ.Γ`. -/
theorem natIotaPlan_pD_domain :
    natIotaPlan.slots.map (fun s =>
      decide (s.pD.e = s.occ.A) &&
        (match s.pD.T with | .sort _ => true | _ => false)) =
      List.replicate 6 true := by
  decide

/-- the same edge instantiated at the ewk-wrapped Nat site — the
    strict bound survives the pending `ewk` edge (every stored
    derivation still sits below `N`). -/
theorem nat_ewk_slot_request_below (j : Nat) {qs : List RawQuery}
    (hq : request_of_iota_slot (planIota natIotaSiteEwk) j = some qs) :
    ∀ q ∈ qs, ∀ d ∈ q.derivations,
      d.wt s16AwNat < natIotaSiteEwk.N s16AwNat :=
  iota_slot_request_below s16AwNat natIotaSiteEwk j hq

/-! ## first user 2 — ct001's List-cons instance (`wCons`) -/

/-- The List-cons admission origin: `L.rec` sits at member 3 of
    `listEnv`, `cons` at 2, the family at 0 — the witness's own member
    lookups, the actual admission source. -/
theorem listCons_origin :
    listEnv.members wCons.recRef = some wCons.recMember ∧
    listEnv.members wCons.ctorRef = some wCons.ctorMember ∧
    listEnv.members wCons.familyRef = some wCons.famMember :=
  ⟨wCons.hrec, wCons.hctor, wCons.hfam⟩

/-- The witness-level slot count a `planIota` produces for `w`: one
    slot per recursor-application argument (`preMajor ++ [major]`), one
    per constructor field, one per directRec result. -/
def planSlotCount {E : ResolvedEnv} (w : IotaWitness E) : Nat :=
  w.preMajor.length + 1 + w.fields.length + (recResultIdxs w.kinds 0).length

/-- PIN: the Nat instance's plan has the §4 count `6`. -/
theorem natIotaPlan_slotCount : natIotaPlan.slots.length = 6 := by
  decide

/-- PIN: `wSuccU1`'s witness-level slot count agrees. -/
theorem wSuccU1_slotCount : planSlotCount wSuccU1 = 6 := rfl

/-- PIN: `wCons`'s witness-level slot shape — `L.rec A P mn mc` +
    major + `hd`/`tl` fields + the `tl` directRec result = `8`. -/
theorem wCons_slotCount : planSlotCount wCons = 8 := rfl

/-- The List-cons below edge: the same real edge, instantiated at any
    `wCons` site — discharged as soon as ct001's typed lhs lands (the
    plan's slots are the site's own forest subderivations either way). -/
theorem listCons_slot_request_below (Aw : Nat → Nat)
    (site : IotaSite listEnv n Γ) (_hw : site.w = wCons)
    (j : Nat) {qs : List RawQuery}
    (hq : request_of_iota_slot (planIota site) j = some qs) :
    ∀ q ∈ qs, ∀ d ∈ q.derivations, d.wt Aw < site.N Aw :=
  iota_slot_request_below Aw site j hq

#print axioms Rcic.Syn.RawQuery
#print axioms Rcic.Syn.IotaSite
#print axioms Rcic.Syn.planIota
#print axioms Rcic.Syn.request_of_iota_slot
#print axioms Rcic.Syn.iota_slot_request_below
#print axioms Rcic.Syn.s16PrefixTy
#print axioms Rcic.Syn.s16RecAtN
#print axioms Rcic.Syn.s16MinorTy
#print axioms Rcic.Syn.s16RhsTy
#print axioms Rcic.Syn.natIotaSite
#print axioms Rcic.Syn.natIotaSiteEwk
#print axioms Rcic.Syn.s16hL_esub
#print axioms Rcic.Syn.s16hL_esub_spine_count
#print axioms Rcic.Syn.s16hL_esub_spine_nonempty
#print axioms Rcic.Syn.s16hL_esub_path_esub
#print axioms Rcic.Syn.s16hL_esub_frozen_nil
#print axioms Rcic.Syn.natIotaPlan_origins
#print axioms Rcic.Syn.natIotaPlan_ewk_origins
#print axioms Rcic.Syn.natIotaPlan_ewk_path
#print axioms Rcic.Syn.nat_slot_request_below
#print axioms Rcic.Syn.natIotaPlan_request_minimum
#print axioms Rcic.Syn.natIotaPlan_pb_first
#print axioms Rcic.Syn.nat_ewk_slot_request_below
#print axioms Rcic.Syn.natIotaPlan_slotCount
#print axioms Rcic.Syn.wCons_slotCount
#print axioms Rcic.Syn.listCons_slot_request_below

end Rcic.Syn
