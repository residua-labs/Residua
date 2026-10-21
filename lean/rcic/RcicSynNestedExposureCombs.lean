import rcic.RcicSynNestedExposureFixture

/-!
# Syntactic sortRow, S20 §5 — the four nested combinations

`research/rcic/sortrow/S20_NESTED_EXPOSURE_HE.md` §5 (ChatGPT, #7415).

One decomposition, four different erased actions: the §6 two-level fixture is
instantiated for each inner/outer transport pair — `esub/esub`, `esub/lsub`,
`lsub/esub`, `lsub/lsub`. Whether `x`/`y` sit in `.assumption` or `.letBinding`
slots decides which transport is legal; every combination lands on the same
displayed head `[] ⊢ S₀ : S₁` and bills the same `[2,2,1,1,6]` atoms.

What this module measures:

* each layer chooses drop/inst/inline under **its own** `σ`, `ρ`, and level
  map — the `eps` clauses are the mechanism; the four pins compute each
  route's actual erased action (`s20c_eps_*`), all `.sort 0`;
* an outer `lsub` inlines `hv.eps σ ρ` — that layer's own `localize κ₂ r₂`
  (`s20c_outer_inline_localize`, `s20c_el_inner_eps`);
* the inner `lsub`'s payload is computed by resolving through the ρ it
  receives — a separate route, not a shared result
  (`s20c_ll_inner_route`, `s20c_pin_no_swapped_payloads`);
* control: a certificate obtained without the outer `τ₂` is never reused for
  `τ₂-view(V₁)` just because `V₁`'s term is the same — the untransported
  certificate erases to `.bvar 0`, the real `τ₂(V₁)` erases to `.sort 0`
  (`s20c_pin_no_cert_reuse_without_outer`).

`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the context variants -/

/-- `Γ₀` for the esub/lsub combination: `x : S₁` an assumption at index `0`,
    `y := S₀` a let binding at index `1`. -/
def s20cΓ0_el : LCtx :=
  [.assumption (.sort (.succ .zero)), .letBinding (.sort (.succ .zero)) (.sort .zero)]

/-- `Γ₀` for the lsub/esub combination: `x := y` a let binding at index `0`
    (its stored value `.bvar 0` is the entry below — `y`), `y : S₁` an
    assumption at index `1`. -/
def s20cΓ0_le : LCtx :=
  [.letBinding (.sort (.succ .zero)) (.bvar 0), .assumption (.sort (.succ .zero))]

/-- `Γ₀` for the lsub/lsub combination: `x := y` and `y := S₀` both let
    bindings, each with its own stored value. -/
def s20cΓ0_ll : LCtx :=
  [.letBinding (.sort (.succ .zero)) (.bvar 0),
    .letBinding (.sort (.succ .zero)) (.sort .zero)]

/-- The `Γ₁` left by `substRemove _ 0` whenever `y` is a let binding —
    shared by the esub/lsub outer layer and the lsub/lsub outer layer. -/
def s20cΓ1_lb : LCtx := [.letBinding (.sort (.succ .zero)) (.sort .zero)]

/-! ## §2 the derivation variants -/

/-- `G₀`/`D₀`/`V₁`/`W₁` variants for the let-binding contexts. `TyP.bvar`
    types a bound variable at a `.letBinding` slot through the same
    `lookupType` route — the stored value does not enter the typing. -/
def s20cG0_el (E : ResolvedEnv) (n : Nat) :
    TyP E n s20cΓ0_el (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort E n s20cΓ0_el (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

def s20cD0_el (E : ResolvedEnv) (n : Nat) :
    TyP E n s20cΓ0_el (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar E n s20cΓ0_el 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
    (s20cG0_el E n)

/-- `W₁` at the let-binding `Γ₁` — τ₁'s `hvT` for the let-binding stacks. -/
def s20cW1_lb (E : ResolvedEnv) (n : Nat) :
    TyP E n s20cΓ1_lb (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort E n s20cΓ1_lb (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- `V₁` for a `y`-as-let-binding `Γ₁`: `[y := S₀ : S₁] ⊢ y : S₁`, weight `2`.
    Shared by the esub/lsub inner `hv` and the lsub/lsub inner `hv`. -/
def s20cV1_lb (E : ResolvedEnv) (n : Nat) :
    TyP E n s20cΓ1_lb (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar E n s20cΓ1_lb 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
    (s20cW1_lb E n)

/-- `G₀`/`D₀` variants where `x` is a let binding (lsub inner stacks). -/
def s20cG0_le (E : ResolvedEnv) (n : Nat) :
    TyP E n s20cΓ0_le (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort E n s20cΓ0_le (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

def s20cD0_le (E : ResolvedEnv) (n : Nat) :
    TyP E n s20cΓ0_le (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar E n s20cΓ0_le 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
    (s20cG0_le E n)

def s20cG0_ll (E : ResolvedEnv) (n : Nat) :
    TyP E n s20cΓ0_ll (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort E n s20cΓ0_ll (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

def s20cD0_ll (E : ResolvedEnv) (n : Nat) :
    TyP E n s20cΓ0_ll (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar E n s20cΓ0_ll 0 (.sort (.succ .zero)) (.succ (.succ .zero)) rfl
    (s20cG0_ll E n)

/-! ## §3 the transport stacks: inner `esub`, outer `lsub` -/

/-- `τ₁(D₀)` for esub/lsub — `x` replaced by `y` through the `esub` route;
    lands in `s20cΓ1_lb` where `y` is a stored let value. -/
def s20ct1D0_el (E : ResolvedEnv) (n : Nat) :
    TyP E n s20cΓ1_lb (.bvar 0) (.sort (.succ .zero)) :=
  TyP.esub E n s20cΓ0_el (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.bvar 0) 0 (.succ (.succ .zero)) (s20cD0_el E n) rfl (s20cV1_lb E n)
    (s20cW1_lb E n)

/-- `H` for esub/lsub — the outer `lsub` removes `y`'s let slot at index `0`;
    its `hv` is `V₂` (the stored value `S₀`'s own typing), its `hvT` is `W₂`. -/
def s20cH_el (E : ResolvedEnv) (n : Nat) :
    TyP E n [] (.sort .zero) (.sort (.succ .zero)) :=
  TyP.lsub E n s20cΓ1_lb (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort .zero) 0 (.succ (.succ .zero)) (s20ct1D0_el E n) rfl (s20V2 E n)
    (s20W2 E n)

/-! ## §4 the transport stacks: inner `lsub`, outer `esub` -/

/-- `τ₁(D₀)` for lsub/esub — `x`'s stored let value `y` (`.bvar 0` below `x`)
    is substituted; lands in `s20Γ₁` where `y` is a real assumption. -/
def s20ct1D0_le (E : ResolvedEnv) (n : Nat) :
    TyP E n s20Γ₁ (.bvar 0) (.sort (.succ .zero)) :=
  TyP.lsub E n s20cΓ0_le (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.bvar 0) 0 (.succ (.succ .zero)) (s20cD0_le E n) rfl (s20V1 E n)
    (s20W1 E n)

/-- `H` for lsub/esub — the outer `esub` replaces `y` by `S₀` (`hv = V₂`,
    `hvT = W₂`), exactly the §6 outer layer. -/
def s20cH_le (E : ResolvedEnv) (n : Nat) :
    TyP E n [] (.sort .zero) (.sort (.succ .zero)) :=
  TyP.esub E n s20Γ₁ (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort .zero) 0 (.succ (.succ .zero)) (s20ct1D0_le E n) rfl (s20V2 E n)
    (s20W2 E n)

/-! ## §5 the transport stacks: `lsub`/`lsub` -/

/-- `τ₁(D₀)` for lsub/lsub — `x := y` removed; lands in `s20cΓ1_lb`. -/
def s20ct1D0_ll (E : ResolvedEnv) (n : Nat) :
    TyP E n s20cΓ1_lb (.bvar 0) (.sort (.succ .zero)) :=
  TyP.lsub E n s20cΓ0_ll (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.bvar 0) 0 (.succ (.succ .zero)) (s20cD0_ll E n) rfl (s20cV1_lb E n)
    (s20cW1_lb E n)

/-- `H` for lsub/lsub — two let slots, two own routes: the outer `lsub`
    removes `y := S₀` with `hv = V₂`, `hvT = W₂`. -/
def s20cH_ll (E : ResolvedEnv) (n : Nat) :
    TyP E n [] (.sort .zero) (.sort (.succ .zero)) :=
  TyP.lsub E n s20cΓ1_lb (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort .zero) 0 (.succ (.succ .zero)) (s20ct1D0_ll E n) rfl (s20V2 E n)
    (s20W2 E n)

/-! ## §6 `τ₂`-view of `V₁` (for the control) -/

/-- `τ₂-view(V₁)` in the §6 `esub` sense: `V₁` transported by the outer
    `τ₂` — a `[] ⊢ S₀ : S₁` derivation built from the original `V₁`, `V₂`,
    `W₂` occurrences, not a fresh object. -/
def s20ct2V1 (E : ResolvedEnv) (n : Nat) :
    TyP E n [] (.sort .zero) (.sort (.succ .zero)) :=
  TyP.esub E n s20Γ₁ (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort .zero) 0 (.succ (.succ .zero)) (s20V1 E n) rfl (s20V2 E n)
    (s20W2 E n)

/-! ## §7 the measured pins -/

/-- One decomposition: all four combinations bill the same original atoms,
    `[2,2,1,1,6]` — transport choice does not change the table. -/
theorem s20c_atoms_same (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (s20cH_el E n).atoms Aw = [2, 2, 1, 1, 6] ∧
    (s20cH_le E n).atoms Aw = [2, 2, 1, 1, 6] ∧
    (s20cH_ll E n).atoms Aw = [2, 2, 1, 1, 6] ∧
    (s20H E n).atoms Aw = [2, 2, 1, 1, 6] := ⟨rfl, rfl, rfl, rfl⟩

/-- esub/esub: both layers take the `keep`/`inst` route — erasure `.sort 0`. -/
theorem s20c_eps_ee (E : ResolvedEnv) (n : Nat) :
    (s20H E n).eps id [] = .sort .zero := s20_erasure_term E n

/-- esub/lsub: the outer `lsub` reads `hv.eps σ ρ = .sort 0` (non-`★`) and
    inlines it — that layer's own `localize κ₂ r₂`; the inner `esub` then
    substitutes under `inst`. Final `.sort 0`. -/
theorem s20c_eps_el (E : ResolvedEnv) (n : Nat) :
    (s20cH_el E n).eps id [] = .sort .zero := rfl

/-- lsub/esub: the inner `lsub` resolves `V₁.eps` under the outer-inherited
    ρ `[.keep]` to `.bvar 0` and inlines that; the outer `esub` substitutes
    `V₂`'s `.sort 0`. Final `.sort 0`. -/
theorem s20c_eps_le (E : ResolvedEnv) (n : Nat) :
    (s20cH_le E n).eps id [] = .sort .zero := rfl

/-- lsub/lsub: two let slots, two own routes — each layer computes its own
    `hv.eps σ ρ`. Final `.sort 0`. -/
theorem s20c_eps_ll (E : ResolvedEnv) (n : Nat) :
    (s20cH_ll E n).eps id [] = .sort .zero := rfl

/-- The outer `lsub`'s inline payload is `V₂`'s OWN erasure `.sort 0`
    computed under the outer layer's `σ`, `ρ` — `localize κ₂ r₂`. Position `0`
    of the inserted ρ resolves to it. -/
theorem s20c_outer_inline_localize (E : ResolvedEnv) (n : Nat) :
    resolve (insertDisp (.inline ((s20V2 E n).eps id [])) 0 []) 0 = .sort .zero :=
  rfl

/-- The inner `esub` layer of the esub/lsub stack, evaluated under the ρ the
    outer `lsub` actually passes down (`[.inline .sort0]`): the inner layer
    chooses `keep`/`inst` under ITS map — it never sees the outer `hv`. -/
theorem s20c_el_inner_eps (E : ResolvedEnv) (n : Nat) :
    (s20ct1D0_el E n).eps id [.inline ((s20V2 E n).eps id [])] = .sort .zero := rfl

/-- lsub/lsub's inner route: `V₁`'s erasure is computed through the
    outer-inlined ρ — a separate localize call resolving `bvar 0` to the
    outer payload `.sort 0`; two κs, two target routes, no shared result. -/
theorem s20c_ll_inner_route (E : ResolvedEnv) (n : Nat) :
    (s20cV1_lb E n).eps id [.inline ((s20V2 E n).eps id [])] = .sort .zero := rfl

/-- No swapped payloads: the inner term `y` erases bare to `.bvar 0`, which is
    NOT the outer `lsub`'s payload `.sort 0`. An implementation that swapped
    `V₁`'s term into the outer inline slot would resolve position `0` to
    `.bvar 0` — observably different from the legal `.sort 0`. -/
theorem s20c_pin_no_swapped_payloads (E : ResolvedEnv) (n : Nat) :
    resolve (insertDisp (.inline ((s20V1 E n).eps id [])) 0 []) 0 = .bvar 0 ∧
    resolve (insertDisp (.inline ((s20V2 E n).eps id [])) 0 []) 0 ≠ .bvar 0 :=
  ⟨rfl, fun h => ETm.noConfusion h⟩

/-- Control: a certificate obtained without the outer `τ₂` is never reused
    for `τ₂-view(V₁)` just because `V₁`'s term is the same. The untransported
    `V₁` erases to `.bvar 0`; the real `τ₂(V₁)` — built from `V₁`, `V₂`,
    `W₂`'s original occurrences — erases to `.sort 0`. The certificates are
    keyed by the real transport position and the stage's context/map/ρ;
    `.bvar 0 ≠ .sort 0` is the exhibit that the τ₁-stage certificate does not
    discharge the `τ₂`-view. -/
theorem s20c_pin_no_cert_reuse_without_outer (E : ResolvedEnv) (n : Nat) :
    (s20V1 E n).eps id [] = .bvar 0 ∧
    (s20ct2V1 E n).eps id [] = .sort .zero ∧
    (s20V1 E n).eps id [] ≠ (s20ct2V1 E n).eps id [] :=
  ⟨rfl, rfl, fun h => ETm.noConfusion h⟩

end Rcic.Syn

#print axioms Rcic.Syn.s20cΓ0_el
#print axioms Rcic.Syn.s20cΓ0_le
#print axioms Rcic.Syn.s20cΓ0_ll
#print axioms Rcic.Syn.s20cΓ1_lb
#print axioms Rcic.Syn.s20cG0_el
#print axioms Rcic.Syn.s20cD0_el
#print axioms Rcic.Syn.s20cV1_lb
#print axioms Rcic.Syn.s20cW1_lb
#print axioms Rcic.Syn.s20cG0_le
#print axioms Rcic.Syn.s20cD0_le
#print axioms Rcic.Syn.s20cG0_ll
#print axioms Rcic.Syn.s20cD0_ll
#print axioms Rcic.Syn.s20ct1D0_el
#print axioms Rcic.Syn.s20cH_el
#print axioms Rcic.Syn.s20ct1D0_le
#print axioms Rcic.Syn.s20cH_le
#print axioms Rcic.Syn.s20ct1D0_ll
#print axioms Rcic.Syn.s20cH_ll
#print axioms Rcic.Syn.s20ct2V1
#print axioms Rcic.Syn.s20c_atoms_same
#print axioms Rcic.Syn.s20c_eps_ee
#print axioms Rcic.Syn.s20c_eps_el
#print axioms Rcic.Syn.s20c_eps_le
#print axioms Rcic.Syn.s20c_eps_ll
#print axioms Rcic.Syn.s20c_outer_inline_localize
#print axioms Rcic.Syn.s20c_el_inner_eps
#print axioms Rcic.Syn.s20c_ll_inner_route
#print axioms Rcic.Syn.s20c_pin_no_swapped_payloads
#print axioms Rcic.Syn.s20c_pin_no_cert_reuse_without_outer
