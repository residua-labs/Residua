import rcic.RcicF8DTileStep
import rcic.RcicF8OM1
import rcic.RcicLevelCalc
import rcic.RcicFixtures

/-!
Stored-mtype provenance for W-X-LEVELS-MTYPE-PROVENANCE (approved S1 #7164).

`storedMtypeLevels?` reads `hres : E.members r = some m` and recurses on that
stored `mtype`. After a syntactic-equality shortcut it builds a reverse
leaf-free `EvTc` by `sortsTc`, `EvCv.consts` at a stored sort, or `EvTc.piCod`
on an unchanged atomic domain. There is no caller-supplied type. Shapes
outside that fragment return `none`. No `EvTy` introduction arm is added.

`closure_claim = 0`.

`natRecMemberU` at `[.zero]` versus `[.max .zero .zero]` changes the root Π
domain (approved note §7). That fixture is `none` here. A leaf-free chain is
not fabricated, and `EvTy.pi` is not added to force one.
-/

set_option autoImplicit false

namespace Rcic.Declarative.F8Measure.MtypeProv

open Rcic.Declarative.F8Measure

variable {E : ResolvedEnv} {n : Nat}

structure StoredChain (R : List (Jd E n)) (Δ : LCtx) (A B : Expr Nat) where
  tc : EvTc R Δ A B
  leaves_nil : tc.leaves = []

structure AtomTy (R : List (Jd E n)) (Δ : LCtx) (A : Expr Nat) where
  u : Level
  ty : EvTy R Δ A (.sort u)
  leaves_nil : ty.leaves = []

structure StoredLevelsOut (E : ResolvedEnv) (n : Nat) (R : List (Jd E n))
    (Γ : LCtx) (r : Nat) (ls ls' : List Level) where
  member : CheckedMember
  lookup : E.members r = some member
  arity : ls.length = member.arity
  arity' : ls'.length = member.arity
  tc : EvTc R Γ (instantiateLevels ls' member.mtype) (instantiateLevels ls member.mtype)
  leaves_nil : tc.leaves = []
  bounds : levelsBounded n ls = true
  bounds' : levelsBounded n ls' = true

def storedRefl {R : List (Jd E n)} {Δ : LCtx} {A B : Expr Nat} (h : A = B) :
    StoredChain R Δ A B where
  tc := EvTc.cast rfl rfl h (EvTc.refl Δ A)
  leaves_nil := by rw [EvTc.cast_leaves]; rfl

def storedRefl? (R : List (Jd E n)) (ls ls' : List Level) (Δ : LCtx) (T : Expr Nat) :
    Option (StoredChain R Δ (instantiateLevels ls' T) (instantiateLevels ls T)) :=
  if h : instantiateLevels ls' T = instantiateLevels ls T then
    some (storedRefl h)
  else
    none

private def idxOfSort {vs : List Level} {k : Level} {T : Expr Nat} (h : T = .sort k) :
    instantiateLevels vs T = .sort (instLevel vs k) := by
  subst h
  rfl

private def evCvCastIndex {R : List (Jd E n)} {Δ : LCtx} {A B U U' : Expr Nat}
    (h : U = U') (c : EvCv R Δ A B U) : EvCv R Δ A B U' :=
  h ▸ c

private theorem evCvCastIndex_leaves {R : List (Jd E n)} {Δ : LCtx} {A B U U' : Expr Nat}
    (h : U = U') (c : EvCv R Δ A B U) :
    (evCvCastIndex h c).leaves = c.leaves := by
  subst h
  rfl

/-- Atomic domain typing already on this main: sort, const-at-sort, var-at-sort. -/
def storedAtom? (R : List (Jd E n)) (Δ : LCtx) (A : Expr Nat) : Option (AtomTy R Δ A) :=
  match A with
  | .sort l =>
    some { u := .succ l, ty := EvTy.sort l, leaves_nil := rfl }
  | .bvar i =>
    match hlk : lookupType Δ i with
    | some (.sort u) =>
      some { u := u, ty := EvTy.var i (.sort u) hlk, leaves_nil := rfl }
    | _ => none
  | .const s vs =>
    match hmem : E.members s with
    | none => none
    | some q =>
      if hlen : vs.length = q.arity then
        if hb : levelsBounded n vs = true then
          match hq : q.mtype with
          | .sort k =>
            some {
              u := instLevel vs k
              ty := EvTy.cast rfl rfl (idxOfSort hq)
                (EvTy.const s vs q hmem hlen hb)
              leaves_nil := by rw [EvTy.cast_leaves, EvTy.leaves]
            }
          | .bvar _ => none
          | .const _ _ => none
          | .app _ _ => none
          | .lam _ _ => none
          | .pi _ _ => none
          | .letE _ _ _ => none
          | .lit _ => none
        else none
      else none
  | .app _ _ => none
  | .lam _ _ => none
  | .pi _ _ => none
  | .letE _ _ _ => none
  | .lit _ => none

/-- Const arm. Lookup, both arities, both bounds, then a stored sort index. -/
def storedConst? (R : List (Jd E n)) (ls ls' : List Level) (heq : eqNList ls ls')
    (Δ : LCtx) (s : Nat) (us : List Level) :
    Option (StoredChain R Δ (instantiateLevels ls' (.const s us))
      (instantiateLevels ls (.const s us))) :=
  match hmem : E.members s with
  | none => none
  | some q =>
    let us' := us.map (instLevel ls')
    let us0 := us.map (instLevel ls)
    if hlen' : us'.length = q.arity then
      if hlen0 : us0.length = q.arity then
        if hb' : levelsBounded n us' = true then
          if hb0 : levelsBounded n us0 = true then
            match hq : q.mtype with
            | .sort k =>
              let cv := evCvCastIndex (idxOfSort hq)
                (EvCv.consts s us' us0 q hmem hlen' hb' hb0
                  (eqNList_symm' (instLevel_eqNList_map heq us)))
              some {
                tc := EvTc.ofCv (instLevel us' k) cv
                leaves_nil := by
                  rw [EvTc.leaves, evCvCastIndex_leaves, EvCv.leaves]
              }
            | .bvar _ => none
            | .const _ _ => none
            | .app _ _ => none
            | .lam _ _ => none
            | .pi _ _ => none
            | .letE _ _ _ => none
            | .lit _ => none
          else none
        else none
      else none
    else none

/-- Structural worker. Recurses only on the codomain of a stored Π. -/
def storedMtypeChain? (R : List (Jd E n)) (ls ls' : List Level) (heq : eqNList ls ls') :
    (Δ : LCtx) → (T : Expr Nat) →
      Option (StoredChain R Δ (instantiateLevels ls' T) (instantiateLevels ls T))
  | Δ, .bvar i => storedRefl? R ls ls' Δ (.bvar i)
  | Δ, .lit t => storedRefl? R ls ls' Δ (.lit t)
  | Δ, .sort l =>
    match storedRefl? R ls ls' Δ (.sort l) with
    | some c => some c
    | none =>
      let u' := instLevel ls' l
      let u := instLevel ls l
      let h := eqN_symm' (instLevel_eqNList heq l)
      some { tc := sortsTc u' u h, leaves_nil := sortsTc_leaves u' u h }
  | Δ, .const s us =>
    match storedRefl? R ls ls' Δ (.const s us) with
    | some c => some c
    | none => storedConst? R ls ls' heq Δ s us
  | Δ, .app f x => storedRefl? R ls ls' Δ (.app f x)
  | Δ, .lam a b => storedRefl? R ls ls' Δ (.lam a b)
  | Δ, .letE a v b => storedRefl? R ls ls' Δ (.letE a v b)
  | Δ, .pi A B =>
    match storedRefl? R ls ls' Δ (.pi A B) with
    | some c => some c
    | none =>
      if hdom : instantiateLevels ls' A = instantiateLevels ls A then
        let A0 := instantiateLevels ls A
        match storedAtom? R Δ A0 with
        | none => none
        | some atom =>
          match storedMtypeChain? R ls ls' heq (.assumption A0 :: Δ) B with
          | none => none
          | some cB =>
            let raw := EvTc.piCod atom.u atom.ty cB.tc
            some {
              tc := EvTc.cast rfl
                (congrArg (fun d => Expr.pi d (instantiateLevels ls' B)) hdom.symm) rfl raw
              leaves_nil := by
                rw [EvTc.cast_leaves, EvTc.leaves, atom.leaves_nil, cB.leaves_nil]
                rfl
            }
      else
        none

/-- Reverse leaf-free chain for the member stored at `r`. No type argument. -/
def storedMtypeLevels? (R : List (Jd E n)) (Γ : LCtx) (r : Nat) (ls ls' : List Level)
    (heq : eqNList ls ls') (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) :
    Option (StoredLevelsOut E n R Γ r ls ls') :=
  match hres : E.members r with
  | none => none
  | some m =>
    if hlen : ls.length = m.arity then
      match storedMtypeChain? R ls ls' heq Γ m.mtype with
      | none => none
      | some c =>
        have hlen' : ls'.length = m.arity :=
          (eqNList_length ls ls' heq).symm.trans hlen
        some {
          member := m
          lookup := hres
          arity := hlen
          arity' := hlen'
          tc := c.tc
          leaves_nil := c.leaves_nil
          bounds := hwf
          bounds' := hwf'
        }
    else
      none

/-! ### shared level lists -/

def zeroLs : List Level := [.zero]
def maxLs : List Level := [.max .zero .zero]

theorem eqN_zero_max : eqN (.zero) (.max .zero .zero) := fun _ => rfl

theorem eqNList_zero_max : eqNList zeroLs maxLs := ⟨eqN_zero_max, True.intro⟩

theorem eqNList_zero_zero : eqNList zeroLs zeroLs := ⟨fun _ => rfl, True.intro⟩

theorem eqNList_nil : eqNList ([] : List Level) [] := True.intro

theorem bounds_zero : levelsBounded 1 zeroLs = true := rfl
theorem bounds_max : levelsBounded 1 maxLs = true := rfl
theorem bounds_nil : levelsBounded 1 ([] : List Level) = true := rfl

def sortMember : CheckedMember := ⟨.axiomM, 1, .sort (.param 0), none⟩
def sortEnv : ResolvedEnv := extendEnv emptyEnv 0 sortMember

def constInner : CheckedMember := ⟨.axiomM, 1, .sort (.param 0), none⟩
def constOuter : CheckedMember := ⟨.axiomM, 1, .const 0 [.param 0], none⟩
def constEnv : ResolvedEnv := extendEnv (extendEnv emptyEnv 0 constInner) 1 constOuter

def piMember : CheckedMember := ⟨.axiomM, 1, .pi (.sort .zero) (.sort (.param 0)), none⟩
def piEnv : ResolvedEnv := extendEnv emptyEnv 0 piMember

def domChgMember : CheckedMember :=
  ⟨.axiomM, 1, .pi (.sort (.param 0)) (.sort .zero), none⟩
def domChgEnv : ResolvedEnv := extendEnv emptyEnv 0 domChgMember

def domTyMember : CheckedMember :=
  ⟨.axiomM, 1, .pi (.pi (.sort .zero) (.sort .zero)) (.sort (.param 0)), none⟩
def domTyEnv : ResolvedEnv := extendEnv emptyEnv 0 domTyMember

def notSortInner : CheckedMember :=
  ⟨.axiomM, 1, .pi (.sort .zero) (.sort .zero), none⟩
def notSortOuter : CheckedMember := ⟨.axiomM, 1, .const 0 [.param 0], none⟩
def notSortEnv : ResolvedEnv :=
  extendEnv (extendEnv emptyEnv 0 notSortInner) 1 notSortOuter

def boundInner : CheckedMember := ⟨.axiomM, 1, .sort .zero, none⟩
def boundOuter : CheckedMember :=
  ⟨.axiomM, 1, .const 0 [.max (.param 0) (.param 5)], none⟩
def boundEnv : ResolvedEnv := extendEnv (extendEnv emptyEnv 0 boundInner) 1 boundOuter

def appMember : CheckedMember :=
  ⟨.axiomM, 1, .app (.sort (.param 0)) (.sort .zero), none⟩
def appEnv : ResolvedEnv := extendEnv emptyEnv 0 appMember

def lamMember : CheckedMember :=
  ⟨.axiomM, 1, .lam (.sort .zero) (.sort (.param 0)), none⟩
def lamEnv : ResolvedEnv := extendEnv emptyEnv 0 lamMember

def letMember : CheckedMember :=
  ⟨.axiomM, 1, .letE (.sort .zero) (.sort .zero) (.sort (.param 0)), none⟩
def letEnv : ResolvedEnv := extendEnv emptyEnv 0 letMember

abbrev noRoots (E : ResolvedEnv) : List (Jd E 1) := []

theorem pin_sort_accepts :
    (storedMtypeLevels? (noRoots sortEnv) [] 0 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max).isSome = true := rfl

theorem pin_sort_leaves :
    match storedMtypeLevels? (noRoots sortEnv) [] 0 zeroLs maxLs
        eqNList_zero_max bounds_zero bounds_max with
    | some o => o.tc.leaves = []
    | none => False := by
  cases h : storedMtypeLevels? (noRoots sortEnv) [] 0 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max with
  | some o => exact o.leaves_nil
  | none => nomatch h

theorem pin_const_accepts :
    (storedMtypeLevels? (noRoots constEnv) [] 1 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max).isSome = true := rfl

theorem pin_const_leaves :
    match storedMtypeLevels? (noRoots constEnv) [] 1 zeroLs maxLs
        eqNList_zero_max bounds_zero bounds_max with
    | some o => o.tc.leaves = []
    | none => False := by
  cases h : storedMtypeLevels? (noRoots constEnv) [] 1 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max with
  | some o => exact o.leaves_nil
  | none => nomatch h

theorem pin_pi_accepts :
    (storedMtypeLevels? (noRoots piEnv) [] 0 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max).isSome = true := rfl

theorem pin_pi_leaves :
    match storedMtypeLevels? (noRoots piEnv) [] 0 zeroLs maxLs
        eqNList_zero_max bounds_zero bounds_max with
    | some o => o.tc.leaves = []
    | none => False := by
  cases h : storedMtypeLevels? (noRoots piEnv) [] 0 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max with
  | some o => exact o.leaves_nil
  | none => nomatch h

theorem pin_piDomainChanges :
    storedMtypeLevels? (noRoots domChgEnv) [] 0 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max = none := rfl

theorem pin_piDomainTyping :
    storedMtypeLevels? (noRoots domTyEnv) [] 0 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max = none := rfl

theorem pin_constIndexNotSort :
    storedMtypeLevels? (noRoots notSortEnv) [] 1 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max = none := rfl

theorem pin_appChanges :
    storedMtypeLevels? (noRoots appEnv) [] 0 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max = none := rfl

theorem pin_lamChanges :
    storedMtypeLevels? (noRoots lamEnv) [] 0 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max = none := rfl

theorem pin_letChanges :
    storedMtypeLevels? (noRoots letEnv) [] 0 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max = none := rfl

theorem pin_lookup_miss :
    storedMtypeLevels? (noRoots sortEnv) [] 7 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max = none := rfl

theorem pin_arity_miss :
    storedMtypeLevels? (noRoots sortEnv) [] 0 ([] : List Level) ([] : List Level)
      eqNList_nil bounds_nil bounds_nil = none := rfl

theorem pin_bounds_miss :
    storedMtypeLevels? (noRoots boundEnv) [] 1 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max = none := rfl

/-- Real member 3. The two `eqN` lists change the root domain, so the fragment
returns `none`. Equal lists on the same member are the leaf-free refl below. -/
theorem pin_natRecMemberU_zero_vs_max :
    storedMtypeLevels? (noRoots natEnvU) [] 3 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max = none := rfl

theorem pin_natRecMemberU_equal_leaves :
    match storedMtypeLevels? (noRoots natEnvU) [] 3 zeroLs zeroLs
        eqNList_zero_zero bounds_zero bounds_zero with
    | some o => o.tc.leaves = []
    | none => False := by
  cases h : storedMtypeLevels? (noRoots natEnvU) [] 3 zeroLs zeroLs
      eqNList_zero_zero bounds_zero bounds_zero with
  | some o => exact o.leaves_nil
  | none => nomatch h

/-! ### replacement-member tooth -/

structure Claim (E : ResolvedEnv) (n : Nat) (R : List (Jd E n)) (Γ : LCtx)
    (r : Nat) (ls ls' : List Level) where
  claimed : CheckedMember
  tc : EvTc R Γ (instantiateLevels ls' claimed.mtype) (instantiateLevels ls claimed.mtype)
  leaves_nil : tc.leaves = []

def sameMember (a b : CheckedMember) : Bool :=
  decide (a.mclass = b.mclass) && decide (a.arity = b.arity) &&
    decide (a.mtype = b.mtype) && decide (a.body = b.body)

/-- Shipped check: a caller member is accepted only when it is the stored one,
and the chain is the reader's, never the caller's. -/
def acceptStoredClaim (R : List (Jd E n)) (Γ : LCtx) (r : Nat) (ls ls' : List Level)
    (heq : eqNList ls ls') (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (c : Claim E n R Γ r ls ls') :
    Option (StoredLevelsOut E n R Γ r ls ls') :=
  match E.members r with
  | none => none
  | some m =>
    if sameMember c.claimed m = true then
      storedMtypeLevels? R Γ r ls ls' heq hwf hwf'
    else
      none

/-- Mutant: ignore `hres` and accept the caller member and its chain. -/
def acceptIgnoringHres {R : List (Jd E n)} {Γ : LCtx} {r : Nat} {ls ls' : List Level}
    (c : Claim E n R Γ r ls ls') : Option (Claim E n R Γ r ls ls') :=
  some c

def replMember : CheckedMember := ⟨.axiomM, 1, .sort .zero, none⟩

def replTc : EvTc (noRoots sortEnv) [] (instantiateLevels maxLs replMember.mtype)
    (instantiateLevels zeroLs replMember.mtype) :=
  EvTc.refl [] (.sort .zero)

def replClaim : Claim sortEnv 1 (noRoots sortEnv) [] 0 zeroLs maxLs where
  claimed := replMember
  tc := replTc
  leaves_nil := rfl

theorem pin_replacement_differs : sameMember replMember sortMember = false := rfl

theorem pin_replacement_rejected :
    acceptStoredClaim (noRoots sortEnv) [] 0 zeroLs maxLs
      eqNList_zero_max bounds_zero bounds_max replClaim = none := rfl

theorem pin_mutant_replacement_accepts :
    (acceptIgnoringHres replClaim).isSome = true := rfl

/-! ### right-index tooth -/

def forwardTc : EvTc (noRoots sortEnv) []
    (instantiateLevels zeroLs sortMember.mtype)
    (instantiateLevels maxLs sortMember.mtype) :=
  sortsTc .zero (.max .zero .zero) eqN_zero_max

/-- Lists swapped, forward chain. Index is the right instantiation. -/
def swappedValley : Valley (noRoots sortEnv) []
    (.const 0 maxLs) (.const 0 zeroLs)
    (instantiateLevels maxLs sortMember.mtype) :=
  Valley.ofConstsWith [] 0 maxLs zeroLs sortMember rfl rfl bounds_max bounds_zero
    (eqNList_symm' eqNList_zero_max) forwardTc

def rightIndexValley : Valley (noRoots sortEnv) []
    (.const 0 zeroLs) (.const 0 maxLs)
    (instantiateLevels maxLs sortMember.mtype) :=
  Valley.symm swappedValley

def acceptLeftIndex {a b T : Expr Nat} (leftIdx : Expr Nat)
    (v : Valley (noRoots sortEnv) [] a b T) :
    Option (Valley (noRoots sortEnv) [] a b T) :=
  if T = leftIdx then some v else none

/-- Mutant: drop the index check. -/
def acceptDroppingIndex {a b T : Expr Nat}
    (v : Valley (noRoots sortEnv) [] a b T) :
    Option (Valley (noRoots sortEnv) [] a b T) :=
  some v

theorem pin_right_index_is_right :
    instantiateLevels maxLs sortMember.mtype =
      .sort (.max .zero .zero) := rfl

theorem pin_right_index_rejected :
    acceptLeftIndex (instantiateLevels zeroLs sortMember.mtype) rightIndexValley = none := rfl

theorem pin_mutant_right_index_accepts :
    (acceptDroppingIndex rightIndexValley).isSome = true := rfl

/-! ### axiom audit. Names below are the pins the build log must show. -/

#print axioms pin_sort_accepts
#print axioms pin_sort_leaves
#print axioms pin_const_accepts
#print axioms pin_const_leaves
#print axioms pin_pi_accepts
#print axioms pin_pi_leaves
#print axioms pin_piDomainChanges
#print axioms pin_piDomainTyping
#print axioms pin_constIndexNotSort
#print axioms pin_appChanges
#print axioms pin_lamChanges
#print axioms pin_letChanges
#print axioms pin_lookup_miss
#print axioms pin_arity_miss
#print axioms pin_bounds_miss
#print axioms pin_natRecMemberU_zero_vs_max
#print axioms pin_natRecMemberU_equal_leaves
#print axioms pin_replacement_differs
#print axioms pin_replacement_rejected
#print axioms pin_mutant_replacement_accepts
#print axioms pin_right_index_is_right
#print axioms pin_right_index_rejected
#print axioms pin_mutant_right_index_accepts

end Rcic.Declarative.F8Measure.MtypeProv
