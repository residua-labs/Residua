import rcic.RcicAnnLRFund
import rcic.RcicAnnTel

/-!
# M2-f (2) — the concrete ι on the copy

`iotaFnA E : IotaFnA` is 05 §11–14's ι as a FUNCTION on `ExprA`: on a spine
`rec ls preMajor major` headed by a recursor member of `E` at its telescope arity,
with a constructor-headed major `c lsC cargs`, the selected minor applied to the
fields, a recursor call inserted after each directly recursive field at the field's own
indices (05 §14) and the λ-wrapped call after a function-recursive one (`recCallFunA`) — main's
`IotaWitness` reduct (`iotaRhsOf`: `rhsArgs`, `recCallField`, `familyIdx`) with the annotations
carried through, and the field SHAPES read through erasure (`ctorShapesA`: admission's
`FieldShape` on the erased Π-domains of the stored constructor type; R-NoFunRec-1 step 1 (1c-γ)).
Three layers, so that each law is proved at the layer
that owns it:

* `recSpineA e` — the spine's head, levels, `preMajor` and `major` (syntax only);
* `iotaGroupA E recRef ctorRef` — the group: members and classes, the consecutive
  layout 05 §3 (family, constructors, recursor), the counts `nparams` /
  `nindices` / `nMinors` / `ctorIdx` from the Π-telescopes (`nindices` from the
  recursor type's body `motive idx major`, 05 §13). It reads `E` and two
  references only, so it is INVARIANT under substitution, lifting and level
  instantiation of the spine;
* `iotaReductA s g` — the argument-dependent checks (the spine at the recursor's
  telescope arity with its universe list at the recursor's arity, the major a full
  constructor application, the minor at its slot, the constructor telescope after
  the recursor-side parameters at the CONSTRUCTOR-side universe view
  `ls.take ctorM.arity`, and `fieldsTelA`: the fields walk that telescope with the
  `shapeGuardA` at every recursive field — a constant-headed domain at a directly recursive one
  (05 §8, main's `directRecConstHead`), the guard under which `familyIdxA` commutes with
  substitution) and the reduct, the minor applied to the constructor's fields, at every group
  (W-1 (e): `main`'s ι; at a struct group the head step is the struct arm's, `structPosA`).

Laws here: `IotaRecHeadA` (recursor head, exact telescope arity) and
`IotaConstHeadA`, by inversion of the layers. The telescope algebra the layers read
(`applyTelA`, `fieldsTelA`, `rhsArgsA`, `ctorShapesA`, …) is `RcicAnnTel`'s, placed below
the relation so that the `fam` clause (M2-f (3)) can read it. `IotaLiftA` / `IotaSubstA` /
`IotaLevelsA` are `RcicAnnIotaLaws`', through one syntax-map structure. Pins: the
Nat group computes `rec P mz ms zero ⇝ mz` and `rec P mz ms (succ zero) ⇝ ms zero
(rec P mz ms zero)`; a variable major is no redex; below the arity nothing fires; a group with a
function-recursive constructor (`node : (Sort 0 → T) → T`) computes `rec P ml mn (node g) ⇝
mn g (λ x. rec P ml mn (g x))` (R-NoFunRec-1 step 1 (1c-γ)).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the spine and the group -/

structure RecSpineA where
  recRef : Nat
  ls : List Level
  preMajor : List ExprA
  major : ExprA

/-- the recursor spine read off the syntax: head constant, levels, the arguments
    before the last one, the last one (the major). -/
def recSpineA (e : ExprA) : Option RecSpineA :=
  match (appsSpineA e).1, (appsSpineA e).2.reverse with
  | .const r ls, major :: preRev => some ⟨r, ls, preRev.reverse, major⟩
  | _, _ => none

structure IotaGroupA where
  recM : CheckedMemberA
  ctorM : CheckedMemberA
  famM : CheckedMemberA
  ctorRef : Nat
  familyRef : Nat
  nparams : Nat
  nindices : Nat
  nMinors : Nat
  ctorIdx : Nat

/-- the group counts from the Π-telescopes (05 §13): the recursor type's body is
    `motive idx major`, so its spine has `nindices + 1` arguments; the family's
    Π-count is `nparams + nindices`; the recursor's Π-count must be
    `nparams + 1 + nMinors + nindices + 1`. Returns `(nparams, nindices)`. -/
def groupCountsA (recM famM : CheckedMemberA) (nMinors : Nat) : Option (Nat × Nat) :=
  match (appsSpineA (piBodyA recM.mtypeA)).2.length with
  | 0 => none
  | nindices + 1 =>
      if nindices ≤ piCountA famM.mtypeA ∧
          (piCountA famM.mtypeA - nindices) + 1 + nMinors + nindices + 1 = piCountA recM.mtypeA then
        some (piCountA famM.mtypeA - nindices, nindices)
      else none

/-- the group from `E`, the recursor's reference and the major's HEAD constant: a
    recursor and a constructor member; the family from the recursor type's last
    Π-domain (the major's type `I params idx`, 05 §13); the consecutive layout
    (05 §3: family, constructors `1..nMinors`, recursor); the counts from the
    telescopes. -/
def iotaGroupA (E : ResolvedEnvA) (recRef ctorRef : Nat) : Option IotaGroupA :=
  match E.members recRef, E.members ctorRef with
  | some recM, some ctorM =>
      if recM.mclass = .recursorM ∧ ctorM.mclass = .constructorM then
        match (piDomsA recM.mtypeA).getLast? with
        | some D =>
            match (appsSpineA D).1 with
            | .const familyRef _ =>
                match E.members familyRef with
                | some famM =>
                    if famM.mclass = .inductiveM ∧ familyRef < ctorRef ∧ ctorRef < recRef then
                      match groupCountsA recM famM (recRef - familyRef - 1) with
                      | some (nparams, nindices) =>
                          some ⟨recM, ctorM, famM, ctorRef, familyRef, nparams, nindices,
                            recRef - familyRef - 1, ctorRef - familyRef - 1⟩
                      | none => none
                    else none
                | none => none
            | _ => none
        | none => none
      else none
  | _, _ => none

/-- the reduct at a spine of a known group: the argument-dependent checks — the
    spine at the recursor's telescope arity with its universe list at the
    recursor's arity, the major a full constructor application, the minor at its
    slot, the shapes through erasure, the constructor telescope after the
    recursor-side parameters (constructor-side universe view), the fields walking
    it under the guard — then 05 §14's right-hand side, the λ-wrapped call at a function-recursive
    field (R-NoFunRec-1 step 1 (1c-γ)). -/
def iotaReductA (s : RecSpineA) (g : IotaGroupA) : Option ExprA :=
  (spineHeadRefA s.major).bind fun c =>
    if c = g.ctorRef ∧ s.preMajor.length + 1 = piCountA g.recM.mtypeA ∧
        s.ls.length = g.recM.arity ∧
        (appsSpineA s.major).2.length = piCountA (g.ctorM.normA.getD g.ctorM.mtypeA) ∧
        g.ctorM.arity ≤ s.ls.length then
      (ctorShapesA g.familyRef g.nparams (g.ctorM.normA.getD g.ctorM.mtypeA)).bind fun shapes =>
        (s.preMajor[g.nparams + 1 + g.ctorIdx]?).bind fun minor =>
          (applyTelA (s.preMajor.take g.nparams)
              (instantiateLevelsA (s.ls.take g.ctorM.arity)
                (g.ctorM.normA.getD g.ctorM.mtypeA))).bind fun ctorAfter =>
            if fieldsTelA ((appsSpineA s.major).2.drop g.nparams) shapes ctorAfter then
              some (foldAppsA minor (rhsArgsA (.const s.recRef s.ls) s.preMajor g.nparams g.nMinors
                ((appsSpineA s.major).2.drop g.nparams) shapes ctorAfter))
            else none
    else none

/-- THE CONCRETE ι: the layers composed. It contracts to the minor applied to the constructor's fields
    at every group, as `main`'s ι does (W-1 (e) reverted (b′)'s projection contractum at a struct group:
    there the head step is the struct arm's, `structPosA`, and `main`'s ι is `ConvA.structIota`). -/
def iotaFnA (E : ResolvedEnvA) (e : ExprA) : Option ExprA :=
  (recSpineA e).bind fun s =>
    (spineHeadRefA s.major).bind fun c =>
      (iotaGroupA E s.recRef c).bind fun g => iotaReductA s g

def iotaIfaceA (E : ResolvedEnvA) : IotaIfaceA := ⟨iotaFnA E⟩

/-! ## (2b) inversions of the layers (the telescope predicates' are `RcicAnnTel`'s) -/

theorem recSpineA_some {e : ExprA} {s : RecSpineA} (h : recSpineA e = some s) :
    appsSpineA e = (.const s.recRef s.ls, s.preMajor ++ [s.major]) := by
  unfold recSpineA at h
  split at h
  · rename_i r ls major preRev hhead hrev
    injection h with h
    subst h
    show appsSpineA e = (.const r ls, preRev.reverse ++ [major])
    have hargs : (appsSpineA e).2 = (major :: preRev).reverse := by
      rw [← hrev, List.reverse_reverse]
    rw [List.reverse_cons] at hargs
    exact Prod.ext hhead hargs
  · exact Option.noConfusion h

theorem recSpineA_of_spine {e : ExprA} {r : Nat} {ls : List Level} {pre : List ExprA}
    {maj : ExprA} (h : appsSpineA e = (.const r ls, pre ++ [maj])) :
    recSpineA e = some ⟨r, ls, pre, maj⟩ := by
  unfold recSpineA
  rw [h]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.reverse_reverse]

theorem groupCountsA_some {recM famM : CheckedMemberA} {nMinors nparams nindices : Nat}
    (h : groupCountsA recM famM nMinors = some (nparams, nindices)) :
    nparams + nindices = piCountA famM.mtypeA ∧
      nparams + 1 + nMinors + nindices + 1 = piCountA recM.mtypeA ∧
      (appsSpineA (piBodyA recM.mtypeA)).2.length = nindices + 1 := by
  unfold groupCountsA at h
  split at h
  · exact Option.noConfusion h
  · rename_i n hn
    split at h
    · rename_i hc
      injection h with h
      injection h with h1 h2
      subst h1 h2
      exact ⟨by omega, hc.2, hn⟩
    · exact Option.noConfusion h

theorem iotaGroupA_some {E : ResolvedEnvA} {recRef ctorRef : Nat} {g : IotaGroupA}
    (h : iotaGroupA E recRef ctorRef = some g) :
    E.members recRef = some g.recM ∧ g.recM.mclass = .recursorM ∧
      E.members ctorRef = some g.ctorM ∧ g.ctorM.mclass = .constructorM ∧ g.ctorRef = ctorRef ∧
      E.members g.familyRef = some g.famM ∧ g.famM.mclass = .inductiveM ∧
      g.familyRef < ctorRef ∧ ctorRef < recRef ∧
      g.nMinors = recRef - g.familyRef - 1 ∧ g.ctorIdx = ctorRef - g.familyRef - 1 ∧
      g.nparams + 1 + g.nMinors + g.nindices + 1 = piCountA g.recM.mtypeA ∧
      g.nparams + g.nindices = piCountA g.famM.mtypeA := by
  unfold iotaGroupA at h
  split at h
  · rename_i recM ctorM hrec hctor
    split at h
    · rename_i hcls
      split at h
      · rename_i D hD
        split at h
        · rename_i familyRef lsF hhead
          split at h
          · rename_i famM hfam
            split at h
            · rename_i hlay
              split at h
              · rename_i nparams nindices hcnt
                obtain ⟨_, hc2, _⟩ := groupCountsA_some hcnt
                injection h with h
                subst h
                exact ⟨hrec, hcls.1, hctor, hcls.2, rfl, hfam, hlay.1, hlay.2.1, hlay.2.2, rfl, rfl,
                  hc2, (groupCountsA_some hcnt).1⟩
              · exact Option.noConfusion h
            · exact Option.noConfusion h
          · exact Option.noConfusion h
        · exact Option.noConfusion h
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  · exact Option.noConfusion h

/-- the family the copy's ι reads is the head of the recursor type's last domain. -/
theorem iotaGroupA_lastDom {E : ResolvedEnvA} {recRef ctorRef : Nat} {g : IotaGroupA}
    (h : iotaGroupA E recRef ctorRef = some g) :
    ∃ D ls', (piDomsA g.recM.mtypeA).getLast? = some D ∧ (appsSpineA D).1 = .const g.familyRef ls' := by
  unfold iotaGroupA at h
  split at h
  · split at h
    · split at h
      · rename_i D hD
        split at h
        · rename_i familyRef lsF hhead
          split at h
          · split at h
            · split at h
              · injection h with h
                subst h
                exact ⟨D, lsF, hD, hhead⟩
              · exact Option.noConfusion h
            · exact Option.noConfusion h
          · exact Option.noConfusion h
        · exact Option.noConfusion h
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  · exact Option.noConfusion h

/-- a group the concrete ι reads has a constructor: its recursor sits past the family's
    successor (O1-a). -/
theorem recHasCtorA_of_iotaGroupA {E : ResolvedEnvA} {recRef ctorRef : Nat} {g : IotaGroupA}
    (h : iotaGroupA E recRef ctorRef = some g) : recHasCtorA recRef g.recM = true := by
  unfold iotaGroupA at h
  split at h
  · rename_i recM ctorM hrec hctor
    split at h
    · rename_i hcls
      split at h
      · rename_i D hD
        split at h
        · rename_i familyRef lsF hhead
          split at h
          · rename_i famM hfam
            split at h
            · rename_i hlay
              split at h
              · rename_i nparams nindices hcnt
                injection h with h
                subst h
                have h1 := hlay.2.1
                have h2 := hlay.2.2
                show recHasCtorA recRef recM = true
                unfold recHasCtorA
                rw [lastPiDomA_eq, hD]
                show (match (appsSpineA D).1 with
                  | .const f _ => !(decide (recRef = f + 1))
                  | _ => true) = true
                rw [hhead]
                show (!(decide (recRef = familyRef + 1))) = true
                have hne : recRef ≠ familyRef + 1 := by omega
                simp [hne]
              · exact Option.noConfusion h
            · exact Option.noConfusion h
          · exact Option.noConfusion h
        · exact Option.noConfusion h
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  · exact Option.noConfusion h

/-- at a recursor whose group has no constructor the concrete ι reads no group (O1-a). -/
theorem iotaGroupA_none_of_noCtor {E : ResolvedEnvA} {r : Nat} {m : CheckedMemberA}
    (hres : E.members r = some m) (hno : recHasCtorA r m = false) (c : Nat) :
    iotaGroupA E r c = none := by
  cases hg : iotaGroupA E r c with
  | none => rfl
  | some g =>
      exfalso
      have h1 := recHasCtorA_of_iotaGroupA hg
      obtain ⟨hrec, _⟩ := iotaGroupA_some hg
      rw [hres] at hrec
      cases hrec
      rw [hno] at h1
      exact Bool.noConfusion h1

theorem iotaReductA_some {s : RecSpineA} {g : IotaGroupA} {e' : ExprA}
    (h : iotaReductA s g = some e') :
    ∃ c, spineHeadRefA s.major = some c ∧ c = g.ctorRef ∧
      s.preMajor.length + 1 = piCountA g.recM.mtypeA ∧ s.ls.length = g.recM.arity ∧
      (appsSpineA s.major).2.length = piCountA (g.ctorM.normA.getD g.ctorM.mtypeA) ∧
        g.ctorM.arity ≤ s.ls.length := by
  unfold iotaReductA at h
  cases hc : spineHeadRefA s.major with
  | none => rw [hc, Option.none_bind] at h; exact Option.noConfusion h
  | some c =>
      simp only [hc, Option.some_bind] at h
      split at h
      · rename_i hcond
        exact ⟨c, rfl, hcond⟩
      · exact Option.noConfusion h

/-- inversion of the layers. -/
theorem iotaFnA_some {E : ResolvedEnvA} {e e' : ExprA} (h : iotaFnA E e = some e') :
    ∃ s c g, recSpineA e = some s ∧ spineHeadRefA s.major = some c ∧
      iotaGroupA E s.recRef c = some g ∧ iotaReductA s g = some e' := by
  unfold iotaFnA at h
  cases hs : recSpineA e with
  | none => rw [hs, Option.none_bind] at h; exact Option.noConfusion h
  | some s =>
      rw [hs, Option.some_bind] at h
      cases hc : spineHeadRefA s.major with
      | none => rw [hc, Option.none_bind] at h; exact Option.noConfusion h
      | some c =>
          rw [hc, Option.some_bind] at h
          cases hg : iotaGroupA E s.recRef c with
          | none => rw [hg, Option.none_bind] at h; exact Option.noConfusion h
          | some g =>
              rw [hg, Option.some_bind] at h
              exact ⟨s, c, g, rfl, hc, hg, h⟩

/-- the layers, forward. -/
theorem iotaFnA_of_layers {E : ResolvedEnvA} {e : ExprA} {s : RecSpineA} {c : Nat} {g : IotaGroupA}
    (hs : recSpineA e = some s) (hc : spineHeadRefA s.major = some c)
    (hg : iotaGroupA E s.recRef c = some g) : iotaFnA E e = iotaReductA s g := by
  unfold iotaFnA
  rw [hs, Option.some_bind, hc, Option.some_bind, hg, Option.some_bind]

/-- W-1 (b′): whether `e` is a ι redex AT A STRUCT GROUP: `e`'s layers name a group whose recursor is a
    struct group's. There the head step is the struct arm's (`structPosA`, W-1 (e)). -/
def iotaAtStructA (E : ResolvedEnvA) (e : ExprA) : Bool :=
  ((recSpineA e).bind fun s => (spineHeadRefA s.major).bind fun c =>
    (iotaGroupA E s.recRef c).map fun g => structGroupA s.recRef g.recM).getD false

theorem iotaAtStructA_of_layers {E : ResolvedEnvA} {e : ExprA} {s : RecSpineA} {c : Nat} {g : IotaGroupA}
    (hs : recSpineA e = some s) (hc : spineHeadRefA s.major = some c)
    (hg : iotaGroupA E s.recRef c = some g) : iotaAtStructA E e = structGroupA s.recRef g.recM := by
  unfold iotaAtStructA
  rw [hs, Option.some_bind, hc, Option.some_bind, hg]
  rfl

/-- `iotaAtStructA`, read back. -/
theorem iotaAtStructA_true {E : ResolvedEnvA} {e : ExprA} (h : iotaAtStructA E e = true) :
    ∃ s c g, recSpineA e = some s ∧ spineHeadRefA s.major = some c ∧ iotaGroupA E s.recRef c = some g ∧
      structGroupA s.recRef g.recM = true := by
  unfold iotaAtStructA at h
  cases hs : recSpineA e with
  | none => rw [hs] at h; exact Bool.noConfusion h
  | some s =>
      rw [hs, Option.some_bind] at h
      cases hc : spineHeadRefA s.major with
      | none => rw [hc] at h; exact Bool.noConfusion h
      | some c =>
          rw [hc, Option.some_bind] at h
          cases hg : iotaGroupA E s.recRef c with
          | none => rw [hg] at h; exact Bool.noConfusion h
          | some g => rw [hg] at h; exact ⟨s, c, g, rfl, hc, hg, h⟩

/-! ## (3) the head laws -/

/-- the concrete ι fires only on a spine headed by a recursor member of `E`, at the
    recursor's telescope arity. -/
theorem iotaFnA_recHead (E : ResolvedEnvA) : IotaRecHeadA E (iotaIfaceA E) := by
  intro e e' h
  have h' : iotaFnA E e = some e' := h
  obtain ⟨s, c, g, hs, _, hg, hr⟩ := iotaFnA_some h'
  have hsp := recSpineA_some hs
  obtain ⟨hrec, hcls, _⟩ := iotaGroupA_some hg
  obtain ⟨_, _, _, hlen, _⟩ := iotaReductA_some hr
  refine ⟨s.recRef, s.ls, g.recM, ?_, hrec, hcls, ?_⟩
  · rw [hsp]
  · rw [hsp]
    show (s.preMajor ++ [s.major]).length = piCountA g.recM.mtypeA
    rw [List.length_append, List.length_singleton]
    exact hlen

theorem iotaFnA_constHead (E : ResolvedEnvA) : IotaConstHeadA (iotaIfaceA E) :=
  iotaConstHeadA_of_recHead (iotaFnA_recHead E)

/-! ## (5) pins: the Nat group computes -/

def pinNatTyA : ExprA := .const 10 []
def pinNatFamA : CheckedMemberA := ⟨.inductiveM, 0, .sort (.succ .zero), none, 0, none⟩
def pinZeroA : CheckedMemberA := ⟨.constructorM, 0, pinNatTyA, none, 0, some pinNatTyA⟩
def pinSuccA : CheckedMemberA :=
  ⟨.constructorM, 0, .pi pinNatTyA (.succ .zero) pinNatTyA (.succ .zero), none, 0,
    some (.pi pinNatTyA (.succ .zero) pinNatTyA (.succ .zero))⟩
/-- `Π (motive : Nat → Sort 1) (mz : motive zero) (ms : Π (n : Nat), motive n → motive (succ n))
    (t : Nat), motive t` (annotations nominal: the function reads shapes). -/
def pinRecTyNatA : ExprA :=
  .pi (.pi pinNatTyA (.succ .zero) (.sort (.succ .zero)) (.succ (.succ .zero))) (.succ (.succ .zero))
    (.pi (.app (.bvar 0) (.const 11 [])) (.succ .zero)
      (.pi (.pi pinNatTyA (.succ .zero)
          (.pi (.app (.bvar 2) (.bvar 0)) (.succ .zero) (.app (.bvar 3) (.app (.const 12 []) (.bvar 1)))
            (.succ .zero)) (.succ .zero)) (.succ .zero)
        (.pi pinNatTyA (.succ .zero) (.app (.bvar 3) (.bvar 0)) (.succ .zero)) (.succ .zero))
      (.succ .zero))
    (.succ .zero)
def pinNatRecA : CheckedMemberA := ⟨.recursorM, 0, pinRecTyNatA, none, 0, none⟩
def pinNatEnvA : ResolvedEnvA :=
  extendEnvA (extendEnvA (extendEnvA (extendEnvA emptyEnvA 10 pinNatFamA) 11 pinZeroA) 12 pinSuccA)
    13 pinNatRecA
def pinNatRecSpineA (P mz ms t : ExprA) : ExprA :=
  .app (.app (.app (.app (.const 13 []) P) mz) ms) t
def pinMsA : ExprA := .lam (.sort .zero) .zero (.sort .zero)

example : piCountA pinRecTyNatA = 4 := rfl
example : ctorKindsA 10 0 pinSuccA.mtypeA = some [.directRec] := by decide
example : ctorKindsA 10 0 pinZeroA.mtypeA = some [] := by decide
/-- `rec P mz ms zero ⇝ mz`. -/
example : iotaFnA pinNatEnvA (pinNatRecSpineA (.sort .zero) (.sort (.succ .zero)) pinMsA (.const 11 [])) =
    some (.sort (.succ .zero)) := by decide
/-- `rec P mz ms (succ zero) ⇝ ms zero (rec P mz ms zero)`: the recursive call at the field. -/
example : iotaFnA pinNatEnvA
    (pinNatRecSpineA (.sort .zero) (.sort (.succ .zero)) pinMsA (.app (.const 12 []) (.const 11 []))) =
    some (.app (.app pinMsA (.const 11 []))
      (pinNatRecSpineA (.sort .zero) (.sort (.succ .zero)) pinMsA (.const 11 []))) := by decide
/-- a variable major is no redex. -/
example : iotaFnA pinNatEnvA (pinNatRecSpineA (.sort .zero) (.sort (.succ .zero)) pinMsA (.bvar 0)) = none := by
  decide
/-- below the telescope arity nothing fires. -/
example : iotaFnA pinNatEnvA (.app (.app (.app (.const 13 []) (.sort .zero)) (.sort .zero)) (.const 11 [])) =
    none := by decide
/-- the step function takes it at the position, the major first when needed. -/
example : whnfA pinNatEnvA (iotaFnA pinNatEnvA) [] 2
    (pinNatRecSpineA (.sort .zero) (.sort (.succ .zero)) pinMsA
      (.app (.lam pinNatTyA (.succ .zero) (.bvar 0)) (.const 11 []))) = some (.sort (.succ .zero)) := by
  decide

def pinTreeTyA : ExprA := .const 20 []
def pinTreeFamA : CheckedMemberA := ⟨.inductiveM, 0, .sort (.succ .zero), none, 0, none⟩
def pinLeafA : CheckedMemberA := ⟨.constructorM, 0, pinTreeTyA, none, 0, none⟩
/-- `node : (Sort 0 → T) → T`: one field, function-recursive at one inner binder. -/
def pinNodeA : CheckedMemberA :=
  ⟨.constructorM, 0, .pi (.pi (.sort .zero) (.succ .zero) pinTreeTyA (.succ .zero)) (.succ .zero) pinTreeTyA
    (.succ .zero), none, 0, none⟩
/-- `Π (motive : T → Sort 1) (ml : motive leaf) (mn : Π (g : Sort 0 → T), (Π (x : Sort 0), motive (g x)) →
    motive (node g)) (t : T), motive t` (annotations nominal). -/
def pinRecTyTreeA : ExprA :=
  .pi (.pi pinTreeTyA (.succ .zero) (.sort (.succ .zero)) (.succ (.succ .zero))) (.succ (.succ .zero))
    (.pi (.app (.bvar 0) (.const 21 [])) (.succ .zero)
      (.pi
        (.pi (.pi (.sort .zero) (.succ .zero) pinTreeTyA (.succ .zero)) (.succ .zero)
          (.pi (.pi (.sort .zero) (.succ .zero) (.app (.bvar 3) (.app (.bvar 1) (.bvar 0))) (.succ .zero))
            (.succ .zero)
            (.app (.bvar 3) (.app (.const 22 []) (.bvar 1))) (.succ .zero))
          (.succ .zero))
        (.succ .zero)
        (.pi pinTreeTyA (.succ .zero) (.app (.bvar 3) (.bvar 0)) (.succ .zero))
        (.succ .zero))
      (.succ .zero))
    (.succ .zero)
def pinTreeRecA : CheckedMemberA := ⟨.recursorM, 0, pinRecTyTreeA, none, 0, none⟩
def pinTreeEnvA : ResolvedEnvA :=
  extendEnvA (extendEnvA (extendEnvA (extendEnvA emptyEnvA 20 pinTreeFamA) 21 pinLeafA) 22 pinNodeA) 23 pinTreeRecA
/-- `λ _. leaf`. -/
def pinGA : ExprA := .lam (.sort .zero) (.succ .zero) (.const 21 [])

example : ctorShapesA 20 0 pinNodeA.mtypeA = some [.recursive 1] := by decide
example : ctorKindsA 20 0 pinNodeA.mtypeA = none := by decide
/-- `rec P ml mn leaf ⇝ ml`. -/
example : iotaFnA pinTreeEnvA (foldAppsA (.const 23 []) [.sort .zero, .sort (.succ .zero), pinMsA, .const 21 []]) =
    some (.sort (.succ .zero)) := by decide
/-- `rec P ml mn (node g) ⇝ mn g (λ x. rec P ml mn (g x))`: the λ-wrapped call at the function-recursive field. -/
example : iotaFnA pinTreeEnvA
    (foldAppsA (.const 23 []) [.sort .zero, .sort (.succ .zero), pinMsA, .app (.const 22 []) pinGA]) =
    some (foldAppsA pinMsA [pinGA, .lam (.sort .zero) (.succ .zero)
      (foldAppsA (.const 23 []) [.sort .zero, .sort (.succ .zero), pinMsA, .app pinGA (.bvar 0)])]) := by decide

#print axioms recSpineA_some
#print axioms recSpineA_of_spine
#print axioms groupCountsA_some
#print axioms recHasCtorA_of_iotaGroupA
#print axioms iotaGroupA_none_of_noCtor
#print axioms iotaGroupA_some
#print axioms iotaGroupA_lastDom
#print axioms iotaReductA_some
#print axioms iotaFnA_some
#print axioms iotaFnA_of_layers
#print axioms iotaAtStructA_of_layers
#print axioms iotaAtStructA_true
#print axioms iotaFnA_recHead
#print axioms iotaFnA_constHead

end Rcic.Declarative.Ann
