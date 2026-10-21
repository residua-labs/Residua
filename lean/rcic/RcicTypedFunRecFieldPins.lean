import rcic.RcicTypedGroup
import rcic.RcicTypedFunRecPins

/-!
# R-NoFunRec S4 — `FieldTX`: the union field list that carries a function-recursive field

cc's ruling on the S4 plan (#6446): appending a `frec` constructor to the sealed `FieldT` is
NOT additive — every definition that matches on `FieldT` (`ctorFieldsT`, `minorFieldsT`,
`plainCtxT`, …) would need a new arm and every statement quantified over `FieldT` silently
changes meaning. S4 therefore takes S2's option-(b) shape: a NEW union type. `FieldTX.old`
wraps `FieldT` (whose matchers it mirrors arm-by-arm), `FieldTX.frec` carries a
function-recursive field. `FieldT` and every file that cases on it stay BYTE-IDENTICAL —
`RcicTypedGroup.lean` is not touched at all; everything here is new.

Measured on this branch (two searches, evidence in the S4 PR comment): 0 sealed names match
on or quantify over `FieldT`; the FieldT-casing definitions live in exactly 3 files
(`RcicTypedGroup`, `RcicTypedScopeCheck`, `RcicAnnEnvBridgeGroup`), none sealed.

The frec builders are the Ann mirrors minus the universe annotations (`frecDomA`,
`RcicAnnGroup.lean:215`; `frecIHA`, `RcicAnnRecView.lean:41`): the plain `Expr` Π carries
no levels. `ctorFieldsTX`/`minorFieldsTX` mirror `ctorFieldsT`/`minorFieldsT`
(`RcicTypedGroup.lean:88/:110`) verbatim on `.old`, and mirror `ctorFieldsA`/`minorFieldsA`'s
`.frec` arms (`RcicAnnGroup.lean:235`, `RcicAnnRecView.lean:77`) on `.frec` — the stored
constructor type keeps the field's Π VERBATIM, and the minor gets the function IH
`Π (B :: Bs), mot idx (x ys)` (`frecIHT`). The delegation lemmas prove the `.old` arms ARE
`ctorFieldsT`/`minorFieldsT` on all-`.old` lists. S5's bridge targets `FieldTX`.

Wall-break pins on S1's W fixture: the union matchers at `sup`'s fields equal the stored
plain type and S1's spelled `wMinorTy` — the function IH `fun b => mot (f b)` on the plain
side. The legacy side is untouched: `RecKind`, `analyzeField` and `IotaWitness` are not
edited (that is what S5+ consumes).
-/

namespace Rcic.Declarative

/-! ## (1) the union type -/

/-- a constructor field list that can carry a function-recursive field WITHOUT touching the
    sealed `FieldT` (cc ruling on #6446, S2's option-(b) shape): `.old` wraps a `FieldT`
    field, `.frec` is a function-recursive field — `B : Sort uB`, then `Bs`, then the
    indices — verbatim mirror of `FieldA.frec` (`RcicAnnGroup.lean:92`). `uB` is carried for
    shape parity with the Ann side so S5's erase is the identity on the field. -/
inductive FieldTX : Type
  | old (f : FieldT)
  | frec (B : Expr Nat) (uB : Level) (Bs : List (Expr Nat × Level)) (idx : List (Expr Nat))

/-! ## (2) the frec builders (Ann mirrors minus the level annotations) -/

/-- a function-recursive field's domain: the inner binders under the plain substitution (each
    under the earlier ones), then `F ls (pl ++ idx)` at the parameter locals carried past
    them. Mirror of `frecDomA` (`RcicAnnGroup.lean:215`) minus the level pair. -/
def frecDomT (f : Nat) (ls : List Level) :
    List (Expr Nat) → SubstT → List (Expr Nat × Level) → List (Expr Nat) → Expr Nat
  | pl, σ, [], idx => foldApps (.const f ls) (pl ++ idx.map (substT σ))
  | pl, σ, (D, _) :: ds, idx =>
      .pi (substT σ D) (frecDomT f ls (pl.map (lift 0 1)) σ.up ds idx)

/-- a function-recursive field's induction hypothesis, in the minor's context right after the
    field `x` (the variable `j` binders up): the inner binders under the plain substitution,
    then the motive at the indices and at `x` applied to the `m` inner variables. Mirror of
    `frecIHA` (`RcicAnnRecView.lean:41`) minus the level pair. -/
def frecIHT : Expr Nat → Nat → SubstT → List (Expr Nat × Level) → List (Expr Nat) → Nat →
    Expr Nat
  | mot, j, σ, [], idx, m =>
      foldApps mot (idx.map (substT σ) ++ [foldApps (.bvar j) ((List.range m).reverse.map Expr.bvar)])
  | mot, j, σ, (D, _) :: ds, idx, m =>
      .pi (substT σ D) (frecIHT (lift 0 1 mot) (j + 1) σ.up ds idx m)

/-! ## (3) the X matchers: `.old` arms mirror the sealed ones VERBATIM, `.frec` arms mirror
    the Ann `.frec` arms minus the levels -/

/-- the fields' telescope over the union list: on `.old`, `ctorFieldsT`'s arm VERBATIM (the
    whole-list delegation is `ctorFieldsTX_olds` below); on `.frec`, the field's Π kept
    VERBATIM (`frecDomT`) and the recursion at `σ.shift1` — mirror of `ctorFieldsA`'s `.frec`
    arm (`RcicAnnGroup.lean:235`). -/
def ctorFieldsTX (f : Nat) (ls : List Level) :
    List (Expr Nat) → SubstT → List FieldTX → List (Expr Nat) → Expr Nat
  | pl, σ, [], res => foldApps (.const f ls) (pl ++ res.map (substT σ))
  | pl, σ, .old (.plain D _) :: fs, res =>
      .pi (substT σ D) (ctorFieldsTX f ls (pl.map (lift 0 1)) σ.up fs res)
  | pl, σ, .old (.drec idx) :: fs, res =>
      .pi (foldApps (.const f ls) (pl ++ idx.map (substT σ)))
        (ctorFieldsTX f ls (pl.map (lift 0 1)) σ.shift1 fs res)
  | pl, σ, .old (.drecD D _) :: fs, res =>
      .pi (substT σ D) (ctorFieldsTX f ls (pl.map (lift 0 1)) σ.shift1 fs res)
  | pl, σ, .frec B uB Bs idx :: fs, res =>
      .pi (frecDomT f ls pl σ ((B, uB) :: Bs) idx)
        (ctorFieldsTX f ls (pl.map (lift 0 1)) σ.shift1 fs res)

/-- a minor premise's fields over the union list: on `.old`, `minorFieldsT`'s arm VERBATIM
    (whole-list delegation `minorFieldsTX_olds` below); on `.frec`, the field's Π, then the
    function IH `Π (B :: Bs), mot idx (x ys)` (`frecIHT`), then the rest — mirror of
    `minorFieldsA`'s `.frec` arm (`RcicAnnRecView.lean:77`). The Π IH landing in the minor is
    the whole point of S4. -/
def minorFieldsTX (f c : Nat) (ls : List Level) :
    List (Expr Nat) → Expr Nat → List (Expr Nat) → SubstT → List FieldTX → List (Expr Nat) →
    Expr Nat
  | pl, mot, fl, σ, [], res =>
      foldApps mot (res.map (substT σ) ++ [foldApps (.const c ls) (pl ++ fl)])
  | pl, mot, fl, σ, .old (.plain D _) :: fs, res =>
      .pi (substT σ D)
        (minorFieldsTX f c ls (pl.map (lift 0 1)) (lift 0 1 mot) (fl.map (lift 0 1) ++ [.bvar 0])
          σ.up fs res)
  | pl, mot, fl, σ, .old (.drec idx) :: fs, res =>
      .pi (foldApps (.const f ls) (pl ++ idx.map (substT σ)))
        (.pi (foldApps (lift 0 1 mot) ((idx.map (substT σ)).map (lift 0 1) ++ [.bvar 0]))
          (minorFieldsTX f c ls (pl.map (lift 0 2)) (lift 0 2 mot)
            (fl.map (lift 0 2) ++ [.bvar 1]) σ.shift1.shift1 fs res))
  | pl, mot, fl, σ, .old (.drecD D idx) :: fs, res =>
      .pi (substT σ D)
        (.pi (foldApps (lift 0 1 mot) ((idx.map (substT σ)).map (lift 0 1) ++ [.bvar 0]))
          (minorFieldsTX f c ls (pl.map (lift 0 2)) (lift 0 2 mot)
            (fl.map (lift 0 2) ++ [.bvar 1]) σ.shift1.shift1 fs res))
  | pl, mot, fl, σ, .frec B uB Bs idx :: fs, res =>
      let d := frecDomT f ls pl σ ((B, uB) :: Bs) idx
      let ih := frecIHT (lift 0 1 mot) 0 σ.shift1 ((B, uB) :: Bs) idx (Bs.length + 1)
      .pi d (.pi ih
        (minorFieldsTX f c ls (pl.map (lift 0 2)) (lift 0 2 mot)
          (fl.map (lift 0 2) ++ [.bvar 1]) σ.shift1.shift1 fs res))

/-! ## (4) delegation: on all-`.old` lists the X matchers ARE the sealed ones -/

/-- `ctorFieldsTX` on an all-`.old` list IS `ctorFieldsT` — the `.old` arms delegate. This is
    the lemma cc's ruling asks for: a group read the old way computes to the same stored type
    through the union, so sealing `ctorFieldsT` still pins `ctorFieldsTX`'s `.old` behavior. -/
theorem ctorFieldsTX_olds (f : Nat) (ls : List Level) :
    (pl : List (Expr Nat)) → (σ : SubstT) → (fs : List FieldT) → (res : List (Expr Nat)) →
    ctorFieldsTX f ls pl σ (fs.map FieldTX.old) res = ctorFieldsT f ls pl σ fs res
  | pl, σ, [], res => rfl
  | pl, σ, .plain D _ :: fs, res => by
      simp only [List.map_cons, ctorFieldsTX, ctorFieldsT,
        ctorFieldsTX_olds f ls (pl.map (lift 0 1)) σ.up fs res]
  | pl, σ, .drec idx :: fs, res => by
      simp only [List.map_cons, ctorFieldsTX, ctorFieldsT,
        ctorFieldsTX_olds f ls (pl.map (lift 0 1)) σ.shift1 fs res]
  | pl, σ, .drecD D _ :: fs, res => by
      simp only [List.map_cons, ctorFieldsTX, ctorFieldsT,
        ctorFieldsTX_olds f ls (pl.map (lift 0 1)) σ.shift1 fs res]

/-- `minorFieldsTX` on an all-`.old` list IS `minorFieldsT` — same delegation for the minor. -/
theorem minorFieldsTX_olds (f c : Nat) (ls : List Level) :
    (pl : List (Expr Nat)) → (mot : Expr Nat) → (fl : List (Expr Nat)) → (σ : SubstT) →
    (fs : List FieldT) → (res : List (Expr Nat)) →
    minorFieldsTX f c ls pl mot fl σ (fs.map FieldTX.old) res =
      minorFieldsT f c ls pl mot fl σ fs res
  | pl, mot, fl, σ, [], res => rfl
  | pl, mot, fl, σ, .plain D _ :: fs, res => by
      simp only [List.map_cons, minorFieldsTX, minorFieldsT,
        minorFieldsTX_olds f c ls (pl.map (lift 0 1)) (lift 0 1 mot)
          (fl.map (lift 0 1) ++ [.bvar 0]) σ.up fs res]
  | pl, mot, fl, σ, .drec idx :: fs, res => by
      simp only [List.map_cons, minorFieldsTX, minorFieldsT,
        minorFieldsTX_olds f c ls (pl.map (lift 0 2)) (lift 0 2 mot)
          (fl.map (lift 0 2) ++ [.bvar 1]) σ.shift1.shift1 fs res]
  | pl, mot, fl, σ, .drecD D _ :: fs, res => by
      simp only [List.map_cons, minorFieldsTX, minorFieldsT,
        minorFieldsTX_olds f c ls (pl.map (lift 0 2)) (lift 0 2 mot)
          (fl.map (lift 0 2) ++ [.bvar 1]) σ.shift1.shift1 fs res]

/-! ## (5) the wall-break pins on S1's W fixture -/

/-- `sup`'s function-recursive field on the union side: first inner binder `Nat` at
    `Sort 1`, none after, no indices — the plain reading of `wFieldF`'s Π telescope. -/
def wFieldFrecTX : FieldTX := .frec wFieldA (.succ .zero) [] []

/-- the union matcher at `sup`'s fields IS the stored plain type `.pi wFieldA
    (.pi wFieldF (.const 4 []))`: the frec field's domain is `wFieldF` VERBATIM — the Π is
    kept, not collapsed to the family application (the negation of the `.frec ↦ .drec`
    collapse S3 measures on the Ann side). -/
theorem wSupCtorFieldsTX :
    ctorFieldsTX 4 [] [] SubstT.id
      [FieldTX.old (.plain wFieldA (.succ .zero)), wFieldFrecTX] [] =
      .pi wFieldA (.pi wFieldF (.const 4 [])) := rfl

/-- the union matcher's minor at `sup` IS S1's spelled `wMinorTy`: after the fields
    `a : Nat` and `f : Π (b : Nat), W` comes the function IH `Π (b : Nat), mot (f b)`
    (`fun b => mot (f b)`, `frecIHT`) VERBATIM, then the conclusion `mot (sup a f)`. The
    function IH landing in the plain minor is the S4 wall-break witness. -/
theorem wSupMinorFieldsTX :
    minorFieldsTX 4 5 [] [] (.bvar 0) [] SubstT.id.shift1
      [FieldTX.old (.plain wFieldA (.succ .zero)), wFieldFrecTX] [] = wMinorTy := rfl

/-! ## (6) the equation lemmas as the S5 surface -/

theorem frecDomT_base (f : Nat) (ls : List Level) (pl : List (Expr Nat)) (σ : SubstT)
    (idx : List (Expr Nat)) :
    frecDomT f ls pl σ [] idx = foldApps (.const f ls) (pl ++ idx.map (substT σ)) := rfl

theorem frecDomT_step (f : Nat) (ls : List Level) (pl : List (Expr Nat)) (σ : SubstT)
    (D : Expr Nat) (u : Level) (ds : List (Expr Nat × Level)) (idx : List (Expr Nat)) :
    frecDomT f ls pl σ ((D, u) :: ds) idx =
      .pi (substT σ D) (frecDomT f ls (pl.map (lift 0 1)) σ.up ds idx) := rfl

theorem frecIHT_base (mot : Expr Nat) (j : Nat) (σ : SubstT) (idx : List (Expr Nat))
    (m : Nat) :
    frecIHT mot j σ [] idx m =
      foldApps mot
        (idx.map (substT σ) ++ [foldApps (.bvar j) ((List.range m).reverse.map Expr.bvar)]) :=
    rfl

theorem frecIHT_step (mot : Expr Nat) (j : Nat) (σ : SubstT) (D : Expr Nat) (u : Level)
    (ds : List (Expr Nat × Level)) (idx : List (Expr Nat)) (m : Nat) :
    frecIHT mot j σ ((D, u) :: ds) idx m =
      .pi (substT σ D) (frecIHT (lift 0 1 mot) (j + 1) σ.up ds idx m) := rfl

end Rcic.Declarative

#print axioms Rcic.Declarative.ctorFieldsTX_olds
#print axioms Rcic.Declarative.minorFieldsTX_olds
#print axioms Rcic.Declarative.wSupCtorFieldsTX
#print axioms Rcic.Declarative.wSupMinorFieldsTX
#print axioms Rcic.Declarative.frecDomT_base
#print axioms Rcic.Declarative.frecDomT_step
#print axioms Rcic.Declarative.frecIHT_base
#print axioms Rcic.Declarative.frecIHT_step
