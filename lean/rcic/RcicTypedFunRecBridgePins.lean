import rcic.RcicTypedFunRecFieldPins
import rcic.RcicTypedFunRecIotaPins

/-!
# R-NoFunRec S5 — the bridge flip: `FieldA.eraseX`, the NoFun-discharged X-compat
theorems, and the function-IH-survives pins at W

cc's S5 GO (#6470 landed via Lean batch 3): S4's `FieldTX` union gets its bridge.
`FieldA.eraseX` maps `.frec` to `FieldTX.frec` — the field's Π, inner binders and
indices survive erasure componentwise (`uB` was carried for exactly this shape
parity). The sealed `FieldA.erase` (`.frec ↦ .drec`), `FieldT` and every sealed
statement are UNTOUCHED: S3's collapse canaries (`wFrecA_erase_collapses`,
`wCtorTypeT_collapse_distinct`) stay true, sealed, byte-identical.

- `erase_ctorFieldsAX` / `erase_ctorTypeAX` / `erase_minorFieldsAX` /
  `erase_minorTyAX` are S3's `erase_ctorFieldsA` / `erase_ctorTypeA` /
  `erase_minorFieldsA` / `erase_minorTyA` with the `NoFun` premise DISCHARGED —
  they hold for EVERY field list: the X matchers carry the `.frec` arm, so the
  `(hnf _ _).elim` vacuity arms become real computation — and the target read
  through `FieldTX` (`ctorFieldsTX` / `ctorTypeTX` / `minorFieldsTX` /
  `minorTyTX`, the last two defined here mirroring `ctorTypeT` / `minorTyT`).
- Positive counterparts at W: `wFrecA_eraseX_keeps` (the frec field stays `.frec`),
  `wCtorTypeTX_keeps` (the X-built T-group IS sup's stored type — the Π over
  `b : Nat`, the function IH's domain, survives), `wSupTypeA_eraseX` (the full
  flip at sup), and `wMinorTyA_eraseX` (the function IH survives erasure at W:
  the Ann-built minor erases to S1's `wMinorTy`, whose third Π is `wCall`'s
  type).

`closure_claim` stays 0.
-/

namespace Rcic.Declarative

/-! ## (1) the X group-builder wrappers (mirrors of `ctorTypeT` / `minorTyT`) -/

/-- the constructor's type BUILT from its X view: `ctorTypeT`'s arm VERBATIM, with the
    fields' telescope read through `ctorFieldsTX` — so a `.frec` field's Π lands in the
    stored type. `FieldT` and `ctorTypeT` stay byte-identical. -/
def ctorTypeTX (f : Nat) (ls : List Level) (mirrors : List (Expr Nat × Level))
    (fields : List FieldTX) (res : List (Expr Nat)) : Expr Nat :=
  policyPi (mirrors.map Prod.fst)
    (ctorFieldsTX f ls (policyLocals mirrors.length) SubstT.id fields res)

/-- `ctorTypeTX` on an all-`.old` list IS `ctorTypeT` — the wrapper delegates (S4's
    `ctorFieldsTX_olds` under the identical `policyPi`). -/
theorem ctorTypeTX_olds (f : Nat) (ls : List Level) (mirrors : List (Expr Nat × Level))
    (fs : List FieldT) (res : List (Expr Nat)) :
    ctorTypeTX f ls mirrors (fs.map FieldTX.old) res = ctorTypeT f ls mirrors fs res := by
  simp only [ctorTypeTX, ctorTypeT,
    ctorFieldsTX_olds f ls (policyLocals mirrors.length) SubstT.id fs res]

/-- a constructor's minor data over the union field list (mirror of `MinorDataT`). -/
abbrev MinorDataTX : Type := Nat × List FieldTX × List (Expr Nat)

/-- a constructor's minor premise type over the union list: `minorTyT`'s arm VERBATIM,
    with the fields' minor telescope read through `minorFieldsTX` — so a `.frec` field's
    function IH (`frecIHT`) lands in the minor. `minorTyT` stays byte-identical. -/
def minorTyTX (f : Nat) (ls : List Level) (np : Nat) (cd : MinorDataTX) : Expr Nat :=
  minorFieldsTX f cd.1 ls ((policyLocals np).map (lift 0 1)) (.bvar 0) [] SubstT.id.shift1
    cd.2.1 cd.2.2

/-- `minorTyTX` on an all-`.old` minor datum IS `minorTyT` (S4's `minorFieldsTX_olds`
    under the identical arguments). -/
theorem minorTyTX_olds (f : Nat) (ls : List Level) (np : Nat)
    (cd : Nat × List FieldT × List (Expr Nat)) :
    minorTyTX f ls np (cd.1, cd.2.1.map FieldTX.old, cd.2.2) = minorTyT f ls np cd := by
  simp only [minorTyTX, minorTyT,
    minorFieldsTX_olds f cd.1 ls ((policyLocals np).map (lift 0 1)) (.bvar 0) []
      SubstT.id.shift1 cd.2.1 cd.2.2]

/-! ## (2) the flip: `FieldA.eraseX` and the NoFun-discharged X-compat theorems -/

namespace Ann

/-- the erasure that KEEPS a function-recursive field (the S5 flip): `.frec` maps to
    `FieldTX.frec`, componentwise on the field's Π domain, inner binders and indices
    (`uB` was carried on both sides for exactly this shape parity — S4,
    `RcicTypedFunRecFieldPins.lean`). The sealed `FieldA.erase` (`.frec ↦ .drec`) is
    UNTOUCHED; this is the parallel route (cc condition 3 on #6391). -/
def FieldA.eraseX : FieldA → FieldTX
  | .plain D u => .old (.plain (Ann.erase D) u)
  | .drec idx => .old (.drec (idx.map Ann.erase))
  | .drecD D idx => .old (.drecD (Ann.erase D) (idx.map Ann.erase))
  | .frec B uB Bs idx =>
      .frec (Ann.erase B) uB (Bs.map fun p => (Ann.erase p.1, p.2)) (idx.map Ann.erase)

/-- on a non-function-recursive field, the X-erasure IS the sealed erasure wrapped
    `.old` — the two routes agree wherever the old theorem applied. -/
theorem FieldA.eraseX_old : (x : FieldA) → x.NoFun → x.eraseX = .old x.erase
  | .plain _ _, _ => rfl
  | .drec _, _ => rfl
  | .drecD _ _, _ => rfl
  | .frec _ _ _ _, h => h.elim

/-- the frec domain erases into S4's plain builder: `frecDomA`'s Π-telescope, level
    annotations dropped, under the erased substitution (S4's `frecDomT`). -/
theorem erase_frecDomA (f : Nat) (ls : List Level) (w : Level) :
    (pl : List ExprA) → (σ : SubstA) → (ds : List (ExprA × Level)) → (idx : List ExprA) →
      erase (frecDomA f ls w pl σ ds idx).1 =
        frecDomT f ls (pl.map erase) (eraseSubst σ) (ds.map fun p => (erase p.1, p.2))
          (idx.map erase)
  | pl, σ, [], idx => by
      simp only [frecDomA, frecDomT, erase_foldAppsA, erase, List.map_append,
        map_erase_substA]
  | pl, σ, (D, _) :: ds, idx => by
      simp only [frecDomA, frecDomT, erase, erase_substA,
        erase_frecDomA f ls w (pl.map (liftA 0 1)) σ.up ds idx, map_erase_liftA,
        eraseSubst_up]

/-- de Bruijn variable lists erase componentwise (`erase` on `.bvar` is the identity). -/
theorem erase_map_bvarA : (ns : List Nat) → (ns.map ExprA.bvar).map erase = ns.map Expr.bvar
  | [] => rfl
  | _ :: ns => by simp only [List.map_cons, erase, erase_map_bvarA ns]

/-- the frec function IH erases into S4's plain builder: `frecIHA` minus the level
    annotations (`frecIHT`) — the IH's `Π (B :: Bs), mot idx (x ys)` survives erasure
    VERBATIM. -/
theorem erase_frecIHA (wM : Level) :
    (mot : ExprA) → (j : Nat) → (σ : SubstA) → (ds : List (ExprA × Level)) →
      (idx : List ExprA) → (m : Nat) →
      erase (frecIHA wM mot j σ ds idx m).1 =
        frecIHT (erase mot) j (eraseSubst σ) (ds.map fun p => (erase p.1, p.2))
          (idx.map erase) m
  | mot, j, σ, [], idx, m => by
      simp only [frecIHA, frecIHT, erase_foldAppsA, erase, List.map_append, map_erase_substA,
        List.map_cons, List.map_nil, erase_map_bvarA]
  | mot, j, σ, (D, _) :: ds, idx, m => by
      simp only [frecIHA, frecIHT, erase, erase_substA, erase_liftA,
        erase_frecIHA wM (liftA 0 1 mot) (j + 1) σ.up ds idx m, eraseSubst_up]

/-- S3's `erase_ctorFieldsA` with the `NoFun` premise DISCHARGED and the target read
    through `FieldTX`: the theorem holds for EVERY field list — the `.frec` arm is real
    computation now (the field's Π lands via `erase_frecDomA`), not the `(hnf _ _).elim`
    vacuity. -/
theorem erase_ctorFieldsAX (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (σ : SubstA) →
      erase (ctorFieldsA f ls w pl σ fs res).1 =
        ctorFieldsTX f ls (pl.map erase) (eraseSubst σ) (fs.map FieldA.eraseX)
          (res.map erase)
  | [], pl, σ => by
      simp only [ctorFieldsA, List.map_nil, ctorFieldsTX, erase_foldAppsA, erase,
        List.map_append, map_erase_substA]
  | .frec B uB Bs idx :: fs, pl, σ => by
      simp only [ctorFieldsA, List.map_cons, FieldA.eraseX, ctorFieldsTX, erase,
        erase_substA, erase_frecDomA, frecDomT, erase_ctorFieldsAX f ls w res fs,
        map_erase_liftA, eraseSubst_shift1, eraseSubst_up]
  | .drecD D idx :: fs, pl, σ => by
      simp only [ctorFieldsA, List.map_cons, FieldA.eraseX, ctorFieldsTX, erase,
        erase_substA, erase_ctorFieldsAX f ls w res fs, map_erase_liftA, eraseSubst_shift1]
  | .plain D u :: fs, pl, σ => by
      simp only [ctorFieldsA, List.map_cons, FieldA.eraseX, ctorFieldsTX, erase,
        erase_substA, erase_ctorFieldsAX f ls w res fs, map_erase_liftA, eraseSubst_up]
  | .drec idx :: fs, pl, σ => by
      simp only [ctorFieldsA, List.map_cons, FieldA.eraseX, ctorFieldsTX, erase,
        erase_foldAppsA, List.map_append, map_erase_substA,
        erase_ctorFieldsAX f ls w res fs, map_erase_liftA, eraseSubst_shift1]

/-- S3's `erase_ctorTypeA` with the `NoFun` premise DISCHARGED, targeting `ctorTypeTX`:
    the constructor's stored type erases to the X-built one for EVERY field list. -/
theorem erase_ctorTypeAX (f : Nat) (ls : List Level) (w : Level)
    (mirrors : List (ExprA × Level)) (fields : List FieldA) (res : List ExprA) :
    erase (ctorTypeA f ls w mirrors fields res) =
      ctorTypeTX f ls (mirrors.map fun d => (erase d.1, d.2)) (fields.map FieldA.eraseX)
        (res.map erase) := by
  simp only [ctorTypeA, ctorTypeTX, erase_piTelA,
    erase_ctorFieldsAX f ls w res fields, erase_paramLocalsA, eraseSubst_id, List.map_map,
    List.length_map]
  rfl

/-- S3's `erase_minorFieldsA` with the `NoFun` premise DISCHARGED and the target read
    through `minorFieldsTX`: the minor's telescope erases for EVERY field list — the
    `.frec` arm lands the field's Π AND the function IH (`erase_frecIHA`), then the
    rest. -/
theorem erase_minorFieldsAX (f c : Nat) (ls : List Level) (wF wM : Level)
    (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (mot : ExprA) → (fl : List ExprA) →
      (σ : SubstA) →
      erase (minorFieldsA f c ls wF wM pl mot fl σ fs res).1 =
        minorFieldsTX f c ls (pl.map erase) (erase mot) (fl.map erase) (eraseSubst σ)
          (fs.map FieldA.eraseX) (res.map erase)
  | [], pl, mot, fl, σ => by
      simp only [minorFieldsA, List.map_nil, minorFieldsTX, erase_foldAppsA, erase,
        List.map_append, map_erase_substA, List.map_cons]
  | .frec B uB Bs idx :: fs, pl, mot, fl, σ => by
      simp only [minorFieldsA, List.map_cons, FieldA.eraseX, minorFieldsTX, erase,
        erase_liftA, erase_substA, erase_frecDomA, frecDomT, erase_frecIHA, frecIHT,
        erase_minorFieldsAX f c ls wF wM res fs, map_erase_liftA, List.map_append,
        List.map_cons, List.map_nil, eraseSubst_shift1, eraseSubst_up, List.length_map]
  | .drecD D idx :: fs, pl, mot, fl, σ => by
      simp only [minorFieldsA, List.map_cons, FieldA.eraseX, minorFieldsTX, erase,
        erase_substA, erase_foldAppsA, List.map_append, map_erase_substA,
        erase_minorFieldsAX f c ls wF wM res fs, map_erase_liftA, eraseSubst_shift1,
        erase_liftA, List.map_cons, List.map_nil]
  | .plain D u :: fs, pl, mot, fl, σ => by
      simp only [minorFieldsA, List.map_cons, FieldA.eraseX, minorFieldsTX, erase,
        erase_substA, erase_minorFieldsAX f c ls wF wM res fs, map_erase_liftA,
        eraseSubst_up, erase_liftA, List.map_append, List.map_cons, List.map_nil]
  | .drec idx :: fs, pl, mot, fl, σ => by
      simp only [minorFieldsA, List.map_cons, FieldA.eraseX, minorFieldsTX, erase,
        erase_foldAppsA, List.map_append, map_erase_substA,
        erase_minorFieldsAX f c ls wF wM res fs, map_erase_liftA, eraseSubst_shift1,
        erase_liftA, List.map_cons, List.map_nil]

/-- a minor datum's X-erasure (mirror of `MinorDataA.erase`). -/
def MinorDataA.eraseX (cd : MinorDataA) : MinorDataTX :=
  (cd.1, cd.2.1.map FieldA.eraseX, cd.2.2.map Ann.erase)

/-- S3's `erase_minorTyA` with the `NoFun` premise DISCHARGED, targeting `minorTyTX`. -/
theorem erase_minorTyAX (f : Nat) (ls : List Level) (wF wM : Level) (np : Nat)
    (cd : MinorDataA) :
    erase (minorTyA f ls wF wM np cd).1 = minorTyTX f ls np cd.eraseX := by
  simp only [minorTyA, minorTyTX, erase_minorFieldsAX f cd.1 ls wF wM cd.2.2 cd.2.1,
    map_erase_liftA, erase_paramLocalsA, MinorDataA.eraseX, eraseSubst_shift1,
    eraseSubst_id]
  rfl

end Ann

/-! ## (3) the positive counterparts at W (S3's collapse canaries stay true, sealed) -/

/-- sup's plain field, X-read (sibling of S4's `wFieldFrecTX`). -/
def wFieldPlainTX : FieldTX := .old (.plain wFieldA (.succ .zero))

/-- the plain field's X-erasure is the `.old` wrap. -/
theorem wPlainA_eraseX : Ann.FieldA.eraseX wFieldPlainA = wFieldPlainTX := rfl

/-- POSITIVE counterpart of S3's `wFrecA_erase_collapses` (which stays true, sealed):
    the X-erasure of sup's frec field KEEPS it — `.frec` maps to `FieldTX.frec` (S4's
    `wFieldFrecTX`); the Π over `b : Nat` and its inner binder survive componentwise. -/
theorem wFrecA_eraseX_keeps : Ann.FieldA.eraseX wFieldFrecA = wFieldFrecTX := rfl

/-- POSITIVE counterpart of S3's `wCtorTypeT_collapse_distinct` (which stays true,
    sealed): the T-group built from the X-erased fields IS sup's stored plain type —
    the Π over `b : Nat` (the function IH's domain) survives the bridge. -/
theorem wCtorTypeTX_keeps :
    ctorTypeTX 4 [] [] [Ann.FieldA.eraseX wFieldPlainA, Ann.FieldA.eraseX wFieldFrecA] [] =
      wSupMember.mtype := rfl

/-- the bridge flip at sup, full: the Ann-built ctor type erases to the TX-built one —
    `erase_ctorTypeA`'s `NoFun` premise is DISCHARGED at a group whose second field is
    `.frec`. With `wCtorTypeTX_keeps`, this is S3's `wSupTypeA_erase` re-derived through
    the honest (Π-keeping) route. -/
theorem wSupTypeA_eraseX :
    Ann.erase (Ann.ctorTypeA 4 [] (.succ .zero) [] [wFieldPlainA, wFieldFrecA] []) =
      ctorTypeTX 4 [] [] [Ann.FieldA.eraseX wFieldPlainA, Ann.FieldA.eraseX wFieldFrecA] [] :=
  Ann.erase_ctorTypeAX 4 [] (.succ .zero) [] [wFieldPlainA, wFieldFrecA] []

/-- the X-built minor at W IS S1's spelled `wMinorTy` (S4's `wSupMinorFieldsTX` under
    the `minorTyTX` wrapper): the function IH `fun b => mot (f b)` is the third Π. -/
theorem wMinorTyTX : minorTyTX 4 [] 0 (5, [wFieldPlainTX, wFieldFrecTX], []) = wMinorTy :=
  rfl

/-- the function IH survives erasure at W: the Ann-built minor (with the frec field)
    erases — no `NoFun` premise — to S1's `wMinorTy`, whose third Π is the function-IH
    type `fun b => mot (f b)` (`wCall`'s type, 05 §14's reduct argument). -/
theorem wMinorTyA_eraseX :
    Ann.erase (Ann.minorTyA 4 [] (.succ .zero) (.param 0) 0
      (5, [wFieldPlainA, wFieldFrecA], [])).1 = wMinorTy := by
  rw [Ann.erase_minorTyAX,
    show Ann.MinorDataA.eraseX (5, [wFieldPlainA, wFieldFrecA], []) =
      (5, [wFieldPlainTX, wFieldFrecTX], []) from rfl, wMinorTyTX]

end Rcic.Declarative

#print axioms Rcic.Declarative.ctorTypeTX
#print axioms Rcic.Declarative.ctorTypeTX_olds
#print axioms Rcic.Declarative.minorTyTX
#print axioms Rcic.Declarative.minorTyTX_olds
#print axioms Rcic.Declarative.Ann.FieldA.eraseX
#print axioms Rcic.Declarative.Ann.FieldA.eraseX_old
#print axioms Rcic.Declarative.Ann.erase_map_bvarA
#print axioms Rcic.Declarative.Ann.erase_frecDomA
#print axioms Rcic.Declarative.Ann.erase_frecIHA
#print axioms Rcic.Declarative.Ann.erase_ctorFieldsAX
#print axioms Rcic.Declarative.Ann.erase_ctorTypeAX
#print axioms Rcic.Declarative.Ann.erase_minorFieldsAX
#print axioms Rcic.Declarative.Ann.erase_minorTyAX
#print axioms Rcic.Declarative.wFieldPlainTX
#print axioms Rcic.Declarative.wPlainA_eraseX
#print axioms Rcic.Declarative.wFrecA_eraseX_keeps
#print axioms Rcic.Declarative.wCtorTypeTX_keeps
#print axioms Rcic.Declarative.wSupTypeA_eraseX
#print axioms Rcic.Declarative.wMinorTyTX
#print axioms Rcic.Declarative.wMinorTyA_eraseX
