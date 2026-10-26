import rcic.RcicF3KTWBig
import rcic.RcicF3FamLim
import rcic.RcicF3RecCore
import rcic.RcicF3Ctor

/-!
# F3 S7 KT-2b-3c-3a: the R-CIC semantics of a constructor telescope as a `Sem`

The R-CIC semantics of a constructor telescope as a `Sem` (base table, truncated
plain fields, sentinel-coded result tuples); `TypeFib` read as truncated fits.

`kindOf`/`kindsOf` read field kinds off syntax (plain / direct / fn from `pi` and
`occursConst`); `argsFitF` says a recursive occurrence's arguments fit the family's
telescope; `recTupAt` is the sentinel-coded index tuple (`{∅}` when the arguments
do not fit); `resTupF` the result-index tuple of a data value.  `semF` packages
`resTupF`/`nonrecOkF`/`recTupF`/`domBigF` as a `Sem.{4}`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v w T

namespace PSet

open Rcic.Declarative

/-- Field kind read off syntax. -/
def kindOf (f : Nat) : Expr Nat → PKind
  | .pi A B => if occursConst f (.pi A B) = true then .fn else .plain
  | A => if occursConst f A = true then .direct else .plain

def kindsOf (f : Nat) (Fs : List (Expr Nat)) : List PKind := Fs.map (kindOf f)

def piDom : Expr Nat → Expr Nat | .pi A _ => A | A => A

def piCod : Expr Nat → Expr Nat | .pi _ B => B | A => A

section

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (σ : Nat → Nat)

/-- A recursive occurrence's arguments fit the family's telescope. -/
def argsFitF (ρ : Nat → PSet.{4}) (A : Expr Nat) : Prop :=
  TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0 ((appsSpine A).2.map (den (mkM P μ) σ ρ))

/-- Sentinel-coded index tuple of a recursive occurrence: `{∅}` when the
arguments do not fit. -/
def recTupAt (ρ : Nat → PSet.{4}) (A : Expr Nat) : PSet.{4} :=
  cond P.dec (argsFitF P μ fd σ ρ A)
    (ordPair pempty (tup ((familyIdx fd.params.length A).map (den (mkM P μ) σ ρ))))
    (singleton pempty)

/-- The result-index tuple of a data value (`∅` when its tag is no constructor). -/
def resTupF (ρp : Nat → PSet.{4}) (z : PSet.{4}) : PSet.{4} :=
  match findIdx (mkM P μ) (fun j => Equiv (tagOf z) (ord j)) fd.ctors.length with
  | some j => ordPair pempty (tup ((fd.ctors.getD j ([], [])).2.map
      (den (mkM P μ) σ (push (untup (nfOf fd j) (payload z)) ρp))))
  | none => pempty

def fieldAt (Fs : List (Expr Nat)) (k : Nat) : Expr Nat := Fs.getD k (.sort .zero)

def nonrecOkF (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat)) (k : Nat)
    (pre : List PSet.{4}) (x : PSet.{4}) : Prop :=
  x ∈ truncW (mkM P μ) W4 (evalTotal σ fd.resLevel)
    (Ed (mkM P μ) (den (mkM P μ) σ (push pre ρp) (fieldAt Fs k)))

def domEF (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat)) (k : Nat)
    (pre : List PSet.{4}) : PSet.{4} :=
  Ed (mkM P μ) (den (mkM P μ) σ (push pre ρp) (piDom (fieldAt Fs k)))

def domBigF (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat)) (k : Nat)
    (pre : List PSet.{4}) : PSet.{4} :=
  match kindOf fd.fref (fieldAt Fs k) with
  | .fn => cond P.dec (domEF P μ σ ρp Fs k pre ∈ W4 (evalTotal σ fd.resLevel))
      (domEF P μ σ ρp Fs k pre) (singleton pempty)
  | _ => singleton pempty

def recTupF (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat)) (k : Nat)
    (pre : List PSet.{4}) (y : PSet.{4}) : PSet.{4} :=
  match kindOf fd.fref (fieldAt Fs k) with
  | .fn => cond P.dec (domEF P μ σ ρp Fs k pre ∈ W4 (evalTotal σ fd.resLevel))
      (recTupAt P μ fd σ (vcons y (push pre ρp)) (piCod (fieldAt Fs k))) (singleton pempty)
  | _ => recTupAt P μ fd σ (push pre ρp) (fieldAt Fs k)

end

/-- `resTupF` respects `≈` in the value. -/
theorem resTupF_congr (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) {z z' : PSet.{4}} (hzz : Equiv z z') :
    Equiv (resTupF P μ fd σ ρp z) (resTupF P μ fd σ ρp z') := by
  unfold resTupF
  rw [findIdx_congr (mkM P μ) (fun i =>
    ⟨fun h => (tagOf_congr hzz).symm.trans h, fun h => (tagOf_congr hzz).trans h⟩)]
  cases findIdx (mkM P μ) (fun j => Equiv (tagOf z') (ord j)) fd.ctors.length with
  | none => exact Equiv.rfl
  | some j =>
      exact ordPair_congr Equiv.rfl (tup_congr (LEq_map_den (mkM P μ) σ
        (fun i => push_congr (untup_congr' (nfOf fd j) (payload_congr hzz))
          (fun _ => Equiv.rfl) i) _))

/-- `resTupF` respects `≈` in the parameter environment. -/
theorem resTupF_env (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) {ρp ρp' : Nat → PSet.{4}} (h : ∀ i, Equiv (ρp i) (ρp' i)) (z : PSet.{4}) :
    Equiv (resTupF P μ fd σ ρp z) (resTupF P μ fd σ ρp' z) := by
  unfold resTupF
  cases findIdx (mkM P μ) (fun j => Equiv (tagOf z) (ord j)) fd.ctors.length with
  | none => exact Equiv.rfl
  | some j =>
      exact ordPair_congr Equiv.rfl (tup_congr (LEq_map_den (mkM P μ) σ
        (fun i => push_congr (LEq.refl _) h i) _))

/-- `argsFitF` respects `≈` in the environment. -/
theorem argsFitF_congr (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) {ρ ρ' : Nat → PSet.{4}} (h : ∀ i, Equiv (ρ i) (ρ' i)) (A : Expr Nat) :
    argsFitF P μ fd σ ρ A ↔ argsFitF P μ fd σ ρ' A :=
  ⟨fun hf => TelFits_congr (mkM P μ) σ _ (fun _ => Equiv.rfl)
      (LEq_map_den (mkM P μ) σ h _) hf,
   fun hf => TelFits_congr (mkM P μ) σ _ (fun _ => Equiv.rfl)
      (LEq_map_den (mkM P μ) σ (fun i => (h i).symm) _) hf⟩

/-- `recTupAt` respects `≈` in the environment. -/
theorem recTupAt_congr (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) {ρ ρ' : Nat → PSet.{4}} (h : ∀ i, Equiv (ρ i) (ρ' i)) (A : Expr Nat) :
    Equiv (recTupAt P μ fd σ ρ A) (recTupAt P μ fd σ ρ' A) := by
  unfold recTupAt
  exact cond_congr (argsFitF_congr P μ fd σ h A)
    (ordPair_congr Equiv.rfl (tup_congr (LEq_map_den (mkM P μ) σ h _))) Equiv.rfl

/-- `nonrecOkF` respects prefix agreement and `≈`. -/
theorem nonrecOkF_congr (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat)) (k : Nat)
    {pre pre' : List PSet.{4}} (hp : LEq pre pre') {x x' : PSet.{4}} (hx : Equiv x x') :
    nonrecOkF P μ fd σ ρp Fs k pre x → nonrecOkF P μ fd σ ρp Fs k pre' x' :=
  fun h => mem_congr_left hx (mem_congr_right (truncW_congr (mkM P μ) W4 _
    (ed_congr (mkM P μ) (den_congr (mkM P μ) σ _
      (push_congr hp (fun _ => Equiv.rfl))))) h)

/-- `domEF` respects prefix agreement. -/
theorem domEF_congr (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat)) (k : Nat)
    {pre pre' : List PSet.{4}} (hp : LEq pre pre') :
    Equiv (domEF P μ σ ρp Fs k pre) (domEF P μ σ ρp Fs k pre') :=
  ed_congr (mkM P μ) (den_congr (mkM P μ) σ _
    (push_congr hp (fun _ => Equiv.rfl)))

/-- `domBigF` respects prefix agreement. -/
theorem domBigF_congr (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat)) (k : Nat)
    {pre pre' : List PSet.{4}} (hp : LEq pre pre') :
    Equiv (domBigF P μ fd σ ρp Fs k pre) (domBigF P μ fd σ ρp Fs k pre') := by
  unfold domBigF
  split
  · exact cond_congr
      ⟨fun h => mem_congr_left (domEF_congr P μ σ ρp Fs k hp) h,
       fun h => mem_congr_left (domEF_congr P μ σ ρp Fs k hp).symm h⟩
      (domEF_congr P μ σ ρp Fs k hp) Equiv.rfl
  · exact Equiv.rfl

/-- `recTupF` respects prefix agreement and `≈`. -/
theorem recTupF_congr (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat)) (k : Nat)
    {pre pre' : List PSet.{4}} (hp : LEq pre pre') {y y' : PSet.{4}} (hy : Equiv y y') :
    Equiv (recTupF P μ fd σ ρp Fs k pre y) (recTupF P μ fd σ ρp Fs k pre' y') := by
  unfold recTupF
  split
  · exact cond_congr
      ⟨fun h => mem_congr_left (domEF_congr P μ σ ρp Fs k hp) h,
       fun h => mem_congr_left (domEF_congr P μ σ ρp Fs k hp).symm h⟩
      (recTupAt_congr P μ fd σ
        (fun i => vcons_congr hy (fun j => push_congr (ρ := ρp) (ρ' := ρp) hp (fun _ => Equiv.rfl) j) i) _)
      Equiv.rfl
  · exact recTupAt_congr P μ fd σ
      (fun i => push_congr hp (fun _ => Equiv.rfl) i) _

/-- The R-CIC constructor semantics as a `Sem`. -/
noncomputable def semF (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat)) : Sem.{4} where
  resTup := resTupF P μ fd σ ρp
  nonrecOk := nonrecOkF P μ fd σ ρp Fs
  recTup := recTupF P μ fd σ ρp Fs
  domBig := domBigF P μ fd σ ρp Fs
  resTup_congr := fun _ _ h => resTupF_congr P μ fd σ ρp h
  nonrecOk_congr := fun k _ _ _ _ hp hx h => nonrecOkF_congr P μ fd σ ρp Fs k hp hx h
  recTup_congr := fun k _ _ _ _ hp hy => recTupF_congr P μ fd σ ρp Fs k hp hy
  domBig_congr := fun k _ _ hp => domBigF_congr P μ fd σ ρp Fs k hp

/-- An ordered pair is never the sentinel `{∅}`. -/
theorem ordPair_ne_singleton_pempty (t : PSet.{4}) :
    ¬ Equiv (ordPair pempty t) (singleton pempty) := fun h => not_mem_pempty
      (mem_congr_right (mem_singleton.mp (mem_congr_right h (mem_pair.mpr (Or.inl Equiv.rfl)))) (mem_singleton.mpr Equiv.rfl))

/-- `resTupF` is never the sentinel `{∅}`. -/
theorem resTupF_ne_sentinel (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (z : PSet.{4}) :
    ¬ Equiv (resTupF P μ fd σ ρp z) (singleton pempty) := by
  unfold resTupF
  cases findIdx (mkM P μ) (fun j => Equiv (tagOf z) (ord j)) fd.ctors.length with
  | some _ => exact ordPair_ne_singleton_pempty _
  | none => exact fun h => not_mem_pempty (mem_congr_right h.symm (mem_singleton.mpr Equiv.rfl))

end PSet

end Rcic.F3
