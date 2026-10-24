import rcic.ScmWire

/-!
# RcicWireEmit — first-order entries of the ScmWire text codec (F0.2, request/response bytes)

Entries over the landed codec of `rcic.ScmWire` (nothing is re-implemented here):

* `wireDecVal bytes fuel`   — `decVal` at offset 0 with the carrier's gas, no trailing bytes;
* `wireDecCanon bytes fuel` — the same plus "accepted bytes re-encode exactly" (`encVal`);
* `wireDecTy bytes fuel`    — `decTy` likewise;
* `wireEncVal v`, `wireEncTy t` — the response side.

`wireDecCanon_reencodes` pins the canonical law: an accepted decode re-encodes to the input.
Emission: `lean/rcic/RcicWireEmitGenerate.lean`. closure_claim 0.
-/

namespace Rcic.Scm.Wire
open Rcic.Scm

def wireDecVal (bytes : String) (fuel : Int) : Except String Val :=
  let cs := bytes.toList.toArray
  match decVal cs (gasFor fuel cs.size) fuel 0 with
  | .error c => .error c
  | .ok (it, q) => if q ≠ cs.size then wErr "trailing" else .ok (asVal it)

def wireDecCanon (bytes : String) (fuel : Int) : Except String Val :=
  match wireDecVal bytes fuel with
  | .error c => .error c
  | .ok v => if encVal v ≠ bytes then wErr "noncanonical" else .ok v

def wireDecTy (bytes : String) (fuel : Int) : Except String CoreTy :=
  let cs := bytes.toList.toArray
  match decTy cs (gasFor fuel cs.size) fuel 0 with
  | .error c => .error c
  | .ok (it, q) => if q ≠ cs.size then wErr "trailing" else .ok (asTy it)

def wireDecTyCanon (bytes : String) (fuel : Int) : Except String CoreTy :=
  match wireDecTy bytes fuel with
  | .error c => .error c
  | .ok t => if encTy t ≠ bytes then wErr "noncanonical" else .ok t

def wireEncVal (v : Val) : String := encVal v
def wireEncTy (t : CoreTy) : String := encTy t

/-- accepted canonical bytes re-encode exactly -/
theorem wireDecCanon_reencodes (bytes : String) (fuel : Int) (v : Val)
    (h : wireDecCanon bytes fuel = .ok v) : encVal v = bytes := by
  unfold wireDecCanon at h
  cases hd : wireDecVal bytes fuel with
  | error c => simp [hd] at h
  | ok w =>
      simp only [hd] at h
      by_cases hne : encVal w ≠ bytes
      · simp [hne, wErr] at h
      · simp only [hne, if_false] at h
        have hw : w = v := by cases h; rfl
        subst hw
        simpa using hne

theorem wireDecTyCanon_reencodes (bytes : String) (fuel : Int) (t : CoreTy)
    (h : wireDecTyCanon bytes fuel = .ok t) : encTy t = bytes := by
  unfold wireDecTyCanon at h
  cases hd : wireDecTy bytes fuel with
  | error c => simp [hd] at h
  | ok w =>
      simp only [hd] at h
      by_cases hne : encTy w ≠ bytes
      · simp [hne, wErr] at h
      · simp only [hne, if_false] at h
        have hw : w = t := by cases h; rfl
        subst hw
        simpa using hne

end Rcic.Scm.Wire

#print axioms Rcic.Scm.Wire.wireDecCanon_reencodes
#print axioms Rcic.Scm.Wire.wireDecTyCanon_reencodes
