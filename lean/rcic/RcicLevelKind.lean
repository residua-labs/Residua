/-
RM-023 slice 1 — the kind-record codec.

`encode` writes a `Level` as the carrier record and does not decide
equality. Tags and field order are `scm/rcic/level_eqn*.scm`:
`kind`, then `a`/`b` or `i`.

* 0 zero — `[.i 0]`
* 1 succ — `[.i 1, child]`
* 2 max  — `[.i 2, left, right]`
* 3 imax — `[.i 3, left, right]`
* 4 param — `[.i 4, .i index]`

`levelEncode` (`RcicExprSubstTask`) is the `LevelWire` image of the
same tags. It is not a `Val`. `encLevel` (`ScmInstantiate`) is the
token string. Neither is this round-trip.

`answerEnc` stores only the bit `decEqN l .zero`. It identifies
`.zero` with `.max .zero .zero`, so it fails
`∀ l, decode (enc l) = some l`, the specification `encode` meets.

`closure_claim` stays 0.
-/
import rcic.ScmCore
import rcic.RcicLevelDec

namespace Rcic.LevelKind

open Rcic.Declarative
open Rcic.Scm

/-- Kind-record of a level. Constructor recursion only: no `decEqN`. -/
def encode : Level → Val
  | .zero => .r [.i 0]
  | .succ l => .r [.i 1, encode l]
  | .max a b => .r [.i 2, encode a, encode b]
  | .imax a b => .r [.i 3, encode a, encode b]
  | .param n => .r [.i 4, .i n]

/-- Read a kind-record back. A wrong tag or a negative index is `none`. -/
def decode : Val → Option Level
  | .r [.i 0] => some .zero
  | .r [.i 1, a] => (decode a).map .succ
  | .r [.i 2, a, b] =>
      match decode a, decode b with
      | some a, some b => some (.max a b)
      | _, _ => none
  | .r [.i 3, a, b] =>
      match decode a, decode b with
      | some a, some b => some (.imax a b)
      | _, _ => none
  | .r [.i 4, .i n] =>
      if 0 ≤ n then some (.param n.toNat) else none
  | _ => none

theorem decode_encode (l : Level) : decode (encode l) = some l := by
  induction l with
  | zero => rfl
  | succ l ih => simp [encode, decode, ih]
  | max a b iha ihb => simp [encode, decode, iha, ihb]
  | imax a b iha ihb => simp [encode, decode, iha, ihb]
  | param n =>
      simp only [encode, decode]
      rw [if_pos (Int.ofNat_nonneg n), Int.toNat_ofNat]

/-- Any encoder that round-trips through `dec` is injective. -/
theorem roundtrip_injective
    (enc : Level → Val) (dec : Val → Option Level)
    (h : ∀ l, dec (enc l) = some l)
    {l1 l2 : Level} (he : enc l1 = enc l2) : l1 = l2 := by
  have h1 := h l1
  rw [he] at h1
  have hs : some l1 = some l2 := h1.symm.trans (h l2)
  injection hs

/-- The real codec separates `.zero` from `.max .zero .zero`. -/
theorem encode_zero_ne_max_zero :
    encode .zero ≠ encode (.max .zero .zero) := by
  intro h
  cases roundtrip_injective encode decode decode_encode h

/-- Stores the `decEqN l .zero` bit as a kind-record of `.zero` or of
`.succ .zero`. The level itself is not in the record. -/
def answerEnc (l : Level) : Val :=
  bif decEqN l .zero then encode .zero else encode (.succ .zero)

private theorem decEqN_zero_zero : decEqN .zero .zero = true :=
  decEqN_complete .zero .zero (fun _ => rfl)

private theorem decEqN_max_zero_zero :
    decEqN (.max .zero .zero) .zero = true :=
  decEqN_complete _ _ (eqN_max_zero_left .zero)

private theorem answerEnc_zero : answerEnc .zero = encode .zero := by
  unfold answerEnc
  rw [decEqN_zero_zero]
  rfl

private theorem answerEnc_max :
    answerEnc (.max .zero .zero) = encode .zero := by
  unfold answerEnc
  rw [decEqN_max_zero_zero]
  rfl

theorem answerEnc_collapses :
    answerEnc .zero = answerEnc (.max .zero .zero) := by
  rw [answerEnc_zero, answerEnc_max]

/-- The codec's round-trip specification, failed by an encoder that
computes the equality answer. -/
theorem answerEnc_fails_roundtrip :
    ¬ ∀ l, decode (answerEnc l) = some l := by
  intro h
  cases roundtrip_injective answerEnc decode h answerEnc_collapses

#print axioms Rcic.LevelKind.decode_encode
#print axioms Rcic.LevelKind.roundtrip_injective
#print axioms Rcic.LevelKind.encode_zero_ne_max_zero
#print axioms Rcic.LevelKind.answerEnc_collapses
#print axioms Rcic.LevelKind.answerEnc_fails_roundtrip

end Rcic.LevelKind
