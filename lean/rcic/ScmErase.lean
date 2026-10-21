/-
RCIC — value elaboration and erasure are mutually inverse at the
FIRST-ORDER value layer (#6029 K3, segment 4). This is the first-order
analogue of 06 §19's value clauses, NOT `ValueAt` on canonical bytes (K3c).

Owner text: 06 §4 "roundtrip and accepted-byte canonicality"; 06 §19
"ValueAt → unique intrinsic decoded value; encode intrinsic value →
ValueAt".

The first-order value `Val` is what the carrier records exchange and what
the core wire (06 §17, `ScmWire.encVal`) serializes. This file proves that
the elaboration `toCore t : Val → Option (CoreVal t)` and the erasure
`CoreVal.erase` are mutually inverse where defined:
  `toCore_erase`  — an accepted first-order value is the erasure of what it
                    elaborates to (no information is invented or dropped);
  `erase_toCore`  — every intrinsic value elaborates back from its erasure,
                    to itself (uniqueness of the decoded value).
-/
import rcic.ScmMachine

namespace Rcic.Scm.Erase
open Rcic.Scm

theorem toBytes_erase : ∀ (bs : List Int) (ys : List UInt8),
    toBytes bs = some ys → ys.map (fun x => (x.toNat : Int)) = bs
  | [], ys, h => by
      have e : ys = [] := (Option.some.inj h).symm
      subst e; rfl
  | b :: bs, ys, h => by
      unfold toBytes at h
      split at h
      · rename_i hb
        cases hr : toBytes bs with
        | none => rw [hr] at h; exact Option.noConfusion h
        | some r =>
          rw [hr] at h
          have e := (Option.some.inj h).symm
          subst e
          have hn : (UInt8.ofNat b.toNat).toNat = b.toNat := by
            show b.toNat % 256 = b.toNat
            exact Nat.mod_eq_of_lt (by
              have h0 : ((b.toNat : Nat) : Int) ≤ ((255 : Nat) : Int) := by
                rw [Int.toNat_of_nonneg hb.1]; exact hb.2
              have h1 : b.toNat ≤ 255 := Int.ofNat_le.mp h0
              exact Nat.lt_succ_of_le h1)
          show ((UInt8.ofNat b.toNat).toNat : Int) :: r.map (fun x => (x.toNat : Int)) = b :: bs
          rw [hn, Int.toNat_of_nonneg hb.1, toBytes_erase bs r hr]
      · exact Option.noConfusion h

mutual
theorem toCore_erase : ∀ (t : CoreTy) (v : Val) (cv : CoreVal t), toCore t v = some cv → cv.erase = v
  | .i64, .i n, cv, h => by
      unfold toCore at h
      split at h
      · have e := (Option.some.inj h).symm; subst e; rfl
      · exact Option.noConfusion h
  | .bool, .b b, cv, h => by
      unfold toCore at h
      split at h
      · rename_i h0; have e := (Option.some.inj h).symm; subst e; subst h0; rfl
      · split at h
        · rename_i _ h1; have e := (Option.some.inj h).symm; subst e; subst h1; rfl
        · exact Option.noConfusion h
  | .str, .s s, cv, h => by
      have e := (Option.some.inj h).symm; subst e; rfl
  | .bytes, .y bs, cv, h => by
      unfold toCore at h
      cases hr : toBytes bs with
      | none => rw [hr] at h; exact Option.noConfusion h
      | some ys =>
        rw [hr] at h
        have e := (Option.some.inj h).symm; subst e
        show Val.y (ys.map (fun x => (x.toNat : Int))) = Val.y bs
        rw [toBytes_erase bs ys hr]
  | .list t, .l xs, cv, h => by
      unfold toCore at h
      cases hr : toCoreList t xs with
      | none => rw [hr] at h; exact Option.noConfusion h
      | some ys =>
        rw [hr] at h
        have e := (Option.some.inj h).symm; subst e
        show Val.l ys.erase = Val.l xs
        rw [toCoreList_erase t xs ys hr]
  | .pair a b, .p x y, cv, h => by
      unfold toCore at h
      cases hx : toCore a x with
      | none => rw [hx] at h; exact Option.noConfusion h
      | some x' =>
        cases hy : toCore b y with
        | none => rw [hx, hy] at h; exact Option.noConfusion h
        | some y' =>
          rw [hx, hy] at h
          have e := (Option.some.inj h).symm; subst e
          show Val.p x'.erase y'.erase = Val.p x y
          rw [toCore_erase a x x' hx, toCore_erase b y y' hy]
  | .sum ts, .j i v, cv, h => by
      unfold toCore at h
      split at h
      · exact Option.noConfusion h
      · rename_i hi
        split at h
        · rename_i t' ht
          cases hv : toCore t' v with
          | none => rw [hv] at h; exact Option.noConfusion h
          | some v' =>
            rw [hv] at h
            have e := (Option.some.inj h).symm; subst e
            show Val.j (i.toNat : Int) v'.erase = Val.j i v
            rw [Int.toNat_of_nonneg (Int.not_lt.mp hi), toCore_erase t' v v' hv]
        · exact Option.noConfusion h
  | .record fs, .r xs, cv, h => by
      unfold toCore at h
      cases hr : toCoreVals (fs.map Prod.snd) xs with
      | none => rw [hr] at h; exact Option.noConfusion h
      | some ys =>
        rw [hr] at h
        have e := (Option.some.inj h).symm; subst e
        show Val.r ys.erase = Val.r xs
        rw [toCoreVals_erase _ xs ys hr]
  | .i64, .b _, _, h | .i64, .s _, _, h | .i64, .y _, _, h | .i64, .l _, _, h | .i64, .p _ _, _, h
  | .i64, .j _ _, _, h | .i64, .r _, _, h => Option.noConfusion h
  | .bool, .i _, _, h | .bool, .s _, _, h | .bool, .y _, _, h | .bool, .l _, _, h | .bool, .p _ _, _, h
  | .bool, .j _ _, _, h | .bool, .r _, _, h => Option.noConfusion h
  | .str, .i _, _, h | .str, .b _, _, h | .str, .y _, _, h | .str, .l _, _, h | .str, .p _ _, _, h
  | .str, .j _ _, _, h | .str, .r _, _, h => Option.noConfusion h
  | .bytes, .i _, _, h | .bytes, .b _, _, h | .bytes, .s _, _, h | .bytes, .l _, _, h | .bytes, .p _ _, _, h
  | .bytes, .j _ _, _, h | .bytes, .r _, _, h => Option.noConfusion h
  | .list _, .i _, _, h | .list _, .b _, _, h | .list _, .s _, _, h | .list _, .y _, _, h
  | .list _, .p _ _, _, h | .list _, .j _ _, _, h | .list _, .r _, _, h => Option.noConfusion h
  | .pair _ _, .i _, _, h | .pair _ _, .b _, _, h | .pair _ _, .s _, _, h | .pair _ _, .y _, _, h
  | .pair _ _, .l _, _, h | .pair _ _, .j _ _, _, h | .pair _ _, .r _, _, h => Option.noConfusion h
  | .sum _, .i _, _, h | .sum _, .b _, _, h | .sum _, .s _, _, h | .sum _, .y _, _, h
  | .sum _, .l _, _, h | .sum _, .p _ _, _, h | .sum _, .r _, _, h => Option.noConfusion h
  | .record _, .i _, _, h | .record _, .b _, _, h | .record _, .s _, _, h | .record _, .y _, _, h
  | .record _, .l _, _, h | .record _, .p _ _, _, h | .record _, .j _ _, _, h => Option.noConfusion h
theorem toCoreList_erase : ∀ (t : CoreTy) (xs : List Val) (ys : CoreList t),
    toCoreList t xs = some ys → ys.erase = xs
  | t, [], ys, h => by
      have e := (Option.some.inj h).symm; subst e; rfl
  | t, x :: xs, ys, h => by
      unfold toCoreList at h
      cases hx : toCore t x with
      | none => rw [hx] at h; exact Option.noConfusion h
      | some x' =>
        cases hxs : toCoreList t xs with
        | none => rw [hx, hxs] at h; exact Option.noConfusion h
        | some xs' =>
          rw [hx, hxs] at h
          have e := (Option.some.inj h).symm; subst e
          show x'.erase :: xs'.erase = x :: xs
          rw [toCore_erase t x x' hx, toCoreList_erase t xs xs' hxs]
theorem toCoreVals_erase : ∀ (ts : List CoreTy) (xs : List Val) (ys : CoreVals ts),
    toCoreVals ts xs = some ys → ys.erase = xs
  | [], [], ys, h => by
      have e := (Option.some.inj h).symm; subst e; rfl
  | t :: ts, x :: xs, ys, h => by
      unfold toCoreVals at h
      cases hx : toCore t x with
      | none => rw [hx] at h; exact Option.noConfusion h
      | some x' =>
        cases hxs : toCoreVals ts xs with
        | none => rw [hx, hxs] at h; exact Option.noConfusion h
        | some xs' =>
          rw [hx, hxs] at h
          have e := (Option.some.inj h).symm; subst e
          show x'.erase :: xs'.erase = x :: xs
          rw [toCore_erase t x x' hx, toCoreVals_erase ts xs xs' hxs]
  | [], _ :: _, _, h => Option.noConfusion h
  | _ :: _, [], _, h => Option.noConfusion h
end

theorem uint8_ofNat_toNat (x : UInt8) : UInt8.ofNat x.toNat = x := by
  cases x with
  | mk v =>
    show UInt8.mk (BitVec.ofNat 8 v.toNat) = UInt8.mk v
    exact congrArg UInt8.mk (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt v.isLt))

theorem erase_toBytes : ∀ (ys : List UInt8), toBytes (ys.map (fun x => (x.toNat : Int))) = some ys
  | [] => rfl
  | y :: ys => by
      have hlt : y.toNat < 256 := y.toBitVec.isLt
      have hb : 0 ≤ (y.toNat : Int) ∧ (y.toNat : Int) ≤ 255 :=
        ⟨Int.ofNat_nonneg _, Int.ofNat_le.mpr (Nat.le_of_lt_succ hlt)⟩
      show toBytes ((y.toNat : Int) :: ys.map (fun x => (x.toNat : Int))) = some (y :: ys)
      unfold toBytes
      rw [if_pos hb, erase_toBytes ys, Int.toNat_ofNat, uint8_ofNat_toNat]
      rfl

mutual
theorem erase_toCore : ∀ {t : CoreTy} (cv : CoreVal t), toCore t cv.erase = some cv
  | _, .i64V n h => by
      show (if h' : inI64 n then some (CoreVal.i64V n h') else none) = some (CoreVal.i64V n h)
      rw [dif_pos h]
  | _, .boolV b => by cases b <;> rfl
  | _, .strV _ => rfl
  | _, .bytesV bs => by
      show (toBytes (bs.map (fun x => (x.toNat : Int)))).map CoreVal.bytesV = some (CoreVal.bytesV bs)
      rw [erase_toBytes bs]; rfl
  | _, .listV xs => by
      show (toCoreList _ xs.erase).map CoreVal.listV = some (CoreVal.listV xs)
      rw [erase_toCoreList xs]; rfl
  | _, .pairV x y => by
      show (match toCore _ x.erase, toCore _ y.erase with
        | some x', some y' => some (CoreVal.pairV x' y')
        | _, _ => none) = some (CoreVal.pairV x y)
      rw [erase_toCore x, erase_toCore y]
  | _, .injV (ts := ts) i t h x => by
      have ih := erase_toCore x
      show toCore (.sum ts) (.j (i : Int) x.erase) = some (CoreVal.injV i t h x)
      unfold toCore
      rw [if_neg (Int.not_lt.mpr (Int.ofNat_nonneg i))]
      split
      · rename_i t' ht'
        have e : t' = t := Option.some.inj (ht'.symm.trans h)
        subst e
        rw [ih]
        rfl
      · rename_i hn
        exact Option.noConfusion (hn.symm.trans h)
  | _, .recordV xs => by
      show (toCoreVals _ xs.erase).map CoreVal.recordV = some (CoreVal.recordV xs)
      rw [erase_toCoreVals xs]; rfl
theorem erase_toCoreList : ∀ {t : CoreTy} (xs : CoreList t), toCoreList t xs.erase = some xs
  | _, .nil => rfl
  | _, .cons x xs => by
      show (match toCore _ x.erase, toCoreList _ xs.erase with
        | some x', some xs' => some (CoreList.cons x' xs')
        | _, _ => none) = some (CoreList.cons x xs)
      rw [erase_toCore x, erase_toCoreList xs]
theorem erase_toCoreVals : ∀ {ts : List CoreTy} (xs : CoreVals ts), toCoreVals ts xs.erase = some xs
  | _, .nil => rfl
  | _, .cons x xs => by
      show (match toCore _ x.erase, toCoreVals _ xs.erase with
        | some x', some xs' => some (CoreVals.cons x' xs')
        | _, _ => none) = some (CoreVals.cons x xs)
      rw [erase_toCore x, erase_toCoreVals xs]
end

/-! ## Instance witnesses (M-005) -/
def h5 : inI64 5 := ⟨by decide, by decide⟩
example : toCore .i64 (Val.i 5) = some (CoreVal.i64V 5 h5) := erase_toCore (CoreVal.i64V 5 h5)
example : (CoreVal.boolV true).erase = Val.b 1 := toCore_erase .bool (.b 1) _ rfl

end Rcic.Scm.Erase
