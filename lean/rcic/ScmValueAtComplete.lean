/-
SCM-014 "ValueAt sound and complete" (06 §22, `docs/rcic/06_SCM_CORE_SEMANTICS.md:465`)
over the 06 §18 objects (06:368-373) and the two 06 §19 value directions (06:409-410).

Owner text, verbatim:

  06 §18 (06:368-373):
    SemanticValue(T : BoundCoreType) :=
      Σ value_bytes : Bytes,
        ValueAt(T,value_bytes)
  06 §19 (06:407-410):
    Required bidirectional theorems:
    encode intrinsic value → ValueAt
    ValueAt → unique intrinsic decoded value

What is on main before this module (`ScmBoundBridge`):

* `valueAt_dec_uniq` / `valueAt_coreVal_uniq` — 06:410, sealed.
* `valueAt_of_enc` — 06:409 over a RAW `Val`, with three premises: `dqV v` (the wire
  bound), `valGas v ≤ gasFor … - 1` and `valFuel v ≤ len` (decoder budgets at the
  input's own length).

What this module adds (the paired `ScmBoundBridge` change extracts the decoder
roundtrip internal to `valueAt_of_enc` as the shared lemma
`valueBytesAt_encVal`, reused here by `semanticValue_of_core_dec`; no existing
statement changed):

* `valGas_lt_encLen` — the decoder gas budget is discharged by the encoding's own
  length (the fuel half is `valFuel_le_encLen`, already on main). Neither budget is a
  premise any more.
* `valueAt_complete` — 06:409 over the INTRINSIC value: every `cv : CoreVal T.ty`
  inside the wire bound (`dqV cv.erase`) has canonical bytes `encVal cv.erase` with
  `ValueAt T`. `semanticValue_of_core` packs that as an element of `SemanticValue T`.
* `valueAt_sound` / `valueAt_iff` — every `ValueAt T b` names a unique intrinsic
  value `cv : CoreVal T.ty` whose canonical encoding is `b`, and `ValueAt T b`
  holds iff `b` decodes (`valueBytesAt`) to the erasure of some `cv : CoreVal T.ty`.
* `typeAt_atLength_complete` / `typeAt_atLength_iff` and
  `valueAt_atLength_complete` / `valueAt_atLength_iff` — completeness of the
  carrier decisions `typeAt` and `valueAt` at each input's own length (converses
  of `ScmBoundCoreTV`'s `typeAt_atLength_accepts` / `valueAt_atLength_accepts`).
* `valueBytesAt_list_bound` / `no_bytes_of_list_bound` /
  `valueAt_complete_unbounded_false` — the wire bound is necessary: a list value
  with 1025 elements has no `ValueAt` bytes at any bound type. Completeness
  without a size premise is PROVEN-FALSE; that refutation is a permanent
  residue, and the claim is restated as `valueAt_complete` (in-bound values)
  plus this tooth.
* `dqV_noListLen` / `dqsV_zerosL` / `zerosL_dqV_noListLen` / `zerosL_dqV_false`
  / `zerosL_bound_control` — the control pair for the tooth: the SAME
  `zerosL 1025` input satisfies `dqV` with only the list-length conjunct
  removed (payload `dqsV` retained), while exact `dqV` and the real codec
  refuse. The guard is the decider, shown as data.

Named over-approximation (not a wall): `dqV` also bounds string payloads to 1024
characters, while `decStr` (`ScmWire.lean:180`) accepts any length. So
`valueAt_complete` is silent on strings longer than 1024 characters. Those strings
are not refuted here. `closure_claim` 0.
-/
import rcic.ScmBoundBridge

namespace Rcic.Scm.ValueAtComplete

open Rcic.Scm Rcic.Scm.Wire Rcic.Scm.BoundTV Rcic.Scm.BoundBridge Rcic.BoundObject

/-! ## The decoder gas budget is bounded by the encoding's length -/

/-- Every `encNat` digit string carries at least its terminator, so a joined list of
    them is at least as long as the list. -/
theorem catEncNat_len_ge : ∀ (bs : List Int),
    bs.length ≤ (catEnc encNat bs).toList.length
  | [] => Nat.zero_le _
  | b :: bs => by
      have ih := catEncNat_len_ge bs
      have hb := encNat_len_pos b
      rw [catEnc_cons, List.length_append, List.length_cons]
      omega

mutual
/-- `decVal`'s gas need is strictly below four times the encoded length. -/
theorem valGas_lt_encLen : ∀ (v : Val), valGas v + 1 ≤ 4 * (encVal v).toList.length
  | .i n => by
      have h := encNat_len_pos n
      show 1 + 1 ≤ 4 * (("I" ++ encNat n)).toList.length
      simp only [toList_append, List.length_append,
        show ("I".toList.length : Nat) = 1 from rfl]; omega
  | .b n => by
      have h := encNat_len_pos n
      show 1 + 1 ≤ 4 * (("B" ++ encNat n)).toList.length
      simp only [toList_append, List.length_append,
        show ("B".toList.length : Nat) = 1 from rfl]; omega
  | .s s => by
      show 1 + 1 ≤ 4 * (("T" ++ encStr s)).toList.length
      simp only [toList_append, List.length_append,
        show ("T".toList.length : Nat) = 1 from rfl]; omega
  | .y bs => by
      have hj := catEncNat_len_ge bs
      have hn := encNat_len_pos (↑bs.length)
      have he : (String.join (bs.map encNat)).toList = (catEnc encNat bs).toList := rfl
      show bs.length + 4 + 1 ≤
        4 * (("Y" ++ encNat ↑bs.length ++ String.join (bs.map encNat))).toList.length
      simp only [toList_append, List.length_append, he,
        show ("Y".toList.length : Nat) = 1 from rfl]; omega
  | .l xs => by
      have ih := valsGas_le_encValsLen xs
      have hn := encNat_len_pos (↑xs.length)
      show valsGas xs + xs.length + 4 + 1 ≤
        4 * (("L" ++ encNat ↑xs.length ++ encVals xs)).toList.length
      simp only [toList_append, List.length_append,
        show ("L".toList.length : Nat) = 1 from rfl]; omega
  | .r xs => by
      have ih := valsGas_le_encValsLen xs
      have hn := encNat_len_pos (↑xs.length)
      show valsGas xs + xs.length + 4 + 1 ≤
        4 * (("R" ++ encNat ↑xs.length ++ encVals xs)).toList.length
      simp only [toList_append, List.length_append,
        show ("R".toList.length : Nat) = 1 from rfl]; omega
  | .p a b => by
      have ia := valGas_lt_encLen a; have ib := valGas_lt_encLen b
      show max (valGas a) (valGas b) + 2 + 1 ≤
        4 * (("P" ++ encVal a ++ encVal b)).toList.length
      simp only [toList_append, List.length_append,
        show ("P".toList.length : Nat) = 1 from rfl]; omega
  | .j i x => by
      have ih := valGas_lt_encLen x
      have hn := encNat_len_pos i
      show valGas x + 2 + 1 ≤ 4 * (("J" ++ encNat i ++ encVal x)).toList.length
      simp only [toList_append, List.length_append,
        show ("J".toList.length : Nat) = 1 from rfl]; omega
/-- The list form: the max element gas plus one per element. -/
theorem valsGas_le_encValsLen : ∀ (xs : List Val),
    valsGas xs + xs.length ≤ 4 * (encVals xs).toList.length
  | [] => Nat.le_refl _
  | x :: xs => by
      have ix := valGas_lt_encLen x; have is := valsGas_le_encValsLen xs
      show max (valGas x) (valsGas xs) + (xs.length + 1) ≤
        4 * ((encVal x ++ encVals xs)).toList.length
      simp only [toList_append, List.length_append]; omega
end

/-- The gas premise of `valueAt_of_enc`, discharged. -/
theorem valGas_le_gasFor (v : Val) :
    valGas v ≤ gasFor (↑(encVal v).length) (encVal v).length - 1 := by
  have h := valGas_lt_encLen v
  have hl : (encVal v).length = (encVal v).toList.length := rfl
  unfold gasFor
  rw [Int.toNat_ofNat, hl]
  omega

/-- The fuel premise of `valueAt_of_enc`, discharged (`valFuel_le_encLen`). -/
theorem valFuel_le_len (v : Val) : (valFuel v : Int) ≤ (encVal v).length := by
  have h := valFuel_le_encLen v
  have hl : (encVal v).length = (encVal v).toList.length := rfl
  rw [hl]
  exact Int.ofNat_le.mpr h

/-! ## Soundness and completeness over the intrinsic value -/

/-- `valueBytesAt` accepts only bytes that are the canonical encoding of the decoded
    value (its re-encode check). -/
theorem valueBytesAt_enc {b : String} {v : Val} (h : valueBytesAt b = some v) :
    encVal v = b := by
  unfold valueBytesAt at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact hc.2
    · exact Option.noConfusion h
  · exact Option.noConfusion h

/-- 06:409 over the intrinsic value: every `cv : CoreVal T.ty` inside the wire bound
    has canonical bytes `encVal cv.erase` with `ValueAt T`. The decoder budgets of
    `valueAt_of_enc` are discharged (`valGas_le_gasFor`, `valFuel_le_len`); the one
    premise left is the wire bound `dqV`. -/
theorem valueAt_complete (T : BoundCoreType) (cv : CoreVal T.ty)
    (hdq : dqV cv.erase) : ValueAt T (encVal cv.erase) :=
  valueAt_of_enc T cv.erase hdq (valGas_le_gasFor _) (valFuel_le_len _)
    (by rw [Rcic.Scm.Erase.erase_toCore]; rfl)

/-- `valueAt_complete` as an element of 06 §18's `SemanticValue T`. -/
def semanticValue_of_core (T : BoundCoreType) (cv : CoreVal T.ty)
    (hdq : dqV cv.erase) : SemanticValue T :=
  ⟨encVal cv.erase, valueAt_complete T cv hdq⟩

/-- The bytes of `semanticValue_of_core` decode back to `cv`'s erasure —
    the shared `valueBytesAt_encVal` roundtrip (`ScmBoundBridge`), with the
    gas/fuel budgets discharged. -/
theorem semanticValue_of_core_dec (T : BoundCoreType) (cv : CoreVal T.ty)
    (hdq : dqV cv.erase) :
    valueBytesAt (semanticValue_of_core T cv hdq).1 = some cv.erase :=
  valueBytesAt_encVal cv.erase hdq (valGas_le_gasFor _) (valFuel_le_len _)

/-- 06:410 with the bytes pinned: every `ValueAt T b` decodes to the erasure of an
    intrinsic value `cv : CoreVal T.ty`, `b` is exactly `cv`'s canonical encoding,
    and `cv` is unique. -/
theorem valueAt_sound (T : BoundCoreType) (b : String) (h : ValueAt T b) :
    ∃ cv : CoreVal T.ty, valueBytesAt b = some cv.erase ∧ b = encVal cv.erase ∧
      ∀ cv' : CoreVal T.ty, valueBytesAt b = some cv'.erase → cv' = cv := by
  obtain ⟨cv, ⟨v, hv, hcv⟩, huniq⟩ := valueAt_coreVal_uniq T b h
  have he : cv.erase = v := Rcic.Scm.Erase.toCore_erase _ _ _ hcv
  refine ⟨cv, by rw [he]; exact hv, by rw [he]; exact (valueBytesAt_enc hv).symm, ?_⟩
  intro cv' h'
  exact huniq cv' ⟨cv'.erase, h', Rcic.Scm.Erase.erase_toCore cv'⟩

/-- SCM-014 as an exact characterization: `ValueAt T b` holds iff `b` decodes (whole
    input, exact re-encode) to the erasure of some intrinsic value at `T.ty`. -/
theorem valueAt_iff (T : BoundCoreType) (b : String) :
    ValueAt T b ↔ ∃ cv : CoreVal T.ty, valueBytesAt b = some cv.erase := by
  constructor
  · intro h
    obtain ⟨cv, hb, -, -⟩ := valueAt_sound T b h
    exact ⟨cv, hb⟩
  · rintro ⟨cv, hb⟩
    have hT := T.type_at
    unfold CanonicalCoreTypeAt CanonicalObjectAt at hT
    obtain ⟨hdec, _, _⟩ := hT
    cases hd : coreTypeSchema.decode T.type_bytes with
    | none => rw [hd] at hdec; exact hdec.elim
    | some t =>
      refine ⟨t, hd, cv.erase, hb, ?_⟩
      rw [← boundCoreType_ty hd, Rcic.Scm.Erase.erase_toCore]
      rfl

/-! ## Carrier decision completeness at the input's own length -/

/-- Completeness of `typeAt` at the input's own length (converse of
    `typeAt_atLength_accepts`): every `CanonicalCoreTypeAt r b` makes `typeAt`
    accept with the decoded `CoreTy`. -/
theorem typeAt_atLength_complete {r : Ref} {b : String}
    (h : CanonicalCoreTypeAt r b) :
    (typeAt b.length r b).ok = 1 ∧
      coreTypeSchema.decode b = some (typeAt b.length r b).t := by
  unfold CanonicalCoreTypeAt CanonicalObjectAt coreTypeSchema at h
  dsimp only [prefixTy] at h
  obtain ⟨hdec, hdig, hex⟩ := h
  cases hd : dec0 0 b.length b with
  | error c =>
    rw [hd] at hdec
    exact hdec.elim
  | ok vp =>
    obtain ⟨it, p⟩ := vp
    rw [hd] at hdec hex
    dsimp only [Option.map] at hdec hex
    obtain ⟨he, hck⟩ := hdec
    have hck' := Bool.and_eq_true_iff.mp hck
    have hcls : r.cls = 3 := beq_iff_eq.mp hck'.1
    have hkind : r.kind = coreTypeKind := beq_iff_eq.mp hck'.2
    have hp : p = b.length := beq_iff_eq.mp hex
    have hdig16 : Rcic.TypedRef.deriveDigest 3 16 b = r.digest := by
      have hk16 : coreTypeKind = 16 := rfl
      rw [hcls, hkind, hk16] at hdig
      exact hdig
    have htr : typeAt b.length r b = tvOk (asTy it) unitVal b r.digest := by
      unfold typeAt
      rw [if_neg (by intro hc; exact hc hcls),
          if_neg (by intro hk; exact hk hkind), hd]
      dsimp only
      rw [if_neg (by intro hp'; exact hp' hp),
          if_neg (by intro he'; exact he' he),
          if_neg (by intro hd'; exact hd' hdig16)]
    rw [htr]
    refine ⟨rfl, ?_⟩
    show (prefixTy b).map Prod.fst = some (asTy it)
    unfold prefixTy
    rw [hd]
    rfl

/-- Exact agreement between `typeAt` at the input's own length and
    `CanonicalCoreTypeAt`. -/
theorem typeAt_atLength_iff (r : Ref) (b : String) :
    (typeAt b.length r b).ok = 1 ↔ CanonicalCoreTypeAt r b :=
  ⟨typeAt_atLength_accepts, fun h => (typeAt_atLength_complete h).1⟩

/-- Completeness of `valueAt` at the input's own length (converse of
    `valueAt_atLength_accepts`): every `ValueAt T vbytes` makes the carrier's
    `valueAt` accept. -/
theorem valueAt_atLength_complete (T : BoundCoreType) (vbytes : String)
    (h : ValueAt T vbytes) :
    (valueAt vbytes.length
      (typeAt T.type_bytes.length T.type_ref T.type_bytes) vbytes).ok = 1 := by
  have ⟨_, ht_dec⟩ := typeAt_atLength_complete T.type_at
  obtain ⟨t, hd, v, hv, hok⟩ := h
  have htt : (typeAt T.type_bytes.length T.type_ref T.type_bytes).t = t :=
    Option.some.inj (ht_dec.symm.trans hd)
  unfold valueBytesAt at hv
  cases hdec : dec0 1 vbytes.length vbytes with
  | error c =>
    rw [hdec] at hv
    exact Option.noConfusion hv
  | ok vp =>
    obtain ⟨it, p⟩ := vp
    rw [hdec] at hv
    dsimp only at hv
    split at hv
    · rename_i hpe
      obtain ⟨hp, he⟩ := hpe
      cases hv
      unfold valueAt
      rw [hdec]
      dsimp only
      rw [if_neg (by intro hp'; exact hp' hp),
          if_neg (by intro he'; exact he' he), htt]
      cases htc : toCore t (asVal it) with
      | none =>
        rw [htc] at hok
        exact Bool.noConfusion hok
      | some cv =>
        rfl
    · exact Option.noConfusion hv

/-- Exact agreement between the carrier's `valueAt` decision at each input's own
    length and `ValueAt T vbytes`. -/
theorem valueAt_atLength_iff (T : BoundCoreType) (vbytes : String) :
    (valueAt vbytes.length
      (typeAt T.type_bytes.length T.type_ref T.type_bytes) vbytes).ok = 1 ↔
      ValueAt T vbytes :=
  ⟨valueAt_atLength_accepts (typeAt_atLength_complete T.type_at).1,
   valueAt_atLength_complete T vbytes⟩

/-! ## The wire bound is necessary: a 1025-element list has no bytes -/

/-- An accepting `decElems` returns exactly `left` elements. -/
theorem decElems_ok_length {cs : Array Char} {kind : Nat} {fuel : Int} :
    ∀ {g : Nat} {left : Int} {iters p q : Nat} {xs : List Item},
      decElems cs g kind fuel left p iters = .ok (xs, q) → 0 ≤ left →
        (xs.length : Int) = left := by
  intro g
  induction g with
  | zero =>
    intro left iters p q xs h _
    simp [decElems] at h
  | succ g ih =>
    intro left iters p q xs h hl
    unfold decElems at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [List.length_nil]
      omega
    · split at h
      · exact Except.noConfusion h
      · obtain ⟨⟨x, q1⟩, _, hf⟩ := Rcic.Scm.Inst.except_bind_eq_ok h
        obtain ⟨⟨xs', q'⟩, hrest, hf2⟩ := Rcic.Scm.Inst.except_bind_eq_ok hf
        have hf2' : Except.ok (x :: xs', q') = Except.ok (xs, q) := hf2
        simp only [Except.ok.injEq, Prod.mk.injEq] at hf2'
        obtain ⟨rfl, -⟩ := hf2'
        have := ih hrest (by omega)
        simp only [List.length_cons]
        omega

/-- A counted list whose count exceeds 1024 is refused: no accepting `decList`. -/
theorem decList_bound_refuse {cs : Array Char} {g kind p q0 : Nat} {fuel n : Int}
    (hn : decNat cs p = .ok (n, q0)) (hbig : 1024 < n) (r : Item × Nat) :
    decList cs g kind fuel p ≠ .ok r := by
  intro h
  cases g with
  | zero => simp only [decList] at h; exact Except.noConfusion h
  | succ g =>
    simp only [decList] at h
    obtain ⟨⟨n', q1⟩, hd, hf⟩ := Rcic.Scm.Inst.except_bind_eq_ok h
    rw [hn] at hd
    simp only [Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    obtain ⟨⟨xs', q'⟩, he, -⟩ := Rcic.Scm.Inst.except_bind_eq_ok hf
    have h1 := decElems_ok_length he (by omega)
    have h2 := Rcic.Scm.Inst.wire_decElems_length_le he
    omega

/-- `dec` at kind 1 that accepts is `decVal` accepting. -/
theorem dec_one_inv {cs : Array Char} {g : Nat} {fuel : Int} {p : Nat} {r : Item × Nat}
    (h : dec cs (g + 1) 1 fuel p = .ok r) : decVal cs g fuel p = .ok r := by
  unfold dec at h
  split at h
  · exact Except.noConfusion h
  · exact h

/-- `decVal` on a `'L'` tag that accepts went through an accepting `decList`. -/
theorem decVal_tagL_ok {cs : Array Char} {g : Nat} {fuel : Int} {p : Nat}
    {r : Item × Nat} (hc : charAt cs p = some 'L')
    (h : decVal cs (g + 1) fuel p = .ok r) :
    ∃ r', decList cs g 1 fuel (p + 1) = .ok r' := by
  unfold decVal at h
  dsimp only at h
  rw [hc] at h
  cases hd : decList cs g 1 fuel (p + 1) with
  | error e => rw [hd] at h; exact Except.noConfusion h
  | ok r' => exact ⟨r', rfl⟩

/-- A list value with 1025 elements: the wire decoder refuses its canonical encoding
    (the 1024-element bound, `[rcic_scm_wire_bound]`), so `valueBytesAt` rejects it. -/
theorem valueBytesAt_list_bound (xs : List Val) (hl : xs.length = 1025) :
    valueBytesAt (encVal (.l xs)) = none := by
  have hEnc : (encVal (.l xs)).toList = 'L' ::
      ((encNat (↑xs.length : Int)).toList ++ (encVals xs).toList) := by
    show (("L" ++ encNat ↑xs.length ++ encVals xs)).toList = _
    simp only [toList_append]; rfl
  have hdrop : (encVal (.l xs)).toList.toArray.toList.drop 0 = 'L' ::
      ((encNat (↑xs.length : Int)).toList ++ (encVals xs).toList) := hEnc
  have hc0 := charAt_head _ 0 'L' _ hdrop
  have hd1 : (encVal (.l xs)).toList.toArray.toList.drop (0 + 1) =
      (encNat (↑xs.length : Int)).toList ++ (encVals xs).toList := drop_succ hdrop
  have hn1 := decNat_encInt (↑xs.length : Int) (by omega)
    ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩ _ (0 + 1) _ hd1
  have hbig : (1024 : Int) < ↑xs.length := by omega
  have key : ∀ (G : Nat) (fuel : Int) (r : Item × Nat),
      dec (encVal (.l xs)).toList.toArray G 1 fuel 0 ≠ .ok r := by
    intro G fuel r h
    cases G with
    | zero => simp [dec] at h
    | succ G =>
      have hv := dec_one_inv h
      cases G with
      | zero => simp [decVal] at hv
      | succ G =>
        obtain ⟨r', hdl⟩ := decVal_tagL_ok hc0 hv
        exact decList_bound_refuse hn1 hbig r' hdl
  unfold valueBytesAt dec0
  dsimp only
  split
  · rename_i it p heq
    exact absurd heq (key _ _ _)
  · rfl

/-- No byte string at all decodes to a 1025-element list value. -/
theorem no_bytes_of_list_bound (xs : List Val) (hl : xs.length = 1025) (b : String) :
    valueBytesAt b ≠ some (.l xs) := by
  intro h
  have he := valueBytesAt_enc h
  rw [← he, valueBytesAt_list_bound xs hl] at h
  exact Option.noConfusion h

/-- `n` copies of the i64 zero, as an intrinsic list. -/
def zerosL : Nat → CoreList .i64
  | 0 => .nil
  | n + 1 => .cons (.i64V 0 ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩) (zerosL n)

theorem zerosL_erase_length : ∀ n, (zerosL n).erase.length = n
  | 0 => rfl
  | n + 1 => by
      simp only [zerosL, CoreList.erase, List.length_cons, zerosL_erase_length n]

/-- The tooth (a PROVEN-FALSE residue): completeness WITHOUT the wire bound fails at
    every bound type whose type is `list i64`. The 1025 zeros are an intrinsic value
    of that type with no `ValueAt` bytes. So `valueAt_complete`'s `dqV` premise is
    necessary, not decorative. -/
theorem valueAt_complete_unbounded_false (T : BoundCoreType) (hT : T.ty = .list .i64) :
    ¬ ∀ cv : CoreVal T.ty, ValueAt T (encVal cv.erase) := by
  rw [hT]
  intro hall
  obtain ⟨_, _, v, hv, _⟩ := hall (.listV (zerosL 1025))
  have hnone := valueBytesAt_list_bound (zerosL 1025).erase (zerosL_erase_length 1025)
  have he : (CoreVal.listV (zerosL 1025)).erase = .l (zerosL 1025).erase := rfl
  rw [he, hnone] at hv
  exact Option.noConfusion hv

/-- The weakened acceptance predicate for the bound control pair: `dqV` with
    only the `.l`/`.r` list-length conjunct removed — the payload check `dqsV`
    is retained untouched, so every element is still `dqV`-checked. -/
def dqV_noListLen : Val → Prop
  | .l xs | .r xs => dqsV xs
  | v => dqV v

/-- Every `zerosL` element is the i64 literal `0`, so the retained payload
    check holds at any length — including 1025. -/
theorem dqsV_zerosL : ∀ n, dqsV (zerosL n).erase := by
  intro n
  induction n with
  | zero => exact trivial
  | succ n ih =>
      exact ⟨⟨by unfold i64Min; omega, by unfold i64Max; omega⟩, ih⟩

/-- Weakened side of the control pair: the SAME `zerosL 1025` input the codec
    refuses satisfies `dqV` minus the length conjunct — the guard, and only
    the guard, is what refuses it. -/
theorem zerosL_dqV_noListLen : dqV_noListLen (.l (zerosL 1025).erase) :=
  dqsV_zerosL 1025

/-- Exact side of the control pair: `dqV` refuses `zerosL 1025` — the dropped
    conjunct is the false one. -/
theorem zerosL_dqV_false : ¬ dqV (.l (zerosL 1025).erase) := by
  intro h
  have hl : (zerosL 1025).erase.length ≤ 1024 := h.1
  rw [zerosL_erase_length] at hl
  omega

/-- The bound tooth is a guard-level split, not a decidability gap: at the same
    `zerosL 1025` input, `dqV` minus the length conjunct is inhabited while
    exact `dqV` is false and the real codec (`valueBytesAt`) returns `none`. -/
theorem zerosL_bound_control :
    dqV_noListLen (.l (zerosL 1025).erase) ∧
      ¬ dqV (.l (zerosL 1025).erase) ∧
      valueBytesAt (encVal (.l (zerosL 1025).erase)) = none :=
  ⟨zerosL_dqV_noListLen, zerosL_dqV_false,
   valueBytesAt_list_bound _ (zerosL_erase_length 1025)⟩

/-- The wire-bound premise is satisfiable (non-vacuity witness): the i64 value 42. -/
theorem dqV_witness :
    dqV (CoreVal.i64V 42 ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩).erase := by
  show inI64 42
  exact ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩

end Rcic.Scm.ValueAtComplete

#print axioms Rcic.Scm.ValueAtComplete.catEncNat_len_ge
#print axioms Rcic.Scm.ValueAtComplete.valGas_lt_encLen
#print axioms Rcic.Scm.ValueAtComplete.valsGas_le_encValsLen
#print axioms Rcic.Scm.ValueAtComplete.valGas_le_gasFor
#print axioms Rcic.Scm.ValueAtComplete.valFuel_le_len
#print axioms Rcic.Scm.ValueAtComplete.valueBytesAt_enc
#print axioms Rcic.Scm.ValueAtComplete.valueAt_complete
#print axioms Rcic.Scm.ValueAtComplete.semanticValue_of_core
#print axioms Rcic.Scm.ValueAtComplete.semanticValue_of_core_dec
#print axioms Rcic.Scm.ValueAtComplete.valueAt_sound
#print axioms Rcic.Scm.ValueAtComplete.valueAt_iff
#print axioms Rcic.Scm.ValueAtComplete.typeAt_atLength_complete
#print axioms Rcic.Scm.ValueAtComplete.typeAt_atLength_iff
#print axioms Rcic.Scm.ValueAtComplete.valueAt_atLength_complete
#print axioms Rcic.Scm.ValueAtComplete.valueAt_atLength_iff
#print axioms Rcic.Scm.ValueAtComplete.decElems_ok_length
#print axioms Rcic.Scm.ValueAtComplete.decList_bound_refuse
#print axioms Rcic.Scm.ValueAtComplete.dec_one_inv
#print axioms Rcic.Scm.ValueAtComplete.decVal_tagL_ok
#print axioms Rcic.Scm.ValueAtComplete.valueBytesAt_list_bound
#print axioms Rcic.Scm.ValueAtComplete.no_bytes_of_list_bound
#print axioms Rcic.Scm.ValueAtComplete.zerosL
#print axioms Rcic.Scm.ValueAtComplete.zerosL_erase_length
#print axioms Rcic.Scm.ValueAtComplete.valueAt_complete_unbounded_false
#print axioms Rcic.Scm.ValueAtComplete.dqV_noListLen
#print axioms Rcic.Scm.ValueAtComplete.dqsV_zerosL
#print axioms Rcic.Scm.ValueAtComplete.zerosL_dqV_noListLen
#print axioms Rcic.Scm.ValueAtComplete.zerosL_dqV_false
#print axioms Rcic.Scm.ValueAtComplete.zerosL_bound_control
#print axioms Rcic.Scm.ValueAtComplete.dqV_witness
