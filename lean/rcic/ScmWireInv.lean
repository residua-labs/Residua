/- Wire codec inverses — 06 §19 `→` direction, the decode-of-encode layer.

  For every encoder in `ScmWire`/`ScmConfigWire`/`ScmBoundTV`/`ScmBoundProgram`
  (`encTy`, `encVal`, `encExpr`, `encItem`/`encItems`, `encTagged`, `encCfg`,
  `encFin`, `cxEnc`, `objEnc`) this module proves that the corresponding
  decoder (`decTy`, `decVal`, `decExpr`, `dec`/`decSeq`/`decList`/`decElems`,
  `decTagged`, `decCfg`, `decFin`, `cxDec`, `dec0`, `objDec`) reads the encoded
  bytes back to the same object and consumes them exactly.  All inverses are
  stated at a byte position `p` with a `rest` tail so they compose inside the
  schema-driven decoders.

  Bounds the carrier decoders impose, carried as premises:
  - `g`: structural gas — `wX x ≤ g` frames are needed (`gasFor` supplies them
    since `wX x ≤ 4 * bytes + 4`).
  - `fuel`: `dec`-depth — `fX x ≤ fuel` (`fX x ≤ bytes` always).
  - `m`: every counted list and every length-prefixed string must have length
    `≤ 1024` (the carrier's `decElems` bound and the 24-position number scan).
  - `dq`: `decNat`-routed naturals nonnegative and all integers in i64 range.
-/
import rcic.ScmBoundConfig
import rcic.ScmBoundCoreTV
import rcic.ScmInstantiate

namespace Rcic.Scm.Wire
open Rcic.Scm Rcic.Scm.CfgWire Rcic.Scm.BoundTV Rcic.Scm.BoundCfg Rcic.Scm.BoundProg
  Rcic.BoundObject Rcic.Scm.Inst

/-! ## Position helpers -/

theorem charAt_of_drop {cs : Array Char} {p : Nat} {c : Char} {r : List Char}
    (h : cs.toList.drop p = c :: r) : charAt cs p = some c := by
  unfold charAt
  rw [Array.getElem?_eq_getElem?_toList, ← List.head?_drop, h, List.head?_cons]

theorem getElem!_of_drop {cs : Array Char} {p : Nat} {c : Char} {r : List Char}
    (h : cs.toList.drop p = c :: r) : cs[p]! = c := by
  rw [getElem!_def, Array.getElem?_eq_getElem?_toList, ← List.head?_drop, h]
  rfl

theorem p_lt_size {cs : Array Char} {p : Nat} {c : Char} {r : List Char}
    (h : cs.toList.drop p = c :: r) : p < cs.size := by
  have hl : cs.toList[p]? = some c := by rw [← List.head?_drop, h]; rfl
  obtain ⟨hp, _⟩ := List.getElem?_eq_some_iff.mp hl
  rwa [Array.length_toList] at hp

theorem drop_succ {l : List Char} {p : Nat} {c : Char} {r : List Char}
    (h : l.drop p = c :: r) : l.drop (p + 1) = r := by
  have : l.drop (p + 1) = (l.drop p).drop 1 := by rw [← List.drop_drop]
  rw [this, h]; rfl

theorem toList_append (a b : String) : (a ++ b).toList = a.toList ++ b.toList := by
  show (a ++ b).data = a.toList ++ b.toList
  rw [String.data_append]; rfl

/-- The bounded scan finds `c` at the end of a `c`-free prefix. -/
theorem scanTo_found : ∀ (s : List Char) (cs : Array Char) (c : Char) (p m : Nat)
    (rest : List Char),
    cs.toList.drop p = s ++ c :: rest → (∀ c' ∈ s, c' ≠ c) → s.length < m →
    scanTo cs c p m = (p + s.length : Int) := by
  intro s
  induction s with
  | nil =>
    intro cs c p m rest h _ hm
    cases m with
    | zero => omega
    | succ m =>
      rw [scanTo, if_neg (by have := p_lt_size h; omega)]
      show (if cs[p]! = c then (p : Int) else scanTo cs c (p + 1) m) = ↑p + ↑[].length
      rw [if_pos (getElem!_of_drop h)]
      simp
  | cons d s ih =>
    intro cs c p m rest h hd hm
    cases m with
    | zero => omega
    | succ m =>
      rw [scanTo, if_neg (by have := p_lt_size h; omega)]
      show (if cs[p]! = c then (p : Int) else scanTo cs c (p + 1) m) = _
      rw [getElem!_of_drop h, if_neg (hd d (List.mem_cons_self _ _))]
      have h' : cs.toList.drop (p + 1) = s ++ c :: rest := drop_succ h
      rw [ih cs c (p + 1) m rest h' (fun c' hc' => hd c' (List.mem_cons_of_mem _ hc'))
        (by rw [List.length_cons] at hm; omega : s.length < m)]
      rw [List.length_cons]
      omega

/-- `sliceStr` over a known prefix. -/
theorem sliceStr_take {cs : Array Char} {a : Nat} {s rest : List Char}
    (h : cs.toList.drop a = s ++ rest) : sliceStr cs a (a + s.length) = String.mk s := by
  unfold sliceStr
  rw [h, Nat.add_sub_cancel_left, List.take_left]

theorem digit_ne_semi {c : Char} (h : c.isDigit = true) : c ≠ ';' := by
  intro h'; subst h'; revert h; decide

theorem digit_ne_colon {c : Char} (h : c.isDigit = true) : c ≠ ':' := by
  intro h'; subst h'; revert h; decide

theorem digit_ne_dash {c : Char} (h : c.isDigit = true) : c ≠ '-' := by
  intro h'; subst h'; revert h; decide

/-! ## `parseI64` / `decNum` / `decNat` / `decStr` inverses -/

/-- The Int-fold inside `parseI64` equals `numOf` of the same digits. -/
theorem numFold_int : ∀ (ds : List Char) (a : Nat),
    (ds.foldl (fun (acc : Int) c => acc * 10 + ((c.toNat - 48 : Nat) : Int)) (a : Int) : Int) =
      (ds.foldl (fun acc c => acc * 10 + digitVal c) a : Nat) := by
  intro ds
  induction ds with
  | nil => intro a; simp
  | cons c ds ih =>
    intro a
    simp only [List.foldl_cons]
    have hacc : ((a : Int) * 10 + ((c.toNat - 48 : Nat) : Int)) =
        ((a * 10 + digitVal c : Nat) : Int) := by simp [digitVal]
    rw [hacc, ih (a * 10 + digitVal c)]

/-- `parseI64` on a nonempty digit string yields `numOf` (nonneg path). -/
theorem parseI64_digits (ds : List Char) (hne : ds ≠ [])
    (hall : ds.all Char.isDigit = true) (hdash : ds.head? ≠ some '-')
    (hv : inI64 (numOf ds : Int)) :
    ∃ h', parseI64 (String.mk ds) = .returned (.i64V (numOf ds : Int) h') := by
  have hmk : ∀ ds : List Char, (String.mk ds).toList = ds := fun _ => rfl
  unfold parseI64
  dsimp only
  rw [hmk]
  have hneg : (ds.head? == some '-') = false := by
    cases hh : ds.head? with
    | none => rfl
    | some c =>
      rw [hh] at hdash
      have hc : c ≠ '-' := fun h' => hdash (by rw [h'])
      show (c == '-') = false
      exact beq_false_of_ne hc
  rw [hneg]
  rw [if_neg (by decide : ¬ (false = true)), if_neg (by decide : ¬ (false = true))]
  have he : ds.isEmpty = false := by
    cases ds with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  rw [if_neg (by simp [he, hall])]
  show ∃ h', checkedI64 (ds.foldl (fun (acc : Int) c => acc * 10 +
      ((c.toNat - 48 : Nat) : Int)) (↑(0:Nat))) = LawResult.returned (CoreVal.i64V ↑(numOf ds) h')
  rw [numFold_int]
  show ∃ h', checkedI64 ↑(numOf ds) = LawResult.returned (CoreVal.i64V ↑(numOf ds) h')
  unfold checkedI64
  rw [dif_pos hv]
  exact ⟨hv, rfl⟩

/-- `parseI64` on `'-' :: digits` yields `-numOf` (negative path). -/
theorem parseI64_neg_digits (ds : List Char) (hne : ds ≠ [])
    (hall : ds.all Char.isDigit = true) (hv : inI64 (-(numOf ds : Int))) :
    ∃ h', parseI64 (String.mk ('-' :: ds)) = .returned (.i64V (-(numOf ds : Int)) h') := by
  have hmk : ∀ ds : List Char, (String.mk ds).toList = ds := fun _ => rfl
  unfold parseI64
  dsimp only
  rw [hmk]
  have hneg : (('-' :: ds).head? == some '-') = true := rfl
  rw [hneg]
  rw [if_pos (by decide : true = true), if_pos (by decide : true = true)]
  show ∃ h', (if ds.isEmpty || !(ds.all Char.isDigit)
        then .raised "malformed_integer"
        else checkedI64 (-(ds.foldl (fun (acc : Int) c => acc * 10 +
            ((c.toNat - 48 : Nat) : Int)) 0))) =
      LawResult.returned (CoreVal.i64V (-↑(numOf ds)) h')
  have he : ds.isEmpty = false := by
    cases ds with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  rw [if_neg (by simp [he, hall])]
  show ∃ h', checkedI64 (-(ds.foldl (fun (acc : Int) c => acc * 10 +
      ((c.toNat - 48 : Nat) : Int)) (↑(0:Nat)))) = LawResult.returned (CoreVal.i64V (-↑(numOf ds)) h')
  rw [numFold_int]
  show ∃ h', checkedI64 (-↑(numOf ds)) = LawResult.returned (CoreVal.i64V (-↑(numOf ds)) h')
  unfold checkedI64
  rw [dif_pos hv]
  exact ⟨hv, rfl⟩

theorem toString_head_ne_dash (n : Nat) : (toString n).data.head? ≠ some '-' := by
  cases hl : (toString n).data with
  | nil => simp
  | cons c _ =>
    rw [List.head?_cons]
    intro h'
    have hd : c.isDigit = true := toString_digits n c (by rw [hl]; exact List.mem_cons_self _ _)
    exact digit_ne_dash hd (Option.some.inj h')

theorem toString_all_digit (n : Nat) : (toString n).data.all Char.isDigit = true :=
  List.all_eq_true.mpr (toString_digits n)

/-- `decNum` reads an `encNat`-shaped number back. -/
theorem decNum_enc (s : List Char) (term : Char) (cs : Array Char) (p : Nat)
    (rest : List Char) (n : Int)
    (h : cs.toList.drop p = s ++ term :: rest)
    (hfree : ∀ c' ∈ s, c' ≠ term)
    (hs : s.length < 24)
    (hp : ∃ h', parseI64 (String.mk s) = .returned (.i64V n h')) :
    decNum cs p term = .ok (n, p + s.length + 1) := by
  unfold decNum
  rw [scanTo_found s cs term p 24 rest h hfree hs]
  dsimp only
  rw [if_neg (by omega), if_neg (by omega)]
  rw [← Int.natCast_add, Int.toNat_ofNat, sliceStr_take h]
  obtain ⟨h', hp'⟩ := hp
  rw [hp']

/-- `encNat` reads back under `decNum` (i64-in-range premise). -/
theorem decNum_encNat (n : Int) (hn : inI64 n) (cs : Array Char) (p : Nat)
    (rest : List Char)
    (h : cs.toList.drop p = (toString n).toList ++ ';' :: rest)
    (hs : (toString n).toList.length < 24) :
    decNum cs p ';' = .ok (n, p + (toString n).toList.length + 1) := by
  cases n with
  | ofNat k =>
    have hd : ∀ c' ∈ (toString k).toList, c' ≠ ';' := fun c' hc' =>
      digit_ne_semi (toString_digits k c' hc')
    apply decNum_enc (toString k).toList ';' cs p rest _ h hd hs
    have hv : inI64 (numOf (toString k).toList : Int) := by
      show inI64 ↑(numOf (toString k).data)
      rw [numOf_toString]; exact hn
    obtain ⟨h', hp⟩ := parseI64_digits _ (toString_ne_nil k)
      (toString_all_digit k) (toString_head_ne_dash k) hv
    have e : (↑(numOf (toString k).data) : Int) = Int.ofNat k :=
      congrArg (fun v : Nat => (v : Int)) (numOf_toString k)
    have eqv : CoreVal.i64V ↑(numOf (toString k).data) h' =
        CoreVal.i64V (Int.ofNat k) hn := by
      congr
    rw [eqv] at hp
    exact ⟨hn, hp⟩
  | negSucc k =>
    have hs' : (toString (Int.negSucc k)).data = '-' :: (toString (k + 1)).data := rfl
    have hd : ∀ c' ∈ (toString (Int.negSucc k)).toList, c' ≠ ';' := by
      show ∀ c' ∈ '-' :: (toString (k + 1)).data, c' ≠ ';'
      intro c' hc'
      cases hc' with
      | head => decide
      | tail _ hm => exact digit_ne_semi (toString_digits (k + 1) c' hm)
    apply decNum_enc _ ';' cs p rest _ h hd hs
    have hv : inI64 (-(numOf (toString (k + 1)).toList : Int)) := by
      show inI64 (-↑(numOf (toString (k + 1)).data))
      rw [numOf_toString]
      have : (-(↑(k + 1) : Int)) = Int.negSucc k := by
        rw [Int.negSucc_eq]; push_cast; omega
      rwa [this]
    obtain ⟨h', hp⟩ := parseI64_neg_digits _ (toString_ne_nil (k + 1))
      (toString_all_digit (k + 1)) hv
    have e : (-(↑(numOf (toString (k + 1)).data) : Int)) = Int.negSucc k := by
      rw [numOf_toString (k + 1), Int.negSucc_eq]; push_cast; rfl
    have eqv : CoreVal.i64V (-↑(numOf (toString (k + 1)).data)) h' =
        CoreVal.i64V (Int.negSucc k) hn := by
      congr
    rw [eqv] at hp
    exact ⟨hn, hp⟩

/-- `decNat` reads a Nat's `encNat` digits. -/
theorem decNat_enc (n : Nat) (cs : Array Char) (p : Nat) (rest : List Char)
    (h : cs.toList.drop p = (toString n).toList ++ ';' :: rest)
    (hs : (toString n).toList.length < 24)
    (hi : inI64 (n : Int)) :
    decNat cs p = .ok ((n : Int), p + (toString n).toList.length + 1) := by
  unfold decNat
  rw [decNum_encNat (n : Int) hi cs p rest h hs]
  show (if ((n : Int) < 0) then wErr "number"
        else Except.ok ((n : Int), p + (toString (n : Int)).toList.length + 1)) = _
  rw [if_neg (by omega : ¬ ((n : Int) < 0))]
  rfl

/-- `l.drop`-advance across a known prefix. -/
theorem drop_append_advance {l : List Char} {p : Nat} {s r : List Char}
    (h : l.drop p = s ++ r) : l.drop (p + s.length) = r := by
  have : l.drop (p + s.length) = (l.drop p).drop s.length := by
    rw [← List.drop_drop]
  rw [this, h]
  simp

/-- Digit-count bound: `toDigitsCore` emits at most `k` digits when
    `n < 10^k`. -/
theorem toDigitsCore_len (fuel : Nat) : ∀ (n : Nat) (ds : List Char) (k : Nat),
    n < fuel → n < 10 ^ k → 0 < k →
    (Nat.toDigitsCore 10 fuel n ds).length ≤ ds.length + k := by
  induction fuel with
  | zero => intro n ds k hf _ _; omega
  | succ f ih =>
    intro n ds k hf hk hk0
    show ((if n / 10 = 0 then (n % 10).digitChar :: ds
        else Nat.toDigitsCore 10 f (n / 10) ((n % 10).digitChar :: ds)).length ≤
        ds.length + k)
    by_cases h0 : n / 10 = 0
    · rw [if_pos h0]
      simp only [List.length_cons]
      omega
    · rw [if_neg h0]
      have h10 : 10 ≤ n := by
        by_cases h' : n < 10
        · have : n / 10 = 0 := Nat.div_eq_of_lt h'
          omega
        · omega
      have hd : n / 10 * 10 ≤ n := Nat.div_mul_le_self n 10
      have hnf : n / 10 < f := by omega
      have hk1 : 1 < k := by
        by_cases kz : k = 0
        · subst kz; simp at hk; omega
        · by_cases ko : k = 1
          · subst ko; simp at hk; omega
          · omega
      have hk2 : n / 10 < 10 ^ (k - 1) := by
        have e : (10 : Nat) ^ k = 10 ^ (k - 1) * 10 := by
          obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 :=
            ⟨k - 1, (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm⟩
          subst hk'
          rw [Nat.pow_succ, Nat.add_sub_cancel]
        omega
      have hlen := ih (n / 10) ((n % 10).digitChar :: ds) (k - 1) hnf hk2
        (by omega)
      rw [List.length_cons] at hlen
      omega

/-- `toString n` for `n < 10^k` has at most `k` digits. -/
theorem toString_len_le (n k : Nat) (hk : n < 10 ^ k) (hk0 : 0 < k) :
    (toString n).toList.length ≤ k := by
  show (Nat.toDigits 10 n).length ≤ k
  show (Nat.toDigitsCore 10 (n + 1) n []).length ≤ k
  have := toDigitsCore_len (n + 1) n ([] : List Char) k (by omega) hk hk0
  simpa using this

/-- The decoder's 24-position scan always reaches a `≤ 1024` count. -/
theorem toString_len_lt24 (n : Nat) (h : n ≤ 1024) :
    (toString n).toList.length < 24 := by
  have : (toString n).toList.length ≤ 4 := toString_len_le n 4 (by omega) (by omega)
  omega

/-- `encNat` on an i64 value stays under the 24-position scan bound. -/
theorem toString_int_len_lt24 (n : Int) (hn : inI64 n) :
    (toString n).toList.length < 24 := by
  cases n with
  | ofNat m =>
    have hm : m < 10 ^ 19 := by
      have hm2 : (m : Int) ≤ i64Max := hn.2
      unfold i64Max at hm2
      omega
    have := toString_len_le m 19 hm (by omega)
    show (toString m).toList.length < 24
    omega
  | negSucc m =>
    have hm : m + 1 < 10 ^ 19 := by
      obtain ⟨hlo, hhi⟩ := hn
      unfold i64Min at hlo
      have : -(↑(m + 1) : Int) = Int.negSucc m := by
        rw [Int.negSucc_eq]; push_cast; rfl
      omega
    have h1 : (toString (m + 1)).toList.length ≤ 19 :=
      toString_len_le (m + 1) 19 hm (by omega)
    show (toString (Int.negSucc m)).toList.length < 24
    rw [show (toString (Int.negSucc m)).toList = '-' :: (toString (m + 1)).toList
      from rfl]
    simp only [List.length_cons]
    omega

/-- `decStr` reads an `encStr` string back. -/
theorem decStr_enc (x : String) (cs : Array Char) (p : Nat) (rest : List Char)
    (h : cs.toList.drop p =
      (toString x.length).toList ++ (':' :: (x.toList ++ rest)))
    (hs : (toString x.length).toList.length < 24)
    (hx : x.length ≤ 1024) :
    decStr cs p = .ok (x, p + (toString x.length).toList.length + 1 + x.length) := by
  unfold decStr
  have hlen : (toString x.length).toList.length + 1 + x.toList.length ≤ cs.toList.length - p := by
    have hl : (cs.toList.drop p).length =
        ((toString x.length).toList ++ ':' :: (x.toList ++ rest)).length := by rw [h]
    rw [List.length_drop] at hl
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    omega
  have hnum : decNum cs p ':' =
      .ok ((x.length : Int), p + (toString x.length).toList.length + 1) := by
    apply decNum_enc (toString x.length).toList ':' cs p (x.toList ++ rest)
      (x.length : Int) h (fun c' hc' => digit_ne_colon (toString_digits x.length c' hc')) hs
    have hv : inI64 (numOf (toString x.length).toList : Int) := by
      show inI64 ↑(numOf (toString x.length).data)
      rw [numOf_toString]
      refine ⟨?_, ?_⟩
      · have : i64Min ≤ (0 : Int) := by decide
        omega
      · show (↑x.length : Int) ≤ i64Max
        unfold i64Max
        have : (x.length : Int) ≤ 1024 := by exact_mod_cast hx
        omega
    obtain ⟨h', hp⟩ := parseI64_digits _ (toString_ne_nil x.length)
      (toString_all_digit x.length) (toString_head_ne_dash x.length) hv
    have e : (↑(numOf (toString x.length).data) : Int) = (↑x.length : Int) :=
      congrArg (fun v : Nat => (v : Int)) (numOf_toString x.length)
    have hiv : inI64 (↑x.length : Int) := ⟨by
      have : i64Min ≤ (0 : Int) := by decide
      omega, by
      show (↑x.length : Int) ≤ i64Max
      unfold i64Max
      have : (x.length : Int) ≤ 1024 := by exact_mod_cast hx
      omega⟩
    have eqv : CoreVal.i64V ↑(numOf (toString x.length).data) h' =
        CoreVal.i64V (↑x.length : Int) hiv := by
      congr
    rw [eqv] at hp
    exact ⟨hiv, hp⟩
  rw [hnum]
  show (if ((x.length : Int) < 0) then wErr "number"
        else if p + (toString x.length).toList.length + 1 + ((x.length : Int)).toNat > cs.size
          then wErr "truncated"
          else Except.ok (sliceStr cs (p + (toString x.length).toList.length + 1)
            (p + (toString x.length).toList.length + 1 + ((x.length : Int)).toNat),
            p + (toString x.length).toList.length + 1 + ((x.length : Int)).toNat)) = _
  rw [if_neg (by omega : ¬ ((x.length : Int) < 0))]
  have hto : ((x.length : Int)).toNat = x.length := Int.toNat_ofNat _
  rw [hto]
  have hsize : p + (toString x.length).toList.length + 1 + x.length ≤ cs.size := by
    have hcl : cs.toList.length = cs.size := Array.length_toList
    have hxl : x.toList.length = x.length := rfl
    omega
  rw [if_neg (by omega : ¬ (p + (toString x.length).toList.length + 1 + x.length > cs.size))]
  have hq : cs.toList.drop (p + (toString x.length).toList.length + 1) =
      x.toList ++ rest := by
    have h1 := drop_append_advance (l := cs.toList) (p := p)
      (s := (toString x.length).toList) (r := ':' :: (x.toList ++ rest)) h
    show cs.toList.drop ((p + (toString x.length).toList.length) + 1) = x.toList ++ rest
    exact drop_append_advance (l := cs.toList) (p := p + (toString x.length).toList.length)
      (s := [':']) (r := x.toList ++ rest) h1
  show Except.ok (sliceStr cs (p + (toString x.length).toList.length + 1)
      (p + (toString x.length).toList.length + 1 + x.toList.length),
      p + (toString x.length).toList.length + 1 + x.toList.length) = _
  rw [sliceStr_take hq]
  rfl

/-! ## Concatenated encodings -/

/-- `String.join` of element encodings. -/
def catEnc (f : α → String) (xs : List α) : String := String.join (xs.map f)

theorem catEnc_toList (f : α → String) (xs : List α) :
    (catEnc f xs).toList = xs.foldr (fun x acc => (f x).toList ++ acc) [] := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    show (String.join ((f x) :: xs'.map f)).toList =
        (f x).toList ++ xs'.foldr (fun x acc => (f x).toList ++ acc) []
    have hj : ∀ ss : List String, (String.join ss).data = ss.flatMap String.data := by
      intro ss; exact join_data ss
    rw [← ih]
    show (String.join ((f x) :: xs'.map f)).data =
        (f x).data ++ (String.join (xs'.map f)).data
    rw [hj, hj]
    rfl

theorem catEnc_cons (f : α → String) (x : α) (xs : List α) :
    (catEnc f (x :: xs)).toList = (f x).toList ++ (catEnc f xs).toList := by
  simp only [catEnc_toList]; rfl

theorem catEnc_len (f : α → String) (xs : List α) :
    (catEnc f xs).toList.length =
    xs.foldr (fun x acc => (f x).toList.length + acc) 0 := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    rw [catEnc_cons]
    simp only [List.length_append, List.foldr_cons, ih]

theorem catEnc_nil (f : α → String) : (catEnc f []).toList = [] := rfl

/-! ## Gas and fuel measures

Every nested decoder call decrements the gas `g` once per `dec`/`decList`/
`decElems`/`decSeq` level and the fuel once per `dec` item. The measures
below bound the requirement of a decoder accepting an encoded value. -/

mutual
/-- Gas needed by `decTy` to accept `encTy t`. -/
def tyGas : CoreTy → Nat
  | .i64 | .bool | .str | .bytes => 1
  | .list t => tyGas t + 2
  | .pair a b => max (tyGas a) (tyGas b) + 2
  | .sum ts => tysGas ts + ts.length + 4
  | .record fs => fieldTysGas fs + fs.length + 4
/-- Gas needed by `decList` over element kind `0` for `ts`. -/
def tysGas : List CoreTy → Nat
  | [] => 0
  | t :: ts => max (tyGas t) (tysGas ts)
/-- Gas needed by `decList` over element kind `8` for `fs`. -/
def fieldTysGas : List (String × CoreTy) → Nat
  | [] => 0
  | (_, t) :: fs => max (tyGas t) (fieldTysGas fs)
end

mutual
/-- Fuel needed by `decTy` to accept `encTy t`. -/
def tyFuel : CoreTy → Nat
  | .i64 | .bool | .str | .bytes => 0
  | .list t => tyFuel t + 1
  | .pair a b => max (tyFuel a) (tyFuel b) + 1
  | .sum ts => tysFuel ts + 1
  | .record fs => fieldTysFuel fs + 2
def tysFuel : List CoreTy → Nat
  | [] => 0
  | t :: ts => max (tyFuel t) (tysFuel ts)
def fieldTysFuel : List (String × CoreTy) → Nat
  | [] => 0
  | (_, t) :: fs => max (tyFuel t) (fieldTysFuel fs)
end

mutual
/-- Gas needed by `decVal` to accept `encVal v`. -/
def valGas : Val → Nat
  | .i _ | .b _ | .s _ => 1
  | .y bs => bs.length + 4
  | .l xs | .r xs => valsGas xs + xs.length + 4
  | .p a b => max (valGas a) (valGas b) + 2
  | .j _ x => valGas x + 2
def valsGas : List Val → Nat
  | [] => 0
  | x :: xs => max (valGas x) (valsGas xs)
end

mutual
/-- Fuel needed by `decVal` to accept `encVal v`. -/
def valFuel : Val → Nat
  | .i _ | .b _ | .s _ => 0
  | .y _ => 1
  | .l xs | .r xs => valsFuel xs + 1
  | .p a b => max (valFuel a) (valFuel b) + 1
  | .j _ x => valFuel x + 1
def valsFuel : List Val → Nat
  | [] => 0
  | x :: xs => max (valFuel x) (valsFuel xs)
end

mutual
/-- Gas needed by `decExpr` to accept `encExpr e` at its schema. -/
def exprGas : RawExpr → Nat
  | .lit x t => max (valGas x) (tyGas t) + 5
  | .var _ => 3
  | .letE a b | .pair a b | .cons a b => max (exprGas a) (exprGas b) + 5
  | .ifE c th el => max (exprGas c) (max (exprGas th) (exprGas el)) + 6
  | .fst a | .snd a => exprGas a + 4
  | .inj _ ts a => max (tysGas ts + ts.length + 3) (exprGas a + 1) + 5
  | .matchE s bs => max (exprGas s + 1) (exprsGas bs + bs.length + 3) + 4
  | .recordE keys fs =>
      max (keys.length + 3) (exprsGas fs + fs.length + 3) + 4
  | .field r _ => exprGas r + 5
  | .nil t => tyGas t + 4
  | .fold l i b => max (exprGas l) (max (exprGas i) (exprGas b)) + 6
  | .fix i l s st => max (exprGas i) (max (exprGas l) (max (exprGas s) (exprGas st))) + 7
  | .prim _ args => max 1 (exprsGas args + args.length + 3) + 4
  | .call _ args => exprsGas args + args.length + 4
  | .raise _ p t => max 1 (max (exprGas p + 1) (tyGas t + 1)) + 5
  | .handle _ b h => max 1 (max (exprGas b + 1) (exprGas h + 1)) + 5
  | .unknown _ => 1
def exprsGas : List RawExpr → Nat
  | [] => 0
  | e :: es => max (exprGas e) (exprsGas es)
end

mutual
/-- Deep check that `e` has no `.unknown` leaf (those encode to `""` and are
    not decodable). -/
def noUnknown : RawExpr → Bool
  | .unknown _ => false
  | .lit _ _ | .var _ | .nil _ | .fst _ | .snd _ | .field _ _ => true
  | .letE a b | .pair a b | .cons a b | .handle _ a b => noUnknown a && noUnknown b
  | .ifE c th el | .fold c th el => noUnknown c && noUnknown th && noUnknown el
  | .inj _ _ a => noUnknown a
  | .matchE s bs => noUnknown s && noUnknowns bs
  | .recordE _ fs => noUnknowns fs
  | .fix i l s st => noUnknown i && noUnknown l && noUnknown s && noUnknown st
  | .prim _ args => noUnknowns args
  | .call _ args => noUnknowns args
  | .raise _ p _ => noUnknown p
def noUnknowns : List RawExpr → Bool
  | [] => true
  | e :: es => noUnknown e && noUnknowns es
end

mutual
/-- Fuel needed by `decExpr` to accept `encExpr e` at its schema. -/
def exprFuel : RawExpr → Nat
  | .lit x t => max (valFuel x) (tyFuel t) + 1
  | .var _ => 0
  | .letE a b | .pair a b | .cons a b => max (exprFuel a) (exprFuel b) + 1
  | .ifE c th el => max (exprFuel c) (max (exprFuel th) (exprFuel el)) + 1
  | .fst a | .snd a => exprFuel a + 1
  | .inj _ ts a => max (tysFuel ts + 1) (exprFuel a + 1)
  | .matchE s bs => max (exprFuel s + 1) (exprsFuel bs + 1)
  | .recordE _ fs => max 1 (exprsFuel fs + 1)
  | .field r _ => exprFuel r + 1
  | .nil t => tyFuel t + 1
  | .fold l i b => max (exprFuel l) (max (exprFuel i) (exprFuel b)) + 1
  | .fix i l s st => max (exprFuel i) (max (exprFuel l) (max (exprFuel s) (exprFuel st))) + 1
  | .prim _ args => max 1 (exprsFuel args + 1)
  | .call _ args => exprsFuel args + 1
  | .raise _ p t => max 1 (max (exprFuel p + 1) (tyFuel t + 1))
  | .handle _ b h => max 1 (max (exprFuel b + 1) (exprFuel h + 1))
  | .unknown _ => 0
def exprsFuel : List RawExpr → Nat
  | [] => 0
  | e :: es => max (exprFuel e) (exprsFuel es)
end

/-- `encTy` on a list of types (`encTys`) is `catEnc encTy`. -/
theorem encTys_catEnc (ts : List CoreTy) :
    (encTys ts).toList = (catEnc encTy ts).toList := by
  induction ts with
  | nil => rfl
  | cons t ts' ih =>
    show (encTy t ++ encTys ts').toList = (catEnc encTy (t :: ts')).toList
    rw [catEnc_cons]
    rw [show (encTy t ++ encTys ts').toList = (encTy t).toList ++ (encTys ts').toList by
      simp [String.append, String.toList, String.data]]
    rw [ih]

theorem encVals_catEnc (xs : List Val) :
    (encVals xs).toList = (catEnc encVal xs).toList := by
  induction xs with
  | nil => rfl
  | cons x xs' ih =>
    show (encVal x ++ encVals xs').toList = (catEnc encVal (x :: xs')).toList
    rw [catEnc_cons]
    rw [show (encVal x ++ encVals xs').toList = (encVal x).toList ++ (encVals xs').toList by
      simp [String.append, String.toList, String.data]]
    rw [ih]

theorem encExprs_catEnc (es : List RawExpr) :
    (encExprs es).toList = (catEnc encExpr es).toList := by
  induction es with
  | nil => rfl
  | cons e es' ih =>
    show (encExpr e ++ encExprs es').toList = (catEnc encExpr (e :: es')).toList
    rw [catEnc_cons]
    rw [show (encExpr e ++ encExprs es').toList = (encExpr e).toList ++ (encExprs es').toList by
      simp [String.append, String.toList, String.data]]
    rw [ih]

theorem encFieldTys_catEnc (fs : List (String × CoreTy)) :
    (encFieldTys fs).toList =
    (catEnc (fun ft => encStr ft.1 ++ encTy ft.2) fs).toList := by
  induction fs with
  | nil => rfl
  | cons ft fs' ih =>
    show (encStr ft.1 ++ encTy ft.2 ++ encFieldTys fs').toList =
        (catEnc _ (ft :: fs')).toList
    rw [catEnc_cons]
    rw [show (encStr ft.1 ++ encTy ft.2 ++ encFieldTys fs').toList =
        (encStr ft.1 ++ encTy ft.2).toList ++ (encFieldTys fs').toList by
      simp [String.append, String.toList, String.data]]
    rw [ih]

theorem encStr_catEnc (ss : List String) :
    (String.join (ss.map encStr)).toList = (catEnc encStr ss).toList := rfl

theorem encNat_catEnc (ns : List Int) :
    (String.join (ns.map encNat)).toList = (catEnc encNat ns).toList := rfl

/-! ## `charAt` on an encoded prefix -/

theorem charAt_head (cs : Array Char) (p : Nat) (c : Char) (rest : List Char)
    (h : cs.toList.drop p = c :: rest) : charAt cs p = some c := by
  unfold charAt
  rw [Array.getElem?_eq_getElem?_toList]
  have hd : (cs.toList.drop p)[0]? = some c := by simp [h]
  have : cs.toList[p]? = (cs.toList.drop p)[0]? := by
    show cs.toList[p + 0]? = _
    exact (List.getElem?_drop ..).symm
  rw [this]; exact hd

/-! ## `dec` dispatch wrappers

`dec cs (g+1) kind fuel p` unfolds to `if fuel < 0` then a match on `kind`;
each wrapper instantiates the literal kind and an already-established
subdecoder result. -/

theorem dec_zero (cs : Array Char) (g : Nat) (fuel : Int) (p q : Nat) (it : Item)
    (hg : decTy cs g fuel p = .ok (it, q)) (hf : ¬ fuel < 0) :
    dec cs (g+1) 0 fuel p = .ok (it, q) := by
  unfold dec; rw [if_neg hf]; exact hg

theorem dec_one (cs : Array Char) (g : Nat) (fuel : Int) (p q : Nat) (it : Item)
    (hg : decVal cs g fuel p = .ok (it, q)) (hf : ¬ fuel < 0) :
    dec cs (g+1) 1 fuel p = .ok (it, q) := by
  unfold dec; rw [if_neg hf]; exact hg

theorem dec_two (cs : Array Char) (g : Nat) (fuel : Int) (p q : Nat) (it : Item)
    (hg : decExpr cs g fuel p = .ok (it, q)) (hf : ¬ fuel < 0) :
    dec cs (g+1) 2 fuel p = .ok (it, q) := by
  unfold dec; rw [if_neg hf]; exact hg

theorem dec_three (cs : Array Char) (g : Nat) (fuel : Int) (p q : Nat) (n : Int)
    (hg : decNum cs p ';' = .ok (n, q)) (hf : ¬ fuel < 0) :
    dec cs (g+1) 3 fuel p = .ok (.num n, q) := by
  unfold dec; rw [if_neg hf]; rw [hg]; rfl

theorem dec_four (cs : Array Char) (g : Nat) (fuel : Int) (p q : Nat) (s : String)
    (hg : decStr cs p = .ok (s, q)) (hf : ¬ fuel < 0) :
    dec cs (g+1) 4 fuel p = .ok (.str s, q) := by
  unfold dec; rw [if_neg hf]; rw [hg]; rfl

theorem dec_five (cs : Array Char) (g : Nat) (fuel : Int) (p q1 q2 : Nat)
    (r : String) (it : Item)
    (hg1 : decStr cs p = .ok (r, q1))
    (hg2 : decTy cs g (fuel - 1) q1 = .ok (it, q2)) (hf : ¬ fuel < 0) :
    dec cs (g+1) 5 fuel p = .ok (.cat ⟨r, asTy it⟩, q2) := by
  unfold dec; rw [if_neg hf]
  rw [hg1]; simp only [Bind.bind, Except.bind]
  rw [hg2]; rfl

theorem dec_six (cs : Array Char) (g : Nat) (fuel : Int) (p q1 q2 q3 : Nat)
    (r : String) (it1 it2 : Item)
    (hg1 : decStr cs p = .ok (r, q1))
    (hg2 : decList cs g 0 fuel q1 = .ok (it1, q2))
    (hg3 : decTy cs g (fuel - 1) q2 = .ok (it2, q3)) (hf : ¬ fuel < 0) :
    dec cs (g+1) 6 fuel p = .ok (.ext ⟨r, (asList it1).map asTy, asTy it2⟩, q3) := by
  unfold dec; rw [if_neg hf]
  rw [hg1]; simp only [Bind.bind, Except.bind]
  rw [hg2]; simp only [Bind.bind, Except.bind]
  rw [hg3]; rfl

theorem dec_seven (cs : Array Char) (g : Nat) (fuel : Int) (p q1 q2 q3 : Nat)
    (it1 it2 it3 : Item)
    (hg1 : decList cs g 0 fuel p = .ok (it1, q1))
    (hg2 : decTy cs g (fuel - 1) q1 = .ok (it2, q2))
    (hg3 : decExpr cs g (fuel - 1) q2 = .ok (it3, q3)) (hf : ¬ fuel < 0) :
    dec cs (g+1) 7 fuel p =
      .ok (.fn ⟨(asList it1).map asTy, asTy it2, asExpr it3⟩, q3) := by
  unfold dec; rw [if_neg hf]
  rw [hg1]; simp only [Bind.bind, Except.bind]
  rw [hg2]; simp only [Bind.bind, Except.bind]
  rw [hg3]; rfl

theorem dec_eight (cs : Array Char) (g : Nat) (fuel : Int) (p q1 q2 : Nat)
    (k : String) (it : Item)
    (hg1 : decStr cs p = .ok (k, q1))
    (hg2 : decTy cs g (fuel - 1) q1 = .ok (it, q2)) (hf : ¬ fuel < 0) :
    dec cs (g+1) 8 fuel p = .ok (.field k (asTy it), q2) := by
  unfold dec; rw [if_neg hf]
  rw [hg1]; simp only [Bind.bind, Except.bind]
  rw [hg2]; rfl

/-! ## `decElems` / `decList` inverses

Inside `decElems cs G`, element `i` is decoded by `dec cs (G-1-i)`, so the
element-inverse hypothesis is quantified over a gas window. -/

theorem decElems_enc (encOf : Item → String) (cs : Array Char)
    (kind : Nat) (fuel : Int) (minG : Nat) (xs : List Item) :
    ∀ (G : Nat) (p : Nat) (rest : List Char),
    cs.toList.drop p = (catEnc encOf xs).toList ++ rest →
    minG + xs.length + 1 ≤ G →
    (∀ g' x, minG ≤ g' → g' < G → x ∈ xs → ∀ p' rest',
        cs.toList.drop p' = (encOf x).toList ++ rest' →
        dec cs g' kind (fuel - 1) p' = .ok (x, p' + (encOf x).toList.length)) →
    ∀ iters, xs.length ≤ iters →
      decElems cs G kind fuel (xs.length : Int) p iters =
        .ok (xs, p + (catEnc encOf xs).toList.length) := by
  induction xs with
  | nil =>
    intro G p rest h hG helem iters _
    cases G with
    | zero => exact False.elim (by omega)
    | succ g =>
      show decElems cs (g+1) kind fuel (↑(0:Nat)) p iters = .ok ([], p + 0)
      unfold decElems
      rw [if_pos (by omega)]
      rfl
  | cons x xs' ih =>
    intro G p rest h hG helem iters hit
    cases G with
    | zero => exact False.elim (by omega)
    | succ g =>
      simp only [List.length_cons] at hG hit
      have hxd : cs.toList.drop p =
          (encOf x).toList ++ ((catEnc encOf xs').toList ++ rest) := by
        rw [← List.append_assoc]
        have hc := h
        rw [catEnc_cons] at hc
        exact hc
      have hx := helem g x (by omega) (by omega) (List.mem_cons_self ..) p
        ((catEnc encOf xs').toList ++ rest) hxd
      have hdrop : cs.toList.drop (p + (encOf x).toList.length) =
          (catEnc encOf xs').toList ++ rest :=
        drop_append_advance (l := cs.toList) (p := p) (s := (encOf x).toList)
          (r := (catEnc encOf xs').toList ++ rest) hxd
      cases iters with
      | zero => exact False.elim (by omega)
      | succ it =>
        show decElems cs (g+1) kind fuel (↑(xs'.length + 1)) p (it+1) = _
        unfold decElems
        rw [if_neg (by omega)]
        rw [hx]
        simp only [Bind.bind, Except.bind, Functor.map, Except.map]
        rw [show ((↑(xs'.length + 1) : Int) - 1) = (↑xs'.length : Int) by omega]
        rw [ih g (p + (encOf x).toList.length) rest hdrop (by omega)
          (fun g' x' hg'1 hg'2 hm p' rest' hd =>
            helem g' x' hg'1 (by omega) (List.mem_cons_of_mem _ hm) p' rest' hd)
          it (by omega)]
        simp only [Except.pure, catEnc_cons, List.length_append, Nat.add_assoc]
        rfl

/-- `decList` accepts `encNat xs.length` followed by the element encodings. -/
theorem decList_enc (encOf : Item → String) (cs : Array Char) (G : Nat)
    (kind : Nat) (fuel : Int) (minG : Nat) (xs : List Item) (p : Nat)
    (rest : List Char)
    (h : cs.toList.drop p =
      (toString xs.length).toList ++ ';' :: ((catEnc encOf xs).toList ++ rest))
    (hG : minG + xs.length + 2 ≤ G)
    (hn : xs.length ≤ 1024)
    (hI : i64Min ≤ (xs.length : Int) ∧ (xs.length : Int) ≤ i64Max)
    (hs : (toString xs.length).toList.length < 24)
    (helem : ∀ g' x, minG ≤ g' → g' < G - 1 → x ∈ xs → ∀ p' rest',
        cs.toList.drop p' = (encOf x).toList ++ rest' →
        dec cs g' kind (fuel - 1) p' = .ok (x, p' + (encOf x).toList.length)) :
    decList cs G kind fuel p =
      .ok (.list xs, p + (toString xs.length).toList.length + 1 +
        (catEnc encOf xs).toList.length) := by
  cases G with
  | zero => exact False.elim (by omega)
  | succ g =>
    unfold decList
    have hnum : decNat cs p =
        .ok (↑xs.length, p + (toString xs.length).toList.length + 1) :=
      decNat_enc xs.length cs p ((catEnc encOf xs).toList ++ rest) h hs ⟨hI.1, hI.2⟩
    rw [hnum]
    simp only [Bind.bind, Except.bind, Functor.map, Except.map]
    have hdrop : cs.toList.drop (p + (toString xs.length).toList.length + 1) =
        (catEnc encOf xs).toList ++ rest := by
      have h1 := drop_append_advance (l := cs.toList) (p := p)
        (s := (toString xs.length).toList)
        (r := ';' :: ((catEnc encOf xs).toList ++ rest)) h
      have h2 := drop_append_advance (l := cs.toList)
        (p := p + (toString xs.length).toList.length) (s := [';'])
        (r := (catEnc encOf xs).toList ++ rest) h1
      show cs.toList.drop ((p + (toString xs.length).toList.length) + 1) = _
      exact h2
    rw [decElems_enc encOf cs kind fuel minG xs g
      (p + (toString xs.length).toList.length + 1)
      rest hdrop (by omega) (fun g' x hg'1 hg'2 hm p' rest' hd =>
        helem g' x hg'1 (by omega) hm p' rest' hd) 1024 hn]
    simp only [Except.pure]
    rfl

/-! ## `decSeq` inverse

Field `i` of the schema is decoded at `decSeq`'s own `G - 1 - i` gas, so the
field hypothesis is again quantified over a gas window. -/

theorem decSeq_enc (cs : Array Char) (fuel : Int) (minG : Nat)
    (kds : List Nat) :
    ∀ (xs : List Item) (G : Nat) (p : Nat) (rest : List Char),
    cs.toList.drop p = (encItems kds xs).toList ++ rest →
    xs.length = kds.length →
    minG + kds.length + 1 ≤ G →
    (∀ g' kd x, minG ≤ g' → g' < G → (kd, x) ∈ kds.zip xs → ∀ p' rest',
        cs.toList.drop p' = (encItem kd x).toList ++ rest' →
        (if kd ≥ 10 then decList cs g' (kd - 10) fuel p'
         else if kd = 5 then (decNat cs p').map (fun (n, q) => (Item.num n, q))
         else dec cs g' kd (fuel - 1) p') = .ok (x, p' + (encItem kd x).toList.length)) →
    decSeq cs G fuel p kds =
      .ok (xs, p + (encItems kds xs).toList.length) := by
  induction kds with
  | nil =>
    intro xs G p rest h hxs hG hfield
    have hx0 : xs = [] := by
      cases xs with
      | nil => rfl
      | cons =>
        simp only [List.length_cons, List.length_nil] at hxs
        exact False.elim (by omega)
    subst hx0
    cases G with
    | zero => exact False.elim (by omega)
    | succ g =>
      show decSeq cs (g+1) fuel p [] = .ok ([], p + 0)
      unfold decSeq
      rfl
  | cons kd kds' ih =>
    intro xs G p rest h hxs hG hfield
    cases xs with
    | nil =>
      simp only [List.length_nil, List.length_cons] at hxs
      exact False.elim (by omega)
    | cons x xs' =>
      cases G with
      | zero => exact False.elim (by omega)
      | succ g =>
        simp only [List.length_cons] at hG hxs
        have hxs' : xs'.length = kds'.length := by omega
        have hIt : (encItems (kd :: kds') (x :: xs')).toList =
            (encItem kd x).toList ++ (encItems kds' xs').toList := by
          simp only [encItems]
          rfl
        have hxd : cs.toList.drop p =
            (encItem kd x).toList ++ ((encItems kds' xs').toList ++ rest) := by
          rw [← List.append_assoc]
          have hc := h
          rw [hIt] at hc
          exact hc
        have hmem : (kd, x) ∈ (kd :: kds').zip (x :: xs') :=
          List.mem_cons_self ..
        have hx := hfield g kd x (by omega) (by omega) hmem p
          ((encItems kds' xs').toList ++ rest) hxd
        have hdrop : cs.toList.drop (p + (encItem kd x).toList.length) =
            (encItems kds' xs').toList ++ rest :=
          drop_append_advance (l := cs.toList) (p := p) (s := (encItem kd x).toList)
            (r := (encItems kds' xs').toList ++ rest) hxd
        have hzip : ∀ a, a ∈ kds'.zip xs' → a ∈ (kd :: kds').zip (x :: xs') := by
          intro a ha
          exact List.mem_cons_of_mem _ ha
        have htail := ih xs' g (p + (encItem kd x).toList.length) rest hdrop hxs'
          (by omega)
          (fun g' kd' x' hg'1 hg'2 hm p' rest' hd =>
            hfield g' kd' x' hg'1 (by omega) (hzip _ hm) p' rest' hd)
        show decSeq cs (g+1) fuel p (kd :: kds') = _
        unfold decSeq
        rw [hIt, List.length_append]
        cases h10 : decide (kd ≥ 10) with
        | true =>
          rw [if_pos (of_decide_eq_true h10)] at hx ⊢; rw [hx]
          simp only [Bind.bind, Except.bind]
          rw [htail]
          simp only [Bind.bind, Except.bind]
          rw [← Nat.add_assoc]
          rfl
        | false =>
          rw [if_neg (of_decide_eq_false h10)] at hx ⊢
          cases h5 : decide (kd = 5) with
          | true =>
            rw [if_pos (of_decide_eq_true h5)] at hx ⊢; rw [hx]
            simp only [Bind.bind, Except.bind]
            rw [htail]
            simp only [Bind.bind, Except.bind]
            rw [← Nat.add_assoc]
            rfl
          | false =>
            rw [if_neg (of_decide_eq_false h5)] at hx ⊢; rw [hx]
            simp only [Bind.bind, Except.bind]
            rw [htail]
            simp only [Bind.bind, Except.bind]
            rw [← Nat.add_assoc]
            rfl

/-! ## `dec` wrappers in `G ≥ 1` form

The element hypotheses of `decElems_enc`/`decList_enc`/`decSeq_enc` produce
`dec cs g' k` calls whose gas is only known `≥ 1`; these variants take the
`g' - 1` subdecoder directly. -/

theorem dec_zero' (cs : Array Char) (G : Nat) (fuel : Int) (p q : Nat) (it : Item)
    (hG : 1 ≤ G)
    (hg : decTy cs (G - 1) fuel p = .ok (it, q)) (hf : ¬ fuel < 0) :
    dec cs G 0 fuel p = .ok (it, q) := by
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by omega⟩
  exact dec_zero _ _ _ _ _ _ hg hf

theorem dec_one' (cs : Array Char) (G : Nat) (fuel : Int) (p q : Nat) (it : Item)
    (hG : 1 ≤ G)
    (hg : decVal cs (G - 1) fuel p = .ok (it, q)) (hf : ¬ fuel < 0) :
    dec cs G 1 fuel p = .ok (it, q) := by
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by omega⟩
  exact dec_one _ _ _ _ _ _ hg hf

theorem dec_two' (cs : Array Char) (G : Nat) (fuel : Int) (p q : Nat) (it : Item)
    (hG : 1 ≤ G)
    (hg : decExpr cs (G - 1) fuel p = .ok (it, q)) (hf : ¬ fuel < 0) :
    dec cs G 2 fuel p = .ok (it, q) := by
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by omega⟩
  exact dec_two _ _ _ _ _ _ hg hf

theorem dec_three' (cs : Array Char) (G : Nat) (fuel : Int) (p q : Nat) (n : Int)
    (hG : 1 ≤ G)
    (hg : decNum cs p ';' = .ok (n, q)) (hf : ¬ fuel < 0) :
    dec cs G 3 fuel p = .ok (.num n, q) := by
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by omega⟩
  exact dec_three _ _ _ _ _ _ hg hf

theorem dec_four' (cs : Array Char) (G : Nat) (fuel : Int) (p q : Nat) (s : String)
    (hG : 1 ≤ G)
    (hg : decStr cs p = .ok (s, q)) (hf : ¬ fuel < 0) :
    dec cs G 4 fuel p = .ok (.str s, q) := by
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by omega⟩
  exact dec_four _ _ _ _ _ _ hg hf

theorem dec_five' (cs : Array Char) (G : Nat) (fuel : Int) (p q1 q2 : Nat)
    (r : String) (it : Item) (hG : 1 ≤ G)
    (hg1 : decStr cs p = .ok (r, q1))
    (hg2 : decTy cs (G - 1) (fuel - 1) q1 = .ok (it, q2)) (hf : ¬ fuel < 0) :
    dec cs G 5 fuel p = .ok (.cat ⟨r, asTy it⟩, q2) := by
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by omega⟩
  exact dec_five _ _ _ _ _ _ _ _ hg1 hg2 hf

theorem dec_eight' (cs : Array Char) (G : Nat) (fuel : Int) (p q1 q2 : Nat)
    (k : String) (it : Item) (hG : 1 ≤ G)
    (hg1 : decStr cs p = .ok (k, q1))
    (hg2 : decTy cs (G - 1) (fuel - 1) q1 = .ok (it, q2)) (hf : ¬ fuel < 0) :
    dec cs G 8 fuel p = .ok (.field k (asTy it), q2) := by
  obtain ⟨g, rfl⟩ : ∃ g, G = g + 1 := ⟨G - 1, by omega⟩
  exact dec_eight _ _ _ _ _ _ _ _ hg1 hg2 hf

/-! ## Data-quality premises

The decoders refuse encodings whose length counts exceed the 1024-element
`decElems` bound or the 24-position number scan, negative naturals, and
integers outside i64. `dqT`/`dqV`/`dqE` collect exactly those premises. -/

mutual
def dqT : CoreTy → Prop
  | .i64 | .bool | .str | .bytes => True
  | .list t => dqT t
  | .pair a b => dqT a ∧ dqT b
  | .sum ts => ts.length ≤ 1024 ∧ dqsT ts
  | .record fs => fs.length ≤ 1024 ∧ dqfsT fs
def dqsT : List CoreTy → Prop
  | [] => True
  | t :: ts => dqT t ∧ dqsT ts
def dqfsT : List (String × CoreTy) → Prop
  | [] => True
  | (k, t) :: fs => k.length ≤ 1024 ∧ dqT t ∧ dqfsT fs
end

theorem dqsT_mem {ts : List CoreTy} {t : CoreTy} (h : dqsT ts) (hm : t ∈ ts) :
    dqT t := by
  induction ts with
  | nil => cases hm
  | cons x xs' ih =>
    obtain ⟨hx, hxs⟩ := h
    cases hm with
    | head => exact hx
    | tail _ hm' => exact ih hxs hm'

theorem dqfsT_mem {fs : List (String × CoreTy)} {k : String} {t : CoreTy}
    (h : dqfsT fs) (hm : (k, t) ∈ fs) : k.length ≤ 1024 ∧ dqT t := by
  induction fs with
  | nil => cases hm
  | cons x xs' ih =>
    obtain ⟨hk, ht, hfs⟩ := h
    cases hm with
    | head => exact ⟨hk, ht⟩
    | tail _ hm' => exact ih hfs hm'

mutual
def dqV : Val → Prop
  | .i n => inI64 n
  | .b n => 0 ≤ n ∧ inI64 n
  | .s s => s.length ≤ 1024
  | .y bs => bs.length ≤ 1024 ∧ ∀ b ∈ bs, 0 ≤ b ∧ inI64 b
  | .l xs | .r xs => xs.length ≤ 1024 ∧ dqsV xs
  | .p a b => dqV a ∧ dqV b
  | .j i x => 0 ≤ i ∧ inI64 i ∧ dqV x
def dqsV : List Val → Prop
  | [] => True
  | x :: xs => dqV x ∧ dqsV xs
end

theorem dqsV_mem {xs : List Val} {x : Val} (h : dqsV xs) (hm : x ∈ xs) :
    dqV x := by
  induction xs with
  | nil => cases hm
  | cons y ys' ih =>
    obtain ⟨hy, hys⟩ := h
    cases hm with
    | head => exact hy
    | tail _ hm' => exact ih hys hm'

mutual
def dqE : RawExpr → Prop
  | .lit x t => dqV x ∧ dqT t
  | .var i => 0 ≤ i ∧ inI64 i
  | .letE a b | .pair a b | .cons a b => dqE a ∧ dqE b
  | .handle r a b => r.length ≤ 1024 ∧ dqE a ∧ dqE b
  | .ifE c th el | .fold c th el => dqE c ∧ dqE th ∧ dqE el
  | .fst a | .snd a => dqE a
  | .inj i ts a => 0 ≤ i ∧ inI64 i ∧ ts.length ≤ 1024 ∧ dqsT ts ∧ dqE a
  | .matchE s bs => dqE s ∧ bs.length ≤ 1024 ∧ dqsE bs
  | .recordE keys fs =>
      keys.length ≤ 1024 ∧ (∀ k ∈ keys, k.length ≤ 1024) ∧
        fs.length ≤ 1024 ∧ dqsE fs
  | .field r i => dqE r ∧ 0 ≤ i ∧ inI64 i
  | .nil t => dqT t
  | .fix i l s st => dqE i ∧ dqE l ∧ dqE s ∧ dqE st
  | .prim op args =>
      op.length ≤ 1024 ∧ args.length ≤ 1024 ∧ dqsE args
  | .call f args =>
      args.length ≤ 1024 ∧ dqsE args ∧
        (match f with | .local i => 0 ≤ i ∧ inI64 i | .ext r => r.length ≤ 1024)
  | .raise r p t => r.length ≤ 1024 ∧ dqE p ∧ dqT t
  | .unknown _ => False
def dqsE : List RawExpr → Prop
  | [] => True
  | e :: es => dqE e ∧ dqsE es
end

theorem dqsE_mem {es : List RawExpr} {e : RawExpr} (h : dqsE es) (hm : e ∈ es) :
    dqE e := by
  induction es with
  | nil => cases hm
  | cons x xs' ih =>
    obtain ⟨hx, hxs⟩ := h
    cases hm with
    | head => exact hx
    | tail _ hm' => exact ih hxs hm'

/-! ## List-map encoding helpers -/

theorem catEnc_map (f : Item → String) (g : α → Item) (xs : List α) :
    (catEnc f (xs.map g)).toList = (catEnc (fun x => f (g x)) xs).toList := by
  simp only [catEnc, List.map_map]
  rfl

theorem map_asTy_ty (ts : List CoreTy) : (ts.map Item.ty).map asTy = ts := by
  induction ts with
  | nil => rfl
  | cons t ts' ih => rw [List.map_cons, List.map_cons, ih]; rfl

theorem map_asVal_val (xs : List Val) : (xs.map Item.val).map asVal = xs := by
  induction xs with
  | nil => rfl
  | cons x xs' ih => rw [List.map_cons, List.map_cons, ih]; rfl

theorem map_asExpr_expr (es : List RawExpr) :
    (es.map Item.expr).map asExpr = es := by
  induction es with
  | nil => rfl
  | cons e es' ih => rw [List.map_cons, List.map_cons, ih]; rfl

theorem map_asStr_str (ss : List String) : (ss.map Item.str).map asStr = ss := by
  induction ss with
  | nil => rfl
  | cons s ss' ih => rw [List.map_cons, List.map_cons, ih]; rfl

theorem map_asNum_num (ns : List Int) : (ns.map Item.num).map asNum = ns := by
  induction ns with
  | nil => rfl
  | cons n ns' ih => rw [List.map_cons, List.map_cons, ih]; rfl

theorem map_asField_field (fs : List (String × CoreTy)) :
    (fs.map (fun ft => Item.field ft.1 ft.2)).map asField = fs := by
  induction fs with
  | nil => rfl
  | cons ft fs' ih => rw [List.map_cons, List.map_cons, ih]; rfl

/-- `encItems` over a singleton schema pair. -/
theorem encItems_cons (k : Nat) (ks : List Nat) (x : Item) (xs : List Item) :
    encItems (k :: ks) (x :: xs) = encItem k x ++ encItems ks xs := by
  simp only [encItems]
  rfl

theorem encItems_nil (xs : List Item) : encItems [] xs = "" := rfl

/-! ## Measure bounds over `max`-folded list measures -/

theorem tyGas_le_tysGas {t : CoreTy} {ts : List CoreTy} (hm : t ∈ ts) :
    tyGas t ≤ tysGas ts := by
  induction ts with
  | nil => cases hm
  | cons y ys' ih =>
    cases hm with
    | head => simp only [tysGas]; omega
    | tail _ hm' => have := ih hm'; simp only [tysGas]; omega

theorem tyFuel_le_tysFuel {t : CoreTy} {ts : List CoreTy} (hm : t ∈ ts) :
    tyFuel t ≤ tysFuel ts := by
  induction ts with
  | nil => cases hm
  | cons y ys' ih =>
    cases hm with
    | head => simp only [tysFuel]; omega
    | tail _ hm' => have := ih hm'; simp only [tysFuel]; omega

theorem tyGas_le_fieldTysGas {k : String} {t : CoreTy} {fs : List (String × CoreTy)}
    (hm : (k, t) ∈ fs) : tyGas t ≤ fieldTysGas fs := by
  induction fs with
  | nil => cases hm
  | cons y ys' ih =>
    cases hm with
    | head => simp only [fieldTysGas]; omega
    | tail _ hm' => have := ih hm'; simp only [fieldTysGas]; omega

theorem tyFuel_le_fieldTysFuel {k : String} {t : CoreTy} {fs : List (String × CoreTy)}
    (hm : (k, t) ∈ fs) : tyFuel t ≤ fieldTysFuel fs := by
  induction fs with
  | nil => cases hm
  | cons y ys' ih =>
    cases hm with
    | head => simp only [fieldTysFuel]; omega
    | tail _ hm' => have := ih hm'; simp only [fieldTysFuel]; omega

theorem valGas_le_valsGas {x : Val} {xs : List Val} (hm : x ∈ xs) :
    valGas x ≤ valsGas xs := by
  induction xs with
  | nil => cases hm
  | cons y ys' ih =>
    cases hm with
    | head => simp only [valsGas]; omega
    | tail _ hm' => have := ih hm'; simp only [valsGas]; omega

theorem valFuel_le_valsFuel {x : Val} {xs : List Val} (hm : x ∈ xs) :
    valFuel x ≤ valsFuel xs := by
  induction xs with
  | nil => cases hm
  | cons y ys' ih =>
    cases hm with
    | head => simp only [valsFuel]; omega
    | tail _ hm' => have := ih hm'; simp only [valsFuel]; omega

theorem exprGas_le_exprsGas {e : RawExpr} {es : List RawExpr} (hm : e ∈ es) :
    exprGas e ≤ exprsGas es := by
  induction es with
  | nil => cases hm
  | cons y ys' ih =>
    cases hm with
    | head => simp only [exprsGas]; omega
    | tail _ hm' => have := ih hm'; simp only [exprsGas]; omega

theorem exprFuel_le_exprsFuel {e : RawExpr} {es : List RawExpr} (hm : e ∈ es) :
    exprFuel e ≤ exprsFuel es := by
  induction es with
  | nil => cases hm
  | cons y ys' ih =>
    cases hm with
    | head => simp only [exprsFuel]; omega
    | tail _ hm' => have := ih hm'; simp only [exprsFuel]; omega

/-! ## `decTy` inverse (`CoreTy.rec`)

`decTy` is a nested inductive consumer: `.sum`/`.record` route through
`decList`, `.list`/`.pair` through `dec` kind `0`.  The four motives are
  1. the `decTy` inverse itself,
  2. elementwise for `List CoreTy`,
  3. elementwise for field lists,
  4. the field-item (`dec` kind `8`) inverse. -/

theorem decTy_enc : ∀ (t : CoreTy) (cs : Array Char) (g : Nat) (fuel : Int)
    (p : Nat) (rest : List Char),
    cs.toList.drop p = (encTy t).toList ++ rest →
    tyGas t ≤ g → (tyFuel t : Int) ≤ fuel → dqT t →
    decTy cs g fuel p = .ok (.ty t, p + (encTy t).toList.length) := by
  intro t
  refine CoreTy.rec
    (motive_1 := fun t => ∀ (cs : Array Char) (g : Nat) (fuel : Int)
        (p : Nat) (rest : List Char),
        cs.toList.drop p = (encTy t).toList ++ rest →
        tyGas t ≤ g → (tyFuel t : Int) ≤ fuel → dqT t →
        decTy cs g fuel p = .ok (.ty t, p + (encTy t).toList.length))
    (motive_2 := fun ts => ∀ t, t ∈ ts → ∀ (cs : Array Char) (g : Nat)
        (fuel : Int) (p : Nat) (rest : List Char),
        cs.toList.drop p = (encTy t).toList ++ rest →
        tyGas t ≤ g → (tyFuel t : Int) ≤ fuel → dqT t →
        decTy cs g fuel p = .ok (.ty t, p + (encTy t).toList.length))
    (motive_3 := fun fs => ∀ ft, ft ∈ fs → ∀ (cs : Array Char) (g : Nat)
        (fuel : Int) (p : Nat) (rest : List Char),
        cs.toList.drop p = (encStr ft.1 ++ encTy ft.2).toList ++ rest →
        tyGas ft.2 + 1 ≤ g → (tyFuel ft.2 : Int) + 1 ≤ fuel →
        ft.1.length ≤ 1024 ∧ dqT ft.2 →
        dec cs g 8 fuel p =
          .ok (.field ft.1 ft.2,
            p + (encStr ft.1 ++ encTy ft.2).toList.length))
    (motive_4 := fun ft => ∀ (cs : Array Char) (g : Nat) (fuel : Int)
        (p : Nat) (rest : List Char),
        cs.toList.drop p = (encStr ft.1 ++ encTy ft.2).toList ++ rest →
        tyGas ft.2 + 1 ≤ g → (tyFuel ft.2 : Int) + 1 ≤ fuel →
        ft.1.length ≤ 1024 ∧ dqT ft.2 →
        dec cs g 8 fuel p =
          .ok (.field ft.1 ft.2,
            p + (encStr ft.1 ++ encTy ft.2).toList.length))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ t
  · intro cs g fuel p rest h _ _ _
    cases g with
    | zero => simp only [tyGas] at *; exact False.elim (by omega)
    | succ g =>
      have h' : cs.toList.drop p = 'i' :: rest := h
      unfold decTy
      rw [charAt_head cs p 'i' rest h']
      rfl
  · intro cs g fuel p rest h _ _ _
    cases g with
    | zero => simp only [tyGas] at *; exact False.elim (by omega)
    | succ g =>
      have h' : cs.toList.drop p = 'b' :: rest := h
      unfold decTy
      rw [charAt_head cs p 'b' rest h']
      rfl
  · intro cs g fuel p rest h _ _ _
    cases g with
    | zero => simp only [tyGas] at *; exact False.elim (by omega)
    | succ g =>
      have h' : cs.toList.drop p = 's' :: rest := h
      unfold decTy
      rw [charAt_head cs p 's' rest h']
      rfl
  · intro cs g fuel p rest h _ _ _
    cases g with
    | zero => simp only [tyGas] at *; exact False.elim (by omega)
    | succ g =>
      have h' : cs.toList.drop p = 'y' :: rest := h
      unfold decTy
      rw [charAt_head cs p 'y' rest h']
      rfl
  · -- .list t
    intro t iht cs g fuel p rest h hG hF hD
    cases g with
    | zero => have hG0 : tyGas t + 2 ≤ 0 := hG; exact False.elim (by omega)
    | succ g =>
      have h' : cs.toList.drop p = 'L' :: ((encTy t).toList ++ rest) := by
        have e : (encTy t.list).toList = 'L' :: (encTy t).toList := by
          show (("L" ++ encTy t)).toList = _
          rw [toList_append]; rfl
        rw [e] at h
        exact h
      have hd : cs.toList.drop (p + 1) = (encTy t).toList ++ rest := drop_succ h'
      have hG' : tyGas t + 2 ≤ g + 1 := hG
      have hF' : (↑(tyFuel t + 1) : Int) ≤ fuel := hF
      have hsub := iht cs (g - 1) (fuel - 1) (p + 1) rest hd
        (by omega) (by omega) (by exact hD)
      unfold decTy
      dsimp only
      rw [charAt_head cs p 'L' _ h']
      rw [dec_zero' cs g (fuel - 1) (p + 1)
        (p + 1 + (encTy t).toList.length) (Item.ty t)
        (by omega) hsub (by omega)]
      simp only [Bind.bind, Except.bind]
      show Except.ok (Item.ty (CoreTy.list t), p + 1 + (encTy t).toList.length) = _
      have e : (encTy t.list).toList.length = 1 + (encTy t).toList.length := by
        show (("L" ++ encTy t)).toList.length = _
        rw [toList_append, List.length_append,
          show ("L".toList.length : Nat) = 1 from rfl]
      rw [e, show p + 1 + (encTy t).toList.length =
        p + (1 + (encTy t).toList.length) from by omega]
  · -- .pair a b
    intro a b iha ihb cs g fuel p rest h hG hF hD
    cases g with
    | zero => have hG0 : max (tyGas a) (tyGas b) + 2 ≤ 0 := hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encTy (a.pair b)).toList =
          'P' :: ((encTy a).toList ++ (encTy b).toList) := by
        show (("P" ++ encTy a ++ encTy b)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      simp only [List.cons_append, List.nil_append, List.append_assoc] at h
      have h' : cs.toList.drop p =
          'P' :: ((encTy a).toList ++ ((encTy b).toList ++ rest)) := h
      have hd1 : cs.toList.drop (p + 1) =
          (encTy a).toList ++ ((encTy b).toList ++ rest) :=
        drop_succ h'
      have hd2 : cs.toList.drop (p + 1 + (encTy a).toList.length) =
          (encTy b).toList ++ rest :=
        drop_append_advance hd1
      have hG' : max (tyGas a) (tyGas b) + 2 ≤ g + 1 := hG
      have hF' : (↑(max (tyFuel a) (tyFuel b) + 1) : Int) ≤ fuel := hF
      have hda : dqT a ∧ dqT b := hD
      have hsub1 := iha cs (g - 1) (fuel - 1) (p + 1)
        ((encTy b).toList ++ rest) hd1
        (by omega) (by omega) hda.1
      have hsub2 := ihb cs (g - 1) (fuel - 1) (p + 1 + (encTy a).toList.length)
        rest hd2
        (by omega) (by omega) hda.2
      unfold decTy
      dsimp only
      rw [charAt_head cs p 'P' _ h']
      rw [dec_zero' cs g (fuel - 1) (p + 1)
        (p + 1 + (encTy a).toList.length) (Item.ty a)
        (by omega) hsub1 (by omega)]
      simp only [Bind.bind, Except.bind]
      rw [dec_zero' cs g (fuel - 1) (p + 1 + (encTy a).toList.length)
        (p + 1 + (encTy a).toList.length + (encTy b).toList.length) (Item.ty b)
        (by omega) hsub2 (by omega)]
      simp only [Bind.bind, Except.bind]
      show Except.ok (Item.ty (CoreTy.pair a b),
            p + 1 + (encTy a).toList.length + (encTy b).toList.length) = _
      have e : (encTy (a.pair b)).toList.length =
          1 + ((encTy a).toList.length + (encTy b).toList.length) := by
        show (("P" ++ encTy a ++ encTy b)).toList.length = _
        rw [toList_append, toList_append, List.length_append, List.length_append,
          show ("P".toList.length : Nat) = 1 from rfl]
        omega
      rw [e, show p + 1 + (encTy a).toList.length + (encTy b).toList.length =
        p + (1 + ((encTy a).toList.length + (encTy b).toList.length))
        from by omega]
  · -- .sum ts
    intro ts ihts cs g fuel p rest h hG hF hD
    obtain ⟨hlen, hdq⟩ := hD
    cases g with
    | zero => have hG0 : tysGas ts + ts.length + 4 ≤ 0 := hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encTy (.sum ts)).toList = 'S' ::
          ((encNat (↑ts.length : Int)).toList ++ (encTys ts).toList) := by
        show (("S" ++ encNat ↑ts.length ++ encTys ts)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      simp only [List.cons_append, List.nil_append, List.append_assoc] at h
      have hNat : (encNat (↑ts.length : Int)).toList =
          (toString (↑ts.length : Int)).toList ++ [';'] := by
        show (toString (↑ts.length : Int) ++ ";").toList = _
        rw [toList_append]; rfl
      have hd : cs.toList.drop (p + 1) =
          (toString (↑ts.length : Int)).toList ++
            (';' :: ((encTys ts).toList ++ rest)) := by
        have e := drop_succ h
        rw [hNat] at e
        simp only [List.append_assoc, List.cons_append, List.nil_append] at e
        exact e
      have hcat : (catEnc (fun x => encTy (asTy x)) (ts.map Item.ty)).toList =
          (encTys ts).toList := by
        rw [catEnc_map]
        show (catEnc (fun t_1 => encTy (asTy (Item.ty t_1))) ts).toList =
            (encTys ts).toList
        rw [show (fun t_1 => encTy (asTy (Item.ty t_1))) = encTy from rfl]
        rw [encTys_catEnc]
      have hdl := decList_enc (fun x => encTy (asTy x)) cs g 0 fuel
        (tysGas ts + 1) (ts.map Item.ty) (p + 1) rest
        (by rw [List.length_map, hcat]; exact hd)
        (by rw [List.length_map]
            have hG' : tysGas ts + ts.length + 4 ≤ g + 1 := hG; omega)
        (by rw [List.length_map]; exact hlen)
        (by rw [List.length_map]
            exact ⟨by unfold i64Min; omega,
                   by unfold i64Max; omega⟩)
        (by rw [List.length_map]; exact toString_len_lt24 _ hlen)
        (fun g' x hg'1 hg'2 hm p' rest' hd' => by
          obtain ⟨t', htm, hte⟩ := List.mem_map.mp hm
          subst hte
          have hd'' : cs.toList.drop p' = (encTy t').toList ++ rest' := hd'
          have hF' : (↑(tysFuel ts + 1) : Int) ≤ fuel := hF
          show dec cs g' 0 (fuel - 1) p' =
            .ok (Item.ty t', p' + (encTy t').toList.length)
          exact dec_zero' cs g' (fuel - 1) p'
            (p' + (encTy t').toList.length) (Item.ty t')
            (by have := tyGas_le_tysGas htm; omega)
            (ihts t' htm cs (g' - 1) (fuel - 1) p' rest' hd''
              (by have := tyGas_le_tysGas htm; omega)
              (by have := tyFuel_le_tysFuel htm; omega)
              (dqsT_mem hdq htm))
            (by omega))
      unfold decTy
      dsimp only
      rw [charAt_head cs p 'S' _ h]
      rw [hdl]
      simp only [Bind.bind, Except.bind]
      show Except.ok (Item.ty (CoreTy.sum ((ts.map Item.ty).map asTy)),
            p + 1 + (toString (ts.map Item.ty).length).toList.length + 1 +
              (catEnc (fun x => encTy (asTy x)) (ts.map Item.ty)).toList.length) = _
      rw [map_asTy_ty, List.length_map, hcat]
      show Except.ok (Item.ty (CoreTy.sum ts),
            p + 1 + (toString (↑ts.length : Int)).toList.length + 1 +
              (encTys ts).toList.length) = _
      have e : (encTy (.sum ts)).toList.length =
          1 + ((toString (↑ts.length : Int)).toList.length + 1 +
            (encTys ts).toList.length) := by
        simp only [hEnc, hNat, List.length_cons, List.length_append,
          List.length_nil]
        omega
      rw [e, show p + 1 + (toString (↑ts.length : Int)).toList.length + 1 +
            (encTys ts).toList.length =
          p + (1 + ((toString (↑ts.length : Int)).toList.length + 1 +
            (encTys ts).toList.length)) from by omega]
  · -- .record fs
    intro fs ihfs cs g fuel p rest h hG hF hD
    obtain ⟨hlen, hdq⟩ := hD
    cases g with
    | zero => have hG0 : fieldTysGas fs + fs.length + 4 ≤ 0 := hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encTy (.record fs)).toList = 'R' ::
          ((encNat (↑fs.length : Int)).toList ++ (encFieldTys fs).toList) := by
        show (("R" ++ encNat ↑fs.length ++ encFieldTys fs)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      simp only [List.cons_append, List.nil_append, List.append_assoc] at h
      have hNat : (encNat (↑fs.length : Int)).toList =
          (toString (↑fs.length : Int)).toList ++ [';'] := by
        show (toString (↑fs.length : Int) ++ ";").toList = _
        rw [toList_append]; rfl
      have hd : cs.toList.drop (p + 1) =
          (toString (↑fs.length : Int)).toList ++
            (';' :: ((encFieldTys fs).toList ++ rest)) := by
        have e := drop_succ h
        rw [hNat] at e
        simp only [List.append_assoc, List.cons_append, List.nil_append] at e
        exact e
      have hcat : (catEnc (fun x : Item => encStr (asField x).1 ++
            encTy (asField x).2)
            (fs.map (fun ft => Item.field ft.1 ft.2))).toList =
          (encFieldTys fs).toList := by
        rw [catEnc_map]
        show (catEnc (fun ft : String × CoreTy =>
            encStr (asField (Item.field ft.1 ft.2)).1 ++
            encTy (asField (Item.field ft.1 ft.2)).2) fs).toList =
            (encFieldTys fs).toList
        rw [show (fun ft : String × CoreTy =>
            encStr (asField (Item.field ft.1 ft.2)).1 ++
            encTy (asField (Item.field ft.1 ft.2)).2) =
            (fun ft : String × CoreTy => encStr ft.1 ++ encTy ft.2) from rfl]
        rw [encFieldTys_catEnc]
      have hdl := decList_enc
        (fun x : Item => encStr (asField x).1 ++ encTy (asField x).2) cs g 8 fuel
        (fieldTysGas fs + 1) (fs.map (fun ft => Item.field ft.1 ft.2)) (p + 1)
        rest
        (by rw [List.length_map, hcat]; exact hd)
        (by rw [List.length_map]
            have hG' : fieldTysGas fs + fs.length + 4 ≤ g + 1 := hG; omega)
        (by rw [List.length_map]; exact hlen)
        (by rw [List.length_map]
            exact ⟨by unfold i64Min; omega,
                   by unfold i64Max; omega⟩)
        (by rw [List.length_map]; exact toString_len_lt24 _ hlen)
        (fun g' x hg'1 hg'2 hm p' rest' hd' => by
          obtain ⟨ft, hfm, hte⟩ := List.mem_map.mp hm
          subst hte
          have hd'' : cs.toList.drop p' =
              (encStr ft.1 ++ encTy ft.2).toList ++ rest' := hd'
          obtain ⟨hk, ht⟩ := dqfsT_mem hdq hfm
          have hF' : (↑(fieldTysFuel fs + 2) : Int) ≤ fuel := hF
          exact ihfs ft hfm cs g' (fuel - 1) p' rest' hd''
            (by have := tyGas_le_fieldTysGas hfm; omega)
            (by have := tyFuel_le_fieldTysFuel hfm; omega) ⟨hk, ht⟩)
      unfold decTy
      dsimp only
      rw [charAt_head cs p 'R' _ h]
      rw [hdl]
      simp only [Bind.bind, Except.bind]
      show Except.ok (Item.ty (CoreTy.record ((fs.map (fun ft =>
              Item.field ft.1 ft.2)).map asField)),
            p + 1 + (toString (fs.map (fun ft =>
              Item.field ft.1 ft.2)).length).toList.length + 1 +
              (catEnc (fun x : Item => encStr (asField x).1 ++ encTy (asField x).2)
                (fs.map (fun ft => Item.field ft.1 ft.2))).toList.length) = _
      rw [map_asField_field, List.length_map, hcat]
      show Except.ok (Item.ty (CoreTy.record fs),
            p + 1 + (toString (↑fs.length : Int)).toList.length + 1 +
              (encFieldTys fs).toList.length) = _
      have e : (encTy (.record fs)).toList.length =
          1 + ((toString (↑fs.length : Int)).toList.length + 1 +
            (encFieldTys fs).toList.length) := by
        simp only [hEnc, hNat, List.length_cons, List.length_append,
          List.length_nil]
        omega
      rw [e, show p + 1 + (toString (↑fs.length : Int)).toList.length + 1 +
            (encFieldTys fs).toList.length =
          p + (1 + ((toString (↑fs.length : Int)).toList.length + 1 +
            (encFieldTys fs).toList.length)) from by omega]
  · -- motive_2 nil
    intro t hm; cases hm
  · -- motive_2 cons
    intro t ts' iht ihts t' hm
    cases hm with
    | head => exact iht
    | tail _ hm' => exact ihts t' hm'
  · -- motive_3 nil
    intro ft hm; cases hm
  · -- motive_3 cons
    intro ft fs' ihft ihfs ft' hm
    cases hm with
    | head => exact ihft
    | tail _ hm' => exact ihfs ft' hm'
  · -- motive_4: field item via dec kind 8
    intro k t iht cs g fuel p rest h hG hF hD
    obtain ⟨hk, htd⟩ := hD
    have hG' : tyGas t + 1 ≤ g := hG
    have hF' : (↑(tyFuel t + 1) : Int) ≤ fuel := hF
    have h' : cs.toList.drop p =
        (encStr k ++ encTy t).toList ++ rest := h
    have eS : (encStr k).toList =
        (toString k.length).toList ++ ':' :: k.toList := by
      show (toString k.length ++ ":" ++ k).toList = _
      simp only [toList_append]
      rw [show (":" : String).toList = [':'] from rfl, List.append_assoc,
        List.cons_append, List.nil_append]
    have hdecomp : cs.toList.drop p = (toString k.length).toList ++
        ':' :: (k.toList ++ ((encTy t).toList ++ rest)) := by
      have e := h'
      rw [toList_append, eS] at e
      simp only [List.append_assoc, List.cons_append, List.nil_append] at e
      exact e
    have hkdec := decStr_enc k cs p ((encTy t).toList ++ rest) hdecomp
      (toString_len_lt24 _ hk) hk
    have hdecomp2 : cs.toList.drop p =
        ((toString k.length).toList ++ ':' :: k.toList) ++
          ((encTy t).toList ++ rest) := by
      rw [hdecomp, ← List.cons_append, ← List.append_assoc]
    have hd2 : cs.toList.drop
        (p + (toString k.length).toList.length + 1 + k.length) =
        (encTy t).toList ++ rest := by
      have e := drop_append_advance hdecomp2
      have hl : ((toString k.length).toList ++ ':' :: k.toList).length =
          (toString k.length).toList.length + 1 + k.length := by
        rw [List.length_append, List.length_cons]
        have hkl : k.toList.length = k.length := rfl
        omega
      rw [hl] at e
      simpa only [← Nat.add_assoc] using e
    have hsub := iht cs (g - 1) (fuel - 1)
      (p + (toString k.length).toList.length + 1 + k.length) rest hd2
      (by omega) (by omega) htd
    have hESlen : (encStr k).toList.length =
        (toString k.length).toList.length + 1 + k.length := by
      rw [eS, List.length_append, List.length_cons]
      have hkl : k.toList.length = k.length := rfl
      omega
    have hlen : p + (encStr k ++ encTy t).toList.length =
        p + (toString k.length).toList.length + 1 + k.length +
          (encTy t).toList.length := by
      rw [toList_append, List.length_append, hESlen]; omega
    show dec cs g 8 fuel p =
      .ok (.field k t, p + (encStr k ++ encTy t).toList.length)
    rw [hlen]
    exact dec_eight' cs g fuel p _ _ k (.ty t) (by omega) hkdec hsub
      (by omega)

/-- `encNat n` is the digits of `n` plus the `';'` terminator. -/
theorem encNat_toList (n : Int) :
    (encNat n).toList = (toString n).toList ++ [';'] := by
  show (toString n ++ ";").toList = _
  rw [toList_append]; rfl

/-- `encStr x` is `len ++ ":" ++ scalars`. -/
theorem encStr_toList (x : String) :
    (encStr x).toList = (toString x.length).toList ++ ':' :: x.toList := by
  show (toString x.length ++ ":" ++ x).toList = _
  rw [toList_append, toList_append,
    show (":" : String).toList = [':'] from rfl, List.append_assoc,
    List.cons_append, List.nil_append]

/-- `decNat` accepts `encNat n` for a nonnegative `n` (the `.b`/`.j`
    natural-number fields). -/
theorem decNat_encInt (n : Int) (h0 : 0 ≤ n) (hn : inI64 n)
    (cs : Array Char) (p : Nat) (rest : List Char)
    (h : cs.toList.drop p = (encNat n).toList ++ rest) :
    decNat cs p = .ok (n, p + (toString n).toList.length + 1) := by
  have hb : (↑n.toNat : Int) = n := by
    cases n with
    | ofNat m => rfl
    | negSucc m => exact absurd h0 (Int.not_le.mpr (Int.negSucc_lt_zero m))
  have hc : (toString n.toNat).toList = (toString n).toList :=
    congrArg String.toList (congrArg toString hb)
  have hd : cs.toList.drop p = (toString n.toNat).toList ++ ';' :: rest := by
    rw [encNat_toList] at h
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h
    rw [hc]; exact h
  have hdn := decNat_enc n.toNat cs p rest hd
    (by rw [hc]; exact toString_int_len_lt24 n hn) (by rw [hb]; exact hn)
  rw [hdn, hb, hc]

/-- `decVal` reads an `encVal` value back. -/
theorem decVal_enc : ∀ (v : Val) (cs : Array Char) (g : Nat) (fuel : Int)
    (p : Nat) (rest : List Char),
    cs.toList.drop p = (encVal v).toList ++ rest →
    valGas v ≤ g → (valFuel v : Int) ≤ fuel → dqV v →
    decVal cs g fuel p = .ok (.val v, p + (encVal v).toList.length) := by
  intro v
  refine Val.rec
    (motive_1 := fun v => ∀ (cs : Array Char) (g : Nat) (fuel : Int)
        (p : Nat) (rest : List Char),
        cs.toList.drop p = (encVal v).toList ++ rest →
        valGas v ≤ g → (valFuel v : Int) ≤ fuel → dqV v →
        decVal cs g fuel p = .ok (.val v, p + (encVal v).toList.length))
    (motive_2 := fun xs => ∀ x, x ∈ xs → ∀ (cs : Array Char) (g : Nat)
        (fuel : Int) (p : Nat) (rest : List Char),
        cs.toList.drop p = (encVal x).toList ++ rest →
        valGas x ≤ g → (valFuel x : Int) ≤ fuel → dqV x →
        decVal cs g fuel p = .ok (.val x, p + (encVal x).toList.length))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ v
  · -- .i n
    intro n cs g fuel p rest h hG hF hD
    cases g with
    | zero => simp only [valGas] at hG; exact False.elim (by omega)
    | succ g =>
      have h' : cs.toList.drop p = 'I' :: ((encNat n).toList ++ rest) := by
        have e : (encVal (.i n)).toList = 'I' :: (encNat n).toList := by
          show (("I" ++ encNat n)).toList = _
          rw [toList_append]; rfl
        rw [e] at h; exact h
      have hd : cs.toList.drop (p + 1) =
          (toString n).toList ++ ';' :: rest := by
        have e := drop_succ h'
        rw [encNat_toList] at e
        simp only [List.append_assoc, List.cons_append, List.nil_append] at e
        exact e
      have hnum := decNum_encNat n hD cs (p + 1) rest hd
        (toString_int_len_lt24 n hD)
      unfold decVal; dsimp only
      rw [charAt_head cs p 'I' _ h', hnum]
      simp only [Functor.map, Except.map]
      show Except.ok (Item.val (Val.i n),
            p + 1 + (toString n).toList.length + 1) = _
      have e : (encVal (.i n)).toList.length =
          1 + ((toString n).toList.length + 1) := by
        show (("I" ++ encNat n)).toList.length = _
        rw [toList_append, List.length_append, encNat_toList,
          List.length_append, List.length_cons, List.length_nil,
          show ("I".toList.length : Nat) = 1 from rfl]
      rw [e, show p + 1 + (toString n).toList.length + 1 =
        p + (1 + ((toString n).toList.length + 1)) from by omega]
  · -- .b b
    intro b cs g fuel p rest h hG hF hD
    obtain ⟨h0, hin⟩ := hD
    cases g with
    | zero => simp only [valGas] at hG; exact False.elim (by omega)
    | succ g =>
      have h' : cs.toList.drop p = 'B' :: ((encNat b).toList ++ rest) := by
        have e : (encVal (.b b)).toList = 'B' :: (encNat b).toList := by
          show (("B" ++ encNat b)).toList = _
          rw [toList_append]; rfl
        rw [e] at h; exact h
      have hd : cs.toList.drop (p + 1) = (encNat b).toList ++ rest :=
        drop_succ h'
      have hdn := decNat_encInt b h0 hin cs (p + 1) rest hd
      unfold decVal; dsimp only
      rw [charAt_head cs p 'B' _ h', hdn]
      simp only [Functor.map, Except.map]
      show Except.ok (Item.val (Val.b b),
            p + 1 + (toString b).toList.length + 1) = _
      have e : (encVal (.b b)).toList.length =
          1 + ((toString b).toList.length + 1) := by
        show (("B" ++ encNat b)).toList.length = _
        rw [toList_append, List.length_append, encNat_toList,
          List.length_append, List.length_cons, List.length_nil,
          show ("B".toList.length : Nat) = 1 from rfl]
      rw [e, show p + 1 + (toString b).toList.length + 1 =
        p + (1 + ((toString b).toList.length + 1)) from by omega]
  · -- .s s
    intro s cs g fuel p rest h hG hF hD
    cases g with
    | zero => simp only [valGas] at hG; exact False.elim (by omega)
    | succ g =>
      have h' : cs.toList.drop p = 'T' :: ((encStr s).toList ++ rest) := by
        have e : (encVal (.s s)).toList = 'T' :: (encStr s).toList := by
          show (("T" ++ encStr s)).toList = _
          rw [toList_append]; rfl
        rw [e] at h; exact h
      have hd : cs.toList.drop (p + 1) =
          (toString s.length).toList ++ ':' :: (s.toList ++ rest) := by
        have e := drop_succ h'
        rw [encStr_toList] at e
        simp only [List.append_assoc, List.cons_append, List.nil_append] at e
        exact e
      have hds := decStr_enc s cs (p + 1) rest hd
        (toString_len_lt24 _ hD) hD
      unfold decVal; dsimp only
      rw [charAt_head cs p 'T' _ h', hds]
      simp only [Functor.map, Except.map]
      show Except.ok (Item.val (Val.s s),
            p + 1 + (toString s.length).toList.length + 1 + s.length) = _
      have e : (encVal (.s s)).toList.length =
          1 + ((toString s.length).toList.length + 1 + s.length) := by
        show (("T" ++ encStr s)).toList.length = _
        rw [toList_append, List.length_append, encStr_toList,
          List.length_append, List.length_cons,
          show ("T".toList.length : Nat) = 1 from rfl,
          show (s.toList.length : Nat) = s.length from rfl]
        omega
      rw [e, show p + 1 + (toString s.length).toList.length + 1 + s.length =
        p + (1 + ((toString s.length).toList.length + 1 + s.length))
        from by omega]
  · -- .y bs
    intro bs cs g fuel p rest h hG hF hD
    obtain ⟨hlen, hdq⟩ := hD
    cases g with
    | zero => have hG0 : bs.length + 4 ≤ 0 := hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encVal (.y bs)).toList = 'Y' ::
          ((encNat (↑bs.length : Int)).toList ++
            (String.join (bs.map encNat)).toList) := by
        show (("Y" ++ encNat ↑bs.length ++
            String.join (bs.map encNat))).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      simp only [List.cons_append, List.nil_append, List.append_assoc] at h
      have hcat : (catEnc (fun x => encNat (asNum x))
            (bs.map Item.num)).toList =
          (String.join (bs.map encNat)).toList := by
        rw [catEnc_map]
        show (catEnc (fun x => encNat (asNum (Item.num x))) bs).toList = _
        rw [show (fun x => encNat (asNum (Item.num x))) = encNat from rfl,
          ← encNat_catEnc]
      have hd : cs.toList.drop (p + 1) =
          (toString (↑bs.length : Int)).toList ++
            (';' :: ((String.join (bs.map encNat)).toList ++ rest)) := by
        have e := drop_succ h
        rw [encNat_toList] at e
        simp only [List.append_assoc, List.cons_append, List.nil_append] at e
        exact e
      have hdl := decList_enc (fun x => encNat (asNum x)) cs g 3 fuel 1
        (bs.map Item.num) (p + 1) rest
        (by rw [List.length_map, hcat]; exact hd)
        (by rw [List.length_map]
            have hG' : bs.length + 4 ≤ g + 1 := hG; omega)
        (by rw [List.length_map]; exact hlen)
        (by rw [List.length_map]
            exact ⟨by unfold i64Min; omega,
                   by unfold i64Max; omega⟩)
        (by rw [List.length_map]; exact toString_len_lt24 _ hlen)
        (fun g' x hg'1 hg'2 hm p' rest' hd' => by
          obtain ⟨b, hbm, hbe⟩ := List.mem_map.mp hm
          subst hbe
          have hd'' : cs.toList.drop p' = (encNat b).toList ++ rest' := hd'
          rw [encNat_toList] at hd''
          simp only [List.append_assoc, List.cons_append,
            List.nil_append] at hd''
          have hF' : (1 : Int) ≤ fuel := hF
          show dec cs g' 3 (fuel - 1) p' =
            .ok (.num b, p' + (encNat b).toList.length)
          have elen : p' + (encNat b).toList.length =
              p' + (toString b).toList.length + 1 := by
            rw [encNat_toList, List.length_append,
              show ([';'] : List Char).length = 1 from rfl]
            omega
          rw [elen]
          exact dec_three' cs g' (fuel - 1) p'
            (p' + (toString b).toList.length + 1) b (by omega)
            (decNum_encNat b (hdq b hbm).2 cs p' rest' hd''
              (toString_int_len_lt24 b (hdq b hbm).2))
            (by omega))
      unfold decVal; dsimp only
      rw [charAt_head cs p 'Y' _ h]
      rw [hdl]
      simp only [Bind.bind, Except.bind, Except.pure]
      show Except.ok (Item.val (Val.y ((bs.map Item.num).map asNum)),
            p + 1 + (toString (bs.map Item.num).length).toList.length + 1 +
              (catEnc (fun x => encNat (asNum x))
                (bs.map Item.num)).toList.length) = _
      rw [map_asNum_num, List.length_map, hcat]
      show Except.ok (Item.val (Val.y bs),
            p + 1 + (toString (↑bs.length : Int)).toList.length + 1 +
              (String.join (bs.map encNat)).toList.length) = _
      have e : (encVal (.y bs)).toList.length =
          1 + ((toString (↑bs.length : Int)).toList.length + 1 +
            (String.join (bs.map encNat)).toList.length) := by
        simp only [hEnc, encNat_toList, List.length_cons,
          List.length_append, List.length_nil]
        omega
      rw [e, show p + 1 + (toString (↑bs.length : Int)).toList.length + 1 +
            (String.join (bs.map encNat)).toList.length =
          p + (1 + ((toString (↑bs.length : Int)).toList.length + 1 +
            (String.join (bs.map encNat)).toList.length)) from by omega]
  · -- .l xs
    intro xs ihxs cs g fuel p rest h hG hF hD
    obtain ⟨hlen, hdq⟩ := hD
    cases g with
    | zero => have hG0 : valsGas xs + xs.length + 4 ≤ 0 := hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encVal (.l xs)).toList = 'L' ::
          ((encNat (↑xs.length : Int)).toList ++ (encVals xs).toList) := by
        show (("L" ++ encNat ↑xs.length ++ encVals xs)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      simp only [List.cons_append, List.nil_append, List.append_assoc] at h
      have hcat : (catEnc (fun x => encVal (asVal x))
            (xs.map Item.val)).toList =
          (encVals xs).toList := by
        rw [catEnc_map]
        show (catEnc (fun x => encVal (asVal (Item.val x))) xs).toList = _
        rw [show (fun x => encVal (asVal (Item.val x))) = encVal from rfl,
          encVals_catEnc]
      have hd : cs.toList.drop (p + 1) =
          (toString (↑xs.length : Int)).toList ++
            (';' :: ((encVals xs).toList ++ rest)) := by
        have e := drop_succ h
        rw [encNat_toList] at e
        simp only [List.append_assoc, List.cons_append, List.nil_append] at e
        exact e
      have hdl := decList_enc (fun x => encVal (asVal x)) cs g 1 fuel
        (valsGas xs + 1) (xs.map Item.val) (p + 1) rest
        (by rw [List.length_map, hcat]; exact hd)
        (by rw [List.length_map]
            have hG' : valsGas xs + xs.length + 4 ≤ g + 1 := hG; omega)
        (by rw [List.length_map]; exact hlen)
        (by rw [List.length_map]
            exact ⟨by unfold i64Min; omega,
                   by unfold i64Max; omega⟩)
        (by rw [List.length_map]; exact toString_len_lt24 _ hlen)
        (fun g' x hg'1 hg'2 hm p' rest' hd' => by
          obtain ⟨v, hvm, hve⟩ := List.mem_map.mp hm
          subst hve
          have hd'' : cs.toList.drop p' = (encVal v).toList ++ rest' := hd'
          have hF' : (↑(valsFuel xs + 1) : Int) ≤ fuel := hF
          show dec cs g' 1 (fuel - 1) p' =
            .ok (.val v, p' + (encVal v).toList.length)
          exact dec_one' cs g' (fuel - 1) p'
            (p' + (encVal v).toList.length) (.val v)
            (by have := valGas_le_valsGas hvm; omega)
            (ihxs v hvm cs (g' - 1) (fuel - 1) p' rest' hd''
              (by have := valGas_le_valsGas hvm; omega)
              (by have := valFuel_le_valsFuel hvm; omega)
              (dqsV_mem hdq hvm))
            (by omega))
      unfold decVal; dsimp only
      rw [charAt_head cs p 'L' _ h]
      rw [hdl]
      simp only [Bind.bind, Except.bind, Except.pure]
      show Except.ok (Item.val (Val.l ((xs.map Item.val).map asVal)),
            p + 1 + (toString (xs.map Item.val).length).toList.length + 1 +
              (catEnc (fun x => encVal (asVal x))
                (xs.map Item.val)).toList.length) = _
      rw [map_asVal_val, List.length_map, hcat]
      show Except.ok (Item.val (Val.l xs),
            p + 1 + (toString (↑xs.length : Int)).toList.length + 1 +
              (encVals xs).toList.length) = _
      have e : (encVal (.l xs)).toList.length =
          1 + ((toString (↑xs.length : Int)).toList.length + 1 +
            (encVals xs).toList.length) := by
        simp only [hEnc, encNat_toList, List.length_cons,
          List.length_append, List.length_nil]
        omega
      rw [e, show p + 1 + (toString (↑xs.length : Int)).toList.length + 1 +
            (encVals xs).toList.length =
          p + (1 + ((toString (↑xs.length : Int)).toList.length + 1 +
            (encVals xs).toList.length)) from by omega]
  · -- .p a b
    intro a b iha ihb cs g fuel p rest h hG hF hD
    obtain ⟨hda, hdb⟩ := hD
    cases g with
    | zero => have hG0 : max (valGas a) (valGas b) + 2 ≤ 0 := hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encVal (a.p b)).toList =
          'P' :: ((encVal a).toList ++ (encVal b).toList) := by
        show (("P" ++ encVal a ++ encVal b)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      simp only [List.cons_append, List.nil_append, List.append_assoc] at h
      have h' : cs.toList.drop p =
          'P' :: ((encVal a).toList ++ ((encVal b).toList ++ rest)) := h
      have hd1 : cs.toList.drop (p + 1) =
          (encVal a).toList ++ ((encVal b).toList ++ rest) :=
        drop_succ h'
      have hd2 : cs.toList.drop (p + 1 + (encVal a).toList.length) =
          (encVal b).toList ++ rest :=
        drop_append_advance hd1
      have hG' : max (valGas a) (valGas b) + 2 ≤ g + 1 := hG
      have hF' : (↑(max (valFuel a) (valFuel b) + 1) : Int) ≤ fuel := hF
      have hsub1 := iha cs (g - 1) (fuel - 1) (p + 1)
        ((encVal b).toList ++ rest) hd1
        (by omega) (by omega) hda
      have hsub2 := ihb cs (g - 1) (fuel - 1)
        (p + 1 + (encVal a).toList.length) rest hd2
        (by omega) (by omega) hdb
      unfold decVal; dsimp only
      rw [charAt_head cs p 'P' _ h']
      rw [dec_one' cs g (fuel - 1) (p + 1)
        (p + 1 + (encVal a).toList.length) (.val a)
        (by omega) hsub1 (by omega)]
      simp only [Bind.bind, Except.bind]
      rw [dec_one' cs g (fuel - 1) (p + 1 + (encVal a).toList.length)
        (p + 1 + (encVal a).toList.length + (encVal b).toList.length)
        (.val b) (by omega) hsub2 (by omega)]
      simp only [Bind.bind, Except.bind]
      show Except.ok (Item.val (Val.p a b),
            p + 1 + (encVal a).toList.length + (encVal b).toList.length) = _
      have e : (encVal (a.p b)).toList.length =
          1 + ((encVal a).toList.length + (encVal b).toList.length) := by
        show (("P" ++ encVal a ++ encVal b)).toList.length = _
        rw [toList_append, toList_append, List.length_append,
          List.length_append,
          show ("P".toList.length : Nat) = 1 from rfl]
        omega
      rw [e, show p + 1 + (encVal a).toList.length + (encVal b).toList.length =
        p + (1 + ((encVal a).toList.length + (encVal b).toList.length))
        from by omega]
  · -- .j i x
    intro i x ihx cs g fuel p rest h hG hF hD
    obtain ⟨h0, hin, hxd⟩ := hD
    cases g with
    | zero => have hG0 : valGas x + 2 ≤ 0 := hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encVal (.j i x)).toList =
          'J' :: ((encNat i).toList ++ (encVal x).toList) := by
        show (("J" ++ encNat i ++ encVal x)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      simp only [List.cons_append, List.nil_append, List.append_assoc] at h
      have hd : cs.toList.drop (p + 1) =
          (encNat i).toList ++ ((encVal x).toList ++ rest) :=
        drop_succ h
      have hdn := decNat_encInt i h0 hin cs (p + 1)
        ((encVal x).toList ++ rest) hd
      have elen : (encNat i).toList.length =
          (toString i).toList.length + 1 := by
        rw [encNat_toList, List.length_append]; rfl
      have hd2 : cs.toList.drop (p + 1 + (toString i).toList.length + 1) =
          (encVal x).toList ++ rest := by
        have e := drop_append_advance hd
        rw [elen] at e
        simpa only [← Nat.add_assoc] using e
      have hsub := ihx cs (g - 1) (fuel - 1)
        (p + 1 + (toString i).toList.length + 1) rest hd2
        (by have hG' : valGas x + 2 ≤ g + 1 := hG; omega)
        (by have hF' : (↑(valFuel x + 1) : Int) ≤ fuel := hF; omega)
        hxd
      unfold decVal; dsimp only
      rw [charAt_head cs p 'J' _ h]
      rw [hdn]
      simp only [Bind.bind, Except.bind]
      rw [dec_one' cs g (fuel - 1) (p + 1 + (toString i).toList.length + 1)
        (p + 1 + (toString i).toList.length + 1 + (encVal x).toList.length)
        (.val x) (by have hG' : valGas x + 2 ≤ g + 1 := hG; omega) hsub
        (by have hF' : (↑(valFuel x + 1) : Int) ≤ fuel := hF; omega)]
      simp only [Bind.bind, Except.bind]
      show Except.ok (Item.val (Val.j i x),
            p + 1 + (toString i).toList.length + 1 +
              (encVal x).toList.length) = _
      have e : (encVal (.j i x)).toList.length =
          1 + ((toString i).toList.length + 1 + (encVal x).toList.length) := by
        show (("J" ++ encNat i ++ encVal x)).toList.length = _
        rw [toList_append, toList_append, List.length_append,
          List.length_append, encNat_toList, List.length_append,
          List.length_cons, List.length_nil,
          show ("J".toList.length : Nat) = 1 from rfl]
        omega
      rw [e, show p + 1 + (toString i).toList.length + 1 +
            (encVal x).toList.length =
          p + (1 + ((toString i).toList.length + 1 +
            (encVal x).toList.length)) from by omega]
  · -- .r fs
    intro fs ihfs cs g fuel p rest h hG hF hD
    obtain ⟨hlen, hdq⟩ := hD
    cases g with
    | zero => have hG0 : valsGas fs + fs.length + 4 ≤ 0 := hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encVal (.r fs)).toList = 'R' ::
          ((encNat (↑fs.length : Int)).toList ++ (encVals fs).toList) := by
        show (("R" ++ encNat ↑fs.length ++ encVals fs)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      simp only [List.cons_append, List.nil_append, List.append_assoc] at h
      have hcat : (catEnc (fun x => encVal (asVal x))
            (fs.map Item.val)).toList =
          (encVals fs).toList := by
        rw [catEnc_map]
        show (catEnc (fun x => encVal (asVal (Item.val x))) fs).toList = _
        rw [show (fun x => encVal (asVal (Item.val x))) = encVal from rfl,
          encVals_catEnc]
      have hd : cs.toList.drop (p + 1) =
          (toString (↑fs.length : Int)).toList ++
            (';' :: ((encVals fs).toList ++ rest)) := by
        have e := drop_succ h
        rw [encNat_toList] at e
        simp only [List.append_assoc, List.cons_append, List.nil_append] at e
        exact e
      have hdl := decList_enc (fun x => encVal (asVal x)) cs g 1 fuel
        (valsGas fs + 1) (fs.map Item.val) (p + 1) rest
        (by rw [List.length_map, hcat]; exact hd)
        (by rw [List.length_map]
            have hG' : valsGas fs + fs.length + 4 ≤ g + 1 := hG; omega)
        (by rw [List.length_map]; exact hlen)
        (by rw [List.length_map]
            exact ⟨by unfold i64Min; omega,
                   by unfold i64Max; omega⟩)
        (by rw [List.length_map]; exact toString_len_lt24 _ hlen)
        (fun g' x hg'1 hg'2 hm p' rest' hd' => by
          obtain ⟨v, hvm, hve⟩ := List.mem_map.mp hm
          subst hve
          have hd'' : cs.toList.drop p' = (encVal v).toList ++ rest' := hd'
          have hF' : (↑(valsFuel fs + 1) : Int) ≤ fuel := hF
          show dec cs g' 1 (fuel - 1) p' =
            .ok (.val v, p' + (encVal v).toList.length)
          exact dec_one' cs g' (fuel - 1) p'
            (p' + (encVal v).toList.length) (.val v)
            (by have := valGas_le_valsGas hvm; omega)
            (ihfs v hvm cs (g' - 1) (fuel - 1) p' rest' hd''
              (by have := valGas_le_valsGas hvm; omega)
              (by have := valFuel_le_valsFuel hvm; omega)
              (dqsV_mem hdq hvm))
            (by omega))
      unfold decVal; dsimp only
      rw [charAt_head cs p 'R' _ h]
      rw [hdl]
      simp only [Bind.bind, Except.bind, Except.pure]
      show Except.ok (Item.val (Val.r ((fs.map Item.val).map asVal)),
            p + 1 + (toString (fs.map Item.val).length).toList.length + 1 +
              (catEnc (fun x => encVal (asVal x))
                (fs.map Item.val)).toList.length) = _
      rw [map_asVal_val, List.length_map, hcat]
      show Except.ok (Item.val (Val.r fs),
            p + 1 + (toString (↑fs.length : Int)).toList.length + 1 +
              (encVals fs).toList.length) = _
      have e : (encVal (.r fs)).toList.length =
          1 + ((toString (↑fs.length : Int)).toList.length + 1 +
            (encVals fs).toList.length) := by
        simp only [hEnc, encNat_toList, List.length_cons,
          List.length_append, List.length_nil]
        omega
      rw [e, show p + 1 + (toString (↑fs.length : Int)).toList.length + 1 +
            (encVals fs).toList.length =
          p + (1 + ((toString (↑fs.length : Int)).toList.length + 1 +
            (encVals fs).toList.length)) from by omega]
  · -- motive_2 nil
    intro x hm; cases hm
  · -- motive_2 cons
    intro x xs' ihx ihxs x' hm
    cases hm with
    | head => exact ihx
    | tail _ hm' => exact ihxs x' hm'

/-! ## `decExpr` inverse

`decExpr` is schema-driven: a one-character tag selects `exprTagKind`,
whose `exprSchema` list drives `decSeq`, and `exprBuild` reassembles the
item vector. The `.call` tag `g` is hand-coded (a `RawFn.local`/`.ext`
subtag, then a counted argument list). The proofs below reuse `decSeq_enc`
/`decList_enc`/`decNat_encInt`/`decStr_enc`/`decTy_enc`/`decVal_enc` plus
the expr IH for `kind = 2` fields. -/

theorem encItem_0 (t : CoreTy) : encItem 0 (.ty t) = encTy t := rfl
theorem encItem_1 (v : Val) : encItem 1 (.val v) = encVal v := rfl
theorem encItem_2 (e : RawExpr) : encItem 2 (.expr e) = encExpr e := rfl
theorem encItem_4 (s : String) : encItem 4 (.str s) = encStr s := rfl
theorem encItem_5 (n : Int) : encItem 5 (.num n) = encNat n := rfl

theorem encItem_10_tys (ts : List CoreTy) :
    (encItem 10 (.list (ts.map Item.ty))).toList =
    (encNat (↑ts.length) ++ encTys ts).toList := by
  show (encNat (↑(ts.map Item.ty).length) ++
    String.join ((ts.map Item.ty).map (encBase 0))).toList = _
  rw [toList_append, toList_append, List.length_map]
  congr 1
  rw [encTys_catEnc]
  show (catEnc (encBase 0) (ts.map Item.ty)).toList = (catEnc encTy ts).toList
  rw [catEnc_map]
  show (catEnc (fun t => encBase 0 (Item.ty t)) ts).toList = _
  rw [show (fun t => encBase 0 (Item.ty t)) = encTy from rfl]

theorem encItem_12_exprs (es : List RawExpr) :
    (encItem 12 (.list (es.map Item.expr))).toList =
    (encNat (↑es.length) ++ encExprs es).toList := by
  show (encNat (↑(es.map Item.expr).length) ++
    String.join ((es.map Item.expr).map (encBase 2))).toList = _
  rw [toList_append, toList_append, List.length_map]
  congr 1
  rw [encExprs_catEnc]
  show (catEnc (encBase 2) (es.map Item.expr)).toList =
    (catEnc encExpr es).toList
  rw [catEnc_map]
  show (catEnc (fun e => encBase 2 (Item.expr e)) es).toList = _
  rw [show (fun e => encBase 2 (Item.expr e)) = encExpr from rfl]

theorem encItem_14_strs (ss : List String) :
    (encItem 14 (.list (ss.map Item.str))).toList =
    (encNat (↑ss.length) ++ String.join (ss.map encStr)).toList := by
  show (encNat (↑(ss.map Item.str).length) ++
    String.join ((ss.map Item.str).map (encBase 4))).toList = _
  rw [toList_append, List.length_map]
  congr 1
  show (String.join ((ss.map Item.str).map (encBase 4))).toList =
    (String.join (ss.map encStr)).toList
  rw [List.map_map]
  show (String.join (ss.map (encBase 4 ∘ Item.str))).toList = _
  rw [show encBase 4 ∘ Item.str = encStr from rfl]

/-- `decStr`-element decoder fact used inside `decList`s of `kind = 4`. -/
theorem decStr_elem (cs : Array Char) (g' : Nat) (fuel : Int) (s : String)
    (p' : Nat) (rest' : List Char)
    (hd : cs.toList.drop p' = (encStr s).toList ++ rest')
    (hg : 1 ≤ g') (hf : ¬ fuel < 0) (hs : s.length ≤ 1024) :
    dec cs g' 4 fuel p' = .ok (.str s, p' + (encStr s).toList.length) := by
  have hd' : cs.toList.drop p' =
      (toString s.length).toList ++ ':' :: (s.toList ++ rest') := by
    rw [encStr_toList] at hd
    simp only [List.append_assoc, List.cons_append] at hd
    exact hd
  have elen : p' + (encStr s).toList.length =
      p' + (toString s.length).toList.length + 1 + s.length := by
    rw [encStr_toList, List.length_append, List.length_cons,
      show (s.toList.length : Nat) = s.length from rfl]
    omega
  rw [elen]
  exact dec_four' cs g' fuel p' _ s hg
    (decStr_enc s cs p' rest' hd' (toString_len_lt24 _ hs) hs) hf

/-- `decNat`-element decoder fact for the `kd = 5` schema field. -/
theorem decNat_elem (cs : Array Char) (i : Int) (h0 : 0 ≤ i) (hin : inI64 i)
    (p' : Nat) (rest' : List Char)
    (hd : cs.toList.drop p' = (encNat i).toList ++ rest') :
    (decNat cs p').map (fun (n, q) => (Item.num n, q)) =
      .ok (.num i, p' + (encNat i).toList.length) := by
  have elen : p' + (encNat i).toList.length =
      p' + (toString i).toList.length + 1 := by
    rw [encNat_toList, List.length_append,
      show ([';'] : List Char).length = 1 from rfl]
    omega
  rw [elen, decNat_encInt i h0 hin cs p' rest' hd]
  rfl

/-- `decExpr` reads an `encExpr` expression back. -/
theorem decExpr_enc : ∀ (e : RawExpr) (cs : Array Char) (g : Nat) (fuel : Int)
    (p : Nat) (rest : List Char),
    cs.toList.drop p = (encExpr e).toList ++ rest →
    exprGas e ≤ g → (exprFuel e : Int) ≤ fuel → dqE e →
    decExpr cs g fuel p = Except.ok (Item.expr e, p + (encExpr e).toList.length) := by
  intro e
  refine RawExpr.rec
    (motive_1 := fun e => ∀ (cs : Array Char) (g : Nat) (fuel : Int)
        (p : Nat) (rest : List Char),
        cs.toList.drop p = (encExpr e).toList ++ rest →
        exprGas e ≤ g → (exprFuel e : Int) ≤ fuel → dqE e →
        decExpr cs g fuel p = Except.ok (Item.expr e, p + (encExpr e).toList.length))
    (motive_2 := fun es => ∀ e, e ∈ es → ∀ (cs : Array Char) (g : Nat)
        (fuel : Int) (p : Nat) (rest : List Char),
        cs.toList.drop p = (encExpr e).toList ++ rest →
        exprGas e ≤ g → (exprFuel e : Int) ≤ fuel → dqE e →
        decExpr cs g fuel p = Except.ok (Item.expr e, p + (encExpr e).toList.length))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · -- .lit x t
    intro x t cs g fuel p rest h hG hF hD
    obtain ⟨hdx, hdt⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.lit x t)).toList =
          '0' :: ((encVal x).toList ++ (encTy t).toList) := by
        show (("0" ++ encVal x ++ encTy t)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [1, 0] [.val x, .ty t]).toList =
          (encVal x ++ encTy t).toList := by
        show ((encVal x) ++ ((encTy t) ++ "")).toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [1, 0] [.val x, .ty t]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel (max (valGas x) (tyGas t) + 1)
        [1, 0] [.val x, .ty t] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show dec cs g' 1 (fuel - 1) p' =
              Except.ok (.val x, p' + (encVal x).toList.length)
            exact dec_one' cs g' (fuel - 1) p' _ (.val x) (by omega)
              (decVal_enc x cs (g' - 1) (fuel - 1) p' rest' hd'
                (by simp only [exprGas] at hG; omega)
                (by simp only [exprFuel] at hF; omega) hdx)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 0 (fuel - 1) p' =
              Except.ok (.ty t, p' + (encTy t).toList.length)
            exact dec_zero' cs g' (fuel - 1) p' _ (.ty t) (by omega)
              (decTy_enc t cs (g' - 1) (fuel - 1) p' rest' hd'
                (by simp only [exprGas] at hG; omega)
                (by simp only [exprFuel] at hF; omega) hdt)
              (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p '0' _ h]
      show bind (decSeq cs g fuel (p + 1) [1, 0]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 0 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.lit x t),
            p + 1 + (encItems [1, 0] [.val x, .ty t]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .var i
    intro i cs g fuel p rest h hG hF hD
    obtain ⟨h0, hin⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.var i)).toList = '1' :: (encNat i).toList := by
        show (("1" ++ encNat i)).toList = _
        simp only [toList_append]; rfl
      have hItems : (encItems [5] [.num i]).toList = (encNat i).toList := by
        show ((encNat i) ++ "").toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil]
      have hd : cs.toList.drop (p + 1) =
          (encItems [5] [.num i]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel 0 [5] [.num i] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv _ _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩
          show (decNat cs p').map (fun (n, q) => (Item.num n, q)) =
            Except.ok (.num i, p' + (encNat i).toList.length)
          exact decNat_elem cs i h0 hin p' rest' hd')
      unfold decExpr; dsimp only
      rw [charAt_head cs p '1' _ h]
      show bind (decSeq cs g fuel (p + 1) [5]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 1 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.var i),
            p + 1 + (encItems [5] [.num i]).toList.length) = _
      rw [hItems]
      have e := congrArg List.length hEnc
      simp only [List.length_cons] at e
      rw [e]; congr 1; congr 1; omega
  · -- .letE a b
    intro a b iha ihb cs g fuel p rest h hG hF hD
    obtain ⟨hda, hdb⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.letE a b)).toList =
          '2' :: ((encExpr a).toList ++ (encExpr b).toList) := by
        show (("2" ++ encExpr a ++ encExpr b)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [2, 2] [.expr a, .expr b]).toList =
          (encExpr a ++ encExpr b).toList := by
        show ((encExpr a) ++ ((encExpr b) ++ "")).toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [2, 2] [.expr a, .expr b]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel (max (exprGas a) (exprGas b) + 1)
        [2, 2] [.expr a, .expr b] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr a, p' + (encExpr a).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr a) (by omega)
              (iha cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hda)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr b, p' + (encExpr b).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr b) (by omega)
              (ihb cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdb)
              (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p '2' _ h]
      show bind (decSeq cs g fuel (p + 1) [2, 2]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 2 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.letE a b),
            p + 1 + (encItems [2, 2] [.expr a, .expr b]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .ifE c th el
    intro c th el ihc ihth ihel cs g fuel p rest h hG hF hD
    obtain ⟨hdc, hdth, hdel⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.ifE c th el)).toList =
          '3' :: ((encExpr c).toList ++ (encExpr th).toList ++
            (encExpr el).toList) := by
        show (("3" ++ encExpr c ++ encExpr th ++ encExpr el)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [2, 2, 2] [.expr c, .expr th, .expr el]).toList =
          (encExpr c ++ encExpr th ++ encExpr el).toList := by
        show ((encExpr c) ++ ((encExpr th) ++ ((encExpr el) ++ ""))).toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [2, 2, 2] [.expr c, .expr th, .expr el]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel
        (max (exprGas c) (max (exprGas th) (exprGas el)) + 1)
        [2, 2, 2] [.expr c, .expr th, .expr el] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr c, p' + (encExpr c).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr c) (by omega)
              (ihc cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdc)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr th, p' + (encExpr th).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr th) (by omega)
              (ihth cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdth)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr el, p' + (encExpr el).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr el) (by omega)
              (ihel cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdel)
              (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p '3' _ h]
      show bind (decSeq cs g fuel (p + 1) [2, 2, 2]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 3 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.ifE c th el),
            p + 1 + (encItems [2, 2, 2] [.expr c, .expr th, .expr el]).toList.length)
            = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .pair a b
    intro a b iha ihb cs g fuel p rest h hG hF hD
    obtain ⟨hda, hdb⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.pair a b)).toList =
          '4' :: ((encExpr a).toList ++ (encExpr b).toList) := by
        show (("4" ++ encExpr a ++ encExpr b)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [2, 2] [.expr a, .expr b]).toList =
          (encExpr a ++ encExpr b).toList := by
        show ((encExpr a) ++ ((encExpr b) ++ "")).toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [2, 2] [.expr a, .expr b]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel (max (exprGas a) (exprGas b) + 1)
        [2, 2] [.expr a, .expr b] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr a, p' + (encExpr a).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr a) (by omega)
              (iha cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hda)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr b, p' + (encExpr b).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr b) (by omega)
              (ihb cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdb)
              (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p '4' _ h]
      show bind (decSeq cs g fuel (p + 1) [2, 2]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 4 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.pair a b),
            p + 1 + (encItems [2, 2] [.expr a, .expr b]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .fst a
    intro a iha cs g fuel p rest h hG hF hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.fst a)).toList = '5' :: (encExpr a).toList := by
        show (("5" ++ encExpr a)).toList = _
        simp only [toList_append]; rfl
      have hItems : (encItems [2] [.expr a]).toList = (encExpr a).toList := by
        show ((encExpr a) ++ "").toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil]
      have hd : cs.toList.drop (p + 1) =
          (encItems [2] [.expr a]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel (exprGas a + 1) [2] [.expr a] g (p + 1)
        rest hd rfl (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩
          show dec cs g' 2 (fuel - 1) p' =
            Except.ok (Item.expr a, p' + (encExpr a).toList.length)
          exact dec_two' cs g' (fuel - 1) p' _ (Item.expr a) (by omega)
            (iha cs (g' - 1) (fuel - 1) p' rest' hd' (by omega)
              (by simp only [exprFuel] at hF; omega) hD)
            (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p '5' _ h]
      show bind (decSeq cs g fuel (p + 1) [2]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 5 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.fst a),
            p + 1 + (encItems [2] [.expr a]).toList.length) = _
      rw [hItems]
      have e := congrArg List.length hEnc
      simp only [List.length_cons] at e
      rw [e]; congr 1; congr 1; omega
  · -- .snd a
    intro a iha cs g fuel p rest h hG hF hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.snd a)).toList = '6' :: (encExpr a).toList := by
        show (("6" ++ encExpr a)).toList = _
        simp only [toList_append]; rfl
      have hItems : (encItems [2] [.expr a]).toList = (encExpr a).toList := by
        show ((encExpr a) ++ "").toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil]
      have hd : cs.toList.drop (p + 1) =
          (encItems [2] [.expr a]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel (exprGas a + 1) [2] [.expr a] g (p + 1)
        rest hd rfl (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩
          show dec cs g' 2 (fuel - 1) p' =
            Except.ok (Item.expr a, p' + (encExpr a).toList.length)
          exact dec_two' cs g' (fuel - 1) p' _ (Item.expr a) (by omega)
            (iha cs (g' - 1) (fuel - 1) p' rest' hd' (by omega)
              (by simp only [exprFuel] at hF; omega) hD)
            (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p '6' _ h]
      show bind (decSeq cs g fuel (p + 1) [2]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 6 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.snd a),
            p + 1 + (encItems [2] [.expr a]).toList.length) = _
      rw [hItems]
      have e := congrArg List.length hEnc
      simp only [List.length_cons] at e
      rw [e]; congr 1; congr 1; omega
  · -- .inj i ts a
    intro i ts a iha cs g fuel p rest h hG hF hD
    obtain ⟨h0, hin, hlen, hdqs, hda⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hcat : (encTys ts).toList =
          (catEnc (encBase 0) (ts.map Item.ty)).toList := by
        rw [encTys_catEnc, catEnc_map]
        show (catEnc encTy ts).toList =
          (catEnc (fun t => encBase 0 (Item.ty t)) ts).toList
        rw [show (fun t => encBase 0 (Item.ty t)) = encTy from rfl]
      have hEnc : (encExpr (.inj i ts a)).toList = '7' ::
          ((encNat i).toList ++ (encNat ↑ts.length).toList ++
            (encTys ts).toList ++ (encExpr a).toList) := by
        show (("7" ++ encNat i ++ encNat ↑ts.length ++ encTys ts ++
          encExpr a)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [5, 10, 2]
            [.num i, .list (ts.map Item.ty), .expr a]).toList =
          (encNat i ++ (encNat ↑ts.length ++ encTys ts) ++ encExpr a).toList := by
        show (encNat i ++ (encItem 10 (.list (ts.map Item.ty)) ++
            (encExpr a ++ ""))).toList = _
        simp only [encItem_10_tys, toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [5, 10, 2] [.num i, .list (ts.map Item.ty), .expr a]).toList
            ++ rest := by
        have e := drop_succ h
        rw [hItems]
        simp only [toList_append, ← List.append_assoc]
        exact e
      have hseq := decSeq_enc cs fuel
        (max (tysGas ts + ts.length + 3) (exprGas a + 1))
        [5, 10, 2] [.num i, .list (ts.map Item.ty), .expr a] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show (decNat cs p').map (fun (n, q) => (Item.num n, q)) =
              Except.ok (.num i, p' + (encNat i).toList.length)
            exact decNat_elem cs i h0 hin p' rest' hd'
          · show decList cs g' 0 fuel p' =
              Except.ok (.list (ts.map Item.ty),
                p' + (encItem 10 (.list (ts.map Item.ty))).toList.length)
            have hdL : cs.toList.drop p' =
                (toString (↑(ts.map Item.ty).length)).toList ++ ';' ::
                ((catEnc (encBase 0) (ts.map Item.ty)).toList ++ rest') := by
              rw [List.length_map, ← hcat]
              rw [encItem_10_tys] at hd'
              simp only [toList_append, encNat_toList, List.append_assoc,
                List.cons_append, List.nil_append] at hd'
              exact hd'
            rw [show p' + (encItem 10 (.list (ts.map Item.ty))).toList.length =
                p' + (toString (↑(ts.map Item.ty).length : Int)).toList.length + 1 +
                  (catEnc (encBase 0) (ts.map Item.ty)).toList.length from by
              rw [encItem_10_tys, toList_append, List.length_append,
                encNat_toList, List.length_append,
                show ([';'] : List Char).length = 1 from rfl, ← hcat,
                List.length_map]; omega]
            exact decList_enc (encBase 0) cs g' 0 fuel (tysGas ts + 1)
              (ts.map Item.ty) p' rest' hdL
              (by rw [List.length_map]; omega)
              (by rw [List.length_map]; exact hlen)
              (by rw [List.length_map]
                  exact ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩)
              (by rw [List.length_map]; exact toString_len_lt24 _ hlen)
              (fun g'' x hg''1 _ hm p'' rest'' hd'' => by
                obtain ⟨t', htm, hte⟩ := List.mem_map.mp hm
                subst hte
                have hd''' : cs.toList.drop p'' =
                    (encTy t').toList ++ rest'' := hd''
                show dec cs g'' 0 (fuel - 1) p'' =
                  .ok (Item.ty t', p'' + (encTy t').toList.length)
                exact dec_zero' cs g'' (fuel - 1) p''
                  (p'' + (encTy t').toList.length) (Item.ty t') (by omega)
                  (decTy_enc t' cs (g'' - 1) (fuel - 1) p'' rest'' hd'''
                    (by have := tyGas_le_tysGas htm; omega)
                    (by have := tyFuel_le_tysFuel htm;
                        simp only [exprFuel] at hF; omega)
                    (dqsT_mem hdqs htm))
                  (by simp only [exprFuel] at hF; omega))
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr a, p' + (encExpr a).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr a) (by omega)
              (iha cs (g' - 1) (fuel - 1) p' rest' hd' (by omega)
                (by simp only [exprFuel] at hF; omega) hda)
              (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p '7' _ h]
      show bind (decSeq cs g fuel (p + 1) [5, 10, 2]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 7 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.inj i
            (List.map asTy (ts.map Item.ty)) a), _) = _
      rw [show (ts.map Item.ty).map asTy = ts from
        map_asTy_ty ts]
      show Except.ok (Item.expr (.inj i ts a),
            p + 1 + (encItems [5, 10, 2] [.num i, .list (ts.map Item.ty),
              .expr a]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .matchE s bs
    intro s bs ihs ihbs cs g fuel p rest h hG hF hD
    obtain ⟨hds, hlen, hdqs⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hcat : (encExprs bs).toList =
          (catEnc (encBase 2) (bs.map Item.expr)).toList := by
        rw [encExprs_catEnc, catEnc_map]
        show (catEnc encExpr bs).toList =
          (catEnc (fun e => encBase 2 (Item.expr e)) bs).toList
        rw [show (fun e => encBase 2 (Item.expr e)) = encExpr from rfl]
      have hEnc : (encExpr (.matchE s bs)).toList = '8' ::
          ((encExpr s).toList ++ (encNat ↑bs.length).toList ++
            (encExprs bs).toList) := by
        show (("8" ++ encExpr s ++ encNat ↑bs.length ++ encExprs bs)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [2, 12] [.expr s, .list (bs.map Item.expr)]).toList =
          (encExpr s ++ (encNat ↑bs.length ++ encExprs bs)).toList := by
        show ((encExpr s) ++ ((encItem 12 (.list (bs.map Item.expr))) ++ "")).toList = _
        simp only [encItem_12_exprs, toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [2, 12] [.expr s, .list (bs.map Item.expr)]).toList
            ++ rest := by
        have e := drop_succ h
        rw [hItems]
        simp only [toList_append, ← List.append_assoc]
        exact e
      have hseq := decSeq_enc cs fuel
        (max (exprGas s + 1) (exprsGas bs + bs.length + 3))
        [2, 12] [.expr s, .list (bs.map Item.expr)] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr s, p' + (encExpr s).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr s) (by omega)
              (ihs cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hds)
              (by simp only [exprFuel] at hF; omega)
          · show decList cs g' 2 fuel p' =
              Except.ok (.list (bs.map Item.expr),
                p' + (encItem 12 (.list (bs.map Item.expr))).toList.length)
            have hdL : cs.toList.drop p' =
                (toString (↑(bs.map Item.expr).length)).toList ++ ';' ::
                ((catEnc (encBase 2) (bs.map Item.expr)).toList ++ rest') := by
              rw [List.length_map, ← hcat]
              rw [encItem_12_exprs] at hd'
              simp only [toList_append, encNat_toList, List.append_assoc,
                List.cons_append, List.nil_append] at hd'
              exact hd'
            rw [show p' + (encItem 12 (.list (bs.map Item.expr))).toList.length =
                p' + (toString (↑(bs.map Item.expr).length : Int)).toList.length + 1 +
                  (catEnc (encBase 2) (bs.map Item.expr)).toList.length from by
              rw [encItem_12_exprs, toList_append, List.length_append,
                encNat_toList, List.length_append,
                show ([';'] : List Char).length = 1 from rfl, ← hcat,
                List.length_map]; omega]
            exact decList_enc (encBase 2) cs g' 2 fuel (exprsGas bs + 1)
              (bs.map Item.expr) p' rest' hdL
              (by rw [List.length_map]; omega)
              (by rw [List.length_map]; exact hlen)
              (by rw [List.length_map]
                  exact ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩)
              (by rw [List.length_map]; exact toString_len_lt24 _ hlen)
              (fun g'' x hg''1 _ hm p'' rest'' hd'' => by
                obtain ⟨e', hem, hte⟩ := List.mem_map.mp hm
                subst hte
                have hd''' : cs.toList.drop p'' =
                    (encExpr e').toList ++ rest'' := hd''
                show dec cs g'' 2 (fuel - 1) p'' =
                  .ok (Item.expr e', p'' + (encExpr e').toList.length)
                exact dec_two' cs g'' (fuel - 1) p''
                  (p'' + (encExpr e').toList.length) (Item.expr e') (by omega)
                  (ihbs e' hem cs (g'' - 1) (fuel - 1) p'' rest'' hd'''
                    (by have := exprGas_le_exprsGas hem; omega)
                    (by have := exprFuel_le_exprsFuel hem;
                        simp only [exprFuel] at hF; omega)
                    (dqsE_mem hdqs hem))
                  (by simp only [exprFuel] at hF; omega)))
      unfold decExpr; dsimp only
      rw [charAt_head cs p '8' _ h]
      show bind (decSeq cs g fuel (p + 1) [2, 12]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 8 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.matchE s
            (List.map asExpr (bs.map Item.expr))), _) = _
      rw [show (bs.map Item.expr).map asExpr = bs from
        map_asExpr_expr bs]
      show Except.ok (Item.expr (.matchE s bs),
            p + 1 + (encItems [2, 12] [.expr s,
              .list (bs.map Item.expr)]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .recordE keys fs
    intro keys fs ihfs cs g fuel p rest h hG hF hD
    obtain ⟨hlen, hklen, hflen, hdqs⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hcat : (encExprs fs).toList =
          (catEnc (encBase 2) (fs.map Item.expr)).toList := by
        rw [encExprs_catEnc, catEnc_map]
        show (catEnc encExpr fs).toList =
          (catEnc (fun e => encBase 2 (Item.expr e)) fs).toList
        rw [show (fun e => encBase 2 (Item.expr e)) = encExpr from rfl]
      have hcat' : (String.join (keys.map encStr)).toList =
          (catEnc (encBase 4) (keys.map Item.str)).toList := by
        show (catEnc encStr keys).toList =
          (catEnc (encBase 4) (keys.map Item.str)).toList
        rw [catEnc_map]
        show (catEnc encStr keys).toList =
          (catEnc (fun s => encBase 4 (Item.str s)) keys).toList
        rw [show (fun s => encBase 4 (Item.str s)) = encStr from rfl]
      have hEnc : (encExpr (.recordE keys fs)).toList = '9' ::
          ((encNat ↑keys.length).toList ++
            (String.join (keys.map encStr)).toList ++
            (encNat ↑fs.length).toList ++ (encExprs fs).toList) := by
        show (("9" ++ encNat ↑keys.length ++ String.join (keys.map encStr) ++
          encNat ↑fs.length ++ encExprs fs)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [14, 12]
            [.list (keys.map Item.str), .list (fs.map Item.expr)]).toList =
          (encNat ↑keys.length ++ String.join (keys.map encStr) ++
            encNat ↑fs.length ++ encExprs fs).toList := by
        show ((encItem 14 (.list (keys.map Item.str))) ++
            ((encItem 12 (.list (fs.map Item.expr))) ++ "")).toList = _
        simp only [encItem_14_strs, encItem_12_exprs, toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [14, 12]
            [.list (keys.map Item.str), .list (fs.map Item.expr)]).toList
            ++ rest := by
        have e := drop_succ h
        rw [hItems]
        simp only [toList_append, ← List.append_assoc]
        exact e
      have hseq := decSeq_enc cs fuel
        (max (keys.length + 3) (exprsGas fs + fs.length + 3))
        [14, 12] [.list (keys.map Item.str), .list (fs.map Item.expr)]
        g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show decList cs g' 4 fuel p' =
              Except.ok (.list (keys.map Item.str),
                p' + (encItem 14 (.list (keys.map Item.str))).toList.length)
            have hdL : cs.toList.drop p' =
                (toString (↑(keys.map Item.str).length)).toList ++ ';' ::
                ((catEnc (encBase 4) (keys.map Item.str)).toList ++ rest') := by
              rw [List.length_map, ← hcat']
              rw [encItem_14_strs] at hd'
              simp only [toList_append, encNat_toList, List.append_assoc,
                List.cons_append, List.nil_append] at hd'
              exact hd'
            rw [show p' + (encItem 14 (.list (keys.map Item.str))).toList.length =
                p' + (toString (↑(keys.map Item.str).length : Int)).toList.length + 1 +
                  (catEnc (encBase 4) (keys.map Item.str)).toList.length from by
              rw [encItem_14_strs, toList_append, List.length_append,
                encNat_toList, List.length_append,
                show ([';'] : List Char).length = 1 from rfl, ← hcat',
                List.length_map]; omega]
            exact decList_enc (encBase 4) cs g' 4 fuel 1
              (keys.map Item.str) p' rest' hdL
              (by rw [List.length_map]; omega)
              (by rw [List.length_map]; exact hlen)
              (by rw [List.length_map]
                  exact ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩)
              (by rw [List.length_map]; exact toString_len_lt24 _ hlen)
              (fun g'' x hg''1 _ hm p'' rest'' hd'' => by
                obtain ⟨s', hsm, hte⟩ := List.mem_map.mp hm
                subst hte
                have hd''' : cs.toList.drop p'' =
                    (encStr s').toList ++ rest'' := hd''
                show dec cs g'' 4 (fuel - 1) p'' =
                  .ok (Item.str s', p'' + (encStr s').toList.length)
                exact decStr_elem cs g'' (fuel - 1) s' p'' rest'' hd'''
                  hg''1
                  (by simp only [exprFuel] at hF; omega)
                  (hklen s' hsm))
          · show decList cs g' 2 fuel p' =
              Except.ok (.list (fs.map Item.expr),
                p' + (encItem 12 (.list (fs.map Item.expr))).toList.length)
            have hdL : cs.toList.drop p' =
                (toString (↑(fs.map Item.expr).length)).toList ++ ';' ::
                ((catEnc (encBase 2) (fs.map Item.expr)).toList ++ rest') := by
              rw [List.length_map, ← hcat]
              rw [encItem_12_exprs] at hd'
              simp only [toList_append, encNat_toList, List.append_assoc,
                List.cons_append, List.nil_append] at hd'
              exact hd'
            rw [show p' + (encItem 12 (.list (fs.map Item.expr))).toList.length =
                p' + (toString (↑(fs.map Item.expr).length : Int)).toList.length + 1 +
                  (catEnc (encBase 2) (fs.map Item.expr)).toList.length from by
              rw [encItem_12_exprs, toList_append, List.length_append,
                encNat_toList, List.length_append,
                show ([';'] : List Char).length = 1 from rfl, ← hcat,
                List.length_map]; omega]
            exact decList_enc (encBase 2) cs g' 2 fuel (exprsGas fs + 1)
              (fs.map Item.expr) p' rest' hdL
              (by rw [List.length_map]; omega)
              (by rw [List.length_map]; exact hflen)
              (by rw [List.length_map]
                  exact ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩)
              (by rw [List.length_map]; exact toString_len_lt24 _ hflen)
              (fun g'' x hg''1 _ hm p'' rest'' hd'' => by
                obtain ⟨e', hem, hte⟩ := List.mem_map.mp hm
                subst hte
                have hd''' : cs.toList.drop p'' =
                    (encExpr e').toList ++ rest'' := hd''
                show dec cs g'' 2 (fuel - 1) p'' =
                  .ok (Item.expr e', p'' + (encExpr e').toList.length)
                exact dec_two' cs g'' (fuel - 1) p''
                  (p'' + (encExpr e').toList.length) (Item.expr e') (by omega)
                  (ihfs e' hem cs (g'' - 1) (fuel - 1) p'' rest'' hd'''
                    (by have := exprGas_le_exprsGas hem; omega)
                    (by have := exprFuel_le_exprsFuel hem;
                        simp only [exprFuel] at hF; omega)
                    (dqsE_mem hdqs hem))
                  (by simp only [exprFuel] at hF; omega)))
      unfold decExpr; dsimp only
      rw [charAt_head cs p '9' _ h]
      show bind (decSeq cs g fuel (p + 1) [14, 12]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 9 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.recordE
            (List.map asStr (keys.map Item.str))
            (List.map asExpr (fs.map Item.expr))), _) = _
      rw [show (keys.map Item.str).map asStr = keys from
        map_asStr_str keys]
      rw [show (fs.map Item.expr).map asExpr = fs from
        map_asExpr_expr fs]
      show Except.ok (Item.expr (.recordE keys fs),
            p + 1 + (encItems [14, 12] [.list (keys.map Item.str),
              .list (fs.map Item.expr)]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .field r i
    intro r i ihr cs g fuel p rest h hG hF hD
    obtain ⟨hdr, h0, hin⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.field r i)).toList = 'a' ::
          ((encExpr r).toList ++ (encNat i).toList) := by
        show (("a" ++ encExpr r ++ encNat i)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [2, 5] [.expr r, .num i]).toList =
          (encExpr r ++ encNat i).toList := by
        show ((encExpr r) ++ ((encNat i) ++ "")).toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil]
      have hd : cs.toList.drop (p + 1) =
          (encItems [2, 5] [.expr r, .num i]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel (exprGas r + 1)
        [2, 5] [.expr r, .num i] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr r, p' + (encExpr r).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr r) (by omega)
              (ihr cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdr)
              (by simp only [exprFuel] at hF; omega)
          · show (decNat cs p').map (fun (n, q) => (Item.num n, q)) =
              Except.ok (.num i, p' + (encNat i).toList.length)
            exact decNat_elem cs i h0 hin p' rest' hd')
      unfold decExpr; dsimp only
      rw [charAt_head cs p 'a' _ h]
      show bind (decSeq cs g fuel (p + 1) [2, 5]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 10 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.field r i),
            p + 1 + (encItems [2, 5] [.expr r, .num i]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .nil t
    intro t cs g fuel p rest h hG hF hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.nil t)).toList = 'b' :: (encTy t).toList := by
        show (("b" ++ encTy t)).toList = _
        simp only [toList_append]; rfl
      have hItems : (encItems [0] [.ty t]).toList = (encTy t).toList := by
        show ((encTy t) ++ "").toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil]
      have hd : cs.toList.drop (p + 1) =
          (encItems [0] [.ty t]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel (tyGas t + 1) [0] [.ty t] g (p + 1)
        rest hd rfl (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩
          show dec cs g' 0 (fuel - 1) p' =
            Except.ok (.ty t, p' + (encTy t).toList.length)
          exact dec_zero' cs g' (fuel - 1) p' _ (.ty t) (by omega)
            (decTy_enc t cs (g' - 1) (fuel - 1) p' rest' hd'
              (by simp only [exprGas] at hG; omega)
              (by simp only [exprFuel] at hF; omega) hD) (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p 'b' _ h]
      show bind (decSeq cs g fuel (p + 1) [0]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 11 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.nil t),
            p + 1 + (encItems [0] [.ty t]).toList.length) = _
      rw [hItems]
      have e := congrArg List.length hEnc
      simp only [List.length_cons] at e
      rw [e]; congr 1; congr 1; omega
  · -- .cons h' tl — named to avoid clash with List.cons
    intro h' tl ihh ihtl cs g fuel p rest h hG hF hD
    obtain ⟨hdh, hdtl⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.cons h' tl)).toList =
          'c' :: ((encExpr h').toList ++ (encExpr tl).toList) := by
        show (("c" ++ encExpr h' ++ encExpr tl)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [2, 2] [.expr h', .expr tl]).toList =
          (encExpr h' ++ encExpr tl).toList := by
        show ((encExpr h') ++ ((encExpr tl) ++ "")).toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [2, 2] [.expr h', .expr tl]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel (max (exprGas h') (exprGas tl) + 1)
        [2, 2] [.expr h', .expr tl] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr h', p' + (encExpr h').toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr h') (by omega)
              (ihh cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdh)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr tl, p' + (encExpr tl).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr tl) (by omega)
              (ihtl cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdtl)
              (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p 'c' _ h]
      show bind (decSeq cs g fuel (p + 1) [2, 2]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 12 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.cons h' tl),
            p + 1 + (encItems [2, 2] [.expr h', .expr tl]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .fold l i b
    intro l i b ihl ihi ihb cs g fuel p rest h hG hF hD
    obtain ⟨hdl, hdi, hdb⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.fold l i b)).toList =
          'd' :: ((encExpr l).toList ++ (encExpr i).toList ++
            (encExpr b).toList) := by
        show (("d" ++ encExpr l ++ encExpr i ++ encExpr b)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [2, 2, 2] [.expr l, .expr i, .expr b]).toList =
          (encExpr l ++ encExpr i ++ encExpr b).toList := by
        show ((encExpr l) ++ ((encExpr i) ++ ((encExpr b) ++ ""))).toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [2, 2, 2] [.expr l, .expr i, .expr b]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel
        (max (exprGas l) (max (exprGas i) (exprGas b)) + 1)
        [2, 2, 2] [.expr l, .expr i, .expr b] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr l, p' + (encExpr l).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr l) (by omega)
              (ihl cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdl)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr i, p' + (encExpr i).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr i) (by omega)
              (ihi cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdi)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr b, p' + (encExpr b).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr b) (by omega)
              (ihb cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdb)
              (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p 'd' _ h]
      show bind (decSeq cs g fuel (p + 1) [2, 2, 2]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 13 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.fold l i b),
            p + 1 + (encItems [2, 2, 2]
              [.expr l, .expr i, .expr b]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .fix i l s st
    intro i l s st ihi ihl ihs ihst cs g fuel p rest h hG hF hD
    obtain ⟨hdi, hdl, hds, hdst⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.fix i l s st)).toList =
          'e' :: ((encExpr i).toList ++ (encExpr l).toList ++
            (encExpr s).toList ++ (encExpr st).toList) := by
        show (("e" ++ encExpr i ++ encExpr l ++ encExpr s ++
          encExpr st)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [2, 2, 2, 2]
            [.expr i, .expr l, .expr s, .expr st]).toList =
          (encExpr i ++ encExpr l ++ encExpr s ++ encExpr st).toList := by
        show ((encExpr i) ++ ((encExpr l) ++ ((encExpr s) ++
            ((encExpr st) ++ "")))).toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [2, 2, 2, 2] [.expr i, .expr l, .expr s, .expr st]).toList
            ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel
        (max (exprGas i) (max (exprGas l) (max (exprGas s) (exprGas st))) + 1)
        [2, 2, 2, 2] [.expr i, .expr l, .expr s, .expr st] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr i, p' + (encExpr i).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr i) (by omega)
              (ihi cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdi)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr l, p' + (encExpr l).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr l) (by omega)
              (ihl cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdl)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr s, p' + (encExpr s).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr s) (by omega)
              (ihs cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hds)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr st, p' + (encExpr st).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr st) (by omega)
              (ihst cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdst)
              (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p 'e' _ h]
      show bind (decSeq cs g fuel (p + 1) [2, 2, 2, 2]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 14 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.fix i l s st),
            p + 1 + (encItems [2, 2, 2, 2]
              [.expr i, .expr l, .expr s, .expr st]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .prim op args
    intro op args ihargs cs g fuel p rest h hG hF hD
    obtain ⟨hop, hlen, hdqs⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hcat : (encExprs args).toList =
          (catEnc (encBase 2) (args.map Item.expr)).toList := by
        rw [encExprs_catEnc, catEnc_map]
        show (catEnc encExpr args).toList =
          (catEnc (fun e => encBase 2 (Item.expr e)) args).toList
        rw [show (fun e => encBase 2 (Item.expr e)) = encExpr from rfl]
      have hEnc : (encExpr (.prim op args)).toList = 'f' ::
          ((encStr op).toList ++ (encNat ↑args.length).toList ++
            (encExprs args).toList) := by
        show (("f" ++ encStr op ++ encNat ↑args.length ++
          encExprs args)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [4, 12]
            [.str op, .list (args.map Item.expr)]).toList =
          (encStr op ++ (encNat ↑args.length ++ encExprs args)).toList := by
        show (encStr op ++ (encItem 12 (.list (args.map Item.expr)) ++
            "")).toList = _
        simp only [encItem_12_exprs, toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [4, 12] [.str op, .list (args.map Item.expr)]).toList
            ++ rest := by
        have e := drop_succ h
        rw [hItems]
        simp only [toList_append, ← List.append_assoc]
        exact e
      have hseq := decSeq_enc cs fuel
        (max 1 (exprsGas args + args.length + 3))
        [4, 12] [.str op, .list (args.map Item.expr)] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show dec cs g' 4 (fuel - 1) p' =
              Except.ok (.str op, p' + (encStr op).toList.length)
            exact decStr_elem cs g' (fuel - 1) op p' rest' hd' (by omega)
              (by simp only [exprFuel] at hF; omega) hop
          · show decList cs g' 2 fuel p' =
              Except.ok (.list (args.map Item.expr),
                p' + (encItem 12 (.list (args.map Item.expr))).toList.length)
            have hdL : cs.toList.drop p' =
                (toString (↑(args.map Item.expr).length)).toList ++ ';' ::
                ((catEnc (encBase 2) (args.map Item.expr)).toList ++ rest') := by
              rw [List.length_map, ← hcat]
              rw [encItem_12_exprs] at hd'
              simp only [toList_append, encNat_toList, List.append_assoc,
                List.cons_append, List.nil_append] at hd'
              exact hd'
            rw [show p' + (encItem 12 (.list (args.map Item.expr))).toList.length =
                p' + (toString (↑(args.map Item.expr).length : Int)).toList.length + 1 +
                  (catEnc (encBase 2) (args.map Item.expr)).toList.length from by
              rw [encItem_12_exprs, toList_append, List.length_append,
                encNat_toList, List.length_append,
                show ([';'] : List Char).length = 1 from rfl, ← hcat,
                List.length_map]; omega]
            exact decList_enc (encBase 2) cs g' 2 fuel (exprsGas args + 1)
              (args.map Item.expr) p' rest' hdL
              (by rw [List.length_map]; omega)
              (by rw [List.length_map]; exact hlen)
              (by rw [List.length_map]
                  exact ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩)
              (by rw [List.length_map]; exact toString_len_lt24 _ hlen)
              (fun g'' x hg''1 _ hm p'' rest'' hd'' => by
                obtain ⟨e', hem, hte⟩ := List.mem_map.mp hm
                subst hte
                have hd''' : cs.toList.drop p'' =
                    (encExpr e').toList ++ rest'' := hd''
                show dec cs g'' 2 (fuel - 1) p'' =
                  .ok (Item.expr e', p'' + (encExpr e').toList.length)
                exact dec_two' cs g'' (fuel - 1) p''
                  (p'' + (encExpr e').toList.length) (Item.expr e') (by omega)
                  (ihargs e' hem cs (g'' - 1) (fuel - 1) p'' rest'' hd'''
                    (by have := exprGas_le_exprsGas hem; omega)
                    (by have := exprFuel_le_exprsFuel hem;
                        simp only [exprFuel] at hF; omega)
                    (dqsE_mem hdqs hem))
                  (by simp only [exprFuel] at hF; omega)))
      unfold decExpr; dsimp only
      rw [charAt_head cs p 'f' _ h]
      show bind (decSeq cs g fuel (p + 1) [4, 12]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 15 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.prim op
            (List.map asExpr (args.map Item.expr))), _) = _
      rw [show (args.map Item.expr).map asExpr = args from
        map_asExpr_expr args]
      show Except.ok (Item.expr (.prim op args),
            p + 1 + (encItems [4, 12] [.str op,
              .list (args.map Item.expr)]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .call f args — 'g' arm: nested fn-tag decode, then decList
    intro f args ihargs cs g fuel p rest h hG hF hD
    obtain ⟨hlen, hdqs, hfD⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hcat : (encExprs args).toList =
          (catEnc (encBase 2) (args.map Item.expr)).toList := by
        rw [encExprs_catEnc, catEnc_map]
        show (catEnc encExpr args).toList =
          (catEnc (fun e => encBase 2 (Item.expr e)) args).toList
        rw [show (fun e => encBase 2 (Item.expr e)) = encExpr from rfl]
      cases f with
      | «local» i =>
        obtain ⟨hi0, hiI⟩ := hfD
        have hEnc : (encExpr (.call (.local i) args)).toList = 'g' :: 'l' ::
            ((encNat i).toList ++ (encNat ↑args.length).toList ++
              (encExprs args).toList) := by
          show (("g" ++ "l" ++ encNat i ++ encNat ↑args.length ++
            encExprs args)).toList = _
          simp only [toList_append]; rfl
        rw [hEnc] at h
        have hq : charAt cs (p + 1) = some 'l' :=
          charAt_head cs (p + 1) 'l' _ (drop_succ h)
        have hd1 : cs.toList.drop (p + 1 + 1) =
            (encNat i).toList ++ ((encNat ↑args.length).toList ++
              ((encExprs args).toList ++ rest)) := by
          have e := drop_succ (drop_succ h)
          simp only [← List.append_assoc]
          exact e
        have hdn : decNat cs (p + 1 + 1) =
            .ok (i, (p + 1 + 1) + (toString i).toList.length + 1) :=
          decNat_encInt i hi0 hiI cs (p + 1 + 1) _ hd1
        have hdL : cs.toList.drop
            ((p + 1 + 1) + (toString i).toList.length + 1) =
            (toString ↑(args.map Item.expr).length).toList ++ ';' ::
            ((catEnc (encBase 2) (args.map Item.expr)).toList ++ rest) := by
          have e := drop_append_advance (l := cs.toList) (p := p + 1 + 1)
            (s := (encNat i).toList) hd1
          rw [encNat_toList, List.length_append,
            show ([';'] : List Char).length = 1 from rfl] at e
          rw [List.length_map, ← hcat]
          simp only [encNat_toList, List.append_assoc, List.cons_append,
            List.nil_append] at e
          exact e
        have hdlist : decList cs g 2 fuel
            ((p + 1 + 1) + (toString i).toList.length + 1) =
            .ok (.list (args.map Item.expr),
              ((p + 1 + 1) + (toString i).toList.length + 1) +
                (toString (args.map Item.expr).length).toList.length + 1 +
                (catEnc (encBase 2) (args.map Item.expr)).toList.length) :=
          decList_enc (encBase 2) cs g 2 fuel (exprsGas args + 1)
            (args.map Item.expr) _ rest hdL
            (by rw [List.length_map]; simp only [exprGas] at hG; omega)
            (by rw [List.length_map]; exact hlen)
            (by rw [List.length_map]
                exact ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩)
            (by rw [List.length_map]; exact toString_len_lt24 _ hlen)
            (fun g'' x hg''1 _ hm p'' rest'' hd'' => by
              obtain ⟨e', hem, hte⟩ := List.mem_map.mp hm
              subst hte
              have hd''' : cs.toList.drop p'' =
                  (encExpr e').toList ++ rest'' := hd''
              show dec cs g'' 2 (fuel - 1) p'' =
                .ok (Item.expr e', p'' + (encExpr e').toList.length)
              exact dec_two' cs g'' (fuel - 1) p''
                (p'' + (encExpr e').toList.length) (Item.expr e') (by omega)
                (ihargs e' hem cs (g'' - 1) (fuel - 1) p'' rest'' hd'''
                  (by have := exprGas_le_exprsGas hem; omega)
                  (by have := exprFuel_le_exprsFuel hem;
                      simp only [exprFuel] at hF; omega)
                  (dqsE_mem hdqs hem))
                (by simp only [exprFuel] at hF; omega))
        unfold decExpr; dsimp only
        rw [charAt_head cs p 'g' _ h, hq]
        show bind ((decNat cs (p + 1 + 1)).map
              (fun x => (RawFn.local x.1, x.2)))
            (fun fq => bind (decList cs g 2 fuel fq.2)
              (fun xq => Except.ok
                (Item.expr (.call fq.1 ((asList xq.1).map asExpr)), xq.2))) = _
        rw [show (decNat cs (p + 1 + 1)).map
              (fun x => (RawFn.local x.1, x.2)) =
            .ok (RawFn.local i,
              (p + 1 + 1) + (toString i).toList.length + 1) from by
          rw [hdn]; rfl]
        show bind (decList cs g 2 fuel
              ((p + 1 + 1) + (toString i).toList.length + 1))
            (fun xq => Except.ok
              (Item.expr (.call (RawFn.local i) ((asList xq.1).map asExpr)),
                xq.2)) = _
        rw [hdlist]
        show Except.ok (Item.expr (.call (RawFn.local i)
              ((asList (.list (args.map Item.expr))).map asExpr)), _) = _
        rw [show (asList (.list (args.map Item.expr))).map asExpr = args
          from map_asExpr_expr args]
        show Except.ok (Item.expr (.call (RawFn.local i) args), _) =
          Except.ok (Item.expr (.call (.local i) args), _)
        congr 1; congr 1
        have e := congrArg List.length hEnc
        simp only [List.length_cons, List.length_append] at e
        have eN : (encNat i).toList.length = (toString i).toList.length + 1 := by
          rw [encNat_toList, List.length_append,
            show ([';'] : List Char).length = 1 from rfl]
        have eL : (encNat ↑args.length).toList.length =
            (toString (↑args.length : Int)).toList.length + 1 := by
          rw [encNat_toList, List.length_append,
            show ([';'] : List Char).length = 1 from rfl]
        have em : (toString (args.map Item.expr).length).toList.length =
            (toString (↑args.length : Int)).toList.length := by
          rw [List.length_map]; rfl
        have hc := congrArg List.length hcat
        omega
      | «ext» r =>
        have hrlen := hfD
        have hEnc : (encExpr (.call (.ext r) args)).toList = 'g' :: 'x' ::
            ((encStr r).toList ++ (encNat ↑args.length).toList ++
              (encExprs args).toList) := by
          show (("g" ++ "x" ++ encStr r ++ encNat ↑args.length ++
            encExprs args)).toList = _
          simp only [toList_append]; rfl
        rw [hEnc] at h
        have hq : charAt cs (p + 1) = some 'x' :=
          charAt_head cs (p + 1) 'x' _ (drop_succ h)
        have hd1 : cs.toList.drop (p + 1 + 1) =
            (encStr r).toList ++ ((encNat ↑args.length).toList ++
              ((encExprs args).toList ++ rest)) := by
          have e := drop_succ (drop_succ h)
          simp only [← List.append_assoc]
          exact e
        have hds : decStr cs (p + 1 + 1) =
            .ok (r, (p + 1 + 1) + (toString r.length).toList.length + 1 +
              r.length) := by
          have hd1' : cs.toList.drop (p + 1 + 1) =
              (toString r.length).toList ++ ':' ::
              (r.toList ++ ((encNat ↑args.length).toList ++
                ((encExprs args).toList ++ rest))) := by
            rw [encStr_toList] at hd1
            simp only [List.append_assoc, List.cons_append,
              List.nil_append] at hd1
            exact hd1
          exact decStr_enc r cs (p + 1 + 1) _ hd1'
            (toString_len_lt24 _ hrlen) hrlen
        have hdL : cs.toList.drop
            ((p + 1 + 1) + (toString r.length).toList.length + 1 + r.length) =
            (toString ↑(args.map Item.expr).length).toList ++ ';' ::
            ((catEnc (encBase 2) (args.map Item.expr)).toList ++ rest) := by
          have e := drop_append_advance (l := cs.toList) (p := p + 1 + 1)
            (s := (encStr r).toList) hd1
          rw [encStr_toList, List.length_append, List.length_cons,
            show (r.toList.length : Nat) = r.length from rfl,
            show (p + 1 + 1) + ((toString r.length).toList.length +
                (r.length + 1)) =
              (p + 1 + 1) + (toString r.length).toList.length + 1 + r.length
              from by omega] at e
          rw [List.length_map, ← hcat]
          simp only [encNat_toList, List.append_assoc, List.cons_append,
            List.nil_append] at e
          exact e
        have hdlist : decList cs g 2 fuel
            ((p + 1 + 1) + (toString r.length).toList.length + 1 + r.length) =
            .ok (.list (args.map Item.expr),
              ((p + 1 + 1) + (toString r.length).toList.length + 1 + r.length) +
                (toString (args.map Item.expr).length).toList.length + 1 +
                (catEnc (encBase 2) (args.map Item.expr)).toList.length) :=
          decList_enc (encBase 2) cs g 2 fuel (exprsGas args + 1)
            (args.map Item.expr) _ rest hdL
            (by rw [List.length_map]; simp only [exprGas] at hG; omega)
            (by rw [List.length_map]; exact hlen)
            (by rw [List.length_map]
                exact ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩)
            (by rw [List.length_map]; exact toString_len_lt24 _ hlen)
            (fun g'' x hg''1 _ hm p'' rest'' hd'' => by
              obtain ⟨e', hem, hte⟩ := List.mem_map.mp hm
              subst hte
              have hd''' : cs.toList.drop p'' =
                  (encExpr e').toList ++ rest'' := hd''
              show dec cs g'' 2 (fuel - 1) p'' =
                .ok (Item.expr e', p'' + (encExpr e').toList.length)
              exact dec_two' cs g'' (fuel - 1) p''
                (p'' + (encExpr e').toList.length) (Item.expr e') (by omega)
                (ihargs e' hem cs (g'' - 1) (fuel - 1) p'' rest'' hd'''
                  (by have := exprGas_le_exprsGas hem; omega)
                  (by have := exprFuel_le_exprsFuel hem;
                      simp only [exprFuel] at hF; omega)
                  (dqsE_mem hdqs hem))
                (by simp only [exprFuel] at hF; omega))
        unfold decExpr; dsimp only
        rw [charAt_head cs p 'g' _ h, hq]
        show bind ((decStr cs (p + 1 + 1)).map
              (fun x => (RawFn.ext x.1, x.2)))
            (fun fq => bind (decList cs g 2 fuel fq.2)
              (fun xq => Except.ok
                (Item.expr (.call fq.1 ((asList xq.1).map asExpr)), xq.2))) = _
        rw [show (decStr cs (p + 1 + 1)).map
              (fun x => (RawFn.ext x.1, x.2)) =
            .ok (RawFn.ext r,
              (p + 1 + 1) + (toString r.length).toList.length + 1 +
                r.length) from by
          rw [hds]; rfl]
        show bind (decList cs g 2 fuel
              ((p + 1 + 1) + (toString r.length).toList.length + 1 + r.length))
            (fun xq => Except.ok
              (Item.expr (.call (RawFn.ext r) ((asList xq.1).map asExpr)),
                xq.2)) = _
        rw [hdlist]
        show Except.ok (Item.expr (.call (RawFn.ext r)
              ((asList (.list (args.map Item.expr))).map asExpr)), _) = _
        rw [show (asList (.list (args.map Item.expr))).map asExpr = args
          from map_asExpr_expr args]
        show Except.ok (Item.expr (.call (RawFn.ext r) args), _) =
          Except.ok (Item.expr (.call (.ext r) args), _)
        congr 1; congr 1
        have e := congrArg List.length hEnc
        simp only [List.length_cons, List.length_append] at e
        have eS : (encStr r).toList.length =
            (toString r.length).toList.length + 1 + r.length := by
          rw [encStr_toList, List.length_append, List.length_cons,
            show (r.toList.length : Nat) = r.length from rfl]; omega
        have eL : (encNat ↑args.length).toList.length =
            (toString (↑args.length : Int)).toList.length + 1 := by
          rw [encNat_toList, List.length_append,
            show ([';'] : List Char).length = 1 from rfl]
        have em : (toString (args.map Item.expr).length).toList.length =
            (toString (↑args.length : Int)).toList.length := by
          rw [List.length_map]; rfl
        have hc := congrArg List.length hcat
        omega
  · -- .raise r p t
    intro r p' t ihr cs g fuel p rest h hG hF hD
    obtain ⟨hrlen, hdp, hdt⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.raise r p' t)).toList = 'h' ::
          ((encStr r).toList ++ (encExpr p').toList ++ (encTy t).toList) := by
        show (("h" ++ encStr r ++ encExpr p' ++ encTy t)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [4, 2, 0] [.str r, .expr p', .ty t]).toList =
          (encStr r ++ encExpr p' ++ encTy t).toList := by
        show (encStr r ++ (encExpr p' ++ (encTy t ++ ""))).toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [4, 2, 0] [.str r, .expr p', .ty t]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel
        (max 1 (max (exprGas p' + 1) (tyGas t + 1)))
        [4, 2, 0] [.str r, .expr p', .ty t] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p'2 rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show dec cs g' 4 (fuel - 1) p'2 =
              Except.ok (.str r, p'2 + (encStr r).toList.length)
            exact decStr_elem cs g' (fuel - 1) r p'2 rest' hd' (by omega)
              (by simp only [exprFuel] at hF; omega) hrlen
          · show dec cs g' 2 (fuel - 1) p'2 =
              Except.ok (Item.expr p', p'2 + (encExpr p').toList.length)
            exact dec_two' cs g' (fuel - 1) p'2 _ (Item.expr p') (by omega)
              (ihr cs (g' - 1) (fuel - 1) p'2 rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdp)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 0 (fuel - 1) p'2 =
              Except.ok (.ty t, p'2 + (encTy t).toList.length)
            exact dec_zero' cs g' (fuel - 1) p'2 _ (.ty t) (by omega)
              (decTy_enc t cs (g' - 1) (fuel - 1) p'2 rest' hd'
                (by simp only [exprGas] at hG; omega)
                (by simp only [exprFuel] at hF; omega) hdt) (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p 'h' _ h]
      show bind (decSeq cs g fuel (p + 1) [4, 2, 0]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 17 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.raise r p' t),
            p + 1 + (encItems [4, 2, 0]
              [.str r, .expr p', .ty t]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .handle r b hh
    intro r b hh ihb ihh cs g fuel p rest h hG hF hD
    obtain ⟨hrlen, hdb, hdhh⟩ := hD
    cases g with
    | zero => simp only [exprGas] at hG; exact False.elim (by omega)
    | succ g =>
      have hEnc : (encExpr (.handle r b hh)).toList = 'j' ::
          ((encStr r).toList ++ (encExpr b).toList ++ (encExpr hh).toList) := by
        show (("j" ++ encStr r ++ encExpr b ++ encExpr hh)).toList = _
        simp only [toList_append]; rfl
      rw [hEnc] at h
      have hItems : (encItems [4, 2, 2] [.str r, .expr b, .expr hh]).toList =
          (encStr r ++ encExpr b ++ encExpr hh).toList := by
        show ((encStr r) ++ ((encExpr b) ++ ((encExpr hh) ++ ""))).toList = _
        simp only [toList_append,
          show ("" : String).toList = [] from rfl, List.append_nil,
          ← List.append_assoc]
      have hd : cs.toList.drop (p + 1) =
          (encItems [4, 2, 2] [.str r, .expr b, .expr hh]).toList ++ rest := by
        have e := drop_succ h
        rw [hItems]; exact e
      have hseq := decSeq_enc cs fuel
        (max 1 (max (exprGas b + 1) (exprGas hh + 1)))
        [4, 2, 2] [.str r, .expr b, .expr hh] g (p + 1) rest hd rfl
        (by simp only [exprGas] at hG; simp only [List.length_cons, List.length_nil]; omega)
        (fun g' kd xv hg' _ hm p' rest' hd' => by
          simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons,
            List.not_mem_nil, or_false, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · show dec cs g' 4 (fuel - 1) p' =
              Except.ok (.str r, p' + (encStr r).toList.length)
            exact decStr_elem cs g' (fuel - 1) r p' rest' hd' (by omega)
              (by simp only [exprFuel] at hF; omega) hrlen
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr b, p' + (encExpr b).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr b) (by omega)
              (ihb cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdb)
              (by simp only [exprFuel] at hF; omega)
          · show dec cs g' 2 (fuel - 1) p' =
              Except.ok (Item.expr hh, p' + (encExpr hh).toList.length)
            exact dec_two' cs g' (fuel - 1) p' _ (Item.expr hh) (by omega)
              (ihh cs (g' - 1) (fuel - 1) p' rest' hd' (by omega) (by simp only [exprFuel] at hF; omega) hdhh)
              (by simp only [exprFuel] at hF; omega))
      unfold decExpr; dsimp only
      rw [charAt_head cs p 'j' _ h]
      show bind (decSeq cs g fuel (p + 1) [4, 2, 2]) (fun __discr =>
          Except.ok (Item.expr (exprBuild 18 __discr.1), __discr.2)) = _
      rw [hseq]
      show Except.ok (Item.expr (.handle r b hh),
            p + 1 + (encItems [4, 2, 2]
              [.str r, .expr b, .expr hh]).toList.length) = _
      rw [hItems]
      simp only [toList_append, List.length_append, List.length_nil]
      have e := congrArg List.length hEnc
      simp only [List.length_cons, List.length_append, List.length_nil] at e
      rw [e]; congr 1; congr 1; omega
  · -- .unknown k — dqE is False
    intro k cs g fuel p rest h hG hF hD
    exact (hD).elim
  · -- motive_2 nil
    intro e hm; cases hm
  · -- motive_2 cons
    intro e es' ihe ihes e' hm
    cases hm with
    | head => exact ihe
    | tail _ hm' => exact ihes e' hm'

/-! ## Fuel bounded by encoded length

Every decoder-fuel measure (`tyFuel`, `valFuel`, `exprFuel` and their list
versions) is bounded by the encoding's own byte length: each encoding level
contributes at least its tag byte, so the `max … + 1` recursion never exceeds
the produced string.  These are the adequacy bridges from a wire object's
own length (the carrier's `fuel = b.length` convention) to every embedded
element's decode/elaborate depth. -/

/-- `encNat` always emits at least the `';'` terminator. -/
theorem encNat_len_pos (n : Int) : 1 ≤ (encNat n).toList.length := by
  rw [encNat_toList, List.length_append, List.length_cons, List.length_nil]
  omega

/-- `encStr` carries its payload's full length. -/
theorem encStr_payload_le (x : String) :
    x.toList.length ≤ (encStr x).toList.length := by
  rw [encStr_toList, List.length_append, List.length_cons]
  omega

mutual
/-- `decTy`-depth is bounded by `encTy`'s length. -/
theorem tyFuel_le_encLen : ∀ (t : CoreTy), tyFuel t ≤ (encTy t).toList.length
  | .i64 | .bool | .str | .bytes => Nat.zero_le _
  | .list t => by
      have ih := tyFuel_le_encLen t
      show tyFuel t + 1 ≤ (("L" ++ encTy t)).toList.length
      simp only [toList_append, List.length_append,
        show ("L".toList.length : Nat) = 1 from rfl]; omega
  | .pair a b => by
      have ia := tyFuel_le_encLen a; have ib := tyFuel_le_encLen b
      show max (tyFuel a) (tyFuel b) + 1 ≤
        (("P" ++ encTy a ++ encTy b)).toList.length
      simp only [toList_append, List.length_append,
        show ("P".toList.length : Nat) = 1 from rfl]; omega
  | .sum ts => by
      have ih := tysFuel_le_encTysLen ts
      show tysFuel ts + 1 ≤
        (("S" ++ encNat ↑ts.length ++ encTys ts)).toList.length
      simp only [toList_append, List.length_append,
        show ("S".toList.length : Nat) = 1 from rfl]; omega
  | .record fs => by
      have ih := fieldTysFuel_le_encFieldTysLen fs
      have hb := encNat_len_pos (↑fs.length)
      show fieldTysFuel fs + 2 ≤
        (("R" ++ encNat ↑fs.length ++ encFieldTys fs)).toList.length
      simp only [toList_append, List.length_append,
        show ("R".toList.length : Nat) = 1 from rfl]; omega
theorem tysFuel_le_encTysLen : ∀ (ts : List CoreTy),
    tysFuel ts ≤ (encTys ts).toList.length
  | [] => Nat.zero_le _
  | t :: ts => by
      have it := tyFuel_le_encLen t; have is := tysFuel_le_encTysLen ts
      show max (tyFuel t) (tysFuel ts) ≤ ((encTy t ++ encTys ts)).toList.length
      simp only [toList_append, List.length_append]; omega
theorem fieldTysFuel_le_encFieldTysLen : ∀ (fs : List (String × CoreTy)),
    fieldTysFuel fs ≤ (encFieldTys fs).toList.length
  | [] => Nat.zero_le _
  | (k, t) :: fs => by
      have it := tyFuel_le_encLen t; have is := fieldTysFuel_le_encFieldTysLen fs
      show max (tyFuel t) (fieldTysFuel fs) ≤
        ((encStr k ++ encTy t ++ encFieldTys fs)).toList.length
      simp only [toList_append, List.length_append]; omega
end

mutual
/-- `decVal`-depth is bounded by `encVal`'s length. -/
theorem valFuel_le_encLen : ∀ (v : Val), valFuel v ≤ (encVal v).toList.length
  | .i _ | .b _ | .s _ => Nat.zero_le _
  | .y bs => by
      show 1 ≤
        (("Y" ++ encNat ↑bs.length ++ String.join (bs.map encNat))).toList.length
      simp only [toList_append, List.length_append,
        show ("Y".toList.length : Nat) = 1 from rfl]; omega
  | .l xs => by
      have ih := valsFuel_le_encValsLen xs
      show valsFuel xs + 1 ≤
        (("L" ++ encNat ↑xs.length ++ encVals xs)).toList.length
      simp only [toList_append, List.length_append,
        show ("L".toList.length : Nat) = 1 from rfl]; omega
  | .r xs => by
      have ih := valsFuel_le_encValsLen xs
      show valsFuel xs + 1 ≤
        (("R" ++ encNat ↑xs.length ++ encVals xs)).toList.length
      simp only [toList_append, List.length_append,
        show ("R".toList.length : Nat) = 1 from rfl]; omega
  | .p a b => by
      have ia := valFuel_le_encLen a; have ib := valFuel_le_encLen b
      show max (valFuel a) (valFuel b) + 1 ≤
        (("P" ++ encVal a ++ encVal b)).toList.length
      simp only [toList_append, List.length_append,
        show ("P".toList.length : Nat) = 1 from rfl]; omega
  | .j i x => by
      have ih := valFuel_le_encLen x
      show valFuel x + 1 ≤ (("J" ++ encNat i ++ encVal x)).toList.length
      simp only [toList_append, List.length_append,
        show ("J".toList.length : Nat) = 1 from rfl]; omega
theorem valsFuel_le_encValsLen : ∀ (xs : List Val),
    valsFuel xs ≤ (encVals xs).toList.length
  | [] => Nat.zero_le _
  | x :: xs => by
      have ix := valFuel_le_encLen x; have is := valsFuel_le_encValsLen xs
      show max (valFuel x) (valsFuel xs) ≤ ((encVal x ++ encVals xs)).toList.length
      simp only [toList_append, List.length_append]; omega
end

mutual
/-- `decExpr`-depth is bounded by `encExpr`'s length. -/
theorem exprFuel_le_encLen : ∀ (e : RawExpr),
    exprFuel e ≤ (encExpr e).toList.length
  | .lit x t => by
      have ix := valFuel_le_encLen x; have it := tyFuel_le_encLen t
      show max (valFuel x) (tyFuel t) + 1 ≤
        (("0" ++ encVal x ++ encTy t)).toList.length
      simp only [toList_append, List.length_append,
        show ("0".toList.length : Nat) = 1 from rfl]; omega
  | .var _ => Nat.zero_le _
  | .letE a b | .pair a b | .cons a b => by
      first
        | (have ia := exprFuel_le_encLen a; have ib := exprFuel_le_encLen b
           show max (exprFuel a) (exprFuel b) + 1 ≤
             (("2" ++ encExpr a ++ encExpr b)).toList.length
           simp only [toList_append, List.length_append,
             show ("2".toList.length : Nat) = 1 from rfl]; omega)
        | (have ia := exprFuel_le_encLen a; have ib := exprFuel_le_encLen b
           show max (exprFuel a) (exprFuel b) + 1 ≤
             (("4" ++ encExpr a ++ encExpr b)).toList.length
           simp only [toList_append, List.length_append,
             show ("4".toList.length : Nat) = 1 from rfl]; omega)
        | (have ia := exprFuel_le_encLen a; have ib := exprFuel_le_encLen b
           show max (exprFuel a) (exprFuel b) + 1 ≤
             (("c" ++ encExpr a ++ encExpr b)).toList.length
           simp only [toList_append, List.length_append,
             show ("c".toList.length : Nat) = 1 from rfl]; omega)
  | .ifE c th el => by
      have i1 := exprFuel_le_encLen c; have i2 := exprFuel_le_encLen th
      have i3 := exprFuel_le_encLen el
      show max (exprFuel c) (max (exprFuel th) (exprFuel el)) + 1 ≤
        (("3" ++ encExpr c ++ encExpr th ++ encExpr el)).toList.length
      simp only [toList_append, List.length_append,
        show ("3".toList.length : Nat) = 1 from rfl]; omega
  | .fst a | .snd a => by
      first
        | (have ia := exprFuel_le_encLen a
           show exprFuel a + 1 ≤ (("5" ++ encExpr a)).toList.length
           simp only [toList_append, List.length_append,
             show ("5".toList.length : Nat) = 1 from rfl]; omega)
        | (have ia := exprFuel_le_encLen a
           show exprFuel a + 1 ≤ (("6" ++ encExpr a)).toList.length
           simp only [toList_append, List.length_append,
             show ("6".toList.length : Nat) = 1 from rfl]; omega)
  | .inj i ts a => by
      have is := tysFuel_le_encTysLen ts; have ia := exprFuel_le_encLen a
      show max (tysFuel ts + 1) (exprFuel a + 1) ≤
        (("7" ++ encNat i ++ encNat ↑ts.length ++ encTys ts ++
          encExpr a)).toList.length
      simp only [toList_append, List.length_append,
        show ("7".toList.length : Nat) = 1 from rfl]; omega
  | .matchE s bs => by
      have is := exprFuel_le_encLen s; have ib := exprsFuel_le_encExprsLen bs
      show max (exprFuel s + 1) (exprsFuel bs + 1) ≤
        (("8" ++ encExpr s ++ encNat ↑bs.length ++ encExprs bs)).toList.length
      simp only [toList_append, List.length_append,
        show ("8".toList.length : Nat) = 1 from rfl]; omega
  | .recordE keys fs => by
      have ib := exprsFuel_le_encExprsLen fs
      show max 1 (exprsFuel fs + 1) ≤
        (("9" ++ encNat ↑keys.length ++
          String.join (keys.map encStr) ++ encNat ↑fs.length ++
          encExprs fs)).toList.length
      simp only [toList_append, List.length_append,
        show ("9".toList.length : Nat) = 1 from rfl]; omega
  | .field r i => by
      have ir := exprFuel_le_encLen r
      show exprFuel r + 1 ≤ (("a" ++ encExpr r ++ encNat i)).toList.length
      simp only [toList_append, List.length_append,
        show ("a".toList.length : Nat) = 1 from rfl]; omega
  | .nil t => by
      have it := tyFuel_le_encLen t
      show tyFuel t + 1 ≤ (("b" ++ encTy t)).toList.length
      simp only [toList_append, List.length_append,
        show ("b".toList.length : Nat) = 1 from rfl]; omega
  | .fold l init body => by
      have i1 := exprFuel_le_encLen l; have i2 := exprFuel_le_encLen init
      have i3 := exprFuel_le_encLen body
      show max (exprFuel l) (max (exprFuel init) (exprFuel body)) + 1 ≤
        (("d" ++ encExpr l ++ encExpr init ++ encExpr body)).toList.length
      simp only [toList_append, List.length_append,
        show ("d".toList.length : Nat) = 1 from rfl]; omega
  | .fix i l s st => by
      have i1 := exprFuel_le_encLen i; have i2 := exprFuel_le_encLen l
      have i3 := exprFuel_le_encLen s; have i4 := exprFuel_le_encLen st
      show max (exprFuel i) (max (exprFuel l) (max (exprFuel s) (exprFuel st)))
          + 1 ≤
        (("e" ++ encExpr i ++ encExpr l ++ encExpr s ++ encExpr st)).toList.length
      simp only [toList_append, List.length_append,
        show ("e".toList.length : Nat) = 1 from rfl]; omega
  | .prim op args => by
      have ia := exprsFuel_le_encExprsLen args
      show max 1 (exprsFuel args + 1) ≤
        (("f" ++ encStr op ++ encNat ↑args.length ++ encExprs args)).toList.length
      simp only [toList_append, List.length_append,
        show ("f".toList.length : Nat) = 1 from rfl]; omega
  | .call (.local i) args => by
      have ia := exprsFuel_le_encExprsLen args
      show exprsFuel args + 1 ≤
        (("g" ++ "l" ++ encNat i ++ encNat ↑args.length ++
          encExprs args)).toList.length
      simp only [toList_append, List.length_append,
        show ("g".toList.length : Nat) = 1 from rfl]; omega
  | .call (.ext r) args => by
      have ia := exprsFuel_le_encExprsLen args
      show exprsFuel args + 1 ≤
        (("g" ++ "x" ++ encStr r ++ encNat ↑args.length ++
          encExprs args)).toList.length
      simp only [toList_append, List.length_append,
        show ("g".toList.length : Nat) = 1 from rfl]; omega
  | .raise r p t => by
      have ip := exprFuel_le_encLen p; have it := tyFuel_le_encLen t
      show max 1 (max (exprFuel p + 1) (tyFuel t + 1)) ≤
        (("h" ++ encStr r ++ encExpr p ++ encTy t)).toList.length
      simp only [toList_append, List.length_append,
        show ("h".toList.length : Nat) = 1 from rfl]; omega
  | .handle r b h => by
      have ib := exprFuel_le_encLen b; have ih := exprFuel_le_encLen h
      show max 1 (max (exprFuel b + 1) (exprFuel h + 1)) ≤
        (("j" ++ encStr r ++ encExpr b ++ encExpr h)).toList.length
      simp only [toList_append, List.length_append,
        show ("j".toList.length : Nat) = 1 from rfl]; omega
  | .unknown _ => Nat.zero_le _
theorem exprsFuel_le_encExprsLen : ∀ (es : List RawExpr),
    exprsFuel es ≤ (encExprs es).toList.length
  | [] => Nat.zero_le _
  | e :: es => by
      have ie := exprFuel_le_encLen e; have is := exprsFuel_le_encExprsLen es
      show max (exprFuel e) (exprsFuel es) ≤
        ((encExpr e ++ encExprs es)).toList.length
      simp only [toList_append, List.length_append]; omega
end

/-- One member's encoding is bounded by the `catEnc` total. -/
theorem catEnc_len_le (f : α → String) : ∀ (xs : List α) (x : α), x ∈ xs →
    (f x).toList.length ≤ (catEnc f xs).toList.length
  | [], _, h => absurd h (List.not_mem_nil _)
  | x :: xs', y, h => by
      rw [catEnc_cons, List.length_append]
      cases h with
      | head => omega
      | tail _ hm => have := catEnc_len_le f xs' y hm; omega

/-- A kind-2 slot's expression encoding is bounded by the `encItems` total. -/
theorem encExpr_le_encItems : ∀ (ks : List Nat) (xs : List Item) (i : Nat)
    (e : RawExpr), ks.get? i = some 2 → xs.get? i = some (.expr e) →
    (encExpr e).toList.length ≤ (encItems ks xs).toList.length
  | [], _, _, _, hk, _ => by simp at hk
  | k :: ks', xs, 0, e, hk, hx => by
      simp at hk; subst hk
      cases xs with
      | nil => simp at hx
      | cons x tail =>
        have hxe : x = .expr e := Option.some.inj hx
        show (encExpr e).toList.length ≤
          ((encItem 2 x ++ encItems ks' tail)).toList.length
        rw [hxe]
        show _ ≤ ((encExpr e ++ encItems ks' tail)).toList.length
        simp only [toList_append, List.length_append]; omega
  | k :: ks', xs, i + 1, e, hk, hx => by
      cases xs with
      | nil => simp at hx
      | cons x tail =>
        have ih := encExpr_le_encItems ks' tail i e hk hx
        show _ ≤ ((encItem k x ++ encItems ks' tail)).toList.length
        simp only [toList_append, List.length_append]; omega

/-- A kind-12 slot member's expression encoding is bounded by the `encItems`
    total. -/
theorem encExpr_le_encItems_list : ∀ (ks : List Nat) (xs : List Item) (i : Nat)
    (es : List RawExpr) (e : RawExpr), ks.get? i = some 12 →
    xs.get? i = some (.list (es.map Item.expr)) → e ∈ es →
    (encExpr e).toList.length ≤ (encItems ks xs).toList.length
  | [], _, _, _, _, hk, _, _ => by simp at hk
  | k :: ks', xs, 0, es, e, hk, hx, he => by
      simp at hk; subst hk
      cases xs with
      | nil => simp at hx
      | cons x tail =>
        have hxe : x = .list (es.map Item.expr) := Option.some.inj hx
        have hmem := catEnc_len_le encExpr es e he
        show _ ≤ ((encItem 12 x ++ encItems ks' tail)).toList.length
        rw [hxe, toList_append, encItem_12_exprs]
        simp only [toList_append, List.length_append, encExprs_catEnc]; omega
  | k :: ks', xs, i + 1, es, e, hk, hx, he => by
      cases xs with
      | nil => simp at hx
      | cons x tail =>
        have ih := encExpr_le_encItems_list ks' tail i es e hk hx he
        show _ ≤ ((encItem k x ++ encItems ks' tail)).toList.length
        simp only [toList_append, List.length_append]; omega

/-- The item block is bounded by the tagged encoding. -/
theorem encItems_le_encTagged (what : Int) (g : Tagged) :
    (encItems ((kindsOf what g.tag).getD []) g.xs).toList.length ≤
    (encTagged what g).toList.length := by
  show _ ≤ ((encNat g.tag ++
    encItems ((kindsOf what g.tag).getD []) g.xs)).toList.length
  simp only [toList_append, List.length_append]; omega

/-! ## Gas bounded by encoded length

The gas measures charge a constant per nesting level plus the element
count of every decoded list (`tyGas .sum = tysGas + len + 4` and its
siblings).  Since each list element contributes at least one encoded
byte, `wXsGas xs + xs.length ≤ 4 * (encXs xs).toList.length + 5`, while
the scalar measures stay within `4 * (encX x).toList.length + 4`.
`exprsGas` needs the `dqsE` well-formedness premise because `.unknown`
encodes to `""` and contributes no byte.  These bounds discharge the
`gasFor` budget when decoding canonical wire objects at fuel = their own
length. -/

theorem encStr_len_pos (x : String) : 1 ≤ (encStr x).toList.length := by
  rw [encStr_toList, List.length_append, List.length_cons]
  omega

theorem encTy_len_pos : ∀ t : CoreTy, 1 ≤ (encTy t).toList.length
  | .i64 => by decide
  | .bool => by decide
  | .str => by decide
  | .bytes => by decide
  | .list t => by
      show 1 ≤ (("L" ++ encTy t)).toList.length
      simp only [toList_append, List.length_append,
        show ("L".toList.length : Nat) = 1 from rfl]; omega
  | .pair a b => by
      show 1 ≤ (("P" ++ encTy a ++ encTy b)).toList.length
      simp only [toList_append, List.length_append,
        show ("P".toList.length : Nat) = 1 from rfl]; omega
  | .sum ts => by
      show 1 ≤ (("S" ++ encNat ↑ts.length ++ encTys ts)).toList.length
      simp only [toList_append, List.length_append,
        show ("S".toList.length : Nat) = 1 from rfl]; omega
  | .record fs => by
      show 1 ≤ (("R" ++ encNat ↑fs.length ++ encFieldTys fs)).toList.length
      simp only [toList_append, List.length_append,
        show ("R".toList.length : Nat) = 1 from rfl]; omega

theorem encVal_len_pos : ∀ v : Val, 1 ≤ (encVal v).toList.length
  | .i n => by
      show 1 ≤ (("I" ++ encNat n)).toList.length
      simp only [toList_append, List.length_append,
        show ("I".toList.length : Nat) = 1 from rfl]; omega
  | .b n => by
      show 1 ≤ (("B" ++ encNat n)).toList.length
      simp only [toList_append, List.length_append,
        show ("B".toList.length : Nat) = 1 from rfl]; omega
  | .s s => by
      show 1 ≤ (("T" ++ encStr s)).toList.length
      simp only [toList_append, List.length_append,
        show ("T".toList.length : Nat) = 1 from rfl]; omega
  | .y bs => by
      show 1 ≤ (("Y" ++ encNat ↑bs.length ++
        String.join (bs.map encNat))).toList.length
      simp only [toList_append, List.length_append,
        show ("Y".toList.length : Nat) = 1 from rfl]; omega
  | .l xs => by
      show 1 ≤ (("L" ++ encNat ↑xs.length ++ encVals xs)).toList.length
      simp only [toList_append, List.length_append,
        show ("L".toList.length : Nat) = 1 from rfl]; omega
  | .p a b => by
      show 1 ≤ (("P" ++ encVal a ++ encVal b)).toList.length
      simp only [toList_append, List.length_append,
        show ("P".toList.length : Nat) = 1 from rfl]; omega
  | .j i x => by
      show 1 ≤ (("J" ++ encNat i ++ encVal x)).toList.length
      simp only [toList_append, List.length_append,
        show ("J".toList.length : Nat) = 1 from rfl]; omega
  | .r fs => by
      show 1 ≤ (("R" ++ encNat ↑fs.length ++ encVals fs)).toList.length
      simp only [toList_append, List.length_append,
        show ("R".toList.length : Nat) = 1 from rfl]; omega

/-- A well-formed expression encodes to at least its tag byte. -/
theorem encExpr_pos_of_dq : ∀ e : RawExpr, dqE e →
    1 ≤ (encExpr e).toList.length
  | .lit x t, _ => by
      show 1 ≤ (("0" ++ encVal x ++ encTy t)).toList.length
      simp only [toList_append, List.length_append,
        show ("0".toList.length : Nat) = 1 from rfl]; omega
  | .var i, _ => by
      show 1 ≤ (("1" ++ encNat i)).toList.length
      simp only [toList_append, List.length_append,
        show ("1".toList.length : Nat) = 1 from rfl]; omega
  | .letE a b, _ => by
      show 1 ≤ (("2" ++ encExpr a ++ encExpr b)).toList.length
      simp only [toList_append, List.length_append,
        show ("2".toList.length : Nat) = 1 from rfl]; omega
  | .ifE c th el, _ => by
      show 1 ≤ (("3" ++ encExpr c ++ encExpr th ++ encExpr el)).toList.length
      simp only [toList_append, List.length_append,
        show ("3".toList.length : Nat) = 1 from rfl]; omega
  | .pair a b, _ => by
      show 1 ≤ (("4" ++ encExpr a ++ encExpr b)).toList.length
      simp only [toList_append, List.length_append,
        show ("4".toList.length : Nat) = 1 from rfl]; omega
  | .fst a, _ => by
      show 1 ≤ (("5" ++ encExpr a)).toList.length
      simp only [toList_append, List.length_append,
        show ("5".toList.length : Nat) = 1 from rfl]; omega
  | .snd a, _ => by
      show 1 ≤ (("6" ++ encExpr a)).toList.length
      simp only [toList_append, List.length_append,
        show ("6".toList.length : Nat) = 1 from rfl]; omega
  | .inj i ts a, _ => by
      show 1 ≤ (("7" ++ encNat i ++ encNat ↑ts.length ++ encTys ts ++
        encExpr a)).toList.length
      simp only [toList_append, List.length_append,
        show ("7".toList.length : Nat) = 1 from rfl]; omega
  | .matchE s bs, _ => by
      show 1 ≤ (("8" ++ encExpr s ++ encNat ↑bs.length ++
        encExprs bs)).toList.length
      simp only [toList_append, List.length_append,
        show ("8".toList.length : Nat) = 1 from rfl]; omega
  | .recordE keys fs, _ => by
      show 1 ≤ (("9" ++ encNat ↑keys.length ++
        String.join (keys.map encStr) ++ encNat ↑fs.length ++
        encExprs fs)).toList.length
      simp only [toList_append, List.length_append,
        show ("9".toList.length : Nat) = 1 from rfl]; omega
  | .field r i, _ => by
      show 1 ≤ (("a" ++ encExpr r ++ encNat i)).toList.length
      simp only [toList_append, List.length_append,
        show ("a".toList.length : Nat) = 1 from rfl]; omega
  | .nil t, _ => by
      show 1 ≤ (("b" ++ encTy t)).toList.length
      simp only [toList_append, List.length_append,
        show ("b".toList.length : Nat) = 1 from rfl]; omega
  | .cons a b, _ => by
      show 1 ≤ (("c" ++ encExpr a ++ encExpr b)).toList.length
      simp only [toList_append, List.length_append,
        show ("c".toList.length : Nat) = 1 from rfl]; omega
  | .fold l i b, _ => by
      show 1 ≤ (("d" ++ encExpr l ++ encExpr i ++ encExpr b)).toList.length
      simp only [toList_append, List.length_append,
        show ("d".toList.length : Nat) = 1 from rfl]; omega
  | .fix i l s st, _ => by
      show 1 ≤ (("e" ++ encExpr i ++ encExpr l ++ encExpr s ++
        encExpr st)).toList.length
      simp only [toList_append, List.length_append,
        show ("e".toList.length : Nat) = 1 from rfl]; omega
  | .prim op args, _ => by
      show 1 ≤ (("f" ++ encStr op ++ encNat ↑args.length ++
        encExprs args)).toList.length
      simp only [toList_append, List.length_append,
        show ("f".toList.length : Nat) = 1 from rfl]; omega
  | .call (.local i) args, _ => by
      show 1 ≤ (("g" ++ "l" ++ encNat i ++ encNat ↑args.length ++
        encExprs args)).toList.length
      simp only [toList_append, List.length_append,
        show ("g".toList.length : Nat) = 1 from rfl]; omega
  | .call (.ext r) args, _ => by
      show 1 ≤ (("g" ++ "x" ++ encStr r ++ encNat ↑args.length ++
        encExprs args)).toList.length
      simp only [toList_append, List.length_append,
        show ("g".toList.length : Nat) = 1 from rfl]; omega
  | .raise r p t, _ => by
      show 1 ≤ (("h" ++ encStr r ++ encExpr p ++ encTy t)).toList.length
      simp only [toList_append, List.length_append,
        show ("h".toList.length : Nat) = 1 from rfl]; omega
  | .handle r b h, _ => by
      show 1 ≤ (("j" ++ encStr r ++ encExpr b ++ encExpr h)).toList.length
      simp only [toList_append, List.length_append,
        show ("j".toList.length : Nat) = 1 from rfl]; omega
  | .unknown _, hd => absurd hd not_false

/-- Element-count bound: a list is no longer than its concatenated
    encoding when every element emits at least one byte. -/
theorem list_length_le_catEnc (f : α → String) : ∀ (xs : List α),
    (∀ x ∈ xs, 1 ≤ (f x).toList.length) →
    xs.length ≤ (catEnc f xs).toList.length
  | [], _ => Nat.zero_le _
  | x :: xs', h => by
      have hx := h x (List.Mem.head _)
      have hxs : ∀ y ∈ xs', 1 ≤ (f y).toList.length :=
        fun y hy => h y (List.Mem.tail _ hy)
      have ih := list_length_le_catEnc f xs' hxs
      rw [catEnc_cons]
      show (xs'.length + 1) ≤ ((f x).toList ++ (catEnc f xs').toList).length
      simp only [List.length_append]; omega

theorem tys_len_le_encTys (ts : List CoreTy) :
    ts.length ≤ (encTys ts).toList.length := by
  rw [encTys_catEnc]
  exact list_length_le_catEnc encTy ts (fun t _ => encTy_len_pos t)

theorem fieldTys_len_le (fs : List (String × CoreTy)) :
    fs.length ≤ (encFieldTys fs).toList.length := by
  rw [encFieldTys_catEnc]
  apply list_length_le_catEnc
  intro ft _
  show 1 ≤ ((encStr ft.1 ++ encTy ft.2)).toList.length
  simp only [toList_append, List.length_append]
  have := encStr_len_pos ft.1
  omega

theorem vals_len_le_encVals (xs : List Val) :
    xs.length ≤ (encVals xs).toList.length := by
  rw [encVals_catEnc]
  exact list_length_le_catEnc encVal xs (fun v _ => encVal_len_pos v)

theorem exprs_len_le_encExprs (es : List RawExpr) (hd : dqsE es) :
    es.length ≤ (encExprs es).toList.length := by
  rw [encExprs_catEnc]
  exact list_length_le_catEnc encExpr es
    (fun e he => encExpr_pos_of_dq e (dqsE_mem hd he))

mutual
/-- `decTy`-gas is bounded by `encTy`'s length (constant 4 slack). -/
theorem tyGas_le_encLen : ∀ (t : CoreTy),
    tyGas t ≤ 4 * (encTy t).toList.length + 4
  | .i64 | .bool | .str | .bytes => by decide
  | .list t => by
      have ih := tyGas_le_encLen t
      show tyGas t + 2 ≤ 4 * (("L" ++ encTy t)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("L".toList.length : Nat) = 1 from rfl]; omega
  | .pair a b => by
      have ia := tyGas_le_encLen a; have ib := tyGas_le_encLen b
      show max (tyGas a) (tyGas b) + 2 ≤
        4 * (("P" ++ encTy a ++ encTy b)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("P".toList.length : Nat) = 1 from rfl]; omega
  | .sum ts => by
      have ih := tysGas_le_encTysLen ts
      have hn := encNat_len_pos (↑ts.length)
      show tysGas ts + ts.length + 4 ≤
        4 * (("S" ++ encNat ↑ts.length ++ encTys ts)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("S".toList.length : Nat) = 1 from rfl]; omega
  | .record fs => by
      have ih := fieldTysGas_le_encFieldTysLen fs
      have hn := encNat_len_pos (↑fs.length)
      show fieldTysGas fs + fs.length + 4 ≤
        4 * (("R" ++ encNat ↑fs.length ++ encFieldTys fs)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("R".toList.length : Nat) = 1 from rfl]; omega
/-- `decList`-gas over a type list, element count charged to the bytes. -/
theorem tysGas_le_encTysLen : ∀ (ts : List CoreTy),
    tysGas ts + ts.length ≤ 4 * (encTys ts).toList.length + 5
  | [] => Nat.zero_le _
  | t :: ts => by
      have it := tyGas_le_encLen t; have is := tysGas_le_encTysLen ts
      have il := tys_len_le_encTys ts; have ip := encTy_len_pos t
      show max (tyGas t) (tysGas ts) + (ts.length + 1) ≤
        4 * ((encTy t ++ encTys ts)).toList.length + 5
      simp only [toList_append, List.length_append]; omega
/-- `decList`-gas over record fields. -/
theorem fieldTysGas_le_encFieldTysLen : ∀ (fs : List (String × CoreTy)),
    fieldTysGas fs + fs.length ≤ 4 * (encFieldTys fs).toList.length + 5
  | [] => Nat.zero_le _
  | (k, t) :: fs => by
      have it := tyGas_le_encLen t; have is := fieldTysGas_le_encFieldTysLen fs
      have il := fieldTys_len_le fs
      have ip : 1 ≤ (encStr k).toList.length + (encTy t).toList.length := by
        have := encStr_len_pos k; omega
      show max (tyGas t) (fieldTysGas fs) + (fs.length + 1) ≤
        4 * ((encStr k ++ encTy t ++ encFieldTys fs)).toList.length + 5
      simp only [toList_append, List.length_append]; omega
end

mutual
/-- `decVal`-gas is bounded by `encVal`'s length. -/
theorem valGas_le_encLen : ∀ (v : Val),
    valGas v ≤ 4 * (encVal v).toList.length + 4
  | .i n => by
      show 1 ≤ 4 * (("I" ++ encNat n)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("I".toList.length : Nat) = 1 from rfl]; omega
  | .b n => by
      show 1 ≤ 4 * (("B" ++ encNat n)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("B".toList.length : Nat) = 1 from rfl]; omega
  | .s s => by
      show 1 ≤ 4 * (("T" ++ encStr s)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("T".toList.length : Nat) = 1 from rfl]; omega
  | .y bs => by
      have hn := encNat_len_pos (↑bs.length)
      have hj : bs.length ≤ (String.join (bs.map encNat)).toList.length := by
        rw [encNat_catEnc]
        exact list_length_le_catEnc encNat bs (fun x _ => encNat_len_pos x)
      show bs.length + 4 ≤
        4 * (("Y" ++ encNat ↑bs.length ++
          String.join (bs.map encNat))).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("Y".toList.length : Nat) = 1 from rfl]; omega
  | .l xs => by
      have ih := valsGas_le_encValsLen xs
      have hn := encNat_len_pos (↑xs.length)
      show valsGas xs + xs.length + 4 ≤
        4 * (("L" ++ encNat ↑xs.length ++ encVals xs)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("L".toList.length : Nat) = 1 from rfl]; omega
  | .r xs => by
      have ih := valsGas_le_encValsLen xs
      have hn := encNat_len_pos (↑xs.length)
      show valsGas xs + xs.length + 4 ≤
        4 * (("R" ++ encNat ↑xs.length ++ encVals xs)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("R".toList.length : Nat) = 1 from rfl]; omega
  | .p a b => by
      have ia := valGas_le_encLen a; have ib := valGas_le_encLen b
      show max (valGas a) (valGas b) + 2 ≤
        4 * (("P" ++ encVal a ++ encVal b)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("P".toList.length : Nat) = 1 from rfl]; omega
  | .j i x => by
      have ih := valGas_le_encLen x
      have hn := encNat_len_pos i
      show valGas x + 2 ≤ 4 * (("J" ++ encNat i ++ encVal x)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("J".toList.length : Nat) = 1 from rfl]; omega
/-- `decList`-gas over a value list. -/
theorem valsGas_le_encValsLen : ∀ (xs : List Val),
    valsGas xs + xs.length ≤ 4 * (encVals xs).toList.length + 5
  | [] => Nat.zero_le _
  | x :: xs => by
      have ix := valGas_le_encLen x; have is := valsGas_le_encValsLen xs
      have il := vals_len_le_encVals xs; have ip := encVal_len_pos x
      show max (valGas x) (valsGas xs) + (xs.length + 1) ≤
        4 * ((encVal x ++ encVals xs)).toList.length + 5
      simp only [toList_append, List.length_append]; omega
end

mutual
/-- `decExpr`-gas is bounded by `encExpr`'s length. -/
theorem exprGas_le_encLen : ∀ (e : RawExpr) (_ : dqE e),
    exprGas e ≤ 4 * (encExpr e).toList.length + 4
  | .lit x t, hd => by
      obtain ⟨_, _⟩ := hd
      have ix := valGas_le_encLen x; have it := tyGas_le_encLen t
      have ip := encVal_len_pos x; have ip' := encTy_len_pos t
      show max (valGas x) (tyGas t) + 5 ≤
        4 * (("0" ++ encVal x ++ encTy t)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("0".toList.length : Nat) = 1 from rfl]; omega
  | .var i, _ => by
      show 3 ≤ 4 * (("1" ++ encNat i)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("1".toList.length : Nat) = 1 from rfl]; omega
  | .letE a b, hd | .pair a b, hd | .cons a b, hd => by
      obtain ⟨ha, hb⟩ := hd
      first
        | (have ia := exprGas_le_encLen a ha; have ib := exprGas_le_encLen b hb
           have ipa := encExpr_pos_of_dq a ha; have ipb := encExpr_pos_of_dq b hb
           show max (exprGas a) (exprGas b) + 5 ≤
             4 * (("2" ++ encExpr a ++ encExpr b)).toList.length + 4
           simp only [toList_append, List.length_append,
             show ("2".toList.length : Nat) = 1 from rfl]; omega)
        | (have ia := exprGas_le_encLen a ha; have ib := exprGas_le_encLen b hb
           have ipa := encExpr_pos_of_dq a ha; have ipb := encExpr_pos_of_dq b hb
           show max (exprGas a) (exprGas b) + 5 ≤
             4 * (("4" ++ encExpr a ++ encExpr b)).toList.length + 4
           simp only [toList_append, List.length_append,
             show ("4".toList.length : Nat) = 1 from rfl]; omega)
        | (have ia := exprGas_le_encLen a ha; have ib := exprGas_le_encLen b hb
           have ipa := encExpr_pos_of_dq a ha; have ipb := encExpr_pos_of_dq b hb
           show max (exprGas a) (exprGas b) + 5 ≤
             4 * (("c" ++ encExpr a ++ encExpr b)).toList.length + 4
           simp only [toList_append, List.length_append,
             show ("c".toList.length : Nat) = 1 from rfl]; omega)
  | .ifE c th el, hd => by
      obtain ⟨h1, h2, h3⟩ := hd
      have i1 := exprGas_le_encLen c h1; have i2 := exprGas_le_encLen th h2
      have i3 := exprGas_le_encLen el h3
      have ip1 := encExpr_pos_of_dq c h1; have ip2 := encExpr_pos_of_dq th h2
      have ip3 := encExpr_pos_of_dq el h3
      show max (exprGas c) (max (exprGas th) (exprGas el)) + 6 ≤
        4 * (("3" ++ encExpr c ++ encExpr th ++ encExpr el)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("3".toList.length : Nat) = 1 from rfl]; omega
  | .fst a, hd | .snd a, hd => by
      have ia := exprGas_le_encLen a hd
      first
        | (show exprGas a + 4 ≤ 4 * (("5" ++ encExpr a)).toList.length + 4
           simp only [toList_append, List.length_append,
             show ("5".toList.length : Nat) = 1 from rfl]; omega)
        | (show exprGas a + 4 ≤ 4 * (("6" ++ encExpr a)).toList.length + 4
           simp only [toList_append, List.length_append,
             show ("6".toList.length : Nat) = 1 from rfl]; omega)
  | .inj i ts a, hd => by
      obtain ⟨_, _, _, _, ha⟩ := hd
      have is := tysGas_le_encTysLen ts; have ia := exprGas_le_encLen a ha
      have ipa := encExpr_pos_of_dq a ha
      have hn := encNat_len_pos i; have hn' := encNat_len_pos (↑ts.length)
      show max (tysGas ts + ts.length + 3) (exprGas a + 1) + 5 ≤
        4 * (("7" ++ encNat i ++ encNat ↑ts.length ++ encTys ts ++
          encExpr a)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("7".toList.length : Nat) = 1 from rfl]; omega
  | .matchE s bs, hd => by
      obtain ⟨hs, _, hbs⟩ := hd
      have is := exprGas_le_encLen s hs; have ib := exprsGas_le_encExprsLen bs hbs
      have hn := encNat_len_pos (↑bs.length)
      show max (exprGas s + 1) (exprsGas bs + bs.length + 3) + 4 ≤
        4 * (("8" ++ encExpr s ++ encNat ↑bs.length ++
          encExprs bs)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("8".toList.length : Nat) = 1 from rfl]; omega
  | .recordE keys fs, hd => by
      obtain ⟨_, _, _, hfs⟩ := hd
      have ib := exprsGas_le_encExprsLen fs hfs
      have hn := encNat_len_pos (↑keys.length)
      have hn' := encNat_len_pos (↑fs.length)
      have hj : keys.length ≤ (String.join (keys.map encStr)).toList.length := by
        rw [encStr_catEnc]
        exact list_length_le_catEnc encStr keys (fun x _ => encStr_len_pos x)
      show max (keys.length + 3) (exprsGas fs + fs.length + 3) + 4 ≤
        4 * (("9" ++ encNat ↑keys.length ++
          String.join (keys.map encStr) ++ encNat ↑fs.length ++
          encExprs fs)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("9".toList.length : Nat) = 1 from rfl]; omega
  | .field r i, hd => by
      obtain ⟨hr, _, _⟩ := hd
      have ir := exprGas_le_encLen r hr
      have hn := encNat_len_pos i
      show exprGas r + 5 ≤
        4 * (("a" ++ encExpr r ++ encNat i)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("a".toList.length : Nat) = 1 from rfl]; omega
  | .nil t, hd => by
      have it := tyGas_le_encLen t
      show tyGas t + 4 ≤ 4 * (("b" ++ encTy t)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("b".toList.length : Nat) = 1 from rfl]; omega
  | .fold l init body, hd => by
      obtain ⟨h1, h2, h3⟩ := hd
      have i1 := exprGas_le_encLen l h1; have i2 := exprGas_le_encLen init h2
      have i3 := exprGas_le_encLen body h3
      have ip1 := encExpr_pos_of_dq l h1; have ip2 := encExpr_pos_of_dq init h2
      have ip3 := encExpr_pos_of_dq body h3
      show max (exprGas l) (max (exprGas init) (exprGas body)) + 6 ≤
        4 * (("d" ++ encExpr l ++ encExpr init ++ encExpr body)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("d".toList.length : Nat) = 1 from rfl]; omega
  | .fix i l s st, hd => by
      obtain ⟨h1, h2, h3, h4⟩ := hd
      have i1 := exprGas_le_encLen i h1; have i2 := exprGas_le_encLen l h2
      have i3 := exprGas_le_encLen s h3; have i4 := exprGas_le_encLen st h4
      have ip1 := encExpr_pos_of_dq i h1; have ip2 := encExpr_pos_of_dq l h2
      have ip3 := encExpr_pos_of_dq s h3; have ip4 := encExpr_pos_of_dq st h4
      show max (exprGas i) (max (exprGas l) (max (exprGas s) (exprGas st))) + 7 ≤
        4 * (("e" ++ encExpr i ++ encExpr l ++ encExpr s ++
          encExpr st)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("e".toList.length : Nat) = 1 from rfl]; omega
  | .prim op args, hd => by
      obtain ⟨_, _, hargs⟩ := hd
      have ia := exprsGas_le_encExprsLen args hargs
      have hn := encNat_len_pos (↑args.length); have hs := encStr_len_pos op
      show max 1 (exprsGas args + args.length + 3) + 4 ≤
        4 * (("f" ++ encStr op ++ encNat ↑args.length ++
          encExprs args)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("f".toList.length : Nat) = 1 from rfl]; omega
  | .call (.local i) args, hd => by
      obtain ⟨_, hargs, _⟩ := hd
      have ia := exprsGas_le_encExprsLen args hargs
      have hn := encNat_len_pos i; have hn' := encNat_len_pos (↑args.length)
      show exprsGas args + args.length + 4 ≤
        4 * (("g" ++ "l" ++ encNat i ++ encNat ↑args.length ++
          encExprs args)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("g".toList.length : Nat) = 1 from rfl,
        show ("l".toList.length : Nat) = 1 from rfl]; omega
  | .call (.ext r) args, hd => by
      obtain ⟨_, hargs, _⟩ := hd
      have ia := exprsGas_le_encExprsLen args hargs
      have hn := encNat_len_pos (↑args.length); have hs := encStr_len_pos r
      show exprsGas args + args.length + 4 ≤
        4 * (("g" ++ "x" ++ encStr r ++ encNat ↑args.length ++
          encExprs args)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("g".toList.length : Nat) = 1 from rfl,
        show ("x".toList.length : Nat) = 1 from rfl]; omega
  | .raise r p t, hd => by
      obtain ⟨_, hp, _⟩ := hd
      have ip := exprGas_le_encLen p hp; have it := tyGas_le_encLen t
      have ipp := encExpr_pos_of_dq p hp; have ipt := encTy_len_pos t
      have hs := encStr_len_pos r
      show max 1 (max (exprGas p + 1) (tyGas t + 1)) + 5 ≤
        4 * (("h" ++ encStr r ++ encExpr p ++ encTy t)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("h".toList.length : Nat) = 1 from rfl]; omega
  | .handle r b h, hd => by
      obtain ⟨_, hb, hh⟩ := hd
      have ib := exprGas_le_encLen b hb; have ih := exprGas_le_encLen h hh
      have ipb := encExpr_pos_of_dq b hb; have iph := encExpr_pos_of_dq h hh
      have hs := encStr_len_pos r
      show max 1 (max (exprGas b + 1) (exprGas h + 1)) + 5 ≤
        4 * (("j" ++ encStr r ++ encExpr b ++ encExpr h)).toList.length + 4
      simp only [toList_append, List.length_append,
        show ("j".toList.length : Nat) = 1 from rfl]; omega
  | .unknown _, hd => absurd hd not_false
/-- `decList`-gas over an expression list. -/
theorem exprsGas_le_encExprsLen : ∀ (es : List RawExpr) (_ : dqsE es),
    exprsGas es + es.length ≤ 4 * (encExprs es).toList.length + 5
  | [], _ => Nat.zero_le _
  | e :: es, hd => by
      obtain ⟨he, hes⟩ := hd
      have ie := exprGas_le_encLen e he
      have is := exprsGas_le_encExprsLen es hes
      have il := exprs_len_le_encExprs es hes
      have ip := encExpr_pos_of_dq e he
      show max (exprGas e) (exprsGas es) + (es.length + 1) ≤
        4 * ((encExpr e ++ encExprs es)).toList.length + 5
      simp only [toList_append, List.length_append]; omega
end

/-! ## Schema-item decoding

`decSeq` dispatches each schema field `kd` three ways: `decList` at
`kd ≥ 10`, `decNat` at `kd = 5`, and `dec` at the element kinds
`0/1/2/4`. `dqItem` collects the data-quality premise an item needs at
its kind; `itemGas`/`itemFuel` measure the `decSeq` level each shape
consumes. -/

/-- `x` decodes as a `dec` element at kind `kd ∈ {0,1,2,4}`. -/
def dqElem (kd : Nat) (x : Item) : Prop :=
  (kd = 0 ∧ ∃ t, x = .ty t ∧ dqT t) ∨
  (kd = 1 ∧ ∃ v, x = .val v ∧ dqV v) ∨
  (kd = 2 ∧ ∃ e, x = .expr e ∧ dqE e) ∨
  (kd = 4 ∧ ∃ s, x = .str s ∧ s.length ≤ 1024)

/-- `x` decodes under schema kind `kd`: an element at `0/1/2/4`, a
    natural at `5`, or a counted list of `kd - 10` elements. -/
def dqItem (kd : Nat) (x : Item) : Prop :=
  dqElem kd x ∨
  (kd = 5 ∧ ∃ n, x = .num n ∧ 0 ≤ n ∧ inI64 n) ∨
  (10 ≤ kd ∧ ∃ xs, x = .list xs ∧ xs.length ≤ 1024 ∧
    ∀ y ∈ xs, dqElem (kd - 10) y)

/-- `dec`-element gas: the `dec` level plus the payload decoder's own. -/
def elemGas : Item → Nat
  | .ty t => tyGas t + 1
  | .val v => valGas v + 1
  | .expr e => exprGas e + 1
  | _ => 1

/-- Element-gas fold over a decoded list. -/
def elemsGas : List Item → Nat
  | [] => 0
  | y :: ys => max (elemGas y) (elemsGas ys)

/-- The `decSeq`-dispatch gas an item needs at kind `kd`. -/
def itemGas (kd : Nat) (x : Item) : Nat :=
  match x with
  | .list xs => if 10 ≤ kd then elemsGas xs + xs.length + 2 else 1
  | _ => elemGas x

/-- `dec`-element fuel: the payload decoder's own fuel measure. -/
def elemFuel : Item → Nat
  | .ty t => tyFuel t
  | .val v => valFuel v
  | .expr e => exprFuel e
  | _ => 0

/-- Element-fuel fold over a decoded list. -/
def elemsFuel : List Item → Nat
  | [] => 0
  | y :: ys => max (elemFuel y) (elemsFuel ys)

/-- The fuel an item needs: `dec`-elements pay one level; lists pay one
    plus the element fold; `decNat` pays nothing. -/
def itemFuel (kd : Nat) (x : Item) : Nat :=
  if 10 ≤ kd then
    match x with
    | .list xs => elemsFuel xs + 1
    | _ => 1
  else if kd = 5 then 0
  else elemFuel x + 1

/-- `decSeq`'s `minG` fold over `ks.zip xs`. -/
def itemsGas (ks : List Nat) (xs : List Item) : Nat :=
  (ks.zip xs).foldr (fun pr a => max (itemGas pr.1 pr.2) a) 0

/-- The fuel fold over `ks.zip xs`. -/
def itemsFuel (ks : List Nat) (xs : List Item) : Nat :=
  (ks.zip xs).foldr (fun pr a => max (itemFuel pr.1 pr.2) a) 0

theorem elemGas_le_elemsGas {y : Item} {xs : List Item} (hm : y ∈ xs) :
    elemGas y ≤ elemsGas xs := by
  induction xs with
  | nil => cases hm
  | cons z zs ih =>
    cases hm with
    | head => simp only [elemsGas]; omega
    | tail _ hm' => have := ih hm'; simp only [elemsGas]; omega

theorem elemFuel_le_elemsFuel {y : Item} {xs : List Item} (hm : y ∈ xs) :
    elemFuel y ≤ elemsFuel xs := by
  induction xs with
  | nil => cases hm
  | cons z zs ih =>
    cases hm with
    | head => simp only [elemsFuel]; omega
    | tail _ hm' => have := ih hm'; simp only [elemsFuel]; omega

theorem itemGas_le_itemsGas {ks : List Nat} {xs : List Item} {kd : Nat}
    {x : Item} : (kd, x) ∈ ks.zip xs → itemGas kd x ≤ itemsGas ks xs := by
  induction xs generalizing ks with
  | nil => intro hm; cases ks <;> cases hm
  | cons z zs ih =>
    intro hm
    cases ks with
    | nil => cases hm
    | cons k ks' =>
      have e : itemsGas (k :: ks') (z :: zs) =
          max (itemGas k z) (itemsGas ks' zs) := rfl
      rw [e]
      cases hm with
      | head => omega
      | tail _ hm' => have := ih hm'; omega

theorem itemFuel_le_itemsFuel {ks : List Nat} {xs : List Item} {kd : Nat}
    {x : Item} : (kd, x) ∈ ks.zip xs → itemFuel kd x ≤ itemsFuel ks xs := by
  induction xs generalizing ks with
  | nil => intro hm; cases ks <;> cases hm
  | cons z zs ih =>
    intro hm
    cases ks with
    | nil => cases hm
    | cons k ks' =>
      have e : itemsFuel (k :: ks') (z :: zs) =
          max (itemFuel k z) (itemsFuel ks' zs) := rfl
      rw [e]
      cases hm with
      | head => omega
      | tail _ hm' => have := ih hm'; omega

theorem encBase_0 (t : CoreTy) : encBase 0 (.ty t) = encTy t := rfl
theorem encBase_1 (v : Val) : encBase 1 (.val v) = encVal v := rfl
theorem encBase_2 (e : RawExpr) : encBase 2 (.expr e) = encExpr e := rfl
theorem encBase_4 (s : String) : encBase 4 (.str s) = encStr s := rfl

theorem encItem_list (kd : Nat) (xs : List Item) (hk : 10 ≤ kd) :
    encItem kd (.list xs) =
      encNat (↑xs.length : Int) ++ String.join (xs.map (encBase (kd - 10))) := by
  unfold encItem
  rw [if_pos hk]
  rfl

theorem elemEnc_pos {kd : Nat} {y : Item} (hdq : dqElem kd y) :
    1 ≤ (encBase kd y).toList.length := by
  rcases hdq with ⟨rfl, t, rfl, _⟩ | ⟨rfl, v, rfl, _⟩ |
    ⟨rfl, e, rfl, hde⟩ | ⟨rfl, s, rfl, _⟩
  · show 1 ≤ (encTy t).toList.length; exact encTy_len_pos t
  · show 1 ≤ (encVal v).toList.length; exact encVal_len_pos v
  · show 1 ≤ (encExpr e).toList.length; exact encExpr_pos_of_dq e hde
  · show 1 ≤ (encStr s).toList.length; exact encStr_len_pos s

theorem elemGas_le_encBase {kd : Nat} {y : Item} (hdq : dqElem kd y) :
    elemGas y ≤ 4 * (encBase kd y).toList.length + 5 := by
  rcases hdq with ⟨rfl, t, rfl, hdt⟩ | ⟨rfl, v, rfl, hdv⟩ |
    ⟨rfl, e, rfl, hde⟩ | ⟨rfl, s, rfl, hslen⟩
  · show tyGas t + 1 ≤ 4 * (encTy t).toList.length + 5
    have := tyGas_le_encLen t; omega
  · show valGas v + 1 ≤ 4 * (encVal v).toList.length + 5
    have := valGas_le_encLen v; omega
  · show exprGas e + 1 ≤ 4 * (encExpr e).toList.length + 5
    have := exprGas_le_encLen e hde; omega
  · show 1 ≤ 4 * (encStr s).toList.length + 5
    have := encStr_len_pos s; omega

theorem elemFuel_le_encBase {kd : Nat} {y : Item} (hdq : dqElem kd y) :
    elemFuel y ≤ (encBase kd y).toList.length := by
  rcases hdq with ⟨rfl, t, rfl, hdt⟩ | ⟨rfl, v, rfl, hdv⟩ |
    ⟨rfl, e, rfl, hde⟩ | ⟨rfl, s, rfl, hslen⟩
  · show tyFuel t ≤ (encTy t).toList.length; exact tyFuel_le_encLen t
  · show valFuel v ≤ (encVal v).toList.length; exact valFuel_le_encLen v
  · show exprFuel e ≤ (encExpr e).toList.length; exact exprFuel_le_encLen e
  · show 0 ≤ (encStr s).toList.length; omega

theorem elemsGas_le_catEnc {kd : Nat} : ∀ (xs : List Item),
    (∀ y ∈ xs, dqElem kd y) →
    elemsGas xs ≤ 4 * (catEnc (encBase kd) xs).toList.length + 5
  | [], _ => Nat.zero_le _
  | y :: ys, hd => by
      have iy := elemGas_le_encBase (hd _ (List.mem_cons_self ..))
      have ih := elemsGas_le_catEnc ys (fun z hz => hd z (List.mem_cons_of_mem _ hz))
      have ip := elemEnc_pos (hd _ (List.mem_cons_self ..))
      rw [catEnc_cons, List.length_append]
      show max (elemGas y) (elemsGas ys) ≤
        4 * ((encBase kd y).toList.length +
          (catEnc (encBase kd) ys).toList.length) + 5
      omega

theorem elemsFuel_le_catEnc {kd : Nat} : ∀ (xs : List Item),
    (∀ y ∈ xs, dqElem kd y) →
    elemsFuel xs ≤ (catEnc (encBase kd) xs).toList.length
  | [], _ => Nat.zero_le _
  | y :: ys, hd => by
      have iy := elemFuel_le_encBase (hd _ (List.mem_cons_self ..))
      have ih := elemsFuel_le_catEnc ys (fun z hz => hd z (List.mem_cons_of_mem _ hz))
      rw [catEnc_cons, List.length_append]
      show max (elemFuel y) (elemsFuel ys) ≤
        (encBase kd y).toList.length + (catEnc (encBase kd) ys).toList.length
      omega

theorem itemGas_le_encItem {kd : Nat} {x : Item} (hdq : dqItem kd x) :
    itemGas kd x ≤ 5 * (encItem kd x).toList.length + 7 := by
  rcases hdq with (⟨rfl, t, rfl, hdt⟩ | ⟨rfl, v, rfl, hdv⟩ |
      ⟨rfl, e, rfl, hde⟩ | ⟨rfl, s, rfl, hslen⟩) |
    ⟨rfl, n, rfl, h0n, hin⟩ | ⟨h10, xs, rfl, hxlen, hdmem⟩
  · show tyGas t + 1 ≤ 5 * (encItem 0 (.ty t)).toList.length + 7
    rw [encItem_0]; have := tyGas_le_encLen t; omega
  · show valGas v + 1 ≤ 5 * (encItem 1 (.val v)).toList.length + 7
    rw [encItem_1]; have := valGas_le_encLen v; omega
  · show exprGas e + 1 ≤ 5 * (encItem 2 (.expr e)).toList.length + 7
    rw [encItem_2]; have := exprGas_le_encLen e hde; omega
  · show (1 : Nat) ≤ 5 * (encItem 4 (.str s)).toList.length + 7
    rw [encItem_4]; omega
  · show (1 : Nat) ≤ 5 * (encItem 5 (.num n)).toList.length + 7
    rw [encItem_5]; omega
  · have hG' : itemGas kd (.list xs) = elemsGas xs + xs.length + 2 := by
      dsimp only [itemGas]; rw [if_pos h10]
    rw [hG']
    have hg := elemsGas_le_catEnc xs hdmem
    have hl : xs.length ≤ (catEnc (encBase (kd - 10)) xs).toList.length :=
      list_length_le_catEnc _ xs (fun y hy => elemEnc_pos (hdmem y hy))
    rw [encItem_list kd xs h10, toList_append, encNat_toList,
      List.length_append, List.length_append, List.length_cons,
      List.length_nil,
      show String.join (xs.map (encBase (kd - 10))) =
        catEnc (encBase (kd - 10)) xs from rfl]
    omega

theorem itemFuel_le_encItem {kd : Nat} {x : Item} (hdq : dqItem kd x) :
    itemFuel kd x ≤ (encItem kd x).toList.length + 1 := by
  rcases hdq with (⟨rfl, t, rfl, hdt⟩ | ⟨rfl, v, rfl, hdv⟩ |
      ⟨rfl, e, rfl, hde⟩ | ⟨rfl, s, rfl, hslen⟩) |
    ⟨rfl, n, rfl, h0n, hin⟩ | ⟨h10, xs, rfl, hxlen, hdmem⟩
  · show tyFuel t + 1 ≤ (encItem 0 (.ty t)).toList.length + 1
    rw [encItem_0]; exact Nat.succ_le_succ (tyFuel_le_encLen t)
  · show valFuel v + 1 ≤ (encItem 1 (.val v)).toList.length + 1
    rw [encItem_1]; exact Nat.succ_le_succ (valFuel_le_encLen v)
  · show exprFuel e + 1 ≤ (encItem 2 (.expr e)).toList.length + 1
    rw [encItem_2]; exact Nat.succ_le_succ (exprFuel_le_encLen e)
  · show 0 + 1 ≤ (encItem 4 (.str s)).toList.length + 1
    rw [encItem_4]; omega
  · show 0 ≤ (encItem 5 (.num n)).toList.length + 1
    rw [encItem_5]; omega
  · have hF' : itemFuel kd (.list xs) = elemsFuel xs + 1 := by
      dsimp only [itemFuel]; rw [if_pos h10]
    rw [hF']
    have hf := elemsFuel_le_catEnc xs hdmem
    have hn := encNat_len_pos (↑xs.length : Int)
    rw [encItem_list kd xs h10, toList_append, encNat_toList,
      List.length_append, List.length_append, List.length_cons,
      List.length_nil,
      show String.join (xs.map (encBase (kd - 10))) =
        catEnc (encBase (kd - 10)) xs from rfl]
    omega

theorem itemsGas_le_encItems : ∀ (ks : List Nat) (xs : List Item),
    (∀ pr ∈ ks.zip xs, dqItem pr.1 pr.2) →
    itemsGas ks xs ≤ 5 * (encItems ks xs).toList.length + 7 := by
  intro ks xs hdq
  induction xs generalizing ks with
  | nil =>
    have e : itemsGas ks [] = 0 := by cases ks <;> rfl
    rw [e]; omega
  | cons y ys ih =>
    cases ks with
    | nil =>
      have e : itemsGas [] (y :: ys) = 0 := rfl
      rw [e]; omega
    | cons k ks' =>
      have e : itemsGas (k :: ks') (y :: ys) =
          max (itemGas k y) (itemsGas ks' ys) := rfl
      rw [e]
      have iy : itemGas k y ≤ 5 * (encItem k y).toList.length + 7 :=
        itemGas_le_encItem (hdq _ (List.mem_cons_self ..))
      have ih' : itemsGas ks' ys ≤ 5 * (encItems ks' ys).toList.length + 7 :=
        ih ks' (fun pr hpr => hdq pr (List.mem_cons_of_mem _ hpr))
      rw [encItems_cons, toList_append, List.length_append]
      omega

theorem itemsFuel_le_encItems : ∀ (ks : List Nat) (xs : List Item),
    (∀ pr ∈ ks.zip xs, dqItem pr.1 pr.2) →
    itemsFuel ks xs ≤ (encItems ks xs).toList.length + 1 := by
  intro ks xs hdq
  induction xs generalizing ks with
  | nil =>
    have e : itemsFuel ks [] = 0 := by cases ks <;> rfl
    rw [e]; omega
  | cons y ys ih =>
    cases ks with
    | nil =>
      have e : itemsFuel [] (y :: ys) = 0 := rfl
      rw [e]; omega
    | cons k ks' =>
      have e : itemsFuel (k :: ks') (y :: ys) =
          max (itemFuel k y) (itemsFuel ks' ys) := rfl
      rw [e]
      have iy : itemFuel k y ≤ (encItem k y).toList.length + 1 :=
        itemFuel_le_encItem (hdq _ (List.mem_cons_self ..))
      have ih' : itemsFuel ks' ys ≤ (encItems ks' ys).toList.length + 1 :=
        ih ks' (fun pr hpr => hdq pr (List.mem_cons_of_mem _ hpr))
      rw [encItems_cons, toList_append, List.length_append]
      omega

/-- `decSeq`'s per-field dispatch accepts a canonical `encItem`. -/
theorem decItemEnc (cs : Array Char) (fuel : Int) (kd : Nat) (x : Item)
    (hdq : dqItem kd x) :
    ∀ (g' : Nat) (p' : Nat) (rest' : List Char),
    cs.toList.drop p' = (encItem kd x).toList ++ rest' →
    itemGas kd x ≤ g' → (itemFuel kd x : Int) ≤ fuel →
    (if kd ≥ 10 then decList cs g' (kd - 10) fuel p'
     else if kd = 5 then (decNat cs p').map (fun (n, q) => (Item.num n, q))
     else dec cs g' kd (fuel - 1) p') =
      .ok (x, p' + (encItem kd x).toList.length) := by
  intro g' p' rest' hd hG hF
  rcases hdq with (⟨rfl, t, rfl, hdt⟩ | ⟨rfl, v, rfl, hdv⟩ |
      ⟨rfl, e, rfl, hde⟩ | ⟨rfl, s, rfl, hslen⟩) |
    ⟨rfl, n, rfl, h0n, hin⟩ | ⟨h10, xs, rfl, hxlen, hdmem⟩
  · rw [if_neg (by decide : ¬ (0 : Nat) ≥ 10),
      if_neg (by decide : ¬ (0 : Nat) = 5)]
    rw [encItem_0] at hd ⊢
    have hG' : tyGas t + 1 ≤ g' := hG
    have hF' : (↑(tyFuel t + 1) : Int) ≤ fuel := hF
    exact dec_zero' cs g' (fuel - 1) p' _ (.ty t) (by omega)
      (decTy_enc t cs (g' - 1) (fuel - 1) p' rest' hd
        (by omega) (by omega) hdt) (by omega)
  · rw [if_neg (by decide : ¬ (1 : Nat) ≥ 10),
      if_neg (by decide : ¬ (1 : Nat) = 5)]
    rw [encItem_1] at hd ⊢
    have hG' : valGas v + 1 ≤ g' := hG
    have hF' : (↑(valFuel v + 1) : Int) ≤ fuel := hF
    exact dec_one' cs g' (fuel - 1) p' _ (.val v) (by omega)
      (decVal_enc v cs (g' - 1) (fuel - 1) p' rest' hd
        (by omega) (by omega) hdv) (by omega)
  · rw [if_neg (by decide : ¬ (2 : Nat) ≥ 10),
      if_neg (by decide : ¬ (2 : Nat) = 5)]
    rw [encItem_2] at hd ⊢
    have hG' : exprGas e + 1 ≤ g' := hG
    have hF' : (↑(exprFuel e + 1) : Int) ≤ fuel := hF
    exact dec_two' cs g' (fuel - 1) p' _ (.expr e) (by omega)
      (decExpr_enc e cs (g' - 1) (fuel - 1) p' rest' hd
        (by omega) (by omega) hde) (by omega)
  · rw [if_neg (by decide : ¬ (4 : Nat) ≥ 10),
      if_neg (by decide : ¬ (4 : Nat) = 5)]
    rw [encItem_4] at hd ⊢
    have hG' : (1 : Nat) ≤ g' := hG
    have hF' : (↑(0 + 1) : Int) ≤ fuel := hF
    exact decStr_elem cs g' (fuel - 1) s p' rest' hd hG' (by omega) hslen
  · rw [if_neg (by decide : ¬ (5 : Nat) ≥ 10), if_pos rfl]
    rw [encItem_5] at hd ⊢
    exact decNat_elem cs n h0n hin p' rest' hd
  · rw [if_pos h10]
    have hG' : elemsGas xs + xs.length + 2 ≤ g' := by
      dsimp only [itemGas] at hG; rw [if_pos h10] at hG; exact hG
    have hF' : (↑(elemsFuel xs + 1) : Int) ≤ fuel := by
      dsimp only [itemFuel] at hF; rw [if_pos h10] at hF; exact hF
    have hd' : cs.toList.drop p' =
        (toString (↑xs.length : Int)).toList ++
          (';' :: ((catEnc (encBase (kd - 10)) xs).toList ++ rest')) := by
      rw [encItem_list kd xs h10, toList_append, encNat_toList,
        List.append_assoc, List.append_assoc, List.cons_append,
        List.nil_append] at hd
      exact hd
    have hdl := decList_enc (encBase (kd - 10)) cs g' (kd - 10) fuel
      (elemsGas xs) xs p' rest' hd' hG' hxlen
      ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩
      (toString_len_lt24 xs.length hxlen)
      (fun g'' y hg''1 _ hm p'' rest'' hd'' => by
        rcases hdmem y hm with ⟨hk0, t, rfl, hdt⟩ | ⟨hk1, v, rfl, hdv⟩ |
            ⟨hk2, e, rfl, hde⟩ | ⟨hk4, s, rfl, hslen⟩
        · have hkd : kd = 10 := by omega
          subst hkd
          have hdg : cs.toList.drop p'' = (encTy t).toList ++ rest'' := hd''
          have hge : tyGas t + 1 ≤ g'' := by
            have := elemGas_le_elemsGas hm; simp only [elemGas] at this; omega
          have hfe : (↑(tyFuel t) : Int) ≤ fuel - 1 := by
            have h1 := elemFuel_le_elemsFuel hm
            simp only [elemFuel] at h1; omega
          exact dec_zero' cs g'' (fuel - 1) p'' _ (.ty t) (by omega)
            (decTy_enc t cs (g'' - 1) (fuel - 1) p'' rest'' hdg
              (by omega) hfe hdt) (by omega)
        · have hkd : kd = 11 := by omega
          subst hkd
          have hdg : cs.toList.drop p'' = (encVal v).toList ++ rest'' := hd''
          have hge : valGas v + 1 ≤ g'' := by
            have := elemGas_le_elemsGas hm; simp only [elemGas] at this; omega
          have hfe : (↑(valFuel v) : Int) ≤ fuel - 1 := by
            have h1 := elemFuel_le_elemsFuel hm
            simp only [elemFuel] at h1; omega
          exact dec_one' cs g'' (fuel - 1) p'' _ (.val v) (by omega)
            (decVal_enc v cs (g'' - 1) (fuel - 1) p'' rest'' hdg
              (by omega) hfe hdv) (by omega)
        · have hkd : kd = 12 := by omega
          subst hkd
          have hdg : cs.toList.drop p'' = (encExpr e).toList ++ rest'' := hd''
          have hge : exprGas e + 1 ≤ g'' := by
            have := elemGas_le_elemsGas hm; simp only [elemGas] at this; omega
          have hfe : (↑(exprFuel e) : Int) ≤ fuel - 1 := by
            have h1 := elemFuel_le_elemsFuel hm
            simp only [elemFuel] at h1; omega
          exact dec_two' cs g'' (fuel - 1) p'' _ (.expr e) (by omega)
            (decExpr_enc e cs (g'' - 1) (fuel - 1) p'' rest'' hdg
              (by omega) hfe hde) (by omega)
        · have hkd : kd = 14 := by omega
          subst hkd
          have hdg : cs.toList.drop p'' = (encStr s).toList ++ rest'' := hd''
          have hge : (1 : Nat) ≤ g'' := by
            have := elemGas_le_elemsGas hm; simp only [elemGas] at this; omega
          exact decStr_elem cs g'' (fuel - 1) s p'' rest'' hdg hge
            (by omega) hslen)
    have elen : (encItem kd (.list xs)).toList.length =
        (toString (↑xs.length : Int)).toList.length + 1 +
          (catEnc (encBase (kd - 10)) xs).toList.length := by
      rw [encItem_list kd xs h10, toList_append, encNat_toList,
        List.length_append, List.length_append, List.length_cons,
        List.length_nil,
        show String.join (xs.map (encBase (kd - 10))) =
          catEnc (encBase (kd - 10)) xs from rfl]
    rw [hdl, elen]
    have he : (toString (↑xs.length : Int)).toList.length =
        (toString xs.length).toList.length := rfl
    rw [he]
    congr 1
    congr 1
    omega

/-- `kindsOf` bounds the tag and the row length. -/
theorem kindsOf_bounds {what tag : Int} {ks : List Nat}
    (h : kindsOf what tag = some ks) :
    0 ≤ tag ∧ tag.toNat ≤ 21 ∧ ks.length ≤ 9 := by
  unfold kindsOf at h
  dsimp only [] at h
  by_cases hneg : tag < 0
  · rw [if_pos hneg] at h; cases h
  · rw [if_neg hneg] at h
    have hnn : 0 ≤ tag := by omega
    by_cases w0 : what = 0
    · rw [if_pos w0] at h
      obtain ⟨hlt, _⟩ := List.get?_eq_some.1 h
      have hlen : ctlKinds.length = 3 := rfl
      rw [hlen] at hlt
      have hkl : ks ∈ ctlKinds := List.get?_mem h
      have hb : ∀ ks ∈ ctlKinds, ks.length ≤ 9 := by decide
      exact ⟨hnn, by omega, hb ks hkl⟩
    · rw [if_neg w0] at h
      by_cases w2 : what = 2
      · rw [if_pos w2] at h
        obtain ⟨hlt, _⟩ := List.get?_eq_some.1 h
        have hlen : finKinds.length = 2 := rfl
        rw [hlen] at hlt
        have hkl : ks ∈ finKinds := List.get?_mem h
        have hb : ∀ ks ∈ finKinds, ks.length ≤ 9 := by decide
        exact ⟨hnn, by omega, hb ks hkl⟩
      · rw [if_neg w2] at h
        obtain ⟨hlt, _⟩ := List.get?_eq_some.1 h
        have hlen : frameKinds.length = 22 := rfl
        rw [hlen] at hlt
        have hkl : ks ∈ frameKinds := List.get?_mem h
        have hb : ∀ ks ∈ frameKinds, ks.length ≤ 9 := by decide
        exact ⟨hnn, by omega, hb ks hkl⟩

/-- `decTagged` reads `encNat tag ++ encItems schema xs` back to `⟨tag, xs⟩`. -/
theorem decTagged_enc (cs : Array Char) (what fuel : Int) (G p : Nat)
    (g : Tagged) (ks : List Nat) (rest : List Char)
    (hk : kindsOf what g.tag = some ks)
    (hxs : g.xs.length = ks.length)
    (hdq : ∀ pr ∈ ks.zip g.xs, dqItem pr.1 pr.2)
    (h : cs.toList.drop p = (encTagged what g).toList ++ rest)
    (hG : itemsGas ks g.xs + ks.length + 1 ≤ G)
    (hF : ∀ pr ∈ ks.zip g.xs, (itemFuel pr.1 pr.2 : Int) ≤ fuel) :
    decTagged cs G what fuel p = .ok (g, p + (encTagged what g).toList.length) := by
  obtain ⟨h0, ht, _⟩ := kindsOf_bounds hk
  have hin : inI64 g.tag := ⟨by unfold i64Min; omega, by unfold i64Max; omega⟩
  have hEnc : (encTagged what g).toList =
      (encNat g.tag).toList ++ (encItems ks g.xs).toList := by
    show (encNat g.tag ++ encItems ((kindsOf what g.tag).getD []) g.xs).toList = _
    rw [hk, Option.getD_some, toList_append]
  have hd : cs.toList.drop p = (encNat g.tag).toList ++
      ((encItems ks g.xs).toList ++ rest) := by
    rw [hEnc] at h; rw [List.append_assoc] at h; exact h
  have hdn := decNat_encInt g.tag h0 hin cs p
    ((encItems ks g.xs).toList ++ rest) hd
  have hseq := decSeq_enc cs fuel (itemsGas ks g.xs) ks g.xs G
    (p + (toString g.tag).toList.length + 1) rest
    (by rw [encNat_toList] at hd
        have e := drop_append_advance (l := cs.toList) (p := p)
          (s := (toString g.tag).toList ++ [';'])
          (r := (encItems ks g.xs).toList ++ rest) hd
        have h1 : ((toString g.tag).toList ++ [';']).length =
            (toString g.tag).toList.length + 1 := by
          rw [List.length_append]; rfl
        rwa [h1] at e)
    hxs hG
    (fun g' k x hg'1 _ hm p' rest' hd' =>
      decItemEnc cs fuel k x (hdq _ hm) g' p' rest' hd'
        (by have := itemGas_le_itemsGas hm; omega) (hF _ hm))
  unfold decTagged
  rw [hdn]
  simp only [Bind.bind, Except.bind]
  rw [hk]
  dsimp only []
  rw [hseq]
  dsimp only []
  rw [hEnc, encNat_toList, List.length_append, List.length_append,
    List.length_cons, List.length_nil]
  congr 1
  congr 1
  omega

/-- `decTaggedStr` accepts a canonical `encTagged` at `fuel ≥ length`. -/
theorem decTaggedStr_encTagged (what fuel : Int) (g : Tagged) (ks : List Nat)
    (hk : kindsOf what g.tag = some ks)
    (hxs : g.xs.length = ks.length)
    (hdq : ∀ pr ∈ ks.zip g.xs, dqItem pr.1 pr.2)
    (hF : ((encTagged what g).toList.length : Int) ≤ fuel) :
    decTaggedStr what fuel (encTagged what g) = .ok g := by
  have hks : (kindsOf what g.tag).getD [] = ks := by
    simp only [hk, Option.getD_some]
  have hIL := encItems_le_encTagged what g
  rw [hks] at hIL
  have hIG := itemsGas_le_encItems ks g.xs hdq
  have hIF := itemsFuel_le_encItems ks g.xs hdq
  have hNP := encNat_len_pos g.tag
  have hEnc : (encTagged what g).toList =
      (encNat g.tag).toList ++ (encItems ks g.xs).toList := by
    show (encNat g.tag ++ encItems ((kindsOf what g.tag).getD []) g.xs).toList = _
    rw [hks, toList_append]
  obtain ⟨_, _, hkl⟩ := kindsOf_bounds hk
  show ((decTagged ((encTagged what g).toList.toArray)
      (gasFor fuel ((encTagged what g).toList.toArray).size)
      what fuel 0).map Prod.fst) = .ok g
  calc (decTagged ((encTagged what g).toList.toArray)
        (gasFor fuel ((encTagged what g).toList.toArray).size)
        what fuel 0).map Prod.fst
      = (Except.ok (g, 0 + (encTagged what g).toList.length)).map Prod.fst :=
        congrArg (·.map Prod.fst)
          (decTagged_enc ((encTagged what g).toList.toArray) what fuel
            (gasFor fuel ((encTagged what g).toList.toArray).size) 0 g ks []
            hk hxs hdq
            (by rw [Array.toList_toArray, List.drop_zero, List.append_nil])
            (by rw [Array.size_toArray]
                have h1 : itemsGas ks g.xs + ks.length + 1 ≤
                    8 * (fuel.toNat + 4) +
                      4 * (encTagged what g).toList.length + 4200 := by
                  have hle : (encTagged what g).toList.length ≤ fuel.toNat :=
                    by omega
                  rw [hEnc, List.length_append] at hIL hle ⊢
                  omega
                unfold gasFor; exact h1)
            (fun pr hm => by
              have h1 : itemFuel pr.1 pr.2 ≤ itemsFuel ks g.xs :=
                itemFuel_le_itemsFuel (kd := pr.1) (x := pr.2) hm
              have h2 : itemsFuel ks g.xs ≤ (encTagged what g).toList.length :=
                by rw [hEnc, List.length_append]; omega
              omega))
    _ = .ok g := rfl

/-! ## Object-layer inverses (`decFin`/`decCfg`/`cxDec`)

`dqTgd` bundles the `decTaggedStr` acceptance premises; `dqCfgO`/`dqFinO`/
`dqCX` extend it to the C/F/D object shapes.  The run member of a `D`
object is itself a C or F object decoded at `fuel - 1`; the tag selects
which: `0` reads a final outcome, `1` a configuration. -/

/-- The `decTaggedStr` premises for an embedded tagged string. -/
def dqTgd (what : Int) (g : Tagged) (fuel : Int) : Prop :=
  ∃ ks, kindsOf what g.tag = some ks ∧ g.xs.length = ks.length ∧
    (∀ pr ∈ ks.zip g.xs, dqItem pr.1 pr.2) ∧
    ((encTagged what g).toList.length : Int) ≤ fuel

theorem decTaggedStr_of_dq {what : Int} {g : Tagged} {fuel : Int}
    (h : dqTgd what g fuel) :
    decTaggedStr what fuel (encTagged what g) = .ok g := by
  obtain ⟨ks, hk, hxs, hdq, hF⟩ := h
  exact decTaggedStr_encTagged what fuel g ks hk hxs hdq hF

/-- `mapM (decTaggedStr 1 fuel)` accepts a list of canonical frame
    encodings. -/
theorem mapM_decTaggedStr (fuel : Int) : ∀ (l : List Tagged),
    (∀ f ∈ l, dqTgd 1 f fuel) →
    (l.map (encTagged 1)).mapM (decTaggedStr 1 fuel) = .ok l
  | [], _ => rfl
  | f :: fs, h => by
    rw [List.map_cons, List.mapM_cons]
    simp only [Bind.bind, Except.bind]
    rw [decTaggedStr_of_dq (h f (List.mem_cons_self ..))]
    rw [mapM_decTaggedStr fuel fs (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

/-- The `decSeq` field-callback assembled from the item predicate and a
    length bound on the encoded items. -/
theorem decItemEnc_of_mem (cs : Array Char) (fuel : Int)
    {ks : List Nat} {xs : List Item} {G : Nat}
    (hdq : ∀ pr ∈ ks.zip xs, dqItem pr.1 pr.2)
    (hIF : ∀ pr ∈ ks.zip xs, (itemFuel pr.1 pr.2 : Int) ≤ fuel) :
    ∀ (g' kd : Nat) (x : Item), itemsGas ks xs ≤ g' → g' < G →
      (kd, x) ∈ ks.zip xs → ∀ (p' : Nat) (rest' : List Char),
      cs.toList.drop p' = (encItem kd x).toList ++ rest' →
      (if kd ≥ 10 then decList cs g' (kd - 10) fuel p'
       else if kd = 5 then (decNat cs p').map (fun (n, q) => (Item.num n, q))
       else dec cs g' kd (fuel - 1) p') =
        .ok (x, p' + (encItem kd x).toList.length) := fun g' kd x hg'1 _ hm p' rest' hd' =>
  decItemEnc cs fuel kd x (hdq _ hm) g' p' rest' hd'
    (Nat.le_trans (itemGas_le_itemsGas hm) hg'1) (hIF _ hm)

/-- `decFin` reads `encFin` back to the `FinO` record. -/
theorem decFin_encFin (fuel : Int) (f : FinO)
    (hdt : dqT f.t) (hdf : dqTgd 2 ⟨f.tag, f.xs⟩ fuel)
    (hF : ((encFin f).toList.length : Int) ≤ fuel) :
    decFin fuel (encFin f) = .ok (f, (encFin f).toList.length) := by
  obtain ⟨ks, hk, hxs, hdq, hFt⟩ := hdf
  have hTL : ((encFin f).toList.toArray).toList = (encFin f).toList :=
    Array.toList_toArray _
  have hF' : (encFin f).toList =
      'F' :: ((encTy f.t).toList ++ (encTagged 2 ⟨f.tag, f.xs⟩).toList) := by
    show ("F" ++ encTy f.t ++ encTagged 2 ⟨f.tag, f.xs⟩).toList = _
    rw [toList_append, toList_append,
      show ("F" : String).toList = ['F'] from rfl,
      List.cons_append, List.nil_append, List.cons_append]
  have hEI : (encItems [0] [.ty f.t]).toList = (encTy f.t).toList := by
    show (encItem 0 (.ty f.t) ++ "").toList = _
    rw [encItem_0, toList_append,
      show ("" : String).toList = [] from rfl, List.append_nil]
  have h0 : charAt ((encFin f).toList.toArray) 0 = some 'F' :=
    charAt_head _ 0 'F' _ (by rw [hTL, List.drop_zero, hF'])
  have hd0 : (((encFin f).toList.toArray).toList).drop 1 =
      (encTy f.t).toList ++ (encTagged 2 ⟨f.tag, f.xs⟩).toList := by
    rw [hTL, hF']; rfl
  have hd : ((encFin f).toList.toArray).toList.drop 1 =
      (encItems [0] [.ty f.t]).toList ++ (encTagged 2 ⟨f.tag, f.xs⟩).toList := by
    rw [hEI]; exact hd0
  have hdq0 : dqItem 0 (.ty f.t) := Or.inl (Or.inl ⟨rfl, _, rfl, hdt⟩)
  have hdqa : ∀ pr ∈ [0].zip [.ty f.t], dqItem pr.1 pr.2 := by
    intro pr hm
    cases hm with
    | head => exact hdq0
    | tail _ hm => cases hm
  have hIF : ∀ pr ∈ [0].zip [.ty f.t], (itemFuel pr.1 pr.2 : Int) ≤ fuel := by
    intro pr hm
    cases hm with
    | head =>
      show (↑(tyFuel f.t + 1) : Int) ≤ fuel
      have h1 := tyFuel_le_encLen f.t
      have h2 : (encTy f.t).toList.length + 1 ≤ (encFin f).toList.length := by
        rw [hF', List.length_cons, List.length_append]; omega
      omega
    | tail _ hm => cases hm
  have hseq := decSeq_enc ((encFin f).toList.toArray) fuel
    (itemsGas [0] [.ty f.t]) [0] [.ty f.t]
    (gasFor fuel ((encFin f).toList.toArray).size) 1
    ((encTagged 2 ⟨f.tag, f.xs⟩).toList) hd rfl
    (by rw [Array.size_toArray]
        show (itemsGas [0] [.ty f.t] + 2 : Nat) ≤
          gasFor fuel (encFin f).toList.length
        have hi := itemsGas_le_encItems [0] [.ty f.t] hdqa
        rw [hEI] at hi
        have hle : (encFin f).toList.length ≤ fuel.toNat := by omega
        have h3 : (encTy f.t).toList.length ≤ (encFin f).toList.length := by
          rw [hF', List.length_cons, List.length_append]; omega
        unfold gasFor; omega)
    (decItemEnc_of_mem _ _ hdqa hIF)
  have hdrop : ((encFin f).toList.toArray).toList.drop
      (1 + (encTy f.t).toList.length) =
      (encTagged 2 ⟨f.tag, f.xs⟩).toList ++ [] := by
    have e1 := drop_append_advance (l := ((encFin f).toList.toArray).toList)
      (p := 0) (s := ['F']) (r := (encTy f.t).toList ++ (encTagged 2 ⟨f.tag, f.xs⟩).toList)
      (by rw [hTL, List.drop_zero, hF']; rfl)
    have e2 := drop_append_advance (l := ((encFin f).toList.toArray).toList)
      (p := 1) (s := (encTy f.t).toList) (r := (encTagged 2 ⟨f.tag, f.xs⟩).toList)
      (by rwa [show (0 : Nat) + ['F'].length = 1 from rfl] at e1)
    rw [List.append_nil]; exact e2
  have htag := decTagged_enc ((encFin f).toList.toArray) 2 fuel
    (gasFor fuel ((encFin f).toList.toArray).size)
    (1 + (encTy f.t).toList.length) ⟨f.tag, f.xs⟩ ks [] hk hxs hdq hdrop
    (by rw [Array.size_toArray]
        show (itemsGas ks f.xs + ks.length + 1 : Nat) ≤
          gasFor fuel (encFin f).toList.length
        have hi := itemsGas_le_encItems ks f.xs hdq
        obtain ⟨_, _, hkl⟩ := kindsOf_bounds hk
        have hle : (encFin f).toList.length ≤ fuel.toNat := by omega
        have h4 : (encItems ks f.xs).toList.length ≤
            (encTagged 2 ⟨f.tag, f.xs⟩).toList.length := by
          have h := encItems_le_encTagged 2 ⟨f.tag, f.xs⟩
          have hks : (kindsOf 2 f.tag).getD [] = ks := by
            simp only [hk, Option.getD_some]
          rwa [hks] at h
        have h5 : (encTagged 2 ⟨f.tag, f.xs⟩).toList.length ≤
            (encFin f).toList.length := by
          rw [hF', List.length_cons, List.length_append]; omega
        unfold gasFor; omega)
    (fun pr hm => by
      have h1 : itemFuel pr.1 pr.2 ≤ itemsFuel ks f.xs :=
        itemFuel_le_itemsFuel (kd := pr.1) (x := pr.2) hm
      have h2 := itemsFuel_le_encItems ks f.xs hdq
      have h4 : (encItems ks f.xs).toList.length ≤
          (encTagged 2 ⟨f.tag, f.xs⟩).toList.length := by
        have h := encItems_le_encTagged 2 ⟨f.tag, f.xs⟩
        have hks : (kindsOf 2 f.tag).getD [] = ks := by
          simp only [hk, Option.getD_some]
        rwa [hks] at h
      have h5 : (encTagged 2 ⟨f.tag, f.xs⟩).toList.length ≤
          (encFin f).toList.length := by
        rw [hF', List.length_cons, List.length_append]; omega
      have h6 : ((encFin f).toList.length : Int) ≤ fuel := hF
      have hTE : (encTagged 2 ⟨f.tag, f.xs⟩).toList.length =
          (encNat f.tag).toList.length + (encItems ks f.xs).toList.length := by
        show (encNat f.tag ++
            encItems ((kindsOf 2 f.tag).getD []) f.xs).toList.length = _
        rw [hk]
        simp only [Option.getD_some, toList_append, List.length_append]
      have hp := encNat_len_pos f.tag
      omega)
  unfold decFin
  dsimp only []
  rw [h0]
  dsimp only []
  rw [if_neg (by decide : ¬ ('F' : Char) ≠ 'F')]
  simp only [Bind.bind, Except.bind]
  rw [hseq]
  dsimp only []
  rw [hEI]
  rw [htag]
  dsimp only []
  show Except.ok (f, 1 + (encTy f.t).toList.length +
      (encTagged 2 ⟨f.tag, f.xs⟩).toList.length) =
    Except.ok (f, (encFin f).toList.length)
  rw [hF', List.length_cons, List.length_append]
  exact congrArg (fun x => Except.ok (f, x)) (by omega)

/-- `decCfg` acceptance premises: the type field, the embedded control
    object, the frame-list length bound, and per-frame tagged quality. -/
def dqCfgO (c : CfgO) (fuel : Int) : Prop :=
  dqT c.t ∧ dqTgd 0 c.ctl fuel ∧ (encTagged 0 c.ctl).length ≤ 1024 ∧
    c.k.length ≤ 1024 ∧
    ∀ fr ∈ c.k, dqTgd 1 fr fuel ∧ (encTagged 1 fr).length ≤ 1024

/-- `decCfg` reads `encCfg` back to the `CfgO` record. -/
theorem decCfg_encCfg (fuel : Int) (c : CfgO)
    (hdq : dqCfgO c fuel)
    (hF : ((encCfg c).toList.length : Int) ≤ fuel) :
    decCfg fuel (encCfg c) = .ok (c, (encCfg c).toList.length) := by
  obtain ⟨hdt, hctl, hcl, hklen, hf⟩ := hdq
  let XS : List Item := [.ty c.t, .str (encTagged 0 c.ctl),
    .list (c.k.map fun fr => Item.str (encTagged 1 fr))]
  have hTL : ((encCfg c).toList.toArray).toList = (encCfg c).toList :=
    Array.toList_toArray _
  have hC : (encCfg c).toList = 'C' ::
      ((encTy c.t).toList ++ ((encStr (encTagged 0 c.ctl)).toList ++
        ((encNat (↑c.k.length)).toList ++
          (String.join (c.k.map fun fr =>
            encStr (encTagged 1 fr))).toList))) := by
    show ("C" ++ encTy c.t ++ encStr (encTagged 0 c.ctl) ++
        encNat (↑c.k.length) ++
        String.join (c.k.map fun fr => encStr (encTagged 1 fr))).toList = _
    simp only [toList_append]
    rw [show ("C" : String).toList = ['C'] from rfl]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
  have hEIC : (encItems [0, 4, 14] XS).toList =
      (encTy c.t).toList ++ ((encStr (encTagged 0 c.ctl)).toList ++
        ((encNat (↑c.k.length)).toList ++
          (String.join (c.k.map fun fr =>
            encStr (encTagged 1 fr))).toList)) := by
    show (encItem 0 (.ty c.t) ++ (encItem 4 (.str (encTagged 0 c.ctl)) ++
        (encItem 14 (.list (c.k.map fun fr => Item.str (encTagged 1 fr))) ++
          ""))).toList = _
    rw [encItem_0, encItem_4, encItem_list 14 _ (by decide)]
    simp only [toList_append]
    rw [show ("" : String).toList = [] from rfl]
    simp only [List.append_nil, List.length_map, List.map_map]
    rw [show (encBase (14 - 10) ∘ fun fr => Item.str (encTagged 1 fr)) =
        (fun fr => encStr (encTagged 1 fr)) from rfl]
  have hdmem : ∀ y ∈ (c.k.map fun fr => Item.str (encTagged 1 fr)),
      dqElem 4 y := by
    intro y hy
    obtain ⟨fr, hfr, rfl⟩ := List.mem_map.1 hy
    exact Or.inr (Or.inr (Or.inr ⟨rfl, _, rfl, (hf fr hfr).2⟩))
  have hdqa : ∀ pr ∈ [0, 4, 14].zip XS, dqItem pr.1 pr.2 := by
    intro pr hm
    cases hm with
    | head => exact Or.inl (Or.inl ⟨rfl, _, rfl, hdt⟩)
    | tail _ hm =>
      cases hm with
      | head =>
        exact Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, _, rfl, hcl⟩)))
      | tail _ hm =>
        cases hm with
        | head =>
          show dqItem 14 (.list (c.k.map fun fr => Item.str (encTagged 1 fr)))
          exact Or.inr (Or.inr ⟨by decide, _, rfl,
            by rw [List.length_map]; exact hklen, hdmem⟩)
        | tail _ hm => cases hm
  have hIF : ∀ pr ∈ [0, 4, 14].zip XS, (itemFuel pr.1 pr.2 : Int) ≤ fuel := by
    intro pr hm
    cases hm with
    | head =>
      show (↑(tyFuel c.t + 1) : Int) ≤ fuel
      have h1 := tyFuel_le_encLen c.t
      have h2 : (encTy c.t).toList.length + 1 ≤ (encCfg c).toList.length := by
        rw [hC, List.length_cons]; simp only [List.length_append]; omega
      omega
    | tail _ hm =>
      cases hm with
      | head =>
        show (1 : Int) ≤ fuel
        have h1c : 1 ≤ (encCfg c).toList.length := by
          rw [hC, List.length_cons]; omega
        omega
      | tail _ hm =>
        cases hm with
        | head =>
          show (↑(elemsFuel (c.k.map fun fr => Item.str (encTagged 1 fr)) +
              1) : Int) ≤ fuel
          have hef := elemsFuel_le_catEnc _ hdmem
          have hcat : (catEnc (encBase 4)
                (c.k.map fun fr => Item.str (encTagged 1 fr))).toList.length =
              (String.join (c.k.map fun fr =>
                encStr (encTagged 1 fr))).toList.length := by
            unfold catEnc
            congr 1
            rw [List.map_map]; rfl
          have hJL : (String.join (c.k.map fun fr =>
                encStr (encTagged 1 fr))).toList.length + 1 ≤
              (encCfg c).toList.length := by
            rw [hC, List.length_cons]
            simp only [List.length_append]; omega
          omega
        | tail _ hm => cases hm
  have hd : ((encCfg c).toList.toArray).toList.drop 1 =
      (encItems [0, 4, 14] XS).toList ++ [] := by
    rw [List.append_nil, hEIC, hTL, hC]; rfl
  have hseq := decSeq_enc ((encCfg c).toList.toArray) fuel
    (itemsGas [0, 4, 14] XS) [0, 4, 14] XS
    (gasFor fuel ((encCfg c).toList.toArray).size) 1
    [] hd rfl
    (by rw [Array.size_toArray]
        show (itemsGas [0, 4, 14] XS + 4 : Nat) ≤
          gasFor fuel (encCfg c).toList.length
        have hi := itemsGas_le_encItems [0, 4, 14] XS hdqa
        rw [hEIC] at hi
        have hle : (encCfg c).toList.length ≤ fuel.toNat := by omega
        have h3 : ((encTy c.t).toList ++
            ((encStr (encTagged 0 c.ctl)).toList ++
            ((encNat (↑c.k.length)).toList ++
              (String.join (c.k.map fun fr =>
                encStr (encTagged 1 fr))).toList))).length ≤
            (encCfg c).toList.length := by
          rw [hC, List.length_cons]; omega
        unfold gasFor; omega)
    (decItemEnc_of_mem _ _ hdqa hIF)
  have h0 : charAt ((encCfg c).toList.toArray) 0 = some 'C' :=
    charAt_head _ 0 'C' _ (by rw [hTL, List.drop_zero, hC])
  unfold decCfg
  dsimp only []
  rw [h0]
  dsimp only []
  rw [if_neg (by decide : ¬ ('C' : Char) ≠ 'C')]
  simp only [Bind.bind, Except.bind]
  rw [hseq]
  dsimp only []
  rw [show asStr ((XS.drop 1).headD default) = encTagged 0 c.ctl from rfl]
  rw [decTaggedStr_of_dq hctl]
  try simp only [Except.bind]
  try dsimp only []
  rw [show (asList ((XS.drop 2).headD default)).map asStr =
      c.k.map (encTagged 1) from by
    show ((c.k.map fun fr => Item.str (encTagged 1 fr)).map asStr) = _
    rw [List.map_map]; rfl]
  rw [mapM_decTaggedStr fuel c.k (fun fr hfr => (hf fr hfr).1)]
  show Except.ok (c, 1 + (encItems [0, 4, 14] XS).toList.length) =
    Except.ok (c, (encCfg c).toList.length)
  have hL : (encItems [0, 4, 14] XS).toList.length =
      ((encTy c.t).toList ++ ((encStr (encTagged 0 c.ctl)).toList ++
        ((encNat (↑c.k.length)).toList ++
          (String.join (c.k.map fun fr =>
            encStr (encTagged 1 fr))).toList))).length :=
    congrArg List.length hEIC
  rw [hL, hC, List.length_cons, Nat.add_comm 1]

/-- `decFin` acceptance premises. -/
def dqFinO (f : FinO) (fuel : Int) : Prop :=
  dqT f.t ∧ dqTgd 2 ⟨f.tag, f.xs⟩ fuel

theorem decFin_of_dq (fuel : Int) (f : FinO) (h : dqFinO f fuel)
    (hF : ((encFin f).toList.length : Int) ≤ fuel) :
    decFin fuel (encFin f) = .ok (f, (encFin f).toList.length) :=
  decFin_encFin fuel f h.1 h.2 hF

/-- `cxDec` acceptance premises: for a run wrapper the member is a final
    outcome (`tag = 0`) or a configuration (`tag = 1`), decoded at
    `fuel - 1`. -/
def dqCX : CX → Int → Prop
  | .cfg c, fuel =>
    dqCfgO c fuel ∧ ((encCfg c).toList.length : Int) ≤ fuel
  | .fin f, fuel =>
    dqFinO f fuel ∧ ((encFin f).toList.length : Int) ≤ fuel
  | .run tag m, fuel =>
    0 ≤ tag ∧ inI64 tag ∧
    (match m with
      | .cfg cf => tag = 1 ∧ dqCfgO cf (fuel - 1) ∧
          (encCfg cf).length ≤ 1024 ∧
          ((encCfg cf).toList.length : Int) ≤ fuel - 1
      | .fin fr => tag = 0 ∧ dqFinO fr (fuel - 1) ∧
          (encFin fr).length ≤ 1024 ∧
          ((encFin fr).toList.length : Int) ≤ fuel - 1
      | .run _ _ => False)

/-- `cxDec` reads `cxEnc` back: kind 22 configuration, 23 final outcome,
    otherwise a run wrapper whose member is a C or F object. -/
theorem cxDec_cxEnc (kind : Int) (x : CX) (fuel : Int) (hdq : dqCX x fuel)
    (hk : match x with
      | .cfg _ => kind = 22
      | .fin _ => kind = 23
      | .run _ _ => kind ≠ 22 ∧ kind ≠ 23) :
    cxDec kind (cxEnc x) fuel = .ok (x, (cxEnc x).toList.length) := by
  cases x with
  | cfg c =>
    obtain ⟨hdqc, hFc⟩ := hdq
    subst hk
    have hC : (encCfg c).toList = 'C' ::
        ((encTy c.t).toList ++ ((encStr (encTagged 0 c.ctl)).toList ++
          ((encNat (↑c.k.length)).toList ++
            (String.join (c.k.map fun fr =>
              encStr (encTagged 1 fr))).toList))) := by
      show ("C" ++ encTy c.t ++ encStr (encTagged 0 c.ctl) ++
          encNat (↑c.k.length) ++
          String.join (c.k.map fun fr => encStr (encTagged 1 fr))).toList = _
      simp only [toList_append]
      rw [show ("C" : String).toList = ['C'] from rfl]
      simp only [List.cons_append, List.nil_append, List.append_assoc]
    have hD : (cxEnc (.cfg c)).toList = 'C' ::
        ((encTy c.t).toList ++ ((encStr (encTagged 0 c.ctl)).toList ++
          ((encNat (↑c.k.length)).toList ++
            (String.join (c.k.map fun fr =>
              encStr (encTagged 1 fr))).toList))) := hC
    have h0 : charAt ((cxEnc (.cfg c)).toList.toArray) 0 = some 'C' :=
      charAt_head _ 0 'C' _ (by
        rw [Array.toList_toArray, List.drop_zero, hD])
    unfold cxDec
    dsimp only []
    rw [h0]
    dsimp only []
    rw [if_pos rfl]
    rw [show cxEnc (.cfg c) = encCfg c from rfl, decCfg_encCfg fuel c hdqc hFc]
    rfl
  | fin f =>
    obtain ⟨hdf, hFf⟩ := hdq
    subst hk
    have h0 : charAt ((cxEnc (.fin f)).toList.toArray) 0 = some 'F' :=
      charAt_head _ 0 'F' _ (by
        rw [Array.toList_toArray, List.drop_zero]
        show (encFin f).toList = 'F' ::
            ((encTy f.t).toList ++ (encTagged 2 ⟨f.tag, f.xs⟩).toList)
        show ("F" ++ encTy f.t ++ encTagged 2 ⟨f.tag, f.xs⟩).toList = _
        simp only [toList_append]
        rw [show ("F" : String).toList = ['F'] from rfl]
        simp only [List.cons_append, List.nil_append])
    unfold cxDec
    dsimp only []
    rw [h0]
    dsimp only []
    rw [if_neg (by omega : ¬ (23 : Int) = 22), if_pos rfl]
    rw [show cxEnc (.fin f) = encFin f from rfl,
      decFin_of_dq fuel f hdf hFf]
    rfl
  | run tag m =>
    obtain ⟨h0t, hin, hm⟩ := hdq
    obtain ⟨h22, h23⟩ := hk
    cases m with
    | run _ _ => exact hm.elim
    | cfg cf =>
      obtain ⟨h1, hdqc, hmbl, hFc⟩ := hm
      subst h1
      have hD : (cxEnc (.run 1 (.cfg cf))).toList = 'D' ::
          ((encNat 1).toList ++ (encStr (encCfg cf)).toList) := by
        show ("D" ++ encNat 1 ++ encStr (encCfg cf)).toList = _
        simp only [toList_append]
        rw [show ("D" : String).toList = ['D'] from rfl]
        simp only [List.cons_append, List.nil_append, List.append_assoc]
      have hEI : (encItems [5, 4] [.num 1, .str (encCfg cf)]).toList =
          (encNat 1).toList ++ (encStr (encCfg cf)).toList := by
        show (encItem 5 (.num 1) ++
            (encItem 4 (.str (encCfg cf)) ++ "")).toList = _
        rw [encItem_5, encItem_4]
        simp only [toList_append]
        rw [show ("" : String).toList = [] from rfl, List.append_nil]
      have hTL : ((cxEnc (.run 1 (.cfg cf))).toList.toArray).toList =
          (cxEnc (.run 1 (.cfg cf))).toList := Array.toList_toArray _
      have hdqa : ∀ pr ∈ [5, 4].zip [.num (1 : Int), .str (encCfg cf)],
          dqItem pr.1 pr.2 := by
        intro pr hm
        cases hm with
        | head => exact Or.inr (Or.inl ⟨rfl, _, rfl, h0t, hin⟩)
        | tail _ hm =>
          cases hm with
          | head =>
            exact Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, _, rfl, hmbl⟩)))
          | tail _ hm => cases hm
      have hIF : ∀ pr ∈ [5, 4].zip [.num (1 : Int), .str (encCfg cf)],
          (itemFuel pr.1 pr.2 : Int) ≤ fuel := by
        intro pr hm
        cases hm with
        | head => show (0 : Int) ≤ fuel; omega
        | tail _ hm =>
          cases hm with
          | head => show (1 : Int) ≤ fuel; omega
          | tail _ hm => cases hm
      have hd : ((cxEnc (.run 1 (.cfg cf))).toList.toArray).toList.drop 1 =
          (encItems [5, 4] [.num 1, .str (encCfg cf)]).toList ++ [] := by
        rw [List.append_nil, hEI, hTL, hD]; rfl
      have hseq := decSeq_enc ((cxEnc (.run 1 (.cfg cf))).toList.toArray) fuel
        (itemsGas [5, 4] [.num (1 : Int), .str (encCfg cf)]) [5, 4]
        [.num (1 : Int), .str (encCfg cf)]
        (gasFor fuel ((cxEnc (.run 1 (.cfg cf))).toList.toArray).size) 1
        [] hd rfl
        (by rw [Array.size_toArray]
            show 4 ≤ gasFor fuel ((cxEnc (.run 1 (.cfg cf))).toList.length)
            unfold gasFor; omega)
        (decItemEnc_of_mem _ _ hdqa hIF)
      have h0 : charAt ((cxEnc (.run 1 (.cfg cf))).toList.toArray) 0 =
          some 'D' :=
        charAt_head _ 0 'D' _ (by rw [hTL, List.drop_zero, hD])
      unfold cxDec
      dsimp only []
      rw [h0]
      dsimp only []
      rw [if_neg h22, if_neg h23,
        if_neg (by decide : ¬ ('D' : Char) ≠ 'D')]
      simp only [Bind.bind, Except.bind]
      rw [hseq]
      dsimp only []
      rw [show asNum (List.headD [.num (1 : Int), .str (encCfg cf)] default) =
          (1 : Int) from rfl]
      rw [if_pos (by decide : (1 : Int) < 2)]
      rw [show asStr (List.headD
          (List.drop 1 [.num (1 : Int), .str (encCfg cf)]) default) =
          encCfg cf from rfl]
      rw [if_neg (by decide : ¬ (1 : Int) = 0)]
      rw [decCfg_encCfg (fuel - 1) cf hdqc hFc]
      dsimp only []
      show Except.ok (CX.run 1 (CX.cfg cf),
          1 + (encItems [5, 4] [.num (1 : Int),
            .str (encCfg cf)]).toList.length) =
        Except.ok (CX.run 1 (CX.cfg cf),
          (cxEnc (.run 1 (.cfg cf))).toList.length)
      rw [hEI, hD, List.length_cons, List.length_append, Nat.add_comm 1]
    | fin fr =>
      obtain ⟨h0', hdf, hmbl, hFf⟩ := hm
      subst h0'
      have hD : (cxEnc (.run 0 (.fin fr))).toList = 'D' ::
          ((encNat 0).toList ++ (encStr (encFin fr)).toList) := by
        show ("D" ++ encNat 0 ++ encStr (encFin fr)).toList = _
        simp only [toList_append]
        rw [show ("D" : String).toList = ['D'] from rfl]
        simp only [List.cons_append, List.nil_append, List.append_assoc]
      have hEI : (encItems [5, 4] [.num 0, .str (encFin fr)]).toList =
          (encNat 0).toList ++ (encStr (encFin fr)).toList := by
        show (encItem 5 (.num 0) ++
            (encItem 4 (.str (encFin fr)) ++ "")).toList = _
        rw [encItem_5, encItem_4]
        simp only [toList_append]
        rw [show ("" : String).toList = [] from rfl, List.append_nil]
      have hTL : ((cxEnc (.run 0 (.fin fr))).toList.toArray).toList =
          (cxEnc (.run 0 (.fin fr))).toList := Array.toList_toArray _
      have hdqa : ∀ pr ∈ [5, 4].zip [.num (0 : Int), .str (encFin fr)],
          dqItem pr.1 pr.2 := by
        intro pr hm
        cases hm with
        | head => exact Or.inr (Or.inl ⟨rfl, _, rfl, h0t, hin⟩)
        | tail _ hm =>
          cases hm with
          | head =>
            exact Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, _, rfl, hmbl⟩)))
          | tail _ hm => cases hm
      have hIF : ∀ pr ∈ [5, 4].zip [.num (0 : Int), .str (encFin fr)],
          (itemFuel pr.1 pr.2 : Int) ≤ fuel := by
        intro pr hm
        cases hm with
        | head => show (0 : Int) ≤ fuel; omega
        | tail _ hm =>
          cases hm with
          | head => show (1 : Int) ≤ fuel; omega
          | tail _ hm => cases hm
      have hd : ((cxEnc (.run 0 (.fin fr))).toList.toArray).toList.drop 1 =
          (encItems [5, 4] [.num 0, .str (encFin fr)]).toList ++ [] := by
        rw [List.append_nil, hEI, hTL, hD]; rfl
      have hseq := decSeq_enc ((cxEnc (.run 0 (.fin fr))).toList.toArray) fuel
        (itemsGas [5, 4] [.num (0 : Int), .str (encFin fr)]) [5, 4]
        [.num (0 : Int), .str (encFin fr)]
        (gasFor fuel ((cxEnc (.run 0 (.fin fr))).toList.toArray).size) 1
        [] hd rfl
        (by rw [Array.size_toArray]
            show 4 ≤ gasFor fuel ((cxEnc (.run 0 (.fin fr))).toList.length)
            unfold gasFor; omega)
        (decItemEnc_of_mem _ _ hdqa hIF)
      have h0 : charAt ((cxEnc (.run 0 (.fin fr))).toList.toArray) 0 =
          some 'D' :=
        charAt_head _ 0 'D' _ (by rw [hTL, List.drop_zero, hD])
      unfold cxDec
      dsimp only []
      rw [h0]
      dsimp only []
      rw [if_neg h22, if_neg h23,
        if_neg (by decide : ¬ ('D' : Char) ≠ 'D')]
      simp only [Bind.bind, Except.bind]
      rw [hseq]
      dsimp only []
      rw [show asNum (List.headD [.num (0 : Int), .str (encFin fr)] default) =
          (0 : Int) from rfl]
      rw [if_pos (by decide : (0 : Int) < 2)]
      rw [show asStr (List.headD
          (List.drop 1 [.num (0 : Int), .str (encFin fr)]) default) =
          encFin fr from rfl]
      rw [if_pos rfl]
      rw [decFin_of_dq (fuel - 1) fr hdf hFf]
      dsimp only []
      show Except.ok (CX.run 0 (CX.fin fr),
          1 + (encItems [5, 4] [.num (0 : Int),
            .str (encFin fr)]).toList.length) =
        Except.ok (CX.run 0 (CX.fin fr),
          (cxEnc (.run 0 (.fin fr))).toList.length)
      rw [hEI, hD, List.length_cons, List.length_append]
      exact congrArg (fun x => Except.ok (CX.run 0 (CX.fin fr), x)) (by omega)

/-! ## Bound and fuel refusals (SCM-011) -/

/-- Decode-fuel exhaustion is refusal, never truncation: at the kind
    dispatcher, negative carrier fuel is refused `[rcic_scm_wire_fuel]`
    before any byte is read. `scm_wire_dec` is the only fuel test
    (06 §17); every element decode recurs at `fuel - 1`, so exhaustion
    surfaces here. -/
theorem scm_wire_dec_fuel_refuse {cs : Array Char} {g kind : Nat} {fuel : Int}
    {p : Nat} :
    fuel < 0 → dec cs (g + 1) kind fuel p = .error "[rcic_scm_wire_fuel]" := by
  intro h; unfold dec; rw [if_pos h]; rfl

/-- The 1024-element bound refuses rather than truncates: while the counted
    list still owes elements (`0 < left`) an exhausted loop budget
    (`iters = 0`, the carrier's 1024-step `fix` spent) is refused
    `[rcic_scm_wire_bound]`. The accepted direction is
    `wire_decElems_length_le` (`xs.length ≤ iters`); together both
    directions of the element bound are decided. -/
theorem scm_wire_decElems_bound_refuse {cs : Array Char} {g kind : Nat}
    {fuel left : Int} {p : Nat} :
    0 < left →
    decElems cs (g + 1) kind fuel left p 0 = .error "[rcic_scm_wire_bound]" := by
  intro h; unfold decElems; rw [if_neg (by omega : ¬ left ≤ 0)]; rfl

end Rcic.Scm.Wire
