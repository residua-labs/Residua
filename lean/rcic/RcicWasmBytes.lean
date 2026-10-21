/-
Canonical self-delimiting byte codec used by `ValRep` and
`SCMOutcomeEnvelope-v1` (`RcicWasmOutcome`).

Numbers are unsigned LEB128. The terminating byte is nonzero whenever a
continuation byte preceded it, so an overlong encoding is not a second
encoding of the same number. `closure_claim` stays 0.
-/

def encNat (n : Nat) : List UInt8 :=
  if h : n < 128 then
    [UInt8.ofNat n]
  else
    UInt8.ofNat (n % 128 + 128) :: encNat (n / 128)
termination_by n
decreasing_by
  have hle : 128 ≤ n := Nat.not_lt.mp h
  exact Nat.div_lt_self (Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 128) hle) (by decide)

set_option linter.unusedVariables false in
def decNatGo (acc mul : Nat) (started : Bool) : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
    if hv : b.toNat < 128 then
      if hs : started = true then
        if hz : b.toNat = 0 then none
        else some (acc + b.toNat * mul, rest)
      else some (acc + b.toNat * mul, rest)
    else
      decNatGo (acc + (b.toNat - 128) * mul) (mul * 128) true rest

def decNat (bs : List UInt8) : Option (Nat × List UInt8) :=
  decNatGo 0 1 false bs

private theorem uint8_toNat_ofNat {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n :=
  UInt8.toNat_ofNat_of_lt h

private theorem uint8_ofNat_toNat (a : UInt8) : UInt8.ofNat a.toNat = a :=
  UInt8.toNat.inj (UInt8.toNat_ofNat_of_lt a.toNat_lt_size)

private theorem encNat_mod_lt (n : Nat) : n % 128 + 128 < 256 := by
  have hm : n % 128 < 128 := Nat.mod_lt n (by decide)
  omega

private theorem encNat_of_lt (n : Nat) (h : n < 128) : encNat n = [UInt8.ofNat n] := by
  unfold encNat; simp [h]

private theorem encNat_of_ge (n : Nat) (h : ¬ n < 128) :
    encNat n = UInt8.ofNat (n % 128 + 128) :: encNat (n / 128) := by
  rw [encNat, dif_neg h]

private theorem leb_arith (q n mul : Nat) :
    q * mul + n * (mul * 128) = (q + 128 * n) * mul := by
  calc
    q * mul + n * (mul * 128)
        = q * mul + n * (128 * mul) := by rw [Nat.mul_comm mul 128]
    _ = q * mul + (n * 128) * mul := by rw [Nat.mul_assoc]
    _ = (q + n * 128) * mul := by exact (Nat.add_mul q (n * 128) mul).symm
    _ = (q + 128 * n) * mul := by rw [Nat.mul_comm n 128]

private theorem decGo_enc (n acc mul : Nat) (rest : List UInt8) (started : Bool)
    (hstart : started = true → n ≠ 0) (hmul : 0 < mul) :
    decNatGo acc mul started (encNat n ++ rest) = some (acc + n * mul, rest) := by
  induction n using Nat.strongRecOn generalizing acc mul rest started with
  | ind n ih =>
    by_cases hlt : n < 128
    · rw [encNat_of_lt n hlt]
      have hvn : (UInt8.ofNat n).toNat = n :=
        uint8_toNat_ofNat (Nat.lt_trans hlt (by decide))
      simp only [List.singleton_append, decNatGo, hvn, hlt]
      by_cases hs : started = true
      · have hnz : n ≠ 0 := hstart hs
        simp [hs, hnz]
      · simp [hs]
    · rw [encNat_of_ge n hlt]
      have hb : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 :=
        uint8_toNat_ofNat (encNat_mod_lt n)
      have hnot : ¬ (UInt8.ofNat (n % 128 + 128)).toNat < 128 := by
        rw [hb]; omega
      simp only [List.cons_append, decNatGo]
      rw [dif_neg hnot, hb]
      have hdiv : n / 128 < n := by
        have hle : 128 ≤ n := Nat.not_lt.mp hlt
        exact Nat.div_lt_self (Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 128) hle) (by decide)
      have hpos : n / 128 ≠ 0 := by
        have hle : 128 ≤ n := Nat.not_lt.mp hlt
        have hone : 1 ≤ n / 128 := (Nat.le_div_iff_mul_le (by decide)).2 hle
        omega
      have ih' := ih (n / 128) hdiv (acc + (n % 128) * mul) (mul * 128) rest true
        (fun _ => hpos) (Nat.mul_pos hmul (by decide))
      have hcall : decNatGo (acc + ((n % 128 + 128) - 128) * mul) (mul * 128) true
          (encNat (n / 128) ++ rest) =
          decNatGo (acc + (n % 128) * mul) (mul * 128) true (encNat (n / 128) ++ rest) := by
        have : (n % 128 + 128) - 128 = n % 128 := by omega
        simp [this]
      have happ : (encNat (n / 128)).append rest = encNat (n / 128) ++ rest := rfl
      rw [happ, hcall, ih']
      have harith : (n % 128) * mul + (n / 128) * (mul * 128) = n * mul := by
        rw [leb_arith (n % 128) (n / 128) mul]
        have h3 : (n % 128) + 128 * (n / 128) = n := Nat.mod_add_div n 128
        rw [h3]
      rw [Nat.add_assoc, harith]

/-- `decNat` reads `encNat` and leaves the suffix. -/
theorem decNat_enc (n : Nat) (rest : List UInt8) :
    decNat (encNat n ++ rest) = some (n, rest) := by
  simpa [decNat] using decGo_enc n 0 1 rest false (by intro h; cases h) (by decide)

private theorem decGo_canonical (acc mul : Nat) (started : Bool) (bs : List UInt8)
    (hmul : 0 < mul) {val rest}
    (h : decNatGo acc mul started bs = some (val, rest)) :
    ∃ n pre, bs = pre ++ rest ∧ val = acc + n * mul ∧ pre = encNat n ∧
      (started = true → n ≠ 0) := by
  induction bs generalizing acc mul started with
  | nil => simp [decNatGo] at h
  | cons b bs ih =>
    unfold decNatGo at h
    split at h
    · rename_i hv
      split at h
      · rename_i hs
        split at h
        · cases h
        · rename_i hz
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hval, hrest⟩ := h
          subst hrest
          refine ⟨b.toNat, [b], rfl, hval.symm, ?_, ?_⟩
          · rw [encNat_of_lt b.toNat hv]
            exact congrArg (fun x => [x]) (uint8_ofNat_toNat b).symm
          · intro _; exact hz
      · rename_i hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hval, hrest⟩ := h
        subst hrest
        refine ⟨b.toNat, [b], rfl, hval.symm, ?_, ?_⟩
        · rw [encNat_of_lt b.toNat hv]
          exact congrArg (fun x => [x]) (uint8_ofNat_toNat b).symm
        · intro hs'; exact absurd hs' hs
    · rename_i hv
      have hmul' : 0 < mul * 128 := Nat.mul_pos hmul (by decide)
      obtain ⟨n, pre, hbs, hval, hpre, hpos⟩ :=
        ih (acc + (b.toNat - 128) * mul) (mul * 128) true hmul' h
      have hn0 : n ≠ 0 := hpos rfl
      have hvge : 128 ≤ b.toNat := Nat.not_lt.mp hv
      have hq : b.toNat - 128 < 128 := by
        have hsz : b.toNat < 256 := b.toNat_lt_size
        have hcancel : (b.toNat - 128) + 128 = b.toNat := Nat.sub_add_cancel hvge
        have : (b.toNat - 128) + 128 < 128 + 128 := by
          rw [hcancel]; simpa using hsz
        exact Nat.lt_of_add_lt_add_right this
      refine ⟨(b.toNat - 128) + 128 * n, b :: pre, ?_, ?_, ?_, ?_⟩
      · simp [hbs]
      · rw [hval, Nat.add_assoc, leb_arith (b.toNat - 128) n mul]
      · have hbig : ¬ (b.toNat - 128) + 128 * n < 128 := by
          have h1 : 0 < n := Nat.pos_of_ne_zero hn0
          have hmuln : 128 * 1 ≤ 128 * n := Nat.mul_le_mul_left 128 h1
          have : 128 ≤ (b.toNat - 128) + 128 * n :=
            Nat.le_trans (by simpa using hmuln) (Nat.le_add_left (128 * n) (b.toNat - 128))
          exact Nat.not_lt.mpr this
        rw [encNat_of_ge ((b.toNat - 128) + 128 * n) hbig]
        have hdiv : ((b.toNat - 128) + 128 * n) / 128 = n := by
          rw [Nat.add_mul_div_left (b.toNat - 128) n (by decide)]
          simp [Nat.div_eq_of_lt hq]
        have hmod : ((b.toNat - 128) + 128 * n) % 128 = b.toNat - 128 := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]
        rw [hdiv, hmod, Nat.sub_add_cancel hvge, uint8_ofNat_toNat b, hpre]
      · intro _
        have h1 : 0 < n := Nat.pos_of_ne_zero hn0
        have : 0 < 128 * n := Nat.mul_pos (by decide) h1
        omega

/-- A successful `decNat` consumed exactly `encNat` of the value it read. -/
theorem decNat_canonical {bs : List UInt8} {n : Nat} {rest : List UInt8}
    (h : decNat bs = some (n, rest)) :
    ∃ pre, bs = pre ++ rest ∧ pre = encNat n := by
  have hgo : decNatGo 0 1 false bs = some (n, rest) := h
  obtain ⟨k, pre, hbs, hval, hpre, _⟩ := decGo_canonical 0 1 false bs (by decide) hgo
  have hk : k = n := by
    have : n = 0 + k * 1 := hval
    omega
  exact ⟨pre, hbs, hk ▸ hpre⟩

/-! ## Int. Sign byte 0 is nonnegative; sign byte 1 is a positive magnitude. -/

def encInt (n : Int) : List UInt8 :=
  match n with
  | Int.ofNat k => (0 : UInt8) :: encNat k
  | Int.negSucc k => (1 : UInt8) :: encNat (k + 1)

def decInt : List UInt8 → Option (Int × List UInt8)
  | [] => none
  | b :: rest =>
    if b = 0 then
      match decNat rest with
      | some (k, rest') => some (Int.ofNat k, rest')
      | none => none
    else if b = 1 then
      match decNat rest with
      | some (k, rest') =>
        if k = 0 then none else some (Int.negSucc (k - 1), rest')
      | none => none
    else none

theorem decInt_enc (n : Int) (rest : List UInt8) :
    decInt (encInt n ++ rest) = some (n, rest) := by
  cases n with
  | ofNat k =>
    rw [encInt]
    simp only [List.cons_append, decInt, decNat_enc]
    rfl
  | negSucc k =>
    rw [encInt]
    simp only [List.cons_append, decInt, decNat_enc]
    have hk : ¬ k + 1 = 0 := by omega
    simp [hk, Nat.add_sub_cancel]

theorem decInt_canonical {bs : List UInt8} {n : Int} {rest : List UInt8}
    (h : decInt bs = some (n, rest)) :
    ∃ pre, bs = pre ++ rest ∧ pre = encInt n := by
  cases bs with
  | nil => simp [decInt] at h
  | cons b tail =>
    simp [decInt] at h
    split at h
    · rename_i hb
      cases hdec : decNat tail with
      | none => simp [hdec] at h
      | some p =>
        obtain ⟨k, rest'⟩ := p
        simp [hdec] at h
        obtain ⟨hn, hr⟩ := h
        subst hn hr
        obtain ⟨pre, htail, hpre⟩ := decNat_canonical hdec
        refine ⟨(0 : UInt8) :: pre, ?_, ?_⟩
        · simp [htail, hb]
        · simp [encInt, hpre]
    · split at h
      · rename_i hb0 hb1
        cases hdec : decNat tail with
        | none => simp [hdec] at h
        | some p =>
          obtain ⟨k, rest'⟩ := p
          simp [hdec] at h
          obtain ⟨hk, hn, hr⟩ := h
          subst hr
          obtain ⟨pre, htail, hpre⟩ := decNat_canonical hdec
          have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.pos_of_ne_zero hk)
          refine ⟨(1 : UInt8) :: pre, ?_, ?_⟩
          · simp [htail, hb1]
          · have hn' : n = Int.negSucc (k - 1) := hn.symm
            simp [encInt, hn', hpre, hk1]
      · cases h

/-! ## Strings. A count of Unicode scalar values, each scalar in canonical
LEB128. Surrogate code units are not scalars, so they are refused. -/

private theorem char_toNat_ofNat (n : Nat) (h : n.isValidChar) :
    (Char.ofNat n).toNat = n := by
  unfold Char.ofNat Char.toNat Char.ofNatAux
  rw [dif_pos h]
  rfl

private theorem char_valid (c : Char) : c.toNat.isValidChar := by
  unfold Char.toNat
  exact c.valid

def encChars : List Char → List UInt8
  | [] => []
  | c :: cs => encNat c.toNat ++ encChars cs

set_option linter.unusedVariables false in
def decChars : Nat → List UInt8 → Option (List Char × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match decNat bs with
    | none => none
    | some (k, rest) =>
      if hk : k.isValidChar then
        match decChars n rest with
        | some (cs, rest') => some (Char.ofNat k :: cs, rest')
        | none => none
      else none

theorem decChars_enc (cs : List Char) (rest : List UInt8) :
    decChars cs.length (encChars cs ++ rest) = some (cs, rest) := by
  induction cs generalizing rest with
  | nil => simp [encChars, decChars]
  | cons c cs ih =>
    simp only [List.length_cons, Nat.succ_eq_add_one, encChars, List.append_assoc,
      decChars, decNat_enc, char_valid, dif_pos, Char.ofNat_toNat, ih]

def encStr (s : String) : List UInt8 :=
  encNat s.data.length ++ encChars s.data

def decStr (bs : List UInt8) : Option (String × List UInt8) :=
  match decNat bs with
  | none => none
  | some (n, rest) =>
    match decChars n rest with
    | some (cs, rest') => some (String.mk cs, rest')
    | none => none

theorem decStr_enc (s : String) (rest : List UInt8) :
    decStr (encStr s ++ rest) = some (s, rest) := by
  simp only [encStr, List.append_assoc, decStr, decNat_enc, decChars_enc, String.ext rfl]

theorem decChars_canonical {n : Nat} {bs rest : List UInt8} {cs : List Char}
    (h : decChars n bs = some (cs, rest)) :
    cs.length = n ∧ ∃ pre, bs = pre ++ rest ∧ pre = encChars cs := by
  induction n generalizing bs cs rest with
  | zero =>
    simp [decChars] at h
    obtain ⟨hcs, hr⟩ := h
    subst hcs hr
    exact ⟨rfl, [], by simp [encChars]⟩
  | succ n ih =>
    unfold decChars at h
    cases hdec : decNat bs with
    | none => simp [hdec] at h
    | some p =>
      obtain ⟨k, mid⟩ := p
      rw [hdec] at h
      by_cases hk : k.isValidChar
      · simp [hk] at h
        cases hrec : decChars n mid with
        | none => simp [hrec] at h
        | some q =>
          obtain ⟨cs0, rest0⟩ := q
          rw [hrec] at h
          simp [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hcs, hr⟩ := h
          subst hcs hr
          obtain ⟨hlen, pre, hmid, hpre⟩ := ih hrec
          obtain ⟨plen, hbs, hplen⟩ := decNat_canonical hdec
          refine ⟨by simp [hlen], plen ++ pre, ?_, ?_⟩
          · simp [hbs, hmid]
          · simp [encChars, hplen, hpre, char_toNat_ofNat k hk]
      · simp [hk] at h

theorem decStr_canonical {bs rest : List UInt8} {s : String}
    (h : decStr bs = some (s, rest)) :
    ∃ pre, bs = pre ++ rest ∧ pre = encStr s := by
  simp [decStr] at h
  split at h
  · cases h
  · rename_i n mid hdec
    split at h
    · rename_i chars suff heq
      simp [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs, hr⟩ := h
      subst hr
      obtain ⟨hlen, pre, hmid, hpre⟩ := decChars_canonical heq
      obtain ⟨plen, hbs, hplen⟩ := decNat_canonical hdec
      have hdata : s.data = chars := by
        rw [hs.symm]
      refine ⟨plen ++ pre, ?_, ?_⟩
      · simp [hbs, hmid]
      · simp [encStr, hplen, hpre, hlen, hdata]
    · cases h
