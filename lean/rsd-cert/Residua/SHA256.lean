/-!
# SHA-256 in pure Lean 4 (no Mathlib)

A concrete, computable SHA-256 used by the slot_eval runtime oracle for
`Expr.contentHash` (#1653 carve 1). This is a RUNTIME hash (the exe computes
the exact digest the wasm engine produces), NOT a theorem-grade model — the
repo's cryptographic-collision stance lives in `Residua.Exe.ContentHash.lean`
(`opaque sha256_hex`). Nothing here is proven about collision-resistance; the
function is trusted lowering, exactly like the rest of the compiled evaluator.

Standard FIPS 180-4. Verified locally against the known-answer vectors
`sha256("") = e3b0c4...`, `sha256("abc") = ba7816bf...`, and against the wasm
engine's `contentHash(42) = sha256("Num(float:42.0)")`.
-/

namespace Residua.SHA256

/-- Rotate right by `n` (UInt32 shift amount). -/
def rotr (n : UInt32) (x : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< ((32 : UInt32) - n))

/-- Schedule σ0. -/
def s0 (x : UInt32) : UInt32 := rotr 7 x ^^^ rotr 18 x ^^^ (x >>> (3 : UInt32))
/-- Schedule σ1. -/
def s1 (x : UInt32) : UInt32 := rotr 17 x ^^^ rotr 19 x ^^^ (x >>> (10 : UInt32))
/-- Compression Σ0. -/
def bigS0 (x : UInt32) : UInt32 := rotr 2 x ^^^ rotr 13 x ^^^ rotr 22 x
/-- Compression Σ1. -/
def bigS1 (x : UInt32) : UInt32 := rotr 6 x ^^^ rotr 11 x ^^^ rotr 25 x
/-- Ch. -/
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~ x) &&& z)
/-- Maj. -/
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- The 64 round constants. -/
def k : Array UInt32 :=
  #[ (0x428a2f98 : UInt32), 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
   , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
   , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
   , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
   , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
   , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
   , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
   , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

/-- Initial hash values. -/
def hInit : Array UInt32 :=
  #[ (0x6a09e667 : UInt32), 0xbb67ae85, 0x3c6ef372, 0xa54ff53a
   , 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

/-- The SHA-256 initial state contains exactly the eight FIPS state words. -/
theorem hInit_size : hInit.size = 8 := rfl

/-- Big-endian UInt32 from four bytes. -/
def u32be (b0 b1 b2 b3 : UInt8) : UInt32 :=
  ((b0.toUInt32 <<< (24 : UInt32)) ||| (b1.toUInt32 <<< (16 : UInt32))
    ||| (b2.toUInt32 <<< (8 : UInt32)) ||| b3.toUInt32)

/-- First 16 schedule words from a 64-byte block (length 64): big-endian, four
    bytes per word. Counts down 16 words consuming 4 bytes each. -/
def blockWordsAux : Nat → List UInt8 → Array UInt32 → Array UInt32
  | 0, _, acc => acc
  | n + 1, b0 :: b1 :: b2 :: b3 :: rest, acc =>
      blockWordsAux n rest (acc.push (u32be b0 b1 b2 b3))
  | _ + 1, _, acc => acc

def blockWords (block : List UInt8) : Array UInt32 := blockWordsAux 16 block #[]

private theorem blockWordsAux_size_of_length_ge
    (n : Nat) (bytes : List UInt8) (acc : Array UInt32)
    (hlen : 4 * n ≤ bytes.length) :
    (blockWordsAux n bytes acc).size = acc.size + n := by
  induction n generalizing bytes acc with
  | zero => simp [blockWordsAux]
  | succ n ih =>
      cases bytes with
      | nil =>
          simp at hlen
          omega
      | cons b0 bytes =>
          cases bytes with
          | nil =>
              simp at hlen
              omega
          | cons b1 bytes =>
              cases bytes with
              | nil =>
                  simp at hlen
                  omega
              | cons b2 bytes =>
                  cases bytes with
                  | nil =>
                      simp at hlen
                      omega
                  | cons b3 rest =>
                      rw [blockWordsAux, ih]
                      · simp [Array.size_push]
                        omega
                      · simp only [List.length_cons] at hlen
                        omega

/-- A complete SHA-256 block supplies all sixteen seed schedule words. -/
theorem blockWords_size_of_length (block : List UInt8)
    (hlen : block.length = 64) :
    (blockWords block).size = 16 := by
  unfold blockWords
  apply blockWordsAux_size_of_length_ge
  omega

/-- Extend the 16 seed words to the full 64-entry message schedule. -/
def extend (w : Array UInt32) (i : Nat) : Array UInt32 :=
  if i ≥ 64 then w
  else
    let wi := s1 (w.getD (i - 2) 0) + w.getD (i - 7) 0 + s0 (w.getD (i - 15) 0) + w.getD (i - 16) 0
    extend (w.push wi) (i + 1)
termination_by 64 - i

/-- Extending a schedule whose size matches its next index reaches exactly
    64 words; each push advances the size/index invariant by one. -/
theorem extend_size_of_size (w : Array UInt32) (i : Nat)
    (hsize : w.size = i) (hi : i ≤ 64) :
    (extend w i).size = 64 := by
  generalize hn : 64 - i = n
  induction n using Nat.strongRecOn generalizing w i with
  | ind n ih =>
      rw [extend]
      split
      next hdone =>
        omega
      next hmore =>
        apply ih (64 - (i + 1))
        · omega
        · simp [Array.size_push, hsize]
        · omega
        · rfl

/-- One compression pass over the 64 rounds; folds the working state into hash. -/
def compress (w : Array UInt32) (hash : Array UInt32)
    (i : Nat) (a b c d e f g h : UInt32) : Array UInt32 :=
  if i ≥ 64 then
    hash.set! 0 (hash.getD 0 0 + a)
      |>.set! 1 (hash.getD 1 0 + b)
      |>.set! 2 (hash.getD 2 0 + c)
      |>.set! 3 (hash.getD 3 0 + d)
      |>.set! 4 (hash.getD 4 0 + e)
      |>.set! 5 (hash.getD 5 0 + f)
      |>.set! 6 (hash.getD 6 0 + g)
      |>.set! 7 (hash.getD 7 0 + h)
  else
    let t1 := h + bigS1 e + ch e f g + k.getD i 0 + w.getD i 0
    let t2 := bigS0 a + maj a b c
    compress w hash (i + 1) (t1 + t2) a b c (d + t1) e f g
termination_by 64 - i

/-- Compression preserves an eight-word hash state.  In particular, every
    terminal `set!` targets an existing word rather than its default branch. -/
theorem compress_size_of_hash_size
    (w hash : Array UInt32) (i : Nat) (a b c d e f g h : UInt32)
    (hsize : hash.size = 8) :
    (compress w hash i a b c d e f g h).size = 8 := by
  generalize hn : 64 - i = n
  induction n using Nat.strongRecOn generalizing i a b c d e f g h with
  | ind n ih =>
      rw [compress]
      split
      next hdone =>
        simp [Array.set!, Array.size_setD, hsize]
      next hmore =>
        apply ih (64 - (i + 1))
        · omega
        · rfl

/-- Run compression over one 64-byte block, updating the running hash. -/
def processBlock (hash : Array UInt32) (block : List UInt8) : Array UInt32 :=
  let w := extend (blockWords block) 16
  compress w hash 0
    (hash.getD 0 0) (hash.getD 1 0) (hash.getD 2 0) (hash.getD 3 0)
    (hash.getD 4 0) (hash.getD 5 0) (hash.getD 6 0) (hash.getD 7 0)

/-- Processing one block preserves the eight-word running hash shape. -/
theorem processBlock_size_of_hash_size
    (hash : Array UInt32) (block : List UInt8) (hsize : hash.size = 8) :
    (processBlock hash block).size = 8 := by
  unfold processBlock
  apply compress_size_of_hash_size
  exact hsize

/-- Fold compression over all 64-byte blocks. -/
def processBlocks (blocks : List (List UInt8)) (hash : Array UInt32) : Array UInt32 :=
  match blocks with
  | [] => hash
  | block :: rest => processBlocks rest (processBlock hash block)
termination_by blocks.length

/-- Folding any block list preserves the eight-word running hash shape. -/
theorem processBlocks_size_of_hash_size
    (blocks : List (List UInt8)) (hash : Array UInt32)
    (hsize : hash.size = 8) :
    (processBlocks blocks hash).size = 8 := by
  induction blocks generalizing hash with
  | nil => simpa [processBlocks] using hsize
  | cons block rest ih =>
      rw [processBlocks]
      apply ih
      exact processBlock_size_of_hash_size hash block hsize

/-- The 8-byte big-endian encoding of a bit length (Nat). -/
def lengthBytes (bitLen : Nat) : List UInt8 :=
  let b (i : Nat) : UInt8 := ((bitLen >>> (i * 8)) &&& 0xff).toUInt8
  [ b 7, b 6, b 5, b 4, b 3, b 2, b 1, b 0 ]

/-- SHA-256 padding: 0x80, zeros to ≡56 mod 64, then 8-byte big-endian bit length. -/
def pad (msg : List UInt8) : List UInt8 :=
  let bitLen := msg.length * 8
  let withMarker := msg ++ [0x80]
  -- (#3115) integer-correct modular padding: Nat subtraction truncates, so
  -- `56 - r` underflows to 0 for r ∈ {57..63} (message len%64 ∈ {56..62}) and
  -- the length field landed off-grid — sha256Hex was NOT SHA-256 on that
  -- 1/64 residue class. Add the modulus before subtracting.
  let zeroCount := (56 + 64 - (withMarker.length % 64)) % 64
  withMarker ++ (List.replicate zeroCount 0) ++ lengthBytes bitLen

/-- Accumulate blocks in reverse order so the recursive call is in tail position. -/
private def chunk64Aux (xs : List UInt8) (acc : List (List UInt8)) :
    List (List UInt8) :=
  match xs with
  | [] => acc.reverse
  | x :: rest => chunk64Aux ((x :: rest).drop 64) ((x :: rest).take 64 :: acc)
termination_by xs.length
decreasing_by
  rw [List.length_drop]
  exact Nat.sub_lt (by simp) (by decide)

/-- Split a list into chunks of at most 64 bytes with constant call-stack
    depth in the number of blocks. -/
def chunk64 (xs : List UInt8) : List (List UInt8) := chunk64Aux xs []

@[simp] private theorem chunk64Aux_nil (acc : List (List UInt8)) :
    chunk64Aux [] acc = acc.reverse := by
  rw [chunk64Aux]

@[simp] private theorem chunk64Aux_cons (x : UInt8) (xs : List UInt8)
    (acc : List (List UInt8)) :
    chunk64Aux (x :: xs) acc =
      chunk64Aux ((x :: xs).drop 64) ((x :: xs).take 64 :: acc) := by
  rw [chunk64Aux]

private theorem chunk64Aux_acc (xs : List UInt8) (acc : List (List UInt8)) :
    chunk64Aux xs acc = acc.reverse ++ chunk64Aux xs [] := by
  generalize hn : xs.length = n
  induction n using Nat.strongRecOn generalizing xs acc with
  | ind n ih =>
      cases xs with
      | nil => simp [chunk64Aux]
      | cons x rest =>
          have hlt0 : ((x :: rest).drop 64).length < (x :: rest).length := by
            rw [List.length_drop]
            exact Nat.sub_lt (by simp) (by decide)
          have hlt : ((x :: rest).drop 64).length < n := by
            simpa [hn] using hlt0
          simp only [chunk64Aux]
          rw [ih _ hlt _ ((x :: rest).take 64 :: acc) rfl,
            ih _ hlt _ [((x :: rest).take 64)] rfl]
          simp [List.reverse_cons, List.append_assoc]

@[simp] theorem chunk64_nil : chunk64 [] = [] := by
  simp [chunk64, chunk64Aux]

@[simp] theorem chunk64_cons (x : UInt8) (xs : List UInt8) :
    chunk64 (x :: xs) =
      (x :: xs).take 64 :: chunk64 ((x :: xs).drop 64) := by
  simp only [chunk64, chunk64Aux]
  rw [chunk64Aux_acc]
  rfl

@[simp] theorem chunk64_append_block (block rest : List UInt8)
    (hlen : block.length = 64) :
    chunk64 (block ++ rest) = block :: chunk64 rest := by
  have hne : block ++ rest ≠ [] := by
    intro h
    have hz : (block ++ rest).length = 0 := by simp [h]
    simp [hlen] at hz
  cases hxs : block ++ rest with
  | nil => exact (hne hxs).elim
  | cons x xs =>
      rw [chunk64_cons]
      have ht : (x :: xs).take 64 = block := by
        rw [← hxs, ← hlen]
        exact List.take_left block rest
      have hd : (x :: xs).drop 64 = rest := by
        rw [← hxs, ← hlen]
        exact List.drop_left block rest
      rw [ht, hd]

theorem flatten_chunk64 (xs : List UInt8) :
    (chunk64 xs).flatten = xs := by
  generalize hn : xs.length = n
  induction n using Nat.strongRecOn generalizing xs with
  | ind n ih =>
      cases xs with
      | nil => simp
      | cons x rest =>
          have hlt0 : ((x :: rest).drop 64).length < (x :: rest).length := by
            rw [List.length_drop]
            exact Nat.sub_lt (by simp) (by decide)
          have hlt : ((x :: rest).drop 64).length < n := by
            simpa [hn] using hlt0
          have hrec := ih _ hlt ((x :: rest).drop 64) rfl
          rw [chunk64_cons, List.flatten_cons]
          rw [hrec]
          exact List.take_append_drop 64 _

theorem chunk64_flatten_of_blocks64 (blocks : List (List UInt8))
    (hlen : ∀ block ∈ blocks, block.length = 64) :
    chunk64 blocks.flatten = blocks := by
  induction blocks with
  | nil => simp
  | cons block rest ih =>
      have hb : block.length = 64 := hlen block (by simp)
      have hr : ∀ next ∈ rest, next.length = 64 := by
        intro next hnext
        exact hlen next (by simp [hnext])
      rw [List.flatten_cons, chunk64_append_block block rest.flatten hb, ih hr]

theorem pad_length_mod64 (msg : List UInt8) :
    (pad msg).length % 64 = 0 := by
  simp [pad, lengthBytes]
  omega

theorem chunk64_blocks_length_of_mod64 (xs : List UInt8)
    (hmod : xs.length % 64 = 0) :
    ∀ block ∈ chunk64 xs, block.length = 64 := by
  generalize hn : xs.length = n at hmod ⊢
  induction n using Nat.strongRecOn generalizing xs with
  | ind n ih =>
      cases xs with
      | nil => simp
      | cons x rest =>
          have hge : 64 ≤ (x :: rest).length := by
            have hpos : 0 < (x :: rest).length := by simp
            omega
          have htake : ((x :: rest).take 64).length = 64 := by
            exact List.length_take_of_le hge
          have hdropmod : ((x :: rest).drop 64).length % 64 = 0 := by
            rw [List.length_drop]
            omega
          have hlt0 : ((x :: rest).drop 64).length < (x :: rest).length := by
            rw [List.length_drop]
            exact Nat.sub_lt (by simp) (by decide)
          have hlt : ((x :: rest).drop 64).length < n := by
            simpa [hn] using hlt0
          have hrec := ih _ hlt ((x :: rest).drop 64) rfl hdropmod
          intro block hmem
          rw [chunk64_cons] at hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact htake
          · exact hrec block hmem

theorem chunk64_pad_blocks64 (msg : List UInt8) :
    ∀ block ∈ chunk64 (pad msg), block.length = 64 :=
  chunk64_blocks_length_of_mod64 (pad msg) (pad_length_mod64 msg)

/-- Lowercase hex for a single nibble. -/
def hexDigit (n : UInt8) : String :=
  if n < 10 then toString n.toNat
  else match n with
    | 10 => "a" | 11 => "b" | 12 => "c" | 13 => "d" | 14 => "e" | _ => "f"

/-- Lowercase hex for a single byte. -/
def hexByte (b : UInt8) : String :=
  hexDigit (b >>> (4 : UInt8)) ++ hexDigit (b &&& 0x0f)

/-- SHA-256 of a string's UTF-8 bytes, returned as 64-char lowercase hex. -/
def sha256Hex (input : String) : String :=
  let msg := input.toUTF8.toList
  let padded := pad msg
  let blocks := chunk64 padded
  let hash := processBlocks blocks hInit
  let words :=
    hash.getD 0 0 :: hash.getD 1 0 :: hash.getD 2 0 :: hash.getD 3 0 ::
    hash.getD 4 0 :: hash.getD 5 0 :: hash.getD 6 0 :: hash.getD 7 0 :: []
  let bytesBE : List UInt8 :=
    words.flatMap (fun w =>
      [ (w >>> (24 : UInt32)).toUInt8, (w >>> (16 : UInt32)).toUInt8
      , (w >>> (8 : UInt32)).toUInt8, w.toUInt8 ])
  String.join (bytesBE.map hexByte)

end Residua.SHA256
