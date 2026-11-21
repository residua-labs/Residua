import Effect.ConformanceSeeds

namespace Effect.ABI.E3

open Wire Fixtures Conformance

structure CaseResult where
  group : String
  id : String
  verdict : Verdict

def check (group id : String) (probe : Probe) : CaseResult := ⟨group, id, probe.run⟩

def inspect (group id : String) (bytes : List Bytes) (equal : Bool) : CaseResult :=
  ⟨group, id, ⟨"matches", if equal then "matches" else "different",
    Format.q (.list .bytes) bytes, equal⟩⟩

private def parameter (n : Nat) : Bytes := littleEndianBytes 9 n

private def around (n : Nat) : List Nat := [n - 1, n, n + 1]

private def generated (group id : String) (values : List Nat) (probe : Nat → Probe) :
    List CaseResult :=
  values.map fun n => check group s!"{id}/{n}" (probe n)

private def extend (frame : Bytes) : Bytes :=
  littleEndianBytes 4 (frame.length + 1) ++ frame.drop 4 ++ [0x41]

private def requests : List Wire.Request :=
  [.version 256 version9P, .auth noFid [] [], .attach 0 noFid [] (ascii "root"), .flush 65534,
   .walk 0 1 [ascii "fs", [], [0xf4, 0x8f, 0xbf, 0xbf]], .openFile 1 2,
   .create 1 (ascii "new") 511 2, .read 1 noLengthChange noFid, .write 1 2 [0, 0xff],
   .clunk 1, .remove 1, .stat 0, .wstat 1 noStatChange]

private def replies : List Wire.Reply :=
  [.version 256 version9P, .auth rootQid, .attach rootQid, .error (ascii "short"), .flush,
   .walk [dirQid, fileQid], .openFile fileQid 0, .create fileQid noFid, .read [0, 0xff],
   .write noFid, .clunk, .remove, .stat (statOf fileQid), .wstat]

private def lexical : List CaseResult :=
  let tag := 0xfe01
  (requests.map fun t =>
    let bytes := request t tag
    inspect "grammar" s!"T/{t.code}" [bytes, extend bytes]
      (decodeT bytes == some ⟨tag, t⟩ && (decodeT (extend bytes)).isNone)) ++
  (replies.map fun r =>
    let bytes := reply r tag
    inspect "grammar" s!"R/{r.code}" [bytes, extend bytes]
      (decodeR bytes == some ⟨tag, r⟩ && (decodeR (extend bytes)).isNone))

private def unsigned : List CaseResult :=
  [1, 2, 4, 8].flatMap fun width =>
    let last := 256^width - 1
    ([0, 1] ++ around last).map fun n =>
    let encoded : Option Bytes := Build.uint width n
    let good :=
      if n > last then encoded.isNone else
        encoded.any (fun (bytes : Bytes) => bytes.length == width && littleEndian bytes == n)
    inspect "prewire" s!"uint{8 * width}/{n}" [parameter width, parameter n, encoded.getD []]
      good

private def readOffset : List CaseResult :=
  (around noLengthChange).map fun n =>
    let t := Wire.Request.read 1 n 1
    let raw := Build.request t 0
    let expected := if n ≤ noLengthChange then "frame" else Residue.t1.label
    let actual := match raw with
      | none => Residue.t1.label
      | some bytes => if decodeT bytes == some ⟨0, t⟩ then "frame" else "wrong-frame"
    ⟨"prewire", s!"Tread-offset/{n}", ⟨expected, actual,
      Format.q (.list .bytes) [parameter n, raw.getD []], expected == actual⟩⟩

private def textBounds : List CaseResult :=
  let textLengths := (around 65535).map fun n =>
    let raw := List.replicate n (0x61 : UInt8)
    let encoded : Option Bytes := Build.text raw
    let good :=
      if n > 65535 then encoded.isNone else
        encoded.any (fun (bytes : Bytes) => littleEndian (bytes.take 2) == n && bytes.drop 2 == raw)
    inspect "prewire" s!"string-length/{n}" [parameter n, Format.q .bytes raw] good
  let encodings : List (String × Bytes × Bool) :=
    [("max-scalar-1", [0xf4, 0x8f, 0xbf, 0xbe], true),
     ("max-scalar", [0xf4, 0x8f, 0xbf, 0xbf], true),
     ("max-scalar+1", [0xf4, 0x90, 0x80, 0x80], false),
     ("surrogate", [0xed, 0xa0, 0x80], false), ("overlong", [0xc0, 0x81], false),
     ("nul", [0], false), ("empty", [], true)]
  textLengths ++ encodings.map fun (id, raw, accepted) =>
    let frame := (Build.frame 107 0 (littleEndianBytes 2 raw.length ++ raw)).getD []
    inspect "prewire" s!"string/{id}" [raw, frame]
      ((Build.text raw).isSome == accepted && (decodeR frame).isSome == accepted)

private def paddingBounds : List CaseResult :=
  let vectors : List (Nat × String) :=
    [(47, "5c51d487c53d6e2d75967a16f31d6334451884a108dfe014448e00291b72b22b"),
     (48, "a96a679f4f0f5605928710e431e5ad9b5e5c262735c530fe753d70f1de32b67c"),
     (49, "c298ced132ecfab215341e3e21e94b69b68cceee0f95c0b6cfdb0b3f382f6c93"),
     (53, "13bbd9d590f2e5092f3d3f3695d7a4148e76ce5f82ccfa0e36dc220c0ed17128"),
     (54, "2266301d52946b0eb32e12ee1638665ac68aacd208c477c213c630b0cb1652ea"),
     (55, "f82bb4ee579341c0c245051a2cb0113a88526ba09f2c157a1c1050356a0c3bdf"),
     (56, "1d1e28acbc54c99fc6b14b39f684734b89a84ffd1ffb7bd054b89e3a332ca4a9")]
  vectors.map fun (n, expected) =>
    let raw := List.replicate n (0x61 : UInt8)
    let preimage := Format.canonical .bytes raw
    inspect "format" s!"sha256/{preimage.length}" [preimage]
      (Format.lowerHex (Format.q .bytes raw) == ascii expected)

private def statAt (offset : Nat) (frame : Bytes) : List (Nat × Bytes) :=
  let size := littleEndian ((frame.drop offset).take 2)
  (around size).map fun n => (n, frame.take offset ++ littleEndianBytes 2 n ++ frame.drop (offset + 2))

private def statBounds : List CaseResult :=
  let t := request (.wstat 1 noStatChange)
  let r := reply (.stat (statOf rootQid []))
  [("T/outer", 11), ("T/inner", 13)].flatMap (fun (name, offset) =>
    (statAt offset t).map fun (n, raw) =>
      inspect "boundary" s!"stat/{name}/{n}" [raw] ((decodeT raw).isSome == (raw == t))) ++
  [("R/outer", 7), ("R/inner", 9)].flatMap (fun (name, offset) =>
    (statAt offset r).map fun (n, raw) =>
      inspect "boundary" s!"stat/{name}/{n}" [raw] ((decodeR raw).isSome == (raw == r)))

private def frameBounds : List CaseResult :=
  let lengths := ([5, 6, 7, 8] : List Nat).map fun n =>
    let raw := littleEndianBytes 4 n ++ ([121, 0, 0, 0] : Bytes).take (n - 4)
    check "boundary" s!"frame/R/{n}" (if n == 7 then
      commit prefixPairs clunkRoot raw afterRootClunk else receive prefixPairs clunkRoot raw (.refuse .r1))
  let ts := generated "boundary" "msize/T" (around 256) fun n =>
    let name := List.replicate (n - walkPair.t.length - 2) (0x61 : UInt8)
    let t := request (.walk 0 1 (fsPath ++ [name]))
    { send prefixPairs t (if n ≤ 256 then .issue t else .refuse .t3) with
      premise := fun _ => t.length == n && (decodeT t).isSome }
  let rs := generated "boundary" "msize/R" (around 256) fun n =>
    let r := errorFrame n
    { receive prefixPairs statRoot r (if n ≤ 256 then .commit r id else .refuse .r2) with
      premise := fun _ => r.length == n && (decodeR r).isSome }
  lengths ++ ts ++ rs

private def profileBounds : List CaseResult :=
  let verify := fun usage valid => openAt (context [] usage) .pre (if valid then .opened else .refuse .c3)
  generated "boundary" "offer"
      (around 256 ++ around noFid) (fun n =>
        verify { profile with offer := UInt64.ofNat n } (256 ≤ n && n ≤ noFid)) ++
    generated "boundary" "reply-msize" (around 256 ++ around 512) (fun n =>
      let p := { profile with offer := 512 }
      if 256 ≤ n && n ≤ 512 then negotiated p n else
        receive [] (versionAt p) (reply (.version n version9P) noTag) (.refuse .r7) p) ++
    generated "boundary" "max-data" ([0, 1] ++ around noFid) (fun n =>
      verify { profile with maxData := UInt64.ofNat n } (n ≤ noFid)) ++
    generated "boundary" "max-steps" ([0, 1] ++ around maxSigned) (fun n =>
      verify { profile with maxSteps := UInt64.ofNat n } (n ≤ maxSigned)) ++
    generated "boundary" "timeout" (around 1 ++ around maxSigned) (fun n =>
      verify { profile with timeout := UInt64.ofNat n } (1 ≤ n && n ≤ maxSigned)) ++
    generated "boundary" "profile-revision" (around 1) (fun n =>
      verify { profile with revision := UInt64.ofNat n } (n == 1))

private def readAt (n : Nat) (offset : Nat := 0) : Bytes := request (.read 1 offset n)

private def readSize (pairs : List RawPair) (usage : Profile) (bound n : Nat) : Probe :=
  let t := readAt n
  send pairs t (if n ≤ bound then .issue t else .refuse .t9) usage

private def writeSize (pairs : List RawPair) (usage : Profile) (bound n : Nat) : Probe :=
  let t := commandWrite (List.replicate n 0x41)
  send pairs t (if n ≤ bound then .issue t else .refuse .t9) usage

private def transferBounds : List CaseResult :=
  let at512 := { profile with offer := 512, maxData := 512 }
  let big := versionPair 512 512 :: (readable 0).drop 1
  let at256 := { profile with maxData := 512 }
  generated "boundary" "walk-count" (around 16) (fun n =>
    let t := namedWalk n
    { send prefixPairs t (if n ≤ 16 then .issue t else .refuse .t9) with
      premise := fun _ => (decodeT t).isSome }) ++
  generated "boundary" "read-cap/profile" (around 128) (readSize (readable 0) profile 128) ++
  generated "boundary" "read-cap/msize-24" (around 232) (readSize (readable 0) at256 232) ++
  generated "boundary" "read-cap/iounit" (around 64) (readSize (readable 64) profile 64) ++
  generated "boundary" "read-cap/device" (around 256) (readSize big at512 256) ++
  generated "boundary" "write-cap/profile" (around 128) (writeSize (readable 0) profile 128) ++
  generated "boundary" "write-cap/msize-24" (around 232) (writeSize (readable 0) at256 232) ++
  generated "boundary" "write-cap/iounit" (around 64) (writeSize (readable 64) profile 64) ++
  generated "boundary" "write-cap/device" (around 256) (writeSize big at512 256) ++
  generated "boundary" "read-count/min" [0, 1] (readSize (readable 0) profile 128) ++
  generated "boundary" "write-count/min" [0, 1] (writeSize (readable 0) profile 128) ++
  generated "boundary" "iounit" (around 1 ++ around 128) (fun n =>
    let r := (openPair 2 n).r
    commit unopenedFile (openPair 2 n).t r (fun s =>
      { s with work := some ((Fid.unopened (fsPath ++ [ascii "file"]) fileQid).openAs fileQid 2 n) })) ++
  generated "boundary" "atomic-record" (around 16) (fun n =>
    let t := commandWrite (List.replicate (n - 1) 0x41 ++ [10])
    send commandReady t (.refuse (if n ≤ 16 then .t15 else .t9))) ++
  generated "boundary" "read-reply-count" (around 1) (fun n =>
    let r := reply (.read (List.replicate n 0x41))
    receive (readable 0) readOne r (if n ≤ 1 then .commit r id else .refuse .r8)) ++
  generated "boundary" "write-reply-count" (around 5) (fun n =>
    let r := reply (.write n)
    receive commandReady echoWrite r
      (if n == 5 then .commit r id else .refuse (if n < 5 then .r10 else .r8))) ++
  generated "boundary" "step-count" (around 2) (fun n =>
    let p := { profile with maxSteps := 2 }
    if n == 1 then sendOK [versionPair] attachPair.t p else
    { send prefixPairs statRoot (.refuse (if n == 2 then .t10 else .c5)) p with
      varyState := fun s => { s with sentSteps := UInt64.ofNat n } }) ++
  [check "boundary" "step-count/zero" (send [] versionPair.t (.refuse .t10)
    { profile with maxSteps := 0 })]

def boundaryCases : List CaseResult :=
  lexical ++ unsigned ++ readOffset ++ textBounds ++ paddingBounds ++ statBounds ++ frameBounds ++
    profileBounds ++ transferBounds

end Effect.ABI.E3
