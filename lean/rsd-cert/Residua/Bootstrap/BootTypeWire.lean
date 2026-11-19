import Residua.Bootstrap.IR
import Residua.Bootstrap.Bundle

namespace Residua.Bootstrap.BootTypeWire

open IR
abbrev Bytes := List UInt8

mutual
  /-- ADR r4.6: constructor declaration order, minimal lengths, names as UTF-8
  bytes leaves. This host encoder is an oracle/initial seed specification,
  not code used by the generated SCM type parser. -/
  def encode : BootTy → Bytes
    | .i64 => [0]
    | .bool => [1]
    | .str => [2]
    | .bytes => [3]
    | .list t => 4 :: encode t
    | .pair a b => 5 :: (encode a ++ encode b)
    | .sum ts => 6 :: (Bundle.lebEnc ts.length ++ encodeTypes ts)
    | .record fs => 7 :: (Bundle.lebEnc fs.length ++ encodeFields fs)
    | .option t => 8 :: encode t
    | .residue t => 9 :: encode t

  def encodeTypes : List BootTy → Bytes
    | [] => []
    | t :: ts => encode t ++ encodeTypes ts

  def encodeFields : List (String × BootTy) → Bytes
    | [] => []
    | (name, t) :: fs =>
        Bundle.bEncode (.bytes name.toUTF8.data.toList) ++ encode t ++ encodeFields fs
end

/-- Signature fragment of a definition entry (not a complete named entry). -/
def encodeSignature (signature : Ctx × BootTy) : Bytes :=
  Bundle.lebEnc signature.1.length ++ encodeTypes signature.1 ++ encode signature.2

/-- Internal count-prefixed signature environment, not the bundle wire format. -/
def encodeSignatures (signatures : SigTable) : Bytes :=
  Bundle.lebEnc signatures.length ++ signatures.flatMap encodeSignature

end Residua.Bootstrap.BootTypeWire
