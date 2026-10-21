import rcic.ScmSrcGroups
import rcic.ScmSrcGroupsKernelRfl
import rcic.ScmWire

/-! Stage 3a: `DerivedAddr` conformance certificates on the K3c layout.

For each of the five DA constructor rows of `srcEnvG` (slots 24-28:
`daI`/`daB`/`daS`/`daY`/`daLB`, family at slot 23) this file proves that
the row's digest constant (slots 17-20, 22) is the real
`Rcic.TypedRef.deriveDigest 3 16 <type bytes>` of the row's type bytes
(slots 11-14, 21), with every hop kernel-checked:

* the wire encodings, the preimage equalities
  `preimageRepr 3 16 <ty> = <displayed literal>` and the unfold
  `deriveDigest 3 16 <ty> = sha256Hex <literal>` (by `rfl`);
* the object-env bindings: member lookups in `srcEnvG`, each row's
  declared type `DerivedAddr 3 16 <bytes> <digest>`, and the decodes of
  the installed `Bytes` literals back to the digest/type strings;
* the hash hops `sha256Hex <literal> = <digest hex>`, by `decide`.
  `Residua.SHA256.sha256Hex` is kernel-reducible since L-H (#6077), so
  the hop the earlier draft certified only by `native_decide` is now a
  kernel proof. No `native_decide`, no `Lean.ofReduceBool`; every
  theorem's axioms are within `{propext, Quot.sound}`.

`daLB` is the V2 row: type bytes `"Lb"` (`list bool`), digest
`Old.digestLBHex`; it is structurally identical to the V1 rows. -/

open Rcic.Declarative Rcic.Machine Rcic.TypedRef Residua.SHA256
open Rcic.Scm.SrcTV
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Rcic.Scm.SrcG.DA

/-- Unquote a `Seq N` byte chain under the K3c numbering
(`Bnil = 5`, `Bcons = 6`). -/
def unquoteG : Expr Nat → Option (List Nat)
  | .const 5 [] => some []
  | .app (.app (.const 6 []) (.lit t)) tl =>
      match unquoteG tl with
      | some ns => some (t :: ns)
      | none => none
  | _ => none

theorem encTy_i64   : Rcic.Scm.Wire.encTy .i64   = "i" := rfl
theorem encTy_bool  : Rcic.Scm.Wire.encTy .bool  = "b" := rfl
theorem encTy_str   : Rcic.Scm.Wire.encTy .str   = "s" := rfl
theorem encTy_bytes : Rcic.Scm.Wire.encTy .bytes = "y" := rfl
theorem encTy_listBool :
    Rcic.Scm.Wire.encTy (.list .bool) = "Lb" := rfl

kernel_rfl_theorem daSlotFam : srcEnvG.members 23 = some mDA

/-! ### Row `mDaI` (`i`) -/

def preimageLitI64 : String :=
  "MakeRecord([[str:9:ref_class,Num(float:3.0)],[str:9:kind_code,Num(float:16.0)],[str:16:hash_profile_ref,Num(float:1.0)],[str:17:domain_schema_ref,Num(float:0.0)],[str:17:object_schema_ref,Num(float:0.0)],[str:22:canonical_object_bytes,StrLit(str:1:i)]])"

theorem preimage_I64 : preimageRepr 3 (16 : Int) "i" = preimageLitI64 := rfl

theorem derive_I64 :
    deriveDigest 3 (16 : Int) "i" = sha256Hex preimageLitI64 := by
  show sha256Hex (preimageRepr 3 (16 : Int) "i") = sha256Hex preimageLitI64
  rw [preimage_I64]

kernel_rfl_theorem daSlotI64 : srcEnvG.members 24 = some mDaI
kernel_rfl_theorem bytesSlotI64 : srcEnvG.members 11 = some mBytesI
kernel_rfl_theorem digestSlotI64 : srcEnvG.members 17 = some mDigestI

theorem daTyI64 : mDaI.mtype =
    .app (.app (.app (.app (.const 23 []) (.lit 3)) (.lit 16))
      (.const 11 [])) (.const 17 []) := rfl

kernel_rfl_theorem bytesDecodeI64 :
    unquoteG (mBytesI.body.getD (.sort .zero)) = some ("i".toList.map Char.toNat)
kernel_rfl_theorem digestDecodeI64 :
    unquoteG (mDigestI.body.getD (.sort .zero)) = some (digestIHex.toList.map Char.toNat)

theorem hash_I64 : sha256Hex preimageLitI64 = digestIHex := by decide

theorem daCert_I64 : deriveDigest 3 (16 : Int) "i" = digestIHex :=
  (derive_I64).trans hash_I64

/-! ### Row `mDaB` (`b`) -/

def preimageLitBool : String :=
  "MakeRecord([[str:9:ref_class,Num(float:3.0)],[str:9:kind_code,Num(float:16.0)],[str:16:hash_profile_ref,Num(float:1.0)],[str:17:domain_schema_ref,Num(float:0.0)],[str:17:object_schema_ref,Num(float:0.0)],[str:22:canonical_object_bytes,StrLit(str:1:b)]])"

theorem preimage_Bool : preimageRepr 3 (16 : Int) "b" = preimageLitBool := rfl

theorem derive_Bool :
    deriveDigest 3 (16 : Int) "b" = sha256Hex preimageLitBool := by
  show sha256Hex (preimageRepr 3 (16 : Int) "b") = sha256Hex preimageLitBool
  rw [preimage_Bool]

kernel_rfl_theorem daSlotBool : srcEnvG.members 25 = some mDaB
kernel_rfl_theorem bytesSlotBool : srcEnvG.members 12 = some mBytesB
kernel_rfl_theorem digestSlotBool : srcEnvG.members 18 = some mDigestB

theorem daTyBool : mDaB.mtype =
    .app (.app (.app (.app (.const 23 []) (.lit 3)) (.lit 16))
      (.const 12 [])) (.const 18 []) := rfl

kernel_rfl_theorem bytesDecodeBool :
    unquoteG (mBytesB.body.getD (.sort .zero)) = some ("b".toList.map Char.toNat)
kernel_rfl_theorem digestDecodeBool :
    unquoteG (mDigestB.body.getD (.sort .zero)) = some (digestBHex.toList.map Char.toNat)

theorem hash_Bool : sha256Hex preimageLitBool = digestBHex := by decide

theorem daCert_Bool : deriveDigest 3 (16 : Int) "b" = digestBHex :=
  (derive_Bool).trans hash_Bool

/-! ### Row `mDaS` (`s`) -/

def preimageLitStr : String :=
  "MakeRecord([[str:9:ref_class,Num(float:3.0)],[str:9:kind_code,Num(float:16.0)],[str:16:hash_profile_ref,Num(float:1.0)],[str:17:domain_schema_ref,Num(float:0.0)],[str:17:object_schema_ref,Num(float:0.0)],[str:22:canonical_object_bytes,StrLit(str:1:s)]])"

theorem preimage_Str : preimageRepr 3 (16 : Int) "s" = preimageLitStr := rfl

theorem derive_Str :
    deriveDigest 3 (16 : Int) "s" = sha256Hex preimageLitStr := by
  show sha256Hex (preimageRepr 3 (16 : Int) "s") = sha256Hex preimageLitStr
  rw [preimage_Str]

kernel_rfl_theorem daSlotStr : srcEnvG.members 26 = some mDaS
kernel_rfl_theorem bytesSlotStr : srcEnvG.members 13 = some mBytesS
kernel_rfl_theorem digestSlotStr : srcEnvG.members 19 = some mDigestS

theorem daTyStr : mDaS.mtype =
    .app (.app (.app (.app (.const 23 []) (.lit 3)) (.lit 16))
      (.const 13 [])) (.const 19 []) := rfl

kernel_rfl_theorem bytesDecodeStr :
    unquoteG (mBytesS.body.getD (.sort .zero)) = some ("s".toList.map Char.toNat)
kernel_rfl_theorem digestDecodeStr :
    unquoteG (mDigestS.body.getD (.sort .zero)) = some (digestSHex.toList.map Char.toNat)

theorem hash_Str : sha256Hex preimageLitStr = digestSHex := by decide

theorem daCert_Str : deriveDigest 3 (16 : Int) "s" = digestSHex :=
  (derive_Str).trans hash_Str

/-! ### Row `mDaY` (`y`) -/

def preimageLitBytes : String :=
  "MakeRecord([[str:9:ref_class,Num(float:3.0)],[str:9:kind_code,Num(float:16.0)],[str:16:hash_profile_ref,Num(float:1.0)],[str:17:domain_schema_ref,Num(float:0.0)],[str:17:object_schema_ref,Num(float:0.0)],[str:22:canonical_object_bytes,StrLit(str:1:y)]])"

theorem preimage_Bytes : preimageRepr 3 (16 : Int) "y" = preimageLitBytes := rfl

theorem derive_Bytes :
    deriveDigest 3 (16 : Int) "y" = sha256Hex preimageLitBytes := by
  show sha256Hex (preimageRepr 3 (16 : Int) "y") = sha256Hex preimageLitBytes
  rw [preimage_Bytes]

kernel_rfl_theorem daSlotBytes : srcEnvG.members 27 = some mDaY
kernel_rfl_theorem bytesSlotBytes : srcEnvG.members 14 = some mBytesY
kernel_rfl_theorem digestSlotBytes : srcEnvG.members 20 = some mDigestY

theorem daTyBytes : mDaY.mtype =
    .app (.app (.app (.app (.const 23 []) (.lit 3)) (.lit 16))
      (.const 14 [])) (.const 20 []) := rfl

kernel_rfl_theorem bytesDecodeBytes :
    unquoteG (mBytesY.body.getD (.sort .zero)) = some ("y".toList.map Char.toNat)
kernel_rfl_theorem digestDecodeBytes :
    unquoteG (mDigestY.body.getD (.sort .zero)) = some (digestYHex.toList.map Char.toNat)

theorem hash_Bytes : sha256Hex preimageLitBytes = digestYHex := by decide

theorem daCert_Bytes : deriveDigest 3 (16 : Int) "y" = digestYHex :=
  (derive_Bytes).trans hash_Bytes

/-! ### Row `mDaLB` (`Lb`) -/

def preimageLitLB : String :=
  "MakeRecord([[str:9:ref_class,Num(float:3.0)],[str:9:kind_code,Num(float:16.0)],[str:16:hash_profile_ref,Num(float:1.0)],[str:17:domain_schema_ref,Num(float:0.0)],[str:17:object_schema_ref,Num(float:0.0)],[str:22:canonical_object_bytes,StrLit(str:2:Lb)]])"

theorem preimage_LB : preimageRepr 3 (16 : Int) "Lb" = preimageLitLB := rfl

theorem derive_LB :
    deriveDigest 3 (16 : Int) "Lb" = sha256Hex preimageLitLB := by
  show sha256Hex (preimageRepr 3 (16 : Int) "Lb") = sha256Hex preimageLitLB
  rw [preimage_LB]

kernel_rfl_theorem daSlotLB : srcEnvG.members 28 = some mDaLB
kernel_rfl_theorem bytesSlotLB : srcEnvG.members 21 = some mBytesLB
kernel_rfl_theorem digestSlotLB : srcEnvG.members 22 = some mDigestLB

theorem daTyLB : mDaLB.mtype =
    .app (.app (.app (.app (.const 23 []) (.lit 3)) (.lit 16))
      (.const 21 [])) (.const 22 []) := rfl

kernel_rfl_theorem bytesDecodeLB :
    unquoteG (mBytesLB.body.getD (.sort .zero)) = some ("Lb".toList.map Char.toNat)
kernel_rfl_theorem digestDecodeLB :
    unquoteG (mDigestLB.body.getD (.sort .zero)) = some (Old.digestLBHex.toList.map Char.toNat)

theorem hash_LB : sha256Hex preimageLitLB = Old.digestLBHex := by decide

theorem daCert_LB : deriveDigest 3 (16 : Int) "Lb" = Old.digestLBHex :=
  (derive_LB).trans hash_LB

def daTable : Prop :=
  deriveDigest 3 (16 : Int) "i" = digestIHex ∧
  deriveDigest 3 (16 : Int) "b" = digestBHex ∧
  deriveDigest 3 (16 : Int) "s" = digestSHex ∧
  deriveDigest 3 (16 : Int) "y" = digestYHex ∧
  deriveDigest 3 (16 : Int) "Lb" = Old.digestLBHex

theorem daTable_holds : daTable :=
  ⟨daCert_I64, daCert_Bool, daCert_Str, daCert_Bytes, daCert_LB⟩

end Rcic.Scm.SrcG.DA

#print axioms Rcic.Scm.SrcG.DA.encTy_i64
#print axioms Rcic.Scm.SrcG.DA.encTy_listBool
#print axioms Rcic.Scm.SrcG.DA.daSlotFam
#print axioms Rcic.Scm.SrcG.DA.preimage_I64
#print axioms Rcic.Scm.SrcG.DA.derive_I64
#print axioms Rcic.Scm.SrcG.DA.daSlotI64
#print axioms Rcic.Scm.SrcG.DA.bytesSlotI64
#print axioms Rcic.Scm.SrcG.DA.digestSlotI64
#print axioms Rcic.Scm.SrcG.DA.daTyI64
#print axioms Rcic.Scm.SrcG.DA.bytesDecodeI64
#print axioms Rcic.Scm.SrcG.DA.digestDecodeI64
#print axioms Rcic.Scm.SrcG.DA.hash_I64
#print axioms Rcic.Scm.SrcG.DA.daCert_I64
#print axioms Rcic.Scm.SrcG.DA.preimage_Bool
#print axioms Rcic.Scm.SrcG.DA.derive_Bool
#print axioms Rcic.Scm.SrcG.DA.daSlotBool
#print axioms Rcic.Scm.SrcG.DA.bytesSlotBool
#print axioms Rcic.Scm.SrcG.DA.digestSlotBool
#print axioms Rcic.Scm.SrcG.DA.daTyBool
#print axioms Rcic.Scm.SrcG.DA.bytesDecodeBool
#print axioms Rcic.Scm.SrcG.DA.digestDecodeBool
#print axioms Rcic.Scm.SrcG.DA.hash_Bool
#print axioms Rcic.Scm.SrcG.DA.daCert_Bool
#print axioms Rcic.Scm.SrcG.DA.preimage_Str
#print axioms Rcic.Scm.SrcG.DA.derive_Str
#print axioms Rcic.Scm.SrcG.DA.daSlotStr
#print axioms Rcic.Scm.SrcG.DA.bytesSlotStr
#print axioms Rcic.Scm.SrcG.DA.digestSlotStr
#print axioms Rcic.Scm.SrcG.DA.daTyStr
#print axioms Rcic.Scm.SrcG.DA.bytesDecodeStr
#print axioms Rcic.Scm.SrcG.DA.digestDecodeStr
#print axioms Rcic.Scm.SrcG.DA.hash_Str
#print axioms Rcic.Scm.SrcG.DA.daCert_Str
#print axioms Rcic.Scm.SrcG.DA.preimage_Bytes
#print axioms Rcic.Scm.SrcG.DA.derive_Bytes
#print axioms Rcic.Scm.SrcG.DA.daSlotBytes
#print axioms Rcic.Scm.SrcG.DA.bytesSlotBytes
#print axioms Rcic.Scm.SrcG.DA.digestSlotBytes
#print axioms Rcic.Scm.SrcG.DA.daTyBytes
#print axioms Rcic.Scm.SrcG.DA.bytesDecodeBytes
#print axioms Rcic.Scm.SrcG.DA.digestDecodeBytes
#print axioms Rcic.Scm.SrcG.DA.hash_Bytes
#print axioms Rcic.Scm.SrcG.DA.daCert_Bytes
#print axioms Rcic.Scm.SrcG.DA.preimage_LB
#print axioms Rcic.Scm.SrcG.DA.derive_LB
#print axioms Rcic.Scm.SrcG.DA.daSlotLB
#print axioms Rcic.Scm.SrcG.DA.bytesSlotLB
#print axioms Rcic.Scm.SrcG.DA.digestSlotLB
#print axioms Rcic.Scm.SrcG.DA.daTyLB
#print axioms Rcic.Scm.SrcG.DA.bytesDecodeLB
#print axioms Rcic.Scm.SrcG.DA.digestDecodeLB
#print axioms Rcic.Scm.SrcG.DA.hash_LB
#print axioms Rcic.Scm.SrcG.DA.daCert_LB
#print axioms Rcic.Scm.SrcG.DA.daTable_holds
