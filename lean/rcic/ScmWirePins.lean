/-
RCIC 06 §17 — M-002 pins of `Wire.scmWire` to
apps/rcic-scm-wire/rcic_scm_wire_corpus.json (22 rows, all transcribed).

Hand-transcribed (§18.3 rule 4). Row n ← the corpus label with its
"SCM-0NN 06 s17 " prefix dropped. The 402-character canonical program
`bigBytes` is the bytes of row 0 and the expected bytes of row 1, written as
its first 50 characters (`bigHead`) and the remainder (`bigTail`); row 18
differs only in the first 50 characters (catalog entries swapped). The
program of row 1 is the same object as `ExprPins.P` (the typing corpus'
program), with profile `SCM-Core-0`.
-/
import rcic.ScmWire
import rcic.ScmExprPins

namespace Rcic.Scm.WirePins
open Rcic.Scm Rcic.Scm.Wire

def prof : String := "SCM-Core-0"
def bigHead : String := "M10:SCM-Core-02;9:bad_inputR0;15:range_violationi"
def bigTail : String :=
  "1;7:ext.len1;si11;2;iiif3:add2;10;11;1;iij15:range_violationh15:range_violation10;i10;1;" ++
  "Liid10;0I0;if3:add2;10;11;1;iR3;9:convergedb5:statei5:stepsie10;0I10;if2:lt2;0I5;i10;" ++
  "f3:add2;10;0I1;i0;igl0;2;0I1;i0I2;i1;sigx7:ext.len1;10;1;S2;ibi810;2;10;310;0I1;i0I0;i0;" ++
  "R2;1:ai1:bb92;1:a1:b2;0I1;i0B1;b1;R2;1:ai1:bbba10;1;0;Lic0I1;ibi0;i20I41;if3:add2;10;0I1;i4;"
def bigBytes : String := bigHead ++ bigTail
def swappedHead : String := "M10:SCM-Core-02;15:range_violationi9:bad_inputR0;"
def small : String := "M10:SCM-Core-00;0;1;1;ii10;0;"
def rep (n : Nat) (s : String) : String := String.join (List.replicate n s)

def BIG : WireProg := ⟨prof, ExprPins.P⟩
def SMALL : WireProg := ⟨prof, ⟨[⟨[.i64], .i64, .var 0⟩], [], [], 0⟩⟩
def noProg : WireProg := ⟨"", ⟨[], [], [], 0⟩⟩

def ok (t : CoreTy) : WireOut := ⟨1, t, none, ""⟩
def no (code : String) : WireOut := ⟨0, unitTy, none, code⟩
def enc (b : String) : WireOut := ⟨1, unitTy, some b, ""⟩
def dec0 (b : String) (fuel : Int := 256) (p : String := prof) : WireOut := scmWire 0 fuel b noProg p

-- 0 canonical bytes of a program with every constructor family decode to a well-typed program
#guard dec0 bigBytes == ok .i64
-- 1 the encoder emits the canonical program bytes
#guard scmWire 1 256 "" BIG prof == enc bigBytes
-- 2 the small program encodes to its canonical bytes
#guard scmWire 1 256 "" SMALL prof == enc small
-- 3 trailing bytes after the entry ref refused
#guard dec0 (small ++ "0") == no "[rcic_scm_wire_trailing]"
-- 4 bytes truncated inside the entry ref refused
#guard dec0 "M10:SCM-Core-00;0;1;1;ii10;0" == no "[rcic_scm_wire_truncated]"
-- 5 empty bytes refused
#guard dec0 "" == no "[rcic_scm_wire_truncated]"
-- 6 bytes that do not start with the program tag refused
#guard dec0 "X10:SCM-Core-00;0;1;1;ii10;0;" == no "[rcic_scm_wire_tag]"
-- 7 unknown expression tag refused
#guard dec0 "M10:SCM-Core-00;0;1;1;iiz0;0;" == no "[rcic_scm_wire_tag]"
-- 8 unknown type tag refused
#guard dec0 "M10:SCM-Core-00;0;1;1;qi10;0;" == no "[rcic_scm_wire_tag]"
-- 9 a count with a leading zero decodes but does not re-encode exactly refused
#guard dec0 "M10:SCM-Core-00;00;1;1;ii10;0;" == no "[rcic_scm_wire_noncanonical]"
-- 10 an integer literal written -0 does not re-encode exactly refused
#guard dec0 "M10:SCM-Core-00;0;1;0;i0I-0;i0;" == no "[rcic_scm_wire_noncanonical]"
-- 11 a number with a non-digit refused
#guard dec0 "M10:SCM-Core-00;0;1a;1;ii10;0;" == no "[rcic_scm_wire_number]"
-- 12 a number with no terminator within the bound refused  (30 × '1' after "ii10;")
#guard dec0 ("M10:SCM-Core-00;0;1;1;ii10;" ++ rep 30 "1") == no "[rcic_scm_wire_number]"
-- 13 a list longer than the 1024 bound refused  (1025 × "0;")
#guard dec0 ("M10:SCM-Core-00;0;1;0;y0Y1025;" ++ rep 1025 "0;" ++ "y0;") == no "[rcic_scm_wire_bound]"
-- 14 decode fuel exhausted refused
#guard dec0 bigBytes 3 == no "[rcic_scm_wire_fuel]"
-- 15 a decoded local call to a function outside the group refused
#guard dec0 "M10:SCM-Core-00;0;1;0;igl9;0;0;" == no "[rcic_scm_typing_local_ref]"
-- 16 a decoded variable outside its de Bruijn scope refused
#guard dec0 "M10:SCM-Core-00;0;1;1;ii15;0;" == no "[rcic_scm_typing_var_scope]"
-- 17 a decoded body whose type differs from its signature refused
#guard dec0 "M10:SCM-Core-00;0;1;1;ib10;0;" == no "[rcic_scm_typing_mismatch]"
-- 18 a decoded residue catalog out of canonical order refused
#guard dec0 (swappedHead ++ bigTail) == no "[rcic_scm_typing_catalog]"
-- 19 bytes naming another semantics profile refused
#guard dec0 small 256 "SCM-Core-1" == no "[rcic_scm_wire_profile]"
-- 20 unknown value tag refused
#guard dec0 "M10:SCM-Core-00;0;1;0;i0Q7;i0;" == no "[rcic_scm_wire_tag]"
-- 21 unknown form refused
#guard scmWire 2 256 "" noProg prof == no "[rcic_scm_wire_unknown_form]"

end Rcic.Scm.WirePins
