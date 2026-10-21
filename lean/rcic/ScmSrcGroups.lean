/-
K3c regroup stage 1a — the 168-slot group-ordered source environment.
Hand-transcribed per the K3c regroup stage-1a spec (no generator — the
transcription itself is not trusted): carried members are
`renameMember πmap <old>`, the 14 NEW members are written fresh, and the
26 recursors are computed by the judgment's own functions
(`policyRecursorType` over `minorFromTelescope`/`fieldShapesFuel` minors)
on the prefix env ending at each family's last constructor.  The env is
tied to the judgment downstream by `kernel_rfl` leaves over
`iotaSchemaAt`/`fieldShapesFuel`/`iotaLhsType` (`ScmSrcGroupsRec`,
`…RecIdx`, `…FunRecTypedVA*`).

Two deliberate hand corrections to the carried V2/V3 objects:

* slot 102 `mCctP` — V2's second-component CCT premise `(bv 10) (bv 8)`
  re-asserted `CCT ra ta`, duplicating the fourth premise instead of
  binding the second component; corrected to `CCT rb tb`
  (`(bv 9) (bv 7)`).
* slot 142 `mVaR` — V3's record constructor omitted the `BLC vs xb`
  premise and left the value count untied; corrected by adding the
  premise and tying the value count to the field count `n`.
-/
import rcic.RcicIndGroupJudgment
import rcic.RcicMachine
import rcic.RcicSrcEnvV1
import rcic.ScmSrcGroupsOld

namespace Rcic.Scm.SrcG
open Rcic.Declarative Rcic.Machine
open Rcic.Scm.SrcTV

set_option maxRecDepth 8192

/-! ## The old→new ref map and member renaming -/

def πmap : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | 6 => 8
  | 7 => 9
  | 8 => 23
  | 9 => 96
  | 10 => 106
  | 11 => 133
  | 12 => 11
  | 13 => 12
  | 14 => 13
  | 15 => 14
  | 16 => 15
  | 17 => 16
  | 18 => 17
  | 19 => 18
  | 20 => 19
  | 21 => 20
  | 22 => 24
  | 23 => 25
  | 24 => 26
  | 25 => 27
  | 26 => 97
  | 27 => 98
  | 28 => 99
  | 29 => 100
  | 30 => 107
  | 31 => 109
  | 32 => 110
  | 33 => 111
  | 34 => 112
  | 35 => 113
  | 36 => 114
  | 37 => 115
  | 38 => 116
  | 39 => 117
  | 40 => 118
  | 41 => 119
  | 42 => 120
  | 43 => 134
  | 44 => 135
  | 45 => 144
  | 46 => 145
  | 47 => 30
  | 48 => 31
  | 49 => 32
  | 50 => 34
  | 51 => 35
  | 52 => 36
  | 53 => 38
  | 54 => 39
  | 55 => 40
  | 56 => 42
  | 57 => 43
  | 58 => 44
  | 59 => 46
  | 60 => 47
  | 61 => 48
  | 62 => 50
  | 63 => 51
  | 64 => 52
  | 65 => 54
  | 66 => 55
  | 67 => 56
  | 68 => 58
  | 69 => 59
  | 70 => 61
  | 71 => 62
  | 72 => 63
  | 73 => 65
  | 74 => 66
  | 75 => 67
  | 76 => 69
  | 77 => 70
  | 78 => 71
  | 79 => 73
  | 80 => 74
  | 81 => 75
  | 82 => 77
  | 83 => 78
  | 84 => 79
  | 85 => 81
  | 86 => 82
  | 87 => 84
  | 88 => 85
  | 89 => 86
  | 96 => 101
  | 97 => 102
  | 98 => 103
  | 99 => 104
  | 100 => 21
  | 101 => 22
  | 102 => 28
  | 103 => 121
  | 104 => 122
  | 105 => 123
  | 106 => 124
  | 107 => 125
  | 108 => 126
  | 109 => 127
  | 110 => 129
  | 111 => 130
  | 112 => 131
  | 119 => 136
  | 120 => 137
  | 121 => 138
  | 122 => 139
  | 123 => 140
  | 124 => 141
  | 125 => 142
  | 126 => 146
  | 127 => 147
  | 128 => 148
  | 129 => 149
  | 130 => 150
  | 131 => 151
  | 132 => 152
  | 133 => 153
  | 134 => 154
  | 135 => 155
  | 136 => 156
  | 137 => 157
  | 138 => 158
  | 139 => 159
  | 140 => 160
  | 141 => 161
  | 142 => 162
  | 143 => 163
  | 144 => 164
  | 145 => 165
  | 146 => 166
  | 147 => 167
  | _ => 9999

/-- The structural ref-map on expressions: only `.const r ls` changes. -/
def exprMapRef (f : Nat → Nat) : Expr Nat → Expr Nat
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls => .const (f r) ls
  | .app a b => .app (exprMapRef f a) (exprMapRef f b)
  | .lam a b => .lam (exprMapRef f a) (exprMapRef f b)
  | .pi a b => .pi (exprMapRef f a) (exprMapRef f b)
  | .letE a v b => .letE (exprMapRef f a) (exprMapRef f v) (exprMapRef f b)
  | .lit t => .lit t

/-- The carried member at the new slot: refs renamed by `f`, classes
    and body-`Option` structure otherwise untouched. -/
def renameMember (f : Nat → Nat) (m : CheckedMember) : CheckedMember :=
  { m with mtype := exprMapRef f m.mtype,
           body := m.body.map (exprMapRef f) }

/-- Literal expansion `.lit t ↦ natExpand t` (a pure syntax map —
    no delta/beta/zeta/iota; those remain the machine's work). -/
def expandLits : Expr Nat → Expr Nat
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .app a b => .app (expandLits a) (expandLits b)
  | .lam a b => .lam (expandLits a) (expandLits b)
  | .pi a b => .pi (expandLits a) (expandLits b)
  | .letE a v b => .letE (expandLits a) (expandLits v) (expandLits b)
  | .lit t => natExpand t

/-! ## NEW members (written fresh in the new numbering) -/

def mNthB : CheckedMember := ⟨.inductiveM, 0, .pi (.const 34 []) (.pi (.const 0 []) (.pi (.const 4 []) (.sort .zero))), none⟩

def mNthBHere : CheckedMember := ⟨.constructorM, 0, .pi (.const 4 []) (.pi (.const 34 []) (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 1)) (.bvar 0))) (.const 1 [])) (.bvar 1))), none⟩

def mNthBNext : CheckedMember := ⟨.constructorM, 0, .pi (.const 4 []) (.pi (.const 34 []) (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.app (.app (.app (.const 88 []) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 4)) (.bvar 3))) (.app (.const 2 []) (.bvar 2))) (.bvar 1)))))), none⟩

def mNthF : CheckedMember := ⟨.inductiveM, 0, .pi (.const 38 []) (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.const 4 []) (.sort .zero)))), none⟩

def mNthFHere : CheckedMember := ⟨.constructorM, 0, .pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 38 []) (.app (.app (.app (.app (.const 92 []) (.app (.app (.app (.const 40 []) (.bvar 2)) (.bvar 1)) (.bvar 0))) (.const 1 [])) (.bvar 2)) (.bvar 1)))), none⟩

def mNthFNext : CheckedMember := ⟨.constructorM, 0, .pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 38 []) (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.app (.app (.app (.app (.const 92 []) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.app (.const 92 []) (.app (.app (.app (.const 40 []) (.bvar 6)) (.bvar 5)) (.bvar 4))) (.app (.const 2 []) (.bvar 3))) (.bvar 2)) (.bvar 1)))))))), none⟩

/-- `cctP` — `Old.mCctP` with the second component's CCT premise
    corrected to `CCT rb tb` (`(bv 9) (bv 7)`): V2's `(bv 10) (bv 8)`
    re-asserted `CCT ra ta`, duplicating the fourth premise. -/
def mCctP : CheckedMember :=
  renameMember πmap
    (Old.ctorM
      (.pi (cst 6) (.pi (cst 6) (.pi (cst 3) (.pi (cst 3)
        (.pi (cst 3) (.pi (cst 3) (.pi (cst 3)
          (.pi (Old.bcE (Old.tB 80) (Old.bv 4) (Old.bv 2))
            (.pi (Old.bcE (Old.bv 3) (Old.bv 4) (Old.bv 2))
              (.pi (daE 3 16 (Old.bv 3) (Old.bv 2))
                (.pi (cctE (Old.bv 9) (Old.bv 7))
                  (.pi (cctE (Old.bv 9) (Old.bv 7))
                    (cctE (mkRefE 3 16 (Old.bv 5)) (Old.bv 6)))))))))))))))

def mCctSum : CheckedMember := ⟨.constructorM, 0, .pi (.const 34 []) (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.app (.app (.const 77 []) (.bvar 6)) (.bvar 4)) (.pi (.app (.app (.const 69 []) (.bvar 7)) (.bvar 6)) (.pi (.app (.app (.const 58 []) (.bvar 7)) (.bvar 5)) (.pi (.app (.app (.app (.const 46 []) (.app (.app (.const 6 []) (.lit 83)) (.const 5 []))) (.bvar 6)) (.bvar 5)) (.pi (.app (.app (.app (.const 46 []) (.bvar 6)) (.bvar 8)) (.bvar 5)) (.pi (.app (.app (.app (.app (.const 23 []) (.lit 3)) (.lit 16)) (.bvar 6)) (.bvar 5)) (.pi (.pi (.const 0 []) (.const 8 [])) (.pi (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.app (.app (.app (.const 88 []) (.bvar 15)) (.bvar 1)) (.bvar 0)) (.app (.app (.const 96 []) (.app (.bvar 3) (.bvar 2))) (.bvar 1))))) (.app (.app (.const 96 []) (.app (.app (.app (.const 9 []) (.lit 3)) (.lit 16)) (.bvar 8))) (.bvar 9)))))))))))))))), none⟩

def mCctRec : CheckedMember := ⟨.constructorM, 0, .pi (.const 38 []) (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.app (.app (.const 84 []) (.bvar 6)) (.bvar 4)) (.pi (.app (.app (.const 73 []) (.bvar 7)) (.bvar 6)) (.pi (.app (.app (.const 58 []) (.bvar 7)) (.bvar 5)) (.pi (.app (.app (.app (.const 46 []) (.app (.app (.const 6 []) (.lit 82)) (.const 5 []))) (.bvar 6)) (.bvar 5)) (.pi (.app (.app (.app (.const 46 []) (.bvar 6)) (.bvar 8)) (.bvar 5)) (.pi (.app (.app (.app (.app (.const 23 []) (.lit 3)) (.lit 16)) (.bvar 6)) (.bvar 5)) (.pi (.pi (.const 0 []) (.const 8 [])) (.pi (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.app (.app (.app (.app (.const 92 []) (.bvar 16)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.app (.app (.const 96 []) (.app (.bvar 4) (.bvar 3))) (.bvar 1)))))) (.app (.app (.const 96 []) (.app (.app (.app (.const 9 []) (.lit 3)) (.lit 16)) (.bvar 8))) (.bvar 9)))))))))))))))), none⟩

def mVaList : CheckedMember := ⟨.constructorM, 0, .pi (.const 8 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 34 []) (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.app (.app (.app (.const 46 []) (.app (.app (.const 6 []) (.lit 76)) (.const 5 []))) (.bvar 8)) (.bvar 7)) (.pi (.app (.app (.app (.app (.const 23 []) (.lit 3)) (.lit 16)) (.bvar 8)) (.bvar 7)) (.pi (.app (.app (.const 96 []) (.bvar 11)) (.bvar 10)) (.pi (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.app (.app (.app (.const 88 []) (.bvar 10)) (.bvar 1)) (.bvar 0)) (.app (.app (.const 133 []) (.app (.app (.app (.const 107 []) (.bvar 15)) (.bvar 14)) (.bvar 3))) (.bvar 1))))) (.pi (.app (.app (.const 69 []) (.bvar 9)) (.bvar 8)) (.pi (.app (.app (.const 77 []) (.bvar 10)) (.bvar 6)) (.pi (.app (.app (.const 58 []) (.bvar 10)) (.bvar 8)) (.pi (.app (.app (.app (.const 46 []) (.app (.app (.const 6 []) (.lit 76)) (.const 5 []))) (.bvar 9)) (.bvar 10)) (.pi (.app (.app (.app (.const 46 []) (.bvar 11)) (.bvar 9)) (.bvar 8)) (.app (.app (.const 133 []) (.app (.app (.app (.const 107 []) (.app (.app (.app (.const 9 []) (.lit 3)) (.lit 16)) (.bvar 15))) (.bvar 16)) (.app (.app (.app (.app (.app (.app (.app (.const 101 []) (.bvar 18)) (.bvar 17)) (.bvar 16)) (.bvar 15)) (.bvar 8)) (.bvar 7)) (.bvar 6)))) (.bvar 9)))))))))))))))))))), none⟩

def mVaJ : CheckedMember := ⟨.constructorM, 0, .pi (.const 34 []) (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.app (.app (.const 77 []) (.bvar 6)) (.bvar 4)) (.pi (.app (.app (.const 69 []) (.bvar 7)) (.bvar 6)) (.pi (.app (.app (.const 58 []) (.bvar 7)) (.bvar 5)) (.pi (.app (.app (.app (.const 46 []) (.app (.app (.const 6 []) (.lit 83)) (.const 5 []))) (.bvar 6)) (.bvar 5)) (.pi (.app (.app (.app (.const 46 []) (.bvar 6)) (.bvar 8)) (.bvar 5)) (.pi (.app (.app (.app (.app (.const 23 []) (.lit 3)) (.lit 16)) (.bvar 6)) (.bvar 5)) (.pi (.pi (.const 0 []) (.const 8 [])) (.pi (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.app (.app (.app (.const 88 []) (.bvar 15)) (.bvar 1)) (.bvar 0)) (.app (.app (.const 96 []) (.app (.bvar 3) (.bvar 2))) (.bvar 1))))) (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.const 106 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.app (.app (.app (.const 129 []) (.bvar 20)) (.bvar 5)) (.bvar 3)) (.pi (.app (.app (.const 133 []) (.bvar 4)) (.bvar 3)) (.pi (.app (.app (.const 58 []) (.bvar 7)) (.bvar 6)) (.pi (.app (.app (.app (.const 46 []) (.app (.app (.const 6 []) (.lit 74)) (.const 5 []))) (.bvar 7)) (.bvar 4)) (.pi (.app (.app (.app (.const 46 []) (.bvar 5)) (.bvar 6)) (.bvar 4)) (.app (.app (.const 133 []) (.app (.app (.app (.const 107 []) (.app (.app (.app (.const 9 []) (.lit 3)) (.lit 16)) (.bvar 19))) (.bvar 20)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 103 []) (.bvar 25)) (.bvar 24)) (.bvar 23)) (.bvar 22)) (.bvar 21)) (.bvar 20)) (.bvar 19)) (.bvar 18)) (.bvar 17)) (.bvar 16)) (.bvar 15)) (.bvar 14)) (.bvar 13)) (.bvar 12)) (.bvar 11)))) (.bvar 5))))))))))))))))))))))))))), none⟩

def mVaR : CheckedMember := ⟨.constructorM, 0, .pi (.const 38 []) (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.app (.app (.const 84 []) (.bvar 6)) (.bvar 4)) (.pi (.app (.app (.const 73 []) (.bvar 7)) (.bvar 6)) (.pi (.app (.app (.const 58 []) (.bvar 7)) (.bvar 5)) (.pi (.app (.app (.app (.const 46 []) (.app (.app (.const 6 []) (.lit 82)) (.const 5 []))) (.bvar 6)) (.bvar 5)) (.pi (.app (.app (.app (.const 46 []) (.bvar 6)) (.bvar 8)) (.bvar 5)) (.pi (.app (.app (.app (.app (.const 23 []) (.lit 3)) (.lit 16)) (.bvar 6)) (.bvar 5)) (.pi (.pi (.const 0 []) (.const 8 [])) (.pi (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.app (.app (.app (.app (.const 92 []) (.bvar 16)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.app (.app (.const 96 []) (.app (.bvar 4) (.bvar 3))) (.bvar 1)))))) (.pi (.const 34 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.pi (.const 0 []) (.pi (.const 4 []) (.pi (.const 4 []) (.pi (.app (.app (.app (.app (.const 92 []) (.bvar 22)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.pi (.const 4 []) (.pi (.app (.app (.app (.const 88 []) (.bvar 9)) (.bvar 4)) (.bvar 0)) (.app (.app (.const 133 []) (.app (.app (.app (.const 107 []) (.app (.bvar 12) (.bvar 5))) (.bvar 3)) (.app (.app (.app (.app (.bvar 11) (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2)))) (.bvar 1)))))))) (.pi (.app (.app (.const 69 []) (.bvar 5)) (.bvar 19)) (.pi (.app (.app (.const 77 []) (.bvar 6)) (.bvar 4)) (.pi (.app (.app (.const 58 []) (.bvar 21)) (.bvar 6)) (.pi (.app (.app (.app (.const 46 []) (.app (.app (.const 6 []) (.lit 82)) (.const 5 []))) (.bvar 7)) (.bvar 5)) (.pi (.app (.app (.app (.const 46 []) (.bvar 6)) (.bvar 7)) (.bvar 5)) (.app (.app (.const 133 []) (.app (.app (.app (.const 107 []) (.app (.app (.app (.const 9 []) (.lit 3)) (.lit 16)) (.bvar 19))) (.bvar 20)) (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 104 []) (.bvar 25)) (.bvar 24)) (.bvar 23)) (.bvar 22)) (.bvar 21)) (.bvar 20)) (.bvar 19)) (.bvar 18)) (.bvar 17)) (.bvar 16)) (.bvar 15)) (.bvar 14)) (.bvar 13)) (.bvar 12)) (.bvar 11)))) (.bvar 6))))))))))))))))))))))))))), none⟩

def mNthBNilVa : CheckedMember := ⟨.theoremM, 0, .pi (.const 0 []) (.pi (.const 4 []) (.pi (.app (.app (.app (.const 88 []) (.const 35 [])) (.bvar 1)) (.bvar 0)) (.app (.app (.const 133 []) (.app (.app (.app (.const 107 []) (.const 110 [])) (.const 12 [])) (.const 114 []))) (.bvar 1)))), some (.lam (.const 0 []) (.lam (.const 4 []) (.lam (.app (.app (.app (.const 88 []) (.const 35 [])) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.app (.app (.app (.app (.const 91 []) (.lam (.const 34 []) (.lam (.const 0 []) (.lam (.const 4 []) (.lam (.app (.app (.app (.const 88 []) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.app (.const 37 [.succ .zero]) (.lam (.const 34 []) (.sort .zero))) (.app (.app (.const 133 []) (.app (.app (.app (.const 107 []) (.const 110 [])) (.const 12 [])) (.const 114 []))) (.bvar 1))) (.lam (.const 4 []) (.lam (.const 34 []) (.lam (.sort .zero) (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1))) (.bvar 5)) (.bvar 4)))))) (.bvar 3))))))) (.lam (.const 4 []) (.lam (.const 34 []) (.app (.app (.const 89 []) (.bvar 1)) (.bvar 0))))) (.lam (.const 4 []) (.lam (.const 34 []) (.lam (.const 0 []) (.lam (.const 4 []) (.lam (.app (.app (.app (.const 88 []) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.lam (.app (.app (.app (.app (.lam (.const 34 []) (.lam (.const 0 []) (.lam (.const 4 []) (.lam (.app (.app (.app (.const 88 []) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.app (.const 37 [.succ .zero]) (.lam (.const 34 []) (.sort .zero))) (.app (.app (.const 133 []) (.app (.app (.app (.const 107 []) (.const 110 [])) (.const 12 [])) (.const 114 []))) (.bvar 1))) (.lam (.const 4 []) (.lam (.const 34 []) (.lam (.sort .zero) (.app (.app (.app (.const 88 []) (.app (.app (.const 36 []) (.bvar 2)) (.bvar 1))) (.bvar 5)) (.bvar 4)))))) (.bvar 3)))))) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.app (.app (.app (.app (.app (.const 90 []) (.bvar 5)) (.bvar 4)) (.bvar 3)) (.bvar 2)) (.bvar 1))))))))) (.const 35 [])) (.bvar 2)) (.bvar 1)) (.bvar 0)))))⟩

def mVLBNil : CheckedMember := ⟨.theoremM, 0, .app (.app (.const 133 []) (.const 124 [])) (.const 149 []), some (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.app (.const 139 []) (.const 110 [])) (.const 12 [])) (.const 21 [])) (.const 22 [])) (.const 35 [])) (.lit 0)) (.const 149 [])) (.const 148 [])) (.const 5 [])) (.const 149 [])) (.const 121 [])) (.const 28 [])) (.const 114 [])) (.const 159 [])) (.const 70 [])) (.const 78 [])) (.const 156 [])) (.const 157 [])) (.const 158 []))⟩

/-! ## Carried member defs — `renameMember πmap <old>` -/

def mN : CheckedMember := renameMember πmap SrcTV.mNatF

def mZero : CheckedMember := renameMember πmap SrcTV.mZero

def mSucc : CheckedMember := renameMember πmap SrcTV.mSucc

def mBytes : CheckedMember := renameMember πmap SrcTV.mBytesF

def mBnil : CheckedMember := renameMember πmap SrcTV.mBNil

def mBcons : CheckedMember := renameMember πmap SrcTV.mBCons

def mRefT : CheckedMember := renameMember πmap SrcTV.mRefF

def mMkRef : CheckedMember := renameMember πmap SrcTV.mMkRef

def mBytesI : CheckedMember := renameMember πmap SrcTV.mBytesI

def mBytesB : CheckedMember := renameMember πmap SrcTV.mBytesB

def mBytesS : CheckedMember := renameMember πmap SrcTV.mBytesS

def mBytesY : CheckedMember := renameMember πmap SrcTV.mBytesY

def mBytesB0 : CheckedMember := renameMember πmap SrcTV.mBytesB0

def mBytesB1 : CheckedMember := renameMember πmap SrcTV.mBytesB1

def mDigestI : CheckedMember := renameMember πmap SrcTV.mDigestI

def mDigestB : CheckedMember := renameMember πmap SrcTV.mDigestB

def mDigestS : CheckedMember := renameMember πmap SrcTV.mDigestS

def mDigestY : CheckedMember := renameMember πmap SrcTV.mDigestY

def mBytesLB : CheckedMember := renameMember πmap Old.mBytesLB

def mDigestLB : CheckedMember := renameMember πmap Old.mDigestLB

def mDA : CheckedMember := renameMember πmap SrcTV.mDA

def mDaI : CheckedMember := renameMember πmap SrcTV.mDaI

def mDaB : CheckedMember := renameMember πmap SrcTV.mDaB

def mDaS : CheckedMember := renameMember πmap SrcTV.mDaS

def mDaY : CheckedMember := renameMember πmap SrcTV.mDaY

def mDaLB : CheckedMember := renameMember πmap Old.mDaLB

def mI : CheckedMember := renameMember πmap Old.mIF

def mIPos : CheckedMember := renameMember πmap Old.mIPos

def mINegS : CheckedMember := renameMember πmap Old.mINeg

def mBL : CheckedMember := renameMember πmap Old.mBLF

def mBlNil : CheckedMember := renameMember πmap Old.mBLNil

def mBlCons : CheckedMember := renameMember πmap Old.mBLCons

def mFT : CheckedMember := renameMember πmap Old.mFTF

def mFtNil : CheckedMember := renameMember πmap Old.mFTNil

def mFtCons : CheckedMember := renameMember πmap Old.mFTCons

def mLt : CheckedMember := renameMember πmap Old.mLtF

def mLtBase : CheckedMember := renameMember πmap Old.mLtB

def mLtStep : CheckedMember := renameMember πmap Old.mLtS

def mBC : CheckedMember := renameMember πmap Old.mBCF

def mCatNil : CheckedMember := renameMember πmap Old.mCatNil

def mCatCons : CheckedMember := renameMember πmap Old.mCatCons

def mDM10 : CheckedMember := renameMember πmap Old.mDM10F

def mDmBase : CheckedMember := renameMember πmap Old.mDmBase

def mDmStep : CheckedMember := renameMember πmap Old.mDmStep

def mND : CheckedMember := renameMember πmap Old.mNDF

def mNdBase : CheckedMember := renameMember πmap Old.mNdBase

def mNdStep : CheckedMember := renameMember πmap Old.mNdStep

def mNEA : CheckedMember := renameMember πmap Old.mNEAF

def mNeIntro : CheckedMember := renameMember πmap Old.mNeIntro

def mIEA : CheckedMember := renameMember πmap Old.mIEAF

def mIePos : CheckedMember := renameMember πmap Old.mIePos

def mIeNeg : CheckedMember := renameMember πmap Old.mIeNeg

def mSL : CheckedMember := renameMember πmap Old.mSLF

def mSlNil : CheckedMember := renameMember πmap Old.mSlNil

def mSlCons : CheckedMember := renameMember πmap Old.mSlCons

def mBLL : CheckedMember := renameMember πmap Old.mBLLF

def mBllNil : CheckedMember := renameMember πmap Old.mBllNil

def mBllCons : CheckedMember := renameMember πmap Old.mBllCons

def mFTL : CheckedMember := renameMember πmap Old.mFTLF

def mFtlNil : CheckedMember := renameMember πmap Old.mFtlNil

def mFtlCons : CheckedMember := renameMember πmap Old.mFtlCons

def mBLC : CheckedMember := renameMember πmap Old.mBLCF

def mBlcNil : CheckedMember := renameMember πmap Old.mBlcNil

def mBlcCons : CheckedMember := renameMember πmap Old.mBlcCons

def mSEA : CheckedMember := renameMember πmap Old.mSEAF

def mSeIntro : CheckedMember := renameMember πmap Old.mSeIntro

def mFTE : CheckedMember := renameMember πmap Old.mFTEF

def mFteNil : CheckedMember := renameMember πmap Old.mFteNil

def mFteCons : CheckedMember := renameMember πmap Old.mFteCons

def mCCT : CheckedMember := renameMember πmap SrcTV.mCCT

def mCctI : CheckedMember := renameMember πmap SrcTV.mCctI

def mCctB : CheckedMember := renameMember πmap SrcTV.mCctB

def mCctStr : CheckedMember := renameMember πmap SrcTV.mCctS

def mCctY : CheckedMember := renameMember πmap SrcTV.mCctY

def mCctL : CheckedMember := renameMember πmap Old.mCctL

def mBCT : CheckedMember := renameMember πmap SrcTV.mBCT

def mMkBound : CheckedMember := renameMember πmap SrcTV.mMkBound

def mI64Ref : CheckedMember := renameMember πmap SrcTV.mI64Ref

def mBoolRef : CheckedMember := renameMember πmap SrcTV.mBoolRef

def mStrRef : CheckedMember := renameMember πmap SrcTV.mStrRef

def mBytesRef : CheckedMember := renameMember πmap SrcTV.mBytesRef

def mCctI64Pf : CheckedMember := renameMember πmap SrcTV.mCctI64Pf

def mCctBoolPf : CheckedMember := renameMember πmap SrcTV.mCctBoolPf

def mCctStrPf : CheckedMember := renameMember πmap SrcTV.mCctStrPf

def mCctBytesPf : CheckedMember := renameMember πmap SrcTV.mCctBytesPf

def mBoundI64 : CheckedMember := renameMember πmap SrcTV.mBoundI64

def mBoundBool : CheckedMember := renameMember πmap SrcTV.mBoundBool

def mBoundStr : CheckedMember := renameMember πmap SrcTV.mBoundStr

def mBoundBytes : CheckedMember := renameMember πmap SrcTV.mBoundBytes

def mBcLB : CheckedMember := renameMember πmap Old.mBcLB

def mLbRef : CheckedMember := renameMember πmap Old.mLbRef

def mCctLbPf : CheckedMember := renameMember πmap Old.mCctLbPf

def mBoundListBool : CheckedMember := renameMember πmap Old.mBoundListBool

def mNEL : CheckedMember := renameMember πmap Old.mNELF

def mNelNil : CheckedMember := renameMember πmap Old.mNelNil

def mNelCons : CheckedMember := renameMember πmap Old.mNelCons

def mNTB : CheckedMember := renameMember πmap Old.mNTBF

def mNtbHere : CheckedMember := renameMember πmap Old.mNtbHere

def mNtbNext : CheckedMember := renameMember πmap Old.mNtbNext

def mValueAt : CheckedMember := renameMember πmap SrcTV.mVA

def mVaB0 : CheckedMember := renameMember πmap SrcTV.mVaB0

def mVaB1 : CheckedMember := renameMember πmap SrcTV.mVaB1

def mVaI64 : CheckedMember := renameMember πmap Old.mVaI64

def mVaStr : CheckedMember := renameMember πmap Old.mVaStr

def mVaY : CheckedMember := renameMember πmap Old.mVaY

def mVaPair : CheckedMember := renameMember πmap Old.mVaPair

def mVb0 : CheckedMember := renameMember πmap SrcTV.mVb0

def mVb1 : CheckedMember := renameMember πmap SrcTV.mVb1

def mBytesSemi : CheckedMember := renameMember πmap Old.mBytesSemi

def mBytesD0 : CheckedMember := renameMember πmap Old.mBytesD0

def mBytesNat0 : CheckedMember := renameMember πmap Old.mBytesNat0

def mBytesVLB0 : CheckedMember := renameMember πmap Old.mBytesVLB0

def mBytesI5 : CheckedMember := renameMember πmap Old.mBytesI5

def mBytesD5 : CheckedMember := renameMember πmap Old.mBytesD5

def mBytesNat5 : CheckedMember := renameMember πmap Old.mBytesNat5

def mLt010 : CheckedMember := renameMember πmap Old.mLt010

def mNd0 : CheckedMember := renameMember πmap Old.mNd0

def mBc48S : CheckedMember := renameMember πmap Old.mBc48S

def mNea0 : CheckedMember := renameMember πmap Old.mNea0

def mBcLN0 : CheckedMember := renameMember πmap Old.mBcLN0

def mBcL0Nil : CheckedMember := renameMember πmap Old.mBcL0Nil

def mLt510 : CheckedMember := renameMember πmap Old.mLt510

def mNd5 : CheckedMember := renameMember πmap Old.mNd5

def mBc53S : CheckedMember := renameMember πmap Old.mBc53S

def mNea5 : CheckedMember := renameMember πmap Old.mNea5

def mIeaP5 : CheckedMember := renameMember πmap Old.mIeaP5

def mBcI5 : CheckedMember := renameMember πmap Old.mBcI5

def mVI5 : CheckedMember := renameMember πmap Old.mVI5

/-! ## Telescope/minor helpers -/

def ctorDom (m : CheckedMember) : List (Expr Nat) :=
  match peelPis (piCount m.mtype) m.mtype with
  | some (ds, _) => ds | none => []

def ctorIdx (m : CheckedMember) : List (Expr Nat) :=
  (appsSpine (piResult m.mtype)).2

private def domTy {E : ResolvedEnv} (Γ : LCtx) (r : Nat) {m : CheckedMember}
    (hm : E.members r = some m) (ht : m.mtype = .sort (.succ .zero))
    (ha : m.arity = 0) :
    HasTy E 0 Γ (.const r []) (.sort (.succ .zero)) :=
  ht ▸ instantiateLevels_nil m.mtype ▸
    HasTy.const Γ r [] m hm (by simp [ha]) (fun _ h => nomatch h)

private def domTel {E : ResolvedEnv} (ds : List (Expr Nat))
    (ht : ∀ j : Fin ds.length,
      HasTy E 0 (policyPrefixContext ds j.val) ds[j.val] (.sort (.succ .zero))) :
    PolicyTelescopeTyping E 0 ds where
  levels := fun _ => .succ .zero
  bounded := fun _ => rfl
  hasType := ht


def pre_0 : ResolvedEnv := emptyEnv

def pre_3 : ResolvedEnv :=
  [(0, mN), (1, mZero), (2, mSucc)].foldl (fun E (r, m) => extendEnv E r m) pre_0

def famViewN : PolicyFamilyView pre_3 where
  ref := 0
  member := mN
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def shapesZero : List FieldShape :=
  (fieldShapesFuel pre_3 96 0 0 0 0 0 (ctorDom mZero)).get (by decide)
def minorZero : Expr Nat :=
  (minorFromTelescope pre_3 96 0 (.bvar 0) (.const 1 []) shapesZero
    (lift 0 (1+0) (policyPi (ctorDom mZero)
      (foldApps (.const 0 []) (ctorIdx mZero))))).get (by decide)
theorem minorZero_isSome :
    (minorFromTelescope pre_3 96 0 (.bvar 0) (.const 1 []) shapesZero
      (lift 0 (1+0) (policyPi (ctorDom mZero)
        (foldApps (.const 0 []) (ctorIdx mZero))))).isSome = true := by decide

def shapesSucc : List FieldShape :=
  (fieldShapesFuel pre_3 96 0 0 0 0 0 (ctorDom mSucc)).get (by decide)
def minorSucc : Expr Nat :=
  (minorFromTelescope pre_3 96 0 (.bvar 1) (.const 2 []) shapesSucc
    (lift 0 (1+1) (policyPi (ctorDom mSucc)
      (foldApps (.const 0 []) (ctorIdx mSucc))))).get (by decide)
theorem minorSucc_isSome :
    (minorFromTelescope pre_3 96 0 (.bvar 1) (.const 2 []) shapesSucc
      (lift 0 (1+1) (policyPi (ctorDom mSucc)
        (foldApps (.const 0 []) (ctorIdx mSucc))))).isSome = true := by decide

def recN : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .anySort,
    policyRecursorType famViewN [minorZero, minorSucc] .anySort, none⟩

def pre_7 : ResolvedEnv :=
  [(3, recN), (4, mBytes), (5, mBnil), (6, mBcons)].foldl (fun E (r, m) => extendEnv E r m) pre_3

def famViewBytes : PolicyFamilyView pre_7 where
  ref := 4
  member := mBytes
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def shapesBnil : List FieldShape :=
  (fieldShapesFuel pre_7 96 4 0 0 0 0 (ctorDom mBnil)).get (by decide)
def minorBnil : Expr Nat :=
  (minorFromTelescope pre_7 96 0 (.bvar 0) (.const 5 []) shapesBnil
    (lift 0 (1+0) (policyPi (ctorDom mBnil)
      (foldApps (.const 4 []) (ctorIdx mBnil))))).get (by decide)
theorem minorBnil_isSome :
    (minorFromTelescope pre_7 96 0 (.bvar 0) (.const 5 []) shapesBnil
      (lift 0 (1+0) (policyPi (ctorDom mBnil)
        (foldApps (.const 4 []) (ctorIdx mBnil))))).isSome = true := by decide

def shapesBcons : List FieldShape :=
  (fieldShapesFuel pre_7 96 4 0 0 0 0 (ctorDom mBcons)).get (by decide)
def minorBcons : Expr Nat :=
  (minorFromTelescope pre_7 96 0 (.bvar 1) (.const 6 []) shapesBcons
    (lift 0 (1+1) (policyPi (ctorDom mBcons)
      (foldApps (.const 4 []) (ctorIdx mBcons))))).get (by decide)
theorem minorBcons_isSome :
    (minorFromTelescope pre_7 96 0 (.bvar 1) (.const 6 []) shapesBcons
      (lift 0 (1+1) (policyPi (ctorDom mBcons)
        (foldApps (.const 4 []) (ctorIdx mBcons))))).isSome = true := by decide

def recBytes : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .anySort,
    policyRecursorType famViewBytes [minorBnil, minorBcons] .anySort, none⟩

def pre_10 : ResolvedEnv :=
  [(7, recBytes), (8, mRefT), (9, mMkRef)].foldl (fun E (r, m) => extendEnv E r m) pre_7

def famViewRefT : PolicyFamilyView pre_10 where
  ref := 8
  member := mRefT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def shapesMkRef : List FieldShape :=
  (fieldShapesFuel pre_10 96 8 0 0 0 0 (ctorDom mMkRef)).get (by decide)
def minorMkRef : Expr Nat :=
  (minorFromTelescope pre_10 96 0 (.bvar 0) (.const 9 []) shapesMkRef
    (lift 0 (1+0) (policyPi (ctorDom mMkRef)
      (foldApps (.const 8 []) (ctorIdx mMkRef))))).get (by decide)
theorem minorMkRef_isSome :
    (minorFromTelescope pre_10 96 0 (.bvar 0) (.const 9 []) shapesMkRef
      (lift 0 (1+0) (policyPi (ctorDom mMkRef)
        (foldApps (.const 8 []) (ctorIdx mMkRef))))).isSome = true := by decide

def recRefT : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .anySort,
    policyRecursorType famViewRefT [minorMkRef] .anySort, none⟩

def pre_29 : ResolvedEnv :=
  [(10, recRefT), (11, mBytesI), (12, mBytesB), (13, mBytesS), (14, mBytesY), (15, mBytesB0), (16, mBytesB1), (17, mDigestI), (18, mDigestB), (19, mDigestS), (20, mDigestY), (21, mBytesLB), (22, mDigestLB), (23, mDA), (24, mDaI), (25, mDaB), (26, mDaS), (27, mDaY), (28, mDaLB)].foldl (fun E (r, m) => extendEnv E r m) pre_10

def famViewDA : PolicyFamilyView pre_29 where
  ref := 23
  member := mDA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 0 [], .const 0 [], .const 4 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨2, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨3, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+4, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesDaI : List FieldShape :=
  (fieldShapesFuel pre_29 96 23 0 0 4 0 (ctorDom mDaI)).get (by decide)
def minorDaI : Expr Nat :=
  (minorFromTelescope pre_29 96 0 (.bvar 0) (.const 24 []) shapesDaI
    (lift 0 (1+0) (policyPi (ctorDom mDaI)
      (foldApps (.const 23 []) (ctorIdx mDaI))))).get (by decide)
theorem minorDaI_isSome :
    (minorFromTelescope pre_29 96 0 (.bvar 0) (.const 24 []) shapesDaI
      (lift 0 (1+0) (policyPi (ctorDom mDaI)
        (foldApps (.const 23 []) (ctorIdx mDaI))))).isSome = true := by decide

def shapesDaB : List FieldShape :=
  (fieldShapesFuel pre_29 96 23 0 0 4 0 (ctorDom mDaB)).get (by decide)
def minorDaB : Expr Nat :=
  (minorFromTelescope pre_29 96 0 (.bvar 1) (.const 25 []) shapesDaB
    (lift 0 (1+1) (policyPi (ctorDom mDaB)
      (foldApps (.const 23 []) (ctorIdx mDaB))))).get (by decide)
theorem minorDaB_isSome :
    (minorFromTelescope pre_29 96 0 (.bvar 1) (.const 25 []) shapesDaB
      (lift 0 (1+1) (policyPi (ctorDom mDaB)
        (foldApps (.const 23 []) (ctorIdx mDaB))))).isSome = true := by decide

def shapesDaS : List FieldShape :=
  (fieldShapesFuel pre_29 96 23 0 0 4 0 (ctorDom mDaS)).get (by decide)
def minorDaS : Expr Nat :=
  (minorFromTelescope pre_29 96 0 (.bvar 2) (.const 26 []) shapesDaS
    (lift 0 (1+2) (policyPi (ctorDom mDaS)
      (foldApps (.const 23 []) (ctorIdx mDaS))))).get (by decide)
theorem minorDaS_isSome :
    (minorFromTelescope pre_29 96 0 (.bvar 2) (.const 26 []) shapesDaS
      (lift 0 (1+2) (policyPi (ctorDom mDaS)
        (foldApps (.const 23 []) (ctorIdx mDaS))))).isSome = true := by decide

def shapesDaY : List FieldShape :=
  (fieldShapesFuel pre_29 96 23 0 0 4 0 (ctorDom mDaY)).get (by decide)
def minorDaY : Expr Nat :=
  (minorFromTelescope pre_29 96 0 (.bvar 3) (.const 27 []) shapesDaY
    (lift 0 (1+3) (policyPi (ctorDom mDaY)
      (foldApps (.const 23 []) (ctorIdx mDaY))))).get (by decide)
theorem minorDaY_isSome :
    (minorFromTelescope pre_29 96 0 (.bvar 3) (.const 27 []) shapesDaY
      (lift 0 (1+3) (policyPi (ctorDom mDaY)
        (foldApps (.const 23 []) (ctorIdx mDaY))))).isSome = true := by decide

def shapesDaLB : List FieldShape :=
  (fieldShapesFuel pre_29 96 23 0 0 4 0 (ctorDom mDaLB)).get (by decide)
def minorDaLB : Expr Nat :=
  (minorFromTelescope pre_29 96 0 (.bvar 4) (.const 28 []) shapesDaLB
    (lift 0 (1+4) (policyPi (ctorDom mDaLB)
      (foldApps (.const 23 []) (ctorIdx mDaLB))))).get (by decide)
theorem minorDaLB_isSome :
    (minorFromTelescope pre_29 96 0 (.bvar 4) (.const 28 []) shapesDaLB
      (lift 0 (1+4) (policyPi (ctorDom mDaLB)
        (foldApps (.const 23 []) (ctorIdx mDaLB))))).isSome = true := by decide

def recDA : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewDA [minorDaI, minorDaB, minorDaS, minorDaY, minorDaLB] .propOnly, none⟩

def pre_33 : ResolvedEnv :=
  [(29, recDA), (30, mI), (31, mIPos), (32, mINegS)].foldl (fun E (r, m) => extendEnv E r m) pre_29

def famViewI : PolicyFamilyView pre_33 where
  ref := 30
  member := mI
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def shapesIPos : List FieldShape :=
  (fieldShapesFuel pre_33 96 30 0 0 0 0 (ctorDom mIPos)).get (by decide)
def minorIPos : Expr Nat :=
  (minorFromTelescope pre_33 96 0 (.bvar 0) (.const 31 []) shapesIPos
    (lift 0 (1+0) (policyPi (ctorDom mIPos)
      (foldApps (.const 30 []) (ctorIdx mIPos))))).get (by decide)
theorem minorIPos_isSome :
    (minorFromTelescope pre_33 96 0 (.bvar 0) (.const 31 []) shapesIPos
      (lift 0 (1+0) (policyPi (ctorDom mIPos)
        (foldApps (.const 30 []) (ctorIdx mIPos))))).isSome = true := by decide

def shapesINegS : List FieldShape :=
  (fieldShapesFuel pre_33 96 30 0 0 0 0 (ctorDom mINegS)).get (by decide)
def minorINegS : Expr Nat :=
  (minorFromTelescope pre_33 96 0 (.bvar 1) (.const 32 []) shapesINegS
    (lift 0 (1+1) (policyPi (ctorDom mINegS)
      (foldApps (.const 30 []) (ctorIdx mINegS))))).get (by decide)
theorem minorINegS_isSome :
    (minorFromTelescope pre_33 96 0 (.bvar 1) (.const 32 []) shapesINegS
      (lift 0 (1+1) (policyPi (ctorDom mINegS)
        (foldApps (.const 30 []) (ctorIdx mINegS))))).isSome = true := by decide

def recI : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .anySort,
    policyRecursorType famViewI [minorIPos, minorINegS] .anySort, none⟩

def pre_37 : ResolvedEnv :=
  [(33, recI), (34, mBL), (35, mBlNil), (36, mBlCons)].foldl (fun E (r, m) => extendEnv E r m) pre_33

def famViewBL : PolicyFamilyView pre_37 where
  ref := 34
  member := mBL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def shapesBlNil : List FieldShape :=
  (fieldShapesFuel pre_37 96 34 0 0 0 0 (ctorDom mBlNil)).get (by decide)
def minorBlNil : Expr Nat :=
  (minorFromTelescope pre_37 96 0 (.bvar 0) (.const 35 []) shapesBlNil
    (lift 0 (1+0) (policyPi (ctorDom mBlNil)
      (foldApps (.const 34 []) (ctorIdx mBlNil))))).get (by decide)
theorem minorBlNil_isSome :
    (minorFromTelescope pre_37 96 0 (.bvar 0) (.const 35 []) shapesBlNil
      (lift 0 (1+0) (policyPi (ctorDom mBlNil)
        (foldApps (.const 34 []) (ctorIdx mBlNil))))).isSome = true := by decide

def shapesBlCons : List FieldShape :=
  (fieldShapesFuel pre_37 96 34 0 0 0 0 (ctorDom mBlCons)).get (by decide)
def minorBlCons : Expr Nat :=
  (minorFromTelescope pre_37 96 0 (.bvar 1) (.const 36 []) shapesBlCons
    (lift 0 (1+1) (policyPi (ctorDom mBlCons)
      (foldApps (.const 34 []) (ctorIdx mBlCons))))).get (by decide)
theorem minorBlCons_isSome :
    (minorFromTelescope pre_37 96 0 (.bvar 1) (.const 36 []) shapesBlCons
      (lift 0 (1+1) (policyPi (ctorDom mBlCons)
        (foldApps (.const 34 []) (ctorIdx mBlCons))))).isSome = true := by decide

def recBL : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .anySort,
    policyRecursorType famViewBL [minorBlNil, minorBlCons] .anySort, none⟩

def pre_41 : ResolvedEnv :=
  [(37, recBL), (38, mFT), (39, mFtNil), (40, mFtCons)].foldl (fun E (r, m) => extendEnv E r m) pre_37

def famViewFT : PolicyFamilyView pre_41 where
  ref := 38
  member := mFT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def shapesFtNil : List FieldShape :=
  (fieldShapesFuel pre_41 96 38 0 0 0 0 (ctorDom mFtNil)).get (by decide)
def minorFtNil : Expr Nat :=
  (minorFromTelescope pre_41 96 0 (.bvar 0) (.const 39 []) shapesFtNil
    (lift 0 (1+0) (policyPi (ctorDom mFtNil)
      (foldApps (.const 38 []) (ctorIdx mFtNil))))).get (by decide)
theorem minorFtNil_isSome :
    (minorFromTelescope pre_41 96 0 (.bvar 0) (.const 39 []) shapesFtNil
      (lift 0 (1+0) (policyPi (ctorDom mFtNil)
        (foldApps (.const 38 []) (ctorIdx mFtNil))))).isSome = true := by decide

def shapesFtCons : List FieldShape :=
  (fieldShapesFuel pre_41 96 38 0 0 0 0 (ctorDom mFtCons)).get (by decide)
def minorFtCons : Expr Nat :=
  (minorFromTelescope pre_41 96 0 (.bvar 1) (.const 40 []) shapesFtCons
    (lift 0 (1+1) (policyPi (ctorDom mFtCons)
      (foldApps (.const 38 []) (ctorIdx mFtCons))))).get (by decide)
theorem minorFtCons_isSome :
    (minorFromTelescope pre_41 96 0 (.bvar 1) (.const 40 []) shapesFtCons
      (lift 0 (1+1) (policyPi (ctorDom mFtCons)
        (foldApps (.const 38 []) (ctorIdx mFtCons))))).isSome = true := by decide

def recFT : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .anySort,
    policyRecursorType famViewFT [minorFtNil, minorFtCons] .anySort, none⟩

def pre_45 : ResolvedEnv :=
  [(41, recFT), (42, mLt), (43, mLtBase), (44, mLtStep)].foldl (fun E (r, m) => extendEnv E r m) pre_41

def famViewLt : PolicyFamilyView pre_45 where
  ref := 42
  member := mLt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 0 [], .const 0 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesLtBase : List FieldShape :=
  (fieldShapesFuel pre_45 96 42 0 0 2 0 (ctorDom mLtBase)).get (by decide)
def minorLtBase : Expr Nat :=
  (minorFromTelescope pre_45 96 0 (.bvar 0) (.const 43 []) shapesLtBase
    (lift 0 (1+0) (policyPi (ctorDom mLtBase)
      (foldApps (.const 42 []) (ctorIdx mLtBase))))).get (by decide)
theorem minorLtBase_isSome :
    (minorFromTelescope pre_45 96 0 (.bvar 0) (.const 43 []) shapesLtBase
      (lift 0 (1+0) (policyPi (ctorDom mLtBase)
        (foldApps (.const 42 []) (ctorIdx mLtBase))))).isSome = true := by decide

def shapesLtStep : List FieldShape :=
  (fieldShapesFuel pre_45 96 42 0 0 2 0 (ctorDom mLtStep)).get (by decide)
def minorLtStep : Expr Nat :=
  (minorFromTelescope pre_45 96 0 (.bvar 1) (.const 44 []) shapesLtStep
    (lift 0 (1+1) (policyPi (ctorDom mLtStep)
      (foldApps (.const 42 []) (ctorIdx mLtStep))))).get (by decide)
theorem minorLtStep_isSome :
    (minorFromTelescope pre_45 96 0 (.bvar 1) (.const 44 []) shapesLtStep
      (lift 0 (1+1) (policyPi (ctorDom mLtStep)
        (foldApps (.const 42 []) (ctorIdx mLtStep))))).isSome = true := by decide

def recLt : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewLt [minorLtBase, minorLtStep] .propOnly, none⟩

def pre_49 : ResolvedEnv :=
  [(45, recLt), (46, mBC), (47, mCatNil), (48, mCatCons)].foldl (fun E (r, m) => extendEnv E r m) pre_45

def famViewBC : PolicyFamilyView pre_49 where
  ref := 46
  member := mBC
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 4 [], .const 4 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨2, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+3, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesCatNil : List FieldShape :=
  (fieldShapesFuel pre_49 96 46 0 0 3 0 (ctorDom mCatNil)).get (by decide)
def minorCatNil : Expr Nat :=
  (minorFromTelescope pre_49 96 0 (.bvar 0) (.const 47 []) shapesCatNil
    (lift 0 (1+0) (policyPi (ctorDom mCatNil)
      (foldApps (.const 46 []) (ctorIdx mCatNil))))).get (by decide)
theorem minorCatNil_isSome :
    (minorFromTelescope pre_49 96 0 (.bvar 0) (.const 47 []) shapesCatNil
      (lift 0 (1+0) (policyPi (ctorDom mCatNil)
        (foldApps (.const 46 []) (ctorIdx mCatNil))))).isSome = true := by decide

def shapesCatCons : List FieldShape :=
  (fieldShapesFuel pre_49 96 46 0 0 3 0 (ctorDom mCatCons)).get (by decide)
def minorCatCons : Expr Nat :=
  (minorFromTelescope pre_49 96 0 (.bvar 1) (.const 48 []) shapesCatCons
    (lift 0 (1+1) (policyPi (ctorDom mCatCons)
      (foldApps (.const 46 []) (ctorIdx mCatCons))))).get (by decide)
theorem minorCatCons_isSome :
    (minorFromTelescope pre_49 96 0 (.bvar 1) (.const 48 []) shapesCatCons
      (lift 0 (1+1) (policyPi (ctorDom mCatCons)
        (foldApps (.const 46 []) (ctorIdx mCatCons))))).isSome = true := by decide

def recBC : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewBC [minorCatNil, minorCatCons] .propOnly, none⟩

def pre_53 : ResolvedEnv :=
  [(49, recBC), (50, mDM10), (51, mDmBase), (52, mDmStep)].foldl (fun E (r, m) => extendEnv E r m) pre_49

def famViewDM10 : PolicyFamilyView pre_53 where
  ref := 50
  member := mDM10
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 0 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 0 [], .const 0 [], .const 0 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨2, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨k+3, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesDmBase : List FieldShape :=
  (fieldShapesFuel pre_53 96 50 0 0 3 0 (ctorDom mDmBase)).get (by decide)
def minorDmBase : Expr Nat :=
  (minorFromTelescope pre_53 96 0 (.bvar 0) (.const 51 []) shapesDmBase
    (lift 0 (1+0) (policyPi (ctorDom mDmBase)
      (foldApps (.const 50 []) (ctorIdx mDmBase))))).get (by decide)
theorem minorDmBase_isSome :
    (minorFromTelescope pre_53 96 0 (.bvar 0) (.const 51 []) shapesDmBase
      (lift 0 (1+0) (policyPi (ctorDom mDmBase)
        (foldApps (.const 50 []) (ctorIdx mDmBase))))).isSome = true := by decide

def shapesDmStep : List FieldShape :=
  (fieldShapesFuel pre_53 96 50 0 0 3 0 (ctorDom mDmStep)).get (by decide)
def minorDmStep : Expr Nat :=
  (minorFromTelescope pre_53 96 0 (.bvar 1) (.const 52 []) shapesDmStep
    (lift 0 (1+1) (policyPi (ctorDom mDmStep)
      (foldApps (.const 50 []) (ctorIdx mDmStep))))).get (by decide)
theorem minorDmStep_isSome :
    (minorFromTelescope pre_53 96 0 (.bvar 1) (.const 52 []) shapesDmStep
      (lift 0 (1+1) (policyPi (ctorDom mDmStep)
        (foldApps (.const 50 []) (ctorIdx mDmStep))))).isSome = true := by decide

def recDM10 : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewDM10 [minorDmBase, minorDmStep] .propOnly, none⟩

def pre_57 : ResolvedEnv :=
  [(53, recDM10), (54, mND), (55, mNdBase), (56, mNdStep)].foldl (fun E (r, m) => extendEnv E r m) pre_53

def famViewND : PolicyFamilyView pre_57 where
  ref := 54
  member := mND
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 0 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesNdBase : List FieldShape :=
  (fieldShapesFuel pre_57 96 54 0 0 2 0 (ctorDom mNdBase)).get (by decide)
def minorNdBase : Expr Nat :=
  (minorFromTelescope pre_57 96 0 (.bvar 0) (.const 55 []) shapesNdBase
    (lift 0 (1+0) (policyPi (ctorDom mNdBase)
      (foldApps (.const 54 []) (ctorIdx mNdBase))))).get (by decide)
theorem minorNdBase_isSome :
    (minorFromTelescope pre_57 96 0 (.bvar 0) (.const 55 []) shapesNdBase
      (lift 0 (1+0) (policyPi (ctorDom mNdBase)
        (foldApps (.const 54 []) (ctorIdx mNdBase))))).isSome = true := by decide

def shapesNdStep : List FieldShape :=
  (fieldShapesFuel pre_57 96 54 0 0 2 0 (ctorDom mNdStep)).get (by decide)
def minorNdStep : Expr Nat :=
  (minorFromTelescope pre_57 96 0 (.bvar 1) (.const 56 []) shapesNdStep
    (lift 0 (1+1) (policyPi (ctorDom mNdStep)
      (foldApps (.const 54 []) (ctorIdx mNdStep))))).get (by decide)
theorem minorNdStep_isSome :
    (minorFromTelescope pre_57 96 0 (.bvar 1) (.const 56 []) shapesNdStep
      (lift 0 (1+1) (policyPi (ctorDom mNdStep)
        (foldApps (.const 54 []) (ctorIdx mNdStep))))).isSome = true := by decide

def recND : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewND [minorNdBase, minorNdStep] .propOnly, none⟩

def pre_60 : ResolvedEnv :=
  [(57, recND), (58, mNEA), (59, mNeIntro)].foldl (fun E (r, m) => extendEnv E r m) pre_57

def famViewNEA : PolicyFamilyView pre_60 where
  ref := 58
  member := mNEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 0 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesNeIntro : List FieldShape :=
  (fieldShapesFuel pre_60 96 58 0 0 2 0 (ctorDom mNeIntro)).get (by decide)
def minorNeIntro : Expr Nat :=
  (minorFromTelescope pre_60 96 0 (.bvar 0) (.const 59 []) shapesNeIntro
    (lift 0 (1+0) (policyPi (ctorDom mNeIntro)
      (foldApps (.const 58 []) (ctorIdx mNeIntro))))).get (by decide)
theorem minorNeIntro_isSome :
    (minorFromTelescope pre_60 96 0 (.bvar 0) (.const 59 []) shapesNeIntro
      (lift 0 (1+0) (policyPi (ctorDom mNeIntro)
        (foldApps (.const 58 []) (ctorIdx mNeIntro))))).isSome = true := by decide

def recNEA : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewNEA [minorNeIntro] .propOnly, none⟩

def pre_64 : ResolvedEnv :=
  [(60, recNEA), (61, mIEA), (62, mIePos), (63, mIeNeg)].foldl (fun E (r, m) => extendEnv E r m) pre_60

def famViewIEA : PolicyFamilyView pre_64 where
  ref := 61
  member := mIEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 30 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 30 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 30 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesIePos : List FieldShape :=
  (fieldShapesFuel pre_64 96 61 0 0 2 0 (ctorDom mIePos)).get (by decide)
def minorIePos : Expr Nat :=
  (minorFromTelescope pre_64 96 0 (.bvar 0) (.const 62 []) shapesIePos
    (lift 0 (1+0) (policyPi (ctorDom mIePos)
      (foldApps (.const 61 []) (ctorIdx mIePos))))).get (by decide)
theorem minorIePos_isSome :
    (minorFromTelescope pre_64 96 0 (.bvar 0) (.const 62 []) shapesIePos
      (lift 0 (1+0) (policyPi (ctorDom mIePos)
        (foldApps (.const 61 []) (ctorIdx mIePos))))).isSome = true := by decide

def shapesIeNeg : List FieldShape :=
  (fieldShapesFuel pre_64 96 61 0 0 2 0 (ctorDom mIeNeg)).get (by decide)
def minorIeNeg : Expr Nat :=
  (minorFromTelescope pre_64 96 0 (.bvar 1) (.const 63 []) shapesIeNeg
    (lift 0 (1+1) (policyPi (ctorDom mIeNeg)
      (foldApps (.const 61 []) (ctorIdx mIeNeg))))).get (by decide)
theorem minorIeNeg_isSome :
    (minorFromTelescope pre_64 96 0 (.bvar 1) (.const 63 []) shapesIeNeg
      (lift 0 (1+1) (policyPi (ctorDom mIeNeg)
        (foldApps (.const 61 []) (ctorIdx mIeNeg))))).isSome = true := by decide

def recIEA : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewIEA [minorIePos, minorIeNeg] .propOnly, none⟩

def pre_68 : ResolvedEnv :=
  [(64, recIEA), (65, mSL), (66, mSlNil), (67, mSlCons)].foldl (fun E (r, m) => extendEnv E r m) pre_64

def famViewSL : PolicyFamilyView pre_68 where
  ref := 65
  member := mSL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 4 [], .const 0 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesSlNil : List FieldShape :=
  (fieldShapesFuel pre_68 96 65 0 0 2 0 (ctorDom mSlNil)).get (by decide)
def minorSlNil : Expr Nat :=
  (minorFromTelescope pre_68 96 0 (.bvar 0) (.const 66 []) shapesSlNil
    (lift 0 (1+0) (policyPi (ctorDom mSlNil)
      (foldApps (.const 65 []) (ctorIdx mSlNil))))).get (by decide)
theorem minorSlNil_isSome :
    (minorFromTelescope pre_68 96 0 (.bvar 0) (.const 66 []) shapesSlNil
      (lift 0 (1+0) (policyPi (ctorDom mSlNil)
        (foldApps (.const 65 []) (ctorIdx mSlNil))))).isSome = true := by decide

def shapesSlCons : List FieldShape :=
  (fieldShapesFuel pre_68 96 65 0 0 2 0 (ctorDom mSlCons)).get (by decide)
def minorSlCons : Expr Nat :=
  (minorFromTelescope pre_68 96 0 (.bvar 1) (.const 67 []) shapesSlCons
    (lift 0 (1+1) (policyPi (ctorDom mSlCons)
      (foldApps (.const 65 []) (ctorIdx mSlCons))))).get (by decide)
theorem minorSlCons_isSome :
    (minorFromTelescope pre_68 96 0 (.bvar 1) (.const 67 []) shapesSlCons
      (lift 0 (1+1) (policyPi (ctorDom mSlCons)
        (foldApps (.const 65 []) (ctorIdx mSlCons))))).isSome = true := by decide

def recSL : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewSL [minorSlNil, minorSlCons] .propOnly, none⟩

def pre_72 : ResolvedEnv :=
  [(68, recSL), (69, mBLL), (70, mBllNil), (71, mBllCons)].foldl (fun E (r, m) => extendEnv E r m) pre_68

def famViewBLL : PolicyFamilyView pre_72 where
  ref := 69
  member := mBLL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 34 [], .const 0 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 34 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesBllNil : List FieldShape :=
  (fieldShapesFuel pre_72 96 69 0 0 2 0 (ctorDom mBllNil)).get (by decide)
def minorBllNil : Expr Nat :=
  (minorFromTelescope pre_72 96 0 (.bvar 0) (.const 70 []) shapesBllNil
    (lift 0 (1+0) (policyPi (ctorDom mBllNil)
      (foldApps (.const 69 []) (ctorIdx mBllNil))))).get (by decide)
theorem minorBllNil_isSome :
    (minorFromTelescope pre_72 96 0 (.bvar 0) (.const 70 []) shapesBllNil
      (lift 0 (1+0) (policyPi (ctorDom mBllNil)
        (foldApps (.const 69 []) (ctorIdx mBllNil))))).isSome = true := by decide

def shapesBllCons : List FieldShape :=
  (fieldShapesFuel pre_72 96 69 0 0 2 0 (ctorDom mBllCons)).get (by decide)
def minorBllCons : Expr Nat :=
  (minorFromTelescope pre_72 96 0 (.bvar 1) (.const 71 []) shapesBllCons
    (lift 0 (1+1) (policyPi (ctorDom mBllCons)
      (foldApps (.const 69 []) (ctorIdx mBllCons))))).get (by decide)
theorem minorBllCons_isSome :
    (minorFromTelescope pre_72 96 0 (.bvar 1) (.const 71 []) shapesBllCons
      (lift 0 (1+1) (policyPi (ctorDom mBllCons)
        (foldApps (.const 69 []) (ctorIdx mBllCons))))).isSome = true := by decide

def recBLL : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewBLL [minorBllNil, minorBllCons] .propOnly, none⟩

def pre_76 : ResolvedEnv :=
  [(72, recBLL), (73, mFTL), (74, mFtlNil), (75, mFtlCons)].foldl (fun E (r, m) => extendEnv E r m) pre_72

def famViewFTL : PolicyFamilyView pre_76 where
  ref := 73
  member := mFTL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 0 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 38 [], .const 0 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 38 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesFtlNil : List FieldShape :=
  (fieldShapesFuel pre_76 96 73 0 0 2 0 (ctorDom mFtlNil)).get (by decide)
def minorFtlNil : Expr Nat :=
  (minorFromTelescope pre_76 96 0 (.bvar 0) (.const 74 []) shapesFtlNil
    (lift 0 (1+0) (policyPi (ctorDom mFtlNil)
      (foldApps (.const 73 []) (ctorIdx mFtlNil))))).get (by decide)
theorem minorFtlNil_isSome :
    (minorFromTelescope pre_76 96 0 (.bvar 0) (.const 74 []) shapesFtlNil
      (lift 0 (1+0) (policyPi (ctorDom mFtlNil)
        (foldApps (.const 73 []) (ctorIdx mFtlNil))))).isSome = true := by decide

def shapesFtlCons : List FieldShape :=
  (fieldShapesFuel pre_76 96 73 0 0 2 0 (ctorDom mFtlCons)).get (by decide)
def minorFtlCons : Expr Nat :=
  (minorFromTelescope pre_76 96 0 (.bvar 1) (.const 75 []) shapesFtlCons
    (lift 0 (1+1) (policyPi (ctorDom mFtlCons)
      (foldApps (.const 73 []) (ctorIdx mFtlCons))))).get (by decide)
theorem minorFtlCons_isSome :
    (minorFromTelescope pre_76 96 0 (.bvar 1) (.const 75 []) shapesFtlCons
      (lift 0 (1+1) (policyPi (ctorDom mFtlCons)
        (foldApps (.const 73 []) (ctorIdx mFtlCons))))).isSome = true := by decide

def recFTL : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewFTL [minorFtlNil, minorFtlCons] .propOnly, none⟩

def pre_80 : ResolvedEnv :=
  [(76, recFTL), (77, mBLC), (78, mBlcNil), (79, mBlcCons)].foldl (fun E (r, m) => extendEnv E r m) pre_76

def famViewBLC : PolicyFamilyView pre_80 where
  ref := 77
  member := mBLC
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 34 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 34 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesBlcNil : List FieldShape :=
  (fieldShapesFuel pre_80 96 77 0 0 2 0 (ctorDom mBlcNil)).get (by decide)
def minorBlcNil : Expr Nat :=
  (minorFromTelescope pre_80 96 0 (.bvar 0) (.const 78 []) shapesBlcNil
    (lift 0 (1+0) (policyPi (ctorDom mBlcNil)
      (foldApps (.const 77 []) (ctorIdx mBlcNil))))).get (by decide)
theorem minorBlcNil_isSome :
    (minorFromTelescope pre_80 96 0 (.bvar 0) (.const 78 []) shapesBlcNil
      (lift 0 (1+0) (policyPi (ctorDom mBlcNil)
        (foldApps (.const 77 []) (ctorIdx mBlcNil))))).isSome = true := by decide

def shapesBlcCons : List FieldShape :=
  (fieldShapesFuel pre_80 96 77 0 0 2 0 (ctorDom mBlcCons)).get (by decide)
def minorBlcCons : Expr Nat :=
  (minorFromTelescope pre_80 96 0 (.bvar 1) (.const 79 []) shapesBlcCons
    (lift 0 (1+1) (policyPi (ctorDom mBlcCons)
      (foldApps (.const 77 []) (ctorIdx mBlcCons))))).get (by decide)
theorem minorBlcCons_isSome :
    (minorFromTelescope pre_80 96 0 (.bvar 1) (.const 79 []) shapesBlcCons
      (lift 0 (1+1) (policyPi (ctorDom mBlcCons)
        (foldApps (.const 77 []) (ctorIdx mBlcCons))))).isSome = true := by decide

def recBLC : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewBLC [minorBlcNil, minorBlcCons] .propOnly, none⟩

def pre_83 : ResolvedEnv :=
  [(80, recBLC), (81, mSEA), (82, mSeIntro)].foldl (fun E (r, m) => extendEnv E r m) pre_80

def famViewSEA : PolicyFamilyView pre_83 where
  ref := 81
  member := mSEA
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 4 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesSeIntro : List FieldShape :=
  (fieldShapesFuel pre_83 96 81 0 0 2 0 (ctorDom mSeIntro)).get (by decide)
def minorSeIntro : Expr Nat :=
  (minorFromTelescope pre_83 96 0 (.bvar 0) (.const 82 []) shapesSeIntro
    (lift 0 (1+0) (policyPi (ctorDom mSeIntro)
      (foldApps (.const 81 []) (ctorIdx mSeIntro))))).get (by decide)
theorem minorSeIntro_isSome :
    (minorFromTelescope pre_83 96 0 (.bvar 0) (.const 82 []) shapesSeIntro
      (lift 0 (1+0) (policyPi (ctorDom mSeIntro)
        (foldApps (.const 81 []) (ctorIdx mSeIntro))))).isSome = true := by decide

def recSEA : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewSEA [minorSeIntro] .propOnly, none⟩

def pre_87 : ResolvedEnv :=
  [(83, recSEA), (84, mFTE), (85, mFteNil), (86, mFteCons)].foldl (fun E (r, m) => extendEnv E r m) pre_83

def famViewFTE : PolicyFamilyView pre_87 where
  ref := 84
  member := mFTE
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 38 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 38 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesFteNil : List FieldShape :=
  (fieldShapesFuel pre_87 96 84 0 0 2 0 (ctorDom mFteNil)).get (by decide)
def minorFteNil : Expr Nat :=
  (minorFromTelescope pre_87 96 0 (.bvar 0) (.const 85 []) shapesFteNil
    (lift 0 (1+0) (policyPi (ctorDom mFteNil)
      (foldApps (.const 84 []) (ctorIdx mFteNil))))).get (by decide)
theorem minorFteNil_isSome :
    (minorFromTelescope pre_87 96 0 (.bvar 0) (.const 85 []) shapesFteNil
      (lift 0 (1+0) (policyPi (ctorDom mFteNil)
        (foldApps (.const 84 []) (ctorIdx mFteNil))))).isSome = true := by decide

def shapesFteCons : List FieldShape :=
  (fieldShapesFuel pre_87 96 84 0 0 2 0 (ctorDom mFteCons)).get (by decide)
def minorFteCons : Expr Nat :=
  (minorFromTelescope pre_87 96 0 (.bvar 1) (.const 86 []) shapesFteCons
    (lift 0 (1+1) (policyPi (ctorDom mFteCons)
      (foldApps (.const 84 []) (ctorIdx mFteCons))))).get (by decide)
theorem minorFteCons_isSome :
    (minorFromTelescope pre_87 96 0 (.bvar 1) (.const 86 []) shapesFteCons
      (lift 0 (1+1) (policyPi (ctorDom mFteCons)
        (foldApps (.const 84 []) (ctorIdx mFteCons))))).isSome = true := by decide

def recFTE : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewFTE [minorFteNil, minorFteCons] .propOnly, none⟩

def pre_91 : ResolvedEnv :=
  [(87, recFTE), (88, mNthB), (89, mNthBHere), (90, mNthBNext)].foldl (fun E (r, m) => extendEnv E r m) pre_87

def famViewNthB : PolicyFamilyView pre_91 where
  ref := 88
  member := mNthB
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 34 [], .const 0 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 34 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨2, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+3, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesNthBHere : List FieldShape :=
  (fieldShapesFuel pre_91 96 88 0 0 3 0 (ctorDom mNthBHere)).get (by decide)
def minorNthBHere : Expr Nat :=
  (minorFromTelescope pre_91 96 0 (.bvar 0) (.const 89 []) shapesNthBHere
    (lift 0 (1+0) (policyPi (ctorDom mNthBHere)
      (foldApps (.const 88 []) (ctorIdx mNthBHere))))).get (by decide)
theorem minorNthBHere_isSome :
    (minorFromTelescope pre_91 96 0 (.bvar 0) (.const 89 []) shapesNthBHere
      (lift 0 (1+0) (policyPi (ctorDom mNthBHere)
        (foldApps (.const 88 []) (ctorIdx mNthBHere))))).isSome = true := by decide

def shapesNthBNext : List FieldShape :=
  (fieldShapesFuel pre_91 96 88 0 0 3 0 (ctorDom mNthBNext)).get (by decide)
def minorNthBNext : Expr Nat :=
  (minorFromTelescope pre_91 96 0 (.bvar 1) (.const 90 []) shapesNthBNext
    (lift 0 (1+1) (policyPi (ctorDom mNthBNext)
      (foldApps (.const 88 []) (ctorIdx mNthBNext))))).get (by decide)
theorem minorNthBNext_isSome :
    (minorFromTelescope pre_91 96 0 (.bvar 1) (.const 90 []) shapesNthBNext
      (lift 0 (1+1) (policyPi (ctorDom mNthBNext)
        (foldApps (.const 88 []) (ctorIdx mNthBNext))))).isSome = true := by decide

def recNthB : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewNthB [minorNthBHere, minorNthBNext] .propOnly, none⟩

def pre_95 : ResolvedEnv :=
  [(91, recNthB), (92, mNthF), (93, mNthFHere), (94, mNthFNext)].foldl (fun E (r, m) => extendEnv E r m) pre_91

def famViewNthF : PolicyFamilyView pre_95 where
  ref := 92
  member := mNthF
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 38 [], .const 0 [], .const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 38 [], .const 0 [], .const 4 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 38 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨2, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨3, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+4, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesNthFHere : List FieldShape :=
  (fieldShapesFuel pre_95 96 92 0 0 4 0 (ctorDom mNthFHere)).get (by decide)
def minorNthFHere : Expr Nat :=
  (minorFromTelescope pre_95 96 0 (.bvar 0) (.const 93 []) shapesNthFHere
    (lift 0 (1+0) (policyPi (ctorDom mNthFHere)
      (foldApps (.const 92 []) (ctorIdx mNthFHere))))).get (by decide)
theorem minorNthFHere_isSome :
    (minorFromTelescope pre_95 96 0 (.bvar 0) (.const 93 []) shapesNthFHere
      (lift 0 (1+0) (policyPi (ctorDom mNthFHere)
        (foldApps (.const 92 []) (ctorIdx mNthFHere))))).isSome = true := by decide

def shapesNthFNext : List FieldShape :=
  (fieldShapesFuel pre_95 96 92 0 0 4 0 (ctorDom mNthFNext)).get (by decide)
def minorNthFNext : Expr Nat :=
  (minorFromTelescope pre_95 96 0 (.bvar 1) (.const 94 []) shapesNthFNext
    (lift 0 (1+1) (policyPi (ctorDom mNthFNext)
      (foldApps (.const 92 []) (ctorIdx mNthFNext))))).get (by decide)
theorem minorNthFNext_isSome :
    (minorFromTelescope pre_95 96 0 (.bvar 1) (.const 94 []) shapesNthFNext
      (lift 0 (1+1) (policyPi (ctorDom mNthFNext)
        (foldApps (.const 92 []) (ctorIdx mNthFNext))))).isSome = true := by decide

def recNthF : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewNthF [minorNthFHere, minorNthFNext] .propOnly, none⟩

def pre_105 : ResolvedEnv :=
  [(95, recNthF), (96, mCCT), (97, mCctI), (98, mCctB), (99, mCctStr), (100, mCctY), (101, mCctL), (102, mCctP), (103, mCctSum), (104, mCctRec)].foldl (fun E (r, m) => extendEnv E r m) pre_95

def famViewCCT : PolicyFamilyView pre_105 where
  ref := 96
  member := mCCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 8 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 8 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 8 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesCctI : List FieldShape :=
  (fieldShapesFuel pre_105 96 96 0 0 2 0 (ctorDom mCctI)).get (by decide)
def minorCctI : Expr Nat :=
  (minorFromTelescope pre_105 96 0 (.bvar 0) (.const 97 []) shapesCctI
    (lift 0 (1+0) (policyPi (ctorDom mCctI)
      (foldApps (.const 96 []) (ctorIdx mCctI))))).get (by decide)
theorem minorCctI_isSome :
    (minorFromTelescope pre_105 96 0 (.bvar 0) (.const 97 []) shapesCctI
      (lift 0 (1+0) (policyPi (ctorDom mCctI)
        (foldApps (.const 96 []) (ctorIdx mCctI))))).isSome = true := by decide

def shapesCctB : List FieldShape :=
  (fieldShapesFuel pre_105 96 96 0 0 2 0 (ctorDom mCctB)).get (by decide)
def minorCctB : Expr Nat :=
  (minorFromTelescope pre_105 96 0 (.bvar 1) (.const 98 []) shapesCctB
    (lift 0 (1+1) (policyPi (ctorDom mCctB)
      (foldApps (.const 96 []) (ctorIdx mCctB))))).get (by decide)
theorem minorCctB_isSome :
    (minorFromTelescope pre_105 96 0 (.bvar 1) (.const 98 []) shapesCctB
      (lift 0 (1+1) (policyPi (ctorDom mCctB)
        (foldApps (.const 96 []) (ctorIdx mCctB))))).isSome = true := by decide

def shapesCctStr : List FieldShape :=
  (fieldShapesFuel pre_105 96 96 0 0 2 0 (ctorDom mCctStr)).get (by decide)
def minorCctStr : Expr Nat :=
  (minorFromTelescope pre_105 96 0 (.bvar 2) (.const 99 []) shapesCctStr
    (lift 0 (1+2) (policyPi (ctorDom mCctStr)
      (foldApps (.const 96 []) (ctorIdx mCctStr))))).get (by decide)
theorem minorCctStr_isSome :
    (minorFromTelescope pre_105 96 0 (.bvar 2) (.const 99 []) shapesCctStr
      (lift 0 (1+2) (policyPi (ctorDom mCctStr)
        (foldApps (.const 96 []) (ctorIdx mCctStr))))).isSome = true := by decide

def shapesCctY : List FieldShape :=
  (fieldShapesFuel pre_105 96 96 0 0 2 0 (ctorDom mCctY)).get (by decide)
def minorCctY : Expr Nat :=
  (minorFromTelescope pre_105 96 0 (.bvar 3) (.const 100 []) shapesCctY
    (lift 0 (1+3) (policyPi (ctorDom mCctY)
      (foldApps (.const 96 []) (ctorIdx mCctY))))).get (by decide)
theorem minorCctY_isSome :
    (minorFromTelescope pre_105 96 0 (.bvar 3) (.const 100 []) shapesCctY
      (lift 0 (1+3) (policyPi (ctorDom mCctY)
        (foldApps (.const 96 []) (ctorIdx mCctY))))).isSome = true := by decide

def shapesCctL : List FieldShape :=
  (fieldShapesFuel pre_105 96 96 0 0 2 0 (ctorDom mCctL)).get (by decide)
def minorCctL : Expr Nat :=
  (minorFromTelescope pre_105 96 0 (.bvar 4) (.const 101 []) shapesCctL
    (lift 0 (1+4) (policyPi (ctorDom mCctL)
      (foldApps (.const 96 []) (ctorIdx mCctL))))).get (by decide)
theorem minorCctL_isSome :
    (minorFromTelescope pre_105 96 0 (.bvar 4) (.const 101 []) shapesCctL
      (lift 0 (1+4) (policyPi (ctorDom mCctL)
        (foldApps (.const 96 []) (ctorIdx mCctL))))).isSome = true := by decide

def shapesCctP : List FieldShape :=
  (fieldShapesFuel pre_105 96 96 0 0 2 0 (ctorDom mCctP)).get (by decide)
def minorCctP : Expr Nat :=
  (minorFromTelescope pre_105 96 0 (.bvar 5) (.const 102 []) shapesCctP
    (lift 0 (1+5) (policyPi (ctorDom mCctP)
      (foldApps (.const 96 []) (ctorIdx mCctP))))).get (by decide)
theorem minorCctP_isSome :
    (minorFromTelescope pre_105 96 0 (.bvar 5) (.const 102 []) shapesCctP
      (lift 0 (1+5) (policyPi (ctorDom mCctP)
        (foldApps (.const 96 []) (ctorIdx mCctP))))).isSome = true := by decide

def shapesCctSum : List FieldShape :=
  (fieldShapesFuel pre_105 96 96 0 0 2 0 (ctorDom mCctSum)).get (by decide)
def minorCctSum : Expr Nat :=
  (minorFromTelescope pre_105 96 0 (.bvar 6) (.const 103 []) shapesCctSum
    (lift 0 (1+6) (policyPi (ctorDom mCctSum)
      (foldApps (.const 96 []) (ctorIdx mCctSum))))).get (by decide)
theorem minorCctSum_isSome :
    (minorFromTelescope pre_105 96 0 (.bvar 6) (.const 103 []) shapesCctSum
      (lift 0 (1+6) (policyPi (ctorDom mCctSum)
        (foldApps (.const 96 []) (ctorIdx mCctSum))))).isSome = true := by decide

def shapesCctRec : List FieldShape :=
  (fieldShapesFuel pre_105 96 96 0 0 2 0 (ctorDom mCctRec)).get (by decide)
def minorCctRec : Expr Nat :=
  (minorFromTelescope pre_105 96 0 (.bvar 7) (.const 104 []) shapesCctRec
    (lift 0 (1+7) (policyPi (ctorDom mCctRec)
      (foldApps (.const 96 []) (ctorIdx mCctRec))))).get (by decide)
theorem minorCctRec_isSome :
    (minorFromTelescope pre_105 96 0 (.bvar 7) (.const 104 []) shapesCctRec
      (lift 0 (1+7) (policyPi (ctorDom mCctRec)
        (foldApps (.const 96 []) (ctorIdx mCctRec))))).isSome = true := by decide

def recCCT : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewCCT [minorCctI, minorCctB, minorCctStr, minorCctY, minorCctL, minorCctP, minorCctSum, minorCctRec] .propOnly, none⟩

def pre_108 : ResolvedEnv :=
  [(105, recCCT), (106, mBCT), (107, mMkBound)].foldl (fun E (r, m) => extendEnv E r m) pre_105

def famViewBCT : PolicyFamilyView pre_108 where
  ref := 106
  member := mBCT
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := PolicyTelescopeTyping.empty _ _

def shapesMkBound : List FieldShape :=
  (fieldShapesFuel pre_108 96 106 0 0 0 0 (ctorDom mMkBound)).get (by decide)
def minorMkBound : Expr Nat :=
  (minorFromTelescope pre_108 96 0 (.bvar 0) (.const 107 []) shapesMkBound
    (lift 0 (1+0) (policyPi (ctorDom mMkBound)
      (foldApps (.const 106 []) (ctorIdx mMkBound))))).get (by decide)
theorem minorMkBound_isSome :
    (minorFromTelescope pre_108 96 0 (.bvar 0) (.const 107 []) shapesMkBound
      (lift 0 (1+0) (policyPi (ctorDom mMkBound)
        (foldApps (.const 106 []) (ctorIdx mMkBound))))).isSome = true := by decide

def recBCT : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .anySort,
    policyRecursorType famViewBCT [minorMkBound] .anySort, none⟩

def pre_128 : ResolvedEnv :=
  [(108, recBCT), (109, mI64Ref), (110, mBoolRef), (111, mStrRef), (112, mBytesRef), (113, mCctI64Pf), (114, mCctBoolPf), (115, mCctStrPf), (116, mCctBytesPf), (117, mBoundI64), (118, mBoundBool), (119, mBoundStr), (120, mBoundBytes), (121, mBcLB), (122, mLbRef), (123, mCctLbPf), (124, mBoundListBool), (125, mNEL), (126, mNelNil), (127, mNelCons)].foldl (fun E (r, m) => extendEnv E r m) pre_108

def famViewNEL : PolicyFamilyView pre_128 where
  ref := 125
  member := mNEL
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 4 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 4 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesNelNil : List FieldShape :=
  (fieldShapesFuel pre_128 96 125 0 0 2 0 (ctorDom mNelNil)).get (by decide)
def minorNelNil : Expr Nat :=
  (minorFromTelescope pre_128 96 0 (.bvar 0) (.const 126 []) shapesNelNil
    (lift 0 (1+0) (policyPi (ctorDom mNelNil)
      (foldApps (.const 125 []) (ctorIdx mNelNil))))).get (by decide)
theorem minorNelNil_isSome :
    (minorFromTelescope pre_128 96 0 (.bvar 0) (.const 126 []) shapesNelNil
      (lift 0 (1+0) (policyPi (ctorDom mNelNil)
        (foldApps (.const 125 []) (ctorIdx mNelNil))))).isSome = true := by decide

def shapesNelCons : List FieldShape :=
  (fieldShapesFuel pre_128 96 125 0 0 2 0 (ctorDom mNelCons)).get (by decide)
def minorNelCons : Expr Nat :=
  (minorFromTelescope pre_128 96 0 (.bvar 1) (.const 127 []) shapesNelCons
    (lift 0 (1+1) (policyPi (ctorDom mNelCons)
      (foldApps (.const 125 []) (ctorIdx mNelCons))))).get (by decide)
theorem minorNelCons_isSome :
    (minorFromTelescope pre_128 96 0 (.bvar 1) (.const 127 []) shapesNelCons
      (lift 0 (1+1) (policyPi (ctorDom mNelCons)
        (foldApps (.const 125 []) (ctorIdx mNelCons))))).isSome = true := by decide

def recNEL : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewNEL [minorNelNil, minorNelCons] .propOnly, none⟩

def pre_132 : ResolvedEnv :=
  [(128, recNEL), (129, mNTB), (130, mNtbHere), (131, mNtbNext)].foldl (fun E (r, m) => extendEnv E r m) pre_128

def famViewNTB : PolicyFamilyView pre_132 where
  ref := 129
  member := mNTB
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 34 [], .const 0 [], .const 106 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 34 [], .const 0 [], .const 106 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 34 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 0 rfl rfl rfl
      | ⟨2, _⟩ => domTy _ 106 rfl rfl rfl
      | ⟨k+3, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesNtbHere : List FieldShape :=
  (fieldShapesFuel pre_132 96 129 0 0 3 0 (ctorDom mNtbHere)).get (by decide)
def minorNtbHere : Expr Nat :=
  (minorFromTelescope pre_132 96 0 (.bvar 0) (.const 130 []) shapesNtbHere
    (lift 0 (1+0) (policyPi (ctorDom mNtbHere)
      (foldApps (.const 129 []) (ctorIdx mNtbHere))))).get (by decide)
theorem minorNtbHere_isSome :
    (minorFromTelescope pre_132 96 0 (.bvar 0) (.const 130 []) shapesNtbHere
      (lift 0 (1+0) (policyPi (ctorDom mNtbHere)
        (foldApps (.const 129 []) (ctorIdx mNtbHere))))).isSome = true := by decide

def shapesNtbNext : List FieldShape :=
  (fieldShapesFuel pre_132 96 129 0 0 3 0 (ctorDom mNtbNext)).get (by decide)
def minorNtbNext : Expr Nat :=
  (minorFromTelescope pre_132 96 0 (.bvar 1) (.const 131 []) shapesNtbNext
    (lift 0 (1+1) (policyPi (ctorDom mNtbNext)
      (foldApps (.const 129 []) (ctorIdx mNtbNext))))).get (by decide)
theorem minorNtbNext_isSome :
    (minorFromTelescope pre_132 96 0 (.bvar 1) (.const 131 []) shapesNtbNext
      (lift 0 (1+1) (policyPi (ctorDom mNtbNext)
        (foldApps (.const 129 []) (ctorIdx mNtbNext))))).isSome = true := by decide

def recNTB : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewNTB [minorNtbHere, minorNtbNext] .propOnly, none⟩

def pre_143 : ResolvedEnv :=
  [(132, recNTB), (133, mValueAt), (134, mVaB0), (135, mVaB1), (136, mVaI64), (137, mVaStr), (138, mVaY), (139, mVaList), (140, mVaPair), (141, mVaJ), (142, mVaR)].foldl (fun E (r, m) => extendEnv E r m) pre_132

def famViewValueAt : PolicyFamilyView pre_143 where
  ref := 133
  member := mValueAt
  present := rfl
  hasClass := rfl
  parameters := []
  indices := [.const 106 [], .const 4 []]
  resultLevel := .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := domTel [.const 106 [], .const 4 []] (fun j => match j with
      | ⟨0, _⟩ => domTy _ 106 rfl rfl rfl
      | ⟨1, _⟩ => domTy _ 4 rfl rfl rfl
      | ⟨k+2, h⟩ => absurd h (by simp only [List.length]; omega))

def shapesVaB0 : List FieldShape :=
  (fieldShapesFuel pre_143 96 133 0 0 2 0 (ctorDom mVaB0)).get (by decide)
def minorVaB0 : Expr Nat :=
  (minorFromTelescope pre_143 96 0 (.bvar 0) (.const 134 []) shapesVaB0
    (lift 0 (1+0) (policyPi (ctorDom mVaB0)
      (foldApps (.const 133 []) (ctorIdx mVaB0))))).get (by decide)
theorem minorVaB0_isSome :
    (minorFromTelescope pre_143 96 0 (.bvar 0) (.const 134 []) shapesVaB0
      (lift 0 (1+0) (policyPi (ctorDom mVaB0)
        (foldApps (.const 133 []) (ctorIdx mVaB0))))).isSome = true := by decide

def shapesVaB1 : List FieldShape :=
  (fieldShapesFuel pre_143 96 133 0 0 2 0 (ctorDom mVaB1)).get (by decide)
def minorVaB1 : Expr Nat :=
  (minorFromTelescope pre_143 96 0 (.bvar 1) (.const 135 []) shapesVaB1
    (lift 0 (1+1) (policyPi (ctorDom mVaB1)
      (foldApps (.const 133 []) (ctorIdx mVaB1))))).get (by decide)
theorem minorVaB1_isSome :
    (minorFromTelescope pre_143 96 0 (.bvar 1) (.const 135 []) shapesVaB1
      (lift 0 (1+1) (policyPi (ctorDom mVaB1)
        (foldApps (.const 133 []) (ctorIdx mVaB1))))).isSome = true := by decide

def shapesVaI64 : List FieldShape :=
  (fieldShapesFuel pre_143 96 133 0 0 2 0 (ctorDom mVaI64)).get (by decide)
def minorVaI64 : Expr Nat :=
  (minorFromTelescope pre_143 96 0 (.bvar 2) (.const 136 []) shapesVaI64
    (lift 0 (1+2) (policyPi (ctorDom mVaI64)
      (foldApps (.const 133 []) (ctorIdx mVaI64))))).get (by decide)
theorem minorVaI64_isSome :
    (minorFromTelescope pre_143 96 0 (.bvar 2) (.const 136 []) shapesVaI64
      (lift 0 (1+2) (policyPi (ctorDom mVaI64)
        (foldApps (.const 133 []) (ctorIdx mVaI64))))).isSome = true := by decide

def shapesVaStr : List FieldShape :=
  (fieldShapesFuel pre_143 96 133 0 0 2 0 (ctorDom mVaStr)).get (by decide)
def minorVaStr : Expr Nat :=
  (minorFromTelescope pre_143 96 0 (.bvar 3) (.const 137 []) shapesVaStr
    (lift 0 (1+3) (policyPi (ctorDom mVaStr)
      (foldApps (.const 133 []) (ctorIdx mVaStr))))).get (by decide)
theorem minorVaStr_isSome :
    (minorFromTelescope pre_143 96 0 (.bvar 3) (.const 137 []) shapesVaStr
      (lift 0 (1+3) (policyPi (ctorDom mVaStr)
        (foldApps (.const 133 []) (ctorIdx mVaStr))))).isSome = true := by decide

def shapesVaY : List FieldShape :=
  (fieldShapesFuel pre_143 96 133 0 0 2 0 (ctorDom mVaY)).get (by decide)
def minorVaY : Expr Nat :=
  (minorFromTelescope pre_143 96 0 (.bvar 4) (.const 138 []) shapesVaY
    (lift 0 (1+4) (policyPi (ctorDom mVaY)
      (foldApps (.const 133 []) (ctorIdx mVaY))))).get (by decide)
theorem minorVaY_isSome :
    (minorFromTelescope pre_143 96 0 (.bvar 4) (.const 138 []) shapesVaY
      (lift 0 (1+4) (policyPi (ctorDom mVaY)
        (foldApps (.const 133 []) (ctorIdx mVaY))))).isSome = true := by decide

def shapesVaList : List FieldShape :=
  (fieldShapesFuel pre_143 96 133 0 0 2 0 (ctorDom mVaList)).get (by decide)
def minorVaList : Expr Nat :=
  (minorFromTelescope pre_143 96 0 (.bvar 5) (.const 139 []) shapesVaList
    (lift 0 (1+5) (policyPi (ctorDom mVaList)
      (foldApps (.const 133 []) (ctorIdx mVaList))))).get (by decide)
theorem minorVaList_isSome :
    (minorFromTelescope pre_143 96 0 (.bvar 5) (.const 139 []) shapesVaList
      (lift 0 (1+5) (policyPi (ctorDom mVaList)
        (foldApps (.const 133 []) (ctorIdx mVaList))))).isSome = true := by decide

def shapesVaPair : List FieldShape :=
  (fieldShapesFuel pre_143 96 133 0 0 2 0 (ctorDom mVaPair)).get (by decide)
def minorVaPair : Expr Nat :=
  (minorFromTelescope pre_143 96 0 (.bvar 6) (.const 140 []) shapesVaPair
    (lift 0 (1+6) (policyPi (ctorDom mVaPair)
      (foldApps (.const 133 []) (ctorIdx mVaPair))))).get (by decide)
theorem minorVaPair_isSome :
    (minorFromTelescope pre_143 96 0 (.bvar 6) (.const 140 []) shapesVaPair
      (lift 0 (1+6) (policyPi (ctorDom mVaPair)
        (foldApps (.const 133 []) (ctorIdx mVaPair))))).isSome = true := by decide

def shapesVaJ : List FieldShape :=
  (fieldShapesFuel pre_143 96 133 0 0 2 0 (ctorDom mVaJ)).get (by decide)
def minorVaJ : Expr Nat :=
  (minorFromTelescope pre_143 96 0 (.bvar 7) (.const 141 []) shapesVaJ
    (lift 0 (1+7) (policyPi (ctorDom mVaJ)
      (foldApps (.const 133 []) (ctorIdx mVaJ))))).get (by decide)
theorem minorVaJ_isSome :
    (minorFromTelescope pre_143 96 0 (.bvar 7) (.const 141 []) shapesVaJ
      (lift 0 (1+7) (policyPi (ctorDom mVaJ)
        (foldApps (.const 133 []) (ctorIdx mVaJ))))).isSome = true := by decide

def shapesVaR : List FieldShape :=
  (fieldShapesFuel pre_143 96 133 0 0 2 0 (ctorDom mVaR)).get (by decide)
def minorVaR : Expr Nat :=
  (minorFromTelescope pre_143 96 0 (.bvar 8) (.const 142 []) shapesVaR
    (lift 0 (1+8) (policyPi (ctorDom mVaR)
      (foldApps (.const 133 []) (ctorIdx mVaR))))).get (by decide)
theorem minorVaR_isSome :
    (minorFromTelescope pre_143 96 0 (.bvar 8) (.const 142 []) shapesVaR
      (lift 0 (1+8) (policyPi (ctorDom mVaR)
        (foldApps (.const 133 []) (ctorIdx mVaR))))).isSome = true := by decide

def recValueAt : CheckedMember :=
  ⟨.recursorM, policyRecursorArity 0 .propOnly,
    policyRecursorType famViewValueAt [minorVaB0, minorVaB1, minorVaI64, minorVaStr, minorVaY, minorVaList, minorVaPair, minorVaJ, minorVaR] .propOnly, none⟩

def srcEnvG : ResolvedEnv :=
  [(143, recValueAt), (144, mVb0), (145, mVb1), (146, mBytesSemi), (147, mBytesD0), (148, mBytesNat0), (149, mBytesVLB0), (150, mBytesI5), (151, mBytesD5), (152, mBytesNat5), (153, mLt010), (154, mNd0), (155, mBc48S), (156, mNea0), (157, mBcLN0), (158, mBcL0Nil), (159, mNthBNilVa), (160, mVLBNil), (161, mLt510), (162, mNd5), (163, mBc53S), (164, mNea5), (165, mIeaP5), (166, mBcI5), (167, mVI5)].foldl (fun E (r, m) => extendEnv E r m) pre_143

/-! ## The 168-slot table and the prefix-chain lemma -/

def srcMembersG : List (Nat × CheckedMember) :=
  [(0, mN),
  (1, mZero),
  (2, mSucc),
  (3, recN),
  (4, mBytes),
  (5, mBnil),
  (6, mBcons),
  (7, recBytes),
  (8, mRefT),
  (9, mMkRef),
  (10, recRefT),
  (11, mBytesI),
  (12, mBytesB),
  (13, mBytesS),
  (14, mBytesY),
  (15, mBytesB0),
  (16, mBytesB1),
  (17, mDigestI),
  (18, mDigestB),
  (19, mDigestS),
  (20, mDigestY),
  (21, mBytesLB),
  (22, mDigestLB),
  (23, mDA),
  (24, mDaI),
  (25, mDaB),
  (26, mDaS),
  (27, mDaY),
  (28, mDaLB),
  (29, recDA),
  (30, mI),
  (31, mIPos),
  (32, mINegS),
  (33, recI),
  (34, mBL),
  (35, mBlNil),
  (36, mBlCons),
  (37, recBL),
  (38, mFT),
  (39, mFtNil),
  (40, mFtCons),
  (41, recFT),
  (42, mLt),
  (43, mLtBase),
  (44, mLtStep),
  (45, recLt),
  (46, mBC),
  (47, mCatNil),
  (48, mCatCons),
  (49, recBC),
  (50, mDM10),
  (51, mDmBase),
  (52, mDmStep),
  (53, recDM10),
  (54, mND),
  (55, mNdBase),
  (56, mNdStep),
  (57, recND),
  (58, mNEA),
  (59, mNeIntro),
  (60, recNEA),
  (61, mIEA),
  (62, mIePos),
  (63, mIeNeg),
  (64, recIEA),
  (65, mSL),
  (66, mSlNil),
  (67, mSlCons),
  (68, recSL),
  (69, mBLL),
  (70, mBllNil),
  (71, mBllCons),
  (72, recBLL),
  (73, mFTL),
  (74, mFtlNil),
  (75, mFtlCons),
  (76, recFTL),
  (77, mBLC),
  (78, mBlcNil),
  (79, mBlcCons),
  (80, recBLC),
  (81, mSEA),
  (82, mSeIntro),
  (83, recSEA),
  (84, mFTE),
  (85, mFteNil),
  (86, mFteCons),
  (87, recFTE),
  (88, mNthB),
  (89, mNthBHere),
  (90, mNthBNext),
  (91, recNthB),
  (92, mNthF),
  (93, mNthFHere),
  (94, mNthFNext),
  (95, recNthF),
  (96, mCCT),
  (97, mCctI),
  (98, mCctB),
  (99, mCctStr),
  (100, mCctY),
  (101, mCctL),
  (102, mCctP),
  (103, mCctSum),
  (104, mCctRec),
  (105, recCCT),
  (106, mBCT),
  (107, mMkBound),
  (108, recBCT),
  (109, mI64Ref),
  (110, mBoolRef),
  (111, mStrRef),
  (112, mBytesRef),
  (113, mCctI64Pf),
  (114, mCctBoolPf),
  (115, mCctStrPf),
  (116, mCctBytesPf),
  (117, mBoundI64),
  (118, mBoundBool),
  (119, mBoundStr),
  (120, mBoundBytes),
  (121, mBcLB),
  (122, mLbRef),
  (123, mCctLbPf),
  (124, mBoundListBool),
  (125, mNEL),
  (126, mNelNil),
  (127, mNelCons),
  (128, recNEL),
  (129, mNTB),
  (130, mNtbHere),
  (131, mNtbNext),
  (132, recNTB),
  (133, mValueAt),
  (134, mVaB0),
  (135, mVaB1),
  (136, mVaI64),
  (137, mVaStr),
  (138, mVaY),
  (139, mVaList),
  (140, mVaPair),
  (141, mVaJ),
  (142, mVaR),
  (143, recValueAt),
  (144, mVb0),
  (145, mVb1),
  (146, mBytesSemi),
  (147, mBytesD0),
  (148, mBytesNat0),
  (149, mBytesVLB0),
  (150, mBytesI5),
  (151, mBytesD5),
  (152, mBytesNat5),
  (153, mLt010),
  (154, mNd0),
  (155, mBc48S),
  (156, mNea0),
  (157, mBcLN0),
  (158, mBcL0Nil),
  (159, mNthBNilVa),
  (160, mVLBNil),
  (161, mLt510),
  (162, mNd5),
  (163, mBc53S),
  (164, mNea5),
  (165, mIeaP5),
  (166, mBcI5),
  (167, mVI5)]

theorem srcEnvG_eq : srcMembersG.foldl
    (fun E (r, m) => extendEnv E r m) emptyEnv = srcEnvG := rfl

/-! ## Checks -/

def layoutOK (tbl : List (Nat × CheckedMember)) : Bool :=
  (tbl.map (·.1) == List.range tbl.length) &&
  tbl.all (fun p => if decide (p.2.mclass = .constructorM) || decide (p.2.mclass = .recursorM) then
      match memberFamRef p.2 with
      | some f => (tbl.lookup f).any (fun m => decide (m.mclass = .inductiveM))
      | none => false
    else true) &&
  tbl.all (fun p => if decide (p.2.mclass = .inductiveM) then
      let f := p.1
      let cs := (tbl.filter (fun q => decide (q.2.mclass = .constructorM) && memberFamRef q.2 == some f)).map (·.1)
      let rs := (tbl.filter (fun q => decide (q.2.mclass = .recursorM) && memberFamRef q.2 == some f)).map (·.1)
      cs == (List.range cs.length).map (f + 1 + ·) && rs == [f + 1 + cs.length]
    else true)

theorem srcLayoutG : layoutOK srcMembersG = true := by decide

theorem srcCountsG :
    (srcMembersG.filter (fun p => decide (p.2.mclass = .inductiveM))).length = 26 ∧
    (srcMembersG.filter (fun p => decide (p.2.mclass = .constructorM))).length = 64 ∧
    (srcMembersG.filter (fun p => decide (p.2.mclass = .definitionM))).length = 29 ∧
    (srcMembersG.filter (fun p => decide (p.2.mclass = .theoremM))).length = 23 ∧
    (srcMembersG.filter (fun p => decide (p.2.mclass = .recursorM))).length = 26 ∧
    (srcMembersG.filter (fun p => decide (p.2.mclass = .constructorM) &&
      memberFamRef p.2 == some 23)).length = 5 := by decide

private def memberEq (a b : CheckedMember) : Bool :=
  decide (a.mclass = b.mclass) && decide (a.arity = b.arity) &&
    decide (a.mtype = b.mtype) && decide (a.body = b.body)

theorem srcV1CorrG :
    srcMembersV1.all (fun (r, m) =>
      ((srcMembersG.lookup (πmap r)).map
        (fun m' => memberEq m' (renameMember πmap m))).getD false) = true := by
  decide

theorem srcNoSentinelG :
    srcMembersG.all (fun p =>
      !(occursConst 9999 p.2.mtype) &&
        (p.2.body.all (fun b => !(occursConst 9999 b)))) = true := by decide


/-! ## Expanded-literal machine checks (stage 1a F2 → R3) -/

/-- Measurement-only literal expansion applied to a member record. -/
def xMem (m : CheckedMember) : CheckedMember :=
  ⟨m.mclass, m.arity, expandLits m.mtype, m.body.map expandLits⟩

/-- `xEnv` maps every member of an env through `xMem`. -/
def xEnv (E : ResolvedEnv) : ResolvedEnv :=
  ⟨fun c => (E.members c).map xMem⟩

/-- The prefix env: every table member with slot `< r`. -/
def srcPrefixEnv (r : Nat) : ResolvedEnv :=
  (srcMembersG.filter (fun p => p.1 < r)).foldl
    (fun E (r, m) => extendEnv E r m) emptyEnv

/-- Bool readout: `infer` of the expanded mtype yields a sort. -/
private def inferSortsX (r : Nat) (m : CheckedMember) : Bool :=
  match kernelStepRaw
      ⟨⟨xEnv (srcPrefixEnv r), 0, []⟩, .infer (expandLits m.mtype), 65536⟩ with
  | .result (.accepted (.inferredType (.sort _))) => true
  | _ => false

/-- Every inductive and constructor member's expanded mtype infers to
    a sort in the `xEnv`-expanded prefix env. -/
theorem srcTypesOkX :
    srcMembersG.all (fun p =>
      if decide (p.2.mclass = .inductiveM) ||
          decide (p.2.mclass = .constructorM)
      then inferSortsX p.1 p.2 else true) = true := by decide

/-- `nthBNilVa`'s expanded body does not machine-check against its
    expanded type: `BL.rec.{1}` is outside the machine's const-level
    slice. The declarative typing is `tyThm159` (ScmSrcGroupsConv). -/
theorem checkmNthBNilVa :
    kernelStepRaw ⟨⟨srcPrefixEnv 159, 0, []⟩,
        .check (expandLits (mNthBNilVa.body.getD (.sort .zero)))
          (expandLits mNthBNilVa.mtype), 65536⟩ =
      .result (.refused "[rcic_infer_const_levels_out_of_slice]") := by rfl

/- RETIRED (convCert `.app` arm refusal re-labelling, R-Retire):
the `.app`/`.app` congruence arm no longer forwards a refused
sub-call's residue — it answers `convMismatchResidue A l r`, the
pre-arm catch-all, so this check lands `[rcic_conv_mismatch]`, not
`[rcic_whnf_unknown_ctor]`. Text kept, not compiled; the corrected
expectation is `checkmVLBNil_convMismatch` below. Not weakened.
  /-- `vLBNil`'s expanded body does not machine-check against its
      expanded type in the unexpanded prefix env: the `.app` congruence
      descent reaches a `.lit` leaf, which whnf refuses. The two proofs
      differ only by proof irrelevance, which the machine does not
      implement; the declarative typing is `tyThm160` (ScmSrcGroupsConv). -/
  theorem checkmVLBNil :
      kernelStepRaw ⟨⟨srcPrefixEnv 160, 0, []⟩,
          .check (expandLits (mVLBNil.body.getD (.sort .zero)))
            (expandLits mVLBNil.mtype), 65536⟩ =
        .result (.refused "[rcic_whnf_unknown_ctor]") := by rfl
-/

/-- `vLBNil`'s expanded body does not machine-check against its
    expanded type in the unexpanded prefix env: the `.app` congruence
    arm's refusal is the match's own `[rcic_conv_mismatch]` residue
    (the two proofs still differ only by proof irrelevance, which the
    machine does not implement; the declarative typing is `tyThm160`
    (ScmSrcGroupsConv)). -/
theorem checkmVLBNil_convMismatch :
    kernelStepRaw ⟨⟨srcPrefixEnv 160, 0, []⟩,
        .check (expandLits (mVLBNil.body.getD (.sort .zero)))
          (expandLits mVLBNil.mtype), 65536⟩ =
      .result (.refused "[rcic_conv_mismatch]") := by rfl

#print axioms srcLayoutG
#print axioms srcCountsG
#print axioms srcV1CorrG
#print axioms srcNoSentinelG
#print axioms srcEnvG_eq
#print axioms srcTypesOkX
#print axioms checkmNthBNilVa
#print axioms checkmVLBNil_convMismatch


end Rcic.Scm.SrcG
