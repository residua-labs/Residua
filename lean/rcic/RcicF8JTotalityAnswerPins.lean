import Lean
import rcic.RcicF8JTotalityAnswers
import rcic.RcicF8XAdmLit
import rcic.RcicF8SepAllPins

/-!
# JT-2: a supported, structurally demanded original literal

ChatGPT's design in `S0_J_TOTALITY.md` requires a positive control with
real demand. This original `TyConvT` source inserts raw reflexivity,
symmetry and transitivity conversions at the non-Π middle of the existing
β detour. Original literal flattening retains all three source conversions,
and the five-link Stratum-B segment demands them before any supplier is selected.

The supported occurrences lie behind an unsupported β request. These
pins assert their structural demand and their actual same-output certified
J answers; they make no whole-X success or operational issued-prefix claim.
The demanded trans case executes the original Via-trans/D branch with
zero-step children. The separate landed `RcicF8JTransViaPins` module proves
the nonreflexive Via-trans control (`actual_source_valley`, `actual_D_reads`).
The empty environment's sort uniqueness is proved by the existing
`F8SepAllPins.emptyEnv_sortUnique`, never assumed. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.F8Measure.JTotality.AnswerPins

open Rcic.Syn F8Occurrences

abbrev u : Level := .imax (.succ .zero) (.succ .zero)

/-- The original β redex has an explicit original typing derivation. -/
def redexTy : HasTyT emptyEnv 0 [] betaRedex sX :=
  .app [] (.lam sX (.bvar 0)) piX sX sX
    (.lam [] sX (.succ u) (.bvar 0) sX
      (.sort [] u) (.bvar [.assumption sX] 0 sX rfl))
    (pinPiT emptyEnv 0)

def reflLiteral : ConvT emptyEnv 0 [] betaRedex betaRedex sX :=
  .refl [] betaRedex sX redexTy

def reflField : TyConvT emptyEnv 0 [] betaRedex betaRedex :=
  .of [] betaRedex betaRedex u reflLiteral

def symmLiteral : ConvT emptyEnv 0 [] betaRedex betaRedex sX :=
  .symm [] betaRedex betaRedex sX reflLiteral

def symmField : TyConvT emptyEnv 0 [] betaRedex betaRedex :=
  .of [] betaRedex betaRedex u symmLiteral

def transLiteral : ConvT emptyEnv 0 [] betaRedex betaRedex sX :=
  .trans [] betaRedex betaRedex betaRedex sX reflLiteral reflLiteral

def transField : TyConvT emptyEnv 0 [] betaRedex betaRedex :=
  .of [] betaRedex betaRedex u transLiteral

def transSuffix : TyConvT emptyEnv 0 [] betaRedex piX :=
  .trans [] betaRedex betaRedex piX transField betaD₂

def symmSuffix : TyConvT emptyEnv 0 [] betaRedex piX :=
  .trans [] betaRedex betaRedex piX symmField transSuffix

def suffix : TyConvT emptyEnv 0 [] betaRedex piX :=
  .trans [] betaRedex betaRedex piX reflField symmSuffix

/-- The independent source has three raw supported links between the β links. -/
def source : TyConvT emptyEnv 0 [] piX piX :=
  .trans [] piX betaRedex piX betaD₁ suffix

def roots : List (Jd emptyEnv 0) := [.tc source]

def rootCert : ∃ r ∈ roots, SubEq (.tc source) r :=
  ⟨.tc source, .head _, .inl rfl⟩

def firstFieldCert : ∃ r ∈ roots, SubEq (.tc betaD₁) r :=
  certOfChild (tcChildFst betaD₁ suffix) rootCert

def suffixCert : ∃ r ∈ roots, SubEq (.tc suffix) r :=
  certOfChild (tcChildSnd betaD₁ suffix) rootCert

def reflFieldCert : ∃ r ∈ roots, SubEq (.tc reflField) r :=
  certOfChild (tcChildFst reflField symmSuffix) suffixCert

def symmSuffixCert : ∃ r ∈ roots, SubEq (.tc symmSuffix) r :=
  certOfChild (tcChildSnd reflField symmSuffix) suffixCert

def symmFieldCert : ∃ r ∈ roots, SubEq (.tc symmField) r :=
  certOfChild (tcChildFst symmField transSuffix) symmSuffixCert

def transSuffixCert : ∃ r ∈ roots, SubEq (.tc transSuffix) r :=
  certOfChild (tcChildSnd symmField transSuffix) symmSuffixCert

def transFieldCert : ∃ r ∈ roots, SubEq (.tc transField) r :=
  certOfChild (tcChildFst transField betaD₂) transSuffixCert

def lastFieldCert : ∃ r ∈ roots, SubEq (.tc betaD₂) r :=
  certOfChild (tcChildSnd transField betaD₂) transSuffixCert

def firstCert : ∃ r ∈ roots,
    SubEq (.cv (.symm [] betaRedex piX sX betaRedexConv)) r :=
  certOfChild (tcChildOf _) firstFieldCert

def reflCert : ∃ r ∈ roots, SubEq (.cv reflLiteral) r :=
  certOfChild (tcChildOf reflLiteral) reflFieldCert

def symmCert : ∃ r ∈ roots, SubEq (.cv symmLiteral) r :=
  certOfChild (tcChildOf symmLiteral) symmFieldCert

def transCert : ∃ r ∈ roots, SubEq (.cv transLiteral) r :=
  certOfChild (tcChildOf transLiteral) transFieldCert

def lastCert : ∃ r ∈ roots, SubEq (.cv betaRedexConv) r :=
  certOfChild (tcChildOf betaRedexConv) lastFieldCert

def entry : XEntryW emptyEnv 0 where
  R := roots
  Γ := []
  A := .sort .zero
  B := .sort .zero
  A' := .sort .zero
  B' := .sort .zero
  c := .lit source rootCert
  hΓ := .nil
  hadm := xAdmW_of_xAdm _ (xAdm_lit source rootCert)

theorem entry_source : entry.c = EvTc.lit source rootCert := rfl

theorem entry_admitted : xAdmW entry.c = true := entry.hadm

theorem source_not_piSpined : piSpinedTc entry.c = false := by
  simp only [entry, source, piSpinedTc, piSpinedT, isPi, Bool.false_and]

theorem actual_flat_length : (flattenTc entry.c).length = 5 := by
  simp only [entry, source, suffix, symmSuffix, transSuffix, reflField,
    symmField, transField, betaD₁, betaD₂, flattenTc, flattenT,
    Flat.append, Flat.length]

def q : JRequestW entry :=
  JRequestW.at entry [.segmentHere, .linkNext, .linkHere, .ofCv]
    (.id []) reflLiteral reflCert

theorem q_source : q.h = reflLiteral := rfl

theorem q_certificate : q.hs = reflCert := rfl

theorem q_via : q.v = CtxWfVia.ofWf (CtxWfT.nil : CtxWfT emptyEnv 0 []) := rfl

theorem q_path : q.path = [.segmentHere, .linkNext, .linkHere, .ofCv] := rfl

theorem q_row : rawConstructor q.h = .refl := rfl

theorem q_not_beta : rawConstructor q.h ≠ .beta := by decide

def qSymm : JRequestW entry :=
  JRequestW.at entry [.segmentHere, .linkNext, .linkNext, .linkHere, .ofCv]
    (.id []) symmLiteral symmCert

theorem qSymm_source : qSymm.h = symmLiteral := rfl
theorem qSymm_certificate : qSymm.hs = symmCert := rfl
theorem qSymm_via :
    qSymm.v = CtxWfVia.ofWf (CtxWfT.nil : CtxWfT emptyEnv 0 []) := rfl
theorem qSymm_path :
    qSymm.path = [.segmentHere, .linkNext, .linkNext, .linkHere, .ofCv] := rfl
theorem qSymm_row : rawConstructor qSymm.h = .symm := rfl

def qTrans : JRequestW entry :=
  JRequestW.at entry [.segmentHere, .linkNext, .linkNext, .linkNext, .linkHere, .ofCv]
    (.id []) transLiteral transCert

theorem qTrans_source : qTrans.h = transLiteral := rfl
theorem qTrans_certificate : qTrans.hs = transCert := rfl
theorem qTrans_via :
    qTrans.v = CtxWfVia.ofWf (CtxWfT.nil : CtxWfT emptyEnv 0 []) := rfl
theorem qTrans_path :
    qTrans.path =
      [.segmentHere, .linkNext, .linkNext, .linkNext, .linkHere, .ofCv] := rfl
theorem qTrans_row : rawConstructor qTrans.h = .trans := rfl
theorem qTrans_not_beta : rawConstructor qTrans.h ≠ .beta := by decide

private def fixtureSegments : Segs roots [] piX piX :=
  .cons
    (.cons (.ofCv u (.lit (.symm [] betaRedex piX sX betaRedexConv) firstCert)) rfl
      (.cons (.ofCv u (.lit reflLiteral reflCert)) rfl
        (.cons (.ofCv u (.lit symmLiteral symmCert)) rfl
          (.cons (.ofCv u (.lit transLiteral transCert)) rfl
            (.cons (.ofCv u (.lit betaRedexConv lastCert)) rfl (.nil piX))))))
    rfl (.nil piX)

/-- This equality is about the existing flattening and segmentation. -/
private theorem actual_segments :
    (flattenTc entry.c).segment rfl = fixtureSegments := by
  simp only [entry, source, suffix, symmSuffix, transSuffix, reflField,
    symmField, transField, betaD₁, betaD₂, flattenTc, flattenT, Flat.append,
    Flat.segment, Flat.segmentF, Flat.length, Flat.splitPi, fixtureSegments]

/-- The middle literal is selected independently of all J answers. -/
theorem actual_need : NeedW entry q := by
  change NeedSegsW entry ((flattenTc entry.c).segment rfl) [] q
  rw [actual_segments]
  exact .head (.multiple (.tail (.head (.ofCv
    (NeedCvW.lit (C := entry) reflLiteral reflCert (.id [])
      [.segmentHere, .linkNext, .linkHere, .ofCv])))))

theorem actual_need_row : NeedRowW entry q .refl := ⟨actual_need, q_row⟩

theorem actual_symm_need : NeedW entry qSymm := by
  change NeedSegsW entry ((flattenTc entry.c).segment rfl) [] qSymm
  rw [actual_segments]
  exact .head (.multiple (.tail (.tail (.head (.ofCv
    (NeedCvW.lit (C := entry) symmLiteral symmCert (.id [])
      [.segmentHere, .linkNext, .linkNext, .linkHere, .ofCv]))))))

theorem actual_trans_need : NeedW entry qTrans := by
  change NeedSegsW entry ((flattenTc entry.c).segment rfl) [] qTrans
  rw [actual_segments]
  exact .head (.multiple (.tail (.tail (.tail (.head (.ofCv
    (NeedCvW.lit (C := entry) transLiteral transCert (.id [])
      [.segmentHere, .linkNext, .linkNext, .linkNext, .linkHere, .ofCv])))))))

theorem actual_symm_need_row : NeedRowW entry qSymm .symm :=
  ⟨actual_symm_need, qSymm_row⟩

theorem actual_trans_need_row : NeedRowW entry qTrans .trans :=
  ⟨actual_trans_need, qTrans_row⟩

theorem j1_fragment : J1.isBase q.h = true := rfl

theorem j3_fragment : J3.supported q.h = true := rfl

theorem j5a_fragment : J5a.fragment q.h = true := rfl

theorem j1_domain : J1Domain q := ⟨actual_need, j1_fragment⟩
theorem j3_domain : J3Domain q := ⟨actual_need, j3_fragment⟩
theorem j5a_domain : J5aDomain q := ⟨actual_need, j5a_fragment⟩

theorem symm_not_j1_fragment : J1.isBase qSymm.h = false := rfl
theorem symm_j3_fragment : J3.supported qSymm.h = true := rfl
theorem symm_j5a_fragment : J5a.fragment qSymm.h = true := rfl
theorem symm_j3_domain : J3Domain qSymm := ⟨actual_symm_need, symm_j3_fragment⟩

theorem trans_not_j1_fragment : J1.isBase qTrans.h = false := rfl
theorem trans_not_j3_fragment : J3.supported qTrans.h = false := rfl
theorem trans_j5a_fragment : J5a.fragment qTrans.h = true := rfl
theorem trans_j5a_domain : J5aDomain qTrans := ⟨actual_trans_need, trans_j5a_fragment⟩

theorem j1_refuses_symm : qSymm.answer (j1Via EnvWfT.empty) = none := rfl
theorem j3_refuses_trans : qTrans.answer (j3Via EnvWfT.empty) = none := rfl

def j1Out : AnswerAtW EnvWfT.empty (j1Via EnvWfT.empty) q :=
  answerJ1 EnvWfT.empty q j1_fragment

def j3Out : AnswerAtW EnvWfT.empty (j3Via EnvWfT.empty) q :=
  answerJ3 EnvWfT.empty q j3_fragment

def j5aOut : AnswerAtW EnvWfT.empty
    (j5aVia EnvWfT.empty (F8SepAllPins.emptyEnv_sortUnique 0)) q :=
  answerJ5a EnvWfT.empty (F8SepAllPins.emptyEnv_sortUnique 0) q j5a_fragment

def j3SymmOut : AnswerAtW EnvWfT.empty (j3Via EnvWfT.empty) qSymm :=
  answerJ3 EnvWfT.empty qSymm symm_j3_fragment

def j5aTransOut : AnswerAtW EnvWfT.empty
    (j5aVia EnvWfT.empty (F8SepAllPins.emptyEnv_sortUnique 0)) qTrans :=
  answerJ5a EnvWfT.empty (F8SepAllPins.emptyEnv_sortUnique 0) qTrans trans_j5a_fragment

theorem j1_returned : q.answer (j1Via EnvWfT.empty) = some j1Out.valley :=
  j1Out.returned

theorem j3_returned : q.answer (j3Via EnvWfT.empty) = some j3Out.valley :=
  j3Out.returned

theorem j5a_returned :
    q.answer (j5aVia EnvWfT.empty (F8SepAllPins.emptyEnv_sortUnique 0)) =
      some j5aOut.valley := j5aOut.returned

theorem j3_symm_returned :
    qSymm.answer (j3Via EnvWfT.empty) = some j3SymmOut.valley :=
  j3SymmOut.returned

theorem j5a_trans_returned :
    qTrans.answer (j5aVia EnvWfT.empty (F8SepAllPins.emptyEnv_sortUnique 0)) =
      some j5aTransOut.valley := j5aTransOut.returned

theorem j1_strict : ∀ ℓ ∈ j1Out.valley.leaves, SubOf ℓ (.cv q.h) := j1Out.strict

theorem j3_strict : ∀ ℓ ∈ j3Out.valley.leaves, SubOf ℓ (.cv q.h) := j3Out.strict

theorem j5a_strict : ∀ ℓ ∈ j5aOut.valley.leaves, SubOf ℓ (.cv q.h) := j5aOut.strict

theorem j3_symm_strict :
    ∀ ℓ ∈ j3SymmOut.valley.leaves, SubOf ℓ (.cv qSymm.h) := j3SymmOut.strict

theorem j5a_trans_strict :
    ∀ ℓ ∈ j5aTransOut.valley.leaves, SubOf ℓ (.cv qTrans.h) := j5aTransOut.strict

def j1Tiles : SameOutputStepCertificates EnvWfT.empty entry.R q.h j1Out.valley :=
  j1Out.tiles
def j3Tiles : SameOutputStepCertificates EnvWfT.empty entry.R q.h j3Out.valley :=
  j3Out.tiles
def j5aTiles : SameOutputStepCertificates EnvWfT.empty entry.R q.h j5aOut.valley :=
  j5aOut.tiles
def j3SymmTiles :
    SameOutputStepCertificates EnvWfT.empty entry.R qSymm.h j3SymmOut.valley :=
  j3SymmOut.tiles
def j5aTransTiles :
    SameOutputStepCertificates EnvWfT.empty entry.R qTrans.h j5aTransOut.valley :=
  j5aTransOut.tiles

/-! Expose the very D call used by the demanded trans result, with its
original children and certificates; this adds no second valley producer. -/
def transLeft : J5aVia.FragmentResult EnvWfT.empty roots reflLiteral :=
  J5aVia.build EnvWfT.empty (F8SepAllPins.emptyEnv_sortUnique 0) roots qTrans.v
    reflLiteral rfl
    (certOfChild (y := .cv transLiteral) (.head _) transCert)

def transRight : J5aVia.FragmentResult EnvWfT.empty roots reflLiteral :=
  J5aVia.build EnvWfT.empty (F8SepAllPins.emptyEnv_sortUnique 0) roots qTrans.v
    reflLiteral rfl
    (certOfChild (y := .cv transLiteral) (.tail _ (.head _)) transCert)

def actualTransD :=
  J5aVia.callD EnvWfT.empty (F8SepAllPins.emptyEnv_sortUnique 0)
    qTrans.v transLeft transRight

/-- The whole certified answer is the original Via-trans branch's valley. -/
theorem j5a_trans_actual_valley :
    j5aTransOut.valley = J5aVia.transValley EnvWfT.empty
      (F8SepAllPins.emptyEnv_sortUnique 0) qTrans.v transLeft transRight := rfl

/-- The certified actual J answer reads its center from this original D run. -/
theorem j5a_trans_D_center : j5aTransOut.valley.N = actualTransD.out.1 := rfl

/-- Alignment evidence from the actual D run, at its exact source/target spines. -/
def actualTransDReads := actualTransD.reads

end Rcic.Declarative.F8Measure.JTotality.AnswerPins

#eval (Rcic.Declarative.F8Measure.flattenTc
  Rcic.Declarative.F8Measure.JTotality.AnswerPins.entry.c).length
#eval Rcic.Declarative.F8Measure.J1.isBase
  Rcic.Declarative.F8Measure.JTotality.AnswerPins.q.h
#eval Rcic.Declarative.F8Measure.J3.supported
  Rcic.Declarative.F8Measure.JTotality.AnswerPins.q.h
#eval Rcic.Declarative.F8Measure.J5a.fragment
  Rcic.Declarative.F8Measure.JTotality.AnswerPins.q.h
#eval (Rcic.Declarative.F8Measure.JTotality.AnswerPins.q.answer
  (Rcic.Declarative.F8Measure.j1Via Rcic.Declarative.EnvWfT.empty)).isSome
#eval (Rcic.Declarative.F8Measure.JTotality.AnswerPins.q.answer
  (Rcic.Declarative.F8Measure.j3Via Rcic.Declarative.EnvWfT.empty)).isSome
#eval Rcic.Declarative.F8Measure.J1.isBase
  Rcic.Declarative.F8Measure.JTotality.AnswerPins.qSymm.h
#eval Rcic.Declarative.F8Measure.J3.supported
  Rcic.Declarative.F8Measure.JTotality.AnswerPins.qSymm.h
#eval (Rcic.Declarative.F8Measure.JTotality.AnswerPins.qSymm.answer
  (Rcic.Declarative.F8Measure.j1Via Rcic.Declarative.EnvWfT.empty)).isSome
#eval (Rcic.Declarative.F8Measure.JTotality.AnswerPins.qSymm.answer
  (Rcic.Declarative.F8Measure.j3Via Rcic.Declarative.EnvWfT.empty)).isSome
#eval Rcic.Declarative.F8Measure.J3.supported
  Rcic.Declarative.F8Measure.JTotality.AnswerPins.qTrans.h
#eval Rcic.Declarative.F8Measure.J5a.fragment
  Rcic.Declarative.F8Measure.JTotality.AnswerPins.qTrans.h
#eval (Rcic.Declarative.F8Measure.JTotality.AnswerPins.qTrans.answer
  (Rcic.Declarative.F8Measure.j3Via Rcic.Declarative.EnvWfT.empty)).isSome
#eval (Rcic.Declarative.F8Measure.JTotality.AnswerPins.qTrans.answer
  (Rcic.Declarative.F8Measure.JTotality.j5aVia Rcic.Declarative.EnvWfT.empty
    (Rcic.Declarative.F8SepAllPins.emptyEnv_sortUnique 0))).isSome

#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.actual_need
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.actual_need_row
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.actual_symm_need_row
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.actual_trans_need_row
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j1_returned
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j3_returned
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j5a_returned
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j3_symm_returned
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j5a_trans_returned
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j1_strict
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j3_strict
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j5a_strict
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j3_symm_strict
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j5a_trans_strict
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j1Tiles
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j3Tiles
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j5aTiles
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j3SymmTiles
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j5aTransTiles
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j5a_trans_actual_valley
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.j5a_trans_D_center
#print axioms Rcic.Declarative.F8Measure.JTotality.AnswerPins.actualTransDReads
