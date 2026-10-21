import rcic.RcicConvProofProducerCerts
import rcic.RcicProofOccurrencesPins
set_option maxRecDepth 8192

namespace Rcic.Declarative.F8ProducerPosition.Pins
open F8Occurrences PEqTProofFront F8OriginSubst
open F8OriginSubst.Pins (binder xTy yTy xAtIndex bodyIndex bodyIndexTy family familyTy argConv commonIndex)

private def cl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty
private def si : EnvMembersSubstStable emptyEnv := envWfT_subst_inst EnvWfT.empty
private def hBinder : CtxWfT emptyEnv 0 binder := .assumption [] P .zero .nil (P_ty [])

def argumentRaw : PEqT emptyEnv 0 [] p q :=
  .proof [] p q P P (P_ty []) (P_ty []) (p_ty []) (q_ty [])

def actualExposure := PEqT.instantiate0 cl si hBinder
  (p_ty []) (q_ty []) argConv xAtIndex (.bvar _ 0) argumentRaw

def actualOccurrence : RawOcc actualExposure :=
  rawOcc_transport (instantiate0_bvar_exact cl si hBinder
    (p_ty []) (q_ty []) argConv xAtIndex argumentRaw).symm PUnit.unit

def actualRequests : RawRequests actualExposure :=
  bvarHostRequests cl si hBinder (P_ty []) (p_ty []) (q_ty []) argConv xAtIndex

def actualAnswers : RawAnswered actualExposure actualRequests :=
  bvarHostAnswers cl si hBinder (P_ty []) (p_ty []) (q_ty []) argConv xAtIndex

theorem actual_left_index : (actualRequests actualOccurrence .left).index = commonIndex :=
  rawRequest_transport_index
    (instantiate0_bvar_exact cl si hBinder (p_ty []) (q_ty []) argConv xAtIndex argumentRaw).symm
    (bvarArgumentRequests cl si (P_ty []) (p_ty []) (q_ty []) xAtIndex) PUnit.unit .left

theorem actual_right_index : (actualRequests actualOccurrence .right).index = commonIndex :=
  rawRequest_transport_index
    (instantiate0_bvar_exact cl si hBinder (p_ty []) (q_ty []) argConv xAtIndex argumentRaw).symm
    (bvarArgumentRequests cl si (P_ty []) (p_ty []) (q_ty []) xAtIndex) PUnit.unit .right

theorem actual_index_nonliteral : commonIndex ≠ P := by intro h; cases h

theorem source_has_no_root :
    (rawOccurrences (PEqT.bvar (E := emptyEnv) (n := 0) binder 0)).length = 0 := rfl

theorem exposure_has_root : (rawOccurrences actualExposure).length = 1 :=
  exposure_count cl si hBinder (p_ty []) (q_ty []) argConv xAtIndex argumentRaw

/-- Two nested roots arrive from the argument even though the source is bvar. -/
def multiRaw : PEqT emptyEnv 0 [] F8OriginSubst.Pins.source F8OriginSubst.Pins.target :=
  .app [] (.lam P (.bvar 0)) (.lam P F8OriginSubst.Pins.y) p q
    (.lam [] P P (.bvar 0) F8OriginSubst.Pins.y (PEqT.refl P)
      (.proof binder (.bvar 0) F8OriginSubst.Pins.y P P
        (P_ty binder) (P_ty binder) xTy yTy)) argumentRaw

def multiLeftTy : HasTyT emptyEnv 0 [] F8OriginSubst.Pins.source commonIndex :=
  .app [] (.lam P (.bvar 0)) p P bodyIndex
    (.lam [] P .zero (.bvar 0) bodyIndex (P_ty []) xAtIndex) (p_ty [])

def multiRightTy : HasTyT emptyEnv 0 [] F8OriginSubst.Pins.target commonIndex :=
  parRedT_sr_peqT_val (F8OriginSubst.Pins.structuralInput 32)

def commonIndexTy : HasTyT emptyEnv 0 [] commonIndex (.sort .zero) :=
  substTy0 cl si (p_ty []) bodyIndexTy

def multiConv : ConvT emptyEnv 0 [] F8OriginSubst.Pins.source F8OriginSubst.Pins.target commonIndex :=
  .irr [] commonIndex _ _ commonIndexTy multiLeftTy multiRightTy

private def multiCtx : CtxWfT emptyEnv 0 [.assumption commonIndex] :=
  .assumption [] commonIndex .zero .nil commonIndexTy
private def multiBodyTy : HasTyT emptyEnv 0 [.assumption commonIndex] (.bvar 0)
    (lift 0 1 commonIndex) := .bvar _ 0 _ rfl

def multiExposure := PEqT.instantiate0 cl si multiCtx
  multiLeftTy multiRightTy multiConv multiBodyTy (.bvar _ 0) multiRaw

def multiRequests : RawRequests multiExposure :=
  exposedRequests cl si multiCtx multiLeftTy multiRightTy multiConv multiBodyTy multiRaw
    F8Occurrences.Pins.nestedRequests

def multiAnswers : RawAnswered multiExposure multiRequests :=
  exposedAnswers cl si multiCtx multiLeftTy multiRightTy multiConv multiBodyTy multiRaw
    F8Occurrences.Pins.nestedRequests F8Occurrences.Pins.nestedAnswers

theorem multi_exposure_count : (rawOccurrences multiExposure).length = 2 :=
  exposure_count cl si multiCtx multiLeftTy multiRightTy multiConv multiBodyTy multiRaw

/-- Latent irr really is an argument-field of a type-valued application conversion. -/
def fieldEnvelope : ConvT emptyEnv 0 [] (.app family p) (.app family q) (.sort .zero) :=
  .app [] family family p q P (.sort .zero) (.refl [] family (.pi P (.sort .zero)) (familyTy [])) argConv

theorem field_is_original : fieldEnvelope =
    ConvT.app [] family family p q P (.sort .zero)
      (.refl [] family (.pi P (.sort .zero)) (familyTy [])) argConv := rfl

def literalTrace : F8ConvProofProducer.Trace argConv :=
  .irr (P_ty []) (p_ty []) (q_ty [])

def indexCv : ConvT emptyEnv 0 [] commonIndex P (.sort .zero) :=
  .beta [] P P p (.sort .zero) .zero (P_ty []) (P_ty [.assumption P]) (p_ty [])

def reindexedCv : ConvT emptyEnv 0 [] p q commonIndex :=
  .tyConv [] p q P commonIndex .zero argConv (.symm [] commonIndex P (.sort .zero) indexCv)

def reindexedTrace : F8ConvProofProducer.Trace reindexedCv :=
  .tyConv (.symm [] commonIndex P (.sort .zero) indexCv) literalTrace

def wrappedCv : ConvT emptyEnv 0 [] q p commonIndex :=
  .trans [] q p p commonIndex (.symm [] p q commonIndex reindexedCv)
    (.refl [] p commonIndex (hasTyT_of_tyConvT (p_ty []) (.of [] P commonIndex .zero (.symm _ _ _ _ indexCv))))

def wrappedTrace : F8ConvProofProducer.Trace wrappedCv :=
  .transLeft (.refl [] p commonIndex
    (hasTyT_of_tyConvT (p_ty []) (.of [] P commonIndex .zero (.symm _ _ _ _ indexCv))))
    (.symm reindexedTrace)

def literalStore := F8ConvProofProducer.Trace.outputAnswers EnvWfT.empty CtxWfT.nil literalTrace

def wrappedStore := F8ConvProofProducer.Trace.outputAnswers EnvWfT.empty CtxWfT.nil wrappedTrace

theorem wrapped_index_retained (side : Side) :
    (F8ConvProofProducer.Trace.outputRequests EnvWfT.empty CtxWfT.nil wrappedTrace PUnit.unit side).index = commonIndex :=
  F8ConvProofProducer.Trace.output_index EnvWfT.empty CtxWfT.nil wrappedTrace side

/-- A certificate for the proof argument is NOT a proof-index certificate for
its type-level parent. This only excludes this trace syntax, not all proofs. -/
theorem no_parent_trace (h : F8ConvProofProducer.Trace fieldEnvelope) : False := by cases h

end Rcic.Declarative.F8ProducerPosition.Pins
