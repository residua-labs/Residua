import rcic.RcicParRedTSR
import rcic.RcicTypedConv
import rcic.RcicPEqTCtx

/-!
# The proof-index sector of the actual `PEqLeafT` and `ParRedT`

A common index `T` with a supplied chain `T ~ P` and an actual typing
`P : Prop` is enough to reconcile ANY two terms already typed at `T`.
Retype both terms to P, use the existing proof-irrelevance constructor,
and transport the conversion back to T. The original endpoint typings
remain the endpoint fields of `PEqLeafT`: no relation is replaced.

This closes mixed proof/structural composition in this sector without
traversing the raw PEqT witnesses. It also joins arbitrary one-step OR
finite-star peaks of the real `ParRedT (PEqLeafT E n)`: both final terms
are typed at T, so they join in one step at the right endpoint. The
producer returns an actual `ConvT` reconciliation at T as well.

The hTP chain is INPUT, not inferred from a loose proof leaf or from
uniqueness. The important special case T=P uses `TyConvT.refl`. Without
this proposition/index evidence the constructions are not asserted.
In particular `T = sort 0` is an index of propositions, not in itself a
propositional index of proofs. No type-level Pi leaf is discharged here.

No EnvWfT, InScope, semantic prefix, Pi row, uniqueness, raw symmetry or
raw transitivity assumption is used in the core constructions. The
endpoint projection for one-step peaks is the existing structural S
component; a star's final typing is its existing terminal refl field.
The constructed reconciliation never re-enters U, X or P. No decrease
claim is made about the produced evidence. `closure_claim = 0`.
-/

namespace Rcic.Declarative

section ProofIndex
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
variable {a b c T U P : Expr Nat}

/-- Terminal proof-sector reconciliation at the ORIGINAL index T.
Both actual T-typings are necessary inputs, unlike the refuted raw
proof supplier. hTP may be any finite TyConvT chain. -/
def peqLeafT_reconcile_propIndex
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (ha : HasTyT E n Γ a T) (hb : HasTyT E n Γ b T) :
    PEqLeafT E n Γ a b T ×' ConvT E n Γ a b T :=
  let haP := hasTyT_of_tyConvT ha hTP
  let hbP := hasTyT_of_tyConvT hb hTP
  ⟨⟨.proof Γ a b P P hP hP haP hbP, ha, hb⟩,
    convT_of_tyConv (.irr Γ P a b hP haP hbP) hTP.symmT⟩

/-- Re-index the original wrapper without changing its raw comparison.
This general transport needs the supplied type chain, not a row. -/
def peqLeafT_retype (hTU : TyConvT E n Γ T U)
    (h : PEqLeafT E n Γ a b T) : PEqLeafT E n Γ a b U :=
  ⟨h.1, hasTyT_of_tyConvT h.2.1 hTU, hasTyT_of_tyConvT h.2.2 hTU⟩

/-- Transport the actual wrapper along an ALREADY SUPPLIED context
conversion. No hdom/hlet supplier is reconstructed from raw PEqT. -/
def peqLeafT_ctx (hcl : EnvClosed E) {Γ' : LCtx}
    (hcc : CtxConvT E n Γ Γ') (h : PEqLeafT E n Γ a b T) :
    PEqLeafT E n Γ' a b T :=
  ⟨PEqT.ctx hcl hcc h.1, hasTyT_ctx hcl hcc h.2.1,
    hasTyT_ctx hcl hcc h.2.2⟩

/-- Any raw constructor may occur in h: in this proof sector the
endpoints alone suffice to construct the reverse actual leaf. -/
def peqLeafT_symm_of_propIndex
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (h : PEqLeafT E n Γ a b T) : PEqLeafT E n Γ b a T :=
  (peqLeafT_reconcile_propIndex hP hTP h.2.2 h.2.1).1

/-- Mixed structural/proof composition at a certified proof index.
This does not use or supply raw PEqT transitivity. -/
def peqLeafT_trans_of_propIndex
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (hab : PEqLeafT E n Γ a b T) (hbc : PEqLeafT E n Γ b c T) :
    PEqLeafT E n Γ a c T :=
  (peqLeafT_reconcile_propIndex hP hTP hab.2.1 hbc.2.2).1

/-- The same composition with a supplied index-change chain on the
second edge; the result remains at the FIRST edge's index T. -/
def peqLeafT_trans_retype_of_propIndex
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (hUT : TyConvT E n Γ U T)
    (hab : PEqLeafT E n Γ a b T) (hbc : PEqLeafT E n Γ b c U) :
    PEqLeafT E n Γ a c T :=
  peqLeafT_trans_of_propIndex hP hTP hab (peqLeafT_retype hUT hbc)

/-- P's terminal conversion output in the proof-index sector. -/
def peqLeafT_conv_of_propIndex
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (h : PEqLeafT E n Γ a b T) : ConvT E n Γ a b T :=
  (peqLeafT_reconcile_propIndex hP hTP h.2.1 h.2.2).2

private def proofIndex_join
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (hb : HasTyT E n Γ b T) (hc : HasTyT E n Γ c T) :
    ParRedT (PEqLeafT E n) E n Γ b c T ×'
      (ParRedT (PEqLeafT E n) E n Γ c c T ×' ConvT E n Γ b c T) :=
  let ⟨leaf, conv⟩ := peqLeafT_reconcile_propIndex hP hTP hb hc
  ⟨.peq Γ b c T leaf, .refl Γ c T hc, conv⟩

/-- Strong diamond of the actual typed reduction in a certified proof
sector. Arbitrary constructors, including conv/eta/iota, are permitted
in both input derivations. The join is c, not a normalized value. -/
def parRedT_propIndex_diamond_data
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (hab : ParRedT (PEqLeafT E n) E n Γ a b T)
    (hac : ParRedT (PEqLeafT E n) E n Γ a c T) :
    ParRedT (PEqLeafT E n) E n Γ b c T ×'
      (ParRedT (PEqLeafT E n) E n Γ c c T ×' ConvT E n Γ b c T) :=
  proofIndex_join hP hTP (parRedT_sr_peqT_val hab) (parRedT_sr_peqT_val hac)

/-- Reversal at a proof index. CtxWfT is used only to project the
original source typing with the existing ParRedT endpoint theorem. -/
def parRedT_propIndex_reverse
    (hΓ : CtxWfT E n Γ)
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (hab : ParRedT (PEqLeafT E n) E n Γ a b T) :
    ParRedT (PEqLeafT E n) E n Γ b a T :=
  let ha := parRedT_hasTy_left (fun h => ⟨h.2.1, h.2.2⟩) hΓ hab
  .peq Γ b a T
    (peqLeafT_reconcile_propIndex hP hTP (parRedT_sr_peqT_val hab) ha).1

/-- A star already terminates in a refl with the final typing. This
recursion is only on its ORIGINAL tail, not on produced evidence. -/
private def star_final_typing
    {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type} :
    {a b T : Expr Nat} → ParRedTStar PEq E n Γ a b T → HasTyT E n Γ b T
  | _, _, _, .refl _ _ _ ht => ht
  | _, _, _, .tail _ hs => star_final_typing hs

/-- Every FINITE peak in this sector joins in one step on each side,
and produces reconciliation without a new call on its generated leaf. -/
def parRedTStar_propIndex_diamond_data
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (hab : ParRedTStar (PEqLeafT E n) E n Γ a b T)
    (hac : ParRedTStar (PEqLeafT E n) E n Γ a c T) :
    ParRedT (PEqLeafT E n) E n Γ b c T ×'
      (ParRedT (PEqLeafT E n) E n Γ c c T ×' ConvT E n Γ b c T) :=
  proofIndex_join hP hTP (star_final_typing hab) (star_final_typing hac)

/-- Standard fixed-index star-confluence conclusion for that sector.
No termination/normalization premise or proof is used. -/
theorem parRedTStar_propIndex_confluent
    (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (hab : ParRedTStar (PEqLeafT E n) E n Γ a b T)
    (hac : ParRedTStar (PEqLeafT E n) E n Γ a c T) :
    ∃ d : Expr Nat,
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ b d T) ∧
      Nonempty (ParRedTStar (PEqLeafT E n) E n Γ c d T) := by
  let ⟨hbc, _, _⟩ := parRedTStar_propIndex_diamond_data hP hTP hab hac
  let hc := star_final_typing hac
  exact ⟨c, ⟨.tail hbc (.refl Γ c T hc)⟩, ⟨.refl Γ c T hc⟩⟩

end ProofIndex
end Rcic.Declarative
