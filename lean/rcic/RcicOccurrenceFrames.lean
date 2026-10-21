import rcic.RcicProofOccurrences

/-!
# Exact-request preservation across every existing proof-occurrence frame

This module adds NO ParRedT producer and NO new relation or provenance layer.
It decomposes the already defined Requests/AnsweredOrigins into child obligations,
and reconstructs the same store at the same map. Root indices are never chosen
here; the caller's actual request map is retained. The pointwise roundtrip proves
that no request, side, or answer is replaced while crossing a structural frame.

All nine raw PEqT and all seventeen ParRedT constructors are handled explicitly.
Existing ConvT/HasTyT fields have no PEqT children; their latent J-production sites
are not asserted answered. This is a compositional preservation theorem, NOT an
arbitrary host-position map or a complete D/J producer invariant. closure_claim=0.
-/

namespace Rcic.Declarative.F8Occurrences
variable {E : ResolvedEnv} {n : Nat}

abbrev RawRequests {Γ : LCtx} {a b : Expr Nat} (h : PEqT E n Γ a b) : Type :=
  (o : RawOcc h) → (side : Side) → SiteRequest (rawSite h o) side

abbrev RawAnswered {Γ : LCtx} {a b : Expr Nat} (h : PEqT E n Γ a b)
    (requests : RawRequests h) : Type :=
  (o : RawOcc h) → (side : Side) → (requests o side).Answer

/-- Child obligations at the EXACT given map, not a synthesized easy map. -/
def RawFrameAnswers : {Γ : LCtx} → {a b : Expr Nat} → (h : PEqT E n Γ a b) → RawRequests h → Type
  | _, _, _, .bvar .., _ => PUnit
  | _, _, _, .sort .., _ => PUnit
  | _, _, _, .const .., _ => PUnit
  | _, _, _, .app _ _ _ _ _ hf ha, r => RawAnswered hf (fun o side => r (Sum.inl o) side) ×
      RawAnswered ha (fun o side => r (Sum.inr o) side)
  | _, _, _, .lam _ _ _ _ _ hA hb, r => RawAnswered hA (fun o side => r (Sum.inl o) side) ×
      RawAnswered hb (fun o side => r (Sum.inr o) side)
  | _, _, _, .pi _ _ _ _ _ hA hB, r => RawAnswered hA (fun o side => r (Sum.inl o) side) ×
      RawAnswered hB (fun o side => r (Sum.inr o) side)
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb, r => RawAnswered hA (fun o side => r (Sum.inl o) side) ×
      (RawAnswered hv (fun o side => r (Sum.inr (Sum.inl o)) side) ×
      RawAnswered hb (fun o side => r (Sum.inr (Sum.inr o)) side))
  | _, _, _, .lit .., _ => PUnit
  | _, _, _, .proof .., r => (side : Side) → (r PUnit.unit side).Answer

/-- Assemble all children without changing any original occurrence request. -/
def rawAnswers_of_frame : {Γ : LCtx} → {a b : Expr Nat} → (h : PEqT E n Γ a b) → (r : RawRequests h) →
    RawFrameAnswers h r → RawAnswered h r
  | _, _, _, .bvar .., _, _ => fun o _ => nomatch o
  | _, _, _, .sort .., _, _ => fun o _ => nomatch o
  | _, _, _, .const .., _, _ => fun o _ => nomatch o
  | _, _, _, .app _ _ _ _ _ _hf _ha, _, a => fun o side => match o with
    | Sum.inl o => a.1 o side
    | Sum.inr o => a.2 o side
  | _, _, _, .lam _ _ _ _ _ _hA _hb, _, a => fun o side => match o with
    | Sum.inl o => a.1 o side
    | Sum.inr o => a.2 o side
  | _, _, _, .pi _ _ _ _ _ _hA _hB, _, a => fun o side => match o with
    | Sum.inl o => a.1 o side
    | Sum.inr o => a.2 o side
  | _, _, _, .letE _ _ _ _ _ _ _ _hA _hv _hb, _, a => fun o side => match o with
    | (Sum.inl o) => a.1 o side
    | (Sum.inr (Sum.inl o)) => a.2.1 o side
    | (Sum.inr (Sum.inr o)) => a.2.2 o side
  | _, _, _, .lit .., _, _ => fun o _ => nomatch o
  | _, _, _, .proof .., _, a => fun _ side => a side

/-- Restrict a full store to every child; both proof sides are retained. -/
def rawFrame_of_answers : {Γ : LCtx} → {a b : Expr Nat} → (h : PEqT E n Γ a b) → (r : RawRequests h) →
    RawAnswered h r → RawFrameAnswers h r
  | _, _, _, .bvar .., _, _ => PUnit.unit
  | _, _, _, .sort .., _, _ => PUnit.unit
  | _, _, _, .const .., _, _ => PUnit.unit
  | _, _, _, .app _ _ _ _ _ _hf _ha, _, a => ⟨(fun o side => a (Sum.inl o) side), (fun o side => a (Sum.inr o) side)⟩
  | _, _, _, .lam _ _ _ _ _ _hA _hb, _, a => ⟨(fun o side => a (Sum.inl o) side), (fun o side => a (Sum.inr o) side)⟩
  | _, _, _, .pi _ _ _ _ _ _hA _hB, _, a => ⟨(fun o side => a (Sum.inl o) side), (fun o side => a (Sum.inr o) side)⟩
  | _, _, _, .letE _ _ _ _ _ _ _ _hA _hv _hb, _, a => ⟨(fun o side => a (Sum.inl o) side), ⟨(fun o side => a (Sum.inr (Sum.inl o)) side), (fun o side => a (Sum.inr (Sum.inr o)) side)⟩⟩
  | _, _, _, .lit .., _, _ => PUnit.unit
  | _, _, _, .proof .., _, a => a PUnit.unit

/-- Data-level roundtrip at every occurrence and side, without function extensionality. -/
theorem rawAnswers_frame_roundtrip {Γ : LCtx} {a b : Expr Nat}
    (h : PEqT E n Γ a b) (r : RawRequests h) (ans : RawAnswered h r)
    (o : RawOcc h) (side : Side) :
    rawAnswers_of_frame h r (rawFrame_of_answers h r ans) o side = ans o side := by
  cases h <;> cases o <;> try rfl
  rename_i o
  cases o <;> rfl

/-- Child obligations at the EXACT given map, not a synthesized easy map. -/
def FrameAnswers : {Γ : LCtx} → {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) → Requests h → Type
  | _, _, _, _, .refl .., _ => PUnit
  | _, _, _, _, .sortEq .., _ => PUnit
  | _, _, _, _, .consts .., _ => PUnit
  | _, _, _, _, .bvarZeta _ _ _ _ _ _ _ hv _ _, r => AnsweredOrigins hv (fun o side => r o side)
  | _, _, _, _, .delta .., _ => PUnit
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf _ _ _ ha _, r => AnsweredOrigins hf (fun o side => r (Sum.inl o) side) ×
      AnsweredOrigins ha (fun o side => r (Sum.inr o) side)
  | _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ _ hb ha _, r => AnsweredOrigins hb (fun o side => r (Sum.inl o) side) ×
      AnsweredOrigins ha (fun o side => r (Sum.inr o) side)
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ hb _, r => AnsweredOrigins hb (fun o side => r o side)
  | _, _, _, _, .pi .., _ => PUnit
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ hb _, r => AnsweredOrigins hv (fun o side => r (Sum.inl o) side) ×
      AnsweredOrigins hb (fun o side => r (Sum.inr o) side)
  | _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ hv _ _ hb _, r => AnsweredOrigins hv (fun o side => r (Sum.inl o) side) ×
      AnsweredOrigins hb (fun o side => r (Sum.inr o) side)
  | _, _, _, _, .iotaSpine _ _ _ _ _ hs _ _ _, r => AnsweredOrigins hs (fun o side => r o side)
  | _, _, _, _, .iotaStarK .., _ => PUnit
  | _, _, _, _, .iotaStarKEta .., _ => PUnit
  | _, _, _, _, .lit .., _ => PUnit
  | _, _, _, _, .eta _ _ _ _ _ hf _, r => AnsweredOrigins hf (fun o side => r o side)
  | _, _, _, _, .peq _ _ _ _ leaf, r => RawAnswered leaf.1 r
  | _, _, _, _, .conv _ _ _ _ _ h _, r => AnsweredOrigins h (fun o side => r o side)

/-- Assemble all children without changing any original occurrence request. -/
def answers_of_frame : {Γ : LCtx} → {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) → (r : Requests h) →
    FrameAnswers h r → AnsweredOrigins h r
  | _, _, _, _, .refl .., _, _ => fun o _ => nomatch o
  | _, _, _, _, .sortEq .., _, _ => fun o _ => nomatch o
  | _, _, _, _, .consts .., _, _ => fun o _ => nomatch o
  | _, _, _, _, .bvarZeta _ _ _ _ _ _ _ _hv _ _, _, a => a
  | _, _, _, _, .delta .., _, _ => fun o _ => nomatch o
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ _hf _ _ _ _ha _, _, a => fun o side => match o with
    | Sum.inl o => a.1 o side
    | Sum.inr o => a.2 o side
  | _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ _ _hb _ha _, _, a => fun o side => match o with
    | Sum.inl o => a.1 o side
    | Sum.inr o => a.2 o side
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ _hb _, _, a => a
  | _, _, _, _, .pi .., _, _ => fun o _ => nomatch o
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ _hv _ _ _hb _, _, a => fun o side => match o with
    | Sum.inl o => a.1 o side
    | Sum.inr o => a.2 o side
  | _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ _hv _ _ _hb _, _, a => fun o side => match o with
    | Sum.inl o => a.1 o side
    | Sum.inr o => a.2 o side
  | _, _, _, _, .iotaSpine _ _ _ _ _ _hs _ _ _, _, a => a
  | _, _, _, _, .iotaStarK .., _, _ => fun o _ => nomatch o
  | _, _, _, _, .iotaStarKEta .., _, _ => fun o _ => nomatch o
  | _, _, _, _, .lit .., _, _ => fun o _ => nomatch o
  | _, _, _, _, .eta _ _ _ _ _ _hf _, _, a => a
  | _, _, _, _, .peq _ _ _ _ _leaf, _, a => a
  | _, _, _, _, .conv _ _ _ _ _ _h _, _, a => a

/-- Restrict a full store to every child; both proof sides are retained. -/
def frame_of_answers : {Γ : LCtx} → {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) → (r : Requests h) →
    AnsweredOrigins h r → FrameAnswers h r
  | _, _, _, _, .refl .., _, _ => PUnit.unit
  | _, _, _, _, .sortEq .., _, _ => PUnit.unit
  | _, _, _, _, .consts .., _, _ => PUnit.unit
  | _, _, _, _, .bvarZeta _ _ _ _ _ _ _ _hv _ _, _, a => a
  | _, _, _, _, .delta .., _, _ => PUnit.unit
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ _hf _ _ _ _ha _, _, a => ⟨(fun o side => a (Sum.inl o) side), (fun o side => a (Sum.inr o) side)⟩
  | _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ _ _hb _ha _, _, a => ⟨(fun o side => a (Sum.inl o) side), (fun o side => a (Sum.inr o) side)⟩
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ _hb _, _, a => a
  | _, _, _, _, .pi .., _, _ => PUnit.unit
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ _hv _ _ _hb _, _, a => ⟨(fun o side => a (Sum.inl o) side), (fun o side => a (Sum.inr o) side)⟩
  | _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ _hv _ _ _hb _, _, a => ⟨(fun o side => a (Sum.inl o) side), (fun o side => a (Sum.inr o) side)⟩
  | _, _, _, _, .iotaSpine _ _ _ _ _ _hs _ _ _, _, a => a
  | _, _, _, _, .iotaStarK .., _, _ => PUnit.unit
  | _, _, _, _, .iotaStarKEta .., _, _ => PUnit.unit
  | _, _, _, _, .lit .., _, _ => PUnit.unit
  | _, _, _, _, .eta _ _ _ _ _ _hf _, _, a => a
  | _, _, _, _, .peq _ _ _ _ _leaf, _, a => a
  | _, _, _, _, .conv _ _ _ _ _ _h _, _, a => a

/-- Data-level roundtrip at every occurrence and side, without function extensionality. -/
theorem answers_frame_roundtrip {Γ : LCtx} {a b T : Expr Nat}
    (h : ParRedT (PEqLeafT E n) E n Γ a b T) (r : Requests h)
    (ans : AnsweredOrigins h r) (o : Occ h) (side : Side) :
    answers_of_frame h r (frame_of_answers h r ans) o side = ans o side := by
  cases h <;> try rfl
  all_goals cases o <;> rfl

end Rcic.Declarative.F8Occurrences
