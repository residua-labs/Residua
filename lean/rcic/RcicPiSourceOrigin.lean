import rcic.RcicPEqLeafTProp
import rcic.RcicParRedCore

/-!
# Pi head escape exposes one local U task

Original candidate basis: 176f97198eabe088ccce4d73cf37d7897eca19c3.
Native-checked against unchanged original dependencies at a2ccbd6090.
No original judgment or reduction is changed. Registration is additive.

The `OriginTrace` below is occurrence evidence about an EXISTING reduction
proof. It is not a replacement conversion or reduction relation. Its only
paths are a proof-root `peq`, and the original `conv.h`/`iotaSpine.hstep`
fields. Consequently the two HasTyT inputs selected for U are original
fields of the supplied reduction, not transported endpoint derivations.

The claim is a decomposition, not global uniqueness or head rigidity:
  a Pi-source step either keeps its Pi head, or exposes such an origin.
An origin produces a SINGLE outstanding type-chain problem. If that one
problem is solved, the existing proof-index constructor terminates an
arbitrary peak, at the original index, without re-entering P on outputs.

Important: the local size bound is relative to the supplied ParRedT.
If J/D fabricated that ParRedT, this is NOT yet a bound relative to J/D's
own input. That bridge, the complete U/X/P and the rigid/rigid cases remain
unpaid. The original candidate and its pins were native-checked before
this registration. closure_claim=0.
-/

namespace Rcic.Declarative.F8PiSourceOrigin

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- Existing judgment-node counter, specialized to the actual leaf. -/
abbrev stepSize {a b T : Expr Nat}
    (h : ParRedT (PEqLeafT E n) E n Γ a b T) : Nat :=
  parRedTSize (fun leaf => peqLeafTSize leaf) h

/-- A local uniqueness request and a type-index continuation.
`originTyping` and `proofTyping` have the SAME term index a.
`back` is used only after U returns; it is not fed into that U call. -/
structure Origin (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (a T : Expr Nat) where
  originIndex : Expr Nat
  proposition : Expr Nat
  propositionTyping : HasTyT E n Γ proposition (.sort .zero)
  originTyping : HasTyT E n Γ a originIndex
  proofTyping : HasTyT E n Γ a proposition
  back : TyConvT E n Γ T originIndex

/-- The exact weak uniqueness OUTPUT still to be supplied. -/
abbrev Origin.Answer {a T : Expr Nat} (o : Origin E n Γ a T) : Type :=
  TyConvT E n Γ o.originIndex o.proposition

/-- Cost of the two actual typings given to U, before any retyping. -/
def Origin.cost {a T : Expr Nat} (o : Origin E n Γ a T) : Nat :=
  hasTyTSize o.originTyping + hasTyTSize o.proofTyping

/-- Compose index chains in the needed direction, without running U. -/
def Origin.reindex {a T U : Expr Nat}
    (o : Origin E n Γ a T) (hTU : TyConvT E n Γ T U) :
    Origin E n Γ a U :=
  ⟨o.originIndex, o.proposition, o.propositionTyping,
    o.originTyping, o.proofTyping,
    .trans Γ U T o.originIndex hTU.symmT o.back⟩

/-- Retargeting the continuation does not replace either U input. -/
theorem Origin.reindex_cost {a T U : Expr Nat}
    (o : Origin E n Γ a T) (hTU : TyConvT E n Γ T U) :
    (o.reindex hTU).cost = o.cost := rfl

/-- A proof-root occurrence, with source-preserving wrappers only.
All HasTyT arguments of `proof` are literally the fields of its index. -/
inductive OriginTrace {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    {a b T : Expr Nat} →
    ParRedT (PEqLeafT E n) E n Γ a b T → Type where
  | proof {a b T P Q : Expr Nat}
      (hP : HasTyT E n Γ P (.sort .zero))
      (hQ : HasTyT E n Γ Q (.sort .zero))
      (hp : HasTyT E n Γ a P) (hq : HasTyT E n Γ b Q)
      (ha : HasTyT E n Γ a T) (hb : HasTyT E n Γ b T) :
      OriginTrace (ParRedT.peq Γ a b T
        ⟨PEqT.proof Γ a b P Q hP hQ hp hq, ha, hb⟩)
  | conv {a b T U : Expr Nat}
      {h : ParRedT (PEqLeafT E n) E n Γ a b T}
      (hc : TyConvT E n Γ T U) (ht : OriginTrace h) :
      OriginTrace (ParRedT.conv Γ a b T U h hc)
  | iotaSpine {a b c T : Expr Nat}
      {h : ParRedT (PEqLeafT E n) E n Γ a b T}
      (hi : DerivedIotaU E b c)
      (hb : HasTyT E n Γ b T) (hc : HasTyT E n Γ c T)
      (ht : OriginTrace h) :
      OriginTrace (ParRedT.iotaSpine Γ a b c T h hi hb hc)

/-- Extract the source's original pair; build only the continuation.
No typing transport occurs in this traversal. -/
def OriginTrace.origin : {a b T : Expr Nat} →
    {h : ParRedT (PEqLeafT E n) E n Γ a b T} →
    OriginTrace h → Origin E n Γ a T
  | _, _, T, _, .proof hP _ hp _ ha _ =>
      ⟨T, _, hP, ha, hp, .refl Γ T⟩
  | _, _, _, _, .conv hc ht => (OriginTrace.origin ht).reindex hc
  | _, _, _, _, .iotaSpine _ _ _ ht => OriginTrace.origin ht

/-- The local U request is strictly smaller than the actual reduction
containing it, using the existing counters. This is NOT a global U/X/P
termination theorem and does not rank any generated continuation. -/
theorem OriginTrace.cost_lt : {a b T : Expr Nat} →
    {h : ParRedT (PEqLeafT E n) E n Γ a b T} →
    (ht : OriginTrace h) → ht.origin.cost < stepSize h
  | _, _, _, _, .proof hP hQ hp hq ha hb => by
      simp only [OriginTrace.origin, Origin.cost, stepSize,
        parRedTSize, peqLeafTSize, peqTSize]
      omega
  | _, _, _, _, .conv hc ht => by
      have ih := OriginTrace.cost_lt ht
      simp only [OriginTrace.origin, Origin.reindex_cost, stepSize,
        parRedTSize] at *
      omega
  | _, _, _, _, .iotaSpine hi hb hc ht => by
      have ih := OriginTrace.cost_lt ht
      simp only [OriginTrace.origin, stepSize, parRedTSize] at *
      omega

/-- Shape-only data: does not claim component conversion or typing. -/
structure PiHead (b : Expr Nat) where
  domain : Expr Nat
  codomain : Expr Nat
  shape : b = .pi domain codomain

/-- Both existing union witnesses have application-headed sources. -/
private theorem iota_source_not_pi {lhs rhs A B : Expr Nat}
    (h : DerivedIotaU E lhs rhs) (heq : lhs = .pi A B) : False := by
  cases h with
  | ofU w =>
      exact foldApps_snoc_ne_pi (.const w.recRef w.ls)
        (ctorMajor w) w.preMajor heq
  | ofUS w =>
      exact foldApps_snoc_ne_pi (.const w.recRef w.ls)
        (foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields))
        w.preMajor heq

/-- For an ACTUAL Pi-source leaf, the only roots are structural pi
or proof. No assumption says a typed Pi cannot be a proof. -/
def leaf_head_or_origin {A B b T : Expr Nat}
    (h : PEqLeafT E n Γ (.pi A B) b T) :
    Sum (PiHead b) (OriginTrace (ParRedT.peq Γ (.pi A B) b T h)) :=
  match h with
  | ⟨.pi _ _ A' _ B' _ _, _, _⟩ => .inl ⟨A', B', rfl⟩
  | ⟨.proof _ _ _ _ _ hP hQ hp hq, ha, hb⟩ =>
      .inr (.proof hP hQ hp hq ha hb)

/-- COVERAGE, with no U/row/separation premise: every Pi-source input
keeps its target's Pi head OR locates one original proof-root occurrence.
Recursion is only on the original conv.h / iotaSpine.hstep fields.
The structural PEq.pi branch supplies HEAD SHAPE ONLY, not reversal. -/
def pi_source_head_or_origin :
    {a b T : Expr Nat} →
    (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    {A B : Expr Nat} → a = .pi A B → Sum (PiHead b) (OriginTrace h)
  | _, _, _, .refl _ _ _ _, A, B, heq => .inl ⟨A, B, heq⟩
  | _, _, _, .sortEq .., _, _, heq => nomatch heq
  | _, _, _, .consts .., _, _, heq => nomatch heq
  | _, _, _, .bvarZeta .., _, _, heq => nomatch heq
  | _, _, _, .delta .., _, _, heq => nomatch heq
  | _, _, _, .app .., _, _, heq => nomatch heq
  | _, _, _, .beta .., _, _, heq => nomatch heq
  | _, _, _, .lam .., _, _, heq => nomatch heq
  | _, _, _, .pi _ _ A' _ B' _ _ _ _ _ _ _, _, _, _ =>
      .inl ⟨A', B', rfl⟩
  | _, _, _, .letE .., _, _, heq => nomatch heq
  | _, _, _, .zeta .., _, _, heq => nomatch heq
  | _, _, _, .iotaSpine _ _ _ _ _ hstep hi hred hrhs, _, _, heq =>
      match pi_source_head_or_origin hstep heq with
      | .inl head => False.elim (iota_source_not_pi hi head.shape)
      | .inr ht => .inr (.iotaSpine hi hred hrhs ht)
  | _, _, _, .iotaStarK .., _, _, heq => by
      simp only [recCall, foldApps_snoc] at heq
      exact nomatch heq
  | _, _, _, .iotaStarKEta _ _ _ _ _ _ _ _ _ _ happ .., _, _, heq => by
      have hhd := (iotaStarKEta_head happ).1
      rw [heq] at hhd
      exact nomatch hhd
  | _, _, _, .lit .., _, _, heq => nomatch heq
  | _, _, _, .eta .., _, _, heq => nomatch heq
  | _, _, _, .peq _ _ _ _ hleaf, _, _, heq => by
      subst heq
      exact leaf_head_or_origin hleaf
  | _, _, _, .conv _ _ _ _ _ h hc, _, _, heq =>
      match pi_source_head_or_origin h heq with
      | .inl head => .inl head
      | .inr ht => .inr (.conv hc ht)

/-- A non-Pi target cannot avoid the original proof-root occurrence.
Still no claim that this occurrence is inconsistent. -/
def pi_escape_origin {A B b T : Expr Nat}
    (h : ParRedT (PEqLeafT E n) E n Γ (.pi A B) b T)
    (hescape : ∀ C D : Expr Nat, b ≠ .pi C D) : OriginTrace h :=
  match pi_source_head_or_origin h rfl with
  | .inl head => False.elim (hescape head.domain head.codomain head.shape)
  | .inr ht => ht

/-- If the one local U request has been answered, the original shared
index has the certificate needed by the previous terminal sector. -/
def Origin.certify {a T : Expr Nat} (o : Origin E n Γ a T)
    (answer : o.Answer) : TyConvT E n Γ T o.proposition :=
  .trans Γ T o.originIndex o.proposition o.back answer

/-- Actual output at the ORIGINAL common index. The `answer` is the
single outstanding local U result, not a global uniqueness oracle. -/
def Origin.finish_peak {a b c T : Expr Nat} (o : Origin E n Γ a T)
    (answer : o.Answer)
    (h₁ : ParRedT (PEqLeafT E n) E n Γ a b T)
    (h₂ : ParRedT (PEqLeafT E n) E n Γ a c T) :
    ParRedT (PEqLeafT E n) E n Γ b c T ×'
      (ParRedT (PEqLeafT E n) E n Γ c c T ×' ConvT E n Γ b c T) :=
  parRedT_propIndex_diamond_data o.propositionTyping (o.certify answer) h₁ h₂

/-- The typed Pi-escape peak reduces to exactly the one extracted U
answer. Its input-cost certificate is `(pi_escape_origin ...).cost_lt`.
No new call is made on the generated leaf or its reconciliation. -/
def pi_escape_peak_of_one_answer {A B b c T : Expr Nat}
    (h₁ : ParRedT (PEqLeafT E n) E n Γ (.pi A B) b T)
    (h₂ : ParRedT (PEqLeafT E n) E n Γ (.pi A B) c T)
    (hescape : ∀ C D : Expr Nat, b ≠ .pi C D)
    (answer : (pi_escape_origin h₁ hescape).origin.Answer) :
    ParRedT (PEqLeafT E n) E n Γ b c T ×'
      (ParRedT (PEqLeafT E n) E n Γ c c T ×' ConvT E n Γ b c T) :=
  (pi_escape_origin h₁ hescape).origin.finish_peak answer h₁ h₂

end Rcic.Declarative.F8PiSourceOrigin
