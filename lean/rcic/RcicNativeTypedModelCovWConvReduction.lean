import rcic.RcicNativeTypedModelCovWConvK

namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

open FamModelAudit ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit FamModelLRSAudit

/-!
Typed occurrences of native CK2 steps.  Each primitive constructor records
the premises of the corresponding `ConvT` rule.  The K constructor uses the
checked K occurrence data, and the application constructors retain the
actual dependent function domain and codomain.

Eta is defined separately below: it has a typed conversion interpretation,
but is not a constructor of the native `WhStepCtx` or `WhStepCK2` relation.
-/

inductive CovWConvReduction (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Expr Nat → Prop where
  | beta (A body arg B : Expr Nat) (u : Level)
      (hA : HasTyT E n Γ A (.sort u))
      (hbody : HasTyT E n (.assumption A :: Γ) body B)
      (harg : HasTyT E n Γ arg A) :
      CovWConvReduction E n Γ
        (.app (.lam A body) arg) (instantiate0 arg body) (instantiate0 arg B)
  | zeta (A value body B : Expr Nat) (u : Level)
      (hA : HasTyT E n Γ A (.sort u))
      (hv : HasTyT E n Γ value A)
      (hb : HasTyT E n (.letBinding A value :: Γ) body B) :
      CovWConvReduction E n Γ
        (.letE A value body) (instantiate0 value body) (instantiate0 value B)
  | zetaLocal (i : Nat) (A v : Expr Nat)
      (hval : lookupValue Γ i = some v)
      (hty : lookupType Γ i = some A)
      (hv : HasTyT E n Γ v A) :
      CovWConvReduction E n Γ (.bvar i) v A
  | delta (r : Nat) (ls : List Level) (m : CheckedMember) (b : Expr Nat)
      (hres : E.members r = some m)
      (hbody : m.body = some b)
      (htr : transparent m.mclass = true)
      (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true)
      (hb : HasTyT E n Γ (instantiateLevels ls b)
        (instantiateLevels ls m.mtype)) :
      CovWConvReduction E n Γ
        (.const r ls) (instantiateLevels ls b) (instantiateLevels ls m.mtype)
  | iota (lhs rhs T : Expr Nat)
      (hi : DerivedIota E lhs rhs)
      (hlhs : HasTyT E n Γ lhs T)
      (hrhs : HasTyT E n Γ rhs T) :
      CovWConvReduction E n Γ lhs rhs T
  | lit (t : Nat) (T : Expr Nat)
      (hexpansion : LiteralExpansion t (natExpand t))
      (hexp : HasTyT E n Γ (natExpand t) T) :
      CovWConvReduction E n Γ (.lit t) (natExpand t) T
  | k {w} {x T : Expr Nat} (h : CovWConvKData E n Γ w x T) :
      CovWConvReduction E n Γ
        (recCall (.const w.recRef w.ls) w.preMajor x) (iotaRhsOf w) T
  | appHead {f g a A B : Expr Nat}
      (h : CovWConvReduction E n Γ f g (.pi A B))
      (ha : HasTyT E n Γ a A) :
      CovWConvReduction E n Γ (.app f a) (.app g a) (instantiate0 a B)
  | recMajor {r : Nat} {m : CheckedMember} {ls : List Level}
      {pre : List (Expr Nat)} {x x' A B : Expr Nat}
      (hprefix : HasTyT E n Γ (foldApps (.const r ls) pre) (.pi A B))
      (hm : E.members r = some m)
      (hrec : m.mclass = .recursorM)
      (hlen : pre.length + 1 = piCount m.mtype)
      (hnK : ¬ KFreeRec E r)
      (hnP : ¬ KProjRec E r)
      (h : CovWConvReduction E n Γ x x' A) :
      CovWConvReduction E n Γ
        (recCall (.const r ls) pre x)
        (recCall (.const r ls) pre x') (instantiate0 x B)
  | retype {a b A B : Expr Nat}
      (h : CovWConvReduction E n Γ a b A)
      (hc : TyConvT E n Γ A B) :
      CovWConvReduction E n Γ a b B

theorem covWConv_reduction_sound {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CovWConvReduction E n Γ a b T) :
    Nonempty (ConvT E n Γ a b T) := by
  induction h with
  | beta A body arg B u hA hbody harg =>
      exact ⟨.beta Γ A body arg B u hA hbody harg⟩
  | zeta A value body B u hA hv hb =>
      exact ⟨.zeta Γ A value body B u hA hv hb⟩
  | zetaLocal i A v hval hty hv =>
      exact ⟨.zetaLocal Γ i A v hval hty hv⟩
  | delta r ls m body hres hbody htr hlen hwf hb =>
      exact ⟨.delta Γ r ls m body hres hbody htr hlen hwf hb⟩
  | iota lhs rhs T hi hlhs hrhs =>
      exact ⟨.iota Γ lhs rhs T hi hlhs hrhs⟩
  | lit t T hexpansion hexp =>
      exact ⟨.lit Γ t (natExpand t) T hexpansion hexp⟩
  | k h =>
      exact covWConv_K_sound h
  | appHead h ha ih =>
      rcases ih with ⟨cfun⟩
      exact ⟨.app Γ _ _ _ _ _ _ cfun (.refl Γ _ _ ha)⟩
  | recMajor hprefix hm hrec hlen hnK hnP h ih =>
      rcases ih with ⟨cmajor⟩
      simpa only [recCall_eq_app] using
        (show Nonempty (ConvT E n Γ _ _ _) from ⟨.app Γ _ _ _ _ _ _ (.refl Γ _ _ hprefix) cmajor⟩)
  | retype h hc ih =>
      rcases ih with ⟨c⟩
      exact ⟨convT_of_tyConv c hc⟩

theorem covWConv_reduction_native {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CovWConvReduction E n Γ a b T) :
    WhStepCK2 E n Γ a b := by
  induction h with
  | beta A body arg B u hA hbody harg =>
      exact .ctx (.beta A body arg)
  | zeta A value body B u hA hv hb =>
      exact .ctx (.zeta A value body)
  | zetaLocal i A v hval hty hv =>
      exact .ctx (.zetaLocal hval)
  | delta r ls m body hres hbody htr hlen hwf hb =>
      exact .ctx (.delta hres hbody)
  | iota lhs rhs T hi hlhs hrhs =>
      exact .ctx (.iota (derivedIotaU_ofDerivedIota hi))
  | lit t T hexpansion hexp =>
      exact .ctx (.lit t)
  | k h =>
      exact covWConv_K_native h
  | appHead h ha ih =>
      exact .appHead ih
  | recMajor hprefix hm hrec hlen hnK hnP h ih =>
      exact .recMajor hm hrec hlen hnK hnP ih
  | retype h hc ih =>
      exact ih

/-- Explicit reflexive-transitive closure of the existing native CK2 relation. -/
inductive CovWConvCK2Star (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Prop where
  | refl (a : Expr Nat) : CovWConvCK2Star E n Γ a a
  | single {a b : Expr Nat} (h : WhStepCK2 E n Γ a b) :
      CovWConvCK2Star E n Γ a b
  | trans {a b c : Expr Nat}
      (h₁ : CovWConvCK2Star E n Γ a b)
      (h₂ : CovWConvCK2Star E n Γ b c) :
      CovWConvCK2Star E n Γ a c

/-- A finite reduction chain at one fixed type; reflexivity records actual typing. -/
inductive CovWConvReductionStar (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Expr Nat → Prop where
  | refl {a T : Expr Nat} (ha : HasTyT E n Γ a T) :
      CovWConvReductionStar E n Γ a a T
  | single {a b T : Expr Nat} (h : CovWConvReduction E n Γ a b T) :
      CovWConvReductionStar E n Γ a b T
  | trans {a b c T : Expr Nat}
      (h₁ : CovWConvReductionStar E n Γ a b T)
      (h₂ : CovWConvReductionStar E n Γ b c T) :
      CovWConvReductionStar E n Γ a c T

theorem covWConv_reductionStar_sound {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CovWConvReductionStar E n Γ a b T) :
    Nonempty (ConvT E n Γ a b T) := by
  induction h with
  | refl ha =>
      exact ⟨.refl Γ _ _ ha⟩
  | single h =>
      exact covWConv_reduction_sound h
  | trans h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨c₁⟩
      rcases ih₂ with ⟨c₂⟩
      exact ⟨.trans Γ _ _ _ _ c₁ c₂⟩

theorem covWConv_reductionStar_native {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CovWConvReductionStar E n Γ a b T) :
    CovWConvCK2Star E n Γ a b := by
  induction h with
  | refl ha =>
      exact .refl _
  | single h =>
      exact .single (covWConv_reduction_native h)
  | trans h₁ h₂ ih₁ ih₂ =>
      exact .trans ih₁ ih₂

/-! A separately named extension adds eta and closes its head/major positions.
Its interpretation below is typed conversion.  The native projection above
applies to `CovWConvReduction`, whose rules are all actual CK2 steps. -/

inductive CovWConvEtaReduction (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Expr Nat → Prop where
  | ck2 {a b T : Expr Nat} (h : CovWConvReduction E n Γ a b T) :
      CovWConvEtaReduction E n Γ a b T
  | eta (f A B : Expr Nat) (hf : HasTyT E n Γ f (.pi A B)) :
      CovWConvEtaReduction E n Γ
        (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B)
  | appHead {f g a A B : Expr Nat}
      (h : CovWConvEtaReduction E n Γ f g (.pi A B))
      (ha : HasTyT E n Γ a A) :
      CovWConvEtaReduction E n Γ (.app f a) (.app g a) (instantiate0 a B)
  | recMajor {r : Nat} {m : CheckedMember} {ls : List Level}
      {pre : List (Expr Nat)} {x x' A B : Expr Nat}
      (hprefix : HasTyT E n Γ (foldApps (.const r ls) pre) (.pi A B))
      (hm : E.members r = some m)
      (hrec : m.mclass = .recursorM)
      (hlen : pre.length + 1 = piCount m.mtype)
      (hnK : ¬ KFreeRec E r)
      (hnP : ¬ KProjRec E r)
      (h : CovWConvEtaReduction E n Γ x x' A) :
      CovWConvEtaReduction E n Γ
        (recCall (.const r ls) pre x)
        (recCall (.const r ls) pre x') (instantiate0 x B)
  | retype {a b A B : Expr Nat}
      (h : CovWConvEtaReduction E n Γ a b A)
      (hc : TyConvT E n Γ A B) :
      CovWConvEtaReduction E n Γ a b B

theorem covWConv_etaReduction_sound {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CovWConvEtaReduction E n Γ a b T) :
    Nonempty (ConvT E n Γ a b T) := by
  induction h with
  | ck2 h =>
      exact covWConv_reduction_sound h
  | eta f A B hf =>
      exact ⟨.eta Γ f A B hf⟩
  | appHead h ha ih =>
      rcases ih with ⟨cfun⟩
      exact ⟨.app Γ _ _ _ _ _ _ cfun (.refl Γ _ _ ha)⟩
  | recMajor hprefix hm hrec hlen hnK hnP h ih =>
      rcases ih with ⟨cmajor⟩
      simpa only [recCall_eq_app] using
        (show Nonempty (ConvT E n Γ _ _ _) from ⟨.app Γ _ _ _ _ _ _ (.refl Γ _ _ hprefix) cmajor⟩)
  | retype h hc ih =>
      rcases ih with ⟨c⟩
      exact ⟨convT_of_tyConv c hc⟩

inductive CovWConvEtaReductionStar (E : ResolvedEnv) (n : Nat) (Γ : LCtx) :
    Expr Nat → Expr Nat → Expr Nat → Prop where
  | refl {a T : Expr Nat} (ha : HasTyT E n Γ a T) :
      CovWConvEtaReductionStar E n Γ a a T
  | single {a b T : Expr Nat} (h : CovWConvEtaReduction E n Γ a b T) :
      CovWConvEtaReductionStar E n Γ a b T
  | trans {a b c T : Expr Nat}
      (h₁ : CovWConvEtaReductionStar E n Γ a b T)
      (h₂ : CovWConvEtaReductionStar E n Γ b c T) :
      CovWConvEtaReductionStar E n Γ a c T

theorem covWConv_etaReductionStar_sound {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CovWConvEtaReductionStar E n Γ a b T) :
    Nonempty (ConvT E n Γ a b T) := by
  induction h with
  | refl ha =>
      exact ⟨.refl Γ _ _ ha⟩
  | single h =>
      exact covWConv_etaReduction_sound h
  | trans h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨c₁⟩
      rcases ih₂ with ⟨c₂⟩
      exact ⟨.trans Γ _ _ _ _ c₁ c₂⟩

#print axioms covWConv_reduction_sound
#print axioms covWConv_reduction_native
#print axioms covWConv_reductionStar_sound
#print axioms covWConv_reductionStar_native
#print axioms covWConv_etaReduction_sound
#print axioms covWConv_etaReductionStar_sound

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
