import rcic.RcicOccurrenceFrames
import rcic.RcicOriginSubst
import rcic.RcicPEqTSubst

/-!
Certificates on unchanged producers, not new ParRedT rules or a global J.
Variable-head instantiation exposes the whole argument PEqT. Its output identity
transports all occurrence requests and answers. For common-Prop arguments the
actual output-position index is read from the ORIGINAL bvar typing inversion;
no arbitrary request map, generated U call, or numeric descent is assumed.
General structural exposure and X remain open. closure_claim=0.
-/

namespace Rcic.Declarative.F8ProducerPosition
variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A N N' T : Expr Nat}

/-- Exact output identity for the existing producer: the removed bound variable
exposes the entire argument comparison, including every nested proof root. -/
theorem instantiate0_bvar_exact (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n (.assumption A :: Γ))
    (hn : HasTyT E n Γ N A) (hn' : HasTyT E n Γ N' A)
    (hc : ConvT E n Γ N N' A)
    (ht : HasTyT E n (.assumption A :: Γ) (.bvar 0) T)
    (hp : PEqT E n Γ N N') :
    PEqT.instantiate0 hcl hinst hΓ hn hn' hc ht (.bvar _ 0) hp = hp := by
  simp [PEqT.instantiate0,
    PEqT.instantiate_pair, peqT_substRemove_weaken]

/-- Read the REAL host index from the original variable typing's inversion
chain, then transport it once. No U call and no chosen easy request index. -/
def bvar_result_chain (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hn : HasTyT E n Γ N A)
    (ht : HasTyT E n (.assumption A :: Γ) (.bvar 0) T) :
    TyConvT E n Γ A (instantiate0 N T) := by
  obtain ⟨B, hlookup, hchain⟩ := hasTyTInv_bvar ht rfl
  have hB : B = lift 0 1 A := by
    have hh : some (lift 0 1 A) = some B := hlookup
    exact (Option.some.inj hh).symm
  subst B
  have out := F8OriginSubst.substChain0 hcl hinst hn hchain
  simpa only [instantiate0, instantiate_lift_id] using out

open F8Occurrences

/-- Equality transport changes no position choice. -/
def rawRequests_transport {a b : Expr Nat} {h k : PEqT E n Γ a b}
    (e : h = k) (r : RawRequests h) : RawRequests k := e ▸ r

def rawAnswers_transport {a b : Expr Nat} {h k : PEqT E n Γ a b}
    (e : h = k) (r : RawRequests h) (ans : RawAnswered h r) :
    RawAnswered k (rawRequests_transport e r) := by
  cases e
  exact ans

def rawOcc_transport {a b : Expr Nat} {h k : PEqT E n Γ a b}
    (e : h = k) (o : RawOcc h) : RawOcc k := e ▸ o

theorem rawAnswer_transport_exact {a b : Expr Nat} {h k : PEqT E n Γ a b}
    (e : h = k) (r : RawRequests h) (ans : RawAnswered h r)
    (o : RawOcc h) (side : Side) :
    HEq (rawAnswers_transport e r ans (rawOcc_transport e o) side) (ans o side) := by
  cases e
  rfl

/-- Every root in the ACTUAL variable-exposure output comes from the argument
comparison; this transports a whole store, not one existentially selected root. -/
def exposedRequests (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n (.assumption A :: Γ))
    (hn : HasTyT E n Γ N A) (hn' : HasTyT E n Γ N' A)
    (hc : ConvT E n Γ N N' A)
    (ht : HasTyT E n (.assumption A :: Γ) (.bvar 0) T)
    (hp : PEqT E n Γ N N') (r : RawRequests hp) :
    RawRequests (PEqT.instantiate0 hcl hinst hΓ hn hn' hc ht (.bvar _ 0) hp) :=
  rawRequests_transport (instantiate0_bvar_exact hcl hinst hΓ hn hn' hc ht hp).symm r

def exposedAnswers (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n (.assumption A :: Γ))
    (hn : HasTyT E n Γ N A) (hn' : HasTyT E n Γ N' A)
    (hc : ConvT E n Γ N N' A)
    (ht : HasTyT E n (.assumption A :: Γ) (.bvar 0) T)
    (hp : PEqT E n Γ N N') (r : RawRequests hp) (ans : RawAnswered hp r) :
    RawAnswered (PEqT.instantiate0 hcl hinst hΓ hn hn' hc ht (.bvar _ 0) hp)
      (exposedRequests hcl hinst hΓ hn hn' hc ht hp r) :=
  rawAnswers_transport (instantiate0_bvar_exact hcl hinst hΓ hn hn' hc ht hp).symm r ans

/-- Actual variable-result index, recovered from the consumer's original typing.
Both argument typings are transported from A to T[N]. Nothing normalizes T[N]. -/
def bvarArgumentRequests (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hA : HasTyT E n Γ A (.sort .zero))
    (hn : HasTyT E n Γ N A) (hn' : HasTyT E n Γ N' A)
    (ht : HasTyT E n (.assumption A :: Γ) (.bvar 0) T) :
    RawRequests (.proof Γ N N' A A hA hA hn hn')
  | _, .left => ⟨instantiate0 N T, hasTyT_of_tyConvT hn (bvar_result_chain hcl hinst hn ht)⟩
  | _, .right => ⟨instantiate0 N T, hasTyT_of_tyConvT hn' (bvar_result_chain hcl hinst hn ht)⟩

def bvarArgumentAnswers (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hA : HasTyT E n Γ A (.sort .zero))
    (hn : HasTyT E n Γ N A) (hn' : HasTyT E n Γ N' A)
    (ht : HasTyT E n (.assumption A :: Γ) (.bvar 0) T) :
    RawAnswered (.proof Γ N N' A A hA hA hn hn')
      (bvarArgumentRequests hcl hinst hA hn hn' ht)
  | _, .left => (bvar_result_chain hcl hinst hn ht).symmT
  | _, .right => (bvar_result_chain hcl hinst hn ht).symmT

/-- The map is fixed by the actual consumer typing ht, never supplied as an
arbitrary Requests parameter. It is indexed by the original producer's output. -/
def bvarHostRequests (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n (.assumption A :: Γ))
    (hA : HasTyT E n Γ A (.sort .zero))
    (hn : HasTyT E n Γ N A) (hn' : HasTyT E n Γ N' A)
    (hc : ConvT E n Γ N N' A)
    (ht : HasTyT E n (.assumption A :: Γ) (.bvar 0) T) :
    RawRequests (PEqT.instantiate0 hcl hinst hΓ hn hn' hc ht (.bvar _ 0)
      (.proof Γ N N' A A hA hA hn hn')) :=
  exposedRequests hcl hinst hΓ hn hn' hc ht (.proof Γ N N' A A hA hA hn hn')
    (bvarArgumentRequests hcl hinst hA hn hn' ht)

def bvarHostAnswers (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n (.assumption A :: Γ))
    (hA : HasTyT E n Γ A (.sort .zero))
    (hn : HasTyT E n Γ N A) (hn' : HasTyT E n Γ N' A)
    (hc : ConvT E n Γ N N' A)
    (ht : HasTyT E n (.assumption A :: Γ) (.bvar 0) T) :
    RawAnswered (PEqT.instantiate0 hcl hinst hΓ hn hn' hc ht (.bvar _ 0)
      (.proof Γ N N' A A hA hA hn hn'))
      (bvarHostRequests hcl hinst hΓ hA hn hn' hc ht) :=
  exposedAnswers hcl hinst hΓ hn hn' hc ht (.proof Γ N N' A A hA hA hn hn')
    (bvarArgumentRequests hcl hinst hA hn hn' ht)
    (bvarArgumentAnswers hcl hinst hA hn hn' ht)

theorem rawRequest_transport_index {a b : Expr Nat} {h k : PEqT E n Γ a b}
    (e : h = k) (r : RawRequests h) (o : RawOcc h) (side : Side) :
    (rawRequests_transport e r (rawOcc_transport e o) side).index = (r o side).index := by
  cases e
  rfl

theorem exposure_count (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (hΓ : CtxWfT E n (.assumption A :: Γ))
    (hn : HasTyT E n Γ N A) (hn' : HasTyT E n Γ N' A)
    (hc : ConvT E n Γ N N' A)
    (ht : HasTyT E n (.assumption A :: Γ) (.bvar 0) T)
    (hp : PEqT E n Γ N N') :
    (rawOccurrences (PEqT.instantiate0 hcl hinst hΓ hn hn' hc ht (.bvar _ 0) hp)).length =
      (rawOccurrences hp).length :=
  congrArg (fun d => (rawOccurrences d).length)
    (instantiate0_bvar_exact hcl hinst hΓ hn hn' hc ht hp)

end Rcic.Declarative.F8ProducerPosition
