import rcic.RcicAnnKTransport

/-!
# The stage-1 K reduct is determined by the call

This is determinism of K alone. It does not assert compatibility with the
old evaluator's step in a reducible major. The singleton layout fixes the
constructor reference, and the parameter count fixes the minor's spine slot.
No conversion decision or logical-relation assumption is used.
closure_claim = 0.
-/

namespace Rcic.Declarative.Ann.KStage

set_option autoImplicit false
set_option maxRecDepth 8192

/-- A singleton stored layout has its only constructor immediately before
the recursor. This does not require choosing a constructor. -/
theorem Target.ctorNext {E : ResolvedEnvA} {s : Shape} (w : Target E s) :
    s.ctorRef + 1 = s.recRef := by
  obtain ⟨_, _, _, _, _, _, _, hfc, hcr, hnm, _⟩ := iotaGroupA_some w.group
  have hone := w.oneConstructor
  omega

/-- Equal complete calls have the same recursor reference. -/
theorem Shape.recRef_eq_of_source_eq {s t : Shape} (h : s.source = t.source) :
    s.recRef = t.recRef := by
  have hh := congrArg (fun e => (appsSpineA e).1) h
  simp only [Shape.source, Shape.prefix, appsSpineA, appsSpineA_foldAppsA] at hh
  exact (ExprA.const.inj hh).1

/-- At a fixed K target the minor is the parameter-count-plus-one argument. -/
theorem Target.minorSlot {E : ResolvedEnvA} {s : Shape} (w : Target E s) :
    ((appsSpineA s.source).2.drop (s.group.nparams + 1)).head? = some s.minor := by
  simp only [Shape.source, Shape.prefix, appsSpineA, appsSpineA_foldAppsA]
  rw [← w.paramCount]
  simp [Shape.pre, List.append_assoc, List.drop_append]

/-- The actual K reduct is a function of the source syntax and environment,
even when the frames contain different typing or conversion derivations. -/
theorem Target.minor_eq_of_source_eq {E : ResolvedEnvA} {s t : Shape}
    (hs : Target E s) (ht : Target E t) (h : s.source = t.source) :
    s.minor = t.minor := by
  have hr := Shape.recRef_eq_of_source_eq h
  have hc : s.ctorRef = t.ctorRef := by
    have hsc := hs.ctorNext
    have htc := ht.ctorNext
    omega
  have hg : s.group = t.group := by
    have hsg := hs.group
    rw [hr, hc, ht.group] at hsg
    exact (Option.some.inj hsg).symm
  have hp : s.group.nparams = t.group.nparams := congrArg IotaGroupA.nparams hg
  have hm := hs.minorSlot
  rw [h, hp, ht.minorSlot] at hm
  exact (Option.some.inj hm).symm

/-- Frame-level K determinism; the result types may be indexed differently. -/
theorem Frame.minor_eq_of_source_eq {E : ResolvedEnvA} {I : IotaIfaceA}
    {n : Nat} {Γ : LCtxA} {s t : Shape}
    (hs : Frame E I n Γ s) (ht : Frame E I n Γ t)
    (h : s.source = t.source) : s.minor = t.minor :=
  hs.target.minor_eq_of_source_eq ht.target h

#print axioms Target.ctorNext
#print axioms Shape.recRef_eq_of_source_eq
#print axioms Target.minorSlot
#print axioms Target.minor_eq_of_source_eq
#print axioms Frame.minor_eq_of_source_eq

end Rcic.Declarative.Ann.KStage
