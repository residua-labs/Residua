import rcic.RcicIotaFunRecCorr

/-!
# R-NoFunRec S6 — reduct-gated frec union faces

`iotaErasesTUA_frec`/`iotaCorrTUA_frec` (landed, batch 251) ask for
`FrecFiringGates` at *every* spine/head/group triple — including triples
where `iotaReductA` fails.  The variants here ask only at *actual reduct
firings*: `hgate` additionally receives the reduct `e'` and
`hr : iotaReductA s g = some e'`, so the gate discharge may read the
successful firing's data (the Acc/W rows need the major-arity fact that
`iotaReductA` pins).  Statements are new names — the landed ones are
untouched.
-/

namespace Rcic.Declarative.Ann

/-- The step-indexed `IotaErasesTUA` face of the union ι-correspondence past
    `EnvNoFunA`, gated at actual reduct firings only: `hgate` sees the
    successful `iotaReductA s g = some e'`. -/
theorem iotaErasesTUA_frecR {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfA I EA) (hn : EnvNormEraseA EA) (hT : EnvWfT (eraseEnv EA))
    (fuel : Nat)
    (hgate : ∀ (e e' : ExprA) (s : RecSpineA) (c : Nat) (g : IotaGroupA),
      recSpineA e = some s → spineHeadRefA s.major = some c →
      iotaGroupA EA s.recRef c = some g → iotaReductA s g = some e' →
      FrecFiringGates EA fuel s g) :
    IotaErasesTUA EA := by
  intro e e' h
  obtain ⟨s, c, g, hs, hc, hg, hr⟩ := iotaFnA_some h
  obtain ⟨hfrag, hsup, hstab, hscope⟩ := hgate e e' s c g hs hc hg hr
  exact derivedIotaUS_of_iotaFnA_frec hW hn hT hs hc hg hr fuel
    hfrag hsup hstab hscope

/-- The full union ι-correspondence on a frec-gated environment, reduct-gated:
    `ann` is the `EnvNoFunA`-free direction unchanged, `eraseT` goes through
    the reduct-gated `.ofUS` arm. -/
theorem iotaCorrTUA_frecR {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hn : EnvNormEraseA EA) (hT : EnvWfT (eraseEnv EA)) (fuel : Nat)
    (hCe : EnvCorrEraseCert (eraseEnv EA)) (hCa : EnvCorrAnnCert (eraseEnv EA))
    (hgate : ∀ (e e' : ExprA) (s : RecSpineA) (c : Nat) (g : IotaGroupA),
      recSpineA e = some s → spineHeadRefA s.major = some c →
      iotaGroupA EA s.recRef c = some g → iotaReductA s g = some e' →
      FrecFiringGates EA fuel s g) :
    IotaCorrTUA EA where
  ann := iotaAnnotatesUA_of_envWfA hW hn hCe hCa
  eraseT := iotaErasesTUA_frecR hW hn hT fuel hgate

#print axioms iotaErasesTUA_frecR
#print axioms iotaCorrTUA_frecR

end Rcic.Declarative.Ann
