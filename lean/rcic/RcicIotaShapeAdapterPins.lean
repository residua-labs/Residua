import rcic.RcicIotaShapeAdapter
import rcic.RcicFixtures
import rcic.RcicTypedDeltaRecPins

namespace Rcic.Declarative

/-! # R-NoFunRec-1 B2 step 2b-2 — adapter pins

Positive pins: the Nat / List / Vec legacy `IotaWitness` fixtures
satisfy `iotaWitnessSB` and adapt to `IotaWitnessS`, with the typed
lhs/rhs equal to the legacy redex lhs/rhs verbatim.

Negative pins: insufficient fuel is refused honestly.

Counterexample pin: the δ-reached `Id F` field of
`RcicTypedDeltaRecPins` is where the two analysers GENUINELY diverge —
admission's `fieldAnalyze` permits `.recursive 0` (it reaches `F`
through `Id`'s transparent body), while the legacy `analyzeField`
returns `none` (its scan is purely syntactic).  No `IotaWitness` can
exist over `drFamEnv` for `mk`, so there is nothing to adapt; the
fragment's `rigid` conjunct (`noTransparentB`) is exactly what fences
the divergence out of `iotaWitnessSB`.  Reported, not patched.

Note on proofs: `iotaWitnessSB` computes correctly under `#eval`, but
its `iotaWitnessStableB` conjunct runs `constsMemberFuel`, whose
compiled recursion is opaque at plain `rfl`/`decide`.  The pins
therefore unfold the recognizer with `simp` on the fixture's
environment and stored types — the same pattern
`RcicIotaShapeStablePins.drField_constsMemberFuel` uses. -/

set_option maxRecDepth 4000

/-- The recognizer's unfold set, shared by every fixture pin. -/
macro "adapter_simp" : tactic =>
  `(tactic| simp [iotaWitnessSB, directFragCheck, directFragOne,
    iotaWitnessStableB,
    constsMemberFuel, iotaSchemaS, iotaOpenRhs, iotaArgs,
    natEnv, natEnvPrefix, listEnv, listEnvPrefix, vecEnv, vecEnvPrefix,
    vecEnvDecoy, vecEnvPrefixDecoy, emptyEnv, extendEnv,
    natFamMember, natZeroMember, natSuccMember, natRecMember,
    listFamMember, listNilMember, listConsMember, listRecMember,
    vecFamMember, vecNilMember, vecConsMember, vecRecMember,
    vecConsDecoyMember,
    transparent, instantiateLevels, fieldBvars, ctorFieldTelRaw, lift,
    piTelescopeFuel, whnfFuel, transparentBody, noTransparentB, headStableB,
    piTailOf, esize, piCount, properShapeB, isFamilyApp, instPrefix,
    exprClosedAt, iotaRhsOf, rhsArgs, ctorSpine, ctorMajor, recCall, foldApps,
    recCallField, recPrefix, familyIdx, exactParamLocals, appsSpine,
    occursConst, piDomsOf, instantiate, instantiate0, instLevel,
    canonRecLevels, preMajorBvars, minorTel,
    wSucc, wZero, wNil, wCons, wVcons, wVconsDecoy,
    natMotive, natMinorZ, natMinorS, natField,
    listParam, listMotive, listMinorN, listMinorC, listHead, listTail,
    listRecDoms, listPreMajor,
    vecParam, vecMotiveArg, vecMinorN, vecMinorC, vecFieldN, vecFieldHd,
    vecFieldTl, vecMajorIdx, vecRecDoms, vecConsDecoyAfterParams])

/-! ### Nat -/

/-- The Nat successor witness satisfies the DIRECT recognizer at
fuel 8. -/
theorem pin_iotaWitnessSB_wSucc : iotaWitnessSB wSucc 8 = true := by
  adapter_simp

/-- The adapted Nat successor witness. -/
def wSuccS : IotaWitnessS natEnv :=
  iotaWitnessSOf wSucc 8 pin_iotaWitnessSB_wSucc

/-- Adaptation preserves the ι left-hand side. -/
theorem pin_wSuccS_lhs : iotaLhsOfS wSuccS = iotaLhsOf wSucc :=
  iotaLhsOfS_iotaWitnessSOf wSucc 8 pin_iotaWitnessSB_wSucc

/-- Adaptation preserves the ι right-hand side — the checked equality
`instPrefix (preMajor ++ fields) (instantiateLevels ls schema) =
iotaRhsOf wSucc` exhibited. -/
theorem pin_wSuccS_rhs : iotaRhsOfS wSuccS = iotaRhsOf wSucc :=
  iotaRhsOfS_iotaWitnessSOf wSucc 8 pin_iotaWitnessSB_wSucc

/-- The typed shapes are `shapeOfKind` of the legacy kinds:
`directRec ↦ recursive 0`. -/
theorem pin_wSuccS_shapes : wSuccS.shapes = [.recursive 0] := rfl

/-- `fieldShapesFuel` on the successor's field telescope agrees. -/
theorem pin_wSuccS_fieldShapes :
    fieldShapesFuel natEnv 8 0 0 0 0 0
      (wSucc.ctorDoms.drop 0) = some [.recursive 0] := rfl

/-- The `iotaArgs`/`rhsArgs` correspondence, exhibited on `wSucc`. -/
theorem pin_wSuccS_iotaArgs :
    ∃ sargs,
      iotaArgs natEnv 8
          (.const wSucc.recRef (canonRecLevels wSucc.recMember.arity))
          (preMajorBvars wSucc.nparams wSucc.nMinors wSucc.nindices
            wSucc.fields.length)
          wSucc.nparams wSucc.nMinors (wSucc.kinds.map shapeOfKind)
          (fieldBvars wSucc.fields.length)
          (lift 0 (wSucc.fields.length + 1 + wSucc.nMinors + wSucc.nindices)
            (ctorFieldTelRaw wSucc.nparams wSucc.ctorDoms wSucc.ctorResult)) =
        some sargs ∧
      sargs.map (fun a => instPrefix (wSucc.preMajor ++ wSucc.fields)
            (instantiateLevels wSucc.ls a)) =
        rhsArgs (.const wSucc.recRef wSucc.ls) wSucc.preMajor
          wSucc.nparams wSucc.nMinors wSucc.fields wSucc.kinds
          wSucc.ctorAfterParams :=
  iotaArgs_rhsArgs_of_iotaWitnessSB wSucc 8 pin_iotaWitnessSB_wSucc

/-- Nat zero (no fields): the empty-telescope case adapts too. -/
theorem pin_iotaWitnessSB_wZero : iotaWitnessSB wZero 64 = true := by
  adapter_simp

/-- The adapted Nat zero witness. -/
def wZeroS : IotaWitnessS natEnv :=
  iotaWitnessSOf wZero 64 pin_iotaWitnessSB_wZero

theorem pin_wZeroS_rhs : iotaRhsOfS wZeroS = iotaRhsOf wZero :=
  iotaRhsOfS_iotaWitnessSOf wZero 64 pin_iotaWitnessSB_wZero

/-! ### List -/

/-- List nil. -/
theorem pin_iotaWitnessSB_wNil : iotaWitnessSB wNil 64 = true := by
  adapter_simp

/-- The adapted List nil witness. -/
def wNilS : IotaWitnessS listEnv :=
  iotaWitnessSOf wNil 64 pin_iotaWitnessSB_wNil

theorem pin_wNilS_rhs : iotaRhsOfS wNilS = iotaRhsOf wNil :=
  iotaRhsOfS_iotaWitnessSOf wNil 64 pin_iotaWitnessSB_wNil

/-- List cons: `hd` plain, `tl` directly recursive. -/
theorem pin_iotaWitnessSB_wCons : iotaWitnessSB wCons 64 = true := by
  adapter_simp

/-- The adapted List cons witness. -/
def wConsS : IotaWitnessS listEnv :=
  iotaWitnessSOf wCons 64 pin_iotaWitnessSB_wCons

theorem pin_wConsS_lhs : iotaLhsOfS wConsS = iotaLhsOf wCons :=
  iotaLhsOfS_iotaWitnessSOf wCons 64 pin_iotaWitnessSB_wCons

theorem pin_wConsS_rhs : iotaRhsOfS wConsS = iotaRhsOf wCons :=
  iotaRhsOfS_iotaWitnessSOf wCons 64 pin_iotaWitnessSB_wCons

theorem pin_wConsS_shapes :
    wConsS.shapes = [.nonrecursive, .recursive 0] := rfl

/-! ### Vec (indexed) -/

/-- Vec vcons: `n`, `hd` plain, `tl : Vec α n` directly recursive with
the canonical index — the correspondence goes through the indexed
`familyIdx`/`idxClean` path. -/
theorem pin_iotaWitnessSB_wVcons : iotaWitnessSB wVcons 64 = true := by
  adapter_simp

/-- The adapted Vec vcons witness. -/
def wVconsS : IotaWitnessS vecEnv :=
  iotaWitnessSOf wVcons 64 pin_iotaWitnessSB_wVcons

theorem pin_wVconsS_lhs : iotaLhsOfS wVconsS = iotaLhsOf wVcons :=
  iotaLhsOfS_iotaWitnessSOf wVcons 64 pin_iotaWitnessSB_wVcons

theorem pin_wVconsS_rhs : iotaRhsOfS wVconsS = iotaRhsOf wVcons :=
  iotaRhsOfS_iotaWitnessSOf wVcons 64 pin_iotaWitnessSB_wVcons

theorem pin_wVconsS_shapes :
    wVconsS.shapes = [.nonrecursive, .nonrecursive, .recursive 0] :=
  rfl

/-- The stored domains classify identically through both analysers. -/
theorem pin_wVconsS_fieldShapes :
    fieldShapesFuel vecEnv 64 4 0 1 1 1
      (wVcons.ctorDoms.drop 1) =
        some [.nonrecursive, .nonrecursive, .recursive 0] := rfl

/-- The decoy environment's legal witness also adapts: the decoy moved
the constructor's `hd` domain, which is orthogonal to the schema/RHS
identity the recognizer checks.  (Its `IotaTyping` refutation —
`pin_vec_decoy_iotaTyping_refuted` — is a separate, stronger claim;
the adapter produces a typed WITNESS, not a typing derivation.) -/
theorem pin_iotaWitnessSB_wVconsDecoy :
    iotaWitnessSB wVconsDecoy 64 = true := by
  adapter_simp

/-- The adapted decoy witness. -/
def wVconsDecoyS : IotaWitnessS vecEnvDecoy :=
  iotaWitnessSOf wVconsDecoy 64 pin_iotaWitnessSB_wVconsDecoy

theorem pin_wVconsDecoyS_rhs :
    iotaRhsOfS wVconsDecoyS = iotaRhsOf wVconsDecoy :=
  iotaRhsOfS_iotaWitnessSOf wVconsDecoy 64 pin_iotaWitnessSB_wVconsDecoy

/-! ### Negatives — refused honestly -/

/-- Zero fuel: the schema computation cannot run, the fragment's fuel
bound fails — refused. -/
theorem pin_iotaWitnessSB_wSucc_zero_fuel :
    iotaWitnessSB wSucc 0 = false := by
  adapter_simp

theorem pin_iotaWitnessSB_wVcons_zero_fuel :
    iotaWitnessSB wVcons 0 = false := by
  adapter_simp

/-! ### Counterexample — the δ-reached `Id F` field

`drField = Id F` is a field of `drMkMember`'s constructor over
`drFamEnv`.  Admission's analyser permits it as `.recursive 0`
(`dr_fieldAnalyze`): `containsFamilyFuel` reaches `F` through `Id`'s
transparent `definitionM` body.  The legacy `analyzeField` returns
`none`: `occursConst` sees `F` syntactically inside the application
but `isFamilyApp` fails — the spine head is `Id`, not `F`.

So `hkinds` can never hold for a `mk` witness over `drFamEnv`: the
legacy carrier cannot even be formed, while the typed analyser has a
definite answer.  This is an ACTUAL divergence of the two scans, and
`DirectFieldFrag.rigid` (`noTransparentB`) is exactly the conjunct
that excludes it — the correspondence theorems do not apply, and the
check below confirms the fence is load-bearing. -/

/-- The legacy analysis returns `none` on `Id F`. -/
theorem pin_dr_analyzeField_none :
    (analyzeField 1 drField).isSome = false := rfl

/-- Admission's analysis permits `Id F` as `.recursive 0` —
established as `dr_fieldAnalyze` upstream; repeated here so the
divergence is stated in one place. -/
theorem pin_dr_fieldAnalyze_permitted :
    fieldAnalyze drFamEnv 8 1 0 0 0 0 drField =
      .permitted (.recursive 0) [] := dr_fieldAnalyze

/-- The fragment's `rigid` conjunct excludes the δ-reached field:
`Id` has a transparent `definitionM` body, so `noTransparentB` is
`false` and no `DirectFieldFrag` for `drField` can be constructed. -/
theorem pin_dr_noTransparentB_false :
    noTransparentB drFamEnv drField = false := rfl

/-! ### The redex-level recognizer

`iotaRedexB E fuel lhs rhs` runs on EXPRESSIONS: `iotaReductCert`
rebuilds the legacy witness from the redex spine, `iotaWitnessSB`
certifies it in the DIRECT fragment, and the typed rhs — the schema
instantiated at the redex's `preMajor ++ fields` — is compared to
`rhs`.  The reconstruction pins
`iotaReductCert env (iotaLhsOf w) = some ⟨w, rfl⟩` hold
definitionally: the certificate recovers each fixture witness
field-for-field, so every recognizer pin is a short rewrite through
the adapted-witness pins above.  This is the computation path step
2c uses to obtain `IotaWitnessS` directly from a redex. -/

/-- `iotaReductCert` reconstructs `wSucc` itself from its redex. -/
theorem pin_iotaReductCert_succ_eq :
    iotaReductCert natEnv (iotaLhsOf wSucc) = some ⟨wSucc, rfl⟩ := rfl

theorem pin_iotaReductCert_zero_eq :
    iotaReductCert natEnv (iotaLhsOf wZero) = some ⟨wZero, rfl⟩ := rfl

theorem pin_iotaReductCert_cons_eq :
    iotaReductCert listEnv (iotaLhsOf wCons) = some ⟨wCons, rfl⟩ := rfl

theorem pin_iotaReductCert_nil_eq :
    iotaReductCert listEnv (iotaLhsOf wNil) = some ⟨wNil, rfl⟩ := rfl

theorem pin_iotaReductCert_vcons_eq :
    iotaReductCert vecEnv (iotaLhsOf wVcons) = some ⟨wVcons, rfl⟩ :=
  rfl

theorem pin_iotaReductCert_vconsDecoy_eq :
    iotaReductCert vecEnvDecoy (iotaLhsOf wVconsDecoy) =
      some ⟨wVconsDecoy, rfl⟩ := rfl

/-- The recognizer fires on the successor redex — the full pipeline
(spine reconstruction, DIRECT fragment check, schema instantiation,
rhs comparison) succeeds. -/
theorem pin_iotaRedexB_succ :
    iotaRedexB natEnv 8 (iotaLhsOf wSucc) (iotaRhsOf wSucc) = true := by
  unfold iotaRedexB iotaReductShapeCert
  rw [pin_iotaReductCert_succ_eq]
  dsimp only
  rw [dif_pos pin_iotaWitnessSB_wSucc]
  dsimp only
  rw [iotaRhsOfS_iotaWitnessSOf]
  rfl

theorem pin_iotaRedexB_zero :
    iotaRedexB natEnv 64 (iotaLhsOf wZero) (iotaRhsOf wZero) = true := by
  unfold iotaRedexB iotaReductShapeCert
  rw [pin_iotaReductCert_zero_eq]
  dsimp only
  rw [dif_pos pin_iotaWitnessSB_wZero]
  dsimp only
  rw [iotaRhsOfS_iotaWitnessSOf]
  rfl

theorem pin_iotaRedexB_cons :
    iotaRedexB listEnv 64 (iotaLhsOf wCons) (iotaRhsOf wCons) = true := by
  unfold iotaRedexB iotaReductShapeCert
  rw [pin_iotaReductCert_cons_eq]
  dsimp only
  rw [dif_pos pin_iotaWitnessSB_wCons]
  dsimp only
  rw [iotaRhsOfS_iotaWitnessSOf]
  rfl

theorem pin_iotaRedexB_nil :
    iotaRedexB listEnv 64 (iotaLhsOf wNil) (iotaRhsOf wNil) = true := by
  unfold iotaRedexB iotaReductShapeCert
  rw [pin_iotaReductCert_nil_eq]
  dsimp only
  rw [dif_pos pin_iotaWitnessSB_wNil]
  dsimp only
  rw [iotaRhsOfS_iotaWitnessSOf]
  rfl

/-- The indexed `Vec` case goes through the recognizer too. -/
theorem pin_iotaRedexB_vcons :
    iotaRedexB vecEnv 64 (iotaLhsOf wVcons) (iotaRhsOf wVcons) = true := by
  unfold iotaRedexB iotaReductShapeCert
  rw [pin_iotaReductCert_vcons_eq]
  dsimp only
  rw [dif_pos pin_iotaWitnessSB_wVcons]
  dsimp only
  rw [iotaRhsOfS_iotaWitnessSOf]
  rfl

/-- The decoy environment's redex also recognizes. -/
theorem pin_iotaRedexB_vconsDecoy :
    iotaRedexB vecEnvDecoy 64 (iotaLhsOf wVconsDecoy)
      (iotaRhsOf wVconsDecoy) = true := by
  unfold iotaRedexB iotaReductShapeCert
  rw [pin_iotaReductCert_vconsDecoy_eq]
  dsimp only
  rw [dif_pos pin_iotaWitnessSB_wVconsDecoy]
  dsimp only
  rw [iotaRhsOfS_iotaWitnessSOf]
  rfl

/-- The typed certificate produces an `IotaWitnessS` for the
successor redex. -/
theorem pin_iotaReductShapeCert_succ :
    (iotaReductShapeCert natEnv 8 (iotaLhsOf wSucc)).isSome = true := by
  unfold iotaReductShapeCert
  rw [pin_iotaReductCert_succ_eq]
  dsimp only
  rw [dif_pos pin_iotaWitnessSB_wSucc]
  rfl

/-- The certificate's VALUE on the successor redex is the adapted
`wSucc` with its lhs proof. -/
theorem pin_iotaReductShapeCert_succ_val :
    iotaReductShapeCert natEnv 8 (iotaLhsOf wSucc) =
      some ⟨wSuccS, pin_wSuccS_lhs⟩ := by
  unfold iotaReductShapeCert
  rw [pin_iotaReductCert_succ_eq]
  dsimp only
  rw [dif_pos pin_iotaWitnessSB_wSucc]
  rfl

/-- The certified witness's typed rhs is the legacy reduct. -/
theorem pin_iotaReductShapeCert_succ_rhs :
    ∃ p, iotaReductShapeCert natEnv 8 (iotaLhsOf wSucc) = some p ∧
      iotaRhsOfS p.1 = iotaRhsOf wSucc :=
  ⟨_, pin_iotaReductShapeCert_succ_val, pin_wSuccS_rhs⟩

/-! ### Recognizer negatives — refused honestly -/

/-- Wrong rhs: the recognizer compares the instantiated schema to
`rhs` — `natMinorZ` is not the reduct of the successor redex. -/
theorem pin_iotaRedexB_succ_wrong_rhs :
    iotaRedexB natEnv 8 (iotaLhsOf wSucc) natMinorZ = false := by
  unfold iotaRedexB iotaReductShapeCert
  rw [pin_iotaReductCert_succ_eq]
  dsimp only
  rw [dif_pos pin_iotaWitnessSB_wSucc]
  dsimp only
  rw [iotaRhsOfS_iotaWitnessSOf]
  rfl

/-- Non-redex lhs: `natMinorZ` is not a recursor application — the
spine analyser returns `none` and the recognizer refuses. -/
theorem pin_iotaRedexB_nonredex :
    iotaRedexB natEnv 8 natMinorZ natMinorZ = false := rfl

/-- Zero fuel at the recognizer: spine reconstruction succeeds but
the fragment's fuel bound refuses inside `iotaWitnessSB`. -/
theorem pin_iotaRedexB_succ_zero_fuel :
    iotaRedexB natEnv 0 (iotaLhsOf wSucc) (iotaRhsOf wSucc) = false := by
  unfold iotaRedexB iotaReductShapeCert
  rw [pin_iotaReductCert_succ_eq]
  dsimp only
  have h0 : ¬ iotaWitnessSB wSucc 0 = true := by
    rw [pin_iotaWitnessSB_wSucc_zero_fuel]
    exact fun h => Bool.noConfusion h
  rw [dif_neg h0]

end Rcic.Declarative
