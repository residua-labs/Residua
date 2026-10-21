import rcic.RcicIotaShapeAdapterPins
import rcic.RcicTypedIdxAdmitted
import rcic.RcicTypedIdxAdmittedPins

namespace Rcic.Declarative

/-! ## DT-024T-witness: the witness analyses are fuel-independent
above a term-determined bound

`IotaWitnessS` stores a `fuel` field (`hshapes`/`hschema`/`hstable`
are run at it), `IotaDescriptorClause` a per-constructor `fuelAt`
(`analyzed`/`typed` are run at it), and `RecursorGroupIdxAdmittedT`'s
`stable`/`covered` quantify over both. The DT-024T-witness follow-up
(#6558 LAND comment) asks that the ι rule not depend on any such fuel
choice: every analysis verdict a witness carries must reproduce
verbatim at every larger bound — "stable under fuel increase" — and
two successful runs of the same analysis cannot disagree.

MEASUREMENT (what already existed, and where):

* `RcicIndGroupJudgment`: the full `some`-monotonicity chain
  `whnfFuel_mono`, `containsFamilyFuel_mono`, `indicesCleanFuel_mono`,
  `domainsContainFuel_mono`, `piTelescopeFuel_mono`,
  `properFamilyFuel_mono`, `fieldAnalyze_mono`, `fieldShapesFuel_mono`,
  `funRecArg_mono`, `iotaArgs_mono`, `iotaOpenRhs_mono` — plus
  cross-fuel verdict uniqueness `fieldAnalyze_agree`,
  `fieldShapesFuel_agree`, `iotaOpenRhs_agree`.
* `RcicIotaShapeStable`: the closure check `constsMemberFuel` with its
  fuel-free certificate `ConstsMemberClosed` (`constsMemberFuel_sound`),
  the env-extension stability lemmas `*_ext` at fixed fuel, and
  `iotaWitnessStableB`/`iotaWitnessS_hstable_of_constsMemberFuel`.
* `RcicIotaShapeAdapter`: the syntactic stability predicates
  `noTransparentB`/`headStableB`, `whnfFuel_of_stable`,
  `piTelescopeFuel_of_tailStable` (`piCount T + 2 ≤ fuel` — the
  term-determined bound), the `*_of_noTransparent` equivalences, the
  DIRECT fragment `DirectFieldFrag` (whose `fuelBound` is the
  term-determined `esize T + piCount T + 2 ≤ fuel`),
  `fieldShapesFuel_eq_analyzeFields_of_directFrag` (the fuel-bounded
  analysis literally EQUALS the fuel-free `analyzeFields` there), and
  the recognizer/adapter pair `iotaWitnessSB`/`iotaWitnessSOf`.

GAPS this file fills:

* `constsMemberFuel_mono` — the one fuel consumer without
  monotonicity (its fuel drops only on transparent δ-unfolds, so the
  proof is a nested fuel×term induction like `constsMemberFuel_sound`).
* `iotaWitnessStableB_mono`, `directFragOne_mono`,
  `directFragCheck_mono`, `DirectFieldFrag.fuel_mono` — the
  closure/fragment checks persist under fuel increase.
* `iotaSchemaAt_mono`/`_agree`, `iotaSchemaAtIn_mono`,
  `iotaSchemaS_mono` — the schema analyses at the descriptor and
  adapter levels.
* `iotaWitnessSB_mono` — the DIRECT recognizer persists.
* `IotaWitnessS.fuelStable` / `IotaWitnessS.analysis_agree`,
  `IotaDescriptorClause.fuelStable`,
  `RecursorGroupIdxAdmittedT.schema_fuelStable`,
  `RecursorGroupIdxAdmittedT.fuelStable` — the packaged statements at
  the three carriers.
* `IdxSrcFuel_mono` / `IdxSrcFuelList_mono` /
  `recIdxSrcFuelWalk_mono` — `IotaTyping.hidxFuel`'s openness bound is
  monotone in `n` (it is a level-param bound, not a recursion fuel;
  `IotaWitness` itself stores no fuel — `analyzeFields`, `applyTel`,
  `peelPis`, `isPiTel`, `directRecConstHead`, `resultConstHead` are
  all fuel-free).

Net: any `IotaWitnessS`/`IotaDescriptorClause` built at one bound is
rebuildable at every larger bound with IDENTICAL `shapes`/`schema`,
and on the DIRECT fragment the bound is the term-determined
`esize + piCount + 2`. The ι rule's data is determined by the stored
declarations, not by a fuel choice. -/

/-! ### The closure check: `constsMemberFuel` -/

/-- `constsMemberFuel` is stable under fuel increase: a successful
closure check at `fuel` reproduces at every `fuel' ≥ fuel`. Fuel drops
only on transparent δ-unfolds (the `.const` branch); structural
recursion passes it unchanged, so the proof is the same nested
fuel×term induction as `constsMemberFuel_sound`. -/
theorem constsMemberFuel_mono (E : ResolvedEnv) :
    ∀ (fuel : Nat) (e : Expr Nat),
      constsMemberFuel E fuel e = true →
      ∀ (fuel' : Nat), fuel ≤ fuel' → constsMemberFuel E fuel' e = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro e h fuel' _
      simp only [constsMemberFuel] at h
      nomatch h
  | succ F ihF =>
      intro e h fuel' hle
      cases fuel' with
      | zero => omega
      | succ F' =>
          have hle' : F ≤ F' := Nat.le_of_succ_le_succ hle
          induction e with
          | bvar i => simp only [constsMemberFuel]
          | sort l => simp only [constsMemberFuel]
          | lit t =>
              have step : ∀ r : Nat,
                  (match E.members r with
                   | none => false
                   | some m =>
                       if transparent m.mclass then
                         match m.body with
                         | some body =>
                             constsMemberFuel E F (instantiateLevels [] body)
                         | none => true
                       else true) = true →
                  (match E.members r with
                   | none => false
                   | some m =>
                       if transparent m.mclass then
                         match m.body with
                         | some body =>
                             constsMemberFuel E F' (instantiateLevels [] body)
                         | none => true
                       else true) = true := by
                intro r hr
                cases hm : E.members r with
                | none =>
                    simp only [hm] at hr
                    nomatch hr
                | some m =>
                    simp only [hm] at hr ⊢
                    cases ht : transparent m.mclass with
                    | false => rfl
                    | true =>
                        cases hb : m.body with
                        | none => rfl
                        | some body =>
                            simp only [ht, hb] at hr ⊢
                            exact ihF _ hr _ hle'
              cases t with
              | zero =>
                  simp only [constsMemberFuel] at h ⊢
                  exact step 1 h
              | succ t' =>
                  simp only [constsMemberFuel, Bool.and_eq_true] at h ⊢
                  exact ⟨step 2 h.1, step 1 h.2⟩
          | const r ls =>
              simp only [constsMemberFuel] at h ⊢
              cases hm : E.members r with
              | none =>
                  simp only [hm] at h
                  nomatch h
              | some m =>
                  simp only [hm] at h ⊢
                  cases ht : transparent m.mclass with
                  | false => rfl
                  | true =>
                      cases hb : m.body with
                      | none => rfl
                      | some body =>
                          simp only [ht, hb] at h ⊢
                          exact ihF _ h _ hle'
          | app f a ihf iha =>
              simp only [constsMemberFuel, Bool.and_eq_true] at h ⊢
              exact ⟨ihf h.1, iha h.2⟩
          | lam A b ihA ihb =>
              simp only [constsMemberFuel, Bool.and_eq_true] at h ⊢
              exact ⟨ihA h.1, ihb h.2⟩
          | pi A b ihA ihb =>
              simp only [constsMemberFuel, Bool.and_eq_true] at h ⊢
              exact ⟨ihA h.1, ihb h.2⟩
          | letE A v b ihA ihv ihb =>
              simp only [constsMemberFuel, Bool.and_eq_true] at h ⊢
              exact ⟨⟨ihA h.1.1, ihv h.1.2⟩, ihb h.2⟩

/-- `constsMemberFuel` over a list is stable under fuel increase. -/
theorem constsMemberFuel_all_mono (E : ResolvedEnv) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') :
    ∀ (Ts : List (Expr Nat)),
      Ts.all (constsMemberFuel E fuel) = true →
        Ts.all (constsMemberFuel E fuel') = true := by
  intro Ts h
  rw [List.all_eq_true] at h ⊢
  intro T hT
  exact constsMemberFuel_mono E _ _ (h T hT) _ hle

/-- `iotaWitnessStableB` is stable under fuel increase: the closure
check it runs uses `fuel + 1` throughout. -/
theorem iotaWitnessStableB_mono (E : ResolvedEnv) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') {fieldDoms fields : List (Expr Nat)}
    {tel : Expr Nat}
    (h : iotaWitnessStableB E fuel fieldDoms fields tel = true) :
    iotaWitnessStableB E fuel' fieldDoms fields tel = true := by
  simp only [iotaWitnessStableB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  have hle' : fuel + 1 ≤ fuel' + 1 := Nat.succ_le_succ hle
  refine ⟨⟨fun T hT => constsMemberFuel_mono E _ _ (h.1.1 T hT) _ hle',
           fun T hT => constsMemberFuel_mono E _ _ (h.1.2 T hT) _ hle'⟩,
          constsMemberFuel_mono E _ _ h.2 _ hle'⟩

/-! ### The DIRECT fragment checks -/

/-- `directFragOne` is stable under fuel increase: every conjunct is
fuel-free except `decide (esize T + piCount T + 2 ≤ fuel)` — the
term-determined bound — which is `Nat.le`-monotone. -/
theorem directFragOne_mono (E : ResolvedEnv) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') {fam nuniv nparams nindices depth : Nat}
    {T : Expr Nat}
    (h : directFragOne E fuel fam nuniv nparams nindices depth T = true) :
    directFragOne E fuel' fam nuniv nparams nindices depth T = true := by
  simp only [directFragOne, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨hrig, hstab⟩, hfuel⟩, hcan⟩, hnoin⟩ := h
  refine ⟨⟨⟨⟨hrig, hstab⟩, ?_⟩, hcan⟩, hnoin⟩
  exact decide_eq_true (Nat.le_trans (of_decide_eq_true hfuel) hle)

/-- `directFragCheck` is stable under fuel increase. -/
theorem directFragCheck_mono (E : ResolvedEnv) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') {fam nuniv nparams nindices depth : Nat} :
    ∀ (Ts : List (Expr Nat)),
      directFragCheck E fuel fam nuniv nparams nindices depth Ts = true →
        directFragCheck E fuel' fam nuniv nparams nindices depth Ts = true := by
  intro Ts h
  induction Ts generalizing depth with
  | nil => rfl
  | cons T Ts ih =>
      simp only [directFragCheck, Bool.and_eq_true] at h ⊢
      exact ⟨directFragOne_mono E hle h.1, ih h.2⟩

/-- The Prop-level fragment is stable under fuel increase: `fuelBound`
is the only fuel mention, and it weakens along `≤`. -/
theorem DirectFieldFrag.fuel_mono {E : ResolvedEnv}
    {fuel fuel' fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    (h : DirectFieldFrag E fuel fam nuniv nparams nindices depth T)
    (hle : fuel ≤ fuel') :
    DirectFieldFrag E fuel' fam nuniv nparams nindices depth T where
  rigid := h.rigid
  stableTail := h.stableTail
  fuelBound := Nat.le_trans h.fuelBound hle
  canon := h.canon
  noInner := h.noInner

/-- On the DIRECT fragment `fieldShapesFuel` returns the fuel-free
`analyzeFields`-of-`shapeOfKind` at EVERY fuel covering the fragment's
own bound — the strongest form of fuel-independence: the analysis
collapses to a fuel-free function of the stored type. -/
theorem fieldShapesFuel_directFrag_fuelStable {E : ResolvedEnv}
    {fuel fuel' fam nuniv nparams nindices depth : Nat}
    {Ts : List (Expr Nat)}
    (hfr : ∀ j (hj : j < Ts.length),
        DirectFieldFrag E fuel fam nuniv nparams nindices (depth + j) Ts[j])
    (hle : fuel ≤ fuel') :
    fieldShapesFuel E fuel' fam nuniv nparams nindices depth Ts =
      (analyzeFields fam Ts).map fun ks => ks.map shapeOfKind :=
  fieldShapesFuel_eq_analyzeFields_of_directFrag Ts fun j hj =>
    (hfr j hj).fuel_mono hle

/-! ### The schema analyses -/

/-- `iotaSchemaAt` is stable under fuel increase. -/
theorem iotaSchemaAt_mono {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {shapes : List FieldShape} {schema : Expr Nat}
    (h : iotaSchemaAt a i fuel shapes = some schema) :
    iotaSchemaAt a i fuel' shapes = some schema :=
  iotaOpenRhs_mono E hle h

/-- `iotaSchemaAt` verdicts are unique across fuels. -/
theorem iotaSchemaAt_agree {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    {fuel₁ fuel₂ : Nat} {shapes : List FieldShape} {s₁ s₂ : Expr Nat}
    (h₁ : iotaSchemaAt a i fuel₁ shapes = some s₁)
    (h₂ : iotaSchemaAt a i fuel₂ shapes = some s₂) : s₁ = s₂ :=
  iotaOpenRhs_agree E h₁ h₂

/-- `iotaSchemaAtIn` is stable under fuel increase. -/
theorem iotaSchemaAtIn_mono {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (E' : ResolvedEnv)
    (a : RecursorEliminationAdmitted E r m) (i : Fin a.constructors.length)
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    {shapes : List FieldShape} {schema : Expr Nat}
    (h : iotaSchemaAtIn E' a i fuel shapes = some schema) :
    iotaSchemaAtIn E' a i fuel' shapes = some schema :=
  iotaOpenRhs_mono E' hle h

/-- `iotaSchemaS` is stable under fuel increase. -/
theorem iotaSchemaS_mono {E : ResolvedEnv} (w : IotaWitness E)
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') {schema : Expr Nat}
    (h : iotaSchemaS w fuel = some schema) :
    iotaSchemaS w fuel' = some schema :=
  iotaOpenRhs_mono E hle h

/-- `iotaSchemaS` verdicts are unique across fuels. -/
theorem iotaSchemaS_agree {E : ResolvedEnv} (w : IotaWitness E)
    {fuel₁ fuel₂ : Nat} {s₁ s₂ : Expr Nat}
    (h₁ : iotaSchemaS w fuel₁ = some s₁) (h₂ : iotaSchemaS w fuel₂ = some s₂) :
    s₁ = s₂ :=
  iotaOpenRhs_agree E h₁ h₂

/-- The DIRECT recognizer is stable under fuel increase: every
conjunct persists (the schema conjunct recomputes the same schema by
`iotaOpenRhs_agree` uniqueness). -/
theorem iotaWitnessSB_mono (w : IotaWitness E) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') (h : iotaWitnessSB w fuel = true) :
    iotaWitnessSB w fuel' = true := by
  unfold iotaWitnessSB at h ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨hfrag, hstable⟩, hmatch⟩ := h
  refine ⟨⟨directFragCheck_mono E hle _ hfrag,
           iotaWitnessStableB_mono E hle hstable⟩, ?_⟩
  cases hs : iotaSchemaS w fuel with
  | none =>
      rw [hs] at hmatch
      simp only at hmatch
      exact absurd hmatch (by decide)
  | some s =>
      rw [hs] at hmatch
      rw [iotaSchemaS_mono w hle hs]
      exact hmatch

/-! ### The witness carriers -/

/-- DT-024T-witness, `IotaWitnessS` (1/2): the analyses a witness
stores reproduce verbatim at every fuel ≥ its own bound — the shapes
and schema the ι rule consumes are determined by the stored
declarations, not by the fuel the witness was built at. -/
theorem IotaWitnessS.fuelStable {E : ResolvedEnv} (w : IotaWitnessS E)
    {fuel' : Nat} (hle : w.fuel ≤ fuel') :
    fieldShapesFuel E fuel' w.familyRef w.famMember.arity w.nparams
        w.nindices w.nparams (w.ctorDoms.drop w.nparams) = some w.shapes ∧
      iotaOpenRhs E fuel'
          (.const w.recRef (canonRecLevels w.recMember.arity))
          (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
          (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
          w.nparams w.nMinors w.shapes (fieldBvars w.fields.length)
          (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = some w.schema :=
  ⟨fieldShapesFuel_mono E hle w.hshapes, iotaOpenRhs_mono E hle w.hschema⟩

/-- DT-024T-witness, `IotaWitnessS` (2/2): a second successful run of
the same analyses — another witness at another bound — cannot return
different data. -/
theorem IotaWitnessS.analysis_agree {E : ResolvedEnv} (w : IotaWitnessS E)
    {fuel' : Nat} {shapes' : List FieldShape} {schema' : Expr Nat}
    (h₁ : fieldShapesFuel E fuel' w.familyRef w.famMember.arity w.nparams
        w.nindices w.nparams (w.ctorDoms.drop w.nparams) = some shapes')
    (h₂ : iotaOpenRhs E fuel'
          (.const w.recRef (canonRecLevels w.recMember.arity))
          (.bvar (w.fields.length + w.nindices + (w.nMinors - 1 - w.ctorIdx)))
          (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
          w.nparams w.nMinors w.shapes (fieldBvars w.fields.length)
          (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
            (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)) = some schema') :
    shapes' = w.shapes ∧ schema' = w.schema :=
  ⟨fieldShapesFuel_agree E h₁ w.hshapes, iotaOpenRhs_agree E h₂ w.hschema⟩

/-- DT-024T-witness, `IotaDescriptorClause` (1/2): the per-constructor
field analysis reproduces at every fuel ≥ `fuelAt i`. -/
theorem IotaDescriptorClause.fuelStable {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} {a : RecursorEliminationAdmitted E r m}
    (h14 : IotaDescriptorClause E a)
    (i : Fin a.constructors.length) {fuel' : Nat} (hle : h14.fuelAt i ≤ fuel') :
    fieldShapesFuel E fuel' a.family.ref a.family.member.arity
      a.family.parameters.length a.family.indices.length
      a.family.parameters.length (a.constructorViews i).fields =
        some (h14.shapesAt i) :=
  fieldShapesFuel_mono E hle (h14.analyzed i)

/-- DT-024T-witness, `IotaDescriptorClause` (2/2): under the
recursor/index obligation, the canonical schema at `fuelAt i` is
`some (descriptorSchema a h14 i)` — and stays that schema at every
larger fuel. -/
theorem RecursorGroupIdxAdmittedT.schema_fuelStable {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} {a : RecursorEliminationAdmitted E r m}
    {h14 : IotaDescriptorClause E a}
    (_ : RecursorGroupIdxAdmittedT a h14)
    (i : Fin a.constructors.length) {fuel' : Nat} (hle : h14.fuelAt i ≤ fuel') :
    iotaSchemaAt a i fuel' (h14.shapesAt i) = some (descriptorSchema a h14 i) :=
  iotaSchemaAt_mono a i hle (descriptorSchema_spec a h14 i)

/-- The full stable package at an arbitrary extension AND arbitrary
larger fuel: the descriptor's analysis recomputes identically, so the
obligation's `stable`/`covered` clauses do not depend on `fuelAt i`
being exactly the bound chosen. -/
theorem RecursorGroupIdxAdmittedT.fuelStable {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} {a : RecursorEliminationAdmitted E r m}
    {h14 : IotaDescriptorClause E a}
    (rga : RecursorGroupIdxAdmittedT a h14)
    (i : Fin a.constructors.length) (E' : ResolvedEnv)
    (hext : ∀ r' m', E.members r' = some m' → E'.members r' = some m')
    {fuel' : Nat} (hle : h14.fuelAt i ≤ fuel') :
    fieldShapesFuel E' fuel' a.family.ref a.family.member.arity
        a.family.parameters.length a.family.indices.length
        a.family.parameters.length (a.constructorViews i).fields =
          some (h14.shapesAt i) ∧
      iotaSchemaAtIn E' a i fuel' (h14.shapesAt i) =
        some (descriptorSchema a h14 i) := by
  obtain ⟨hsh, hsc⟩ := rga.stable i E' hext
  refine ⟨fieldShapesFuel_mono E' hle hsh, ?_⟩
  have hspec := descriptorSchema_spec a h14 i
  rw [← hsc] at hspec
  exact iotaSchemaAtIn_mono E' a i hle hspec

/-! ### `IotaTyping.hidxFuel`'s openness bound -/

/-- `IdxSrcFuel` is monotone in the level-param bound `n`. -/
theorem IdxSrcFuel_mono {n n' : Nat} (hle : n ≤ n') :
    ∀ {e : Expr Nat} {s : IdxSrc}, IdxSrcFuel n e s → IdxSrcFuel n' e s := by
  intro e
  induction e with
  | const r ls =>
      intro s h
      cases s with
      | constNotFam _ =>
          intro l hl
          obtain ⟨k, hk⟩ := h l hl
          exact ⟨k, hk.elim Or.inl fun hk' => Or.inr (by omega)⟩
      | _ => exact h
  | app f a ihf iha =>
      intro s h
      cases s with
      | app sf sa => exact ⟨ihf h.1, iha h.2⟩
      | _ => exact h
  | _ => intro s h; exact h

/-- `IdxSrcFuelList` is monotone in the level-param bound `n`. -/
theorem IdxSrcFuelList_mono {n n' : Nat} (hle : n ≤ n') :
    ∀ {xs : List (Expr Nat)} {ss : List IdxSrc},
      IdxSrcFuelList n xs ss → IdxSrcFuelList n' xs ss := by
  intro xs
  induction xs with
  | nil => intro ss h; exact h
  | cons x xs ih =>
      intro ss h
      cases ss with
      | nil => exact h
      | cons s ss => exact ⟨IdxSrcFuel_mono hle h.1, ih h.2⟩

/-- `recIdxSrcFuelWalk` is monotone in the level-param bound `n` —
`IotaTyping.hidxFuel`'s openness is stable under increasing the bound,
and `n` is determined by the level parameters the sources carry, not
by a recursion fuel choice. -/
theorem recIdxSrcFuelWalk_mono {n n' nparams : Nat} (hle : n ≤ n') :
    ∀ (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
      (pss : List (List IdxSrc)),
      recIdxSrcFuelWalk n nparams ks T fs pss →
        recIdxSrcFuelWalk n' nparams ks T fs pss := by
  intro ks
  induction ks with
  | nil => intro T fs pss h; exact h
  | cons k ks ih =>
      intro T fs pss h
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | cons f fs =>
                  cases pss with
                  | cons ps pss =>
                      cases ps with
                      | nil => exact ih _ _ _ h
                      | cons _ _ => exact h
                  | nil => exact h
              | nil => exact h
          | _ => exact h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | cons f fs =>
                  cases pss with
                  | cons src pss =>
                      exact ⟨IdxSrcFuelList_mono hle h.1, ih _ _ _ h.2⟩
                  | nil => exact h
              | nil => exact h
          | _ => exact h

/-! ### Pins -/

/-- The Nat successor S-witness's analyses reproduce at fuel 16 (it was
built at 8). -/
theorem pin_wSuccS_fuelStable :
    fieldShapesFuel natEnv 16 wSuccS.familyRef wSuccS.famMember.arity
        wSuccS.nparams wSuccS.nindices wSuccS.nparams
        (wSuccS.ctorDoms.drop wSuccS.nparams) = some wSuccS.shapes ∧
      iotaOpenRhs natEnv 16
          (.const wSuccS.recRef (canonRecLevels wSuccS.recMember.arity))
          (.bvar (wSuccS.fields.length + wSuccS.nindices +
            (wSuccS.nMinors - 1 - wSuccS.ctorIdx)))
          (preMajorBvars wSuccS.nparams wSuccS.nMinors wSuccS.nindices
            wSuccS.fields.length)
          wSuccS.nparams wSuccS.nMinors wSuccS.shapes
          (fieldBvars wSuccS.fields.length)
          (lift 0 (wSuccS.fields.length + 1 + wSuccS.nMinors + wSuccS.nindices)
            (ctorFieldTelRaw wSuccS.nparams wSuccS.ctorDoms
              wSuccS.ctorResult)) = some wSuccS.schema :=
  wSuccS.fuelStable (by decide)

/-- The recognizer persists: `iotaWitnessSB wSucc` at 16, from its
success at 8. -/
theorem pin_iotaWitnessSB_wSucc_16 : iotaWitnessSB wSucc 16 = true :=
  iotaWitnessSB_mono wSucc (by decide) pin_iotaWitnessSB_wSucc

/-- The adapted witness at the higher bound is the same ι rule:
`iotaLhsOfS`/`iotaRhsOfS` read only the fuel-free fields. -/
theorem pin_wSuccS_16_same_rule :
    iotaLhsOfS (iotaWitnessSOf wSucc 16 pin_iotaWitnessSB_wSucc_16) =
      iotaLhsOfS wSuccS ∧
    iotaRhsOfS (iotaWitnessSOf wSucc 16 pin_iotaWitnessSB_wSucc_16) =
      iotaRhsOfS wSuccS := by
  refine ⟨?_, ?_⟩
  · rw [iotaLhsOfS_iotaWitnessSOf wSucc 16 pin_iotaWitnessSB_wSucc_16,
        pin_wSuccS_lhs]
  · rw [iotaRhsOfS_iotaWitnessSOf wSucc 16 pin_iotaWitnessSB_wSucc_16,
        pin_wSuccS_rhs]

/-- Nat's descriptor clause: the field analysis at fuel 8 (the
descriptor was built at `fuelAt = 4`) reproduces the recorded
shapes. -/
theorem pin_natIotaClause_fuelStable
    (i : Fin natGroupAdmitted.constructors.length) :
    fieldShapesFuel natEnvPrefix 8 natGroupAdmitted.family.ref
        natGroupAdmitted.family.member.arity
        natGroupAdmitted.family.parameters.length
        natGroupAdmitted.family.indices.length
        natGroupAdmitted.family.parameters.length
        (natGroupAdmitted.constructorViews i).fields =
          some (natIotaClause.shapesAt i) :=
  natIotaClause.fuelStable i (by show (4 : Nat) ≤ 8; decide)

/-- Nat's descriptor schema at fuel 8 is the canonical
`descriptorSchema` — the same value `fuelAt = 4` computes. -/
theorem pin_natRecIdx_schema_fuelStable
    (i : Fin natGroupAdmitted.constructors.length) :
    iotaSchemaAt natGroupAdmitted i 8 (natIotaClause.shapesAt i) =
      some (descriptorSchema natGroupAdmitted natIotaClause i) := by
  apply RecursorGroupIdxAdmittedT.schema_fuelStable natRecIdxAdmittedT i
  show (4 : Nat) ≤ 8
  decide

/-- `IotaTyping.hidxFuel`'s openness walk at bound 0 reproduces at
bound 4 on an all-`.pos` source list — monotone in `n`. -/
theorem pin_recIdxSrcFuelWalk_mono {nparams : Nat}
    {ks : List RecKind} {T : Expr Nat} {fs : List (Expr Nat)}
    {pss : List (List Nat)}
    (h : recIdxSrcFuelWalk 0 nparams ks T fs
      (pss.map fun is => is.map IdxSrc.pos)) :
    recIdxSrcFuelWalk 4 nparams ks T fs
      (pss.map fun is => is.map IdxSrc.pos) :=
  recIdxSrcFuelWalk_mono (by decide) _ _ _ _ h

#print axioms constsMemberFuel_mono
#print axioms iotaWitnessStableB_mono
#print axioms directFragCheck_mono
#print axioms iotaSchemaAt_mono
#print axioms iotaSchemaAt_agree
#print axioms iotaWitnessSB_mono
#print axioms IotaWitnessS.fuelStable
#print axioms IotaWitnessS.analysis_agree
#print axioms IotaDescriptorClause.fuelStable
#print axioms RecursorGroupIdxAdmittedT.fuelStable
#print axioms IdxSrcFuel_mono
#print axioms recIdxSrcFuelWalk_mono
#print axioms pin_wSuccS_fuelStable
#print axioms pin_iotaWitnessSB_wSucc_16
#print axioms pin_natIotaClause_fuelStable
#print axioms pin_natRecIdx_schema_fuelStable

end Rcic.Declarative
