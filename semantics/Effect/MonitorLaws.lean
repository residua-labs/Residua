import Effect.Monitor

namespace Effect.ABI

theorem LocalJudgment.functional {core : Core} {registry : Registry} {c : Context core}
    {s : State} {event : Event core} {out other : Outcome core}
    (a : LocalJudgment registry c s event out) (b : LocalJudgment registry c s event other) :
    out = other := by
  cases a with
  | refuse first =>
    cases b with
    | refuse second => rw [first.unique second]
    | openSession p | send p | receive p _ _ _ => exact (p.noFirst first).elim
  | openSession p =>
    cases b with
    | refuse first => exact (p.noFirst first).elim
    | openSession _ => rfl
  | send p =>
    cases b with
    | refuse first => exact (p.noFirst first).elim
    | send _ => rfl
  | receive p ht dt dr =>
    cases b with
    | refuse first => exact (p.noFirst first).elim
    | receive _ ht' dt' dr' =>
      have sameT := Option.some.inj (ht.symm.trans ht')
      subst sameT
      have sameRequest := Option.some.inj (dt.symm.trans dt')
      have sameReply := Option.some.inj (dr.symm.trans dr')
      subst sameRequest
      subst sameReply
      rfl

theorem ReplayFrom.functional {core : Core} {registry : Registry} {c : Context core}
    {plan : Plan core} {s : State} {step : Step core.stateType core.resultType}
    {pairs : List RawPair} {v other : ReplayBoundary core}
    (a : ReplayFrom registry c plan s step pairs v)
    (b : ReplayFrom registry c plan s step pairs other) : v = other := by
  induction a generalizing other with
  | boundary => cases b; rfl
  | extra => cases b; rfl
  | requestMismatch bad =>
    cases b with
    | requestMismatch _ => rfl
    | sendRefused agree _ | receiveRefused agree _ _ | transaction agree _ _ _ _ _ =>
      exact (bad agree).elim
  | sendRefused agree bad =>
    cases b with
    | requestMismatch wrong => exact (wrong agree).elim
    | sendRefused _ bad' => rw [bad.unique bad']
    | receiveRefused _ passed _ | transaction _ passed _ _ _ _ => exact (passed.noFirst bad).elim
  | receiveRefused agree passed bad =>
    cases b with
    | requestMismatch wrong => exact (wrong agree).elim
    | sendRefused _ bad' => exact (passed.noFirst bad').elim
    | receiveRefused _ _ bad' => rw [bad.unique bad']
    | transaction _ _ received _ _ _ => exact (received.noFirst bad).elim
  | transaction agree sent received dt dr _ ih =>
    cases b with
    | requestMismatch wrong => exact (wrong agree).elim
    | sendRefused _ bad => exact (sent.noFirst bad).elim
    | receiveRefused _ _ bad => exact (received.noFirst bad).elim
    | transaction _ _ _ dt' dr' tail =>
      have sameRequest := Option.some.inj (dt.symm.trans dt')
      have sameReply := Option.some.inj (dr.symm.trans dr')
      subst sameRequest
      subst sameReply
      exact ih tail

theorem Replay.functional {core : Core} {registry : Registry} {c : Context core}
    {pairs : List RawPair} {v other : ReplayBoundary core}
    (a : Replay registry c pairs v) (b : Replay registry c pairs other) : v = other := by
  cases a with
  | openRefused bad =>
    cases b with
    | openRefused bad' => rw [bad.unique bad']
    | start passed _ _ => exact (passed.noFirst bad).elim
  | start passed plan prefixReplay =>
    cases b with
    | openRefused bad => exact (passed.noFirst bad).elim
    | start _ plan' otherReplay =>
      have same := Option.some.inj (plan.symm.trans plan')
      subst same
      exact prefixReplay.functional otherReplay

theorem SealJudgment.contextValid {core : Core} {registry : Registry} {store : ObjectStore}
    {c : Context core} {s : State} {request : SealRequest core} {out : Outcome core}
    (a : SealJudgment registry store c s request out) :
    Passes (contextTests registry c s false) := by
  cases a with
  | pending p _ | missing p _ _ | digest p _ _ _ => exact p
  | replayRefused l _ | incomplete l _ | root l _ _ _ | results l _ _ _ _ | accept l _ _ _ _ _ =>
    exact l.contextValid

theorem SealJudgment.functional {core : Core} {registry : Registry} {store : ObjectStore}
    {c : Context core} {s : State} {request : SealRequest core} {out other : Outcome core}
    (a : SealJudgment registry store c s request out)
    (b : SealJudgment registry store c s request other) : out = other := by
  cases a <;> cases b <;> try rfl
  all_goals
    repeat' (rename LoadedTrace _ _ _ _ _ _ => loaded; rcases loaded with ⟨_, _, _, _⟩)
    simp_all
  all_goals
    subst_vars
    rename Replay _ _ _ _ => rightReplay
    revert rightReplay
    rename Replay _ _ _ _ => leftReplay
    intro rightReplay
    have same := leftReplay.functional rightReplay
    cases same <;> simp_all

theorem Admission.functional {core : Core} {registry : Registry} {store : ObjectStore}
    {c : Context core} {s : State} {event : Event core} {out other : Outcome core}
    (a : Admission registry store c s event out)
    (b : Admission registry store c s event other) : out = other := by
  cases a with
  | «local» aa =>
    cases b with
    | «local» bb => exact aa.functional bb
    | «seal» bb =>
      cases aa with
      | refuse first => exact (bb.contextValid.noFirst first).elim
  | «seal» aa =>
    cases b with
    | «local» bb =>
      cases bb with
      | refuse first => exact (aa.contextValid.noFirst first).elim
    | «seal» bb => exact aa.functional bb

namespace Monitor

variable {core : Core}

theorem decision_factorization (registry : Registry) (store : ObjectStore) (c : Context core)
    (input : RawInput core) : run registry store c input = step registry store c (classify input) := rfl

theorem projection_idempotent (input : RawInput core) :
    classify (classify input).embed = classify input := rfl

theorem preimage_invariant (c : Context core) (input : RawInput core) :
    inputPreimage c (sigma (classify input).embed.state) (classify input).embed.event =
    inputPreimage c (sigma input.state) input.event := rfl

theorem q_invariant (c : Context core) (input : RawInput core) :
    inputQ c (sigma (classify input).embed.state) (classify input).embed.event =
    inputQ c (sigma input.state) input.event := congrArg Format.hashCanonical (preimage_invariant c input)

theorem sound (registry : Registry) (store : ObjectStore) (c : Context core) (input : Class core) :
    Admission registry store c input.state input.event (step registry store c input) :=
  (stepCertified registry store c input).property

theorem complete {registry : Registry} {store : ObjectStore} {c : Context core} {input : Class core}
    (derivation : Admission registry store c input.state input.event out) :
    step registry store c input = out := (sound registry store c input).functional derivation

theorem exact_outcome {registry : Registry} {store : ObjectStore} {c : Context core}
    {input : Class core} {out : Outcome core} :
    Admission registry store c input.state input.event out ↔ step registry store c input = out :=
  ⟨complete, fun h => h ▸ sound registry store c input⟩

theorem residue_exact (registry : Registry) (store : ObjectStore) (c : Context core)
    (input : Class core) : residue? registry store c input = (step registry store c input).residue := by
  unfold residue? step stepCertified
  cases Lambda registry store c input with
  | inl r => exact r.property.2.symm
  | inr f => rfl

theorem admit_exact (registry : Registry) (store : ObjectStore) (c : Context core) (input : Class core) :
    admit registry store c input = true ↔
    ∃ out, Admission registry store c input.state input.event out ∧ out.residue = none := by
  unfold admit
  rw [residue_exact]
  constructor
  · intro h
    exact ⟨_, sound registry store c input, by simpa using h⟩
  · rintro ⟨out, h, clear⟩
    rw [complete h, clear]
    rfl

theorem replay_exact {registry : Registry} {c : Context core} {pairs : List RawPair}
    {verdict : ReplayBoundary core} :
    Replay registry c pairs verdict ↔ (replay registry c pairs).val = verdict :=
  let checked := replay registry c pairs
  ⟨fun h => checked.property.functional h, fun h => h ▸ checked.property⟩

theorem rejected_send {registry : Registry} {store : ObjectStore} {c : Context core} (s : State) (t : Bytes)
    (h : (step registry store c ⟨s, .send t⟩).residue = some cause) :
    step registry store c ⟨s, .send t⟩ = ⟨s, some cause, .noIO⟩ :=
  (sound registry store c ⟨s, .send t⟩).refusal h

theorem rejected_receive {registry : Registry} {store : ObjectStore} {c : Context core} (s : State)
    (r : Bytes) (h : (step registry store c ⟨s, .receive r⟩).residue = some cause) :
    step registry store c ⟨s, .receive r⟩ =
      ⟨s, some cause, .close ⟨inputQ c s (.receive r), s.prev, s.pending, .reply r, cause⟩⟩ :=
  (sound registry store c ⟨s, .receive r⟩).refusal h

theorem rejected_fault {registry : Registry} {store : ObjectStore} {c : Context core} (s : State)
    (obs : FaultObservation) (h : (step registry store c ⟨s, .fault obs⟩).residue = some cause) :
    step registry store c ⟨s, .fault obs⟩ =
      ⟨s, some cause, .close ⟨inputQ c s (.fault obs), s.prev, s.pending, .fault obs, cause⟩⟩ :=
  (sound registry store c ⟨s, .fault obs⟩).refusal h

theorem valid_receive {registry : Registry} {store : ObjectStore} {c : Context core} (s : State) (r : Bytes)
    (h : (step registry store c ⟨s, .receive r⟩).residue = none) :
    let out := step registry store c ⟨s, .receive r⟩
    ∃ t, s.pending = some t ∧ out.state.pending = none ∧
      out.state.prev = Format.pair s.prev t r ∧ out.disposition = .commit ⟨t, r⟩ := by
  have j := sound registry store c ⟨s, .receive r⟩
  generalize he : step registry store c ⟨s, .receive r⟩ = out at h j ⊢
  clear he
  cases j with
  | «local» j =>
    cases j with
    | refuse _ => cases h
    | receive _ ht _ _ => exact ⟨_, ht, rfl, rfl, rfl⟩

end Monitor
end Effect.ABI
