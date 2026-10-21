import rcic.RcicEtaKLambdaClass

/-! An unconditional, constructive obstruction to joining the ACTUAL positive
A2 peak. A join yields real proof typings at one of four explicitly defined
positions. Their exclusion is a named open obligation, NOT assumed as an axiom
or claimed from positivity. No relation or producer is changed. closure_claim=0. -/
namespace Rcic.Declarative.F8EtaK.A2
set_option maxRecDepth 8192

def positiveCtx : LCtx := ctx (.succ .zero)
def positiveArgs : List (Expr Nat) := [.bvar 3, .bvar 2, .bvar 1, .bvar 0, .bvar 2]

/-- Concrete typing witnesses, not a synonym for (non-)joinability. -/
inductive ProofEscape : Prop where
  | variable (i : Nat) {P : Expr Nat}
      (hP : HasTyT eqEnvT 2 positiveCtx P (.sort .zero))
      (hp : HasTyT eqEnvT 2 positiveCtx (.bvar i) P) : ProofEscape
  | shortRec {ls : List Level} {xs : List (Expr Nat)} {P : Expr Nat}
      (hls : GoodLs ls) (hlen : xs.length < 6) (hvars : AllVars xs)
      (hP : HasTyT eqEnvT 2 positiveCtx P (.sort .zero))
      (hp : HasTyT eqEnvT 2 positiveCtx (foldApps (.const 65 ls) xs) P) : ProofEscape
  | minor {A P : Expr Nat}
      (hΓ : CtxWfT eqEnvT 2 (.assumption A :: positiveCtx))
      (hP : HasTyT eqEnvT 2 (.assumption A :: positiveCtx) P (.sort .zero))
      (hp : HasTyT eqEnvT 2 (.assumption A :: positiveCtx) (.bvar 1) P) : ProofEscape
  | abstraction {A P : Expr Nat}
      (hP : HasTyT eqEnvT 2 positiveCtx P (.sort .zero))
      (hp : HasTyT eqEnvT 2 positiveCtx (.lam A (.bvar 1)) P) : ProofEscape

/-- Named residual: not proved and not silently injected into any definition. -/
def NoProofEscape : Prop := ¬ ProofEscape

theorem positiveCtx_noLet (i : Nat) (A v : Expr Nat) :
    positiveCtx.get? i ≠ some (.letBinding A v) := by
  match i with
  | 0 => simp [positiveCtx, ctx, eqJoinCtx, instLvlsCtx, instLvlsDecl]
  | 1 => simp [positiveCtx, ctx, eqJoinCtx, instLvlsCtx, instLvlsDecl]
  | 2 => simp [positiveCtx, ctx, eqJoinCtx, instLvlsCtx, instLvlsDecl]
  | 3 => simp [positiveCtx, ctx, eqJoinCtx, instLvlsCtx, instLvlsDecl]
  | k + 4 =>
      intro h
      have hl : positiveCtx.length ≤ k + 4 := by
        have : positiveCtx.length = 4 := rfl
        omega
      rw [List.get?_eq_none.mpr hl] at h
      exact Option.noConfusion h

theorem positiveArgs_vars : AllVars positiveArgs := by
  intro x hx
  simp only [positiveArgs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact ⟨3, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

theorem rec_star_or : {a b T : Expr Nat} →
    (s : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveCtx a b T) →
    NoEtaKStar s →
    RecClass positiveArgs a → RecClass positiveArgs b ∨ ProofEscape
  | _, _, _, .refl _ _ _ _, _, hc => .inl hc
  | _, _, _, .tail h s, hno, hc => by
      rcases hno with ⟨hno1, hno2⟩
      rcases hc with ⟨ls, he, hls⟩
      rcases par_rec_or positiveCtx_noLet
        (fun {i P} hP hp => ProofEscape.variable i hP hp)
        (fun hls hn hv hP hp => ProofEscape.shortRec hls hn hv hP hp)
        h hno1 ls positiveArgs he hls (by decide) positiveArgs_vars with hc' | esc
      · exact rec_star_or s hno2 hc'
      · exact .inr esc

theorem lam_star_or : {a b T : Expr Nat} →
    ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveCtx a b T →
    LamClass a → LamClass b ∨ ProofEscape
  | _, _, _, .refl _ _ _ _, hc => .inl hc
  | _, _, _, .tail h s, hc => by
      rcases hc with ⟨A, he⟩
      rcases par_lam_or
        (fun hP hp => ProofEscape.abstraction hP hp)
        (fun hΓ hP hp => ProofEscape.minor hΓ hP hp)
        (contextWf _ positive_levels) (positiveCtx_noLet 0) h A he with hc' | esc
      · exact lam_star_or s hc'
      · exact .inr esc

/-- Joinability for the KEta-free ParRedT(PEqLeafT) and its finite closure. -/
def PositiveJoinable : Prop := ∃ c : Expr Nat,
    (∃ hl : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveCtx
      (partialRec (.succ .zero)) c commonIndex, NoEtaKStar hl) ∧
    (∃ hr : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveCtx
      contracted c commonIndex, NoEtaKStar hr)

/-- Every hypothetical common reduct produces an actual typing witness from
one of the four escape classes. No uniqueness or separation premise is used. -/
theorem positive_join_forces_escape : PositiveJoinable → ProofEscape := by
  rintro ⟨c, ⟨hl, hno⟩, ⟨hr, _hnoR⟩⟩
  have hleft : RecClass positiveArgs (partialRec (.succ .zero)) :=
    ⟨[.succ .zero], rfl, ⟨fun _ => rfl, True.intro⟩⟩
  rcases rec_star_or hl hno hleft with hc | esc
  · rcases lam_star_or hr ⟨domain, rfl⟩ with hd | esc
    · rcases hc with ⟨ls, hc, _⟩
      rcases hd with ⟨A, hd⟩
      exact False.elim (const_spine_not_lam (hc.symm.trans hd))
    · exact esc
  · exact esc

/-- CONDITIONAL non-joinability. NoProofEscape is an explicit unpaid premise. -/
theorem positive_not_joinable_of_no_escape (h : NoProofEscape) : ¬ PositiveJoinable :=
  fun hj => h (positive_join_forces_escape hj)


/-- Also cover the proof-leaf-modulo version of D, not only an identical common term. -/
def PositiveModuloJoinable : Prop := ∃ l r : Expr Nat,
    (∃ hl : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveCtx
      (partialRec (.succ .zero)) l commonIndex, NoEtaKStar hl) ∧
    (∃ hr : ParRedTStar (PEqLeafT eqEnvT 2) eqEnvT 2 positiveCtx
      contracted r commonIndex, NoEtaKStar hr) ∧
    Nonempty (PEqLeafT eqEnvT 2 positiveCtx l r commonIndex)

theorem positive_modulo_join_forces_escape : PositiveModuloJoinable → ProofEscape := by
  rintro ⟨l, r, ⟨hl, hno⟩, ⟨hr, _hnoR⟩, ⟨hm⟩⟩
  have hleft : RecClass positiveArgs (partialRec (.succ .zero)) :=
    ⟨[.succ .zero], rfl, ⟨fun _ => rfl, True.intro⟩⟩
  rcases rec_star_or hl hno hleft with hc | esc
  · rcases lam_star_or hr ⟨domain, rfl⟩ with hd | esc
    · rcases hc with ⟨ls, hc, hls⟩
      rcases raw_rec_or
        (fun {i P} hP hp => ProofEscape.variable i hP hp)
        (fun hls hn hv hP hp => ProofEscape.shortRec hls hn hv hP hp)
        hm.1 ls positiveArgs hc hls (by decide) positiveArgs_vars with hrc | esc
      · rcases hrc with ⟨ls', hrc, _⟩
        rcases hd with ⟨A, hd⟩
        exact False.elim (const_spine_not_lam (hrc.symm.trans hd))
      · exact esc
    · exact esc
  · exact esc

theorem positive_not_modulo_joinable_of_no_escape (h : NoProofEscape) :
    ¬ PositiveModuloJoinable := fun hj => h (positive_modulo_join_forces_escape hj)

theorem positive_partial_no_K_call (w : IotaWitness eqEnvT) (major : Expr Nat) :
    recCall (.const w.recRef w.ls) w.preMajor major ≠ partialRec (.succ .zero) :=
  fun he => call_not_short (xs := positiveArgs) w major (by decide) he

theorem positive_partial_no_derived_iota {rhs : Expr Nat}
    (h : DerivedIotaU eqEnvT (partialRec (.succ .zero)) rhs) : False :=
  iota_not_short (xs := positiveArgs) h (by decide) rfl

theorem positive_canonical_arity : (witness (.succ .zero)).preMajor.length + 1 = 6 :=
  witness_arity _ rfl

theorem positive_partial_arity : (appsSpine (partialRec (.succ .zero))).2.length = 5 := rfl

theorem zero_not_good : ¬ GoodLs [.zero] := by
  intro h
  have hz := h.1 (fun _ => none)
  cases hz

end Rcic.Declarative.F8EtaK.A2
