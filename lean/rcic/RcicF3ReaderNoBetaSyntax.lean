import rcic.RcicF3PointwiseReaderNoBetaFields

/-!
# Produced trace certificates for literal and zeta-hidden spines

Literal family-headed telescopes produce the new certificate at every
sufficient original fuel. A zeta wrapper preserves the certificate after
one additional head step. These are syntax producers, not semantic laws
supplied by a caller. In particular cached/source equality implies the new
trace face at the actual bodyless family head. closure_claim = 0.
-/
set_option autoImplicit false

namespace Rcic.F3.PSet.ReaderNoBeta
open Rcic.Declarative RawFamily PiValueRule

theorem Head.raise {E : ResolvedEnv} {fuel : Nat} {e w : Expr Nat}
    (h : Head E fuel e w) : Head E (fuel + 1) e w := by
  induction h with
  | stop fuel e hs => exact Head.stop (fuel + 1) e hs
  | zeta hs _ ih => exact Head.zeta hs ih
  | delta hs hb _ ih => exact Head.delta hs hb ih

theorem Telescope.raise {E : ResolvedEnv} {fuel : Nat} {e b : Expr Nat}
    {ds : List (Expr Nat)} (h : Telescope E fuel e ds b) :
    Telescope E (fuel + 1) e ds b := by
  induction h with
  | leaf hh hn => exact Telescope.leaf hh.raise hn
  | pi hh _ ih => exact Telescope.pi hh.raise ih

/-- A literal family-headed Pi telescope takes no beta edge, regardless
of dependencies in its domains or complete terminal argument list. -/
theorem Telescope.literal {E : ResolvedEnv} {f : Nat} {ls : List Level}
    (hf : transparentBody E f ls = none)
    (ds args : List (Expr Nat)) {fuel : Nat} (hfu : ds.length + 2 ≤ fuel) :
    Telescope E fuel (policyPi ds (foldApps (.const f ls) args))
      ds (foldApps (.const f ls) args) := by
  induction ds generalizing fuel with
  | nil =>
      obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by simp only [List.length_nil] at hfu; omega⟩
      apply Telescope.leaf (Head.stop n _ ?_) ?_
      · simp only [Stops, policyPi, appsSpine_foldApps, appsSpine, List.nil_append, hf]
      · intro A B he
        have hs := congrArg appsSpine he
        simp only [policyPi, appsSpine_foldApps, appsSpine, List.nil_append] at hs
        exact Expr.noConfusion (congrArg Prod.fst hs)
  | cons A ds ih =>
      obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 3 :=
        ⟨fuel - 3, by simp only [List.length_cons] at hfu; omega⟩
      apply Telescope.pi (Head.stop (n + 1) _ ?_) (ih ?_)
      · trivial
      · simp only [List.length_cons] at hfu
        omega

/-- A literal zeta wrapper has no semantic side condition. The increased
fuel is also supplied to every retained codomain trace. -/
theorem Telescope.prepend_zeta {E : ResolvedEnv} {fuel : Nat}
    {A v body b : Expr Nat} {ds : List (Expr Nat)}
    (h : Telescope E fuel (instantiate0 v body) ds b) :
    Telescope E (fuel + 1) (.letE A v body) ds b := by
  cases h with
  | leaf hh hn => exact Telescope.leaf (Head.zeta rfl hh) hn
  | pi hh ht => exact Telescope.pi (Head.zeta rfl hh) ht.raise

/-- Concrete hidden recursive syntax: a let-wrapped family head is
certified even though it is not literally its cached normal form. -/
theorem hidden_family {E : ResolvedEnv} {f : Nat} {ls : List Level}
    (hf : transparentBody E f ls = none) :
    Telescope E 3 (.letE (.sort (.succ .zero)) (.sort .zero) (.const f ls))
      [] (.const f ls) := by
  exact Telescope.prepend_zeta
    (Telescope.literal hf [] [] (fuel := 2) (Nat.le_refl 2))

theorem hidden_family_ne {f : Nat} {ls : List Level} :
    (.letE (.sort (.succ .zero)) (.sort .zero) (.const f ls) : Expr Nat) ≠
      .const f ls := by
  intro h
  cases h

/-- A trace of the actual source at the cache's fuel determines the cache's
output by the original reader's functionality. -/
theorem fieldTrace_of_telescope {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {A : Expr Nat} {s : FieldShape} {ds : List (Expr Nat)} {b : Expr Nat}
    (q : EvalPlan.Field E fuel f nu np ni prior A s)
    (ht : Telescope E fuel A ds b) : FieldTrace q := by
  cases q with
  | plain => exact True.intro
  | recursive r =>
      have he := Option.some.inj (ht.read.symm.trans r.read)
      have hd : ds = r.domains := congrArg Prod.fst he
      have hb : b = foldApps (.const f (canonL nu)) r.arguments :=
        congrArg Prod.snd he
      rw [hd, hb] at ht
      exact ht

/-- The original positivity reader accepts this hidden source as a direct
recursive field. This is a field-level admission fact, not a group fixture. -/
theorem hidden_field_analyzed {E : ResolvedEnv} {f nu : Nat}
    (hf : transparentBody E f (canonL nu) = none) :
    fieldAnalyze E 4 f nu 0 0 0
      (.letE (.sort (.succ .zero)) (.sort .zero) (.const f (canonL nu))) =
      .permitted (.recursive 0) [] := by
  have hr := (hidden_family hf).read
  -- Use only definitional reduction and explicit equalities here: even
  -- simp-only unfolding materializes imported matcher splitters.
  have hff : decide (f = f) = true := decide_eq_true rfl
  have hls : decide (canonL nu = (List.range nu).map Level.param) = true :=
    decide_eq_true rfl
  have hp : properFamilyFuel E 3 f nu 0 0
      (([] : List (Expr Nat)).length + 0 - 1) (.const f (canonL nu)) =
      some true := by
    change (if (decide (f = f) && true && true &&
        decide (canonL nu = (List.range nu).map Level.param)) = true
      then some true else some false) = some true
    rw [hff, hls]
    rfl
  unfold fieldAnalyze
  dsimp only
  rw [hr]
  dsimp only [domainsContainFuel]
  rw [hp] <;> rfl

/-- The certificate attaches to the actual cache produced by that
successful original field admission; its fuel is the unchanged 4. -/
theorem hidden_field_cached {E : ResolvedEnv} {f nu : Nat}
    (hf : transparentBody E f (canonL nu) = none) :
    FieldTrace (EvalPlan.of_admitted (prior := 0) (hidden_field_analyzed hf)) := by
  exact fieldTrace_of_telescope _ (hidden_family hf).raise

/-- A cached recursive field already equal to its source admits the
certificate at exactly the cache's original successful reader fuel. -/
theorem fieldTrace_of_eq {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {A : Expr Nat} {s : FieldShape}
    (q : EvalPlan.Field E fuel f nu np ni prior A s)
    (hf : transparentBody E f (canonL nu) = none)
    (he : fieldExpr f (canonL nu) (EvalPlanNormal.fieldSpec q) = A) :
    FieldTrace q := by
  cases q with
  | plain => exact True.intro
  | recursive r =>
      have hfu := piTelescopeFuel_some_lower E fuel r.read
      have ht := Telescope.literal hf r.domains r.arguments hfu
      change policyPi r.domains (foldApps (.const f (canonL nu)) r.arguments) = A at he
      rw [he] at ht
      exact ht

theorem fieldsTrace_of_eq {E : ResolvedEnv} {fuel f nu np ni prior : Nat}
    {ss : List FieldShape} {Fs : List (Expr Nat)}
    (q : EvalPlan.Fields E fuel f nu np ni prior ss Fs)
    (hf : transparentBody E f (canonL nu) = none)
    (he : (EvalPlanNormal.specs q).map (fieldExpr f (canonL nu)) = Fs) :
    FieldsTrace q := by
  revert he
  induction q with
  | nil => intro _; exact True.intro
  | @cons prior s A ss Fs head tail ih =>
      intro he
      change fieldExpr f (canonL nu) (EvalPlanNormal.fieldSpec head) ::
        (EvalPlanNormal.specs tail).map (fieldExpr f (canonL nu)) = A :: Fs at he
      obtain ⟨hh, ht⟩ := List.cons.inj he
      exact ⟨fieldTrace_of_eq head hf hh, ih ht⟩

/-- The family head is bodyless in the actual admitted reader environment;
cached/source equality therefore produces all trace certificates. -/
theorem cached_of_source_eq (p : EvalPlan.Plan)
    (he : ∀ j : Fin p.node.a.constructors.length,
      EvalPlanNormal.fields p j = (p.node.a.constructorViews j).fields) : Cached p := by
  have hf : transparentBody p.node.E0 p.node.a.family.ref
      (canonL p.node.a.family.member.arity) = none := by
    simp only [transparentBody, p.node.a.family.present]
    rw [p.node.a.family.hasClass]
    rfl
  intro j
  exact fieldsTrace_of_eq (p.constructors j).fields hf (he j)

end Rcic.F3.PSet.ReaderNoBeta

#print axioms Rcic.F3.PSet.ReaderNoBeta.Telescope.literal
#print axioms Rcic.F3.PSet.ReaderNoBeta.hidden_family
#print axioms Rcic.F3.PSet.ReaderNoBeta.cached_of_source_eq
