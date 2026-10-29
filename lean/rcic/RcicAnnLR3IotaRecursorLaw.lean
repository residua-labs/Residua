import rcic.RcicAnnLR3IotaNativeRecursor
import rcic.RcicAnnIota

/-!
# The source recursor interpreted in EnvironmentEval: forward ι computation

`iotaHook E` is a closed native family hook built from the actual environment:

* a constructor `c` is `ctorN c n` with `n` its normalized telescope count — the
  Π-count that the source ι (`iotaReductA`) requires of a constructor major;
* a recursor `r` is the fixed point `yN (genN np nm ni comps)`, where the header
  `(np, nm, ni)` is read exactly as `iotaGroupA` reads it (`recHeader_of_group`),
  and component `c` of the selector is the case of constructor `c` *computed from
  `iotaGroupA E r c` itself*: the field shapes of `ctorShapesA`, the minor at the
  constructor index, a recursive call after every directly recursive field.

`denote_iota` is the forward source ι law for every EnvironmentEval view/hook
pair that routes constructors and recursors of `E` to this hook (`Routes`): at
`iotaFnA E lhs = some rhs` the two raw images are equal, for every valuation and
every raw local environment. It needs no typing, admission or Fundamental premise;
its only side condition is `FirstOrderArity E`: every recursive field read by the
source ι is a direct one whose family application carries exactly the recursor's
index count. This is the first-order recursive class (non-recursive and directly
recursive fields, any parameters, indices and constructors). Function-recursive
fields are *not* covered by this module; they need the evaluator lifting law and
are a separate carrier.

`routes_plain` supplies `Routes` for `EnvironmentEval.denote E (iotaHook E)`.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.IotaRecursor

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER
open EnvironmentEval (FamilySyntax definitionBody rigidTerm denote_rigid denote_application denote_bot)

/-! ## Reading the source ι -/

/-- The constructor type the source ι reads. -/
def ctorTypeOf (g : IotaGroupA) : ExprA := g.ctorM.normA.getD g.ctorM.mtypeA

theorem iotaReductA_inv {s : RecSpineA} {g : IotaGroupA} {e' : ExprA}
    (h : iotaReductA s g = some e') :
    ∃ (c : Nat) (shapes : List FieldShape) (minor ctorAfter : ExprA),
      spineHeadRefA s.major = some c ∧ c = g.ctorRef ∧
      s.preMajor.length + 1 = piCountA g.recM.mtypeA ∧
      (appsSpineA s.major).2.length = piCountA (ctorTypeOf g) ∧
      ctorShapesA g.familyRef g.nparams (ctorTypeOf g) = some shapes ∧
      s.preMajor[g.nparams + 1 + g.ctorIdx]? = some minor ∧
      applyTelA (s.preMajor.take g.nparams)
        (instantiateLevelsA (s.ls.take g.ctorM.arity) (ctorTypeOf g)) = some ctorAfter ∧
      fieldsTelA ((appsSpineA s.major).2.drop g.nparams) shapes ctorAfter = true ∧
      e' = foldAppsA minor (rhsArgsA (.const s.recRef s.ls) s.preMajor g.nparams g.nMinors
        ((appsSpineA s.major).2.drop g.nparams) shapes ctorAfter) := by
  unfold iotaReductA at h
  cases hc : spineHeadRefA s.major with
  | none => rw [hc, Option.none_bind] at h; exact Option.noConfusion h
  | some c =>
      simp only [hc, Option.some_bind] at h
      split at h
      · rename_i hcond
        simp only [Option.bind_eq_some] at h
        obtain ⟨shapes, hshapes, minor, hminor, ctorAfter, htel, h⟩ := h
        split at h
        · rename_i hft
          injection h with h
          exact ⟨c, shapes, minor, ctorAfter, rfl, hcond.1, hcond.2.1, hcond.2.2.2.1, hshapes,
            hminor, htel, hft, h.symm⟩
        · exact Option.noConfusion h
      · exact Option.noConfusion h

/-- The recursor header `(nparams, nMinors, nindices)`, read from the recursor
alone exactly as `iotaGroupA` reads it. -/
def recHeader (E : ResolvedEnvA) (recRef : Nat) : Option (Nat × Nat × Nat) :=
  match E.members recRef with
  | some recM =>
      match (piDomsA recM.mtypeA).getLast? with
      | some D =>
          match (appsSpineA D).1 with
          | .const familyRef _ =>
              match E.members familyRef with
              | some famM =>
                  (groupCountsA recM famM (recRef - familyRef - 1)).map
                    (fun p => (p.1, recRef - familyRef - 1, p.2))
              | none => none
          | _ => none
      | none => none
  | none => none

theorem recHeader_of_group {E : ResolvedEnvA} {recRef ctorRef : Nat} {g : IotaGroupA}
    (h : iotaGroupA E recRef ctorRef = some g) :
    recHeader E recRef = some (g.nparams, g.nMinors, g.nindices) := by
  unfold iotaGroupA at h
  split at h
  · rename_i recM ctorM hrec hctor
    split at h
    · rename_i hcls
      split at h
      · rename_i D hD
        split at h
        · rename_i familyRef lsF hhead
          split at h
          · rename_i famM hfam
            split at h
            · rename_i hlay
              split at h
              · rename_i nparams nindices hcnt
                injection h with h
                subst h
                simp only [recHeader, hrec, hD, hhead, hfam, hcnt, Option.map_some']
              · exact Option.noConfusion h
            · exact Option.noConfusion h
          · exact Option.noConfusion h
        · exact Option.noConfusion h
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  · exact Option.noConfusion h

theorem fieldsTelA_length : ∀ (fs : List ExprA) (ss : List FieldShape) (T : ExprA),
    fieldsTelA fs ss T = true → fs.length = ss.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [fieldsTelA] at h
  | _ :: _, [], _, h => by simp [fieldsTelA] at h
  | f :: fs, s :: ss, .pi A _ B _, h => by
      simp only [fieldsTelA, Bool.and_eq_true] at h
      simp [fieldsTelA_length fs ss _ h.2]
  | _ :: _, _ :: _, .bvar _, h => by simp [fieldsTelA] at h
  | _ :: _, _ :: _, .sort _, h => by simp [fieldsTelA] at h
  | _ :: _, _ :: _, .const _ _, h => by simp [fieldsTelA] at h
  | _ :: _, _ :: _, .app _ _, h => by simp [fieldsTelA] at h
  | _ :: _, _ :: _, .lam _ _ _, h => by simp [fieldsTelA] at h
  | _ :: _, _ :: _, .letE _ _ _, h => by simp [fieldsTelA] at h
  | _ :: _, _ :: _, .lit _, h => by simp [fieldsTelA] at h

/-! ## The case and recursor terms -/

/-- A recursive call from a case body under `d` further binders: `self` applied to
dummy parameters and motive, all minors, dummy indices and the given major. -/
def recCallN (np nm ni k d : Nat) (major : Expr Nat) : Expr Nat :=
  foldApps (.bvar (d + k + nm + 1))
    (List.replicate (np + 1) dummy ++ argVars (d + k + 1) nm ++ List.replicate ni dummy ++
      [major])

/-- What follows field variable `p` in a case body, by its shape. -/
def shapeCallN (np nm ni k p : Nat) : FieldShape → List (Expr Nat)
  | .nonrecursive => []
  | .recursive 0 => [recCallN np nm ni k 0 (.bvar p)]
  | .recursive (a + 1) =>
      [lams (a + 1) (recCallN np nm ni k (a + 1)
        (foldApps (.bvar (a + 1 + p)) (argVars 0 (a + 1))))]

/-- The minor's arguments from field `i` on. -/
def caseArgsN (np nm ni k : Nat) : Nat → List FieldShape → List (Expr Nat)
  | _, [] => []
  | i, s :: ss => .bvar (k - 1 - i) ::
      (shapeCallN np nm ni k (k - 1 - i) s ++ caseArgsN np nm ni k (i + 1) ss)

/-- The case of constructor index `j`: `dcount` dropped arguments, then the fields. -/
def caseN (np nm ni j dcount : Nat) (shapes : List FieldShape) : Expr Nat :=
  drops dcount (lams shapes.length
    (foldApps (.bvar (shapes.length + nm - j)) (caseArgsN np nm ni shapes.length 0 shapes)))

/-- Selector component `c` of recursor `recRef`: the case computed from the source
group of `(recRef, c)`, or a dummy where the source ι never fires. -/
def compN (E : ResolvedEnvA) (recRef np nm ni c : Nat) : Expr Nat :=
  match iotaGroupA E recRef c with
  | some g =>
      match ctorShapesA g.familyRef g.nparams (ctorTypeOf g) with
      | some shapes => caseN np nm ni g.ctorIdx (piCountA (ctorTypeOf g) - shapes.length) shapes
      | none => dummy
  | none => dummy

def compsN (E : ResolvedEnvA) (recRef np nm ni : Nat) : List (Expr Nat) :=
  (List.range recRef).map (compN E recRef np nm ni)

def recTermN (E : ResolvedEnvA) (recRef : Nat) : Expr Nat :=
  match recHeader E recRef with
  | some (np, nm, ni) => .app yN (genN np nm ni (compsN E recRef np nm ni))
  | none => .const recRef []

/-- The native term of a member: constructors and recursors as above, all other
members (and families) neutral. -/
def iotaTerm (E : ResolvedEnvA) (r : Nat) : Expr Nat :=
  match E.members r with
  | some m =>
      match m.mclass with
      | .constructorM => ctorN r (piCountA (m.normA.getD m.mtypeA))
      | .recursorM => recTermN E r
      | _ => .const r []
  | none => .const r []

/-- The recursor family hook; it reads only the source environment and the reference. -/
def iotaHook (E : ResolvedEnvA) : FamilySyntax := fun _ r _ _ => iotaTerm E r

/-- A view/hook pair routes the constructors and recursors of `E` to `iotaTerm`. -/
def Routes (E V : ResolvedEnvA) (H : FamilySyntax) : Prop :=
  ∀ (ν : Valuation) (ρ : EnvI) (r : Nat) (ls : List Level) (m : CheckedMemberA),
    E.members r = some m → (m.mclass = .constructorM ∨ m.mclass = .recursorM) →
      EnvironmentEval.denote V H ν ρ (.const r ls) = denI ρ (iotaTerm E r)

theorem routes_plain (E : ResolvedEnvA) : Routes E E (iotaHook E) := by
  intro ν ρ r ls m hm hc
  have hbody : definitionBody E r ls = none := by
    rcases hc with hc | hc <;> simp [definitionBody, hm, hc, transparent]
  have hrigid : rigidTerm E (iotaHook E) ν r ls = iotaTerm E r := by
    rcases hc with hc | hc <;> simp [rigidTerm, hm, hc, iotaHook]
  rw [NeutralCodes.valueEq_eq (denote_rigid hbody (iotaHook E) ν ρ), hrigid]

/-! ## Source images as iterated applications -/

theorem denote_foldAppsA (V : ResolvedEnvA) (H : FamilySyntax) (ν : Valuation) (ρ : EnvI) :
    ∀ (h : ExprA) (xs : List ExprA),
      EnvironmentEval.denote V H ν ρ (foldAppsA h xs) =
        applyAll (EnvironmentEval.denote V H ν ρ h) (xs.map (EnvironmentEval.denote V H ν ρ))
  | h, [] => rfl
  | h, x :: xs => by
      show EnvironmentEval.denote V H ν ρ (foldAppsA (.app h x) xs) = _
      rw [denote_foldAppsA V H ν ρ (.app h x) xs,
        NeutralCodes.valueEq_eq (denote_application V H ν ρ h x)]
      rfl

/-! ## The first-order arity side condition -/

/-- Arity of a field read by the source ι: a direct recursive field's family
application carries exactly `ni` indices; function-recursive fields are outside
the first-order class. -/
def firstOrderShapeA (np ni : Nat) (A : ExprA) : FieldShape → Prop
  | .nonrecursive => True
  | .recursive 0 => (familyIdxA np A).length = ni
  | .recursive (_ + 1) => False

/-- The arity condition along the source ι's field walk. -/
def FirstOrderWalkA (np ni : Nat) : List ExprA → List FieldShape → ExprA → Prop
  | f :: fs, s :: ss, .pi A _ B _ =>
      firstOrderShapeA np ni A s ∧ FirstOrderWalkA np ni fs ss (instantiate0A f B)
  | _, _, _ => True

/-- Every field walk the source ι can accept is first-order and index-exact. -/
def FirstOrderArity (E : ResolvedEnvA) : Prop :=
  ∀ (recRef c : Nat) (g : IotaGroupA) (shapes : List FieldShape) (pre : List ExprA)
    (ls : List Level) (args : List ExprA) (ctorAfter : ExprA),
    iotaGroupA E recRef c = some g →
    ctorShapesA g.familyRef g.nparams (ctorTypeOf g) = some shapes →
    applyTelA (pre.take g.nparams)
      (instantiateLevelsA (ls.take g.ctorM.arity) (ctorTypeOf g)) = some ctorAfter →
    fieldsTelA (args.drop g.nparams) shapes ctorAfter = true →
    FirstOrderWalkA g.nparams g.nindices (args.drop g.nparams) shapes ctorAfter

/-! ## The case computation -/

section Case

variable (np nm ni : Nat) (comps : List (Expr Nat)) (ρ : EnvI) (ms : List Value) (maj : Value)

/-- A recursive call from a case body computes the recursor body at the same
minors and the call's major. -/
theorem recCallN_denI (hms : ms.length = nm) (hmsb : ∀ x ∈ ms, x .bot)
    (fieldsV ys : List Value) (major : Expr Nat) :
    denI (pushAll ys (pushAll fieldsV (bodyEnv (fixValue (genN np nm ni comps) ρ) ρ ms maj)))
        (recCallN np nm ni fieldsV.length ys.length major) =
      bodyValue np nm ni comps ρ ms
        (denI (pushAll ys (pushAll fieldsV
          (bodyEnv (fixValue (genN np nm ni comps) ρ) ρ ms maj))) major) := by
  generalize hΘ : fixValue (genN np nm ni comps) ρ = Θ
  have henv : pushAll ys (pushAll fieldsV (bodyEnv Θ ρ ms maj)) =
      pushAll (([maj] ++ fieldsV) ++ ys) (pushAll ms (EnvI.cons Θ ρ)) := by
    rw [pushAll_append, pushAll_append]; rfl
  unfold recCallN
  rw [foldApps_denI, henv]
  have hself : pushAll (([maj] ++ fieldsV) ++ ys) (pushAll ms (EnvI.cons Θ ρ))
      (ys.length + fieldsV.length + nm + 1) = Θ := by
    rw [pushAll_ge _ _ _ (by simp; omega)]
    rw [show ys.length + fieldsV.length + nm + 1 - (([maj] ++ fieldsV) ++ ys).length = nm by
      simp; omega]
    rw [pushAll_ge _ _ _ (by omega), hms, Nat.sub_self]
    rfl
  have hselfb : pushAll (([maj] ++ fieldsV) ++ ys) (pushAll ms (EnvI.cons Θ ρ))
      (ys.length + fieldsV.length + nm + 1) .bot := by
    rw [hself, ← hΘ]; exact denI_bot _ _
  rw [denI_bvar hselfb, hself]
  have hvars := argVars_denI ms (EnvI.cons Θ ρ) (([maj] ++ fieldsV) ++ ys) hmsb
  have hlen : (([maj] ++ fieldsV) ++ ys).length = ys.length + fieldsV.length + 1 := by
    simp; omega
  rw [hlen, hms] at hvars
  simp only [List.map_append, List.map_replicate, hvars, List.map_cons, List.map_nil]
  rw [← hΘ]
  exact recN_apply_split np nm ni comps ρ _ ms _ (by simp) hms (by simp) _ (denI_bot _ _)

end Case

theorem drop_eq_drop_of_length {α : Type} (l : List α) (N np k : Nat) (hN : l.length = N)
    (hk : (l.drop np).length = k) : l.drop (N - k) = l.drop np := by
  by_cases h : np ≤ N
  · have : N - k = np := by simp at hk; omega
    rw [this]
  · have h1 : (l.drop np) = [] := List.drop_eq_nil_of_le (by omega)
    have hk0 : k = 0 := by rw [← hk, h1]; rfl
    rw [hk0, Nat.sub_zero, h1]
    exact List.drop_eq_nil_of_le (by omega)

/-- The minors seen by the recursor body: entries `np + 1 … np + nm` of the
pre-major images. -/
def minorsOf (d : ExprA → Value) (pre : List ExprA) (np nm : Nat) : List Value :=
  ((pre.map d).drop (np + 1)).take nm

theorem minorsOf_length (d : ExprA → Value) (pre : List ExprA) (np nm : Nat)
    (h : np + 1 + nm ≤ pre.length) : (minorsOf d pre np nm).length = nm := by
  simp [minorsOf]; omega

/-- `List.drop_take` without the classical dependency of the library proof. -/
theorem drop_take_eq {α : Type} : ∀ (m n : Nat) (l : List α),
    (l.take n).drop m = (l.drop m).take (n - m)
  | 0, n, l => by simp
  | m + 1, 0, l => by simp
  | m + 1, n + 1, [] => by simp
  | m + 1, n + 1, x :: xs => by
      simp only [List.take_succ_cons, List.drop_succ_cons]
      rw [drop_take_eq m n xs, Nat.add_sub_add_right]

theorem minorsOf_prefix (d : ExprA → Value) (pre idx : List ExprA) (np nm : Nat)
    (h : np + 1 + nm ≤ pre.length) :
    (((recPrefixA pre np nm ++ idx).map d).drop (np + 1)).take nm = minorsOf d pre np nm := by
  unfold recPrefixA minorsOf
  have hl : ((pre.take (np + 1 + nm)).map d).length = np + 1 + nm := by simp; omega
  rw [List.map_append, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega), List.map_take, drop_take_eq,
    List.take_take]
  congr 1
  omega

theorem minorsOf_getElem (d : ExprA → Value) (pre : List ExprA) (np nm j : Nat)
    (h : np + 1 + nm ≤ pre.length) (hj : j < nm) (minor : ExprA)
    (hminor : pre[np + 1 + j]? = some minor) :
    (minorsOf d pre np nm)[j]'(by rw [minorsOf_length d pre np nm h]; exact hj) = d minor := by
  unfold minorsOf
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map]
  have h1 : np + 1 + j < pre.length := by omega
  rw [List.getElem?_eq_getElem h1] at hminor
  injection hminor with hminor
  rw [← hminor]

theorem caseN_apply (np nm ni j : Nat) (shapes : List FieldShape) (σ : EnvI)
    (argsV : List Value) (dcount : Nat) (hlen : argsV.length = dcount + shapes.length) :
    applyAll (denI σ (caseN np nm ni j dcount shapes)) argsV =
      denI (pushAll (argsV.drop dcount) σ)
        (foldApps (.bvar (shapes.length + nm - j)) (caseArgsN np nm ni shapes.length 0 shapes)) := by
  unfold caseN
  conv => lhs; rw [← List.take_append_drop dcount argsV]
  rw [applyAll_append, drops_apply dcount _ σ _ (by simp; omega),
    lams_apply _ _ σ _ (by simp; omega)]

theorem minor_lookup (Θ : Value) (ρ : EnvI) (ms : List Value) (maj : Value)
    (fieldsV : List Value) (k nm j : Nat) (hk : fieldsV.length = k) (hnm : ms.length = nm)
    (hj : j < nm) (hb : (ms[j]'(by omega)) .bot) :
    denI (pushAll fieldsV (bodyEnv Θ ρ ms maj)) (.bvar (k + nm - j)) = ms[j]'(by omega) := by
  have henv : pushAll fieldsV (bodyEnv Θ ρ ms maj) =
      pushAll ([maj] ++ fieldsV) (pushAll ms (EnvI.cons Θ ρ)) := by
    rw [pushAll_append]; rfl
  have h := bvar_lookup_denI ms (EnvI.cons Θ ρ) ([maj] ++ fieldsV) j (by omega) hb
  rw [henv]
  have hidx : k + nm - j = ([maj] ++ fieldsV).length + (ms.length - 1 - j) := by
    simp; omega
  rw [hidx]
  exact h

theorem getElem?_of_drop_eq {α : Type} {l fs : List α} {i : Nat} {f : α}
    (h : f :: fs = l.drop i) : l[i]? = some f := by
  have h0 : (l.drop i)[0]? = some f := by rw [← h]; simp
  rw [List.getElem?_drop, Nat.add_zero] at h0
  exact h0

theorem drop_succ_of_drop_eq {α : Type} {l fs : List α} {i : Nat} {f : α}
    (h : f :: fs = l.drop i) : fs = l.drop (i + 1) := by
  rw [← List.drop_drop, ← h]
  rfl

/-- The case's argument list computes the source ι right-hand side's argument
list, along the first-order field walk. -/
theorem walk_firstOrder (V : ResolvedEnvA) (H : FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (np nm ni : Nat) (comps : List (Expr Nat)) (recRef : Nat) (ls : List Level)
    (hrec : EnvironmentEval.denote V H ν ρ (.const recRef ls) = fixValue (genN np nm ni comps) ρ)
    (pre : List ExprA) (hpre : np + 1 + nm ≤ pre.length) (maj : Value) (fields : List ExprA) :
    ∀ (fs : List ExprA) (i : Nat) (ss : List FieldShape) (T : ExprA),
      fs = fields.drop i → fieldsTelA fs ss T = true → FirstOrderWalkA np ni fs ss T →
      (caseArgsN np nm ni fields.length i ss).map
          (denI (pushAll (fields.map (EnvironmentEval.denote V H ν ρ))
            (bodyEnv (fixValue (genN np nm ni comps) ρ) ρ
              (minorsOf (EnvironmentEval.denote V H ν ρ) pre np nm) maj))) =
        (rhsArgsA (.const recRef ls) pre np nm fs ss T).map (EnvironmentEval.denote V H ν ρ) := by
  intro fs
  induction fs with
  | nil =>
      intro i ss T _ hft _
      cases ss with
      | nil => rfl
      | cons s ss => simp [fieldsTelA] at hft
  | cons f fs ih =>
      intro i ss T hfs hft hwalk
      cases ss with
      | nil => simp [fieldsTelA] at hft
      | cons s ss =>
          cases T with
          | pi A u B v =>
              simp only [fieldsTelA, Bool.and_eq_true] at hft
              obtain ⟨hshape, hwalk'⟩ := hwalk
              have hfs' := drop_succ_of_drop_eq hfs
              have hfi := getElem?_of_drop_eq hfs
              have hi : i < fields.length := by
                rcases Nat.lt_or_ge i fields.length with hi | hi
                · exact hi
                · rw [List.getElem?_eq_none hi] at hfi
                  exact Option.noConfusion hfi
              show (Expr.bvar (fields.length - 1 - i) ::
                    (shapeCallN np nm ni fields.length (fields.length - 1 - i) s ++
                      caseArgsN np nm ni fields.length (i + 1) ss)).map _ =
                  (f :: (recCallsA (.const recRef ls) pre np nm f A s ++
                    rhsArgsA (.const recRef ls) pre np nm fs ss (instantiate0A f B))).map _
              rw [List.map_cons, List.map_cons, List.map_append, List.map_append,
                ih (i + 1) ss (instantiate0A f B) hfs' hft.2 hwalk']
              have hfv : (fields.map (EnvironmentEval.denote V H ν ρ))[i]'(by simp; exact hi) =
                  EnvironmentEval.denote V H ν ρ f := by
                rw [List.getElem_map]
                rw [List.getElem?_eq_getElem hi] at hfi
                injection hfi with hfi
                rw [hfi]
              have hhead : denI (pushAll (fields.map (EnvironmentEval.denote V H ν ρ))
                  (bodyEnv (fixValue (genN np nm ni comps) ρ) ρ
                    (minorsOf (EnvironmentEval.denote V H ν ρ) pre np nm) maj))
                  (.bvar (fields.length - 1 - i)) = EnvironmentEval.denote V H ν ρ f := by
                have h := bvar_lookup_denI (fields.map (EnvironmentEval.denote V H ν ρ))
                  (bodyEnv (fixValue (genN np nm ni comps) ρ) ρ
                    (minorsOf (EnvironmentEval.denote V H ν ρ) pre np nm) maj) [] i
                  (by simp; exact hi) (by rw [hfv]; exact denote_bot _ _ _ _ _)
                simp only [pushAll, List.length_nil, List.length_map, Nat.zero_add] at h
                rw [h, ← hfv]
              rw [hhead]
              congr 1
              congr 1
              cases s with
              | nonrecursive => rfl
              | recursive n =>
                  cases n with
                  | zero =>
                      have hms := minorsOf_length (EnvironmentEval.denote V H ν ρ) pre np nm hpre
                      have hmsb : ∀ x ∈ minorsOf (EnvironmentEval.denote V H ν ρ) pre np nm,
                          x .bot := by
                        intro x hx
                        unfold minorsOf at hx
                        obtain ⟨e, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop
                          (List.mem_of_mem_take hx))
                        exact denote_bot _ _ _ _ _
                      have h := recCallN_denI np nm ni comps ρ
                        (minorsOf (EnvironmentEval.denote V H ν ρ) pre np nm) maj hms hmsb
                        (fields.map (EnvironmentEval.denote V H ν ρ)) []
                        (.bvar (fields.length - 1 - i))
                      simp only [pushAll, List.length_nil, List.length_map] at h
                      show [denI _ (recCallN np nm ni fields.length 0
                          (.bvar (fields.length - 1 - i)))] =
                        [EnvironmentEval.denote V H ν ρ
                          (recCallFieldA (.const recRef ls) pre np nm f A)]
                      rw [h, hhead]
                      unfold recCallFieldA
                      rw [denote_foldAppsA, hrec, List.map_append, List.map_singleton]
                      have hidx : (familyIdxA np A).length = ni := hshape
                      have hl : ((recPrefixA pre np nm ++ familyIdxA np A).map
                          (EnvironmentEval.denote V H ν ρ)).length = np + 1 + nm + ni := by
                        simp [recPrefixA, hidx]; omega
                      rw [recN_apply np nm ni comps ρ _ hl _ (denote_bot _ _ _ _ _),
                        minorsOf_prefix _ pre _ np nm hpre]
                  | succ a => exact absurd hshape id
          | _ => simp [fieldsTelA] at hft

/-- The case argument list of a constructor computes the source ι right-hand side's
argument list (the walk property consumed by `denote_iota_core`). -/
def WalkOK (V : ResolvedEnvA) (H : FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (np nm ni : Nat) (comps : List (Expr Nat)) (recRef : Nat) (ls : List Level)
    (pre : List ExprA) (maj : Value) (fields : List ExprA) (shapes : List FieldShape)
    (T : ExprA) : Prop :=
  (caseArgsN np nm ni fields.length 0 shapes).map
      (denI (pushAll (fields.map (EnvironmentEval.denote V H ν ρ))
        (bodyEnv (fixValue (genN np nm ni comps) ρ) ρ
          (minorsOf (EnvironmentEval.denote V H ν ρ) pre np nm) maj))) =
    (rhsArgsA (.const recRef ls) pre np nm fields shapes T).map (EnvironmentEval.denote V H ν ρ)

/-- The walk property at the actual layers of a redex. -/
def RedexWalkOK (E V : ResolvedEnvA) (H : FamilySyntax) (ν : Valuation) (ρ : EnvI)
    (lhs : ExprA) : Prop :=
  ∀ (s : RecSpineA) (c : Nat) (g : IotaGroupA) (shapes : List FieldShape) (ctorAfter : ExprA),
    recSpineA lhs = some s → spineHeadRefA s.major = some c → iotaGroupA E s.recRef c = some g →
    s.preMajor.length + 1 = piCountA g.recM.mtypeA →
    ctorShapesA g.familyRef g.nparams (ctorTypeOf g) = some shapes →
    applyTelA (s.preMajor.take g.nparams)
      (instantiateLevelsA (s.ls.take g.ctorM.arity) (ctorTypeOf g)) = some ctorAfter →
    fieldsTelA ((appsSpineA s.major).2.drop g.nparams) shapes ctorAfter = true →
    WalkOK V H ν ρ g.nparams g.nMinors g.nindices
      (compsN E s.recRef g.nparams g.nMinors g.nindices) s.recRef s.ls s.preMajor
      (EnvironmentEval.denote V H ν ρ s.major) ((appsSpineA s.major).2.drop g.nparams) shapes
      ctorAfter

/-- The recursor's image is the fixed point, at every raw local environment. -/
theorem recursor_value {E V : ResolvedEnvA} {H : FamilySyntax} (hroute : Routes E V H)
    {recRef c : Nat} {g : IotaGroupA} (hg : iotaGroupA E recRef c = some g)
    (ν : Valuation) (ρ : EnvI) (ls : List Level) :
    EnvironmentEval.denote V H ν ρ (.const recRef ls) =
      fixValue (genN g.nparams g.nMinors g.nindices
        (compsN E recRef g.nparams g.nMinors g.nindices)) ρ := by
  obtain ⟨hrecM, hrecC, _⟩ := iotaGroupA_some hg
  rw [hroute ν ρ recRef ls g.recM hrecM (Or.inr hrecC)]
  simp only [iotaTerm, hrecM, hrecC, recTermN, recHeader_of_group hg]
  exact fix_denI _ _

/-- **The forward source ι computation** for every view/hook pair routing to
`iotaTerm`, given the walk property at the redex. -/
theorem denote_iota_core {E V : ResolvedEnvA} {H : FamilySyntax} (hroute : Routes E V H)
    {lhs rhs : ExprA} (h : iotaFnA E lhs = some rhs) (ν : Valuation) (ρ : EnvI)
    (hW : RedexWalkOK E V H ν ρ lhs) :
    EnvironmentEval.denote V H ν ρ lhs = EnvironmentEval.denote V H ν ρ rhs := by
  obtain ⟨s, c, g, hs, hc, hg, hred⟩ := iotaFnA_some h
  obtain ⟨c', shapes, minor, ctorAfter, hc', _, hplen, hargs, hshapes, hminor, htel, hft, hrhs⟩ :=
    iotaReductA_inv hred
  rw [hc] at hc'
  injection hc' with hcc
  subst hcc
  obtain ⟨hrecM, hrecC, hctorM, hctorC, _, _, _, hfc, hcr, hnm, hidx, hcount, _⟩ :=
    iotaGroupA_some hg
  have hhead := recHeader_of_group hg
  have hwalk := hW s c g shapes ctorAfter hs hc hg hplen hshapes htel hft
  have hlhs : lhs = foldAppsA (.const s.recRef s.ls) (s.preMajor ++ [s.major]) := by
    rw [← foldAppsA_appsSpineA lhs, recSpineA_some hs]
  obtain ⟨lsC, hmh⟩ := spineHeadRefA_some hc
  have hmaj : s.major = foldAppsA (.const c lsC) (appsSpineA s.major).2 := by
    rw [← hmh, foldAppsA_appsSpineA]
  generalize (appsSpineA s.major).2 = args at hargs hft hrhs hmaj hwalk
  -- the native values of the recursor and the constructor
  have hR : EnvironmentEval.denote V H ν ρ (.const s.recRef s.ls) =
      fixValue (genN g.nparams g.nMinors g.nindices
        (compsN E s.recRef g.nparams g.nMinors g.nindices)) ρ := by
    rw [hroute ν ρ s.recRef s.ls g.recM hrecM (Or.inr hrecC)]
    simp only [iotaTerm, hrecM, hrecC, recTermN, hhead]
    exact fix_denI _ _
  have hC : EnvironmentEval.denote V H ν ρ (.const c lsC) =
      denI ρ (ctorN c (piCountA (ctorTypeOf g))) := by
    rw [hroute ν ρ c lsC g.ctorM hctorM (Or.inl hctorC)]
    simp only [iotaTerm, hctorM, hctorC, ctorTypeOf]
  -- arithmetic
  have hpre : s.preMajor.length = g.nparams + 1 + g.nMinors + g.nindices := by omega
  have hk : (args.drop g.nparams).length = shapes.length :=
    fieldsTelA_length _ _ _ hft
  have hj : g.ctorIdx < g.nMinors := by omega
  have hcomps : c < (compsN E s.recRef g.nparams g.nMinors g.nindices).length := by
    simp [compsN]; exact hcr
  have hcomp : (compsN E s.recRef g.nparams g.nMinors g.nindices)[c]'hcomps =
      caseN g.nparams g.nMinors g.nindices g.ctorIdx
        (piCountA (ctorTypeOf g) - shapes.length) shapes := by
    simp only [compsN, List.getElem_map, List.getElem_range]
    simp only [compN, hg, hshapes]
  -- the abbreviations
  unfold WalkOK at hwalk
  generalize hd : EnvironmentEval.denote V H ν ρ = d at hR hC hwalk
  generalize hcs : compsN E s.recRef g.nparams g.nMinors g.nindices = comps at hR hcomps hcomp hwalk
  have hdb : ∀ e, d e .bot := by intro e; rw [← hd]; exact denote_bot _ _ _ _ _
  have hfold : ∀ (h : ExprA) (xs : List ExprA), d (foldAppsA h xs) = applyAll (d h) (xs.map d) := by
    rw [← hd]; exact denote_foldAppsA V H ν ρ
  have hargsV : (args.map d).length = piCountA (ctorTypeOf g) := by simp; exact hargs
  have hmsb : ∀ x ∈ minorsOf d s.preMajor g.nparams g.nMinors, x .bot := by
    intro x hx
    unfold minorsOf at hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    exact hdb e
  have hms := minorsOf_length d s.preMajor g.nparams g.nMinors (by omega)
  have hargsb : ∀ x ∈ args.map d, x .bot := by
    intro x hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    exact hdb e
  have hmajV : d s.major = applyAll (denI ρ (ctorN c (args.map d).length)) (args.map d) := by
    rw [hmaj, hfold, hC, hargsV]
  have hlenC : (args.map d).length = (piCountA (ctorTypeOf g) - shapes.length) + shapes.length := by
    have h1 : args.length - g.nparams = shapes.length := by rw [← List.length_drop]; exact hk
    rw [hargsV]; omega
  -- left-hand side
  have hL : d lhs =
      applyAll ((minorsOf d s.preMajor g.nparams g.nMinors)[g.ctorIdx]'(by rw [hms]; exact hj))
        ((caseArgsN g.nparams g.nMinors g.nindices shapes.length 0 shapes).map
          (denI (pushAll ((args.drop g.nparams).map d)
            (bodyEnv (fixValue (genN g.nparams g.nMinors g.nindices comps) ρ) ρ
              (minorsOf d s.preMajor g.nparams g.nMinors) (d s.major))))) := by
    rw [hlhs, hfold, hR, List.map_append, List.map_singleton,
      recN_apply _ _ _ comps ρ _ (by simp; exact hpre) _ (hdb _)]
    unfold bodyValue
    conv => lhs; arg 1; rw [hmajV]
    rw [ctorN_apply c ρ (args.map d) hargsb _ comps hcomps, hcomp,
      caseN_apply g.nparams g.nMinors g.nindices g.ctorIdx shapes _ (args.map d)
        (piCountA (ctorTypeOf g) - shapes.length) hlenC,
      foldApps_denI]
    have hdrop : (args.map d).drop (piCountA (ctorTypeOf g) - shapes.length) =
        (args.drop g.nparams).map d := by
      rw [← List.map_drop,
        drop_eq_drop_of_length args (piCountA (ctorTypeOf g)) g.nparams shapes.length hargs hk]
    rw [hdrop]
    have hlen' : ((args.drop g.nparams).map d).length = shapes.length := by simp at hk ⊢; omega
    have hlook := minor_lookup (fixValue (genN g.nparams g.nMinors g.nindices comps) ρ) ρ
      (minorsOf d s.preMajor g.nparams g.nMinors) (d s.major) ((args.drop g.nparams).map d)
      shapes.length g.nMinors g.ctorIdx hlen' hms hj (hmsb _ (List.getElem_mem _))
    change applyAll (denI (pushAll ((args.drop g.nparams).map d)
        (bodyEnv (fixValue (genN g.nparams g.nMinors g.nindices comps) ρ) ρ
          (minorsOf d s.preMajor g.nparams g.nMinors) (d s.major)))
        (.bvar (shapes.length + g.nMinors - g.ctorIdx))) _ = _
    rw [hlook]
    rfl
  -- right-hand side
  have hRr : d rhs =
      applyAll (d minor) ((rhsArgsA (.const s.recRef s.ls) s.preMajor g.nparams g.nMinors
        (args.drop g.nparams) shapes ctorAfter).map d) := by
    rw [hrhs, hfold]
  rw [hL, hRr, minorsOf_getElem d s.preMajor g.nparams g.nMinors g.ctorIdx (by omega) hj minor
    hminor]
  rw [← hk, hwalk]

/-- **The forward source ι law** on the first-order recursive class: no typing,
admission or Fundamental premise. -/
theorem denote_iota {E V : ResolvedEnvA} {H : FamilySyntax} (hroute : Routes E V H)
    (harity : FirstOrderArity E) {lhs rhs : ExprA} (h : iotaFnA E lhs = some rhs)
    (ν : Valuation) (ρ : EnvI) :
    EnvironmentEval.denote V H ν ρ lhs = EnvironmentEval.denote V H ν ρ rhs := by
  apply denote_iota_core hroute h ν ρ
  intro s c g shapes ctorAfter _ _ hg hplen hshapes htel hft
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcount, _⟩ := iotaGroupA_some hg
  exact walk_firstOrder V H ν ρ g.nparams g.nMinors g.nindices _ s.recRef s.ls
    (recursor_value hroute hg ν ρ s.ls) s.preMajor (by omega) _
    ((appsSpineA s.major).2.drop g.nparams) _ 0 shapes ctorAfter (by simp) hft
    (harity s.recRef c g shapes s.preMajor s.ls (appsSpineA s.major).2 ctorAfter hg hshapes htel hft)

end Rcic.Declarative.Ann.LR3.IotaRecursor
