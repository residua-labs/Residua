import rcic.RcicIotaSRRowsLemmas
import rcic.RcicIotaSRRowsTel
import rcic.RcicIotaWitnessTypedClosed
import rcic.RcicIARecIH
import rcic.RcicDT0709EnvWf
import rcic.RcicTypedValidity

/-!
# DT-019 S1 — the constructor side of the direct ι-SR route

The ι redex applies the recursor at `w.ls` to a major `ctor_{lsC} cp fs`; the
admission equation is stated at the recursor's universes over the recursor's
own parameters. Three gaps separate the two readings of the constructor
telescope: the universe lists (`lsC` versus the family prefix of `ls`, `=ₙ` by
ROW 3), the parameters (`cp` versus the recursor's `p`, pointwise convertible
by ROW 3), and the constructor's own parameter domains versus the family's
(the admission mirror `CtorTypedT`). This module closes them, delivering:

* every field typed at the recursor-side instantiation of its stored domain;
* the major convertible to the recursor-side constructor application at the
  major domain;
* every index of the redex convertible to the equation's result index.

Everything rides the generic transports of `RcicIotaSRRowsLemmas` (level
instantiation, relocation, same-argument `instPrefix`), the Π row (spine
inversion) and ROW 3 (`famAppRow`) — the two rows DT-010 already consumes.

`closure_claim` 0.
-/

namespace Rcic.Declarative

/-! ## (1) small list facts -/

theorem finChoiceT : (k : Nat) → (P : (i : Nat) → i < k → Type) →
    (∀ i hi, Nonempty (P i hi)) → Nonempty (∀ i hi, P i hi)
  | 0, _, _ => ⟨fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | k + 1, P, h => by
      obtain ⟨f⟩ := finChoiceT k (fun i hi => P i (Nat.lt_succ_of_lt hi)) (fun i hi => h i _)
      obtain ⟨g⟩ := h k (Nat.lt_succ_self k)
      refine ⟨fun i hi => ?_⟩
      by_cases hik : i < k
      · exact f i hik
      · have heq : i = k := by omega
        subst heq
        exact g

theorem policyPrefixContext_append_left (xs ys : List (Expr Nat)) (k : Nat)
    (hk : k ≤ xs.length) :
    policyPrefixContext (xs ++ ys) k = policyPrefixContext xs k := by
  simp only [policyPrefixContext, List.take_append_of_le_length hk]

theorem liftFields_length (extra : Nat) : (As : List (Expr Nat)) → (j : Nat) →
    (liftFields extra As j).length = As.length
  | [], _ => rfl
  | _ :: As, j => by simp only [liftFields, List.length_cons, liftFields_length extra As (j + 1)]

theorem liftFields_getElem? (extra : Nat) : (As : List (Expr Nat)) → (j0 j : Nat) →
    (liftFields extra As j0)[j]? = (As[j]?).map (lift (j0 + j) extra)
  | [], _, _ => by simp [liftFields]
  | A :: As, j0, 0 => by simp [liftFields]
  | A :: As, j0, j + 1 => by
      simp only [liftFields, List.getElem?_cons_succ]
      rw [liftFields_getElem? extra As (j0 + 1) j, show j0 + 1 + j = j0 + (j + 1) by omega]

theorem take_append_add (l₁ l₂ : List α) (j : Nat) :
    (l₁ ++ l₂).take (l₁.length + j) = l₁ ++ l₂.take j := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp only [List.cons_append, List.length_cons, Nat.succ_add, List.take_succ_cons, ih]

/-! ## (2) the transports: a derivation over a stored prefix context, instantiated at the
    redex's universes, relocated under `Γ`, and instantiated at the redex's arguments -/

/-- a prefix of the stored telescope, instantiated at `L` and relocated under `Γ`, is a
    well-formed context when every stored domain is sort-typed in its prefix at the base
    arity. -/
def ctxWfT_telescope {E : ResolvedEnv} (hW : EnvWfT E) {a n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {L : List Level} (hls : levelsBounded n L = true) (hlen : L.length = a)
    (ds : List (Expr Nat)) (lv : Nat → Level)
    (hds : ∀ j (hj : j < ds.length),
      HasTyT E a (policyPrefixContext ds j ++ []) ds[j] (.sort (lv j)))
    (k : Nat) (hk : k ≤ ds.length) :
    Nonempty (CtxWfT E n (policyPrefixContext (ds.map (instantiateLevels L)) k ++ Γ)) := by
  refine ctxWfT_prefix hΓ (ds.map (instantiateLevels L)) k
    (by simp only [List.length_map]; exact hk) ?_
  intro i hi
  have hi' : i < ds.length := by omega
  have h1 := hasTyT_instLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW) hls hlen
    (hds i hi')
  rw [List.append_nil, instLvlsCtx_policyPrefixContext] at h1
  refine ⟨instLevel L (lv i), ⟨?_⟩⟩
  have h2 := hasTyT_relocateN (Γ := Γ) h1
  simpa only [List.getElem_map, instantiateLevels] using h2

/-! ## (3) the recursor's stored telescope, as admission builds it -/

/-- the major domain of the policy recursor type. -/
def policyMajorDom {E : ResolvedEnv} (fam : PolicyFamilyView E) (k : Nat) : Expr Nat :=
  foldApps (.const fam.ref (policyFamilyLevels fam))
    (policyParameterLocals fam.parameters.length (k + 1 + fam.indices.length) ++
      policyLocals fam.indices.length)

/-- the innermost body of the policy recursor type. -/
def policyRecBody (k q : Nat) : Expr Nat :=
  foldApps (.bvar (k + q + 1)) ((List.range q).reverse.map (fun i => Expr.bvar (i + 1)) ++ [.bvar 0])

/-- the policy recursor type as one telescope. -/
def policyRecDoms {E : ResolvedEnv} (fam : PolicyFamilyView E) (minorTypes : List (Expr Nat))
    (policy : EliminationPolicy) : List (Expr Nat) :=
  fam.parameters ++ [policyMotiveType fam policy] ++ minorTypes ++
    fam.indices.mapIdx (fun j T => lift j (minorTypes.length + 1) T) ++
    [policyMajorDom fam minorTypes.length]

theorem policyRecursorType_eq_policyPi {E : ResolvedEnv} (fam : PolicyFamilyView E)
    (minorTypes : List (Expr Nat)) (policy : EliminationPolicy) :
    policyRecursorType fam minorTypes policy =
      policyPi (policyRecDoms fam minorTypes policy)
        (policyRecBody minorTypes.length fam.indices.length) := by
  simp only [policyRecursorType, policyRecDoms, policyMajorDom, policyRecBody, policyPi_append]
  rfl

theorem policyRecDoms_length {E : ResolvedEnv} (fam : PolicyFamilyView E)
    (minorTypes : List (Expr Nat)) (policy : EliminationPolicy) :
    (policyRecDoms fam minorTypes policy).length =
      fam.parameters.length + 1 + minorTypes.length + fam.indices.length + 1 := by
  simp only [policyRecDoms, List.length_append, List.length_cons, List.length_nil,
    List.length_mapIdx]

/-- the witness's peeled recursor telescope IS admission's. -/
theorem IotaWitnessS.recDoms_eq {E E0 : ResolvedEnv} (w : IotaWitnessS E)
    (a : RecursorEliminationAdmitted E0 w.recRef w.recMember)
    (hnp : w.nparams = a.family.parameters.length) (hni : w.nindices = a.family.indices.length)
    (hnm : w.nMinors = a.constructors.length) :
    w.recDoms = policyRecDoms a.family a.minorTypes a.policy ∧
      w.recBody = policyRecBody a.minorTypes.length a.family.indices.length := by
  have hpeel := w.hpeelRec
  rw [a.recursorType, policyRecursorType_eq_policyPi, hnp, hni, hnm, ← a.minorCount,
    show a.family.parameters.length + 1 + a.minorTypes.length + a.family.indices.length + 1 =
      (policyRecDoms a.family a.minorTypes a.policy).length from
      (policyRecDoms_length a.family a.minorTypes a.policy).symm,
    peelPis_policyPi] at hpeel
  have hpair := Option.some.inj hpeel
  exact ⟨(congrArg Prod.fst hpair).symm, (congrArg Prod.snd hpair).symm⟩

theorem policyRecDoms_getElem?_param {E : ResolvedEnv} (fam : PolicyFamilyView E)
    (minorTypes : List (Expr Nat)) (policy : EliminationPolicy) (k : Nat)
    (hk : k < fam.parameters.length) :
    (policyRecDoms fam minorTypes policy)[k]? = fam.parameters[k]? := by
  simp only [policyRecDoms, List.append_assoc]
  rw [List.getElem?_append_left hk]

theorem policyRecDoms_getElem?_motive {E : ResolvedEnv} (fam : PolicyFamilyView E)
    (minorTypes : List (Expr Nat)) (policy : EliminationPolicy) :
    (policyRecDoms fam minorTypes policy)[fam.parameters.length]? =
      some (policyMotiveType fam policy) := by
  simp only [policyRecDoms, List.append_assoc]
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  simp only [List.singleton_append, List.getElem?_cons_zero]

theorem policyRecDoms_getElem?_major {E : ResolvedEnv} (fam : PolicyFamilyView E)
    (minorTypes : List (Expr Nat)) (policy : EliminationPolicy) :
    (policyRecDoms fam minorTypes policy)[fam.parameters.length + 1 + minorTypes.length +
      fam.indices.length]? = some (policyMajorDom fam minorTypes.length) := by
  simp only [policyRecDoms]
  have hl : (fam.parameters ++ [policyMotiveType fam policy] ++ minorTypes ++
      fam.indices.mapIdx (fun j T => lift j (minorTypes.length + 1) T)).length =
      fam.parameters.length + 1 + minorTypes.length + fam.indices.length := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_mapIdx]
  rw [List.getElem?_append_right (by rw [hl]; exact Nat.le_refl _), hl, Nat.sub_self]
  rfl

theorem policyRecDoms_dropLast {E : ResolvedEnv} (fam : PolicyFamilyView E)
    (minorTypes : List (Expr Nat)) (policy : EliminationPolicy) :
    (policyRecDoms fam minorTypes policy).dropLast =
      fam.parameters ++ [policyMotiveType fam policy] ++ minorTypes ++
        fam.indices.mapIdx (fun j T => lift j (minorTypes.length + 1) T) := by
  simp only [policyRecDoms, List.dropLast_concat]

/-! ## (4) level bounds of the stored types, from `EnvWfT` -/

theorem famArity_le_recArity (baseArity : Nat) (policy : EliminationPolicy) :
    baseArity ≤ policyRecursorArity baseArity policy := by
  cases policy <;> simp [policyRecursorArity]


/-! ## (5) argument typings, `getElem?`-indexed (no dependent bound proofs) -/

/-- `args[i]` typed at the `i`-th stored domain instantiated at `L` and at the earlier
    arguments. -/
def ArgsAt (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (L : List Level) (ds args : List (Expr Nat)) :
    Type :=
  ∀ i x d, args[i]? = some x → ds[i]? = some d →
    HasTyT E n Γ x (instPrefix (args.take i) (instantiateLevels L d))

theorem argsAt_outerDom {L : List Level} {ds args : List (Expr Nat)}
    (hk : args.length ≤ ds.length) (i : Nat) (hi : i < args.length) :
    outerDom ((ds.map (instantiateLevels L)).take args.length).reverse i =
      instantiateLevels L (ds[i]'(by omega)) := by
  rw [outerDom_take_reverse _ _ _ (by simp only [List.length_map]; exact hk) hi]
  simp only [List.getElem_map]

/-- the package-A form of an `ArgsAt`. -/
def argsAt_pkgA {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {L : List Level} {ds args : List (Expr Nat)}
    (hk : args.length ≤ ds.length) (h : ArgsAt E n Γ L ds args) :
    ∀ i (hi : i < args.length), HasTyT E n Γ args[i]
      (instPrefix (args.take i) (outerDom ((ds.map (instantiateLevels L)).take args.length).reverse i)) :=
  fun i hi => by
    rw [argsAt_outerDom hk i hi]
    exact h i _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (by omega))

def argsAt_of_spine {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {L : List Level}
    {ds args : List (Expr Nat)}
    (h : ∀ i x d, args[i]? = some x → (ds.map (instantiateLevels L))[i]? = some d →
      HasTyT E n Γ x (instPrefix (args.take i) d)) :
    ArgsAt E n Γ L ds args :=
  fun i x d hx hd => h i x _ hx (by rw [List.getElem?_map, hd]; rfl)

theorem take_take_of_le {α : Type} (l : List α) {i k : Nat} (hik : i ≤ k) :
    (l.take k).take i = l.take i := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < i
  · rw [List.getElem?_take_of_lt hj, List.getElem?_take_of_lt hj,
      List.getElem?_take_of_lt (by omega)]
  · have h1 : ((l.take k).take i)[j]? = none := by
      rw [List.getElem?_eq_none]; simp only [List.length_take]; omega
    have h2 : (l.take i)[j]? = none := by
      rw [List.getElem?_eq_none]; simp only [List.length_take]; omega
    rw [h1, h2]

def argsAt_take {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {L : List Level} {ds args : List (Expr Nat)}
    (h : ArgsAt E n Γ L ds args) (k : Nat) : ArgsAt E n Γ L ds (args.take k) :=
  fun i x d hx hd => by
    have hi : i < k := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      simp only [List.length_take] at this; omega
    rw [take_take_of_le args (Nat.le_of_lt hi)]
    rw [List.getElem?_take_of_lt hi] at hx
    exact h i x d hx hd

def argsAt_snoc {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {L : List Level} {ds args : List (Expr Nat)}
    (h : ArgsAt E n Γ L ds args) {x d : Expr Nat} (hd : ds[args.length]? = some d)
    (hx : HasTyT E n Γ x (instPrefix args (instantiateLevels L d))) :
    ArgsAt E n Γ L ds (args ++ [x]) :=
  fun i y d' hy hd' => by
    by_cases hi : i < args.length
    · rw [List.getElem?_append_left hi] at hy
      rw [List.take_append_of_le_length (Nat.le_of_lt hi)]
      exact h i y d' hy hd'
    · have hlt := (List.getElem?_eq_some_iff.mp hy).1
      simp only [List.length_append, List.length_cons, List.length_nil] at hlt
      have hieq : i = args.length := by omega
      subst hieq
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hy
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      rw [hd] at hd'
      have hdd : d = d' := Option.some.inj hd'
      subst hdd
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      exact hx

/-! ## (6) the transports -/

def transportHasTyT {E : ResolvedEnv} (hW : EnvWfT E) {a n : Nat} {Γ : LCtx} {L : List Level}
    (hls : levelsBounded n L = true) (hlen : L.length = a)
    {ds args : List (Expr Nat)} (hk : args.length ≤ ds.length)
    (hargs : ArgsAt E n Γ L ds args) {e A : Expr Nat}
    (h : HasTyT E a (policyPrefixContext ds args.length) e A) :
    HasTyT E n Γ (instPrefix args (instantiateLevels L e))
      (instPrefix args (instantiateLevels L A)) := by
  have h1 := hasTyT_instLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW) hls hlen h
  rw [instLvlsCtx_policyPrefixContext] at h1
  have h2 := hasTyT_relocateN (Γ := Γ) h1
  refine hasTyT_instPrefix_of_envWfT hW
    (ΔT := ((ds.map (instantiateLevels L)).take args.length).reverse) ?_ h2 (argsAt_pkgA hk hargs)
  simp only [List.length_reverse, List.length_take, List.length_map]; omega

def transportConvT {E : ResolvedEnv} (hW : EnvWfT E) {a n : Nat} {Γ : LCtx} {L : List Level}
    (hls : levelsBounded n L = true) (hlen : L.length = a)
    {ds args : List (Expr Nat)} (hk : args.length ≤ ds.length)
    (hargs : ArgsAt E n Γ L ds args) {x y A : Expr Nat}
    (h : ConvT E a (policyPrefixContext ds args.length) x y A) :
    ConvT E n Γ (instPrefix args (instantiateLevels L x))
      (instPrefix args (instantiateLevels L y)) (instPrefix args (instantiateLevels L A)) := by
  have h1 := convT_instLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW) hls hlen h
  rw [instLvlsCtx_policyPrefixContext] at h1
  have h2 := convT_relocateN (Γ := Γ) h1
  refine convT_instPrefixSame_of_envWfT hW
    (ΔT := ((ds.map (instantiateLevels L)).take args.length).reverse) ?_ h2 (argsAt_pkgA hk hargs)
  simp only [List.length_reverse, List.length_take, List.length_map]; omega

def transportTyConvT {E : ResolvedEnv} (hW : EnvWfT E) {a n : Nat} {Γ : LCtx} {L : List Level}
    (hls : levelsBounded n L = true) (hlen : L.length = a)
    {ds args : List (Expr Nat)} (hk : args.length ≤ ds.length)
    (hargs : ArgsAt E n Γ L ds args) {A B : Expr Nat}
    (h : TyConvT E a (policyPrefixContext ds args.length) A B) :
    TyConvT E n Γ (instPrefix args (instantiateLevels L A))
      (instPrefix args (instantiateLevels L B)) := by
  have h1 := tyConvT_instLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW) hls hlen h
  rw [instLvlsCtx_policyPrefixContext] at h1
  have h2 := tyConvT_relocateN (Γ := Γ) h1
  refine tyConvT_instPrefixSame_of_envWfT hW
    (ΔT := ((ds.map (instantiateLevels L)).take args.length).reverse) ?_ (argsAt_pkgA hk hargs) h2
  simp only [List.length_reverse, List.length_take, List.length_map]; omega

/-- the universe gap: the same stored term at two `=ₙ` universe lists, over the same
    argument instantiation. -/
def levelGapConvT {E : ResolvedEnv} (hW : EnvWfT E) {a n : Nat} {Γ : LCtx} {L L' : List Level}
    (heq : eqNList L L') (hls : levelsBounded n L = true) (hls' : levelsBounded n L' = true)
    (hlen : L.length = a)
    {ds args : List (Expr Nat)} (hk : args.length ≤ ds.length)
    (hargs : ArgsAt E n Γ L ds args) {e A : Expr Nat}
    (h : HasTyT E a (policyPrefixContext ds args.length) e A) :
    ConvT E n Γ (instPrefix args (instantiateLevels L e))
      (instPrefix args (instantiateLevels L' e)) (instPrefix args (instantiateLevels L A)) := by
  have h1 := convT_instantiateLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW) heq hls hls'
    hlen h
  rw [instLvlsCtx_policyPrefixContext] at h1
  have h2 := convT_relocateN (Γ := Γ) h1
  refine convT_instPrefixSame_of_envWfT hW
    (ΔT := ((ds.map (instantiateLevels L)).take args.length).reverse) ?_ h2 (argsAt_pkgA hk hargs)
  simp only [List.length_reverse, List.length_take, List.length_map]; omega

/-- argument conversions assembled under `foldApps`, `getElem?`-indexed: the head converts at
    the full telescope, each argument at its instantiated domain. A constructive twin of
    `convT_foldApps_args` (which the reflective seal cannot admit): `instDomsT` moves the
    telescope one argument at a time. -/
theorem convT_foldApps_args' {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (doms xs xs' : List (Expr Nat)) → xs.length = doms.length → xs'.length = xs.length →
    (h h' U : Expr Nat) → Nonempty (ConvT E n Γ h h' (policyPi doms U)) →
    (∀ i x x' d, xs[i]? = some x → xs'[i]? = some x' → doms[i]? = some d →
      Nonempty (ConvT E n Γ x x' (instPrefix (xs.take i) d))) →
    Nonempty (ConvT E n Γ (foldApps h xs) (foldApps h' xs') (instPrefix xs U))
  | [], [], [], _, _, _, _, _, hhead, _ => by
      simpa only [foldApps, instPrefix_nil, policyPi] using hhead
  | [], _ :: _, _, hl, _, _, _, _, _, _ => by
      rw [List.length_cons, List.length_nil] at hl; exact absurd hl (Nat.succ_ne_zero _)
  | _ :: _, [], _, hl, _, _, _, _, _, _ => by
      rw [List.length_cons, List.length_nil] at hl; exact absurd hl.symm (Nat.succ_ne_zero _)
  | _ :: _, _ :: _, [], _, hl', _, _, _, _, _ => by
      rw [List.length_cons, List.length_nil] at hl'; exact absurd hl'.symm (Nat.succ_ne_zero _)
  | D :: doms, a :: as, a' :: as', hl, hl', h, h', U, hhead, hper => by
      obtain ⟨ch⟩ := hhead
      obtain ⟨ca⟩ := hper 0 a a' D List.getElem?_cons_zero List.getElem?_cons_zero List.getElem?_cons_zero
      rw [List.take_zero, instPrefix_nil] at ca
      have hstep0 : ConvT E n Γ (.app h a) (.app h' a') (instantiate0 a (policyPi doms U)) :=
        .app _ _ _ _ _ _ _ ch ca
      rw [instantiate0, instantiate_policyPi, Nat.zero_add] at hstep0
      have hlas : as.length = doms.length := Nat.succ.inj hl
      have hlas' : as'.length = as.length := Nat.succ.inj hl'
      have hrec := convT_foldApps_args' (instDomsT 0 a doms) as as'
        (by rw [length_instDomsT]; exact hlas) hlas' (.app h a) (.app h' a')
        (instantiate doms.length (lift 0 doms.length a) U) ⟨hstep0⟩
        (fun i x x' d hx hx' hd => by
          have hi : i < doms.length := by
            rw [← length_instDomsT 0 a doms]; exact (List.getElem?_eq_some_iff.mp hd).1
          rw [List.getElem?_eq_getElem (by rw [length_instDomsT]; exact hi),
            getElem_instDomsT _ _ _ _ hi, Nat.zero_add] at hd
          have hia : i < as.length := by rw [hlas]; exact hi
          have := hper (i + 1) x x' (doms[i])
            (by rw [List.getElem?_cons_succ]; exact hx)
            (by rw [List.getElem?_cons_succ]; exact hx')
            (by rw [List.getElem?_cons_succ, List.getElem?_eq_getElem hi])
          rw [List.take_succ_cons, instPrefix_cons, List.length_take,
            Nat.min_eq_left (Nat.le_of_lt hia)] at this
          rw [← Option.some.inj hd]
          exact this)
      rw [instPrefix_cons, hlas]
      exact hrec

/-! ## (7) the family application instantiated at the redex -/

theorem instantiateLevels_sort' (L : List Level) (u : Level) :
    instantiateLevels L (.sort u) = .sort (instLevel L u) := rfl

theorem policyParameterLocals_instantiateLevels (L : List Level) (np fl : Nat) :
    (policyParameterLocals np fl).map (instantiateLevels L) = policyParameterLocals np fl := by
  simp only [policyParameterLocals, List.map_map]; rfl

/-- a family application over the parameter locals and some index arguments, instantiated
    at `L` and at `args` (the parameters then the fields): the parameters become the first
    `np` arguments, each index argument is instantiated. -/
theorem instPrefix_famApp (args : List (Expr Nat)) (np fl r : Nat) (lvls L : List Level)
    (resIdx : List (Expr Nat)) (hlen : args.length = np + fl) :
    instPrefix args (instantiateLevels L
      (foldApps (.const r lvls) (policyParameterLocals np fl ++ resIdx))) =
      foldApps (.const r (lvls.map (instLevel L)))
        (args.take np ++ resIdx.map (fun x => instPrefix args (instantiateLevels L x))) := by
  rw [foldApps_instantiateLevels, instPrefix_foldApps]
  simp only [instantiateLevels, instPrefix_const, List.map_append, List.map_map,
    policyParameterLocals_instantiateLevels]
  have hp := instPrefix_paramPrefix args np fl hlen rfl
  simp only [policyParameterLocals]
  rw [hp]
  rfl

/-! ## (8) the redex's recursor-side pieces -/

def recP {E : ResolvedEnv} (w : IotaWitnessS E) : List (Expr Nat) := w.preMajor.take w.nparams
def recIdx {E : ResolvedEnv} (w : IotaWitnessS E) : List (Expr Nat) :=
  w.preMajor.drop (w.nparams + 1 + w.nMinors)
def famL1 {E : ResolvedEnv} (w : IotaWitnessS E) : List Level :=
  ((List.range w.famMember.arity).map Level.param).map (instLevel w.ls)
def majorTyW {E : ResolvedEnv} (w : IotaWitnessS E) : Expr Nat :=
  foldApps (.const w.familyRef (famL1 w)) (recP w ++ recIdx w)
def majorW {E : ResolvedEnv} (w : IotaWitnessS E) : Expr Nat :=
  foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields)

theorem recP_length {E : ResolvedEnv} (w : IotaWitnessS E) : (recP w).length = w.nparams := by
  simp only [recP, List.length_take]; have := w.hpre; omega

theorem recIdx_length {E : ResolvedEnv} (w : IotaWitnessS E) : (recIdx w).length = w.nindices := by
  simp only [recIdx, List.length_drop]; have := w.hpre; omega

theorem recP_getElem? {E : ResolvedEnv} (w : IotaWitnessS E) (k : Nat) (hk : k < w.nparams) :
    (recP w)[k]? = w.preMajor[k]? := by
  simp only [recP, List.getElem?_take_of_lt hk]

theorem recP_take {E : ResolvedEnv} (w : IotaWitnessS E) (k : Nat) (hk : k ≤ w.nparams) :
    (recP w).take k = w.preMajor.take k := by
  simp only [recP, take_take_of_le w.preMajor hk]

/-- the admission mirror at the redex: the constructor's `k`-th parameter domain and the
    family's, instantiated at `L` and at `args` (typed at the constructor's own domains). -/
theorem ctorMirror {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    (w : IotaWitnessS E) (c : RecursorCellHT E w.recRef w.recMember)
    (i : Fin c.cell.adm.constructors.length) (L : List Level)
    (hls : levelsBounded n L = true) (hlen : L.length = c.cell.adm.family.member.arity)
    (args : List (Expr Nat)) (k : Nat) (hk : k < (c.cell.adm.constructorViews i).parameters.length)
    (hargl : args.length = k)
    (hargs : ArgsAt E n Γ L ((c.cell.adm.constructorViews i).parameters ++
      (c.cell.adm.constructorViews i).fields) args) :
    Nonempty (TyConvT E n Γ
      (instPrefix args (instantiateLevels L ((c.cell.adm.constructorViews i).parameters[k])))
      (instPrefix args (instantiateLevels L (c.cell.adm.family.parameters[k]'(by
        rw [← (c.cell.adm.constructorViews i).parameterCount]; exact hk))))) := by
  obtain ⟨hm⟩ := (c.ctorsTyped i).2 ⟨k, hk⟩
  have hm1 := tyConvTExt c.cell.env_extends hm
  have hm' : TyConvT E c.cell.adm.family.member.arity
      (policyPrefixContext ((c.cell.adm.constructorViews i).parameters ++
        (c.cell.adm.constructorViews i).fields) args.length)
      ((c.cell.adm.constructorViews i).parameters[k])
      (c.cell.adm.family.parameters[k]'(by
        rw [← (c.cell.adm.constructorViews i).parameterCount]; exact hk)) := by
    rw [hargl, policyPrefixContext_append_left _ _ _ (Nat.le_of_lt hk)]
    exact hm1
  exact ⟨transportTyConvT hW hls hlen (by rw [hargl, List.length_append]; omega) hargs hm'⟩

/-! ## (9) the constructor side -/

structure CtorSideData {E : ResolvedEnv} (n : Nat) (Γ : LCtx) (w : IotaWitnessS E)
    (c : RecursorCellHT E w.recRef w.recMember) : Type where
  i : Fin c.cell.adm.constructors.length
  hi : i.val = w.ctorIdx
  /-- every field typed at the recursor-side instantiation of its stored domain. -/
  fsTyped : ∀ j f d, w.fields[j]? = some f →
    (c.cell.adm.constructorViews i).fields[j]? = some d →
    HasTyT E n Γ f (instPrefix (recP w ++ w.fields.take j) (instantiateLevels w.ls d))
  /-- the major converts to the recursor-side constructor application at the major domain. -/
  majorConv : ConvT E n Γ (majorW w)
    (foldApps (.const w.ctorRef (famL1 w)) (recP w ++ w.fields)) (majorTyW w)
  /-- every redex index converts to the equation's result index at the family's index domain. -/
  idxConv : ∀ j x r d, (recIdx w)[j]? = some x →
    (c.cell.adm.constructorViews i).resultIndices[j]? = some r →
    c.cell.adm.family.indices[j]? = some d →
    Nonempty (ConvT E n Γ x (instPrefix (recP w ++ w.fields) (instantiateLevels w.ls r))
      (instPrefix (recP w ++ (recIdx w).take j) (instantiateLevels w.ls d)))

set_option maxHeartbeats 2000000 in
theorem ctorSide {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} (hrows : TypedRowsWf E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (w : IotaWitnessS E)
    (c : RecursorCellHT E w.recRef w.recMember)
    (hlsLen : w.ls.length = w.recMember.arity) (hwf : levelsBounded n w.ls = true)
    (hmajor : HasTyT E n Γ (majorW w) (majorTyW w))
    (hAM : ∃ u, Nonempty (HasTyT E n Γ (majorTyW w) (.sort u)))
    (pTyped : ∀ k x d, w.preMajor[k]? = some x → k < w.nparams →
      c.cell.adm.family.parameters[k]? = some d →
      HasTyT E n Γ x (instPrefix (w.preMajor.take k) (instantiateLevels w.ls d))) :
    Nonempty (CtorSideData n Γ w c) := by
  -- (0) the admission data behind the witness
  obtain ⟨hfam, hfamM, hnp, hni, hnm⟩ :=
    IotaWitnessS.recData_admitted c.cell.adm c.cell.sub w rfl rfl
  have hiv : w.ctorIdx < c.cell.adm.constructors.length := by rw [← hnm]; exact w.hidx
  have hcm := c.cell.ctorMember_eq w hfam ⟨w.ctorIdx, hiv⟩ rfl
  obtain ⟨hdoms, hres⟩ := c.cell.ctorData_eq w ⟨w.ctorIdx, hiv⟩ hcm
  have hcpl : (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters.length =
      c.cell.adm.family.parameters.length := (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameterCount
  have hctorA : w.ctorMember.arity = c.cell.adm.family.member.arity := by
    rw [hcm]; exact (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).arity
  have hcplen : w.ctorParams.length = (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters.length := by
    rw [w.hctorParams, hnp, hcpl]
  have hst : w.ctorMember.mtype = policyPi ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields)
      (foldApps (.const c.cell.adm.family.ref (policyFamilyLevels c.cell.adm.family))
        (policyParameterLocals (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters.length
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields.length ++
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).resultIndices)) := by
    rw [hcm]; exact (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).storedType
  have hfl : w.fields.length = (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields.length := by
    have hpc : piCount w.ctorMember.mtype = ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
        (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).length := by
      rw [hst, piCount_policyPi,
        piCount_foldApps_of_zero (.const c.cell.adm.family.ref (policyFamilyLevels c.cell.adm.family)) _ rfl,
        Nat.add_zero]
    have hnpar := w.hnpar
    rw [hpc, List.length_append] at hnpar
    omega
  have hplen : (recP w).length = w.nparams := recP_length w
  have hplen' : (recP w).length = w.ctorParams.length := by rw [hplen, w.hctorParams]
  have hilen : (recIdx w).length = w.nindices := recIdx_length w
  have hfamE : E.members c.cell.adm.family.ref = some c.cell.adm.family.member :=
    c.cell.env_extends _ _ c.cell.adm.family.present
  have hle : c.cell.adm.family.member.arity ≤ w.ls.length := by
    rw [hlsLen, c.cell.adm.recursorArity]; exact famArity_le_recArity _ _
  -- the telescope length bookkeeping
  have hTelLen : ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).length = w.ctorParams.length + w.fields.length := by
    simp only [List.length_append, hcplen, hfl]
  -- level vectors
  have hL1len : (famL1 w).length = c.cell.adm.family.member.arity := by
    simp only [famL1, List.length_map, List.length_range, hfamM]
  have hwfL1 : levelsBounded n (famL1 w) = true := by
    refine levelsBounded_inst hwf hlsLen ?_
    exact levelsBounded_mono (by rw [hfamM]; exact Nat.le_trans hle (Nat.le_of_eq hlsLen)) _
      (levelsBounded_canonRecLevels _)
  have hbelow : ∀ k, k < c.cell.adm.family.member.arity →
      instLevel (famL1 w) (.param k) = instLevel w.ls (.param k) := by
    simp only [famL1, hfamM]
    exact famLevels_instLevel_param w.ls c.cell.adm.family.member.arity hle
  have hcongF : ∀ e, exprLevelsBounded c.cell.adm.family.member.arity e = true →
      instantiateLevels (famL1 w) e = instantiateLevels w.ls e :=
    fun e hb => instantiateLevels_congr_bounded hbelow e hb
  -- level bounds of the stored types
  have hctorB : exprLevelsBounded c.cell.adm.family.member.arity w.ctorMember.mtype = true := by
    have := (envWfT_levels hW _ _ w.hctor).1
    rw [hctorA] at this
    exact this
  rw [hst] at hctorB
  obtain ⟨hdomsB, hbodyB⟩ := Ann.exprLevelsBounded_policyPi _ _ _ hctorB
  obtain ⟨_, hresB⟩ := Ann.exprLevelsBounded_foldApps_rev _ _ _ hbodyB
  have hfamB : exprLevelsBounded c.cell.adm.family.member.arity c.cell.adm.family.member.mtype = true :=
    (envWfT_levels hW _ _ hfamE).1
  rw [c.cell.adm.family.storedType] at hfamB
  obtain ⟨hfamDomsB, _⟩ := Ann.exprLevelsBounded_policyPi _ _ _ hfamB
  -- (1) the constructor spine
  have hctorPi : instantiateLevels w.lsC w.ctorMember.mtype =
      policyPi (w.ctorDoms.map (instantiateLevels w.lsC)) (instantiateLevels w.lsC w.ctorResult) := by
    rw [policyPi_of_peelPis _ _ w.hpeel, instantiateLevels_policyPi]
  have hlenC : (w.ctorDoms.map (instantiateLevels w.lsC)).length =
      (w.ctorParams ++ w.fields).length := by
    simp only [List.length_map, List.length_append, peelPis_length _ _ w.hpeel, w.hctorParams]
  obtain ⟨hlsC, hwfC, cfArgs0, convR⟩ :=
    hasTyT_spineInv_rows hW hrows.piRow hΓ w.hctor hctorPi (w.ctorParams ++ w.fields) hlenC hmajor
  have hlsC' : w.lsC.length = c.cell.adm.family.member.arity := hlsC.trans hctorA
  rw [hdoms] at cfArgs0
  have cfArgs : ArgsAt E n Γ w.lsC ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields) (w.ctorParams ++ w.fields) :=
    argsAt_of_spine cfArgs0
  have hkC : (w.ctorParams ++ w.fields).length ≤ ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).length := by
    rw [hTelLen, List.length_append]; exact Nat.le_refl _
  have hL2 : (policyFamilyLevels c.cell.adm.family).map (instLevel w.lsC) = w.lsC :=
    famLevels_instLevel w.lsC hlsC'
  have hL1fam : (policyFamilyLevels c.cell.adm.family).map (instLevel (famL1 w)) = famL1 w :=
    famLevels_instLevel (famL1 w) hL1len
  -- the stored telescope's sort typings at the family arity, as data
  obtain ⟨uC, hCty⟩ := envWfT_mtypeSortTyped hW _ _ w.hctor
  rw [hctorA, hst] at hCty
  obtain ⟨lvC, hdomsTy⟩ := hasTyT_policyPi_invTS _ hCty
  obtain ⟨_, vC, ⟨hbodyTy⟩⟩ := hasTyT_policyPi_inv _ hCty
  rw [List.append_nil] at hbodyTy
  have hbodyTy' : HasTyT E c.cell.adm.family.member.arity
      (policyPrefixContext ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
        (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields) (w.ctorParams ++ w.fields).length)
      (foldApps (.const c.cell.adm.family.ref (policyFamilyLevels c.cell.adm.family))
        (policyParameterLocals (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters.length
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields.length ++
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).resultIndices))
      (.sort vC) := by
    rw [List.length_append, ← hTelLen]
    exact hbodyTy
  have hdomsTy' : ∀ j (hj : j < ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).length),
      HasTyT E c.cell.adm.family.member.arity
        (policyPrefixContext ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields) j)
        (((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields)[j]) (.sort (lvC j)) := by
    intro j hj
    have := hdomsTy j hj
    rw [List.append_nil] at this
    exact this
  -- (2) the constructor's result type at the redex, and its sort
  have hR0 : instPrefix (w.ctorParams ++ w.fields) (instantiateLevels w.lsC w.ctorResult) =
      foldApps (.const c.cell.adm.family.ref w.lsC) (w.ctorParams ++
        (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).resultIndices.map
          (fun r => instPrefix (w.ctorParams ++ w.fields) (instantiateLevels w.lsC r))) := by
    rw [hres, instPrefix_famApp _ _ _ _ _ _ _ (by rw [List.length_append, hcplen, hfl]), hL2,
      List.take_left' hcplen]
  have hR0sort : HasTyT E n Γ (foldApps (.const c.cell.adm.family.ref w.lsC) (w.ctorParams ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).resultIndices.map
        (fun r => instPrefix (w.ctorParams ++ w.fields) (instantiateLevels w.lsC r))))
      (.sort (instLevel w.lsC vC)) := by
    have h := transportHasTyT hW hwfC hlsC' hkC cfArgs hbodyTy'
    rw [← hres, hR0, instantiateLevels_sort', instPrefix_sort] at h
    exact h
  have convR' : TyConvT E n Γ (foldApps (.const c.cell.adm.family.ref w.lsC) (w.ctorParams ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).resultIndices.map
        (fun r => instPrefix (w.ctorParams ++ w.fields) (instantiateLevels w.lsC r)))) (majorTyW w) := by
    rw [← hR0]; exact convR
  have hAMform : majorTyW w = foldApps (.const c.cell.adm.family.ref (famL1 w)) (recP w ++ recIdx w) := by
    simp only [majorTyW, hfam]
  -- (3) ROW 3, constructor side on the left: the universes and the parameters
  have hfamPi : ∀ L : List Level, instantiateLevels L c.cell.adm.family.member.mtype =
      policyPi ((c.cell.adm.family.parameters ++ c.cell.adm.family.indices).map (instantiateLevels L))
        (.sort (instLevel L c.cell.adm.family.resultLevel)) := by
    intro L; rw [c.cell.adm.family.storedType, instantiateLevels_policyPi]; rfl
  obtain ⟨heqC, _, hargs21⟩ := hrows.famAppRow hΓ hfamE c.cell.adm.family.hasClass hR0sort
    (by rw [hAMform] at convR'; exact convR')
  have cpConvFam_lsC : ∀ k x y d, w.ctorParams[k]? = some x → (recP w)[k]? = some y →
      c.cell.adm.family.parameters[k]? = some d →
      Nonempty (ConvT E n Γ x y (instPrefix (w.ctorParams.take k) (instantiateLevels w.lsC d))) := by
    intro k x y d hx hy hd
    have hk : k < w.ctorParams.length := (List.getElem?_eq_some_iff.mp hx).1
    have hkp : k < (recP w).length := (List.getElem?_eq_some_iff.mp hy).1
    have h := convArgsT_instPrefix hargs21 _ _ (hfamPi w.lsC) k x y (instantiateLevels w.lsC d)
      (by rw [List.getElem?_append_left hk]; exact hx)
      (by rw [List.getElem?_append_left hkp]; exact hy)
      (by rw [List.getElem?_map, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hd).1, hd]; rfl)
    rw [List.take_append_of_le_length (Nat.le_of_lt hk)] at h
    exact h
  -- (4) the parameters converted at the constructor's own domains, at `lsC`
  have cpConvCtor_lsC : ∀ k x y d, w.ctorParams[k]? = some x → (recP w)[k]? = some y →
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters[k]? = some d →
      Nonempty (ConvT E n Γ x y (instPrefix (w.ctorParams.take k) (instantiateLevels w.lsC d))) := by
    intro k x y d hx hy hd
    have hk : k < (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters.length :=
      (List.getElem?_eq_some_iff.mp hd).1
    have hkf : k < c.cell.adm.family.parameters.length := by rw [← hcpl]; exact hk
    obtain ⟨hc⟩ := cpConvFam_lsC k x y _ hx hy (List.getElem?_eq_getElem hkf)
    obtain ⟨hm⟩ := ctorMirror hW w c ⟨w.ctorIdx, hiv⟩ w.lsC hwfC hlsC' (w.ctorParams.take k) k hk
      (by simp only [List.length_take]; omega)
      (by
        have := argsAt_take cfArgs k
        rw [List.take_append_of_le_length (by rw [hcplen]; exact Nat.le_of_lt hk)] at this
        exact this)
    have hd' : d = (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters[k] := by
      rw [List.getElem?_eq_getElem hk] at hd; exact (Option.some.inj hd).symm
    subst hd'
    exact ⟨convT_of_tyConv hc (TyConvT.symmT hm)⟩
  -- (5) the major converts to the recursor-side constructor application
  have majorConv : Nonempty (ConvT E n Γ (majorW w)
      (foldApps (.const w.ctorRef (famL1 w)) (recP w ++ w.fields)) (majorTyW w)) := by
    have hhead : ConvT E n Γ (.const w.ctorRef w.lsC) (.const w.ctorRef (famL1 w))
        (policyPi (((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).map (instantiateLevels w.lsC))
          (instantiateLevels w.lsC w.ctorResult)) := by
      have h := ConvT.consts Γ w.ctorRef w.lsC (famL1 w) w.ctorMember w.hctor hlsC hwfC hwfL1 heqC
      rw [hctorPi, hdoms] at h
      exact h
    have hl : (w.ctorParams ++ w.fields).length = (((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
        (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).map (instantiateLevels w.lsC)).length := by
      rw [List.length_map, hTelLen, List.length_append]
    have hl' : (recP w ++ w.fields).length = (w.ctorParams ++ w.fields).length := by
      simp only [List.length_append, hplen']
    obtain ⟨hc⟩ := convT_foldApps_args' _ (w.ctorParams ++ w.fields) (recP w ++ w.fields) hl hl'
      _ _ _ ⟨hhead⟩ (by
        intro k x y d hx hy hd
        rw [List.getElem?_map] at hd
        by_cases hkp : k < w.ctorParams.length
        · rw [List.getElem?_append_left hkp] at hx
          rw [List.getElem?_append_left (by rw [hplen']; exact hkp)] at hy
          rw [List.getElem?_append_left (by rw [← hcplen]; exact hkp)] at hd
          cases hd1 : (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters[k]? with
          | none => rw [hd1] at hd; cases hd
          | some d0 =>
              rw [hd1] at hd
              simp only [Option.map_some', Option.some.injEq] at hd
              subst hd
              rw [List.take_append_of_le_length (Nat.le_of_lt hkp)]
              exact cpConvCtor_lsC k x y d0 hx hy hd1
        · have hkf : w.ctorParams.length ≤ k := Nat.le_of_not_lt hkp
          rw [List.getElem?_append_right hkf] at hx
          rw [List.getElem?_append_right (by rw [hplen']; exact hkf), hplen'] at hy
          rw [hx] at hy
          have hxy : x = y := Option.some.inj hy
          subst hxy
          cases hd1 : ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
              (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields)[k]? with
          | none => rw [hd1] at hd; cases hd
          | some d0 =>
              rw [hd1] at hd
              simp only [Option.map_some', Option.some.injEq] at hd
              subst hd
              exact ⟨.refl _ _ _ (cfArgs k x d0 (by rw [List.getElem?_append_right hkf]; exact hx) hd1)⟩)
    exact ⟨convT_of_tyConv hc convR⟩
  -- (6) the universe gap on the constructor telescope: the arguments at `famL1`
  have cfArgsL1 : ArgsAt E n Γ (famL1 w) ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields) (w.ctorParams ++ w.fields) := by
    intro k x d hx hd
    have hk : k < (w.ctorParams ++ w.fields).length := (List.getElem?_eq_some_iff.mp hx).1
    have hkd : k < ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).length := (List.getElem?_eq_some_iff.mp hd).1
    have h0 := cfArgs k x d hx hd
    have hdd : d = ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
        (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields)[k] := by
      rw [List.getElem?_eq_getElem hkd] at hd; exact (Option.some.inj hd).symm
    subst hdd
    have hg := levelGapConvT hW heqC hwfC hwfL1 hlsC'
      (args := (w.ctorParams ++ w.fields).take k) (by simp only [List.length_take]; omega)
      (argsAt_take cfArgs k)
      (by
        have := hdomsTy' k hkd
        rw [show ((w.ctorParams ++ w.fields).take k).length = k by simp only [List.length_take]; omega]
        exact this)
    rw [instantiateLevels_sort'] at hg
    rw [instPrefix_sort] at hg
    exact hasTyT_of_tyConv h0 (.of _ _ _ _ hg)
  -- (7) ROW 3, recursor side on the left: the parameters at `famL1`
  obtain ⟨uA, ⟨hAMsort⟩⟩ := hAM
  have hAMsort' := hAMsort
  rw [hAMform] at hAMsort'
  have convR'' := convR'
  rw [hAMform] at convR''
  obtain ⟨_, _, hargs12⟩ := hrows.famAppRow hΓ hfamE c.cell.adm.family.hasClass hAMsort'
    (TyConvT.symmT convR'')
  have pConvFam_L1 : ∀ k x y d, (recP w)[k]? = some x → w.ctorParams[k]? = some y →
      c.cell.adm.family.parameters[k]? = some d →
      Nonempty (ConvT E n Γ x y (instPrefix ((recP w).take k) (instantiateLevels (famL1 w) d))) := by
    intro k x y d hx hy hd
    have hk : k < w.ctorParams.length := (List.getElem?_eq_some_iff.mp hy).1
    have hkp : k < (recP w).length := (List.getElem?_eq_some_iff.mp hx).1
    have h := convArgsT_instPrefix hargs12 _ _ (hfamPi (famL1 w)) k x y (instantiateLevels (famL1 w) d)
      (by rw [List.getElem?_append_left hkp]; exact hx)
      (by rw [List.getElem?_append_left hk]; exact hy)
      (by rw [List.getElem?_map, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hd).1, hd]; rfl)
    rw [List.take_append_of_le_length (Nat.le_of_lt hkp)] at h
    exact h
  -- (8) the recursor-side parameters typed at the constructor's own domains, at `famL1`
  have pArgsL1 : ∀ k, k ≤ (recP w).length →
      Nonempty (ArgsAt E n Γ (famL1 w) ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
        (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields) ((recP w).take k)) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun i x d hx _ => by simp at hx⟩
    | succ k ih =>
        intro hk
        obtain ⟨f⟩ := ih (Nat.le_of_succ_le hk)
        have hkc : k < (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters.length := by
          rw [hcpl, ← hnp, ← hplen]; omega
        have hkf : k < c.cell.adm.family.parameters.length := by rw [← hcpl]; exact hkc
        have hkp : k < (recP w).length := by omega
        have hp0 := pTyped k ((recP w)[k]) (c.cell.adm.family.parameters[k])
          (by rw [← recP_getElem? w k (by rw [← hplen]; exact hkp), List.getElem?_eq_getElem hkp])
          (by rw [← hplen]; exact hkp) (List.getElem?_eq_getElem hkf)
        rw [← recP_take w k (by rw [← hplen]; omega),
          ← hcongF _ (hfamDomsB _ (List.mem_append_left _ (List.getElem_mem hkf)))] at hp0
        obtain ⟨hm⟩ := ctorMirror hW w c ⟨w.ctorIdx, hiv⟩ (famL1 w) hwfL1 hL1len ((recP w).take k) k hkc
          (by simp only [List.length_take]; omega) f
        have hp2 : HasTyT E n Γ ((recP w)[k])
            (instPrefix ((recP w).take k)
              (instantiateLevels (famL1 w) ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters[k]))) :=
          hasTyT_of_tyConv hp0 (TyConvT.symmT hm)
        refine ⟨?_⟩
        have hsnoc := argsAt_snoc f (x := (recP w)[k])
          (d := (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters[k])
          (by
            rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hkp), List.getElem?_append_left hkc,
              List.getElem?_eq_getElem hkc])
          hp2
        have htake : (recP w).take k ++ [(recP w)[k]] = (recP w).take (k + 1) := by
          rw [List.take_succ, List.getElem?_eq_getElem hkp]; rfl
        rw [htake] at hsnoc
        exact hsnoc
  obtain ⟨pArgs⟩ := pArgsL1 (recP w).length (Nat.le_refl _)
  rw [List.take_length] at pArgs
  have pConvCtor_L1 : ∀ k x y d, (recP w)[k]? = some x → w.ctorParams[k]? = some y →
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters[k]? = some d →
      Nonempty (ConvT E n Γ x y (instPrefix ((recP w).take k) (instantiateLevels (famL1 w) d))) := by
    intro k x y d hx hy hd
    have hk : k < (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters.length :=
      (List.getElem?_eq_some_iff.mp hd).1
    have hkf : k < c.cell.adm.family.parameters.length := by rw [← hcpl]; exact hk
    obtain ⟨hc⟩ := pConvFam_L1 k x y _ hx hy (List.getElem?_eq_getElem hkf)
    obtain ⟨hm⟩ := ctorMirror hW w c ⟨w.ctorIdx, hiv⟩ (famL1 w) hwfL1 hL1len ((recP w).take k) k hk
      (by simp only [List.length_take]; rw [hplen, hnp, ← hcpl]; omega) (argsAt_take pArgs k)
    have hd' : d = (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters[k] := by
      rw [List.getElem?_eq_getElem hk] at hd; exact (Option.some.inj hd).symm
    subst hd'
    exact ⟨convT_of_tyConv hc (TyConvT.symmT hm)⟩
  -- (9) the fields typed at the recursor-side instantiation, at `famL1`
  have hSL : SubstLetT E n := substLetT_of_envWfT hW
  have hconst : ConstsRightDataT E n := constsRightDataT_of_envWfT hW
  have hdomL1 : ∀ k (hk : k < ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).length),
      HasTyT E n (policyPrefixContext (((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
        (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).map (instantiateLevels (famL1 w))) k ++ Γ)
        (instantiateLevels (famL1 w) (((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields)[k])) (.sort (instLevel (famL1 w) (lvC k))) := by
    intro k hk
    have h1 := hasTyT_instLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW) hwfL1 hL1len (hdomsTy' k hk)
    rw [instLvlsCtx_policyPrefixContext] at h1
    exact hasTyT_relocateN (Γ := Γ) h1
  -- the argument conversions `p ++ args` versus `cp ++ args`, at the `famL1` domains
  have hargConvs : ∀ (args : List (Expr Nat)), args.length ≤ w.fields.length →
      ArgsAt E n Γ (famL1 w) ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
        (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields) (recP w ++ args) →
      ∀ k (hk : k < (recP w ++ args).length),
        Nonempty (ConvT E n Γ (recP w ++ args)[k] ((w.ctorParams ++ args)[k]'(by
            simp only [List.length_append, hplen'] at hk ⊢; exact hk))
          (instPrefix ((recP w ++ args).take k)
            (outerDom ((((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
              (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).map (instantiateLevels (famL1 w))).take
              (recP w ++ args).length).reverse k))) := by
    intro args hargsLen g k hk
    have hkd : (recP w ++ args).length ≤ ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
        (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).length := by
      rw [hTelLen]; simp only [List.length_append, hplen']; omega
    rw [argsAt_outerDom hkd k hk]
    by_cases hkp : k < (recP w).length
    · have hkc : k < (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters.length := by
        rw [hcpl, ← hnp, ← hplen]; exact hkp
      obtain ⟨hc⟩ := pConvCtor_L1 k ((recP w)[k]) (w.ctorParams[k]'(by rw [← hplen']; exact hkp))
        ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters[k])
        (List.getElem?_eq_getElem hkp) (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem hkc)
      refine ⟨?_⟩
      rw [List.getElem_append_left hkp, List.getElem_append_left (by rw [← hplen']; exact hkp),
        List.take_append_of_le_length (Nat.le_of_lt hkp), List.getElem_append_left hkc]
      exact hc
    · have hkf : (recP w).length ≤ k := Nat.le_of_not_lt hkp
      have hkf' : w.ctorParams.length ≤ k := by rw [← hplen']; exact hkf
      refine ⟨?_⟩
      rw [List.getElem_append_right hkf, List.getElem_append_right hkf']
      have hidx : k - w.ctorParams.length = k - (recP w).length := by rw [hplen']
      have hb1 : k - w.ctorParams.length < args.length := by
        simp only [List.length_append] at hk; omega
      have hb2 : k - (recP w).length < args.length := by
        simp only [List.length_append] at hk; omega
      rw [getElem_idx_congr hidx hb1 hb2]
      have := g k (args[k - (recP w).length]) (((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields)[k])
        (by rw [List.getElem?_append_right hkf, List.getElem?_eq_getElem hb2])
        (List.getElem?_eq_getElem (by omega))
      exact .refl _ _ _ this
  have fsArgsL1 : ∀ j, j ≤ w.fields.length →
      Nonempty (ArgsAt E n Γ (famL1 w) ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
        (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields) (recP w ++ w.fields.take j)) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨by simpa only [List.take_zero, List.append_nil] using pArgs⟩
    | succ j ih =>
        intro hj
        obtain ⟨g⟩ := ih (Nat.le_of_succ_le hj)
        have hjf : j < w.fields.length := hj
        have hjc : j < (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields.length := by rw [← hfl]; exact hjf
        have hlenj : (recP w ++ w.fields.take j).length = (recP w).length + j := by
          simp only [List.length_append, List.length_take]; omega
        have hidxT : (recP w).length + j < ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
            (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).length := by
          rw [hTelLen, hplen']; omega
        have hidxE : ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
            (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields)[(recP w).length + j]'hidxT =
            (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields[j] := by
          rw [List.getElem_append_right (by rw [hplen, hnp, hcpl]; exact Nat.le_add_right _ _)]
          congr 1; rw [hplen, hnp, hcpl]; exact Nat.add_sub_cancel_left _ _
        have hidxE? : ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
            (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields)[(recP w).length + j]? =
            some ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields[j]) := by
          rw [List.getElem?_eq_getElem hidxT, hidxE]
        -- the field at the constructor-side instantiation, at `famL1`
        have hf0 := cfArgsL1 ((recP w).length + j) w.fields[j] ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields[j])
          (by rw [hplen', List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
            List.getElem?_eq_getElem hjf])
          hidxE?
        rw [hplen', take_append_add] at hf0
        -- the domain sort-typing at `famL1` under `Γ`
        have hG := hdomL1 ((recP w).length + j) hidxT
        rw [hidxE, ← hlenj] at hG
        obtain ⟨hctx⟩ := ctxWfT_telescope hW hΓ hwfL1 hL1len _ lvC hdomsTy
          (recP w ++ w.fields.take j).length (by rw [hlenj]; exact Nat.le_of_lt hidxT)
        obtain ⟨hconvs⟩ := finChoiceT _ _ (hargConvs (w.fields.take j)
          (by simp only [List.length_take]; omega) g)
        have hpar := convT_instPrefix hW hSL hconst (recP w ++ w.fields.take j)
          (w.ctorParams ++ w.fields.take j)
          (ΔT := ((((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
            (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).map (instantiateLevels (famL1 w))).take
            (recP w ++ w.fields.take j).length).reverse)
          (by simp only [List.length_reverse, List.length_take, List.length_map]; rw [hlenj]; omega)
          (by simp only [List.length_append, hplen'])
          hctx (.refl _ _ _ hG) hG hconvs
          (argsAt_pkgA (by rw [hlenj]; exact Nat.le_of_lt hidxT) g)
        rw [instPrefix_sort] at hpar
        have hf1 : HasTyT E n Γ w.fields[j]
            (instPrefix (recP w ++ w.fields.take j)
              (instantiateLevels (famL1 w) ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields[j]))) :=
          hasTyT_of_tyConv hf0 (TyConvT.symmT (.of _ _ _ _ hpar))
        refine ⟨?_⟩
        have hsnoc := argsAt_snoc g (x := w.fields[j]) (d := (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields[j])
          (by rw [hlenj]; exact hidxE?) hf1
        have htake : recP w ++ w.fields.take j ++ [w.fields[j]] = recP w ++ w.fields.take (j + 1) := by
          rw [List.append_assoc, List.take_succ, List.getElem?_eq_getElem hjf]; rfl
        rw [htake] at hsnoc
        exact hsnoc
  obtain ⟨fsArgs⟩ := fsArgsL1 w.fields.length (Nat.le_refl _)
  rw [List.take_length] at fsArgs
  -- (10) the constructor's result type: constructor-side to recursor-side instantiation
  have hkP : (recP w ++ w.fields).length ≤ ((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).length := by
    rw [hTelLen]; simp only [List.length_append, hplen']; exact Nat.le_refl _
  have hbodyL1 : HasTyT E n (policyPrefixContext (((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).map (instantiateLevels (famL1 w)))
      (recP w ++ w.fields).length ++ Γ)
      (instantiateLevels (famL1 w) (foldApps (.const c.cell.adm.family.ref (policyFamilyLevels c.cell.adm.family))
        (policyParameterLocals (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters.length
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields.length ++
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).resultIndices)))
      (.sort (instLevel (famL1 w) vC)) := by
    have h1 := hasTyT_instLevels (envWfT_levels hW) (iotaLevelsT_of_envWfT hW) hwfL1 hL1len hbodyTy'
    rw [instLvlsCtx_policyPrefixContext] at h1
    have h2 := hasTyT_relocateN (Γ := Γ) h1
    rw [show (w.ctorParams ++ w.fields).length = (recP w ++ w.fields).length by
      simp only [List.length_append, hplen']] at h2
    exact h2
  have hlevelGap := levelGapConvT hW heqC hwfC hwfL1 hlsC' hkC cfArgs hbodyTy'
  rw [instantiateLevels_sort'] at hlevelGap
  rw [instPrefix_sort] at hlevelGap
  obtain ⟨hctxF⟩ := ctxWfT_telescope hW hΓ hwfL1 hL1len _ lvC hdomsTy (recP w ++ w.fields).length hkP
  obtain ⟨hconvsF⟩ := finChoiceT _ _ (hargConvs w.fields (Nat.le_refl _) fsArgs)
  have hparamGap := convT_instPrefix hW hSL hconst (recP w ++ w.fields) (w.ctorParams ++ w.fields)
    (ΔT := ((((c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters ++
      (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields).map (instantiateLevels (famL1 w))).take
      (recP w ++ w.fields).length).reverse)
    (by simp only [List.length_reverse, List.length_take, List.length_map]; omega)
    (by simp only [List.length_append, hplen'])
    hctxF (.refl _ _ _ hbodyL1) hbodyL1 hconvsF (argsAt_pkgA hkP fsArgs)
  rw [instPrefix_sort] at hparamGap
  have hR1 : TyConvT E n Γ (majorTyW w)
      (instPrefix (recP w ++ w.fields) (instantiateLevels (famL1 w)
        (foldApps (.const c.cell.adm.family.ref (policyFamilyLevels c.cell.adm.family))
          (policyParameterLocals (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters.length
            (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields.length ++
            (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).resultIndices)))) := by
    refine .trans _ _ _ _ (TyConvT.symmT convR) ?_
    rw [hres]
    exact .trans _ _ _ _ (.of _ _ _ _ hlevelGap) (.of _ _ _ _ (.symm _ _ _ _ hparamGap))
  -- (11) ROW 3, recursor side on the left, against the equation's family application
  have hR1form : instPrefix (recP w ++ w.fields) (instantiateLevels (famL1 w)
      (foldApps (.const c.cell.adm.family.ref (policyFamilyLevels c.cell.adm.family))
        (policyParameterLocals (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).parameters.length
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).fields.length ++
          (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).resultIndices))) =
      foldApps (.const c.cell.adm.family.ref (famL1 w)) (recP w ++
        (c.cell.adm.constructorViews ⟨w.ctorIdx, hiv⟩).resultIndices.map
          (fun r => instPrefix (recP w ++ w.fields) (instantiateLevels (famL1 w) r))) := by
    rw [instPrefix_famApp _ _ _ _ _ _ _ (by simp only [List.length_append, hplen, hnp, ← hcpl, hfl]),
      hL1fam, List.take_left' (by rw [hplen, hnp, hcpl])]
  rw [hR1form, hAMform] at hR1
  obtain ⟨_, _, hargs13⟩ := hrows.famAppRow hΓ hfamE c.cell.adm.family.hasClass hAMsort' hR1
  obtain ⟨majorConvT⟩ := majorConv
  -- the data
  refine ⟨⟨⟨w.ctorIdx, hiv⟩, rfl, ?_, majorConvT, ?_⟩⟩
  · intro j f d hf hd
    have h := fsArgs ((recP w).length + j) f d
      (by rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]; exact hf)
      (by rw [List.getElem?_append_right (by rw [hplen, hnp, hcpl]; exact Nat.le_add_right _ _),
        hplen, hnp, hcpl, Nat.add_sub_cancel_left]; exact hd)
    rw [take_append_add, hcongF d (hdomsB d (List.mem_append_right _ (List.getElem?_mem hd)))] at h
    exact h
  · intro j x r d hx hr hd
    have h := convArgsT_instPrefix hargs13 _ _ (hfamPi (famL1 w)) ((recP w).length + j) x
      (instPrefix (recP w ++ w.fields) (instantiateLevels (famL1 w) r))
      (instantiateLevels (famL1 w) d)
      (by rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]; exact hx)
      (by rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        List.getElem?_map, hr]; rfl)
      (by rw [List.getElem?_map, List.getElem?_append_right (by rw [hplen, hnp]; exact Nat.le_add_right _ _),
        show (recP w).length + j - c.cell.adm.family.parameters.length = j by
          rw [hplen, hnp]; exact Nat.add_sub_cancel_left _ _, hd]; rfl)
    rw [take_append_add] at h
    have hrB : exprLevelsBounded c.cell.adm.family.member.arity r = true :=
      hresB r (List.mem_append_right _ (List.getElem?_mem hr))
    have hdB : exprLevelsBounded c.cell.adm.family.member.arity d = true :=
      hfamDomsB d (List.mem_append_right _ (List.getElem?_mem hd))
    rw [hcongF r hrB, hcongF d hdB] at h
    exact h

end Rcic.Declarative
