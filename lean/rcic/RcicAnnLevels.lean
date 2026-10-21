import rcic.RcicAnnLREnv

/-!
# M2-e (6) — level instantiation on the copy: the algebra, and the head step

Polymorphic members (the inductive-class members under `EnvWfA`, every member in
the polymorphic model) are used at level lists `ls`; their types and bodies are
read through `instantiateLevelsA ls`. This file is the syntactic half of what
their semantic clause needs: `instantiateLevelsA` composes on level-bounded
terms (`instantiateLevelsA_instantiateLevelsA`, with `instLevel_instLevel` on
bounded levels), commutes with `instantiateA` (`instantiateLevelsA_instantiateA`,
hence with `instantiate0A`), fixes the literal expansion, preserves level bounds
and `=ₙ`, acts on contexts through the lookups (`instCtxA`,
`lookupTypeA_instCtxA`, `lookupValueA_instCtxA`), and commutes with the head step
on terms whose constants carry their members' arities (`hStepFnA_instLevels`, under
`EnvLevelsA` — members' types and bodies level-bounded by their arity — and
`IotaLevelsA` — the oracle commutes with level instantiation). Typed terms are such
(`hasTyA_constsArity`; hereditary, since the major arm reads an ARGUMENT, M2-f (1)).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) bounded levels and lists -/

/-- every `param i` anywhere in the expression, annotations included, has `i < k`
    (`exprLevelsBounded` on the copy). -/
def exprLevelsBoundedA (k : Nat) : ExprA → Bool
  | .bvar _ => true
  | .sort l => levelBounded k l
  | .const _ ms => levelsBounded k ms
  | .app f x => exprLevelsBoundedA k f && exprLevelsBoundedA k x
  | .lam a u b => exprLevelsBoundedA k a && levelBounded k u && exprLevelsBoundedA k b
  | .pi a u b v => exprLevelsBoundedA k a && levelBounded k u && exprLevelsBoundedA k b && levelBounded k v
  | .letE a w b => exprLevelsBoundedA k a && exprLevelsBoundedA k w && exprLevelsBoundedA k b
  | .lit _ => true

theorem levelsBounded_getElem {n : Nat} :
    (ls : List Level) → levelsBounded n ls = true → (i : Nat) → (hi : i < ls.length) →
    levelBounded n ls[i] = true
  | [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | _ :: _, h, 0, _ => boolAnd_left h
  | _ :: t, h, i + 1, hi => levelsBounded_getElem t (boolAnd_right h) i (Nat.lt_of_succ_lt_succ hi)

/-- instantiation composes on a level bounded by the inner list's length. -/
theorem instLevel_instLevel (ls ms : List Level) :
    (l : Level) → levelBounded ms.length l = true →
    instLevel ls (instLevel ms l) = instLevel (ms.map (instLevel ls)) l
  | .zero, _ => rfl
  | .succ l, h => by
      simp only [instLevel_succ, instLevel_instLevel ls ms l h]
  | .max a b, h => by
      simp only [instLevel_max, instLevel_instLevel ls ms a (boolAnd_left h),
        instLevel_instLevel ls ms b (boolAnd_right h)]
  | .imax a b, h => by
      simp only [instLevel_imax, instLevel_instLevel ls ms a (boolAnd_left h),
        instLevel_instLevel ls ms b (boolAnd_right h)]
  | .param i, h => by
      have hi : i < ms.length := of_decide_eq_true h
      rw [instLevel_param, instLevel_param, List.getElem?_map, List.getElem?_eq_getElem hi]
      rfl

theorem map_instLevel_instLevel (ls ms : List Level) :
    (ns : List Level) → levelsBounded ms.length ns = true →
    (ns.map (instLevel ms)).map (instLevel ls) = ns.map (instLevel (ms.map (instLevel ls)))
  | [], _ => rfl
  | l :: t, h => by
      simp only [List.map, instLevel_instLevel ls ms l (boolAnd_left h),
        map_instLevel_instLevel ls ms t (boolAnd_right h)]

/-- instantiation composes on a level-bounded expression. -/
theorem instantiateLevelsA_instantiateLevelsA (ls ms : List Level) :
    (e : ExprA) → exprLevelsBoundedA ms.length e = true →
    instantiateLevelsA ls (instantiateLevelsA ms e) = instantiateLevelsA (ms.map (instLevel ls)) e
  | .bvar _, _ => rfl
  | .sort l, h => by simp only [instantiateLevelsA, instLevel_instLevel ls ms l h]
  | .const _ ns, h => by simp only [instantiateLevelsA, map_instLevel_instLevel ls ms ns h]
  | .app f x, h => by
      simp only [instantiateLevelsA, instantiateLevelsA_instantiateLevelsA ls ms f (boolAnd_left h),
        instantiateLevelsA_instantiateLevelsA ls ms x (boolAnd_right h)]
  | .lam a u b, h => by
      simp only [instantiateLevelsA,
        instantiateLevelsA_instantiateLevelsA ls ms a (boolAnd_left (boolAnd_left h)),
        instLevel_instLevel ls ms u (boolAnd_right (boolAnd_left h)),
        instantiateLevelsA_instantiateLevelsA ls ms b (boolAnd_right h)]
  | .pi a u b v, h => by
      simp only [instantiateLevelsA,
        instantiateLevelsA_instantiateLevelsA ls ms a (boolAnd_left (boolAnd_left (boolAnd_left h))),
        instLevel_instLevel ls ms u (boolAnd_right (boolAnd_left (boolAnd_left h))),
        instantiateLevelsA_instantiateLevelsA ls ms b (boolAnd_right (boolAnd_left h)),
        instLevel_instLevel ls ms v (boolAnd_right h)]
  | .letE a w b, h => by
      simp only [instantiateLevelsA,
        instantiateLevelsA_instantiateLevelsA ls ms a (boolAnd_left (boolAnd_left h)),
        instantiateLevelsA_instantiateLevelsA ls ms w (boolAnd_right (boolAnd_left h)),
        instantiateLevelsA_instantiateLevelsA ls ms b (boolAnd_right h)]
  | .lit _, _ => rfl

/-! ## (2) instantiation commutes with substitution and fixes the literal expansion -/

theorem instantiateLevelsA_instantiateA (ls : List Level) :
    (e : ExprA) → (idx : Nat) → (v : ExprA) →
    instantiateLevelsA ls (instantiateA idx v e) =
      instantiateA idx (instantiateLevelsA ls v) (instantiateLevelsA ls e)
  | .bvar i, idx, v => by
      by_cases h1 : i = idx
      · simp only [instantiateA, instantiateLevelsA, if_pos h1]
      · by_cases h2 : idx < i
        · simp only [instantiateA, instantiateLevelsA, if_neg h1, if_pos h2]
        · simp only [instantiateA, instantiateLevelsA, if_neg h1, if_neg h2]
  | .sort _, _, _ => rfl
  | .const _ _, _, _ => rfl
  | .app f x, idx, v => by
      simp only [instantiateA, instantiateLevelsA, instantiateLevelsA_instantiateA ls f idx v,
        instantiateLevelsA_instantiateA ls x idx v]
  | .lam a u b, idx, v => by
      simp only [instantiateA, instantiateLevelsA, instantiateLevelsA_instantiateA ls a idx v,
        instantiateLevelsA_instantiateA ls b (idx + 1) (liftA 0 1 v), instantiateLevelsA_liftA]
  | .pi a u b w, idx, v => by
      simp only [instantiateA, instantiateLevelsA, instantiateLevelsA_instantiateA ls a idx v,
        instantiateLevelsA_instantiateA ls b (idx + 1) (liftA 0 1 v), instantiateLevelsA_liftA]
  | .letE a w b, idx, v => by
      simp only [instantiateA, instantiateLevelsA, instantiateLevelsA_instantiateA ls a idx v,
        instantiateLevelsA_instantiateA ls w idx v,
        instantiateLevelsA_instantiateA ls b (idx + 1) (liftA 0 1 v), instantiateLevelsA_liftA]
  | .lit _, _, _ => rfl

theorem instantiateLevelsA_instantiate0A (ls : List Level) (v e : ExprA) :
    instantiateLevelsA ls (instantiate0A v e) =
      instantiate0A (instantiateLevelsA ls v) (instantiateLevelsA ls e) :=
  instantiateLevelsA_instantiateA ls e 0 v

theorem instantiateLevelsA_natExpandA (ls : List Level) :
    (t : Nat) → instantiateLevelsA ls (natExpandA t) = natExpandA t
  | 0 => rfl
  | t + 1 => by
      simp only [natExpandA, litSuccA, instantiateLevelsA, instantiateLevelsA_natExpandA ls t,
        List.map]

/-! ## (3) level bounds and `=ₙ` under instantiation -/

theorem levelBounded_instLevel {n : Nat} {ls : List Level} (hls : levelsBounded n ls = true) :
    (l : Level) → levelBounded ls.length l = true → levelBounded n (instLevel ls l) = true
  | .zero, _ => rfl
  | .succ l, h => by
      simp only [instLevel_succ]; exact levelBounded_instLevel hls l h
  | .max a b, h => by
      simp only [instLevel_max]
      show (levelBounded n (instLevel ls a) && levelBounded n (instLevel ls b)) = true
      rw [levelBounded_instLevel hls a (boolAnd_left h), levelBounded_instLevel hls b (boolAnd_right h)]
      rfl
  | .imax a b, h => by
      simp only [instLevel_imax]
      show (levelBounded n (instLevel ls a) && levelBounded n (instLevel ls b)) = true
      rw [levelBounded_instLevel hls a (boolAnd_left h), levelBounded_instLevel hls b (boolAnd_right h)]
      rfl
  | .param i, h => by
      have hi : i < ls.length := of_decide_eq_true h
      rw [instLevel_param, List.getElem?_eq_getElem hi]
      exact levelsBounded_getElem ls hls i hi

theorem levelsBounded_map_instLevel {n : Nat} {ls : List Level} (hls : levelsBounded n ls = true) :
    (ns : List Level) → levelsBounded ls.length ns = true →
    levelsBounded n (ns.map (instLevel ls)) = true
  | [], _ => rfl
  | l :: t, h => by
      show (levelBounded n (instLevel ls l) && levelsBounded n (t.map (instLevel ls))) = true
      rw [levelBounded_instLevel hls l (boolAnd_left h), levelsBounded_map_instLevel hls t (boolAnd_right h)]
      rfl

theorem eqN_instLevel {l l' : Level} (h : eqN l l') (ls : List Level) :
    eqN (instLevel ls l) (instLevel ls l') := fun ρ => by
  rw [eval_instLevel, eval_instLevel]; exact h _

theorem eqNList_map_instLevel (ls : List Level) :
    (ns ns' : List Level) → eqNList ns ns' → eqNList (ns.map (instLevel ls)) (ns'.map (instLevel ls))
  | [], [], _ => trivial
  | _ :: _, [], h => h.elim
  | [], _ :: _, h => h.elim
  | l :: t, l' :: t', h => ⟨eqN_instLevel h.1 ls, eqNList_map_instLevel ls t t' h.2⟩

/-! ## (4) contexts -/

def instDeclA (ls : List Level) : LocalDeclA → LocalDeclA
  | .assumption a => .assumption (instantiateLevelsA ls a)
  | .letBinding a v => .letBinding (instantiateLevelsA ls a) (instantiateLevelsA ls v)

def instCtxA (ls : List Level) (Γ : LCtxA) : LCtxA := Γ.map (instDeclA ls)

theorem instCtxA_cons (ls : List Level) (d : LocalDeclA) (Γ : LCtxA) :
    instCtxA ls (d :: Γ) = instDeclA ls d :: instCtxA ls Γ := rfl

theorem lookupTypeA_instCtxA (ls : List Level) (Γ : LCtxA) (i : Nat) :
    lookupTypeA (instCtxA ls Γ) i = (lookupTypeA Γ i).map (instantiateLevelsA ls) := by
  unfold lookupTypeA instCtxA
  rw [List.get?_map]
  cases Γ.get? i with
  | none => rfl
  | some d =>
      cases d with
      | assumption a => simp only [Option.map, instDeclA, instantiateLevelsA_liftA]
      | letBinding a v => simp only [Option.map, instDeclA, instantiateLevelsA_liftA]

theorem lookupValueA_instCtxA (ls : List Level) (Γ : LCtxA) (i : Nat) :
    lookupValueA (instCtxA ls Γ) i = (lookupValueA Γ i).map (instantiateLevelsA ls) := by
  unfold lookupValueA instCtxA
  rw [List.get?_map]
  cases Γ.get? i with
  | none => rfl
  | some d =>
      cases d with
      | assumption a => simp only [Option.map, instDeclA]
      | letBinding a v => simp only [Option.map, instDeclA, instantiateLevelsA_liftA]

/-! ## (5) the head step commutes with instantiation -/

/-- members' types and bodies are level-bounded by their arity. -/
def EnvLevelsA (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m →
    exprLevelsBoundedA m.arity m.mtypeA = true ∧
    (∀ b, m.bodyA = some b → exprLevelsBoundedA m.arity b = true)

/-- every constructor member's `normA`, when it carries one, is level-bounded at the member's
    arity (R-NoDeltaRec-3b): the `EnvLevelsA` twin of `EnvNormClosedA` (the ι read-back's levels
    side, for `iotaFnA_levels`). -/
def EnvNormLevelsA (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m → m.mclass = .constructorM →
    ∀ T, m.normA = some T → exprLevelsBoundedA m.arity T = true

/-- the ι oracle commutes with level instantiation (05's ι fires on constructor
    shapes, which instantiation preserves; heads are unchanged, so no collapse
    with `IotaConstHeadA`). -/
def IotaLevelsA (I : IotaIfaceA) : Prop :=
  ∀ (ls : List Level) (e : ExprA), I.fn (instantiateLevelsA ls e) = (I.fn e).map (instantiateLevelsA ls)

theorem noIotaA_levels : IotaLevelsA noIotaA := fun _ _ => rfl

/-- every constant occurrence carries the arity of its member — hereditary, since
    R-MajorStep's arm reads the ARGUMENT of a spine (M2-f (1); until then the head
    alone, `HeadOkA`). -/
def ConstsArityA (E : ResolvedEnvA) : ExprA → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const r ms => ∃ m, E.members r = some m ∧ ms.length = m.arity
  | .app f x => ConstsArityA E f ∧ ConstsArityA E x
  | .lam a _ b => ConstsArityA E a ∧ ConstsArityA E b
  | .pi a _ b _ => ConstsArityA E a ∧ ConstsArityA E b
  | .letE a w b => ConstsArityA E a ∧ ConstsArityA E w ∧ ConstsArityA E b
  | .lit _ => True

/-- the spine under level instantiation: the head instantiated, the arguments mapped. -/
theorem appsSpineA_instLevels (ls : List Level) : (e : ExprA) →
    appsSpineA (instantiateLevelsA ls e) =
      (instantiateLevelsA ls (appsSpineA e).1, (appsSpineA e).2.map (instantiateLevelsA ls))
  | .app f x => by
      show appsSpineA (.app (instantiateLevelsA ls f) (instantiateLevelsA ls x)) = _
      simp only [appsSpineA, appsSpineA_instLevels ls f, List.map_append, List.map_cons, List.map_nil]
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .lam _ _ _ => rfl
  | .pi _ _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- the major arm reads the spine's shape and the head's member, which instantiation keeps. -/
theorem recAtMajorA_instLevels (E : ResolvedEnvA) (ls : List Level) (f : ExprA) :
    recAtMajorA E (instantiateLevelsA ls f) = recAtMajorA E f := by
  unfold recAtMajorA
  rw [appsSpineA_instLevels ls f, List.length_map]
  cases (appsSpineA f).1 <;> rfl

/-- W-1 (e): the struct head and the struct position read the spine's head, whose member level
    instantiation keeps. -/
theorem structHeadA_instLevels (E : ResolvedEnvA) (ls : List Level) (f : ExprA) :
    structHeadA E (instantiateLevelsA ls f) = structHeadA E f := by
  unfold structHeadA
  rw [appsSpineA_instLevels ls f]
  cases (appsSpineA f).1 <;> rfl

theorem structPosA_instLevels (E : ResolvedEnvA) (ls : List Level) (f : ExprA) :
    structPosA E (instantiateLevelsA ls f) = structPosA E f := by
  unfold structPosA; rw [recAtMajorA_instLevels, structHeadA_instLevels]

theorem unitHeadA_instLevels (E : ResolvedEnvA) (ls : List Level) : (h : ExprA) →
    unitHeadA E (instantiateLevelsA ls h) = unitHeadA E h
  | .const _ _ => rfl
  | .bvar _ => rfl
  | .sort _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .pi _ _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- the K-unit arm reads the head's member and the last argument, which instantiation keeps and maps. -/
theorem unitMinorA_instLevels (E : ResolvedEnvA) (ls : List Level) :
    (f : ExprA) → unitMinorA E (instantiateLevelsA ls f) = (unitMinorA E f).map (instantiateLevelsA ls)
  | .app g mn => by
      show (if unitHeadA E (appsSpineA (instantiateLevelsA ls g)).1 then some (instantiateLevelsA ls mn)
          else none) = (if unitHeadA E (appsSpineA g).1 then some mn else none).map (instantiateLevelsA ls)
      rw [appsSpineA_instLevels ls g]
      dsimp only
      rw [unitHeadA_instLevels E ls]
      cases unitHeadA E (appsSpineA g).1 <;> rfl
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .lam _ _ _ => rfl
  | .pi _ _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-! W-1 (a): the struct arm commutes with level instantiation — it reads the recursor's level-bounded
    type at the spine's levels, and the motive's level it sets to zero is fixed by instantiation. -/

theorem constsArityA_head {E : ResolvedEnvA} : (e : ExprA) → ConstsArityA E e →
    ∀ {r : Nat} {ms : List Level}, (appsSpineA e).1 = .const r ms →
      ∃ m, E.members r = some m ∧ ms.length = m.arity
  | .const r' ms', h, r, ms, hsp => by
      have hsp' : ExprA.const r' ms' = .const r ms := hsp
      injection hsp' with e1 e2
      subst e1 e2
      exact h
  | .app f _, h, _, _, hsp => constsArityA_head f h.1 hsp
  | .bvar _, _, _, _, hsp => ExprA.noConfusion hsp
  | .sort _, _, _, _, hsp => ExprA.noConfusion hsp
  | .lam _ _ _, _, _, _, hsp => ExprA.noConfusion hsp
  | .pi _ _ _ _, _, _, _, hsp => ExprA.noConfusion hsp
  | .letE _ _ _, _, _, _, hsp => ExprA.noConfusion hsp
  | .lit _, _, _, _, hsp => ExprA.noConfusion hsp

theorem applyTelA_instLevels (ls : List Level) : (xs : List ExprA) → (T : ExprA) →
    applyTelA (xs.map (instantiateLevelsA ls)) (instantiateLevelsA ls T) =
      (applyTelA xs T).map (instantiateLevelsA ls)
  | [], _ => rfl
  | x :: xs, .pi D u B v => by
      show applyTelA (xs.map (instantiateLevelsA ls))
          (instantiate0A (instantiateLevelsA ls x) (instantiateLevelsA ls B)) =
        (applyTelA xs (instantiate0A x B)).map (instantiateLevelsA ls)
      rw [← instantiateLevelsA_instantiate0A]
      exact applyTelA_instLevels ls xs _
  | _ :: _, .bvar _ => rfl
  | _ :: _, .sort _ => rfl
  | _ :: _, .const _ _ => rfl
  | _ :: _, .app _ _ => rfl
  | _ :: _, .lam _ _ _ => rfl
  | _ :: _, .letE _ _ _ => rfl
  | _ :: _, .lit _ => rfl

theorem piCountA_instLevels (ls : List Level) : (T : ExprA) →
    piCountA (instantiateLevelsA ls T) = piCountA T
  | .pi _ _ B _ => by
      show piCountA (instantiateLevelsA ls B) + 1 = piCountA B + 1
      rw [piCountA_instLevels ls B]
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

theorem piDomListA_instLevels (ls : List Level) : (T : ExprA) →
    piDomListA (instantiateLevelsA ls T) = instDomsA ls (piDomListA T)
  | .pi D u B _ => by
      show (instantiateLevelsA ls D, instLevel ls u) :: piDomListA (instantiateLevelsA ls B) =
        (instantiateLevelsA ls D, instLevel ls u) :: instDomsA ls (piDomListA B)
      rw [piDomListA_instLevels ls B]
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

theorem lamTelA_instLevels (ls : List Level) : (ds : List (ExprA × Level)) → (b : ExprA) →
    instantiateLevelsA ls (lamTelA ds b) = lamTelA (instDomsA ls ds) (instantiateLevelsA ls b)
  | [], _ => rfl
  | (D, u) :: ds, b => by
      show ExprA.lam (instantiateLevelsA ls D) (instLevel ls u) (instantiateLevelsA ls (lamTelA ds b)) =
        ExprA.lam (instantiateLevelsA ls D) (instLevel ls u)
          (lamTelA (instDomsA ls ds) (instantiateLevelsA ls b))
      rw [lamTelA_instLevels ls ds b]

theorem fieldSelA_instLevels (ls : List Level) (ds : List (ExprA × Level)) (i : Nat) :
    instantiateLevelsA ls (fieldSelA ds i) = fieldSelA (instDomsA ls ds) i := by
  unfold fieldSelA
  rw [lamTelA_instLevels]
  have hl : (instDomsA ls ds).length = ds.length := List.length_map _ _
  rw [hl]
  rfl

theorem structProjA_instLevels (ls : List Level) (r : Nat) (ls₀ : List Level) (ps : List ExprA)
    (S : ExprA) (uS : Level) (ds : List (ExprA × Level)) (x : ExprA) (i : Nat) (F : ExprA) :
    instantiateLevelsA ls (structProjA r ls₀ ps S uS ds x i F) =
      structProjA r (ls₀.map (instLevel ls)) (ps.map (instantiateLevelsA ls)) (instantiateLevelsA ls S)
        (instLevel ls uS) (instDomsA ls ds) (instantiateLevelsA ls x) i (instantiateLevelsA ls F) := by
  have hlam : instantiateLevelsA ls (ExprA.lam S uS (liftA 0 1 F)) =
      .lam (instantiateLevelsA ls S) (instLevel ls uS) (liftA 0 1 (instantiateLevelsA ls F)) := by
    show ExprA.lam (instantiateLevelsA ls S) (instLevel ls uS) (instantiateLevelsA ls (liftA 0 1 F)) = _
    rw [instantiateLevelsA_liftA]
  unfold structProjA
  rw [instantiateLevelsA_foldAppsA, List.map_append]
  simp only [List.map_cons, List.map_nil, hlam, fieldSelA_instLevels]
  rfl

theorem structProjsA_instLevels (ls : List Level) (r : Nat) (ls₀ : List Level) (ps : List ExprA)
    (S : ExprA) (uS : Level) (ds : List (ExprA × Level)) (x : ExprA) : (k i : Nat) → (T : ExprA) →
    structProjsA r (ls₀.map (instLevel ls)) (ps.map (instantiateLevelsA ls)) (instantiateLevelsA ls S)
        (instLevel ls uS) (instDomsA ls ds) (instantiateLevelsA ls x) k i (instantiateLevelsA ls T) =
      (structProjsA r ls₀ ps S uS ds x k i T).map (instantiateLevelsA ls)
  | 0, _, _ => rfl
  | k + 1, i, .pi F u B v => by
      show structProjA r (ls₀.map (instLevel ls)) (ps.map (instantiateLevelsA ls)) (instantiateLevelsA ls S)
            (instLevel ls uS) (instDomsA ls ds) (instantiateLevelsA ls x) i (instantiateLevelsA ls F) ::
          structProjsA r (ls₀.map (instLevel ls)) (ps.map (instantiateLevelsA ls)) (instantiateLevelsA ls S)
            (instLevel ls uS) (instDomsA ls ds) (instantiateLevelsA ls x) k (i + 1)
            (instantiate0A (structProjA r (ls₀.map (instLevel ls)) (ps.map (instantiateLevelsA ls))
              (instantiateLevelsA ls S) (instLevel ls uS) (instDomsA ls ds) (instantiateLevelsA ls x) i
              (instantiateLevelsA ls F)) (instantiateLevelsA ls B)) = _
      rw [← structProjA_instLevels, ← instantiateLevelsA_instantiate0A,
        structProjsA_instLevels ls r ls₀ ps S uS ds x k (i + 1)]
      rfl
  | _ + 1, _, .bvar _ => rfl
  | _ + 1, _, .sort _ => rfl
  | _ + 1, _, .const _ _ => rfl
  | _ + 1, _, .app _ _ => rfl
  | _ + 1, _, .lam _ _ _ => rfl
  | _ + 1, _, .letE _ _ _ => rfl
  | _ + 1, _, .lit _ => rfl

theorem take_instDomsA (ls : List Level) (ds : List (ExprA × Level)) (k : Nat) :
    (instDomsA ls ds).take k = instDomsA ls (ds.take k) :=
  (List.map_take _ ds k).symm

/-- level instantiation on what the struct arm reads. -/
def StructSpineA.instS (ls : List Level) (d : StructSpineA) : StructSpineA :=
  ⟨d.r, d.ls₀.map (instLevel ls), d.ps.map (instantiateLevelsA ls), instantiateLevelsA ls d.S,
    instLevel ls d.uS, instantiateLevelsA ls d.Dm, instantiateLevelsA ls d.mn, d.nf⟩

theorem StructSpineA.reduct_instLevels (ls : List Level) (d : StructSpineA) (x : ExprA) :
    (d.instS ls).reduct (instantiateLevelsA ls x) = instantiateLevelsA ls (d.reduct x) := by
  unfold StructSpineA.reduct StructSpineA.instS
  dsimp only
  rw [instantiateLevelsA_foldAppsA, piDomListA_instLevels, take_instDomsA, structProjsA_instLevels]

/-- the motive's level set to zero commutes with instantiation: zero is fixed. -/
theorem motZeroLevelsA_map (ls ms : List Level) :
    motZeroLevelsA (ms.map (instLevel ls)) = (motZeroLevelsA ms).map (instLevel ls) := by
  unfold motZeroLevelsA
  rw [List.map_set, List.length_map]
  rfl

/-- the struct arm's reading commutes with level instantiation, when the spine's head constant carries its
    member's arity (all the reading instantiates). -/
theorem structSpineA_instLevels_head {E : ResolvedEnvA} (hEL : EnvLevelsA E) (ls : List Level) :
    (f : ExprA) → (∀ r ms, (appsSpineA f).1 = .const r ms → ∃ m, E.members r = some m ∧ ms.length = m.arity) →
    structSpineA E (instantiateLevelsA ls f) = (structSpineA E f).map (StructSpineA.instS ls)
  | .app g mn, hok => by
      show structSpineA E (.app (instantiateLevelsA ls g) (instantiateLevelsA ls mn)) =
        (structSpineA E (.app g mn)).map _
      dsimp only [structSpineA]
      rw [appsSpineA_instLevels ls g]
      dsimp only
      cases hh : (appsSpineA g).1 with
      | const r ms =>
          obtain ⟨m₀, hm₀, hlen⟩ := hok r ms hh
          dsimp only [instantiateLevelsA]
          rw [hm₀]
          dsimp only
          cases hs : structGroupA r m₀ with
          | false => rfl
          | true =>
              simp only [if_true]
              rw [← instantiateLevelsA_instantiateLevelsA ls ms m₀.mtypeA
                (by rw [hlen]; exact (hEL r m₀ hm₀).1)]
              have hA := applyTelA_instLevels ls (appsSpineA g).2 (instantiateLevelsA ms m₀.mtypeA)
              rw [hA]
              cases ha : applyTelA (appsSpineA g).2 (instantiateLevelsA ms m₀.mtypeA) with
              | none => rfl
              | some T =>
                  simp only [Option.map_some']
                  cases T with
                  | pi Dm u B v =>
                      show (match instantiate0A (instantiateLevelsA ls mn) (instantiateLevelsA ls B) with
                        | .pi S uS _ _ => some (⟨r, motZeroLevelsA (ms.map (instLevel ls)),
                            ((appsSpineA g).2.map (instantiateLevelsA ls)).dropLast, S, uS,
                            instantiateLevelsA ls Dm, instantiateLevelsA ls mn,
                            structFieldCountA m₀⟩ : StructSpineA)
                        | _ => none) = Option.map (StructSpineA.instS ls) (match instantiate0A mn B with
                        | .pi S uS _ _ => some ⟨r, motZeroLevelsA ms, (appsSpineA g).2.dropLast, S, uS, Dm, mn,
                            structFieldCountA m₀⟩
                        | _ => none)
                      rw [← instantiateLevelsA_instantiate0A]
                      cases hB : instantiate0A mn B with
                      | pi S uS C w =>
                          show some _ = some _
                          simp only [StructSpineA.instS, List.map_dropLast, motZeroLevelsA_map]
                      | bvar _ => rfl
                      | sort _ => rfl
                      | const _ _ => rfl
                      | app _ _ => rfl
                      | lam _ _ _ => rfl
                      | letE _ _ _ => rfl
                      | lit _ => rfl
                  | bvar _ => rfl
                  | sort _ => rfl
                  | const _ _ => rfl
                  | app _ _ => rfl
                  | lam _ _ _ => rfl
                  | letE _ _ _ => rfl
                  | lit _ => rfl
      | bvar _ => rfl
      | sort _ => rfl
      | app _ _ => rfl
      | lam _ _ _ => rfl
      | pi _ _ _ _ => rfl
      | letE _ _ _ => rfl
      | lit _ => rfl
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .lam _ _ _, _ => rfl
  | .pi _ _ _ _, _ => rfl
  | .letE _ _ _, _ => rfl
  | .lit _, _ => rfl

theorem structSpineA_instLevels {E : ResolvedEnvA} (hEL : EnvLevelsA E) (ls : List Level) (f : ExprA)
    (hok : ConstsArityA E f) :
    structSpineA E (instantiateLevelsA ls f) = (structSpineA E f).map (StructSpineA.instS ls) :=
  structSpineA_instLevels_head hEL ls f (fun _ _ hh => constsArityA_head f hok hh)

/-- THE STRUCT ARM COMMUTES WITH LEVEL INSTANTIATION, on a spine whose head constant carries its arity. -/
theorem structArmA_instLevels_head {E : ResolvedEnvA} (hEL : EnvLevelsA E) (ls : List Level) (f x : ExprA)
    (hok : ∀ r ms, (appsSpineA f).1 = .const r ms → ∃ m, E.members r = some m ∧ ms.length = m.arity) :
    structArmA E (instantiateLevelsA ls f) (instantiateLevelsA ls x) =
      (structArmA E f x).map (instantiateLevelsA ls) := by
  unfold structArmA
  rw [structSpineA_instLevels_head hEL ls f hok]
  cases structSpineA E f with
  | none => rfl
  | some d =>
      show (if d.nf ≤ piCountA (instantiateLevelsA ls d.Dm) then
          some ((d.instS ls).reduct (instantiateLevelsA ls x)) else none) =
        Option.map (instantiateLevelsA ls) (if d.nf ≤ piCountA d.Dm then some (d.reduct x) else none)
      rw [piCountA_instLevels]
      by_cases hn : d.nf ≤ piCountA d.Dm
      · rw [if_pos hn, if_pos hn, StructSpineA.reduct_instLevels ls d x]; rfl
      · rw [if_neg hn, if_neg hn]; rfl

/-- THE STRUCT ARM COMMUTES WITH LEVEL INSTANTIATION, on a spine whose constants carry their arity. -/
theorem structArmA_instLevels {E : ResolvedEnvA} (hEL : EnvLevelsA E) (ls : List Level) (f x : ExprA)
    (hok : ConstsArityA E f) :
    structArmA E (instantiateLevelsA ls f) (instantiateLevelsA ls x) =
      (structArmA E f x).map (instantiateLevelsA ls) :=
  structArmA_instLevels_head hEL ls f x (fun _ _ hh => constsArityA_head f hok hh)

section Step
variable {E : ResolvedEnvA} {I : IotaIfaceA}

theorem hStepFnA_instLevels_app (hIL : IotaLevelsA I) {ls : List Level} {Γ : LCtxA} {f : ExprA}
    (x : ExprA) (hnl : ∀ A u b, f ≠ .lam A u b)
    (hnl' : ∀ A u b, instantiateLevelsA ls f ≠ .lam A u b)
    (hf : hStepFnA E I.fn (instCtxA ls Γ) (instantiateLevelsA ls f) =
      (hStepFnA E I.fn Γ f).map (instantiateLevelsA ls))
    (hx : hStepFnA E I.fn (instCtxA ls Γ) (instantiateLevelsA ls x) =
      (hStepFnA E I.fn Γ x).map (instantiateLevelsA ls))
    (hs : structArmA E (instantiateLevelsA ls f) (instantiateLevelsA ls x) =
      (structArmA E f x).map (instantiateLevelsA ls)) :
    hStepFnA E I.fn (instCtxA ls Γ) (.app (instantiateLevelsA ls f) (instantiateLevelsA ls x)) =
      (hStepFnA E I.fn Γ (.app f x)).map (instantiateLevelsA ls) := by
  rw [hStepFnA_app_nonlam E I.fn _ _ hnl', hStepFnA_app_nonlam E I.fn Γ x hnl, hf]
  cases hStepFnA E I.fn Γ f with
  | some f' => rfl
  | none =>
      dsimp only
      rw [structPosA_instLevels E ls f]
      cases structPosA E f with
      | true => exact hs
      | false =>
          have hfn : I.fn (.app (instantiateLevelsA ls f) (instantiateLevelsA ls x)) =
              (I.fn (.app f x)).map (instantiateLevelsA ls) := hIL ls (.app f x)
          rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hfn]
          cases I.fn (.app f x) with
          | some e' => rfl
          | none =>
              rw [recAtMajorA_instLevels E ls f, unitMinorA_instLevels E ls f, hx]
              cases recAtMajorA E f <;> cases unitMinorA E f <;> cases hStepFnA E I.fn Γ x <;> rfl

theorem hStepFnA_instLevels (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (ls : List Level) (Γ : LCtxA) :
    (e : ExprA) → ConstsArityA E e →
    hStepFnA E I.fn (instCtxA ls Γ) (instantiateLevelsA ls e) =
      (hStepFnA E I.fn Γ e).map (instantiateLevelsA ls)
  | .bvar i, _ => by
      show lookupValueA (instCtxA ls Γ) i = (lookupValueA Γ i).map (instantiateLevelsA ls)
      exact lookupValueA_instCtxA ls Γ i
  | .sort _, _ => rfl
  | .lam _ _ _, _ => rfl
  | .pi _ _ _ _, _ => rfl
  | .lit t, _ => by
      show some (natExpandA t) = some (instantiateLevelsA ls (natExpandA t))
      rw [instantiateLevelsA_natExpandA]
  | .letE a w b, _ => by
      show some (instantiate0A (instantiateLevelsA ls w) (instantiateLevelsA ls b)) =
        some (instantiateLevelsA ls (instantiate0A w b))
      rw [instantiateLevelsA_instantiate0A]
  | .const r ms, hok => by
      obtain ⟨m, hm, hlen⟩ := hok
      show (match E.members r with
          | some m => if transparent m.mclass = true then
              m.bodyA.map (instantiateLevelsA (ms.map (instLevel ls))) else none
          | none => none) =
        (match E.members r with
          | some m => if transparent m.mclass = true then m.bodyA.map (instantiateLevelsA ms) else none
          | none => none).map (instantiateLevelsA ls)
      rw [hm]
      show (if transparent m.mclass = true then
          m.bodyA.map (instantiateLevelsA (ms.map (instLevel ls))) else none) =
        (if transparent m.mclass = true then m.bodyA.map (instantiateLevelsA ms) else none).map
          (instantiateLevelsA ls)
      cases transparent m.mclass with
      | false => rfl
      | true =>
          cases hb : m.bodyA with
          | none => rfl
          | some b =>
              show some (instantiateLevelsA (ms.map (instLevel ls)) b) =
                some (instantiateLevelsA ls (instantiateLevelsA ms b))
              rw [instantiateLevelsA_instantiateLevelsA ls ms b (by rw [hlen]; exact (hEL r m hm).2 b hb)]
  | .app (.lam A u body) arg, _ => by
      show some (instantiate0A (instantiateLevelsA ls arg) (instantiateLevelsA ls body)) =
        some (instantiateLevelsA ls (instantiate0A arg body))
      rw [instantiateLevelsA_instantiate0A]
  | .app (.bvar i) x, hok =>
      hStepFnA_instLevels_app hIL x (fun _ _ _ h => ExprA.noConfusion h)
        (fun _ _ _ h => ExprA.noConfusion h) (hStepFnA_instLevels hEL hIL ls Γ (.bvar i) hok.1)
        (hStepFnA_instLevels hEL hIL ls Γ x hok.2) (structArmA_instLevels hEL ls _ x hok.1)
  | .app (.sort l) x, hok =>
      hStepFnA_instLevels_app hIL x (fun _ _ _ h => ExprA.noConfusion h)
        (fun _ _ _ h => ExprA.noConfusion h) (hStepFnA_instLevels hEL hIL ls Γ (.sort l) hok.1)
        (hStepFnA_instLevels hEL hIL ls Γ x hok.2) (structArmA_instLevels hEL ls _ x hok.1)
  | .app (.const r ms) x, hok =>
      hStepFnA_instLevels_app hIL x (fun _ _ _ h => ExprA.noConfusion h)
        (fun _ _ _ h => ExprA.noConfusion h) (hStepFnA_instLevels hEL hIL ls Γ (.const r ms) hok.1)
        (hStepFnA_instLevels hEL hIL ls Γ x hok.2) (structArmA_instLevels hEL ls _ x hok.1)
  | .app (.app g y) x, hok =>
      hStepFnA_instLevels_app hIL x (fun _ _ _ h => ExprA.noConfusion h)
        (fun _ _ _ h => ExprA.noConfusion h) (hStepFnA_instLevels hEL hIL ls Γ (.app g y) hok.1)
        (hStepFnA_instLevels hEL hIL ls Γ x hok.2) (structArmA_instLevels hEL ls _ x hok.1)
  | .app (.pi a u b v) x, hok =>
      hStepFnA_instLevels_app hIL x (fun _ _ _ h => ExprA.noConfusion h)
        (fun _ _ _ h => ExprA.noConfusion h) (hStepFnA_instLevels hEL hIL ls Γ (.pi a u b v) hok.1)
        (hStepFnA_instLevels hEL hIL ls Γ x hok.2) (structArmA_instLevels hEL ls _ x hok.1)
  | .app (.letE a w b) x, hok =>
      hStepFnA_instLevels_app hIL x (fun _ _ _ h => ExprA.noConfusion h)
        (fun _ _ _ h => ExprA.noConfusion h) (hStepFnA_instLevels hEL hIL ls Γ (.letE a w b) hok.1)
        (hStepFnA_instLevels hEL hIL ls Γ x hok.2) (structArmA_instLevels hEL ls _ x hok.1)
  | .app (.lit t) x, hok =>
      hStepFnA_instLevels_app hIL x (fun _ _ _ h => ExprA.noConfusion h)
        (fun _ _ _ h => ExprA.noConfusion h) (hStepFnA_instLevels hEL hIL ls Γ (.lit t) hok.1)
        (hStepFnA_instLevels hEL hIL ls Γ x hok.2) (structArmA_instLevels hEL ls _ x hok.1)

/-- every constant of a typed term carries its member's arity (every constant has
    a `const` leaf, with `hlen`). -/
theorem hasTyA_constsArity {n : Nat} :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E I n Γ e A → ConstsArityA E e
  | _, _, _, .sort _ _ => trivial
  | _, _, _, .bvar _ _ _ _ _ _ => trivial
  | _, _, _, .const _ _ _ m _ hres hlen _ _ => ⟨m, hres, hlen⟩
  | _, _, _, .pi _ _ _ _ _ hA hB => ⟨hasTyA_constsArity hA, hasTyA_constsArity hB⟩
  | _, _, _, .lam _ _ _ _ _ _ hA _ hbody => ⟨hasTyA_constsArity hA, hasTyA_constsArity hbody⟩
  | _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf ha => ⟨hasTyA_constsArity hf, hasTyA_constsArity ha⟩
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv _ hb =>
      ⟨hasTyA_constsArity hA, hasTyA_constsArity hv, hasTyA_constsArity hb⟩
  | _, _, _, .lit _ _ _ _ => trivial
  | _, _, _, .conv _ _ _ _ _ _ h _ _ _ _ => hasTyA_constsArity h

end Step

/-! ## (6) the judgments under level instantiation

A derivation at universe arity `a` instantiated at a bounded level list `ls` of
length `a` is a derivation at arity `n`: `HasTyA E I a Γ e A → HasTyA E I n
(instCtxA ls Γ) (instantiateLevelsA ls e) (instantiateLevelsA ls A)`, and the
same for `ConvA`. Every rule is re-applied under instantiation; the `const` /
`delta` / `consts` rules compose the instantiations on the member's level-bounded
type and body (`EnvLevelsA`), the ι rule goes through `hStepFnA_instLevels` on
its typed redex (`hasTyA_constsArity`) and `IotaLevelsA`, the `sorts` / `conv` /
`tyConv` rules carry `=ₙ` through `eqN_instLevel`. -/

section Inst
variable {E : ResolvedEnvA} {I : IotaIfaceA}

theorem instCtxA_lookupType {ls : List Level} {Γ : LCtxA} {i : Nat} {A : ExprA}
    (h : lookupTypeA Γ i = some A) :
    lookupTypeA (instCtxA ls Γ) i = some (instantiateLevelsA ls A) := by
  rw [lookupTypeA_instCtxA, h]; rfl

theorem instCtxA_lookupValue {ls : List Level} {Γ : LCtxA} {i : Nat} {v : ExprA}
    (h : lookupValueA Γ i = some v) :
    lookupValueA (instCtxA ls Γ) i = some (instantiateLevelsA ls v) := by
  rw [lookupValueA_instCtxA, h]; rfl

/-- the member's type, instantiated twice, instantiated once. -/
theorem instLevels_mtype (hEL : EnvLevelsA E) {r : Nat} {m : CheckedMemberA}
    (hres : E.members r = some m) {ms : List Level} (hlen : ms.length = m.arity) (ls : List Level) :
    instantiateLevelsA ls (instantiateLevelsA ms m.mtypeA) =
      instantiateLevelsA (ms.map (instLevel ls)) m.mtypeA :=
  instantiateLevelsA_instantiateLevelsA ls ms m.mtypeA (by rw [hlen]; exact (hEL r m hres).1)

theorem instLevels_mbody (hEL : EnvLevelsA E) {r : Nat} {m : CheckedMemberA} {b : ExprA}
    (hres : E.members r = some m) (hb : m.bodyA = some b) {ms : List Level}
    (hlen : ms.length = m.arity) (ls : List Level) :
    instantiateLevelsA ls (instantiateLevelsA ms b) = instantiateLevelsA (ms.map (instLevel ls)) b :=
  instantiateLevelsA_instantiateLevelsA ls ms b (by rw [hlen]; exact (hEL r m hres).2 b hb)

theorem length_map_arity {ms : List Level} {m : CheckedMemberA} (hlen : ms.length = m.arity)
    (f : Level → Level) : (ms.map f).length = m.arity := by
  rw [List.length_map]; exact hlen

theorem levelsBounded_inst {a n : Nat} {ls : List Level} (hls : levelsBounded n ls = true)
    (hlen : ls.length = a) {ms : List Level} (hwf : levelsBounded a ms = true) :
    levelsBounded n (ms.map (instLevel ls)) = true :=
  levelsBounded_map_instLevel hls ms (by rw [hlen]; exact hwf)

mutual

def hasTyA_instLevels (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) {a n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) :
    {Γ : LCtxA} → {e A : ExprA} → HasTyA E I a Γ e A →
    HasTyA E I n (instCtxA ls Γ) (instantiateLevelsA ls e) (instantiateLevelsA ls A)
  | _, _, _, .sort Γ l => .sort (instCtxA ls Γ) (instLevel ls l)
  | _, _, _, .bvar Γ i A u h hA =>
      .bvar (instCtxA ls Γ) i (instantiateLevelsA ls A) (instLevel ls u) (instCtxA_lookupType h)
        (hasTyA_instLevels hEL hIL hls hlen hA)
  | _, _, _, .const Γ r ms m u hres hlen' hwf hT => by
      have hT' := hasTyA_instLevels hEL hIL hls hlen hT
      rw [instLevels_mtype hEL hres hlen' ls] at hT'
      show HasTyA E I n (instCtxA ls Γ) (.const r (ms.map (instLevel ls)))
        (instantiateLevelsA ls (instantiateLevelsA ms m.mtypeA))
      rw [instLevels_mtype hEL hres hlen' ls]
      exact .const _ r _ m (instLevel ls u) hres (length_map_arity hlen' _)
        (levelsBounded_inst hls hlen hwf) hT'
  | _, _, _, .pi Γ A u B v hA hB =>
      .pi (instCtxA ls Γ) (instantiateLevelsA ls A) (instLevel ls u) (instantiateLevelsA ls B)
        (instLevel ls v) (hasTyA_instLevels hEL hIL hls hlen hA) (hasTyA_instLevels hEL hIL hls hlen hB)
  | _, _, _, .lam Γ A u body B v hA hB hbody =>
      .lam (instCtxA ls Γ) (instantiateLevelsA ls A) (instLevel ls u) (instantiateLevelsA ls body)
        (instantiateLevelsA ls B) (instLevel ls v) (hasTyA_instLevels hEL hIL hls hlen hA)
        (hasTyA_instLevels hEL hIL hls hlen hB) (hasTyA_instLevels hEL hIL hls hlen hbody)
  | _, _, _, .app Γ f a A B u v w hB hTy hf ha => by
      have hTy' := hasTyA_instLevels hEL hIL hls hlen hTy
      rw [instantiateLevelsA_instantiate0A] at hTy'
      show HasTyA E I n (instCtxA ls Γ) (.app (instantiateLevelsA ls f) (instantiateLevelsA ls a))
        (instantiateLevelsA ls (instantiate0A a B))
      rw [instantiateLevelsA_instantiate0A]
      exact .app _ _ _ (instantiateLevelsA ls A) _ (instLevel ls u) (instLevel ls v) (instLevel ls w)
        (hasTyA_instLevels hEL hIL hls hlen hB) hTy' (hasTyA_instLevels hEL hIL hls hlen hf)
        (hasTyA_instLevels hEL hIL hls hlen ha)
  | _, _, _, .letE Γ A u w value B body hA hv hTy hb => by
      have hTy' := hasTyA_instLevels hEL hIL hls hlen hTy
      rw [instantiateLevelsA_instantiate0A] at hTy'
      show HasTyA E I n (instCtxA ls Γ)
        (.letE (instantiateLevelsA ls A) (instantiateLevelsA ls value) (instantiateLevelsA ls body))
        (instantiateLevelsA ls (instantiate0A value B))
      rw [instantiateLevelsA_instantiate0A]
      exact .letE _ _ (instLevel ls u) (instLevel ls w) _ (instantiateLevelsA ls B) _
        (hasTyA_instLevels hEL hIL hls hlen hA) (hasTyA_instLevels hEL hIL hls hlen hv) hTy'
        (hasTyA_instLevels hEL hIL hls hlen hb)
  | _, _, _, .lit Γ t T hexp => by
      have h' := hasTyA_instLevels hEL hIL hls hlen hexp
      rw [instantiateLevelsA_natExpandA] at h'
      exact .lit _ t _ h'
  | _, _, _, .conv Γ e A B l u h hAl hlu hB hc =>
      .conv (instCtxA ls Γ) _ (instantiateLevelsA ls A) _ (instLevel ls l) (instLevel ls u)
        (hasTyA_instLevels hEL hIL hls hlen h) (hasTyA_instLevels hEL hIL hls hlen hAl)
        (eqN_instLevel hlu ls) (hasTyA_instLevels hEL hIL hls hlen hB)
        (convA_instLevels hEL hIL hls hlen hc)

def convA_instLevels (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) {a n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) :
    {Γ : LCtxA} → {x y A : ExprA} → ConvA E I a Γ x y A →
    ConvA E I n (instCtxA ls Γ) (instantiateLevelsA ls x) (instantiateLevelsA ls y)
      (instantiateLevelsA ls A)
  | _, _, _, _, .refl Γ x A h => .refl _ _ _ (hasTyA_instLevels hEL hIL hls hlen h)
  | _, _, _, _, .symm Γ x y A h => .symm _ _ _ _ (convA_instLevels hEL hIL hls hlen h)
  | _, _, _, _, .trans Γ x y z A h1 h2 =>
      .trans _ _ (instantiateLevelsA ls y) _ _ (convA_instLevels hEL hIL hls hlen h1)
        (convA_instLevels hEL hIL hls hlen h2)
  | _, _, _, _, .beta Γ A u body arg B hA hbody harg hred => by
      have hred' := hasTyA_instLevels hEL hIL hls hlen hred
      rw [instantiateLevelsA_instantiate0A, instantiateLevelsA_instantiate0A] at hred'
      show ConvA E I n (instCtxA ls Γ)
        (.app (.lam (instantiateLevelsA ls A) (instLevel ls u) (instantiateLevelsA ls body))
          (instantiateLevelsA ls arg))
        (instantiateLevelsA ls (instantiate0A arg body)) (instantiateLevelsA ls (instantiate0A arg B))
      rw [instantiateLevelsA_instantiate0A, instantiateLevelsA_instantiate0A]
      exact .beta _ _ _ _ _ _ (hasTyA_instLevels hEL hIL hls hlen hA)
        (hasTyA_instLevels hEL hIL hls hlen hbody) (hasTyA_instLevels hEL hIL hls hlen harg) hred'
  | _, _, _, _, .zeta Γ A value body B u hA hv hb hred => by
      have hred' := hasTyA_instLevels hEL hIL hls hlen hred
      rw [instantiateLevelsA_instantiate0A, instantiateLevelsA_instantiate0A] at hred'
      show ConvA E I n (instCtxA ls Γ)
        (.letE (instantiateLevelsA ls A) (instantiateLevelsA ls value) (instantiateLevelsA ls body))
        (instantiateLevelsA ls (instantiate0A value body))
        (instantiateLevelsA ls (instantiate0A value B))
      rw [instantiateLevelsA_instantiate0A, instantiateLevelsA_instantiate0A]
      exact .zeta _ _ _ _ _ (instLevel ls u) (hasTyA_instLevels hEL hIL hls hlen hA)
        (hasTyA_instLevels hEL hIL hls hlen hv) (hasTyA_instLevels hEL hIL hls hlen hb) hred'
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      .zetaLocal _ i _ _ (instCtxA_lookupValue hval) (instCtxA_lookupType hty)
        (hasTyA_instLevels hEL hIL hls hlen hv)
  | _, _, _, _, .delta Γ r ms m b hres hbody htr hlen' hwf hb => by
      have hb' := hasTyA_instLevels hEL hIL hls hlen hb
      rw [instLevels_mtype hEL hres hlen' ls, instLevels_mbody hEL hres hbody hlen' ls] at hb'
      show ConvA E I n (instCtxA ls Γ) (.const r (ms.map (instLevel ls)))
        (instantiateLevelsA ls (instantiateLevelsA ms b))
        (instantiateLevelsA ls (instantiateLevelsA ms m.mtypeA))
      rw [instLevels_mtype hEL hres hlen' ls, instLevels_mbody hEL hres hbody hlen' ls]
      exact .delta _ r _ m b hres hbody htr (length_map_arity hlen' _)
        (levelsBounded_inst hls hlen hwf) hb'
  | _, _, _, _, .iota Γ lhs rhs T h hlhs hrhs =>
      .iota _ _ _ _
        ⟨by rw [hIL ls lhs, h.1]; rfl,
         by rw [hStepFnA_instLevels hEL hIL ls Γ lhs (hasTyA_constsArity hlhs), h.2]; rfl⟩
        (hasTyA_instLevels hEL hIL hls hlen hlhs) (hasTyA_instLevels hEL hIL hls hlen hrhs)
  | _, _, _, _, .structIota Γ f a rhs e T hrec hs h hlhs hrhs hcv =>
      .structIota _ (instantiateLevelsA ls f) (instantiateLevelsA ls a) _ (instantiateLevelsA ls e) _
        (by rw [recAtMajorA_instLevels]; exact hrec)
        (by rw [structArmA_instLevels hEL ls f a (hasTyA_constsArity hlhs).1, hs]; rfl)
        (by have h' := hIL ls (.app f a); rw [h] at h'; exact h')
        (hasTyA_instLevels hEL hIL hls hlen hlhs) (hasTyA_instLevels hEL hIL hls hlen hrhs)
        (convA_instLevels hEL hIL hls hlen hcv)
  | _, _, _, _, .lit Γ t T hexp => by
      have h' := hasTyA_instLevels hEL hIL hls hlen hexp
      rw [instantiateLevelsA_natExpandA] at h'
      show ConvA E I n (instCtxA ls Γ) (.lit t) (instantiateLevelsA ls (natExpandA t))
        (instantiateLevelsA ls T)
      rw [instantiateLevelsA_natExpandA]
      exact .lit _ t _ h'
  | _, _, _, _, .app Γ f g x y A B u v h1 h2 hB hrt => by
      have hrt' := hasTyA_instLevels hEL hIL hls hlen hrt
      rw [instantiateLevelsA_instantiate0A] at hrt'
      show ConvA E I n (instCtxA ls Γ) (.app (instantiateLevelsA ls f) (instantiateLevelsA ls x))
        (.app (instantiateLevelsA ls g) (instantiateLevelsA ls y))
        (instantiateLevelsA ls (instantiate0A x B))
      rw [instantiateLevelsA_instantiate0A]
      exact .app _ _ _ _ _ (instantiateLevelsA ls A) _ (instLevel ls u) (instLevel ls v)
        (convA_instLevels hEL hIL hls hlen h1) (convA_instLevels hEL hIL hls hlen h2)
        (hasTyA_instLevels hEL hIL hls hlen hB) hrt'
  | _, _, _, _, .lam Γ A A' b b' B u u' v hu hA hb hrt =>
      .lam _ _ _ _ _ (instantiateLevelsA ls B) (instLevel ls u) (instLevel ls u') (instLevel ls v)
        (eqN_instLevel hu ls) (convA_instLevels hEL hIL hls hlen hA)
        (convA_instLevels hEL hIL hls hlen hb) (hasTyA_instLevels hEL hIL hls hlen hrt)
  | _, _, _, _, .pi Γ A A' B B' u u' v v' hu hv hA hB hrt =>
      .pi _ _ _ _ _ (instLevel ls u) (instLevel ls u') (instLevel ls v) (instLevel ls v')
        (eqN_instLevel hu ls) (eqN_instLevel hv ls) (convA_instLevels hEL hIL hls hlen hA)
        (convA_instLevels hEL hIL hls hlen hB) (hasTyA_instLevels hEL hIL hls hlen hrt)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb hrt => by
      have hrt' := hasTyA_instLevels hEL hIL hls hlen hrt
      rw [instantiateLevelsA_instantiate0A] at hrt'
      show ConvA E I n (instCtxA ls Γ)
        (.letE (instantiateLevelsA ls A) (instantiateLevelsA ls v) (instantiateLevelsA ls b))
        (.letE (instantiateLevelsA ls A') (instantiateLevelsA ls v') (instantiateLevelsA ls b'))
        (instantiateLevelsA ls (instantiate0A v B))
      rw [instantiateLevelsA_instantiate0A]
      exact .letE _ _ _ _ _ _ _ (instantiateLevelsA ls B) (instLevel ls u)
        (convA_instLevels hEL hIL hls hlen hA) (convA_instLevels hEL hIL hls hlen hv)
        (convA_instLevels hEL hIL hls hlen hb) hrt'
  | _, _, _, _, .sorts Γ l₁ l₂ h => .sorts _ (instLevel ls l₁) (instLevel ls l₂) (eqN_instLevel h ls)
  | _, _, _, _, .consts Γ r ms ms' m hres hlen' hwf hwf' h hrt => by
      have hrt' := hasTyA_instLevels hEL hIL hls hlen hrt
      rw [instLevels_mtype hEL hres hlen' ls] at hrt'
      show ConvA E I n (instCtxA ls Γ) (.const r (ms.map (instLevel ls)))
        (.const r (ms'.map (instLevel ls))) (instantiateLevelsA ls (instantiateLevelsA ms m.mtypeA))
      rw [instLevels_mtype hEL hres hlen' ls]
      exact .consts _ r _ _ m hres (length_map_arity hlen' _) (levelsBounded_inst hls hlen hwf)
        (levelsBounded_inst hls hlen hwf') (eqNList_map_instLevel ls ms ms' h) hrt'
  | _, _, _, _, .eta Γ f A B u v h hrt => by
      have hrt' := hasTyA_instLevels hEL hIL hls hlen hrt
      show ConvA E I n (instCtxA ls Γ)
        (.lam (instantiateLevelsA ls A) (instLevel ls u)
          (.app (instantiateLevelsA ls (liftA 0 1 f)) (.bvar 0)))
        (instantiateLevelsA ls f)
        (.pi (instantiateLevelsA ls A) (instLevel ls u) (instantiateLevelsA ls B) (instLevel ls v))
      rw [instantiateLevelsA_liftA]
      refine .eta _ _ _ _ (instLevel ls u) (instLevel ls v) (hasTyA_instLevels hEL hIL hls hlen h) ?_
      have : instantiateLevelsA ls (.lam A u (.app (liftA 0 1 f) (.bvar 0))) =
          .lam (instantiateLevelsA ls A) (instLevel ls u) (.app (liftA 0 1 (instantiateLevelsA ls f)) (.bvar 0)) := by
        simp only [instantiateLevelsA, instantiateLevelsA_liftA]
      rw [← this]
      exact hrt'
  | _, _, _, _, .irr Γ P p q hP hp hq =>
      .irr _ _ _ _ (hasTyA_instLevels hEL hIL hls hlen hP) (hasTyA_instLevels hEL hIL hls hlen hp)
        (hasTyA_instLevels hEL hIL hls hlen hq)
  | _, _, _, _, .tyConv Γ x y A A' l l' u h hAl hlu hA'l hl'u hA =>
      .tyConv _ _ _ (instantiateLevelsA ls A) _ (instLevel ls l) (instLevel ls l') (instLevel ls u)
        (convA_instLevels hEL hIL hls hlen h) (hasTyA_instLevels hEL hIL hls hlen hAl)
        (eqN_instLevel hlu ls) (hasTyA_instLevels hEL hIL hls hlen hA'l) (eqN_instLevel hl'u ls)
        (convA_instLevels hEL hIL hls hlen hA)

/-- `TyConvA` under level instantiation (R-NoDeltaRec-4d-iii): each `.of` node's data
    instantiates pointwise. -/
def tyConvA_instLevels (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) {a n : Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a) :
    {Γ : LCtxA} → {M P : ExprA} → TyConvA E I a Γ M P →
    TyConvA E I n (instCtxA ls Γ) (instantiateLevelsA ls M) (instantiateLevelsA ls P)
  | _, _, _, .refl Γ A => .refl _ _
  | _, _, _, .of Γ A B l l' u hAl hlu hBl hl'u h =>
      .of _ _ _ (instLevel ls l) (instLevel ls l') (instLevel ls u)
        (hasTyA_instLevels hEL hIL hls hlen hAl) (eqN_instLevel hlu ls)
        (hasTyA_instLevels hEL hIL hls hlen hBl) (eqN_instLevel hl'u ls)
        (convA_instLevels hEL hIL hls hlen h)
  | _, _, _, .trans Γ A B C h1 h2 =>
      .trans _ _ (instantiateLevelsA ls B) _ (tyConvA_instLevels hEL hIL hls hlen h1)
        (tyConvA_instLevels hEL hIL hls hlen h2)

end

end Inst

#print axioms instantiateLevelsA_instantiateLevelsA
#print axioms instantiateLevelsA_instantiate0A
#print axioms levelsBounded_map_instLevel
#print axioms eqNList_map_instLevel
#print axioms lookupTypeA_instCtxA
#print axioms hStepFnA_instLevels
#print axioms hasTyA_constsArity
#print axioms hasTyA_instLevels
#print axioms convA_instLevels
#print axioms structArmA_instLevels

end Rcic.Declarative.Ann
