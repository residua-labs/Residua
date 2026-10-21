import rcic.RcicAnnCtxMorph

/-!
# M2-a (i) — the operations commute with lifting, on the copy

Weakening the relation (M2-a (ii)) and the judgments (M2-s (2)) both reduce to
this: inserting a declaration at `c` and lifting every term at `c` is INVISIBLE
to the head step, to weak-head normalisation and to type synthesis — each
answers, on the lifted term in the extended context, the lift of what it
answered before (on `Option`, so "no step" / "no type" is preserved too). Two
facts about the PARAMETERS carry it, the named hypotheses `RcicAnnDecl`
promised: the environment twin's types and bodies are closed (`EnvClosedA`),
and the ι oracle is equivariant under lifting (`IotaLiftA`). Everything else is
the copy's own structure: `RcicAnnCtxMorph` for the variable arms,
`RcicAnnSubstCalc` for β/ζ.

Then the predicates the relation's clauses read — `RedTo`, `IsPropTy`,
`StuckA` — are stable under one insertion (`RedTo` and `IsPropTy` also
reflect), and along a whole `WkSpecA`. (`SortOfWhnfA` left with M1-d (iv).)
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the two hypotheses on the parameters -/

/-- every member's type and body are closed: lifting at any cutoff is the
    identity on them. -/
def EnvClosedA (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m →
    (∀ k, liftA k 1 m.mtypeA = m.mtypeA) ∧
    (∀ b, m.bodyA = some b → ∀ k, liftA k 1 b = b)

/-- every constructor member's `normA`, when it carries one, is closed (R-NoDeltaRec-3a): the ι
    reader sees `normA`'s shapes where the stored type's are hidden by δ. Only `constructorM`
    members carry one (`ctorMemberA`), so the hypothesis reads at `constructorM`. -/
def EnvNormClosedA (E : ResolvedEnvA) : Prop :=
  ∀ r m, E.members r = some m → m.mclass = .constructorM →
    ∀ T, m.normA = some T → ∀ k, liftA k 1 T = T

/-- `normA.getD`'s closedness member-wise (R-NoDeltaRec-4d-iii): `none` collapses to `mtypeA`
    (`EnvClosedA`), `some` is `EnvNormClosedA` at a `constructorM`. -/
theorem envNormClosedA_getD {E : ResolvedEnvA} (hnorm : EnvNormClosedA E) (hE : EnvClosedA E)
    {c : Nat} {cm : CheckedMemberA} (hm : E.members c = some cm)
    (hk : cm.mclass = .constructorM) :
    ∀ k, liftA k 1 (cm.normA.getD cm.mtypeA) = cm.normA.getD cm.mtypeA := by
  intro k
  cases hna : cm.normA with
  | none => exact (hE c cm hm).1 k
  | some T =>
      show liftA k 1 T = T
      exact hnorm c cm hm hk T hna k





/-- the ι oracle commutes with lifting (05's ι fires on constructor shapes,
    which lifting preserves; discharged with the content, M3). -/
def IotaLiftA (I : IotaIfaceA) : Prop :=
  ∀ c e, I.fn (liftA c 1 e) = (I.fn e).map (liftA c 1)

theorem emptyEnvA_closed : EnvClosedA emptyEnvA := fun _ _ h => Option.noConfusion h
theorem noIotaA_lift : IotaLiftA noIotaA := fun _ _ => rfl

/-! ## (2) closed pieces and shapes -/

theorem liftA_natExpandA (c a : Nat) : (t : Nat) → liftA c a (natExpandA t) = natExpandA t
  | 0 => rfl
  | t + 1 => by
      simp only [natExpandA, litSuccA, liftA, liftA_natExpandA c a t]

theorem liftA_instantiate0A (c : Nat) (r e : ExprA) :
    liftA c 1 (instantiate0A r e) = instantiate0A (liftA c 1 r) (liftA (c + 1) 1 e) :=
  liftA_instantiateA_low 1 c 0 r (Nat.zero_le c) e

theorem liftA_eq_lam {c : Nat} : (f : ExprA) → {A : ExprA} → {u : Level} → {b : ExprA} →
    liftA c 1 f = .lam A u b → ∃ A₀ b₀, f = .lam A₀ u b₀ ∧ A = liftA c 1 A₀ ∧ b = liftA (c + 1) 1 b₀
  | .lam A₀ u₀ b₀, _, _, _, h => by
      simp only [liftA, ExprA.lam.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨A₀, b₀, rfl, rfl, rfl⟩
  | .bvar i, _, _, _, h => by rw [liftA_bvar] at h; cases h
  | .sort _, _, _, _, h => by simp [liftA] at h
  | .const _ _, _, _, _, h => by simp [liftA] at h
  | .app _ _, _, _, _, h => by simp [liftA] at h
  | .pi _ _ _ _, _, _, _, h => by simp [liftA] at h
  | .letE _ _ _, _, _, _, h => by simp [liftA] at h
  | .lit _, _, _, _, h => by simp [liftA] at h

theorem liftA_not_lam {c : Nat} {f : ExprA} (hnl : ∀ A u b, f ≠ .lam A u b) :
    ∀ A u b, liftA c 1 f ≠ .lam A u b := fun _ u _ h =>
  (liftA_eq_lam f h).elim fun A₀ h₀ => h₀.elim fun b₀ hf => hnl A₀ u b₀ hf.1

theorem liftA_eq_sort {c : Nat} : (A : ExprA) → {l : Level} → liftA c 1 A = .sort l → A = .sort l
  | .sort _, _, h => by simp only [liftA] at h; exact h
  | .bvar i, _, h => by rw [liftA_bvar] at h; cases h
  | .lam _ _ _, _, h => by simp [liftA] at h
  | .const _ _, _, h => by simp [liftA] at h
  | .app _ _, _, h => by simp [liftA] at h
  | .pi _ _ _ _, _, h => by simp [liftA] at h
  | .letE _ _ _, _, h => by simp [liftA] at h
  | .lit _, _, h => by simp [liftA] at h

theorem liftA_eq_pi {c : Nat} : (A : ExprA) → {D C : ExprA} → {u v : Level} →
    liftA c 1 A = .pi D u C v →
      ∃ D₀ C₀, A = .pi D₀ u C₀ v ∧ D = liftA c 1 D₀ ∧ C = liftA (c + 1) 1 C₀
  | .pi D₀ u₀ C₀ v₀, _, _, _, _, h => by
      simp only [liftA, ExprA.pi.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨D₀, C₀, rfl, rfl, rfl⟩
  | .bvar i, _, _, _, _, h => by rw [liftA_bvar] at h; cases h
  | .sort _, _, _, _, _, h => by simp [liftA] at h
  | .const _ _, _, _, _, _, h => by simp [liftA] at h
  | .app _ _, _, _, _, _, h => by simp [liftA] at h
  | .lam _ _ _, _, _, _, _, h => by simp [liftA] at h
  | .letE _ _ _, _, _, _, _, h => by simp [liftA] at h
  | .lit _, _, _, _, _, h => by simp [liftA] at h

theorem appsSpineA_liftA (c : Nat) : (e : ExprA) →
    appsSpineA (liftA c 1 e) = (liftA c 1 (appsSpineA e).1, (appsSpineA e).2.map (liftA c 1))
  | .app f x => by
      show appsSpineA (.app (liftA c 1 f) (liftA c 1 x)) = _
      simp only [appsSpineA, appsSpineA_liftA c f, List.map_append, List.map_cons, List.map_nil]
  | .bvar i => by
      show appsSpineA (liftA c 1 (.bvar i)) = (liftA c 1 (.bvar i), [])
      rw [liftA_bvar]
      rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .lam _ _ _ => rfl
  | .pi _ _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- the major arm reads the spine's shape, which one insertion preserves. -/
theorem recAtMajorA_liftA (E : ResolvedEnvA) (c : Nat) (f : ExprA) :
    recAtMajorA E (liftA c 1 f) = recAtMajorA E f := by
  unfold recAtMajorA
  rw [appsSpineA_liftA c f, List.length_map]
  cases (appsSpineA f).1 <;> first | rfl | (rw [liftA_bvar]; rfl)

theorem unitHeadA_liftA (E : ResolvedEnvA) (c : Nat) : (h : ExprA) →
    unitHeadA E (liftA c 1 h) = unitHeadA E h
  | .bvar i => by rw [liftA_bvar]; rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .pi _ _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- the K-unit arm reads the spine's head and its last argument, which one insertion maps. -/
theorem unitMinorA_liftA (E : ResolvedEnvA) (c : Nat) :
    (f : ExprA) → unitMinorA E (liftA c 1 f) = (unitMinorA E f).map (liftA c 1)
  | .app g mn => by
      show (if unitHeadA E (appsSpineA (liftA c 1 g)).1 then some (liftA c 1 mn) else none) =
        (if unitHeadA E (appsSpineA g).1 then some mn else none).map (liftA c 1)
      rw [appsSpineA_liftA c g]
      dsimp only
      rw [unitHeadA_liftA E c]
      cases unitHeadA E (appsSpineA g).1 <;> rfl
  | .bvar i => by rw [liftA_bvar]; rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .lam _ _ _ => rfl
  | .pi _ _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-! W-1 (a): the struct arm commutes with one insertion — it reads the recursor's closed type and the
    spine's arguments, and builds its reduct from them by application, λ and instantiation. -/

theorem applyTelA_liftA (c : Nat) : (xs : List ExprA) → (T : ExprA) →
    applyTelA (xs.map (liftA c 1)) (liftA c 1 T) = (applyTelA xs T).map (liftA c 1)
  | [], _ => rfl
  | x :: xs, .pi D u B v => by
      show applyTelA (xs.map (liftA c 1)) (instantiate0A (liftA c 1 x) (liftA (c + 1) 1 B)) =
        (applyTelA xs (instantiate0A x B)).map (liftA c 1)
      rw [← liftA_instantiate0A]
      exact applyTelA_liftA c xs _
  | _ :: _, .bvar i => by rw [liftA_bvar]; rfl
  | _ :: _, .sort _ => rfl
  | _ :: _, .const _ _ => rfl
  | _ :: _, .app _ _ => rfl
  | _ :: _, .lam _ _ _ => rfl
  | _ :: _, .letE _ _ _ => rfl
  | _ :: _, .lit _ => rfl

theorem piCountA_liftA (c : Nat) : (T : ExprA) → piCountA (liftA c 1 T) = piCountA T
  | .pi _ _ B _ => by
      show piCountA (liftA (c + 1) 1 B) + 1 = piCountA B + 1
      rw [piCountA_liftA (c + 1) B]
  | .bvar i => by rw [liftA_bvar]; rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

theorem piDomListA_liftA (c : Nat) : (T : ExprA) →
    piDomListA (liftA c 1 T) = liftDomsA c 1 (piDomListA T)
  | .pi D u B _ => by
      show (liftA c 1 D, u) :: piDomListA (liftA (c + 1) 1 B) =
        (liftA c 1 D, u) :: liftDomsA (c + 1) 1 (piDomListA B)
      rw [piDomListA_liftA (c + 1) B]
  | .bvar i => by rw [liftA_bvar]; rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

theorem lamTelA_liftA (c : Nat) : (ds : List (ExprA × Level)) → (b : ExprA) →
    liftA c 1 (lamTelA ds b) = lamTelA (liftDomsA c 1 ds) (liftA (c + ds.length) 1 b)
  | [], b => by simp only [lamTelA, liftDomsA, List.length_nil, Nat.add_zero]
  | (D, u) :: ds, b => by
      show ExprA.lam (liftA c 1 D) u (liftA (c + 1) 1 (lamTelA ds b)) =
        ExprA.lam (liftA c 1 D) u (lamTelA (liftDomsA (c + 1) 1 ds) (liftA (c + (ds.length + 1)) 1 b))
      rw [lamTelA_liftA (c + 1) ds b, show c + 1 + ds.length = c + (ds.length + 1) from by omega]

theorem fieldSelA_liftA (c : Nat) (ds : List (ExprA × Level)) (i : Nat) (hi : i < ds.length) :
    fieldSelA (liftDomsA c 1 ds) i = liftA c 1 (fieldSelA ds i) := by
  unfold fieldSelA
  rw [lamTelA_liftA, liftDomsA_length]
  congr 1
  show ExprA.bvar (ds.length - 1 - i) =
    (if c + ds.length ≤ ds.length - 1 - i then .bvar (ds.length - 1 - i + 1) else .bvar (ds.length - 1 - i))
  rw [if_neg (by omega)]

theorem structProjA_liftA (c r : Nat) (ls₀ : List Level) (ps : List ExprA) (S : ExprA) (uS : Level)
    (ds : List (ExprA × Level)) (x : ExprA) (i : Nat) (F : ExprA) (hi : i < ds.length) :
    structProjA r ls₀ (ps.map (liftA c 1)) (liftA c 1 S) uS (liftDomsA c 1 ds) (liftA c 1 x) i
        (liftA c 1 F) =
      liftA c 1 (structProjA r ls₀ ps S uS ds x i F) := by
  have hlam : liftA c 1 (ExprA.lam S uS (liftA 0 1 F)) =
      .lam (liftA c 1 S) uS (liftA 0 1 (liftA c 1 F)) := by
    show ExprA.lam (liftA c 1 S) uS (liftA (c + 1) 1 (liftA 0 1 F)) = _
    rw [liftA_liftA_permute 1 1 c 0 (Nat.zero_le c) F, Nat.add_comm 1 c]
  unfold structProjA
  rw [liftA_foldAppsA, List.map_append, fieldSelA_liftA c ds i hi]
  simp only [List.map_cons, List.map_nil, hlam]
  rfl

theorem structProjsA_liftA (c r : Nat) (ls₀ : List Level) (ps : List ExprA) (S : ExprA) (uS : Level)
    (ds : List (ExprA × Level)) (x : ExprA) :
    (k i : Nat) → (T : ExprA) → i + k ≤ ds.length →
    structProjsA r ls₀ (ps.map (liftA c 1)) (liftA c 1 S) uS (liftDomsA c 1 ds) (liftA c 1 x) k i
        (liftA c 1 T) =
      (structProjsA r ls₀ ps S uS ds x k i T).map (liftA c 1)
  | 0, _, _, _ => rfl
  | k + 1, i, .pi F u B v, hk => by
      show structProjA r ls₀ (ps.map (liftA c 1)) (liftA c 1 S) uS (liftDomsA c 1 ds) (liftA c 1 x) i
            (liftA c 1 F) ::
          structProjsA r ls₀ (ps.map (liftA c 1)) (liftA c 1 S) uS (liftDomsA c 1 ds) (liftA c 1 x) k (i + 1)
            (instantiate0A (structProjA r ls₀ (ps.map (liftA c 1)) (liftA c 1 S) uS (liftDomsA c 1 ds)
              (liftA c 1 x) i (liftA c 1 F)) (liftA (c + 1) 1 B)) = _
      rw [structProjA_liftA c r ls₀ ps S uS ds x i F (by omega), ← liftA_instantiate0A,
        structProjsA_liftA c r ls₀ ps S uS ds x k (i + 1) _ (by omega)]
      rfl
  | _ + 1, _, .bvar j, _ => by rw [liftA_bvar]; rfl
  | _ + 1, _, .sort _, _ => rfl
  | _ + 1, _, .const _ _, _ => rfl
  | _ + 1, _, .app _ _, _ => rfl
  | _ + 1, _, .lam _ _ _, _ => rfl
  | _ + 1, _, .letE _ _ _, _ => rfl
  | _ + 1, _, .lit _, _ => rfl

theorem liftDomsA_take (c a : Nat) : (k : Nat) → (ds : List (ExprA × Level)) →
    (liftDomsA c a ds).take k = liftDomsA c a (ds.take k)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, (D, u) :: ds => by
      show (liftA c a D, u) :: (liftDomsA (c + 1) a ds).take k =
        (liftA c a D, u) :: liftDomsA (c + 1) a (ds.take k)
      rw [liftDomsA_take (c + 1) a k ds]

/-- one insertion on what the struct arm reads. -/
def StructSpineA.liftS (c : Nat) (d : StructSpineA) : StructSpineA :=
  ⟨d.r, d.ls₀, d.ps.map (liftA c 1), liftA c 1 d.S, d.uS, liftA c 1 d.Dm, liftA c 1 d.mn, d.nf⟩

theorem StructSpineA.reduct_liftA (c : Nat) (d : StructSpineA) (x : ExprA) (hn : d.nf ≤ piCountA d.Dm) :
    (d.liftS c).reduct (liftA c 1 x) = liftA c 1 (d.reduct x) := by
  unfold StructSpineA.reduct StructSpineA.liftS
  dsimp only
  rw [liftA_foldAppsA, piDomListA_liftA, liftDomsA_take,
    structProjsA_liftA c d.r d.ls₀ d.ps d.S d.uS ((piDomListA d.Dm).take d.nf) x d.nf 0 d.Dm
      (by rw [List.length_take, piDomListA_length]; omega)]

theorem structSpineA_liftA {E : ResolvedEnvA} (hE : EnvClosedA E) (c : Nat) :
    (f : ExprA) → structSpineA E (liftA c 1 f) = (structSpineA E f).map (StructSpineA.liftS c)
  | .app g mn => by
      show structSpineA E (.app (liftA c 1 g) (liftA c 1 mn)) = (structSpineA E (.app g mn)).map _
      dsimp only [structSpineA]
      rw [appsSpineA_liftA c g]
      dsimp only
      cases hh : (appsSpineA g).1 with
      | const r ls =>
          show (match E.members r with
            | some m =>
                if structGroupA r m = true then
                  match applyTelA ((appsSpineA g).2.map (liftA c 1)) (instantiateLevelsA ls m.mtypeA) with
                  | some (.pi Dm _ B _) =>
                      match instantiate0A (liftA c 1 mn) B with
                      | .pi S uS _ _ => some ⟨r, motZeroLevelsA ls, ((appsSpineA g).2.map (liftA c 1)).dropLast,
                          S, uS, Dm, liftA c 1 mn, structFieldCountA m⟩
                      | _ => none
                  | _ => none
                else none
            | none => none) = Option.map (StructSpineA.liftS c) (match E.members r with
            | some m =>
                if structGroupA r m = true then
                  match applyTelA (appsSpineA g).2 (instantiateLevelsA ls m.mtypeA) with
                  | some (.pi Dm _ B _) =>
                      match instantiate0A mn B with
                      | .pi S uS _ _ => some ⟨r, motZeroLevelsA ls, (appsSpineA g).2.dropLast, S, uS, Dm, mn,
                          structFieldCountA m⟩
                      | _ => none
                  | _ => none
                else none
            | none => none)
          cases hm : E.members r with
          | none => rfl
          | some m =>
              dsimp only
              cases hs : structGroupA r m with
              | false => rfl
              | true =>
                  simp only [if_true]
                  have hT : liftA c 1 (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA ls m.mtypeA := by
                    rw [← instantiateLevelsA_liftA, (hE r m hm).1 c]
                  have hA := applyTelA_liftA c (appsSpineA g).2 (instantiateLevelsA ls m.mtypeA)
                  rw [hT] at hA
                  rw [hA]
                  cases ha : applyTelA (appsSpineA g).2 (instantiateLevelsA ls m.mtypeA) with
                  | none => rfl
                  | some T =>
                      simp only [Option.map_some']
                      cases T with
                      | pi Dm u B v =>
                          show (match instantiate0A (liftA c 1 mn) (liftA (c + 1) 1 B) with
                            | .pi S uS _ _ => some (⟨r, motZeroLevelsA ls,
                                ((appsSpineA g).2.map (liftA c 1)).dropLast, S, uS, liftA c 1 Dm, liftA c 1 mn,
                                structFieldCountA m⟩ :
                                  StructSpineA)
                            | _ => none) = Option.map (StructSpineA.liftS c) (match instantiate0A mn B with
                            | .pi S uS _ _ => some ⟨r, motZeroLevelsA ls, (appsSpineA g).2.dropLast, S, uS, Dm, mn,
                                structFieldCountA m⟩
                            | _ => none)
                          rw [← liftA_instantiate0A]
                          cases hB : instantiate0A mn B with
                          | pi S uS C w =>
                              show some _ = some _
                              simp only [StructSpineA.liftS, List.map_dropLast]
                          | bvar j => rw [liftA_bvar]; rfl
                          | sort _ => rfl
                          | const _ _ => rfl
                          | app _ _ => rfl
                          | lam _ _ _ => rfl
                          | letE _ _ _ => rfl
                          | lit _ => rfl
                      | bvar j => rw [liftA_bvar]; rfl
                      | sort _ => rfl
                      | const _ _ => rfl
                      | app _ _ => rfl
                      | lam _ _ _ => rfl
                      | letE _ _ _ => rfl
                      | lit _ => rfl
      | bvar i => rw [liftA_bvar]; rfl
      | sort _ => rfl
      | app _ _ => rfl
      | lam _ _ _ => rfl
      | pi _ _ _ _ => rfl
      | letE _ _ _ => rfl
      | lit _ => rfl
  | .bvar i => by rw [liftA_bvar]; rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .lam _ _ _ => rfl
  | .pi _ _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- THE STRUCT ARM COMMUTES WITH ONE INSERTION. -/
theorem structArmA_liftA {E : ResolvedEnvA} (hE : EnvClosedA E) (c : Nat) (f x : ExprA) :
    structArmA E (liftA c 1 f) (liftA c 1 x) = (structArmA E f x).map (liftA c 1) := by
  unfold structArmA
  rw [structSpineA_liftA hE c f]
  cases structSpineA E f with
  | none => rfl
  | some d =>
      show (if d.nf ≤ piCountA (liftA c 1 d.Dm) then some ((d.liftS c).reduct (liftA c 1 x)) else none) =
        Option.map (liftA c 1) (if d.nf ≤ piCountA d.Dm then some (d.reduct x) else none)
      rw [piCountA_liftA]
      by_cases hn : d.nf ≤ piCountA d.Dm
      · rw [if_pos hn, if_pos hn, StructSpineA.reduct_liftA c d x hn]; rfl
      · rw [if_neg hn, if_neg hn]; rfl

/-- W-1 (e): the struct head reads the spine's head, which one insertion keeps. -/
theorem structHeadA_liftA (E : ResolvedEnvA) (c : Nat) (f : ExprA) :
    structHeadA E (liftA c 1 f) = structHeadA E f := by
  unfold structHeadA
  rw [appsSpineA_liftA c f]
  cases (appsSpineA f).1 <;> first | rfl | (rw [liftA_bvar]; done) | (rw [liftA_bvar]; rfl)

theorem structPosA_liftA (E : ResolvedEnvA) (c : Nat) (f : ExprA) :
    structPosA E (liftA c 1 f) = structPosA E f := by
  unfold structPosA; rw [recAtMajorA_liftA, structHeadA_liftA]

theorem isShapeHeadA_liftA (E : ResolvedEnvA) (c : Nat) : (h : ExprA) →
    (isShapeHeadA E (liftA c 1 h) ↔ isShapeHeadA E h)
  | .bvar i => by rw [liftA_bvar]; exact Iff.rfl
  | .sort _ => Iff.rfl
  | .pi _ _ _ _ => Iff.rfl
  | .const _ _ => Iff.rfl
  | .app _ _ => Iff.rfl
  | .lam _ _ _ => Iff.rfl
  | .letE _ _ _ => Iff.rfl
  | .lit _ => Iff.rfl

/-! ## (3) the head step, whnf and synthesis commute with one insertion -/

theorem hStepFnA_liftA {E : ResolvedEnvA} {I : IotaIfaceA} (hE : EnvClosedA E) (hI : IotaLiftA I)
    (d : LocalDeclA) : (c : Nat) → (Γ : LCtxA) → c ≤ Γ.length → (e : ExprA) →
    hStepFnA E I.fn (insertAtA d c Γ) (liftA c 1 e) = (hStepFnA E I.fn Γ e).map (liftA c 1)
  | c, Γ, hc, .app f x => by
      rcases lamA_or_not f with ⟨A, u, b, rfl⟩ | hnl
      · show hStepFnA E I.fn (insertAtA d c Γ)
            (.app (.lam (liftA c 1 A) u (liftA (c + 1) 1 b)) (liftA c 1 x)) = _
        rw [hStepFnA_app_lam, hStepFnA_app_lam, Option.map_some', liftA_instantiate0A]
      · have hnl' := liftA_not_lam (c := c) hnl
        show hStepFnA E I.fn (insertAtA d c Γ) (.app (liftA c 1 f) (liftA c 1 x)) = _
        rw [hStepFnA_app_nonlam E I.fn _ _ hnl', hStepFnA_app_nonlam E I.fn Γ x hnl,
          hStepFnA_liftA hE hI d c Γ hc f]
        cases hStepFnA E I.fn Γ f with
        | some f' => rfl
        | none =>
            dsimp only
            rw [structPosA_liftA E c f]
            cases structPosA E f with
            | true => exact structArmA_liftA hE c f x
            | false =>
                have hfn : I.fn (.app (liftA c 1 f) (liftA c 1 x)) =
                    (I.fn (.app f x)).map (liftA c 1) := hI c (.app f x)
                rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hfn]
                cases I.fn (.app f x) with
                | some e' => rfl
                | none =>
                    rw [recAtMajorA_liftA E c f, unitMinorA_liftA E c f,
                      hStepFnA_liftA hE hI d c Γ hc x]
                    cases recAtMajorA E f <;> cases unitMinorA E f <;>
                      cases hStepFnA E I.fn Γ x <;> rfl
  | c, Γ, _, .letE A v b => by
      show hStepFnA E I.fn (insertAtA d c Γ)
          (.letE (liftA c 1 A) (liftA c 1 v) (liftA (c + 1) 1 b)) = _
      simp only [hStepFnA, Option.map_some', liftA_instantiate0A]
  | c, Γ, hc, .bvar i => by
      rw [liftA_bvar]
      show lookupValueA (insertAtA d c Γ) (shiftIdx c i) = (lookupValueA Γ i).map (liftA c 1)
      exact lookupValueA_insertAtA d c Γ hc i
  | c, Γ, _, .const r ls => by
      show hStepFnA E I.fn (insertAtA d c Γ) (.const r ls) =
        (hStepFnA E I.fn Γ (.const r ls)).map (liftA c 1)
      simp only [hStepFnA]
      cases hm : E.members r with
      | none => rfl
      | some m =>
          dsimp only
          by_cases ht : transparent m.mclass = true
          · rw [if_pos ht]
            cases hb : m.bodyA with
            | none => rfl
            | some b =>
                simp only [Option.map_some']
                rw [← instantiateLevelsA_liftA, (hE r m hm).2 b hb c]
          · rw [if_neg ht]; rfl
  | c, Γ, _, .lit t => by
      show hStepFnA E I.fn (insertAtA d c Γ) (.lit t) = _
      simp only [hStepFnA, Option.map_some', liftA_natExpandA]
  | _, _, _, .sort _ => rfl
  | _, _, _, .lam _ _ _ => rfl
  | _, _, _, .pi _ _ _ _ => rfl

theorem whnfA_liftA {E : ResolvedEnvA} {I : IotaIfaceA} (hE : EnvClosedA E) (hI : IotaLiftA I)
    (d : LocalDeclA) (c : Nat) (Γ : LCtxA) (hc : c ≤ Γ.length) :
    (fuel : Nat) → (e : ExprA) →
    whnfA E I.fn (insertAtA d c Γ) fuel (liftA c 1 e) = (whnfA E I.fn Γ fuel e).map (liftA c 1)
  | 0, e => by
      simp only [whnfA]
      rw [hStepFnA_liftA hE hI d c Γ hc e]
      cases hStepFnA E I.fn Γ e <;> rfl
  | fuel + 1, e => by
      simp only [whnfA]
      rw [hStepFnA_liftA hE hI d c Γ hc e]
      cases hStepFnA E I.fn Γ e with
      | none => rfl
      | some e' => exact whnfA_liftA hE hI d c Γ hc fuel e'

theorem inferA_liftA {E : ResolvedEnvA} {I : IotaIfaceA} (hE : EnvClosedA E) (hI : IotaLiftA I)
    (d : LocalDeclA) : (fuel : Nat) → (c : Nat) → (Γ : LCtxA) → c ≤ Γ.length → (e : ExprA) →
    inferA E I.fn fuel (insertAtA d c Γ) (liftA c 1 e) = (inferA E I.fn fuel Γ e).map (liftA c 1)
  | 0, _, _, _, _ => rfl
  | fuel + 1, c, Γ, hc, e => by
      cases e with
      | bvar i =>
          rw [liftA_bvar, inferA_succ_bvar, inferA_succ_bvar]
          exact lookupTypeA_insertAtA d c Γ hc i
      | sort l => rfl
      | pi A u B v => rfl
      | const r ls =>
          show inferA E I.fn (fuel + 1) (insertAtA d c Γ) (.const r ls) = _
          rw [inferA_succ_const, inferA_succ_const]
          cases hm : E.members r with
          | none => rfl
          | some m =>
              dsimp only
              by_cases hl : ls.length = m.arity
              · rw [if_pos hl]
                simp only [Option.map_some']
                rw [← instantiateLevelsA_liftA, (hE r m hm).1 c]
              · rw [if_neg hl]; rfl
      | lit t =>
          show inferA E I.fn (fuel + 1) (insertAtA d c Γ) (.lit t) = _
          rw [inferA_succ_lit, inferA_succ_lit]
          have h := inferA_liftA hE hI d fuel c Γ hc (natExpandA t)
          rw [liftA_natExpandA] at h
          exact h
      | lam A u body =>
          show inferA E I.fn (fuel + 1) (insertAtA d c Γ)
            (.lam (liftA c 1 A) u (liftA (c + 1) 1 body)) = _
          rw [inferA_succ_lam, inferA_succ_lam]
          have hc' : c + 1 ≤ (LocalDeclA.assumption A :: Γ).length := Nat.succ_le_succ hc
          have e1 : insertAtA d (c + 1) (.assumption A :: Γ) =
              .assumption (liftA c 1 A) :: insertAtA d c Γ := rfl
          have h1 := inferA_liftA hE hI d fuel (c + 1) _ hc' body
          rw [e1] at h1
          rw [h1]
          cases inferA E I.fn fuel (.assumption A :: Γ) body with
          | none => rfl
          | some B =>
              dsimp only [Option.map]
              have h2 := inferA_liftA hE hI d fuel (c + 1) _ hc' B
              rw [e1] at h2
              rw [h2]
              cases inferA E I.fn fuel (.assumption A :: Γ) B with
              | none => rfl
              | some TB =>
                  dsimp only [Option.map]
                  have h3 := whnfA_liftA hE hI d (c + 1) _ hc' fuel TB
                  rw [e1] at h3
                  rw [h3]
                  cases whnfA E I.fn (.assumption A :: Γ) fuel TB with
                  | none => rfl
                  | some w =>
                      dsimp only [Option.map]
                      cases w with
                      | bvar i => rw [liftA_bvar]
                      | _ => rfl
      | app f a =>
          show inferA E I.fn (fuel + 1) (insertAtA d c Γ) (.app (liftA c 1 f) (liftA c 1 a)) = _
          rw [inferA_succ_app, inferA_succ_app, inferA_liftA hE hI d fuel c Γ hc f]
          cases inferA E I.fn fuel Γ f with
          | none => rfl
          | some Tf =>
              dsimp only [Option.map]
              rw [whnfA_liftA hE hI d c Γ hc fuel Tf]
              cases whnfA E I.fn Γ fuel Tf with
              | none => rfl
              | some w =>
                  dsimp only [Option.map]
                  cases w with
                  | bvar i => rw [liftA_bvar]
                  | pi D u B v =>
                      show some (instantiate0A (liftA c 1 a) (liftA (c + 1) 1 B)) =
                        some (liftA c 1 (instantiate0A a B))
                      rw [liftA_instantiate0A]
                  | _ => rfl
      | letE A v body =>
          show inferA E I.fn (fuel + 1) (insertAtA d c Γ)
            (.letE (liftA c 1 A) (liftA c 1 v) (liftA (c + 1) 1 body)) = _
          rw [inferA_succ_letE, inferA_succ_letE]
          have hc' : c + 1 ≤ (LocalDeclA.letBinding A v :: Γ).length := Nat.succ_le_succ hc
          have e1 : insertAtA d (c + 1) (.letBinding A v :: Γ) =
              .letBinding (liftA c 1 A) (liftA c 1 v) :: insertAtA d c Γ := rfl
          have h1 := inferA_liftA hE hI d fuel (c + 1) _ hc' body
          rw [e1] at h1
          rw [h1]
          cases inferA E I.fn fuel (.letBinding A v :: Γ) body with
          | none => rfl
          | some B =>
              show some (instantiate0A (liftA c 1 v) (liftA (c + 1) 1 B)) =
                some (liftA c 1 (instantiate0A v B))
              rw [liftA_instantiate0A]

theorem inferSortA_liftA {E : ResolvedEnvA} {I : IotaIfaceA} (hE : EnvClosedA E) (hI : IotaLiftA I)
    (d : LocalDeclA) (fuel c : Nat) (Γ : LCtxA) (hc : c ≤ Γ.length) (T : ExprA) :
    inferSortA E I.fn fuel (insertAtA d c Γ) (liftA c 1 T) = inferSortA E I.fn fuel Γ T := by
  unfold inferSortA
  rw [inferA_liftA hE hI d fuel c Γ hc T]
  cases inferA E I.fn fuel Γ T with
  | none => rfl
  | some TT =>
      dsimp only [Option.map]
      rw [whnfA_liftA hE hI d c Γ hc fuel TT]
      cases whnfA E I.fn Γ fuel TT with
      | none => rfl
      | some w =>
          dsimp only [Option.map]
          cases w with
          | bvar i => rw [liftA_bvar]
          | _ => rfl

/-! ## (4) the four predicates under one insertion -/

section OneInsertion
variable {E : ResolvedEnvA} {I : IotaIfaceA} {c : Nat} {Γ : LCtxA}

theorem redTo_liftA (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) (hc : c ≤ Γ.length)
    {t t' : ExprA} (h : RedTo E I Γ t t') :
    RedTo E I (insertAtA d c Γ) (liftA c 1 t) (liftA c 1 t') :=
  h.elim fun fuel hf => ⟨fuel, by rw [whnfA_liftA hE hI d c Γ hc fuel t, hf]; rfl⟩

/-- reflection: a normal form of the lifted term is the lift of a normal form. -/
theorem redTo_liftA_rev (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) (hc : c ≤ Γ.length)
    {t w : ExprA} (h : RedTo E I (insertAtA d c Γ) (liftA c 1 t) w) :
    ∃ t', w = liftA c 1 t' ∧ RedTo E I Γ t t' := by
  obtain ⟨fuel, hf⟩ := h
  rw [whnfA_liftA hE hI d c Γ hc fuel t] at hf
  cases h' : whnfA E I.fn Γ fuel t with
  | none => rw [h'] at hf; exact Option.noConfusion hf
  | some t' => rw [h'] at hf; exact ⟨t', (Option.some.inj hf).symm, fuel, h'⟩

theorem isPropTy_liftA_iff (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA)
    (hc : c ≤ Γ.length) (A : ExprA) :
    IsPropTy E I (insertAtA d c Γ) (liftA c 1 A) ↔ IsPropTy E I Γ A := by
  unfold IsPropTy
  constructor
  · intro ⟨fuel, l, h, hz⟩
    rw [inferSortA_liftA hE hI d fuel c Γ hc A] at h
    exact ⟨fuel, l, h, hz⟩
  · intro ⟨fuel, l, h, hz⟩
    exact ⟨fuel, l, by rw [inferSortA_liftA hE hI d fuel c Γ hc A]; exact h, hz⟩

theorem stuckA_liftA (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) (hc : c ≤ Γ.length)
    {N : ExprA} (h : StuckA E I Γ N) : StuckA E I (insertAtA d c Γ) (liftA c 1 N) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [hStepFnA_liftA hE hI d c Γ hc N, h1]; rfl, ?_⟩
  rw [appsSpineA_liftA]
  exact fun hs => h2 ((isShapeHeadA_liftA E c _).1 hs)

theorem tripleLikeA_liftA (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA) (hc : c ≤ Γ.length)
    {N : ExprA} (h : TripleLikeA E I Γ N) : TripleLikeA E I (insertAtA d c Γ) (liftA c 1 N) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [hStepFnA_liftA hE hI d c Γ hc N, h1]; rfl, ?_⟩
  rcases h2 with hP | hs
  · exact Or.inl ((isPropTy_liftA_iff hE hI d hc N).2 hP)
  · right
    rw [appsSpineA_liftA]
    exact fun h' => hs ((isShapeHeadA_liftA E c _).1 h')

end OneInsertion

/-! ## (5) along a weakening spec -/

theorem wkExprA_sort : (ρ : WkSpecA) → (l : Level) → wkExprA ρ (.sort l) = .sort l
  | [], _ => rfl
  | (_, _) :: ρ, l => wkExprA_sort ρ l

theorem wkExprA_const : (ρ : WkSpecA) → (r : Nat) → (ls : List Level) →
    wkExprA ρ (.const r ls) = .const r ls
  | [], _, _ => rfl
  | (_, _) :: ρ, r, ls => wkExprA_const ρ r ls

theorem wkExprA_app : (ρ : WkSpecA) → (f x : ExprA) →
    wkExprA ρ (.app f x) = .app (wkExprA ρ f) (wkExprA ρ x)
  | [], _, _ => rfl
  | (_, c) :: ρ, f, x => wkExprA_app ρ (liftA c 1 f) (liftA c 1 x)

theorem wkExprA_pi_ub : (ρ : WkSpecA) → (D : ExprA) → (u : Level) → (C : ExprA) → (v : Level) →
    wkExprA ρ (.pi D u C v) = .pi (wkExprA ρ D) u (wkExprA (WkSpecA.ub ρ) C) v
  | [], _, _, _, _ => rfl
  | (_, c) :: ρ, D, u, C, v => wkExprA_pi_ub ρ (liftA c 1 D) u (liftA (c + 1) 1 C) v

theorem wkExprA_lam_ub : (ρ : WkSpecA) → (A : ExprA) → (u : Level) → (b : ExprA) →
    wkExprA ρ (.lam A u b) = .lam (wkExprA ρ A) u (wkExprA (WkSpecA.ub ρ) b)
  | [], _, _, _ => rfl
  | (_, c) :: ρ, A, u, b => wkExprA_lam_ub ρ (liftA c 1 A) u (liftA (c + 1) 1 b)

theorem wkExprA_instantiate0A : (ρ : WkSpecA) → (a C : ExprA) →
    wkExprA ρ (instantiate0A a C) = instantiate0A (wkExprA ρ a) (wkExprA (WkSpecA.ub ρ) C)
  | [], _, _ => rfl
  | (_, c) :: ρ, a, C => by
      show wkExprA ρ (liftA c 1 (instantiate0A a C)) = _
      rw [liftA_instantiate0A]
      exact wkExprA_instantiate0A ρ (liftA c 1 a) (liftA (c + 1) 1 C)

theorem WkSpecA.comp_nil : (ρ : WkSpecA) → WkSpecA.comp ρ [] = ρ
  | [] => rfl
  | (d, c) :: ρ => congrArg (fun τ => (d, c) :: τ) (WkSpecA.comp_nil ρ)

theorem wkExprA_comp : (σ ρ : WkSpecA) → (e : ExprA) →
    wkExprA (WkSpecA.comp σ ρ) e = wkExprA ρ (wkExprA σ e)
  | [], _, _ => rfl
  | (_, c) :: σ, ρ, e => wkExprA_comp σ ρ (liftA c 1 e)

theorem wkCtxA_comp : (σ ρ : WkSpecA) → (Γ : LCtxA) →
    wkCtxA (WkSpecA.comp σ ρ) Γ = wkCtxA ρ (wkCtxA σ Γ)
  | [], _, _ => rfl
  | (d, c) :: σ, ρ, Γ => wkCtxA_comp σ ρ (insertAtA d c Γ)

theorem WkSpecA.ub_comp : (σ ρ : WkSpecA) →
    WkSpecA.ub (WkSpecA.comp σ ρ) = WkSpecA.comp (WkSpecA.ub σ) (WkSpecA.ub ρ)
  | [], _ => rfl
  | (d, c) :: σ, ρ => congrArg (fun τ => (d, c + 1) :: τ) (WkSpecA.ub_comp σ ρ)

theorem WkSpecA.ok_comp : (σ ρ : WkSpecA) → (Γ : LCtxA) → WkSpecA.ok σ Γ →
    WkSpecA.ok ρ (wkCtxA σ Γ) → WkSpecA.ok (WkSpecA.comp σ ρ) Γ
  | [], _, _, _, hρ => hρ
  | (d, c) :: σ, ρ, Γ, ⟨hc, hσ⟩, hρ => ⟨hc, WkSpecA.ok_comp σ ρ (insertAtA d c Γ) hσ hρ⟩

theorem wkOkA_comp {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} {σ ρ : WkSpecA}
    (hσ : WkOkA E I n σ Γ) (hρ : WkOkA E I n ρ (wkCtxA σ Γ)) : WkOkA E I n (WkSpecA.comp σ ρ) Γ :=
  ⟨WkSpecA.ok_comp σ ρ Γ hσ.1 hρ.1, by rw [wkCtxA_comp]; exact hρ.2⟩

theorem redTo_wk {E : ResolvedEnvA} {I : IotaIfaceA} (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {t t' : ExprA} →
    RedTo E I Γ t t' → RedTo E I (wkCtxA ρ Γ) (wkExprA ρ t) (wkExprA ρ t')
  | _, [], _, _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, _, _, h =>
      redTo_wk hE hI (insertAtA d c Γ) ρ hρ (redTo_liftA hE hI d hc h)

theorem redTo_wk_rev {E : ResolvedEnvA} {I : IotaIfaceA} (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {t w : ExprA} →
    RedTo E I (wkCtxA ρ Γ) (wkExprA ρ t) w → ∃ t', w = wkExprA ρ t' ∧ RedTo E I Γ t t'
  | _, [], _, _, _, h => ⟨_, rfl, h⟩
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, t, w, h => by
      obtain ⟨t₁, rfl, h₁⟩ :=
        redTo_wk_rev hE hI (insertAtA d c Γ) ρ hρ (t := liftA c 1 t) h
      obtain ⟨t', rfl, h'⟩ := redTo_liftA_rev hE hI d hc h₁
      exact ⟨t', rfl, h'⟩

theorem isPropTy_wk_iff {E : ResolvedEnvA} {I : IotaIfaceA} (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → (A : ExprA) →
    (IsPropTy E I (wkCtxA ρ Γ) (wkExprA ρ A) ↔ IsPropTy E I Γ A)
  | _, [], _, _ => Iff.rfl
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, A =>
      (isPropTy_wk_iff hE hI (insertAtA d c Γ) ρ hρ (liftA c 1 A)).trans
        (isPropTy_liftA_iff hE hI d hc A)

theorem stuckA_wk {E : ResolvedEnvA} {I : IotaIfaceA} (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {N : ExprA} →
    StuckA E I Γ N → StuckA E I (wkCtxA ρ Γ) (wkExprA ρ N)
  | _, [], _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, _, h =>
      stuckA_wk hE hI (insertAtA d c Γ) ρ hρ (stuckA_liftA hE hI d hc h)

theorem tripleLikeA_wk {E : ResolvedEnvA} {I : IotaIfaceA} (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Γ : LCtxA) → (ρ : WkSpecA) → WkSpecA.ok ρ Γ → {N : ExprA} →
    TripleLikeA E I Γ N → TripleLikeA E I (wkCtxA ρ Γ) (wkExprA ρ N)
  | _, [], _, _, h => h
  | Γ, (d, c) :: ρ, ⟨hc, hρ⟩, _, h =>
      tripleLikeA_wk hE hI (insertAtA d c Γ) ρ hρ (tripleLikeA_liftA hE hI d hc h)

#print axioms hStepFnA_liftA
#print axioms whnfA_liftA
#print axioms inferA_liftA
#print axioms inferSortA_liftA
#print axioms redTo_liftA
#print axioms redTo_liftA_rev
#print axioms isPropTy_liftA_iff
#print axioms stuckA_liftA
#print axioms redTo_wk
#print axioms redTo_wk_rev
#print axioms isPropTy_wk_iff
#print axioms stuckA_wk
#print axioms wkOkA_comp
#print axioms wkExprA_instantiate0A
#print axioms structArmA_liftA

end Rcic.Declarative.Ann
