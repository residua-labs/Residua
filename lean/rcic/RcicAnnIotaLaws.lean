import rcic.RcicAnnIota
import rcic.RcicAnnLevels
import rcic.RcicAnnSynMap

/-!
# M2-f (2) — the interface laws of the concrete ι, through one syntax map

`IotaLiftA` / `IotaSubstA` / `IotaLevelsA` for `iotaIfaceA E`, each as a theorem.
One development, not three: a SYNTAX MAP `IotaMapA` is a `φ : ExprA → ExprA` that is
a homomorphism on applications and Π-types, passes through `0`-instantiation with a
companion `φb` under one binder, and acts on constants through a level map `ψ`. The
layers of `iotaFnA` commute with every such map ON SUCCESS (`recSpineA` and
the major's head by `appsSpineA_const`, the group untouched, the reduct by
`applyTelA_some`, and `fieldsTelA_map` / `rhsArgsA_map` through a CHAIN of syntax maps), provided the map fixes the
instantiated member types up to `ψ` (`MemTyA`: closedness for lifting and
substitution, composition for level instantiation). `substA σ` is such a map — that
is `IotaSubstA`. A SHAPE MAP (`IotaShapeMapA`) moreover preserves every constructor,
and then the layers commute as Option EQUALITIES (`recSpineA_shape`,
`applyTelA_shape`, `fieldsTelA_shape`): `liftA c 1` and `instantiateLevelsA ms` are
shape maps — that is `IotaLiftA` and `IotaLevelsA`. ι's right-hand side at a function-recursive field
is a λ-wrapped call that binds a whole telescope, so the laws read the map under each of its binders:
an `IotaMapChainA` (`liftChainA`, `substChainA`, `levelsChainA`) carries the maps at every depth, and
`iotaReductA_some_map` / `iotaReductA_shape` are stated through it (R-NoFunRec-1 step 1 (1c-γ)). Substitution is NOT a shape map
(a variable head becomes anything), which is exactly why `IotaSubstA` is success
preservation (M2-f (1)).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) the three layers commute with a syntax map -/

namespace IotaMapA

/-- the spine under the map. -/
def mapSpine (M : IotaMapA) (s : RecSpineA) : RecSpineA :=
  ⟨s.recRef, s.ls.map M.ψ, s.preMajor.map M.φ, M.φ s.major⟩

variable (M : IotaMapA)

/-! ### (1b) the layers commute on success -/

theorem recSpineA_some_map {e : ExprA} {s : RecSpineA} (h : recSpineA e = some s) :
    recSpineA (M.φ e) = some (M.mapSpine s) := by
  have hsp := recSpineA_some h
  have hhead : (appsSpineA e).1 = .const s.recRef s.ls := by rw [hsp]
  have h' := M.appsSpineA_const e hhead
  rw [hsp] at h'
  simp only [List.map_append, List.map_cons, List.map_nil] at h'
  exact recSpineA_of_spine h'

theorem spineHeadRefA_some_map {e : ExprA} {c : Nat} (h : spineHeadRefA e = some c) :
    spineHeadRefA (M.φ e) = some c := by
  obtain ⟨ls, hc⟩ := spineHeadRefA_some h
  exact spineHeadRefA_of_const (ls := ls.map M.ψ) (by rw [M.appsSpineA_const e hc])

end IotaMapA

namespace IotaShapeMapA

variable (M : IotaShapeMapA)

theorem recSpineA_shape (e : ExprA) :
    recSpineA (M.φ e) = (recSpineA e).map M.toIotaMapA.mapSpine := by
  cases hs : recSpineA e with
  | some s => exact M.toIotaMapA.recSpineA_some_map hs
  | none =>
      rw [Option.map_none']
      unfold recSpineA at hs ⊢
      rw [M.appsSpineA_shape_fst, M.appsSpineA_shape_snd, ← List.map_reverse]
      generalize (appsSpineA e).1 = h0 at hs ⊢
      generalize (appsSpineA e).2.reverse = rev at hs ⊢
      cases h0 <;> cases rev <;>
        simp only [M.bvar, M.sort, M.const, M.app, M.lam, M.pi, M.letE, M.lit, List.map_nil,
          List.map_cons] <;>
        exact Option.noConfusion hs

end IotaShapeMapA

/-! ### (1d) the laws through a chain (R-NoFunRec-1 step 1 (1c-γ)): ι's λ-wrapped call binds a telescope -/

namespace IotaMapChainA

variable (C : IotaMapChainA)

theorem iotaReductA_some_map {E : ResolvedEnvA} (hM : (C.dep 0).MemTyA E) {s : RecSpineA} {g : IotaGroupA}
    {e' : ExprA} (hcm : E.members g.ctorRef = some g.ctorM) (hmc : g.ctorM.mclass = .constructorM)
    (h : iotaReductA s g = some e') :
    iotaReductA ((C.dep 0).mapSpine s) g = some ((C.dep 0).φ e') := by
  unfold iotaReductA at h ⊢
  dsimp only [IotaMapA.mapSpine]
  cases hc : spineHeadRefA s.major with
  | none => rw [hc, Option.none_bind] at h; exact Option.noConfusion h
  | some c =>
      simp only [hc, Option.some_bind] at h
      simp only [(C.dep 0).spineHeadRefA_some_map hc, Option.some_bind]
      obtain ⟨lsC, hcc⟩ := spineHeadRefA_some hc
      have hargs : (appsSpineA ((C.dep 0).φ s.major)).2 = (appsSpineA s.major).2.map (C.dep 0).φ := by
        rw [(C.dep 0).appsSpineA_const s.major hcc]
      rw [hargs]
      simp only [List.length_map]
      split at h
      · rename_i hcond
        rw [if_pos hcond]
        cases hk : ctorShapesA g.familyRef g.nparams (g.ctorM.normA.getD g.ctorM.mtypeA) with
        | none => rw [hk, Option.none_bind] at h; exact Option.noConfusion h
        | some shapes =>
            simp only [hk, Option.some_bind] at h ⊢
            cases hm : s.preMajor[g.nparams + 1 + g.ctorIdx]? with
            | none => rw [hm, Option.none_bind] at h; exact Option.noConfusion h
            | some minor =>
                simp only [hm, Option.some_bind] at h
                simp only [List.getElem?_map, hm, Option.map_some', Option.some_bind]
                cases ha : applyTelA (s.preMajor.take g.nparams)
                    (instantiateLevelsA (s.ls.take g.ctorM.arity) (g.ctorM.normA.getD g.ctorM.mtypeA)) with
                | none => rw [ha, Option.none_bind] at h; exact Option.noConfusion h
                | some ctorAfter =>
                    simp only [ha, Option.some_bind] at h
                    rw [← (hM g.ctorRef g.ctorM s.ls hcm hcond.2.2.2.2).2 hmc,
                      ← List.map_take (C.dep 0).φ s.preMajor g.nparams, (C.dep 0).applyTelA_some _ ha]
                    simp only [Option.some_bind]
                    split at h
                    · rename_i hft
                      injection h with h
                      subst h
                      rw [← List.map_drop, if_pos (C.fieldsTelA_map _ _ _ hft), (C.dep 0).foldAppsA_map]
                      have hr := C.rhsArgsA_map (.const s.recRef s.ls) (fun k => C.const_dep k _ _) s.preMajor g.nparams
                        g.nMinors _ shapes ctorAfter hft
                      rw [(C.dep 0).const] at hr
                      rw [hr]
                    · exact Option.noConfusion h
      · exact Option.noConfusion h

/-- THE SUCCESS LAW of every chain of syntax maps fixing the member types. -/
theorem iotaFnA_some_map {E : ResolvedEnvA} (hM : (C.dep 0).MemTyA E)
    {e e' : ExprA} (h : iotaFnA E e = some e') : iotaFnA E ((C.dep 0).φ e) = some ((C.dep 0).φ e') := by
  obtain ⟨s, c, g, hs, hc, hg, hr⟩ := iotaFnA_some h
  obtain ⟨_, _, h3, hmc, h5, _⟩ := iotaGroupA_some hg
  have hcm : E.members g.ctorRef = some g.ctorM := by
    rw [h5]; exact h3
  rw [iotaFnA_of_layers ((C.dep 0).recSpineA_some_map hs) ((C.dep 0).spineHeadRefA_some_map hc) hg]
  exact C.iotaReductA_some_map hM hcm hmc hr

theorem iotaReductA_shape (hS : C.Shape) {E : ResolvedEnvA} (hM : (C.dep 0).MemTyA E) (s : RecSpineA)
    {g : IotaGroupA} (hcm : E.members g.ctorRef = some g.ctorM) (hmc : g.ctorM.mclass = .constructorM) :
    iotaReductA ((C.dep 0).mapSpine s) g = (iotaReductA s g).map (C.dep 0).φ := by
  have hsref : ∀ e, spineHeadRefA ((C.dep 0).φ e) = spineHeadRefA e := fun e => by
    obtain ⟨S, hS'⟩ := hS 0
    rw [← hS']
    exact S.spineHeadRefA_shape e
  have hsnd : ∀ e, (appsSpineA ((C.dep 0).φ e)).2 = (appsSpineA e).2.map (C.dep 0).φ := fun e => by
    obtain ⟨S, hS'⟩ := hS 0
    rw [← hS']
    exact S.appsSpineA_shape_snd e
  have happ : ∀ (as : List ExprA) (T : ExprA),
      applyTelA (as.map (C.dep 0).φ) ((C.dep 0).φ T) = (applyTelA as T).map (C.dep 0).φ := fun as T => by
    obtain ⟨S, hS'⟩ := hS 0
    rw [← hS']
    exact S.applyTelA_shape as T
  unfold iotaReductA
  dsimp only [IotaMapA.mapSpine]
  rw [hsref, hsnd]
  cases spineHeadRefA s.major with
  | none => rfl
  | some c =>
      simp only [Option.some_bind, List.length_map]
      by_cases hcond : c = g.ctorRef ∧ s.preMajor.length + 1 = piCountA g.recM.mtypeA ∧
          s.ls.length = g.recM.arity ∧
          (appsSpineA s.major).2.length = piCountA (g.ctorM.normA.getD g.ctorM.mtypeA) ∧
          g.ctorM.arity ≤ s.ls.length
      · rw [if_pos hcond, if_pos hcond, ← (hM g.ctorRef g.ctorM s.ls hcm hcond.2.2.2.2).2 hmc,
          ← List.map_take (C.dep 0).φ s.preMajor g.nparams, happ, List.getElem?_map,
          ← List.map_drop]
        cases ctorShapesA g.familyRef g.nparams (g.ctorM.normA.getD g.ctorM.mtypeA) with
        | none => rfl
        | some shapes =>
            simp only [Option.some_bind]
            cases s.preMajor[g.nparams + 1 + g.ctorIdx]? with
            | none => rfl
            | some minor =>
                simp only [Option.map_some', Option.some_bind]
                cases applyTelA (s.preMajor.take g.nparams)
                    (instantiateLevelsA (s.ls.take g.ctorM.arity) (g.ctorM.normA.getD g.ctorM.mtypeA)) with
                | none => rfl
                | some ctorAfter =>
                    simp only [Option.map_some', Option.some_bind]
                    rw [fieldsTelA_shape hS]
                    by_cases hft :
                        fieldsTelA ((appsSpineA s.major).2.drop g.nparams) shapes ctorAfter = true
                    · rw [if_pos hft, if_pos hft, Option.map_some', (C.dep 0).foldAppsA_map]
                      have hr := C.rhsArgsA_map (.const s.recRef s.ls) (fun k => C.const_dep k _ _) s.preMajor
                        g.nparams g.nMinors _ shapes ctorAfter hft
                      rw [(C.dep 0).const] at hr
                      rw [hr]
                    · rw [if_neg hft, if_neg hft]; rfl
      · rw [if_neg hcond, if_neg hcond]; rfl

/-- THE EQUALITY LAW of every shape chain fixing the member types. -/
theorem iotaFnA_shape (hS : C.Shape) {E : ResolvedEnvA} (hM : (C.dep 0).MemTyA E)
    (e : ExprA) : iotaFnA E ((C.dep 0).φ e) = (iotaFnA E e).map (C.dep 0).φ := by
  have hsref : ∀ e, spineHeadRefA ((C.dep 0).φ e) = spineHeadRefA e := fun e => by
    obtain ⟨S, hS'⟩ := hS 0
    rw [← hS']
    exact S.spineHeadRefA_shape e
  have hrs : ∀ e, recSpineA ((C.dep 0).φ e) = (recSpineA e).map (C.dep 0).mapSpine := fun e => by
    obtain ⟨S, hS'⟩ := hS 0
    rw [← hS']
    exact S.recSpineA_shape e
  unfold iotaFnA
  rw [hrs]
  cases recSpineA e with
  | none => rfl
  | some s =>
      simp only [Option.map_some', Option.some_bind]
      dsimp only [IotaMapA.mapSpine]
      rw [hsref]
      cases spineHeadRefA s.major with
      | none => rfl
      | some c =>
          simp only [Option.some_bind]
          cases hg : iotaGroupA E s.recRef c with
          | none => rfl
          | some g =>
              simp only [Option.some_bind]
              obtain ⟨_, _, h3, hmc, h5, _⟩ := iotaGroupA_some hg
              have hcm : E.members g.ctorRef = some g.ctorM := by rw [h5]; exact h3
              exact C.iotaReductA_shape hS hM s hcm hmc

end IotaMapChainA

/-! ## (2) the three maps (`liftMapA` is `RcicAnnSynMap`'s, with the structures) -/

/-- level instantiation `instantiateLevelsA ms` is a shape map. -/
def levelsMapA (ms : List Level) : IotaShapeMapA where
  φ := instantiateLevelsA ms
  φb := instantiateLevelsA ms
  ψ := instLevel ms
  ψv := id
  app := fun _ _ => rfl
  pi := fun _ _ _ _ => rfl
  inst := fun a B => instantiateLevelsA_instantiate0A ms a B
  const := fun _ _ => rfl
  bvar := fun _ => rfl
  sort := fun _ => rfl
  lam := fun _ _ _ => rfl
  letE := fun _ _ _ => rfl
  lit := fun _ => rfl

/-- level instantiation at every depth (it fixes the variables and does not move under binders). -/
def levelsChainA (ms : List Level) : IotaMapChainA where
  dep _ := (levelsMapA ms).toIotaMapA
  coh := fun _ => rfl
  ψc := fun _ => rfl
  lam := fun _ _ _ _ => rfl
  liftk := fun k e => instantiateLevelsA_liftA ms 0 k e
  bound := fun _ _ _ => rfl

theorem levelsChainA_shape (ms : List Level) : (levelsChainA ms).Shape :=
  fun _ => ⟨levelsMapA ms, rfl⟩

section Laws
variable {E : ResolvedEnvA}

theorem liftMapA_memTy (hE : EnvClosedA E) (hN : EnvNormClosedA E) (c : Nat) :
    (liftMapA c).toIotaMapA.MemTyA E :=
  fun r m ls hres _ => ⟨by
      show liftA c 1 (instantiateLevelsA (ls.take m.arity) m.mtypeA) =
        instantiateLevelsA ((ls.map id).take m.arity) m.mtypeA
      rw [List.map_id]
      exact liftA_instantiateLevelsA_closed (hE r m hres).1 _ c,
    fun hmc => by
      cases hT : m.normA with
      | none =>
          show liftA c 1 (instantiateLevelsA (ls.take m.arity) m.mtypeA) =
            instantiateLevelsA ((ls.map id).take m.arity) m.mtypeA
          rw [List.map_id]
          exact liftA_instantiateLevelsA_closed (hE r m hres).1 _ c
      | some T =>
          show liftA c 1 (instantiateLevelsA (ls.take m.arity) T) =
            instantiateLevelsA ((ls.map id).take m.arity) T
          rw [List.map_id]
          exact liftA_instantiateLevelsA_closed (hN r m hres hmc T hT) _ c⟩

theorem substMapA_memTy (hE : EnvClosedA E) (hN : EnvNormClosedA E) (σ : SubstA) :
    (substMapA σ).MemTyA E :=
  fun r m ls hres _ => ⟨by
      show substA σ (instantiateLevelsA (ls.take m.arity) m.mtypeA) =
        instantiateLevelsA ((ls.map id).take m.arity) m.mtypeA
      rw [List.map_id]
      exact substA_mtype hE hres _ σ,
    fun hmc => by
      cases hT : m.normA with
      | none =>
          show substA σ (instantiateLevelsA (ls.take m.arity) m.mtypeA) =
            instantiateLevelsA ((ls.map id).take m.arity) m.mtypeA
          rw [List.map_id]
          exact substA_mtype hE hres _ σ
      | some T =>
          show substA σ (instantiateLevelsA (ls.take m.arity) T) =
            instantiateLevelsA ((ls.map id).take m.arity) T
          rw [List.map_id]
          exact substA_closed (liftA_instantiateLevelsA_closed (hN r m hres hmc T hT) _) σ⟩

theorem levelsMapA_memTy (hEL : EnvLevelsA E) (hNL : EnvNormLevelsA E) (ms : List Level) :
    (levelsMapA ms).toIotaMapA.MemTyA E :=
  fun r m ls hres hle => ⟨by
      show instantiateLevelsA ms (instantiateLevelsA (ls.take m.arity) m.mtypeA) =
        instantiateLevelsA ((ls.map (instLevel ms)).take m.arity) m.mtypeA
      rw [← List.map_take]
      apply instantiateLevelsA_instantiateLevelsA
      rw [List.length_take, Nat.min_eq_left hle]
      exact (hEL r m hres).1,
    fun hmc => by
      cases hT : m.normA with
      | none =>
          show instantiateLevelsA ms (instantiateLevelsA (ls.take m.arity) m.mtypeA) =
            instantiateLevelsA ((ls.map (instLevel ms)).take m.arity) m.mtypeA
          rw [← List.map_take]
          apply instantiateLevelsA_instantiateLevelsA
          rw [List.length_take, Nat.min_eq_left hle]
          exact (hEL r m hres).1
      | some T =>
          show instantiateLevelsA ms (instantiateLevelsA (ls.take m.arity) T) =
            instantiateLevelsA ((ls.map (instLevel ms)).take m.arity) T
          rw [← List.map_take]
          apply instantiateLevelsA_instantiateLevelsA
          rw [List.length_take, Nat.min_eq_left hle]
          exact hNL r m hres hmc T hT⟩

/-! ## (3) THE LAWS -/

/-- ι commutes with weakening (05's ι fires on shapes, which lifting preserves). The member types
    ι reads include the constructor members' `normA` (R-NoDeltaRec-3b): `EnvNormClosedA`. -/
theorem iotaFnA_lift (hE : EnvClosedA E) (hN : EnvNormClosedA E) : IotaLiftA (iotaIfaceA E) :=
  fun c e => (liftChainA c).iotaFnA_shape (liftChainA_shape c) (liftMapA_memTy hE hN c) e

/-- ι steps are preserved by substitution — success preservation (M2-f (1)): the
    recursor spine and the constructor-headed major keep their heads, the member
    types are closed, the `directRec` domains are constant-headed. -/
theorem iotaFnA_subst (hE : EnvClosedA E) (hN : EnvNormClosedA E) : IotaSubstA (iotaIfaceA E) :=
  fun σ _ _ h => (substChainA σ).iotaFnA_some_map (substMapA_memTy hE hN σ) h

/-- ι commutes with level instantiation: the constructor-side universe view
    `ls.take ctorM.arity` composes under `EnvLevelsA`. -/
theorem iotaFnA_levels (hEL : EnvLevelsA E) (hNL : EnvNormLevelsA E) : IotaLevelsA (iotaIfaceA E) :=
  fun ms e => (levelsChainA ms).iotaFnA_shape (levelsChainA_shape ms) (levelsMapA_memTy hEL hNL ms) e

/-- the whole interface, realized. -/
theorem iotaIfaceA_laws (hE : EnvClosedA E) (hN : EnvNormClosedA E) (hEL : EnvLevelsA E)
    (hNL : EnvNormLevelsA E) :
    IotaLiftA (iotaIfaceA E) ∧ IotaSubstA (iotaIfaceA E) ∧ IotaLevelsA (iotaIfaceA E) ∧
      IotaRecHeadA E (iotaIfaceA E) :=
  ⟨iotaFnA_lift hE hN, iotaFnA_subst hE hN, iotaFnA_levels hEL hNL, iotaFnA_recHead E⟩

end Laws

#print axioms IotaMapChainA.iotaFnA_some_map
#print axioms IotaMapChainA.iotaFnA_shape
#print axioms iotaFnA_lift
#print axioms iotaFnA_subst
#print axioms iotaFnA_levels
#print axioms iotaIfaceA_laws

end Rcic.Declarative.Ann
