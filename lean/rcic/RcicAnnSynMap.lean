import rcic.RcicAnnTel
import rcic.RcicAnnWkOps
import rcic.RcicAnnSubst

/-!
# Syntax maps on the copy (M2-f (2), split out for M2-f (3))

A SYNTAX MAP `IotaMapA` is a `φ : ExprA → ExprA` that is a homomorphism on
applications and Π-types, passes through `0`-instantiation with a companion `φb`
under one binder, and acts on constants through a level map `ψ`; a SHAPE MAP
`IotaShapeMapA` moreover preserves every constructor. The telescope algebra of
`RcicAnnTel` commutes with every syntax map on success and with every shape map as
`Option` equalities — proved ONCE here and instantiated: `liftMapA c` (`liftA c 1`)
and `wkMapA σ` (`wkExprA σ`, a whole weakening spec) below; `substMapA σ` and
`levelsMapA ms` in `RcicAnnIotaLaws`. `RcicAnnFamWk` reads `wkMapA` for the `fam`
clause's weakening; `RcicAnnIotaLaws` reads all four for the concrete ι's laws.

A CHAIN `IotaMapChainA` (R-NoFunRec-1 step 1 (1c-γ)) carries the syntax map at every depth: ι's
λ-wrapped call at a function-recursive field binds a whole telescope (`recCallFunA`), so its laws
(`recCallFunA_map`, `recCallsA_map`, `fieldsTelA_map`, `rhsArgsA_map`, and for a chain of shape maps
`piCountA_shape`, `piBodyA_shape`, `shapeGuardA_shape`, `fieldsTelA_shape`) read the map under each of
its binders. Instances: `liftChainA`, `substChainA` here, `levelsChainA` in `RcicAnnIotaLaws`;
`wkMapA` needs none.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) syntax maps -/

/-- a syntax map: homomorphism on `app` and `pi`, through `instantiate0A` with the
    companion `φb` under one binder, constants through the level map `ψ`. -/
structure IotaMapA where
  φ : ExprA → ExprA
  φb : ExprA → ExprA
  ψ : Level → Level
  app : ∀ f x, φ (.app f x) = .app (φ f) (φ x)
  pi : ∀ A u B v, φ (.pi A u B v) = .pi (φ A) (ψ u) (φb B) (ψ v)
  inst : ∀ a B, φ (instantiate0A a B) = instantiate0A (φ a) (φb B)
  const : ∀ r ls, φ (.const r ls) = .const r (ls.map ψ)

/-- a shape map: a syntax map preserving every constructor. -/
structure IotaShapeMapA extends IotaMapA where
  ψv : Nat → Nat
  bvar : ∀ i, φ (.bvar i) = .bvar (ψv i)
  sort : ∀ l, φ (.sort l) = .sort (ψ l)
  lam : ∀ A u b, φ (.lam A u b) = .lam (φ A) (ψ u) (φb b)
  letE : ∀ A w b, φ (.letE A w b) = .letE (φ A) (φ w) (φb b)
  lit : ∀ t, φ (.lit t) = .lit t

/-- a syntax map at every depth (R-NoFunRec-1 step 1 (1c-γ)): `dep k` is the map under `k` binders. ι's
    λ-wrapped call binds a whole telescope, so its laws read the map under each of its binders. -/
structure IotaMapChainA where
  dep : Nat → IotaMapA
  coh : ∀ k, (dep k).φb = (dep (k + 1)).φ
  ψc : ∀ k, (dep k).ψ = (dep 0).ψ
  lam : ∀ k A u b, (dep k).φ (.lam A u b) = .lam ((dep k).φ A) ((dep k).ψ u) ((dep (k + 1)).φ b)
  liftk : ∀ k e, (dep k).φ (liftA 0 k e) = liftA 0 k ((dep 0).φ e)
  bound : ∀ k i, i < k → (dep k).φ (.bvar i) = .bvar i

namespace IotaMapChainA
/-- every depth is a shape map. -/
def Shape (C : IotaMapChainA) : Prop := ∀ k, ∃ S : IotaShapeMapA, S.toIotaMapA = C.dep k
/-- a telescope's domains under the chain, the `j`-th at depth `k + j`. -/
def doms (C : IotaMapChainA) : Nat → List (ExprA × Level) → List (ExprA × Level)
  | _, [] => []
  | k, (D, u) :: ds => ((C.dep k).φ D, (C.dep k).ψ u) :: C.doms (k + 1) ds
end IotaMapChainA

namespace IotaMapA

/-- the map fixes instantiated member types up to the level map: closedness for
    `liftA` / `substA` (`EnvClosedA`), composition for level instantiation
    (`EnvLevelsA`); at the constructor-side view `ls.take m.arity`. The second
    conjunct is the same fact at a constructor member's `normA` (`EnvNormClosedA`
    / `EnvNormLevelsA`), which is the type ι actually reads (R-NoDeltaRec-3b);
    only `constructorM` members carry `normA`, so it is gated there. -/
def MemTyA (M : IotaMapA) (E : ResolvedEnvA) : Prop :=
  ∀ (r : Nat) (m : CheckedMemberA) (ls : List Level), E.members r = some m → m.arity ≤ ls.length →
    M.φ (instantiateLevelsA (ls.take m.arity) m.mtypeA) =
      instantiateLevelsA ((ls.map M.ψ).take m.arity) m.mtypeA ∧
    (m.mclass = .constructorM →
      M.φ (instantiateLevelsA (ls.take m.arity) (m.normA.getD m.mtypeA)) =
        instantiateLevelsA ((ls.map M.ψ).take m.arity) (m.normA.getD m.mtypeA))

variable (M : IotaMapA)

/-! ### (1a) the telescope algebra commutes on success -/

theorem appsSpineA_const : (e : ExprA) → {r : Nat} → {ls : List Level} →
    (appsSpineA e).1 = .const r ls →
    appsSpineA (M.φ e) = (.const r (ls.map M.ψ), (appsSpineA e).2.map M.φ)
  | .const r' ls', _, _, h => by
      have h' : ExprA.const r' ls' = .const _ _ := h
      injection h' with h1 h2
      subst h1; subst h2
      show appsSpineA (M.φ (.const r' ls')) = (.const r' (ls'.map M.ψ), [])
      rw [M.const] <;> rfl
  | .app f x, r, ls, h => by
      have hf : (appsSpineA f).1 = .const r ls := h
      rw [M.app]
      simp only [appsSpineA, appsSpineA_const f hf, List.map_append, List.map_cons, List.map_nil]
  | .bvar _, _, _, h => by simp [appsSpineA] at h
  | .sort _, _, _, h => by simp [appsSpineA] at h
  | .lam _ _ _, _, _, h => by simp [appsSpineA] at h
  | .pi _ _ _ _, _, _, h => by simp [appsSpineA] at h
  | .letE _ _ _, _, _, h => by simp [appsSpineA] at h
  | .lit _, _, _, h => by simp [appsSpineA] at h

theorem foldAppsA_map (f : ExprA) : (xs : List ExprA) →
    M.φ (foldAppsA f xs) = foldAppsA (M.φ f) (xs.map M.φ)
  | [] => rfl
  | x :: xs => by
      show M.φ (foldAppsA (.app f x) xs) = foldAppsA (.app (M.φ f) (M.φ x)) (xs.map M.φ)
      rw [foldAppsA_map (.app f x) xs, M.app]

theorem applyTelA_some : (as : List ExprA) → {T R : ExprA} → applyTelA as T = some R →
    applyTelA (as.map M.φ) (M.φ T) = some (M.φ R)
  | [], T, R, h => by
      have h' : T = R := Option.some.inj h
      subst h'; rfl
  | a :: as, .pi A u B v, R, h => by
      have h' : applyTelA as (instantiate0A a B) = some R := h
      rw [List.map_cons, M.pi]
      show applyTelA (as.map M.φ) (instantiate0A (M.φ a) (M.φb B)) = some (M.φ R)
      rw [← M.inst]
      exact applyTelA_some as h'
  | _ :: _, .bvar _, _, h => Option.noConfusion h
  | _ :: _, .sort _, _, h => Option.noConfusion h
  | _ :: _, .const _ _, _, h => Option.noConfusion h
  | _ :: _, .app _ _, _, h => Option.noConfusion h
  | _ :: _, .lam _ _ _, _, h => Option.noConfusion h
  | _ :: _, .letE _ _ _, _, h => Option.noConfusion h
  | _ :: _, .lit _, _, h => Option.noConfusion h

theorem familyIdxA_const (n : Nat) {A : ExprA} {r : Nat} {ls : List Level}
    (h : (appsSpineA A).1 = .const r ls) :
    familyIdxA n (M.φ A) = (familyIdxA n A).map M.φ := by
  unfold familyIdxA
  rw [M.appsSpineA_const A h]
  exact (List.map_drop M.φ (appsSpineA A).2 n).symm

theorem recPrefixA_map (pre : List ExprA) (n m : Nat) :
    recPrefixA (pre.map M.φ) n m = (recPrefixA pre n m).map M.φ := by
  unfold recPrefixA
  exact (List.map_take M.φ pre (n + 1 + m)).symm

theorem recCallFieldA_const (rec : ExprA) (pre : List ExprA) (n m : Nat) (f : ExprA) {A : ExprA}
    {r : Nat} {ls : List Level} (h : (appsSpineA A).1 = .const r ls) :
    M.φ (recCallFieldA rec pre n m f A) =
      recCallFieldA (M.φ rec) (pre.map M.φ) n m (M.φ f) (M.φ A) := by
  unfold recCallFieldA
  rw [M.foldAppsA_map, List.map_append, List.map_append, M.recPrefixA_map, M.familyIdxA_const n h]
  rfl

theorem spineHeadConstA_map {A : ExprA} (h : spineHeadConstA A = true) :
    spineHeadConstA (M.φ A) = true := by
  obtain ⟨r, ls, hr⟩ := spineHeadConstA_true h
  exact spineHeadConstA_of_const (r := r) (ls := ls.map M.ψ) (by rw [M.appsSpineA_const A hr])

end IotaMapA

namespace IotaShapeMapA

variable (M : IotaShapeMapA)

/-! ### (1c) a shape map commutes with the layers as equalities -/

theorem appsSpineA_shape : (e : ExprA) →
    appsSpineA (M.φ e) = (M.φ (appsSpineA e).1, (appsSpineA e).2.map M.φ)
  | .app f x => by
      rw [M.app]
      simp only [appsSpineA, appsSpineA_shape f, List.map_append, List.map_cons, List.map_nil]
  | .bvar i => by
      show appsSpineA (M.φ (.bvar i)) = (M.φ (.bvar i), [])
      rw [M.bvar] <;> rfl
  | .sort l => by
      show appsSpineA (M.φ (.sort l)) = (M.φ (.sort l), [])
      rw [M.sort] <;> rfl
  | .const r ls => by
      show appsSpineA (M.φ (.const r ls)) = (M.φ (.const r ls), [])
      rw [M.const] <;> rfl
  | .lam A u b => by
      show appsSpineA (M.φ (.lam A u b)) = (M.φ (.lam A u b), [])
      rw [M.lam] <;> rfl
  | .pi A u B v => by
      show appsSpineA (M.φ (.pi A u B v)) = (M.φ (.pi A u B v), [])
      rw [M.pi] <;> rfl
  | .letE A w b => by
      show appsSpineA (M.φ (.letE A w b)) = (M.φ (.letE A w b), [])
      rw [M.letE] <;> rfl
  | .lit t => by
      show appsSpineA (M.φ (.lit t)) = (M.φ (.lit t), [])
      rw [M.lit] <;> rfl

theorem appsSpineA_shape_fst (e : ExprA) : (appsSpineA (M.φ e)).1 = M.φ (appsSpineA e).1 := by
  rw [M.appsSpineA_shape e]

theorem appsSpineA_shape_snd (e : ExprA) : (appsSpineA (M.φ e)).2 = (appsSpineA e).2.map M.φ := by
  rw [M.appsSpineA_shape e]

theorem spineHeadRefA_shape (e : ExprA) : spineHeadRefA (M.φ e) = spineHeadRefA e := by
  unfold spineHeadRefA
  rw [M.appsSpineA_shape_fst]
  generalize (appsSpineA e).1 = h0
  cases h0 <;> simp only [M.bvar, M.sort, M.const, M.app, M.lam, M.pi, M.letE, M.lit]

theorem spineHeadConstA_shape (e : ExprA) : spineHeadConstA (M.φ e) = spineHeadConstA e := by
  unfold spineHeadConstA
  rw [M.appsSpineA_shape_fst]
  generalize (appsSpineA e).1 = h0
  cases h0 <;> simp only [M.bvar, M.sort, M.const, M.app, M.lam, M.pi, M.letE, M.lit]

theorem applyTelA_shape : (as : List ExprA) → (T : ExprA) →
    applyTelA (as.map M.φ) (M.φ T) = (applyTelA as T).map M.φ
  | [], _ => rfl
  | a :: as, .pi A u B v => by
      rw [List.map_cons, M.pi]
      show applyTelA (as.map M.φ) (instantiate0A (M.φ a) (M.φb B)) =
        (applyTelA as (instantiate0A a B)).map M.φ
      rw [← M.inst]
      exact applyTelA_shape as _
  | _ :: _, .bvar i => by rw [List.map_cons, M.bvar] <;> rfl
  | _ :: _, .sort l => by rw [List.map_cons, M.sort] <;> rfl
  | _ :: _, .const r ls => by rw [List.map_cons, M.const] <;> rfl
  | _ :: _, .app f x => by rw [List.map_cons, M.app] <;> rfl
  | _ :: _, .lam A u b => by rw [List.map_cons, M.lam] <;> rfl
  | _ :: _, .letE A w b => by rw [List.map_cons, M.letE] <;> rfl
  | _ :: _, .lit t => by rw [List.map_cons, M.lit] <;> rfl

end IotaShapeMapA

/-! ### (1d) a chain of syntax maps: the λ-wrapped call (R-NoFunRec-1 step 1 (1c-γ)) -/

namespace IotaMapChainA

variable (C : IotaMapChainA)

theorem const_dep (k r : Nat) (ls : List Level) :
    (C.dep k).φ (.const r ls) = (C.dep 0).φ (.const r ls) := by
  rw [(C.dep k).const, (C.dep 0).const, C.ψc k]

theorem doms_length : (k : Nat) → (ds : List (ExprA × Level)) → (C.doms k ds).length = ds.length
  | _, [] => rfl
  | k, _ :: ds => by simp only [doms, List.length_cons, doms_length (k + 1) ds]

theorem lamTelA_map : (ds : List (ExprA × Level)) → (k : Nat) → (b : ExprA) →
    (C.dep k).φ (lamTelA ds b) = lamTelA (C.doms k ds) ((C.dep (k + ds.length)).φ b)
  | [], _, _ => rfl
  | (D, u) :: ds, k, b => by
      show (C.dep k).φ (.lam D u (lamTelA ds b)) = .lam ((C.dep k).φ D) ((C.dep k).ψ u)
        (lamTelA (C.doms (k + 1) ds) ((C.dep (k + (ds.length + 1))).φ b))
      rw [C.lam, lamTelA_map ds (k + 1) b, show k + 1 + ds.length = k + (ds.length + 1) by omega]

theorem piDomListA_map : (A : ExprA) → (k : Nat) → spineHeadConstA (piBodyA A) = true →
    piDomListA ((C.dep k).φ A) = C.doms k (piDomListA A)
  | .pi D u B v, k, h => by
      show piDomListA ((C.dep k).φ (.pi D u B v)) = ((C.dep k).φ D, (C.dep k).ψ u) :: C.doms (k + 1) (piDomListA B)
      rw [(C.dep k).pi, C.coh k]
      show ((C.dep k).φ D, (C.dep k).ψ u) :: piDomListA ((C.dep (k + 1)).φ B) = _
      rw [piDomListA_map B (k + 1) h]
  | .bvar _, _, h => by simp [piBodyA, spineHeadConstA, appsSpineA] at h
  | .sort _, _, h => by simp [piBodyA, spineHeadConstA, appsSpineA] at h
  | .lam _ _ _, _, h => by simp [piBodyA, spineHeadConstA, appsSpineA] at h
  | .letE _ _ _, _, h => by simp [piBodyA, spineHeadConstA, appsSpineA] at h
  | .lit _, _, h => by simp [piBodyA, spineHeadConstA, appsSpineA] at h
  | .const r ls, k, _ => by
      have hc : (appsSpineA ((C.dep k).φ (.const r ls))).1 = .const r (ls.map (C.dep k).ψ) := by
        rw [(C.dep k).appsSpineA_const (.const r ls) (r := r) (ls := ls) rfl]
      exact (piBodyA_of_const hc).2
  | .app f x, k, h => by
      obtain ⟨r, ls, hr⟩ := spineHeadConstA_true h
      have hc := (C.dep k).appsSpineA_const (.app f x) hr
      exact (piBodyA_of_const (e := (C.dep k).φ (.app f x)) (by rw [hc])).2

theorem piBodyA_map : (A : ExprA) → (k : Nat) → spineHeadConstA (piBodyA A) = true →
    piBodyA ((C.dep k).φ A) = (C.dep (k + piCountA A)).φ (piBodyA A)
  | .pi D u B v, k, h => by
      show piBodyA ((C.dep k).φ (.pi D u B v)) = (C.dep (k + (piCountA B + 1))).φ (piBodyA B)
      rw [(C.dep k).pi, C.coh k]
      show piBodyA ((C.dep (k + 1)).φ B) = _
      rw [piBodyA_map B (k + 1) h, show k + 1 + piCountA B = k + (piCountA B + 1) by omega]
  | .bvar _, _, h => by simp [piBodyA, spineHeadConstA, appsSpineA] at h
  | .sort _, _, h => by simp [piBodyA, spineHeadConstA, appsSpineA] at h
  | .lam _ _ _, _, h => by simp [piBodyA, spineHeadConstA, appsSpineA] at h
  | .letE _ _ _, _, h => by simp [piBodyA, spineHeadConstA, appsSpineA] at h
  | .lit _, _, h => by simp [piBodyA, spineHeadConstA, appsSpineA] at h
  | .const r ls, k, _ => by
      have hc : (appsSpineA ((C.dep k).φ (.const r ls))).1 = .const r (ls.map (C.dep k).ψ) := by
        rw [(C.dep k).appsSpineA_const (.const r ls) (r := r) (ls := ls) rfl]
      exact (piBodyA_of_const hc).1
  | .app f x, k, h => by
      obtain ⟨r, ls, hr⟩ := spineHeadConstA_true h
      have hc := (C.dep k).appsSpineA_const (.app f x) hr
      exact (piBodyA_of_const (e := (C.dep k).φ (.app f x)) (by rw [hc])).1

theorem recCallFunA_map (rec : ExprA) (hrec : ∀ k, (C.dep k).φ rec = (C.dep 0).φ rec)
    (pre : List ExprA) (n m : Nat) (f A : ExprA) (hA : spineHeadConstA (piBodyA A) = true) :
    (C.dep 0).φ (recCallFunA rec pre n m f A) =
      recCallFunA ((C.dep 0).φ rec) (pre.map (C.dep 0).φ) n m ((C.dep 0).φ f) ((C.dep 0).φ A) := by
  have hL : (piDomListA A).length = piCountA A := piDomListA_length A
  have hdl : piDomListA ((C.dep 0).φ A) = C.doms 0 (piDomListA A) := C.piDomListA_map A 0 hA
  have hbody : piBodyA ((C.dep 0).φ A) = (C.dep (piCountA A)).φ (piBodyA A) := by
    rw [C.piBodyA_map A 0 hA, Nat.zero_add]
  obtain ⟨r, ls, hr⟩ := spineHeadConstA_true hA
  have hr' : (appsSpineA (piBodyA A)).1 = .const r ls := hr
  unfold recCallFunA
  rw [C.lamTelA_map, hdl, hbody, C.doms_length, hL, Nat.zero_add]
  have hrange : ((List.range (piCountA A)).reverse.map ExprA.bvar).map (C.dep (piCountA A)).φ =
      (List.range (piCountA A)).reverse.map ExprA.bvar := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    have : i < piCountA A := by simpa using hi
    exact C.bound _ i this
  rw [(C.dep (piCountA A)).recCallFieldA_const _ _ n m _ hr', (C.dep (piCountA A)).foldAppsA_map,
    hrange, C.liftk, hrec, List.map_map]
  have hpre : pre.map ((C.dep (piCountA A)).φ ∘ liftA 0 (piCountA A)) =
      (pre.map (C.dep 0).φ).map (liftA 0 (piCountA A)) := by
    rw [List.map_map]
    exact List.map_congr_left (fun x _ => C.liftk _ x)
  rw [hpre]

theorem shapeGuardA_map {A : ExprA} : (s : FieldShape) → shapeGuardA A s = true →
    shapeGuardA ((C.dep 0).φ A) s = true
  | .nonrecursive, _ => rfl
  | .recursive 0, h => (C.dep 0).spineHeadConstA_map h
  | .recursive (k + 1), h => by
      have hb := boolAnd_right h
      have h1 := boolAnd_left h
      have hdl : piDomListA ((C.dep 0).φ A) = C.doms 0 (piDomListA A) := C.piDomListA_map A 0 hb
      show ((piDomListA ((C.dep 0).φ A)).length == k + 1 && spineHeadConstA (piBodyA ((C.dep 0).φ A))) = true
      rw [hdl, C.doms_length, h1, C.piBodyA_map A 0 hb]
      exact (C.dep _).spineHeadConstA_map hb

theorem recCallsA_map (rec : ExprA) (hrec : ∀ k, (C.dep k).φ rec = (C.dep 0).φ rec)
    (pre : List ExprA) (n m : Nat) (f A : ExprA) :
    (s : FieldShape) → shapeGuardA A s = true →
    (recCallsA rec pre n m f A s).map (C.dep 0).φ =
      recCallsA ((C.dep 0).φ rec) (pre.map (C.dep 0).φ) n m ((C.dep 0).φ f) ((C.dep 0).φ A) s
  | .nonrecursive, _ => rfl
  | .recursive 0, h => by
      obtain ⟨r, ls, hr⟩ := spineHeadConstA_true h
      show [(C.dep 0).φ (recCallFieldA rec pre n m f A)] =
        [recCallFieldA ((C.dep 0).φ rec) (pre.map (C.dep 0).φ) n m ((C.dep 0).φ f) ((C.dep 0).φ A)]
      rw [(C.dep 0).recCallFieldA_const rec pre n m f hr]
  | .recursive (k + 1), h => by
      show [(C.dep 0).φ (recCallFunA rec pre n m f A)] =
        [recCallFunA ((C.dep 0).φ rec) (pre.map (C.dep 0).φ) n m ((C.dep 0).φ f) ((C.dep 0).φ A)]
      rw [C.recCallFunA_map rec hrec pre n m f A (boolAnd_right h)]

theorem fieldsTelA_map (fs : List ExprA) : (ss : List FieldShape) → (T : ExprA) →
    fieldsTelA fs ss T = true → fieldsTelA (fs.map (C.dep 0).φ) ss ((C.dep 0).φ T) = true := by
  induction fs with
  | nil =>
      intro ss T h
      cases ss with
      | nil => rfl
      | cons s ss => exact Bool.noConfusion h
  | cons f fs ih =>
      intro ss T h
      cases ss with
      | nil => exact Bool.noConfusion h
      | cons s ss =>
          obtain ⟨A, u, B, v, rfl, hk, ht⟩ := fieldsTelA_cons h
          rw [List.map_cons, (C.dep 0).pi]
          show (shapeGuardA ((C.dep 0).φ A) s &&
            fieldsTelA (fs.map (C.dep 0).φ) ss (instantiate0A ((C.dep 0).φ f) ((C.dep 0).φb B))) = true
          rw [← (C.dep 0).inst, C.shapeGuardA_map s hk, ih ss _ ht]
          rfl

theorem rhsArgsA_map (rec : ExprA) (hrec : ∀ k, (C.dep k).φ rec = (C.dep 0).φ rec)
    (pre : List ExprA) (n m : Nat) (fs : List ExprA) :
    (ss : List FieldShape) → (T : ExprA) → fieldsTelA fs ss T = true →
    rhsArgsA ((C.dep 0).φ rec) (pre.map (C.dep 0).φ) n m (fs.map (C.dep 0).φ) ss ((C.dep 0).φ T) =
      (rhsArgsA rec pre n m fs ss T).map (C.dep 0).φ := by
  induction fs with
  | nil => intro ss T _; rfl
  | cons f fs ih =>
      intro ss T h
      cases ss with
      | nil => exact Bool.noConfusion h
      | cons s ss =>
          obtain ⟨A, u, B, v, rfl, hk, ht⟩ := fieldsTelA_cons h
          rw [List.map_cons, (C.dep 0).pi]
          show (_ :: (recCallsA ((C.dep 0).φ rec) (pre.map (C.dep 0).φ) n m ((C.dep 0).φ f) ((C.dep 0).φ A) s ++
              rhsArgsA ((C.dep 0).φ rec) (pre.map (C.dep 0).φ) n m (fs.map (C.dep 0).φ) ss
                (instantiate0A ((C.dep 0).φ f) ((C.dep 0).φb B)))) =
            (f :: (recCallsA rec pre n m f A s ++
              rhsArgsA rec pre n m fs ss (instantiate0A f B))).map (C.dep 0).φ
          rw [← (C.dep 0).inst, ih ss _ ht, List.map_cons, List.map_append,
            C.recCallsA_map rec hrec pre n m f A s hk]

/-! #### shape chains -/

/-- at a shape chain every depth is a shape map. -/
theorem dep_eq {C : IotaMapChainA} (hS : C.Shape) (k : Nat) :
    ∃ S : IotaShapeMapA, (C.dep k).φ = S.φ := by
  obtain ⟨S, hS'⟩ := hS k
  exact ⟨S, by rw [← hS']⟩

theorem piCountBodyA_shape {C : IotaMapChainA} (hS : C.Shape) : (A : ExprA) → (k : Nat) →
    piCountA ((C.dep k).φ A) = piCountA A ∧ piBodyA ((C.dep k).φ A) = (C.dep (k + piCountA A)).φ (piBodyA A)
  | .pi D u B v, k => by
      show piCountA ((C.dep k).φ (.pi D u B v)) = piCountA B + 1 ∧
        piBodyA ((C.dep k).φ (.pi D u B v)) = (C.dep (k + (piCountA B + 1))).φ (piBodyA B)
      rw [(C.dep k).pi, C.coh k]
      obtain ⟨h1, h2⟩ := piCountBodyA_shape hS B (k + 1)
      refine ⟨?_, ?_⟩
      · show piCountA ((C.dep (k + 1)).φ B) + 1 = _
        rw [h1]
      · show piBodyA ((C.dep (k + 1)).φ B) = _
        rw [h2, show k + 1 + piCountA B = k + (piCountA B + 1) by omega]
  | .bvar i, k => by
      obtain ⟨S, he⟩ := dep_eq hS k
      show piCountA ((C.dep k).φ (.bvar i)) = 0 ∧ piBodyA ((C.dep k).φ (.bvar i)) = (C.dep (k + 0)).φ (.bvar i)
      rw [he, S.bvar]; exact ⟨rfl, by rw [Nat.add_zero, he, S.bvar]; rfl⟩
  | .sort l, k => by
      obtain ⟨S, he⟩ := dep_eq hS k
      show piCountA ((C.dep k).φ (.sort l)) = 0 ∧ piBodyA ((C.dep k).φ (.sort l)) = (C.dep (k + 0)).φ (.sort l)
      rw [he, S.sort]; exact ⟨rfl, by rw [Nat.add_zero, he, S.sort]; rfl⟩
  | .const r ls, k => by
      obtain ⟨S, he⟩ := dep_eq hS k
      show piCountA ((C.dep k).φ (.const r ls)) = 0 ∧ piBodyA ((C.dep k).φ (.const r ls)) = (C.dep (k + 0)).φ (.const r ls)
      rw [he, S.const]; exact ⟨rfl, by rw [Nat.add_zero, he, S.const]; rfl⟩
  | .app g x, k => by
      obtain ⟨S, he⟩ := dep_eq hS k
      show piCountA ((C.dep k).φ (.app g x)) = 0 ∧ piBodyA ((C.dep k).φ (.app g x)) = (C.dep (k + 0)).φ (.app g x)
      rw [he, S.app]; exact ⟨rfl, by rw [Nat.add_zero, he, S.app]; rfl⟩
  | .lam a u b, k => by
      obtain ⟨S, he⟩ := dep_eq hS k
      show piCountA ((C.dep k).φ (.lam a u b)) = 0 ∧ piBodyA ((C.dep k).φ (.lam a u b)) = (C.dep (k + 0)).φ (.lam a u b)
      rw [he, S.lam]; exact ⟨rfl, by rw [Nat.add_zero, he, S.lam]; rfl⟩
  | .letE a w b, k => by
      obtain ⟨S, he⟩ := dep_eq hS k
      show piCountA ((C.dep k).φ (.letE a w b)) = 0 ∧ piBodyA ((C.dep k).φ (.letE a w b)) = (C.dep (k + 0)).φ (.letE a w b)
      rw [he, S.letE]; exact ⟨rfl, by rw [Nat.add_zero, he, S.letE]; rfl⟩
  | .lit t, k => by
      obtain ⟨S, he⟩ := dep_eq hS k
      show piCountA ((C.dep k).φ (.lit t)) = 0 ∧ piBodyA ((C.dep k).φ (.lit t)) = (C.dep (k + 0)).φ (.lit t)
      rw [he, S.lit]; exact ⟨rfl, by rw [Nat.add_zero, he, S.lit]; rfl⟩

theorem piCountA_shape {C : IotaMapChainA} (hS : C.Shape) (A : ExprA) (k : Nat) :
    piCountA ((C.dep k).φ A) = piCountA A :=
  (piCountBodyA_shape hS A k).1

theorem piBodyA_shape {C : IotaMapChainA} (hS : C.Shape) (A : ExprA) (k : Nat) :
    piBodyA ((C.dep k).φ A) = (C.dep (k + piCountA A)).φ (piBodyA A) :=
  (piCountBodyA_shape hS A k).2

theorem spineHeadConstA_dep {C : IotaMapChainA} (hS : C.Shape) (k : Nat) (e : ExprA) :
    spineHeadConstA ((C.dep k).φ e) = spineHeadConstA e := by
  obtain ⟨S, hS'⟩ := hS k
  rw [← hS']
  exact S.spineHeadConstA_shape e

theorem shapeGuardA_shape {C : IotaMapChainA} (hS : C.Shape) (A : ExprA) :
    (s : FieldShape) → shapeGuardA ((C.dep 0).φ A) s = shapeGuardA A s
  | .nonrecursive => rfl
  | .recursive 0 => spineHeadConstA_dep hS 0 A
  | .recursive (k + 1) => by
      obtain ⟨h1, h2⟩ := piCountBodyA_shape hS A 0
      show ((piDomListA ((C.dep 0).φ A)).length == k + 1 && spineHeadConstA (piBodyA ((C.dep 0).φ A))) =
        ((piDomListA A).length == k + 1 && spineHeadConstA (piBodyA A))
      rw [piDomListA_length, piDomListA_length, h1, h2, spineHeadConstA_dep hS]

theorem fieldsTelA_shape {C : IotaMapChainA} (hS : C.Shape) (fs : List ExprA) :
    (ss : List FieldShape) → (T : ExprA) →
    fieldsTelA (fs.map (C.dep 0).φ) ss ((C.dep 0).φ T) = fieldsTelA fs ss T := by
  obtain ⟨S, he⟩ := dep_eq hS 0
  induction fs with
  | nil => intro ss T; cases ss <;> rfl
  | cons f fs ih =>
      intro ss T
      cases ss with
      | nil => rfl
      | cons s ss =>
          cases T with
          | pi A u B v =>
              rw [List.map_cons, (C.dep 0).pi]
              show (shapeGuardA ((C.dep 0).φ A) s &&
                  fieldsTelA (fs.map (C.dep 0).φ) ss (instantiate0A ((C.dep 0).φ f) ((C.dep 0).φb B))) =
                (shapeGuardA A s && fieldsTelA fs ss (instantiate0A f B))
              rw [← (C.dep 0).inst, ih, shapeGuardA_shape hS]
          | bvar i => rw [List.map_cons, he, S.bvar] <;> rfl
          | sort l => rw [List.map_cons, he, S.sort] <;> rfl
          | const r ls => rw [List.map_cons, he, S.const] <;> rfl
          | app g x => rw [List.map_cons, he, S.app] <;> rfl
          | lam A u b => rw [List.map_cons, he, S.lam] <;> rfl
          | letE A w b => rw [List.map_cons, he, S.letE] <;> rfl
          | lit t => rw [List.map_cons, he, S.lit] <;> rfl

end IotaMapChainA

/-! ## (2) weakening maps -/

/-- weakening `liftA c 1` is a shape map. -/
def liftMapA (c : Nat) : IotaShapeMapA where
  φ := liftA c 1
  φb := liftA (c + 1) 1
  ψ := id
  ψv := shiftIdx c
  app := fun _ _ => rfl
  pi := fun _ _ _ _ => rfl
  inst := fun a B => liftA_instantiate0A c a B
  const := fun r ls => by rw [List.map_id] <;> rfl
  bvar := fun i => liftA_bvar c i
  sort := fun _ => rfl
  lam := fun _ _ _ => rfl
  letE := fun _ _ _ => rfl
  lit := fun _ => rfl

/-- the weakening maps `liftA (c + k) 1` at every depth. -/
def liftChainA (c : Nat) : IotaMapChainA where
  dep k := (liftMapA (c + k)).toIotaMapA
  coh := fun _ => rfl
  ψc := fun _ => rfl
  lam := fun _ _ _ _ => rfl
  liftk := fun k e => by
    show liftA (c + k) 1 (liftA 0 k e) = liftA 0 k (liftA c 1 e)
    rw [liftA_liftA_permute k 1 c 0 (Nat.zero_le _) e, Nat.add_comm k c]
  bound := fun k i hi => by
    show liftA (c + k) 1 (.bvar i) = .bvar i
    rw [liftA_bvar, shiftIdx, if_neg (by omega)]

theorem liftChainA_shape (c : Nat) : (liftChainA c).Shape := fun k => ⟨liftMapA (c + k), rfl⟩

/-- the variable index under a whole spec. -/
def wkIdxA : WkSpecA → Nat → Nat
  | [], i => i
  | (_, c) :: ρ, i => wkIdxA ρ (shiftIdx c i)

theorem wkExprA_bvar_idx : (ρ : WkSpecA) → (i : Nat) → wkExprA ρ (.bvar i) = .bvar (wkIdxA ρ i)
  | [], _ => rfl
  | (_, c) :: ρ, i => by
      show wkExprA ρ (liftA c 1 (.bvar i)) = _
      rw [liftA_bvar]
      exact wkExprA_bvar_idx ρ (shiftIdx c i)

theorem wkExprA_letE_ub : (ρ : WkSpecA) → (A w b : ExprA) →
    wkExprA ρ (.letE A w b) = .letE (wkExprA ρ A) (wkExprA ρ w) (wkExprA (WkSpecA.ub ρ) b)
  | [], _, _, _ => rfl
  | (_, c) :: ρ, A, w, b => wkExprA_letE_ub ρ (liftA c 1 A) (liftA c 1 w) (liftA (c + 1) 1 b)

theorem wkExprA_lit : (ρ : WkSpecA) → (t : Nat) → wkExprA ρ (.lit t) = .lit t
  | [], _ => rfl
  | (_, _) :: ρ, t => wkExprA_lit ρ t

/-- a whole weakening spec is a shape map. -/
def wkMapA (σ : WkSpecA) : IotaShapeMapA where
  φ := wkExprA σ
  φb := wkExprA (WkSpecA.ub σ)
  ψ := id
  ψv := wkIdxA σ
  app := wkExprA_app σ
  pi := fun A u B v => wkExprA_pi_ub σ A u B v
  inst := wkExprA_instantiate0A σ
  const := fun r ls => by rw [List.map_id]; exact wkExprA_const σ r ls
  bvar := wkExprA_bvar_idx σ
  sort := wkExprA_sort σ
  lam := fun A u b => wkExprA_lam_ub σ A u b
  letE := wkExprA_letE_ub σ
  lit := wkExprA_lit σ

/-- the spine of a weakened term. -/
theorem appsSpineA_wkExprA (σ : WkSpecA) (e : ExprA) :
    appsSpineA (wkExprA σ e) = (wkExprA σ (appsSpineA e).1, (appsSpineA e).2.map (wkExprA σ)) :=
  (wkMapA σ).appsSpineA_shape e

theorem wkExprA_foldAppsA (σ : WkSpecA) (f : ExprA) (xs : List ExprA) :
    wkExprA σ (foldAppsA f xs) = foldAppsA (wkExprA σ f) (xs.map (wkExprA σ)) :=
  (wkMapA σ).toIotaMapA.foldAppsA_map f xs

/-- a closed telescope applied to weakened arguments. -/
theorem applyTelA_wk_closed (σ : WkSpecA) (xs : List ExprA) {T : ExprA}
    (hcl : ∀ c, liftA c 1 T = T) :
    applyTelA (xs.map (wkExprA σ)) T = (applyTelA xs T).map (wkExprA σ) := by
  have h : applyTelA (xs.map (wkExprA σ)) (wkExprA σ T) = (applyTelA xs T).map (wkExprA σ) :=
    (wkMapA σ).applyTelA_shape xs T
  rw [wkExprA_closed hcl σ] at h
  exact h

/-! ## (3) substitution as a syntax map, and the struct arm under it (W-1 (e): moved up from
    `RcicAnnIotaLaws`, so the fundamental theorem's ι relation reads the struct arm under a
    substitution) -/

/-- substitution `substA σ` is a syntax map (not a shape map: a variable head goes
    anywhere). -/
def substMapA (σ : SubstA) : IotaMapA where
  φ := substA σ
  φb := substA σ.up
  ψ := id
  app := fun _ _ => rfl
  pi := fun _ _ _ _ => rfl
  inst := fun a B => substA_instantiate0A σ a B
  const := fun r ls => by rw [List.map_id] <;> rfl

/-- the substitutions `upNA k σ` at every depth. -/
def substChainA (σ : SubstA) : IotaMapChainA where
  dep k := substMapA (upNA k σ)
  coh := fun k => by
    show substA (upNA k σ).up = substA (upNA (k + 1) σ)
    rw [upNA_succ]
  ψc := fun _ => rfl
  lam := fun k A u b => by
    show substA (upNA k σ) (.lam A u b) = .lam (substA (upNA k σ) A) u (substA (upNA (k + 1) σ) b)
    rw [upNA_succ]
    rfl
  liftk := fun k e => substA_upNA_liftA k σ e
  bound := fun k i hi => by
    show substA (upNA k σ) (.bvar i) = .bvar i
    exact upNA_lt k σ i hi

/-- member types are fixed by every substitution (`EnvClosedA`). -/
theorem substA_mtype {E : ResolvedEnvA} (hE : EnvClosedA E) {r : Nat} {m : CheckedMemberA} (hres : E.members r = some m)
    (ls : List Level) (τ : SubstA) :
    substA τ (instantiateLevelsA ls m.mtypeA) = instantiateLevelsA ls m.mtypeA :=
  substA_closed (liftA_instantiateLevelsA_closed (hE r m hres).1 ls) τ

/-! ## (2b) W-1 (b′): the struct arm under a substitution, on success

ι's contractum at a struct group is the struct arm's, so `IotaSubstA` needs the arm's success law. The
arm's reading moves with the spine's arguments only (the member's type is closed); the projections walk
the member's field count (`structFieldCountA`) along the minor's domain, which a substitution can only
lengthen (`piCountA_le_substA`), with selectors over that many binders, whose bodies are bound
variables a substitution fixes (`fieldSelA_substA`). -/

section StructSubst

/-- a telescope's domains under a substitution (it moves under each binder). -/
def substDomsA (σ : SubstA) : List (ExprA × Level) → List (ExprA × Level)
  | [] => []
  | (D, u) :: ds => (substA σ D, u) :: substDomsA σ.up ds

theorem substDomsA_length (σ : SubstA) : (ds : List (ExprA × Level)) → (substDomsA σ ds).length = ds.length
  | [] => rfl
  | _ :: ds => by simp only [substDomsA, List.length_cons, substDomsA_length σ.up ds]

/-- a substitution only adds Π-binders (at a substituted variable). -/
theorem piCountA_le_substA : (T : ExprA) → (σ : SubstA) → piCountA T ≤ piCountA (substA σ T)
  | .pi _ _ B _, σ => Nat.succ_le_succ (piCountA_le_substA B σ.up)
  | .bvar _, _ => Nat.zero_le _
  | .sort _, _ => Nat.zero_le _
  | .const _ _, _ => Nat.zero_le _
  | .app _ _, _ => Nat.zero_le _
  | .lam _ _ _, _ => Nat.zero_le _
  | .letE _ _ _, _ => Nat.zero_le _
  | .lit _, _ => Nat.zero_le _

theorem piCountA_le_instantiate0A (a B : ExprA) : piCountA B ≤ piCountA (instantiate0A a B) := by
  have h : instantiate0A a B = substA (SubstA.cons a SubstA.id) B := by
    rw [← instantiate0A_substA_up, substA_ext SubstA.id_up B, substA_id]
  rw [h]
  exact piCountA_le_substA B _

/-- the first `k` binders of a type under a substitution, when it has `k`. -/
theorem piDomListA_substA_take : (k : Nat) → (T : ExprA) → (σ : SubstA) → k ≤ piCountA T →
    (piDomListA (substA σ T)).take k = substDomsA σ ((piDomListA T).take k)
  | 0, _, _, _ => rfl
  | k + 1, .pi D u B v, σ, hT => by
      show (substA σ D, u) :: (piDomListA (substA σ.up B)).take k =
        (substA σ D, u) :: substDomsA σ.up ((piDomListA B).take k)
      rw [piDomListA_substA_take k B σ.up (Nat.le_of_succ_le_succ hT)]
  | _ + 1, .bvar _, _, hT => absurd hT (Nat.not_succ_le_zero _)
  | _ + 1, .sort _, _, hT => absurd hT (Nat.not_succ_le_zero _)
  | _ + 1, .const _ _, _, hT => absurd hT (Nat.not_succ_le_zero _)
  | _ + 1, .app _ _, _, hT => absurd hT (Nat.not_succ_le_zero _)
  | _ + 1, .lam _ _ _, _, hT => absurd hT (Nat.not_succ_le_zero _)
  | _ + 1, .letE _ _ _, _, hT => absurd hT (Nat.not_succ_le_zero _)
  | _ + 1, .lit _, _, hT => absurd hT (Nat.not_succ_le_zero _)

/-- a substitution fixing the variables below `n` fixes those below `n + 1` under a binder. -/
theorem substA_up_fix {σ : SubstA} {n : Nat} (hσ : ∀ i, i < n → σ i = .bvar i) :
    ∀ i, i < n + 1 → σ.up i = .bvar i
  | 0, _ => rfl
  | i + 1, hi => by
      show liftA 0 1 (σ i) = .bvar (i + 1)
      rw [hσ i (by omega), liftA_bvar, shiftIdx, if_pos (Nat.zero_le i)]

/-- a variable bound by the telescope (or fixed below it) is fixed. -/
theorem substA_lamTelA_bvar : (ds : List (ExprA × Level)) → (σ : SubstA) → (n j : Nat) →
    (∀ i, i < n → σ i = .bvar i) → j < n + ds.length →
    substA σ (lamTelA ds (.bvar j)) = lamTelA (substDomsA σ ds) (.bvar j)
  | [], σ, n, j, hσ, hj => hσ j (by simpa using hj)
  | (D, u) :: ds, σ, n, j, hσ, hj => by
      show ExprA.lam (substA σ D) u (substA σ.up (lamTelA ds (.bvar j))) =
        .lam (substA σ D) u (lamTelA (substDomsA σ.up ds) (.bvar j))
      rw [substA_lamTelA_bvar ds σ.up (n + 1) j (substA_up_fix hσ)
        (by simp only [List.length_cons] at hj; omega)]

theorem fieldSelA_substA (σ : SubstA) (ds : List (ExprA × Level)) (i : Nat) (hi : i < ds.length) :
    fieldSelA (substDomsA σ ds) i = substA σ (fieldSelA ds i) := by
  unfold fieldSelA
  rw [substDomsA_length, substA_lamTelA_bvar ds σ 0 _ (fun _ h => absurd h (Nat.not_lt_zero _))
    (by omega)]

theorem structProjA_substA (σ : SubstA) (r : Nat) (ls₀ : List Level) (ps : List ExprA) (S : ExprA)
    (uS : Level) (ds : List (ExprA × Level)) (x : ExprA) (i : Nat) (F : ExprA) (hi : i < ds.length) :
    structProjA r ls₀ (ps.map (substA σ)) (substA σ S) uS (substDomsA σ ds) (substA σ x) i (substA σ F) =
      substA σ (structProjA r ls₀ ps S uS ds x i F) := by
  have hfold : ∀ (f : ExprA) (xs : List ExprA),
      substA σ (foldAppsA f xs) = foldAppsA (substA σ f) (xs.map (substA σ)) :=
    (substMapA σ).foldAppsA_map
  unfold structProjA
  rw [hfold, List.map_append, fieldSelA_substA σ ds i hi]
  simp only [List.map_cons, List.map_nil, substA_lam, substA_up_liftA]
  rfl

theorem structProjsA_substA (σ : SubstA) (r : Nat) (ls₀ : List Level) (ps : List ExprA) (S : ExprA)
    (uS : Level) (ds : List (ExprA × Level)) (x : ExprA) :
    (k i : Nat) → (T : ExprA) → i + k ≤ ds.length → k ≤ piCountA T →
    structProjsA r ls₀ (ps.map (substA σ)) (substA σ S) uS (substDomsA σ ds) (substA σ x) k i (substA σ T) =
      (structProjsA r ls₀ ps S uS ds x k i T).map (substA σ)
  | 0, _, _, _, _ => rfl
  | k + 1, i, .pi F u B v, hk, hT => by
      show structProjA r ls₀ (ps.map (substA σ)) (substA σ S) uS (substDomsA σ ds) (substA σ x) i
            (substA σ F) ::
          structProjsA r ls₀ (ps.map (substA σ)) (substA σ S) uS (substDomsA σ ds) (substA σ x) k (i + 1)
            (instantiate0A (structProjA r ls₀ (ps.map (substA σ)) (substA σ S) uS (substDomsA σ ds)
              (substA σ x) i (substA σ F)) (substA σ.up B)) = _
      rw [structProjA_substA σ r ls₀ ps S uS ds x i F (by omega), ← substA_instantiate0A,
        structProjsA_substA σ r ls₀ ps S uS ds x k (i + 1) _ (by omega)
          (Nat.le_trans (Nat.le_of_succ_le_succ hT) (piCountA_le_instantiate0A _ B))]
      rfl
  | _ + 1, _, .bvar _, _, hT => absurd hT (Nat.not_succ_le_zero _)
  | _ + 1, _, .sort _, _, hT => absurd hT (Nat.not_succ_le_zero _)
  | _ + 1, _, .const _ _, _, hT => absurd hT (Nat.not_succ_le_zero _)
  | _ + 1, _, .app _ _, _, hT => absurd hT (Nat.not_succ_le_zero _)
  | _ + 1, _, .lam _ _ _, _, hT => absurd hT (Nat.not_succ_le_zero _)
  | _ + 1, _, .letE _ _ _, _, hT => absurd hT (Nat.not_succ_le_zero _)
  | _ + 1, _, .lit _, _, hT => absurd hT (Nat.not_succ_le_zero _)

/-- a substitution on what the struct arm reads: the member's type is closed, so only what the spine's
    arguments carry moves. -/
def StructSpineA.substS (σ : SubstA) (d : StructSpineA) : StructSpineA :=
  ⟨d.r, d.ls₀, d.ps.map (substA σ), substA σ d.S, d.uS, substA σ d.Dm, substA σ d.mn, d.nf⟩

theorem StructSpineA.reduct_substA (σ : SubstA) (d : StructSpineA) (x : ExprA) (hn : d.nf ≤ piCountA d.Dm) :
    (d.substS σ).reduct (substA σ x) = substA σ (d.reduct x) := by
  have hfold : ∀ (f : ExprA) (xs : List ExprA),
      substA σ (foldAppsA f xs) = foldAppsA (substA σ f) (xs.map (substA σ)) :=
    (substMapA σ).foldAppsA_map
  unfold StructSpineA.reduct StructSpineA.substS
  dsimp only
  rw [hfold, piDomListA_substA_take d.nf d.Dm σ hn,
    structProjsA_substA σ d.r d.ls₀ d.ps d.S d.uS ((piDomListA d.Dm).take d.nf) x d.nf 0 d.Dm
      (by rw [List.length_take, piDomListA_length]; omega) hn]

/-- the struct arm's reading, read back. -/
theorem structSpineA_some {E : ResolvedEnvA} {f : ExprA} {d : StructSpineA} (h : structSpineA E f = some d) :
    ∃ g mn r ls m Dm u B v S uS C w, f = .app g mn ∧ (appsSpineA g).1 = .const r ls ∧
      E.members r = some m ∧ structGroupA r m = true ∧
      applyTelA (appsSpineA g).2 (instantiateLevelsA ls m.mtypeA) = some (.pi Dm u B v) ∧
      instantiate0A mn B = .pi S uS C w ∧
      d = ⟨r, motZeroLevelsA ls, (appsSpineA g).2.dropLast, S, uS, Dm, mn, structFieldCountA m⟩ := by
  cases f
  case app g mn =>
    dsimp only [structSpineA] at h
    split at h
    · rename_i r ls hh
      split at h
      · rename_i m hm
        split at h
        · rename_i hs
          split at h
          · rename_i Dm u B v ha
            split at h
            · rename_i S uS C w hB
              injection h with h
              subst h
              exact ⟨g, mn, r, ls, m, Dm, u, B, v, S, uS, C, w, rfl, hh, hm, hs, ha, hB, rfl⟩
            · exact Option.noConfusion h
          · exact Option.noConfusion h
        · exact Option.noConfusion h
      · exact Option.noConfusion h
    · exact Option.noConfusion h
  all_goals exact absurd h (by simp [structSpineA])

/-- the struct arm's reading, forward. -/
theorem structSpineA_of_parts {E : ResolvedEnvA} {g mn : ExprA} {r : Nat} {ls : List Level}
    {args : List ExprA} {m : CheckedMemberA} {Dm B S C : ExprA} {u v uS w : Level}
    (hh : appsSpineA g = (.const r ls, args)) (hm : E.members r = some m) (hs : structGroupA r m = true)
    (ha : applyTelA args (instantiateLevelsA ls m.mtypeA) = some (.pi Dm u B v))
    (hB : instantiate0A mn B = .pi S uS C w) :
    structSpineA E (.app g mn) =
      some ⟨r, motZeroLevelsA ls, args.dropLast, S, uS, Dm, mn, structFieldCountA m⟩ := by
  simp only [structSpineA, hh, hm, hs, if_true, ha, hB]

/-- THE STRUCT ARM'S READING UNDER A SUBSTITUTION, on success. -/
theorem structSpineA_substA {E : ResolvedEnvA} (hE : EnvClosedA E) (σ : SubstA) {f : ExprA}
    {d : StructSpineA} (h : structSpineA E f = some d) : structSpineA E (substA σ f) = some (d.substS σ) := by
  obtain ⟨g, mn, r, ls, m, Dm, u, B, v, S, uS, C, w, rfl, hh, hm, hs, ha, hB, rfl⟩ := structSpineA_some h
  have hh' : appsSpineA (substA σ g) = (.const r ls, (appsSpineA g).2.map (substA σ)) := by
    have h1 : appsSpineA (substA σ g) = (.const r (ls.map id), (appsSpineA g).2.map (substA σ)) :=
      (substMapA σ).appsSpineA_const g hh
    rwa [List.map_id] at h1
  have ha' : applyTelA ((appsSpineA g).2.map (substA σ)) (instantiateLevelsA ls m.mtypeA) =
      some (.pi (substA σ Dm) u (substA σ.up B) v) := by
    have h1 : applyTelA ((appsSpineA g).2.map (substA σ)) (substA σ (instantiateLevelsA ls m.mtypeA)) =
        some (substA σ (.pi Dm u B v)) := (substMapA σ).applyTelA_some _ ha
    rwa [substA_mtype hE hm ls σ] at h1
  have hB' : instantiate0A (substA σ mn) (substA σ.up B) = .pi (substA σ S) uS (substA σ.up C) w := by
    rw [← substA_instantiate0A, hB]
    rfl
  show structSpineA E (.app (substA σ g) (substA σ mn)) = _
  rw [structSpineA_of_parts hh' hm hs ha' hB']
  simp only [StructSpineA.substS, List.map_dropLast]

/-- THE STRUCT ARM UNDER A SUBSTITUTION, on success. -/
theorem structArmA_substA {E : ResolvedEnvA} (hE : EnvClosedA E) (σ : SubstA) {f x e : ExprA}
    (h : structArmA E f x = some e) : structArmA E (substA σ f) (substA σ x) = some (substA σ e) := by
  obtain ⟨d, hs, hn, rfl⟩ := structArmA_some h
  unfold structArmA
  rw [structSpineA_substA hE σ hs, Option.some_bind]
  show (if d.nf ≤ piCountA (substA σ d.Dm) then some ((d.substS σ).reduct (substA σ x)) else none) = _
  rw [if_pos (Nat.le_trans hn (piCountA_le_substA d.Dm σ)), StructSpineA.reduct_substA σ d x hn]

end StructSubst

#print axioms IotaMapChainA.rhsArgsA_map
#print axioms IotaMapChainA.fieldsTelA_shape
#print axioms IotaMapChainA.recCallFunA_map
#print axioms applyTelA_wk_closed
#print axioms piCountA_le_substA
#print axioms piDomListA_substA_take
#print axioms fieldSelA_substA
#print axioms structProjsA_substA
#print axioms structSpineA_some
#print axioms structSpineA_substA
#print axioms structArmA_substA

end Rcic.Declarative.Ann
