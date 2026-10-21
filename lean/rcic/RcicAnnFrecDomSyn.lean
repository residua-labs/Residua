import rcic.RcicAnnFamBuild
import rcic.RcicAnnSpineConv

/-!
# R-NoFunRec-1 step 1 (1c-ε2d-a0) — the function-recursive domain's syntactic evidence

The function-recursive field's domain is typed in the group environment `G`, a prefix of the full one,
by the view-typing chain (`frecDomTyG`). This module holds that chain below the recursors' clause, and
the experiment of (1c-ε2d-a0): the conversion between the two instances' declared domains, produced
from syntactic typing in `G`, level irrelevance, and the walk's valid substitution evidence, with no
semantic fundamental theorem of `G` or `E`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (0) the fields' typing (R-NoFunRec-1 step 1 (1c-ε2d-0))

Moved here from `RcicAnnViewTy`, below the recursors' clause, with the typed recursor-head fact
(`IotaRecHeadTypedA`) in place of `IotaRecHeadA`: the group environment, a prefix of the full one, has
only the typed fact (`iotaRecHeadTypedA_prefix`). R-NoFunRec-1 step 1 (1c-ε2d): the family-open data
(`viewTy_openFam`), the environment moves of the fields' typing (`viewTy_fields_env`) and the weakening past
a context (`viewTy_wkBy`) moved with it, for the whole function-recursive domain's typing (`frecDomTyG`). -/

section ViewTyFields
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- a telescope whose body is `Sort w`. `Type`, not `Prop`: the fold eliminates it
    into a derivation. -/
inductive IsIdxTel : ExprA → Level → Type
  | sort (w : Level) : IsIdxTel (.sort w) w
  | pi (A : ExprA) (u : Level) (B : ExprA) (v : Level) (h : IsIdxTel B w) :
      IsIdxTel (.pi A u B v) w

def isIdxTel_lift (c a : Nat) : {T : ExprA} → {w : Level} → IsIdxTel T w →
    IsIdxTel (liftA c a T) w
  | _, w, .sort _ => by
      simp only [liftA]
      exact .sort w
  | _, w, .pi _ u _ v h => by
      simp only [liftA]
      exact .pi _ u _ v (isIdxTel_lift (c + 1) a h)

def isIdxTel_instantiate (k : Nat) (r : ExprA) : {T : ExprA} → {w : Level} →
    IsIdxTel T w → IsIdxTel (instantiateA k r T) w
  | _, w, .sort _ => by
      simp only [instantiateA]
      exact .sort w
  | _, w, .pi _ u _ v h => by
      simp only [instantiateA]
      exact .pi _ u _ v (isIdxTel_instantiate (k + 1) (liftA 0 1 r) h)

def isIdxTel_piTel (w s : Level) : (ds : List (ExprA × Level)) →
    IsIdxTel (piTelA ds (.sort w) s).1 w
  | [] => by
      simp only [piTelA]
      exact .sort w
  | (_, u) :: ds => by
      simp only [piTelA]
      exact .pi _ u _ _ (isIdxTel_piTel w s ds)

theorem instantiate0A_sort (a : ExprA) (v : Level) : instantiate0A a (.sort v) = .sort v := rfl

theorem viewTy_instLevel_canon (a : Nat) : (l : Level) → instLevel (canonLevelsA a) l = l
  | .zero => rfl
  | .succ l => congrArg Level.succ (viewTy_instLevel_canon a l)
  | .max x y => by
      show Level.max (instLevel _ x) (instLevel _ y) = _
      rw [viewTy_instLevel_canon a x, viewTy_instLevel_canon a y]
  | .imax x y => by
      show Level.imax (instLevel _ x) (instLevel _ y) = _
      rw [viewTy_instLevel_canon a x, viewTy_instLevel_canon a y]
  | .param i => by
      rw [instLevel_param]
      by_cases h : i < a
      · simp [canonLevelsA, List.getElem?_map, List.getElem?_range, h]
      · have hnone : (canonLevelsA a)[i]? = none := by
          simp only [canonLevelsA, List.getElem?_map, List.getElem?_range]
          simp [h, Nat.le_of_not_lt h]
        simp [hnone]

theorem viewTy_map_instLevel_canon (a : Nat) :
    (ms : List Level) → ms.map (instLevel (canonLevelsA a)) = ms
  | [] => rfl
  | l :: ms => by
      simp only [List.map, viewTy_instLevel_canon a l, viewTy_map_instLevel_canon a ms]

theorem viewTy_instantiateLevelsA_canon (a : Nat) :
    (e : ExprA) → instantiateLevelsA (canonLevelsA a) e = e
  | .bvar _ => rfl
  | .sort l => by simp only [instantiateLevelsA, viewTy_instLevel_canon]
  | .const _ ms => by
      simp only [instantiateLevelsA, viewTy_map_instLevel_canon a ms]
  | .app f x => by
      simp only [instantiateLevelsA, viewTy_instantiateLevelsA_canon a f,
        viewTy_instantiateLevelsA_canon a x]
  | .lam x u b => by
      simp only [instantiateLevelsA, viewTy_instLevel_canon, viewTy_instantiateLevelsA_canon a x,
        viewTy_instantiateLevelsA_canon a b]
  | .pi x u b v => by
      simp only [instantiateLevelsA, viewTy_instLevel_canon, viewTy_instantiateLevelsA_canon a x,
        viewTy_instantiateLevelsA_canon a b]
  | .letE x w b => by
      simp only [instantiateLevelsA, viewTy_instantiateLevelsA_canon a x,
        viewTy_instantiateLevelsA_canon a w, viewTy_instantiateLevelsA_canon a b]
  | .lit _ => rfl

theorem viewTy_canon_length (a : Nat) : (canonLevelsA a).length = a := by
  simp [canonLevelsA, List.length_map, List.length_range]

theorem viewTy_levelBounded_mono {a b : Nat} (hab : a ≤ b) :
    (l : Level) → levelBounded a l = true → levelBounded b l = true
  | .zero, _ => rfl
  | .succ l, h => viewTy_levelBounded_mono hab l h
  | .max x y, h => by
      simp only [levelBounded, Bool.and_eq_true] at h ⊢
      exact ⟨viewTy_levelBounded_mono hab x h.1, viewTy_levelBounded_mono hab y h.2⟩
  | .imax x y, h => by
      simp only [levelBounded, Bool.and_eq_true] at h ⊢
      exact ⟨viewTy_levelBounded_mono hab x h.1, viewTy_levelBounded_mono hab y h.2⟩
  | .param i, h => by
      simp only [levelBounded] at h ⊢
      exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h) hab)

theorem viewTy_levelsBounded_mono {a b : Nat} (hab : a ≤ b) :
    (ls : List Level) → levelsBounded a ls = true → levelsBounded b ls = true
  | [], _ => rfl
  | l :: ls, h => by
      simp only [levelsBounded, Bool.and_eq_true] at h ⊢
      exact ⟨viewTy_levelBounded_mono hab l h.1, viewTy_levelsBounded_mono hab ls h.2⟩

theorem viewTy_levelsBounded_canon (a : Nat) : levelsBounded a (canonLevelsA a) = true := by
  have canon : ∀ xs : List Nat, (∀ i ∈ xs, i < a) → levelsBounded a (xs.map Level.param) = true := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons i xs ih =>
        intro h
        simp only [List.map_cons, levelsBounded, Bool.and_eq_true]
        refine ⟨?_, ih (fun j hj => h j (List.mem_cons_of_mem _ hj))⟩
        simp only [levelBounded]
        exact decide_eq_true (h i (List.mem_cons_self _ _))
  simpa [canonLevelsA] using canon (List.range a) (fun i hi => List.mem_range.mp hi)

theorem viewTy_subst_shift1 (σ : SubstA) (e : ExprA) :
    substA σ.shift1 e = liftA 0 1 (substA σ e) := by
  unfold SubstA.shift1
  exact (liftA_substA 0 σ e).symm

theorem viewTy_map_shift1 (σ : SubstA) :
    (pl : List ExprA) → pl.map (substA σ.shift1) = (pl.map (substA σ)).map (liftA 0 1)
  | [] => rfl
  | p :: pl => by
      simp only [List.map, viewTy_subst_shift1 σ p, viewTy_map_shift1 σ pl]

/-- past a binder the plain substitution does not name: images lift, the source
    context does not grow. -/
def substTyA_shift1 (hE : EnvClosedA E) (hI : IotaLiftA I) {Δ Γ : LCtxA} {σ : SubstA}
    (hσ : SubstTyA E I n Δ σ Γ) (D : ExprA) :
    SubstTyA E I n (.assumption D :: Δ) σ.shift1 Γ where
  ty := fun i A h => by
    have hw := hasTyWeakenA hE hI (.assumption D) (Nat.zero_le _) (hσ.ty i A h)
    simp only [insertAtA] at hw
    rw [← viewTy_subst_shift1 σ A] at hw
    rw [show liftA 0 1 (σ i) = σ.shift1 i from rfl] at hw
    exact hw
  val := fun i A v hty hval => by
    have hw := convWeakenA hE hI (.assumption D) (Nat.zero_le _) (hσ.val i A v hty hval)
    simp only [insertAtA] at hw
    rw [← viewTy_subst_shift1 σ v, ← viewTy_subst_shift1 σ A] at hw
    rw [show liftA 0 1 (σ i) = σ.shift1 i from rfl] at hw
    exact hw

theorem viewTy_eta_lift (k : Nat) (f : ExprA) :
    liftA 0 k (ExprA.app (liftA 0 1 f) (ExprA.bvar 0)) =
      ExprA.app (liftA 0 (k + 1) f) (ExprA.bvar k) := by
  have hApp : liftA 0 k (ExprA.app (liftA 0 1 f) (ExprA.bvar 0)) =
      ExprA.app (liftA 0 k (liftA 0 1 f)) (liftA 0 k (ExprA.bvar 0)) := by
    simp only [liftA]
  rw [hApp, liftA_liftA_merge k 1 0 0 (Nat.le_refl 0) (Nat.zero_le _) f]
  rw [show 1 + k = k + 1 from Nat.add_comm 1 k]
  have hb : liftA 0 k (ExprA.bvar 0) = ExprA.bvar k := by
    simp only [liftA, Nat.zero_le, ite_true, Nat.zero_add]
  rw [hb]

theorem viewTy_apply_locals (k : Nat) (f : ExprA) :
    foldAppsA (liftA 0 k (.app (liftA 0 1 f) (.bvar 0))) (paramLocalsA k) =
      foldAppsA (liftA 0 (k + 1) f) (paramLocalsA (k + 1)) := by
  rw [viewTy_eta_lift]
  rfl

/-- arguments typed along a telescope that ends in `Sort w`. The telescope expression
    is typed on its own (`hasTyA_pi_parts` inverts a subject that is a Π). -/
def viewTy_foldIdx (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) :
    {T : ExprA} → {w : Level} → IsIdxTel T w → {s : Level} → HasTyA E I n Γ T (.sort s) →
    {f : ExprA} → HasTyA E I n Γ f T → {as : List ExprA} → ArgsTyA E I n Γ T as →
    HasTyA E I n Γ (foldAppsA f as) (.sort w)
  | _, w, .sort _, _, _, _, hf, _, .nil _ => hf
  | _, w, .pi A u B v hRest, _, hT, f, hf, _, .cons _ _ _ _ a _ ha tl => by
      obtain ⟨tA, tB⟩ := hasTyA_pi_parts hT
      have hInst := hasTyA_inst0 hE hI hR hIS hΓ tB ha tA
      have hInst' : HasTyA E I n Γ (instantiate0A a B) (.sort v) :=
        instantiate0A_sort a v ▸ hInst
      have hApp := HasTyA.app Γ f a A B u v v tB hInst' hf ha
      have hTel := isIdxTel_instantiate 0 a hRest
      rw [show instantiateA 0 a B = instantiate0A a B from rfl] at hTel
      exact viewTy_foldIdx hE hI hR hIS hΓ hTel hInst' hApp tl

/-- the parameter locals, under the telescope: `f` at `Π ds, B` becomes
    `f` applied to `bvar (length-1) … bvar 0`, typed at `B`. -/
def viewTy_applyParams (hE : EnvClosedA E) (hI : IotaLiftA I) {Γ : LCtxA}
    (hΓ : CtxWfA E I n Γ) :
    {ds : List (ExprA × Level)} → {B : ExprA} → {wb u : Level} →
    HasTyA E I n Γ (piTelA ds B wb).1 (.sort u) →
    {f : ExprA} → HasTyA E I n Γ f (piTelA ds B wb).1 →
    HasTyA E I n (telCtxA ds ++ Γ)
      (foldAppsA (liftA 0 ds.length f) (paramLocalsA ds.length)) B
  | [], _, _, _, _, f, hf => by
      simpa [piTelA, telCtxA, paramLocalsA, foldAppsA, liftA_zero] using hf
  | (D, du) :: ds, B, wb, _, hT, f, hf => by
      obtain ⟨tD, tC⟩ := hasTyA_pi_parts hT
      have hη := hasTyA_eta_body hE hI tD tC hf
      have ih := viewTy_applyParams hE hI (.assumption hΓ tD) tC hη
      simp only [List.length_cons]
      rw [telCtxA_cons_append (D, du) ds Γ]
      rw [← viewTy_apply_locals ds.length f]
      exact ih

/-- the family's constant, at the canonical level vector, typed at the stored type. -/
def viewTy_famConst {Γ : LCtxA} {f : Nat} {fm : CheckedMemberA} {u : Level}
    (hn : fm.arity ≤ n) (hmem : E.members f = some fm)
    (hFam : HasTyA E I n Γ fm.mtypeA (.sort u)) :
    HasTyA E I n Γ (.const f (canonLevelsA fm.arity)) fm.mtypeA := by
  have hid : instantiateLevelsA (canonLevelsA fm.arity) fm.mtypeA = fm.mtypeA :=
    viewTy_instantiateLevelsA_canon fm.arity _
  have hwf : levelsBounded n (canonLevelsA fm.arity) = true :=
    viewTy_levelsBounded_mono hn _ (viewTy_levelsBounded_canon _)
  exact hid ▸ HasTyA.const Γ f (canonLevelsA fm.arity) fm u hmem (viewTy_canon_length _) hwf
    (hid.symm ▸ hFam)

/-- what a plain field does to the family application and the index telescope.
    The minor walker of T2 steps by this same function: the field domain is
    `ctorFieldsA`'s, whether or not an induction hypothesis is interleaved after it. -/
structure ViewTyIdxStepA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (f : Nat)
    (ls : List Level) (w : Level) (idxBase : ExprA) (Γp Γt : LCtxA) (σ : SubstA)
    (k : Nat) (s : Level) (plP pl : List ExprA) (D : ExprA) (u : Level) : Type where
  substTy : SubstTyA E I n (.assumption (substA σ D) :: Γt) σ.up (.assumption D :: Γp)
  ctxP : CtxWfA E I n (.assumption D :: Γp)
  ctxT : CtxWfA E I n (.assumption (substA σ D) :: Γt)
  pl : pl.map (liftA 0 1) = (plP.map (liftA 0 1)).map (substA σ.up)
  fp : HasTyA E I n (.assumption D :: Γp)
    (foldAppsA (.const f ls) (plP.map (liftA 0 1))) (liftA 0 (k + 1) idxBase)
  idx : HasTyA E I n (.assumption D :: Γp) (liftA 0 (k + 1) idxBase) (.sort s)
  tel : IsIdxTel (liftA 0 (k + 1) idxBase) w

def viewTy_idxStep (hE : EnvClosedA E) (hI : IotaLiftA I) {f : Nat} {ls : List Level}
    {w : Level} {idxBase : ExprA} {Γp Γt : LCtxA} {σ : SubstA} {k : Nat} {s : Level}
    {plP pl : List ExprA} {D : ExprA} {u : Level}
    (hσ : SubstTyA E I n Γt σ Γp) (hΓp : CtxWfA E I n Γp) (hΓt : CtxWfA E I n Γt)
    (hpl : pl = plP.map (substA σ))
    (hFp : HasTyA E I n Γp (foldAppsA (.const f ls) plP) (liftA 0 k idxBase))
    (hIdx : HasTyA E I n Γp (liftA 0 k idxBase) (.sort s))
    (hTel : IsIdxTel (liftA 0 k idxBase) w)
    (hD : HasTyA E I n Γp D (.sort u))
    (hDom : HasTyA E I n Γt (substA σ D) (.sort u)) :
    ViewTyIdxStepA E I n f ls w idxBase Γp Γt σ k s plP pl D u := by
  have hσ' := substTyA_up hE hI hσ hDom
  have hΓp' : CtxWfA E I n (.assumption D :: Γp) := .assumption hΓp hD
  have hΓt' : CtxWfA E I n (.assumption (substA σ D) :: Γt) := .assumption hΓt hDom
  have hpl' : pl.map (liftA 0 1) = (plP.map (liftA 0 1)).map (substA σ.up) := by
    rw [hpl]
    exact (map_substA_up_liftA σ plP).symm
  have hmerge : liftA 0 1 (liftA 0 k idxBase) = liftA 0 (k + 1) idxBase := by
    rw [liftA_liftA_merge 1 k 0 0 (Nat.le_refl _) (Nat.zero_le _) idxBase]
  have hFp0 := hasTyWeakenA hE hI (.assumption D) (Nat.zero_le _) hFp
  have hFp' : HasTyA E I n (.assumption D :: Γp)
      (foldAppsA (.const f ls) (plP.map (liftA 0 1))) (liftA 0 (k + 1) idxBase) := by
    simp only [insertAtA] at hFp0
    rw [liftA_foldAppsA, show liftA 0 1 (.const f ls) = .const f ls from rfl, hmerge] at hFp0
    exact hFp0
  have hIdx0 := hasTyWeakenA hE hI (.assumption D) (Nat.zero_le _) hIdx
  have hIdx' : HasTyA E I n (.assumption D :: Γp) (liftA 0 (k + 1) idxBase) (.sort s) := by
    simp only [insertAtA, liftA] at hIdx0
    rw [hmerge] at hIdx0
    exact hIdx0
  have hTel' : IsIdxTel (liftA 0 (k + 1) idxBase) w := by
    have h := isIdxTel_lift 0 1 hTel
    rw [hmerge] at h
    exact h
  exact ⟨hσ', hΓp', hΓt', hpl', hFp', hIdx', hTel'⟩

def viewTy_fields (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {f : Nat} {ls : List Level} {w : Level} {idxBase : ExprA}
    {Γp Γt : LCtxA} {σ : SubstA} (hσ : SubstTyA E I n Γt σ Γp)
    (hΓp : CtxWfA E I n Γp) (hΓt : CtxWfA E I n Γt) :
    {k : Nat} → {s : Level} → {plP pl : List ExprA} →
    (hpl : pl = plP.map (substA σ)) →
    (hFp : HasTyA E I n Γp (foldAppsA (.const f ls) plP) (liftA 0 k idxBase)) →
    (hIdx : HasTyA E I n Γp (liftA 0 k idxBase) (.sort s)) →
    (hTel : IsIdxTel (liftA 0 k idxBase) w) →
    {fs : List FieldA} → {res : List ExprA} →
    FieldsTyA E I n (fun k => liftA 0 k idxBase) Γp k fs res → (∀ x ∈ fs, x.NoDelta) →
    HasTyA E I n Γt (ctorFieldsA f ls w pl σ fs res).1
      (.sort (ctorFieldsA f ls w pl σ fs res).2)
  | _, _, _, _, hpl, hFp, hIdx, hTel, _, _, .nil _ _ res hres, _ => by
      have hApp := viewTy_foldIdx hE hI hR hIS hΓp hTel hIdx hFp hres
      rw [← foldAppsA_append] at hApp
      have hSub := hasTyA_substA hE hI hR hIS hσ hApp
      rw [substA_sort, substA_foldAppsA, substA_const, List.map_append, ← hpl] at hSub
      simpa [ctorFieldsA] using hSub
  | k, s, plP, pl, hpl, hFp, hIdx, hTel, _, res,
      .plain _ _ D u fs _ hD tl, hnd => by
      have hDom : HasTyA E I n Γt (substA σ D) (.sort u) := by
        have h := hasTyA_substA hE hI hR hIS hσ hD
        rw [substA_sort] at h
        exact h
      let step := viewTy_idxStep hE hI hσ hΓp hΓt hpl hFp hIdx hTel hD hDom
      have ih := viewTy_fields hE hI hR hIS step.substTy step.ctxP step.ctxT step.pl
        step.fp step.idx step.tel tl (fun x hx => hnd x (List.mem_cons_of_mem _ hx))
      simpa [ctorFieldsA] using
        (HasTyA.pi Γt (substA σ D) u _ _ hDom ih)
  | _, _, plP, pl, hpl, hFp, hIdx, hTel, _, res, .drec _ _ idx fs _ hidx tl, hnd => by
      have hApp := viewTy_foldIdx hE hI hR hIS hΓp hTel hIdx hFp hidx
      rw [← foldAppsA_append] at hApp
      have hDom0 := hasTyA_substA hE hI hR hIS hσ hApp
      rw [substA_sort, substA_foldAppsA, substA_const, List.map_append, ← hpl] at hDom0
      have hDom : HasTyA E I n Γt
          (foldAppsA (.const f ls) (pl ++ idx.map (substA σ))) (.sort w) := hDom0
      have hσ' := substTyA_shift1 hE hI hσ
        (foldAppsA (.const f ls) (pl ++ idx.map (substA σ)))
      have hΓt' := CtxWfA.assumption hΓt hDom
      have hpl' : pl.map (liftA 0 1) = plP.map (substA σ.shift1) := by
        rw [hpl]
        exact (viewTy_map_shift1 σ plP).symm
      have ih := viewTy_fields hE hI hR hIS hσ' hΓp hΓt' hpl' hFp hIdx hTel tl
        (fun x hx => hnd x (List.mem_cons_of_mem _ hx))
      simpa [ctorFieldsA] using (HasTyA.pi Γt _ w _ _ hDom ih)
  | _, _, plP, pl, hpl, hFp, hIdx, hTel, _, res, .frec _ _ B uB Bs idx fs _ hdom tl, hnd => by
      -- the domain: the inner binders as plain fields, ending in the family at the indices
      have hDom := viewTy_fields hE hI hR hIS hσ hΓp hΓt hpl hFp hIdx hTel hdom (plainA_noDelta _)
      rw [← frecDomA_eq] at hDom
      have hσ' := substTyA_shift1 hE hI hσ (frecDomA f ls w pl σ ((B, uB) :: Bs) idx).1
      have hΓt' := CtxWfA.assumption hΓt hDom
      have hpl' : pl.map (liftA 0 1) = plP.map (substA σ.shift1) := by
        rw [hpl]
        exact (viewTy_map_shift1 σ plP).symm
      have ih := viewTy_fields hE hI hR hIS hσ' hΓp hΓt' hpl' hFp hIdx hTel tl
        (fun x hx => hnd x (List.mem_cons_of_mem _ hx))
      exact HasTyA.pi Γt _ _ _ _ hDom ih
  | _, _, plP, pl, hpl, hFp, hIdx, hTel, _, res, .drecD _ _ D idx fs _ hidx tl, hnd =>
      (hnd _ (List.mem_cons_self _ _)).elim

/-- the walk's substitution past the plain binders: source variables `j + t` are carried to
    locals `t + d`, `d` the binders consumed (every field binds once). Maintained by `up` at
    plain fields and `shift1` at recursive ones (R-NoDeltaRec-4d-iii). -/
theorem substA_walk_ge {σ : SubstA} {j d : Nat} (h : ∀ t, σ (j + t) = .bvar (t + d)) :
    (∀ t, σ.up (j + 1 + t) = .bvar (t + (d + 1))) ∧
    (∀ t, σ.shift1 (j + t) = .bvar (t + (d + 1))) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [Nat.add_right_comm j 1 t, SubstA.up_succ, h t]
    show liftA 0 1 (.bvar (t + d)) = .bvar (t + (d + 1))
    rw [show t + (d + 1) = t + d + 1 from by omega]
    simp only [liftA]; rw [if_pos (Nat.zero_le _)]
  · show liftA 0 1 (σ (j + t)) = .bvar (t + (d + 1))
    rw [h t, show t + (d + 1) = t + d + 1 from by omega]
    simp only [liftA]; rw [if_pos (Nat.zero_le _)]

/-- the walk's substitution on the lifted parameter locals lands on the walked `pl`. -/
theorem substA_walk_paramLocals {σ : SubstA} {j d : Nat}
    (h : ∀ t, σ (j + t) = .bvar (t + d)) :
    ∀ np, ((paramLocalsA np).map (liftA 0 j)).map (substA σ) =
      (paramLocalsA np).map (liftA 0 d)
  | 0 => rfl
  | np + 1 => by
      have hL : liftA 0 j (.bvar np) = .bvar (np + j) := by
        unfold liftA; rw [if_pos (Nat.zero_le np)]
      have hnp := h np
      rw [show j + np = np + j from Nat.add_comm _ _] at hnp
      have hh : substA σ (liftA 0 j (.bvar np)) = liftA 0 d (.bvar np) := by
        rw [hL, substA_bvar, hnp]
        show ExprA.bvar (np + d) = liftA 0 d (ExprA.bvar np)
        unfold liftA; rw [if_pos (Nat.zero_le np)]
      simp only [paramLocalsA, List.map_cons, List.map_map]
      rw [hh]
      have e := substA_walk_paramLocals h np
      simp only [List.map_map] at e
      exact congrArg (_ :: ·) e

/-- the identity substitution satisfies the walk invariant at `0`. -/
theorem substA_walk_ge_id : ∀ t, SubstA.id (0 + t) = .bvar (t + 0) := fun t => by
  rw [Nat.zero_add, Nat.add_zero]; rfl

/-- `norm` never changes the telescope's level: every field's sort annotation is
    `norm`-invariant (`drecD` and `drec` both annotate `w`). -/
theorem fieldsLevelA_norm (w : Level) : (fs : List FieldA) →
    fieldsLevelA w (fs.map FieldA.norm) = fieldsLevelA w fs
  | [] => rfl
  | .plain _ _ :: fs => by simp only [List.map, FieldA.norm, fieldsLevelA, fieldsLevelA_norm w fs]
  | .drec _ :: fs => by simp only [List.map, FieldA.norm, fieldsLevelA, fieldsLevelA_norm w fs]
  | .frec _ _ _ _ :: fs => by
      simp only [List.map, FieldA.norm, fieldsLevelA, fieldsLevelA_norm w fs]
  | .drecD _ _ :: fs => by simp only [List.map, FieldA.norm, fieldsLevelA, fieldsLevelA_norm w fs]

/-- `eqN` under `imax` (componentwise; `eval`'s `imax` clause respects both). -/
theorem eqNA_imax_local {u u' v v' : Level} (hu : eqN u u') (hv : eqN v v') :
    eqN (.imax u v) (.imax u' v') := by
  intro ρ; simp only [eval]; rw [hu ρ, hv ρ]

/-- R-NoDeltaRec-4d-iii: at every position the raw fields' telescope converts to the normed
    fields'. At `drecD` the raw domain `substA σ D` converts to the normed `drec` domain
    `F canon (pl ++ idx)` — the field's `drecD_typed` evidence transported along the walk's
    substitution by `convA_substA` (the parameter-locals image is `pl` by `substA_walk_paramLocals`,
    the indices by `map`); every other field is identical, `refl`. The `ConvA.pi` right-typing
    slot is `viewTy_fields` on the normed tail (every `FieldA.norm` output is `NoDelta`-free). -/
theorem ctorFieldsA_conv_norm (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadTypedA E I)
    (hIS : IotaSubstA I) {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    {w : Level} {idxBase : ExprA} {fsAll : List FieldA} {Γp0 : LCtxA}
    (hw : fv.sort = w)
    (hdd : ∀ fsPre D idx fsRest,
      fsAll = fsPre ++ FieldA.drecD D idx :: fsRest →
      Nonempty (HasTyA E I n (plainCtxA fsPre Γp0) D (.sort fv.sort)) ∧
      Nonempty (ConvA E I n (plainCtxA fsPre Γp0) D
        (foldAppsA (.const f (canonLevelsA fm.arity))
          ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre 0)) ++ idx))
        (.sort fv.sort))) :
    {Γp Γt : LCtxA} → {σ : SubstA} →
    SubstTyA E I n Γt σ Γp →
    CtxWfA E I n Γp → CtxWfA E I n Γt →
    {k j d : Nat} → {s : Level} → {plP pl : List ExprA} →
    (pl = plP.map (substA σ)) →
    (pl = (paramLocalsA fv.params.length).map (liftA 0 d)) →
    (∀ t, σ (j + t) = .bvar (t + d)) →
    HasTyA E I n Γp (foldAppsA (.const f (canonLevelsA fm.arity)) plP)
      (liftA 0 k idxBase) →
    HasTyA E I n Γp (liftA 0 k idxBase) (.sort s) →
    IsIdxTel (liftA 0 k idxBase) w →
    {fsPre fs : List FieldA} → {res : List ExprA} →
    fsAll = fsPre ++ fs →
    Γp = plainCtxA fsPre Γp0 →
    j = plainIdxA fsPre 0 → d = fsPre.length →
    FieldsTyA E I n (fun k => liftA 0 k idxBase) Γp k fs res →
    Nonempty (ConvA E I n Γt (ctorFieldsA f (canonLevelsA fm.arity) w pl σ fs res).1
      (ctorFieldsA f (canonLevelsA fm.arity) w pl σ (fs.map FieldA.norm) res).1
      (.sort (ctorFieldsA f (canonLevelsA fm.arity) w pl σ fs res).2)) := by
  intro Γp Γt σ hσ hΓp hΓt k j d s plP pl hpl hplN hσge hFp hIdx hTel fsPre fs res
    hsplit hΓpe hj hd hFT
  induction hFT generalizing σ Γt j d s plP pl fsPre with
  | nil Γ₀ k₀ res₀ hres =>
      have hApp := viewTy_foldIdx hE hI hR hIS hΓp hTel hIdx hFp hres
      rw [← foldAppsA_append] at hApp
      have hSub := hasTyA_substA hE hI hR hIS hσ hApp
      rw [substA_sort, substA_foldAppsA, substA_const, List.map_append, ← hpl] at hSub
      exact ⟨.refl _ _ _ (by simpa [ctorFieldsA] using hSub)⟩
  | plain Γ₀ k₀ D u fs' res' hD tl ih =>
      have hDom : HasTyA E I n Γt (substA σ D) (.sort u) := by
        have h := hasTyA_substA hE hI hR hIS hσ hD
        rw [substA_sort] at h; exact h
      let step := viewTy_idxStep hE hI hσ hΓp hΓt hpl hFp hIdx hTel hD hDom
      have hsplit' : fsAll = (fsPre ++ [.plain D u]) ++ fs' := by
        rw [List.append_assoc]; exact hsplit
      have hΓpe' : LocalDeclA.assumption D :: Γ₀ = plainCtxA (fsPre ++ [.plain D u]) Γp0 := by
        rw [plainCtxA_append, ← hΓpe]; rfl
      have hj' : j + 1 = plainIdxA (fsPre ++ [.plain D u]) 0 := by
        rw [plainIdxA_append, ← hj]; rfl
      have hd' : d + 1 = (fsPre ++ ([.plain D u] : List FieldA)).length := by
        rw [hd, List.length_append]; rfl
      have hplN' : pl.map (liftA 0 1) =
          (paramLocalsA fv.params.length).map (liftA 0 (d + 1)) := by
        rw [hplN, List.map_map]
        exact List.map_congr_left fun x _ =>
          liftA_liftA_merge 1 d 0 0 (Nat.le_refl 0) (Nat.zero_le _) x
      have hσge' : ∀ t, σ.up (j + 1 + t) = .bvar (t + (d + 1)) := (substA_walk_ge hσge).1
      have hpl' : pl.map (liftA 0 1) = (plP.map (liftA 0 1)).map (substA σ.up) := step.pl
      obtain ⟨ih'⟩ := ih step.substTy step.ctxP step.ctxT step.pl hplN' hσge'
        step.fp step.idx step.tel hsplit' hΓpe' hj' hd'
      have htyN := viewTy_fields hE hI hR hIS step.substTy step.ctxP step.ctxT step.pl
        step.fp step.idx step.tel tl.norm
        (fun x hx => by
          obtain ⟨y, _, hyx⟩ := List.mem_map.mp hx; exact hyx ▸ y.norm_noDelta)
      have hsnd : (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.up fs' res').2 =
          (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.up
            (fs'.map FieldA.norm) res').2 := by
        rw [ctorFieldsA_snd, ctorFieldsA_snd, fieldsLevelA_norm]
      have hvEq : eqN
          (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.up fs' res').2
          (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.up
            (fs'.map FieldA.norm) res').2 := fun ρ => congrArg (eval ρ) hsnd
      exact ⟨by simpa [ctorFieldsA] using
        (.pi _ _ _ _ _ _ _ _ _ (eqNA_refl u) hvEq (.refl _ _ _ hDom) ih'
          (hasTyA_retype_sort (HasTyA.pi Γt _ u _ _ hDom htyN)
            (eqNA_imax_local (eqNA_refl u) (eqNA_symm hvEq))))⟩
  | drec Γ₀ k₀ idx fs' res' hidx tl ih =>
      have hApp := viewTy_foldIdx hE hI hR hIS hΓp hTel hIdx hFp hidx
      rw [← foldAppsA_append] at hApp
      have hDom0 := hasTyA_substA hE hI hR hIS hσ hApp
      rw [substA_sort, substA_foldAppsA, substA_const, List.map_append, ← hpl] at hDom0
      have hDom : HasTyA E I n Γt
          (foldAppsA (.const f (canonLevelsA fm.arity)) (pl ++ idx.map (substA σ)))
          (.sort w) := hDom0
      have hσ' := substTyA_shift1 hE hI hσ
        (foldAppsA (.const f (canonLevelsA fm.arity)) (pl ++ idx.map (substA σ)))
      have hΓt' := CtxWfA.assumption hΓt hDom
      have hpl' : pl.map (liftA 0 1) = plP.map (substA σ.shift1) := by
        rw [hpl]; exact (viewTy_map_shift1 σ plP).symm
      have hplN' : pl.map (liftA 0 1) =
          (paramLocalsA fv.params.length).map (liftA 0 (d + 1)) := by
        rw [hplN, List.map_map]
        exact List.map_congr_left fun x _ =>
          liftA_liftA_merge 1 d 0 0 (Nat.le_refl 0) (Nat.zero_le _) x
      have hσge' : ∀ t, σ.shift1 (j + t) = .bvar (t + (d + 1)) := (substA_walk_ge hσge).2
      have hsplit' : fsAll = (fsPre ++ [.drec idx]) ++ fs' := by
        rw [List.append_assoc]; exact hsplit
      have hΓpe' : Γ₀ = plainCtxA (fsPre ++ [.drec idx]) Γp0 := by
        rw [plainCtxA_append, ← hΓpe]; rfl
      have hj' : j = plainIdxA (fsPre ++ [.drec idx]) 0 := by
        rw [plainIdxA_append, hj]; rfl
      have hd' : d + 1 = (fsPre ++ ([.drec idx] : List FieldA)).length := by
        rw [hd, List.length_append]; rfl
      obtain ⟨ih'⟩ := ih hσ' hΓp hΓt' hpl' hplN' hσge' hFp hIdx hTel hsplit' hΓpe' hj' hd'
      have htyN := viewTy_fields hE hI hR hIS hσ' hΓp hΓt' hpl' hFp hIdx hTel tl.norm
        (fun x hx => by
          obtain ⟨y, _, hyx⟩ := List.mem_map.mp hx; exact hyx ▸ y.norm_noDelta)
      have hsnd : (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.shift1 fs' res').2 =
          (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.shift1
            (fs'.map FieldA.norm) res').2 := by
        rw [ctorFieldsA_snd, ctorFieldsA_snd, fieldsLevelA_norm]
      have hvEq : eqN
          (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.shift1 fs' res').2
          (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.shift1
            (fs'.map FieldA.norm) res').2 := fun ρ => congrArg (eval ρ) hsnd
      exact ⟨by simpa [ctorFieldsA] using
        (.pi _ _ _ _ _ _ _ _ _ (eqNA_refl w) hvEq (.refl _ _ _ hDom) ih'
          (hasTyA_retype_sort (HasTyA.pi Γt _ w _ _ hDom htyN)
            (eqNA_imax_local (eqNA_refl w) (eqNA_symm hvEq))))⟩
  | frec Γ₀ k₀ B uB Bs idx fs' res' hdom tl _ihd iht =>
      have hDom := viewTy_fields hE hI hR hIS hσ hΓp hΓt hpl hFp hIdx hTel hdom
        (plainA_noDelta _)
      rw [← frecDomA_eq] at hDom
      have hσ' := substTyA_shift1 hE hI hσ
        (frecDomA f (canonLevelsA fm.arity) w pl σ ((B, uB) :: Bs) idx).1
      have hΓt' := CtxWfA.assumption hΓt hDom
      have hpl' : pl.map (liftA 0 1) = plP.map (substA σ.shift1) := by
        rw [hpl]; exact (viewTy_map_shift1 σ plP).symm
      have hplN' : pl.map (liftA 0 1) =
          (paramLocalsA fv.params.length).map (liftA 0 (d + 1)) := by
        rw [hplN, List.map_map]
        exact List.map_congr_left fun x _ =>
          liftA_liftA_merge 1 d 0 0 (Nat.le_refl 0) (Nat.zero_le _) x
      have hσge' : ∀ t, σ.shift1 (j + t) = .bvar (t + (d + 1)) := (substA_walk_ge hσge).2
      have hsplit' : fsAll = (fsPre ++ [.frec B uB Bs idx]) ++ fs' := by
        rw [List.append_assoc]; exact hsplit
      have hΓpe' : Γ₀ = plainCtxA (fsPre ++ [.frec B uB Bs idx]) Γp0 := by
        rw [plainCtxA_append, ← hΓpe]; rfl
      have hj' : j = plainIdxA (fsPre ++ [.frec B uB Bs idx]) 0 := by
        rw [plainIdxA_append, hj]; rfl
      have hd' : d + 1 = (fsPre ++ ([.frec B uB Bs idx] : List FieldA)).length := by
        rw [hd, List.length_append]; rfl
      obtain ⟨ih'⟩ := iht hσ' hΓp hΓt' hpl' hplN' hσge' hFp hIdx hTel hsplit' hΓpe' hj' hd'
      have htyN := viewTy_fields hE hI hR hIS hσ' hΓp hΓt' hpl' hFp hIdx hTel tl.norm
        (fun x hx => by
          obtain ⟨y, _, hyx⟩ := List.mem_map.mp hx; exact hyx ▸ y.norm_noDelta)
      have hsnd : (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.shift1 fs' res').2 =
          (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.shift1
            (fs'.map FieldA.norm) res').2 := by
        rw [ctorFieldsA_snd, ctorFieldsA_snd, fieldsLevelA_norm]
      have hvEq : eqN
          (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.shift1 fs' res').2
          (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.shift1
            (fs'.map FieldA.norm) res').2 := fun ρ => congrArg (eval ρ) hsnd
      exact ⟨by simpa [ctorFieldsA] using
        (.pi _ _ _ _ _ _ _ _ _ (eqNA_refl _) hvEq (.refl _ _ _ hDom) ih'
          (hasTyA_retype_sort (HasTyA.pi Γt _ _ _ _ hDom htyN)
            (eqNA_imax_local (eqNA_refl _) (eqNA_symm hvEq))))⟩
  | drecD Γ₀ k₀ D idx fs' res' hidx tl ih =>
      obtain ⟨⟨hDT⟩, ⟨hCT⟩⟩ := hdd fsPre D idx fs' (by simpa [List.append_assoc] using hsplit)
      have hσp : SubstTyA E I n Γt σ (plainCtxA fsPre Γp0) := hΓpe ▸ hσ
      have hC : ConvA E I n Γt (substA σ D)
          (foldAppsA (.const f (canonLevelsA fm.arity)) (pl ++ idx.map (substA σ)))
          (.sort w) := by
        have hc := convA_substA hE hI hR hIS hσp hCT
        rw [substA_sort, substA_foldAppsA, substA_const, List.map_append] at hc
        rw [← hj, substA_walk_paramLocals hσge] at hc
        rw [← hplN] at hc
        exact hw ▸ hc
      have hDom : HasTyA E I n Γt (substA σ D) (.sort w) := by
        have h := hasTyA_substA hE hI hR hIS hσp hDT
        rw [substA_sort] at h; exact hw ▸ h
      have hApp := viewTy_foldIdx hE hI hR hIS hΓp hTel hIdx hFp hidx
      rw [← foldAppsA_append] at hApp
      have hDomN0 := hasTyA_substA hE hI hR hIS hσ hApp
      rw [substA_sort, substA_foldAppsA, substA_const, List.map_append, ← hpl] at hDomN0
      have hDomN : HasTyA E I n Γt
          (foldAppsA (.const f (canonLevelsA fm.arity)) (pl ++ idx.map (substA σ)))
          (.sort w) := hDomN0
      have hσR' := substTyA_shift1 hE hI hσ (substA σ D)
      have hσN' := substTyA_shift1 hE hI hσ
        (foldAppsA (.const f (canonLevelsA fm.arity)) (pl ++ idx.map (substA σ)))
      have hΓtR' := CtxWfA.assumption hΓt hDom
      have hΓtN' := CtxWfA.assumption hΓt hDomN
      have hpl' : pl.map (liftA 0 1) = plP.map (substA σ.shift1) := by
        rw [hpl]; exact (viewTy_map_shift1 σ plP).symm
      have hplN' : pl.map (liftA 0 1) =
          (paramLocalsA fv.params.length).map (liftA 0 (d + 1)) := by
        rw [hplN, List.map_map]
        exact List.map_congr_left fun x _ =>
          liftA_liftA_merge 1 d 0 0 (Nat.le_refl 0) (Nat.zero_le _) x
      have hσge' : ∀ t, σ.shift1 (j + t) = .bvar (t + (d + 1)) := (substA_walk_ge hσge).2
      have hsplit' : fsAll = (fsPre ++ [.drecD D idx]) ++ fs' := by
        rw [List.append_assoc]; exact hsplit
      have hΓpe' : Γ₀ = plainCtxA (fsPre ++ [.drecD D idx]) Γp0 := by
        rw [plainCtxA_append, ← hΓpe]; rfl
      have hj' : j = plainIdxA (fsPre ++ [.drecD D idx]) 0 := by
        rw [plainIdxA_append, hj]; rfl
      have hd' : d + 1 = (fsPre ++ ([.drecD D idx] : List FieldA)).length := by
        rw [hd, List.length_append]; rfl
      obtain ⟨ih'⟩ := ih hσR' hΓp hΓtR' hpl' hplN' hσge' hFp hIdx hTel hsplit' hΓpe' hj' hd'
      have htyN := viewTy_fields hE hI hR hIS hσN' hΓp hΓtN' hpl' hFp hIdx hTel tl.norm
        (fun x hx => by
          obtain ⟨y, _, hyx⟩ := List.mem_map.mp hx; exact hyx ▸ y.norm_noDelta)
      have hsnd : (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.shift1 fs' res').2 =
          (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.shift1
            (fs'.map FieldA.norm) res').2 := by
        rw [ctorFieldsA_snd, ctorFieldsA_snd, fieldsLevelA_norm]
      have hvEq : eqN
          (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.shift1 fs' res').2
          (ctorFieldsA f (canonLevelsA fm.arity) w (pl.map (liftA 0 1)) σ.shift1
            (fs'.map FieldA.norm) res').2 := fun ρ => congrArg (eval ρ) hsnd
      exact ⟨by simpa [ctorFieldsA] using
        (.pi _ _ _ _ _ _ _ _ _ (eqNA_refl w) hvEq hC ih'
          (hasTyA_retype_sort (HasTyA.pi Γt _ w _ _ hDomN htyN)
            (eqNA_imax_local (eqNA_refl w) (eqNA_symm hvEq))))⟩

/-- `ctorFieldsA_conv_norm` at the constructor's entry: the stored field telescope converts to
    the normed one in the parameter context. -/
theorem ctorFieldsA_conv_norm_entry (hE : EnvClosedA E) (hI : IotaLiftA I)
    (hR : IotaRecHeadTypedA E I) (hIS : IotaSubstA I)
    {f : Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    {w : Level} {idxBase : ExprA} {fields : List FieldA} {res : List ExprA}
    {Γp : LCtxA} (hΓp : CtxWfA E I n Γp)
    (hdd : ∀ fsPre D idx fsRest,
      fields = fsPre ++ FieldA.drecD D idx :: fsRest →
      Nonempty (HasTyA E I n (plainCtxA fsPre Γp) D (.sort fv.sort)) ∧
      Nonempty (ConvA E I n (plainCtxA fsPre Γp) D
        (foldAppsA (.const f (canonLevelsA fm.arity))
          ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre 0)) ++ idx))
        (.sort fv.sort)))
    (hw : fv.sort = w)
    (hFp : HasTyA E I n Γp
      (foldAppsA (.const f (canonLevelsA fm.arity)) (paramLocalsA fv.params.length))
      (liftA 0 0 idxBase))
    (hIdx : HasTyA E I n Γp idxBase (.sort fv.sort)) (hTel : IsIdxTel idxBase w)
    (hFT : FieldsTyA E I n (fun k => liftA 0 k idxBase) Γp 0 fields res) :
    Nonempty (ConvA E I n Γp
      (ctorFieldsA f (canonLevelsA fm.arity) w (paramLocalsA fv.params.length) SubstA.id
        fields res).1
      (ctorFieldsA f (canonLevelsA fm.arity) w (paramLocalsA fv.params.length) SubstA.id
        (fields.map FieldA.norm) res).1
      (.sort (ctorFieldsA f (canonLevelsA fm.arity) w (paramLocalsA fv.params.length) SubstA.id
        fields res).2)) :=
  have hσid : SubstTyA E I n Γp SubstA.id Γp := substTyA_id hE hI hΓp
  have hplid : (paramLocalsA fv.params.length).map (substA SubstA.id)
      = paramLocalsA fv.params.length :=
    (List.map_congr_left fun x _ => substA_id x).trans (List.map_id _)
  have hplz : (paramLocalsA fv.params.length).map (liftA 0 0)
      = paramLocalsA fv.params.length :=
    (List.map_congr_left fun x _ => liftA_zero 0 x).trans (List.map_id _)
  ctorFieldsA_conv_norm hE hI hR hIS hw hdd hσid hΓp hΓp (k := 0) (j := 0) (d := 0)
    hplid.symm hplz.symm substA_walk_ge_id hFp (by simpa [liftA_zero] using hIdx)
    (by simpa [liftA_zero] using hTel) (List.nil_append _).symm rfl rfl rfl hFT

inductive DomTyA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    LCtxA → List (ExprA × Level) → Type
  | nil (Γ : LCtxA) : DomTyA E I n Γ []
  | cons (Γ : LCtxA) (D : ExprA) (u : Level) (ds : List (ExprA × Level))
      (hD : HasTyA E I n Γ D (.sort u))
      (tl : DomTyA E I n (.assumption D :: Γ) ds) :
      DomTyA E I n Γ ((D, u) :: ds)

def viewTy_pi : {Γ : LCtxA} → {ds : List (ExprA × Level)} → DomTyA E I n Γ ds →
    {B : ExprA} → {w : Level} → HasTyA E I n (telCtxA ds ++ Γ) B (.sort w) →
    HasTyA E I n Γ (piTelA ds B w).1 (.sort (piTelA ds B w).2)
  | _, _, .nil _, _, _, hB => hB
  | _, _, .cons Γ D u ds hD tl, B, w, hB =>
      .pi Γ D u (piTelA ds B w).1 (piTelA ds B w).2 hD
        (viewTy_pi tl ((telCtxA_cons_append (D, u) ds Γ) ▸ hB))

/-- a telescope that ends in `Sort w`, annotated `.succ w`, peeled into its domains.
    The outer sort of the derivation is not the annotation (`conv` can sit on it);
    each binder is recovered by `hasTyA_pi_parts`, and the body by the sort rule. -/
def viewTy_domOfSort {w : Level} : {ds : List (ExprA × Level)} → {Γ : LCtxA} → {T : ExprA} →
    HasTyA E I n Γ (piTelA ds (.sort w) (.succ w)).1 T → CtxWfA E I n Γ →
    Σ' (_ : DomTyA E I n Γ ds) (_ : CtxWfA E I n (telCtxA ds ++ Γ)),
      HasTyA E I n (telCtxA ds ++ Γ) (.sort w) (.sort (.succ w))
  | [], _, _, _, hΓ => ⟨.nil _, hΓ, .sort _ w⟩
  | (D, u) :: ds, _, _, h, hΓ =>
      let parts := hasTyA_pi_parts h
      let ih := viewTy_domOfSort parts.2 (.assumption hΓ parts.1)
      ⟨.cons _ D u ds parts.1 ih.1,
        (telCtxA_cons_append (D, u) ds _).symm ▸ ih.2.1,
        (telCtxA_cons_append (D, u) ds _).symm ▸ ih.2.2⟩

def viewTy_dom_split : {Γ : LCtxA} → {xs ys : List (ExprA × Level)} →
    DomTyA E I n Γ (xs ++ ys) →
    DomTyA E I n Γ xs × DomTyA E I n (telCtxA xs ++ Γ) ys
  | _, [], _, h => ⟨.nil _, h⟩
  | _, (D, u) :: xs, ys, .cons _ _ _ _ hD tl =>
      let ih := viewTy_dom_split tl
      ⟨.cons _ D u xs hD ih.1, (telCtxA_cons_append (D, u) xs _).symm ▸ ih.2⟩

def viewTy_ctxOfDom : {Γ : LCtxA} → {ds : List (ExprA × Level)} →
    DomTyA E I n Γ ds → CtxWfA E I n Γ → CtxWfA E I n (telCtxA ds ++ Γ)
  | _, _, .nil _, hΓ => hΓ
  | _, _, .cons _ D u ds hD tl, hΓ =>
      (telCtxA_cons_append (D, u) ds _).symm ▸
        viewTy_ctxOfDom tl (.assumption hΓ hD)

def viewTy_wkBy (hE : EnvClosedA E) (hI : IotaLiftA I) :
    (Δ : LCtxA) → {Γ : LCtxA} → {e A : ExprA} → HasTyA E I n Γ e A →
      HasTyA E I n (Δ ++ Γ) (liftA 0 Δ.length e) (liftA 0 Δ.length A)
  | [], _, _, _, h => by
      simpa [List.nil_append, List.length_nil, liftA_zero] using h
  | d :: Δ, _, _, _, h => by
      have ih := viewTy_wkBy hE hI Δ h
      have hw := hasTyWeakenA hE hI d (c := 0) (Nat.zero_le _) ih
      simp only [insertAtA, List.cons_append, List.length_cons] at hw ⊢
      rw [liftA_liftA_merge 1 Δ.length 0 0 (Nat.le_refl _) (Nat.zero_le _),
        liftA_liftA_merge 1 Δ.length 0 0 (Nat.le_refl _) (Nat.zero_le _)] at hw
      exact hw

theorem viewTy_double_apply {f : ExprA} (hf : ∀ a, liftA 0 a f = f) (np ni : Nat) :
    foldAppsA (liftA 0 ni (foldAppsA f (paramLocalsA np))) (paramLocalsA ni) =
      foldAppsA f ((paramLocalsA np).map (liftA 0 ni) ++ paramLocalsA ni) := by
  rw [liftA_foldAppsA, hf, foldAppsA_append]

structure ViewTyOpenA (f : Nat) (fm : CheckedMemberA) (fv : FamViewA fm) (wM : Level) : Type where
  domP : DomTyA E I n [] fv.params
  domI : DomTyA E I n (telCtxA fv.params) fv.indices
  ctxP : CtxWfA E I n (telCtxA fv.params)
  ctxI : CtxWfA E I n (telCtxA fv.indices ++ telCtxA fv.params)
  idxTy : HasTyA E I n (telCtxA fv.params) fv.idxTelA
    (.sort (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2)
  atSort : HasTyA E I n (telCtxA fv.indices ++ telCtxA fv.params) (.sort fv.sort)
    (.sort (.succ fv.sort))
  atParams : HasTyA E I n (telCtxA fv.params)
    (foldAppsA (.const f (canonLevelsA fm.arity)) (paramLocalsA fv.params.length)) fv.idxTelA
  here : HasTyA E I n (telCtxA fv.indices ++ telCtxA fv.params)
    (famLocalsA f (canonLevelsA fm.arity) fv.params.length fv.indices.length) (.sort fv.sort)
  mot : HasTyA E I n (telCtxA fv.params)
    (motTyA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort wM).1
    (.sort (motTyA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort wM).2)

def viewTy_openFam (hE : EnvClosedA E) (hI : IotaLiftA I) {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} {u : Level} (hFam : HasTyA E I n [] fm.mtypeA (.sort u))
    (hmem : E.members f = some fm) (hn : fm.arity ≤ n) (wM : Level) :
    ViewTyOpenA (E := E) (I := I) (n := n) f fm fv wM := by
  have hStored : HasTyA E I n []
      (piTelA (fv.params ++ fv.indices) (.sort fv.sort) (.succ fv.sort)).1 (.sort u) :=
    fv.stored ▸ hFam
  have opened := viewTy_domOfSort hStored CtxWfA.nil
  have split := viewTy_dom_split opened.1
  have hnilP : telCtxA fv.params ++ [] = telCtxA fv.params := List.append_nil _
  have domP : DomTyA E I n [] fv.params := split.1
  have domI : DomTyA E I n (telCtxA fv.params) fv.indices := hnilP ▸ split.2
  have hctxAll : telCtxA (fv.params ++ fv.indices) ++ [] =
      telCtxA fv.indices ++ telCtxA fv.params := by
    rw [telCtxA_append, List.append_nil]
  have atSort := hctxAll ▸ opened.2.2
  have ctxI : CtxWfA E I n (telCtxA fv.indices ++ telCtxA fv.params) :=
    hctxAll ▸ opened.2.1
  have ctxP0 := viewTy_ctxOfDom domP CtxWfA.nil
  have ctxP : CtxWfA E I n (telCtxA fv.params) := hnilP ▸ ctxP0
  have idxTy := viewTy_pi domI atSort
  have hFamPi : HasTyA E I n []
      (piTelA fv.params fv.idxTelA (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2).1
      (.sort u) := by
    simpa [FamViewA.idxTelA, piTelA_append] using hStored
  have hConst0 := viewTy_famConst hn hmem hFam
  have hConst : HasTyA E I n [] (.const f (canonLevelsA fm.arity))
      (piTelA fv.params fv.idxTelA (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2).1 := by
    have h := fv.stored ▸ hConst0
    simpa [FamViewA.idxTelA, piTelA_append] using h
  have hAt0 := viewTy_applyParams hE hI (Γ := []) CtxWfA.nil hFamPi hConst
  have atParams0 : HasTyA E I n (telCtxA fv.params ++ [])
      (foldAppsA (.const f (canonLevelsA fm.arity)) (paramLocalsA fv.params.length))
      fv.idxTelA := by
    simpa [FamViewA.idxTelA, liftA] using hAt0
  have atParams := hnilP ▸ atParams0
  have hIdxPi : HasTyA E I n (telCtxA fv.params)
      (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).1
      (.sort (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2) := idxTy
  have hHere0 := viewTy_applyParams hE hI ctxP hIdxPi atParams
  have hHere1 : HasTyA E I n (telCtxA fv.indices ++ telCtxA fv.params)
      (foldAppsA (liftA 0 fv.indices.length
        (foldAppsA (.const f (canonLevelsA fm.arity)) (paramLocalsA fv.params.length)))
        (paramLocalsA fv.indices.length)) (.sort fv.sort) := by
    simpa [piTelA] using hHere0
  have here := viewTy_double_apply (f := .const f (canonLevelsA fm.arity))
      (fun _ => rfl) fv.params.length fv.indices.length ▸ hHere1
  have hPiMot : HasTyA E I n (telCtxA fv.indices ++ telCtxA fv.params)
      (.pi (famLocalsA f (canonLevelsA fm.arity) fv.params.length fv.indices.length) fv.sort
        (.sort wM) (.succ wM))
      (.sort (.imax fv.sort (.succ wM))) :=
    .pi _ _ _ _ _ here (.sort _ wM)
  have mot := viewTy_pi domI hPiMot
  exact {
    domP, domI, ctxP, ctxI,
    idxTy := by simpa [FamViewA.idxTelA] using idxTy,
    atSort, atParams,
    here := by simpa [famLocalsA] using here,
    mot := mot }


theorem viewTy_map_lift_add (a b : Nat) :
    (xs : List ExprA) → (xs.map (liftA 0 a)).map (liftA 0 b) = xs.map (liftA 0 (a + b))
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, viewTy_map_lift_add a b xs]
      exact congrArg (fun z => z :: xs.map (liftA 0 (a + b)))
        (liftA_liftA_merge b a 0 0 (Nat.le_refl _) (Nat.zero_le _) x)

end ViewTyFields

section ViewTyEnvMove
variable {E₀ E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

def viewTy_ctx_env (hpre : PrefixA E₀ E) : {Γ : LCtxA} → CtxWfA E₀ I n Γ → CtxWfA E I n Γ
  | _, .nil => .nil
  | _, .assumption hΓ hA => .assumption (viewTy_ctx_env hpre hΓ) (hasTyEnvA hpre hA)
  | _, .letBinding hΓ hA hv =>
      .letBinding (viewTy_ctx_env hpre hΓ) (hasTyEnvA hpre hA) (hasTyEnvA hpre hv)

def viewTy_subst_env (hpre : PrefixA E₀ E) {Δ Γ : LCtxA} {σ : SubstA}
    (hσ : SubstTyA E₀ I n Δ σ Γ) : SubstTyA E I n Δ σ Γ where
  ty := fun i A h => hasTyEnvA hpre (hσ.ty i A h)
  val := fun i A v hty hval => convEnvA hpre (hσ.val i A v hty hval)

def viewTy_dom_env (hpre : PrefixA E₀ E) : {Γ : LCtxA} → {ds : List (ExprA × Level)} →
    DomTyA E₀ I n Γ ds → DomTyA E I n Γ ds
  | _, _, .nil Γ => .nil Γ
  | _, _, .cons Γ D u ds hD tl =>
      .cons Γ D u ds (hasTyEnvA hpre hD) (viewTy_dom_env hpre tl)

def viewTy_args_env (hpre : PrefixA E₀ E) : {Γ : LCtxA} → {T : ExprA} → {as : List ExprA} →
    ArgsTyA E₀ I n Γ T as → ArgsTyA E I n Γ T as
  | _, _, _, .nil l => .nil l
  | _, _, _, .cons A u B v a as ha tl =>
      .cons A u B v a as (hasTyEnvA hpre ha) (viewTy_args_env hpre tl)

def viewTy_fields_env (hpre : PrefixA E₀ E) {idxTel : Nat → ExprA} :
    {Γ : LCtxA} → {k : Nat} → {fs : List FieldA} → {res : List ExprA} →
    FieldsTyA E₀ I n idxTel Γ k fs res → FieldsTyA E I n idxTel Γ k fs res
  | _, _, _, _, .nil Γ k res h => .nil Γ k res (viewTy_args_env hpre h)
  | _, _, _, _, .plain Γ k D u fs res hD tl =>
      .plain Γ k D u fs res (hasTyEnvA hpre hD) (viewTy_fields_env hpre tl)
  | _, _, _, _, .drec Γ k idx fs res hidx tl =>
      .drec Γ k idx fs res (viewTy_args_env hpre hidx) (viewTy_fields_env hpre tl)
  | _, _, _, _, .frec Γ k B uB Bs idx fs res hdom tl =>
      .frec Γ k B uB Bs idx fs res (viewTy_fields_env hpre hdom) (viewTy_fields_env hpre tl)
  | _, _, _, _, .drecD Γ k D idx fs res hidx tl =>
      .drecD Γ k D idx fs res (viewTy_args_env hpre hidx) (viewTy_fields_env hpre tl)

end ViewTyEnvMove

/-! ## (0b) the function-recursive field's whole domain (R-NoFunRec-1 step 1 (1c-ε2d), N1)

The base domain `frecDomA … SubstA.id` over the parameter locals, in the plain context past a prefix, is
typed in the group environment (`frecDomTyG`: `viewTy_fields` over the carried facts, `frecOpenA`); its
instance at the walk's substitution is the walk's reached domain (`frecDomA_instance`). -/

section FrecDomG
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/- (`plainIdxA_add` landed upstream in `RcicAnnGroup` — same statement, same proof shape.) -/

theorem map_liftA_zero : (xs : List ExprA) → xs.map (liftA 0 0) = xs
  | [] => rfl
  | x :: xs => by simp only [List.map, liftA_zero, map_liftA_zero xs]

/-- the facts `viewTy_fields` reads at a field list's plain context, carried from the parameter context
    past the plain fields of a prefix (R-NoFunRec-1 step 1 (1c-ε2d)). -/
structure PlainOpenA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (f : Nat) (ls : List Level) (w : Level)
    (idxBase : ExprA) (s : Level) (Γp : LCtxA) (k : Nat) (plP : List ExprA) (fsPre : List FieldA) : Type where
  ctx : CtxWfA E I n (plainCtxA fsPre Γp)
  fp : HasTyA E I n (plainCtxA fsPre Γp)
    (foldAppsA (.const f ls) (plP.map (liftA 0 (plainIdxA fsPre 0)))) (liftA 0 (plainIdxA fsPre k) idxBase)
  idx : HasTyA E I n (plainCtxA fsPre Γp) (liftA 0 (plainIdxA fsPre k) idxBase) (.sort s)
  tel : IsIdxTel (liftA 0 (plainIdxA fsPre k) idxBase) w

def frecOpenA (hE : EnvClosedA E) (hI : IotaLiftA I) {f : Nat} {ls : List Level} {w : Level}
    {idxBase : ExprA} {s : Level} :
    (fsPre : List FieldA) → {fsRest : List FieldA} → {res : List ExprA} → {Γp : LCtxA} → {k : Nat} →
    {plP : List ExprA} → CtxWfA E I n Γp →
    HasTyA E I n Γp (foldAppsA (.const f ls) plP) (liftA 0 k idxBase) →
    HasTyA E I n Γp (liftA 0 k idxBase) (.sort s) → IsIdxTel (liftA 0 k idxBase) w →
    FieldsTyA E I n (fun k => liftA 0 k idxBase) Γp k (fsPre ++ fsRest) res →
    PlainOpenA E I n f ls w idxBase s Γp k plP fsPre
  | [], _, _, _, k, plP, hΓ, hFp, hIdx, hTel, _ => by
      have hm : plP.map (liftA 0 0) = plP := map_liftA_zero plP
      refine ⟨hΓ, ?_, ?_, ?_⟩
      · show HasTyA E I n _ (foldAppsA (.const f ls) (plP.map (liftA 0 0))) (liftA 0 k idxBase)
        rw [hm]; exact hFp
      · exact hIdx
      · exact hTel
  | .plain D u :: fsPre, _, _, Γp, k, plP, hΓ, hFp, hIdx, hTel, .plain _ _ _ _ _ _ hD tl => by
      have hDom : HasTyA E I n Γp (substA SubstA.id D) (.sort u) := by rw [substA_id]; exact hD
      have step := viewTy_idxStep hE hI (σ := SubstA.id) (substTyA_id hE hI hΓ) hΓ hΓ
        (map_substA_id plP).symm hFp hIdx hTel hD hDom
      have ih := frecOpenA hE hI fsPre step.ctxP step.fp step.idx step.tel tl
      have e1 : plainIdxA fsPre 1 = 1 + plainIdxA fsPre 0 := plainIdxA_add fsPre 1
      refine ⟨ih.ctx, ?_, ih.idx, ih.tel⟩
      have h := ih.fp
      rw [viewTy_map_lift_add 1 (plainIdxA fsPre 0) plP] at h
      show HasTyA E I n _ (foldAppsA (.const f ls) (plP.map (liftA 0 (plainIdxA fsPre 1))))
        (liftA 0 (plainIdxA fsPre (k + 1)) idxBase)
      rw [e1]; exact h
  | .drec _ :: fsPre, _, _, Γp, k, plP, hΓ, hFp, hIdx, hTel, .drec _ _ _ _ _ _ tl => by
      have ih := frecOpenA hE hI fsPre hΓ hFp hIdx hTel tl
      exact ⟨ih.ctx, ih.fp, ih.idx, ih.tel⟩
  | .frec _ _ _ _ :: fsPre, _, _, Γp, k, plP, hΓ, hFp, hIdx, hTel, .frec _ _ _ _ _ _ _ _ _ tl => by
      have ih := frecOpenA hE hI fsPre hΓ hFp hIdx hTel tl
      exact ⟨ih.ctx, ih.fp, ih.idx, ih.tel⟩
  | .drecD _ _ :: fsPre, _, _, Γp, k, plP, hΓ, hFp, hIdx, hTel, .drecD _ _ _ _ _ _ _ tl => by
      have ih := frecOpenA hE hI fsPre hΓ hFp hIdx hTel tl
      exact ⟨ih.ctx, ih.fp, ih.idx, ih.tel⟩


def frecDomTyG {E₀ G : ResolvedEnvA} {I : IotaIfaceA} (hG : EnvClosedA G) (hI : IotaLiftA I)
    (hR : IotaRecHeadTypedA G I) (hIS : IotaSubstA I) (hpre : PrefixA E₀ G) {f : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} {u : Level}
    (hFam : HasTyA G I fm.arity [] fm.mtypeA (.sort u)) (hmem : G.members f = some fm)
    (fsPre : List FieldA) {B : ExprA} {uB : Level} {Bs : List (ExprA × Level)} {idx : List ExprA}
    {fsRest : List FieldA} {res : List ExprA}
    (hty : FieldsTyA E₀ I fm.arity (fun k => liftA 0 k fv.idxTelA) (telCtxA fv.params) 0
      (fsPre ++ FieldA.frec B uB Bs idx :: fsRest) res) :
    HasTyA G I fm.arity (plainCtxA fsPre (telCtxA fv.params))
      (frecDomA f (canonLevelsA fm.arity) fv.sort
        ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre 0))) SubstA.id ((B, uB) :: Bs) idx).1
      (.sort (frecDomA f (canonLevelsA fm.arity) fv.sort
        ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre 0))) SubstA.id ((B, uB) :: Bs) idx).2) := by
  have hop := viewTy_openFam (fv := fv) hG hI hFam hmem (Nat.le_refl _) fv.sort
  have hty' := viewTy_fields_env hpre hty
  have hFp := (liftA_zero 0 fv.idxTelA).symm ▸ hop.atParams
  have hIdx := (liftA_zero 0 fv.idxTelA).symm ▸ hop.idxTy
  have hTel : IsIdxTel (liftA 0 0 fv.idxTelA) fv.sort :=
    (liftA_zero 0 fv.idxTelA).symm ▸ isIdxTel_piTel fv.sort (.succ fv.sort) fv.indices
  have op := frecOpenA hG hI fsPre hop.ctxP hFp hIdx hTel hty'
  have hdrop := FieldsTyA.drop fsPre hty'
  cases hdrop with
  | frec _ _ _ _ _ _ _ _ hdom _ =>
      have h := viewTy_fields hG hI hR hIS (substTyA_id hG hI op.ctx) op.ctx op.ctx
        (map_substA_id _).symm op.fp op.idx op.tel hdom (plainA_noDelta _)
      rw [← frecDomA_eq] at h
      exact h

end FrecDomG

theorem leN_frecLevelA {w : Level} : (ds : List (ExprA × Level)) → (∀ d ∈ ds, leN d.2 w) →
    leN (frecLevelA w ds) w
  | [], _ => fun ρ x y hx hy => by
      simp only [frecLevelA] at hx
      rw [hx] at hy; cases hy; exact Nat.le_refl _
  | (_, u) :: ds, h => fun ρ x y hx hy => by
      have ih := leN_frecLevelA ds (fun d hd => h d (List.mem_cons_of_mem _ hd))
      have hu := h (_, u) (List.mem_cons_self _ _)
      simp only [frecLevelA, eval] at hx
      cases hr : eval ρ (frecLevelA w ds) with
      | none => rw [hr] at hx; simp at hx
      | some r =>
          have hry : r ≤ y := ih ρ r y hr hy
          rw [hr] at hx
          have hx' : (if r = 0 then some 0 else Option.map (fun x => max x r) (eval ρ u)) = some x := hx
          by_cases h0 : r = 0
          · rw [if_pos h0] at hx'; cases hx'; exact Nat.zero_le _
          · rw [if_neg h0] at hx'
            cases hu' : eval ρ u with
            | none => rw [hu'] at hx'; simp at hx'
            | some xu =>
                rw [hu'] at hx'
                cases hx'
                exact Nat.max_le.mpr ⟨hu ρ xu y hu' hy, hry⟩


theorem frecSort_ht_le {ρ₀ : Nat → Nat} {fm : CheckedMemberA} {fv : FamViewA fm}
    (hUT : UniformType fv.sort) {ds : List (ExprA × Level)}
    (h : ∀ d ∈ ds, UniformProp fv.sort ∨ (UniformType fv.sort ∧ leN d.2 fv.sort))
    {ls lsC : List Level} (hlsC : eqNList ls lsC) :
    ht ρ₀ (instLevel lsC (frecLevelA fv.sort ds)) ≤ ht ρ₀ (instLevel ls fv.sort) := by
  have hle : leN (frecLevelA fv.sort ds) fv.sort :=
    leN_frecLevelA ds fun d hd => by
      rcases h d hd with hP | ⟨_, hle⟩
      · have h1 := hUT (fun _ => 0)
        rw [hP (fun _ => 0)] at h1
        exact absurd h1 (Nat.lt_irrefl 0)
      · exact hle
  rw [ht_of_eqN (instLevel_eqNList hlsC fv.sort)]
  exact ht_le_of_leN (leN_instLevel hle lsC)

theorem frecDomA_instance (f : Nat) (lsC : List Level) (w : Level) (idx : List ExprA)
    (ds : List (ExprA × Level)) (xs ps : List ExprA) :
    substA (consListA xs (consListA ps SubstA.id))
      (instantiateLevelsA lsC (frecDomA f (canonLevelsA lsC.length) w
        ((paramLocalsA ps.length).map (liftA 0 xs.length)) SubstA.id ds idx).1) =
    (frecDomA f lsC (instLevel lsC w) ps (consListA xs (consListA ps SubstA.id)) (instDomsA lsC ds)
      (idx.map (instantiateLevelsA lsC))).1 := by
  rw [instantiateLevelsA_frecDomA, substA_frecDomA, canonLevelsA_instLevel]
  have e1 : ((paramLocalsA ps.length).map (liftA 0 xs.length)).map (instantiateLevelsA lsC) =
      (paramLocalsA ps.length).map (liftA 0 xs.length) := by
    rw [List.map_map]
    have h : (instantiateLevelsA lsC ∘ liftA 0 xs.length) = (liftA 0 xs.length ∘ instantiateLevelsA lsC) :=
      funext fun e => instantiateLevelsA_liftA lsC 0 xs.length e
    rw [h, ← List.map_map, map_instantiateLevelsA_paramLocalsA]
  have e2 : ((paramLocalsA ps.length).map (liftA 0 xs.length)).map
      (substA (consListA xs (consListA ps SubstA.id))) = ps := by
    rw [List.map_map]
    have h : (substA (consListA xs (consListA ps SubstA.id)) ∘ liftA 0 xs.length) =
        substA (consListA ps SubstA.id) :=
      funext fun e => substA_consListA_liftA xs _ e
    rw [h]
    exact paramLocalsA_consListA ps SubstA.id
  have e3 : (fun i => substA (consListA xs (consListA ps SubstA.id)) (instantiateLevelsA lsC (SubstA.id i))) =
      consListA xs (consListA ps SubstA.id) := funext fun i => rfl
  rw [e1, e2, e3]

/-! ## (1) the experiment (1c-ε2d-a0): the declared domains' conversion, from syntactic evidence only -/

section FrecDomSyn
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat}

/-- a context of assumptions only. -/
def AssumpOnlyA (Γ : LCtxA) : Prop := ∀ d ∈ Γ, ∃ A, d = LocalDeclA.assumption A

theorem assumpOnlyA_telCtxA (ds : List (ExprA × Level)) : AssumpOnlyA (telCtxA ds) := by
  intro d hd
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hd)
  exact ⟨x.1, rfl⟩

theorem assumpOnlyA_plainCtxA : (fs : List FieldA) → (Γ : LCtxA) → AssumpOnlyA Γ → AssumpOnlyA (plainCtxA fs Γ)
  | [], _, h => h
  | .plain D _ :: fs, Γ, h =>
      assumpOnlyA_plainCtxA fs _ fun d hd => by
        rcases List.mem_cons.mp hd with rfl | hd
        · exact ⟨D, rfl⟩
        · exact h d hd
  | .drec _ :: fs, Γ, h => assumpOnlyA_plainCtxA fs Γ h
  | .frec _ _ _ _ :: fs, Γ, h => assumpOnlyA_plainCtxA fs Γ h
  | .drecD _ _ :: fs, Γ, h => assumpOnlyA_plainCtxA fs Γ h

theorem assumpOnlyA_instCtxA (ls : List Level) {Γ : LCtxA} (h : AssumpOnlyA Γ) :
    AssumpOnlyA (instCtxA ls Γ) := by
  intro d hd
  obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.mp hd
  obtain ⟨A, rfl⟩ := h d₀ hd₀
  exact ⟨instantiateLevelsA ls A, rfl⟩

/-- a convertible pair of images for an assumption's variable, over a convertible pair of tails. -/
def convSubstA_cons_gen {Δ Γ : LCtxA} {σ σ' : SubstA} {t t' A : ExprA}
    (h : ConvSubstA E I n Δ σ σ' Γ) (ht : HasTyA E I n Δ t (substA σ A))
    (ht' : HasTyA E I n Δ t' (substA σ' A)) (hc : ConvA E I n Δ t t' (substA σ A)) :
    ConvSubstA E I n Δ (SubstA.cons t σ) (SubstA.cons t' σ') (.assumption A :: Γ) where
  left := substTyA_cons h.left ht
  right := substTyA_cons h.right ht'
  conv := fun i B hlu => by
    cases i with
    | zero =>
        have hB : B = liftA 0 1 A := lookupTypeA_zero_assumption_eq hlu
        subst hB
        rw [SubstA.cons_zero, SubstA.cons_zero, substA_cons_liftA]
        exact hc
    | succ i =>
        let s := liftedTypeA (.assumption A) Γ hlu
        have hEq : B = liftA 0 1 s.orig := s.eq_lift
        rw [hEq, SubstA.cons_succ, SubstA.cons_succ, substA_cons_liftA]
        exact h.conv i s.orig s.got

/-- THE WALK'S VALID PAIR IS A CONVERTIBLE SUBSTITUTION PAIR, on a context of assumptions: each variable's
    pair is typed and convertible at the left's substituted type, the right's typing moved across the
    domains' type conversion. -/
theorem convSubstA_of_validSubstA : (Γ : LCtxA) → AssumpOnlyA Γ → {k : Nat} → {Δ : LCtxA} →
    {σ σ' : SubstA} → ValidSubstA E I n ρ₀ k Δ σ σ' Γ → Nonempty (ConvSubstA E I n Δ σ σ' Γ)
  | [], _, _, Δ, σ, σ', _ =>
      ⟨{ left := { ty := fun i _ h => by cases i <;> simp [lookupTypeA] at h
                   val := fun i _ _ h _ => by cases i <;> simp [lookupTypeA] at h }
         right := { ty := fun i _ h => by cases i <;> simp [lookupTypeA] at h
                    val := fun i _ _ h _ => by cases i <;> simp [lookupTypeA] at h }
         conv := fun i _ h => by cases i <;> simp [lookupTypeA] at h }⟩
  | d :: Γ, hd, k, Δ, σ, σ', h => by
      obtain ⟨D, rfl⟩ := hd d (List.mem_cons_self _ _)
      have hσ : σ = SubstA.cons (σ 0) (fun i => σ (i + 1)) := funext fun i => by cases i <;> rfl
      have hσ' : σ' = SubstA.cons (σ' 0) (fun i => σ' (i + 1)) := funext fun i => by cases i <;> rfl
      have htail : ValidSubstA E I n ρ₀ k Δ (fun i => σ (i + 1)) (fun i => σ' (i + 1)) Γ := by
        refine ⟨fun i B hB => ?_, fun i B v hB hv => ?_⟩
        · have h1 := h.1 (i + 1) (liftA 0 1 B) (by rw [lookupTypeA_cons_succ, hB]; rfl)
          rw [substA_liftA_succ, substA_liftA_succ] at h1
          exact h1
        · have h1 := h.2 (i + 1) (liftA 0 1 B) (liftA 0 1 v) (by rw [lookupTypeA_cons_succ, hB]; rfl)
            (by rw [lookupValueA_cons_succ, hv]; rfl)
          rw [substA_liftA_succ, substA_liftA_succ, substA_liftA_succ] at h1
          exact h1
      have h0 := h.1 0 (liftA 0 1 D) (lookupTypeA_cons_zero_assumption D Γ)
      rw [substA_liftA_succ, substA_liftA_succ] at h0
      obtain ⟨tl⟩ := convSubstA_of_validSubstA Γ (fun d' hd' => hd d' (List.mem_cons_of_mem _ hd')) htail
      obtain ⟨t0⟩ := (LRRelA_hasTy h0.2).1
      obtain ⟨t0'⟩ := (LRRelA_hasTy h0.2).2
      obtain ⟨c0⟩ := LRRelA_conv h0.2
      obtain ⟨tc⟩ := LREqA_tyConv h0.1
      have t0'' : HasTyA E I n Δ (σ' 0) (substA (fun i => σ' (i + 1)) D) := hasTyA_of_tyConvA t0' tc
      have hres := convSubstA_cons_gen tl t0 t0'' c0
      rw [← hσ, ← hσ'] at hres
      exact ⟨hres⟩

/-- A TERM TYPED IN THE GROUP ENVIRONMENT, at two level vectors that agree up to `=ₙ` and under a
    convertible pair of substitutions into the instantiated context, converts across them. The levels move
    by level irrelevance in `G`, the substitutions by functionality in `E`: syntactic typing in `G` and
    the substitutions' typing, no semantics. -/
theorem frecSubstConvA {G : ResolvedEnvA} (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (hpre : PrefixA G E) {a : Nat}
    {Γ : LCtxA} (hΓ : CtxWfA G I a Γ) {e : ExprA} {w : Level} (ht : HasTyA G I a Γ e (.sort w))
    {lsC lsC' : List Level} (hbC : levelsBounded n lsC = true) (hbC' : levelsBounded n lsC' = true)
    (hlC : lsC.length = a) (hlC' : lsC'.length = a) (heq : eqNList lsC lsC') {Δ : LCtxA} {κ κ' : SubstA}
    (cs : ConvSubstA E I n Δ κ κ' (instCtxA lsC Γ)) :
    Nonempty (ConvA E I n Δ (substA κ (instantiateLevelsA lsC e)) (substA κ' (instantiateLevelsA lsC' e))
      (.sort (instLevel lsC w))) := by
  have hEG : EnvClosedA G := fun r m h => hE r m (hpre r m h)
  have hELG : EnvLevelsA G := fun r m h => hEL r m (hpre r m h)
  have hRG := iotaRecHeadTypedA_prefix hpre hR
  have hRE := iotaRecHeadTypedA_of hR
  have t1 : HasTyA E I n (instCtxA lsC Γ) (instantiateLevelsA lsC e) (.sort (instLevel lsC w)) :=
    hasTyA_instLevels hEL hIL hbC hlC (hasTyEnvA hpre ht)
  have c1 := hasTyA_func hE hI hRE hIS cs t1
  obtain ⟨irr⟩ := convA_levelIrr_wf hEG hI hRG hELG hIL hbC hbC' hlC hlC' heq hΓ ht
  have c2 := convA_substA hE hI hRE hIS cs.right (convEnvA hpre irr)
  exact ⟨.trans _ _ _ _ _ c1 c2⟩

/-- a conversion at a sort is a type conversion. -/
def tyConvA_of_sortConv (hE : EnvClosedA E) (hI : IotaLiftA I) (hR : IotaRecHeadA E I)
    (hIS : IotaSubstA I) {Γ : LCtxA} (hΓ : CtxWfA E I n Γ) {A B : ExprA} {w : Level}
    (c : ConvA E I n Γ A B (.sort w)) : TyConvA E I n Γ A B :=
  .of Γ A B w w w (convA_hasTy_left hE hI hR hIS hΓ c) (eqNA_refl w) (convA_hasTy_right hE hI hR hIS hΓ c)
    (eqNA_refl w) c

/-- THE FIELD'S SYNTACTIC TRIPLE CARRIES ACROSS A TYPE CONVERSION OF ITS DOMAIN. -/
theorem frecTripleA_carry {Γ : LCtxA} {d d' f f' : ExprA} (hc : Nonempty (TyConvA E I n Γ d d'))
    (h : Nonempty (HasTyA E I n Γ f d) ∧ Nonempty (HasTyA E I n Γ f' d) ∧ Nonempty (ConvA E I n Γ f f' d)) :
    Nonempty (HasTyA E I n Γ f d') ∧ Nonempty (HasTyA E I n Γ f' d') ∧ Nonempty (ConvA E I n Γ f f' d') := by
  have := congrFun (congrFun (tripleA_eq_of_tyConv hc) f) f'
  exact this ▸ h

/-- THE WALK'S REACHED DOMAIN IS THE BASE DOMAIN'S INSTANCE: the function-recursive field's domain after
    `pre`, at the parameters `ps` and the levels `lsC`, is the base domain (over the parameter locals past
    the plain fields) instantiated at `lsC` and substituted at the walk's substitution. -/
theorem frecDomA_reach {fm : CheckedMemberA} (fv : FamViewA fm) {f : Nat} {lsC : List Level}
    (hlC : lsC.length = fm.arity) {fsPre : List FieldA} {pre ps : List ExprA}
    (hps : ps.length = fm.nparamsA) (hlen : pre.length = fsPre.length) {B : ExprA} {uB : Level}
    {Bs : List (ExprA × Level)} {idx : List ExprA} {D : ExprA}
    (hDe : (ctorFieldsA f lsC (instLevel lsC fv.sort) ps
      (consListA (plainArgsA fsPre pre) (consListA ps SubstA.id))
      ((instDomsA lsC ((B, uB) :: Bs)).map plainA) (idx.map (instantiateLevelsA lsC))).1 = D) :
    substA (consListA (plainArgsA fsPre pre) (consListA ps SubstA.id))
      (instantiateLevelsA lsC (frecDomA f (canonLevelsA fm.arity) fv.sort
        ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre 0))) SubstA.id ((B, uB) :: Bs) idx).1)
      = D := by
  have hxs : plainIdxA fsPre 0 = (plainArgsA fsPre pre).length := by
    have := plainIdxA_length fsPre pre hlen 0
    simpa using this
  have e1 : fv.params.length = ps.length := by rw [hps, fv.nparams]
  rw [e1, hxs, ← hlC]
  rw [frecDomA_instance f lsC fv.sort idx ((B, uB) :: Bs) (plainArgsA fsPre pre) ps]
  rw [← hDe, frecDomA_eq]

/-- two telescopes' domains pairwise convertible, each at its binder's sort, in the context of the left
    earlier ones (R-NoFunRec-1 step 1 (1c-ε2d-L3b-2)). -/
inductive TelConvA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    LCtxA → List (ExprA × Level) → List (ExprA × Level) → Prop
  | nil (Γ : LCtxA) : TelConvA E I n Γ [] []
  | cons (Γ : LCtxA) (D D' : ExprA) (u u' : Level) (ds ds' : List (ExprA × Level)) (hu : eqN u u')
      (hc : Nonempty (ConvA E I n Γ D D' (.sort u))) (tl : TelConvA E I n (.assumption D :: Γ) ds ds') :
      TelConvA E I n Γ ((D, u) :: ds) ((D', u') :: ds')

theorem piDomListA_of_not_pi {e : ExprA} (h : ∀ D u C v, e ≠ .pi D u C v) : piDomListA e = [] := by
  cases e with
  | pi D u C v => exact absurd rfl (h D u C v)
  | _ => rfl

/-- THE FUNCTION-RECURSIVE FIELD'S INNER BINDERS CONVERT BINDERWISE, from syntactic evidence: the
    base binders are typed in the group environment (`FieldsTyA.plain`), the substitution pair is
    convertible, and the levels agree up to `=ₙ`. Each binder's two instances convert at the binder's
    own sort (`frecSubstConvA`), the pair extends under it (`convSubstA_up`: the right substitution
    retyped by the same type's functionality). -/
theorem frecTelConvAux {E₀ G : ResolvedEnvA} (hE : EnvClosedA E) (hI : IotaLiftA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (hpre₀G : PrefixA E₀ G)
    (hpreG : PrefixA G E) {a : Nat} {lsC lsC' : List Level} (hbC : levelsBounded n lsC = true)
    (hbC' : levelsBounded n lsC' = true) (hlC : lsC.length = a) (hlC' : lsC'.length = a)
    (heq : eqNList lsC lsC') {f : Nat} {idxTel : Nat → ExprA} (idx : List ExprA)
    {wL wR : Level} :
    (ds : List (ExprA × Level)) → {Γp : LCtxA} → {k : Nat} → CtxWfA E₀ I a Γp →
    FieldsTyA E₀ I a idxTel Γp k (ds.map plainA) idx → {Δ : LCtxA} → {σ σ' : SubstA} →
    (pl pl' : List ExprA) → ConvSubstA E I n Δ σ σ' (instCtxA lsC Γp) →
    TelConvA E I n Δ
      (piDomListA (frecDomA f lsC wL pl σ (instDomsA lsC ds) (idx.map (instantiateLevelsA lsC))).1)
      (piDomListA (frecDomA f lsC' wR pl' σ' (instDomsA lsC' ds) (idx.map (instantiateLevelsA lsC'))).1)
  | [], _, _, _, _, _, _, _, pl, pl', _ => by
      simp only [instDomsA, List.map_nil, frecDomA]
      rw [piDomListA_of_not_pi (foldAppsA_const_ne_pi f lsC _),
        piDomListA_of_not_pi (foldAppsA_const_ne_pi f lsC' _)]
      exact .nil _
  | (D, u) :: ds, Γp, k, hΓ, hty, Δ, σ, σ', pl, pl', cs => by
      simp only [List.map, plainA] at hty
      cases hty with
      | plain _ _ _ _ _ _ hD tl =>
          have hEG : EnvClosedA G := fun r m h => hE r m (hpreG r m h)
          have hD' := hasTyEnvA hpre₀G hD
          have hRE := iotaRecHeadTypedA_of hR
          have hDΓ : CtxWfA G I a Γp := viewTy_ctx_env hpre₀G hΓ
          obtain ⟨hc⟩ := frecSubstConvA hE hI hIS hR hEL hIL hpreG hDΓ hD' hbC hbC' hlC hlC' heq cs
          have t1 : HasTyA E I n (instCtxA lsC Γp) (instantiateLevelsA lsC D)
              (.sort (instLevel lsC u)) := hasTyA_instLevels hEL hIL hbC hlC
            (hasTyEnvA hpreG hD')
          have hA := hasTyA_substA hE hI hRE hIS cs.left t1
          have hA' := hasTyA_substA hE hI hRE hIS cs.right t1
          have hc' := hasTyA_func hE hI hRE hIS cs t1
          have cs₁ := convSubstA_up hE hI cs hA hA' hc'
          have ih := frecTelConvAux (f := f) (wL := wL) (wR := wR) hE hI hIS hR hEL hIL hpre₀G hpreG hbC
            hbC' hlC hlC' heq idx ds
            (Γp := .assumption D :: Γp) (k := k + 1) (.assumption hΓ hD) tl (pl.map (liftA 0 1))
            (pl'.map (liftA 0 1)) cs₁
          simp only [instDomsA, List.map, frecDomA, piDomListA]
          exact .cons _ _ _ _ _ _ _ (instLevel_eqNList heq u) ⟨hc⟩ ih

/-- THE PRODUCER (1c-ε2d-a0), WITH ITS BINDERWISE HALF (1c-ε2d-L3b-2). A walk reaching a function-recursive
    field reaches a declared domain on each side (after `pre` at `ps`, `lsC`; after `pre'` at `ps'`, `lsC'`);
    the two are type-convertible, and their inner binders are convertible pairwise (`TelConvA`).
    From the walk's evidence only: the field list's typing in `E₀` and the valid substitution pair
    (the base's fundamental theorem, through `frecWalkA`), the base domain's syntactic typing in the
    group environment `G` (`frecDomTyG`), level irrelevance in `G`, and functionality in `E`. No
    fundamental theorem of `G` or `E`, no Π-injectivity, no recursor clause. -/
theorem frecDomConvCoreA {E₀ E G : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {f : Nat}
    {fm : CheckedMemberA}
    {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hEL : EnvLevelsA E)
    (hIL : IotaLevelsA I) (hIS : IotaSubstA I) (hR : IotaRecHeadA E I)
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (hpre₀G : PrefixA E₀ G) (hpreG : PrefixA G E) (hmemG : G.members f = some fm)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity) {j : Nat}
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ρ : WkSpecA}
    (hρ : WkOk₀A E I n ρ Γ) {c : Nat} {cm : CheckedMemberA}
    {lsA lsC lsC' : List Level} {kinds ksPre ks : List FieldShape} {jn : Nat} {T T' : ExprA}
    {pre pre' : List ExprA} {D : ExprA} {uD : Level} {C₀ : ExprA} {vC : Level} {D' : ExprA}
    {uD' : Level} {C₀' : ExprA} {vC' : Level}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hsp : kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    (hlA : eqNList ls lsA) (hlAC : eqNListB n lsA lsC) (hlCC : eqNListB n lsC lsC')
    (hTc : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hTc' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    (hw : ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) X F fm.nparamsA (ps.map (wkExprA ρ)) T
      ksPre pre pre')
    (hTD : applyTelA pre T = some (.pi D uD C₀ vC)) (hTD' : applyTelA pre' T' = some (.pi D' uD' C₀' vC')) :
    Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D') ∧
      TelConvA E I n (wkCtxA ρ Γ) (piDomListA D) (piDomListA D') := by
  refine frecWalkA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hIL hfresh hcensus hcl hT hb hl hΓ
    hps hps' hrel hρ hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' ?_
  intro fsPre B uB Bs idx hBs hlen hlen' hdom hΓp huniv hDe hDe' ⟨fsRest, res, ⟨hty⟩⟩ ⟨K₁, hK₁⟩
  have hlsC : eqNList ls lsC := eqNListA_trans hlA hlAC.1
  have hlsC' : eqNList ls lsC' := eqNListA_trans hlsC hlCC.1
  have hlC : lsC.length = fm.arity := (eqNListA_length hlsC).symm.trans hl
  have hlC' : lsC'.length = fm.arity := (eqNListA_length hlsC').symm.trans hl
  have hbC : levelsBounded n lsC = true := hlAC.2
  have hbC' : levelsBounded n lsC' = true := hlCC.2
  obtain ⟨hΓρ⟩ := ctxWfA_wk₀ hΓ hρ
  have hEG : EnvClosedA G := fun r m h => hE r m (hpreG r m h)
  have hd0 := frecDomTyG hEG hI (iotaRecHeadTypedA_prefix hpreG hR) hIS hpre₀G (fv := fv)
    (hasTyEnvA hpre₀G hT) hmemG fsPre hty
  have hΓG := viewTy_ctx_env hpre₀G hΓp
  have hK1 : K₁ ≤ max K₁ (max k j) := by omega
  have hKk : k ≤ max K₁ (max k j) := by omega
  have hKj : j ≤ max K₁ (max k j) := by omega
  have hV₁ := (hK₁ _ hK1 hKj hKk).2
  have hasm : AssumpOnlyA (instCtxA lsC (plainCtxA fsPre (telCtxA fv.params))) :=
    assumpOnlyA_instCtxA lsC (assumpOnlyA_plainCtxA fsPre _ (assumpOnlyA_telCtxA fv.params))
  obtain ⟨cs'⟩ := convSubstA_of_validSubstA _ hasm hV₁
  obtain ⟨hc⟩ := frecSubstConvA hE hI hIS hR hEL hIL hpreG hΓG hd0 hbC hbC' hlC hlC' hlCC.1 cs'
  have hps₁ : (ps.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps]
  have hps₂ : (ps'.map (wkExprA ρ)).length = fm.nparamsA := by rw [List.length_map, hps']
  have hDC := frecDomA_reach fv hlC hps₁ hlen hDe
  have hDC' := frecDomA_reach fv hlC' hps₂ hlen' hDe'
  refine ⟨?_, ?_⟩
  · rw [hDC, hDC'] at hc
    exact ⟨tyConvA_of_sortConv hE hI hR hIS hΓρ hc⟩
  · rw [← hDe, ← hDe', ← frecDomA_eq, ← frecDomA_eq]
    exact frecTelConvAux hE hI hIS hR hEL hIL hpre₀G hpreG hbC hbC' hlC hlC' hlCC.1 idx
      ((B, uB) :: Bs) hΓp hdom _ _ cs'

/-- THE PRODUCER (1c-ε2d-a0), its type-conversion half. -/
theorem frecDomConvA {E₀ E G : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {f : Nat}
    {fm : CheckedMemberA}
    {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I)
    (hR₀ : IotaRecHeadTypedA E₀ I) (hEL₀ : EnvLevelsA E₀) (hEL : EnvLevelsA E)
    (hIL : IotaLevelsA I) (hIS : IotaSubstA I) (hR : IotaRecHeadA E I)
    (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (hpre₀G : PrefixA E₀ G) (hpreG : PrefixA G E) (hmemG : G.members f = some fm)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity) {j : Nat}
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : CRelA} {F : Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} {ρ : WkSpecA}
    (hρ : WkOk₀A E I n ρ Γ) {c : Nat} {cm : CheckedMemberA}
    {lsA lsC lsC' : List Level} {kinds ksPre ks : List FieldShape} {jn : Nat} {T T' : ExprA}
    {pre pre' : List ExprA} {D : ExprA} {uD : Level} {C₀ : ExprA} {vC : Level} {D' : ExprA}
    {uD' : Level} {C₀' : ExprA} {vC' : Level}
    (hcm : E.members c = some cm) (hk : cm.mclass = .constructorM) (hfam : memberFamRefA cm = some f)
    (hkinds : ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds)
    (hsp : kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks)
    (hlA : eqNList ls lsA) (hlAC : eqNListB n lsA lsC) (hlCC : eqNListB n lsC lsC')
    (hTc : applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T)
    (hTc' : applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T')
    (hw : ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) X F fm.nparamsA (ps.map (wkExprA ρ)) T
      ksPre pre pre')
    (hTD : applyTelA pre T = some (.pi D uD C₀ vC)) (hTD' : applyTelA pre' T' = some (.pi D' uD' C₀' vC')) :
    Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D') :=
  (frecDomConvCoreA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hEL hIL hIS hR hfresh hcensus hcl hT hpre₀G hpreG hmemG hb
    hl hΓ hps hps' hrel hρ hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD').1

/-- THE DECLARED-DOMAIN DATUM (`hFldIdom`) (R-NoFunRec-1 step 1 (1c-ε2d-L1)): at a function-recursive
    position, the declared domains reached by two walks at `=ₙ` level lists, on one parameter list,
    are type-convertible. `frecDomConvA` at the diagonal parameters. -/
theorem famFldIdomA {E₀ E G : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {f : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (hpre₀G : PrefixA E₀ G) (hpreG : PrefixA G E) (hmemG : G.members f = some fm)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity) {j : Nat}
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps is : List ExprA}
    (hps : ps.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps ++ is))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC lsC' : List Level) (kinds ksPre ks : List FieldShape) (jn : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks →
      eqNList ls lsA → eqNListB n lsA lsC → eqNListB n lsC lsC' →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC' (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      applyTelA pre' T' = some (.pi D' uD' C' vC') →
      Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D') :=
  fun _ρ hρ _c _cm _lsA _lsC _lsC' _kinds _ksPre _ks _jn _T _T' _pre _pre' _D _uD _C _vC _D' _uD' _C' _vC'
      hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD' =>
    frecDomConvA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hEL hIL hIS hR hfresh hcensus hcl hT hpre₀G hpreG hmemG hb hl
      hΓ hps hps hrel hρ hcm hk hfam hkinds hsp hlA hlAC hlCC hTc hTc' hw hTD hTD'

/-- the same across two parameter lists, at one level list (`hXFldIdom`). -/
theorem famXFldIdomA {E₀ E G : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {ρ₀ : Nat → Nat} {f : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} {cs : List (GroupCtorA I E₀ f fm fv)}
    (hfund : BaseFundA E₀ E I n ρ₀) (hfc : BaseFundConvA E₀ E I n ρ₀)
    (hEN : EnvNormCtorTypeA E) (hNC : EnvNormClosedA E)
    (hE₀ : EnvClosedA E₀) (hE : EnvClosedA E) (hI : IotaLiftA I) (hR₀ : IotaRecHeadTypedA E₀ I)
    (hEL₀ : EnvLevelsA E₀) (hEL : EnvLevelsA E) (hIL : IotaLevelsA I) (hIS : IotaSubstA I)
    (hR : IotaRecHeadA E I) (hfresh : E₀.members f = none)
    (hcensus : ∀ c cm, E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ∃ gc ∈ cs, gc.ref = c ∧ gc.member = cm)
    (hcl : ∀ k, liftA k 1 fm.mtypeA = fm.mtypeA) {u : Level}
    (hT : HasTyA E₀ I fm.arity [] fm.mtypeA (.sort u))
    (hpre₀G : PrefixA E₀ G) (hpreG : PrefixA G E) (hmemG : G.members f = some fm)
    {ls : List Level} (hb : levelsBounded n ls = true) (hl : ls.length = fm.arity) {j : Nat}
    {k : Nat} {Γ : LCtxA} (hΓ : Nonempty (CtxWfA E I n Γ)) {ps ps' is is' : List ExprA}
    (hps : ps.length = fm.nparamsA) (hps' : ps'.length = fm.nparamsA)
    (hrel : ArgsRelKA E I n ρ₀ k Γ (instantiateLevelsA ls fm.mtypeA) (ps ++ is) (ps' ++ is'))
    {X : WkSpecA → List Level → CRelA}
    {F : WkSpecA → Nat → List Level → List Level → Nat → List ExprA → ExprA → Nat → ExprA → ExprA → Prop} :
    ∀ (ρ : WkSpecA), WkOk₀A E I n ρ Γ → ∀ (c : Nat) (cm : CheckedMemberA)
      (lsA lsC : List Level) (kinds ksPre ks : List FieldShape) (jn : Nat) (T T' : ExprA)
      (pre pre' : List ExprA) (D : ExprA) (uD : Level) (C : ExprA) (vC : Level)
      (D' : ExprA) (uD' : Level) (C' : ExprA) (vC' : Level),
      E.members c = some cm → cm.mclass = .constructorM → memberFamRefA cm = some f →
      ctorShapesA f fm.nparamsA (cm.normA.getD cm.mtypeA) = some kinds →
      kinds = ksPre ++ FieldShape.recursive (jn + 1) :: ks →
      eqNList ls lsA → eqNListB n lsA lsC →
      applyTelA (ps.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T →
      applyTelA (ps'.map (wkExprA ρ)) (instantiateLevelsA lsC (cm.normA.getD cm.mtypeA)) = some T' →
      ArgsRelA (famRsA E I n ρ₀ j Γ ρ c lsC) (X ρ lsA) (F ρ c lsC lsA) fm.nparamsA (ps.map (wkExprA ρ)) T
        ksPre pre pre' →
      applyTelA pre T = some (.pi D uD C vC) →
      applyTelA pre T' = some (.pi D' uD' C' vC') →
      Nonempty (TyConvA E I n (wkCtxA ρ Γ) D D') :=
  fun _ρ hρ _c _cm _lsA _lsC _kinds _ksPre _ks _jn _T _T' _pre _pre' _D _uD _C _vC _D' _uD' _C' _vC'
      hcm hk hfam hkinds hsp hlA hlAC hTc hTc' hw hTD hTD' =>
    frecDomConvA hfund hfc hEN hNC hE₀ hE hI hR₀ hEL₀ hEL hIL hIS hR hfresh hcensus hcl hT hpre₀G hpreG hmemG hb hl
      hΓ hps hps' hrel hρ hcm hk hfam hkinds hsp hlA hlAC (eqNListB_refl hlAC.2) hTc hTc'
      (argsRelA_diag hEN (famRsA_refl_left hEN) hw) hTD hTD'

end FrecDomSyn


/-! ## (2) the non-vacuous instance

A family `Fam.{l} : Sort (l+1)` with a constructor `mk`, a plain variable `x : Sort l`, and the base domain
`Π (_ : x) (_ : x), Fam.{l}` with two inner binders. The left instance is at the level `2` and the
parameter `Sort 1`; the right at the level `imax 1 2` (`=ₙ` `2`, syntactically different) and the
parameter's β-redex (convertible, not equal). The core lemma gives the two declared domains' conversion,
and a field of the left domain carries to the right. The substitution pair is given as a `ConvSubstA`
here; the producer builds it from the walk's valid pair (`convSubstA_of_validSubstA`). -/

namespace FrecDomSynTest

def p : Level := .param 0
def lv2 : Level := .succ (.succ .zero)
def lv2' : Level := .imax (.succ .zero) (.succ (.succ .zero))
def famM : CheckedMemberA := ⟨.inductiveM, 1, .sort (.succ p), none, 0, none⟩
def mkM : CheckedMemberA := ⟨.constructorM, 1, .const 0 [p], none, 0, none⟩
def tEnv : ResolvedEnvA := extendEnvA (extendEnvA emptyEnvA 0 famM) 1 mkM

theorem tEnv_fam : tEnv.members 0 = some famM := rfl
theorem tEnv_mk : tEnv.members 1 = some mkM := rfl

theorem tEnv_closed : EnvClosedA tEnv := by
  intro r m hm
  by_cases h1 : r = 1
  · subst h1; cases hm; exact ⟨fun _ => rfl, fun _ hb => Option.noConfusion hb⟩
  · by_cases h0 : r = 0
    · subst h0
      have : tEnv.members 0 = some famM := rfl
      rw [this] at hm; cases hm; exact ⟨fun _ => rfl, fun _ hb => Option.noConfusion hb⟩
    · exfalso
      simp [tEnv, extendEnvA, emptyEnvA, h0, h1] at hm

theorem tEnv_levels : EnvLevelsA tEnv := by
  intro r m hm
  by_cases h1 : r = 1
  · subst h1; cases hm; exact ⟨rfl, fun _ hb => Option.noConfusion hb⟩
  · by_cases h0 : r = 0
    · subst h0
      have : tEnv.members 0 = some famM := rfl
      rw [this] at hm; cases hm; exact ⟨rfl, fun _ hb => Option.noConfusion hb⟩
    · exfalso
      simp [tEnv, extendEnvA, emptyEnvA, h0, h1] at hm


/-- the base domain: two inner binders over the plain variable `x : Sort p`, ending in the family. -/
def d₀ : ExprA := .pi (.bvar 0) p (.pi (.bvar 1) p (.const 0 [p]) (.succ p)) (.imax p (.succ p))
def Γ₀ : LCtxA := [.assumption (.sort p)]
def w₀ : Level := .imax p (.imax p (.succ p))

def famConstTy (n : Nat) (Γ : LCtxA) (l : Level) (hb : levelsBounded n [l] = true) :
    HasTyA tEnv noIotaA n Γ (.const 0 [l]) (.sort (.succ l)) :=
  .const Γ 0 [l] famM (.succ (.succ l)) tEnv_fam rfl hb (.sort Γ (.succ l))

def mkConstTy (n : Nat) (Γ : LCtxA) (l : Level) (hb : levelsBounded n [l] = true) :
    HasTyA tEnv noIotaA n Γ (.const 1 [l]) (.const 0 [l]) :=
  .const Γ 1 [l] mkM (.succ l) tEnv_mk rfl hb (famConstTy n Γ l hb)

def d₀Ty : HasTyA tEnv noIotaA 1 Γ₀ d₀ (.sort w₀) :=
  .pi Γ₀ (.bvar 0) p _ _
    (.bvar Γ₀ 0 (.sort p) (.succ p) rfl (.sort Γ₀ p))
    (.pi _ (.bvar 1) p (.const 0 [p]) (.succ p)
      (.bvar _ 1 (.sort p) (.succ p) rfl (.sort _ p))
      (famConstTy 1 _ p rfl))

/-- the left parameter image `Sort 1` and the right one, its β-redex: convertible, not equal. -/
def argL : ExprA := .sort (.succ .zero)
def argR : ExprA := .app (.lam (.sort lv2) (.succ lv2) (.bvar 0)) (.sort (.succ .zero))

def argRTy : HasTyA tEnv noIotaA 0 [] argR (.sort lv2) :=
  .app [] (.lam (.sort lv2) (.succ lv2) (.bvar 0)) (.sort (.succ .zero)) (.sort lv2) (.sort lv2)
    (.succ lv2) (.succ lv2) (.succ lv2)
    (.sort _ lv2) (.sort [] lv2)
    (.lam [] (.sort lv2) (.succ lv2) (.bvar 0) (.sort lv2) (.succ lv2) (.sort [] lv2) (.sort _ lv2)
      (.bvar _ 0 (.sort lv2) (.succ lv2) rfl (.sort _ lv2)))
    (.sort [] (.succ .zero))

def argConv : ConvA tEnv noIotaA 0 [] argL argR (.sort lv2) :=
  .symm _ _ _ _
    (.beta [] (.sort lv2) (.succ lv2) (.bvar 0) (.sort (.succ .zero)) (.sort lv2) (.sort [] lv2)
      (.bvar _ 0 (.sort lv2) (.succ lv2) rfl (.sort _ lv2)) (.sort [] (.succ .zero))
      (.sort [] (.succ .zero)))

def κL : SubstA := SubstA.cons argL SubstA.id
def κR : SubstA := SubstA.cons argR SubstA.id

def csTest : ConvSubstA tEnv noIotaA 0 [] κL κR [.assumption (.sort lv2)] :=
  convSubstA_cons_gen
    (σ := SubstA.id) (σ' := SubstA.id)
    { left := { ty := fun i _ h => by cases i <;> simp [lookupTypeA] at h
                val := fun i _ _ h _ => by cases i <;> simp [lookupTypeA] at h }
      right := { ty := fun i _ h => by cases i <;> simp [lookupTypeA] at h
                 val := fun i _ _ h _ => by cases i <;> simp [lookupTypeA] at h }
      conv := fun i _ h => by cases i <;> simp [lookupTypeA] at h }
    (.sort [] (.succ .zero)) argRTy argConv

/-- the two instances' declared domains: the left at `Sort 1` and the level `2`, the right at its β-redex
    and the level `imax 1 2` (`=ₙ` `2`, syntactically different). -/
def dL : ExprA := .pi argL lv2 (.pi argL lv2 (.const 0 [lv2]) (.succ lv2)) (.imax lv2 (.succ lv2))
def dR : ExprA := .pi argR lv2' (.pi argR lv2' (.const 0 [lv2']) (.succ lv2')) (.imax lv2' (.succ lv2'))

/-- a field of the left domain: `fun _ _ => mk`. -/
def fT : ExprA := .lam argL lv2 (.lam argL lv2 (.const 1 [lv2]))

def fTy : HasTyA tEnv noIotaA 0 [] fT dL :=
  .lam [] argL lv2 (.lam argL lv2 (.const 1 [lv2])) (.pi argL lv2 (.const 0 [lv2]) (.succ lv2))
    (.imax lv2 (.succ lv2))
    (.sort [] (.succ .zero))
    (.pi _ argL lv2 (.const 0 [lv2]) (.succ lv2) (.sort _ (.succ .zero)) (famConstTy 0 _ lv2 rfl))
    (.lam _ argL lv2 (.const 1 [lv2]) (.const 0 [lv2]) (.succ lv2) (.sort _ (.succ .zero))
      (famConstTy 0 _ lv2 rfl) (mkConstTy 0 _ lv2 rfl))

theorem dL_ne_dR : dL ≠ dR := by
  intro h
  simp [dL, dR, argL, argR, lv2, lv2'] at h

theorem frecDomSyn_instance :
    dL ≠ dR ∧ Nonempty (TyConvA tEnv noIotaA 0 [] dL dR) ∧ Nonempty (HasTyA tEnv noIotaA 0 [] fT dR) ∧
      Nonempty (HasTyA tEnv noIotaA 0 [] fT dR) ∧ Nonempty (ConvA tEnv noIotaA 0 [] fT fT dR) := by
  have hΓ₀ : CtxWfA tEnv noIotaA 1 Γ₀ := .assumption .nil (.sort [] p)
  have heq : eqNList [lv2] [lv2'] := ⟨fun _ => rfl, trivial⟩
  obtain ⟨hc⟩ := frecSubstConvA (n := 0) (G := tEnv) tEnv_closed noIotaA_lift noIotaA_subst
    (noIotaA_recHead tEnv) tEnv_levels noIotaA_levels (fun _ _ h => h) hΓ₀ d₀Ty
    (lsC := [lv2]) (lsC' := [lv2']) rfl rfl rfl rfl heq csTest
  have hc' : ConvA tEnv noIotaA 0 [] dL dR (.sort (instLevel [lv2] w₀)) := hc
  have tc := tyConvA_of_sortConv tEnv_closed noIotaA_lift (noIotaA_recHead tEnv) noIotaA_subst .nil hc'
  obtain ⟨h1, h2, h3⟩ := frecTripleA_carry ⟨tc⟩ ⟨⟨fTy⟩, ⟨fTy⟩, ⟨.refl [] fT dL fTy⟩⟩
  exact ⟨dL_ne_dR, ⟨tc⟩, h1, h2, h3⟩

end FrecDomSynTest

#print axioms plainIdxA_add
#print axioms map_liftA_zero
#print axioms frecOpenA
#print axioms frecDomTyG
#print axioms leN_frecLevelA
#print axioms frecSort_ht_le
#print axioms frecDomA_instance
#print axioms assumpOnlyA_telCtxA
#print axioms assumpOnlyA_plainCtxA
#print axioms assumpOnlyA_instCtxA
#print axioms convSubstA_cons_gen
#print axioms convSubstA_of_validSubstA
#print axioms frecSubstConvA
#print axioms tyConvA_of_sortConv
#print axioms frecTripleA_carry
#print axioms frecDomA_reach
#print axioms piDomListA_of_not_pi
#print axioms frecTelConvAux
#print axioms frecDomConvCoreA
#print axioms frecDomConvA
#print axioms famFldIdomA
#print axioms famXFldIdomA
#print axioms FrecDomSynTest.frecDomSyn_instance

end Rcic.Declarative.Ann
