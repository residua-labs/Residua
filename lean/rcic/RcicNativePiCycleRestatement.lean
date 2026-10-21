import rcic.RcicNativeTypedModelRel
import rcic.RcicIotaSRRowsCtor

/-!
# The declared telescope has its own conversion algebra

The family PER's symmetry and transitivity need only compare two level instances
of the same declared telescope, after related prefixes.  The general
`convArgs_symm_walk` forgets that common template and subsequently uses `PiRowField`
to recover its domains.  Here the declared domain's own typing feeds the landed
level and mixed-prefix substitution congruences directly.

No derivation-domain alignment is inferred.  The application fundamental case
and `NodeDeclAlign` still need their own producers.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.PiCycleAudit

open Rcic.Declarative.NativeValleys.FamModelAudit
open Rcic.Declarative.NativeValleys.FamModelLRSAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- Assemble a syntactically given telescope from all its actual left-domain
slot conversions.  This is independent of the family and of any injectivity row. -/
theorem convArgsT_of_allSlots
    (pre ds xs ys : List (Expr Nat)) (U : Expr Nat)
    (hlen : xs.length = ds.length) (hlen' : ys.length = xs.length)
    (hslots : ∀ i (hi : i < xs.length),
      Nonempty (ConvT E n Γ xs[i] (getElem ys i (by omega))
        (instPrefix (pre ++ xs.take i) (getElem ds i (by omega))))) :
    ConvArgsT E n Γ (instPrefix pre (policyPi ds U)) xs ys := by
  induction ds generalizing pre xs ys with
  | nil =>
      have hx : xs = [] := List.length_eq_zero.mp hlen
      have hy : ys = [] := List.length_eq_zero.mp (hlen'.trans hlen)
      subst xs; subst ys
      exact .nil _
  | cons d ds ih =>
      cases xs with
      | nil => exact Nat.noConfusion hlen
      | cons x xs =>
          cases ys with
          | nil => exact Nat.noConfusion hlen'
          | cons y ys =>
              have hx : xs.length = ds.length := Nat.succ.inj hlen
              have hy : ys.length = xs.length := Nat.succ.inj hlen'
              have hc := hslots 0 (Nat.succ_pos _)
              simp only [List.getElem_cons_zero, List.take_zero, List.append_nil] at hc
              have htail := ih (pre ++ [x]) xs ys hx hy (by
                intro i hi
                have h := hslots (i + 1) (Nat.succ_lt_succ hi)
                simpa only [List.getElem_cons_succ, List.take_succ_cons,
                  List.append_assoc, List.singleton_append] using h)
              change ConvArgsT E n Γ (instPrefix pre (.pi d (policyPi ds U)))
                (x :: xs) (y :: ys)
              rw [instPrefix_pi]
              rw [instPrefix_snoc] at htail
              exact .cons _ _ x y xs ys hc htail

/-- Slot projection, with bounded indices.  It retains the original declared
domain, before either level substitution or argument-prefix substitution. -/
theorem declaredSlotConv
    (hW : EnvWfT E) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls : List Level} {xs ys : List (Expr Nat)}
    (hlen : xs.length = (piDomsOf m.mtype).length)
    (hxy : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs ys)
    (i : Nat) (hi : i < xs.length) :
    Nonempty (ConvT E n Γ xs[i]
      (getElem ys i (by have := NativeFamilyProjection.convArgs_length hxy; omega))
      (instPrefix (xs.take i)
        (instantiateLevels ls (getElem (piDomsOf m.mtype) i (by omega))))) := by
  have hy : i < ys.length := by
    have := NativeFamilyProjection.convArgs_length hxy; omega
  have hd : i < (piDomsOf m.mtype).length := by omega
  have h := convArgsT_instPrefix hxy
    ((piDomsOf m.mtype).map (instantiateLevels ls))
    (.sort (instLevel ls (inductiveSortLevel hW hm hind)))
    (instMtype_policyPi_of_inductiveM hW hm hind ls)
    i xs[i] ys[i] (instantiateLevels ls (piDomsOf m.mtype)[i])
    (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hy)
    (by rw [List.getElem?_map, List.getElem?_eq_getElem hd]; rfl)
  exact h

/-- The alignment used by the family PER: two related prefixes of the SAME
declared telescope, possibly at pointwise-convertible universe lists.  The proof
composes level congruence with mixed prefix substitution and uses no Π row. -/
theorem declaredSlotAlign
    (hW : EnvWfT E) (hΓ : CtxWfT E n Γ)
    {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    {ls ls' : List Level} {xs ys : List (Expr Nat)} {w w' : Level}
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (hty' : HasTyT E n Γ (foldApps (.const r ls') ys) (.sort w'))
    (heqN : eqNList ls ls')
    (hlen : xs.length = (piDomsOf m.mtype).length)
    (hxy : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs ys)
    (i : Nat) (hi : i < (piDomsOf m.mtype).length) :
    Nonempty (TyConvT E n Γ
      (instPrefix (xs.take i) (instantiateLevels ls (piDomsOf m.mtype)[i]))
      (instPrefix (ys.take i) (instantiateLevels ls' (piDomsOf m.mtype)[i]))) := by
  obtain ⟨hlsl, hwfL⟩ := NativeFamilyProjection.native_level_facts hm hty
  obtain ⟨_, hwfR⟩ := NativeFamilyProjection.native_level_facts hm hty'
  obtain ⟨u, hmT⟩ := envWfT_mtypeSortTyped hW r m hm
  rw [mtype_policyPi_of_inductiveM hW hm hind] at hmT
  obtain ⟨lv, hds⟩ := hasTyT_policyPi_invTS (piDomsOf m.mtype) hmT
  have hD := hds i hi
  rw [List.append_nil] at hD
  have cD := convT_instantiateLevels (envWfT_levels hW)
    (iotaLevelsT_of_envWfT hW) heqN hwfL hwfR hlsl hD
  rw [instLvlsCtx_policyPrefixContext] at cD
  have cDΓ := convT_relocateN (Γ := Γ) cD
  obtain ⟨hctx⟩ := ctxWfT_telescope hW hΓ hwfL hlsl
    (piDomsOf m.mtype) lv hds i (Nat.le_of_lt hi)
  have hright := (convEnds hW hctx cDΓ).2.1
  have hlenxy := NativeFamilyProjection.convArgs_length hxy
  have hiX : i ≤ xs.length := by omega
  have hiY : i ≤ ys.length := by omega
  have hxTake : (xs.take i).length = i := by
    rw [List.length_take, Nat.min_eq_left hiX]
  have hyTake : (ys.take i).length = i := by
    rw [List.length_take, Nat.min_eq_left hiY]
  obtain ⟨prefixConvs⟩ := finChoiceT i
    (fun j hj => ConvT E n Γ (getElem xs j (by omega)) (getElem ys j (by omega))
      (instPrefix (xs.take j)
        (instantiateLevels ls (getElem (piDomsOf m.mtype) j (by omega)))))
    (fun j hj => declaredSlotConv hW hm hind hlen hxy j (by omega))
  have hargs : ∀ j (hj : j < (xs.take i).length),
      ConvT E n Γ (xs.take i)[j]
        (getElem (ys.take i) j (by rw [hxTake] at hj; rw [hyTake]; exact hj))
        (instPrefix ((xs.take i).take j)
          (outerDom ((((piDomsOf m.mtype).map (instantiateLevels ls)).take i).reverse) j)) := by
    intro j hj
    have hj' : j < i := by rwa [hxTake] at hj
    rw [outerDom_take_reverse _ i j (by rw [List.length_map]; omega) hj']
    simpa only [List.getElem_take, List.take_take,
      Nat.min_eq_left (Nat.le_of_lt hj'), List.getElem_map] using prefixConvs j hj'
  have hconv := convT_instPrefix hW (substLetT_of_envWfT hW)
    (constsRightDataT_of_envWfT hW) (xs.take i) (ys.take i)
    (ΔT := (((piDomsOf m.mtype).map (instantiateLevels ls)).take i).reverse)
    (by rw [List.length_reverse, List.length_take, List.length_map,
      Nat.min_eq_left (Nat.le_of_lt hi), hxTake])
    (by rw [hxTake, hyTake]) hctx cDΓ hright hargs
    (fun j hj => (convEnds hW hΓ (hargs j hj)).1)
  change ConvT E n Γ _ _ (instPrefix (xs.take i) (.sort (instLevel ls (lv i)))) at hconv
  rw [instPrefix_sort] at hconv
  exact ⟨.of _ _ _ _ hconv⟩

/-- The existing typed PER's symmetry input, now paid directly from admission. -/
theorem convArgsSymmT_of_envWfT (hW : EnvWfT E) : ConvArgsSymmT E n := by
  intro Γ hΓ r m hm hind ls ls' xs ys w w' hty hty' heqN hlen hlen' hxy
  have hlenxy := NativeFamilyProjection.convArgs_length hxy
  rw [instMtype_policyPi_of_inductiveM hW hm hind ls']
  refine convArgsT_of_allSlots []
    ((piDomsOf m.mtype).map (instantiateLevels ls')) ys xs
    (.sort (instLevel ls' (inductiveSortLevel hW hm hind)))
    (by rw [List.length_map]; exact hlen') hlenxy ?_
  intro i hi
  have hiX : i < xs.length := by omega
  obtain ⟨cxy⟩ := declaredSlotConv hW hm hind hlen hxy i hiX
  obtain ⟨hdom⟩ := declaredSlotAlign hW hΓ hm hind hty hty' heqN hlen hxy i (by omega)
  have cyx := convT_of_tyConv (ConvT.symm _ _ _ _ cxy) hdom
  simpa only [List.nil_append, List.getElem_map] using (show Nonempty _ from ⟨cyx⟩)

/-- The existing typed PER's transitivity input, now paid directly from
admission.  The final leg is transported onto the original left slot domain. -/
theorem convArgsTransT_of_envWfT (hW : EnvWfT E) : ConvArgsTransT E n := by
  intro Γ hΓ r m hm hind ls ls' ls'' xs ys zs w w' w''
    hty hty' _ heqN _ hlen hlen' hlen'' hxy hyz
  have hlenxy := NativeFamilyProjection.convArgs_length hxy
  have hlenyz := NativeFamilyProjection.convArgs_length hyz
  rw [instMtype_policyPi_of_inductiveM hW hm hind ls]
  refine convArgsT_of_allSlots []
    ((piDomsOf m.mtype).map (instantiateLevels ls)) xs zs
    (.sort (instLevel ls (inductiveSortLevel hW hm hind)))
    (by rw [List.length_map]; exact hlen) (by omega) ?_
  intro i hi
  obtain ⟨cxy⟩ := declaredSlotConv hW hm hind hlen hxy i hi
  obtain ⟨cyz⟩ := declaredSlotConv hW hm hind hlen' hyz i (by omega)
  obtain ⟨hdom⟩ := declaredSlotAlign hW hΓ hm hind hty hty' heqN hlen hxy i (by omega)
  have cxz := ConvT.trans _ _ _ _ _ cxy
    (convT_of_tyConv cyz (TyConvT.symmT hdom))
  simpa only [List.nil_append, List.getElem_map] using (show Nonempty _ from ⟨cxz⟩)

/-- All five PER components at all compacts.  This is the landed `typedPER`
consumer with its two family inputs constructed above; no Π-injectivity input
appears in the theorem or in either input producer. -/
theorem typedPER_of_envWfT {R : Readback}
    (hL : ReadbackLaws E R) (hNU : NormalUniqueR R) (hW : EnvWfT E) :
    ∀ k : Nat,
      (∀ c : CptT, sizeOf c ≤ k → SymmTyAt R E n c ∧ TransTyAt R E n c) ∧
      (∀ a u : CptT, sizeOf a + sizeOf u ≤ k →
        IrrelAt R E n a u ∧ SymmTmAt R E n a u ∧ TransTmAt R E n a u) :=
  typedPER hL hNU hW (convArgsSymmT_of_envWfT hW) (convArgsTransT_of_envWfT hW)

/-! Erasing all spine compacts is not automatically compatible with the landed
typed-PER interface.  Distinct demand sets can merge, activating a previously
incompatible codomain step.  This is a counterexample to the typing-preservation
adapter only; it does not rule out another fundamental-lemma formulation. -/

def distinctGuardValue : CptT := .lam [([.spine 0 []], .sort)]
def distinctGuardType : CptT :=
  .pi .sort [([.spine 0 []], .sort), ([.spine 1 []], .prop)]
def collapsedGuardValue : CptT := .lam [([.bot], .sort)]
def collapsedGuardType : CptT := .pi .sort [([.bot], .sort), ([.bot], .prop)]

/-- Before the two spine demands are identified, only the first codomain step
is compatible, and that step supplies the strict typing's required coverage. -/
theorem distinctGuard_typed (E : ResolvedEnv) :
    CTyS E distinctGuardValue distinctGuardType := by
  unfold distinctGuardValue distinctGuardType
  rw [CTyS]
  refine Or.inr ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · intro h
    cases h with
    | pi _ hg => exact not_isPropCT_sort E (hg ([.spine 0 []], .sort) (by simp))
  · intro s hs v hv
    have es := List.mem_singleton.mp hs
    subst s
    have ev := List.mem_singleton.mp hv
    subst v
    rw [CTyS]
    exact Or.inr (.spine 0 [])
  · intro s hs t ht hc
    have es := List.mem_singleton.mp hs
    subst s
    rcases List.mem_cons.mp ht with et | ht
    · subst t
      rw [CTyS]
      exact Or.inr .sort
    · have et := List.mem_singleton.mp ht
      subst t
      have hbad := hc (.spine 1 []) (by simp)
      simp at hbad
  · intro s hs
    have es := List.mem_singleton.mp hs
    subst s
    exact Or.inr ⟨([.spine 0 []], .sort), by simp, fun _ hv => hv⟩

/-- After both demand spines become `bot`, the second codomain step also
matches.  It would require `sort : prop`, which strict typing refutes. -/
theorem collapsedGuard_not_typed (E : ResolvedEnv) :
    ¬ CTyS E collapsedGuardValue collapsedGuardType := by
  intro h
  change CTyS E (.lam [([.bot], .sort)])
    (.pi .sort [([.bot], .sort), ([.bot], .prop)]) at h
  rcases ctyS_pi_inv h with hzero | ⟨f, hf, _, _, hcod, _⟩
  · exact CptT.noConfusion hzero
  · injection hf with hf
    subst f
    have hbad := hcod ([.bot], .sort) (by simp)
      ([.bot], .prop) (by simp) (fun _ hv => hv)
    rcases ctyS_prop_inv hbad with hzero | hprop
    · exact CptT.noConfusion hzero
    · exact not_isPropCT_sort E hprop

/-- Any compact map with these two literal images fails the general `CTyS`
preservation law needed to reuse typed irrelevance directly after erasure. -/
theorem not_ctyS_preserved_of_guard_collapse (E : ResolvedEnv)
    (erase : CptT → CptT)
    (hv : erase distinctGuardValue = collapsedGuardValue)
    (ha : erase distinctGuardType = collapsedGuardType) :
    ¬ (∀ u a, CTyS E u a → CTyS E (erase u) (erase a)) := by
  intro h
  have hbad := h _ _ (distinctGuard_typed E)
  rw [hv, ha] at hbad
  exact collapsedGuard_not_typed E hbad

-- BEGIN RCIC_PI_CYCLE_RESTATEMENT_ROOTS
#print axioms convArgsT_of_allSlots
#print axioms declaredSlotConv
#print axioms declaredSlotAlign
#print axioms convArgsSymmT_of_envWfT
#print axioms convArgsTransT_of_envWfT
#print axioms typedPER_of_envWfT
#print axioms distinctGuardValue
#print axioms distinctGuardType
#print axioms collapsedGuardValue
#print axioms collapsedGuardType
#print axioms distinctGuard_typed
#print axioms collapsedGuard_not_typed
#print axioms not_ctyS_preserved_of_guard_collapse
-- END RCIC_PI_CYCLE_RESTATEMENT_ROOTS

end Rcic.Declarative.NativeValleys.PiCycleAudit
