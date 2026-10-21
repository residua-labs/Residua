import rcic.RcicIotaSRRowsLemmas
import rcic.RcicTypedRowsWf
import rcic.RcicTypedConv
import rcic.RcicTypedValidity
import rcic.RcicTypedLevelsCongr
import rcic.RcicTypedInst0Congr
import rcic.RcicParRedT
import rcic.RcicParRedSRTyped
import rcic.RcicTypedSubst
import rcic.RcicDT0709EnvWf

/-!
# piece G — `famAppRow` modulo the relevant-slot port (spec §7.4)

The left-instantiation construction of
`research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md` §7.4, stated as a
reduction theorem: `TypedRowsWf.famAppRow`'s conclusion is built from

* **`PiRowField`** — the Π row's exact field type, carried as a hypothesis.
  It is consumed twice per slot (domain chain for the Prop-slot transport
  and the right-endpoint move, codomain chain for the residual update), and
  once per side inside the refactored `hasTyT_spineInv_rows` that derives
  the argument typings from `hm` + `hty` (+ the right application typing
  transported along `h`);
* **`FamAppSaturation`** — piece E's supply, telescope data only: both
  instantiated stored types decompose as `policyPi` telescopes, the
  level-list relation keeps `eqNList`, and the three length facts witness
  §7.2's exact saturation (sort–Π separation: the walk cannot be formed
  unless domain and argument lists advance in lockstep);
* **`RelevantSlotConv`** — the ONLY remaining comparison premise, stated
  and not proved: at a slot whose left-instantiated domain is sorted away
  from Prop (`u ≠ .zero` on the regularity classifier), the native `ConvT`
  between the two arguments at that left domain exists. Prop slots
  (`u = .zero`) are discharged inside the walk by `ConvT.irr` — no port.

The walk `convArgsT_of_piRow_walk` is §7.4's recursion and does the residual
update itself: at each slot it applies `hpi` to the CURRENT residual chain
`TyConvT Γ (instPrefix pre (policyPi ds U)) (instPrefix pre' (policyPi ds' U'))`,
takes the codomain chain `cB`, and advances the residual by dependent
substitution congruence — `convT_inst0_sortCongr` along the slot's `ConvT`
for the left codomain, `tyConvT_subst0_of_envWfT` on `cB` for the right —
recursing on `instPrefix (pre ++ [f])` vs `instPrefix (pre' ++ [f'])`. The
slot-0 residual is built from `eqNList` + member typing +
`convT_instantiateLevels` (level-list congruence), not assumed.

`closure_claim = 0`. Nothing here asserts the rows hold; the theorem is the
conditional construction only.
-/

namespace Rcic.Declarative

/-- §7.4's remaining premise — the native argument comparison at each
    RELEVANT slot, indexed over the suffix the walk is at: `as`/`as'` are the
    remaining left/right argument lists and `ds` the remaining left stored
    domains, `pre` the already-consumed left prefix. The `getElem?` guards pin
    the obligation to actual spine slots (outside the lists the premises are
    false and the quantifier is vacuous); `pre ++ as.take i` is the consumed
    prefix at slot `i`, so the comparison is at the left-instantiated domain
    `instPrefix (pre ++ as.take i) d`. -/
def RelevantSlotConv (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (pre ds as as' : List (Expr Nat)) : Prop :=
  ∀ (i : Nat) (x x' d : Expr Nat) (u : Level),
    as[i]? = some x → as'[i]? = some x' → ds[i]? = some d →
    HasTyT E n Γ (instPrefix (pre ++ as.take i) d) (.sort u) → u ≠ .zero →
    Nonempty (ConvT E n Γ x x' (instPrefix (pre ++ as.take i) d))

/-- Per-slot argument typings in the same suffix-indexed shape — what
    §7.1's spine inversion hands the walk (per side). `HasTyT` is
    data-carrying, so this sits in `Type`. -/
def ArgTypings (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (pre ds as : List (Expr Nat)) : Type :=
  ∀ (i : Nat) (x d : Expr Nat),
    as[i]? = some x → ds[i]? = some d →
    HasTyT E n Γ x (instPrefix (pre ++ as.take i) d)

/-- Tail-step `ArgTypings`: the index shift `i ↦ i + 1` and the prefix
    append are all bookkeeping. (`def`, not `theorem`: `ArgTypings` is
    data, not Prop.) -/
def argTypings_tail {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {pre : List (Expr Nat)} {f d : Expr Nat} {as ds : List (Expr Nat)}
    (h : ArgTypings E n Γ pre (d :: ds) (f :: as)) :
    ArgTypings E n Γ (pre ++ [f]) ds as := by
  intro i x d' hx hd'
  have hx' : (f :: as)[i + 1]? = some x := by
    rw [List.getElem?_cons_succ]; exact hx
  have hd'' : (d :: ds)[i + 1]? = some d' := by
    rw [List.getElem?_cons_succ]; exact hd'
  have hty := h (i + 1) x d' hx' hd''
  have heq : (pre ++ [f]) ++ as.take i = pre ++ (f :: as).take (i + 1) := by
    rw [List.append_assoc, List.take_succ_cons, List.singleton_append]
  rwa [heq]

/-- The port at a slot is the port at the tail's slot 0 with the consumed
    prefix extended — the index shift `i ↦ i + 1` is all bookkeeping. -/
theorem relevantSlotConv_tail {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {pre : List (Expr Nat)} {d f f' : Expr Nat}
    {ds fs fs' : List (Expr Nat)}
    (h : RelevantSlotConv E n Γ pre (d :: ds) (f :: fs) (f' :: fs')) :
    RelevantSlotConv E n Γ (pre ++ [f]) ds fs fs' := by
  intro i x x' dd u hx hx' hd hdT hu
  have heq : (pre ++ [f]) ++ fs.take i = pre ++ (f :: fs).take (i + 1) := by
    rw [List.append_assoc, List.take_succ_cons, List.singleton_append]
  rw [heq] at hdT
  have hconv := h (i + 1) x x' dd u
    (by rwa [List.getElem?_cons_succ])
    (by rwa [List.getElem?_cons_succ])
    (by rwa [List.getElem?_cons_succ])
    hdT hu
  rwa [heq]

/-- the chain fold: a `TyConvT` chain's right endpoint is sort-typed,
    seeded by the left endpoint's. Each `.of` leg's endpoint typing comes
    from `endpoints3_of_envWfT` (whose `SubstLetT`/`ConstsRightDataT` debts
    are discharged from `hW`). Used to type the right spine of `h` so the
    right spine inversion can run. -/
def tyConvT_rhsSort (hW : EnvWfT E) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) :
    {A B : Expr Nat} → TyConvT E n Γ A B →
    (Σ' w, HasTyT E n Γ A (.sort w)) → Σ' w, HasTyT E n Γ B (.sort w)
  | _, _, .refl _ _, seed => seed
  | _, _, .of _ _ _ u c, _ =>
      ⟨u, (endpoints3_of_envWfT hW (substLetT_of_envWfT hW)
        (constsRightDataT_of_envWfT hW) hΓ c).2.1⟩
  | _, _, .trans _ _ _ _ c₁ c₂, seed =>
      tyConvT_rhsSort hW hΓ c₂ (tyConvT_rhsSort hW hΓ c₁ seed)

/-- §7.4's walk. The residual chain is the ACCUMULATOR: at each slot `hpi`
    peels the current residual's domain/codomain conversions, the sort
    classifier comes from the left residual's Π-typing (regularity,
    `hasTyTInv_pi`), the right argument is moved to the left domain along
    `cD.symmT`, `hconv` is `ConvT.irr` at Prop slots and `hport` otherwise,
    and the residual is updated by dependent substitution congruence:
    `convT_inst0_sortCongr` on the LEFT codomain along `hconv` (the body is
    already typed under the left binder, so no context transport is needed)
    composed with `tyConvT_subst0_of_envWfT` of the codomain chain at the
    right argument. The left residual's sort-typing is maintained alongside
    (`hasTyT_subst0S`) — it is what produces the next slot's classifier. -/
def convArgsT_of_piRow_walk
    {n : Nat} (hpi : PiRowField E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {U U' : Expr Nat} :
    (pre pre' as as' ds ds' : List (Expr Nat)) →
    as.length = as'.length → ds.length = as.length → ds'.length = as'.length →
    TyConvT E n Γ (instPrefix pre (policyPi ds U)) (instPrefix pre' (policyPi ds' U')) →
    (Σ' s, HasTyT E n Γ (instPrefix pre (policyPi ds U)) (.sort s)) →
    ArgTypings E n Γ pre ds as → ArgTypings E n Γ pre' ds' as' →
    RelevantSlotConv E n Γ pre ds as as' →
    ConvArgsT E n Γ (instPrefix pre (policyPi ds U)) as as'
  | _, _, [], [], _, _, _, _, _, _, _, _, _, _ => ConvArgsT.nil _
  | _, _, [], _ :: _, _, _, haa, _, _, _, _, _, _, _ => by
      rw [List.length_nil, List.length_cons] at haa; exact Nat.noConfusion haa
  | _, _, _ :: _, [], _, _, haa, _, _, _, _, _, _, _ => by
      rw [List.length_cons, List.length_nil] at haa; exact Nat.noConfusion haa
  | _, _, _ :: _, _ :: _, [], _, _, hlen, _, _, _, _, _, _ => by
      rw [List.length_nil, List.length_cons] at hlen; exact Nat.noConfusion hlen
  | _, _, _ :: _, _ :: _, _ :: _, [], _, _, hlen', _, _, _, _, _ => by
      rw [List.length_nil, List.length_cons] at hlen'; exact Nat.noConfusion hlen'
  | pre, pre', f :: fs, f' :: fs', d :: ds, d' :: ds', haa, hlen, hlen',
      res, resL, hL, hR, hport => by
      have hcl := envClosed_of_envWfT hW
      have hinst := envMembersSubstStable_of_envWfT hW
      have hπ : instPrefix pre (policyPi (d :: ds) U)
          = .pi (instPrefix pre d) (instTel pre (policyPi ds U)) :=
        instPrefix_pi _ _ _
      have hπ' : instPrefix pre' (policyPi (d' :: ds') U')
          = .pi (instPrefix pre' d') (instTel pre' (policyPi ds' U')) :=
        instPrefix_pi _ _ _
      rw [hπ, hπ'] at res
      obtain ⟨⟨cD⟩, ⟨cB⟩⟩ := hpi hΓ res
      obtain ⟨sL, resLw⟩ := resL
      rw [hπ] at resLw
      obtain ⟨u, v, hA, hC, _⟩ := hasTyTInv_pi resLw rfl
      have h0 : pre ++ (f :: fs).take 0 = pre := by simp
      have h0' : pre' ++ (f' :: fs').take 0 = pre' := by simp
      have hl : HasTyT E n Γ f (instPrefix pre d) := by
        have hty := hL 0 f d (by simp) (by simp)
        rwa [h0] at hty
      have hr : HasTyT E n Γ f' (instPrefix pre' d') := by
        have hty := hR 0 f' d' (by simp) (by simp)
        rwa [h0'] at hty
      have hv' : HasTyT E n Γ f' (instPrefix pre d) :=
        hasTyT_of_tyConvT hr cD.symmT
      obtain ⟨c⟩ : Nonempty (ConvT E n Γ f f' (instPrefix pre d)) := by
        by_cases hu : u = .zero
        · subst hu; exact ⟨.irr _ _ _ _ hA hl hv'⟩
        · have hcv0 := hport 0 f f' d u (by simp) (by simp) (by simp)
              (by rw [h0]; exact hA) hu
          rwa [h0] at hcv0
      have sL : TyConvT E n Γ
          (instantiate0 f (instTel pre (policyPi ds U)))
          (instantiate0 f' (instTel pre (policyPi ds U))) :=
        .of _ _ _ v (convT_inst0_sortCongr hA hC hl hv' c)
      have sR : TyConvT E n Γ
          (instantiate0 f' (instTel pre (policyPi ds U)))
          (instantiate0 f' (instTel pre' (policyPi ds' U'))) :=
        tyConvT_subst0_of_envWfT hW hv' cB
      have res' : TyConvT E n Γ
          (instPrefix (pre ++ [f]) (policyPi ds U))
          (instPrefix (pre' ++ [f']) (policyPi ds' U')) := by
        rw [instPrefix_snoc, instPrefix_snoc]
        exact .trans _ _ _ _ sL sR
      have resL' : Σ' s, HasTyT E n Γ
          (instPrefix (pre ++ [f]) (policyPi ds U)) (.sort s) := by
        refine ⟨v, ?_⟩
        rw [instPrefix_snoc]
        exact hasTyT_subst0S (envClosed_of_envWfT hW)
          (envMembersSubstStable_of_envWfT hW) hC hl
      have htail := convArgsT_of_piRow_walk hpi hW hΓ
        (pre ++ [f]) (pre' ++ [f']) fs fs' ds ds'
        (Nat.succ.inj haa) (Nat.succ.inj hlen) (Nat.succ.inj hlen')
        res' resL' (argTypings_tail hL) (argTypings_tail hR)
        (relevantSlotConv_tail hport)
      rw [instPrefix_snoc] at htail
      rw [hπ]
      exact .cons _ _ _ _ _ _ ⟨c⟩ htail

/-- Piece E's saturation package — telescope and arity data only (in `Type`:
    it carries the domain lists). All PROOF content of the walk — the
    residual chain, the per-slot argument typings, the domain sort
    classifiers — is produced inside `convArgsT_of_piRow_walk` from `hpi`,
    `hm`, `hty`, and `h`. -/
structure FamAppSaturation (E : ResolvedEnv) (r : Nat) (m : CheckedMember)
    (ls ls' : List Level) (xs xs' : List (Expr Nat)) : Type where
  /-- left stored-type telescope domains -/
  doms : List (Expr Nat)
  /-- right stored-type telescope domains -/
  doms' : List (Expr Nat)
  /-- left stored-type telescope body -/
  U : Expr Nat
  /-- right stored-type telescope body -/
  U' : Expr Nat
  /-- the left instantiated stored type decomposes as a `policyPi` telescope -/
  telL : instantiateLevels ls m.mtype = policyPi doms U
  /-- the right instantiated stored type decomposes as a `policyPi` telescope -/
  telR : instantiateLevels ls' m.mtype = policyPi doms' U'
  /-- the level-list relation the head conversion determines -/
  eqN : eqNList ls ls'
  /-- both instantiations of the same `m.mtype` telescope have the same arity -/
  lenDD : doms.length = doms'.length
  /-- the left spine is fully applied (§7.2's arity check) -/
  lenXD : doms.length = xs.length
  /-- the right spine is fully applied -/
  lenXD' : doms'.length = xs'.length

/-- THE §7.4 REDUCTION: `famAppRow`'s exact conclusion from `piRow` (as the
    standalone `PiRowField`), piece-E saturation, and the `RelevantSlotConv`
    port — the port the only remaining premise.

    The four `famAppRow` premises are consumed genuinely: `hm` drives member
    typing (`envWfT_mtypeSortTyped`, `instMtypeSort`) and both spine
    inversions; `hty` is the left spine inversion's input; `h` produces the
    right application typing (`hasTyT_of_tyConvT`) feeding the right spine
    inversion; the seed residual is level-list congruence on the member
    type's closed typing. `hind` is kept for interface fidelity — the class
    distinction belongs to the iota/ctor rows, not the left-instantiation
    argument. -/
theorem famAppRow_of_piRow_saturation_slotConv
    {n : Nat} (hpi : PiRowField E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {r : Nat} {m : CheckedMember}
    {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
    (sat : FamAppSaturation E r m ls ls' xs xs')
    (hport : RelevantSlotConv E n Γ [] sat.doms xs xs')
    (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
    (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
    (h : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')) :
    eqNList ls ls' ∧ xs.length = xs'.length ∧
      ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' := by
  have hcl := envClosed_of_envWfT hW
  have hinst := envMembersSubstStable_of_envWfT hW
  have hEL := envWfT_levels hW
  have hIL := iotaLevelsT_of_envWfT hW
  have hms := envWfT_mtypeSortTyped hW
  -- §7.1: the left spine inversion derives the per-slot left typings,
  -- the level arity, and boundedness from `hm` + `hty`.
  obtain ⟨⟨hlsl, hwfL, hargsL, _⟩⟩ :=
    hasTyT_spineInv_rows hW hpi hΓ hm sat.telL xs sat.lenXD hty
  -- the right application is sort-typed by folding `h`'s chain (each leg
  -- via `endpoints3`), then the same inversion yields the right per-slot
  -- typings (consumes `h`).
  obtain ⟨w', htyR⟩ := tyConvT_rhsSort hW hΓ h ⟨w, hty⟩
  obtain ⟨⟨hlsl', hwfR, hargsR, _⟩⟩ :=
    hasTyT_spineInv_rows hW hpi hΓ hm sat.telR xs' sat.lenXD' htyR
  -- slot-0 residual: level-list congruence on `m.mtype`'s member typing.
  obtain ⟨u₀, hT₀⟩ := hms r m hm
  have hcv0 := convT_instantiateLevels hEL hIL sat.eqN hwfL hwfR hlsl hT₀
  have hcv := convTLiftPrefix hcl Γ hcv0
  have hclm := (hcl r m hm).1
  simp only [List.append_nil, instLvlsCtx, List.map_nil,
    lift_instantiateLevels, lift] at hcv
  rw [lift_of_closed _ (hclm 0)] at hcv
  have seed : TyConvT E n Γ (instantiateLevels ls m.mtype)
      (instantiateLevels ls' m.mtype) := .of _ _ _ _ hcv
  rw [sat.telL, sat.telR] at seed
  -- slot-0 endpoint typings (left is maintained; right is unused by the
  -- walk but kept here for symmetry of the seed invariant).
  have resL0 : Σ' s, HasTyT E n Γ (instPrefix [] (policyPi sat.doms sat.U))
      (.sort s) := by
    have ⟨s₀, hs₀⟩ := instMtypeSort (Γ := Γ) hcl hms hEL hIL hm hlsl hwfL
    rw [sat.telL] at hs₀; exact ⟨s₀, hs₀⟩
  have hL0 : ArgTypings E n Γ [] sat.doms xs := hargsL
  have hR0 : ArgTypings E n Γ [] sat.doms' xs' := hargsR
  have lenAA : xs.length = xs'.length :=
    sat.lenXD.symm.trans (sat.lenDD.trans sat.lenXD')
  have conv := convArgsT_of_piRow_walk hpi hW hΓ [] [] xs xs' sat.doms
    sat.doms' lenAA sat.lenXD sat.lenXD' seed resL0 hL0 hR0 hport
  rw [sat.telL]
  exact ⟨sat.eqN, lenAA, conv⟩

end Rcic.Declarative

#print axioms Rcic.Declarative.PiRowField.of_typedRowsWf
#print axioms Rcic.Declarative.relevantSlotConv_tail
#print axioms Rcic.Declarative.argTypings_tail
#print axioms Rcic.Declarative.tyConvT_rhsSort
#print axioms Rcic.Declarative.convArgsT_of_piRow_walk
#print axioms Rcic.Declarative.famAppRow_of_piRow_saturation_slotConv
