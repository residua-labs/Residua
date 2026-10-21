import rcic.RcicNativeTypedModelRelS
import rcic.RcicIotaSRRowsCtor

/-!
# RcicNativeTypedModelTel — the declared telescope's conversion algebra, and the boundary of the
#7721 port (kernel-checked)

The 2.2 plan ports #7721's `RcicNativePiCycleRestatement` (landed on main after this branch's
base; the text is ported, not imported) from inductive heads to **every** member and from
saturated spines to available prefixes, paying the level premises from the amended clause
(item 2.1) instead of `native_level_facts`.

**The plan's load-bearing length lemma is refuted, by witness** (`convArgsT_beyondTelescope`,
`not_convArgsSymmS_cexEnvP`): `ConvArgsT`'s `cons` walks a *syntactic* `.pi`, and after one
step the type is `instantiate0 f B` — the declared Π-tail with the argument substituted for
its variable.  When the tail is a bare variable (`∀ (x : Prop), x`) and the argument is
Π-headed, the walk continues **past the declared telescope** (`xs.length > (piDomsOf m.mtype).length`),
so `convArgsT_length_le_piDoms` is false, and with it the unbounded `ConvArgsSymmS`/`ConvArgsTransS`
(item 2.1's restatement): a β-redex convertible to the Π-headed argument at `Prop` has no
`ConvArgsT` on the flipped side, because its substituted tail is an `.app` — not syntactically
a Π.  So `EnvWfT E → ConvArgsSymmS E n` is refuted at the one-axiom environment `cexEnvP`
(`not_convArgsSymmS_cexEnvP`), and every plan item that drops `hCAs`/`hCAt` from signatures in
favour of `EnvWfT` alone (the 5 `*_wf` corollaries, the Fund/FundStrong drops) is unprovable
**as stated**: the spine clause does not record the telescope bound on `xs`.

**The exact restatement** (§2–§5, all kernel-checked): the same slot algebra with the telescope
bound `xs.length ≤ (piDomsOf m.mtype).length` as an explicit premise — `ConvArgsSymmTel` /
`ConvArgsTransTel` — paid from `EnvWfT` alone (`convArgsSymmTel_of_envWfT`,
`convArgsTransTel_of_envWfT`), by #7721's route generalised from saturation to prefixes
(`convArgsT_of_allSlotsS` assembles the flipped spine at any available prefix).  The premise the
amended clause can supply at a family reading is the saturation conditional; recording the bound
for arbitrary spines is a clause change (a cc/architect ruling, reported; not done here).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.FamModelLRSAudit

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-! ### §1 — the boundary, kernel-checked -/

/-- The member of the counterexample: the axiom `∀ (x : Prop), x`, whose Π-tail is a bare
    variable. -/
def cexPolyAxiomType : Expr Nat := .pi (.sort .zero) (.bvar 0)
def cexMemberP : CheckedMember := ⟨.axiomM, 0, cexPolyAxiomType, none⟩
def cexEnvP : ResolvedEnv := extendEnv emptyEnv 0 cexMemberP

/-- A proposition (an argument of the axiom) that is Π-headed. -/
def cexPiProp : Expr Nat := .pi (.sort .zero) (.pi (.sort .zero) (.bvar 0))

/-- Its β-redex: convertible to `cexPiProp` at `Prop`, but not Π-headed. -/
def cexBetaHead : Expr Nat := .app (.lam (.sort .zero) (.bvar 0)) cexPiProp

theorem eqN_imax_succ_zero_zero : eqN (.imax (.succ .zero) .zero) .zero := by
  intro ρ; simp [eval]

theorem eqN_imax_succ_imax_succ_zero_zero :
    eqN (.imax (.succ .zero) (.imax (.succ .zero) .zero)) .zero := by
  intro ρ; simp [eval]

def cexPolyAxiomType_sortTypedEmpty {n : Nat} :
    HasTyT emptyEnv n [] cexPolyAxiomType (.sort .zero) :=
  .conv [] cexPolyAxiomType (.sort (.imax (.succ .zero) .zero)) (.sort .zero)
    (.succ (.imax (.succ .zero) .zero))
    (.pi [] (.sort .zero) (.succ .zero) (.bvar 0) .zero (.sort [] .zero)
      (.bvar (.assumption (.sort .zero) :: []) 0 (.sort .zero) rfl))
    (.sorts [] (.imax (.succ .zero) .zero) .zero eqN_imax_succ_zero_zero)

def cexPiProp_sortTypedEmpty {n : Nat} :
    HasTyT emptyEnv n [] cexPiProp (.sort .zero) :=
  .conv [] cexPiProp (.sort (.imax (.succ .zero) (.imax (.succ .zero) .zero)))
    (.sort .zero) (.succ (.imax (.succ .zero) (.imax (.succ .zero) .zero)))
    (.pi [] (.sort .zero) (.succ .zero) (.pi (.sort .zero) (.bvar 0))
      (.imax (.succ .zero) .zero) (.sort [] .zero)
      (.pi (.assumption (.sort .zero) :: []) (.sort .zero) (.succ .zero) (.bvar 0) .zero
        (.sort _ .zero)
        (.bvar (.assumption (.sort .zero) :: .assumption (.sort .zero) :: []) 0 (.sort .zero)
          rfl)))
    (.sorts [] (.imax (.succ .zero) (.imax (.succ .zero) .zero)) .zero
      eqN_imax_succ_imax_succ_zero_zero)

def cexEmptyExt : ∀ r m, emptyEnv.members r = some m → cexEnvP.members r = some m := by
  intro r m hm
  simp [emptyEnv] at hm

def cexPolyAxiomType_sortTyped {n : Nat} :
    HasTyT cexEnvP n [] cexPolyAxiomType (.sort .zero) :=
  hasTyTExt cexEmptyExt cexPolyAxiomType_sortTypedEmpty

def cexPiProp_sortTyped {n : Nat} :
    HasTyT cexEnvP n [] cexPiProp (.sort .zero) :=
  hasTyTExt cexEmptyExt cexPiProp_sortTypedEmpty

def envWfT_cexEnvP : EnvWfT cexEnvP :=
  .axiom emptyEnv 0 cexPolyAxiomType .zero .empty (by simp [emptyEnv])
    cexPolyAxiomType_sortTypedEmpty
    (by intro k; simp [cexPolyAxiomType, lift])
    (by simp [cexPolyAxiomType, exprLevelsBounded, levelBounded])

theorem cexEnvP_members : cexEnvP.members 0 = some cexMemberP := by
  simp [cexEnvP, extendEnv]

/-- The β step of the counterexample: at `Prop`, the redex converts to the Π-headed argument. -/
def convT_cexBetaHead {n : Nat} :
    ConvT cexEnvP n [] cexBetaHead cexPiProp (.sort .zero) :=
  .beta [] (.sort .zero) (.bvar 0) cexPiProp (.sort .zero) (.succ .zero)
    (.sort [] .zero)
    (.bvar (.assumption (.sort .zero) :: []) 0 (.sort .zero) rfl)
    cexPiProp_sortTyped

theorem instLvls_nil_cexMemberP :
    instantiateLevels [] cexMemberP.mtype = cexPolyAxiomType := by
  simp [cexMemberP, instantiateLevels_nil]

/-- **The walk past the telescope**: two arguments against the one-domain telescope of
    `∀ (x : Prop), x` — the second slot sits at the Π-headed first argument, substituted into
    the declared tail. -/
theorem convArgsT_overlong {n : Nat} :
    ConvArgsT cexEnvP n [] (instantiateLevels [] cexMemberP.mtype)
      [cexPiProp, cexPiProp] [cexBetaHead, cexPiProp] := by
  rw [instLvls_nil_cexMemberP, cexPolyAxiomType]
  exact .cons (.sort .zero) (.bvar 0) cexPiProp cexBetaHead [cexPiProp] [cexPiProp]
    ⟨.symm [] cexBetaHead cexPiProp (.sort .zero) convT_cexBetaHead⟩
    (.cons _ _ _ _ _ _ ⟨.refl [] cexPiProp (.sort .zero) cexPiProp_sortTyped⟩ (.nil _))

/-- `convArgsT_length_le_piDoms` is false: the telescope has one domain, the walk two
    arguments. -/
theorem convArgsT_beyondTelescope (n : Nat) :
    ∃ xs xs' : List (Expr Nat),
      ConvArgsT cexEnvP n [] (instantiateLevels [] cexMemberP.mtype) xs xs' ∧
      (piDomsOf cexMemberP.mtype).length < xs.length :=
  ⟨[cexPiProp, cexPiProp], [cexBetaHead, cexPiProp], convArgsT_overlong, by
    simp [cexMemberP, piDomsOf]⟩

/-- **The unbounded `ConvArgsSymmS` is false** at a well-formed one-axiom environment: the
    flipped spine would have to continue at `instantiate0 cexBetaHead (.bvar 0) = cexBetaHead`,
    an `.app` — no `ConvArgsT` constructor fires. -/
theorem not_convArgsSymmS_cexEnvP (n : Nat) : ¬ ConvArgsSymmS cexEnvP n := by
  intro hS
  have hflipped : ConvArgsT cexEnvP n [] (instantiateLevels [] cexMemberP.mtype)
      [cexBetaHead, cexPiProp] [cexPiProp, cexPiProp] :=
    hS (ls := []) (ls' := []) (xs := [cexPiProp, cexPiProp])
      (xs' := [cexBetaHead, cexPiProp]) CtxWfT.nil cexEnvP_members trivial
      convArgsT_overlong
  rw [instLvls_nil_cexMemberP, cexPolyAxiomType] at hflipped
  cases hflipped with
  | cons _ _ _ _ _ _ _ hs' =>
      have hs'' : ConvArgsT cexEnvP n [] cexBetaHead [cexPiProp] [cexPiProp] := hs'
      rw [cexBetaHead] at hs''
      cases hs''

/-! ### §2 — the declared telescope as a `policyPi` template, at every member -/

/-- #7721's `instMtype_policyPi_of_inductiveM` without the inductive restriction: every
    member's type instantiates to its declared Π-telescope with the instantiated tail. -/
theorem instantiateLevels_mtype_policyPi (m : CheckedMember) (ls : List Level) :
    instantiateLevels ls m.mtype =
      policyPi ((piDomsOf m.mtype).map (instantiateLevels ls)) (instantiateLevels ls (piTailOf m.mtype)) := by
  have h := instantiateLevels_policyPi ls (piDomsOf m.mtype) (piTailOf m.mtype)
  rw [policyPi_piDomsOf_piTailOf m.mtype] at h
  exact h

/-! ### §3 — the prefix assembly -/

/-- #7721's `convArgsT_of_allSlots` generalised from saturation to prefixes: a spine whose
    arguments are convertible at all its slots assembles, with the leftover telescope left
    standing. -/
theorem convArgsT_of_allSlotsS (pre ds xs ys : List (Expr Nat)) (U : Expr Nat)
    (hle : xs.length ≤ ds.length) (hlen' : ys.length = xs.length)
    (hslots : ∀ i (hi : i < xs.length),
      Nonempty (ConvT E n Γ xs[i] (getElem ys i (by omega))
        (instPrefix (pre ++ xs.take i) (getElem ds i (by omega))))) :
    ConvArgsT E n Γ (instPrefix pre (policyPi ds U)) xs ys := by
  induction xs generalizing pre ds ys with
  | nil =>
      have hy : ys = [] := List.length_eq_zero.mp (by simpa using hlen')
      subst hy
      exact .nil _
  | cons x xs' ih =>
      cases ds with
      | nil => exact absurd hle (by simp)
      | cons d ds' =>
          cases ys with
          | nil => rw [List.length_cons] at hlen'; exact Nat.noConfusion hlen'
          | cons y ys' =>
              have hc := hslots 0 (Nat.succ_pos _)
              simp only [List.getElem_cons_zero, List.take_zero, List.append_nil] at hc
              have htail := ih (pre ++ [x]) ds' ys'
                (Nat.le_of_succ_le_succ hle) (Nat.succ.inj hlen') (by
                  intro i hi
                  have h := hslots (i + 1) (Nat.succ_lt_succ hi)
                  simpa only [List.getElem_cons_succ, List.take_succ_cons,
                    List.append_assoc, List.singleton_append] using h)
              show ConvArgsT E n Γ (instPrefix pre (.pi d (policyPi ds' U))) (x :: xs') (y :: ys')
              rw [instPrefix_pi]
              rw [instPrefix_snoc] at htail
              exact .cons _ _ x y xs' ys' hc htail

/-! ### §4 — the slot lemmas, with the telescope bound as a premise -/

/-- Slot projection (#7721's `declaredSlotConv` at every member, prefix-or-saturated): the
    original declared domain, before either substitution. -/
theorem declaredSlotConvS {m : CheckedMember}
    {ls : List Level} {xs ys : List (Expr Nat)}
    (hxy : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs ys)
    (i : Nat) (hi : i < xs.length) (hd : i < (piDomsOf m.mtype).length) :
    Nonempty (ConvT E n Γ xs[i] (ys[i]'(by
        have := NativeFamilyProjection.convArgs_length hxy; omega))
      (instPrefix (xs.take i) (instantiateLevels ls ((piDomsOf m.mtype)[i]'(hd)))) ) := by
  have hy : i < ys.length := by
    have := NativeFamilyProjection.convArgs_length hxy; omega
  exact convArgsT_instPrefix hxy ((piDomsOf m.mtype).map (instantiateLevels ls))
    (instantiateLevels ls (piTailOf m.mtype)) (instantiateLevels_mtype_policyPi m ls)
    i xs[i] ys[i] (instantiateLevels ls (piDomsOf m.mtype)[i])
    (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hy)
    (by rw [List.getElem?_map, List.getElem?_eq_getElem hd]; rfl)

/-- The alignment used by the family PER (#7721's `declaredSlotAlign` at every member): two
    related prefixes of the SAME declared telescope at pointwise-convertible universe lists.
    The member's own sort typing (`envWfT_mtypeSortTyped`, every member) replaces the
    inductive-head restriction; the clause's level facts (2.1) replace `native_level_facts`;
    the telescope bound replaces saturation. -/
theorem declaredSlotAlignS (hW : EnvWfT E) (hΓ : CtxWfT E n Γ) {r : Nat} {m : CheckedMember}
    (hm : E.members r = some m) {ls ls' : List Level} {xs ys : List (Expr Nat)}
    (hlen : ls.length = m.arity) (hwfL : levelsBounded n ls = true)
    (hwfR : levelsBounded n ls' = true) (heqN : eqNList ls ls')
    (hxy : ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs ys)
    (hxb : xs.length ≤ (piDomsOf m.mtype).length)
    (i : Nat) (hi : i < xs.length) :
    Nonempty (TyConvT E n Γ
      (instPrefix (xs.take i) (instantiateLevels ls ((piDomsOf m.mtype)[i]'(by omega))))
      (instPrefix (ys.take i) (instantiateLevels ls' ((piDomsOf m.mtype)[i]'(by omega))))) := by
  have hlenxy := NativeFamilyProjection.convArgs_length hxy
  have hd : i < (piDomsOf m.mtype).length := by omega
  obtain ⟨u, hmT⟩ := envWfT_mtypeSortTyped hW r m hm
  rw [← policyPi_piDomsOf_piTailOf m.mtype] at hmT
  obtain ⟨lv, hds⟩ := hasTyT_policyPi_invTS (piDomsOf m.mtype) hmT
  have hD := hds i hd
  rw [List.append_nil] at hD
  have cD := convT_instantiateLevels (envWfT_levels hW)
    (iotaLevelsT_of_envWfT hW) heqN hwfL hwfR hlen hD
  rw [instLvlsCtx_policyPrefixContext] at cD
  have cDΓ := convT_relocateN (Γ := Γ) cD
  obtain ⟨hctx⟩ := ctxWfT_telescope hW hΓ hwfL hlen
    (piDomsOf m.mtype) lv hds i (Nat.le_of_lt hd)
  have hright := (convEnds hW hctx cDΓ).2.1
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
    (fun j hj => declaredSlotConvS hxy j (by omega) (by omega))
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
      Nat.min_eq_left (Nat.le_of_lt hd), hxTake])
    (by rw [hxTake, hyTake]) hctx cDΓ hright hargs
    (fun j hj => (convEnds hW hΓ (hargs j hj)).1)
  change ConvT E n Γ _ _ (instPrefix (xs.take i) (.sort (instLevel ls (lv i)))) at hconv
  rw [instPrefix_sort] at hconv
  exact ⟨.of _ _ _ _ hconv⟩

/-! ### §5 — the bounded PER inputs, paid from `EnvWfT` -/

/-- The exact restatement of the 2.1 premise with the telescope bound recorded. -/
def ConvArgsSymmTel (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}, E.members r = some m →
    ∀ {ls ls' : List Level} {xs xs' : List (Expr Nat)}, ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → eqNList ls ls' →
    xs.length ≤ (piDomsOf m.mtype).length →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' →
    ConvArgsT E n Γ (instantiateLevels ls' m.mtype) xs' xs

def ConvArgsTransTel (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}, E.members r = some m →
    ∀ {ls ls' ls'' : List Level} {xs xs' xs'' : List (Expr Nat)}, ls.length = m.arity →
    levelsBounded n ls = true → levelsBounded n ls' = true → levelsBounded n ls'' = true →
    eqNList ls ls' → eqNList ls' ls'' → xs.length ≤ (piDomsOf m.mtype).length →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs' →
    ConvArgsT E n Γ (instantiateLevels ls' m.mtype) xs' xs'' →
    ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs''

/-- The bounded inputs are paid from admission alone — #7721's route at every member and every
    available prefix. -/
theorem convArgsSymmTel_of_envWfT (hW : EnvWfT E) : ConvArgsSymmTel E n := by
  intro Γ hΓ r m hm ls ls' xs xs' hlen hwfL hwfR heqN hxb hxy
  have hlenxy := NativeFamilyProjection.convArgs_length hxy
  rw [instantiateLevels_mtype_policyPi]
  refine convArgsT_of_allSlotsS [] ((piDomsOf m.mtype).map (instantiateLevels ls')) xs' xs
    (instantiateLevels ls' (piTailOf m.mtype))
    (by rw [List.length_map]; omega) hlenxy ?_
  intro i hi
  have hiX : i < xs.length := by omega
  obtain ⟨cxy⟩ := declaredSlotConvS hxy i hiX (by omega)
  obtain ⟨hdom⟩ := declaredSlotAlignS hW hΓ hm hlen hwfL hwfR heqN hxy hxb i hiX
  have cyx := convT_of_tyConv (ConvT.symm _ _ _ _ cxy) hdom
  simpa only [List.nil_append, List.getElem_map] using (show Nonempty _ from ⟨cyx⟩)

theorem convArgsTransTel_of_envWfT (hW : EnvWfT E) : ConvArgsTransTel E n := by
  intro Γ hΓ r m hm ls ls' ls'' xs xs' xs'' hlen hwfL hwfR hwfR'' heqN heqN' hxb hxy hyz
  have hlenxy := NativeFamilyProjection.convArgs_length hxy
  have hlenyz := NativeFamilyProjection.convArgs_length hyz
  rw [instantiateLevels_mtype_policyPi]
  refine convArgsT_of_allSlotsS [] ((piDomsOf m.mtype).map (instantiateLevels ls)) xs xs''
    (instantiateLevels ls (piTailOf m.mtype))
    (by rw [List.length_map]; omega) (by omega) ?_
  intro i hi
  obtain ⟨cxy⟩ := declaredSlotConvS hxy i hi (by omega)
  obtain ⟨cyz⟩ := declaredSlotConvS hyz i (by omega) (by omega)
  obtain ⟨hdom⟩ := declaredSlotAlignS hW hΓ hm hlen hwfL hwfR heqN hxy hxb i hi
  have cxz := ConvT.trans _ _ _ _ _ cxy
    (convT_of_tyConv cyz (TyConvT.symmT hdom))
  simpa only [List.nil_append, List.getElem_map] using (show Nonempty _ from ⟨cxz⟩)

-- BEGIN GLM FUND TEL ROOTS
#print axioms cexPolyAxiomType
#print axioms cexMemberP
#print axioms cexEnvP
#print axioms cexPiProp
#print axioms cexBetaHead
#print axioms eqN_imax_succ_zero_zero
#print axioms eqN_imax_succ_imax_succ_zero_zero
#print axioms cexPolyAxiomType_sortTypedEmpty
#print axioms cexPiProp_sortTypedEmpty
#print axioms cexEmptyExt
#print axioms cexPolyAxiomType_sortTyped
#print axioms cexPiProp_sortTyped
#print axioms envWfT_cexEnvP
#print axioms cexEnvP_members
#print axioms convT_cexBetaHead
#print axioms instLvls_nil_cexMemberP
#print axioms convArgsT_overlong
#print axioms convArgsT_beyondTelescope
#print axioms not_convArgsSymmS_cexEnvP
#print axioms instantiateLevels_mtype_policyPi
#print axioms convArgsT_of_allSlotsS
#print axioms declaredSlotConvS
#print axioms declaredSlotAlignS
#print axioms ConvArgsSymmTel
#print axioms ConvArgsTransTel
#print axioms convArgsSymmTel_of_envWfT
#print axioms convArgsTransTel_of_envWfT
-- END GLM FUND TEL ROOTS

end Rcic.Declarative.NativeValleys.TypedModelAudit
