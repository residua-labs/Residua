import rcic.RcicAnnRecSem
import rcic.RcicAnnLRFundBind
import rcic.RcicAnnIotaCorr

/-!
# M2-f (5) — a non-empty `EnvWfA.groupRec`: Nat, with its recursor

Family `10` (no parameters, no indices, sort `succ zero`), `zero` at `11` (no field),
`succ` at `12` (one `FieldA.drec []`), recursor at `13`. `groupEnvA` adds the list's
head last, so the group list is `succ` then `zero`: candidate order is `11, 12`, and
`groupRecTypeA` is the type already pinned as `pinNatRecBuiltA`. The recursor is
AnySort, so its arity is `1` and the ι spine's constant carries `[.zero]` — the level
list the sealed decide pin on `pinNatBuiltEnvA` uses. Stored type `groupRecTypeA`,
typed in `groupEnvA` at arity `1`, entered by `EnvWfA.groupRec`.

M2-f (5b) reads that same environment (`pinNatBuiltEnvA`, definitionally
`pinNatRecEnvA (iotaIfaceA pinNatBuiltEnvA)`) and discharges `EnvSemA` by
`envSemA_of_envWfA_rec`. On this main that theorem's premises are `EnvWfA`,
`PosValA`, `SmallIndexProfileA` and `PropElimOnlyA`; `NoParamsA` is no longer
one of them (M2-f (6c)). `piConvInjA_rec` takes no `hz` (any codomain since
M2-g′). The family is a Type family (`Sort 1`), so `PropElimOnlyA` holds on
the AnySort branch: `UniformProp` of its sort fails, and the motive-is-`Prop`
obligation is not demanded.

The erasure tooth (`pinNatGroupRec_derivedIota`) is `derivedIota_of_iotaFnA` applied to
`pinNatGroupRecWfA` at `rec P mz ms zero ⇝ mz`. It does not build an `IotaWitness`.

O1-a (section (7)): `False` at `20`, no constructor, its AnySort recursor at `21`, by the same
`EnvWfA.groupRec`. `PropElimOnlyA` holds by the exemption of a recursor right after its family alone
(`pinFalse_motive_not_prop`: the obligation itself fails there), and `EnvSemA` is discharged by the
same `envSemA_of_envWfA_rec`. The major arm is off at `False`'s recursor and on at Nat's, each pinned
on one β-redex major by `decide` (`pinFalse_noMajorStep`, `pinNat_majorStep`).

O1-b (section (8)): `True` at `30`, `intro` at `31`, its AnySort recursor at `32`, by the same
`EnvWfA.groupRec`. Proof irrelevance and ι make `rec M True a ≡ True : Prop` at every proof `a`
(`pinTrueConv`). Over the head step before O1-b-1 the left side stayed stuck there and `EnvSemA` failed,
with no axiom and with one (O1-b-0, README). O1-b-1's K-unit arm steps every full application of a unit
group's recursor to its minor (`pinTrue_var_kunit`, `pinTrueAx_kunit`). `PropElimOnlyA` exempts that
recursor (`pinTrue_propElim`), and `EnvSemA` holds, with no axiom and with `ax : True`
(`envSemA_pinTrue`, `envSemA_pinTrueAx`). The unit test refuses Nat, `False` and an indexed singleton
(`pinNat_notUnit`, `pinFalse_notUnit`, `pinIdx_notUnit`).

O1-c-0 (section (9)): (K-struct), one constructor whose every field is a proof, no index. `Struct` at
`50` (one non-recursive field, `Π (P : Prop), P → P`) and `Loop` at `60` (one recursive field), each
with its AnySort recursor, by the same `EnvWfA.groupRec`. `Struct` was outside this relation over the
head step before W-1 (a) (O1-c-0, README: O1-b-0's mechanism, with a field). `Loop` is outside it
whatever the head step does at the recursor: `rec M m t` is convertible to its own self-arrow
(`pinLoopConv`), and no proposition is `PropEqA`-related to its own self-arrow
(`propEqA_not_selfArrow`).

W-1 (section (10)): the struct arm. At a struct group (`structGroupA`, read off the recursor's type:
`pinStruct_struct`; not Nat's, `False`'s, `True`'s, `Loop`'s or an indexed singleton's) a recursor spine
at its major steps to the minor applied to the major's projections (`pinStructArm_var`). The projection
of a variable proof loops through one β (`pinStructProj_var_step`, `pinStructArm_proj_loop`). Since
W-1 (e) the arm is the step at a constructor major too (`pinStruct_ctor_arm`), and ι contracts there as
`main`'s does, to the minor at the constructor's field (`pinStruct_ctor_iotaFn`). So ι there is not the
head step (`pinStruct_ctor_notIotaRel`): its rule is `ConvA.structIota`. The redex is at a struct group
(`pinStruct_ctor_atStruct`), which the bridge's scope leaves out until W-1 (e-2).

W-1 (c) (section (11)): `PropElimStructA` exempts a struct group's recursor as well; it holds at
`Struct` (`pinStruct_propElimStruct`), where `EnvSemA` now holds (`envSemA_pinStruct`), and not at `Loop`
(`pinLoop_not_propElimStruct`). W-1 (d) (section (12)): `And`, a struct with two parameters, at `70`;
`EnvSemA` holds there too (`envSemA_pinAnd`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) `boundOkB`/`liftA_of_boundOkB`/`boundOkB_add` live in `RcicAnnSyntax`
    (moved up for R-NoDeltaRec-4d: `envWfA_norm*` need them below `RcicAnnRecView`). -/

/-! ## (2) the Nat members, and typing `Nat` / `zero` / `succ` -/

abbrev pinMotTyA : ExprA :=
  .pi (.const 10 []) (.succ .zero) (.sort (.param 0)) (.succ (.param 0))

abbrev pinMotSortA : Level := .imax (.succ .zero) (.succ (.param 0))

abbrev pinMzDomA : ExprA := .app (.bvar 0) (.const 11 [])

abbrev pinIhDomA : ExprA := .app (.bvar 2) (.bvar 0)

abbrev pinIhBodyA : ExprA := .app (.bvar 3) (.app (.const 12 []) (.bvar 1))

abbrev pinIhTyA : ExprA := .pi pinIhDomA (.param 0) pinIhBodyA (.param 0)

abbrev pinMsSortInnerA : Level := .imax (.param 0) (.param 0)

abbrev pinMsTyA : ExprA :=
  .pi (.const 10 []) (.succ .zero) pinIhTyA pinMsSortInnerA

abbrev pinMsSortA : Level := .imax (.succ .zero) pinMsSortInnerA

abbrev pinMajorBodyA : ExprA := .app (.bvar 3) (.bvar 0)

abbrev pinMajorSortA : Level := .imax (.succ .zero) (.param 0)

abbrev pinMajorTyA : ExprA :=
  .pi (.const 10 []) (.succ .zero) pinMajorBodyA (.param 0)

abbrev pinMsPiSortA : Level := .imax pinMsSortA pinMajorSortA

abbrev pinMsPiA : ExprA := .pi pinMsTyA pinMsSortA pinMajorTyA pinMajorSortA

abbrev pinMzPiSortA : Level := .imax (.param 0) pinMsPiSortA

abbrev pinMzPiA : ExprA := .pi pinMzDomA (.param 0) pinMsPiA pinMsPiSortA

abbrev pinRecSortA : Level := .imax pinMotSortA pinMzPiSortA

theorem pinNatRecBuiltA_shape :
    pinNatRecBuiltA = .pi pinMotTyA pinMotSortA pinMzPiA pinMzPiSortA := rfl

theorem boundOkB_pinNatRecBuiltA : boundOkB 0 pinNatRecBuiltA = true := rfl

theorem liftA_pinNatRecBuiltA (k : Nat) : liftA k 1 pinNatRecBuiltA = pinNatRecBuiltA :=
  liftA_of_boundOkB 1 k pinNatRecBuiltA
    (boundOkB_add k 0 pinNatRecBuiltA boundOkB_pinNatRecBuiltA)

def pinNatRecMemberA : CheckedMemberA :=
  ⟨.recursorM, 1, pinNatRecBuiltA, none, 0, none⟩

/-- `Nat` at `10` : `Sort 1`, in any context, at any universe arity. -/
def pinNatConstTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h : E.members 10 = some pinNatFamA) :
    HasTyA E I n Γ (.const 10 []) (.sort (.succ .zero)) :=
  .const Γ 10 [] pinNatFamA (.succ (.succ .zero)) h rfl rfl (.sort Γ (.succ .zero))

/-- `zero` at `11` : `Nat`. -/
def pinZeroConstTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h10 : E.members 10 = some pinNatFamA) (h11 : E.members 11 = some pinZeroA) :
    HasTyA E I n Γ (.const 11 []) (.const 10 []) :=
  .const Γ 11 [] pinZeroA (.succ .zero) h11 rfl rfl (pinNatConstTy h10)

/-- `succ`'s stored type inhabits `Sort (imax 1 1)`. -/
def pinSuccPiTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h10 : E.members 10 = some pinNatFamA) :
    HasTyA E I n Γ pinSuccA.mtypeA (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi Γ (.const 10 []) (.succ .zero) (.const 10 []) (.succ .zero)
    (pinNatConstTy h10)
    (pinNatConstTy (Γ := .assumption (.const 10 []) :: Γ) h10)

/-- `succ` at `12` : `Nat → Nat`. -/
def pinSuccConstTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h12 : E.members 12 = some pinSuccA) (h10 : E.members 10 = some pinNatFamA) :
    HasTyA E I n Γ (.const 12 []) pinSuccA.mtypeA :=
  .const Γ 12 [] pinSuccA (.imax (.succ .zero) (.succ .zero)) h12 rfl rfl (pinSuccPiTy h10)

def pinNatFamEnvA : ResolvedEnvA := extendEnvA emptyEnvA 10 pinNatFamA

theorem pinNatFamEnv_fam : pinNatFamEnvA.members 10 = some pinNatFamA := rfl

/-- the DerivationScope: family, then `zero`, then `succ`. -/
def pinNatGroupEnvA : ResolvedEnvA :=
  extendEnvA (extendEnvA pinNatFamEnvA 11 pinZeroA) 12 pinSuccA

theorem pinNatGroupEnv_fam : pinNatGroupEnvA.members 10 = some pinNatFamA := rfl
theorem pinNatGroupEnv_zero : pinNatGroupEnvA.members 11 = some pinZeroA := rfl
theorem pinNatGroupEnv_succ : pinNatGroupEnvA.members 12 = some pinSuccA := rfl

/-! ## (3) the family view and the two constructors -/

def pinNatFamViewA : FamViewA pinNatFamA where
  params := []
  indices := []
  sort := .succ .zero
  stored := rfl
  nparams := rfl
  profile := .inr (fun _ => Nat.succ_pos 0)

def pinNatZeroViewA (I : IotaIfaceA) :
    CtorViewA emptyEnvA I 10 pinNatFamA pinNatFamViewA pinZeroA where
  mirrors := []
  fields := []
  res := []
  stored := rfl
  mirrorsConv := .nil []
  typed := .nil [] 0 [] (.nil (.succ .zero))
  univI := fun _ _ _ _ h => absurd h (List.not_mem_nil _)
  drecD_typed := drecDTypedA_of_noDelta (fun _ h => absurd h (List.not_mem_nil _))
  normConv := ⟨.refl [] _⟩
  normTyped := ⟨_, ⟨pinNatConstTy pinNatFamEnv_fam⟩⟩
  univ := fun _ _ h => absurd h (List.not_mem_nil _)

def pinNatSuccViewA (I : IotaIfaceA) :
    CtorViewA emptyEnvA I 10 pinNatFamA pinNatFamViewA pinSuccA where
  mirrors := []
  fields := [.drec []]
  res := []
  stored := rfl
  mirrorsConv := .nil []
  typed := .drec [] 0 [] [] [] (.nil (.succ .zero)) (.nil [] 0 [] (.nil (.succ .zero)))
  univI := fun _ _ _ _ h => by cases List.mem_singleton.mp h
  drecD_typed := drecDTypedA_of_noDelta (fun _ h => by cases List.mem_singleton.mp h; trivial)
  normConv := ⟨.refl [] _⟩
  normTyped := ⟨_, ⟨pinSuccPiTy pinNatFamEnv_fam⟩⟩
  univ := fun _ _ h => by
    cases List.mem_singleton.mp h

def pinNatZeroGroupA (I : IotaIfaceA) :
    GroupCtorA I emptyEnvA 10 pinNatFamA pinNatFamViewA where
  ref := 11
  member := pinZeroA
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := fun _ => rfl
  u := .succ .zero
  hT := pinNatConstTy pinNatFamEnv_fam
  hlvl := rfl
  view := pinNatZeroViewA I
  hnorm := rfl
  hclN := fun _ => rfl
  hlvlN := rfl

def pinNatSuccGroupA (I : IotaIfaceA) :
    GroupCtorA I emptyEnvA 10 pinNatFamA pinNatFamViewA where
  ref := 12
  member := pinSuccA
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := fun _ => rfl
  u := .imax (.succ .zero) (.succ .zero)
  hT := pinSuccPiTy pinNatFamEnv_fam
  hlvl := rfl
  view := pinNatSuccViewA I
  hnorm := rfl
  hclN := fun _ => rfl
  hlvlN := rfl

/-- head added last, so this list puts `zero` at `11` and `succ` at `12`. -/
def pinNatCs (I : IotaIfaceA) : List (GroupCtorA I emptyEnvA 10 pinNatFamA pinNatFamViewA) :=
  [pinNatSuccGroupA I, pinNatZeroGroupA I]

theorem pinNatGroup_layout (I : IotaIfaceA) :
    (pinNatCs I).reverse.map GroupCtorA.ref =
      List.range' (10 + 1) (pinNatCs I).length := rfl

theorem pinNatGroup_fresh (I : IotaIfaceA) :
    GroupFreshA emptyEnvA 10 pinNatFamA ((pinNatCs I).map GroupCtorA.entry) :=
  ⟨⟨rfl, rfl⟩, rfl⟩

theorem pinNatGroupEnv_eq (I : IotaIfaceA) :
    groupEnvA emptyEnvA 10 pinNatFamA ((pinNatCs I).map GroupCtorA.entry) =
      pinNatGroupEnvA := rfl

/-! ## (4) the recursor type, typed in the DerivationScope at arity 1 -/

def pinMotTyTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h : E.members 10 = some pinNatFamA) :
    HasTyA E I n Γ pinMotTyA (.sort pinMotSortA) :=
  .pi Γ (.const 10 []) (.succ .zero) (.sort (.param 0)) (.succ (.param 0))
    (pinNatConstTy h) (.sort (.assumption (.const 10 []) :: Γ) (.param 0))

def pinNatBvarTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} (i : Nat)
    (h : lookupTypeA Γ i = some (.const 10 [])) :
    HasTyA pinNatGroupEnvA I n Γ (.bvar i) (.const 10 []) :=
  .bvar Γ i (.const 10 []) (.succ .zero) h (pinNatConstTy pinNatGroupEnv_fam)

/-- `motive a : Sort (param 0)`, with `motive` the variable `i` and `a : Nat`. -/
def pinMotAppTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} (i : Nat) (a : ExprA)
    (ha : HasTyA pinNatGroupEnvA I n Γ a (.const 10 []))
    (hm : lookupTypeA Γ i = some pinMotTyA) :
    HasTyA pinNatGroupEnvA I n Γ (.app (.bvar i) a) (.sort (.param 0)) :=
  .app Γ (.bvar i) a (.const 10 []) (.sort (.param 0))
    (.succ .zero) (.succ (.param 0)) (.succ (.param 0))
    (.sort (.assumption (.const 10 []) :: Γ) (.param 0))
    (.sort Γ (.param 0))
    (.bvar Γ i pinMotTyA pinMotSortA hm (pinMotTyTy pinNatGroupEnv_fam))
    ha

abbrev ctxMot (Γ : LCtxA) : LCtxA := .assumption pinMotTyA :: Γ
abbrev ctxMz (Γ : LCtxA) : LCtxA := .assumption pinMzDomA :: ctxMot Γ
abbrev ctxN (Γ : LCtxA) : LCtxA := .assumption (.const 10 []) :: ctxMz Γ
abbrev ctxIh (Γ : LCtxA) : LCtxA := .assumption pinIhDomA :: ctxN Γ
abbrev ctxMs (Γ : LCtxA) : LCtxA := .assumption pinMsTyA :: ctxMz Γ
abbrev ctxMajor (Γ : LCtxA) : LCtxA := .assumption (.const 10 []) :: ctxMs Γ

def pinMzDomTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA pinNatGroupEnvA I n (ctxMot Γ) pinMzDomA (.sort (.param 0)) :=
  pinMotAppTy 0 (.const 11 [])
    (pinZeroConstTy pinNatGroupEnv_fam pinNatGroupEnv_zero) rfl

def pinIhDomTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA pinNatGroupEnvA I n (ctxN Γ) pinIhDomA (.sort (.param 0)) :=
  pinMotAppTy 2 (.bvar 0) (pinNatBvarTy 0 rfl) rfl

def pinIhBodyTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA pinNatGroupEnvA I n (ctxIh Γ) pinIhBodyA (.sort (.param 0)) :=
  pinMotAppTy 3 (.app (.const 12 []) (.bvar 1))
    (pinSuccAppRaw (pinNatBvarTy 1 rfl)) rfl
  where
    pinSuccAppRaw {Γ' : LCtxA}
        (ha : HasTyA pinNatGroupEnvA I n Γ' (.bvar 1) (.const 10 [])) :
        HasTyA pinNatGroupEnvA I n Γ' (.app (.const 12 []) (.bvar 1)) (.const 10 []) :=
      .app Γ' (.const 12 []) (.bvar 1) (.const 10 []) (.const 10 [])
        (.succ .zero) (.succ .zero) (.succ .zero)
        (pinNatConstTy (Γ := .assumption (.const 10 []) :: Γ') pinNatGroupEnv_fam)
        (pinNatConstTy pinNatGroupEnv_fam)
        (pinSuccConstTy pinNatGroupEnv_succ pinNatGroupEnv_fam)
        ha

def pinIhHasTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA pinNatGroupEnvA I n (ctxN Γ) pinIhTyA (.sort pinMsSortInnerA) :=
  .pi (ctxN Γ) pinIhDomA (.param 0) pinIhBodyA (.param 0)
    (pinIhDomTy (Γ := Γ)) (pinIhBodyTy (Γ := Γ))

def pinMsHasTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA pinNatGroupEnvA I n (ctxMz Γ) pinMsTyA (.sort pinMsSortA) :=
  .pi (ctxMz Γ) (.const 10 []) (.succ .zero) pinIhTyA pinMsSortInnerA
    (pinNatConstTy pinNatGroupEnv_fam) (pinIhHasTy (Γ := Γ))

def pinMajorBodyTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA pinNatGroupEnvA I n (ctxMajor Γ) pinMajorBodyA (.sort (.param 0)) :=
  pinMotAppTy 3 (.bvar 0) (pinNatBvarTy 0 rfl) rfl

def pinMajorHasTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA pinNatGroupEnvA I n (ctxMs Γ) pinMajorTyA (.sort pinMajorSortA) :=
  .pi (ctxMs Γ) (.const 10 []) (.succ .zero) pinMajorBodyA (.param 0)
    (pinNatConstTy pinNatGroupEnv_fam) (pinMajorBodyTy (Γ := Γ))

def pinMsPiHasTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA pinNatGroupEnvA I n (ctxMz Γ) pinMsPiA (.sort pinMsPiSortA) :=
  .pi (ctxMz Γ) pinMsTyA pinMsSortA pinMajorTyA pinMajorSortA
    (pinMsHasTy (Γ := Γ)) (pinMajorHasTy (Γ := Γ))

def pinMzPiHasTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA pinNatGroupEnvA I n (ctxMot Γ) pinMzPiA (.sort pinMzPiSortA) :=
  .pi (ctxMot Γ) pinMzDomA (.param 0) pinMsPiA pinMsPiSortA
    (pinMzDomTy (Γ := Γ)) (pinMsPiHasTy (Γ := Γ))

def pinNatRecHasTy (I : IotaIfaceA) :
    HasTyA pinNatGroupEnvA I 1 [] pinNatRecBuiltA (.sort pinRecSortA) :=
  .pi [] pinMotTyA pinMotSortA pinMzPiA pinMzPiSortA
    (pinMotTyTy pinNatGroupEnv_fam) (pinMzPiHasTy (Γ := []))

theorem pinNatGroupRec_stored (I : IotaIfaceA) :
    pinNatRecMemberA.mtypeA = groupRecTypeA pinNatFamViewA (pinNatCs I) .anySort := rfl

def pinNatGroupRecA (I : IotaIfaceA) : GroupRecA I emptyEnvA 10 pinNatFamA pinNatFamViewA
    (pinNatCs I) where
  member := pinNatRecMemberA
  hcls := rfl
  hnobody := rfl
  hnp := rfl
  elim := .anySort
  harity := rfl
  stored := pinNatGroupRec_stored I
  hclT := liftA_pinNatRecBuiltA
  u := pinRecSortA
  hT := pinNatGroupEnv_eq I ▸ pinNatRecHasTy I
  hlvl := rfl

theorem pinNatRec_fresh (I : IotaIfaceA) :
    (groupEnvA emptyEnvA 10 pinNatFamA ((pinNatCs I).map GroupCtorA.entry)).members
        (10 + 1 + (pinNatCs I).length) = none := rfl

/-! ## (5) the group with its recursor, and the ι pin -/

def pinNatRecEnvA (I : IotaIfaceA) : ResolvedEnvA :=
  groupRecEnvA (pinNatCs I) (pinNatGroupRecA I)

/-- `Nat` with `zero`, `succ` and the derived recursor, by `EnvWfA.groupRec`. -/
def pinNatGroupRecWfA (I : IotaIfaceA) : EnvWfA I (pinNatRecEnvA I) :=
  .groupRec emptyEnvA 10 pinNatFamA (.succ (.succ .zero))
    .empty rfl rfl (fun _ => rfl) (.sort [] (.succ .zero)) rfl
    pinNatFamViewA (pinNatCs I) (pinNatGroup_fresh I) (pinNatGroup_layout I)
    (pinNatGroupRecA I) (pinNatRec_fresh I)

theorem pinNatRecEnvA_eq (I : IotaIfaceA) : pinNatRecEnvA I = pinNatBuiltEnvA := rfl

/-- `rec P mz ms (succ zero) ⇝ ms zero (rec P mz ms zero)` on the group-recursor
    environment. The constant carries `[.zero]`: AnySort makes the recursor's arity `1`. -/
theorem pinNatGroupRec_iota (I : IotaIfaceA) :
    iotaFnA (pinNatRecEnvA I)
        (.app (.app (.app (.app (.const 13 [.zero]) (.sort .zero)) (.sort (.succ .zero))) pinMsA)
          (.app (.const 12 []) (.const 11 []))) =
      some (.app (.app pinMsA (.const 11 []))
        (.app (.app (.app (.app (.const 13 [.zero]) (.sort .zero)) (.sort (.succ .zero))) pinMsA)
          (.const 11 []))) := by
  rw [pinNatRecEnvA_eq]
  decide

/-- `rec P mz ms zero` on this environment: `P` is `sort zero`, `mz` is `sort (succ zero)`,
    `ms` is `pinMsA`, `zero` is `const 11`. The constant carries `[.zero]`, as in the succ pin. -/
def pinNatZeroLhs : ExprA :=
  .app (.app (.app (.app (.const 13 [.zero]) (.sort .zero)) (.sort (.succ .zero))) pinMsA)
    (.const 11 [])

/-- `rec P mz ms zero ⇝ mz`. -/
theorem pinNatGroupRec_iotaZero (I : IotaIfaceA) :
    iotaFnA (pinNatRecEnvA I) pinNatZeroLhs = some (.sort (.succ .zero)) := by
  rw [pinNatRecEnvA_eq]
  decide

/-! ## (6) M2-f (5b): `EnvSemA` on this Nat environment -/

/-- the built recursor really sits at `13`. -/
theorem pinNatBuilt_recMember :
    pinNatBuiltEnvA.members 13 = some pinNatRecMemberA := rfl

theorem pinNatBuilt_recClass : pinNatRecMemberA.mclass = .recursorM := rfl

/-- every resident of `pinNatBuiltEnvA` is one of `10`–`13`. -/
theorem pinNatBuilt_mem {r : Nat} {m : CheckedMemberA}
    (hm : pinNatBuiltEnvA.members r = some m) :
    (r = 10 ∧ m = pinNatFamA) ∨ (r = 11 ∧ m = pinZeroA) ∨
      (r = 12 ∧ m = pinSuccA) ∨ (r = 13 ∧ m = pinNatRecMemberA) := by
  revert hm
  unfold pinNatBuiltEnvA
  simp only [extendEnvA, emptyEnvA]
  intro hm
  by_cases h13 : r = 13
  · subst h13
    simp only [if_pos rfl] at hm
    cases hm
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · simp only [if_neg h13] at hm
    by_cases h12 : r = 12
    · subst h12
      simp only [if_pos rfl] at hm
      cases hm
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · simp only [if_neg h12] at hm
      by_cases h11 : r = 11
      · subst h11
        simp only [if_pos rfl] at hm
        cases hm
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · simp only [if_neg h11] at hm
        by_cases h10 : r = 10
        · subst h10
          simp only [if_pos rfl] at hm
          cases hm
          exact Or.inl ⟨rfl, rfl⟩
        · simp only [if_neg h10] at hm
          cases hm

theorem pinNatBuilt_inductive {r : Nat} {m : CheckedMemberA}
    (hm : pinNatBuiltEnvA.members r = some m) (hc : m.mclass = .inductiveM) :
    r = 10 ∧ m = pinNatFamA := by
  rcases pinNatBuilt_mem hm with h | h | h | h
  · exact h
  · rcases h with ⟨_, rfl⟩
    simp [pinZeroA] at hc
  · rcases h with ⟨_, rfl⟩
    simp [pinSuccA] at hc
  · rcases h with ⟨_, rfl⟩
    simp [pinNatRecMemberA] at hc

/-- `Nat` has no parameters. -/
theorem pinNatBuilt_noParams : NoParamsA pinNatBuiltEnvA := by
  intro r m hm hc
  obtain ⟨_, rfl⟩ := pinNatBuilt_inductive hm hc
  rfl

/-- `Nat` has no index binders, so the small-index profile holds vacuously at its only family. -/
theorem pinNatBuilt_small : SmallIndexProfileA pinNatBuiltEnvA := by
  intro r m u₀ hm hc _ v hv _ _ _ _ _ _
  obtain ⟨_, rfl⟩ := pinNatBuilt_inductive hm hc
  simp [pinNatFamA, piDomLevelsA, List.drop] at hv

/-- AnySort branch: the only family is `Nat : Sort 1`, which is not `UniformProp`, so a
    Prop-elimination restriction is not demanded of its recursor. -/
theorem pinNatBuilt_propElim : PropElimOnlyA pinNatBuiltEnvA := by
  intro _ _ _ _ _ fm u₀ _ _ _ _ hfm hind hbody hup _ _ _ _
  obtain ⟨_, rfl⟩ := pinNatBuilt_inductive hfm hind
  simp [pinNatFamA, piBodyA] at hbody
  subst hbody
  have h1 : evalTotal (fun _ => 0) (.succ .zero) = 1 := rfl
  have h0 := hup (fun _ => 0)
  rw [h1] at h0
  exact Nat.noConfusion h0

/-- `Nat`'s constructors have no function-recursive field: `zero` has none, `succ`'s is directly recursive. -/
theorem pinNatBuilt_noFun : EnvNoFunA pinNatBuiltEnvA := by
  intro c cm f fm shapes hc hcl hfam hf hsh s hs j
  rcases pinNatBuilt_mem hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · simp [pinNatFamA] at hcl
  · have h : memberFamRefA pinZeroA = some 10 := rfl
    rw [h] at hfam
    cases hfam
    have h10 : pinNatBuiltEnvA.members 10 = some pinNatFamA := rfl
    rw [h10] at hf
    cases hf
    have hs0 : ctorShapesA 10 pinNatFamA.nparamsA (pinZeroA.normA.getD pinZeroA.mtypeA) = some [] := rfl
    rw [hs0] at hsh
    cases hsh
    cases hs
  · have h : memberFamRefA pinSuccA = some 10 := rfl
    rw [h] at hfam
    cases hfam
    have h10 : pinNatBuiltEnvA.members 10 = some pinNatFamA := rfl
    rw [h10] at hf
    cases hf
    have hs0 : ctorShapesA 10 pinNatFamA.nparamsA (pinSuccA.normA.getD pinSuccA.mtypeA) = some [.recursive 0] := rfl
    rw [hs0] at hsh
    cases hsh
    rcases List.mem_singleton.mp hs with rfl
    intro h
    cases h
  · simp [pinNatRecMemberA] at hcl

/-- the pin's constructors' normed types erase to the stored ones — they are the same term
    (`.drecD`-free, `normA = some mtypeA`). -/
theorem pinNatBuilt_normErase : EnvNormEraseA pinNatBuiltEnvA := by
  intro r m hm hmc T hT
  rcases pinNatBuilt_mem hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · simp [pinNatFamA] at hmc
  · cases hT; rfl
  · cases hT; rfl
  · simp [pinNatRecMemberA] at hmc

/-- That step, erased, is a derived ι on `main`. One application of `derivedIota_of_iotaFnA`
    to `pinNatGroupRecWfA`. -/
theorem pinNatGroupRec_derivedIota (I : IotaIfaceA) :
    Nonempty (DerivedIota (eraseEnv (pinNatRecEnvA I)) (erase pinNatZeroLhs)
      (erase (.sort (.succ .zero)))) :=
  derivedIota_of_iotaFnA (pinNatGroupRecWfA I) (pinNatBuilt_noFun) pinNatBuilt_normErase
    (pinNatGroupRec_iotaZero I)

def pinNatBuilt_wf : EnvWfA (iotaIfaceA pinNatBuiltEnvA) pinNatBuiltEnvA :=
  pinNatRecEnvA_eq (iotaIfaceA pinNatBuiltEnvA) ▸
    pinNatGroupRecWfA (iotaIfaceA pinNatBuiltEnvA)

theorem envSemA_pinNat (n : Nat) :
    EnvSemA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) n (fun _ => 1) :=
  envSemA_of_envWfA_rec (E := pinNatBuiltEnvA) (n := n) (ρ₀ := fun _ => 1)
    pinNatBuilt_wf posValA_one pinNatBuilt_small pinNatBuilt_propElim

theorem sortConvCharA_pinNat (n : Nat) {Γ : LCtxA} {l₁ l₂ u : Level}
    (hΓ : CtxWfA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) n Γ)
    (h : ConvA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) n Γ (.sort l₁) (.sort l₂) (.sort u)) :
    eqN l₁ l₂ :=
  sortConvCharA_rec (E := pinNatBuiltEnvA) (n := n) (ρ₀ := fun _ => 1)
    pinNatBuilt_wf posValA_one pinNatBuilt_small (propElimStructA_of_propElimOnlyA pinNatBuilt_propElim) hΓ h

theorem piConvInjA_pinNat (n : Nat) {Γ : LCtxA} {D : ExprA} {u : Level} {C : ExprA} {v : Level}
    {D' : ExprA} {u' : Level} {C' : ExprA} {v' w : Level}
    (hΓ : CtxWfA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) n Γ)
    (h : ConvA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) n Γ
      (.pi D u C v) (.pi D' u' C' v') (.sort w)) :
    eqN u u' ∧ eqN v v' ∧
      Nonempty (TyConvA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) n Γ D D') ∧
      Nonempty (TyConvA pinNatBuiltEnvA (iotaIfaceA pinNatBuiltEnvA) n
        (.assumption D :: Γ) C C') :=
  piConvInjA_rec (E := pinNatBuiltEnvA) (n := n) (ρ₀ := fun _ => 1)
    pinNatBuilt_wf posValA_one pinNatBuilt_small (propElimStructA_of_propElimOnlyA pinNatBuilt_propElim) hΓ h

/-! ## (7) O1-a: `False`, a `Prop` family without constructors, eliminating into any sort

Family `20` (no parameters, no indices, sort `zero`), no constructor, recursor at `21` (05 §3: right
after the family). The recursor is AnySort, as 05 §10 selects for a `Prop` family without constructors
(L-K1's `EliminationSelection.emptyProp`). Its group has no constructor, so ι never fires at it and the
major arm is off (`recHasCtorA`); `PropElimOnlyA` exempts it (`r = f + 1`), and the recursors' clause
relates its applications by reflection at any motive universe. -/

/-- `False` at `20` : `Sort 0`. -/
def pinFalseFamA : CheckedMemberA := ⟨.inductiveM, 0, .sort .zero, none, 0, none⟩

def pinFalseFamViewA : FamViewA pinFalseFamA where
  params := []
  indices := []
  sort := .zero
  stored := rfl
  nparams := rfl
  profile := .inl (fun _ => rfl)

def pinFalseCs (I : IotaIfaceA) : List (GroupCtorA I emptyEnvA 20 pinFalseFamA pinFalseFamViewA) := []

/-- the motive's type, `False → Sort u`. -/
abbrev pinFalseMotTyA : ExprA := .pi (.const 20 []) .zero (.sort (.param 0)) (.succ (.param 0))

abbrev pinFalseMotSortA : Level := .imax .zero (.succ (.param 0))

/-- the major and the body, `Π (t : False), motive t`, under the motive. -/
abbrev pinFalseMajorTyA : ExprA := .pi (.const 20 []) .zero (.app (.bvar 1) (.bvar 0)) (.param 0)

abbrev pinFalseMajorSortA : Level := .imax .zero (.param 0)

/-- the recursor type, `Π (motive : False → Sort u) (t : False), motive t`. -/
def pinFalseRecBuiltA : ExprA := .pi pinFalseMotTyA pinFalseMotSortA pinFalseMajorTyA pinFalseMajorSortA

theorem boundOkB_pinFalseRecBuiltA : boundOkB 0 pinFalseRecBuiltA = true := rfl

theorem liftA_pinFalseRecBuiltA (k : Nat) : liftA k 1 pinFalseRecBuiltA = pinFalseRecBuiltA :=
  liftA_of_boundOkB 1 k pinFalseRecBuiltA (boundOkB_add k 0 pinFalseRecBuiltA boundOkB_pinFalseRecBuiltA)

def pinFalseRecMemberA : CheckedMemberA := ⟨.recursorM, 1, pinFalseRecBuiltA, none, 0, none⟩

/-- `False` at `20` : `Sort 0`, in any context, at any universe arity. -/
def pinFalseConstTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h : E.members 20 = some pinFalseFamA) :
    HasTyA E I n Γ (.const 20 []) (.sort .zero) :=
  .const Γ 20 [] pinFalseFamA (.succ .zero) h rfl rfl (.sort Γ .zero)

def pinFalseFamEnvA : ResolvedEnvA := extendEnvA emptyEnvA 20 pinFalseFamA

def pinFalseMotTyTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h : E.members 20 = some pinFalseFamA) :
    HasTyA E I n Γ pinFalseMotTyA (.sort pinFalseMotSortA) :=
  .pi Γ (.const 20 []) .zero (.sort (.param 0)) (.succ (.param 0))
    (pinFalseConstTy h) (.sort (.assumption (.const 20 []) :: Γ) (.param 0))

/-- `motive t : Sort (param 0)`, under the motive and `t : False`. -/
def pinFalseMajorBodyTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA pinFalseFamEnvA I n (.assumption (.const 20 []) :: .assumption pinFalseMotTyA :: Γ)
      (.app (.bvar 1) (.bvar 0)) (.sort (.param 0)) :=
  .app _ (.bvar 1) (.bvar 0) (.const 20 []) (.sort (.param 0))
    .zero (.succ (.param 0)) (.succ (.param 0))
    (.sort _ (.param 0)) (.sort _ (.param 0))
    (.bvar _ 1 pinFalseMotTyA pinFalseMotSortA rfl (pinFalseMotTyTy rfl))
    (.bvar _ 0 (.const 20 []) .zero rfl (pinFalseConstTy rfl))

def pinFalseMajorTy {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA pinFalseFamEnvA I n (.assumption pinFalseMotTyA :: Γ) pinFalseMajorTyA (.sort pinFalseMajorSortA) :=
  .pi _ (.const 20 []) .zero (.app (.bvar 1) (.bvar 0)) (.param 0) (pinFalseConstTy rfl) pinFalseMajorBodyTy

def pinFalseRecHasTy (I : IotaIfaceA) :
    HasTyA pinFalseFamEnvA I 1 [] pinFalseRecBuiltA (.sort (.imax pinFalseMotSortA pinFalseMajorSortA)) :=
  .pi [] pinFalseMotTyA pinFalseMotSortA pinFalseMajorTyA pinFalseMajorSortA
    (pinFalseMotTyTy rfl) pinFalseMajorTy

/-- the stored type is the one built from the views: a prediction that could fail. -/
theorem pinFalseGroupRec_stored (I : IotaIfaceA) :
    pinFalseRecMemberA.mtypeA = groupRecTypeA pinFalseFamViewA (pinFalseCs I) .anySort := rfl

def pinFalseGroupRecA (I : IotaIfaceA) :
    GroupRecA I emptyEnvA 20 pinFalseFamA pinFalseFamViewA (pinFalseCs I) where
  member := pinFalseRecMemberA
  hcls := rfl
  hnobody := rfl
  hnp := rfl
  elim := .anySort
  harity := rfl
  stored := pinFalseGroupRec_stored I
  hclT := liftA_pinFalseRecBuiltA
  u := .imax pinFalseMotSortA pinFalseMajorSortA
  hT := pinFalseRecHasTy I
  hlvl := rfl

def pinFalseRecEnvA (I : IotaIfaceA) : ResolvedEnvA :=
  groupRecEnvA (pinFalseCs I) (pinFalseGroupRecA I)

/-- `False` with its derived recursor and no constructor, by `EnvWfA.groupRec`. -/
def pinFalseGroupRecWfA (I : IotaIfaceA) : EnvWfA I (pinFalseRecEnvA I) :=
  .groupRec emptyEnvA 20 pinFalseFamA (.succ .zero)
    .empty rfl rfl (fun _ => rfl) (.sort [] .zero) rfl
    pinFalseFamViewA (pinFalseCs I) rfl rfl (pinFalseGroupRecA I) rfl

/-- the environment, independent of the interface. -/
def pinFalseEnvA : ResolvedEnvA := extendEnvA pinFalseFamEnvA 21 pinFalseRecMemberA

theorem pinFalseRecEnvA_eq (I : IotaIfaceA) : pinFalseRecEnvA I = pinFalseEnvA := rfl

def pinFalse_wf : EnvWfA (iotaIfaceA pinFalseEnvA) pinFalseEnvA :=
  pinFalseRecEnvA_eq (iotaIfaceA pinFalseEnvA) ▸ pinFalseGroupRecWfA (iotaIfaceA pinFalseEnvA)

/-- D1 at `False`: its group has no constructor, read off the recursor's type and reference. -/
theorem pinFalse_noCtor : recHasCtorA 21 pinFalseRecMemberA = false := rfl

/-- every resident of `pinFalseEnvA` is `False` at `20` or its recursor at `21`. -/
theorem pinFalse_mem {r : Nat} {m : CheckedMemberA} (hm : pinFalseEnvA.members r = some m) :
    (r = 20 ∧ m = pinFalseFamA) ∨ (r = 21 ∧ m = pinFalseRecMemberA) := by
  revert hm
  unfold pinFalseEnvA pinFalseFamEnvA
  simp only [extendEnvA, emptyEnvA]
  intro hm
  by_cases h21 : r = 21
  · subst h21
    simp only [if_pos rfl] at hm
    cases hm
    exact Or.inr ⟨rfl, rfl⟩
  · simp only [if_neg h21] at hm
    by_cases h20 : r = 20
    · subst h20
      simp only [if_pos rfl] at hm
      cases hm
      exact Or.inl ⟨rfl, rfl⟩
    · simp only [if_neg h20] at hm
      cases hm

/-- `False` has no index binders, so the small-index profile holds vacuously. -/
theorem pinFalse_small : SmallIndexProfileA pinFalseEnvA := by
  intro r m u₀ hm hc _ v hv _ _ _ _ _ _
  rcases pinFalse_mem hm with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact absurd hv (List.not_mem_nil v)
  · exact MemberClass.noConfusion hc

/-- O1-a: the only recursor sits right after its family (`r = f + 1`), so `PropElimOnlyA` exempts it. -/
theorem pinFalse_propElim : PropElimOnlyA pinFalseEnvA := by
  intro r rm D f ls fm u₀ hrm hcl hlast hhead _ _ _ _ hne _ _ _
  rcases pinFalse_mem hrm with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
  · exact MemberClass.noConfusion hcl
  · have hD : (piDomsA pinFalseRecMemberA.mtypeA).getLast? = some (.const 20 []) := rfl
    rw [hD] at hlast
    cases hlast
    have hh : (appsSpineA (.const 20 [] : ExprA)).1 = .const 20 [] := rfl
    rw [hh] at hhead
    injection hhead with hf _
    subst hf
    exact absurd rfl hne

/-- TOOTH: `PropElimOnlyA`'s obligation fails at `False`'s recursor (its motive eliminates into
    `Sort u`), so `pinFalse_propElim` holds by O1-a's exemption alone. -/
theorem pinFalse_motive_not_prop :
    ∃ M, (piDomsA pinFalseRecMemberA.mtypeA)[pinFalseFamA.nparamsA]? = some M ∧ piBodyA M ≠ .sort .zero :=
  ⟨_, rfl, fun h => by cases h⟩

/-- THE SEMANTIC ENVIRONMENT AT `False`: the recursors' clause at a group without a constructor. -/
theorem envSemA_pinFalse (n : Nat) :
    EnvSemA pinFalseEnvA (iotaIfaceA pinFalseEnvA) n (fun _ => 1) :=
  envSemA_of_envWfA_rec (E := pinFalseEnvA) (n := n) (ρ₀ := fun _ => 1)
    pinFalse_wf posValA_one pinFalse_small pinFalse_propElim

/-- D1 at `False`, as a step: at its recursor the major arm is off, so a stepping major (a β-redex)
    is not stepped and the spine is weak-head normal. -/
theorem pinFalse_noMajorStep :
    hStepFnA pinFalseEnvA (iotaFnA pinFalseEnvA) []
      (.app (.app (.const 21 [.zero]) (.sort .zero))
        (.app (.lam (.sort .zero) (.succ .zero) (.bvar 0)) (.const 20 []))) = none := by
  decide

/-- the contrast at Nat: a group with a constructor, the same β-redex as the major is stepped. -/
theorem pinNat_majorStep :
    hStepFnA pinNatBuiltEnvA (iotaFnA pinNatBuiltEnvA) []
      (.app (.app (.app (.app (.const 13 [.zero]) (.sort .zero)) (.sort (.succ .zero))) pinMsA)
        (.app (.lam (.sort .zero) (.succ .zero) (.bvar 0)) (.const 11 []))) =
      some (.app (.app (.app (.app (.const 13 [.zero]) (.sort .zero)) (.sort (.succ .zero))) pinMsA)
        (.const 11 [])) := by
  decide

theorem sortConvCharA_pinFalse (n : Nat) {Γ : LCtxA} {l₁ l₂ u : Level}
    (hΓ : CtxWfA pinFalseEnvA (iotaIfaceA pinFalseEnvA) n Γ)
    (h : ConvA pinFalseEnvA (iotaIfaceA pinFalseEnvA) n Γ (.sort l₁) (.sort l₂) (.sort u)) :
    eqN l₁ l₂ :=
  sortConvCharA_rec (E := pinFalseEnvA) (n := n) (ρ₀ := fun _ => 1)
    pinFalse_wf posValA_one pinFalse_small (propElimStructA_of_propElimOnlyA pinFalse_propElim) hΓ h

/-! ## (8) `True` with its AnySort recursor: refuted over the old head step (O1-b-0), inside with K-unit (O1-b-1)

Family `30` (no parameters, no indices, sort `zero`), `intro` at `31` (no field), the recursor at `32`,
by `EnvWfA.groupRec`; a second environment adds an axiom `ax : True` at `33`. 05 §10 sends `True` to
AnySort (L-K1's `EliminationSelection.singletonProp`, `el05_pin`). Proof irrelevance makes
`rec M True a` convertible to `True` at every proof `a` (`pinTrueConv`). Over the head step before
O1-b-1 the spine stayed stuck at a proof that is not a constructor, and `EnvSemA` failed: with no axiom
in the context `t : True`, with one at a closed term (README O1-b-0). O1-b-1 adds the K-unit arm: at a
unit group (`unitGroupA`, read off the recursor's type: `pinTrue_unit`; not Nat's, `False`'s or an
indexed singleton's) the spine at its major steps to the minor, whatever the major
(`pinTrue_var_kunit`, `pinTrueAx_kunit`). `PropElimOnlyA` exempts the unit group's recursor
(`pinTrue_propElim`), and `EnvSemA` holds in both environments (`envSemA_pinTrue`,
`envSemA_pinTrueAx`): O1-b-0's prediction. -/

/-- `True` at `30` : `Sort 0`. -/
def pinTrueFamA : CheckedMemberA := ⟨.inductiveM, 0, .sort .zero, none, 0, none⟩
/-- `intro` at `31` : `True`, no field. -/
def pinTrueIntroA : CheckedMemberA := ⟨.constructorM, 0, .const 30 [], none, 0, some (.const 30 [])⟩
/-- the axiom `ax` at `33` : `True`: a proof that is not a constructor. -/
def pinTrueAxA : CheckedMemberA := ⟨.axiomM, 0, .const 30 [], none, 0, none⟩

def pinTrueFamViewA : FamViewA pinTrueFamA where
  params := []
  indices := []
  sort := .zero
  stored := rfl
  nparams := rfl
  profile := .inl (fun _ => rfl)

def pinTrueFamEnvA : ResolvedEnvA := extendEnvA emptyEnvA 30 pinTrueFamA

/-- `True` at `30` : `Sort 0`, in any context, at any universe arity. -/
def pinTrueConstTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h : E.members 30 = some pinTrueFamA) :
    HasTyA E I n Γ (.const 30 []) (.sort .zero) :=
  .const Γ 30 [] pinTrueFamA (.succ .zero) h rfl rfl (.sort Γ .zero)

def pinTrueIntroViewA (I : IotaIfaceA) :
    CtorViewA emptyEnvA I 30 pinTrueFamA pinTrueFamViewA pinTrueIntroA where
  mirrors := []
  fields := []
  res := []
  stored := rfl
  mirrorsConv := .nil []
  typed := .nil [] 0 [] (.nil .zero)
  univI := fun _ _ _ _ h => absurd h (List.not_mem_nil _)
  drecD_typed := drecDTypedA_of_noDelta (fun _ h => absurd h (List.not_mem_nil _))
  normConv := ⟨.refl [] _⟩
  normTyped := ⟨_, ⟨pinTrueConstTy (E := pinTrueFamEnvA) rfl⟩⟩
  univ := fun _ _ h => absurd h (List.not_mem_nil _)

/-- `intro` at `31` : `True`. -/
def pinTrueIntroTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h30 : E.members 30 = some pinTrueFamA) (h31 : E.members 31 = some pinTrueIntroA) :
    HasTyA E I n Γ (.const 31 []) (.const 30 []) :=
  .const Γ 31 [] pinTrueIntroA .zero h31 rfl rfl (pinTrueConstTy h30)

def pinTrueIntroGroupA (I : IotaIfaceA) :
    GroupCtorA I emptyEnvA 30 pinTrueFamA pinTrueFamViewA where
  ref := 31
  member := pinTrueIntroA
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := fun _ => rfl
  u := .zero
  hT := pinTrueConstTy (E := pinTrueFamEnvA) rfl
  hlvl := rfl
  view := pinTrueIntroViewA I
  hnorm := rfl
  hclN := fun _ => rfl
  hlvlN := rfl

def pinTrueCs (I : IotaIfaceA) : List (GroupCtorA I emptyEnvA 30 pinTrueFamA pinTrueFamViewA) :=
  [pinTrueIntroGroupA I]

/-- the motive's type at universe `u`, `True → Sort u`. -/
abbrev pinTrueMotTyAt (u : Level) : ExprA := .pi (.const 30 []) .zero (.sort u) (.succ u)
abbrev pinTrueMotSortAt (u : Level) : Level := .imax .zero (.succ u)
/-- the minor's type, `motive intro`, under the motive. -/
abbrev pinTrueMinorDomA : ExprA := .app (.bvar 0) (.const 31 [])
/-- the major and the body, `Π (t : True), motive t`, under the motive and the minor. -/
abbrev pinTrueMajorTyAt (u : Level) : ExprA := .pi (.const 30 []) .zero (.app (.bvar 2) (.bvar 0)) u
abbrev pinTrueMajorSortAt (u : Level) : Level := .imax .zero u
abbrev pinTrueMinorPiAt (u : Level) : ExprA :=
  .pi pinTrueMinorDomA u (pinTrueMajorTyAt u) (pinTrueMajorSortAt u)
abbrev pinTrueMinorPiSortAt (u : Level) : Level := .imax u (pinTrueMajorSortAt u)
/-- the recursor type at universe `u`, `Π (motive : True → Sort u) (m : motive intro) (t : True), motive t`. -/
def pinTrueRecTyAt (u : Level) : ExprA :=
  .pi (pinTrueMotTyAt u) (pinTrueMotSortAt u) (pinTrueMinorPiAt u) (pinTrueMinorPiSortAt u)

def pinTrueRecMemberA : CheckedMemberA := ⟨.recursorM, 1, pinTrueRecTyAt (.param 0), none, 0, none⟩

def pinTrueMotTyTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} (u : Level)
    (h30 : E.members 30 = some pinTrueFamA) :
    HasTyA E I n Γ (pinTrueMotTyAt u) (.sort (pinTrueMotSortAt u)) :=
  .pi Γ (.const 30 []) .zero (.sort u) (.succ u) (pinTrueConstTy h30) (.sort _ u)

/-- `motive a : Sort u`, the motive the variable `i`, `a : True`. -/
def pinTrueMotAppTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} (u : Level)
    (h30 : E.members 30 = some pinTrueFamA) (i : Nat) (a : ExprA)
    (hm : lookupTypeA Γ i = some (pinTrueMotTyAt u)) (ha : HasTyA E I n Γ a (.const 30 [])) :
    HasTyA E I n Γ (.app (.bvar i) a) (.sort u) :=
  .app Γ (.bvar i) a (.const 30 []) (.sort u) .zero (.succ u) (.succ u) (.sort _ u) (.sort Γ u)
    (.bvar Γ i (pinTrueMotTyAt u) (pinTrueMotSortAt u) hm (pinTrueMotTyTy u h30)) ha

def pinTrueRecTyTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} (u : Level)
    (h30 : E.members 30 = some pinTrueFamA) (h31 : E.members 31 = some pinTrueIntroA) :
    HasTyA E I n Γ (pinTrueRecTyAt u) (.sort (.imax (pinTrueMotSortAt u) (pinTrueMinorPiSortAt u))) :=
  .pi Γ (pinTrueMotTyAt u) (pinTrueMotSortAt u) (pinTrueMinorPiAt u) (pinTrueMinorPiSortAt u)
    (pinTrueMotTyTy u h30)
    (.pi _ pinTrueMinorDomA u (pinTrueMajorTyAt u) (pinTrueMajorSortAt u)
      (pinTrueMotAppTy u h30 0 (.const 31 []) rfl (pinTrueIntroTy h30 h31))
      (.pi _ (.const 30 []) .zero (.app (.bvar 2) (.bvar 0)) u (pinTrueConstTy h30)
        (pinTrueMotAppTy u h30 2 (.bvar 0) rfl (.bvar _ 0 (.const 30 []) .zero rfl (pinTrueConstTy h30)))))

theorem boundOkB_pinTrueRecTyA : boundOkB 0 (pinTrueRecTyAt (.param 0)) = true := rfl

theorem liftA_pinTrueRecTyA (k : Nat) : liftA k 1 (pinTrueRecTyAt (.param 0)) = pinTrueRecTyAt (.param 0) :=
  liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ boundOkB_pinTrueRecTyA)

/-- the stored type is the one built from the views: a prediction that could fail. -/
theorem pinTrueGroupRec_stored (I : IotaIfaceA) :
    pinTrueRecMemberA.mtypeA = groupRecTypeA pinTrueFamViewA (pinTrueCs I) .anySort := rfl

def pinTrueGroupRecA (I : IotaIfaceA) :
    GroupRecA I emptyEnvA 30 pinTrueFamA pinTrueFamViewA (pinTrueCs I) where
  member := pinTrueRecMemberA
  hcls := rfl
  hnobody := rfl
  hnp := rfl
  elim := .anySort
  harity := rfl
  stored := pinTrueGroupRec_stored I
  hclT := liftA_pinTrueRecTyA
  u := .imax (pinTrueMotSortAt (.param 0)) (pinTrueMinorPiSortAt (.param 0))
  hT := pinTrueRecTyTy (.param 0) rfl rfl
  hlvl := rfl

def pinTrueRecEnvA (I : IotaIfaceA) : ResolvedEnvA :=
  groupRecEnvA (pinTrueCs I) (pinTrueGroupRecA I)

/-- `True`, `intro` and the derived AnySort recursor, by `EnvWfA.groupRec`. -/
def pinTrueGroupRecWfA (I : IotaIfaceA) : EnvWfA I (pinTrueRecEnvA I) :=
  .groupRec emptyEnvA 30 pinTrueFamA (.succ .zero)
    .empty rfl rfl (fun _ => rfl) (.sort [] .zero) rfl
    pinTrueFamViewA (pinTrueCs I) ⟨rfl, rfl⟩ rfl (pinTrueGroupRecA I) rfl

/-- `True`, `intro` and the recursor, independent of the interface. -/
def pinTrueEnvA : ResolvedEnvA :=
  extendEnvA (extendEnvA pinTrueFamEnvA 31 pinTrueIntroA) 32 pinTrueRecMemberA

theorem pinTrueRecEnvA_eq (I : IotaIfaceA) : pinTrueRecEnvA I = pinTrueEnvA := rfl

def pinTrue_wf : EnvWfA (iotaIfaceA pinTrueEnvA) pinTrueEnvA :=
  pinTrueRecEnvA_eq (iotaIfaceA pinTrueEnvA) ▸ pinTrueGroupRecWfA (iotaIfaceA pinTrueEnvA)

/-- the same, with an axiom `ax : True` at `33`. -/
def pinTrueAxEnvA : ResolvedEnvA := extendEnvA pinTrueEnvA 33 pinTrueAxA

def pinTrueAx_wf : EnvWfA (iotaIfaceA pinTrueAxEnvA) pinTrueAxEnvA :=
  .axiomM (pinTrueRecEnvA (iotaIfaceA pinTrueAxEnvA)) 33 (.const 30 []) .zero
    (pinTrueGroupRecWfA (iotaIfaceA pinTrueAxEnvA)) rfl (pinTrueConstTy rfl) (fun _ => rfl) rfl

/-- every resident of `pinTrueEnvA` is `True` at `30`, `intro` at `31` or the recursor at `32`. -/
theorem pinTrue_mem {r : Nat} {m : CheckedMemberA} (hm : pinTrueEnvA.members r = some m) :
    (r = 30 ∧ m = pinTrueFamA) ∨ (r = 31 ∧ m = pinTrueIntroA) ∨ (r = 32 ∧ m = pinTrueRecMemberA) := by
  revert hm
  unfold pinTrueEnvA pinTrueFamEnvA
  simp only [extendEnvA, emptyEnvA]
  intro hm
  by_cases h32 : r = 32
  · subst h32
    simp only [if_pos rfl] at hm
    cases hm
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · simp only [if_neg h32] at hm
    by_cases h31 : r = 31
    · subst h31
      simp only [if_pos rfl] at hm
      cases hm
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · simp only [if_neg h31] at hm
      by_cases h30 : r = 30
      · subst h30
        simp only [if_pos rfl] at hm
        cases hm
        exact Or.inl ⟨rfl, rfl⟩
      · simp only [if_neg h30] at hm
        cases hm

/-- `True` has no index binders, so the small-index profile holds vacuously. -/
theorem pinTrue_small : SmallIndexProfileA pinTrueEnvA := by
  intro r m u₀ hm hc _ v hv _ _ _ _ _ _
  rcases pinTrue_mem hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact absurd hv (List.not_mem_nil v)
  · exact MemberClass.noConfusion hc
  · exact MemberClass.noConfusion hc

/-- O1-b-1: `PropElimOnlyA` holds at `True` by the unit exemption alone: its only recursor is the
    recursor of a unit group (`pinTrue_unit`), where the obligation is not demanded. -/
theorem pinTrue_propElim : PropElimOnlyA pinTrueEnvA := by
  intro r rm _ _ _ _ _ hrm hcl _ _ _ _ _ _ _ hun _ _
  rcases pinTrue_mem hrm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, rfl⟩
  · exact MemberClass.noConfusion hcl
  · exact MemberClass.noConfusion hcl
  · have h : unitGroupA 32 pinTrueRecMemberA = true := by decide
    rw [h] at hun
    exact Bool.noConfusion hun

section TrueTooth
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}

/-- the motive `λ (_ : True). Prop`. -/
abbrev pinTrueM : ExprA := .lam (.const 30 []) .zero (.sort .zero)
/-- `rec.{1} (λ _. Prop) True`: the minor is `True` itself. -/
abbrev pinTrueF : ExprA := .app (.app (.const 32 [.succ .zero]) pinTrueM) (.const 30 [])

def pinTrueMTy (h30 : E.members 30 = some pinTrueFamA) :
    HasTyA E I n Γ pinTrueM (pinTrueMotTyAt (.succ .zero)) :=
  .lam Γ (.const 30 []) .zero (.sort .zero) (.sort (.succ .zero)) (.succ (.succ .zero))
    (pinTrueConstTy h30) (.sort _ (.succ .zero)) (.sort _ .zero)

/-- `M a : Sort 1` at `a : True`. -/
def pinTrueMAppTy (h30 : E.members 30 = some pinTrueFamA) (a : ExprA)
    (ha : HasTyA E I n Γ a (.const 30 [])) :
    HasTyA E I n Γ (.app pinTrueM a) (.sort (.succ .zero)) :=
  .app Γ pinTrueM a (.const 30 []) (.sort (.succ .zero)) .zero (.succ (.succ .zero)) (.succ (.succ .zero))
    (.sort _ (.succ .zero)) (.sort Γ (.succ .zero)) (pinTrueMTy h30) ha

def pinTrueVar0Ty (h30 : E.members 30 = some pinTrueFamA) :
    HasTyA E I n (.assumption (.const 30 []) :: Γ) (.bvar 0) (.const 30 []) :=
  .bvar _ 0 (.const 30 []) .zero rfl (pinTrueConstTy h30)

/-- `Π (t : True), M t : Sort (imax 0 1)`. -/
def pinTrueMajorInstTy (h30 : E.members 30 = some pinTrueFamA) :
    HasTyA E I n Γ (.pi (.const 30 []) .zero (.app pinTrueM (.bvar 0)) (.succ .zero))
      (.sort (.imax .zero (.succ .zero))) :=
  .pi Γ (.const 30 []) .zero (.app pinTrueM (.bvar 0)) (.succ .zero) (pinTrueConstTy h30)
    (pinTrueMAppTy h30 (.bvar 0) (pinTrueVar0Ty h30))

/-- β at the motive: `M a ≡ Prop : Sort 1`. -/
def pinTrueBeta (h30 : E.members 30 = some pinTrueFamA) (a : ExprA) (ha : HasTyA E I n Γ a (.const 30 [])) :
    ConvA E I n Γ (.app pinTrueM a) (.sort .zero) (.sort (.succ .zero)) :=
  .beta Γ (.const 30 []) .zero (.sort .zero) a (.sort (.succ .zero)) (pinTrueConstTy h30)
    (.sort _ .zero) ha (.sort Γ .zero)

def pinTrueRecCTy (h30 : E.members 30 = some pinTrueFamA) (h31 : E.members 31 = some pinTrueIntroA)
    (h32 : E.members 32 = some pinTrueRecMemberA) :
    HasTyA E I n Γ (.const 32 [.succ .zero]) (pinTrueRecTyAt (.succ .zero)) :=
  .const Γ 32 [.succ .zero] pinTrueRecMemberA _ h32 rfl rfl (pinTrueRecTyTy (.succ .zero) h30 h31)

/-- `rec M : Π (m : M intro) (t : True), M t`. -/
def pinTrueF0Ty (h30 : E.members 30 = some pinTrueFamA) (h31 : E.members 31 = some pinTrueIntroA)
    (h32 : E.members 32 = some pinTrueRecMemberA) :
    HasTyA E I n Γ (.app (.const 32 [.succ .zero]) pinTrueM)
      (.pi (.app pinTrueM (.const 31 [])) (.succ .zero)
        (.pi (.const 30 []) .zero (.app pinTrueM (.bvar 0)) (.succ .zero)) (.imax .zero (.succ .zero))) :=
  .app Γ _ pinTrueM (pinTrueMotTyAt (.succ .zero)) (pinTrueMinorPiAt (.succ .zero))
    (pinTrueMotSortAt (.succ .zero)) (pinTrueMinorPiSortAt (.succ .zero)) (pinTrueMinorPiSortAt (.succ .zero))
    (.pi _ pinTrueMinorDomA (.succ .zero) (pinTrueMajorTyAt (.succ .zero)) (pinTrueMajorSortAt (.succ .zero))
      (pinTrueMotAppTy (.succ .zero) h30 0 (.const 31 []) rfl (pinTrueIntroTy h30 h31))
      (.pi _ (.const 30 []) .zero (.app (.bvar 2) (.bvar 0)) (.succ .zero) (pinTrueConstTy h30)
        (pinTrueMotAppTy (.succ .zero) h30 2 (.bvar 0) rfl (pinTrueVar0Ty h30))))
    (.pi Γ _ _ _ _ (pinTrueMAppTy h30 (.const 31 []) (pinTrueIntroTy h30 h31)) (pinTrueMajorInstTy h30))
    (pinTrueRecCTy h30 h31 h32) (pinTrueMTy h30)

/-- the minor `True : M intro`, through β. -/
def pinTrueMinorTy (h30 : E.members 30 = some pinTrueFamA) (h31 : E.members 31 = some pinTrueIntroA) :
    HasTyA E I n Γ (.const 30 []) (.app pinTrueM (.const 31 [])) :=
  .conv Γ (.const 30 []) (.sort .zero) (.app pinTrueM (.const 31 [])) (.succ .zero) (.succ .zero)
    (pinTrueConstTy h30) (.sort Γ .zero) (eqNA_refl _)
    (pinTrueMAppTy h30 (.const 31 []) (pinTrueIntroTy h30 h31))
    (.symm _ _ _ _ (pinTrueBeta h30 (.const 31 []) (pinTrueIntroTy h30 h31)))

/-- `rec M True : Π (t : True), M t`. -/
def pinTrueFTy (h30 : E.members 30 = some pinTrueFamA) (h31 : E.members 31 = some pinTrueIntroA)
    (h32 : E.members 32 = some pinTrueRecMemberA) :
    HasTyA E I n Γ pinTrueF (.pi (.const 30 []) .zero (.app pinTrueM (.bvar 0)) (.succ .zero)) :=
  .app Γ _ (.const 30 []) (.app pinTrueM (.const 31 []))
    (.pi (.const 30 []) .zero (.app pinTrueM (.bvar 0)) (.succ .zero)) (.succ .zero)
    (.imax .zero (.succ .zero)) (.imax .zero (.succ .zero))
    (pinTrueMajorInstTy h30) (pinTrueMajorInstTy h30) (pinTrueF0Ty h30 h31 h32) (pinTrueMinorTy h30 h31)

/-- `rec M True a : M a` at `a : True`. -/
def pinTrueFAppTy (h30 : E.members 30 = some pinTrueFamA) (h31 : E.members 31 = some pinTrueIntroA)
    (h32 : E.members 32 = some pinTrueRecMemberA) (a : ExprA) (ha : HasTyA E I n Γ a (.const 30 [])) :
    HasTyA E I n Γ (.app pinTrueF a) (.app pinTrueM a) :=
  .app Γ pinTrueF a (.const 30 []) (.app pinTrueM (.bvar 0)) .zero (.succ .zero) (.succ .zero)
    (pinTrueMAppTy h30 (.bvar 0) (pinTrueVar0Ty h30)) (pinTrueMAppTy h30 a ha) (pinTrueFTy h30 h31 h32) ha

/-- THE DERIVATION: `rec M True a ≡ True : Prop` at ANY proof `a : True`. Proof irrelevance (02 §10)
    gives `a ≡ intro`, the congruence carries it into the major, ι fires on `intro`, and β reads both
    motive instances as `Prop`. -/
def pinTrueConv (h30 : E.members 30 = some pinTrueFamA) (h31 : E.members 31 = some pinTrueIntroA)
    (h32 : E.members 32 = some pinTrueRecMemberA)
    (hι : I.rel E Γ (.app pinTrueF (.const 31 [])) (.const 30 []))
    (a : ExprA) (ha : HasTyA E I n Γ a (.const 30 [])) :
    ConvA E I n Γ (.app pinTrueF a) (.const 30 []) (.sort .zero) := by
  have hI := pinTrueIntroTy (E := E) (I := I) (n := n) (Γ := Γ) h30 h31
  have hIrr : ConvA E I n Γ a (.const 31 []) (.const 30 []) :=
    .irr Γ (.const 30 []) a (.const 31 []) (pinTrueConstTy h30) ha hI
  -- the two motive instances agree: `M a ≡ M intro : Sort 1`
  have hMM : ConvA E I n Γ (.app pinTrueM a) (.app pinTrueM (.const 31 [])) (.sort (.succ .zero)) :=
    .trans _ _ _ _ _ (pinTrueBeta h30 _ ha) (.symm _ _ _ _ (pinTrueBeta h30 _ hI))
  have hFI : HasTyA E I n Γ (.app pinTrueF (.const 31 [])) (.app pinTrueM a) :=
    .conv Γ _ _ _ (.succ .zero) (.succ .zero) (pinTrueFAppTy h30 h31 h32 _ hI) (pinTrueMAppTy h30 _ hI)
      (eqNA_refl _) (pinTrueMAppTy h30 _ ha) (.symm _ _ _ _ hMM)
  -- congruence at the major
  have c2 : ConvA E I n Γ (.app pinTrueF a) (.app pinTrueF (.const 31 [])) (.app pinTrueM a) :=
    .app Γ pinTrueF pinTrueF a (.const 31 []) (.const 30 []) (.app pinTrueM (.bvar 0)) .zero
      (.succ .zero) (.refl Γ pinTrueF _ (pinTrueFTy h30 h31 h32)) hIrr
      (pinTrueMAppTy h30 (.bvar 0) (pinTrueVar0Ty h30)) hFI
  -- ι at `intro`
  have c3 : ConvA E I n Γ (.app pinTrueF (.const 31 [])) (.const 30 []) (.app pinTrueM (.const 31 [])) :=
    .iota Γ _ _ _ hι (pinTrueFAppTy h30 h31 h32 _ hI) (pinTrueMinorTy h30 h31)
  have c2' := ConvA.tyConv Γ _ _ _ (.sort .zero) (.succ .zero) (.succ .zero) (.succ .zero) c2
    (pinTrueMAppTy h30 _ ha) (eqNA_refl _) (.sort Γ .zero) (eqNA_refl _) (pinTrueBeta h30 _ ha)
  have c3' := ConvA.tyConv Γ _ _ _ (.sort .zero) (.succ .zero) (.succ .zero) (.succ .zero) c3
    (pinTrueMAppTy h30 _ hI) (eqNA_refl _) (.sort Γ .zero) (eqNA_refl _) (pinTrueBeta h30 _ hI)
  exact .trans _ _ _ _ _ c2' c3'

end TrueTooth

/-- O1-b-1 (K-unit): `True`'s recursor is the recursor of a unit group, read off its own type; Nat's
    and `False`'s are not. -/
theorem pinTrue_unit : unitGroupA 32 pinTrueRecMemberA = true := by decide
theorem pinNat_notUnit : unitGroupA 13 pinNatRecMemberA = false := by decide
theorem pinFalse_notUnit : unitGroupA 21 pinFalseRecMemberA = false := by decide

/-- the recursor type of an INDEXED singleton `Prop` family `P : Prop → Prop` at `40` with
    `mk (i : Prop) : P i` at `41` (its field revealed in the index, 05 §10 AnySort):
    `Π (M : Π (i : Prop) (t : P i), Sort u) (m : Π (i : Prop), M i (mk i)) (i : Prop) (t : P i), M i t`. -/
def pinIdxRecTyA : ExprA :=
  .pi (.pi (.sort .zero) (.succ .zero) (.pi (.app (.const 40 []) (.bvar 0)) .zero (.sort (.param 0)) (.succ (.param 0)))
        (.succ (.param 0)))
    (.succ (.param 0))
    (.pi (.pi (.sort .zero) (.succ .zero) (.app (.app (.bvar 1) (.bvar 0)) (.app (.const 41 []) (.bvar 0))) (.param 0))
      (.param 0)
      (.pi (.sort .zero) (.succ .zero)
        (.pi (.app (.const 40 []) (.bvar 0)) .zero (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) (.param 0))
        (.param 0))
      (.param 0))
    (.param 0)

def pinIdxRecMemberA : CheckedMemberA := ⟨.recursorM, 1, pinIdxRecTyA, none, 0, none⟩

/-- TOOTH: an indexed singleton is no unit group. Its last three binders are the major, the index and
    the minor. The minor's domain `Π i, M i (mk i)` has one binder, so a test counting binders accepts
    it — and its spine's last argument before the major is the INDEX, not the minor. The motive-shape
    test refuses it: the third binder from the end is not `Π (t : D'), Sort w`. -/
theorem pinIdx_notUnit : unitGroupA 42 pinIdxRecMemberA = false := by decide

/-- K-unit at the variable proof: the spine steps to the minor, `True`, whatever the major (O1-b-0's
    stuck spine). -/
theorem pinTrue_var_kunit :
    hStepFnA pinTrueEnvA (iotaFnA pinTrueEnvA) [.assumption (.const 30 [])] (.app pinTrueF (.bvar 0)) =
      some (.const 30 []) := by
  decide

/-- the same at the axiom, in the empty context. -/
theorem pinTrueAx_kunit :
    hStepFnA pinTrueAxEnvA (iotaFnA pinTrueAxEnvA) [] (.app pinTrueF (.const 33 [])) = some (.const 30 []) := by
  decide

/-- every resident of `pinTrueAxEnvA` is one of `pinTrueEnvA`'s, or the axiom at `33`. -/
theorem pinTrueAx_mem {r : Nat} {m : CheckedMemberA} (hm : pinTrueAxEnvA.members r = some m) :
    pinTrueEnvA.members r = some m ∨ (r = 33 ∧ m = pinTrueAxA) := by
  revert hm
  unfold pinTrueAxEnvA
  simp only [extendEnvA]
  intro hm
  by_cases h33 : r = 33
  · subst h33
    simp only [if_pos rfl] at hm
    cases hm
    exact Or.inr ⟨rfl, rfl⟩
  · simp only [if_neg h33] at hm
    exact Or.inl hm

theorem pinTrueAx_small : SmallIndexProfileA pinTrueAxEnvA := by
  intro r m u₀ hm hc _ v hv _ _ _ _ _ _
  rcases pinTrueAx_mem hm with hm' | ⟨_, rfl⟩
  · rcases pinTrue_mem hm' with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact absurd hv (List.not_mem_nil v)
    · exact MemberClass.noConfusion hc
    · exact MemberClass.noConfusion hc
  · exact MemberClass.noConfusion hc

/-- the unit exemption at the axiom's environment too: the axiom is no recursor. -/
theorem pinTrueAx_propElim : PropElimOnlyA pinTrueAxEnvA := by
  intro r rm _ _ _ _ _ hrm hcl _ _ _ _ _ _ _ hun _ _
  rcases pinTrueAx_mem hrm with hrm' | ⟨_, rfl⟩
  · rcases pinTrue_mem hrm' with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, rfl⟩
    · exact MemberClass.noConfusion hcl
    · exact MemberClass.noConfusion hcl
    · rw [pinTrue_unit] at hun
      exact Bool.noConfusion hun
  · exact MemberClass.noConfusion hcl

/-- O1-b-1, THE PREDICTION: `True` with its AnySort recursor satisfies `EnvSemA` at the concrete ι, the
    environment O1-b-0 refuted over the old head step. -/
theorem envSemA_pinTrue (n : Nat) :
    EnvSemA pinTrueEnvA (iotaIfaceA pinTrueEnvA) n (fun _ => 1) :=
  envSemA_of_envWfA_rec (E := pinTrueEnvA) (n := n) (ρ₀ := fun _ => 1)
    pinTrue_wf posValA_one pinTrue_small pinTrue_propElim

/-- the same with the axiom `ax : True`, where O1-b-0's failure was at a closed term. -/
theorem envSemA_pinTrueAx (n : Nat) :
    EnvSemA pinTrueAxEnvA (iotaIfaceA pinTrueAxEnvA) n (fun _ => 1) :=
  envSemA_of_envWfA_rec (E := pinTrueAxEnvA) (n := n) (ρ₀ := fun _ => 1)
    pinTrueAx_wf posValA_one pinTrueAx_small pinTrueAx_propElim


/-! ## (9) O1-c-0: (K-struct) measured — one constructor, every field a proof, no index

(K-struct) splits in two. `Struct` (`50`–`52`, one non-recursive field `f : Π (P : Prop), P → P`) and
`Loop` (`60`–`62`, one recursive field `l : Loop`) are both one `EnvWfA.groupRec` step with the AnySort
recursor 05 §10 selects (`singletonProp`: each field's level is zero at every valuation, as at `And`,
`el06_pin`), and the recursor types built from the views are the hand-written ones, by `rfl`.

* `Struct` was outside this relation over the head step before W-1 (a) (README O1-c-0): proof
  irrelevance and ι make `rec M m a ≡ Struct : Prop` at every proof `a` (`pinStructConv`), and at a
  variable the spine was weak-head normal, a stuck spine against a family. The failure was O1-b-0's,
  with a field. W-1 (a)'s struct arm steps that spine (section (10)); the refutation's pins are retired
  (README W-1 (a)), `pinStructConv` stays as the conversion the arm realises.
* `Loop` is outside it WHATEVER the head step does at `rec M m t` (`pinLoop_envSem_false`): ι hands
  the minor the recursive call, so with the minor `λ l ih. ih → ih` the proposition `rec M m t` is
  convertible to its own self-arrow (`pinLoopConv`), and no proposition is `PropEqA`-related to its
  own self-arrow (`propEqA_not_selfArrow`): the Π-depth along the codomains (`PiDepthA`) would be its
  own successor. That lemma reads the head step only through determinism, lifting and the context's
  values, which any head step of the copy keeps (README O1-c-0). -/

/-! ### (9a) no proposition has its own self-arrow's structure -/
section SelfArrow
variable {E : ResolvedEnvA} {I : IotaIfaceA}

/-- the Π-depth of a type along its codomains: how many Π-binders its weak-head normal forms show,
    codomain by codomain, before a normal form that is no Π. -/
inductive PiDepthA (E : ResolvedEnvA) (I : IotaIfaceA) : LCtxA → ExprA → Nat → Prop
  | pi {Γ : LCtxA} {A D C : ExprA} {u v : Level} {k : Nat}
      (hA : RedTo E I Γ A (.pi D u C v)) (hC : PiDepthA E I (.assumption D :: Γ) C k) :
      PiDepthA E I Γ A (k + 1)
  | rigid {Γ : LCtxA} {A N : ExprA} (hA : RedTo E I Γ A N)
      (hnp : ∀ D u C v, N ≠ .pi D u C v) : PiDepthA E I Γ A 0

theorem piDepthA_det {Γ : LCtxA} {A : ExprA} {k : Nat} (h : PiDepthA E I Γ A k) :
    ∀ {k' : Nat}, PiDepthA E I Γ A k' → k = k' := by
  induction h with
  | pi hA hC ih =>
      intro k' h'
      cases h' with
      | pi hA' hC' =>
          have e := RedTo_det hA hA'
          injection e with e1 e2 e3 e4
          subst e1 e2 e3 e4
          rw [ih hC']
      | rigid hA' hnp => exact absurd (RedTo_det hA hA').symm (hnp _ _ _ _)
  | rigid hA hnp =>
      intro k' h'
      cases h' with
      | pi hA' _ => exact absurd (RedTo_det hA hA') (hnp _ _ _ _)
      | rigid _ _ => rfl

/-- two contexts that differ only in the types of assumptions: the head step reads neither. -/
inductive AsmEqA : LCtxA → LCtxA → Prop
  | refl (Γ : LCtxA) : AsmEqA Γ Γ
  | asm {Γ Γ' : LCtxA} (D D' : ExprA) (h : AsmEqA Γ Γ') :
      AsmEqA (.assumption D :: Γ) (.assumption D' :: Γ')

theorem asmEqA_lookupValue {Γ Γ' : LCtxA} (h : AsmEqA Γ Γ') :
    ∀ i, lookupValueA Γ i = lookupValueA Γ' i := by
  induction h with
  | refl _ => intro _; rfl
  | asm D D' _ ih =>
      intro i
      cases i with
      | zero => rfl
      | succ i => rw [lookupValueA_cons_succ, lookupValueA_cons_succ, ih i]

theorem hStepFnA_valEq (E : ResolvedEnvA) (iota : IotaFnA) {Γ Γ' : LCtxA}
    (h : ∀ i, lookupValueA Γ i = lookupValueA Γ' i) :
    (e : ExprA) → hStepFnA E iota Γ e = hStepFnA E iota Γ' e
  | .app f x => by
      rcases lamA_or_not f with ⟨A, u, b, rfl⟩ | hnl
      · rfl
      · rw [hStepFnA_app_nonlam E iota Γ x hnl, hStepFnA_app_nonlam E iota Γ' x hnl,
          hStepFnA_valEq E iota h f, hStepFnA_valEq E iota h x]
  | .bvar i => h i
  | .letE _ _ _ => rfl
  | .const _ _ => rfl
  | .lit _ => rfl
  | .sort _ => rfl
  | .lam _ _ _ => rfl
  | .pi _ _ _ _ => rfl

theorem whnfA_valEq (E : ResolvedEnvA) (iota : IotaFnA) {Γ Γ' : LCtxA}
    (h : ∀ i, lookupValueA Γ i = lookupValueA Γ' i) :
    (fuel : Nat) → (e : ExprA) → whnfA E iota Γ fuel e = whnfA E iota Γ' fuel e
  | 0, e => by simp only [whnfA, hStepFnA_valEq E iota h e]
  | fuel + 1, e => by
      simp only [whnfA, hStepFnA_valEq E iota h e]
      cases hStepFnA E iota Γ' e with
      | none => rfl
      | some e' => exact whnfA_valEq E iota h fuel e'

theorem redTo_asmEq {Γ Γ' : LCtxA} (h : AsmEqA Γ Γ') {t t' : ExprA} (ht : RedTo E I Γ t t') :
    RedTo E I Γ' t t' :=
  ht.elim fun fuel hf => ⟨fuel, by rw [← whnfA_valEq E I.fn (asmEqA_lookupValue h)]; exact hf⟩

theorem piDepthA_asmEq {Γ : LCtxA} {A : ExprA} {k : Nat} (h : PiDepthA E I Γ A k) :
    ∀ {Γ' : LCtxA}, AsmEqA Γ Γ' → PiDepthA E I Γ' A k := by
  induction h with
  | pi hA _ ih => intro Γ' hΓ; exact .pi (redTo_asmEq hΓ hA) (ih (.asm _ _ hΓ))
  | rigid hA hnp => intro Γ' hΓ; exact .rigid (redTo_asmEq hΓ hA) hnp

theorem piDepthA_liftA (hE : EnvClosedA E) (hI : IotaLiftA I) (d : LocalDeclA)
    {Γ : LCtxA} {A : ExprA} {k : Nat} (h : PiDepthA E I Γ A k) :
    ∀ {c : Nat}, c ≤ Γ.length → PiDepthA E I (insertAtA d c Γ) (liftA c 1 A) k := by
  induction h with
  | pi hA _ ih =>
      intro c hc
      have hA' := redTo_liftA hE hI d hc hA
      rw [liftA_pi] at hA'
      exact .pi hA' (ih (c := c + 1) (Nat.succ_le_succ hc))
  | rigid hA hnp =>
      intro c hc
      refine .rigid (redTo_liftA hE hI d hc hA) ?_
      intro D u C v e
      obtain ⟨D₀, C₀, rfl, _, _⟩ := liftA_eq_pi _ e
      exact hnp _ _ _ _ rfl

theorem propEqA_piDepth {n : Nat} {Γ : LCtxA} {a b : ExprA} (h : PropEqA E I n Γ a b) :
    Nonempty (CtxWfA E I n Γ) → ∃ k, PiDepthA E I Γ a k ∧ PiDepthA E I Γ b k := by
  induction h with
  | @pi Γ a b D C D' C' u v u' v' ha hb _ _ hDty _ _ _ _ ih =>
      intro hΓ
      have hctx : Nonempty (CtxWfA E I n (.assumption D :: Γ)) :=
        hΓ.elim fun g => hDty.elim fun t => ⟨.assumption g t⟩
      have hD₀ : Nonempty (TyConvA E I n Γ D D) :=
        hDty.elim fun t => ⟨.of Γ D D u u u t (eqNA_refl u) t (eqNA_refl u) (.refl Γ D (.sort u) t)⟩
      obtain ⟨k, hk, hk'⟩ := ih [] ⟨trivial, hΓ⟩ D hctx hD₀ hctx
      exact ⟨k + 1, .pi (whTyA_redTo ha (hStepFnA_pi E I.fn Γ D u C v)) hk,
        .pi (whTyA_redTo hb (hStepFnA_pi E I.fn Γ D' u' C' v')) (piDepthA_asmEq hk' (.asm D D' (.refl Γ)))⟩
  | fam ha hb hna hnb _ _ _ _ _ =>
      intro _
      exact ⟨0, .rigid (whTyA_redTo ha hna) (fun _ _ _ _ e => foldAppsA_const_ne_pi _ _ _ _ _ _ _ e),
        .rigid (whTyA_redTo hb hnb) (fun _ _ _ _ e => foldAppsA_const_ne_pi _ _ _ _ _ _ _ e)⟩
  | stuck ha hb hN hN' _ =>
      intro _
      exact ⟨0, .rigid (whTyA_redTo ha hN.1) (fun _ _ _ _ e => by subst e; exact stuckA_not_pi hN),
        .rigid (whTyA_redTo hb hN'.1) (fun _ _ _ _ e => by subst e; exact stuckA_not_pi hN')⟩

/-- NO PROPOSITION HAS ITS OWN SELF-ARROW'S STRUCTURE: `PropEqA` gives both sides the same Π-depth,
    and the self-arrow's is one more than its codomain's, the proposition lifted. -/
theorem propEqA_not_selfArrow (hE : EnvClosedA E) (hI : IotaLiftA I) {n : Nat} {Γ : LCtxA}
    (hΓ : Nonempty (CtxWfA E I n Γ)) {a : ExprA} {u v : Level}
    (h : PropEqA E I n Γ a (.pi a u (liftA 0 1 a) v)) : False := by
  obtain ⟨k, ha, hb⟩ := propEqA_piDepth h hΓ
  have hpi : RedTo E I Γ (.pi a u (liftA 0 1 a) v) (.pi a u (liftA 0 1 a) v) :=
    ⟨0, whnfA_of_normal E I.fn Γ 0 _ (hStepFnA_pi E I.fn Γ _ _ _ _)⟩
  cases hb with
  | pi hA hC =>
      have e := RedTo_det hA hpi
      injection e with e1 _ e3 _
      rw [e1, e3] at hC
      have hw := piDepthA_liftA hE hI (.assumption a) ha (c := 0) (Nat.zero_le _)
      exact Nat.succ_ne_self _ (piDepthA_det hC hw).symm
  | rigid hA hnp => exact hnp _ _ _ _ (RedTo_det hA hpi)

end SelfArrow


/-! ### (9b) `Struct`: one non-recursive proof field -/
/-- the field's type `Π (P : Prop), P → P`, a closed proposition. -/
abbrev pinIdPropA : ExprA := .pi (.sort .zero) (.succ .zero) (.pi (.bvar 0) .zero (.bvar 1) .zero) (.imax .zero .zero)
abbrev pinIdPropLvA : Level := .imax (.succ .zero) (.imax .zero .zero)
/-- its proof `λ (P : Prop) (p : P). p`. -/
abbrev pinIdTermA : ExprA := .lam (.sort .zero) (.succ .zero) (.lam (.bvar 0) .zero (.bvar 0))

def pinStructFamA : CheckedMemberA := ⟨.inductiveM, 0, .sort .zero, none, 0, none⟩
def pinStructMkA : CheckedMemberA := ⟨.constructorM, 0, .pi pinIdPropA pinIdPropLvA (.const 50 []) .zero, none, 0, some (.pi pinIdPropA pinIdPropLvA (.const 50 []) .zero)⟩

def pinIdPropTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA E I n Γ pinIdPropA (.sort pinIdPropLvA) :=
  .pi Γ (.sort .zero) (.succ .zero) (.pi (.bvar 0) .zero (.bvar 1) .zero) (.imax .zero .zero) (.sort Γ .zero)
    (.pi _ (.bvar 0) .zero (.bvar 1) .zero (.bvar _ 0 (.sort .zero) (.succ .zero) rfl (.sort _ .zero))
      (.bvar _ 1 (.sort .zero) (.succ .zero) rfl (.sort _ .zero)))

def pinIdTermTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA E I n Γ pinIdTermA pinIdPropA :=
  .lam Γ (.sort .zero) (.succ .zero) (.lam (.bvar 0) .zero (.bvar 0)) (.pi (.bvar 0) .zero (.bvar 1) .zero)
    (.imax .zero .zero) (.sort Γ .zero)
    (.pi _ (.bvar 0) .zero (.bvar 1) .zero (.bvar _ 0 (.sort .zero) (.succ .zero) rfl (.sort _ .zero))
      (.bvar _ 1 (.sort .zero) (.succ .zero) rfl (.sort _ .zero)))
    (.lam _ (.bvar 0) .zero (.bvar 0) (.bvar 1) .zero (.bvar _ 0 (.sort .zero) (.succ .zero) rfl (.sort _ .zero))
      (.bvar _ 1 (.sort .zero) (.succ .zero) rfl (.sort _ .zero))
      (.bvar _ 0 (.bvar 1) .zero rfl (.bvar _ 1 (.sort .zero) (.succ .zero) rfl (.sort _ .zero))))

def pinStructFamViewA : FamViewA pinStructFamA where
  params := []
  indices := []
  sort := .zero
  stored := rfl
  nparams := rfl
  profile := .inl (fun _ => rfl)

def pinStructFamEnvA : ResolvedEnvA := extendEnvA emptyEnvA 50 pinStructFamA

def pinStructConstTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h : E.members 50 = some pinStructFamA) :
    HasTyA E I n Γ (.const 50 []) (.sort .zero) :=
  .const Γ 50 [] pinStructFamA (.succ .zero) h rfl rfl (.sort Γ .zero)

def pinStructMkPiTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h : E.members 50 = some pinStructFamA) :
    HasTyA E I n Γ pinStructMkA.mtypeA (.sort (.imax pinIdPropLvA .zero)) :=
  .pi Γ pinIdPropA pinIdPropLvA (.const 50 []) .zero pinIdPropTy (pinStructConstTy h)

def pinStructMkViewA (I : IotaIfaceA) :
    CtorViewA emptyEnvA I 50 pinStructFamA pinStructFamViewA pinStructMkA where
  mirrors := []
  fields := [.plain pinIdPropA pinIdPropLvA]
  res := []
  stored := rfl
  mirrorsConv := .nil []
  typed := .plain [] 0 pinIdPropA pinIdPropLvA [] [] pinIdPropTy (.nil _ 1 [] (.nil .zero))
  univI := fun _ _ _ _ h => by cases List.mem_singleton.mp h
  drecD_typed := drecDTypedA_of_noDelta (fun _ h => by cases List.mem_singleton.mp h; trivial)
  normConv := ⟨.refl [] _⟩
  normTyped := ⟨_, ⟨pinStructMkPiTy (E := pinStructFamEnvA) rfl⟩⟩
  univ := fun _ _ _ => Or.inl (fun _ => rfl)

def pinStructMkConstTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h50 : E.members 50 = some pinStructFamA) (h51 : E.members 51 = some pinStructMkA) :
    HasTyA E I n Γ (.const 51 []) pinStructMkA.mtypeA :=
  .const Γ 51 [] pinStructMkA (.imax pinIdPropLvA .zero) h51 rfl rfl (pinStructMkPiTy h50)

/-- `mk a : S` at `a : Π P, P → P`. -/
def pinStructMkAppTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h50 : E.members 50 = some pinStructFamA) (h51 : E.members 51 = some pinStructMkA) (a : ExprA)
    (ha : HasTyA E I n Γ a pinIdPropA) :
    HasTyA E I n Γ (.app (.const 51 []) a) (.const 50 []) :=
  .app Γ (.const 51 []) a pinIdPropA (.const 50 []) pinIdPropLvA .zero .zero (pinStructConstTy h50) (pinStructConstTy h50)
    (pinStructMkConstTy h50 h51) ha

def pinStructMkGroupA (I : IotaIfaceA) :
    GroupCtorA I emptyEnvA 50 pinStructFamA pinStructFamViewA where
  ref := 51
  member := pinStructMkA
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := fun _ => rfl
  u := .imax pinIdPropLvA .zero
  hT := pinStructMkPiTy (E := pinStructFamEnvA) rfl
  hlvl := rfl
  view := pinStructMkViewA I
  hnorm := rfl
  hclN := fun _ => rfl
  hlvlN := rfl

def pinStructCs (I : IotaIfaceA) : List (GroupCtorA I emptyEnvA 50 pinStructFamA pinStructFamViewA) :=
  [pinStructMkGroupA I]

abbrev pinStructMotTyAt (u : Level) : ExprA := .pi (.const 50 []) .zero (.sort u) (.succ u)
abbrev pinStructMotSortAt (u : Level) : Level := .imax .zero (.succ u)
/-- the minor's type under the motive: `Π (f : Π P, P → P), motive (mk f)`. -/
abbrev pinStructMinorDomAt (u : Level) : ExprA :=
  .pi pinIdPropA pinIdPropLvA (.app (.bvar 1) (.app (.const 51 []) (.bvar 0))) u
abbrev pinStructMinorDomSortAt (u : Level) : Level := .imax pinIdPropLvA u
abbrev pinStructMajorTyAt (u : Level) : ExprA := .pi (.const 50 []) .zero (.app (.bvar 2) (.bvar 0)) u
abbrev pinStructMajorSortAt (u : Level) : Level := .imax .zero u
abbrev pinStructMinorPiAt (u : Level) : ExprA :=
  .pi (pinStructMinorDomAt u) (pinStructMinorDomSortAt u) (pinStructMajorTyAt u) (pinStructMajorSortAt u)
abbrev pinStructMinorPiSortAt (u : Level) : Level := .imax (pinStructMinorDomSortAt u) (pinStructMajorSortAt u)
def pinStructRecTyAt (u : Level) : ExprA :=
  .pi (pinStructMotTyAt u) (pinStructMotSortAt u) (pinStructMinorPiAt u) (pinStructMinorPiSortAt u)

def pinStructRecMemberA : CheckedMemberA := ⟨.recursorM, 1, pinStructRecTyAt (.param 0), none, 0, none⟩

theorem pinStructGroupRec_stored (I : IotaIfaceA) :
    pinStructRecMemberA.mtypeA = groupRecTypeA pinStructFamViewA (pinStructCs I) .anySort := rfl

def pinStructMotTyTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} (u : Level)
    (h50 : E.members 50 = some pinStructFamA) :
    HasTyA E I n Γ (pinStructMotTyAt u) (.sort (pinStructMotSortAt u)) :=
  .pi Γ (.const 50 []) .zero (.sort u) (.succ u) (pinStructConstTy h50) (.sort _ u)

/-- `motive a : Sort u`, the motive the variable `i`, `a : S`. -/
def pinStructMotAppTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} (u : Level)
    (h50 : E.members 50 = some pinStructFamA) (i : Nat) (a : ExprA)
    (hm : lookupTypeA Γ i = some (pinStructMotTyAt u)) (ha : HasTyA E I n Γ a (.const 50 [])) :
    HasTyA E I n Γ (.app (.bvar i) a) (.sort u) :=
  .app Γ (.bvar i) a (.const 50 []) (.sort u) .zero (.succ u) (.succ u) (.sort _ u) (.sort Γ u)
    (.bvar Γ i (pinStructMotTyAt u) (pinStructMotSortAt u) hm (pinStructMotTyTy u h50)) ha

/-- the field variable `0 : Π P, P → P`. -/
def pinStructFieldVarTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    HasTyA E I n (.assumption pinIdPropA :: Γ) (.bvar 0) pinIdPropA :=
  .bvar _ 0 pinIdPropA pinIdPropLvA rfl pinIdPropTy

def pinStructVar0Ty {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}
    (h50 : E.members 50 = some pinStructFamA) :
    HasTyA E I n (.assumption (.const 50 []) :: Γ) (.bvar 0) (.const 50 []) :=
  .bvar _ 0 (.const 50 []) .zero rfl (pinStructConstTy h50)

def pinStructMinorPiTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} (u : Level)
    (h50 : E.members 50 = some pinStructFamA) (h51 : E.members 51 = some pinStructMkA) :
    HasTyA E I n (.assumption (pinStructMotTyAt u) :: Γ) (pinStructMinorPiAt u) (.sort (pinStructMinorPiSortAt u)) :=
  .pi _ (pinStructMinorDomAt u) (pinStructMinorDomSortAt u) (pinStructMajorTyAt u) (pinStructMajorSortAt u)
    (.pi _ pinIdPropA pinIdPropLvA (.app (.bvar 1) (.app (.const 51 []) (.bvar 0))) u pinIdPropTy
      (pinStructMotAppTy u h50 1 _ rfl (pinStructMkAppTy h50 h51 (.bvar 0) pinStructFieldVarTy)))
    (.pi _ (.const 50 []) .zero (.app (.bvar 2) (.bvar 0)) u (pinStructConstTy h50)
      (pinStructMotAppTy u h50 2 (.bvar 0) rfl (pinStructVar0Ty h50)))

def pinStructRecTyTy {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} (u : Level)
    (h50 : E.members 50 = some pinStructFamA) (h51 : E.members 51 = some pinStructMkA) :
    HasTyA E I n Γ (pinStructRecTyAt u) (.sort (.imax (pinStructMotSortAt u) (pinStructMinorPiSortAt u))) :=
  .pi Γ (pinStructMotTyAt u) (pinStructMotSortAt u) (pinStructMinorPiAt u) (pinStructMinorPiSortAt u)
    (pinStructMotTyTy u h50) (pinStructMinorPiTy u h50 h51)

theorem boundOkB_pinStructRecTyA : boundOkB 0 (pinStructRecTyAt (.param 0)) = true := rfl

theorem liftA_pinStructRecTyA (k : Nat) : liftA k 1 (pinStructRecTyAt (.param 0)) = pinStructRecTyAt (.param 0) :=
  liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ boundOkB_pinStructRecTyA)

def pinStructGroupRecA (I : IotaIfaceA) :
    GroupRecA I emptyEnvA 50 pinStructFamA pinStructFamViewA (pinStructCs I) where
  member := pinStructRecMemberA
  hcls := rfl
  hnobody := rfl
  hnp := rfl
  elim := .anySort
  harity := rfl
  stored := pinStructGroupRec_stored I
  hclT := liftA_pinStructRecTyA
  u := .imax (pinStructMotSortAt (.param 0)) (pinStructMinorPiSortAt (.param 0))
  hT := pinStructRecTyTy (.param 0) rfl rfl
  hlvl := rfl

def pinStructRecEnvA (I : IotaIfaceA) : ResolvedEnvA :=
  groupRecEnvA (pinStructCs I) (pinStructGroupRecA I)

/-- `S`, `mk` and the derived AnySort recursor, by `EnvWfA.groupRec`. -/
def pinStructGroupRecWfA (I : IotaIfaceA) : EnvWfA I (pinStructRecEnvA I) :=
  .groupRec emptyEnvA 50 pinStructFamA (.succ .zero)
    .empty rfl rfl (fun _ => rfl) (.sort [] .zero) rfl
    pinStructFamViewA (pinStructCs I) ⟨rfl, rfl⟩ rfl (pinStructGroupRecA I) rfl

def pinStructEnvA : ResolvedEnvA :=
  extendEnvA (extendEnvA pinStructFamEnvA 51 pinStructMkA) 52 pinStructRecMemberA

theorem pinStructRecEnvA_eq (I : IotaIfaceA) : pinStructRecEnvA I = pinStructEnvA := rfl

def pinStruct_wf : EnvWfA (iotaIfaceA pinStructEnvA) pinStructEnvA :=
  pinStructRecEnvA_eq (iotaIfaceA pinStructEnvA) ▸ pinStructGroupRecWfA (iotaIfaceA pinStructEnvA)

theorem pinStruct_mem {r : Nat} {m : CheckedMemberA} (hm : pinStructEnvA.members r = some m) :
    (r = 50 ∧ m = pinStructFamA) ∨ (r = 51 ∧ m = pinStructMkA) ∨ (r = 52 ∧ m = pinStructRecMemberA) := by
  revert hm
  unfold pinStructEnvA pinStructFamEnvA
  simp only [extendEnvA, emptyEnvA]
  intro hm
  by_cases h52 : r = 52
  · subst h52
    simp only [if_pos rfl] at hm
    cases hm
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · simp only [if_neg h52] at hm
    by_cases h51 : r = 51
    · subst h51
      simp only [if_pos rfl] at hm
      cases hm
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · simp only [if_neg h51] at hm
      by_cases h50 : r = 50
      · subst h50
        simp only [if_pos rfl] at hm
        cases hm
        exact Or.inl ⟨rfl, rfl⟩
      · simp only [if_neg h50] at hm
        cases hm

theorem pinStruct_small : SmallIndexProfileA pinStructEnvA := by
  intro r m u₀ hm hc _ v hv _ _ _ _ _ _
  rcases pinStruct_mem hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact absurd hv (List.not_mem_nil v)
  · exact MemberClass.noConfusion hc
  · exact MemberClass.noConfusion hc

/-- `S`'s recursor is no unit group's: its minor has a field. -/
theorem pinStruct_notUnit : unitGroupA 52 pinStructRecMemberA = false := by decide

theorem pinStruct_not_propElim : ¬ PropElimOnlyA pinStructEnvA := by
  intro h
  have := h 52 pinStructRecMemberA (.const 50 []) 50 [] pinStructFamA .zero rfl rfl rfl rfl rfl rfl rfl
    (fun _ => rfl) (by decide) pinStruct_notUnit _ rfl
  cases this

section StructTooth
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}

/-- the motive `λ (_ : S). Prop`. -/
abbrev pinStructM : ExprA := .lam (.const 50 []) .zero (.sort .zero)
/-- the minor `λ (f : Π P, P → P). S`. -/
abbrev pinStructm : ExprA := .lam pinIdPropA pinIdPropLvA (.const 50 [])
/-- `rec.{1} (λ _. Prop) (λ f. S)`. -/
abbrev pinStructF : ExprA := .app (.app (.const 52 [.succ .zero]) pinStructM) pinStructm
/-- the minor's domain at the motive: `Π (f : Π P, P → P), M (mk f)`. -/
abbrev pinStructMinorDomM : ExprA := .pi pinIdPropA pinIdPropLvA (.app pinStructM (.app (.const 51 []) (.bvar 0))) (.succ .zero)
/-- the major and the body at the motive: `Π (t : S), M t`. -/
abbrev pinStructMajorM : ExprA := .pi (.const 50 []) .zero (.app pinStructM (.bvar 0)) (.succ .zero)

def pinStructMTy (h50 : E.members 50 = some pinStructFamA) :
    HasTyA E I n Γ pinStructM (pinStructMotTyAt (.succ .zero)) :=
  .lam Γ (.const 50 []) .zero (.sort .zero) (.sort (.succ .zero)) (.succ (.succ .zero))
    (pinStructConstTy h50) (.sort _ (.succ .zero)) (.sort _ .zero)

def pinStructMAppTy (h50 : E.members 50 = some pinStructFamA) (a : ExprA)
    (ha : HasTyA E I n Γ a (.const 50 [])) :
    HasTyA E I n Γ (.app pinStructM a) (.sort (.succ .zero)) :=
  .app Γ pinStructM a (.const 50 []) (.sort (.succ .zero)) .zero (.succ (.succ .zero)) (.succ (.succ .zero))
    (.sort _ (.succ .zero)) (.sort Γ (.succ .zero)) (pinStructMTy h50) ha

def pinStructBeta (h50 : E.members 50 = some pinStructFamA) (a : ExprA) (ha : HasTyA E I n Γ a (.const 50 [])) :
    ConvA E I n Γ (.app pinStructM a) (.sort .zero) (.sort (.succ .zero)) :=
  .beta Γ (.const 50 []) .zero (.sort .zero) a (.sort (.succ .zero)) (pinStructConstTy h50)
    (.sort _ .zero) ha (.sort Γ .zero)

/-- `S : M (mk a)`, through β. -/
def pinStructAtMkTy (h50 : E.members 50 = some pinStructFamA) (h51 : E.members 51 = some pinStructMkA) (a : ExprA)
    (ha : HasTyA E I n Γ a pinIdPropA) :
    HasTyA E I n Γ (.const 50 []) (.app pinStructM (.app (.const 51 []) a)) :=
  .conv Γ (.const 50 []) (.sort .zero) (.app pinStructM (.app (.const 51 []) a)) (.succ .zero) (.succ .zero)
    (pinStructConstTy h50) (.sort Γ .zero) (eqNA_refl _) (pinStructMAppTy h50 _ (pinStructMkAppTy h50 h51 a ha))
    (.symm _ _ _ _ (pinStructBeta h50 _ (pinStructMkAppTy h50 h51 a ha)))

def pinStructmTy (h50 : E.members 50 = some pinStructFamA) (h51 : E.members 51 = some pinStructMkA) :
    HasTyA E I n Γ pinStructm pinStructMinorDomM :=
  .lam Γ pinIdPropA pinIdPropLvA (.const 50 []) (.app pinStructM (.app (.const 51 []) (.bvar 0))) (.succ .zero)
    pinIdPropTy (pinStructMAppTy h50 _ (pinStructMkAppTy h50 h51 (.bvar 0) pinStructFieldVarTy))
    (pinStructAtMkTy h50 h51 (.bvar 0) pinStructFieldVarTy)

def pinStructRecCTy (h50 : E.members 50 = some pinStructFamA) (h51 : E.members 51 = some pinStructMkA)
    (h52 : E.members 52 = some pinStructRecMemberA) :
    HasTyA E I n Γ (.const 52 [.succ .zero]) (pinStructRecTyAt (.succ .zero)) :=
  .const Γ 52 [.succ .zero] pinStructRecMemberA _ h52 rfl rfl (pinStructRecTyTy (.succ .zero) h50 h51)

def pinStructMajorMTy (h50 : E.members 50 = some pinStructFamA) {Δ : LCtxA} :
    HasTyA E I n Δ pinStructMajorM (.sort (pinStructMajorSortAt (.succ .zero))) :=
  .pi Δ (.const 50 []) .zero (.app pinStructM (.bvar 0)) (.succ .zero) (pinStructConstTy h50)
    (pinStructMAppTy h50 (.bvar 0) (pinStructVar0Ty h50))

/-- `rec M : Π (m : Π f, M (mk f)) (t : S), M t`. -/
def pinStructF0Ty (h50 : E.members 50 = some pinStructFamA) (h51 : E.members 51 = some pinStructMkA)
    (h52 : E.members 52 = some pinStructRecMemberA) :
    HasTyA E I n Γ (.app (.const 52 [.succ .zero]) pinStructM)
      (.pi pinStructMinorDomM (pinStructMinorDomSortAt (.succ .zero)) pinStructMajorM (pinStructMajorSortAt (.succ .zero))) :=
  .app Γ _ pinStructM (pinStructMotTyAt (.succ .zero)) (pinStructMinorPiAt (.succ .zero))
    (pinStructMotSortAt (.succ .zero)) (pinStructMinorPiSortAt (.succ .zero)) (pinStructMinorPiSortAt (.succ .zero))
    (pinStructMinorPiTy (.succ .zero) h50 h51)
    (.pi Γ _ _ _ _ (.pi Γ pinIdPropA pinIdPropLvA _ (.succ .zero) pinIdPropTy
        (pinStructMAppTy h50 _ (pinStructMkAppTy h50 h51 (.bvar 0) pinStructFieldVarTy)))
      (pinStructMajorMTy h50))
    (pinStructRecCTy h50 h51 h52) (pinStructMTy h50)

/-- `rec M m : Π (t : S), M t`. -/
def pinStructFTy (h50 : E.members 50 = some pinStructFamA) (h51 : E.members 51 = some pinStructMkA)
    (h52 : E.members 52 = some pinStructRecMemberA) :
    HasTyA E I n Γ pinStructF pinStructMajorM :=
  .app Γ _ pinStructm pinStructMinorDomM pinStructMajorM (pinStructMinorDomSortAt (.succ .zero)) (pinStructMajorSortAt (.succ .zero))
    (pinStructMajorSortAt (.succ .zero)) (pinStructMajorMTy h50) (pinStructMajorMTy h50) (pinStructF0Ty h50 h51 h52) (pinStructmTy h50 h51)

/-- `rec M m a : M a` at `a : S`. -/
def pinStructFAppTy (h50 : E.members 50 = some pinStructFamA) (h51 : E.members 51 = some pinStructMkA)
    (h52 : E.members 52 = some pinStructRecMemberA) (a : ExprA) (ha : HasTyA E I n Γ a (.const 50 [])) :
    HasTyA E I n Γ (.app pinStructF a) (.app pinStructM a) :=
  .app Γ pinStructF a (.const 50 []) (.app pinStructM (.bvar 0)) .zero (.succ .zero) (.succ .zero)
    (pinStructMAppTy h50 (.bvar 0) (pinStructVar0Ty h50)) (pinStructMAppTy h50 a ha) (pinStructFTy h50 h51 h52) ha

/-- ι's reduct `m id : M (mk id)`. -/
def pinStructmAppTy (h50 : E.members 50 = some pinStructFamA) (h51 : E.members 51 = some pinStructMkA) :
    HasTyA E I n Γ (.app pinStructm pinIdTermA) (.app pinStructM (.app (.const 51 []) pinIdTermA)) :=
  .app Γ pinStructm pinIdTermA pinIdPropA (.app pinStructM (.app (.const 51 []) (.bvar 0))) pinIdPropLvA (.succ .zero)
    (.succ .zero) (pinStructMAppTy h50 _ (pinStructMkAppTy h50 h51 (.bvar 0) pinStructFieldVarTy))
    (pinStructMAppTy h50 _ (pinStructMkAppTy h50 h51 _ pinIdTermTy)) (pinStructmTy h50 h51) pinIdTermTy

/-- THE DERIVATION: `rec M m a ≡ S : Prop` at ANY proof `a : S`. Proof irrelevance gives
    `a ≡ mk id`, the congruence carries it into the major, ι's conversion at `mk id` (`hc3`), and β
    reads the minor and both motive instances. ι's conversion is `ConvA.iota` where ι is the head step;
    at the copy's own head step, where the struct arm takes `mk id` (`pinStruct_ctor_arm`), it is
    `ConvA.structIota` (W-1 (e-2), `pinStruct_conv`). -/
def pinStructConv (h50 : E.members 50 = some pinStructFamA) (h51 : E.members 51 = some pinStructMkA)
    (h52 : E.members 52 = some pinStructRecMemberA)
    (hc3 : ConvA E I n Γ (.app pinStructF (.app (.const 51 []) pinIdTermA)) (.app pinStructm pinIdTermA)
      (.app pinStructM (.app (.const 51 []) pinIdTermA)))
    (a : ExprA) (ha : HasTyA E I n Γ a (.const 50 [])) :
    ConvA E I n Γ (.app pinStructF a) (.const 50 []) (.sort .zero) := by
  have hK := pinStructMkAppTy (E := E) (I := I) (n := n) (Γ := Γ) h50 h51 _ pinIdTermTy
  have hIrr : ConvA E I n Γ a (.app (.const 51 []) pinIdTermA) (.const 50 []) :=
    .irr Γ (.const 50 []) a _ (pinStructConstTy h50) ha hK
  have hMM : ConvA E I n Γ (.app pinStructM a) (.app pinStructM (.app (.const 51 []) pinIdTermA)) (.sort (.succ .zero)) :=
    .trans _ _ _ _ _ (pinStructBeta h50 _ ha) (.symm _ _ _ _ (pinStructBeta h50 _ hK))
  have hFI : HasTyA E I n Γ (.app pinStructF (.app (.const 51 []) pinIdTermA)) (.app pinStructM a) :=
    .conv Γ _ _ _ (.succ .zero) (.succ .zero) (pinStructFAppTy h50 h51 h52 _ hK) (pinStructMAppTy h50 _ hK)
      (eqNA_refl _) (pinStructMAppTy h50 _ ha) (.symm _ _ _ _ hMM)
  have c2 : ConvA E I n Γ (.app pinStructF a) (.app pinStructF (.app (.const 51 []) pinIdTermA)) (.app pinStructM a) :=
    .app Γ pinStructF pinStructF a _ (.const 50 []) (.app pinStructM (.bvar 0)) .zero (.succ .zero)
      (.refl Γ pinStructF _ (pinStructFTy h50 h51 h52)) hIrr (pinStructMAppTy h50 (.bvar 0) (pinStructVar0Ty h50)) hFI
  have c4 : ConvA E I n Γ (.app pinStructm pinIdTermA) (.const 50 []) (.app pinStructM (.app (.const 51 []) pinIdTermA)) :=
    .beta Γ pinIdPropA pinIdPropLvA (.const 50 []) pinIdTermA (.app pinStructM (.app (.const 51 []) (.bvar 0)))
      pinIdPropTy (pinStructAtMkTy h50 h51 (.bvar 0) pinStructFieldVarTy) pinIdTermTy (pinStructAtMkTy h50 h51 _ pinIdTermTy)
  have c2' := ConvA.tyConv Γ _ _ _ (.sort .zero) (.succ .zero) (.succ .zero) (.succ .zero) c2
    (pinStructMAppTy h50 _ ha) (eqNA_refl _) (.sort Γ .zero) (eqNA_refl _) (pinStructBeta h50 _ ha)
  have c34' := ConvA.tyConv Γ _ _ _ (.sort .zero) (.succ .zero) (.succ .zero) (.succ .zero)
    (.trans _ _ _ _ _ hc3 c4) (pinStructMAppTy h50 _ hK) (eqNA_refl _) (.sort Γ .zero) (eqNA_refl _) (pinStructBeta h50 _ hK)
  exact .trans _ _ _ _ _ c2' c34'

end StructTooth

/-! ### (9c) `Loop`: one recursive proof field -/
def pinLoopFamA : CheckedMemberA := ⟨.inductiveM, 0, .sort .zero, none, 0, none⟩
/-- `mk : Loop → Loop`: one field, a proof, directly recursive. -/
def pinLoopMkA : CheckedMemberA := ⟨.constructorM, 0, .pi (.const 60 []) .zero (.const 60 []) .zero, none, 0, some (.pi (.const 60 []) .zero (.const 60 []) .zero)⟩

def pinLoopFamViewA : FamViewA pinLoopFamA where
  params := []
  indices := []
  sort := .zero
  stored := rfl
  nparams := rfl
  profile := .inl (fun _ => rfl)

def pinLoopFamEnvA : ResolvedEnvA := extendEnvA emptyEnvA 60 pinLoopFamA

def pinLoopConstTy (h : E.members 60 = some pinLoopFamA) :
    HasTyA E I n Γ (.const 60 []) (.sort .zero) :=
  .const Γ 60 [] pinLoopFamA (.succ .zero) h rfl rfl (.sort Γ .zero)

def pinLoopMkPiTy (h60 : E.members 60 = some pinLoopFamA) :
    HasTyA E I n Γ pinLoopMkA.mtypeA (.sort (.imax .zero .zero)) :=
  .pi Γ (.const 60 []) .zero (.const 60 []) .zero (pinLoopConstTy h60) (pinLoopConstTy h60)

def pinLoopMkViewA (I : IotaIfaceA) :
    CtorViewA emptyEnvA I 60 pinLoopFamA pinLoopFamViewA pinLoopMkA where
  mirrors := []
  fields := [.drec []]
  res := []
  stored := rfl
  mirrorsConv := .nil []
  typed := .drec [] 0 [] [] [] (.nil .zero) (.nil [] 0 [] (.nil .zero))
  univI := fun _ _ _ _ h => by cases List.mem_singleton.mp h
  drecD_typed := drecDTypedA_of_noDelta (fun _ h => by cases List.mem_singleton.mp h; trivial)
  normConv := ⟨.refl [] _⟩
  normTyped := ⟨_, ⟨pinLoopMkPiTy (E := extendEnvA emptyEnvA 60 pinLoopFamA) rfl⟩⟩
  univ := fun _ _ h => by cases List.mem_singleton.mp h

section LoopTy
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}

def pinLoopVarTy (h60 : E.members 60 = some pinLoopFamA) (i : Nat)
    (h : lookupTypeA Γ i = some (.const 60 [])) : HasTyA E I n Γ (.bvar i) (.const 60 []) :=
  .bvar Γ i (.const 60 []) .zero h (pinLoopConstTy h60)

def pinLoopMkConstTy (h60 : E.members 60 = some pinLoopFamA) (h61 : E.members 61 = some pinLoopMkA) :
    HasTyA E I n Γ (.const 61 []) pinLoopMkA.mtypeA :=
  .const Γ 61 [] pinLoopMkA (.imax .zero .zero) h61 rfl rfl (pinLoopMkPiTy h60)

def pinLoopMkAppTy (h60 : E.members 60 = some pinLoopFamA) (h61 : E.members 61 = some pinLoopMkA)
    (a : ExprA) (ha : HasTyA E I n Γ a (.const 60 [])) :
    HasTyA E I n Γ (.app (.const 61 []) a) (.const 60 []) :=
  .app Γ (.const 61 []) a (.const 60 []) (.const 60 []) .zero .zero .zero (pinLoopConstTy h60)
    (pinLoopConstTy h60) (pinLoopMkConstTy h60 h61) ha

end LoopTy

def pinLoopMkGroupA (I : IotaIfaceA) :
    GroupCtorA I emptyEnvA 60 pinLoopFamA pinLoopFamViewA where
  ref := 61
  member := pinLoopMkA
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := fun _ => rfl
  u := .imax .zero .zero
  hT := pinLoopMkPiTy (E := pinLoopFamEnvA) rfl
  hlvl := rfl
  view := pinLoopMkViewA I
  hnorm := rfl
  hclN := fun _ => rfl
  hlvlN := rfl

def pinLoopCs (I : IotaIfaceA) : List (GroupCtorA I emptyEnvA 60 pinLoopFamA pinLoopFamViewA) :=
  [pinLoopMkGroupA I]

abbrev pinLoopMotTyAt (u : Level) : ExprA := .pi (.const 60 []) .zero (.sort u) (.succ u)
abbrev pinLoopMotSortAt (u : Level) : Level := .imax .zero (.succ u)
/-- under the motive and the field `l`: `Π (ih : motive l), motive (mk l)`. -/
abbrev pinLoopIhPiAt (u : Level) : ExprA :=
  .pi (.app (.bvar 1) (.bvar 0)) u (.app (.bvar 2) (.app (.const 61 []) (.bvar 1))) u
abbrev pinLoopMinorDomAt (u : Level) : ExprA := .pi (.const 60 []) .zero (pinLoopIhPiAt u) (.imax u u)
abbrev pinLoopMinorDomSortAt (u : Level) : Level := .imax .zero (.imax u u)
abbrev pinLoopMajorTyAt (u : Level) : ExprA := .pi (.const 60 []) .zero (.app (.bvar 2) (.bvar 0)) u
abbrev pinLoopMajorSortAt (u : Level) : Level := .imax .zero u
abbrev pinLoopMinorPiAt (u : Level) : ExprA :=
  .pi (pinLoopMinorDomAt u) (pinLoopMinorDomSortAt u) (pinLoopMajorTyAt u) (pinLoopMajorSortAt u)
abbrev pinLoopMinorPiSortAt (u : Level) : Level := .imax (pinLoopMinorDomSortAt u) (pinLoopMajorSortAt u)
/-- `Π (motive : Loop → Sort u) (m : Π (l : Loop) (ih : motive l), motive (mk l)) (t : Loop), motive t`. -/
def pinLoopRecTyAt (u : Level) : ExprA :=
  .pi (pinLoopMotTyAt u) (pinLoopMotSortAt u) (pinLoopMinorPiAt u) (pinLoopMinorPiSortAt u)

def pinLoopRecMemberA : CheckedMemberA := ⟨.recursorM, 1, pinLoopRecTyAt (.param 0), none, 0, none⟩

theorem pinLoopGroupRec_stored (I : IotaIfaceA) :
    pinLoopRecMemberA.mtypeA = groupRecTypeA pinLoopFamViewA (pinLoopCs I) .anySort := rfl

section LoopRecTy
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}

def pinLoopMotTyTy (u : Level) (h60 : E.members 60 = some pinLoopFamA) :
    HasTyA E I n Γ (pinLoopMotTyAt u) (.sort (pinLoopMotSortAt u)) :=
  .pi Γ (.const 60 []) .zero (.sort u) (.succ u) (pinLoopConstTy h60) (.sort _ u)

def pinLoopMotAppTy (u : Level) (h60 : E.members 60 = some pinLoopFamA) (i : Nat) (a : ExprA)
    (hm : lookupTypeA Γ i = some (pinLoopMotTyAt u)) (ha : HasTyA E I n Γ a (.const 60 [])) :
    HasTyA E I n Γ (.app (.bvar i) a) (.sort u) :=
  .app Γ (.bvar i) a (.const 60 []) (.sort u) .zero (.succ u) (.succ u) (.sort _ u) (.sort Γ u)
    (.bvar Γ i (pinLoopMotTyAt u) (pinLoopMotSortAt u) hm (pinLoopMotTyTy u h60)) ha

def pinLoopMinorPiTy (u : Level) (h60 : E.members 60 = some pinLoopFamA)
    (h61 : E.members 61 = some pinLoopMkA) :
    HasTyA E I n (.assumption (pinLoopMotTyAt u) :: Γ) (pinLoopMinorPiAt u) (.sort (pinLoopMinorPiSortAt u)) :=
  .pi _ (pinLoopMinorDomAt u) (pinLoopMinorDomSortAt u) (pinLoopMajorTyAt u) (pinLoopMajorSortAt u)
    (.pi _ (.const 60 []) .zero (pinLoopIhPiAt u) (.imax u u) (pinLoopConstTy h60)
      (.pi _ (.app (.bvar 1) (.bvar 0)) u (.app (.bvar 2) (.app (.const 61 []) (.bvar 1))) u
        (pinLoopMotAppTy u h60 1 (.bvar 0) rfl (pinLoopVarTy h60 0 rfl))
        (pinLoopMotAppTy u h60 2 _ rfl (pinLoopMkAppTy h60 h61 (.bvar 1) (pinLoopVarTy h60 1 rfl)))))
    (.pi _ (.const 60 []) .zero (.app (.bvar 2) (.bvar 0)) u (pinLoopConstTy h60)
      (pinLoopMotAppTy u h60 2 (.bvar 0) rfl (pinLoopVarTy h60 0 rfl)))

def pinLoopRecTyTy (u : Level) (h60 : E.members 60 = some pinLoopFamA)
    (h61 : E.members 61 = some pinLoopMkA) :
    HasTyA E I n Γ (pinLoopRecTyAt u) (.sort (.imax (pinLoopMotSortAt u) (pinLoopMinorPiSortAt u))) :=
  .pi Γ (pinLoopMotTyAt u) (pinLoopMotSortAt u) (pinLoopMinorPiAt u) (pinLoopMinorPiSortAt u)
    (pinLoopMotTyTy u h60) (pinLoopMinorPiTy u h60 h61)

end LoopRecTy

theorem boundOkB_pinLoopRecTyA : boundOkB 0 (pinLoopRecTyAt (.param 0)) = true := rfl

theorem liftA_pinLoopRecTyA (k : Nat) : liftA k 1 (pinLoopRecTyAt (.param 0)) = pinLoopRecTyAt (.param 0) :=
  liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ boundOkB_pinLoopRecTyA)

def pinLoopGroupRecA (I : IotaIfaceA) :
    GroupRecA I emptyEnvA 60 pinLoopFamA pinLoopFamViewA (pinLoopCs I) where
  member := pinLoopRecMemberA
  hcls := rfl
  hnobody := rfl
  hnp := rfl
  elim := .anySort
  harity := rfl
  stored := pinLoopGroupRec_stored I
  hclT := liftA_pinLoopRecTyA
  u := .imax (pinLoopMotSortAt (.param 0)) (pinLoopMinorPiSortAt (.param 0))
  hT := pinLoopRecTyTy (.param 0) rfl rfl
  hlvl := rfl

def pinLoopRecEnvA (I : IotaIfaceA) : ResolvedEnvA :=
  groupRecEnvA (pinLoopCs I) (pinLoopGroupRecA I)

/-- `Loop`, `mk` and the derived AnySort recursor, by `EnvWfA.groupRec`. -/
def pinLoopGroupRecWfA (I : IotaIfaceA) : EnvWfA I (pinLoopRecEnvA I) :=
  .groupRec emptyEnvA 60 pinLoopFamA (.succ .zero)
    .empty rfl rfl (fun _ => rfl) (.sort [] .zero) rfl
    pinLoopFamViewA (pinLoopCs I) ⟨rfl, rfl⟩ rfl (pinLoopGroupRecA I) rfl

def pinLoopEnvA : ResolvedEnvA :=
  extendEnvA (extendEnvA pinLoopFamEnvA 61 pinLoopMkA) 62 pinLoopRecMemberA

theorem pinLoopRecEnvA_eq (I : IotaIfaceA) : pinLoopRecEnvA I = pinLoopEnvA := rfl

def pinLoop_wf : EnvWfA (iotaIfaceA pinLoopEnvA) pinLoopEnvA :=
  pinLoopRecEnvA_eq (iotaIfaceA pinLoopEnvA) ▸ pinLoopGroupRecWfA (iotaIfaceA pinLoopEnvA)

theorem pinLoop_mem {r : Nat} {m : CheckedMemberA} (hm : pinLoopEnvA.members r = some m) :
    (r = 60 ∧ m = pinLoopFamA) ∨ (r = 61 ∧ m = pinLoopMkA) ∨ (r = 62 ∧ m = pinLoopRecMemberA) := by
  revert hm
  unfold pinLoopEnvA pinLoopFamEnvA
  simp only [extendEnvA, emptyEnvA]
  intro hm
  by_cases h62 : r = 62
  · subst h62
    simp only [if_pos rfl] at hm
    cases hm
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · simp only [if_neg h62] at hm
    by_cases h61 : r = 61
    · subst h61
      simp only [if_pos rfl] at hm
      cases hm
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · simp only [if_neg h61] at hm
      by_cases h60 : r = 60
      · subst h60
        simp only [if_pos rfl] at hm
        cases hm
        exact Or.inl ⟨rfl, rfl⟩
      · simp only [if_neg h60] at hm
        cases hm

theorem pinLoop_small : SmallIndexProfileA pinLoopEnvA := by
  intro r m u₀ hm hc _ v hv _ _ _ _ _ _
  rcases pinLoop_mem hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact absurd hv (List.not_mem_nil v)
  · exact MemberClass.noConfusion hc
  · exact MemberClass.noConfusion hc

theorem pinLoop_notUnit : unitGroupA 62 pinLoopRecMemberA = false := by decide

theorem pinLoop_not_propElim : ¬ PropElimOnlyA pinLoopEnvA := by
  intro h
  have := h 62 pinLoopRecMemberA (.const 60 []) 60 [] pinLoopFamA .zero rfl rfl rfl rfl rfl rfl rfl
    (fun _ => rfl) (by decide) pinLoop_notUnit _ rfl
  cases this

section LoopTooth
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA}

/-- the motive `λ (_ : Loop). Prop`. -/
abbrev pinLoopM : ExprA := .lam (.const 60 []) .zero (.sort .zero)
/-- the minor's body under `l` and `ih`: `ih → ih`. -/
abbrev pinLoopBody : ExprA := .pi (.bvar 0) .zero (.bvar 1) .zero
abbrev pinLoopIhLam : ExprA := .lam (.app pinLoopM (.bvar 0)) (.succ .zero) pinLoopBody
/-- the minor `λ (l : Loop) (ih : M l). ih → ih`. -/
abbrev pinLoopm : ExprA := .lam (.const 60 []) .zero pinLoopIhLam
/-- `rec.{1} (λ _. Prop) (λ l ih. ih → ih)`. -/
abbrev pinLoopF : ExprA := .app (.app (.const 62 [.succ .zero]) pinLoopM) pinLoopm
abbrev pinLoopIhPiM : ExprA :=
  .pi (.app pinLoopM (.bvar 0)) (.succ .zero) (.app pinLoopM (.app (.const 61 []) (.bvar 1))) (.succ .zero)
abbrev pinLoopMinorDomM : ExprA := .pi (.const 60 []) .zero pinLoopIhPiM (.imax (.succ .zero) (.succ .zero))
abbrev pinLoopMajorM : ExprA := .pi (.const 60 []) .zero (.app pinLoopM (.bvar 0)) (.succ .zero)
/-- `t ↦ rec M m t` at the variable `0`, and its self-arrow. -/
abbrev pinLoopA : ExprA := .app pinLoopF (.bvar 0)
abbrev pinLoopArrow : ExprA := .pi pinLoopA .zero (.app pinLoopF (.bvar 1)) .zero

def pinLoopMTy (h60 : E.members 60 = some pinLoopFamA) :
    HasTyA E I n Γ pinLoopM (pinLoopMotTyAt (.succ .zero)) :=
  .lam Γ (.const 60 []) .zero (.sort .zero) (.sort (.succ .zero)) (.succ (.succ .zero))
    (pinLoopConstTy h60) (.sort _ (.succ .zero)) (.sort _ .zero)

def pinLoopMAppTy (h60 : E.members 60 = some pinLoopFamA) (a : ExprA)
    (ha : HasTyA E I n Γ a (.const 60 [])) :
    HasTyA E I n Γ (.app pinLoopM a) (.sort (.succ .zero)) :=
  .app Γ pinLoopM a (.const 60 []) (.sort (.succ .zero)) .zero (.succ (.succ .zero)) (.succ (.succ .zero))
    (.sort _ (.succ .zero)) (.sort Γ (.succ .zero)) (pinLoopMTy h60) ha

def pinLoopBeta (h60 : E.members 60 = some pinLoopFamA) (a : ExprA) (ha : HasTyA E I n Γ a (.const 60 [])) :
    ConvA E I n Γ (.app pinLoopM a) (.sort .zero) (.sort (.succ .zero)) :=
  .beta Γ (.const 60 []) .zero (.sort .zero) a (.sort (.succ .zero)) (pinLoopConstTy h60)
    (.sort _ .zero) ha (.sort Γ .zero)

/-- a term at `M a` is a proposition, through β. -/
def pinLoopAsProp (h60 : E.members 60 = some pinLoopFamA) {e a : ExprA}
    (ha : HasTyA E I n Γ a (.const 60 [])) (he : HasTyA E I n Γ e (.app pinLoopM a)) :
    HasTyA E I n Γ e (.sort .zero) :=
  .conv Γ e _ _ (.succ .zero) (.succ .zero) he (pinLoopMAppTy h60 a ha) (eqNA_refl _) (.sort Γ .zero)
    (pinLoopBeta h60 a ha)

/-- a proposition at `sort (imax 0 0)` is at `M a`: the sorts agree and β reads the motive. -/
def pinLoopAtM (h60 : E.members 60 = some pinLoopFamA) {e a : ExprA}
    (ha : HasTyA E I n Γ a (.const 60 [])) (he : HasTyA E I n Γ e (.sort (.imax .zero .zero))) :
    HasTyA E I n Γ e (.app pinLoopM a) :=
  .conv Γ e _ _ (.succ (.imax .zero .zero)) (.succ .zero) he (.sort Γ (.imax .zero .zero)) (fun _ => rfl)
    (pinLoopMAppTy h60 a ha)
    (.trans _ _ (.sort .zero) _ _ (.symm _ _ _ _ (.sorts _ .zero (.imax .zero .zero) (fun _ => rfl)))
      (.symm _ _ _ _ (pinLoopBeta h60 a ha)))

/-- `ih → ih : sort (imax 0 0)` under `l` and `ih : M l`. -/
def pinLoopBodyTy (h60 : E.members 60 = some pinLoopFamA) :
    HasTyA E I n (.assumption (.app pinLoopM (.bvar 0)) :: .assumption (.const 60 []) :: Γ) pinLoopBody
      (.sort (.imax .zero .zero)) :=
  .pi _ (.bvar 0) .zero (.bvar 1) .zero
    (pinLoopAsProp h60 (pinLoopVarTy h60 1 rfl)
      (.bvar _ 0 (.app pinLoopM (.bvar 1)) (.succ .zero) rfl (pinLoopMAppTy h60 _ (pinLoopVarTy h60 1 rfl))))
    (pinLoopAsProp h60 (pinLoopVarTy h60 2 rfl)
      (.bvar _ 1 (.app pinLoopM (.bvar 2)) (.succ .zero) rfl (pinLoopMAppTy h60 _ (pinLoopVarTy h60 2 rfl))))

def pinLoopIhPiMTy (h60 : E.members 60 = some pinLoopFamA) (h61 : E.members 61 = some pinLoopMkA) :
    HasTyA E I n (.assumption (.const 60 []) :: Γ) pinLoopIhPiM (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi _ (.app pinLoopM (.bvar 0)) (.succ .zero) (.app pinLoopM (.app (.const 61 []) (.bvar 1))) (.succ .zero)
    (pinLoopMAppTy h60 _ (pinLoopVarTy h60 0 rfl))
    (pinLoopMAppTy h60 _ (pinLoopMkAppTy h60 h61 _ (pinLoopVarTy h60 1 rfl)))

def pinLoopIhLamTy (h60 : E.members 60 = some pinLoopFamA) (h61 : E.members 61 = some pinLoopMkA) :
    HasTyA E I n (.assumption (.const 60 []) :: Γ) pinLoopIhLam pinLoopIhPiM :=
  .lam _ (.app pinLoopM (.bvar 0)) (.succ .zero) pinLoopBody (.app pinLoopM (.app (.const 61 []) (.bvar 1)))
    (.succ .zero) (pinLoopMAppTy h60 _ (pinLoopVarTy h60 0 rfl))
    (pinLoopMAppTy h60 _ (pinLoopMkAppTy h60 h61 _ (pinLoopVarTy h60 1 rfl)))
    (pinLoopAtM h60 (pinLoopMkAppTy h60 h61 _ (pinLoopVarTy h60 1 rfl)) (pinLoopBodyTy h60))

def pinLoopmTy (h60 : E.members 60 = some pinLoopFamA) (h61 : E.members 61 = some pinLoopMkA) :
    HasTyA E I n Γ pinLoopm pinLoopMinorDomM :=
  .lam Γ (.const 60 []) .zero pinLoopIhLam pinLoopIhPiM (.imax (.succ .zero) (.succ .zero))
    (pinLoopConstTy h60) (pinLoopIhPiMTy h60 h61) (pinLoopIhLamTy h60 h61)

def pinLoopRecCTy (h60 : E.members 60 = some pinLoopFamA) (h61 : E.members 61 = some pinLoopMkA)
    (h62 : E.members 62 = some pinLoopRecMemberA) :
    HasTyA E I n Γ (.const 62 [.succ .zero]) (pinLoopRecTyAt (.succ .zero)) :=
  .const Γ 62 [.succ .zero] pinLoopRecMemberA _ h62 rfl rfl (pinLoopRecTyTy (.succ .zero) h60 h61)

def pinLoopMajorMTy (h60 : E.members 60 = some pinLoopFamA) {Δ : LCtxA} :
    HasTyA E I n Δ pinLoopMajorM (.sort (pinLoopMajorSortAt (.succ .zero))) :=
  .pi Δ (.const 60 []) .zero (.app pinLoopM (.bvar 0)) (.succ .zero) (pinLoopConstTy h60)
    (pinLoopMAppTy h60 (.bvar 0) (pinLoopVarTy h60 0 rfl))

def pinLoopF0Ty (h60 : E.members 60 = some pinLoopFamA) (h61 : E.members 61 = some pinLoopMkA)
    (h62 : E.members 62 = some pinLoopRecMemberA) :
    HasTyA E I n Γ (.app (.const 62 [.succ .zero]) pinLoopM)
      (.pi pinLoopMinorDomM (pinLoopMinorDomSortAt (.succ .zero)) pinLoopMajorM (pinLoopMajorSortAt (.succ .zero))) :=
  .app Γ _ pinLoopM (pinLoopMotTyAt (.succ .zero)) (pinLoopMinorPiAt (.succ .zero))
    (pinLoopMotSortAt (.succ .zero)) (pinLoopMinorPiSortAt (.succ .zero)) (pinLoopMinorPiSortAt (.succ .zero))
    (pinLoopMinorPiTy (.succ .zero) h60 h61)
    (.pi Γ _ _ _ _ (.pi Γ (.const 60 []) .zero _ _ (pinLoopConstTy h60) (pinLoopIhPiMTy h60 h61))
      (pinLoopMajorMTy h60))
    (pinLoopRecCTy h60 h61 h62) (pinLoopMTy h60)

def pinLoopFTy (h60 : E.members 60 = some pinLoopFamA) (h61 : E.members 61 = some pinLoopMkA)
    (h62 : E.members 62 = some pinLoopRecMemberA) :
    HasTyA E I n Γ pinLoopF pinLoopMajorM :=
  .app Γ _ pinLoopm pinLoopMinorDomM pinLoopMajorM (pinLoopMinorDomSortAt (.succ .zero))
    (pinLoopMajorSortAt (.succ .zero)) (pinLoopMajorSortAt (.succ .zero)) (pinLoopMajorMTy h60)
    (pinLoopMajorMTy h60) (pinLoopF0Ty h60 h61 h62) (pinLoopmTy h60 h61)

def pinLoopFAppTy (h60 : E.members 60 = some pinLoopFamA) (h61 : E.members 61 = some pinLoopMkA)
    (h62 : E.members 62 = some pinLoopRecMemberA) (a : ExprA) (ha : HasTyA E I n Γ a (.const 60 [])) :
    HasTyA E I n Γ (.app pinLoopF a) (.app pinLoopM a) :=
  .app Γ pinLoopF a (.const 60 []) (.app pinLoopM (.bvar 0)) .zero (.succ .zero) (.succ .zero)
    (pinLoopMAppTy h60 (.bvar 0) (pinLoopVarTy h60 0 rfl)) (pinLoopMAppTy h60 a ha) (pinLoopFTy h60 h61 h62) ha

/-- `rec M m t → rec M m t : sort (imax 0 0)` in the context `t : Loop`. -/
def pinLoopArrowTy (h60 : E.members 60 = some pinLoopFamA) (h61 : E.members 61 = some pinLoopMkA)
    (h62 : E.members 62 = some pinLoopRecMemberA) :
    HasTyA E I n (.assumption (.const 60 []) :: Γ) pinLoopArrow (.sort (.imax .zero .zero)) :=
  .pi _ pinLoopA .zero (.app pinLoopF (.bvar 1)) .zero
    (pinLoopAsProp h60 (pinLoopVarTy h60 0 rfl) (pinLoopFAppTy h60 h61 h62 _ (pinLoopVarTy h60 0 rfl)))
    (pinLoopAsProp h60 (pinLoopVarTy h60 1 rfl) (pinLoopFAppTy h60 h61 h62 _ (pinLoopVarTy h60 1 rfl)))

/-- THE DERIVATION, in the context `t : Loop`: `rec M m t ≡ (rec M m t → rec M m t) : Prop`. Proof
    irrelevance gives `t ≡ mk t`; ι fires on `mk t` and hands the minor the field and the recursive
    call, `m t (rec M m t)`; β twice reads the minor. -/
def pinLoopConv (h60 : E.members 60 = some pinLoopFamA) (h61 : E.members 61 = some pinLoopMkA)
    (h62 : E.members 62 = some pinLoopRecMemberA)
    (hι : I.rel E (.assumption (.const 60 []) :: Γ) (.app pinLoopF (.app (.const 61 []) (.bvar 0)))
      (.app (.app pinLoopm (.bvar 0)) pinLoopA)) :
    ConvA E I n (.assumption (.const 60 []) :: Γ) pinLoopA pinLoopArrow (.sort .zero) := by
  have hx := pinLoopVarTy (E := E) (I := I) (n := n) (Γ := .assumption (.const 60 []) :: Γ) h60 0 rfl
  have hK := pinLoopMkAppTy h60 h61 _ hx
  have hFx := pinLoopFAppTy h60 h61 h62 _ hx
  have hIrr : ConvA E I n _ (.bvar 0) (.app (.const 61 []) (.bvar 0)) (.const 60 []) :=
    .irr _ (.const 60 []) (.bvar 0) _ (pinLoopConstTy h60) hx hK
  have hMM : ConvA E I n _ (.app pinLoopM (.bvar 0)) (.app pinLoopM (.app (.const 61 []) (.bvar 0)))
      (.sort (.succ .zero)) :=
    .trans _ _ _ _ _ (pinLoopBeta h60 _ hx) (.symm _ _ _ _ (pinLoopBeta h60 _ hK))
  have hFI : HasTyA E I n _ (.app pinLoopF (.app (.const 61 []) (.bvar 0))) (.app pinLoopM (.bvar 0)) :=
    .conv _ _ _ _ (.succ .zero) (.succ .zero) (pinLoopFAppTy h60 h61 h62 _ hK) (pinLoopMAppTy h60 _ hK)
      (eqNA_refl _) (pinLoopMAppTy h60 _ hx) (.symm _ _ _ _ hMM)
  -- congruence at the major
  have c2 : ConvA E I n _ pinLoopA (.app pinLoopF (.app (.const 61 []) (.bvar 0))) (.app pinLoopM (.bvar 0)) :=
    .app _ pinLoopF pinLoopF (.bvar 0) _ (.const 60 []) (.app pinLoopM (.bvar 0)) .zero (.succ .zero)
      (.refl _ pinLoopF _ (pinLoopFTy h60 h61 h62)) hIrr (pinLoopMAppTy h60 (.bvar 0) (pinLoopVarTy h60 0 rfl)) hFI
  -- the minor at the field: `m t : Π (ih : M t), M (mk t)`
  have hmx : HasTyA E I n _ (.app pinLoopm (.bvar 0)) pinLoopIhPiM :=
    .app _ pinLoopm (.bvar 0) (.const 60 []) pinLoopIhPiM .zero (.imax (.succ .zero) (.succ .zero))
      (.imax (.succ .zero) (.succ .zero)) (pinLoopIhPiMTy h60 h61) (pinLoopIhPiMTy h60 h61) (pinLoopmTy h60 h61) hx
  -- ι's reduct, `m t (rec M m t) : M (mk t)`
  have hR : HasTyA E I n _ (.app (.app pinLoopm (.bvar 0)) pinLoopA) (.app pinLoopM (.app (.const 61 []) (.bvar 0))) :=
    .app _ _ pinLoopA (.app pinLoopM (.bvar 0)) (.app pinLoopM (.app (.const 61 []) (.bvar 1))) (.succ .zero)
      (.succ .zero) (.succ .zero) (pinLoopMAppTy h60 _ (pinLoopMkAppTy h60 h61 _ (pinLoopVarTy (Γ := .assumption (.app pinLoopM (.bvar 0)) :: .assumption (.const 60 []) :: Γ) h60 1 rfl)))
      (pinLoopMAppTy h60 _ hK) hmx hFx
  have c3 : ConvA E I n _ (.app pinLoopF (.app (.const 61 []) (.bvar 0))) (.app (.app pinLoopm (.bvar 0)) pinLoopA)
      (.app pinLoopM (.app (.const 61 []) (.bvar 0))) :=
    .iota _ _ _ _ hι (pinLoopFAppTy h60 h61 h62 _ hK) hR
  -- β at the field: `m t ≡ λ (ih : M t). ih → ih`
  have c4a : ConvA E I n _ (.app pinLoopm (.bvar 0)) pinLoopIhLam pinLoopIhPiM :=
    .beta _ (.const 60 []) .zero pinLoopIhLam (.bvar 0) pinLoopIhPiM (pinLoopConstTy h60)
      (pinLoopIhLamTy h60 h61) hx (pinLoopIhLamTy h60 h61)
  have hArr := pinLoopArrowTy (Γ := Γ) (E := E) (I := I) (n := n) h60 h61 h62
  have c4b : ConvA E I n _ (.app (.app pinLoopm (.bvar 0)) pinLoopA) (.app pinLoopIhLam pinLoopA)
      (.app pinLoopM (.app (.const 61 []) (.bvar 0))) :=
    .app _ _ _ pinLoopA pinLoopA (.app pinLoopM (.bvar 0)) (.app pinLoopM (.app (.const 61 []) (.bvar 1)))
      (.succ .zero) (.succ .zero) c4a (.refl _ pinLoopA _ hFx)
      (pinLoopMAppTy h60 _ (pinLoopMkAppTy h60 h61 _ (pinLoopVarTy (Γ := .assumption (.app pinLoopM (.bvar 0)) :: .assumption (.const 60 []) :: Γ) h60 1 rfl)))
      (.app _ pinLoopIhLam pinLoopA (.app pinLoopM (.bvar 0)) (.app pinLoopM (.app (.const 61 []) (.bvar 1)))
        (.succ .zero) (.succ .zero) (.succ .zero)
        (pinLoopMAppTy h60 _ (pinLoopMkAppTy h60 h61 _ (pinLoopVarTy (Γ := .assumption (.app pinLoopM (.bvar 0)) :: .assumption (.const 60 []) :: Γ) h60 1 rfl))) (pinLoopMAppTy h60 _ hK)
        (pinLoopIhLamTy h60 h61) hFx)
  -- β at the recursive call: `(λ ih. ih → ih) (rec M m t) ≡ rec M m t → rec M m t`
  have c4c : ConvA E I n _ (.app pinLoopIhLam pinLoopA) pinLoopArrow (.app pinLoopM (.app (.const 61 []) (.bvar 0))) :=
    .beta _ (.app pinLoopM (.bvar 0)) (.succ .zero) pinLoopBody pinLoopA
      (.app pinLoopM (.app (.const 61 []) (.bvar 1))) (pinLoopMAppTy h60 _ hx)
      (pinLoopAtM h60 (pinLoopMkAppTy h60 h61 _ (pinLoopVarTy (Γ := .assumption (.app pinLoopM (.bvar 0)) :: .assumption (.const 60 []) :: Γ) h60 1 rfl)) (pinLoopBodyTy h60)) hFx
      (pinLoopAtM h60 hK hArr)
  have c2' := ConvA.tyConv _ _ _ _ (.sort .zero) (.succ .zero) (.succ .zero) (.succ .zero) c2
    (pinLoopMAppTy h60 _ hx) (eqNA_refl _) (.sort _ .zero) (eqNA_refl _) (pinLoopBeta h60 _ hx)
  have c3' := ConvA.tyConv _ _ _ _ (.sort .zero) (.succ .zero) (.succ .zero) (.succ .zero)
    (.trans _ _ _ _ _ c3 (.trans _ _ _ _ _ c4b c4c)) (pinLoopMAppTy h60 _ hK) (eqNA_refl _) (.sort _ .zero)
    (eqNA_refl _) (pinLoopBeta h60 _ hK)
  exact .trans _ _ _ _ _ c2' c3'

/-- THE REFUTATION, once: wherever `Loop`, `mk` and the AnySort recursor sit at `60`–`62`, the
    semantic environment FAILS. The fundamental theorem relates `rec M m t` and its own self-arrow as
    propositions, and no proposition is `PropEqA`-related to its own self-arrow
    (`propEqA_not_selfArrow`). The proof does not ask what `rec M m t` reduces to. -/
theorem pinLoop_envSem_false_at {ρ₀ : Nat → Nat} (hW : EnvWfA (iotaIfaceA E) E)
    (h60 : E.members 60 = some pinLoopFamA) (h61 : E.members 61 = some pinLoopMkA)
    (h62 : E.members 62 = some pinLoopRecMemberA) (hΓ : CtxWfA E (iotaIfaceA E) n Γ)
    (hι : (iotaIfaceA E).rel E (.assumption (.const 60 []) :: Γ)
      (.app pinLoopF (.app (.const 61 []) (.bvar 0))) (.app (.app pinLoopm (.bvar 0)) pinLoopA))
    (hρ : PosValA ρ₀) :
    ¬ EnvSemA E (iotaIfaceA E) n ρ₀ := by
  intro hS
  have hE := envWfA_closed hW
  have hN := envWfA_normClosed hW
  have hNC := envWfA_normCtorType hW
  have hΓ' : CtxWfA E (iotaIfaceA E) n (.assumption (.const 60 []) :: Γ) := .assumption hΓ (pinLoopConstTy h60)
  obtain ⟨k₀, h⟩ := fund_conv hE (iotaFnA_lift hE hN) (iotaFnA_subst hE hN) hNC hN (iotaFnA_recHead E) hS hρ
    hΓ' (pinLoopConv h60 h61 h62 hι)
  obtain ⟨_, _, _, _, _, hP⟩ := LRRelA_sortP_elim (u := .zero) rfl (h k₀ (Nat.le_refl _))
  exact propEqA_not_selfArrow hE (iotaFnA_lift hE hN) ⟨hΓ'⟩ hP

end LoopTooth

/-- TOOTH: `Loop` with its AnySort recursor, no axiom, at every positive valuation. -/
theorem pinLoop_envSem_false {n : Nat} {ρ₀ : Nat → Nat} (hρ : PosValA ρ₀) :
    ¬ EnvSemA pinLoopEnvA (iotaIfaceA pinLoopEnvA) n ρ₀ :=
  pinLoop_envSem_false_at (Γ := []) pinLoop_wf rfl rfl rfl .nil ⟨by decide, by decide⟩ hρ

theorem pinLoop_O1_exact (n : Nat) :
    SmallIndexProfileA pinLoopEnvA ∧ ¬ PropElimOnlyA pinLoopEnvA ∧
      ¬ EnvSemA pinLoopEnvA (iotaIfaceA pinLoopEnvA) n (fun _ => 1) :=
  ⟨pinLoop_small, pinLoop_not_propElim, pinLoop_envSem_false posValA_one⟩

/-! ## (10) W-1: the struct arm on `S`

W-1-0 measured the arm for (K-struct) without recursion on `S`; W-1 (a) puts it in the head step
(`structArmA`), and W-1 (e) before ι. At a struct group's (`structGroupA`) recursor spine at its major,
it steps to the minor applied to the major's projections, each projection the recursor itself at motive
level `zero`. It never steps the major. Pinned on `S` (one
field `f : Π P, P → P`, recursor at `52`): the test holds at `S` and fails at the other groups; the
step takes `rec M m t` to the minor at the projection, and `S` after one β; the projection, a proof,
returns to itself after one step and one β; and at a constructor major the arm is the step (W-1 (e)),
while ι contracts to the minor at the constructor's field. -/

/-- `S`'s projection at a major `x`: the recursor at motive level `zero`, motive `λ _. F`, minor
    `λ f. f`. The struct arm builds exactly this term (`pinStructArm_var`). -/
abbrev pinStructProjA (x : ExprA) : ExprA :=
  .app (.app (.app (.const 52 [.zero]) (.lam (.const 50 []) .zero pinIdPropA))
    (.lam pinIdPropA pinIdPropLvA (.bvar 0))) x

/-- the struct test holds at `S`'s recursor, read off its type. -/
theorem pinStruct_struct : structGroupA 52 pinStructRecMemberA = true := by decide
/-- TEETH: it fails at a `Type` family's recursor (Nat), at a constructor-free group's (`False`), at a
    unit group's (`True`: no field), at a recursive field's (`Loop`: the induction hypothesis's sort
    is the motive's) and at an indexed singleton's. -/
theorem pinNat_notStruct : structGroupA 13 pinNatRecMemberA = false := by decide
theorem pinFalse_notStruct : structGroupA 21 pinFalseRecMemberA = false := by decide
theorem pinTrue_notStruct : structGroupA 32 pinTrueRecMemberA = false := by decide
theorem pinLoop_notStruct : structGroupA 62 pinLoopRecMemberA = false := by decide
theorem pinIdx_notStruct : structGroupA 42 pinIdxRecMemberA = false := by decide

/-- the struct arm at `rec M m t`, `t` a variable: the minor `λ f. S` applied to the projection. -/
theorem pinStructArm_var :
    hStepFnA pinStructEnvA (iotaFnA pinStructEnvA) [.assumption (.const 50 [])] (.app pinStructF (.bvar 0)) =
      some (.app pinStructm (pinStructProjA (.bvar 0))) := by
  decide

/-- one β from the arm's reduct reaches `S`, which is weak-head normal: the spine the head step before
    W-1 (a) left stuck reaches the family, where `PropEqA.fam` relates it. -/
theorem pinStructArm_var_beta :
    hStepFnA pinStructEnvA (iotaFnA pinStructEnvA) [.assumption (.const 50 [])]
        (.app pinStructm (pinStructProjA (.bvar 0))) = some (.const 50 []) ∧
      hStepFnA pinStructEnvA (iotaFnA pinStructEnvA) [.assumption (.const 50 [])]
        (.const 50 []) = none := by
  decide

/-- the projection at a variable proof is itself a struct-group spine at its major: the arm takes it to
    the identity minor applied to its own projection. -/
theorem pinStructProj_var_step :
    hStepFnA pinStructEnvA (iotaFnA pinStructEnvA) [.assumption (.const 50 [])]
      (pinStructProjA (.bvar 0)) =
      some (.app (.lam pinIdPropA pinIdPropLvA (.bvar 0)) (pinStructProjA (.bvar 0))) := by
  decide

/-- the projection loops: one arm step and one β give it back. It is a proof, so the loop is harmless
    exactly where nothing asks a proof for a weak-head normal form, and the arm never steps a major. -/
theorem pinStructArm_proj_loop :
    (hStepFnA pinStructEnvA (iotaFnA pinStructEnvA) [.assumption (.const 50 [])]
        (pinStructProjA (.bvar 0))).bind
        (hStepFnA pinStructEnvA (iotaFnA pinStructEnvA) [.assumption (.const 50 [])]) =
      some (pinStructProjA (.bvar 0)) := by
  decide

/-- W-1 (e): at a constructor major the arm is the step, as at every major: the minor applied to the
    major's projection. -/
theorem pinStruct_ctor_arm :
    hStepFnA pinStructEnvA (iotaFnA pinStructEnvA) []
        (.app pinStructF (.app (.const 51 []) pinIdTermA)) =
      some (.app pinStructm (pinStructProjA (.app (.const 51 []) pinIdTermA))) := by
  decide

/-- W-1 (e): ι contracts there to the minor applied to the constructor's field (`pinIdTermA`), as `main`'s
    ι does. The two contracta differ by proof irrelevance alone. -/
theorem pinStruct_ctor_iotaFn :
    iotaFnA pinStructEnvA (.app pinStructF (.app (.const 51 []) pinIdTermA)) =
      some (.app pinStructm pinIdTermA) := by
  decide

/-- TOOTH: so ι there is not the head step, and `ConvA.iota` does not fire (`IotaIfaceA.rel`); ι's rule at
    a struct group is `ConvA.structIota`. -/
theorem pinStruct_ctor_notIotaRel :
    ¬ (iotaIfaceA pinStructEnvA).rel pinStructEnvA [] (.app pinStructF (.app (.const 51 []) pinIdTermA))
      (.app pinStructm pinIdTermA) := by
  intro h
  have h2 : hStepFnA pinStructEnvA (iotaFnA pinStructEnvA) []
      (.app pinStructF (.app (.const 51 []) pinIdTermA)) = some (.app pinStructm pinIdTermA) := h.exec
  rw [pinStruct_ctor_arm] at h2
  exact absurd h2 (by decide)

/-- TOOTH: the redex is at a struct group (`iotaAtStructA`), which the bridge's scope leaves out until W-1
    (e-2). -/
theorem pinStruct_ctor_atStruct :
    iotaAtStructA pinStructEnvA (.app pinStructF (.app (.const 51 []) pinIdTermA)) = true := by
  decide

/-! ## (11) W-1 (c): `EnvSemA` at `S`

`S` is outside `PropElimOnlyA` (`pinStruct_not_propElim`): its recursor eliminates into every sort and
is neither its family's next member nor a unit group's. `PropElimStructA` exempts a struct group's
recursor as well, so it holds at `S` (`pinStruct_propElimStruct`), and the recursors' clause at a struct
group (`recStructAppsA`) discharges `EnvSemA` at `S` (`envSemA_pinStruct`). `Loop` stays outside the
struct profile (`pinLoop_not_propElimStruct`: its recursive field fails the struct test), as it must:
`EnvSemA` fails there (`pinLoop_envSem_false`). -/

/-- W-1 (c): `PropElimStructA` holds at `S` by the struct exemption alone. -/
theorem pinStruct_propElimStruct : PropElimStructA pinStructEnvA := by
  intro r rm _ _ _ _ _ hrm hcl _ _ _ _ _ _ _ _ hns _ _
  rcases pinStruct_mem hrm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, rfl⟩
  · exact MemberClass.noConfusion hcl
  · exact MemberClass.noConfusion hcl
  · rw [pinStruct_struct] at hns
    exact Bool.noConfusion hns

/-- the constructor of `S` has no function-recursive field. -/
theorem pinStruct_noFun : EnvNoFunA pinStructEnvA := by
  intro c cm f fm shapes hc hcl hfam hf hsh s hs j
  rcases pinStruct_mem hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · simp [pinStructFamA] at hcl
  · have h : memberFamRefA pinStructMkA = some 50 := rfl
    rw [h] at hfam
    cases hfam
    have h10 : pinStructEnvA.members 50 = some pinStructFamA := rfl
    rw [h10] at hf
    cases hf
    have hs0 : ctorShapesA 50 pinStructFamA.nparamsA (pinStructMkA.normA.getD pinStructMkA.mtypeA) =
      some [.nonrecursive] := rfl
    rw [hs0] at hsh
    cases hsh
    simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> intro h <;> cases h
  · simp [pinStructRecMemberA] at hcl

/-- W-1 (c), THE PREDICTION: `S` with its AnySort recursor satisfies `EnvSemA` at the concrete ι. -/
theorem envSemA_pinStruct (n : Nat) :
    EnvSemA pinStructEnvA (iotaIfaceA pinStructEnvA) n (fun _ => 1) :=
  envSemA_of_envWfA_recStruct (E := pinStructEnvA) (n := n) (ρ₀ := fun _ => 1)
    pinStruct_wf posValA_one pinStruct_small pinStruct_propElimStruct

/-- TOOTH: the struct exemption does not reach `Loop`'s recursor. -/
theorem pinLoop_not_propElimStruct : ¬ PropElimStructA pinLoopEnvA := by
  intro h
  have := h 62 pinLoopRecMemberA (.const 60 []) 60 [] pinLoopFamA .zero rfl rfl rfl rfl rfl rfl rfl
    (fun _ => rfl) (by decide) pinLoop_notUnit pinLoop_notStruct _ rfl
  cases this

/-! ## (12) W-1 (d): `EnvSemA` at `And`, a struct with parameters

`And` at `70` (`Π (a b : Prop), Prop`), `And.intro` at `71` (two plain fields, `left : a` and
`right : b`) and the derived AnySort recursor at `72`, by `EnvWfA.groupRec`. The struct test holds at
the recursor (`pinAnd_struct`); `And` is outside `PropElimOnlyA` (`pinAnd_not_propElim`) and inside
`PropElimStructA` (`pinAnd_propElimStruct`), and `EnvSemA` holds (`envSemA_pinAnd`): the recursors'
clause at a struct group (W-1 (c)) at a group with parameters. -/

/-- `Prop`, each parameter's domain. -/
abbrev pinAndPropA : ExprA := .sort .zero
/-- `And x y`. -/
abbrev pinAndAppA (x y : ExprA) : ExprA := .app (.app (.const 70 []) x) y
/-- `And.intro x y l r`. -/
abbrev pinAndMkAppA (x y l r : ExprA) : ExprA := .app (.app (.app (.app (.const 71 []) x) y) l) r

/-- `And`'s type: `Π (a b : Prop), Prop`. -/
abbrev pinAndFamTyA : ExprA :=
  .pi pinAndPropA (.succ .zero) (.pi pinAndPropA (.succ .zero) pinAndPropA (.succ .zero))
    (.imax (.succ .zero) (.succ .zero))
abbrev pinAndFamSortA : Level := .imax (.succ .zero) (.imax (.succ .zero) (.succ .zero))

/-- `And.intro`'s type after its first parameter: `Π (b : Prop) (left : a) (right : b), And a b`. -/
abbrev pinAndMkTel1A : ExprA :=
  .pi pinAndPropA (.succ .zero)
    (.pi (.bvar 1) .zero (.pi (.bvar 1) .zero (pinAndAppA (.bvar 3) (.bvar 2)) .zero) (.imax .zero .zero))
    (.imax .zero (.imax .zero .zero))
abbrev pinAndMkTel1SortA : Level := .imax (.succ .zero) (.imax .zero (.imax .zero .zero))
/-- `And.intro`'s type: `Π (a b : Prop) (left : a) (right : b), And a b`. -/
abbrev pinAndMkTyA : ExprA := .pi pinAndPropA (.succ .zero) pinAndMkTel1A pinAndMkTel1SortA
abbrev pinAndMkSortA : Level := .imax (.succ .zero) pinAndMkTel1SortA

def pinAndFamA : CheckedMemberA := ⟨.inductiveM, 0, pinAndFamTyA, none, 2, none⟩
def pinAndMkA : CheckedMemberA := ⟨.constructorM, 0, pinAndMkTyA, none, 0, some pinAndMkTyA⟩

section AndTy
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- a variable at `Prop`. -/
def pinAndPropVarTy {Γ : LCtxA} (i : Nat) (h : lookupTypeA Γ i = some pinAndPropA) :
    HasTyA E I n Γ (.bvar i) pinAndPropA :=
  .bvar Γ i pinAndPropA (.succ .zero) h (.sort Γ .zero)

def pinAndFamTyTy {Γ : LCtxA} : HasTyA E I n Γ pinAndFamTyA (.sort pinAndFamSortA) :=
  .pi Γ pinAndPropA (.succ .zero) _ _ (.sort Γ .zero)
    (.pi _ pinAndPropA (.succ .zero) pinAndPropA (.succ .zero) (.sort _ .zero) (.sort _ .zero))

def pinAndConstTy {Γ : LCtxA} (h70 : E.members 70 = some pinAndFamA) :
    HasTyA E I n Γ (.const 70 []) pinAndFamTyA :=
  .const Γ 70 [] pinAndFamA pinAndFamSortA h70 rfl rfl pinAndFamTyTy

/-- `And x y : Prop` at `x y : Prop`. -/
def pinAndAppTy {Γ : LCtxA} (h70 : E.members 70 = some pinAndFamA) (x y : ExprA)
    (hx : HasTyA E I n Γ x pinAndPropA) (hy : HasTyA E I n Γ y pinAndPropA) :
    HasTyA E I n Γ (pinAndAppA x y) pinAndPropA :=
  .app Γ (.app (.const 70 []) x) y pinAndPropA pinAndPropA (.succ .zero) (.succ .zero) (.succ .zero)
    (.sort _ .zero) (.sort Γ .zero)
    (.app Γ (.const 70 []) x pinAndPropA (.pi pinAndPropA (.succ .zero) pinAndPropA (.succ .zero)) (.succ .zero)
      (.imax (.succ .zero) (.succ .zero)) (.imax (.succ .zero) (.succ .zero))
      (.pi _ pinAndPropA (.succ .zero) pinAndPropA (.succ .zero) (.sort _ .zero) (.sort _ .zero))
      (.pi Γ pinAndPropA (.succ .zero) pinAndPropA (.succ .zero) (.sort Γ .zero) (.sort _ .zero))
      (pinAndConstTy h70) hx)
    hy

/-- `And.intro`'s type after its first parameter, the parameter the context's innermost variable. -/
def pinAndMkTel1Ty {Γ : LCtxA} (h70 : E.members 70 = some pinAndFamA) :
    HasTyA E I n (.assumption pinAndPropA :: Γ) pinAndMkTel1A (.sort pinAndMkTel1SortA) :=
  .pi _ pinAndPropA (.succ .zero) _ _ (.sort _ .zero)
    (.pi _ (.bvar 1) .zero _ _ (pinAndPropVarTy 1 rfl)
      (.pi _ (.bvar 1) .zero _ _ (pinAndPropVarTy 1 rfl)
        (pinAndAppTy h70 (.bvar 3) (.bvar 2) (pinAndPropVarTy 3 rfl) (pinAndPropVarTy 2 rfl))))

def pinAndMkTyTy {Γ : LCtxA} (h70 : E.members 70 = some pinAndFamA) :
    HasTyA E I n Γ pinAndMkTyA (.sort pinAndMkSortA) :=
  .pi Γ pinAndPropA (.succ .zero) _ _ (.sort Γ .zero) (pinAndMkTel1Ty h70)

def pinAndMkConstTy {Γ : LCtxA} (h70 : E.members 70 = some pinAndFamA)
    (h71 : E.members 71 = some pinAndMkA) :
    HasTyA E I n Γ (.const 71 []) pinAndMkTyA :=
  .const Γ 71 [] pinAndMkA pinAndMkSortA h71 rfl rfl (pinAndMkTyTy h70)

end AndTy

/-- `And`'s parameters `(a b : Prop)`. -/
abbrev pinAndParamsA : List (ExprA × Level) := [(pinAndPropA, .succ .zero), (pinAndPropA, .succ .zero)]

def pinAndFamViewA : FamViewA pinAndFamA where
  params := pinAndParamsA
  indices := []
  sort := .zero
  stored := rfl
  nparams := rfl
  profile := .inl (fun _ => rfl)

/-- `And.intro`'s fields `(left : a) (right : b)`, in the plain context. -/
abbrev pinAndFieldsA : List FieldA := [.plain (.bvar 1) .zero, .plain (.bvar 1) .zero]

def pinAndMkViewA (I : IotaIfaceA) :
    CtorViewA emptyEnvA I 70 pinAndFamA pinAndFamViewA pinAndMkA where
  mirrors := pinAndParamsA
  fields := pinAndFieldsA
  res := []
  stored := rfl
  mirrorsConv := .cons [] _ _ _ _ _ _ (.refl [] _) (fun _ => rfl)
    (.cons _ _ _ _ _ [] [] (.refl _ _) (fun _ => rfl) (.nil _))
  typed := .plain _ 0 (.bvar 1) .zero _ [] (pinAndPropVarTy 1 rfl)
    (.plain _ 1 (.bvar 1) .zero [] [] (pinAndPropVarTy 1 rfl) (.nil _ 2 [] (.nil .zero)))
  univI := fun _ _ _ _ h => by
    simp only [pinAndFieldsA, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> cases h
  drecD_typed := drecDTypedA_of_noDelta (fun _ h => by
    simp only [pinAndFieldsA, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> trivial)
  normConv := ⟨.refl [] _⟩
  normTyped := ⟨_, ⟨pinAndMkTyTy (E := extendEnvA emptyEnvA 70 pinAndFamA) rfl⟩⟩
  univ := fun _ _ _ => Or.inl (fun _ => rfl)

def pinAndFamEnvA : ResolvedEnvA := extendEnvA emptyEnvA 70 pinAndFamA

def pinAndMkGroupA (I : IotaIfaceA) :
    GroupCtorA I emptyEnvA 70 pinAndFamA pinAndFamViewA where
  ref := 71
  member := pinAndMkA
  hcls := rfl
  hnobody := rfl
  harity := rfl
  hnp := rfl
  hclT := fun _ => rfl
  u := pinAndMkSortA
  hT := pinAndMkTyTy (E := pinAndFamEnvA) rfl
  hlvl := rfl
  view := pinAndMkViewA I
  hnorm := rfl
  hclN := fun _ => rfl
  hlvlN := rfl

def pinAndCs (I : IotaIfaceA) : List (GroupCtorA I emptyEnvA 70 pinAndFamA pinAndFamViewA) :=
  [pinAndMkGroupA I]

/-- the motive's type over the parameters: `Π (_ : And a b), Sort u`. -/
abbrev pinAndMotTyAt (u : Level) : ExprA := .pi (pinAndAppA (.bvar 1) (.bvar 0)) .zero (.sort u) (.succ u)
abbrev pinAndMotSortAt (u : Level) : Level := .imax .zero (.succ u)
/-- the minor's type under the motive: `Π (left : a) (right : b), motive (And.intro a b left right)`. -/
abbrev pinAndMinorDomAt (u : Level) : ExprA :=
  .pi (.bvar 2) .zero
    (.pi (.bvar 2) .zero (.app (.bvar 2) (pinAndMkAppA (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0))) u)
    (.imax .zero u)
abbrev pinAndMinorDomSortAt (u : Level) : Level := .imax .zero (.imax .zero u)
/-- the major and the body under the minor: `Π (t : And a b), motive t`. -/
abbrev pinAndMajorTyAt (u : Level) : ExprA :=
  .pi (pinAndAppA (.bvar 3) (.bvar 2)) .zero (.app (.bvar 2) (.bvar 0)) u
abbrev pinAndMajorSortAt (u : Level) : Level := .imax .zero u
abbrev pinAndMinorPiAt (u : Level) : ExprA :=
  .pi (pinAndMinorDomAt u) (pinAndMinorDomSortAt u) (pinAndMajorTyAt u) (pinAndMajorSortAt u)
abbrev pinAndMinorPiSortAt (u : Level) : Level := .imax (pinAndMinorDomSortAt u) (pinAndMajorSortAt u)
abbrev pinAndMotPiAt (u : Level) : ExprA :=
  .pi (pinAndMotTyAt u) (pinAndMotSortAt u) (pinAndMinorPiAt u) (pinAndMinorPiSortAt u)
abbrev pinAndMotPiSortAt (u : Level) : Level := .imax (pinAndMotSortAt u) (pinAndMinorPiSortAt u)
/-- `And.rec.{u} : Π (a b : Prop) (motive : And a b → Sort u)
      (intro : Π (left : a) (right : b), motive (And.intro a b left right)) (t : And a b), motive t`. -/
def pinAndRecTyAt (u : Level) : ExprA :=
  .pi pinAndPropA (.succ .zero) (.pi pinAndPropA (.succ .zero) (pinAndMotPiAt u) (pinAndMotPiSortAt u))
    (.imax (.succ .zero) (pinAndMotPiSortAt u))
abbrev pinAndRecSortAt (u : Level) : Level := .imax (.succ .zero) (.imax (.succ .zero) (pinAndMotPiSortAt u))

def pinAndRecMemberA : CheckedMemberA := ⟨.recursorM, 1, pinAndRecTyAt (.param 0), none, 0, none⟩

theorem pinAndGroupRec_stored (I : IotaIfaceA) :
    pinAndRecMemberA.mtypeA = groupRecTypeA pinAndFamViewA (pinAndCs I) .anySort := rfl

/-- the contexts under the recursor's binders: the parameters, then the motive, then the minor's
    fields. -/
abbrev pinAndCtxP : LCtxA := [.assumption pinAndPropA, .assumption pinAndPropA]
abbrev pinAndCtxM (u : Level) : LCtxA := .assumption (pinAndMotTyAt u) :: pinAndCtxP
abbrev pinAndCtxF (u : Level) : LCtxA := .assumption (.bvar 2) :: .assumption (.bvar 2) :: pinAndCtxM u

section AndRecTy
variable {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}

/-- `motive x : Sort u`, the motive the variable `i`, `x : And x₁ x₂`. -/
def pinAndMotAppTy {Γ : LCtxA} (u : Level) (h70 : E.members 70 = some pinAndFamA) (i : Nat)
    (x₁ x₂ x : ExprA) (hm : lookupTypeA Γ i = some (.pi (pinAndAppA x₁ x₂) .zero (.sort u) (.succ u)))
    (h₁ : HasTyA E I n Γ x₁ pinAndPropA) (h₂ : HasTyA E I n Γ x₂ pinAndPropA)
    (hx : HasTyA E I n Γ x (pinAndAppA x₁ x₂)) :
    HasTyA E I n Γ (.app (.bvar i) x) (.sort u) :=
  .app Γ (.bvar i) x (pinAndAppA x₁ x₂) (.sort u) .zero (.succ u) (.succ u) (.sort _ u) (.sort Γ u)
    (.bvar Γ i _ (pinAndMotSortAt u) hm
      (.pi Γ _ .zero (.sort u) (.succ u) (pinAndAppTy h70 x₁ x₂ h₁ h₂) (.sort _ u)))
    hx

/-- `Π (left : a) (right : b'), And a b'` under a fresh `b' : Prop`, in the minor's context. -/
def pinAndMkTel2Ty (u : Level) (h70 : E.members 70 = some pinAndFamA) :
    HasTyA E I n (.assumption pinAndPropA :: pinAndCtxF u)
      (.pi (.bvar 5) .zero (.pi (.bvar 1) .zero (pinAndAppA (.bvar 7) (.bvar 2)) .zero) (.imax .zero .zero))
      (.sort (.imax .zero (.imax .zero .zero))) :=
  .pi _ (.bvar 5) .zero _ _ (pinAndPropVarTy 5 rfl)
    (.pi _ (.bvar 1) .zero _ _ (pinAndPropVarTy 1 rfl)
      (pinAndAppTy h70 (.bvar 7) (.bvar 2) (pinAndPropVarTy 7 rfl) (pinAndPropVarTy 2 rfl)))

/-- `And.intro a b left right : And a b` in the minor's context: `a b` the variables `4 3`, `left right`
    the variables `1 0`. -/
def pinAndMkVarsTy (u : Level) (h70 : E.members 70 = some pinAndFamA)
    (h71 : E.members 71 = some pinAndMkA) :
    HasTyA E I n (pinAndCtxF u) (pinAndMkAppA (.bvar 4) (.bvar 3) (.bvar 1) (.bvar 0))
      (pinAndAppA (.bvar 4) (.bvar 3)) :=
  .app _ _ (.bvar 0) (.bvar 3) (pinAndAppA (.bvar 5) (.bvar 4)) .zero .zero .zero
    (pinAndAppTy h70 (.bvar 5) (.bvar 4) (pinAndPropVarTy 5 rfl) (pinAndPropVarTy 4 rfl))
    (pinAndAppTy h70 (.bvar 4) (.bvar 3) (pinAndPropVarTy 4 rfl) (pinAndPropVarTy 3 rfl))
    (.app _ _ (.bvar 1) (.bvar 4) (.pi (.bvar 4) .zero (pinAndAppA (.bvar 6) (.bvar 5)) .zero) .zero
        (.imax .zero .zero) (.imax .zero .zero)
      (.pi _ (.bvar 4) .zero _ _ (pinAndPropVarTy 4 rfl)
        (pinAndAppTy h70 (.bvar 6) (.bvar 5) (pinAndPropVarTy 6 rfl) (pinAndPropVarTy 5 rfl)))
      (.pi _ (.bvar 3) .zero _ _ (pinAndPropVarTy 3 rfl)
        (pinAndAppTy h70 (.bvar 5) (.bvar 4) (pinAndPropVarTy 5 rfl) (pinAndPropVarTy 4 rfl)))
      (.app _ _ (.bvar 3) pinAndPropA
          (.pi (.bvar 5) .zero (.pi (.bvar 1) .zero (pinAndAppA (.bvar 7) (.bvar 2)) .zero) (.imax .zero .zero))
          (.succ .zero) (.imax .zero (.imax .zero .zero)) (.imax .zero (.imax .zero .zero))
        (pinAndMkTel2Ty u h70)
        (.pi _ (.bvar 4) .zero _ _ (pinAndPropVarTy 4 rfl)
          (.pi _ (.bvar 4) .zero _ _ (pinAndPropVarTy 4 rfl)
            (pinAndAppTy h70 (.bvar 6) (.bvar 5) (pinAndPropVarTy 6 rfl) (pinAndPropVarTy 5 rfl))))
        (.app _ (.const 71 []) (.bvar 4) pinAndPropA pinAndMkTel1A (.succ .zero) pinAndMkTel1SortA
            pinAndMkTel1SortA
          (pinAndMkTel1Ty h70)
          (.pi _ pinAndPropA (.succ .zero) _ _ (.sort _ .zero) (pinAndMkTel2Ty u h70))
          (pinAndMkConstTy h70 h71) (pinAndPropVarTy 4 rfl))
        (pinAndPropVarTy 3 rfl))
      (.bvar _ 1 (.bvar 4) .zero rfl (pinAndPropVarTy 4 rfl)))
    (.bvar _ 0 (.bvar 3) .zero rfl (pinAndPropVarTy 3 rfl))

/-- the minor's type, under the parameters and the motive. -/
def pinAndMinorDomTy (u : Level) (h70 : E.members 70 = some pinAndFamA)
    (h71 : E.members 71 = some pinAndMkA) :
    HasTyA E I n (pinAndCtxM u) (pinAndMinorDomAt u) (.sort (pinAndMinorDomSortAt u)) :=
  .pi _ (.bvar 2) .zero _ _ (pinAndPropVarTy 2 rfl)
    (.pi _ (.bvar 2) .zero _ _ (pinAndPropVarTy 2 rfl)
      (pinAndMotAppTy u h70 2 (.bvar 4) (.bvar 3) _ rfl (pinAndPropVarTy 4 rfl) (pinAndPropVarTy 3 rfl)
        (pinAndMkVarsTy u h70 h71)))

/-- `And`'s recursor type, typed. -/
def pinAndRecTyTy (u : Level) (h70 : E.members 70 = some pinAndFamA)
    (h71 : E.members 71 = some pinAndMkA) :
    HasTyA E I n [] (pinAndRecTyAt u) (.sort (pinAndRecSortAt u)) :=
  .pi [] pinAndPropA (.succ .zero) _ _ (.sort [] .zero)
    (.pi _ pinAndPropA (.succ .zero) _ _ (.sort _ .zero)
      (.pi _ (pinAndMotTyAt u) (pinAndMotSortAt u) _ _
        (.pi _ _ .zero (.sort u) (.succ u)
          (pinAndAppTy h70 (.bvar 1) (.bvar 0) (pinAndPropVarTy 1 rfl) (pinAndPropVarTy 0 rfl)) (.sort _ u))
        (.pi _ (pinAndMinorDomAt u) (pinAndMinorDomSortAt u) _ _ (pinAndMinorDomTy u h70 h71)
          (.pi _ (pinAndAppA (.bvar 3) (.bvar 2)) .zero _ _
            (pinAndAppTy h70 (.bvar 3) (.bvar 2) (pinAndPropVarTy 3 rfl) (pinAndPropVarTy 2 rfl))
            (pinAndMotAppTy u h70 2 (.bvar 4) (.bvar 3) (.bvar 0) rfl (pinAndPropVarTy 4 rfl)
              (pinAndPropVarTy 3 rfl)
              (.bvar _ 0 _ .zero rfl
                (pinAndAppTy h70 (.bvar 4) (.bvar 3) (pinAndPropVarTy 4 rfl) (pinAndPropVarTy 3 rfl))))))))

end AndRecTy

theorem boundOkB_pinAndRecTyA : boundOkB 0 (pinAndRecTyAt (.param 0)) = true := rfl

theorem liftA_pinAndRecTyA (k : Nat) :
    liftA k 1 (pinAndRecTyAt (.param 0)) = pinAndRecTyAt (.param 0) :=
  liftA_of_boundOkB 1 k _ (boundOkB_add k 0 _ boundOkB_pinAndRecTyA)

def pinAndGroupRecA (I : IotaIfaceA) :
    GroupRecA I emptyEnvA 70 pinAndFamA pinAndFamViewA (pinAndCs I) where
  member := pinAndRecMemberA
  hcls := rfl
  hnobody := rfl
  hnp := rfl
  elim := .anySort
  harity := rfl
  stored := pinAndGroupRec_stored I
  hclT := liftA_pinAndRecTyA
  u := pinAndRecSortAt (.param 0)
  hT := pinAndRecTyTy (.param 0) rfl rfl
  hlvl := rfl

def pinAndRecEnvA (I : IotaIfaceA) : ResolvedEnvA :=
  groupRecEnvA (pinAndCs I) (pinAndGroupRecA I)

/-- `And`, `And.intro` and the derived AnySort recursor, by `EnvWfA.groupRec`. -/
def pinAndGroupRecWfA (I : IotaIfaceA) : EnvWfA I (pinAndRecEnvA I) :=
  .groupRec emptyEnvA 70 pinAndFamA pinAndFamSortA
    .empty rfl rfl (fun _ => rfl) pinAndFamTyTy rfl
    pinAndFamViewA (pinAndCs I) ⟨rfl, rfl⟩ rfl (pinAndGroupRecA I) rfl

def pinAndEnvA : ResolvedEnvA :=
  extendEnvA (extendEnvA pinAndFamEnvA 71 pinAndMkA) 72 pinAndRecMemberA

theorem pinAndRecEnvA_eq (I : IotaIfaceA) : pinAndRecEnvA I = pinAndEnvA := rfl

def pinAnd_wf : EnvWfA (iotaIfaceA pinAndEnvA) pinAndEnvA :=
  pinAndRecEnvA_eq (iotaIfaceA pinAndEnvA) ▸ pinAndGroupRecWfA (iotaIfaceA pinAndEnvA)

theorem pinAnd_mem {r : Nat} {m : CheckedMemberA} (hm : pinAndEnvA.members r = some m) :
    (r = 70 ∧ m = pinAndFamA) ∨ (r = 71 ∧ m = pinAndMkA) ∨ (r = 72 ∧ m = pinAndRecMemberA) := by
  revert hm
  unfold pinAndEnvA pinAndFamEnvA
  simp only [extendEnvA, emptyEnvA]
  intro hm
  by_cases h72 : r = 72
  · subst h72
    simp only [if_pos rfl] at hm
    cases hm
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · simp only [if_neg h72] at hm
    by_cases h71 : r = 71
    · subst h71
      simp only [if_pos rfl] at hm
      cases hm
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · simp only [if_neg h71] at hm
      by_cases h70 : r = 70
      · subst h70
        simp only [if_pos rfl] at hm
        cases hm
        exact Or.inl ⟨rfl, rfl⟩
      · simp only [if_neg h70] at hm
        cases hm

/-- `And` has two parameters and no index binder, so the small-index profile holds vacuously. -/
theorem pinAnd_small : SmallIndexProfileA pinAndEnvA := by
  intro r m u₀ hm hc _ v hv _ _ _ _ _ _
  rcases pinAnd_mem hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact absurd hv (List.not_mem_nil v)
  · exact MemberClass.noConfusion hc
  · exact MemberClass.noConfusion hc

/-- the struct test holds at `And`'s recursor. -/
theorem pinAnd_struct : structGroupA 72 pinAndRecMemberA = true := by decide

/-- `And`'s recursor is no unit group's: its minor has fields. -/
theorem pinAnd_notUnit : unitGroupA 72 pinAndRecMemberA = false := by decide

/-- TOOTH: `And` is outside `PropElimOnlyA`: its recursor eliminates into every sort, and is neither
    its family's next member nor a unit group's. -/
theorem pinAnd_not_propElim : ¬ PropElimOnlyA pinAndEnvA := by
  intro h
  have := h 72 pinAndRecMemberA (pinAndAppA (.bvar 3) (.bvar 2)) 70 [] pinAndFamA .zero rfl rfl rfl rfl
    rfl rfl rfl (fun _ => rfl) (by decide) pinAnd_notUnit _ rfl
  cases this

/-- W-1 (d): `PropElimStructA` holds at `And` by the struct exemption alone. -/
theorem pinAnd_propElimStruct : PropElimStructA pinAndEnvA := by
  intro r rm _ _ _ _ _ hrm hcl _ _ _ _ _ _ _ _ hns _ _
  rcases pinAnd_mem hrm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨rfl, rfl⟩
  · exact MemberClass.noConfusion hcl
  · exact MemberClass.noConfusion hcl
  · rw [pinAnd_struct] at hns
    exact Bool.noConfusion hns

/-- the constructor of `And` has no function-recursive field. -/
theorem pinAnd_noFun : EnvNoFunA pinAndEnvA := by
  intro c cm f fm shapes hc hcl hfam hf hsh s hs j
  rcases pinAnd_mem hc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · simp [pinAndFamA] at hcl
  · have h : memberFamRefA pinAndMkA = some 70 := rfl
    rw [h] at hfam
    cases hfam
    have h10 : pinAndEnvA.members 70 = some pinAndFamA := rfl
    rw [h10] at hf
    cases hf
    have hs0 : ctorShapesA 70 pinAndFamA.nparamsA (pinAndMkA.normA.getD pinAndMkA.mtypeA) =
      some [.nonrecursive, .nonrecursive] := rfl
    rw [hs0] at hsh
    cases hsh
    simp only [List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> intro h <;> cases h
  · simp [pinAndRecMemberA] at hcl

/-- W-1 (d), THE PREDICTION: `And`, a struct with two parameters and its AnySort recursor, satisfies
    `EnvSemA` at the concrete ι. -/
theorem envSemA_pinAnd (n : Nat) :
    EnvSemA pinAndEnvA (iotaIfaceA pinAndEnvA) n (fun _ => 1) :=
  envSemA_of_envWfA_recStruct (E := pinAndEnvA) (n := n) (ρ₀ := fun _ => 1)
    pinAnd_wf posValA_one pinAnd_small pinAnd_propElimStruct

#print axioms liftA_app
#print axioms liftA_lam
#print axioms liftA_pi
#print axioms liftA_letE
#print axioms liftA_of_boundOkB
#print axioms boundOkB_add
#print axioms pinNatRecBuiltA_shape
#print axioms boundOkB_pinNatRecBuiltA
#print axioms liftA_pinNatRecBuiltA
#print axioms pinNatFamEnv_fam
#print axioms pinNatGroupEnv_fam
#print axioms pinNatGroupEnv_zero
#print axioms pinNatGroupEnv_succ
#print axioms pinNatGroup_layout
#print axioms pinNatGroup_fresh
#print axioms pinNatGroupEnv_eq
#print axioms pinNatGroupRec_stored
#print axioms pinNatRec_fresh
#print axioms pinNatRecEnvA_eq
#print axioms pinNatGroupRec_iota
#print axioms pinNatGroupRec_iotaZero
#print axioms pinNatGroupRec_derivedIota
#print axioms pinNatGroupRecWfA
#print axioms pinNatBuilt_recMember
#print axioms pinNatBuilt_recClass
#print axioms pinNatBuilt_mem
#print axioms pinNatBuilt_inductive
#print axioms pinNatBuilt_noParams
#print axioms pinNatBuilt_small
#print axioms pinNatBuilt_propElim
#print axioms pinNatBuilt_wf
#print axioms envSemA_pinNat
#print axioms sortConvCharA_pinNat
#print axioms piConvInjA_pinNat
#print axioms pinFalseGroupRecWfA
#print axioms pinFalse_noCtor
#print axioms pinFalse_small
#print axioms pinFalse_propElim
#print axioms pinFalse_motive_not_prop
#print axioms envSemA_pinFalse
#print axioms pinFalse_noMajorStep
#print axioms pinNat_majorStep
#print axioms sortConvCharA_pinFalse
#print axioms pinTrueGroupRec_stored
#print axioms pinTrueGroupRecWfA
#print axioms pinTrue_wf
#print axioms pinTrueAx_wf
#print axioms pinTrue_small
#print axioms pinTrue_propElim
#print axioms pinTrueConv
#print axioms pinTrue_unit
#print axioms pinNat_notUnit
#print axioms pinFalse_notUnit
#print axioms pinIdx_notUnit
#print axioms pinTrue_var_kunit
#print axioms pinTrueAx_kunit
#print axioms pinTrueAx_mem
#print axioms pinTrueAx_small
#print axioms pinTrueAx_propElim
#print axioms envSemA_pinTrue
#print axioms envSemA_pinTrueAx
#print axioms piDepthA_det
#print axioms asmEqA_lookupValue
#print axioms hStepFnA_valEq
#print axioms whnfA_valEq
#print axioms redTo_asmEq
#print axioms piDepthA_asmEq
#print axioms piDepthA_liftA
#print axioms propEqA_piDepth
#print axioms propEqA_not_selfArrow
#print axioms pinStructGroupRec_stored
#print axioms pinStructGroupRecWfA
#print axioms pinStruct_wf
#print axioms pinStruct_small
#print axioms pinStruct_notUnit
#print axioms pinStruct_not_propElim
#print axioms pinStructConv
#print axioms pinLoopGroupRec_stored
#print axioms pinLoopGroupRecWfA
#print axioms pinLoop_wf
#print axioms pinLoop_small
#print axioms pinLoop_notUnit
#print axioms pinLoop_not_propElim
#print axioms pinLoopConv
#print axioms pinLoop_envSem_false_at
#print axioms pinLoop_envSem_false
#print axioms pinLoop_O1_exact
#print axioms pinStruct_struct
#print axioms pinNat_notStruct
#print axioms pinFalse_notStruct
#print axioms pinTrue_notStruct
#print axioms pinLoop_notStruct
#print axioms pinIdx_notStruct
#print axioms pinStructArm_var
#print axioms pinStructProj_var_step
#print axioms pinStructArm_var_beta
#print axioms pinStructArm_proj_loop
#print axioms pinStruct_ctor_arm
#print axioms pinStruct_ctor_iotaFn
#print axioms pinStruct_ctor_notIotaRel
#print axioms pinStruct_ctor_atStruct
#print axioms pinStruct_propElimStruct
#print axioms envSemA_pinStruct
#print axioms pinLoop_not_propElimStruct
#print axioms pinAndFamViewA
#print axioms pinAndMkViewA
#print axioms pinAndRecTyTy
#print axioms pinAndGroupRec_stored
#print axioms pinAndGroupRecWfA
#print axioms pinAnd_wf
#print axioms pinAnd_small
#print axioms pinAnd_struct
#print axioms pinAnd_notUnit
#print axioms pinAnd_not_propElim
#print axioms pinAnd_propElimStruct
#print axioms envSemA_pinAnd

end Rcic.Declarative.Ann
