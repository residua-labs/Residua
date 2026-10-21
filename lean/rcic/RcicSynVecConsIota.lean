import rcic.RcicSynNatSuccIota
import rcic.RcicTypedGroupPinsVec

/-!
# S19 — the indexed Vec-cons retained-result ι instance (`wVecCons0`)

`research/rcic/sortrow/S19_VEC_INDEXED_ES.md` (PR #7412). The fixture is
`vecEnvUT` (the Nat group extended by `Vec : Sort 1 → N → Sort 1` at `4`,
`vnil 5`, `vcons 6`, `Vec.rec 7`, arity 1) with the fresh witness
`wVecCons0` at `ls = [.succ .zero]`, `lsC = []`:

`N.rec`'s Vec sibling — `Vec.rec.{1} A M mn mc k₀ (vcons A n₀ h₀ t₀)` —
reduces to `mc n₀ h₀ t₀ (Vec.rec.{1} A M mn mc n₀ t₀)`: the recursive call
takes the FIELD's own index `n₀`, never the major's result index `k₀`.
That separation is the indexed contribution of this slice.

* `wVecCons0` (§3): `preMajor = [A, M, mn, mc, k₀]`, `ctorParams = [A]`,
  `fields = [n₀, h₀, t₀]`, `kinds = [plain, plain, directRec]`,
  `minor = mc`, `nparams = 1`, `nindices = 1`, `nMinors = 2`, `ctorIdx = 1`;
  the lhs/rhs equations are sealed first (`wVecCons0_lhs`/`wVecCons0_rhs`).
* `hLᵀ`/`hRᵀ` (§4) are built independently from the real const/app
  producers — `s19MotiveBeta` is the finite two-β `M k xs ≡ N` chain, never
  `iotaPreserveT`/`spineInvAux`/`TypedRowsWf`/family injectivity.
* `hL`/`hR`/`H`/`Nι` (§5) mirror S17 at `vecEnvUWfT`/`AwVec`.
* §6: the 11-occurrence slot plan — the index slot `k₀`, the ctor-param
  copy `A`, the field index `n₀` and the RHS recursive result are distinct
  occurrences; every stored derivation's weight is `< Nι`.
* §7: the two index equations separately — `familyIdx` of the
  constructor's result is `[succ n₀] = [k₀]`; `familyIdx` of the
  directRec field's own type `Vec A n₀` is `[n₀]`; they differ.
* §8: `vecConsRule` (nine-λ template), `TableWF`, `CRoot.ctor`, exactly
  nine β steps to `ER = mcε n₀ε h₀ε t₀ε (recε Aε Mε mnε mcε n₀ε t₀ε)`;
  `vecCons_iota_erasure : ES vecConsTable id [] H`.
* §9: the five exactness mutants.
* the declaration-domain views are lazy instantiations of `vecRecTypeU`'s
  own telescope fields (and `vecConsType`'s), each atom `< Nι` — no
  canonical full-application chain.

`closure_claim = 0`; general indexed-family alignment (T7) stays the open
wall.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §2 the fixture terms (spec §2)

`n₀ = 0`, `k₀ = 1`, `h₀ = 2` — three deliberately distinct N values; `A`
is the Nat family `const 0`; `t₀ = vnil A`; the major is
`vcons A n₀ h₀ t₀`. -/

/-- `A = N`. -/
abbrev s19A : Expr Nat := .const 0 []
/-- `n₀ = zero`. -/
abbrev s19N0 : Expr Nat := .const 1 []
/-- `k₀ = succ zero` — the major's result index. -/
abbrev s19K0 : Expr Nat := .app (.const 2 []) (.const 1 [])
/-- `h₀ = succ (succ zero)` — the head value. -/
abbrev s19H0 : Expr Nat := .app (.const 2 []) s19K0
/-- `t₀ = vnil A`. -/
abbrev s19T0 : Expr Nat := .app (.const 5 []) (.const 0 [])
/-- `M = λ k:N. λ xs:Vec A k. N` — the constant motive. -/
abbrev vecMotiveS19 : Expr Nat :=
  .lam (.const 0 [])
    (.lam (.app (.app (.const 4 []) (.const 0 [])) (.bvar 0)) (.const 0 []))
/-- `mn = zero`. -/
abbrev s19Mn : Expr Nat := .const 1 []
/-- `mc = λ k:N. λ x:A. λ xs:Vec A k. λ ih:M k xs. x` — the cons minor. -/
abbrev vecMinorConsS19 : Expr Nat :=
  .lam (.const 0 [])
    (.lam (.const 0 [])
      (.lam (.app (.app (.const 4 []) (.const 0 [])) (.bvar 1))
        (.lam (.app (.app vecMotiveS19 (.bvar 2)) (.bvar 0)) (.bvar 2))))
/-- the major `vcons A n₀ h₀ t₀`. -/
abbrev s19Major : Expr Nat :=
  foldApps (.const 6 []) [s19A, s19N0, s19H0, s19T0]
/-- `Vec A i` as a raw type expression. -/
abbrev s19VecAt (i : Expr Nat) : Expr Nat :=
  .app (.app (.const 4 []) (.const 0 [])) i

/-- PIN: the three index/value literals are distinct — `n₀ ≠ k₀ ≠ h₀`. -/
theorem s19_idx_distinct : s19N0 ≠ s19K0 ∧ s19K0 ≠ s19H0 ∧ s19N0 ≠ s19H0 :=
  ⟨by decide, by decide, by decide⟩

/-! ## §3 the witness `wVecCons0` and the lhs/rhs equations -/

/-- the fresh Vec-cons ι witness (spec §3). -/
def wVecCons0 : IotaWitness vecEnvUT where
  recRef := 7
  ctorRef := 6
  ls := [.succ .zero]
  lsC := []
  recMember := vecRecMemberU
  ctorMember := vecConsMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [s19A, vecMotiveS19, s19Mn, vecMinorConsS19, s19K0]
  fields := [s19N0, s19H0, s19T0]
  ctorParams := [s19A]
  kinds := [.plain, .plain, .directRec]
  minor := vecMinorConsS19
  hlen := rfl
  familyRef := 4
  famMember := vecFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 1
  nindices := 1
  nMinors := 2
  ctorIdx := 1
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  hminor := rfl
  ctorDoms := [.sort (.succ .zero), .const 0 [], .bvar 1,
    .app (.app (.const 4 []) (.bvar 2)) (.bvar 1)]
  ctorResult := .app (.app (.const 4 []) (.bvar 3)) (.app (.const 2 []) (.bvar 2))
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := [.sort (.succ .zero), vecMotTy 1,
    .app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1)),
    vecMinorCons, .const 0 [],
    .app (.app (.const 4 []) (.bvar 4)) (.bvar 0)]
  recBody := .app (.app (.bvar 4) (.bvar 1)) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams :=
    .pi (.const 0 [])
      (.pi (.const 0 [])
        (.pi (.app (.app (.const 4 []) (.const 0 [])) (.bvar 1))
          (.app (.app (.const 4 []) (.const 0 []))
            (.app (.const 2 []) (.bvar 2)))))
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- `rec A M mn mc a` as a raw `Expr Nat`, at `ls = [.succ .zero]`. -/
def recAppS19 (a b : Expr Nat) : Expr Nat :=
  .app (.app (.app (.app (.app (.app (.const 7 [.succ .zero])
    s19A) vecMotiveS19) s19Mn) vecMinorConsS19) a) b

/-- §3's lhs equation: `iotaLhsOf` is exactly `rec A M mn mc k₀ major`. -/
theorem wVecCons0_lhs : iotaLhsOf wVecCons0 = recAppS19 s19K0 s19Major := rfl

/-- §3's rhs equation: `iotaRhsOf` is exactly
    `mc n₀ h₀ t₀ (rec A M mn mc n₀ t₀)` — the recursive call reads the
    directRec field's OWN index `n₀` (`rhsArgs`/`recCallField` at the
    field's type `Vec A n₀`), never the major index `k₀`. -/
theorem wVecCons0_rhs : iotaRhsOf wVecCons0 =
    foldApps vecMinorConsS19
      [s19N0, s19H0, s19T0, recAppS19 s19N0 s19T0] := rfl

/-- PIN: `rhsArgs` itself — the recursive call the witness mechanics
    produces is `rec A M mn mc n₀ t₀` (index `const 1`, not `app (const 2)
    (const 1)`). -/
theorem wVecCons0_rhsArgs :
    rhsArgs (.const 7 [.succ .zero]) wVecCons0.preMajor 1 2 wVecCons0.fields
      wVecCons0.kinds wVecCons0.ctorAfterParams =
      [s19N0, s19H0, s19T0, recAppS19 s19N0 s19T0] := rfl

/-- PIN: the recursive call's index slot carries `n₀`, not `k₀`. -/
theorem wVecCons0_rhs_index :
    (rhsArgs (.const 7 [.succ .zero]) wVecCons0.preMajor 1 2 wVecCons0.fields
      wVecCons0.kinds wVecCons0.ctorAfterParams)[3]? =
      some (recAppS19 s19N0 s19T0) := rfl

/-! ## §4 independent native typings (no `iotaPreserveT`, no `spineInvAux`,
    no `TypedRowsWf`, no family injectivity) -/

/-- `N : Sort 1` in any context over `vecEnvUT`. -/
noncomputable def s19NTy (Γ : LCtx) :
    HasTyT vecEnvUT 0 Γ (.const 0 []) (.sort (.succ .zero)) :=
  natConstTyT rfl

/-- `zero : N`. -/
noncomputable def s19ZTy (Γ : LCtx) :
    HasTyT vecEnvUT 0 Γ (.const 1 []) (.const 0 []) :=
  HasTyT.const Γ 1 [] natZeroMember rfl rfl rfl

/-- `succ : Π (_ : N), N`. -/
noncomputable def s19STy (Γ : LCtx) :
    HasTyT vecEnvUT 0 Γ (.const 2 []) (.pi (.const 0 []) (.const 0 [])) :=
  HasTyT.const Γ 2 [] natSuccMember rfl rfl rfl

/-- `k₀ : N`. -/
noncomputable def s19K0Ty (Γ : LCtx) :
    HasTyT vecEnvUT 0 Γ s19K0 (.const 0 []) :=
  HasTyT.app Γ _ _ _ _ (s19STy Γ) (s19ZTy Γ)

/-- `h₀ : N`. -/
noncomputable def s19H0Ty (Γ : LCtx) :
    HasTyT vecEnvUT 0 Γ s19H0 (.const 0 []) :=
  HasTyT.app Γ _ _ _ _ (s19STy Γ) (s19K0Ty Γ)

/-- `t₀ : Vec A zero` — `vnil` applied to the family parameter. -/
noncomputable def s19T0Ty (Γ : LCtx) :
    HasTyT vecEnvUT 0 Γ s19T0 (s19VecAt s19N0) :=
  HasTyT.app Γ _ _ _ _
    (HasTyT.const Γ 5 [] vecNilMember rfl rfl rfl) (s19NTy Γ)

/-- `major : Vec A k₀` — `vcons A n₀ h₀ t₀` at `Vec A (succ n₀)`. -/
noncomputable def s19MajorTy :
    HasTyT vecEnvUT 0 [] s19Major (s19VecAt s19K0) :=
  HasTyT.app [] _ _ _ _
    (HasTyT.app [] _ _ _ _
      (HasTyT.app [] _ _ _ _
        (HasTyT.app [] _ _ _ _
          (HasTyT.const [] 6 [] vecConsMember rfl rfl rfl) (s19NTy []))
        (s19ZTy []))
      (s19H0Ty []))
    (s19T0Ty [])

/-- `Vec A k : Sort 1` in any context (the real family application). -/
noncomputable def s19VecTy (Γ : LCtx) {a i : Expr Nat}
    (ha : HasTyT vecEnvUT 0 Γ a (.sort (.succ .zero)))
    (hi : HasTyT vecEnvUT 0 Γ i (.const 0 [])) :
    HasTyT vecEnvUT 0 Γ (.app (.app (.const 4 []) a) i) (.sort (.succ .zero)) :=
  vecOfTyT rfl ha hi

/-- the constant motive `M : Π k:N. Π xs:Vec A k. Sort 1`, in any context. -/
noncomputable def vecMotiveTyS19 (Γ : LCtx) :
    HasTyT vecEnvUT 0 Γ vecMotiveS19
      (.pi (.const 0 [])
        (.pi (s19VecAt (.bvar 0)) (.sort (.succ .zero)))) :=
  HasTyT.lam Γ (.const 0 []) (.succ .zero) _ _ (s19NTy Γ)
    (HasTyT.lam _ (s19VecAt (.bvar 0)) (.succ .zero) (.const 0 [])
      (.sort (.succ .zero))
      (s19VecTy _ (s19NTy _) (HasTyT.bvar _ 0 _ rfl))
      (s19NTy _))

/-- §4's finite helper: `M k xs ≡ N` at `Sort 1` — two original β steps
    (`M k → λxs.N`, `(λxs.N) xs → N`) composed by one application
    congruence and one transitivity. No normalizer, no general subject
    reduction: the typing premises are the real `hk`/`hxs` plus the
    motive's own λ-bodies. -/
noncomputable def s19MotiveBeta (Γ : LCtx) {k xs : Expr Nat}
    (hk : HasTyT vecEnvUT 0 Γ k (.const 0 []))
    (hxs : HasTyT vecEnvUT 0 Γ xs (s19VecAt k)) :
    ConvT vecEnvUT 0 Γ (.app (.app vecMotiveS19 k) xs) (.const 0 [])
      (.sort (.succ .zero)) :=
  have hb1 : ConvT vecEnvUT 0 Γ (.app vecMotiveS19 k)
      (.lam (s19VecAt k) (.const 0 [])) (.pi (s19VecAt k) (.sort (.succ .zero))) :=
    ConvT.beta Γ (.const 0 [])
      (.lam (.app (.app (.const 4 []) (.const 0 [])) (.bvar 0)) (.const 0 [])) k
      (.pi (s19VecAt (.bvar 0)) (.sort (.succ .zero))) (.succ .zero)
      (s19NTy Γ)
      (HasTyT.lam _ (s19VecAt (.bvar 0)) (.succ .zero) (.const 0 [])
        (.sort (.succ .zero))
        (s19VecTy _ (s19NTy _) (HasTyT.bvar _ 0 _ rfl))
        (s19NTy _))
      hk
  have hbapp : ConvT vecEnvUT 0 Γ (.app (.app vecMotiveS19 k) xs)
      (.app (.lam (s19VecAt k) (.const 0 [])) xs) (.sort (.succ .zero)) :=
    ConvT.app Γ _ _ _ _ (s19VecAt k) (.sort (.succ .zero)) hb1
      (ConvT.refl Γ _ _ hxs)
  have hb2 : ConvT vecEnvUT 0 Γ (.app (.lam (s19VecAt k) (.const 0 [])) xs)
      (.const 0 []) (.sort (.succ .zero)) :=
    ConvT.beta Γ (s19VecAt k) (.const 0 []) xs (.sort (.succ .zero)) (.succ .zero)
      (s19VecTy Γ (s19NTy Γ) hk) (s19NTy _) hxs
  ConvT.trans Γ _ _ _ _ hbapp hb2

/-- `mn : M zero (vnil A)` — the original `zero : N` retyped backward
    through `s19MotiveBeta`. -/
noncomputable def s19MnTy : HasTyT vecEnvUT 0 [] s19Mn
    (.app (.app vecMotiveS19 s19N0) s19T0) :=
  HasTyT.conv [] _ _ _ (.succ .zero) (s19ZTy [])
    (ConvT.symm _ _ _ _ (s19MotiveBeta [] (s19ZTy []) (s19T0Ty [])))

/-- the cons minor's full four-layer type (the recursor's own minor
    telescope at `A := N`, `M := vecMotiveS19`). -/
abbrev s19McTy : Expr Nat :=
  .pi (.const 0 [])
    (.pi (.const 0 [])
      (.pi (s19VecAt (.bvar 1))
        (.pi (.app (.app vecMotiveS19 (.bvar 2)) (.bvar 0))
          (.app (.app vecMotiveS19 (.app (.const 2 []) (.bvar 3)))
            (foldApps (.const 6 [])
              [.const 0 [], .bvar 3, .bvar 2, .bvar 1])))))

/-- the cons minor's ih domain `M k xs` in the `xs`-under context. -/
abbrev s19IhDom : Expr Nat := .app (.app vecMotiveS19 (.bvar 2)) (.bvar 0)

/-- the cons minor's result `M (succ k) (vcons A k x xs)`. -/
abbrev s19McRes : Expr Nat :=
  .app (.app vecMotiveS19 (.app (.const 2 []) (.bvar 3)))
    (foldApps (.const 6 []) [.const 0 [], .bvar 3, .bvar 2, .bvar 1])

/-- `mc`'s ih-domain `M k xs : Sort 1` in ctx `[xs, x, k]`. -/
noncomputable def s19IhDomTy :
    HasTyT vecEnvUT 0
      [.assumption (s19VecAt (.bvar 1)), .assumption (.const 0 []),
       .assumption (.const 0 [])]
      s19IhDom (.sort (.succ .zero)) :=
  HasTyT.app _ (.app vecMotiveS19 (.bvar 2)) (.bvar 0)
    (s19VecAt (.bvar 2)) (.sort (.succ .zero))
    (HasTyT.app _ vecMotiveS19 (.bvar 2) (.const 0 [])
      (.pi (s19VecAt (.bvar 0)) (.sort (.succ .zero)))
      (vecMotiveTyS19 _) (HasTyT.bvar _ 2 _ rfl))
    (HasTyT.bvar _ 0 _ rfl)

/-- `vcons A k x xs : Vec A (succ k)` in ctx `[ih, xs, x, k]` — the real
    constructor application for the conv leg. -/
noncomputable def s19VconsBvarTy :
    HasTyT vecEnvUT 0
      [.assumption s19IhDom, .assumption (s19VecAt (.bvar 1)),
       .assumption (.const 0 []), .assumption (.const 0 [])]
      (foldApps (.const 6 [])
        [.const 0 [], .bvar 3, .bvar 2, .bvar 1])
      (s19VecAt (.app (.const 2 []) (.bvar 3))) :=
  HasTyT.app _ _ (.bvar 1) _ _
    (HasTyT.app _ _ (.bvar 2) _ _
      (HasTyT.app _ _ (.bvar 3) _ _
        (HasTyT.app _ _ (.const 0 []) _ _
          (HasTyT.const _ 6 [] vecConsMember rfl rfl rfl) (s19NTy _))
        (HasTyT.bvar [.assumption s19IhDom, .assumption (s19VecAt (.bvar 1)),
          .assumption (.const 0 []), .assumption (.const 0 [])] 3 _ rfl))
      (HasTyT.bvar [.assumption s19IhDom, .assumption (s19VecAt (.bvar 1)),
        .assumption (.const 0 []), .assumption (.const 0 [])] 2 _ rfl))
    (HasTyT.bvar [.assumption s19IhDom, .assumption (s19VecAt (.bvar 1)),
      .assumption (.const 0 []), .assumption (.const 0 [])] 1 _ rfl)

/-- `mc`'s body `x : M (succ k) (vcons A k x xs)` in ctx `[ih, xs, x, k]` —
    the original variable `x : A = N` retyped through `s19MotiveBeta`. -/
noncomputable def s19McBodyTy :
    HasTyT vecEnvUT 0
      [.assumption s19IhDom, .assumption (s19VecAt (.bvar 1)),
       .assumption (.const 0 []), .assumption (.const 0 [])]
      (.bvar 2) s19McRes :=
  HasTyT.conv _ (.bvar 2) (.const 0 []) s19McRes (.succ .zero)
    (HasTyT.bvar _ 2 _ rfl)
    (ConvT.symm _ _ _ _
      (s19MotiveBeta _
        (HasTyT.app _ (.const 2 []) (.bvar 3) (.const 0 []) (.const 0 [])
          (s19STy _) (HasTyT.bvar _ 3 _ rfl))
        s19VconsBvarTy))

/-- `mc : Π k:N. Π x:A. Π xs:Vec A k. Π ih:M k xs. M (succ k) (vcons A k x
    xs)` — each binder's real typing kept. -/
noncomputable def s19McTy' : HasTyT vecEnvUT 0 [] vecMinorConsS19 s19McTy :=
  HasTyT.lam [] (.const 0 []) (.succ .zero) _ _ (s19NTy [])
    (HasTyT.lam _ (.const 0 []) (.succ .zero) _ _ (s19NTy _)
      (HasTyT.lam _ (s19VecAt (.bvar 1)) (.succ .zero) _ _
        (s19VecTy _ (s19NTy _) (HasTyT.bvar _ 1 _ rfl))
        (HasTyT.lam _ s19IhDom (.succ .zero) (.bvar 2) s19McRes
          s19IhDomTy s19McBodyTy)))

/-- `prefixTy`: `Vec.rec A M mn mc : Π k:N. Π xs:Vec A k. M k xs` — the
    first four real recursor applications. -/
noncomputable def vecPrefixTy :
    HasTyT vecEnvUT 0 []
      (foldApps (.const 7 [.succ .zero])
        [s19A, vecMotiveS19, s19Mn, vecMinorConsS19])
      (.pi (.const 0 [])
        (.pi (s19VecAt (.bvar 0))
          (.app (.app vecMotiveS19 (.bvar 1)) (.bvar 0)))) :=
  have h0 : HasTyT vecEnvUT 0 [] (.const 7 [.succ .zero]) _ :=
    HasTyT.const [] 7 [.succ .zero] vecRecMemberU rfl rfl rfl
  have h1 := HasTyT.app [] _ _ _ _ h0 (s19NTy [])
  have h2 := HasTyT.app [] _ _ _ _ h1 (vecMotiveTyS19 [])
  have h3 := HasTyT.app [] _ _ _ _ h2 s19MnTy
  HasTyT.app [] _ _ _ _ h3 s19McTy'

/-- `hL₀`: the lhs at the motive's own application type — `lhs : M k₀
    major`. -/
noncomputable def s19HL0 :
    HasTyT vecEnvUT 0 [] (iotaLhsOf wVecCons0)
      (.app (.app vecMotiveS19 s19K0) s19Major) :=
  HasTyT.app [] _ _ _ _
    (HasTyT.app [] _ _ _ _ vecPrefixTy (s19K0Ty [])) s19MajorTy

/-- `hRec`: the RHS's recursive call `rec A M mn mc n₀ t₀ : M n₀ t₀`. -/
noncomputable def s19HRec :
    HasTyT vecEnvUT 0 [] (recAppS19 s19N0 s19T0)
      (.app (.app vecMotiveS19 s19N0) s19T0) :=
  HasTyT.app [] _ _ _ _
    (HasTyT.app [] _ _ _ _ vecPrefixTy (s19ZTy [])) (s19T0Ty [])

/-- `hR₀`: the rhs `mc n₀ h₀ t₀ (rec …)` at `M (succ n₀) (vcons A n₀ h₀ t₀)
    = M k₀ major` — the literal is defeq to `M k₀ major`. -/
noncomputable def s19HR0 :
    HasTyT vecEnvUT 0 [] (iotaRhsOf wVecCons0)
      (.app (.app vecMotiveS19 s19K0) s19Major) :=
  HasTyT.app [] _ _ _ _
    (HasTyT.app [] _ _ _ _
      (HasTyT.app [] _ _ _ _
        (HasTyT.app [] _ _ _ _ s19McTy' (s19ZTy [])) (s19H0Ty []))
      (s19T0Ty []))
    s19HRec

/-- `hLᵀ`: `lhs : N` — converted by the real `s19MotiveBeta` chain. -/
noncomputable def s19HLT : HasTyT vecEnvUT 0 [] (iotaLhsOf wVecCons0) (.const 0 []) :=
  HasTyT.conv [] _ _ _ (.succ .zero) s19HL0
    (s19MotiveBeta [] (s19K0Ty []) s19MajorTy)

/-- `hRecT`: the recursive call converted to `N`. -/
noncomputable def s19HRecT :
    HasTyT vecEnvUT 0 [] (recAppS19 s19N0 s19T0) (.const 0 []) :=
  HasTyT.conv [] _ _ _ (.succ .zero) s19HRec
    (s19MotiveBeta [] (s19ZTy []) (s19T0Ty []))

/-- `hRᵀ`: `rhs : N`. -/
noncomputable def s19HRT : HasTyT vecEnvUT 0 [] (iotaRhsOf wVecCons0) (.const 0 []) :=
  HasTyT.conv [] _ _ _ (.succ .zero) s19HR0
    (s19MotiveBeta [] (s19K0Ty []) s19MajorTy)

/-! ## §5 the enriched `hL`/`hR`, `H`, `Nι` -/

/-- the enriched lhs typing. -/
noncomputable def s19hL : TyP vecEnvUT 0 [] (iotaLhsOf wVecCons0) (.const 0 []) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil s19HLT

/-- the enriched rhs typing. -/
noncomputable def s19hR : TyP vecEnvUT 0 [] (iotaRhsOf wVecCons0) (.const 0 []) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil s19HRT

/-- `H`: the stored ι node; `hlhs`/`hrhs`/`dl`/`dr` keep the four original
    occurrences. -/
noncomputable def s19H :
    CvP vecEnvUT 0 [] (iotaLhsOf wVecCons0) (iotaRhsOf wVecCons0) (.const 0 []) :=
  CvP.iota vecEnvUT 0 [] _ _ _ (DerivedIota.of wVecCons0) s19hL s19hR s19hL s19hR

/-- the real admission weight of `enrichEnvWfT vecEnvUWfT`. -/
noncomputable def AwVec : Nat → Nat := (enrichEnvWfT vecEnvUWfT).admW

/-- `Nι := H.wt AwVec`. -/
noncomputable def s19Nι : Nat := s19H.wt AwVec

/-- §5's shape: `Nι = 1 + 2 * hL.wt + 2 * hR.wt`. -/
theorem s19Nι_eq : s19Nι = 1 + 2 * s19hL.wt AwVec + 2 * s19hR.wt AwVec := by
  have hw : s19H.wt AwVec =
      1 + s19hL.wt AwVec + s19hR.wt AwVec + s19hL.wt AwVec + s19hR.wt AwVec := rfl
  rw [s19Nι, hw]; omega

/-! ## §4' declaration-domain views — `vecRecTypeU`'s and `vecConsType`'s
    own admission telescope fields, lazily instantiated

Each §6 `pD` is the real domain field of this recursor's/constructor's own
stored telescope — transported `vecPrefixU → vecEnvUT` along the fresh
member's `EnvExt`, enriched under `vecEnvUWfT`/`AwVec`, level-instantiated
at `σ = [.succ .zero]` (`TyP.linst`, no atoms), and lazily substituted at
descending index by the real arguments already used (`TyP.esub`; each
`hv`/`hvT` is the actual argument derivation and its `.reg.2`; the `wk`
lifts add no atoms). -/

/-- `vecPrefixU → vecEnvUT`: the fresh recursor member's forward
    extension. -/
theorem vecPrefToUT : EnvExt vecPrefixU vecEnvUT :=
  envExt_extendEnv vecRecMemberU rfl

/-- the telescope's field decomposition — the domains are literally
    `vecRecTypeU`'s binder fields. -/
theorem vecRecTele_eq : vecRecTypeU =
    .pi (.sort (.succ .zero)) (.pi (vecMotTy 1)
      (.pi (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1)))
        (.pi vecMinorCons (.pi (.const 0 [])
          (.pi (.app (.app (.const 4 []) (.bvar 4)) (.bvar 0))
            (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))))))) := rfl

/-- the constructor telescope's decomposition — `vecConsType` after the
    `A` parameter is `Π n:N. Π hd:A. Π tl:Vec A n. Vec A (succ n)`. -/
theorem vecConsTele_eq : vecConsType =
    .pi (.sort (.succ .zero)) (.pi (.const 0 []) (.pi (.bvar 1)
      (.pi (.app (.app (.const 4 []) (.bvar 2)) (.bvar 1))
        (.app (.app (.const 4 []) (.bvar 3)) (.app (.const 2 []) (.bvar 2)))))) := rfl

/-- d0 — `A`'s domain `Sort 1`, `vecRecTypeTyT`'s first `.pi` leaf. -/
noncomputable def s19Dom0T :
    HasTyT vecPrefixU 1 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sort [] (.succ .zero)

/-- d1 — `M`'s domain `Π k:N. Π xs:Vec A k. Sort u`, `vecRecTypeTyT`'s
    second domain field verbatim. -/
noncomputable def s19Dom1T :
    HasTyT vecPrefixU 1 [.assumption (.sort (.succ .zero))] (vecMotTy 1)
      (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ (.param 0))))) :=
  .pi _ _ _ _ _ (natConstTyT rfl)
    (.pi _ _ _ _ _ (vecOfTyT rfl (.bvar _ 1 _ rfl) (.bvar _ 0 _ rfl))
      (.sort _ (.param 0)))

/-- d2 — `mn`'s domain `M zero (vnil A)`, `vecRecTypeTyT`'s third field
    verbatim. -/
noncomputable def s19Dom2T :
    HasTyT vecPrefixU 1
      [.assumption (vecMotTy 1), .assumption (.sort (.succ .zero))]
      (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1)))
      (.sort (.param 0)) :=
  .app _ (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))
    (.app (.app (.const 4 []) (.bvar 1)) (.const 1 [])) (.sort (.param 0))
    (.app _ (.bvar 0) (.const 1 []) (.const 0 [])
      (.pi (.app (.app (.const 4 []) (.bvar 2)) (.bvar 0)) (.sort (.param 0)))
      (.bvar _ 0 (vecMotTy 2) rfl) (.const _ 1 [] natZeroMember rfl rfl rfl))
    (.app _ (.const 5 []) (.bvar 1) (.sort (.succ .zero))
      (.app (.app (.const 4 []) (.bvar 0)) (.const 1 []))
      (.const _ 5 [] vecNilMember rfl rfl rfl) (.bvar _ 1 _ rfl))

/-- d3 — `mc`'s domain `Π k:N. Π x:A. Π xs:Vec A k. Π ih:M k xs. M (succ
    k) (vcons A k x xs)`, `vecRecTypeTyT`'s fourth field verbatim. -/
noncomputable def s19Dom3T :
    HasTyT vecPrefixU 1
      [.assumption (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))),
       .assumption (vecMotTy 1), .assumption (.sort (.succ .zero))]
      vecMinorCons
      (.sort (.imax (.succ .zero) (.imax (.succ .zero)
        (.imax (.succ .zero) (.imax (.param 0) (.param 0)))))) :=
  .pi _ _ _ _ _ (natConstTyT rfl)
    (.pi _ _ _ _ _ (.bvar _ 3 _ rfl)
      (.pi _ _ _ _ _ (vecOfTyT rfl (.bvar _ 4 _ rfl) (.bvar _ 1 _ rfl))
        (.pi _ _ _ _ _
          (.app _ (.app (.bvar 4) (.bvar 2)) (.bvar 0)
            (.app (.app (.const 4 []) (.bvar 5)) (.bvar 2)) (.sort (.param 0))
            (.app _ (.bvar 4) (.bvar 2) (.const 0 [])
              (.pi (.app (.app (.const 4 []) (.bvar 6)) (.bvar 0)) (.sort (.param 0)))
              (.bvar _ 4 (vecMotTy 6) rfl) (.bvar _ 2 _ rfl))
            (.bvar _ 0 _ rfl))
          (.app _ (.app (.bvar 5) (.app (.const 2 []) (.bvar 3)))
            (.app (.app (.app (.app (.const 6 []) (.bvar 6)) (.bvar 3)) (.bvar 2)) (.bvar 1))
            (.app (.app (.const 4 []) (.bvar 6)) (.app (.const 2 []) (.bvar 3)))
            (.sort (.param 0))
            (.app _ (.bvar 5) (.app (.const 2 []) (.bvar 3)) (.const 0 [])
              (.pi (.app (.app (.const 4 []) (.bvar 7)) (.bvar 0)) (.sort (.param 0)))
              (.bvar _ 5 (vecMotTy 7) rfl)
              (.app _ (.const 2 []) (.bvar 3) (.const 0 []) (.const 0 [])
                (.const _ 2 [] natSuccMember rfl rfl rfl) (.bvar _ 3 _ rfl)))
            (.app _ (.app (.app (.app (.const 6 []) (.bvar 6)) (.bvar 3)) (.bvar 2)) (.bvar 1)
              (.app (.app (.const 4 []) (.bvar 6)) (.bvar 3))
              (.app (.app (.const 4 []) (.bvar 7)) (.app (.const 2 []) (.bvar 4)))
              (.app _ (.app (.app (.const 6 []) (.bvar 6)) (.bvar 3)) (.bvar 2) (.bvar 6)
                (.pi (.app (.app (.const 4 []) (.bvar 7)) (.bvar 4))
                  (.app (.app (.const 4 []) (.bvar 8)) (.app (.const 2 []) (.bvar 5))))
                (.app _ (.app (.const 6 []) (.bvar 6)) (.bvar 3) (.const 0 [])
                  (.pi (.bvar 7) (.pi (.app (.app (.const 4 []) (.bvar 8)) (.bvar 1))
                    (.app (.app (.const 4 []) (.bvar 9)) (.app (.const 2 []) (.bvar 2)))))
                  (.app _ (.const 6 []) (.bvar 6) (.sort (.succ .zero))
                    (.pi (.const 0 []) (.pi (.bvar 1) (.pi (.app (.app (.const 4 []) (.bvar 2)) (.bvar 1))
                      (.app (.app (.const 4 []) (.bvar 3)) (.app (.const 2 []) (.bvar 2))))))
                    (.const _ 6 [] vecConsMember rfl rfl rfl) (.bvar _ 6 _ rfl))
                  (.bvar _ 3 _ rfl))
                (.bvar _ 2 _ rfl))
              (.bvar _ 1 _ rfl))))))

/-- d4 — the index `k`'s domain `N`, the `natConstTyT` leaf
    `vecRecTypeTyT` uses for its fifth domain field. -/
noncomputable def s19Dom4T :
    HasTyT vecPrefixU 1
      [.assumption vecMinorCons,
       .assumption (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))),
       .assumption (vecMotTy 1), .assumption (.sort (.succ .zero))]
      (.const 0 []) (.sort (.succ .zero)) :=
  natConstTyT rfl

/-- d5 — the major's domain `Vec A k`, `vecRecTypeTyT`'s `vecOfTyT` leaf
    at the sixth domain field. -/
noncomputable def s19Dom5T :
    HasTyT vecPrefixU 1
      [.assumption (.const 0 []), .assumption vecMinorCons,
       .assumption (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))),
       .assumption (vecMotTy 1), .assumption (.sort (.succ .zero))]
      (.app (.app (.const 4 []) (.bvar 4)) (.bvar 0)) (.sort (.succ .zero)) :=
  vecOfTyT rfl (.bvar _ 4 _ rfl) (.bvar _ 0 _ rfl)

/-- the result field — `M k xs : Sort u` under the whole telescope,
    `vecRecTypeTyT`'s innermost `.app` verbatim. -/
noncomputable def s19DomResT :
    HasTyT vecPrefixU 1
      [.assumption (.app (.app (.const 4 []) (.bvar 4)) (.bvar 0)),
       .assumption (.const 0 []), .assumption vecMinorCons,
       .assumption (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))),
       .assumption (vecMotTy 1), .assumption (.sort (.succ .zero))]
      (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0)) (.sort (.param 0)) :=
  .app _ (.app (.bvar 4) (.bvar 1)) (.bvar 0)
    (.app (.app (.const 4 []) (.bvar 5)) (.bvar 1)) (.sort (.param 0))
    (.app _ (.bvar 4) (.bvar 1) (.const 0 [])
      (.pi (.app (.app (.const 4 []) (.bvar 6)) (.bvar 0)) (.sort (.param 0)))
      (.bvar _ 4 (vecMotTy 6) rfl) (.bvar _ 1 _ rfl))
    (.bvar _ 0 _ rfl)

/-- the domain fields transported to `vecEnvUT` along `vecPrefToUT`. -/
noncomputable def s19Dom0U :
    HasTyT vecEnvUT 1 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  hasTyTExt vecPrefToUT s19Dom0T
noncomputable def s19Dom1U :
    HasTyT vecEnvUT 1 [.assumption (.sort (.succ .zero))] (vecMotTy 1)
      (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ (.param 0))))) :=
  hasTyTExt vecPrefToUT s19Dom1T
noncomputable def s19Dom2U :
    HasTyT vecEnvUT 1
      [.assumption (vecMotTy 1), .assumption (.sort (.succ .zero))]
      (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1)))
      (.sort (.param 0)) :=
  hasTyTExt vecPrefToUT s19Dom2T
noncomputable def s19Dom3U :
    HasTyT vecEnvUT 1
      [.assumption (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))),
       .assumption (vecMotTy 1), .assumption (.sort (.succ .zero))]
      vecMinorCons
      (.sort (.imax (.succ .zero) (.imax (.succ .zero)
        (.imax (.succ .zero) (.imax (.param 0) (.param 0)))))) :=
  hasTyTExt vecPrefToUT s19Dom3T
noncomputable def s19Dom4U :
    HasTyT vecEnvUT 1
      [.assumption vecMinorCons,
       .assumption (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))),
       .assumption (vecMotTy 1), .assumption (.sort (.succ .zero))]
      (.const 0 []) (.sort (.succ .zero)) :=
  hasTyTExt vecPrefToUT s19Dom4T
noncomputable def s19Dom5U :
    HasTyT vecEnvUT 1
      [.assumption (.const 0 []), .assumption vecMinorCons,
       .assumption (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))),
       .assumption (vecMotTy 1), .assumption (.sort (.succ .zero))]
      (.app (.app (.const 4 []) (.bvar 4)) (.bvar 0)) (.sort (.succ .zero)) :=
  hasTyTExt vecPrefToUT s19Dom5T
noncomputable def s19DomResU :
    HasTyT vecEnvUT 1
      [.assumption (.app (.app (.const 4 []) (.bvar 4)) (.bvar 0)),
       .assumption (.const 0 []), .assumption vecMinorCons,
       .assumption (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))),
       .assumption (vecMotTy 1), .assumption (.sort (.succ .zero))]
      (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0)) (.sort (.param 0)) :=
  hasTyTExt vecPrefToUT s19DomResT

/-- the telescope contexts as `CtxWfT`s at `n = 1` — the `esub` domains
    live in them before the level instantiation. -/
noncomputable def s19CtxA : CtxWfT vecEnvUT 1 [.assumption (.sort (.succ .zero))] :=
  .assumption _ _ _ .nil s19Dom0U
noncomputable def s19CtxM :
    CtxWfT vecEnvUT 1 [.assumption (vecMotTy 1), .assumption (.sort (.succ .zero))] :=
  .assumption _ _ _ s19CtxA s19Dom1U
noncomputable def s19CtxMn :
    CtxWfT vecEnvUT 1
      [.assumption (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))),
       .assumption (vecMotTy 1), .assumption (.sort (.succ .zero))] :=
  .assumption _ _ _ s19CtxM s19Dom2U
noncomputable def s19CtxMc :
    CtxWfT vecEnvUT 1
      [.assumption vecMinorCons,
       .assumption (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))),
       .assumption (vecMotTy 1), .assumption (.sort (.succ .zero))] :=
  .assumption _ _ _ s19CtxMn s19Dom3U
noncomputable def s19CtxK :
    CtxWfT vecEnvUT 1
      [.assumption (.const 0 []), .assumption vecMinorCons,
       .assumption (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))),
       .assumption (vecMotTy 1), .assumption (.sort (.succ .zero))] :=
  .assumption _ _ _ s19CtxMc s19Dom4U
noncomputable def s19CtxXs :
    CtxWfT vecEnvUT 1
      [.assumption (.app (.app (.const 4 []) (.bvar 4)) (.bvar 0)),
       .assumption (.const 0 []), .assumption vecMinorCons,
       .assumption (.app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.bvar 1))),
       .assumption (vecMotTy 1), .assumption (.sort (.succ .zero))] :=
  .assumption _ _ _ s19CtxK s19Dom5U

/-- the post-instantiation domain literals (at `σ = [.succ .zero]`, then
    after the named substitutions). -/
abbrev s19DomA1 : Expr Nat := .sort (.succ .zero)
abbrev s19DomM1 : Expr Nat :=
  .pi (.const 0 [])
    (.pi (.app (.app (.const 4 []) (.const 0 [])) (.bvar 0)) (.sort (.succ .zero)))
abbrev s19DomMn1 : Expr Nat :=
  .app (.app vecMotiveS19 (.const 1 [])) (.app (.const 5 []) (.const 0 []))

/-- the `A := N` intermediate forms that `substRemove` leaves in the
    surviving telescope entries (the `esub` `hv`/`hvT` contexts). -/
abbrev s19DomMnA : Expr Nat :=
  .app (.app (.bvar 0) (.const 1 [])) (.app (.const 5 []) (.const 0 []))
abbrev s19DomMcA : Expr Nat :=
  .pi (.const 0 [])
    (.pi (.const 0 [])
      (.pi (s19VecAt (.bvar 1))
        (.pi (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0))
          (.app (.app (.bvar 5) (.app (.const 2 []) (.bvar 3)))
            (.app (.app (.app (.app (.const 6 []) (.const 0 [])) (.bvar 3))
              (.bvar 2)) (.bvar 1))))))

/-- the enriched argument derivations (one per real occurrence — the §6
    slot plan's `qa`s). -/
noncomputable def s19qA : TyP vecEnvUT 0 [] s19A (.sort (.succ .zero)) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil (s19NTy [])
noncomputable def s19qM : TyP vecEnvUT 0 [] vecMotiveS19
    (.pi (.const 0 [])
      (.pi (s19VecAt (.bvar 0)) (.sort (.succ .zero)))) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil (vecMotiveTyS19 [])
noncomputable def s19qMn : TyP vecEnvUT 0 [] s19Mn
    (.app (.app vecMotiveS19 s19N0) s19T0) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil s19MnTy
noncomputable def s19qMc : TyP vecEnvUT 0 [] vecMinorConsS19 s19McTy :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil s19McTy'
noncomputable def s19qK0 : TyP vecEnvUT 0 [] s19K0 (.const 0 []) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil (s19K0Ty [])
noncomputable def s19qMajor : TyP vecEnvUT 0 [] s19Major (s19VecAt s19K0) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil s19MajorTy
noncomputable def s19qN0 : TyP vecEnvUT 0 [] s19N0 (.const 0 []) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil (s19ZTy [])
noncomputable def s19qH0 : TyP vecEnvUT 0 [] s19H0 (.const 0 []) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil (s19H0Ty [])
noncomputable def s19qT0 : TyP vecEnvUT 0 [] s19T0 (s19VecAt s19N0) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil (s19T0Ty [])
noncomputable def s19qRec : TyP vecEnvUT 0 [] (recAppS19 s19N0 s19T0)
    (.app (.app vecMotiveS19 s19N0) s19T0) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil s19HRec
noncomputable def s19qRecT : TyP vecEnvUT 0 [] (recAppS19 s19N0 s19T0) (.const 0 []) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil s19HRecT
/-- `cβ` — the original β conversion `M n₀ t₀ ≡ N` enriched. -/
noncomputable def s19cβ : CvP vecEnvUT 0 []
    (.app (.app vecMotiveS19 s19N0) s19T0) (.const 0 []) (.sort (.succ .zero)) :=
  enrichConvT_of_envWfT vecEnvUWfT .nil (s19MotiveBeta [] (s19ZTy []) (s19T0Ty []))

/-- §6 slot 0 — `A`'s declaration domain `Sort 1`: the telescope's `d0`
    field transported and enriched (param-free, no `linst` needed). -/
noncomputable def domViewA : TyP vecEnvUT 0 [] s19DomA1
    (.sort (.succ (.succ .zero))) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil
    (hasTyTExt vecPrefToUT
      (.sort [] (.succ .zero) : HasTyT vecPrefixU 0 _ _ _))

/-- §6 slot 1 — `M`'s declaration domain `Π k:N. Π xs:Vec A k. Sort 1`:
    `vecMotTy 1` `linst`'d at `σ` and `esub`'d by `s19qA`. -/
noncomputable def domViewM : TyP vecEnvUT 0 [] s19DomM1
    (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ (.succ .zero))))) :=
  .esub vecEnvUT 0 _ _ _ s19DomA1 s19A 0 _
    (.linst vecEnvUT 1 0 _ _ _ [.succ .zero] rfl rfl
      (enrichHasTyT_of_envWfT vecEnvUWfT s19CtxA s19Dom1U))
    rfl s19qA s19qA.reg.2

/-- §6 slot 2 — `mn`'s declaration domain `M zero (vnil A)`: `d2` after
    `A := N` then `M := vecMotiveS19`, paid by `s19qA`/`s19qM` and their regs. -/
noncomputable def domViewMn : TyP vecEnvUT 0 [] s19DomMn1 (.sort (.succ .zero)) :=
  .esub vecEnvUT 0 _ _ _ s19DomM1 vecMotiveS19 0 _
    (.esub vecEnvUT 0 _ _ _ s19DomA1 s19A 1 _
      (.linst vecEnvUT 1 0 _ _ _ [.succ .zero] rfl rfl
        (enrichHasTyT_of_envWfT vecEnvUWfT s19CtxM s19Dom2U))
      rfl
      (.wk vecEnvUT 0 _ _ _ (.assumption s19DomM1) 0 s19qA)
      (.wk vecEnvUT 0 _ _ _ (.assumption s19DomM1) 0 s19qA.reg.2))
    rfl s19qM s19qM.reg.2

/-- §6 slot 3 — `mc`'s declaration domain `s19McTy`: `vecMinorCons` after
    `A := N`, `M := vecMotiveS19`, `mn := zero` (a dead binder). -/
noncomputable def domViewMc : TyP vecEnvUT 0 [] s19McTy
    (.sort (.imax (.succ .zero) (.imax (.succ .zero)
      (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))))) :=
  .esub vecEnvUT 0 _ _ _ s19DomMn1 s19N0 0 _
    (.esub vecEnvUT 0 _ _ _ s19DomM1 vecMotiveS19 1 _
      (.esub vecEnvUT 0 _ _ _ s19DomA1 s19A 2 _
        (.linst vecEnvUT 1 0 _ _ _ [.succ .zero] rfl rfl
          (enrichHasTyT_of_envWfT vecEnvUWfT s19CtxMn s19Dom3U))
        rfl
        (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMnA) 0
          (.wk vecEnvUT 0 _ _ _ (.assumption s19DomM1) 0 s19qA))
        (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMnA) 0
          (.wk vecEnvUT 0 _ _ _ (.assumption s19DomM1) 0 s19qA.reg.2)))
      rfl
      (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMn1) 0 s19qM)
      (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMn1) 0 s19qM.reg.2))
    rfl s19qMn s19qMn.reg.2

/-- §6 slot 4 — the index `k`'s declaration domain `N`: `d4` after
    `A`, `M`, `mn`, `mc`. -/
noncomputable def domViewK : TyP vecEnvUT 0 [] (.const 0 []) (.sort (.succ .zero)) :=
  .esub vecEnvUT 0 _ _ _ s19McTy vecMinorConsS19 0 _
    (.esub vecEnvUT 0 _ _ _ s19DomMn1 s19N0 1 _
      (.esub vecEnvUT 0 _ _ _ s19DomM1 vecMotiveS19 2 _
        (.esub vecEnvUT 0 _ _ _ s19DomA1 s19A 3 _
          (.linst vecEnvUT 1 0 _ _ _ [.succ .zero] rfl rfl
            (enrichHasTyT_of_envWfT vecEnvUWfT s19CtxMc s19Dom4U))
          rfl
          (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMcA) 0
            (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMnA) 0
              (.wk vecEnvUT 0 _ _ _ (.assumption s19DomM1) 0 s19qA)))
          (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMcA) 0
            (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMnA) 0
              (.wk vecEnvUT 0 _ _ _ (.assumption s19DomM1) 0 s19qA.reg.2))))
        rfl
        (.wk vecEnvUT 0 _ _ _ (.assumption s19McTy) 0
          (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMn1) 0 s19qM))
        (.wk vecEnvUT 0 _ _ _ (.assumption s19McTy) 0
          (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMn1) 0 s19qM.reg.2)))
      rfl
      (.wk vecEnvUT 0 _ _ _ (.assumption s19McTy) 0 s19qMn)
      (.wk vecEnvUT 0 _ _ _ (.assumption s19McTy) 0 s19qMn.reg.2))
    rfl s19qMc s19qMc.reg.2

/-- §6 slot 5 — the major's declaration domain `Vec A k₀`: `d5` after
    `A`, `M`, `mn`, `mc`, `k := k₀`. -/
noncomputable def domViewMajorS19 : TyP vecEnvUT 0 [] (s19VecAt s19K0) (.sort (.succ .zero)) :=
  .esub vecEnvUT 0 _ _ _ (.const 0 []) s19K0 0 _
    (.esub vecEnvUT 0 _ _ _ s19McTy vecMinorConsS19 1 _
      (.esub vecEnvUT 0 _ _ _ s19DomMn1 s19N0 2 _
        (.esub vecEnvUT 0 _ _ _ s19DomM1 vecMotiveS19 3 _
          (.esub vecEnvUT 0 _ _ _ s19DomA1 s19A 4 _
            (.linst vecEnvUT 1 0 _ _ _ [.succ .zero] rfl rfl
              (enrichHasTyT_of_envWfT vecEnvUWfT s19CtxK s19Dom5U))
            rfl
            (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
              (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMcA) 0
                (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMnA) 0
                  (.wk vecEnvUT 0 _ _ _ (.assumption s19DomM1) 0 s19qA))))
            (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
              (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMcA) 0
                (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMnA) 0
                  (.wk vecEnvUT 0 _ _ _ (.assumption s19DomM1) 0 s19qA.reg.2)))))
          rfl
          (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
            (.wk vecEnvUT 0 _ _ _ (.assumption s19McTy) 0
              (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMn1) 0 s19qM)))
          (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
            (.wk vecEnvUT 0 _ _ _ (.assumption s19McTy) 0
              (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMn1) 0 s19qM.reg.2))))
        rfl
        (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
          (.wk vecEnvUT 0 _ _ _ (.assumption s19McTy) 0 s19qMn))
        (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
          (.wk vecEnvUT 0 _ _ _ (.assumption s19McTy) 0 s19qMn.reg.2)))
      rfl
      (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0 s19qMc)
      (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0 s19qMc.reg.2))
    rfl s19qK0 s19qK0.reg.2

/-- §6's directRec row — the recursive result's declaration domain `M n₀
    t₀`: the telescope's result field `M k xs` lazily instantiated at the
    real preceding arguments with `k := n₀`, `xs := t₀`. -/
noncomputable def domViewRes : TyP vecEnvUT 0 []
    (.app (.app vecMotiveS19 s19N0) s19T0) (.sort (.succ .zero)) :=
  .esub vecEnvUT 0 _ _ _ (s19VecAt s19N0) s19T0 0 _
    (.esub vecEnvUT 0 _ _ _ (.const 0 []) s19N0 1 _
      (.esub vecEnvUT 0 _ _ _ s19McTy vecMinorConsS19 2 _
        (.esub vecEnvUT 0 _ _ _ s19DomMn1 s19N0 3 _
          (.esub vecEnvUT 0 _ _ _ s19DomM1 vecMotiveS19 4 _
            (.esub vecEnvUT 0 _ _ _ s19DomA1 s19A 5 _
              (.linst vecEnvUT 1 0 _ _ _ [.succ .zero] rfl rfl
                (enrichHasTyT_of_envWfT vecEnvUWfT s19CtxXs s19DomResU))
              rfl
              (.wk vecEnvUT 0 _ _ _ (.assumption (s19VecAt (.bvar 0))) 0
                (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
                  (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMcA) 0
                    (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMnA) 0
                      (.wk vecEnvUT 0 _ _ _ (.assumption s19DomM1) 0 s19qA)))))
              (.wk vecEnvUT 0 _ _ _ (.assumption (s19VecAt (.bvar 0))) 0
                (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
                  (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMcA) 0
                    (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMnA) 0
                      (.wk vecEnvUT 0 _ _ _ (.assumption s19DomM1) 0 s19qA.reg.2))))))
            rfl
            (.wk vecEnvUT 0 _ _ _ (.assumption (s19VecAt (.bvar 0))) 0
              (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
                (.wk vecEnvUT 0 _ _ _ (.assumption s19McTy) 0
                  (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMn1) 0 s19qM))))
            (.wk vecEnvUT 0 _ _ _ (.assumption (s19VecAt (.bvar 0))) 0
              (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
                (.wk vecEnvUT 0 _ _ _ (.assumption s19McTy) 0
                  (.wk vecEnvUT 0 _ _ _ (.assumption s19DomMn1) 0 s19qM.reg.2)))))
          rfl
          (.wk vecEnvUT 0 _ _ _ (.assumption (s19VecAt (.bvar 0))) 0
            (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
              (.wk vecEnvUT 0 _ _ _ (.assumption s19McTy) 0 s19qMn)))
          (.wk vecEnvUT 0 _ _ _ (.assumption (s19VecAt (.bvar 0))) 0
            (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
              (.wk vecEnvUT 0 _ _ _ (.assumption s19McTy) 0 s19qMn.reg.2))))
        rfl
        (.wk vecEnvUT 0 _ _ _ (.assumption (s19VecAt (.bvar 0))) 0
          (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0 s19qMc))
        (.wk vecEnvUT 0 _ _ _ (.assumption (s19VecAt (.bvar 0))) 0
          (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0 s19qMc.reg.2)))
      rfl
      (.wk vecEnvUT 0 _ _ _ (.assumption (s19VecAt s19N0)) 0 s19qN0)
      (.wk vecEnvUT 0 _ _ _ (.assumption (s19VecAt s19N0)) 0 s19qN0.reg.2))
    rfl s19qT0 s19qT0.reg.2

/-- the constructor's domain fields, at `vecPrefixU` — `vecConsType`'s own
    `vecConsTyT` children verbatim (param-free, `n = 0`). -/
noncomputable def s19CtorDom0T :
    HasTyT vecPrefixU 0 [] (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sort [] (.succ .zero)
noncomputable def s19CtorDom1T :
    HasTyT vecPrefixU 0 [.assumption (.sort (.succ .zero))] (.const 0 [])
      (.sort (.succ .zero)) :=
  natConstTyT rfl
noncomputable def s19CtorDom2T :
    HasTyT vecPrefixU 0 [.assumption (.const 0 []), .assumption (.sort (.succ .zero))]
      (.bvar 1) (.sort (.succ .zero)) :=
  .bvar _ 1 _ rfl
noncomputable def s19CtorDom3T :
    HasTyT vecPrefixU 0
      [.assumption (.bvar 1), .assumption (.const 0 []),
       .assumption (.sort (.succ .zero))]
      (.app (.app (.const 4 []) (.bvar 2)) (.bvar 1)) (.sort (.succ .zero)) :=
  vecOfTyT rfl (.bvar _ 2 _ rfl) (.bvar _ 1 _ rfl)

/-- §6 slot 6 — the constructor parameter `A`'s domain `Sort 1`. -/
noncomputable def domViewCtorA : TyP vecEnvUT 0 [] s19DomA1
    (.sort (.succ (.succ .zero))) :=
  enrichHasTyT_of_envWfT vecEnvUWfT .nil (hasTyTExt vecPrefToUT s19CtorDom0T)

/-- §6 slot 7 — `n`'s constructor domain `N` after `A := N`. -/
noncomputable def domViewCtorN : TyP vecEnvUT 0 [] (.const 0 []) (.sort (.succ .zero)) :=
  .esub vecEnvUT 0 _ _ _ s19DomA1 s19A 0 _
    (enrichHasTyT_of_envWfT vecEnvUWfT
      (.assumption _ _ _ .nil (hasTyTExt vecPrefToUT s19CtorDom0T))
      (hasTyTExt vecPrefToUT s19CtorDom1T))
    rfl s19qA s19qA.reg.2

/-- §6 slot 8 — `hd`'s constructor domain `A` after `A := N`, `n := n₀`:
    `bvar 1` instantiated to the real parameter. -/
noncomputable def domViewCtorHd : TyP vecEnvUT 0 [] (.const 0 []) (.sort (.succ .zero)) :=
  .esub vecEnvUT 0 _ _ _ (.const 0 []) s19N0 0 _
    (.esub vecEnvUT 0 _ _ _ s19DomA1 s19A 1 _
      (enrichHasTyT_of_envWfT vecEnvUWfT
        (.assumption _ _ _
          (.assumption _ _ _ .nil (hasTyTExt vecPrefToUT s19CtorDom0T))
          (hasTyTExt vecPrefToUT s19CtorDom1T))
        (hasTyTExt vecPrefToUT s19CtorDom2T))
      rfl
      (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0 s19qA)
      (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0 s19qA.reg.2))
    rfl s19qN0 s19qN0.reg.2

/-- §6 slot 9 — `tl`'s constructor domain `Vec A n` after `A`, `n := n₀`,
    `hd := h₀` — `Vec A n₀`. -/
noncomputable def domViewCtorTl : TyP vecEnvUT 0 [] (s19VecAt s19N0)
    (.sort (.succ .zero)) :=
  .esub vecEnvUT 0 _ _ _ (.const 0 []) s19H0 0 _
    (.esub vecEnvUT 0 _ _ _ (.const 0 []) s19N0 1 _
      (.esub vecEnvUT 0 _ _ _ s19DomA1 s19A 2 _
        (enrichHasTyT_of_envWfT vecEnvUWfT
          (.assumption _ _ _
            (.assumption _ _ _
              (.assumption _ _ _ .nil (hasTyTExt vecPrefToUT s19CtorDom0T))
              (hasTyTExt vecPrefToUT s19CtorDom1T))
            (hasTyTExt vecPrefToUT s19CtorDom2T))
          (hasTyTExt vecPrefToUT s19CtorDom3T))
        rfl
        (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
          (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0 s19qA))
        (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0
          (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0 s19qA.reg.2)))
      rfl
      (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0 s19qN0)
      (.wk vecEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0 s19qN0.reg.2))
    rfl s19qH0 s19qH0.reg.2

section
set_option maxHeartbeats 64000000

/-- ONE fused `decide` over every weighted bound in this section — the
    S18 recipe that took `RcicSynListConsIota` 97min → 7min. Inside a
    single `decide`, `whnf` memoizes each shared subterm: `AwVec`
    enrichment, `s19H.wt`, and every `domView*.wt` are each normalized
    once for the whole pass instead of once per theorem. Every public
    bound below is a zero-cost projection of this conjunction — same
    statements, same names. -/
private theorem s19ComputedBudgets :
    s19hL.wt AwVec = 1628661 ∧ s19hR.wt AwVec = 3308539 ∧
    AwVec 7 < s19Nι ∧
    domViewA.wt AwVec < s19Nι ∧ domViewM.wt AwVec < s19Nι ∧
    domViewMn.wt AwVec < s19Nι ∧ domViewMc.wt AwVec < s19Nι ∧
    domViewK.wt AwVec < s19Nι ∧ domViewMajorS19.wt AwVec < s19Nι ∧
    domViewRes.wt AwVec < s19Nι ∧ domViewCtorA.wt AwVec < s19Nι ∧
    domViewCtorN.wt AwVec < s19Nι ∧ domViewCtorHd.wt AwVec < s19Nι ∧
    domViewCtorTl.wt AwVec < s19Nι ∧
    s19qRecT.wt AwVec < s19Nι ∧
    s19qA.wt AwVec < domViewM.wt AwVec ∧ s19qM.wt AwVec < domViewMn.wt AwVec ∧
    s19qMn.wt AwVec < domViewMc.wt AwVec ∧ s19qMc.wt AwVec < domViewK.wt AwVec ∧
    s19qK0.wt AwVec < domViewMajorS19.wt AwVec ∧
    s19qN0.wt AwVec < domViewCtorHd.wt AwVec ∧
    s19qH0.wt AwVec < domViewCtorTl.wt AwVec ∧
    s19qT0.wt AwVec < domViewRes.wt AwVec ∧
    s19qMajor.wt AwVec < s19hL.wt AwVec ∧ s19qRec.wt AwVec < s19hR.wt AwVec ∧
    s19cβ.wt AwVec < s19qRecT.wt AwVec := by decide

/-- kernel-verified weights of the two iota legs — the fused decide's
    first two projections, reused as literals by every bound below
    (`Nι = 9874401`). -/
theorem s19hL_wt_val : s19hL.wt AwVec = 1628661 := s19ComputedBudgets.1
theorem s19hR_wt_val : s19hR.wt AwVec = 3308539 := s19ComputedBudgets.2.1

/-- `Nι` as a literal — pure rewrite over `s19Nι_eq`, so no downstream
    bound re-normalizes the enriched legs. -/
theorem s19Nι_val : s19Nι = 9874401 := by
  rw [s19Nι_eq, s19hL_wt_val, s19hR_wt_val]

/-- the legs' own weights are strictly below `Nι` for free. -/
theorem s19hL_wt_lt : s19hL.wt AwVec < s19Nι := by
  rw [s19Nι_eq]; omega
theorem s19hR_wt_lt : s19hR.wt AwVec < s19Nι := by
  rw [s19Nι_eq]; omega

/-- the recursor const's own admission atom is paid through `AwVec 7` —
    strictly below `Nι`. -/
theorem s19_aw7_below : AwVec 7 < s19Nι := s19ComputedBudgets.2.2.1

/-- each view's own total weight is below `Nι` — fused-decide
    projections, no re-normalization. -/
theorem domViewA_wt : domViewA.wt AwVec < s19Nι := s19ComputedBudgets.2.2.2.1
theorem domViewM_wt : domViewM.wt AwVec < s19Nι := s19ComputedBudgets.2.2.2.2.1
theorem domViewMn_wt : domViewMn.wt AwVec < s19Nι := s19ComputedBudgets.2.2.2.2.2.1
theorem domViewMc_wt : domViewMc.wt AwVec < s19Nι := s19ComputedBudgets.2.2.2.2.2.2.1
theorem domViewK_wt : domViewK.wt AwVec < s19Nι := s19ComputedBudgets.2.2.2.2.2.2.2.1
theorem domViewMajorS19_wt : domViewMajorS19.wt AwVec < s19Nι :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.1
theorem domViewRes_wt : domViewRes.wt AwVec < s19Nι := s19ComputedBudgets.2.2.2.2.2.2.2.2.2.1
theorem domViewCtorA_wt : domViewCtorA.wt AwVec < s19Nι :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.1
theorem domViewCtorN_wt : domViewCtorN.wt AwVec < s19Nι :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.1
theorem domViewCtorHd_wt : domViewCtorHd.wt AwVec < s19Nι :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem domViewCtorTl_wt : domViewCtorTl.wt AwVec < s19Nι :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- every atom stored in each declaration-domain view is strictly below
    `Nι` — discharged through `atoms_lt_of_wt_lt` from the view's `wt`. -/
theorem domViewA_atoms : ∀ a ∈ domViewA.atoms AwVec, a < s19Nι :=
  atoms_lt_of_wt_lt AwVec domViewA domViewA_wt
theorem domViewM_atoms : ∀ a ∈ domViewM.atoms AwVec, a < s19Nι :=
  atoms_lt_of_wt_lt AwVec domViewM domViewM_wt
theorem domViewMn_atoms : ∀ a ∈ domViewMn.atoms AwVec, a < s19Nι :=
  atoms_lt_of_wt_lt AwVec domViewMn domViewMn_wt
theorem domViewMc_atoms : ∀ a ∈ domViewMc.atoms AwVec, a < s19Nι :=
  atoms_lt_of_wt_lt AwVec domViewMc domViewMc_wt
theorem domViewK_atoms : ∀ a ∈ domViewK.atoms AwVec, a < s19Nι :=
  atoms_lt_of_wt_lt AwVec domViewK domViewK_wt
theorem domViewMajorS19_atoms : ∀ a ∈ domViewMajorS19.atoms AwVec, a < s19Nι :=
  atoms_lt_of_wt_lt AwVec domViewMajorS19 domViewMajorS19_wt
theorem domViewRes_atoms : ∀ a ∈ domViewRes.atoms AwVec, a < s19Nι :=
  atoms_lt_of_wt_lt AwVec domViewRes domViewRes_wt
theorem domViewCtorA_atoms : ∀ a ∈ domViewCtorA.atoms AwVec, a < s19Nι :=
  atoms_lt_of_wt_lt AwVec domViewCtorA domViewCtorA_wt
theorem domViewCtorN_atoms : ∀ a ∈ domViewCtorN.atoms AwVec, a < s19Nι :=
  atoms_lt_of_wt_lt AwVec domViewCtorN domViewCtorN_wt
theorem domViewCtorHd_atoms : ∀ a ∈ domViewCtorHd.atoms AwVec, a < s19Nι :=
  atoms_lt_of_wt_lt AwVec domViewCtorHd domViewCtorHd_wt
theorem domViewCtorTl_atoms : ∀ a ∈ domViewCtorTl.atoms AwVec, a < s19Nι :=
  atoms_lt_of_wt_lt AwVec domViewCtorTl domViewCtorTl_wt

/-- §6's eleven declaration-domain views, as stored `TyP`s. -/
noncomputable def s19DeclViews : List (Σ e T, TyP vecEnvUT 0 [] e T) :=
  [⟨_, _, domViewA⟩, ⟨_, _, domViewM⟩, ⟨_, _, domViewMn⟩, ⟨_, _, domViewMc⟩,
   ⟨_, _, domViewK⟩, ⟨_, _, domViewMajorS19⟩, ⟨_, _, domViewCtorA⟩,
   ⟨_, _, domViewCtorN⟩, ⟨_, _, domViewCtorHd⟩, ⟨_, _, domViewCtorTl⟩,
   ⟨_, _, domViewRes⟩]

/-- the fixed declaration-domain budget: every atom of every
    lazy-instantiated view is strictly below `Nι` — membership cases routed
    to the per-view atom bounds, no normalization. -/
theorem s19_decl_budget :
    ∀ v ∈ s19DeclViews, ∀ a ∈ v.2.2.atoms AwVec, a < s19Nι := by
  intro v hv a ha
  simp only [s19DeclViews] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact domViewA_atoms a ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact domViewM_atoms a ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact domViewMn_atoms a ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact domViewMc_atoms a ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact domViewK_atoms a ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact domViewMajorS19_atoms a ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact domViewCtorA_atoms a ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact domViewCtorN_atoms a ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact domViewCtorHd_atoms a ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact domViewCtorTl_atoms a ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact domViewRes_atoms a ha
  · cases hv

/-! ## §6 the 11-occurrence slot plan -/

/-- §6 request kinds: pair-below `PB[a,b]`, the bit `BIT[a,b]` on two
    sort typings of one type, and an outer `CL[a,b]`. -/
inductive S19Request : Type where
  | pb {e₁ T₁ e₂ T₂ : Expr Nat}
      (a : TyP vecEnvUT 0 [] e₁ T₁) (b : TyP vecEnvUT 0 [] e₂ T₂)
  | bit {T : Expr Nat} {u v : Level}
      (a : TyP vecEnvUT 0 [] T (.sort u)) (b : TyP vecEnvUT 0 [] T (.sort v))
  | cl {e T₁ T₂ : Expr Nat}
      (a : TyP vecEnvUT 0 [] e T₁) (b : TyP vecEnvUT 0 [] e T₂)

/-- the derivations each request stores. -/
def S19Request.derivations : S19Request → List (Σ e T, TyP vecEnvUT 0 [] e T)
  | .pb a b | .cl a b => [⟨_, _, a⟩, ⟨_, _, b⟩]
  | .bit a b => [⟨_, _, a⟩, ⟨_, _, b⟩]

/-- §6's freezable request table: eleven slot PBs (the two `A` copies are
    distinct occurrences at positions 0 and 6), eleven slot BITs, the K1
    pair on the motive-β conversion, and the four outer requests. -/
noncomputable def s19Requests : List S19Request :=
  [ .pb s19qA s19qA.reg.2, .pb s19qM s19qM.reg.2, .pb s19qMn s19qMn.reg.2, .pb s19qMc s19qMc.reg.2,
    .pb s19qK0 s19qK0.reg.2, .pb s19qMajor s19qMajor.reg.2,
    .pb s19qA s19qA.reg.2,
    .pb s19qN0 s19qN0.reg.2, .pb s19qH0 s19qH0.reg.2, .pb s19qT0 s19qT0.reg.2,
    .pb s19qRec s19qRec.reg.2,
    .bit s19qA.reg.2 domViewA, .bit s19qM.reg.2 domViewM,
    .bit s19qMn.reg.2 domViewMn, .bit s19qMc.reg.2 domViewMc,
    .bit s19qK0.reg.2 domViewK, .bit s19qMajor.reg.2 domViewMajorS19,
    .bit s19qA.reg.2 domViewCtorA, .bit s19qN0.reg.2 domViewCtorN,
    .bit s19qH0.reg.2 domViewCtorHd, .bit s19qT0.reg.2 domViewCtorTl,
    .bit s19qRec.reg.2 domViewRes,
    .bit s19qRecT.reg.2 s19cβ.dr, .bit s19cβ.dl domViewRes,
    .pb s19hL s19hL.reg.2, .pb s19hR s19hL.reg.2,
    .cl s19H.dl s19hL, .cl s19hR s19H.dr ]

/-- §6's per-element weight bounds — fused-decide projections. The `q*`s
    are literally the `hv`s the lazy-instantiated views' `esub`s pay
    (`domViewRes`'s chain alone covers six of them), `s19qMajor`/`s19qRec`
    are literal children of the legs' app spines, and `s19cβ` is
    `s19qRecT`'s own conversion child. The `.reg.2` sides stay free
    through `TyP.wt_reg_le`. -/
theorem s19qA_wt_lt : s19qA.wt AwVec < domViewM.wt AwVec :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem s19qM_wt_lt : s19qM.wt AwVec < domViewMn.wt AwVec :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem s19qMn_wt_lt : s19qMn.wt AwVec < domViewMc.wt AwVec :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem s19qMc_wt_lt : s19qMc.wt AwVec < domViewK.wt AwVec :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem s19qK0_wt_lt : s19qK0.wt AwVec < domViewMajorS19.wt AwVec :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem s19qN0_wt_lt : s19qN0.wt AwVec < domViewCtorHd.wt AwVec :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem s19qH0_wt_lt : s19qH0.wt AwVec < domViewCtorTl.wt AwVec :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem s19qT0_wt_lt : s19qT0.wt AwVec < domViewRes.wt AwVec :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem s19qMajor_wt_lt : s19qMajor.wt AwVec < s19hL.wt AwVec :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem s19qRec_wt_lt : s19qRec.wt AwVec < s19hR.wt AwVec :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem s19cβ_wt_lt : s19cβ.wt AwVec < s19qRecT.wt AwVec :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem s19b_qA : s19qA.wt AwVec < s19Nι ∧ s19qA.reg.2.wt AwVec < s19Nι :=
  ⟨Nat.lt_trans s19qA_wt_lt domViewM_wt,
   Nat.lt_of_le_of_lt (TyP.wt_reg_le AwVec s19qA) (Nat.lt_trans s19qA_wt_lt domViewM_wt)⟩
theorem s19b_qM : s19qM.wt AwVec < s19Nι ∧ s19qM.reg.2.wt AwVec < s19Nι :=
  ⟨Nat.lt_trans s19qM_wt_lt domViewMn_wt,
   Nat.lt_of_le_of_lt (TyP.wt_reg_le AwVec s19qM) (Nat.lt_trans s19qM_wt_lt domViewMn_wt)⟩
theorem s19b_qMn : s19qMn.wt AwVec < s19Nι ∧ s19qMn.reg.2.wt AwVec < s19Nι :=
  ⟨Nat.lt_trans s19qMn_wt_lt domViewMc_wt,
   Nat.lt_of_le_of_lt (TyP.wt_reg_le AwVec s19qMn) (Nat.lt_trans s19qMn_wt_lt domViewMc_wt)⟩
theorem s19b_qMc : s19qMc.wt AwVec < s19Nι ∧ s19qMc.reg.2.wt AwVec < s19Nι :=
  ⟨Nat.lt_trans s19qMc_wt_lt domViewK_wt,
   Nat.lt_of_le_of_lt (TyP.wt_reg_le AwVec s19qMc) (Nat.lt_trans s19qMc_wt_lt domViewK_wt)⟩
theorem s19b_qK0 : s19qK0.wt AwVec < s19Nι ∧ s19qK0.reg.2.wt AwVec < s19Nι :=
  ⟨Nat.lt_trans s19qK0_wt_lt domViewMajorS19_wt,
   Nat.lt_of_le_of_lt (TyP.wt_reg_le AwVec s19qK0) (Nat.lt_trans s19qK0_wt_lt domViewMajorS19_wt)⟩
theorem s19b_qMajor : s19qMajor.wt AwVec < s19Nι ∧ s19qMajor.reg.2.wt AwVec < s19Nι :=
  ⟨Nat.lt_trans s19qMajor_wt_lt s19hL_wt_lt,
   Nat.lt_of_le_of_lt (TyP.wt_reg_le AwVec s19qMajor) (Nat.lt_trans s19qMajor_wt_lt s19hL_wt_lt)⟩
theorem s19b_qN0 : s19qN0.wt AwVec < s19Nι ∧ s19qN0.reg.2.wt AwVec < s19Nι :=
  ⟨Nat.lt_trans s19qN0_wt_lt domViewCtorHd_wt,
   Nat.lt_of_le_of_lt (TyP.wt_reg_le AwVec s19qN0) (Nat.lt_trans s19qN0_wt_lt domViewCtorHd_wt)⟩
theorem s19b_qH0 : s19qH0.wt AwVec < s19Nι ∧ s19qH0.reg.2.wt AwVec < s19Nι :=
  ⟨Nat.lt_trans s19qH0_wt_lt domViewCtorTl_wt,
   Nat.lt_of_le_of_lt (TyP.wt_reg_le AwVec s19qH0) (Nat.lt_trans s19qH0_wt_lt domViewCtorTl_wt)⟩
theorem s19b_qT0 : s19qT0.wt AwVec < s19Nι ∧ s19qT0.reg.2.wt AwVec < s19Nι :=
  ⟨Nat.lt_trans s19qT0_wt_lt domViewRes_wt,
   Nat.lt_of_le_of_lt (TyP.wt_reg_le AwVec s19qT0) (Nat.lt_trans s19qT0_wt_lt domViewRes_wt)⟩
theorem s19b_qRec : s19qRec.wt AwVec < s19Nι ∧ s19qRec.reg.2.wt AwVec < s19Nι :=
  ⟨Nat.lt_trans s19qRec_wt_lt s19hR_wt_lt,
   Nat.lt_of_le_of_lt (TyP.wt_reg_le AwVec s19qRec) (Nat.lt_trans s19qRec_wt_lt s19hR_wt_lt)⟩
theorem s19b_qRecT : s19qRecT.wt AwVec < s19Nι :=
  s19ComputedBudgets.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem s19cβ_wt_below : s19cβ.wt AwVec < s19Nι :=
  Nat.lt_trans s19cβ_wt_lt s19b_qRecT
theorem s19b_cβdl : s19cβ.dl.wt AwVec < s19Nι :=
  Nat.lt_trans (CvP.wt_dl_lt AwVec s19cβ) s19cβ_wt_below
theorem s19b_cβdr : s19cβ.dr.wt AwVec < s19Nι :=
  Nat.lt_trans (CvP.wt_dr_lt AwVec s19cβ) s19cβ_wt_below

/-- `hL.reg.2` below `Nι` — no kernel work: `wt_reg_le` + the leg bound. -/
theorem s19b_hLreg : s19hL.reg.2.wt AwVec < s19Nι :=
  Nat.lt_of_le_of_lt (TyP.wt_reg_le AwVec s19hL) s19hL_wt_lt

/-- two stored derivations each below `Nι` discharge a two-element
    membership directly — no search. -/
private theorem s19_mem2 {e₁ T₁ e₂ T₂ : Expr Nat}
    {a : TyP vecEnvUT 0 [] e₁ T₁} {b : TyP vecEnvUT 0 [] e₂ T₂}
    (ha : a.wt AwVec < s19Nι) (hb : b.wt AwVec < s19Nι)
    {D : Σ e T, TyP vecEnvUT 0 [] e T}
    (hD : D ∈ [⟨_, _, a⟩, ⟨_, _, b⟩]) : D.2.2.wt AwVec < s19Nι := by
  rcases List.mem_cons.mp hD with rfl | hD
  · exact ha
  rcases List.mem_cons.mp hD with rfl | hD
  · exact hb
  · cases hD

/-- every stored derivation's weight is strictly below `Nι` — membership
    cases routed to the per-element bounds, no search. -/
theorem s19_requests_below :
    ∀ r ∈ s19Requests, ∀ D ∈ r.derivations, D.2.2.wt AwVec < s19Nι := by
  intro r hr D hD
  simp only [s19Requests] at hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qA.1 s19b_qA.2 hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qM.1 s19b_qM.2 hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qMn.1 s19b_qMn.2 hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qMc.1 s19b_qMc.2 hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qK0.1 s19b_qK0.2 hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qMajor.1 s19b_qMajor.2 hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qA.1 s19b_qA.2 hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qN0.1 s19b_qN0.2 hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qH0.1 s19b_qH0.2 hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qT0.1 s19b_qT0.2 hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qRec.1 s19b_qRec.2 hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qA.2 domViewA_wt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qM.2 domViewM_wt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qMn.2 domViewMn_wt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qMc.2 domViewMc_wt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qK0.2 domViewK_wt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qMajor.2 domViewMajorS19_wt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qA.2 domViewCtorA_wt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qN0.2 domViewCtorN_wt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qH0.2 domViewCtorHd_wt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qT0.2 domViewCtorTl_wt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_qRec.2 domViewRes_wt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2
      (Nat.lt_of_le_of_lt (TyP.wt_reg_le AwVec s19qRecT) s19b_qRecT) s19b_cβdr hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19b_cβdl domViewRes_wt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19hL_wt_lt s19b_hLreg hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19hR_wt_lt s19b_hLreg hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19hL_wt_lt s19hL_wt_lt hD
  rcases List.mem_cons.mp hr with rfl | hr
  · exact s19_mem2 s19hR_wt_lt s19hR_wt_lt hD
  · cases hr

/-- §6's eleven bit-false discharges, one per real slot — kernel-evaluated
    `levelIsZero` on the real regularity level at `σ = id`. -/
theorem s19bit_qA : levelIsZero (id s19qA.reg.1) = false := by decide
theorem s19bit_qM : levelIsZero (id s19qM.reg.1) = false := by decide
theorem s19bit_qMn : levelIsZero (id s19qMn.reg.1) = false := by decide
theorem s19bit_qMc : levelIsZero (id s19qMc.reg.1) = false := by decide
theorem s19bit_qK0 : levelIsZero (id s19qK0.reg.1) = false := by decide
theorem s19bit_qMajor : levelIsZero (id s19qMajor.reg.1) = false := by decide
theorem s19bit_qN0 : levelIsZero (id s19qN0.reg.1) = false := by decide
theorem s19bit_qH0 : levelIsZero (id s19qH0.reg.1) = false := by decide
theorem s19bit_qT0 : levelIsZero (id s19qT0.reg.1) = false := by decide
theorem s19bit_qRec : levelIsZero (id s19qRec.reg.1) = false := by decide
theorem s19bit_qRecT : levelIsZero (id s19qRecT.reg.1) = false := by decide

/-- §6's `qa.reg.2.wt ≤ qa.wt` side of each PB payment — substrate lemma,
    no kernel computation. -/
theorem s19reg_le_qA : s19qA.reg.2.wt AwVec ≤ s19qA.wt AwVec := TyP.wt_reg_le AwVec s19qA
theorem s19reg_le_qM : s19qM.reg.2.wt AwVec ≤ s19qM.wt AwVec := TyP.wt_reg_le AwVec s19qM
theorem s19reg_le_qMn : s19qMn.reg.2.wt AwVec ≤ s19qMn.wt AwVec := TyP.wt_reg_le AwVec s19qMn
theorem s19reg_le_qMc : s19qMc.reg.2.wt AwVec ≤ s19qMc.wt AwVec := TyP.wt_reg_le AwVec s19qMc
theorem s19reg_le_qK0 : s19qK0.reg.2.wt AwVec ≤ s19qK0.wt AwVec := TyP.wt_reg_le AwVec s19qK0
theorem s19reg_le_qMajor : s19qMajor.reg.2.wt AwVec ≤ s19qMajor.wt AwVec := TyP.wt_reg_le AwVec s19qMajor
theorem s19reg_le_qN0 : s19qN0.reg.2.wt AwVec ≤ s19qN0.wt AwVec := TyP.wt_reg_le AwVec s19qN0
theorem s19reg_le_qH0 : s19qH0.reg.2.wt AwVec ≤ s19qH0.wt AwVec := TyP.wt_reg_le AwVec s19qH0
theorem s19reg_le_qT0 : s19qT0.reg.2.wt AwVec ≤ s19qT0.wt AwVec := TyP.wt_reg_le AwVec s19qT0
theorem s19reg_le_qRec : s19qRec.reg.2.wt AwVec ≤ s19qRec.wt AwVec := TyP.wt_reg_le AwVec s19qRec

/-- the K1 pair on the original motive-β conversion — natural side
    `s19qRecT.reg.2`/the retained view `domViewRes` through `s19cβ`. -/
theorem s19_k1_pair_1 : BitCoh id s19qRecT.reg.2 s19cβ.dr := rfl
theorem s19_k1_pair_2 : BitCoh id s19cβ.dl domViewRes := rfl

end

/-! ## §7 the two index equations, proved separately -/

/-- constructor-result index: `applyTel` of the three fields on
    `ctorAfterParams` lands on `Vec A (succ n₀)`, whose family index is
    `[succ n₀] = [k₀]` — the major's own index, binding the index slot. -/
theorem s19_ctor_result_idx :
    Option.map (familyIdx 1)
      (applyTel [s19N0, s19H0, s19T0] wVecCons0.ctorAfterParams) =
      some [s19K0] := rfl

/-- recursive-field index: `familyIdx` of the directRec field's own type
    `Vec A n₀` (the `tl` domain after `n := n₀`) is `[n₀]` — what decides
    the RHS recursive call. -/
theorem s19_rec_field_idx :
    familyIdx 1 (s19VecAt s19N0) = [s19N0] := rfl

/-- the `tl` domain inside `ctorAfterParams` after `n := n₀`, `hd := h₀`
    IS `Vec A n₀` — the field's own type, not the major's result. -/
theorem s19_field2_dom :
    applyTel [s19N0, s19H0] wVecCons0.ctorAfterParams =
      some (.pi (s19VecAt s19N0) (s19VecAt s19K0)) := rfl

/-- their difference IS the indexed contribution: `[k₀] ≠ [n₀]`. -/
theorem s19_idx_gap : [s19K0] ≠ [s19N0] := by decide

/-! ## §8 the singleton Vec-cons rule, `TableWF`, the match, nine β steps
    to `ER`, and the `ES` theorem -/

/-- the erasures of the real arguments (spec §8). -/
def s19Aε : ETm := .const 0 []
def s19Mε : ETm := .lam (.lam (.const 0 []))
def s19Mnε : ETm := .const 1 []
def s19Mcε : ETm := .lam (.lam (.lam (.lam (.bvar 2))))
def s19N0ε : ETm := .const 1 []
def s19K0ε : ETm := .app (.const 2 []) (.const 1 [])
def s19H0ε : ETm := .app (.const 2 []) (.const 1 []) |> .app (.const 2 [])
def s19T0ε : ETm := .app (.const 5 []) (.const 0 [])
def s19Majorε : ETm := ETm.appN (.const 6 []) [s19Aε, s19N0ε, s19H0ε, s19T0ε]

/-- `recε k x` — the erased recursor spine `const 7 [.succ .zero]` applied
    to the real prefix args plus index `k` and major `x`. -/
def s19Recε (k x : ETm) : ETm :=
  ETm.appN (.const 7 [.succ .zero]) [s19Aε, s19Mε, s19Mnε, s19Mcε, k, x]

/-- §8 `vecConsRule` — verbatim the spec's nine-λ template; innermost
    indices `A=8, M=7, mn=6, mc=5, kMajor=4, A_ctor=3, nField=2, head=1,
    tail=0`, and the recursive call takes `bvar 2` (`nField`), never
    `bvar 4` (`kMajor`). -/
def vecConsRule : CRule where
  head := 7
  nargs := fun _ => 5
  major := some (6, fun _ => 4)
  rhs := fun ls _ =>
    .lam (.lam (.lam (.lam (.lam (.lam (.lam (.lam (.lam
      (ETm.appN (.bvar 5) [.bvar 2, .bvar 1, .bvar 0,
        ETm.appN (.const 7 ls)
          [.bvar 8, .bvar 7, .bvar 6, .bvar 5, .bvar 2, .bvar 0]])))))))))

/-- the singleton table. -/
def vecConsTable0 : List CRule := [vecConsRule]

/-- `TableWF` for the singleton, mirroring `natSuccTable_wf`: rhs
    congruence, closedness under nine λs, no rule for the constructor
    head `6`, singleton disjointness, empty bare premises. -/
theorem vecConsTable_wf : TableWF vecConsTable0 where
  congr :=
    { rhs := by
        intro ρ hρ ls₁ ls₂ ms₁ ms₂ hls _
        simp only [vecConsTable0, List.mem_singleton] at hρ; subst hρ
        exact .lam (.lam (.lam (.lam (.lam (.lam (.lam (.lam (.lam
          (.app (.app (.app (.app (.bvar _) (.bvar _)) (.bvar _)) (.bvar _))
            (lvlEq_appN (.const _ hls)
              (.cons (.bvar _) (.cons (.bvar _) (.cons (.bvar _)
                (.cons (.bvar _) (.cons (.bvar _)
                  (.cons (.bvar _) .nil))))))))))))))))
      nargs := by
        intro ρ hρ _ _ _
        simp only [vecConsTable0, List.mem_singleton] at hρ; subst hρ; rfl
      marity := by
        intro ρ hρ _ _ hm
        simp only [vecConsTable0, List.mem_singleton] at hρ; subst hρ
        cases hm; exact fun _ => rfl }
  closed := by
    intro ρ hρ ls ms
    simp only [vecConsTable0, List.mem_singleton] at hρ; subst hρ
    simp only [vecConsRule, ETm.appN, ETm.ClosedAt]
    exact ⟨by decide, by decide⟩
  rigid := by
    intro ρ hρ d m hm σ hσ
    simp only [vecConsTable0, List.mem_singleton] at hρ hσ; subst hρ; subst hσ
    cases hm; decide
  bare_unique := by
    intro ρ hρ hm σ hσ _
    simp only [vecConsTable0, List.mem_singleton] at hρ; subst hρ
    simp only [vecConsRule] at hm; exact Option.noConfusion hm
  ctor_disjoint := by
    intro ρ hρ σ hσ _ d e m n hm hn
    simp only [vecConsTable0, List.mem_singleton] at hρ hσ; subst hρ; subst hσ
    exact ⟨rfl, fun _ => rfl⟩
  bare_nullary := by
    intro ρ hρ hm ls
    simp only [vecConsTable0, List.mem_singleton] at hρ; subst hρ
    simp only [vecConsRule] at hm; exact Option.noConfusion hm

/-- `EL` — `s19hL`'s erasure: `recε k₀ε majorε` with the ctor spine as
    major. -/
def s19EL : ETm := ETm.appN (.const 7 [.succ .zero])
  [s19Aε, s19Mε, s19Mnε, s19Mcε, s19K0ε, s19Majorε]

/-- `ER` — the kept-result rhs:
    `mcε n₀ε h₀ε t₀ε (recε Aε Mε mnε mcε n₀ε t₀ε)`. -/
def s19ER : ETm :=
  ETm.appN s19Mcε [s19N0ε, s19H0ε, s19T0ε, s19Recε s19N0ε s19T0ε]

/-- the nine-λ template body at `ls = [.succ .zero]`:
    `mc n hd tl (rec A M mn mc n tl)` — `bvar 2` for the recursive index. -/
def s19Body : ETm :=
  ETm.appN (.bvar 5) [.bvar 2, .bvar 1, .bvar 0,
    ETm.appN (.const 7 [.succ .zero])
      [.bvar 8, .bvar 7, .bvar 6, .bvar 5, .bvar 2, .bvar 0]]

/-- the nine-λ template. -/
def s19Template : ETm :=
  .lam (.lam (.lam (.lam (.lam (.lam (.lam (.lam (.lam s19Body))))))))

/-- PIN: `vecConsRule`'s template at the concrete level list. -/
theorem vecConsRule_rhs_eq :
    vecConsRule.rhs [.succ .zero] [] = s19Template := rfl

/-- the two outer CLs hold reflexively on `H`'s chosen fields. -/
theorem s19_cl_outer_left : CL vecConsTable0 id [] s19H.dl s19hL := ConvMod.refl _
theorem s19_cl_outer_right : CL vecConsTable0 id [] s19hR s19H.dr := ConvMod.refl _

/-- PIN: the match root — `EL → appN template (args ++ bs)` with
    `args = [Aε, Mε, mnε, mcε, k₀ε]`, `bs = [Aε, n₀ε, h₀ε, t₀ε]`. -/
theorem vecCons_croot :
    CRoot vecConsTable0 s19EL
      (ETm.appN s19Template
        [s19Aε, s19Mε, s19Mnε, s19Mcε, s19K0ε, s19Aε, s19N0ε, s19H0ε, s19T0ε]) :=
  CRoot.ctor (List.mem_singleton_self _) rfl [.succ .zero] []
    [s19Aε, s19Mε, s19Mnε, s19Mcε, s19K0ε] [s19Aε, s19N0ε, s19H0ε, s19T0ε]
    rfl rfl

/-- the β residual bodies — `inst` chains at the absolute binder indices
    (`bvar 8` for `A` down to `bvar 1` for `h`; `bvar 0` is `t₀`'s own
    step). -/
def s19X1 : ETm := ETm.inst 8 s19Aε s19Body
def s19X2 : ETm := ETm.inst 7 s19Mε s19X1
def s19X3 : ETm := ETm.inst 6 s19Mnε s19X2
def s19X4 : ETm := ETm.inst 5 s19Mcε s19X3
def s19X5 : ETm := ETm.inst 4 s19K0ε s19X4
def s19X6 : ETm := ETm.inst 3 s19Aε s19X5
def s19X7 : ETm := ETm.inst 2 s19N0ε s19X6
def s19X8 : ETm := ETm.inst 1 s19H0ε s19X7

/-- the post-βᵢ terms — `lam^{9-i}` over the residual bodies. -/
def s19M1 : ETm := .lam (.lam (.lam (.lam (.lam (.lam (.lam (.lam s19X1)))))))
def s19M2 : ETm := .lam (.lam (.lam (.lam (.lam (.lam (.lam s19X2))))))
def s19M3 : ETm := .lam (.lam (.lam (.lam (.lam (.lam s19X3)))))
def s19M4 : ETm := .lam (.lam (.lam (.lam (.lam s19X4))))
def s19M5 : ETm := .lam (.lam (.lam (.lam s19X5)))
def s19M6 : ETm := .lam (.lam (.lam s19X6))
def s19M7 : ETm := .lam (.lam s19X7)
def s19M8 : ETm := .lam s19X8

/-- PIN: the nine-step chain lands on `ER` exactly — kernel index
    arithmetic, not a normal-value check. -/
theorem s19_beta9_tgt : ETm.inst 0 s19T0ε s19X8 = s19ER := rfl

/-- the nine β steps as `RStep`s, lifted through the outer applications. -/
def s19Step1 :
    RStep vecConsTable0
      (ETm.appN s19Template
        [s19Aε, s19Mε, s19Mnε, s19Mcε, s19K0ε, s19Aε, s19N0ε, s19H0ε, s19T0ε])
      (ETm.appN s19M1
        [s19Mε, s19Mnε, s19Mcε, s19K0ε, s19Aε, s19N0ε, s19H0ε, s19T0ε]) :=
  .appL s19T0ε (.appL s19H0ε (.appL s19N0ε (.appL s19Aε (.appL s19K0ε
    (.appL s19Mcε (.appL s19Mnε (.appL s19Mε
      (.beta (.lam (.lam (.lam (.lam (.lam (.lam (.lam (.lam s19Body))))))))
        s19Aε))))))))

def s19Step2 :
    RStep vecConsTable0
      (ETm.appN s19M1
        [s19Mε, s19Mnε, s19Mcε, s19K0ε, s19Aε, s19N0ε, s19H0ε, s19T0ε])
      (ETm.appN s19M2
        [s19Mnε, s19Mcε, s19K0ε, s19Aε, s19N0ε, s19H0ε, s19T0ε]) :=
  .appL s19T0ε (.appL s19H0ε (.appL s19N0ε (.appL s19Aε (.appL s19K0ε
    (.appL s19Mcε (.appL s19Mnε
      (.beta (.lam (.lam (.lam (.lam (.lam (.lam (.lam s19X1)))))))
        s19Mε)))))))

def s19Step3 :
    RStep vecConsTable0
      (ETm.appN s19M2
        [s19Mnε, s19Mcε, s19K0ε, s19Aε, s19N0ε, s19H0ε, s19T0ε])
      (ETm.appN s19M3
        [s19Mcε, s19K0ε, s19Aε, s19N0ε, s19H0ε, s19T0ε]) :=
  .appL s19T0ε (.appL s19H0ε (.appL s19N0ε (.appL s19Aε (.appL s19K0ε
    (.appL s19Mcε
      (.beta (.lam (.lam (.lam (.lam (.lam (.lam s19X2)))))) s19Mnε))))))

def s19Step4 :
    RStep vecConsTable0
      (ETm.appN s19M3
        [s19Mcε, s19K0ε, s19Aε, s19N0ε, s19H0ε, s19T0ε])
      (ETm.appN s19M4
        [s19K0ε, s19Aε, s19N0ε, s19H0ε, s19T0ε]) :=
  .appL s19T0ε (.appL s19H0ε (.appL s19N0ε (.appL s19Aε (.appL s19K0ε
    (.beta (.lam (.lam (.lam (.lam (.lam s19X3))))) s19Mcε)))))

def s19Step5 :
    RStep vecConsTable0
      (ETm.appN s19M4
        [s19K0ε, s19Aε, s19N0ε, s19H0ε, s19T0ε])
      (ETm.appN s19M5
        [s19Aε, s19N0ε, s19H0ε, s19T0ε]) :=
  .appL s19T0ε (.appL s19H0ε (.appL s19N0ε (.appL s19Aε
    (.beta (.lam (.lam (.lam (.lam s19X4)))) s19K0ε))))

def s19Step6 :
    RStep vecConsTable0
      (ETm.appN s19M5
        [s19Aε, s19N0ε, s19H0ε, s19T0ε])
      (ETm.appN s19M6
        [s19N0ε, s19H0ε, s19T0ε]) :=
  .appL s19T0ε (.appL s19H0ε (.appL s19N0ε
    (.beta (.lam (.lam (.lam s19X5))) s19Aε)))

def s19Step7 :
    RStep vecConsTable0
      (ETm.appN s19M6
        [s19N0ε, s19H0ε, s19T0ε])
      (ETm.appN s19M7
        [s19H0ε, s19T0ε]) :=
  .appL s19T0ε (.appL s19H0ε (.beta (.lam (.lam s19X6)) s19N0ε))

def s19Step8 :
    RStep vecConsTable0
      (ETm.appN s19M7
        [s19H0ε, s19T0ε])
      (ETm.app s19M8 s19T0ε) :=
  .appL s19T0ε (.beta (.lam s19X7) s19H0ε)

def s19Step9 :
    RStep vecConsTable0
      (ETm.app s19M8 s19T0ε) s19ER :=
  .beta s19X8 s19T0ε

/-- PIN: `s19hL.eps id []` is exactly `EL` — the real enriched typing's
    own erasure. -/
theorem s19hL_eps_el : s19hL.eps id [] = s19EL := rfl

/-- PIN: `s19hR.eps id []` is exactly `ER`. -/
theorem s19hR_eps_er : s19hR.eps id [] = s19ER := rfl

/-- §8's target: `ES vecConsTable0 id [] H` — the retained-result ι
    discharged by its real match plus exactly nine β steps. The recursive
    call is NOT reduced and the result is NOT normalized to `h₀`. -/
theorem vecCons_iota_erasure : ES vecConsTable0 id [] s19H := by
  show ConvMod (EStep vecConsTable0) LvlEq (s19hL.eps id []) (s19hR.eps id [])
  rw [s19hL_eps_el, s19hR_eps_er]
  exact (ConvMod.fwd (.inl (.cr vecCons_croot))).trans
    ((ConvMod.fwd (.inl s19Step1)).trans
      ((ConvMod.fwd (.inl s19Step2)).trans
        ((ConvMod.fwd (.inl s19Step3)).trans
          ((ConvMod.fwd (.inl s19Step4)).trans
            ((ConvMod.fwd (.inl s19Step5)).trans
              ((ConvMod.fwd (.inl s19Step6)).trans
                ((ConvMod.fwd (.inl s19Step7)).trans
                  ((ConvMod.fwd (.inl s19Step8)).trans
                    (ConvMod.fwd (.inl s19Step9))))))))))

/-! ## §9 the five exactness mutants -/

/-- (1) WRONG RECURSIVE INDEX — the template with `bvar 4` (`kMajor`) in
    the recursive call's index slot instead of `bvar 2` (`nField`). -/
def s19BodyMutIdx : ETm :=
  ETm.appN (.bvar 5) [.bvar 2, .bvar 1, .bvar 0,
    ETm.appN (.const 7 [.succ .zero])
      [.bvar 8, .bvar 7, .bvar 6, .bvar 5, .bvar 4, .bvar 0]]

/-- the mutant's nine-step result — the recursive call carries `k₀ε` at
    its index slot. -/
def s19MutIdxRhs : ETm :=
  ETm.appN s19Mcε [s19N0ε, s19H0ε, s19T0ε, s19Recε s19K0ε s19T0ε]

/-- PIN: the mutant template's nine-step inst chain lands on the wrong
    recursive index. -/
theorem s19_mut_idx_nine :
    ETm.inst 0 s19T0ε (ETm.inst 1 s19H0ε (ETm.inst 2 s19N0ε
      (ETm.inst 3 s19Aε (ETm.inst 4 s19K0ε (ETm.inst 5 s19Mcε
        (ETm.inst 6 s19Mnε (ETm.inst 7 s19Mε
          (ETm.inst 8 s19Aε s19BodyMutIdx)))))))) = s19MutIdxRhs := rfl

/-- the mutant nine-step RHS differs from `ER`. -/
theorem s19_mut_idx_rejected : s19MutIdxRhs ≠ s19ER := by decide

/-- …but `mc = λ⁴.x` discards `ih` — extra β reduction returns `h₀` on
    BOTH sides, so a final-value check wrongly accepts the mutant. -/
theorem s19_mut_idx_value :
    ETm.inst 0 (s19Recε s19K0ε s19T0ε)
      (ETm.inst 1 s19T0ε (ETm.inst 2 s19H0ε (ETm.inst 3 s19N0ε (.bvar 2)))) =
      s19H0ε := rfl
theorem s19_real_idx_value :
    ETm.inst 0 (s19Recε s19N0ε s19T0ε)
      (ETm.inst 1 s19T0ε (ETm.inst 2 s19H0ε (ETm.inst 3 s19N0ε (.bvar 2)))) =
      s19H0ε := rfl

/-- (2) WRONG MAJOR INDEX — `preMajor` with `h₀` (the head value `2`) in
    the index slot instead of `k₀` (`1`). -/
def wVecCons0MutMajor : IotaWitness vecEnvUT :=
  { wVecCons0 with preMajor := [s19A, vecMotiveS19, s19Mn, vecMinorConsS19, s19H0] }

/-- the mutant's raw lhs — `rec A M mn mc h₀ major` — is well-formed as a
    raw redex (the witness fields pass), but it is not our lhs. -/
theorem s19_mutMajor_lhs :
    iotaLhsOf wVecCons0MutMajor = recAppS19 s19H0 s19Major := rfl

/-- the fixed instance's actual lhs subject rejects it: `hL`'s subject is
    `rec … k₀ …`, not `rec … h₀ …`. -/
theorem s19_mutMajor_subject : iotaLhsOf wVecCons0MutMajor ≠ iotaLhsOf wVecCons0 := by
  decide

/-- the constructor-result-index correspondence rejects it: the major's
    own index is `[k₀]` (`s19_ctor_result_idx`), and the mutant's `h₀`
    fails the major-domain match `Vec A h₀ ≠ Vec A k₀`. -/
theorem s19_mutMajor_index :
    s19VecAt s19H0 ≠ s19VecAt s19K0 := by decide

/-- the slot plan rejects it: the index slot's stored derivation is `s19qK0`
    (`k₀ : N` at `const 0`), and `h₀`'s literal differs. -/
theorem s19_mutMajor_slot : s19K0 ≠ s19H0 := by decide

/-- (3) FIELD 0 MISCODED AS `directRec` — `n₀`'s domain is `N`, not a
    `Vec` family application: `rhsArgs` would manufacture a recursive call
    not present in the original — and it would read `familyIdx` of `N`
    (which is `[]`), producing a call missing its index slot. -/
theorem s19_mut_directRec0 :
    rhsArgs (.const 7 [.succ .zero]) wVecCons0.preMajor 1 2 wVecCons0.fields
      [.directRec, .plain, .directRec] wVecCons0.ctorAfterParams ≠
      rhsArgs (.const 7 [.succ .zero]) wVecCons0.preMajor 1 2 wVecCons0.fields
        wVecCons0.kinds wVecCons0.ctorAfterParams := by decide

/-- the manufactured call is `rec A M mn mc n₀` — a partial spine missing
    the real major argument and reading `[]` as the index list. -/
theorem s19_mut_directRec0_call :
    (rhsArgs (.const 7 [.succ .zero]) wVecCons0.preMajor 1 2 wVecCons0.fields
      [.directRec, .plain, .directRec] wVecCons0.ctorAfterParams).take 2 =
      [s19N0,
       foldApps (.const 7 [.succ .zero])
         [s19A, vecMotiveS19, s19Mn, vecMinorConsS19, s19N0]] := rfl

/-- (4) INDEX PARAMETER DROPPED — `nargs = 4` rejects at the original lhs
    match's length correspondence: the real `args` has five entries. -/
def vecConsRuleN4 : CRule := { vecConsRule with nargs := fun _ => 4 }

theorem s19_mut_nargs4 :
    [s19Aε, s19Mε, s19Mnε, s19Mcε, s19K0ε].length ≠ vecConsRuleN4.nargs [.succ .zero] := by
  decide

/-- the head of an application spine — `appN` preserves it. -/
def s19Head : ETm → ETm
  | .app f _ => s19Head f
  | e => e

theorem s19Head_appN (f : ETm) (bs : List ETm) :
    s19Head (ETm.appN f bs) = s19Head f := by
  induction bs generalizing f with
  | nil => rfl
  | cons b bs ih => exact ih (.app f b)

/-- with `nargs = 4` the "major" position would consume `k₀ε` — which is
    not a `const 6` constructor spine, so `CRoot.ctor` cannot even form
    the match. -/
theorem s19_mut_major_not_ctor (bs : List ETm) :
    s19K0ε ≠ ETm.appN (.const 6 []) bs := by
  intro h
  have hh := congrArg s19Head h
  rw [s19Head_appN] at hh
  exact absurd hh (by decide)

/-- (5) WRONG FIELD ORDER — swapping `nField`/`head` in `bs` produces a
    different nine-step result: `mc h₀ n₀ …` and the recursive call at
    index `h₀`. -/
def s19MutSwapRhs : ETm :=
  ETm.appN s19Mcε [s19H0ε, s19N0ε, s19T0ε, s19Recε s19H0ε s19T0ε]

theorem s19_mut_swap : s19MutSwapRhs ≠ s19ER := by decide

/-- the swapped template's nine-step chain lands on the mutant — the
    `bvar 2`/`bvar 1` positions pick up `h₀ε`/`n₀ε` respectively. -/
theorem s19_mut_swap_nine :
    ETm.inst 0 s19T0ε (ETm.inst 1 s19N0ε (ETm.inst 2 s19H0ε
      (ETm.inst 3 s19Aε (ETm.inst 4 s19K0ε (ETm.inst 5 s19Mcε
        (ETm.inst 6 s19Mnε (ETm.inst 7 s19Mε
          (ETm.inst 8 s19Aε s19Body)))))))) = s19MutSwapRhs := rfl

/-- and a wrong same-valued occurrence can't substitute: the ctor-side
    `A` slot's view types `sort 1`, the motive's `Π`-domain is a different
    type — `BitCoh` is per-type. -/
theorem s19_mut_param_dom : s19DomA1 ≠ s19DomM1 := by decide

#print axioms Rcic.Syn.wVecCons0
#print axioms Rcic.Syn.wVecCons0_lhs
#print axioms Rcic.Syn.wVecCons0_rhs
#print axioms Rcic.Syn.vecRecTele_eq
#print axioms Rcic.Syn.vecConsTele_eq
#print axioms Rcic.Syn.s19MotiveBeta
#print axioms Rcic.Syn.s19HLT
#print axioms Rcic.Syn.s19HRT
#print axioms Rcic.Syn.s19hL
#print axioms Rcic.Syn.s19hR
#print axioms Rcic.Syn.s19H
#print axioms Rcic.Syn.s19Nι_eq
#print axioms Rcic.Syn.s19_ctor_result_idx
#print axioms Rcic.Syn.s19_rec_field_idx
#print axioms Rcic.Syn.s19_idx_gap
#print axioms Rcic.Syn.vecConsTable_wf
#print axioms Rcic.Syn.vecCons_croot
#print axioms Rcic.Syn.s19_beta9_tgt
#print axioms Rcic.Syn.s19hL_eps_el
#print axioms Rcic.Syn.s19hR_eps_er
#print axioms Rcic.Syn.vecCons_iota_erasure
#print axioms Rcic.Syn.s19_requests_below
#print axioms Rcic.Syn.s19_k1_pair_1
#print axioms Rcic.Syn.s19_k1_pair_2
#print axioms Rcic.Syn.s19_mut_idx_rejected
#print axioms Rcic.Syn.s19_mutMajor_subject
#print axioms Rcic.Syn.s19_mut_directRec0
#print axioms Rcic.Syn.s19_mut_nargs4
#print axioms Rcic.Syn.s19_mut_swap
#print axioms Rcic.Syn.s19_aw7_below
#print axioms Rcic.Syn.s19_decl_budget
#print axioms Rcic.Syn.s19hL_wt_val
#print axioms Rcic.Syn.s19hR_wt_val
#print axioms Rcic.Syn.s19Nι_val
#print axioms Rcic.Syn.s19qA_wt_lt
#print axioms Rcic.Syn.s19qMajor_wt_lt
#print axioms Rcic.Syn.s19qRec_wt_lt
#print axioms Rcic.Syn.s19cβ_wt_lt
#print axioms Rcic.Syn.s19cβ_wt_below
#print axioms Rcic.Syn.s19b_qA
#print axioms Rcic.Syn.s19b_qRec
#print axioms Rcic.Syn.s19b_qRecT
#print axioms Rcic.Syn.s19b_cβdl
#print axioms Rcic.Syn.s19b_cβdr
#print axioms Rcic.Syn.s19b_hLreg
#print axioms Rcic.Syn.s19_field2_dom
#print axioms Rcic.Syn.domViewRes_wt
