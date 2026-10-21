import rcic.RcicSynBelow
import rcic.RcicSynES
import rcic.RcicSynPack
import rcic.RcicSynEnrich
import rcic.RcicSynNatSuccIota
import rcic.RcicTypedGroupPinsList

/-!
# S18 — the List-cons retained-result ι instance (`wConsNat`)

`research/rcic/sortrow/S18_LIST_CONS_ES.md` (PR #7395). The fixture is
`listEnvUT` — Nat plus the *raised* `List` group (`raisedFam` at ref 8,
`nil` at 9, `cons` at 10, recursor at 11) — and the redex
`List.rec.{1,1} A M mn mc (cons.{1} A h t)` where `A = Nat`, `M = λ xs:L.
Nat`, `mn = zero`, `mc = λ x. λ xs. λ ih. x`, `h = succ zero`,
`t = nil.{1} Nat`, `L = List.{1} Nat`.

* `wConsNat` is built FIELD-BY-FIELD against `listEnvUT`'s `raisedFam` —
  never a record update of `wConsU` (`wConsU` lives on `listUEnv`'s
  `listUFamMember`, a different environment and a different family
  member; nothing is record-updated across that boundary).
* `s18prefixTy`, `motiveBeta`, and the `mn`/`mc` typings are rebuilt from
  the real declarations — `mn`/`mc` are retyped by the original motive
  β (`M a ≡ Nat`), never `iotaPreserveT`/`TypedRowsWf`/`InScope`.
* `s18hL`/`s18hR` are `enrichHasTyT_of_envWfT listEnvUWfT CtxWfT.nil`-enriched;
  `s18H := CvP.iota … (DerivedIota.of wConsNat) s18hL s18hR s18hL s18hR`;
  `s18Nι := s18H.wt AwList` is kernel-computed, never estimated.
* `listConsRule` is §7's singleton with `TableWF`; `CRoot.ctor` gives the
  match; exactly SEVEN β steps reach the retained result
  `mcε hε tε (recε Aε Mε mnε mcε tε)` — the recursive call is kept, not
  reduced. `s18hL.eps id [] = s18EL`, `s18hR.eps id [] = s18ER`,
  `ES [listConsRule] id [] s18H`.
* §5's request list stores the real slot derivations, each `< s18Nι`.
* §9's mutants (wrong recursive argument; `plain↔directRec`; the dropped
  constructor-side parameter; hd/tl swap; `lsC` vs `ls`) are rejected by
  the exact-RHS / exact-redex checks — the wrong-recursive-argument
  mutant still β-collapses to the same head `hε`, which is WHY the check
  is exact rather than normal-valued.

`closure_claim = 0`; T7 declaration correspondence stays the open wall.
-/

namespace Rcic.Syn

open Rcic.Declarative
open PosList

set_option maxHeartbeats 8000000

/-! ## §1 the fixture — `wConsNat` built fresh against `listEnvUT` -/

/-- `Nat`, the shared parameter (both sides carry a copy). -/
def listConsA : Expr Nat := .const 0 []

/-- `List.{1} Nat` — `raisedFam.{1}` applied to `Nat`. -/
def listConsL : Expr Nat := .app (.const 8 [.succ .zero]) (.const 0 [])

/-- the motive `λ xs : List.{1} Nat. Nat`. -/
def listConsM : Expr Nat := .lam listConsL (.const 0 [])

/-- `nil.{1} Nat` — the `directRec` field. -/
def listConsT : Expr Nat := .app (.const 9 [.succ .zero]) (.const 0 [])

/-- `succ zero` — the `plain` field. -/
def listConsH : Expr Nat := .app (.const 2 []) (.const 1 [])

/-- the recursive-call spine's cons argument `cons.{1} A hd tl` with the
    bound-field shape used inside the minor's declared codomain. -/
def listConsConsApp : Expr Nat :=
  .app (.app (.app (.const 10 [.succ .zero]) (.const 0 [])) (.bvar 2))
    (.bvar 1)

/-- the cons minor `λ x : Nat. λ xs : L. λ ih : M xs. x`. -/
def listConsMc : Expr Nat :=
  .lam (.const 0 [])
    (.lam listConsL (.lam (.app listConsM (.bvar 0)) (.bvar 2)))

/-- `cons.{1} Nat (succ zero) (nil.{1} Nat)` — the major. -/
def listConsCtor : Expr Nat :=
  .app (.app (.app (.const 10 [.succ .zero]) listConsA) listConsH)
    listConsT

/-- the recursive call `rec.{1,1} A M mn mc t`. -/
def listConsRecT : Expr Nat :=
  recCall (.const 11 [.succ .zero, .succ .zero])
    [listConsA, listConsM, .const 1 [], listConsMc] listConsT

/-- the minor's declared domain after `M` is instantiated:
    `Π x : Nat. Π xs : L. Π ih : M xs. M (cons.{1} A x xs)`. -/
def listConsDomMc : Expr Nat :=
  .pi (.const 0 [])
    (.pi listConsL
      (.pi (.app listConsM (.bvar 0)) (.app listConsM listConsConsApp)))

/-- `wConsNat` — the cons-redex witness on `listEnvUT`, every field fresh
    against `raisedFam` (family ref 8, nil 9, cons 10, recursor 11).
    `ls = [1,1]` (recursor arity 2), `lsC = [1]` (constructor/family
    arity 1); `kinds = [.plain, .directRec]`; `ctorParams` and
    `preMajor.take 1` are the two independent `A` copies. -/
def wConsNat : IotaWitness listEnvUT where
  recRef := 11
  ctorRef := 10
  ls := [.succ .zero, .succ .zero]
  lsC := [.succ .zero]
  recMember := listURecMember
  ctorMember := listUConsMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [listConsA, listConsM, .const 1 [], listConsMc]
  fields := [listConsH, listConsT]
  ctorParams := [listConsA]
  kinds := [.plain, .directRec]
  minor := listConsMc
  hlen := rfl
  familyRef := 8
  famMember := raisedFam
  hfam := rfl
  hfamK := rfl
  nparams := 1
  nindices := 0
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
  ctorDoms :=
    [ .sort (.param 0)
    , .bvar 0
    , .app (.const 8 [.param 0]) (.bvar 1) ]
  ctorResult := .app (.const 8 [.param 0]) (.bvar 2)
  hpeel := rfl
  hfamApp := rfl
  hkinds := rfl
  recDoms := listURecDoms
  recBody := .app (.bvar 3) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  ctorAfterParams := .pi (.const 0 []) (.pi listConsL listConsL)
  hctorAfter := rfl
  hctorTel := rfl
  hfamTel := rfl
  hresTel := rfl

/-- `iotaTypingCert` accepts `wConsNat` — the declarative checks (telescope
    arithmetic, `hfamSpineExact` at `ls.take 1 = [1]`, minor-telescope
    shapes) all discharge definitionally. -/
theorem wConsNat_cert : (iotaTypingCert wConsNat).isSome = true := rfl

/-- `iotaLhsOf` is the real redex `rec.{1,1} A M mn mc (cons.{1} A h t)`. -/
theorem wConsNat_lhs :
    iotaLhsOf wConsNat =
      recCall (.const 11 [.succ .zero, .succ .zero])
        [listConsA, listConsM, .const 1 [], listConsMc] listConsCtor := rfl

/-- `iotaRhsOf` is `mc h t (rec.{1,1} A M mn mc t)` — the retained
    recursive result, via `rhsArgs`/`recCallField` at the `directRec`
    field `t`. -/
theorem wConsNat_rhs :
    iotaRhsOf wConsNat =
      .app (.app (.app listConsMc listConsH) listConsT) listConsRecT := rfl

/-! ## §2 the independent native typings (no `iotaPreserveT`/`InScope`) -/

/-- `Nat : Sort 1` in `listEnvUT`. -/
def listConsATy (Γ : LCtx) :
    HasTyT listEnvUT 0 Γ listConsA (.sort (.succ .zero)) :=
  HasTyT.const Γ 0 [] natFamMember rfl rfl rfl

/-- `raisedFam.{1} : Π (α : Sort 1). Sort 2`. -/
def listConsFamTy (Γ : LCtx) : HasTyT listEnvUT 0 Γ (.const 8 [.succ .zero])
    (.pi (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))) :=
  HasTyT.const Γ 8 [.succ .zero] raisedFam rfl rfl rfl

/-- `List.{1} Nat : Sort 2`. -/
def listConsLTy (Γ : LCtx) :
    HasTyT listEnvUT 0 Γ listConsL (.sort (.succ (.succ .zero))) :=
  HasTyT.app Γ (.const 8 [.succ .zero]) (.const 0 []) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) (listConsFamTy Γ)
    (HasTyT.const Γ 0 [] natFamMember rfl rfl rfl)

/-- `M : Π xs : L. Sort 1`. -/
def listConsMTy (Γ : LCtx) :
    HasTyT listEnvUT 0 Γ listConsM
      (.pi listConsL (.sort (.succ .zero))) :=
  HasTyT.lam Γ listConsL (.succ (.succ .zero)) (.const 0 [])
    (.sort (.succ .zero)) (listConsLTy Γ)
    (HasTyT.const _ 0 [] natFamMember rfl rfl rfl)

/-- `nil.{1} : Π (α : Sort 1). List.{1} α`. -/
def listConsNilTy (Γ : LCtx) : HasTyT listEnvUT 0 Γ
    (.const 9 [.succ .zero])
    (.pi (.sort (.succ .zero)) (.app (.const 8 [.succ .zero]) (.bvar 0))) :=
  HasTyT.const Γ 9 [.succ .zero] listUNilMember rfl rfl rfl

/-- `t = nil.{1} Nat : L`. -/
def listConsTTy (Γ : LCtx) :
    HasTyT listEnvUT 0 Γ listConsT listConsL :=
  HasTyT.app Γ (.const 9 [.succ .zero]) (.const 0 []) (.sort (.succ .zero))
    (.app (.const 8 [.succ .zero]) (.bvar 0)) (listConsNilTy Γ)
    (HasTyT.const Γ 0 [] natFamMember rfl rfl rfl)

/-- `zero : Nat`. -/
def listConsZeroTy (Γ : LCtx) :
    HasTyT listEnvUT 0 Γ (.const 1 []) (.const 0 []) :=
  HasTyT.const Γ 1 [] natZeroMember rfl rfl rfl

/-- `succ : Nat → Nat`. -/
def listConsSuccTy (Γ : LCtx) : HasTyT listEnvUT 0 Γ (.const 2 [])
    (.pi (.const 0 []) (.const 0 [])) :=
  HasTyT.const Γ 2 [] natSuccMember rfl rfl rfl

/-- `h = succ zero : Nat`. -/
def listConsHTy (Γ : LCtx) :
    HasTyT listEnvUT 0 Γ listConsH (.const 0 []) :=
  HasTyT.app Γ (.const 2 []) (.const 1 []) (.const 0 []) (.const 0 [])
    (listConsSuccTy Γ) (listConsZeroTy Γ)

/-- `cons.{1} : Π (α : Sort 1). α → List.{1} α → List.{1} α`. -/
def listConsConsTy (Γ : LCtx) : HasTyT listEnvUT 0 Γ
    (.const 10 [.succ .zero])
    (.pi (.sort (.succ .zero))
      (.pi (.bvar 0)
        (.pi (.app (.const 8 [.succ .zero]) (.bvar 1))
          (.app (.const 8 [.succ .zero]) (.bvar 2))))) :=
  HasTyT.const Γ 10 [.succ .zero] listUConsMember rfl rfl rfl

/-- the major `cons.{1} Nat h t : L`. -/
def listConsCtorTy (Γ : LCtx) :
    HasTyT listEnvUT 0 Γ listConsCtor listConsL :=
  have h1 : HasTyT listEnvUT 0 Γ (.app (.const 10 [.succ .zero]) listConsA)
      (.pi (.const 0 []) (.pi listConsL listConsL)) :=
    HasTyT.app Γ (.const 10 [.succ .zero]) listConsA (.sort (.succ .zero))
      (.pi (.bvar 0)
        (.pi (.app (.const 8 [.succ .zero]) (.bvar 1))
          (.app (.const 8 [.succ .zero]) (.bvar 2))))
      (listConsConsTy Γ) (listConsATy Γ)
  have h2 : HasTyT listEnvUT 0 Γ
      (.app (.app (.const 10 [.succ .zero]) listConsA) listConsH)
      (.pi listConsL listConsL) :=
    HasTyT.app Γ _ listConsH (.const 0 []) (.pi listConsL listConsL) h1
      (listConsHTy Γ)
  HasTyT.app Γ _ listConsT listConsL listConsL h2 (listConsTTy Γ)

/-- the original motive β `M a ≡ Nat` at `Sort 1` — `ConvT.beta` on the
    real motive body, for any `a : L` in any context. -/
def motiveBeta (Γ : LCtx) (a : Expr Nat)
    (ha : HasTyT listEnvUT 0 Γ a listConsL) :
    ConvT listEnvUT 0 Γ (.app listConsM a) (.const 0 [])
      (.sort (.succ .zero)) :=
  ConvT.beta Γ listConsL (.const 0 []) a (.sort (.succ .zero))
    (.succ (.succ .zero)) (listConsLTy Γ)
    (HasTyT.const _ 0 [] natFamMember rfl rfl rfl) ha

/-- `mn = zero : M t` — `zero`'s Nat typing retyped by the original β
    (the `ConvT.symm` direction, matching `ConvT`'s `A ≡ B` use in
    `HasTyT.conv`). -/
noncomputable def listConsMnTy :
    HasTyT listEnvUT 0 [] (.const 1 []) (.app listConsM listConsT) :=
  HasTyT.conv [] (.const 1 []) (.const 0 []) (.app listConsM listConsT)
    (.succ .zero) (listConsZeroTy [])
    (ConvT.symm _ _ _ _ (motiveBeta [] listConsT (listConsTTy [])))

/-- the field context `[xs : L, x : Nat]`. -/
def listConsΓ₂ : LCtx := [.assumption listConsL, .assumption (.const 0 [])]

/-- the inner context `[ih : M xs, xs : L, x : Nat]`. -/
def listConsΓ₃ : LCtx :=
  [.assumption (.app listConsM (.bvar 0)), .assumption listConsL,
    .assumption (.const 0 [])]

/-- `M` weakened into `Γ₂`. -/
def listConsMWk2 : HasTyT listEnvUT 0 listConsΓ₂ listConsM
    (.pi listConsL (.sort (.succ .zero))) :=
  hasTyTWeaken (.assumption listConsL) (envClosed_of_envWfT listEnvUWfT)
    (c := 0)
    (hasTyTWeaken (.assumption (.const 0 []))
      (envClosed_of_envWfT listEnvUWfT) (c := 0) (listConsMTy []))

/-- `M` weakened into `Γ₃`. -/
def listConsMWk3 : HasTyT listEnvUT 0 listConsΓ₃ listConsM
    (.pi listConsL (.sort (.succ .zero))) :=
  hasTyTWeaken (.assumption (.app listConsM (.bvar 0)))
    (envClosed_of_envWfT listEnvUWfT) (c := 0) listConsMWk2

/-- `xs : L` in `Γ₂`. -/
def listConsXsTy : HasTyT listEnvUT 0 listConsΓ₂ (.bvar 0) listConsL :=
  HasTyT.bvar _ 0 listConsL rfl

/-- `xs : L` in `Γ₃`. -/
def listConsXs3 : HasTyT listEnvUT 0 listConsΓ₃ (.bvar 1) listConsL :=
  HasTyT.bvar _ 1 listConsL rfl

/-- `x : Nat` in `Γ₃`. -/
def listConsX3 : HasTyT listEnvUT 0 listConsΓ₃ (.bvar 2) (.const 0 []) :=
  HasTyT.bvar _ 2 (.const 0 []) rfl

/-- `ih`-domain `M xs : Sort 1` in `Γ₂`. -/
def listConsMx : HasTyT listEnvUT 0 listConsΓ₂
    (.app listConsM (.bvar 0)) (.sort (.succ .zero)) :=
  HasTyT.app _ listConsM (.bvar 0) listConsL (.sort (.succ .zero))
    listConsMWk2 listConsXsTy

/-- `cons.{1} A x xs : L` in `Γ₃` — `x` at `bvar 2`, `xs` at `bvar 1`. -/
def listConsConsB : HasTyT listEnvUT 0 listConsΓ₃ listConsConsApp
    listConsL :=
  have h1 : HasTyT listEnvUT 0 listConsΓ₃
      (.app (.const 10 [.succ .zero]) (.const 0 []))
      (.pi (.const 0 []) (.pi listConsL listConsL)) :=
    HasTyT.app _ (.const 10 [.succ .zero]) (.const 0 [])
      (.sort (.succ .zero))
      (.pi (.bvar 0)
        (.pi (.app (.const 8 [.succ .zero]) (.bvar 1))
          (.app (.const 8 [.succ .zero]) (.bvar 2))))
      (listConsConsTy _) (listConsATy _)
  have h2 : HasTyT listEnvUT 0 listConsΓ₃
      (.app (.app (.const 10 [.succ .zero]) (.const 0 [])) (.bvar 2))
      (.pi listConsL listConsL) :=
    HasTyT.app _ _ (.bvar 2) (.const 0 []) (.pi listConsL listConsL) h1
      listConsX3
  HasTyT.app _ _ (.bvar 1) listConsL listConsL h2 listConsXs3

/-- the minor body `x : M (cons.{1} A x xs)` — `x`'s Nat typing retyped by
    the original β at the bound `cons` spine. -/
def listConsMcBody : HasTyT listEnvUT 0 listConsΓ₃ (.bvar 2)
    (.app listConsM listConsConsApp) :=
  HasTyT.conv _ (.bvar 2) (.const 0 []) (.app listConsM listConsConsApp)
    (.succ .zero) listConsX3
    (ConvT.symm _ _ _ _ (motiveBeta _ listConsConsApp listConsConsB))

/-- `mc : listConsDomMc` — the three-λ chain over the real motive domains;
    the `ih` binder is `M xs` and the codomain `M (cons A x xs)` is
    discharged by `listConsMcBody`'s β, not by a declared-domain copy. -/
noncomputable def listConsMcTy :
    HasTyT listEnvUT 0 [] listConsMc listConsDomMc :=
  have hInner : HasTyT listEnvUT 0 listConsΓ₂
      (.lam (.app listConsM (.bvar 0)) (.bvar 2))
      (.pi (.app listConsM (.bvar 0)) (.app listConsM listConsConsApp)) :=
    HasTyT.lam _ (.app listConsM (.bvar 0)) (.succ .zero) (.bvar 2)
      (.app listConsM listConsConsApp) listConsMx listConsMcBody
  have hMid : HasTyT listEnvUT 0 [.assumption (.const 0 [])]
      (.lam listConsL (.lam (.app listConsM (.bvar 0)) (.bvar 2)))
      (.pi listConsL
        (.pi (.app listConsM (.bvar 0)) (.app listConsM listConsConsApp))) :=
    HasTyT.lam _ listConsL (.succ (.succ .zero))
      (.lam (.app listConsM (.bvar 0)) (.bvar 2))
      (.pi (.app listConsM (.bvar 0)) (.app listConsM listConsConsApp))
      (listConsLTy _) hInner
  HasTyT.lam [] (.const 0 []) (.succ .zero)
    (.lam listConsL (.lam (.app listConsM (.bvar 0)) (.bvar 2)))
    (.pi listConsL
      (.pi (.app listConsM (.bvar 0)) (.app listConsM listConsConsApp)))
    (listConsATy _) hMid

/-- `s18prefixTy`: `rec.{1,1} A M mn mc : Π xs : L. M xs` — the `h0–h4`
    spine against `listURecType` instantiated at `[1,1]`. The motive's
    declared domain `Π xs : L. Sort 1` and the `directRec` field `t`'s
    recursive call both follow the raw `listURecDoms` shape. -/
noncomputable def s18prefixTy : HasTyT listEnvUT 0 []
    (foldApps (.const 11 [.succ .zero, .succ .zero])
      [listConsA, listConsM, .const 1 [], listConsMc])
    (.pi listConsL (.app listConsM (.bvar 0))) :=
  have h0 : HasTyT listEnvUT 0 []
      (.const 11 [.succ .zero, .succ .zero]) _ :=
    HasTyT.const [] 11 [.succ .zero, .succ .zero] listURecMember rfl rfl rfl
  have h1 : HasTyT listEnvUT 0 []
      (.app (.const 11 [.succ .zero, .succ .zero]) listConsA)
      (.pi (.pi listConsL (.sort (.succ .zero)))
        (.pi (.app (.bvar 0) listConsT)
          (.pi (.pi (.const 0 [])
              (.pi listConsL
                (.pi (.app (.bvar 3) (.bvar 0))
                  (.app (.bvar 4)
                    (.app (.app (.app (.const 10 [.succ .zero])
                        (.const 0 [])) (.bvar 2)) (.bvar 1))))))
            (.pi listConsL (.app (.bvar 3) (.bvar 0)))))) :=
    HasTyT.app [] _ _ _ _ h0 (listConsATy [])
  have h2 : HasTyT listEnvUT 0 []
      (.app (.app (.const 11 [.succ .zero, .succ .zero]) listConsA)
        listConsM)
      (.pi (.app listConsM listConsT)
        (.pi listConsDomMc (.pi listConsL (.app listConsM (.bvar 0))))) :=
    HasTyT.app [] _ _ _ _ h1 (listConsMTy [])
  have h3 : HasTyT listEnvUT 0 []
      (foldApps (.const 11 [.succ .zero, .succ .zero])
        [listConsA, listConsM, .const 1 []])
      (.pi listConsDomMc (.pi listConsL (.app listConsM (.bvar 0)))) :=
    HasTyT.app [] _ _ _ _ h2 listConsMnTy
  HasTyT.app [] _ _ _ _ h3 listConsMcTy

/-- `hL₀`: the lhs at its motive-viewed type `M (cons A h t)`. -/
noncomputable def hL0 : HasTyT listEnvUT 0 [] (iotaLhsOf wConsNat)
    (.app listConsM listConsCtor) :=
  HasTyT.app [] _ _ _ _ s18prefixTy (listConsCtorTy [])

/-- `hLᵀ`: the lhs retyped to `Nat` along the original β. -/
noncomputable def s18hLT :
    HasTyT listEnvUT 0 [] (iotaLhsOf wConsNat) (.const 0 []) :=
  HasTyT.conv [] _ (.app listConsM listConsCtor) (.const 0 [])
    (.succ .zero) hL0
    (motiveBeta [] listConsCtor (listConsCtorTy []))

/-- `hRecT`: the recursive call `rec A M mn mc t : M t` — the
    `directRec`-field spine off the same `s18prefixTy`. -/
noncomputable def hRecT : HasTyT listEnvUT 0 [] listConsRecT
    (.app listConsM listConsT) :=
  HasTyT.app [] _ _ _ _ s18prefixTy (listConsTTy [])

/-- `hR₀`: the rhs at its motive-viewed type `M (cons A h t)`, built
    independently through `listConsMcTy`'s own λ-chain. -/
noncomputable def hR0 : HasTyT listEnvUT 0 [] (iotaRhsOf wConsNat)
    (.app listConsM listConsCtor) :=
  have h1 : HasTyT listEnvUT 0 [] (.app listConsMc listConsH)
      (.pi listConsL
        (.pi (.app listConsM (.bvar 0))
          (.app listConsM
            (.app (.app (.app (.const 10 [.succ .zero]) (.const 0 []))
              listConsH) (.bvar 1))))) :=
    HasTyT.app [] _ _ _ _ listConsMcTy (listConsHTy [])
  have h2 : HasTyT listEnvUT 0 []
      (.app (.app listConsMc listConsH) listConsT)
      (.pi (.app listConsM listConsT) (.app listConsM listConsCtor)) :=
    HasTyT.app [] _ _ _ _ h1 (listConsTTy [])
  HasTyT.app [] _ _ _ _ h2 hRecT

/-- `hRᵀ`: the rhs retyped to `Nat` along the original β. -/
noncomputable def s18hRT :
    HasTyT listEnvUT 0 [] (iotaRhsOf wConsNat) (.const 0 []) :=
  HasTyT.conv [] _ (.app listConsM listConsCtor) (.const 0 [])
    (.succ .zero) hR0
    (motiveBeta [] listConsCtor (listConsCtorTy []))

/-! ## §3 the enriched endpoints, `s18H`, `s18Nι` -/

/-- the enriched lhs typing (one of `s18H`'s four occurrences). -/
noncomputable def s18hL :
    TyP listEnvUT 0 [] (iotaLhsOf wConsNat) (.const 0 []) :=
  enrichHasTyT_of_envWfT listEnvUWfT CtxWfT.nil s18hLT

/-- the enriched rhs typing. -/
noncomputable def s18hR :
    TyP listEnvUT 0 [] (iotaRhsOf wConsNat) (.const 0 []) :=
  enrichHasTyT_of_envWfT listEnvUWfT CtxWfT.nil s18hRT

/-- `s18H`: the stored ι node. `hlhs`/`hrhs`/`dl`/`dr` keep the constructor's
    four original occurrences — equal in value, never de-duplicated. -/
noncomputable def s18H : CvP listEnvUT 0 [] (iotaLhsOf wConsNat)
    (iotaRhsOf wConsNat) (.const 0 []) :=
  CvP.iota listEnvUT 0 [] _ _ _ (DerivedIota.of wConsNat) s18hL s18hR s18hL s18hR

/-- the real admission weight of `enrichEnvWfT listEnvUWfT`. -/
noncomputable def AwList : Nat → Nat := (enrichEnvWfT listEnvUWfT).admW

/-- `s18Nι := s18H.wt Aw` — computed by the kernel from the real derivations,
    never estimated. -/
noncomputable def s18Nι : Nat := s18H.wt AwList

/-- §4's shape: `s18Nι = 1 + 2 * s18hL.wt + 2 * s18hR.wt` (four real occurrences). -/
theorem s18Nι_eq : s18Nι = 1 + 2 * s18hL.wt AwList + 2 * s18hR.wt AwList := by
  have hw : s18H.wt AwList =
      1 + s18hL.wt AwList + s18hR.wt AwList + s18hL.wt AwList + s18hR.wt AwList := rfl
  rw [s18Nι, hw]; omega

/-! ## §4–§5 the request list — real slots, each `< s18Nι` -/

/-- §5's enriched slot typings — the nine request positions of §5
    (recursor-side `A`, `M`, `mn`, `mc`; the major; the constructor-side
    `A`; `hd`; `tl`; the recursive call), each an independent enrichment
    of its own native producer. -/
noncomputable def qA : TyP listEnvUT 0 [] listConsA (.sort (.succ .zero)) :=
  enrichHasTyT_of_envWfT listEnvUWfT CtxWfT.nil (listConsATy [])

noncomputable def qM : TyP listEnvUT 0 [] listConsM
    (.pi listConsL (.sort (.succ .zero))) :=
  enrichHasTyT_of_envWfT listEnvUWfT CtxWfT.nil (listConsMTy [])

noncomputable def qMn : TyP listEnvUT 0 [] (.const 1 [])
    (.app listConsM listConsT) :=
  enrichHasTyT_of_envWfT listEnvUWfT CtxWfT.nil listConsMnTy

noncomputable def qMc : TyP listEnvUT 0 [] listConsMc listConsDomMc :=
  enrichHasTyT_of_envWfT listEnvUWfT CtxWfT.nil listConsMcTy

noncomputable def qMajor : TyP listEnvUT 0 [] listConsCtor listConsL :=
  enrichHasTyT_of_envWfT listEnvUWfT CtxWfT.nil (listConsCtorTy [])

/-- the constructor-side `A` — an INDEPENDENT occurrence of the same
    `Nat`, matching `ctorParams`'s own copy. -/
noncomputable def qACtor : TyP listEnvUT 0 [] listConsA
    (.sort (.succ .zero)) :=
  enrichHasTyT_of_envWfT listEnvUWfT CtxWfT.nil
    (HasTyT.const [] 0 [] natFamMember rfl rfl rfl)

noncomputable def qH : TyP listEnvUT 0 [] listConsH (.const 0 []) :=
  enrichHasTyT_of_envWfT listEnvUWfT CtxWfT.nil (listConsHTy [])

noncomputable def qT : TyP listEnvUT 0 [] listConsT listConsL :=
  enrichHasTyT_of_envWfT listEnvUWfT CtxWfT.nil (listConsTTy [])

noncomputable def qRecT : TyP listEnvUT 0 [] listConsRecT
    (.app listConsM listConsT) :=
  enrichHasTyT_of_envWfT listEnvUWfT CtxWfT.nil hRecT

/-! ## §5's domain views — the admission telescope's OWN fields, lazily
    instantiated (S18 §5/§10)

`listRecTypeTyT` is the recursor's OWN admission: it types the
`listURecType` telescope inside `listPrefixU` at two level parameters;
`listConsTyT` types `listUConsType` inside `listFamNilU` at one. Each
`pD` below takes the real domain field of that SAME admission telescope
(`s18RecTele_eq`/`s18CtorTele_eq` are the verbatim decompositions),
transports it forward along the fresh members' `EnvExt` (`hasTyTExt`),
enriches it under `listEnvUWfT`, level-instantiates it at `σ`/`σC`
(`TyP.linst`), and lazily substitutes the preceding real arguments at
descending index (`TyP.esub` — each `hv` is the slot's own argument
derivation, each `hvT` that argument's `TyP.reg.2`; the `wk` lifts place
them in the remaining context). No new typed Π chain (§10). -/

/-- the recursor telescope's field decomposition — `listURecDoms`' five
    domain fields, literally `listURecType`'s binder domains; the result
    field `M t` is `bvar 3 = M`, `bvar 0 = t`. -/
theorem s18RecTele_eq : listURecDoms =
    [ .sort (.param 0), listMotTy 0,
      .app (.bvar 0) (.app (.const 9 [.param 0]) (.bvar 1)),
      .pi (.bvar 2) (.pi (.app (.const 8 [.param 0]) (.bvar 3))
        (.pi (.app (.bvar 3) (.bvar 0))
          (.app (.bvar 4)
            (.app (.app (.app (.const 10 [.param 0]) (.bvar 5)) (.bvar 2))
              (.bvar 1))))),
      .app (.const 8 [.param 0]) (.bvar 3) ] := rfl

/-- the constructor telescope's field decomposition — `listUConsType`'s
    three binder domains and its `L A` result field. -/
theorem s18CtorTele_eq : listUConsType =
    .pi (.sort (.param 0))
      (.pi (.bvar 0)
        (.pi (.app (.const 8 [.param 0]) (.bvar 1))
          (.app (.const 8 [.param 0]) (.bvar 2)))) := rfl

/-- `listPrefixU → listEnvUT`: the recursor member's forward extension —
    the recursor-side `hasTyTExt` premise. -/
theorem listPrefToU : EnvExt listPrefixU listEnvUT :=
  envExt_extendEnv (r := 11) listURecMember rfl

/-- `listFamNilU → listEnvUT`: the two fresh members' forward extension —
    the constructor-side `hasTyTExt` premise. -/
theorem listNilToU : EnvExt listFamNilU listEnvUT :=
  envExt_trans (envExt_extendEnv (r := 10) listUConsMember rfl) listPrefToU

/-- the telescope's stored `mn`-domain `M (nil A)` — `listURecDoms[2]`,
    in its own relative coordinates (`bvar 0 = M`, `bvar 1 = A`). -/
abbrev s18dMnT : Expr Nat := .app (.bvar 0) (.app (.const 9 [.param 0]) (.bvar 1))

/-- the telescope's stored `mc`-domain — `listURecDoms[3]` —
    `Π x : A. Π xs : L A. Π ih : M xs. M (cons A x xs)` in relative
    coordinates (`x : bvar 2`, `xs : L (bvar 3)`, `ih : (bvar 3) (bvar 0)`,
    result `(bvar 4) (cons (bvar 5) (bvar 2) (bvar 1))`). -/
abbrev s18dMcT : Expr Nat :=
  .pi (.bvar 2) (.pi (.app (.const 8 [.param 0]) (.bvar 3))
    (.pi (.app (.bvar 3) (.bvar 0))
      (.app (.bvar 4)
        (.app (.app (.app (.const 10 [.param 0]) (.bvar 5)) (.bvar 2))
          (.bvar 1)))))

/-- `Sort 1` — `A`'s domain at `σ = [1,1]`/`σC = [1]`. -/
abbrev s18tSort1 : Expr Nat := .sort (.succ .zero)

/-- `M`'s domain at `σ`: `Π xs : L.{1} (bvar 0). Sort 1` — `A` still a
    binder (the pre-`esub` `linst` image of `listMotTy 0`). -/
abbrev s18dM0 : Expr Nat :=
  .pi (.app (.const 8 [.succ .zero]) (.bvar 0)) (.sort (.succ .zero))

/-- `M`'s domain after `A := Nat`: `Π xs : L.{1} Nat. Sort 1`. -/
abbrev s18dM : Expr Nat := .pi listConsL (.sort (.succ .zero))

/-- `mn`'s domain at `σ`: `M (nil.{1} A)` — `bvar 0 = M`, `bvar 1 = A`. -/
abbrev s18dMn01 : Expr Nat :=
  .app (.bvar 0) (.app (.const 9 [.succ .zero]) (.bvar 1))

/-- `mn`'s domain after `A := Nat`: `M (nil.{1} Nat)` — `M` still bound. -/
abbrev s18dMnA : Expr Nat := .app (.bvar 0) listConsT

/-- `mn`'s domain after `A := Nat`, `M := listConsM` — `M t`, the same
    type `qMn`'s argument carries. -/
abbrev s18dMnF : Expr Nat := .app listConsM listConsT

/-- `mc`'s domain at `σ` — the three-layer minor telescope, all three
    binder references live. -/
abbrev s18dMc012 : Expr Nat :=
  .pi (.bvar 2) (.pi (.app (.const 8 [.succ .zero]) (.bvar 3))
    (.pi (.app (.bvar 3) (.bvar 0))
      (.app (.bvar 4)
        (.app (.app (.app (.const 10 [.succ .zero]) (.bvar 5)) (.bvar 2))
          (.bvar 1)))))

/-- `mc`'s domain after `A := Nat` — `Π x : Nat. Π xs : L.{1} Nat. Π ih :
    M xs. M (cons.{1} Nat x xs)` with `M` still a binder. -/
abbrev s18dMcA : Expr Nat :=
  .pi (.const 0 []) (.pi listConsL
    (.pi (.app (.bvar 3) (.bvar 0))
      (.app (.bvar 4)
        (.app (.app (.app (.const 10 [.succ .zero]) (.const 0 []))
          (.bvar 2)) (.bvar 1)))))

/-- `t`'s domain at `σ`: `L.{1} (bvar 3)` — `A` at `bvar 3`. -/
abbrev s18dT3 : Expr Nat := .app (.const 8 [.succ .zero]) (.bvar 3)

/-- d0 — `A`'s domain `Sort (param 0)`, `listRecTypeTyT`'s first leaf,
    verbatim. -/
noncomputable def s18Dom0T : HasTyT listPrefixU 2 [] (.sort (.param 0))
    (.sort (.succ (.param 0))) :=
  .sort [] (.param 0)

/-- d1 — `M`'s domain `Π xs : L A. Sort v`, the admission's second `.pi`
    node verbatim (the same `listOfTyT`/`sort` leaves). -/
noncomputable def s18Dom1T : HasTyT listPrefixU 2
    [.assumption (.sort (.param 0))] (listMotTy 0)
    (.sort (.imax (.succ (.param 0)) (.succ (.param 1)))) :=
  .pi _ _ _ _ _ (listOfTyT (n := 2) rfl rfl (.bvar _ 0 _ rfl)) (.sort _ (.param 1))

/-- d2 — `mn`'s domain `M (nil A)` — the admission's `.app` node verbatim
    (`bvar 0 = M`, `nil (bvar 1) = nil A`). -/
noncomputable def s18Dom2T : HasTyT listPrefixU 2
    [.assumption (listMotTy 0), .assumption (.sort (.param 0))]
    (.app (.bvar 0) (.app (.const 9 [.param 0]) (.bvar 1)))
    (.sort (.param 1)) :=
  .app _ (.bvar 0) (.app (.const 9 [.param 0]) (.bvar 1))
    (.app (.const 8 [.param 0]) (.bvar 1)) (.sort (.param 1))
    (.bvar _ 0 (listMotTy 1) rfl)
    (.app _ (.const 9 [.param 0]) (.bvar 1) (.sort (.param 0))
      (.app (.const 8 [.param 0]) (.bvar 0))
      (.const _ 9 [.param 0] listUNilMember rfl rfl rfl)
      (.bvar _ 1 _ rfl))

/-- d3 — `mc`'s domain `Π x : A. Π xs : L A. Π ih : M xs. M (cons A x
    xs)` — the admission's three-`.pi` block verbatim (`x : bvar 2`,
    `xs : L (bvar 3)`, `ih : (bvar 3) (bvar 0)`, result `(bvar 4)
    (cons (bvar 5) (bvar 2) (bvar 1))`). -/
noncomputable def s18Dom3T : HasTyT listPrefixU 2
    [.assumption (.app (.bvar 0) (.app (.const 9 [.param 0]) (.bvar 1))),
     .assumption (listMotTy 0), .assumption (.sort (.param 0))]
    (.pi (.bvar 2)
      (.pi (.app (.const 8 [.param 0]) (.bvar 3))
        (.pi (.app (.bvar 3) (.bvar 0))
          (.app (.bvar 4)
            (.app (.app (.app (.const 10 [.param 0]) (.bvar 5)) (.bvar 2))
              (.bvar 1))))))
    (.sort (.imax (.param 0)
      (.imax (.succ (.param 0)) (.imax (.param 1) (.param 1))))) :=
  .pi _ _ _ _ _ (.bvar _ 2 _ rfl)
    (.pi _ _ _ _ _ (listOfTyT (n := 2) rfl rfl (.bvar _ 3 _ rfl))
      (.pi _ _ _ _ _
        (.app _ (.bvar 3) (.bvar 0) (.app (.const 8 [.param 0]) (.bvar 4))
          (.sort (.param 1)) (.bvar _ 3 (listMotTy 4) rfl)
          (.bvar _ 0 _ rfl))
        (.app _ (.bvar 4)
          (.app (.app (.app (.const 10 [.param 0]) (.bvar 5)) (.bvar 2))
            (.bvar 1))
          (.app (.const 8 [.param 0]) (.bvar 5)) (.sort (.param 1))
          (.bvar _ 4 (listMotTy 5) rfl)
          (.app _ (.app (.app (.const 10 [.param 0]) (.bvar 5)) (.bvar 2))
            (.bvar 1) (.app (.const 8 [.param 0]) (.bvar 5))
            (.app (.const 8 [.param 0]) (.bvar 6))
            (.app _ (.app (.const 10 [.param 0]) (.bvar 5)) (.bvar 2)
              (.bvar 5)
              (.pi (.app (.const 8 [.param 0]) (.bvar 6))
                (.app (.const 8 [.param 0]) (.bvar 7)))
              (.app _ (.const 10 [.param 0]) (.bvar 5) (.sort (.param 0))
                (.pi (.bvar 0)
                  (.pi (.app (.const 8 [.param 0]) (.bvar 1))
                    (.app (.const 8 [.param 0]) (.bvar 2))))
                (.const _ 10 [.param 0] listUConsMember rfl rfl rfl)
                (.bvar _ 5 _ rfl))
              (.bvar _ 2 _ rfl))
            (.bvar _ 1 _ rfl)))))

/-- d4 — the major's domain `L A`, the admission's `listOfTyT` leaf at
    `bvar 3 = A`, verbatim. -/
noncomputable def s18Dom4T : HasTyT listPrefixU 2
    [.assumption s18dMcT, .assumption s18dMnT,
     .assumption (listMotTy 0), .assumption (.sort (.param 0))]
    (.app (.const 8 [.param 0]) (.bvar 3)) (.sort (.succ (.param 0))) :=
  listOfTyT (n := 2) rfl rfl (.bvar _ 3 _ rfl)

/-- the result field `M t` — the admission's `.app` leaf verbatim
    (`bvar 3 = M`, `bvar 0 = t`). -/
noncomputable def s18BodyT : HasTyT listPrefixU 2
    [.assumption (.app (.const 8 [.param 0]) (.bvar 3)),
     .assumption s18dMcT, .assumption s18dMnT,
     .assumption (listMotTy 0), .assumption (.sort (.param 0))]
    (.app (.bvar 3) (.bvar 0)) (.sort (.param 1)) :=
  .app _ (.bvar 3) (.bvar 0) (.app (.const 8 [.param 0]) (.bvar 4))
    (.sort (.param 1)) (.bvar _ 3 (listMotTy 4) rfl) (.bvar _ 0 _ rfl)

/-- ctor d0 — `A`'s domain `Sort (param 0)`, `listConsTyT`'s first leaf
    in the constructor's own admission scope `listFamNilU`. -/
noncomputable def s18CDom0T : HasTyT listFamNilU 1 [] (.sort (.param 0))
    (.sort (.succ (.param 0))) :=
  .sort [] (.param 0)

/-- ctor d1 — `hd`'s domain `bvar 0` (the `A` binder itself), the
    constructor admission's `.bvar` leaf verbatim. -/
noncomputable def s18CDom1T : HasTyT listFamNilU 1
    [.assumption (.sort (.param 0))] (.bvar 0) (.sort (.param 0)) :=
  .bvar _ 0 _ rfl

/-- ctor d2 — `tl`'s domain `L.{u} A`, the constructor admission's
    `listOfTyT` leaf verbatim. -/
noncomputable def s18CDom2T : HasTyT listFamNilU 1
    [.assumption (.bvar 0), .assumption (.sort (.param 0))]
    (.app (.const 8 [.param 0]) (.bvar 1)) (.sort (.succ (.param 0))) :=
  listOfTyT (n := 1) rfl rfl (.bvar _ 1 _ rfl)

/-- the domain fields transported to `listEnvUT` along `listPrefToU`
    (recursor side) and `listNilToU` (constructor side). -/
noncomputable def s18Dom0U : HasTyT listEnvUT 2 [] (.sort (.param 0))
    (.sort (.succ (.param 0))) :=
  hasTyTExt listPrefToU s18Dom0T
noncomputable def s18Dom1U : HasTyT listEnvUT 2
    [.assumption (.sort (.param 0))] (listMotTy 0)
    (.sort (.imax (.succ (.param 0)) (.succ (.param 1)))) :=
  hasTyTExt listPrefToU s18Dom1T
noncomputable def s18Dom2U : HasTyT listEnvUT 2
    [.assumption (listMotTy 0), .assumption (.sort (.param 0))]
    (.app (.bvar 0) (.app (.const 9 [.param 0]) (.bvar 1)))
    (.sort (.param 1)) :=
  hasTyTExt listPrefToU s18Dom2T
noncomputable def s18Dom3U : HasTyT listEnvUT 2
    [.assumption (.app (.bvar 0) (.app (.const 9 [.param 0]) (.bvar 1))),
     .assumption (listMotTy 0), .assumption (.sort (.param 0))]
    s18dMcT
    (.sort (.imax (.param 0)
      (.imax (.succ (.param 0)) (.imax (.param 1) (.param 1))))) :=
  hasTyTExt listPrefToU s18Dom3T
noncomputable def s18Dom4U : HasTyT listEnvUT 2
    [.assumption s18dMcT, .assumption s18dMnT,
     .assumption (listMotTy 0), .assumption (.sort (.param 0))]
    (.app (.const 8 [.param 0]) (.bvar 3)) (.sort (.succ (.param 0))) :=
  hasTyTExt listPrefToU s18Dom4T
noncomputable def s18BodyU : HasTyT listEnvUT 2
    [.assumption (.app (.const 8 [.param 0]) (.bvar 3)),
     .assumption s18dMcT, .assumption s18dMnT,
     .assumption (listMotTy 0), .assumption (.sort (.param 0))]
    (.app (.bvar 3) (.bvar 0)) (.sort (.param 1)) :=
  hasTyTExt listPrefToU s18BodyT
noncomputable def s18CDom0U : HasTyT listEnvUT 1 [] (.sort (.param 0))
    (.sort (.succ (.param 0))) :=
  hasTyTExt listNilToU s18CDom0T
noncomputable def s18CDom1U : HasTyT listEnvUT 1
    [.assumption (.sort (.param 0))] (.bvar 0) (.sort (.param 0)) :=
  hasTyTExt listNilToU s18CDom1T
noncomputable def s18CDom2U : HasTyT listEnvUT 1
    [.assumption (.bvar 0), .assumption (.sort (.param 0))]
    (.app (.const 8 [.param 0]) (.bvar 1)) (.sort (.succ (.param 0))) :=
  hasTyTExt listNilToU s18CDom2T

/-- the telescope contexts as `CtxWfT`s — the `esub` domains live in
    them, each entry justified by the preceding field derivation. -/
noncomputable def s18CtxM : CtxWfT listEnvUT 2
    [.assumption (.sort (.param 0))] :=
  .assumption _ _ _ .nil s18Dom0U
noncomputable def s18CtxMn : CtxWfT listEnvUT 2
    [.assumption (listMotTy 0), .assumption (.sort (.param 0))] :=
  .assumption _ _ _ s18CtxM s18Dom1U
noncomputable def s18CtxMc : CtxWfT listEnvUT 2
    [.assumption (.app (.bvar 0) (.app (.const 9 [.param 0]) (.bvar 1))),
     .assumption (listMotTy 0), .assumption (.sort (.param 0))] :=
  .assumption _ _ _ s18CtxMn s18Dom2U
noncomputable def s18CtxT : CtxWfT listEnvUT 2
    [.assumption s18dMcT, .assumption s18dMnT,
     .assumption (listMotTy 0), .assumption (.sort (.param 0))] :=
  .assumption _ _ _ s18CtxMc s18Dom3U
noncomputable def s18CtxRes : CtxWfT listEnvUT 2
    [.assumption (.app (.const 8 [.param 0]) (.bvar 3)),
     .assumption s18dMcT, .assumption s18dMnT,
     .assumption (listMotTy 0), .assumption (.sort (.param 0))] :=
  .assumption _ _ _ s18CtxT s18Dom4U
noncomputable def s18CtxHd : CtxWfT listEnvUT 1
    [.assumption (.sort (.param 0))] :=
  .assumption _ _ _ .nil s18CDom0U
noncomputable def s18CtxTl : CtxWfT listEnvUT 1
    [.assumption (.bvar 0), .assumption (.sort (.param 0))] :=
  .assumption _ _ _ s18CtxHd s18CDom1U

/-- §5 slot `A` — the recursor's parameter domain `Sort (param 0)`,
    enriched and level-instantiated at `σ` (no preceding arguments). -/
noncomputable def pDSort1 : TyP listEnvUT 0 [] s18tSort1
    (.sort (.succ (.succ .zero))) :=
  .linst listEnvUT 2 0 _ _ _ [.succ .zero, .succ .zero] rfl rfl
    (enrichHasTyT_of_envWfT listEnvUWfT .nil s18Dom0U)

/-- §5 slot `M` — `listMotTy 0` at `σ`, then `A := Nat` by the real
    `qA`/`qA.reg.2`. -/
noncomputable def pDMotive : TyP listEnvUT 0 [] s18dM
    (.sort (.imax (.succ (.succ .zero)) (.succ (.succ .zero)))) :=
  .esub listEnvUT 0 _ _ _ s18tSort1 listConsA 0 _
    (.linst listEnvUT 2 0 _ _ _ [.succ .zero, .succ .zero] rfl rfl
      (enrichHasTyT_of_envWfT listEnvUWfT s18CtxM s18Dom1U))
    rfl qA qA.reg.2

/-- §5 slot `mn` — `M (nil A)` after `A := Nat` then `M := listConsM`:
    the lazy pair `qA`/`qM` and their regularities. -/
noncomputable def pDMt : TyP listEnvUT 0 [] s18dMnF (.sort (.succ .zero)) :=
  .esub listEnvUT 0 _ _ _ s18dM listConsM 0 _
    (.esub listEnvUT 0 _ _ _ s18tSort1 listConsA 1 _
      (.linst listEnvUT 2 0 _ _ _ [.succ .zero, .succ .zero] rfl rfl
        (enrichHasTyT_of_envWfT listEnvUWfT s18CtxMn s18Dom2U))
      rfl
      (.wk listEnvUT 0 _ _ _ (.assumption s18dM) 0 qA)
      (.wk listEnvUT 0 _ _ _ (.assumption s18dM) 0 qA.reg.2))
    rfl qM qM.reg.2

/-- §5 slot `mc` — the three-layer minor telescope after `A`, `M`,
    `mn` — the dead `mn` binder still consumed. -/
noncomputable def pDMc : TyP listEnvUT 0 [] listConsDomMc
    (.sort (.imax (.succ .zero)
      (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero))))) :=
  .esub listEnvUT 0 _ _ _ s18dMnF (.const 1 []) 0 _
    (.esub listEnvUT 0 _ _ _ s18dM listConsM 1 _
      (.esub listEnvUT 0 _ _ _ s18tSort1 listConsA 2 _
        (.linst listEnvUT 2 0 _ _ _ [.succ .zero, .succ .zero] rfl rfl
          (enrichHasTyT_of_envWfT listEnvUWfT s18CtxMc s18Dom3U))
        rfl
        (.wk listEnvUT 0 _ _ _ (.assumption s18dMnA) 0
          (.wk listEnvUT 0 _ _ _ (.assumption s18dM) 0 qA))
        (.wk listEnvUT 0 _ _ _ (.assumption s18dMnA) 0
          (.wk listEnvUT 0 _ _ _ (.assumption s18dM) 0 qA.reg.2)))
      rfl
      (.wk listEnvUT 0 _ _ _ (.assumption s18dMnF) 0 qM)
      (.wk listEnvUT 0 _ _ _ (.assumption s18dMnF) 0 qM.reg.2))
    rfl qMn qMn.reg.2

/-- §5 slot `major` — `L A` after all four real prefix arguments. -/
noncomputable def pDL : TyP listEnvUT 0 [] listConsL
    (.sort (.succ (.succ .zero))) :=
  .esub listEnvUT 0 _ _ _ listConsDomMc listConsMc 0 _
    (.esub listEnvUT 0 _ _ _ s18dMnF (.const 1 []) 1 _
      (.esub listEnvUT 0 _ _ _ s18dM listConsM 2 _
        (.esub listEnvUT 0 _ _ _ s18tSort1 listConsA 3 _
          (.linst listEnvUT 2 0 _ _ _ [.succ .zero, .succ .zero] rfl rfl
            (enrichHasTyT_of_envWfT listEnvUWfT s18CtxT s18Dom4U))
          rfl
          (.wk listEnvUT 0 _ _ _ (.assumption s18dMcA) 0
            (.wk listEnvUT 0 _ _ _ (.assumption s18dMnA) 0
              (.wk listEnvUT 0 _ _ _ (.assumption s18dM) 0 qA)))
          (.wk listEnvUT 0 _ _ _ (.assumption s18dMcA) 0
            (.wk listEnvUT 0 _ _ _ (.assumption s18dMnA) 0
              (.wk listEnvUT 0 _ _ _ (.assumption s18dM) 0 qA.reg.2))))
        rfl
        (.wk listEnvUT 0 _ _ _ (.assumption listConsDomMc) 0
          (.wk listEnvUT 0 _ _ _ (.assumption s18dMnF) 0 qM))
        (.wk listEnvUT 0 _ _ _ (.assumption listConsDomMc) 0
          (.wk listEnvUT 0 _ _ _ (.assumption s18dMnF) 0 qM.reg.2)))
      rfl
      (.wk listEnvUT 0 _ _ _ (.assumption listConsDomMc) 0 qMn)
      (.wk listEnvUT 0 _ _ _ (.assumption listConsDomMc) 0 qMn.reg.2))
    rfl qMc qMc.reg.2

/-- §5 slot `A_ctor` — the constructor's own parameter domain `Sort
    (param 0)`, admitted at `listFamNilU`, enriched and instantiated at
    `σC` (no preceding constructor-side arguments). -/
noncomputable def pDSort1C : TyP listEnvUT 0 [] s18tSort1
    (.sort (.succ (.succ .zero))) :=
  .linst listEnvUT 1 0 _ _ _ [.succ .zero] rfl rfl
    (enrichHasTyT_of_envWfT listEnvUWfT .nil s18CDom0U)

/-- §5 slot `hd` — the constructor's `bvar 0` field after `A := Nat` —
    `qACtor`, the ctor-side independent `A` occurrence. -/
noncomputable def pDNat : TyP listEnvUT 0 [] (.const 0 [])
    (.sort (.succ .zero)) :=
  .esub listEnvUT 0 _ _ _ s18tSort1 listConsA 0 _
    (.linst listEnvUT 1 0 _ _ _ [.succ .zero] rfl rfl
      (enrichHasTyT_of_envWfT listEnvUWfT s18CtxHd s18CDom1U))
    rfl qACtor qACtor.reg.2

/-- §5 slot `tl` — `L A` after `A := Nat`, `hd := succ zero` — the
    `directRec` field's declaration domain. -/
noncomputable def pDL2 : TyP listEnvUT 0 [] listConsL
    (.sort (.succ (.succ .zero))) :=
  .esub listEnvUT 0 _ _ _ (.const 0 []) listConsH 0 _
    (.esub listEnvUT 0 _ _ _ s18tSort1 listConsA 1 _
      (.linst listEnvUT 1 0 _ _ _ [.succ .zero] rfl rfl
        (enrichHasTyT_of_envWfT listEnvUWfT s18CtxTl s18CDom2U))
      rfl
      (.wk listEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0 qACtor)
      (.wk listEnvUT 0 _ _ _ (.assumption (.const 0 [])) 0 qACtor.reg.2))
    rfl qH qH.reg.2

/-- §5 slot `recT` — the result field `M t` after all five real
    arguments: `A`, `M`, `mn`, `mc`, `t` in that order at descending
    index. -/
noncomputable def pDMt2 : TyP listEnvUT 0 [] s18dMnF (.sort (.succ .zero)) :=
  .esub listEnvUT 0 _ _ _ listConsL listConsT 0 _
    (.esub listEnvUT 0 _ _ _ listConsDomMc listConsMc 1 _
      (.esub listEnvUT 0 _ _ _ s18dMnF (.const 1 []) 2 _
        (.esub listEnvUT 0 _ _ _ s18dM listConsM 3 _
          (.esub listEnvUT 0 _ _ _ s18tSort1 listConsA 4 _
            (.linst listEnvUT 2 0 _ _ _ [.succ .zero, .succ .zero] rfl rfl
              (enrichHasTyT_of_envWfT listEnvUWfT s18CtxRes s18BodyU))
            rfl
            (.wk listEnvUT 0 _ _ _ (.assumption listConsL) 0
              (.wk listEnvUT 0 _ _ _ (.assumption s18dMcA) 0
                (.wk listEnvUT 0 _ _ _ (.assumption s18dMnA) 0
                  (.wk listEnvUT 0 _ _ _ (.assumption s18dM) 0 qA))))
            (.wk listEnvUT 0 _ _ _ (.assumption listConsL) 0
              (.wk listEnvUT 0 _ _ _ (.assumption s18dMcA) 0
                (.wk listEnvUT 0 _ _ _ (.assumption s18dMnA) 0
                  (.wk listEnvUT 0 _ _ _ (.assumption s18dM) 0 qA.reg.2)))))
          rfl
          (.wk listEnvUT 0 _ _ _ (.assumption listConsL) 0
            (.wk listEnvUT 0 _ _ _ (.assumption listConsDomMc) 0
              (.wk listEnvUT 0 _ _ _ (.assumption s18dMnF) 0 qM)))
          (.wk listEnvUT 0 _ _ _ (.assumption listConsL) 0
            (.wk listEnvUT 0 _ _ _ (.assumption listConsDomMc) 0
              (.wk listEnvUT 0 _ _ _ (.assumption s18dMnF) 0 qM.reg.2))))
        rfl
        (.wk listEnvUT 0 _ _ _ (.assumption listConsL) 0
          (.wk listEnvUT 0 _ _ _ (.assumption listConsDomMc) 0 qMn))
        (.wk listEnvUT 0 _ _ _ (.assumption listConsL) 0
          (.wk listEnvUT 0 _ _ _ (.assumption listConsDomMc) 0 qMn.reg.2)))
      rfl
      (.wk listEnvUT 0 _ _ _ (.assumption listConsL) 0 qMc)
      (.wk listEnvUT 0 _ _ _ (.assumption listConsL) 0 qMc.reg.2))
    rfl qT qT.reg.2

/-- §5.2's `s18cβ` — the original β `M t ≡ Nat` enriched. -/
noncomputable def s18cβ : CvP listEnvUT 0 [] (.app listConsM listConsT)
    (.const 0 []) (.sort (.succ .zero)) :=
  enrichConvT_of_envWfT listEnvUWfT CtxWfT.nil
    (motiveBeta [] listConsT (listConsTTy []))

/-- `cMt` — the stored conv `Nat ≡ M t` inside `listConsMnTy`, enriched. -/
noncomputable def cMt : CvP listEnvUT 0 [] (.const 0 [])
    (.app listConsM listConsT) (.sort (.succ .zero)) :=
  enrichConvT_of_envWfT listEnvUWfT CtxWfT.nil
    (ConvT.symm _ _ _ _ (motiveBeta [] listConsT (listConsTTy [])))

/-- PIN: `qMn`'s regularity is definitionally `cMt.dr` — the stored conv
    is the same enrichment, so the correspondence is direct. -/
theorem qMn_reg_eq : qMn.reg.2 = cMt.dr := rfl

/-- §5 request kinds: pair-below `PB[a,b]`, the K1 bit `BIT[a,b]` on two
    sort typings of one type, and an outer `CL[a,b]`. -/
inductive S18Request : Type where
  | pb {e₁ T₁ e₂ T₂ : Expr Nat}
      (a : TyP listEnvUT 0 [] e₁ T₁) (b : TyP listEnvUT 0 [] e₂ T₂)
  | bit {T : Expr Nat} {u v : Level}
      (a : TyP listEnvUT 0 [] T (.sort u)) (b : TyP listEnvUT 0 [] T (.sort v))
  | cl {e T₁ T₂ : Expr Nat}
      (a : TyP listEnvUT 0 [] e T₁) (b : TyP listEnvUT 0 [] e T₂)

/-- the derivations each request stores. -/
def S18Request.derivations : S18Request → List (Σ e T, TyP listEnvUT 0 [] e T)
  | .pb a b | .cl a b => [⟨_, _, a⟩, ⟨_, _, b⟩]
  | .bit a b => [⟨_, _, a⟩, ⟨_, _, b⟩]

/-- §5's request table: the nine slot PBs and slot-BITs, the K1 pair
    across the real β, and the four outer requests of the current ES. -/
noncomputable def s18Requests : List S18Request :=
  [ .pb qA qA.reg.2, .bit qA.reg.2 pDSort1,
    .pb qM qM.reg.2, .bit qM.reg.2 pDMotive,
    .pb qMn qMn.reg.2, .bit qMn.reg.2 pDMt,
    .pb qMc qMc.reg.2, .bit qMc.reg.2 pDMc,
    .pb qMajor qMajor.reg.2, .bit qMajor.reg.2 pDL,
    .pb qACtor qACtor.reg.2, .bit qACtor.reg.2 pDSort1C,
    .pb qH qH.reg.2, .bit qH.reg.2 pDNat,
    .pb qT qT.reg.2, .bit qT.reg.2 pDL2,
    .pb qRecT qRecT.reg.2, .bit qRecT.reg.2 pDMt2,
    .bit pDMt s18cβ.dl, .bit s18cβ.dr pDNat,
    .pb s18hL s18hL.reg.2, .pb s18hR s18hR.reg.2, .cl s18H.dl s18hL, .cl s18hR s18H.dr ]

/-- §5's nine declaration-domain views, as stored `TyP`s. -/
noncomputable def s18DeclViews :
    List (Σ e T, TyP listEnvUT 0 [] e T) :=
  [⟨_, _, pDSort1⟩, ⟨_, _, pDMotive⟩, ⟨_, _, pDMt⟩, ⟨_, _, pDMc⟩,
   ⟨_, _, pDL⟩, ⟨_, _, pDSort1C⟩, ⟨_, _, pDNat⟩, ⟨_, _, pDL2⟩,
   ⟨_, _, pDMt2⟩]

/-- §5's entire computed surface, evaluated in ONE kernel pass: inside a
    single `decide`, `whnf` memoizes every enriched derivation, so `s18Nι`
    and each stored `TyP` weight are computed exactly once instead of once
    per theorem.  Every public obligation below is a projection of this
    conjunction, so no repeated normalization is paid per statement. -/
private theorem s18ComputedBudgets :
      (∀ r ∈ s18Requests, ∀ D ∈ r.derivations, D.2.2.wt AwList < s18Nι)
    ∧ ((qA.wt AwList < s18Nι ∧ qA.reg.2.wt AwList < s18Nι)
    ∧ (qM.wt AwList < s18Nι ∧ qM.reg.2.wt AwList < s18Nι)
    ∧ (qMn.wt AwList < s18Nι ∧ qMn.reg.2.wt AwList < s18Nι)
    ∧ (qMc.wt AwList < s18Nι ∧ qMc.reg.2.wt AwList < s18Nι)
    ∧ (qMajor.wt AwList < s18Nι ∧ qMajor.reg.2.wt AwList < s18Nι)
    ∧ (qACtor.wt AwList < s18Nι ∧ qACtor.reg.2.wt AwList < s18Nι)
    ∧ (qH.wt AwList < s18Nι ∧ qH.reg.2.wt AwList < s18Nι)
    ∧ (qT.wt AwList < s18Nι ∧ qT.reg.2.wt AwList < s18Nι)
    ∧ (qRecT.wt AwList < s18Nι ∧ qRecT.reg.2.wt AwList < s18Nι))
    ∧ ((pDSort1.wt AwList < s18Nι ∧ pDMotive.wt AwList < s18Nι
        ∧ pDMt.wt AwList < s18Nι)
    ∧ ((pDMc.wt AwList < s18Nι ∧ pDL.wt AwList < s18Nι
        ∧ pDSort1C.wt AwList < s18Nι)
    ∧ (pDNat.wt AwList < s18Nι ∧ pDL2.wt AwList < s18Nι
        ∧ pDMt2.wt AwList < s18Nι)))
    ∧ (∀ v ∈ s18DeclViews, ∀ a ∈ v.2.2.atoms AwList, a < s18Nι)
    ∧ (AwList 11 < s18Nι ∧ AwList 10 < s18Nι) := by
  decide

/-- every stored derivation's weight is strictly below `s18Nι` — the §5 bound,
    kernel-computed on the real derivations. -/
theorem s18_requests_below :
    ∀ r ∈ s18Requests, ∀ D ∈ r.derivations, D.2.2.wt AwList < s18Nι :=
  s18ComputedBudgets.1

/-- §4's bit-false discharges, one per slot — kernel-evaluated
    `levelIsZero` on the real regularity level at `σ = id`. -/
theorem bit_qA : levelIsZero (id qA.reg.1) = false := by decide
theorem bit_qM : levelIsZero (id qM.reg.1) = false := by decide
theorem bit_qMn : levelIsZero (id qMn.reg.1) = false := by decide
theorem bit_qMc : levelIsZero (id qMc.reg.1) = false := by decide
theorem bit_qMajor : levelIsZero (id qMajor.reg.1) = false := by decide
theorem bit_qACtor : levelIsZero (id qACtor.reg.1) = false := by decide
theorem bit_qH : levelIsZero (id qH.reg.1) = false := by decide
theorem bit_qT : levelIsZero (id qT.reg.1) = false := by decide
theorem bit_qRecT : levelIsZero (id qRecT.reg.1) = false := by decide

/-- §5.1's `qa.reg.2.wt ≤ qa.wt` side of each PB payment — the structural
    `TyP.wt_reg_le` lemma, no normalization needed. -/
theorem reg_le_qA : qA.reg.2.wt AwList ≤ qA.wt AwList := TyP.wt_reg_le _ _
theorem reg_le_qM : qM.reg.2.wt AwList ≤ qM.wt AwList := TyP.wt_reg_le _ _
theorem reg_le_qMn : qMn.reg.2.wt AwList ≤ qMn.wt AwList := TyP.wt_reg_le _ _
theorem reg_le_qMc : qMc.reg.2.wt AwList ≤ qMc.wt AwList := TyP.wt_reg_le _ _
theorem reg_le_qMajor : qMajor.reg.2.wt AwList ≤ qMajor.wt AwList := TyP.wt_reg_le _ _
theorem reg_le_qACtor : qACtor.reg.2.wt AwList ≤ qACtor.wt AwList := TyP.wt_reg_le _ _
theorem reg_le_qH : qH.reg.2.wt AwList ≤ qH.wt AwList := TyP.wt_reg_le _ _
theorem reg_le_qT : qT.reg.2.wt AwList ≤ qT.wt AwList := TyP.wt_reg_le _ _
theorem reg_le_qRecT : qRecT.reg.2.wt AwList ≤ qRecT.wt AwList := TyP.wt_reg_le _ _

/-- each stored argument typing is strictly below `s18Nι`, with its
    regularity — the `qa.wt < s18Nι ∧ qa.reg.2.wt ≤ qa.wt` payment shape;
    projections of the single fused budget evaluation. -/
theorem pb_qA_below : qA.wt AwList < s18Nι ∧ qA.reg.2.wt AwList < s18Nι :=
  s18ComputedBudgets.2.1.1
theorem pb_qM_below : qM.wt AwList < s18Nι ∧ qM.reg.2.wt AwList < s18Nι :=
  s18ComputedBudgets.2.1.2.1
theorem pb_qMn_below : qMn.wt AwList < s18Nι ∧ qMn.reg.2.wt AwList < s18Nι :=
  s18ComputedBudgets.2.1.2.2.1
theorem pb_qMc_below : qMc.wt AwList < s18Nι ∧ qMc.reg.2.wt AwList < s18Nι :=
  s18ComputedBudgets.2.1.2.2.2.1
theorem pb_qMajor_below :
    qMajor.wt AwList < s18Nι ∧ qMajor.reg.2.wt AwList < s18Nι :=
  s18ComputedBudgets.2.1.2.2.2.2.1
theorem pb_qACtor_below :
    qACtor.wt AwList < s18Nι ∧ qACtor.reg.2.wt AwList < s18Nι :=
  s18ComputedBudgets.2.1.2.2.2.2.2.1
theorem pb_qH_below : qH.wt AwList < s18Nι ∧ qH.reg.2.wt AwList < s18Nι :=
  s18ComputedBudgets.2.1.2.2.2.2.2.2.1
theorem pb_qT_below : qT.wt AwList < s18Nι ∧ qT.reg.2.wt AwList < s18Nι :=
  s18ComputedBudgets.2.1.2.2.2.2.2.2.2.1
theorem pb_qRecT_below :
    qRecT.wt AwList < s18Nι ∧ qRecT.reg.2.wt AwList < s18Nι :=
  s18ComputedBudgets.2.1.2.2.2.2.2.2.2.2

/-- the nine slot-BITs, discharged as `BitCoh id` — both sides type the
    same declared domain at concrete levels, so `levelIsZero` reduces. -/
theorem bitcoh_qA : BitCoh id qA.reg.2 pDSort1 := rfl
theorem bitcoh_qM : BitCoh id qM.reg.2 pDMotive := rfl
theorem bitcoh_qMn : BitCoh id qMn.reg.2 pDMt := rfl
theorem bitcoh_qMc : BitCoh id qMc.reg.2 pDMc := rfl
theorem bitcoh_qMajor : BitCoh id qMajor.reg.2 pDL := rfl
theorem bitcoh_qACtor : BitCoh id qACtor.reg.2 pDSort1C := rfl
theorem bitcoh_qH : BitCoh id qH.reg.2 pDNat := rfl
theorem bitcoh_qT : BitCoh id qT.reg.2 pDL2 := rfl
theorem bitcoh_qRecT : BitCoh id qRecT.reg.2 pDMt2 := rfl

/-- the two K1 correspondences across the original β:
    `BIT[real M t domain, s18cβ.dl]` and `BIT[s18cβ.dr, real Nat domain]`. -/
theorem s18k1_pair_1 : BitCoh id pDMt s18cβ.dl := rfl
theorem s18k1_pair_2 : BitCoh id s18cβ.dr pDNat := rfl

/-- every atom stored in each §5 declaration-domain view is strictly
    below `s18Nι` — `atoms_lt_of_wt_lt` over the fused weight facts; the
    admission-side const atoms are paid through `AwList`. -/
theorem pDSort1_atoms : ∀ a ∈ pDSort1.atoms AwList, a < s18Nι :=
  atoms_lt_of_wt_lt AwList pDSort1 s18ComputedBudgets.2.2.1.1.1
theorem pDMotive_atoms : ∀ a ∈ pDMotive.atoms AwList, a < s18Nι :=
  atoms_lt_of_wt_lt AwList pDMotive s18ComputedBudgets.2.2.1.1.2.1
theorem pDMt_atoms : ∀ a ∈ pDMt.atoms AwList, a < s18Nι :=
  atoms_lt_of_wt_lt AwList pDMt s18ComputedBudgets.2.2.1.1.2.2
theorem pDMc_atoms : ∀ a ∈ pDMc.atoms AwList, a < s18Nι :=
  atoms_lt_of_wt_lt AwList pDMc s18ComputedBudgets.2.2.1.2.1.1
theorem pDL_atoms : ∀ a ∈ pDL.atoms AwList, a < s18Nι :=
  atoms_lt_of_wt_lt AwList pDL s18ComputedBudgets.2.2.1.2.1.2.1
theorem pDSort1C_atoms : ∀ a ∈ pDSort1C.atoms AwList, a < s18Nι :=
  atoms_lt_of_wt_lt AwList pDSort1C s18ComputedBudgets.2.2.1.2.1.2.2
theorem pDNat_atoms : ∀ a ∈ pDNat.atoms AwList, a < s18Nι :=
  atoms_lt_of_wt_lt AwList pDNat s18ComputedBudgets.2.2.1.2.2.1
theorem pDL2_atoms : ∀ a ∈ pDL2.atoms AwList, a < s18Nι :=
  atoms_lt_of_wt_lt AwList pDL2 s18ComputedBudgets.2.2.1.2.2.2.1
theorem pDMt2_atoms : ∀ a ∈ pDMt2.atoms AwList, a < s18Nι :=
  atoms_lt_of_wt_lt AwList pDMt2 s18ComputedBudgets.2.2.1.2.2.2.2

/-- §5's fixed declaration-domain budget: every atom of every
    lazy-instantiated view is strictly below `s18Nι`. -/
theorem s18_decl_budget :
    ∀ v ∈ s18DeclViews, ∀ a ∈ v.2.2.atoms AwList, a < s18Nι :=
  s18ComputedBudgets.2.2.2.1

/-- the recursor const's own admission atom is paid through `AwList 11` —
    strictly below `s18Nι`. -/
theorem s18_aw11_below : AwList 11 < s18Nι := s18ComputedBudgets.2.2.2.2.1

/-- the constructor const's admission atom is paid through `AwList 10` —
    strictly below `s18Nι`. -/
theorem s18_aw10_below : AwList 10 < s18Nι := s18ComputedBudgets.2.2.2.2.2

/-- the two outer CLs hold reflexively on `s18H`'s chosen fields. -/
theorem s18cl_outer_left : CL listConsTable id [] s18H.dl s18hL := ConvMod.refl _
theorem s18cl_outer_right : CL listConsTable id [] s18hR s18H.dr := ConvMod.refl _

/-! ## §6–§7 the singleton table, the match, seven β steps, `ES` -/

/-- the erasure leaves: `Aε`, `Mε`, `mnε`, `mcε`, `hε`, `tε`. -/
def Aε : ETm := .const 0 []
def Mε : ETm := .lam (.const 0 [])
def mnε : ETm := .const 1 []
def mcε : ETm := .lam (.lam (.lam (.bvar 2)))
def hε : ETm := .app (.const 2 []) (.const 1 [])
def tε : ETm := .app (.const 9 [.succ .zero]) (.const 0 [])

/-- `recε` — the erased recursive call `rec.{1,1} Aε Mε mnε mcε tε`. -/
def recεCall : ETm :=
  ETm.appN (.const 11 [.succ .zero, .succ .zero])
    [Aε, Mε, mnε, mcε, tε]

/-- `majorε` — `cons.{1} Aε hε tε` at the constructor's `lsC = [1]`. -/
def majorE : ETm := ETm.appN (.const 10 [.succ .zero]) [Aε, hε, tε]

/-- `s18EL` — `s18hL`'s erasure: the redex `rec.{1,1} Aε Mε mnε mcε majorε`. -/
def s18EL : ETm :=
  ETm.appN (.const 11 [.succ .zero, .succ .zero])
    [Aε, Mε, mnε, mcε, majorE]

/-- `s18ER` — the retained result `mcε hε tε (recε Aε Mε mnε mcε tε)`. -/
def s18ER : ETm := .app (.app (.app mcε hε) tε) recεCall

/-- §7's rule — verbatim: head 11, four prefix args, the `cons` major at
    three spine args, and the seven-λ template whose recursive call uses
    the recursor-side `A` at `bvar 6` (never the constructor-side copy
    at `bvar 2`). -/
def listConsRule : CRule where
  head := 11
  nargs := fun _ => 4
  major := some (10, fun _ => 3)
  rhs := fun ls _ =>
    ETm.lam (ETm.lam (ETm.lam (ETm.lam (ETm.lam (ETm.lam (ETm.lam
      (ETm.appN (.bvar 3)
        [ .bvar 1, .bvar 0,
          ETm.appN (.const 11 ls)
            [.bvar 6, .bvar 5, .bvar 4, .bvar 3, .bvar 0] ])))))))

def listConsTable : List CRule := [listConsRule]

/-- `TableWF` for the singleton, mirroring `natSuccTable_wf`: rhs
    congruence at `const 11`, closedness under seven λs, no rule for the
    constructor head 10, singleton disjointness, empty bare premises. -/
theorem listConsTable_wf : TableWF listConsTable where
  congr :=
    { rhs := by
        intro ρ hρ ls₁ ls₂ ms₁ ms₂ hls _
        simp only [listConsTable, List.mem_singleton] at hρ; subst hρ
        refine .lam (.lam (.lam (.lam (.lam (.lam (.lam ?_))))))
        refine .app (.app (.app (.bvar _) (.bvar _)) (.bvar _)) ?_
        exact lvlEq_appN (.const _ hls)
          (.cons (.bvar _) (.cons (.bvar _) (.cons (.bvar _)
            (.cons (.bvar _) (.cons (.bvar _) .nil)))))
      nargs := by
        intro ρ hρ _ _ _
        simp only [listConsTable, List.mem_singleton] at hρ; subst hρ; rfl
      marity := by
        intro ρ hρ _ _ hm
        simp only [listConsTable, List.mem_singleton] at hρ; subst hρ
        cases hm; exact fun _ => rfl }
  closed := by
    intro ρ hρ ls ms
    simp only [listConsTable, List.mem_singleton] at hρ; subst hρ
    simp only [listConsRule, ETm.appN, ETm.ClosedAt]
    decide
  rigid := by
    intro ρ hρ d m hm σ hσ
    simp only [listConsTable, List.mem_singleton] at hρ hσ; subst hρ; subst hσ
    cases hm; decide
  bare_unique := by
    intro ρ hρ hm σ hσ _
    simp only [listConsTable, List.mem_singleton] at hρ; subst hρ
    simp only [listConsRule] at hm; exact Option.noConfusion hm
  ctor_disjoint := by
    intro ρ hρ σ hσ _ d e m n hm hn
    simp only [listConsTable, List.mem_singleton] at hρ hσ; subst hρ; subst hσ
    exact ⟨rfl, fun _ => rfl⟩
  bare_nullary := by
    intro ρ hρ hm ls
    simp only [listConsTable, List.mem_singleton] at hρ; subst hρ
    simp only [listConsRule] at hm; exact Option.noConfusion hm

/-- the seven-λ template body at `ls = [1,1]`:
    `mc hd tl (rec A M mn mc tl)` in de Bruijn coordinates. -/
def s18Body : ETm :=
  .app (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
    (ETm.appN (.const 11 [.succ .zero, .succ .zero])
      [.bvar 6, .bvar 5, .bvar 4, .bvar 3, .bvar 0])

/-- PIN: `listConsRule`'s template at the concrete level list. -/
theorem listConsRule_rhs_eq :
    listConsRule.rhs [.succ .zero, .succ .zero] [.succ .zero] =
      .lam (.lam (.lam (.lam (.lam (.lam (.lam s18Body)))))) := rfl

/-- PIN: the match root — `s18EL → appN template [Aε, Mε, mnε, mcε, Aε, hε, tε]`.
    `args = [Aε, Mε, mnε, mcε]` (the recursor-side prefix), `bs = [Aε, hε, tε]`
    (the constructor spine at `lsC = [1]`). -/
theorem listCons_croot :
    CRoot listConsTable s18EL
      (ETm.appN (listConsRule.rhs [.succ .zero, .succ .zero] [.succ .zero])
        [Aε, Mε, mnε, mcε, Aε, hε, tε]) :=
  CRoot.ctor (List.mem_singleton_self _) rfl [.succ .zero, .succ .zero]
    [.succ .zero] [Aε, Mε, mnε, mcε] [Aε, hε, tε] rfl rfl

/-- the β residuals at each peeled λ (kernel-evaluated `inst` chains):
    `inst 0 a (λᵏ. X) = λᵏ. inst k a X`, each substituend closed so the
    lifts are the identity. -/
def s18R1 : ETm := ETm.inst 6 Aε s18Body
def s18R2 : ETm := ETm.inst 5 Mε s18R1
def s18R3 : ETm := ETm.inst 4 mnε s18R2
def s18R4 : ETm := ETm.inst 3 mcε s18R3
def s18R5 : ETm := ETm.inst 2 Aε s18R4
def s18R6 : ETm := ETm.inst 1 hε s18R5

def s18M1 : ETm := .lam (.lam (.lam (.lam (.lam (.lam s18R1)))))
def s18M2 : ETm := .lam (.lam (.lam (.lam (.lam s18R2))))
def s18M3 : ETm := .lam (.lam (.lam (.lam s18R3)))
def s18M4 : ETm := .lam (.lam (.lam s18R4))
def s18M5 : ETm := .lam (.lam s18R5)
def s18M6 : ETm := .lam s18R6

/-- PINs: each β step's kernel-evaluated target — index arithmetic, not a
    normal-value check. -/
theorem s18_beta1_tgt :
    ETm.inst 0 Aε (.lam (.lam (.lam (.lam (.lam (.lam s18Body)))))) =
      s18M1 := rfl
theorem s18_beta2_tgt :
    ETm.inst 0 Mε (.lam (.lam (.lam (.lam (.lam s18R1))))) = s18M2 := rfl
theorem s18_beta3_tgt :
    ETm.inst 0 mnε (.lam (.lam (.lam (.lam s18R2)))) = s18M3 := rfl
theorem s18_beta4_tgt :
    ETm.inst 0 mcε (.lam (.lam (.lam s18R3))) = s18M4 := rfl
theorem s18_beta5_tgt :
    ETm.inst 0 Aε (.lam (.lam s18R4)) = s18M5 := rfl
theorem s18_beta6_tgt :
    ETm.inst 0 hε (.lam s18R5) = s18M6 := rfl
/-- the seven-step chain lands on `s18ER` exactly. -/
theorem s18_beta7_tgt : ETm.inst 0 tε s18R6 = s18ER := rfl

/-- the seven β steps as `RStep`s, lifted through the outer applications.
    Each `.beta`'s first argument is the peeled λ's BODY; the kernel's
    `inst` evaluates to the next `λᵏ. inst k a s18Rⱼ` residual. -/
def s18Step1 : RStep listConsTable
    (ETm.appN (listConsRule.rhs [.succ .zero, .succ .zero] [.succ .zero])
      [Aε, Mε, mnε, mcε, Aε, hε, tε])
    (ETm.appN s18M1 [Mε, mnε, mcε, Aε, hε, tε]) :=
  .appL tε (.appL hε (.appL Aε (.appL mcε (.appL mnε (.appL Mε
    (.beta (.lam (.lam (.lam (.lam (.lam (.lam s18Body)))))) Aε))))))

def s18Step2 : RStep listConsTable
    (ETm.appN s18M1 [Mε, mnε, mcε, Aε, hε, tε])
    (ETm.appN s18M2 [mnε, mcε, Aε, hε, tε]) :=
  .appL tε (.appL hε (.appL Aε (.appL mcε (.appL mnε
    (.beta (.lam (.lam (.lam (.lam (.lam s18R1))))) Mε)))))

def s18Step3 : RStep listConsTable
    (ETm.appN s18M2 [mnε, mcε, Aε, hε, tε])
    (ETm.appN s18M3 [mcε, Aε, hε, tε]) :=
  .appL tε (.appL hε (.appL Aε (.appL mcε
    (.beta (.lam (.lam (.lam (.lam s18R2)))) mnε))))

def s18Step4 : RStep listConsTable
    (ETm.appN s18M3 [mcε, Aε, hε, tε])
    (ETm.appN s18M4 [Aε, hε, tε]) :=
  .appL tε (.appL hε (.appL Aε
    (.beta (.lam (.lam (.lam s18R3))) mcε)))

def s18Step5 : RStep listConsTable
    (ETm.appN s18M4 [Aε, hε, tε])
    (ETm.appN s18M5 [hε, tε]) :=
  .appL tε (.appL hε (.beta (.lam (.lam s18R4)) Aε))

def s18Step6 : RStep listConsTable
    (ETm.appN s18M5 [hε, tε])
    (ETm.appN s18M6 [tε]) :=
  .appL tε (.beta (.lam s18R5) hε)

def s18Step7 : RStep listConsTable
    (ETm.appN s18M6 [tε]) s18ER :=
  .beta s18R6 tε

/-- PIN: `s18hL.eps id []` is exactly `s18EL` — the real enriched typing's own
    erasure (level-gated consts stay consts; `ls.map id = ls`). -/
theorem s18hL_eps_el : s18hL.eps id [] = s18EL := rfl

/-- PIN: `s18hR.eps id []` is exactly `s18ER`. -/
theorem s18hR_eps_er : s18hR.eps id [] = s18ER := rfl

/-- §7's target: `ES listConsTable id [] s18H` — the retained-result ι
    discharged by its real match plus exactly seven β steps. The recursive
    call `recε Aε Mε mnε mcε tε` is KEPT, not reduced through `mc`. -/
theorem listCons_iota_erasure : ES listConsTable id [] s18H := by
  show ConvMod (EStep listConsTable) LvlEq (s18hL.eps id []) (s18hR.eps id [])
  rw [s18hL_eps_el, s18hR_eps_er]
  exact (ConvMod.fwd (.inl (.cr listCons_croot))).trans
    ((ConvMod.fwd (.inl s18Step1)).trans
      ((ConvMod.fwd (.inl s18Step2)).trans
        ((ConvMod.fwd (.inl s18Step3)).trans
          ((ConvMod.fwd (.inl s18Step4)).trans
            ((ConvMod.fwd (.inl s18Step5)).trans
              ((ConvMod.fwd (.inl s18Step6)).trans
                (ConvMod.fwd (.inl s18Step7))))))))

/-! ## §9 the exactness mutants -/

/-- §9-a: the wrong recursive argument — `sort 0` where the recursor-side
    `A` belongs (`bvar 6` of the template). -/
def s18MutWrongRec : ETm :=
  .app (.app (.app mcε hε) tε)
    (ETm.appN (.const 11 [.succ .zero, .succ .zero])
      [.sort .zero, Mε, mnε, mcε, tε])

/-- the mutant is NOT `s18ER` — the exact-RHS check rejects it. -/
theorem mut_wrongRec_ne : s18MutWrongRec ≠ s18ER := by decide

/-- but it β-collapses to the same head `hε` — `mc` discards its third
    argument. The exactness check, not the value check, is what rejects
    the wrong recursive argument. -/
theorem mut_wrongRec_value :
    ETm.inst 0
      (ETm.appN (.const 11 [.succ .zero, .succ .zero])
        [.sort .zero, Mε, mnε, mcε, tε])
      (ETm.inst 1 tε (ETm.inst 2 hε (.bvar 2))) = hε := rfl

/-- the correct call collapses to the same value — confirming the check
    must be on the retained RHS, not the evaluated head. -/
theorem correct_value :
    ETm.inst 0 recεCall (ETm.inst 1 tε (ETm.inst 2 hε (.bvar 2))) = hε := rfl

/-- §9-b: `plain` miscoded as `directRec` — `analyzeFields` returns the
    real classification, never the swapped one. -/
theorem mut_kinds_rejected : analyzeFields 8
    [.bvar 0, .app (.const 8 [.param 0]) (.bvar 1)] ≠
      some [.directRec, .directRec] := by decide

/-- the full swap is likewise refused. -/
theorem mut_kinds_swap_rejected : analyzeFields 8
    [.bvar 0, .app (.const 8 [.param 0]) (.bvar 1)] ≠
      some [.directRec, .plain] := by decide

/-- §9-c: dropping the constructor-side parameter — a six-λ template
    applied to all seven arguments leaves a seventh argument stranded;
    the residual is not `s18ER`. -/
def s18MutDropParam : ETm :=
  .app (ETm.inst 0 hε (ETm.inst 1 Aε (ETm.inst 2 mcε (ETm.inst 3 mnε
    (ETm.inst 4 Mε (ETm.inst 5 Aε s18Body)))))) tε

theorem mut_dropParam_ne : s18MutDropParam ≠ s18ER := by decide

/-- §9-d: `hd`/`tl` swapped in the outer application — `mcε tε hε` is a
    different RHS. -/
def s18MutSwap : ETm := .app (.app (.app mcε tε) hε) recεCall

theorem mut_swap_ne : s18MutSwap ≠ s18ER := by decide

/-- §9-e: `lsC` vs `ls` — the miswritten TEMPLATE level list. The real
    redex `s18EL`, the position table, `args`, `bs` are all unchanged; only
    the level list fed to the rule's `rhs` is the constructor's `[1]`
    where the recursor's `[1,1]` belongs, so the applied template's
    embedded `rec` carries `const 11 [1]` instead of `const 11 [1,1]`. -/
def s18MutLsApplied : ETm :=
  ETm.appN (listConsRule.rhs [.succ .zero] [.succ .zero])
    [Aε, Mε, mnε, mcε, Aε, hε, tε]

/-- the miswritten application is not the real CRoot target — the exact
    correspondence rejects it (the redex and the position table never
    changed; `mc` still discards the mislevelled call into the same
    head `hε`, which is why the check is exact, not normal-valued). -/
theorem mut_ls_ne : s18MutLsApplied ≠
    ETm.appN (listConsRule.rhs [.succ .zero, .succ .zero] [.succ .zero])
      [Aε, Mε, mnε, mcε, Aε, hε, tε] := by decide

end Rcic.Syn

#print axioms Rcic.Syn.wConsNat
#print axioms Rcic.Syn.wConsNat_cert
#print axioms Rcic.Syn.wConsNat_lhs
#print axioms Rcic.Syn.wConsNat_rhs
#print axioms Rcic.Syn.s18prefixTy
#print axioms Rcic.Syn.listConsMcTy
#print axioms Rcic.Syn.s18hLT
#print axioms Rcic.Syn.s18hRT
#print axioms Rcic.Syn.s18hL
#print axioms Rcic.Syn.s18hR
#print axioms Rcic.Syn.s18H
#print axioms Rcic.Syn.s18Nι_eq
#print axioms Rcic.Syn.s18_requests_below
#print axioms Rcic.Syn.s18RecTele_eq
#print axioms Rcic.Syn.s18CtorTele_eq
#print axioms Rcic.Syn.pDSort1
#print axioms Rcic.Syn.pDMotive
#print axioms Rcic.Syn.pDMt
#print axioms Rcic.Syn.pDMc
#print axioms Rcic.Syn.pDL
#print axioms Rcic.Syn.pDSort1C
#print axioms Rcic.Syn.pDNat
#print axioms Rcic.Syn.pDL2
#print axioms Rcic.Syn.pDMt2
#print axioms Rcic.Syn.s18_decl_budget
#print axioms Rcic.Syn.s18_aw10_below
#print axioms Rcic.Syn.s18_aw11_below
#print axioms Rcic.Syn.s18k1_pair_1
#print axioms Rcic.Syn.s18k1_pair_2
#print axioms Rcic.Syn.listConsTable_wf
#print axioms Rcic.Syn.listCons_croot
#print axioms Rcic.Syn.s18_beta7_tgt
#print axioms Rcic.Syn.s18hL_eps_el
#print axioms Rcic.Syn.s18hR_eps_er
#print axioms Rcic.Syn.listCons_iota_erasure
#print axioms Rcic.Syn.mut_wrongRec_ne
#print axioms Rcic.Syn.mut_dropParam_ne
#print axioms Rcic.Syn.mut_swap_ne
#print axioms Rcic.Syn.mut_ls_ne
