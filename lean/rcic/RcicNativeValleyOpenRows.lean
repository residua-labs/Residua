import rcic.RcicNativeValleyLevels
import rcic.RcicNativeValleyIota
import rcic.RcicNativeValleyAppBeta
import rcic.RcicNativeValleyLamEta
import rcic.RcicNativeValleyLet
import rcic.RcicNativeValleySubst
import rcic.RcicNativeValleyLetCtx

/-!
# RcicNativeValleyOpenRows — the `OpenRows` record from the fronts
(Wall 1, `NativeConvValleys`, piece 15)

The nine fields of `OpenRows` (`RcicNativeValleyAssemble`), as the session-7 modules leave
them:

| field | status |
|---|---|
| `retype` | the front `Retype` (uniqueness-shaped, `NATIVE_VALLEYS_STATUS.md` §2b) |
| `consts_delta` | CLOSED (`consts_delta_of`, `RcicNativeValleyLevels`) |
| `subst0` | CLOSED (`certSubst0_of`, `RcicNativeValleySubst`) |
| `app_beta` | `Retype`, `PropAlign`, `PiPropCodom`, `AppBetaEta`, `AppBetaIota` (`app_beta_of`) |
| `lam_eta` | `Retype`, `PropAlign`, `LamEtaApp`, `LamEtaBeta`, `LamEtaIota` (`lam_eta_of`) |
| `letE_letE` | `LetJoin` (`letE_letE_of`; `CertLetAnnCtx` CLOSED, `certLetAnnCtx_of`) |
| `letE_zeta` | `LetJoin` (`letE_zeta_of`; `CertLetAnnCtx`, `CertSubstLet` CLOSED, `certSubstLet_of`) |
| `zeta_zeta` | `LetJoin` (`zeta_zeta_of`; `CertSubstLet` CLOSED) |
| `iota_commute` | `Retype`, `IotaDetU`, `IotaRefireT` (`iotaCommute_of`) |

`RowFronts` bundles the fronts; `openRows_of` builds the record; `nativeConvValleys_of_fronts`
closes the chain to the spec's §5.5 shape from the fronts, the `let` row of the producer
(`LetValley`), `EnvWfT` and the leaf transports (weakening, and context transport along
`LetAnnCtxConvT`, which covers `F8EtaK.AssumpCtxConvT`).

Session 8: `CertLetAnnCtx` and `CertSubstLet` are discharged (`RcicNativeValleyLetCtx`,
`RcicNativeValleySubst`) and leave `RowFronts`. NOTE (session 8, `NATIVE_VALLEYS_STATUS.md` §8):
`LamEtaApp` is refuted as a one-step join by an irrelevance-leaf instance, so `RowFronts` is
uninhabited whenever the leaf interface is inhabited at a `Prop` with two distinct proofs; the
chain below is correct and vacuous there — the record is kept as the exact statement of what the
session-7 reduction demands.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- The fronts the remaining rows reduce to, as one record. -/
structure RowFronts (E : ResolvedEnv) (n : Nat)
    (PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type) : Type where
  retype : Retype E n PEq
  propAlign : PropAlign E n
  piPropCodom : PiPropCodom E n
  iotaDet : IotaDetU E
  iotaRefire : IotaRefireT E n PEq
  appBetaEta : AppBetaEta E n PEq
  appBetaIota : AppBetaIota E n PEq
  lamEtaApp : LamEtaApp E n PEq
  lamEtaBeta : LamEtaBeta E n PEq
  lamEtaIota : LamEtaIota E n PEq
  letJoin : LetJoin E n PEq

/-- The `OpenRows` record from the fronts, `EnvWfT` and the leaf transports. -/
noncomputable def openRows_of (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
        LetAnnCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T)
    (F : RowFronts E n PEq) : OpenRows E n PEq :=
  let S : CertSubst0 E n PEq := certSubst0_of hW L hPEqL
  let SL : CertSubstLet E n PEq := certSubstLet_of hW L hPEqL
  let Ac : CertAssumpCtx E n PEq :=
    certAssumpCtx_of (PEq := PEq) (envClosed_of_envWfT hW) (fun hcc hp => hPEqC_ofAssump (PEq := PEq) (fun hcc' hp' => hPEqC hcc' hp') hcc hp)
  let Lc : CertLetAnnCtx E n PEq :=
    certLetAnnCtx_of (PEq := PEq) (envClosed_of_envWfT hW) (fun hcc hp => hPEqC hcc hp)
  { retype := F.retype
    consts_delta := consts_delta_of hW L
    subst0 := S
    app_beta := app_beta_of hW L F.retype F.propAlign F.piPropCodom S Ac F.appBetaEta
      F.appBetaIota
    lam_eta := lam_eta_of hW L F.retype F.propAlign F.lamEtaApp F.lamEtaBeta F.lamEtaIota
    letE_letE := letE_letE_of hW L Lc F.letJoin
    letE_zeta := letE_zeta_of hW L Lc SL F.letJoin
    zeta_zeta := zeta_zeta_of hW L SL F.letJoin
    iota_commute := iotaCommute_of L F.retype F.iotaDet F.iotaRefire }

/-- The spec's §5.5 shape from the fronts, the producer's `let` row, `EnvWfT` and the leaf
    transports. -/
theorem nativeConvValleys_of_fronts (hW : EnvWfT E) (L : LeafIface E n PEq)
    (hPEqL : ∀ {Γ : LCtx} {p q T : Expr Nat} {d' : LocalDecl} {c : Nat},
        PEq Γ p q T →
        PEq (insertAt d' c Γ) (lift c 1 p) (lift c 1 q) (lift c 1 T))
    (hPEqC : ∀ {Γ Γ' : LCtx} {p q T : Expr Nat},
        LetAnnCtxConvT E n Γ Γ' → PEq Γ p q T → PEq Γ' p q T)
    (F : RowFronts E n PEq) (Lt : LetValley E n PEq) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {a b T : Expr Nat} (c : ConvT E n Γ a b T) :
    ∃ centre : Expr Nat,
      Nonempty (ParRedTStar PEq E n Γ a centre T) ∧
      Nonempty (ParRedTStar PEq E n Γ b centre T) :=
  nativeConvValleys_of_rows (openRows_of hW L hPEqL hPEqC F) hW L hPEqL
    (fun hcc hp => hPEqC_ofAssump (PEq := PEq) (fun hcc' hp' => hPEqC hcc' hp') hcc hp) Lt hΓ c

end Rcic.Declarative.NativeValleys
