import rcic.RcicNativeValleyFronts
import rcic.RcicEtaKHeadInvariant
import rcic.RcicParRedCore

/-!
# RcicNativeValleyIota — the ι row of the certified diamond
(Wall 1, `NativeConvValleys`, piece 11)

`OpenRows.iota_commute` (`RcicNativeValleyAssemble`): from `lhs' →ι rhs` and a certified
`lhs' ⇒ k` at `T`, a `j` with `rhs ⇒ j` at `T` and an `IotaTail` at the other input's index —
ι re-fires at `k`, or `j = k`.

**The finding that fixed the statement.** The step `lhs' ⇒ k` is produced by the assembler's
recursion and may be an irrelevance LEAF (`join_peq_indep` emits `CStep.irr` legs), so `k` is
an arbitrary proof and ι cannot re-fire at it; the row as first stated (ι always re-fires) was
unprovable. In that case `T` is a `Prop` (`LeafIface.prop`) and the original reduct steps to
`k` by irrelevance at `T`: the join is `k`. Hence `IotaTail.stay`.

**What closes here** (`iotaCore`, recursion on the certificate of `lhs' ⇒ k` with the source
read through an equation, the landed `parRedT_lam` technique):

* `refl` — `j := rhs`, ι re-fires by the given landing;
* `peq` — `j := k`, the irrelevance step `rhs ⇒ k` at the leaf's `Prop`;
* `conv` — peeled, `rhs` and the certificate moved to the inner index by the chain read
  backwards (`TyConvT.symmT`);
* nested `iotaSpine` (`lhs' ⇒ m`, `m →ι k`) — by recursion on the inner step: if ι re-fires at
  `m` onto `j₀`, determinism (`IotaDetU`) gives `j₀ = k`; if the inner join is `m` itself, the
  original reduct's step to `m` absorbs `m →ι k` into one `iotaSpine` step onto `k`;
* every other structural root is refuted: an ι source is a `recCall`, i.e. an application
  whose function is a `const`-headed spine (`derivedIotaU_source`, `foldApps_snoc`,
  `foldApps_const_ne_lam_any`);
* the `app` root — the classical ι commutation — is the front `IotaRefireT`.

**The other index** (`iotaCommute_of`): when ι re-fires at `k` onto `j`, the certified step
`k ⇒ j` at `T` (one `iotaSpine` over `refl k`, certificate `k ← lhs' → rhs → j`) is presented
at `T'` through `Retype`; its right endpoint and certificate are the `IotaTail.refire` data.
So the ι row is closed modulo `Retype`, `IotaDetU` and `IotaRefireT`.

`closure_claim = 0`. No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

/-- Every ι source is a recursor call: a `const`-headed spine applied to the major. -/
def derivedIotaU_source {lhs rhs : Expr Nat} (hI : DerivedIotaU E lhs rhs) :
    Σ' (r : Nat) (ls : List Level) (pre : List (Expr Nat)) (major : Expr Nat),
      lhs = recCall (.const r ls) pre major :=
  match hI with
  | .ofU w => ⟨w.recRef, w.ls, w.preMajor, ctorMajor w, rfl⟩
  | .ofUS w =>
      ⟨w.recRef, w.ls, w.preMajor, foldApps (.const w.ctorRef w.lsC) (w.ctorParams ++ w.fields),
        rfl⟩

/-- The core of the ι row at the step's own index: `j` with `rhs ⇒ j` at `T`, and ι re-firing
    at `k` onto `j` or `j = k`. Recursion on the certificate of the step out of the redex,
    its source read through the equation `x = lhs'`. -/
def iotaCore (L : LeafIface E n PEq) (D : IotaDetU E) (IR : IotaRefireT E n PEq) {Γ : LCtx}
    (hΓ : CtxWfT E n Γ) {lhs' rhs : Expr Nat} (hI : DerivedIotaU E lhs' rhs) :
    {x k T : Expr Nat} → {p : ParRedT PEq E n Γ x k T} → Certified p → x = lhs' →
    ConvT E n Γ lhs' rhs T → HasTyT E n Γ rhs T →
    Σ' (j : Expr Nat), CStep E n PEq Γ rhs j T ×' (DerivedIotaU E k j ⊕' j = k)
  | _, _, _, _, @Certified.refl _ _ _ _ _ _ _ _, hx, _, hrhs => by
      subst hx
      exact ⟨rhs, ⟨.refl _ _ _ hrhs, .refl (.refl _ _ _ hrhs)⟩, .inl hI⟩
  | _, _, _, _, @Certified.peq _ _ _ _ _ _ _ h _, hx, _, hrhs => by
      subst hx
      exact ⟨_, CStep.irr L (L.prop h) hrhs (L.typed h).2, .inr rfl⟩
  | _, _, _, _, @Certified.conv _ _ _ _ _ _ A _ _ hcT _ ch, hx, hc, hrhs =>
      let hrhsA : HasTyT E n Γ rhs A := hasTyT_of_tyConv hrhs hcT.symmT
      let hcA : ConvT E n Γ lhs' rhs A := convT_of_tyConv hc hcT.symmT
      let ⟨j, pr, tl⟩ := iotaCore L D IR hΓ hI ch hx hcA hrhsA
      ⟨j, pr.reindex hcT, tl⟩
  | _, _, _, _, @Certified.iotaSpine _ _ _ _ _ m k T _ hI₂ hm hk c₂ cinner, hx, hc, hrhs =>
      match iotaCore L D IR hΓ hI cinner hx hc hrhs with
      | ⟨_, pr, .inl hIj⟩ => ⟨k, (D hIj hI₂) ▸ pr, .inr rfl⟩
      | ⟨_, pr, .inr e⟩ =>
          let pr' : CStep E n PEq Γ rhs m T := e ▸ pr
          ⟨k, ⟨.iotaSpine Γ rhs m k T pr'.step hI₂ hm hk,
            .iotaSpine (.trans _ _ _ _ _ pr'.toConvT
              (.trans _ _ _ _ _ (.symm _ _ _ _ cinner.root) c₂)) pr'.cert⟩, .inr rfl⟩
  | _, _, _, _, cq@(@Certified.app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cf ca), hx, hc,
      hrhs => by
      subst hx
      exact IR hΓ hI hc cq cf ca hrhs
  | _, _, _, _, .sortEq .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .consts .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .bvarZeta .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .delta .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .beta .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp only [recCall, foldApps_snoc, Expr.app.injEq] at hx
      exact (F8EtaK.foldApps_const_ne_lam_any hx.1.symm).elim
  | _, _, _, _, .lam .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .pi .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .letE .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .zeta .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .lit .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx
  | _, _, _, _, .eta .., hx, _, _ => by
      obtain ⟨r, ls, pre, major, hl⟩ := derivedIotaU_source hI
      rw [hl] at hx; simp [recCall, foldApps_snoc] at hx

/-- `OpenRows.iota_commute` from the fronts: the core at the step's own index, and — when ι
    re-fires at `k` — the certified ι step `k ⇒ j` presented at the other index by `Retype`
    (its right endpoint and certificate are the `refire` data). -/
def iotaCommute_of (L : LeafIface E n PEq) (Rt : Retype E n PEq) (D : IotaDetU E)
    (IR : IotaRefireT E n PEq) :
    ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {lhs' rhs k T T' : Expr Nat},
      DerivedIotaU E lhs' rhs → ConvT E n Γ lhs' rhs T → CStep E n PEq Γ lhs' k T →
      HasTyT E n Γ rhs T → HasTyT E n Γ k T' →
      Σ' (j : Expr Nat), CStep E n PEq Γ rhs j T ×' IotaTail E n Γ k j T' :=
  fun {Γ} hΓ {_ _ k T T'} hI hc pk hrhs hk' =>
    match iotaCore L D IR hΓ hI pk.cert rfl hc hrhs with
    | ⟨j, pr, .inr h⟩ => ⟨j, pr, .stay h⟩
    | ⟨j, pr, .inl hIj⟩ =>
        let hk : HasTyT E n Γ k T := pk.rightTyped L hΓ
        let hj : HasTyT E n Γ j T := pr.rightTyped L hΓ
        let ckj : ConvT E n Γ k j T :=
          .trans _ _ _ _ _ (.symm _ _ _ _ pk.toConvT) (.trans _ _ _ _ _ hc pr.toConvT)
        let s : CStep E n PEq Γ k j T :=
          ⟨.iotaSpine Γ k k j T (.refl Γ k T hk) hIj hk hj,
            .iotaSpine ckj (.refl (.refl Γ k T hk))⟩
        let s' : CStep E n PEq Γ k j T' := Rt hΓ hk' s
        ⟨j, pr, .refire hIj (s'.rightTyped L hΓ) s'.toConvT⟩

end Rcic.Declarative.NativeValleys
