import rcic.RcicSynA6Owner

/-!
# A6 — changed Π/λ/let binders: the two-C scalar span

`BELOWC_A6_LINK_DECODER.md` §4 (ChatGPT J line, docs PR #7450), implemented on
`RcicSynA6Link` / `RcicSynA6Owner` (fable-step ITEM 6, 2026-10-17). `closure_claim = 0`.

For a changed binder `cA : A ≡ A' : sort w` (the domain conversion of a `CvP.pi` /
`CvP.lam` / `CvP.letE` node) the two body traces reach `ΓL = declL :: Γ` and
`ΓR = declR :: Γ` at one slot `j` under one map `μ`. The span pairs each terminal domain
representative with an endpoint / provider view of the SAME subject at its own context
(two C legs), and the middle is a scalar on one recorded sort, `bit (μ w) = bit (μ w)`:

* **slot `0`** (`binderSpanZero`): the endpoint views are `L0 = wk₀ cA.dl`,
  `R0 = wk₀ cA.dr` (subjects `lift 0 1 A`, `lift 0 1 A'`, both at the bridge's own sort
  `w`); each survivor's lookup IS that subject (`lookupType_cons_zero`).
* **slot `k+1`** (`binderSpanSucc`): both sides read the same tail entry `Γ[k]`; its
  provider `I` is the root receipt's selected domain field (`rootOwner`), weakened up to
  `Γ` (`TyP.wkDrop`, the dropped entries re-entered one by one) and then separately
  through `declL` and `declR`; both C legs have the provider's own sort.
* Changed let values do not obstruct this: `lookupType` reads the type, not the value,
  and `TyP.wk` accepts either declaration (`declL`/`declR` are arbitrary entries with
  the required stored types).

The acquisition boundary stays (recorded, not claimed): `hb.dr` is in the left
context; the span does not fabricate the right body / `H` nor the full changed-let-body
`EConv`. Residue carried: W-A6-RIGHT-SITE-ACQUISITION.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- The innermost entry looks up as its stored type under one lift, whatever its kind. -/
theorem lookupType_cons_zero (d : LocalDecl) (Γ : LCtx) :
    lookupType (d :: Γ) 0 = some (lift 0 1 (LocalDecl.ty d)) := by
  cases d <;> rfl

/-- Re-enter the `k` dropped entries of `Γ` one at a time: a typing at `Γ.drop k`
    weakens to `Γ` at cutoff `0`, `k` times (`lift_lift_merge`). -/
def TyP.wkDrop {E : ResolvedEnv} {n : Nat} :
    (Γ : LCtx) → (k : Nat) → k ≤ Γ.length → {e T : Expr Nat} →
      TyP E n (Γ.drop k) e T → TyP E n Γ (lift 0 k e) (lift 0 k T)
  | _, 0, _, _, _, D => by rw [lift_zero, lift_zero]; exact D
  | [], k + 1, hk, _, _, _ => absurd hk (by simp)
  | d :: Γ, k + 1, hk, e, T, D => by
      have D' : TyP E n Γ (lift 0 k e) (lift 0 k T) :=
        TyP.wkDrop Γ k (Nat.le_of_succ_le_succ hk) D
      rw [← lift_lift_merge 1 k 0 0 (Nat.le_refl 0) (Nat.zero_le _) e,
        ← lift_lift_merge 1 k 0 0 (Nat.le_refl 0) (Nat.zero_le _) T]
      exact TyP.wk E n Γ _ _ d 0 D'

/-- **The two-C scalar span** at one slot `j` of a changed binder: each terminal
    representative `J` is paired with a view `P` of the same subject at the same context
    (a C leg), and both views carry ONE recorded sort `w` — the scalar middle
    `bit (μ w) = bit (μ w)` is reflexive for every map `μ`. -/
structure BinderSpan (E : ResolvedEnv) (n : Nat) (ΓL ΓR : LCtx) (j : Nat) : Type where
  BL : Expr Nat
  BR : Expr Nat
  hlookL : lookupType ΓL j = some BL
  hlookR : lookupType ΓR j = some BR
  {uL : Level}
  JL : TyP E n ΓL BL (.sort uL)
  {uR : Level}
  JR : TyP E n ΓR BR (.sort uR)
  w : Level
  PL : TyP E n ΓL BL (.sort w)
  PR : TyP E n ΓR BR (.sort w)

/-- The scalar middle: on the shared recorded sort every map agrees with itself. -/
theorem BinderSpan.middle {E : ResolvedEnv} {n : Nat} {ΓL ΓR : LCtx} {j : Nat}
    (sp : BinderSpan E n ΓL ΓR j) (μ : Level → Level) :
    levelIsZero (μ sp.w) = levelIsZero (μ sp.w) := rfl

/-- **Slot `0`** of a changed binder: the endpoint views `wk₀ cA.dl` / `wk₀ cA.dr`. -/
def binderSpanZero {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' : Expr Nat} {w : Level}
    (cA : CvP E n Γ A A' (.sort w)) (declL declR : LocalDecl)
    (hL : LocalDecl.ty declL = A) (hR : LocalDecl.ty declR = A')
    (sL : Survivor E n (declL :: Γ) 0) (sR : Survivor E n (declR :: Γ) 0) :
    BinderSpan E n (declL :: Γ) (declR :: Γ) 0 :=
  have hBL : sL.dom = lift 0 1 A :=
    Option.some.inj (sL.hlook.symm.trans (by rw [lookupType_cons_zero, hL]))
  have hBR : sR.dom = lift 0 1 A' :=
    Option.some.inj (sR.hlook.symm.trans (by rw [lookupType_cons_zero, hR]))
  { BL := lift 0 1 A, BR := lift 0 1 A',
    hlookL := by rw [lookupType_cons_zero, hL],
    hlookR := by rw [lookupType_cons_zero, hR],
    uL := sL.u, JL := by rw [← hBL]; exact sL.rep,
    uR := sR.u, JR := by rw [← hBR]; exact sR.rep,
    w := w,
    PL := TyP.wk E n Γ A (.sort w) declL 0 cA.dl,
    PR := TyP.wk E n Γ A' (.sort w) declR 0 cA.dr }

/-- A successful entry read bounds the index. -/
theorem succ_le_length_of_get? {Γ : LCtx} {k : Nat} (h : ∃ d, Γ.get? k = some d) :
    k + 1 ≤ Γ.length := by
  obtain ⟨d, hd⟩ := h
  rw [List.get?_eq_getElem?] at hd
  exact Nat.succ_le_of_lt (List.getElem?_eq_some.mp hd).1

/-- **Slot `k+1`** of a changed binder: both sides read the same tail entry `Γ[k]`,
    whose provider is the root receipt's own selected domain field, weakened up to `Γ`
    and then separately through `declL` / `declR`; both C legs carry the provider's
    sort. -/
noncomputable def binderSpanSucc {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hΓ : CtxP E n Γ)
    (declL declR : LocalDecl) (k : Nat) (hk : ∃ d, Γ.get? k = some d)
    (sL : Survivor E n (declL :: Γ) (k + 1)) (sR : Survivor E n (declR :: Γ) (k + 1)) :
    BinderSpan E n (declL :: Γ) (declR :: Γ) (k + 1) :=
  let o := rootOwner hΓ k hk
  -- the provider at its own tail context, carried up to `Γ`
  have I : TyP E n (Γ.drop (k + 1)) o.sel.A (.sort o.sel.u) := by
    rw [RootOwner.drop_eq o]; exact o.sel.dom
  let Iw : TyP E n Γ (lift 0 (k + 1) o.sel.A) (.sort o.sel.u) :=
    TyP.wkDrop Γ (k + 1) (succ_le_length_of_get? hk) I
  have hlook : lookupType Γ k = some (lift 0 (k + 1) o.sel.A) := RootOwner.lookup o
  have hL : lookupType (declL :: Γ) (k + 1) = some (lift 0 1 (lift 0 (k + 1) o.sel.A)) := by
    rw [lookupType_cons_succ, hlook, Option.map_some']
  have hR : lookupType (declR :: Γ) (k + 1) = some (lift 0 1 (lift 0 (k + 1) o.sel.A)) := by
    rw [lookupType_cons_succ, hlook, Option.map_some']
  have hBL : sL.dom = lift 0 1 (lift 0 (k + 1) o.sel.A) :=
    Option.some.inj (sL.hlook.symm.trans hL)
  have hBR : sR.dom = lift 0 1 (lift 0 (k + 1) o.sel.A) :=
    Option.some.inj (sR.hlook.symm.trans hR)
  { BL := lift 0 1 (lift 0 (k + 1) o.sel.A), BR := lift 0 1 (lift 0 (k + 1) o.sel.A),
    hlookL := hL, hlookR := hR,
    uL := sL.u, JL := by rw [← hBL]; exact sL.rep,
    uR := sR.u, JR := by rw [← hBR]; exact sR.rep,
    w := o.sel.u,
    PL := TyP.wk E n Γ _ (.sort o.sel.u) declL 0 Iw,
    PR := TyP.wk E n Γ _ (.sort o.sel.u) declR 0 Iw }

/-- At a successor slot the two C legs read ONE subject: `BL = BR`. -/
theorem binderSpanSucc_subjects {E : ResolvedEnv} {n : Nat} {Γ : LCtx} (hΓ : CtxP E n Γ)
    (declL declR : LocalDecl) (k : Nat) (hk : ∃ d, Γ.get? k = some d)
    (sL : Survivor E n (declL :: Γ) (k + 1)) (sR : Survivor E n (declR :: Γ) (k + 1)) :
    (binderSpanSucc hΓ declL declR k hk sL sR).BL =
      (binderSpanSucc hΓ declL declR k hk sL sR).BR := rfl

end Rcic.Syn
