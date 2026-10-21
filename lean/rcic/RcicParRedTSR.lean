import rcic.RcicParRedT
import rcic.RcicPEqT

/-!
# RcicParRedTSR — S component: subject reduction for `ParRedT` by
extraction, with the `ht' ≺ hr` bound (S3, #6293; stacked on #6454 + #6479)

The S3 `S` component for the plain-side ATR mutual. `ParRedT` carries
both endpoint typings by construction (F-ParRedT-3: every arm's reduct
typing is an explicit premise except `conv`, which retargets through
`hasTyT_of_tyConvT`), so subject reduction is *extraction* — the S3
spec's `∃ T' (ht' : HasTyT b T'), rel T T' ∧ ht' ≺ hr` at `T' := T`,
`rel := PEq`-refl, because the index typing is in the relation, not
recovered after.

## `≺` — the concrete `dsize` (F-ι★-8)

`≺` is the strict `dsize` bound: `dsize` counts *judgment nodes*
(`HasTyT`/`ConvT`/`TyConvT`/`ParRedT`/`PEq` constructors only — payload
`Expr`s, `Level`s, `eq`-proofs and `DerivedIotaU` evidence contribute
nothing). These are the rank values F-ι★-8's `found` multiset is over:
`parRedT_sr`'s output satisfies `hasTyTSize ht' < parRedTSize pS hr`,
so a `dsize`-ranked foundation multiset can cite `ht'` inside `hr`'s
tree. The `PEq` leaf is abstract here — `pS` is the caller's node count
(F-ParRedT-7 stub; `peqTSize` instantiates it once `PEqT` lands) and
`hPEqLt` is the per-leaf bound it must satisfy.

## Why `conv` still closes

`conv`'s right typing is `hasTyT_of_tyConvT hb hc` — a fabricated wrap,
not a field. The bound still holds: each `TyConvT` node adds ≤ its own
`dsize` in output `.conv` nodes (`hasTyT_of_tyConvT_size`), and `hb`'s
bound comes from the recursive call on `h` — `hS hb + tcS hc <
1 + pRS h + tcS hc` follows from `hS hb < pRS h`.

No `sorry`, no new axiom.
-/

namespace Rcic.Declarative

universe u

variable {E : ResolvedEnv} {n : Nat}

/-! ## the `dsize` family — judgment-node counters -/

mutual

/-- `HasTyT` node count: every constructor contributes 1, judgment-typed
    fields contribute their own counts (payload contributes 0). -/
def hasTyTSize {Γ : LCtx} {e T : Expr Nat} : HasTyT E n Γ e T → Nat
  | .sort _ _ => 1
  | .bvar _ _ _ _ => 1
  | .const _ _ _ _ _ _ _ => 1
  | .pi _ _ _ _ _ hA hB => 1 + hasTyTSize hA + hasTyTSize hB
  | .lam _ _ _ _ _ hA hbody => 1 + hasTyTSize hA + hasTyTSize hbody
  | .app _ _ _ _ _ hf ha => 1 + hasTyTSize hf + hasTyTSize ha
  | .letE _ _ _ _ _ _ hA hv hb => 1 + hasTyTSize hA + hasTyTSize hv + hasTyTSize hb
  | .lit _ _ _ hexp => 1 + hasTyTSize hexp
  | .conv _ _ _ _ _ h hc => 1 + hasTyTSize h + convTSize hc

/-- `ConvT` node count. -/
def convTSize {Γ : LCtx} {a b T : Expr Nat} : ConvT E n Γ a b T → Nat
  | .refl _ _ _ h => 1 + hasTyTSize h
  | .symm _ _ _ _ h => 1 + convTSize h
  | .trans _ _ _ _ _ h1 h2 => 1 + convTSize h1 + convTSize h2
  | .beta _ _ _ _ _ _ hA hbody harg =>
      1 + hasTyTSize hA + hasTyTSize hbody + hasTyTSize harg
  | .zeta _ _ _ _ _ _ hA hv hb =>
      1 + hasTyTSize hA + hasTyTSize hv + hasTyTSize hb
  | .zetaLocal _ _ _ _ _ _ hv => 1 + hasTyTSize hv
  | .delta _ _ _ _ _ _ _ _ _ _ hb => 1 + hasTyTSize hb
  | .iota _ _ _ _ _ hlhs hrhs => 1 + hasTyTSize hlhs + hasTyTSize hrhs
  | .lit _ _ _ _ _ hexp => 1 + hasTyTSize hexp
  | .app _ _ _ _ _ _ _ h1 h2 => 1 + convTSize h1 + convTSize h2
  | .lam _ _ _ _ _ _ _ hA hb => 1 + convTSize hA + convTSize hb
  | .pi _ _ _ _ _ _ _ hA hB => 1 + convTSize hA + convTSize hB
  | .letE _ _ _ _ _ _ _ _ _ hA hv hb =>
      1 + convTSize hA + convTSize hv + convTSize hb
  | .sorts _ _ _ _ => 1
  | .consts _ _ _ _ _ _ _ _ _ _ => 1
  | .eta _ _ _ _ h => 1 + hasTyTSize h
  | .irr _ _ _ _ hP hp hq => 1 + hasTyTSize hP + hasTyTSize hp + hasTyTSize hq
  | .tyConv _ _ _ _ _ _ h hA => 1 + convTSize h + convTSize hA

/-- `TyConvT` node count. -/
def tyConvTSize {Γ : LCtx} {A B : Expr Nat} : TyConvT E n Γ A B → Nat
  | .refl _ _ => 1
  | .of _ _ _ _ h => 1 + convTSize h
  | .trans _ _ _ _ h1 h2 => 1 + tyConvTSize h1 + tyConvTSize h2

end

/-- `ParRedT` node count, parameterized by the abstract `PEq` leaf's
    count `pS` (the leaf relation is a module parameter — F-ParRedT-7;
    `PEqT`'s `peqTSize` instantiates it). -/
def parRedTSize {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    (pS : ∀ {Γ : LCtx} {p q T : Expr Nat}, PEq Γ p q T → Nat)
    {Γ : LCtx} {a b T : Expr Nat} : ParRedT PEq E n Γ a b T → Nat
  | .refl _ _ _ h => 1 + hasTyTSize h
  | .sortEq _ _ _ _ _ hl hr => 1 + hasTyTSize hl + hasTyTSize hr
  | .consts _ _ _ _ _ _ hl hr => 1 + hasTyTSize hl + hasTyTSize hr
  | .bvarZeta _ _ _ _ _ _ _ hv hl hr =>
      1 + parRedTSize pS hv + hasTyTSize hl + hasTyTSize hr
  | .delta _ _ _ _ _ _ _ _ _ _ _ hl hr => 1 + hasTyTSize hl + hasTyTSize hr
  | .app _ _ _ _ _ _ _ _ _ _ hf hc hB hTy ha hr =>
      1 + parRedTSize pS hf + tyConvTSize hc + hasTyTSize hB +
        hasTyTSize hTy + parRedTSize pS ha + hasTyTSize hr
  | .beta _ _ _ _ _ _ _ _ _ _ hA hB hTy hb ha hred =>
      1 + hasTyTSize hA + hasTyTSize hB + hasTyTSize hTy +
        parRedTSize pS hb + parRedTSize pS ha + hasTyTSize hred
  | .lam _ _ _ _ _ _ _ _ hc hA hB hb hrt =>
      1 + convTSize hc + hasTyTSize hA + hasTyTSize hB +
        parRedTSize pS hb + hasTyTSize hrt
  | .pi _ _ _ _ _ _ _ hA hc hB hcB hrt =>
      1 + hasTyTSize hA + convTSize hc + hasTyTSize hB +
        convTSize hcB + hasTyTSize hrt
  | .letE _ _ _ _ _ _ _ _ _ _ hc hA hv hB hTy hb hrt =>
      1 + convTSize hc + hasTyTSize hA + parRedTSize pS hv +
        hasTyTSize hB + hasTyTSize hTy + parRedTSize pS hb +
        hasTyTSize hrt
  | .zeta _ _ _ _ _ _ _ _ _ hA hv hB hTy hb hred =>
      1 + hasTyTSize hA + parRedTSize pS hv + hasTyTSize hB +
        hasTyTSize hTy + parRedTSize pS hb + hasTyTSize hred
  | .iotaSpine _ _ _ _ _ hstep _ hred hrhs =>
      1 + parRedTSize pS hstep + hasTyTSize hred + hasTyTSize hrhs
  | .iotaStarK _ _ _ _ _ _ _ _ _ _ _ hmajor hmk hTm0 _ hlι hlhs hrhs =>
      1 + hasTyTSize hmajor + hasTyTSize hmk + hasTyTSize hTm0 +
        hasTyTSize hlι + hasTyTSize hlhs + hasTyTSize hrhs
  | .iotaStarKEta _ _ _ _ _ _ _ _ _ _ _ hA hf _ _ _ hmajor hmk hTm0 _ hlι hlhs hrhs =>
      1 + hasTyTSize hA + hasTyTSize hf + hasTyTSize hmajor + hasTyTSize hmk +
        hasTyTSize hTm0 + hasTyTSize hlι + hasTyTSize hlhs + hasTyTSize hrhs
  | .lit _ _ _ hexp => 1 + hasTyTSize hexp
  | .eta _ _ _ _ _ hf hl => 1 + parRedTSize pS hf + hasTyTSize hl
  | .peq _ _ _ _ h => 1 + pS h
  | .conv _ _ _ _ _ h hc => 1 + parRedTSize pS h + tyConvTSize hc

private theorem hasTyTSize_pos {Γ : LCtx} {e T : Expr Nat}
    (h : HasTyT E n Γ e T) : 0 < hasTyTSize h := by
  cases h <;> simp [hasTyTSize] <;> omega

/-! ## the `hasTyT_of_tyConvT` bound -/

/-- Retyping through `TyConvT` adds at most the conversion's own node
    count: `.refl` adds 0, `.of` adds exactly 1 `.conv` node, `.trans`
    adds the two legs' — `hS out ≤ hS hb + tcS hc`. -/
def hasTyT_of_tyConvT_size {Γ : LCtx} {b A A' : Expr Nat}
    (hb : HasTyT E n Γ b A) (hc : TyConvT E n Γ A A') :
    hasTyTSize (hasTyT_of_tyConvT hb hc) ≤ hasTyTSize hb + tyConvTSize hc :=
  match hc with
  | .refl _ _ => Nat.le_add_right _ _
  | .of _ _ _ _ hcv => by
      simp only [tyConvTSize, hasTyT_of_tyConvT, hasTyTSize]; omega
  | .trans _ _ _ _ h1 h2 => by
      have i1 := hasTyT_of_tyConvT_size hb h1
      have i2 := hasTyT_of_tyConvT_size (hasTyT_of_tyConvT hb h1) h2
      simp only [tyConvTSize, hasTyT_of_tyConvT] at *
      omega

/-! ## S — the right endpoint by extraction, with `ht' ≺ hr` -/

/-- **S component**: subject reduction for `ParRedT` by extraction.
    The output typing is a carried premise in fifteen of sixteen arms
    (`conv` retargets through `hasTyT_of_tyConvT`, still bounded), so
    the returned `ht' : HasTyT E n Γ b T` satisfies the strict
    `dsize`-bound `hasTyTSize ht' < parRedTSize pS hr` — F-ι★-8's `≺`.

    `hPEq` is the leaf's endpoint evidence (`parRedT_typed`'s hypothesis,
    verbatim); `hPEqLt` is its node bound — both stay hypotheses until
    `PEqT` lands and supplies them. -/
def parRedT_sr {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    (pS : ∀ {Γ : LCtx} {p q T : Expr Nat}, PEq Γ p q T → Nat)
    (hPEq : ∀ {Γ : LCtx} {p q T : Expr Nat},
      PEq Γ p q T → HasTyT E n Γ p T × HasTyT E n Γ q T)
    (hPEqLt : ∀ {Γ : LCtx} {p q T : Expr Nat} (h : PEq Γ p q T),
      hasTyTSize (hPEq h).2 < pS h)
    {Γ : LCtx} {a b T : Expr Nat} (hr : ParRedT PEq E n Γ a b T) :
    Σ' ht' : HasTyT E n Γ b T, hasTyTSize ht' < parRedTSize pS hr := by
  match hr with
  | .refl _ _ _ h => exact ⟨h, by simp only [parRedTSize]; omega⟩
  | .sortEq _ _ _ _ _ _ hr => exact ⟨hr, by simp only [parRedTSize]; omega⟩
  | .consts _ _ _ _ _ _ _ hr => exact ⟨hr, by simp only [parRedTSize]; omega⟩
  | .bvarZeta _ _ _ _ _ _ _ _ _ hr => exact ⟨hr, by simp only [parRedTSize]; omega⟩
  | .delta _ _ _ _ _ _ _ _ _ _ _ _ hr => exact ⟨hr, by simp only [parRedTSize]; omega⟩
  | .app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr => exact ⟨hr, by simp only [parRedTSize]; omega⟩
  | .beta _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hred => exact ⟨hred, by simp only [parRedTSize]; omega⟩
  | .lam _ _ _ _ _ _ _ _ _ _ _ _ hrt => exact ⟨hrt, by simp only [parRedTSize]; omega⟩
  | .pi _ _ _ _ _ _ _ _ _ _ _ hrt => exact ⟨hrt, by simp only [parRedTSize]; omega⟩
  | .letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrt => exact ⟨hrt, by simp only [parRedTSize]; omega⟩
  | .zeta _ _ _ _ _ _ _ _ _ _ _ _ _ _ hred => exact ⟨hred, by simp only [parRedTSize]; omega⟩
  | .iotaSpine _ _ _ _ _ _ _ _ hrhs => exact ⟨hrhs, by simp only [parRedTSize]; omega⟩
  | .iotaStarK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrhs =>
      exact ⟨hrhs, by simp only [parRedTSize]; omega⟩
  | .iotaStarKEta Γ _ _ A B _ rhs u _ _ _ hA hf _ _ _ _ _ _ _ _ _ hrhs =>
      exact ⟨.lam Γ A u rhs B hA hrhs, by
        have := hasTyTSize_pos hf
        simp only [parRedTSize, hasTyTSize]; omega⟩
  | .lit _ _ _ hexp => exact ⟨hexp, by simp only [parRedTSize]; omega⟩
  | .eta _ _ _ _ _ hf _ =>
      -- reduct typing is `f'`'s — the recursive call on `hf`
      have ⟨ht', ht'Lt⟩ := parRedT_sr pS hPEq hPEqLt hf
      exact ⟨ht', by simp only [parRedTSize]; omega⟩
  | .peq _ _ _ _ h =>
      exact ⟨(hPEq h).2, by
        simp only [parRedTSize]; exact
          Nat.lt_of_lt_of_le (hPEqLt h) (Nat.le_add_left _ _)⟩
  | .conv _ _ _ _ _ h hc =>
      have ⟨hb, hbLt⟩ := parRedT_sr pS hPEq hPEqLt h
      exact ⟨hasTyT_of_tyConvT hb hc, by
        have := hasTyT_of_tyConvT_size hb hc
        simp only [parRedTSize]; omega⟩

/-- the extracted typing, projected. -/
def parRedT_sr_val {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    (pS : ∀ {Γ : LCtx} {p q T : Expr Nat}, PEq Γ p q T → Nat)
    (hPEq : ∀ {Γ : LCtx} {p q T : Expr Nat},
      PEq Γ p q T → HasTyT E n Γ p T × HasTyT E n Γ q T)
    (hPEqLt : ∀ {Γ : LCtx} {p q T : Expr Nat} (h : PEq Γ p q T),
      hasTyTSize (hPEq h).2 < pS h)
    {Γ : LCtx} {a b T : Expr Nat} (hr : ParRedT PEq E n Γ a b T) :
    HasTyT E n Γ b T :=
  (parRedT_sr pS hPEq hPEqLt hr).1

/-- the `ht' ≺ hr` bound, projected. -/
def parRedT_sr_lt {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}
    (pS : ∀ {Γ : LCtx} {p q T : Expr Nat}, PEq Γ p q T → Nat)
    (hPEq : ∀ {Γ : LCtx} {p q T : Expr Nat},
      PEq Γ p q T → HasTyT E n Γ p T × HasTyT E n Γ q T)
    (hPEqLt : ∀ {Γ : LCtx} {p q T : Expr Nat} (h : PEq Γ p q T),
      hasTyTSize (hPEq h).2 < pS h)
    {Γ : LCtx} {a b T : Expr Nat} (hr : ParRedT PEq E n Γ a b T) :
    hasTyTSize (parRedT_sr_val pS hPEq hPEqLt hr) < parRedTSize pS hr :=
  (parRedT_sr pS hPEq hPEqLt hr).2

/-! ## the `PEqT` instantiation — F-ParRedT-7 discharged (LAND)

`PEqT` is on main, so the abstract leaf instantiates. `PEqT` alone gives
`p : P`, `q : Q` at the leaf's own proposition indices — never `p : T` /
`q : T` at the arm's `T`. The endpoint typings are therefore part of the
leaf's contract: `PEqLeafT` bundles `≈P` with both `HasTyT`s at `T`, so
`hPEq` is a projection and `hPEqLt` falls out of the node count. The
caller's remaining obligation is supplying `p : T`, `q : T` when it
builds the `peq` arm — the `irr`-arm discharge plus P's index
reconciliation, not a size-level fact. -/

/-- `PEqT` node count — the leaf pool `parRedTSize` consumes. The
    `proof` leaf counts its four `HasTyT` premises. -/
def peqTSize : {Γ : LCtx} → {a b : Expr Nat} → PEqT E n Γ a b → Nat
  | _, _, _, .bvar _ _ => 1
  | _, _, _, .sort _ _ _ _ => 1
  | _, _, _, .const _ _ _ _ _ => 1
  | _, _, _, .app _ _ _ _ _ hf ha => 1 + peqTSize hf + peqTSize ha
  | _, _, _, .lam _ _ _ _ _ hA hb => 1 + peqTSize hA + peqTSize hb
  | _, _, _, .pi _ _ _ _ _ hA hB => 1 + peqTSize hA + peqTSize hB
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb =>
      1 + peqTSize hA + peqTSize hv + peqTSize hb
  | _, _, _, .lit _ _ => 1
  | _, _, _, .proof _ _ _ _ _ hP hQ hp hq =>
      1 + hasTyTSize hP + hasTyTSize hQ + hasTyTSize hp + hasTyTSize hq

/-- The instantiated `peq` leaf: `≈P` bundled with both endpoint typings
    at the arm's `T`. -/
def PEqLeafT (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (p q T : Expr Nat) :
    Type :=
  PEqT E n Γ p q ×' (HasTyT E n Γ p T ×' HasTyT E n Γ q T)

/-- `PEqLeafT` node count: the `≈P` plus the two carried typings. -/
def peqLeafTSize {Γ : LCtx} {p q T : Expr Nat} (h : PEqLeafT E n Γ p q T) :
    Nat :=
  1 + peqTSize h.1 + hasTyTSize h.2.1 + hasTyTSize h.2.2

/-- **S, instantiated at `PEqT`**: the endpoint evidence is the bundled
    projection, the bound is by the size count — no `hPEq`/`hPEqLt`
    hypotheses remain. -/
def parRedT_sr_peqT {Γ : LCtx} {a b T : Expr Nat}
    (hr : ParRedT (PEqLeafT E n) E n Γ a b T) :
    Σ' ht' : HasTyT E n Γ b T,
      hasTyTSize ht' < parRedTSize (fun h => peqLeafTSize h) hr :=
  parRedT_sr (fun h => peqLeafTSize h)
    (fun h => ⟨h.2.1, h.2.2⟩)
    (fun h => by simp only [peqLeafTSize]; omega) hr

/-- the extracted typing, projected (instantiated). -/
def parRedT_sr_peqT_val {Γ : LCtx} {a b T : Expr Nat}
    (hr : ParRedT (PEqLeafT E n) E n Γ a b T) : HasTyT E n Γ b T :=
  (parRedT_sr_peqT hr).1

/-- the `ht' ≺ hr` bound, projected (instantiated). -/
def parRedT_sr_peqT_lt {Γ : LCtx} {a b T : Expr Nat}
    (hr : ParRedT (PEqLeafT E n) E n Γ a b T) :
    hasTyTSize (parRedT_sr_peqT hr).1 <
      parRedTSize (fun h => peqLeafTSize h) hr :=
  (parRedT_sr_peqT hr).2

#print axioms Rcic.Declarative.parRedT_sr
#print axioms Rcic.Declarative.parRedT_sr_val
#print axioms Rcic.Declarative.parRedT_sr_lt
#print axioms Rcic.Declarative.hasTyT_of_tyConvT_size
#print axioms Rcic.Declarative.peqTSize
#print axioms Rcic.Declarative.parRedT_sr_peqT

end Rcic.Declarative
