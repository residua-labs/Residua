import rcic.RcicSynWalk

/-!
# RcicSynPiInv — Π-generation on an enriched typing (step 3r)

S3 §12. `piInv` reads a typing of `.pi A B` as a domain typing and a
codomain typing. The recursion is structural on the derivation, with the
term equation as a premise, in the shape of `TyP.reg`. A call through
`piHead` is not that recursion: the view's `inner` is not a subterm.

The result is at the outer environment. An `ewk` node composes `EnvExt`.
A premise copied out of an inner derivation is wrapped in `TyP.ewk`.

The codomain of a `cctx` is not one `TyP.cctx`: the converted binder sits
at position 1. `tyCctxAt` is `tyAt` of the empty pack (`FuelRel.nil`,
`EsInv.nil`, `Run.nil`). `FuelRel.nil` is the empty skeleton at the same
level bound, which is the level `cctx` keeps. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

variable {E : ResolvedEnv}

/-- The two components of a Π, at the conclusion context. -/
structure PiGen (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (A B : Expr Nat) : Type where
  u : Level
  v : Level
  hA : TyP E n Γ A (.sort u)
  hB : TyP E n (.assumption A :: Γ) B (.sort v)

theorem hget_succ {Γ : LCtx} {j : Nat} {t : Expr Nat} {d : LocalDecl}
    (h : Γ[j]? = some (.assumption t)) :
    (d :: Γ)[j + 1]? = some (.assumption t) := by
  have hg : Γ.get? j = some (.assumption t) :=
    (List.get?_eq_getElem? Γ j).symm ▸ h
  exact List.get?_eq_getElem? (d :: Γ) (j + 1) ▸
    get?_cons_succ_assumption (d := d) hg

theorem hget_succ_let {Γ : LCtx} {j : Nat} {t v : Expr Nat} {d : LocalDecl}
    (h : Γ[j]? = some (.letBinding t v)) :
    (d :: Γ)[j + 1]? = some (.letBinding t v) := by
  have hg : Γ.get? j = some (.letBinding t v) :=
    (List.get?_eq_getElem? Γ j).symm ▸ h
  exact List.get?_eq_getElem? (d :: Γ) (j + 1) ▸
    get?_cons_succ_let (d := d) hg

theorem substRemove_cod (v : Expr Nat) (j : Nat) (A₀ : Expr Nat) (Γ₀ : LCtx) :
    substRemove v (j + 1) (.assumption A₀ :: Γ₀) =
      .assumption (instantiate j (lift 0 j v) A₀) :: substRemove v j Γ₀ := by
  rw [substRemove_succ_cons]
  rfl

theorem substRemove_cod_eq (v : Expr Nat) (j : Nat) (A₀ A : Expr Nat) (Γ₀ : LCtx)
    (hAe : instantiate j (lift 0 j v) A₀ = A) :
    substRemove v (j + 1) (.assumption A₀ :: Γ₀) =
      .assumption A :: substRemove v j Γ₀ := by
  rw [substRemove_cod, hAe]

theorem instantiate_succ_merge (j : Nat) (repl B₀ B : Expr Nat)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) B₀ = B) :
    instantiate (j + 1) (lift 0 (j + 1) repl) B₀ = B := by
  rw [← lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) repl]
  exact hBe

theorem get?_one_assumption (A Dom : Expr Nat) (Γ : LCtx) :
    (.assumption A :: .assumption Dom :: Γ).get? 1 = some (.assumption Dom) := by
  rw [List.get?_cons_succ]
  rfl

theorem setAssump_one (A Dom' Dom : Expr Nat) (Γ : LCtx) :
    setAssump 1 Dom' (.assumption A :: .assumption Dom :: Γ) =
      .assumption A :: .assumption Dom' :: Γ := by
  rw [setAssump_succ, setAssump_zero]

/-- Empty skeleton. `FuelRel.nil` is this level bound, so `nIn = n`. -/
def packNil {n k : Nat} {Dom Dom' : Expr Nat} {uSlot : Level} {Γ : LCtx}
    (hget : Γ.get? k = some (.assumption Dom))
    (hslot : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort uSlot)) :
    Pack E n k Dom Dom' uSlot n [] Γ where
  fuel := .nil
  inv := .nil
  run := .nil
  get := hget
  slot := hslot

/-- Replace the assumption at `k`, leaving the term and the ascribed type.
    The skeleton is empty, so this is `tyAt` at `FuelRel.nil`. -/
def tyCctxAt {Ei : ResolvedEnv} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (hext : EnvExt Ei E) {n : Nat} {Γ : LCtx} {k : Nat}
    {Dom Dom' : Expr Nat} {uSlot : Level} {e T : Expr Nat}
    (hget : Γ.get? k = some (.assumption Dom))
    (hslot : CvP E n (Γ.drop (k + 1)) Dom Dom' (.sort uSlot))
    (D : TyP Ei n Γ e T) :
    TyP E n (setAssump k Dom' Γ) e T :=
  tyAt (nIn := n) (ss := []) hW ι ιenv hext (packNil hget hslot) D

def piWk {n : Nat} {Γ₀ : LCtx} {A₀ B₀ : Expr Nat}
    (d : LocalDecl) (c : Nat) (R : PiGen E n Γ₀ A₀ B₀)
    {A B : Expr Nat} (hAe : lift c 1 A₀ = A) (hBe : lift (c + 1) 1 B₀ = B) :
    PiGen E n (insertAt d c Γ₀) A B :=
  let dom := tyCast hAe rfl (TyP.wk E n Γ₀ A₀ (.sort R.u) d c R.hA)
  let cod0 := TyP.wk E n (.assumption A₀ :: Γ₀) B₀ (.sort R.v) d (c + 1) R.hB
  let cod1 := tyCast hBe rfl cod0
  let cod := tyCastCtx (congrArg (fun X => .assumption X :: insertAt d c Γ₀) hAe) cod1
  ⟨R.u, R.v, dom, cod⟩

def piLinst {a n : Nat} {Γ₀ : LCtx} {A₀ B₀ : Expr Nat} (ls : List Level)
    (hls : levelsBounded n ls = true) (hlen : ls.length = a)
    (R : PiGen E a Γ₀ A₀ B₀) {A B : Expr Nat}
    (hAe : instantiateLevels ls A₀ = A) (hBe : instantiateLevels ls B₀ = B) :
    PiGen E n (instLvlsCtx ls Γ₀) A B :=
  let dom := tyCast hAe rfl
    (TyP.linst E a n Γ₀ A₀ (.sort R.u) ls hls hlen R.hA)
  let cod0 := TyP.linst E a n (.assumption A₀ :: Γ₀) B₀ (.sort R.v) ls hls hlen R.hB
  let cod1 := tyCast hBe rfl cod0
  let cod := tyCastCtx
    (congrArg (fun X => .assumption X :: instLvlsCtx ls Γ₀) hAe) cod1
  ⟨instLevel ls R.u, instLevel ls R.v, dom, cod⟩

def piEsub {n : Nat} {Γ₀ : LCtx} {A₀ B₀ : Expr Nat}
    (t repl : Expr Nat) (j : Nat) (uE : Level)
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    (R : PiGen E n Γ₀ A₀ B₀) {A B : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) B₀ = B) :
    PiGen E n (substRemove repl j Γ₀) A B :=
  let Γ := substRemove repl j Γ₀
  let dom := tyCast hAe rfl
    (TyP.esub E n Γ₀ A₀ (.sort R.u) t repl j uE R.hA hget hv hvT)
  let hctx := (substRemove_cod_eq repl j A₀ A Γ₀ hAe).symm
  let hv1 := TyP.wk E n Γ (lift 0 j repl) (lift 0 j t) (.assumption A) 0 hv
  let hv2 := tyCast
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) repl)
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) t)
    hv1
  let hv3 := tyCastCtx hctx hv2
  let hvT1 := TyP.wk E n Γ (lift 0 j t) (.sort uE) (.assumption A) 0 hvT
  let hvT2 := tyCast
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) t) rfl hvT1
  let hvT3 := tyCastCtx hctx hvT2
  let hget' := hget_succ (d := .assumption A₀) hget
  let cod0 := TyP.esub E n (.assumption A₀ :: Γ₀) B₀ (.sort R.v) t repl (j + 1) uE
    R.hB hget' hv3 hvT3
  let cod1 := tyCast (instantiate_succ_merge j repl B₀ B hBe) rfl cod0
  let cod := tyCastCtx (substRemove_cod_eq repl j A₀ A Γ₀ hAe) cod1
  ⟨R.u, R.v, dom, cod⟩

def piLsub {n : Nat} {Γ₀ : LCtx} {A₀ B₀ : Expr Nat}
    (t repl : Expr Nat) (j : Nat) (uE : Level)
    (hget : Γ₀[j]? = some (.letBinding t repl))
    (hv : TyP E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t))
    (hvT : TyP E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE))
    (R : PiGen E n Γ₀ A₀ B₀) {A B : Expr Nat}
    (hAe : instantiate j (lift 0 j repl) A₀ = A)
    (hBe : instantiate (j + 1) (lift 0 1 (lift 0 j repl)) B₀ = B) :
    PiGen E n (substRemove repl j Γ₀) A B :=
  let Γ := substRemove repl j Γ₀
  let dom := tyCast hAe rfl
    (TyP.lsub E n Γ₀ A₀ (.sort R.u) t repl j uE R.hA hget hv hvT)
  let hctx := (substRemove_cod_eq repl j A₀ A Γ₀ hAe).symm
  let hv1 := TyP.wk E n Γ (lift 0 j repl) (lift 0 j t) (.assumption A) 0 hv
  let hv2 := tyCast
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) repl)
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) t)
    hv1
  let hv3 := tyCastCtx hctx hv2
  let hvT1 := TyP.wk E n Γ (lift 0 j t) (.sort uE) (.assumption A) 0 hvT
  let hvT2 := tyCast
    (lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) t) rfl hvT1
  let hvT3 := tyCastCtx hctx hvT2
  let hget' := hget_succ_let (d := .assumption A₀) hget
  let cod0 := TyP.lsub E n (.assumption A₀ :: Γ₀) B₀ (.sort R.v) t repl (j + 1) uE
    R.hB hget' hv3 hvT3
  let cod1 := tyCast (instantiate_succ_merge j repl B₀ B hBe) rfl cod0
  let cod := tyCastCtx (substRemove_cod_eq repl j A₀ A Γ₀ hAe) cod1
  ⟨R.u, R.v, dom, cod⟩

def piCctx (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    {n : Nat} {Γtail : LCtx} {A B Dom Dom' : Expr Nat} {uDom : Level}
    (R : PiGen E n (.assumption Dom :: Γtail) A B)
    (hDom : CvP E n Γtail Dom Dom' (.sort uDom)) :
    PiGen E n (.assumption Dom' :: Γtail) A B :=
  let dom := TyP.cctx E n Γtail A (.sort R.u) Dom Dom' uDom R.hA hDom
  let cod0 := tyCctxAt (Ei := E) hW ι ιenv (envExt_refl E)
    (get?_one_assumption A Dom Γtail) hDom R.hB
  let cod := tyCastCtx (setAssump_one A Dom' Dom Γtail) cod0
  ⟨R.u, R.v, dom, cod⟩

/-- Π-generation. `he` is the term equation. Impossible constructors are
    a different head, so the equation is empty. -/
def piInv {Ei : ResolvedEnv} (hW : CvWalkHyp E) (ι : IotaPack E)
    (ιenv : ∀ {E₀ : ResolvedEnv} {lhs rhs : Expr Nat},
      EnvExt E₀ E → DerivedIota E₀ lhs rhs → DerivedIota E lhs rhs)
    (hext : EnvExt Ei E) :
    {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP Ei n Γ e T → {A B : Expr Nat} → e = .pi A B → PiGen E n Γ A B
  | _, _, _, _, .sort .., _, _, he => by cases he
  | _, _, _, _, .bvar .., _, _, he => by cases he
  | _, _, _, _, .const .., _, _, he => by cases he
  | n, Γ, _, _, .pi _ _ _ A₀ u B₀ v hA hB, _, _, he => by
      cases he
      exact PiGen.mk u v
        (TyP.ewk Ei E n Γ A₀ (.sort u) hext hA)
        (TyP.ewk Ei E n (.assumption A₀ :: Γ) B₀ (.sort v) hext hB)
  | _, _, _, _, .lam .., _, _, he => by cases he
  | _, _, _, _, .app .., _, _, he => by cases he
  | _, _, _, _, .letE .., _, _, he => by cases he
  | _, _, _, _, .lit .., _, _, he => by cases he
  | _, _, _, _, .conv _ _ _ _ _ _ _ h _, A, B, he =>
      piInv hW ι ιenv hext h he
  | _, _, _, _, .wk _ _ _ _ _ d c inner, _, _, he =>
      match lift_eq_pi he with
      | .mk _ _ he₀ hAe hBe =>
          piWk d c (piInv hW ι ιenv hext inner he₀) hAe hBe
  | n, _, _, _, .esub _ _ Γ₀ _ _ t repl j uE inner hget hv hvT, _, _, he =>
      match instantiate_eq_pi he with
      | .under _ _ he₀ hAe hBe =>
          piEsub t repl j uE hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT)
            (piInv hW ι ιenv hext inner he₀) hAe hBe
      | .here _ hr =>
          piInv hW ι ιenv hext hv hr
  | n, _, _, _, .lsub _ _ Γ₀ _ _ t repl j uE inner hget hv hvT, _, _, he =>
      match instantiate_eq_pi he with
      | .under _ _ he₀ hAe hBe =>
          piLsub t repl j uE hget
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j repl) (lift 0 j t) hext hv)
            (TyP.ewk Ei E n (substRemove repl j Γ₀) (lift 0 j t) (.sort uE) hext hvT)
            (piInv hW ι ιenv hext inner he₀) hAe hBe
      | .here _ hr =>
          piInv hW ι ιenv hext hv hr
  | _, _, _, _, .linst _ _ _ _ _ _ ls hls hlen inner, _, _, he =>
      match instantiateLevels_eq_pi he with
      | .mk _ _ he₀ hAe hBe =>
          piLinst ls hls hlen (piInv hW ι ιenv hext inner he₀) hAe hBe
  | _, _, _, _, .ewk E₀ _ _ _ _ _ hext' inner, _, _, he =>
      piInv hW ι ιenv (envExt_trans hext' hext) inner he
  | _, _, _, _, .cctx _ _ Γtail _ _ Dom Dom' uDom inner hDom, _, _, he =>
      piCctx hW ι ιenv
        (piInv hW ι ιenv hext inner he)
        (CvP.ewk Ei E _ Γtail Dom Dom' (.sort uDom) hext hDom)

#print axioms hget_succ
#print axioms substRemove_cod
#print axioms substRemove_cod_eq
#print axioms instantiate_succ_merge
#print axioms get?_one_assumption
#print axioms setAssump_one
#print axioms packNil
#print axioms tyCctxAt
#print axioms piWk
#print axioms piLinst
#print axioms piEsub
#print axioms piCctx
#print axioms piInv

end Rcic.Syn
