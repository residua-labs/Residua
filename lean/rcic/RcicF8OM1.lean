import Lean
import rcic.RcicF8EvInv
import rcic.RcicPEqLeafTIntro

/-!
# `RcicF8OM1` — piRow O-M1 + the U→U edge of O-M3(b), intro-spine fragment

O-M1 (S2 §2): a U-processor's output cites only sub-derivations of its
inputs, measured by `EvTc.leaves` against the inputs' `EvTy.leaves` —
`OM1 U` is that statement for an arbitrary `U : UProc R`.

The currently checkable built-U fragment is the intro-spine uniqueness
process `introTypeSpine_unique` (`RcicPEqLeafTIntro`, private aux
`introTypeSpineUniqueAux`), re-expressed on provenance as `introU`: the
first input stays a certified literal `HasTyT` (the recursion is on it,
exactly as in the plain aux), the second input is lit-rooted provenance
inverted with B3a's `EvTy.inv*` — no judgment is ever materialized.
`introU_OM1` proves the fragment satisfies `OM1`; `introU_edge_*`
witness the U→U edge of O-M3(b) (S2 §4): each recursive arm's new
argument multiset is a `DMStep` below the caller's.

The `app` case of a general U waits for X and is a contract (B4b);
`introU`'s `.app` arm is excluded by `introTypeSpine`.  `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-- a U-processor: two provenance typings of the same subject yield a
    provenance conversion between their types. -/
abbrev UProc (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {a A B : Expr Nat}, EvTy R Γ a A → EvTy R Γ a B → EvTc R Γ A B

/-- O-M1: U's output cites only sub-derivations of its inputs. -/
def OM1 {R : List (Jd E n)} (U : UProc R) : Prop :=
  ∀ {Γ : LCtx} {a A B : Expr Nat} (l : EvTy R Γ a A) (r : EvTy R Γ a B),
    ∀ ℓ ∈ (U l r).leaves, ∃ ℓ' ∈ l.leaves ++ r.leaves, SubEq ℓ ℓ'

/-! ### index casts

Inversion pieces arrive at index values proved equal to what the arm
needs (`bvar`'s looked-up type, `letE`'s `lift 0 0` casts); a cast keeps
the transport out of the `Ev` structure so `.leaves` still computes. -/

/-- index cast for provenance typings. -/
def EvTy.cast {Γ Γ' : LCtx} {e e' T T' : Expr Nat} (hΓ : Γ = Γ')
    (he : e = e') (hT : T = T') (D : EvTy R Γ e T) : EvTy R Γ' e' T' := by
  subst hΓ; subst he; subst hT; exact D

/-- index cast for provenance conversions. -/
def EvTc.cast {Γ Γ' : LCtx} {A A' B B' : Expr Nat} (hΓ : Γ = Γ')
    (hA : A = A') (hB : B = B') (c : EvTc R Γ A B) : EvTc R Γ' A' B' := by
  subst hΓ; subst hA; subst hB; exact c

/-- leaves are cast-invariant. -/
theorem EvTy.cast_leaves {Γ Γ' : LCtx} {e e' T T' : Expr Nat}
    (hΓ : Γ = Γ') (he : e = e') (hT : T = T') (D : EvTy R Γ e T) :
    (D.cast hΓ he hT).leaves = D.leaves := by
  subst hΓ; subst he; subst hT; rfl

/-- leaves are cast-invariant. -/
theorem EvTc.cast_leaves {Γ Γ' : LCtx} {A A' B B' : Expr Nat}
    (hΓ : Γ = Γ') (hA : A = A') (hB : B = B') (c : EvTc R Γ A B) :
    (EvTc.cast hΓ hA hB c).leaves = c.leaves := by
  subst hΓ; subst hA; subst hB; rfl

/-! ### inverted body pieces stay lit-rooted

`introU`'s recursive calls consume `pieces.hb`, which is always a
`lit` (under no wrapper) — at a `.conv` the aux recurses into the
premise with the SAME certificate term `invLamAux`/`invLetEAux` built
(`certOfChild (convChildFst h hc) hsub`, now public), so the recursion
below matches by definitional equality. -/

private def invLamHbLit {A body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (hsub : ∃ r ∈ R, SubEq (.ty d) r) → (heq : e = .lam A body) →
    ((EvTy.lit d hsub).invLam rfl heq).hb.litRooted = true
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => by
      injection heq with h1 h2
      subst h1; subst h2
      rfl
  | _, _, _, .conv _ _ _ _ _ h hc, hsub, heq =>
      invLamHbLit h (certOfChild (convChildFst h hc) hsub) heq
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

private def invLetEHbLit {A value body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (d : HasTyT E n Γ e T) →
    (hsub : ∃ r ∈ R, SubEq (.ty d) r) → (heq : e = .letE A value body) →
    ((EvTy.lit d hsub).invLetE rfl heq).hb.litRooted = true
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, _, heq => by
      injection heq with h1 h2 h3
      subst h1; subst h2; subst h3
      rfl
  | _, _, _, .conv _ _ _ _ _ h hc, hsub, heq =>
      invLetEHbLit h (certOfChild (convChildFst h hc) hsub) heq
  | _, _, _, .sort _ _, _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq => nomatch heq

/-- the `.hb` field of a `lam` inversion is itself lit-rooted. -/
def EvTy.invLam_hb_litRooted {A body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .lam A body) →
    (D.invLam hD heq).hb.litRooted = true
  | _, _, _, .lit d hsub, _, heq => invLamHbLit d hsub heq
  | _, _, _, .rety D _, hD, heq => D.invLam_hb_litRooted hD heq
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-- the `.hb` field of a `letE` inversion is itself lit-rooted. -/
def EvTy.invLetE_hb_litRooted {A value body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .letE A value body) →
    (D.invLetE hD heq).hb.litRooted = true
  | _, _, _, .lit d hsub, _, heq => invLetEHbLit d hsub heq
  | _, _, _, .rety D _, hD, heq => D.invLetE_hb_litRooted hD heq
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-! ### inverted body pieces are strictly below the input's leaves

Needed for the U→U edge: the recursive arm's second argument is a
strict piece of `r`, not `r` itself. -/

/-- every leaf of a `lam` inversion's `.hb` is a strict sub-derivation
    of a leaf of the (lit-rooted) input. -/
def EvTy.invLam_hb_strictRooted {A body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .lam A body) →
    ∀ ℓ ∈ (D.invLam hD heq).hb.leaves, ∃ ℓ' ∈ D.leaves, SubOf ℓ ℓ'
  | _, _, _, .lit d hsub, _, heq => fun ℓ hℓ =>
      ⟨.ty d, by
        show (Jd.ty d : Jd E n) ∈ ([Jd.ty d] : List (Jd E n))
        exact .head _,
        EvTy.invLam_strict d hsub heq ℓ (by
          simp only [EvInvLam.leaves, List.mem_append, or_assoc]
          exact .inr (.inl hℓ))⟩
  | _, _, _, .rety D c, hD, heq => fun ℓ hℓ => by
      obtain ⟨ℓ', hℓ', s⟩ := EvTy.invLam_hb_strictRooted D hD heq ℓ hℓ
      exact ⟨ℓ', List.mem_append.mpr (.inl hℓ'), s⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-- every leaf of a `letE` inversion's `.hb` is a strict sub-derivation
    of a leaf of the (lit-rooted) input. -/
def EvTy.invLetE_hb_strictRooted {A value body : Expr Nat} :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (hD : D.litRooted = true) → (heq : e = .letE A value body) →
    ∀ ℓ ∈ (D.invLetE hD heq).hb.leaves, ∃ ℓ' ∈ D.leaves, SubOf ℓ ℓ'
  | _, _, _, .lit d hsub, _, heq => fun ℓ hℓ =>
      ⟨.ty d, by
        show (Jd.ty d : Jd E n) ∈ ([Jd.ty d] : List (Jd E n))
        exact .head _,
        EvTy.invLetE_strict d hsub heq ℓ (by
          simp only [EvInvLetE.leaves, List.mem_append, or_assoc]
          exact .inr (.inr (.inl hℓ)))⟩
  | _, _, _, .rety D c, hD, heq => fun ℓ hℓ => by
      obtain ⟨ℓ', hℓ', s⟩ := EvTy.invLetE_hb_strictRooted D hD heq ℓ hℓ
      exact ⟨ℓ', List.mem_append.mpr (.inl hℓ'), s⟩
  | _, _, _, .wk _ _ _, hD, _ => nomatch hD
  | _, _, _, .esub _ _ _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .subst0 _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .substLet _ _ _ _, hD, _ => nomatch hD
  | _, _, _, .var _ _ _, hD, _ => nomatch hD
  | _, _, _, .sort _, hD, _ => nomatch hD
  | _, _, _, .const _ _ _ _ _ _, hD, _ => nomatch hD

/-! ### the intro-spine U on provenance

Mirror of `introTypeSpineUniqueAux` arm by arm: recursion on the first
(literal) input; the second is inverted on provenance. -/

/-- the intro-spine U on provenance: first input a certified literal,
    second input lit-rooted provenance. -/
def introU (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT E n Γ e A) →
    (∃ r ∈ R, SubEq (.ty d) r) →
    introTypeSpine e = true → {B : Expr Nat} → (r : EvTy R Γ e B) →
    r.litRooted = true → EvTc R Γ A B
  | _, _, _, .sort _ _, _, _, _, r, hr => r.invSortT hr rfl
  | _, _, _, .bvar _ _ _ hlk, _, _, _, r, hr => by
      let p := r.invBvar hr rfl
      exact EvTc.cast rfl (Option.some.inj (p.hlk.symm.trans hlk)) rfl p.hc
  | _, _, _, .const _ _ _ _ hres _ _, _, _, _, r, hr => by
      let p := r.invConst hr rfl
      exact EvTc.cast rfl
        (congrArg (fun m' => instantiateLevels _ m'.mtype)
          (Option.some.inj (p.hres.symm.trans hres))) rfl p.hc
  | _, _, _, .lam _ A0 u0 body B0 hA hbody, hsub, hs, _, r, hr => by
      let pieces := r.invLam hr rfl
      have hbl := EvTy.invLam_hb_litRooted r hr rfl
      have cc := introU hcl hinst hbody
        (certOfChild (lamChildSnd hA hbody) hsub) hs pieces.hb hbl
      exact .trans
        (.piCod u0 (.lit hA (certOfChild (lamChildFst hA hbody) hsub)) cc)
        pieces.hc
  | Γ, _, _, .letE _ dom _ value B0 body hA' hv hbody, hsub, hs, _, r, hr => by
      let pieces := r.invLetE hr rfl
      have hbl := EvTy.invLetE_hb_litRooted r hr rfl
      have cc := introU hcl hinst hbody
        (certOfChild (letEChildThd hA' hv hbody) hsub) hs pieces.hb hbl
      have ci : EvTc R Γ (instantiate0 value B0)
          (instantiate0 value pieces.B) :=
        EvTc.cast rfl (by simp [lift_zero, instantiate0])
          (by simp [lift_zero, instantiate0])
          (.substLet (t := dom) (w0 := value) 0 cc (by simp)
            (EvTy.cast rfl (by simp [lift_zero]) (by simp [lift_zero])
              (.lit hv (certOfChild (letEChildSnd hA' hv hbody) hsub))))
      exact .trans ci pieces.hc
  | _, _, _, .conv _ _ _ _ u0 ha hc, hsub, hs, _, r, hr =>
      .trans (.symm (.ofCv u0 (.lit hc (certOfChild (convChildSnd ha hc) hsub))))
        (introU hcl hinst ha (certOfChild (convChildFst ha hc) hsub) hs r hr)
  | _, _, _, .pi .., _, hs, _, _, _ => nomatch hs
  | _, _, _, .app .., _, hs, _, _, _ => nomatch hs
  | _, _, _, .lit .., _, hs, _, _, _ => nomatch hs

/-! ### O-M1 for `introU` -/

/-- O-M1 for `introU`: every output leaf is a sub-derivation of the
    literal root `.ty d` or of a leaf of `r`. -/
theorem introU_OM1 (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT E n Γ e A) →
    (hsub : ∃ r ∈ R, SubEq (.ty d) r) → (hs : introTypeSpine e = true) →
    {B : Expr Nat} → (r : EvTy R Γ e B) → (hr : r.litRooted = true) →
    ∀ ℓ ∈ (introU hcl hinst d hsub hs r hr).leaves,
    ∃ ℓ' ∈ (.ty d :: r.leaves), SubEq ℓ ℓ'
  | _, _, _, .sort _ _, _, _, _, r, hr => fun ℓ hℓ => by
      simp only [introU] at hℓ
      obtain ⟨ℓ', hℓ', s⟩ := EvTy.invSortT_leaves r hr rfl ℓ hℓ
      exact ⟨ℓ', .tail _ hℓ', s⟩
  | _, _, _, .bvar _ _ _ hlk, _, _, _, r, hr => fun ℓ hℓ => by
      simp only [introU, EvTc.cast_leaves] at hℓ
      obtain ⟨ℓ', hℓ', s⟩ := EvTy.invBvar_leaves r hr rfl ℓ hℓ
      exact ⟨ℓ', .tail _ hℓ', s⟩
  | _, _, _, .const _ _ _ _ hres _ _, _, _, _, r, hr => fun ℓ hℓ => by
      simp only [introU, EvTc.cast_leaves] at hℓ
      obtain ⟨ℓ', hℓ', s⟩ := EvTy.invConst_leaves r hr rfl ℓ hℓ
      exact ⟨ℓ', .tail _ hℓ', s⟩
  | Γ, _, _, .lam _ A0 u0 body B0 hA hbody, hsub, hs, _, r, hr =>
      fun ℓ hℓ => by
      simp only [introU, EvTc.leaves, EvTy.leaves, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false, List.append_nil,
        or_assoc] at hℓ
      rcases hℓ with rfl | hm | hm
      · exact ⟨.ty (.lam Γ A0 u0 body B0 hA hbody), .head _,
          .inr (.child (lamChildFst hA hbody))⟩
      · obtain ⟨ℓ', hℓ', s⟩ := introU_OM1 hcl hinst hbody
          (certOfChild (lamChildSnd hA hbody) hsub) hs
          (r.invLam hr rfl).hb (EvTy.invLam_hb_litRooted r hr rfl) ℓ hm
        rcases List.mem_cons.mp hℓ' with rfl | hℓ'
        · exact ⟨.ty (.lam Γ A0 u0 body B0 hA hbody), .head _,
            .inr (subEq_trans_subOf s (.child (lamChildSnd hA hbody)))⟩
        · obtain ⟨ℓ'', hℓ'', s2⟩ := EvTy.invLam_hb_strictRooted r hr rfl ℓ' hℓ'
          exact ⟨ℓ'', .tail _ hℓ'', .inr (subEq_trans_subOf s s2)⟩
      · obtain ⟨ℓ', hℓ', s⟩ := EvTy.invLam_leaves r hr rfl ℓ
          (List.mem_append.mpr (.inr hm))
        exact ⟨ℓ', .tail _ hℓ', s⟩
  | Γ, _, _, .letE _ dom _ value B0 body hA' hv hbody, hsub, hs, _, r, hr =>
      fun ℓ hℓ => by
      simp only [introU, EvTc.leaves, EvTy.leaves, EvTc.cast_leaves,
        EvTy.cast_leaves, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, List.append_nil, or_assoc] at hℓ
      rcases hℓ with hm | rfl | hm
      · obtain ⟨ℓ', hℓ', s⟩ := introU_OM1 hcl hinst hbody
          (certOfChild (letEChildThd hA' hv hbody) hsub) hs
          (r.invLetE hr rfl).hb (EvTy.invLetE_hb_litRooted r hr rfl) ℓ hm
        rcases List.mem_cons.mp hℓ' with rfl | hℓ'
        · exact ⟨.ty (.letE Γ dom _ value B0 body hA' hv hbody), .head _,
            .inr (subEq_trans_subOf s (.child (letEChildThd hA' hv hbody)))⟩
        · obtain ⟨ℓ'', hℓ'', s2⟩ :=
            EvTy.invLetE_hb_strictRooted r hr rfl ℓ' hℓ'
          exact ⟨ℓ'', .tail _ hℓ'', .inr (subEq_trans_subOf s s2)⟩
      · exact ⟨.ty (.letE Γ dom _ value B0 body hA' hv hbody), .head _,
          .inr (.child (letEChildSnd hA' hv hbody))⟩
      · obtain ⟨ℓ', hℓ', s⟩ := EvTy.invLetE_leaves r hr rfl ℓ
          (List.mem_append.mpr (.inr hm))
        exact ⟨ℓ', .tail _ hℓ', s⟩
  | _, _, _, .conv Γ0 e0 A0 B0 u0 ha hc, hsub, hs, _, r, hr => fun ℓ hℓ => by
      simp only [introU, EvTc.leaves, EvTy.leaves, EvCv.leaves,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.append_nil, or_assoc] at hℓ
      rcases hℓ with rfl | hm
      · exact ⟨.ty (.conv Γ0 e0 A0 B0 u0 ha hc), .head _,
          .inr (.child (convChildSnd ha hc))⟩
      · obtain ⟨ℓ', hℓ', s⟩ := introU_OM1 hcl hinst ha
          (certOfChild (convChildFst ha hc) hsub) hs r hr ℓ hm
        rcases List.mem_cons.mp hℓ' with rfl | hℓ'
        · exact ⟨.ty (.conv Γ0 e0 A0 B0 u0 ha hc), .head _,
            .inr (subEq_trans_subOf s (.child (convChildFst ha hc)))⟩
        · exact ⟨ℓ', .tail _ hℓ', s⟩
  | _, _, _, .pi .., _, hs, _, _, _ => nomatch hs
  | _, _, _, .app .., _, hs, _, _, _ => nomatch hs
  | _, _, _, .lit .., _, hs, _, _, _ => nomatch hs

/-! ### the U→U edge of O-M3(b), per recursive arm

`lam`/`letE` remove the literal first input and replace the second
argument with a strict piece; `conv` keeps the second argument (its
leaves stay in `Z`) and strictly descends only the first input. -/

/-- the `.lam` arm's U→U edge. -/
theorem introU_edge_lam {Γ : LCtx} {A0 body B0 B : Expr Nat} {u0 : Level}
    {hA : HasTyT E n Γ A0 (.sort u0)}
    {hbody : HasTyT E n (.assumption A0 :: Γ) body B0}
    {r : EvTy R Γ (.lam A0 body) B} (hr : r.litRooted = true) :
    DMStep ((.ty hbody :: (r.invLam hr rfl).hb.leaves).map Jd.wt)
      ((.ty (.lam Γ A0 u0 body B0 hA hbody) :: r.leaves).map Jd.wt) := by
  have dm := dm_of_strictLeaves
    (X := .ty (.lam Γ A0 u0 body B0 hA hbody) :: r.leaves) (Z := [])
    (L := .ty hbody :: (r.invLam hr rfl).hb.leaves) (List.cons_ne_nil _ _)
    (fun ℓ hℓ => by
      rcases List.mem_cons.mp hℓ with rfl | hm
      · exact ⟨.ty (.lam Γ A0 u0 body B0 hA hbody), .head _,
          .child (lamChildSnd hA hbody)⟩
      · obtain ⟨ℓ', hℓ', s⟩ := EvTy.invLam_hb_strictRooted r hr rfl ℓ hm
        exact ⟨ℓ', .tail _ hℓ', s⟩)
  simpa only [List.map, List.append_nil] using dm

/-- the `.letE` arm's U→U edge. -/
theorem introU_edge_letE {Γ : LCtx} {A0 value B0 body B : Expr Nat}
    {u0 : Level}
    {hA : HasTyT E n Γ A0 (.sort u0)}
    {hv : HasTyT E n Γ value A0}
    {hbody : HasTyT E n (.letBinding A0 value :: Γ) body B0}
    {r : EvTy R Γ (.letE A0 value body) B} (hr : r.litRooted = true) :
    DMStep ((.ty hbody :: (r.invLetE hr rfl).hb.leaves).map Jd.wt)
      ((.ty (.letE Γ A0 u0 value B0 body hA hv hbody) :: r.leaves).map Jd.wt) := by
  have dm := dm_of_strictLeaves
    (X := .ty (.letE Γ A0 u0 value B0 body hA hv hbody) :: r.leaves)
    (Z := [])
    (L := .ty hbody :: (r.invLetE hr rfl).hb.leaves) (List.cons_ne_nil _ _)
    (fun ℓ hℓ => by
      rcases List.mem_cons.mp hℓ with rfl | hm
      · exact ⟨.ty (.letE Γ A0 u0 value B0 body hA hv hbody), .head _,
          .child (letEChildThd hA hv hbody)⟩
      · obtain ⟨ℓ', hℓ', s⟩ := EvTy.invLetE_hb_strictRooted r hr rfl ℓ hm
        exact ⟨ℓ', .tail _ hℓ', s⟩)
  simpa only [List.map, List.append_nil] using dm

/-- the `.conv` arm's U→U edge: only the first literal root descends;
    the second argument's leaves are kept in `Z`. -/
theorem introU_edge_conv {Γ : LCtx} {e A0 B0 B : Expr Nat} {u0 : Level}
    {ha : HasTyT E n Γ e A0} {hc : ConvT E n Γ A0 B0 (.sort u0)}
    {r : EvTy R Γ e B} :
    DMStep ((.ty ha :: r.leaves).map Jd.wt)
      ((.ty (.conv Γ e A0 B0 u0 ha hc) :: r.leaves).map Jd.wt) := by
  have dm := dm_of_strictLeaves (X := [.ty (.conv Γ e A0 B0 u0 ha hc)])
    (Z := r.leaves) (L := [.ty ha]) (List.cons_ne_nil _ _)
    (fun ℓ hℓ => by
      rcases List.mem_cons.mp hℓ with rfl | hm
      · exact ⟨.ty (.conv Γ e A0 B0 u0 ha hc), .head _,
          .child (convChildFst ha hc)⟩
      · exact absurd hm (List.not_mem_nil _))
  simpa only [List.map, List.nil_append, List.cons_append] using dm

/-! ### non-vacuity pins -/

private def pinCl : EnvClosed emptyEnv := envClosed_of_envWfT EnvWfT.empty

private def pinSS : EnvMembersSubstStable emptyEnv :=
  envWfT_subst_inst EnvWfT.empty

/-- the body of the pin lambda: `bvar 0` at `sort 0` in one assumption. -/
private def pinLamBody : HasTyT emptyEnv 0 [.assumption (.sort .zero)]
    (.bvar 0) (.sort .zero) :=
  .bvar _ 0 _ rfl

/-- first (literal) typing of `lam (sort 0) (bvar 0)` at `pi (sort 0) (sort 0)`. -/
private def pinLamD : HasTyT emptyEnv 0 []
    (.lam (.sort .zero) (.bvar 0)) (.pi (.sort .zero) (.sort .zero)) :=
  .lam [] (.sort .zero) (.succ .zero) (.bvar 0) (.sort .zero)
    (.sort [] .zero) pinLamBody

/-- `pi (sort 0) (sort 0)` is a `sort (imax 1 1)`. -/
private def pinPiTy : HasTyT emptyEnv 0 []
    (.pi (.sort .zero) (.sort .zero))
    (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (.sort [] .zero) (.sort [.assumption (.sort .zero)] .zero)

/-- the same lambda under one `.conv` — a different derivation, and its
    `hc` premise becomes a nontrivial `ofCv (lit …)` chain link. -/
private def pinLamConv : HasTyT emptyEnv 0 []
    (.lam (.sort .zero) (.bvar 0)) (.pi (.sort .zero) (.sort .zero)) :=
  .conv [] _ _ _ (.imax (.succ .zero) (.succ .zero)) pinLamD
    (.refl [] _ _ pinPiTy)

/-- root bundle for the pin: both derivations' atoms. -/
private def pinLamR : List (Jd emptyEnv 0) := [.ty pinLamD, .ty pinLamConv]

/-- second (provenance) input: the conv-wrapped typing as a `lit`. -/
private def pinLamEv : EvTy pinLamR []
    (.lam (.sort .zero) (.bvar 0)) (.pi (.sort .zero) (.sort .zero)) :=
  .lit pinLamConv ⟨.ty pinLamConv, .tail _ (.head _), .inl rfl⟩

/-- `introU` at the pin: `pi (sort 0) (sort 0)` converts to itself. -/
def pin_introU : EvTc pinLamR []
    (.pi (.sort .zero) (.sort .zero)) (.pi (.sort .zero) (.sort .zero)) :=
  introU pinCl pinSS pinLamD ⟨.ty pinLamD, .head _, .inl rfl⟩ rfl
    pinLamEv rfl

/-- O-M1 instantiated at the pin. -/
theorem pin_introU_OM1 :
    ∀ ℓ ∈ pin_introU.leaves,
    ∃ ℓ' ∈ (.ty pinLamD :: pinLamEv.leaves), SubEq ℓ ℓ' :=
  introU_OM1 pinCl pinSS pinLamD ⟨.ty pinLamD, .head _, .inl rfl⟩ rfl
    pinLamEv rfl

/-- the lam-edge instantiated at the pin. -/
theorem pin_introU_edge_lam :
    DMStep
      ((.ty pinLamBody :: (pinLamEv.invLam rfl rfl).hb.leaves).map Jd.wt)
      ((.ty pinLamD :: pinLamEv.leaves).map Jd.wt) :=
  introU_edge_lam (r := pinLamEv) rfl

/-- the materialized result has the expected endpoints. -/
def pin_introU_val : TyConvT emptyEnv 0 []
    (.pi (.sort .zero) (.sort .zero)) (.pi (.sort .zero) (.sort .zero)) :=
  pin_introU.val pinCl pinSS

#print axioms UProc
#print axioms OM1
#print axioms EvTy.cast
#print axioms EvTc.cast
#print axioms EvTy.cast_leaves
#print axioms EvTc.cast_leaves
#print axioms EvTy.invLam_hb_litRooted
#print axioms EvTy.invLetE_hb_litRooted
#print axioms EvTy.invLam_hb_strictRooted
#print axioms EvTy.invLetE_hb_strictRooted
#print axioms introU
#print axioms introU_OM1
#print axioms introU_edge_lam
#print axioms introU_edge_letE
#print axioms introU_edge_conv
#print axioms pin_introU
#print axioms pin_introU_OM1
#print axioms pin_introU_edge_lam
#print axioms pin_introU_val

end Rcic.Declarative.F8Measure
