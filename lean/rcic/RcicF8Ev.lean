import Lean
import rcic.RcicF8Child
import rcic.RcicConvPlus
import rcic.RcicTypedWeaken
import rcic.RcicTypedSubst
import rcic.RcicParRedTSubst
import rcic.RcicDT008Equiv
import rcic.RcicTypedConv

/-! # RcicF8Ev — provenance derivations over a root bundle (piRow O-M, part 2)

Carrier part 2 for LIFT♮'s measure obligations O-M1..O-M3
(`research/rcic/semantic/S2_OM_OBLIGATIONS.md` on PR #6792, cc ruling 14:49Z Q1):
the plain-side *provenance* layer over a root bundle `R : List (Jd E n)`. Only
`lit` contributes atoms; transports and retyping are lazy constructors whose
leaves are exactly the union of their children's. `closure_claim = 0`.

This module imports `RcicConvPlus` and REUSES its transport index shapes: `wk`
inserts a `LocalDecl` at a cutoff and lifts, `esub` removes an assumption entry
at `j` and instantiates. No ConvPlus object (`Rcic.Syn.TyP`, `Rcic.Syn.CvP`,
`Rcic.Syn.EnvExt`, ...) is re-declared — the drift guards below check that the
shared constructors' result indices still coincide term-by-term. The lazy
constructors added here beyond ConvPlus's lazy transports are `rety`
(materializes via `hasTyT_of_tyConvT`), `EvTy.var` (the premise-free `HasTyT.bvar`, leaf-less,
D-VAR for the X tile's context conversion, #7026 Q2), `EvTy.sort` / `EvTy.const` /
`EvCv.sorts` / `EvCv.consts` (premise-free leaf-less sort/const atoms for J/D under the
D-VAR principle, #7060 Q2), `EvCv.rety` (`convT_of_tyConv` — lazy conversion retyping along
an `EvTc` chain, #7060 Q2), `piCod` (`tyConvT_pi_cod`), `subst0`
(`tyConvT_substS`), `substLet` (`tyConvT_substLetS`), `EvTc.wk`
(`tyConvTWeaken` — the residual chain's weakening, added for O-M1b's
inversion through `wk` roots), and `EvCv.refl` (`ConvT.refl` — lazy
reflexivity whose leaves are its typing's, added for the StructPi
refl-source arm).

Omitted transports, and why:
- `linst` is omitted from all three layers: it changes the level arity (its `D`
  lives at arity `a`, the result at `n`), so a root bundle `R : List (Jd E n)`
  at a single arity cannot certify its inner leaves without a multi-arity
  bundle.
- `ewk` is omitted from all three layers: no plain-side materialization lemma
  for an ARBITRARY `Rcic.Syn.EnvExt` exists. Two searches: (1) `EnvExt` appears
  only inside `RcicConvPlus` itself (the `TyP`/`CvP` `ewk` arms and
  `TyP.triv`/`CvP.triv`) — no `EnvExt E₀ E → HasTyT E₀ Γ e A → HasTyT E Γ e A`;
  (2) the only environment-monotonicity results on the plain judgments are the
  single-member transports `hasTyT_extendEnv` / `convT_extendEnv` /
  `tyConvT_extendEnv` (`RcicTypedGroup.lean`) and their `restrictExt` inverses —
  a fixed `extendEnv E r m` shape, not arbitrary `EnvExt`. F8's U/X/P do not
  need either transport now.

The O6 bridge to ConvPlus's `TyP` is stated as `EvTyPBridge` — sealed as an
obligation, intentionally unproved.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat}

mutual

/-- provenance typing over `R`: a `HasTyT`-shaped derivation whose only atoms
    are `lit` leaves certified (`SubEq`) into the root bundle. -/
inductive EvTy (R : List (Jd E n)) : LCtx → Expr Nat → Expr Nat → Type where
  | lit {Γ e T} (d : HasTyT E n Γ e T) (hsub : ∃ r ∈ R, SubEq (.ty d) r) :
      EvTy R Γ e T
  | wk {Γ e A} (d : LocalDecl) (c : Nat) (D : EvTy R Γ e A) :
      EvTy R (insertAt d c Γ) (lift c 1 e) (lift c 1 A)
  | esub {Γ e A t v} (j : Nat) (u : Level) (D : EvTy R Γ e A)
      (hget : Γ[j]? = some (.assumption t))
      (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : EvTy R (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      EvTy R (substRemove v j Γ) (instantiate j (lift 0 j v) e)
        (instantiate j (lift 0 j v) A)
  /-- the `hvT`-free substitution (W-X-SUBST S0 #7107, cc Q7): the exact mirror of
      `EvTc.subst0`; materialized by `hasTyT_substS`, which reads no sort typing of the
      binder. Needed to re-wrap a valley's endpoint typings under a substitution. -/
  | subst0 {Γ e A t v} (j : Nat) (D : EvTy R Γ e A)
      (hget : Γ[j]? = some (.assumption t))
      (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
      EvTy R (substRemove v j Γ) (instantiate j (lift 0 j v) e)
        (instantiate j (lift 0 j v) A)
  /-- the let twin (`EvTc.substLet`'s typing counterpart); materialized by `hasTyT_substLetS`. -/
  | substLet {Γ e A t w} (j : Nat) (D : EvTy R Γ e A)
      (hget : Γ[j]? = some (.letBinding t w))
      (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) :
      EvTy R (substRemove w j Γ) (instantiate j (lift 0 j w) e)
        (instantiate j (lift 0 j w) A)
  | var {Γ : LCtx} (i : Nat) (A : Expr Nat) (hlk : lookupType Γ i = some A) :
      EvTy R Γ (.bvar i) A
  | sort {Γ : LCtx} (l : Level) : EvTy R Γ (.sort l) (.sort (.succ l))
  | const {Γ : LCtx} (r : Nat) (ls : List Level) (m : CheckedMember)
      (hres : E.members r = some m) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true) :
      EvTy R Γ (.const r ls) (instantiateLevels ls m.mtype)
  | rety {Γ e T T'} (D : EvTy R Γ e T) (c : EvTc R Γ T T') : EvTy R Γ e T'

/-- provenance type-conversion chain over `R`; `refl` has no leaves. -/
inductive EvTc (R : List (Jd E n)) : LCtx → Expr Nat → Expr Nat → Type where
  | lit {Γ A B} (d : TyConvT E n Γ A B) (hsub : ∃ r ∈ R, SubEq (.tc d) r) :
      EvTc R Γ A B
  | ofCv {Γ A B} (u : Level) (c : EvCv R Γ A B (.sort u)) : EvTc R Γ A B
  | refl (Γ : LCtx) (A : Expr Nat) : EvTc R Γ A A
  | symm {Γ A B} (c : EvTc R Γ A B) : EvTc R Γ B A
  | trans {Γ A B C} (c₁ : EvTc R Γ A B) (c₂ : EvTc R Γ B C) : EvTc R Γ A C
  | piCod {Γ A B B'} (u : Level) (hA : EvTy R Γ A (.sort u))
      (c : EvTc R (.assumption A :: Γ) B B') :
      EvTc R Γ (.pi A B) (.pi A B')
  | subst0 {Γ A A' t v} (j : Nat) (c : EvTc R Γ A A')
      (hget : Γ[j]? = some (.assumption t))
      (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
      EvTc R (substRemove v j Γ) (instantiate j (lift 0 j v) A)
        (instantiate j (lift 0 j v) A')
  | substLet {Γ A A' t w0} (j : Nat) (c : EvTc R Γ A A')
      (hget : Γ[j]? = some (.letBinding t w0))
      (hv : EvTy R (substRemove w0 j Γ) (lift 0 j w0) (lift 0 j t)) :
      EvTc R (substRemove w0 j Γ) (instantiate j (lift 0 j w0) A)
        (instantiate j (lift 0 j w0) A')
  | wk {Γ A B} (d : LocalDecl) (c : Nat) (h : EvTc R Γ A B) :
      EvTc R (insertAt d c Γ) (lift c 1 A) (lift c 1 B)

/-- provenance conversion over `R`. -/
inductive EvCv (R : List (Jd E n)) : LCtx → Expr Nat → Expr Nat → Expr Nat → Type
    where
  | lit {Γ a b T} (d : ConvT E n Γ a b T) (hsub : ∃ r ∈ R, SubEq (.cv d) r) :
      EvCv R Γ a b T
  | refl {Γ a A} (D : EvTy R Γ a A) : EvCv R Γ a a A
  | symm {Γ a b T} (c : EvCv R Γ a b T) : EvCv R Γ b a T
  | trans {Γ a b c T} (c₁ : EvCv R Γ a b T) (c₂ : EvCv R Γ b c T) :
      EvCv R Γ a c T
  | tyConv {Γ a b A A'} (u : Level) (h : EvCv R Γ a b A)
      (hA : EvCv R Γ A A' (.sort u)) : EvCv R Γ a b A'
  | wk {Γ a b T} (d : LocalDecl) (c : Nat) (h : EvCv R Γ a b T) :
      EvCv R (insertAt d c Γ) (lift c 1 a) (lift c 1 b) (lift c 1 T)
  | esub {Γ a b T t v} (j : Nat) (u : Level) (h : EvCv R Γ a b T)
      (hget : Γ[j]? = some (.assumption t))
      (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
      (hvT : EvTy R (substRemove v j Γ) (lift 0 j t) (.sort u)) :
      EvCv R (substRemove v j Γ) (instantiate j (lift 0 j v) a)
        (instantiate j (lift 0 j v) b) (instantiate j (lift 0 j v) T)
  /-- the `hvT`-free substitution (W-X-SUBST slice 1): `EvTy.subst0`'s conversion twin,
      materialized by `convT_substS`, which reads no sort typing of the binder. -/
  | subst0 {Γ a b T t v} (j : Nat) (h : EvCv R Γ a b T)
      (hget : Γ[j]? = some (.assumption t))
      (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
      EvCv R (substRemove v j Γ) (instantiate j (lift 0 j v) a)
        (instantiate j (lift 0 j v) b) (instantiate j (lift 0 j v) T)
  /-- the let twin, materialized by `convT_substLetS`. -/
  | substLet {Γ a b T t w} (j : Nat) (h : EvCv R Γ a b T)
      (hget : Γ[j]? = some (.letBinding t w))
      (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) :
      EvCv R (substRemove w j Γ) (instantiate j (lift 0 j w) a)
        (instantiate j (lift 0 j w) b) (instantiate j (lift 0 j w) T)
  | sorts {Γ : LCtx} (l l' : Level) (heq : eqN l l') :
      EvCv R Γ (.sort l) (.sort l') (.sort (.succ l))
  | consts {Γ : LCtx} (r : Nat) (ls ls' : List Level) (m : CheckedMember)
      (hres : E.members r = some m) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true)
      (heq : eqNList ls ls') :
      EvCv R Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype)
  | rety {Γ a b T T'} (h : EvCv R Γ a b T) (c : EvTc R Γ T T') :
      EvCv R Γ a b T'

end

variable {R : List (Jd E n)}

mutual

/-- forgetful materialization of a provenance typing into the plain `HasTyT`,
    through the landed transport lemmas. `hcl`/`hinst` are exactly the
    environment hypotheses those lemmas state — no `EnvWfT` is needed. -/
def EvTy.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {e T : Expr Nat} → EvTy R Γ e T → HasTyT E n Γ e T
  | _, _, _, .lit d _ => d
  | _, _, _, .wk d c D => hasTyTWeaken d hcl (D.val hcl hinst)
  | _, _, _, .esub _ _ D hget hv _ =>
      hasTyT_substS hcl hinst _ _ (D.val hcl hinst) hget (hv.val hcl hinst)
  | _, _, _, .subst0 _ D hget hv =>
      hasTyT_substS hcl hinst _ _ (D.val hcl hinst) hget (hv.val hcl hinst)
  | _, _, _, .substLet _ D hget hv =>
      hasTyT_substLetS hcl hinst _ _ (D.val hcl hinst) hget (hv.val hcl hinst)
  | _, _, _, .var i A hlk => .bvar _ i A hlk
  | _, _, _, .sort l => .sort _ l
  | _, _, _, .const r ls m hres hlen hwf => .const _ r ls m hres hlen hwf
  | _, _, _, .rety D c => hasTyT_of_tyConvT (D.val hcl hinst) (c.val hcl hinst)

/-- materialization of a provenance chain into the plain `TyConvT`. -/
def EvTc.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → TyConvT E n Γ A B
  | _, _, _, .lit d _ => d
  | _, _, _, .ofCv u c => .of _ _ _ u (c.val hcl hinst)
  | _, _, _, .refl Γ A => .refl Γ A
  | _, _, _, .symm c => (c.val hcl hinst).symmT
  | _, _, _, .trans c₁ c₂ => .trans _ _ _ _ (c₁.val hcl hinst) (c₂.val hcl hinst)
  | _, _, _, .piCod _ hA c =>
      tyConvT_pi_cod (hA.val hcl hinst) (c.val hcl hinst)
  | _, _, _, .subst0 _ c hget hv =>
      tyConvT_substS hcl hinst _ _ (c.val hcl hinst) hget (hv.val hcl hinst)
  | _, _, _, .substLet _ c hget hv =>
      tyConvT_substLetS hcl hinst _ _ (c.val hcl hinst) hget (hv.val hcl hinst)
  | _, _, _, .wk d c h => tyConvTWeaken d hcl (h.val hcl hinst)

/-- materialization of a provenance conversion into the plain `ConvT`. -/
def EvCv.val (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {a b T : Expr Nat} → EvCv R Γ a b T → ConvT E n Γ a b T
  | _, _, _, _, .lit d _ => d
  | _, _, _, _, .refl D => .refl _ _ _ (D.val hcl hinst)
  | _, _, _, _, .symm c => .symm _ _ _ _ (c.val hcl hinst)
  | _, _, _, _, .trans c₁ c₂ =>
      .trans _ _ _ _ _ (c₁.val hcl hinst) (c₂.val hcl hinst)
  | _, _, _, _, .tyConv u h hA =>
      .tyConv _ _ _ _ _ u (h.val hcl hinst) (hA.val hcl hinst)
  | _, _, _, _, .wk d c h => convTWeaken d hcl (h.val hcl hinst)
  | _, _, _, _, .esub _ _ h hget hv _ =>
      convT_substS hcl hinst _ _ (h.val hcl hinst) hget (hv.val hcl hinst)
  | _, _, _, _, .subst0 _ h hget hv =>
      convT_substS hcl hinst _ _ (h.val hcl hinst) hget (hv.val hcl hinst)
  | _, _, _, _, .substLet _ h hget hv =>
      convT_substLetS hcl hinst _ _ (h.val hcl hinst) hget (hv.val hcl hinst)
  | _, _, _, _, .sorts l l' heq => .sorts _ l l' heq
  | _, _, _, _, .consts r ls ls' m hres hlen hwf hwf' heq =>
      .consts _ r ls ls' m hres hlen hwf hwf' heq
  | _, _, _, _, .rety h c => convT_of_tyConv (h.val hcl hinst) (c.val hcl hinst)

end

mutual

/-- the literal leaves of a provenance typing, with multiplicity, in
    constructor order. -/
def EvTy.leaves : {Γ : LCtx} → {e T : Expr Nat} → EvTy R Γ e T → List (Jd E n)
  | _, _, _, .lit d _ => [.ty d]
  | _, _, _, .wk _ _ D => D.leaves
  | _, _, _, .esub _ _ D _ hv hvT => D.leaves ++ hv.leaves ++ hvT.leaves
  | _, _, _, .subst0 _ D _ hv => D.leaves ++ hv.leaves
  | _, _, _, .substLet _ D _ hv => D.leaves ++ hv.leaves
  | _, _, _, .var _ _ _ => []
  | _, _, _, .sort _ => []
  | _, _, _, .const _ _ _ _ _ _ => []
  | _, _, _, .rety D c => D.leaves ++ c.leaves

/-- leaves of a provenance chain (`refl` has none). -/
def EvTc.leaves : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → List (Jd E n)
  | _, _, _, .lit d _ => [.tc d]
  | _, _, _, .ofCv _ c => c.leaves
  | _, _, _, .refl _ _ => []
  | _, _, _, .symm c => c.leaves
  | _, _, _, .trans c₁ c₂ => c₁.leaves ++ c₂.leaves
  | _, _, _, .piCod _ hA c => hA.leaves ++ c.leaves
  | _, _, _, .subst0 _ c _ hv => c.leaves ++ hv.leaves
  | _, _, _, .substLet _ c _ hv => c.leaves ++ hv.leaves
  | _, _, _, .wk _ _ h => h.leaves

/-- leaves of a provenance conversion. -/
def EvCv.leaves : {Γ : LCtx} → {a b T : Expr Nat} → EvCv R Γ a b T →
    List (Jd E n)
  | _, _, _, _, .lit d _ => [.cv d]
  | _, _, _, _, .refl D => D.leaves
  | _, _, _, _, .symm c => c.leaves
  | _, _, _, _, .trans c₁ c₂ => c₁.leaves ++ c₂.leaves
  | _, _, _, _, .tyConv _ h hA => h.leaves ++ hA.leaves
  | _, _, _, _, .wk _ _ h => h.leaves
  | _, _, _, _, .esub _ _ h _ hv hvT => h.leaves ++ hv.leaves ++ hvT.leaves
  | _, _, _, _, .subst0 _ h _ hv => h.leaves ++ hv.leaves
  | _, _, _, _, .substLet _ h _ hv => h.leaves ++ hv.leaves
  | _, _, _, _, .sorts _ _ _ => []
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ => []
  | _, _, _, _, .rety h c => h.leaves ++ c.leaves

end

mutual

/-- constructor count of a provenance typing: 1 + children. -/
def EvTy.size : {Γ : LCtx} → {e T : Expr Nat} → EvTy R Γ e T → Nat
  | _, _, _, .lit _ _ => 1
  | _, _, _, .wk _ _ D => 1 + D.size
  | _, _, _, .esub _ _ D _ hv hvT => 1 + D.size + hv.size + hvT.size
  | _, _, _, .subst0 _ D _ hv => 1 + D.size + hv.size
  | _, _, _, .substLet _ D _ hv => 1 + D.size + hv.size
  | _, _, _, .var _ _ _ => 1
  | _, _, _, .sort _ => 1
  | _, _, _, .const _ _ _ _ _ _ => 1
  | _, _, _, .rety D c => 1 + D.size + c.size

/-- constructor count of a provenance chain. -/
def EvTc.size : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → Nat
  | _, _, _, .lit _ _ => 1
  | _, _, _, .ofCv _ c => 1 + c.size
  | _, _, _, .refl _ _ => 1
  | _, _, _, .symm c => 1 + c.size
  | _, _, _, .trans c₁ c₂ => 1 + c₁.size + c₂.size
  | _, _, _, .piCod _ hA c => 1 + hA.size + c.size
  | _, _, _, .subst0 _ c _ hv => 1 + c.size + hv.size
  | _, _, _, .substLet _ c _ hv => 1 + c.size + hv.size
  | _, _, _, .wk _ _ h => 1 + h.size

/-- constructor count of a provenance conversion. -/
def EvCv.size : {Γ : LCtx} → {a b T : Expr Nat} → EvCv R Γ a b T → Nat
  | _, _, _, _, .lit _ _ => 1
  | _, _, _, _, .refl D => 1 + D.size
  | _, _, _, _, .symm c => 1 + c.size
  | _, _, _, _, .trans c₁ c₂ => 1 + c₁.size + c₂.size
  | _, _, _, _, .tyConv _ h hA => 1 + h.size + hA.size
  | _, _, _, _, .wk _ _ h => 1 + h.size
  | _, _, _, _, .esub _ _ h _ hv hvT => 1 + h.size + hv.size + hvT.size
  | _, _, _, _, .subst0 _ h _ hv => 1 + h.size + hv.size
  | _, _, _, _, .substLet _ h _ hv => 1 + h.size + hv.size
  | _, _, _, _, .sorts _ _ _ => 1
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ => 1
  | _, _, _, _, .rety h c => 1 + h.size + c.size

end

/-! ### O-M3(a): every leaf is certified into the root bundle -/

mutual

def EvTy.leaves_root :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    ∀ ℓ ∈ D.leaves, ∃ r ∈ R, SubEq ℓ r
  | _, _, _, .lit _ hsub => fun _ hℓ => by
      simp only [EvTy.leaves, List.mem_cons, List.not_mem_nil, or_false] at hℓ
      subst hℓ; exact hsub
  | _, _, _, .wk _ _ D => D.leaves_root
  | _, _, _, .esub _ _ D _ hv hvT => fun ℓ hℓ => by
      simp only [EvTy.leaves] at hℓ
      rcases (List.mem_append.mp hℓ) with h | h
      · rcases (List.mem_append.mp h) with h | h
        · exact EvTy.leaves_root D ℓ h
        · exact EvTy.leaves_root hv ℓ h
      · exact EvTy.leaves_root hvT ℓ h
  | _, _, _, .subst0 _ D _ hv => fun ℓ hℓ => by
      simp only [EvTy.leaves] at hℓ
      rcases (List.mem_append.mp hℓ) with h | h
      · exact EvTy.leaves_root D ℓ h
      · exact EvTy.leaves_root hv ℓ h
  | _, _, _, .substLet _ D _ hv => fun ℓ hℓ => by
      simp only [EvTy.leaves] at hℓ
      rcases (List.mem_append.mp hℓ) with h | h
      · exact EvTy.leaves_root D ℓ h
      · exact EvTy.leaves_root hv ℓ h
  | _, _, _, .var _ _ _ => fun _ hℓ => absurd hℓ (List.not_mem_nil _)
  | _, _, _, .sort _ => fun _ hℓ => absurd hℓ (List.not_mem_nil _)
  | _, _, _, .const _ _ _ _ _ _ => fun _ hℓ => absurd hℓ (List.not_mem_nil _)
  | _, _, _, .rety D c => fun ℓ hℓ => by
      simp only [EvTy.leaves, List.mem_append] at hℓ
      rcases hℓ with h | h
      · exact EvTy.leaves_root D ℓ h
      · exact EvTc.leaves_root c ℓ h

def EvTc.leaves_root :
    {Γ : LCtx} → {A B : Expr Nat} → (c : EvTc R Γ A B) →
    ∀ ℓ ∈ c.leaves, ∃ r ∈ R, SubEq ℓ r
  | _, _, _, .lit _ hsub => fun _ hℓ => by
      simp only [EvTc.leaves, List.mem_cons, List.not_mem_nil, or_false] at hℓ
      subst hℓ; exact hsub
  | _, _, _, .ofCv _ c => EvCv.leaves_root c
  | _, _, _, .refl _ _ => fun _ hℓ => absurd hℓ (List.not_mem_nil _)
  | _, _, _, .symm c => EvTc.leaves_root c
  | _, _, _, .trans c₁ c₂ => fun ℓ hℓ => by
      simp only [EvTc.leaves, List.mem_append] at hℓ
      rcases hℓ with h | h
      · exact EvTc.leaves_root c₁ ℓ h
      · exact EvTc.leaves_root c₂ ℓ h
  | _, _, _, .piCod _ hA c => fun ℓ hℓ => by
      simp only [EvTc.leaves, List.mem_append] at hℓ
      rcases hℓ with h | h
      · exact EvTy.leaves_root hA ℓ h
      · exact EvTc.leaves_root c ℓ h
  | _, _, _, .subst0 _ c _ hv => fun ℓ hℓ => by
      simp only [EvTc.leaves, List.mem_append] at hℓ
      rcases hℓ with h | h
      · exact EvTc.leaves_root c ℓ h
      · exact EvTy.leaves_root hv ℓ h
  | _, _, _, .substLet _ c _ hv => fun ℓ hℓ => by
      simp only [EvTc.leaves, List.mem_append] at hℓ
      rcases hℓ with h | h
      · exact EvTc.leaves_root c ℓ h
      · exact EvTy.leaves_root hv ℓ h
  | _, _, _, .wk _ _ h => EvTc.leaves_root h

def EvCv.leaves_root :
    {Γ : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ a b T) →
    ∀ ℓ ∈ c.leaves, ∃ r ∈ R, SubEq ℓ r
  | _, _, _, _, .lit _ hsub => fun _ hℓ => by
      simp only [EvCv.leaves, List.mem_cons, List.not_mem_nil, or_false] at hℓ
      subst hℓ; exact hsub
  | _, _, _, _, .refl D => EvTy.leaves_root D
  | _, _, _, _, .symm c => EvCv.leaves_root c
  | _, _, _, _, .trans c₁ c₂ => fun ℓ hℓ => by
      simp only [EvCv.leaves, List.mem_append] at hℓ
      rcases hℓ with h | h
      · exact EvCv.leaves_root c₁ ℓ h
      · exact EvCv.leaves_root c₂ ℓ h
  | _, _, _, _, .tyConv _ h hA => fun ℓ hℓ => by
      simp only [EvCv.leaves, List.mem_append] at hℓ
      rcases hℓ with hm | hm
      · exact EvCv.leaves_root h ℓ hm
      · exact EvCv.leaves_root hA ℓ hm
  | _, _, _, _, .wk _ _ h => EvCv.leaves_root h
  | _, _, _, _, .esub _ _ h _ hv hvT => fun ℓ hℓ => by
      simp only [EvCv.leaves] at hℓ
      rcases (List.mem_append.mp hℓ) with hm | hm
      · rcases (List.mem_append.mp hm) with hm | hm
        · exact EvCv.leaves_root h ℓ hm
        · exact EvTy.leaves_root hv ℓ hm
      · exact EvTy.leaves_root hvT ℓ hm
  | _, _, _, _, .subst0 _ h _ hv => fun ℓ hℓ => by
      simp only [EvCv.leaves] at hℓ
      rcases (List.mem_append.mp hℓ) with hm | hm
      · exact EvCv.leaves_root h ℓ hm
      · exact EvTy.leaves_root hv ℓ hm
  | _, _, _, _, .substLet _ h _ hv => fun ℓ hℓ => by
      simp only [EvCv.leaves] at hℓ
      rcases (List.mem_append.mp hℓ) with hm | hm
      · exact EvCv.leaves_root h ℓ hm
      · exact EvTy.leaves_root hv ℓ hm
  | _, _, _, _, .sorts _ _ _ => fun _ hℓ => absurd hℓ (List.not_mem_nil _)
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ =>
      fun _ hℓ => absurd hℓ (List.not_mem_nil _)
  | _, _, _, _, .rety h c => fun ℓ hℓ => by
      simp only [EvCv.leaves, List.mem_append] at hℓ
      rcases hℓ with hm | hm
      · exact EvCv.leaves_root h ℓ hm
      · exact EvTc.leaves_root c ℓ hm

end

/-! ### widening the root bundle -/

mutual

def EvTy.widen {R' : List (Jd E n)} (hRR' : ∀ r ∈ R, r ∈ R') :
    {Γ : LCtx} → {e T : Expr Nat} → EvTy R Γ e T → EvTy R' Γ e T
  | _, _, _, .lit d hsub =>
      .lit d (hsub.elim fun r hr => ⟨r, hRR' r hr.1, hr.2⟩)
  | _, _, _, .wk d c D => .wk d c (D.widen hRR')
  | _, _, _, .esub j u D hget hv hvT =>
      .esub j u (D.widen hRR') hget (hv.widen hRR') (hvT.widen hRR')
  | _, _, _, .subst0 j D hget hv => .subst0 j (D.widen hRR') hget (hv.widen hRR')
  | _, _, _, .substLet j D hget hv => .substLet j (D.widen hRR') hget (hv.widen hRR')
  | _, _, _, .var i A hlk => .var i A hlk
  | _, _, _, .sort l => .sort l
  | _, _, _, .const r ls m hres hlen hwf => .const r ls m hres hlen hwf
  | _, _, _, .rety D c => .rety (D.widen hRR') (c.widen hRR')

def EvTc.widen {R' : List (Jd E n)} (hRR' : ∀ r ∈ R, r ∈ R') :
    {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → EvTc R' Γ A B
  | _, _, _, .lit d hsub =>
      .lit d (hsub.elim fun r hr => ⟨r, hRR' r hr.1, hr.2⟩)
  | _, _, _, .ofCv u c => .ofCv u (c.widen hRR')
  | _, _, _, .refl Γ A => .refl Γ A
  | _, _, _, .symm c => .symm (c.widen hRR')
  | _, _, _, .trans c₁ c₂ => .trans (c₁.widen hRR') (c₂.widen hRR')
  | _, _, _, .piCod u hA c => .piCod u (hA.widen hRR') (c.widen hRR')
  | _, _, _, .subst0 j c hget hv =>
      .subst0 j (c.widen hRR') hget (hv.widen hRR')
  | _, _, _, .substLet j c hget hv =>
      .substLet j (c.widen hRR') hget (hv.widen hRR')
  | _, _, _, .wk d c h => .wk d c (h.widen hRR')

def EvCv.widen {R' : List (Jd E n)} (hRR' : ∀ r ∈ R, r ∈ R') :
    {Γ : LCtx} → {a b T : Expr Nat} → EvCv R Γ a b T → EvCv R' Γ a b T
  | _, _, _, _, .lit d hsub =>
      .lit d (hsub.elim fun r hr => ⟨r, hRR' r hr.1, hr.2⟩)
  | _, _, _, _, .refl D => .refl (D.widen hRR')
  | _, _, _, _, .symm c => .symm (c.widen hRR')
  | _, _, _, _, .trans c₁ c₂ => .trans (c₁.widen hRR') (c₂.widen hRR')
  | _, _, _, _, .tyConv u h hA => .tyConv u (h.widen hRR') (hA.widen hRR')
  | _, _, _, _, .wk d c h => .wk d c (h.widen hRR')
  | _, _, _, _, .esub j u h hget hv hvT =>
      .esub j u (h.widen hRR') hget (hv.widen hRR') (hvT.widen hRR')
  | _, _, _, _, .subst0 j h hget hv => .subst0 j (h.widen hRR') hget (hv.widen hRR')
  | _, _, _, _, .substLet j h hget hv => .substLet j (h.widen hRR') hget (hv.widen hRR')
  | _, _, _, _, .sorts l l' heq => .sorts l l' heq
  | _, _, _, _, .consts r ls ls' m hres hlen hwf hwf' heq =>
      .consts r ls ls' m hres hlen hwf hwf' heq
  | _, _, _, _, .rety h c => .rety (h.widen hRR') (c.widen hRR')

end

mutual

/-- widening leaves the leaves untouched. -/
def EvTy.leaves_widen {R' : List (Jd E n)} (hRR' : ∀ r ∈ R, r ∈ R') :
    {Γ : LCtx} → {e T : Expr Nat} → (D : EvTy R Γ e T) →
    (D.widen hRR').leaves = D.leaves
  | _, _, _, .lit _ _ => rfl
  | _, _, _, .wk _ _ D => D.leaves_widen hRR'
  | _, _, _, .esub _ _ D _ hv hvT => by
      simp only [EvTy.widen, EvTy.leaves, D.leaves_widen hRR',
        hv.leaves_widen hRR', hvT.leaves_widen hRR']
  | _, _, _, .subst0 _ D _ hv => by
      simp only [EvTy.widen, EvTy.leaves, D.leaves_widen hRR', hv.leaves_widen hRR']
  | _, _, _, .substLet _ D _ hv => by
      simp only [EvTy.widen, EvTy.leaves, D.leaves_widen hRR', hv.leaves_widen hRR']
  | _, _, _, .var _ _ _ => rfl
  | _, _, _, .sort _ => rfl
  | _, _, _, .const _ _ _ _ _ _ => rfl
  | _, _, _, .rety D c => by
      simp only [EvTy.widen, EvTy.leaves, EvTc.leaves, D.leaves_widen hRR',
        EvTc.leaves_widen hRR' c]

def EvTc.leaves_widen {R' : List (Jd E n)} (hRR' : ∀ r ∈ R, r ∈ R') :
    {Γ : LCtx} → {A B : Expr Nat} → (c : EvTc R Γ A B) →
    (c.widen hRR').leaves = c.leaves
  | _, _, _, .lit _ _ => rfl
  | _, _, _, .ofCv _ c => EvCv.leaves_widen hRR' c
  | _, _, _, .refl _ _ => rfl
  | _, _, _, .symm c => EvTc.leaves_widen hRR' c
  | _, _, _, .trans c₁ c₂ => by
      simp only [EvTc.widen, EvTc.leaves, EvTc.leaves_widen hRR' c₁,
        EvTc.leaves_widen hRR' c₂]
  | _, _, _, .piCod _ hA c => by
      simp only [EvTc.widen, EvTc.leaves, EvTy.leaves, hA.leaves_widen hRR',
        EvTc.leaves_widen hRR' c]
  | _, _, _, .subst0 _ c _ hv => by
      simp only [EvTc.widen, EvTc.leaves, EvTy.leaves,
        EvTc.leaves_widen hRR' c, hv.leaves_widen hRR']
  | _, _, _, .substLet _ c _ hv => by
      simp only [EvTc.widen, EvTc.leaves, EvTy.leaves,
        EvTc.leaves_widen hRR' c, hv.leaves_widen hRR']
  | _, _, _, .wk _ _ h => EvTc.leaves_widen hRR' h

def EvCv.leaves_widen {R' : List (Jd E n)} (hRR' : ∀ r ∈ R, r ∈ R') :
    {Γ : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ a b T) →
    (c.widen hRR').leaves = c.leaves
  | _, _, _, _, .lit _ _ => rfl
  | _, _, _, _, .refl D => D.leaves_widen hRR'
  | _, _, _, _, .symm c => EvCv.leaves_widen hRR' c
  | _, _, _, _, .trans c₁ c₂ => by
      simp only [EvCv.widen, EvCv.leaves, EvCv.leaves_widen hRR' c₁,
        EvCv.leaves_widen hRR' c₂]
  | _, _, _, _, .tyConv _ h hA => by
      simp only [EvCv.widen, EvCv.leaves, EvCv.leaves_widen hRR' h,
        EvCv.leaves_widen hRR' hA]
  | _, _, _, _, .wk _ _ h => EvCv.leaves_widen hRR' h
  | _, _, _, _, .esub _ _ h _ hv hvT => by
      simp only [EvCv.widen, EvCv.leaves, EvTy.leaves,
        EvCv.leaves_widen hRR' h, hv.leaves_widen hRR', hvT.leaves_widen hRR']
  | _, _, _, _, .subst0 _ h _ hv => by
      simp only [EvCv.widen, EvCv.leaves, EvCv.leaves_widen hRR' h, hv.leaves_widen hRR']
  | _, _, _, _, .substLet _ h _ hv => by
      simp only [EvCv.widen, EvCv.leaves, EvCv.leaves_widen hRR' h, hv.leaves_widen hRR']
  | _, _, _, _, .sorts _ _ _ => rfl
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ => rfl
  | _, _, _, _, .rety h c => by
      simp only [EvCv.widen, EvCv.leaves, EvTc.leaves,
        EvCv.leaves_widen hRR' h, EvTc.leaves_widen hRR' c]

end

/-! ### leaf-free `sorts` / `consts` endpoint helpers (#7035 ruling item 5, #7060 Q2 & 12:34Z) -/

/-- Left endpoint of `ConvT.sorts Γ l l' heq` at provenance level (`leaves = []`). -/
def EvTy.sortsLeft {Γ : LCtx} (l l' : Level) (_heq : eqN l l') :
    EvTy R Γ (.sort l) (.sort (.succ l)) :=
  .sort l

theorem EvTy.sortsLeft_leaves {Γ : LCtx} (l l' : Level) (heq : eqN l l') :
    (EvTy.sortsLeft (R := R) (Γ := Γ) l l' heq).leaves = [] := rfl

/-- Right endpoint of `ConvT.sorts Γ l l' heq` at the original LEFT index `.sort (.succ l)`
    (`leaves = []`). -/
def EvTy.sortsRight {Γ : LCtx} (l l' : Level) (heq : eqN l l') :
    EvTy R Γ (.sort l') (.sort (.succ l)) :=
  .rety (.sort l') (.ofCv (.succ (.succ l'))
    (.sorts (.succ l') (.succ l) (by intro ρ; simp only [eval, heq ρ])))

theorem EvTy.sortsRight_leaves {Γ : LCtx} (l l' : Level) (heq : eqN l l') :
    (EvTy.sortsRight (R := R) (Γ := Γ) l l' heq).leaves = [] := rfl

/-- Left endpoint of `ConvT.consts Γ r ls ls' m hres hlen hwf hwf' heq` at the original
    LEFT index `instantiateLevels ls m.mtype` (`leaves = []`). -/
def EvTy.constsLeft {Γ : LCtx} (r : Nat) (ls ls' : List Level)
    (m : CheckedMember) (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (_hwf' : levelsBounded n ls' = true) (_heq : eqNList ls ls') :
    EvTy R Γ (.const r ls) (instantiateLevels ls m.mtype) :=
  .const r ls m hres hlen hwf

theorem EvTy.constsLeft_leaves {Γ : LCtx} (r : Nat) (ls ls' : List Level)
    (m : CheckedMember) (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (heq : eqNList ls ls') :
    (EvTy.constsLeft (R := R) (Γ := Γ) r ls ls' m hres hlen hwf hwf' heq).leaves = [] := rfl

/-- Right endpoint of `ConvT.consts Γ r ls ls' m hres hlen hwf hwf' heq`, retyped to the
    original LEFT instantiation `instantiateLevels ls m.mtype` through lazy `EvTy.rety`
    with its leaves (`leaves = tc.leaves`, per cc ruling 12:34Z item 3). -/
def EvTy.constsRightWith {Γ : LCtx} (r : Nat) (ls ls' : List Level)
    (m : CheckedMember) (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (_hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (heq : eqNList ls ls')
    (tc : EvTc R Γ (instantiateLevels ls' m.mtype) (instantiateLevels ls m.mtype)) :
    EvTy R Γ (.const r ls') (instantiateLevels ls m.mtype) :=
  .rety (.const r ls' m hres ((eqNList_length ls ls' heq).symm.trans hlen) hwf') tc

theorem EvTy.constsRightWith_leaves {Γ : LCtx} (r : Nat) (ls ls' : List Level)
    (m : CheckedMember) (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (heq : eqNList ls ls')
    (tc : EvTc R Γ (instantiateLevels ls' m.mtype) (instantiateLevels ls m.mtype)) :
    (EvTy.constsRightWith (R := R) (Γ := Γ) r ls ls' m hres hlen hwf hwf' heq tc).leaves =
      tc.leaves := by
  simp only [EvTy.constsRightWith, EvTy.leaves, List.nil_append]

/-- Ancestry pin: any strict-leaf list below a childless root must be `[]`. -/
theorem empty_children_strict_leaves_nil {root : Jd E n} (hc : root.children = [])
    {L : List (Jd E n)} (hL : ∀ x ∈ L, SubOf x root) : L = [] := by
  cases L with
  | nil => rfl
  | cons x xs =>
      have hsub := hL x (.head _)
      have hfalse : ∀ {a b : Jd E n}, SubOf a b → b.children = [] → False := by
        intro a b hs hb
        induction hs with
        | child hm =>
            change _ ∈ _ at hm
            rw [hb] at hm
            exact List.not_mem_nil _ hm
        | trans _ _ _ ih₂ => exact ih₂ hb
      exact False.elim (hfalse hsub hc)

/-- O6 bridge (sealed, UNPROVED obligation for whoever builds plain →
    enriched): at a well-formed environment and context, every provenance
    typing has an enriched counterpart at the same endpoints. -/
def EvTyPBridge (E : ResolvedEnv) (n : Nat) : Prop :=
  EnvWfT E → ∀ {R : List (Jd E n)} {Γ : LCtx} {e T : Expr Nat},
    CtxWfT E n Γ → EvTy R Γ e T → Nonempty (Rcic.Syn.TyP E n Γ e T)

/-! ### drift guards: ConvPlus and this layer keep the same result indices -/

/-- `TyP.wk` and `EvTy.wk` land at the same indices. -/
theorem wk_shape_agree {R : List (Jd E n)} {Γ : LCtx} {e A : Expr Nat}
    (d : LocalDecl) (c : Nat)
    (Dp : Rcic.Syn.TyP E n Γ e A) (D : EvTy R Γ e A) :
    ∃ (_ : Rcic.Syn.TyP E n (insertAt d c Γ) (lift c 1 e) (lift c 1 A))
      (_ : EvTy R (insertAt d c Γ) (lift c 1 e) (lift c 1 A)), True :=
  ⟨.wk E n Γ e A d c Dp, .wk d c D, trivial⟩

/-- `TyP.esub` and `EvTy.esub` land at the same indices. -/
theorem esub_shape_agree {R : List (Jd E n)} {Γ : LCtx} {e A t v : Expr Nat}
    (j : Nat) (u : Level)
    (Dp : Rcic.Syn.TyP E n Γ e A) (hget : Γ[j]? = some (.assumption t))
    (hvp : Rcic.Syn.TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvTp : Rcic.Syn.TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (D : EvTy R Γ e A)
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : EvTy R (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    ∃ (_ : Rcic.Syn.TyP E n (substRemove v j Γ)
        (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) A))
      (_ : EvTy R (substRemove v j Γ)
        (instantiate j (lift 0 j v) e) (instantiate j (lift 0 j v) A)), True :=
  ⟨.esub E n Γ e A t v j u Dp hget hvp hvTp, .esub j u D hget hv hvT, trivial⟩

/-- `CvP.wk` and `EvCv.wk` land at the same indices. -/
theorem cvWk_shape_agree {R : List (Jd E n)} {Γ : LCtx} {a b T : Expr Nat}
    (d : LocalDecl) (c : Nat)
    (hp : Rcic.Syn.CvP E n Γ a b T) (h : EvCv R Γ a b T) :
    ∃ (_ : Rcic.Syn.CvP E n (insertAt d c Γ) (lift c 1 a) (lift c 1 b)
          (lift c 1 T))
      (_ : EvCv R (insertAt d c Γ) (lift c 1 a) (lift c 1 b) (lift c 1 T)),
        True :=
  ⟨.wk E n Γ a b T d c hp, .wk d c h, trivial⟩

/-- `CvP.esub` and `EvCv.esub` land at the same indices. -/
theorem cvEsub_shape_agree {R : List (Jd E n)} {Γ : LCtx} {a b T t v : Expr Nat}
    (j : Nat) (u : Level)
    (hp : Rcic.Syn.CvP E n Γ a b T) (hget : Γ[j]? = some (.assumption t))
    (hvp : Rcic.Syn.TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvTp : Rcic.Syn.TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (h : EvCv R Γ a b T)
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : EvTy R (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    ∃ (_ : Rcic.Syn.CvP E n (substRemove v j Γ)
        (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
        (instantiate j (lift 0 j v) T))
      (_ : EvCv R (substRemove v j Γ)
        (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
        (instantiate j (lift 0 j v) T)), True :=
  ⟨.esub E n Γ a b T t v j u hp hget hvp hvTp, .esub j u h hget hv hvT, trivial⟩

/-! ### non-vacuity pins -/

private def envCl : EnvClosed emptyEnv := fun _ _ h => Option.noConfusion h
private def envSS : EnvMembersSubstStable emptyEnv :=
  fun _ _ h => Option.noConfusion h

private def pinHs : HasTyT emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  pinSortT emptyEnv 0

private def pinHc : ConvT emptyEnv 0 [] (.sort (.succ .zero))
    (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sorts [] (.succ .zero) (.succ .zero) (fun _ => rfl)

private def pinHconv : HasTyT emptyEnv 0 [] (.sort .zero)
    (.sort (.succ .zero)) :=
  .conv [] (.sort .zero) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.succ (.succ .zero)) pinHs pinHc

/-- the fixture root bundle: the `.conv` atom and both of its children. -/
private def pinR : List (Jd emptyEnv 0) := [.ty pinHs, .cv pinHc, .ty pinHconv]

private def pinEvHs : EvTy pinR [] (.sort .zero) (.sort (.succ .zero)) :=
  .lit pinHs ⟨.ty pinHs,
    by show (Jd.ty pinHs : Jd emptyEnv 0) ∈
        ([Jd.ty pinHs, Jd.cv pinHc, Jd.ty pinHconv] : List (Jd emptyEnv 0))
       exact .head _,
    Or.inl rfl⟩

private def pinEvHc : EvCv pinR [] (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  .lit pinHc ⟨.ty pinHconv,
    by show (Jd.ty pinHconv : Jd emptyEnv 0) ∈
        ([Jd.ty pinHs, Jd.cv pinHc, Jd.ty pinHconv] : List (Jd emptyEnv 0))
       exact .tail _ (.tail _ (.head _)),
    Or.inr (.child (by
      show (Jd.cv pinHc : Jd emptyEnv 0) ∈
        ([Jd.ty pinHs, Jd.cv pinHc] : List (Jd emptyEnv 0))
      exact .tail _ (.head _)))⟩

/-- a `wk` node over a `lit` leaf at `emptyEnv`. -/
def pin_ev_wk : EvTy pinR [.assumption (.sort .zero)] (.sort .zero)
    (.sort (.succ .zero)) :=
  .wk (.assumption (.sort .zero)) 0 pinEvHs

/-- its materialization elaborates to a plain `HasTyT`. -/
def pin_ev_wk_val : HasTyT emptyEnv 0 [.assumption (.sort .zero)]
    (.sort .zero) (.sort (.succ .zero)) :=
  EvTy.val envCl envSS pin_ev_wk

/-- its only leaf is the `sort` literal. -/
theorem pin_ev_wk_leaves : pin_ev_wk.leaves = [Jd.ty pinHs] := rfl

/-- a `trans` of the same `lit` twice: the leaf is duplicated. -/
def pin_ev_dup : EvCv pinR [] (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort (.succ (.succ .zero))) :=
  .trans pinEvHc pinEvHc

theorem pin_ev_dup_leaves :
    pin_ev_dup.leaves = [Jd.cv pinHc, Jd.cv pinHc] := rfl

/-- a `rety` over a `lit` typing and an `ofCv` of a `lit` conversion. -/
def pin_ev_rety : EvTy pinR [] (.sort .zero) (.sort (.succ .zero)) :=
  .rety pinEvHs (.ofCv _ pinEvHc)

/-- the pin `rety`'s leaves are strict sub-derivations of the removed `.conv`
    atom — a `DMStep`, duplicates allowed. -/
theorem pin_ev_dm :
    DMStep (pin_ev_rety.leaves.map Jd.wt ++
      ([] : List (Jd emptyEnv 0)).map Jd.wt)
      (([Jd.ty pinHconv] : List (Jd emptyEnv 0)).map Jd.wt ++
        ([] : List (Jd emptyEnv 0)).map Jd.wt) :=
  dm_of_strictLeaves (X := [Jd.ty pinHconv]) (Z := [])
    (L := pin_ev_rety.leaves) (List.cons_ne_nil _ _)
    (fun ℓ hℓ => by
      rcases (List.mem_cons.mp hℓ) with rfl | hℓ
      · exact ⟨_, .head _, .child (by
          show (Jd.ty pinHs : Jd emptyEnv 0) ∈
            ([Jd.ty pinHs, Jd.cv pinHc] : List (Jd emptyEnv 0))
          exact .head _)⟩
      · rcases (List.mem_cons.mp hℓ) with rfl | hℓ
        · exact ⟨_, .head _, .child (by
            show (Jd.cv pinHc : Jd emptyEnv 0) ∈
              ([Jd.ty pinHs, Jd.cv pinHc] : List (Jd emptyEnv 0))
            exact .tail _ (.head _))⟩
        · exact absurd hℓ (List.not_mem_nil _))

/-- Syntactically distinct (`≠`) but `eqN`-equivalent universe levels for owner tests. -/
def pin_l₁ : Level := .succ .zero
def pin_l₂ : Level := .max (.succ .zero) .zero

theorem pin_levels_ne : pin_l₁ ≠ pin_l₂ := by decide

theorem pin_levels_eqN : eqN pin_l₁ pin_l₂ := fun _ => rfl

/-- Both `sortsLeft` and `sortsRight` at the original LEFT index `.sort (.succ pin_l₁)`
    over empty `R = []`, with `leaves = []`. -/
def pin_ev_sortsLeft : EvTy ([] : List (Jd emptyEnv 0)) []
    (.sort pin_l₁) (.sort (.succ pin_l₁)) :=
  EvTy.sortsLeft pin_l₁ pin_l₂ pin_levels_eqN

theorem pin_ev_sortsLeft_leaves : pin_ev_sortsLeft.leaves = [] := rfl

def pin_ev_sortsRight : EvTy ([] : List (Jd emptyEnv 0)) []
    (.sort pin_l₂) (.sort (.succ pin_l₁)) :=
  EvTy.sortsRight pin_l₁ pin_l₂ pin_levels_eqN

theorem pin_ev_sortsRight_leaves : pin_ev_sortsRight.leaves = [] := rfl

def pin_evCv_rety : EvCv ([] : List (Jd emptyEnv 0)) []
    (.sort pin_l₁) (.sort pin_l₂)
    (.sort (.succ pin_l₂)) :=
  .rety (.sorts pin_l₁ pin_l₂ pin_levels_eqN)
    (.ofCv (.succ (.succ pin_l₁))
      (.sorts (.succ pin_l₁) (.succ pin_l₂) (fun _ => rfl)))

theorem pin_evCv_rety_leaves : pin_evCv_rety.leaves = [] := rfl

/-! ### empty-leaf skeleton

An empty leaf list leaves only reflexivity, sort and constant level
conversions, and structure or substitution of one common replacement.
`.lit` is a singleton leaf, so it is not an empty-leaf β source. The
skeleton erases universe labels and keeps binder structure and de Bruijn
indices. `closure_claim = 0`. -/

/-- Term skeleton after erasing universe labels. -/
def exprSkel : Expr Nat → Expr Nat
  | .bvar i => .bvar i
  | .sort _ => .sort .zero
  | .const r _ => .const r []
  | .app f a => .app (exprSkel f) (exprSkel a)
  | .lam a b => .lam (exprSkel a) (exprSkel b)
  | .pi a b => .pi (exprSkel a) (exprSkel b)
  | .letE a v b => .letE (exprSkel a) (exprSkel v) (exprSkel b)
  | .lit t => .lit t

theorem exprSkel_lift (k n₀ : Nat) (e : Expr Nat) :
    exprSkel (lift k n₀ e) = lift k n₀ (exprSkel e) := by
  induction e generalizing k with
  | bvar i =>
      simp only [lift]
      split <;> rfl
  | sort _ => simp [lift, exprSkel]
  | const _ _ => simp [lift, exprSkel]
  | app _ _ ihf iha => simp [lift, exprSkel, ihf, iha]
  | lam _ _ iha ihb => simp [lift, exprSkel, iha, ihb]
  | pi _ _ iha ihb => simp [lift, exprSkel, iha, ihb]
  | letE _ _ _ iha ihv ihb => simp [lift, exprSkel, iha, ihv, ihb]
  | lit _ => simp [lift, exprSkel]

theorem exprSkel_instantiate (j : Nat) (v e : Expr Nat) :
    exprSkel (instantiate j v e) =
      instantiate j (exprSkel v) (exprSkel e) := by
  induction e generalizing j v with
  | bvar i =>
      simp only [instantiate]
      split
      · rfl
      · split <;> rfl
  | sort _ => simp [instantiate, exprSkel]
  | const _ _ => simp [instantiate, exprSkel]
  | app _ _ ihf iha => simp [instantiate, exprSkel, ihf, iha]
  | lam _ _ iha ihb =>
      simp only [instantiate, exprSkel, iha, ihb, exprSkel_lift]
  | pi _ _ iha ihb =>
      simp only [instantiate, exprSkel, iha, ihb, exprSkel_lift]
  | letE _ _ _ iha ihv ihb =>
      simp only [instantiate, exprSkel, iha, ihv, ihb, exprSkel_lift]
  | lit _ => simp [instantiate, exprSkel]

mutual

theorem evTc_empty_skel : {Γ : LCtx} → {A B : Expr Nat} → (c : EvTc R Γ A B) →
    c.leaves = [] → exprSkel A = exprSkel B
  | _, _, _, .lit _ _, h => False.elim (List.cons_ne_nil _ _ h)
  | _, _, _, .ofCv _ c, h => evCv_empty_skel c h
  | _, _, _, .refl _ _, _ => rfl
  | _, _, _, .symm c, h => (evTc_empty_skel c h).symm
  | _, _, _, .trans c₁ c₂, h => by
      obtain ⟨h₁, h₂⟩ := List.append_eq_nil.mp h
      exact (evTc_empty_skel c₁ h₁).trans (evTc_empty_skel c₂ h₂)
  | _, _, _, .piCod _ _ c, h => by
      obtain ⟨_, hc⟩ := List.append_eq_nil.mp h
      simp only [exprSkel, evTc_empty_skel c hc]
  | _, _, _, .subst0 _ c _ _, h => by
      obtain ⟨hc, _⟩ := List.append_eq_nil.mp h
      simp only [exprSkel_instantiate, evTc_empty_skel c hc]
  | _, _, _, .substLet _ c _ _, h => by
      obtain ⟨hc, _⟩ := List.append_eq_nil.mp h
      simp only [exprSkel_instantiate, evTc_empty_skel c hc]
  | _, _, _, .wk _ _ c, h => by
      simp only [exprSkel_lift, evTc_empty_skel c h]

theorem evCv_empty_skel : {Γ : LCtx} → {a b T : Expr Nat} →
    (c : EvCv R Γ a b T) → c.leaves = [] → exprSkel a = exprSkel b
  | _, _, _, _, .lit _ _, h => False.elim (List.cons_ne_nil _ _ h)
  | _, _, _, _, .refl _, _ => rfl
  | _, _, _, _, .symm c, h => (evCv_empty_skel c h).symm
  | _, _, _, _, .trans c₁ c₂, h => by
      obtain ⟨h₁, h₂⟩ := List.append_eq_nil.mp h
      exact (evCv_empty_skel c₁ h₁).trans (evCv_empty_skel c₂ h₂)
  | _, _, _, _, .tyConv _ c _, h => by
      obtain ⟨hc, _⟩ := List.append_eq_nil.mp h
      exact evCv_empty_skel c hc
  | _, _, _, _, .wk _ _ c, h => by
      simp only [exprSkel_lift, evCv_empty_skel c h]
  | _, _, _, _, .esub _ _ c _ _ _, h => by
      -- leaves are `(c ++ hv) ++ hvT`; the sort typing is not itself an append.
      obtain ⟨hcv, _⟩ := List.append_eq_nil.mp h
      obtain ⟨hc, _⟩ := List.append_eq_nil.mp hcv
      simp only [exprSkel_instantiate, evCv_empty_skel c hc]
  | _, _, _, _, .subst0 _ c _ _, h => by
      obtain ⟨hc, _⟩ := List.append_eq_nil.mp h
      simp only [exprSkel_instantiate, evCv_empty_skel c hc]
  | _, _, _, _, .substLet _ c _ _, h => by
      obtain ⟨hc, _⟩ := List.append_eq_nil.mp h
      simp only [exprSkel_instantiate, evCv_empty_skel c hc]
  | _, _, _, _, .sorts _ _ _, _ => rfl
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _, _ => rfl
  | _, _, _, _, .rety c _, h => by
      obtain ⟨hc, _⟩ := List.append_eq_nil.mp h
      exact evCv_empty_skel c hc

end

/-- `A = Sort 1`, `B₁ = Sort 1`, `B₂ = (λZ:A. Sort 1) (bvar 0)`. -/
def ctrlSort1 : Expr Nat := .sort (.succ .zero)
def ctrlLamId : Expr Nat := .lam ctrlSort1 (.bvar 0)
def ctrlCodSort : Expr Nat := ctrlSort1
def ctrlCodBeta : Expr Nat := .app (.lam ctrlSort1 ctrlSort1) (.bvar 0)
def ctrlPiSort : Expr Nat := .pi ctrlSort1 ctrlCodSort
def ctrlPiBeta : Expr Nat := .pi ctrlSort1 ctrlCodBeta

theorem ctrl_pi_skel_ne : exprSkel ctrlPiSort ≠ exprSkel ctrlPiBeta := by
  decide

/-- The two reflexive Π chains contribute no leaves, and their skeletons differ. -/
theorem ctrl_hc_leaves_empty (Γ : LCtx) :
    ((EvTc.refl (R := R) Γ ctrlPiSort).leaves ++
      (EvTc.refl (R := R) Γ ctrlPiBeta).leaves) = [] := rfl

theorem ctrl_empty_pi_refused {Γ : LCtx}
    (c : EvTc R Γ ctrlPiSort ctrlPiBeta) (h : c.leaves = []) : False :=
  ctrl_pi_skel_ne (evTc_empty_skel c h)

/-- Three syntactically different `=ₙ` sorts. A diagonal on equal targets misses them. -/
def ctrlSortMax : Expr Nat := .sort (.max .zero .zero)
def ctrlSortZero : Expr Nat := .sort .zero
def ctrlSortImax : Expr Nat := .sort (.imax .zero .zero)

theorem ctrl_three_sorts_distinct :
    ctrlSortMax ≠ ctrlSortZero ∧ ctrlSortMax ≠ ctrlSortImax ∧
      ctrlSortZero ≠ ctrlSortImax := by
  decide

theorem ctrl_three_sorts_eqN :
    eqN (.max .zero .zero) .zero ∧
      eqN (.max .zero .zero) (.imax .zero .zero) ∧
        eqN .zero (.imax .zero .zero) :=
  ⟨decEqN_sound _ _ (by decide), decEqN_sound _ _ (by decide),
    decEqN_sound _ _ (by decide)⟩

theorem ctrl_app_targets_ne :
    Expr.app ctrlLamId ctrlSortMax ≠ Expr.app ctrlLamId ctrlSortZero ∧
      Expr.app ctrlLamId ctrlSortMax ≠ Expr.app ctrlLamId ctrlSortImax ∧
        Expr.app ctrlLamId ctrlSortZero ≠ Expr.app ctrlLamId ctrlSortImax := by
  decide

/-- `B = bvar 0`. Instantiating a sort is the sort. -/
def ctrlInstB : Expr Nat := .bvar 0

theorem ctrl_inst_max : instantiate0 ctrlSortMax ctrlInstB = ctrlSortMax := rfl
theorem ctrl_inst_zero : instantiate0 ctrlSortZero ctrlInstB = ctrlSortZero := rfl

/-- Sort instantiation inside the leaf budget: `EvCv.sorts`, leaves `[]`. -/
def ctrlInstSort (Γ : LCtx) : EvTc R Γ ctrlSortMax ctrlSortZero :=
  .ofCv (.succ (.max .zero .zero))
    (.sorts (.max .zero .zero) .zero
      (decEqN_sound _ _ (by decide : decEqN (.max .zero .zero) .zero = true)))

theorem ctrlInstSort_leaves (Γ : LCtx) :
    (ctrlInstSort (R := R) Γ).leaves = [] := by
  simp [ctrlInstSort, EvTc.leaves, EvCv.leaves]

#print axioms EvTy
#print axioms EvTc
#print axioms EvCv
#print axioms EvTy.val
#print axioms EvTc.val
#print axioms EvCv.val
#print axioms EvTy.leaves
#print axioms EvTc.leaves
#print axioms EvCv.leaves
#print axioms EvTy.size
#print axioms EvTc.size
#print axioms EvCv.size
#print axioms EvTy.leaves_root
#print axioms EvTc.leaves_root
#print axioms EvCv.leaves_root
#print axioms EvTy.widen
#print axioms EvTc.widen
#print axioms EvCv.widen
#print axioms EvTy.leaves_widen
#print axioms EvTc.leaves_widen
#print axioms EvCv.leaves_widen
#print axioms EvTy.sortsLeft
#print axioms EvTy.sortsLeft_leaves
#print axioms EvTy.sortsRight
#print axioms EvTy.sortsRight_leaves
#print axioms EvTy.constsLeft
#print axioms EvTy.constsLeft_leaves
#print axioms EvTy.constsRightWith
#print axioms EvTy.constsRightWith_leaves
#print axioms empty_children_strict_leaves_nil
#print axioms EvTyPBridge
#print axioms wk_shape_agree
#print axioms esub_shape_agree
#print axioms cvWk_shape_agree
#print axioms cvEsub_shape_agree
#print axioms pin_ev_wk
#print axioms pin_ev_wk_val
#print axioms pin_ev_wk_leaves
#print axioms pin_ev_dup
#print axioms pin_ev_dup_leaves
#print axioms pin_ev_rety
#print axioms pin_ev_dm
#print axioms pin_l₁
#print axioms pin_l₂
#print axioms pin_levels_ne
#print axioms pin_levels_eqN
#print axioms pin_ev_sortsLeft
#print axioms pin_ev_sortsLeft_leaves
#print axioms pin_ev_sortsRight
#print axioms pin_ev_sortsRight_leaves
#print axioms pin_evCv_rety
#print axioms pin_evCv_rety_leaves
#print axioms exprSkel
#print axioms exprSkel_lift
#print axioms exprSkel_instantiate
#print axioms evTc_empty_skel
#print axioms evCv_empty_skel
#print axioms ctrl_pi_skel_ne
#print axioms ctrl_hc_leaves_empty
#print axioms ctrl_empty_pi_refused
#print axioms ctrl_three_sorts_distinct
#print axioms ctrl_three_sorts_eqN
#print axioms ctrl_app_targets_ne
#print axioms ctrl_inst_max
#print axioms ctrl_inst_zero
#print axioms ctrlInstSort
#print axioms ctrlInstSort_leaves

end Rcic.Declarative.F8Measure

