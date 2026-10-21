import rcic.RcicF8DTileBase
import rcic.RcicF8EvInvT
import rcic.RcicF8XStruct
import rcic.RcicF8CtxConvVar
import rcic.RcicA2SortSupport

/-!
# `RcicF8DTileStep` — the D tile, slice D1 (the {proofIndex, structPi} step diamond)

S0 §2 (#7060), cc ruling 11:44Z (Q1). The certified step diamond `DStepDiamondWf` of
`RcicF8DTileBase` for the two landed `EvPar` constructors, hence `DProcWf` / `DContractWf`
for the landed carrier.

**Reading a transported step.** A `DStep` is an `EvPar` step under the star's lazy transports.
To BUILD the closing step the diamond reads the base payload's components through those
transports, each component staying a lazy transport (`EvTy.wk`, `EvTc.wk`, `EvCv.wk`,
`EvTy.rety`, `EvTc.trans`): `EvPar.readConv` / `EvPar.readWk`. The input stars are never
rewritten (`EvParStar.spine` keeps every `.conv` / `.wk` as a `DStep` wrapper) and no carrier
constructor is added; the reader only feeds the diamond's OUTPUT. Leaves are preserved
exactly by `readWk` and up to the chain's own leaves by `readConv`.

**Case table** (S0 §2).
* `proofIndex p₁ × s₂` (any `s₂`): one step `b ⇒ c` by `.proofIndex` with `p₁`'s proposition
  and chain, `leftTy := p₁.rightTy`, `rightTy := s₂.rightTy`; zero steps on the right. No
  hypothesis at all.
* `s₁ × proofIndex p₂`: symmetric.
* `structPi p₁ × structPi p₂` (`Π A B ⇒ Π A₁ B₁`, `Π A B ⇒ Π A₂ B₂`): the forward join
  `Π A₁ B₁ ⇒ Π A₂ B₂` at `p₂`'s levels, reusing `p₂.hrt` / `p₂.idx`; zero steps on the
  right. The domain chain is `p₁.hc⁻¹ · p₂.hc`, the codomain chain `p₁.hcB⁻¹ · p₂.hcB` moved
  under the binder `A₁` by D-VAR (`EvTy.var`, `EvCv.wk`, `EvCv.esub`; `cvCtxConvVar`), and
  the level alignments are leaf-less `EvCv.sorts` retypings (the carrier amendment
  `G-D-EVCV-SORT`, cc Q2). The four `=ₙ` facts are Prop-level, from `SortUnique E n` at
  materialized typings in well-formed contexts (`EnvWfT E`, `CtxWfT E n Γ`).

**Hypotheses.** `hW : EnvWfT E` and `su : F8A2Support.SortUnique E n` at the module boundary
(the same named premise StructPi / SP-1 and A-2 take; it is NOT discharged here — see the
circularity guard of `RcicSortUniqueRows`, whose `sortUnique_of_inScope` is an inhabitant at
every `InScope` environment and must not be imported into this construction). `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### index cast for provenance conversions and steps -/

def EvCv.dcast {Γ Γ' : LCtx} {a a' b b' T T' : Expr Nat} (hΓ : Γ = Γ') (ha : a = a')
    (hb : b = b') (hT : T = T') (c : EvCv R Γ a b T) : EvCv R Γ' a' b' T' := by
  subst hΓ; subst ha; subst hb; subst hT; exact c

theorem EvCv.dcast_leaves {Γ Γ' : LCtx} {a a' b b' T T' : Expr Nat} (hΓ : Γ = Γ')
    (ha : a = a') (hb : b = b') (hT : T = T') (c : EvCv R Γ a b T) :
    (EvCv.dcast hΓ ha hb hT c).leaves = c.leaves := by
  subst hΓ; subst ha; subst hb; subst hT; rfl

def EvPar.castR {Γ : LCtx} {a b b' T : Expr Nat} (hb : b = b') (h : EvPar R Γ a b T) :
    EvPar R Γ a b' T := by
  subst hb; exact h

theorem EvPar.castR_leaves {Γ : LCtx} {a b b' T : Expr Nat} (hb : b = b')
    (h : EvPar R Γ a b T) : (h.castR hb).leaves = h.leaves := by
  subst hb; rfl

def EvPar.dcast {Γ Γ' : LCtx} {a a' b b' T T' : Expr Nat} (hΓ : Γ = Γ') (ha : a = a')
    (hb : b = b') (hT : T = T') (h : EvPar R Γ a b T) : EvPar R Γ' a' b' T' := by
  subst hΓ; subst ha; subst hb; subst hT; exact h

theorem EvPar.dcast_leaves {Γ Γ' : LCtx} {a a' b b' T T' : Expr Nat} (hΓ : Γ = Γ')
    (ha : a = a') (hb : b = b') (hT : T = T') (h : EvPar R Γ a b T) :
    (EvPar.dcast hΓ ha hb hT h).leaves = h.leaves := by
  subst hΓ; subst ha; subst hb; subst hT; rfl

def EvTy.wkPrefix : (Δ : LCtx) → {Γ : LCtx} → {e T : Expr Nat} →
    EvTy R Γ e T → EvTy R (Δ ++ Γ) (lift 0 Δ.length e) (lift 0 Δ.length T)
  | [], _, _, _, h => EvTy.cast rfl (lift_zero 0 _).symm (lift_zero 0 _).symm h
  | d :: Δ, _, e, T, h =>
      EvTy.cast rfl (lift_zero_succ Δ.length e) (lift_zero_succ Δ.length T)
        (.wk d 0 (EvTy.wkPrefix Δ h))

theorem EvTy.wkPrefix_leaves : (Δ : LCtx) → {Γ : LCtx} → {e T : Expr Nat} →
    (h : EvTy R Γ e T) → (EvTy.wkPrefix Δ h).leaves = h.leaves
  | [], _, _, _, _ => by simp only [EvTy.wkPrefix, EvTy.cast_leaves]
  | d :: Δ, _, _, _, h => by
      simp only [EvTy.wkPrefix, EvTy.cast_leaves, EvTy.leaves, EvTy.wkPrefix_leaves Δ h]

def DStep.dcast {Γ Γ' : LCtx} {a a' b b' T T' : Expr Nat}
    (hΓ : Γ = Γ') (ha : a = a') (hb : b = b') (hT : T = T') (s : DStep R Γ a b T) :
    DStep R Γ' a' b' T' := by
  subst hΓ; subst ha; subst hb; subst hT; exact s

theorem DStep.dcast_leaves {Γ Γ' : LCtx} {a a' b b' T T' : Expr Nat}
    (hΓ : Γ = Γ') (ha : a = a') (hb : b = b') (hT : T = T') (s : DStep R Γ a b T) :
    (DStep.dcast hΓ ha hb hT s).leaves = s.leaves := by
  subst hΓ; subst ha; subst hb; subst hT; rfl

def DStep.wkPrefix : (Δ : LCtx) → {Γ : LCtx} → {a b T : Expr Nat} →
    DStep R Γ a b T →
    DStep R (Δ ++ Γ) (lift 0 Δ.length a) (lift 0 Δ.length b) (lift 0 Δ.length T)
  | [], _, _, _, _, s =>
      DStep.dcast rfl (lift_zero 0 _).symm (lift_zero 0 _).symm (lift_zero 0 _).symm s
  | d :: Δ, _, a, b, T, s =>
      DStep.dcast rfl (lift_zero_succ Δ.length a) (lift_zero_succ Δ.length b)
        (lift_zero_succ Δ.length T) (.wk d 0 (DStep.wkPrefix Δ s))

theorem DStep.wkPrefix_leaves : (Δ : LCtx) → {Γ : LCtx} → {a b T : Expr Nat} →
    (s : DStep R Γ a b T) → (DStep.wkPrefix Δ s).leaves = s.leaves
  | [], _, _, _, _, _ => by simp only [DStep.wkPrefix, DStep.dcast_leaves]
  | d :: Δ, _, _, _, _, s => by
      simp only [DStep.wkPrefix, DStep.dcast_leaves, DStep.leaves, DStep.wkPrefix_leaves Δ s]

def DOpt.dcast {Γ Γ' : LCtx} {b b' d d' T T' : Expr Nat}
    (hΓ : Γ = Γ') (hb : b = b') (hd : d = d') (hT : T = T') (o : DOpt R Γ b d T) :
    DOpt R Γ' b' d' T' := by
  subst hΓ; subst hb; subst hd; subst hT; exact o

theorem DOpt.dcast_leaves {Γ Γ' : LCtx} {b b' d d' T T' : Expr Nat}
    (hΓ : Γ = Γ') (hb : b = b') (hd : d = d') (hT : T = T') (o : DOpt R Γ b d T) :
    (DOpt.dcast hΓ hb hd hT o).leaves = o.leaves := by
  subst hΓ; subst hb; subst hd; subst hT; rfl

def DOpt.wkPrefix (Δ : LCtx) {Γ : LCtx} {b d T : Expr Nat} :
    DOpt R Γ b d T → DOpt R (Δ ++ Γ) (lift 0 Δ.length b) (lift 0 Δ.length d) (lift 0 Δ.length T)
  | .stay h => .stay (EvTy.wkPrefix Δ h)
  | .step s => .step (DStep.wkPrefix Δ s)

theorem DOpt.wkPrefix_leaves (Δ : LCtx) {Γ : LCtx} {b d T : Expr Nat}
    (o : DOpt R Γ b d T) : (o.wkPrefix Δ).leaves = o.leaves := by
  cases o <;> simp only [DOpt.wkPrefix, DOpt.leaves, EvTy.wkPrefix_leaves, DStep.wkPrefix_leaves]

def DOpt.conv {Γ : LCtx} {b d T T' : Expr Nat} (c : EvTc R Γ T T') :
    DOpt R Γ b d T → DOpt R Γ b d T'
  | .stay h => .stay (.rety h c)
  | .step s => .step (.conv s c)

theorem DOpt.conv_leaves {Γ : LCtx} {b d T T' : Expr Nat} (c : EvTc R Γ T T')
    (o : DOpt R Γ b d T) : (o.conv c).leaves = o.leaves ++ c.leaves := by
  cases o <;> rfl

/-! ### reading a transported step (output construction only) -/

/-- the base payload read through an index chain. -/
def EvPar.readConv {Γ : LCtx} {a b T T' : Expr Nat} :
    EvPar R Γ a b T → EvTc R Γ T T' → EvPar R Γ a b T'
  | .proofIndex p, c => .proofIndex
      { proposition := p.proposition, propTy := p.propTy, chain := .trans (.symm c) p.chain,
        leftTy := .rety p.leftTy c, rightTy := .rety p.rightTy c }
  | .structPi p, c => .structPi
      { u := p.u, v := p.v, hA := p.hA, hc := p.hc, hB := p.hB, hcB := p.hcB, hrt := p.hrt,
        idx := .trans p.idx c }
  | .sortEq p, c => .sortEq
      { T₀ := p.T₀, h := p.h, hl := p.hl, hr := p.hr, idx := .trans p.idx c }
  | .consts p, c => .consts
      { T₀ := p.T₀, h := p.h, hl := p.hl, hr := p.hr, idx := .trans p.idx c }
  | .lit p, c => .lit
      { T₀ := p.T₀, hexp := p.hexp, idx := .trans p.idx c }
  | .refl p, c => .refl
      { T₀ := p.T₀, h := p.h, idx := .trans p.idx c }

theorem EvPar.readConv_leaves {Γ : LCtx} {a b T T' : Expr Nat} :
    (D : EvPar R Γ a b T) → (c : EvTc R Γ T T') →
    ∀ ℓ ∈ (D.readConv c).leaves, ℓ ∈ D.leaves ++ c.leaves
  | .proofIndex p, c => fun ℓ hℓ => by
      simp only [EvPar.readConv, EvPar.leaves, ProofIndexPayload.leaves, EvTc.leaves,
        EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with ((h | (h | h)) | (h | h)) | (h | h)
      · exact .inl (.inl (.inl (.inl h)))
      · exact .inr h
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inl (.inl (.inr h))
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h
  | .structPi p, c => fun ℓ hℓ => by
      simp only [EvPar.readConv, EvPar.leaves, StructPiPayload.leaves, EvTc.leaves,
        List.mem_append] at hℓ ⊢
      rcases hℓ with (((((h | h) | h) | h) | h) | (h | h))
      · exact .inl (.inl (.inl (.inl (.inl (.inl h)))))
      · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
      · exact .inl (.inl (.inl (.inl (.inr h))))
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
      · exact .inr h
  | .sortEq p, c => fun ℓ hℓ => by
      simp only [EvPar.readConv, EvPar.leaves, SortEqPayload.leaves, EvTc.leaves,
        List.mem_append] at hℓ ⊢
      rcases hℓ with (h | h) | (h | h)
      · exact .inl (.inl (.inl h))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
      · exact .inr h
  | .consts p, c => fun ℓ hℓ => by
      simp only [EvPar.readConv, EvPar.leaves, ConstsPayload.leaves, EvTc.leaves,
        List.mem_append] at hℓ ⊢
      rcases hℓ with (h | h) | (h | h)
      · exact .inl (.inl (.inl h))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
      · exact .inr h
  | .lit p, c => fun ℓ hℓ => by
      simp only [EvPar.readConv, EvPar.leaves, LitPayload.leaves, EvTc.leaves,
        List.mem_append] at hℓ ⊢
      rcases hℓ with h | (h | h)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h
  | .refl p, c => fun ℓ hℓ => by
      simp only [EvPar.readConv, EvPar.leaves, ReflPayload.leaves, EvTc.leaves,
        List.mem_append] at hℓ ⊢
      rcases hℓ with h | (h | h)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h

/-- the base payload read under a weakening, componentwise by the lazy `wk`s. -/
def EvPar.readWk (d : LocalDecl) (k : Nat) {Γ : LCtx} {a b T : Expr Nat} :
    EvPar R Γ a b T → EvPar R (insertAt d k Γ) (lift k 1 a) (lift k 1 b) (lift k 1 T)
  | .proofIndex p => .proofIndex
      { proposition := lift k 1 p.proposition, propTy := .wk d k p.propTy,
        chain := .wk d k p.chain, leftTy := .wk d k p.leftTy, rightTy := .wk d k p.rightTy }
  | .structPi p => .structPi
      { u := p.u, v := p.v, hA := .wk d k p.hA, hc := .wk d k p.hc,
        hB := .wk d (k + 1) p.hB, hcB := .wk d (k + 1) p.hcB, hrt := .wk d k p.hrt,
        idx := .wk d k p.idx }
  | .sortEq p => .sortEq
      { T₀ := lift k 1 p.T₀, h := p.h, hl := .wk d k p.hl, hr := .wk d k p.hr,
        idx := .wk d k p.idx }
  | .consts p => .consts
      { T₀ := lift k 1 p.T₀, h := p.h, hl := .wk d k p.hl, hr := .wk d k p.hr,
        idx := .wk d k p.idx }
  | .lit (t := t) p =>
      EvPar.castR (natExpand_lift k 1 t).symm
        (.lit { T₀ := lift k 1 p.T₀,
                hexp := EvTy.cast rfl (natExpand_lift k 1 t) rfl (.wk d k p.hexp),
                idx := .wk d k p.idx })
  | .refl p => .refl
      { T₀ := lift k 1 p.T₀, h := .wk d k p.h, idx := .wk d k p.idx }

/-- `readWk` preserves the leaves EXACTLY. -/
theorem EvPar.readWk_leaves (d : LocalDecl) (k : Nat) {Γ : LCtx} {a b T : Expr Nat} :
    (D : EvPar R Γ a b T) → (D.readWk d k).leaves = D.leaves
  | .proofIndex p => by
      simp only [EvPar.readWk, EvPar.leaves, ProofIndexPayload.leaves, EvTc.leaves,
        EvTy.leaves]
  | .structPi p => by
      simp only [EvPar.readWk, EvPar.leaves, StructPiPayload.leaves, EvTc.leaves,
        EvTy.leaves, EvCv.leaves]
  | .sortEq p => by
      simp only [EvPar.readWk, EvPar.leaves, SortEqPayload.leaves, EvTc.leaves,
        EvTy.leaves]
  | .consts p => by
      simp only [EvPar.readWk, EvPar.leaves, ConstsPayload.leaves, EvTc.leaves,
        EvTy.leaves]
  | .lit p => by
      simp only [EvPar.readWk, EvPar.castR_leaves]
      simp only [EvPar.leaves, LitPayload.leaves, EvTy.cast_leaves, EvTc.leaves, EvTy.leaves]
  | .refl p => by
      simp only [EvPar.readWk, EvPar.leaves, ReflPayload.leaves, EvTc.leaves, EvTy.leaves]

/-- the base payload read under an assumption substitution, componentwise by the lazy
    `subst0`s (the codomain pieces one binder deeper). -/
def EvPar.readSubst0 {Γ : LCtx} {t v : Expr Nat} (j : Nat) (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) : {a b T : Expr Nat} →
    EvPar R Γ a b T → EvPar R (substRemove v j Γ) (instantiate j (lift 0 j v) a)
      (instantiate j (lift 0 j v) b) (instantiate j (lift 0 j v) T)
  | _, _, _, .proofIndex p => .proofIndex
      { proposition := instantiate j (lift 0 j v) p.proposition,
        propTy := .subst0 j p.propTy hget hv, chain := .subst0 j p.chain hget hv,
        leftTy := .subst0 j p.leftTy hget hv, rightTy := .subst0 j p.rightTy hget hv }
  | _, _, _, @EvPar.structPi _ _ _ _ A B A' B' _ p =>
      EvPar.structPi (A := instantiate j (lift 0 j v) A)
        (B := instantiate (j + 1) (lift 0 1 (lift 0 j v)) B)
        (A' := instantiate j (lift 0 j v) A')
        (B' := instantiate (j + 1) (lift 0 1 (lift 0 j v)) B')
        { u := p.u, v := p.v, hA := .subst0 j p.hA hget hv, hc := .subst0 j p.hc hget hv,
          hB := EvTy.cast rfl
            (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v]) rfl
            (.subst0 (j + 1) p.hB (by simpa using hget) (substBinderArg (d := .assumption A) hv)),
          hcB := EvCv.dcast rfl
            (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v])
            (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) v]) rfl
            (.subst0 (j + 1) p.hcB (by simpa using hget) (substBinderArg (d := .assumption A) hv)),
          hrt := .subst0 j p.hrt hget hv, idx := .subst0 j p.idx hget hv }

  | _, _, _, .sortEq p => .sortEq
      { T₀ := instantiate j (lift 0 j v) p.T₀, h := p.h,
        hl := .subst0 j p.hl hget hv, hr := .subst0 j p.hr hget hv,
        idx := .subst0 j p.idx hget hv }
  | _, _, _, .consts p => .consts
      { T₀ := instantiate j (lift 0 j v) p.T₀, h := p.h,
        hl := .subst0 j p.hl hget hv, hr := .subst0 j p.hr hget hv,
        idx := .subst0 j p.idx hget hv }
  | _, _, _, .lit (t := a) p =>
      EvPar.castR (natExpand_instantiate j (lift 0 j v) a).symm
        (.lit { T₀ := instantiate j (lift 0 j v) p.T₀,
                hexp := EvTy.cast rfl (natExpand_instantiate j (lift 0 j v) a) rfl
                  (.subst0 j p.hexp hget hv),
                idx := .subst0 j p.idx hget hv })
  | _, _, _, .refl p => .refl
      { T₀ := instantiate j (lift 0 j v) p.T₀,
        h := .subst0 j p.h hget hv,
        idx := .subst0 j p.idx hget hv }

theorem EvPar.readSubst0_leaves {Γ : LCtx} {t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) : {a b T : Expr Nat} →
    (D : EvPar R Γ a b T) → ∀ ℓ ∈ (D.readSubst0 j hget hv).leaves, ℓ ∈ D.leaves ++ hv.leaves
  | _, _, _, .proofIndex p => fun ℓ hℓ => by
      simp only [EvPar.readSubst0, EvPar.leaves, ProofIndexPayload.leaves, EvTc.leaves,
        EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with (((h | h) | (h | h)) | (h | h)) | (h | h)
      · exact .inl (.inl (.inl (.inl h)))
      · exact .inr h
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h
  | _, _, _, .structPi p => fun ℓ hℓ => by
      simp only [EvPar.readSubst0, EvPar.leaves, StructPiPayload.leaves, EvTc.leaves,
        EvTy.leaves, EvCv.leaves, EvTy.cast_leaves, EvCv.dcast_leaves, substBinderArg_leaves,
        List.mem_append] at hℓ ⊢
      rcases hℓ with (((((h | h) | (h | h)) | (h | h)) | (h | h)) | (h | h)) | (h | h)
      · exact .inl (.inl (.inl (.inl (.inl (.inl h)))))
      · exact .inr h
      · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
      · exact .inr h
      · exact .inl (.inl (.inl (.inl (.inr h))))
      · exact .inr h
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h

  | _, _, _, .sortEq p => fun ℓ hℓ => by
      simp only [EvPar.readSubst0, EvPar.leaves, SortEqPayload.leaves, EvTc.leaves,
        EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with ((h | h) | (h | h)) | (h | h)
      · exact .inl (.inl (.inl h))
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h
  | _, _, _, .consts p => fun ℓ hℓ => by
      simp only [EvPar.readSubst0, EvPar.leaves, ConstsPayload.leaves, EvTc.leaves,
        EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with ((h | h) | (h | h)) | (h | h)
      · exact .inl (.inl (.inl h))
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h
  | _, _, _, .lit p => fun ℓ hℓ => by
      simp only [EvPar.readSubst0, EvPar.castR_leaves] at hℓ
      simp only [EvPar.leaves, LitPayload.leaves, EvTy.cast_leaves, EvTc.leaves,
        EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with (h | h) | (h | h)
      · exact .inl (.inl h)
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h
  | _, _, _, .refl p => fun ℓ hℓ => by
      simp only [EvPar.readSubst0, EvPar.leaves, ReflPayload.leaves, EvTc.leaves,
        EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with (h | h) | (h | h)
      · exact .inl (.inl h)
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h

/-- the let twin. -/
def EvPar.readSubstLet {Γ : LCtx} {t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) : {a b T : Expr Nat} →
    EvPar R Γ a b T → EvPar R (substRemove w j Γ) (instantiate j (lift 0 j w) a)
      (instantiate j (lift 0 j w) b) (instantiate j (lift 0 j w) T)
  | _, _, _, .proofIndex p => .proofIndex
      { proposition := instantiate j (lift 0 j w) p.proposition,
        propTy := .substLet j p.propTy hget hv, chain := .substLet j p.chain hget hv,
        leftTy := .substLet j p.leftTy hget hv, rightTy := .substLet j p.rightTy hget hv }
  | _, _, _, @EvPar.structPi _ _ _ _ A B A' B' _ p =>
      EvPar.structPi (A := instantiate j (lift 0 j w) A)
        (B := instantiate (j + 1) (lift 0 1 (lift 0 j w)) B)
        (A' := instantiate j (lift 0 j w) A')
        (B' := instantiate (j + 1) (lift 0 1 (lift 0 j w)) B')
        { u := p.u, v := p.v, hA := .substLet j p.hA hget hv, hc := .substLet j p.hc hget hv,
          hB := EvTy.cast rfl
            (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w]) rfl
            (.substLet (j + 1) p.hB (by simpa using hget)
              (substBinderArg (d := .assumption A) hv)),
          hcB := EvCv.dcast rfl
            (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w])
            (by rw [lift_lift_merge 1 j 0 0 (Nat.le_refl 0) (Nat.zero_le j) w]) rfl
            (.substLet (j + 1) p.hcB (by simpa using hget)
              (substBinderArg (d := .assumption A) hv)),
          hrt := .substLet j p.hrt hget hv, idx := .substLet j p.idx hget hv }

  | _, _, _, .sortEq p => .sortEq
      { T₀ := instantiate j (lift 0 j w) p.T₀, h := p.h,
        hl := .substLet j p.hl hget hv, hr := .substLet j p.hr hget hv,
        idx := .substLet j p.idx hget hv }
  | _, _, _, .consts p => .consts
      { T₀ := instantiate j (lift 0 j w) p.T₀, h := p.h,
        hl := .substLet j p.hl hget hv, hr := .substLet j p.hr hget hv,
        idx := .substLet j p.idx hget hv }
  | _, _, _, .lit (t := a) p =>
      EvPar.castR (natExpand_instantiate j (lift 0 j w) a).symm
        (.lit { T₀ := instantiate j (lift 0 j w) p.T₀,
                hexp := EvTy.cast rfl (natExpand_instantiate j (lift 0 j w) a) rfl
                  (.substLet j p.hexp hget hv),
                idx := .substLet j p.idx hget hv })
  | _, _, _, .refl p => .refl
      { T₀ := instantiate j (lift 0 j w) p.T₀,
        h := .substLet j p.h hget hv,
        idx := .substLet j p.idx hget hv }

theorem EvPar.readSubstLet_leaves {Γ : LCtx} {t w : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.letBinding t w))
    (hv : EvTy R (substRemove w j Γ) (lift 0 j w) (lift 0 j t)) : {a b T : Expr Nat} →
    (D : EvPar R Γ a b T) → ∀ ℓ ∈ (D.readSubstLet j hget hv).leaves, ℓ ∈ D.leaves ++ hv.leaves
  | _, _, _, .proofIndex p => fun ℓ hℓ => by
      simp only [EvPar.readSubstLet, EvPar.leaves, ProofIndexPayload.leaves, EvTc.leaves,
        EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with (((h | h) | (h | h)) | (h | h)) | (h | h)
      · exact .inl (.inl (.inl (.inl h)))
      · exact .inr h
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h
  | _, _, _, .structPi p => fun ℓ hℓ => by
      simp only [EvPar.readSubstLet, EvPar.leaves, StructPiPayload.leaves, EvTc.leaves,
        EvTy.leaves, EvCv.leaves, EvTy.cast_leaves, EvCv.dcast_leaves, substBinderArg_leaves,
        List.mem_append] at hℓ ⊢
      rcases hℓ with (((((h | h) | (h | h)) | (h | h)) | (h | h)) | (h | h)) | (h | h)
      · exact .inl (.inl (.inl (.inl (.inl (.inl h)))))
      · exact .inr h
      · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
      · exact .inr h
      · exact .inl (.inl (.inl (.inl (.inr h))))
      · exact .inr h
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h

  | _, _, _, .sortEq p => fun ℓ hℓ => by
      simp only [EvPar.readSubstLet, EvPar.leaves, SortEqPayload.leaves, EvTc.leaves,
        EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with ((h | h) | (h | h)) | (h | h)
      · exact .inl (.inl (.inl h))
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h
  | _, _, _, .consts p => fun ℓ hℓ => by
      simp only [EvPar.readSubstLet, EvPar.leaves, ConstsPayload.leaves, EvTc.leaves,
        EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with ((h | h) | (h | h)) | (h | h)
      · exact .inl (.inl (.inl h))
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h
  | _, _, _, .lit p => fun ℓ hℓ => by
      simp only [EvPar.readSubstLet, EvPar.castR_leaves] at hℓ
      simp only [EvPar.leaves, LitPayload.leaves, EvTy.cast_leaves, EvTc.leaves,
        EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with (h | h) | (h | h)
      · exact .inl (.inl h)
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h
  | _, _, _, .refl p => fun ℓ hℓ => by
      simp only [EvPar.readSubstLet, EvPar.leaves, ReflPayload.leaves, EvTc.leaves,
        EvTy.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with (h | h) | (h | h)
      · exact .inl (.inl h)
      · exact .inr h
      · exact .inl (.inr h)
      · exact .inr h

/-- the base step of a transported step, read through its transports. -/
def DStep.read : {Γ : LCtx} → {a b T : Expr Nat} → DStep R Γ a b T → EvPar R Γ a b T
  | _, _, _, _, .base h => h
  | _, _, _, _, .conv s c => s.read.readConv c
  | _, _, _, _, .wk d k s => s.read.readWk d k
  | _, _, _, _, .subst0 j s hget hv => s.read.readSubst0 j hget hv
  | _, _, _, _, .substLet j s hget hv => s.read.readSubstLet j hget hv

/-- reading invents no leaf. -/
theorem DStep.read_leaves : {Γ : LCtx} → {a b T : Expr Nat} → (s : DStep R Γ a b T) →
    ∀ ℓ ∈ s.read.leaves, ℓ ∈ s.leaves
  | _, _, _, _, .base _ => fun _ h => h
  | _, _, _, _, .conv s c => fun ℓ hℓ => by
      simp only [DStep.read, DStep.leaves, List.mem_append] at hℓ ⊢
      rcases List.mem_append.mp (s.read.readConv_leaves c ℓ hℓ) with h | h
      · exact .inl (s.read_leaves ℓ h)
      · exact .inr h
  | _, _, _, _, .wk d k s => fun ℓ hℓ => by
      simp only [DStep.read, DStep.leaves, EvPar.readWk_leaves] at hℓ ⊢
      exact s.read_leaves ℓ hℓ
  | _, _, _, _, .subst0 j s hget hv => fun ℓ hℓ => by
      simp only [DStep.read, DStep.leaves, List.mem_append] at hℓ ⊢
      rcases List.mem_append.mp (s.read.readSubst0_leaves j hget hv ℓ hℓ) with h | h
      · exact .inl (s.read_leaves ℓ h)
      · exact .inr h
  | _, _, _, _, .substLet j s hget hv => fun ℓ hℓ => by
      simp only [DStep.read, DStep.leaves, List.mem_append] at hℓ ⊢
      rcases List.mem_append.mp (s.read.readSubstLet_leaves j hget hv ℓ hℓ) with h | h
      · exact .inl (s.read_leaves ℓ h)
      · exact .inr h

/-- every 0-or-1 step `DOpt` read as a single `EvPar` (`.stay h` becomes `EvPar.ofTy h`). -/
def DOpt.toEvPar {Γ : LCtx} {b d T : Expr Nat} : DOpt R Γ b d T → EvPar R Γ b d T
  | .stay h => .ofTy h
  | .step s => s.read

theorem DOpt.toEvPar_leaves {Γ : LCtx} {b d T : Expr Nat} (o : DOpt R Γ b d T) :
    ∀ ℓ ∈ o.toEvPar.leaves, ℓ ∈ o.leaves := by
  cases o with
  | stay h =>
      intro ℓ hℓ
      simpa only [DOpt.toEvPar, EvPar.ofTy_leaves, DOpt.leaves] using hℓ
  | step s =>
      exact s.read_leaves

/-- Request map for any `EvPar` step (`proofIndex` uses `proofIndexRequests`; others have `Occ = PEmpty`). -/
def EvPar.requests (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {a b T : Expr Nat} → (D : EvPar R Γ a b T) →
      F8Occurrences.Requests (D.val hcl hinst)
  | _, _, _, _, .proofIndex p => EvPar.proofIndexRequests hcl hinst p
  | _, _, _, _, .structPi _ => fun o => nomatch o
  | _, _, _, _, .sortEq _ => fun o => nomatch o
  | _, _, _, _, .consts _ => fun o => nomatch o
  | _, _, _, _, .lit _ => fun o => nomatch o
  | _, _, _, _, .refl _ => fun o => nomatch o

/-- Answered origin store for any `EvPar` step. -/
def EvPar.answers (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E) :
    {Γ : LCtx} → {a b T : Expr Nat} → (D : EvPar R Γ a b T) →
      F8Occurrences.AnsweredOrigins (D.val hcl hinst) (D.requests hcl hinst)
  | _, _, _, _, .proofIndex p => EvPar.proofIndexAnswers hcl hinst p
  | _, _, _, _, .structPi _ => fun o => nomatch o
  | _, _, _, _, .sortEq _ => fun o => nomatch o
  | _, _, _, _, .consts _ => fun o => nomatch o
  | _, _, _, _, .lit _ => fun o => nomatch o
  | _, _, _, _, .refl _ => fun o => nomatch o

/-- every landed `EvPar` step is a `DTile` (`proofIndex` is answered by its payload's
    `proofIndexAnswers`; `structPi`, `sortEq`, `consts`, `lit`, and `refl` have `Occ = PEmpty`). -/
def EvPar.toDTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (D : EvPar R Γ a b T) : DTile R where
  X := X
  step := D.val hcl hinst
  status := statusOfAnswered (R := R) (D.requests hcl hinst) (D.answers hcl hinst)
  om2 := om2_of_answered X (D.requests hcl hinst) (D.answers hcl hinst)

/-- every transported step read into `EvPar` packages as a `DTile`. -/
def DStep.toDTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {a b T : Expr Nat} (s : DStep R Γ a b T) : DTile R :=
  s.read.toDTile hcl hinst X

/-- the D1/D2a/D2b base step diamond makes zero recursive U/X/D/J calls, satisfying `EdgeContract`. -/
theorem dStep_edgeContract : EdgeContract ([] : List (List (Jd E n) × List (Jd E n))) :=
  fun _ h => nomatch h

/-! ### D2b payload readers (`readConv`, `readWk`) and `DTile` packaging -/

def DeltaPayload.readConv {Γ : LCtx} {r : Nat} {ls : List Level} {body T T' : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) (c : EvTc R Γ T T') :
    DeltaPayload R Γ r ls body T' :=
  { p with idx := .trans p.idx c }

theorem DeltaPayload.readConv_leaves {Γ : LCtx} {r : Nat} {ls : List Level}
    {body T T' : Expr Nat} (p : DeltaPayload R Γ r ls body T) (c : EvTc R Γ T T') :
    ∀ ℓ ∈ (p.readConv c).leaves, ℓ ∈ p.leaves ++ c.leaves := by
  intro ℓ hℓ
  simp only [DeltaPayload.readConv, DeltaPayload.leaves, EvTc.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with (h | h) | (h | h)
  · exact .inl (.inl (.inl h))
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)
  · exact .inr h

def DeltaPayload.toDTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {r : Nat} {ls : List Level} {body T : Expr Nat}
    (p : DeltaPayload R Γ r ls body T) : DTile R where
  X := X
  step := p.val hcl hinst
  status := fun o => nomatch o
  om2 := fun o => nomatch o

def BVarZetaPayload.readConv {Γ : LCtx} {i : Nat} {v' T T' : Expr Nat}
    (p : BVarZetaPayload R Γ i v' T) (c : EvTc R Γ T T') :
    BVarZetaPayload R Γ i v' T' :=
  { p with idx := .trans p.idx c }

theorem BVarZetaPayload.readConv_leaves {Γ : LCtx} {i : Nat} {v' T T' : Expr Nat}
    (p : BVarZetaPayload R Γ i v' T) (c : EvTc R Γ T T') :
    ∀ ℓ ∈ (p.readConv c).leaves, ℓ ∈ p.leaves ++ c.leaves := by
  intro ℓ hℓ
  simp only [BVarZetaPayload.readConv, BVarZetaPayload.leaves, EvTc.leaves,
    List.mem_append] at hℓ ⊢
  rcases hℓ with ((h | h) | h) | (h | h)
  · exact .inl (.inl (.inl (.inl h)))
  · exact .inl (.inl (.inl (.inr h)))
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)
  · exact .inr h

def BVarZetaPayload.requests (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {i : Nat} {v' T : Expr Nat}
    (p : BVarZetaPayload R Γ i v' T) :
    F8Occurrences.Requests (p.val hcl hinst) :=
  p.hv.requests hcl hinst

def BVarZetaPayload.answers (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {i : Nat} {v' T : Expr Nat}
    (p : BVarZetaPayload R Γ i v' T) :
    F8Occurrences.AnsweredOrigins (p.val hcl hinst) (p.requests hcl hinst) :=
  p.hv.answers hcl hinst

def BVarZetaPayload.toDTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {i : Nat} {v' T : Expr Nat}
    (p : BVarZetaPayload R Γ i v' T) : DTile R where
  X := X
  step := p.val hcl hinst
  status := statusOfAnswered (R := R) (p.requests hcl hinst) (p.answers hcl hinst)
  om2 := om2_of_answered X (p.requests hcl hinst) (p.answers hcl hinst)

def LamPayload.readConv {Γ : LCtx} {A body A' body' T T' : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) (c : EvTc R Γ T T') :
    LamPayload R Γ A body A' body' T' :=
  { p with idx := .trans p.idx c }

theorem LamPayload.readConv_leaves {Γ : LCtx} {A body A' body' T T' : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) (c : EvTc R Γ T T') :
    ∀ ℓ ∈ (p.readConv c).leaves, ℓ ∈ p.leaves ++ c.leaves := by
  intro ℓ hℓ
  simp only [LamPayload.readConv, LamPayload.leaves, EvTc.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with ((((h | h) | h) | h) | h) | (h | h)
  · exact .inl (.inl (.inl (.inl (.inl (.inl h)))))
  · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
  · exact .inl (.inl (.inl (.inl (.inr h))))
  · exact .inl (.inl (.inl (.inr h)))
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)
  · exact .inr h

def LamPayload.readWk (d : LocalDecl) (k : Nat) {Γ : LCtx} {A body A' body' T : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) :
    LamPayload R (insertAt d k Γ)
      (lift k 1 A) (lift (k + 1) 1 body) (lift k 1 A') (lift (k + 1) 1 body') (lift k 1 T) where
  B := lift (k + 1) 1 p.B
  u := p.u
  v := p.v
  hc := .wk d k p.hc
  hA := .wk d k p.hA
  hB := .wk d (k + 1) p.hB
  hb := p.hb.readWk d (k + 1)
  hrt := .wk d k p.hrt
  idx := .wk d k p.idx

theorem LamPayload.readWk_leaves (d : LocalDecl) (k : Nat) {Γ : LCtx}
    {A body A' body' T : Expr Nat} (p : LamPayload R Γ A body A' body' T) :
    (p.readWk d k).leaves = p.leaves := by
  simp only [LamPayload.readWk, LamPayload.leaves, EvCv.leaves, EvTy.leaves,
    EvPar.readWk_leaves, EvTc.leaves]

def LamPayload.requests (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A body A' body' T : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) :
    F8Occurrences.Requests (p.val hcl hinst) :=
  p.hb.requests hcl hinst

def LamPayload.answers (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A body A' body' T : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) :
    F8Occurrences.AnsweredOrigins (p.val hcl hinst) (p.requests hcl hinst) :=
  p.hb.answers hcl hinst

def LamPayload.toDTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {A body A' body' T : Expr Nat}
    (p : LamPayload R Γ A body A' body' T) : DTile R where
  X := X
  step := p.val hcl hinst
  status := statusOfAnswered (R := R) (p.requests hcl hinst) (p.answers hcl hinst)
  om2 := om2_of_answered X (p.requests hcl hinst) (p.answers hcl hinst)

def AppPayload.readConv {Γ : LCtx} {f a f' a' T T' : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) (c : EvTc R Γ T T') :
    AppPayload R Γ f a f' a' T' :=
  { p with idx := .trans p.idx c }

theorem AppPayload.readConv_leaves {Γ : LCtx} {f a f' a' T T' : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) (c : EvTc R Γ T T') :
    ∀ ℓ ∈ (p.readConv c).leaves, ℓ ∈ p.leaves ++ c.leaves := by
  intro ℓ hℓ
  simp only [AppPayload.readConv, AppPayload.leaves, EvTc.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with ((((((h | h) | h) | h) | h) | h) | h) | (h | h)
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl h)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr h)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr h))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
  · exact .inl (.inl (.inl (.inl (.inr h))))
  · exact .inl (.inl (.inl (.inr h)))
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)
  · exact .inr h

def AppPayload.readWk (d : LocalDecl) (k : Nat) {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) :
    AppPayload R (insertAt d k Γ)
      (lift k 1 f) (lift k 1 a) (lift k 1 f') (lift k 1 a') (lift k 1 T) where
  T₀ := lift k 1 p.T₀
  A := lift k 1 p.A
  B := lift (k + 1) 1 p.B
  u := p.u
  v := p.v
  w := p.w
  hf := p.hf.readWk d k
  hc := .wk d k p.hc
  hPi := .wk d k p.hPi
  hB := .wk d (k + 1) p.hB
  hTy := EvTy.cast rfl (lift_instantiate_low 1 k 0 a (Nat.zero_le k) p.B) rfl (.wk d k p.hTy)
  ha := p.ha.readWk d k
  hr := EvTy.cast rfl rfl (lift_instantiate_low 1 k 0 a (Nat.zero_le k) p.B) (.wk d k p.hr)
  idx := EvTc.cast rfl (lift_instantiate_low 1 k 0 a (Nat.zero_le k) p.B) rfl (.wk d k p.idx)

theorem AppPayload.readWk_leaves (d : LocalDecl) (k : Nat) {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) :
    (p.readWk d k).leaves = p.leaves := by
  simp only [AppPayload.readWk, AppPayload.leaves, EvPar.readWk_leaves, EvTc.leaves,
    EvTy.leaves, EvTy.cast_leaves, EvTc.cast_leaves]

def AppPayload.requests (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {f a f' a' T : Expr Nat} (p : AppPayload R Γ f a f' a' T) :
    F8Occurrences.Requests (p.val hcl hinst)
  | .inl o => p.hf.requests hcl hinst o
  | .inr o => p.ha.requests hcl hinst o

def AppPayload.answers (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {f a f' a' T : Expr Nat} (p : AppPayload R Γ f a f' a' T) :
    F8Occurrences.AnsweredOrigins (p.val hcl hinst) (p.requests hcl hinst)
  | .inl o, side => p.hf.answers hcl hinst o side
  | .inr o, side => p.ha.answers hcl hinst o side

def AppPayload.toDTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {f a f' a' T : Expr Nat}
    (p : AppPayload R Γ f a f' a' T) : DTile R where
  X := X
  step := p.val hcl hinst
  status := statusOfAnswered (R := R) (p.requests hcl hinst) (p.answers hcl hinst)
  om2 := om2_of_answered X (p.requests hcl hinst) (p.answers hcl hinst)

def LetEPayload.readConv {Γ : LCtx} {A value body A' value' body' T T' : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) (c : EvTc R Γ T T') :
    LetEPayload R Γ A value body A' value' body' T' :=
  { p with idx := .trans p.idx c }

theorem LetEPayload.readConv_leaves {Γ : LCtx} {A value body A' value' body' T T' : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) (c : EvTc R Γ T T') :
    ∀ ℓ ∈ (p.readConv c).leaves, ℓ ∈ p.leaves ++ c.leaves := by
  intro ℓ hℓ
  simp only [LetEPayload.readConv, LetEPayload.leaves, EvTc.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with ((((((h | h) | h) | h) | h) | h) | h) | (h | h)
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl h)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr h)))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr h))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
  · exact .inl (.inl (.inl (.inl (.inr h))))
  · exact .inl (.inl (.inl (.inr h)))
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)
  · exact .inr h

def LetEPayload.readWk (d : LocalDecl) (k : Nat) {Γ : LCtx}
    {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) :
    LetEPayload R (insertAt d k Γ)
      (lift k 1 A) (lift k 1 value) (lift (k + 1) 1 body)
      (lift k 1 A') (lift k 1 value') (lift (k + 1) 1 body') (lift k 1 T) where
  B := lift (k + 1) 1 p.B
  u := p.u
  w := p.w
  hc := .wk d k p.hc
  hA := .wk d k p.hA
  hv := p.hv.readWk d k
  hB := .wk d (k + 1) p.hB
  hTy := EvTy.cast rfl (lift_instantiate_low 1 k 0 value (Nat.zero_le k) p.B) rfl (.wk d k p.hTy)
  hb := p.hb.readWk d (k + 1)
  hrt := EvTy.cast rfl rfl (lift_instantiate_low 1 k 0 value (Nat.zero_le k) p.B) (.wk d k p.hrt)
  idx := EvTc.cast rfl (lift_instantiate_low 1 k 0 value (Nat.zero_le k) p.B) rfl (.wk d k p.idx)

theorem LetEPayload.readWk_leaves (d : LocalDecl) (k : Nat) {Γ : LCtx}
    {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) :
    (p.readWk d k).leaves = p.leaves := by
  simp only [LetEPayload.readWk, LetEPayload.leaves, EvCv.leaves, EvTy.leaves,
    EvPar.readWk_leaves, EvTc.leaves, EvTy.cast_leaves, EvTc.cast_leaves]

def LetEPayload.requests (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) :
    F8Occurrences.Requests (p.val hcl hinst)
  | .inl o => p.hv.requests hcl hinst o
  | .inr o => p.hb.requests hcl hinst o

def LetEPayload.answers (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    {Γ : LCtx} {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) :
    F8Occurrences.AnsweredOrigins (p.val hcl hinst) (p.requests hcl hinst)
  | .inl o, side => p.hv.answers hcl hinst o side
  | .inr o, side => p.hb.answers hcl hinst o side

def LetEPayload.toDTile (hcl : EnvClosed E) (hinst : EnvMembersSubstStable E)
    (X : List (Jd E n)) {Γ : LCtx} {A value body A' value' body' T : Expr Nat}
    (p : LetEPayload R Γ A value body A' value' body' T) : DTile R where
  X := X
  step := p.val hcl hinst
  status := statusOfAnswered (R := R) (p.requests hcl hinst) (p.answers hcl hinst)
  om2 := om2_of_answered X (p.requests hcl hinst) (p.answers hcl hinst)

/-! ### W-X-LEVELS: 1-step valleys for `ConvT.sorts` and `ConvT.consts` -/

/-- Leaf-less 1-step `Valley` for `ConvT.sorts` (`leaves = []`). -/
def Valley.ofSorts (Γ : LCtx) (l₁ l₂ : Level) (h : eqN l₁ l₂) :
    Valley R Γ (.sort l₁) (.sort l₂) (.sort (.succ l₁)) where
  N := .sort l₂
  left := .tail (.ofSorts Γ l₁ l₂ h) (.refl (.sortsRight (Γ := Γ) l₁ l₂ h))
  right := .refl (.sortsRight (Γ := Γ) l₁ l₂ h)
  ty₁ := .sortsLeft (Γ := Γ) l₁ l₂ h
  ty₂ := .sortsRight (Γ := Γ) l₁ l₂ h

theorem Valley.ofSorts_leaves (Γ : LCtx) (l₁ l₂ : Level) (h : eqN l₁ l₂) :
    (Valley.ofSorts (R := R) Γ l₁ l₂ h).leaves = [] := rfl

/-- 1-step `Valley` for `ConvT.consts` with retyping chain `tc`, every leaf in `tc.leaves`. -/
def Valley.ofConstsWith (Γ : LCtx) (r : Nat) (ls ls' : List Level)
    (m : CheckedMember) (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (heq : eqNList ls ls')
    (tc : EvTc R Γ (instantiateLevels ls' m.mtype) (instantiateLevels ls m.mtype)) :
    Valley R Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype) where
  N := .const r ls'
  left := .tail (.ofConstsWith Γ r ls ls' m hres hlen hwf hwf' heq tc)
    (.refl (.constsRightWith (Γ := Γ) r ls ls' m hres hlen hwf hwf' heq tc))
  right := .refl (.constsRightWith (Γ := Γ) r ls ls' m hres hlen hwf hwf' heq tc)
  ty₁ := .constsLeft (Γ := Γ) r ls ls' m hres hlen hwf hwf' heq
  ty₂ := .constsRightWith (Γ := Γ) r ls ls' m hres hlen hwf hwf' heq tc

theorem Valley.ofConstsWith_leaves (Γ : LCtx) (r : Nat) (ls ls' : List Level)
    (m : CheckedMember) (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (heq : eqNList ls ls')
    (tc : EvTc R Γ (instantiateLevels ls' m.mtype) (instantiateLevels ls m.mtype)) :
    ∀ ℓ ∈ (Valley.ofConstsWith (R := R) Γ r ls ls' m hres hlen hwf hwf' heq tc).leaves,
      ℓ ∈ tc.leaves := by
  intro ℓ hℓ
  simp only [Valley.ofConstsWith, Valley.leaves, EvParStar.leaves, EvPar.ofConstsWith_leaves,
    EvTy.constsRightWith_leaves, EvTy.constsLeft_leaves, List.append_nil, List.mem_append] at hℓ
  rcases hℓ with ((h | h) | h) | h <;> exact h

/-! ### the proof-index rows (no hypothesis) -/

/-- `proofIndex p₁ × s₂`: the step `b ⇒ c` from `p₁`'s proposition and chain. -/
def proofIndexJoin {Γ : LCtx} {a b c T : Expr Nat} (p₁ : ProofIndexPayload R Γ a b T)
    (hc : EvTy R Γ c T) : EvPar R Γ b c T :=
  .proofIndex
    { proposition := p₁.proposition
      propTy := p₁.propTy
      chain := p₁.chain
      leftTy := p₁.rightTy
      rightTy := hc }

theorem proofIndexJoin_leaves {Γ : LCtx} {a b c T : Expr Nat}
    (p₁ : ProofIndexPayload R Γ a b T) (hc : EvTy R Γ c T) :
    ∀ ℓ ∈ (proofIndexJoin p₁ hc).leaves, ℓ ∈ p₁.leaves ∨ ℓ ∈ hc.leaves := by
  intro ℓ hℓ
  simp only [proofIndexJoin, EvPar.leaves, ProofIndexPayload.leaves, List.mem_append] at hℓ ⊢
  rcases hℓ with ((h | h) | h) | h
  · exact .inl (.inl (.inl (.inl h)))
  · exact .inl (.inl (.inl (.inr h)))
  · exact .inl (.inr h)
  · exact .inr h

/-- `D₁ × proofIndex p₂`: symmetric 1-step join on the right. -/
def proofIndexRightJoin {Γ : LCtx} {a b c T : Expr Nat}
    (D₁ : EvPar R Γ a b T) (p₂ : ProofIndexPayload R Γ a c T) :
    DOptJoin R Γ b c T (D₁.leaves ++ (EvPar.proofIndex p₂).leaves) :=
  { d := b, left := .stay D₁.rightTy,
    right := .step (.base (proofIndexJoin p₂ D₁.rightTy)),
    sound := fun ℓ hℓ => by
      simp only [DOpt.leaves, DStep.leaves, List.mem_append] at hℓ
      refine dSubEq_of_mem ?_
      rcases hℓ with h | h
      · exact List.mem_append.mpr (.inl (D₁.rightTy_leaves ℓ h))
      · rcases proofIndexJoin_leaves p₂ D₁.rightTy ℓ h with h' | h'
        · exact List.mem_append.mpr (.inr h')
        · exact List.mem_append.mpr (.inl (D₁.rightTy_leaves ℓ h')) }

/-! ### D-VAR context conversion for provenance conversions -/

/-- a conversion under the binder `A` moved under a convertible binder `A₁`
    (weaken under a copy of `A₁`, substitute the bound variable typed by `EvTy.var`
    retyped along the weakened domain chain; the binder's sort typing feeds `esub`'s
    `hvT`). Leaves: exactly the three inputs'. -/
def cvCtxConvVar {Γ : LCtx} {A A₁ x y U : Expr Nat} {w : Level} (cA : EvTc R Γ A₁ A)
    (hAs : EvTy R Γ A (.sort w)) (e : EvCv R (.assumption A :: Γ) x y U) :
    EvCv R (.assumption A₁ :: Γ) x y U :=
  EvCv.dcast rfl (instantiate_bvar_lift_succ 0 x) (instantiate_bvar_lift_succ 0 y)
    (instantiate_bvar_lift_succ 0 U)
    (EvCv.esub (v := .bvar 0) 0 w (EvCv.wk (.assumption A₁) 1 e) rfl
      (EvTy.cast rfl (lift_zero 0 _).symm (lift_zero 0 _).symm
        (EvTy.rety (EvTy.var 0 (lift 0 1 A₁) rfl) (EvTc.wk (.assumption A₁) 0 cA)))
      (EvTy.cast rfl (lift_zero 0 _).symm rfl (EvTy.wk (.assumption A₁) 0 hAs)))

theorem cvCtxConvVar_leaves {Γ : LCtx} {A A₁ x y U : Expr Nat} {w : Level}
    (cA : EvTc R Γ A₁ A) (hAs : EvTy R Γ A (.sort w)) (e : EvCv R (.assumption A :: Γ) x y U) :
    (cvCtxConvVar cA hAs e).leaves = e.leaves ++ cA.leaves ++ hAs.leaves := by
  simp only [cvCtxConvVar, EvCv.dcast_leaves, EvCv.leaves, EvTy.cast_leaves, EvTy.leaves,
    EvTc.leaves, List.nil_append]

/-- D-VAR context conversion for provenance typings: move `e : EvTy R (.assumption A :: Γ) x U`
    under a convertible binder `A₁`. -/
def tyCtxConvVar {Γ : LCtx} {A A₁ x U : Expr Nat} {w : Level} (cA : EvTc R Γ A₁ A)
    (hAs : EvTy R Γ A (.sort w)) (e : EvTy R (.assumption A :: Γ) x U) :
    EvTy R (.assumption A₁ :: Γ) x U :=
  EvTy.cast rfl (instantiate_bvar_lift_succ 0 x) (instantiate_bvar_lift_succ 0 U)
    (EvTy.esub (v := .bvar 0) 0 w (EvTy.wk (.assumption A₁) 1 e) rfl
      (EvTy.cast rfl (lift_zero 0 _).symm (lift_zero 0 _).symm
        (EvTy.rety (EvTy.var 0 (lift 0 1 A₁) rfl) (EvTc.wk (.assumption A₁) 0 cA)))
      (EvTy.cast rfl (lift_zero 0 _).symm rfl (EvTy.wk (.assumption A₁) 0 hAs)))

theorem tyCtxConvVar_leaves {Γ : LCtx} {A A₁ x U : Expr Nat} {w : Level}
    (cA : EvTc R Γ A₁ A) (hAs : EvTy R Γ A (.sort w)) (e : EvTy R (.assumption A :: Γ) x U) :
    (tyCtxConvVar cA hAs e).leaves = e.leaves ++ cA.leaves ++ hAs.leaves := by
  simp only [tyCtxConvVar, EvTy.cast_leaves, EvTy.leaves, EvTc.leaves, List.nil_append]

/-- Provenance-level substitution of an assumption slot `j` in any `EvPar` step,
    using `EvTy.esub`, `EvCv.esub`, and `EvTc.subst0`. Named `readEsub0` so it
    does not collide with `EvPar.readSubst0` (no level, no `hvT`, `.subst0` on pieces). -/
def EvPar.readEsub0 {Γ : LCtx} {a b T t v : Expr Nat} (j : Nat) (u : Level) :
    EvPar R Γ a b T →
    (hget : Γ[j]? = some (.assumption t)) →
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) →
    (hvT : EvTy R (substRemove v j Γ) (lift 0 j t) (.sort u)) →
    EvPar R (substRemove v j Γ)
      (instantiate j (lift 0 j v) a) (instantiate j (lift 0 j v) b)
      (instantiate j (lift 0 j v) T)
  | .proofIndex p, hget, hv, hvT => .proofIndex
      { proposition := instantiate j (lift 0 j v) p.proposition
        propTy := .esub j u p.propTy hget hv hvT
        chain := .subst0 j p.chain hget hv
        leftTy := .esub j u p.leftTy hget hv hvT
        rightTy := .esub j u p.rightTy hget hv hvT }
  | .structPi (A := A) (B := B) (A' := A') (B' := B') p, hget, hv, hvT =>
      let hget' : (LocalDecl.assumption A :: Γ)[j + 1]? = some (.assumption t) :=
        subst_arg_get_succ (.assumption A) hget
      let hv' : EvTy R (substRemove v (j + 1) (.assumption A :: Γ))
          (lift 0 (j + 1) v) (lift 0 (j + 1) t) :=
        EvTy.cast (by simp [substRemove_succ_cons, instDecl])
          (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v)
          (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t)
          (.wk (.assumption (instantiate j (lift 0 j v) A)) 0 hv)
      let hvT' : EvTy R (substRemove v (j + 1) (.assumption A :: Γ))
          (lift 0 (j + 1) t) (.sort u) :=
        EvTy.cast (by simp [substRemove_succ_cons, instDecl])
          (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) t)
          rfl (.wk (.assumption (instantiate j (lift 0 j v) A)) 0 hvT)
      let hll : lift 0 (j + 1) v = lift 0 1 (lift 0 j v) :=
        (lift_lift_merge 1 j 0 0 (Nat.zero_le _) (Nat.zero_le _) v).symm
      EvPar.dcast rfl (by simp only [instantiate, hll]) (by simp only [instantiate, hll]) rfl
        (.structPi
          { u := p.u, v := p.v
            hA := .esub j u p.hA hget hv hvT
            hc := .esub j u p.hc hget hv hvT
            hB := EvTy.cast (by simp [substRemove_succ_cons, instDecl]) rfl rfl
              (.esub (j + 1) u p.hB hget' hv' hvT')
            hcB := EvCv.dcast (by simp [substRemove_succ_cons, instDecl]) rfl rfl rfl
              (.esub (j + 1) u p.hcB hget' hv' hvT')
            hrt := EvTy.cast rfl (by simp only [instantiate, hll]) rfl
              (.esub j u p.hrt hget hv hvT)
            idx := EvTc.cast rfl rfl rfl (.subst0 j p.idx hget hv) })
  | .sortEq p, hget, hv, hvT => .sortEq
      { T₀ := instantiate j (lift 0 j v) p.T₀
        h := p.h
        hl := .esub j u p.hl hget hv hvT
        hr := .esub j u p.hr hget hv hvT
        idx := .subst0 j p.idx hget hv }
  | .consts p, hget, hv, hvT => .consts
      { T₀ := instantiate j (lift 0 j v) p.T₀
        h := p.h
        hl := .esub j u p.hl hget hv hvT
        hr := .esub j u p.hr hget hv hvT
        idx := .subst0 j p.idx hget hv }
  | .lit (t := tl) p, hget, hv, hvT =>
      EvPar.castR (natExpand_instantiate j (lift 0 j v) tl).symm
        (.lit
          { T₀ := instantiate j (lift 0 j v) p.T₀
            hexp := EvTy.cast rfl (natExpand_instantiate j (lift 0 j v) tl) rfl
              (.esub j u p.hexp hget hv hvT)
            idx := .subst0 j p.idx hget hv })
  | .refl p, hget, hv, hvT => .refl
      { T₀ := instantiate j (lift 0 j v) p.T₀
        h := .esub j u p.h hget hv hvT
        idx := .subst0 j p.idx hget hv }

theorem EvPar.readEsub0_leaves {Γ : LCtx} {a b T t v : Expr Nat} (j : Nat) (u : Level) :
    (D : EvPar R Γ a b T) →
    (hget : Γ[j]? = some (.assumption t)) →
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) →
    (hvT : EvTy R (substRemove v j Γ) (lift 0 j t) (.sort u)) →
    ∀ ℓ ∈ (D.readEsub0 j u hget hv hvT).leaves,
      ℓ ∈ D.leaves ++ hv.leaves ++ hvT.leaves
  | .proofIndex p, hget, hv, hvT => fun ℓ hℓ => by
      simp only [EvPar.readEsub0, EvPar.leaves, ProofIndexPayload.leaves, EvTy.leaves,
        EvTc.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with ((((h | h) | h) | (h | h)) | ((h | h) | h)) | ((h | h) | h)
      · exact .inl (.inl (.inl (.inl (.inl h))))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inl (.inl (.inr h))))
      · exact .inl (.inr h)
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
      · exact .inr h
  | .structPi p, hget, hv, hvT => fun ℓ hℓ => by
      simp only [EvPar.readEsub0, EvPar.dcast_leaves] at hℓ
      simp only [EvPar.leaves, StructPiPayload.leaves,
        EvTy.cast_leaves, EvCv.dcast_leaves, EvTc.cast_leaves, EvTy.leaves, EvCv.leaves,
        EvTc.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with (((((((h | h) | h) | ((h | h) | h)) | ((h | h) | h)) | ((h | h) | h)) | ((h | h) | h)) | (h | h))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl h))))))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr h))))))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inl (.inl (.inl (.inr h)))))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inl (.inl (.inr h))))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
  | .sortEq p, hget, hv, hvT => fun ℓ hℓ => by
      simp only [EvPar.readEsub0, EvPar.leaves, SortEqPayload.leaves, EvTy.leaves,
        EvTc.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with (((h | h) | h) | ((h | h) | h)) | (h | h)
      · exact .inl (.inl (.inl (.inl h)))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
  | .consts p, hget, hv, hvT => fun ℓ hℓ => by
      simp only [EvPar.readEsub0, EvPar.leaves, ConstsPayload.leaves, EvTy.leaves,
        EvTc.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with (((h | h) | h) | ((h | h) | h)) | (h | h)
      · exact .inl (.inl (.inl (.inl h)))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inl (.inr h)))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
  | .lit p, hget, hv, hvT => fun ℓ hℓ => by
      simp only [EvPar.readEsub0, EvPar.castR_leaves] at hℓ
      simp only [EvPar.leaves, LitPayload.leaves,
        EvTy.cast_leaves, EvTy.leaves, EvTc.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with ((h | h) | h) | (h | h)
      · exact .inl (.inl (.inl h))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)
  | .refl p, hget, hv, hvT => fun ℓ hℓ => by
      simp only [EvPar.readEsub0, EvPar.leaves, ReflPayload.leaves, EvTy.leaves,
        EvTc.leaves, List.mem_append] at hℓ ⊢
      rcases hℓ with ((h | h) | h) | (h | h)
      · exact .inl (.inl (.inl h))
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inr h))
      · exact .inl (.inr h)

/-- D-VAR context conversion for `EvPar`: move `D : EvPar R (.assumption A :: Γ) x y U`
    under a convertible binder `A₁`. -/
def evParCtxConvVar {Γ : LCtx} {A A₁ x y U : Expr Nat} {w : Level}
    (cA : EvTc R Γ A₁ A) (hAs : EvTy R Γ A (.sort w))
    (D : EvPar R (.assumption A :: Γ) x y U) :
    EvPar R (.assumption A₁ :: Γ) x y U :=
  EvPar.dcast rfl (instantiate_bvar_lift_succ 0 x) (instantiate_bvar_lift_succ 0 y)
    (instantiate_bvar_lift_succ 0 U)
    (EvPar.readEsub0 (v := .bvar 0) 0 w (D.readWk (.assumption A₁) 1) rfl
      (EvTy.cast rfl (lift_zero 0 _).symm (lift_zero 0 _).symm
        (EvTy.rety (EvTy.var 0 (lift 0 1 A₁) rfl) (EvTc.wk (.assumption A₁) 0 cA)))
      (EvTy.cast rfl (lift_zero 0 _).symm rfl (EvTy.wk (.assumption A₁) 0 hAs)))

theorem evParCtxConvVar_leaves {Γ : LCtx} {A A₁ x y U : Expr Nat} {w : Level}
    (cA : EvTc R Γ A₁ A) (hAs : EvTy R Γ A (.sort w))
    (D : EvPar R (.assumption A :: Γ) x y U) :
    ∀ ℓ ∈ (evParCtxConvVar cA hAs D).leaves,
      ℓ ∈ D.leaves ++ cA.leaves ++ hAs.leaves := by
  intro ℓ hℓ
  simp only [evParCtxConvVar, EvPar.dcast_leaves] at hℓ
  have h := EvPar.readEsub0_leaves (v := .bvar 0) 0 w (D.readWk (.assumption A₁) 1) rfl
    (EvTy.cast rfl (lift_zero 0 _).symm (lift_zero 0 _).symm
      (EvTy.rety (EvTy.var 0 (lift 0 1 A₁) rfl) (EvTc.wk (.assumption A₁) 0 cA)))
    (EvTy.cast rfl (lift_zero 0 _).symm rfl (EvTy.wk (.assumption A₁) 0 hAs))
    ℓ hℓ
  simpa only [EvPar.readWk_leaves, EvTy.cast_leaves, EvTy.leaves, EvTc.leaves,
    List.nil_append] using h

/-! ### the `refl` rows (no hypothesis) -/

/-- `refl p₁ × D₂`: `a ⇒ a` against `a ⇒ c` closes at `c` (`left` steps by `D₂`, `right` stays). -/
def reflLeftJoin {Γ : LCtx} {a c T : Expr Nat}
    (p₁ : ReflPayload R Γ a T) (D₂ : EvPar R Γ a c T) :
    DOptJoin R Γ a c T ((EvPar.refl p₁).leaves ++ D₂.leaves) :=
  { d := c, left := .step (.base D₂), right := .stay D₂.rightTy,
    sound := fun ℓ hℓ => by
      simp only [DOpt.leaves, DStep.leaves, List.mem_append] at hℓ
      refine dSubEq_of_mem (List.mem_append.mpr (.inr ?_))
      rcases hℓ with h | h
      · exact h
      · exact D₂.rightTy_leaves ℓ h }

/-- `D₁ × refl p₂`: `a ⇒ b` against `a ⇒ a` closes at `b` (`left` stays, `right` steps by `D₁`). -/
def reflRightJoin {Γ : LCtx} {a b T : Expr Nat}
    (D₁ : EvPar R Γ a b T) (p₂ : ReflPayload R Γ a T) :
    DOptJoin R Γ b a T (D₁.leaves ++ (EvPar.refl p₂).leaves) :=
  { d := b, left := .stay D₁.rightTy, right := .step (.base D₁),
    sound := fun ℓ hℓ => by
      simp only [DOpt.leaves, DStep.leaves, List.mem_append] at hℓ
      refine dSubEq_of_mem (List.mem_append.mpr (.inl ?_))
      rcases hℓ with h | h
      · exact D₁.rightTy_leaves ℓ h
      · exact h }

/-! ### the atomic rows (`sortEq`, `consts`, `delta`) and structural-Pi row -/

/-- a leaf-less sort retyping along `=ₙ` levels. -/
def sortsTc {Γ : LCtx} (u u' : Level) (h : eqN u u') : EvTc R Γ (.sort u) (.sort u') :=
  .ofCv (.succ u) (.sorts u u' h)

theorem sortsTc_leaves {Γ : LCtx} (u u' : Level) (h : eqN u u') :
    (sortsTc (R := R) (Γ := Γ) u u' h).leaves = [] := rfl

theorem eqN_symm' {u v : Level} (h : eqN u v) : eqN v u := fun ρ => (h ρ).symm

theorem eqN_trans' {u v w : Level} (h₁ : eqN u v) (h₂ : eqN v w) : eqN u w :=
  fun ρ => (h₁ ρ).trans (h₂ ρ)

theorem eqNList_symm' : {ls₁ ls₂ : List Level} → eqNList ls₁ ls₂ → eqNList ls₂ ls₁
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨eqN_symm' h, eqNList_symm' hs⟩

theorem eqNList_trans' : {ls₁ ls₂ ls₃ : List Level} →
    eqNList ls₁ ls₂ → eqNList ls₂ ls₃ → eqNList ls₁ ls₃
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h₁, hs₁⟩, ⟨h₂, hs₂⟩ =>
      ⟨eqN_trans' h₁ h₂, eqNList_trans' hs₁ hs₂⟩

/-- `sortEq p₁ × sortEq p₂`: the forward closing step `sort l₂ ⇒ sort l₃` at `T`. -/
def sortEqJoin {Γ : LCtx} {l₁ l₂ l₃ : Level} {T : Expr Nat}
    (p₁ : SortEqPayload R Γ l₁ l₂ T) (p₂ : SortEqPayload R Γ l₁ l₃ T) :
    SortEqPayload R Γ l₂ l₃ T where
  T₀ := T
  h := eqN_trans' (eqN_symm' p₁.h) p₂.h
  hl := .rety p₁.hr p₁.idx
  hr := .rety p₂.hr p₂.idx
  idx := .refl Γ T

theorem sortEqJoin_leaves {Γ : LCtx} {l₁ l₂ l₃ : Level} {T : Expr Nat}
    (p₁ : SortEqPayload R Γ l₁ l₂ T) (p₂ : SortEqPayload R Γ l₁ l₃ T) :
    ∀ ℓ ∈ (sortEqJoin p₁ p₂).leaves, ℓ ∈ p₁.leaves ++ p₂.leaves := by
  intro ℓ hℓ
  simp only [sortEqJoin, SortEqPayload.leaves, EvTy.leaves, EvTc.leaves,
    List.append_nil, List.mem_append] at hℓ ⊢
  rcases hℓ with (h | h) | (h | h)
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)
  · exact .inr (.inl (.inr h))
  · exact .inr (.inr h)

/-- `consts p₁ × consts p₂`: the forward closing step `const r ls₁ ⇒ const r ls₂` at `T`. -/
def constsJoin {Γ : LCtx} {r : Nat} {ls ls₁ ls₂ : List Level} {T : Expr Nat}
    (p₁ : ConstsPayload R Γ r ls ls₁ T) (p₂ : ConstsPayload R Γ r ls ls₂ T) :
    ConstsPayload R Γ r ls₁ ls₂ T where
  T₀ := T
  h := eqNList_trans' (eqNList_symm' p₁.h) p₂.h
  hl := .rety p₁.hr p₁.idx
  hr := .rety p₂.hr p₂.idx
  idx := .refl Γ T

theorem constsJoin_leaves {Γ : LCtx} {r : Nat} {ls ls₁ ls₂ : List Level} {T : Expr Nat}
    (p₁ : ConstsPayload R Γ r ls ls₁ T) (p₂ : ConstsPayload R Γ r ls ls₂ T) :
    ∀ ℓ ∈ (constsJoin p₁ p₂).leaves, ℓ ∈ p₁.leaves ++ p₂.leaves := by
  intro ℓ hℓ
  simp only [constsJoin, ConstsPayload.leaves, EvTy.leaves, EvTc.leaves,
    List.append_nil, List.mem_append] at hℓ ⊢
  rcases hℓ with (h | h) | (h | h)
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)
  · exact .inr (.inl (.inr h))
  · exact .inr (.inr h)

/-- `delta p₁ × delta p₂`: same constant `r` and levels `ls`, so `body₁ = body₂` and the
    peak closes in 0 steps with no hypothesis. -/
def deltaJoin {Γ : LCtx} {r : Nat} {ls : List Level} {body₁ body₂ T : Expr Nat}
    (p₁ : DeltaPayload R Γ r ls body₁ T) (p₂ : DeltaPayload R Γ r ls body₂ T) :
    DOptJoin R Γ (instantiateLevels ls body₁) (instantiateLevels ls body₂) T
      (p₁.leaves ++ p₂.leaves) := by
  have hm : p₁.m = p₂.m := Option.some.inj (p₁.hres.symm.trans p₂.hres)
  have hb : body₁ = body₂ := Option.some.inj (p₁.hbody.symm.trans (hm ▸ p₂.hbody))
  cases hb
  exact
    { d := instantiateLevels ls body₁
      left := .stay p₁.rightTy
      right := .stay p₂.rightTy
      sound := fun ℓ hℓ => by
        simp only [DOpt.leaves, List.mem_append] at hℓ
        refine dSubEq_of_mem ?_
        rcases hℓ with h | h
        · exact List.mem_append.mpr (.inl (p₁.rightTy_leaves ℓ h))
        · exact List.mem_append.mpr (.inr (p₂.rightTy_leaves ℓ h)) }

section StructPi
variable (hW : EnvWfT E) (su : F8A2Support.SortUnique E n)

/-- `structPi p₁ × structPi p₂`: the forward closing step `Π A₁ B₁ ⇒ Π A₂ B₂`. -/
def structPiJoin {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B A₁ B₁ A₂ B₂ T : Expr Nat}
    (p₁ : StructPiPayload R Γ A B A₁ B₁ T) (p₂ : StructPiPayload R Γ A B A₂ B₂ T) :
    StructPiPayload R Γ A₁ B₁ A₂ B₂ T :=
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  -- levels of the two inputs agree on the shared source
  have hu : eqN p₁.u p₂.u := su hW hΓ (p₁.hA.val hcl hinst) (p₂.hA.val hcl hinst)
  let hΓA : CtxWfT E n (.assumption A :: Γ) := .assumption Γ A p₁.u hΓ (p₁.hA.val hcl hinst)
  have hv : eqN p₁.v p₂.v := su hW hΓA (p₁.hB.val hcl hinst) (p₂.hB.val hcl hinst)
  -- the domain and codomain chains at `p₂`'s levels
  let hc : EvCv R Γ A₁ A₂ (.sort p₂.u) :=
    .trans (.symm (.rety p₁.hc (sortsTc p₁.u p₂.u hu))) p₂.hc
  let hcB₀ : EvCv R (.assumption A :: Γ) B₁ B₂ (.sort p₂.v) :=
    .trans (.symm (.rety p₁.hcB (sortsTc p₁.v p₂.v hv))) p₂.hcB
  let hcB : EvCv R (.assumption A₁ :: Γ) B₁ B₂ (.sort p₂.v) :=
    cvCtxConvVar (.ofCv p₁.u (.symm p₁.hc)) p₁.hA hcB₀
  -- the target's own pieces, from the inverted root typing of `Π A₁ B₁`
  let inv := (EvTy.rety p₁.hrt p₁.idx).invPiT rfl
  have hu' : eqN inv.u p₂.u := by
    obtain ⟨_, ⟨hA₁⟩⟩ := convT_endpoints hW hΓ (p₁.hc.val hcl hinst)
    exact eqN_trans' (su hW hΓ (inv.hA.val hcl hinst) hA₁) hu
  let hΓA₁ : CtxWfT E n (.assumption A₁ :: Γ) :=
    .assumption Γ A₁ inv.u hΓ (inv.hA.val hcl hinst)
  have hv' : eqN inv.v p₂.v := by
    obtain ⟨⟨hB₁⟩, _⟩ := convT_endpoints hW hΓA₁ (hcB.val hcl hinst)
    exact su hW hΓA₁ (inv.hB.val hcl hinst) hB₁
  { u := p₂.u, v := p₂.v
    hA := .rety inv.hA (sortsTc inv.u p₂.u hu')
    hc := hc
    hB := .rety inv.hB (sortsTc inv.v p₂.v hv')
    hcB := hcB
    hrt := p₂.hrt
    idx := p₂.idx }

/-- every leaf of the closing step is `SubEq` a leaf of the two inputs. -/
theorem structPiJoin_sound {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A B A₁ B₁ A₂ B₂ T : Expr Nat}
    (p₁ : StructPiPayload R Γ A B A₁ B₁ T) (p₂ : StructPiPayload R Γ A B A₂ B₂ T) :
    ∀ ℓ ∈ (structPiJoin hW su hΓ p₁ p₂).leaves,
      ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves, SubEq ℓ ℓ' := by
  intro ℓ hℓ
  have hinv := (EvTy.rety p₁.hrt p₁.idx).invPiT_leaves (A := A₁) (B := B₁) rfl
  have h₁ : ∀ x, x ∈ p₁.hrt.leaves ∨ x ∈ p₁.idx.leaves → x ∈ p₁.leaves ++ p₂.leaves := by
    intro x hx
    simp only [StructPiPayload.leaves, List.mem_append]
    rcases hx with h | h
    · exact .inl (.inl (.inr h))
    · exact .inl (.inr h)
  have hroot : ∀ x ∈ (EvTy.rety p₁.hrt p₁.idx).leaves, x ∈ p₁.leaves ++ p₂.leaves := by
    intro x hx
    simp only [EvTy.leaves, List.mem_append] at hx
    exact h₁ x hx
  have m1 : ∀ x ∈ p₁.leaves, x ∈ p₁.leaves ++ p₂.leaves :=
    fun x hx => List.mem_append.mpr (.inl hx)
  have m2 : ∀ x ∈ p₂.leaves, x ∈ p₁.leaves ++ p₂.leaves :=
    fun x hx => List.mem_append.mpr (.inr hx)
  simp only [structPiJoin, StructPiPayload.leaves, cvCtxConvVar_leaves, EvTy.leaves,
    EvCv.leaves, EvTc.leaves, sortsTc_leaves, List.append_nil, List.mem_append] at hℓ
  rcases hℓ with (((((hA | hc) | hB) | hcB) | hrt) | hidx)
  · obtain ⟨k, hk, hs⟩ := hinv ℓ (by
      simp only [EvInvPi.leaves, List.mem_append]; exact .inl (.inl hA))
    exact ⟨k, hroot k hk, hs⟩
  · rcases hc with (h | h)
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [StructPiPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inr h))))))
    · exact dSubEq_of_mem (m2 ℓ (by
        simp only [StructPiPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inr h))))))
  · obtain ⟨k, hk, hs⟩ := hinv ℓ (by
      simp only [EvInvPi.leaves, List.mem_append]; exact .inl (.inr hB))
    exact ⟨k, hroot k hk, hs⟩
  · rcases hcB with ((h | h) | h) | h
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [StructPiPayload.leaves, List.mem_append]
        exact .inl (.inl (.inr h))))
    · exact dSubEq_of_mem (m2 ℓ (by
        simp only [StructPiPayload.leaves, List.mem_append]
        exact .inl (.inl (.inr h))))
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [StructPiPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inr h))))))
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [StructPiPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inl h))))))
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [StructPiPayload.leaves, List.mem_append]
      exact .inl (.inr hrt)))
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [StructPiPayload.leaves, List.mem_append]
      exact .inr hidx))

/-! ### the certified step diamond -/

/-- The sole context-sensitive producer and its source leaf law. -/
structure StructPiJoinAt (R : List (Jd E n)) (Γ : LCtx) where
  join : ∀ {A B A₁ B₁ A₂ B₂ T : Expr Nat},
    StructPiPayload R Γ A B A₁ B₁ T → StructPiPayload R Γ A B A₂ B₂ T →
      StructPiPayload R Γ A₁ B₁ A₂ B₂ T
  sound : ∀ {A B A₁ B₁ A₂ B₂ T : Expr Nat}
    (p₁ : StructPiPayload R Γ A B A₁ B₁ T) (p₂ : StructPiPayload R Γ A B A₂ B₂ T),
    ∀ ℓ ∈ (join p₁ p₂).leaves, ∃ k ∈ p₁.leaves ++ p₂.leaves, SubEq ℓ k

/-- the diamond on the base steps (`{proofIndex, structPi, sortEq, consts, lit, refl}`).
    The five landed arms are main's; `refl` is this carrier's sixth `EvPar` constructor. -/
def evParDiamondAt {Γ : LCtx} (P : StructPiJoinAt R Γ) {a b c T : Expr Nat} :
    (D₁ : EvPar R Γ a b T) → (D₂ : EvPar R Γ a c T) →
    DOptJoin R Γ b c T (D₁.leaves ++ D₂.leaves)
  | .proofIndex p₁, D₂ =>
      { d := c, left := .step (.base (proofIndexJoin p₁ D₂.rightTy)),
        right := .stay D₂.rightTy,
        sound := fun ℓ hℓ => by
          simp only [DOpt.leaves, DStep.leaves, List.mem_append] at hℓ
          refine dSubEq_of_mem ?_
          simp only [EvPar.leaves, List.mem_append]
          rcases hℓ with h | h
          · rcases proofIndexJoin_leaves p₁ D₂.rightTy ℓ h with h' | h'
            · exact .inl h'
            · exact .inr (D₂.rightTy_leaves ℓ h')
          · exact .inr (D₂.rightTy_leaves ℓ h) }
  | .structPi p₁, .proofIndex p₂ => proofIndexRightJoin (.structPi p₁) p₂
  | .sortEq p₁, .proofIndex p₂ => proofIndexRightJoin (.sortEq p₁) p₂
  | .consts p₁, .proofIndex p₂ => proofIndexRightJoin (.consts p₁) p₂
  | .lit p₁, .proofIndex p₂ => proofIndexRightJoin (.lit p₁) p₂
  | .refl p₁, D₂ => reflLeftJoin p₁ D₂
  | .structPi p₁, .refl p₂ => reflRightJoin (.structPi p₁) p₂
  | .sortEq p₁, .refl p₂ => reflRightJoin (.sortEq p₁) p₂
  | .consts p₁, .refl p₂ => reflRightJoin (.consts p₁) p₂
  | .lit p₁, .refl p₂ => reflRightJoin (.lit p₁) p₂
  | .structPi p₁, .structPi p₂ =>
      { d := _, left := .step (.base (.structPi (P.join p₁ p₂))),
        right := .stay (EvPar.structPi p₂).rightTy,
        sound := fun ℓ hℓ => by
          simp only [DOpt.leaves, DStep.leaves, List.mem_append] at hℓ
          rcases hℓ with h | h
          · exact P.sound p₁ p₂ ℓ h
          · exact dSubEq_of_mem (List.mem_append.mpr
              (.inr ((EvPar.structPi p₂).rightTy_leaves ℓ h))) }
  | .sortEq p₁, .sortEq p₂ =>
      { d := _, left := .step (.base (.sortEq (sortEqJoin p₁ p₂))),
        right := .stay (EvPar.sortEq p₂).rightTy,
        sound := fun ℓ hℓ => by
          simp only [DOpt.leaves, DStep.leaves, List.mem_append] at hℓ
          rcases hℓ with h | h
          · exact dSubEq_of_mem (sortEqJoin_leaves p₁ p₂ ℓ h)
          · exact dSubEq_of_mem (List.mem_append.mpr
              (.inr ((EvPar.sortEq p₂).rightTy_leaves ℓ h))) }
  | .consts p₁, .consts p₂ =>
      { d := _, left := .step (.base (.consts (constsJoin p₁ p₂))),
        right := .stay (EvPar.consts p₂).rightTy,
        sound := fun ℓ hℓ => by
          simp only [DOpt.leaves, DStep.leaves, List.mem_append] at hℓ
          rcases hℓ with h | h
          · exact dSubEq_of_mem (constsJoin_leaves p₁ p₂ ℓ h)
          · exact dSubEq_of_mem (List.mem_append.mpr
              (.inr ((EvPar.consts p₂).rightTy_leaves ℓ h))) }
  | .lit p₁, .lit p₂ =>
      { d := _, left := .stay (EvPar.lit p₁).rightTy,
        right := .stay (EvPar.lit p₂).rightTy,
        sound := fun ℓ hℓ => by
          simp only [DOpt.leaves, List.mem_append] at hℓ
          rcases hℓ with h | h
          · exact dSubEq_of_mem (List.mem_append.mpr
              (.inl ((EvPar.lit p₁).rightTy_leaves ℓ h)))
          · exact dSubEq_of_mem (List.mem_append.mpr
              (.inr ((EvPar.lit p₂).rightTy_leaves ℓ h))) }

/-- the certified step diamond on transported steps: read both bases, close them. -/
def dStepDiamondAt {Γ : LCtx} (P : StructPiJoinAt R Γ) : DStepDiamondAt R Γ := fun s₁ s₂ =>
  let J := evParDiamondAt P s₁.read s₂.read
  { d := J.d, left := J.left, right := J.right,
    sound := dCover_trans J.sound (fun m hm => by
      rcases List.mem_append.mp hm with h | h
      · exact dSubEq_of_mem (List.mem_append.mpr (.inl (s₁.read_leaves m h)))
      · exact dSubEq_of_mem (List.mem_append.mpr (.inr (s₂.read_leaves m h)))) }

/-- The well-formed instance of the one Π-join parameter. -/
def structPiJoinAtWf {Γ : LCtx} (hΓ : CtxWfT E n Γ) : StructPiJoinAt R Γ :=
  ⟨structPiJoin hW su hΓ, structPiJoin_sound hW su hΓ⟩

/-- The landed table signature, with its original branch priority and outputs. -/
def evParDiamondWf {Γ : LCtx} (hΓ : CtxWfT E n Γ) {a b c T : Expr Nat}
    (D₁ : EvPar R Γ a b T) (D₂ : EvPar R Γ a c T) :
    DOptJoin R Γ b c T (D₁.leaves ++ D₂.leaves) :=
  evParDiamondAt (structPiJoinAtWf hW su hΓ) D₁ D₂

/-- The landed step signature, reading the same source steps. -/
def dStepDiamondWf : DStepDiamondWf R := fun hΓ =>
  dStepDiamondAt (structPiJoinAtWf hW su hΓ)

/-- H-D for the landed carrier. -/
def dProcWf : DProcWf R := dProcWf_of_step (dStepDiamondWf hW su)

/-- ... with its leaf contract. -/
theorem dContractWf : DContractWf (fun R => dProcWf (R := R) hW su) :=
  dContractWf_of_step (fun _ => dStepDiamondWf hW su)

/-! ### D2b step-diamond joins (`bvarZetaJoin`, `lamForwardJoin`, `appForwardJoin`) -/

/-- `bvarZeta p₁ × bvarZeta p₂`: joins `p₁.hv` and `p₂.hv` in `Γ.drop (i + 1)` via
    `evParDiamondWf`, weakens across `Γ.take (i + 1)` with `DOpt.wkPrefix` (no `.wk`
    pushed into payloads, per Q3), and retypes from `lift 0 (i + 1) p₁.A` to `T` via
    `invBvarT` on `p₁`'s left-endpoint typing. -/
def bvarZetaJoin {Γ : LCtx} (hΓ : CtxWfT E n Γ) {i : Nat} {v₁ v₂ T : Expr Nat}
    (p₁ : BVarZetaPayload R Γ i v₁ T) (p₂ : BVarZetaPayload R Γ i v₂ T) :
    DOptJoin R Γ (lift 0 (i + 1) v₁) (lift 0 (i + 1) v₂) T (p₁.leaves ++ p₂.leaves) :=
  have hdecl : LocalDecl.letBinding p₁.A p₁.v = .letBinding p₂.A p₂.v :=
    Option.some.inj (p₁.h.symm.trans p₂.h)
  have hA : p₂.A = p₁.A := by injection hdecl with h1 _; exact h1.symm
  have hv : p₂.v = p₁.v := by injection hdecl with _ h2; exact h2.symm
  let hv₂ : EvPar R (Γ.drop (i + 1)) p₁.v v₂ p₁.A := EvPar.dcast rfl hv rfl hA p₂.hv
  let J := evParDiamondWf hW su (ctxWfT_drop hΓ (i + 1)) p₁.hv hv₂
  let Δ := Γ.take (i + 1)
  have hΓ_eq : Δ ++ Γ.drop (i + 1) = Γ := List.take_append_drop (i + 1) Γ
  have hlen : Δ.length = i + 1 := by
    have hlt := get?_some_lt p₁.h
    exact List.length_take_of_le (by omega)
  let inv := (EvTy.rety p₁.hl p₁.idx).invBvarT rfl
  have hlkA : inv.A = lift 0 (i + 1) p₁.A := by
    have hlk₀ : lookupType Γ i = some (lift 0 (i + 1) p₁.A) := by simp only [lookupType, p₁.h]
    exact Option.some.inj (inv.hlk.symm.trans hlk₀)
  let cT : EvTc R Γ (lift 0 (i + 1) p₁.A) T := EvTc.cast rfl hlkA rfl inv.hc
  let oL : DOpt R Γ (lift 0 (i + 1) v₁) (lift 0 (i + 1) J.d) T :=
    (DOpt.dcast hΓ_eq (by rw [hlen]) (by rw [hlen]) (by rw [hlen]) (J.left.wkPrefix Δ)).conv cT
  let oR : DOpt R Γ (lift 0 (i + 1) v₂) (lift 0 (i + 1) J.d) T :=
    (DOpt.dcast hΓ_eq (by rw [hlen]) (by rw [hlen]) (by rw [hlen]) (J.right.wkPrefix Δ)).conv cT
  { d := lift 0 (i + 1) J.d
    left := oL
    right := oR
    sound := fun ℓ hℓ => by
      have hinv := (EvTy.rety p₁.hl p₁.idx).invBvarT_leaves (i := i) rfl
      have hroot : ∀ x ∈ (EvTy.rety p₁.hl p₁.idx).leaves, x ∈ p₁.leaves ++ p₂.leaves := by
        intro x hx
        simp only [EvTy.leaves, BVarZetaPayload.leaves, List.mem_append] at hx ⊢
        rcases hx with h | h
        · exact .inl (.inl (.inl (.inr h)))
        · exact .inl (.inr h)
      have hcT : ∀ x ∈ cT.leaves, ∃ k ∈ p₁.leaves ++ p₂.leaves, SubEq x k := by
        intro x hx
        simp only [cT, EvTc.cast_leaves] at hx
        obtain ⟨k, hk, hs⟩ := hinv x hx
        exact ⟨k, hroot k hk, hs⟩
      have hJcov : ∀ m ∈ p₁.hv.leaves ++ hv₂.leaves,
          ∃ k ∈ p₁.leaves ++ p₂.leaves, SubEq m k := by
        intro m hm
        simp only [hv₂, EvPar.dcast_leaves, BVarZetaPayload.leaves, List.mem_append] at hm
        refine dSubEq_of_mem ?_
        simp only [BVarZetaPayload.leaves, List.mem_append]
        rcases hm with h | h
        · exact .inl (.inl (.inl (.inl h)))
        · exact .inr (.inl (.inl (.inl h)))
      simp only [oL, oR, DOpt.conv_leaves, DOpt.dcast_leaves, DOpt.wkPrefix_leaves,
        List.mem_append] at hℓ
      rcases hℓ with (h | h) | (h | h)
      · exact dCover_trans J.sound hJcov ℓ (List.mem_append.mpr (.inl h))
      · exact hcT ℓ h
      · exact dCover_trans J.sound hJcov ℓ (List.mem_append.mpr (.inr h))
      · exact hcT ℓ h }

/-- `lamForwardJoin`: given `p₁ : LamPayload R Γ A body A₁ body₁ T`,
    `p₂ : LamPayload R Γ A body A₂ body₂ T`, and a forward body step
    `hb₁₂ : EvPar R (.assumption A :: Γ) body₁ body₂ p₁.B`, builds the closing step
    `LamPayload R Γ A₁ body₁ A₂ body₂ T` using `X : XProc R`, `invLamT`, `tyCtxConvVar`,
    and `evParCtxConvVar`. -/
def lamForwardJoin (X : ∀ R : List (Jd E n), XProc R) {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A body A₁ body₁ A₂ body₂ T : Expr Nat}
    (p₁ : LamPayload R Γ A body A₁ body₁ T) (p₂ : LamPayload R Γ A body A₂ body₂ T)
    (hb₁₂ : EvPar R (.assumption A :: Γ) body₁ body₂ p₁.B) :
    LamPayload R Γ A₁ body₁ A₂ body₂ T :=
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  have hu : eqN p₁.u p₂.u := su hW hΓ (p₁.hA.val hcl hinst) (p₂.hA.val hcl hinst)
  let hc : EvCv R Γ A₁ A₂ (.sort p₂.u) :=
    .trans (.symm (.rety p₁.hc (sortsTc p₁.u p₂.u hu))) p₂.hc
  let inv₁ := (EvTy.rety p₁.hrt p₁.idx).invLamT rfl
  have hu' : eqN inv₁.u p₂.u := by
    obtain ⟨_, ⟨hA₁⟩⟩ := convT_endpoints hW hΓ (p₁.hc.val hcl hinst)
    exact eqN_trans' (su hW hΓ (inv₁.hA.val hcl hinst) hA₁) hu
  let cA₁ : EvTc R Γ A₁ A := .ofCv p₁.u (.symm p₁.hc)
  let hB₁ : EvTy R (.assumption A₁ :: Γ) p₁.B (.sort p₁.v) :=
    tyCtxConvVar cA₁ p₁.hA p₁.hB
  let hb₁ : EvPar R (.assumption A₁ :: Γ) body₁ body₂ p₁.B :=
    evParCtxConvVar cA₁ p₁.hA hb₁₂
  let cB₁ : EvTc R (.assumption A₁ :: Γ) inv₁.B p₁.B :=
    (X R (.trans inv₁.hc (.symm p₁.idx))).2
  let idx₁ : EvTc R Γ (.pi A₁ p₁.B) T :=
    .trans (.symm (.piCod inv₁.u inv₁.hA cB₁)) inv₁.hc
  let hrt₁ : EvTy R Γ (.lam A₂ body₂) (.pi A₁ p₁.B) :=
    .rety (.rety p₂.hrt p₂.idx) (.symm idx₁)
  { B := p₁.B
    u := p₂.u
    v := p₁.v
    hc := hc
    hA := .rety inv₁.hA (sortsTc inv₁.u p₂.u hu')
    hB := hB₁
    hb := hb₁
    hrt := hrt₁
    idx := idx₁ }

theorem lamForwardJoin_sound (X : ∀ R : List (Jd E n), XProc R) (hX : XContract X)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {A body A₁ body₁ A₂ body₂ T : Expr Nat}
    (p₁ : LamPayload R Γ A body A₁ body₁ T) (p₂ : LamPayload R Γ A body A₂ body₂ T)
    (hb₁₂ : EvPar R (.assumption A :: Γ) body₁ body₂ p₁.B) :
    ∀ ℓ ∈ (lamForwardJoin hW su X hΓ p₁ p₂ hb₁₂).leaves,
      ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves ++ hb₁₂.leaves, SubEq ℓ ℓ' := by
  intro ℓ hℓ
  let inv₁ := (EvTy.rety p₁.hrt p₁.idx).invLamT rfl
  have hinv := (EvTy.rety p₁.hrt p₁.idx).invLamT_leaves (A := A₁) (body := body₁) rfl
  have m1 : ∀ x ∈ p₁.leaves, x ∈ p₁.leaves ++ p₂.leaves ++ hb₁₂.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hx)))
  have m2 : ∀ x ∈ p₂.leaves, x ∈ p₁.leaves ++ p₂.leaves ++ hb₁₂.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hx)))
  have mb : ∀ x ∈ hb₁₂.leaves, x ∈ p₁.leaves ++ p₂.leaves ++ hb₁₂.leaves :=
    fun x hx => List.mem_append.mpr (.inr hx)
  have hroot : ∀ x ∈ (EvTy.rety p₁.hrt p₁.idx).leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hb₁₂.leaves := by
    intro x hx
    simp only [EvTy.leaves, List.mem_append] at hx
    rcases hx with h | h
    · exact m1 x (by simp only [LamPayload.leaves, List.mem_append]; exact .inl (.inr h))
    · exact m1 x (by simp only [LamPayload.leaves, List.mem_append]; exact .inr h)
  have hinv_cov : ∀ x ∈ inv₁.leaves, ∃ k ∈ p₁.leaves ++ p₂.leaves ++ hb₁₂.leaves, SubEq x k := by
    intro x hx
    obtain ⟨k, hk, hs⟩ := hinv x hx
    exact ⟨k, hroot k hk, hs⟩
  have hcB₁_cov : ∀ x ∈ ((X R (.trans inv₁.hc (.symm p₁.idx))).2).leaves,
      ∃ k ∈ p₁.leaves ++ p₂.leaves ++ hb₁₂.leaves, SubEq x k := by
    intro x hx
    obtain ⟨m, hm, hs⟩ := hX R (.trans inv₁.hc (.symm p₁.idx)) x (List.mem_append.mpr (.inr hx))
    simp only [EvTc.leaves, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨k, hk, hs'⟩ := hinv_cov m (by
        simp only [EvInvLam.leaves, List.mem_append]; exact .inr hm)
      exact ⟨k, hk, dSubEq_trans hs hs'⟩
    · exact ⟨m, m1 m (by simp only [LamPayload.leaves, List.mem_append]; exact .inr hm), hs⟩
  simp only [lamForwardJoin, LamPayload.leaves, tyCtxConvVar_leaves, EvTy.leaves, EvCv.leaves,
    EvTc.leaves, sortsTc_leaves, List.append_nil, List.mem_append] at hℓ
  rcases hℓ with (((((hc | hA) | hB) | hb) | ((hrt | hrtIdx) | ((hidxA | hidxB) | hidxC))) | ((hidxA | hidxB) | hidxC))
  · rcases hc with h | h
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [LamPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inl h))))))
    · exact dSubEq_of_mem (m2 ℓ (by
        simp only [LamPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inl h))))))
  · exact hinv_cov ℓ (by simp only [EvInvLam.leaves, List.mem_append]; exact .inl (.inl hA))
  · rcases hB with (h | h) | h
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [LamPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inr h)))))
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [LamPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inl h))))))
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [LamPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inr h))))))
  · have hb_mem := evParCtxConvVar_leaves (.ofCv p₁.u (.symm p₁.hc)) p₁.hA hb₁₂ ℓ hb
    simp only [EvTc.leaves, EvCv.leaves, List.mem_append] at hb_mem
    rcases hb_mem with (h | h) | h
    · exact dSubEq_of_mem (mb ℓ h)
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [LamPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inl h))))))
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [LamPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inr h))))))
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [LamPayload.leaves, List.mem_append]; exact .inl (.inr hrt)))
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [LamPayload.leaves, List.mem_append]; exact .inr hrtIdx))
  · exact hinv_cov ℓ (by simp only [EvInvLam.leaves, List.mem_append]; exact .inl (.inl hidxA))
  · exact hcB₁_cov ℓ hidxB
  · exact hinv_cov ℓ (by simp only [EvInvLam.leaves, List.mem_append]; exact .inr hidxC)
  · exact hinv_cov ℓ (by simp only [EvInvLam.leaves, List.mem_append]; exact .inl (.inl hidxA))
  · exact hcB₁_cov ℓ hidxB
  · exact hinv_cov ℓ (by simp only [EvInvLam.leaves, List.mem_append]; exact .inr hidxC)

/-- `appForwardJoin`: given `p₁ : AppPayload R Γ f a f₁ a₁ T`,
    `p₂ : AppPayload R Γ f a f₂ a₂ T`, forward steps `hf₁₂ : EvPar R Γ f₁ f₂ p₂.T₀` and
    `ha₁₂ : EvPar R Γ a₁ a₂ p₂.A`, the domain chain `cA : EvTc R Γ p₁.A p₂.A`,
    and the instantiated codomain chain `cInst : EvTc R Γ (instantiate0 a p₂.B) (instantiate0 a₁ p₂.B)`,
    builds the closing `AppPayload R Γ f₁ a₁ f₂ a₂ T` using `p₁.ha.rightTy`,
    `p₂.hPi.invPiT rfl`, and `EvTy.esub`. -/
def appForwardJoin {Γ : LCtx} {f a f₁ a₁ f₂ a₂ T : Expr Nat}
    (p₁ : AppPayload R Γ f a f₁ a₁ T) (p₂ : AppPayload R Γ f a f₂ a₂ T)
    (hf₁₂ : EvPar R Γ f₁ f₂ p₂.T₀) (ha₁₂ : EvPar R Γ a₁ a₂ p₂.A)
    (cA : EvTc R Γ p₁.A p₂.A)
    (cInst : EvTc R Γ (instantiate0 a p₂.B) (instantiate0 a₁ p₂.B)) :
    AppPayload R Γ f₁ a₁ f₂ a₂ T :=
  let ha₁ : EvTy R Γ a₁ p₂.A := .rety p₁.ha.rightTy cA
  let invPi := p₂.hPi.invPiT rfl
  let hTy₁ : EvTy R Γ (instantiate0 a₁ p₂.B) (.sort p₂.v) :=
    EvTy.cast rfl (congrArg (fun x => instantiate 0 x p₂.B) (lift_zero 0 a₁)) rfl
      (EvTy.esub (t := p₂.A) (v := a₁) 0 invPi.u p₂.hB List.getElem?_cons_zero
        (EvTy.cast rfl (lift_zero 0 a₁).symm (lift_zero 0 p₂.A).symm ha₁)
        (EvTy.cast rfl (lift_zero 0 p₂.A).symm rfl invPi.hA))
  { T₀ := p₂.T₀
    A := p₂.A
    B := p₂.B
    u := p₂.u
    v := p₂.v
    w := p₂.v
    hf := hf₁₂
    hc := p₂.hc
    hPi := p₂.hPi
    hB := p₂.hB
    hTy := hTy₁
    ha := ha₁₂
    hr := .rety p₂.hr cInst
    idx := .trans (.symm cInst) p₂.idx }

theorem appForwardJoin_sound {Γ : LCtx} {f a f₁ a₁ f₂ a₂ T : Expr Nat}
    (p₁ : AppPayload R Γ f a f₁ a₁ T) (p₂ : AppPayload R Γ f a f₂ a₂ T)
    (hf₁₂ : EvPar R Γ f₁ f₂ p₂.T₀) (ha₁₂ : EvPar R Γ a₁ a₂ p₂.A)
    (cA : EvTc R Γ p₁.A p₂.A)
    (cInst : EvTc R Γ (instantiate0 a p₂.B) (instantiate0 a₁ p₂.B)) :
    ∀ ℓ ∈ (appForwardJoin p₁ p₂ hf₁₂ ha₁₂ cA cInst).leaves,
      ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves ++ hf₁₂.leaves ++ ha₁₂.leaves ++
        cA.leaves ++ cInst.leaves, SubEq ℓ ℓ' := by
  intro ℓ hℓ
  have hinv := p₂.hPi.invPiT_leaves (A := p₂.A) (B := p₂.B) rfl
  have m1 : ∀ x ∈ p₁.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hf₁₂.leaves ++ ha₁₂.leaves ++ cA.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
      (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hx)))))))))
  have m2 : ∀ x ∈ p₂.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hf₁₂.leaves ++ ha₁₂.leaves ++ cA.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
      (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hx)))))))))
  have mf : ∀ x ∈ hf₁₂.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hf₁₂.leaves ++ ha₁₂.leaves ++ cA.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
      (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hx)))))))
  have ma : ∀ x ∈ ha₁₂.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hf₁₂.leaves ++ ha₁₂.leaves ++ cA.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
      (List.mem_append.mpr (.inr hx)))))
  have mcA : ∀ x ∈ cA.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hf₁₂.leaves ++ ha₁₂.leaves ++ cA.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hx)))
  have mc : ∀ x ∈ cInst.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hf₁₂.leaves ++ ha₁₂.leaves ++ cA.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inr hx)
  simp only [appForwardJoin, AppPayload.leaves, EvTy.cast_leaves, EvTy.leaves, EvTc.leaves,
    List.mem_append] at hℓ
  rcases hℓ with (((((((hf | hc) | hPi) | hB) | ((hTyB | (hTya | hTycA)) | hTyA)) | ha) | (hr | hrc)) | (hidxC | hidx))
  · exact dSubEq_of_mem (mf ℓ hf)
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [AppPayload.leaves, List.mem_append]
      exact .inl (.inl (.inl (.inl (.inl (.inl (.inr hc))))))))
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [AppPayload.leaves, List.mem_append]
      exact .inl (.inl (.inl (.inl (.inl (.inr hPi)))))))
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [AppPayload.leaves, List.mem_append]
      exact .inl (.inl (.inl (.inl (.inr hB))))))
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [AppPayload.leaves, List.mem_append]
      exact .inl (.inl (.inl (.inl (.inr hTyB))))))
  · exact dSubEq_of_mem (m1 ℓ (by
      simp only [AppPayload.leaves, List.mem_append]
      exact .inl (.inl (.inr (p₁.ha.rightTy_leaves ℓ hTya)))))
  · exact dSubEq_of_mem (mcA ℓ hTycA)
  · obtain ⟨k, hk, hs⟩ := hinv ℓ (by
      simp only [EvInvPi.leaves, List.mem_append]; exact .inl (.inl hTyA))
    exact ⟨k, m2 k (by
      simp only [AppPayload.leaves, List.mem_append]
      exact .inl (.inl (.inl (.inl (.inl (.inr hk)))))), hs⟩
  · exact dSubEq_of_mem (ma ℓ ha)
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [AppPayload.leaves, List.mem_append]
      exact .inl (.inr hr)))
  · exact dSubEq_of_mem (mc ℓ hrc)
  · exact dSubEq_of_mem (mc ℓ hidxC)
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [AppPayload.leaves, List.mem_append]
      exact .inr hidx))

/-- `letEForwardJoin`: given `p₁ : LetEPayload R Γ A value body A₁ value₁ body₁ T`,
    `p₂ : LetEPayload R Γ A value body A₂ value₂ body₂ T`, forward steps `hv₁₂` and `hb₁₂`,
    and the transported codomain typing `hB₁`, instantiated sort typing `hTy₁`, and
    instantiated codomain chain `cInst`, builds the closing
    `LetEPayload R Γ A₁ value₁ body₁ A₂ value₂ body₂ T` using `invLetET` and `SortUnique`. -/
def letEForwardJoin {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A value body A₁ value₁ body₁ A₂ value₂ body₂ T : Expr Nat}
    (p₁ : LetEPayload R Γ A value body A₁ value₁ body₁ T)
    (p₂ : LetEPayload R Γ A value body A₂ value₂ body₂ T)
    (hv₁₂ : EvPar R Γ value₁ value₂ A₁)
    (hB₁ : EvTy R (.letBinding A₁ value₁ :: Γ) p₂.B (.sort p₂.w))
    (hTy₁ : EvTy R Γ (instantiate0 value₁ p₂.B) (.sort p₂.w))
    (hb₁₂ : EvPar R (.letBinding A₁ value₁ :: Γ) body₁ body₂ p₂.B)
    (cInst : EvTc R Γ (instantiate0 value p₂.B) (instantiate0 value₁ p₂.B)) :
    LetEPayload R Γ A₁ value₁ body₁ A₂ value₂ body₂ T :=
  let hcl := envClosed_of_envWfT hW
  let hinst := envMembersSubstStable_of_envWfT hW
  have hu : eqN p₁.u p₂.u := su hW hΓ (p₁.hA.val hcl hinst) (p₂.hA.val hcl hinst)
  let hc : EvCv R Γ A₁ A₂ (.sort p₂.u) :=
    .trans (.symm (.rety p₁.hc (sortsTc p₁.u p₂.u hu))) p₂.hc
  let inv₁ := (EvTy.rety p₁.hrt p₁.idx).invLetET rfl
  have hu' : eqN inv₁.u p₂.u := by
    obtain ⟨_, ⟨hA₁⟩⟩ := convT_endpoints hW hΓ (p₁.hc.val hcl hinst)
    exact eqN_trans' (su hW hΓ (inv₁.hA.val hcl hinst) hA₁) hu
  { B := p₂.B
    u := p₂.u
    w := p₂.w
    hc := hc
    hA := .rety inv₁.hA (sortsTc inv₁.u p₂.u hu')
    hv := hv₁₂
    hB := hB₁
    hTy := hTy₁
    hb := hb₁₂
    hrt := .rety p₂.hrt cInst
    idx := .trans (.symm cInst) p₂.idx }

theorem letEForwardJoin_sound {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {A value body A₁ value₁ body₁ A₂ value₂ body₂ T : Expr Nat}
    (p₁ : LetEPayload R Γ A value body A₁ value₁ body₁ T)
    (p₂ : LetEPayload R Γ A value body A₂ value₂ body₂ T)
    (hv₁₂ : EvPar R Γ value₁ value₂ A₁)
    (hB₁ : EvTy R (.letBinding A₁ value₁ :: Γ) p₂.B (.sort p₂.w))
    (hTy₁ : EvTy R Γ (instantiate0 value₁ p₂.B) (.sort p₂.w))
    (hb₁₂ : EvPar R (.letBinding A₁ value₁ :: Γ) body₁ body₂ p₂.B)
    (cInst : EvTc R Γ (instantiate0 value p₂.B) (instantiate0 value₁ p₂.B)) :
    ∀ ℓ ∈ (letEForwardJoin hW su hΓ p₁ p₂ hv₁₂ hB₁ hTy₁ hb₁₂ cInst).leaves,
      ∃ ℓ' ∈ p₁.leaves ++ p₂.leaves ++ hv₁₂.leaves ++ hB₁.leaves ++
        hTy₁.leaves ++ hb₁₂.leaves ++ cInst.leaves, SubEq ℓ ℓ' := by
  intro ℓ hℓ
  have hinv := (EvTy.rety p₁.hrt p₁.idx).invLetET_leaves (A := A₁) (value := value₁) (body := body₁) rfl
  have m1 : ∀ x ∈ p₁.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hv₁₂.leaves ++ hB₁.leaves ++ hTy₁.leaves ++ hb₁₂.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
      (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
        (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hx)))))))))))
  have m2 : ∀ x ∈ p₂.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hv₁₂.leaves ++ hB₁.leaves ++ hTy₁.leaves ++ hb₁₂.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
      (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
        (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hx)))))))))))
  have mv : ∀ x ∈ hv₁₂.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hv₁₂.leaves ++ hB₁.leaves ++ hTy₁.leaves ++ hb₁₂.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
      (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
        (List.mem_append.mpr (.inr hx)))))))))
  have mB₁ : ∀ x ∈ hB₁.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hv₁₂.leaves ++ hB₁.leaves ++ hTy₁.leaves ++ hb₁₂.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
      (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hx)))))))
  have mTy₁ : ∀ x ∈ hTy₁.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hv₁₂.leaves ++ hB₁.leaves ++ hTy₁.leaves ++ hb₁₂.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
      (List.mem_append.mpr (.inr hx)))))
  have mb : ∀ x ∈ hb₁₂.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hv₁₂.leaves ++ hB₁.leaves ++ hTy₁.leaves ++ hb₁₂.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hx)))
  have mc : ∀ x ∈ cInst.leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hv₁₂.leaves ++ hB₁.leaves ++ hTy₁.leaves ++ hb₁₂.leaves ++ cInst.leaves :=
    fun x hx => List.mem_append.mpr (.inr hx)
  have hroot : ∀ x ∈ (EvTy.rety p₁.hrt p₁.idx).leaves,
      x ∈ p₁.leaves ++ p₂.leaves ++ hv₁₂.leaves ++ hB₁.leaves ++ hTy₁.leaves ++ hb₁₂.leaves ++ cInst.leaves := by
    intro x hx
    simp only [EvTy.leaves, List.mem_append] at hx
    rcases hx with h | h
    · exact m1 x (by simp only [LetEPayload.leaves, List.mem_append]; exact .inl (.inr h))
    · exact m1 x (by simp only [LetEPayload.leaves, List.mem_append]; exact .inr h)
  simp only [letEForwardJoin, LetEPayload.leaves, EvTy.leaves, EvCv.leaves, EvTc.leaves,
    sortsTc_leaves, List.append_nil, List.mem_append] at hℓ
  rcases hℓ with (((((((hc | hA) | hv) | hB) | hTy) | hb) | (hrt | hrc)) | (hidxC | hidx))
  · rcases hc with h | h
    · exact dSubEq_of_mem (m1 ℓ (by
        simp only [LetEPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inl (.inl (.inl h))))))))
    · exact dSubEq_of_mem (m2 ℓ (by
        simp only [LetEPayload.leaves, List.mem_append]
        exact .inl (.inl (.inl (.inl (.inl (.inl (.inl h))))))))
  · obtain ⟨k, hk, hs⟩ := hinv ℓ (by
      simp only [EvInvLetE.leaves, List.mem_append]; exact .inl (.inl (.inl hA)))
    exact ⟨k, hroot k hk, hs⟩
  · exact dSubEq_of_mem (mv ℓ hv)
  · exact dSubEq_of_mem (mB₁ ℓ hB)
  · exact dSubEq_of_mem (mTy₁ ℓ hTy)
  · exact dSubEq_of_mem (mb ℓ hb)
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [LetEPayload.leaves, List.mem_append]; exact .inl (.inr hrt)))
  · exact dSubEq_of_mem (mc ℓ hrc)
  · exact dSubEq_of_mem (mc ℓ hidxC)
  · exact dSubEq_of_mem (m2 ℓ (by
      simp only [LetEPayload.leaves, List.mem_append]; exact .inr hidx))

end StructPi

/-! ### non-vacuity and regression pins -/

namespace DTilePins
open IrrPins PEqTProofFront

/-- `EvPar.rightTy` on the concrete `proofIndex` producer from `IrrPins`. -/
theorem pin_proofIndex_rightTy :
    producer.rightTy = payload.rightTy := rfl

/-- a 1-step `EvParStar` under `.wk` and `.conv`, viewed through `EvParStar.spine`. -/
def pinStarWk :
    EvParStar [root] [.assumption (.sort .zero)] (lift 0 1 p) (lift 0 1 q) (lift 0 1 P) :=
  .wk (.assumption (.sort .zero)) 0 (.tail producer (.refl producer.rightTy))

theorem pin_spine_wk_leaves :
    pinStarWk.spine.leaves =
      (DSpine.tail (.base producer) (.refl producer.rightTy)).leaves :=
  DSpine.wk_leaves (.assumption (.sort .zero)) 0 _

/-- `proofIndexJoin` closes a non-identity peak `p ⇒ q` and `p ⇒ p` with `q ≠ p`. -/
def pinJoinStep : EvPar [root] [] q p P :=
  proofIndexJoin payload payload.leftTy

def pinJoinTile : DTile [root] :=
  pinJoinStep.toDTile (envClosed_of_envWfT EnvWfT.empty)
    (envMembersSubstStable_of_envWfT EnvWfT.empty) [root]

theorem pin_proofIndexJoin_nonid : q ≠ p := fun h => nonidentity h.symm

/-- `cvCtxConvVar` moves a conversion under `.assumption (.sort (.max .zero .zero))`
    to `.assumption (.sort .zero)` with leaves preserved by `rfl`. -/
def pinDomL : Expr Nat := .sort (.max .zero .zero)
def pinDomR : Expr Nat := .sort .zero

theorem pin_doms_ne : pinDomL ≠ pinDomR := by decide

def pinChainDom : EvTc ([] : List (Jd emptyEnv 0)) [] pinDomR pinDomL :=
  sortsTc .zero (.max .zero .zero) (fun _ => rfl)

def pinBodyCv : EvCv ([] : List (Jd emptyEnv 0)) [.assumption pinDomL]
    (.sort (.max .zero .zero)) (.sort .zero) (.sort (.succ (.max .zero .zero))) :=
  .sorts (.max .zero .zero) .zero (fun _ => rfl)

def pinMovedCv : EvCv ([] : List (Jd emptyEnv 0)) [.assumption pinDomR]
    (.sort (.max .zero .zero)) (.sort .zero) (.sort (.succ (.max .zero .zero))) :=
  cvCtxConvVar pinChainDom (.sort (.max .zero .zero)) pinBodyCv

theorem pin_cvCtxConvVar_leaves : pinMovedCv.leaves = [] := rfl

/-- concrete `structPi × structPi` peak at distinct domain sort annotations `pinDomL ≠ pinDomR`. -/
def pinTargetPi : HasTyT emptyEnv 0 [] (.pi pinDomR (.bvar 0))
    (.sort (.imax (.succ .zero) .zero)) :=
  .pi [] pinDomR (.succ .zero) (.bvar 0) .zero (.sort [] .zero) (.bvar _ 0 pinDomR rfl)

def pinPiRoot : Jd emptyEnv 0 := .ty pinTargetPi

def pinStructPiPayload :
    StructPiPayload [pinPiRoot] [] pinDomL (.bvar 0) pinDomR (.bvar 0)
      (.sort (.imax (.succ (.max .zero .zero)) .zero)) where
  u := .succ (.max .zero .zero)
  v := .zero
  hA := .sort (.max .zero .zero)
  hc := .sorts (.max .zero .zero) .zero (fun _ => rfl)
  hB := .rety (.var 0 pinDomL rfl)
    (sortsTc (.max .zero .zero) .zero (fun _ => rfl))
  hcB := .refl (.rety (.var 0 pinDomL rfl)
    (sortsTc (.max .zero .zero) .zero (fun _ => rfl)))
  hrt := .rety (.lit pinTargetPi ⟨pinPiRoot, .head _, .inl rfl⟩)
    (sortsTc (.imax (.succ .zero) .zero) (.imax (.succ (.max .zero .zero)) .zero) (fun _ => rfl))
  idx := .refl [] (.sort (.imax (.succ (.max .zero .zero)) .zero))

def pinStructPiJoin (su : F8A2Support.SortUnique emptyEnv 0) :
    StructPiPayload [pinPiRoot] [] pinDomR (.bvar 0) pinDomR (.bvar 0)
      (.sort (.imax (.succ (.max .zero .zero)) .zero)) :=
  structPiJoin EnvWfT.empty su CtxWfT.nil pinStructPiPayload pinStructPiPayload

theorem pin_structPiJoin_sound (su : F8A2Support.SortUnique emptyEnv 0) :
    ∀ ℓ ∈ (pinStructPiJoin su).leaves,
      ∃ ℓ' ∈ pinStructPiPayload.leaves ++ pinStructPiPayload.leaves, SubEq ℓ ℓ' :=
  structPiJoin_sound EnvWfT.empty su CtxWfT.nil pinStructPiPayload pinStructPiPayload

/-- concrete `dProcWf` and `dContractWf` on a diverging `EvParStar` pair (`p ⇒ q` vs `p ⇒ p`). -/
def pinStarLeft : EvParStar [root] [] p q P :=
  .tail producer (.refl producer.rightTy)

def pinStarRight : EvParStar [root] [] p p P :=
  .refl payload.leftTy

def pinDiamondOut (su : F8A2Support.SortUnique emptyEnv 0) :
    Σ' d : Expr Nat, EvParStar [root] [] q d P × EvParStar [root] [] p d P :=
  dProcWf EnvWfT.empty su CtxWfT.nil pinStarLeft pinStarRight

theorem pin_dContractWf (su : F8A2Support.SortUnique emptyEnv 0) :
    ∀ ℓ ∈ (pinDiamondOut su).2.1.leaves ++ (pinDiamondOut su).2.2.leaves,
      ∃ ℓ' ∈ pinStarLeft.leaves ++ pinStarRight.leaves, SubEq ℓ ℓ' :=
  dContractWf EnvWfT.empty su [root] CtxWfT.nil pinStarLeft pinStarRight

/-- concrete `sortEq × sortEq` peak at non-identical levels `.max .zero .zero ⇒ .zero`
    and `.max .zero .zero ⇒ .imax .zero .zero`, closed by `sortEqJoin` with `leaves = []`. -/
def pinSortEqL : SortEqPayload ([] : List (Jd emptyEnv 0)) []
    (.max .zero .zero) .zero (.sort (.succ (.max .zero .zero))) :=
  .ofSorts [] (.max .zero .zero) .zero (fun _ => rfl)

def pinSortEqR : SortEqPayload ([] : List (Jd emptyEnv 0)) []
    (.max .zero .zero) (.imax .zero .zero) (.sort (.succ (.max .zero .zero))) :=
  .ofSorts [] (.max .zero .zero) (.imax .zero .zero) (fun _ => rfl)

def pinSortEqJoin : SortEqPayload ([] : List (Jd emptyEnv 0)) []
    .zero (.imax .zero .zero) (.sort (.succ (.max .zero .zero))) :=
  sortEqJoin pinSortEqL pinSortEqR

theorem pin_sortEqJoin_leaves : pinSortEqJoin.leaves = [] := rfl

/-- concrete `Valley.ofSorts` and its `DTile` with `leaves = []` (W-X-LEVELS). -/
def pinValleySorts : Valley ([] : List (Jd emptyEnv 0)) []
    (.sort (.max .zero .zero)) (.sort .zero) (.sort (.succ (.max .zero .zero))) :=
  .ofSorts [] (.max .zero .zero) .zero (fun _ => rfl)

theorem pin_valleySorts_leaves : pinValleySorts.leaves = [] := rfl

def pinSortEqDTile : DTile ([] : List (Jd emptyEnv 0)) :=
  (EvPar.ofSorts [] (.max .zero .zero) .zero (fun _ => rfl)).toDTile
    (envClosed_of_envWfT EnvWfT.empty) (envMembersSubstStable_of_envWfT EnvWfT.empty) []

/-- concrete `substVal0` pin on `EvPar.sortEq` under assumption substitution at `j = 0`. -/
def pinSortEqInAssump : EvPar ([] : List (Jd emptyEnv 0))
    [.assumption (.sort (.succ .zero))] (.sort (.max .zero .zero)) (.sort .zero)
    (.sort (.succ (.max .zero .zero))) :=
  .ofSorts [.assumption (.sort (.succ .zero))] (.max .zero .zero) .zero (fun _ => rfl)

def pinSortEqSubstVal :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 []
      (.sort (.max .zero .zero)) (.sort .zero) (.sort (.succ (.max .zero .zero))) :=
  pinSortEqInAssump.substVal0 (v := .sort .zero) (envClosed_of_envWfT EnvWfT.empty)
    (envMembersSubstStable_of_envWfT EnvWfT.empty) 0 rfl (.sort [] .zero)

/-- concrete `refl × sortEq` peak closed by `reflLeftJoin` with `leaves = []`. -/
def pinReflStep : ReflPayload ([] : List (Jd emptyEnv 0)) []
    (.sort (.max .zero .zero)) (.sort (.succ (.max .zero .zero))) :=
  .ofTy (.sort (.max .zero .zero))

def pinReflJoin : DOptJoin ([] : List (Jd emptyEnv 0)) []
    (.sort (.max .zero .zero)) (.sort .zero) (.sort (.succ (.max .zero .zero))) [] :=
  reflLeftJoin pinReflStep (.sortEq pinSortEqL)

theorem pin_reflJoin_leaves :
    pinReflJoin.left.leaves ++ pinReflJoin.right.leaves = [] := rfl

/-- concrete `tyCtxConvVar` and `evParCtxConvVar` pins with `leaves = []`. -/
def pinMovedTy : EvTy ([] : List (Jd emptyEnv 0)) [.assumption pinDomR]
    (.sort (.max .zero .zero)) (.sort (.succ (.max .zero .zero))) :=
  tyCtxConvVar pinChainDom (.sort (.max .zero .zero)) (.sort (.max .zero .zero))

theorem pin_tyCtxConvVar_leaves : pinMovedTy.leaves = [] := rfl

def pinBodyEvPar : EvPar ([] : List (Jd emptyEnv 0)) [.assumption pinDomL]
    (.sort (.max .zero .zero)) (.sort .zero) (.sort (.succ (.max .zero .zero))) :=
  .ofSorts [.assumption pinDomL] (.max .zero .zero) .zero (fun _ => rfl)

def pinMovedEvPar : EvPar ([] : List (Jd emptyEnv 0)) [.assumption pinDomR]
    (.sort (.max .zero .zero)) (.sort .zero) (.sort (.succ (.max .zero .zero))) :=
  evParCtxConvVar pinChainDom (.sort (.max .zero .zero)) pinBodyEvPar

theorem pin_evParCtxConvVar_leaves :
    ∀ ℓ ∈ pinMovedEvPar.leaves, ℓ ∈ ([] : List (Jd emptyEnv 0)) :=
  evParCtxConvVar_leaves pinChainDom (.sort (.max .zero .zero)) pinBodyEvPar

/-- concrete `DeltaPayload`, `deltaJoin`, `DeltaPayload.substVal`, and `DeltaPayload.toDTile`. -/
def pinDeltaMember : CheckedMember :=
  ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩

def pinDeltaEnv : ResolvedEnv :=
  extendEnv emptyEnv 0 pinDeltaMember

def pinDeltaEnvWf : EnvWfT pinDeltaEnv :=
  .definition emptyEnv 0 (.sort (.succ .zero)) (.sort .zero) (.succ (.succ .zero))
    .empty rfl (.sort [] (.succ .zero)) (.sort [] .zero)
    (fun _ => rfl) (fun _ => rfl) rfl rfl

def pinDeltaPayload (Γ : LCtx) :
    DeltaPayload ([] : List (Jd pinDeltaEnv 0)) Γ 0 [] (.sort .zero) (.sort (.succ .zero)) where
  m := pinDeltaMember
  T₀ := .sort (.succ .zero)
  hres := rfl
  hbody := rfl
  htr := rfl
  hlen := rfl
  hwf := rfl
  hl := .const 0 [] pinDeltaMember rfl rfl rfl
  hr := .sort .zero
  idx := .refl Γ (.sort (.succ .zero))

def pinDeltaJoin :
    DOptJoin ([] : List (Jd pinDeltaEnv 0)) [] (.sort .zero) (.sort .zero)
      (.sort (.succ .zero)) [] :=
  deltaJoin (pinDeltaPayload []) (pinDeltaPayload [])

theorem pin_deltaJoin_leaves :
    pinDeltaJoin.left.leaves ++ pinDeltaJoin.right.leaves = [] := rfl

def pinDeltaSubstVal :
    ParRedT (PEqLeafT pinDeltaEnv 0) pinDeltaEnv 0 []
      (.const 0 []) (.sort .zero) (.sort (.succ .zero)) :=
  (pinDeltaPayload [.assumption (.sort (.succ .zero))]).substVal (v := .sort .zero)
    (envClosed_of_envWfT pinDeltaEnvWf) (envMembersSubstStable_of_envWfT pinDeltaEnvWf)
    0 rfl (.sort [] .zero)

def pinDeltaTile : DTile ([] : List (Jd pinDeltaEnv 0)) :=
  (pinDeltaPayload []).toDTile
    (envClosed_of_envWfT pinDeltaEnvWf) (envMembersSubstStable_of_envWfT pinDeltaEnvWf) []

/-- concrete `BVarZetaPayload`, `bvarZetaJoin` on diverging let-value steps, and `substVal`. -/
def pinZetaCtx : LCtx :=
  [.letBinding (.sort (.succ (.max .zero .zero))) (.sort (.max .zero .zero))]

def pinZetaCtxWf : CtxWfT emptyEnv 0 pinZetaCtx :=
  .letBinding [] (.sort (.succ (.max .zero .zero)))
    (.succ (.succ (.max .zero .zero))) (.sort (.max .zero .zero)) .nil
    (.sort [] (.succ (.max .zero .zero))) (.sort [] (.max .zero .zero))

def pinBVarZetaL :
    BVarZetaPayload ([] : List (Jd emptyEnv 0)) pinZetaCtx 0
      (.sort .zero) (.sort (.succ (.max .zero .zero))) where
  A := .sort (.succ (.max .zero .zero))
  v := .sort (.max .zero .zero)
  T₀ := .sort (.succ (.max .zero .zero))
  h := rfl
  hv := .ofSorts [] (.max .zero .zero) .zero (fun _ => rfl)
  hl := .var 0 (.sort (.succ (.max .zero .zero))) rfl
  hr := .sortsRight (.max .zero .zero) .zero (fun _ => rfl)
  idx := .refl pinZetaCtx (.sort (.succ (.max .zero .zero)))

def pinBVarZetaR :
    BVarZetaPayload ([] : List (Jd emptyEnv 0)) pinZetaCtx 0
      (.sort (.imax .zero .zero)) (.sort (.succ (.max .zero .zero))) where
  A := .sort (.succ (.max .zero .zero))
  v := .sort (.max .zero .zero)
  T₀ := .sort (.succ (.max .zero .zero))
  h := rfl
  hv := .ofSorts [] (.max .zero .zero) (.imax .zero .zero) (fun _ => rfl)
  hl := .var 0 (.sort (.succ (.max .zero .zero))) rfl
  hr := .sortsRight (.max .zero .zero) (.imax .zero .zero) (fun _ => rfl)
  idx := .refl pinZetaCtx (.sort (.succ (.max .zero .zero)))

def pinBVarZetaJoin (su : F8A2Support.SortUnique emptyEnv 0) :
    DOptJoin ([] : List (Jd emptyEnv 0)) pinZetaCtx
      (.sort .zero) (.sort (.imax .zero .zero)) (.sort (.succ (.max .zero .zero))) [] :=
  bvarZetaJoin EnvWfT.empty su pinZetaCtxWf pinBVarZetaL pinBVarZetaR

def pinZetaAssumpCtx : LCtx :=
  [.letBinding (.sort (.succ (.max .zero .zero))) (.sort (.max .zero .zero)),
   .assumption (.sort (.succ .zero))]

def pinBVarZetaInAssump :
    BVarZetaPayload ([] : List (Jd emptyEnv 0)) pinZetaAssumpCtx 0
      (.sort .zero) (.sort (.succ (.max .zero .zero))) where
  A := .sort (.succ (.max .zero .zero))
  v := .sort (.max .zero .zero)
  T₀ := .sort (.succ (.max .zero .zero))
  h := rfl
  hv := .ofSorts [.assumption (.sort (.succ .zero))] (.max .zero .zero) .zero (fun _ => rfl)
  hl := .var 0 (.sort (.succ (.max .zero .zero))) rfl
  hr := .sortsRight (.max .zero .zero) .zero (fun _ => rfl)
  idx := .refl pinZetaAssumpCtx (.sort (.succ (.max .zero .zero)))

def pinBVarZetaSubstVal :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 pinZetaCtx
      (.bvar 0) (.sort .zero) (.sort (.succ (.max .zero .zero))) :=
  pinBVarZetaInAssump.substVal (w := .sort .zero) (envClosed_of_envWfT EnvWfT.empty)
    (envMembersSubstStable_of_envWfT EnvWfT.empty) 1 rfl
    (.sort pinZetaCtx .zero) (.sort [] .zero)

/-- concrete `LamPayload` and `LamPayload.substVal`. -/
def pinTargetLam (Γ : LCtx) : HasTyT emptyEnv 0 Γ (.lam pinDomR (.sort .zero))
    (.pi pinDomR (.sort (.succ .zero))) :=
  .lam Γ pinDomR (.succ .zero) (.sort .zero) (.sort (.succ .zero))
    (.sort Γ .zero) (.sort (.assumption pinDomR :: Γ) .zero)

def pinLamRootAssump : Jd emptyEnv 0 :=
  .ty (pinTargetLam [.assumption (.sort (.succ .zero))])

def pinLamInAssump :
    LamPayload [pinLamRootAssump] [.assumption (.sort (.succ .zero))]
      pinDomR (.sort (.max .zero .zero)) pinDomR (.sort .zero)
      (.pi pinDomR (.sort (.succ (.max .zero .zero)))) where
  B := .sort (.succ (.max .zero .zero))
  u := .succ .zero
  v := .succ (.succ (.max .zero .zero))
  hc := .refl (.sort .zero)
  hA := .sort .zero
  hB := .sort (.succ (.max .zero .zero))
  hb := .ofSorts [.assumption pinDomR, .assumption (.sort (.succ .zero))]
    (.max .zero .zero) .zero (fun _ => rfl)
  hrt := .rety (.lit (pinTargetLam [.assumption (.sort (.succ .zero))])
      ⟨pinLamRootAssump, .head _, .inl rfl⟩)
    (.piCod (.succ .zero) (.sort .zero)
      (sortsTc (.succ .zero) (.succ (.max .zero .zero)) (fun _ => rfl)))
  idx := .refl [.assumption (.sort (.succ .zero))]
    (.pi pinDomR (.sort (.succ (.max .zero .zero))))

def pinLamSubstVal :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 []
      (.lam pinDomR (.sort (.max .zero .zero))) (.lam pinDomR (.sort .zero))
      (.pi pinDomR (.sort (.succ (.max .zero .zero)))) :=
  pinLamInAssump.substVal (w := .sort .zero) (envClosed_of_envWfT EnvWfT.empty)
    (envMembersSubstStable_of_envWfT EnvWfT.empty) 0 rfl (.sort [] .zero)

/-- concrete `AppPayload`, `appForwardJoin`, and `AppPayload.substVal`. -/
def pinAppDom : Expr Nat := .sort (.succ (.max .zero .zero))
def pinAppCod : Expr Nat := .sort (.succ .zero)
def pinAppFun : Expr Nat := .lam pinAppDom (.sort .zero)

def pinAppPiTy (Γ : LCtx) : HasTyT emptyEnv 0 Γ (.pi pinAppDom pinAppCod)
    (.sort (.imax (.succ (.succ (.max .zero .zero))) (.succ (.succ .zero)))) :=
  .pi Γ pinAppDom (.succ (.succ (.max .zero .zero))) pinAppCod (.succ (.succ .zero))
    (.sort Γ (.succ (.max .zero .zero))) (.sort (.assumption pinAppDom :: Γ) (.succ .zero))

def pinAppFunTy (Γ : LCtx) : HasTyT emptyEnv 0 Γ pinAppFun (.pi pinAppDom pinAppCod) :=
  .lam Γ pinAppDom (.succ (.succ (.max .zero .zero))) (.sort .zero) pinAppCod
    (.sort Γ (.succ (.max .zero .zero))) (.sort (.assumption pinAppDom :: Γ) .zero)

def pinAppResTy (Γ : LCtx) : HasTyT emptyEnv 0 Γ (.app pinAppFun (.sort .zero)) pinAppCod :=
  .app Γ pinAppFun (.sort .zero) pinAppDom pinAppCod
    (pinAppFunTy Γ)
    (.conv Γ (.sort .zero) (.sort (.succ .zero)) pinAppDom (.succ (.succ .zero))
      (.sort Γ .zero)
      (.sorts Γ (.succ .zero) (.succ (.max .zero .zero)) (fun _ => rfl)))

def pinAppRoots (Γ : LCtx) : List (Jd emptyEnv 0) :=
  [.ty (pinAppFunTy Γ), .ty (pinAppPiTy Γ), .ty (pinAppResTy Γ)]

def pinAppPayload (Γ : LCtx) :
    AppPayload (pinAppRoots Γ) Γ pinAppFun (.sort (.max .zero .zero))
      pinAppFun (.sort .zero) pinAppCod where
  T₀ := .pi pinAppDom pinAppCod
  A := pinAppDom
  B := pinAppCod
  u := .succ (.succ (.max .zero .zero))
  v := .succ (.succ .zero)
  w := .succ (.succ .zero)
  hf := .ofTy (.lit (pinAppFunTy Γ) ⟨_, .head _, .inl rfl⟩)
  hc := .refl Γ (.pi pinAppDom pinAppCod)
  hPi := .lit (pinAppPiTy Γ) ⟨_, .tail _ (.head _), .inl rfl⟩
  hB := .sort (.succ .zero)
  hTy := .sort (.succ .zero)
  ha := .ofSorts Γ (.max .zero .zero) .zero (fun _ => rfl)
  hr := .lit (pinAppResTy Γ) ⟨_, .tail _ (.tail _ (.head _)), .inl rfl⟩
  idx := .refl Γ pinAppCod

def pinAppForwardJoin :
    AppPayload (pinAppRoots []) [] pinAppFun (.sort .zero)
      pinAppFun (.sort .zero) pinAppCod :=
  appForwardJoin (pinAppPayload []) (pinAppPayload [])
    (EvPar.ofTy (pinAppPayload []).hf.rightTy)
    (EvPar.ofTy (pinAppPayload []).ha.rightTy)
    (.refl [] pinAppDom) (.refl [] pinAppCod)

def pinAppSubstVal :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 []
      (.app pinAppFun (.sort (.max .zero .zero))) (.app pinAppFun (.sort .zero)) pinAppCod :=
  (pinAppPayload [.assumption (.sort (.succ .zero))]).substVal (w₀ := .sort .zero)
    (envClosed_of_envWfT EnvWfT.empty) (envMembersSubstStable_of_envWfT EnvWfT.empty)
    0 rfl (.sort [] .zero)

/-- concrete `LetEPayload`, `letEForwardJoin`, and `LetEPayload.substVal`. -/
def pinTargetLetE (Γ : LCtx) :
    HasTyT emptyEnv 0 Γ (.letE pinAppDom (.sort .zero) (.sort .zero)) (.sort (.succ .zero)) :=
  .letE Γ pinAppDom (.succ (.succ (.max .zero .zero))) (.sort .zero)
    (.sort (.succ .zero)) (.sort .zero)
    (.sort Γ (.succ (.max .zero .zero)))
    (.conv Γ (.sort .zero) (.sort (.succ .zero)) pinAppDom (.succ (.succ .zero))
      (.sort Γ .zero)
      (.sorts Γ (.succ .zero) (.succ (.max .zero .zero)) (fun _ => rfl)))
    (.sort (.letBinding pinAppDom (.sort .zero) :: Γ) .zero)

def pinLetERoot (Γ : LCtx) : Jd emptyEnv 0 := .ty (pinTargetLetE Γ)

def pinLetEPayload (Γ : LCtx) :
    LetEPayload [pinLetERoot Γ] Γ
      pinAppDom (.sort (.max .zero .zero)) (.sort (.max .zero .zero))
      pinAppDom (.sort .zero) (.sort .zero) pinAppDom where
  B := pinAppDom
  u := .succ (.succ (.max .zero .zero))
  w := .succ (.succ (.max .zero .zero))
  hc := .refl (.sort (.succ (.max .zero .zero)))
  hA := .sort (.succ (.max .zero .zero))
  hv := .ofSorts Γ (.max .zero .zero) .zero (fun _ => rfl)
  hB := .sort (.succ (.max .zero .zero))
  hTy := .sort (.succ (.max .zero .zero))
  hb := .ofSorts (.letBinding pinAppDom (.sort (.max .zero .zero)) :: Γ)
    (.max .zero .zero) .zero (fun _ => rfl)
  hrt := .rety (.lit (pinTargetLetE Γ) ⟨pinLetERoot Γ, .head _, .inl rfl⟩)
    (sortsTc (.succ .zero) (.succ (.max .zero .zero)) (fun _ => rfl))
  idx := .refl Γ pinAppDom

def pinLetEForwardJoin (su : F8A2Support.SortUnique emptyEnv 0) :
    LetEPayload [pinLetERoot []] []
      pinAppDom (.sort .zero) (.sort .zero)
      pinAppDom (.sort .zero) (.sort .zero) pinAppDom :=
  letEForwardJoin EnvWfT.empty su CtxWfT.nil (pinLetEPayload []) (pinLetEPayload [])
    (EvPar.ofTy (pinLetEPayload []).hv.rightTy)
    (.sort (.succ (.max .zero .zero))) (.sort (.succ (.max .zero .zero)))
    (EvPar.ofTy (.sortsRight (.max .zero .zero) .zero (fun _ => rfl)))
    (.refl [] pinAppDom)

def pinLetESubstVal :
    ParRedT (PEqLeafT emptyEnv 0) emptyEnv 0 []
      (.letE pinAppDom (.sort (.max .zero .zero)) (.sort (.max .zero .zero)))
      (.letE pinAppDom (.sort .zero) (.sort .zero)) pinAppDom :=
  (pinLetEPayload [.assumption (.sort (.succ .zero))]).substVal (w₀ := .sort .zero)
    (envClosed_of_envWfT EnvWfT.empty) (envMembersSubstStable_of_envWfT EnvWfT.empty)
    0 rfl (.sort [] .zero)

end DTilePins

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.EvCv.dcast
#print axioms Rcic.Declarative.F8Measure.EvCv.dcast_leaves
#print axioms Rcic.Declarative.F8Measure.EvPar.castR
#print axioms Rcic.Declarative.F8Measure.EvPar.castR_leaves
#print axioms Rcic.Declarative.F8Measure.EvPar.dcast
#print axioms Rcic.Declarative.F8Measure.EvPar.dcast_leaves
#print axioms Rcic.Declarative.F8Measure.EvTy.wkPrefix
#print axioms Rcic.Declarative.F8Measure.EvTy.wkPrefix_leaves
#print axioms Rcic.Declarative.F8Measure.DStep.dcast
#print axioms Rcic.Declarative.F8Measure.DStep.dcast_leaves
#print axioms Rcic.Declarative.F8Measure.DStep.wkPrefix
#print axioms Rcic.Declarative.F8Measure.DStep.wkPrefix_leaves
#print axioms Rcic.Declarative.F8Measure.DOpt.dcast
#print axioms Rcic.Declarative.F8Measure.DOpt.dcast_leaves
#print axioms Rcic.Declarative.F8Measure.DOpt.wkPrefix
#print axioms Rcic.Declarative.F8Measure.DOpt.wkPrefix_leaves
#print axioms Rcic.Declarative.F8Measure.DOpt.conv
#print axioms Rcic.Declarative.F8Measure.DOpt.conv_leaves
#print axioms Rcic.Declarative.F8Measure.EvPar.readConv
#print axioms Rcic.Declarative.F8Measure.EvPar.readConv_leaves
#print axioms Rcic.Declarative.F8Measure.EvPar.readWk
#print axioms Rcic.Declarative.F8Measure.EvPar.readWk_leaves
#print axioms Rcic.Declarative.F8Measure.DStep.read
#print axioms Rcic.Declarative.F8Measure.DStep.read_leaves
#print axioms Rcic.Declarative.F8Measure.DOpt.toEvPar
#print axioms Rcic.Declarative.F8Measure.DOpt.toEvPar_leaves
#print axioms Rcic.Declarative.F8Measure.EvPar.requests
#print axioms Rcic.Declarative.F8Measure.EvPar.answers
#print axioms Rcic.Declarative.F8Measure.EvPar.toDTile
#print axioms Rcic.Declarative.F8Measure.DStep.toDTile
#print axioms Rcic.Declarative.F8Measure.dStep_edgeContract
#print axioms Rcic.Declarative.F8Measure.DeltaPayload.readConv
#print axioms Rcic.Declarative.F8Measure.DeltaPayload.readConv_leaves
#print axioms Rcic.Declarative.F8Measure.DeltaPayload.toDTile
#print axioms Rcic.Declarative.F8Measure.BVarZetaPayload.readConv
#print axioms Rcic.Declarative.F8Measure.BVarZetaPayload.readConv_leaves
#print axioms Rcic.Declarative.F8Measure.BVarZetaPayload.requests
#print axioms Rcic.Declarative.F8Measure.BVarZetaPayload.answers
#print axioms Rcic.Declarative.F8Measure.BVarZetaPayload.toDTile
#print axioms Rcic.Declarative.F8Measure.LamPayload.readConv
#print axioms Rcic.Declarative.F8Measure.LamPayload.readConv_leaves
#print axioms Rcic.Declarative.F8Measure.LamPayload.readWk
#print axioms Rcic.Declarative.F8Measure.LamPayload.readWk_leaves
#print axioms Rcic.Declarative.F8Measure.LamPayload.requests
#print axioms Rcic.Declarative.F8Measure.LamPayload.answers
#print axioms Rcic.Declarative.F8Measure.LamPayload.toDTile
#print axioms Rcic.Declarative.F8Measure.AppPayload.readConv
#print axioms Rcic.Declarative.F8Measure.AppPayload.readConv_leaves
#print axioms Rcic.Declarative.F8Measure.AppPayload.readWk
#print axioms Rcic.Declarative.F8Measure.AppPayload.readWk_leaves
#print axioms Rcic.Declarative.F8Measure.AppPayload.requests
#print axioms Rcic.Declarative.F8Measure.AppPayload.answers
#print axioms Rcic.Declarative.F8Measure.AppPayload.toDTile
#print axioms Rcic.Declarative.F8Measure.LetEPayload.readConv
#print axioms Rcic.Declarative.F8Measure.LetEPayload.readConv_leaves
#print axioms Rcic.Declarative.F8Measure.LetEPayload.readWk
#print axioms Rcic.Declarative.F8Measure.LetEPayload.readWk_leaves
#print axioms Rcic.Declarative.F8Measure.LetEPayload.requests
#print axioms Rcic.Declarative.F8Measure.LetEPayload.answers
#print axioms Rcic.Declarative.F8Measure.LetEPayload.toDTile
#print axioms Rcic.Declarative.F8Measure.Valley.ofSorts
#print axioms Rcic.Declarative.F8Measure.Valley.ofSorts_leaves
#print axioms Rcic.Declarative.F8Measure.Valley.ofConstsWith
#print axioms Rcic.Declarative.F8Measure.Valley.ofConstsWith_leaves
#print axioms Rcic.Declarative.F8Measure.proofIndexJoin
#print axioms Rcic.Declarative.F8Measure.proofIndexJoin_leaves
#print axioms Rcic.Declarative.F8Measure.proofIndexRightJoin
#print axioms Rcic.Declarative.F8Measure.cvCtxConvVar
#print axioms Rcic.Declarative.F8Measure.cvCtxConvVar_leaves
#print axioms Rcic.Declarative.F8Measure.tyCtxConvVar
#print axioms Rcic.Declarative.F8Measure.tyCtxConvVar_leaves
#print axioms Rcic.Declarative.F8Measure.EvPar.readEsub0
#print axioms Rcic.Declarative.F8Measure.EvPar.readEsub0_leaves
#print axioms Rcic.Declarative.F8Measure.evParCtxConvVar
#print axioms Rcic.Declarative.F8Measure.evParCtxConvVar_leaves
#print axioms Rcic.Declarative.F8Measure.reflLeftJoin
#print axioms Rcic.Declarative.F8Measure.reflRightJoin
#print axioms Rcic.Declarative.F8Measure.sortsTc
#print axioms Rcic.Declarative.F8Measure.sortsTc_leaves
#print axioms Rcic.Declarative.F8Measure.eqN_symm'
#print axioms Rcic.Declarative.F8Measure.eqN_trans'
#print axioms Rcic.Declarative.F8Measure.eqNList_symm'
#print axioms Rcic.Declarative.F8Measure.eqNList_trans'
#print axioms Rcic.Declarative.F8Measure.sortEqJoin
#print axioms Rcic.Declarative.F8Measure.sortEqJoin_leaves
#print axioms Rcic.Declarative.F8Measure.constsJoin
#print axioms Rcic.Declarative.F8Measure.constsJoin_leaves
#print axioms Rcic.Declarative.F8Measure.deltaJoin
#print axioms Rcic.Declarative.F8Measure.structPiJoin
#print axioms Rcic.Declarative.F8Measure.structPiJoin_sound
#print axioms Rcic.Declarative.F8Measure.evParDiamondWf
#print axioms Rcic.Declarative.F8Measure.dStepDiamondWf
#print axioms Rcic.Declarative.F8Measure.dProcWf
#print axioms Rcic.Declarative.F8Measure.dContractWf
#print axioms Rcic.Declarative.F8Measure.bvarZetaJoin
#print axioms Rcic.Declarative.F8Measure.lamForwardJoin
#print axioms Rcic.Declarative.F8Measure.lamForwardJoin_sound
#print axioms Rcic.Declarative.F8Measure.appForwardJoin
#print axioms Rcic.Declarative.F8Measure.appForwardJoin_sound
#print axioms Rcic.Declarative.F8Measure.letEForwardJoin
#print axioms Rcic.Declarative.F8Measure.letEForwardJoin_sound
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_proofIndex_rightTy
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinStarWk
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_spine_wk_leaves
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinJoinStep
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinJoinTile
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_proofIndexJoin_nonid
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinDomL
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinDomR
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_doms_ne
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinChainDom
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinBodyCv
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinMovedCv
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_cvCtxConvVar_leaves
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinTargetPi
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinPiRoot
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinStructPiPayload
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinStructPiJoin
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_structPiJoin_sound
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinStarLeft
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinStarRight
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinDiamondOut
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_dContractWf
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinSortEqL
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinSortEqR
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinSortEqJoin
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_sortEqJoin_leaves
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinValleySorts
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_valleySorts_leaves
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinSortEqDTile
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinSortEqInAssump
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinSortEqSubstVal
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinReflStep
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinReflJoin
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_reflJoin_leaves
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinMovedTy
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_tyCtxConvVar_leaves
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinBodyEvPar
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinMovedEvPar
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_evParCtxConvVar_leaves
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinDeltaMember
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinDeltaEnv
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinDeltaEnvWf
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinDeltaPayload
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinDeltaJoin
#print axioms Rcic.Declarative.F8Measure.DTilePins.pin_deltaJoin_leaves
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinDeltaSubstVal
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinDeltaTile
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinZetaCtx
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinZetaCtxWf
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinBVarZetaL
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinBVarZetaR
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinBVarZetaJoin
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinZetaAssumpCtx
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinBVarZetaInAssump
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinBVarZetaSubstVal
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinTargetLam
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinLamRootAssump
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinLamInAssump
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinLamSubstVal
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinAppDom
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinAppCod
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinAppFun
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinAppPiTy
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinAppFunTy
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinAppResTy
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinAppRoots
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinAppPayload
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinAppForwardJoin
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinAppSubstVal
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinTargetLetE
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinLetERoot
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinLetEPayload
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinLetEForwardJoin
#print axioms Rcic.Declarative.F8Measure.DTilePins.pinLetESubstVal
#print axioms Rcic.Declarative.F8Measure.StructPiJoinAt
#print axioms Rcic.Declarative.F8Measure.evParDiamondAt
#print axioms Rcic.Declarative.F8Measure.dStepDiamondAt
#print axioms Rcic.Declarative.F8Measure.structPiJoinAtWf
#print axioms Rcic.Declarative.F8Measure.StructPiJoinAt.join
#print axioms Rcic.Declarative.F8Measure.StructPiJoinAt.sound
