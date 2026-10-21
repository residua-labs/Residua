import rcic.RcicSynPack
import rcic.RcicSynBvarEpsEsub
import rcic.RcicSynBvarEpsLsub

/-!
`research/rcic/sortrow/S6_MIXED_TRANSPORT_STEPS.md` §2–§3: one-sided
exposure of an original `bvar` node under `esub`/`lsub`.

Three smaller calls replace the exposed node, each paid on the original
`DMStep`/`LexDM` with the occurrence lists kept verbatim (S6 §1: count by
occurrence, never deduplicate by value):

- **E-type** (`dmStep_expose_etype`): the original type-view `G` replaces
  the bvar atom — strict descent because `bvar.wt = 1 + G.wt`. The callee
  keeps the original `G`, `V`, `W` once each; it is NOT the materialized
  pair `tyPairMeas (esub … G …) W`, which would carry `W`'s atoms twice.
- **E-value** (`dmStep_expose_evalue`): the bvar atom is dropped; the
  actual `PBit σ ρ V W` is the callee's business, `V`/`W` are not copied.
- **E-main** (`dmStep_expose_emain`): the bvar atom and the no-longer-
  needed `W` atoms are both removed; the actual value `V` stays.

The §2.1 same-target identities — the ascribed type is the stored type
lifted, and its instantiation is the target's stored type — are
`expose_ascribed_assumption` / `expose_ascribed_letBinding` /
`expose_target_ty`. §2.3's composite — after the two gates are paid, the
exposed `esub`-bvar erases exactly to `V.eps` — is `eps_esub_bvar_eq`.
§3's `lsub` form uses the lsub `drop`/`inline` rule only
(`eps_lsub_bvar_drop`/`eps_lsub_bvar_proof`/`eps_lsub_bvar_inline`); no
`ETm.inst` object is substituted for it.

§4 is the spec's executable control row: `s6Γ`/`s6Sa`/`s6Sl`, the direct
sorts `s6G`/`s6V`/`s6W`, the six-node `conv ∘ refl` retype `s6W2`, the
entries `s6H`/`s6Hl`, the positive descents `s6_step_*`, and the
materialized-pair refutations `s6_dup_no_step`/`s6_dup_no_lex` (the
highest changed level `6` grows, and the secondary weight cannot rescue
a `LexDM` whose first component fails).

`closure_claim` stays `0`: the smaller `MixedCore`/`PBit` producers this
step *calls* remain the open residue; this module only pays the exposure
edges and their erasure identities.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the same-target identities (S6 §2.1) -/

/-- A let-binding's ascribed type under `lookupType` is the stored type
    lifted past the newer binders — the `letBinding` analogue of
    `lookupType_get_assumption`. -/
theorem lookupType_get_letBinding {Γ : LCtx} {j : Nat} {t v : Expr Nat}
    (h : Γ[j]? = some (.letBinding t v)) :
    lookupType Γ j = some (lift 0 (j + 1) t) := by
  simp [lookupType, h]

/-- The bvar's ascribed type under an `assumption` entry is the stored
    type lifted past the newer binders (`U = lift 0 (j+1) t`). -/
theorem expose_ascribed_assumption {Γ : LCtx} {j : Nat} {U t : Expr Nat}
    (hlook : lookupType Γ j = some U) (hget : Γ[j]? = some (.assumption t)) :
    U = lift 0 (j + 1) t := by
  rw [lookupType_get_assumption hget] at hlook
  exact (Option.some.inj hlook).symm

/-- The bvar's ascribed type under a `letBinding` entry, same identity. -/
theorem expose_ascribed_letBinding {Γ : LCtx} {j : Nat} {U t v : Expr Nat}
    (hlook : lookupType Γ j = some U) (hget : Γ[j]? = some (.letBinding t v)) :
    U = lift 0 (j + 1) t := by
  rw [lookupType_get_letBinding hget] at hlook
  exact (Option.some.inj hlook).symm

/-- Instantiating the ascribed type at `j` reproduces the target's stored
    type view (`instantiate j (lift 0 j v) U = lift 0 j t`). -/
theorem expose_target_ty {j : Nat} {U t v : Expr Nat}
    (hU : U = lift 0 (j + 1) t) :
    instantiate j (lift 0 j v) U = lift 0 j t := by
  subst hU
  simpa using instantiate_lift_cancel (j + 1) 0 j (lift 0 j v)
    (Nat.zero_le j) (by omega) t

/-- The exposed index itself instantiates to the lifted value — the
    subject side of the same target judgment. -/
theorem instantiate_bvar_self (j : Nat) (r : Expr Nat) :
    instantiate j r (.bvar j) = r := by
  unfold instantiate
  rw [if_pos rfl]

/-! ## §2 the three real subqueries, paid on the original atoms -/

/-- Generic occurrence edge: one atom `x` is replaced by strictly smaller
    atoms `Y`; `K` and `R` keep their positions. -/
theorem dmStep_expose {x : Nat} {Y : List Nat}
    (h : ∀ y ∈ Y, y < x) (K R : List Nat) :
    DMStep (K ++ Y ++ R) (K ++ [x] ++ R) := by
  obtain ⟨X, Y', Z, hX, hM, hN, hkey⟩ :=
    dmStep_of_below (x := x) (Y := Y) (Z := K ++ R) h
  have hp : (K ++ Y ++ R).Perm (Y ++ (K ++ R)) := by
    rw [← List.append_assoc]
    exact List.Perm.append_right R List.perm_append_comm
  have hm : (K ++ [x] ++ R).Perm (X ++ Z) := by
    rw [List.append_assoc, List.singleton_append]
    exact List.perm_middle.trans hM
  exact ⟨X, Y', Z, hX, hm, hp.trans hN, hkey⟩

/-- **E-type** (S6 §2.2): the source type-view `G` replaces the bvar
    atom. `R` is where the original `V`/`W` occurrences stay. -/
theorem dmStep_expose_etype (Aw : Nat → Nat) (K R : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {U : Expr Nat} {w : Level}
    {hlook : lookupType Γ i = some U} {G : TyP E n Γ U (.sort w)} :
    DMStep (K ++ G.atoms Aw ++ R)
      (K ++ (TyP.bvar E n Γ i U w hlook G).atoms Aw ++ R) := by
  have hb : (TyP.bvar E n Γ i U w hlook G).atoms Aw =
      [(TyP.bvar E n Γ i U w hlook G).wt Aw] := rfl
  rw [hb]
  exact dmStep_expose
    (fun y hy => atoms_lt_of_wt_lt Aw G (by simp only [TyP.wt]; omega) y hy) K R

/-- **E-value** (S6 §2.2): the bvar atom is dropped outright; `R` keeps
    the original `V`, `W` occurrences, each once. -/
theorem dmStep_expose_evalue (Aw : Nat → Nat) (K R : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {U : Expr Nat} {w : Level}
    {hlook : lookupType Γ i = some U} {G : TyP E n Γ U (.sort w)} :
    DMStep (K ++ R)
      (K ++ (TyP.bvar E n Γ i U w hlook G).atoms Aw ++ R) := by
  have hb : (TyP.bvar E n Γ i U w hlook G).atoms Aw =
      [(TyP.bvar E n Γ i U w hlook G).wt Aw] := rfl
  rw [hb]
  obtain ⟨X, Y, Z, hX, hM, hN, hkey⟩ :=
    dmStep_drop (X := [(TyP.bvar E n Γ i U w hlook G).wt Aw]) (Z := K ++ R)
      (List.cons_ne_nil _ _)
  have hm : (K ++ [(TyP.bvar E n Γ i U w hlook G).wt Aw] ++ R).Perm
      (X ++ Z) := by
    rw [List.append_assoc, List.singleton_append]
    exact List.perm_middle.trans hM
  exact ⟨X, Y, Z, hX, hm, hN, hkey⟩

/-- **E-main** (S6 §2.2): the bvar atom and the `W` atoms are both
    removed; the actual `V` occurrence stays. -/
theorem dmStep_expose_emain (Aw : Nat → Nat) (K : List Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {U : Expr Nat} {w : Level}
    {hlook : lookupType Γ i = some U} {G : TyP E n Γ U (.sort w)}
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e₁ T₁ e₂ T₂ : Expr Nat}
    (V : TyP E' n' Γ' e₁ T₁) (W : TyP E' n' Γ' e₂ T₂) :
    DMStep (K ++ V.atoms Aw)
      (K ++ (TyP.bvar E n Γ i U w hlook G).atoms Aw ++
        V.atoms Aw ++ W.atoms Aw) := by
  have hb : (TyP.bvar E n Γ i U w hlook G).atoms Aw =
      [(TyP.bvar E n Γ i U w hlook G).wt Aw] := rfl
  rw [hb]
  have hp : (K ++ [(TyP.bvar E n Γ i U w hlook G).wt Aw] ++ V.atoms Aw ++
        W.atoms Aw).Perm
      (([(TyP.bvar E n Γ i U w hlook G).wt Aw] ++ W.atoms Aw) ++
        (K ++ V.atoms Aw)) := by
    rw [List.append_assoc, List.append_assoc, List.singleton_append]
    refine List.perm_middle.trans (List.Perm.cons _ ?_)
    rw [← List.append_assoc]
    exact List.perm_append_comm
  refine ⟨[(TyP.bvar E n Γ i U w hlook G).wt Aw] ++ W.atoms Aw, [],
    K ++ V.atoms Aw, List.cons_ne_nil _ _, hp, List.Perm.refl _,
    fun y hy => absurd hy (List.not_mem_nil _)⟩

/-! ## §3 the erasure identities (S6 §2.3, §3) -/

/-- The original `esub`-bvar erases to `★` once the substituted type's
    sort bit is `true` — the first gate of §2.3's composite. -/
theorem eps_esub_bvar_sort_true
    {E : ResolvedEnv} {n : Nat} {Src : LCtx} {j : Nat}
    {U t v : Expr Nat} {w s : Level}
    {hlook : lookupType Src j = some U} {G : TyP E n Src U (.sort w)}
    (hget : Src[j]? = some (.assumption t))
    {V : TyP E n (substRemove v j Src) (lift 0 j v) (lift 0 j t)}
    {W : TyP E n (substRemove v j Src) (lift 0 j t) (.sort s)}
    {σ : Level → Level} {ρ : List Disp}
    (hs : levelIsZero (σ s) = true) (hρ : j ≤ ρ.length) :
    (TyP.esub E n Src (.bvar j) U t v j s
      (TyP.bvar E n Src j U w hlook G) hget V W).eps σ ρ = .star := by
  rw [eps_esub_drop hs]
  cases hw : levelIsZero (σ w) with
  | true => exact eps_bvar_proof hw
  | false => rw [eps_bvar_rel hw]; exact resolve_insertDisp_drop j ρ hρ

/-- **E-type + E-value suffice** (S6 §2.3): with the two sort bits
    aligned (`bw = bs`) and the actual `PBit σ ρ V W`, the exposed
    `esub`-bvar erases exactly to `V.eps`. -/
theorem eps_esub_bvar_eq
    {E : ResolvedEnv} {n : Nat} {Src : LCtx} {j : Nat}
    {U t v : Expr Nat} {w s : Level}
    {hlook : lookupType Src j = some U} {G : TyP E n Src U (.sort w)}
    (hget : Src[j]? = some (.assumption t))
    {V : TyP E n (substRemove v j Src) (lift 0 j v) (lift 0 j t)}
    {W : TyP E n (substRemove v j Src) (lift 0 j t) (.sort s)}
    {σ : Level → Level} {ρ : List Disp}
    (hρ : j ≤ ρ.length)
    (hbits : levelIsZero (σ w) = levelIsZero (σ s))
    (hbit : PBit σ ρ V W) :
    (TyP.esub E n Src (.bvar j) U t v j s
      (TyP.bvar E n Src j U w hlook G) hget V W).eps σ ρ = V.eps σ ρ := by
  cases hs : levelIsZero (σ s) with
  | true =>
    rw [eps_esub_bvar_sort_true hget hs hρ]
    exact (hbit.mpr hs).symm
  | false =>
    rw [eps_esub_keep hs]
    have hw : levelIsZero (σ w) = false := by rw [hbits]; exact hs
    rw [eps_bvar_rel hw, resolve_insertDisp_keep j ρ hρ, inst_bvar_hit]

/-- §3's `lsub` gate when the value erases to `★`: the disposition is
    `drop` and the exposed bvar erases to `★` — the lsub rule, not an
    `esub`-style `ETm.inst`. -/
theorem eps_lsub_bvar_drop
    {E : ResolvedEnv} {n : Nat} {Src : LCtx} {j : Nat}
    {U t v : Expr Nat} {w s : Level}
    {hlook : lookupType Src j = some U} {G : TyP E n Src U (.sort w)}
    (hget : Src[j]? = some (.letBinding t v))
    {V : TyP E n (substRemove v j Src) (lift 0 j v) (lift 0 j t)}
    {W : TyP E n (substRemove v j Src) (lift 0 j t) (.sort s)}
    {σ : Level → Level} {ρ : List Disp}
    (hve : V.eps σ ρ = .star) (hρ : j ≤ ρ.length) :
    (TyP.lsub E n Src (.bvar j) U t v j s
      (TyP.bvar E n Src j U w hlook G) hget V W).eps σ ρ = .star := by
  rw [eps_lsub, hve]
  cases hw : levelIsZero (σ w) with
  | true => exact eps_bvar_proof hw
  | false => rw [eps_bvar_rel hw]; exact resolve_insertDisp_drop j ρ hρ

/-- §3's `lsub` gate when the source type-view bit is `true`: the
    inlined bvar erases to `★` even though `V.eps` is not `★`. -/
theorem eps_lsub_bvar_proof
    {E : ResolvedEnv} {n : Nat} {Src : LCtx} {j : Nat}
    {U t v : Expr Nat} {w s : Level}
    {hlook : lookupType Src j = some U} {G : TyP E n Src U (.sort w)}
    (hget : Src[j]? = some (.letBinding t v))
    {V : TyP E n (substRemove v j Src) (lift 0 j v) (lift 0 j t)}
    {W : TyP E n (substRemove v j Src) (lift 0 j t) (.sort s)}
    {σ : Level → Level} {ρ : List Disp}
    (hne : V.eps σ ρ ≠ .star) (hw : levelIsZero (σ w) = true) :
    (TyP.lsub E n Src (.bvar j) U t v j s
      (TyP.bvar E n Src j U w hlook G) hget V W).eps σ ρ = .star := by
  rw [eps_lsub_ne_star hne, eps_bvar_proof hw]

/-- §3's `lsub` composite in the relevant case: the value's erasure is
    inlined at the bvar's hole as the `localize`d payload, lifted over
    the kept prefix — `restore κ (V.eps σ ρ)` in expanded form. -/
theorem eps_lsub_bvar_inline
    {E : ResolvedEnv} {n : Nat} {Src : LCtx} {j : Nat}
    {U t v : Expr Nat} {w s : Level}
    {hlook : lookupType Src j = some U} {G : TyP E n Src U (.sort w)}
    (hget : Src[j]? = some (.letBinding t v))
    {V : TyP E n (substRemove v j Src) (lift 0 j v) (lift 0 j t)}
    {W : TyP E n (substRemove v j Src) (lift 0 j t) (.sort s)}
    {σ : Level → Level} {ρ : List Disp}
    (hne : V.eps σ ρ ≠ .star) (hw : levelIsZero (σ w) = false)
    (hρ : j ≤ ρ.length) :
    (TyP.lsub E n Src (.bvar j) U t v j s
      (TyP.bvar E n Src j U w hlook G) hget V W).eps σ ρ =
      (localize (countKeep (ρ.take j)) (V.eps σ ρ)).lift 0
        (countKeep (ρ.take j)) := by
  rw [eps_lsub_ne_star hne, eps_bvar_rel hw,
    resolve_insertDisp_inline j _ ρ hρ]

/-- Under an `AvoidPrefix` scope certificate the localized payload is
    lossless and the lsub composite is the value's erasure itself — the
    spec's `Hlet.eps = eV` shorthand. -/
theorem eps_lsub_bvar_eq
    {E : ResolvedEnv} {n : Nat} {Src : LCtx} {j : Nat}
    {U t v : Expr Nat} {w s : Level}
    {hlook : lookupType Src j = some U} {G : TyP E n Src U (.sort w)}
    (hget : Src[j]? = some (.letBinding t v))
    {V : TyP E n (substRemove v j Src) (lift 0 j v) (lift 0 j t)}
    {W : TyP E n (substRemove v j Src) (lift 0 j t) (.sort s)}
    {σ : Level → Level} {ρ : List Disp}
    (hne : V.eps σ ρ ≠ .star) (hw : levelIsZero (σ w) = false)
    (hρ : j ≤ ρ.length)
    (hcert : AvoidPrefix (countKeep (ρ.take j)) 0 (V.eps σ ρ)) :
    (TyP.lsub E n Src (.bvar j) U t v j s
      (TyP.bvar E n Src j U w hlook G) hget V W).eps σ ρ = V.eps σ ρ := by
  rw [eps_lsub_bvar_inline hget hne hw hρ]
  exact restore_eq _ _ hcert

/-! ## §4 the executable controls (S6 §3's six-node row) -/

/-- target context `[z : s₀]`. -/
def s6Γ : LCtx := [.assumption (.sort .zero)]

/-- source context with the assumption exposed: `[x : s₁, z : s₀]`. -/
def s6Sa : LCtx := .assumption (.sort (.succ .zero)) :: s6Γ

/-- source context with the let exposed: `[let x : s₁ := s₀, z : s₀]`. -/
def s6Sl : LCtx := .letBinding (.sort (.succ .zero)) (.sort .zero) :: s6Γ

/-- the left provider: `s₀ : s₁` in the empty context. -/
def s6Left (E : ResolvedEnv) (n : Nat) :
    TyP E n [] (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort E n [] .zero (.succ .zero) (eqN_refl _)

/-- the source type-view: `s₁ : s₂` in `s6Sa`. -/
def s6G (E : ResolvedEnv) (n : Nat) :
    TyP E n s6Sa (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort E n s6Sa (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

theorem s6look : lookupType s6Sa 0 = some (.sort (.succ .zero)) := rfl

theorem s6getA : s6Sa[0]? = some (.assumption (.sort (.succ .zero))) := rfl

/-- the exposed bvar node itself: `x : s₁` in `s6Sa`, weight `2`. -/
def s6D (E : ResolvedEnv) (n : Nat) :
    TyP E n s6Sa (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar E n s6Sa 0 (.sort (.succ .zero)) (.succ (.succ .zero))
    s6look (s6G E n)

/-- the actual value: `s₀ : s₁` in `s6Γ`, weight `1`. -/
def s6V (E : ResolvedEnv) (n : Nat) :
    TyP E n s6Γ (.sort .zero) (.sort (.succ .zero)) :=
  TyP.sort E n s6Γ .zero (.succ .zero) (eqN_refl _)

/-- the value's type view: `s₁ : s₂` in `s6Γ`, weight `1`. -/
def s6W (E : ResolvedEnv) (n : Nat) :
    TyP E n s6Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort E n s6Γ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- `s₂ : s₃` in `s6Γ` — a field of the negative control's `refl`. -/
def s6S3 (E : ResolvedEnv) (n : Nat) :
    TyP E n s6Γ (.sort (.succ (.succ .zero)))
      (.sort (.succ (.succ (.succ .zero)))) :=
  TyP.sort E n s6Γ (.succ (.succ .zero)) (.succ (.succ (.succ .zero)))
    (eqN_refl _)

/-- the six-node retype of the same judgment `s₁ : s₂`: a `conv` node over
    `s6W` whose conversion is a `refl` of three `s₂ : s₃` typings —
    `wt = 1 + 1 + (1 + 3) = 6`. -/
def s6W2 (E : ResolvedEnv) (n : Nat) :
    TyP E n s6Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.conv E n s6Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
    (.sort (.succ (.succ .zero))) (.succ (.succ (.succ .zero))) (s6W E n)
    (CvP.refl E n s6Γ (.sort (.succ (.succ .zero)))
      (.sort (.succ (.succ (.succ .zero)))) (s6S3 E n) (s6S3 E n) (s6S3 E n))

/-- the assumption-side entry: the `esub` of the bvar over `s₀`. -/
def s6H (E : ResolvedEnv) (n : Nat) :
    TyP E n s6Γ (.sort .zero) (.sort (.succ .zero)) :=
  TyP.esub E n s6Sa (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort .zero) 0 (.succ (.succ .zero)) (s6D E n) s6getA
    (s6V E n) (s6W E n)

theorem s6lookL : lookupType s6Sl 0 = some (.sort (.succ .zero)) := rfl

theorem s6getL : s6Sl[0]? =
    some (.letBinding (.sort (.succ .zero)) (.sort .zero)) := rfl

/-- `s₁ : s₂` inside the let source — the bvar's `G` there. -/
def s6Gl (E : ResolvedEnv) (n : Nat) :
    TyP E n s6Sl (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  TyP.sort E n s6Sl (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- the exposed bvar inside the let source. -/
def s6Dl (E : ResolvedEnv) (n : Nat) :
    TyP E n s6Sl (.bvar 0) (.sort (.succ .zero)) :=
  TyP.bvar E n s6Sl 0 (.sort (.succ .zero)) (.succ (.succ .zero))
    s6lookL (s6Gl E n)

/-- the let-side entry: the `lsub` of the bvar over the bound `s₀`. -/
def s6Hl (E : ResolvedEnv) (n : Nat) :
    TyP E n s6Γ (.sort .zero) (.sort (.succ .zero)) :=
  TyP.lsub E n s6Sl (.bvar 0) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.sort .zero) 0 (.succ (.succ .zero)) (s6Dl E n) s6getL
    (s6V E n) (s6W E n)

theorem s6D_wt (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (s6D E n).wt Aw = 2 := rfl

theorem s6W2_wt (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (s6W2 E n).wt Aw = 6 := rfl

theorem s6H_atoms (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (s6H E n).atoms Aw = [2, 1, 1] := rfl

theorem s6Hl_atoms (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    (s6Hl E n).atoms Aw = [2, 1, 1] := rfl

/-- positive row 1: the entry's E-type step with the plain `W` —
    `[1,2,1,1] → [1,1,1,1]` on the original atoms. -/
theorem s6_step_etype_plain (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    DMStep ([(s6Left E n).wt Aw] ++ (s6G E n).atoms Aw ++
        (s6V E n).atoms Aw ++ (s6W E n).atoms Aw)
      ([(s6Left E n).wt Aw] ++ (s6D E n).atoms Aw ++
        (s6V E n).atoms Aw ++ (s6W E n).atoms Aw) :=
  dmStep_expose_etype Aw [(s6Left E n).wt Aw]
    ((s6V E n).atoms Aw ++ (s6W E n).atoms Aw)
    (hlook := s6look) (G := s6G E n)

/-- positive row 2: the same step still descends with the six-node `W`
    kept — `[1,2,1,6] → [1,1,1,6]`. -/
theorem s6_step_etype_heavy (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    DMStep ([(s6Left E n).wt Aw] ++ (s6G E n).atoms Aw ++
        (s6V E n).atoms Aw ++ (s6W2 E n).atoms Aw)
      ([(s6Left E n).wt Aw] ++ (s6D E n).atoms Aw ++
        (s6V E n).atoms Aw ++ (s6W2 E n).atoms Aw) :=
  dmStep_expose_etype Aw [(s6Left E n).wt Aw]
    ((s6V E n).atoms Aw ++ (s6W2 E n).atoms Aw)
    (hlook := s6look) (G := s6G E n)

/-- the E-value step on the fixture: drop the bvar atom, keep `V`, `W2`. -/
theorem s6_step_evalue_heavy (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    DMStep ([(s6Left E n).wt Aw] ++
        (s6V E n).atoms Aw ++ (s6W2 E n).atoms Aw)
      ([(s6Left E n).wt Aw] ++ (s6D E n).atoms Aw ++
        (s6V E n).atoms Aw ++ (s6W2 E n).atoms Aw) :=
  dmStep_expose_evalue Aw [(s6Left E n).wt Aw]
    ((s6V E n).atoms Aw ++ (s6W2 E n).atoms Aw)
    (hlook := s6look) (G := s6G E n)

/-- the E-main step on the fixture: drop the bvar and `W2`, keep `V`. -/
theorem s6_step_emain_heavy (Aw : Nat → Nat) (E : ResolvedEnv) (n : Nat) :
    DMStep ([(s6Left E n).wt Aw] ++ (s6V E n).atoms Aw)
      ([(s6Left E n).wt Aw] ++ (s6D E n).atoms Aw ++
        (s6V E n).atoms Aw ++ (s6W2 E n).atoms Aw) :=
  dmStep_expose_emain Aw [(s6Left E n).wt Aw] (s6V E n) (s6W2 E n)
    (hlook := s6look) (G := s6G E n)

/-- negative row: the materialized pair's atom list duplicates `W2`,
    giving `[1,1,1,6,6]` — it cannot descend to `[1,2,1,6]` because the
    only changed level is `6`, and it grows. -/
theorem s6_dup_no_step : ¬ DMStep [1, 1, 1, 6, 6] [1, 2, 1, 6] := by
  rintro ⟨X, Y, Z, hX, hM, hN, hlt⟩
  have cM : ([1, 2, 1, 6] : List Nat).count 6 = 1 := rfl
  have cN : ([1, 1, 1, 6, 6] : List Nat).count 6 = 2 := rfl
  have h6M : X.count 6 + Z.count 6 = 1 := by
    rw [← List.count_append, ← hM.count_eq 6]; exact cM
  have h6N : Y.count 6 + Z.count 6 = 2 := by
    rw [← List.count_append, ← hN.count_eq 6]; exact cN
  obtain ⟨x, hxX, hxlt⟩ := hlt 6 (List.count_pos_iff.mp (by omega))
  have hxM : x ∈ ([1, 2, 1, 6] : List Nat) :=
    hM.symm.subset (List.mem_append_left Z hxX)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxM
  rcases hxM with rfl | rfl | rfl | rfl <;> omega

/-- no secondary weight rescues the materialized pair: a `LexDM` would
    need either the refuted `DMStep` or equal first components with a
    smaller total weight (`15 < 10` fails anyway). -/
theorem s6_dup_no_lex :
    ¬ LexDM (([1, 1, 1, 6, 6] : List Nat), 15)
      (([1, 2, 1, 6] : List Nat), 10) := by
  intro h
  cases h <;> first | exact s6_dup_no_step ‹_› | omega

/-- the fixture's value erasure is `s₀` — the `esub` never sees `★`. -/
theorem s6_epsV (E : ResolvedEnv) (n : Nat) :
    (s6V E n).eps id [.keep, .drop] = .sort .zero := rfl

/-- the fixture satisfies the E-type gate under `id`: the `W` bit is
    `false` and the `V` erasure is not `★` — both directions vacuous. -/
theorem s6_pbit (E : ResolvedEnv) (n : Nat) :
    PBit id [.keep, .drop] (s6V E n) (s6W E n) :=
  ⟨fun h => by rw [s6_epsV] at h; exact absurd h (by decide),
   fun h => absurd h (by decide)⟩

/-- the general `esub` identity instantiated at the fixture: the exposed
    bvar erases exactly to the value's erasure. -/
theorem s6_eps_expose (E : ResolvedEnv) (n : Nat) :
    (s6H E n).eps id [.keep, .drop] = (s6V E n).eps id [.keep, .drop] :=
  eps_esub_bvar_eq (v := .sort .zero) (hlook := s6look) (G := s6G E n) s6getA
    (V := s6V E n) (W := s6W E n) (Nat.zero_le _) rfl (s6_pbit E n)

/-- the lsub entry erases through its own `inline` rule to the same value
    erasure. -/
theorem s6_eps_lsub (E : ResolvedEnv) (n : Nat) :
    (s6Hl E n).eps id [.keep, .drop] = .sort .zero := rfl

end Rcic.Syn

#print axioms Rcic.Syn.dmStep_expose_etype
#print axioms Rcic.Syn.eps_esub_bvar_eq
#print axioms Rcic.Syn.eps_lsub_bvar_inline
#print axioms Rcic.Syn.eps_lsub_bvar_eq
#print axioms Rcic.Syn.s6_dup_no_step
#print axioms Rcic.Syn.s6_eps_expose
