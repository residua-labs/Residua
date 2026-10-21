import rcic.RcicF8XStruct
import rcic.RcicF8EvParStar

/-!
# `RcicF8XFlat` — flattening and segmentation for the X tile's Stratum B (S3a)

S0 §1.2–1.3 (#7026) and `S3_X_VALLEY_DESIGN.md`. A provenance chain is flattened into a list
of **links**: an `ofCv` node (the lazy conversion inside is left whole — the plain literal's
own `trans`/`symm` are J's business, cc Q3), a `piCod` node, a `subst0`/`substLet` node
(kept opaque: pushing a substitution needs the `hvT` that `EvTc.subst0` does not carry,
S0 §1.1), or a weakening of a link. Flattening pushes `symm` to the links and `wk` over
them, splits `EvTc.trans`, `TyConvT.trans` (through `certOfChild`) and `EvCv.trans` at a sort,
and drops `refl`. It never duplicates a leaf, and every flattened leaf is `SubEq` a leaf of the
input (`flattenTc_leaves`).

`splitPi` cuts the shortest nonempty prefix that ends at a Π-shaped type. By construction a
prefix of length ≥ 2 has no Π→Π link: a link ending at a Π ends the prefix, and a link starting
at a Π would have ended it one step earlier. So Stratum B's valley route (S3b) is only ever run
on links with a non-Π endpoint, and a length-1 prefix is a Π→Π link for Stratum A. The
admissibility of a prefix for the valley route is the Bool `bPrefix`: every link is an `ofCv`
node whose conversion has no `esub` and weakens only at cutoff 0 (`bCv`), or a cutoff-0
weakening of one. Two named walls make `bPrefix` false, nothing is papered over: a
`subst0`/`substLet` link or an `esub` node (W-X-SUBST, S0 §5.6), and a weakening at cutoff
`k > 0` (W-X-WK: J runs in a well-formed context — cc's ruling of 2026-10-14 on #7035 — and
`CtxWfT (insertAt d (k+1) Γ₀)` does not yield `CtxWfT Γ₀` without a strengthening lemma, which
the tree lacks; at cutoff 0 the tail of `CtxWfT (d :: Γ₀)` is `CtxWfT Γ₀`). `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)}

/-! ### links -/

/-- a lazy conversion the valley route can read in a well-formed context: `lit` → J, `refl` →
    trivial, `symm`/`trans`/`tyConv` → `Valley` operations (the index chain of `tyConv` is used
    whole), `wk` at cutoff 0 → the tail context; no `esub` (W-X-SUBST), no weakening at cutoff
    `k > 0` (W-X-WK). -/
def bCv : {Γ : LCtx} → {a b T : Expr Nat} → EvCv R Γ a b T → Bool
  | _, _, _, _, .lit _ _ => true
  | _, _, _, _, .refl _ => true
  | _, _, _, _, .symm c => bCv c
  | _, _, _, _, .trans c₁ c₂ => bCv c₁ && bCv c₂
  | _, _, _, _, .tyConv _ c _ => bCv c
  | _, _, _, _, .rety c _ => bCv c
  | _, _, _, _, .wk _ k c =>
      match k with
      | 0 => bCv c
      | _ + 1 => false
  | _, _, _, _, .esub .. => false
  | _, _, _, _, .subst0 .. => false
  | _, _, _, _, .substLet .. => false
  | _, _, _, _, .sorts .. => false
  | _, _, _, _, .consts .. => false

/-- a flat link. -/
def isLink : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → Bool
  | _, _, _, .ofCv _ _ => true
  | _, _, _, .piCod .. => true
  | _, _, _, .subst0 .. => true
  | _, _, _, .substLet .. => true
  | _, _, _, .wk _ _ l => isLink l
  | _, _, _, .lit .. => false
  | _, _, _, .refl .. => false
  | _, _, _, .symm .. => false
  | _, _, _, .trans .. => false

/-- a link the valley route accepts: an `ofCv` node with a `bCv` conversion, or a cutoff-0
    weakening of one. -/
def bLink : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → Bool
  | _, _, _, .ofCv _ c => bCv c
  | _, _, _, .wk _ k l =>
      match k with
      | 0 => bLink l
      | _ + 1 => false
  | _, _, _, .piCod .. => false
  | _, _, _, .subst0 .. => false
  | _, _, _, .substLet .. => false
  | _, _, _, .lit .. => false
  | _, _, _, .refl .. => false
  | _, _, _, .symm .. => false
  | _, _, _, .trans .. => false

/-- the symmetric link: `symm` pushed into the node. -/
def linkSymm : {Γ : LCtx} → {A B : Expr Nat} → (l : EvTc R Γ A B) → isLink l = true →
    EvTc R Γ B A
  | _, _, _, .ofCv u c, _ => .ofCv u (.symm c)
  | _, _, _, .piCod u hA c, _ => .piCod u hA (.symm c)
  | _, _, _, .subst0 j c hget hv, _ => .subst0 j (.symm c) hget hv
  | _, _, _, .substLet j c hget hv, _ => .substLet j (.symm c) hget hv
  | _, _, _, .wk d k l, hl => .wk d k (linkSymm l (by simpa only [isLink] using hl))
  | _, _, _, .lit .., hl => nomatch hl
  | _, _, _, .refl .., hl => nomatch hl
  | _, _, _, .symm .., hl => nomatch hl
  | _, _, _, .trans .., hl => nomatch hl

theorem linkSymm_isLink : {Γ : LCtx} → {A B : Expr Nat} → (l : EvTc R Γ A B) →
    (hl : isLink l = true) → isLink (linkSymm l hl) = true
  | _, _, _, .ofCv _ _, _ => rfl
  | _, _, _, .piCod .., _ => rfl
  | _, _, _, .subst0 .., _ => rfl
  | _, _, _, .substLet .., _ => rfl
  | _, _, _, .wk d k l, hl => by
      simp only [linkSymm, isLink]
      exact linkSymm_isLink l (by simpa only [isLink] using hl)
  | _, _, _, .lit .., hl => nomatch hl
  | _, _, _, .refl .., hl => nomatch hl
  | _, _, _, .symm .., hl => nomatch hl
  | _, _, _, .trans .., hl => nomatch hl

theorem linkSymm_leaves : {Γ : LCtx} → {A B : Expr Nat} → (l : EvTc R Γ A B) →
    (hl : isLink l = true) → (linkSymm l hl).leaves = l.leaves
  | _, _, _, .ofCv _ _, _ => rfl
  | _, _, _, .piCod .., _ => rfl
  | _, _, _, .subst0 .., _ => rfl
  | _, _, _, .substLet .., _ => rfl
  | _, _, _, .wk d k l, hl => by
      simp only [linkSymm, EvTc.leaves]
      exact linkSymm_leaves l (by simpa only [isLink] using hl)
  | _, _, _, .lit .., hl => nomatch hl
  | _, _, _, .refl .., hl => nomatch hl
  | _, _, _, .symm .., hl => nomatch hl
  | _, _, _, .trans .., hl => nomatch hl

theorem linkSymm_bLink : {Γ : LCtx} → {A B : Expr Nat} → (l : EvTc R Γ A B) →
    (hl : isLink l = true) → bLink (linkSymm l hl) = bLink l
  | _, _, _, .ofCv _ _, _ => rfl
  | _, _, _, .piCod .., _ => rfl
  | _, _, _, .subst0 .., _ => rfl
  | _, _, _, .substLet .., _ => rfl
  | _, _, _, .wk d k l, hl => by
      cases k with
      | zero =>
          simp only [linkSymm, bLink]
          exact linkSymm_bLink l (by simpa only [isLink] using hl)
      | succ k => simp only [linkSymm, bLink]
  | _, _, _, .lit .., hl => nomatch hl
  | _, _, _, .refl .., hl => nomatch hl
  | _, _, _, .symm .., hl => nomatch hl
  | _, _, _, .trans .., hl => nomatch hl

/-! ### flat chains -/

/-- a flat chain: a list of links with matching endpoints. -/
inductive Flat (R : List (Jd E n)) (Γ : LCtx) : Expr Nat → Expr Nat → Type where
  | nil (A : Expr Nat) : Flat R Γ A A
  | cons {A M B : Expr Nat} (l : EvTc R Γ A M) (hl : isLink l = true) (rest : Flat R Γ M B) :
      Flat R Γ A B

variable {Γ : LCtx}

def Flat.leaves : {A B : Expr Nat} → Flat R Γ A B → List (Jd E n)
  | _, _, .nil _ => []
  | _, _, .cons l _ rest => l.leaves ++ rest.leaves

def Flat.length : {A B : Expr Nat} → Flat R Γ A B → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ _ rest => rest.length + 1

def Flat.append : {A M B : Expr Nat} → Flat R Γ A M → Flat R Γ M B → Flat R Γ A B
  | _, _, _, .nil _, g => g
  | _, _, _, .cons l hl rest, g => .cons l hl (rest.append g)

theorem Flat.append_leaves : {A M B : Expr Nat} → (f : Flat R Γ A M) → (g : Flat R Γ M B) →
    (f.append g).leaves = f.leaves ++ g.leaves
  | _, _, _, .nil _, g => by simp only [Flat.append, Flat.leaves, List.nil_append]
  | _, _, _, .cons l hl rest, g => by
      simp only [Flat.append, Flat.leaves, rest.append_leaves g, List.append_assoc]

theorem Flat.append_length : {A M B : Expr Nat} → (f : Flat R Γ A M) → (g : Flat R Γ M B) →
    (f.append g).length = f.length + g.length
  | _, _, _, .nil _, g => by simp only [Flat.append, Flat.length, Nat.zero_add]
  | _, _, _, .cons l hl rest, g => by
      simp only [Flat.append, Flat.length, rest.append_length g]
      omega

/-- reversal with every link turned around. -/
def Flat.symm : {A B : Expr Nat} → Flat R Γ A B → Flat R Γ B A
  | _, _, .nil A => .nil A
  | _, _, .cons l hl rest => rest.symm.append (.cons (linkSymm l hl) (linkSymm_isLink l hl) (.nil _))

theorem Flat.symm_leaves_mem : {A B : Expr Nat} → (f : Flat R Γ A B) →
    ∀ ℓ ∈ f.symm.leaves, ℓ ∈ f.leaves
  | _, _, .nil _ => fun _ h => h
  | _, _, .cons l hl rest => fun ℓ hℓ => by
      simp only [Flat.symm, Flat.append_leaves, Flat.leaves, linkSymm_leaves,
        List.append_nil, List.mem_append] at hℓ
      simp only [Flat.leaves, List.mem_append]
      rcases hℓ with hℓ | hℓ
      · exact .inr (rest.symm_leaves_mem ℓ hℓ)
      · exact .inl hℓ

theorem Flat.symm_length : {A B : Expr Nat} → (f : Flat R Γ A B) → f.symm.length = f.length
  | _, _, .nil _ => rfl
  | _, _, .cons l hl rest => by
      simp only [Flat.symm, Flat.append_length, Flat.length, rest.symm_length]

/-- weakening every link. -/
def Flat.wk (d : LocalDecl) (k : Nat) : {A B : Expr Nat} → Flat R Γ A B →
    Flat R (insertAt d k Γ) (lift k 1 A) (lift k 1 B)
  | _, _, .nil A => .nil _
  | _, _, .cons l hl rest => .cons (.wk d k l) (by simpa only [isLink] using hl) (rest.wk d k)

theorem Flat.wk_leaves (d : LocalDecl) (k : Nat) : {A B : Expr Nat} → (f : Flat R Γ A B) →
    (f.wk d k).leaves = f.leaves
  | _, _, .nil _ => rfl
  | _, _, .cons l hl rest => by
      simp only [Flat.wk, Flat.leaves, EvTc.leaves, rest.wk_leaves d k]

theorem Flat.wk_length (d : LocalDecl) (k : Nat) : {A B : Expr Nat} → (f : Flat R Γ A B) →
    (f.wk d k).length = f.length
  | _, _, .nil _ => rfl
  | _, _, .cons l hl rest => by simp only [Flat.wk, Flat.length, rest.wk_length d k]

/-! ### flattening -/

/-- index cast for provenance conversions (leaves computed through it). -/
def EvCv.castIdx {Γ : LCtx} {a b T T' : Expr Nat} (h : T = T') (c : EvCv R Γ a b T) :
    EvCv R Γ a b T' := by subst h; exact c

theorem EvCv.castIdx_leaves {Γ : LCtx} {a b T T' : Expr Nat} (h : T = T') (c : EvCv R Γ a b T) :
    (EvCv.castIdx h c).leaves = c.leaves := by subst h; rfl

/-- a provenance conversion whose index is a sort: split `trans`, push `symm`, drop `refl`,
    otherwise one `ofCv` link. -/
def flattenCv (u : Level) : {Γ : LCtx} → {a b T : Expr Nat} → (c : EvCv R Γ a b T) →
    T = .sort u → Flat R Γ a b
  | _, _, _, _, .trans c₁ c₂, hT => (flattenCv u c₁ hT).append (flattenCv u c₂ hT)
  | _, _, _, _, .symm c, hT => (flattenCv u c hT).symm
  | _, _, _, _, .refl _, _ => .nil _
  | _, _, _, _, .lit h hsub, hT => .cons (.ofCv u (EvCv.castIdx hT (.lit h hsub))) rfl (.nil _)
  | _, _, _, _, .tyConv u' c cA, hT =>
      .cons (.ofCv u (EvCv.castIdx hT (.tyConv u' c cA))) rfl (.nil _)
  | _, _, _, _, .wk d k c, hT => .cons (.ofCv u (EvCv.castIdx hT (.wk d k c))) rfl (.nil _)
  | _, _, _, _, .esub j u' c hget hv hvT, hT =>
      .cons (.ofCv u (EvCv.castIdx hT (.esub j u' c hget hv hvT))) rfl (.nil _)
  | _, _, _, _, .subst0 j c hget hv, hT =>
      .cons (.ofCv u (EvCv.castIdx hT (.subst0 j c hget hv))) rfl (.nil _)
  | _, _, _, _, .substLet j c hget hv, hT =>
      .cons (.ofCv u (EvCv.castIdx hT (.substLet j c hget hv))) rfl (.nil _)
  | _, _, _, _, .sorts l₁ l₂ h, hT =>
      .cons (.ofCv u (EvCv.castIdx hT (.sorts l₁ l₂ h))) rfl (.nil _)
  | _, _, _, _, .consts r ls ls' m hres hlen hwf hwf' heq, hT =>
      .cons (.ofCv u (EvCv.castIdx hT (.consts r ls ls' m hres hlen hwf hwf' heq))) rfl (.nil _)
  | _, _, _, _, .rety c cA, hT =>
      .cons (.ofCv u (EvCv.castIdx hT (.rety c cA))) rfl (.nil _)

/-- a plain type-conversion chain: split `trans` through `certOfChild`, drop `refl`. -/
def flattenT : {Γ : LCtx} → {A B : Expr Nat} → (d : TyConvT E n Γ A B) →
    (∃ r ∈ R, SubEq (.tc d) r) → Flat R Γ A B
  | _, _, _, .refl _ _, _ => .nil _
  | _, _, _, .of _ _ _ u h, hsub =>
      .cons (.ofCv u (.lit h (certOfChild (tcChildOf h) hsub))) rfl (.nil _)
  | _, _, _, .trans _ _ _ _ d₁ d₂, hsub =>
      (flattenT d₁ (certOfChild (tcChildFst d₁ d₂) hsub)).append
        (flattenT d₂ (certOfChild (tcChildSnd d₁ d₂) hsub))

/-- a provenance chain. -/
def flattenTc : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → Flat R Γ A B
  | _, _, _, .lit d hsub => flattenT d hsub
  | _, _, _, .ofCv u c => flattenCv u c rfl
  | _, _, _, .refl _ _ => .nil _
  | _, _, _, .symm c => (flattenTc c).symm
  | _, _, _, .trans c₁ c₂ => (flattenTc c₁).append (flattenTc c₂)
  | _, _, _, .piCod u hA c => .cons (.piCod u hA c) rfl (.nil _)
  | _, _, _, .subst0 j c hget hv => .cons (.subst0 j c hget hv) rfl (.nil _)
  | _, _, _, .substLet j c hget hv => .cons (.substLet j c hget hv) rfl (.nil _)
  | _, _, _, .wk d k c => (flattenTc c).wk d k

/-! ### leaves: every flattened leaf is a sub-derivation of an input leaf -/

theorem flattenCv_leaves (u : Level) : {Γ : LCtx} → {a b T : Expr Nat} →
    (c : EvCv R Γ a b T) → (hT : T = .sort u) → ∀ ℓ ∈ (flattenCv u c hT).leaves, ℓ ∈ c.leaves
  | _, _, _, _, .trans c₁ c₂, hT => fun ℓ hℓ => by
      simp only [flattenCv, Flat.append_leaves, List.mem_append] at hℓ
      simp only [EvCv.leaves, List.mem_append]
      rcases hℓ with hℓ | hℓ
      · exact .inl (flattenCv_leaves u c₁ hT ℓ hℓ)
      · exact .inr (flattenCv_leaves u c₂ hT ℓ hℓ)
  | _, _, _, _, .symm c, hT => fun ℓ hℓ => by
      simp only [flattenCv] at hℓ
      have := (flattenCv u c hT).symm_leaves_mem ℓ hℓ
      simpa only [EvCv.leaves] using flattenCv_leaves u c hT ℓ this
  | _, _, _, _, .refl _, _ => fun _ h => by simp only [flattenCv, Flat.leaves, List.not_mem_nil] at h
  | _, _, _, _, .lit _ _, hT => fun ℓ hℓ => by
      simpa only [flattenCv, Flat.leaves, EvTc.leaves, EvCv.castIdx_leaves, List.append_nil]
        using hℓ
  | _, _, _, _, .tyConv _ _ _, hT => fun ℓ hℓ => by
      simpa only [flattenCv, Flat.leaves, EvTc.leaves, EvCv.castIdx_leaves, List.append_nil]
        using hℓ
  | _, _, _, _, .wk _ _ _, hT => fun ℓ hℓ => by
      simpa only [flattenCv, Flat.leaves, EvTc.leaves, EvCv.castIdx_leaves, List.append_nil]
        using hℓ
  | _, _, _, _, .esub .., hT => fun ℓ hℓ => by
      simpa only [flattenCv, Flat.leaves, EvTc.leaves, EvCv.castIdx_leaves, List.append_nil]
        using hℓ
  | _, _, _, _, .subst0 .., hT => fun ℓ hℓ => by
      simpa only [flattenCv, Flat.leaves, EvTc.leaves, EvCv.castIdx_leaves, List.append_nil]
        using hℓ
  | _, _, _, _, .substLet .., hT => fun ℓ hℓ => by
      simpa only [flattenCv, Flat.leaves, EvTc.leaves, EvCv.castIdx_leaves, List.append_nil]
        using hℓ
  | _, _, _, _, .sorts .., hT => fun ℓ hℓ => by
      simpa only [flattenCv, Flat.leaves, EvTc.leaves, EvCv.castIdx_leaves, List.append_nil]
        using hℓ
  | _, _, _, _, .consts .., hT => fun ℓ hℓ => by
      simpa only [flattenCv, Flat.leaves, EvTc.leaves, EvCv.castIdx_leaves, List.append_nil]
        using hℓ
  | _, _, _, _, .rety _ _, hT => fun ℓ hℓ => by
      simpa only [flattenCv, Flat.leaves, EvTc.leaves, EvCv.castIdx_leaves, List.append_nil]
        using hℓ

theorem flattenT_leaves : {Γ : LCtx} → {A B : Expr Nat} → (d : TyConvT E n Γ A B) →
    (hsub : ∃ r ∈ R, SubEq (.tc d) r) → ∀ ℓ ∈ (flattenT d hsub).leaves, SubOf ℓ (.tc d)
  | _, _, _, .refl _ _, _ => fun _ h => by simp only [flattenT, Flat.leaves, List.not_mem_nil] at h
  | _, _, _, .of _ _ _ u h, _ => fun ℓ hℓ => by
      simp only [flattenT, Flat.leaves, EvTc.leaves, EvCv.leaves, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hℓ
      subst hℓ
      exact .child (tcChildOf h)
  | _, _, _, .trans _ _ _ _ d₁ d₂, hsub => fun ℓ hℓ => by
      simp only [flattenT, Flat.append_leaves, List.mem_append] at hℓ
      rcases hℓ with hℓ | hℓ
      · exact .trans (flattenT_leaves d₁ _ ℓ hℓ) (.child (tcChildFst d₁ d₂))
      · exact .trans (flattenT_leaves d₂ _ ℓ hℓ) (.child (tcChildSnd d₁ d₂))

theorem flattenTc_leaves : {Γ : LCtx} → {A B : Expr Nat} → (c : EvTc R Γ A B) →
    ∀ ℓ ∈ (flattenTc c).leaves, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ'
  | _, _, _, .lit d hsub => fun ℓ hℓ =>
      ⟨.tc d, by simp only [EvTc.leaves, List.mem_cons, List.not_mem_nil, or_false],
        .inr (flattenT_leaves d hsub ℓ hℓ)⟩
  | _, _, _, .ofCv u c => fun ℓ hℓ => ⟨ℓ, flattenCv_leaves u c rfl ℓ hℓ, .inl rfl⟩
  | _, _, _, .refl _ _ => fun _ h => by simp only [flattenTc, Flat.leaves, List.not_mem_nil] at h
  | _, _, _, .symm c => fun ℓ hℓ => by
      simp only [flattenTc] at hℓ
      exact flattenTc_leaves c ℓ ((flattenTc c).symm_leaves_mem ℓ hℓ)
  | _, _, _, .trans c₁ c₂ => fun ℓ hℓ => by
      simp only [flattenTc, Flat.append_leaves, List.mem_append] at hℓ
      simp only [EvTc.leaves, List.mem_append]
      rcases hℓ with hℓ | hℓ
      · obtain ⟨ℓ', h', hs⟩ := flattenTc_leaves c₁ ℓ hℓ
        exact ⟨ℓ', .inl h', hs⟩
      · obtain ⟨ℓ', h', hs⟩ := flattenTc_leaves c₂ ℓ hℓ
        exact ⟨ℓ', .inr h', hs⟩
  | _, _, _, .piCod _ _ _ => fun ℓ hℓ => by
      simp only [flattenTc, Flat.leaves, List.append_nil] at hℓ
      exact ⟨ℓ, hℓ, .inl rfl⟩
  | _, _, _, .subst0 .. => fun ℓ hℓ => by
      simp only [flattenTc, Flat.leaves, List.append_nil] at hℓ
      exact ⟨ℓ, hℓ, .inl rfl⟩
  | _, _, _, .substLet .. => fun ℓ hℓ => by
      simp only [flattenTc, Flat.leaves, List.append_nil] at hℓ
      exact ⟨ℓ, hℓ, .inl rfl⟩
  | _, _, _, .wk d k c => fun ℓ hℓ => by
      simp only [flattenTc, Flat.wk_leaves] at hℓ
      simpa only [EvTc.leaves] using flattenTc_leaves c ℓ hℓ

/-! ### segmentation: the shortest nonempty prefix ending at a Π -/

/-- the shortest nonempty prefix of `f` whose end is a Π-shaped type (returned with the proof),
    and the rest; for `nil` the prefix is empty and the end is `A₀` itself. -/
def Flat.splitPi : {A₀ C : Expr Nat} → (f : Flat R Γ A₀ C) → isPi C = true →
    Σ' (M : Expr Nat), isPi M = true ×' (Flat R Γ A₀ M × Flat R Γ M C)
  | _, _, .nil A, hC => ⟨A, hC, .nil A, .nil A⟩
  | _, _, @Flat.cons _ _ _ _ A (.pi M₁ M₂) B l hl rest, _ =>
      ⟨.pi M₁ M₂, rfl, .cons l hl (.nil _), rest⟩
  | _, _, @Flat.cons _ _ _ _ A M B l hl rest, hC =>
      let s := rest.splitPi hC
      ⟨s.1, s.2.1, .cons l hl s.2.2.1, s.2.2.2⟩

theorem Flat.splitPi_rest_le : {A₀ C : Expr Nat} → (f : Flat R Γ A₀ C) → (hC : isPi C = true) →
    (f.splitPi hC).2.2.2.length ≤ f.length
  | _, _, .nil _, _ => Nat.le_refl _
  | _, _, @Flat.cons _ _ _ _ A M B l hl rest, hC => by
      have ih := rest.splitPi_rest_le hC
      cases M <;> simp only [Flat.splitPi, Flat.length] <;> omega

/-- the rest is strictly shorter than a `cons` chain (the prefix is nonempty). -/
theorem Flat.splitPi_rest_lt {A M B : Expr Nat} (l : EvTc R Γ A M) (hl : isLink l = true)
    (rest : Flat R Γ M B) (hC : isPi B = true) :
    ((Flat.cons l hl rest).splitPi hC).2.2.2.length < (Flat.cons l hl rest).length := by
  have ih := rest.splitPi_rest_le hC
  cases M <;> simp only [Flat.splitPi, Flat.length] <;> omega

/-- the prefix and the rest together are the chain's leaves. -/
theorem Flat.splitPi_leaves : {A₀ C : Expr Nat} → (f : Flat R Γ A₀ C) → (hC : isPi C = true) →
    (f.splitPi hC).2.2.1.leaves ++ (f.splitPi hC).2.2.2.leaves = f.leaves
  | _, _, .nil _, _ => rfl
  | _, _, @Flat.cons _ _ _ _ A M B l hl rest, hC => by
      have ih := rest.splitPi_leaves hC
      cases M <;> simp only [Flat.splitPi, Flat.leaves, List.append_nil, List.append_assoc, ih]

/-! ### admissibility of a prefix for the valley route -/

/-- every link is a `bLink`. -/
def Flat.bPrefix : {A B : Expr Nat} → Flat R Γ A B → Bool
  | _, _, .nil _ => true
  | _, _, .cons l _ rest => bLink l && rest.bPrefix

/-- no Π-shaped type strictly inside: the links' right endpoints before the last are non-Π. -/
def Flat.interiorNonPi : {A B : Expr Nat} → Flat R Γ A B → Bool
  | _, _, .nil _ => true
  | _, _, .cons _ _ (.nil _) => true
  | _, _, @Flat.cons _ _ _ _ _ M _ _ _ (.cons l' hl' rest) =>
      (!isPi M) && Flat.interiorNonPi (.cons l' hl' rest)

theorem Flat.interiorNonPi_cons {A M B : Expr Nat} (l : EvTc R Γ A M) (hl : isLink l = true)
    (p : Flat R Γ M B) (hM : isPi M = false) (hp : p.interiorNonPi = true) :
    (Flat.cons l hl p).interiorNonPi = true := by
  cases p with
  | nil _ => rfl
  | cons l' hl' rest' =>
      simp only [Flat.interiorNonPi, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨hM, hp⟩

/-- `splitPi`'s prefix has no Π-shaped type strictly inside. -/
theorem Flat.splitPi_interior : {A₀ C : Expr Nat} → (f : Flat R Γ A₀ C) → (hC : isPi C = true) →
    (f.splitPi hC).2.2.1.interiorNonPi = true
  | _, _, .nil _, _ => rfl
  | _, _, @Flat.cons _ _ _ _ A M B l hl rest, hC => by
      have ih := rest.splitPi_interior hC
      cases M <;> simp only [Flat.splitPi, Flat.interiorNonPi] <;>
        exact Flat.interiorNonPi_cons l hl _ rfl ih

/-! ### pins -/

section Pins
open EtaKAnnot EtaKAnnot.Pins

/-- the etaK fixture's request flattens to one Π→Π link (`cL` is `refl`, dropped; `cR` is one
    `of`): Stratum A's case. -/
theorem pin_request_flat_length : (flattenTc request).length = 1 := by
  simp only [request, annotRequest, cL, cR, flattenTc, flattenT, Flat.append, Flat.symm,
    Flat.length]

/-- the β-redex middle (S1's `betaMiddleT`) flattens to two links. -/
theorem pin_betaMiddle_flat_length :
    (flattenTc (EvTc.lit betaMiddleT ⟨.tc betaMiddleT, .head _, .inl rfl⟩ :
      EvTc [Jd.tc betaMiddleT] [] piX piX)).length = 2 := by
  simp only [betaMiddleT, flattenTc, flattenT, Flat.append, Flat.length]

/-- the two links of the β-redex middle, written out: `Π ≡ redex` and `redex ≡ Π`, each the
    `of` child of `betaMiddleT`'s `trans`, so each literal is strictly below the one root. -/
abbrev betaRedex : Expr Nat := .app (.lam sX (.bvar 0)) piX

def betaD₁ : TyConvT emptyEnv 0 [] piX betaRedex :=
  .of [] piX betaRedex (.imax (.succ .zero) (.succ .zero)) (.symm [] betaRedex piX sX betaRedexConv)

def betaD₂ : TyConvT emptyEnv 0 [] betaRedex piX :=
  .of [] betaRedex piX (.imax (.succ .zero) (.succ .zero)) betaRedexConv

def betaLink₁ : EvTc [Jd.tc betaMiddleT] [] piX betaRedex :=
  .ofCv (.imax (.succ .zero) (.succ .zero)) (.lit (.symm [] betaRedex piX sX betaRedexConv)
    ⟨.tc betaMiddleT, .head _, .inr (.trans (.child (tcChildOf _)) (.child (tcChildFst betaD₁ betaD₂)))⟩)

def betaLink₂ : EvTc [Jd.tc betaMiddleT] [] betaRedex piX :=
  .ofCv (.imax (.succ .zero) (.succ .zero)) (.lit betaRedexConv
    ⟨.tc betaMiddleT, .head _, .inr (.trans (.child (tcChildOf _)) (.child (tcChildSnd betaD₁ betaD₂)))⟩)

/-- the flat two-link chain `Π ≡ redex ≡ Π`. -/
def betaTwoLinks : Flat [Jd.tc betaMiddleT] [] piX piX :=
  .cons betaLink₁ rfl (.cons betaLink₂ rfl (.nil piX))

/-- its `splitPi` prefix is the whole chain: the interior type is an application. -/
theorem pin_betaTwoLinks_splitPi_prefix_length :
    (betaTwoLinks.splitPi rfl).2.2.1.length = 2 := by
  simp only [betaTwoLinks, Flat.splitPi, Flat.length]

/-- and it is admissible for the valley route. -/
theorem pin_betaTwoLinks_bPrefix : (betaTwoLinks.splitPi rfl).2.2.1.bPrefix = true := by
  simp only [betaTwoLinks, Flat.splitPi, Flat.bPrefix, betaLink₁, betaLink₂, bLink, bCv,
    Bool.and_self, Bool.and_true]

/-- the interior is not a Π. -/
theorem pin_betaTwoLinks_interior : (betaTwoLinks.splitPi rfl).2.2.1.interiorNonPi = true := by
  simp only [betaTwoLinks, Flat.splitPi, Flat.interiorNonPi, isPi, Bool.not_false, Bool.true_and]

/-- a substitution link in a Stratum-B position is not `bLink` (W-X-SUBST). -/
theorem pin_subst_not_bLink {Γ₀ : LCtx} {A₀ A₀' t v : Expr Nat} (j : Nat) (c : EvTc R Γ₀ A₀ A₀')
    (hget : Γ₀[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ₀) (lift 0 j v) (lift 0 j t)) :
    bLink (EvTc.subst0 j c hget hv) = false := rfl

end Pins

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.bCv
#print axioms Rcic.Declarative.F8Measure.isLink
#print axioms Rcic.Declarative.F8Measure.bLink
#print axioms Rcic.Declarative.F8Measure.linkSymm
#print axioms Rcic.Declarative.F8Measure.linkSymm_isLink
#print axioms Rcic.Declarative.F8Measure.linkSymm_leaves
#print axioms Rcic.Declarative.F8Measure.linkSymm_bLink
#print axioms Rcic.Declarative.F8Measure.Flat
#print axioms Rcic.Declarative.F8Measure.Flat.leaves
#print axioms Rcic.Declarative.F8Measure.Flat.length
#print axioms Rcic.Declarative.F8Measure.Flat.append
#print axioms Rcic.Declarative.F8Measure.Flat.append_leaves
#print axioms Rcic.Declarative.F8Measure.Flat.append_length
#print axioms Rcic.Declarative.F8Measure.Flat.symm
#print axioms Rcic.Declarative.F8Measure.Flat.symm_leaves_mem
#print axioms Rcic.Declarative.F8Measure.Flat.symm_length
#print axioms Rcic.Declarative.F8Measure.Flat.wk
#print axioms Rcic.Declarative.F8Measure.Flat.wk_leaves
#print axioms Rcic.Declarative.F8Measure.Flat.wk_length
#print axioms Rcic.Declarative.F8Measure.EvCv.castIdx
#print axioms Rcic.Declarative.F8Measure.EvCv.castIdx_leaves
#print axioms Rcic.Declarative.F8Measure.flattenCv
#print axioms Rcic.Declarative.F8Measure.flattenT
#print axioms Rcic.Declarative.F8Measure.flattenTc
#print axioms Rcic.Declarative.F8Measure.flattenCv_leaves
#print axioms Rcic.Declarative.F8Measure.flattenT_leaves
#print axioms Rcic.Declarative.F8Measure.flattenTc_leaves
#print axioms Rcic.Declarative.F8Measure.Flat.splitPi
#print axioms Rcic.Declarative.F8Measure.Flat.splitPi_rest_le
#print axioms Rcic.Declarative.F8Measure.Flat.splitPi_rest_lt
#print axioms Rcic.Declarative.F8Measure.Flat.splitPi_leaves
#print axioms Rcic.Declarative.F8Measure.Flat.bPrefix
#print axioms Rcic.Declarative.F8Measure.Flat.interiorNonPi
#print axioms Rcic.Declarative.F8Measure.Flat.interiorNonPi_cons
#print axioms Rcic.Declarative.F8Measure.Flat.splitPi_interior
#print axioms Rcic.Declarative.F8Measure.pin_request_flat_length
#print axioms Rcic.Declarative.F8Measure.pin_betaMiddle_flat_length
#print axioms Rcic.Declarative.F8Measure.betaD₁
#print axioms Rcic.Declarative.F8Measure.betaD₂
#print axioms Rcic.Declarative.F8Measure.betaLink₁
#print axioms Rcic.Declarative.F8Measure.betaLink₂
#print axioms Rcic.Declarative.F8Measure.betaTwoLinks
#print axioms Rcic.Declarative.F8Measure.pin_betaTwoLinks_splitPi_prefix_length
#print axioms Rcic.Declarative.F8Measure.pin_betaTwoLinks_bPrefix
#print axioms Rcic.Declarative.F8Measure.pin_betaTwoLinks_interior
#print axioms Rcic.Declarative.F8Measure.pin_subst_not_bLink
