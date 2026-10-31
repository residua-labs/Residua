import rcic.RcicDTMeta
import rcic.RcicDTMetaTypedScope
import rcic.RcicAnnCoh
import rcic.RcicAnnErase
import rcic.RcicTypedInvert
import rcic.RcicTypedConv
import rcic.RcicTypedWeaken
import rcic.RcicFixtures
import rcic.RcicTypedGroupPins

/-!
# O2S — the DT carriers' typed counterparts, in scope (00 §19.1 O-2)

The three chain rows are discharged in scope on the typed root
(`typedRowsWf_of_scopeCheck` / `typedRowsWf_of_envWfT_semPrefix`), but the
top-level DT carriers still state them on the legacy judgment, where they are
refuted or degenerate (R-ConvCollapse). This module lands the carriers' typed
counterparts over `EnvWfT E` + `hW.InScope`, one beside each legacy carrier,
without editing any legacy statement:

* `DT021T_no_cumulativity` — ROW 1 restated at the legacy carrier's shape;
* `DT012T_type_uniqueness` — through annotation coherence (`Ann.annTyA` on two
  annotations from `annHasTyT'`, then `tyConvT_of_tyConvA` erasure);
* `iotaPreserveT` — `hasTyT_iota_sr` through `annEnvA_of_envWfT_semPrefix`
  only (the ι route stays behind that one name so a later rebase onto a
  `DerivedIotaT`-based `ConvT.iota` touches one place);
* `oneStepSRT` / `DT010T_one_step_subject_reduction` — per-arm (β, ζ, ζ-local,
  δ, ι, lit) subject reduction concluding `HasTyT` + `TyConvT`;
* `DT011T_multi_step_subject_reduction` — the `Steps` chain.

Premise disclosure (the degeneracy tooth): every counterpart below takes only
`EnvWfT`, `hW.InScope`, `CtxWfT`, and the carrier's own subject matter. No
premise names a row, `TypedRowsWf`, `AnnEnvA`, `EnvSemA` or `IotaSRA`; no
statement mentions the legacy `HasTy`, `Conv` or `CtxWf` (grep count 0 in this
file). The rows enter only through the scope bridge inside the proofs.

Helper inventory (all new, all in this file, none editing another module):
`levelBounded_zero_any`/`levelsBounded_zero_any`; the append-lookup lemmas
`lookupType_lt_length`/`lookupValue_lt_length`/`lookupType_append_lt`/
`lookupValue_append_lt`; the mutual `hasTyT_relocate`/`convT_relocate` (a
derivation at level bound 0 over `Δ` relocates to any bound over `Δ ++ Γ`;
sub-derivations live in extended contexts, so the source context is carried
along, and at `Δ = []` this is the plain []-to-Γ relocation); the inversions
`hasTyTInv_bvar`/`hasTyTInv_const`/`hasTyTInv_lit` (the RcicTypedInvert fork
pattern on the three shapes this arc inverts); `ctxWfTLookupValueAt` (ζ-local's
value typing through the context, each successor step composed with the typed
weakening, matching the lookup's lift); and `envWfT_bodyTyped` (δ's body typing
from the `EnvWfT` admission; a member with a body is a singleton
`definition`/`thm`/`opaque` entry whose stored arity is literally `0`, so the
level list collapses to `[]` exactly as the legacy `envWf_bodyTyped` tripwire
prescribes; the group walk carries `body = none` at every cons cell, so it
never produces one).

closure_claim 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Declarative

open Rcic.Declarative.Ann

/-! ## bounded-level relocation and append lookups -/

/-- a level bounded at 0 is param-free, hence bounded at every bound. -/
theorem levelBounded_zero_any {l : Level} (h : levelBounded 0 l = true) :
    ∀ (n : Nat), levelBounded n l = true := by
  induction l with
  | zero => intro _; rfl
  | param i => intro _; simp [levelBounded] at h
  | succ l ih =>
      intro n
      simp only [levelBounded] at h ⊢
      exact ih h n
  | max a b iha ihb =>
      intro n
      simp only [levelBounded, Bool.and_eq_true] at h ⊢
      exact ⟨iha h.1 n, ihb h.2 n⟩
  | imax a b iha ihb =>
      intro n
      simp only [levelBounded, Bool.and_eq_true] at h ⊢
      exact ⟨iha h.1 n, ihb h.2 n⟩

/-- the list form of the same fact. -/
theorem levelsBounded_zero_any {ls : List Level} (h : levelsBounded 0 ls = true) (n : Nat) :
    levelsBounded n ls = true := by
  induction ls with
  | nil => rfl
  | cons l t ih =>
      simp only [levelsBounded, Bool.and_eq_true] at h ⊢
      exact ⟨levelBounded_zero_any h.1 n, ih h.2⟩

/-- a successful type lookup is in range. -/
theorem lookupType_lt_length {Δ : LCtx} {i : Nat} {A : Expr Nat}
    (h : lookupType Δ i = some A) : i < Δ.length := by
  cases hn : Δ.get? i with
  | none =>
      exfalso
      rw [lookupType, hn] at h
      exact Option.noConfusion h
  | some d =>
      have hnne : ¬(Δ.get? i = none) := fun he => by rw [he] at hn; exact Option.noConfusion hn
      have hnl : ¬(Δ.length ≤ i) :=
        fun hle => hnne ((List.get?_eq_none (l := Δ) (n := i)).mpr hle)
      omega

/-- a successful value lookup is in range. -/
theorem lookupValue_lt_length {Δ : LCtx} {i : Nat} {v : Expr Nat}
    (h : lookupValue Δ i = some v) : i < Δ.length := by
  cases hn : Δ.get? i with
  | none =>
      exfalso
      rw [lookupValue, hn] at h
      exact Option.noConfusion h
  | some d =>
      have hnne : ¬(Δ.get? i = none) := fun he => by rw [he] at hn; exact Option.noConfusion hn
      have hnl : ¬(Δ.length ≤ i) :=
        fun hle => hnne ((List.get?_eq_none (l := Δ) (n := i)).mpr hle)
      omega

/-- below the split, appending a suffix changes neither lookup. -/
theorem lookupType_append_lt {Δ Γ : LCtx} {i : Nat} (h : i < Δ.length) :
    lookupType (Δ ++ Γ) i = lookupType Δ i := by
  simp only [lookupType]
  rw [List.get?_append h]

theorem lookupValue_append_lt {Δ Γ : LCtx} {i : Nat} (h : i < Δ.length) :
    lookupValue (Δ ++ Γ) i = lookupValue Δ i := by
  simp only [lookupValue]
  rw [List.get?_append h]

/- a derivation at level bound 0 over `Δ` relocates to any bound over
    `Δ ++ Γ`: sub-derivations live in contexts extended from `Δ`, so the
    source context is carried structurally; `bvar`/`zetaLocal` transport along
    the append lookups (the stored lift depends only on the index, not the
    tail); the only level-bound premise (`const`'s) is param-free, so it holds
    at every `n`. Mutually with `convT_relocate` for the `conv`/`refl` arms. -/
mutual
  def hasTyT_relocate {E : ResolvedEnv} :
      {Δ : LCtx}→ {e A : Expr Nat}→ HasTyT E 0 Δ e A →
      {n : Nat}→ {Γ : LCtx}→ HasTyT E n (Δ ++ Γ) e A
    | _, _, _, .sort _ _, _, _ => .sort _ _
    | _, _, _, .bvar _ _ _ h, _, _ =>
        .bvar _ _ _ (by rw [lookupType_append_lt (lookupType_lt_length h)]; exact h)
    | _, _, _, .const _ _ _ m hres hlen hwf, _, _ =>
        .const _ _ _ m hres hlen (levelsBounded_zero_any hwf _)
    | _, _, _, .pi _ _ _ _ _ hA hB, _, _ =>
        .pi _ _ _ _ _ (hasTyT_relocate hA) (hasTyT_relocate hB)
    | _, _, _, .lam _ _ _ _ _ hA hb, _, _ =>
        .lam _ _ _ _ _ (hasTyT_relocate hA) (hasTyT_relocate hb)
    | _, _, _, .app _ _ _ _ _ hf ha, _, _ =>
        .app _ _ _ _ _ (hasTyT_relocate hf) (hasTyT_relocate ha)
    | _, _, _, .letE _ _ _ _ _ _ hA hv hb, _, _ =>
        .letE _ _ _ _ _ _ (hasTyT_relocate hA) (hasTyT_relocate hv) (hasTyT_relocate hb)
    | _, _, _, .lit _ _ _ h, _, _ => .lit _ _ _ (hasTyT_relocate h)
    | _, _, _, .conv _ _ _ _ _ h hc, _, _ =>
        .conv _ _ _ _ _ (hasTyT_relocate h) (convT_relocate hc)

  def convT_relocate {E : ResolvedEnv} :
      {Δ : LCtx}→ {a b T : Expr Nat}→ ConvT E 0 Δ a b T →
      {n : Nat}→ {Γ : LCtx}→ ConvT E n (Δ ++ Γ) a b T
    | _, _, _, _, .refl _ _ _ hA, _, _ => .refl _ _ _ (hasTyT_relocate hA)
    | _, _, _, _, .symm _ _ _ _ h, _, _ => .symm _ _ _ _ (convT_relocate h)
    | _, _, _, _, .trans _ _ _ _ _ h1 h2, _, _ =>
        .trans _ _ _ _ _ (convT_relocate h1) (convT_relocate h2)
    | _, _, _, _, .beta _ _ _ _ _ _ hA hbody harg, _, _ =>
        .beta _ _ _ _ _ _ (hasTyT_relocate hA) (hasTyT_relocate hbody)
          (hasTyT_relocate harg)
    | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb, _, _ =>
        .zeta _ _ _ _ _ _ (hasTyT_relocate hA) (hasTyT_relocate hv)
          (hasTyT_relocate hb)
    | _, _, _, _, .zetaLocal _ _ _ _ hval hty hv, _, _ =>
        .zetaLocal _ _ _ _
          (by rw [lookupValue_append_lt (lookupValue_lt_length hval)]; exact hval)
          (by rw [lookupType_append_lt (lookupType_lt_length hty)]; exact hty)
          (hasTyT_relocate hv)
    | _, _, _, _, .delta _ r ls m b hres hbody htr hlen hwf hb, _, _ =>
        .delta _ r ls m b hres hbody htr hlen (levelsBounded_zero_any hwf _)
          (hasTyT_relocate hb)
    | _, _, _, _, .iota _ _ _ _ h hl hr, _, _ =>
        .iota _ _ _ _ h (hasTyT_relocate hl) (hasTyT_relocate hr)
    | _, _, _, _, .lit _ _ _ _ h hexp, _, _ =>
        .lit _ _ _ _ h (hasTyT_relocate hexp)
    | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2, _, _ =>
        .app _ _ _ _ _ _ _ (convT_relocate h1) (convT_relocate h2)
    | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb, _, _ =>
        .lam _ _ _ _ _ _ _ (convT_relocate hA) (convT_relocate hb)
    | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB, _, _ =>
        .pi _ _ _ _ _ _ _ (convT_relocate hA) (convT_relocate hB)
    | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb, _, _ =>
        .letE _ _ _ _ _ _ _ _ _ (convT_relocate hA) (convT_relocate hv)
          (convT_relocate hb)
    | _, _, _, _, .sorts _ _ _ h, _, _ => .sorts _ _ _ h
    | _, _, _, _, .consts _ _ _ _ _ hres hlen hwf hwf' h, _, _ =>
        .consts _ _ _ _ _ hres hlen (levelsBounded_zero_any hwf _)
          (levelsBounded_zero_any hwf' _) h
    | _, _, _, _, .eta _ _ _ _ h, _, _ => .eta _ _ _ _ (hasTyT_relocate h)
    | _, _, _, _, .irr _ _ _ _ hP hp hq, _, _ =>
        .irr _ _ _ _ (hasTyT_relocate hP) (hasTyT_relocate hp) (hasTyT_relocate hq)
    | _, _, _, _, .tyConv _ _ _ _ _ _ h hA, _, _ =>
        .tyConv _ _ _ _ _ _ (convT_relocate h) (convT_relocate hA)
end

/-! ## the three inversions this arc adds (RcicTypedInvert fork pattern) -/

/-- `bvar`-inversion, typed: every typing of `.bvar i` reads off the looked-up
    type and the type as a `TyConvT` from it. -/
def hasTyTInv_bvar {E : ResolvedEnv} {n : Nat} {i : Nat} :
    {Γ : LCtx}→ {e T : Expr Nat}→ HasTyT E n Γ e T → e = .bvar i →
    Σ' (A : Expr Nat), lookupType Γ i = some A ×' TyConvT E n Γ A T
  | _, _, _, .bvar _ _ _ h, heq => by
      injection heq with heq'; subst heq'; exact ⟨_, h, .refl _ _⟩
  | _, _, _, .conv _ _ _ _ _ h hc, heq =>
      let ⟨A, hlk, hcv⟩ := hasTyTInv_bvar h heq
      ⟨A, hlk, .trans _ _ _ _ hcv (.of _ _ _ _ hc)⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- `const`-inversion, typed. -/
def hasTyTInv_const {E : ResolvedEnv} {n : Nat} {r : Nat} {ls : List Level} :
    {Γ : LCtx}→ {e T : Expr Nat}→ HasTyT E n Γ e T → e = .const r ls →
    Σ' (m : CheckedMember), E.members r = some m ×' ls.length = m.arity ×'
      levelsBounded n ls = true ×' TyConvT E n Γ (instantiateLevels ls m.mtype) T
  | _, _, _, .const _ r' ls' m hres hlen hwf, heq => by
      injection heq with h1 h2
      subst h2
      subst h1
      exact ⟨m, hres, hlen, hwf, .refl _ _⟩
  | _, _, _, .conv Γ _ A _ _ h hc, heq =>
      have rec : Σ' (m : CheckedMember), E.members r = some m ×' ls.length = m.arity ×'
          levelsBounded n ls = true ×' TyConvT E n Γ (instantiateLevels ls m.mtype) A :=
        hasTyTInv_const h heq
      let ⟨m, hres, hlen, hwf, hcv⟩ := rec
      ⟨m, hres, hlen, hwf, .trans _ _ _ _ hcv (.of _ _ _ _ hc)⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- `lit`-inversion, typed: every typing of `.lit t` reads off the expansion's
    own typing and the type as a `TyConvT` from it. -/
def hasTyTInv_lit {E : ResolvedEnv} {n : Nat} {t : Nat} :
    {Γ : LCtx}→ {e T : Expr Nat}→ HasTyT E n Γ e T → e = .lit t →
    Σ' (T' : Expr Nat), HasTyT E n Γ (natExpand t) T' ×' TyConvT E n Γ T' T
  | _, _, _, .lit _ _ _ h, heq => by
      injection heq with heq'; subst heq'; exact ⟨_, h, .refl _ _⟩
  | _, _, _, .conv _ _ _ _ _ h hc, heq =>
      let ⟨T', hnat, hcv⟩ := hasTyTInv_lit h heq
      ⟨T', hnat, .trans _ _ _ _ hcv (.of _ _ _ _ hc)⟩
  | _, _, _, .sort _ _, heq => nomatch heq
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _ _, heq => nomatch heq

/-! ## ζ-local's value typing through the context -/

/-- a let-binding's value is typed at the SAME index's looked-up type; an
    assumption carries no value. Each successor step's lookup lifts by one, so
    the recursion composes the typed weakening at cutoff 0, matching the
    lifted value and type the context actually stores. -/
def ctxWfTLookupValueAt {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    (hΓ : CtxWfT E n Γ) : ∀ (i : Nat) (v : Expr Nat),
      lookupValue Γ i = some v →
      Σ' (A : Expr Nat), HasTyT E n Γ v A ×' lookupType Γ i = some A :=
  match hΓ with
  | .nil => fun i v h => by simp [lookupValue] at h
  | .assumption Γ A u hΓ _ => fun i v h => by
      cases i with
      | zero => simp [lookupValue] at h
      | succ i' =>
          rw [lookupValue_cons_succ] at h
          cases hl : lookupValue Γ i' with
          | none => rw [hl] at h; simp at h
          | some v0 =>
              rw [hl, Option.map_some'] at h
              injection h with hvEq
              subst hvEq
              have ⟨A0, hv0, hlk0⟩ := ctxWfTLookupValueAt hcl hΓ i' v0 hl
              exact ⟨lift 0 1 A0,
                hasTyTWeaken (LocalDecl.assumption A) hcl (c := 0) hv0,
                by rw [lookupType_cons_succ, hlk0, Option.map_some']⟩
  | .letBinding Γ A u v0 hΓ _ hv => fun i v h => by
      cases i with
      | zero =>
          simp only [lookupValue, List.getElem?_cons_zero] at h
          injection h with hvEq
          subst hvEq
          exact ⟨lift 0 1 A,
            hasTyTWeaken (LocalDecl.letBinding A v0) hcl (c := 0) hv, rfl⟩
      | succ i' =>
          rw [lookupValue_cons_succ] at h
          cases hl : lookupValue Γ i' with
          | none => rw [hl] at h; simp at h
          | some v1 =>
              rw [hl, Option.map_some'] at h
              injection h with hvEq
              subst hvEq
              have ⟨A0, hv0, hlk0⟩ := ctxWfTLookupValueAt hcl hΓ i' v1 hl
              exact ⟨lift 0 1 A0,
                hasTyTWeaken (LocalDecl.letBinding A v0) hcl (c := 0) hv0,
                by rw [lookupType_cons_succ, hlk0, Option.map_some']⟩

/-! ## δ's body typing from the `EnvWfT` admission -/

/-- the group-member walk, parameterized by the base environment's own body
    typing: every cons cell carries `body = none`, so the walk never produces a
    body-bearing member; the base fact is transported along the member
    extension by `hasTyTExt` + `members_extend_preserved`. -/
def envWfT_bodyTypedWalk {E : ResolvedEnv}
    (hbase : ∀ (r : Nat) (m : CheckedMember) (b : Expr Nat),
      E.members r = some m → m.body = some b →
      HasTyT E 0 [] b m.mtype ×' m.arity = 0)
    {S : ResolvedEnv} :
    {list : List (Nat × CheckedMember)} → {E' : ResolvedEnv} →
    GroupMembersT S E list E' →
    ∀ (r : Nat) (m : CheckedMember) (b : Expr Nat),
      E'.members r = some m → m.body = some b →
      HasTyT E' 0 [] b m.mtype ×' m.arity = 0
  | _, _, .nil _, r, m, b, hm, hb => hbase r m b hm hb
  | _, _, .cons E₁ r₁ m₁ rest E' hfresh hnobody _ _ _ _ _ _ _ _ _ _ _ hrest,
      r, m, b, hm, hb => by
      have hbase' : ∀ (r : Nat) (m : CheckedMember) (b : Expr Nat),
          (extendEnv E₁ r₁ m₁).members r = some m → m.body = some b →
          HasTyT (extendEnv E₁ r₁ m₁) 0 [] b m.mtype ×' m.arity = 0 := by
        intro r m b hmr hbr
        by_cases hrr : r = r₁
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hmr
          cases hmr
          rw [hnobody] at hbr
          cases hbr
        · simp only [extendEnv, if_neg hrr] at hmr
          exact ⟨hasTyTExt (members_extend_preserved hfresh) (hbase r m b hmr hbr).1,
            (hbase r m b hmr hbr).2⟩
      exact envWfT_bodyTypedWalk hbase' hrest r m b hm hb

/-- the raw recursion: a member WITH a body of an `EnvWfT` environment is a
    singleton definition/theorem/opaque entry, whose stored body typing lives
    at level bound 0 over the empty context (then relocated); group members
    all carry `body = none`, so the walk refutes the body case and defers to
    the pre-group base. Arity is the singleton entry's literal `0`. -/
def envWfT_bodyTypedRaw {E : ResolvedEnv} (hW : EnvWfT E) :
    ∀ (r : Nat) (m : CheckedMember) (b : Expr Nat),
      E.members r = some m → m.body = some b →
      HasTyT E 0 [] b m.mtype ×' m.arity = 0 :=
  match hW with
  | .empty => fun r m b hm hb => by simp only [emptyEnv] at hm; cases hm
  | .axiom (arity := arity) E r₀ A u hE hfresh _ _ _ =>
      fun r m b hm hb => by
        have hext := members_extend_preserved (m := ⟨.axiomM, arity, A, none⟩) hfresh
        by_cases hrr : r = r₀
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          cases hb
        · simp only [extendEnv, if_neg hrr] at hm
          have ⟨hv, h0⟩ := envWfT_bodyTypedRaw hE r m b hm hb
          exact ⟨hasTyTExt hext hv, h0⟩
  | .definition E r₀ A v u hE hfresh _ hv _ _ _ _ =>
      fun r m b hm hb => by
        have hext := members_extend_preserved (m := ⟨.definitionM, 0, A, some v⟩) hfresh
        by_cases hrr : r = r₀
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          injection hb with hb'
          subst hb'
          exact ⟨hasTyTExt hext (hasTyT_relocate hv), rfl⟩
        · simp only [extendEnv, if_neg hrr] at hm
          have ⟨hv0, h0⟩ := envWfT_bodyTypedRaw hE r m b hm hb
          exact ⟨hasTyTExt hext hv0, h0⟩
  | .thm E r₀ A p hE hfresh _ hp _ _ _ _ =>
      fun r m b hm hb => by
        have hext := members_extend_preserved (m := ⟨.theoremM, 0, A, some p⟩) hfresh
        by_cases hrr : r = r₀
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          injection hb with hb'
          subst hb'
          exact ⟨hasTyTExt hext (hasTyT_relocate hp), rfl⟩
        · simp only [extendEnv, if_neg hrr] at hm
          have ⟨hv0, h0⟩ := envWfT_bodyTypedRaw hE r m b hm hb
          exact ⟨hasTyTExt hext hv0, h0⟩
  | .opaque E r₀ A v u hE hfresh _ hv _ _ _ _ =>
      fun r m b hm hb => by
        have hext := members_extend_preserved (m := ⟨.opaqueM, 0, A, some v⟩) hfresh
        by_cases hrr : r = r₀
        · subst hrr
          simp only [extendEnv, if_pos rfl] at hm
          cases hm
          injection hb with hb'
          subst hb'
          exact ⟨hasTyTExt hext (hasTyT_relocate hv), rfl⟩
        · simp only [extendEnv, if_neg hrr] at hm
          have ⟨hv0, h0⟩ := envWfT_bodyTypedRaw hE r m b hm hb
          exact ⟨hasTyTExt hext hv0, h0⟩
  | .group E f fm ctors rr rm E' hE _ _ _ hmem =>
      envWfT_bodyTypedWalk (envWfT_bodyTypedRaw hE) hmem

/-- δ's body typing, the legacy `envWf_bodyTyped`'s counterpart: the arity-0
    tripwire (a member with a body is a 0-arity singleton) collapses the level
    list to `[]`, then the []-context relocation lands the stored typing at
    any `(n, Γ)`. -/
def envWfT_bodyTyped {E : ResolvedEnv} (hW : EnvWfT E) {n : Nat} {Γ : LCtx}
    {r : Nat} {m : CheckedMember} {b : Expr Nat} {ls : List Level}
    (hres : E.members r = some m) (hbody : m.body = some b) (hlen : ls.length = m.arity) :
    HasTyT E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype) := by
  have ⟨hv, h0⟩ := envWfT_bodyTypedRaw hW r m b hres hbody
  have hz : ls = [] := by
    rw [h0] at hlen
    cases ls with
    | nil => rfl
    | cons _ xs => exfalso; simp only [List.length_cons] at hlen; omega
  subst hz
  simp only [instantiateLevels_nil]
  exact hasTyT_relocate hv

/-! ## the counterparts -/

/-- DT-021 in scope: ROW 1 restated at the legacy carrier's shape — a typed
    conversion between two sorts collapses their levels. Premises: the scope,
    the context, the conversion. -/
theorem DT021T_no_cumulativity {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {u v : Level} {T : Expr Nat}
    (hc : ConvT E n Γ (.sort u) (.sort v) T) : eqN u v :=
  Ann.sortConvCharT_semPrefix hW hP hΓ hc

/-- DT-012 in scope: type uniqueness through annotation coherence — two
    annotations of one term (`annHasTyT'`) have convertible types
    (`Ann.annTyA`), and the chain erases (`tyConvT_of_tyConvA`). -/
theorem DT012T_type_uniqueness {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ) {e A B : Expr Nat}
    (hA : HasTyT E n Γ e A) (hB : HasTyT E n Γ e B) :
    Nonempty (TyConvT E n Γ A B) := by
  obtain ⟨EA, rfl, C, hn⟩ := Ann.annEnvA_of_envWfT_semPrefix hW hP
  obtain ⟨ΓA, hctx, ⟨hΓA⟩⟩ := annCtxWfT' C hn hΓ
  obtain ⟨eA1, TA1, he1, hT1, ⟨t1⟩⟩ := annHasTyT' C hn hA hΓA hctx
  obtain ⟨eA2, TA2, he2, hT2, ⟨t2⟩⟩ := annHasTyT' C hn hB hΓA hctx
  obtain ⟨hW⟩ := C.wf
  obtain ⟨c⟩ := Ann.annTyA C.hE C.hI C.hIS C.hENC C.hEN C.hR (C.hS n) posValA_one hΓA
    (he1.trans he2.symm) t1 t2
  obtain ⟨c'⟩ := tyConvT_of_tyConvA hW (C.hNS hn) c
  rw [hT1, hT2, hctx] at c'
  exact ⟨c'⟩

/-- ι preservation in scope, through `hasTyT_iota_sr` ONLY (one name, so a
    later `DerivedIotaT` rebase touches one place). -/
theorem iotaPreserveT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {lhs rhs T : Expr Nat}
    (hd : DerivedIota E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) := by
  obtain ⟨EA, rfl, C, hn⟩ := Ann.annEnvA_of_envWfT_semPrefix hW hP
  exact hasTyT_iota_sr C hn hΓ hd hlhs

/-- TYPED-ROUTE SIBLING (R-NoFunRec-1 B2, phase-2B): `iotaPreserveT` at the
    shape-based `DerivedIotaT` evidence, riding `Ann.hasTyT_iota_srT`.  The
    `CorrCertsBelow` premise is the sound gate the `vecOnlyEnvU` countermodel
    demands — it cannot be derived from `EnvWfT` + `InScope` (it is REFUTED at
    `vecEnvUT`, `not_corrCertsBelow_vecEnvUT`), so it stays an explicit
    hypothesis here and is never a universal assumption. -/
theorem iotaPreserveTT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope) {n : Nat}
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) (hC : CorrCertsBelow E) {lhs rhs T : Expr Nat}
    (hd : DerivedIotaT E lhs rhs) (hlhs : HasTyT E n Γ lhs T) :
    Nonempty (HasTyT E n Γ rhs T) := by
  obtain ⟨EA, rfl, C, hn⟩ := Ann.annEnvA_of_envWfT_semPrefix hW hP
  exact hasTyT_iota_srT C hn hC hΓ hd hlhs

/-- DT-010's core, per arm. β: app/lam inversion, the Π row in scope for the
    domains and codomains, then retype the body along the codomain chain
    (`hasTyT_of_tyConv`) and substitute the argument at the domain conversion
    collapsed at the domain's own sort. ζ: letE inversion, `ConvT.zeta`, and
    the endpoints theorem. ζ-local: bvar inversion plus the context's own
    value typing. δ: const inversion plus `envWfT_bodyTyped`. ι:
    `hasTyT_iota_sr`. lit: lit inversion and the expansion equation. -/
theorem oneStepSRT {E : ResolvedEnv} (hW : EnvWfT E) (hP : hW.InScope)
    {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e S e' : Expr Nat} (h : HasTyT E n Γ e S) (hs : Step E n Γ e e') :
    Nonempty (Σ' (B : Expr Nat), HasTyT E n Γ e' B ×' TyConvT E n Γ S B) := by
  obtain ⟨EA, rfl, C, hn⟩ := Ann.annEnvA_of_envWfT_semPrefix hW hP
  have hrows := Ann.typedRowsWf_of_envWfT_semPrefix hW hP n
  have hcl := envClosed_of_envWfT hW
  exact match hs with
    | .beta _ A0 body arg => by
        obtain ⟨A1, B1, hf, ha, hcv⟩ := hasTyTInv_app h rfl
        obtain ⟨u, B_lam, hA0ty, hbody, hcv_lam⟩ := hasTyTInv_lam hf rfl
        obtain ⟨⟨hBdom⟩, ⟨hBcod⟩⟩ := hrows.piRow hΓ hcv_lam
        obtain ⟨cdom⟩ := Ann.convT_of_tyConvT_sort C hn hΓ hA0ty hBdom
        have hbody' := hasTyT_of_tyConv hbody hBcod
        have ha' :=
          HasTyT.conv _ _ _ _ u ha (ConvT.symm _ _ _ _ cdom)
        have hsub := hasTyT_subst0_of_envWfT hW hbody' ha'
        exact ⟨_, hsub, TyConvT.symmT hcv⟩
    | .zeta _ A0 value body => by
        obtain ⟨u, B_let, hAty, hv, hb, hcv⟩ := hasTyTInv_letE h rfl
        have hz := ConvT.zeta (Γ := Γ) A0 value body B_let u hAty hv hb
        obtain ⟨_, ⟨hr⟩⟩ := DT009T_endpoints_inScope hW hP hΓ hz
        exact ⟨_, hr, TyConvT.symmT hcv⟩
    | .zetaLocal _ i vz hvz => by
        obtain ⟨A0, hlk, hcv⟩ := hasTyTInv_bvar (i := i) h rfl
        obtain ⟨A_v, hvty, hlk'⟩ := ctxWfTLookupValueAt hcl hΓ i vz hvz
        have hEq : some A0 = some A_v := hlk.symm.trans hlk'
        injection hEq with hAeq
        rw [← hAeq] at hvty
        exact ⟨A0, hvty, TyConvT.symmT hcv⟩
    | .delta _ r ls m b0 hres hbody _htr => by
        obtain ⟨m', hres', hlen, hwf, hcv⟩ := hasTyTInv_const (r := r) (ls := ls) h rfl
        have hmeq : some m = some m' := hres.symm.trans hres'
        injection hmeq with hmeq'
        subst hmeq'
        have hty := envWfT_bodyTyped (n := n) (Γ := Γ) hW hres hbody hlen
        exact ⟨_, hty, TyConvT.symmT hcv⟩
    | .iota _ _ _ hd => by
        obtain ⟨hr⟩ := hasTyT_iota_sr C hn hΓ hd h
        exact ⟨S, hr, TyConvT.refl _ _⟩
    | .lit _ t exp hlexp => by
        obtain ⟨T', hnat, hcv⟩ := hasTyTInv_lit (t := t) h rfl
        cases hlexp
        exact ⟨T', hnat, TyConvT.symmT hcv⟩

/-- DT-010 in scope: one-step subject reduction on the typed judgment. The
    reduct is typed at some type convertible with the source's. -/
theorem DT010T_one_step_subject_reduction {E : ResolvedEnv} (hW : EnvWfT E)
    (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e S e' : Expr Nat} (h : HasTyT E n Γ e S) (hs : Step E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) :=
  (oneStepSRT hW hP hΓ h hs).elim fun ⟨B, h1, h2⟩ => ⟨B, ⟨h1⟩, ⟨h2⟩⟩

/-- DT-011 in scope: the multi-step chain, by induction on `Steps`, chained
    through `TyConvT.trans`. -/
theorem DT011T_multi_step_subject_reduction {E : ResolvedEnv} (hW : EnvWfT E)
    (hP : hW.InScope) {n : Nat} {Γ : LCtx} (hΓ : CtxWfT E n Γ)
    {e S e' : Expr Nat} (h : HasTyT E n Γ e S) (hs : Steps E n Γ e e') :
    ∃ B, Nonempty (HasTyT E n Γ e' B) ∧ Nonempty (TyConvT E n Γ S B) := by
  induction hs generalizing S with
  | refl _ => exact ⟨S, ⟨h⟩, ⟨TyConvT.refl _ _⟩⟩
  | step a b c h1 h2 ih =>
      obtain ⟨B1, hb1, hc1⟩ := oneStepSRT hW hP hΓ h h1
      obtain ⟨B2, hb2, hc2⟩ := ih hb1
      exact ⟨B2, hb2, hc2.elim fun hc2' => ⟨TyConvT.trans _ _ _ _ hc1 hc2'⟩⟩

/-! ## consumption pins (real in-scope environments, no supply parameter) -/

/-- PIN (β): the identity-on-sorts beta redex, typed at `listEnvUT`. -/
def pinBetaFn (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] (.lam (.sort (.succ .zero)) (.bvar 0))
      (.pi (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  HasTyT.lam [] (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)
    (.sort (.succ .zero))
    (HasTyT.sort [] (.succ .zero))
    (HasTyT.bvar [LocalDecl.assumption (.sort (.succ .zero))] 0 _ rfl)

def pinBetaApp (E : ResolvedEnv) (n : Nat) :
    HasTyT E n [] (.app (.lam (.sort (.succ .zero)) (.bvar 0)) (.sort .zero))
      (instantiate0 (.sort .zero) (.sort (.succ .zero))) :=
  HasTyT.app _ _ _ _ _ (pinBetaFn E n) (HasTyT.sort [] .zero)

/-- PIN: DT-010T consumed at a REAL β-redex on the two-group environment;
    both the typing and the step are constructed, nothing assumed. -/
theorem pin_DT010T_beta {n : Nat} :
    ∃ B, Nonempty (HasTyT listEnvUT n []
        (instantiate0 (.sort .zero) (.bvar 0)) B) ∧
      Nonempty (TyConvT listEnvUT n [] (.sort (.succ .zero)) B) :=
  DT010T_one_step_subject_reduction listEnvUWfT listEnvUWfT_inScope CtxWfT.nil
    (pinBetaApp listEnvUT n)
    (Step.beta [] (.sort (.succ .zero)) (.bvar 0) (.sort .zero))

/-- PIN (δ): one definition member (`Sort 0`, of type `Sort 1`) extending
    `natEnvU` — `EnvWfT`'s definition arm, in scope by the base's scope. -/
def pinDefEnvU : ResolvedEnv :=
  extendEnv natEnvU 4 ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩

theorem pinDefEnvU_fresh : natEnvU.members 4 = none := by
  simp [natEnvU, natEnvPrefix, extendEnv, emptyEnv]

def pinDefEnvUWfT : EnvWfT pinDefEnvU :=
  EnvWfT.definition natEnvU 4 (.sort (.succ .zero)) (.sort .zero)
    (.succ (.succ .zero)) natEnvUWfT pinDefEnvU_fresh
    (HasTyT.sort [] (.succ .zero)) (HasTyT.sort [] .zero)
    (fun _ => rfl) (fun _ => rfl) rfl rfl

theorem pinDefEnvU_inScope : pinDefEnvUWfT.InScope := natEnvUWfT_inScope

def pinDeltaConst (n : Nat) :
    HasTyT pinDefEnvU n [] (.const 4 [])
      (instantiateLevels [] (.sort (.succ .zero))) :=
  HasTyT.const [] 4 [] ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩
    rfl rfl rfl

/-- PIN: DT-010T consumed at δ unfolding the definition at ref 4. -/
theorem pin_DT010T_delta {n : Nat} :
    ∃ B, Nonempty (HasTyT pinDefEnvU n []
        (instantiateLevels [] (.sort .zero)) B) ∧
      Nonempty (TyConvT pinDefEnvU n []
        (instantiateLevels [] (.sort (.succ .zero))) B) :=
  DT010T_one_step_subject_reduction pinDefEnvUWfT pinDefEnvU_inScope CtxWfT.nil
    (pinDeltaConst n)
    (Step.delta [] 4 [] ⟨.definitionM, 0, .sort (.succ .zero), some (.sort .zero)⟩
      (.sort .zero) rfl rfl rfl)

/-! ### the ι pin: the succ redex at the recursor, on a TYPABLE spine

`wSuccU`'s level list is `[param 0]`, under which its motive
`λ (_ : N), N` is not `HasTyT`-typable (its codomain would need
`Sort 1 ≡ Sort (param 0)`). The pin uses `wSuccU1`, the same witness at
`ls = [succ zero]` — the motive is typed at `Π (_ : N), Sort 1` with the
body `N : Sort 1`, and every motive application is beta-converted to `N`
through `ConvT.beta` at `B := Sort 1` (the body typing the rule needs). -/

def wSuccU1 : IotaWitness natEnvU := { wSuccU with ls := [.succ .zero] }

/-- the concrete upgrade: `wSuccU1` passes the DIRECT-fragment recognizer at
    fuel 64 — the same computation `pin_iotaWitnessSB_wSucc` runs at `natEnv`,
    here at `natEnvU`'s large-eliminating recursor (arity 1) and at
    `ls = [.succ .zero]`. -/
theorem pin_iotaWitnessSB_wSuccU1 : iotaWitnessSB wSuccU1 64 = true := by
  simp [iotaWitnessSB, directFragCheck, directFragOne,
    iotaWitnessStableB,
    constsMemberFuel, iotaSchemaS, iotaOpenRhs, iotaArgs,
    natEnvU, natEnvPrefix, listEnv, listEnvPrefix, emptyEnv, extendEnv,
    natFamMember, natZeroMember, natSuccMember, natRecMemberU, natRecTypeU,
    natRecDomsU,
    transparent, instantiateLevels, fieldBvars, ctorFieldTelRaw, lift,
    piTelescopeFuel, whnfFuel, transparentBody, noTransparentB, headStableB,
    piTailOf, esize, piCount, properShapeB, isFamilyApp, instPrefix,
    exprClosedAt, iotaRhsOf, rhsArgs, ctorSpine, ctorMajor, recCall, foldApps,
    recCallField, recPrefix, familyIdx, exactParamLocals, appsSpine,
    occursConst, piDomsOf, instantiate, instantiate0, instLevel,
    canonRecLevels, preMajorBvars, minorTel,
    wSuccU, wSuccU1,
    natMotive, natMinorZ, natMinorS, natField]
  decide

/-- the typed `IotaWitnessS` `wSuccU1` adapts to. -/
def wSuccU1S : IotaWitnessS natEnvU :=
  iotaWitnessSOf wSuccU1 64 pin_iotaWitnessSB_wSuccU1

/-- the typed derived-iota evidence at the pin's own lhs/rhs — the adapted
    witness transported along the checked lhs/rhs equalities
    (`iotaLhsOfS_iotaWitnessSOf`, `iotaRhsOfS_iotaWitnessSOf`). -/
def wSuccU1D : DerivedIotaT natEnvU (iotaLhsOf wSuccU1) (iotaRhsOf wSuccU1) := by
  have h1 : iotaLhsOfS wSuccU1S = iotaLhsOf wSuccU1 :=
    iotaLhsOfS_iotaWitnessSOf wSuccU1 64 pin_iotaWitnessSB_wSuccU1
  have h2 : iotaRhsOfS wSuccU1S = iotaRhsOf wSuccU1 :=
    iotaRhsOfS_iotaWitnessSOf wSuccU1 64 pin_iotaWitnessSB_wSuccU1
  rw [← h1, ← h2]
  exact .of wSuccU1S

def pinIotaFamTy : HasTyT natEnvU 1 [] (.const 0 []) (.sort (.succ .zero)) :=
  HasTyT.const [] 0 [] natFamMember rfl rfl rfl

def pinIotaZeroTy : HasTyT natEnvU 1 [] (.const 1 []) (.const 0 []) :=
  HasTyT.const [] 1 [] natZeroMember rfl rfl rfl

def pinIotaSuccTy :
    HasTyT natEnvU 1 [] (.const 2 []) (.pi (.const 0 []) (.const 0 [])) :=
  HasTyT.const [] 2 [] natSuccMember rfl rfl rfl

/-- the motive `λ (_ : N), N` at `Π (_ : N), Sort 1`. -/
def pinIotaMotiveTy : HasTyT natEnvU 1 [] natMotive
    (.pi (.const 0 []) (.sort (.succ .zero))) :=
  HasTyT.lam [] (.const 0 []) (.succ .zero) (.const 0 []) (.sort (.succ .zero))
    pinIotaFamTy (HasTyT.const _ 0 [] natFamMember rfl rfl rfl)

/-- `N : Sort 1` in any context over `N`. -/
def pinIotaNSortTy (Γ : LCtx) (hΓ : CtxWfT natEnvU 1 Γ) :
    HasTyT natEnvU 1 Γ (.const 0 []) (.sort (.succ .zero)) :=
  HasTyT.const _ 0 [] natFamMember rfl rfl rfl

/-- the beta conversion every motive application rides on: with the body
    `N` typed at `Sort 1`, `ConvT.beta` closes `motive a ≡ N` at `Sort 1`. -/
def pinIotaMotiveApp (Γ : LCtx) (a : Expr Nat)
    (ha : HasTyT natEnvU 1 Γ a (.const 0 [])) :
    ConvT natEnvU 1 Γ (.app natMotive a) (.const 0 []) (.sort (.succ .zero)) :=
  ConvT.beta Γ (.const 0 []) (.const 0 []) a (.sort (.succ .zero)) (.succ .zero)
    (HasTyT.const _ 0 [] natFamMember rfl rfl rfl)
    (HasTyT.const _ 0 [] natFamMember rfl rfl rfl) ha

/-- the zero minor, at the instantiated domain `motive zero`. -/
def pinIotaMinorZTy : HasTyT natEnvU 1 [] natMinorZ (.app natMotive (.const 1 [])) :=
  HasTyT.conv _ _ _ _ (.succ .zero) pinIotaZeroTy
    (ConvT.symm _ _ _ _ (pinIotaMotiveApp [] (.const 1 []) pinIotaZeroTy))

/-- the motive weakened under one `N` binder. -/
def pinIotaMotiveTy1 : HasTyT natEnvU 1 [LocalDecl.assumption (.const 0 [])] natMotive
    (.pi (.const 0 []) (.sort (.succ .zero))) :=
  hasTyTWeaken (LocalDecl.assumption (.const 0 [])) (envClosed_of_envWfT natEnvUWfT)
    (c := 0) pinIotaMotiveTy

/-- the motive weakened under the `ih : N` binder (`wSuccU`'s minor binds
    `ih` at `N`, not at the motive application, so the domain conversion rides
    a Π congruence below). -/
def pinIotaMotiveTyNN : HasTyT natEnvU 1
    [LocalDecl.assumption (.const 0 []), LocalDecl.assumption (.const 0 [])] natMotive
    (.pi (.const 0 []) (.sort (.succ .zero))) :=
  hasTyTWeaken (LocalDecl.assumption (.const 0 [])) (envClosed_of_envWfT natEnvUWfT)
    (c := 0) pinIotaMotiveTy1

/-- `succ n : N` under the `ih : N` binder. -/
def pinIotaSuccBvarNN :
    HasTyT natEnvU 1
      [LocalDecl.assumption (.const 0 []), LocalDecl.assumption (.const 0 [])]
      (.app (.const 2 []) (.bvar 1)) (.const 0 []) :=
  HasTyT.app _ (.const 2 []) (.bvar 1) (.const 0 []) (.const 0 [])
    (HasTyT.const _ 2 [] natSuccMember rfl rfl rfl)
    (HasTyT.bvar _ 1 (.const 0 []) rfl)

/-- the minor's body `zero : motive (succ n)` under the `ih : N` binder. -/
def pinIotaZeroBodyNN :
    HasTyT natEnvU 1
      [LocalDecl.assumption (.const 0 []), LocalDecl.assumption (.const 0 [])]
      (.const 1 []) (.app natMotive (.app (.const 2 []) (.bvar 1))) :=
  HasTyT.conv _ (.const 1 []) (.const 0 [])
    (.app natMotive (.app (.const 2 []) (.bvar 1))) (.succ .zero)
    (HasTyT.const _ 1 [] natZeroMember rfl rfl rfl)
    (ConvT.symm _ _ _ _
      (pinIotaMotiveApp
        [LocalDecl.assumption (.const 0 []), LocalDecl.assumption (.const 0 [])]
        (.app (.const 2 []) (.bvar 1)) pinIotaSuccBvarNN))

/-- the inner λ at its own domain `N`:
    `λ (ih : N), zero : Π (ih : N), motive (succ n)`. -/
def pinIotaMinorSInner : HasTyT natEnvU 1 [LocalDecl.assumption (.const 0 [])]
    (.lam (.const 0 []) (.const 1 []))
    (.pi (.const 0 []) (.app natMotive (.app (.const 2 []) (.bvar 1)))) :=
  HasTyT.lam [LocalDecl.assumption (.const 0 [])] (.const 0 []) (.succ .zero)
    (.const 1 []) (.app natMotive (.app (.const 2 []) (.bvar 1)))
    (HasTyT.const _ 0 [] natFamMember rfl rfl rfl)
    pinIotaZeroBodyNN

/-- the codomain's typing under the EXPECTED ih domain, for the congruence's
    reflexive right leg. -/
def pinIotaMotiveTyMN : HasTyT natEnvU 1
    [LocalDecl.assumption (.app natMotive (.bvar 0)), LocalDecl.assumption (.const 0 [])]
    natMotive (.pi (.const 0 []) (.sort (.succ .zero))) :=
  hasTyTWeaken (LocalDecl.assumption (.app natMotive (.bvar 0)))
    (envClosed_of_envWfT natEnvUWfT) (c := 0) pinIotaMotiveTy1

def pinIotaSuccBvarMN :
    HasTyT natEnvU 1
      [LocalDecl.assumption (.app natMotive (.bvar 0)),
        LocalDecl.assumption (.const 0 [])]
      (.app (.const 2 []) (.bvar 1)) (.const 0 []) :=
  HasTyT.app _ (.const 2 []) (.bvar 1) (.const 0 []) (.const 0 [])
    (HasTyT.const _ 2 [] natSuccMember rfl rfl rfl)
    (HasTyT.bvar _ 1 (.const 0 []) rfl)

def pinIotaMotiveAppMNTy : HasTyT natEnvU 1
    [LocalDecl.assumption (.app natMotive (.bvar 0)),
      LocalDecl.assumption (.const 0 [])]
    (.app natMotive (.app (.const 2 []) (.bvar 1))) (.sort (.succ .zero)) :=
  HasTyT.app _ natMotive (.app (.const 2 []) (.bvar 1)) (.const 0 [])
    (.sort (.succ .zero)) pinIotaMotiveTyMN pinIotaSuccBvarMN

/-- the same codomain typing under the LEFT domain's binder (`ConvT.pi`'s
    right leg ranges over `assumption A :: Γ`, the LEFT `A`). -/
def pinIotaMotiveAppNNTy : HasTyT natEnvU 1
    [LocalDecl.assumption (.const 0 []), LocalDecl.assumption (.const 0 [])]
    (.app natMotive (.app (.const 2 []) (.bvar 1))) (.sort (.succ .zero)) :=
  HasTyT.app _ natMotive (.app (.const 2 []) (.bvar 1)) (.const 0 [])
    (.sort (.succ .zero)) pinIotaMotiveTyNN pinIotaSuccBvarNN

/-- the inner λ retyped at the EXPECTED ih domain `motive n`, by Π
    congruence along `N ≡ motive n` (the beta conversion). -/
def pinIotaMinorSInnerConv : HasTyT natEnvU 1 [LocalDecl.assumption (.const 0 [])]
    (.lam (.const 0 []) (.const 1 []))
    (.pi (.app natMotive (.bvar 0)) (.app natMotive (.app (.const 2 []) (.bvar 1)))) :=
  HasTyT.conv _ _ (.pi (.const 0 []) (.app natMotive (.app (.const 2 []) (.bvar 1))))
    (.pi (.app natMotive (.bvar 0)) (.app natMotive (.app (.const 2 []) (.bvar 1))))
    (.imax (.succ .zero) (.succ .zero))
    pinIotaMinorSInner
    (ConvT.pi [LocalDecl.assumption (.const 0 [])] (.const 0 [])
      (.app natMotive (.bvar 0))
      (.app natMotive (.app (.const 2 []) (.bvar 1)))
      (.app natMotive (.app (.const 2 []) (.bvar 1)))
      (.succ .zero) (.succ .zero)
      (ConvT.symm _ _ _ _
        (pinIotaMotiveApp [LocalDecl.assumption (.const 0 [])] (.bvar 0)
          (HasTyT.bvar [LocalDecl.assumption (.const 0 [])] 0 (.const 0 []) rfl)))
      (ConvT.refl [LocalDecl.assumption (.const 0 []),
        LocalDecl.assumption (.const 0 [])]
        (.app natMotive (.app (.const 2 []) (.bvar 1))) (.sort (.succ .zero))
        pinIotaMotiveAppNNTy))

/-- the succ minor at the instantiated domain
    `Π (n : N), Π (ih : motive n), motive (succ n)`. -/
def pinIotaMinorSTy : HasTyT natEnvU 1 [] natMinorS
    (.pi (.const 0 []) (.pi (.app natMotive (.bvar 0))
      (.app natMotive (.app (.const 2 []) (.bvar 1))))) :=
  HasTyT.lam [] (.const 0 []) (.succ .zero)
    (.lam (.const 0 []) (.const 1 []))
    (.pi (.app natMotive (.bvar 0)) (.app natMotive (.app (.const 2 []) (.bvar 1))))
    pinIotaFamTy
    pinIotaMinorSInnerConv

/-- the major `succ zero : N`. -/
def pinIotaMajorTy :
    HasTyT natEnvU 1 [] (foldApps (.const 2 []) [natField]) (.const 0 []) :=
  HasTyT.app [] (.const 2 []) (.const 1 []) (.const 0 []) (.const 0 [])
    pinIotaSuccTy pinIotaZeroTy

/-- the whole spine `N.rec.{1} P z s (succ zero) : N`, at `n = 1`. -/
def pinIotaLhsTy : HasTyT natEnvU 1 [] (iotaLhsOf wSuccU1) (.const 0 []) :=
  have h0 : HasTyT natEnvU 1 [] (.const 3 [.succ .zero]) _ :=
    HasTyT.const [] 3 [.succ .zero] natRecMemberU rfl rfl rfl
  have h1 : HasTyT natEnvU 1 [] (.app (.const 3 [.succ .zero]) natMotive)
      (.pi (.app natMotive (.const 1 []))
        (.pi (.pi (.const 0 []) (.pi (.app natMotive (.bvar 0))
            (.app natMotive (.app (.const 2 []) (.bvar 1)))))
          (.pi (.const 0 []) (.app natMotive (.bvar 0))))) :=
    HasTyT.app [] _ _ _ _ h0 pinIotaMotiveTy
  have h2 : HasTyT natEnvU 1 []
      (.app (.app (.const 3 [.succ .zero]) natMotive) natMinorZ)
      (.pi (.pi (.const 0 []) (.pi (.app natMotive (.bvar 0))
          (.app natMotive (.app (.const 2 []) (.bvar 1)))))
        (.pi (.const 0 []) (.app natMotive (.bvar 0)))) :=
    HasTyT.app [] _ _ _ _ h1 pinIotaMinorZTy
  have h3 : HasTyT natEnvU 1 []
      (.app (.app (.app (.const 3 [.succ .zero]) natMotive) natMinorZ) natMinorS)
      (.pi (.const 0 []) (.app natMotive (.bvar 0))) :=
    HasTyT.app [] _ _ _ _ h2 pinIotaMinorSTy
  have h4 : HasTyT natEnvU 1 []
      (.app (.app (.app (.app (.const 3 [.succ .zero]) natMotive) natMinorZ)
        natMinorS) (foldApps (.const 2 []) [natField]))
      (.app natMotive (foldApps (.const 2 []) [natField])) :=
    HasTyT.app [] _ _ _ _ h3 pinIotaMajorTy
  HasTyT.conv _ _ (.app natMotive (foldApps (.const 2 []) [natField]))
    (.const 0 []) (.succ .zero) h4
    (pinIotaMotiveApp [] (foldApps (.const 2 []) [natField]) pinIotaMajorTy)

/-- PIN: `iotaPreserveT` consumed at the recursor on a constructor — the
    succ redex at `N.rec.{1}`, with the redex's typing CONSTRUCTED. -/
theorem pin_iotaPreserveT :
    Nonempty (HasTyT natEnvU 1 [] (iotaRhsOf wSuccU1) (.const 0 [])) :=
  iotaPreserveT natEnvUWfT natEnvUWfT_inScope CtxWfT.nil
    (DerivedIota.of wSuccU1) pinIotaLhsTy

/-- PIN: the typed-route sibling `iotaPreserveTT` consumed at the same redex —
    the shape-based evidence `wSuccU1D` fires at `natEnvU` under
    `corrCertsBelow_natEnvU`, the certificate the countermodel shows cannot
    be assumed at every well-formed environment. -/
theorem pin_iotaPreserveTT :
    Nonempty (HasTyT natEnvU 1 [] (iotaRhsOf wSuccU1) (.const 0 [])) :=
  iotaPreserveTT natEnvUWfT natEnvUWfT_inScope CtxWfT.nil
    corrCertsBelow_natEnvU wSuccU1D pinIotaLhsTy

/-- PIN: DT-010T's ι arm consumed at the same redex. -/
theorem pin_DT010T_iota :
    ∃ B, Nonempty (HasTyT natEnvU 1 [] (iotaRhsOf wSuccU1) B) ∧
      Nonempty (TyConvT natEnvU 1 [] (.const 0 []) B) :=
  DT010T_one_step_subject_reduction natEnvUWfT natEnvUWfT_inScope CtxWfT.nil
    pinIotaLhsTy (Step.iota [] _ _ (DerivedIota.of wSuccU1))

/-! ### the census pin -/

/-- the eight (carrier, counterpart) pairs this arc owns; segments iv/v land
    their counterparts in their own modules beside their own carriers. -/
def o2sCounterpartCensus : List (String × String) :=
  [("DT010_one_step_subject_reduction", "DT010T_one_step_subject_reduction"),
   ("DT011_multi_step_subject_reduction", "DT011T_multi_step_subject_reduction"),
   ("DT012_type_uniqueness", "DT012T_type_uniqueness"),
   ("DT021_no_cumulativity", "DT021T_no_cumulativity"),
   ("iotaPreserve", "iotaPreserveT"),
   ("RM014_whnf_typed", "RM014T_whnf_typed (RcicMachineSoundTyped)"),
   ("RM017_join_typed", "RM017T_join_typed (RcicMachineSoundTyped)"),
    ("parRedSR", "parRedSRT — SEALED under R-1″: levelsIn carries the three-site content rule (consts target list + the iotaSpine witness lists w2.ls/w2.lsC), supply step_to_parRed_levelsIn conditioned on the source typing (the typed source spine-inverts to bounded heads), the 13-arm mutual closed at every arm incl. iotaSpine (head moves at the predicate's bounds, iotaPreserveT via the scope bridge); both refutation theorems kept as true theorems on the preserved consts-only levelsInR1; RcicParRedSRTyped R-1″ record")]

theorem pin_o2s_census : o2sCounterpartCensus.length = 8 := rfl

end Rcic.Declarative

#print axioms Rcic.Declarative.levelBounded_zero_any
#print axioms Rcic.Declarative.levelsBounded_zero_any
#print axioms Rcic.Declarative.lookupType_lt_length
#print axioms Rcic.Declarative.lookupValue_lt_length
#print axioms Rcic.Declarative.lookupType_append_lt
#print axioms Rcic.Declarative.lookupValue_append_lt
#print axioms Rcic.Declarative.hasTyT_relocate
#print axioms Rcic.Declarative.convT_relocate
#print axioms Rcic.Declarative.hasTyTInv_bvar
#print axioms Rcic.Declarative.hasTyTInv_const
#print axioms Rcic.Declarative.hasTyTInv_lit
#print axioms Rcic.Declarative.ctxWfTLookupValueAt
#print axioms Rcic.Declarative.envWfT_bodyTypedWalk
#print axioms Rcic.Declarative.envWfT_bodyTypedRaw
#print axioms Rcic.Declarative.envWfT_bodyTyped
#print axioms Rcic.Declarative.DT021T_no_cumulativity
#print axioms Rcic.Declarative.DT012T_type_uniqueness
#print axioms Rcic.Declarative.iotaPreserveT
#print axioms Rcic.Declarative.iotaPreserveTT
#print axioms Rcic.Declarative.oneStepSRT
#print axioms Rcic.Declarative.DT010T_one_step_subject_reduction
#print axioms Rcic.Declarative.DT011T_multi_step_subject_reduction
#print axioms Rcic.Declarative.pin_DT010T_beta
#print axioms Rcic.Declarative.pinDefEnvUWfT
#print axioms Rcic.Declarative.pin_DT010T_delta
#print axioms Rcic.Declarative.wSuccU1
#print axioms Rcic.Declarative.pinIotaLhsTy
#print axioms Rcic.Declarative.pin_iotaPreserveT
#print axioms Rcic.Declarative.pin_iotaPreserveTT
#print axioms Rcic.Declarative.pin_DT010T_iota
#print axioms Rcic.Declarative.pin_o2s_census
