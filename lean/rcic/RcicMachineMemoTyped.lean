import rcic.RcicCertEmit
import Std.Data.HashMap.Lemmas

/-!
# RcicMachineMemoTyped — the derivation-carrying cert machine, memoized, proved equal

`certStep` (RcicCertKernel) runs the typed conversion `convAt?` / `tyConv?`
(RcicTypedConv). On δ-duplicating inputs it re-derives the same conversion many
times: `convAt? (fuel+1)` on `d_k ≡ d'_k` reaches `d_{k-1} ≡ d'_{k-1}` twice by
application congruence, so the call count doubles per level (a2 at n = 16:
5.5 M calls). This module threads a table through the same computation.

* `TTable` — a `Std.HashMap` from a structural hash to a bucket of entries; an
  entry is a key `(fuel, Γ, A, B)` / `(fuel, Γ, a, b, T)` with the derivation
  the original returned there. The hash only picks the bucket; a hit is decided
  by `decide` on the whole key, so a collision can never produce a hit.
* THE FUEL IS IN THE KEY, for successes and refusals alike. The typed machine is
  not monotone in fuel in either direction (`cex_tyConv_*`, `cex_certConvS_*`
  below: `converted` at budget 3 and 4, `refused` at 5..8, `converted` again at
  9). Reusing a success at a larger fuel, or a refusal at another fuel, would
  change the verdict; both rules are refuted by those pins and not used.
* `TTable.Sound t` — every entry is the original at its own key.
* `Agrees m v` — from every sound table, `m` returns `v` and leaves a sound
  table. Each memoized function agrees with its original (`*M_agrees`), and the
  memoized entries are equal to the originals outright
  (`certStepMemo_eq`, `certConvSMemo_eq`, `certWhnfSMemo_eq`,
  `certTyConvSMemo_eq`): the same `CertResult`, derivation included.

closure_claim 0; axioms within {propext, Quot.sound}.
-/

namespace Rcic.Machine.TMemo

open Rcic.Declarative Rcic.Machine

/-! ## structural hashes (performance only; no theorem depends on them) -/

def hLevel : Level → UInt64
  | .zero => 11
  | .succ l => mixHash 13 (hLevel l)
  | .max a b => mixHash 17 (mixHash (hLevel a) (hLevel b))
  | .imax a b => mixHash 19 (mixHash (hLevel a) (hLevel b))
  | .param i => mixHash 23 (hash i)

def hExpr : Expr Nat → UInt64
  | .bvar i => mixHash 31 (hash i)
  | .sort l => mixHash 37 (hLevel l)
  | .const r ls => mixHash 41 (ls.foldl (fun acc l => mixHash acc (hLevel l)) (hash r))
  | .app f x => mixHash 43 (mixHash (hExpr f) (hExpr x))
  | .lam a b => mixHash 47 (mixHash (hExpr a) (hExpr b))
  | .pi a b => mixHash 53 (mixHash (hExpr a) (hExpr b))
  | .letE a v b => mixHash 59 (mixHash (hExpr a) (mixHash (hExpr v) (hExpr b)))
  | .lit t => mixHash 61 (hash t)

def hDecl : LocalDecl → UInt64
  | .assumption a => mixHash 67 (hExpr a)
  | .letBinding a v => mixHash 71 (mixHash (hExpr a) (hExpr v))

def hCtx (Γ : LCtx) : UInt64 := Γ.foldl (fun acc d => mixHash acc (hDecl d)) 73

def keyTy (fuel : Nat) (Γ : LCtx) (A B : Expr Nat) : UInt64 :=
  mixHash 1 (mixHash (hash fuel) (mixHash (hCtx Γ) (mixHash (hExpr A) (hExpr B))))

def keyAt (fuel : Nat) (Γ : LCtx) (a b T : Expr Nat) : UInt64 :=
  mixHash 2 (mixHash (hash fuel) (mixHash (hCtx Γ)
    (mixHash (hExpr a) (mixHash (hExpr b) (hExpr T)))))

/-! ## the table -/

/-- a recorded answer of `tyConv?` / `convAt?` at its key (fuel included) -/
inductive TEntry (E : ResolvedEnv) (n : Nat) : Type
  | ty (fuel : Nat) (Γ : LCtx) (A B : Expr Nat) (r : Option (TyConvT E n Γ A B))
  | at (fuel : Nat) (Γ : LCtx) (a b T : Expr Nat) (r : Option (ConvT E n Γ a b T))

/-- an entry is sound iff it is the original's answer at its key -/
def TEntry.Sound {E : ResolvedEnv} {n : Nat} : TEntry E n → Prop
  | .ty f Γ A B r => r = tyConv? E n f Γ A B
  | .at f Γ a b T r => r = convAt? E n f Γ a b T

structure TTable (E : ResolvedEnv) (n : Nat) where
  map : Std.HashMap UInt64 (List (TEntry E n))

def TTable.empty (E : ResolvedEnv) (n : Nat) : TTable E n := ⟨{}⟩

def TTable.Sound {E : ResolvedEnv} {n : Nat} (t : TTable E n) : Prop :=
  ∀ (h : UInt64) (l : List (TEntry E n)), t.map[h]? = some l → ∀ e ∈ l, e.Sound

def TTable.bucket {E : ResolvedEnv} {n : Nat} (t : TTable E n) (k : UInt64) : List (TEntry E n) :=
  t.map[k]?.getD []

def TTable.push {E : ResolvedEnv} {n : Nat} (t : TTable E n) (k : UInt64) (e : TEntry E n) :
    TTable E n :=
  ⟨t.map.insert k (e :: t.bucket k)⟩

theorem TTable.empty_sound (E : ResolvedEnv) (n : Nat) : (TTable.empty E n).Sound := by
  intro h l hl
  simp [TTable.empty] at hl

theorem TTable.bucket_sound {E : ResolvedEnv} {n : Nat} {t : TTable E n} (ht : t.Sound)
    (k : UInt64) : ∀ e ∈ t.bucket k, e.Sound := by
  unfold TTable.bucket
  cases hk : t.map[k]? with
  | none => simp
  | some l => exact ht k l hk

theorem TTable.push_sound {E : ResolvedEnv} {n : Nat} {t : TTable E n} (ht : t.Sound)
    (k : UInt64) {e : TEntry E n} (he : e.Sound) : (t.push k e).Sound := by
  intro h l hl
  simp only [TTable.push, Std.HashMap.getElem?_insert] at hl
  split at hl
  · cases hl
    intro e' he'
    cases List.mem_cons.mp he' with
    | inl h' => exact h' ▸ he
    | inr h' => exact TTable.bucket_sound ht k e' h'
  · exact ht h l hl

abbrev TM (E : ResolvedEnv) (n : Nat) := StateM (TTable E n)

/-- `m` returns `v` from every sound table and leaves a sound table -/
def Agrees {E : ResolvedEnv} {n : Nat} {α : Type} (m : TM E n α) (v : α) : Prop :=
  ∀ t : TTable E n, t.Sound → (m.run t).1 = v ∧ (m.run t).2.Sound

theorem Agrees.pure' {E : ResolvedEnv} {n : Nat} {α : Type} (v : α) :
    Agrees (pure v : TM E n α) v :=
  fun _ ht => ⟨rfl, ht⟩

theorem Agrees.bind {E : ResolvedEnv} {n : Nat} {α β : Type} {m : TM E n α} {k : α → TM E n β}
    {v : α} {w : β} (hm : Agrees m v) (hk : Agrees (k v) w) : Agrees (m >>= k) w := by
  intro t ht
  obtain ⟨h1, h2⟩ := hm t ht
  have e : (m >>= k).run t = (k (m.run t).1).run (m.run t).2 := rfl
  rw [e, h1]
  exact hk _ h2

theorem Agrees.of_eq {E : ResolvedEnv} {n : Nat} {α : Type} {m : TM E n α} {v w : α}
    (hm : Agrees m v) (h : v = w) : Agrees m w := h ▸ hm

/-! ## lookup -/

def castTy {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx} {A A' B B' : Expr Nat} :
    Γ' = Γ → A' = A → B' = B → Option (TyConvT E n Γ' A' B') → Option (TyConvT E n Γ A B)
  | rfl, rfl, rfl, r => r

def castAt {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx} {a a' b b' T T' : Expr Nat} :
    Γ' = Γ → a' = a → b' = b → T' = T → Option (ConvT E n Γ' a' b' T') →
      Option (ConvT E n Γ a b T)
  | rfl, rfl, rfl, rfl, r => r

def findTy {E : ResolvedEnv} {n : Nat} (f : Nat) (Γ : LCtx) (A B : Expr Nat) :
    List (TEntry E n) → Option (Option (TyConvT E n Γ A B))
  | [] => none
  | .ty f' Γ' A' B' r :: es =>
      if h : f' = f ∧ Γ' = Γ ∧ A' = A ∧ B' = B then some (castTy h.2.1 h.2.2.1 h.2.2.2 r)
      else findTy f Γ A B es
  | .at .. :: es => findTy f Γ A B es

def findAt {E : ResolvedEnv} {n : Nat} (f : Nat) (Γ : LCtx) (a b T : Expr Nat) :
    List (TEntry E n) → Option (Option (ConvT E n Γ a b T))
  | [] => none
  | .at f' Γ' a' b' T' r :: es =>
      if h : f' = f ∧ Γ' = Γ ∧ a' = a ∧ b' = b ∧ T' = T then
        some (castAt h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 r)
      else findAt f Γ a b T es
  | .ty .. :: es => findAt f Γ a b T es

theorem findTy_sound {E : ResolvedEnv} {n : Nat} {f : Nat} {Γ : LCtx} {A B : Expr Nat} :
    ∀ {l : List (TEntry E n)} {r}, (∀ e ∈ l, e.Sound) → findTy f Γ A B l = some r →
      r = tyConv? E n f Γ A B
  | [], _, _, h => by simp [findTy] at h
  | .ty f' Γ' A' B' r' :: es, r, hs, h => by
      simp only [findTy] at h
      split at h
      · rename_i hk
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hk
        cases h
        exact hs _ (List.mem_cons_self _ _)
      · exact findTy_sound (fun e he => hs e (List.mem_cons_of_mem _ he)) h
  | .at .. :: es, r, hs, h => by
      simp only [findTy] at h
      exact findTy_sound (fun e he => hs e (List.mem_cons_of_mem _ he)) h

theorem findAt_sound {E : ResolvedEnv} {n : Nat} {f : Nat} {Γ : LCtx} {a b T : Expr Nat} :
    ∀ {l : List (TEntry E n)} {r}, (∀ e ∈ l, e.Sound) → findAt f Γ a b T l = some r →
      r = convAt? E n f Γ a b T
  | [], _, _, h => by simp [findAt] at h
  | .at f' Γ' a' b' T' r' :: es, r, hs, h => by
      simp only [findAt] at h
      split at h
      · rename_i hk
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hk
        cases h
        exact hs _ (List.mem_cons_self _ _)
      · exact findAt_sound (fun e he => hs e (List.mem_cons_of_mem _ he)) h
  | .ty .. :: es, r, hs, h => by
      simp only [findAt] at h
      exact findAt_sound (fun e he => hs e (List.mem_cons_of_mem _ he)) h

/-! ## the memo wrappers: a hit returns the recorded answer; a miss runs the
    thunk and records it at its own key -/

def memoTy {E : ResolvedEnv} {n : Nat} (f : Nat) (Γ : LCtx) (A B : Expr Nat)
    (body : Unit → TM E n (Option (TyConvT E n Γ A B))) : TM E n (Option (TyConvT E n Γ A B)) :=
  fun t =>
    let k := keyTy f Γ A B
    match findTy f Γ A B (t.bucket k) with
    | some r => (r, t)
    | none =>
        let p := (body ()).run t
        (p.1, p.2.push k (.ty f Γ A B p.1))

def memoAt {E : ResolvedEnv} {n : Nat} (f : Nat) (Γ : LCtx) (a b T : Expr Nat)
    (body : Unit → TM E n (Option (ConvT E n Γ a b T))) : TM E n (Option (ConvT E n Γ a b T)) :=
  fun t =>
    let k := keyAt f Γ a b T
    match findAt f Γ a b T (t.bucket k) with
    | some r => (r, t)
    | none =>
        let p := (body ()).run t
        (p.1, p.2.push k (.at f Γ a b T p.1))

theorem memoTy_agrees {E : ResolvedEnv} {n : Nat} {f : Nat} {Γ : LCtx} {A B : Expr Nat}
    {body : Unit → TM E n (Option (TyConvT E n Γ A B))}
    (hb : Agrees (body ()) (tyConv? E n f Γ A B)) :
    Agrees (memoTy f Γ A B body) (tyConv? E n f Γ A B) := by
  intro t ht
  show (memoTy f Γ A B body t).1 = _ ∧ (memoTy f Γ A B body t).2.Sound
  unfold memoTy
  simp only
  split
  · rename_i r hr
    exact ⟨findTy_sound (TTable.bucket_sound ht _) hr, ht⟩
  · obtain ⟨h1, h2⟩ := hb t ht
    refine ⟨h1, TTable.push_sound h2 _ ?_⟩
    exact h1

theorem memoAt_agrees {E : ResolvedEnv} {n : Nat} {f : Nat} {Γ : LCtx} {a b T : Expr Nat}
    {body : Unit → TM E n (Option (ConvT E n Γ a b T))}
    (hb : Agrees (body ()) (convAt? E n f Γ a b T)) :
    Agrees (memoAt f Γ a b T body) (convAt? E n f Γ a b T) := by
  intro t ht
  show (memoAt f Γ a b T body t).1 = _ ∧ (memoAt f Γ a b T body t).2.Sound
  unfold memoAt
  simp only
  split
  · rename_i r hr
    exact ⟨findAt_sound (TTable.bucket_sound ht _) hr, ht⟩
  · obtain ⟨h1, h2⟩ := hb t ht
    refine ⟨h1, TTable.push_sound h2 _ ?_⟩
    exact h1

/-! ## the checker's rules over a table-threading conversion -/

abbrev CVM (E : ResolvedEnv) (n : Nat) :=
  (Γ : LCtx) → (A B : Expr Nat) → TM E n (Option (TyConvT E n Γ A B))
abbrev CAM (E : ResolvedEnv) (n : Nat) :=
  (Γ : LCtx) → (a b T : Expr Nat) → TM E n (Option (ConvT E n Γ a b T))

/-- `convM` implements `conv` -/
def CVImpl {E : ResolvedEnv} {n : Nat} (convM : CVM E n)
    (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)) : Prop :=
  ∀ Γ A B, Agrees (convM Γ A B) (conv Γ A B)

def CAImpl {E : ResolvedEnv} {n : Nat} (convAtM : CAM E n)
    (convAt : (Γ : LCtx) → (a b T : Expr Nat) → Option (ConvT E n Γ a b T)) : Prop :=
  ∀ Γ a b T, Agrees (convAtM Γ a b T) (convAt Γ a b T)

/-- `checkWith` (RcicTypedConv) over `convM` -/
def checkWithM (E : ResolvedEnv) (n fuel : Nat) (conv : CVM E n) :
    (Γ : LCtx) → (e : Expr Nat) → TM E n (Option (Σ T, HasTyT E n Γ e T))
  | Γ, .sort l => pure (some ⟨_, .sort Γ l⟩)
  | Γ, .bvar i => pure (match h : lookupType Γ i with
      | some A => some ⟨A, .bvar Γ i A h⟩
      | none => none)
  | Γ, .const r ls => pure (checkConstT E n Γ r ls)
  | Γ, .pi A B => do
      let r1 ← checkWithM E n fuel conv Γ A
      let r2 ← checkWithM E n fuel conv (.assumption A :: Γ) B
      pure (match r1, r2 with
        | some ⟨TA, dA⟩, some ⟨TB, dB⟩ =>
            match toSort? E n fuel Γ TA, toSort? E n fuel (.assumption A :: Γ) TB with
            | some ⟨u, cA⟩, some ⟨v, cB⟩ =>
                some ⟨_, .pi Γ A u B v (hasTyT_of_tyConv dA cA) (hasTyT_of_tyConv dB cB)⟩
            | _, _ => none
        | _, _ => none)
  | Γ, .lam A b => do
      let r1 ← checkWithM E n fuel conv Γ A
      let r2 ← checkWithM E n fuel conv (.assumption A :: Γ) b
      pure (match r1, r2 with
        | some ⟨TA, dA⟩, some ⟨B, db⟩ =>
            match toSort? E n fuel Γ TA with
            | some ⟨u, cA⟩ => some ⟨_, .lam Γ A u b B (hasTyT_of_tyConv dA cA) db⟩
            | none => none
        | _, _ => none)
  | Γ, .app f a => do
      let r1 ← checkWithM E n fuel conv Γ f
      let r2 ← checkWithM E n fuel conv Γ a
      match r1, r2 with
      | some ⟨Tf, df⟩, some ⟨Ta, da⟩ =>
          match toPi? E n fuel Γ Tf with
          | some ⟨A, B, cf⟩ => do
              let ca ← conv Γ Ta A
              pure (match ca with
                | some ca => some ⟨_, .app Γ f a A B (hasTyT_of_tyConv df cf) (hasTyT_of_tyConv da ca)⟩
                | none => none)
          | none => pure none
      | _, _ => pure none
  | Γ, .letE A v b => do
      let r1 ← checkWithM E n fuel conv Γ A
      let r2 ← checkWithM E n fuel conv Γ v
      let r3 ← checkWithM E n fuel conv (.letBinding A v :: Γ) b
      match r1, r2, r3 with
      | some ⟨TA, dA⟩, some ⟨Tv, dv⟩, some ⟨B, db⟩ => do
          let cv ← conv Γ Tv A
          pure (match toSort? E n fuel Γ TA, cv with
            | some ⟨u, cA⟩, some cv =>
                some ⟨_, .letE Γ A u v B b (hasTyT_of_tyConv dA cA) (hasTyT_of_tyConv dv cv) db⟩
            | _, _ => none)
      | _, _, _ => pure none
  | Γ, .lit t => pure ((checkLitT E n Γ t).map fun p => ⟨p.1, .lit Γ t p.1 p.2⟩)

theorem checkWithM_agrees {E : ResolvedEnv} {n fuel : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) :
    ∀ (Γ : LCtx) (e : Expr Nat), Agrees (checkWithM E n fuel convM Γ e) (checkWith E n fuel conv Γ e)
  | Γ, .sort l => by rw [checkWithM, checkWith]; exact Agrees.pure' _
  | Γ, .bvar i => by rw [checkWithM, checkWith]; exact Agrees.pure' _
  | Γ, .const r ls => by rw [checkWithM, checkWith]; exact Agrees.pure' _
  | Γ, .pi A B => by
      rw [checkWithM, checkWith]
      refine Agrees.bind (checkWithM_agrees hc Γ A) ?_
      refine Agrees.bind (checkWithM_agrees hc _ B) ?_
      exact Agrees.pure' _
  | Γ, .lam A b => by
      rw [checkWithM, checkWith]
      refine Agrees.bind (checkWithM_agrees hc Γ A) ?_
      refine Agrees.bind (checkWithM_agrees hc _ b) ?_
      exact Agrees.pure' _
  | Γ, .app f a => by
      rw [checkWithM, checkWith]
      refine Agrees.bind (checkWithM_agrees hc Γ f) ?_
      refine Agrees.bind (checkWithM_agrees hc Γ a) ?_
      generalize checkWith E n fuel conv Γ f = r1
      generalize checkWith E n fuel conv Γ a = r2
      rcases r1 with _ | ⟨Tf, df⟩ <;> rcases r2 with _ | ⟨Ta, da⟩ <;> try exact Agrees.pure' _
      dsimp only
      generalize toPi? E n fuel Γ Tf = p
      rcases p with _ | ⟨A, B, cf⟩
      · exact Agrees.pure' _
      · exact Agrees.bind (hc Γ Ta A) (Agrees.pure' _)
  | Γ, .letE A v b => by
      rw [checkWithM, checkWith]
      refine Agrees.bind (checkWithM_agrees hc Γ A) ?_
      refine Agrees.bind (checkWithM_agrees hc Γ v) ?_
      refine Agrees.bind (checkWithM_agrees hc _ b) ?_
      generalize checkWith E n fuel conv Γ A = r1
      generalize checkWith E n fuel conv Γ v = r2
      generalize checkWith E n fuel conv (.letBinding A v :: Γ) b = r3
      rcases r1 with _ | ⟨TA, dA⟩ <;> rcases r2 with _ | ⟨Tv, dv⟩ <;>
        rcases r3 with _ | ⟨B, db⟩ <;> try exact Agrees.pure' _
      dsimp only
      exact Agrees.bind (hc Γ Tv A) (Agrees.pure' _)
  | Γ, .lit t => by rw [checkWithM, checkWith]; exact Agrees.pure' _

/-- `tyAtWith` over `convM` -/
def tyAtWithM (E : ResolvedEnv) (n fuel : Nat) (conv : CVM E n) (Γ : LCtx) (e T : Expr Nat) :
    TM E n (Option (HasTyT E n Γ e T)) := do
  match ← checkWithM E n fuel conv Γ e with
  | some ⟨T', d⟩ => do
      let c ← conv Γ T' T
      pure (c.map (hasTyT_of_tyConv d))
  | none => pure none

theorem tyAtWithM_agrees {E : ResolvedEnv} {n fuel : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) (Γ : LCtx) (e T : Expr Nat) :
    Agrees (tyAtWithM E n fuel convM Γ e T) (tyAtWith E n fuel conv Γ e T) := by
  unfold tyAtWithM tyAtWith
  refine Agrees.bind (checkWithM_agrees hc Γ e) ?_
  generalize checkWith E n fuel conv Γ e = r
  rcases r with _ | ⟨T', d⟩
  · exact Agrees.pure' _
  · exact Agrees.bind (hc Γ T' T) (Agrees.pure' _)

/-- `stepAt?` over `convM` -/
def stepAtM (E : ResolvedEnv) (n : Nat) (conv : CVM E n) (Γ : LCtx) (e T : Expr Nat) :
    TM E n (Option (Σ e', ConvT E n Γ e e' T)) :=
  match headStep? E n Γ (appsSpine e).1 (appsSpine e).2 with
  | some ⟨U, e', c⟩ => do
      let cU ← conv Γ U T
      pure (cU.map fun cU => ⟨e', convT_of_tyConv (foldApps_appsSpine e ▸ c) cU⟩)
  | none => pure none

theorem stepAtM_agrees {E : ResolvedEnv} {n : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) (Γ : LCtx) (e T : Expr Nat) :
    Agrees (stepAtM E n convM Γ e T) (stepAt? E n conv Γ e T) := by
  unfold stepAtM stepAt?
  generalize headStep? E n Γ (appsSpine e).1 (appsSpine e).2 = r
  rcases r with _ | ⟨U, e', c⟩
  · exact Agrees.pure' _
  · exact Agrees.bind (hc Γ U T) (Agrees.pure' _)

/-- `appConvWith` over `convM` / `convAtM` -/
def appConvWithM (E : ResolvedEnv) (n fuel : Nat) (conv : CVM E n) (convAt : CAM E n)
    (Γ : LCtx) (f a g b : Expr Nat) : TM E n (Option (Σ U, ConvT E n Γ (.app f a) (.app g b) U)) := do
  match ← checkWithM E n fuel conv Γ f with
  | some ⟨Tf, _⟩ =>
      match toPi? E n fuel Γ Tf with
      | some ⟨A, B, _⟩ => do
          let c₁ ← convAt Γ f g (.pi A B)
          let c₂ ← convAt Γ a b A
          pure (match c₁, c₂ with
            | some c₁, some c₂ => some ⟨_, .app Γ f g a b A B c₁ c₂⟩
            | _, _ => none)
      | none => pure none
  | none => pure none

theorem appConvWithM_agrees {E : ResolvedEnv} {n fuel : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    {convAtM : CAM E n} {convAt : (Γ : LCtx) → (a b T : Expr Nat) → Option (ConvT E n Γ a b T)}
    (hc : CVImpl convM conv) (ha : CAImpl convAtM convAt) (Γ : LCtx) (f a g b : Expr Nat) :
    Agrees (appConvWithM E n fuel convM convAtM Γ f a g b) (appConvWith E n fuel conv convAt Γ f a g b) := by
  unfold appConvWithM appConvWith
  refine Agrees.bind (checkWithM_agrees hc Γ f) ?_
  generalize checkWith E n fuel conv Γ f = r
  rcases r with _ | ⟨Tf, _⟩
  · exact Agrees.pure' _
  · dsimp only
    generalize toPi? E n fuel Γ Tf = p
    rcases p with _ | ⟨A, B, _⟩
    · exact Agrees.pure' _
    · exact Agrees.bind (ha Γ f g _) (Agrees.bind (ha Γ a b A) (Agrees.pure' _))

/-- `litAt?` over `convM` -/
def litAtM (E : ResolvedEnv) (n : Nat) (conv : CVM E n) (Γ : LCtx) (t : Nat) (T : Expr Nat) :
    TM E n (Option (ConvT E n Γ (.lit t) (natExpand t) T)) :=
  match checkLitT E n Γ t with
  | some ⟨U, hexp⟩ => do
      let c ← conv Γ U T
      pure (c.map (convT_of_tyConv (.lit Γ t _ U (.of t) hexp)))
  | none => pure none

theorem litAtM_agrees {E : ResolvedEnv} {n : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) (Γ : LCtx) (t : Nat) (T : Expr Nat) :
    Agrees (litAtM E n convM Γ t T) (litAt? E n conv Γ t T) := by
  unfold litAtM litAt?
  generalize checkLitT E n Γ t = r
  rcases r with _ | ⟨U, hexp⟩
  · exact Agrees.pure' _
  · exact Agrees.bind (hc Γ U T) (Agrees.pure' _)

/-- `irrAt?` over `convM` (the two premises are only computed when `P : Sort 0`) -/
def irrAtM (E : ResolvedEnv) (n fuel : Nat) (conv : CVM E n) (Γ : LCtx) (p q P : Expr Nat) :
    TM E n (Option (ConvT E n Γ p q P)) := do
  match ← tyAtWithM E n fuel conv Γ P (.sort .zero) with
  | some hP => do
      let hp ← tyAtWithM E n fuel conv Γ p P
      let hq ← tyAtWithM E n fuel conv Γ q P
      pure (match hp, hq with
        | some hp, some hq => some (.irr Γ P p q hP hp hq)
        | _, _ => none)
  | none => pure none

theorem irrAtM_agrees {E : ResolvedEnv} {n fuel : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) (Γ : LCtx) (p q P : Expr Nat) :
    Agrees (irrAtM E n fuel convM Γ p q P) (irrAt? E n fuel conv Γ p q P) := by
  unfold irrAtM irrAt?
  refine Agrees.bind (tyAtWithM_agrees hc Γ P _) ?_
  generalize tyAtWith E n fuel conv Γ P (.sort .zero) = r
  rcases r with _ | hP
  · exact Agrees.pure' _
  · exact Agrees.bind (tyAtWithM_agrees hc Γ p P)
      (Agrees.bind (tyAtWithM_agrees hc Γ q P) (Agrees.pure' _))

/-- `liftSpineWith` over `convM` -/
def liftSpineWithM (E : ResolvedEnv) (n fuel : Nat) (conv : CVM E n) (Γ : LCtx) :
    (f g T : Expr Nat) → ConvT E n Γ f g T → (args : List (Expr Nat)) →
    TM E n (Option (Σ T', ConvT E n Γ (foldApps f args) (foldApps g args) T'))
  | _, _, T, c, [] => pure (some ⟨T, c⟩)
  | f, g, .pi A B, c, a :: as => do
      match ← tyAtWithM E n fuel conv Γ a A with
      | some ha =>
          liftSpineWithM E n fuel conv Γ (.app f a) (.app g a) (instantiate0 a B)
            (.app Γ f g a a A B c (.refl Γ a A ha)) as
      | none => pure none
  | _, _, _, _, _ :: _ => pure none

theorem liftSpineWithM_agrees {E : ResolvedEnv} {n fuel : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) (Γ : LCtx) :
    ∀ (f g T : Expr Nat) (c : ConvT E n Γ f g T) (args : List (Expr Nat)),
      Agrees (liftSpineWithM E n fuel convM Γ f g T c args) (liftSpineWith E n fuel conv Γ f g T c args)
  | _, _, T, c, [] => by rw [liftSpineWithM, liftSpineWith]; exact Agrees.pure' _
  | f, g, .pi A B, c, a :: as => by
      rw [liftSpineWithM, liftSpineWith]
      refine Agrees.bind (tyAtWithM_agrees hc Γ a A) ?_
      generalize tyAtWith E n fuel conv Γ a A = r
      rcases r with _ | ha
      · exact Agrees.pure' _
      · exact liftSpineWithM_agrees hc Γ _ _ _ _ as
  | _, _, .bvar _, _, _ :: _ => Agrees.pure' _
  | _, _, .sort _, _, _ :: _ => Agrees.pure' _
  | _, _, .const _ _, _, _ :: _ => Agrees.pure' _
  | _, _, .app _ _, _, _ :: _ => Agrees.pure' _
  | _, _, .lam _ _, _, _ :: _ => Agrees.pure' _
  | _, _, .letE _ _ _, _, _ :: _ => Agrees.pure' _
  | _, _, .lit _, _, _ :: _ => Agrees.pure' _

/-- `betaStepWith?` over `convM` -/
def betaStepWithM (E : ResolvedEnv) (n fuel : Nat) (conv : CVM E n) (Γ : LCtx) (a : Expr Nat) :
    TM E n (Option (Σ U e', ConvT E n Γ a e' U)) :=
  match hs : appsSpine a with
  | (.lam A body, arg :: rest) => do
      let r1 ← checkWithM E n fuel conv Γ A
      let r2 ← checkWithM E n fuel conv (.assumption A :: Γ) body
      let r3 ← tyAtWithM E n fuel conv Γ arg A
      match r1, r2, r3 with
      | some ⟨.sort u, hA⟩, some ⟨B, hbody⟩, some harg => do
          let r ← liftSpineWithM E n fuel conv Γ _ _ _ (.beta Γ A body arg B u hA hbody harg) rest
          pure (r.map fun ⟨U, c⟩ => ⟨U, _, (foldApps_lam_spine hs).symm ▸ c⟩)
      | _, _, _ => pure none
  | _ => pure none

/-- `iotaStepWith?` over `convM` -/
def iotaStepWithM (E : ResolvedEnv) (n fuel : Nat) (conv : CVM E n) (Γ : LCtx) (a : Expr Nat) :
    TM E n (Option (Σ U e', ConvT E n Γ a e' U)) :=
  match iotaReductCert E a with
  | some ⟨w, hwl⟩ => do
      let r1 ← checkWithM E n fuel conv Γ a
      let r2 ← checkWithM E n fuel conv Γ (iotaRhsOf w)
      match r1, r2 with
      | some ⟨U, hl⟩, some ⟨U', hr⟩ => do
          let c ← conv Γ U' U
          pure (c.map fun cU'U => ⟨U, iotaRhsOf w,
            hwl ▸ ConvT.iota Γ (iotaLhsOf w) (iotaRhsOf w) U (DerivedIota.of w)
              (hwl.symm ▸ hl) (hasTyT_of_tyConv hr cU'U)⟩)
      | _, _ => pure none
  | none => pure none

theorem iotaStepWithM_agrees {E : ResolvedEnv} {n fuel : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) (Γ : LCtx) (a : Expr Nat) :
    Agrees (iotaStepWithM E n fuel convM Γ a) (iotaStepWith? E n fuel conv Γ a) := by
  unfold iotaStepWithM iotaStepWith?
  generalize iotaReductCert E a = r
  rcases r with _ | ⟨w, hwl⟩
  · exact Agrees.pure' _
  · dsimp only
    refine Agrees.bind (checkWithM_agrees hc Γ a) ?_
    refine Agrees.bind (checkWithM_agrees hc Γ _) ?_
    generalize checkWith E n fuel conv Γ a = r1
    generalize checkWith E n fuel conv Γ (iotaRhsOf w) = r2
    rcases r1 with _ | ⟨U, hl⟩ <;> rcases r2 with _ | ⟨U', hr⟩ <;> try exact Agrees.pure' _
    exact Agrees.bind (hc Γ U' U) (Agrees.pure' _)

theorem betaStepWithM_agrees {E : ResolvedEnv} {n fuel : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) (Γ : LCtx) (a : Expr Nat) :
    Agrees (betaStepWithM E n fuel convM Γ a) (betaStepWith? E n fuel conv Γ a) := by
  unfold betaStepWithM betaStepWith?
  split
  · rename_i A body arg rest hs
    split
    · rename_i A' body' arg' rest' hs'
      rw [hs] at hs'
      cases hs'
      refine Agrees.bind (checkWithM_agrees hc Γ A) ?_
      refine Agrees.bind (checkWithM_agrees hc _ body) ?_
      refine Agrees.bind (tyAtWithM_agrees hc Γ arg A) ?_
      generalize checkWith E n fuel conv Γ A = r1
      generalize checkWith E n fuel conv (.assumption A :: Γ) body = r2
      generalize tyAtWith E n fuel conv Γ arg A = r3
      rcases r1 with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _, hA⟩ <;>
        rcases r2 with _ | ⟨B, hbody⟩ <;> rcases r3 with _ | harg <;> try exact Agrees.pure' _
      exact Agrees.bind (liftSpineWithM_agrees hc Γ _ _ _ _ rest) (Agrees.pure' _)
    · rename_i hne
      exact absurd hs (hne _ _ _ _)
  · rename_i hne
    split
    · rename_i A' body' arg' rest' hs'
      exact absurd hs' (hne _ _ _ _)
    · exact Agrees.pure' _

/-- `iotaBetaStep?` over `convM` -/
def iotaBetaStepM (E : ResolvedEnv) (n fuel : Nat) (conv : CVM E n) (Γ : LCtx) (a : Expr Nat) :
    TM E n (Option (Σ U e', ConvT E n Γ a e' U)) := do
  match ← iotaStepWithM E n fuel conv Γ a with
  | some s => pure (some s)
  | none => betaStepWithM E n fuel conv Γ a

theorem iotaBetaStepM_agrees {E : ResolvedEnv} {n fuel : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) (Γ : LCtx) (a : Expr Nat) :
    Agrees (iotaBetaStepM E n fuel convM Γ a) (iotaBetaStep? E n fuel conv Γ a) := by
  unfold iotaBetaStepM iotaBetaStep?
  refine Agrees.bind (iotaStepWithM_agrees hc Γ a) ?_
  generalize iotaStepWith? E n fuel conv Γ a = r
  rcases r with _ | s
  · exact betaStepWithM_agrees hc Γ a
  · exact Agrees.pure' _

/-- `iotaMid?`'s inner `step?`, restated as a definition -/
def iotaMidStepP (E : ResolvedEnv) (n fuel : Nat)
    (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
    (Γ : LCtx) (a : Expr Nat) : Option (Σ' u e', ConvT E n Γ a e' (.sort u)) :=
  match iotaBetaStep? E n fuel conv Γ a with
  | some ⟨U, a', c⟩ => (toSort? E n fuel Γ U).map fun ⟨u, cU⟩ => ⟨u, a', convT_of_tyConv c cU⟩
  | none => none

theorem iotaMid?_eq (E : ResolvedEnv) (n fuel : Nat)
    (conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
    (Γ : LCtx) (rA rB : Expr Nat) :
    iotaMid? E n fuel conv Γ rA rB =
      match iotaMidStepP E n fuel conv Γ rA, iotaMidStepP E n fuel conv Γ rB with
      | some ⟨u, a', c⟩, _ =>
          (conv Γ a' rB).map fun d => .trans Γ rA a' rB (.of Γ rA a' u c) d
      | none, some ⟨u, b', c⟩ =>
          (conv Γ rA b').map fun d =>
            .trans Γ rA b' rB d (.of Γ b' rB u (ConvT.symm Γ rB b' (.sort u) c))
      | none, none => none := rfl

def iotaMidStepM (E : ResolvedEnv) (n fuel : Nat) (conv : CVM E n) (Γ : LCtx) (a : Expr Nat) :
    TM E n (Option (Σ' u e', ConvT E n Γ a e' (.sort u))) := do
  match ← iotaBetaStepM E n fuel conv Γ a with
  | some ⟨U, a', c⟩ =>
      pure ((toSort? E n fuel Γ U).map fun ⟨u, cU⟩ => ⟨u, a', convT_of_tyConv c cU⟩)
  | none => pure none

theorem iotaMidStepM_agrees {E : ResolvedEnv} {n fuel : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) (Γ : LCtx) (a : Expr Nat) :
    Agrees (iotaMidStepM E n fuel convM Γ a) (iotaMidStepP E n fuel conv Γ a) := by
  unfold iotaMidStepM iotaMidStepP
  refine Agrees.bind (iotaBetaStepM_agrees hc Γ a) ?_
  generalize iotaBetaStep? E n fuel conv Γ a = r
  rcases r with _ | ⟨U, a', c⟩ <;> exact Agrees.pure' _

/-- `iotaMid?` over `convM` (the right side is only stepped when the left does not) -/
def iotaMidM (E : ResolvedEnv) (n fuel : Nat) (conv : CVM E n) (Γ : LCtx) (rA rB : Expr Nat) :
    TM E n (Option (TyConvT E n Γ rA rB)) := do
  match ← iotaMidStepM E n fuel conv Γ rA with
  | some ⟨u, a', c⟩ => do
      let d ← conv Γ a' rB
      pure (d.map fun d => .trans Γ rA a' rB (.of Γ rA a' u c) d)
  | none =>
      match ← iotaMidStepM E n fuel conv Γ rB with
      | some ⟨u, b', c⟩ => do
          let d ← conv Γ rA b'
          pure (d.map fun d => .trans Γ rA b' rB d (.of Γ b' rB u (ConvT.symm Γ rB b' (.sort u) c)))
      | none => pure none

theorem iotaMidM_agrees {E : ResolvedEnv} {n fuel : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) (Γ : LCtx) (rA rB : Expr Nat) :
    Agrees (iotaMidM E n fuel convM Γ rA rB) (iotaMid? E n fuel conv Γ rA rB) := by
  rw [iotaMid?_eq]
  unfold iotaMidM
  refine Agrees.bind (iotaMidStepM_agrees hc Γ rA) ?_
  generalize iotaMidStepP E n fuel conv Γ rA = sA
  rcases sA with _ | ⟨u, a', c⟩
  · dsimp only
    refine Agrees.bind (iotaMidStepM_agrees hc Γ rB) ?_
    generalize iotaMidStepP E n fuel conv Γ rB = sB
    rcases sB with _ | ⟨u, b', c⟩
    · exact Agrees.pure' _
    · exact Agrees.bind (hc Γ rA b') (Agrees.pure' _)
  · exact Agrees.bind (hc Γ a' rB) (Agrees.pure' _)

/-- `tyConv?.domChain` over `convM` -/
def domChainM (E : ResolvedEnv) (n fuel : Nat) (conv : CVM E n) (Γ : LCtx) (B : Expr Nat) :
    {A A' : Expr Nat} → TyConvT E n Γ A A' → TM E n (Option (TyConvT E n Γ (.pi A B) (.pi A' B)))
  | _, _, .refl _ A => pure (some (.refl Γ (.pi A B)))
  | _, _, .of _ X Y u c => do
      match ← checkWithM E n fuel conv (.assumption X :: Γ) B with
      | some ⟨TB, dB⟩ =>
          pure (match toSort? E n fuel (.assumption X :: Γ) TB with
            | some ⟨v, cBs⟩ =>
                some (.of Γ _ _ _
                  (.pi Γ X Y B B u v c
                    (.refl (.assumption X :: Γ) B (.sort v) (hasTyT_of_tyConv dB cBs))))
            | none => none)
      | _ => pure none
  | _, _, .trans _ _ _ _ c₁ c₂ => do
      let d₁ ← domChainM E n fuel conv Γ B c₁
      let d₂ ← domChainM E n fuel conv Γ B c₂
      pure (match d₁, d₂ with
        | some d₁, some d₂ => some (.trans Γ _ _ _ d₁ d₂)
        | _, _ => none)

theorem domChainM_agrees {E : ResolvedEnv} {n fuel : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) (Γ : LCtx) (B : Expr Nat) :
    ∀ {A A' : Expr Nat} (c : TyConvT E n Γ A A'),
      Agrees (domChainM E n fuel convM Γ B c) (tyConv?.domChain E n fuel conv Γ B c)
  | _, _, .refl _ A => by rw [domChainM, tyConv?.domChain]; exact Agrees.pure' _
  | _, _, .of _ X Y u c => by
      rw [domChainM, tyConv?.domChain]
      refine Agrees.bind (checkWithM_agrees hc _ B) ?_
      generalize checkWith E n fuel conv (.assumption X :: Γ) B = r
      rcases r with _ | ⟨TB, dB⟩ <;> exact Agrees.pure' _
  | _, _, .trans _ _ _ _ c₁ c₂ => by
      rw [domChainM, tyConv?.domChain]
      exact Agrees.bind (domChainM_agrees hc Γ B c₁)
        (Agrees.bind (domChainM_agrees hc Γ B c₂) (Agrees.pure' _))

/-- `tyConv?.piCongr?` over `convM` -/
def piCongrM (E : ResolvedEnv) (n fuel : Nat) (conv : CVM E n) (Γ : LCtx) (A₁ A₂ B₁ B₂ : Expr Nat)
    (cA : TyConvT E n Γ A₁ A₂) (cB : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) :
    TM E n (Option (TyConvT E n Γ (.pi A₁ B₁) (.pi A₂ B₂))) := do
  match ← checkWithM E n fuel conv Γ A₁ with
  | some ⟨TA₁, dA⟩ =>
      match toSort? E n fuel Γ TA₁ with
      | some ⟨u, cAs⟩ => do
          let c₂ ← domChainM E n fuel conv Γ B₂ cA
          pure (match tyConv?.codChain E n Γ A₁ u (hasTyT_of_tyConv dA cAs) cB, c₂ with
            | some c₁, some c₂ => some (.trans Γ _ _ _ c₁ c₂)
            | _, _ => none)
      | none => pure none
  | _ => pure none

theorem piCongrM_agrees {E : ResolvedEnv} {n fuel : Nat} {convM : CVM E n}
    {conv : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl convM conv) (Γ : LCtx) (A₁ A₂ B₁ B₂ : Expr Nat)
    (cA : TyConvT E n Γ A₁ A₂) (cB : TyConvT E n (.assumption A₁ :: Γ) B₁ B₂) :
    Agrees (piCongrM E n fuel convM Γ A₁ A₂ B₁ B₂ cA cB)
      (tyConv?.piCongr? E n fuel conv Γ A₁ A₂ B₁ B₂ cA cB) := by
  unfold piCongrM tyConv?.piCongr?
  refine Agrees.bind (checkWithM_agrees hc Γ A₁) ?_
  generalize checkWith E n fuel conv Γ A₁ = r
  rcases r with _ | ⟨TA₁, dA⟩
  · exact Agrees.pure' _
  · dsimp only
    generalize toSort? E n fuel Γ TA₁ = s
    rcases s with _ | ⟨u, cAs⟩
    · exact Agrees.pure' _
    · exact Agrees.bind (domChainM_agrees hc Γ B₂ cA) (Agrees.pure' _)

/-! ## the two levels restated with fuel-level callbacks (`rfl` / equation lemma) -/

section restate
variable (E : ResolvedEnv) (n fuel : Nat)
  (TC : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B))
  (CA : (Γ : LCtx) → (a b T : Expr Nat) → Option (ConvT E n Γ a b T))

/-- `tyConv?`'s `mid` at the whnf'ed sides -/
def tyMidP (Γ : LCtx) (X Y : Expr Nat) : Option (TyConvT E n Γ X Y) :=
  if h' : X = Y then some (h' ▸ .refl Γ X) else
  match X, Y with
  | .sort l₁, .sort l₂ =>
      if hl : decEqN l₁ l₂ = true then some (.of Γ _ _ _ (.sorts Γ l₁ l₂ (decEqN_sound l₁ l₂ hl)))
      else none
  | .pi A₁ B₁, .pi A₂ B₂ =>
      match TC Γ A₁ A₂, TC (.assumption A₁ :: Γ) B₁ B₂ with
      | some cA, some cB => tyConv?.piCongr? E n fuel TC Γ A₁ A₂ B₁ B₂ cA cB
      | _, _ => none
  | .app f a, .app g b =>
      match appConvWith E n fuel TC CA Γ f a g b with
      | some ⟨U, c⟩ => (toSort? E n fuel Γ U).map fun s => TyConvT.of Γ _ _ s.1 (convT_of_tyConv c s.2)
      | none => none
  | _, _ => none

/-- `tyConv? (fuel+1)` with the fuel-level calls as callbacks -/
def tyConvBodyP (Γ : LCtx) (A B : Expr Nat) : Option (TyConvT E n Γ A B) :=
  if h : A = B then some (h ▸ .refl Γ A) else
  let rA := whnfTy E n Γ (fuel + 1) A
  let rB := whnfTy E n Γ (fuel + 1) B
  let mid := match tyMidP E n fuel TC CA Γ rA.1 rB.1 with
    | some c => some c
    | none => iotaMid? E n fuel TC Γ rA.1 rB.1
  mid.map fun c => .trans Γ A rA.1 B rA.2 (.trans Γ rA.1 rB.1 B c rB.2.symmT)

/-- `convAt?`'s inner `step?` -/
def convStepP (Γ : LCtx) (T x : Expr Nat) : Option (Σ e', ConvT E n Γ x e' T) :=
  match iotaBetaStep? E n fuel TC Γ x with
  | some ⟨U, x', c⟩ => (TC Γ U T).map fun cU => ⟨x', convT_of_tyConv c cU⟩
  | none => none

/-- `convAt?`'s application / literal tail -/
def convTailP (Γ : LCtx) (a b T : Expr Nat) : Option (ConvT E n Γ a b T) :=
  match a, b with
  | .app f x, .app g y =>
      match appConvWith E n fuel TC CA Γ f x g y with
      | some ⟨U, c⟩ => (TC Γ U T).map (convT_of_tyConv c)
      | none => none
  | .lit t, b' =>
      match litAt? E n TC Γ t T, CA Γ (natExpand t) b' T with
      | some c, some c' => some (ConvT.trans Γ _ _ _ T c c')
      | _, _ => none
  | a', .lit t =>
      match litAt? E n TC Γ t T, CA Γ a' (natExpand t) T with
      | some c, some c' => some (ConvT.trans Γ _ _ _ T c' (ConvT.symm Γ _ _ T c))
      | _, _ => none
  | _, _ => none

/-- `convAt?`'s ι/β-step arm (either side), before the tail -/
def convFirstP (Γ : LCtx) (a b T : Expr Nat) : Option (ConvT E n Γ a b T) :=
  match convStepP E n fuel TC Γ T a, convStepP E n fuel TC Γ T b with
  | some ⟨a', c⟩, _ => (CA Γ a' b T).map (ConvT.trans Γ a a' b T c)
  | none, some ⟨b', c⟩ =>
      (CA Γ a b' T).map fun c' => ConvT.trans Γ a b' b T c' (ConvT.symm Γ b b' T c)
  | none, none => none

/-- `convAt? (fuel+1)` with the fuel-level calls as callbacks -/
def convAtBodyP (Γ : LCtx) (a b T : Expr Nat) : Option (ConvT E n Γ a b T) :=
  if h : a = b then
    match tyAtWith E n fuel TC Γ a T with
    | some d => some (h ▸ .refl Γ a T d)
    | none => none
  else
  match irrAt? E n fuel TC Γ a b T with
  | some c => some c
  | none =>
    match stepAt? E n TC Γ a T, stepAt? E n TC Γ b T with
    | some ⟨a', c⟩, _ => (CA Γ a' b T).map (ConvT.trans Γ a a' b T c)
    | none, some ⟨b', c⟩ =>
        (CA Γ a b' T).map fun c' => ConvT.trans Γ a b' b T c' (ConvT.symm Γ b b' T c)
    | none, none => convFirstP E n fuel TC CA Γ a b T <|> convTailP E n fuel TC CA Γ a b T

end restate

theorem tyConv?_succ_eq (E : ResolvedEnv) (n fuel : Nat) (Γ : LCtx) (A B : Expr Nat) :
    tyConv? E n (fuel + 1) Γ A B =
      tyConvBodyP E n fuel (tyConv? E n fuel) (convAt? E n fuel) Γ A B := by
  rw [tyConv?]
  unfold tyConvBodyP tyMidP
  by_cases h : A = B
  · simp only [dif_pos h]
  · simp only [dif_neg h]
    generalize whnfTy E n Γ (fuel + 1) A = rA
    generalize whnfTy E n Γ (fuel + 1) B = rB
    rcases rA with ⟨X, cX⟩
    rcases rB with ⟨Y, cY⟩
    dsimp only
    by_cases h' : X = Y
    · simp only [dif_pos h']
    · simp only [dif_neg h']
      cases X <;> cases Y <;> rfl

theorem convAt?_succ_eq (E : ResolvedEnv) (n fuel : Nat) (Γ : LCtx) (a b T : Expr Nat) :
    convAt? E n (fuel + 1) Γ a b T =
      convAtBodyP E n fuel (tyConv? E n fuel) (convAt? E n fuel) Γ a b T := by
  rw [convAt?]
  unfold convAtBodyP
  by_cases h : a = b
  · rw [dif_pos h, dif_pos h]
    generalize tyAtWith E n fuel (tyConv? E n fuel) Γ a T = r
    rcases r with _ | d <;> rfl
  · rw [dif_neg h, dif_neg h]
    generalize irrAt? E n fuel (tyConv? E n fuel) Γ a b T = ri
    rcases ri with _ | c
    · generalize stepAt? E n (tyConv? E n fuel) Γ a T = sa
      generalize stepAt? E n (tyConv? E n fuel) Γ b T = sb
      rcases sa with _ | ⟨a', c⟩ <;> rcases sb with _ | ⟨b', c'⟩ <;> try rfl
      unfold convFirstP convStepP
      dsimp only
      generalize iotaBetaStep? E n fuel (tyConv? E n fuel) Γ a = ia
      generalize iotaBetaStep? E n fuel (tyConv? E n fuel) Γ b = ib
      rcases ia with _ | ⟨U, a', c⟩ <;> rcases ib with _ | ⟨V, b', c'⟩ <;> dsimp only
      all_goals first
        | (generalize tyConv? E n fuel Γ U T = tu; rcases tu with _ | tu <;> dsimp only)
        | skip
      all_goals first
        | (generalize tyConv? E n fuel Γ V T = tv; rcases tv with _ | tv <;> dsimp only)
        | skip
      all_goals first
        | rfl
        | (cases a <;> cases b <;> first | rfl | (exfalso; exact h rfl))
    · rfl

/-! ## the two levels over table-threading callbacks -/

section bodies
variable {E : ResolvedEnv} {n fuel : Nat}

def tyMidM (E : ResolvedEnv) (n fuel : Nat) (TC : CVM E n) (CA : CAM E n) (Γ : LCtx) (X Y : Expr Nat) :
    TM E n (Option (TyConvT E n Γ X Y)) :=
  if h' : X = Y then pure (some (h' ▸ .refl Γ X)) else
  match X, Y with
  | .sort l₁, .sort l₂ =>
      pure (if hl : decEqN l₁ l₂ = true then
        some (.of Γ _ _ _ (.sorts Γ l₁ l₂ (decEqN_sound l₁ l₂ hl))) else none)
  | .pi A₁ B₁, .pi A₂ B₂ => do
      let cA ← TC Γ A₁ A₂
      let cB ← TC (.assumption A₁ :: Γ) B₁ B₂
      match cA, cB with
      | some cA, some cB => piCongrM E n fuel TC Γ A₁ A₂ B₁ B₂ cA cB
      | _, _ => pure none
  | .app f a, .app g b => do
      let r ← appConvWithM E n fuel TC CA Γ f a g b
      pure (match r with
        | some ⟨U, c⟩ => (toSort? E n fuel Γ U).map fun s => TyConvT.of Γ _ _ s.1 (convT_of_tyConv c s.2)
        | none => none)
  | _, _ => pure none

theorem tyMidM_agrees {TCM : CVM E n} {CAM' : CAM E n}
    {TC : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    {CA : (Γ : LCtx) → (a b T : Expr Nat) → Option (ConvT E n Γ a b T)}
    (hc : CVImpl TCM TC) (ha : CAImpl CAM' CA) (Γ : LCtx) (X Y : Expr Nat) :
    Agrees (tyMidM E n fuel TCM CAM' Γ X Y) (tyMidP E n fuel TC CA Γ X Y) := by
  unfold tyMidM tyMidP
  by_cases h' : X = Y
  · rw [dif_pos h', dif_pos h']; exact Agrees.pure' _
  · rw [dif_neg h', dif_neg h']
    cases X <;> cases Y
    all_goals dsimp only
    all_goals first
      | exact Agrees.pure' _
      | (rename_i f a g b
         refine Agrees.bind (appConvWithM_agrees hc ha Γ f a g b) ?_
         generalize appConvWith E n fuel TC CA Γ f a g b = r
         rcases r with _ | ⟨U, c⟩ <;> exact Agrees.pure' _)
      | (rename_i A₁ B₁ A₂ B₂
         refine Agrees.bind (hc Γ A₁ A₂) (Agrees.bind (hc _ B₁ B₂) ?_)
         generalize TC Γ A₁ A₂ = r1
         generalize TC (.assumption A₁ :: Γ) B₁ B₂ = r2
         rcases r1 with _ | cA <;> rcases r2 with _ | cB
         all_goals first
           | exact Agrees.pure' _
           | exact piCongrM_agrees hc Γ A₁ A₂ B₁ B₂ cA cB)

def tyConvBodyM (E : ResolvedEnv) (n fuel : Nat) (TC : CVM E n) (CA : CAM E n) (Γ : LCtx) (A B : Expr Nat) :
    TM E n (Option (TyConvT E n Γ A B)) :=
  if h : A = B then pure (some (h ▸ .refl Γ A)) else do
  let rA := whnfTy E n Γ (fuel + 1) A
  let rB := whnfTy E n Γ (fuel + 1) B
  let mid ← tyMidM E n fuel TC CA Γ rA.1 rB.1
  let mid ← match mid with
    | some c => pure (some c)
    | none => iotaMidM E n fuel TC Γ rA.1 rB.1
  pure (mid.map fun c => .trans Γ A rA.1 B rA.2 (.trans Γ rA.1 rB.1 B c rB.2.symmT))

theorem tyConvBodyM_agrees {TCM : CVM E n} {CAM' : CAM E n}
    {TC : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    {CA : (Γ : LCtx) → (a b T : Expr Nat) → Option (ConvT E n Γ a b T)}
    (hc : CVImpl TCM TC) (ha : CAImpl CAM' CA) (Γ : LCtx) (A B : Expr Nat) :
    Agrees (tyConvBodyM E n fuel TCM CAM' Γ A B) (tyConvBodyP E n fuel TC CA Γ A B) := by
  unfold tyConvBodyM tyConvBodyP
  by_cases h : A = B
  · rw [dif_pos h, dif_pos h]; exact Agrees.pure' _
  · rw [dif_neg h, dif_neg h]
    dsimp only
    generalize whnfTy E n Γ (fuel + 1) A = rA
    generalize whnfTy E n Γ (fuel + 1) B = rB
    rcases rA with ⟨X, cX⟩
    rcases rB with ⟨Y, cY⟩
    dsimp only
    refine Agrees.bind (tyMidM_agrees hc ha Γ X Y) ?_
    generalize tyMidP E n fuel TC CA Γ X Y = m
    rcases m with _ | c
    · exact Agrees.bind (iotaMidM_agrees hc Γ X Y) (Agrees.pure' _)
    · exact Agrees.bind (Agrees.pure' _) (Agrees.pure' _)

def convStepM (E : ResolvedEnv) (n fuel : Nat) (TC : CVM E n) (Γ : LCtx) (T x : Expr Nat) :
    TM E n (Option (Σ e', ConvT E n Γ x e' T)) := do
  match ← iotaBetaStepM E n fuel TC Γ x with
  | some ⟨U, x', c⟩ => do
      let cU ← TC Γ U T
      pure (cU.map fun cU => ⟨x', convT_of_tyConv c cU⟩)
  | none => pure none

theorem convStepM_agrees {TCM : CVM E n}
    {TC : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    (hc : CVImpl TCM TC) (Γ : LCtx) (T x : Expr Nat) :
    Agrees (convStepM E n fuel TCM Γ T x) (convStepP E n fuel TC Γ T x) := by
  unfold convStepM convStepP
  refine Agrees.bind (iotaBetaStepM_agrees hc Γ x) ?_
  generalize iotaBetaStep? E n fuel TC Γ x = r
  rcases r with _ | ⟨U, x', c⟩
  · exact Agrees.pure' _
  · exact Agrees.bind (hc Γ U T) (Agrees.pure' _)

/-- the right side is only stepped when the left does not -/
def convFirstM (E : ResolvedEnv) (n fuel : Nat) (TC : CVM E n) (CA : CAM E n) (Γ : LCtx) (a b T : Expr Nat) :
    TM E n (Option (ConvT E n Γ a b T)) := do
  match ← convStepM E n fuel TC Γ T a with
  | some ⟨a', c⟩ => do
      let r ← CA Γ a' b T
      pure (r.map (ConvT.trans Γ a a' b T c))
  | none =>
      match ← convStepM E n fuel TC Γ T b with
      | some ⟨b', c⟩ => do
          let r ← CA Γ a b' T
          pure (r.map fun c' => ConvT.trans Γ a b' b T c' (ConvT.symm Γ b b' T c))
      | none => pure none

theorem convFirstM_agrees {TCM : CVM E n} {CAM' : CAM E n}
    {TC : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    {CA : (Γ : LCtx) → (a b T : Expr Nat) → Option (ConvT E n Γ a b T)}
    (hc : CVImpl TCM TC) (ha : CAImpl CAM' CA) (Γ : LCtx) (a b T : Expr Nat) :
    Agrees (convFirstM E n fuel TCM CAM' Γ a b T) (convFirstP E n fuel TC CA Γ a b T) := by
  unfold convFirstM convFirstP
  refine Agrees.bind (convStepM_agrees hc Γ T a) ?_
  generalize convStepP E n fuel TC Γ T a = s1
  rcases s1 with _ | ⟨a', c⟩
  · dsimp only
    refine Agrees.bind (convStepM_agrees hc Γ T b) ?_
    generalize convStepP E n fuel TC Γ T b = s2
    rcases s2 with _ | ⟨b', c⟩
    · exact Agrees.pure' _
    · exact Agrees.bind (ha Γ a b' T) (Agrees.pure' _)
  · exact Agrees.bind (ha Γ a' b T) (Agrees.pure' _)

def convTailM (E : ResolvedEnv) (n fuel : Nat) (TC : CVM E n) (CA : CAM E n) (Γ : LCtx) (a b T : Expr Nat) :
    TM E n (Option (ConvT E n Γ a b T)) :=
  match a, b with
  | .app f x, .app g y => do
      match ← appConvWithM E n fuel TC CA Γ f x g y with
      | some ⟨U, c⟩ => do
          let cU ← TC Γ U T
          pure (cU.map (convT_of_tyConv c))
      | none => pure none
  | .lit t, b' => do
      let c ← litAtM E n TC Γ t T
      let c' ← CA Γ (natExpand t) b' T
      pure (match c, c' with
        | some c, some c' => some (ConvT.trans Γ _ _ _ T c c')
        | _, _ => none)
  | a', .lit t => do
      let c ← litAtM E n TC Γ t T
      let c' ← CA Γ a' (natExpand t) T
      pure (match c, c' with
        | some c, some c' => some (ConvT.trans Γ _ _ _ T c' (ConvT.symm Γ _ _ T c))
        | _, _ => none)
  | _, _ => pure none

theorem convTailM_agrees {TCM : CVM E n} {CAM' : CAM E n}
    {TC : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    {CA : (Γ : LCtx) → (a b T : Expr Nat) → Option (ConvT E n Γ a b T)}
    (hc : CVImpl TCM TC) (ha : CAImpl CAM' CA) (Γ : LCtx) (a b T : Expr Nat) :
    Agrees (convTailM E n fuel TCM CAM' Γ a b T) (convTailP E n fuel TC CA Γ a b T) := by
  unfold convTailM convTailP
  cases a <;> cases b
  all_goals dsimp only
  all_goals first
    | exact Agrees.pure' _
    | (rename_i f x g y
       refine Agrees.bind (appConvWithM_agrees hc ha Γ f x g y) ?_
       generalize appConvWith E n fuel TC CA Γ f x g y = r
       rcases r with _ | ⟨U, c⟩
       · exact Agrees.pure' _
       · exact Agrees.bind (hc Γ U T) (Agrees.pure' _))
    | (refine Agrees.bind (litAtM_agrees hc Γ _ T) (Agrees.bind (ha _ _ _ T) ?_)
       generalize litAt? E n TC Γ _ T = r1
       exact Agrees.pure' _)

def convAtBodyM (E : ResolvedEnv) (n fuel : Nat) (TC : CVM E n) (CA : CAM E n) (Γ : LCtx) (a b T : Expr Nat) :
    TM E n (Option (ConvT E n Γ a b T)) :=
  if h : a = b then do
    let d ← tyAtWithM E n fuel TC Γ a T
    pure (match d with
      | some d => some (h ▸ .refl Γ a T d)
      | none => none)
  else do
  match ← irrAtM E n fuel TC Γ a b T with
  | some c => pure (some c)
  | none =>
    match ← stepAtM E n TC Γ a T with
    | some ⟨a', c⟩ => do
        let r ← CA Γ a' b T
        pure (r.map (ConvT.trans Γ a a' b T c))
    | none =>
      match ← stepAtM E n TC Γ b T with
      | some ⟨b', c⟩ => do
          let r ← CA Γ a b' T
          pure (r.map fun c' => ConvT.trans Γ a b' b T c' (ConvT.symm Γ b b' T c))
      | none => do
          match ← convFirstM E n fuel TC CA Γ a b T with
          | some c => pure (some c)
          | none => convTailM E n fuel TC CA Γ a b T

theorem convAtBodyM_agrees {TCM : CVM E n} {CAM' : CAM E n}
    {TC : (Γ : LCtx) → (A B : Expr Nat) → Option (TyConvT E n Γ A B)}
    {CA : (Γ : LCtx) → (a b T : Expr Nat) → Option (ConvT E n Γ a b T)}
    (hc : CVImpl TCM TC) (ha : CAImpl CAM' CA) (Γ : LCtx) (a b T : Expr Nat) :
    Agrees (convAtBodyM E n fuel TCM CAM' Γ a b T) (convAtBodyP E n fuel TC CA Γ a b T) := by
  unfold convAtBodyM convAtBodyP
  by_cases h : a = b
  · rw [dif_pos h, dif_pos h]
    refine Agrees.bind (tyAtWithM_agrees hc Γ a T) ?_
    generalize tyAtWith E n fuel TC Γ a T = r
    rcases r with _ | d <;> exact Agrees.pure' _
  · rw [dif_neg h, dif_neg h]
    refine Agrees.bind (irrAtM_agrees hc Γ a b T) ?_
    generalize irrAt? E n fuel TC Γ a b T = ri
    rcases ri with _ | c
    · dsimp only
      refine Agrees.bind (stepAtM_agrees hc Γ a T) ?_
      generalize stepAt? E n TC Γ a T = sa
      rcases sa with _ | ⟨a', c⟩
      · dsimp only
        refine Agrees.bind (stepAtM_agrees hc Γ b T) ?_
        generalize stepAt? E n TC Γ b T = sb
        rcases sb with _ | ⟨b', c⟩
        · dsimp only
          refine Agrees.bind (convFirstM_agrees hc ha Γ a b T) ?_
          generalize convFirstP E n fuel TC CA Γ a b T = fr
          rcases fr with _ | c
          · exact convTailM_agrees hc ha Γ a b T
          · exact Agrees.pure' _
        · exact Agrees.bind (ha Γ a b' T) (Agrees.pure' _)
      · exact Agrees.bind (ha Γ a' b T) (Agrees.pure' _)
    · exact Agrees.pure' _

end bodies

/-! ## the memoized levels: fuel `f+1` memoizes its body over level `f` -/

/-- level `fuel`: the table-threading `tyConv?` / `convAt?` at that fuel (fuel 0 is the
    original: equality as written / `synCheck`) -/
def lvl (E : ResolvedEnv) (n : Nat) : Nat → CVM E n × CAM E n
  | 0 => (fun Γ A B => pure (tyConv? E n 0 Γ A B), fun Γ a b T => pure (convAt? E n 0 Γ a b T))
  | fuel + 1 =>
      let p := lvl E n fuel
      (fun Γ A B => memoTy (fuel + 1) Γ A B fun _ => tyConvBodyM E n fuel p.1 p.2 Γ A B,
       fun Γ a b T => memoAt (fuel + 1) Γ a b T fun _ => convAtBodyM E n fuel p.1 p.2 Γ a b T)

/-- every level implements the original at its fuel -/
theorem lvl_impl (E : ResolvedEnv) (n : Nat) :
    ∀ fuel, CVImpl (lvl E n fuel).1 (tyConv? E n fuel) ∧ CAImpl (lvl E n fuel).2 (convAt? E n fuel)
  | 0 => ⟨fun _ _ _ => Agrees.pure' _, fun _ _ _ _ => Agrees.pure' _⟩
  | fuel + 1 =>
      have ih := lvl_impl E n fuel
      ⟨fun Γ A B => memoTy_agrees (Agrees.of_eq (tyConvBodyM_agrees ih.1 ih.2 Γ A B)
          (tyConv?_succ_eq E n fuel Γ A B).symm),
       fun Γ a b T => memoAt_agrees (Agrees.of_eq (convAtBodyM_agrees ih.1 ih.2 Γ a b T)
          (convAt?_succ_eq E n fuel Γ a b T).symm)⟩

/-! ## the cert machine over the table -/

def certWhnfM (E : ResolvedEnv) (n k : Nat) (TC : CVM E n) (Γ : LCtx) (T : Expr Nat) :
    Nat → (e : Expr Nat) → TM E n (Option (Σ w, ConvT E n Γ e w T))
  | 0, e => do
      let d ← tyAtWithM E n k TC Γ e T
      pure (d.map fun d => ⟨e, .refl Γ e T d⟩)
  | s + 1, e => do
      match ← stepAtM E n TC Γ e T with
      | some ⟨e', c⟩ => do
          let r ← certWhnfM E n k TC Γ T s e'
          pure (r.map fun ⟨w, c2⟩ => ⟨w, .trans Γ e e' w T c c2⟩)
      | none => do
          let d ← tyAtWithM E n k TC Γ e T
          pure (d.map fun d => ⟨e, .refl Γ e T d⟩)

theorem certWhnfM_agrees {E : ResolvedEnv} {n k : Nat} {TCM : CVM E n}
    (hc : CVImpl TCM (tyConv? E n k)) (Γ : LCtx) (T : Expr Nat) :
    ∀ (s : Nat) (e : Expr Nat), Agrees (certWhnfM E n k TCM Γ T s e) (certWhnf E n k Γ T s e)
  | 0, e => by
      rw [certWhnfM, certWhnf]
      exact Agrees.bind (tyAtWithM_agrees hc Γ e T) (Agrees.pure' _)
  | s + 1, e => by
      rw [certWhnfM, certWhnf]
      refine Agrees.bind (stepAtM_agrees hc Γ e T) ?_
      generalize stepAt? E n (tyConv? E n k) Γ e T = r
      rcases r with _ | ⟨e', c⟩
      · exact Agrees.bind (tyAtWithM_agrees hc Γ e T) (Agrees.pure' _)
      · exact Agrees.bind (certWhnfM_agrees hc Γ T s e') (Agrees.pure' _)

/-- `certStep` over the table -/
def certStepT (s : CertState) : TM s.ambient.env s.ambient.univs (CertResult s.ambient) :=
  match s.budget with
  | 0 => pure .suspended
  | _ + 1 =>
    let L := lvl s.ambient.env s.ambient.univs s.budget
    match s.task with
    | .whnfT T e => do
        let r ← certWhnfM s.ambient.env s.ambient.univs s.budget L.1 s.ambient.ctx T s.budget e
        pure (match r with
          | some ⟨w, c⟩ => .accepted (.whnfed e w T c)
          | none => .refused "[rcic_cert_whnf_refused]")
    | .convT T l r => do
        let x ← L.2 s.ambient.ctx l r T
        pure (match x with
          | some c => .accepted (.converted l r T c)
          | none => .refused "[rcic_cert_conv_refused]")
    | .tyConvT A B => do
        let x ← L.1 s.ambient.ctx A B
        pure (match x with
          | some c => .accepted (.tyConverted A B c)
          | none => .refused "[rcic_cert_tyconv_refused]")

theorem certStepT_agrees : ∀ s : CertState, Agrees (certStepT s) (certStep s)
  | ⟨amb, task, 0⟩ => by
      unfold certStepT certStep
      exact Agrees.pure' _
  | ⟨amb, task, b + 1⟩ => by
      have hl := lvl_impl amb.env amb.univs (b + 1)
      unfold certStepT certStep
      dsimp only
      cases task with
      | whnfT T e =>
          dsimp only
          refine Agrees.bind (certWhnfM_agrees hl.1 amb.ctx T (b + 1) e) ?_
          generalize certWhnf amb.env amb.univs (b + 1) amb.ctx T (b + 1) e = r
          rcases r with _ | ⟨w, c⟩ <;> exact Agrees.pure' _
      | convT T l r =>
          dsimp only
          refine Agrees.bind (hl.2 amb.ctx l r T) ?_
          generalize convAt? amb.env amb.univs (b + 1) amb.ctx l r T = x
          rcases x with _ | c <;> exact Agrees.pure' _
      | tyConvT A B =>
          dsimp only
          refine Agrees.bind (hl.1 amb.ctx A B) ?_
          generalize tyConv? amb.env amb.univs (b + 1) amb.ctx A B = x
          rcases x with _ | c <;> exact Agrees.pure' _

/-! ## the memoized entries, equal to the originals -/

/-- `certStep`, run over a fresh table -/
def certStepMemo (s : CertState) : CertResult s.ambient :=
  ((certStepT s).run (TTable.empty s.ambient.env s.ambient.univs)).1

/-- THE MEMOIZED CERT STEP IS THE CERT STEP: the same result, derivation included,
    at every state (every budget, task, environment). -/
theorem certStepMemo_eq (s : CertState) : certStepMemo s = certStep s :=
  (certStepT_agrees s _ (TTable.empty_sound _ _)).1

def certWhnfSMemo (tbl : List (Nat × CheckedMember)) (univs : Nat) (ctx : LCtx)
    (T e : Expr Nat) (budget : Nat) : Summ :=
  summ (certStepMemo (certState tbl univs ctx (.whnfT T e) budget))

def certConvSMemo (tbl : List (Nat × CheckedMember)) (univs : Nat) (ctx : LCtx)
    (T l r : Expr Nat) (budget : Nat) : Summ :=
  summ (certStepMemo (certState tbl univs ctx (.convT T l r) budget))

def certTyConvSMemo (tbl : List (Nat × CheckedMember)) (univs : Nat) (ctx : LCtx)
    (A B : Expr Nat) (budget : Nat) : Summ :=
  summ (certStepMemo (certState tbl univs ctx (.tyConvT A B) budget))

theorem certWhnfSMemo_eq (tbl univs ctx T e budget) :
    certWhnfSMemo tbl univs ctx T e budget = certWhnfS tbl univs ctx T e budget := by
  unfold certWhnfSMemo certWhnfS; rw [certStepMemo_eq]

theorem certConvSMemo_eq (tbl univs ctx T l r budget) :
    certConvSMemo tbl univs ctx T l r budget = certConvS tbl univs ctx T l r budget := by
  unfold certConvSMemo certConvS; rw [certStepMemo_eq]

theorem certTyConvSMemo_eq (tbl univs ctx A B budget) :
    certTyConvSMemo tbl univs ctx A B budget = certTyConvS tbl univs ctx A B budget := by
  unfold certTyConvSMemo certTyConvS; rw [certStepMemo_eq]

/-- the soundness rows transfer: an accepted memoized conversion carries a `ConvT` -/
theorem certConvSMemo_sound (tbl univs ctx T l r budget)
    (h : certConvSMemo tbl univs ctx T l r budget = .converted l r T) :
    Nonempty (ConvT (envOfTable tbl) univs ctx l r T) :=
  certConvS_sound tbl univs ctx T l r budget (certConvSMemo_eq .. ▸ h)

/-! ## why the fuel is in the key: the typed machine is not fuel-monotone

Environment: `B : Sort 1`, `b : B`, `G : B → Sort 1`, `cbig0 := λ z : B. z`,
`cbig1 := cbig0`, `K := λ z : B. G (cbig1 z)`, `cx := b`, `a1 := K cx`, `a2 := a1`,
`b1 := K b`, `b2 := b1`, `x : a2`. At fuel 2, `whnfTy 2` stops the two sides at
`K cx` / `K b` and application congruence joins them; at fuel 4 the sides are
`G (cbig1 cx)` / `G (cbig1 b)`, whose argument conversion (head steps before
congruence) needs more fuel than is left. -/

def cexG : Expr Nat := .const 10 []
def cexBig0 : Expr Nat := .const 11 []
def cexBig1 : Expr Nat := .const 12 []
def cexK : Expr Nat := .const 13 []
def cexCx : Expr Nat := .const 14 []
def cexA2 : Expr Nat := .const 16 []
def cexB2 : Expr Nat := .const 18 []
def cexX : Expr Nat := .const 19 []

def cexTbl : List (Nat × CheckedMember) :=
  let s1 : Expr Nat := .sort (.succ .zero)
  let cB : Expr Nat := .const 0 []
  let ax := fun (T : Expr Nat) => (⟨.axiomM, 0, T, none⟩ : CheckedMember)
  let dfn := fun (T b : Expr Nat) => (⟨.definitionM, 0, T, some b⟩ : CheckedMember)
  [(0, ax s1), (1, ax cB), (10, ax (.pi cB s1)),
   (11, dfn (.pi cB cB) (.lam cB (.bvar 0))), (12, dfn (.pi cB cB) cexBig0),
   (13, dfn (.pi cB s1) (.lam cB (.app cexG (.app cexBig1 (.bvar 0))))),
   (14, dfn cB (.const 1 [])), (15, dfn s1 (.app cexK cexCx)), (16, dfn s1 (.const 15 [])),
   (17, dfn s1 (.app cexK (.const 1 []))), (18, dfn s1 (.const 17 [])), (19, ax cexA2)]

/-- a success at fuel 2 that is a refusal at fuel 4: reusing a recorded success at a
    larger fuel would change the verdict -/
theorem cex_tyConv_ok_not_up :
    (tyConv? (envOfTable cexTbl) 0 2 [] cexA2 cexB2).isSome = true ∧
    (tyConv? (envOfTable cexTbl) 0 4 [] cexA2 cexB2).isSome = false := ⟨rfl, rfl⟩

/-- a refusal at fuel 1 that is a success at fuel 2: reusing a recorded refusal at
    another fuel would change the verdict -/
theorem cex_tyConv_no_not_up :
    (tyConv? (envOfTable cexTbl) 0 1 [] cexA2 cexB2).isSome = false ∧
    (tyConv? (envOfTable cexTbl) 0 2 [] cexA2 cexB2).isSome = true := ⟨rfl, rfl⟩

/-- the same at the emitted entry: `converted` at budget 3, `refused` at budget 5 -/
theorem cex_certConvS_ok_not_up :
    certConvS cexTbl 0 [] cexB2 cexX cexX 3 = .converted cexX cexX cexB2 ∧
    certConvS cexTbl 0 [] cexB2 cexX cexX 5 = .refused "[rcic_cert_conv_refused]" := ⟨rfl, rfl⟩

/-- `refused` at budget 2, `converted` at budget 3 -/
theorem cex_certConvS_no_not_up :
    certConvS cexTbl 0 [] cexB2 cexX cexX 2 = .refused "[rcic_cert_conv_refused]" ∧
    certConvS cexTbl 0 [] cexB2 cexX cexX 3 = .converted cexX cexX cexB2 := ⟨rfl, rfl⟩

/-- both rules, as table entries: a SOUND entry recorded at fuel 3 (a success) and one
    recorded at fuel 2 (a refusal) each disagree with the original at another fuel -/
theorem cex_sound_entry_wrong_elsewhere :
    (∃ r, (TEntry.at 3 [] cexX cexX cexB2 r : TEntry (envOfTable cexTbl) 0).Sound ∧
        r.isSome = true ∧ (convAt? (envOfTable cexTbl) 0 5 [] cexX cexX cexB2).isSome = false) ∧
    (∃ r, (TEntry.at 2 [] cexX cexX cexB2 r : TEntry (envOfTable cexTbl) 0).Sound ∧
        r.isSome = false ∧ (convAt? (envOfTable cexTbl) 0 3 [] cexX cexX cexB2).isSome = true) :=
  ⟨⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩⟩

end Rcic.Machine.TMemo
