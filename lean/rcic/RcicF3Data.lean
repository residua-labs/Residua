import rcic.RcicF3Tel

/-!
# F3 S5a: data values and telescopes

- `psnd`: the second projection of a pair; `tup` / `untup`: tuples;
- `dataVal j xs = ⟨∅, ⟨j, xs⟩⟩`: the value of constructor `j` at fields `xs`
  (never `∅`, never a type value), with `tagOf` / `payload` decoding it;
- `TelFits Ds ρ xs`: the values `xs` fit the telescope `Ds` read from `ρ`;
  `push`: the environment after them;
- `fapps_piLam`: applying a telescope abstraction to fitting values computes
  its end value; `mem_fapps`: applying an element of a telescope type to
  fitting values gives an element of the end type;
- `findIdx`: the first index satisfying a decided predicate.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

universe T

namespace PSet

/-- Second projection of a pair. -/
def psnd (p : PSet.{T}) : PSet.{T} :=
  sUnion (sep (fun z => Equiv p (ordPair (pfst p) z)) (sUnion p))

theorem psnd_pair {a b : PSet.{T}} : Equiv (psnd (ordPair a b)) b := by
  apply ext; intro z
  constructor
  · intro hz
    obtain ⟨w, hw, hzw⟩ := mem_sUnion.mp hz
    obtain ⟨_, hp, he⟩ := mem_sep.mp hw
    have hp' : Equiv (ordPair a b) (ordPair (pfst (ordPair a b)) w) :=
      hp.trans (ordPair_congr Equiv.rfl he)
    exact mem_congr_right (ordPair_equiv hp').2.symm hzw
  · intro hz
    have hb : b ∈ sUnion (ordPair a b) :=
      mem_sUnion.mpr ⟨pair a b, mem_pair.mpr (Or.inr Equiv.rfl), mem_pair.mpr (Or.inr Equiv.rfl)⟩
    obtain ⟨i, hi⟩ := hb
    exact mem_sUnion.mpr ⟨b, mem_sep.mpr ⟨i, ordPair_congr pfst_pair.symm hi.symm, hi⟩, hz⟩

theorem psnd_congr {p q : PSet.{T}} (h : Equiv p q) : Equiv (psnd p) (psnd q) :=
  sUnion_congr (sep_congr
    (fun x y hxy hx => h.symm.trans (hx.trans (ordPair_congr (pfst_congr h) hxy)))
    (fun x y hxy hx => h.trans (hx.trans (ordPair_congr (pfst_congr h.symm) hxy)))
    (sUnion_congr h))

/-- Tuples. -/
def tup : List PSet.{T} → PSet.{T}
  | [] => pempty
  | x :: xs => ordPair x (tup xs)

/-- The first `m` components of a tuple. -/
def untup : Nat → PSet.{T} → List PSet.{T}
  | 0, _ => []
  | m + 1, t => pfst t :: untup m (psnd t)

/-- Pointwise `≈` of lists. -/
def LEq : List PSet.{T} → List PSet.{T} → Prop
  | [], [] => True
  | x :: xs, y :: ys => Equiv x y ∧ LEq xs ys
  | _, _ => False

theorem LEq.refl : (xs : List PSet.{T}) → LEq xs xs
  | [] => trivial
  | _ :: xs => ⟨Equiv.rfl, LEq.refl xs⟩

theorem LEq.symm : {xs ys : List PSet.{T}} → LEq xs ys → LEq ys xs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨h.symm, LEq.symm hs⟩

theorem LEq.trans : {xs ys zs : List PSet.{T}} → LEq xs ys → LEq ys zs → LEq xs zs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h, hs⟩, ⟨h', hs'⟩ => ⟨h.trans h', LEq.trans hs hs'⟩

theorem LEq.length : {xs ys : List PSet.{T}} → LEq xs ys → xs.length = ys.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, hs⟩ => by simp [LEq.length hs]

theorem untup_tup : (xs : List PSet.{T}) → LEq (untup xs.length (tup xs)) xs
  | [] => trivial
  | x :: xs => ⟨pfst_pair, LEq.trans (untup_congr xs.length psnd_pair) (untup_tup xs)⟩
where
  untup_congr : (m : Nat) → {t t' : PSet.{T}} → Equiv t t' → LEq (untup m t) (untup m t')
    | 0, _, _, _ => trivial
    | m + 1, _, _, h => ⟨pfst_congr h, untup_congr m (psnd_congr h)⟩

theorem tup_congr : {xs ys : List PSet.{T}} → LEq xs ys → Equiv (tup xs) (tup ys)
  | [], [], _ => Equiv.rfl
  | _ :: _, _ :: _, ⟨h, hs⟩ => ordPair_congr h (tup_congr hs)

theorem tup_inj : {xs ys : List PSet.{T}} → xs.length = ys.length → Equiv (tup xs) (tup ys) → LEq xs ys
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, hl, h =>
      ⟨(ordPair_equiv h).1, tup_inj (by simpa using hl) (ordPair_equiv h).2⟩

/-- The value of constructor `j` at fields `xs`. -/
def dataVal (j : Nat) (xs : List PSet.{T}) : PSet.{T} := ordPair pempty (ordPair (ord j) (tup xs))

/-- The constructor tag of a data value. -/
def tagOf (z : PSet.{T}) : PSet.{T} := pfst (psnd z)

/-- The field tuple of a data value. -/
def payload (z : PSet.{T}) : PSet.{T} := psnd (psnd z)

theorem tagOf_dataVal (j : Nat) (xs : List PSet.{T}) : Equiv (tagOf (dataVal j xs)) (ord j) :=
  (pfst_congr psnd_pair).trans pfst_pair

theorem payload_dataVal (j : Nat) (xs : List PSet.{T}) : Equiv (payload (dataVal j xs)) (tup xs) :=
  (psnd_congr psnd_pair).trans psnd_pair

theorem tagOf_congr {z z' : PSet.{T}} (h : Equiv z z') : Equiv (tagOf z) (tagOf z') :=
  pfst_congr (psnd_congr h)

theorem payload_congr {z z' : PSet.{T}} (h : Equiv z z') : Equiv (payload z) (payload z') :=
  psnd_congr (psnd_congr h)

theorem dataVal_congr (j : Nat) {xs ys : List PSet.{T}} (h : LEq xs ys) :
    Equiv (dataVal j xs) (dataVal j ys) :=
  ordPair_congr Equiv.rfl (ordPair_congr Equiv.rfl (tup_congr h))

theorem dataVal_ne_pempty (j : Nat) (xs : List PSet.{T}) : ¬ Equiv (dataVal j xs) pempty := fun h =>
  not_mem_pempty (mem_congr_right h (mem_pair.mpr (Or.inl Equiv.rfl)))

theorem dataVal_inj {j j' : Nat} {xs ys : List PSet.{T}} (hl : xs.length = ys.length)
    (h : Equiv (dataVal j xs) (dataVal j' ys)) : j = j' ∧ LEq xs ys := by
  have h2 := (ordPair_equiv (ordPair_equiv h).2)
  exact ⟨ord_inj h2.1, tup_inj hl h2.2⟩

/-! ### telescopes -/

/-- The environment after pushing `xs` in order. -/
def push : List PSet.{T} → (Nat → PSet.{T}) → Nat → PSet.{T}
  | [], ρ => ρ
  | x :: xs, ρ => push xs (vcons x ρ)

/-- `xs` fit the telescope `Ds` read from `ρ`. -/
def TelFits (M : Interp.{T}) (σ : Nat → Nat) : List (Expr Nat) → (Nat → PSet.{T}) → List PSet.{T} → Prop
  | [], _, [] => True
  | A :: Ds, ρ, x :: xs => x ∈ Ed M (den M σ ρ A) ∧ TelFits M σ Ds (vcons x ρ) xs
  | _, _, _ => False

theorem TelFits.length {M : Interp.{T}} {σ : Nat → Nat} :
    {Ds : List (Expr Nat)} → {ρ : Nat → PSet.{T}} → {xs : List PSet.{T}} →
    TelFits M σ Ds ρ xs → xs.length = Ds.length
  | [], _, [], _ => rfl
  | _ :: _, _, _ :: _, ⟨_, h⟩ => by simp [TelFits.length h]

theorem TelFits.append {M : Interp.{T}} {σ : Nat → Nat} :
    {Ds Ds' : List (Expr Nat)} → {ρ : Nat → PSet.{T}} → {xs xs' : List PSet.{T}} →
    TelFits M σ Ds ρ xs → TelFits M σ Ds' (push xs ρ) xs' → TelFits M σ (Ds ++ Ds') ρ (xs ++ xs')
  | [], _, _, [], _, _, h' => h'
  | _ :: _, _, _, _ :: _, _, ⟨hx, h⟩, h' => ⟨hx, TelFits.append h h'⟩

/-- Iterated application of a telescope abstraction to fitting values. -/
theorem fapps_piLam (M : Interp.{T}) (σ : Nat → Nat) {g : (Nat → PSet.{T}) → PSet.{T}}
    (hg : EnvResp g) (b : Expr Nat) :
    (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{T}) → (xs : List PSet.{T}) → TelFits M σ Ds ρ xs →
      Equiv (fapps (piLam M σ g ρ (policyPi Ds b)) xs) (piLam M σ g (push xs ρ) b)
  | [], _, [], _ => Equiv.rfl
  | A :: Ds, ρ, x :: xs, ⟨hx, h⟩ => by
      show Equiv (fapps (fapp (lamVal M (den M σ ρ A) (fun y => piLam M σ g (vcons y ρ) (policyPi Ds b))) x) xs) _
      have e1 := beta_val M (b := fun y => piLam M σ g (vcons y ρ) (policyPi Ds b))
        (fun y y' hy => piLam_congr M σ hg _ (vcons_congr (ρ := ρ) (ρ' := ρ) hy (fun _ => Equiv.rfl))) hx
      exact (fapps_congr e1 xs).trans (fapps_piLam M σ hg b Ds (vcons x ρ) xs h)

/-- Applying an element of a telescope type to fitting values lands in the end type. -/
theorem mem_fapps (M : Interp.{T}) (σ : Nat → Nat) (b : Expr Nat) :
    (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{T}) → (f : PSet.{T}) → (xs : List PSet.{T}) →
      f ∈ Ed M (den M σ ρ (policyPi Ds b)) → TelFits M σ Ds ρ xs →
      fapps f xs ∈ Ed M (den M σ (push xs ρ) b)
  | [], _, _, [], hf, _ => hf
  | A :: Ds, ρ, f, x :: xs, hf, ⟨hx, h⟩ =>
      mem_fapps M σ b Ds (vcons x ρ) (fapp f x) xs (app_mem M (den_resp M σ ρ _) hf hx) h

theorem fapps_append : (F : PSet.{T}) → (xs ys : List PSet.{T}) →
    fapps F (xs ++ ys) = fapps (fapps F xs) ys
  | _, [], _ => rfl
  | F, x :: xs, ys => fapps_append (fapp F x) xs ys

theorem fapps_congr_args : (F : PSet.{T}) → {xs ys : List PSet.{T}} → LEq xs ys →
    Equiv (fapps F xs) (fapps F ys)
  | _, [], [], _ => Equiv.rfl
  | F, _ :: _, _ :: _, ⟨h, hs⟩ => (fapps_congr (fapp_congr Equiv.rfl h) _).trans (fapps_congr_args _ hs)

/-! ### decided search -/

/-- The first index below `k` satisfying `p`, decided by the interpretation's `dec`. -/
def findIdx (M : Interp.{T}) (p : Nat → Prop) : Nat → Option Nat
  | 0 => none
  | k + 1 =>
      match findIdx M p k with
      | some i => some i
      | none => cond' M p k
where
  cond' (M : Interp.{T}) (p : Nat → Prop) (k : Nat) : Option Nat :=
    match M.dec (p k) with
    | isTrue _ => some k
    | isFalse _ => none

theorem findIdx_none (M : Interp.{T}) (p : Nat → Prop) {j : Nat}
    (hno : ∀ i, i < j → ¬ p i) : ∀ k, k ≤ j → findIdx M p k = none
  | 0, _ => rfl
  | k + 1, hk => by
      show (match findIdx M p k with
        | some i => some i
        | none => findIdx.cond' M p k) = none
      rw [findIdx_none M p hno k (Nat.le_of_succ_le hk)]
      show findIdx.cond' M p k = none
      unfold findIdx.cond'
      cases M.dec (p k) with
      | isTrue h => exact absurd h (hno k hk)
      | isFalse _ => rfl

theorem findIdx_eq (M : Interp.{T}) (p : Nat → Prop) {j : Nat} (hj : p j)
    (huniq : ∀ i, p i → i = j) : ∀ k, j < k → findIdx M p k = some j
  | 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, h => by
      show (match findIdx M p k with
        | some i => some i
        | none => findIdx.cond' M p k) = some j
      rcases Nat.lt_or_ge j k with hjk | hjk
      · rw [findIdx_eq M p hj huniq k hjk]
      · have hjk' : j = k := Nat.le_antisymm (Nat.le_of_lt_succ h) hjk
        subst hjk'
        have hnone : findIdx M p j = none := findIdx_none M p (fun i hi hpi =>
          absurd (huniq i hpi) (Nat.ne_of_lt hi)) j (Nat.le_refl j)
        rw [hnone]
        unfold findIdx.cond'
        cases M.dec (p j) with
        | isTrue _ => rfl
        | isFalse hn => exact absurd hj hn

end PSet

end Rcic.F3
