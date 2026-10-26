import rcic.RcicF3KTWTransfer

/-!
# F3 S7 KT-2d-2a: the Prop-instance least fixed point.

`DStarP σ ρp` is the least fixed point of `PhiP` inside `UP` — the set of
index tuples for which some constructor has a proof-instance. `famLfpP` is the
Prop-instance family entry.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

namespace PSet

open Rcic.Declarative

universe T

/-- Untruncated fits as a set of tuples. -/
def FitSetU (M : Interp.{T}) (σ : Nat → Nat) : List (Expr Nat) → (Nat → PSet.{T}) → PSet.{T}
  | [], _ => singleton pempty
  | A :: Ds, ρ => sUnion (sImage (fun x => sImage (fun t => ordPair x t)
      (FitSetU M σ Ds (vcons x ρ))) (Ed M (den M σ ρ A)))

/-- `FitSetU` respects pointwise environment equivalence. -/
theorem FitSetU_congr (M : Interp.{T}) (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) → ∀ {ρ ρ' : Nat → PSet.{T}}, (∀ i, Equiv (ρ i) (ρ' i)) →
      Equiv (FitSetU M σ Ds ρ) (FitSetU M σ Ds ρ')
  | [], _, _, _ => Equiv.rfl
  | A :: Ds, ρ, ρ', h => sUnion_congr (sImage_congr
      (fun a a' haa => sImage_congr (fun b b' hbb =>
        ordPair_congr haa hbb) (FitSetU_congr M σ Ds (vcons_congr haa h)))
      (ed_congr M (den_congr M σ A h)))

/-- `FitSetU` respects level valuations agreeing below `ar`. -/
theorem FitSetU_levels (M : Interp.{T}) {σ σ' : Nat → Nat} {ar : Nat}
    (hσ : ∀ i, i < ar → σ i = σ' i) :
    (Ds : List (Expr Nat)) → ExprsBounded ar Ds → (ρ : Nat → PSet.{T}) →
    Equiv (FitSetU M σ Ds ρ) (FitSetU M σ' Ds ρ)
  | [], _, ρ => Equiv.rfl
  | A :: Ds, hb, ρ => sUnion_congr (sImage_congr
      (fun a a' haa => sImage_congr (fun b b' hbb =>
        ordPair_congr haa hbb) ((FitSetU_levels M hσ Ds
          (fun e he => hb e (List.mem_cons.mpr (Or.inr he))) (vcons a ρ)).trans
          (FitSetU_congr M σ' Ds (vcons_congr haa (fun _ => Equiv.rfl)))))
      (ed_congr M (by rw [den_levels_agree M hσ A
        (hb A (List.mem_cons.mpr (Or.inl rfl))) ρ]; exact Equiv.rfl)))

/-- Membership in `FitSetU` is an exactly-fitting tuple. -/
theorem mem_FitSetU_iff (M : Interp.{T}) (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{T}) → {t : PSet.{T}} →
    (t ∈ FitSetU M σ Ds ρ ↔ ∃ xs, Equiv t (tup xs) ∧ TelFits M σ Ds ρ xs)
  | [], ρ, t => by
      constructor
      · intro h; exact ⟨[], mem_singleton.mp h, trivial⟩
      · rintro ⟨xs, hx, h⟩
        cases xs with
        | nil => exact mem_singleton.mpr hx
        | cons _ _ => exact False.elim h
  | A :: Ds, ρ, t => by
      constructor
      · intro h
        obtain ⟨s, hs, ht⟩ := mem_sUnion.mp h
        obtain ⟨i, hseq⟩ := mem_sImage.mp hs
        obtain ⟨j, hte⟩ := mem_sImage.mp (mem_congr_right hseq.symm ht)
        obtain ⟨xs, hxs, hfit⟩ := (mem_FitSetU_iff M σ Ds
          (vcons ((Ed M (den M σ ρ A)).Func i) ρ)).mp ⟨j, Equiv.refl _⟩
        exact ⟨(Ed M (den M σ ρ A)).Func i :: xs,
          hte.symm.trans (ordPair_congr Equiv.rfl hxs), ⟨⟨i, Equiv.refl _⟩, hfit⟩⟩
      · rintro ⟨xs, hx, h⟩
        cases xs with
        | nil => exact False.elim h
        | cons x xs =>
            obtain ⟨hxEd, hfit⟩ := h
            obtain ⟨ix, hix⟩ := hxEd
            obtain ⟨it, hit⟩ : tup xs ∈ FitSetU M σ Ds (vcons x ρ) :=
              (mem_FitSetU_iff M σ Ds (vcons x ρ)).mpr ⟨xs, Equiv.rfl, hfit⟩
            refine mem_sUnion.mpr
              ⟨sImage (fun t => ordPair x t) (FitSetU M σ Ds (vcons x ρ)), ⟨ix, ?_⟩, ⟨it, ?_⟩⟩
            · exact sImage_congr
                (fun a a' haa => ordPair_congr hix haa)
                (FitSetU_congr M σ Ds (vcons_congr hix (fun _ => Equiv.rfl)))
            · exact (ordPair_congr Equiv.rfl hit).trans hx.symm

section

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)


/-- One field's Prop-instance condition: recursive fields are proofs (`∅`)
whose index tuples are derivable. -/
def okP (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (T : PSet.{4}) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (A : Expr Nat) (x : PSet.{4}) : Prop :=
  match kindOf fd.fref A with
  | .plain => x ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ A)
  | .direct => Equiv x pempty ∧ argsFitF P μ fd σ ρ A ∧
      tup ((familyIdx fd.params.length A).map (den (mkM P μ) σ ρ)) ∈ T
  | .fn => Equiv x pempty ∧ ∀ y, y ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ (piDom A)) →
      argsFitF P μ fd σ (vcons y ρ) (piCod A) ∧
      tup ((familyIdx fd.params.length (piCod A)).map (den (mkM P μ) σ (vcons y ρ))) ∈ T

/-- `TelFits` with `okP` per field. -/
def TelFitsP (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (T : PSet.{4}) (σ : Nat → Nat) : List (Expr Nat) →
    (Nat → PSet.{4}) → List PSet.{4} → Prop
  | [], _, [] => True
  | A :: Ds, ρ, x :: xs => okP P μ fd T σ ρ A x ∧ TelFitsP P μ fd T σ Ds (vcons x ρ) xs
  | _, _, _ => False

/-- The universe of index tuples: all `fd.indices`-fitting tuples. -/
def UP (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) : PSet.{4} :=
  FitSetU (mkM P μ) σ fd.indices ρp

/-- The one-step operator on index tuples. -/
def PhiP (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (T : PSet.{4}) : PSet.{4} :=
  sep (fun t => ∃ (j : Nat), ∃ c : List (Expr Nat) × List (Expr Nat), ∃ xs,
      fd.ctors[j]? = some c ∧ TelFitsP P μ fd T σ c.1 ρp xs ∧
      Equiv t (tup (c.2.map (den (mkM P μ) σ (push xs ρp))))) (UP P μ fd σ ρp)

/-- The Prop-instance least fixed point. -/
noncomputable def DStarP (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) : PSet.{4} :=
  lfp (UP P μ fd σ ρp) (PhiP P μ fd σ ρp)

/-- `okP` is monotone in `T`. -/
theorem okP_mono {T T' : PSet.{4}} (h : Sub T T') (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (A : Expr Nat) (x : PSet.{4}) : okP P μ fd T σ ρ A x → okP P μ fd T' σ ρ A x := by
  unfold okP
  cases kindOf fd.fref A with
  | plain => exact id
  | direct => exact fun ⟨hx, hf, ht⟩ => ⟨hx, hf, h _ ht⟩
  | fn => exact fun ⟨hx, hf⟩ => ⟨hx, fun y hy => let ⟨hfy, hty⟩ := hf y hy; ⟨hfy, h _ hty⟩⟩

/-- `TelFitsP` is monotone in `T`. -/
theorem TelFitsP_mono {T T' : PSet.{4}} (h : Sub T T') (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{4}) → (xs : List PSet.{4}) →
    TelFitsP P μ fd T σ Ds ρ xs → TelFitsP P μ fd T' σ Ds ρ xs := by
  intro Ds
  induction Ds with
  | nil =>
      intro ρ xs h
      cases xs with
      | nil => exact h
      | cons x xs => exact False.elim h
  | cons A Ds ih =>
      intro ρ xs h
      cases xs with
      | nil => exact False.elim h
      | cons x xs =>
          obtain ⟨hx, hxs⟩ := h
          exact ⟨okP_mono P μ fd h σ ρ A x hx, ih (vcons x ρ) xs hxs⟩

/-- `okP` respects `T`-equivalence. -/
theorem okP_congrT {T T' : PSet.{4}} (h : Equiv T T') (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (A : Expr Nat) (x : PSet.{4}) : okP P μ fd T σ ρ A x → okP P μ fd T' σ ρ A x :=
  okP_mono P μ fd (fun z hz => mem_congr_right h hz) σ ρ A x

/-- `okP` respects pointwise environment and value equivalence. -/
theorem okP_congr {T : PSet.{4}} (σ : Nat → Nat)
    {ρ ρ' : Nat → PSet.{4}} (hρ : ∀ i, Equiv (ρ i) (ρ' i))
    {x x' : PSet.{4}} (hx : Equiv x x') {A : Expr Nat} :
    okP P μ fd T σ ρ A x → okP P μ fd T σ ρ' A x' := by
  unfold okP
  cases kindOf fd.fref A with
  | plain =>
      exact fun h => mem_congr_left hx
        (mem_congr_right (ed_congr (mkM P μ) (den_congr (mkM P μ) σ A hρ)) h)
  | direct =>
      exact fun ⟨hxe, hf, ht⟩ => ⟨hx.symm.trans hxe,
        (argsFitF_congr P μ fd σ hρ A).mp hf,
        mem_congr_left (tup_congr (LEq_map_den (mkM P μ) σ hρ _)) ht⟩
  | fn =>
      exact fun ⟨hxe, hf⟩ => ⟨hx.symm.trans hxe, fun y hy =>
        let ⟨hfy, hty⟩ := hf y (mem_congr_right
          (ed_congr (mkM P μ) (den_congr (mkM P μ) σ (piDom A) (fun i => (hρ i).symm))) hy)
        ⟨(argsFitF_congr P μ fd σ (vcons_congr (Equiv.refl y) hρ) (piCod A)).mp hfy,
          mem_congr_left (tup_congr (LEq_map_den (mkM P μ) σ
            (vcons_congr (Equiv.refl y) hρ) _)) hty⟩⟩

/-- `TelFitsP` respects pointwise environment and tuple equivalence. -/
theorem TelFitsP_congr {T : PSet.{4}} (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) → {ρ ρ' : Nat → PSet.{4}} →
    (∀ i, Equiv (ρ i) (ρ' i)) → {xs xs' : List PSet.{4}} →
    LEq xs xs' → TelFitsP P μ fd T σ Ds ρ xs → TelFitsP P μ fd T σ Ds ρ' xs' := by
  intro Ds
  induction Ds with
  | nil =>
      intro ρ ρ' hρ xs xs' hle h
      cases xs with
      | nil =>
          cases xs' with
          | nil => exact h
          | cons x' xs' => exact False.elim hle
      | cons x xs => exact False.elim h
  | cons A Ds ih =>
      intro ρ ρ' hρ xs xs' hle h
      cases xs with
      | nil => exact False.elim h
      | cons x xs =>
          cases xs' with
          | nil => exact False.elim hle
          | cons x' xs' =>
              obtain ⟨hxx', hxs⟩ := hle
              obtain ⟨hx, hxs'⟩ := h
              exact ⟨okP_congr P μ fd σ hρ hxx' hx,
                ih (vcons_congr hxx' hρ) hxs hxs'⟩

/-- `PhiP` is monotone on all sets (not only inside `UP`). -/
theorem PhiP_mono (σ : Nat → Nat) (ρp : Nat → PSet.{4}) {T T' : PSet.{4}}
    (h : Sub T T') : Sub (PhiP P μ fd σ ρp T) (PhiP P μ fd σ ρp T') := by
  show Sub (sep (fun t => ∃ (j : Nat), ∃ c : List (Expr Nat) × List (Expr Nat), ∃ xs,
      fd.ctors[j]? = some c ∧ TelFitsP P μ fd T σ c.1 ρp xs ∧
        Equiv t (tup (c.2.map (den (mkM P μ) σ (push xs ρp))))) (UP P μ fd σ ρp))
    (sep (fun t => ∃ (j : Nat), ∃ c : List (Expr Nat) × List (Expr Nat), ∃ xs,
      fd.ctors[j]? = some c ∧ TelFitsP P μ fd T' σ c.1 ρp xs ∧
        Equiv t (tup (c.2.map (den (mkM P μ) σ (push xs ρp))))) (UP P μ fd σ ρp))
  intro t ht
  obtain ⟨i, hp, he⟩ := mem_sep.mp ht
  obtain ⟨j, c, xs, hc, htf, ht'⟩ := hp
  exact mem_sep.mpr ⟨i, ⟨j, c, xs, hc,
    TelFitsP_mono P μ fd h σ c.1 ρp xs htf, ht'⟩, he⟩

/-- `PhiP` respects `T`-equivalence. -/
theorem PhiP_resp (σ : Nat → Nat) (ρp : Nat → PSet.{4}) {T T' : PSet.{4}}
    (h : Equiv T T') : Equiv (PhiP P μ fd σ ρp T) (PhiP P μ fd σ ρp T') :=
  Subset.equiv (PhiP_mono P μ fd σ ρp (fun z hz => mem_congr_right h hz))
    (PhiP_mono P μ fd σ ρp (fun z hz => mem_congr_right h.symm hz))

/-- `PhiP` is a Kleene operator on `UP`. -/
theorem PhiP_ktop (σ : Nat → Nat) (ρp : Nat → PSet.{4}) :
    KTOp (UP P μ fd σ ρp) (PhiP P μ fd σ ρp) where
  resp := fun X Y h => PhiP_resp P μ fd σ ρp h
  into := fun X _ z hz => mem_sep_subset
      (show z ∈ sep _ (UP P μ fd σ ρp) from hz)
  mono := fun X Y hXY _ => PhiP_mono P μ fd σ ρp hXY

/-- `DStarP` is the least fixed point of `PhiP`. -/
theorem DStarP_isLfp (σ : Nat → Nat) (ρp : Nat → PSet.{4}) :
    IsLfp (PhiP P μ fd σ ρp) (DStarP P μ fd σ ρp) := by
  have hK := PhiP_ktop P μ fd σ ρp
  refine ⟨lfp_closed hK, lfp_dense hK, fun Z hZ => ?_⟩
  have hZ' : Sub (sep (fun z => z ∈ Z) (UP P μ fd σ ρp)) (UP P μ fd σ ρp) :=
    fun z hz => mem_sep_subset hz
  have hsub : Sub (sep (fun z => z ∈ Z) (UP P μ fd σ ρp)) Z := by
    intro z hz
    obtain ⟨i, hp, he⟩ := mem_sep.mp hz
    exact mem_congr_left he hp
  have hc : Sub (PhiP P μ fd σ ρp (sep (fun z => z ∈ Z) (UP P μ fd σ ρp)))
      (sep (fun z => z ∈ Z) (UP P μ fd σ ρp)) := by
    intro t ht
    have hU : t ∈ UP P μ fd σ ρp := hK.into _ hZ' t ht
    have hZt : t ∈ Z := hZ _ (PhiP_mono P μ fd σ ρp hsub _ ht)
    obtain ⟨i, hi⟩ := hU
    exact mem_sep.mpr ⟨i, mem_congr_left hi.symm hZt, hi⟩
  intro z hz
  obtain ⟨i, hp, he⟩ := mem_sep.mp (lfp_least hZ' hc _ hz)
  exact mem_congr_left he hp

/-- `PhiP` respects pointwise parameter environments. -/
theorem PhiP_env (σ : Nat → Nat) {ρp ρp' : Nat → PSet.{4}}
    (h : ∀ i, Equiv (ρp i) (ρp' i)) (T : PSet.{4}) :
    Equiv (PhiP P μ fd σ ρp T) (PhiP P μ fd σ ρp' T) := by
  show Equiv (sep (fun t => ∃ (j : Nat), ∃ c : List (Expr Nat) × List (Expr Nat), ∃ xs,
      fd.ctors[j]? = some c ∧ TelFitsP P μ fd T σ c.1 ρp xs ∧
        Equiv t (tup (c.2.map (den (mkM P μ) σ (push xs ρp))))) (UP P μ fd σ ρp))
    (sep (fun t => ∃ (j : Nat), ∃ c : List (Expr Nat) × List (Expr Nat), ∃ xs,
      fd.ctors[j]? = some c ∧ TelFitsP P μ fd T σ c.1 ρp' xs ∧
        Equiv t (tup (c.2.map (den (mkM P μ) σ (push xs ρp'))))) (UP P μ fd σ ρp'))
  refine sep_congr
    (fun a b hab ⟨j, c, xs, hc, htf, ht⟩ => ⟨j, c, xs, hc,
      TelFitsP_congr P μ fd σ c.1 h (LEq.refl xs) htf,
      hab.symm.trans (ht.trans (tup_congr (LEq_map_den (mkM P μ) σ (push_congr (LEq.refl xs) h) _)))⟩)
    (fun a b hab ⟨j, c, xs, hc, htf, ht⟩ => ⟨j, c, xs, hc,
      TelFitsP_congr P μ fd σ c.1 (fun i => (h i).symm) (LEq.refl xs) htf,
      hab.symm.trans (ht.trans (tup_congr (LEq_map_den (mkM P μ) σ
        (push_congr (LEq.refl xs) (fun i => (h i).symm)) _)))⟩)
    (FitSetU_congr (mkM P μ) σ fd.indices h)

/-- `DStarP` respects pointwise parameter environments. -/
theorem DStarP_env (σ : Nat → Nat) {ρp ρp' : Nat → PSet.{4}}
    (h : ∀ i, Equiv (ρp i) (ρp' i)) :
    Equiv (DStarP P μ fd σ ρp) (DStarP P μ fd σ ρp') :=
  IsLfp.unique_of_congr (fun X => PhiP_env P μ fd σ h X)
    (DStarP_isLfp P μ fd σ ρp) (DStarP_isLfp P μ fd σ ρp')

/-- `okP` respects level valuations agreeing below `ar`. -/
theorem okP_levels (hB : FamBounded fd ar) {σ σ' : Nat → Nat}
    (hσ : ∀ i, i < ar → σ i = σ' i) (ρ : Nat → PSet.{4}) {A : Expr Nat}
    (hA : exprLevelsBounded ar A = true) (T : PSet.{4}) (x : PSet.{4}) :
    okP P μ fd T σ ρ A x → okP P μ fd T σ' ρ A x := by
  unfold okP
  cases hk : kindOf fd.fref A with
  | plain =>
      rw [den_levels_agree (mkM P μ) hσ A hA ρ]; exact id
  | direct =>
      intro ⟨hx, hf, ht⟩
      exact ⟨hx, (argsFitF_levels P μ fd hB hσ hA ρ).mp hf,
        mem_congr_left (by rw [map_den_levels (mkM P μ) hσ _
          (exprLevelsBounded_familyIdx hA) ρ]; exact Equiv.rfl) ht⟩
  | fn =>
      intro ⟨hx, hf⟩
      refine ⟨hx, fun y hy => ?_⟩
      have hy' : y ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ (piDom A)) := by
        rw [den_levels_agree (mkM P μ) hσ (piDom A)
          (exprLevelsBounded_piDom hA) ρ]; exact hy
      obtain ⟨hfy, hty⟩ := hf y hy'
      exact ⟨(argsFitF_levels P μ fd hB hσ (exprLevelsBounded_piCod hA) _).mp hfy,
        mem_congr_left (by rw [map_den_levels (mkM P μ) hσ
          (familyIdx fd.params.length (piCod A))
          (exprLevelsBounded_familyIdx
            (exprLevelsBounded_piCod hA)) (vcons y ρ)]; exact Equiv.rfl) hty⟩

/-- `TelFitsP` respects level valuations agreeing below `ar`. -/
theorem TelFitsP_levels (hB : FamBounded fd ar) {σ σ' : Nat → Nat}
    (hσ : ∀ i, i < ar → σ i = σ' i) {T : PSet.{4}} :
    (Ds : List (Expr Nat)) → ExprsBounded ar Ds → (ρ : Nat → PSet.{4}) →
    (xs : List PSet.{4}) → TelFitsP P μ fd T σ Ds ρ xs →
      TelFitsP P μ fd T σ' Ds ρ xs := by
  intro Ds
  induction Ds with
  | nil =>
      intro hb ρ xs h
      cases xs with
      | nil => exact h
      | cons x xs => exact False.elim h
  | cons A Ds ih =>
      intro hb ρ xs h
      cases xs with
      | nil => exact False.elim h
      | cons x xs =>
          obtain ⟨hx, hxs⟩ := h
          exact ⟨okP_levels P μ fd ar hB hσ ρ
            (hb A (List.mem_cons.mpr (Or.inl rfl))) _ x hx,
            ih (fun e he => hb e (List.mem_cons.mpr (Or.inr he))) (vcons x ρ) xs hxs⟩

/-- `PhiP` respects level valuations agreeing below `ar`. -/
theorem PhiP_levels (hB : FamBounded fd ar) {σ σ' : Nat → Nat}
    (hσ : ∀ i, i < ar → σ i = σ' i) (ρp : Nat → PSet.{4}) (T : PSet.{4}) :
    Equiv (PhiP P μ fd σ ρp T) (PhiP P μ fd σ' ρp T) := by
  show Equiv (sep (fun t => ∃ (j : Nat), ∃ c : List (Expr Nat) × List (Expr Nat), ∃ xs,
      fd.ctors[j]? = some c ∧ TelFitsP P μ fd T σ c.1 ρp xs ∧
        Equiv t (tup (c.2.map (den (mkM P μ) σ (push xs ρp))))) (UP P μ fd σ ρp))
    (sep (fun t => ∃ (j : Nat), ∃ c : List (Expr Nat) × List (Expr Nat), ∃ xs,
      fd.ctors[j]? = some c ∧ TelFitsP P μ fd T σ' c.1 ρp xs ∧
        Equiv t (tup (c.2.map (den (mkM P μ) σ' (push xs ρp))))) (UP P μ fd σ' ρp))
  refine sep_congr
    (fun a b hab ⟨j, c, xs, hc, htf, ht⟩ => ⟨j, c, xs, hc,
      TelFitsP_levels P μ fd ar hB hσ c.1
        (fun e he => (hB.ctors c (List.getElem?_mem hc)).1 e he) ρp xs htf,
      hab.symm.trans (ht.trans (tup_congr (by rw [map_den_levels (mkM P μ) hσ _
        (fun e he => (hB.ctors c (List.getElem?_mem hc)).2 e he) _]; exact LEq.refl _)))⟩)
    (fun a b hab ⟨j, c, xs, hc, htf, ht⟩ => ⟨j, c, xs, hc,
      TelFitsP_levels P μ fd ar hB (fun i hi => (hσ i hi).symm) c.1
        (fun e he => (hB.ctors c (List.getElem?_mem hc)).1 e he) ρp xs htf,
      hab.symm.trans (ht.trans (tup_congr (by rw [map_den_levels (mkM P μ) hσ _
        (fun e he => (hB.ctors c (List.getElem?_mem hc)).2 e he) _]; exact LEq.refl _)))⟩)
    (FitSetU_levels (mkM P μ) hσ fd.indices hB.indices ρp)

/-- `DStarP` respects level valuations agreeing below `ar`. -/
theorem DStarP_levels (hB : FamBounded fd ar) {σ σ' : Nat → Nat}
    (hσ : ∀ i, i < ar → σ i = σ' i) (ρp : Nat → PSet.{4}) :
    Equiv (DStarP P μ fd σ ρp) (DStarP P μ fd σ' ρp) :=
  IsLfp.unique_of_congr (fun X => PhiP_levels P μ fd ar hB hσ ρp X)
    (DStarP_isLfp P μ fd σ ρp) (DStarP_isLfp P μ fd σ' ρp)

/-- The Prop-instance family end value: the truth that the index tuple is
in the least fixed point. -/
def famEndP (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) : PSet.{4} :=
  tyv (tv (tup (lastVals fd.indices.length ρ) ∈
    DStarP P μ fd σ (shiftρ fd.indices.length ρ)))

/-- The Prop-instance family entry. -/
noncomputable def famLfpP (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) : List Nat → PSet.{4} :=
  fun vs => piLam (mkM P μ) (σOf vs) (famEndP P μ fd (σOf vs)) ρ0 (famType fd)

/-- `famEndP` respects pointwise environments. -/
theorem famEndP_envResp (σ : Nat → Nat) : EnvResp (famEndP P μ fd σ) := by
  intro ρ ρ' h
  show Equiv (tyv (tv (tup (lastVals fd.indices.length ρ) ∈
      DStarP P μ fd σ (shiftρ fd.indices.length ρ))))
    (tyv (tv (tup (lastVals fd.indices.length ρ') ∈
      DStarP P μ fd σ (shiftρ fd.indices.length ρ'))))
  refine tyv_congr (tv_congr ⟨fun hm => ?_, fun hm => ?_⟩)
  · exact mem_congr_left (tup_congr (lastVals_congr _ h))
      (mem_congr_right (DStarP_env P μ fd σ
        (fun i => h (i + fd.indices.length))) hm)
  · exact mem_congr_left (tup_congr (lastVals_congr _ h).symm)
      (mem_congr_right (DStarP_env P μ fd σ
        (fun i => h (i + fd.indices.length))).symm hm)

/-- `famEndP` respects level valuations agreeing below `ar`. -/
theorem famEndP_levels (hB : FamBounded fd ar) {σ σ' : Nat → Nat}
    (hσ : ∀ i, i < ar → σ i = σ' i) (ρ : Nat → PSet.{4}) :
    Equiv (famEndP P μ fd σ ρ) (famEndP P μ fd σ' ρ) :=
  tyv_congr (tv_congr ⟨fun hm =>
      mem_congr_right (DStarP_levels P μ fd ar hB hσ
        (shiftρ fd.indices.length ρ)) hm,
    fun hm => mem_congr_right (DStarP_levels P μ fd ar hB
      (fun i hi => (hσ i hi).symm) (shiftρ fd.indices.length ρ)) hm⟩)

end

end PSet

end Rcic.F3
