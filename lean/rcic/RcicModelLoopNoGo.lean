import rcic.RcicModelDenote

/-!
# RcicModelLoopNoGo — T2: the PSet model is refuted at Loop

Lane R1-b terminal segment (cc ruling, #6293 @01:45Z):

> r1b's set model is refuted at Loop. `pinLoopConv_erased` under
> `asnDefault` forces `P ≈ piSet(P, const P)`, impossible in a
> well-founded `PS`, at `pinLoopEnvT`.

**The soundness instance that fails:** `ConvT`-soundness at the
Loop cyclic conversion `X ≡ X→X` — `ConvT pinLoopEnvT _ [] X
(.pi X (.lift 0 1 X)) (sort 0)`, ambient `T = sort 0` (whose
`PropDen` disjunct is excluded by `sort_den_not_PropDen`), `hlhs`
giving `X : sort 0` (the `MemAt` level-tag side `tagOf ⟦X⟧ ≈
ord 1`), at any `⟦Γ⟧⁺` assignment `ν` — `Γ = []`, so `asnDefault`
in particular.  The soundness output `⟦X⟧ ≈ ⟦X→X⟧` then forces
`payloadOf ⟦X⟧ ≈ piSet (payloadOf ⟦X⟧) (const ·)`, impossible
for well-founded `PS`: the identity graph `mkLam id P` is always a
`piSet`-element, so `P` has an element `f`; functionality gives
`⟨f,b⟩ ∈ f`, and `f ∈ {f} ∈ ⟨f,b⟩ ∈ f` is an ∈-cycle
(`piSet_self_absurd`).

`closure_claim = 0`.
-/

namespace Rcic.Model

namespace PS

/-! ### Well-founded `∈` — no cycles -/

/-- No ∈-3-cycle: `x ∈ y ∈ z ∈ x` rotates to a cycle at `z ∈ x`,
contradicting well-founded induction. -/
theorem mem_no_three_cycle (x : PS) :
    ¬ ∃ y z : PS, x ∈ y ∧ y ∈ z ∧ z ∈ x :=
  mem_wf.induction x fun x ih => by
    show ¬ ∃ y z : PS, x ∈ y ∧ y ∈ z ∧ z ∈ x
    rintro ⟨y, z, h1, h2, h3⟩
    exact ih z h3 ⟨x, y, h3, h1, h2⟩

/-! ### The self-map fixed point -/

/-- The identity graph `mkLam id P` is `isFuncOnDep P (const P)`. -/
theorem isFuncOnDep_id (P : PS) :
    isFuncOnDep P (fun _ => P) (mkLam (fun a => a) P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, hi⟩ := ha
    exact ⟨a, ⟨i, hi⟩, ⟨i, ordPair_congr hi hi⟩⟩
  · rintro p ⟨i, hi⟩
    exact ⟨P.Func i, ⟨i, Equiv.refl _⟩, P.Func i,
      ⟨i, Equiv.refl _⟩, hi.symm⟩
  · intro a b b' h1 h2
    obtain ⟨i, hi⟩ := h1
    obtain ⟨j, hj⟩ := h2
    obtain ⟨hai, hbi⟩ := ordPair_equiv hi
    obtain ⟨haj, hbj⟩ := ordPair_equiv hj
    exact (hbi.symm.trans (hai.trans haj.symm)).trans hbj

/-- `mkLam id P` is a `piSet P (const P)`-element: the self-map
function space always contains the identity graph. -/
theorem mkLam_id_mem_piSet (P : PS) :
    mkLam (fun a => a) P ∈ piSet P (fun _ => P) := by
  have hpow : mkLam (fun a => a) P ∈
      powerset (prod P (sUnion (sImage (fun _ => P) P))) := by
    apply mem_powerset.mpr
    rintro y ⟨i, hi⟩
    exact mem_prod.mpr ⟨P.Func i, ⟨i, Equiv.refl _⟩, P.Func i,
      mem_sUnion.mpr ⟨P, ⟨i, Equiv.refl _⟩, ⟨i, Equiv.refl _⟩⟩,
      hi.symm⟩
  obtain ⟨i, hi⟩ := hpow
  exact mem_sep.mpr ⟨i,
    isFuncOnDep_equiv Equiv.rfl (fun _ _ _ => Equiv.refl _) hi.symm
      (isFuncOnDep_id P), hi⟩

/-- `P ≈ piSet P (const P)` is impossible in well-founded `PS`:
the identity graph inhabits the RHS, so `P` has an element `f`;
`isFuncOnDep` gives `⟨f,b⟩ ∈ f`, and `f ∈ {f} ∈ ⟨f,b⟩ ∈ f`
contradicts `mem_transGen_irrefl`.  This is the Loop fixpoint
equation `pinLoopConv_erased` would force. -/
theorem piSet_self_absurd {P : PS}
    (h : Equiv P (piSet P (fun _ => P))) : False := by
  have hf : mkLam (fun a => a) P ∈ P :=
    mem_congr_right h.symm (mkLam_id_mem_piSet P)
  obtain ⟨i, hi⟩ := hf
  have hFf : isFuncOnDep P (fun _ => P) (P.Func i) :=
    isFuncOnDep_equiv Equiv.rfl (fun _ _ _ => Equiv.refl _) hi.symm
      (isFuncOnDep_id P)
  obtain ⟨b, -, hab⟩ := hFf.1 (P.Func i) ⟨i, Equiv.refl _⟩
  have h1 : P.Func i ∈ singleton (P.Func i) :=
    mem_singleton.mpr (Equiv.refl _)
  have h2 : singleton (P.Func i) ∈ ordPair (P.Func i) b :=
    mem_pair.mpr (Or.inl (Equiv.refl _))
  exact mem_no_three_cycle _ ⟨singleton (P.Func i),
    ordPair (P.Func i) b, h1, h2, hab⟩

/-! ### The Loop pi-tag and the failing instance -/

/-- `⋃ ord 1 = ∅` — `ord 1`'s only element is `∅`. -/
theorem sUnion_ord_one : Equiv (sUnion (ord 1)) pempty := by
  apply ext; intro z; constructor
  · intro hz
    obtain ⟨t, ht, hzt⟩ := mem_sUnion.mp hz
    obtain ⟨k, hk, htk⟩ := ord_mem_iff.mp ht
    have : k = 0 := by omega
    subst this
    exact (not_mem_pempty (mem_congr_right htk hzt)).elim
  · exact fun hz => (not_mem_pempty hz).elim

/-- `imaxTag1` at Prop-level tags `ord 1, ord 1` is `∅`: every
`select`-candidate `t` is an `ord 1`-element, hence `≈ ∅`, and
`z ∈ t` dies. -/
theorem imaxTag1_prop : Equiv (imaxTag1 (ord 1) (ord 1)) pempty := by
  apply ext; intro z; constructor
  · intro hz
    obtain ⟨t, ht, hzt⟩ := mem_sUnion.mp hz
    obtain ⟨i, hp, he⟩ := mem_sep.mp ht
    obtain ⟨k, hk, htk⟩ := ord_mem_iff.mp (hp.1 sUnion_ord_one)
    have : k = 0 := by omega
    subst this
    exact (not_mem_pempty
      (mem_congr_right htk (mem_congr_right he.symm hzt))).elim
  · exact fun hz => (not_mem_pempty hz).elim

/-- `⟦sort l⟧` is never `PropDen`: its tag is `ord (u+2)`, not
`ord 1`.  The `PropDen` disjunct cannot save the Loop instance. -/
theorem sort_den_not_PropDen {μ : Nat → List Nat → PS}
    {σ : Nat → Nat} {ν : Nat → PS} (l : Declarative.Level) :
    ¬ PropDen (den μ σ ν (.sort l)) := by
  intro hP
  have htag : Equiv (tagOf (den μ σ ν (.sort l)))
      (ord (Declarative.evalTotal σ l + 2)) := by
    show Equiv (pfst (ordPair (ord (Declarative.evalTotal σ l + 2))
      (ord (Declarative.evalTotal σ l)))) _
    exact pfst_pair
  exact ord_ne (show Declarative.evalTotal σ l + 2 ≠ 1 by omega)
    (htag.symm.trans hP)

/-- **T2 — the failing soundness instance.**  `ConvT`-soundness at
the Loop cyclic conversion `X ≡ X→X` cannot hold in this model:
`tagOf ⟦X⟧ ≈ ord 1` (the `X : sort 0`/`hlhs` side) plus the
soundness output `⟦X⟧ ≈ ⟦pi X (lift 0 1 X)⟧` at `ν` forces
`payloadOf ⟦X⟧ ≈ piSet (payloadOf ⟦X⟧) (const ·)` —
`piSet_self_absurd`.  At `pinLoopEnvT`'s `ConvT` derivation under
`asnDefault` (`Γ = []`, so `Asn` is vacuous and any `ν` serves)
this is exactly `pinLoopConv_erased`. -/
theorem loop_conv_sound_fails {μ : Nat → List Nat → PS}
    {σ : Nat → Nat} {ν : Nat → PS} {X : Declarative.Expr Nat}
    (hX : Equiv (tagOf (den μ σ ν X)) (ord 1))
    (h : Equiv (den μ σ ν X)
      (den μ σ ν (.pi X (Declarative.lift 0 1 X)))) : False := by
  have hrep : ∀ x : PS,
      den μ σ (νcons x ν) (Declarative.lift 0 1 X) =
        den μ σ ν X := by
    intro x
    rw [den_lift, liftν_zero, shiftν_one_cons]
  -- the arrow `⟦X→X⟧` carries an ordinal tag: `imaxTag1 ord1 ord1 ≈ ∅`
  have htag : Equiv (imaxTag1 (tagOf (den μ σ ν X))
      (tagOf (den μ σ (νcons junk₀ ν) (Declarative.lift 0 1 X))))
      (ord 0) :=
    (imaxTag1_congr hX (by rw [hrep]; exact hX)).trans imaxTag1_prop
  -- `payloadOf ⟦X→X⟧ ≈ piSet (payloadOf ⟦X⟧) (const ·)`
  have hpay : Equiv
      (payloadOf (den μ σ ν (.pi X (Declarative.lift 0 1 X))))
      (piSet (payloadOf (den μ σ ν X))
        (fun _ => payloadOf (den μ σ ν X))) := by
    have hB : (fun a => payloadOf (den μ σ (νcons a ν)
        (Declarative.lift 0 1 X))) =
        fun _ => payloadOf (den μ σ ν X) :=
      funext fun a => congrArg payloadOf (hrep a)
    simp only [den]
    rw [hB]
    exact (payloadOf_congr
      (ordPair_congr htag (Equiv.refl _))).trans payloadOf_ctorVal
  exact piSet_self_absurd ((payloadOf_congr h).trans hpay)

end PS

end Rcic.Model
