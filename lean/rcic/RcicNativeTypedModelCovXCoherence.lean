import rcic.RcicNativeTypedModelCovXCore

/-!
# Coherence and type-readback transport of finite extensional views

The relation does not depend on which finite view is supplied. This permits
an existential wrapper without choosing a view, and without a new axiom.
Bottom keeps the landed empty-observation behavior. A non-bottom edge must
carry an actual view; global existence of views is not asserted here.

All recursion below is on the domain/codomain children of the given view.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovXAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit TypedModelAudit TypedModelCovRelAudit
open TypedModelCovNormReadbackAudit

variable {E : ResolvedEnv} {R : Readback} {n : Nat}

/-- Any two supplied finite views of the same native type give the same
relation. The proof compares their readback heads before using child IHs. -/
theorem lrSCoreCovXAt_view_iff (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) {Γ : LCtx} {A : Expr Nat}
    (v : CovXTypeView E R n Γ A) :
    ∀ (w : CovXTypeView E R n Γ A) (x y : Expr Nat) (c : CptT),
      LRSCoreCovXAt C v x y c ↔ LRSCoreCovXAt C w x y c := by
  induction v with
  | sort l hr =>
      intro w x y c
      cases w with
      | sort l' hr' =>
          have hl : l = l' := Expr.sort.inj
            (hNU _ hr (hL.sort_normal _ _) hr' (hL.sort_normal _ _))
          subst l'
          rfl
      | base Z hz hn hs hp => exact (hs ⟨l, hr⟩).elim
      | pi D B hp dom body cod =>
          exact (not_redR_pi_of_redR_sort hL hNU hr D B hp).elim
  | base Z hz hn hs hp =>
      intro w x y c
      cases w with
      | sort l hr => exact (hs ⟨l, hr⟩).elim
      | base Z' hz' hn' hs' hp' => rfl
      | pi D B hr dom body cod => exact (hp ⟨D, B, hr⟩).elim
  | pi D B hr dom body cod ihdom ihbody ihcod =>
      intro w x y c
      cases w with
      | sort l hs =>
          exact (not_redR_pi_of_redR_sort hL hNU hs D B hr).elim
      | base Z hz hn hs hp => exact (hp ⟨D, B, hr⟩).elim
      | pi D' B' hr' dom' body' cod' =>
          obtain ⟨rfl, rfl⟩ := redR_pi_unique hL hNU hr hr'
          constructor
          · intro h
            refine ⟨h.1, ?_⟩
            intro ds out ha N N' hN hN' hc hd
            have hd' : ∀ u ∈ ds, LRSCoreCovXAt C dom N N' u :=
              fun u hu => (ihdom dom' N N' u).mpr (hd u hu)
            obtain ⟨ho, ho'⟩ := h.2 ds out ha N N' hN hN' hc hd'
            exact ⟨(ihcod N hN (cod' N hN) _ _ out).mp ho,
              (ihcod N' hN' (cod' N' hN') _ _ out).mp ho'⟩
          · intro h
            refine ⟨h.1, ?_⟩
            intro ds out ha N N' hN hN' hc hd
            have hd' : ∀ u ∈ ds, LRSCoreCovXAt C dom' N N' u :=
              fun u hu => (ihdom dom' N N' u).mp (hd u hu)
            obtain ⟨ho, ho'⟩ := h.2 ds out ha N N' hN hN' hc hd'
            exact ⟨(ihcod N hN (cod' N hN) _ _ out).mpr ho,
              (ihcod N' hN' (cod' N' hN') _ _ out).mpr ho'⟩

/-- Agreement at normal readback heads is the exact input to reindexing a
finite view. This input concerns readback only, not model observations. -/
def CovXNormalHeadAgreement (R : Readback) (Γ : LCtx) (A A₀ : Expr Nat) : Prop :=
  ∀ Z, NormalR R Γ Z → (RedR R Γ A Z ↔ RedR R Γ A₀ Z)

theorem covXNormalHeadAgreement_of_red (hD : DetR R)
    {Γ : LCtx} {A A₀ : Expr Nat} (h : RedR R Γ A A₀) :
    CovXNormalHeadAgreement R Γ A A₀ := by
  intro Z hn
  constructor
  · intro hz
    have hd : DiamondR R := fun Δ _ _ _ h₁ h₂ => Or.inl (hD Δ h₁ h₂)
    obtain ⟨z, h₀, hZ⟩ := redR_confluent hd h hz
    obtain rfl := redR_of_normal hn hZ
    exact h₀
  · exact redR_trans h

/-- Reindex only the outer readback certificate; all hereditary children
are retained literally. No global view selection occurs. -/
def CovXTypeView.reindex (hL : ReadbackLaws E R)
    {Γ : LCtx} {A A₀ : Expr Nat} (h : CovXNormalHeadAgreement R Γ A A₀)
    (v : CovXTypeView E R n Γ A) : CovXTypeView E R n Γ A₀ :=
  match v with
  | .sort l hr => .sort l ((h _ (hL.sort_normal Γ l)).mp hr)
  | .base Z hr hn hs hp => .base Z ((h Z hn).mp hr) hn
      (fun ⟨l, hl⟩ => hs ⟨l, (h _ (hL.sort_normal Γ l)).mpr hl⟩)
      (fun ⟨D, B, hp'⟩ => hp ⟨D, B, (h _ (hL.pi_normal Γ D B)).mpr hp'⟩)
  | .pi D B hr dom body cod =>
      .pi D B ((h _ (hL.pi_normal Γ D B)).mp hr) dom body cod

theorem lrSCoreCovXAt_reindex_iff (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {A A₀ : Expr Nat} (h : CovXNormalHeadAgreement R Γ A A₀)
    (v : CovXTypeView E R n Γ A) (x y : Expr Nat) (c : CptT) :
    LRSCoreCovXAt C v x y c ↔ LRSCoreCovXAt C (v.reindex hL h) x y c := by
  have hs : (∃ l, RedR R Γ A (.sort l)) ↔ ∃ l, RedR R Γ A₀ (.sort l) := by
    constructor
    · rintro ⟨l, hl⟩
      exact ⟨l, (h _ (hL.sort_normal Γ l)).mp hl⟩
    · rintro ⟨l, hl⟩
      exact ⟨l, (h _ (hL.sort_normal Γ l)).mpr hl⟩
  cases v with
  | sort l hr =>
      exact and_congr Iff.rfl
        (lrSCoreCov_type_heads_iff C c hs (fun D B => h _ (hL.pi_normal Γ D B)))
  | base Z hr hn hns hnp =>
      exact lrSCoreCov_type_heads_iff C c hs (fun D B => h _ (hL.pi_normal Γ D B))
  | pi D B hr dom body cod => rfl

/-- The unindexed candidate requires a supplied finite view at every
non-bottom edge. Its bottom branch is exactly the empty observation. -/
def LRSCoreCovX (C : CovTyping E) (R : Readback) (n : Nat) (Γ : LCtx)
    (x y A : Expr Nat) (c : CptT) : Prop :=
  c = .bot ∨ ∃ v : CovXTypeView E R n Γ A, LRSCoreCovXAt C v x y c

theorem lrSCoreCovX_bot (C : CovTyping E) (Γ : LCtx) (x y A : Expr Nat) :
    LRSCoreCovX C R n Γ x y A .bot := Or.inl rfl

theorem lrSCoreCovX_of_view (C : CovTyping E) {Γ : LCtx} {A x y : Expr Nat}
    (v : CovXTypeView E R n Γ A) {c : CptT} (h : LRSCoreCovXAt C v x y c) :
    LRSCoreCovX C R n Γ x y A c := Or.inr ⟨v, h⟩

/-- Once a view is supplied, the existential wrapper has exactly its
meaning. Coherence discharges the choice of witness constructively. -/
theorem lrSCoreCovX_iff_at_view (C : CovTyping E) (hL : ReadbackLaws E R)
    (hNU : NormalUniqueR R) {Γ : LCtx} {A x y : Expr Nat}
    (v : CovXTypeView E R n Γ A) (c : CptT) :
    LRSCoreCovX C R n Γ x y A c ↔ LRSCoreCovXAt C v x y c := by
  constructor
  · rintro (rfl | ⟨w, hw⟩)
    · exact lrSCoreCovXAt_bot C v x y
    · exact (lrSCoreCovXAt_view_iff C hL hNU w v x y c).mp hw
  · exact lrSCoreCovX_of_view C v

theorem lrSCoreCovX_type_heads_iff (C : CovTyping E) (hL : ReadbackLaws E R)
    {Γ : LCtx} {A A₀ x y : Expr Nat}
    (h : CovXNormalHeadAgreement R Γ A A₀) (c : CptT) :
    LRSCoreCovX C R n Γ x y A c ↔ LRSCoreCovX C R n Γ x y A₀ c := by
  constructor
  · rintro (hb | ⟨v, hv⟩)
    · exact Or.inl hb
    · exact Or.inr ⟨v.reindex hL h, (lrSCoreCovXAt_reindex_iff C hL h v x y c).mp hv⟩
  · rintro (hb | ⟨v, hv⟩)
    · exact Or.inl hb
    · let h' : CovXNormalHeadAgreement R Γ A₀ A := fun Z hn => (h Z hn).symm
      exact Or.inr ⟨v.reindex hL h', (lrSCoreCovXAt_reindex_iff C hL h' v x y c).mp hv⟩

theorem lrSCoreCovX_type_readback_iff (C : CovTyping E) (hL : ReadbackLaws E R)
    (hD : DetR R) {Γ : LCtx} {A A₀ x y : Expr Nat}
    (h : RedR R Γ A A₀) (c : CptT) :
    LRSCoreCovX C R n Γ x y A c ↔ LRSCoreCovX C R n Γ x y A₀ c :=
  lrSCoreCovX_type_heads_iff C hL (covXNormalHeadAgreement_of_red hD h) c

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_X_COHERENCE_ROOTS
#print axioms lrSCoreCovXAt_view_iff
#print axioms CovXNormalHeadAgreement
#print axioms covXNormalHeadAgreement_of_red
#print axioms CovXTypeView.reindex
#print axioms lrSCoreCovXAt_reindex_iff
#print axioms LRSCoreCovX
#print axioms lrSCoreCovX_bot
#print axioms lrSCoreCovX_of_view
#print axioms lrSCoreCovX_iff_at_view
#print axioms lrSCoreCovX_type_heads_iff
#print axioms lrSCoreCovX_type_readback_iff
-- END RCIC_NATIVE_TYPED_MODEL_COV_X_COHERENCE_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovXAudit
