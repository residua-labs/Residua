import rcic.RcicAnnLR3HeadLayer

/-!
# Positive LR3 normality under context insertions and worlds

These laws concern the injective lifts used by `WkSpecA`.  A legal insertion
preserves existing variable lookups even when the inserted declaration is a
local definition.  Static apartness and every positive normal constructor
therefore transport and reflect.  No K-guard decision, conversion
strengthening, or step-reflection premise is used.

The four contracts at the end are separate predicates on the explicit head
layer.  The contextual instance supplies all four.  This is distinct from
arbitrary typed substitution, whose raw laws are refuted separately.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace Rcic.Declarative.Ann.LR3

open Rcic.Declarative

private theorem nonAppA3_lift {e : ExprA} (c : Nat) :
    NonAppA3 e → NonAppA3 (liftA c 1 e)
  | .bvar i => by rw [liftA_bvar]; exact .bvar _
  | .sort l => .sort l
  | .const r ls => .const r ls
  | .lam A u b => .lam (liftA c 1 A) u (liftA (c + 1) 1 b)
  | .pi A u B v => .pi (liftA c 1 A) u (liftA (c + 1) 1 B) v
  | .letE A v b => .letE (liftA c 1 A) (liftA c 1 v) (liftA (c + 1) 1 b)
  | .lit t => .lit t

private theorem nonAppA3_of_lift {e : ExprA} (c : Nat)
    (h : NonAppA3 (liftA c 1 e)) : NonAppA3 e := by
  cases e with
  | bvar i => exact .bvar i
  | sort l => exact .sort l
  | const r ls => exact .const r ls
  | app f a => exact (h.not_app (liftA c 1 f) (liftA c 1 a) rfl).elim
  | lam A u b => exact .lam A u b
  | pi A u B v => exact .pi A u B v
  | letE A v b => exact .letE A v b
  | lit t => exact .lit t

private theorem nonConstA3_lift {e : ExprA} (c : Nat) :
    NonConstA3 e → NonConstA3 (liftA c 1 e)
  | .bvar i => by rw [liftA_bvar]; exact .bvar _
  | .sort l => .sort l
  | .app f a => .app (liftA c 1 f) (liftA c 1 a)
  | .lam A u b => .lam (liftA c 1 A) u (liftA (c + 1) 1 b)
  | .pi A u B v => .pi (liftA c 1 A) u (liftA (c + 1) 1 B) v
  | .letE A v b => .letE (liftA c 1 A) (liftA c 1 v) (liftA (c + 1) 1 b)
  | .lit t => .lit t

private theorem nonConstA3_of_lift {e : ExprA} (c : Nat)
    (h : NonConstA3 (liftA c 1 e)) : NonConstA3 e := by
  cases e with
  | bvar i => exact .bvar i
  | sort l => exact .sort l
  | const r ls => exact (h.not_const r ls rfl).elim
  | app f a => exact .app f a
  | lam A u b => exact .lam A u b
  | pi A u B v => exact .pi A u B v
  | letE A v b => exact .letE A v b
  | lit t => exact .lit t

private theorem const_of_lift_eq {e : ExprA} {r : Nat} {ls : List Level} (c : Nat)
    (h : liftA c 1 e = .const r ls) : e = .const r ls := by
  cases e with
  | bvar i => rw [liftA_bvar] at h; cases h
  | sort l => cases h
  | const r' ls' => exact h
  | app f a => cases h
  | lam A u b => cases h
  | pi A u B v => cases h
  | letE A v b => cases h
  | lit t => cases h

private theorem spineHead_lift {e : ExprA} {r : Nat} {ls : List Level} (c : Nat)
    (h : (appsSpineA e).1 = .const r ls) :
    (appsSpineA (liftA c 1 e)).1 = .const r ls := by
  rw [appsSpineA_liftA]
  simpa only [h, liftA]

private theorem spineHead_of_lift {e : ExprA} {r : Nat} {ls : List Level} (c : Nat)
    (h : (appsSpineA (liftA c 1 e)).1 = .const r ls) :
    (appsSpineA e).1 = .const r ls := by
  rw [appsSpineA_liftA] at h
  exact const_of_lift_eq c h

/-- Static certificates depend on syntax and the stored group, so their
target context may be arbitrary. -/
theorem apartA3_lift {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ : LCtxA} {e : ExprA} (c : Nat) (Δ : LCtxA) (h : ApartA3 E I n Γ e) :
    ApartA3 E I n Δ (liftA c 1 e) := by
  cases h with
  | nonApp h => exact .nonApp (nonAppA3_lift c h)
  | nonConstHead h =>
      apply ApartA3.nonConstHead
      simpa only [appsSpineA_liftA] using nonConstA3_lift c h
  | noGroup hh hg => exact .noGroup (spineHead_lift c hh) hg
  | short hh hm hn =>
      exact .short (spineHead_lift c hh) hm
        (by simpa only [appsSpineA_liftA, List.length_map] using hn)
  | long hh hm hn =>
      exact .long (spineHead_lift c hh) hm
        (by simpa only [appsSpineA_liftA, List.length_map] using hn)
  | layout hh hg hb => exact .layout (spineHead_lift c hh) hg hb

theorem apartA3_of_lift {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {Γ Δ : LCtxA} {e : ExprA} (c : Nat) (h : ApartA3 E I n Δ (liftA c 1 e)) :
    ApartA3 E I n Γ e := by
  cases h with
  | nonApp h => exact .nonApp (nonAppA3_of_lift c h)
  | nonConstHead h =>
      apply ApartA3.nonConstHead
      rw [appsSpineA_liftA] at h
      exact nonConstA3_of_lift c h
  | noGroup hh hg => exact .noGroup (spineHead_of_lift c hh) hg
  | short hh hm hn =>
      exact .short (spineHead_of_lift c hh) hm
        (by simpa only [appsSpineA_liftA, List.length_map] using hn)
  | long hh hm hn =>
      exact .long (spineHead_of_lift c hh) hm
        (by simpa only [appsSpineA_liftA, List.length_map] using hn)
  | layout hh hg hb => exact .layout (spineHead_of_lift c hh) hg hb

private theorem iota_lift_none_iff {I : IotaIfaceA} (hI : IotaLiftA I)
    (c : Nat) (e : ExprA) : I.fn (liftA c 1 e) = none ↔ I.fn e = none := by
  rw [hI c e]
  cases I.fn e <;> simp

private theorem unit_lift_none_iff (E : ResolvedEnvA) (c : Nat) (e : ExprA) :
    unitMinorA E (liftA c 1 e) = none ↔ unitMinorA E e = none := by
  rw [unitMinorA_liftA]
  cases unitMinorA E e <;> simp

private theorem lookup_insert_none_iff (d : LocalDeclA) (c : Nat) (Γ : LCtxA)
    (hc : c ≤ Γ.length) (i : Nat) :
    lookupValueA (insertAtA d c Γ) (shiftIdx c i) = none ↔ lookupValueA Γ i = none := by
  rw [lookupValueA_insertAtA d c Γ hc i]
  cases lookupValueA Γ i <;> simp

private theorem normal_neutral_lift_iff {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : IotaLiftA I) (d : LocalDeclA) {c : Nat} {Γ : LCtxA} (hc : c ≤ Γ.length)
    (e : ExprA) :
    (NormalA3 E I n (insertAtA d c Γ) (liftA c 1 e) ↔ NormalA3 E I n Γ e) ∧
    (NeutralA3 E I n (insertAtA d c Γ) (liftA c 1 e) ↔ NeutralA3 E I n Γ e) := by
  induction e with
  | bvar i =>
      simp only [liftA_bvar]
      have hn : NeutralA3 E I n (insertAtA d c Γ) (.bvar (shiftIdx c i)) ↔
          NeutralA3 E I n Γ (.bvar i) := by
        constructor
        · intro h
          cases h with
          | bvar _ hv => exact .bvar i ((lookup_insert_none_iff d c Γ hc i).mp hv)
        · intro h
          cases h with
          | bvar _ hv => exact .bvar _ ((lookup_insert_none_iff d c Γ hc i).mpr hv)
      refine ⟨?_, hn⟩
      constructor
      · intro h; cases h with
        | neutral h => exact .neutral (hn.mp h)
      · intro h; cases h with
        | neutral h => exact .neutral (hn.mpr h)
  | sort l =>
      refine ⟨⟨fun _ => .sort l, fun _ => .sort l⟩, ?_⟩
      constructor <;> intro h <;> cases h
  | const r ls =>
      have hn : NeutralA3 E I n (insertAtA d c Γ) (.const r ls) ↔
          NeutralA3 E I n Γ (.const r ls) := by
        constructor
        · intro h
          cases h with
          | missing _ _ hm => exact .missing r ls hm
          | rigid _ _ m hm ht => exact .rigid r ls m hm ht
          | noBody _ _ m hm hb => exact .noBody r ls m hm hb
        · intro h
          cases h with
          | missing _ _ hm => exact .missing r ls hm
          | rigid _ _ m hm ht => exact .rigid r ls m hm ht
          | noBody _ _ m hm hb => exact .noBody r ls m hm hb
      refine ⟨?_, hn⟩
      constructor
      · intro h; cases h with
        | neutral h => exact .neutral (hn.mp h)
      · intro h; cases h with
        | neutral h => exact .neutral (hn.mpr h)
  | app f a ihf iha =>
      have hn : NeutralA3 E I n (insertAtA d c Γ) (.app (liftA c 1 f) (liftA c 1 a)) ↔
          NeutralA3 E I n Γ (.app f a) := by
        constructor
        · intro h
          cases h with
          | appIdle hf ha hs hi hr =>
              exact .appIdle (ihf.2.mp hf) (apartA3_of_lift c ha)
                (by simpa only [structPosA_liftA] using hs)
                ((iota_lift_none_iff hI c (.app f a)).mp hi)
                (by simpa only [recAtMajorA_liftA] using hr)
          | appMajor hf ha hs hi hr hu hx =>
              exact .appMajor (ihf.2.mp hf) (apartA3_of_lift c ha)
                (by simpa only [structPosA_liftA] using hs)
                ((iota_lift_none_iff hI c (.app f a)).mp hi)
                (by simpa only [recAtMajorA_liftA] using hr)
                ((unit_lift_none_iff E c f).mp hu) (iha.1.mp hx)
        · intro h
          cases h with
          | appIdle hf ha hs hi hr =>
              exact .appIdle (ihf.2.mpr hf) (apartA3_lift c _ ha)
                (by simpa only [structPosA_liftA] using hs)
                ((iota_lift_none_iff hI c (.app f a)).mpr hi)
                (by simpa only [recAtMajorA_liftA] using hr)
          | appMajor hf ha hs hi hr hu hx =>
              exact .appMajor (ihf.2.mpr hf) (apartA3_lift c _ ha)
                (by simpa only [structPosA_liftA] using hs)
                ((iota_lift_none_iff hI c (.app f a)).mpr hi)
                (by simpa only [recAtMajorA_liftA] using hr)
                ((unit_lift_none_iff E c f).mpr hu) (iha.1.mpr hx)
      refine ⟨?_, hn⟩
      constructor
      · intro h; cases h with
        | neutral h => exact .neutral (hn.mp h)
      · intro h; cases h with
        | neutral h => exact .neutral (hn.mpr h)
  | lam A u b _ _ =>
      refine ⟨⟨fun _ => .lam A u b,
        fun _ => .lam (liftA c 1 A) u (liftA (c + 1) 1 b)⟩, ?_⟩
      constructor <;> intro h <;> cases h
  | pi A u B v _ _ =>
      refine ⟨⟨fun _ => .pi A u B v,
        fun _ => .pi (liftA c 1 A) u (liftA (c + 1) 1 B) v⟩, ?_⟩
      constructor <;> intro h <;> cases h
  | letE A v b _ _ _ =>
      constructor
      · constructor <;> intro h <;> cases h with
        | neutral h => cases h
      · constructor <;> intro h <;> cases h
  | lit t =>
      constructor
      · constructor <;> intro h <;> cases h with
        | neutral h => cases h
      · constructor <;> intro h <;> cases h

theorem normalA3_lift {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : IotaLiftA I) (d : LocalDeclA) {c : Nat} {Γ : LCtxA} (hc : c ≤ Γ.length)
    {e : ExprA} (h : NormalA3 E I n Γ e) :
    NormalA3 E I n (insertAtA d c Γ) (liftA c 1 e) :=
  (normal_neutral_lift_iff hI d hc e).1.mpr h

theorem normalA3_of_lift {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : IotaLiftA I) (d : LocalDeclA) {c : Nat} {Γ : LCtxA} (hc : c ≤ Γ.length)
    {e : ExprA} (h : NormalA3 E I n (insertAtA d c Γ) (liftA c 1 e)) :
    NormalA3 E I n Γ e :=
  (normal_neutral_lift_iff hI d hc e).1.mp h

theorem neutralA3_lift {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : IotaLiftA I) (d : LocalDeclA) {c : Nat} {Γ : LCtxA} (hc : c ≤ Γ.length)
    {e : ExprA} (h : NeutralA3 E I n Γ e) :
    NeutralA3 E I n (insertAtA d c Γ) (liftA c 1 e) :=
  (normal_neutral_lift_iff hI d hc e).2.mpr h

theorem neutralA3_of_lift {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : IotaLiftA I) (d : LocalDeclA) {c : Nat} {Γ : LCtxA} (hc : c ≤ Γ.length)
    {e : ExprA} (h : NeutralA3 E I n (insertAtA d c Γ) (liftA c 1 e)) :
    NeutralA3 E I n Γ e :=
  (normal_neutral_lift_iff hI d hc e).2.mp h

theorem normalA3_wk {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : IotaLiftA I) (ρ : WkSpecA) (Γ : LCtxA) (hρ : WkSpecA.ok ρ Γ)
    {e : ExprA} (h : NormalA3 E I n Γ e) :
    NormalA3 E I n (wkCtxA ρ Γ) (wkExprA ρ e) := by
  induction ρ generalizing Γ e with
  | nil => exact h
  | cons dc ρ ih =>
      obtain ⟨d, c⟩ := dc
      exact ih (insertAtA d c Γ) hρ.2 (normalA3_lift hI d hρ.1 h)

theorem normalA3_of_wk {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : IotaLiftA I) (ρ : WkSpecA) (Γ : LCtxA) (hρ : WkSpecA.ok ρ Γ)
    {e : ExprA} (h : NormalA3 E I n (wkCtxA ρ Γ) (wkExprA ρ e)) :
    NormalA3 E I n Γ e := by
  induction ρ generalizing Γ e with
  | nil => exact h
  | cons dc ρ ih =>
      obtain ⟨d, c⟩ := dc
      exact normalA3_of_lift hI d hρ.1 (ih (insertAtA d c Γ) hρ.2 h)

theorem neutralA3_wk {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : IotaLiftA I) (ρ : WkSpecA) (Γ : LCtxA) (hρ : WkSpecA.ok ρ Γ)
    {e : ExprA} (h : NeutralA3 E I n Γ e) :
    NeutralA3 E I n (wkCtxA ρ Γ) (wkExprA ρ e) := by
  induction ρ generalizing Γ e with
  | nil => exact h
  | cons dc ρ ih =>
      obtain ⟨d, c⟩ := dc
      exact ih (insertAtA d c Γ) hρ.2 (neutralA3_lift hI d hρ.1 h)

theorem neutralA3_of_wk {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : IotaLiftA I) (ρ : WkSpecA) (Γ : LCtxA) (hρ : WkSpecA.ok ρ Γ)
    {e : ExprA} (h : NeutralA3 E I n (wkCtxA ρ Γ) (wkExprA ρ e)) :
    NeutralA3 E I n Γ e := by
  induction ρ generalizing Γ e with
  | nil => exact h
  | cons dc ρ ih =>
      obtain ⟨d, c⟩ := dc
      exact neutralA3_of_lift hI d hρ.1 (ih (insertAtA d c Γ) hρ.2 h)

def NormalInsertA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (d : LocalDeclA) (c : Nat) (Γ : LCtxA), c ≤ Γ.length → ∀ e,
    H.normal Γ e → H.normal (insertAtA d c Γ) (liftA c 1 e)

def NormalInsertReflectA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (d : LocalDeclA) (c : Nat) (Γ : LCtxA), c ≤ Γ.length → ∀ e,
    H.normal (insertAtA d c Γ) (liftA c 1 e) → H.normal Γ e

def NormalWorldA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (ρ : WkSpecA) (Γ : LCtxA), WkSpecA.ok ρ Γ → ∀ e,
    H.normal Γ e → H.normal (wkCtxA ρ Γ) (wkExprA ρ e)

def NormalWorldReflectA3 (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat)
    (H : HeadLayerA3 E I n) : Prop :=
  ∀ (ρ : WkSpecA) (Γ : LCtxA), WkSpecA.ok ρ Γ → ∀ e,
    H.normal (wkCtxA ρ Γ) (wkExprA ρ e) → H.normal Γ e

theorem contextualHeadLayerA3_normalInsert {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : IotaLiftA I) : NormalInsertA3 E I n (contextualHeadLayerA3 E I n) :=
  fun d _ _ hc _ h => normalA3_lift hI d hc h

theorem contextualHeadLayerA3_normalInsertReflect
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} (hI : IotaLiftA I) :
    NormalInsertReflectA3 E I n (contextualHeadLayerA3 E I n) :=
  fun d _ _ hc _ h => normalA3_of_lift hI d hc h

theorem contextualHeadLayerA3_normalWorld {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (hI : IotaLiftA I) : NormalWorldA3 E I n (contextualHeadLayerA3 E I n) :=
  fun ρ Γ hρ _ h => normalA3_wk hI ρ Γ hρ h

theorem contextualHeadLayerA3_normalWorldReflect
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} (hI : IotaLiftA I) :
    NormalWorldReflectA3 E I n (contextualHeadLayerA3 E I n) :=
  fun ρ Γ hρ _ h => normalA3_of_wk hI ρ Γ hρ h

#print axioms apartA3_lift
#print axioms apartA3_of_lift
#print axioms normalA3_lift
#print axioms normalA3_of_lift
#print axioms neutralA3_lift
#print axioms neutralA3_of_lift
#print axioms normalA3_wk
#print axioms normalA3_of_wk
#print axioms neutralA3_wk
#print axioms neutralA3_of_wk
#print axioms NormalInsertA3
#print axioms NormalInsertReflectA3
#print axioms NormalWorldA3
#print axioms NormalWorldReflectA3
#print axioms contextualHeadLayerA3_normalInsert
#print axioms contextualHeadLayerA3_normalInsertReflect
#print axioms contextualHeadLayerA3_normalWorld
#print axioms contextualHeadLayerA3_normalWorldReflect

end Rcic.Declarative.Ann.LR3
