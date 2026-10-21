import rcic.RcicNativeTypedModelCovWConvControls
import rcic.RcicNativeReadbackCK2Inputs
import rcic.RcicNativeTypedModelCovWRigidLegacy

/-! A finite output invariant for the actual Eq minor.  The auxiliary
judgment records only the six argument positions of Eq's recursor; all
unrelated syntax has the unrestricted shape.  No native discrimination
or normalization premise is used. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

open FamModelAudit FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovWAudit TypedModelCovWIrrelAudit TypedModelCovWNativeAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open ReadbackCK2IndexAudit ReadbackCK2InputsAudit
open TypedModelCovWMatrixAudit

inductive CovWConvMCodeSafe : CptWConvR → Prop
  | bot : CovWConvMCodeSafe .bot
  | prop : CovWConvMCodeSafe (.sort .zero)
  | spine (r : Nat) (ls : List Level) (args : List CptWConvR) :
      CovWConvMCodeSafe (.spine r ls args)
  | lam {rows : List (List CptWConvR × CptWConvR)}
      (h : ∀ s ∈ rows, CovWConvMCodeSafe s.2) :
      CovWConvMCodeSafe (.lam rows)

inductive CovWConvMShape where
  | any
  | safe
  | fn (domain codomain : CovWConvMShape)
  deriving DecidableEq

def CovWConvMShape.Matches : CovWConvMShape → CptWConvR → Prop
  | .any, _ => True
  | .safe, c => CovWConvMCodeSafe c
  | .fn A B, c =>
      match c with
      | .bot => True
      | .spine _ _ _ => True
      | .lam rows => ∀ s ∈ rows,
          (∀ u ∈ s.1, A.Matches u) → B.Matches s.2
      | _ => False

def covWConvMRecShape : CovWConvMShape :=
  .fn .any (.fn .any (.fn .any (.fn .safe (.fn .any (.fn .any .safe)))))

inductive CovWConvMTerm (τ : Nat → CovWConvMShape) : Expr Nat → CovWConvMShape → Prop
  | any (e : Expr Nat) : CovWConvMTerm τ e .any
  | bvar (i : Nat) : CovWConvMTerm τ (.bvar i) (τ i)
  | prop : CovWConvMTerm τ (.sort .zero) .safe
  | eqRec (ls : List Level) : CovWConvMTerm τ (.const 65 ls) covWConvMRecShape
  | app {f a : Expr Nat} {A B : CovWConvMShape}
      (hf : CovWConvMTerm τ f (.fn A B)) (ha : CovWConvMTerm τ a A) :
      CovWConvMTerm τ (.app f a) B
  | safeApp {f a : Expr Nat} (hf : CovWConvMTerm τ f .safe) :
      CovWConvMTerm τ (.app f a) .safe

def covWConvMShapeCons (A : CovWConvMShape) (τ : Nat → CovWConvMShape) :
    Nat → CovWConvMShape
  | 0 => A
  | i + 1 => τ i

theorem covWConvM_matches_bot (A : CovWConvMShape) : A.Matches .bot := by
  cases A with
  | any => trivial
  | safe => exact .bot
  | fn => trivial

theorem covWConvM_matches_spine (A : CovWConvMShape)
    (r : Nat) (ls : List Level) (args : List CptWConvR) :
    A.Matches (.spine r ls args) := by
  cases A with
  | any => trivial
  | safe => exact .spine _ _ _
  | fn => trivial

theorem covWConvM_term_lift {τ : Nat → CovWConvMShape}
    {e : Expr Nat} {B : CovWConvMShape} (h : CovWConvMTerm τ e B)
    (A : CovWConvMShape) :
    CovWConvMTerm (covWConvMShapeCons A τ) (lift 0 1 e) B := by
  induction h with
  | any e => exact .any _
  | bvar i =>
      simpa only [lift, Nat.zero_le, ite_true, Nat.add_comm,
        covWConvMShapeCons] using
        (CovWConvMTerm.bvar (τ := covWConvMShapeCons A τ) (i + 1))
  | prop => exact .prop
  | eqRec ls => exact .eqRec ls
  | app hf ha ihf iha => exact .app ihf iha
  | safeApp hf ihf => exact .safeApp ihf

private theorem covWConvM_prefix_app_inv {τ : Nat → CovWConvMShape}
    {f x : Expr Nat} {A B : CovWConvMShape} {P : Prop}
    (hf : ∀ C, CovWConvMTerm τ f C → C = .any ∨ (C = .fn A B ∧ P))
    {C : CovWConvMShape} (h : CovWConvMTerm τ (.app f x) C) :
    C = .any ∨ (C = B ∧ P ∧ CovWConvMTerm τ x A) := by
  cases h with
  | any => exact Or.inl rfl
  | app hfun harg =>
      rcases hf _ hfun with he | ⟨he, hp⟩
      · cases he
      · cases he
        exact Or.inr ⟨rfl, hp, harg⟩
  | safeApp hfun =>
      rcases hf _ hfun with he | ⟨he, hp⟩ <;> cases he

private theorem covWConvM_prefix_any_inv {τ : Nat → CovWConvMShape}
    {f x : Expr Nat} {B : CovWConvMShape} {P : Prop}
    (hf : ∀ C, CovWConvMTerm τ f C → C = .any ∨ (C = .fn .any B ∧ P))
    {C : CovWConvMShape} (h : CovWConvMTerm τ (.app f x) C) :
    C = .any ∨ (C = B ∧ P) := by
  rcases covWConvM_prefix_app_inv hf h with he | ⟨he, hp, _⟩
  · exact Or.inl he
  · exact Or.inr ⟨he, hp⟩

theorem covWConvM_eq_call_inv {τ : Nat → CovWConvMShape}
    {ls : List Level} {A a motive minor b major : Expr Nat}
    {C : CovWConvMShape}
    (h : CovWConvMTerm τ
      (recCall (.const 65 ls) [A, a, motive, minor, b] major) C) :
    C = .any ∨ (C = .safe ∧ CovWConvMTerm τ minor .safe) := by
  have h0 : ∀ D, CovWConvMTerm τ (.const 65 ls) D →
      D = .any ∨ (D = covWConvMRecShape ∧ True) := by
    intro D hd
    cases hd with
    | any => exact Or.inl rfl
    | eqRec => exact Or.inr ⟨rfl, trivial⟩
  have h1 := fun D (hd : CovWConvMTerm τ (.app (.const 65 ls) A) D) =>
    covWConvM_prefix_any_inv h0 hd
  have h2 := fun D (hd : CovWConvMTerm τ (.app (.app (.const 65 ls) A) a) D) =>
    covWConvM_prefix_any_inv h1 hd
  have h3 := fun D (hd : CovWConvMTerm τ
      (.app (.app (.app (.const 65 ls) A) a) motive) D) =>
    covWConvM_prefix_any_inv h2 hd
  have h4 : ∀ D, CovWConvMTerm τ
      (.app (.app (.app (.app (.const 65 ls) A) a) motive) minor) D →
      D = .any ∨ (D = .fn .any (.fn .any .safe) ∧ CovWConvMTerm τ minor .safe) := by
    intro D hd
    rcases covWConvM_prefix_app_inv h3 hd with he | ⟨he, _, hm⟩
    · exact Or.inl he
    · exact Or.inr ⟨he, hm⟩
  have h5 := fun D (hd : CovWConvMTerm τ
      (.app (.app (.app (.app (.app (.const 65 ls) A) a) motive) minor) b) D) =>
    covWConvM_prefix_any_inv h4 hd
  exact covWConvM_prefix_any_inv h5 h

theorem covWConvM_term_const_inv {τ : Nat → CovWConvMShape}
    {e : Expr Nat} {C : CovWConvMShape} (h : CovWConvMTerm τ e C) :
    ∀ {r : Nat} {ls : List Level}, e = .const r ls →
      C = .any ∨ (r = 65 ∧ C = covWConvMRecShape) := by
  cases h with
  | any => intro r ls he; exact Or.inl rfl
  | bvar => intro r ls he; cases he
  | prop => intro r ls he; cases he
  | eqRec =>
      intro r ls he
      exact Or.inr ⟨(Expr.const.inj he).1.symm, rfl⟩
  | app => intro r ls he; cases he
  | safeApp => intro r ls he; cases he

theorem covWConvM_term_const_head {τ : Nat → CovWConvMShape}
    {e : Expr Nat} {C : CovWConvMShape} (h : CovWConvMTerm τ e C) :
    ∀ {r : Nat} {ls : List Level}, (appsSpine e).1 = .const r ls →
      C ≠ .any → r = 65 := by
  induction h with
  | any => intro r ls he hn; exact (hn rfl).elim
  | bvar => intro r ls he hn; cases he
  | prop => intro r ls he hn; cases he
  | eqRec => intro r ls he hn; exact (Expr.const.inj he).1.symm
  | app hf ha ihf iha =>
      intro r ls he hn
      exact ihf he (fun h => CovWConvMShape.noConfusion h)
  | safeApp hf ihf =>
      intro r ls he hn
      exact ihf he (fun h => CovWConvMShape.noConfusion h)

private theorem covWConvM_five_list (xs : List (Expr Nat)) (h : xs.length = 5) :
    ∃ A a mot minor b, xs = [A, a, mot, minor, b] := by
  rcases xs with _ | ⟨A, xs⟩
  · cases h
  rcases xs with _ | ⟨a, xs⟩
  · cases h
  rcases xs with _ | ⟨mot, xs⟩
  · cases h
  rcases xs with _ | ⟨minor, xs⟩
  · cases h
  rcases xs with _ | ⟨b, xs⟩
  · cases h
  have hn : xs.length = 0 := by simp only [List.length_cons] at h; omega
  obtain rfl := List.length_eq_zero.mp hn
  exact ⟨A, a, mot, minor, b, rfl⟩

/-- Every actual legacy Eq witness computes its fourth pre-major argument.
The structured witness is obtained from the checked legacy bridge, rather
than being postulated as an additional iota rule. -/
theorem covWConvM_legacy_eq_rhs (w : IotaWitness eqEnvT) (hr : w.recRef = 65) :
    ∃ A a mot minor b, w.preMajor = [A, a, mot, minor, b] ∧
      iotaRhsOf w = minor := by
  obtain ⟨hi⟩ := derivedIotaT_of_iotaWitness_envWfT pinEqGroupWfT w
  obtain ⟨v, hleft, hright⟩ := derivedIotaT_inv hi
  have hi := recCall_const_inj hleft
  have hrv : v.recRef = 65 := hi.1.trans hr
  have hp : v.preMajor = w.preMajor := hi.2.2.1
  obtain ⟨_, hlen, hfields, hschema⟩ := eqRec_model_schema v hrv
  have hwlen : w.preMajor.length = 5 := by rw [← hp]; exact hlen
  obtain ⟨A, a, mot, minor, b, hpre⟩ := covWConvM_five_list w.preMajor hwlen
  refine ⟨A, a, mot, minor, b, hpre, ?_⟩
  rw [← hright]
  unfold iotaRhsOfS
  rw [hschema, hfields, hp, hpre]
  change instantiate0 (lift 0 0 b) (lift 0 1 minor) = minor
  exact instantiate_lift_id 0 _ _

/-- Structural induction over the full grammar, including all application
and eta branches.  The only restricted input position is the actual minor
of the Eq recursor. -/
theorem covWConvM_shape_sound {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {e : Expr Nat} {c : CptWConvR} (h : ApproxTKWConv eqEnvT n Γ ρ e c) :
    ∀ (τ : Nat → CovWConvMShape) (C : CovWConvMShape),
      (∀ i u, ρ i u → (τ i).Matches u) →
      CovWConvMTerm τ e C → C.Matches c := by
  induction h with
  | bot => intro τ C hρ ht; exact covWConvM_matches_bot C
  | bvar hv =>
      intro τ C hρ ht
      cases ht with
      | any => trivial
      | bvar => exact hρ _ _ hv
  | sort Γ ρ l =>
      intro τ C hρ ht
      cases ht with
      | any => trivial
      | prop => exact .prop
  | const Γ ρ r ls hr hp =>
      intro τ C hρ ht
      exact covWConvM_matches_spine C _ _ _
  | @recursor Γ ρ w ls hi hn hpre hfields h ih =>
      intro τ C hρ ht
      rcases covWConvM_term_const_inv ht rfl with hc | ⟨hr, hc⟩
      · subst C; trivial
      · exact (hn (eqRec_model_schema w hr).1).elim
  | pi hA ht hb ihA ihb =>
      intro τ C hρ ht
      cases ht with
      | any => trivial
  | lam hA ht hn hb ihA ihb =>
      intro τ C hρ ht
      cases ht with
      | any => trivial
  | @app Γ ρ f x rows s hf hs hx ihf ihx =>
      intro τ C hρ ht
      cases ht with
      | any => trivial
      | app hft hxt =>
          exact ihf τ _ hρ hft s hs (fun u hu => ihx u hu τ _ hρ hxt)
      | safeApp hft =>
          have hm := ihf τ .safe hρ hft
          cases hm with
          | lam hrows => exact hrows s hs
  | appSpine hf hx hslot hfield ihf ihx =>
      intro τ C hρ ht
      exact covWConvM_matches_spine C _ _ _
  | @delta Γ ρ r ls m b c hd h ih =>
      intro τ C hρ ht
      rcases covWConvM_term_const_inv ht rfl with hc | ⟨hr, hc⟩
      · subst C; trivial
      · subst r
        obtain ⟨hm, _, hnrec, _⟩ := hd
        have hem : m = eqRecT := (Option.some.inj hm).symm
        subst m
        exact (hnrec rfl).elim
  | letE h ih =>
      intro τ C hρ ht
      cases ht with
      | any => trivial
  | lit h ih =>
      intro τ C hρ ht
      cases ht with
      | any => trivial
  | @iota Γ ρ c w T hl hr h ih =>
      intro τ C hρ ht
      by_cases hc : C = .any
      · subst C; trivial
      have hw : w.recRef = 65 := covWConvM_term_const_head ht (ls := w.ls)
        (by simp only [iotaLhsOf, recCall, appsSpine_foldApps_const]) hc
      obtain ⟨A, a, mot, minor, b, hp, hminor⟩ := covWConvM_legacy_eq_rhs w hw
      have ht' : CovWConvMTerm τ
          (recCall (.const 65 w.ls) [A, a, mot, minor, b] (ctorMajor w)) C := by
        simpa only [iotaLhsOf, hw, hp] using ht
      rcases covWConvM_eq_call_inv ht' with hc' | ⟨hc', hmt⟩
      · exact (hc hc').elim
      · subst C
        exact ih τ .safe hρ (by rw [hminor]; exact hmt)
  | @recursorPropK Γ ρ c w x T hK h ih =>
      intro τ C hρ ht
      by_cases hc : C = .any
      · subst C; trivial
      have hw : w.recRef = 65 := covWConvM_term_const_head ht (ls := w.ls)
        (by simp only [recCall, appsSpine_foldApps_const]) hc
      obtain ⟨A, a, mot, minor, b, hp, hminor⟩ := covWConvM_legacy_eq_rhs w hw
      have ht' : CovWConvMTerm τ
          (recCall (.const 65 w.ls) [A, a, mot, minor, b] x) C := by
        simpa only [hw, hp] using ht
      rcases covWConvM_eq_call_inv ht' with hc' | ⟨hc', hmt⟩
      · exact (hc hc').elim
      · subst C
        exact ih τ .safe hρ (by rw [hminor]; exact hmt)
  | @eta Γ ρ e D B a rows he hD ht hn hb ihD ihb =>
      intro τ C hρ hterm
      cases C with
      | any => trivial
      | safe =>
          apply CovWConvMCodeSafe.lam
          intro s hs
          apply ihb s hs (covWConvMShapeCons .any τ) .safe
          · intro i u hu
            cases i with
            | zero => trivial
            | succ i => exact hρ i u hu
          · exact .safeApp (covWConvM_term_lift hterm .any)
      | fn A C =>
          intro s hs hinput
          apply ihb s hs (covWConvMShapeCons A τ) C
          · intro i u hu
            cases i with
            | zero => exact hinput u hu
            | succ i => exact hρ i u hu
          · exact .app (covWConvM_term_lift hterm A) (.bvar 0)

theorem covWConvM_eq_call_safe {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {ls : List Level} {A a motive b major : Expr Nat} {c : CptWConvR}
    (h : ApproxTKWConv eqEnvT n Γ ρ
      (recCall (.const 65 ls) [A, a, motive, .sort .zero, b] major) c) :
    CovWConvMCodeSafe c := by
  apply covWConvM_shape_sound h (fun _ => .any) .safe (fun _ _ _ => trivial)
  exact .app (.app (.app (.app (.app (.app (.eqRec ls) (.any A))
    (.any a)) (.any motive)) .prop) (.any b)) (.any major)

private theorem covWConvM_eq_member_sort_body_zero
    {r : Nat} {ls : List Level} {m : CheckedMember} {u : Level}
    (hm : eqEnvT.members r = some m)
    (hu : piBody (instantiateLevels ls m.mtype) = .sort u) : u = .zero := by
  rw [eqEnvT_mem] at hm
  by_cases h65 : r = 65
  · simp only [h65, if_true] at hm
    cases hm
    cases hu
  · simp only [h65, if_false] at hm
    by_cases h64 : r = 64
    · simp only [h64, if_true] at hm
      cases hm
      cases hu
    · simp only [h64, if_false] at hm
      by_cases h63 : r = 63
      · simp only [h63, if_true] at hm
        cases hm
        change (.sort .zero : Expr Nat) = .sort u at hu
        exact (Expr.sort.inj hu).symm
      · simp only [h63, if_false] at hm
        cases hm

private theorem covWConvM_spine_not_universe_one
    {r : Nat} {ls : List Level} {args : List CptWConvR} {l : Level}
    (hu : UniverseWConv eqEnvT (.spine r ls args) l)
    (hl : LevelCode.ofLevel l = LevelCode.ofLevel (.succ .zero)) : False := by
  cases hu with
  | spine r ls args m u l hm hbody hlevel =>
      obtain rfl := covWConvM_eq_member_sort_body_zero hm hbody
      have hone := (LevelCode.ofLevel_eq_iff _ _).mp hl
      have he := (hlevel (fun _ => some 0)).trans (hone (fun _ => some 0))
      change (some 0 : Option Nat) = some 1 at he
      cases he

/-- Universe typing removes both the residual lambda bound and all Eq
environment spines.  This is finite code/environment inversion, not a
native conversion-discrimination theorem. -/
theorem covWConvM_safe_typed_shape {d : CptWConvR}
    (hs : CovWConvMCodeSafe d)
    (ht : CTySConv eqEnvT (covWConvCode d)
      (.sort (LevelCode.ofLevel (.succ .zero)))) :
    d = .bot ∨ d = .sort .zero := by
  cases hs with
  | bot => exact Or.inl rfl
  | prop => exact Or.inr rfl
  | spine r ls args =>
      obtain ⟨c, a, hc, ha, hraw⟩ := ht
      cases hraw with
      | bot => cases hc
      | sortTy hu hcoarse =>
          have hl := CptWConv.sort.inj ha
          cases hu with
          | bot => cases hc
          | sort => cases hc
          | pi => cases hc
          | spine r' ls' args' m u l hm hbody hlevel =>
              exact (covWConvM_spine_not_universe_one
                (.spine r' ls' args' m u _ hm hbody hlevel) hl).elim
      | function => cases ha
      | spine => cases ha
  | lam hrows =>
      obtain ⟨c, a, hc, ha, hraw⟩ := ht
      cases hraw with
      | bot => cases hc
      | sortTy hu hcoarse => cases hu <;> cases hc
      | function => cases ha
      | spine => cases ha

theorem covWConvM_eq_call_typed_shape {n : Nat} {Γ : LCtx} {ρ : EnvWConvR}
    {ls : List Level} {A a motive b major : Expr Nat} {c : CptWConv}
    (ht : CTySConv eqEnvT c (.sort (LevelCode.ofLevel (.succ .zero))))
    (h : CovWConvObservation eqEnvT n Γ ρ
      (recCall (.const 65 ls) [A, a, motive, .sort .zero, b] major) c) :
    c = .bot ∨ c = .sort (LevelCode.ofLevel .zero) := by
  obtain ⟨d, hd, ho⟩ := h
  have ht' : CTySConv eqEnvT (covWConvCode d)
      (.sort (LevelCode.ofLevel (.succ .zero))) := by rw [hd]; exact ht
  rcases covWConvM_safe_typed_shape (covWConvM_eq_call_safe ho) ht' with rfl | rfl
  · exact Or.inl hd.symm
  · exact Or.inr hd.symm

theorem covWConvM_at_sort_one (n : Nat) (ρ : EnvWConvR) {c : CptWConv}
    (ht : CTySConv eqEnvT c (.sort (LevelCode.ofLevel (.succ .zero)))) :
    CovWConvObservation eqEnvT n etaEqCtx ρ etaIndexRedex c ↔
      CovWConvObservation eqEnvT n etaEqCtx ρ covWMatrixMajorCtorCall c := by
  constructor
  · intro ho
    rcases covWConvM_eq_call_typed_shape ht ho with rfl | rfl
    · exact ⟨.bot, rfl, .bot _ _ _⟩
    · exact covWConv_observation_of (covWConv_eqIota_observed n ρ)
  · intro ho
    rcases covWConvM_eq_call_typed_shape ht ho with rfl | rfl
    · exact ⟨.bot, rfl, .bot _ _ _⟩
    · exact covWConv_observation_of (covWConv_etaIndex_K_observed n ρ)

private theorem covWConvM_sort_outer {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : EnvWConvR} {e : Expr Nat} {c : CptWConvR}
    (h : ApproxTKWConv E n Γ ρ e c) :
    ∀ {l : Level}, e = .sort l →
      c = .bot ∨ c = .sort l ∨ ∃ rows, c = .lam rows := by
  cases h with
  | bot => intro l he; exact Or.inl rfl
  | bvar => intro l he; cases he
  | sort => intro l he; cases he; exact Or.inr (Or.inl rfl)
  | const => intro l he; cases he
  | recursor => intro l he; cases he
  | pi => intro l he; cases he
  | lam => intro l he; cases he
  | app => intro l he; cases he
  | appSpine => intro l he; cases he
  | delta => intro l he; cases he
  | letE => intro l he; cases he
  | lit => intro l he; cases he
  | iota =>
      intro l he
      simp only [iotaLhsOf, recCall_eq_app] at he
      cases he
  | recursorPropK =>
      intro l he
      simp only [recCall_eq_app] at he
      cases he
  | eta => intro l he; exact Or.inr (Or.inr ⟨_, rfl⟩)

private theorem covWConvM_typed_at_bot {E : ResolvedEnv} {c : CptWConv}
    (ht : CTySConv E c .bot) : c = .bot := by
  obtain ⟨d, b, hd, hb, hraw⟩ := ht
  cases hraw with
  | bot => exact hd.symm
  | sortTy => cases hb
  | function => cases hb
  | spine => cases hb

private theorem covWConvM_typed_at_lam {E : ResolvedEnv} {c : CptWConv}
    {rows : List (List CptWConv × CptWConv)}
    (ht : CTySConv E c (.lam rows)) : c = .bot := by
  obtain ⟨d, b, hd, hb, hraw⟩ := ht
  cases hraw with
  | bot => exact hd.symm
  | sortTy => cases hb
  | function => cases hb
  | spine => cases hb

/-- Equality for every demanded output and every observation of the actual
type, for arbitrary valuation `ρ` in the fixed Eq environment and context. -/
theorem covWConv_M_typed_equality (n : Nat) (ρ : EnvWConvR) :
    CovWConvTypedInvariant eqEnvT n etaEqCtx ρ (.sort (.succ .zero))
      etaIndexRedex covWMatrixMajorCtorCall := by
  intro a ha c ht
  obtain ⟨d, hd, ho⟩ := ha
  rcases covWConvM_sort_outer ho rfl with rfl | rfl | ⟨rows, rfl⟩
  · have ha : a = .bot := hd.symm
    subst a
    obtain rfl := covWConvM_typed_at_bot ht
    exact ⟨fun _ => ⟨.bot, rfl, .bot _ _ _⟩,
      fun _ => ⟨.bot, rfl, .bot _ _ _⟩⟩
  · have ha : a = .sort (LevelCode.ofLevel (.succ .zero)) := hd.symm
    subst a
    exact covWConvM_at_sort_one n ρ ht
  · have ha : a = .lam (covWConvCodeRows rows) := hd.symm
    subst a
    obtain rfl := covWConvM_typed_at_lam ht
    exact ⟨fun _ => ⟨.bot, rfl, .bot _ _ _⟩,
      fun _ => ⟨.bot, rfl, .bot _ _ _⟩⟩

open TypedModelCovWRigidAudit

/-- The full M invariant in the revised grammar follows from the exact
Eq/assumption-context transport, including its local-head discipline. -/
theorem covWRigid_M_typed_equality (n : Nat) (ρ : EnvWConvR) :
    CovWRigidTypedInvariant eqEnvT n etaEqCtx ρ (.sort (.succ .zero))
      etaIndexRedex covWMatrixMajorCtorCall := by
  intro a ha c ht
  have ha' := (covWRigid_eq_observations_iff covWRigid_etaEq_localFree).mp ha
  have h := covWConv_M_typed_equality n ρ a ha' c ht
  constructor
  · intro ho
    exact (covWRigid_eq_observations_iff covWRigid_etaEq_localFree).mpr
      (h.mp ((covWRigid_eq_observations_iff covWRigid_etaEq_localFree).mp ho))
  · intro ho
    exact (covWRigid_eq_observations_iff covWRigid_etaEq_localFree).mpr
      (h.mpr ((covWRigid_eq_observations_iff covWRigid_etaEq_localFree).mp ho))

#print axioms covWConvM_legacy_eq_rhs
#print axioms covWConvM_shape_sound
#print axioms covWConvM_eq_call_safe
#print axioms covWConvM_safe_typed_shape
#print axioms covWConvM_eq_call_typed_shape
#print axioms covWConvM_at_sort_one
#print axioms covWConv_M_typed_equality
#print axioms covWRigid_M_typed_equality

end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit

-- BEGIN COVWRIGID GENERATED MISSING AXIOM ROOTS
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvMCodeSafe
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvMShape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvMShape.Matches
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvMRecShape
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.CovWConvMTerm
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvMShapeCons
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_matches_bot
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_matches_spine
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_term_lift
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_eq_call_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_term_const_inv
#print axioms Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit.covWConvM_term_const_head
-- END COVWRIGID GENERATED MISSING AXIOM ROOTS
