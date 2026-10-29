import rcic.RcicAnnLR3IotaRecursorLaw
import rcic.RcicAnnLR3EnvironmentPortConditions

/-!
# Closedness of the recursor hook terms

`nbound k t` states that every free variable of the native term `t` is below `k`.
`denI_env_agree` is the exact consequence: denotations only read the first `k`
environment entries. Every `iotaTerm E r` is closed (`nbound_iotaTerm`), so the
recursor hook satisfies the two family-hook ports that the external evaluator laws
consume: `HookLiftFixed` and `HookEnvironmentIndependent` (`iotaHook_liftFixed`,
`iotaHook_environmentIndependent`). The recursor fixed point and the recursor body
are therefore independent of the ambient local environment (`fixValue_env`,
`bodyValue_env`). No admission or source judgment is used. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.IotaRecursor

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER

/-- All free variables are below `k`. -/
def nbound : Nat → Expr Nat → Bool
  | k, .bvar i => decide (i < k)
  | _, .sort _ => true
  | _, .const _ _ => true
  | k, .app f a => nbound k f && nbound k a
  | k, .lam A b => nbound k A && nbound (k + 1) b
  | k, .pi A B => nbound k A && nbound (k + 1) B
  | k, .letE A v b => nbound k A && nbound k v && nbound (k + 1) b
  | _, .lit _ => true

theorem nbound_mono : ∀ (t : Expr Nat) (k k' : Nat), nbound k t = true → k ≤ k' →
    nbound k' t = true
  | .bvar i, k, k', h, hk => by
      simp only [nbound, decide_eq_true_eq] at h ⊢; omega
  | .sort _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _ => rfl
  | .app f a, k, k', h, hk => by
      simp only [nbound, Bool.and_eq_true] at h ⊢
      exact ⟨nbound_mono f k k' h.1 hk, nbound_mono a k k' h.2 hk⟩
  | .lam A b, k, k', h, hk => by
      simp only [nbound, Bool.and_eq_true] at h ⊢
      exact ⟨nbound_mono A k k' h.1 hk, nbound_mono b (k + 1) (k' + 1) h.2 (by omega)⟩
  | .pi A B, k, k', h, hk => by
      simp only [nbound, Bool.and_eq_true] at h ⊢
      exact ⟨nbound_mono A k k' h.1 hk, nbound_mono B (k + 1) (k' + 1) h.2 (by omega)⟩
  | .letE A v b, k, k', h, hk => by
      simp only [nbound, Bool.and_eq_true] at h ⊢
      exact ⟨⟨nbound_mono A k k' h.1.1 hk, nbound_mono v k k' h.1.2 hk⟩,
        nbound_mono b (k + 1) (k' + 1) h.2 (by omega)⟩
  | .lit _, _, _, _, _ => rfl

theorem nbound_lift : ∀ (t : Expr Nat) (k c n : Nat), nbound k t = true →
    nbound (k + n) (lift c n t) = true
  | .bvar i, k, c, n, h => by
      simp only [nbound, decide_eq_true_eq] at h
      simp only [lift]
      split <;> simp only [nbound, decide_eq_true_eq] <;> omega
  | .sort _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _ => rfl
  | .app f a, k, c, n, h => by
      simp only [nbound, Bool.and_eq_true] at h
      simp only [lift, nbound, Bool.and_eq_true]
      exact ⟨nbound_lift f k c n h.1, nbound_lift a k c n h.2⟩
  | .lam A b, k, c, n, h => by
      simp only [nbound, Bool.and_eq_true] at h
      simp only [lift, nbound, Bool.and_eq_true]
      refine ⟨nbound_lift A k c n h.1, ?_⟩
      have := nbound_lift b (k + 1) (c + 1) n h.2
      rwa [Nat.add_right_comm] at this
  | .pi A B, k, c, n, h => by
      simp only [nbound, Bool.and_eq_true] at h
      simp only [lift, nbound, Bool.and_eq_true]
      refine ⟨nbound_lift A k c n h.1, ?_⟩
      have := nbound_lift B (k + 1) (c + 1) n h.2
      rwa [Nat.add_right_comm] at this
  | .letE A v b, k, c, n, h => by
      simp only [nbound, Bool.and_eq_true] at h
      simp only [lift, nbound, Bool.and_eq_true]
      refine ⟨⟨nbound_lift A k c n h.1.1, nbound_lift v k c n h.1.2⟩, ?_⟩
      have := nbound_lift b (k + 1) (c + 1) n h.2
      rwa [Nat.add_right_comm] at this
  | .lit _, _, _, _, _ => rfl

/-- A term bounded below the cutoff is fixed by lifting. -/
theorem lift_of_nbound : ∀ (t : Expr Nat) (k c n : Nat), nbound k t = true → k ≤ c →
    lift c n t = t
  | .bvar i, k, c, n, h, hc => by
      simp only [nbound, decide_eq_true_eq] at h
      simp only [lift]
      rw [if_neg (by omega)]
  | .sort _, _, _, _, _, _ => rfl
  | .const _ _, _, _, _, _, _ => rfl
  | .app f a, k, c, n, h, hc => by
      simp only [nbound, Bool.and_eq_true] at h
      simp only [lift, lift_of_nbound f k c n h.1 hc, lift_of_nbound a k c n h.2 hc]
  | .lam A b, k, c, n, h, hc => by
      simp only [nbound, Bool.and_eq_true] at h
      simp only [lift, lift_of_nbound A k c n h.1 hc,
        lift_of_nbound b (k + 1) (c + 1) n h.2 (by omega)]
  | .pi A B, k, c, n, h, hc => by
      simp only [nbound, Bool.and_eq_true] at h
      simp only [lift, lift_of_nbound A k c n h.1 hc,
        lift_of_nbound B (k + 1) (c + 1) n h.2 (by omega)]
  | .letE A v b, k, c, n, h, hc => by
      simp only [nbound, Bool.and_eq_true] at h
      simp only [lift, lift_of_nbound A k c n h.1.1 hc, lift_of_nbound v k c n h.1.2 hc,
        lift_of_nbound b (k + 1) (c + 1) n h.2 (by omega)]
  | .lit _, _, _, _, _, _ => rfl

/-- One direction of environment agreement; `denI_env_agree` is the equation. -/
theorem approxI_env_agree {ρ : EnvI} {t : Expr Nat} {c : CptI} (h : ApproxI ρ t c) :
    ∀ (k : Nat) (ρ' : EnvI), nbound k t = true → (∀ i, i < k → ρ i = ρ' i) →
      ApproxI ρ' t c := by
  induction h with
  | bot => intro _ _ _ _; exact .bot _ _
  | @bvar ρ i c hi =>
      intro k ρ' hb hag
      simp only [nbound, decide_eq_true_eq] at hb
      exact .bvar (by rw [← hag i hb]; exact hi)
  | sort => intro _ _ _ _; exact .sort _ _
  | pi _ _ ihA ihB =>
      intro k ρ' hb hag
      simp only [nbound, Bool.and_eq_true] at hb
      refine .pi (ihA k ρ' hb.1 hag) (fun s hs => ihB s hs (k + 1) _ hb.2 ?_)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
  | lam _ ihb =>
      intro k ρ' hb hag
      simp only [nbound, Bool.and_eq_true] at hb
      refine .lam (fun s hs => ihb s hs (k + 1) _ hb.2 ?_)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
  | app _ hs _ ihf iha =>
      intro k ρ' hb hag
      simp only [nbound, Bool.and_eq_true] at hb
      exact .app (ihf k ρ' hb.1 hag) hs (fun u hu => iha u hu k ρ' hb.2 hag)
  | const => intro _ _ _ _; exact .const _ _ _
  | appSpine _ _ ihf iha =>
      intro k ρ' hb hag
      simp only [nbound, Bool.and_eq_true] at hb
      exact .appSpine (ihf k ρ' hb.1 hag) (iha k ρ' hb.2 hag)
  | letE _ ih =>
      intro k ρ' hb hag
      simp only [nbound, Bool.and_eq_true] at hb
      exact .letE (ih k ρ' (by simp only [nbound, Bool.and_eq_true]; exact ⟨⟨hb.1.1, hb.2⟩, hb.1.2⟩)
        hag)
  | lit h _ =>
      intro _ ρ' _ _
      exact .lit (approxI_natExpand_env _ ρ' _ h)

theorem denI_env_agree (t : Expr Nat) (k : Nat) (ρ ρ' : EnvI) (hb : nbound k t = true)
    (hag : ∀ i, i < k → ρ i = ρ' i) : denI ρ t = denI ρ' t := by
  funext c
  apply propext
  exact ⟨fun h => approxI_env_agree h k ρ' hb hag,
    fun h => approxI_env_agree h k ρ hb (fun i hi => (hag i hi).symm)⟩

theorem denI_closed (t : Expr Nat) (hb : nbound 0 t = true) (ρ ρ' : EnvI) :
    denI ρ t = denI ρ' t :=
  denI_env_agree t 0 ρ ρ' hb (fun _ hi => absurd hi (Nat.not_lt_zero _))

/-! ## Closedness of the builders -/

theorem nbound_app_eq (k : Nat) (f a : Expr Nat) :
    nbound k (.app f a) = (nbound k f && nbound k a) := rfl

theorem nbound_lam_eq (k : Nat) (A b : Expr Nat) :
    nbound k (.lam A b) = (nbound k A && nbound (k + 1) b) := rfl

theorem nbound_bvar_of_lt {k i : Nat} (h : i < k) : nbound k (.bvar i) = true :=
  decide_eq_true h

theorem nbound_dummy (k : Nat) : nbound k dummy = true := rfl

theorem nbound_lams : ∀ (n : Nat) (b : Expr Nat) (k : Nat), nbound (k + n) b = true →
    nbound k (lams n b) = true
  | 0, b, k, h => h
  | n + 1, b, k, h => by
      show nbound k (.lam dummy (lams n b)) = true
      rw [nbound_lam_eq, Bool.and_eq_true]
      refine ⟨rfl, nbound_lams n b (k + 1) ?_⟩
      rwa [Nat.add_right_comm, Nat.add_assoc]

theorem nbound_drops : ∀ (n : Nat) (b : Expr Nat) (k : Nat), nbound k b = true →
    nbound k (drops n b) = true
  | 0, _, _, h => h
  | n + 1, b, k, h => by
      show nbound k (.lam dummy (lift 0 1 (drops n b))) = true
      rw [nbound_lam_eq, Bool.and_eq_true]
      exact ⟨rfl, nbound_lift _ k 0 1 (nbound_drops n b k h)⟩

theorem nbound_foldApps (k : Nat) : ∀ (f : Expr Nat) (xs : List (Expr Nat)),
    nbound k f = true → (∀ x ∈ xs, nbound k x = true) → nbound k (foldApps f xs) = true
  | _, [], hf, _ => hf
  | f, x :: xs, hf, hx => by
      show nbound k (foldApps (.app f x) xs) = true
      apply nbound_foldApps k (.app f x) xs
      · rw [nbound_app_eq, Bool.and_eq_true]; exact ⟨hf, hx x (by simp)⟩
      · exact fun y hy => hx y (List.mem_cons_of_mem x hy)

theorem nbound_argVars (base k : Nat) : ∀ n, base + n ≤ k → ∀ x ∈ argVars base n,
    nbound k x = true
  | 0, _, _, hx => absurd hx (List.not_mem_nil _)
  | n + 1, h, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · simp only [nbound, decide_eq_true_eq]; omega
      · exact nbound_argVars base k n (by omega) x hx

theorem nbound_replicate_dummy (k n : Nat) : ∀ x ∈ List.replicate n dummy, nbound k x = true := by
  intro x hx
  rw [(List.mem_replicate.mp hx).2]
  rfl

theorem nbound_fstN (k : Nat) : nbound k fstN = true :=
  nbound_mono fstN 0 k (by decide) (Nat.zero_le k)
theorem nbound_sndN (k : Nat) : nbound k sndN = true :=
  nbound_mono sndN 0 k (by decide) (Nat.zero_le k)
theorem nbound_yN (k : Nat) : nbound k yN = true :=
  nbound_mono yN 0 k (by decide) (Nat.zero_le k)

theorem nbound_selN (k : Nat) : ∀ (comps : List (Expr Nat)), (∀ c ∈ comps, nbound k c = true) →
    nbound k (selN comps) = true
  | [], _ => rfl
  | a :: as, h => by
      show nbound k (.lam dummy (.app (.app (.bvar 0) (lift 0 1 a)) (lift 0 1 (selN as)))) = true
      rw [nbound_lam_eq, Bool.and_eq_true, nbound_app_eq, Bool.and_eq_true, nbound_app_eq,
        Bool.and_eq_true]
      exact ⟨rfl, ⟨nbound_bvar_of_lt (by omega), nbound_lift a k 0 1 (h a (by simp))⟩,
        nbound_lift _ k 0 1 (nbound_selN k as (fun c hc => h c (List.mem_cons_of_mem a hc)))⟩

theorem nbound_nthN (k : Nat) : ∀ (c : Nat) (t : Expr Nat), nbound k t = true →
    nbound k (nthN c t) = true
  | 0, t, h => by
      show nbound k (.app fstN t) = true
      rw [nbound_app_eq, Bool.and_eq_true]
      exact ⟨nbound_fstN k, h⟩
  | c + 1, t, h => by
      apply nbound_nthN k c
      rw [nbound_app_eq, Bool.and_eq_true]
      exact ⟨nbound_sndN k, h⟩

theorem nbound_ctorN (c n : Nat) : nbound 0 (ctorN c n) = true := by
  unfold ctorN
  apply nbound_lams
  rw [nbound_lam_eq, Bool.and_eq_true]
  refine ⟨rfl, nbound_foldApps _ _ _ (nbound_nthN _ c _ (nbound_bvar_of_lt (by omega))) ?_⟩
  exact nbound_argVars 1 _ n (by omega)

theorem nbound_recCallN (np nm ni k d K : Nat) (major : Expr Nat) (hK : d + k + nm + 2 ≤ K)
    (hm : nbound K major = true) : nbound K (recCallN np nm ni k d major) = true := by
  unfold recCallN
  apply nbound_foldApps
  · simp only [nbound, decide_eq_true_eq]; omega
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact nbound_replicate_dummy K _ x hx
    · exact nbound_argVars _ K nm (by omega) x hx
    · exact nbound_replicate_dummy K _ x hx
    · rw [hx]; exact hm

theorem nbound_shapeCallN (np nm ni k p : Nat) (hp : p < k) :
    ∀ (s : FieldShape), ∀ x ∈ shapeCallN np nm ni k p s, nbound (k + nm + 2) x = true
  | .nonrecursive, x, hx => absurd hx (List.not_mem_nil _)
  | .recursive 0, x, hx => by
      rw [List.mem_singleton.mp hx]
      exact nbound_recCallN np nm ni k 0 _ _ (by omega)
        (by simp only [nbound, decide_eq_true_eq]; omega)
  | .recursive (a + 1), x, hx => by
      rw [List.mem_singleton.mp hx]
      apply nbound_lams
      apply nbound_recCallN np nm ni k (a + 1) _ _ (by omega)
      apply nbound_foldApps
      · simp only [nbound, decide_eq_true_eq]; omega
      · exact nbound_argVars 0 _ (a + 1) (by omega)

theorem nbound_caseArgsN (np nm ni k : Nat) : ∀ (i : Nat) (ss : List FieldShape),
    i + ss.length ≤ k → ∀ x ∈ caseArgsN np nm ni k i ss, nbound (k + nm + 2) x = true
  | _, [], _, x, hx => absurd hx (List.not_mem_nil _)
  | i, s :: ss, h, x, hx => by
      simp only [caseArgsN, List.mem_cons, List.mem_append] at hx
      simp only [List.length_cons] at h
      rcases hx with hx | hx | hx
      · rw [hx]; simp only [nbound, decide_eq_true_eq]; omega
      · exact nbound_shapeCallN np nm ni k (k - 1 - i) (by omega) s x hx
      · exact nbound_caseArgsN np nm ni k (i + 1) ss (by omega) x hx

theorem nbound_caseN (np nm ni j dcount : Nat) (shapes : List FieldShape) :
    nbound (nm + 2) (caseN np nm ni j dcount shapes) = true := by
  unfold caseN
  apply nbound_drops
  apply nbound_lams
  apply nbound_foldApps
  · simp only [nbound, decide_eq_true_eq]; omega
  · intro x hx
    have := nbound_caseArgsN np nm ni shapes.length 0 shapes (by omega) x hx
    rwa [show shapes.length + nm + 2 = nm + 2 + shapes.length by omega] at this

theorem nbound_compN (E : ResolvedEnvA) (r np nm ni c : Nat) :
    nbound (nm + 2) (compN E r np nm ni c) = true := by
  unfold compN
  split
  · split
    · exact nbound_caseN _ _ _ _ _ _
    · rfl
  · rfl

theorem nbound_genN (np nm ni : Nat) (comps : List (Expr Nat))
    (h : ∀ c ∈ comps, nbound (nm + 2) c = true) : nbound 0 (genN np nm ni comps) = true := by
  unfold genN
  rw [nbound_lam_eq, Bool.and_eq_true]
  refine ⟨rfl, nbound_drops _ _ _ (nbound_lams _ _ _ (nbound_drops _ _ _ ?_))⟩
  rw [nbound_lam_eq, Bool.and_eq_true, nbound_app_eq, Bool.and_eq_true]
  refine ⟨rfl, nbound_bvar_of_lt (by omega), ?_⟩
  have := nbound_selN (nm + 2) comps h
  rwa [show 0 + 1 + nm + 1 = nm + 2 by omega]

theorem nbound_compsN (E : ResolvedEnvA) (r np nm ni : Nat) :
    ∀ c ∈ compsN E r np nm ni, nbound (nm + 2) c = true := by
  intro c hc
  obtain ⟨c', _, rfl⟩ := List.mem_map.mp hc
  exact nbound_compN E r np nm ni c'

theorem nbound_recTermN (E : ResolvedEnvA) (r : Nat) : nbound 0 (recTermN E r) = true := by
  unfold recTermN
  split
  · rename_i np nm ni _
    rw [nbound_app_eq, Bool.and_eq_true]
    exact ⟨nbound_yN 0, nbound_genN np nm ni _ (nbound_compsN E r np nm ni)⟩
  · rfl

theorem nbound_iotaTerm (E : ResolvedEnvA) (r : Nat) : nbound 0 (iotaTerm E r) = true := by
  unfold iotaTerm
  split
  · split
    · exact nbound_ctorN _ _
    · exact nbound_recTermN E r
    · rfl
  · rfl

/-! ## The family-hook ports for the recursor hook -/

theorem iotaHook_liftFixed (E : ResolvedEnvA) :
    EnvironmentPortConditions.HookLiftFixed E (iotaHook E) :=
  fun _ r _ _ _ _ c => lift_of_nbound _ 0 c 1 (nbound_iotaTerm E r) (Nat.zero_le c)

theorem iotaHook_environmentIndependent (E : ResolvedEnvA) :
    EnvironmentPortConditions.HookEnvironmentIndependent E (iotaHook E) := by
  intro _ r _ _ _ _ ρ σ
  rw [show iotaHook E _ r _ _ = iotaTerm E r from rfl, denI_closed _ (nbound_iotaTerm E r) ρ σ]
  exact ValueEq.refl _

/-! ## Environment independence of the fixed point and the body -/

theorem fixValue_env (np nm ni : Nat) (comps : List (Expr Nat))
    (h : ∀ c ∈ comps, nbound (nm + 2) c = true) (ρ ρ' : EnvI) :
    fixValue (genN np nm ni comps) ρ = fixValue (genN np nm ni comps) ρ' := by
  rw [← fix_denI, ← fix_denI]
  exact denI_closed _ (by rw [nbound_app_eq, Bool.and_eq_true]; exact ⟨nbound_yN 0, nbound_genN _ _ _ _ h⟩)
    ρ ρ'

theorem bodyValue_env (np nm ni : Nat) (comps : List (Expr Nat))
    (h : ∀ c ∈ comps, nbound (nm + 2) c = true) (ρ ρ' : EnvI) (ms : List Value)
    (hms : ms.length = nm) (maj : Value) :
    bodyValue np nm ni comps ρ ms maj = bodyValue np nm ni comps ρ' ms maj := by
  unfold bodyValue
  rw [fixValue_env np nm ni comps h ρ ρ']
  rw [denI_env_agree (selN comps) (nm + 2) _ (bodyEnv (fixValue (genN np nm ni comps) ρ') ρ' ms maj)
    (nbound_selN _ comps h)]
  intro i hi
  unfold bodyEnv
  cases i with
  | zero => rfl
  | succ i =>
      show pushAll ms _ i = pushAll ms _ i
      by_cases hlt : i < ms.length
      · have h1 := pushAll_lookup ms (EnvI.cons (fixValue (genN np nm ni comps) ρ') ρ)
          (ms.length - 1 - i) (by omega)
        have h2 := pushAll_lookup ms (EnvI.cons (fixValue (genN np nm ni comps) ρ') ρ')
          (ms.length - 1 - i) (by omega)
        rw [show ms.length - 1 - (ms.length - 1 - i) = i by omega] at h1 h2
        rw [h1, h2]
      · rw [pushAll_ge ms _ i (by omega), pushAll_ge ms _ i (by omega)]
        rw [show i - ms.length = 0 by omega]
        rfl

end Rcic.Declarative.Ann.LR3.IotaRecursor
