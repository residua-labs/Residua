import rcic.RcicNativeTypedModelCovWConvCore

/-! One-way structural erasure into the landed native grammar. This transfers
negative results only; positive observations are constructed in the new grammar.
Legacy iota is embedded through its checked environment bridge. -/
namespace Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open ReadbackCKAudit ReadbackCK2Audit ReadbackCK2ConvAudit
open TypedModelCovWAudit TypedModelCovTAudit TypedModelCovWIrrelAudit
open TypedModelCovWNativeAudit

private theorem rows_typed {E : ResolvedEnv} {a : CptWConvR}
    {rows : List (List CptWConvR × CptWConvR)}
    (h : ∀ s ∈ rows, ∀ u ∈ s.1, CTyWConvR E u a) :
    ∀ s ∈ rows.map covWConvRawRowErase, ∀ u ∈ s.1,
      CTyS E (covWIrrelErase u) (covWConvCoarse a) := by
  intro s hs u hu
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  exact covWConv_typing_forget (h t ht v hv)

private theorem rows_nonbottom {rows : List (List CptWConvR × CptWConvR)}
    (h : ∃ s ∈ rows, s.2 ≠ .bot) :
    ∃ s ∈ rows.map covWConvRawRowErase, s.2 ≠ .bot := by
  obtain ⟨s, hs, hn⟩ := h
  exact ⟨covWConvRawRowErase s, List.mem_map.mpr ⟨s, hs, rfl⟩,
    fun h => hn ((covWConvRaw_erase_bot_iff s.2).mp h)⟩

theorem covWConv_forget {E : ResolvedEnv} {n : Nat} (hW : EnvWfT E)
    {Γ : LCtx} {ρ : EnvWConvR} {e : Expr Nat} {c : CptWConvR}
    (h : ApproxTKWConv E n Γ ρ e c) :
    ApproxTKWNative E n Γ (covWConvRawEnvErase ρ) e (covWConvRawErase c) := by
  induction h with
  | bot => exact .bot _ _ _
  | bvar h => exact .bvar ⟨_, h, rfl⟩
  | sort Γ ρ l => exact .sort _ _ _
  | const Γ ρ r ls hr hp => exact .const _ _ _ _ hr hp
  | recursor ls hi hp hpre hf h ih =>
      rw [covWConvRaw_erase_curry]
      simp only [List.map_append, List.map_cons, List.map_nil, covWConvRaw_erase_ctorDemand]
      apply ApproxTKWNative.recursor ls hp
      · simpa only [List.length_map] using hpre
      · simpa only [List.length_map] using hf
      · rw [covWConvRaw_env_erase_push, covWConvRaw_env_erase_bot] at ih
        simpa only [List.map_append] using ih
  | pi hA ht hb ihA ihb =>
      simp only [covWConvRawErase, covWConvRaw_erase_rows]
      refine .pi ihA (rows_typed ht) ?_
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      simpa only [covWConvRaw_env_erase_cons, covWConvRawRowErase] using ihb t ht
  | lam hA ht hn hb ihA ihb =>
      simp only [covWConvRawErase, covWConvRaw_erase_rows]
      refine .lam ihA (rows_typed ht) (rows_nonbottom hn) ?_
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      simpa only [covWConvRaw_env_erase_cons, covWConvRawRowErase] using ihb t ht
  | app hf hs ha ihf iha =>
      simp only [covWConvRawErase, covWConvRaw_erase_rows] at ihf
      refine .app ihf (List.mem_map.mpr ⟨_, hs, rfl⟩) ?_
      intro u hu
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      exact iha v hv
  | appSpine hf ha hslot hfield ihf iha =>
      simp only [covWConvRawErase, covWConvRaw_erase_args] at ihf ⊢
      simp only [List.map_append, List.map_cons, List.map_nil]
      refine .appSpine ihf iha ?_ hfield
      intro hp
      have hb := hslot (by simpa only [List.length_map] using hp)
      exact congrArg covWConvRawErase hb
  | delta hd h ih =>
      exact .delta hd (by simpa only [covWConvRaw_env_erase_bot] using ih)
  | letE h ih => exact .letE ih
  | lit h ih => exact .lit ih
  | iota w hl hr h ih =>
      obtain ⟨hi⟩ := derivedIotaT_of_iotaWitness_envWfT hW w
      obtain ⟨v, hleft, hright⟩ := derivedIotaT_inv hi
      rw [← hright] at ih
      rw [← hleft]
      exact .iota v ih
  | recursorPropK w x hk h ih =>
      exact .recursorPropK w x hk.canon hk.nonconstructor hk.index hk.common ih
  | eta he hD ht hn hb ihD ihb =>
      simp only [covWConvRawErase, covWConvRaw_erase_rows]
      refine .eta he ihD (rows_typed ht) (rows_nonbottom hn) ?_
      intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      simpa only [covWConvRaw_env_erase_cons, covWConvRawRowErase] using ihb t ht

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_FORGET_ROOTS
#print axioms covWConv_forget
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_CONV_FORGET_ROOTS
end Rcic.Declarative.NativeValleys.TypedModelCovWConvAudit
