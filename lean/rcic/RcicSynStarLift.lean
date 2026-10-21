import rcic.RcicSynCR
import rcic.RcicSynClauseAlg

/-!
# Syntactic sortRow, build step 3an — `★ ↔* F↑` gives `★ ↔* F`

`research/rcic/semantic/S3_ES_ARMS.md` §39. `↔*_{E ∪ ≈}` reflects `lift`
at the normal form `★`, for every `TableWF` table.

Confluence modulo `≈` (`joinMod_of_convMod`, `confluent_eStep_wf`) turns
`★ ↔* F↑` into `★ →* x ≈ y *← F↑`. `★` is E-normal (`eStep_star_normal`),
so `x = ★`, and `≈` relates `★` only to itself, so `y = ★`. A reduction
out of a lifted term is a lifted reduction (`rstar_lift_inv`, from
`rStep_lift_inv` and `etaStep_lift_inv`, both landed in step 2), so
`F →* G` with `G↑ = ★`, hence `G = ★` (`lift_eq_star`).

§37's η arm uses it in place of the premise `hcoh`. `closure_claim`
stays 0.
-/

namespace Rcic.Syn

theorem appN_ne_star : (xs : List ETm) → (f : ETm) → f ≠ .star → ETm.appN f xs ≠ .star
  | [], _, hf => hf
  | _ :: xs, f, _ => appN_ne_star xs _ (by intro h; cases h)

theorem rStep_star_normal (tbl : List CRule) (t : ETm) : ¬ RStep tbl .star t := by
  intro h
  generalize hs : ETm.star = s at h
  cases h with
  | beta => cases hs
  | cr hc =>
      obtain ⟨c, ls, xs, rfl⟩ := cRoot_lhs hc
      exact appN_ne_star xs (.const c ls) (by intro h; cases h) hs.symm
  | appL => cases hs
  | appR => cases hs
  | lam => cases hs
  | piL => cases hs
  | piR => cases hs

theorem etaStep_star_normal (t : ETm) : ¬ EtaStep .star t := by
  intro h
  generalize hs : ETm.star = s at h
  cases h with
  | eta => cases hs
  | appL => cases hs
  | appR => cases hs
  | lam => cases hs
  | piL => cases hs
  | piR => cases hs

theorem eStep_star_normal (tbl : List CRule) (t : ETm) : ¬ EStep tbl .star t
  | .inl h => rStep_star_normal tbl t h
  | .inr h => etaStep_star_normal t h

theorem lvlEq_star_left {x : ETm} (h : LvlEq .star x) : x = .star := by
  cases h
  rfl

theorem eStep_lift_inv {tbl : List CRule} (hcl : TableClosed tbl) {c k : Nat} {F G : ETm}
    (h : EStep tbl (F.lift c k) G) : ∃ G', G = G'.lift c k ∧ EStep tbl F G' := by
  rcases h with h | h
  · obtain ⟨G', rfl, hG⟩ := rStep_lift_inv hcl h
    exact ⟨G', rfl, .inl hG⟩
  · obtain ⟨G', rfl, hG⟩ := etaStep_lift_inv h
    exact ⟨G', rfl, .inr hG⟩

theorem rstar_lift_inv {tbl : List CRule} (hcl : TableClosed tbl) {c k : Nat} {F G : ETm}
    (h : RStar (EStep tbl) (F.lift c k) G) :
    ∃ G', G = G'.lift c k ∧ RStar (EStep tbl) F G' := by
  generalize hT : F.lift c k = T at h
  induction h generalizing F with
  | refl =>
      exact ⟨F, hT.symm, .refl F⟩
  | step hs _ ih =>
      subst hT
      obtain ⟨M', rfl, hM⟩ := eStep_lift_inv hcl hs
      obtain ⟨G', rfl, hG⟩ := ih rfl
      exact ⟨G', rfl, .step hM hG⟩

theorem convMod_of_rstar_rev {R Q : ETm → ETm → Prop} {a b : ETm}
    (h : RStar R a b) : ConvMod R Q b a := by
  induction h with
  | refl a => exact .refl a
  | step h _ ih => exact .trans ih (.bwd h)

/-- `★ ↔* F↑` gives `★ ↔* F`. -/
theorem convMod_star_of_lift {tbl : List CRule} (hW : TableWF tbl) {c k : Nat} {F : ETm}
    (h : ConvMod (EStep tbl) LvlEq .star (F.lift c k)) :
    ConvMod (EStep tbl) LvlEq .star F := by
  obtain ⟨x, y, hx, hq, hy⟩ :=
    joinMod_of_convMod lvlEq_equivalence (eStep_strongSim hW.congr) (confluent_eStep_wf hW) h
  have hx' := rstar_of_normal (eStep_star_normal tbl) hx
  subst hx'
  have hy' := lvlEq_star_left hq
  subst hy'
  obtain ⟨G', hG, hs⟩ := rstar_lift_inv hW.closed hy
  have hG' : G' = .star := lift_eq_star hG.symm
  subst hG'
  exact convMod_of_rstar_rev hs

end Rcic.Syn

#print axioms Rcic.Syn.appN_ne_star
#print axioms Rcic.Syn.rStep_star_normal
#print axioms Rcic.Syn.etaStep_star_normal
#print axioms Rcic.Syn.eStep_star_normal
#print axioms Rcic.Syn.lvlEq_star_left
#print axioms Rcic.Syn.eStep_lift_inv
#print axioms Rcic.Syn.rstar_lift_inv
#print axioms Rcic.Syn.convMod_of_rstar_rev
#print axioms Rcic.Syn.convMod_star_of_lift
