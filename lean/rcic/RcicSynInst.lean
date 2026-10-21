import rcic.RcicSynCR

/-!
# Syntactic sortRow, build step 3b — substitution for E modulo `≈`

`research/rcic/semantic/S3_ES_ARMS.md` §3. `CvP.fsub` erases to a substitution of convertible
terms. The lemma that arm consumes is `convMod_inst`: `↔*_{E ∪ ≈}` is a congruence for `ETm.inst`
in both the body and the replacement. One step in the body stays one step (`eStep_inst`, using
`TableClosed` so a constant right-hand side is fixed by `inst`). One step in the replacement is
one step per occurrence (`convMod_of_estep_inst_repl`).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 one step under `inst` and `lift` -/

theorem rStep_inst {tbl : List CRule} (hcl : TableClosed tbl) {M M' : ETm}
    (h : RStep tbl M M') (j : Nat) (r : ETm) :
    RStep tbl (ETm.inst j r M) (ETm.inst j r M') := by
  induction h generalizing j r with
  | beta M N =>
      have hβ : ETm.inst j r (ETm.inst 0 N M) =
          ETm.inst 0 (ETm.inst j r N) (ETm.inst (j + 1) (ETm.lift 0 1 r) M) :=
        ETm.inst_inst 0 j N r (Nat.zero_le j) M
      rw [show ETm.inst j r (.app (.lam M) N) =
          .app (.lam (ETm.inst (j + 1) (r.lift 0 1) M)) (ETm.inst j r N) from rfl, hβ]
      exact .beta _ _
  | cr hc => exact .cr (cRoot_inst hcl hc j r)
  | appL a _ ih => exact .appL _ (ih j r)
  | appR f _ ih => exact .appR _ (ih j r)
  | lam _ ih => exact .lam (ih (j + 1) (r.lift 0 1))
  | piL b _ ih => exact .piL _ (ih j r)
  | piR a _ ih => exact .piR _ (ih (j + 1) (r.lift 0 1))

theorem rStep_lift {tbl : List CRule} (hcl : TableClosed tbl) {M M' : ETm}
    (h : RStep tbl M M') (c k : Nat) :
    RStep tbl (M.lift c k) (M'.lift c k) := by
  induction h generalizing c with
  | beta M N =>
      have hβ : ETm.lift c k (ETm.inst 0 N M) =
          ETm.inst 0 (ETm.lift c k N) (ETm.lift (c + 1) k M) :=
        ETm.lift_inst_low k c 0 N (Nat.zero_le c) M
      rw [show ETm.lift c k (.app (.lam M) N) =
          .app (.lam (ETm.lift (c + 1) k M)) (ETm.lift c k N) from rfl, hβ]
      exact .beta _ _
  | cr hc => exact .cr (cRoot_lift hcl hc c k)
  | appL a _ ih => exact .appL _ (ih c)
  | appR f _ ih => exact .appR _ (ih c)
  | lam _ ih => exact .lam (ih (c + 1))
  | piL b _ ih => exact .piL _ (ih c)
  | piR a _ ih => exact .piR _ (ih (c + 1))

theorem eStep_inst {tbl : List CRule} (hcl : TableClosed tbl) {M M' : ETm}
    (h : EStep tbl M M') (j : Nat) (r : ETm) :
    EStep tbl (ETm.inst j r M) (ETm.inst j r M') :=
  match h with
  | .inl hr => .inl (rStep_inst hcl hr j r)
  | .inr he => .inr (etaStep_inst he j r)

theorem eStep_lift {tbl : List CRule} (hcl : TableClosed tbl) {M M' : ETm}
    (h : EStep tbl M M') (c k : Nat) :
    EStep tbl (M.lift c k) (M'.lift c k) :=
  match h with
  | .inl hr => .inl (rStep_lift hcl hr c k)
  | .inr he => .inr (etaStep_lift he c k)

/-! ## §2 `↔*` is a congruence -/

theorem ConvMod.symm' {α : Type} {R Q : α → α → Prop}
    (hQ : ∀ {a b : α}, Q a b → Q b a) {a b : α} (h : ConvMod R Q a b) :
    ConvMod R Q b a := by
  induction h with
  | refl => exact .refl _
  | fwd hs => exact .bwd hs
  | bwd hs => exact .fwd hs
  | eqv hs => exact .eqv (hQ hs)
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1

theorem convMod_appL {tbl : List CRule} (a : ETm) {f f' : ETm}
    (h : ConvMod (EStep tbl) LvlEq f f') :
    ConvMod (EStep tbl) LvlEq (.app f a) (.app f' a) := by
  induction h with
  | refl => exact .refl _
  | fwd hs =>
      exact .fwd (match hs with
        | .inl hr => .inl (.appL a hr)
        | .inr he => .inr (.appL a he))
  | bwd hs =>
      exact .bwd (match hs with
        | .inl hr => .inl (.appL a hr)
        | .inr he => .inr (.appL a he))
  | eqv hs => exact .eqv (.app hs (LvlEq.rfl' a))
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem convMod_appR {tbl : List CRule} (f : ETm) {a a' : ETm}
    (h : ConvMod (EStep tbl) LvlEq a a') :
    ConvMod (EStep tbl) LvlEq (.app f a) (.app f a') := by
  induction h with
  | refl => exact .refl _
  | fwd hs =>
      exact .fwd (match hs with
        | .inl hr => .inl (.appR f hr)
        | .inr he => .inr (.appR f he))
  | bwd hs =>
      exact .bwd (match hs with
        | .inl hr => .inl (.appR f hr)
        | .inr he => .inr (.appR f he))
  | eqv hs => exact .eqv (.app (LvlEq.rfl' f) hs)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem convMod_lam {tbl : List CRule} {b b' : ETm}
    (h : ConvMod (EStep tbl) LvlEq b b') :
    ConvMod (EStep tbl) LvlEq (.lam b) (.lam b') := by
  induction h with
  | refl => exact .refl _
  | fwd hs =>
      exact .fwd (match hs with
        | .inl hr => .inl (.lam hr)
        | .inr he => .inr (.lam he))
  | bwd hs =>
      exact .bwd (match hs with
        | .inl hr => .inl (.lam hr)
        | .inr he => .inr (.lam he))
  | eqv hs => exact .eqv (.lam hs)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem convMod_piL {tbl : List CRule} (b : ETm) {a a' : ETm}
    (h : ConvMod (EStep tbl) LvlEq a a') :
    ConvMod (EStep tbl) LvlEq (.pi a b) (.pi a' b) := by
  induction h with
  | refl => exact .refl _
  | fwd hs =>
      exact .fwd (match hs with
        | .inl hr => .inl (.piL b hr)
        | .inr he => .inr (.piL b he))
  | bwd hs =>
      exact .bwd (match hs with
        | .inl hr => .inl (.piL b hr)
        | .inr he => .inr (.piL b he))
  | eqv hs => exact .eqv (.pi hs (LvlEq.rfl' b))
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem convMod_piR {tbl : List CRule} (a : ETm) {b b' : ETm}
    (h : ConvMod (EStep tbl) LvlEq b b') :
    ConvMod (EStep tbl) LvlEq (.pi a b) (.pi a b') := by
  induction h with
  | refl => exact .refl _
  | fwd hs =>
      exact .fwd (match hs with
        | .inl hr => .inl (.piR a hr)
        | .inr he => .inr (.piR a he))
  | bwd hs =>
      exact .bwd (match hs with
        | .inl hr => .inl (.piR a hr)
        | .inr he => .inr (.piR a he))
  | eqv hs => exact .eqv (.pi (LvlEq.rfl' a) hs)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem convMod_app {tbl : List CRule} {f f' a a' : ETm}
    (hf : ConvMod (EStep tbl) LvlEq f f') (ha : ConvMod (EStep tbl) LvlEq a a') :
    ConvMod (EStep tbl) LvlEq (.app f a) (.app f' a') :=
  (convMod_appL a hf).trans (convMod_appR f' ha)

theorem convMod_pi {tbl : List CRule} {a a' b b' : ETm}
    (ha : ConvMod (EStep tbl) LvlEq a a') (hb : ConvMod (EStep tbl) LvlEq b b') :
    ConvMod (EStep tbl) LvlEq (.pi a b) (.pi a' b') :=
  (convMod_piL b ha).trans (convMod_piR a' hb)

/-! ## §3 the substitution lemma -/

/-- one `E` step in the replacement is `↔*` in the instance, one step per free occurrence. -/
theorem convMod_of_estep_inst_repl {tbl : List CRule} (hcl : TableClosed tbl) :
    (M : ETm) → (j : Nat) → {r r' : ETm} → EStep tbl r r' →
      ConvMod (EStep tbl) LvlEq (ETm.inst j r M) (ETm.inst j r' M)
  | .bvar _, j, _, _, hr => by
      simp only [ETm.inst]
      split
      · exact .fwd hr
      · exact .refl _
  | .star, _, _, _, _ => .refl _
  | .sort _, _, _, _, _ => .refl _
  | .const _ _, _, _, _, _ => .refl _
  | .app f a, j, _, _, hr =>
      convMod_app (convMod_of_estep_inst_repl hcl f j hr)
        (convMod_of_estep_inst_repl hcl a j hr)
  | .lam b, j, _, _, hr =>
      convMod_lam (convMod_of_estep_inst_repl hcl b (j + 1) (eStep_lift hcl hr 0 1))
  | .pi a b, j, _, _, hr =>
      convMod_pi (convMod_of_estep_inst_repl hcl a j hr)
        (convMod_of_estep_inst_repl hcl b (j + 1) (eStep_lift hcl hr 0 1))

theorem convMod_inst_repl {tbl : List CRule} (hcl : TableClosed tbl) {r r' : ETm}
    (h : ConvMod (EStep tbl) LvlEq r r') (M : ETm) (j : Nat) :
    ConvMod (EStep tbl) LvlEq (ETm.inst j r M) (ETm.inst j r' M) := by
  induction h with
  | refl => exact .refl _
  | fwd hs => exact convMod_of_estep_inst_repl hcl M j hs
  | bwd hs => exact ConvMod.symm' LvlEq.symm' (convMod_of_estep_inst_repl hcl M j hs)
  | eqv hs => exact .eqv (LvlEq.inst' (LvlEq.rfl' M) j hs)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem convMod_inst_body {tbl : List CRule} (hcl : TableClosed tbl) {M M' : ETm}
    (h : ConvMod (EStep tbl) LvlEq M M') (j : Nat) (r : ETm) :
    ConvMod (EStep tbl) LvlEq (ETm.inst j r M) (ETm.inst j r M') := by
  induction h generalizing j r with
  | refl => exact .refl _
  | fwd hs => exact .fwd (eStep_inst hcl hs j r)
  | bwd hs => exact .bwd (eStep_inst hcl hs j r)
  | eqv hs => exact .eqv (LvlEq.inst' hs j (LvlEq.rfl' r))
  | trans _ _ ih1 ih2 => exact .trans (ih1 j r) (ih2 j r)

/-- `M ↔* M'` and `N ↔* N'` give `M[N] ↔* M'[N']`. -/
theorem convMod_inst {tbl : List CRule} (hcl : TableClosed tbl) {M M' N N' : ETm}
    (hM : ConvMod (EStep tbl) LvlEq M M') (hN : ConvMod (EStep tbl) LvlEq N N')
    (j : Nat) :
    ConvMod (EStep tbl) LvlEq (ETm.inst j N M) (ETm.inst j N' M') :=
  (convMod_inst_body hcl hM j N).trans (convMod_inst_repl hcl hN M' j)

end Rcic.Syn

#print axioms Rcic.Syn.rStep_inst
#print axioms Rcic.Syn.rStep_lift
#print axioms Rcic.Syn.eStep_inst
#print axioms Rcic.Syn.eStep_lift
#print axioms Rcic.Syn.ConvMod.symm'
#print axioms Rcic.Syn.convMod_appL
#print axioms Rcic.Syn.convMod_appR
#print axioms Rcic.Syn.convMod_lam
#print axioms Rcic.Syn.convMod_piL
#print axioms Rcic.Syn.convMod_piR
#print axioms Rcic.Syn.convMod_app
#print axioms Rcic.Syn.convMod_pi
#print axioms Rcic.Syn.convMod_of_estep_inst_repl
#print axioms Rcic.Syn.convMod_inst_repl
#print axioms Rcic.Syn.convMod_inst_body
#print axioms Rcic.Syn.convMod_inst
