/-
RCIC 06 §16 — progress for the intrinsic machine (#6029 K3, segment 2).

Owner text (06 §16): "progress: well-typed nonfinal configs have a step".
06 §14: "There is no `none`, stuck, trap, or fuel-exhausted source outcome."

A typed configuration (`Config S T`, `ScmMachine`) is well-typed by
construction. One step of it ends in an integrity residue in exactly two
situations, and this file names both in ONE per-program well-formedness
predicate `WF` (over expressions, frames, continuations, configurations,
bodies):
  * an external call (`FnRef.external`): this bundle holds no body for it
    (06 §7: a closed bundle contains the transitive closure of groups; the
    carrier refuses `[rcic_scm_core_external_call]`);
  * a primitive or `boundedFix` OCCURRING in the configuration whose
    residues the catalog does not type with the unit payload (06 §6
    "payload types come from the catalog") → `PrimCat S op` at each `prim`
    node / `primArgsF` frame, `NlbCat S` at each `boundedFix` node /
    `fixI`, `fixL` frame.
The catalog premise is per program (#6029 K3 HOLD item 2a): a program with no
primitive and no bounded fix is `WF` over the empty catalog (witness in
`ScmNoStuck`). Under `WF`, `stepI` is never an integrity residue: it is a next
configuration or a final outcome (`progress`); `WF` is preserved by steps
(`NoStuck.stepI_wf`).
-/
import rcic.ScmMachine

namespace Rcic.Scm.Progress
open Rcic.Scm

/-! ## The well-formedness premises -/

/-- Every residue in the primitive's direct row `primRow` (06 §11) is
    catalogued with the unit payload (06 §6 "payload types come from the
    catalog"), for ONE primitive. The transcribed law `primLaw` raises only
    refs of `primRow` (`primLaw_raised_mem`): `mod`'s `signed_overflow` arm
    is unreachable (`fmod_inI64`, #6029 K3 HOLD item 2b), and `str_len` /
    `bytes_len` raise `signed_overflow` for a length outside `i64`, which is
    their direct row by E-06LenRows (00 §19.7). The former `primLawRow` (the
    law's row before E-06LenRows) is retired: it equals `primRow`. A program
    that does not USE `str_len` / `bytes_len` needs no `signed_overflow`
    catalogued on their account (`PrimCat` is per primitive occurrence). -/
def PrimCat (S : Sig) (op : PrimOp) : Prop :=
  ∀ r : RaisedRef, r ∈ primRow op → catalogPt S.catalog r = some unitTy

/-- `negative_loop_bound` (06 §12) is catalogued with the unit payload. -/
def NlbCat (S : Sig) : Prop := catalogPt S.catalog "negative_loop_bound" = some unitTy

end Rcic.Scm.Progress

namespace Rcic.Scm

section WF
variable {S : Sig}

mutual
def CoreExpr.WF : {Γ : List CoreTy} → {T : CoreTy} → CoreExpr S Γ T → Prop
  | _, _, .lit _ => True
  | _, _, .var _ _ => True
  | _, _, .letE a b => a.WF ∧ b.WF
  | _, _, .ifE c th el => c.WF ∧ th.WF ∧ el.WF
  | _, _, .pairE a b => a.WF ∧ b.WF
  | _, _, .fstE a => a.WF
  | _, _, .sndE a => a.WF
  | _, _, .injE _ _ _ a => a.WF
  | _, _, .matchSum s bs _ => s.WF ∧ bs.WF
  | _, _, .recordE xs _ => xs.WF
  | _, _, .fieldE _ _ _ r => r.WF
  | _, _, .nilE => True
  | _, _, .consE h tl => h.WF ∧ tl.WF
  | _, _, .foldList l init body => l.WF ∧ init.WF ∧ body.WF
  | _, _, .boundedFix init limit stop step => Progress.NlbCat S ∧ init.WF ∧ limit.WF ∧ stop.WF ∧ step.WF
  | _, _, .prim op args => Progress.PrimCat S op ∧ args.WF
  | _, _, .call (.local _ _ _) args => args.WF
  | _, _, .call (.external _ _ _) _ => False
  | _, _, .raise _ _ p => p.WF
  | _, _, .handle _ _ body hd => body.WF ∧ hd.WF
def Branches.WF : {Γ ts : List CoreTy} → {T : CoreTy} → Branches S Γ ts T → Prop
  | _, _, _, .nil => True
  | _, _, _, .cons b bs => b.WF ∧ bs.WF
def Fields.WF : {Γ : List CoreTy} → {fs : List (String × CoreTy)} → Fields S Γ fs → Prop
  | _, _, .nil => True
  | _, _, .cons _ x xs => x.WF ∧ xs.WF
def Args.WF : {Γ ps : List CoreTy} → Args S Γ ps → Prop
  | _, _, .nil => True
  | _, _, .cons x xs => x.WF ∧ xs.WF
end

def Control.WF {A : CoreTy} : Control S A → Prop
  | .evalC _ e => e.WF
  | .retC _ => True
  | .raiseC _ _ _ => True

end WF

end Rcic.Scm

namespace Rcic.Scm

section WFCfg
variable {S : Sig}

def Frame.WF {A B : CoreTy} : Frame S A B → Prop
  | .letF _ b => b.WF
  | .ifF _ th el => th.WF ∧ el.WF
  | .pairL _ b => b.WF
  | .pairR _ => True
  | .fstF => True
  | .sndF => True
  | .injF _ _ => True
  | .matchF _ bs => bs.WF
  | .recF _ _ _ _ _ _ _ rest => rest.WF
  | .fieldF _ _ _ => True
  | .consH _ tl => tl.WF
  | .consT _ => True
  | .foldL _ init body => init.WF ∧ body.WF
  | .foldI _ _ body => body.WF
  | .fixI _ limit stop step => Progress.NlbCat S ∧ limit.WF ∧ stop.WF ∧ step.WF
  | .fixL _ _ stop step => Progress.NlbCat S ∧ stop.WF ∧ step.WF
  | .fixS _ _ _ _ _ stop step => stop.WF ∧ step.WF
  | .fixT _ _ _ _ stop step => stop.WF ∧ step.WF
  | .primArgsF op _ _ _ _ _ rest => Progress.PrimCat S op ∧ rest.WF
  | .callArgsF _ _ _ _ _ _ _ _ rest => rest.WF
  | .retF => True
  | .handleF _ _ _ hd => hd.WF
  | .raiseF _ _ => True

def Cont.WF {A T : CoreTy} : Cont S A T → Prop
  | .nil => True
  | .cons fr k => fr.WF ∧ k.WF

def Config.WF {T : CoreTy} (c : Config S T) : Prop := c.ctl.WF ∧ c.k.WF

def Bodies.WF : {fs : List FnSig} → Bodies S fs → Prop
  | _, .nil => True
  | _, .cons b bs => b.WF ∧ bs.WF

end WFCfg

end Rcic.Scm

namespace Rcic.Scm.Progress
open Rcic.Scm

/-! ## Primitive residues are in the primitive's row -/

theorem checkedI64_raised {n : Int} {r : RaisedRef} (h : checkedI64 n = .raised r) :
    r = "signed_overflow" := by
  unfold checkedI64 at h
  split at h
  · exact LawResult.noConfusion h
  · exact (LawResult.raised.inj h).symm

theorem boolResult_not_raised {b : Bool} {r : RaisedRef} (h : boolResult b = .raised r) : False :=
  LawResult.noConfusion h

theorem ite_parse_raised {c : Prop} [Decidable c] {x : Int} {r : RaisedRef}
    (h : (if c then LawResult.raised "malformed_integer" else checkedI64 x) = .raised r) :
    r = "malformed_integer" ∨ r = "signed_overflow" := by
  split at h
  · exact Or.inl (LawResult.raised.inj h).symm
  · exact Or.inr (checkedI64_raised h)

theorem parseI64_raised {s : String} {r : RaisedRef} (h : parseI64 s = .raised r) :
    r = "malformed_integer" ∨ r = "signed_overflow" := by
  unfold parseI64 at h
  dsimp only at h
  exact ite_parse_raised h

theorem fmod_negSucc_bounds (a : Int) (n : Nat) :
    -(n : Int) ≤ Int.fmod a (Int.negSucc n) ∧ Int.fmod a (Int.negSucc n) ≤ 0 := by
  have hn0 : -(n : Int) ≤ 0 := Int.neg_nonpos_of_nonneg (Int.ofNat_nonneg n)
  cases a with
  | ofNat m =>
    cases m with
    | zero => exact ⟨hn0, Int.le_refl 0⟩
    | succ m =>
      show -(n : Int) ≤ Int.subNatNat (m % Nat.succ n) n ∧ Int.subNatNat (m % Nat.succ n) n ≤ 0
      rw [Int.subNatNat_eq_coe]
      have h2 : ((m % Nat.succ n : Nat) : Int) ≤ n :=
        Int.ofNat_le.mpr (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos n)))
      refine ⟨?_, Int.sub_nonpos_of_le h2⟩
      have := Int.sub_le_sub_right (Int.ofNat_nonneg (m % Nat.succ n)) (n : Int)
      rw [Int.zero_sub] at this
      exact this
  | negSucc m =>
    show -(n : Int) ≤ -((Nat.succ m % Nat.succ n : Nat) : Int) ∧ -((Nat.succ m % Nat.succ n : Nat) : Int) ≤ 0
    have h2 : ((Nat.succ m % Nat.succ n : Nat) : Int) ≤ n :=
      Int.ofNat_le.mpr (Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos n)))
    exact ⟨Int.neg_le_neg h2, Int.neg_nonpos_of_nonneg (Int.ofNat_nonneg _)⟩

/-- Floor modulo of i64 operands by a nonzero divisor is in range: the
    `signed_overflow` arm of `mod` is unreachable (#6029 K3 HOLD item 2b). -/
theorem fmod_inI64 {a b : Int} (hb : inI64 b) (hb0 : b ≠ 0) : inI64 (Int.fmod a b) := by
  have hmin : i64Min ≤ 0 := by decide
  have hmax : (0 : Int) ≤ i64Max := by decide
  cases b with
  | ofNat n =>
    cases n with
    | zero => exact absurd rfl hb0
    | succ n =>
      have hpos : (0 : Int) < Int.ofNat (n + 1) := Int.ofNat_lt.mpr (Nat.succ_pos n)
      exact ⟨Int.le_trans hmin (Int.fmod_nonneg' a hpos),
        Int.le_trans (Int.le_of_lt (Int.fmod_lt_of_pos a hpos)) hb.2⟩
  | negSucc n =>
    obtain ⟨h1, h2⟩ := fmod_negSucc_bounds a n
    have hlo : i64Min ≤ -(n : Int) := by
      have hle : Int.negSucc n ≤ -(n : Int) := by
        rw [Int.negSucc_eq]
        exact Int.neg_le_neg (Int.le_add_of_nonneg_right (by decide))
      exact Int.le_trans hb.1 hle
    exact ⟨Int.le_trans hlo h1, Int.le_trans h2 hmax⟩

theorem primLaw_raised_mem : ∀ (op : PrimOp) (args : CoreVals (primSig op).ps) (r : RaisedRef),
    primLaw op args = .raised r → r ∈ primRow op
  | .add, .cons (.i64V _ _) (.cons (.i64V _ _) .nil), r, h => by
      rw [checkedI64_raised h]; exact List.Mem.head _
  | .sub, .cons (.i64V _ _) (.cons (.i64V _ _) .nil), r, h => by
      rw [checkedI64_raised h]; exact List.Mem.head _
  | .mul, .cons (.i64V _ _) (.cons (.i64V _ _) .nil), r, h => by
      rw [checkedI64_raised h]; exact List.Mem.head _
  | .neg, .cons (.i64V _ _) .nil, r, h => by
      rw [checkedI64_raised h]; exact List.Mem.head _
  | .div, .cons (.i64V a _) (.cons (.i64V b _) .nil), r, h => by
      have h : (if b = 0 then LawResult.raised "division_by_zero"
          else if a % b ≠ 0 then LawResult.raised "nonexact_division" else checkedI64 (a / b)) = .raised r := h
      split at h
      · rw [← LawResult.raised.inj h]; exact List.Mem.head _
      · split at h
        · rw [← LawResult.raised.inj h]; exact List.Mem.tail _ (List.Mem.head _)
        · rw [checkedI64_raised h]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  | .mod, .cons (.i64V a _) (.cons (.i64V b hb) .nil), r, h => by
      have h : (if b = 0 then LawResult.raised "division_by_zero" else checkedI64 (Int.fmod a b)) = .raised r := h
      split at h
      · rw [← LawResult.raised.inj h]; exact List.Mem.head _
      · rename_i hb0
        unfold checkedI64 at h
        rw [dif_pos (fmod_inI64 hb hb0)] at h
        exact LawResult.noConfusion h
  | .lt, .cons (.i64V _ _) (.cons (.i64V _ _) .nil), _, h => (boolResult_not_raised h).elim
  | .eq, .cons (.i64V _ _) (.cons (.i64V _ _) .nil), _, h => (boolResult_not_raised h).elim
  | .strLen, .cons (.strV _) .nil, r, h => by
      rw [checkedI64_raised h]; exact List.Mem.head _
  | .strSlice, .cons (.strV s) (.cons (.i64V a _) (.cons (.i64V b _) .nil)), r, h => by
      have h : (if 0 ≤ a ∧ a ≤ b ∧ b ≤ s.length then
          LawResult.returned (CoreVal.strV (String.mk ((s.toList.drop a.toNat).take (b - a).toNat)))
          else LawResult.raised "index_out_of_range") = .raised r := h
      split at h
      · exact LawResult.noConfusion h
      · rw [← LawResult.raised.inj h]; exact List.Mem.head _
  | .strSplit, .cons (.strV s) (.cons (.strV sep) .nil), r, h => by
      have h : (if sep = "" then LawResult.raised "empty_separator"
          else LawResult.returned (CoreVal.listV (strList (s.splitOn sep)))) = .raised r := h
      split at h
      · rw [← LawResult.raised.inj h]; exact List.Mem.head _
      · exact LawResult.noConfusion h
  | .strToI64, .cons (.strV _) .nil, r, h => by
      cases parseI64_raised h with
      | inl e => rw [e]; exact List.Mem.head _
      | inr e => rw [e]; exact List.Mem.tail _ (List.Mem.head _)
  | .bytesPack, .cons (.listV xs) .nil, r, h => by
      have h : (match packBytes xs with
          | some bs => LawResult.returned (CoreVal.bytesV bs)
          | none => LawResult.raised "byte_out_of_range") = .raised r := h
      split at h
      · exact LawResult.noConfusion h
      · rw [← LawResult.raised.inj h]; exact List.Mem.head _
  | .bytesLen, .cons (.bytesV _) .nil, r, h => by
      rw [checkedI64_raised h]; exact List.Mem.head _

/-! ## One step is never an integrity residue -/

section Step
variable {S : Sig} (prog : Bodies S S.fns)

theorem primSig_ps_ne_nil (op : PrimOp) : (primSig op).ps ≠ [] := by
  cases op <;> exact List.cons_ne_nil _ _

theorem raiseUnit_ne {B T : CoreTy} (r : RaisedRef) (rest : Cont S B T)
    (hr : catalogPt S.catalog r = some unitTy) (code : String) : raiseUnit r rest ≠ .integrity code := by
  intro e
  unfold raiseUnit at e
  split at e
  · rename_i hn
    exact Option.noConfusion (hr.symm.trans hn)
  · rename_i P hP
    split at e
    · exact StepResult.noConfusion e
    · rename_i hp
      exact hp (Option.some.inj (hP.symm.trans hr))

theorem pushPrim_ne {Γ : List CoreTy} {T : CoreTy} (op : PrimOp) (env : CoreVals Γ) (code : String) :
    ∀ (ps : List CoreTy) (heq : (primSig op).ps = ps) (args : Args S Γ ps) (k : Cont S (primSig op).rt T),
    pushPrim op env ps heq args k ≠ .integrity code
  | [], heq, .nil, _ => absurd heq (primSig_ps_ne_nil op)
  | _ :: _, _, .cons _ _, _ => fun e => StepResult.noConfusion e

theorem pushCall_ne {Γ : List CoreTy} {T : CoreTy} (i : Nat) (f : FnSig) (hf : S.fns.get? i = some f)
    (env : CoreVals Γ) (code : String) :
    ∀ (ps : List CoreTy) (heq : f.params = ps) (args : Args S Γ ps) (k : Cont S f.result T),
    pushCall prog i f hf env ps heq args k ≠ .integrity code
  | [], _, .nil, _ => fun e => StepResult.noConfusion e
  | _ :: _, _, .cons _ _, _ => fun e => StepResult.noConfusion e

theorem pushRecord_ne {Γ : List CoreTy} {T : CoreTy} (env : CoreVals Γ) (code : String) :
    ∀ (fs : List (String × CoreTy)) (xs : Fields S Γ fs) (k : Cont S (.record fs) T),
    pushRecord env fs xs k ≠ .integrity code
  | [], .nil, _ => fun e => StepResult.noConfusion e
  | (_, _) :: _, .cons _ _ _, _ => fun e => StepResult.noConfusion e

theorem evalI_ne {Γ : List CoreTy} {T : CoreTy} (env : CoreVals Γ) (code : String) :
    ∀ {A : CoreTy} (e : CoreExpr S Γ A) (k : Cont S A T), e.WF → evalI prog env e k ≠ .integrity code := by
  intro A e k hne
  cases e with
  | recordE xs hk => exact pushRecord_ne env code _ xs k
  | prim op args => exact pushPrim_ne op env code _ rfl args k
  | call f args =>
    cases f with
    | «local» i fs hf => exact pushCall_ne prog i fs hf env code _ rfl args k
    | external r ex hx => exact hne.elim
  | _ => intro e; exact StepResult.noConfusion e

theorem raiseI_ne {A T P : CoreTy} (r : RaisedRef) (h : catalogPt S.catalog r = some P) (v : CoreVal P)
    (code : String) : ∀ (k : Cont S A T), raiseI r h v k ≠ .integrity code := by
  intro k e
  cases k with
  | nil => exact StepResult.noConfusion e
  | cons fr rest =>
    cases fr with
    | handleF r' h' env hd =>
      unfold raiseI at e
      dsimp only at e
      split at e <;> exact StepResult.noConfusion e
    | _ => exact StepResult.noConfusion e

theorem retI_ne {T : CoreTy} (code : String) :
    ∀ {A : CoreTy} (v : CoreVal A) (k : Cont S A T), k.WF → retI prog v k ≠ .integrity code := by
  intro A v k hk e
  cases k with
  | nil => exact StepResult.noConfusion e
  | cons fr rest =>
    have hfr := hk.1
    cases fr with
    | ifF env th el => cases v; exact StepResult.noConfusion e
    | fstF => cases v; exact StepResult.noConfusion e
    | sndF => cases v; exact StepResult.noConfusion e
    | matchF env bs => cases v; exact StepResult.noConfusion e
    | recF fs pre post key heq env done more => cases more <;> exact StepResult.noConfusion e
    | fieldF i key h => cases v; exact StepResult.noConfusion e
    | consT h => cases v; exact StepResult.noConfusion e
    | foldL env init body => cases v; exact StepResult.noConfusion e
    | foldI env xs body => cases xs <;> exact StepResult.noConfusion e
    | fixL env s stop step =>
      cases v with
      | i64V n hn =>
        dsimp only [retI] at e
        split at e
        · exact raiseUnit_ne "negative_loop_bound" rest hfr.1 code e
        · exact StepResult.noConfusion e
    | fixS env s left count hb stop step =>
      cases v with
      | boolV c =>
        dsimp only [retI] at e
        split at e
        · exact StepResult.noConfusion e
        · split at e <;> exact StepResult.noConfusion e
    | primArgsF op pre post heq env done more =>
      cases more with
      | nil =>
        dsimp only [retI] at e
        split at e
        · exact StepResult.noConfusion e
        · rename_i r hlaw
          exact raiseUnit_ne r rest (hfr.1 r (primLaw_raised_mem op _ r hlaw)) code e
      | cons x more' => exact StepResult.noConfusion e
    | callArgsF i f hf pre post heq env done more =>
      cases more <;> exact StepResult.noConfusion e
    | _ => exact StepResult.noConfusion e

/-- 06 §16 progress: a well-formed typed configuration (no external call in
    it, and the residues of every primitive / bounded fix in it catalogued
    with the unit payload) steps or is final. -/
theorem progress {T : CoreTy} (c : Config S T) (hc : c.WF) :
    (∃ c', stepI prog c = .next c') ∨ (∃ o, stepI prog c = .final o) := by
  cases h : stepI prog c with
  | next c' => exact Or.inl ⟨c', rfl⟩
  | final o => exact Or.inr ⟨o, rfl⟩
  | integrity code =>
    exfalso
    match c, hc, h with
    | ⟨_, .evalC env e, k⟩, hc, h => exact evalI_ne prog env code e k hc.1 h
    | ⟨_, .retC v, k⟩, hc, h => exact retI_ne prog code v k hc.2 h
    | ⟨_, .raiseC r hr v, k⟩, _, h => exact raiseI_ne r hr v code k h

end Step

end Rcic.Scm.Progress
