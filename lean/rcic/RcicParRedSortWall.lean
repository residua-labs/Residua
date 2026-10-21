/-
RCIC ParRed, piece 4 of 7: complete development (Takahashi) and the
SortConvChar / PiConvInj wall.

`devel` and its characterization suite (`nfRel_*`,
`sortConvChar_of_nfRel`), the `iotaReductCert*` certificate chain,
the F-05b eta/irr postponement for sorts, the PiConvInj wall
(`piIrr_pi_pi`, `piConvInj_sortConvChar_false`), and the
Conv-to-Join-at-sorts fragments.  These are the standalone
characterization artifacts behind the named obligations O-1 / O-3;
nothing in `RcicParRedDiamond` depends on this piece.

Split out of the former single `rcic.RcicParRed`; statements and
proofs are verbatim.
-/
import rcic.RcicParRedCore
import rcic.RcicParRedIota

namespace Rcic.Declarative

/-! ### Complete development (Takahashi) toward SortConvChar.
lit develops to `natExpand` (08 pin). Delta/zeta/iota of non-subterms
are one-shot (structural recursion). Eta is contracted in the lam case
(M-001: syntactic nfRel of an η-expansion vs its function is false;
the short development makes `conv_nfRel` of `Conv.eta` true).
Complete-Takahashi iota (`devel lhs = devel rhs`) is the one-shot wall
(rhs is not a subterm — same as delta). -/

/-- Last element of a list; `none` on `[]`. -/
def listLast {α} : List α → Option α
  | [] => none
  | x :: xs =>
      match xs with
      | [] => some x
      | _ :: _ => listLast xs

theorem listLast_eq_getElem {α} :
    (xs : List α) → (n : Nat) → xs.length = n + 1 →
    listLast xs = xs[n]?
  | [], n, h => by
      simp only [List.length_nil] at h
      cases h
  | x :: xs, n, h =>
      match xs, n with
      | [], 0 => rfl
      | [], k + 1 => by
          simp only [List.length_cons, List.length_nil] at h
          cases h
      | y :: ys, 0 => by
          simp only [List.length_cons] at h
          cases h
      | y :: ys, k + 1 => by
          have hlen : (y :: ys).length = k + 1 := by
            simp only [List.length_cons] at h ⊢
            omega
          have ih := listLast_eq_getElem (y :: ys) k hlen
          change listLast (y :: ys) = (x :: y :: ys)[k + 1]?
          rw [ih]
          simp only [List.getElem?_cons_succ]

/-- `applyTel` commutes with `lift` on the whole `Option`. -/
theorem applyTel_map_lift (c amt : Nat) :
    (xs : List (Expr Nat)) → (T : Expr Nat) →
    applyTel (xs.map (lift c amt)) (lift c amt T) =
      (applyTel xs T).map (lift c amt)
  | [], T => rfl
  | x :: xs, T => by
      cases T with
      | pi A B =>
        simp only [List.map_cons, lift, applyTel]
        have hinst :
            instantiate0 (lift c amt x) (lift (c + 1) amt B) =
              lift c amt (instantiate0 x B) := by
          simp only [instantiate0]
          exact (lift_instantiate_low amt c 0 x (Nat.zero_le c) B).symm
        rw [hinst]
        exact applyTel_map_lift c amt xs (instantiate0 x B)
      | bvar i =>
        simp only [List.map_cons, lift, applyTel]
        split <;> simp only [applyTel, Option.map]
      | sort _ =>
        simp only [List.map_cons, lift, applyTel, Option.map]
      | const _ _ =>
        simp only [List.map_cons, lift, applyTel, Option.map]
      | app _ _ =>
        simp only [List.map_cons, lift, applyTel, Option.map]
      | lam _ _ =>
        simp only [List.map_cons, lift, applyTel, Option.map]
      | letE _ _ _ =>
        simp only [List.map_cons, lift, applyTel, Option.map]
      | lit _ =>
        simp only [List.map_cons, lift, applyTel, Option.map]

theorem applyTel_map_lift_closed (c : Nat) (xs : List (Expr Nat))
    (T : Expr Nat) (hcl : lift 0 1 T = T) :
    applyTel (xs.map (lift c 1)) T =
      (applyTel xs T).map (lift c 1) := by
  have h := applyTel_map_lift c 1 xs T
  rw [lift_of_closed T hcl c 1] at h
  exact h

theorem applyTel_eq_some_unlift {c : Nat} {xs : List (Expr Nat)}
    {T U0 : Expr Nat} (hcl : lift 0 1 T = T) {U : Expr Nat}
    (hmap : applyTel (xs.map (lift c 1)) T = some U)
    (hU : lift c 1 U0 = U) :
    applyTel xs T = some U0 := by
  have h := applyTel_map_lift_closed c xs T hcl
  rw [hmap] at h
  cases htel : applyTel xs T with
  | none =>
      simp only [htel, Option.map] at h
      nomatch h
  | some V =>
      simp only [htel, Option.map] at h
      injection h with hVU
      have := lift_inj c V U0 (hVU.symm.trans hU.symm)
      subst this
      rfl

/-- Invert `lift` at a Π: only a Π lifts to a Π. -/
theorem lift_eq_pi {c : Nat} {e A B : Expr Nat}
    (h : lift c 1 e = .pi A B) :
    ∃ A0 B0, e = .pi A0 B0 ∧ lift c 1 A0 = A ∧ lift (c + 1) 1 B0 = B := by
  cases e with
  | pi A0 B0 =>
      simp only [lift] at h
      injection h with hA hB
      exact ⟨A0, B0, rfl, hA, hB⟩
  | bvar i =>
      simp only [lift] at h
      by_cases hle : c ≤ i
      · rw [if_pos hle] at h; nomatch h
      · rw [if_neg hle] at h; nomatch h
  | sort _ => simp only [lift] at h; nomatch h
  | const _ _ => simp only [lift] at h; nomatch h
  | app _ _ => simp only [lift] at h; nomatch h
  | lam _ _ => simp only [lift] at h; nomatch h
  | letE _ _ _ => simp only [lift] at h; nomatch h
  | lit _ => simp only [lift] at h; nomatch h

theorem getElem?_unlift {c i : Nat} {xs : List (Expr Nat)} {y : Expr Nat}
    (h : (xs.map (lift c 1))[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ lift c 1 x = y := by
  rw [List.getElem?_map] at h
  cases hx : xs[i]? with
  | none =>
      simp only [hx, Option.map] at h
      nomatch h
  | some x =>
      simp only [hx, Option.map] at h
      injection h with hy
      exact ⟨x, rfl, hy⟩

theorem map_lift_inj_aux (c : Nat) : {xs ys : List (Expr Nat)} →
    xs.map (lift c 1) = ys.map (lift c 1) → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, y :: ys, h => by
      simp only [List.map_cons] at h
      injection h with hxy hrest
      have hx := lift_inj c x y hxy
      subst hx
      exact congrArg (List.cons x) (map_lift_inj_aux c hrest)

theorem all_mem_of_map_lift (c : Nat) :
    (xs ys : List (Expr Nat)) →
    (xs.map (lift c 1)).all
        (fun y => decide (y ∈ ys.map (lift c 1))) = true →
    xs.all (fun x => decide (x ∈ ys)) = true
  | [], _, _ => rfl
  | x :: xs, ys, h => by
      simp only [List.all_cons, List.map_cons] at h ⊢
      have ⟨hx, hxs⟩ := bool_and_true h
      have hxmem : lift c 1 x ∈ ys.map (lift c 1) := of_decide_eq_true hx
      have ⟨a, ha, hfa⟩ := List.mem_map.mp hxmem
      have hax : a = x := lift_inj c a x hfa
      have hx' : decide (x ∈ ys) = true := decide_eq_true (hax ▸ ha)
      have hxs' := all_mem_of_map_lift c xs ys hxs
      simp only [hx', hxs']
      rfl

theorem isPiTel_of_lift (c a : Nat) :
    (n : Nat) → (T : Expr Nat) →
    isPiTel n (lift c a T) = true → isPiTel n T = true
  | 0, _, _ => rfl
  | n + 1, .pi A B, h => by
      simp only [isPiTel, lift] at h ⊢
      exact isPiTel_of_lift (c + 1) a n B h
  | n + 1, .bvar i, h => by
      simp only [lift, isPiTel] at h
      by_cases hle : c ≤ i
      · rw [if_pos hle] at h; nomatch h
      · rw [if_neg hle] at h; nomatch h
  | n + 1, .sort _, h => by simp only [lift, isPiTel] at h; nomatch h
  | n + 1, .const _ _, h => by simp only [lift, isPiTel] at h; nomatch h
  | n + 1, .app _ _, h => by simp only [lift, isPiTel] at h; nomatch h
  | n + 1, .lam _ _, h => by simp only [lift, isPiTel] at h; nomatch h
  | n + 1, .letE _ _ _, h => by simp only [lift, isPiTel] at h; nomatch h
  | n + 1, .lit _, h => by simp only [lift, isPiTel] at h; nomatch h

theorem spineHeadConst_of_lift (c a : Nat) (A : Expr Nat)
    (h : spineHeadConst (lift c a A) = true) :
    spineHeadConst A = true := by
  simp only [spineHeadConst] at h ⊢
  have hlift := appsSpine_lift c a A
  rw [hlift] at h
  cases hsp : (appsSpine A).1 with
  | const _ _ => simp only [hsp, lift]
  | bvar i =>
      simp only [hsp, lift] at h
      by_cases hle : c ≤ i
      · rw [if_pos hle] at h; nomatch h
      · rw [if_neg hle] at h; nomatch h
  | sort _ => simp only [hsp, lift] at h; nomatch h
  | app _ _ => simp only [hsp, lift] at h; nomatch h
  | lam _ _ => simp only [hsp, lift] at h; nomatch h
  | pi _ _ => simp only [hsp, lift] at h; nomatch h
  | letE _ _ _ => simp only [hsp, lift] at h; nomatch h
  | lit _ => simp only [hsp, lift] at h; nomatch h

theorem directRecConstHead_of_lift (c a : Nat) :
    (ks : List RecKind) → (T : Expr Nat) →
    directRecConstHead ks (lift c a T) = true →
    directRecConstHead ks T = true
  | [], _, _ => rfl
  | .plain :: ks, .pi A B, h => by
      simp only [directRecConstHead, lift] at h ⊢
      exact directRecConstHead_of_lift (c + 1) a ks B h
  | .directRec :: ks, .pi A B, h => by
      simp only [directRecConstHead, lift] at h ⊢
      have ⟨hA, hB⟩ := bool_and_true h
      have hA' := spineHeadConst_of_lift c a A hA
      have hB' := directRecConstHead_of_lift (c + 1) a ks B hB
      simp only [hA', hB']
      rfl
  | .plain :: ks, .bvar _, _ => by simp only [directRecConstHead]
  | .plain :: ks, .sort _, _ => rfl
  | .plain :: ks, .const _ _, _ => rfl
  | .plain :: ks, .app _ _, _ => rfl
  | .plain :: ks, .lam _ _, _ => rfl
  | .plain :: ks, .letE _ _ _, _ => rfl
  | .plain :: ks, .lit _, _ => rfl
  | .directRec :: ks, .bvar _, _ => by simp only [directRecConstHead]
  | .directRec :: ks, .sort _, _ => rfl
  | .directRec :: ks, .const _ _, _ => rfl
  | .directRec :: ks, .app _ _, _ => rfl
  | .directRec :: ks, .lam _ _, _ => rfl
  | .directRec :: ks, .letE _ _ _, _ => rfl
  | .directRec :: ks, .lit _, _ => rfl

/-- Reverse-lift sibling of `directRecConstHead_of_lift`. The base is
`spineHeadConst`, not `true`, so the base and every catch-all arm go
through `spineHeadConst_of_lift`; the `.bvar` catch-alls are refuted
from the hypothesis (a lifted bvar is still a bvar, so the lifted
side is `false` too). Needed to unlift `hresTel` in `unliftWitness`. -/
theorem resultConstHead_of_lift (c a : Nat) :
    (ks : List RecKind) → (T : Expr Nat) →
    resultConstHead ks (lift c a T) = true →
    resultConstHead ks T = true
  | [], T, h => spineHeadConst_of_lift c a T h
  | .plain :: ks, .pi A B, h => by
      simp only [resultConstHead, lift] at h ⊢
      exact resultConstHead_of_lift (c + 1) a ks B h
  | .directRec :: ks, .pi A B, h => by
      simp only [resultConstHead, lift] at h ⊢
      exact resultConstHead_of_lift (c + 1) a ks B h
  | .plain :: _, .bvar i, h => by
      simp only [lift] at h
      by_cases hle : c ≤ i
      · rw [if_pos hle] at h; nomatch h
      · rw [if_neg hle] at h; nomatch h
  | .plain :: _, .sort l, h => spineHeadConst_of_lift c a (.sort l) h
  | .plain :: _, .const r ls, h =>
      spineHeadConst_of_lift c a (.const r ls) h
  | .plain :: _, .app f x, h => spineHeadConst_of_lift c a (.app f x) h
  | .plain :: _, .lam A B, h => spineHeadConst_of_lift c a (.lam A B) h
  | .plain :: _, .letE A v B, h =>
      spineHeadConst_of_lift c a (.letE A v B) h
  | .plain :: _, .lit t, h => spineHeadConst_of_lift c a (.lit t) h
  | .directRec :: _, .bvar i, h => by
      simp only [lift] at h
      by_cases hle : c ≤ i
      · rw [if_pos hle] at h; nomatch h
      · rw [if_neg hle] at h; nomatch h
  | .directRec :: _, .sort l, h => spineHeadConst_of_lift c a (.sort l) h
  | .directRec :: _, .const r ls, h =>
      spineHeadConst_of_lift c a (.const r ls) h
  | .directRec :: _, .app f x, h => spineHeadConst_of_lift c a (.app f x) h
  | .directRec :: _, .lam A B, h => spineHeadConst_of_lift c a (.lam A B) h
  | .directRec :: _, .letE A v B, h =>
      spineHeadConst_of_lift c a (.letE A v B) h
  | .directRec :: _, .lit t, h => spineHeadConst_of_lift c a (.lit t) h

theorem idxPosZip_of_lift (c : Nat) (pf : List (Expr Nat)) :
    (xs : List (Expr Nat)) → (pos : List Nat) →
    idxPosZip (pf.map (lift c 1)) (xs.map (lift c 1)) pos = true →
    idxPosZip pf xs pos = true
  | [], pos, h => by
      cases pos with
      | nil => rfl
      | cons _ _ => simp only [idxPosZip, List.map_nil] at h; nomatch h
  | x :: xs, pos, h => by
      cases pos with
      | nil => simp only [idxPosZip, List.map_cons] at h; nomatch h
      | cons i is =>
          simp only [idxPosZip, List.map_cons] at h ⊢
          have ⟨hx, hrest⟩ := bool_and_true h
          have hxmem : (pf.map (lift c 1))[i]? = some (lift c 1 x) :=
            of_decide_eq_true hx
          have ⟨a, ha, hfa⟩ := getElem?_unlift hxmem
          have hax : a = x := lift_inj c a x hfa
          have hx0 : decide (pf[i]? = some x) = true :=
            decide_eq_true (hax ▸ ha)
          have hrest0 := idxPosZip_of_lift c pf xs is hrest
          simp only [hx0, hrest0]
          rfl

theorem recIdxPosWalk_of_lift (c nparams : Nat) (pf : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
    (pss : List (List Nat))
    (h : recIdxPosWalk nparams (pf.map (lift c 1)) ks (lift c 1 T)
      (fs.map (lift c 1)) pss = true) :
    recIdxPosWalk nparams pf ks T fs pss = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxPosWalk]
          | cons _ _ =>
              simp only [recIdxPosWalk, List.map_nil] at h; nomatch h
      | cons _ _ =>
          simp only [recIdxPosWalk, List.map_cons] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil =>
                  simp only [recIdxPosWalk, List.map_nil, lift] at h
                  nomatch h
              | cons f fs =>
                  cases pss with
                  | nil =>
                      simp only [recIdxPosWalk, List.map_cons, lift] at h
                      nomatch h
                  | cons pos pss =>
                      cases pos with
                      | nil =>
                          simp only [recIdxPosWalk, List.map_cons, lift]
                            at h ⊢
                          rw [instantiate0_lift] at h
                          exact ih (instantiate0 f B) fs pss h
                      | cons _ _ =>
                          simp only [recIdxPosWalk, List.map_cons, lift] at h
                          nomatch h
          | bvar _ =>
              simp only [recIdxPosWalk, lift] at h
              split at h <;> (simp only [recIdxPosWalk] at h; nomatch h)
          | sort _ => simp only [recIdxPosWalk, lift] at h; nomatch h
          | const _ _ => simp only [recIdxPosWalk, lift] at h; nomatch h
          | app _ _ => simp only [recIdxPosWalk, lift] at h; nomatch h
          | lam _ _ => simp only [recIdxPosWalk, lift] at h; nomatch h
          | letE _ _ _ => simp only [recIdxPosWalk, lift] at h; nomatch h
          | lit _ => simp only [recIdxPosWalk, lift] at h; nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil =>
                  simp only [recIdxPosWalk, List.map_nil, lift] at h
                  nomatch h
              | cons f fs =>
                  cases pss with
                  | nil =>
                      simp only [recIdxPosWalk, List.map_cons, lift] at h
                      nomatch h
                  | cons pos pss =>
                      simp only [recIdxPosWalk, List.map_cons, lift] at h ⊢
                      have ⟨hzip, hrest⟩ := bool_and_true h
                      have hfi := familyIdx_lift c 1 nparams A
                      rw [hfi] at hzip
                      have hzip0 := idxPosZip_of_lift c pf
                        (familyIdx nparams A) pos hzip
                      have hrest0 := ih (instantiate0 f B) fs pss (by
                        rw [instantiate0_lift] at hrest; exact hrest)
                      simp only [hzip0, hrest0]
                      rfl
          | bvar _ =>
              simp only [recIdxPosWalk, lift] at h
              split at h <;> (simp only [recIdxPosWalk] at h; nomatch h)
          | sort _ => simp only [recIdxPosWalk, lift] at h; nomatch h
          | const _ _ => simp only [recIdxPosWalk, lift] at h; nomatch h
          | app _ _ => simp only [recIdxPosWalk, lift] at h; nomatch h
          | lam _ _ => simp only [recIdxPosWalk, lift] at h; nomatch h
          | letE _ _ _ => simp only [recIdxPosWalk, lift] at h; nomatch h
          | lit _ => simp only [recIdxPosWalk, lift] at h; nomatch h

theorem directRecFamilySpine_of_lift (c fam : Nat) (ls : List Level)
    (nparams : Nat) (params : List (Expr Nat)) :
    (ks : List RecKind) → (T : Expr Nat) → (fs : List (Expr Nat)) →
    directRecFamilySpine fam ls nparams (params.map (lift c 1)) ks
      (lift c 1 T) (fs.map (lift c 1)) = true →
    directRecFamilySpine fam ls nparams params ks T fs = true
  | [], _, _, _ => rfl
  | .plain :: ks, .pi A B, f :: fs, h => by
      simp only [directRecFamilySpine, List.map_cons, lift] at h ⊢
      rw [instantiate0_lift] at h
      exact directRecFamilySpine_of_lift c fam ls nparams params ks
        (instantiate0 f B) fs h
  | .directRec :: ks, .pi A B, f :: fs, h => by
      simp only [directRecFamilySpine, List.map_cons, lift] at h ⊢
      have ⟨hhead, hrest⟩ := bool_and_true h
      have hsp := appsSpine_lift c 1 A
      have hhead0 :
          (match (appsSpine A).1 with
            | .const r _ => decide (r = fam)
            | _ => false) = true := by
        rw [hsp] at hhead
        cases hhd : (appsSpine A).1 with
        | const r ls' =>
            simp only [hhd, lift] at hhead
            exact hhead
        | bvar i =>
            simp only [hhd, lift] at hhead
            by_cases hle : c ≤ i
            · rw [if_pos hle] at hhead; exact Bool.noConfusion hhead
            · rw [if_neg hle] at hhead; exact Bool.noConfusion hhead
        | sort _ => simp only [hhd, lift] at hhead; exact Bool.noConfusion hhead
        | app _ _ => simp only [hhd, lift] at hhead; exact Bool.noConfusion hhead
        | lam _ _ => simp only [hhd, lift] at hhead; exact Bool.noConfusion hhead
        | pi _ _ => simp only [hhd, lift] at hhead; exact Bool.noConfusion hhead
        | letE _ _ _ => simp only [hhd, lift] at hhead; exact Bool.noConfusion hhead
        | lit _ => simp only [hhd, lift] at hhead; exact Bool.noConfusion hhead
      have hrest0 := directRecFamilySpine_of_lift c fam ls nparams params ks
        (instantiate0 f B) fs (by rw [instantiate0_lift] at hrest; exact hrest)
      have htrue :
          (true &&
            directRecFamilySpine fam ls nparams params ks
              (instantiate0 f B) fs) = true :=
        Bool.true_and _ ▸ hrest0
      exact hhead0 ▸ htrue
  | .plain :: ks, .pi _ _, [], _ => by simp only [directRecFamilySpine]
  | .directRec :: ks, .pi _ _, [], _ => by simp only [directRecFamilySpine]
  | .plain :: _, .bvar _, _, _ => by simp only [directRecFamilySpine]
  | .plain :: _, .sort _, _, _ => by simp only [directRecFamilySpine]
  | .plain :: _, .const _ _, _, _ => by simp only [directRecFamilySpine]
  | .plain :: _, .app _ _, _, _ => by simp only [directRecFamilySpine]
  | .plain :: _, .lam _ _, _, _ => by simp only [directRecFamilySpine]
  | .plain :: _, .letE _ _ _, _, _ => by simp only [directRecFamilySpine]
  | .plain :: _, .lit _, _, _ => by simp only [directRecFamilySpine]
  | .directRec :: _, .bvar _, _, _ => by simp only [directRecFamilySpine]
  | .directRec :: _, .sort _, _, _ => by simp only [directRecFamilySpine]
  | .directRec :: _, .const _ _, _, _ => by simp only [directRecFamilySpine]
  | .directRec :: _, .app _ _, _, _ => by simp only [directRecFamilySpine]
  | .directRec :: _, .lam _ _, _, _ => by simp only [directRecFamilySpine]
  | .directRec :: _, .letE _ _ _, _, _ => by simp only [directRecFamilySpine]
  | .directRec :: _, .lit _, _, _ => by simp only [directRecFamilySpine]

theorem idxTyAlignPosGo_of_lift (c : Nat) (recType ctorType : Expr Nat)
    (hrecCl : lift c 1 recType = recType)
    (hctorCl : lift c 1 ctorType = ctorType)
    (recPre paramsFields pre rest : List (Expr Nat)) (pos : List Nat)
    (h : idxTyAlignPosGo recType ctorType (recPre.map (lift c 1))
      (paramsFields.map (lift c 1)) (pre.map (lift c 1))
      (rest.map (lift c 1)) pos = true) :
    idxTyAlignPosGo recType ctorType recPre paramsFields pre rest pos =
      true := by
  induction rest generalizing pre pos with
  | nil =>
      cases pos with
      | nil => rfl
      | cons i is =>
          simp only [List.map_nil] at h
          nomatch h
  | cons x xs ih =>
      cases pos with
      | nil =>
          simp only [List.map_cons] at h
          nomatch h
      | cons i is =>
          simp only [idxTyAlignPosGo, List.map_cons] at h
          rw [← List.map_append] at h
          rw [← List.map_take (lift c 1) paramsFields i] at h
          cases happR : applyTel ((recPre ++ pre).map (lift c 1)) recType with
          | none => simp only [happR] at h; nomatch h
          | some Ur =>
              match Ur with
              | .pi Ar Br =>
                  simp only [happR] at h
                  cases happC :
                      applyTel ((paramsFields.take i).map (lift c 1))
                        ctorType with
                  | none => simp only [happC] at h; nomatch h
                  | some Uc =>
                      match Uc with
                      | .pi Ac Bc =>
                          simp only [happC] at h
                          have ⟨heq, hrest⟩ := bool_and_true h
                          have hAcAr : Ac = Ar := of_decide_eq_true heq
                          have hR := applyTel_map_lift c 1 (recPre ++ pre)
                            recType
                          rw [hrecCl] at hR
                          rw [happR] at hR
                          cases happR0 : applyTel (recPre ++ pre) recType with
                          | none =>
                              simp only [happR0, Option.map] at hR
                              nomatch hR
                          | some Vr =>
                              simp only [happR0, Option.map] at hR
                              injection hR with hVR
                              have ⟨Ar0, Br0, hVpi, hAr0, _⟩ :=
                                lift_eq_pi hVR.symm
                              subst hVpi
                              have hC := applyTel_map_lift c 1
                                (paramsFields.take i) ctorType
                              rw [hctorCl] at hC
                              rw [happC] at hC
                              cases happC0 :
                                  applyTel (paramsFields.take i) ctorType with
                              | none =>
                                  simp only [happC0, Option.map] at hC
                                  nomatch hC
                              | some Vc =>
                                  simp only [happC0, Option.map] at hC
                                  injection hC with hVC
                                  have ⟨Ac0, Bc0, hVpiC, hAc0, _⟩ :=
                                    lift_eq_pi hVC.symm
                                  subst hVpiC
                                  have hAc0Ar0 : Ac0 = Ar0 :=
                                    lift_inj c Ac0 Ar0
                                      (hAc0.trans (hAcAr.trans hAr0.symm))
                                  have heq0 :
                                      decide (Ac0 = Ar0) = true :=
                                    decide_eq_true hAc0Ar0
                                  have hpre' :
                                      pre.map (lift c 1) ++ [lift c 1 x] =
                                        (pre ++ [x]).map (lift c 1) := by
                                    rw [List.map_append, List.map_cons,
                                      List.map_nil]
                                  have ih' := ih (pre ++ [x]) is (by
                                    rw [← hpre']
                                    exact hrest)
                                  simp only [idxTyAlignPosGo, happR0, happC0,
                                    heq0, ih']
                                  rfl
                      | .bvar _ => simp only [happC] at h; nomatch h
                      | .sort _ => simp only [happC] at h; nomatch h
                      | .const _ _ => simp only [happC] at h; nomatch h
                      | .app _ _ => simp only [happC] at h; nomatch h
                      | .lam _ _ => simp only [happC] at h; nomatch h
                      | .letE _ _ _ => simp only [happC] at h; nomatch h
                      | .lit _ => simp only [happC] at h; nomatch h
              | .bvar _ => simp only [happR] at h; nomatch h
              | .sort _ => simp only [happR] at h; nomatch h
              | .const _ _ => simp only [happR] at h; nomatch h
              | .app _ _ => simp only [happR] at h; nomatch h
              | .lam _ _ => simp only [happR] at h; nomatch h
              | .letE _ _ _ => simp only [happR] at h; nomatch h
              | .lit _ => simp only [happR] at h; nomatch h

theorem recIdxTyWalkPos_of_lift (c : Nat) (recType ctorType : Expr Nat)
    (hrecCl : lift c 1 recType = recType)
    (hctorCl : lift c 1 ctorType = ctorType)
    (nparams : Nat) (recPre paramsFields : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
    (pss : List (List Nat))
    (h : recIdxTyWalkPos recType ctorType nparams
      (recPre.map (lift c 1)) (paramsFields.map (lift c 1)) ks
      (lift c 1 T) (fs.map (lift c 1)) pss = true) :
    recIdxTyWalkPos recType ctorType nparams recPre paramsFields ks T
      fs pss = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxTyWalkPos]
          | cons _ _ =>
              simp only [recIdxTyWalkPos, List.map_nil] at h; nomatch h
      | cons _ _ =>
          simp only [recIdxTyWalkPos, List.map_cons] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil =>
                  simp only [recIdxTyWalkPos, List.map_nil, lift] at h
                  nomatch h
              | cons f fs =>
                  cases pss with
                  | nil =>
                      simp only [recIdxTyWalkPos, List.map_cons, lift] at h
                      nomatch h
                  | cons pos pss =>
                      cases pos with
                      | nil =>
                          simp only [recIdxTyWalkPos, List.map_cons, lift]
                            at h ⊢
                          rw [instantiate0_lift] at h
                          exact ih (instantiate0 f B) fs pss h
                      | cons _ _ =>
                          simp only [recIdxTyWalkPos, List.map_cons, lift] at h
                          nomatch h
          | bvar _ =>
              simp only [recIdxTyWalkPos, lift] at h
              split at h <;> (simp only [recIdxTyWalkPos] at h; nomatch h)
          | sort _ => simp only [recIdxTyWalkPos, lift] at h; nomatch h
          | const _ _ => simp only [recIdxTyWalkPos, lift] at h; nomatch h
          | app _ _ => simp only [recIdxTyWalkPos, lift] at h; nomatch h
          | lam _ _ => simp only [recIdxTyWalkPos, lift] at h; nomatch h
          | letE _ _ _ => simp only [recIdxTyWalkPos, lift] at h; nomatch h
          | lit _ => simp only [recIdxTyWalkPos, lift] at h; nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil =>
                  simp only [recIdxTyWalkPos, List.map_nil, lift] at h
                  nomatch h
              | cons f fs =>
                  cases pss with
                  | nil =>
                      simp only [recIdxTyWalkPos, List.map_cons, lift] at h
                      nomatch h
                  | cons pos pss =>
                      simp only [recIdxTyWalkPos, List.map_cons, lift] at h ⊢
                      have ⟨halign, hrest⟩ := bool_and_true h
                      have hfi := familyIdx_lift c 1 nparams A
                      have halign0 : idxTyAlignPos recType ctorType recPre
                          paramsFields (familyIdx nparams A) pos = true := by
                        simp only [idxTyAlignPos]
                        simp only [idxTyAlignPos, hfi] at halign
                        exact idxTyAlignPosGo_of_lift c recType ctorType
                          hrecCl hctorCl recPre paramsFields []
                          (familyIdx nparams A) pos halign
                      have hrest0 := ih (instantiate0 f B) fs pss (by
                        rw [instantiate0_lift] at hrest; exact hrest)
                      simp only [halign0, hrest0]
                      rfl
          | bvar _ =>
              simp only [recIdxTyWalkPos, lift] at h
              split at h <;> (simp only [recIdxTyWalkPos] at h; nomatch h)
          | sort _ => simp only [recIdxTyWalkPos, lift] at h; nomatch h
          | const _ _ => simp only [recIdxTyWalkPos, lift] at h; nomatch h
          | app _ _ => simp only [recIdxTyWalkPos, lift] at h; nomatch h
          | lam _ _ => simp only [recIdxTyWalkPos, lift] at h; nomatch h
          | letE _ _ _ => simp only [recIdxTyWalkPos, lift] at h; nomatch h
          | lit _ => simp only [recIdxTyWalkPos, lift] at h; nomatch h

/-- Dual of `liftWitness`: unlift expr fields of a witness whose spine
is in the image of `lift c 1`. Fill-produced witnesses of a lifted lhs
are of this shape (ctorAfter / mdom via `applyTel_map_lift`). -/
def unliftWitness (c : Nat) {E : ResolvedEnv} (w : IotaWitness E)
    (pre0 fields0 ctorParams0 : List (Expr Nat))
    (minor0 ctorAfter0 : Expr Nat)
    (hpreEq : w.preMajor = pre0.map (lift c 1))
    (hfieldsEq : w.fields = fields0.map (lift c 1))
    (hctorParamsEq : w.ctorParams = ctorParams0.map (lift c 1))
    (hminorEq : w.minor = lift c 1 minor0)
    (hctorAfterEq : w.ctorAfterParams = lift c 1 ctorAfter0) :
    IotaWitness E where
  recRef := w.recRef
  ctorRef := w.ctorRef
  ls := w.ls
  lsC := w.lsC
  recMember := w.recMember
  ctorMember := w.ctorMember
  hrec := w.hrec
  hctor := w.hctor
  hrecK := w.hrecK
  hctorK := w.hctorK
  preMajor := pre0
  fields := fields0
  ctorParams := ctorParams0
  kinds := w.kinds
  minor := minor0
  hlen := by
    have h := w.hlen
    rw [hfieldsEq, List.length_map] at h
    exact h
  familyRef := w.familyRef
  famMember := w.famMember
  hfam := w.hfam
  hfamK := w.hfamK
  nparams := w.nparams
  nindices := w.nindices
  nMinors := w.nMinors
  ctorIdx := w.ctorIdx
  hctorParams := by
    have h := w.hctorParams
    rw [hctorParamsEq, List.length_map] at h
    exact h
  hnpar := by
    have h := w.hnpar
    rw [hfieldsEq, List.length_map] at h
    exact h
  hnidx := w.hnidx
  hnmin := w.hnmin
  hidx := w.hidx
  hctorIdx := w.hctorIdx
  hrecIdx := w.hrecIdx
  hpre := by
    have h := w.hpre
    rw [hpreEq, List.length_map] at h
    exact h
  hminor := by
    have hw : (pre0.map (lift c 1))[w.nparams + 1 + w.ctorIdx]? =
        some (lift c 1 minor0) := by
      rw [← hpreEq, w.hminor, hminorEq]
    have ⟨m, hm, hfm⟩ := getElem?_unlift hw
    have hm0 : m = minor0 := lift_inj c m minor0 hfm
    exact hm0 ▸ hm
  ctorDoms := w.ctorDoms
  ctorResult := w.ctorResult
  hpeel := by
    have hlenf : w.fields.length = fields0.length := by
      rw [hfieldsEq, List.length_map]
    rw [← hlenf]
    exact w.hpeel
  hfamApp := w.hfamApp
  hkinds := w.hkinds
  recDoms := w.recDoms
  recBody := w.recBody
  hpeelRec := w.hpeelRec
  hrecBody := w.hrecBody
  hmajorTy := w.hmajorTy
  hrecClosed := w.hrecClosed
  hctorClosed := w.hctorClosed
  hlsLen := w.hlsLen
  ctorAfterParams := ctorAfter0
  hctorAfter := by
    have htake :
        w.preMajor.take w.nparams =
          (pre0.take w.nparams).map (lift c 1) := by
      rw [hpreEq, ← List.map_take (lift c 1) pre0 w.nparams]
    have happ := w.hctorAfter
    rw [htake, hctorAfterEq] at happ
    have hmap := applyTel_map_lift c 1 (pre0.take w.nparams)
      (instantiateLevels w.ls w.ctorMember.mtype)
    rw [lift_of_closed (instantiateLevels w.ls w.ctorMember.mtype)
      (instantiateLevels_closed0 w.hctorClosed w.ls) c 1] at hmap
    rw [happ] at hmap
    cases htel : applyTel (pre0.take w.nparams)
        (instantiateLevels w.ls w.ctorMember.mtype) with
    | none =>
        simp only [htel, Option.map] at hmap
        nomatch hmap
    | some V =>
        simp only [htel, Option.map] at hmap
        injection hmap with hV
        have hVeq : V = ctorAfter0 := lift_inj c V ctorAfter0 hV.symm
        rw [hVeq]
  hctorTel := isPiTel_of_lift c 1 w.kinds.length ctorAfter0 (by
    rw [← hctorAfterEq]; exact w.hctorTel)
  hfamTel := directRecConstHead_of_lift c 1 w.kinds ctorAfter0 (by
    rw [← hctorAfterEq]; exact w.hfamTel)
  hresTel := resultConstHead_of_lift c 1 w.kinds ctorAfter0 (by
    rw [← hctorAfterEq]; exact w.hresTel)

theorem lift_eq_const {c : Nat} {e : Expr Nat} {r : Nat} {ls : List Level}
    (h : lift c 1 e = .const r ls) : e = .const r ls := by
  cases e with
  | const r' ls' =>
      simp only [lift] at h
      injection h with hr hls
      subst hr; subst hls
      rfl
  | bvar i =>
      simp only [lift] at h
      by_cases hle : c ≤ i
      · rw [if_pos hle] at h; nomatch h
      · rw [if_neg hle] at h; nomatch h
  | sort _ => simp only [lift] at h; nomatch h
  | app _ _ => simp only [lift] at h; nomatch h
  | lam _ _ => simp only [lift] at h; nomatch h
  | pi _ _ => simp only [lift] at h; nomatch h
  | letE _ _ _ => simp only [lift] at h; nomatch h
  | lit _ => simp only [lift] at h; nomatch h

theorem Option_map_ite {α β} (f : α → β) (p : Prop) [Decidable p]
    (a b : Option α) :
    Option.map f (if p then a else b) =
      if p then Option.map f a else Option.map f b := by
  by_cases h : p
  · simp only [if_pos h]
  · simp only [if_neg h]

theorem Option_map_opt {α β γ} (f : β → γ) (o : Option α) (g : α → Option β) :
    Option.map f (match o with | none => none | some x => g x) =
      match o with | none => none | some x => Option.map f (g x) := by
  cases o with
  | none => rfl
  | some _ => rfl

theorem Option_map_bind {α β γ} (f : β → γ) (o : Option α) (g : α → Option β) :
    Option.map f (o.bind g) = o.bind (fun x => Option.map f (g x)) := by
  cases o with
  | none => rfl
  | some _ => rfl

theorem map_lift_inj (c : Nat) : {xs ys : List (Expr Nat)} →
    xs.map (lift c 1) = ys.map (lift c 1) → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: xs, y :: ys, h => by
      simp only [List.map_cons] at h
      injection h with hxy hrest
      have hx := lift_inj c x y hxy
      subst hx
      exact congrArg (List.cons x) (map_lift_inj c hrest)

/-- Tail of one-shot ι after nparams/nMinors/ctorIdx are known. -/
def iotaReductTail (E : ResolvedEnv)
    (recRef : Nat) (ls : List Level) (ctorMember : CheckedMember)
    (familyRef : Nat) (ctorIdx nparams nMinors : Nat)
    (preMajor ctorArgs : List (Expr Nat)) : Option (Expr Nat) :=
  (peelPis (piCount ctorMember.mtype) ctorMember.mtype).bind fun ctorPr =>
  (analyzeFields familyRef (ctorPr.1.drop nparams)).bind fun kinds =>
  (applyTel (preMajor.take nparams)
      (instantiateLevels ls ctorMember.mtype)).bind fun ctorAfterParams =>
  (preMajor[nparams + 1 + ctorIdx]?).bind fun minor =>
    some (foldApps minor
      (rhsArgs (.const recRef ls) preMajor nparams nMinors
        (ctorArgs.drop nparams) kinds ctorAfterParams))

theorem iotaReductTail_lift (E : ResolvedEnv) (c : Nat)
    (recRef : Nat) (ls : List Level) (ctorMember : CheckedMember)
    (familyRef : Nat) (ctorIdx nparams nMinors : Nat)
    (preMajor ctorArgs : List (Expr Nat))
    (hcl : lift 0 1 ctorMember.mtype = ctorMember.mtype) :
    iotaReductTail E recRef ls ctorMember familyRef ctorIdx nparams nMinors
      (preMajor.map (lift c 1)) (ctorArgs.map (lift c 1)) =
      (iotaReductTail E recRef ls ctorMember familyRef ctorIdx nparams nMinors
        preMajor ctorArgs).map (lift c 1) := by
  unfold iotaReductTail
  conv => rhs; rw [Option_map_bind]
  cases peelPis (piCount ctorMember.mtype) ctorMember.mtype with
  | none => simp only [Option.none_bind, Option.some_bind]
  | some ctorPr =>
    simp only [Option.none_bind, Option.some_bind]
    conv => rhs; rw [Option_map_bind]
    cases analyzeFields familyRef (ctorPr.1.drop nparams) with
      | none => simp only [Option.none_bind, Option.some_bind]
      | some kinds =>
        simp only [Option.none_bind, Option.some_bind]
        have happ := applyTel_map_lift_closed c (preMajor.take nparams)
          (instantiateLevels ls ctorMember.mtype)
          (instantiateLevels_closed0 hcl ls)
        rw [← List.map_take]
        rw [happ]
        cases htel : applyTel (preMajor.take nparams)
            (instantiateLevels ls ctorMember.mtype) with
        | none =>
          simp only [htel, Option.map, Option.none_bind]
        | some ctorAfterParams =>
          simp only [htel, Option.map, Option.some_bind]
          rw [List.getElem?_map (lift c 1) preMajor (nparams + 1 + ctorIdx)]
          cases hmin : preMajor[nparams + 1 + ctorIdx]? with
          | none =>
            simp only [hmin, Option.map, Option.none_bind]
          | some minor =>
            simp only [hmin, Option.map, Option.some_bind, foldApps_lift]
            have hr :=
              (rhsArgs_lift c nparams nMinors (.const recRef ls) preMajor
                (ctorArgs.drop nparams) kinds ctorAfterParams).symm
            simp only [lift] at hr
            rw [List.map_drop] at hr
            exact congrArg (fun t => some (foldApps (lift c 1 minor) t)) hr

/-- One-shot ι reduct from the 05 §11–12 data recoverable from `E`.
The rhs is not a subterm of the lhs (same one-shot as delta). -/
def iotaReductGo (E : ResolvedEnv)
    (recRef : Nat) (ls : List Level) (recMember : CheckedMember)
    (ctorRef : Nat) (ctorMember : CheckedMember)
    (preMajor ctorArgs : List (Expr Nat)) : Option (Expr Nat) :=
  if lift 0 1 recMember.mtype = recMember.mtype then
    if lift 0 1 ctorMember.mtype = ctorMember.mtype then
      (peelPis (piCount recMember.mtype) recMember.mtype).bind fun recPr =>
      (listLast recPr.1).bind fun lastDom =>
          match (appsSpine lastDom).1 with
          | .const familyRef _ =>
            (E.members familyRef).bind fun famMember =>
              match famMember.mclass with
              | .inductiveM =>
                if familyRef < recRef then
                  if familyRef < ctorRef then
                    if ctorRef < recRef then
                      let nMinors := recRef - familyRef - 1
                      let ctorIdx := ctorRef - familyRef - 1
                      match (appsSpine recPr.2).2 with
                      | [] => none
                      | _ :: rest =>
                        let nindices := rest.length
                        let nparidx := piCount famMember.mtype
                        if nindices ≤ nparidx then
                          let nparams := nparidx - nindices
                          if preMajor.length = nparams + 1 + nMinors + nindices then
                            if preMajor.length + 1 = piCount recMember.mtype then
                              if ctorArgs.length = piCount ctorMember.mtype then
                                iotaReductTail E recRef ls ctorMember familyRef
                                  ctorIdx nparams nMinors preMajor ctorArgs
                              else none
                            else none
                          else none
                        else none
                    else none
                  else none
                else none
              | .axiomM => none
              | .definitionM => none
              | .theoremM => none
              | .opaqueM => none
              | .constructorM => none
              | .recursorM => none
          | .bvar _ => none
          | .sort _ => none
          | .app _ _ => none
          | .lam _ _ => none
          | .pi _ _ => none
          | .letE _ _ _ => none
          | .lit _ => none
    else none
  else none

def iotaReduct (E : ResolvedEnv) (e : Expr Nat) : Option (Expr Nat) :=
  match (appsSpine e).1 with
  | .const recRef ls =>
    (E.members recRef).bind fun recMember =>
      match recMember.mclass with
      | .recursorM =>
        match (appsSpine e).2.reverse with
        | [] => none
        | major :: preRev =>
          let preMajor := preRev.reverse
          match (appsSpine major).1 with
          | .const ctorRef cls =>
            (E.members ctorRef).bind fun ctorMember =>
              match ctorMember.mclass with
              | .constructorM =>
                iotaReductGo E recRef ls recMember ctorRef ctorMember
                  preMajor (appsSpine major).2
              | .axiomM => none
              | .definitionM => none
              | .theoremM => none
              | .opaqueM => none
              | .inductiveM => none
              | .recursorM => none
          | .bvar _ => none
          | .sort _ => none
          | .app _ _ => none
          | .lam _ _ => none
          | .pi _ _ => none
          | .letE _ _ _ => none
          | .lit _ => none
      | .axiomM => none
      | .definitionM => none
      | .theoremM => none
      | .opaqueM => none
      | .inductiveM => none
      | .constructorM => none
  | .bvar _ => none
  | .sort _ => none
  | .app _ _ => none
  | .lam _ _ => none
  | .pi _ _ => none
  | .letE _ _ _ => none
  | .lit _ => none

theorem appsSpine_app_lam (A body arg : Expr Nat) :
    appsSpine (.app (.lam A body) arg) = (.lam A body, [arg]) := rfl

theorem appsSpine_app_bvar (i : Nat) (arg : Expr Nat) :
    appsSpine (.app (.bvar i) arg) = (.bvar i, [arg]) := rfl

theorem iotaReduct_lam_app (E : ResolvedEnv) (A body arg : Expr Nat) :
    iotaReduct E (.app (.lam A body) arg) = none := by
  simp only [iotaReduct, appsSpine_app_lam]

theorem reverse_cons_snoc {α} {xs : List α} {y : α} {ys : List α}
    (h : xs.reverse = y :: ys) : xs = ys.reverse ++ [y] := by
  have hrev := congrArg List.reverse h
  simp [List.reverse_cons, List.reverse_reverse] at hrev
  exact hrev

/-- Build-to-pack fragment of Fill. Small enough to invert with
`split at h` (the full Fill unfold times out). -/
def iotaReductCertFillIdx (E : ResolvedEnv) (e : Expr Nat)
    (recRef ctorRef familyRef : Nat) (ls lsC : List Level)
    (recMember ctorMember famMember : CheckedMember)
    (hrec : E.members recRef = some recMember)
    (hctor : E.members ctorRef = some ctorMember)
    (hfam : E.members familyRef = some famMember)
    (hrecK : recMember.mclass = .recursorM)
    (hctorK : ctorMember.mclass = .constructorM)
    (hfamK : famMember.mclass = .inductiveM)
    (preMajor : List (Expr Nat)) (major : Expr Nat)
    (ctorArgs fields : List (Expr Nat))
    (nparams nindices nMinors ctorIdx : Nat)
    (recPr : List (Expr Nat) × Expr Nat)
    (hrecClosed : lift 0 1 recMember.mtype = recMember.mtype)
    (hctorClosed : lift 0 1 ctorMember.mtype = ctorMember.mtype)
    (hpeelRec0 : peelPis (piCount recMember.mtype) recMember.mtype = some recPr)
    (hnmin : nparams + 1 + nMinors + nindices + 1 = piCount recMember.mtype)
    (hnpar : nparams + fields.length = piCount ctorMember.mtype)
    (hnidx : nparams + nindices = piCount famMember.mtype)
    (hidx : ctorIdx < nMinors)
    (hctorIdx : ctorRef = familyRef + 1 + ctorIdx)
    (hrecIdx : recRef = familyRef + 1 + nMinors)
    (hpre : preMajor.length = nparams + 1 + nMinors + nindices)
    (hfields : fields = ctorArgs.drop nparams)
    (hle : nparams ≤ ctorArgs.length)
    (hhead : (appsSpine e).1 = .const recRef ls)
    (hargs : (appsSpine e).2 = preMajor ++ [major])
    (hmaj : (appsSpine major).1 = .const ctorRef lsC)
    (hctorArgs : (appsSpine major).2 = ctorArgs)
    (kinds : List RecKind) (ctorAfterParams mdom restMin minor motive : Expr Nat)
    (ctorPr : List (Expr Nat) × Expr Nat)
    (hpeel : peelPis (nparams + fields.length) ctorMember.mtype = some ctorPr)
    (hfamApp : isFamilyApp familyRef ctorPr.2 = true)
    (hkinds : analyzeFields familyRef (ctorPr.1.drop nparams) = some kinds)
    (hlen : kinds.length = fields.length)
    (hminor : preMajor[nparams + 1 + ctorIdx]? = some minor)
    (hmotive : preMajor[nparams]? = some motive)
    (hminDom : applyTel (preMajor.take (nparams + 1 + ctorIdx))
        (instantiateLevels ls recMember.mtype) = some (.pi mdom restMin))
    (hctorAfter : applyTel (preMajor.take nparams)
        (instantiateLevels ls ctorMember.mtype) = some ctorAfterParams)
    (hctorTel : isPiTel kinds.length ctorAfterParams = true)
    (hfamTel : directRecConstHead kinds ctorAfterParams = true)
    (hresTel : resultConstHead kinds ctorAfterParams = true) :
    Option (Σ' (w : IotaWitness E), iotaLhsOf w = e) :=
    if hrecBody : recPr.2 =
        foldApps
          (.bvar (nMinors + nindices + 1))
          ((List.range nindices).reverse.map
            (fun i => Expr.bvar (i + 1)) ++
            [Expr.bvar 0]) then
      if hmajorTy :
          recPr.1[nparams + 1 + nMinors + nindices]? =
          some (foldApps (.const familyRef
            ((List.range famMember.arity).map Level.param))
            ((List.range nparams).reverse.map
              (fun i => Expr.bvar
                (i + nindices + nMinors + 1)) ++
            (List.range nindices).reverse.map
              (fun i => Expr.bvar i))) then
        if hlsLen : ls.length = recMember.arity then
          have hpeelRec :
              peelPis (nparams + 1 + nMinors + nindices + 1)
                recMember.mtype = some recPr := by
            rw [hnmin]; exact hpeelRec0
          let w : IotaWitness E := {
                    recRef := recRef
                    ctorRef := ctorRef
                    ls := ls
                    lsC := lsC
                    recMember := recMember
                    ctorMember := ctorMember
                    hrec := hrec
                    hctor := hctor
                    hrecK := hrecK
                    hctorK := hctorK
                    preMajor := preMajor
                    fields := fields
                    ctorParams := ctorArgs.take nparams
                    kinds := kinds
                    minor := minor
                    hlen := hlen
                    familyRef := familyRef
                    famMember := famMember
                    hfam := hfam
                    hfamK := hfamK
                    nparams := nparams
                    nindices := nindices
                    nMinors := nMinors
                    ctorIdx := ctorIdx
                    hctorParams := by
                      simp only [List.length_take]
                      exact Nat.min_eq_left hle
                    hnpar := hnpar
                    hnidx := hnidx
                    hnmin := hnmin
                    hidx := hidx
                    hctorIdx := hctorIdx
                    hrecIdx := hrecIdx
                    hpre := hpre
                    hminor := hminor
                    ctorDoms := ctorPr.1
                    ctorResult := ctorPr.2
                    hpeel := hpeel
                    hfamApp := hfamApp
                    hkinds := hkinds
                    recDoms := recPr.1
                    recBody := recPr.2
                    hpeelRec := hpeelRec
                    hrecBody := hrecBody
                    hmajorTy := hmajorTy
                    hrecClosed := hrecClosed
                    hctorClosed := hctorClosed
                    hlsLen := hlsLen
                    ctorAfterParams := ctorAfterParams
                    hctorAfter := hctorAfter
                    hctorTel := hctorTel
                    hfamTel := hfamTel
                    hresTel := hresTel
                  }
                  have hlhs : iotaLhsOf w = e := by
                    unfold iotaLhsOf ctorMajor ctorSpine recCall
                    have hmaj' :
                        foldApps (.const ctorRef lsC) ctorArgs = major := by
                      have hsp := foldApps_appsSpine major
                      rw [hmaj, hctorArgs] at hsp
                      exact hsp
                    have hca :
                        ctorArgs.take nparams ++ fields = ctorArgs := by
                      rw [hfields, List.take_append_drop]
                    rw [hca, hmaj']
                    have hsp := foldApps_appsSpine e
                    rw [hhead, hargs] at hsp
                    exact hsp
          some ⟨w, hlhs⟩
        else none
      else none
    else none

/-- Remaining decidable checks and `IotaWitness` assembly. -/
def iotaReductCertFill (E : ResolvedEnv) (e : Expr Nat)
    (recRef ctorRef familyRef : Nat) (ls lsC : List Level)
    (recMember ctorMember famMember : CheckedMember)
    (hrec : E.members recRef = some recMember)
    (hctor : E.members ctorRef = some ctorMember)
    (hfam : E.members familyRef = some famMember)
    (hrecK : recMember.mclass = .recursorM)
    (hctorK : ctorMember.mclass = .constructorM)
    (hfamK : famMember.mclass = .inductiveM)
    (preMajor : List (Expr Nat)) (major : Expr Nat)
    (ctorArgs fields : List (Expr Nat))
    (nparams nindices nMinors ctorIdx : Nat)
    (recPr : List (Expr Nat) × Expr Nat)
    (hrecClosed : lift 0 1 recMember.mtype = recMember.mtype)
    (hctorClosed : lift 0 1 ctorMember.mtype = ctorMember.mtype)
    (hpeelRec0 : peelPis (piCount recMember.mtype) recMember.mtype = some recPr)
    (hnmin : nparams + 1 + nMinors + nindices + 1 = piCount recMember.mtype)
    (hnpar : nparams + fields.length = piCount ctorMember.mtype)
    (hnidx : nparams + nindices = piCount famMember.mtype)
    (hidx : ctorIdx < nMinors)
    (hctorIdx : ctorRef = familyRef + 1 + ctorIdx)
    (hrecIdx : recRef = familyRef + 1 + nMinors)
    (hpre : preMajor.length = nparams + 1 + nMinors + nindices)
    (hfields : fields = ctorArgs.drop nparams)
    (hle : nparams ≤ ctorArgs.length)
    (hhead : (appsSpine e).1 = .const recRef ls)
    (hargs : (appsSpine e).2 = preMajor ++ [major])
    (hmaj : (appsSpine major).1 = .const ctorRef lsC)
    (hctorArgs : (appsSpine major).2 = ctorArgs) :
    Option (Σ' (w : IotaWitness E), iotaLhsOf w = e) :=
  match hpeel : peelPis (nparams + fields.length) ctorMember.mtype with
  | none => none
  | some ctorPr =>
    if hfamApp : isFamilyApp familyRef ctorPr.2 = true then
      match hkinds : analyzeFields familyRef (ctorPr.1.drop nparams) with
      | none => none
      | some kinds =>
        if hlen : kinds.length = fields.length then
          match hminor : preMajor[nparams + 1 + ctorIdx]? with
          | none => none
          | some minor =>
            match hmotive : preMajor[nparams]? with
            | none => none
            | some motive =>
              match hminDom :
                  applyTel (preMajor.take (nparams + 1 + ctorIdx))
                    (instantiateLevels ls recMember.mtype) with
              | none => none
              | some (.bvar _) => none
              | some (.sort _) => none
              | some (.const _ _) => none
              | some (.app _ _) => none
              | some (.lam _ _) => none
              | some (.letE _ _ _) => none
              | some (.lit _) => none
              | some (.pi mdom restMin) =>
                match hctorAfter :
                    applyTel (preMajor.take nparams)
                      (instantiateLevels ls ctorMember.mtype) with
                | none => none
                | some ctorAfterParams =>
                  if hctorTel : isPiTel kinds.length ctorAfterParams = true then
                    if hfamTel :
                        directRecConstHead kinds ctorAfterParams = true then
                      if hresTel :
                          resultConstHead kinds ctorAfterParams = true then
                        iotaReductCertFillIdx E e recRef ctorRef familyRef ls lsC
                          recMember ctorMember famMember hrec hctor hfam
                          hrecK hctorK hfamK preMajor major ctorArgs fields
                          nparams nindices nMinors ctorIdx recPr
                          hrecClosed hctorClosed hpeelRec0 hnmin hnpar hnidx
                          hidx hctorIdx hrecIdx hpre hfields hle hhead hargs
                          hmaj hctorArgs kinds ctorAfterParams mdom restMin
                          minor motive ctorPr hpeel hfamApp hkinds hlen hminor
                          hmotive hminDom hctorAfter hctorTel hfamTel hresTel
                      else none
                    else none
                  else none
        else none
    else none

-- Deleted: `iotaReductCertFill_hcanon` packed idxPositions (moved to IotaTyping / EnvWf).
/-- Ctor-suffix of cert: from `E.members ctorRef` through Fill.
Extracted so FromSpine's `hls` then-branch is an opaque call. -/
def iotaReductCertFromCtor (E : ResolvedEnv) (e : Expr Nat)
    (sp : Expr Nat × List (Expr Nat))
    (heq : appsSpine e = sp)
    (recRef : Nat) (ls lsC : List Level)
    (recMember : CheckedMember)
    (hrec : E.members recRef = some recMember)
    (hrecK : recMember.mclass = .recursorM)
    (preRev : List (Expr Nat)) (major : Expr Nat)
    (hrev : sp.2.reverse = major :: preRev)
    (ctorRef : Nat)
    (hmaj : (appsSpine major).1 = .const ctorRef lsC)
    (hhead : sp.1 = .const recRef ls) :
    Option (Σ' (w : IotaWitness E), iotaLhsOf w = e) :=
  match hctor : E.members ctorRef with
  | none => none
  | some ctorMember =>
    if hctorK : ctorMember.mclass = .constructorM then
      if hrecClosed : lift 0 1 recMember.mtype = recMember.mtype then
        if hctorClosed : lift 0 1 ctorMember.mtype = ctorMember.mtype then
          match hpeelRec0 :
              peelPis (piCount recMember.mtype) recMember.mtype with
          | none => none
          | some recPr =>
            match hlast : listLast recPr.1 with
            | none => none
            | some lastDom =>
              match hfamH : (appsSpine lastDom).1 with
              | .bvar _ => none
              | .sort _ => none
              | .app _ _ => none
              | .lam _ _ => none
              | .pi _ _ => none
              | .letE _ _ _ => none
              | .lit _ => none
              | .const familyRef _ =>
                match hfam : E.members familyRef with
                | none => none
                | some famMember =>
                  if hfamK : famMember.mclass = .inductiveM then
                    if hfr : familyRef < recRef then
                      if hfc : familyRef < ctorRef then
                        if hcr : ctorRef < recRef then
                          let nMinors := recRef - familyRef - 1
                          let ctorIdx := ctorRef - familyRef - 1
                          match hrest : (appsSpine recPr.2).2 with
                          | [] => none
                          | _ :: rest =>
                            let nindices := rest.length
                            let nparidx := piCount famMember.mtype
                            if hnidxle : nindices ≤ nparidx then
                              let nparams := nparidx - nindices
                              if hpre : preRev.reverse.length =
                                  nparams + 1 + nMinors + nindices then
                                if harity : preRev.reverse.length + 1 =
                                    piCount recMember.mtype then
                                let ctorArgs := (appsSpine major).2
                                if hctorLen : ctorArgs.length =
                                    piCount ctorMember.mtype then
                                  if hle : nparams ≤ ctorArgs.length then
                                    let fields := ctorArgs.drop nparams
                                    have hnmin :
                                        nparams + 1 + nMinors +
                                          nindices + 1 =
                                        piCount recMember.mtype := by omega
                                    have hnpar :
                                        nparams + fields.length =
                                        piCount ctorMember.mtype := by
                                      simp only [fields, List.length_drop,
                                        hctorLen]; omega
                                    have hnidx :
                                        nparams + nindices =
                                        piCount famMember.mtype := by
                                      simp only [nparams]; omega
                                    have hidx : ctorIdx < nMinors := by
                                      simp only [ctorIdx, nMinors]; omega
                                    have hctorIdx : ctorRef =
                                        familyRef + 1 + ctorIdx := by
                                      simp only [ctorIdx]; omega
                                    have hrecIdx : recRef =
                                        familyRef + 1 + nMinors := by
                                      simp only [nMinors]; omega
                                    have hheadE :
                                        (appsSpine e).1 =
                                          .const recRef ls := by
                                      rw [heq]; exact hhead
                                    have hargs :
                                        (appsSpine e).2 =
                                          preRev.reverse ++ [major] := by
                                      rw [heq]
                                      exact reverse_cons_snoc hrev
                                    iotaReductCertFill E e
                                      recRef ctorRef familyRef ls lsC
                                      recMember ctorMember famMember
                                      hrec hctor hfam hrecK hctorK
                                      hfamK preRev.reverse major ctorArgs
                                      fields nparams nindices
                                      nMinors ctorIdx recPr
                                      hrecClosed hctorClosed
                                      hpeelRec0 hnmin hnpar hnidx
                                      hidx hctorIdx hrecIdx hpre
                                      rfl hle hheadE hargs hmaj rfl
                                  else none
                                else none
                              else none
                            else none
                          else none
                        else none
                      else none
                    else none
                  else none
        else none
      else none
    else none

-- Deleted: `iotaReductCertFromCtor_hcanon` packed idxPositions (moved to IotaTyping / EnvWf).
/-- Spine-parameterized cert. `heq` lets callers rewrite `appsSpine e`
without a dependent match on that spine. `hls` then-branch is the
opaque `FromCtor` call (FillIdx extraction pattern). -/
def iotaReductCertFromSpine (E : ResolvedEnv) (e : Expr Nat)
    (sp : Expr Nat × List (Expr Nat))
    (heq : appsSpine e = sp) :
    Option (Σ' (w : IotaWitness E), iotaLhsOf w = e) :=
  match hhead : sp.1 with
  | .bvar _ => none
  | .sort _ => none
  | .app _ _ => none
  | .lam _ _ => none
  | .pi _ _ => none
  | .letE _ _ _ => none
  | .lit _ => none
  | .const recRef ls =>
    match hrec : E.members recRef with
    | none => none
    | some recMember =>
      if hrecK : recMember.mclass = .recursorM then
        match hrev : sp.2.reverse with
        | [] => none
        | major :: preRev =>
          match hmaj : (appsSpine major).1 with
          | .bvar _ => none
          | .sort _ => none
          | .app _ _ => none
          | .lam _ _ => none
          | .pi _ _ => none
          | .letE _ _ _ => none
          | .lit _ => none
          | .const ctorRef cls =>
            iotaReductCertFromCtor E e sp heq recRef ls cls recMember
              hrec hrecK preRev major hrev ctorRef hmaj hhead
      else none

/-- Certifying ι: each `IotaWitness` field is a captured `if h :` /
`match h :` on a decidable Eq/Bool/Option. No Prop quantifiers. -/
def iotaReductCert (E : ResolvedEnv) (e : Expr Nat) :
    Option (Σ' (w : IotaWitness E), iotaLhsOf w = e) :=
  iotaReductCertFromSpine E e (appsSpine e) rfl

theorem iotaReductCertFromSpine_eq_spine {E : ResolvedEnv}
    {e : Expr Nat} {sp sp' : Expr Nat × List (Expr Nat)}
    (heq : appsSpine e = sp) (h : sp = sp') :
    iotaReductCertFromSpine E e sp heq =
      iotaReductCertFromSpine E e sp' (h ▸ heq) := by
  subst h
  rfl

theorem iotaReductCert_eq_spine (E : ResolvedEnv) (e : Expr Nat)
    (sp : Expr Nat × List (Expr Nat)) (h : appsSpine e = sp) :
    iotaReductCert E e = iotaReductCertFromSpine E e sp h :=
  iotaReductCertFromSpine_eq_spine rfl h

theorem iotaReductGo_lift (E : ResolvedEnv) (c : Nat)
    (recRef : Nat) (ls : List Level) (recMember : CheckedMember)
    (ctorRef : Nat) (ctorMember : CheckedMember)
    (preMajor ctorArgs : List (Expr Nat)) :
    iotaReductGo E recRef ls recMember ctorRef ctorMember
      (preMajor.map (lift c 1)) (ctorArgs.map (lift c 1)) =
      (iotaReductGo E recRef ls recMember ctorRef ctorMember
        preMajor ctorArgs).map (lift c 1) := by
  unfold iotaReductGo
  simp only [List.length_map]
  conv => rhs; rw [Option_map_ite]
  split
  · conv => rhs; rw [Option_map_ite]
    split
    · conv => rhs; rw [Option_map_bind]
      cases peelPis (piCount recMember.mtype) recMember.mtype with
      | none => simp only [Option.none_bind, Option.some_bind]
      | some recPr =>
        simp only [Option.none_bind, Option.some_bind]
        conv => rhs; rw [Option_map_bind]
        cases listLast recPr.1 with
          | none => simp only [Option.none_bind, Option.some_bind]
          | some lastDom =>
            simp only [Option.none_bind, Option.some_bind]
            cases hhd : (appsSpine lastDom).1 with
            | const familyRef _fls =>
              conv => rhs; rw [Option_map_bind]
              cases hfamM : E.members familyRef with
              | none =>
                simp only [hfamM, Option.none_bind, Option.map]
              | some famMember =>
                simp only [hfamM, Option.none_bind, Option.some_bind]
                cases famMember.mclass with
                | inductiveM =>
                  simp only [Option_map_ite, Option.map]
                  split
                  · split
                    · split
                      · cases (appsSpine recPr.2).2 with
                        | nil => rfl
                        | cons _ rest =>
                          simp only [Option_map_ite, Option.map]
                          split
                          · split
                            · split
                              · split
                                · exact iotaReductTail_lift E c recRef ls
                                    ctorMember familyRef
                                    (ctorRef - familyRef - 1)
                                    (piCount famMember.mtype - rest.length)
                                    (recRef - familyRef - 1)
                                    preMajor ctorArgs (by assumption)
                                · rfl
                              · rfl
                            · rfl
                          · rfl
                      · rfl
                    · rfl
                  · rfl
                | axiomM => simp only [Option.map]
                | definitionM => simp only [Option.map]
                | theoremM => simp only [Option.map]
                | opaqueM => simp only [Option.map]
                | constructorM => simp only [Option.map]
                | recursorM => simp only [Option.map]
            | bvar _ => simp only [Option.map]
            | sort _ => simp only [Option.map]
            | app _ _ => simp only [Option.map]
            | lam _ _ => simp only [Option.map]
            | pi _ _ => simp only [Option.map]
            | letE _ _ _ => simp only [Option.map]
            | lit _ => simp only [Option.map]
    · simp only [Option.map]
  · simp only [Option.map]

theorem iotaReduct_lift (E : ResolvedEnv) (c : Nat) :
    (e : Expr Nat) →
    iotaReduct E (lift c 1 e) = (iotaReduct E e).map (lift c 1)
  | e => by
      have hsp := appsSpine_lift c 1 e
      simp only [iotaReduct]
      rw [hsp]
      cases hhead : (appsSpine e).1 with
      | const recRef ls =>
          simp only [hhead, lift]
          conv => rhs; rw [Option_map_bind]
          cases hmem : E.members recRef with
          | none => simp only [hmem, Option.none_bind, Option.map]
          | some recMember =>
            simp only [hmem, Option.some_bind]
            cases hmcl : recMember.mclass with
            | recursorM =>
              have hrev :
                  ((appsSpine e).2.map (lift c 1)).reverse =
                    (appsSpine e).2.reverse.map (lift c 1) :=
                (List.map_reverse (lift c 1) (appsSpine e).2).symm
              rw [hrev]
              cases hsnoc : (appsSpine e).2.reverse with
              | nil => rfl
              | cons major preRev =>
                simp only [List.map_cons]
                have hpre :
                    (preRev.map (lift c 1)).reverse =
                      preRev.reverse.map (lift c 1) :=
                  (List.map_reverse (lift c 1) preRev).symm
                rw [hpre]
                have hmaj := appsSpine_lift c 1 major
                rw [hmaj]
                cases hch : (appsSpine major).1 with
                | const ctorRef cls =>
                    simp only [hch, lift]
                    conv => rhs; rw [Option_map_bind]
                    cases hcm : E.members ctorRef with
                    | none => simp only [hcm, Option.none_bind, Option.map]
                    | some ctorMember =>
                      simp only [hcm, Option.some_bind]
                      cases hccl : ctorMember.mclass with
                      | constructorM =>
                        exact iotaReductGo_lift E c recRef ls recMember
                          ctorRef ctorMember preRev.reverse
                          (appsSpine major).2
                      | axiomM => simp only [Option.map]
                      | definitionM => simp only [Option.map]
                      | theoremM => simp only [Option.map]
                      | opaqueM => simp only [Option.map]
                      | inductiveM => simp only [Option.map]
                      | recursorM => simp only [Option.map]
                | bvar i =>
                    simp only [hch, lift]
                    by_cases hi : c ≤ i
                    · rw [if_pos hi]; rfl
                    · rw [if_neg hi]; rfl
                | sort _ => simp only [hch, lift, Option.map]
                | app _ _ => simp only [hch, lift, Option.map]
                | lam _ _ => simp only [hch, lift, Option.map]
                | pi _ _ => simp only [hch, lift, Option.map]
                | letE _ _ _ => simp only [hch, lift, Option.map]
                | lit _ => simp only [hch, lift, Option.map]
            | axiomM => simp only [Option.map]
            | definitionM => simp only [Option.map]
            | theoremM => simp only [Option.map]
            | opaqueM => simp only [Option.map]
            | inductiveM => simp only [Option.map]
            | constructorM => simp only [Option.map]
      | bvar i =>
          simp only [hhead, lift]
          by_cases hi : c ≤ i
          · rw [if_pos hi]; rfl
          · rw [if_neg hi]; rfl
      | sort _ => simp only [hhead, lift, Option.map]
      | app _ _ => simp only [hhead, lift, Option.map]
      | lam _ _ => simp only [hhead, lift, Option.map]
      | pi _ _ => simp only [hhead, lift, Option.map]
      | letE _ _ _ => simp only [hhead, lift, Option.map]
      | lit _ => simp only [hhead, lift, Option.map]

def devel (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Expr Nat → Expr Nat
  | .sort l => .sort l
  | .lit t => natExpand t
  | .const r ls =>
      match E.members r with
      | some m =>
          if transparent m.mclass = true then
            match m.body with
            -- 00 §20.6: the complete development of a delta redex is the
            -- LEVEL-INSTANTIATED body, matching `ParRed.delta`'s new
            -- conclusion index. At `ls = []` (the only case reachable
            -- under `EnvWf`, by `envWf_body_arity_zero`) this is the
            -- stored `b` verbatim (`instantiateLevels_nil`).
            | some b => instantiateLevels ls b
            | none => .const r ls
          else .const r ls
      | none => .const r ls
  | .bvar i =>
      match lookupValue Γ i with
      | some v => v
      | none => .bvar i
  | .app f a =>
      match iotaReduct E (.app f a) with
      | some rhs => rhs
      | none =>
          let f' := devel E n Γ f
          let a' := devel E n Γ a
          match f' with
          | .lam _ b => instantiate0 a' b
          | _ => .app f' a'
  | .lam A b =>
      .lam (devel E n Γ A) (devel E n (LocalDecl.assumption A :: Γ) b)
  | .pi A B =>
      .pi (devel E n Γ A) (devel E n (LocalDecl.assumption A :: Γ) B)
  | .letE A v b =>
      instantiate0 (devel E n Γ v)
        (devel E n (LocalDecl.letBinding A v :: Γ) b)

theorem devel_sort (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (l : Level) :
    devel E n Γ (.sort l) = .sort l := rfl

theorem devel_lit (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (t : Nat) :
    devel E n Γ (.lit t) = natExpand t := rfl

/-- nfRel of complete developments: sorts up to =ₙ, else syntactic. -/
def nfRel : Expr Nat → Expr Nat → Prop
  | .sort u, .sort v => eqN u v
  | .const r ls, .const r' ls' => r = r' ∧ eqNList ls ls'
  | a, b => a = b

theorem nfRel_refl : (e : Expr Nat) → nfRel e e
  | .sort l => eqN_refl l
  | .const r ls => ⟨rfl, eqNList_refl ls⟩
  | .bvar _ => rfl
  | .app _ _ => rfl
  | .lam _ _ => rfl
  | .pi _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

theorem nfRel_symm : {a b : Expr Nat} → nfRel a b → nfRel b a
  | .sort u, .sort v, h => eqN_symm h
  | .const r ls, .const r' ls', h => ⟨h.1.symm, eqNList_symm h.2⟩
  | .sort _, .bvar _, h => nomatch h
  | .sort _, .const _ _, h => nomatch h
  | .sort _, .app _ _, h => nomatch h
  | .sort _, .lam _ _, h => nomatch h
  | .sort _, .pi _ _, h => nomatch h
  | .sort _, .letE _ _ _, h => nomatch h
  | .sort _, .lit _, h => nomatch h
  | .const _ _, .sort _, h => nomatch h
  | .const _ _, .bvar _, h => nomatch h
  | .const _ _, .app _ _, h => nomatch h
  | .const _ _, .lam _ _, h => nomatch h
  | .const _ _, .pi _ _, h => nomatch h
  | .const _ _, .letE _ _ _, h => nomatch h
  | .const _ _, .lit _, h => nomatch h
  | .bvar _, .sort _, h => nomatch h
  | .app _ _, .sort _, h => nomatch h
  | .lam _ _, .sort _, h => nomatch h
  | .pi _ _, .sort _, h => nomatch h
  | .letE _ _ _, .sort _, h => nomatch h
  | .lit _, .sort _, h => nomatch h
  | .bvar _, .const _ _, h => nomatch h
  | .app _ _, .const _ _, h => nomatch h
  | .lam _ _, .const _ _, h => nomatch h
  | .pi _ _, .const _ _, h => nomatch h
  | .letE _ _ _, .const _ _, h => nomatch h
  | .lit _, .const _ _, h => nomatch h
  | .bvar i, .bvar j, h => h.symm
  | .app f a, .app g b, h => h.symm
  | .lam A b, .lam A' b', h => h.symm
  | .pi A B, .pi A' B', h => h.symm
  | .letE A v b, .letE A' v' b', h => h.symm
  | .lit t, .lit t', h => h.symm
  | .bvar _, .app _ _, h => nomatch h
  | .bvar _, .lam _ _, h => nomatch h
  | .bvar _, .pi _ _, h => nomatch h
  | .bvar _, .letE _ _ _, h => nomatch h
  | .bvar _, .lit _, h => nomatch h
  | .app _ _, .bvar _, h => nomatch h
  | .app _ _, .lam _ _, h => nomatch h
  | .app _ _, .pi _ _, h => nomatch h
  | .app _ _, .letE _ _ _, h => nomatch h
  | .app _ _, .lit _, h => nomatch h
  | .lam _ _, .bvar _, h => nomatch h
  | .lam _ _, .app _ _, h => nomatch h
  | .lam _ _, .pi _ _, h => nomatch h
  | .lam _ _, .letE _ _ _, h => nomatch h
  | .lam _ _, .lit _, h => nomatch h
  | .pi _ _, .bvar _, h => nomatch h
  | .pi _ _, .app _ _, h => nomatch h
  | .pi _ _, .lam _ _, h => nomatch h
  | .pi _ _, .letE _ _ _, h => nomatch h
  | .pi _ _, .lit _, h => nomatch h
  | .letE _ _ _, .bvar _, h => nomatch h
  | .letE _ _ _, .app _ _, h => nomatch h
  | .letE _ _ _, .lam _ _, h => nomatch h
  | .letE _ _ _, .pi _ _, h => nomatch h
  | .letE _ _ _, .lit _, h => nomatch h
  | .lit _, .bvar _, h => nomatch h
  | .lit _, .app _ _, h => nomatch h
  | .lit _, .lam _ _, h => nomatch h
  | .lit _, .pi _ _, h => nomatch h
  | .lit _, .letE _ _ _, h => nomatch h

theorem nfRel_trans : {a b c : Expr Nat} → nfRel a b → nfRel b c → nfRel a c
  | .sort u, .sort v, .sort w, h1, h2 => eqN_trans h1 h2
  | .sort _, .sort _, .bvar _, _, h2 => nomatch h2
  | .sort _, .sort _, .const _ _, _, h2 => nomatch h2
  | .sort _, .sort _, .app _ _, _, h2 => nomatch h2
  | .sort _, .sort _, .lam _ _, _, h2 => nomatch h2
  | .sort _, .sort _, .pi _ _, _, h2 => nomatch h2
  | .sort _, .sort _, .letE _ _ _, _, h2 => nomatch h2
  | .sort _, .sort _, .lit _, _, h2 => nomatch h2
  | .const r ls, .const r' ls', .const r'' ls'', h1, h2 =>
      ⟨h1.1.trans h2.1, eqNList_trans h1.2 h2.2⟩
  | .const _ _, .const _ _, .sort _, _, h2 => nomatch h2
  | .const _ _, .const _ _, .bvar _, _, h2 => nomatch h2
  | .const _ _, .const _ _, .app _ _, _, h2 => nomatch h2
  | .const _ _, .const _ _, .lam _ _, _, h2 => nomatch h2
  | .const _ _, .const _ _, .pi _ _, _, h2 => nomatch h2
  | .const _ _, .const _ _, .letE _ _ _, _, h2 => nomatch h2
  | .const _ _, .const _ _, .lit _, _, h2 => nomatch h2
  | .sort _, .bvar _, _, h1, _ => nomatch h1
  | .sort _, .const _ _, _, h1, _ => nomatch h1
  | .sort _, .app _ _, _, h1, _ => nomatch h1
  | .sort _, .lam _ _, _, h1, _ => nomatch h1
  | .sort _, .pi _ _, _, h1, _ => nomatch h1
  | .sort _, .letE _ _ _, _, h1, _ => nomatch h1
  | .sort _, .lit _, _, h1, _ => nomatch h1
  | .const _ _, .sort _, _, h1, _ => nomatch h1
  | .const _ _, .bvar _, _, h1, _ => nomatch h1
  | .const _ _, .app _ _, _, h1, _ => nomatch h1
  | .const _ _, .lam _ _, _, h1, _ => nomatch h1
  | .const _ _, .pi _ _, _, h1, _ => nomatch h1
  | .const _ _, .letE _ _ _, _, h1, _ => nomatch h1
  | .const _ _, .lit _, _, h1, _ => nomatch h1
  | .bvar _, .sort _, _, h1, _ => nomatch h1
  | .app _ _, .sort _, _, h1, _ => nomatch h1
  | .lam _ _, .sort _, _, h1, _ => nomatch h1
  | .pi _ _, .sort _, _, h1, _ => nomatch h1
  | .letE _ _ _, .sort _, _, h1, _ => nomatch h1
  | .lit _, .sort _, _, h1, _ => nomatch h1
  | .bvar _, .const _ _, _, h1, _ => nomatch h1
  | .app _ _, .const _ _, _, h1, _ => nomatch h1
  | .lam _ _, .const _ _, _, h1, _ => nomatch h1
  | .pi _ _, .const _ _, _, h1, _ => nomatch h1
  | .letE _ _ _, .const _ _, _, h1, _ => nomatch h1
  | .lit _, .const _ _, _, h1, _ => nomatch h1
  | .bvar i, .bvar j, c, h1, h2 => by
      cases h1
      exact h2
  | .app f a, .app g b, c, h1, h2 => by
      cases h1
      exact h2
  | .lam A b, .lam A' b', c, h1, h2 => by
      cases h1
      exact h2
  | .pi A B, .pi A' B', c, h1, h2 => by
      cases h1
      exact h2
  | .letE A v b, .letE A' v' b', c, h1, h2 => by
      cases h1
      exact h2
  | .lit t, .lit t', c, h1, h2 => by
      cases h1
      exact h2
  | .bvar _, .app _ _, _, h1, _ => nomatch h1
  | .bvar _, .lam _ _, _, h1, _ => nomatch h1
  | .bvar _, .pi _ _, _, h1, _ => nomatch h1
  | .bvar _, .letE _ _ _, _, h1, _ => nomatch h1
  | .bvar _, .lit _, _, h1, _ => nomatch h1
  | .app _ _, .bvar _, _, h1, _ => nomatch h1
  | .app _ _, .lam _ _, _, h1, _ => nomatch h1
  | .app _ _, .pi _ _, _, h1, _ => nomatch h1
  | .app _ _, .letE _ _ _, _, h1, _ => nomatch h1
  | .app _ _, .lit _, _, h1, _ => nomatch h1
  | .lam _ _, .bvar _, _, h1, _ => nomatch h1
  | .lam _ _, .app _ _, _, h1, _ => nomatch h1
  | .lam _ _, .pi _ _, _, h1, _ => nomatch h1
  | .lam _ _, .letE _ _ _, _, h1, _ => nomatch h1
  | .lam _ _, .lit _, _, h1, _ => nomatch h1
  | .pi _ _, .bvar _, _, h1, _ => nomatch h1
  | .pi _ _, .app _ _, _, h1, _ => nomatch h1
  | .pi _ _, .lam _ _, _, h1, _ => nomatch h1
  | .pi _ _, .letE _ _ _, _, h1, _ => nomatch h1
  | .pi _ _, .lit _, _, h1, _ => nomatch h1
  | .letE _ _ _, .bvar _, _, h1, _ => nomatch h1
  | .letE _ _ _, .app _ _, _, h1, _ => nomatch h1
  | .letE _ _ _, .lam _ _, _, h1, _ => nomatch h1
  | .letE _ _ _, .pi _ _, _, h1, _ => nomatch h1
  | .letE _ _ _, .lit _, _, h1, _ => nomatch h1
  | .lit _, .bvar _, _, h1, _ => nomatch h1
  | .lit _, .app _ _, _, h1, _ => nomatch h1
  | .lit _, .lam _ _, _, h1, _ => nomatch h1
  | .lit _, .pi _ _, _, h1, _ => nomatch h1
  | .lit _, .letE _ _ _, _, h1, _ => nomatch h1

theorem nfRel_sort_eq {u v : Level} (h : nfRel (.sort u) (.sort v)) : eqN u v := h

/-- SortConvChar from nfRel of developments: `devel (sort u) = sort u`. -/
theorem sortConvChar_of_nfRel {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {u v : Level}
    (h : nfRel (devel E n Γ (.sort u)) (devel E n Γ (.sort v))) : eqN u v := by
  simp only [devel] at h
  exact h

/-- `devel` depends only on `lookupValue`, not assumption-types. -/
theorem devel_ctx_lookup {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx}
    (hΓ : ∀ i, lookupValue Γ i = lookupValue Γ' i) :
    (e : Expr Nat) → devel E n Γ e = devel E n Γ' e
  | .sort _ => rfl
  | .lit _ => rfl
  | .const _ _ => rfl
  | .bvar i => by simp only [devel, hΓ i]
  | .app f a => by
      simp only [devel]
      cases iotaReduct E (.app f a) with
      | some _ => rfl
      | none =>
          simp only [devel_ctx_lookup hΓ f, devel_ctx_lookup hΓ a]
  | .lam A b => by
      have hΓ' : ∀ i, lookupValue (.assumption A :: Γ) i =
          lookupValue (.assumption A :: Γ') i := by
        intro i; cases i with
        | zero => rfl
        | succ i => simp only [lookupValue_cons_succ, hΓ]
      simp only [devel, devel_ctx_lookup hΓ A, devel_ctx_lookup hΓ' b]
  | .pi A B => by
      have hΓ' : ∀ i, lookupValue (.assumption A :: Γ) i =
          lookupValue (.assumption A :: Γ') i := by
        intro i; cases i with
        | zero => rfl
        | succ i => simp only [lookupValue_cons_succ, hΓ]
      simp only [devel, devel_ctx_lookup hΓ A, devel_ctx_lookup hΓ' B]
  | .letE A v b => by
      have hΓ' : ∀ i, lookupValue (.letBinding A v :: Γ) i =
          lookupValue (.letBinding A v :: Γ') i := by
        intro i; cases i with
        | zero => rfl
        | succ i => simp only [lookupValue_cons_succ, hΓ]
      simp only [devel, devel_ctx_lookup hΓ A, devel_ctx_lookup hΓ v,
        devel_ctx_lookup hΓ' b]

theorem lookupValue_assump_irrel (A A' : Expr Nat) (Γ : LCtx) (i : Nat) :
    lookupValue (.assumption A :: Γ) i =
      lookupValue (.assumption A' :: Γ) i :=
  lookupValue_assumption_irrel A A' Γ i

theorem devel_replace_assump {E : ResolvedEnv} {n : Nat}
    (A A' : Expr Nat) (Γ : LCtx) (e : Expr Nat) :
    devel E n (.assumption A :: Γ) e =
      devel E n (.assumption A' :: Γ) e :=
  devel_ctx_lookup (lookupValue_assump_irrel A A' Γ) e

/-- Missed lookup stays missed at-or-above the insertion. -/
theorem lookupValue_insertAt_ge_none (d : LocalDecl) {c i : Nat} {Γ : LCtx}
    (hic : c ≤ i) (h : lookupValue Γ i = none) :
    lookupValue (insertAt d c Γ) (i + 1) = none := by
  induction c generalizing i Γ with
  | zero =>
      rw [insertAt_zero, lookupValue_cons_succ, h]
      rfl
  | succ c ih =>
    match Γ with
    | [] =>
        match i with
        | 0 => omega
        | _ + 1 =>
            simp only [insertAt, lookupValue, List.get?_cons_succ, List.get?]
    | _x :: Γ' =>
      match i with
      | 0 => omega
      | i' + 1 =>
        rw [lookupValue_cons_succ] at h
        simp only [Option.map_eq_none'] at h
        rw [insertAt_succ_cons, lookupValue_cons_succ, ih (by omega) h]
        rfl

/-- Missed lookup stays missed below the insertion, given `c ≤ Γ.length`
so the slot exists (it is an assumption; `d` sits at `c`). -/
theorem lookupValue_insertAt_lt_none (d : LocalDecl) {c i : Nat} {Γ : LCtx}
    (hlen : c ≤ Γ.length) (hic : i < c) (h : lookupValue Γ i = none) :
    lookupValue (insertAt d c Γ) i = none := by
  induction c generalizing i Γ with
  | zero => exfalso; omega
  | succ c ih =>
    match Γ with
    | [] =>
        simp only [List.length_nil] at hlen
        exfalso
        omega
    | x :: Γ' =>
      match i with
      | 0 =>
        match x with
        | .assumption _ =>
            simp only [insertAt_succ_cons, lookupValue, List.get?_cons_zero,
              liftDecl]
        | .letBinding _ _ =>
            nomatch h
      | i' + 1 =>
        rw [lookupValue_cons_succ] at h
        simp only [Option.map_eq_none'] at h
        have hlen' : c ≤ Γ'.length := by
          simp only [List.length_cons] at hlen; omega
        rw [insertAt_succ_cons, lookupValue_cons_succ,
          ih hlen' (by omega) h]
        rfl

/-- Weakening of complete development (`c ≤ Γ.length`). -/
theorem devel_lift {E : ResolvedEnv} {n : Nat} (hE : EnvWf E n)
    (d : LocalDecl) (Γ : LCtx) (c : Nat) (hlen : c ≤ Γ.length) :
    (e : Expr Nat) →
    devel E n (insertAt d c Γ) (lift c 1 e) = lift c 1 (devel E n Γ e)
  | .sort _ => rfl
  | .lit t => by
      simp only [lift, devel]
      exact (natExpand_lift c 1 t).symm
  | .const r ls => by
      simp only [lift, devel]
      cases hmem : E.members r with
      | none => rfl
      | some m =>
          cases htr : transparent m.mclass with
          | true =>
              cases hb : m.body with
              | none => simp [hmem, htr, hb]; rfl
              | some b =>
                  simp [hmem, htr, hb]
                  exact ((envWf_closed_inst hE r m hmem).2 b hb ls c).symm
          | false => simp [hmem, htr]; rfl
  | .bvar i => by
      by_cases hi : c ≤ i
      · rw [lift, if_pos hi]
        cases hlk : lookupValue Γ i with
        | none =>
            have hnone := lookupValue_insertAt_ge_none d hi hlk
            simp only [devel, hlk, hnone, lift, if_pos hi]
        | some v =>
            have hge := lookupValue_insertAt_ge d hi hlk
            simp only [devel, hlk, hge]
      · have hic : i < c := Nat.lt_of_not_ge hi
        rw [lift, if_neg hi]
        cases hlk : lookupValue Γ i with
        | none =>
            have hnone := lookupValue_insertAt_lt_none d hlen hic hlk
            simp only [devel, hlk, hnone, lift, if_neg hi]
        | some v =>
            have hlt := lookupValue_insertAt_lt d hic hlk
            simp only [devel, hlk, hlt]
  | .app f a => by
      simp only [lift, devel]
      have hmap := iotaReduct_lift (E := E) c (.app f a)
      simp only [lift] at hmap
      cases hred : iotaReduct E (.app f a) with
      | some rhs =>
          simp only [hred, Option.map] at hmap
          simp only [hmap, hred]
      | none =>
          simp only [hred, Option.map] at hmap
          simp only [hmap, hred]
          rw [devel_lift hE d Γ c hlen f, devel_lift hE d Γ c hlen a]
          cases devel E n Γ f with
          | lam A b =>
              simp only [lift, instantiate0]
              exact (lift_instantiate_low 1 c 0 (devel E n Γ a) (Nat.zero_le c) b).symm
          | sort _ => simp only [lift]
          | const _ _ => simp only [lift]
          | bvar i =>
              simp only [lift]
              by_cases h : c ≤ i <;> simp [h]
          | app _ _ => simp only [lift]
          | pi _ _ => simp only [lift]
          | letE _ _ _ => simp only [lift]
          | lit _ => simp only [lift]
  | .lam A b => by
      simp only [lift, devel]
      rw [devel_lift hE d Γ c hlen A]
      have hlen' : c + 1 ≤ (LocalDecl.assumption A :: Γ).length := by
        simp only [List.length_cons]; omega
      have hb := devel_lift hE d (LocalDecl.assumption A :: Γ) (c + 1) hlen' b
      rw [insertAt_succ_cons] at hb
      exact congrArg (Expr.lam (lift c 1 (devel E n Γ A))) hb
  | .pi A B => by
      simp only [lift, devel]
      rw [devel_lift hE d Γ c hlen A]
      have hlen' : c + 1 ≤ (LocalDecl.assumption A :: Γ).length := by
        simp only [List.length_cons]; omega
      have hB := devel_lift hE d (LocalDecl.assumption A :: Γ) (c + 1) hlen' B
      rw [insertAt_succ_cons] at hB
      exact congrArg (Expr.pi (lift c 1 (devel E n Γ A))) hB
  | .letE A v b => by
      simp only [lift, devel]
      rw [devel_lift hE d Γ c hlen v]
      have hlen' : c + 1 ≤ (LocalDecl.letBinding A v :: Γ).length := by
        simp only [List.length_cons]; omega
      have hb := devel_lift hE d (LocalDecl.letBinding A v :: Γ) (c + 1) hlen' b
      rw [insertAt_succ_cons] at hb
      simp only [liftDecl] at hb
      simp only [instantiate0]
      rw [hb]
      exact (lift_instantiate_low 1 c 0 (devel E n Γ v) (Nat.zero_le c)
        (devel E n (LocalDecl.letBinding A v :: Γ) b)).symm

/-- The dummy assumption occupies index `j`; it has no value. -/
theorem lookupValue_insertAt_dummy (Γ : LCtx) (j : Nat)
    (hlen : j ≤ Γ.length) :
    lookupValue (insertAt dummyAssump j Γ) j = none := by
  induction j generalizing Γ with
  | zero =>
      simp only [insertAt_zero, dummyAssump, lookupValue, List.get?_cons_zero]
  | succ j ih =>
    match Γ with
    | [] =>
        simp only [List.length_nil] at hlen
        exfalso
        omega
    | x :: Γ' =>
        have hlen' : j ≤ Γ'.length := by
          simp only [List.length_cons] at hlen; omega
        rw [insertAt_succ_cons, lookupValue_cons_succ, ih Γ' hlen']
        rfl

/-- M-001: `devel (instantiate j r e) = instantiate j (devel r) (devel dummy e)`
is FALSE. Instantiating a `bvar j` function can create a beta redex
(`r` a lam) that the dummy-assumption development never sees.
SortConvChar only needs: an instantiation that *is* a sort came from a
sort or from `bvar j` replaced by a sort. -/
theorem instantiate_eq_sort {j : Nat} {r e : Expr Nat} {u : Level} :
    instantiate j r e = .sort u →
    (e = .sort u) ∨ (e = .bvar j ∧ r = .sort u) := by
  cases e with
  | sort l =>
      intro h
      simp only [instantiate] at h
      exact .inl h
  | bvar i =>
      intro h
      simp only [instantiate] at h
      by_cases hij : i = j
      · subst hij
        simp only [if_pos rfl] at h
        exact .inr ⟨rfl, h⟩
      · simp only [if_neg hij] at h
        split at h <;> exact nomatch h
  | const _ _ => intro h; exact nomatch h
  | app _ _ => intro h; exact nomatch h
  | lam _ _ => intro h; exact nomatch h
  | pi _ _ => intro h; exact nomatch h
  | letE _ _ _ => intro h; exact nomatch h
  | lit _ => intro h; exact nomatch h

/-- devel of a beta redex whose reduct is a sort is that sort. -/
theorem devel_beta_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg : Expr Nat} {u : Level}
    (h : instantiate0 arg body = .sort u) :
    devel E n Γ (.app (.lam A body) arg) = .sort u := by
  have hι := iotaReduct_lam_app E A body arg
  simp only [devel, hι, instantiate0] at h ⊢
  match instantiate_eq_sort h with
  | .inl hb =>
      subst hb
      simp only [devel, instantiate0, instantiate]
  | .inr ⟨hb, hr⟩ =>
      subst hb
      subst hr
      simp [devel, instantiate0, instantiate, lookupValue,
        List.get?_cons_zero]

/-- devel of a zeta redex whose reduct is a sort is that sort. -/
theorem devel_zeta_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A v body : Expr Nat} {u : Level}
    (h : instantiate0 v body = .sort u) :
    devel E n Γ (.letE A v body) = .sort u := by
  simp only [devel, instantiate0] at h ⊢
  match instantiate_eq_sort h with
  | .inl hb =>
      subst hb
      simp only [devel, instantiate0, instantiate]
  | .inr ⟨hb, hr⟩ =>
      subst hb
      subst hr
      simp [devel, instantiate0, instantiate, lookupValue, List.get?_cons_zero]

/-- One-shot delta to a sort.

M-003 (00 §20.6 RULE CHANGES). The conclusion moved
    old:  devel E n Γ (.const r ls) = .sort u
    new:  devel E n Γ (.const r ls) = .sort (instLevel ls u)
in lockstep with `devel`'s `.const` arm, which now yields the
level-instantiated body. The old form is the `ls = []` instance
(`instLevel_nil`) — the only one reachable under `EnvWf`
(`envWf_body_arity_zero`); as a statement about an arbitrary
`ResolvedEnv` with a stored body `.sort (param 0)` it is now false.
Correction, not weakening. -/
theorem devel_delta_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    {u : Level}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htr : transparent m.mclass = true) (hb : b = .sort u) :
    devel E n Γ (.const r ls) = .sort (instLevel ls u) := by
  simp [devel, hres, htr, hbody, hb, instantiateLevels]

/-- One-shot zetaLocal to a sort. -/
theorem devel_zetaLocal_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {i : Nat} {v : Expr Nat} {u : Level}
    (h : lookupValue Γ i = some v) (hv : v = .sort u) :
    devel E n Γ (.bvar i) = .sort u := by
  simp only [devel, h, hv]

theorem appsSpine_iotaLhs {E : ResolvedEnv} (w : IotaWitness E) :
    appsSpine (iotaLhsOf w) =
      (.const w.recRef w.ls, w.preMajor ++ [ctorMajor w]) := by
  unfold iotaLhsOf recCall
  rw [appsSpine_foldApps, appsSpine_const, List.nil_append]

theorem appsSpine_ctorMajor {E : ResolvedEnv} (w : IotaWitness E) :
    appsSpine (ctorMajor w) =
      (.const w.ctorRef w.lsC, w.ctorParams ++ w.fields) := by
  unfold ctorMajor ctorSpine
  rw [appsSpine_foldApps, appsSpine_const, List.nil_append]

theorem iotaLhs_eq_lift_preMajor {E : ResolvedEnv} {c : Nat} {e : Expr Nat}
    (w : IotaWitness E) (hlhs : iotaLhsOf w = lift c 1 e) :
    w.preMajor ++ [ctorMajor w] = (appsSpine e).2.map (lift c 1) := by
  have h1 := appsSpine_iotaLhs w
  have h2 : appsSpine (iotaLhsOf w) = appsSpine (lift c 1 e) :=
    congrArg appsSpine hlhs
  have h3 := appsSpine_lift c 1 e
  exact congrArg Prod.snd (h1.symm.trans (h2.trans h3))

theorem reverse_snoc {α} (xs : List α) (z : α) :
    (xs ++ [z]).reverse = z :: xs.reverse := by
  rw [List.reverse_append, List.reverse_cons, List.reverse_nil]
  rfl

theorem ctorMajor_eq_of_lhs {E : ResolvedEnv} {w1 w2 : IotaWitness E}
    (h : iotaLhsOf w1 = iotaLhsOf w2) :
    ctorMajor w1 = ctorMajor w2 := by
  have s1 := appsSpine_iotaLhs w1
  have s2 := appsSpine_iotaLhs w2
  rw [h] at s1
  have hs := s1.symm.trans s2
  injection hs with _ hargs
  have hr :=
    congrArg (fun l : List (Expr Nat) => l.reverse.head?) hargs
  simp only [reverse_snoc, List.head?] at hr
  exact Option.some.inj hr

/-- One-shot iota: `iotaReduct` recovers `iotaRhsOf` from `iotaLhsOf`. -/
theorem iotaReduct_of {E : ResolvedEnv} (w : IotaWitness E) :
    iotaReduct E (iotaLhsOf w) = some (iotaRhsOf w) := by
  have hsp := appsSpine_iotaLhs w
  simp only [iotaReduct, hsp]
  rw [w.hrec]
  simp only [Option.some_bind]
  rw [w.hrecK]
  simp only
  rw [reverse_snoc]
  simp only
  rw [List.reverse_reverse]
  have hmaj := appsSpine_ctorMajor w
  rw [hmaj]
  simp only [↓reduceIte]
  rw [w.hctor]
  simp only [Option.some_bind]
  rw [w.hctorK]
  simp only
  unfold iotaReductGo
  rw [if_pos w.hrecClosed]
  rw [if_pos w.hctorClosed]
  have hpcRec : piCount w.recMember.mtype =
      w.nparams + 1 + w.nMinors + w.nindices + 1 := w.hnmin.symm
  rw [hpcRec, w.hpeelRec]
  simp only [Option.some_bind, Prod.fst, Prod.snd]
  have hlenD : w.recDoms.length = w.nparams + 1 + w.nMinors + w.nindices + 1 :=
    peelPis_length _ _ w.hpeelRec
  have hlast := listLast_eq_getElem w.recDoms
      (w.nparams + 1 + w.nMinors + w.nindices) (by
        have := hlenD
        omega)
  rw [hlast, w.hmajorTy]
  simp only [Option.some_bind]
  have hspLast := appsSpine_foldApps
      (.const w.familyRef ((List.range w.famMember.arity).map Level.param))
      ((List.range w.nparams).reverse.map
        (fun i => Expr.bvar (i + w.nindices + w.nMinors + 1)) ++
        (List.range w.nindices).reverse.map (fun i => Expr.bvar i))
  simp only [appsSpine_const, List.nil_append] at hspLast
  rw [hspLast]
  simp only
  rw [w.hfam]
  simp only [Option.some_bind]
  rw [w.hfamK]
  simp only
  have hfr : w.familyRef < w.recRef := by
    have := w.hrecIdx
    omega
  have hfc : w.familyRef < w.ctorRef := by
    have := w.hctorIdx
    omega
  have hcr : w.ctorRef < w.recRef := by
    have := w.hctorIdx
    have := w.hrecIdx
    have := w.hidx
    omega
  rw [if_pos hfr, if_pos hfc, if_pos hcr]
  have hnMin : w.recRef - w.familyRef - 1 = w.nMinors := by
    have := w.hrecIdx
    omega
  have hnIdx : w.ctorRef - w.familyRef - 1 = w.ctorIdx := by
    have := w.hctorIdx
    omega
  simp only [hnMin, hnIdx]
  have hspB := appsSpine_foldApps
      (.bvar (w.nMinors + w.nindices + 1) : Expr Nat)
      ((List.range w.nindices).reverse.map (fun i => Expr.bvar (i + 1)) ++
        [Expr.bvar 0])
  simp only [appsSpine_bvar, List.nil_append] at hspB
  rw [w.hrecBody, hspB]
  cases hba : ((List.range w.nindices).reverse.map
      (fun i => (Expr.bvar (i + 1) : Expr Nat)) ++
      [Expr.bvar 0]) with
  | nil => nomatch (List.append_eq_nil.mp hba).2
  | cons _hd rest =>
    have hlenB : rest.length = w.nindices := by
      have hlen : ((List.range w.nindices).reverse.map
          (fun i => (Expr.bvar (i + 1) : Expr Nat)) ++
          [Expr.bvar 0]).length = w.nindices + 1 := by
        simp only [List.length_append, List.length_map, List.length_reverse,
          List.length_range, List.length_cons, List.length_nil]
      rw [hba] at hlen
      simp only [List.length_cons] at hlen
      omega
    simp only [hlenB]
    have hle : w.nindices ≤ piCount w.famMember.mtype := by
      have := w.hnidx
      omega
    rw [if_pos hle]
    have hnpar : piCount w.famMember.mtype - w.nindices = w.nparams := by
      have := w.hnidx
      omega
    simp only [hnpar]
    have hpreL : w.preMajor.length =
        w.nparams + 1 + w.nMinors + w.nindices := w.hpre
    rw [if_pos hpreL]
    have hfull' : w.preMajor.length + 1 =
        w.nparams + 1 + w.nMinors + w.nindices + 1 := by
      rw [hpreL]
    rw [if_pos hfull']
    have htkLen : (w.ctorParams).length = w.nparams := w.hctorParams
    have hctorL : (w.ctorParams ++ w.fields).length =
        piCount w.ctorMember.mtype := by
      simp only [List.length_append, htkLen]
      exact w.hnpar
    rw [if_pos hctorL]
    unfold iotaReductTail
    have hpcCtor : piCount w.ctorMember.mtype =
        w.nparams + w.fields.length := w.hnpar.symm
    rw [hpcCtor, w.hpeel]
    simp only [Option.some_bind, Prod.fst]
    rw [w.hkinds]
    simp only [Option.some_bind]
    rw [w.hctorAfter]
    simp only [Option.some_bind]
    rw [w.hminor]
    simp only [Option.some_bind]
    rw [List.drop_left' htkLen]
    rfl

theorem iotaReductCert_some_reduct {E : ResolvedEnv} {e : Expr Nat}
    {w : IotaWitness E} {hlhs : iotaLhsOf w = e}
    (h : iotaReductCert E e = some ⟨w, hlhs⟩) :
    iotaReduct E e = some (iotaRhsOf w) := by
  rw [← hlhs, iotaReduct_of]

/-- Cert is stricter than reduct, so a failed reduct kills cert. -/
theorem iotaReductCert_eq_none_of_reduct_none {E : ResolvedEnv}
    {e : Expr Nat} (h : iotaReduct E e = none) :
    iotaReductCert E e = none := by
  match hc : iotaReductCert E e with
  | none => rfl
  | some wσ =>
      match wσ with
      | ⟨w, hlhs⟩ =>
          have hred := iotaReductCert_some_reduct hc
          rw [h] at hred
          nomatch hred

theorem listIndexOf_isSome_of_getElem {α} [DecidableEq α] (y : α) :
    (xs : List α) → (i : Nat) → xs[i]? = some y →
    (listIndexOf y xs).isSome = true
  | [], i, h => by
      simp only [List.getElem?_nil] at h
      nomatch h
  | x :: xs, Nat.zero, h => by
      simp only [List.getElem?_cons_zero] at h
      injection h with hxy
      subst hxy
      simp only [listIndexOf]
      rfl
  | x :: xs, Nat.succ i, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [listIndexOf]
      split
      · rfl
      · have ih := listIndexOf_isSome_of_getElem y xs i h
        cases hio : listIndexOf y xs with
        | none =>
            simp only [hio, Option.isSome] at ih
            nomatch ih
        | some _ =>
            simp only [hio, Option.map, Option.isSome]

theorem idxPosZip_mapIndexOf_isSome (xs : List (Expr Nat))
    (ys : List (Expr Nat)) (is : List Nat)
    (h : idxPosZip xs ys is = true) :
    (mapIndexOf xs ys).isSome = true := by
  match ys, is with
  | [], [] => rfl
  | [], _ :: _ => simp only [idxPosZip] at h; nomatch h
  | _ :: _, [] => simp only [idxPosZip] at h; nomatch h
  | y :: ys, i :: is =>
      simp only [idxPosZip] at h
      have ⟨hget, hrest⟩ := bool_and_true h
      have hy : xs[i]? = some y := of_decide_eq_true hget
      have h1 := listIndexOf_isSome_of_getElem y xs i hy
      have h2 := idxPosZip_mapIndexOf_isSome xs ys is hrest
      simp only [mapIndexOf]
      cases hl : listIndexOf y xs with
      | none =>
          simp only [hl, Option.isSome] at h1
          nomatch h1
      | some _ =>
          cases hm : mapIndexOf xs ys with
          | none =>
              simp only [hm, Option.isSome] at h2
              nomatch h2
          | some _ => rfl

theorem recIdxPosWalk_build_isSome (nparams : Nat) (pf : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
    (pss : List (List Nat))
    (h : recIdxPosWalk nparams pf ks T fs pss = true) :
    (recIdxPosBuild nparams pf ks T fs).isSome = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          cases pss with
          | nil => simp only [recIdxPosBuild, Option.isSome]
          | cons _ _ => simp only [recIdxPosWalk] at h; nomatch h
      | cons _ _ => simp only [recIdxPosWalk] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxPosWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxPosWalk] at h; nomatch h
                  | cons pos pss =>
                      cases pos with
                      | nil =>
                          simp only [recIdxPosWalk] at h
                          have ih' := ih (instantiate0 f B) fs pss h
                          simp only [recIdxPosBuild]
                          cases hb : recIdxPosBuild nparams pf ks
                              (instantiate0 f B) fs with
                          | none =>
                              simp only [hb, Option.isSome] at ih'
                              nomatch ih'
                          | some _ =>
                              simp only [Option.map, Option.isSome]
                      | cons _ _ =>
                          simp only [recIdxPosWalk] at h; nomatch h
          | bvar _ => simp only [recIdxPosWalk] at h; nomatch h
          | sort _ => simp only [recIdxPosWalk] at h; nomatch h
          | const _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | app _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lam _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | letE _ _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lit _ => simp only [recIdxPosWalk] at h; nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxPosWalk] at h; nomatch h
              | cons f fs =>
                  cases pss with
                  | nil => simp only [recIdxPosWalk] at h; nomatch h
                  | cons pos pss =>
                      have ⟨hzip, hrest⟩ := recIdxPosWalk_directRec h
                      have ih' := ih (instantiate0 f B) fs pss hrest
                      have hmap := idxPosZip_mapIndexOf_isSome pf
                          (familyIdx nparams A) pos hzip
                      simp only [recIdxPosBuild]
                      cases h1 : mapIndexOf pf (familyIdx nparams A) with
                      | none =>
                          simp only [h1, Option.isSome] at hmap
                          nomatch hmap
                      | some _ =>
                          cases h2 : recIdxPosBuild nparams pf ks
                              (instantiate0 f B) fs with
                          | none =>
                              simp only [h2, Option.isSome] at ih'
                              nomatch ih'
                          | some _ => rfl
          | bvar _ => simp only [recIdxPosWalk] at h; nomatch h
          | sort _ => simp only [recIdxPosWalk] at h; nomatch h
          | const _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | app _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lam _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | letE _ _ _ => simp only [recIdxPosWalk] at h; nomatch h
          | lit _ => simp only [recIdxPosWalk] at h; nomatch h

theorem listIndexOf_getElem {α} [DecidableEq α] (y : α) :
    (xs : List α) → (i : Nat) → listIndexOf y xs = some i →
    xs[i]? = some y
  | [], i, h => by simp only [listIndexOf] at h; nomatch h
  | x :: xs, i, h => by
      simp only [listIndexOf] at h
      split at h
      · next hxy =>
          injection h with hi
          subst hi
          subst hxy
          simp only [List.getElem?_cons_zero]
      · next _hne =>
          cases hio : listIndexOf y xs with
          | none =>
              simp only [hio, Option.map] at h
              nomatch h
          | some j =>
              simp only [hio, Option.map] at h
              injection h with hi
              subst hi
              simp only [List.getElem?_cons_succ]
              exact listIndexOf_getElem y xs j hio

theorem mapIndexOf_idxPosZip (xs : List (Expr Nat))
    (ys : List (Expr Nat)) (is : List Nat)
    (h : mapIndexOf xs ys = some is) :
    idxPosZip xs ys is = true := by
  induction ys generalizing is with
  | nil =>
      cases is with
      | nil => rfl
      | cons _ _ => simp only [mapIndexOf] at h; nomatch h
  | cons y ys ih =>
      cases is with
      | nil =>
          simp only [mapIndexOf] at h
          cases h1 : listIndexOf y xs with
          | none => simp only [h1] at h; nomatch h
          | some _i =>
              cases h2 : mapIndexOf xs ys with
              | none => simp only [h1, h2] at h; nomatch h
              | some _is' => simp only [h1, h2] at h; nomatch h
      | cons i is =>
          simp only [mapIndexOf] at h
          cases h1 : listIndexOf y xs with
          | none =>
              simp only [h1] at h
              nomatch h
          | some i' =>
              cases h2 : mapIndexOf xs ys with
              | none =>
                  simp only [h1, h2] at h
                  nomatch h
              | some is' =>
                  simp only [h1, h2] at h
                  have hcons := Option.some.inj h
                  have ⟨hi, his⟩ := List.cons.inj hcons
                  subst hi
                  subst his
                  simp only [idxPosZip]
                  have hget := listIndexOf_getElem y xs i' h1
                  have hdec : decide (xs[i']? = some y) = true := by
                    simp only [hget]
                    rfl
                  simp only [hdec, Bool.true_and]
                  exact ih is' h2

theorem recIdxPosBuild_walk (nparams : Nat) (pf : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat))
    (pss : List (List Nat))
    (h : recIdxPosBuild nparams pf ks T fs = some pss) :
    recIdxPosWalk nparams pf ks T fs pss = true := by
  induction ks generalizing T fs pss with
  | nil =>
      cases fs with
      | nil =>
          simp only [recIdxPosBuild] at h
          injection h with hs
          subst hs
          rfl
      | cons _ _ => simp only [recIdxPosBuild] at h; nomatch h
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxPosBuild] at h; nomatch h
              | cons f fs =>
                  simp only [recIdxPosBuild] at h
                  cases hb : recIdxPosBuild nparams pf ks
                      (instantiate0 f B) fs with
                  | none =>
                      simp only [hb, Option.map] at h
                      nomatch h
                  | some pss' =>
                      simp only [hb, Option.map] at h
                      injection h with hs
                      subst hs
                      simp only [recIdxPosWalk]
                      exact ih (instantiate0 f B) fs pss' hb
          | bvar _ => simp only [recIdxPosBuild] at h; nomatch h
          | sort _ => simp only [recIdxPosBuild] at h; nomatch h
          | const _ _ => simp only [recIdxPosBuild] at h; nomatch h
          | app _ _ => simp only [recIdxPosBuild] at h; nomatch h
          | lam _ _ => simp only [recIdxPosBuild] at h; nomatch h
          | letE _ _ _ => simp only [recIdxPosBuild] at h; nomatch h
          | lit _ => simp only [recIdxPosBuild] at h; nomatch h
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxPosBuild] at h; nomatch h
              | cons f fs =>
                  simp only [recIdxPosBuild] at h
                  cases h1 : mapIndexOf pf (familyIdx nparams A) with
                  | none =>
                      simp only [h1] at h
                      nomatch h
                  | some pos =>
                      cases h2 : recIdxPosBuild nparams pf ks
                          (instantiate0 f B) fs with
                      | none =>
                          simp only [h1, h2] at h
                          nomatch h
                      | some pss' =>
                          simp only [h1, h2] at h
                          injection h with hs
                          subst hs
                          simp only [recIdxPosWalk]
                          have hzip := mapIndexOf_idxPosZip pf
                              (familyIdx nparams A) pos h1
                          have hrest := ih (instantiate0 f B) fs pss' h2
                          simp only [hzip, hrest, Bool.true_and]
          | bvar _ => simp only [recIdxPosBuild] at h; nomatch h
          | sort _ => simp only [recIdxPosBuild] at h; nomatch h
          | const _ _ => simp only [recIdxPosBuild] at h; nomatch h
          | app _ _ => simp only [recIdxPosBuild] at h; nomatch h
          | lam _ _ => simp only [recIdxPosBuild] at h; nomatch h
          | letE _ _ _ => simp only [recIdxPosBuild] at h; nomatch h
          | lit _ => simp only [recIdxPosBuild] at h; nomatch h

theorem mapIndexOf_lift (c : Nat) (xs : List (Expr Nat)) :
    (ys : List (Expr Nat)) →
    mapIndexOf (xs.map (lift c 1)) (ys.map (lift c 1)) = mapIndexOf xs ys
  | [] => rfl
  | y :: ys => by
      simp only [mapIndexOf, List.map_cons]
      rw [listIndexOf_lift, mapIndexOf_lift c xs ys]

theorem recIdxPosBuild_lift (c nparams : Nat) (pf : List (Expr Nat))
    (ks : List RecKind) (T : Expr Nat) (fs : List (Expr Nat)) :
    recIdxPosBuild nparams (pf.map (lift c 1)) ks (lift c 1 T)
      (fs.map (lift c 1)) =
      recIdxPosBuild nparams pf ks T fs := by
  induction ks generalizing T fs with
  | nil =>
      cases fs with
      | nil => simp only [recIdxPosBuild, List.map_nil]
      | cons _ _ => simp only [recIdxPosBuild, List.map_cons]
  | cons k ks ih =>
      cases k with
      | plain =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxPosBuild, List.map_cons, lift]
              | cons f fs =>
                  simp only [recIdxPosBuild, List.map_cons, lift]
                  rw [instantiate0_lift, ih]
          | bvar _ => simp only [recIdxPosBuild, List.map_cons, lift]; split <;> rfl
          | sort _ => simp only [recIdxPosBuild, List.map_cons, lift]
          | const _ _ => simp only [recIdxPosBuild, List.map_cons, lift]
          | app _ _ => simp only [recIdxPosBuild, List.map_cons, lift]
          | lam _ _ => simp only [recIdxPosBuild, List.map_cons, lift]
          | letE _ _ _ => simp only [recIdxPosBuild, List.map_cons, lift]
          | lit _ => simp only [recIdxPosBuild, List.map_cons, lift]
      | directRec =>
          cases T with
          | pi A B =>
              cases fs with
              | nil => simp only [recIdxPosBuild, List.map_cons, lift]
              | cons f fs =>
                  simp only [recIdxPosBuild, List.map_cons, lift]
                  rw [familyIdx_lift, mapIndexOf_lift, instantiate0_lift, ih]
          | bvar _ => simp only [recIdxPosBuild, List.map_cons, lift]; split <;> rfl
          | sort _ => simp only [recIdxPosBuild, List.map_cons, lift]
          | const _ _ => simp only [recIdxPosBuild, List.map_cons, lift]
          | app _ _ => simp only [recIdxPosBuild, List.map_cons, lift]
          | lam _ _ => simp only [recIdxPosBuild, List.map_cons, lift]
          | letE _ _ _ => simp only [recIdxPosBuild, List.map_cons, lift]
          | lit _ => simp only [recIdxPosBuild, List.map_cons, lift]

-- Deleted: `hcanon_liftWitness` packed idxPositions (moved to IotaTyping / EnvWf).
/-- Completeness for canonical positions: Fill reconstructs
`idxPositions` via `recIdxPosBuild` (first-occurrence). Stored
positions that are not that canonical choice are a representation
gap (`listIndexOf` vs `idxPosZip`); do not inhabit the unconditioned
`iotaReductCert_of`. Spine via `eq_spine`; named matches via `split`
/`dif_pos`. -/
theorem iotaReductCert_of {E : ResolvedEnv} (w : IotaWitness E) :
    (iotaReductCert E (iotaLhsOf w)).isSome = true := by
  have hsp := appsSpine_iotaLhs w
  rw [iotaReductCert_eq_spine E (iotaLhsOf w) _ hsp]
  unfold iotaReductCertFromSpine
  dsimp only
  -- split members; none is `w.hrec`.
  split
  · next hnone => exact nomatch (hnone.symm.trans w.hrec)
  · next recMember hmem =>
      have : recMember = w.recMember :=
        Option.some.inj (hmem.symm.trans w.hrec)
      subst this
      rw [dif_pos w.hrecK]
      have hrev := reverse_snoc w.preMajor (ctorMajor w)
      -- named match on reverse: split, not rw.
      split
      · next hempty =>
          exact nomatch (hrev.symm.trans hempty)
      · next major preRev hcons =>
          have ⟨h1, h2⟩ := List.cons.inj (hcons.symm.trans hrev)
          subst h1
          subst h2
          have hmaj := appsSpine_ctorMajor w
          have hmaj1 : (appsSpine (ctorMajor w)).1 =
              .const w.ctorRef w.lsC := congrArg Prod.fst hmaj
          split
          · next h => exact nomatch (h.symm.trans hmaj1)
          · next h => exact nomatch (h.symm.trans hmaj1)
          · next h => exact nomatch (h.symm.trans hmaj1)
          · next h => exact nomatch (h.symm.trans hmaj1)
          · next h => exact nomatch (h.symm.trans hmaj1)
          · next h => exact nomatch (h.symm.trans hmaj1)
          · next h => exact nomatch (h.symm.trans hmaj1)
          · next ctorRef cls hconst =>
              have hce := hconst.symm.trans hmaj1
              injection hce with hr hls
              subst hr
              subst hls
              unfold iotaReductCertFromCtor
              dsimp only
              split
              · next hcn => exact nomatch (hcn.symm.trans w.hctor)
              · next ctorMember hcmem =>
                  have : ctorMember = w.ctorMember :=
                    Option.some.inj (hcmem.symm.trans w.hctor)
                  subst this
                  rw [dif_pos w.hctorK]
                  rw [dif_pos w.hrecClosed]
                  rw [dif_pos w.hctorClosed]
                  have hpeelEq :
                      peelPis (piCount w.recMember.mtype) w.recMember.mtype =
                        some (w.recDoms, w.recBody) := by
                    rw [w.hnmin.symm]; exact w.hpeelRec
                  split
                  · next hnone =>
                      exact nomatch (hnone.symm.trans hpeelEq)
                  · next recPr hpeel =>
                      have : recPr = (w.recDoms, w.recBody) :=
                        Option.some.inj (hpeel.symm.trans hpeelEq)
                      subst this
                      have hlenD : w.recDoms.length =
                          w.nparams + 1 + w.nMinors + w.nindices + 1 :=
                        peelPis_length _ _ w.hpeelRec
                      have hlastEq : listLast w.recDoms =
                          w.recDoms[w.nparams + 1 + w.nMinors +
                            w.nindices]? :=
                        listLast_eq_getElem w.recDoms
                          (w.nparams + 1 + w.nMinors + w.nindices) (by
                            have := hlenD; omega)
                      split
                      · next hnone =>
                          exact nomatch
                            (hnone.symm.trans (hlastEq.trans w.hmajorTy))
                      · next lastDom hlast =>
                          have : lastDom =
                              foldApps (.const w.familyRef
                                  ((List.range w.famMember.arity).map Level.param))
                                ((List.range w.nparams).reverse.map
                                  (fun i => Expr.bvar
                                    (i + w.nindices + w.nMinors + 1)) ++
                                (List.range w.nindices).reverse.map
                                  (fun i => Expr.bvar i)) :=
                            Option.some.inj
                              (hlast.symm.trans (hlastEq.trans w.hmajorTy))
                          subst this
                          have hspLast :
                              appsSpine (foldApps (.const w.familyRef
                                  ((List.range w.famMember.arity).map Level.param))
                                ((List.range w.nparams).reverse.map
                                  (fun i => Expr.bvar
                                    (i + w.nindices + w.nMinors + 1)) ++
                                (List.range w.nindices).reverse.map
                                  (fun i => Expr.bvar i))) =
                                (.const w.familyRef
                                    ((List.range w.famMember.arity).map Level.param),
                                  ((List.range w.nparams).reverse.map
                                    (fun i => Expr.bvar
                                      (i + w.nindices + w.nMinors + 1)) ++
                                  (List.range w.nindices).reverse.map
                                    (fun i => Expr.bvar i))) := by
                            rw [appsSpine_foldApps, appsSpine_const,
                              List.nil_append]
                          have hfam1 :
                              (appsSpine (foldApps (.const w.familyRef
                                  ((List.range w.famMember.arity).map Level.param))
                                ((List.range w.nparams).reverse.map
                                  (fun i => Expr.bvar
                                    (i + w.nindices + w.nMinors + 1)) ++
                                (List.range w.nindices).reverse.map
                                  (fun i => Expr.bvar i)))).1 =
                                .const w.familyRef
                                  ((List.range w.famMember.arity).map Level.param) :=
                            congrArg Prod.fst hspLast
                          split
                          · next h => exact nomatch (h.symm.trans hfam1)
                          · next h => exact nomatch (h.symm.trans hfam1)
                          · next h => exact nomatch (h.symm.trans hfam1)
                          · next h => exact nomatch (h.symm.trans hfam1)
                          · next h => exact nomatch (h.symm.trans hfam1)
                          · next h => exact nomatch (h.symm.trans hfam1)
                          · next h => exact nomatch (h.symm.trans hfam1)
                          · next familyRef fls hconst =>
                              have hce := hconst.symm.trans hfam1
                              injection hce with hr _hls
                              subst hr
                              split
                              · next hfn =>
                                  exact nomatch (hfn.symm.trans w.hfam)
                              · next famMember hfmem =>
                                  have : famMember = w.famMember :=
                                    Option.some.inj
                                      (hfmem.symm.trans w.hfam)
                                  subst this
                                  rw [dif_pos w.hfamK]
                                  have hfr : w.familyRef < w.recRef := by
                                    have := w.hrecIdx; omega
                                  have hfc : w.familyRef < w.ctorRef := by
                                    have := w.hctorIdx; omega
                                  have hcr : w.ctorRef < w.recRef := by
                                    have := w.hctorIdx
                                    have := w.hrecIdx
                                    have := w.hidx
                                    omega
                                  rw [dif_pos hfr, dif_pos hfc, dif_pos hcr]
                                  have hspB :
                                      appsSpine (foldApps
                                        (.bvar (w.nMinors + w.nindices + 1)
                                          : Expr Nat)
                                        ((List.range w.nindices).reverse.map
                                          (fun i => Expr.bvar (i + 1)) ++
                                          [Expr.bvar 0])) =
                                        (.bvar (w.nMinors + w.nindices + 1),
                                          ((List.range w.nindices).reverse.map
                                            (fun i => Expr.bvar (i + 1)) ++
                                            [Expr.bvar 0])) := by
                                    rw [appsSpine_foldApps, appsSpine_bvar,
                                      List.nil_append]
                                  have hrestEq :
                                      (appsSpine w.recBody).2 =
                                        ((List.range w.nindices).reverse.map
                                          (fun i => Expr.bvar (i + 1)) ++
                                          [Expr.bvar 0]) := by
                                    rw [w.hrecBody]
                                    exact congrArg Prod.snd hspB
                                  split
                                  · next hnil =>
                                      exact nomatch
                                        (List.append_eq_nil.mp
                                          (hrestEq.symm.trans hnil)).2
                                  · next _hd rest hba =>
                                      have hcons := hrestEq.symm.trans hba
                                      have hlenB : rest.length =
                                          w.nindices := by
                                        have hlen :
                                            ((List.range w.nindices).reverse.map
                                              (fun i => (Expr.bvar (i + 1)
                                                : Expr Nat)) ++
                                            [Expr.bvar 0]).length =
                                              w.nindices + 1 := by
                                          simp only [List.length_append,
                                            List.length_map,
                                            List.length_reverse,
                                            List.length_range,
                                            List.length_cons, List.length_nil]
                                        rw [hcons] at hlen
                                        simp only [List.length_cons] at hlen
                                        omega
                                      have hle : rest.length ≤
                                          piCount w.famMember.mtype := by
                                        rw [hlenB]
                                        have := w.hnidx; omega
                                      rw [dif_pos hle]
                                      have hnparamsEq :
                                          piCount w.famMember.mtype -
                                            rest.length = w.nparams := by
                                        rw [hlenB]
                                        have := w.hnidx; omega
                                      have hnMinorsEq :
                                          w.recRef - w.familyRef - 1 =
                                            w.nMinors := by
                                        have := w.hrecIdx; omega
                                      have hpreG : w.preMajor.length =
                                          (piCount w.famMember.mtype -
                                            rest.length) + 1 +
                                          (w.recRef - w.familyRef - 1) +
                                          rest.length := by
                                        rw [hnparamsEq, hnMinorsEq, hlenB]
                                        exact w.hpre
                                      have hpreG' :
                                          w.preMajor.reverse.reverse.length =
                                            (piCount w.famMember.mtype -
                                              rest.length) + 1 +
                                            (w.recRef - w.familyRef - 1) +
                                            rest.length := by
                                        rw [List.reverse_reverse]
                                        exact hpreG
                                      rw [dif_pos hpreG']
                                      have harityG :
                                          w.preMajor.reverse.reverse.length +
                                            1 = piCount w.recMember.mtype := by
                                        rw [List.reverse_reverse]
                                        have := w.hpre
                                        have := w.hnmin
                                        omega
                                      rw [dif_pos harityG]
                                      have hspMaj := appsSpine_ctorMajor w
                                      have hctorArgsEq :
                                          (appsSpine (ctorMajor w)).2 =
                                            w.ctorParams ++ w.fields :=
                                        congrArg Prod.snd hspMaj
                                      have htkLen : w.ctorParams.length =
                                          w.nparams := w.hctorParams
                                      have hctorLenG :
                                          (appsSpine (ctorMajor w)).2.length =
                                            piCount w.ctorMember.mtype := by
                                        rw [hctorArgsEq]
                                        simp only [List.length_append, htkLen]
                                        exact w.hnpar
                                      rw [dif_pos hctorLenG]
                                      have hle2 :
                                          piCount w.famMember.mtype -
                                            rest.length ≤
                                            (appsSpine (ctorMajor w)).2.length := by
                                        rw [hnparamsEq, hctorArgsEq]
                                        simp only [List.length_append, htkLen]
                                        omega
                                      rw [dif_pos hle2]
                                      have hctorIdxEq :
                                          w.ctorRef - w.familyRef - 1 =
                                            w.ctorIdx := by
                                        have := w.hctorIdx; omega
                                      have hdrop :
                                          List.drop
                                            (piCount w.famMember.mtype -
                                              rest.length)
                                            (appsSpine (ctorMajor w)).2 =
                                          w.fields := by
                                        rw [hnparamsEq, hctorArgsEq]
                                        exact List.drop_left' htkLen
                                      have hpeelN :
                                          piCount w.famMember.mtype -
                                              rest.length +
                                            (List.drop
                                              (piCount w.famMember.mtype -
                                                rest.length)
                                              (appsSpine (ctorMajor w)).2).length =
                                          w.nparams + w.fields.length := by
                                        rw [hdrop, hnparamsEq]
                                      have hpeelLoc :
                                          peelPis
                                            (piCount w.famMember.mtype -
                                                rest.length +
                                              (List.drop
                                                (piCount w.famMember.mtype -
                                                  rest.length)
                                                (appsSpine (ctorMajor w)).2).length)
                                            w.ctorMember.mtype =
                                          some (w.ctorDoms, w.ctorResult) := by
                                        rw [hpeelN]; exact w.hpeel
                                      unfold iotaReductCertFill
                                      split
                                      · next hnone =>
                                          exact nomatch
                                            (hnone.symm.trans hpeelLoc)
                                      · next ctorPr hpeelC =>
                                          have : ctorPr =
                                              (w.ctorDoms, w.ctorResult) :=
                                            Option.some.inj
                                              (hpeelC.symm.trans hpeelLoc)
                                          subst this
                                          dsimp only [Prod.snd, Prod.fst]
                                          rw [dif_pos w.hfamApp]
                                          have hkindsLoc :
                                              analyzeFields w.familyRef
                                                (List.drop
                                                  (piCount w.famMember.mtype -
                                                    rest.length)
                                                  w.ctorDoms) =
                                              some w.kinds := by
                                            rw [hnparamsEq]; exact w.hkinds
                                          split
                                          · next hn =>
                                              exact nomatch
                                                (hn.symm.trans hkindsLoc)
                                          · next kinds hk =>
                                              have : kinds = w.kinds :=
                                                Option.some.inj
                                                  (hk.symm.trans hkindsLoc)
                                              subst this
                                              have hlenLoc :
                                                  w.kinds.length =
                                                    (List.drop
                                                      (piCount
                                                          w.famMember.mtype -
                                                        rest.length)
                                                      (appsSpine
                                                        (ctorMajor w)).2).length := by
                                                rw [hdrop]; exact w.hlen
                                              rw [dif_pos hlenLoc]
                                              have hminorLoc :
                                                  w.preMajor.reverse.reverse[
                                                    piCount w.famMember.mtype -
                                                      rest.length + 1 +
                                                      (w.ctorRef -
                                                        w.familyRef - 1)]? =
                                                  some w.minor := by
                                                rw [List.reverse_reverse,
                                                  hnparamsEq, hctorIdxEq]
                                                exact w.hminor
                                              split
                                              · next hn =>
                                                  exact nomatch
                                                    (hn.symm.trans hminorLoc)
                                              · next minor hm =>
                                                  have : minor = w.minor :=
                                                    Option.some.inj
                                                      (hm.symm.trans
                                                        hminorLoc)
                                                  subst this
                                                  have hmotiveLoc :
                                                      w.preMajor.reverse.reverse[
                                                        piCount
                                                            w.famMember.mtype -
                                                          rest.length]? =
                                                      some (recMotiveOf w) := by
                                                    rw [List.reverse_reverse,
                                                      hnparamsEq]
                                                    exact recMotiveOf_spec w
                                                  split
                                                  · next hn =>
                                                      exact nomatch
                                                        (hn.symm.trans
                                                          hmotiveLoc)
                                                  · next motive hmot =>
                                                      have : motive =
                                                          recMotiveOf w :=
                                                        Option.some.inj
                                                          (hmot.symm.trans
                                                            hmotiveLoc)
                                                      subst this
                                                      have hminDomLoc :
                                                          applyTel
                                                            (List.take
                                                              (piCount
                                                                  w.famMember.mtype -
                                                                rest.length +
                                                                1 +
                                                                (w.ctorRef -
                                                                  w.familyRef -
                                                                  1))
                                                              w.preMajor.reverse.reverse)
                                                            (instantiateLevels w.ls
                                                              w.recMember.mtype) =
                                                          some
                                                            (Expr.pi
                                                              (recMinorDom w w.ls).1
                                                              (recMinorDom w w.ls).2.1) := by
                                                        rw [List.reverse_reverse,
                                                          hnparamsEq,
                                                          hctorIdxEq]
                                                        exact (recMinorDom w w.ls).2.2
                                                      split
                                                      · next hn =>
                                                          exact nomatch
                                                            (hn.symm.trans
                                                              hminDomLoc)
                                                      · next h =>
                                                          exact nomatch
                                                            (h.symm.trans
                                                              hminDomLoc)
                                                      · next h =>
                                                          exact nomatch
                                                            (h.symm.trans
                                                              hminDomLoc)
                                                      · next h =>
                                                          exact nomatch
                                                            (h.symm.trans
                                                              hminDomLoc)
                                                      · next h =>
                                                          exact nomatch
                                                            (h.symm.trans
                                                              hminDomLoc)
                                                      · next h =>
                                                          exact nomatch
                                                            (h.symm.trans
                                                              hminDomLoc)
                                                      · next h =>
                                                          exact nomatch
                                                            (h.symm.trans
                                                              hminDomLoc)
                                                      · next h =>
                                                          exact nomatch
                                                            (h.symm.trans
                                                              hminDomLoc)
                                                      · next mdom restMin hmd =>
                                                          have hpi :=
                                                            Option.some.inj
                                                              (hmd.symm.trans
                                                                hminDomLoc)
                                                          injection hpi
                                                            with hmdom hrest
                                                          subst hmdom
                                                          subst hrest
                                                          have hctorAfterLoc :
                                                              applyTel
                                                                (List.take
                                                                  (piCount
                                                                      w.famMember.mtype -
                                                                    rest.length)
                                                                  w.preMajor.reverse.reverse)
                                                                (instantiateLevels w.ls
                                                                  w.ctorMember.mtype) =
                                                              some
                                                                w.ctorAfterParams := by
                                                            rw [List.reverse_reverse,
                                                              hnparamsEq]
                                                            exact w.hctorAfter
                                                          split
                                                          · next hn =>
                                                              exact nomatch
                                                                (hn.symm.trans
                                                                  hctorAfterLoc)
                                                          · next ctorAfter
                                                              hca =>
                                                              have :
                                                                  ctorAfter =
                                                                    w.ctorAfterParams :=
                                                                Option.some.inj
                                                                  (hca.symm.trans
                                                                    hctorAfterLoc)
                                                              subst this
                                                              rw [dif_pos
                                                                w.hctorTel]
                                                              rw [dif_pos
                                                                w.hfamTel]
                                                              rw [dif_pos
                                                                w.hresTel]
                                                              unfold iotaReductCertFillIdx
                                                              have hrecBodyLoc :
                                                                  (w.recDoms,
                                                                      w.recBody).2 =
                                                                    foldApps
                                                                      (.bvar
                                                                        (w.recRef -
                                                                          w.familyRef -
                                                                          1 +
                                                                          rest.length +
                                                                          1))
                                                                      ((List.range
                                                                            rest.length).reverse.map
                                                                        (fun i =>
                                                                          Expr.bvar
                                                                            (i +
                                                                              1)) ++
                                                                        [Expr.bvar
                                                                          0]) := by
                                                                dsimp only [Prod.snd]
                                                                rw [hnMinorsEq, hlenB]
                                                                exact w.hrecBody
                                                              rw [dif_pos hrecBodyLoc]
                                                              have hmajorTyLoc :
                                                                  (w.recDoms,
                                                                      w.recBody).1[piCount
                                                                        w.famMember.mtype -
                                                                      rest.length +
                                                                      1 +
                                                                      (w.recRef -
                                                                        w.familyRef -
                                                                        1) +
                                                                      rest.length]? =
                                                                    some
                                                                      (foldApps
                                                                        (.const
                                                                          w.familyRef
                                                                          ((List.range
                                                                              w.famMember.arity).map
                                                                            Level.param))
                                                                        ((List.range
                                                                              (piCount
                                                                                  w.famMember.mtype -
                                                                                rest.length)).reverse.map
                                                                          (fun i =>
                                                                            Expr.bvar
                                                                              (i +
                                                                                rest.length +
                                                                                (w.recRef -
                                                                                  w.familyRef -
                                                                                  1) +
                                                                                1)) ++
                                                                          (List.range
                                                                                rest.length).reverse.map
                                                                            (fun i =>
                                                                              Expr.bvar
                                                                                i))) := by
                                                                dsimp only [Prod.fst]
                                                                rw [hnparamsEq, hnMinorsEq,
                                                                  hlenB]
                                                                exact w.hmajorTy
                                                              rw [dif_pos hmajorTyLoc]
                                                              -- 00 §20.7 B2: the
                                                              -- level-arity guard,
                                                              -- discharged from the
                                                              -- witness's own field.
                                                              rw [dif_pos w.hlsLen]
                                                              rfl

/-- Cert some lifts: Fill inversion gives hcanon of the source,
then `iotaReductCert_of` of `liftWitness`. Mixed some/none in
`develWfGo_lift` closes with this. Reverse (cert of a lift isSome
⇒ cert of the source) needs `unliftWitness`: spine unlift is
`map_eq_snoc_unlift` / `iotaLhs_eq_lift_preMajor`; the Fill pack
still needs unlifted `ctorAfterParams`/`mdom`. Do not inhabit with
`cert_of` of the lifted witness (wrong lhs). -/
theorem iotaReductCert_lift_isSome_of {E : ResolvedEnv} (c : Nat)
    {e : Expr Nat} {w : IotaWitness E} {hlhs : iotaLhsOf w = e}
    (h : iotaReductCert E e = some ⟨w, hlhs⟩) :
    (iotaReductCert E (lift c 1 e)).isSome = true := by
  have hlw : iotaLhsOf (liftWitness c w) = lift c 1 e := by
    rw [iotaLhsOf_lift, hlhs]
  have his := iotaReductCert_of (liftWitness c w)
  rw [hlw] at his
  exact his

-- Deleted: `hcanon_unliftWitness` packed idxPositions (moved to IotaTyping / EnvWf).
/-- Reverse of `iotaReductCert_lift_isSome_of`: a cert on `lift e`
unlifts (Fill of the unlifted spine) to a cert on `e`. Mixed none/some
in `develWfGo_lift` closes by this Bool, not by `none = some` across
different `Σ'` payloads. -/
theorem iotaReductCert_isSome_of_lift {E : ResolvedEnv} (c : Nat)
    {e : Expr Nat}
    (h : (iotaReductCert E (lift c 1 e)).isSome = true) :
    (iotaReductCert E e).isSome = true := by
  cases hc : iotaReductCert E (lift c 1 e) with
  | none =>
      simp only [hc, Option.isSome] at h
      nomatch h
  | some wσ =>
      match wσ with
      | ⟨w, hlhs⟩ =>
          have hargs := iotaLhs_eq_lift_preMajor w hlhs
          have ⟨pre0, maj0, hys, hpre, hmaj⟩ :=
            map_eq_snoc_unlift (appsSpine e).2 w.preMajor (ctorMajor w) hargs
          have hhd : (appsSpine e).1 = .const w.recRef w.ls := by
            have h1 := appsSpine_iotaLhs w
            have h2 : appsSpine (iotaLhsOf w) = appsSpine (lift c 1 e) :=
              congrArg appsSpine hlhs
            have h3 := appsSpine_lift c 1 e
            have hs := h1.symm.trans (h2.trans h3)
            have hfst := congrArg Prod.fst hs
            simp only [lift] at hfst
            exact lift_eq_const hfst.symm
          have hlen_take :
              (w.preMajor.take w.nparams).length = w.nparams := by
            simp only [List.length_take]
            have hp := w.hpre
            have : w.nparams ≤ w.preMajor.length := by omega
            exact Nat.min_eq_left this
          have hspM := appsSpine_ctorMajor w
          have hspEq : appsSpine (ctorMajor w) =
              appsSpine (lift c 1 maj0) := congrArg appsSpine hmaj
          have hargsM :
              w.ctorParams ++ w.fields =
                (appsSpine maj0).2.map (lift c 1) := by
            have hs := hspM.symm.trans (hspEq.trans (appsSpine_lift c 1 maj0))
            exact congrArg Prod.snd hs
          have htk :
              w.preMajor.take w.nparams =
                (pre0.take w.nparams).map (lift c 1) := by
            rw [hpre, ← List.map_take (lift c 1) pre0 w.nparams]
          have hlenC : w.ctorParams.length = w.nparams := w.hctorParams
          let ctorParams0 := (appsSpine maj0).2.take w.nparams
          let fields0 := (appsSpine maj0).2.drop w.nparams
          have hctorP :
              w.ctorParams = ctorParams0.map (lift c 1) := by
            have hL : (w.ctorParams ++ w.fields).take w.nparams =
                w.ctorParams := List.take_left' hlenC
            have hR :
                ((appsSpine maj0).2.map (lift c 1)).take w.nparams =
                  ((appsSpine maj0).2.take w.nparams).map (lift c 1) :=
              (List.map_take (lift c 1) (appsSpine maj0).2 w.nparams).symm
            have hboth := congrArg (List.take w.nparams) hargsM
            rw [hL, hR] at hboth
            exact hboth
          have hfields :
              w.fields = fields0.map (lift c 1) := by
            have hL : (w.ctorParams ++ w.fields).drop w.nparams =
                w.fields := List.drop_left' hlenC
            have hR :
                ((appsSpine maj0).2.map (lift c 1)).drop w.nparams =
                  ((appsSpine maj0).2.drop w.nparams).map (lift c 1) :=
              (List.map_drop (lift c 1) (appsSpine maj0).2 w.nparams).symm
            have hboth := congrArg (List.drop w.nparams) hargsM
            rw [hL, hR] at hboth
            exact hboth
          have ⟨minor0, hminSlot, hminLift⟩ :=
            getElem?_unlift (c := c) (i := w.nparams + 1 + w.ctorIdx)
              (xs := pre0) (y := w.minor) (by
                rw [← hpre, w.hminor])
          have ⟨motive0, hmotSlot, hmotLift⟩ :=
            getElem?_unlift (c := c) (i := w.nparams)
              (xs := pre0) (y := recMotiveOf w) (by
                rw [← hpre, recMotiveOf_spec w])
          have hctorAfter_map :
              applyTel ((pre0.take w.nparams).map (lift c 1))
                  (instantiateLevels w.ls w.ctorMember.mtype) =
                some w.ctorAfterParams := by
            have happ := w.hctorAfter
            rw [htk] at happ
            exact happ
          have hmapC := applyTel_map_lift c 1 (pre0.take w.nparams)
            (instantiateLevels w.ls w.ctorMember.mtype)
          rw [lift_of_closed (instantiateLevels w.ls w.ctorMember.mtype)
            (instantiateLevels_closed0 w.hctorClosed w.ls) c 1] at hmapC
          rw [hctorAfter_map] at hmapC
          have ⟨ctorAfter0, hctorAfter0, hctorAfterLift⟩ :
              ∃ ctorAfter0,
                applyTel (pre0.take w.nparams)
                    (instantiateLevels w.ls w.ctorMember.mtype) =
                  some ctorAfter0 ∧
                lift c 1 ctorAfter0 = w.ctorAfterParams := by
            cases htel : applyTel (pre0.take w.nparams)
                (instantiateLevels w.ls w.ctorMember.mtype) with
            | none =>
                simp only [htel, Option.map] at hmapC
                nomatch hmapC
            | some V =>
                simp only [htel, Option.map] at hmapC
                injection hmapC with hV
                exact ⟨V, rfl, hV.symm⟩
          let w0 := unliftWitness c w pre0 fields0 ctorParams0
            minor0 ctorAfter0 hpre hfields hctorP
            hminLift.symm hctorAfterLift.symm
          have hlhs0 : iotaLhsOf w0 = e := by
            have hfold := foldApps_appsSpine e
            rw [hhd, hys] at hfold
            have hmajHd : (appsSpine maj0).1 = .const w.ctorRef w.lsC := by
              have hs := hspM.symm.trans
                (hspEq.trans (appsSpine_lift c 1 maj0))
              have hfst := congrArg Prod.fst hs
              simp only [lift] at hfst
              exact lift_eq_const hfst.symm
            have hmajArgs : (appsSpine maj0).2 =
                ctorParams0 ++ fields0 :=
              (List.take_append_drop w.nparams (appsSpine maj0).2).symm
            have hmaj0 : maj0 = ctorMajor w0 := by
              have hf := foldApps_appsSpine maj0
              rw [hmajHd, hmajArgs] at hf
              have hcm : ctorMajor w0 =
                  foldApps (.const w.ctorRef w.lsC)
                    (ctorParams0 ++ fields0) := rfl
              exact hf.symm.trans hcm.symm
            have hunf : iotaLhsOf w0 =
                recCall (.const w.recRef w.ls) pre0 (ctorMajor w0) := rfl
            rw [hunf, recCall, ← hmaj0]
            exact hfold
          have his := iotaReductCert_of w0
          rw [hlhs0] at his
          exact his


/-- One-shot iota in devel: `devel lhs = rhs` (rhs not further developed). -/
theorem devel_iota {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {lhs rhs : Expr Nat} (h : DerivedIota E lhs rhs) :
    devel E n Γ lhs = rhs := by
  match h with
  | .of w =>
      have happ := iotaLhsOf_app w
      have hred := iotaReduct_of w
      rw [happ]
      simp only [devel]
      rw [← happ, hred]

/-- Sort-shaped one-shot iota. `foldApps minor rhsArgs` CAN be a sort
(empty `rhsArgs` and `minor` a sort); do not claim iota never returns
a sort. Complete Takahashi `devel lhs = devel rhs` is FALSE when the
rhs is not already a devel-normal form (rhs is not a subterm). -/
theorem devel_iota_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {lhs rhs : Expr Nat} {u : Level}
    (h : DerivedIota E lhs rhs) (hr : rhs = .sort u) :
    devel E n Γ lhs = .sort u := by
  rw [devel_iota h, hr]

/-
F-05b attempt 9: iota in devel is one-shot (`iotaReduct` / `devel_iota`).
M-001: complete Takahashi `devel (iotaLhsOf w) = devel (iotaRhsOf w)` is
FALSE — the rhs is not a subterm, so devel cannot recurse into it (same
one-shot as delta). Sort-shaped `devel_iota_sort` holds: if the iota rhs
is a sort (possible: nil fields and minor a sort), devel of the lhs is
that sort. irr postponement remains for conv_devel_is_sort / SortConvChar.
Ledger not flipped.
-/

/-! PiConvInj fragment `parRedStar_pi_inj` is above (star injectivity).
`devel_pi_inj` / `parRedStar_devel` from the parallel pci arc assumed
devel does not fire iota; that contradicts `iotaReduct` in `devel`.
Not merged (M-001). -/

/-! ### Star congruence and complete-development reduct (PiConvInj fragment).

`ParRed t (devel t)` is false: devel of `app` fires delta-then-beta when
`f` unfolds to a lam, which is two ParRed constructors. `ParRedStar`
is the matching judgment. Iota is one-shot in `devel` (`iotaReduct`);
`parRedStar_devel` of an iota redex must fire `ParRed.iota`.
Eta is not contracted in `devel` of a lam; a pi has no eta-contract. -/

/- PiConvInj fragment `parRedStar_pi_inj` is earlier. `parRedStar_devel` /
`devel_pi_inj` assumed devel does not fire iota; `iotaReduct` in devel
makes that false (M-001). Not merged. -/

/-! ### F-05b eta / irr postponement for sorts (attempt 9).

Recorded route (00 §19 F-05b): eta and irr as postponement lemmas, not
eta-short devel. Wiring `etaContract` into `devel` would make
`devel (etaExpand f) = devel f`, but `ParRed` has no eta constructor, so
a contracted lam would not be a `parRedStar` reduct of the original lam;
`devel_lift` was reverted on the same grounds. Keep postponement.

Eta: the expansion side is a lam (never a sort). `HasTy (sort u) (pi A B)`
is not constructor-impossible at the Conv layer (trans through middles
still exists) — it **yields a smaller Conv** `sort (succ u) ≈ pi A B` via
`hasTySortInv`, and the HasTy derivation must be `HasTy.conv`
(`HasTy.sort` ascribes a sort, not a Π).

Irr: `nfRel (devel p) (devel q)` for arbitrary proofs is false. Restricted
to `p = sort u` (and `q = sort v`): `hasTySortInv` yields
`Conv (sort (succ u)) P` with `P : Prop`. `HasTy.sort` never ascribes
Prop (`succ ≠ 0`). `eqN (succ l) 0` is false by eval. Do not conclude
`eqN u v` or `False` from the sort-sort Conv that remains — that is
SortConvChar (circular with uniqueTy / DT-012). Do not inhabit
`conv_nfRel`. -/

/-- The eta-expansion side of `Conv.eta` is a lambda, never a sort. -/
theorem etaExpand_ne_sort (A f : Expr Nat) (u : Level) :
    Expr.lam A (.app (lift 0 1 f) (.bvar 0)) ≠ .sort u :=
  fun h => nomatch h

/-- devel of an eta-expansion of a sort is still a lam (eta is not
contracted in devel). So `nfRel` of that development against `devel (sort u)`
is false — postponement, not eta-short devel. -/
theorem devel_etaExpand_sort {E : ResolvedEnv} {n : Nat}
    (Γ : LCtx) (A : Expr Nat) (u : Level) :
    devel E n Γ (.lam A (.app (lift 0 1 (.sort u)) (.bvar 0))) =
      .lam (devel E n Γ A) (.app (.sort u) (.bvar 0)) := by
  have hι : iotaReduct E (.app (.sort u) (.bvar 0)) = none := by
    simp only [iotaReduct, appsSpine]
  simp only [lift, devel, hι, lookupValue, List.get?_cons_zero]

theorem nfRel_etaExpand_sort_false {E : ResolvedEnv} {n : Nat}
    (Γ : LCtx) (A : Expr Nat) (u : Level) :
    ¬ nfRel
        (devel E n Γ (.lam A (.app (lift 0 1 (.sort u)) (.bvar 0))))
        (devel E n Γ (.sort u)) := by
  rw [devel_etaExpand_sort, devel_sort]
  intro h
  exact nomatch h

/-- `HasTy (sort u) (pi A B)` yields `Conv (sort (succ u)) (pi A B)`.
Not impossible at the Conv layer (M-001: trans through middles); the
yielded Conv is the `hasTySortInv` characterization. -/
def hasTySort_pi {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {u : Level} {A B : Expr Nat}
    (h : HasTy E n Γ (.sort u) (.pi A B)) :
    Conv E n Γ (.sort (.succ u)) (.pi A B) :=
  hasTySortInv h rfl

/-- `HasTy.sort` ascribes a sort, never a Π. So `HasTy (sort u) (pi A B)`
is a `HasTy.conv` peel: a strictly smaller inner typing of the sort,
plus a Conv onto the Π. -/
def hasTySortPi_is_conv {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T →
    {u : Level} → {A B : Expr Nat} →
    e = .sort u → T = .pi A B →
    Σ' (U : Expr Nat), HasTy E n Γ e U ×' Conv E n Γ U T
  | _, _, _, .sort _ _, _, _, _, _heq, hT => nomatch hT
  | _, _, _, .conv _ _ A0 _B0 h hc, _, _, _, _heq, hT =>
      ⟨A0, h, hT ▸ hc⟩
  | _, _, _, .bvar _ _ _ _, _, _, _, heq, _ => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, _, _, heq, _ => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, _, _, heq, _ => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, _, _, heq, _ => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, _, _, heq, _ => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, _, _, _, heq, _ => nomatch heq
  | _, _, _, .lit _ _ _ _, _, _, _, heq, _ => nomatch heq

/-- The Conv `hasTySortInv` builds is no larger than the typing it
inverts. For a `HasTy.conv` peel it is the inner inversion trans the
outer Conv; for `HasTy.sort` it is `refl`. -/
theorem sizeConv_hasTySortInv {E : ResolvedEnv} {n : Nat} {l : Level} :
    {Γ : LCtx} → {e T : Expr Nat} →
    (h : HasTy E n Γ e T) → (heq : e = .sort l) →
    sizeConv (hasTySortInv h heq) ≤ sizeHasTy h
  | _, _, _, .sort _Γ _l', heq => by
      injection heq with h1; subst h1
      simp only [hasTySortInv, sizeConv, sizeHasTy]
      exact Nat.le_refl 1
  | _, _, _, .conv _Γ _e _A0 _B0 h hc, heq => by
      simp only [hasTySortInv, sizeConv, sizeHasTy]
      have ih := sizeConv_hasTySortInv h heq
      exact Nat.add_le_add_right (Nat.add_le_add_right ih _) _
  | _, _, _, .bvar _ _ _ _, heq => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, heq => nomatch heq
  | _, _, _, .lit _ _ _ _, heq => nomatch heq

/-- `⟦succ l⟧ρ` is never `some 0`. -/
theorem eval_succ_ne_zero (ρ : Nat → Option Nat) (l : Level) :
    eval ρ (.succ l) ≠ some 0 := by
  simp only [eval]
  cases eval ρ l with
  | none => intro h; cases h
  | some k =>
      intro h
      injection h with hk
      exact Nat.succ_ne_zero k hk

/-- `succ l =ₙ 0` is false at every valuation. -/
theorem eqN_succ_ne_zero (l : Level) : ¬ eqN (.succ l) .zero := by
  intro h
  have heq := h (fun _ => none)
  exact eval_succ_ne_zero (fun _ => none) l (by rw [heq]; rfl)

/-- The level-eval tooth quoted by the irr-of-sorts postponement. -/
theorem eqN_succ_succ_ne_zero (l : Level) :
    ¬ eqN (.succ (.succ l)) .zero :=
  eqN_succ_ne_zero (.succ l)

/-- `HasTy.sort` ascribes `sort (succ l)`, never Prop. So
`HasTy (sort u) (sort 0)` is a `HasTy.conv` peel. -/
def hasTySort_at_zero_is_conv {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {e T : Expr Nat} →
    HasTy E n Γ e T →
    {u : Level} →
    e = .sort u → T = .sort .zero →
    Σ' (U : Expr Nat), HasTy E n Γ e U ×' Conv E n Γ U (.sort .zero)
  | _, _, _, .sort _ _l', _, _heq, hT =>
      False.elim (by
        injection hT with hs
        cases hs)
  | _, _, _, .conv _ _ A0 _B0 h hc, _, _heq, hT =>
      ⟨A0, h, hT ▸ hc⟩
  | _, _, _, .bvar _ _ _ _, _, heq, _ => nomatch heq
  | _, _, _, .const _ _ _ _ _ _ _, _, heq, _ => nomatch heq
  | _, _, _, .pi _ _ _ _ _ _ _, _, heq, _ => nomatch heq
  | _, _, _, .lam _ _ _ _ _ _ _, _, heq, _ => nomatch heq
  | _, _, _, .app _ _ _ _ _ _ _, _, heq, _ => nomatch heq
  | _, _, _, .letE _ _ _ _ _ _ _ _, _, heq, _ => nomatch heq
  | _, _, _, .lit _ _ _ _, _, heq, _ => nomatch heq

/-- Restricted irr postponement: a sort proof yields
`Conv (sort (succ u)) P` by `hasTySortInv`. Does not use uniqueTy /
SortConvChar. -/
def irr_sort_char {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {P p q : Expr Nat} {u : Level}
    (_hP : HasTy E n Γ P (.sort .zero))
    (hp : HasTy E n Γ p P)
    (_hq : HasTy E n Γ q P)
    (hp_sort : p = .sort u) :
    Conv E n Γ (.sort (.succ u)) P :=
  hasTySortInv hp hp_sort

/-- Both proofs of an irr are sorts: each universe converts to `P`.
Does not conclude `eqN u v` (that is SortConvChar). -/
def irr_sorts_char {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {P : Expr Nat} {u v : Level}
    (_hP : HasTy E n Γ P (.sort .zero))
    (hp : HasTy E n Γ (.sort u) P)
    (hq : HasTy E n Γ (.sort v) P) :
    Conv E n Γ (.sort (.succ u)) P ×'
      Conv E n Γ (.sort (.succ v)) P :=
  ⟨hasTySortInv hp rfl, hasTySortInv hq rfl⟩

/-- Irr of a sort at syntactic Prop: `hasTySortInv` produces
`Conv (sort (succ u)) (sort 0)`. The levels are not `=ₙ`
(`eqN_succ_ne_zero`). Closing that Conv is SortConvChar, not this
lemma. -/
def irr_sort_at_prop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {u : Level}
    (h : HasTy E n Γ (.sort u) (.sort .zero)) :
    Conv E n Γ (.sort (.succ u)) (.sort .zero) :=
  hasTySortInv h rfl

theorem devel_lam_ne_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A b : Expr Nat) (u : Level) :
    devel E n Γ (.lam A b) ≠ .sort u := by
  simp only [devel]
  intro h
  exact nomatch h

theorem devel_pi_ne_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (A B : Expr Nat) (u : Level) :
    devel E n Γ (.pi A B) ≠ .sort u := by
  simp only [devel]
  intro h
  exact nomatch h

theorem devel_lit_ne_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (t : Nat) (u : Level) :
    devel E n Γ (.lit t) ≠ .sort u := by
  simp only [devel]
  exact natExpand_ne_sort t u

/-! ### F-05b attempt 12: PiConvInj wall — `Conv.irr`.

Measured (do not assume):
- `step_pi_false`: a pi never Steps (beta/iota/delta/zeta/lit heads
  are not pi). `Conv.step` is impossible on a pi-headed subject.
- `Conv.pi` stores `hA` / `hb` (easy arm).
- Delta through a const whose body is a pi is a *middle*, not a
  pi-headed Step. Unique lookup would identify bodies; that is the
  trans-delta join, not a counterexample.
- `devel_pi_inj` is not merged (iota-in-devel).

`irr` is the false-making constructor of the UNCONDITIONED statement.
A transparent junk member `T : Prop := Prop` makes every impredicative
Π (`B : Prop`, so `imax u 0 =ₙ 0`) a *proof of T*: `HasTy.pi` ascribes
`sort (imax u 0)`, `Conv.sorts` + delta identify that universe with
`T`. Proof irrelevance then converts `Π (sort 0). T` to `Π (sort 1). T`.
The domains are distinct universes (`eqN_succ_ne_zero`). Conjunction
with unconditioned sort-characterization at this env is `False`.
O-3: the obligation `PiConvInj` is now `EnvWf`-conditioned; these
theorems stay as type-④ evidence against the raw pair. -/

/-- `imax l 0` is lazy in `l` and equals `0` at every valuation. -/
theorem eqN_imax_zero (l : Level) : eqN (.imax l .zero) .zero :=
  fun _ρ => rfl

/-- Junk transparent `T : Prop := Prop`. Not `EnvWf` (`Prop : Prop` is
false-shaped). Witness that the unconditioned pair is false. -/
def piIrrMember : CheckedMember :=
  ⟨.definitionM, 0, .sort .zero, some (.sort .zero)⟩

def piIrrEnv : ResolvedEnv where
  members := fun r => if r = 0 then some piIrrMember else none

theorem piIrrEnv_lookup : piIrrEnv.members 0 = some piIrrMember := rfl

def piIrr_hasTyP {n : Nat} (Γ : LCtx) :
    HasTy piIrrEnv n Γ (.const 0 []) (.sort .zero) :=
  .const Γ 0 [] piIrrMember rfl rfl (fun _l hl => nomatch hl)

def piIrr_delta {n : Nat} (Γ : LCtx) :
    Step piIrrEnv n Γ (.const 0 []) (.sort .zero) :=
  .delta Γ 0 [] piIrrMember (.sort .zero) rfl rfl rfl

def piIrr_convP {n : Nat} (Γ : LCtx) :
    Conv piIrrEnv n Γ (.sort .zero) (.const 0 []) :=
  .symm _ _ _ (.step _ _ _ (piIrr_delta Γ))

/-- A Π into `T` is a proof of `T`: `HasTy.pi` ascribes
`sort (imax u 0)`, identified with `T` by `=ₙ` and delta. -/
def piIrr_tyPi {n : Nat} (Γ : LCtx) (A : Expr Nat) (u : Level)
    (hA : HasTy piIrrEnv n Γ A (.sort u)) :
    HasTy piIrrEnv n Γ (.pi A (.const 0 [])) (.const 0 []) :=
  .conv _ _ _ _
    (.pi Γ A u (.const 0 []) .zero hA
      (piIrr_hasTyP (LocalDecl.assumption A :: Γ)))
    (.trans _ _ (.sort .zero) _
      (.sorts _ _ _ (eqN_imax_zero u))
      (piIrr_convP Γ))

/-- Concrete `irr` inhabitant: `Conv (Π sort0. T) (Π sort1. T)`. -/
def piIrr_pi_pi {n : Nat} (Γ : LCtx) :
    Conv piIrrEnv n Γ
      (.pi (.sort .zero) (.const 0 []))
      (.pi (.sort (.succ .zero)) (.const 0 [])) :=
  .irr Γ (.const 0 [])
    (.pi (.sort .zero) (.const 0 []))
    (.pi (.sort (.succ .zero)) (.const 0 []))
    (piIrr_hasTyP Γ)
    (piIrr_tyPi Γ (.sort .zero) (.succ .zero) (.sort Γ .zero))
    (piIrr_tyPi Γ (.sort (.succ .zero)) (.succ (.succ .zero))
      (.sort Γ (.succ .zero)))

/-- Unconditioned pi-injectivity at the junk env yields
`Conv (sort 0) (sort 1)`. Not an application of the obligation
`PiConvInj` (that one carries `EnvWf`). -/
def piConvInj_implies_sort_succ {n : Nat} (Γ : LCtx)
    (H : ∀ (Γ' : LCtx) (A B A' B' : Expr Nat),
      Conv piIrrEnv n Γ' (.pi A B) (.pi A' B') →
        Conv piIrrEnv n Γ' A A' ×'
          Conv piIrrEnv n (LocalDecl.assumption A :: Γ') B B') :
    Conv piIrrEnv n Γ (.sort .zero) (.sort (.succ .zero)) :=
  (H Γ (.sort .zero) (.const 0 []) (.sort (.succ .zero)) (.const 0 [])
    (piIrr_pi_pi Γ)).1

/-- Unconditioned sort-characterization and unconditioned
pi-injectivity cannot both hold at `piIrrEnv`. Type-④ evidence
(00 §19.2 erratum). The obligations `SortConvChar` / `PiConvInj`
are the EnvWf-conditioned restatements. -/
theorem piConvInj_sortConvChar_false {n : Nat}
    (hs : ∀ (Γ : LCtx) (u v : Level),
      Conv piIrrEnv n Γ (.sort u) (.sort v) → eqN u v)
    (hp : ∀ (Γ : LCtx) (A B A' B' : Expr Nat),
      Conv piIrrEnv n Γ (.pi A B) (.pi A' B') →
        Conv piIrrEnv n Γ A A' ×'
          Conv piIrrEnv n (LocalDecl.assumption A :: Γ) B B') : False :=
  eqN_succ_ne_zero .zero
    (eqN_symm (hs [] _ _ (piConvInj_implies_sort_succ [] hp)))

/-
F-05b O-3 (this patch): unconditioned PiConvInj is false
(`piIrr_pi_pi` / `piConvInj_sortConvChar_false`, commit 910087743).
Obligations restated with `EnvWf`. Counterexample stays sealed.

F-05b SortConvChar (EnvWf-conditioned) wall: do not recurse on Conv
(attempts 11–13: reconstructed `trans` is not a subterm). Identified
ring is Conv→Join reliability (`parRed_sort` is the ParRed end; irr
arm needs EnvWf typing to cut). Not inhabited. Ledger not flipped.

F-05b attempt 10: `conv_devel_sort_fwd`
  Conv a b → devel a = sort u → Σ' v, devel b = sort v ∧ eqN u v
is the Takahashi statement that would close unconditioned
SortConvChar. Remaining false arms with one-shot devel (M-001):
- Conv.app: devel of an iota/beta redex is one-shot rhs.
- Conv.step iota reverse.
- Conv.eta reverse: devel (η-exp) is a lam.
-/

/-! ### F-05b attempt 14: Conv→Join at sorts (EnvWf).

`parRed_sort` is the ParRed end. Two `ParRedStar`s from the same
term to sorts join by `parRedStar_sort_eq` when either star is
`refl` (source already a sort). Nested `trans` through a non-sort
middle needs `transport_sort` (star + Conv → star); that is the
remaining ring. -/

theorem parRed_lam_ne_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A b : Expr Nat} {e : Expr Nat} {u : Level}
    (h : ParRed E n Γ (.lam A b) e) : e ≠ .sort u :=
  fun he =>
    let ⟨_, _, heq, _, _⟩ := parRed_lam h rfl
    nomatch heq.symm.trans he

def parRedStar_lam_ne_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {u : Level} :
    {A b : Expr Nat} →
    {a e : Expr Nat} →
    (ha : a = .lam A b) →
    (h : ParRedStar E n Γ a e) →
    e ≠ .sort u
  | _, _, _, _, ha, .refl _ _ => fun he => by subst ha; exact nomatch he
  | _, _, _, _, ha, .tail h0 hs => fun he =>
      let ⟨A', b', heq, _, _⟩ := parRed_lam (ha ▸ h0) rfl
      parRedStar_lam_ne_sort heq hs he

theorem parRed_pi_ne_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B : Expr Nat} {e : Expr Nat} {u : Level}
    (h : ParRed E n Γ (.pi A B) e) : e ≠ .sort u :=
  fun he =>
    let ⟨_, _, heq, _, _⟩ := parRed_pi h rfl
    nomatch heq.symm.trans he

def parRedStar_pi_ne_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {u : Level} :
    {A B : Expr Nat} →
    {a e : Expr Nat} →
    (ha : a = .pi A B) →
    (h : ParRedStar E n Γ a e) →
    e ≠ .sort u
  | _, _, _, _, ha, .refl _ _ => fun he => by subst ha; exact nomatch he
  | _, _, _, _, ha, .tail h0 hs => fun he =>
      let ⟨A', B', heq, _, _⟩ := parRed_pi (ha ▸ h0) rfl
      parRedStar_pi_ne_sort heq hs he

/-- Two stars from a *sort* source to sorts: `parRedStar_sort_eq`.
Tail-vs-tail from a non-sort (delta/zeta/beta/iota preimage) WAS
attempt 14's wall; the record is corrected: `parRed_diamond` (13032)
and the general `two_stars_to_sort` (13773) are both inhabited, and
both are sealed. This lemma stays as the source-already-sort
fragment. -/
theorem two_stars_of_sort {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {u w w' : Level}
    (h1 : ParRedStar E n Γ (.sort u) (.sort w))
    (h2 : ParRedStar E n Γ (.sort u) (.sort w')) : eqN w w' :=
  eqN_trans (eqN_symm (parRedStar_sort_eq h1)) (parRedStar_sort_eq h2)

/-
Attempt 14 wall (Conv→Join at sorts) — CLOSED; record corrected.
The statement it named,
two_stars_to_sort : ParRedStar m (sort w) → ParRedStar m (sort w') →
eqN w w' for a non-sort m (tail-vs-tail), IS inhabited (13773): the
sort-preimage case is `parRed_diamond` (13032, the §20.3 pairwise
TML diamond over ParRedCtx) and its strip / star closure (13745,
13759). two_stars_of_sort stays as the source-already-sort fragment.
The earlier instruction "do not inhabit the general form" is
WITHDRAWN: it was written while that diamond was open.

Transport ParRedStar m (sort v) → Conv m b → ParRedStar b (sort w)
is likewise no longer blocked on the diamond: `convRedOnly_join`
(`RcicConvChar.lean`) does it for every Conv derivation using
neither `eta` nor `irr`. What remains is the irr cut, which needs
EnvWf+CtxWf typing (HasTy (sort) P with P : Prop) and, through it,
`parRedSR` — see this file's header wall record (attempt 53 global /
15 on the Conv lane).
-/

end Rcic.Declarative
