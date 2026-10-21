import rcic.RcicIotaFunRecWalk
import rcic.RcicAnnCorrDW
import rcic.RcicAnnIotaCorrUA

/-!
# R-NoFunRec S6 3b-2b port + (e): the walk agreement and the witness corollary

This module is the working port of `lean/rcic/RcicIotaFunRecWalkAgree.lean` —
the walk-agreement algebra plus the `iotaArgs` = `Ann.rhsArgsS` induction,
followed by the (e) witness-level corollary `iotaRhsOfS` = `foldApps minor
(rhsArgsS …)` that segment 3c's assembly consumes.

The landed file `RcicIotaFunRecWalkAgree.lean` is an ORPHANED DRAFT: it is not a
lakefile root, is imported by nothing, and does NOT compile on current main
(14 errors — reported in the PR).  Per the landed-file rule it is left
untouched; every declaration here is re-stated under a `C`-suffixed name, and
this file imports only modules that build on main (`RcicIotaFunRecWalk` for the
TEL-CONS/frame algebra, `RcicAnnCorrDW` for the REL₀ bridge chain
`applyTel_eq_ctorAfterFieldTel` → `ctorAfterFieldTel_eq_ctorFieldTelInst` →
`ctorFieldTelInst_eq_schemaLift`).

Premises are the honest ones only (see the draft's own note): CLOSEDNESS of the
redex's arguments, fuel bounds, level agreement, and the frec arm's
no-created-Π readings carried by `WalkSuppliesC`.  `closure_claim` stays 0. -/

namespace Rcic.Declarative


/-! ## (4) levels through the peel

The copy's parameter application reads the stored type LEVEL-INSTANTIATED
(`instantiateLevels (ls.take arity) ctorMember.mtype` inside `applyTel`), so the
TEL-CONS bridge (§3 of `RcicIotaFunRecWalk`) must see through the level
substitution: levels never touch bvars, so `instantiateLevels` commutes with the
Π-structure and hence with `peelPis`, domain-wise — ALREADY upstream as
`peelPis_instantiateLevels` (`RcicLevelCalc.lean:542`, hypothesis form); consumed
as-is, not duplicated here. -/

/-! ## (5) the frame shift: equation frame ↔ parameter-only frame

R6a's corrected lift (`fields.length + 1 + nMinors + nindices`) puts the constructor's
parameter positions at the TOP of the equation frame; `preMajorBvars_map_instPrefix`
(3b-2a) then instantiates them at the redex's own parameter arguments.  The base bridge
needs the same image under the PARAMETER-ONLY frame `pre.take nparams` that TEL-CONS
produces: for a term closed at `np` (free variables = parameter positions only), both
frames give the SAME parallel image — the prelude's motive/minors/indices slots are
never referenced, and the parameter slots address `pre[np-1-q]` in both. -/

/-- the frame shift at closed parameters: a parameter-frame term's image under
    `pre.take np ++ identity` (lift `nf`, the TEL-CONS frame) equals its image under
    `pre ++ identity` (lift `nf + d`, the equation frame). -/
theorem frame_shiftC (nf d : Nat) :
    (np : Nat) → (pre : List (Expr Nat)) → (T' : Expr Nat) →
    pre.length = np + d →
    exprClosedAt np T' = true →
    (∀ a ∈ pre.take np, exprClosedAt 0 a = true) →
    instPrefix (pre.take np ++ (List.range nf).map Expr.bvar) (lift 0 nf T') =
      instPrefix (pre ++ (List.range nf).map Expr.bvar) (lift 0 (nf + d) T') := by
  intro np
  induction np with
  | zero =>
      intro pre T' hlen hc _
      have hT : lift 0 nf T' = T' :=
        lift_amt_eq_of_exprClosedAt_le hc (Nat.le_refl 0)
      have hT2 : lift 0 (nf + d) T' = T' :=
        lift_amt_eq_of_exprClosedAt_le hc (Nat.le_refl 0)
      simp only [List.take_zero, List.nil_append, hT, hT2]
      rw [instPrefix_exprClosedAt_0 hc _, instPrefix_exprClosedAt_0 hc _]
  | succ n ih =>
      intro pre T' hlen hc hcpre
      obtain ⟨p₀, pre', rfl⟩ : ∃ p₀ pre', pre = p₀ :: pre' := by
        cases pre with
        | nil => simp only [List.length_nil] at hlen; exact absurd hlen (by omega)
        | cons p₀ pre' => exact ⟨p₀, pre', rfl⟩
      have hlen' : pre'.length = n + d := by
        simp only [List.length_cons] at hlen; omega
      have htake : (p₀ :: pre').take (n + 1) = p₀ :: pre'.take n := rfl
      have hpcl : exprClosedAt 0 p₀ = true :=
        hcpre p₀ (htake ▸ List.mem_cons_self p₀ _)
      have hmin : min n pre'.length = n := Nat.min_eq_left (by omega)
      have htl : (pre'.take n ++ (List.range nf).map Expr.bvar).length = n + nf := by
        simp only [List.length_append, List.length_take, List.length_map,
          List.length_range]
        rw [hmin]
      have htr : (pre' ++ (List.range nf).map Expr.bvar).length = n + d + nf := by
        simp only [List.length_append, List.length_map, List.length_range]
        omega
      -- the closedness carrier for the recursive call
      have hclB : exprClosedAt n (instantiate n p₀ T') = true :=
        exprClosedAt_instantiate_cutoff hc (exprClosedAt_mono hpcl (Nat.zero_le n))
      have hcpre' : ∀ a ∈ pre'.take n, exprClosedAt 0 a = true := fun a ha =>
        hcpre a (by rw [htake]; exact List.mem_cons_of_mem _ ha)
      -- the substitution commutation both directions (P4, at the closed head)
      have hpF : ∀ (m : Nat), lift 0 m p₀ = p₀ := fun m =>
        lift_amt_eq_of_exprClosedAt_le hpcl (Nat.le_refl 0)
      have hcomm : instantiate (n + nf) p₀ (lift 0 nf T') =
          lift 0 nf (instantiate n p₀ T') := by
        have h := lift_instantiate_high nf 0 n p₀ (Nat.zero_le n) T'
        rw [hpF nf, Nat.add_comm nf n] at h
        exact h.symm
      have hcomm2 : lift 0 (nf + d) (instantiate n p₀ T') =
          instantiate (nf + d + n) p₀ (lift 0 (nf + d) T') := by
        have h := lift_instantiate_high (nf + d) 0 n p₀ (Nat.zero_le n) T'
        rw [hpF (nf + d)] at h
        exact h
      rw [htake, List.cons_append, instPrefix_cons, htl, hpF (n + nf), hcomm,
        ih pre' (instantiate n p₀ T') hlen' hclB hcpre', hcomm2,
        List.cons_append, instPrefix_cons, htr, hpF (n + d + nf)]
      have hidx : nf + d + n = n + d + nf := by omega
      rw [hidx]

/-! ## (6) the step: pointwise images

At walk step `j` the invariant's args list is `X = pre ++ done ++ I_k`
(`I_k = (List.range k).map bvar`, the INCREASING identity suffix — design
note item 3: bottom slot ↔ the CURRENT binder) and the next step's is
`Y = pre ++ (done ++ [f]) ++ I_{k-1}`; both have the SAME length, and the
only slot whose value changes is the consumed field's.  These are the two
pointwise facts the step needs (`instPrefix_bvar_lt` + slot arithmetic). -/

/-- the identity region: `X`'s image of a remaining-field binder is the
    binder's global canonical slot (decreasing), the current binder (slot 0)
    included. -/
theorem instPrefix_image_bvar_idsC (pre done : List (Expr Nat)) (k i : Nat) :
    i < k →
    instPrefix (pre ++ (done ++ (List.range k).map Expr.bvar)) (.bvar i) =
      .bvar (k - 1 - i) := by
  intro hik
  have hlen : (pre ++ (done ++ (List.range k).map Expr.bvar)).length =
      pre.length + (done.length + k) := by
    simp only [List.length_append, List.length_map, List.length_range]
  have hpos : pre.length + (done.length + k) - 1 - i =
      pre.length + (done.length + (k - 1 - i)) := by omega
  have himp1 : done.length + (k - 1 - i) - done.length = k - 1 - i := by omega
  have hmem : (done ++ (List.range k).map Expr.bvar)[done.length + (k - 1 - i)]? =
      some (.bvar (k - 1 - i)) := by
    have h1 : done.length ≤ done.length + (k - 1 - i) := by omega
    rw [List.getElem?_append_right h1, himp1, List.getElem?_map,
      List.getElem?_range (m := k - 1 - i) (n := k) (by omega)]
    rfl
  apply instPrefix_bvar_lt (j := i) (a := .bvar (k - 1 - i))
  · rw [hlen]; omega
  · have h2 : pre.length ≤ pre.length + (done.length + (k - 1 - i)) := by omega
    have himp2 : pre.length + (done.length + (k - 1 - i)) - pre.length =
        done.length + (k - 1 - i) := by omega
    rw [hlen, hpos, List.getElem?_append_right h2, himp2, hmem]

/-- the consumed slot: `Y`'s image of the just-consumed field's global slot
    (`k-1`) is the redex's own field argument — `instPrefix X_{j+1} (bvar k) = f_r`
    in design note item 4's numbering. -/
theorem instPrefix_image_bvar_consumedC (pre done : List (Expr Nat))
    (f : Expr Nat) (k : Nat) :
    instPrefix (pre ++ ((done ++ [f]) ++ (List.range (k - 1)).map Expr.bvar))
      (.bvar (k - 1)) = f := by
  have hlen : (pre ++ ((done ++ [f]) ++ (List.range (k - 1)).map Expr.bvar)).length =
      pre.length + ((done.length + 1) + (k - 1)) := by
    simp only [List.length_append, List.length_map, List.length_range,
      List.length_cons, List.length_nil]
  have hpos : pre.length + ((done.length + 1) + (k - 1)) - 1 - (k - 1) =
      pre.length + done.length := by omega
  have hmem : ((done ++ [f]) ++ (List.range (k - 1)).map Expr.bvar)[done.length]? =
      some f := by
    have hl : (done ++ [f]).length = done.length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    have h2 : done.length < (done ++ [f]).length := by rw [hl]; omega
    rw [List.getElem?_append_left h2, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self]
    rfl
  apply instPrefix_bvar_lt (j := k - 1) (a := f)
  · rw [hlen]; omega
  · have h3 : pre.length ≤ pre.length + done.length := by omega
    have himp3 : pre.length + done.length - pre.length = done.length := by omega
    rw [hlen, hpos, List.getElem?_append_right h3, himp3, hmem]

/-! ## (7) the image congruences: `Φ = instPrefix X ∘ instantiateLevels ls` through structure

The walk agreement is proved with a CONSTANT final frame `X = pre ++ fields`
(length `count + nf`, invariant across the walk): the schema's walked terms
carry only marker bvars — fields at `[0, nf)`, prelude at `[nf, nf+count)` —
and `Φ` maps them to the redex's own arguments.  Substitution structure
lemmas (upstream): `instPrefix_append`, `instOff_instantiate`, `instOff_lift`,
`instPrefix_instPrefix`, `instPrefix_foldApps`, `instPrefix_const`,
`instPrefix_bvar_lt`, `lift_instantiateLevels`, `instantiateLevels_instantiate0`. -/

/- `exprClosedAt` is level-invariant (upstream: `exprClosedAt_instantiateLevels`,
   `RcicIotaShape.lean`); consumed as-is, not duplicated here. -/

/-- the offset substitution is a Π-congruence: the body image shifts the
    offset by the binder (levels need no shift — they never bind). -/
theorem instOff_piC (k : Nat) : (xs : List (Expr Nat)) → (A B : Expr Nat) →
    instOff k xs (.pi A B) = .pi (instOff k xs A) (instOff (k + 1) xs B)
  | [], _, _ => rfl
  | a :: as, A, B => by
      have hmerge : lift 0 1 (lift 0 (k + as.length) a) =
          lift 0 (k + as.length + 1) a := by
        have h := lift_lift_merge 1 (k + as.length) 0 0 (by omega) (by omega) a
        simpa using h
      have hlen : k + 1 + as.length = k + as.length + 1 := by omega
      have hrec := instOff_piC k as
        (instantiate (k + as.length) (lift 0 (k + as.length) a) A)
        (instantiate (k + as.length + 1) (lift 0 (k + as.length + 1) a) B)
      show instOff k as (.pi (instantiate (k + as.length) (lift 0 (k + as.length) a) A)
          (instantiate (k + as.length + 1) (lift 0 1 (lift 0 (k + as.length) a)) B)) = _
      rw [hmerge, hrec]
      simp only [instOff_cons, hlen]

/-- the parallel prefix substitution as a Π-congruence: the body image is the
    offset-1 form (this is `instOff_piC` at 0, unfolded). -/
theorem instPrefix_piC (X : List (Expr Nat)) (A B : Expr Nat) :
    instPrefix X (.pi A B) =
      .pi (instPrefix X A) (instOff 1 X B) := by
  have h := instOff_piC 0 X A B
  rwa [show (0 : Nat) + 1 = 1 by rfl, instOff_zero, instOff_zero] at h

/-- `Φ` through a Π: domain at the frame, body at the offset-1 frame. -/
theorem img_piC (X : List (Expr Nat)) (ls : List Level) (A B : Expr Nat) :
    instPrefix X (instantiateLevels ls (.pi A B)) =
      .pi (instPrefix X (instantiateLevels ls A))
          (instOff 1 X (instantiateLevels ls B)) := by
  show instPrefix X (.pi (instantiateLevels ls A) (instantiateLevels ls B)) = _
  exact instPrefix_piC X _ _

/-- the canonical field markers deplete from the front: consuming one field
    drops the top marker (`fieldBvars (n+1)` heads with `bvar n`). -/
theorem fieldBvars_succC (n : Nat) :
    fieldBvars (n + 1) = .bvar n :: fieldBvars n := by
  simp only [fieldBvars, List.range_succ, List.reverse_append]
  simp

/-- the walk step, pure algebra: consuming the current binder on the image
    side.  The schema's `instantiate0 (bvar k)` followed by the constant
    frame `X` equals one head consumption `instantiate0 f` against the
    body's offset-1 image — for ANY `f` that is `X`'s image of `bvar k`. -/
theorem instPrefix_stepC (X : List (Expr Nat)) (f : Expr Nat) (k : Nat)
    (eB : Expr Nat) (hk : instPrefix X (.bvar k) = f) :
    instPrefix X (instantiate0 (.bvar k) eB) = instantiate0 f (instOff 1 X eB) := by
  have h1 : instPrefix [.bvar k] eB = instantiate0 (.bvar k) eB := by
    simp only [instPrefix, lift_zero, List.length_nil, instantiate0]
  rw [← h1, instPrefix_instPrefix X [.bvar k] eB]
  simp only [List.map_cons, List.map_nil]
  rw [hk, instPrefix_append X [f] eB]
  show instPrefix [f] (instOff 1 X eB) = _
  simp only [instPrefix, lift_zero, List.length_nil, instantiate0]

/-- the parallel prefix substitution is an application congruence. -/
theorem instPrefix_appC (X : List (Expr Nat)) (u v : Expr Nat) :
    instPrefix X (.app u v) = .app (instPrefix X u) (instPrefix X v) := by
  induction X generalizing u v with
  | nil => rfl
  | cons w ws ih =>
      rw [instPrefix_cons, instPrefix_cons, instPrefix_cons]
      show instPrefix ws (.app (instantiate ws.length (lift 0 ws.length w) u)
          (instantiate ws.length (lift 0 ws.length w) v)) = _
      exact ih _ _

/-- `Φ` through an application fold. -/
theorem img_foldAppsC (X : List (Expr Nat)) (ls : List Level) :
    ∀ (f : Expr Nat) (as : List (Expr Nat)),
      instPrefix X (instantiateLevels ls (foldApps f as)) =
        foldApps (instPrefix X (instantiateLevels ls f))
          (as.map (fun a => instPrefix X (instantiateLevels ls a)))
  | _, [] => rfl
  | f, x :: xs => by
      have h := img_foldAppsC X ls (.app f x) xs
      show instPrefix X (instantiateLevels ls (foldApps (.app f x) xs)) = _
      rw [h]
      simp only [instantiateLevels, instPrefix_appC, List.map_cons]
      rfl

/-- the spine image at a CONST-headed application fold (every site the walk
    agreement uses: family applications).  A substitution can create an
    application at a replaced `bvar`, so the raw-spine form is false in
    general; const heads stay const (`instPrefix_const`). -/
theorem spine_img_constC (X : List (Expr Nat)) (ls : List Level) (r : Nat)
    (lv : List Level) :
    ∀ (as : List (Expr Nat)),
      appsSpine (instPrefix X (instantiateLevels ls (foldApps (.const r lv) as))) =
        (.const r (lv.map (instLevel ls)),
          as.map (fun a => instPrefix X (instantiateLevels ls a)))
  | [] => by
      show appsSpine (instPrefix X (.const r (lv.map (instLevel ls)))) = _
      rw [instPrefix_const]
      rfl
  | x :: xs => by
      rw [img_foldAppsC]
      have hhead : instPrefix X (instantiateLevels ls (.const r lv)) =
          .const r (lv.map (instLevel ls)) := instPrefix_const X r _
      rw [hhead, appsSpine_foldApps]
      rfl

/-- the direct recursive call's image: the schema-side `recCallField` at the
    canonical markers images to the copy-side one at the redex's own
    arguments, given the prefix/field/index agreements. -/
theorem recCallField_imgC (X : List (Expr Nat)) (ls : List Level)
    (rec rec' : Expr Nat) (pm pre : List (Expr Nat)) (np nMin : Nat)
    (fcan fr A_C A_R : Expr Nat)
    (hrec : instPrefix X (instantiateLevels ls rec) = rec')
    (hpm : (recPrefix pm np nMin).map
        (fun a => instPrefix X (instantiateLevels ls a)) = recPrefix pre np nMin)
    (hf : instPrefix X (instantiateLevels ls fcan) = fr)
    (hidx : (familyIdx np A_C).map
        (fun a => instPrefix X (instantiateLevels ls a)) = familyIdx np A_R) :
    instPrefix X (instantiateLevels ls
        (recCallField rec pm np nMin fcan A_C)) =
      recCallField rec' pre np nMin fr A_R := by
  show instPrefix X (instantiateLevels ls
      (foldApps rec (recPrefix pm np nMin ++ familyIdx np A_C ++ [fcan]))) = _
  rw [img_foldAppsC, List.map_append, List.map_append, hpm, hidx, hrec]
  simp only [List.map_cons, List.map_nil, hf]
  rfl

/-! ## (8) identity extension: `idextC X nd = X ++ fieldBvars nd`

MEASURED (2026-10-13, this session — the staged draft's law (a) is FALSE as
stated, in both parts):
- `instPrefix (idextC X nd) (lift 0 nd e) = instPrefix X e` fails without
  closedness: at `X = [x]`, `nd = 1`, `e = .bvar 1` both sides leave the
  out-of-frame bvar untouched but at different heights (`bvar 2` vs `bvar 1`).
  It HOLDS for `e` closed at `|X|` — exactly the walk's marker-closed terms
  (fields at `[0, nf)`, prelude at `[nf, nf+count)`): the induction is on the
  frame, the base frame is empty (a closed term is fixed by `instPrefix` at
  any arguments), and the step commutes the lift through the head entry's
  substitution (`lift_instantiate_high`).
- the pointwise identity-region claim on the `fieldBvars` part is false at the
  FRAME level: `instPrefix (fieldBvars 2) (.bvar 1) = .bvar 2` (entries are
  lifted by the remaining length before use; the INCREASING suffix in (6)
  flips slots rather than fixing them).  The true identity-region fact lives
  at the OFFSET level and is what the frec arm consumes:
  `instOff nd X (.bvar j) = .bvar j` for `j < nd`. -/

/-- the identity extension of a frame: `X` on the top slots, `fieldBvars nd`
    filling the `nd` slots below it. -/
def idextC (X : List (Expr Nat)) (nd : Nat) : List (Expr Nat) := X ++ fieldBvars nd

/-- the identity region at an offset: the offset substitution never fires
    below the offset, whatever the arguments. -/
theorem instOff_bvar_ltC : (xs : List (Expr Nat)) → (k j : Nat) → j < k →
    instOff k xs (.bvar j) = .bvar j
  | [], _, _, _ => rfl
  | a :: as, k, j, hj => by
      have hne : ¬ (j = k + as.length) := by omega
      have hlt : ¬ (k + as.length < j) := by omega
      rw [instOff_cons]
      have hstep : instantiate (k + as.length) (lift 0 (k + as.length) a)
          (.bvar j) = .bvar j := by
        simp only [instantiate, if_neg hne, if_neg hlt]
      rw [hstep]
      exact instOff_bvar_ltC as k j hj

/-- the identity-extension law (draft (a), corrected with the closedness
    premise): for a term closed at the frame length, extending the frame by
    `fieldBvars nd` below and lifting the term by `nd` above addresses `X`'s
    slots exactly as before — the extension is invisible to `X`'s region. -/
theorem instPrefix_idext_liftC (X : List (Expr Nat)) :
    (∀ a ∈ X, exprClosedAt 0 a = true) →
    (nd : Nat) → ∀ (e : Expr Nat), exprClosedAt X.length e = true →
      instPrefix (idextC X nd) (lift 0 nd e) = instPrefix X e := by
  induction X with
  | nil =>
      intro _ nd e he
      have hl : lift 0 nd e = e :=
        lift_amt_eq_of_exprClosedAt_le he (Nat.le_refl 0)
      rw [hl]
      exact instPrefix_exprClosedAt_0 he _
  | cons x xs ih =>
      intro hX nd e he
      have hxF : exprClosedAt 0 x = true := hX x (List.mem_cons_self x xs)
      have hXs : ∀ a ∈ xs, exprClosedAt 0 a = true := fun a ha =>
        hX a (List.mem_cons_of_mem x ha)
      have hlenF : (fieldBvars nd).length = nd := by
        simp only [fieldBvars, List.length_map, List.length_range,
          List.length_reverse]
      have hlen : (xs ++ fieldBvars nd).length = xs.length + nd := by
        simp only [List.length_append, hlenF]
      have hcomm : instantiate (xs.length + nd) (lift 0 (xs.length + nd) x)
          (lift 0 nd e) =
          lift 0 nd (instantiate xs.length (lift 0 xs.length x) e) := by
        have h := lift_instantiate_high nd 0 xs.length
          (lift 0 xs.length x) (Nat.zero_le xs.length) e
        have hentry : lift 0 nd (lift 0 xs.length x) =
            lift 0 (xs.length + nd) x :=
          lift_lift_merge nd xs.length 0 0 (Nat.zero_le 0) (by omega) x
        rw [h, hentry, Nat.add_comm nd xs.length]
      have hfx : lift 0 xs.length x = x :=
        lift_amt_eq_of_exprClosedAt_le hxF (Nat.le_refl 0)
      have hvx : exprClosedAt xs.length (lift 0 xs.length x) = true := by
        rw [hfx]
        exact exprClosedAt_mono hxF (Nat.zero_le xs.length)
      have he' : exprClosedAt xs.length
          (instantiate xs.length (lift 0 xs.length x) e) = true :=
        exprClosedAt_instantiate_cutoff he hvx
      show instPrefix (xs ++ fieldBvars nd)
          (instantiate (xs ++ fieldBvars nd).length
            (lift 0 (xs ++ fieldBvars nd).length x) (lift 0 nd e)) =
        instPrefix xs (instantiate xs.length (lift 0 xs.length x) e)
      rw [hlen, hcomm]
      exact ih hXs nd (instantiate xs.length (lift 0 xs.length x) e) he'

/-! ## (9) the offset image algebra: `instOff k X ∘ instantiateLevels ls`

The frec arm's built call (`Ann.recCallFunS`) sits under the inner
Π-telescope's `nd` binders: the body's image runs at OFFSET `nd`, and each
telescope domain's image under binder `t` at offset `t` — the per-level
offsets (the draft's measured note: the inner domains are NOT plain
`Φ`-images).  These are the general-offset mirrors of (7)'s plain-frame
congruences, plus the two facts that only exist at an offset: the identity
region below it (`instOff_bvar_ltC`, (8)) and the lift-commute
`instOff_lift` (upstream) which turns a lifted entry's image into the lift
of its plain image. -/

/-- consts are invisible to the offset substitution (as at the plain frame). -/
theorem instOff_constC : (xs : List (Expr Nat)) → (k : Nat) → (r : Nat) →
    (lv : List Level) → instOff k xs (.const r lv) = .const r lv
  | [], _, _, _ => rfl
  | _ :: as, k, r, lv =>
      show instOff k as (.const r lv) = .const r lv from instOff_constC as k r lv

/-- the offset substitution is an application congruence. -/
theorem instOff_appC : (xs : List (Expr Nat)) → (k : Nat) → (u v : Expr Nat) →
    instOff k xs (.app u v) = .app (instOff k xs u) (instOff k xs v)
  | [], _, _, _ => rfl
  | a :: as, k, u, v =>
      show instOff k as (.app
        (instantiate (k + as.length) (lift 0 (k + as.length) a) u)
        (instantiate (k + as.length) (lift 0 (k + as.length) a) v)) = _
        from instOff_appC as k _ _

/-- the offset substitution is a λ-congruence: the body image shifts the
    offset by the binder (levels need no shift). -/
theorem instOff_lamC (k : Nat) : (xs : List (Expr Nat)) → (A B : Expr Nat) →
    instOff k xs (.lam A B) = .lam (instOff k xs A) (instOff (k + 1) xs B)
  | [], _, _ => rfl
  | a :: as, A, B => by
      have hmerge : lift 0 1 (lift 0 (k + as.length) a) =
          lift 0 (k + as.length + 1) a := by
        have h := lift_lift_merge 1 (k + as.length) 0 0 (by omega) (by omega) a
        simpa using h
      have hlen : k + 1 + as.length = k + as.length + 1 := by omega
      have hrec := instOff_lamC k as
        (instantiate (k + as.length) (lift 0 (k + as.length) a) A)
        (instantiate (k + as.length + 1) (lift 0 (k + as.length + 1) a) B)
      show instOff k as (.lam (instantiate (k + as.length)
            (lift 0 (k + as.length) a) A)
          (instantiate (k + as.length + 1)
            (lift 0 1 (lift 0 (k + as.length) a)) B)) = _
      rw [hmerge, hrec]
      simp only [instOff_cons, hlen]

/-- the offset substitution through an application fold. -/
theorem instOff_foldAppsC (k : Nat) (xs : List (Expr Nat)) :
    (f : Expr Nat) → (as : List (Expr Nat)) →
      instOff k xs (foldApps f as) =
        foldApps (instOff k xs f) (as.map (instOff k xs))
  | _, [] => rfl
  | f, x :: r => by
      have h := instOff_foldAppsC k xs (.app f x) r
      show instOff k xs (foldApps (.app f x) r) = _
      rw [h]
      simp only [instOff_appC, List.map_cons]
      rfl

/-- a uniform map that fixes every `bvar i`, `i < n`, fixes `fieldBvars n`
    (the argument-list identity — pointwise in the ENTRIES, unlike the frame
    identity which fails, see (8)). -/
theorem fieldBvars_map_constC (n : Nat) (g : Expr Nat → Expr Nat)
    (hg : ∀ i, i < n → g (.bvar i) = .bvar i) :
    (fieldBvars n).map g = fieldBvars n := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [fieldBvars_succC, List.map_cons,
        hg m (Nat.lt_succ_self m), ih (fun i hi => hg i (Nat.lt_succ_of_lt hi))]

/-- the frec spine's canonical argument list images to itself at the offset:
    every entry is inside the identity region. -/
theorem fieldBvars_imgC (X : List (Expr Nat)) (ls : List Level) (nd : Nat) :
    (fieldBvars nd).map
        (fun e => instOff nd X (instantiateLevels ls e)) = fieldBvars nd := by
  refine fieldBvars_map_constC nd _ fun i hi => ?_
  exact instOff_bvar_ltC X nd i hi

/-- the per-level image of a domain list: domain `t` images at offset
    `k + t` — the accumulated binder depth. -/
def telImgC (k : Nat) (xs : List (Expr Nat)) (ls : List Level) :
    List (Expr Nat) → List (Expr Nat)
  | [] => []
  | A :: As => instOff k xs (instantiateLevels ls A) :: telImgC (k + 1) xs ls As

theorem telImg_lengthC (k : Nat) (xs : List (Expr Nat)) (ls : List Level) :
    (doms : List (Expr Nat)) → (telImgC k xs ls doms).length = doms.length
  | [] => rfl
  | _ :: As => by
      simp only [telImgC, List.length_cons]
      exact congrArg Nat.succ (telImg_lengthC (k + 1) xs ls As)

/-- the λ-telescope image, per-level: `instOff` through `lamTelescope`
    images each domain at its own binder depth and the body at the total. -/
theorem img_lamTelescope_offC (xs : List (Expr Nat)) (ls : List Level) (k : Nat) :
    (doms : List (Expr Nat)) → (body : Expr Nat) →
      instOff k xs (instantiateLevels ls (lamTelescope doms body)) =
        lamTelescope (telImgC k xs ls doms)
          (instOff (k + doms.length) xs (instantiateLevels ls body))
  | [], body => by
      simp only [lamTelescope, telImgC, List.length_nil, Nat.add_zero]
  | A :: As, body => by
      have hrec := img_lamTelescope_offC xs ls (k + 1) As body
      show instOff k xs (.lam (instantiateLevels ls A)
            (instantiateLevels ls (lamTelescope As body))) = _
      rw [instOff_lamC, hrec]
      simp only [telImgC, lamTelescope, List.length_cons]
      have hlen : k + 1 + As.length = k + (As.length + 1) := by omega
      rw [hlen]

/-- `Φ` through a λ-telescope at the plain frame ((9)'s per-level law at
    offset 0). -/
theorem img_lamTelescopeC (X : List (Expr Nat)) (ls : List Level)
    (doms : List (Expr Nat)) (body : Expr Nat) :
    instPrefix X (instantiateLevels ls (lamTelescope doms body)) =
      lamTelescope (telImgC 0 X ls doms)
        (instOff doms.length X (instantiateLevels ls body)) := by
  have h := img_lamTelescope_offC X ls 0 doms body
  rwa [instOff_zero, Nat.zero_add] at h

/-- a lifted entry's offset image is the lift of its plain image: the
    frec prefix's per-entry congruence. -/
theorem img_lift_entryC (X : List (Expr Nat)) (ls : List Level) (nd : Nat)
    (a : Expr Nat) :
    instOff nd X (instantiateLevels ls (lift 0 nd a)) =
      lift 0 nd (instPrefix X (instantiateLevels ls a)) := by
  rw [(lift_instantiateLevels ls nd a 0).symm]
  exact instOff_lift nd X _

/-- map fusion with a per-entry law (avoids `Function.comp` juggling at
    the rewrite sites). -/
theorem map_map_imgC (L : List (Expr Nat)) (F G H : Expr Nat → Expr Nat)
    (h : ∀ x, F (G x) = H x) : (L.map G).map F = L.map H := by
  induction L with
  | nil => rfl
  | cons x r ih => simp only [List.map_cons, h x, ih]

/-- level instantiation is an application-fold congruence. -/
theorem instLevels_foldAppsC (ls : List Level) :
    (f : Expr Nat) → (as : List (Expr Nat)) →
      instantiateLevels ls (foldApps f as) =
        foldApps (instantiateLevels ls f) (as.map (instantiateLevels ls))
  | _, [] => rfl
  | f, x :: r => by
      have h := instLevels_foldAppsC ls (.app f x) r
      show instantiateLevels ls (foldApps (.app f x) r) = _
      rw [h]
      simp only [instantiateLevels, List.map_cons]
      rfl

/-- the frec arm's call congruence (draft (b), per-level-offset form): the
    schema-side `recCallFunS` at the canonical inputs images — under the
    constant frame — to the copy-side one at the redex's own arguments.
    Telescope domains image at per-level offsets (`telImgC`), the folded spine
    through the identity region (`instOff_bvar_ltC`), the prefix through the
    lift-commute (`img_lift_entryC`).  The copy-side telescope reading
    `piTelE A_R` is a HYPOTHESIS (`hARtel`), NOT derived: a substitution can
    CREATE Π-structure at a replaced slot (compare `spine_img_constC`'s note),
    so the walk must supply the reading. -/
theorem recCallFunS_imgC (X : List (Expr Nat)) (ls : List Level)
    (rec rec' : Expr Nat) (pm pre : List (Expr Nat)) (np nMin nd : Nat)
    (fcan fr A_C A_R tail_C tail_R : Expr Nat) (doms : List (Expr Nat))
    (hrec : instOff nd X (instantiateLevels ls rec) = rec')
    (hpm : (recPrefix pm np nMin).map
      (fun a => instPrefix X (instantiateLevels ls a)) = recPrefix pre np nMin)
    (hf : instPrefix X (instantiateLevels ls fcan) = fr)
    (hAC : piTelE A_C = (doms, tail_C))
    (hnd : doms.length = nd)
    (hARtel : piTelE A_R = (telImgC 0 X ls doms, tail_R))
    (hidx : (familyIdx np tail_C).map
      (fun a => instOff nd X (instantiateLevels ls a)) = familyIdx np tail_R) :
    instPrefix X (instantiateLevels ls
        (Ann.recCallFunS rec pm np nMin fcan A_C)) =
      Ann.recCallFunS rec' pre np nMin fr A_R := by
  have hLHS : Ann.recCallFunS rec pm np nMin fcan A_C =
      lamTelescope doms
        (recCallField rec (pm.map (lift 0 nd)) np nMin
          (foldApps (lift 0 nd fcan) (fieldBvars nd)) tail_C) := by
    simp only [Ann.recCallFunS, hAC, hnd, fieldBvars]
  have hRHS : Ann.recCallFunS rec' pre np nMin fr A_R =
      lamTelescope (telImgC 0 X ls doms)
        (recCallField rec' (pre.map (lift 0 nd)) np nMin
          (foldApps (lift 0 nd fr) (fieldBvars nd)) tail_R) := by
    simp only [Ann.recCallFunS, hARtel, telImg_lengthC, hnd, fieldBvars]
  rw [hLHS, img_lamTelescopeC, hRHS, hnd]
  -- the folded spine at the offset
  have hfapp : instOff nd X (instantiateLevels ls
      (foldApps (lift 0 nd fcan) (fieldBvars nd))) =
      foldApps (lift 0 nd fr) (fieldBvars nd) := by
    rw [instLevels_foldAppsC, instOff_foldAppsC, img_lift_entryC, hf]
    have hsp : ((fieldBvars nd).map (instantiateLevels ls)).map (instOff nd X) =
        (fieldBvars nd).map
          (fun e => instOff nd X (instantiateLevels ls e)) :=
      map_map_imgC _ _ _ _ (fun _ => rfl)
    rw [hsp, fieldBvars_imgC]
  -- the prefix segment: lifted entries image to lifts of their images
  have hseg1 : ((recPrefix pm np nMin).map (lift 0 nd)).map
      (fun e => instOff nd X (instantiateLevels ls e)) =
      (recPrefix pre np nMin).map (lift 0 nd) := by
    calc ((recPrefix pm np nMin).map (lift 0 nd)).map
          (fun e => instOff nd X (instantiateLevels ls e))
        = (recPrefix pm np nMin).map
          (fun a => instOff nd X (instantiateLevels ls (lift 0 nd a))) :=
          map_map_imgC _ _ _ _ (fun _ => rfl)
      _ = (recPrefix pm np nMin).map
          (fun a => lift 0 nd (instPrefix X (instantiateLevels ls a))) := by
          apply List.map_congr_left
          intro a _
          exact img_lift_entryC X ls nd a
      _ = ((recPrefix pm np nMin).map
          (fun a => instPrefix X (instantiateLevels ls a))).map (lift 0 nd) :=
          (map_map_imgC _ _ _ _ (fun _ => rfl)).symm
      _ = (recPrefix pre np nMin).map (lift 0 nd) := by rw [hpm]
  -- the body: foldApps congruence at the offset, segment by segment
  have hsp : (((recPrefix pm np nMin).map (lift 0 nd)
        ++ familyIdx np tail_C ++ [foldApps (lift 0 nd fcan) (fieldBvars nd)]).map
        (instantiateLevels ls)).map (instOff nd X) =
      ((recPrefix pm np nMin).map (lift 0 nd)
        ++ familyIdx np tail_C ++ [foldApps (lift 0 nd fcan) (fieldBvars nd)]).map
        (fun e => instOff nd X (instantiateLevels ls e)) :=
    map_map_imgC _ _ _ _ (fun _ => rfl)
  refine congrArg (lamTelescope (telImgC 0 X ls doms)) ?_
  show instOff nd X (instantiateLevels ls
      (foldApps rec (recPrefix (pm.map (lift 0 nd)) np nMin
        ++ familyIdx np tail_C ++ [foldApps (lift 0 nd fcan) (fieldBvars nd)]))) =
    foldApps rec' (recPrefix (pre.map (lift 0 nd)) np nMin
      ++ familyIdx np tail_R ++ [foldApps (lift 0 nd fr) (fieldBvars nd)])
  rw [← recPrefix_map_lift pm np nMin nd, ← recPrefix_map_lift pre np nMin nd,
    instLevels_foldAppsC, instOff_foldAppsC, hrec, hsp]
  simp only [List.map_append, List.map_append, hseg1, hidx,
    List.map_cons, List.map_nil, hfapp]

/-! ## (10) the walk agreement (draft (c)): `iotaArgs`'s args image to `Ann.rhsArgsS`'s

The induction runs on a SUPPLIES predicate that mirrors the walk's own
recursion: what each arm must be handed beyond its fuel-success — the
CANONICAL fuel reads (`piTelescopeFuel` returning the syntactic
decomposition; what the fragment's stability gives) and the copy-side
telescope/index readings (the no-created-Π facts `hARtel`-style).  The
fragment-to-supplies connection (`FunRecFrag`/`DirectFieldFrag` ⇒ canon
reads, lift-stable) is the (e)-level measurement, not done here. -/

/-- the frec arm's fuel read at the canonical decomposition: `funRecArg`
    builds exactly `recCallFunS` (seg 2's `funRecArg_eq_recCallFunS` with the
    fragment's consequences taken as hypotheses). -/
theorem funRecArg_of_canonC {E : ResolvedEnv} {fuel : Nat} {rec : Expr Nat}
    {pm : List (Expr Nat)} {np nMin inner : Nat} {f A : Expr Nat}
    (hcanon : piTelescopeFuel E fuel A = some ((piTelE A).1, (piTelE A).2))
    (hinner : (piTelE A).1.length = inner) :
    funRecArg E fuel rec pm np nMin f A inner =
      some (Ann.recCallFunS rec pm np nMin f A) := by
  simp only [funRecArg, hcanon, hinner]
  simp only [Ann.recCallFunS, recCallField, recPrefix_map_lift, hinner]
  rfl

/-- what each walk arm must be SUPPLIED beyond its fuel-success, mirroring
    `iotaArgs`'s own recursion so the agreement induction can consume it arm
    by arm: the CANONICAL fuel reads (what the fragment's stability gives)
    and, at the frec arm, the copy-side telescope/index readings (the
    no-created-Π facts — `hARtel`-style, see (9)'s note).  Markers are the
    walk's own `.bvar k`s. -/
inductive WalkSuppliesC (E : ResolvedEnv) (fuel : Nat) (X : List (Expr Nat))
    (ls : List Level) (np nMin : Nat) :
    List (Expr Nat) → List FieldShape → Expr Nat → Prop
  | supNil (fb : List (Expr Nat)) (T : Expr Nat) (hfb : fb = []) :
      WalkSuppliesC E fuel X ls np nMin fb [] T
  | supNonrec (k : Nat) (fb' : List (Expr Nat)) (ss' : List FieldShape)
      (A B : Expr Nat)
      (sup : WalkSuppliesC E fuel X ls np nMin fb' ss' (instantiate0 (.bvar k) B)) :
      WalkSuppliesC E fuel X ls np nMin (.bvar k :: fb') (.nonrecursive :: ss')
        (.pi A B)
  | supRec0 (k : Nat) (fb' : List (Expr Nat)) (ss' : List FieldShape)
      (A B : Expr Nat)
      (hcanon : piTelescopeFuel E fuel A = some ([], A))
      (hidx : (familyIdx np A).map
        (fun a => instPrefix X (instantiateLevels ls a)) =
        familyIdx np (instPrefix X (instantiateLevels ls A)))
      (sup : WalkSuppliesC E fuel X ls np nMin fb' ss' (instantiate0 (.bvar k) B)) :
      WalkSuppliesC E fuel X ls np nMin (.bvar k :: fb') (.recursive 0 :: ss')
        (.pi A B)
  | supFrec (k : Nat) (fb' : List (Expr Nat)) (ss' : List FieldShape)
      (A B : Expr Nat) (inner : Nat)
      (hcanon : piTelescopeFuel E fuel A = some ((piTelE A).1, (piTelE A).2))
      (hinner : (piTelE A).1.length = inner + 1)
      (hARtel : piTelE (instPrefix X (instantiateLevels ls A)) =
        (telImgC 0 X ls (piTelE A).1,
         instOff (piTelE A).1.length X (instantiateLevels ls (piTelE A).2)))
      (hidx : (familyIdx np (piTelE A).2).map
        (fun a => instOff (piTelE A).1.length X (instantiateLevels ls a)) =
        familyIdx np (instOff (piTelE A).1.length X
          (instantiateLevels ls (piTelE A).2)))
      (sup : WalkSuppliesC E fuel X ls np nMin fb' ss' (instantiate0 (.bvar k) B)) :
      WalkSuppliesC E fuel X ls np nMin (.bvar k :: fb') (.recursive (inner + 1) :: ss')
        (.pi A B)

/-- the walk agreement (draft (c)): under the supplies, `iotaArgs`'s produced
    arguments image — pointwise, under the constant frame — to `Ann.rhsArgsS`'s,
    given the invariant `telR = Φ telC` and the marker list's image being the
    redex's own field list.  The recursor is const-headed (both walks'). -/
theorem iotaArgs_agreeC (E : ResolvedEnv) (fuel : Nat) (X : List (Expr Nat))
    (ls : List Level) (r : Nat) (lv : List Level) (rec' : Expr Nat)
    (pm pre : List (Expr Nat)) (np nMin : Nat)
    (hrec : rec' = .const r (lv.map (instLevel ls)))
    (hpm : (recPrefix pm np nMin).map
      (fun a => instPrefix X (instantiateLevels ls a)) = recPrefix pre np nMin) :
    (ss : List FieldShape) → (fb fs : List (Expr Nat)) → (telC telR : Expr Nat) →
    WalkSuppliesC E fuel X ls np nMin fb ss telC →
    telR = instPrefix X (instantiateLevels ls telC) →
    fb.map (fun a => instPrefix X (instantiateLevels ls a)) = fs →
    ∃ args, iotaArgs E fuel (.const r lv) pm np nMin ss fb telC = some args ∧
      args.map (fun a => instPrefix X (instantiateLevels ls a)) =
        Ann.rhsArgsS rec' pre np nMin fs ss telR := by
  intro ss fb fs telC telR hsup
  induction hsup generalizing telR fs with
  | supNil fb T hfb =>
      intro _ hmark
      rw [hfb] at hmark ⊢
      simp only [List.map_nil] at hmark
      subst hmark
      exact ⟨[], rfl, rfl⟩
  | supNonrec k fb' ss' A B sup ih =>
      intro hINV hmark
      obtain ⟨f, fs', hfs⟩ : ∃ f fs', fs = f :: fs' := by
        cases fs with
        | nil => rw [List.map_cons] at hmark; exact absurd hmark (by simp)
        | cons f fs' => exact ⟨f, fs', rfl⟩
      subst hfs
      rw [List.map_cons, List.cons.injEq] at hmark
      obtain ⟨hhead0, hmark'⟩ := hmark
      have hhead : instPrefix X (instantiateLevels ls (.bvar k)) = f := hhead0
      have htelR : telR = .pi (instPrefix X (instantiateLevels ls A))
          (instOff 1 X (instantiateLevels ls B)) := by rw [hINV, img_piC]
      have hstep : instPrefix X (instantiateLevels ls (instantiate0 (.bvar k) B)) =
          instantiate0 f (instOff 1 X (instantiateLevels ls B)) := by
        rw [instantiateLevels_instantiate0 ls (.bvar k) B]
        exact instPrefix_stepC X f k (instantiateLevels ls B) hhead
      obtain ⟨rest, hrest, hrestmap⟩ := ih
        fs' (instantiate0 f (instOff 1 X (instantiateLevels ls B)))
        (by rw [hstep]) hmark'
      refine ⟨.bvar k :: rest, ?_, ?_⟩
      · show (iotaArgs E fuel (.const r lv) pm np nMin ss' fb'
            (instantiate0 (.bvar k) B)).map
            (fun rest => .bvar k :: rest) = some (.bvar k :: rest)
        rw [hrest]
        rfl
      · rw [htelR, List.map_cons]
        show instPrefix X (instantiateLevels ls (.bvar k)) ::
            rest.map (fun a => instPrefix X (instantiateLevels ls a)) =
          f :: ([] ++ Ann.rhsArgsS rec' pre np nMin fs' ss'
            (instantiate0 f (instOff 1 X (instantiateLevels ls B))))
        rw [hhead, hrestmap]
        rfl
  | supRec0 k fb' ss' A B hcanon hidx sup ih =>
      intro hINV hmark
      obtain ⟨f, fs', hfs⟩ : ∃ f fs', fs = f :: fs' := by
        cases fs with
        | nil => rw [List.map_cons] at hmark; exact absurd hmark (by simp)
        | cons f fs' => exact ⟨f, fs', rfl⟩
      subst hfs
      rw [List.map_cons, List.cons.injEq] at hmark
      obtain ⟨hhead0, hmark'⟩ := hmark
      have hhead : instPrefix X (instantiateLevels ls (.bvar k)) = f := hhead0
      have htelR : telR = .pi (instPrefix X (instantiateLevels ls A))
          (instOff 1 X (instantiateLevels ls B)) := by rw [hINV, img_piC]
      have hstep : instPrefix X (instantiateLevels ls (instantiate0 (.bvar k) B)) =
          instantiate0 f (instOff 1 X (instantiateLevels ls B)) := by
        rw [instantiateLevels_instantiate0 ls (.bvar k) B]
        exact instPrefix_stepC X f k (instantiateLevels ls B) hhead
      obtain ⟨rest, hrest, hrestmap⟩ := ih
        fs' (instantiate0 f (instOff 1 X (instantiateLevels ls B)))
        (by rw [hstep]) hmark'
      have hrecPlain : instPrefix X (instantiateLevels ls (.const r lv)) = rec' := by
        simp only [hrec, instantiateLevels, instPrefix_const]
      have hcall : instPrefix X (instantiateLevels ls
          (recCallField (.const r lv) pm np nMin (.bvar k) A)) =
          recCallField rec' pre np nMin f (instPrefix X (instantiateLevels ls A)) :=
        recCallField_imgC X ls (.const r lv) rec' pm pre np nMin (.bvar k) f A
          (instPrefix X (instantiateLevels ls A)) hrecPlain hpm hhead hidx
      refine ⟨.bvar k :: recCallField (.const r lv) pm np nMin (.bvar k) A :: rest,
        ?_, ?_⟩
      · simp only [iotaArgs, hcanon]
        rw [hrest]
        rfl
      · rw [htelR]
        show instPrefix X (instantiateLevels ls (.bvar k)) ::
            instPrefix X (instantiateLevels ls
              (recCallField (.const r lv) pm np nMin (.bvar k) A)) ::
            rest.map (fun a => instPrefix X (instantiateLevels ls a)) =
          f :: (recCallField rec' pre np nMin f
              (instPrefix X (instantiateLevels ls A)) ::
            Ann.rhsArgsS rec' pre np nMin fs' ss'
              (instantiate0 f (instOff 1 X (instantiateLevels ls B))))
        rw [hhead, hcall, hrestmap]
  | supFrec k fb' ss' A B inner hcanon hinner hARtel hidx sup ih =>
      intro hINV hmark
      obtain ⟨f, fs', hfs⟩ : ∃ f fs', fs = f :: fs' := by
        cases fs with
        | nil => rw [List.map_cons] at hmark; exact absurd hmark (by simp)
        | cons f fs' => exact ⟨f, fs', rfl⟩
      subst hfs
      rw [List.map_cons, List.cons.injEq] at hmark
      obtain ⟨hhead0, hmark'⟩ := hmark
      have hhead : instPrefix X (instantiateLevels ls (.bvar k)) = f := hhead0
      have htelR : telR = .pi (instPrefix X (instantiateLevels ls A))
          (instOff 1 X (instantiateLevels ls B)) := by rw [hINV, img_piC]
      have hstep : instPrefix X (instantiateLevels ls (instantiate0 (.bvar k) B)) =
          instantiate0 f (instOff 1 X (instantiateLevels ls B)) := by
        rw [instantiateLevels_instantiate0 ls (.bvar k) B]
        exact instPrefix_stepC X f k (instantiateLevels ls B) hhead
      obtain ⟨rest, hrest, hrestmap⟩ := ih
        fs' (instantiate0 f (instOff 1 X (instantiateLevels ls B)))
        (by rw [hstep]) hmark'
      have hfun := funRecArg_of_canonC (rec := .const r lv) (pm := pm) (np := np)
        (nMin := nMin) (f := .bvar k) (inner := inner + 1) hcanon hinner
      have hrecOff : instOff (piTelE A).1.length X
          (instantiateLevels ls (.const r lv)) = rec' := by
        simp only [hrec, instantiateLevels, instOff_constC]
      have hcall : instPrefix X (instantiateLevels ls
          (Ann.recCallFunS (.const r lv) pm np nMin (.bvar k) A)) =
          Ann.recCallFunS rec' pre np nMin f
            (instPrefix X (instantiateLevels ls A)) :=
        recCallFunS_imgC X ls (.const r lv) rec' pm pre np nMin
          (piTelE A).1.length (.bvar k) f A (instPrefix X (instantiateLevels ls A))
          (piTelE A).2
          (instOff (piTelE A).1.length X (instantiateLevels ls (piTelE A).2))
          (piTelE A).1
          hrecOff hpm hhead rfl rfl hARtel hidx
      refine ⟨.bvar k ::
        Ann.recCallFunS (.const r lv) pm np nMin (.bvar k) A :: rest, ?_, ?_⟩
      · simp only [iotaArgs, hfun]
        rw [hrest]
        rfl
      · rw [htelR]
        show instPrefix X (instantiateLevels ls (.bvar k)) ::
            instPrefix X (instantiateLevels ls
              (Ann.recCallFunS (.const r lv) pm np nMin (.bvar k) A)) ::
            rest.map (fun a => instPrefix X (instantiateLevels ls a)) =
          f :: (Ann.recCallFunS rec' pre np nMin f
              (instPrefix X (instantiateLevels ls A)) ::
            Ann.rhsArgsS rec' pre np nMin fs' ss'
              (instantiate0 f (instOff 1 X (instantiateLevels ls B))))
        rw [hhead, hcall, hrestmap]


end Rcic.Declarative

namespace Rcic.Declarative.Ann

/-- `preMajorBvars` entries are bvars, so the level map inside the walk's
    `Φ' = instPrefix X ∘ instLevels ls` is invisible: the prelude marker list
    images to the redex's `preMajor` exactly as `preMajorBvars_map_instPrefix`,
    levels or not. -/
theorem preMajorBvars_map_img (pre fields : List (Expr Nat))
    (nparams nMinors nindices : Nat) (ls : List Level)
    (hpre : pre.length = nparams + 1 + nMinors + nindices) :
    (preMajorBvars nparams nMinors nindices fields.length).map
      (fun a => instPrefix (pre ++ fields) (instantiateLevels ls a)) = pre := by
  have hcong : (preMajorBvars nparams nMinors nindices fields.length).map
      (fun a => instPrefix (pre ++ fields) (instantiateLevels ls a)) =
      (preMajorBvars nparams nMinors nindices fields.length).map
      (instPrefix (pre ++ fields)) := by
    apply List.map_congr_left
    intro a ha
    simp only [preMajorBvars, List.mem_map, List.mem_reverse, List.mem_range] at ha
    obtain ⟨i, _, rfl⟩ := ha
    rfl
  rw [hcong, preMajorBvars_map_instPrefix pre fields nparams nMinors nindices hpre]

/-- `fieldBvars` entries are bvars, so the level map is invisible: the field
    markers image to `fields` by `fieldBvars_take_map_instPrefix` at the full
    count. -/
theorem fieldBvars_map_img {pre fields : List (Expr Nat)} (ls : List Level)
    (nparams nMinors nindices : Nat)
    (hpre : pre.length = nparams + 1 + nMinors + nindices) :
    (fieldBvars fields.length).map
      (fun a => instPrefix (pre ++ fields) (instantiateLevels ls a)) = fields := by
  have hpmlen : pre.length =
      nparams + ((pre ++ fields).length - nparams - fields.length) := by
    rw [List.length_append]; omega
  have h := fieldBvars_take_map_instPrefix (args := pre ++ fields)
    (pm := pre) (fs := fields) (np := nparams) (nf := fields.length)
    (i := fields.length) rfl hpmlen rfl (Nat.le_refl _)
  have hbvars : (fieldBvars fields.length).map
      (fun a => instPrefix (pre ++ fields) (instantiateLevels ls a)) =
      (fieldBvars fields.length).map (instPrefix (pre ++ fields)) := by
    apply List.map_congr_left
    intro a ha
    simp only [fieldBvars, List.mem_map, List.mem_reverse, List.mem_range] at ha
    obtain ⟨i, _, rfl⟩ := ha
    rfl
  rw [hbvars]
  have htk : (fieldBvars fields.length).take fields.length =
      fieldBvars fields.length :=
    List.take_of_length_le (Nat.le_of_eq (fieldBvars_length fields.length))
  have hfs : fields.take fields.length = fields :=
    List.take_of_length_le (Nat.le_refl fields.length)
  rwa [htk, hfs] at h

/-- The schema's `recPrefix` of prelude markers images to the redex's
    `recPrefix`: `take` commutes with the pointwise image, then
    `preMajorBvars_map_img`. -/
theorem recPrefix_map_img {E : ResolvedEnv} (w : IotaWitnessS E)
    (ls : List Level) :
    (recPrefix (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length)
        w.nparams w.nMinors).map
      (fun a => instPrefix (w.preMajor ++ w.fields) (instantiateLevels ls a)) =
      recPrefix w.preMajor w.nparams w.nMinors := by
  unfold recPrefix
  rw [List.map_take,
    preMajorBvars_map_img w.preMajor w.fields w.nparams w.nMinors w.nindices ls
      w.hpre]

/-- (e): the witness's `iotaRhsOfS` IS the copy-side ι right-hand side — the
    minor at its slot applied to the `rhsArgsS` walk at `ctorFieldTelInst`
    (= `ctorAfter`, the `applyTel` image, by
    `ctorAfterFieldTel_eq_ctorFieldTelInst`).  Premises: `EnvWfT` (the REL₀
    base bridge's level agreement), the `WalkSuppliesC` derivation (the field
    fragment's canonical fuel reads and the frec arm's no-created-Π facts), and
    the minor lookup.  No `EnvNoFunA`. -/
theorem iotaRhsOfS_eq_rhsArgsS_ctorFieldTelInst {E : ResolvedEnv}
    (hW : EnvWfT E) (w : IotaWitnessS E)
    (hsup : WalkSuppliesC E w.fuel (w.preMajor ++ w.fields) w.ls
      w.nparams w.nMinors (fieldBvars w.fields.length) w.shapes
      (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)))
    {minor : Expr Nat}
    (hm : w.preMajor[w.nparams + 1 + w.ctorIdx]? = some minor) :
    iotaRhsOfS w = foldApps minor
      (rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
        w.fields w.shapes (ctorFieldTelInst w)) := by
  have hrec : (.const w.recRef w.ls : Expr Nat) =
      .const w.recRef ((canonRecLevels w.recMember.arity).map (instLevel w.ls)) :=
    congrArg _ (canonRecLevels_instLevel w.ls w.recMember.arity w.hlsLen).symm
  obtain ⟨args, hargs, hmap⟩ := iotaArgs_agreeC E w.fuel (w.preMajor ++ w.fields)
    w.ls w.recRef (canonRecLevels w.recMember.arity) (.const w.recRef w.ls)
    (preMajorBvars w.nparams w.nMinors w.nindices w.fields.length) w.preMajor
    w.nparams w.nMinors hrec (recPrefix_map_img w w.ls)
    w.shapes (fieldBvars w.fields.length) w.fields
    (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
      (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult))
    (ctorFieldTelInst w) hsup
    (ctorFieldTelInst_eq_schemaLift hW w).symm
    (fieldBvars_map_img w.ls w.nparams w.nMinors w.nindices w.hpre)
  rw [iotaRhsOfS_eq_fold w hargs hm, hmap]

/-- the same at the `applyTel` image: `ctorAfterFieldTel` is what `iotaReductA`'s
    parameter application produces, and it IS `ctorFieldTelInst`. -/
theorem iotaRhsOfS_eq_rhsArgsS_ctorAfter {E : ResolvedEnv}
    (hW : EnvWfT E) (w : IotaWitnessS E)
    (hsup : WalkSuppliesC E w.fuel (w.preMajor ++ w.fields) w.ls
      w.nparams w.nMinors (fieldBvars w.fields.length) w.shapes
      (lift 0 (w.fields.length + 1 + w.nMinors + w.nindices)
        (ctorFieldTelRaw w.nparams w.ctorDoms w.ctorResult)))
    {minor : Expr Nat}
    (hm : w.preMajor[w.nparams + 1 + w.ctorIdx]? = some minor) :
    iotaRhsOfS w = foldApps minor
      (rhsArgsS (.const w.recRef w.ls) w.preMajor w.nparams w.nMinors
        w.fields w.shapes (ctorAfterFieldTel w)) := by
  rw [ctorAfterFieldTel_eq_ctorFieldTelInst w]
  exact iotaRhsOfS_eq_rhsArgsS_ctorFieldTelInst hW w hsup hm

#print axioms iotaRhsOfS_eq_rhsArgsS_ctorFieldTelInst

/-! ## segment 3 (A2b): the union erase direction at a frec firing

`derivedIota_of_iotaFnA` (RcicAnnIotaCorr.lean:695) lands `.ofU` — the legacy
`IotaWitness`, which cannot represent a `.recursive (n+1)` field.  This is the
`.ofUS` sibling: the same `recSpineA`/`iotaGroupA`/`iotaReductA` decomposition
and the same group record, but the witness is `IotaWitnessS` — the shapes go
through `fieldShapesFuel` (gated on `FieldFragList` at the fired constructor's
erased post-parameter domains — `FunRecFrag` at the frec fields), the schema's
`iotaOpenRhs` success through `iotaArgs_agreeC` at the canonical marker frame
(the `WalkSuppliesC` premise — the walk's canonical fuel reads and the frec
arm's no-created-Π image agreements, quantified over BOTH frames: the schema's
canonical levels and the copy's own), stability through the decidable
`iotaWitnessStableB` check, and the schema's scope through an explicit premise —
the Ann route has no typed cell to read it from (the legacy bridge's `hscope`
comes from `hasTyT`; here it is an honest gate, as `WalkSuppliesC` is).  The
erased right-hand side is `rhsArgsA_eraseS` (unconditional — the frec arm erases
to `recCallFunS`), then the (e) corollary lands `iotaRhsOfS` on it.
`closure_claim` stays 0. -/

/-- A2b: a step of the copy's ι landing on a constructor whose erased field
    domains are per-field in the fragment yields union derived-ι evidence on
    the erased endpoints, via the `.ofUS` arm.  The four gates: `FieldFragList`
    (the semantic shape read agrees with the fired one), `WalkSuppliesC` at
    every frame/levels (the walk's canonical reads and no-created-Π images),
    the `iotaWitnessStableB` closure check (env-extension stability), and the
    schema scope certificate.  `EnvNoFunA` is NOT a premise — that is the
    point of the segment. -/
theorem derivedIotaUS_of_iotaFnA_frec {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfA I EA) (hn : EnvNormEraseA EA) (hT : EnvWfT (eraseEnv EA))
    {e e' : ExprA} {s : RecSpineA} {c : Nat} {g : IotaGroupA}
    (hs : recSpineA e = some s) (hc : spineHeadRefA s.major = some c)
    (hg : iotaGroupA EA s.recRef c = some g) (hr : iotaReductA s g = some e')
    (fuel : Nat)
    (hfrag : FieldFragList (eraseEnv EA) fuel g.familyRef g.famM.arity g.nparams
        g.nindices g.nparams
        (((piDomsA g.ctorM.mtypeA).drop g.nparams).map erase))
    (hsup : ∀ (shapes : List FieldShape) (X : List (Expr Nat)) (ls : List Level),
        ctorShapesA g.familyRef g.nparams (g.ctorM.normA.getD g.ctorM.mtypeA) =
            some shapes →
        WalkSuppliesC (eraseEnv EA) fuel X ls g.nparams g.nMinors
          (fieldBvars ((appsSpineA s.major).2.drop g.nparams).length) shapes
          (lift 0 (((appsSpineA s.major).2.drop g.nparams).length + 1 +
            g.nMinors + g.nindices)
            (ctorFieldTelRaw g.nparams ((piDomsA g.ctorM.mtypeA).map erase)
              (erase (piBodyA g.ctorM.mtypeA)))))
    (hstab : iotaWitnessStableB (eraseEnv EA) fuel
        (((piDomsA g.ctorM.mtypeA).drop g.nparams).map erase)
        (fieldBvars ((appsSpineA s.major).2.drop g.nparams).length)
        (lift 0 (((appsSpineA s.major).2.drop g.nparams).length + 1 +
            g.nMinors + g.nindices)
          (ctorFieldTelRaw g.nparams ((piDomsA g.ctorM.mtypeA).map erase)
            (erase (piBodyA g.ctorM.mtypeA)))) = true)
    (hscope : ∀ (shapes : List FieldShape) (schema : Expr Nat),
        ctorShapesA g.familyRef g.nparams (g.ctorM.normA.getD g.ctorM.mtypeA) =
            some shapes →
        iotaOpenRhs (eraseEnv EA) fuel
            (.const s.recRef (canonRecLevels g.recM.arity))
            (.bvar (((appsSpineA s.major).2.drop g.nparams).length + g.nindices +
              (g.nMinors - 1 - g.ctorIdx)))
            (preMajorBvars g.nparams g.nMinors g.nindices
              ((appsSpineA s.major).2.drop g.nparams).length)
            g.nparams g.nMinors shapes
            (fieldBvars ((appsSpineA s.major).2.drop g.nparams).length)
            (lift 0 (((appsSpineA s.major).2.drop g.nparams).length + 1 +
              g.nMinors + g.nindices)
              (ctorFieldTelRaw g.nparams ((piDomsA g.ctorM.mtypeA).map erase)
                (erase (piBodyA g.ctorM.mtypeA)))) = some schema →
        exprClosedAt (g.nparams + 1 + g.nMinors + g.nindices +
            ((appsSpineA s.major).2.drop g.nparams).length) schema = true) :
    Nonempty (DerivedIotaU (eraseEnv EA) (erase e) (erase e')) := by
  obtain ⟨recRef, ls, pre, major⟩ := s
  have hsp := recSpineA_some hs
  simp only at hsp hc hg
  obtain ⟨hrm, hrk, _, _, _, _, _, hlt1, hlt2, _, _, _, _⟩ := iotaGroupA_some hg
  obtain ⟨E₀, f, fm, fv, cs, rec, hrr, hrec, hcls, hfresh, hlay, hpre, _⟩ :=
    envWfA_recGroup hW _ _ hrm hrk
  subst hrr
  have hst : rec.member.mtypeA =
      recTypeA f (canonLevelsA fm.arity) fv.params fv.indices fv.sort
        (rec.elim.motiveLevel fm.arity) (cs.reverse.map GroupCtorA.minorData) :=
    rec.stored
  -- the family is the group's: the recursor type's last domain is headed by `f`
  have hfamf : g.familyRef = f := by
    obtain ⟨D, ls', hD, hhead⟩ := iotaGroupA_lastDom hg
    rw [← hrec, hst, piDomsA_recTypeA_getLast] at hD
    injection hD with hD
    rw [← hD, appsSpineA_majorDom] at hhead
    injection hhead with h1 _
    exact h1.symm
  -- the constructor is the group's `j`-th
  rw [hfamf] at hlt1
  have hj : c - f - 1 < cs.length := by omega
  obtain ⟨gc, hgcj⟩ : ∃ gc, cs.reverse[c - f - 1]? = some gc :=
    ⟨cs.reverse[c - f - 1]'(by rw [List.length_reverse]; exact hj),
      List.getElem?_eq_getElem _⟩
  obtain ⟨href, _⟩ := ref_of_layoutA hlay hgcj
  have hcref : c = gc.ref := by omega
  subst hcref
  have hg' := iotaGroupA_groupRecA hfresh hlay hcls hpre hgcj
  rw [hg'] at hg
  injection hg with hg
  subst hg
  -- the members
  obtain ⟨hmr, hmf, hmc⟩ := members_groupRecA hfresh hlay hpre
  have hmg := hmc hgcj
  -- the normed constructor type erases to the stored one (`EnvNormEraseA`)
  have hNE : erase (gc.member.normA.getD gc.member.mtypeA) =
      erase gc.member.mtypeA := by
    rw [gc.hnorm]
    exact hn _ _ hmg gc.hcls _ gc.hnorm
  -- the reduct's data and the arities
  obtain ⟨shapes, minor, ctorAfter, hshapes, hmin, happ, _, he'⟩ :=
    iotaReductA_inv hr
  obtain ⟨_, _, _, hplen, hlslen, hmlen, har⟩ := iotaReductA_some hr
  simp only at hshapes hmin happ he' hplen hlslen hmlen har
  rw [gc.normA_getD] at hmlen
  have hnpF : fv.params.length = fm.nparamsA := fv.nparams
  have hcp : piCountA gc.member.mtypeA =
      fv.params.length + gc.view.fields.length := by
    rw [gc.view.stored, piCountA_ctorTypeA, gc.view.mirrors_length, hnpF]
  have hcpN : piCountA (ctorTypeA f (canonLevelsA fm.arity) fv.sort
      gc.view.mirrors (gc.view.fields.map FieldA.norm) gc.view.res) =
      fv.params.length + gc.view.fields.length := by
    rw [piCountA_ctorTypeA, gc.view.mirrors_length, List.length_map, hnpF]
  have hrp : piCountA rec.member.mtypeA =
      fv.params.length + 1 + cs.length + fv.indices.length + 1 := by
    rw [hst, piCountA_recTypeA, List.length_map, List.length_reverse]
  -- the major
  obtain ⟨lsC, hmh⟩ := spineHeadRefA_some hc
  have hmaj : major = foldAppsA (.const gc.ref lsC) (appsSpineA major).2 := by
    conv => lhs; rw [← foldAppsA_appsSpineA major]
    rw [hmh]
  have he : e = foldAppsA (.const (f + 1 + cs.length) ls)
      (pre ++ [major]) := by
    conv => lhs; rw [← foldAppsA_appsSpineA e]
    rw [hsp]
  have hmlen' : (appsSpineA major).2.length =
      fv.params.length + gc.view.fields.length := by
    rw [hmlen, hcpN]
  have hfslen : ((appsSpineA major).2.drop fv.params.length).length =
      gc.view.fields.length := by
    rw [List.length_drop, hmlen']; omega
  -- the fired shapes through erasure, then the semantic fuel read via the
  -- `FieldFragList` gate
  have hsE : fieldShapesE f
      (((piDomsA gc.member.mtypeA).drop fv.params.length).map erase) =
      some shapes := by
    have h' := ctorShapesA_of_erase (fam := f) (nparams := fv.params.length) hNE
    show ctorShapesA f fv.params.length gc.member.mtypeA = some shapes
    rw [← h']
    exact hshapes
  have hshapesF : fieldShapesFuel (eraseEnv EA) fuel f fm.arity fv.params.length
      fv.indices.length fv.params.length
      (((piDomsA gc.member.mtypeA).drop fv.params.length).map erase) =
      some shapes :=
    fieldShapesFuel_eq_fieldShapesE _ _ hfrag _ hsE
  -- the canonical-frame walk: the schema's `iotaOpenRhs` success
  have hpmBlen : (preMajorBvars fv.params.length cs.length fv.indices.length
      ((appsSpineA major).2.drop fv.params.length).length).length =
      fv.params.length + 1 + cs.length + fv.indices.length := by
    simp only [preMajorBvars, List.length_map, List.length_reverse,
      List.length_range]
  have hcanonlen : (canonRecLevels rec.member.arity).length =
      rec.member.arity := by
    simp only [canonRecLevels, List.length_map, List.length_range]
  have hpmC : (recPrefix (preMajorBvars fv.params.length cs.length
      fv.indices.length ((appsSpineA major).2.drop fv.params.length).length)
        fv.params.length cs.length).map
      (fun a => instPrefix (preMajorBvars fv.params.length cs.length
          fv.indices.length ((appsSpineA major).2.drop fv.params.length).length ++
        fieldBvars ((appsSpineA major).2.drop fv.params.length).length)
        (instantiateLevels (canonRecLevels rec.member.arity) a)) =
      recPrefix (preMajorBvars fv.params.length cs.length fv.indices.length
        ((appsSpineA major).2.drop fv.params.length).length)
        fv.params.length cs.length := by
    unfold recPrefix
    rw [List.map_take]
    have h := preMajorBvars_map_img
      (preMajorBvars fv.params.length cs.length fv.indices.length
        ((appsSpineA major).2.drop fv.params.length).length)
      (fieldBvars ((appsSpineA major).2.drop fv.params.length).length)
      fv.params.length cs.length fv.indices.length
      (canonRecLevels rec.member.arity) hpmBlen
    rw [fieldBvars_length] at h
    rw [h]
  have hmarkC : (fieldBvars ((appsSpineA major).2.drop fv.params.length).length).map
      (fun a => instPrefix (preMajorBvars fv.params.length cs.length
          fv.indices.length ((appsSpineA major).2.drop fv.params.length).length ++
        fieldBvars ((appsSpineA major).2.drop fv.params.length).length)
        (instantiateLevels (canonRecLevels rec.member.arity) a)) =
      fieldBvars ((appsSpineA major).2.drop fv.params.length).length := by
    have h := fieldBvars_map_img
      (pre := preMajorBvars fv.params.length cs.length fv.indices.length
        ((appsSpineA major).2.drop fv.params.length).length)
      (fields := fieldBvars ((appsSpineA major).2.drop fv.params.length).length)
      (canonRecLevels rec.member.arity)
      fv.params.length cs.length fv.indices.length hpmBlen
    rw [fieldBvars_length] at h
    exact h
  obtain ⟨argsW, hargsW, _⟩ := iotaArgs_agreeC (eraseEnv EA) fuel
      (preMajorBvars fv.params.length cs.length fv.indices.length
          ((appsSpineA major).2.drop fv.params.length).length ++
        fieldBvars ((appsSpineA major).2.drop fv.params.length).length)
      (canonRecLevels rec.member.arity) (f + 1 + cs.length)
      (canonRecLevels rec.member.arity)
      (.const (f + 1 + cs.length) (canonRecLevels rec.member.arity))
      (preMajorBvars fv.params.length cs.length fv.indices.length
        ((appsSpineA major).2.drop fv.params.length).length)
      (preMajorBvars fv.params.length cs.length fv.indices.length
        ((appsSpineA major).2.drop fv.params.length).length)
      fv.params.length cs.length
      (congrArg (Expr.const _) ((canonRecLevels_instLevel
        (canonRecLevels rec.member.arity) rec.member.arity hcanonlen).symm))
      hpmC shapes
      (fieldBvars ((appsSpineA major).2.drop fv.params.length).length)
      (fieldBvars ((appsSpineA major).2.drop fv.params.length).length)
      (lift 0 (((appsSpineA major).2.drop fv.params.length).length + 1 +
          cs.length + fv.indices.length)
        (ctorFieldTelRaw fv.params.length ((piDomsA gc.member.mtypeA).map erase)
          (erase (piBodyA gc.member.mtypeA))))
      (instPrefix (preMajorBvars fv.params.length cs.length fv.indices.length
          ((appsSpineA major).2.drop fv.params.length).length ++
        fieldBvars ((appsSpineA major).2.drop fv.params.length).length)
        (instantiateLevels (canonRecLevels rec.member.arity)
          (lift 0 (((appsSpineA major).2.drop fv.params.length).length + 1 +
            cs.length + fv.indices.length)
            (ctorFieldTelRaw fv.params.length
              ((piDomsA gc.member.mtypeA).map erase)
              (erase (piBodyA gc.member.mtypeA))))))
      (hsup shapes _ _ hshapes) rfl hmarkC
  have hschemaW : iotaOpenRhs (eraseEnv EA) fuel
      (.const (f + 1 + cs.length) (canonRecLevels rec.member.arity))
      (.bvar (((appsSpineA major).2.drop fv.params.length).length +
        fv.indices.length + (cs.length - 1 - (gc.ref - f - 1))))
      (preMajorBvars fv.params.length cs.length fv.indices.length
        ((appsSpineA major).2.drop fv.params.length).length)
      fv.params.length cs.length shapes
      (fieldBvars ((appsSpineA major).2.drop fv.params.length).length)
      (lift 0 (((appsSpineA major).2.drop fv.params.length).length + 1 +
          cs.length + fv.indices.length)
        (ctorFieldTelRaw fv.params.length ((piDomsA gc.member.mtypeA).map erase)
          (erase (piBodyA gc.member.mtypeA)))) =
      some (foldApps (.bvar (((appsSpineA major).2.drop fv.params.length).length +
        fv.indices.length + (cs.length - 1 - (gc.ref - f - 1)))) argsW) := by
    unfold iotaOpenRhs
    rw [hargsW]
    rfl
  -- the witness's `ctorDoms.drop`/`fields.length` phrasings, transported
  have hshapesW : fieldShapesFuel (eraseEnv EA) fuel f fm.arity fv.params.length
      fv.indices.length fv.params.length
      (((piDomsA gc.member.mtypeA).map erase).drop fv.params.length) =
      some shapes := by
    simpa only [List.map_drop] using hshapesF
  have hschemaM : iotaOpenRhs (eraseEnv EA) fuel
      (.const (f + 1 + cs.length) (canonRecLevels rec.member.arity))
      (.bvar ((((appsSpineA major).2.drop fv.params.length).map erase).length +
        fv.indices.length + (cs.length - 1 - (gc.ref - f - 1))))
      (preMajorBvars fv.params.length cs.length fv.indices.length
        (((appsSpineA major).2.drop fv.params.length).map erase).length)
      fv.params.length cs.length shapes
      (fieldBvars (((appsSpineA major).2.drop fv.params.length).map erase).length)
      (lift 0 ((((appsSpineA major).2.drop fv.params.length).map erase).length +
          1 + cs.length + fv.indices.length)
        (ctorFieldTelRaw fv.params.length ((piDomsA gc.member.mtypeA).map erase)
          (erase (piBodyA gc.member.mtypeA)))) =
      some (foldApps (.bvar ((((appsSpineA major).2.drop fv.params.length).map
          erase).length + fv.indices.length + (cs.length - 1 - (gc.ref - f - 1))))
        argsW) := by
    simpa only [List.length_map] using hschemaW
  have hstabT : iotaWitnessStableB (eraseEnv EA) fuel
      (((piDomsA gc.member.mtypeA).map erase).drop fv.params.length)
      (fieldBvars (((appsSpineA major).2.drop fv.params.length).map erase).length)
      (lift 0 ((((appsSpineA major).2.drop fv.params.length).map erase).length +
          1 + cs.length + fv.indices.length)
        (ctorFieldTelRaw fv.params.length ((piDomsA gc.member.mtypeA).map erase)
          (erase (piBodyA gc.member.mtypeA)))) = true := by
    rw [← List.map_drop, List.length_map]
    exact hstab
  -- the witness
  let w : IotaWitnessS (eraseEnv EA) :=
    { recRef := f + 1 + cs.length
      ctorRef := gc.ref
      ls := ls
      lsC := lsC
      recMember := eraseMember rec.member
      ctorMember := eraseMember gc.member
      hrec := by rw [members_eraseEnv, hmr]; rfl
      hctor := by rw [members_eraseEnv, hmg]; rfl
      hrecK := rec.hcls
      hctorK := gc.hcls
      preMajor := pre.map erase
      fields := ((appsSpineA major).2.drop fv.params.length).map erase
      ctorParams := ((appsSpineA major).2.take fv.params.length).map erase
      familyRef := f
      famMember := eraseMember fm
      hfam := by rw [members_eraseEnv, hmf]; rfl
      hfamK := hcls
      nparams := fv.params.length
      nindices := fv.indices.length
      nMinors := cs.length
      ctorIdx := gc.ref - f - 1
      hctorParams := by
        rw [List.length_map, List.length_take, hmlen']; omega
      hnpar := by
        show fv.params.length + _ = piCount (erase gc.member.mtypeA)
        rw [List.length_map, hfslen, piCountA_erase, hcp]
      hnidx := by
        show _ = piCount (erase fm.mtypeA)
        rw [piCountA_erase, piCountA_famView fv]
      hnmin := by
        show _ = piCount (erase rec.member.mtypeA)
        rw [piCountA_erase, hrp]
      hidx := hj
      hctorIdx := href
      hrecIdx := rfl
      hpre := by rw [List.length_map]; rw [hrp] at hplen; omega
      ctorDoms := (piDomsA gc.member.mtypeA).map erase
      ctorResult := erase (piBodyA gc.member.mtypeA)
      hpeel := by
        show peelPis (fv.params.length + _) (erase gc.member.mtypeA) = _
        rw [List.length_map, hfslen, ← hcp]
        exact piDomsA_erase_peelPis _
      hfamApp := by
        rw [gc.view.stored]
        exact isFamilyApp_erase_piBodyA_ctorTypeA _ _ _ _ _ _
          (gc.view.freeOf hfresh.base).2
      recDoms := (piDomsA rec.member.mtypeA).map erase
      recBody := erase (piBodyA rec.member.mtypeA)
      hpeelRec := by
        show peelPis _ (erase rec.member.mtypeA) = _
        rw [← hrp]
        exact piDomsA_erase_peelPis _
      hrecBody := by
        rw [hst, piBodyA_recTypeA, List.length_map, List.length_reverse,
          erase_recBodyA]
      hmajorTy := by
        have hl := piDomsA_recTypeA_getLast f (canonLevelsA fm.arity) fv.params
          fv.indices fv.sort (rec.elim.motiveLevel fm.arity)
          (cs.reverse.map GroupCtorA.minorData)
        rw [← hst, List.getLast?_eq_getElem?, length_piDomsA, hrp] at hl
        rw [List.getElem?_map]
        have hidx' : fv.params.length + 1 + cs.length + fv.indices.length + 1 - 1 =
            fv.params.length + 1 + cs.length + fv.indices.length := by omega
        rw [hidx'] at hl
        rw [hl]
        simp only [List.length_map, List.length_reverse, Option.map_some']
        rw [erase_majorDomA]
        rfl
      hrecClosed := by
        show lift 0 1 (erase rec.member.mtypeA) = erase rec.member.mtypeA
        rw [← erase_liftA, rec.hclT 0]
      hctorClosed := by
        show lift 0 1 (erase gc.member.mtypeA) = erase gc.member.mtypeA
        rw [← erase_liftA, gc.hclT 0]
      hlsLen := hlslen
      fuel := fuel
      shapes := shapes
      hshapes := hshapesW
      schema := foldApps
        (.bvar ((((appsSpineA major).2.drop fv.params.length).map erase).length +
          fv.indices.length + (cs.length - 1 - (gc.ref - f - 1)))) argsW
      hschema := hschemaM
      hstable := fun E' hext =>
        iotaWitnessS_hstable_of_constsMemberFuel hshapesW hschemaM hstabT E' hext
      hschemaScope := by
        simpa only [List.length_map] using hscope shapes _ hshapes hschemaW }
  -- the endpoints
  have hmajE : erase major = foldApps (.const gc.ref lsC)
      (((appsSpineA major).2.take fv.params.length).map erase ++
        ((appsSpineA major).2.drop fv.params.length).map erase) := by
    rw [← List.map_append, List.take_append_drop]
    conv => lhs; rw [hmaj]
    rw [foldAppsA_erase]
    rfl
  have hL : iotaLhsOfS w = erase e := by
    rw [he, foldAppsA_erase, List.map_append, List.map_cons, List.map_nil, hmajE]
    rfl
  -- the reduct: `applyTel`-uniqueness lands `ctorAfterFieldTel` on `erase ctorAfter`
  have hcaE : ctorAfterFieldTel w = erase ctorAfter := by
    have happ' := applyTelA_erase (pre.take fv.params.length)
      (instantiateLevelsA (ls.take gc.member.arity)
        (gc.member.normA.getD gc.member.mtypeA))
    rw [happ] at happ'
    simp only [Option.map_some'] at happ'
    rw [erase_instantiateLevelsA, hNE] at happ'
    have happW : applyTel ((pre.map erase).take fv.params.length)
        (instantiateLevels (ls.take gc.member.arity) (erase gc.member.mtypeA)) =
        some (ctorAfterFieldTel w) :=
      applyTel_eq_ctorAfterFieldTel w
    rw [← List.map_take] at happW
    rw [happW] at happ'
    exact (Option.some.inj happ').symm
  have hm' : (pre.map erase)[fv.params.length + 1 + (gc.ref - f - 1)]? =
      some (erase minor) := by
    rw [List.getElem?_map, hmin]
    rfl
  have hsupCopy : WalkSuppliesC (eraseEnv EA) fuel
      (pre.map erase ++
        ((appsSpineA major).2.drop fv.params.length).map erase) ls
      fv.params.length cs.length
      (fieldBvars (((appsSpineA major).2.drop fv.params.length).map erase).length)
      shapes
      (lift 0 ((((appsSpineA major).2.drop fv.params.length).map erase).length +
          1 + cs.length + fv.indices.length)
        (ctorFieldTelRaw fv.params.length ((piDomsA gc.member.mtypeA).map erase)
          (erase (piBodyA gc.member.mtypeA)))) := by
    simpa only [List.length_map] using hsup shapes _ _ hshapes
  have hR : iotaRhsOfS w = erase e' := by
    rw [he', foldAppsA_erase, rhsArgsA_eraseS]
    rw [← hcaE]
    exact iotaRhsOfS_eq_rhsArgsS_ctorAfter hT w hsupCopy hm'
  exact ⟨hL ▸ hR ▸ DerivedIotaU.ofUS w⟩

/-- The per-firing gate bundle of `derivedIotaUS_of_iotaFnA_frec`, packaged so a
    step-indexed statement can carry it.  Every conjunct is at the fired
    constructor's erased post-parameter domains — `FunRecFrag` rows at the
    `.recursive (n+1)` fields, direct/plain rows at the rest. -/
def FrecFiringGates (EA : ResolvedEnvA) (fuel : Nat) (s : RecSpineA)
    (g : IotaGroupA) : Prop :=
  FieldFragList (eraseEnv EA) fuel g.familyRef g.famM.arity g.nparams g.nindices
      g.nparams (((piDomsA g.ctorM.mtypeA).drop g.nparams).map erase) ∧
  (∀ (shapes : List FieldShape) (X : List (Expr Nat)) (ls : List Level),
    ctorShapesA g.familyRef g.nparams (g.ctorM.normA.getD g.ctorM.mtypeA) =
        some shapes →
    WalkSuppliesC (eraseEnv EA) fuel X ls g.nparams g.nMinors
      (fieldBvars ((appsSpineA s.major).2.drop g.nparams).length) shapes
      (lift 0 (((appsSpineA s.major).2.drop g.nparams).length + 1 +
        g.nMinors + g.nindices)
        (ctorFieldTelRaw g.nparams ((piDomsA g.ctorM.mtypeA).map erase)
          (erase (piBodyA g.ctorM.mtypeA))))) ∧
  iotaWitnessStableB (eraseEnv EA) fuel
      (((piDomsA g.ctorM.mtypeA).drop g.nparams).map erase)
      (fieldBvars ((appsSpineA s.major).2.drop g.nparams).length)
      (lift 0 (((appsSpineA s.major).2.drop g.nparams).length + 1 +
        g.nMinors + g.nindices)
        (ctorFieldTelRaw g.nparams ((piDomsA g.ctorM.mtypeA).map erase)
          (erase (piBodyA g.ctorM.mtypeA)))) = true ∧
  ∀ (shapes : List FieldShape) (schema : Expr Nat),
    ctorShapesA g.familyRef g.nparams (g.ctorM.normA.getD g.ctorM.mtypeA) =
        some shapes →
    iotaOpenRhs (eraseEnv EA) fuel
        (.const s.recRef (canonRecLevels g.recM.arity))
        (.bvar (((appsSpineA s.major).2.drop g.nparams).length + g.nindices +
          (g.nMinors - 1 - g.ctorIdx)))
        (preMajorBvars g.nparams g.nMinors g.nindices
          ((appsSpineA s.major).2.drop g.nparams).length)
        g.nparams g.nMinors shapes
        (fieldBvars ((appsSpineA s.major).2.drop g.nparams).length)
        (lift 0 (((appsSpineA s.major).2.drop g.nparams).length + 1 +
          g.nMinors + g.nindices)
          (ctorFieldTelRaw g.nparams ((piDomsA g.ctorM.mtypeA).map erase)
            (erase (piBodyA g.ctorM.mtypeA)))) = some schema →
    exprClosedAt (g.nparams + 1 + g.nMinors + g.nindices +
      ((appsSpineA s.major).2.drop g.nparams).length) schema = true

/-- The frec erase direction at the union face, step-indexed: on every firing
    whose fired group satisfies `FrecFiringGates`, a step of the copy's ι is a
    union derived-ι step of the erased environment — the `.ofUS` arm.  This is
    the union ι-correspondence's erase face past `EnvNoFunA`: environments whose
    admitted firings all sit inside the frec fragment. -/
theorem iotaErasesTUA_frec {I : IotaIfaceA} {EA : ResolvedEnvA}
    (hW : EnvWfA I EA) (hn : EnvNormEraseA EA) (hT : EnvWfT (eraseEnv EA))
    (fuel : Nat)
    (hgate : ∀ (e : ExprA) (s : RecSpineA) (c : Nat) (g : IotaGroupA),
      recSpineA e = some s → spineHeadRefA s.major = some c →
      iotaGroupA EA s.recRef c = some g → FrecFiringGates EA fuel s g) :
    IotaErasesTUA EA := by
  intro e e' h
  obtain ⟨s, c, g, hs, hc, hg, hr⟩ := iotaFnA_some h
  obtain ⟨hfrag, hsup, hstab, hscope⟩ := hgate e s c g hs hc hg
  exact derivedIotaUS_of_iotaFnA_frec hW hn hT hs hc hg hr fuel
    hfrag hsup hstab hscope

/-- The full union ι-correspondence on a frec-gated environment: `ann` is the
    `EnvNoFunA`-free direction unchanged, `eraseT` goes through the `.ofUS`
    arm. -/
theorem iotaCorrTUA_frec {I : IotaIfaceA} {EA : ResolvedEnvA} (hW : EnvWfA I EA)
    (hn : EnvNormEraseA EA) (hT : EnvWfT (eraseEnv EA)) (fuel : Nat)
    (hCe : EnvCorrEraseCert (eraseEnv EA)) (hCa : EnvCorrAnnCert (eraseEnv EA))
    (hgate : ∀ (e : ExprA) (s : RecSpineA) (c : Nat) (g : IotaGroupA),
      recSpineA e = some s → spineHeadRefA s.major = some c →
      iotaGroupA EA s.recRef c = some g → FrecFiringGates EA fuel s g) :
    IotaCorrTUA EA where
  ann := iotaAnnotatesUA_of_envWfA hW hn hCe hCa
  eraseT := iotaErasesTUA_frec hW hn hT fuel hgate

#print axioms derivedIotaUS_of_iotaFnA_frec
#print axioms iotaErasesTUA_frec
#print axioms iotaCorrTUA_frec

end Rcic.Declarative.Ann
