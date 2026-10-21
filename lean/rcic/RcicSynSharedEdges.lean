import rcic.RcicSynSharedRank
import rcic.RcicSynStepSkeleton

/-!
# Wall B §9–§10 — `BeforeShared` on `P2Query`, the self-edge, representative port edges

`research/rcic/sortrow/BELOWC_MIXED_STEP_AND_LEDGER.md` Part II §9–§10. The
landed `P2Query.rank` / `Before` (`RcicSynBelowCFix`) are untouched; the
shared key is a second rank alongside. `closure_claim` stays 0.

* **A materialised ledger.** `P2Query.sharedRank Aw = (frame suffix length,
  operand atoms, one pending source job per operand)`. It is the honest
  approximation available from a `P2Query`'s materialised operands: the
  frontier is the operands' atoms (never the receipt spine — the difference
  from the landed `localKey`), and sharing between operands is NOT recovered
  (a packet appearing in two operands is counted twice). The identity-based
  frontier of §7 (`Occ` in a `RootForest`, `RcicSynSharedRank`) is the key
  the issuance grammar must eventually compute; `BeforeSharedL` is the order
  for any such ledger.
* **§9.5 the legal self-edge.** For the direct sort typing `s : S_l : S_{l+1}`
  and `c = CvP.sorts l l refl s s`, `q = ES[c]` is an `AssumpPref` public
  root (`Demand.rootEs`), `q.subAt 0 [] = some (cv c)` and `q.site.es c = q`,
  so `Issues.occ_es` gives `Issues q q` (`issues_self_edge`). It is never
  strict under any ledger (`beforeSharedL_irrefl`); strictness is a property
  of the concrete worker port.
* **§10 representative issued-port edges under `BeforeShared`:** `refl_cl`,
  `symm_es`, `trans_es1/2`, `esub_es`, `cctx_es`, `pb_bvar_bitCoh` descend
  by a **frontier** `DMStep` (F(N) / direct packet deletion); `wk_es`,
  `linst_es`, `ewk_es` leave the frontier unchanged and descend only by the
  **work** coordinate (`WorkStep`, a weight drop of the one pending job) —
  these are the edges that need the third coordinate. The A6 `C` edge is the
  abstract two-owner cut `a6_c_edge` (`RcicSynSharedRank`).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the materialised ledger -/

/-- The operands' atoms — no receipt spine. -/
def P2Query.opAtoms (Aw : Nat → Nat) {Eₐ : ResolvedEnv} : P2Query Eₐ → List Nat
  | .es h _ _ _ => h.atoms Aw
  | .cl D₁ D₂ _ _ _ => D₁.atoms Aw ++ D₂.atoms Aw
  | .eut D₁ D₂ _ _ _ => D₁.atoms Aw ++ D₂.atoms Aw
  | .cts h DX _ _ => h.atoms Aw ++ DX.atoms Aw
  | .pb D DT _ _ _ => D.atoms Aw ++ DT.atoms Aw
  | .bitCoh D₁ D₂ _ _ _ => D₁.atoms Aw ++ D₂.atoms Aw
  | .mixed D₁ D₂ _ _ _ => D₁.atoms Aw ++ D₂.atoms Aw
  | .head c _ _ dL dR _ _ _ => c.atoms Aw ++ dL.atoms Aw ++ dR.atoms Aw
  | .slot _ _ _ dSlot _ _ _ _ => dSlot.atoms Aw
  | .observation D _ _ _ _ _ _ _ => D.atoms Aw
  | .obsPair D₁ D₂ _ _ _ => D₁.atoms Aw ++ D₂.atoms Aw

/-- One pending source job per operand: `(atoms, wt)`. -/
def P2Query.jobs (Aw : Nat → Nat) {Eₐ : ResolvedEnv} : P2Query Eₐ → List SourceKey
  | .es h _ _ _ => [(h.atoms Aw, h.wt Aw)]
  | .cl D₁ D₂ _ _ _ => [(D₁.atoms Aw, D₁.wt Aw), (D₂.atoms Aw, D₂.wt Aw)]
  | .eut D₁ D₂ _ _ _ => [(D₁.atoms Aw, D₁.wt Aw), (D₂.atoms Aw, D₂.wt Aw)]
  | .cts h DX _ _ => [(h.atoms Aw, h.wt Aw), (DX.atoms Aw, DX.wt Aw)]
  | .pb D DT _ _ _ => [(D.atoms Aw, D.wt Aw), (DT.atoms Aw, DT.wt Aw)]
  | .bitCoh D₁ D₂ _ _ _ => [(D₁.atoms Aw, D₁.wt Aw), (D₂.atoms Aw, D₂.wt Aw)]
  | .mixed D₁ D₂ _ _ _ => [(D₁.atoms Aw, D₁.wt Aw), (D₂.atoms Aw, D₂.wt Aw)]
  | .head c _ _ dL dR _ _ _ =>
      [(c.atoms Aw, c.wt Aw), (dL.atoms Aw, dL.wt Aw), (dR.atoms Aw, dR.wt Aw)]
  | .slot _ _ _ dSlot _ _ _ _ => [(dSlot.atoms Aw, dSlot.wt Aw)]
  | .observation D _ _ _ _ _ _ _ => [(D.atoms Aw, D.wt Aw)]
  | .obsPair D₁ D₂ _ _ _ => [(D₁.atoms Aw, D₁.wt Aw), (D₂.atoms Aw, D₂.wt Aw)]

/-- The materialised shared key of a query. -/
def P2Query.sharedRank (Aw : Nat → Nat) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) : SharedKey :=
  (q.originalPrefixLength, (q.opAtoms Aw, q.jobs Aw))

/-- `BeforeShared`: the shared key order on the materialised ledger. Added
    alongside the landed `Before`; never replaces it. -/
abbrev BeforeShared (Aw : Nat → Nat) {Eₐ : ResolvedEnv} (q' q : P2Query Eₐ) : Prop :=
  SharedLT (q'.sharedRank Aw) (q.sharedRank Aw)

theorem beforeShared_wf (Aw : Nat → Nat) (Eₐ : ResolvedEnv) :
    WellFounded (BeforeShared (Eₐ := Eₐ) Aw) :=
  InvImage.wf (P2Query.sharedRank Aw) sharedLT_wf

theorem beforeShared_irrefl (Aw : Nat → Nat) {Eₐ : ResolvedEnv} (q : P2Query Eₐ) :
    ¬ BeforeShared Aw q q :=
  sharedLT_irrefl _

/-- Same frame, strictly smaller inner key. -/
theorem beforeShared_of_same_frame (Aw : Nat → Nat) {Eₐ : ResolvedEnv} {q' q : P2Query Eₐ}
    (hp : q'.originalPrefixLength = q.originalPrefixLength)
    (hk : InnerLT (q'.opAtoms Aw, q'.jobs Aw) (q.opAtoms Aw, q.jobs Aw)) :
    BeforeShared Aw q' q := by
  show Prod.Lex (fun p' p : Nat => p' < p) InnerLT
    (q'.originalPrefixLength, (q'.opAtoms Aw, q'.jobs Aw))
    (q.originalPrefixLength, (q.opAtoms Aw, q.jobs Aw))
  rw [hp]
  exact Prod.Lex.right _ hk

/-- Strictly shorter frame. -/
theorem beforeShared_of_lt_frame (Aw : Nat → Nat) {Eₐ : ResolvedEnv} {q' q : P2Query Eₐ}
    (hp : q'.originalPrefixLength < q.originalPrefixLength) : BeforeShared Aw q' q :=
  Prod.Lex.left _ _ hp

/-- A sub-conversion of strictly smaller weight than a rule node is a frontier cut
    (every atom of it lies under the node's one atom). -/
theorem sub_rule_dm (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    (node : CvP E n Γ a b T) (hnode : node.isTransport = false)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {a' b' T' : Expr Nat} (h' : CvP E' n' Γ' a' b' T')
    (hwt : h'.wt Aw < node.wt Aw) : DMStep (h'.atoms Aw) (node.atoms Aw) :=
  dmStep_under_rule Aw node hnode (fun y hy => Nat.lt_of_le_of_lt (CvP.atoms_le Aw h' y hy) hwt)

/-! ## §2 representative issued-port edges under `BeforeShared` -/

section Edges

variable {Eₐ E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {E : ResolvedEnv} {n : Nat} {Γ : LCtx}

/-- `refl_cl` (F(N)): the endpoint `CL` by the landed `below_refl` cut. -/
theorem refl_cl_shared (Aw : Nat → Nat) {a A : Expr Nat} (ht dl dr : TyP E n Γ a A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    BeforeShared Aw (.cl dl dr S σ ρ) (.es (CvP.refl E n Γ a A ht dl dr) S σ ρ) := by
  refine beforeShared_of_same_frame Aw rfl ?_
  simp only [P2Query.opAtoms, P2Query.jobs]
  exact Prod.Lex.left _ _ (below_refl Aw ht dl dr)

/-- `symm_es` (F(N)). -/
theorem symm_es_shared (Aw : Nat → Nat) {a b A : Expr Nat} (h : CvP E n Γ a b A)
    (dl : TyP E n Γ b A) (dr : TyP E n Γ a A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    BeforeShared Aw (.es h S σ ρ) (.es (CvP.symm E n Γ a b A h dl dr) S σ ρ) := by
  refine beforeShared_of_same_frame Aw rfl ?_
  simp only [P2Query.opAtoms, P2Query.jobs]
  exact Prod.Lex.left _ _ (sub_rule_dm Aw (CvP.symm E n Γ a b A h dl dr) rfl h
    (by simp only [CvP.wt]; omega))

/-- `trans_es1` (F(N)). -/
theorem trans_es1_shared (Aw : Nat → Nat) {a b c A : Expr Nat} (h1 : CvP E n Γ a b A)
    (h2 : CvP E n Γ b c A) (dl : TyP E n Γ a A) (dr : TyP E n Γ c A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    BeforeShared Aw (.es h1 S σ ρ) (.es (CvP.trans E n Γ a b c A h1 h2 dl dr) S σ ρ) := by
  refine beforeShared_of_same_frame Aw rfl ?_
  simp only [P2Query.opAtoms, P2Query.jobs]
  exact Prod.Lex.left _ _ (sub_rule_dm Aw (CvP.trans E n Γ a b c A h1 h2 dl dr) rfl h1
    (by simp only [CvP.wt]; omega))

/-- `trans_es2` (F(N)). -/
theorem trans_es2_shared (Aw : Nat → Nat) {a b c A : Expr Nat} (h1 : CvP E n Γ a b A)
    (h2 : CvP E n Γ b c A) (dl : TyP E n Γ a A) (dr : TyP E n Γ c A)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    BeforeShared Aw (.es h2 S σ ρ) (.es (CvP.trans E n Γ a b c A h1 h2 dl dr) S σ ρ) := by
  refine beforeShared_of_same_frame Aw rfl ?_
  simp only [P2Query.opAtoms, P2Query.jobs]
  exact Prod.Lex.left _ _ (sub_rule_dm Aw (CvP.trans E n Γ a b c A h1 h2 dl dr) rfl h2
    (by simp only [CvP.wt]; omega))

/-- **`wk_es` needs the work coordinate (W).** The child's atoms are the parent's
    (a transport adds no atom): the frontier is unchanged and only the one pending
    job's weight drops. -/
theorem wk_es_shared (Aw : Nat → Nat) {a b T : Expr Nat} (h : CvP E n Γ a b T)
    (d : LocalDecl) (c : Nat) (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    BeforeShared Aw (.es h S σ (removeAt ρ c)) (.es (CvP.wk E n Γ a b T d c h) S σ ρ) := by
  refine beforeShared_of_same_frame Aw rfl ?_
  simp only [P2Query.opAtoms, P2Query.jobs, CvP.atoms, CvP.wt]
  exact Prod.Lex.right _ (workStep_of_sourceR (sourceR_of_wt_lt (by omega)) [])

/-- **`linst_es` needs the work coordinate (W).** -/
theorem linst_es_shared (Aw : Nat → Nat) {a' : Nat} {a b T : Expr Nat} {ls : List Level}
    (hls : levelsBounded n ls = true) (hlen : ls.length = a') (h : CvP E a' Γ a b T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    BeforeShared Aw (.es h S (fun l => σ (instLevel ls l)) ρ)
      (.es (CvP.linst E a' n Γ a b T ls hls hlen h) S σ ρ) := by
  refine beforeShared_of_same_frame Aw rfl ?_
  simp only [P2Query.opAtoms, P2Query.jobs, CvP.atoms, CvP.wt]
  exact Prod.Lex.right _ (workStep_of_sourceR (sourceR_of_wt_lt (by omega)) [])

/-- **`ewk_es` needs the work coordinate (W).** -/
theorem ewk_es_shared (Aw : Nat → Nat) {Eₚ : ResolvedEnv} {a b T : Expr Nat}
    (hext : EnvExt Eₚ E) (h : CvP Eₚ n Γ a b T)
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    BeforeShared Aw (.es h S σ ρ) (.es (CvP.ewk Eₚ E n Γ a b T hext h) S σ ρ) := by
  refine beforeShared_of_same_frame Aw rfl ?_
  simp only [P2Query.opAtoms, P2Query.jobs, CvP.atoms, CvP.wt]
  exact Prod.Lex.right _ (workStep_of_sourceR (sourceR_of_wt_lt (by omega)) [])

/-- `esub_es` (direct port): the packet atoms `V`, `W` are deleted — a frontier cut. -/
theorem esub_es_shared (Aw : Nat → Nat) {a b T t v : Expr Nat} {j : Nat} {u : Level}
    (h : CvP E n Γ a b T) (hget : Γ[j]? = some (.assumption t))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    BeforeShared Aw (.es h S σ (insertDisp (binderDisp (levelIsZero (σ u))) j ρ))
      (.es (CvP.esub E n Γ a b T t v j u h hget hv hvT) S σ ρ) := by
  refine beforeShared_of_same_frame Aw rfl ?_
  simp only [P2Query.opAtoms, P2Query.jobs, CvP.atoms]
  exact Prod.Lex.left _ _
    (dmStep_drop_right (dmStep_drop_tail (h.atoms Aw) (TyP.atoms_ne_nil Aw hv)) (hvT.atoms Aw))

/-- `cctx_es` (direct port): the bridge's atoms are deleted — a frontier cut. -/
theorem cctx_es_shared (Aw : Nat → Nat) {a b T A A' : Expr Nat} {u : Level}
    (h : CvP E n (.assumption A :: Γ) a b T) (hA : CvP E n Γ A A' (.sort u))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    BeforeShared Aw (.es h S σ ρ) (.es (CvP.cctx E n Γ a b T A A' u h hA) S σ ρ) := by
  refine beforeShared_of_same_frame Aw rfl ?_
  simp only [P2Query.opAtoms, P2Query.jobs, CvP.atoms]
  exact Prod.Lex.left _ _ (dmStep_drop_tail (h.atoms Aw) (CvP.atoms_ne_nil Aw hA))

/-- `pb_bvar_bitCoh` (§10 PB bvar family): `K + [1 + w(H)] + at(DT) → K + at(H) + at(DT)`. -/
theorem pb_bvar_shared (Aw : Nat → Nat) {i : Nat} {A : Expr Nat} {u s : Level}
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u)) (DT : TyP E n Γ A (.sort s))
    (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level) (ρ : List Disp) :
    BeforeShared Aw (.bitCoh hA DT S σ ρ) (.pb (TyP.bvar E n Γ i A u hlook hA) DT S σ ρ) := by
  refine beforeShared_of_same_frame Aw rfl ?_
  simp only [P2Query.opAtoms, P2Query.jobs, TyP.atoms, List.cons_append, List.nil_append]
  exact Prod.Lex.left _ _ (dmStep_of_below fun y hy =>
    Nat.lt_of_le_of_lt (TyP.atoms_le Aw hA y hy) (by simp only [TyP.wt]; omega))

end Edges

/-! ## §3 the §9.5 legal self-edge -/

section SelfEdge

variable {Eₐ E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} (E : ResolvedEnv) (n : Nat) (Γ : LCtx)

/-- The direct sort typing `s : S_l : S_{l+1}`. -/
def sortRow (l : Level) : TyP E n Γ (.sort l) (.sort (.succ l)) :=
  TyP.sort E n Γ l (.succ l) (eqN_refl _)

/-- `c = CvP.sorts l l refl s s`. -/
def sortsRefl (l : Level) : CvP E n Γ (.sort l) (.sort l) (.sort (.succ l)) :=
  CvP.sorts E n Γ l l (eqN_refl l) (sortRow E n Γ l) (sortRow E n Γ l)

/-- Active weight 3. -/
theorem sortsRefl_wt (Aw : Nat → Nat) (l : Level) : (sortsRefl E n Γ l).wt Aw = 3 := by
  simp only [sortsRefl, sortRow, CvP.wt, TyP.wt]

theorem sortsRefl_ap (l : Level) : (sortsRefl E n Γ l).AssumpPref := by
  simp only [sortsRefl, sortRow, CvP.AssumpPref, TyP.AssumpPref, and_self]

/-- `q = ES[c]` is an `AssumpPref` public root. -/
theorem sortsRefl_root_demanded (l : Level) (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level)
    (hσ : LevelHom σ) : Demand (.es (sortsRefl E n Γ l) S σ (S.can σ)) :=
  Demand.rootEs _ (sortsRefl_ap E n Γ l) S σ hσ

/-- **§9.5 the legal self-edge.** `q.subAt 0 [] = some (cv c)` and `q.site.es c = q`,
    so `Issues.occ_es` gives `Issues q q`. -/
theorem issues_self_edge (l : Level) (S : ScopedCtx Eₐ E₀ n₀ Γ₀) (σ : Level → Level)
    (ρ : List Disp) :
    Issues (.es (sortsRefl E n Γ l) S σ ρ) (.es (sortsRefl E n Γ l) S σ ρ) :=
  Issues.occ_es (q := .es (sortsRefl E n Γ l) S σ ρ) (k := 0) (p := [])
    (h := sortsRefl E n Γ l) rfl (sortsRefl_ap E n Γ l)

/-- The self-edge is never strict (under the materialised ledger, and by
    `beforeSharedL_irrefl` under any ledger). -/
theorem self_edge_not_strict (Aw : Nat → Nat) (l : Level) (S : ScopedCtx Eₐ E₀ n₀ Γ₀)
    (σ : Level → Level) (ρ : List Disp) :
    ¬ BeforeShared Aw (.es (sortsRefl E n Γ l) S σ ρ) (.es (sortsRefl E n Γ l) S σ ρ) :=
  beforeShared_irrefl Aw _

end SelfEdge

end Rcic.Syn

#print axioms Rcic.Syn.beforeShared_wf
#print axioms Rcic.Syn.beforeShared_irrefl
#print axioms Rcic.Syn.refl_cl_shared
#print axioms Rcic.Syn.symm_es_shared
#print axioms Rcic.Syn.trans_es1_shared
#print axioms Rcic.Syn.trans_es2_shared
#print axioms Rcic.Syn.wk_es_shared
#print axioms Rcic.Syn.linst_es_shared
#print axioms Rcic.Syn.ewk_es_shared
#print axioms Rcic.Syn.esub_es_shared
#print axioms Rcic.Syn.cctx_es_shared
#print axioms Rcic.Syn.pb_bvar_shared
#print axioms Rcic.Syn.sortsRefl_root_demanded
#print axioms Rcic.Syn.issues_self_edge
#print axioms Rcic.Syn.self_edge_not_strict
