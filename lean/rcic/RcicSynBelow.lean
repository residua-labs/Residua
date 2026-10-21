import rcic.RcicSynES

/-!
# Syntactic sortRow, build step 3f — rule-node call measures

`research/rcic/semantic/S3_ES_ARMS.md` §8. `es_transports` folds the five transports.
A rule node (`isTransport = false`) is one atom (`CvP.atoms_rule`). Every recursive
call the mutual induction makes from that node is a `DMStep` below it (`S1` §3.4,
kind (a)):

* `ES` on a premise conversion, whose atoms all lie under the node's weight;
* `CL` on a pair of typings, whose atom lists are concatenated. Copies stay a
  step, which is why the measure is a multiset and not a sum.

`Prod.Lex.left` (`lex_of_dm`) turns each `DMStep` into a `lexDM_wf` step. The
second component is not consulted. `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- Coherence of two typings of one term: their erasures are convertible in `E ∪ ≈`.
    The types may differ. Same context, same pending `σ` and `ρ`. -/
def CL (tbl : List CRule) (σ : Level → Level) (ρ : List Disp) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {e T₁ T₂ : Expr Nat} (D₁ : TyP E n Γ e T₁) (D₂ : TyP E n Γ e T₂) : Prop :=
  ConvMod (EStep tbl) LvlEq (D₁.eps σ ρ) (D₂.eps σ ρ)

/-- A rule node is one atom, its weight. Transports are not rule nodes. -/
theorem CvP.atoms_rule (Aw : Nat → Nat) : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} → (h : CvP E n Γ a b T) → h.isTransport = false →
    h.atoms Aw = [h.wt Aw]
  | _, _, _, _, _, _, .refl .., _ => rfl
  | _, _, _, _, _, _, .symm .., _ => rfl
  | _, _, _, _, _, _, .trans .., _ => rfl
  | _, _, _, _, _, _, .beta .., _ => rfl
  | _, _, _, _, _, _, .zeta .., _ => rfl
  | _, _, _, _, _, _, .zetaLocal .., _ => rfl
  | _, _, _, _, _, _, .delta .., _ => rfl
  | _, _, _, _, _, _, .iota .., _ => rfl
  | _, _, _, _, _, _, .lit .., _ => rfl
  | _, _, _, _, _, _, .app .., _ => rfl
  | _, _, _, _, _, _, .lam .., _ => rfl
  | _, _, _, _, _, _, .pi .., _ => rfl
  | _, _, _, _, _, _, .letE .., _ => rfl
  | _, _, _, _, _, _, .sorts .., _ => rfl
  | _, _, _, _, _, _, .consts .., _ => rfl
  | _, _, _, _, _, _, .eta .., _ => rfl
  | _, _, _, _, _, _, .irr .., _ => rfl
  | _, _, _, _, _, _, .tyConv .., _ => rfl
  | _, _, _, _, _, _, .fsub .., _ => rfl
  | _, _, _, _, _, _, .wk .., ht => nomatch ht
  | _, _, _, _, _, _, .esub .., ht => nomatch ht
  | _, _, _, _, _, _, .linst .., ht => nomatch ht
  | _, _, _, _, _, _, .ewk .., ht => nomatch ht
  | _, _, _, _, _, _, .cctx .., ht => nomatch ht

/-- A lighter typing is a `DMStep` below a rule node. -/
theorem dmStep_ty_below (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CvP E n Γ a b T) (ht : h.isTransport = false)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {e T' : Expr Nat}
    (D : TyP E' n' Γ' e T') (hw : D.wt Aw < h.wt Aw) :
    DMStep (D.atoms Aw) (h.atoms Aw) := by
  rw [CvP.atoms_rule Aw h ht, ← List.append_nil (D.atoms Aw)]
  exact dmStep_of_below (atoms_lt_of_wt_lt Aw D hw)

/-- A lighter conversion is a `DMStep` below a rule node. -/
theorem dmStep_cv_below (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CvP E n Γ a b T) (ht : h.isTransport = false)
    {E' : ResolvedEnv} {n' : Nat} {Γ' : LCtx} {a' b' T' : Expr Nat}
    (k : CvP E' n' Γ' a' b' T') (hw : k.wt Aw < h.wt Aw) :
    DMStep (k.atoms Aw) (h.atoms Aw) := by
  rw [CvP.atoms_rule Aw h ht, ← List.append_nil (k.atoms Aw)]
  exact dmStep_of_below (cvp_atoms_lt_of_wt_lt Aw k hw)

/-- A `CL` call on two lighter typings. Both atom lists sit under the one removed atom. -/
theorem dmStep_pair_below (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CvP E n Γ a b T) (ht : h.isTransport = false)
    {E₁ : ResolvedEnv} {n₁ : Nat} {Γ₁ : LCtx} {e₁ T₁ : Expr Nat}
    (D₁ : TyP E₁ n₁ Γ₁ e₁ T₁)
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    (h₁ : D₁.wt Aw < h.wt Aw) (h₂ : D₂.wt Aw < h.wt Aw) :
    DMStep (D₁.atoms Aw ++ D₂.atoms Aw) (h.atoms Aw) := by
  rw [CvP.atoms_rule Aw h ht, ← List.append_nil (D₁.atoms Aw ++ D₂.atoms Aw)]
  refine dmStep_of_below ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact atoms_lt_of_wt_lt Aw D₁ h₁ y hy
  · exact atoms_lt_of_wt_lt Aw D₂ h₂ y hy

/-- A multiset step is a `lexDM_wf` step at any summed weights. -/
theorem lex_of_dm {M' M : List Nat} {k k' : Nat} (h : DMStep M' M) :
    Prod.Lex DMStep (fun x y : Nat => x < y) (M', k') (M, k) :=
  Prod.Lex.left _ _ h

/-- Any list of atoms already known to lie under a rule node's weight is a `DMStep`. -/
theorem dmStep_under_rule (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b T : Expr Nat} (h : CvP E n Γ a b T) (ht : h.isTransport = false)
    {Y : List Nat} (hY : ∀ y ∈ Y, y < h.wt Aw) : DMStep Y (h.atoms Aw) := by
  rw [CvP.atoms_rule Aw h ht, ← List.append_nil Y]
  exact dmStep_of_below hY

/-! ## §1 structural arms: `refl`, `symm`, `trans`, `tyConv` -/

/-- `es_refl` calls `CL(dl, dr)`. -/
theorem below_refl (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a A : Expr Nat}
    (ht : TyP E n Γ a A) (dl dr : TyP E n Γ a A) :
    let hnode := CvP.refl E n Γ a A ht dl dr
    DMStep (dl.atoms Aw ++ dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.refl E n Γ a A ht dl dr
  have htr : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact dmStep_pair_below Aw hnode htr dl dr hwl hwr

/-- `es_symm` calls `ES(h)`, `CL(dl, h.dr)` and `CL(h.dl, dr)`. -/
theorem below_symm (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b A : Expr Nat}
    (h : CvP E n Γ a b A) (dl : TyP E n Γ b A) (dr : TyP E n Γ a A) :
    let hnode := CvP.symm E n Γ a b A h dl dr
    DMStep (h.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dl.atoms Aw ++ h.dr.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (h.dl.atoms Aw ++ dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.symm E n Γ a b A h dl dr
  have htr : hnode.isTransport = false := rfl
  have hw : h.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwdr : h.dr.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dr_lt Aw h
    simp only [CvP.wt]; omega
  have hwdl : h.dl.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dl_lt Aw h
    simp only [CvP.wt]; omega
  exact ⟨dmStep_cv_below Aw hnode htr h hw,
    dmStep_pair_below Aw hnode htr dl h.dr hwl hwdr,
    dmStep_pair_below Aw hnode htr h.dl dr hwdl hwr⟩

/-- `es_trans` calls `ES(h1)`, `ES(h2)`, `CL(dl, h1.dl)`, `CL(h1.dr, h2.dl)`, `CL(h2.dr, dr)`. -/
theorem below_trans (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b c A : Expr Nat} (h1 : CvP E n Γ a b A) (h2 : CvP E n Γ b c A)
    (dl : TyP E n Γ a A) (dr : TyP E n Γ c A) :
    let hnode := CvP.trans E n Γ a b c A h1 h2 dl dr
    DMStep (h1.atoms Aw) (hnode.atoms Aw) ∧ DMStep (h2.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dl.atoms Aw ++ h1.dl.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (h1.dr.atoms Aw ++ h2.dl.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (h2.dr.atoms Aw ++ dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.trans E n Γ a b c A h1 h2 dl dr
  have htr : hnode.isTransport = false := rfl
  have hw1 : h1.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hw2 : h2.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hw1l : h1.dl.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dl_lt Aw h1
    simp only [CvP.wt]; omega
  have hw1r : h1.dr.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dr_lt Aw h1
    simp only [CvP.wt]; omega
  have hw2l : h2.dl.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dl_lt Aw h2
    simp only [CvP.wt]; omega
  have hw2r : h2.dr.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dr_lt Aw h2
    simp only [CvP.wt]; omega
  exact ⟨dmStep_cv_below Aw hnode htr h1 hw1, dmStep_cv_below Aw hnode htr h2 hw2,
    dmStep_pair_below Aw hnode htr dl h1.dl hwl hw1l,
    dmStep_pair_below Aw hnode htr h1.dr h2.dl hw1r hw2l,
    dmStep_pair_below Aw hnode htr h2.dr dr hw2r hwr⟩

/-- `es_tyConv` calls `ES(h)`, `CL(dl, h.dl)` and `CL(h.dr, dr)`. The type conversion is not a call. -/
theorem below_tyConv (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {a b A A' : Expr Nat} {u : Level} (h : CvP E n Γ a b A) (hA : CvP E n Γ A A' (.sort u))
    (dl : TyP E n Γ a A') (dr : TyP E n Γ b A') :
    let hnode := CvP.tyConv E n Γ a b A A' u h hA dl dr
    DMStep (h.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dl.atoms Aw ++ h.dl.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (h.dr.atoms Aw ++ dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.tyConv E n Γ a b A A' u h hA dl dr
  have htr : hnode.isTransport = false := rfl
  have hw : h.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwdl : h.dl.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dl_lt Aw h
    simp only [CvP.wt]; omega
  have hwdr : h.dr.wt Aw < hnode.wt Aw := by
    have := CvP.wt_dr_lt Aw h
    simp only [CvP.wt]; omega
  exact ⟨dmStep_cv_below Aw hnode htr h hw,
    dmStep_pair_below Aw hnode htr dl h.dl hwl hwdl,
    dmStep_pair_below Aw hnode htr h.dr dr hwdr hwr⟩

/-! ## §2 proof and level arms: `irr`, `sorts`, `consts` -/

/-- `es_irr_star` is PB on the two endpoints. Each endpoint is read with the Prop's sort typing. -/
theorem below_irr (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {P p q : Expr Nat}
    (hP : TyP E n Γ P (.sort .zero)) (hp : TyP E n Γ p P) (hq : TyP E n Γ q P)
    (dl : TyP E n Γ p P) (dr : TyP E n Γ q P) :
    let hnode := CvP.irr E n Γ P p q hP hp hq dl dr
    DMStep (dl.atoms Aw ++ hP.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dr.atoms Aw ++ hP.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (hp.atoms Aw) (hnode.atoms Aw) ∧ DMStep (hq.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.irr E n Γ P p q hP hp hq dl dr
  have htr : hnode.isTransport = false := rfl
  have hwP : hP.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwp : hp.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwq : hq.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_pair_below Aw hnode htr dl hP hwl hwP,
    dmStep_pair_below Aw hnode htr dr hP hwr hwP,
    dmStep_ty_below Aw hnode htr hp hwp, dmStep_ty_below Aw hnode htr hq hwq⟩

/-- `es_sorts` reads the two endpoint typings. -/
theorem below_sorts (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {l₁ l₂ : Level}
    (h : eqN l₁ l₂) (dl : TyP E n Γ (.sort l₁) (.sort (.succ l₁)))
    (dr : TyP E n Γ (.sort l₂) (.sort (.succ l₁))) :
    let hnode := CvP.sorts E n Γ l₁ l₂ h dl dr
    DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.sorts E n Γ l₁ l₂ h dl dr
  have htr : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_ty_below Aw hnode htr dl hwl, dmStep_ty_below Aw hnode htr dr hwr⟩

/-- `es_consts` reads the two endpoint typings. -/
theorem below_consts (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls ls' : List Level} {m : CheckedMember} (hres : E.members r = some m)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hwf' : levelsBounded n ls' = true) (h : eqNList ls ls')
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (.const r ls') (instantiateLevels ls m.mtype)) :
    let hnode := CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr
    DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.consts E n Γ r ls ls' m hres hlen hwf hwf' h dl dr
  have htr : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_ty_below Aw hnode htr dl hwl, dmStep_ty_below Aw hnode htr dr hwr⟩

/-! ## §3 root arms: `beta`, `zeta`, `zetaLocal`, `delta`, `iota`, `lit`, `eta` -/

/-- `es_beta` reads the binder, the body, the argument and both endpoints.
    The combined list is S1 §3.4's one call `CL` of the explicit substitution against `dr`:
    the body's atoms, the argument's, the domain's, and `dr`'s. -/
theorem below_beta (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body arg B : Expr Nat} {u : Level} (hA : TyP E n Γ A (.sort u))
    (hbody : TyP E n (.assumption A :: Γ) body B) (harg : TyP E n Γ arg A)
    (dl : TyP E n Γ (.app (.lam A body) arg) (instantiate0 arg B))
    (dr : TyP E n Γ (instantiate0 arg body) (instantiate0 arg B)) :
    let hnode := CvP.beta E n Γ A body arg B u hA hbody harg dl dr
    DMStep (hbody.atoms Aw) (hnode.atoms Aw) ∧ DMStep (harg.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (hA.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dr.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (hbody.atoms Aw ++ harg.atoms Aw ++ hA.atoms Aw ++ dr.atoms Aw)
        (hnode.atoms Aw) := by
  let hnode := CvP.beta E n Γ A body arg B u hA hbody harg dl dr
  have htr : hnode.isTransport = false := rfl
  have hwA : hA.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwb : hbody.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwa : harg.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  refine ⟨dmStep_ty_below Aw hnode htr hbody hwb, dmStep_ty_below Aw hnode htr harg hwa,
    dmStep_ty_below Aw hnode htr hA hwA, dmStep_ty_below Aw hnode htr dl hwl,
    dmStep_ty_below Aw hnode htr dr hwr, ?_⟩
  refine dmStep_under_rule Aw hnode htr ?_
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · rcases List.mem_append.mp hy with hy | hy
    · rcases List.mem_append.mp hy with hy | hy
      · exact atoms_lt_of_wt_lt Aw hbody hwb y hy
      · exact atoms_lt_of_wt_lt Aw harg hwa y hy
    · exact atoms_lt_of_wt_lt Aw hA hwA y hy
  · exact atoms_lt_of_wt_lt Aw dr hwr y hy

/-- `es_zeta` reads the domain, the value, the body and both endpoints. -/
theorem below_zeta (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level} (hA : TyP E n Γ A (.sort u))
    (hv : TyP E n Γ value A) (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B)) :
    let hnode := CvP.zeta E n Γ A value body B u hA hv hb dl dr
    DMStep (hA.atoms Aw) (hnode.atoms Aw) ∧ DMStep (hv.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (hb.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.zeta E n Γ A value body B u hA hv hb dl dr
  have htr : hnode.isTransport = false := rfl
  have hwA : hA.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwv : hv.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwb : hb.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_ty_below Aw hnode htr hA hwA, dmStep_ty_below Aw hnode htr hv hwv,
    dmStep_ty_below Aw hnode htr hb hwb, dmStep_ty_below Aw hnode htr dl hwl,
    dmStep_ty_below Aw hnode htr dr hwr⟩

/-- `es_zetaLocal`'s coherence reads the variable typing, the value typing and `hv`. -/
theorem below_zetaLocal (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat}
    {A v : Expr Nat} (hval : lookupValue Γ i = some v) (hty : lookupType Γ i = some A)
    (hv : TyP E n Γ v A) (dl : TyP E n Γ (.bvar i) A) (dr : TyP E n Γ v A) :
    let hnode := CvP.zetaLocal E n Γ i A v hval hty hv dl dr
    DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dr.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (hv.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dr.atoms Aw ++ hv.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.zetaLocal E n Γ i A v hval hty hv dl dr
  have htr : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwv : hv.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_ty_below Aw hnode htr dl hwl, dmStep_ty_below Aw hnode htr dr hwr,
    dmStep_ty_below Aw hnode htr hv hwv, dmStep_pair_below Aw hnode htr dr hv hwr hwv⟩

/-- `es_delta` reads the constant's endpoint, the body's endpoint and the body typing. -/
theorem below_delta (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat}
    {ls : List Level} {m : CheckedMember} {b : Expr Nat} (hres : E.members r = some m)
    (hbody : m.body = some b) (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype)) :
    let hnode := CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr
    DMStep (hb.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr
  have htr : hnode.isTransport = false := rfl
  have hwb : hb.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_ty_below Aw hnode htr hb hwb, dmStep_ty_below Aw hnode htr dl hwl,
    dmStep_ty_below Aw hnode htr dr hwr⟩

/-- `es_iota` reads both endpoints and both premise typings of the derived equation. -/
theorem below_iota (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {lhs rhs T : Expr Nat} (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T)
    (hrhs : TyP E n Γ rhs T) (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T) :
    let hnode := CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr
    DMStep (hlhs.atoms Aw) (hnode.atoms Aw) ∧ DMStep (hrhs.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dr.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dl.atoms Aw ++ hlhs.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (hrhs.atoms Aw ++ dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr
  have htr : hnode.isTransport = false := rfl
  have hwlhs : hlhs.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwrhs : hrhs.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_ty_below Aw hnode htr hlhs hwlhs, dmStep_ty_below Aw hnode htr hrhs hwrhs,
    dmStep_ty_below Aw hnode htr dl hwl, dmStep_ty_below Aw hnode htr dr hwr,
    dmStep_pair_below Aw hnode htr dl hlhs hwl hwlhs,
    dmStep_pair_below Aw hnode htr hrhs dr hwrhs hwr⟩

/-- `es_lit` reads the literal's endpoint, the expansion's typing and the expansion's endpoint.
    `hexp` and `dr` type the same term. -/
theorem below_lit (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {t : Nat}
    {exp T : Expr Nat} (h : LiteralExpansion t exp) (hexp : TyP E n Γ exp T)
    (dl : TyP E n Γ (.lit t) T) (dr : TyP E n Γ exp T) :
    let hnode := CvP.lit E n Γ t exp T h hexp dl dr
    DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧ DMStep (hexp.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dr.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (hexp.atoms Aw ++ dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.lit E n Γ t exp T h hexp dl dr
  have htr : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwe : hexp.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_ty_below Aw hnode htr dl hwl, dmStep_ty_below Aw hnode htr hexp hwe,
    dmStep_ty_below Aw hnode htr dr hwr, dmStep_pair_below Aw hnode htr hexp dr hwe hwr⟩

/-- `es_eta` reads the function's typing and both endpoints. -/
theorem below_eta (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B)) :
    let hnode := CvP.eta E n Γ f A B h dl dr
    DMStep (h.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dr.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dr.atoms Aw ++ h.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.eta E n Γ f A B h dl dr
  have htr : hnode.isTransport = false := rfl
  have hw : h.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_ty_below Aw hnode htr h hw, dmStep_ty_below Aw hnode htr dl hwl,
    dmStep_ty_below Aw hnode htr dr hwr, dmStep_pair_below Aw hnode htr dr h hwr hw⟩

/-! ## §4 congruence and functionality -/

/-- `es_app` reads both premise conversions and both endpoints. -/
theorem below_app (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f g a b A B : Expr Nat} (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B)) :
    let hnode := CvP.app E n Γ f g a b A B h1 h2 dl dr
    DMStep (h1.atoms Aw) (hnode.atoms Aw) ∧ DMStep (h2.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.app E n Γ f g a b A B h1 h2 dl dr
  have htr : hnode.isTransport = false := rfl
  have hw1 : h1.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hw2 : h2.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_cv_below Aw hnode htr h1 hw1, dmStep_cv_below Aw hnode htr h2 hw2,
    dmStep_ty_below Aw hnode htr dl hwl, dmStep_ty_below Aw hnode htr dr hwr⟩

/-- `es_lam` reads the domain conversion, the body conversion and both endpoints. -/
theorem below_lam (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' b b' B : Expr Nat} {u : Level} (hA : CvP E n Γ A A' (.sort u))
    (hb : CvP E n (.assumption A :: Γ) b b' B)
    (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B)) :
    let hnode := CvP.lam E n Γ A A' b b' B u hA hb dl dr
    DMStep (hA.atoms Aw) (hnode.atoms Aw) ∧ DMStep (hb.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.lam E n Γ A A' b b' B u hA hb dl dr
  have htr : hnode.isTransport = false := rfl
  have hwA : hA.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwb : hb.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_cv_below Aw hnode htr hA hwA, dmStep_cv_below Aw hnode htr hb hwb,
    dmStep_ty_below Aw hnode htr dl hwl, dmStep_ty_below Aw hnode htr dr hwr⟩

/-- `es_pi` reads both premise conversions and both endpoints. -/
theorem below_pi (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' B B' : Expr Nat} {u v : Level} (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v))) :
    let hnode := CvP.pi E n Γ A A' B B' u v hA hB dl dr
    DMStep (hA.atoms Aw) (hnode.atoms Aw) ∧ DMStep (hB.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.pi E n Γ A A' B B' u v hA hB dl dr
  have htr : hnode.isTransport = false := rfl
  have hwA : hA.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwB : hB.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_cv_below Aw hnode htr hA hwA, dmStep_cv_below Aw hnode htr hB hwB,
    dmStep_ty_below Aw hnode htr dl hwl, dmStep_ty_below Aw hnode htr dr hwr⟩

/-- `es_letE` reads the domain, the value, the body and both endpoints. -/
theorem below_letE (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level} (hA : CvP E n Γ A A' (.sort u))
    (hv : CvP E n Γ v v' A) (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)) :
    let hnode := CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr
    DMStep (hA.atoms Aw) (hnode.atoms Aw) ∧ DMStep (hv.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (hb.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr
  have htr : hnode.isTransport = false := rfl
  have hwA : hA.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwv : hv.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwb : hb.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨dmStep_cv_below Aw hnode htr hA hwA, dmStep_cv_below Aw hnode htr hv hwv,
    dmStep_cv_below Aw hnode htr hb hwb, dmStep_ty_below Aw hnode htr dl hwl,
    dmStep_ty_below Aw hnode htr dr hwr⟩

/-- `es_fsub` reads the body, the domain, the conversion and both endpoints.
    `fsub_child_below` already covers the body, the conversion and the endpoints;
    the domain typing is the remaining call. -/
theorem below_fsub (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A B S a b : Expr Nat} {u : Level}
    (hB : TyP E n (.assumption A :: Γ) B S) (hA : TyP E n Γ A (.sort u))
    (hab : CvP E n Γ a b A)
    (dl : TyP E n Γ (instantiate0 a B) (instantiate0 a S))
    (dr : TyP E n Γ (instantiate0 b B) (instantiate0 a S)) :
    let hnode := CvP.fsub E n Γ A B S a b u hB hA hab dl dr
    DMStep (hB.atoms Aw) (hnode.atoms Aw) ∧ DMStep (hA.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (hab.atoms Aw) (hnode.atoms Aw) ∧ DMStep (dl.atoms Aw) (hnode.atoms Aw) ∧
      DMStep (dr.atoms Aw) (hnode.atoms Aw) := by
  let hnode := CvP.fsub E n Γ A B S a b u hB hA hab dl dr
  have kids := fsub_child_below Aw hB hA hab dl dr
  have htr : hnode.isTransport = false := rfl
  have hwA : hA.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  exact ⟨kids.1, dmStep_ty_below Aw hnode htr hA hwA, kids.2.1, kids.2.2.1, kids.2.2.2⟩

end Rcic.Syn

#print axioms Rcic.Syn.CvP.atoms_rule
#print axioms Rcic.Syn.dmStep_ty_below
#print axioms Rcic.Syn.dmStep_cv_below
#print axioms Rcic.Syn.dmStep_pair_below
#print axioms Rcic.Syn.lex_of_dm
#print axioms Rcic.Syn.dmStep_under_rule
#print axioms Rcic.Syn.below_refl
#print axioms Rcic.Syn.below_symm
#print axioms Rcic.Syn.below_trans
#print axioms Rcic.Syn.below_tyConv
#print axioms Rcic.Syn.below_irr
#print axioms Rcic.Syn.below_sorts
#print axioms Rcic.Syn.below_consts
#print axioms Rcic.Syn.below_beta
#print axioms Rcic.Syn.below_zeta
#print axioms Rcic.Syn.below_zetaLocal
#print axioms Rcic.Syn.below_delta
#print axioms Rcic.Syn.below_iota
#print axioms Rcic.Syn.below_lit
#print axioms Rcic.Syn.below_eta
#print axioms Rcic.Syn.below_app
#print axioms Rcic.Syn.below_lam
#print axioms Rcic.Syn.below_pi
#print axioms Rcic.Syn.below_letE
#print axioms Rcic.Syn.below_fsub
