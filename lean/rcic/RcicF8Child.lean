import Lean
import rcic.RcicParRedTSR
import rcic.RcicSynOrder

/-!
# RcicF8Child — piRow O-M carrier part 1: atoms, weights, premises, DM step

Carrier part 1 for LIFT♮'s measure obligations O-M1..O-M3
(`research/rcic/semantic/S2_OM_OBLIGATIONS.md` on PR #6792, cc ruling
14:49Z). The atoms of the syntactic multiset are the plain judgments —
`HasTyT`, `ConvT`, `TyConvT`, `ParRedT` at the `PEqLeafT` leaf, and
`PEqT` — weighted by the EXISTING size counters of `RcicParRedTSR`
(`hasTyTSize`, `convTSize`, `tyConvTSize`, `parRedTSize` at
`peqLeafTSize` — i.e. F8's `stepSize` — and `peqTSize`); no new counter
is introduced.

`Jd.children` is the immediate-premise relation: every judgment-valued
field of every constructor contributes a `Jd` (for `ParRedT.peq` the
`PEqLeafT` field contributes `.pe h.1`, `.ty h.2.1`, `.ty h.2.2`).
Non-judgment payload — `Level`, `eqN`, `DerivedIota`/`DerivedIotaU`,
`IotaWitness`, lookup equations, `EliminationSelection`, … — is not a
child. `Child` is membership in `children`; `SubOf`/`SubEq` are the
strict and reflexive sub-derivation closures; `dm_of_strictLeaves` is
the core Dershowitz–Manna step over `RcicSynOrder.DMStep`, the single
owner of the order — no well-foundedness is reproved here and
`RcicMulLTUnbounded`/`mulLT_wf` are not used.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

/-- The judgment atoms of the S2 multiset: one constructor per plain
    judgment family. -/
inductive Jd (E : ResolvedEnv) (n : Nat) : Type
  | ty {Γ : LCtx} {e T : Expr Nat} (d : HasTyT E n Γ e T)
  | cv {Γ : LCtx} {a b T : Expr Nat} (d : ConvT E n Γ a b T)
  | tc {Γ : LCtx} {A B : Expr Nat} (d : TyConvT E n Γ A B)
  | pr {Γ : LCtx} {a b T : Expr Nat}
      (d : ParRedT (PEqLeafT E n) E n Γ a b T)
  | pe {Γ : LCtx} {a b : Expr Nat} (d : PEqT E n Γ a b)

variable {E : ResolvedEnv} {n : Nat}

/-- weights = the existing counters (RcicParRedTSR: `hasTyTSize`,
    `convTSize`, `tyConvTSize`, `parRedTSize` with `peqLeafTSize` — i.e.
    F8's stepSize — and `peqTSize`). -/
def Jd.wt : Jd E n → Nat
  | .ty d => hasTyTSize d
  | .cv d => convTSize d
  | .tc d => tyConvTSize d
  | .pr d => parRedTSize (fun leaf => peqLeafTSize leaf) d
  | .pe d => peqTSize d

/-- immediate premises of a `HasTyT` node: every judgment-valued field,
    as a `Jd`. Single-level match over the indexed family — exhaustively
    per constructor, no wildcard arm. -/
def Jd.tyChildren {Γ : LCtx} {e T : Expr Nat} :
    HasTyT E n Γ e T → List (Jd E n)
  | .sort _ _ => []
  | .bvar _ _ _ _ => []
  | .const _ _ _ _ _ _ _ => []
  | .pi _ _ _ _ _ hA hB => [.ty hA, .ty hB]
  | .lam _ _ _ _ _ hA hbody => [.ty hA, .ty hbody]
  | .app _ _ _ _ _ hf ha => [.ty hf, .ty ha]
  | .letE _ _ _ _ _ _ hA hv hb => [.ty hA, .ty hv, .ty hb]
  | .lit _ _ _ hexp => [.ty hexp]
  | .conv _ _ _ _ _ h hc => [.ty h, .cv hc]

/-- immediate premises of a `ConvT` node. -/
def Jd.cvChildren {Γ : LCtx} {a b T : Expr Nat} :
    ConvT E n Γ a b T → List (Jd E n)
  | .refl _ _ _ h => [.ty h]
  | .symm _ _ _ _ h => [.cv h]
  | .trans _ _ _ _ _ h1 h2 => [.cv h1, .cv h2]
  | .beta _ _ _ _ _ _ hA hbody harg => [.ty hA, .ty hbody, .ty harg]
  | .zeta _ _ _ _ _ _ hA hv hb => [.ty hA, .ty hv, .ty hb]
  | .zetaLocal _ _ _ _ _ _ hv => [.ty hv]
  | .delta _ _ _ _ _ _ _ _ _ _ hb => [.ty hb]
  | .iota _ _ _ _ _ hlhs hrhs => [.ty hlhs, .ty hrhs]
  | .lit _ _ _ _ _ hexp => [.ty hexp]
  | .app _ _ _ _ _ _ _ h1 h2 => [.cv h1, .cv h2]
  | .lam _ _ _ _ _ _ _ hA hb => [.cv hA, .cv hb]
  | .pi _ _ _ _ _ _ _ hA hB => [.cv hA, .cv hB]
  | .letE _ _ _ _ _ _ _ _ _ hA hv hb => [.cv hA, .cv hv, .cv hb]
  | .sorts _ _ _ _ => []
  | .consts _ _ _ _ _ _ _ _ _ _ => []
  | .eta _ _ _ _ h => [.ty h]
  | .irr _ _ _ _ hP hp hq => [.ty hP, .ty hp, .ty hq]
  | .tyConv _ _ _ _ _ _ h hA => [.cv h, .cv hA]

/-- immediate premises of a `TyConvT` node. -/
def Jd.tcChildren {Γ : LCtx} {A B : Expr Nat} :
    TyConvT E n Γ A B → List (Jd E n)
  | .refl _ _ => []
  | .of _ _ _ _ h => [.cv h]
  | .trans _ _ _ _ h1 h2 => [.tc h1, .tc h2]

/-- immediate premises of a `ParRedT (PEqLeafT E n)` node. For `.peq` the
    `PEqLeafT` field contributes its three judgment components `.pe h.1`,
    `.ty h.2.1`, `.ty h.2.2`. -/
def Jd.prChildren {Γ : LCtx} {a b T : Expr Nat} :
    ParRedT (PEqLeafT E n) E n Γ a b T → List (Jd E n)
  | .refl _ _ _ h => [.ty h]
  | .sortEq _ _ _ _ _ hl hr => [.ty hl, .ty hr]
  | .consts _ _ _ _ _ _ hl hr => [.ty hl, .ty hr]
  | .bvarZeta _ _ _ _ _ _ _ hv hl hr => [.pr hv, .ty hl, .ty hr]
  | .delta _ _ _ _ _ _ _ _ _ _ _ hl hr => [.ty hl, .ty hr]
  | .app _ _ _ _ _ _ _ _ _ _ hf hc hB hTy ha hr =>
      [.pr hf, .tc hc, .ty hB, .ty hTy, .pr ha, .ty hr]
  | .beta _ _ _ _ _ _ _ _ _ _ hA hB hTy hb ha hred =>
      [.ty hA, .ty hB, .ty hTy, .pr hb, .pr ha, .ty hred]
  | .lam _ _ _ _ _ _ _ _ hc hA hB hb hrt =>
      [.cv hc, .ty hA, .ty hB, .pr hb, .ty hrt]
  | .pi _ _ _ _ _ _ _ hA hc hB hcB hrt =>
      [.ty hA, .cv hc, .ty hB, .cv hcB, .ty hrt]
  | .letE _ _ _ _ _ _ _ _ _ _ hc hA hv hB hTy hb hrt =>
      [.cv hc, .ty hA, .pr hv, .ty hB, .ty hTy, .pr hb, .ty hrt]
  | .zeta _ _ _ _ _ _ _ _ _ hA hv hB hTy hb hred =>
      [.ty hA, .pr hv, .ty hB, .ty hTy, .pr hb, .ty hred]
  | .iotaSpine _ _ _ _ _ hstep _ hred hrhs =>
      [.pr hstep, .ty hred, .ty hrhs]
  | .iotaStarK _ _ _ _ _ _ _ _ _ _ _ hmajor hmk hTm0 _ hlι hlhs hrhs =>
      [.ty hmajor, .ty hmk, .ty hTm0, .ty hlι, .ty hlhs, .ty hrhs]
  | .iotaStarKEta _ _ _ _ _ _ _ _ _ _ _ hA hf _ _ _ hmajor hmk hTm0 _ hlι hlhs hrhs =>
      [.ty hA, .ty hf, .ty hmajor, .ty hmk, .ty hTm0, .ty hlι, .ty hlhs, .ty hrhs]
  | .lit _ _ _ hexp => [.ty hexp]
  | .eta _ _ _ _ _ hf hl => [.pr hf, .ty hl]
  | .peq _ _ _ _ h => [.pe h.1, .ty h.2.1, .ty h.2.2]
  | .conv _ _ _ _ _ h hc => [.pr h, .tc hc]

/-- immediate premises of a `PEqT` node. -/
def Jd.peChildren {Γ : LCtx} {a b : Expr Nat} :
    PEqT E n Γ a b → List (Jd E n)
  | .bvar _ _ => []
  | .sort _ _ _ _ => []
  | .const _ _ _ _ _ => []
  | .app _ _ _ _ _ hf ha => [.pe hf, .pe ha]
  | .lam _ _ _ _ _ hA hb => [.pe hA, .pe hb]
  | .pi _ _ _ _ _ hA hB => [.pe hA, .pe hB]
  | .letE _ _ _ _ _ _ _ hA hv hb => [.pe hA, .pe hv, .pe hb]
  | .lit _ _ => []
  | .proof _ _ _ _ _ hP hQ hp hq => [.ty hP, .ty hQ, .ty hp, .ty hq]

/-- immediate premises: EVERY judgment-valued field of every constructor
    of `HasTyT`, `ConvT`, `TyConvT`, `ParRedT (PEqLeafT E n)`, `PEqT`, as
    a `Jd`; for `ParRedT.peq` the `PEqLeafT` field contributes `.pe h.1`,
    `.ty h.2.1`, `.ty h.2.2`. Non-judgment payload (`Level`, `eqN`,
    `DerivedIota`/`DerivedIotaU`, `IotaWitness`, lookup equations,
    `EliminationSelection`, …) is not a child. Exhaustive per
    constructor — no wildcard arm. -/
def Jd.children : Jd E n → List (Jd E n)
  | .ty d => Jd.tyChildren d
  | .cv d => Jd.cvChildren d
  | .tc d => Jd.tcChildren d
  | .pr d => Jd.prChildren d
  | .pe d => Jd.peChildren d

/-- `x` is an immediate premise of `y`: membership in `children`. -/
def Child (x y : Jd E n) : Prop := x ∈ y.children

/-- every immediate premise is strictly lighter — each child weight is a
    summand of the parent's `1 + …` counter. -/
theorem child_wt_lt {x y : Jd E n} (h : Child x y) : x.wt < y.wt := by
  cases y <;> rename_i d <;> cases d <;>
    simp only [Child, Jd.children, Jd.tyChildren, Jd.cvChildren,
      Jd.tcChildren, Jd.prChildren, Jd.peChildren, List.mem_cons,
      List.not_mem_nil, or_false, false_or] at h <;>
    (first
      | obtain rfl := h
      | obtain rfl | rfl := h
      | obtain rfl | rfl | rfl := h
      | obtain rfl | rfl | rfl | rfl := h
      | obtain rfl | rfl | rfl | rfl | rfl := h
      | obtain rfl | rfl | rfl | rfl | rfl | rfl := h
      | obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl := h
      | obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := h
      | cases h) <;>
    simp only [Jd.wt, hasTyTSize, convTSize, tyConvTSize, parRedTSize,
      peqTSize, peqLeafTSize] <;>
    omega

/-- strict sub-derivation: the transitive closure of `Child`. -/
inductive SubOf : Jd E n → Jd E n → Prop
  | child {x y} : Child x y → SubOf x y
  | trans {x y z} : SubOf x y → SubOf y z → SubOf x z

/-- non-strict sub-derivation: equal or strictly below. -/
def SubEq (x y : Jd E n) : Prop := x = y ∨ SubOf x y

theorem subOf_wt_lt {x y : Jd E n} (h : SubOf x y) : x.wt < y.wt := by
  induction h with
  | child hc => exact child_wt_lt hc
  | trans _ _ ihx ihy => exact Nat.lt_trans ihx ihy

theorem subEq_wt_le {x y : Jd E n} (h : SubEq x y) : x.wt ≤ y.wt := by
  cases h with
  | inl heq => exact heq ▸ Nat.le_refl _
  | inr hs => exact Nat.le_of_lt (subOf_wt_lt hs)

theorem subOf_irrefl (x : Jd E n) : ¬ SubOf x x :=
  fun h => absurd (subOf_wt_lt h) (Nat.lt_irrefl _)

theorem subEq_trans_subOf {x y z : Jd E n} (hxy : SubEq x y)
    (hyz : SubOf y z) : SubOf x z := by
  cases hxy with
  | inl heq => subst heq; exact hyz
  | inr hs => exact .trans hs hyz

theorem subOf_trans_subEq {x y z : Jd E n} (hxy : SubOf x y)
    (hyz : SubEq y z) : SubOf x z := by
  cases hyz with
  | inl heq => subst heq; exact hxy
  | inr hs => exact .trans hxy hs

/-- THE CORE LEMMA (S2 §1): a call whose literal leaves are all strict
    sub-derivations of removed atoms is a DM step; duplicates allowed. -/
theorem dm_of_strictLeaves {X Z L : List (Jd E n)} (hX : X ≠ [])
    (h : ∀ ℓ ∈ L, ∃ x ∈ X, SubOf ℓ x) :
    DMStep (L.map Jd.wt ++ Z.map Jd.wt) (X.map Jd.wt ++ Z.map Jd.wt) := by
  refine ⟨X.map Jd.wt, L.map Jd.wt, Z.map Jd.wt, ?_, List.Perm.refl _,
    List.Perm.refl _, ?_⟩
  · cases X with
    | nil => exact absurd rfl hX
    | cons a as => exact List.cons_ne_nil _ _
  · intro y hy
    rcases List.mem_map.mp hy with ⟨ℓ, hℓ, rfl⟩
    rcases h ℓ hℓ with ⟨x, hx, hsub⟩
    exact ⟨x.wt, List.mem_map.mpr ⟨x, hx, rfl⟩, subOf_wt_lt hsub⟩

/-! ### non-vacuity pins -/

/-- `Sort 0 : Sort 1` at the empty environment — the declarative pin. -/
private def pinHs : HasTyT emptyEnv 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  pinSortT emptyEnv 0

/-- `Sort 1 ≡ Sort 1` at `Sort 2` — the `ConvT` premise of the conv pin. -/
private def pinHc : ConvT emptyEnv 0 [] (.sort (.succ .zero))
    (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
  .sorts [] (.succ .zero) (.succ .zero) (fun _ => rfl)

/-- `Sort 0 : Sort 1` via `conv` — carries `pinHs` and `pinHc` as
    immediate premises. -/
private def pinHconv : HasTyT emptyEnv 0 [] (.sort .zero)
    (.sort (.succ .zero)) :=
  .conv [] (.sort .zero) (.sort (.succ .zero)) (.sort (.succ .zero))
    (.succ (.succ .zero)) pinHs pinHc

/-- pin: the `HasTyT` premise of a `conv` node is its child. -/
theorem pin_child_ty :
    Child (.ty pinHs : Jd emptyEnv 0) (.ty pinHconv) := by
  show (Jd.ty pinHs : Jd emptyEnv 0) ∈
    ([Jd.ty pinHs, Jd.cv pinHc] : List (Jd emptyEnv 0))
  exact .head _

/-- pin: the `ConvT` premise of a `conv` node is its child. -/
theorem pin_child_cv :
    Child (.cv pinHc : Jd emptyEnv 0) (.ty pinHconv) := by
  show (Jd.cv pinHc : Jd emptyEnv 0) ∈
    ([Jd.ty pinHs, Jd.cv pinHc] : List (Jd emptyEnv 0))
  exact .tail _ (.head _)

/-- pin: the DM step with the conv node as the removed atom and its two
    children DUPLICATED as the strict leaves (`Z = []`) — duplication is
    accepted. -/
theorem pin_dm_dup :
    DMStep
      (([.ty pinHs, .cv pinHc, .ty pinHs, .cv pinHc] :
            List (Jd emptyEnv 0)).map Jd.wt ++
        ([] : List (Jd emptyEnv 0)).map Jd.wt)
      (([.ty pinHconv] : List (Jd emptyEnv 0)).map Jd.wt ++
        ([] : List (Jd emptyEnv 0)).map Jd.wt) :=
  dm_of_strictLeaves
    (X := [Jd.ty pinHconv]) (Z := [])
    (L := [Jd.ty pinHs, Jd.cv pinHc, Jd.ty pinHs, Jd.cv pinHc])
    (List.cons_ne_nil _ _)
    (fun ℓ hℓ => by
      rcases (List.mem_cons.mp hℓ) with rfl | hℓ
      · exact ⟨_, .head _, .child pin_child_ty⟩
      · rcases (List.mem_cons.mp hℓ) with rfl | hℓ
        · exact ⟨_, .head _, .child pin_child_cv⟩
        · rcases (List.mem_cons.mp hℓ) with rfl | hℓ
          · exact ⟨_, .head _, .child pin_child_ty⟩
          · rcases (List.mem_cons.mp hℓ) with rfl | hℓ
            · exact ⟨_, .head _, .child pin_child_cv⟩
            · exact absurd hℓ (List.not_mem_nil _))

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.Jd
#print axioms Rcic.Declarative.F8Measure.Jd.wt
#print axioms Rcic.Declarative.F8Measure.Jd.tyChildren
#print axioms Rcic.Declarative.F8Measure.Jd.cvChildren
#print axioms Rcic.Declarative.F8Measure.Jd.tcChildren
#print axioms Rcic.Declarative.F8Measure.Jd.prChildren
#print axioms Rcic.Declarative.F8Measure.Jd.peChildren
#print axioms Rcic.Declarative.F8Measure.Jd.children
#print axioms Rcic.Declarative.F8Measure.Child
#print axioms Rcic.Declarative.F8Measure.child_wt_lt
#print axioms Rcic.Declarative.F8Measure.SubOf
#print axioms Rcic.Declarative.F8Measure.SubEq
#print axioms Rcic.Declarative.F8Measure.subOf_wt_lt
#print axioms Rcic.Declarative.F8Measure.subEq_wt_le
#print axioms Rcic.Declarative.F8Measure.subOf_irrefl
#print axioms Rcic.Declarative.F8Measure.subEq_trans_subOf
#print axioms Rcic.Declarative.F8Measure.subOf_trans_subEq
#print axioms Rcic.Declarative.F8Measure.dm_of_strictLeaves
#print axioms Rcic.Declarative.F8Measure.pin_child_ty
#print axioms Rcic.Declarative.F8Measure.pin_child_cv
#print axioms Rcic.Declarative.F8Measure.pin_dm_dup
