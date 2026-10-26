import rcic.RcicF3KTWBridge
import rcic.RcicF3KTWFun
import rcic.RcicF3Data
import rcic.RcicF3Rec

/-!
# F3 S7 KT-2b-3a: the semantic constructor spec and its guarded W-signature

Theory-agnostic (ADR #8005 §7b): no R-CIC syntax.  A constructor telescope is described by field
*kinds* (`plain` / `direct` recursion / `fn` recursion), a small index type `Sh` of the non-recursive
data, the small domains of the recursive positions, and the big-universe semantics `Sem`
(`resTup`: the result-index tuple of a data value; `nonrecOk`; `recTup`).  `Layout.sig` builds the
`GSig`: shapes `Sh`, branches `Σ k, FBr (dom k s)`, code `dataVal tag (asm …)`, guard `okW`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v w

namespace PSet

inductive PKind where
  | plain | direct | fn
  deriving DecidableEq

/-- Signature-side layout of one constructor. -/
structure Layout (Sh : Type u) where
  tag : Nat
  kinds : List PKind
  dom : Nat → Sh → PSet.{u}
  pt : (k : Nat) → (s : Sh) → Option (FBr (dom k s))
  nr : Sh → List PSet.{u}

/-- Branches: a recursive position and a class of its domain. -/
def Layout.Br {Sh : Type u} (L : Layout Sh) (s : Sh) : Type u := Σ k : Nat, FBr (L.dom k s)

/-- The value of the field at position `k` of kind `p`, given the next non-recursive value `x`. -/
def Layout.fieldVal {Sh : Type u} (L : Layout Sh) (s : Sh) (h : L.Br s → PSet.{u}) (p : PKind) (k : Nat)
    (x : PSet.{u}) : PSet.{u} :=
  match p with
  | .plain => x
  | .direct => (match L.pt k s with | some q => h ⟨k, q⟩ | none => pempty)
  | .fn => graphOf (L.dom k s) (fun q => h ⟨k, q⟩)

def nrTail : PKind → List PSet.{u} → List PSet.{u}
  | .plain, _ :: nr => nr
  | _, nr => nr

/-- The assembled field values. -/
def Layout.asm {Sh : Type u} (L : Layout Sh) (s : Sh) (h : L.Br s → PSet.{u}) :
    List PKind → Nat → List PSet.{u} → List PSet.{u}
  | [], _, _ => []
  | p :: ps, k, nr => L.fieldVal s h p k (nr.headD pempty) :: L.asm s h ps (k + 1) (nrTail p nr)

/-- Big-universe semantics of the group's guards. -/
structure Sem where
  resTup : PSet.{w} → PSet.{w}
  nonrecOk : Nat → List PSet.{w} → PSet.{w} → Prop
  recTup : Nat → List PSet.{w} → PSet.{w} → PSet.{w}
  domBig : Nat → List PSet.{w} → PSet.{w}
  resTup_congr : ∀ x y, Equiv x y → Equiv (resTup x) (resTup y)
  nonrecOk_congr : ∀ k pre pre' x x', LEq pre pre' → Equiv x x' → nonrecOk k pre x → nonrecOk k pre' x'
  recTup_congr : ∀ k pre pre' y y', LEq pre pre' → Equiv y y' → Equiv (recTup k pre y) (recTup k pre' y')
  domBig_congr : ∀ k pre pre', LEq pre pre' → Equiv (domBig k pre) (domBig k pre')

/-- The guard on one field. -/
def Layout.fieldOk {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v}) (s : Sh) (h : L.Br s → PSet.{u})
    (p : PKind) (k : Nat) (x : PSet.{u}) (pre : List PSet.{max u v}) : Prop :=
  match p with
  | .plain => Sm.nonrecOk k pre (lift.{u, v} x)
  | .direct => (match L.pt k s with
      | some q => Equiv (Sm.resTup (lift.{u, v} (h ⟨k, q⟩))) (Sm.recTup k pre pempty)
      | none => False)
  | .fn => ∀ i : (L.dom k s).Idx,
      Equiv (Sm.resTup (lift.{u, v} (h ⟨k, Quotient.mk (FSetoid (L.dom k s)) i⟩)))
        (Sm.recTup k pre (lift.{u, v} ((L.dom k s).Func i)))

/-- The guard on the whole telescope, walked with the lifted prefix. -/
def Layout.okW {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v}) (s : Sh) (h : L.Br s → PSet.{u}) :
    List PKind → Nat → List PSet.{u} → List PSet.{max u v} → Prop
  | [], _, _, _ => True
  | p :: ps, k, nr, pre =>
      L.fieldOk Sm s h p k (L.fieldVal s h p k (nr.headD pempty)) pre ∧
      L.okW Sm s h ps (k + 1) (nrTail p nr) (pre ++ [lift.{u, v} (L.fieldVal s h p k (nr.headD pempty))])

theorem graphOf_congr {A : PSet.{u}} {h h' : FBr A → PSet.{u}} (e : ∀ q, Equiv (h q) (h' q)) :
    Equiv (graphOf A h) (graphOf A h') :=
  ⟨fun i => ⟨i, ordPair_congr Equiv.rfl (e _)⟩, fun i => ⟨i, ordPair_congr Equiv.rfl (e _)⟩⟩

theorem Layout.fieldVal_congr {Sh : Type u} (L : Layout Sh) (s : Sh) {h h' : L.Br s → PSet.{u}}
    (e : ∀ b, Equiv (h b) (h' b)) (p : PKind) (k : Nat) (x : PSet.{u}) :
    Equiv (L.fieldVal s h p k x) (L.fieldVal s h' p k x) := by
  cases p with
  | plain => exact Equiv.rfl
  | direct =>
      simp only [Layout.fieldVal]
      cases L.pt k s with
      | none => exact Equiv.rfl
      | some q => exact e _
  | fn => exact graphOf_congr (fun q => e _)

theorem Layout.asm_congr {Sh : Type u} (L : Layout Sh) (s : Sh) {h h' : L.Br s → PSet.{u}}
    (e : ∀ b, Equiv (h b) (h' b)) :
    (ps : List PKind) → (k : Nat) → (nr : List PSet.{u}) →
    LEq (L.asm s h ps k nr) (L.asm s h' ps k nr)
  | [], _, _ => trivial
  | p :: ps, k, nr => ⟨L.fieldVal_congr s e p k _, L.asm_congr s e ps (k + 1) _⟩

theorem Layout.fieldOk_congr {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v}) (s : Sh) {h h' : L.Br s → PSet.{u}}
    (e : ∀ b, Equiv (h b) (h' b)) (p : PKind) (k : Nat) (x : PSet.{u}) {pre pre' : List PSet.{max u v}}
    (hp : LEq pre pre') (hok : L.fieldOk Sm s h p k x pre) : L.fieldOk Sm s h' p k x pre' := by
  cases p with
  | plain => exact Sm.nonrecOk_congr k pre pre' _ _ hp Equiv.rfl hok
  | direct =>
      simp only [Layout.fieldOk] at hok ⊢
      cases hq : L.pt k s with
      | none => rw [hq] at hok; exact hok
      | some q =>
          rw [hq] at hok
          exact ((Sm.resTup_congr _ _ (lift_equiv.{u, v} (e _))).symm.trans hok).trans
            (Sm.recTup_congr k pre pre' _ _ hp Equiv.rfl)
  | fn =>
      intro i
      exact ((Sm.resTup_congr _ _ (lift_equiv.{u, v} (e _))).symm.trans (hok i)).trans
        (Sm.recTup_congr k pre pre' _ _ hp Equiv.rfl)

theorem Layout.okW_congr {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v}) (s : Sh) {h h' : L.Br s → PSet.{u}}
    (e : ∀ b, Equiv (h b) (h' b)) :
    (ps : List PKind) → (k : Nat) → (nr : List PSet.{u}) → (pre pre' : List PSet.{max u v}) → LEq pre pre' →
    L.okW Sm s h ps k nr pre → L.okW Sm s h' ps k nr pre'
  | [], _, _, _, _, _ => fun _ => trivial
  | p :: ps, k, nr, pre, pre', hp => by
      refine fun ⟨hf, hr⟩ => ⟨?_, ?_⟩
      · have hv : Equiv (L.fieldVal s h p k (nr.headD pempty)) (L.fieldVal s h' p k (nr.headD pempty)) :=
          L.fieldVal_congr s e p k _
        have hf' := L.fieldOk_congr Sm s e p k _ hp hf
        cases p with
        | plain => exact hf'
        | direct => exact hf'
        | fn => exact hf'
      · have hl : LEq [lift.{u, v} (L.fieldVal s h p k (nr.headD pempty))]
            [lift.{u, v} (L.fieldVal s h' p k (nr.headD pempty))] :=
          ⟨lift_equiv.{u, v} (L.fieldVal_congr s e p k _), trivial⟩
        exact L.okW_congr Sm s e ps (k + 1) _ _ _ (LEq_append hp hl) hr

/-- The guarded W-signature of one constructor. -/
noncomputable def Layout.sig {Sh : Type u} (L : Layout Sh) (Sm : Sem.{max u v}) : GSig.{u} where
  Sh := Sh
  br := L.Br
  code := fun s h => dataVal L.tag (L.asm s h L.kinds 0 (L.nr s))
  ok := fun s h => L.okW Sm s h L.kinds 0 (L.nr s) []
  code_congr := fun s h h' e => dataVal_congr L.tag (L.asm_congr s e L.kinds 0 _)
  ok_congr := fun s h h' e => L.okW_congr Sm s e L.kinds 0 _ [] [] trivial

end PSet

end Rcic.F3
