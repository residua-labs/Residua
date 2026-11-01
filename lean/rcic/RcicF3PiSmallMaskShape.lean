import rcic.RcicF3PiSmallMaskSpine
import rcic.RcicF3PiSmallKeyProducerAt
import rcic.RcicF3PiValueRule
import rcic.RcicF3KTWLfp

/-!
# Small ordinary shapes with actual recursive values reconstructed

Only conditional small addresses for ordinary fields enter the shape.
Recursive fields advance the shape environment with pempty, and are later
supplied as actual values. Their branch topology uses the masked prefix;
child and result keys use the reconstructed actual prefix. All ordinary
dependencies and arbitrary inner Pi depth remain in the construction.

TupleMask is an exact intermediate domain-independence predicate. Its
admitted producer is not asserted here. Leaves is reached full-key leaf
inclusion, not a constructor/recursion producer. The complete theorem
constructs the shape and forward field spine from those precise inputs.
The resulting small signature is independent of recursive field values.
Parameterwise all-universe frame assembly remains separate.
closure_claim = 0.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallMaskShape
open Rcic.Declarative PiIndex
open PiValueRule (FieldSpec Place fieldExpr)
open PiSmallTuple (rep rep_spec)
universe u v T

noncomputable def Space (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : List FieldSpec → (Nat → PSet.{max (u+1) v}) → Type u
  | [], _ => ULift.{u} Unit
  | .plain A :: fs, η =>
      (q : FBr (rep.{u,v} N ch (Ed N (den N σ η A)))) ×
        Space N ch σ fs
          (vcons (lift.{u,max (u+1) v} (PiCompile.classValue _ q)) η)
  | .recursive _ _ :: fs, η => Space N ch σ fs (vcons pempty η)

noncomputable def values (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : (fs : List FieldSpec) → (η : Nat → PSet.{max (u+1) v}) →
      Space.{u,v} N ch σ fs η → (Place fs → PSet.{max (u+1) v}) → List PSet.{max (u+1) v}
  | [], _, _, _ => []
  | .plain A :: fs, η, s, f =>
      lift.{u,max (u+1) v} (PiCompile.classValue (rep.{u,v} N ch (Ed N (den N σ η A))) s.1) ::
        values N ch σ fs
          (vcons (lift.{u,max (u+1) v} (PiCompile.classValue _ s.1)) η) s.2
          (fun p => f (.next (.plain A) p))
  | .recursive ds args :: fs, η, s, f =>
      f .here :: values N ch σ fs (vcons pempty η) s
        (fun p => f (.next (.recursive ds args) p))

theorem values_length (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : ∀ fs η (s : Space.{u,v} N ch σ fs η) f,
      (values.{u,v} N ch σ fs η s f).length = fs.length
  | [], _, _, _ => rfl
  | .plain _ :: fs, _, s, _ => congrArg Nat.succ (values_length N ch σ fs _ s.2 _)
  | .recursive _ _ :: fs, _, s, _ => congrArg Nat.succ (values_length N ch σ fs _ s _)

theorem values_congr (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : ∀ fs η (s : Space.{u,v} N ch σ fs η) f g,
      (∀ k, Equiv (f k) (g k)) →
      LEq (values.{u,v} N ch σ fs η s f) (values.{u,v} N ch σ fs η s g)
  | [], _, _, _, _, _ => True.intro
  | .plain A :: fs, _, s, f, g, h =>
      ⟨Equiv.rfl, values_congr N ch σ fs _ s.2 _ _ (fun p => h (.next (.plain A) p))⟩
  | .recursive ds args :: fs, _, s, f, g, h =>
      ⟨h .here, values_congr N ch σ fs _ s _ _
        (fun p => h (.next (.recursive ds args) p))⟩

/-- A path label contains its complete inner argument tuple. No large
quotient representative is selected to form this label. -/
noncomputable def tel (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : (fs : List FieldSpec) → (η : Nat → PSet.{max (u+1) v}) →
      (s : Space.{u,v} N ch σ fs η) → (p : Place fs) →
        RecTel.{u,max (u+1) v + 1} (List PSet.{max (u+1) v}) p.depth := by
  intro fs η s p
  revert η s
  induction p with
  | @next a fs p ih =>
      intro η s
      cases a with
      | plain A =>
          exact ih (vcons (lift.{u,max (u+1) v}
            (PiCompile.classValue _ s.1)) η) s.2
      | recursive ds args => exact ih (vcons pempty η) s
  | @here ds args fs =>
      intro η _
      exact PiSmallRecursive.compile.{u,v,max (u+1) v + 1}
        N ch σ (lastVals ds.length) ds η

theorem tel_domains (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : ∀ fs η (s : Space.{u,v} N ch σ fs η) (p : Place fs),
      (tel.{u,v} N ch σ fs η s p).DomainsDich
  | .plain _ :: fs, _, s, .next _ p => tel_domains N ch σ fs _ s.2 p
  | .recursive _ _ :: fs, _, s, .next _ p => tel_domains N ch σ fs _ s p
  | .recursive ds _ :: _, η, _, .here =>
      PiSmallFieldAt.compile_domains.{u,v,max (u+1) v + 1} N ch σ (lastVals ds.length) ds η

/-- Only domains use the masked environment. This reader uses every
actual preceding recursive field and every actual inner argument. -/
noncomputable def child (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : (fs : List FieldSpec) → (η : Nat → PSet.{max (u+1) v}) →
      Space.{u,v} N ch σ fs η → (Place fs → PSet.{max (u+1) v}) →
      (Nat → PSet.{max (u+1) v}) → Place fs → List PSet.{max (u+1) v} → Index.{max (u+1) v} := by
  intro fs η s f ρ p zs
  revert η s f ρ zs
  induction p with
  | @next a fs p ih =>
      intro η s f ρ zs
      cases a with
      | plain A =>
          let x := lift.{u,max (u+1) v} (PiCompile.classValue
            (rep.{u,v} N ch (Ed N (den N σ η A))) s.1)
          exact ih (vcons x η) s.2 (fun p => f (.next (.plain A) p)) (vcons x ρ) zs
      | recursive ds args =>
          exact ih (vcons pempty η) s (fun p => f (.next (.recursive ds args) p))
            (vcons (f .here) ρ) zs
  | @here ds args fs =>
      intro _ _ _ ρ zs
      exact read N σ args (push zs ρ)

theorem child_congr (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : ∀ fs η (s : Space.{u,v} N ch σ fs η) f g ρ ρ',
      (∀ k, Equiv (f k) (g k)) → (∀ k, Equiv (ρ k) (ρ' k)) →
      ∀ p zs, child.{u,v} N ch σ fs η s f ρ p zs = child.{u,v} N ch σ fs η s g ρ' p zs
  | .plain A :: fs, _, s, f, g, _, _, h, hρ, .next _ p, zs =>
      child_congr N ch σ fs _ s.2 _ _ _ _
        (fun p => h (.next (.plain A) p)) (vcons_congr Equiv.rfl hρ) p zs
  | .recursive ds args :: fs, _, s, f, g, _, _, h, hρ, .next _ p, zs =>
      child_congr N ch σ fs _ s _ _ _ _
        (fun p => h (.next (.recursive ds args) p)) (vcons_congr (h .here) hρ) p zs
  | .recursive _ args :: _, _, _, _, _, _, _, _, hρ, .here, zs =>
      read_congr N σ args (push_congr (LEq.refl zs) hρ)

/-- The concrete domain mask is local to the actual supplied tuple.
Ordinary representatives may change by Equiv; recursive values are erased
only in the topology environment. No terminal-index clause occurs. -/
def TupleMask (M N : Interp.{T}) (σ : Nat → Nat) :
    List FieldSpec → (Nat → PSet.{T}) →
      (Nat → PSet.{T}) → List PSet.{T} → Prop
  | [], _, _, [] => True
  | .plain A :: fs, ρ, η, x :: xs =>
      Equiv (Ed M (den M σ ρ A)) (Ed N (den N σ η A)) ∧
      ∀ y, Equiv x y → TupleMask M N σ fs (vcons x ρ) (vcons y η) xs
  | .recursive ds _ :: fs, ρ, η, x :: xs =>
      PiSmallMaskSpine.Domains M N σ ds ρ η ∧
      TupleMask M N σ fs (vcons x ρ) (vcons pempty η) xs
  | _, _, _, _ => False

/-- Every recursive leaf keeps the complete arguments evaluated in the
actual prefix. An actual family-application decoder can supply this input. -/
def Leaves (M N : Interp.{T}) (σ : Nat → Nat) (family : Nat)
    (ls : List Level) (X : Index.{T} → PSet.{T}) :
    List FieldSpec → (Nat → PSet.{T}) → List PSet.{T} → Prop
  | [], _, [] => True
  | .plain _ :: fs, ρ, x :: xs => Leaves M N σ family ls X fs (vcons x ρ) xs
  | .recursive ds args :: fs, ρ, x :: xs =>
      (∀ zs, TelFits M σ ds ρ zs →
        Sub (Ed M (den M σ (push zs ρ) (foldApps (.const family ls) args)))
          (X (read N σ args (push zs ρ)))) ∧
      Leaves M N σ family ls X fs (vcons x ρ) xs
  | _, _, _ => False

def FieldsFit (M N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) (fs : List FieldSpec) (η : Nat → PSet.{max (u+1) v})
    (s : Space.{u,v} N ch σ fs η) (f : Place fs → PSet.{max (u+1) v})
    (ρ : Nat → PSet.{max (u+1) v}) (X : Index.{max (u+1) v} → PSet.{max (u+1) v}) : Prop :=
  ∀ p, f p ∈ Ed M
    ((PiSmallRecursive.widen.{u,v,max (u+1) v + 1} (tel.{u,v} N ch σ fs η s p)).erasedType M
      (fun zs => X (child.{u,v} N ch σ fs η s f ρ p zs)))

/-- The shape and every recursive field are constructed from the literal
tuple. Source and reconstructed prefixes are pointwise equivalent; the
separate masked prefix is related only by TupleMask. -/
theorem complete (M N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) (family : Nat) (ls : List Level)
    (X : Index.{max (u+1) v} → PSet.{max (u+1) v}) (hX : ∀ i, Dich (X i)) :
    ∀ fs ρ η ρ' xs, (∀ k, Equiv (ρ k) (ρ' k)) →
      TelFits M σ (fs.map (fieldExpr family ls)) ρ xs →
      SmallAlong M σ (univIn.{u,v}) (fs.map (fieldExpr family ls)) ρ xs →
      TupleMask M N σ fs ρ η xs → Leaves M N σ family ls X fs ρ xs →
      ∃ (s : Space.{u,v} N ch σ fs η) (f : Place fs → PSet.{max (u+1) v}),
        LEq xs (values.{u,v} N ch σ fs η s f) ∧ FieldsFit.{u,v} M N ch σ fs η s f ρ' X := by
  intro fs
  induction fs with
  | nil =>
      intro ρ η ρ' xs _ hx _ _ _
      cases xs with
      | nil =>
          let f : Place [] → PSet.{max (u+1) v} := by intro p; cases p
          refine ⟨⟨()⟩, f, True.intro, ?_⟩
          intro p
          cases p
      | cons _ _ => exact False.elim hx
  | cons field fs ih =>
      intro ρ η ρ' xs hρ hx hs hm hl
      cases xs with
      | nil => exact False.elim hx
      | cons x xs =>
        cases field with
        | plain A =>
          let D := Ed N (den N σ η A)
          let S := rep.{u,v} N ch D
          have hD : Small.{u,max (u+1) v} D :=
            mem_univIn.{u,v}.mp (mem_congr_left hm.1 hs.1)
          have hxD : x ∈ D := mem_congr_right hm.1 hx.1
          have hxS : x ∈ lift.{u,max (u+1) v} S :=
            mem_congr_right (rep_spec.{u,v} N ch D hD) hxD
          obtain ⟨y, ⟨a, ha⟩, hy⟩ := mem_lift.{u,max (u+1) v}.mp hxS
          let q : FBr S := Quotient.mk (FSetoid S) a
          let x' := lift.{u,max (u+1) v} (PiCompile.classValue S q)
          have he : Equiv x x' := hy.trans
            ((lift_equiv.{u,max (u+1) v} ha).symm.trans
              (lift_equiv.{u,max (u+1) v} (PiCompile.classValue_at S a)).symm)
          obtain ⟨st, ft, ht, hf⟩ := ih (vcons x ρ) (vcons x' η) (vcons x' ρ') xs
            (vcons_congr he hρ) hx.2 hs.2 (hm.2 x' he) hl
          let f : Place (.plain A :: fs) → PSet.{max (u+1) v} := by
            intro p
            cases p with
            | next _ k => exact ft k
          refine ⟨⟨q, st⟩, f, ⟨he, ht⟩, ?_⟩
          intro p
          cases p with
          | next _ p => exact hf p
        | recursive ds args =>
          obtain ⟨st, ft, ht, hf⟩ := ih (vcons x ρ) (vcons pempty η) (vcons x ρ') xs
            (vcons_congr Equiv.rfl hρ) hx.2 hs.2 hm.2 hl.2
          let f : Place (.recursive ds args :: fs) → PSet.{max (u+1) v} := by
            intro p
            cases p with
            | here => exact x
            | next _ k => exact ft k
          refine ⟨st, f, ⟨Equiv.rfl, ht⟩, ?_⟩
          intro p
          cases p with
          | next _ p => exact hf p
          | here =>
            apply PiSmallMaskSpine.compile_mem_of_stage.{u,v,max (u+1) v + 1} M N ch σ (lastVals ds.length)
              (fun zs => X (read N σ args (push zs ρ'))) (fun _ => hX _)
              ds (foldApps (.const family ls) args) ρ η hm.1 ?_ x hs.1 hx.1
            intro zs hz z hleaf
            have hlen : ds.length = zs.length := hz.length.symm
            rw [hlen, lastVals_push]
            have he : read N σ args (push zs ρ) = read N σ args (push zs ρ') :=
              read_congr N σ args (push_congr (LEq.refl zs) hρ)
            change z ∈ X (read N σ args (push zs ρ'))
            rw [← he]
            exact hl.1 zs hz z hleaf

/-- All shape-stored ordinary values are small at the selected universe.
Only the recursive field values are supplied to this implication. -/
theorem values_small (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) : ∀ fs η (s : Space.{u,v} N ch σ fs η) f,
      (∀ p, Small.{u,max (u+1) v} (f p)) →
      ∀ x, x ∈ values.{u,v} N ch σ fs η s f → Small.{u,max (u+1) v} x
  | [], _, _, _, _, _, hx => (List.not_mem_nil _ hx).elim
  | .plain A :: fs, η, s, f, hf, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · let D := Ed N (den N σ η A)
        have hD := PiSmallTuple.small_of_rep_mem.{u,v} N ch D s.1
        exact small_of_mem_small hD (mem_congr_right (rep_spec.{u,v} N ch D hD).symm
          (lift_mem_lift.{u,max (u+1) v}.mpr (PiCompile.classValue_mem _ s.1)))
      · exact values_small N ch σ fs _ s.2 _ (fun p => hf (.next (.plain A) p)) x hx
  | .recursive ds args :: fs, _, s, f, hf, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hf .here
      · exact values_small N ch σ fs _ s _
          (fun p => hf (.next (.recursive ds args) p)) x hx

noncomputable def signature (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) (cs : List PiValueRule.Constructor) (ps : List PSet.{max (u+1) v}) :
    PiSmallKeyProducerAt.Sig.{u,v,max (u+1) v + 1,max (u+1) v + 1}
      Index.{max (u+1) v} (List PSet.{max (u+1) v}) where
  Sh := (j : Fin cs.length) × Space.{u,v} N ch σ (cs[j]).fields (push ps (fun _ => pempty))
  Field s := ULift.{u} (Place (cs[s.1]).fields)
  depth _ p := p.down.depth
  tel s p := tel.{u,v} N ch σ _ _ s.2 p.down
  child s f p zs := child.{u,v} N ch σ _ _ s.2 (fun k => f ⟨k⟩) (push ps (fun _ => pempty)) p.down zs
  out s f := key (ps ++ (cs[s.1]).result.map (den N σ
    (push (values.{u,v} N ch σ _ _ s.2 (fun k => f ⟨k⟩)) (push ps (fun _ => pempty)))))
  code s f := dataVal s.1.val (values.{u,v} N ch σ _ _ s.2 (fun k => f ⟨k⟩))
  child_congr s f g h p zs := child_congr.{u,v} N ch σ _ _ s.2 _ _ _ _
    (fun k => h ⟨k⟩) (fun _ => Equiv.rfl) p.down zs
  out_congr s f g h := (key_eq_iff _ _).mpr
    (LEq_append (LEq.refl ps) (LEq_map_den N σ
      (push_congr (values_congr.{u,v} N ch σ _ _ s.2 _ _ (fun k => h ⟨k⟩))
        (fun _ => Equiv.rfl)) (cs[s.1]).result))
  code_congr s f g h := dataVal_congr s.1.val
    (values_congr.{u,v} N ch σ _ _ s.2 _ _ (fun k => h ⟨k⟩))

theorem signature_domains (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) (cs : List PiValueRule.Constructor) (ps : List PSet.{max (u+1) v})
    (s : (signature.{u,v} N ch σ cs ps).Sh) (p : (signature.{u,v} N ch σ cs ps).Field s) :
    ((signature.{u,v} N ch σ cs ps).tel s p).DomainsDich :=
  tel_domains.{u,v} N ch σ _ _ s.2 p.down

theorem signature_data (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) (cs : List PiValueRule.Constructor) (ps : List PSet.{max (u+1) v}) :
    PiSmallKeyProducerAt.DataCode (signature.{u,v} N ch σ cs ps) :=
  fun s f => dataVal_ne_pempty s.1.val _

theorem signature_stage (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) (cs : List PiValueRule.Constructor) (ps : List PSet.{max (u+1) v})
    (hW : Stage (univIn.{u,v})) :
    PiSmallKeyProducerAt.CodeStage (signature.{u,v} N ch σ cs ps) (univIn.{u,v}) := by
  intro s f hf
  apply dataVal_mem_stage hW s.1.val
  intro x hx
  exact mem_univIn.{u,v}.mpr (values_small.{u,v} N ch σ _ _ s.2 _
    (fun p => mem_univIn.{u,v}.mp (hf ⟨p⟩)) x hx)

/-- A genuine small closed semantic signature is constructed. This is
closure for its compiled domain topology, not yet for the original family
operator. The latter must supply TupleMask and its actual reached leaves. -/
theorem component (N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (σ : Nat → Nat) (cs : List PiValueRule.Constructor) (ps : List PSet.{max (u+1) v})
    (hW : Stage (univIn.{u,v})) :
    PiSmallKeyProducerAt.Closed N (signature.{u,v} N ch σ cs ps)
      (PiSmallKeyProducerAt.family N (signature.{u,v} N ch σ cs ps)) ∧
    ∀ i, PiSmallKeyProducerAt.family N (signature.{u,v} N ch σ cs ps) i ∈ univIn.{u,v} ∧
      ¬ pempty ∈ PiSmallKeyProducerAt.family N (signature.{u,v} N ch σ cs ps) i :=
  PiSmallKeyProducerAt.component ch N (signature.{u,v} N ch σ cs ps)
    (signature_data.{u,v} N ch σ cs ps) (signature_domains.{u,v} N ch σ cs ps)
    (signature_stage.{u,v} N ch σ cs ps hW)

/-- The actual constructor code enters the newly constructed small family.
Source and topology models may have different constant tables, while their
decision procedures agree. All leaf keys and the output key remain full. -/
theorem produce (M N : Interp.{max (u+1) v}) (ch : Choice.{u})
    (hdec : M.dec = N.dec) (σ : Nat → Nat)
    (cs : List PiValueRule.Constructor) (ps : List PSet.{max (u+1) v})
    (family : Nat) (ls : List Level) (j : Fin cs.length) (xs : List PSet.{max (u+1) v})
    (hx : TelFits M σ ((cs[j]).fields.map (fieldExpr family ls)) (push ps (fun _ => pempty)) xs)
    (hs : SmallAlong M σ (univIn.{u,v})
      ((cs[j]).fields.map (fieldExpr family ls)) (push ps (fun _ => pempty)) xs)
    (hm : TupleMask M N σ (cs[j]).fields (push ps (fun _ => pempty)) (push ps (fun _ => pempty)) xs)
    (hl : Leaves M N σ family ls
      (PiSmallKeyProducerAt.family N (signature.{u,v} N ch σ cs ps))
      (cs[j]).fields (push ps (fun _ => pempty)) xs) :
    dataVal j.val xs ∈ PiSmallKeyProducerAt.family N (signature.{u,v} N ch σ cs ps)
      (key (ps ++ (cs[j]).result.map (den N σ (push xs (push ps (fun _ => pempty)))))) := by
  let S := signature.{u,v} N ch σ cs ps
  let X := PiSmallKeyProducerAt.family N S
  have hX : ∀ i, Dich (X i) :=
    PiSmallKeyProducerAt.family_dich N S (Or.inr (signature_data.{u,v} N ch σ cs ps))
  obtain ⟨s, f, he, hf⟩ := complete.{u,v} M N ch σ family ls X hX (cs[j]).fields
    (push ps (fun _ => pempty)) (push ps (fun _ => pempty)) (push ps (fun _ => pempty)) xs (fun _ => Equiv.rfl) hx hs hm hl
  let t : S.Sh := ⟨j, s⟩
  let g : S.Field t → PSet.{max (u+1) v} := fun p => f p.down
  have hfit : PiSmallKeyProducerAt.FieldsFit N S X t g := by
    intro p
    have hm' := hf p.down
    have heq := PiSmallMaskSpine.elements_of_dec M N hdec
      (PiSmallRecursive.widen.{u,v,max (u+1) v + 1}
        (tel.{u,v} N ch σ (cs[j]).fields (push ps (fun _ => pempty)) s p.down))
      (fun zs => X (child.{u,v} N ch σ (cs[j]).fields (push ps (fun _ => pempty)) s f (push ps (fun _ => pempty)) p.down zs))
    exact heq ▸ hm'
  have hmem := PiSmallKeyProducerAt.produce N ch S
    (Or.inr (signature_data.{u,v} N ch σ cs ps)) (signature_domains.{u,v} N ch σ cs ps) t g hfit
  have hkey : key (ps ++ (cs[j]).result.map (den N σ (push xs (push ps (fun _ => pempty))))) =
      S.out t g := (key_eq_iff _ _).mpr (LEq_append (LEq.refl ps)
        (LEq_map_den N σ (push_congr he (fun _ => Equiv.rfl)) (cs[j]).result))
  rw [hkey]
  exact mem_congr_left (dataVal_congr j.val he).symm hmem

theorem component_stage_one (P : Premises4) (N : Interp.{4}) (σ : Nat → Nat)
    (cs : List PiValueRule.Constructor) (ps : List PSet.{4}) :
    PiSmallKeyProducerAt.Closed N (signature.{0,4} N P.c0 σ cs ps)
      (PiSmallKeyProducerAt.family N (signature.{0,4} N P.c0 σ cs ps)) ∧
    ∀ i, PiSmallKeyProducerAt.family N (signature.{0,4} N P.c0 σ cs ps) i ∈ W4 1 ∧
      ¬ pempty ∈ PiSmallKeyProducerAt.family N (signature.{0,4} N P.c0 σ cs ps) i :=
  component.{0,4} N P.c0 σ cs ps (stage4 P 0)

theorem component_stage_two (P : Premises4) (N : Interp.{4}) (σ : Nat → Nat)
    (cs : List PiValueRule.Constructor) (ps : List PSet.{4}) :
    PiSmallKeyProducerAt.Closed N (signature.{1,4} N P.c1 σ cs ps)
      (PiSmallKeyProducerAt.family N (signature.{1,4} N P.c1 σ cs ps)) ∧
    ∀ i, PiSmallKeyProducerAt.family N (signature.{1,4} N P.c1 σ cs ps) i ∈ W4 2 ∧
      ¬ pempty ∈ PiSmallKeyProducerAt.family N (signature.{1,4} N P.c1 σ cs ps) i :=
  component.{1,4} N P.c1 σ cs ps (stage4 P 1)

theorem component_stage_three (P : Premises4) (N : Interp.{4}) (σ : Nat → Nat)
    (cs : List PiValueRule.Constructor) (ps : List PSet.{4}) :
    PiSmallKeyProducerAt.Closed N (signature.{2,4} N P.c2 σ cs ps)
      (PiSmallKeyProducerAt.family N (signature.{2,4} N P.c2 σ cs ps)) ∧
    ∀ i, PiSmallKeyProducerAt.family N (signature.{2,4} N P.c2 σ cs ps) i ∈ W4 3 ∧
      ¬ pempty ∈ PiSmallKeyProducerAt.family N (signature.{2,4} N P.c2 σ cs ps) i :=
  component.{2,4} N P.c2 σ cs ps (stage4 P 2)

theorem component_stage_four_plus (P : Premises4) (N : Interp.{4}) (σ : Nat → Nat)
    (cs : List PiValueRule.Constructor) (ps : List PSet.{4}) (k : Nat) :
    PiSmallKeyProducerAt.Closed N (signature.{3,4} N P.c3 σ cs ps)
      (PiSmallKeyProducerAt.family N (signature.{3,4} N P.c3 σ cs ps)) ∧
    ∀ i, PiSmallKeyProducerAt.family N (signature.{3,4} N P.c3 σ cs ps) i ∈ W4 (k+4) ∧
      ¬ pempty ∈ PiSmallKeyProducerAt.family N (signature.{3,4} N P.c3 σ cs ps) i :=
  component.{3,4} N P.c3 σ cs ps (stageW4 P (k+4))

end Rcic.F3.PSet.PiSmallMaskShape
