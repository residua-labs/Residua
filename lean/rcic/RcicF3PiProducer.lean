import rcic.RcicF3PiField

/-! An indexed semantic constructor producer from represented recursive
arguments. Raw syntax/StepAG integration is not asserted. `closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet
universe u

/-- A strictly positive indexed semantic signature. Nonrecursive data is
part of the shape; recursive fields retain their dependent telescopes. -/
structure RecSig (I : Type u) where
  Sh : Type u
  Field : Sh → Type u
  depth : (s : Sh) → Field s → Nat
  tel : (s : Sh) → (k : Field s) → RecTel I (depth s k)
  out : Sh → I
  code : (s : Sh) → (Field s → PSet.{u}) → PSet.{u}
  tag : PSet.{u} → I → Prop
  tag_congr : ∀ a b, Equiv a b → ∀ i, tag a i → tag b i
  code_tag : ∀ s f, tag (code s f) (out s)
  code_congr : ∀ s f g, (∀ k, Equiv (f k) (g k)) → Equiv (code s f) (code s g)

def RecSig.toPiSig {I : Type u} (S : RecSig I) : PiSig.{u} where
  Sh := S.Sh
  Field := S.Field
  depth := S.depth
  tel := fun s k => (S.tel s k).tel
  code := fun s f => S.code s (fun k => (S.tel s k).encode (f k))
  ok := fun s f => ∀ k p, S.tag ((S.tel s k).tel.flatten (f k) p) ((S.tel s k).result p)
  code_congr := fun s _ _ h => S.code_congr s _ _ (fun k => (S.tel s k).encode_congr _ _ (h k))
  ok_congr := fun _ _ _ h hf k p => S.tag_congr _ _ (h k p) _ (hf k p)

def RecSig.family {I : Type u} (S : RecSig I) (i : I) : PSet.{u} :=
  sep (fun z => S.tag z i) (gSet S.toPiSig.toGSig)

/-- A local, explicit representation of all recursive children. This is
DATA, not a global choice principle or a closure hypothesis. -/
structure RecSig.Args {I : Type u} (S : RecSig I) (s : S.Sh) where
  trees : (k : S.Field s) → (S.tel s k).tel.Value (fun _ => GT S.toPiSig.toGSig)
  valid : ∀ k, (S.tel s k).tel.All (fun _ w => ValidW S.toPiSig.toGSig w) (trees k)
  indexed : ∀ k p, S.tag
    (decG S.toPiSig.toGSig ((S.tel s k).tel.flatten (trees k) p)) ((S.tel s k).result p)

def RecSig.Args.values {I : Type u} {S : RecSig I} {s : S.Sh} (a : S.Args s) :
    (k : S.Field s) → PiTel.Value.{u, u + 1} (S.tel s k).tel (fun _ => PSet.{u}) :=
  fun k => (S.tel s k).tel.unflatten
    (fun p => decG S.toPiSig.toGSig ((S.tel s k).tel.flatten (a.trees k) p))

/-- Exact product relation of the represented children, including indices. -/
theorem RecSig.Args.related {I : Type u} {S : RecSig I} {s : S.Sh} (a : S.Args s)
    (k : S.Field s) : (S.tel s k).Rel S.family (a.values k) := by
  apply (PiTel.all_iff _ _ _).mpr
  intro p
  rw [RecSig.Args.values, PiTel.flatten_unflatten]
  exact mem_sep.mpr ⟨⟨(S.tel s k).tel.flatten (a.trees k) p,
    (PiTel.all_iff _ _ _).mp (a.valid k) p⟩, a.indexed k p, Equiv.rfl⟩

/-- The producer composes field interpretation and guarded W construction.
Every supplied field is its represented total graph; the conclusion pays
both input product typing and output family membership. -/
theorem RecSig.produce {I : Type u} (S : RecSig I) (s : S.Sh) (a : S.Args s)
    (f : S.Field s → PSet.{u})
    (hf : ∀ k, Equiv (f k) ((S.tel s k).encode (a.values k))) :
    (∀ k, f k ∈ (S.tel s k).denote S.family) ∧
      S.code s f ∈ S.family (S.out s) := by
  constructor
  · intro k
    exact mem_congr_left (hf k).symm ((S.tel s k).encode_mem S.family _ (a.related k))
  · have hv : ValidW S.toPiSig.toGSig (S.toPiSig.roll s a.trees) := by
      apply S.toPiSig.roll_valid s a.trees a.valid
      intro k p
      simpa only [RecSig.toPiSig, PiTel.flatten_unflatten] using a.indexed k p
    have hm : S.code s (fun k => (S.tel s k).encode (a.values k)) ∈ S.family (S.out s) :=
      mem_sep.mpr ⟨⟨S.toPiSig.roll s a.trees, hv⟩, S.code_tag s _, Equiv.rfl⟩
    exact mem_congr_left (S.code_congr s _ f (fun k => (hf k).symm)) hm
/-- Elimination for extensional predicates on decoded guarded trees.
Every child contributes an induction hypothesis; guards remain premises
of the constructor case. No finite-height restriction is imposed. -/
theorem PiSig.induction_mem (S : PiSig.{u}) (Q : PSet.{u} → Prop)
    (hQ : ∀ a b, Equiv a b → Q a → Q b)
    (step : ∀ s f, (∀ k, (S.tel s k).All (fun _ z => Q z) (f k)) →
      S.ok s f → Q (S.code s f)) :
    ∀ z, z ∈ gSet S.toGSig → Q z := by
  have key : ∀ w, ValidW S.toGSig w → Q (decG S.toGSig w) := by
    intro w hw
    induction hw with
    | sup s g hg hok ih =>
      apply step s (fun k => (S.tel s k).unflatten (fun p => decG S.toGSig (g ⟨k, p⟩)))
      · intro k
        apply (PiTel.all_iff _ _ _).mpr
        intro p
        simpa only [PiTel.flatten_unflatten] using ih ⟨k, p⟩
      · exact hok
  intro z ⟨⟨w, hw⟩, hz⟩
  exact hQ _ _ hz (key w hw)
/-- General constructor closure from actual dependent-product members.
The only ambient data is the landed F3 Choice premise at this universe;
it is explicit, not an added axiom. No tree representation or closure
premise is demanded of the caller. -/
theorem RecSig.produce_of_mem {I : Type u} (ch : Choice.{u}) (S : RecSig I)
    (s : S.Sh) (f : S.Field s → PSet.{u})
    (hf : ∀ k, f k ∈ (S.tel s k).denote S.family) :
    S.code s f ∈ S.family (S.out s) := by
  let r := fun k => (S.tel s k).read (f k)
  have hr := fun k => ((S.tel s k).read_spec S.family (hf k)).1
  have hex : ∀ k p, ∃ w : GT S.toPiSig.toGSig,
      ValidW S.toPiSig.toGSig w ∧ S.tag (decG S.toPiSig.toGSig w) ((S.tel s k).result p) ∧
        Equiv (decG S.toPiSig.toGSig w) ((S.tel s k).tel.flatten (r k) p) := by
    intro k p
    have hp := (PiTel.all_iff _ _ _).mp (hr k) p
    obtain ⟨w, ht, he⟩ := mem_sep.mp hp
    exact ⟨w.1, w.2, ht, he⟩
  let pick := fun k p => ch (α := ULift.{u + 1} (GT S.toPiSig.toGSig))
    (fun w => ValidW S.toPiSig.toGSig w.down ∧
      S.tag (decG S.toPiSig.toGSig w.down) ((S.tel s k).result p) ∧
      Equiv (decG S.toPiSig.toGSig w.down) ((S.tel s k).tel.flatten (r k) p))
    (let ⟨w, hw⟩ := hex k p; ⟨⟨w⟩, hw⟩)
  let a : S.Args s := {
    trees := fun k => (S.tel s k).tel.unflatten (fun p => (pick k p).1.down)
    valid := fun k => (PiTel.all_iff _ _ _).mpr (fun p => by
      simpa only [PiTel.flatten_unflatten] using (pick k p).2.1)
    indexed := fun k p => by
      simpa only [PiTel.flatten_unflatten] using (pick k p).2.2.1
  }
  apply (S.produce s a f ?_).2
  intro k
  apply ((S.tel s k).read_spec S.family (hf k)).2.trans
  apply (S.tel s k).encode_congr
  intro p
  simpa only [RecSig.Args.values, PiTel.flatten_unflatten] using (pick k p).2.2.2.symm
end Rcic.F3.PSet
