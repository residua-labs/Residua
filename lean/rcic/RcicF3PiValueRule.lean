import rcic.RcicF3PiValue
/-! Constructor signatures extracted from literal normalized Prop syntax.
Shapes and recursive branch guards are produced from actual fitting tuples.
The exact predicate equation and constructor membership are checked; semantic
result typehood comes from the hereditary type derivation. This component
does not reverse hidden normalization or produce universal group closure.
`closure_claim = 0`. -/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiValueRule
open Rcic.Declarative PiIndex PiValue
universe u

/-- Domain membership descends to the extensional complete-argument index. -/
def fits (M : Interp.{u}) (σ : Nat → Nat) (ds : List (Expr Nat))
    (ρ : Nat → PSet.{u}) : Index.{u} → Prop :=
  Quotient.lift (TelFits M σ ds ρ) (fun _ _ h => propext
    ⟨TelFits_congr M σ ds (fun _ => Equiv.rfl) h,
      TelFits_congr M σ ds (fun _ => Equiv.rfl) h.symm⟩)

/-- Elementary computation, with no representative choice. -/
theorem fits_key (M : Interp.{u}) (σ : Nat → Nat) (ds : List (Expr Nat))
    (ρ : Nat → PSet.{u}) (xs : List PSet.{u}) :
    fits M σ ds ρ (key xs) ↔ TelFits M σ ds ρ xs := by
  exact Iff.rfl

/-- The family leaf is a positive predicate plus a candidate-independent domain guard. -/
theorem leaf_ed (M : Interp.{u}) (σ : Nat → Nat) (φ : Index.{u} → Prop)
    (ds : List (Expr Nat)) (ρ : Nat → PSet.{u}) (xs : List PSet.{u})
    (hl : xs.length = ds.length) :
    Equiv (tv (fits M σ ds ρ (key xs) ∧ φ (key xs)))
      (Ed M (fapps (value M σ φ ds ρ) xs)) := by
  apply ext
  intro z
  rw [mem_tv, apply_mem_iff M σ φ ds ρ xs hl z]
  exact ⟨fun ⟨⟨hf, hp⟩, hz⟩ => ⟨(fits_key M σ ds ρ xs).mp hf, hp, hz⟩,
    fun ⟨hf, hp, hz⟩ => ⟨⟨(fits_key M σ ds ρ xs).mpr hf, hp⟩, hz⟩⟩

/-- Exact normalized field equation with an explicit positive leaf predicate. -/
theorem recursive_ed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (φ : List Nat → Index.{4} → Prop) (famDs : List (Expr Nat))
    (σ : Nat → Nat) (ls : List Level) (ds args : List (Expr Nat))
    (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false)
    (hl : args.length = famDs.length) (ρ : Nat → PSet.{4}) :
    let vs := ls.map (evalTotal σ)
    let X := table P μ φ famDs
    let M := mkM P (upd μ f X)
    Equiv (Ed M ((PiIndex.tel (mkM P μ) σ ds args ρ).erasedType M
      (fun i => tv (fits (mkM P μ) (σOf vs) famDs ρ0 i ∧ φ vs i))))
      (Ed M (den M σ ρ (policyPi ds (foldApps (.const f ls) args)))) := by
  dsimp only
  let X := table P μ φ famDs
  have he := tel_free P μ f (μ f) X σ ds args hd ha ρ
  rw [PiIndependent.upd_self] at he
  rw [he]
  unfold PiIndex.tel
  apply PiIndependent.compile_ed (mkM P (upd μ f X)) σ
    (read (mkM P (upd μ f X)) σ args)
    (fun i => tv (fits (mkM P μ) (σOf (ls.map (evalTotal σ))) famDs ρ0 i ∧
      φ (ls.map (evalTotal σ)) i)) (fun _ => dich_tv _)
    (foldApps (.const f ls) args)
  intro ρ'
  rw [PiIndependent.leaf_read P μ f X σ ls args ha ρ']
  have hr := read_free P μ f X (μ f) σ args ha ρ'
  rw [PiIndependent.upd_self] at hr
  rw [hr]
  exact leaf_ed (mkM P μ) (σOf (ls.map (evalTotal σ)))
    (φ (ls.map (evalTotal σ))) famDs ρ0 (PiIndependent.leafArgs P μ σ args ρ')
    ((List.length_map _ _).trans hl)

/-- Normalized raw fields are exactly empty proof values with valid guarded branches. -/
theorem recursive_mem_iff (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (φ : List Nat → Index.{4} → Prop) (famDs : List (Expr Nat))
    (σ : Nat → Nat) (ls : List Level) (ds args : List (Expr Nat))
    (hd : ∀ e ∈ ds, occursConst f e = false)
    (ha : ∀ e ∈ args, occursConst f e = false)
    (hl : args.length = famDs.length) (ρ : Nat → PSet.{4}) (z : PSet.{4}) :
    let vs := ls.map (evalTotal σ)
    let M := mkM P (upd μ f (table P μ φ famDs))
    let t := PiIndex.tel (mkM P μ) σ ds args ρ
    z ∈ Ed M (den M σ ρ (policyPi ds (foldApps (.const f ls) args))) ↔
      Equiv z pempty ∧ ∀ p,
        fits (mkM P μ) (σOf vs) famDs ρ0 (t.result p) ∧ φ vs (t.result p) := by
  dsimp only
  let M := mkM P (upd μ f (table P μ φ famDs))
  let t := PiIndex.tel (mkM P μ) σ ds args ρ
  have ht : t.DomainsDich := PiSyntaxCompile.compile_domains (mkM P μ) σ
    (read (mkM P μ) σ args) ds ρ
  have he := recursive_ed P μ f φ famDs σ ls ds args hd ha hl ρ
  have hi := PiPropField.member_iff M t ht
    (fun i => fits (mkM P μ) (σOf (ls.map (evalTotal σ))) famDs ρ0 i ∧
      φ (ls.map (evalTotal σ)) i) z
  exact ⟨fun hz => hi.mp (mem_congr_right he.symm hz),
    fun hz => mem_congr_right he (hi.mpr hz)⟩

inductive FieldSpec where
  | plain (A : Expr Nat)
  | recursive (ds args : List (Expr Nat))

def fieldExpr (f : Nat) (ls : List Level) : FieldSpec → Expr Nat
  | .plain A => A
  | .recursive ds args => policyPi ds (foldApps (.const f ls) args)

def Clean (f ar : Nat) : List FieldSpec → Prop
  | [] => True
  | .plain A :: fs => occursConst f A = false ∧ Clean f ar fs
  | .recursive ds args :: fs =>
      (∀ A ∈ ds, occursConst f A = false) ∧
      (∀ A ∈ args, occursConst f A = false) ∧ args.length = ar ∧ Clean f ar fs

/-- Shape stores plain data, canonical recursive proofs and domain guards.
It stores no recursive candidate predicate or constructor-closure witness. -/
inductive Shape (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (vs : List Nat) (famDs : List (Expr Nat)) :
    List FieldSpec → (Nat → PSet.{4}) → Type 5 where
  | nil (ρ) : Shape P μ σ vs famDs [] ρ
  | plain {A fs ρ} (x : PSet.{4}) (hx : x ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ A))
      (tail : Shape P μ σ vs famDs fs (vcons x ρ)) :
      Shape P μ σ vs famDs (.plain A :: fs) ρ
  | recursive {ds args fs ρ}
      (guard : ∀ p, fits (mkM P μ) (σOf vs) famDs ρ0
        ((PiIndex.tel (mkM P μ) σ ds args ρ).result p))
      (tail : Shape P μ σ vs famDs fs (vcons pempty ρ)) :
      Shape P μ σ vs famDs (.recursive ds args :: fs) ρ

def Shape.values {P μ σ vs famDs} : ∀ {fs ρ}, Shape P μ σ vs famDs fs ρ → List PSet.{4}
  | _, _, .nil _ => []
  | _, _, .plain x _ tail => x :: tail.values
  | _, _, .recursive _ tail => pempty :: tail.values

inductive Place : List FieldSpec → Type where
  | next (a : FieldSpec) {fs} : Place fs → Place (a :: fs)
  | here {ds args fs} : Place (.recursive ds args :: fs)

def Place.depth : ∀ {fs}, Place fs → Nat
  | _, .next _ p => p.depth
  | _, @Place.here ds _ _ => ds.length

def Shape.tel {P μ σ vs famDs} : ∀ {fs ρ} (_s : Shape P μ σ vs famDs fs ρ)
    (p : Place fs), RecTel.{4,5} Index.{4} p.depth
  | _, _, .plain _ _ tail, .next _ p => tail.tel p
  | _, _, .recursive _ tail, .next _ p => tail.tel p
  | _, _, @Shape.recursive _ _ _ _ _ ds args _ ρ _ _, .here =>
      PiIndex.tel (mkM P μ) σ ds args ρ

theorem Shape.tel_domains {P μ σ vs famDs} : ∀ {fs ρ}
    (s : Shape P μ σ vs famDs fs ρ) (p : Place fs), (s.tel p).DomainsDich := by
  intro fs ρ s
  induction s with
  | nil => intro p; cases p
  | plain x hx tail ih => intro p; cases p with
    | next _ p => exact ih p
  | recursive guard tail ih => intro p; cases p with
    | next _ p => exact ih p
    | here => exact PiSyntaxCompile.compile_domains _ _ _ _ _

/-- Exact constructor-tuple equation for normalized syntax. The signature
shape contains only ordinary plain-field membership and domain guards. -/
theorem Shape.fits_iff (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (φ : List Nat → Index.{4} → Prop) (famDs : List (Expr Nat))
    (σ : Nat → Nat) (ls : List Level) : ∀ {fs ρ}
    (s : Shape P μ σ (ls.map (evalTotal σ)) famDs fs ρ),
    Clean f famDs.length fs →
    (TelFits (mkM P (upd μ f (table P μ φ famDs))) σ (fs.map (fieldExpr f ls)) ρ s.values ↔
      ∀ k p, φ (ls.map (evalTotal σ)) ((s.tel k).result p)) := by
  intro fs ρ s
  induction s with
  | nil =>
    intro _
    constructor
    · intro _ k; cases k
    · intro _; trivial
  | @plain A fs ρ x hx tail ih =>
    intro hc
    have he := PiIndependent.den_free P μ f (table P μ φ famDs) (μ f) σ A hc.1 ρ
    rw [PiIndependent.upd_self] at he
    have hx' : x ∈ Ed (mkM P (upd μ f (table P μ φ famDs)))
        (den (mkM P (upd μ f (table P μ φ famDs))) σ ρ A) := by
      rw [he]
      exact hx
    change (x ∈ _ ∧ TelFits _ _ _ _ tail.values) ↔ _
    constructor
    · intro h k p
      cases k with
      | next _ k => exact (ih hc.2).mp h.2 k p
    · intro h
      exact ⟨hx', (ih hc.2).mpr (fun k p => h (.next _ k) p)⟩
  | @recursive ds args fs ρ guard tail ih =>
    intro hc
    have hi := recursive_mem_iff P μ f φ famDs σ ls ds args hc.1 hc.2.1 hc.2.2.1 ρ pempty
    change (pempty ∈ _ ∧ TelFits _ _ _ _ tail.values) ↔ _
    constructor
    · intro h k p
      cases k with
      | next _ k => exact (ih hc.2.2.2).mp h.2 k p
      | here => exact ((hi.mp h.1).2 p).2
    · intro h
      exact ⟨hi.mpr ⟨Equiv.rfl, fun p => ⟨guard p, h .here p⟩⟩,
        (ih hc.2.2.2).mpr (fun k p => h (.next _ k) p)⟩

structure Constructor where
  fields : List FieldSpec
  result : List (Expr Nat)

def signature (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (vs : List Nat) (famDs : List (Expr Nat))
    (cs : List Constructor) (ρ : Nat → PSet.{4}) : PiPropProducer.Sig.{4,5,5} Index.{4} where
  Sh := (c : Fin cs.length) × Shape P μ σ vs famDs (cs[c]).fields ρ
  Field s := ULift.{5} (Place (cs[s.1]).fields)
  depth _ p := p.down.depth
  tel s p := s.2.tel p.down
  out s := read (mkM P μ) σ (cs[s.1]).result (push s.2.values ρ)

theorem signature_domains (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (σ : Nat → Nat) (vs : List Nat) (famDs : List (Expr Nat))
    (cs : List Constructor) (ρ : Nat → PSet.{4})
    (s : (signature P μ σ vs famDs cs ρ).Sh)
    (k : (signature P μ σ vs famDs cs ρ).Field s) :
    ((signature P μ σ vs famDs cs ρ).tel s k).DomainsDich := by
  exact s.2.tel_domains k.down

def predicate (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (famDs : List (Expr Nat)) (cs : List Constructor) (vs : List Nat) : Index.{4} → Prop :=
  PiPropProducer.Valid (signature P μ (σOf vs) vs famDs cs ρ0)

/-- Normalized syntax supplies an actual inductive constructor step. -/
theorem produce (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (famDs : List (Expr Nat)) (cs : List Constructor) (vs : List Nat)
    (c : Fin cs.length) (s : Shape P μ (σOf vs) vs famDs (cs[c]).fields ρ0)
    (hc : Clean f famDs.length (cs[c]).fields)
    (hs : TelFits (mkM P (upd μ f (table P μ (predicate P μ famDs cs) famDs)))
      (σOf vs) ((cs[c]).fields.map (fieldExpr f ((List.range vs.length).map Level.param)))
      ρ0 s.values) :
    predicate P μ famDs cs vs (read (mkM P μ) (σOf vs) (cs[c]).result (push s.values ρ0)) := by
  have hi := Shape.fits_iff P μ f (predicate P μ famDs cs) famDs
    (σOf vs) ((List.range vs.length).map Level.param) (fs := (cs[c]).fields) (ρ := ρ0)
  rw [map_param_σOf] at hi
  have hb := (hi s hc).mp hs
  exact PiPropProducer.Valid.sup (S := signature P μ (σOf vs) vs famDs cs ρ0)
    ⟨c, s⟩ (fun k p => hb k.down p)

/-- Actual fitting tuples produce shapes; a shape inhabitant is not an input wall. -/
theorem shape_of_fits (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (φ : List Nat → Index.{4} → Prop) (famDs : List (Expr Nat))
    (σ : Nat → Nat) (ls : List Level) : ∀ fs,
    Clean f famDs.length fs → ∀ ρ xs,
    TelFits (mkM P (upd μ f (table P μ φ famDs))) σ (fs.map (fieldExpr f ls)) ρ xs →
    ∃ s : Shape P μ σ (ls.map (evalTotal σ)) famDs fs ρ, LEq xs s.values := by
  intro fs
  induction fs with
  | nil =>
    intro _ ρ xs hx
    cases xs with
    | nil => exact ⟨.nil ρ, True.intro⟩
    | cons x xs => exact False.elim hx
  | cons a fs ih =>
    intro hc ρ xs hx
    cases xs with
    | nil => exact False.elim hx
    | cons x xs =>
      cases a with
      | plain A =>
        have he := PiIndependent.den_free P μ f (table P μ φ famDs) (μ f) σ A hc.1 ρ
        rw [PiIndependent.upd_self] at he
        have hx' : x ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ A) := by
          have hh := hx.1
          change x ∈ Ed (mkM P μ) (den (mkM P (upd μ f (table P μ φ famDs))) σ ρ A) at hh
          rw [he] at hh
          exact hh
        obtain ⟨s, hs⟩ := ih hc.2 (vcons x ρ) xs hx.2
        exact ⟨.plain x hx' s, Equiv.rfl, hs⟩
      | recursive ds args =>
        have hi := (recursive_mem_iff P μ f φ famDs σ ls ds args
          hc.1 hc.2.1 hc.2.2.1 ρ x).mp hx.1
        have ht : TelFits (mkM P (upd μ f (table P μ φ famDs))) σ
            (fs.map (fieldExpr f ls)) (vcons pempty ρ) xs :=
          TelFits_congr _ _ _ (vcons_congr hi.1 (fun _ => Equiv.rfl)) (LEq.refl xs) hx.2
        obtain ⟨s, hs⟩ := ih hc.2.2.2 (vcons pempty ρ) xs ht
        exact ⟨.recursive (fun p => (hi.2 p).1) s, hi.1, hs⟩

/-- Every fitting normalized constructor tuple enters the extracted predicate;
canonical proof slots are constructed internally. -/
theorem close_tuple (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (famDs : List (Expr Nat)) (cs : List Constructor) (vs : List Nat)
    (c : Fin cs.length) (hc : Clean f famDs.length (cs[c]).fields)
    (xs : List PSet.{4})
    (hx : TelFits (mkM P (upd μ f (table P μ (predicate P μ famDs cs) famDs)))
      (σOf vs) ((cs[c]).fields.map (fieldExpr f ((List.range vs.length).map Level.param)))
      ρ0 xs) :
    predicate P μ famDs cs vs (read (mkM P μ) (σOf vs) (cs[c]).result (push xs ρ0)) := by
  have hi := shape_of_fits P μ f (predicate P μ famDs cs) famDs
    (σOf vs) ((List.range vs.length).map Level.param) (cs[c]).fields
  rw [map_param_σOf] at hi
  obtain ⟨s, hs⟩ := hi hc ρ0 xs hx
  have ht := TelFits_congr (mkM P (upd μ f (table P μ (predicate P μ famDs cs) famDs)))
    (σOf vs) ((cs[c]).fields.map (fieldExpr f ((List.range vs.length).map Level.param)))
    (fun _ => Equiv.rfl) hs hx
  have hp := produce P μ f famDs cs vs c s hc ht
  have he := read_congr (mkM P μ) (σOf vs) (cs[c]).result
    (push_congr (ρ := ρ0) (ρ' := ρ0) hs (fun _ => Equiv.rfl))
  rw [he]
  exact hp

/-- Actual normalized constructor closure. The result-domain guard follows
from semantic typehood, rather than being a constructor-closure premise. -/
theorem constructor_mem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (famDs : List (Expr Nat)) (cs : List Constructor) (vs : List Nat)
    (c : Fin cs.length) (hc : Clean f famDs.length (cs[c]).fields)
    (ha : ∀ e ∈ (cs[c]).result, occursConst f e = false)
    (hl : (cs[c]).result.length = famDs.length) (xs : List PSet.{4})
    (hx : TelFits (mkM P (upd μ f (table P μ (predicate P μ famDs cs) famDs)))
      (σOf vs) ((cs[c]).fields.map (fieldExpr f ((List.range vs.length).map Level.param)))
      ρ0 xs)
    (v : Level)
    (hk : let M := mkM P (upd μ f (table P μ (predicate P μ famDs cs) famDs))
      den M (σOf vs) (push xs ρ0)
        (foldApps (.const f ((List.range vs.length).map Level.param)) (cs[c]).result) ∈
      Ed M (den M (σOf vs) (push xs ρ0) (.sort v))) :
    let M := mkM P (upd μ f (table P μ (predicate P μ famDs cs) famDs))
    pempty ∈ Ed M (den M (σOf vs) (push xs ρ0)
      (foldApps (.const f ((List.range vs.length).map Level.param)) (cs[c]).result)) := by
  dsimp only
  let φ := predicate P μ famDs cs
  let X := table P μ φ famDs
  let ys := PiIndependent.leafArgs P μ (σOf vs) (cs[c]).result (push xs ρ0)
  have he := PiIndependent.leaf_read P μ f X (σOf vs)
    ((List.range vs.length).map Level.param) (cs[c]).result ha (push xs ρ0)
  rw [map_param_σOf] at he
  have hn : ¬ Equiv (fapps (X vs) ys) pempty := by
    rw [← he]
    exact ne_of_mem_sort rfl hk
  have hy : ys.length = famDs.length := (List.length_map _ _).trans hl
  have hf := fits_of_fapps_ne (mkM P μ) (σOf vs) (endValue_resp (φ vs) famDs.length)
    (.sort .zero) famDs ρ0 ys hy hn
  have hp := close_tuple P μ f famDs cs vs c hc xs hx
  rw [he]
  exact (apply_mem_iff (mkM P μ) (σOf vs) (φ vs) famDs ρ0 ys hy pempty).mpr
    ⟨hf, hp, Equiv.rfl⟩

/-- Literal constructor equation for the predicate extracted from normalized syntax. -/
theorem predicate_equation (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (famDs : List (Expr Nat)) (cs : List Constructor) (vs : List Nat)
    (hc : ∀ c : Fin cs.length, Clean f famDs.length (cs[c]).fields) (i : Index.{4}) :
    predicate P μ famDs cs vs i ↔ ∃ (c : Fin cs.length) (xs : List PSet.{4}),
      TelFits (mkM P (upd μ f (table P μ (predicate P μ famDs cs) famDs)))
        (σOf vs) ((cs[c]).fields.map (fieldExpr f ((List.range vs.length).map Level.param)))
        ρ0 xs ∧ read (mkM P μ) (σOf vs) (cs[c]).result (push xs ρ0) = i := by
  constructor
  · intro hi
    cases hi with
    | sup s hg =>
      have ht := Shape.fits_iff P μ f (predicate P μ famDs cs) famDs (σOf vs)
        ((List.range vs.length).map Level.param) (fs := (cs[s.1]).fields) (ρ := ρ0)
      rw [map_param_σOf] at ht
      exact ⟨s.1, s.2.values, (ht s.2 (hc s.1)).mpr (fun k p => hg ⟨k⟩ p), rfl⟩
  · rintro ⟨c, xs, hx, hi⟩
    rw [← hi]
    exact close_tuple P μ f famDs cs vs c (hc c) xs hx

/-- The hereditary type derivation supplies semantic result typehood. This
corollary is restricted to the literal normalized constructor syntax. -/
theorem constructor_mem_typed (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (f : Nat)
    (famDs : List (Expr Nat)) (cs : List Constructor) (vs : List Nat)
    (c : Fin cs.length) (hc : Clean f famDs.length (cs[c]).fields)
    (ha : ∀ e ∈ (cs[c]).result, occursConst f e = false)
    (hl : (cs[c]).result.length = famDs.length)
    {E : ResolvedEnv} {n : Nat} {u : Level}
    (d : HasTyT E n []
      (policyPi ((cs[c]).fields.map (fieldExpr f ((List.range vs.length).map Level.param)))
        (foldApps (.const f ((List.range vs.length).map Level.param)) (cs[c]).result)) (.sort u))
    (hd : HSoundT (mkM P (upd μ f (table P μ (predicate P μ famDs cs) famDs))) (σOf vs) d)
    (xs : List PSet.{4})
    (hx : TelFits (mkM P (upd μ f (table P μ (predicate P μ famDs cs) famDs)))
      (σOf vs) ((cs[c]).fields.map (fieldExpr f ((List.range vs.length).map Level.param)))
      ρ0 xs) :
    let M := mkM P (upd μ f (table P μ (predicate P μ famDs cs) famDs))
    pempty ∈ Ed M (den M (σOf vs) (push xs ρ0)
      (foldApps (.const f ((List.range vs.length).map Level.param)) (cs[c]).result)) := by
  obtain ⟨v, hv⟩ := tel_end_type
    (foldApps (.const f ((List.range vs.length).map Level.param)) (cs[c]).result)
    ((cs[c]).fields.map (fieldExpr f ((List.range vs.length).map Level.param)))
    d hd ρ0 xs True.intro hx
  exact constructor_mem P μ f famDs cs vs c hc ha hl xs hx v hv

end Rcic.F3.PSet.PiValueRule
