import rcic.RcicNativeTypedModelIota

/-!
# RcicNativeTypedModelIotaSound — the `IotaSoundT` premise is FALSE: kernel counterexample

The `approxDI_iotaS` port does not go through.  `IotaSoundT E` quantifies over
*every* structured witness `w : IotaWitnessS E`, including proposition-family
ones.  For a `PropFamilyS` witness the `recursorProp` clause interprets **all**
constructor fields at the empty demand `[]`, i.e. the left-hand side's schema
evaluation runs in an environment whose field positions are `⊥`-only.  The
right-hand side `iotaRhsOfS w = instPrefix (w.preMajor ++ w.fields) schema`
still substitutes the *actual* field terms, so any non-`⊥` compact a minor
genuinely demands of a field appears on the right and is missing on the left.

This is real whenever the family is propositional but a constructor field is
not.  The fixture below is the minimal one — the `Exists`-shape

    Ex   : Π (α : Sort 1) (p : α → Prop), Prop          (ref 1, inductiveM)
    mk   : Π (α : Sort 1) (p : α → Prop) (w : α) (h : p w), Ex α p   (ref 2, ctor)
    Ex.r : Π (α : Sort 1) (p : α → Prop) (M : Π (_ : Ex α p), Sort 1)
             (m : Π (w : α) (h : p w), M (mk α p w h)) (x : Ex α p), M x
             (ref 3, recursorM)

plus a rigid axiom `N : Sort 1` at ref 0.  The witness `wEx` takes the minor

    m' := λ (_ : Sort 1) (_ : Sort 0). bvar 1

whose only step demands the compact `.spine 0 []` of `w` and returns it: the
contractum `m' w h` evaluates to `.spine 0 []` — a genuine compact of the
non-propositional field — while the lhs schema evaluation at field demand `[]`
can never fire that step.  So

    ApproxT exEnv ρ (iotaRhsOfS wEx) (.spine 0 [])    holds, and
    ApproxT exEnv ρ (iotaLhsOfS wEx) (.spine 0 [])    does not,

giving `not_iotaSoundT_ex : ¬ IotaSoundT exEnv`.  The obstruction for the port
is the `recursorProp` clause itself: its `w.fields.map (fun _ => [])` erases
demands of *non-proof* fields, which only a `kinds`-aware split (proof fields
erased, plain fields demanded) could keep sound.

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.FamModelKAudit

/-! ### §1 — the `Exists`-shaped environment -/

/-- `Π (α : Sort 1) (p : α → Prop), Prop`. -/
def exFamTy : Expr Nat :=
  .pi (.sort (.succ .zero))
    (.pi (.pi (.bvar 0) (.sort .zero)) (.sort .zero))

/-- `mk : Π (α : Sort 1) (p : α → Prop) (w : α) (h : p w), Ex α p`. -/
def exMkTy : Expr Nat :=
  .pi (.sort (.succ .zero))
    (.pi (.pi (.bvar 0) (.sort .zero))
      (.pi (.bvar 1)
        (.pi (.app (.bvar 1) (.bvar 0))
          (.app (.app (.const 1 []) (.bvar 3)) (.bvar 2)))))

/-- The derived minor domain `Π (w : α) (h : p w), M (mk α p w h)` at context
    `[α, p, M]`. -/
def exMinorDom : Expr Nat :=
  .pi (.bvar 2)
    (.pi (.app (.bvar 2) (.bvar 0))
      (.app (.bvar 2)
        (.app (.app (.app (.app (.const 2 []) (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0))))

/-- `Ex.rec : Π (α : Sort 1) (p : α → Prop) (M : Π (_ : Ex α p), Sort 1)
    (m : Π (w : α) (h : p w), M (mk α p w h)) (x : Ex α p), M x`. -/
def exRecTy : Expr Nat :=
  .pi (.sort (.succ .zero))
    (.pi (.pi (.bvar 0) (.sort .zero))
      (.pi (.pi (.app (.app (.const 1 []) (.bvar 1)) (.bvar 0)) (.sort (.succ .zero)))
        (.pi exMinorDom
          (.pi (.app (.app (.const 1 []) (.bvar 3)) (.bvar 2))
            (.app (.bvar 2) (.bvar 0))))))

def exAxMember : CheckedMember := ⟨.axiomM, 0, .sort (.succ .zero), none⟩
def exFamMember : CheckedMember := ⟨.inductiveM, 0, exFamTy, none⟩
def exMkMember : CheckedMember := ⟨.constructorM, 0, exMkTy, none⟩
def exRecMember : CheckedMember := ⟨.recursorM, 0, exRecTy, none⟩

def exB0 : ResolvedEnv := extendEnv emptyEnv 0 exAxMember
def exB1 : ResolvedEnv := extendEnv exB0 1 exFamMember
def exB2 : ResolvedEnv := extendEnv exB1 2 exMkMember
def exEnv : ResolvedEnv := extendEnv exB2 3 exRecMember

theorem exEnv_mem0 : exEnv.members 0 = some exAxMember := rfl
theorem exEnv_mem1 : exEnv.members 1 = some exFamMember := rfl
theorem exEnv_mem2 : exEnv.members 2 = some exMkMember := rfl
theorem exEnv_mem3 : exEnv.members 3 = some exRecMember := rfl

theorem exEnv_mem_ge4 {r : Nat} (h : 4 ≤ r) : exEnv.members r = none := by
  simp only [exEnv, exB2, exB1, exB0, extendEnv, emptyEnv]
  rw [if_neg (by omega : ¬ r = 3), if_neg (by omega : ¬ r = 2),
    if_neg (by omega : ¬ r = 1), if_neg (by omega : ¬ r = 0)]

/-- The refuting minor: `λ (_ : Sort 1) (_ : Sort 0). w`. -/
def exMinorArg : Expr Nat :=
  .lam (.sort (.succ .zero)) (.lam (.sort .zero) (.bvar 1))

/-- The witness's field values: both the rigid `N`. -/
def exFieldVal : Expr Nat := .const 0 []

/-- The constructor-major term `mk α p w h` at the chosen arguments. -/
def exCtorApp : Expr Nat :=
  foldApps (.const 2 []) [.const 0 [], .const 0 [], .const 0 [], .const 0 []]

/-- The schema `m w h` in the equation context `(α p M m w h)`. -/
def exSchema : Expr Nat := .app (.app (.bvar 2) (.bvar 1)) (.bvar 0)

/-- The full structured witness at `exEnv`. -/
def wEx : IotaWitnessS exEnv where
  recRef := 3
  ctorRef := 2
  ls := []
  lsC := []
  recMember := exRecMember
  ctorMember := exMkMember
  hrec := rfl
  hctor := rfl
  hrecK := rfl
  hctorK := rfl
  preMajor := [.const 0 [], .const 0 [], .const 0 [], exMinorArg]
  fields := [.const 0 [], .const 0 []]
  ctorParams := [.const 0 [], .const 0 []]
  familyRef := 1
  famMember := exFamMember
  hfam := rfl
  hfamK := rfl
  nparams := 2
  nindices := 0
  nMinors := 1
  ctorIdx := 0
  hctorParams := rfl
  hnpar := rfl
  hnidx := rfl
  hnmin := rfl
  hidx := by decide
  hctorIdx := rfl
  hrecIdx := rfl
  hpre := rfl
  ctorDoms := [.sort (.succ .zero), .pi (.bvar 0) (.sort .zero), .bvar 1,
    .app (.bvar 1) (.bvar 0)]
  ctorResult := .app (.app (.const 1 []) (.bvar 3)) (.bvar 2)
  hpeel := rfl
  hfamApp := rfl
  recDoms := [.sort (.succ .zero), .pi (.bvar 0) (.sort .zero),
    .pi (.app (.app (.const 1 []) (.bvar 1)) (.bvar 0)) (.sort (.succ .zero)),
    exMinorDom, .app (.app (.const 1 []) (.bvar 3)) (.bvar 2)]
  recBody := .app (.bvar 2) (.bvar 0)
  hpeelRec := rfl
  hrecBody := rfl
  hmajorTy := rfl
  hrecClosed := rfl
  hctorClosed := rfl
  hlsLen := rfl
  fuel := 8
  shapes := [.nonrecursive, .nonrecursive]
  hshapes := rfl
  schema := exSchema
  hschema := rfl
  hstable := iotaWitnessS_hstable_of_constsMemberFuel rfl rfl (by
    have hmem0 : exEnv.members 0 = some exAxMember := rfl
    have hmem1 : exEnv.members 1 = some exFamMember := rfl
    have hmem2 : exEnv.members 2 = some exMkMember := rfl
    have hmem3 : exEnv.members 3 = some exRecMember := rfl
    show iotaWitnessStableB exEnv 8
      [.bvar 1, .app (.bvar 1) (.bvar 0)] (fieldBvars 2)
      (lift 0 4 (ctorFieldTelRaw 2
        [.sort (.succ .zero), .pi (.bvar 0) (.sort .zero), .bvar 1,
          .app (.bvar 1) (.bvar 0)]
        (.app (.app (.const 1 []) (.bvar 3)) (.bvar 2)))) = true
    simp [iotaWitnessStableB, fieldBvars, ctorFieldTelRaw, lift,
      constsMemberFuel, hmem0, hmem1, hmem2, hmem3, exAxMember, exFamMember,
      exMkMember, exRecMember, transparent, instantiateLevels])
  hschemaScope := rfl

theorem exW_propFamily : PropFamilyS wEx := rfl

/-- The reduct is the explicit redex `m' w h`. -/
theorem wEx_rhs : iotaRhsOfS wEx =
    .app (.app exMinorArg exFieldVal) exFieldVal := by
  decide

/-! ### §2 — every witness at ref 3 is pinned to the `Ex` shape -/

theorem exW_family {w' : IotaWitnessS exEnv} (hw : w'.recRef = 3) :
    w'.familyRef = 1 ∧ w'.famMember = exFamMember := by
  have hidx : w'.recRef = w'.familyRef + 1 + w'.nMinors := w'.hrecIdx
  rw [hw] at hidx
  have hmin : 1 ≤ w'.nMinors := by have := w'.hidx; omega
  rcases Nat.lt_or_ge w'.familyRef 1 with hlt | hge
  · have h0 : w'.familyRef = 0 := by omega
    have hf := w'.hfam
    rw [h0, exEnv_mem0] at hf
    have hm : w'.famMember = exAxMember := (Option.some.inj hf).symm
    have hk := w'.hfamK
    rw [hm] at hk
    exact absurd hk (by decide)
  · have h1 : w'.familyRef = 1 := by omega
    have hf := w'.hfam
    rw [h1, exEnv_mem1] at hf
    have hm : w'.famMember = exFamMember := (Option.some.inj hf).symm
    exact ⟨h1, hm⟩

theorem exW_shape {w' : IotaWitnessS exEnv} (hw : w'.recRef = 3) :
    w'.nMinors = 1 ∧ w'.ctorIdx = 0 ∧ w'.familyRef = 1 ∧ w'.famMember = exFamMember ∧
      w'.recMember = exRecMember ∧ w'.ctorMember = exMkMember ∧ w'.nparams ≤ 2 := by
  obtain ⟨hf, hfm⟩ := exW_family hw
  have hidx : w'.recRef = w'.familyRef + 1 + w'.nMinors := w'.hrecIdx
  rw [hw, hf] at hidx
  have hnm : w'.nMinors = 1 := by omega
  have hrm : w'.recMember = exRecMember := by
    have h := w'.hrec
    rw [hw, exEnv_mem3] at h
    exact (Option.some.inj h).symm
  have hci : w'.ctorIdx = 0 := by
    have hcr : w'.ctorRef = w'.familyRef + 1 + w'.ctorIdx := w'.hctorIdx
    rw [hf] at hcr
    rcases Nat.lt_or_ge w'.ctorIdx 1 with hlt | hge
    · omega
    · have hge3 : 3 ≤ w'.ctorRef := by omega
      have h := w'.hctor
      rcases Nat.lt_or_ge w'.ctorRef 4 with hlt4 | hge4
      · have hr3 : w'.ctorRef = 3 := by omega
        rw [hr3, exEnv_mem3] at h
        have hm : w'.ctorMember = exRecMember := (Option.some.inj h).symm
        have hk := w'.hctorK
        rw [hm] at hk
        exact absurd hk (by decide)
      · rw [exEnv_mem_ge4 hge4] at h
        exact Option.noConfusion h
  have hcm : w'.ctorMember = exMkMember := by
    have hcr : w'.ctorRef = w'.familyRef + 1 + w'.ctorIdx := w'.hctorIdx
    rw [hf, hci] at hcr
    have hr2 : w'.ctorRef = 2 := by omega
    have h := w'.hctor
    rw [hr2, exEnv_mem2] at h
    exact (Option.some.inj h).symm
  have hnp : w'.nparams ≤ 2 := by
    have h := w'.hnidx
    rw [hfm, show piCount exFamMember.mtype = 2 from rfl] at h
    omega
  exact ⟨hnm, hci, hf, hfm, hrm, hcm, hnp⟩

theorem exW_prop {w' : IotaWitnessS exEnv} (hw : w'.recRef = 3) : PropFamilyS w' := by
  obtain ⟨_, _, _, hfm, _, _, _⟩ := exW_shape hw
  show piBody w'.famMember.mtype = .sort .zero
  rw [hfm]
  rfl

/-- Every witness at ref 3 has the 4-long preMajor and ≥ 2 fields. -/
theorem exW_lengths {w' : IotaWitnessS exEnv} (hw : w'.recRef = 3) :
    w'.preMajor.length = 4 ∧ w'.fields.length = 4 - w'.nparams ∧
      w'.nparams + w'.nindices = 2 := by
  obtain ⟨hnm, _, _, hfm, hrm, hcm, _⟩ := exW_shape hw
  have hpre := w'.hpre
  have hnmin := w'.hnmin
  have hnpar := w'.hnpar
  have hnidx := w'.hnidx
  rw [hrm, show piCount exRecMember.mtype = 5 from rfl] at hnmin
  rw [hcm, show piCount exMkMember.mtype = 4 from rfl] at hnpar
  rw [hfm, show piCount exFamMember.mtype = 2 from rfl] at hnidx
  exact ⟨by omega, by omega, by omega⟩

/-- The schema of a ref-3 witness is `foldApps` of the minor bvar onto a spine
    whose first argument is the first field bvar. -/
theorem exW_schema_head {w' : IotaWitnessS exEnv} (hw : w'.recRef = 3) :
    ∃ rest, w'.schema =
      foldApps (.bvar (w'.fields.length + w'.nindices + (w'.nMinors - 1 - w'.ctorIdx)))
        (.bvar (w'.fields.length - 1) :: rest) := by
  obtain ⟨_, _, _, _, _, _, hnp⟩ := exW_shape hw
  obtain ⟨_, hfl, _⟩ := exW_lengths hw
  have hfl2 : 2 ≤ w'.fields.length := by omega
  have hbvars : fieldBvars w'.fields.length =
      Expr.bvar (w'.fields.length - 1) :: fieldBvars (w'.fields.length - 1) := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w'.fields.length ≠ 0)
    rw [hn, show n + 1 - 1 = n from rfl]
    simp [fieldBvars, List.range_succ]
  have hschema := w'.hschema
  simp only [iotaOpenRhs, Option.map_eq_some'] at hschema
  obtain ⟨args, hi, hsch⟩ := hschema
  rw [hbvars] at hi
  have harg : ∃ rest, args = Expr.bvar (w'.fields.length - 1) :: rest := by
    cases hsh : w'.shapes with
    | nil =>
        rw [hsh] at hi
        simp [iotaArgs] at hi
    | cons s ss =>
        rw [hsh] at hi
        cases s with
        | nonrecursive =>
            cases hT : lift 0 (w'.fields.length + 1 + w'.nMinors + w'.nindices)
                (ctorFieldTelRaw w'.nparams w'.ctorDoms w'.ctorResult) with
            | pi A B =>
                rw [hT] at hi
                simp only [iotaArgs] at hi
                rw [Option.map_eq_some'] at hi
                obtain ⟨rest, _, rfl⟩ := hi
                exact ⟨rest, rfl⟩
            | bvar i => rw [hT] at hi; simp [iotaArgs] at hi
            | sort l => rw [hT] at hi; simp [iotaArgs] at hi
            | const r ls => rw [hT] at hi; simp [iotaArgs] at hi
            | app f x => rw [hT] at hi; simp [iotaArgs] at hi
            | lam A B => rw [hT] at hi; simp [iotaArgs] at hi
            | letE A v B => rw [hT] at hi; simp [iotaArgs] at hi
            | lit t => rw [hT] at hi; simp [iotaArgs] at hi
        | recursive inner =>
            cases hT : lift 0 (w'.fields.length + 1 + w'.nMinors + w'.nindices)
                (ctorFieldTelRaw w'.nparams w'.ctorDoms w'.ctorResult) with
            | pi A B =>
                rw [hT] at hi
                cases inner with
                | zero =>
                    simp only [iotaArgs] at hi
                    cases hpi : piTelescopeFuel exEnv w'.fuel A with
                    | none => rw [hpi] at hi; simp at hi
                    | some p =>
                        cases p with
                        | mk doms famApp =>
                            cases doms with
                            | nil =>
                                rw [hpi] at hi
                                simp only [] at hi
                                rw [Option.map_eq_some'] at hi
                                obtain ⟨rest, _, rfl⟩ := hi
                                exact ⟨_, rfl⟩
                            | cons _ _ => rw [hpi] at hi; simp at hi
                | succ inner' =>
                    simp only [iotaArgs] at hi
                    cases hfr : funRecArg exEnv w'.fuel
                        (.const w'.recRef (canonRecLevels w'.recMember.arity))
                        (preMajorBvars w'.nparams w'.nMinors w'.nindices w'.fields.length)
                        w'.nparams w'.nMinors (.bvar (w'.fields.length - 1)) A (inner' + 1) with
                    | none => rw [hfr] at hi; simp at hi
                    | some call =>
                        rw [hfr] at hi
                        rw [Option.map_eq_some'] at hi
                        obtain ⟨rest, _, rfl⟩ := hi
                        exact ⟨_, rfl⟩
            | bvar i => rw [hT] at hi; simp [iotaArgs] at hi
            | sort l => rw [hT] at hi; simp [iotaArgs] at hi
            | const r ls => rw [hT] at hi; simp [iotaArgs] at hi
            | app f x => rw [hT] at hi; simp [iotaArgs] at hi
            | lam A B => rw [hT] at hi; simp [iotaArgs] at hi
            | letE A v B => rw [hT] at hi; simp [iotaArgs] at hi
            | lit t => rw [hT] at hi; simp [iotaArgs] at hi
  obtain ⟨rest, rfl⟩ := harg
  exact ⟨rest, hsch.symm⟩

/-! ### §3 — environment lookups along `pushArgs` -/

/-- `pushArgs` beyond the pushed list reads the base env. -/
theorem envT_pushArgs_ge {Ss : List (CptT → Prop)} {ρ : EnvT} {i : Nat}
    (hi : Ss.length ≤ i) :
    EnvT.pushArgs Ss ρ i = ρ (i - Ss.length) := by
  induction Ss generalizing ρ i with
  | nil => rfl
  | cons T Ts ih =>
      show EnvT.pushArgs Ts (EnvT.cons T ρ) i = _
      cases i with
      | zero => simp [List.length] at hi
      | succ i =>
          have hle : Ts.length ≤ i := by simp [List.length] at hi; omega
          have e1 : i + 1 - Ts.length = i - Ts.length + 1 := by omega
          have e2 : i + 1 - (T :: Ts).length = i - Ts.length := by simp
          calc EnvT.pushArgs Ts (EnvT.cons T ρ) (i + 1)
              = EnvT.cons T ρ (i + 1 - Ts.length) := ih (by omega)
            _ = EnvT.cons T ρ (i - Ts.length + 1) := by rw [e1]
            _ = ρ (i - Ts.length) := rfl
            _ = ρ (i + 1 - (T :: Ts).length) := by rw [e2]

/-- `pushArgs` inside the pushed list reads `Ss[len-1-i]`. -/
theorem envT_pushArgs_index {Ss : List (CptT → Prop)} {ρ : EnvT} {i : Nat} {S : CptT → Prop}
    (hi : i < Ss.length) (h : Ss[Ss.length - 1 - i]? = some S) :
    EnvT.pushArgs Ss ρ i = S := by
  induction Ss generalizing ρ i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons T Ts ih =>
      show EnvT.pushArgs Ts (EnvT.cons T ρ) i = S
      cases Ts with
      | nil =>
          have h0 : i = 0 := by simp at hi; omega
          subst h0
          simp at h
          obtain rfl := h
          rfl
      | cons U Us =>
          cases i with
          | zero =>
              have hh : (T :: U :: Us).length - 1 - 0 = Us.length + 1 := by simp
              rw [hh, List.getElem?_cons_succ] at h
              have hk : (U :: Us).length - 1 - 0 = Us.length := by simp
              exact ih (i := 0) (by simp) (by rw [hk]; exact h)
          | succ i =>
              have hi2 : i + 1 < Us.length + 2 := by simpa using hi
              have hlen' : (T :: U :: Us).length - 1 - (i + 1) = Us.length - i := by simp
              rw [hlen'] at h
              cases hzi : Us.length - i with
              | zero =>
                  rw [hzi, List.getElem?_cons_zero] at h
                  obtain rfl := Option.some.inj h
                  have hie : i + 1 = (U :: Us).length := by simp; omega
                  rw [hie, envT_pushArgs_ge (i := (U :: Us).length) (Nat.le_refl _),
                    Nat.sub_self]
                  rfl
              | succ k =>
                  rw [hzi, List.getElem?_cons_succ] at h
                  have hk : (U :: Us).length - 1 - (i + 1) = k := by simp; omega
                  exact ih (i := i + 1) (by simp; omega) (by rw [hk]; exact h)

/-! ### §4 — compacts of the fixture terms -/

/-- The rigid axiom `N` has only `⊥` and its own spine. -/
theorem approxT_exAx {ρ : EnvT} {u : CptT}
    (h : ApproxT exEnv ρ (.const 0 []) u) : u = .bot ∨ u = .spine 0 [] := by
  rcases approxT_const_inv h with h0 | ⟨_, _, e⟩ | ⟨m, b, hd, _⟩ |
      ⟨w, _, _, _, hw, _, _, _, _, _⟩ | ⟨w, _, _, hw, _, _, _, _⟩
  · exact Or.inl h0
  · exact Or.inr e
  · have h1 := hd.1
    rw [exEnv_mem0] at h1
    obtain rfl := Option.some.inj h1
    exact Option.noConfusion hd.2.1
  · have h := w.hrec
    rw [hw, exEnv_mem0] at h
    have hrm : w.recMember = exAxMember := (Option.some.inj h).symm
    have hk := w.hrecK
    rw [hrm] at hk
    exact absurd hk (by decide)
  · have h := w.hrec
    rw [hw, exEnv_mem0] at h
    have hrm : w.recMember = exAxMember := (Option.some.inj h).symm
    have hk := w.hrecK
    rw [hrm] at hk
    exact absurd hk (by decide)

/-- `m'`'s lam compacts: every step demanded only at `⊥` yields `⊥` or a
    lam whose steps all output `⊥`. -/
theorem exMinor_lam_outputs {ρ : EnvT} {g : List (List CptT × CptT)}
    (h : ApproxT exEnv ρ exMinorArg (.lam g)) :
    ∀ s ∈ g, (∀ u ∈ s.1, u = .bot) →
      s.2 = .bot ∨ ∃ g₂, s.2 = .lam g₂ ∧ ∀ t ∈ g₂, t.2 = .bot := by
  intro s hs hbot
  obtain ⟨s₁, s₂⟩ := s
  rcases approxT_lam_inv h with h0 | ⟨a, g', e, _, _, hg⟩
  · exact CptT.noConfusion h0
  · obtain rfl := CptT.lam.inj e
    obtain ⟨_, hb⟩ := hg _ hs
    rcases approxT_lam_inv hb with h0 | ⟨a₂, g₂, e₂, _, _, hg₂⟩
    · exact Or.inl h0
    · obtain rfl := e₂
      refine Or.inr ⟨g₂, rfl, fun t ht => ?_⟩
      obtain ⟨_, hbt⟩ := hg₂ t ht
      rcases approxT_bvar_inv hbt with h0 | h0
      · exact h0
      · exact hbot _ h0

/-! ### §5 — fold-application refutations -/

/-- A fold through a `.spine` head only ever grows the spine's argument list. -/
theorem foldAppCptT_spine_grow {E : ResolvedEnv} {ρ : EnvT} {r : Nat}
    {args : List CptT} {xs : List (Expr Nat)} {r' : Nat} {args' : List CptT}
    (h : FoldAppCptT E ρ (.spine r args) xs (.spine r' args')) :
    ∃ ys, args' = args ++ ys := by
  induction xs generalizing args args' with
  | nil =>
      cases h with
      | nil => exact ⟨[], by simp⟩
  | cons x xs ih =>
      cases h with
      | cons hstep hrest =>
          cases hstep with
          | bot => exact CptT.noConfusion (foldAppCptT_bot_inv hrest)
          | appSpine hx =>
              obtain ⟨ys, e⟩ := ih hrest
              exact ⟨_, e.trans (List.append_assoc _ _ _)⟩

theorem foldAppCptT_lam_botouts_no_spine {E : ResolvedEnv} {ρ : EnvT}
    {g : List (List CptT × CptT)} (hout : ∀ t ∈ g, t.2 = .bot)
    {xs : List (Expr Nat)} {r : Nat} {args : List CptT} :
    FoldAppCptT E ρ (.lam g) xs (.spine r args) → False := by
  induction xs with
  | nil => intro h; cases h
  | cons x xs ih =>
      intro h; cases h with
      | cons hstep hrest =>
          cases hstep with
          | bot => exact CptT.noConfusion (foldAppCptT_bot_inv hrest)
          | app hs hx =>
              have := hout _ hs
              rw [this] at hrest
              exact CptT.noConfusion (foldAppCptT_bot_inv hrest)

/-- `instantiateLevels` commutes with `foldApps`. -/
theorem instantiateLevels_foldApps (ls : List Level) (f : Expr Nat)
    (args : List (Expr Nat)) :
    instantiateLevels ls (foldApps f args) =
      foldApps (instantiateLevels ls f) (args.map (instantiateLevels ls)) := by
  induction args generalizing f with
  | nil => rfl
  | cons a as ih => simp only [foldApps, instantiateLevels, List.map_cons, ih]

/-! ### §6 — the schema evaluation cannot produce `.spine 0 []` -/

/-- Shared kernel of the schema refutation: under `env'`, the minor-slot bvar
    reads only `S`-compacts and the field-slot bvar is `[]`. -/
theorem ex_schema_aux {env' : EnvT} {k j : Nat} {S : List CptT}
    {rest : List (Expr Nat)} {cf : CptT}
    (hk : env' k = demandT S) (hj : env' j = demandT [])
    (hS : ∀ u ∈ S, u = .bot ∨ u = .spine 0 [] ∨
      ∃ g, u = .lam g ∧ ApproxT exEnv EnvT.bot exMinorArg u)
    (hcf : ApproxT exEnv env' (.bvar k) cf)
    (hf : FoldAppCptT exEnv env' cf (.bvar j :: rest) (.spine 0 [])) : False := by
  rcases approxT_bvar_inv hcf with hcb | hcb
  · cases hf with
    | cons hstep hrest =>
        cases hstep with
        | bot => exact CptT.noConfusion (foldAppCptT_bot_inv hrest)
        | app hs hx => exact CptT.noConfusion hcb
        | appSpine hx => exact CptT.noConfusion hcb
  · rw [hk] at hcb
    have hcfK := hS cf hcb
    cases hf with
    | cons hstep hrest =>
        cases hstep with
        | bot => exact CptT.noConfusion (foldAppCptT_bot_inv hrest)
        | app hs hx =>
            rcases hcfK with e | e | ⟨g', e, hApr⟩
            · exact CptT.noConfusion e
            · exact CptT.noConfusion e
            · obtain rfl := CptT.lam.inj e
              obtain (e2 | ⟨g₂, e2, hout₂⟩) := exMinor_lam_outputs hApr _ hs
                (fun u hu => by
                  rcases approxT_bvar_inv (hx u hu) with h0 | h0
                  · exact h0
                  · rw [hj] at h0
                    exact (List.not_mem_nil _ h0).elim)
              · rw [e2] at hrest
                exact CptT.noConfusion (foldAppCptT_bot_inv hrest)
              · rw [e2] at hrest
                exact foldAppCptT_lam_botouts_no_spine hout₂ hrest
        | appSpine hx =>
            rcases hcfK with e | e | ⟨g, e, _⟩
            · exact CptT.noConfusion e
            · obtain ⟨rfl, rfl⟩ := CptT.spine.inj e
              simp only [List.nil_append] at hrest
              obtain ⟨ys, e⟩ := foldAppCptT_spine_grow hrest
              simp at e
            · exact CptT.noConfusion e

/-- Under the `recursorProp` environment the schema `m w …` evaluates to nothing
    but `⊥`-output lams and `⊥`: never `.spine 0 []`. -/
theorem ex_schema_no_spine {w' : IotaWitnessS exEnv} {us_pre : List (List CptT)}
    {rest : List (Expr Nat)} {ls : List Level}
    (hargs : ApproxArgsDemandT exEnv EnvT.bot (wEx.preMajor ++ [exCtorApp])
      (us_pre ++ [[]]))
    (hup : us_pre.length = w'.preMajor.length)
    (hw : w'.recRef = 3)
    (hsch : instantiateLevels ls w'.schema =
      foldApps (.bvar (w'.fields.length + w'.nindices))
        (.bvar (w'.fields.length - 1) :: rest))
    (h : ApproxT exEnv (EnvT.pushArgs ((us_pre ++ w'.fields.map (fun _ => [])).map demandT)
      EnvT.bot) (instantiateLevels ls w'.schema) (.spine 0 [])) : False := by
  obtain ⟨hnm, hci, _, _, _, _, hnp⟩ := exW_shape hw
  obtain ⟨hpreLen, hfl, hnpi⟩ := exW_lengths hw
  have hup4 : us_pre.length = 4 := by omega
  have hfl2 : 2 ≤ w'.fields.length := by omega
  rw [hsch] at h
  rw [approxT_foldApps_iff] at h
  obtain ⟨cf, hcf, hf⟩ := h
  rcases us_pre with _ | ⟨u0, _ | ⟨u1, _ | ⟨u2, _ | ⟨um, _ | _⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hup4 <;> try omega
  rw [show wEx.preMajor ++ [exCtorApp] =
      [.const 0 [], .const 0 [], .const 0 [], exMinorArg, exCtorApp] from rfl] at hargs
  obtain ⟨hα, hp, hM, hm, _⟩ :
      (∀ u ∈ u0, ApproxT exEnv EnvT.bot (.const 0 []) u) ∧
      (∀ u ∈ u1, ApproxT exEnv EnvT.bot (.const 0 []) u) ∧
      (∀ u ∈ u2, ApproxT exEnv EnvT.bot (.const 0 []) u) ∧
      (∀ u ∈ um, ApproxT exEnv EnvT.bot exMinorArg u) ∧
      (∀ u ∈ ([] : List CptT), ApproxT exEnv EnvT.bot exCtorApp u) := by
    cases hargs with
    | cons hα h1 =>
        cases h1 with
        | cons hp h2 =>
            cases h2 with
            | cons hM h3 =>
                cases h3 with
                | cons hm h4 =>
                    cases h4 with
                    | cons hmajor _ => exact ⟨hα, hp, hM, hm, hmajor⟩
  have hfields_map : w'.fields.map (fun _ => []) =
      List.replicate w'.fields.length ([] : List CptT) := by
    induction w'.fields with
    | nil => rfl
    | cons f fs ih => simp [List.map_cons, List.replicate_succ, ih]
  have hSs_len : (([u0, u1, u2, um] ++ w'.fields.map (fun _ => [])).map demandT).length =
      4 + w'.fields.length := by simp [hfields_map]; omega
  have hj : ∀ j, j < w'.fields.length →
      EnvT.pushArgs (([u0, u1, u2, um] ++ w'.fields.map (fun _ => [])).map demandT)
        EnvT.bot j = demandT [] := by
    intro j hjlt
    apply envT_pushArgs_index (i := j) (by rw [hSs_len]; omega)
    rw [hSs_len]
    have hidx : 4 + w'.fields.length - 1 - j = 4 + (w'.fields.length - 1 - j) := by omega
    rw [hidx, List.map_append, hfields_map, List.map_replicate]
    rw [List.getElem?_append_right
      (by simp only [List.length_map, List.length_cons, List.length_nil]; omega)]
    rw [show 4 + (w'.fields.length - 1 - j) - (List.map demandT [u0, u1, u2, um]).length =
        w'.fields.length - 1 - j from by simp; omega]
    rw [List.getElem?_replicate, if_pos (show w'.fields.length - 1 - j < w'.fields.length
      from by omega)]
  have hj1 : EnvT.pushArgs (([u0, u1, u2, um] ++ w'.fields.map (fun _ => [])).map demandT)
      EnvT.bot (w'.fields.length - 1) = demandT [] := hj _ (by omega)
  rcases (by omega : w'.nindices = 0 ∨ w'.nindices = 1 ∨ w'.nindices = 2) with h0 | h1 | h2
  · have hk : EnvT.pushArgs (([u0, u1, u2, um] ++ w'.fields.map (fun _ => [])).map demandT)
        EnvT.bot (w'.fields.length + w'.nindices) = demandT um := by
      rw [h0]
      apply envT_pushArgs_index (i := w'.fields.length + 0) (by rw [hSs_len]; omega)
      rw [hSs_len, List.map_append, hfields_map, List.map_replicate]
      have hidx : 4 + w'.fields.length - 1 - (w'.fields.length + 0) = 3 := by omega
      rw [hidx, List.getElem?_append_left (by simp), List.getElem?_map]
      rfl
    have hS : ∀ u ∈ um, u = .bot ∨ u = .spine 0 [] ∨
        ∃ g, u = .lam g ∧ ApproxT exEnv EnvT.bot exMinorArg u := by
      intro u hu
      rcases approxT_lam_inv (hm u hu) with e | ⟨a, g, e, _, _⟩
      · exact Or.inl e
      · exact Or.inr (Or.inr ⟨g, e, hm u hu⟩)
    exact ex_schema_aux hk hj1 hS hcf hf
  · have hk : EnvT.pushArgs (([u0, u1, u2, um] ++ w'.fields.map (fun _ => [])).map demandT)
        EnvT.bot (w'.fields.length + w'.nindices) = demandT u2 := by
      rw [h1]
      apply envT_pushArgs_index (i := w'.fields.length + 1) (by rw [hSs_len]; omega)
      rw [hSs_len, List.map_append, hfields_map, List.map_replicate]
      have hidx : 4 + w'.fields.length - 1 - (w'.fields.length + 1) = 2 := by omega
      rw [hidx, List.getElem?_append_left (by simp), List.getElem?_map]
      rfl
    have hS : ∀ u ∈ u2, u = .bot ∨ u = .spine 0 [] ∨
        ∃ g, u = .lam g ∧ ApproxT exEnv EnvT.bot exMinorArg u := by
      intro u hu
      rcases approxT_exAx (hM u hu) with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    exact ex_schema_aux hk hj1 hS hcf hf
  · have hk : EnvT.pushArgs (([u0, u1, u2, um] ++ w'.fields.map (fun _ => [])).map demandT)
        EnvT.bot (w'.fields.length + w'.nindices) = demandT u1 := by
      rw [h2]
      apply envT_pushArgs_index (i := w'.fields.length + 2) (by rw [hSs_len]; omega)
      rw [hSs_len, List.map_append, hfields_map, List.map_replicate]
      have hidx : 4 + w'.fields.length - 1 - (w'.fields.length + 2) = 1 := by omega
      rw [hidx, List.getElem?_append_left (by simp), List.getElem?_map]
      rfl
    have hS : ∀ u ∈ u1, u = .bot ∨ u = .spine 0 [] ∨
        ∃ g, u = .lam g ∧ ApproxT exEnv EnvT.bot exMinorArg u := by
      intro u hu
      rcases approxT_exAx (hp u hu) with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
    exact ex_schema_aux hk hj1 hS hcf hf

/-! ### §7 — the two sides of the SemEqT -/

/-- The contractum's redex produces `.spine 0 []`. -/
theorem approxT_exRhs : ApproxT exEnv EnvT.bot (iotaRhsOfS wEx) (.spine 0 []) := by
  simp only [wEx_rhs, exFieldVal, exMinorArg]
  apply ApproxT.app (g := [([], .spine 0 [])]) (s := ([], .spine 0 []))
  · apply ApproxT.app (g := [([.spine 0 []], .lam [([], .spine 0 [])])])
      (s := ([.spine 0 []], .lam [([], .spine 0 [])]))
    · apply ApproxT.lam (a := .sort)
      · exact .sort _ _
      · intro s hs u hu
        rw [List.mem_singleton] at hs
        obtain rfl := hs
        rw [List.mem_singleton] at hu
        obtain rfl := hu
        rw [CTyS]
        exact Or.inr (TyCodeCT.spine _ _)
      · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptT.noConfusion h⟩
      · intro s hs
        rw [List.mem_singleton] at hs
        obtain rfl := hs
        apply ApproxT.lam (a := .prop)
        · exact .sort _ _
        · intro t ht u hu
          rw [List.mem_singleton] at ht
          obtain rfl := ht
          exact (List.not_mem_nil _ hu).elim
        · exact ⟨_, List.mem_singleton.mpr rfl, fun h => CptT.noConfusion h⟩
        · intro t ht
          rw [List.mem_singleton] at ht
          obtain rfl := ht
          exact .bvar (List.mem_singleton.mpr rfl)
    · exact List.mem_singleton.mpr rfl
    · intro u hu
      rw [List.mem_singleton] at hu
      obtain rfl := hu
      exact .const _ _ _ (fun m hm => by
        rw [exEnv_mem0] at hm
        obtain rfl := Option.some.inj hm
        exact ⟨Or.inl rfl, by decide⟩) (fun ⟨m, _, _, hm, hclass, _⟩ => by
        rw [exEnv_mem0] at hm
        obtain rfl := Option.some.inj hm
        exact absurd hclass (by decide))
  · exact List.mem_singleton.mpr rfl
  · intro u hu
    exact (List.not_mem_nil _ hu).elim

/-- The lhs `rec N₃.rec args major` cannot produce `.spine 0 []`. -/
theorem not_approxT_exLhs :
    ¬ ApproxT exEnv EnvT.bot (iotaLhsOfS wEx) (.spine 0 []) := by
  intro h
  simp only [iotaLhsOfS, recCall] at h
  rw [approxT_foldApps_iff] at h
  obtain ⟨cf, hcf, hfold⟩ := h
  have hctor : foldApps (Expr.const wEx.ctorRef wEx.lsC) (wEx.ctorParams ++ wEx.fields) =
      exCtorApp := rfl
  rw [hctor] at hfold
  rcases approxT_propRec_inv (not_rigidConst_of_recursor wEx) (recRef_not_delta wEx)
      (fun w => @exW_prop w) hcf with hcb | ⟨w', us_pre, c₀, hw', hpre, hsc, hc⟩
  · rw [hcb] at hfold
    exact CptT.noConfusion (foldAppCptT_bot_inv hfold)
  · obtain ⟨hpreLen, _, _⟩ := exW_lengths hw'
    rw [hc] at hfold
    have hlen : (us_pre ++ [[]]).length = (wEx.preMajor ++ [exCtorApp]).length := by
      have hwpm : (wEx.preMajor ++ [exCtorApp]).length = 5 := rfl
      rw [hwpm]
      have : us_pre.length = 4 := by omega
      simp [this]
    rcases (foldAppCptT_curryStepT_iff hlen).mp hfold with h0 | ⟨hargs, hc₀⟩
    · exact CptT.noConfusion h0
    · subst hc₀
      obtain ⟨rest, hsch⟩ := exW_schema_head hw'
      obtain ⟨hnm, hci, _, _, hrm, _, _⟩ := exW_shape hw'
      have hminor : w'.fields.length + w'.nindices + (w'.nMinors - 1 - w'.ctorIdx) =
          w'.fields.length + w'.nindices := by omega
      have hsch' : instantiateLevels wEx.ls w'.schema =
          foldApps (.bvar (w'.fields.length + w'.nindices))
            (.bvar (w'.fields.length - 1) :: rest.map (instantiateLevels wEx.ls)) := by
        rw [hsch, hminor, instantiateLevels_foldApps]
        rfl
      exact ex_schema_no_spine hargs hpre hw' hsch' hsc

/-- **The named premise is refuted at `exEnv`.** -/
theorem not_iotaSoundT_ex : ¬ IotaSoundT exEnv := by
  intro hI
  exact not_approxT_exLhs ((hI wEx EnvT.bot (.spine 0 [])).2 approxT_exRhs)

#print axioms exFamTy
#print axioms exMkTy
#print axioms exMinorDom
#print axioms exRecTy
#print axioms exAxMember
#print axioms exFamMember
#print axioms exMkMember
#print axioms exRecMember
#print axioms exB0
#print axioms exB1
#print axioms exB2
#print axioms exEnv
#print axioms exEnv_mem0
#print axioms exEnv_mem1
#print axioms exEnv_mem2
#print axioms exEnv_mem3
#print axioms exEnv_mem_ge4
#print axioms exMinorArg
#print axioms exFieldVal
#print axioms exCtorApp
#print axioms exSchema
#print axioms wEx
#print axioms exW_propFamily
#print axioms wEx_rhs
#print axioms exW_family
#print axioms exW_shape
#print axioms exW_prop
#print axioms exW_lengths
#print axioms exW_schema_head
#print axioms envT_pushArgs_ge
#print axioms envT_pushArgs_index
#print axioms approxT_exAx
#print axioms exMinor_lam_outputs
#print axioms foldAppCptT_spine_grow
#print axioms foldAppCptT_lam_botouts_no_spine
#print axioms instantiateLevels_foldApps
#print axioms ex_schema_aux
#print axioms ex_schema_no_spine
#print axioms approxT_exRhs
#print axioms not_approxT_exLhs
#print axioms not_iotaSoundT_ex

end Rcic.Declarative.NativeValleys.TypedModelAudit
