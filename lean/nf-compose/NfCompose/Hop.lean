import NfCompose.Seq
/-!
A hop is an NF instance (NF-0, "A hop is an NF instance; its correctness
is exactness"). For a translation `T` from layer `M_A` to layer `M_B` and
an observation map `obs` (B outcomes to A outcomes), `hopModel` packages
the hop as an `ExecModel`:

  * `Raw` = A programs, `q = M_A.q`, `evalRaw`/`evalClass` = A's
    evaluation — the outcome a hop preserves is A's own;
  * `a` = exactness **and B-admission** (round 2, audit F4/hop-shape):
    `sigma_A c` must exist, the translated program must be B-admissible
    (`M_B.admissible (M_B.q (T rep))`), and B's evaluation of it, mapped
    by `obs`, must equal A's evaluation of `c` under `eqA` — the
    caller-supplied A-side value equality, which the hop theorems
    constrain to be equality (`heqA`);
  * `sigma` = `M_B.sigma (M_B.q (T rep))` — the B representative, so
    chains of `seq` consume it like every other layer's sigma;
  * `rho` = the named failure: `translationRefused` when `sigma_A`
    gives no representative, `targetRefused` carrying the B residue
    when the translation lands outside B's admission, `valueMismatch`
    carrying both outcomes when the evaluations differ.

`hopModel_profile` proves the four Tier-1 laws once, from the two layer
profiles. `hop_rho_none_iff_admissible` is the exactness reading.
`seq_residue_none_iff` / `seq_residue_empty_iff` are the seq-of-hops
residue lemmas.

`ModelEquiv` (round 2/3, audit F4 & R2-F4) is a genuine equivalence: maps
both ways on every component, both directions' preservation laws, and all
ten round-trip laws, so no component collapses distinct values.
`modelEquiv_refl/symm/trans` exhibit the equivalence structure;
`seq_assoc` (round 3, R2-F4) and `seq_congr` both construct full
`ModelEquiv` instances between sequential composites (using both forward
and inverse reassociation maps and proving all round-trip laws).

Prior art for the shape: CompCert's `forward_simulation` record and its
composition lemma; CakeML's per-phase semantics preservation.
-/
namespace NfCompose
open MSTNecessityExecModelMWE
/-- the named failure of a hop: the translation could not be made (no
    representative of the A-class), the translated program is outside
    B's admission (carrying B's own residue, if any), or the two
    evaluations differed — carrying both outcomes. -/
inductive HopResidue (O_A O_B R_B : Type) where
  | translationRefused
  | targetRefused (r : Option R_B)
  | valueMismatch (a : O_A) (b : O_B)
/-- the generic hop model. `eqA` is the A-side outcome equality the
    admission compares with; callers supply it (for `DecidableEq`
    outcomes, `(· == ·)`). -/
def hopModel (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool) : ExecModel where
  Raw := M_A.Raw
  Class := M_A.Class
  Rep := M_B.Rep
  Residue := HopResidue M_A.Outcome M_B.Outcome M_B.Residue
  Outcome := M_A.Outcome
  q := M_A.q
  evalRaw := M_A.evalRaw
  evalClass := M_A.evalClass
  admissible := fun c => match M_A.sigma c with
    | none => false
    | some rep =>
        M_B.admissible (M_B.q (T rep)) &&
        eqA (obs (M_B.evalRaw (T rep))) (M_A.evalClass c)
  rho := fun c => match M_A.sigma c with
    | none => some .translationRefused
    | some rep =>
        if !(M_B.admissible (M_B.q (T rep))) then
          some (.targetRefused (M_B.rho (M_B.q (T rep))))
        else if eqA (obs (M_B.evalRaw (T rep))) (M_A.evalClass c) then none
        else some (.valueMismatch (M_A.evalClass c) (M_B.evalRaw (T rep)))
  sigma := fun c => match M_A.sigma c with
    | none => none
    | some rep =>
        if M_B.admissible (M_B.q (T rep)) &&
            eqA (obs (M_B.evalRaw (T rep))) (M_A.evalClass c)
        then M_B.sigma (M_B.q (T rep)) else none
/-- the four Tier-1 laws of a hop, proved once from the two layer
    profiles (`M_A`'s quotient factorization for factorization,
    `M_B`'s admissibility soundness and representative precision for
    the new B-admission side). -/
theorem hopModel_profile (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool)
    (hA : hasMSTNFProfile M_A) (hB : hasMSTNFProfile M_B) :
    hasMSTNFProfile (hopModel M_A M_B T obs eqA) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; exact hA.1 r
  · intro c rep selected
    cases hsig : M_A.sigma c with
    | none => simp [hopModel, hsig] at selected
    | some repA =>
        simp only [hopModel, hsig] at selected ⊢
        cases hadm : M_B.admissible (M_B.q (T repA)) <;>
        cases heq : eqA (obs (M_B.evalRaw (T repA))) (M_A.evalClass c) <;>
          simp_all
  · intro c _ refused
    cases hsig : M_A.sigma c with
    | none => simp [hopModel, hsig]
    | some repA =>
        simp only [hopModel, hsig] at refused ⊢
        cases hadm : M_B.admissible (M_B.q (T repA)) <;>
          simp_all
  · intro c _ admitted
    cases hsig : M_A.sigma c with
    | none => simp [hopModel, hsig] at admitted
    | some repA =>
        simp only [hopModel, hsig] at admitted ⊢
        cases hadm : M_B.admissible (M_B.q (T repA)) with
        | false => simp_all
        | true =>
            cases heq : eqA (obs (M_B.evalRaw (T repA))) (M_A.evalClass c) with
            | false => simp_all
            | true =>
                have hactB : activeClass M_B (M_B.q (T repA)) := ⟨T repA, rfl⟩
                have hsigB := hB.2.2.2 _ hactB hadm
                simp [hadm, heq]
                exact hsigB
/-- exactness as residue emptiness: a hop class has no residue iff the
    hop's own admission holds on it. -/
theorem hop_rho_none_iff_admissible (M_A M_B : ExecModel)
    (T : M_A.Rep → M_B.Raw) (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool) (c : M_A.Class) :
    (hopModel M_A M_B T obs eqA).rho c = none ↔
      (hopModel M_A M_B T obs eqA).admissible c = true := by
  cases hsig : M_A.sigma c with
  | none => simp [hopModel, hsig]
  | some repA =>
      simp only [hopModel, hsig]
      cases hadm : M_B.admissible (M_B.q (T repA)) <;>
        cases heq : eqA (obs (M_B.evalRaw (T repA))) (M_A.evalClass c) <;>
          simp [hadm, heq]
/-- "no residue on the admissible classes": the correctness statement of
    a hop (and of any model against a predicate on its classes). -/
def noResidueOn (M : ExecModel) (P : M.Class → Prop) : Prop :=
  ∀ c, activeClass M c → P c → M.rho c = none
/-- a hop's correctness theorem: no residue on the A-admissible classes —
    by `hop_rho_none_iff_admissible`, equivalently every A-admissible
    class is exact and lands inside B's admission. -/
def hopCorrect (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool) : Prop :=
  noResidueOn (hopModel M_A M_B T obs eqA)
    (fun c => M_A.admissible c = true)
theorem hopCorrect_iff_exact (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool) :
    hopCorrect M_A M_B T obs eqA ↔
      ∀ c, activeClass M_A c → M_A.admissible c = true →
        (hopModel M_A M_B T obs eqA).admissible c = true := by
  unfold hopCorrect noResidueOn
  constructor
  · intro h c hc ha
    exact (hop_rho_none_iff_admissible M_A M_B T obs eqA c).mp (h c hc ha)
  · intro h c hc ha
    exact (hop_rho_none_iff_admissible M_A M_B T obs eqA c).mpr (h c hc ha)
/-- the seq-of-hops residue lemma, pointwise: under both profiles a seq
    residue vanishes on an active class iff stage 1 admits the class and
    stage 2 admits the class `feed` hands it (refusals stay tagged by
    stage: `SeqResidue.stage1` / `.stage2`). -/
theorem seq_residue_none_iff (M1 M2 : ExecModel) (feed : M1.Rep → M2.Raw)
    (h1 : hasMSTNFProfile M1) (h2 : hasMSTNFProfile M2)
    (c : M1.Class) (hc : activeClass M1 c) :
    (seqModel M1 M2 feed).rho c = none ↔
      M1.admissible c = true ∧
      (∀ rep, M1.sigma c = some rep →
        M2.admissible (M2.q (feed rep)) = true) := by
  constructor
  · intro h
    cases ha : M1.admissible c with
    | false =>
        have hrho := h1.2.2.1 c hc ha
        cases hr : M1.rho c with
        | none => exact absurd hr hrho
        | some _ => simp [seqModel, seqRhoOf, ha, hr] at h
    | true =>
        have hsig := h1.2.2.2 c hc ha
        cases hs : M1.sigma c with
        | none => exact absurd hs hsig
        | some rep =>
            refine ⟨rfl, ?_⟩
            intro rep' hs'
            have hrr : rep = rep' := Option.some.inj hs'
            cases hrr
            cases hb : M2.admissible (M2.q (feed rep)) with
            | true => rfl
            | false =>
                have hrho2 := h2.2.2.1 _ ⟨feed rep, rfl⟩ hb
                cases hr2 : M2.rho (M2.q (feed rep)) with
                | none => exact absurd hr2 hrho2
                | some _ => simp [seqModel, seqRhoOf, ha, hs, hb, hr2] at h
  · intro ⟨ha, hrep⟩
    cases hs : M1.sigma c with
    | none => simp [seqModel, seqRhoOf, ha, hs]
    | some rep =>
        have hb := hrep rep hs
        simp [seqModel, seqRhoOf, ha, hs, hb]
/-- the seq-of-hops residue lemma, set form: a seq of two models has an
    empty residue set on `P` iff stage 1 admits every `P` class and
    stage 2 admits every class `feed` reaches from them. For two hops
    chained on sigma this is "the chain is correct iff every hop's
    residue set is empty". -/
theorem seq_residue_empty_iff (M1 M2 : ExecModel) (feed : M1.Rep → M2.Raw)
    (h1 : hasMSTNFProfile M1) (h2 : hasMSTNFProfile M2)
    (P : M1.Class → Prop) :
    (∀ c, activeClass M1 c → P c →
      (seqModel M1 M2 feed).rho c = none) ↔
    (∀ c, activeClass M1 c → P c → M1.admissible c = true) ∧
    (∀ c rep, activeClass M1 c → P c → M1.sigma c = some rep →
      M2.admissible (M2.q (feed rep)) = true) := by
  constructor
  · intro h
    refine ⟨fun c hc hp => ?_, fun c rep hc hp hs => ?_⟩
    · exact ((seq_residue_none_iff M1 M2 feed h1 h2 c hc).mp (h c hc hp)).1
    · exact ((seq_residue_none_iff M1 M2 feed h1 h2 c hc).mp
        (h c hc hp)).2 rep hs
  · intro ⟨h1a, h2a⟩ c hc hp
    exact (seq_residue_none_iff M1 M2 feed h1 h2 c hc).mpr
      ⟨h1a c hc hp, fun rep hs => h2a c rep hc hp hs⟩
/-! ## Model equivalence, seq associativity as `ModelEquiv`, seq congruence, and the hop as `obs ∘ seq` -/
/-- a model equivalence: maps in both directions on every component,
    preservation of every field in both directions, and all ten
    round-trip laws — no component may collapse distinct values
    (round 2/3, audit F4 & R2-F4). -/
structure ModelEquiv (M N : ExecModel) where
  toR : M.Raw → N.Raw
  toC : M.Class → N.Class
  toP : M.Rep → N.Rep
  toE : M.Residue → N.Residue
  toO : M.Outcome → N.Outcome
  q_map : ∀ r, toC (M.q r) = N.q (toR r)
  evalR_map : ∀ r, toO (M.evalRaw r) = N.evalRaw (toR r)
  evalC_map : ∀ c, toO (M.evalClass c) = N.evalClass (toC c)
  adm_map : ∀ c, M.admissible c = N.admissible (toC c)
  rho_map : ∀ c, (M.rho c).map toE = N.rho (toC c)
  sig_map : ∀ c, (M.sigma c).map toP = N.sigma (toC c)
  fromR : N.Raw → M.Raw
  fromC : N.Class → M.Class
  fromP : N.Rep → M.Rep
  fromE : N.Residue → M.Residue
  fromO : N.Outcome → M.Outcome
  q_bmap : ∀ r, fromC (N.q r) = M.q (fromR r)
  evalR_bmap : ∀ r, fromO (N.evalRaw r) = M.evalRaw (fromR r)
  evalC_bmap : ∀ c, fromO (N.evalClass c) = M.evalClass (fromC c)
  adm_bmap : ∀ c, N.admissible c = M.admissible (fromC c)
  rho_bmap : ∀ c, (N.rho c).map fromE = M.rho (fromC c)
  sig_bmap : ∀ c, (N.sigma c).map fromP = M.sigma (fromC c)
  to_from_R : ∀ r, fromR (toR r) = r
  to_from_C : ∀ c, fromC (toC c) = c
  to_from_P : ∀ p, fromP (toP p) = p
  to_from_E : ∀ e, fromE (toE e) = e
  to_from_O : ∀ o, fromO (toO o) = o
  from_to_R : ∀ r, toR (fromR r) = r
  from_to_C : ∀ c, toC (fromC c) = c
  from_to_P : ∀ p, toP (fromP p) = p
  from_to_E : ∀ e, toE (fromE e) = e
  from_to_O : ∀ o, toO (fromO o) = o
/-- the identity equivalence. -/
def modelEquiv_refl (M : ExecModel) : ModelEquiv M M where
  toR := id; toC := id; toP := id; toE := id; toO := id
  fromR := id; fromC := id; fromP := id; fromE := id; fromO := id
  q_map := fun _ => rfl
  evalR_map := fun _ => rfl
  evalC_map := fun _ => rfl
  adm_map := fun _ => rfl
  rho_map := fun _ => congrFun Option.map_id _
  sig_map := fun _ => congrFun Option.map_id _
  q_bmap := fun _ => rfl
  evalR_bmap := fun _ => rfl
  evalC_bmap := fun _ => rfl
  adm_bmap := fun _ => rfl
  rho_bmap := fun _ => congrFun Option.map_id _
  sig_bmap := fun _ => congrFun Option.map_id _
  to_from_R := fun _ => rfl
  to_from_C := fun _ => rfl
  to_from_P := fun _ => rfl
  to_from_E := fun _ => rfl
  to_from_O := fun _ => rfl
  from_to_R := fun _ => rfl
  from_to_C := fun _ => rfl
  from_to_P := fun _ => rfl
  from_to_E := fun _ => rfl
  from_to_O := fun _ => rfl
/-- symmetry: swap the two directions. -/
def modelEquiv_symm {M N : ExecModel} (e : ModelEquiv M N) :
    ModelEquiv N M where
  toR := e.fromR; toC := e.fromC; toP := e.fromP; toE := e.fromE; toO := e.fromO
  fromR := e.toR; fromC := e.toC; fromP := e.toP; fromE := e.toE; fromO := e.toO
  q_map := e.q_bmap
  evalR_map := e.evalR_bmap
  evalC_map := e.evalC_bmap
  adm_map := e.adm_bmap
  rho_map := e.rho_bmap
  sig_map := e.sig_bmap
  q_bmap := e.q_map
  evalR_bmap := e.evalR_map
  evalC_bmap := e.evalC_map
  adm_bmap := e.adm_map
  rho_bmap := e.rho_map
  sig_bmap := e.sig_map
  to_from_R := e.from_to_R
  to_from_C := e.from_to_C
  to_from_P := e.from_to_P
  to_from_E := e.from_to_E
  to_from_O := e.from_to_O
  from_to_R := e.to_from_R
  from_to_C := e.to_from_C
  from_to_P := e.to_from_P
  from_to_E := e.to_from_E
  from_to_O := e.to_from_O
/-- transitivity: compose both directions. -/
def modelEquiv_trans {M N P : ExecModel} (e1 : ModelEquiv M N)
    (e2 : ModelEquiv N P) : ModelEquiv M P where
  toR := e2.toR ∘ e1.toR
  toC := e2.toC ∘ e1.toC
  toP := e2.toP ∘ e1.toP
  toE := e2.toE ∘ e1.toE
  toO := e2.toO ∘ e1.toO
  fromR := e1.fromR ∘ e2.fromR
  fromC := e1.fromC ∘ e2.fromC
  fromP := e1.fromP ∘ e2.fromP
  fromE := e1.fromE ∘ e2.fromE
  fromO := e1.fromO ∘ e2.fromO
  q_map := fun r =>
    (congrArg e2.toC (e1.q_map r)).trans (e2.q_map (e1.toR r))
  evalR_map := fun r =>
    (congrArg e2.toO (e1.evalR_map r)).trans (e2.evalR_map (e1.toR r))
  evalC_map := fun c =>
    (congrArg e2.toO (e1.evalC_map c)).trans (e2.evalC_map (e1.toC c))
  adm_map := fun c => (e1.adm_map c).trans (e2.adm_map (e1.toC c))
  rho_map := fun c => by
    rw [← Option.map_map, e1.rho_map, e2.rho_map]
    rfl
  sig_map := fun c => by
    rw [← Option.map_map, e1.sig_map, e2.sig_map]
    rfl
  q_bmap := fun r =>
    (congrArg e1.fromC (e2.q_bmap r)).trans (e1.q_bmap (e2.fromR r))
  evalR_bmap := fun r =>
    (congrArg e1.fromO (e2.evalR_bmap r)).trans (e1.evalR_bmap (e2.fromR r))
  evalC_bmap := fun c =>
    (congrArg e1.fromO (e2.evalC_bmap c)).trans (e1.evalC_bmap (e2.fromC c))
  adm_bmap := fun c => (e2.adm_bmap c).trans (e1.adm_bmap (e2.fromC c))
  rho_bmap := fun c => by
    rw [← Option.map_map, e2.rho_bmap, e1.rho_bmap]
    rfl
  sig_bmap := fun c => by
    rw [← Option.map_map, e2.sig_bmap, e1.sig_bmap]
    rfl
  to_from_R := fun r =>
    (congrArg e1.fromR (e2.to_from_R (e1.toR r))).trans (e1.to_from_R r)
  to_from_C := fun c =>
    (congrArg e1.fromC (e2.to_from_C (e1.toC c))).trans (e1.to_from_C c)
  to_from_P := fun p =>
    (congrArg e1.fromP (e2.to_from_P (e1.toP p))).trans (e1.to_from_P p)
  to_from_E := fun x =>
    (congrArg e1.fromE (e2.to_from_E (e1.toE x))).trans (e1.to_from_E x)
  to_from_O := fun o =>
    (congrArg e1.fromO (e2.to_from_O (e1.toO o))).trans (e1.to_from_O o)
  from_to_R := fun r =>
    (congrArg e2.toR (e1.from_to_R (e2.fromR r))).trans (e2.from_to_R r)
  from_to_C := fun c =>
    (congrArg e2.toC (e1.from_to_C (e2.fromC c))).trans (e2.from_to_C c)
  from_to_P := fun p =>
    (congrArg e2.toP (e1.from_to_P (e2.fromP p))).trans (e2.from_to_P p)
  from_to_E := fun x =>
    (congrArg e2.toE (e1.from_to_E (e2.fromE x))).trans (e2.from_to_E x)
  from_to_O := fun o =>
    (congrArg e2.toO (e1.from_to_O (e2.fromO o))).trans (e2.from_to_O o)
/-- reassociate a left-nested sequential outcome rightward. -/
def seqAssocOut {O1 O2 O3 : Type} :
    SeqOutcome (SeqOutcome O1 O2) O3 → SeqOutcome O1 (SeqOutcome O2 O3)
  | .stage1 (.stage1 a) => .stage1 a
  | .stage1 (.stage2 b) => .stage2 (.stage1 b)
  | .stage2 c => .stage2 (.stage2 c)
/-- reassociate a left-nested sequential residue rightward. -/
def seqAssocRes {R1 R2 R3 : Type} :
    SeqResidue (SeqResidue R1 R2) R3 → SeqResidue R1 (SeqResidue R2 R3)
  | .stage1 (.stage1 a) => .stage1 a
  | .stage1 (.stage2 b) => .stage2 (.stage1 b)
  | .stage2 c => .stage2 (.stage2 c)
/-- reassociate a left-nested sequential representative rightward. -/
def seqAssocRep {P1 P2 P3 : Type} :
    SeqRep (SeqRep P1 P2) P3 → SeqRep P1 (SeqRep P2 P3)
  | .both (.both a b) c => .both a (.both b c)
/-- the inverse reassociation on representatives. -/
def seqAssocRepInv {P1 P2 P3 : Type} :
    SeqRep P1 (SeqRep P2 P3) → SeqRep (SeqRep P1 P2) P3
  | .both a (.both b c) => .both (.both a b) c
/-- the inverse reassociation on outcomes. -/
def seqAssocOutInv {O1 O2 O3 : Type} :
    SeqOutcome O1 (SeqOutcome O2 O3) → SeqOutcome (SeqOutcome O1 O2) O3
  | .stage1 a => .stage1 (.stage1 a)
  | .stage2 (.stage1 b) => .stage1 (.stage2 b)
  | .stage2 (.stage2 c) => .stage2 c
/-- the inverse reassociation on residues. -/
def seqAssocResInv {R1 R2 R3 : Type} :
    SeqResidue R1 (SeqResidue R2 R3) → SeqResidue (SeqResidue R1 R2) R3
  | .stage1 a => .stage1 (.stage1 a)
  | .stage2 (.stage1 b) => .stage1 (.stage2 b)
  | .stage2 (.stage2 c) => .stage2 c
/-- the left-associated feed into stage 3: it reads the second
    component's representative. -/
def seqAssocPairFeed {P1 P2 R3 : Type} (f23 : P2 → R3) :
    SeqRep P1 P2 → R3
  | .both _ r2 => f23 r2
theorem seqAssocRep_left_inv {P1 P2 P3 : Type}
    (p : SeqRep (SeqRep P1 P2) P3) : seqAssocRepInv (seqAssocRep p) = p := by
  cases p with | both ab c => cases ab with | both a b => rfl
theorem seqAssocRep_right_inv {P1 P2 P3 : Type}
    (p : SeqRep P1 (SeqRep P2 P3)) : seqAssocRep (seqAssocRepInv p) = p := by
  cases p with | both a bc => cases bc with | both b c => rfl
theorem seqAssocRes_left_inv {R1 R2 R3 : Type}
    (e : SeqResidue (SeqResidue R1 R2) R3) : seqAssocResInv (seqAssocRes e) = e := by
  cases e with
  | stage1 ab => cases ab <;> rfl
  | stage2 _ => rfl
theorem seqAssocRes_right_inv {R1 R2 R3 : Type}
    (e : SeqResidue R1 (SeqResidue R2 R3)) : seqAssocRes (seqAssocResInv e) = e := by
  cases e with
  | stage1 _ => rfl
  | stage2 bc => cases bc <;> rfl
theorem seqAssocOut_left_inv {O1 O2 O3 : Type}
    (o : SeqOutcome (SeqOutcome O1 O2) O3) : seqAssocOutInv (seqAssocOut o) = o := by
  cases o with
  | stage1 ab => cases ab <;> rfl
  | stage2 _ => rfl
theorem seqAssocOut_right_inv {O1 O2 O3 : Type}
    (o : SeqOutcome O1 (SeqOutcome O2 O3)) : seqAssocOut (seqAssocOutInv o) = o := by
  cases o with
  | stage1 _ => rfl
  | stage2 bc => cases bc <;> rfl
/-- reassociation on the stage-nested residue tags, as function equalities
    (the `Option.map` compositions `seq` produces). -/
theorem seqAssocRes_s1s1 {R1 R2 R3 : Type} :
    (seqAssocRes (R1 := R1) (R2 := R2) (R3 := R3) ∘
        SeqResidue.stage1 ∘ SeqResidue.stage1) =
      (SeqResidue.stage1 : R1 → SeqResidue R1 (SeqResidue R2 R3)) :=
  funext fun _ => rfl
theorem seqAssocRes_s1s2 {R1 R2 R3 : Type} :
    (seqAssocRes (R1 := R1) (R2 := R2) (R3 := R3) ∘
        SeqResidue.stage1 ∘ SeqResidue.stage2) =
      (SeqResidue.stage2 ∘ SeqResidue.stage1 :
        R2 → SeqResidue R1 (SeqResidue R2 R3)) :=
  funext fun _ => rfl
theorem seqAssocRes_s2 {R1 R2 R3 : Type} :
    (seqAssocRes (R1 := R1) (R2 := R2) (R3 := R3) ∘ SeqResidue.stage2) =
      (SeqResidue.stage2 ∘ SeqResidue.stage2 :
        R3 → SeqResidue R1 (SeqResidue R2 R3)) :=
  funext fun _ => rfl
/-- Pointwise forward reassociation laws on classes, used to build the
    full two-way `ModelEquiv` in `seq_assoc`. -/
theorem seq_assoc_laws (M1 M2 M3 : ExecModel) (f12 : M1.Rep → M2.Raw)
    (f23 : M2.Rep → M3.Raw) (h1 : hasMSTNFProfile M1) :
    ∀ c : M1.Class,
      (seqModel (seqModel M1 M2 f12) M3 (seqAssocPairFeed f23)).admissible c =
        (seqModel M1 (seqModel M2 M3 f23) f12).admissible c ∧
      seqAssocOut ((seqModel (seqModel M1 M2 f12) M3
          (seqAssocPairFeed f23)).evalClass c) =
        (seqModel M1 (seqModel M2 M3 f23) f12).evalClass c ∧
      ((seqModel (seqModel M1 M2 f12) M3
          (seqAssocPairFeed f23)).rho c).map seqAssocRes =
        (seqModel M1 (seqModel M2 M3 f23) f12).rho c ∧
      ((seqModel (seqModel M1 M2 f12) M3
          (seqAssocPairFeed f23)).sigma c).map seqAssocRep =
        (seqModel M1 (seqModel M2 M3 f23) f12).sigma c := by
  intro c
  cases ha : M1.admissible c with
  | false =>
      cases hs1 : M1.sigma c with
      | some r1 =>
          simp [h1.2.1 c r1 hs1] at ha
      | none =>
          simp [seqModel, seqEvalOf, seqAdmOf, seqRhoOf, seqSigmaOf,
            seqAssocOut, seqAssocRes, seqAssocRep, seqAssocPairFeed,
            seqAssocRes_s1s1, seqAssocRes_s1s2, seqAssocRes_s2,
            ha, hs1]
  | true =>
      cases hs1 : M1.sigma c with
      | none =>
          simp [seqModel, seqEvalOf, seqAdmOf, seqRhoOf, seqSigmaOf,
            seqAssocOut, seqAssocRes, seqAssocRep, seqAssocPairFeed,
            seqAssocRes_s1s1, seqAssocRes_s1s2, seqAssocRes_s2,
            ha, hs1]
      | some r1 =>
          cases ha2 : M2.admissible (M2.q (f12 r1)) with
          | false =>
              cases hs2 : M2.sigma (M2.q (f12 r1)) <;>
                simp [seqModel, seqEvalOf, seqAdmOf, seqRhoOf, seqSigmaOf,
                  seqAssocOut, seqAssocRes, seqAssocRep, seqAssocPairFeed,
                  seqAssocRes_s1s1, seqAssocRes_s1s2, seqAssocRes_s2,
                  ha, hs1, ha2, hs2]
          | true =>
              cases hs2 : M2.sigma (M2.q (f12 r1)) with
              | none =>
                  simp [seqModel, seqEvalOf, seqAdmOf, seqRhoOf, seqSigmaOf,
                    seqAssocOut, seqAssocRes, seqAssocRep, seqAssocPairFeed,
                    seqAssocRes_s1s1, seqAssocRes_s1s2, seqAssocRes_s2,
                    ha, hs1, ha2, hs2]
              | some r2 =>
                  cases ha3 : M3.admissible (M3.q (f23 r2)) <;>
                  cases hs3 : M3.sigma (M3.q (f23 r2)) <;>
                  simp [seqModel, seqEvalOf, seqAdmOf, seqRhoOf, seqSigmaOf,
                    seqAssocOut, seqAssocRes, seqAssocRep, seqAssocPairFeed,
                    seqAssocRes_s1s1, seqAssocRes_s1s2, seqAssocRes_s2,
                    ha, hs1, ha2, hs2, ha3, hs3]
/-- Pointwise forward reassociation of `evalRaw`. -/
theorem seq_assoc_evalRaw (M1 M2 M3 : ExecModel) (f12 : M1.Rep → M2.Raw)
    (f23 : M2.Rep → M3.Raw) (h1 : hasMSTNFProfile M1) (r : M1.Raw) :
    seqAssocOut ((seqModel (seqModel M1 M2 f12) M3
        (seqAssocPairFeed f23)).evalRaw r) =
      (seqModel M1 (seqModel M2 M3 f23) f12).evalRaw r := by
  cases ha : M1.admissible (M1.q r) with
  | false =>
      cases hs1 : M1.sigma (M1.q r) with
      | some r1 => simp [h1.2.1 (M1.q r) r1 hs1] at ha
      | none => simp [seqModel, seqEvalOf, seqSigmaOf, seqAssocOut, ha, hs1]
  | true =>
      cases hs1 : M1.sigma (M1.q r) with
      | none => simp [seqModel, seqEvalOf, seqSigmaOf, seqAssocOut, ha, hs1]
      | some r1 =>
          cases hs2 : M2.sigma (M2.q (f12 r1)) <;>
            simp [seqModel, seqEvalOf, seqSigmaOf, seqAssocOut,
              seqAssocPairFeed, ha, hs1, hs2]
/-- `seq` is associative as a full `ModelEquiv` (round 3, R2-F4):
    uses both `seqAssoc{Rep,Res,Out}` and `seqAssoc{Rep,Res,Out}Inv`,
    proving forward and backward preservation of all six model operations
    plus all ten round-trip laws. -/
def seq_assoc (M1 M2 M3 : ExecModel) (f12 : M1.Rep → M2.Raw)
    (f23 : M2.Rep → M3.Raw) (h1 : hasMSTNFProfile M1) :
    ModelEquiv
      (seqModel (seqModel M1 M2 f12) M3 (seqAssocPairFeed f23))
      (seqModel M1 (seqModel M2 M3 f23) f12) where
  toR := id
  toC := id
  toP := seqAssocRep
  toE := seqAssocRes
  toO := seqAssocOut
  q_map := fun _ => rfl
  evalR_map := seq_assoc_evalRaw M1 M2 M3 f12 f23 h1
  evalC_map := fun c => (seq_assoc_laws M1 M2 M3 f12 f23 h1 c).2.1
  adm_map := fun c => (seq_assoc_laws M1 M2 M3 f12 f23 h1 c).1
  rho_map := fun c => (seq_assoc_laws M1 M2 M3 f12 f23 h1 c).2.2.1
  sig_map := fun c => (seq_assoc_laws M1 M2 M3 f12 f23 h1 c).2.2.2
  fromR := id
  fromC := id
  fromP := seqAssocRepInv
  fromE := seqAssocResInv
  fromO := seqAssocOutInv
  q_bmap := fun _ => rfl
  evalR_bmap := fun r => by
    rw [← seq_assoc_evalRaw M1 M2 M3 f12 f23 h1 r]
    exact seqAssocOut_left_inv _
  evalC_bmap := fun c => by
    rw [← (seq_assoc_laws M1 M2 M3 f12 f23 h1 c).2.1]
    exact seqAssocOut_left_inv _
  adm_bmap := fun c => ((seq_assoc_laws M1 M2 M3 f12 f23 h1 c).1).symm
  rho_bmap := fun c => by
    dsimp only [id]
    rw [← (seq_assoc_laws M1 M2 M3 f12 f23 h1 c).2.2.1]
    cases (seqModel (seqModel M1 M2 f12) M3 (seqAssocPairFeed f23)).rho c with
    | none => rfl
    | some e => exact congrArg some (seqAssocRes_left_inv e)
  sig_bmap := fun c => by
    dsimp only [id]
    rw [← (seq_assoc_laws M1 M2 M3 f12 f23 h1 c).2.2.2]
    cases (seqModel (seqModel M1 M2 f12) M3 (seqAssocPairFeed f23)).sigma c with
    | none => rfl
    | some p => exact congrArg some (seqAssocRep_left_inv p)
  to_from_R := fun _ => rfl
  to_from_C := fun _ => rfl
  to_from_P := seqAssocRep_left_inv
  to_from_E := seqAssocRes_left_inv
  to_from_O := seqAssocOut_left_inv
  from_to_R := fun _ => rfl
  from_to_C := fun _ => rfl
  from_to_P := seqAssocRep_right_inv
  from_to_E := seqAssocRes_right_inv
  from_to_O := seqAssocOut_right_inv
/-- a model morphism componentwise through the seq tags. -/
def seqRepMap {P1 P2 P1' P2' : Type} (t1 : P1 → P1') (t2 : P2 → P2') :
    SeqRep P1 P2 → SeqRep P1' P2'
  | .both p1 p2 => .both (t1 p1) (t2 p2)
def seqResMap {R1 R2 R1' R2' : Type} (t1 : R1 → R1') (t2 : R2 → R2') :
    SeqResidue R1 R2 → SeqResidue R1' R2'
  | .stage1 r => .stage1 (t1 r)
  | .stage2 r => .stage2 (t2 r)
def seqOutMap {O1 O2 O1' O2' : Type} (t1 : O1 → O1') (t2 : O2 → O2') :
    SeqOutcome O1 O2 → SeqOutcome O1' O2'
  | .stage1 o => .stage1 (t1 o)
  | .stage2 o => .stage2 (t2 o)
/-- the tag maps commute with the stage tags, as function equalities
    (the `Option.map` compositions `seq` produces). -/
theorem seqResMap_s1 {R1 R2 R1' R2' : Type} (t1 : R1 → R1')
    (t2 : R2 → R2') :
    (seqResMap t1 t2 ∘ SeqResidue.stage1 :
        R1 → SeqResidue R1' R2') = SeqResidue.stage1 ∘ t1 :=
  funext fun _ => rfl
theorem seqResMap_s2 {R1 R2 R1' R2' : Type} (t1 : R1 → R1')
    (t2 : R2 → R2') :
    (seqResMap t1 t2 ∘ SeqResidue.stage2 :
        R2 → SeqResidue R1' R2') = SeqResidue.stage2 ∘ t2 :=
  funext fun _ => rfl
theorem seqRepMap_both {P1 P2 P1' P2' : Type} (t1 : P1 → P1')
    (t2 : P2 → P2') (p1 : P1) :
    (seqRepMap t1 t2 ∘ SeqRep.both p1 :
        P2 → SeqRep P1' P2') = SeqRep.both (t1 p1) ∘ t2 :=
  funext fun _ => rfl
/-- the fed class's stage-2 image, translated: `q` then `admissible`
    and `rho` commute through `feed` and the two maps. -/
theorem seqCong_feed_q (M1 M1' M2 M2' : ExecModel) (e1 : ModelEquiv M1 M1')
    (e2 : ModelEquiv M2 M2') (feed : M1.Rep → M2.Raw)
    (feed' : M1'.Rep → M2'.Raw)
    (feedC : ∀ r, feed' (e1.toP r) = e2.toR (feed r)) (rep : M1.Rep) :
    M2'.q (feed' (e1.toP rep)) = e2.toC (M2.q (feed rep)) :=
  (congrArg M2'.q (feedC rep)).trans (e2.q_map (feed rep)).symm
/-- the same for the backward direction. -/
theorem seqCong_feed_q_inv (M1 M1' M2 M2' : ExecModel) (e1 : ModelEquiv M1 M1')
    (e2 : ModelEquiv M2 M2') (feed : M1.Rep → M2.Raw)
    (feed' : M1'.Rep → M2'.Raw)
    (feedC' : ∀ r, feed (e1.fromP r) = e2.fromR (feed' r)) (rep : M1'.Rep) :
    M2.q (feed (e1.fromP rep)) = e2.fromC (M2'.q (feed' rep)) :=
  (congrArg M2.q (feedC' rep)).trans (e2.q_bmap (feed' rep)).symm
/-- `seq` is a congruence for model equivalence: compatible translations
    of the two stages (the feed commutes with the representative maps in
    both directions) transport to a full equivalence of the composites.
    `ModelEquiv` is data — the congruence is a definition, not a
    theorem. -/
def seq_congr (M1 M2 M1' M2' : ExecModel) (feed : M1.Rep → M2.Raw)
    (feed' : M1'.Rep → M2'.Raw)
    (e1 : ModelEquiv M1 M1') (e2 : ModelEquiv M2 M2')
    (feedC : ∀ r, feed' (e1.toP r) = e2.toR (feed r))
    (feedC' : ∀ r, feed (e1.fromP r) = e2.fromR (feed' r)) :
    ModelEquiv (seqModel M1 M2 feed) (seqModel M1' M2' feed') where
  toR := e1.toR
  toC := e1.toC
  toP := seqRepMap e1.toP e2.toP
  toE := seqResMap e1.toE e2.toE
  toO := seqOutMap e1.toO e2.toO
  q_map := e1.q_map
  evalR_map := by
    intro r
    have hq : M1'.q (e1.toR r) = e1.toC (M1.q r) := (e1.q_map r).symm
    have hs' : M1'.sigma (e1.toC (M1.q r)) =
        (M1.sigma (M1.q r)).map e1.toP := (e1.sig_map (M1.q r)).symm
    cases hs : M1.sigma (M1.q r) <;>
      simp [seqModel, seqEvalOf, seqOutMap, hs, hs', hq,
        e1.evalR_map r, feedC, e2.evalR_map]
  evalC_map := by
    intro c
    have hs' : M1'.sigma (e1.toC c) = (M1.sigma c).map e1.toP :=
      (e1.sig_map c).symm
    cases hs : M1.sigma c <;>
      simp [seqModel, seqEvalOf, seqOutMap, hs, hs',
        e1.evalC_map c, feedC, e2.evalR_map]
  adm_map := by
    intro c
    have hs' : M1'.sigma (e1.toC c) = (M1.sigma c).map e1.toP :=
      (e1.sig_map c).symm
    have ha' : M1'.admissible (e1.toC c) = M1.admissible c :=
      (e1.adm_map c).symm
    cases ha : M1.admissible c <;> cases hs : M1.sigma c <;>
      simp [seqModel, seqAdmOf, ha, hs, hs', ha',
        seqCong_feed_q M1 M1' M2 M2' e1 e2 feed feed' feedC, e2.adm_map]
  rho_map := by
    intro c
    have hs' : M1'.sigma (e1.toC c) = (M1.sigma c).map e1.toP :=
      (e1.sig_map c).symm
    have ha' : M1'.admissible (e1.toC c) = M1.admissible c :=
      (e1.adm_map c).symm
    have hr' : M1'.rho (e1.toC c) = (M1.rho c).map e1.toE :=
      (e1.rho_map c).symm
    cases ha : M1.admissible c <;> cases hs : M1.sigma c <;>
      simp [seqModel, seqRhoOf, ha, hs, hs', ha', hr',
        seqCong_feed_q M1 M1' M2 M2' e1 e2 feed feed' feedC, e2.adm_map,
        e2.rho_map, seqResMap_s1, seqResMap_s2]
    · rename_i rep
      cases hb : M2'.admissible (e2.toC (M2.q (feed rep))) <;>
        simp [hb, seqResMap_s1, seqResMap_s2]
      rw [← Option.map_map, e2.rho_map]
  sig_map := by
    intro c
    have hs' : M1'.sigma (e1.toC c) = (M1.sigma c).map e1.toP :=
      (e1.sig_map c).symm
    have ha' : M1'.admissible (e1.toC c) = M1.admissible c :=
      (e1.adm_map c).symm
    cases ha : M1.admissible c <;> cases hs : M1.sigma c <;>
      simp [seqModel, seqSigmaOf, ha, hs, hs', ha',
        seqCong_feed_q M1 M1' M2 M2' e1 e2 feed feed' feedC, e2.sig_map,
        seqRepMap_both]
    · rename_i rep
      cases hsi : M2.sigma (M2.q (feed rep)) <;>
        simp [hsi, ← e2.sig_map, seqRepMap]
  fromR := e1.fromR
  fromC := e1.fromC
  fromP := seqRepMap e1.fromP e2.fromP
  fromE := seqResMap e1.fromE e2.fromE
  fromO := seqOutMap e1.fromO e2.fromO
  q_bmap := e1.q_bmap
  evalR_bmap := by
    intro r
    have hq : M1.q (e1.fromR r) = e1.fromC (M1'.q r) := (e1.q_bmap r).symm
    have hs' : M1.sigma (e1.fromC (M1'.q r)) =
        (M1'.sigma (M1'.q r)).map e1.fromP := (e1.sig_bmap (M1'.q r)).symm
    cases hs : M1'.sigma (M1'.q r) <;>
      simp [seqModel, seqEvalOf, seqOutMap, hs, hs', hq,
        e1.evalR_bmap r, feedC', e2.evalR_bmap]
  evalC_bmap := by
    intro c
    have hs' : M1.sigma (e1.fromC c) = (M1'.sigma c).map e1.fromP :=
      (e1.sig_bmap c).symm
    cases hs : M1'.sigma c <;>
      simp [seqModel, seqEvalOf, seqOutMap, hs, hs',
        e1.evalC_bmap c, feedC', e2.evalR_bmap]
  adm_bmap := by
    intro c
    have hs' : M1.sigma (e1.fromC c) = (M1'.sigma c).map e1.fromP :=
      (e1.sig_bmap c).symm
    have ha' : M1.admissible (e1.fromC c) = M1'.admissible c :=
      (e1.adm_bmap c).symm
    cases ha : M1'.admissible c <;> cases hs : M1'.sigma c <;>
      simp [seqModel, seqAdmOf, ha, hs, hs', ha',
        seqCong_feed_q_inv M1 M1' M2 M2' e1 e2 feed feed' feedC', e2.adm_bmap]
  rho_bmap := by
    intro c
    have hs' : M1.sigma (e1.fromC c) = (M1'.sigma c).map e1.fromP :=
      (e1.sig_bmap c).symm
    have ha' : M1.admissible (e1.fromC c) = M1'.admissible c :=
      (e1.adm_bmap c).symm
    have hr' : M1.rho (e1.fromC c) = (M1'.rho c).map e1.fromE :=
      (e1.rho_bmap c).symm
    cases ha : M1'.admissible c <;> cases hs : M1'.sigma c <;>
      simp [seqModel, seqRhoOf, ha, hs, hs', ha', hr',
        seqCong_feed_q_inv M1 M1' M2 M2' e1 e2 feed feed' feedC',
        e2.adm_bmap, e2.rho_bmap, seqResMap_s1, seqResMap_s2]
    · rename_i rep
      cases hb : M2.admissible (e2.fromC (M2'.q (feed' rep))) <;>
        simp [hb, seqResMap_s1, seqResMap_s2]
      rw [← Option.map_map, e2.rho_bmap]
  sig_bmap := by
    intro c
    have hs' : M1.sigma (e1.fromC c) = (M1'.sigma c).map e1.fromP :=
      (e1.sig_bmap c).symm
    have ha' : M1.admissible (e1.fromC c) = M1'.admissible c :=
      (e1.adm_bmap c).symm
    cases ha : M1'.admissible c <;> cases hs : M1'.sigma c <;>
      simp [seqModel, seqSigmaOf, ha, hs, hs', ha',
        seqCong_feed_q_inv M1 M1' M2 M2' e1 e2 feed feed' feedC',
        e2.sig_bmap, seqRepMap_both]
    · rename_i rep
      cases hsi : M2'.sigma (M2'.q (feed' rep)) <;>
        simp [hsi, ← e2.sig_bmap, seqRepMap]
  to_from_R := e1.to_from_R
  to_from_C := e1.to_from_C
  to_from_P := fun
    | .both a b => by simp [seqRepMap, e1.to_from_P, e2.to_from_P]
  to_from_E := fun
    | .stage1 r => congrArg SeqResidue.stage1 (e1.to_from_E r)
    | .stage2 r => congrArg SeqResidue.stage2 (e2.to_from_E r)
  to_from_O := fun
    | .stage1 o => congrArg SeqOutcome.stage1 (e1.to_from_O o)
    | .stage2 o => congrArg SeqOutcome.stage2 (e2.to_from_O o)
  from_to_R := e1.from_to_R
  from_to_C := e1.from_to_C
  from_to_P := fun
    | .both a b => by simp [seqRepMap, e1.from_to_P, e2.from_to_P]
  from_to_E := fun
    | .stage1 r => congrArg SeqResidue.stage1 (e1.from_to_E r)
    | .stage2 r => congrArg SeqResidue.stage2 (e2.from_to_E r)
  from_to_O := fun
    | .stage1 o => congrArg SeqOutcome.stage1 (e1.from_to_O o)
    | .stage2 o => congrArg SeqOutcome.stage2 (e2.from_to_O o)
/-- the observation of a sequential outcome: the B-side value mapped
    back into A's outcome space. -/
def hopSeqObs {A B : Type} (obs : B → A) : SeqOutcome A B → A
  | .stage1 a => a
  | .stage2 b => obs b
/-- on a hop-admissible class the observed sequential outcome is the
    hop's own outcome: `M_A ~ obs ∘ seq(T, M_B)` on the class, stated
    with outcome equality. -/
theorem hop_eval_eq_obs_seq (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool)
    (heqA : ∀ x y, eqA x y = true ↔ x = y) (c : M_A.Class)
    (hadm : (hopModel M_A M_B T obs eqA).admissible c = true) :
    hopSeqObs obs ((seqModel M_A M_B T).evalClass c) =
        (hopModel M_A M_B T obs eqA).evalClass c := by
  cases hsig : M_A.sigma c with
  | none => simp [hopModel, hsig] at hadm
  | some rep =>
      simp only [hopModel, hsig] at hadm
      cases hadmB : M_B.admissible (M_B.q (T rep)) with
      | false => simp [hadmB] at hadm
      | true =>
          simp only [hadmB, Bool.true_and] at hadm
          have heq := (heqA _ _).mp hadm
          simp [seqModel, seqEvalOf, hsig, hopSeqObs, hopModel, heq]
/-- a hop stated on canonical representatives:
    `M_A ~ obs ∘ seq(T, M_B)` — on every active A-admissible class the
    sequential composite's outcome, observed back into A's outcome
    space, is A's own outcome, and the translated program lands inside
    B's admission. Stated with outcome equality — the `eqA` used by the
    hop's admission must be equality (`heqA` below), so the statement
    cannot be made vacuous by a trivially-true `eqA`. -/
def hopObsSeq (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome) : Prop :=
  ∀ c, activeClass M_A c → M_A.admissible c = true →
    ∃ rep, M_A.sigma c = some rep ∧
      M_B.admissible (M_B.q (T rep)) = true ∧
      hopSeqObs obs ((seqModel M_A M_B T).evalClass c) = M_A.evalClass c
/-- the two forms of a hop theorem coincide when `eqA` is equality:
    no residue on the A-admissible classes iff the observed
    `seq(T, M_B)` agrees with `M_A` on them and the image is
    B-admissible. -/
theorem hopCorrect_iff_obsSeq (M_A M_B : ExecModel) (T : M_A.Rep → M_B.Raw)
    (obs : M_B.Outcome → M_A.Outcome)
    (eqA : M_A.Outcome → M_A.Outcome → Bool)
    (heqA : ∀ x y, eqA x y = true ↔ x = y)
    (hA : hasMSTNFProfile M_A) :
    hopCorrect M_A M_B T obs eqA ↔ hopObsSeq M_A M_B T obs := by
  constructor
  · intro h c hact ha
    have hadm : (hopModel M_A M_B T obs eqA).admissible c = true :=
      (hopCorrect_iff_exact M_A M_B T obs eqA).mp h c hact ha
    have hsig := hA.2.2.2 c hact ha
    cases hs : M_A.sigma c with
    | none => exact absurd hs hsig
    | some rep =>
        refine ⟨rep, rfl, ?_, ?_⟩
        · simp only [hopModel, hs] at hadm
          cases hb : M_B.admissible (M_B.q (T rep)) <;>
            simp_all
        · exact hop_eval_eq_obs_seq M_A M_B T obs eqA heqA c hadm
  · intro h
    unfold hopCorrect noResidueOn
    intro c hact ha
    rcases h c hact ha with ⟨rep, hs, hadmB, hobs⟩
    have hadm : (hopModel M_A M_B T obs eqA).admissible c = true := by
      simp only [hopModel, hs, hadmB, Bool.true_and]
      apply (heqA _ _).mpr
      simpa [seqModel, seqEvalOf, hs, hopSeqObs] using hobs
    exact (hop_rho_none_iff_admissible M_A M_B T obs eqA c).mpr hadm
end NfCompose
#print axioms NfCompose.hopModel_profile
#print axioms NfCompose.hop_rho_none_iff_admissible
#print axioms NfCompose.hopCorrect_iff_exact
#print axioms NfCompose.seq_residue_none_iff
#print axioms NfCompose.seq_residue_empty_iff
#print axioms NfCompose.seq_assoc
#print axioms NfCompose.modelEquiv_refl
#print axioms NfCompose.modelEquiv_symm
#print axioms NfCompose.modelEquiv_trans
#print axioms NfCompose.seq_congr
#print axioms NfCompose.hop_eval_eq_obs_seq
#print axioms NfCompose.hopCorrect_iff_obsSeq
