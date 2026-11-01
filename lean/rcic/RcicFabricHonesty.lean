/-!
# Agent proof fabric — the honesty rule, stated in Lean (R-4a)

ADR draft #7925 §2a (second correction) makes the fabric's honesty predicate one more **Conflux gate**
with a `verdict_q`. A gate is a trust surface, so its rule is stated here first (R-4a). The scm belief
`apps/rcic-fabric-honesty` carries the same rule by composing existing modules:
- the statement check is `stmt_q = goal_q`;
- the axiom check is `rcic.ct_allow_policy`: the submission's axiom closure must be a subset of the
  allowed assumption set that a policy profile binds by digest (the allowlist is a policy reference,
  not a constant of this rule);
- the landed check is `rcic.env_weaken`: the landed environment image must be kept, entry for entry,
  in the submitted image (append-only; additions are allowed).
Those modules also refuse inputs that are not in canonical form (unsorted or duplicated CSV or image,
an unbound policy reference). That gating is theirs; this module states the rule on canonical inputs.
lean→scm emission of this module is not done, so the scm carrier is tied to it by the corpus theorems
generated in §4 from `rcic_fabric_honesty_corpus.json`.

`entryBytes` is the one definition of a landed declaration's image bytes: a theorem's image holds its
kind and statement only, so its proof may change (proof irrelevance); any other declaration's image
also holds its body, which dependents unfold (δ).

The result is a gate verdict, an input to Conflux's admission; it admits nothing. `closure_claim = 0`.
-/

namespace Rcic.Fabric.Honesty

/-! ## 1. Image bytes of a landed declaration -/

def entryBytes (kind stmtQ bodyQ : String) : String :=
  if kind == "theorem" then "theorem|" ++ stmtQ else kind ++ "|" ++ stmtQ ++ "|" ++ bodyQ

theorem entryBytes_theorem (s b b' : String) : entryBytes "theorem" s b = entryBytes "theorem" s b' :=
  rfl

theorem entryBytes_body_inj (k s b b' : String) (hk : k ≠ "theorem")
    (h : entryBytes k s b = entryBytes k s b') : b = b' := by
  have hk' : (k == "theorem") = false := by simpa using hk
  simp only [entryBytes, hk', Bool.false_eq_true, if_false] at h
  have := congrArg String.data h
  simp only [String.data_append] at this
  exact String.ext (List.append_cancel_left this)

/-! ## 2. The rule -/

/-- One entry of an environment image: a declaration name and its `entryBytes`. -/
structure Img where
  ref : String
  bytes : String
  deriving DecidableEq, Repr

/-- The bytes of the first entry with this ref. -/
def lookup (r : String) : List Img → Option String
  | [] => none
  | e :: es => if e.ref == r then some e.bytes else lookup r es

def goalOk (goalQ stmtQ : String) : Bool := stmtQ == goalQ

/-- `allow` is the allowed assumption set the policy profile binds. -/
def axiomsOk (allow closure : List String) : Bool := closure.all fun a => allow.contains a

def landedOk (old new : List Img) : Bool := old.all fun e => lookup e.ref new == some e.bytes

structure Checks where
  goal : Bool
  axioms : Bool
  landed : Bool
  deriving DecidableEq, Repr

def checks (goalQ stmtQ : String) (allow closure : List String) (old new : List Img) : Checks :=
  ⟨goalOk goalQ stmtQ, axiomsOk allow closure, landedOk old new⟩

def accepted (c : Checks) : Bool := c.goal && c.axioms && c.landed

/-! ## 3. What the rule says -/

theorem goalOk_iff (g s : String) : goalOk g s = true ↔ s = g := by
  simp [goalOk]

theorem axiomsOk_iff (allow closure : List String) :
    axiomsOk allow closure = true ↔ ∀ a ∈ closure, a ∈ allow := by
  simp [axiomsOk, List.all_eq_true]

theorem landedOk_iff (old new : List Img) :
    landedOk old new = true ↔ ∀ e ∈ old, lookup e.ref new = some e.bytes := by
  simp [landedOk, List.all_eq_true]

/-- Accepted exactly when the statement is the goal, every axiom is allowed by the policy, and every
    landed entry is kept with its bytes. -/
theorem accepted_iff (g s : String) (allow closure : List String) (old new : List Img) :
    accepted (checks g s allow closure old new) = true ↔
      s = g ∧ (∀ a ∈ closure, a ∈ allow) ∧ ∀ e ∈ old, lookup e.ref new = some e.bytes := by
  simp only [accepted, checks, Bool.and_eq_true, goalOk_iff, axiomsOk_iff, landedOk_iff, and_assoc]

/-- Adding entries never breaks the landed check. -/
theorem landedOk_nil (new : List Img) : landedOk [] new = true := rfl

/-- A landed theorem whose proof changed keeps its image entry. -/
theorem landed_theorem_proof_change (n s b b' : String) :
    (⟨n, entryBytes "theorem" s b⟩ : Img) = ⟨n, entryBytes "theorem" s b'⟩ := rfl

/-- A landed definition whose body changed is refused: its entry's bytes differ. -/
theorem landed_definition_body_change (n k s b b' : String) (hk : k ≠ "theorem") (hb : b ≠ b')
    (new : List Img) (h : lookup n new = some (entryBytes k s b')) :
    landedOk [⟨n, entryBytes k s b⟩] new = false := by
  have hne : entryBytes k s b' ≠ entryBytes k s b := fun he =>
    hb (entryBytes_body_inj k s b' b hk he).symm
  simp [landedOk, h, hne]

/-! ## 4. The scm carrier's corpus, evaluated by the rule

Generated from `apps/rcic-fabric-honesty/rcic_fabric_honesty_corpus.json`. For each row whose inputs are
canonical, `checks` on the row's inputs (the allowlist is the store entry the row's profile binds) gives
the carrier's outcome per check, read off the expected residues: `[fabric_goal_mismatch]`,
`[rcic_allowed_axioms_subset]`, `[rcic_cog_append_only_dropped]` / `_rewrite`. Rows 13–15 are refused by
the composed modules' canonical-form gates (unbound policy reference, non-canonical closure CSV, unsorted
image), which this rule leaves to them; they have no theorem here. -/

/-- corpus row 1: 1 clean admit: stmt equals goal, closure canonical, landed image unchanged -/
theorem corpus_row_01 :
    checks "G" "G" ["Quot.sound", "propext"] ["Quot.sound", "propext"]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1"⟩]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1"⟩] =
      ⟨true, true, true⟩ := by decide

/-- corpus row 2: 2 goal mismatch only: restated statement, otherwise clean -/
theorem corpus_row_02 :
    checks "G" "S2" ["Quot.sound", "propext"] ["propext"]
      []
      [] =
      ⟨false, true, true⟩ := by decide

/-- corpus row 3: 3 Classical.choice leak only -/
theorem corpus_row_03 :
    checks "G" "G" ["Quot.sound", "propext"] ["Classical.choice", "propext"]
      []
      [] =
      ⟨true, false, true⟩ := by decide

/-- corpus row 4: 4 sorryAx leak only -/
theorem corpus_row_04 :
    checks "G" "G" ["Quot.sound", "propext"] ["sorryAx"]
      []
      [] =
      ⟨true, false, true⟩ := by decide

/-- corpus row 5: 5 landed theorem statement changed -/
theorem corpus_row_05 :
    checks "G" "G" ["Quot.sound", "propext"] ["Quot.sound", "propext"]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1"⟩]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1x"⟩] =
      ⟨true, true, false⟩ := by decide

/-- corpus row 6: 6 landed theorem proof body changed (body outside the image): images identical, accepted -/
theorem corpus_row_06 :
    checks "G" "G" ["Quot.sound", "propext"] ["Quot.sound", "propext"]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1"⟩]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1"⟩] =
      ⟨true, true, true⟩ := by decide

/-- corpus row 7: 7 landed definition body changed: refused -/
theorem corpus_row_07 :
    checks "G" "G" ["Quot.sound", "propext"] ["Quot.sound", "propext"]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1"⟩]
      [⟨"D1", "definition|s2|b2x"⟩, ⟨"T1", "theorem|s1"⟩] =
      ⟨true, true, false⟩ := by decide

/-- corpus row 8: 8 landed name deleted -/
theorem corpus_row_08 :
    checks "G" "G" ["Quot.sound", "propext"] ["Quot.sound", "propext"]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1"⟩]
      [⟨"T1", "theorem|s1"⟩] =
      ⟨true, true, false⟩ := by decide

/-- corpus row 9: 9 landed kind changed (theorem to definition) -/
theorem corpus_row_09 :
    checks "G" "G" ["Quot.sound", "propext"] ["Quot.sound", "propext"]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1"⟩]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "definition|s1|b1"⟩] =
      ⟨true, true, false⟩ := by decide

/-- corpus row 10: 10 all three at once: goal mismatch, axiom leak, landed statement changed -/
theorem corpus_row_10 :
    checks "G" "S2" ["Quot.sound", "propext"] ["Classical.choice", "propext"]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1"⟩]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1x"⟩] =
      ⟨false, false, false⟩ := by decide

/-- corpus row 11: 11 empty closure and empty images: accepted -/
theorem corpus_row_11 :
    checks "G" "G" ["Quot.sound", "propext"] []
      []
      [] =
      ⟨true, true, true⟩ := by decide

/-- corpus row 12: 12 new after-only name accepted -/
theorem corpus_row_12 :
    checks "G" "G" ["Quot.sound", "propext"] ["Quot.sound", "propext"]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1"⟩]
      [⟨"D1", "definition|s2|b2"⟩, ⟨"T1", "theorem|s1"⟩, ⟨"T2", "theorem|s3"⟩] =
      ⟨true, true, true⟩ := by decide

end Rcic.Fabric.Honesty
