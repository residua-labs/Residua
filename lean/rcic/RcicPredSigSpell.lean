/-
RCIC 07 §3 — G1-S4: `spellOf` injectivity, binding recovery, member
typing, and agreement with `rcic.pred_sig_spell`'s tokens (the CT-001
bridge).

Ruling on #6652 (cc, point 1): the member-to-digest binding is a fixed
rule over canonical bytes; S4 proves `spellOf` injective and that the
rule recovers the binding from the group bytes and the contract bytes
alone.  The plan's item-4 bridge is `spellOf mtype = y ↔ mtype =
exprOfSig slot` — token equality turned into member-type equality.

* **Binding recovery.**  `memberTokens_getElem?_sv`/`_svp`/`_natFam`
  give the token table per block; `atomsOf_sv`/`_svp`/`_natFam` read a
  `const` reference back to its token.  `svBinding`/`svpBinding` are the
  recovery theorems: group position `i` (a `sort 1` `axiomM` member —
  the group bytes) denotes the `i`-th canonical digest/residue id (the
  contract bytes).  No external table.
* **`spellOf` injectivity** on the signature image (`SigForm`), under
  `SigTokSafe` (no `>` inside a digest or residue id — the `>`
  delimiter must be unambiguous; real digests are hash bytes).  The
  image's tokens (`SV<d>`/`SVP<r>`/`"Nat"`/`"Prop"`) form a
  prefix-free code (`sigTok_prefix`), so concatenation is injective
  (`tokCat_inj` → `spellOf_inj`).
* **member_typing.**  `predMember_typed` — each signature
  `exprOfSig cd s` is a `Sort u` type in `predEnvOf cd`; `member_typing`
  bundles it with `predEnvOf_predIndex`'s `m.mtype = exprOfSig` — the
  wire's missing check (`m.mtype = sigExpr ∧ HasTyT m.mtype (.sort u)`).
* **Agreement.**  `spellOf` on each of the six slots yields exactly the
  string `scm/rcic/pred_sig_spell.scm` builds per field (`pre`/`rg`/
  `case_g` share one type: `SV<tin>SV<tst>Prop`).

`closure_claim = 0`.
-/
import rcic.RcicPredEnvWf

namespace Rcic.PredSig
open Rcic.Declarative Rcic.ScopeExact

/-! ## Token-table blocks -/

theorem memberTokens_getElem?_sv (cd : ContractSigData) {i : Nat}
    (hi : i < svCount cd) :
    (memberTokens cd)[i]? = (cd.svDigests)[i]?.map svToken := by
  have hmt : memberTokens cd = (cd.svDigests).map svToken ++
      ((cd.resIds).map svpToken ++ ["Nat", "Nat.zero", "Nat.succ", "Nat.rec"] ++
        ["pre", "returnGuard", "returnPost"] ++ (cd.resIds).map guardToken ++
        (cd.resIds).map postToken ++ ["bound"]) := by
    simp only [memberTokens, ← List.append_assoc]
  rw [hmt, List.getElem?_append_left (by rw [List.length_map]; exact hi),
      List.getElem?_map]

theorem memberTokens_getElem?_svp (cd : ContractSigData) {i : Nat}
    (hi : i < svpCount cd) :
    (memberTokens cd)[svpBase cd + i]? = (cd.resIds)[i]?.map svpToken := by
  have hmt : memberTokens cd = (cd.svDigests).map svToken ++
      ((cd.resIds).map svpToken ++
        (["Nat", "Nat.zero", "Nat.succ", "Nat.rec"] ++
          ["pre", "returnGuard", "returnPost"] ++ (cd.resIds).map guardToken ++
          (cd.resIds).map postToken ++ ["bound"])) := by
    simp only [memberTokens, ← List.append_assoc]
  rw [hmt, List.getElem?_append_right]
  · have hb : svpBase cd + i - ((cd.svDigests).map svToken).length = i := by
      rw [List.length_map]; simp only [svpBase, svCount]; omega
    rw [hb, List.getElem?_append_left (by rw [List.length_map]; exact hi),
        List.getElem?_map]
  · rw [List.length_map]; simp only [svpBase, svCount]; omega

theorem memberTokens_getElem?_natFam (cd : ContractSigData) :
    (memberTokens cd)[natFamIndex cd]? = some "Nat" := by
  have hmt : memberTokens cd = (cd.svDigests).map svToken ++
      ((cd.resIds).map svpToken ++
        (["Nat", "Nat.zero", "Nat.succ", "Nat.rec"] ++
          ["pre", "returnGuard", "returnPost"] ++ (cd.resIds).map guardToken ++
          (cd.resIds).map postToken ++ ["bound"])) := by
    simp only [memberTokens, ← List.append_assoc]
  have hle1 : ((cd.svDigests).map svToken).length ≤ natFamIndex cd := by
    rw [List.length_map]
    simp only [natFamIndex, natBase, svpBase, svCount]; omega
  have hb : natFamIndex cd - ((cd.svDigests).map svToken).length =
      svpCount cd := by
    rw [List.length_map]
    simp only [natFamIndex, natBase, svpBase, svCount]; omega
  have hle : ((cd.resIds).map svpToken).length ≤ svpCount cd := by
    rw [List.length_map]; simp only [svpCount]; omega
  have hb2 : svpCount cd - ((cd.resIds).map svpToken).length = 0 := by
    rw [List.length_map]; simp only [svpCount]; omega
  rw [hmt, List.getElem?_append_right hle1, hb,
      List.getElem?_append_right hle, hb2]
  rfl

/-! ## `atomsOf` at the signature references -/

/-- The findIdx roundtrip on `svDigests` (`resIds_getElem_findIdx`'s SV
arm). -/
theorem svDigests_getElem_findIdx (cd : ContractSigData) {d : String}
    (hd : d ∈ cd.svDigests) :
    ∃ hlt, (cd.svDigests)[(cd.svDigests).findIdx (· == d)]'hlt = d := by
  have hlt : (cd.svDigests).findIdx (· == d) < (cd.svDigests).length :=
    List.findIdx_lt_length_of_exists ⟨d, hd, by simp⟩
  exact ⟨hlt, eq_of_beq (List.findIdx_getElem (p := (· == d))
    (xs := cd.svDigests))⟩

theorem atomsOf_sv (cd : ContractSigData) {d : String}
    (hd : d ∈ cd.svDigests) :
    atomsOf cd (svIndexOf cd d) = some (svToken d) := by
  obtain ⟨hlt, hel⟩ := svDigests_getElem_findIdx cd hd
  have hi : svIndexOf cd d < svCount cd := hlt
  rw [atomsOf, memberTokens_getElem?_sv cd hi]
  have : (cd.svDigests)[svIndexOf cd d]? = some d :=
    List.getElem?_eq_some_iff.mpr ⟨hlt, hel⟩
  rw [this]
  rfl

theorem atomsOf_svp (cd : ContractSigData) {r : String}
    (hr : r ∈ cd.resIds) :
    atomsOf cd (svpIndexOf cd r) = some (svpToken r) := by
  obtain ⟨hlt, hel⟩ := resIds_getElem_findIdx cd hr
  have hi : svpIndexOf cd r = svpBase cd + (cd.resIds).findIdx (· == r) := rfl
  rw [atomsOf, hi, memberTokens_getElem?_svp cd hlt]
  have : (cd.resIds)[(cd.resIds).findIdx (· == r)]? = some r :=
    List.getElem?_eq_some_iff.mpr ⟨hlt, hel⟩
  rw [this]
  rfl

theorem atomsOf_natFam (cd : ContractSigData) :
    atomsOf cd (natFamIndex cd) = some "Nat" :=
  memberTokens_getElem?_natFam cd

/-! ## Binding recovery (group bytes ∧ contract bytes) -/

/-- `svToken`'s cons normal form. -/
theorem svToken_cons (d : String) :
    (svToken d).data = 'S' :: 'V' :: '<' :: (d.data ++ ['>']) := by
  simp only [svToken, String.data_append, List.append_assoc,
             List.cons_append, List.nil_append]

/-- `svpToken`'s cons normal form. -/
theorem svpToken_cons (r : String) :
    (svpToken r).data = 'S' :: 'V' :: 'P' :: '<' :: (r.data ++ ['>']) := by
  simp only [svpToken, String.data_append, List.append_assoc,
             List.cons_append, List.nil_append]

/-- `svToken` is injective — equality, not prefix: no delimiter-free
hypothesis needed for plain equality. -/
theorem svToken_inj {d e : String} (h : svToken d = svToken e) : d = e := by
  have hd := congrArg String.data h
  rw [svToken_cons, svToken_cons] at hd
  simp only [List.cons.injEq] at hd
  exact String.ext ((List.append_left_inj ['>']).mp hd.2.2.2)

theorem svpToken_inj {r r' : String} (h : svpToken r = svpToken r') :
    r = r' := by
  have hd := congrArg String.data h
  rw [svpToken_cons, svpToken_cons] at hd
  simp only [List.cons.injEq] at hd
  exact String.ext ((List.append_left_inj ['>']).mp hd.2.2.2.2)

/-- **The binding**: group position `i < svCount` denotes the `i`-th
canonical digest — the member bytes (`memberEntries`, a `sort 1`
`axiomM`) plus the contract bytes (`svDigests`, from `tin`/`tst`/`tout`)
fix it completely.  `findIdx` inverts it (`atomsOf_sv`). -/
theorem svBinding (cd : ContractSigData) {i : Nat} (hi : i < svCount cd) :
    (memberTokens cd)[i]? = (cd.svDigests)[i]?.map svToken :=
  memberTokens_getElem?_sv cd hi

theorem svBinding_iff (cd : ContractSigData) {i : Nat} (hi : i < svCount cd)
    {d : String} :
    ((memberTokens cd)[i]? = some (svToken d)) ↔
      ((cd.svDigests)[i]? = some d) := by
  rw [svBinding cd hi]
  cases hget : (cd.svDigests)[i]? with
  | none =>
      exact iff_of_false (fun h => Option.noConfusion h)
        (fun h => Option.noConfusion h)
  | some d' =>
      constructor
      · intro h; exact congrArg some (svToken_inj (Option.some.inj h))
      · intro h; rw [Option.some.inj h]; rfl

theorem svpBinding (cd : ContractSigData) {i : Nat} (hi : i < svpCount cd) :
    (memberTokens cd)[svpBase cd + i]? = (cd.resIds)[i]?.map svpToken :=
  memberTokens_getElem?_svp cd hi

theorem svpBinding_iff (cd : ContractSigData) {i : Nat} (hi : i < svpCount cd)
    {r : String} :
    ((memberTokens cd)[svpBase cd + i]? = some (svpToken r)) ↔
      ((cd.resIds)[i]? = some r) := by
  rw [svpBinding cd hi]
  cases hget : (cd.resIds)[i]? with
  | none =>
      exact iff_of_false (fun h => Option.noConfusion h)
        (fun h => Option.noConfusion h)
  | some r' =>
      constructor
      · intro h; exact congrArg some (svpToken_inj (Option.some.inj h))
      · intro h; rw [Option.some.inj h]; rfl

/-- The group-byte side: the member at an SV position is a `sort 1`
`axiomM` — position, not content, carries the digest. -/
theorem memberEntries_getElem?_sv_lt (cd : ContractSigData) {i : Nat}
    (hi : i < svCount cd) :
    (memberEntries cd)[i]? = some typeObjectMember := by
  have hmt : memberEntries cd =
      List.replicate (svCount cd) typeObjectMember ++
        (List.replicate (svpCount cd) typeObjectMember ++
          [ natFamMember, natZeroMemberAt (natBase cd),
            natSuccMemberAt (natBase cd), natRecMemberAt (natBase cd) ] ++
          [ predMember cd .pre, predMember cd .returnGuard,
            predMember cd .returnPost ] ++
          (cd.resIds).map (fun r => predMember cd (.residueGuard r)) ++
          (cd.resIds).map (fun r => predMember cd (.residuePost r)) ++
          [ predMember cd .bound ]) := by
    simp only [memberEntries, ← List.append_assoc]
  rw [hmt, List.getElem?_append_left (by rw [List.length_replicate]; exact hi),
      List.getElem?_replicate, if_pos hi]

/-! ## Token safety and the prefix-free code -/

/-- `a ++ '>' :: w = b ++ '>' :: w'` with `>`-free `a`,`b` forces
`a = b`. -/
theorem gtSfx {a b : List Char} {w₁ w₂ : List Char}
    (ha : '>' ∉ a) (hb : '>' ∉ b)
    (h : a ++ '>' :: w₁ = b ++ '>' :: w₂) : a = b ∧ w₁ = w₂ := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp_all
    | cons y ys =>
      simp at h
      have : '>' ∈ y :: ys := by rw [← h.1]; simp
      exact absurd this hb
  | cons x xs ih =>
    cases b with
    | nil =>
      simp at h
      have : '>' ∈ x :: xs := by rw [h.1]; simp
      exact absurd this ha
    | cons y ys =>
      simp at h
      obtain ⟨hxy, hrest⟩ := h
      subst hxy
      have ha' : '>' ∉ xs := fun m => ha (List.mem_cons_of_mem _ m)
      have hb' : '>' ∉ ys := fun m => hb (List.mem_cons_of_mem _ m)
      obtain ⟨hxs, hw⟩ := ih ha' hb' hrest
      subst hxs; subst hw
      exact ⟨rfl, rfl⟩

/-- The digest/residue side-condition making the surface token grammar
unambiguous: no fragment may contain the `>` delimiter (contract
digests are hash bytes). -/
def SigTokSafe (cd : ContractSigData) : Prop :=
  (∀ d ∈ cd.svDigests, '>' ∉ d.data) ∧ (∀ r ∈ cd.resIds, '>' ∉ r.data)

/-- The four token classes `exprOfSig`'s image reads through `atomsOf`. -/
def SigTok (cd : ContractSigData) (s : String) : Prop :=
  s = "Prop" ∨ s = "Nat" ∨
    (∃ d ∈ cd.svDigests, s = svToken d) ∨ (∃ r ∈ cd.resIds, s = svpToken r)

/-- Every signature token is nonempty. -/
theorem sigTok_nonempty {cd : ContractSigData} {s : String}
    (hs : SigTok cd s) : s.data ≠ [] := by
  rcases hs with rfl | rfl | ⟨d, _, rfl⟩ | ⟨r, _, rfl⟩
  · decide
  · decide
  · rw [svToken_cons]; simp
  · rw [svpToken_cons]; simp

/-- **Prefix-free**: `s`'s data prefixing `t`'s forces `s = t` — the
classes are distinguished by a fixed character (`P`/`N`/`S` at 0,
`SV<` vs `SVP<` at 2) and same-class fragments terminate in `>`. -/
theorem sigTok_prefix {cd : ContractSigData} (hsafe : SigTokSafe cd)
    {s t : String} (hs : SigTok cd s) (ht : SigTok cd t) {c : List Char}
    (h : s.data ++ c = t.data) : s = t := by
  rcases hs with rfl | rfl | ⟨d, hd, rfl⟩ | ⟨r, hr, rfl⟩ <;>
  rcases ht with rfl | rfl | ⟨e, he, rfl⟩ | ⟨r', hr', rfl⟩
  · rfl
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  · simp only [svToken_cons, List.cons_append, List.nil_append,
               List.append_assoc, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  · simp only [svpToken_cons, List.cons_append, List.nil_append,
               List.append_assoc, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  · rfl
  · simp only [svToken_cons, List.cons_append, List.nil_append,
               List.append_assoc, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  · simp only [svpToken_cons, List.cons_append, List.nil_append,
               List.append_assoc, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  · simp only [svToken_cons, List.cons_append, List.nil_append,
               List.append_assoc, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  · simp only [svToken_cons, List.cons_append, List.nil_append,
               List.append_assoc, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  · simp only [svToken_cons, List.cons_append, List.nil_append,
               List.append_assoc, List.cons.injEq] at h
    obtain ⟨hde, _⟩ := gtSfx (hsafe.1 d hd) (hsafe.1 e he) h.2.2.2
    exact congrArg svToken (String.ext hde)
  · simp only [svToken_cons, svpToken_cons, List.cons_append,
               List.nil_append, List.append_assoc, List.cons.injEq] at h
    exact absurd h.2.2.1 (by decide)
  · simp only [svpToken_cons, List.cons_append, List.nil_append,
               List.append_assoc, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  · simp only [svpToken_cons, List.cons_append, List.nil_append,
               List.append_assoc, List.cons.injEq] at h
    exact absurd h.1 (by decide)
  · simp only [svpToken_cons, svToken_cons, List.cons_append,
               List.nil_append, List.append_assoc, List.cons.injEq] at h
    exact absurd h.2.2.1 (by decide)
  · simp only [svpToken_cons, List.cons_append, List.nil_append,
               List.append_assoc, List.cons.injEq] at h
    obtain ⟨hde, _⟩ := gtSfx (hsafe.2 r hr) (hsafe.2 r' hr') h.2.2.2.2
    exact congrArg svpToken (String.ext hde)

/-- Append form: two signature tokens heading equal concatenations are
equal. -/
theorem sigTok_append_inj {cd : ContractSigData} (hsafe : SigTokSafe cd)
    {s t w w' : String} (hs : SigTok cd s) (ht : SigTok cd t)
    (h : s ++ w = t ++ w') : s = t := by
  have hd : s.data ++ w.data = t.data ++ w'.data := by
    have h' := congrArg String.data h
    rwa [String.data_append, String.data_append] at h'
  rcases List.append_eq_append_iff.mp hd with ⟨a, ht', _⟩ | ⟨a, hs', _⟩
  · exact sigTok_prefix hsafe hs ht ht'.symm
  · exact (sigTok_prefix hsafe ht hs hs'.symm).symm

/-! ## The signature image -/

/-- The atoms `exprOfSig` places under its `pi` spine: `SV<d>`/`SVP<r>`
member references, the `Nat` family, and `Prop`.  `Type`-valued so the
token extraction (`tokOfAtom`) can eliminate into `String`. -/
inductive SigAtom (cd : ContractSigData) : Expr Nat → Type
  | sv (d : String) (hd : d ∈ cd.svDigests) : SigAtom cd (svExpr cd d)
  | svp (r : String) (hr : r ∈ cd.resIds) : SigAtom cd (svpExpr cd r)
  | nat : SigAtom cd (natExpr cd)
  | prop : SigAtom cd propExpr

/-- A signature image: a `pi`-telescope of `SigAtom`s ending in one
(`exprOfSig cd s` for valid `s` is always one). -/
inductive SigForm (cd : ContractSigData) : Expr Nat → Type
  | atom {a : Expr Nat} : SigAtom cd a → SigForm cd a
  | pi {a b : Expr Nat} : SigAtom cd a → SigForm cd b → SigForm cd (.pi a b)

/-- The token a `SigAtom` spells to. -/
def tokOfAtom {cd : ContractSigData} {e : Expr Nat} : SigAtom cd e → String
  | .sv d _ => svToken d
  | .svp r _ => svpToken r
  | .nat => "Nat"
  | .prop => "Prop"

/-- The token list of a signature image (domain tokens left to right,
codomain last). -/
def toksOfForm {cd : ContractSigData} {e : Expr Nat} :
    SigForm cd e → List String
  | .atom a => [tokOfAtom a]
  | .pi a f => tokOfAtom a :: toksOfForm f

/-- Right-nested concatenation — `spellOf`'s `pi` traversal order. -/
def tokCat : List String → String
  | [] => ""
  | t :: ts => t ++ tokCat ts

theorem tokOfAtom_mem {cd : ContractSigData} {e : Expr Nat} (a : SigAtom cd e) :
    SigTok cd (tokOfAtom a) := by
  cases a with
  | sv d hd => exact Or.inr (Or.inr (Or.inl ⟨d, hd, rfl⟩))
  | svp r hr => exact Or.inr (Or.inr (Or.inr ⟨r, hr, rfl⟩))
  | nat => exact Or.inr (Or.inl rfl)
  | prop => exact Or.inl rfl

theorem spellOf_sigAtom {cd : ContractSigData} {e : Expr Nat}
    (a : SigAtom cd e) :
    spellOf (atomsOf cd) e = some (tokOfAtom a) := by
  cases a with
  | sv d hd => exact atomsOf_sv cd hd
  | svp r hr => exact atomsOf_svp cd hr
  | nat => exact atomsOf_natFam cd
  | prop => rfl

theorem spellOf_sigForm {cd : ContractSigData} {e : Expr Nat}
    (f : SigForm cd e) :
    spellOf (atomsOf cd) e = some (tokCat (toksOfForm f)) := by
  induction f with
  | atom a =>
      show spellOf (atomsOf cd) _ = some (tokCat [tokOfAtom a])
      rw [show tokCat [tokOfAtom a] = tokOfAtom a from String.append_empty _]
      exact spellOf_sigAtom a
  | pi a f ih =>
      show (do let sa ← spellOf (atomsOf cd) _
               let sb ← spellOf (atomsOf cd) _
               pure (sa ++ sb)) = _
      rw [spellOf_sigAtom a, ih]
      rfl

theorem toksOfForm_ne_nil {cd : ContractSigData} {e : Expr Nat}
    (f : SigForm cd e) : toksOfForm f ≠ [] := by
  cases f <;> simp [toksOfForm]

theorem toksOfForm_allSig {cd : ContractSigData} {e : Expr Nat}
    (f : SigForm cd e) : ∀ t ∈ toksOfForm f, SigTok cd t := by
  induction f with
  | atom a =>
      intro t ht
      simp only [toksOfForm, List.mem_singleton] at ht
      rw [ht]
      exact tokOfAtom_mem a
  | pi a f ih =>
      intro t ht
      simp only [toksOfForm, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact tokOfAtom_mem a
      · exact ih t ht

/-- `tokCat` on signature tokens is injective — the code is
prefix-free. -/
theorem tokCat_inj {cd : ContractSigData} (hsafe : SigTokSafe cd)
    {ts₁ ts₂ : List String}
    (h₁ : ∀ t ∈ ts₁, SigTok cd t) (h₂ : ∀ t ∈ ts₂, SigTok cd t)
    (h : tokCat ts₁ = tokCat ts₂) : ts₁ = ts₂ := by
  induction ts₁ generalizing ts₂ with
  | nil =>
      cases ts₂ with
      | nil => rfl
      | cons t₂ ts₂' =>
          have hne : (t₂ ++ tokCat ts₂').data ≠ [] := by
            rw [String.data_append]
            intro hnil
            exact sigTok_nonempty (h₂ t₂ (List.mem_cons_self _ _))
              (List.append_eq_nil.mp hnil).1
          simp only [tokCat] at h
          exact absurd (congrArg String.data h.symm) hne
  | cons t₁ ts₁' ih =>
      cases ts₂ with
      | nil =>
          have hne : (t₁ ++ tokCat ts₁').data ≠ [] := by
            rw [String.data_append]
            intro hnil
            exact sigTok_nonempty (h₁ t₁ (List.mem_cons_self _ _))
              (List.append_eq_nil.mp hnil).1
          simp only [tokCat] at h
          exact absurd (congrArg String.data h) hne
      | cons t₂ ts₂' =>
          simp only [tokCat] at h
          have htok : t₁ = t₂ := sigTok_append_inj hsafe
            (h₁ t₁ (List.mem_cons_self _ _))
            (h₂ t₂ (List.mem_cons_self _ _)) h
          subst htok
          have hrest : tokCat ts₁' = tokCat ts₂' := by
            have hd := congrArg String.data h
            rw [String.data_append, String.data_append] at hd
            exact String.ext ((List.append_right_inj _).mp hd)
          rw [ih (fun t ht => h₁ t (List.mem_cons_of_mem _ ht))
            (fun t ht => h₂ t (List.mem_cons_of_mem _ ht)) hrest]

/-- `tokOfAtom` determines the atom — the token class selects the
constructor, its payload the index. -/
theorem tokOfAtom_inj {cd : ContractSigData} {e₁ e₂ : Expr Nat}
    (a₁ : SigAtom cd e₁) (a₂ : SigAtom cd e₂)
    (h : tokOfAtom a₁ = tokOfAtom a₂) : e₁ = e₂ := by
  cases a₁ <;> cases a₂
  · rename_i d _ e _
    rw [svToken_inj h]
  · rename_i d _ r _
    exfalso
    have hd : (svToken d).data = (svpToken r).data := congrArg String.data h
    rw [svToken_cons, svpToken_cons] at hd
    simp only [List.cons.injEq] at hd
    exact absurd hd.2.2.1 (by decide)
  · rename_i d _
    exfalso
    have hd : (svToken d).data = ("Nat").data := congrArg String.data h
    rw [svToken_cons] at hd
    simp only [List.cons.injEq] at hd
    exact absurd hd.1 (by decide)
  · rename_i d _
    exfalso
    have hd : (svToken d).data = ("Prop").data := congrArg String.data h
    rw [svToken_cons] at hd
    simp only [List.cons.injEq] at hd
    exact absurd hd.1 (by decide)
  · rename_i r _ d _
    exfalso
    have hd : (svpToken r).data = (svToken d).data := congrArg String.data h
    rw [svpToken_cons, svToken_cons] at hd
    simp only [List.cons.injEq] at hd
    exact absurd hd.2.2.1 (by decide)
  · rename_i r _ e _
    rw [svpToken_inj h]
  · rename_i r _
    exfalso
    have hd : (svpToken r).data = ("Nat").data := congrArg String.data h
    rw [svpToken_cons] at hd
    simp only [List.cons.injEq] at hd
    exact absurd hd.1 (by decide)
  · rename_i r _
    exfalso
    have hd : (svpToken r).data = ("Prop").data := congrArg String.data h
    rw [svpToken_cons] at hd
    simp only [List.cons.injEq] at hd
    exact absurd hd.1 (by decide)
  · rename_i d _
    exfalso
    have hd : ("Nat").data = (svToken d).data := congrArg String.data h
    rw [svToken_cons] at hd
    simp only [List.cons.injEq] at hd
    exact absurd hd.1 (by decide)
  · rename_i r _
    exfalso
    have hd : ("Nat").data = (svpToken r).data := congrArg String.data h
    rw [svpToken_cons] at hd
    simp only [List.cons.injEq] at hd
    exact absurd hd.1 (by decide)
  · rfl
  · exfalso
    have hd : ("Nat").data = ("Prop").data := congrArg String.data h
    exact absurd hd (by decide)
  · rename_i d _
    exfalso
    have hd : ("Prop").data = (svToken d).data := congrArg String.data h
    rw [svToken_cons] at hd
    simp only [List.cons.injEq] at hd
    exact absurd hd.1 (by decide)
  · rename_i r _
    exfalso
    have hd : ("Prop").data = (svpToken r).data := congrArg String.data h
    rw [svpToken_cons] at hd
    simp only [List.cons.injEq] at hd
    exact absurd hd.1 (by decide)
  · exfalso
    have hd : ("Prop").data = ("Nat").data := congrArg String.data h
    exact absurd hd (by decide)
  · rfl

/-- The token list determines the image: `toksOfForm` is injective. -/
theorem toksOfForm_inj {cd : ContractSigData} {e₁ e₂ : Expr Nat}
    (f₁ : SigForm cd e₁) (f₂ : SigForm cd e₂)
    (h : toksOfForm f₁ = toksOfForm f₂) : e₁ = e₂ := by
  induction f₁ generalizing e₂ with
  | atom a₁ =>
      cases f₂ with
      | atom a₂ =>
          have h' : [tokOfAtom a₁] = [tokOfAtom a₂] := h
          injection h' with htok hnil
          exact tokOfAtom_inj a₁ a₂ htok
      | pi a₂ f₂ =>
          have h' : [tokOfAtom a₁] = tokOfAtom a₂ :: toksOfForm f₂ := h
          injection h' with htok hnil
          exact absurd hnil.symm (toksOfForm_ne_nil f₂)
  | pi a₁ f₁' ih =>
      cases f₂ with
      | atom a₂ =>
          have h' : tokOfAtom a₁ :: toksOfForm f₁' = [tokOfAtom a₂] := h
          injection h' with htok hnil
          exact absurd hnil (toksOfForm_ne_nil f₁')
      | pi a₂ f₂ =>
          have h' : tokOfAtom a₁ :: toksOfForm f₁' =
              tokOfAtom a₂ :: toksOfForm f₂ := h
          injection h' with htok hrest
          have he1 := tokOfAtom_inj a₁ a₂ htok
          subst he1
          have := ih f₂ hrest
          subst this
          rfl

/-- **spellOf injective** on the signature image: the surface token
uniquely determines the signature `Expr`. -/
theorem spellOf_inj {cd : ContractSigData} (hsafe : SigTokSafe cd)
    {e₁ e₂ : Expr Nat} (f₁ : SigForm cd e₁) (f₂ : SigForm cd e₂)
    (h : spellOf (atomsOf cd) e₁ = spellOf (atomsOf cd) e₂) :
    e₁ = e₂ := by
  rw [spellOf_sigForm f₁, spellOf_sigForm f₂] at h
  injection h with h'
  exact toksOfForm_inj f₁ f₂
    (tokCat_inj hsafe (toksOfForm_allSig f₁) (toksOfForm_allSig f₂) h')

/-! ## The signatures are in the image -/

/-- Each valid slot's signature is a `SigForm` — a `def` so its token
list computes (`theorem`s are opaque to `toksOfForm`/`tokCat`). -/
def exprOfSig_isSig (cd : ContractSigData) (s : PredSlot)
    (hs : s.validFor cd) : SigForm cd (exprOfSig cd s) := by
  cases s with
  | pre | returnGuard | residueGuard _ =>
      exact .pi (.sv _ (tin_mem cd)) (.pi (.sv _ (tst_mem cd)) (.atom .prop))
  | returnPost =>
      exact .pi (.sv _ (tin_mem cd)) (.pi (.sv _ (tst_mem cd))
        (.pi (.sv _ (tout_mem cd)) (.pi (.sv _ (tst_mem cd)) (.atom .prop))))
  | residuePost _ =>
      exact .pi (.sv _ (tin_mem cd)) (.pi (.sv _ (tst_mem cd))
        (.pi (.svp _ hs) (.atom .prop)))
  | bound =>
      exact .pi (.sv _ (tin_mem cd)) (.pi (.sv _ (tst_mem cd)) (.atom .nat))

/-! ## member_typing -/

/-- Each signature is a `Sort u` type inside the bound predicate
environment (the admitted SV/SVP/Nat members supply its `const`
references). -/
def predMember_typed (cd : ContractSigData) (s : PredSlot)
    (hs : s.validFor cd) :
    Σ' u, HasTyT (predEnvOf cd) 0 [] (exprOfSig cd s) (.sort u) :=
  predSlotTy cd (predEnvOf_sv (tin_mem cd)) (predEnvOf_sv (tst_mem cd))
    (predEnvOf_sv (tout_mem cd)) (predEnvOf_natFam cd)
    (fun _ hr => predEnvOf_svp hr) s hs

/-- **member_typing**: the predicate member's stored type IS the
signature and it is typed in the environment — the wire's missing
check (`m.mtype = sigExpr ∧ HasTyT m.mtype (.sort u)`, #6652 plan 2). -/
theorem member_typing (cd : ContractSigData) (s : PredSlot)
    (hs : s.validFor cd) :
    ∃ m, (predEnvOf cd).members (predIndex cd s) = some m ∧
      m.mtype = exprOfSig cd s ∧
      Nonempty (Σ' u, HasTyT (predEnvOf cd) 0 [] m.mtype (.sort u)) := by
  obtain ⟨m, hm, hty⟩ := predEnvOf_predIndex cd s hs
  exact ⟨m, hm, hty, ⟨hty ▸ predMember_typed cd s hs⟩⟩

/-! ## Agreement with `rcic.pred_sig_spell` -/

/-- scm `pred_sig_spell`'s shared prefix `p`. -/
def sigSpellP (cd : ContractSigData) : String :=
  "SV<" ++ cd.tin ++ ">SV<" ++ cd.tst ++ ">"

theorem spell_pre (cd : ContractSigData) :
    spellOf (atomsOf cd) (exprOfSig cd .pre) =
      some (sigSpellP cd ++ "Prop") := by
  rw [spellOf_sigForm (exprOfSig_isSig cd .pre trivial)]
  apply congrArg some
  show svToken cd.tin ++ (svToken cd.tst ++ ("Prop" ++ "")) =
      sigSpellP cd ++ "Prop"
  rw [String.append_empty]
  apply String.ext
  simp only [sigSpellP, svToken, String.data_append, List.append_assoc,
             List.cons_append, List.nil_append]

theorem spell_rg (cd : ContractSigData) :
    spellOf (atomsOf cd) (exprOfSig cd .returnGuard) =
      some (sigSpellP cd ++ "Prop") :=
  spell_pre cd

theorem spell_case_g (cd : ContractSigData) (r : String) :
    spellOf (atomsOf cd) (exprOfSig cd (.residueGuard r)) =
      some (sigSpellP cd ++ "Prop") :=
  spell_pre cd

theorem spell_rp (cd : ContractSigData) :
    spellOf (atomsOf cd) (exprOfSig cd .returnPost) =
      some (sigSpellP cd ++ "SV<" ++ cd.tout ++ ">SV<" ++ cd.tst ++ ">Prop") := by
  rw [spellOf_sigForm (exprOfSig_isSig cd .returnPost trivial)]
  apply congrArg some
  show svToken cd.tin ++ (svToken cd.tst ++
      (svToken cd.tout ++ (svToken cd.tst ++ ("Prop" ++ "")))) = _
  rw [String.append_empty]
  apply String.ext
  simp only [sigSpellP, svToken, String.data_append, List.append_assoc,
             List.cons_append, List.nil_append]

theorem spell_case_p (cd : ContractSigData) {r : String}
    (hr : r ∈ cd.resIds) :
    spellOf (atomsOf cd) (exprOfSig cd (.residuePost r)) =
      some (sigSpellP cd ++ "SVP<" ++ r ++ ">Prop") := by
  rw [spellOf_sigForm (exprOfSig_isSig cd (.residuePost r) hr)]
  apply congrArg some
  show svToken cd.tin ++ (svToken cd.tst ++
      (svpToken r ++ ("Prop" ++ ""))) = _
  rw [String.append_empty]
  apply String.ext
  simp only [sigSpellP, svToken, svpToken, String.data_append,
             List.append_assoc, List.cons_append, List.nil_append]

theorem spell_bound (cd : ContractSigData) :
    spellOf (atomsOf cd) (exprOfSig cd .bound) =
      some (sigSpellP cd ++ "Nat") := by
  rw [spellOf_sigForm (exprOfSig_isSig cd .bound trivial)]
  apply congrArg some
  show svToken cd.tin ++ (svToken cd.tst ++ ("Nat" ++ "")) =
      sigSpellP cd ++ "Nat"
  rw [String.append_empty]
  apply String.ext
  simp only [sigSpellP, svToken, String.data_append, List.append_assoc,
             List.cons_append, List.nil_append]

/-! ## The CT-001 bridge -/

/-- The wire's token equality decides member-type equality on the
signature image: `spellOf mtype = spellOf (exprOfSig s) ↔ mtype =
exprOfSig s` (#6652 plan 4, under `SigTokSafe`). -/
theorem spellOf_eq_exprOfSig_iff {cd : ContractSigData}
    (hsafe : SigTokSafe cd) {e : Expr Nat} (he : SigForm cd e)
    (s : PredSlot) (hs : s.validFor cd) :
    spellOf (atomsOf cd) e = spellOf (atomsOf cd) (exprOfSig cd s) ↔
      e = exprOfSig cd s :=
  ⟨fun h => spellOf_inj hsafe he (exprOfSig_isSig cd s hs) h,
   fun h => congrArg _ h⟩

/-- The wire check against the scm `pre`/`rg`/`case_g` token: matching
`sigSpellP ++ "Prop"` makes the member type the guard signature —
the CT-001 bridge's `←` direction turned into Lean equality. -/
theorem spell_eq_guardTok_iff {cd : ContractSigData} (hsafe : SigTokSafe cd)
    {e : Expr Nat} (he : SigForm cd e) :
    spellOf (atomsOf cd) e = some (sigSpellP cd ++ "Prop") ↔
      e = exprOfSig cd .pre := by
  rw [← spell_pre]
  exact spellOf_eq_exprOfSig_iff hsafe he .pre trivial

/-- Same, against the scm `rp` token. -/
theorem spell_eq_rpTok_iff {cd : ContractSigData} (hsafe : SigTokSafe cd)
    {e : Expr Nat} (he : SigForm cd e) :
    spellOf (atomsOf cd) e =
        some (sigSpellP cd ++ "SV<" ++ cd.tout ++ ">SV<" ++ cd.tst ++ ">Prop") ↔
      e = exprOfSig cd .returnPost := by
  rw [← spell_rp]
  exact spellOf_eq_exprOfSig_iff hsafe he .returnPost trivial

/-- Same, against the scm `bound` token. -/
theorem spell_eq_boundTok_iff {cd : ContractSigData} (hsafe : SigTokSafe cd)
    {e : Expr Nat} (he : SigForm cd e) :
    spellOf (atomsOf cd) e = some (sigSpellP cd ++ "Nat") ↔
      e = exprOfSig cd .bound := by
  rw [← spell_bound]
  exact spellOf_eq_exprOfSig_iff hsafe he .bound trivial

end Rcic.PredSig
