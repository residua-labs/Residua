/-
RCIC 07 §3 — G1-S2: the bound predicate environment object and the
`all_predicate_refs_resolve` shadow.

`predEnvOf cd` builds the contract's `ResolvedEnv` from `memberEntries`
(ruling on #6652: one checked group per contract; the flat kernel member
index is the canonical-order list index). The env is exactly the contract's
group — the scm image is closure-complete (Annex 25.11 admits extra entries),
but every clause this module states is per-member, so extending `members` at
other indices preserves them.

`allPredicateRefsResolve` is the Lean shadow of `pred_env_one`'s resolve
clauses (`apps/rcic-pred-env`: group-find + canon + `0 ≤ i < a`): at the
kernel flattening, resolve is member existence at the ref's flat index. The
strengthened statement `predEnvOf_predIndex` pins the resolved member's
identity AND its `mtype` — this is where "the six predicate types" live, so
the shadow is stated at member-value precision, not just existence.

Carrier note: `pred_env_refs` enumerates `[pre, rg, rp, bound]` then each
case's `(g, p)` pair in the contract's `cases` order; the canonical member
order (ruling 1) enumerates predicates in §4 slot order with per-residue
slots sorted by residue id. Order is immaterial to the resolve ∀, which is
stated over `predSlotsOf` (the canonical enumeration).
-/
import rcic.RcicPredSigObj

namespace Rcic.PredSig
open Rcic.Declarative Rcic.ScopeExact

/-- The bound predicate environment for one contract's group: `members i`
is the `i`-th entry of the canonical member list (`none` past it). -/
def predEnvOf (cd : ContractSigData) : ResolvedEnv where
  members := fun i => (memberEntries cd)[i]?

/-- The non-predicate prefix — SV block ++ SVP block ++ Nat block — whose
length is `predBase`. -/
def prefixEntries (cd : ContractSigData) : List CheckedMember :=
  List.replicate (svCount cd) typeObjectMember ++
  List.replicate (svpCount cd) typeObjectMember ++
  [ natFamMember, natZeroMemberAt (natBase cd),
    natSuccMemberAt (natBase cd), natRecMemberAt (natBase cd) ]

/-- The contract's predicate slots in canonical member order. -/
def predSlotsOf (cd : ContractSigData) : List PredSlot :=
  [.pre, .returnGuard, .returnPost] ++
  (cd.resIds).map PredSlot.residueGuard ++
  (cd.resIds).map PredSlot.residuePost ++
  [.bound]

/-- The predicate block as a literal member list. -/
def predEntriesOf (cd : ContractSigData) : List CheckedMember :=
  [ predMember cd .pre, predMember cd .returnGuard,
    predMember cd .returnPost ] ++
  (cd.resIds).map (fun r => predMember cd (.residueGuard r)) ++
  (cd.resIds).map (fun r => predMember cd (.residuePost r)) ++
  [ predMember cd .bound ]

theorem prefixEntries_length (cd : ContractSigData) :
    (prefixEntries cd).length = predBase cd := by
  simp [prefixEntries, predBase, natBase, svpBase]

theorem predSlotsOf_map_predMember (cd : ContractSigData) :
    (predSlotsOf cd).map (predMember cd) = predEntriesOf cd := by
  simp only [predSlotsOf, predEntriesOf, List.map_append, List.map_map]
  rfl

theorem memberEntries_eq_prefix_append (cd : ContractSigData) :
    memberEntries cd =
      prefixEntries cd ++ predEntriesOf cd := by
  simp only [memberEntries, prefixEntries, predEntriesOf,
    List.append_assoc]

theorem memberEntries_eq_prefix_append_slots (cd : ContractSigData) :
    memberEntries cd =
      prefixEntries cd ++ (predSlotsOf cd).map (predMember cd) := by
  rw [predSlotsOf_map_predMember]
  exact memberEntries_eq_prefix_append cd

theorem predEntriesOf_length (cd : ContractSigData) :
    (predEntriesOf cd).length = 3 + 2 * svpCount cd + 1 := by
  simp only [predEntriesOf, List.length_append, List.length_map,
    List.length_cons, List.length_nil, svpCount]
  omega

theorem memberEntries_length (cd : ContractSigData) :
    (memberEntries cd).length = memberCount cd := by
  rw [memberEntries_eq_prefix_append, List.length_append,
    prefixEntries_length, predEntriesOf_length]
  simp only [memberCount, predIndex]
  omega

/-- A predicate slot is VALID for `cd` when its residue parameter (if any)
names a residue of the contract — the premise `pred_env_one` enforces at the
wire (`0 ≤ i < a` against the resolved group). -/
def PredSlot.validFor (cd : ContractSigData) : PredSlot → Prop
  | .residueGuard r | .residuePost r => r ∈ cd.resIds
  | _ => True

theorem predIndex_ge_predBase (cd : ContractSigData) (s : PredSlot) :
    predBase cd ≤ predIndex cd s := by
  cases s <;> simp only [predIndex] <;> omega

theorem predIndex_lt_memberCount (cd : ContractSigData) (s : PredSlot)
    (hs : s.validFor cd) : predIndex cd s < memberCount cd := by
  cases s with
  | pre | returnGuard | returnPost | bound =>
      simp only [memberCount, predIndex]; omega
  | residueGuard r =>
      have hr : r ∈ cd.resIds := hs
      have hlt : (cd.resIds).findIdx (· == r) < (cd.resIds).length :=
        List.findIdx_lt_length_of_exists ⟨r, hr, by simp⟩
      simp only [memberCount, predIndex, svpCount]; omega
  | residuePost r =>
      have hr : r ∈ cd.resIds := hs
      have hlt : (cd.resIds).findIdx (· == r) < (cd.resIds).length :=
        List.findIdx_lt_length_of_exists ⟨r, hr, by simp⟩
      simp only [memberCount, predIndex, svpCount]; omega

/-- `resIds[findIdx r] = r` for `r ∈ resIds` — the findIdx roundtrip. -/
theorem resIds_getElem_findIdx (cd : ContractSigData) {r : String}
    (hr : r ∈ cd.resIds) :
    ∃ hlt, (cd.resIds)[(cd.resIds).findIdx (· == r)]'hlt = r := by
  have hlt : (cd.resIds).findIdx (· == r) < (cd.resIds).length :=
    List.findIdx_lt_length_of_exists ⟨r, hr, by simp⟩
  exact ⟨hlt, eq_of_beq (List.findIdx_getElem (p := (· == r))
    (xs := cd.resIds) (w := hlt))⟩

/-! ## Per-block lookups -/

theorem memberEntries_getElem?_sv {cd : ContractSigData} {d : String}
    (hd : d ∈ cd.svDigests) :
    (memberEntries cd)[svIndexOf cd d]? = some typeObjectMember := by
  have hlt : svIndexOf cd d < svCount cd :=
    List.findIdx_lt_length_of_exists ⟨d, hd, by simp⟩
  rw [memberEntries_eq_prefix_append,
    List.getElem?_append_left (by
      rw [prefixEntries_length]
      simp only [predBase, natBase, svpBase]; omega)]
  simp only [prefixEntries]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_replicate]; omega),
    List.getElem?_append_left (by
      rw [List.length_replicate]; exact hlt)]
  rw [List.getElem?_replicate, if_pos hlt]

theorem memberEntries_getElem?_svp {cd : ContractSigData} {r : String}
    (hr : r ∈ cd.resIds) :
    (memberEntries cd)[svpIndexOf cd r]? = some typeObjectMember := by
  have hlt : (cd.resIds).findIdx (· == r) < svpCount cd :=
    List.findIdx_lt_length_of_exists ⟨r, hr, by simp⟩
  rw [memberEntries_eq_prefix_append,
    List.getElem?_append_left (by
      rw [prefixEntries_length]
      simp only [svpIndexOf, svpBase, predBase, natBase]; omega)]
  simp only [prefixEntries]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_replicate, svpIndexOf,
      svpBase]; omega),
    List.getElem?_append_right (by
      simp only [List.length_replicate, svpIndexOf, svpBase]; omega),
    List.length_replicate,
    show svpIndexOf cd r - svCount cd = (cd.resIds).findIdx (· == r) from
      by simp only [svpIndexOf, svpBase]; omega]
  rw [List.getElem?_replicate, if_pos hlt]

/-- The Nat block occupies `[natBase, natBase + 4)`. -/
theorem memberEntries_getElem?_nat (cd : ContractSigData) (k : Nat)
    (hk : k < 4) :
    (memberEntries cd)[natBase cd + k]? =
      ([ natFamMember, natZeroMemberAt (natBase cd),
         natSuccMemberAt (natBase cd), natRecMemberAt (natBase cd) ]
        : List CheckedMember)[k]? := by
  rw [memberEntries_eq_prefix_append,
    List.getElem?_append_left (by
      rw [prefixEntries_length]
      simp only [predBase, natBase, svpBase]; omega)]
  simp only [prefixEntries]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_replicate, natBase,
      svpBase]; omega)]
  simp only [List.length_append, List.length_replicate]
  rw [show natBase cd + k - (svCount cd + svpCount cd) = k from
      by simp only [natBase, svpBase]; omega]

theorem memberEntries_getElem?_natFam (cd : ContractSigData) :
    (memberEntries cd)[natFamIndex cd]? = some natFamMember := by
  simpa [natFamIndex] using memberEntries_getElem?_nat cd 0 (by omega)

theorem memberEntries_getElem?_natZero (cd : ContractSigData) :
    (memberEntries cd)[natZeroIndex cd]? =
      some (natZeroMemberAt (natBase cd)) := by
  simpa [natZeroIndex] using memberEntries_getElem?_nat cd 1 (by omega)

theorem memberEntries_getElem?_natSucc (cd : ContractSigData) :
    (memberEntries cd)[natSuccIndex cd]? =
      some (natSuccMemberAt (natBase cd)) := by
  simpa [natSuccIndex] using memberEntries_getElem?_nat cd 2 (by omega)

theorem memberEntries_getElem?_natRec (cd : ContractSigData) :
    (memberEntries cd)[natRecIndex cd]? =
      some (natRecMemberAt (natBase cd)) := by
  simpa [natRecIndex] using memberEntries_getElem?_nat cd 3 (by omega)

/-- Length of the `pre3 ++ guardMap` portion of the predicate block. -/
theorem predEntriesOf_head_length (cd : ContractSigData) :
    (([ predMember cd .pre, predMember cd .returnGuard,
        predMember cd .returnPost ] ++
      (cd.resIds).map (fun r => predMember cd (.residueGuard r))) ++
      (cd.resIds).map (fun r => predMember cd (.residuePost r))).length =
      3 + 2 * svpCount cd := by
  simp only [List.length_append, List.length_map, List.length_cons,
    List.length_nil, svpCount]
  omega

/-- Length of the `pre3` portion of the predicate block. -/
theorem predEntriesOf_pre3_length (cd : ContractSigData) :
    ([ predMember cd .pre, predMember cd .returnGuard,
        predMember cd .returnPost ] ++
      (cd.resIds).map (fun r => predMember cd (.residueGuard r))).length =
      3 + svpCount cd := by
  simp only [List.length_append, List.length_map, List.length_cons,
    List.length_nil, svpCount]

/-- Slot-offset lookup inside `predEntriesOf`: `predIndex s - predBase` is
the slot's position in the predicate block. -/
theorem predEntriesOf_getElem?_offset (cd : ContractSigData) (s : PredSlot)
    (hs : s.validFor cd) :
    (predEntriesOf cd)[predIndex cd s - predBase cd]? =
      some (predMember cd s) := by
  cases s with
  | pre =>
      have hoff : predIndex cd .pre - predBase cd = 0 := by
        simp only [predIndex]; omega
      rw [hoff]
      simp only [predEntriesOf]
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_map, List.length_cons,
          List.length_nil]; omega),
        List.getElem?_append_left (by
          simp only [List.length_append, List.length_map, List.length_cons,
            List.length_nil]; omega),
        List.getElem?_append_left (by simp)]
      rfl
  | returnGuard =>
      have hoff : predIndex cd .returnGuard - predBase cd = 1 := by
        simp only [predIndex]; omega
      rw [hoff]
      simp only [predEntriesOf]
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_map, List.length_cons,
          List.length_nil]; omega),
        List.getElem?_append_left (by
          simp only [List.length_append, List.length_map, List.length_cons,
            List.length_nil]; omega),
        List.getElem?_append_left (by simp)]
      rfl
  | returnPost =>
      have hoff : predIndex cd .returnPost - predBase cd = 2 := by
        simp only [predIndex]; omega
      rw [hoff]
      simp only [predEntriesOf]
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_map, List.length_cons,
          List.length_nil]; omega),
        List.getElem?_append_left (by
          simp only [List.length_append, List.length_map, List.length_cons,
            List.length_nil]; omega),
        List.getElem?_append_left (by simp)]
      rfl
  | residueGuard r =>
      obtain ⟨hlt, hel⟩ := resIds_getElem_findIdx cd hs
      have hoff : predIndex cd (.residueGuard r) - predBase cd =
          3 + (cd.resIds).findIdx (· == r) := by
        simp only [predIndex]; omega
      rw [hoff]
      simp only [predEntriesOf]
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_map, List.length_cons,
          List.length_nil]; omega),
        List.getElem?_append_left (by
          simp only [List.length_append, List.length_map, List.length_cons,
            List.length_nil]; omega),
        List.getElem?_append_right (by
          simp only [List.length_cons, List.length_nil]; omega),
        show ([predMember cd .pre, predMember cd .returnGuard,
                predMember cd .returnPost] : List CheckedMember).length = 3
          from rfl,
        show 3 + (cd.resIds).findIdx (· == r) - 3 =
          (cd.resIds).findIdx (· == r) from by omega,
        List.getElem?_map, List.getElem?_eq_getElem hlt, hel]
      rfl
  | residuePost r =>
      obtain ⟨hlt, hel⟩ := resIds_getElem_findIdx cd hs
      have hoff : predIndex cd (.residuePost r) - predBase cd =
          3 + svpCount cd + (cd.resIds).findIdx (· == r) := by
        simp only [predIndex]; omega
      rw [hoff]
      simp only [predEntriesOf]
      rw [List.getElem?_append_left (by
        simp only [List.length_append, List.length_map, List.length_cons,
          List.length_nil, svpCount]; omega),
        List.getElem?_append_right (by
          rw [predEntriesOf_pre3_length]; simp only [svpCount]; omega),
        predEntriesOf_pre3_length,
        show 3 + svpCount cd + (cd.resIds).findIdx (· == r) -
            (3 + svpCount cd) = (cd.resIds).findIdx (· == r) from
          by omega,
        List.getElem?_map, List.getElem?_eq_getElem hlt, hel]
      rfl
  | bound =>
      have hoff : predIndex cd .bound - predBase cd =
          3 + 2 * svpCount cd := by
        simp only [predIndex]; omega
      rw [hoff]
      simp only [predEntriesOf]
      rw [List.getElem?_append_right (by
        rw [predEntriesOf_head_length]; omega),
        predEntriesOf_head_length, Nat.sub_self]
      rfl

/-- The generic prefix-strip: `memberEntries[predBase + j]` indexes the
predicate block at `j`. -/
theorem memberEntries_getElem?_add_predBase (cd : ContractSigData) (j : Nat) :
    (memberEntries cd)[predBase cd + j]? = (predEntriesOf cd)[j]? := by
  rw [memberEntries_eq_prefix_append,
    List.getElem?_append_right (by
      rw [prefixEntries_length]; omega),
    prefixEntries_length,
    show predBase cd + j - predBase cd = j from by omega]

/-- The predicate block lookup: `memberEntries[predIndex s] = predMember s`
for every valid slot — the strengthened shadow of the wire's `i < a`. -/
theorem memberEntries_getElem?_predIndex (cd : ContractSigData)
    (s : PredSlot) (hs : s.validFor cd) :
    (memberEntries cd)[predIndex cd s]? = some (predMember cd s) := by
  have hge := predIndex_ge_predBase cd s
  rw [show predIndex cd s = predBase cd + (predIndex cd s - predBase cd)
        from by omega,
    memberEntries_getElem?_add_predBase,
    predEntriesOf_getElem?_offset cd s hs]

/-! ## The env-level statements -/

/-- `refs_resolve` at a valid slot — the wire's `i < a` member-existence,
strengthened to the member's identity and `mtype`. -/
theorem predEnvOf_predIndex (cd : ContractSigData) (s : PredSlot)
    (hs : s.validFor cd) :
    ∃ m, (predEnvOf cd).members (predIndex cd s) = some m ∧
      m.mtype = exprOfSig cd s :=
  ⟨predMember cd s, memberEntries_getElem?_predIndex cd s hs, rfl⟩

/-- `all_predicate_refs_resolve` (the `apps/rcic-pred-env` result): every
predicate ref of the contract resolves to a member of `predEnvOf cd`. -/
def allPredicateRefsResolve (cd : ContractSigData) : Prop :=
  ∀ s ∈ predSlotsOf cd,
    ∃ m, (predEnvOf cd).members (predIndex cd s) = some m

theorem slot_valid_of_mem (cd : ContractSigData) {s : PredSlot}
    (hs : s ∈ predSlotsOf cd) : s.validFor cd := by
  simp [predSlotsOf] at hs
  rcases hs with rfl | rfl | rfl | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | rfl
  · trivial
  · trivial
  · trivial
  · exact hr
  · exact hr
  · trivial

theorem all_predicate_refs_resolve (cd : ContractSigData) :
    allPredicateRefsResolve cd := by
  intro s hs
  obtain ⟨m, hm, _⟩ := predEnvOf_predIndex cd s (slot_valid_of_mem cd hs)
  exact ⟨m, hm⟩

/-- `refs_resolve` for the type-object members the signatures name. -/
theorem predEnvOf_sv {cd : ContractSigData} {d : String}
    (hd : d ∈ cd.svDigests) :
    (predEnvOf cd).members (svIndexOf cd d) = some typeObjectMember :=
  memberEntries_getElem?_sv hd

theorem predEnvOf_svp {cd : ContractSigData} {r : String}
    (hr : r ∈ cd.resIds) :
    (predEnvOf cd).members (svpIndexOf cd r) = some typeObjectMember :=
  memberEntries_getElem?_svp hr

/-- The Nat block at its canonical base. -/
theorem predEnvOf_natFam (cd : ContractSigData) :
    (predEnvOf cd).members (natFamIndex cd) = some natFamMember :=
  memberEntries_getElem?_natFam cd

theorem predEnvOf_natZero (cd : ContractSigData) :
    (predEnvOf cd).members (natZeroIndex cd) =
      some (natZeroMemberAt (natBase cd)) :=
  memberEntries_getElem?_natZero cd

theorem predEnvOf_natSucc (cd : ContractSigData) :
    (predEnvOf cd).members (natSuccIndex cd) =
      some (natSuccMemberAt (natBase cd)) :=
  memberEntries_getElem?_natSucc cd

theorem predEnvOf_natRec (cd : ContractSigData) :
    (predEnvOf cd).members (natRecIndex cd) =
      some (natRecMemberAt (natBase cd)) :=
  memberEntries_getElem?_natRec cd

/-- Past the group, no member — `a:`-bounded lookups refuse (the wire's
`i < a` misses at the flat index). -/
theorem predEnvOf_none_of_ge (cd : ContractSigData) {i : Nat}
    (hi : memberCount cd ≤ i) :
    (predEnvOf cd).members i = none := by
  show (memberEntries cd)[i]? = none
  exact List.getElem?_eq_none (by rw [memberEntries_length]; exact hi)

/-! ## Pins -/

theorem pin_predEnvOf_pre :
    (predEnvOf pinSigData).members 8 =
      some (predMember pinSigData .pre) := rfl

theorem pin_predEnvOf_bound :
    (predEnvOf pinSigData).members 13 =
      some (predMember pinSigData .bound) := rfl

theorem pin_predEnvOf_sv_d0 :
    (predEnvOf pinSigData).members 0 = some typeObjectMember := rfl

theorem pin_predEnvOf_natFam :
    (predEnvOf pinSigData).members 4 = some natFamMember := rfl

theorem pin_predEnvOf_past_end :
    (predEnvOf pinSigData).members 14 = none := rfl

end Rcic.PredSig
