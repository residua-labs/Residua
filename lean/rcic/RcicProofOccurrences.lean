import rcic.RcicPiSourceOriginCalls

/-!
# All existing PEqT proof-root occurrences in an actual typed reduction

This domain follows every ParRedT recursive child and every nested raw PEqT
structural child. HasTyT/ConvT fields contain no PEqT objects; their irr nodes
are latent J-production sites, not existing proof roots. They belong to the
planned/transport inventory, not to a claim of general D/J coverage.

The site stores its ORIGINAL loose proof fields and exact left context.
Nested raw sites have no carried common index. This file does not manufacture
one, provide general uniqueness, or assert a global AnsweredOrigins invariant.
The complete finite enumeration is indexed by the original derivation.
closure_claim = 0.
-/

namespace Rcic.Declarative.F8Occurrences

structure ProofSite (E : ResolvedEnv) (n : Nat) where
  context : LCtx
  left : Expr Nat
  right : Expr Nat
  leftProp : Expr Nat
  rightProp : Expr Nat
  leftPropTy : HasTyT E n context leftProp (.sort .zero)
  rightPropTy : HasTyT E n context rightProp (.sort .zero)
  leftTy : HasTyT E n context left leftProp
  rightTy : HasTyT E n context right rightProp

private def sumList {α β : Type} (xs : List α) (ys : List β) : List (Sum α β) :=
  xs.map Sum.inl ++ ys.map Sum.inr
private theorem sumList_complete {α β : Type} (xs : List α) (ys : List β)
    (hx : ∀ x, x ∈ xs) (hy : ∀ y, y ∈ ys) : ∀ z, z ∈ sumList xs ys
  | .inl x => List.mem_append.mpr (.inl (List.mem_map_of_mem Sum.inl (hx x)))
  | .inr y => List.mem_append.mpr (.inr (List.mem_map_of_mem Sum.inr (hy y)))

variable {E : ResolvedEnv} {n : Nat}

/-- Exhaustive constructor recursion: no catch-all for future constructors. -/
def RawOcc : {Γ : LCtx} → {a b : Expr Nat} → PEqT E n Γ a b → Type
  | _, _, _, .bvar .. => PEmpty
  | _, _, _, .sort .. => PEmpty
  | _, _, _, .const .. => PEmpty
  | _, _, _, .app _ _ _ _ _ hf ha => Sum (RawOcc hf) (RawOcc ha)
  | _, _, _, .lam _ _ _ _ _ hA hb => Sum (RawOcc hA) (RawOcc hb)
  | _, _, _, .pi _ _ _ _ _ hA hB => Sum (RawOcc hA) (RawOcc hB)
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb => Sum (RawOcc hA) (Sum (RawOcc hv) (RawOcc hb))
  | _, _, _, .lit .. => PEmpty
  | _, _, _, .proof .. => PUnit

def rawOccurrences : {Γ : LCtx} → {a b : Expr Nat} → (h : PEqT E n Γ a b) → List (RawOcc h)
  | _, _, _, .bvar .. => []
  | _, _, _, .sort .. => []
  | _, _, _, .const .. => []
  | _, _, _, .app _ _ _ _ _ hf ha => sumList (rawOccurrences hf) (rawOccurrences ha)
  | _, _, _, .lam _ _ _ _ _ hA hb => sumList (rawOccurrences hA) (rawOccurrences hb)
  | _, _, _, .pi _ _ _ _ _ hA hB => sumList (rawOccurrences hA) (rawOccurrences hB)
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb => sumList (rawOccurrences hA) (sumList (rawOccurrences hv) (rawOccurrences hb))
  | _, _, _, .lit .. => []
  | _, _, _, .proof .. => [PUnit.unit]

/-- Every address has an entry; duplication at two addresses is retained. -/
theorem rawOccurrences_complete : {Γ : LCtx} → {a b : Expr Nat} → (h : PEqT E n Γ a b) →
    (o : RawOcc h) → o ∈ rawOccurrences h
  | _, _, _, .bvar .., o => nomatch o
  | _, _, _, .sort .., o => nomatch o
  | _, _, _, .const .., o => nomatch o
  | _, _, _, .app _ _ _ _ _ hf ha, o => sumList_complete _ _ (rawOccurrences_complete hf) (rawOccurrences_complete ha) o
  | _, _, _, .lam _ _ _ _ _ hA hb, o => sumList_complete _ _ (rawOccurrences_complete hA) (rawOccurrences_complete hb) o
  | _, _, _, .pi _ _ _ _ _ hA hB, o => sumList_complete _ _ (rawOccurrences_complete hA) (rawOccurrences_complete hB) o
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb, o => sumList_complete _ _ (rawOccurrences_complete hA)
      (sumList_complete _ _ (rawOccurrences_complete hv) (rawOccurrences_complete hb)) o
  | _, _, _, .lit .., o => nomatch o
  | _, _, _, .proof .., o => by cases o; exact List.mem_cons_self _ _

/-- Reads the exact original proof evidence and binder context at an address. -/
def rawSite : {Γ : LCtx} → {a b : Expr Nat} → (h : PEqT E n Γ a b) → RawOcc h → ProofSite E n
  | _, _, _, .bvar .., o => nomatch o
  | _, _, _, .sort .., o => nomatch o
  | _, _, _, .const .., o => nomatch o
  | _, _, _, .app _ _ _ _ _ hf ha, o => match o with
    | .inl x => rawSite hf x
    | .inr y => rawSite ha y
  | _, _, _, .lam _ _ _ _ _ hA hb, o => match o with
    | .inl x => rawSite hA x
    | .inr y => rawSite hb y
  | _, _, _, .pi _ _ _ _ _ hA hB, o => match o with
    | .inl x => rawSite hA x
    | .inr y => rawSite hB y
  | _, _, _, .letE _ _ _ _ _ _ _ hA hv hb, o => match o with
    | .inl x => rawSite hA x
    | .inr (.inl y) => rawSite hv y
    | .inr (.inr z) => rawSite hb z
  | _, _, _, .lit .., o => nomatch o
  | _, _, _, .proof Γ a b P Q hP hQ hp hq, _ => ⟨Γ, a, b, P, Q, hP, hQ, hp, hq⟩

/-- Exhaustive constructor recursion: no catch-all for future constructors. -/
def Occ : {Γ : LCtx} → {a b T : Expr Nat} → ParRedT (PEqLeafT E n) E n Γ a b T → Type
  | _, _, _, _, .refl .. => PEmpty
  | _, _, _, _, .sortEq .. => PEmpty
  | _, _, _, _, .consts .. => PEmpty
  | _, _, _, _, .bvarZeta _ _ _ _ _ _ _ hv _ _ => Occ hv
  | _, _, _, _, .delta .. => PEmpty
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf _ _ _ ha _ => Sum (Occ hf) (Occ ha)
  | _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ _ hb ha _ => Sum (Occ hb) (Occ ha)
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ hb _ => Occ hb
  | _, _, _, _, .pi .. => PEmpty
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ hb _ => Sum (Occ hv) (Occ hb)
  | _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ hv _ _ hb _ => Sum (Occ hv) (Occ hb)
  | _, _, _, _, .iotaSpine _ _ _ _ _ hs _ _ _ => Occ hs
  | _, _, _, _, .iotaStarK .. => PEmpty
  | _, _, _, _, .iotaStarKEta .. => PEmpty
  | _, _, _, _, .lit .. => PEmpty
  | _, _, _, _, .eta _ _ _ _ _ hf _ => Occ hf
  | _, _, _, _, .peq _ _ _ _ leaf => RawOcc leaf.1
  | _, _, _, _, .conv _ _ _ _ _ h _ => Occ h

def occurrences : {Γ : LCtx} → {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) → List (Occ h)
  | _, _, _, _, .refl .. => []
  | _, _, _, _, .sortEq .. => []
  | _, _, _, _, .consts .. => []
  | _, _, _, _, .bvarZeta _ _ _ _ _ _ _ hv _ _ => occurrences hv
  | _, _, _, _, .delta .. => []
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf _ _ _ ha _ => sumList (occurrences hf) (occurrences ha)
  | _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ _ hb ha _ => sumList (occurrences hb) (occurrences ha)
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ hb _ => occurrences hb
  | _, _, _, _, .pi .. => []
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ hb _ => sumList (occurrences hv) (occurrences hb)
  | _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ hv _ _ hb _ => sumList (occurrences hv) (occurrences hb)
  | _, _, _, _, .iotaSpine _ _ _ _ _ hs _ _ _ => occurrences hs
  | _, _, _, _, .iotaStarK .. => []
  | _, _, _, _, .iotaStarKEta .. => []
  | _, _, _, _, .lit .. => []
  | _, _, _, _, .eta _ _ _ _ _ hf _ => occurrences hf
  | _, _, _, _, .peq _ _ _ _ leaf => rawOccurrences leaf.1
  | _, _, _, _, .conv _ _ _ _ _ h _ => occurrences h

/-- Every address has an entry; duplication at two addresses is retained. -/
theorem occurrences_complete : {Γ : LCtx} → {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) →
    (o : Occ h) → o ∈ occurrences h
  | _, _, _, _, .refl .., o => nomatch o
  | _, _, _, _, .sortEq .., o => nomatch o
  | _, _, _, _, .consts .., o => nomatch o
  | _, _, _, _, .bvarZeta _ _ _ _ _ _ _ hv _ _, o => occurrences_complete hv o
  | _, _, _, _, .delta .., o => nomatch o
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf _ _ _ ha _, o => sumList_complete _ _ (occurrences_complete hf) (occurrences_complete ha) o
  | _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ _ hb ha _, o => sumList_complete _ _ (occurrences_complete hb) (occurrences_complete ha) o
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ hb _, o => occurrences_complete hb o
  | _, _, _, _, .pi .., o => nomatch o
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ hb _, o => sumList_complete _ _ (occurrences_complete hv) (occurrences_complete hb) o
  | _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ hv _ _ hb _, o => sumList_complete _ _ (occurrences_complete hv) (occurrences_complete hb) o
  | _, _, _, _, .iotaSpine _ _ _ _ _ hs _ _ _, o => occurrences_complete hs o
  | _, _, _, _, .iotaStarK .., o => nomatch o
  | _, _, _, _, .iotaStarKEta .., o => nomatch o
  | _, _, _, _, .lit .., o => nomatch o
  | _, _, _, _, .eta _ _ _ _ _ hf _, o => occurrences_complete hf o
  | _, _, _, _, .peq _ _ _ _ leaf, o => rawOccurrences_complete leaf.1 o
  | _, _, _, _, .conv _ _ _ _ _ h _, o => occurrences_complete h o

/-- Reads the exact original proof evidence and binder context at an address. -/
def site : {Γ : LCtx} → {a b T : Expr Nat} → (h : ParRedT (PEqLeafT E n) E n Γ a b T) → Occ h → ProofSite E n
  | _, _, _, _, .refl .., o => nomatch o
  | _, _, _, _, .sortEq .., o => nomatch o
  | _, _, _, _, .consts .., o => nomatch o
  | _, _, _, _, .bvarZeta _ _ _ _ _ _ _ hv _ _, o => site hv o
  | _, _, _, _, .delta .., o => nomatch o
  | _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ hf _ _ _ ha _, o => match o with
    | .inl x => site hf x
    | .inr y => site ha y
  | _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ _ hb ha _, o => match o with
    | .inl x => site hb x
    | .inr y => site ha y
  | _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ hb _, o => site hb o
  | _, _, _, _, .pi .., o => nomatch o
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ hb _, o => match o with
    | .inl x => site hv x
    | .inr y => site hb y
  | _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ hv _ _ hb _, o => match o with
    | .inl x => site hv x
    | .inr y => site hb y
  | _, _, _, _, .iotaSpine _ _ _ _ _ hs _ _ _, o => site hs o
  | _, _, _, _, .iotaStarK .., o => nomatch o
  | _, _, _, _, .iotaStarKEta .., o => nomatch o
  | _, _, _, _, .lit .., o => nomatch o
  | _, _, _, _, .eta _ _ _ _ _ hf _, o => site hf o
  | _, _, _, _, .peq _ _ _ _ leaf, o => rawSite leaf.1 o
  | _, _, _, _, .conv _ _ _ _ _ h _, o => site h o


/-- A raw proof root has two proof typings. Neither side is silently omitted. -/
inductive Side where | left | right

def ProofSite.term (s : ProofSite E n) : Side → Expr Nat
  | .left => s.left
  | .right => s.right

def ProofSite.proposition (s : ProofSite E n) : Side → Expr Nat
  | .left => s.leftProp
  | .right => s.rightProp

/-- A concrete request at an occurrence. Its position typing is DATA, not an
inference from the loose PEqT. Producers/consumers must use this exact request.
Producing these position typings from arbitrary structural paths remains open. -/
structure SiteRequest (s : ProofSite E n) (side : Side) where
  index : Expr Nat
  positionTyping : HasTyT E n s.context (s.term side) index

def SiteRequest.Answer {s : ProofSite E n} {side : Side}
    (r : SiteRequest s side) : Type :=
  TyConvT E n s.context r.index (s.proposition side)

/-- Total request assignment: every occurrence and BOTH sides have a slot.
There is no Option/empty fallback hiding an unpositioned structural occurrence. -/
abbrev Requests {Γ : LCtx} {a b T : Expr Nat}
    (h : ParRedT (PEqLeafT E n) E n Γ a b T) : Type :=
  (o : Occ h) → (side : Side) → SiteRequest (site h o) side

/-- The invariant is indexed by the EXACT request assignment. A store for an
easy/different index cannot be used as the answer to another actual request.
This declaration is an interface, not a universal producer for the invariant. -/
abbrev AnsweredOrigins {Γ : LCtx} {a b T : Expr Nat}
    (h : ParRedT (PEqLeafT E n) E n Γ a b T) (requests : Requests h) : Type :=
  (o : Occ h) → (side : Side) → (requests o side).Answer

section Producers
variable {Γ : LCtx} {a b c T U P : Expr Nat}

def rootRequests (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (ha : HasTyT E n Γ a T) (hb : HasTyT E n Γ b T) :
    Requests (.peq Γ a b T (peqLeafT_reconcile_propIndex hP hTP ha hb).1)
  | _, .left => ⟨T, ha⟩
  | _, .right => ⟨T, hb⟩

/-- Every occurrence on the actual emitted root, not an existentially selected
one. The two side requests share the original hTP, so no second U call occurs. -/
def rootAnswers (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (ha : HasTyT E n Γ a T) (hb : HasTyT E n Γ b T) :
    AnsweredOrigins (.peq Γ a b T (peqLeafT_reconcile_propIndex hP hTP ha hb).1)
      (rootRequests hP hTP ha hb)
  | _, .left => hTP
  | _, .right => hTP

/-- Reindexing keeps the original internal request indices, not the outer index. -/
def requests_conv {h : ParRedT (PEqLeafT E n) E n Γ a b T}
    (hc : TyConvT E n Γ T U) (r : Requests h) :
    Requests (.conv Γ a b T U h hc) := r

def answers_conv {h : ParRedT (PEqLeafT E n) E n Γ a b T}
    (hc : TyConvT E n Γ T U) (r : Requests h) (ans : AnsweredOrigins h r) :
    AnsweredOrigins (.conv Γ a b T U h hc) (requests_conv hc r) := ans

def requests_iotaSpine {h : ParRedT (PEqLeafT E n) E n Γ a b T}
    (hi : DerivedIotaU E b c) (hb : HasTyT E n Γ b T) (hc : HasTyT E n Γ c T)
    (r : Requests h) : Requests (.iotaSpine Γ a b c T h hi hb hc) := r

def answers_iotaSpine {h : ParRedT (PEqLeafT E n) E n Γ a b T}
    (hi : DerivedIotaU E b c) (hb : HasTyT E n Γ b T) (hc : HasTyT E n Γ c T)
    (r : Requests h) (ans : AnsweredOrigins h r) :
    AnsweredOrigins (.iotaSpine Γ a b c T h hi hb hc)
      (requests_iotaSpine hi hb hc r) := ans

def peakRequests (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (h1 : ParRedT (PEqLeafT E n) E n Γ a b T)
    (h2 : ParRedT (PEqLeafT E n) E n Γ a c T) :
    Requests (parRedT_propIndex_diamond_data hP hTP h1 h2).1 :=
  rootRequests hP hTP (parRedT_sr_peqT_val h1) (parRedT_sr_peqT_val h2)

def peakAnswers (hP : HasTyT E n Γ P (.sort .zero)) (hTP : TyConvT E n Γ T P)
    (h1 : ParRedT (PEqLeafT E n) E n Γ a b T)
    (h2 : ParRedT (PEqLeafT E n) E n Γ a c T) :
    AnsweredOrigins (parRedT_propIndex_diamond_data hP hTP h1 h2).1
      (peakRequests hP hTP h1 h2) :=
  rootAnswers hP hTP (parRedT_sr_peqT_val h1) (parRedT_sr_peqT_val h2)
end Producers
end Rcic.Declarative.F8Occurrences
