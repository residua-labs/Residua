import rcic.RcicWireEmit
import rcic.RcicCertEmit
import rcic.ScmValueAtComplete
import Residua.SHA256

/-!
# RcicWireConsumer — the Lean definition of the ScmWire consumer (fusion F0 / F4)

`Rcic.Wire.Consumer.handle : Request → Response` is the fused entry: a decoded ScmWire request is
checked by the cert-layer machine (`certStep`, through the first-order entries of `RcicCertEmit`) and the
verdict is encoded by `ScmWire.encVal`. **No kernel logic is added.** The request and response are `Val`
trees on the existing codec; bytes go through `wireDecCanon` (full consumption + canonical re-encode) and
`encVal`.

* `Request` = a body (universe count, environment table, local context, one task, budget) and `q`, the
  content digest of the body's canonical bytes. The task is one of `whnfT`, `convT`, `tyConvT`, exactly
  the three cert entries of `RcicCertEmit` (`certWhnfS`, `certConvS`, `certTyConvS`).
* `Response` = a verdict (`Summ`: accepted payload data, checker refusal, suspension) tagged with the
  request's `q`, or a named input residue.
* Named residues: the codec's own (`[rcic_scm_wire_*]`) pass through; the consumer adds
  `[rcic_wire_consumer_shape]`, `_schema`, `_term`, `_budget`, `_altered` (q mismatch) and `_replay`.

Properties proved here: `decodeRequest_encode` (decode ∘ encode = id on valid requests), `handleBytes_encode`
(the bytes of a valid request are handled as the request), `handle_q` (the response carries the request's
`q`), `handleBytes_malformed` (a decode failure is its named residue), `handleSeen_replay`,
`handle_altered`, and soundness of an accepted verdict (`handle_converted_sound` etc.: an accepted response
carries a `ConvT` / `TyConvT` derivation in the request's environment).
This is the v3 widening named in `WIRE_CONTRACT_V2.md`; v2's Sort-level request is not this request.
closure_claim = 0.
-/

namespace Rcic.Wire.Consumer

open Rcic.Declarative Rcic.Machine Rcic.Scm Rcic.Scm.Wire

/-! ## §1 levels and expressions as `Val` trees -/

/-- every natural carried by a request is below this bound (inside i64 with a wide margin). -/
def natB : Nat := 1000000000

def lvlVal : Level → Val
  | .zero => .j 0 (.r [])
  | .succ a => .j 1 (.r [lvlVal a])
  | .max a b => .j 2 (.r [lvlVal a, lvlVal b])
  | .imax a b => .j 3 (.r [lvlVal a, lvlVal b])
  | .param i => .j 4 (.i i)

def lvlOf : Nat → Val → Option Level
  | 0, _ => none
  | _ + 1, .j 0 (.r []) => some .zero
  | f + 1, .j 1 (.r [a]) => (lvlOf f a).map Level.succ
  | f + 1, .j 2 (.r [a, b]) =>
      match lvlOf f a, lvlOf f b with
      | some x, some y => some (.max x y)
      | _, _ => none
  | f + 1, .j 3 (.r [a, b]) =>
      match lvlOf f a, lvlOf f b with
      | some x, some y => some (.imax x y)
      | _, _ => none
  | _ + 1, .j 4 (.i i) => if 0 ≤ i then some (.param i.toNat) else none
  | _, _ => none

def lvlD : Level → Nat
  | .zero => 1
  | .succ a => lvlD a + 1
  | .max a b => max (lvlD a) (lvlD b) + 1
  | .imax a b => max (lvlD a) (lvlD b) + 1
  | .param _ => 1

def LvlOK : Level → Prop
  | .zero => True
  | .succ a => LvlOK a
  | .max a b => LvlOK a ∧ LvlOK b
  | .imax a b => LvlOK a ∧ LvlOK b
  | .param i => i ≤ natB

theorem lvlOf_lvlVal : ∀ (l : Level) (f : Nat), lvlD l ≤ f → lvlOf f (lvlVal l) = some l := by
  intro l
  induction l with
  | zero => intro f hf; cases f with
    | zero => simp [lvlD] at hf
    | succ f => rfl
  | succ a ih => intro f hf; cases f with
    | zero => simp [lvlD] at hf
    | succ f =>
        simp only [lvlD] at hf
        simp only [lvlVal, lvlOf, ih f (by omega)]; rfl
  | max a b iha ihb => intro f hf; cases f with
    | zero => simp [lvlD] at hf
    | succ f =>
        simp only [lvlD] at hf
        simp only [lvlVal, lvlOf, iha f (by omega), ihb f (by omega)]
  | imax a b iha ihb => intro f hf; cases f with
    | zero => simp [lvlD] at hf
    | succ f =>
        simp only [lvlD] at hf
        simp only [lvlVal, lvlOf, iha f (by omega), ihb f (by omega)]
  | param i => intro f hf; cases f with
    | zero => simp [lvlD] at hf
    | succ f => simp [lvlVal, lvlOf]; omega

theorem inI64_nat {n : Nat} (h : n ≤ natB) : inI64 (n : Int) := by
  unfold natB at h
  unfold inI64 i64Min i64Max
  refine ⟨?_, ?_⟩ <;> omega

theorem inI64_small {n : Int} (h0 : 0 ≤ n) (h : n ≤ 100000) : inI64 n := by
  unfold inI64 i64Min i64Max
  refine ⟨?_, ?_⟩ <;> omega

theorem dqV_lvlVal : ∀ l : Level, LvlOK l → dqV (lvlVal l) := by
  intro l
  induction l with
  | zero => intro _; simp [lvlVal, dqV, dqsV, inI64_small]
  | succ a ih => intro h; simp [lvlVal, dqV, dqsV, inI64_small, ih h]
  | max a b iha ihb => intro h; simp [lvlVal, dqV, dqsV, inI64_small, iha h.1, ihb h.2]
  | imax a b iha ihb => intro h; simp [lvlVal, dqV, dqsV, inI64_small, iha h.1, ihb h.2]
  | param i =>
      intro h
      simp only [lvlVal, dqV]
      exact ⟨by omega, inI64_small (by omega) (by omega), inI64_nat h⟩

/-! ### list helpers -/

theorem mapM_map {α β : Type} (f : α → β) (g : β → Option α) :
    ∀ (xs : List α), (∀ x ∈ xs, g (f x) = some x) → (xs.map f).mapM g = some xs
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.map_cons, List.mapM_cons, h x (List.mem_cons_self _ _)]
      rw [mapM_map f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      rfl

theorem dqsV_map {α : Type} (f : α → Val) :
    ∀ (xs : List α), (∀ x ∈ xs, dqV (f x)) → dqsV (xs.map f)
  | [], _ => trivial
  | x :: xs, h => ⟨h x (List.mem_cons_self _ _),
      dqsV_map f xs (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

/-! ### expressions -/

def exprVal : Expr Nat → Val
  | .bvar i => .j 0 (.i i)
  | .sort l => .j 1 (lvlVal l)
  | .const r ls => .j 2 (.r [.i r, .l (ls.map lvlVal)])
  | .app f x => .j 3 (.r [exprVal f, exprVal x])
  | .lam a b => .j 4 (.r [exprVal a, exprVal b])
  | .pi a b => .j 5 (.r [exprVal a, exprVal b])
  | .letE a v b => .j 6 (.r [exprVal a, exprVal v, exprVal b])
  | .lit t => .j 7 (.i t)

def exprOf : Nat → Val → Option (Expr Nat)
  | 0, _ => none
  | _ + 1, .j 0 (.i i) => if 0 ≤ i then some (.bvar i.toNat) else none
  | f + 1, .j 1 v => (lvlOf f v).map Expr.sort
  | f + 1, .j 2 (.r [.i r, .l ls]) =>
      if 0 ≤ r then (ls.mapM (lvlOf f)).map (fun L => Expr.const r.toNat L) else none
  | f + 1, .j 3 (.r [a, b]) =>
      match exprOf f a, exprOf f b with
      | some x, some y => some (.app x y)
      | _, _ => none
  | f + 1, .j 4 (.r [a, b]) =>
      match exprOf f a, exprOf f b with
      | some x, some y => some (.lam x y)
      | _, _ => none
  | f + 1, .j 5 (.r [a, b]) =>
      match exprOf f a, exprOf f b with
      | some x, some y => some (.pi x y)
      | _, _ => none
  | f + 1, .j 6 (.r [a, v, b]) =>
      match exprOf f a, exprOf f v, exprOf f b with
      | some x, some y, some z => some (.letE x y z)
      | _, _, _ => none
  | _ + 1, .j 7 (.i t) => if 0 ≤ t then some (.lit t.toNat) else none
  | _, _ => none

def lvlsD (ls : List Level) : Nat := ls.foldr (fun l m => max (lvlD l) m) 0

theorem le_lvlsD {l : Level} {ls : List Level} (h : l ∈ ls) : lvlD l ≤ lvlsD ls := by
  induction ls with
  | nil => cases h
  | cons x xs ih =>
      unfold lvlsD at *
      simp only [List.foldr_cons]
      cases List.mem_cons.mp h with
      | inl e => subst e; exact Nat.le_max_left _ _
      | inr h' => exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

def exprD : Expr Nat → Nat
  | .bvar _ => 1
  | .sort l => lvlD l + 1
  | .const _ ls => lvlsD ls + 1
  | .app f x => max (exprD f) (exprD x) + 1
  | .lam a b => max (exprD a) (exprD b) + 1
  | .pi a b => max (exprD a) (exprD b) + 1
  | .letE a v b => max (max (exprD a) (exprD v)) (exprD b) + 1
  | .lit _ => 1

def ExprOK : Expr Nat → Prop
  | .bvar i => i ≤ natB
  | .sort l => LvlOK l
  | .const r ls => r ≤ natB ∧ ls.length ≤ 1000 ∧ ∀ l ∈ ls, LvlOK l
  | .app f x => ExprOK f ∧ ExprOK x
  | .lam a b => ExprOK a ∧ ExprOK b
  | .pi a b => ExprOK a ∧ ExprOK b
  | .letE a v b => ExprOK a ∧ ExprOK v ∧ ExprOK b
  | .lit t => t ≤ natB

theorem exprOf_exprVal : ∀ (e : Expr Nat) (f : Nat), exprD e ≤ f → exprOf f (exprVal e) = some e := by
  intro e
  induction e with
  | bvar i => intro f hf; cases f with
    | zero => simp [exprD] at hf
    | succ f => simp [exprVal, exprOf]; omega
  | sort l => intro f hf; cases f with
    | zero => simp [exprD] at hf
    | succ f =>
        simp only [exprD] at hf
        simp [exprVal, exprOf, lvlOf_lvlVal l f (by omega)]
  | const r ls => intro f hf; cases f with
    | zero => simp [exprD] at hf
    | succ f =>
        simp only [exprD] at hf
        have hm : (ls.map lvlVal).mapM (lvlOf f) = some ls :=
          mapM_map lvlVal (lvlOf f) ls (fun l hl => lvlOf_lvlVal l f (by
            have := le_lvlsD hl; omega))
        simp [exprVal, exprOf, hm]; omega
  | app a b iha ihb => intro f hf; cases f with
    | zero => simp [exprD] at hf
    | succ f =>
        simp only [exprD] at hf
        simp [exprVal, exprOf, iha f (by omega), ihb f (by omega)]
  | lam a b iha ihb => intro f hf; cases f with
    | zero => simp [exprD] at hf
    | succ f =>
        simp only [exprD] at hf
        simp [exprVal, exprOf, iha f (by omega), ihb f (by omega)]
  | pi a b iha ihb => intro f hf; cases f with
    | zero => simp [exprD] at hf
    | succ f =>
        simp only [exprD] at hf
        simp [exprVal, exprOf, iha f (by omega), ihb f (by omega)]
  | letE a v b iha ihv ihb => intro f hf; cases f with
    | zero => simp [exprD] at hf
    | succ f =>
        simp only [exprD] at hf
        simp [exprVal, exprOf, iha f (by omega), ihv f (by omega), ihb f (by omega)]
  | lit t => intro f hf; cases f with
    | zero => simp [exprD] at hf
    | succ f => simp [exprVal, exprOf]; omega

theorem dqV_exprVal : ∀ e : Expr Nat, ExprOK e → dqV (exprVal e) := by
  intro e
  induction e with
  | bvar i => intro h; simp only [exprVal, dqV]; exact ⟨by omega, inI64_small (by omega) (by omega), inI64_nat h⟩
  | sort l => intro h; simp [exprVal, dqV, inI64_small, dqV_lvlVal l h]
  | const r ls =>
      intro h
      obtain ⟨hr, hl, hall⟩ := h
      have hs : dqsV (ls.map lvlVal) := dqsV_map lvlVal ls (fun l hl' => dqV_lvlVal l (hall l hl'))
      have hL : dqV (Val.l (ls.map lvlVal)) := ⟨by simpa using (by omega : ls.length ≤ 1024), hs⟩
      have hI : dqV (Val.i r) := inI64_nat hr
      exact ⟨by omega, inI64_small (by omega) (by omega), by simp, hI, hL, trivial⟩
  | app a b iha ihb => intro h; simp [exprVal, dqV, dqsV, inI64_small, iha h.1, ihb h.2]
  | lam a b iha ihb => intro h; simp [exprVal, dqV, dqsV, inI64_small, iha h.1, ihb h.2]
  | pi a b iha ihb => intro h; simp [exprVal, dqV, dqsV, inI64_small, iha h.1, ihb h.2]
  | letE a v b iha ihv ihb =>
      intro h; simp [exprVal, dqV, dqsV, inI64_small, iha h.1, ihv h.2.1, ihb h.2.2]
  | lit t => intro h; simp only [exprVal, dqV]; exact ⟨by omega, inI64_small (by omega) (by omega), inI64_nat h⟩

/-! ## §2 members, environments, contexts, tasks -/

/-- decoder depth for every term: requests deeper than this are refused (`_term`). -/
def exprFuel : Nat := 4096

def ExprGood (e : Expr Nat) : Prop := ExprOK e ∧ exprD e ≤ exprFuel

theorem exprOf_good {e : Expr Nat} (h : ExprGood e) : exprOf exprFuel (exprVal e) = some e :=
  exprOf_exprVal e exprFuel h.2

theorem dqV_good {e : Expr Nat} (h : ExprGood e) : dqV (exprVal e) := dqV_exprVal e h.1

def classCode : MemberClass → Int
  | .axiomM => 0 | .definitionM => 1 | .theoremM => 2 | .opaqueM => 3
  | .inductiveM => 4 | .constructorM => 5 | .recursorM => 6

def classOf : Int → Option MemberClass
  | 0 => some .axiomM | 1 => some .definitionM | 2 => some .theoremM | 3 => some .opaqueM
  | 4 => some .inductiveM | 5 => some .constructorM | 6 => some .recursorM
  | _ => none

theorem classOf_classCode (c : MemberClass) : classOf (classCode c) = some c := by
  cases c <;> rfl

def optVal : Option (Expr Nat) → Val
  | none => .j 0 (.r [])
  | some e => .j 1 (exprVal e)

/-- outer `none` = malformed; inner = the option. -/
def optOf : Val → Option (Option (Expr Nat))
  | .j 0 (.r []) => some none
  | .j 1 v => (exprOf exprFuel v).map some
  | _ => none

def memberVal (m : CheckedMember) : Val :=
  .r [.i (classCode m.mclass), .i m.arity, exprVal m.mtype, optVal m.body]

def memberOf : Val → Option CheckedMember
  | .r [.i c, .i a, t, o] =>
      if 0 ≤ a then
        match classOf c, exprOf exprFuel t, optOf o with
        | some k, some ty, some b => some ⟨k, a.toNat, ty, b⟩
        | _, _, _ => none
      else none
  | _ => none

def MemberGood (m : CheckedMember) : Prop :=
  m.arity ≤ natB ∧ ExprGood m.mtype ∧ ∀ b, m.body = some b → ExprGood b

theorem optOf_optVal (o : Option (Expr Nat)) (h : ∀ b, o = some b → ExprGood b) :
    optOf (optVal o) = some o := by
  cases o with
  | none => rfl
  | some e => simp [optVal, optOf, exprOf_good (h e rfl)]

theorem memberOf_memberVal (m : CheckedMember) (h : MemberGood m) :
    memberOf (memberVal m) = some m := by
  obtain ⟨m1, m2, m3, m4⟩ := m
  obtain ⟨ha, hty, hb⟩ := h
  simp only [memberVal, memberOf, classOf_classCode, exprOf_good hty, optOf_optVal _ hb]
  simp; omega

theorem dqV_optVal (o : Option (Expr Nat)) (h : ∀ b, o = some b → ExprGood b) : dqV (optVal o) := by
  cases o with
  | none => simp [optVal, dqV, dqsV, inI64_small]
  | some e => simp only [optVal, dqV]; exact ⟨by omega, inI64_small (by omega) (by omega), dqV_good (h e rfl)⟩

theorem dqV_memberVal (m : CheckedMember) (h : MemberGood m) : dqV (memberVal m) := by
  obtain ⟨ha, hty, hb⟩ := h
  have hc : inI64 (classCode m.mclass) := by
    cases m.mclass <;> exact inI64_small (by decide) (by decide)
  simp only [memberVal, dqV, dqsV]
  exact ⟨by simp, hc, inI64_nat ha, dqV_good hty, dqV_optVal _ hb, trivial⟩

def entryVal (p : Nat × CheckedMember) : Val := .p (.i p.1) (memberVal p.2)

def entryOf : Val → Option (Nat × CheckedMember)
  | .p (.i r) v => if 0 ≤ r then (memberOf v).map (fun m => (r.toNat, m)) else none
  | _ => none

def EntryGood (p : Nat × CheckedMember) : Prop := p.1 ≤ natB ∧ MemberGood p.2

theorem entryOf_entryVal (p : Nat × CheckedMember) (h : EntryGood p) :
    entryOf (entryVal p) = some p := by
  obtain ⟨r, m⟩ := p
  simp [entryVal, entryOf, memberOf_memberVal m h.2]; omega

theorem dqV_entryVal (p : Nat × CheckedMember) (h : EntryGood p) : dqV (entryVal p) := by
  simp only [entryVal, dqV]
  exact ⟨inI64_nat h.1, dqV_memberVal _ h.2⟩

def declVal : LocalDecl → Val
  | .assumption A => .j 0 (exprVal A)
  | .letBinding A v => .j 1 (.p (exprVal A) (exprVal v))

def declOf : Val → Option LocalDecl
  | .j 0 v => (exprOf exprFuel v).map LocalDecl.assumption
  | .j 1 (.p a v) =>
      match exprOf exprFuel a, exprOf exprFuel v with
      | some x, some y => some (.letBinding x y)
      | _, _ => none
  | _ => none

def DeclGood : LocalDecl → Prop
  | .assumption A => ExprGood A
  | .letBinding A v => ExprGood A ∧ ExprGood v

theorem declOf_declVal (d : LocalDecl) (h : DeclGood d) : declOf (declVal d) = some d := by
  cases d with
  | assumption A => simp [declVal, declOf, exprOf_good h]
  | letBinding A v => simp [declVal, declOf, exprOf_good h.1, exprOf_good h.2]

theorem dqV_declVal (d : LocalDecl) (h : DeclGood d) : dqV (declVal d) := by
  cases d with
  | assumption A => simp only [declVal, dqV]; exact ⟨by omega, inI64_small (by omega) (by omega), dqV_good h⟩
  | letBinding A v =>
      simp only [declVal, dqV]
      exact ⟨by omega, inI64_small (by omega) (by omega), dqV_good h.1, dqV_good h.2⟩

def taskVal : CertTask → Val
  | .whnfT T e => .j 0 (.r [exprVal T, exprVal e])
  | .convT T l r => .j 1 (.r [exprVal T, exprVal l, exprVal r])
  | .tyConvT A B => .j 2 (.r [exprVal A, exprVal B])

def taskOf : Val → Option CertTask
  | .j 0 (.r [t, e]) =>
      match exprOf exprFuel t, exprOf exprFuel e with
      | some x, some y => some (.whnfT x y)
      | _, _ => none
  | .j 1 (.r [t, l, r]) =>
      match exprOf exprFuel t, exprOf exprFuel l, exprOf exprFuel r with
      | some x, some y, some z => some (.convT x y z)
      | _, _, _ => none
  | .j 2 (.r [a, b]) =>
      match exprOf exprFuel a, exprOf exprFuel b with
      | some x, some y => some (.tyConvT x y)
      | _, _ => none
  | _ => none

def TaskGood : CertTask → Prop
  | .whnfT T e => ExprGood T ∧ ExprGood e
  | .convT T l r => ExprGood T ∧ ExprGood l ∧ ExprGood r
  | .tyConvT A B => ExprGood A ∧ ExprGood B

theorem taskOf_taskVal (k : CertTask) (h : TaskGood k) : taskOf (taskVal k) = some k := by
  cases k with
  | whnfT T e => simp [taskVal, taskOf, exprOf_good h.1, exprOf_good h.2]
  | convT T l r => simp [taskVal, taskOf, exprOf_good h.1, exprOf_good h.2.1, exprOf_good h.2.2]
  | tyConvT A B => simp [taskVal, taskOf, exprOf_good h.1, exprOf_good h.2]

theorem dqV_taskVal (k : CertTask) (h : TaskGood k) : dqV (taskVal k) := by
  cases k with
  | whnfT T e => simp [taskVal, dqV, dqsV, inI64_small, dqV_good h.1, dqV_good h.2]
  | convT T l r =>
      simp [taskVal, dqV, dqsV, inI64_small, dqV_good h.1, dqV_good h.2.1, dqV_good h.2.2]
  | tyConvT A B => simp [taskVal, dqV, dqsV, inI64_small, dqV_good h.1, dqV_good h.2]

/-! ## §3 the canonical decoder inverts the encoder -/

/-- the decoder fuel is the byte length (the carrier's own-fuel shape). -/
def wireFuel (b : String) : Int := (b.length : Int)

/-- `wireDecCanon` reads `encVal v` back to `v`, from the landed `decVal_enc` and its gas/fuel
    bounds (`ScmValueAtComplete`). -/
theorem wireDecCanon_encVal (v : Val) (hdq : dqV v) :
    wireDecCanon (encVal v) (wireFuel (encVal v)) = .ok v := by
  have hg := Rcic.Scm.ValueAtComplete.valGas_le_gasFor v
  have hf := Rcic.Scm.ValueAtComplete.valFuel_le_len v
  have hsz : ((encVal v).toList.toArray).size = (encVal v).length := by
    simp only [Array.size_toArray]; rfl
  have hd := decVal_enc v ((encVal v).toList.toArray)
    (gasFor (wireFuel (encVal v)) ((encVal v).toList.toArray).size) (wireFuel (encVal v)) 0 []
    (by simp) (by unfold wireFuel; rw [hsz]; omega) hf hdq
  unfold wireDecCanon wireDecVal
  simp only [hd]
  simp only [asVal, hsz, Nat.zero_add]
  have e1 : (encVal v).toList.length = (encVal v).length := rfl
  simp [e1]

/-! ## §4 requests and responses -/

def schemaName : String := "residua.rcic-cert-request.v3"

structure Body where
  univs : Nat
  tbl : List (Nat × CheckedMember)
  ctx : LCtx
  task : CertTask
  budget : Nat

structure Request where
  body : Body
  q : String

def bodyVal (b : Body) : Val :=
  .r [.s schemaName, .i b.univs, .l (b.tbl.map entryVal), .l (b.ctx.map declVal),
      taskVal b.task, .i b.budget]

/-- the request's content digest: SHA-256 of the canonical bytes of its body. -/
def qOf (b : Body) : String := Residua.SHA256.sha256Hex (encVal (bodyVal b))

def requestVal (r : Request) : Val := .r [.s r.q, bodyVal r.body]

def encodeRequest (r : Request) : String := encVal (requestVal r)

/-- the sealed request of a body: `q` computed. -/
def Request.ofBody (b : Body) : Request := ⟨b, qOf b⟩

def maxBudget : Int := 4096

def valRequest : Val → Except String Request
  | .r [.s q, .r [.s sch, .i u, .l tbl, .l ctx, tk, .i bud]] =>
      if sch ≠ schemaName then .error "[rcic_wire_consumer_schema]"
      else if u < 0 ∨ maxBudget < u ∨ bud < 0 ∨ maxBudget < bud then
        .error "[rcic_wire_consumer_budget]"
      else
        match tbl.mapM entryOf, ctx.mapM declOf, taskOf tk with
        | some t, some c, some k => .ok ⟨⟨u.toNat, t, c, k, bud.toNat⟩, q⟩
        | _, _, _ => .error "[rcic_wire_consumer_term]"
  | _ => .error "[rcic_wire_consumer_shape]"

def decodeRequest (bytes : String) : Except String Request :=
  match wireDecCanon bytes (wireFuel bytes) with
  | .error c => .error c
  | .ok v => valRequest v

def BodyGood (b : Body) : Prop :=
  b.univs ≤ 4096 ∧ b.budget ≤ 4096 ∧ b.tbl.length ≤ 1000 ∧ b.ctx.length ≤ 1000 ∧
  (∀ p ∈ b.tbl, EntryGood p) ∧ (∀ d ∈ b.ctx, DeclGood d) ∧ TaskGood b.task

def RequestGood (r : Request) : Prop := BodyGood r.body ∧ r.q.length ≤ 1024

theorem dqV_bodyVal (b : Body) (h : BodyGood b) : dqV (bodyVal b) := by
  obtain ⟨hu, hb, ht, hc, he, hd, hk⟩ := h
  have h1 : dqV (Val.l (b.tbl.map entryVal)) :=
    ⟨by simpa using (by omega : b.tbl.length ≤ 1024), dqsV_map _ _ (fun p hp => dqV_entryVal p (he p hp))⟩
  have h2 : dqV (Val.l (b.ctx.map declVal)) :=
    ⟨by simpa using (by omega : b.ctx.length ≤ 1024), dqsV_map _ _ (fun d hd' => dqV_declVal d (hd d hd'))⟩
  have h3 : dqV (Val.s schemaName) := by
    show schemaName.length ≤ 1024
    decide
  simp only [bodyVal, dqV, dqsV]
  exact ⟨by simp, h3, inI64_small (by omega) (by omega), h1, h2, dqV_taskVal _ hk,
    inI64_small (by omega) (by omega), trivial⟩

theorem dqV_requestVal (r : Request) (h : RequestGood r) : dqV (requestVal r) := by
  simp only [requestVal, dqV, dqsV]
  exact ⟨by simp, h.2, dqV_bodyVal _ h.1, trivial⟩

theorem valRequest_requestVal (r : Request) (h : RequestGood r) :
    valRequest (requestVal r) = .ok r := by
  obtain ⟨⟨u, t, c, k, bud⟩, q⟩ := r
  obtain ⟨⟨hu, hb, ht, hc, he, hd, hk⟩, hq⟩ := h
  have e1 : (t.map entryVal).mapM entryOf = some t :=
    mapM_map entryVal entryOf t (fun p hp => entryOf_entryVal p (he p hp))
  have e2 : (c.map declVal).mapM declOf = some c :=
    mapM_map declVal declOf c (fun d hd' => declOf_declVal d (hd d hd'))
  have e3 := taskOf_taskVal k hk
  simp only [requestVal, bodyVal, valRequest, schemaName, e1, e2, e3]
  have hu' : ¬ ((u : Int) < 0 ∨ maxBudget < (u : Int) ∨ (bud : Int) < 0 ∨ maxBudget < (bud : Int)) := by
    unfold maxBudget; simp only [Body.univs, Body.budget] at *; omega
  simp [hu']

/-- decode ∘ encode = id on valid requests. -/
theorem decodeRequest_encode (r : Request) (h : RequestGood r) :
    decodeRequest (encodeRequest r) = .ok r := by
  unfold decodeRequest encodeRequest
  rw [wireDecCanon_encVal _ (dqV_requestVal r h)]
  exact valRequest_requestVal r h

/-! ## §5 the response and the consumer -/

inductive Response : Type
  | verdict (q : String) (s : Summ)
  | malformed (residue : String)
  deriving DecidableEq

def summVal : Summ → Val
  | .whnfed e w T => .j 0 (.r [exprVal e, exprVal w, exprVal T])
  | .converted l r T => .j 1 (.r [exprVal l, exprVal r, exprVal T])
  | .tyConverted A B => .j 2 (.r [exprVal A, exprVal B])
  | .refused c => .j 3 (.s c)
  | .suspended => .j 4 (.r [])

def respVal : Response → Val
  | .verdict q s => .j 0 (.r [.s q, summVal s])
  | .malformed c => .j 1 (.s c)

def encodeResponse (r : Response) : String := encVal (respVal r)

/-- the verdict data of the requested task: `certStep` through the three cert entries. -/
def summOf (b : Body) : Summ :=
  match b.task with
  | .whnfT T e => certWhnfS b.tbl b.univs b.ctx T e b.budget
  | .convT T l r => certConvS b.tbl b.univs b.ctx T l r b.budget
  | .tyConvT A B => certTyConvS b.tbl b.univs b.ctx A B b.budget

def SummAccepted : Summ → Prop
  | .whnfed _ _ _ => True
  | .converted _ _ _ => True
  | .tyConverted _ _ => True
  | .refused _ => False
  | .suspended => False

def residueAltered : String := "[rcic_wire_consumer_altered]"
def residueReplay : String := "[rcic_wire_consumer_replay]"

/-- **The consumer.** A request whose `q` is not the digest of its body is altered. Otherwise the
    response is the cert machine's verdict on the request, tagged with the request's `q`. -/
def handle (req : Request) : Response :=
  if req.q ≠ qOf req.body then .malformed residueAltered
  else .verdict req.q (summOf req.body)

/-- the consumer on bytes, with the set of `q`s already served (replay protection). -/
def handleSeen (seen : List String) (bytes : String) : Response :=
  match decodeRequest bytes with
  | .error c => .malformed c
  | .ok req => if req.q ∈ seen then .malformed residueReplay else handle req

def handleBytes (bytes : String) : Response := handleSeen [] bytes

def serve (seen : List String) (bytes : String) : String := encodeResponse (handleSeen seen bytes)

/-! ## §6 properties -/

theorem ofBody_q (b : Body) : (Request.ofBody b).q = qOf b := rfl
theorem ofBody_body (b : Body) : (Request.ofBody b).body = b := rfl

theorem ofBody_good (b : Body) (hb : BodyGood b) (hq : (qOf b).length ≤ 1024) :
    RequestGood (Request.ofBody b) :=
  And.intro (by rw [ofBody_body]; exact hb) (by rw [ofBody_q]; exact hq)


theorem handle_ofBody (b : Body) :
    handle (Request.ofBody b) = .verdict (qOf b) (summOf b) := by
  simp [handle, Request.ofBody]

/-- the response carries the request's `q`. -/
theorem handle_q (req : Request) (q : String) (s : Summ)
    (h : handle req = .verdict q s) : q = req.q := by
  unfold handle at h
  by_cases hq : req.q ≠ qOf req.body
  · simp [hq] at h
  · simp only [hq, if_false] at h
    exact (Response.verdict.inj h).1.symm

theorem handle_altered (req : Request) (h : req.q ≠ qOf req.body) :
    handle req = .malformed residueAltered := by
  simp [handle, h]

/-- a decode failure is its named residue. -/
theorem handleSeen_malformed (seen : List String) (bytes c : String)
    (h : decodeRequest bytes = .error c) : handleSeen seen bytes = .malformed c := by
  simp [handleSeen, h]

theorem handleSeen_replay (seen : List String) (bytes : String) (req : Request)
    (hd : decodeRequest bytes = .ok req) (hr : req.q ∈ seen) :
    handleSeen seen bytes = .malformed residueReplay := by
  simp [handleSeen, hd, hr]

/-- the bytes of a valid request are handled as the request. -/
theorem handleSeen_encode (seen : List String) (r : Request) (h : RequestGood r)
    (hn : r.q ∉ seen) : handleSeen seen (encodeRequest r) = handle r := by
  simp [handleSeen, decodeRequest_encode r h, hn]

theorem handleBytes_encode (r : Request) (h : RequestGood r) :
    handleBytes (encodeRequest r) = handle r :=
  handleSeen_encode [] r h (List.not_mem_nil _)

/-- replay: serving the same valid bytes twice is refused the second time. -/
theorem handleSeen_encode_replay (r : Request) (h : RequestGood r) :
    handleSeen [r.q] (encodeRequest r) = .malformed residueReplay :=
  handleSeen_replay _ _ r (decodeRequest_encode r h) (List.mem_singleton_self _)

/-- **accepted round trip.** A sealed request whose check is accepted is answered by an accepted
    verdict carrying the same `q` and the machine's data. -/
theorem handleBytes_accepted (b : Body) (hb : BodyGood b) (hq : (qOf b).length ≤ 1024)
    (hs : SummAccepted (summOf b)) :
    handleBytes (encodeRequest (Request.ofBody b)) = .verdict (qOf b) (summOf b) := by
  exact (handleBytes_encode _ (ofBody_good b hb hq)).trans (handle_ofBody b)

/-- any sealed valid request round-trips to its verdict (accepted or not). -/
theorem handleBytes_sealed (b : Body) (hb : BodyGood b) (hq : (qOf b).length ≤ 1024) :
    handleBytes (encodeRequest (Request.ofBody b)) = .verdict (qOf b) (summOf b) := by
  exact (handleBytes_encode _ (ofBody_good b hb hq)).trans (handle_ofBody b)

/-! ### an accepted response carries a derivation in the request's environment -/

theorem handle_converted_sound (req : Request) (T l r : Expr Nat)
    (ht : req.body.task = .convT T l r) (h : handle req = .verdict req.q (.converted l r T)) :
    Nonempty (ConvT (envOfTable req.body.tbl) req.body.univs req.body.ctx l r T) := by
  unfold handle at h
  by_cases hq : req.q ≠ qOf req.body
  · simp [hq] at h
  · simp only [hq, if_false] at h
    have h2 := (Response.verdict.inj h).2
    unfold summOf at h2
    rw [ht] at h2
    exact certConvS_sound _ _ _ _ _ _ _ h2

theorem handle_whnfed_sound (req : Request) (T e w : Expr Nat)
    (ht : req.body.task = .whnfT T e) (h : handle req = .verdict req.q (.whnfed e w T)) :
    Nonempty (ConvT (envOfTable req.body.tbl) req.body.univs req.body.ctx e w T) := by
  unfold handle at h
  by_cases hq : req.q ≠ qOf req.body
  · simp [hq] at h
  · simp only [hq, if_false] at h
    have h2 := (Response.verdict.inj h).2
    unfold summOf at h2
    rw [ht] at h2
    exact certWhnfS_sound _ _ _ _ _ _ _ h2

theorem handle_tyConverted_sound (req : Request) (A B : Expr Nat)
    (ht : req.body.task = .tyConvT A B) (h : handle req = .verdict req.q (.tyConverted A B)) :
    Nonempty (TyConvT (envOfTable req.body.tbl) req.body.univs req.body.ctx A B) := by
  unfold handle at h
  by_cases hq : req.q ≠ qOf req.body
  · simp [hq] at h
  · simp only [hq, if_false] at h
    have h2 := (Response.verdict.inj h).2
    unfold summOf at h2
    rw [ht] at h2
    exact certTyConvS_sound _ _ _ _ _ _ h2

/-! ## §7 named residues at the bytes level -/

theorem decodeRequest_encVal (v : Val) (h : dqV v) : decodeRequest (encVal v) = valRequest v := by
  unfold decodeRequest
  rw [wireDecCanon_encVal v h]

theorem valRequest_schema (q sch : String) (u : Int) (t c : List Val) (k : Val) (bud : Int)
    (h : sch ≠ schemaName) :
    valRequest (.r [.s q, .r [.s sch, .i u, .l t, .l c, k, .i bud]]) =
      .error "[rcic_wire_consumer_schema]" := by
  simp [valRequest, h]

theorem valRequest_budget (q : String) (u : Int) (t c : List Val) (k : Val) (bud : Int)
    (h : u < 0 ∨ maxBudget < u ∨ bud < 0 ∨ maxBudget < bud) :
    valRequest (.r [.s q, .r [.s schemaName, .i u, .l t, .l c, k, .i bud]]) =
      .error "[rcic_wire_consumer_budget]" := by
  simp [valRequest, h]

theorem valRequest_term (q : String) (u : Int) (t c : List Val) (k : Val) (bud : Int)
    (hb : ¬ (u < 0 ∨ maxBudget < u ∨ bud < 0 ∨ maxBudget < bud))
    (h : t.mapM entryOf = none ∨ c.mapM declOf = none ∨ taskOf k = none) :
    valRequest (.r [.s q, .r [.s schemaName, .i u, .l t, .l c, k, .i bud]]) =
      .error "[rcic_wire_consumer_term]" := by
  simp only [valRequest, ne_eq, not_true_eq_false, if_false, hb, if_neg, not_false_eq_true]
  rcases h with h | h | h <;> simp [h]

theorem valRequest_shape_i (n : Int) : valRequest (.i n) = .error "[rcic_wire_consumer_shape]" := rfl
theorem valRequest_shape_nil : valRequest (.r []) = .error "[rcic_wire_consumer_shape]" := rfl

/-- a well-formed value that is not a request is the shape residue, end to end. -/
theorem handleBytes_shape_i (n : Int) (hn : inI64 n) :
    handleBytes (encVal (.i n)) = .malformed "[rcic_wire_consumer_shape]" :=
  handleSeen_malformed [] _ _ ((decodeRequest_encVal (.i n) hn).trans (valRequest_shape_i n))

/-- a request with a foreign schema, end to end. -/
theorem handleBytes_schema (v : Val) (hv : dqV v) (q sch : String) (u : Int) (t c : List Val)
    (k : Val) (bud : Int) (hv' : v = .r [.s q, .r [.s sch, .i u, .l t, .l c, k, .i bud]])
    (h : sch ≠ schemaName) : handleBytes (encVal v) = .malformed "[rcic_wire_consumer_schema]" := by
  subst hv'
  exact handleSeen_malformed [] _ _
    ((decodeRequest_encVal _ hv).trans (valRequest_schema q sch u t c k bud h))

/-- an altered request (its `q` is not the digest of its body), end to end. -/
theorem handleBytes_altered (r : Request) (h : RequestGood r) (ha : r.q ≠ qOf r.body) :
    handleBytes (encodeRequest r) = .malformed residueAltered :=
  (handleBytes_encode r h).trans (handle_altered r ha)

/-! ## §8 a pinned accepted request -/

def pinBody : Body :=
  ⟨0, [], [], .convT (.sort (.succ .zero)) (.sort .zero) (.sort .zero), 8⟩

theorem pinBody_good : BodyGood pinBody := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · intro p hp; simp [pinBody] at hp
  · intro d hd; simp [pinBody] at hd
  · simp [pinBody, TaskGood, ExprGood, ExprOK, exprD, LvlOK, lvlD, exprFuel, natB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem pin_summ :
    summOf pinBody = .converted (.sort .zero) (.sort .zero) (.sort (.succ .zero)) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem pin_q_length : (qOf pinBody).length ≤ 1024 := by decide

/-- the accepted pin: the sealed bytes of a `Sort 0 ≡ Sort 0` request are answered by the accepted
    verdict with the same `q`. -/
theorem pin_accepted :
    handleBytes (encodeRequest (Request.ofBody pinBody)) =
      .verdict (qOf pinBody) (.converted (.sort .zero) (.sort .zero) (.sort (.succ .zero))) := by
  have := handleBytes_accepted pinBody pinBody_good pin_q_length (by rw [pin_summ]; trivial)
  rw [pin_summ] at this
  exact this

end Rcic.Wire.Consumer

#print axioms Rcic.Wire.Consumer.wireDecCanon_encVal
#print axioms Rcic.Wire.Consumer.decodeRequest_encode
#print axioms Rcic.Wire.Consumer.handleBytes_encode
#print axioms Rcic.Wire.Consumer.handleBytes_accepted
#print axioms Rcic.Wire.Consumer.handle_q
#print axioms Rcic.Wire.Consumer.handle_altered
#print axioms Rcic.Wire.Consumer.handleSeen_malformed
#print axioms Rcic.Wire.Consumer.handleSeen_encode_replay
#print axioms Rcic.Wire.Consumer.handle_converted_sound
#print axioms Rcic.Wire.Consumer.handle_whnfed_sound
#print axioms Rcic.Wire.Consumer.handle_tyConverted_sound
#print axioms Rcic.Wire.Consumer.handleBytes_schema
#print axioms Rcic.Wire.Consumer.pin_accepted
