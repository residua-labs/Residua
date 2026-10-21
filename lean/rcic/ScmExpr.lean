/-
RCIC 06 §6–§9, §12 — function groups, core expressions, raise/handle,
fold and bounded fix: the intrinsic `CoreExpr Π Γ T` (K2 statement layer).

Owner text:
  §7 (06:118-150) "Group-local calls use local function refs; external calls
      use complete `FunctionRef` values. Bodies are typed under parameter
      contexts and exact result types."
  §8 (06:154-179) `CoreExpr Π Γ T` with 19 families and the frozen binding
      conventions.
  §9 (06:183-198) the types of `raise` and `handle`.
  §12 (06:238-240) bounded fix "returns a record containing convergence flag,
      state, and semantic step count".

`Π` is written `S : Sig` (signature scope: local function signatures,
external `FunctionRef` signatures, residue catalog).

PIN (M-002): `scmTyping` is the carrier entry `rcic.scm_typing form fuel prog
ctx e` of `apps/rcic-scm-typing` (#6042). It does not infer a bare type: it
ELABORATES the raw expression into an intrinsic `CoreExpr S Γ T` (or the raw
program into intrinsic bodies), and reports `T`. So every `CoreExpr`
constructor, `Branches`, `Fields`, `Args`, `FnRef` and `Bodies` is reachable
from the 56 pinned rows (M-002a). Refusal codes and their order follow the
carrier exactly; a failing row fails the build (`#guard`).

TRANSCRIPTION TABLE (06 rule → Lean):
  §6 "Each residue ref has exactly one payload type"  → `catalogCanonical`
        (checked by `progCheck`); payload lookup `catalogPt`
  §7 group-local calls use local function refs        → `FnRef.local`
  §7 external calls use complete FunctionRef values  → `FnRef.external`
  §7 bodies typed under parameter contexts and exact result types
                                                      → `Bodies` / `progCheck`
  §7 CoreProgramRoot owns the entry                   → `RawProg.entry`, checked
        in range by `progCheck`
  §8 literals → `lit` · var → `var` · letE → `letE` · ifE → `ifE`
     pairE fstE sndE → `pairE` `fstE` `sndE` · injE matchSum → `injE`
     `matchSum` · recordE fieldE → `recordE` `fieldE` · nilE consE foldList
     → `nilE` `consE` `foldList` · boundedFix → `boundedFix` · prim → `prim`
     · call → `call` · raise → `raise` · handle → `handle`   (19 = 19)
  §8 binding conventions:
     "let body: value :: Γ"            → `letE` body context `A :: Γ`
     "sum branch: payload :: Γ"        → `Branches.cons` branch context `A :: Γ`
     "fold body: element :: accumulator :: Γ" → `foldList` body context `A :: B :: Γ`
     "bounded-fix stop/step: state :: Γ"      → `boundedFix` stop/step context `St :: Γ`
     "handler: residue payload :: Γ"   → `handle` handler context `P :: Γ`
  §9 raise : (r) → CoreExpr Π Γ (PayloadType r) → CoreExpr Π Γ T  → `raise`
  §9 handle : (r) → CoreExpr Π Γ T → CoreExpr Π (PayloadType r :: Γ) T → … → `handle`
  §12 bounded fix result record                      → `fixTy`
  §3 record field keys are unique                    → `recordE`'s `keysUnique` proof
  `[spec_ambiguity]` (carrier-recorded): a `matchSum` over the empty sum has
     no result type → `matchSum`'s `ts ≠ []` proof
-/
import rcic.ScmPrim

namespace Rcic.Scm

/-! ## Signature scope Π -/

structure FnSig where
  params : List CoreTy
  result : CoreTy

structure ExtSig where
  ref : String
  params : List CoreTy
  result : CoreTy

structure Sig where
  fns : List FnSig
  ext : List ExtSig
  catalog : List CatalogEntry

/-- 06 §12: bounded fix returns convergence flag, state, semantic step count. -/
def fixTy (st : CoreTy) : CoreTy := .record [("converged", .bool), ("state", st), ("steps", .i64)]

def keysUnique : List String → Bool
  | [] => true
  | k :: ks => !(ks.contains k) && keysUnique ks

/-- A function reference of signature `ps → T` in scope `S`. -/
inductive FnRef (S : Sig) : List CoreTy → CoreTy → Type where
  | local (i : Nat) (fs : FnSig) (h : S.fns.get? i = some fs) : FnRef S fs.params fs.result
  | external (r : String) (e : ExtSig) (h : S.ext.find? (fun x => x.ref == r) = some e) :
      FnRef S e.params e.result

/-! ## §8 Core expressions (intrinsic) -/

mutual
inductive CoreExpr (S : Sig) : List CoreTy → CoreTy → Type where
  | lit {Γ : List CoreTy} {T : CoreTy} (v : CoreVal T) : CoreExpr S Γ T
  | var {Γ : List CoreTy} {T : CoreTy} (i : Nat) (h : Γ.get? i = some T) : CoreExpr S Γ T
  | letE {Γ : List CoreTy} {A T : CoreTy} (a : CoreExpr S Γ A) (b : CoreExpr S (A :: Γ) T) :
      CoreExpr S Γ T
  | ifE {Γ : List CoreTy} {T : CoreTy} (c : CoreExpr S Γ .bool) (th el : CoreExpr S Γ T) :
      CoreExpr S Γ T
  | pairE {Γ : List CoreTy} {A B : CoreTy} (a : CoreExpr S Γ A) (b : CoreExpr S Γ B) :
      CoreExpr S Γ (.pair A B)
  | fstE {Γ : List CoreTy} {A B : CoreTy} (a : CoreExpr S Γ (.pair A B)) : CoreExpr S Γ A
  | sndE {Γ : List CoreTy} {A B : CoreTy} (a : CoreExpr S Γ (.pair A B)) : CoreExpr S Γ B
  | injE {Γ : List CoreTy} {A : CoreTy} (ts : List CoreTy) (i : Nat) (h : ts.get? i = some A)
      (a : CoreExpr S Γ A) : CoreExpr S Γ (.sum ts)
  | matchSum {Γ : List CoreTy} {ts : List CoreTy} {T : CoreTy} (s : CoreExpr S Γ (.sum ts))
      (bs : Branches S Γ ts T) (hne : ts ≠ []) : CoreExpr S Γ T
  | recordE {Γ : List CoreTy} {fs : List (String × CoreTy)} (xs : Fields S Γ fs)
      (hk : keysUnique (fs.map Prod.fst) = true) : CoreExpr S Γ (.record fs)
  | fieldE {Γ : List CoreTy} {fs : List (String × CoreTy)} {A : CoreTy} (i : Nat) (k : String)
      (h : fs.get? i = some (k, A)) (r : CoreExpr S Γ (.record fs)) : CoreExpr S Γ A
  | nilE {Γ : List CoreTy} {A : CoreTy} : CoreExpr S Γ (.list A)
  | consE {Γ : List CoreTy} {A : CoreTy} (h : CoreExpr S Γ A) (tl : CoreExpr S Γ (.list A)) :
      CoreExpr S Γ (.list A)
  | foldList {Γ : List CoreTy} {A B : CoreTy} (l : CoreExpr S Γ (.list A)) (init : CoreExpr S Γ B)
      (body : CoreExpr S (A :: B :: Γ) B) : CoreExpr S Γ B
  | boundedFix {Γ : List CoreTy} {St : CoreTy} (init : CoreExpr S Γ St) (limit : CoreExpr S Γ .i64)
      (stop : CoreExpr S (St :: Γ) .bool) (step : CoreExpr S (St :: Γ) St) : CoreExpr S Γ (fixTy St)
  | prim {Γ : List CoreTy} (op : PrimOp) (args : Args S Γ (primSig op).ps) :
      CoreExpr S Γ (primSig op).rt
  | call {Γ : List CoreTy} {ps : List CoreTy} {T : CoreTy} (f : FnRef S ps T) (args : Args S Γ ps) :
      CoreExpr S Γ T
  | raise {Γ : List CoreTy} {P T : CoreTy} (r : RaisedRef) (h : catalogPt S.catalog r = some P)
      (p : CoreExpr S Γ P) : CoreExpr S Γ T
  | handle {Γ : List CoreTy} {P T : CoreTy} (r : RaisedRef) (h : catalogPt S.catalog r = some P)
      (body : CoreExpr S Γ T) (hd : CoreExpr S (P :: Γ) T) : CoreExpr S Γ T
inductive Branches (S : Sig) : List CoreTy → List CoreTy → CoreTy → Type where
  | nil {Γ : List CoreTy} {T : CoreTy} : Branches S Γ [] T
  | cons {Γ : List CoreTy} {A T : CoreTy} {ts : List CoreTy} (b : CoreExpr S (A :: Γ) T)
      (bs : Branches S Γ ts T) : Branches S Γ (A :: ts) T
inductive Fields (S : Sig) : List CoreTy → List (String × CoreTy) → Type where
  | nil {Γ : List CoreTy} : Fields S Γ []
  | cons {Γ : List CoreTy} {A : CoreTy} {fs : List (String × CoreTy)} (k : String)
      (x : CoreExpr S Γ A) (xs : Fields S Γ fs) : Fields S Γ ((k, A) :: fs)
inductive Args (S : Sig) : List CoreTy → List CoreTy → Type where
  | nil {Γ : List CoreTy} : Args S Γ []
  | cons {Γ : List CoreTy} {A : CoreTy} {ps : List CoreTy} (x : CoreExpr S Γ A)
      (xs : Args S Γ ps) : Args S Γ (A :: ps)
end

/-- A closed core program over `S`: one body per local signature, typed
    under its parameter context at its exact result type (06 §7). -/
inductive Bodies (S : Sig) : List FnSig → Type where
  | nil : Bodies S []
  | cons {f : FnSig} {fs : List FnSig} (b : CoreExpr S f.params f.result) (bs : Bodies S fs) :
      Bodies S (f :: fs)

/-! ## Raw expressions and programs: the carrier record encoding -/

inductive RawFn where
  | local (i : Int)
  | ext (ref : String)
  deriving BEq

inductive RawExpr where
  | lit (v : Val) (t : CoreTy)
  | var (i : Int)
  | letE (a b : RawExpr)
  | ifE (c th el : RawExpr)
  | pair (a b : RawExpr)
  | fst (a : RawExpr)
  | snd (a : RawExpr)
  | inj (i : Int) (ts : List CoreTy) (a : RawExpr)
  | matchE (s : RawExpr) (bs : List RawExpr)
  | recordE (keys : List String) (fs : List RawExpr)
  | field (r : RawExpr) (i : Int)
  | nil (t : CoreTy)
  | cons (h tl : RawExpr)
  | fold (l init body : RawExpr)
  | fix (init limit stop step : RawExpr)
  | prim (op : String) (args : List RawExpr)
  | call (f : RawFn) (args : List RawExpr)
  | raise (r : String) (p : RawExpr) (t : CoreTy)
  | handle (r : String) (body h : RawExpr)
  | unknown (k : Int)
  deriving Inhabited, BEq

structure RawFnDef where
  params : List CoreTy
  result : CoreTy
  body : RawExpr

structure RawProg where
  fns : List RawFnDef
  ext : List ExtSig
  catalog : List CatalogEntry
  entry : Int

def sigOf (p : RawProg) : Sig :=
  ⟨p.fns.map (fun f => ⟨f.params, f.result⟩), p.ext, p.catalog⟩

/-! ## Elaboration raw → intrinsic (the carrier's inference, refusal for refusal) -/

abbrev Elab (S : Sig) (Γ : List CoreTy) := Except String (Σ T, CoreExpr S Γ T)

def tyErr (c : String) : Except String α := .error ("[rcic_scm_typing_" ++ c ++ "]")

def toArgs {S : Sig} {Γ : List CoreTy} : List (Σ T, CoreExpr S Γ T) → (ps : List CoreTy) →
    Option (Args S Γ ps)
  | [], [] => some .nil
  | ⟨T, e⟩ :: xs, p :: ps =>
      if h : T = p then (toArgs xs ps).map (Args.cons (h ▸ e)) else none
  | _, _ => none

/-- Elaborate a list of expressions with one elaborator (the carrier's
    `rcic.scm_ty_infer_list`: left to right, first refusal wins). -/
def elabListWith {S : Sig} {Γ : List CoreTy} (g : RawExpr → Elab S Γ) :
    List RawExpr → Except String (List (Σ T, CoreExpr S Γ T))
  | [] => .ok []
  | e :: es => do
      let x ← g e
      let xs ← elabListWith g es
      pure (x :: xs)

/-- The remaining branches of a match at a known result type `T`, each under
    its payload-extended context (06 §8 "sum branch: payload :: Γ"). -/
def elabBranchesWith {S : Sig} (g : (Γ' : List CoreTy) → RawExpr → Elab S Γ') (Γ : List CoreTy)
    (T : CoreTy) : (ts : List CoreTy) → List RawExpr → Except String (Branches S Γ ts T)
  | [], [] => .ok .nil
  | A :: ts, b :: bs => do
      let ⟨T', eb⟩ ← g (A :: Γ) b
      if ht : T' = T then
        let rest ← elabBranchesWith g Γ T ts bs
        pure (.cons (ht ▸ eb) rest)
      else tyErr "mismatch"
  | _, _ => tyErr "shape"

/-- Record fields in schema order, keeping the key list. -/
def elabFieldsWith {S : Sig} {Γ : List CoreTy} (g : RawExpr → Elab S Γ) :
    (keys : List String) → List RawExpr →
    Except String (Σ fs : List (String × CoreTy), Σ' (_ : Fields S Γ fs), fs.map Prod.fst = keys)
  | [], [] => .ok ⟨[], .nil, rfl⟩
  | k :: ks, e :: es => do
      let ⟨A, ex⟩ ← g e
      let ⟨fs, xs, h⟩ ← elabFieldsWith g ks es
      pure ⟨(k, A) :: fs, .cons k ex xs, h ▸ rfl⟩
  | _, _ => tyErr "shape"

/-- Elaboration, structural on the carrier's fuel: `n = fuel + 1`, so `n = 0`
    is the carrier's `fuel < 0` refusal and every child gets `n - 1`. -/
def elabE : Nat → (S : Sig) → (Γ : List CoreTy) → RawExpr → Elab S Γ
  | 0, _, _, _ => tyErr "fuel"
  | f + 1, S, Γ, e =>
  match e with
  | .lit v t =>
      match toCore t v with
      | some cv => .ok ⟨t, .lit cv⟩
      | none => tyErr "mismatch"
  | .var i =>
      if i < 0 then tyErr "var_scope" else
      match h : Γ.get? i.toNat with
      | some T => .ok ⟨T, .var i.toNat h⟩
      | none => tyErr "var_scope"
  | .letE a b => do
      let ⟨A, ea⟩ ← elabE f S Γ a
      let ⟨T, eb⟩ ← elabE f S (A :: Γ) b
      pure ⟨T, .letE ea eb⟩
  | .ifE c th el => do
      let ⟨C, ec⟩ ← elabE f S Γ c
      if hc : C = .bool then
        let ⟨T, et⟩ ← elabE f S Γ th
        let ⟨E, ee⟩ ← elabE f S Γ el
        if he : E = T then pure ⟨T, .ifE (hc ▸ ec) et (he ▸ ee)⟩ else tyErr "mismatch"
      else tyErr "mismatch"
  | .pair a b => do
      let ⟨A, ea⟩ ← elabE f S Γ a
      let ⟨B, eb⟩ ← elabE f S Γ b
      pure ⟨.pair A B, .pairE ea eb⟩
  | .fst a => do
      let r ← elabE f S Γ a
      match r with
      | ⟨.pair A _, ea⟩ => pure ⟨A, .fstE ea⟩
      | _ => tyErr "shape"
  | .snd a => do
      let r ← elabE f S Γ a
      match r with
      | ⟨.pair _ B, ea⟩ => pure ⟨B, .sndE ea⟩
      | _ => tyErr "shape"
  | .inj i ts a =>
      if i < 0 then tyErr "shape" else
      match h : ts.get? i.toNat with
      | none => tyErr "shape"
      | some A => do
          let ⟨T, ea⟩ ← elabE f S Γ a
          if hA : T = A then pure ⟨.sum ts, .injE ts i.toNat h (hA ▸ ea)⟩ else tyErr "mismatch"
  | .matchE s bs => do
      let r ← elabE f S Γ s
      match r with
      | ⟨.sum ts, es⟩ =>
          match ts, bs, es with
          | A :: ts', b :: bs', es =>
              if bs'.length = ts'.length then do
                let ⟨T, eb⟩ ← elabE f S (A :: Γ) b
                let rest ← elabBranchesWith (elabE f S) Γ T ts' bs'
                pure ⟨T, .matchSum es (.cons eb rest) (fun h => List.noConfusion h)⟩
              else tyErr "shape"
          | _, _, _ => tyErr "shape"
      | _ => tyErr "shape"
  | .recordE keys fs =>
      if keys.length ≠ fs.length then tyErr "shape" else
      if hk : keysUnique keys = true then do
        let ⟨flds, xs, hkeys⟩ ← elabFieldsWith (elabE f S Γ) keys fs
        pure ⟨.record flds, .recordE xs (hkeys ▸ hk)⟩
      else tyErr "record_keys"
  | .field r i => do
      let rr ← elabE f S Γ r
      match rr with
      | ⟨.record fs, er⟩ =>
          if i < 0 then tyErr "shape" else
          match h : fs.get? i.toNat with
          | some (k, A) => pure ⟨A, .fieldE i.toNat k h er⟩
          | none => tyErr "shape"
      | _ => tyErr "shape"
  | .nil t => .ok ⟨.list t, .nilE⟩
  | .cons h tl => do
      let ⟨H, eh⟩ ← elabE f S Γ h
      let ⟨L, el⟩ ← elabE f S Γ tl
      if hl : L = .list H then pure ⟨.list H, .consE eh (hl ▸ el)⟩ else tyErr "mismatch"
  | .fold l init body => do
      let rl ← elabE f S Γ l
      match rl with
      | ⟨.list A, el⟩ => do
          let ⟨B, ei⟩ ← elabE f S Γ init
          let ⟨B', eb⟩ ← elabE f S (A :: B :: Γ) body
          if hb : B' = B then pure ⟨B, .foldList el ei (hb ▸ eb)⟩ else tyErr "mismatch"
      | _ => tyErr "shape"
  | .fix init limit stop step => do
      let ⟨St, ei⟩ ← elabE f S Γ init
      let ⟨L, el⟩ ← elabE f S Γ limit
      if hl : L = .i64 then
        let ⟨B, es⟩ ← elabE f S (St :: Γ) stop
        if hb : B = .bool then
          let ⟨St', ep⟩ ← elabE f S (St :: Γ) step
          if hs : St' = St then pure ⟨fixTy St, .boundedFix ei (hl ▸ el) (hb ▸ es) (hs ▸ ep)⟩
          else tyErr "mismatch"
        else tyErr "mismatch"
      else tyErr "mismatch"
  | .prim op args =>
      match primOfString op with
      | none => tyErr "prim"
      | some o => do
          let xs ← elabListWith (elabE f S Γ) args
          match toArgs xs (primSig o).ps with
          | some as => pure ⟨(primSig o).rt, .prim o as⟩
          | none => tyErr "mismatch"
  | .call (.local i) args =>
      if i < 0 then tyErr "local_ref" else
      match h : S.fns.get? i.toNat with
      | none => tyErr "local_ref"
      | some fs => do
          let xs ← elabListWith (elabE f S Γ) args
          match toArgs xs fs.params with
          | some as => pure ⟨fs.result, .call (.local i.toNat fs h) as⟩
          | none => tyErr "mismatch"
  | .call (.ext ref) args =>
      match h : S.ext.find? (fun (y : ExtSig) => y.ref == ref) with
      | none => tyErr "external_ref"
      | some x => do
          let xs ← elabListWith (elabE f S Γ) args
          match toArgs xs x.params with
          | some as =>
              pure ⟨x.result, .call (.external ref x h) as⟩
          | none => tyErr "mismatch"
  | .raise r p t =>
      match h : catalogPt S.catalog r with
      | none => tyErr "residue_ref"
      | some P => do
          let ⟨P', ep⟩ ← elabE f S Γ p
          if hp : P' = P then pure ⟨t, .raise r h (hp ▸ ep)⟩ else tyErr "mismatch"
  | .handle r body hd =>
      match h : catalogPt S.catalog r with
      | none => tyErr "residue_ref"
      | some P => do
          let ⟨T, eb⟩ ← elabE f S Γ body
          let ⟨T', eh⟩ ← elabE f S (P :: Γ) hd
          if ht : T' = T then pure ⟨T, .handle r h eb (ht ▸ eh)⟩ else tyErr "mismatch"
  | .unknown _ => tyErr "unknown_expr"

/-- The carrier's Int fuel as the structural `n = fuel + 1` (`0` when the
    carrier would refuse at once). -/
def fuelN (fuel : Int) : Nat := if fuel < 0 then 0 else fuel.toNat + 1

/-- Elaborate every body of a raw program (06 §7: bodies typed under their
    parameter contexts at their exact result types). -/
def elabBodies (n : Nat) (S : Sig) : (fs : List RawFnDef) →
    Except String (Bodies S (fs.map (fun f => ⟨f.params, f.result⟩)))
  | [] => .ok .nil
  | f :: fs => do
      let ⟨T, eb⟩ ← elabE n S f.params f.body
      if ht : T = f.result then
        let rest ← elabBodies n S fs
        pure (.cons (f := ⟨f.params, f.result⟩) (ht ▸ eb) rest)
      else tyErr "mismatch"

/-- The carrier's program check: canonical catalog, entry in the group,
    every body elaborated; reports the entry result type. -/
def progCheck (fuel : Int) (p : RawProg) : Except String (Σ' (_ : Bodies (sigOf p) (sigOf p).fns), CoreTy) :=
  if !catalogCanonical p.catalog then tyErr "catalog" else
  if p.entry < 0 then tyErr "entry" else
  match p.fns.get? p.entry.toNat with
  | none => tyErr "entry"
  | some ef => do
      let bs ← elabBodies (fuelN fuel) (sigOf p) p.fns
      pure ⟨bs, ef.result⟩

/-! ## The carrier entry point -/

structure TyOut where
  ok : Int
  t : CoreTy
  code : String
  deriving BEq

def scmTyping (form : Int) (fuel : Int) (p : RawProg) (ctx : List CoreTy) (e : RawExpr) : TyOut :=
  if form = 0 then
    match progCheck fuel p with
    | .ok ⟨_, t⟩ => ⟨1, t, ""⟩
    | .error c => ⟨0, unitTy, c⟩
  else if form = 1 then
    match elabE (fuelN fuel) (sigOf p) ctx e with
    | .ok ⟨t, _⟩ => ⟨1, t, ""⟩
    | .error c => ⟨0, unitTy, c⟩
  else ⟨0, unitTy, "[rcic_scm_typing_unknown_form]"⟩

end Rcic.Scm
