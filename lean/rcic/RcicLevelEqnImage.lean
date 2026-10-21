/-
RM-023 slice 2 — `RawProg` image of `scm/rcic/level_eqn.scm`.

The entry is that file's composition: fuel check, then calls to
`params_of`, `union_nat`, `all_subsets`, `all_none`, `level_ok`,
`level_refuse`. Helper bodies are not pasted into the entry.
`paramsOf` / `unionNat` / `allSubsets` / `allNoneAgree` stay the
landed Lean functions; `denoteCall` dispatches a call to them.

Parameter order is the belief `(call rcic.level_eqn l r fuel)`:
index 0 `l`, 1 `r`, 2 `fuel`. Record fields are source order
(`ok`, `params`/`val`, `code`).

`encode`'s kind-record is not one `CoreTy`, so `progCheck` is not
claimed. `closure_claim` stays 0.
-/
import rcic.ScmExpr
import rcic.RcicLevelKind

namespace Rcic.LevelEqnImage

open Rcic.Scm
open Rcic.Declarative
open Rcic.LevelKind

def iRefuse : Int := 1
def iParams : Int := 2
def iUnion : Int := 3
def iSubsets : Int := 4
def iAllNone : Int := 5
def iOk : Int := 6

def i64 : CoreTy := .i64
def strTy : CoreTy := .str
def resTy : CoreTy := .record [("ok", i64), ("val", i64), ("code", strTy)]
def natListTy : CoreTy := .list i64
def paramsTy : CoreTy :=
  .record [("ok", i64), ("params", natListTy), ("code", strTy)]
/-- Tag slot. `encode` is a variable-width record, not this schema. -/
def kindSlot : CoreTy := .record [("kind", i64)]

def li (n : Int) : RawExpr := .lit (.i n) i64
def ls (s : String) : RawExpr := .lit (.s s) strTy
def v (i : Int) : RawExpr := .var i
def callL (i : Int) (args : List RawExpr) : RawExpr := .call (.local i) args
def fld (e : RawExpr) (i : Int) : RawExpr := .field e i
def eqI (a b : RawExpr) : RawExpr := .prim "eq" [a, b]

/-- `scm/rcic/level_eqn.scm`, de Bruijn, calls only. -/
def levelEqnBody : RawExpr :=
  .ifE (.prim "lt" [v 2, li 0])
    (callL iRefuse [ls "[rcic_level_fuel]"])
    (.letE (callL iParams [v 0])
      (.ifE (eqI (fld (v 0) 0) (li 0))
        (callL iRefuse [fld (v 0) 2])
        (.letE (callL iParams [v 2])
          (.ifE (eqI (fld (v 0) 0) (li 0))
            (callL iRefuse [fld (v 0) 2])
            (.letE (callL iUnion [fld (v 1) 1, fld (v 0) 1])
              (.letE (callL iSubsets [v 0])
                (.letE (callL iAllNone [v 4, v 5, v 1, v 0, v 6])
                  (.ifE (eqI (fld (v 0) 0) (li 0))
                    (callL iRefuse [fld (v 0) 2])
                    (.ifE (eqI (fld (v 0) 1) (li 1))
                      (callL iOk [li 1])
                      (callL iRefuse [ls "[rcic_level_not_equal]"]))))))))))

def stub (k : Int) : RawExpr := .unknown k

def fn (ps : List CoreTy) (rt : CoreTy) (b : RawExpr) : RawFnDef := ⟨ps, rt, b⟩

/-- Refuse and ok are the one-line modules. The four decision calls
stay at the boundary (`unknown`): their meaning is `denoteCall`. -/
def levelEqnProg : RawProg where
  fns := [
    fn [kindSlot, kindSlot, i64] resTy levelEqnBody,
    fn [strTy] resTy (.recordE ["ok", "val", "code"] [li 0, li 0, v 0]),
    fn [kindSlot] paramsTy (stub iParams),
    fn [natListTy, natListTy] natListTy (stub iUnion),
    fn [natListTy] (.list natListTy) (stub iSubsets),
    fn [kindSlot, kindSlot, natListTy, .list natListTy, i64] resTy (stub iAllNone),
    fn [i64] resTy (.recordE ["ok", "val", "code"] [li 1, v 0, ls ""]),
  ]
  ext := []
  catalog := []
  entry := 0

/-- Answer planted as `level_ok 1`, with none of the decision calls. -/
def inlinedAccept : RawExpr := callL iOk [li 1]

mutual
def localCalls : RawExpr → List Int
  | .lit _ _ => []
  | .var _ => []
  | .nil _ => []
  | .unknown _ => []
  | .letE a b => localCalls a ++ localCalls b
  | .ifE c t e => localCalls c ++ localCalls t ++ localCalls e
  | .pair a b => localCalls a ++ localCalls b
  | .fst a => localCalls a
  | .snd a => localCalls a
  | .inj _ _ a => localCalls a
  | .matchE s bs => localCalls s ++ localCallsList bs
  | .recordE _ fs => localCallsList fs
  | .field r _ => localCalls r
  | .cons h tl => localCalls h ++ localCalls tl
  | .fold l init body => localCalls l ++ localCalls init ++ localCalls body
  | .fix i lim stop step =>
      localCalls i ++ localCalls lim ++ localCalls stop ++ localCalls step
  | .prim _ args => localCallsList args
  | .call (.local i) args => i :: localCallsList args
  | .call (.ext _) args => localCallsList args
  | .raise _ p _ => localCalls p
  | .handle _ body h => localCalls body ++ localCalls h

def localCallsList : List RawExpr → List Int
  | [] => []
  | e :: es => localCalls e ++ localCallsList es
end

theorem levelEqnBody_calls :
    localCalls levelEqnBody =
      [iRefuse, iParams, iRefuse, iParams, iRefuse, iUnion, iSubsets,
        iAllNone, iRefuse, iOk, iRefuse] := rfl

theorem inlinedAccept_not_composer :
    (localCalls inlinedAccept == localCalls levelEqnBody) = false := rfl

/-! ## Denotation: calls go to the landed decider, not a second copy -/

def okRec (v : Val) : Val := .r [.i 1, v, .s ""]
def refuseRec (c : String) : Val := .r [.i 0, .i 0, .s c]
def encNats (xs : List Nat) : Val := .l (xs.map fun n => .i (Int.ofNat n))

def decNats : List Val → Option (List Nat)
  | [] => some []
  | .i n :: xs =>
    if 0 ≤ n then
      match decNats xs with
      | some ys => some (n.toNat :: ys)
      | none => none
    else none
  | _ :: _ => none

def decNatList : Val → Option (List Nat)
  | .l xs => decNats xs
  | _ => none

def encSets (xss : List (List Nat)) : Val := .l (xss.map encNats)

def decSets : List Val → Option (List (List Nat))
  | [] => some []
  | x :: xs =>
    match decNatList x, decSets xs with
    | some ys, some yss => some (ys :: yss)
    | _, _ => none

def decSetList : Val → Option (List (List Nat))
  | .l xs => decSets xs
  | _ => none

/-- A local call's meaning. `iParams` / `iUnion` / `iSubsets` / `iAllNone`
are `paramsOf`, `unionNat`, `allSubsets`, `allNoneAgree`. -/
def denoteCall (i : Int) (args : List Val) : Option Val :=
  if i = iRefuse then
    match args with
    | [.s c] => some (refuseRec c)
    | _ => none
  else if i = iOk then
    match args with
    | [v] => some (okRec v)
    | _ => none
  else if i = iParams then
    match args with
    | [lv] =>
      some (match decode lv with
        | some l => .r [.i 1, encNats (paramsOf l), .s ""]
        | none => .r [.i 0, encNats [], .s "[rcic_level_unknown_ctor]"])
    | _ => none
  else if i = iUnion then
    match args with
    | [a, b] =>
      match decNatList a, decNatList b with
      | some xs, some ys => some (encNats (unionNat xs ys))
      | _, _ => none
    | _ => none
  else if i = iSubsets then
    match args with
    | [a] =>
      match decNatList a with
      | some xs => some (encSets (allSubsets xs))
      | none => none
    | _ => none
  else if i = iAllNone then
    match args with
    | [lv, rv, p, ns, .i fuel] =>
      if fuel < 0 then some (refuseRec "[rcic_level_fuel]")
      else
        match decode lv, decode rv, decNatList p, decSetList ns with
        | some l, some r, some P, some Ns =>
          some (.r [.i 1, .i (bif allNoneAgree l r P Ns then 1 else 0), .s ""])
        | _, _, _, _ => none
    | _ => none
  else none

mutual
def denote (env : List Val) (e : RawExpr) : Option Val :=
  match e with
  | .lit v _ => some v
  | .var i => if 0 ≤ i then env.get? i.toNat else none
  | .letE a b =>
    match denote env a with
    | some va => denote (va :: env) b
    | none => none
  | .ifE c t e =>
    match denote env c with
    | some (.b x) => if x = 1 then denote env t else denote env e
    | _ => none
  | .prim op args =>
    match denoteList env args with
    | some [.i a, .i b] =>
      if op = "lt" then some (.b (if a < b then 1 else 0))
      else if op = "eq" then some (.b (if a = b then 1 else 0))
      else none
    | _ => none
  | .field r i =>
    match denote env r with
    | some (.r fs) => if 0 ≤ i then fs.get? i.toNat else none
    | _ => none
  | .call (.local i) args =>
    match denoteList env args with
    | some vs => denoteCall i vs
    | none => none
  | _ => none

def denoteList (env : List Val) (es : List RawExpr) : Option (List Val) :=
  match es with
  | [] => some []
  | e :: rest =>
    match denote env e, denoteList env rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none
end

def envAt (l r : Level) (fuel : Int) : List Val := [encode l, encode r, .i fuel]

def accepts (v : Option Val) : Bool :=
  match v with
  | some (.r [.i 1, .i 1, .s ""]) => true
  | _ => false

def refuses (c : String) (v : Option Val) : Bool :=
  match v with
  | some (.r [.i 0, .i 0, .s d]) => d == c
  | _ => false

/-- Corpus fuel `-1`, and `decEqNNone`'s three `#eval` rows (also the
first three `rcic_level_eqn` corpus rows). -/
theorem pin_fuel :
    refuses "[rcic_level_fuel]"
      (denote (envAt .zero .zero (-1)) levelEqnBody) = true := by
  decide

theorem pin_imax :
    accepts (denote (envAt (.imax (.succ .zero) .zero) .zero 32) levelEqnBody) = true ∧
      decEqN (.imax (.succ .zero) .zero) .zero = true := by
  decide

theorem pin_params :
    refuses "[rcic_level_not_equal]"
      (denote (envAt (.param 0) (.param 1) 32) levelEqnBody) = true ∧
      decEqN (.param 0) (.param 1) = false := by
  decide

theorem pin_unbound :
    accepts (denote (envAt (.imax .zero (.param 0)) (.param 0) 32) levelEqnBody) = true ∧
      decEqN (.imax .zero (.param 0)) (.param 0) = true := by
  decide

theorem inlinedAccept_disagrees :
    accepts (denote (envAt (.param 0) (.param 1) 32) inlinedAccept) = true ∧
      accepts (denote (envAt (.param 0) (.param 1) 32) levelEqnBody) = false := by
  decide

#print axioms Rcic.LevelEqnImage.levelEqnBody_calls
#print axioms Rcic.LevelEqnImage.inlinedAccept_not_composer
#print axioms Rcic.LevelEqnImage.pin_fuel
#print axioms Rcic.LevelEqnImage.pin_imax
#print axioms Rcic.LevelEqnImage.pin_params
#print axioms Rcic.LevelEqnImage.pin_unbound
#print axioms Rcic.LevelEqnImage.inlinedAccept_disagrees

end Rcic.LevelEqnImage
