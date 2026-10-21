/-
RCIC 07 §3 — G2-S1: per-form pins at an ADMITTED env. `svRecordEnv`
(Pos@0, BNat@5, then one `SV<d>` group per `CoreTy` form, `RcicG2AdmitSV*`)
is `EnvWfT` (`svRecordBlockWfT`); here a concrete value of every form
embeds lit-free through `embedValAt` and its image `HasTyT`-checks at its
`SV<d>` family in that same env — so the blocks the pins type against are
the blocks admission accepted, not a raw table (`RcicG2Pins.pinEnv`).
-/
import rcic.RcicG2AdmitSVRecord
import rcic.RcicG2Pins

namespace Rcic.G2
open Rcic.Declarative Rcic.Scm

/-- every `SV<d>` family of the admitted stack. Agrees with `svRefOf` on
    `i64`/`bool` — the only component types the stacked blocks name. -/
def svAdmRefOf : CoreTy → Nat
  | .i64 => 9
  | .bool => 12
  | .list .i64 => 16
  | .str => 20
  | .bytes => 24
  | .pair .i64 .bool => 28
  | .sum [.i64, .bool] => 31
  | .record [(_, .i64), (_, .bool)] => 35
  | _ => 0

def svAdmEnvWfT : EnvWfT svRecordEnv := svRecordBlockWfT

theorem svAdmSup_ok : BNatPrereq svRecordEnv svSup := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- i64 — `.i (-1)` at offset `-1 + 2^63` under `SV<i64>.mk` (member 10). -/
def admI64Term : Expr Nat := .app (.const 10 []) (bnatTerm svSup ((-1 : Int) + 2^63).toNat)

theorem adm_i64_embeds : embedValAt svSup svAdmRefOf .i64 (.i (-1)) = some admI64Term := by
  simp [embedValAt, svAdmRefOf, i64Term, admI64Term]

def adm_i64_ty : HasTyT svRecordEnv 0 [] admI64Term (.const 9 []) :=
  .app _ _ _ _ _ (const_ty svRecordEnv 0 [] 10 _ rfl rfl)
    (bnatTerm_ty svRecordEnv 0 [] svSup _ svAdmSup_ok.h0 svAdmSup_ok.h1
      svAdmSup_ok.hone svAdmSup_ok.hz svAdmSup_ok.hp)

/-- bool — `.b 1` is `SV<bool>.tt` (member 14). -/
theorem adm_bool_embeds : embedValAt svSup svAdmRefOf .bool (.b 1) = some (.const 14 []) := by
  simp [embedValAt, svAdmRefOf]

def adm_bool_ty : HasTyT svRecordEnv 0 [] (.const 14 []) (.const 12 []) :=
  const_ty svRecordEnv 0 [] 14 _ rfl rfl

/-- list — `.l [.i (-1)]` is `cons (mk …) nil` at `SV<list i64>` (16). -/
theorem adm_list_embeds :
    embedValAt svSup svAdmRefOf (.list .i64) (.l [.i (-1)]) =
      some (consTower 17 18 [admI64Term]) := by
  simp [embedValAt, svAdmRefOf, i64Term, admI64Term, mapOpt]

def adm_list_ty : HasTyT svRecordEnv 0 [] (consTower 17 18 [admI64Term]) (.const 16 []) :=
  .app _ _ _ _ _
    (.app _ _ _ _ _ (const_ty svRecordEnv 0 [] 18 _ rfl rfl) adm_i64_ty)
    (const_ty svRecordEnv 0 [] 17 _ rfl rfl)

/-- str — `.s "ab"` is `scons 97 (scons 98 snil)` at `SV<str>` (20). -/
theorem adm_str_embeds :
    embedValAt svSup svAdmRefOf .str (.s "ab") = some (strTerm svSup 21 22 "ab") := by
  simp [embedValAt, svAdmRefOf]

def adm_str_ty : HasTyT svRecordEnv 0 [] (strTerm svSup 21 22 "ab") (.const 20 []) :=
  strTerm_ty svRecordEnv 0 [] svSup 21 22 20 "ab" svAdmSup_ok rfl rfl

/-- bytes — `.y [0, 255]` is `bcons 0 (bcons 255 bnil)` at `SV<bytes>` (24). -/
theorem adm_bytes_embeds :
    embedValAt svSup svAdmRefOf .bytes (.y [0, 255]) =
      some (consTower 25 26 [bnatTerm svSup 0, bnatTerm svSup 255]) := by
  simp [embedValAt, svAdmRefOf, bytesTerm]

def adm_bytes_ty :
    HasTyT svRecordEnv 0 [] (consTower 25 26 [bnatTerm svSup 0, bnatTerm svSup 255])
      (.const 24 []) :=
  bytesTerm_ty svRecordEnv 0 [] svSup 25 26 24 [0, 255] _ svAdmSup_ok rfl rfl rfl

/-- pair — `.p (.i (-1)) (.b 1)` is `mk (mk …) tt` at `SV<pair i64 bool>` (28). -/
def admPairTerm : Expr Nat := .app (.app (.const 29 []) admI64Term) (.const 14 [])

theorem adm_pair_embeds :
    embedValAt svSup svAdmRefOf (.pair .i64 .bool) (.p (.i (-1)) (.b 1)) = some admPairTerm := by
  simp [embedValAt, svAdmRefOf, i64Term, admI64Term, admPairTerm]

def adm_pair_ty : HasTyT svRecordEnv 0 [] admPairTerm (.const 28 []) :=
  .app _ _ _ _ _ (.app _ _ _ _ _ (const_ty svRecordEnv 0 [] 29 _ rfl rfl) adm_i64_ty)
    (const_ty svRecordEnv 0 [] 14 _ rfl rfl)

/-- sum — `.j 1 (.b 1)` is `inj₁ tt` (member 33) at `SV<sum [i64, bool]>` (31). -/
theorem adm_sum_embeds :
    embedValAt svSup svAdmRefOf (.sum [.i64, .bool]) (.j 1 (.b 1)) =
      some (.app (.const 33 []) (.const 14 [])) := by
  simp [embedValAt, svAdmRefOf]

def adm_sum_ty : HasTyT svRecordEnv 0 [] (.app (.const 33 []) (.const 14 [])) (.const 31 []) :=
  .app _ _ _ _ _ (const_ty svRecordEnv 0 [] 33 _ rfl rfl) (const_ty svRecordEnv 0 [] 14 _ rfl rfl)

/-- record — `.r [.i (-1), .b 1]` is `mk (mk …) tt` at `SV<record a:i64 b:bool>` (35). -/
theorem adm_record_embeds :
    embedValAt svSup svAdmRefOf svRecordTy (.r [.i (-1), .b 1]) =
      some (appsp 36 [admI64Term, .const 14 []]) := by
  simp [embedValAt, svAdmRefOf, svRecordTy, i64Term, admI64Term, mapOpt]

def adm_record_ty :
    HasTyT svRecordEnv 0 [] (appsp 36 [admI64Term, .const 14 []]) (.const 35 []) :=
  .app _ _ _ _ _ (.app _ _ _ _ _ (const_ty svRecordEnv 0 [] 36 _ rfl rfl) adm_i64_ty)
    (const_ty svRecordEnv 0 [] 14 _ rfl rfl)

/-! ## `no lit` teeth (rewrite-only, as `RcicG2Pins`' — never evaluate the tower) -/

theorem admI64Term_noLit : hasLit admI64Term = false := by
  rw [admI64Term, hasLit_app, hasLit_const, bnatTerm_noLit]; rfl

/-- a two-element list of literal-free terms. -/
theorem noLit_pair_list {a b : Expr Nat} (ha : hasLit a = false) (hb : hasLit b = false) :
    ∀ e ∈ [a, b], hasLit e = false := fun e he => by
  rcases List.mem_cons.mp he with rfl | he
  · exact ha
  rcases List.mem_cons.mp he with rfl | he
  · exact hb
  exact absurd he (List.not_mem_nil _)

theorem adm_pins_no_lit :
    hasLit admI64Term = false ∧ hasLit (.const 14 [] : Expr Nat) = false ∧
    hasLit (consTower 17 18 [admI64Term]) = false ∧
    hasLit (strTerm svSup 21 22 "ab") = false ∧
    hasLit (consTower 25 26 [bnatTerm svSup 0, bnatTerm svSup 255]) = false ∧
    hasLit admPairTerm = false ∧
    hasLit (.app (.const 33 []) (.const 14 [])) = false ∧
    hasLit (appsp 36 [admI64Term, .const 14 []]) = false :=
  ⟨admI64Term_noLit, hasLit_const 14,
    consTower_noLit 17 18 _ (fun e he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact admI64Term_noLit
      exact absurd he (List.not_mem_nil _)),
    strTerm_noLit svSup 21 22 "ab",
    consTower_noLit 25 26 _ (noLit_pair_list (bnatTerm_noLit svSup 0) (bnatTerm_noLit svSup 255)),
    by rw [admPairTerm, hasLit_app, hasLit_app, hasLit_const, hasLit_const, admI64Term_noLit]; rfl,
    by rw [hasLit_app, hasLit_const, hasLit_const]; rfl,
    appsp_noLit 36 _ (noLit_pair_list admI64Term_noLit (hasLit_const 14))⟩

end Rcic.G2
