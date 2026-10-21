import rcic.RcicTypedJ

/-!
# A certified syntactic checker for the typed judgment

`checkT` reads the typed judgment's rules off a term: no reduction, no conversion, a numeral through its
expansion. Its answer carries the derivation, so it is sound by construction. `synCheck` compares the
type it finds with the one asked for, as written.

W-2 (b-0) and W-3 wrote these in `RcicTypedScopeCheck`. They sit here, on the typed judgment alone, so
the typed environment judgment's pins can discharge a typing by evaluation: since R-NoFunRec-1 step 0,
`IndGroupTypedT` asks for each ι equation's typing (`IotaEquationTypedT`).
-/

namespace Rcic.Declarative

/-- the constant rule read off a reference. -/
def checkConstT (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (r : Nat) (ls : List Level) :
    Option (Σ T, HasTyT E n Γ (.const r ls) T) :=
  match h : E.members r with
  | some m =>
      if hlen : ls.length = m.arity then
        if hwf : levelsBounded n ls = true then some ⟨_, .const Γ r ls m h hlen hwf⟩ else none
      else none
  | none => none

/-- a literal's expansion `succ^t zero` typed (the profile's `zero` and `succ` at `1` and `2`), each
    `succ`'s argument at its domain as written. -/
def checkLitT (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : (t : Nat) → Option (Σ T, HasTyT E n Γ (natExpand t) T)
  | 0 => checkConstT E n Γ 1 []
  | t + 1 =>
      match checkConstT E n Γ 2 [], checkLitT E n Γ t with
      | some ⟨.pi A B, df⟩, some ⟨A', da⟩ =>
          if h : A' = A then some ⟨_, .app Γ (.const 2 []) (natExpand t) A B df (h ▸ da)⟩ else none
      | _, _ => none

/-- the typed judgment's rules read off the term: no reduction, no conversion; a literal through its
    expansion (`HasTyT.lit`). The answer carries its derivation, so the checker is sound by construction. -/
def checkT (E : ResolvedEnv) (n : Nat) : (Γ : LCtx) → (e : Expr Nat) → Option (Σ T, HasTyT E n Γ e T)
  | Γ, .sort l => some ⟨_, .sort Γ l⟩
  | Γ, .bvar i =>
      match h : lookupType Γ i with
      | some A => some ⟨A, .bvar Γ i A h⟩
      | none => none
  | Γ, .const r ls => checkConstT E n Γ r ls
  | Γ, .pi A B =>
      match checkT E n Γ A, checkT E n (.assumption A :: Γ) B with
      | some ⟨.sort u, dA⟩, some ⟨.sort v, dB⟩ => some ⟨_, .pi Γ A u B v dA dB⟩
      | _, _ => none
  | Γ, .lam A b =>
      match checkT E n Γ A, checkT E n (.assumption A :: Γ) b with
      | some ⟨.sort u, dA⟩, some ⟨B, db⟩ => some ⟨_, .lam Γ A u b B dA db⟩
      | _, _ => none
  | Γ, .app f a =>
      match checkT E n Γ f, checkT E n Γ a with
      | some ⟨.pi A B, df⟩, some ⟨A', da⟩ =>
          if h : A' = A then some ⟨_, .app Γ f a A B df (h ▸ da)⟩ else none
      | _, _ => none
  | Γ, .letE A v b =>
      match checkT E n Γ A, checkT E n Γ v, checkT E n (.letBinding A v :: Γ) b with
      | some ⟨.sort u, dA⟩, some ⟨A', dv⟩, some ⟨B, db⟩ =>
          if h : A' = A then some ⟨_, .letE Γ A u v B b dA (h ▸ dv) db⟩ else none
      | _, _, _ => none
  | Γ, .lit t => (checkLitT E n Γ t).map fun p => ⟨p.1, .lit Γ t p.1 p.2⟩

/-- the checker's type. -/
def inferT (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e : Expr Nat) : Option (Expr Nat) :=
  (checkT E n Γ e).map Sigma.fst

/-- the checker's answer is a typing. -/
def hasTyT_of_inferT {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (h : inferT E n Γ e = some T) : HasTyT E n Γ e T :=
  match hc : checkT E n Γ e with
  | some ⟨T', d⟩ => by
      have h' : some T' = some T := by rw [← h, inferT, hc]; rfl
      exact (Option.some.inj h') ▸ d
  | none => by
      have h' : (none : Option (Expr Nat)) = some T := by rw [← h, inferT, hc]; rfl
      exact absurd h' (fun h => Option.noConfusion h)

/-- the syntactic checker's type against the one asked for, compared as written. -/
def synCheck (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e T : Expr Nat) : Option (HasTyT E n Γ e T) :=
  match checkT E n Γ e with
  | some ⟨T', d⟩ => if h : T' = T then some (h ▸ d) else none
  | none => none

end Rcic.Declarative

#print axioms Rcic.Declarative.checkConstT
#print axioms Rcic.Declarative.checkLitT
#print axioms Rcic.Declarative.checkT
#print axioms Rcic.Declarative.hasTyT_of_inferT
#print axioms Rcic.Declarative.synCheck
