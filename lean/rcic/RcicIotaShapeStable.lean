import rcic.RcicIotaShape

namespace Rcic.Declarative

/-- Fail-closed, fuel-bounded closure of the constants an admission computation can meet.
Fuel zero refuses. Every syntactic constant must be an `E` member; for a transparent
member with a body, that body is instantiated at the encountered levels and checked
again with one less unit of fuel. -/
def constsMemberFuel (E : ResolvedEnv) : Nat → Expr Nat → Bool
  | 0, _ => false
  | _ + 1, .bvar _ => true
  | _ + 1, .sort _ => true
  | fuel + 1, .lit t =>
      match t with
      | 0 =>
          match E.members 1 with
          | none => false
          | some m =>
              if transparent m.mclass then
                match m.body with
                | some body => constsMemberFuel E fuel (instantiateLevels [] body)
                | none => true
              else true
      | _ + 1 =>
          (match E.members 2 with
          | none => false
          | some m =>
              if transparent m.mclass then
                match m.body with
                | some body => constsMemberFuel E fuel (instantiateLevels [] body)
                | none => true
              else true) &&
          (match E.members 1 with
          | none => false
          | some m =>
              if transparent m.mclass then
                match m.body with
                | some body => constsMemberFuel E fuel (instantiateLevels [] body)
                | none => true
              else true)
  | fuel + 1, .const r ls =>
      match E.members r with
      | none => false
      | some m =>
          if transparent m.mclass then
            match m.body with
            | some body => constsMemberFuel E fuel (instantiateLevels ls body)
            | none => true
          else true
  | fuel + 1, .app f a =>
      constsMemberFuel E (fuel + 1) f && constsMemberFuel E (fuel + 1) a
  | fuel + 1, .lam A b =>
      constsMemberFuel E (fuel + 1) A && constsMemberFuel E (fuel + 1) b
  | fuel + 1, .pi A b =>
      constsMemberFuel E (fuel + 1) A && constsMemberFuel E (fuel + 1) b
  | fuel + 1, .letE A v b =>
      constsMemberFuel E (fuel + 1) A && constsMemberFuel E (fuel + 1) v &&
        constsMemberFuel E (fuel + 1) b

/-- The finite certificate extracted from a successful closure check. It is not
fuel-indexed: success means every transparent-body branch encountered by the term
ends inside `E`, so computations may reset their own fuel without losing closure. -/
inductive ConstsMemberClosed (E : ResolvedEnv) : Expr Nat → Prop
  | bvar (i : Nat) : ConstsMemberClosed E (.bvar i)
  | sort (l : Level) : ConstsMemberClosed E (.sort l)
  | lit (t : Nat) (h : ConstsMemberClosed E (natExpand t)) :
      ConstsMemberClosed E (.lit t)
  | const (r : Nat) (ls : List Level) (m : CheckedMember)
      (hmem : E.members r = some m)
      (hbody : ∀ body, transparent m.mclass = true → m.body = some body →
        ConstsMemberClosed E (instantiateLevels ls body)) :
      ConstsMemberClosed E (.const r ls)
  | app {f a : Expr Nat} (hf : ConstsMemberClosed E f)
      (ha : ConstsMemberClosed E a) : ConstsMemberClosed E (.app f a)
  | lam {A b : Expr Nat} (hA : ConstsMemberClosed E A)
      (hb : ConstsMemberClosed E b) : ConstsMemberClosed E (.lam A b)
  | pi {A b : Expr Nat} (hA : ConstsMemberClosed E A)
      (hb : ConstsMemberClosed E b) : ConstsMemberClosed E (.pi A b)
  | letE {A v b : Expr Nat} (hA : ConstsMemberClosed E A)
      (hv : ConstsMemberClosed E v) (hb : ConstsMemberClosed E b) :
      ConstsMemberClosed E (.letE A v b)

private theorem constsMemberFuel_litRef {E : ResolvedEnv} {fuel r : Nat}
    (ihFuel : ∀ {e : Expr Nat}, constsMemberFuel E fuel e = true →
        ConstsMemberClosed E e)
    (h : (match E.members r with
          | none => false
          | some m =>
              if transparent m.mclass then
                match m.body with
                | some body => constsMemberFuel E fuel (instantiateLevels [] body)
                | none => true
              else true) = true) :
    ConstsMemberClosed E (.const r []) := by
  cases hm : E.members r with
  | none =>
      simp only [hm] at h
      exact Bool.noConfusion h
  | some m =>
      refine .const r [] m hm ?_
      intro body ht hb
      simp only [hm, ht, ite_true, hb] at h
      exact ihFuel h

private theorem constsMemberFuel_natExpandCMC {E : ResolvedEnv}
    (c2 : ConstsMemberClosed E (.const 2 []))
    (c1 : ConstsMemberClosed E (.const 1 [])) :
    (t : Nat) → ConstsMemberClosed E (natExpand t)
  | 0 => c1
  | t + 1 => .app c2 (constsMemberFuel_natExpandCMC c2 c1 t)

theorem constsMemberFuel_sound (E : ResolvedEnv) {fuel : Nat} {e : Expr Nat}
    (h : constsMemberFuel E fuel e = true) : ConstsMemberClosed E e := by
  induction fuel generalizing e with
  | zero =>
      simp only [constsMemberFuel] at h
      nomatch h
  | succ fuel ihFuel =>
      induction e with
      | bvar i => exact .bvar i
      | sort l => exact .sort l
      | lit t =>
          cases t with
          | zero =>
              simp only [constsMemberFuel] at h
              exact .lit 0 (constsMemberFuel_litRef ihFuel h)
          | succ n =>
              simp only [constsMemberFuel] at h
              rw [Bool.and_eq_true] at h
              have c2 := constsMemberFuel_litRef ihFuel h.1
              have c1 := constsMemberFuel_litRef ihFuel h.2
              exact .lit _ (.app c2 (constsMemberFuel_natExpandCMC c2 c1 n))
      | const r ls =>
          simp only [constsMemberFuel] at h
          cases hm : E.members r with
          | none =>
              simp only [hm] at h
              nomatch h
          | some m =>
              refine .const r ls m hm ?_
              intro body ht hb
              simp only [hm, ht, ite_true, hb] at h
              exact ihFuel h
      | app f a ihf iha =>
          simp only [constsMemberFuel, Bool.and_eq_true] at h
          exact .app (ihf h.1) (iha h.2)
      | lam A b ihA ihb =>
          simp only [constsMemberFuel, Bool.and_eq_true] at h
          exact .lam (ihA h.1) (ihb h.2)
      | pi A b ihA ihb =>
          simp only [constsMemberFuel, Bool.and_eq_true] at h
          exact .pi (ihA h.1) (ihb h.2)
      | letE A v b ihA ihv ihb =>
          simp only [constsMemberFuel, Bool.and_eq_true] at h
          exact .letE (ihA h.1.1) (ihv h.1.2) (ihb h.2)

/-- `constsMemberFuel` is lift-insensitive: `lift` only shifts `.bvar` indices and
    leaves every other head — and every `bvar` stays a `bvar`, which the check accepts
    unconditionally.  So the `lift 0 (1 + nMinors + nindices)` wrapper
    `iotaWitnessStableB`/`iotaWitnessSB` put around `ctorFieldTelRaw` does not
    change the closure check. -/
theorem constsMemberFuel_lift (E : ResolvedEnv) (hi : Nat) :
    ∀ (fuel lo : Nat) (e : Expr Nat),
      constsMemberFuel E fuel (lift lo hi e) = constsMemberFuel E fuel e := by
  intro fuel lo e
  induction e generalizing fuel lo with
  | bvar i =>
      cases fuel with
      | zero => simp only [constsMemberFuel]
      | succ F =>
          rw [lift]
          by_cases h : lo ≤ i <;> simp only [h, if_true, if_false, constsMemberFuel]
  | sort l => cases fuel with
      | zero => simp only [constsMemberFuel]
      | succ _ => rfl
  | lit t => cases fuel with
      | zero => simp only [constsMemberFuel]
      | succ _ => rfl
  | const r ls => cases fuel with
      | zero => simp only [constsMemberFuel]
      | succ _ => rfl
  | app f a ihf iha =>
      cases fuel with
      | zero => simp only [constsMemberFuel]
      | succ F =>
          show constsMemberFuel E (F + 1) (.app (lift lo hi f) (lift lo hi a)) =
            constsMemberFuel E (F + 1) (.app f a)
          simp only [constsMemberFuel, ihf (F + 1) lo, iha (F + 1) lo]
  | lam A b ihA ihb =>
      cases fuel with
      | zero => simp only [constsMemberFuel]
      | succ F =>
          show constsMemberFuel E (F + 1) (.lam (lift lo hi A) (lift (lo + 1) hi b)) =
            constsMemberFuel E (F + 1) (.lam A b)
          simp only [constsMemberFuel, ihA (F + 1) lo, ihb (F + 1) (lo + 1)]
  | pi A b ihA ihb =>
      cases fuel with
      | zero => simp only [constsMemberFuel]
      | succ F =>
          show constsMemberFuel E (F + 1) (.pi (lift lo hi A) (lift (lo + 1) hi b)) =
            constsMemberFuel E (F + 1) (.pi A b)
          simp only [constsMemberFuel, ihA (F + 1) lo, ihb (F + 1) (lo + 1)]
  | letE A v b ihA ihv ihb =>
      cases fuel with
      | zero => simp only [constsMemberFuel]
      | succ F =>
          show constsMemberFuel E (F + 1)
              (.letE (lift lo hi A) (lift lo hi v) (lift (lo + 1) hi b)) =
            constsMemberFuel E (F + 1) (.letE A v b)
          simp only [constsMemberFuel, ihA (F + 1) lo, ihv (F + 1) lo, ihb (F + 1) (lo + 1)]

theorem ConstsMemberClosed.lift {E : ResolvedEnv} {e : Expr Nat}
    (h : ConstsMemberClosed E e) (c a : Nat) :
    ConstsMemberClosed E (lift c a e) := by
  induction h generalizing c with
  | bvar i =>
      by_cases hc : c ≤ i
      · rw [Rcic.Declarative.lift, if_pos hc]
        exact .bvar _
      · rw [Rcic.Declarative.lift, if_neg hc]
        exact .bvar _
  | sort l => exact .sort l
  | lit t hn ihh =>
      exact .lit t (natExpand_lift c a t ▸ ihh c)
  | const r ls m hmem hbody => exact .const r ls m hmem hbody
  | app hf ha ihf iha => exact .app (ihf c) (iha c)
  | lam hA hb ihA ihb => exact .lam (ihA c) (ihb (c + 1))
  | pi hA hb ihA ihb => exact .pi (ihA c) (ihb (c + 1))
  | letE hA hv hb ihA ihv ihb => exact .letE (ihA c) (ihv c) (ihb (c + 1))

theorem ConstsMemberClosed.instantiate {E : ResolvedEnv} {e : Expr Nat}
    (h : ConstsMemberClosed E e) (j : Nat) {v : Expr Nat}
    (hv : ConstsMemberClosed E v) : ConstsMemberClosed E (instantiate j v e) := by
  induction h generalizing j v with
  | bvar i =>
      by_cases hij : i = j
      · rw [Rcic.Declarative.instantiate, if_pos hij]
        exact hv
      · rw [Rcic.Declarative.instantiate, if_neg hij]
        split <;> exact .bvar _
  | sort l => exact .sort l
  | lit t hn ihh =>
      exact .lit t (natExpand_instantiate j v t ▸ ihh j hv)
  | const r ls m hmem hbody => exact .const r ls m hmem hbody
  | app hf ha ihf iha => exact .app (ihf j hv) (iha j hv)
  | lam hA hb ihA ihb =>
      exact .lam (ihA j hv) (ihb (j + 1) (hv.lift 0 1))
  | pi hA hb ihA ihb =>
      exact .pi (ihA j hv) (ihb (j + 1) (hv.lift 0 1))
  | letE hA hx hb ihA ihx ihb =>
      exact .letE (ihA j hv) (ihx j hv) (ihb (j + 1) (hv.lift 0 1))

theorem ConstsMemberClosed.ext {E E' : ResolvedEnv} {e : Expr Nat}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (h : ConstsMemberClosed E e) : ConstsMemberClosed E' e := by
  induction h with
  | bvar i => exact .bvar i
  | sort l => exact .sort l
  | lit t hn ihh => exact .lit t ihh
  | const r ls m hmem hbody ihbody =>
      exact .const r ls m (hext r m hmem) ihbody
  | app hf ha ihf iha => exact .app ihf iha
  | lam hA hb ihA ihb => exact .lam ihA ihb
  | pi hA hb ihA ihb => exact .pi ihA ihb
  | letE hA hv hb ihA ihv ihb => exact .letE ihA ihv ihb

private theorem transparentBody_ext_of_closed {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    {r : Nat} {ls : List Level} (h : ConstsMemberClosed E (.const r ls)) :
    transparentBody E' r ls = transparentBody E r ls := by
  cases h with
  | const _ _ m hmem _ =>
      unfold transparentBody
      rw [hmem, hext r m hmem]

private theorem closed_of_transparentBody {E : ResolvedEnv} {r : Nat}
    {ls : List Level} {body : Expr Nat}
    (h : ConstsMemberClosed E (.const r ls))
    (hb : transparentBody E r ls = some body) : ConstsMemberClosed E body := by
  cases h with
  | const _ _ m hmem hbody =>
      unfold transparentBody at hb
      rw [hmem] at hb
      by_cases ht : transparent m.mclass = true
      · simp only [ht, ite_true] at hb
        cases hm : m.body with
        | none =>
            simp only [hm] at hb
            nomatch hb
        | some raw =>
            simp only [hm] at hb
            cases hb
            exact hbody raw ht hm
      · simp only [ht, ite_false] at hb
        nomatch hb

private theorem ConstsMemberClosed.foldApps {E : ResolvedEnv} {f : Expr Nat}
    (hf : ConstsMemberClosed E f) {args : List (Expr Nat)}
    (ha : ∀ a ∈ args, ConstsMemberClosed E a) :
    ConstsMemberClosed E (foldApps f args) := by
  induction args generalizing f with
  | nil => exact hf
  | cons a args ih =>
      apply ih (.app hf (ha a (by simp)))
      intro x hx
      exact ha x (by simp [hx])

private theorem closed_appsSpine {E : ResolvedEnv} {e : Expr Nat}
    (h : ConstsMemberClosed E e) :
    ConstsMemberClosed E (appsSpine e).1 ∧
      ∀ a ∈ (appsSpine e).2, ConstsMemberClosed E a := by
  induction h with
  | app hf ha ihf iha =>
      simp only [appsSpine]
      constructor
      · exact ihf.1
      · intro a hx
        rw [List.mem_append] at hx
        cases hx with
        | inl hx => exact ihf.2 a hx
        | inr hx =>
            simp only [List.mem_singleton] at hx
            subst a
            exact ha
  | bvar i => exact ⟨.bvar i, by simp [appsSpine]⟩
  | sort l => exact ⟨.sort l, by simp [appsSpine]⟩
  | lit t hn => exact ⟨.lit t hn, by simp [appsSpine]⟩
  | const r ls m hmem hbody =>
      exact ⟨.const r ls m hmem hbody, by simp [appsSpine]⟩
  | lam hA hb ihA ihb => exact ⟨.lam hA hb, by simp [appsSpine]⟩
  | pi hA hb ihA ihb => exact ⟨.pi hA hb, by simp [appsSpine]⟩
  | letE hA hv hb ihA ihv ihb => exact ⟨.letE hA hv hb, by simp [appsSpine]⟩

private theorem whnfFuel_ext_closed {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    ∀ fuel e, ConstsMemberClosed E e → whnfFuel E' fuel e = whnfFuel E fuel e := by
  intro fuel
  induction fuel with
  | zero =>
      intro e h
      rfl
  | succ fuel ih =>
      intro e h
      cases hsp : appsSpine e with
      | mk head args =>
          have hs := closed_appsSpine h
          simp only [hsp] at hs
          cases head with
          | lam A b =>
              cases args with
              | nil => simp only [whnfFuel, hsp]
              | cons a rest =>
                  simp only [whnfFuel, hsp]
                  cases hs.1 with
                  | lam hA hb =>
                      apply ih
                      apply (hb.instantiate 0 (hs.2 a (by simp))).foldApps
                      intro x hx
                      exact hs.2 x (by simp [hx])
          | letE A v b =>
              simp only [whnfFuel, hsp]
              cases hs.1 with
              | letE hA hv hb =>
                  apply ih
                  exact (hb.instantiate 0 hv).foldApps hs.2
          | const r ls =>
              have htb := transparentBody_ext_of_closed hext hs.1
              simp only [whnfFuel, hsp, htb]
              cases hb : transparentBody E r ls with
              | none => rfl
              | some body =>
                  simp only [hb]
                  apply ih
                  exact (closed_of_transparentBody hs.1 hb).foldApps hs.2
          | bvar _ | sort _ | app _ _ | pi _ _ | lit _ =>
              simp only [whnfFuel, hsp]

theorem whnfFuel_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    {fuel : Nat} {e : Expr Nat}
    (hclosed : constsMemberFuel E (fuel + 1) e = true) :
    whnfFuel E' fuel e = whnfFuel E fuel e :=
  whnfFuel_ext_closed hext fuel e (constsMemberFuel_sound E hclosed)

private theorem closed_of_whnfFuel {E : ResolvedEnv} :
    ∀ fuel e w, ConstsMemberClosed E e → whnfFuel E fuel e = some w →
      ConstsMemberClosed E w := by
  intro fuel
  induction fuel with
  | zero =>
      intro e w h hw
      simp only [whnfFuel] at hw
      nomatch hw
  | succ fuel ih =>
      intro e w h hw
      cases hsp : appsSpine e with
      | mk head args =>
          have hs := closed_appsSpine h
          simp only [hsp] at hs
          cases head with
          | lam A b =>
              cases args with
              | nil =>
                  simp only [whnfFuel, hsp] at hw
                  cases hw
                  exact h
              | cons a rest =>
                  simp only [whnfFuel, hsp] at hw
                  cases hs.1 with
                  | lam hA hb =>
                      apply ih _ _ ((hb.instantiate 0 (hs.2 a (by simp))).foldApps ?_) hw
                      intro x hx
                      exact hs.2 x (by simp [hx])
          | letE A v b =>
              simp only [whnfFuel, hsp] at hw
              cases hs.1 with
              | letE hA hv hb => exact ih _ _ ((hb.instantiate 0 hv).foldApps hs.2) hw
          | const r ls =>
              simp only [whnfFuel, hsp] at hw
              cases hb : transparentBody E r ls with
              | none =>
                  simp only [hb] at hw
                  cases hw
                  exact h
              | some body =>
                  simp only [hb] at hw
                  exact ih _ _ ((closed_of_transparentBody hs.1 hb).foldApps hs.2) hw
          | bvar _ | sort _ | app _ _ | pi _ _ | lit _ =>
              simp only [whnfFuel, hsp] at hw
              cases hw
              exact h

private theorem containsFamilyFuel_ext_closed {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fam : Nat) : ∀ fuel e, ConstsMemberClosed E e →
      containsFamilyFuel E' fam fuel e = containsFamilyFuel E fam fuel e := by
  intro fuel
  induction fuel with
  | zero => intro e h; rfl
  | succ fuel ih =>
      intro e h
      cases h with
      | bvar _ | sort _ => rfl
      | lit t hexp =>
          cases t with
          | zero => exact ih _ hexp
          | succ n =>
              have hleaf : ∀ {k : Nat}, ConstsMemberClosed E (natExpand k) →
                  ConstsMemberClosed E litZero := by
                intro k hk
                induction k with
                | zero => exact hk
                | succ k ihk =>
                    cases hk with
                    | app _ hrest => exact ihk hrest
              cases hexp with
              | app hf2 hrest =>
                  have h2 := ih _ hf2
                  have h1 := ih _ (hleaf hrest)
                  show (match containsFamilyFuel E' fam fuel (.const 2 []) with
                        | some false =>
                            containsFamilyFuel E' fam fuel litZero
                        | r => r) =
                      (match containsFamilyFuel E fam fuel (.const 2 []) with
                        | some false =>
                            containsFamilyFuel E fam fuel litZero
                        | r => r)
                  rw [h2]
                  cases containsFamilyFuel E fam fuel (.const 2 []) with
                  | none => rfl
                  | some b =>
                      cases b with
                      | false => exact h1
                      | true => rfl
      | const r ls m hmem hbody =>
          by_cases hr : r = fam
          · simp only [containsFamilyFuel, hr, ite_true]
          · have hc : ConstsMemberClosed E (.const r ls) := .const r ls m hmem hbody
            have htb := transparentBody_ext_of_closed hext hc
            simp only [containsFamilyFuel, hr, ite_false, htb]
            cases hb : transparentBody E r ls with
            | none => rfl
            | some body =>
                simp only [hb]
                exact ih body (closed_of_transparentBody hc hb)
      | app hf ha =>
          simp only [containsFamilyFuel, ih _ hf, ih _ ha]
      | lam hA hb =>
          simp only [containsFamilyFuel, ih _ hA, ih _ hb]
      | pi hA hb =>
          simp only [containsFamilyFuel, ih _ hA, ih _ hb]
      | letE hA hv hb =>
          simp only [containsFamilyFuel, ih _ hA, ih _ hv, ih _ hb]

theorem containsFamilyFuel_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fam : Nat) {fuel : Nat} {e : Expr Nat}
    (hclosed : constsMemberFuel E (fuel + 1) e = true) :
    containsFamilyFuel E' fam fuel e = containsFamilyFuel E fam fuel e :=
  containsFamilyFuel_ext_closed hext fam fuel e (constsMemberFuel_sound E hclosed)

private theorem piTelescopeFuel_ext_closed {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m) :
    ∀ fuel e, ConstsMemberClosed E e →
      piTelescopeFuel E' fuel e = piTelescopeFuel E fuel e := by
  intro fuel
  induction fuel with
  | zero => intro e h; rfl
  | succ fuel ih =>
      intro e h
      simp only [piTelescopeFuel]
      rw [whnfFuel_ext_closed hext fuel e h]
      cases hw : whnfFuel E fuel e with
      | none => rfl
      | some w =>
          have hc := closed_of_whnfFuel fuel e w h hw
          cases w with
          | pi A B =>
              cases hc with
              | pi hA hB =>
                  simp only
                  rw [ih B hB]
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ => rfl

theorem piTelescopeFuel_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    {fuel : Nat} {e : Expr Nat}
    (hclosed : constsMemberFuel E (fuel + 1) e = true) :
    piTelescopeFuel E' fuel e = piTelescopeFuel E fuel e :=
  piTelescopeFuel_ext_closed hext fuel e (constsMemberFuel_sound E hclosed)

private theorem domainsContainFuel_ext_closed {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fam : Nat) : ∀ fuel es, (∀ e ∈ es, ConstsMemberClosed E e) →
      domainsContainFuel E' fam fuel es = domainsContainFuel E fam fuel es := by
  intro fuel
  induction fuel with
  | zero => intro es h; cases es <;> rfl
  | succ fuel ih =>
      intro es h
      cases es with
      | nil => rfl
      | cons A As =>
          simp only [domainsContainFuel]
          rw [containsFamilyFuel_ext_closed hext fam fuel A (h A (by simp))]
          cases hc : containsFamilyFuel E fam fuel A with
          | none => rfl
          | some b =>
              cases b with
              | false => rw [ih As (fun e he => h e (by simp [he]))]
              | true => rfl

theorem domainsContainFuel_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fam : Nat) {fuel : Nat} {es : List (Expr Nat)}
    (hclosed : ∀ e ∈ es, constsMemberFuel E (fuel + 1) e = true) :
    domainsContainFuel E' fam fuel es = domainsContainFuel E fam fuel es :=
  domainsContainFuel_ext_closed hext fam fuel es
    (fun e he => constsMemberFuel_sound E (hclosed e he))

private theorem indicesCleanFuel_ext_closed {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fam : Nat) : ∀ fuel es, (∀ e ∈ es, ConstsMemberClosed E e) →
      indicesCleanFuel E' fam fuel es = indicesCleanFuel E fam fuel es := by
  intro fuel
  induction fuel with
  | zero => intro es h; cases es <;> rfl
  | succ fuel ih =>
      intro es h
      cases es with
      | nil => rfl
      | cons A As =>
          simp only [indicesCleanFuel]
          rw [containsFamilyFuel_ext_closed hext fam fuel A (h A (by simp))]
          cases hc : containsFamilyFuel E fam fuel A with
          | none => rfl
          | some b =>
              cases b with
              | false => rw [ih As (fun e he => h e (by simp [he]))]
              | true => rfl

theorem indicesCleanFuel_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fam : Nat) {fuel : Nat} {es : List (Expr Nat)}
    (hclosed : ∀ e ∈ es, constsMemberFuel E (fuel + 1) e = true) :
    indicesCleanFuel E' fam fuel es = indicesCleanFuel E fam fuel es :=
  indicesCleanFuel_ext_closed hext fam fuel es
    (fun e he => constsMemberFuel_sound E (hclosed e he))

private theorem properFamilyFuel_ext_closed {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    {fuel fam nuniv nparams nindices top : Nat} {body : Expr Nat}
    (h : ConstsMemberClosed E body) :
    properFamilyFuel E' fuel fam nuniv nparams nindices top body =
      properFamilyFuel E fuel fam nuniv nparams nindices top body := by
  simp only [properFamilyFuel]
  cases hsp : appsSpine body with
  | mk head args =>
      have hs := closed_appsSpine h
      simp only [hsp] at hs
      cases head with
      | const r ls =>
          by_cases hshape : r = fam && args.length = nparams + nindices &&
              exactParamLocals (args.take nparams) top &&
              ls = (List.range nuniv).map Level.param
          · simp only [hshape, ite_true]
            rw [indicesCleanFuel_ext_closed hext fam fuel (args.drop nparams)]
            intro e he
            exact hs.2 e (List.mem_of_mem_drop he)
          · simp only [hshape, Bool.false_eq_true, if_false]
      | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ | letE _ _ _ | lit _ => rfl

theorem properFamilyFuel_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    {fuel fam nuniv nparams nindices top : Nat} {body : Expr Nat}
    (hclosed : constsMemberFuel E (fuel + 1) body = true) :
    properFamilyFuel E' fuel fam nuniv nparams nindices top body =
      properFamilyFuel E fuel fam nuniv nparams nindices top body :=
  properFamilyFuel_ext_closed hext (constsMemberFuel_sound E hclosed)

private theorem closed_of_piTelescopeFuel {E : ResolvedEnv} :
    ∀ fuel e ds body, ConstsMemberClosed E e →
      piTelescopeFuel E fuel e = some (ds, body) →
      (∀ A ∈ ds, ConstsMemberClosed E A) ∧ ConstsMemberClosed E body := by
  intro fuel
  induction fuel with
  | zero =>
      intro e ds body h hp
      simp only [piTelescopeFuel] at hp
      nomatch hp
  | succ fuel ih =>
      intro e ds body h hp
      simp only [piTelescopeFuel] at hp
      cases hw : whnfFuel E fuel e with
      | none =>
          simp only [hw] at hp
          nomatch hp
      | some w =>
          simp only [hw] at hp
          have hc := closed_of_whnfFuel fuel e w h hw
          cases w with
          | pi A B =>
              cases hc with
              | pi hA hB =>
                  cases ht : piTelescopeFuel E fuel B with
                  | none =>
                      simp only [ht] at hp
                      nomatch hp
                  | some pr =>
                      cases pr with
                      | mk ds' resultBody =>
                          have hi := ih B ds' resultBody hB ht
                          simp only [ht] at hp
                          cases hp
                          exact ⟨fun x hx => by
                            simp only [List.mem_cons] at hx
                            cases hx with
                            | inl hx => simpa [hx] using hA
                            | inr hx => exact hi.1 x hx,
                            hi.2⟩
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              cases hp
              exact ⟨by simp, hc⟩

private theorem fieldAnalyze_ext_closed {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    {fuel fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    (hT : ConstsMemberClosed E T) :
    fieldAnalyze E' fuel fam nuniv nparams nindices depth T =
      fieldAnalyze E fuel fam nuniv nparams nindices depth T := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [fieldAnalyze]
      rw [piTelescopeFuel_ext_closed hext fuel T hT]
      cases hp : piTelescopeFuel E fuel T with
      | none => rfl
      | some pr =>
          cases pr with
          | mk doms body =>
              have hc := closed_of_piTelescopeFuel fuel T doms body hT hp
              simp only
              rw [domainsContainFuel_ext_closed hext fam fuel doms hc.1]
              cases hd : domainsContainFuel E fam fuel doms with
              | none => rfl
              | some bdom =>
                  cases bdom with
                  | true => rfl
                  | false =>
                      rw [properFamilyFuel_ext_closed hext hc.2]
                      cases hproper : properFamilyFuel E fuel fam nuniv nparams nindices
                          (doms.length + depth - 1) body with
                      | none => rfl
                      | some bproper =>
                          cases bproper with
                          | true => rfl
                          | false =>
                              rw [containsFamilyFuel_ext_closed hext fam fuel T hT]
                              cases hcontains : containsFamilyFuel E fam fuel T with
                              | none => rfl
                              | some bcontains =>
                                  cases bcontains with
                                  | false => rfl
                                  | true =>
                                      cases hsp : appsSpine body with
                                      | mk head args =>
                                          cases head with
                                          | const r ls =>
                                              by_cases hr : r = fam
                                              · simp only [hsp, hr, if_pos]
                                              · simp only [hsp, hr, if_neg]
                                                have hs := closed_appsSpine hc.2
                                                simp only [hsp] at hs
                                                rw [domainsContainFuel_ext_closed hext fam fuel args hs.2]
                                          | bvar _ | sort _ | app _ _ | lam _ _ | pi _ _ |
                                              letE _ _ _ | lit _ => rfl

theorem fieldAnalyze_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    {fuel fam nuniv nparams nindices depth : Nat} {T : Expr Nat}
    (hclosed : constsMemberFuel E (fuel + 1) T = true) :
    fieldAnalyze E' fuel fam nuniv nparams nindices depth T =
      fieldAnalyze E fuel fam nuniv nparams nindices depth T :=
  fieldAnalyze_ext_closed hext (constsMemberFuel_sound E hclosed)

private theorem fieldShapesFuel_ext_closed {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fuel fam nuniv nparams nindices : Nat) :
    ∀ depth Ts, (∀ T ∈ Ts, ConstsMemberClosed E T) →
      fieldShapesFuel E' fuel fam nuniv nparams nindices depth Ts =
        fieldShapesFuel E fuel fam nuniv nparams nindices depth Ts := by
  intro depth Ts hTs
  induction Ts generalizing depth with
  | nil => rfl
  | cons T Ts ih =>
      simp only [fieldShapesFuel]
      rw [fieldAnalyze_ext_closed hext (hTs T (by simp))]
      cases ha : fieldAnalyze E fuel fam nuniv nparams nindices depth T with
      | permitted shape indices =>
          rw [ih (depth + 1) (fun e he => hTs e (by simp [he]))]
      | refused why | unresolved => rfl

theorem fieldShapesFuel_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    {fuel fam nuniv nparams nindices depth : Nat} {Ts : List (Expr Nat)}
    (hclosed : ∀ T ∈ Ts, constsMemberFuel E (fuel + 1) T = true) :
    fieldShapesFuel E' fuel fam nuniv nparams nindices depth Ts =
      fieldShapesFuel E fuel fam nuniv nparams nindices depth Ts :=
  fieldShapesFuel_ext_closed hext fuel fam nuniv nparams nindices depth Ts
    (fun T hT => constsMemberFuel_sound E (hclosed T hT))

private theorem funRecArg_ext_closed {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fuel : Nat) (rec : Expr Nat) (preMajor : List (Expr Nat))
    (nparams nMinors : Nat) (f A : Expr Nat) (inner : Nat)
    (hA : ConstsMemberClosed E A) :
    funRecArg E' fuel rec preMajor nparams nMinors f A inner =
      funRecArg E fuel rec preMajor nparams nMinors f A inner := by
  simp only [funRecArg]
  rw [piTelescopeFuel_ext_closed hext fuel A hA]

theorem funRecArg_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fuel : Nat) (rec : Expr Nat) (preMajor : List (Expr Nat))
    (nparams nMinors : Nat) (f A : Expr Nat) (inner : Nat)
    (hclosed : constsMemberFuel E (fuel + 1) A = true) :
    funRecArg E' fuel rec preMajor nparams nMinors f A inner =
      funRecArg E fuel rec preMajor nparams nMinors f A inner :=
  funRecArg_ext_closed hext fuel rec preMajor nparams nMinors f A inner
    (constsMemberFuel_sound E hclosed)

private theorem iotaArgs_ext_closed {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fuel : Nat) (rec : Expr Nat) (preMajor : List (Expr Nat))
    (nparams nMinors : Nat) :
    ∀ shapes fields tel, (∀ f ∈ fields, ConstsMemberClosed E f) →
      ConstsMemberClosed E tel →
      iotaArgs E' fuel rec preMajor nparams nMinors shapes fields tel =
        iotaArgs E fuel rec preMajor nparams nMinors shapes fields tel := by
  intro shapes fields tel hfields htel
  induction shapes generalizing fields tel with
  | nil => cases fields <;> cases tel <;> rfl
  | cons shape shapes ih =>
      cases fields with
      | nil =>
          cases shape with
          | nonrecursive => cases tel <;> simp only [iotaArgs]
          | recursive inner => cases inner <;> cases tel <;> simp only [iotaArgs]
      | cons f fs =>
          cases tel with
          | bvar _ | sort _ | const _ _ | app _ _ | lam _ _ | letE _ _ _ | lit _ =>
              cases shape <;> simp only [iotaArgs]
          | pi A B =>
              cases htel with
              | pi hA hB =>
                  have hf := hfields f (by simp)
                  have hfs : ∀ x ∈ fs, ConstsMemberClosed E x :=
                    fun x hx => hfields x (by simp [hx])
                  have hnext := hB.instantiate 0 hf
                  cases shape with
                  | nonrecursive =>
                      simp only [iotaArgs]
                      rw [ih fs (instantiate0 f B) hfs hnext]
                  | recursive inner =>
                      cases inner with
                      | zero =>
                          simp only [iotaArgs]
                          rw [piTelescopeFuel_ext_closed hext fuel A hA]
                          cases hp : piTelescopeFuel E fuel A with
                          | none => rfl
                          | some pr =>
                              cases pr with
                              | mk doms famApp =>
                                  cases doms with
                                  | nil => rw [ih fs (instantiate0 f B) hfs hnext]
                                  | cons d ds => rfl
                      | succ inner =>
                          simp only [iotaArgs]
                          rw [funRecArg_ext_closed hext fuel rec preMajor nparams nMinors
                            f A (inner + 1) hA]
                          cases hc : funRecArg E fuel rec preMajor nparams nMinors f A
                              (inner + 1) with
                          | none => rfl
                          | some call => rw [ih fs (instantiate0 f B) hfs hnext]

theorem iotaArgs_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fuel : Nat) (rec : Expr Nat) (preMajor : List (Expr Nat))
    (nparams nMinors : Nat) (shapes : List FieldShape)
    (fields : List (Expr Nat)) (tel : Expr Nat)
    (hfields : ∀ f ∈ fields, constsMemberFuel E (fuel + 1) f = true)
    (htel : constsMemberFuel E (fuel + 1) tel = true) :
    iotaArgs E' fuel rec preMajor nparams nMinors shapes fields tel =
      iotaArgs E fuel rec preMajor nparams nMinors shapes fields tel :=
  iotaArgs_ext_closed hext fuel rec preMajor nparams nMinors shapes fields tel
    (fun f hf => constsMemberFuel_sound E (hfields f hf))
    (constsMemberFuel_sound E htel)

theorem iotaOpenRhs_ext {E E' : ResolvedEnv}
    (hext : ∀ r m, E.members r = some m → E'.members r = some m)
    (fuel : Nat) (rec minor : Expr Nat) (preMajor : List (Expr Nat))
    (nparams nMinors : Nat) (shapes : List FieldShape)
    (fields : List (Expr Nat)) (tel : Expr Nat)
    (hfields : ∀ f ∈ fields, constsMemberFuel E (fuel + 1) f = true)
    (htel : constsMemberFuel E (fuel + 1) tel = true) :
    iotaOpenRhs E' fuel rec minor preMajor nparams nMinors shapes fields tel =
      iotaOpenRhs E fuel rec minor preMajor nparams nMinors shapes fields tel := by
  simp only [iotaOpenRhs]
  rw [iotaArgs_ext hext fuel rec preMajor nparams nMinors shapes fields tel
    hfields htel]

/-- Decidable sufficient condition for the field-analysis and schema inputs to be
closed under transparent unfolding in the witness environment. -/
def iotaWitnessStableB (E : ResolvedEnv) (fuel : Nat)
    (fieldDoms fields : List (Expr Nat)) (tel : Expr Nat) : Bool :=
  fieldDoms.all (constsMemberFuel E (fuel + 1)) &&
    fields.all (constsMemberFuel E (fuel + 1)) &&
    constsMemberFuel E (fuel + 1) tel

/-- A successful closure check supplies exactly `IotaWitnessS.hstable`: every
environment extension computes the same admission field shapes and open ι schema. -/
theorem iotaWitnessS_hstable_of_constsMemberFuel
    {E : ResolvedEnv} {fuel familyRef nuniv nparams nindices depth : Nat}
    {fieldDoms : List (Expr Nat)} {shapes : List FieldShape}
    {rec minor : Expr Nat} {preMajor fields : List (Expr Nat)}
    {nMinors : Nat} {tel schema : Expr Nat}
    (hshapes : fieldShapesFuel E fuel familyRef nuniv nparams nindices depth
      fieldDoms = some shapes)
    (hschema : iotaOpenRhs E fuel rec minor preMajor nparams nMinors shapes
      fields tel = some schema)
    (hcheck : iotaWitnessStableB E fuel fieldDoms fields tel = true) :
    ∀ E', (∀ r m, E.members r = some m → E'.members r = some m) →
      fieldShapesFuel E' fuel familyRef nuniv nparams nindices depth
          fieldDoms = some shapes ∧
        iotaOpenRhs E' fuel rec minor preMajor nparams nMinors shapes
          fields tel = some schema := by
  simp only [iotaWitnessStableB, Bool.and_eq_true, List.all_eq_true] at hcheck
  intro E' hext
  constructor
  · rw [fieldShapesFuel_ext hext hcheck.1.1]
    exact hshapes
  · rw [iotaOpenRhs_ext hext fuel rec minor preMajor nparams nMinors shapes
      fields tel hcheck.1.2 hcheck.2]
    exact hschema

end Rcic.Declarative
