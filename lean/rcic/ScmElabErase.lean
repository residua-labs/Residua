/-
RCIC 06 §8 — elaboration is faithful: an elaborated intrinsic
expression erases back to the raw expression it came from (#6029 K3,
segment 5).

Owner text: 06 §19 "intrinsic program/config/outcome → bound canonical wire
object"; 06 §17 "Accepted bytes re-encode exactly". The raw expression is
the first-order form the core wire serializes (`ScmWire.encExpr`) and the
raw machine runs. `elabE_erase`: if `elabE` accepts `e` at some type, the
intrinsic expression it returns erases to `e` exactly — elaboration neither
invents nor drops structure. This is what lets the intrinsic machine's
configurations erase to the raw machine's (the step simulation, a later
segment).
-/
import rcic.ScmErase

namespace Rcic.Scm.ElabErase
open Rcic.Scm

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => exact Except.noConfusion h
  | ok a => exact ⟨a, rfl, h⟩

theorem tyErr_ne_ok {α : Type} {c : String} {y : α} (h : (tyErr c : Except String α) = .ok y) : False :=
  Except.noConfusion h

variable {S : Sig}

theorem erase_cast {Γ : List CoreTy} {T T' : CoreTy} (h : T = T') (e : CoreExpr S Γ T) :
    (h ▸ e : CoreExpr S Γ T').erase = e.erase := by
  subst h; rfl

theorem elabListWith_erase {Γ : List CoreTy} (g : RawExpr → Elab S Γ)
    (hg : ∀ e r, g e = .ok r → r.2.erase = e) :
    ∀ (es : List RawExpr) (xs : List (Σ T, CoreExpr S Γ T)), elabListWith g es = .ok xs →
      xs.map (fun x => x.2.erase) = es
  | [], xs, h => by
      have e : xs = [] := (Except.ok.inj h).symm
      subst e; rfl
  | e :: es, xs, h => by
      obtain ⟨x, hx, h⟩ := bind_ok h
      obtain ⟨rest, hrest, h⟩ := bind_ok h
      have ex := (Except.ok.inj h).symm
      subst ex
      show x.2.erase :: rest.map (fun x => x.2.erase) = e :: es
      rw [hg e x hx, elabListWith_erase g hg es rest hrest]

theorem toArgs_erase {Γ : List CoreTy} :
    ∀ (xs : List (Σ T, CoreExpr S Γ T)) (ps : List CoreTy) (as : Args S Γ ps),
    toArgs xs ps = some as → as.erase = xs.map (fun x => x.2.erase)
  | [], [], as, h => by
      have e := (Option.some.inj h).symm; subst e; rfl
  | ⟨T, e⟩ :: xs, p :: ps, as, h => by
      unfold toArgs at h
      split at h
      · rename_i hT
        cases hr : toArgs xs ps with
        | none => rw [hr] at h; exact Option.noConfusion h
        | some rest =>
          rw [hr] at h
          have ea := (Option.some.inj h).symm; subst ea; subst hT
          show e.erase :: rest.erase = e.erase :: xs.map (fun x => x.2.erase)
          rw [toArgs_erase xs ps rest hr]
      · exact Option.noConfusion h
  | [], _ :: _, _, h => Option.noConfusion h
  | _ :: _, [], _, h => Option.noConfusion h

theorem elabBranchesWith_erase (g : (Γ' : List CoreTy) → RawExpr → Elab S Γ')
    (hg : ∀ Γ' e r, g Γ' e = .ok r → r.2.erase = e) (Γ : List CoreTy) (T : CoreTy) :
    ∀ (ts : List CoreTy) (bs : List RawExpr) (out : Branches S Γ ts T),
    elabBranchesWith g Γ T ts bs = .ok out → out.erase = bs
  | [], [], out, h => by
      have e := (Except.ok.inj h).symm; subst e; rfl
  | A :: ts, b :: bs, out, h => by
      obtain ⟨⟨T', eb⟩, hb, h⟩ := bind_ok h
      dsimp only at h
      split at h
      · rename_i hT
        obtain ⟨rest, hrest, h⟩ := bind_ok h
        have e := (Except.ok.inj h).symm; subst e; subst hT
        show eb.erase :: rest.erase = b :: bs
        rw [hg (A :: Γ) b ⟨T', eb⟩ hb, elabBranchesWith_erase g hg Γ T' ts bs rest hrest]
      · exact (tyErr_ne_ok h).elim
  | [], _ :: _, _, h => (tyErr_ne_ok h).elim
  | _ :: _, [], _, h => (tyErr_ne_ok h).elim

theorem elabFieldsWith_erase {Γ : List CoreTy} (g : RawExpr → Elab S Γ)
    (hg : ∀ e r, g e = .ok r → r.2.erase = e) :
    ∀ (keys : List String) (es : List RawExpr) out, elabFieldsWith g keys es = .ok out →
      out.2.1.erase = es
  | [], [], out, h => by
      have e := (Except.ok.inj h).symm; subst e; rfl
  | k :: ks, e :: es, out, h => by
      obtain ⟨⟨A, ex⟩, hx, h⟩ := bind_ok h
      obtain ⟨⟨fs, xs, hfs⟩, hrest, h⟩ := bind_ok h
      have eo := (Except.ok.inj h).symm; subst eo
      show ex.erase :: xs.erase = e :: es
      rw [hg e ⟨A, ex⟩ hx, elabFieldsWith_erase g hg ks es ⟨fs, xs, hfs⟩ hrest]
  | [], _ :: _, _, h => (tyErr_ne_ok h).elim
  | _ :: _, [], _, h => (tyErr_ne_ok h).elim

end Rcic.Scm.ElabErase

namespace Rcic.Scm.ElabErase
open Rcic.Scm

theorem primOfString_name {s : String} {o : PrimOp} (h : primOfString s = some o) : primName o = s := by
  unfold primOfString at h
  split at h <;> first | exact Option.noConfusion h | (cases h; rfl)

end Rcic.Scm.ElabErase

namespace Rcic.Scm.ElabErase
open Rcic.Scm Rcic.Scm.Erase

theorem int_toNat_cast {i : Int} (h : ¬ i < 0) : ((i.toNat : Nat) : Int) = i :=
  Int.toNat_of_nonneg (Int.not_lt.mp h)

/-- First-order analogue of 06 §19 "intrinsic program → bound canonical wire object" (not that clause, K3c), expression layer: an elaborated expression
    erases to its source. -/
theorem elabE_erase : ∀ (n : Nat) (S : Sig) (Γ : List CoreTy) (e : RawExpr) (r : Σ T, CoreExpr S Γ T),
    elabE n S Γ e = .ok r → r.2.erase = e
  | 0, _, _, _, _, h => (tyErr_ne_ok h).elim
  | f + 1, S, Γ, e, r, h => by
    have ih : ∀ (Γ' : List CoreTy) (e' : RawExpr) (r' : Σ T, CoreExpr S Γ' T),
        elabE f S Γ' e' = .ok r' → r'.2.erase = e' := fun Γ' e' r' h' => elabE_erase f S Γ' e' r' h'
    cases e with
    | lit v t =>
      dsimp only [elabE] at h
      split at h
      · rename_i cv hcv
        have e := (Except.ok.inj h).symm; subst e
        show RawExpr.lit cv.erase t = .lit v t
        rw [toCore_erase t v cv hcv]
      · exact (tyErr_ne_ok h).elim
    | var i =>
      dsimp only [elabE] at h
      split at h
      · exact (tyErr_ne_ok h).elim
      · rename_i hi
        split at h
        · have e := (Except.ok.inj h).symm; subst e
          show RawExpr.var ((i.toNat : Nat) : Int) = .var i
          rw [int_toNat_cast hi]
        · exact (tyErr_ne_ok h).elim
    | letE a b =>
      obtain ⟨⟨A, ea⟩, ha, h⟩ := bind_ok h
      obtain ⟨⟨T, eb⟩, hb, h⟩ := bind_ok h
      have e := (Except.ok.inj h).symm; subst e
      show RawExpr.letE ea.erase eb.erase = .letE a b
      rw [ih Γ a _ ha, ih _ b _ hb]
    | ifE c th el =>
      obtain ⟨⟨C, ec⟩, hc, h⟩ := bind_ok h
      dsimp only at h
      split at h
      · rename_i hC
        obtain ⟨⟨T, et⟩, ht, h⟩ := bind_ok h
        obtain ⟨⟨E, ee⟩, he, h⟩ := bind_ok h
        dsimp only at h
        split at h
        · rename_i hE
          have e := (Except.ok.inj h).symm; subst e; subst hC; subst hE
          show RawExpr.ifE ec.erase et.erase ee.erase = .ifE c th el
          rw [ih Γ c _ hc, ih Γ th _ ht, ih Γ el _ he]
        · exact (tyErr_ne_ok h).elim
      · exact (tyErr_ne_ok h).elim
    | pair a b =>
      obtain ⟨⟨A, ea⟩, ha, h⟩ := bind_ok h
      obtain ⟨⟨B, eb⟩, hb, h⟩ := bind_ok h
      have e := (Except.ok.inj h).symm; subst e
      show RawExpr.pair ea.erase eb.erase = .pair a b
      rw [ih Γ a _ ha, ih Γ b _ hb]
    | fst a =>
      obtain ⟨r0, ha, h⟩ := bind_ok h
      split at h
      · rename_i A B ea
        have e := (Except.ok.inj h).symm; subst e
        show RawExpr.fst ea.erase = .fst a
        rw [ih Γ a _ ha]
      · exact (tyErr_ne_ok h).elim
    | snd a =>
      obtain ⟨r0, ha, h⟩ := bind_ok h
      split at h
      · rename_i A B ea
        have e := (Except.ok.inj h).symm; subst e
        show RawExpr.snd ea.erase = .snd a
        rw [ih Γ a _ ha]
      · exact (tyErr_ne_ok h).elim
    | inj i ts a =>
      dsimp only [elabE] at h
      split at h
      · exact (tyErr_ne_ok h).elim
      · rename_i hi
        split at h
        · exact (tyErr_ne_ok h).elim
        · rename_i A hA0
          obtain ⟨⟨T, ea⟩, ha, h⟩ := bind_ok h
          dsimp only at h
          split at h
          · rename_i hTA
            have e := (Except.ok.inj h).symm; subst e; subst hTA
            show RawExpr.inj ((i.toNat : Nat) : Int) ts ea.erase = .inj i ts a
            rw [int_toNat_cast hi, ih Γ a _ ha]
          · exact (tyErr_ne_ok h).elim
    | matchE sc bs =>
      obtain ⟨r0, hs, h⟩ := bind_ok h
      split at h
      · rename_i ts es
        split at h
        · rename_i A ts' b bs' es' _
          split at h
          · obtain ⟨⟨T, eb⟩, hb, h⟩ := bind_ok h
            obtain ⟨rest, hrest, h⟩ := bind_ok h
            have e := (Except.ok.inj h).symm; subst e
            show RawExpr.matchE es'.erase (eb.erase :: rest.erase) = .matchE sc (b :: bs')
            rw [ih Γ sc _ hs, ih _ b _ hb,
              elabBranchesWith_erase (elabE f S) (fun Γ' e' r' h' => elabE_erase f S Γ' e' r' h') Γ T ts' bs' rest hrest]
          · exact (tyErr_ne_ok h).elim
        · exact (tyErr_ne_ok h).elim
      · exact (tyErr_ne_ok h).elim
    | recordE keys fs =>
      dsimp only [elabE] at h
      split at h
      · exact (tyErr_ne_ok h).elim
      · split at h
        · obtain ⟨⟨flds, xs, hkeys⟩, hf, h⟩ := bind_ok h
          have e := (Except.ok.inj h).symm; subst e
          show RawExpr.recordE (flds.map Prod.fst) xs.erase = .recordE keys fs
          rw [hkeys, elabFieldsWith_erase (elabE f S Γ) (ih Γ) keys fs ⟨flds, xs, hkeys⟩ hf]
        · exact (tyErr_ne_ok h).elim
    | field rr i =>
      obtain ⟨r0, hr0, h⟩ := bind_ok h
      split at h
      · rename_i fs er
        split at h
        · exact (tyErr_ne_ok h).elim
        · rename_i hi
          split at h
          · have e := (Except.ok.inj h).symm; subst e
            show RawExpr.field er.erase ((i.toNat : Nat) : Int) = .field rr i
            rw [int_toNat_cast hi, ih Γ rr _ hr0]
          · exact (tyErr_ne_ok h).elim
      · exact (tyErr_ne_ok h).elim
    | nil t =>
      have e := (Except.ok.inj h).symm; subst e; rfl
    | cons hd tl =>
      obtain ⟨⟨H, eh⟩, hh, h⟩ := bind_ok h
      obtain ⟨⟨L, el⟩, hl, h⟩ := bind_ok h
      dsimp only at h
      split at h
      · rename_i hL
        have e := (Except.ok.inj h).symm; subst e; subst hL
        show RawExpr.cons eh.erase el.erase = .cons hd tl
        rw [ih Γ hd _ hh, ih Γ tl _ hl]
      · exact (tyErr_ne_ok h).elim
    | fold l init body =>
      obtain ⟨r0, hl, h⟩ := bind_ok h
      split at h
      · rename_i A el
        obtain ⟨⟨B, ei⟩, hi, h⟩ := bind_ok h
        obtain ⟨⟨B', eb⟩, hb, h⟩ := bind_ok h
        dsimp only at h
        split at h
        · rename_i hB
          have e := (Except.ok.inj h).symm; subst e; subst hB
          show RawExpr.fold el.erase ei.erase eb.erase = .fold l init body
          rw [ih Γ l _ hl, ih Γ init _ hi, ih _ body _ hb]
        · exact (tyErr_ne_ok h).elim
      · exact (tyErr_ne_ok h).elim
    | fix init limit stop step =>
      obtain ⟨⟨St, ei⟩, hi, h⟩ := bind_ok h
      obtain ⟨⟨L, el⟩, hl, h⟩ := bind_ok h
      dsimp only at h
      split at h
      · rename_i hL
        obtain ⟨⟨B, es⟩, hs, h⟩ := bind_ok h
        dsimp only at h
        split at h
        · rename_i hB
          obtain ⟨⟨St', ep⟩, hp, h⟩ := bind_ok h
          dsimp only at h
          split at h
          · rename_i hSt
            have e := (Except.ok.inj h).symm; subst e; subst hL; subst hB; subst hSt
            show RawExpr.fix ei.erase el.erase es.erase ep.erase = .fix init limit stop step
            rw [ih Γ init _ hi, ih Γ limit _ hl, ih _ stop _ hs, ih _ step _ hp]
          · exact (tyErr_ne_ok h).elim
        · exact (tyErr_ne_ok h).elim
      · exact (tyErr_ne_ok h).elim
    | prim op args =>
      dsimp only [elabE] at h
      split at h
      · exact (tyErr_ne_ok h).elim
      · rename_i o ho
        obtain ⟨xs, hxs, h⟩ := bind_ok h
        split at h
        · rename_i as has
          have e := (Except.ok.inj h).symm; subst e
          show RawExpr.prim (primName o) as.erase = .prim op args
          rw [primOfString_name ho, toArgs_erase xs _ as has, elabListWith_erase (elabE f S Γ) (ih Γ) args xs hxs]
        · exact (tyErr_ne_ok h).elim
    | call fr args =>
      cases fr with
      | «local» i =>
        dsimp only [elabE] at h
        split at h
        · exact (tyErr_ne_ok h).elim
        · rename_i hi
          split at h
          · exact (tyErr_ne_ok h).elim
          · rename_i fs hfs
            obtain ⟨xs, hxs, h⟩ := bind_ok h
            split at h
            · rename_i as has
              have e := (Except.ok.inj h).symm; subst e
              show RawExpr.call (.local ((i.toNat : Nat) : Int)) as.erase = .call (.local i) args
              rw [int_toNat_cast hi, toArgs_erase xs _ as has, elabListWith_erase (elabE f S Γ) (ih Γ) args xs hxs]
            · exact (tyErr_ne_ok h).elim
      | ext ref =>
        dsimp only [elabE] at h
        split at h
        · exact (tyErr_ne_ok h).elim
        · rename_i x hx
          obtain ⟨xs, hxs, h⟩ := bind_ok h
          split at h
          · rename_i as has
            have e := (Except.ok.inj h).symm; subst e
            show RawExpr.call (.ext ref) as.erase = .call (.ext ref) args
            rw [toArgs_erase xs _ as has, elabListWith_erase (elabE f S Γ) (ih Γ) args xs hxs]
          · exact (tyErr_ne_ok h).elim
    | raise rf p t =>
      dsimp only [elabE] at h
      split at h
      · exact (tyErr_ne_ok h).elim
      · rename_i P hP
        obtain ⟨⟨P', ep⟩, hp, h⟩ := bind_ok h
        dsimp only at h
        split at h
        · rename_i hPP
          have e := (Except.ok.inj h).symm; subst e; subst hPP
          show RawExpr.raise rf ep.erase t = .raise rf p t
          rw [ih Γ p _ hp]
        · exact (tyErr_ne_ok h).elim
    | handle rf body hd =>
      dsimp only [elabE] at h
      split at h
      · exact (tyErr_ne_ok h).elim
      · rename_i P hP
        obtain ⟨⟨T, eb⟩, hb, h⟩ := bind_ok h
        obtain ⟨⟨T', eh⟩, hh, h⟩ := bind_ok h
        dsimp only at h
        split at h
        · rename_i hT
          have e := (Except.ok.inj h).symm; subst e; subst hT
          show RawExpr.handle rf eb.erase eh.erase = .handle rf body hd
          rw [ih Γ body _ hb, ih _ hd _ hh]
        · exact (tyErr_ne_ok h).elim
    | unknown k => exact (tyErr_ne_ok h).elim

end Rcic.Scm.ElabErase

namespace Rcic.Scm.ElabErase
open Rcic.Scm

/-- The erasures of a program's bodies, in group order. -/
def Bodies.erasures {S : Sig} : {fs : List FnSig} → Bodies S fs → List RawExpr
  | _, .nil => []
  | _, .cons b bs => b.erase :: Bodies.erasures bs

/-- First-order analogue (program direction): elaborated bodies erase to the raw bodies. -/
theorem elabBodies_erase (n : Nat) (S : Sig) :
    ∀ (fs : List RawFnDef) (bs : Bodies S (fs.map (fun f => ⟨f.params, f.result⟩))),
    elabBodies n S fs = .ok bs → Bodies.erasures bs = fs.map RawFnDef.body
  | [], bs, h => by
      have e := (Except.ok.inj h).symm; subst e; rfl
  | f :: fs, bs, h => by
      obtain ⟨⟨T, eb⟩, hb, h⟩ := bind_ok h
      dsimp only at h
      split at h
      · rename_i hT
        obtain ⟨rest, hrest, h⟩ := bind_ok h
        have e := (Except.ok.inj h).symm; subst e; subst hT
        show eb.erase :: Bodies.erasures rest = f.body :: fs.map RawFnDef.body
        rw [elabE_erase n S f.params f.body _ hb, elabBodies_erase n S fs rest hrest]
      · exact (tyErr_ne_ok h).elim

/-- The body a typed program enters at index `i` erases to the raw body at
    the same index. -/
theorem bodies_at_erase {S : Sig} :
    ∀ {sigs : List FnSig} (bs : Bodies S sigs) (i : Nat) (f : FnSig) (h : sigs.get? i = some f),
    (Bodies.erasures bs).get? i = some (bs.at i f h).erase
  | _ :: _, .cons b _, 0, _, h => by
      have e := Option.some.inj h; subst e; rfl
  | _ :: _, .cons _ bs, n + 1, f, h => bodies_at_erase bs n f h
  | [], .nil, _, _, h => nomatch h

/-! ## Instance witness (M-005) -/
def five : CoreVal .i64 := .i64V 5 ⟨by decide, by decide⟩
example : (CoreExpr.lit (S := ⟨[], [], []⟩) (Γ := []) five).erase = .lit (.i 5) .i64 :=
  elabE_erase 2 ⟨[], [], []⟩ [] (.lit (.i 5) .i64) ⟨.i64, .lit five⟩ rfl

end Rcic.Scm.ElabErase
