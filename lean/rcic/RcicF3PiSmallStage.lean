import rcic.RcicF3PiSmallProducer
/-!
# Universe bounds for decoded small trees

Small collections of small decoded values stay small, including erased
recursive fields at arbitrary Pi depth. `family_small` bounds the existing
mixed-universe model at stage 4 using local code closure; producing that
closure and the smaller result-stage signatures from admitted syntax remains
open. No new tree type or universal group certificate is introduced.
`closure_claim = 0`.
-/
set_option autoImplicit false
namespace Rcic.F3.PSet.PiSmallStage
universe u v

theorem small_mk (ch : Choice.{u}) (α : Type u) (f : α → PSet.{max u v})
    (hf : ∀ a, Small.{u,v} (f a)) :
    Small.{u,v} (mk (ULift.{max u v} α) (fun a => f a.down)) := by
  let pick := fun a => ch (fun y => Equiv (f a) (lift.{u,v} y)) (hf a)
  refine ⟨mk α (fun a => (pick a).1), ext fun z => ⟨?_, ?_⟩⟩
  · intro ⟨a, ha⟩
    have hm : lift.{u,v} ((pick a.down).1) ∈
        lift.{u,v} (mk α (fun a => (pick a).1)) :=
      (lift_mem_lift.{u,v}).mpr ⟨a.down, Equiv.rfl⟩
    exact mem_congr_left ((pick a.down).2.symm.trans ha) hm
  · intro hz
    obtain ⟨y, ⟨a, ha⟩, hz⟩ := mem_lift.{u,v}.mp hz
    exact ⟨⟨a⟩, (pick a).2.trans ((lift_equiv.{u,v} ha).trans hz.symm)⟩

theorem small_lamVal (ch : Choice.{u}) (M : Interp.{max u v})
    (A : PSet.{max u v}) (b : PSet.{max u v} → PSet.{max u v})
    (hA : Small.{u,v} (Ed M A))
    (hb : ∀ x y, Equiv x y → Equiv (b x) (b y))
    (hs : ∀ x, x ∈ Ed M A → Small.{u,v} (b x)) :
    Small.{u,v} (lamVal M A b) := by
  cases hd : M.dec (LamProof M A b) with
  | isTrue h =>
      unfold lamVal
      rw [cond_pos h]
      exact small_pempty
  | isFalse h =>
      unfold lamVal
      rw [cond_neg h]
      apply small_sImage ch hA
        (fun x y _ he => ordPair_congr he (hb x y he))
      intro x hx
      have hxs : Small.{u,v} x := small_of_mem_small hA hx
      obtain ⟨x0, hx0⟩ := hxs
      have hsingle : Small.{u,v} (singleton x) :=
        ⟨singleton x0, (singleton_congr hx0).trans (lift_singleton.{u,v} x0).symm⟩
      exact small_pair hsingle (small_pair ⟨x0, hx0⟩ (hs x hx))

universe w

def DomainsSmall {I : Type w} : {m : Nat} → RecTel.{max u v,w} I m → Prop
  | _, .ret _ => True
  | _, .pi A B => Small.{u,v} A ∧ ∀ q, DomainsSmall (B q)

theorem erasedEncode_small {I : Type w} (ch : Choice.{u})
    (M : Interp.{max u v}) {m : Nat} (t : RecTel.{max u v,w} I m)
    (ht : t.DomainsDich) (hD : DomainsSmall.{u,v,w} t)
    (f : PiTel.Value t.tel (fun _ => PSet.{max u v}))
    (hf : ∀ p, Small.{u,v} (t.tel.flatten f p)) :
    Small.{u,v} (t.erasedEncode M f) := by
  induction t with
  | ret i => exact hf .unit
  | pi A B ih =>
      apply small_lamVal ch M (tyv A)
        (classFiber A (fun q => (B q).erasedEncode M (f q)))
      · exact hD.1.congr (ed_tyv M ht.1).symm
      · exact fun _ _ he => classFiber_congr A _ he
      · intro x hx
        obtain ⟨a, ha⟩ := mem_congr_right (ed_tyv M ht.1) hx
        have hs := ih (Quotient.mk (FSetoid A) a) (ht.2 _) (hD.2 _) (f _)
          (fun p => hf ⟨Quotient.mk (FSetoid A) a, p⟩)
        exact hs.congr ((classFiber_at A _ a).symm.trans
          (classFiber_congr A _ ha))

theorem encode_small {I : Type w} (ch : Choice.{3})
    (M : Interp.{4}) {m : Nat} (t : RecTel.{3,w} I m)
    (ht : t.DomainsDich) (f : PiTel.Value t.tel (fun _ => PSet.{4}))
    (hf : ∀ p, Small.{3,4} (t.tel.flatten f p)) :
    Small.{3,4} (PiSmallField.encode M t f) := by
  have hd : DomainsSmall.{3,4,w} (PiSmallCompile.widen t) := by
    clear ht f hf
    induction t with
    | ret _ => trivial
    | pi A B ih => exact ⟨small_lift A, fun q => ih (FBrDown A q)⟩
  have hs : ∀ p, Small.{3,4} ((PiSmallCompile.widen t).tel.flatten
      (PiSmallField.expand t f) p) := by
    clear hd
    induction t with
    | ret _ => exact fun _ => hf .unit
    | pi A B ih =>
        intro p
        exact ih (FBrDown A p.1) (ht.2 _) (f _) (fun r => hf ⟨FBrDown A p.1, r⟩) p.2
  exact erasedEncode_small ch M (PiSmallCompile.widen t)
    (PiSmallField.widen_dich t ht) hd (PiSmallField.expand t f) hs

theorem decode_small {I : Type w} (ch : Choice.{3}) (M : Interp.{4})
    (S : PiSmallProducer.Sig I) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : ∀ s f, (∀ k, Small.{3,4} (f k)) → Small.{3,4} (S.code s f))
    (t : PiSmallProducer.Tree S) : Small.{3,4} (PiSmallProducer.decode M S t) := by
  induction t with
  | sup s g ih =>
      apply hcode s
      intro k
      apply encode_small ch M (S.tel s k) (hD s k)
      intro p
      simpa only [PiTel.flatten_unflatten] using ih ⟨k,p⟩

theorem family_small {I : Type w} (ch : Choice.{3}) (M : Interp.{4})
    (S : PiSmallProducer.Sig I) (hD : ∀ s k, (S.tel s k).DomainsDich)
    (hcode : ∀ s f, (∀ k, Small.{3,4} (f k)) → Small.{3,4} (S.code s f))
    (i : I) : Small.{3,4} (PiSmallProducer.family M S i) := by
  exact small_mk ch {t : PiSmallProducer.Tree S // PiSmallProducer.Valid S i t}
    (fun t => PiSmallProducer.decode M S t.1)
    (fun t => decode_small ch M S hD hcode t.1)

end Rcic.F3.PSet.PiSmallStage
