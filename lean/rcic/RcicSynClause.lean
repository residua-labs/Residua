import rcic.RcicSynCanon

/-!
# Syntactic sortRow, build step 3v — clause endpoints that stay under the node

`research/rcic/semantic/S3_ES_ARMS.md` §21. A stored endpoint is `CL` to a
canonical node only when that node's weight sits under the rule. The node
is one atom, its weight. These canons are sums of strict pieces of the
node, plus at most the endpoint's regularity (`wt_reg_le`):

* `app` (left): `h1.dl`, `h2.dl`, `dl.reg`. Each premise endpoint is
  strictly lighter than the premise, and the node pays for both premises.
* `pi` (left): `hA.dl` and `hB.dl`. No regularity copy.
* `letE` (left) and `zeta` (left): the three premise typings, and
  `dl.reg` as the ascribed-type typing. `zeta` pays for those three
  typings already; `dl.reg` is covered by `dr`.

A `lam` is not in this list. Its constructor pays for the body and, beside
it, for a typing of the body's type. That second copy is `hbody.reg`, and
the rule node paid for the body only once. The same copy is why a canonical
`app` of a canonical `lam` (the β redex) can outweigh `CvP.beta`. `pi`'s
right endpoint and `app`'s right endpoint are not here either: the codomain
is typed under the left binder, and moving it (`cctx`, or `piInv` plus
`instEnd` at the right argument) puts the whole domain conversion back into
the atom.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 clause equations -/

theorem eps_app_clause {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a A B : Expr Nat} {w : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.app E n Γ f a A B w hf ha hT).eps σ ρ =
      match hf.eps σ ρ with
      | .star => .star
      | ef =>
          match ha.eps σ ρ with
          | .star => ef
          | ea => .app ef ea := rfl

theorem eps_let_clause {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {value B body : Expr Nat} {w : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.letE E n Γ A u value B body w hA hv hb hT).eps σ ρ =
      match hv.eps σ ρ with
      | .star => hb.eps σ (.drop :: ρ)
      | ev => hb.eps σ (.inline ev :: ρ) := rfl

/-! ## §2 `app`, the left endpoint -/

/-- The left application erases to the clause of its two premise endpoints.
    `h1.dl` types `f`, `h2.dl` types `a`, and `dl.reg` types `B[a]`. -/
theorem app_dl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f g a b A B : Expr Nat}
    (h1 : CvP E n Γ f g (.pi A B)) (h2 : CvP E n Γ a b A)
    (dl : TyP E n Γ (.app f a) (instantiate0 a B))
    (dr : TyP E n Γ (.app g b) (instantiate0 a B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.app E n Γ f g a b A B h1 h2 dl dr))) :
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (match h1.dl.eps σ ρ with
        | .star => .star
        | ef =>
            match h2.dl.eps σ ρ with
            | .star => ef
            | ea => .app ef ea) := by
  let hnode := CvP.app E n Γ f g a b A B h1 h2 dl dr
  have ht : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  let canon := TyP.app E n Γ f a A B dl.reg.1 h1.dl h2.dl dl.reg.2
  have hwc : canon.wt Aw < hnode.wt Aw := by
    have hlt1 := CvP.wt_dl_lt Aw h1
    have hlt2 := CvP.wt_dl_lt Aw h2
    have hreg := TyP.wt_reg_le Aw dl
    have _hpos := TyP.wt_pos Aw dr
    simp only [TyP.wt, CvP.wt]
    omega
  have hC := cl_under Aw tbl hnode ht Bel dl canon σ ρ hρ hwl hwc
  simpa only [CL, eps_app_clause] using hC

/-! ## §3 `pi`, the left endpoint -/

/-- The left Π erases to `pi` of its two premise endpoints. A proof domain
    extends the codomain by `drop`; a relevant domain extends it by `keep`. -/
theorem pi_dl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' B B' : Expr Nat} {u v : Level}
    (hA : CvP E n Γ A A' (.sort u))
    (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
    (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
    (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.pi E n Γ A A' B B' u v hA hB dl dr))) :
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (match levelIsZero (σ u) with
        | true => .pi (hA.dl.eps σ ρ) (piSlot true (hB.dl.eps σ (.drop :: ρ)))
        | false => .pi (hA.dl.eps σ ρ) (hB.dl.eps σ (.keep :: ρ))) := by
  let hnode := CvP.pi E n Γ A A' B B' u v hA hB dl dr
  have ht : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  let canon := TyP.pi E n Γ A u B v hA.dl hB.dl
  have hwc : canon.wt Aw < hnode.wt Aw := by
    have hltA := CvP.wt_dl_lt Aw hA
    have hltB := CvP.wt_dl_lt Aw hB
    have _hpos := TyP.wt_pos Aw dr
    simp only [TyP.wt, CvP.wt]
    omega
  have hC := cl_under Aw tbl hnode ht Bel dl canon σ ρ hρ hwl hwc
  match hzu : levelIsZero (σ u) with
  | true =>
      simpa only [CL, eps_pi_drop (hA := hA.dl) (hB := hB.dl) hzu, hzu] using hC
  | false =>
      simpa only [CL, eps_pi_keep (hA := hA.dl) (hB := hB.dl) hzu, hzu] using hC

/-! ## §4 `let`, the left endpoint -/

/-- The left `let` erases to the body under `drop` when the value erases to
    `★`, and under `inline` of that value otherwise. -/
theorem letE_dl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A A' v v' b b' B : Expr Nat} {u : Level}
    (hA : CvP E n Γ A A' (.sort u)) (hv : CvP E n Γ v v' A)
    (hb : CvP E n (.letBinding A v :: Γ) b b' B)
    (dl : TyP E n Γ (.letE A v b) (instantiate0 v B))
    (dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr))) :
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (match hv.dl.eps σ ρ with
        | .star => hb.dl.eps σ (.drop :: ρ)
        | ev => hb.dl.eps σ (.inline ev :: ρ)) := by
  let hnode := CvP.letE E n Γ A A' v v' b b' B u hA hv hb dl dr
  have ht : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  let canon := TyP.letE E n Γ A u v B b dl.reg.1 hA.dl hv.dl hb.dl dl.reg.2
  have hwc : canon.wt Aw < hnode.wt Aw := by
    have hltA := CvP.wt_dl_lt Aw hA
    have hltv := CvP.wt_dl_lt Aw hv
    have hltb := CvP.wt_dl_lt Aw hb
    have hreg := TyP.wt_reg_le Aw dl
    have _hpos := TyP.wt_pos Aw dr
    simp only [TyP.wt, CvP.wt]
    omega
  have hC := cl_under Aw tbl hnode ht Bel dl canon σ ρ hρ hwl hwc
  simpa only [CL, eps_let_clause] using hC

/-- `zeta`'s left endpoint is the same clause, read off the rule's own value
    and body. `dl.reg` types `B[value]`. The reduct is not this clause:
    the body is typed under a let, and `instEnd` substitutes an assumption. -/
theorem zeta_dl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (dl : TyP E n Γ (.letE A value body) (instantiate0 value B))
    (dr : TyP E n Γ (instantiate0 value body) (instantiate0 value B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.zeta E n Γ A value body B u hA hv hb dl dr))) :
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ)
      (match hv.eps σ ρ with
        | .star => hb.eps σ (.drop :: ρ)
        | ev => hb.eps σ (.inline ev :: ρ)) := by
  let hnode := CvP.zeta E n Γ A value body B u hA hv hb dl dr
  have ht : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  let canon := TyP.letE E n Γ A u value B body dl.reg.1 hA hv hb dl.reg.2
  have hwc : canon.wt Aw < hnode.wt Aw := by
    have hreg := TyP.wt_reg_le Aw dl
    have _hpos := TyP.wt_pos Aw dr
    simp only [TyP.wt, CvP.wt]
    omega
  have hC := cl_under Aw tbl hnode ht Bel dl canon σ ρ hρ hwl hwc
  simpa only [CL, eps_let_clause] using hC

/-! ## §5 coherences that do not build a node -/

/-- `ι`'s two endpoints are `CL` to the two premise typings of the same terms.
    The `EStep` between those erasures is `eraseTable`, step 4. -/
theorem iota_dl (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr))) :
    ConvMod (EStep tbl) LvlEq (dl.eps σ ρ) (hlhs.eps σ ρ) := by
  let hnode := CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr
  have ht : hnode.isTransport = false := rfl
  have hwl : dl.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwh : hlhs.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  simpa only [CL] using cl_under Aw tbl hnode ht Bel dl hlhs σ ρ hρ hwl hwh

theorem iota_dr (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (h : DerivedIota E lhs rhs) (hlhs : TyP E n Γ lhs T) (hrhs : TyP E n Γ rhs T)
    (dl : TyP E n Γ lhs T) (dr : TyP E n Γ rhs T)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr))) :
    ConvMod (EStep tbl) LvlEq (hrhs.eps σ ρ) (dr.eps σ ρ) := by
  let hnode := CvP.iota E n Γ lhs rhs T h hlhs hrhs dl dr
  have ht : hnode.isTransport = false := rfl
  have hwh : hrhs.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  simpa only [CL] using cl_under Aw tbl hnode ht Bel hrhs dr σ ρ hρ hwh hwr

/-- δ's right endpoint types the instantiated body, and so does `hb`. -/
theorem delta_dr (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    ConvMod (EStep tbl) LvlEq (hb.eps σ ρ) (dr.eps σ ρ) := by
  let hnode := CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr
  have ht : hnode.isTransport = false := rfl
  have hwb : hb.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  simpa only [CL] using cl_under Aw tbl hnode ht Bel hb dr σ ρ hρ hwb hwr

/-- η's right endpoint types `f`, and so does the premise. `es_eta`'s `F`
    is this erasure. The left endpoint is a `lam` of an application. -/
theorem eta_dr (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {f A B : Expr Nat}
    (h : TyP E n Γ f (.pi A B))
    (dl : TyP E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) (.pi A B))
    (dr : TyP E n Γ f (.pi A B))
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (Bel : Below Aw tbl (cvMeas Aw (CvP.eta E n Γ f A B h dl dr))) :
    ConvMod (EStep tbl) LvlEq (h.eps σ ρ) (dr.eps σ ρ) := by
  let hnode := CvP.eta E n Γ f A B h dl dr
  have ht : hnode.isTransport = false := rfl
  have hwh : h.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  have hwr : dr.wt Aw < hnode.wt Aw := by simp only [CvP.wt]; omega
  simpa only [CL] using cl_under Aw tbl hnode ht Bel h dr σ ρ hρ hwh hwr

end Rcic.Syn

#print axioms Rcic.Syn.eps_app_clause
#print axioms Rcic.Syn.eps_let_clause
#print axioms Rcic.Syn.app_dl
#print axioms Rcic.Syn.pi_dl
#print axioms Rcic.Syn.letE_dl
#print axioms Rcic.Syn.zeta_dl
#print axioms Rcic.Syn.iota_dl
#print axioms Rcic.Syn.iota_dr
#print axioms Rcic.Syn.delta_dr
#print axioms Rcic.Syn.eta_dr
