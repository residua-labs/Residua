import rcic.RcicERPiSlot
import rcic.RcicSynES

/-!
# ER1 repair, batch R1 — conversion pad/unpad for `piSlot`

`research/rcic/sortrow/S12_ER1_REPAIR.md` §3. Lifting and cancelling a proof-domain
codomain conversion uses the existing table closedness: `convMod_lift` requires a real
`TableClosed tbl`, and `convMod_unpad` is `convMod_inst_body` at the padded slot followed
by `ETm.inst_lift_id` — not an assumed lift-injectivity of conversion.

This layer sits above `RcicSynErase` (it needs `RcicSynES`), so it is a separate module
from `RcicERPiSlot`, which the R2 `eps.pi` switch will import.
-/

namespace Rcic.Syn

/-- Pad a conversion (S12 §3): `q ↔* q'` gives `piSlot b q ↔* piSlot b q'`. The `true`
    branch is `convMod_lift` at `0 1`, hence the real `TableClosed`; `false` is `h`. -/
theorem convMod_piSlot {tbl : List CRule} (hcl : TableClosed tbl) (b : Bool) {q q' : ETm}
    (h : ConvMod (EStep tbl) LvlEq q q') :
    ConvMod (EStep tbl) LvlEq (piSlot b q) (piSlot b q') := by
  cases b
  · exact h
  · exact convMod_lift hcl h 0 1

/-- Unpad (S12 §3, verbatim): inst congruence at the padded slot with an arbitrary legal
    replacement (`ETm.star` — the slot is never looked at), then `inst_lift_id` cancels
    both pads. -/
theorem convMod_unpad {tbl : List CRule} (hcl : TableClosed tbl) {q q' : ETm}
    (h : ConvMod (EStep tbl) LvlEq (q.lift 0 1) (q'.lift 0 1)) :
    ConvMod (EStep tbl) LvlEq q q' := by
  have h' := convMod_inst_body hcl h 0 ETm.star
  simpa only [ETm.inst_lift_id] using h'

/-- `convMod_unpad` at the `piSlot` view: `piSlot true q` is `q.lift 0 1` by definition. -/
theorem convMod_unpiSlot {tbl : List CRule} (hcl : TableClosed tbl) {q q' : ETm}
    (h : ConvMod (EStep tbl) LvlEq (piSlot true q) (piSlot true q')) :
    ConvMod (EStep tbl) LvlEq q q' :=
  convMod_unpad hcl h

end Rcic.Syn

#print axioms Rcic.Syn.convMod_piSlot
#print axioms Rcic.Syn.convMod_unpad
#print axioms Rcic.Syn.convMod_unpiSlot
