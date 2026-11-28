import J6R54DispatchRetained
import J6R54DispatchKeys

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 11500000
set_option maxRecDepth 2950
set_option linter.unusedSectionVars false

/-! A small routed payload that reuses the existing checked forwarded
LocalLoad. Its raw argument is the actual external mode word; the route
is not allowed to silently substitute a different retained vector. -/
namespace J6R54Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion J6R32StatefulArithmetic
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R48DFS
open J6R50SourceProducer J6R51Online J6R52Dispatch J6R53Dispatch J6R49DFS J6R25PreparedSupply
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (X : StoredSite T v key prec tw bw page)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Slots" => ((Plan sel).Slot v.child)
local notation "Bank" => (PageBank f ell key prec tw bw page)
local notation "Job" => (PageJob f ell key prec tw bw page)

variable {X}
local notation "M" => (N sel)
local notation "W" => J6R15ModeCost.Word q

theorem retained_chart_selects_exact_observed_slot {d : Ready SP (sourceDelta s) v.child}
    {t : Center SP v.child} {raw : List W}
    (I : SiteTape sel d t q) (row : RetainedTicket X raw) (z : Probe SP v.child) (g : Fin 64)
    (β : NativeMenu M v.child t) (observed : decodeAt I raw=some β)
    (tExact : row.w.val.1=t) (zExact : row.w.val.2.1=z) (gExact : row.w.val.2.2.2=g)
    (declared : SiteTape sel
      (ticketReady T (J6R48RawRoute.successorTicket v row.w)) row.w.val.1 q)
    (sameTape : HEq declared I)
    (sameKey : raw.map Word.val=vectorKey sel (ticketReady T (J6R48RawRoute.successorTicket v row.w))
      row.w.val.1 declared row.w.val.2.2.1) :
    row.w=addressed (sel:=sel) d t z β g := by
  have mode : HEq row.w.val.2.2.1 β :=
    same_selected_mode_from_same_incoming tExact I declared sameTape raw
      row.w.val.2.2.1 β sameKey observed
  apply Subtype.ext
  exact native_field_ext row.w.val t z β g tExact zExact mode gExact

theorem retained_load_exact_native_field_words {d : Ready SP (sourceDelta s) v.child}
    {t : Center SP v.child} {raw : List W}
    (I : SiteTape sel d t q) (row : RetainedTicket X raw) (z : Probe SP v.child) (g : Fin 64)
    (β : NativeMenu M v.child t) (observed : decodeAt I raw=some β)
    (tExact : row.w.val.1=t) (zExact : row.w.val.2.1=z) (gExact : row.w.val.2.2.2=g)
    (declared : SiteTape sel
      (ticketReady T (J6R48RawRoute.successorTicket v row.w)) row.w.val.1 q)
    (sameTape : HEq declared I)
    (sameKey : raw.map Word.val=vectorKey sel (ticketReady T (J6R48RawRoute.successorTicket v row.w))
      row.w.val.1 declared row.w.val.2.2.1) :
    let atSlot := addressed (sel:=sel) d t z β g
    let current := J6R48RawRoute.successorTicket v atSlot
    let out := row.localLoad.result
    out.event.native.result.tWord.val=centerOrdinal T current ∧
      out.event.native.result.zWord.val=z.val ∧
      out.event.native.result.mWord.val=modeOrdinal T current ∧
      out.event.native.result.gWord.val=g.val ∧
      out.event.words.result.exponents.map Word.val=liveExponentSpec row.packet.base.geometry := by
  have exactSlot := retained_chart_selects_exact_observed_slot I row z g β observed
    tExact zExact gExact declared sameTape sameKey
  let cur := J6R48RawRoute.successorTicket v (addressed (sel:=sel) d t z β g)
  let target := J6R48RawRoute.successorTicket v row.w
  have same : target=cur := congrArg (J6R48RawRoute.successorTicket v) exactSlot
  obtain ⟨E,ok,fields⟩ := row.packet.checked
  have data := accepted_event_loads_its_returned_data row.packet.base.geometry row.packet.base.shell
    row.packet.base.directory row.packet.materialized row.packet.checked E ok
  have ht : row.localLoad.result.event.native.result.tWord.val=E.centre.val :=
    congrArg Word.val data.1
  have hz : row.localLoad.result.event.native.result.zWord.val=E.probe.val :=
    congrArg Word.val data.2.1
  have hm : row.localLoad.result.event.native.result.mWord.val=E.mode.val :=
    congrArg Word.val data.2.2.1
  have hg : row.localLoad.result.event.native.result.gWord.val=E.group.val :=
    congrArg Word.val data.2.2.2.1
  have ex : row.localLoad.result.event.words.result.exponents.map Word.val=E.exponents.map Word.val :=
    congrArg (List.map Word.val) data.2.2.2.2
  have c1 : E.centre.val=centerOrdinal T target := fields.centre
  have z1 : E.probe.val=target.probeAt.val := fields.probe
  have m1 : E.mode.val=modeOrdinal T target := fields.mode
  have g1 : E.group.val=target.groupAt.val := fields.group
  rw [same] at c1 z1 m1 g1
  exact ⟨ht.trans c1,hz.trans z1,hm.trans m1,hg.trans g1,ex.trans fields.exponents⟩

#print axioms retained_chart_selects_exact_observed_slot
#print axioms retained_load_exact_native_field_words
end
end J6R54Dispatch

