import J6R49SourceLayoutExport
import J6R33GeneratedChildSiteSparse

/-! Generate one resident layout in its stable ordered-cell chart.
Its normal raw export (masks, seats, sparse modes) and its extra
native-order seat stream are produced by one paid greedy run, not two
separate choices with matching page counts. -/
namespace J6R49SourceLayout
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R14LayoutCost J6R27OriginalGate J6R31RootResidentTables P11FullPacking
open J6R32ChildResidentTransfer J6R48RawRoute J6R12CollisionMenu J6R17ModeTape
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R10Repack J6R9PacketScopes
open J6R33GeneratedChildSite
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12000000
set_option maxRecDepth 2550
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

structure PreparedSeats (a q : ℕ) where
  native : ChildResidents a q
  ordered : List (SeatField a ((q-a)+13*a))

def prepareGreedySeats (a e kR kC b q i : ℕ) (axis : List Bool)
    (targets : List Target) (input : List (List Bool×List Bool)) (precision : Word (q+1)) :
    Meter (Option (PreparedSeats a q)) :=
  let file := fullGreedyResident a e kR kC b q i axis targets input precision
  let rows := reorderInstalledSeats q (3*(kR+kC)+9)
    file.result.raw.packed.boxes file.result.seats input
  ⟨rows.result.map (PreparedSeats.mk file.result),file.steps+rows.steps+5⟩

def preparedSeatFee {E R C : Type} [Fintype E] [Fintype R] [Fintype C] {a : ℕ}
    (F : Format E R C (Fin a→Fin 64)) (q i copies p : ℕ) (boxes : List ExportBox) : ℕ :=
  fullGreedyFee F q i copies p+
    (6+q+(18*q+(3*(F.kR+F.kC)+9)+8)*F.edges.length+
      alignFee q a ((q-a)+13*a) F.edges.length (exportRows boxes) boxes.length
        (packingTraffic boxes)+4)+5

theorem generate_stable_residents_and_native_rows
    {E R C : Type} [Fintype E] [Fintype R] [Fintype C] {a : ℕ}
    (N : Network E R C) (F : Format E R C (Fin a→Fin 64))
    (hrow : F.row=N.row) (hcol : F.col=N.col)
    (hb : F.b=6*a) (hFormat : ∀ x,F.label x=coordinateLabel x)
    (vs : List (R⊕C)) (hn : vs.Nodup) (hall : ∀ v : R⊕C,v∈vs)
    (Δ q : ℕ) (hq : 0<q) (ha : a≤q) (hfit : Fintype.card E<2^q)
    (hr : ∀ v,Nat.card {e : E // N.row e=v}≤Δ)
    (hc : ∀ v,Nat.card {e : E // N.col e=v}≤Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E)
    (hslots : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card E)
    (i : Fin a) (axis : List Bool) (clock : axis.length=i.val)
    (precision : Word (q+1)) (hp : 0<precision.val) :
    let raw := F.edges.map (fun e=>
      (encodeBits F.kR (F.rCode (F.row e)),encodeBits F.kC (F.cCode (F.col e))))
    let out := prepareGreedySeats a F.e F.kR F.kC F.b q i.val axis (vs.map F.target) raw precision
    ∃ P : PhysicalPacking N a (Fin 64), ∃ L : PreparedSeats a q,
      out.result=some L ∧ P.mask=childMask a P.copies ∧
      Nonempty (ResidentReceipt P i precision.val L.native) ∧
      L.ordered=F.edges.map (physicalSeatField P i (childPageKey (q-a))) ∧
      out.steps≤preparedSeatFee F q i.val P.copies precision.val L.native.raw.packed.boxes := by
  let raw := F.edges.map (fun e=>
    (encodeBits F.kR (F.rCode (F.row e)),encodeBits F.kC (F.cCode (F.col e))))
  let g := packGreedy a F.e F.kR F.kC F.b q (vs.map F.target) raw
  obtain ⟨z,P,hZ,_,hQ,hCopy,hRel,hTags,gFee⟩ :=
    packGreedy_exact N F hrow hcol hb hFormat vs hn hall Δ q hq ha hfit hr hc hcollision hslots
  let Q := installedChart F z P hrow hcol hb hFormat hZ ha hfit hRel hTags
  let ord := installedEdgeOrder F z hfit hTags
  have on := installed_edge_order_exact F z hfit hTags
  obtain ⟨seats,seatFee⟩ := install_full_greedy_seat_table F z P hrow hcol hb hFormat hZ ha hfit hRel hTags i axis clock
  have qfit : Q.copies≤2^(q-a) := packed_copy_bits_fit P i ha hfit
  let cp := fitWord (q+1) g.result.copies
  have hBits : cp.result.bits=g.result.copies := fit_word_value _ _ hQ
  have hcp : cp.result.val=P.copies := by
    change bitsValue cp.result.bits=P.copies
    rw [hBits]
    exact hCopy
  obtain ⟨cs,hH,hN,hA,hB,_,hR⟩ := packed_header_lift F hb z hRel
  let bm := writeChildMaskBank (Nat.succ_pos q) a cp.result
  obtain ⟨em,_,mf⟩ := child_mask_bank_exact (Nat.succ_pos q) a cp.result hcp
  let traffic := rowTraffic F.kR F.kC F.b q a
  let rs := buildTape (Nat.succ_pos q) a i.val traffic g.result.boxes cp.result precision
  have hi : i.val+1<q+1 := by omega
  obtain ⟨ms,nd,all,raws,rawND,weights,_,rf⟩ :=
    buildTape_exact (Nat.succ_pos q) i hi traffic g.result.boxes cs hH hN hA cp.result precision hcp rfl hp
  let S := writeSeatedBoxes a (q-a) axis g.result.boxes
  let resident := fullGreedyResident a F.e F.kR F.kC F.b q i.val axis (vs.map F.target) raw precision
  let childSeats := F.edges.map (physicalSeatField Q i (childPageKey (q-a)))
  let L : PreparedSeats a q := ⟨resident.result,childSeats⟩
  have cnt : ord.length=Fintype.card E := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (rosterIndex ord on.1 on.2)
  have proof : ResidentReceipt Q i precision.val L.native :=
    ⟨ord,on.1,on.2,cnt.trans_lt hfit,qfit,hcp,seats,em,ms,nd,all,raws,rawND,weights,rfl⟩
  have R := exact_installed_export_in_source_order F hfit z hTags P hrow hcol hb hFormat hZ ha hRel i
    axis clock resident.result.seats rfl raw (List.length_map ..) (3*(F.kR+F.kC)+9) hq
  refine ⟨Q,L,?_,rfl,⟨proof⟩,rfl,?_⟩
  · change (reorderInstalledSeats q (3*(F.kR+F.kC)+9) g.result.boxes resident.result.seats raw).result.map
      (PreparedSeats.mk resident.result)=some L
    rw [R.1]
    rfl
  · change g.steps+cp.steps+bm.steps+rs.steps+6+S.steps+4+
      (reorderInstalledSeats q (3*(F.kR+F.kC)+9) g.result.boxes resident.result.seats raw).steps+5≤_
    change g.steps≤_ at gFee
    change rs.steps≤_ at rf
    change g.result.boxes.length=2^(6*a)*2^(6*a) at hB
    change exportRows g.result.boxes=Fintype.card E at hR
    rw [hB,hR] at rf
    have cfee : cp.steps=2+6*(q+1) := fit_word_fee _ _
    have mFee : bm.steps≤childMaskBankFee a (q+1) P.copies := mf
    have rFee : rs.steps≤buildCap a (q+1) (2^(6*a)*2^(6*a)) (Fintype.card E)
        (rowTraffic F.kR F.kC F.b q a) P.copies (2^(i.val+1)) precision.val := rf
    have B : g.steps+cp.steps+bm.steps+rs.steps+6≤greedyResidentFee F q i.val P.copies precision.val :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add gFee cfee.le) mFee) rFee) 6
    have body := Nat.add_le_add_right (Nat.add_le_add B seatFee) 4
    exact Nat.add_le_add_right (Nat.add_le_add body R.2) 5

#print axioms generate_stable_residents_and_native_rows
end
end J6R49SourceLayout