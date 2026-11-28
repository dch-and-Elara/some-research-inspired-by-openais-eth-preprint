import J6R32ChildResidentTransferInstall
import J6R32ChildResidentTransferRoster

/-! All three resident files come from one actual greedy packing run.
The stable packing can be the successor selector at this site; it is
not identified with a previously arbitrary choice of within-cell seats. -/
namespace J6R32ChildResidentTransfer
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open P11FullPacking J6R14LayoutCost J6R24LegalLayout J6R27OriginalGate J6R15ModeCost
open J6R12CollisionEdges J6R12CollisionGreedyStep
open J6R9PacketScopes J6R10Repack J6R17ModeTape J6R31RootResidentTables
set_option maxHeartbeats 18500000
set_option maxRecDepth 2600

structure ChildResidents (a q : ℕ) where
  raw : GreedyRosterInput q
  seats : List (SeatField a ((q-a)+13*a))

def fullGreedyResident (a e r c b q i : ℕ) (axis : List Bool) (targets : List Target)
    (incidence : List (List Bool×List Bool)) (precision : Word (q+1)) :
    Meter (ChildResidents a q) :=
  let child := buildGreedyResident a e r c b q i targets incidence precision
  let out := writeSeatedBoxes a (q-a) axis child.result.packed.boxes
  ⟨⟨child.result,out.result⟩,child.steps+out.steps+4⟩

def fullGreedyFee {E R C : Type} [Fintype E] [Fintype R] [Fintype C] {a : ℕ}
    (F : Format E R C (Fin a→Fin 64)) (q i pages p : ℕ) : ℕ :=
  greedyResidentFee F q i pages p +
    ((2*maskedSeatFee a (q-a)+12)*Fintype.card E+5*(2^(6*a)*2^(6*a)))+4

theorem packed_copy_bits_fit {E R C : Type} [Fintype E] {N : Network E R C} {a q : ℕ}
    (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (ha : a≤q) (fit : Fintype.card E<2^q) :
    P.copies≤2^(q-a) := by
  have hc : 3≤Nat.card (Cell (Fin a) (Fin 64)) := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_prod,Fintype.card_fin]
    exact (by decide : 3≤(64*64)^1).trans
      (Nat.pow_le_pow_right (by decide) (by have h := i.isLt; omega))
  have h := (Nat.mul_le_mul_right (P.copies*2^a) hc).trans P.paddedBudget
  have h' : P.copies*2^a≤Nat.card E := Nat.le_of_mul_le_mul_left h (by decide)
  have H : P.copies*2^a≤2^(q-a)*2^a := by
    rw [←pow_add,Nat.sub_add_cancel ha]
    exact h'.trans (by rw [Nat.card_eq_fintype_card]; exact fit.le)
  exact Nat.le_of_mul_le_mul_right H (by positivity)

theorem actual_paid_greedy_residents {E R C : Type} [Fintype E] [Fintype R] [Fintype C]
    {a : ℕ} (N : Network E R C) (F : Format E R C (Fin a→Fin 64))
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
    let out := fullGreedyResident a F.e F.kR F.kC F.b q i.val axis (vs.map F.target) raw precision
    ∃ P : PhysicalPacking N a (Fin 64), ∃ order : List E,
      order.Nodup ∧ (∀ e,e∈order) ∧
      P.mask=childMask a P.copies ∧ P.copies≤2^(q-a) ∧
      out.result.seats=order.map (physicalSeatField P i (childPageKey (q-a))) ∧
      out.result.raw.copies.val=P.copies ∧
      out.result.raw.masks=(orderedChildPages a P.copies).map (encodeMaskRow P.mask) ∧
      (∃ ms : List (PacketMode i P.copies (2^(i.val+1)) precision.val),
        ms.Nodup ∧ (∀ m,m∈ms) ∧ out.result.raw.roster.modes=ms.map (encodeMode i) ∧
        out.result.raw.roster.modes.Nodup ∧ out.result.raw.roster.weights.map Word.val=ms.map modeWeight ∧
        out.result.raw.roster.precision=precision) ∧
      out.steps≤fullGreedyFee F q i.val P.copies precision.val := by
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
  refine ⟨Q,ord,on.1,on.2,rfl,qfit,seats,hcp,em,⟨ms,nd,all,raws,rawND,weights,rfl⟩,?_⟩
  let S := writeSeatedBoxes a (q-a) axis g.result.boxes
  change g.steps+cp.steps+bm.steps+rs.steps+6+S.steps+4≤fullGreedyFee F q i.val P.copies precision.val
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
  exact Nat.add_le_add_right (Nat.add_le_add B seatFee) 4

#print axioms packed_copy_bits_fit
#print axioms actual_paid_greedy_residents
end J6R32ChildResidentTransfer