import J6R32ChildResidentTransferMask
import J6R31RootResidentTablesSeat
import J6R17ModeTapeLayout

/-! A new admitted orientation convention for a paid greedy descendant.
The labels/copy count come from the literal collision routine and the
mode list from its actual exported headers. Recharting is not an
assertion that the old chosen seats equal the emitted stable rank seats. -/
namespace J6R32ChildResidentTransfer
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open P11FullPacking J6R10Repack J6R27OriginalGate J6R15ModeCost J6R17ModeTape
open J6R31RootResidentTables J6R14LayoutCost J6R24LegalLayout
open J6R12CollisionEdges J6R12CollisionGreedyStep
set_option maxHeartbeats 13000000

noncomputable def remask {E R C : Type} {N : Network E R C} {a : ℕ}
    (P : PhysicalPacking N a (Fin 64)) : PhysicalPacking N a (Fin 64) where
  rowLabel := P.rowLabel
  colLabel := P.colLabel
  copies := P.copies
  mask := childMask a P.copies
  seat := (P.seat.trans (twistChart P.mask).toEmbedding).trans (twistChart (childMask a P.copies)).toEmbedding
  exactCell e := by
    change physicalCell (childMask a P.copies)
      (twistSeat (childMask a P.copies) (twistSeat P.mask (P.seat e)))=_
    rw [twist_preserves_ordered_cell]
    have h := twist_preserves_ordered_cell P.mask (twistSeat P.mask (P.seat e))
    rw [twist_seat_involutive] at h
    rw [←h]
    exact P.exactCell e
  paddedBudget := P.paddedBudget

theorem remask_chart {E R C : Type} {N : Network E R C} {a : ℕ}
    (P : PhysicalPacking N a (Fin 64)) :
    (remask P).rowLabel=P.rowLabel ∧ (remask P).colLabel=P.colLabel ∧
      (remask P).copies=P.copies ∧ (remask P).mask=childMask a P.copies :=
  ⟨rfl,rfl,rfl,rfl⟩

structure GreedyRosterInput (q : ℕ) where
  packed : GreedyPackedTape
  copies : Word (q+1)
  masks : List (MaskRow (q+1))
  roster : RawTape (q+1)

def buildGreedyResident (a e r c b q i : ℕ) (targets : List Target)
    (incidence : List (List Bool×List Bool))
    (precision : Word (q+1)) : Meter (GreedyRosterInput q) :=
  let g := packGreedy a e r c b q targets incidence
  let copies := fitWord (q+1) g.result.copies
  let masks := writeChildMaskBank (Nat.succ_pos q) a copies.result
  let roster := buildTape (Nat.succ_pos q) a i (rowTraffic r c b q a) g.result.boxes copies.result precision
  ⟨⟨g.result,copies.result,masks.result,roster.result⟩,g.steps+copies.steps+masks.steps+roster.steps+6⟩

def greedyResidentFee {E R C : Type} [Fintype E] [Fintype R] [Fintype C]
    {a : ℕ} (F : Format E R C (Fin a→Fin 64)) (q i pages p : ℕ) : ℕ :=
  packGreedyCap a q F + (2+6*(q+1)) + childMaskBankFee a (q+1) pages +
    buildCap a (q+1) (2^(6*a)*2^(6*a)) (Fintype.card E)
      (rowTraffic F.kR F.kC F.b q a) pages (2^(i+1)) p + 6

theorem paid_greedy_child_roster {E R C : Type} [Fintype E] [Fintype R] [Fintype C]
    {a : ℕ} (N : Network E R C) (F : Format E R C (Fin a→Fin 64))
    (hrow : F.row=N.row) (hcol : F.col=N.col)
    (hb : F.b=6*a) (hFormat : ∀ x,F.label x=coordinateLabel x)
    (vs : List (R⊕C)) (hn : vs.Nodup) (hall : ∀ v : R⊕C,v∈vs)
    (Δ q : ℕ) (hq : 0<q) (ha : a≤q) (hfit : Fintype.card E<2^q)
    (hr : ∀ v,Nat.card {e : E // N.row e=v}≤Δ)
    (hc : ∀ v,Nat.card {e : E // N.col e=v}≤Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E)
    (hslots : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card E)
    (i : Fin a) (precision : Word (q+1)) (hp : 0<precision.val) :
    let raw := F.edges.map (fun e=>
      (encodeBits F.kR (F.rCode (F.row e)),encodeBits F.kC (F.cCode (F.col e))))
    let out := buildGreedyResident a F.e F.kR F.kC F.b q i.val (vs.map F.target) raw precision
    ∃ P : PhysicalPacking N a (Fin 64),
      P.mask=childMask a P.copies ∧ out.result.copies.val=P.copies ∧
      out.result.masks=(orderedChildPages a P.copies).map (encodeMaskRow P.mask) ∧
      (∃ ms : List (PacketMode i P.copies (2^(i.val+1)) precision.val),
        ms.Nodup ∧ (∀ m,m∈ms) ∧ out.result.roster.modes=ms.map (encodeMode i) ∧
        out.result.roster.modes.Nodup ∧ out.result.roster.weights.map Word.val=ms.map modeWeight ∧
        out.result.roster.precision=precision) ∧
      out.steps≤greedyResidentFee F q i.val P.copies precision.val := by
  let raw := F.edges.map (fun e=>
    (encodeBits F.kR (F.rCode (F.row e)),encodeBits F.kC (F.cCode (F.col e))))
  let g := packGreedy a F.e F.kR F.kC F.b q (vs.map F.target) raw
  obtain ⟨z,P,hZ,hLabels,hQ,hCopy,hRel,hTags,gFee⟩ :=
    packGreedy_exact N F hrow hcol hb hFormat vs hn hall Δ q hq ha hfit hr hc hcollision hslots
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
    buildTape_exact (Nat.succ_pos q) i hi traffic g.result.boxes cs hH hN hA
      cp.result precision hcp rfl hp
  refine ⟨remask P,rfl,hcp,em,⟨ms,nd,all,raws,rawND,weights,rfl⟩,?_⟩
  change g.steps+cp.steps+bm.steps+rs.steps+6≤greedyResidentFee F q i.val P.copies precision.val
  change g.steps≤_ at gFee
  change bm.steps≤_ at mf
  change rs.steps≤_ at rf
  change g.result.boxes.length=2^(6*a)*2^(6*a) at hB
  change exportRows g.result.boxes=Fintype.card E at hR
  rw [hB,hR] at rf
  have cfee : cp.steps=2+6*(q+1) := fit_word_fee _ _
  have mFee : bm.steps≤childMaskBankFee a (q+1) P.copies := mf
  have rFee : rs.steps≤buildCap a (q+1) (2^(6*a)*2^(6*a)) (Fintype.card E)
      (rowTraffic F.kR F.kC F.b q a) P.copies (2^(i.val+1)) precision.val := rf
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add gFee cfee.le) mFee) rFee) 6

#print axioms remask_chart
#print axioms paid_greedy_child_roster
end J6R32ChildResidentTransfer