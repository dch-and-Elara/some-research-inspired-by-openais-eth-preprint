import J6R32ChildResidentTransferPorts
import J6R32ChildResidentTransferRoster

/-! Exact raw incidence and target tapes into the paid greedy algorithm.
The child edge list is the actual transferred parent half-ports. A
complete installed vertex-key file is still required on each side;
zero-degree old factors are not silently reconstructed from incidence. -/
namespace J6R32ChildResidentTransfer
open scoped Classical Polynomial
open AOracleMachineTime AOracleMachineTimeTape
open J6R10Repack P11FullPacking J6R11Blueprint J6R9PacketScopes
open J6R15ModeCost J6R26DescriptorTree J6R27OriginalGate J6R17ModeTape
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionMenu J6R14LayoutCost
open J6R29BinaryFieldSearch
set_option maxHeartbeats 16000000
set_option maxRecDepth 2300

def rawLane {r k e w p : ℕ} (x : ChildLane r k e w p) : Meter (List Bool×List Bool) :=
  let left := duplicateWord x.oldKey
  let right := duplicateWord x.pageKey
  ⟨(left.result.bits,right.result.bits),left.steps+right.steps+3⟩

theorem raw_lane_exact {r k e w p : ℕ} (x : ChildLane r k e w p) :
    rawLane x=⟨(x.oldKey.bits,x.pageKey.bits),3*r+3*k+11⟩ := by
  unfold rawLane
  simp only [duplicate_word_exact]
  congr 1
  omega

theorem raw_lanes_exact {r k e w p : ℕ} (xs : List (ChildLane r k e w p)) :
    (mapMeter rawLane xs).result=xs.map (fun x=>(x.oldKey.bits,x.pageKey.bits)) ∧
      (mapMeter rawLane xs).steps≤(3*r+3*k+17)*xs.length :=
  mapMeter_exact rawLane _ (3*r+3*k+11) xs (fun x _=>by
    rw [raw_lane_exact]; exact ⟨rfl,le_rfl⟩)

def writeTargets {r k : ℕ} (rows : List (Word r)) (cols : List (Word k)) : Meter (List Target) :=
  let R := mapMeter (fun x=>let cp := duplicateWord x; ⟨Target.row cp.result.bits,cp.steps+3⟩) rows
  let C := mapMeter (fun x=>let cp := duplicateWord x; ⟨Target.col cp.result.bits,cp.steps+3⟩) cols
  ⟨R.result++C.result,R.steps+C.steps+(3*r+9)*rows.length+4⟩

theorem targets_exact {r k : ℕ} (rows : List (Word r)) (cols : List (Word k)) :
    (writeTargets rows cols).result=rows.map (fun x=>Target.row x.bits) ++ cols.map (fun x=>Target.col x.bits) ∧
      (writeTargets rows cols).steps≤(6*r+22)*rows.length+(3*k+13)*cols.length+4 := by
  obtain ⟨hr,pr⟩ := mapMeter_exact (fun x : Word r=>
    let d := duplicateWord x; ⟨Target.row d.result.bits,d.steps+3⟩)
    (fun x=>Target.row x.bits) (3*r+7) rows (fun x _=>by
      dsimp only; rw [duplicate_word_exact]; exact ⟨rfl,le_rfl⟩)
  obtain ⟨hc,pc⟩ := mapMeter_exact (fun x : Word k=>
    let d := duplicateWord x; ⟨Target.col d.result.bits,d.steps+3⟩)
    (fun x=>Target.col x.bits) (3*k+7) cols (fun x _=>by
      dsimp only; rw [duplicate_word_exact]; exact ⟨rfl,le_rfl⟩)
  dsimp only [writeTargets]
  refine ⟨by rw [hr,hc],?_⟩
  nlinarith only [pr,pc]

noncomputable def childFormat {E R C : Type} [Fintype E] {a r k : ℕ}
    (N : Network E R C) (rank : ℕ) (fit : Fintype.card E<2^rank)
    (edges : List E) (nd : edges.Nodup) (all : ∀ v,v∈edges)
    (rr : R→Word r) (cc : C→Word k)
    (ri : Function.Injective rr) (ci : Function.Injective cc) :
    Format E R C (Fin a→Fin 64) where
  e := rank
  kR := r
  kC := k
  b := 6*a
  rCode := fun v=>(rr v).val
  cCode := fun v=>(cc v).val
  aCode := fun v=>bitsValue (coordinateLabel v)
  rInj := fun _ _ h=>ri ((valued_word _).symm.trans ((congrArg word h).trans (valued_word _)))
  cInj := fun _ _ h=>ci ((valued_word _).symm.trans ((congrArg word h).trans (valued_word _)))
  aInj := by
    intro x y h
    exact coordinateLabel_inj
      (J6R12CollisionMenu.equal_width_inj ((coordinateLabel_len x).trans (coordinateLabel_len y).symm) h)
  rFit := fun i=>val_lt (rr i)
  cFit := fun i=>val_lt (cc i)
  aFit := by intro i; rw [←coordinateLabel_len i]; exact bitsValue_lt _
  edgesFit := fit
  alphabetFit := by rw [source_alphabet (G:=Fin 64) (by simp) a]
  row := N.row
  col := N.col
  edges := edges
  edgesNodup := nd
  edgesAll := all

theorem child_format_label {E R C : Type} [Fintype E] {a r k : ℕ}
    (N : Network E R C) (rank : ℕ) (fit : Fintype.card E<2^rank)
    (edges : List E) (nd : edges.Nodup) (all : ∀ v,v∈edges)
    (rr : R→Word r) (cc : C→Word k)
    (ri : Function.Injective rr) (ci : Function.Injective cc) :
    ∀ x,(childFormat (a:=a) N rank fit edges nd all rr cc ri ci).label x=coordinateLabel x := by
  intro x
  change encodeBits (6*a) (bitsValue (coordinateLabel x))=coordinateLabel x
  apply J6R12CollisionMenu.equal_width_inj
  · rw [encodeBits_length,coordinateLabel_len]
  · exact encodeBits_exact _ _ (by rw [←coordinateLabel_len x]; exact bitsValue_lt _)

theorem typed_target_tape {E R C : Type} [Fintype E] {a r k : ℕ}
    (N : Network E R C) (rank : ℕ) (fit : Fintype.card E<2^rank)
    (edges : List E) (nd : edges.Nodup) (all : ∀ v,v∈edges)
    (rr : R→Word r) (cc : C→Word k)
    (ri : Function.Injective rr) (ci : Function.Injective cc) (rows : List R) (cols : List C) :
    let F := childFormat (a:=a) N rank fit edges nd all rr cc ri ci
    let out := writeTargets (rows.map rr) (cols.map cc)
    out.result=(rows.map Sum.inl++cols.map Sum.inr).map F.target ∧
      out.steps≤(6*r+22)*rows.length+(3*k+13)*cols.length+4 := by
  let F := childFormat (a:=a) N rank fit edges nd all rr cc ri ci
  obtain ⟨m,h⟩ := targets_exact (rows.map rr) (cols.map cc)
  rw [List.length_map,List.length_map] at h
  refine ⟨m.trans ?_,h⟩
  rw [List.map_append,List.map_map,List.map_map,List.map_map,List.map_map]
  congr 1
  · apply List.map_congr_left
    intro x _
    change Target.row (rr x).bits=Target.row (word (q:=r) (rr x).val).bits
    rw [valued_word]
  · apply List.map_congr_left
    intro x _
    change Target.col (cc x).bits=Target.col (word (q:=k) (cc x).val).bits
    rw [valued_word]

#print axioms raw_lanes_exact
#print axioms targets_exact
#print axioms child_format_label
#print axioms typed_target_tape
end J6R32ChildResidentTransfer