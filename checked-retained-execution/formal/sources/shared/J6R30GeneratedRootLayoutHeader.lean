
import J6R24LegalLayoutTags
import J6R24LegalLayoutBudget
import J6R29BinaryFieldSearchRoot
import J6R27PrescribedProbeBits

/-! Issue the actual compact root tape for the deterministic stable
all-zero diagonal chart. The planted cutoff is built by scanning the
finite input-port record list, then prepending the layer-zero bits.
No pre-serialized cutoff, cell key, or root seat list is an input. -/
namespace J6R30GeneratedRootLayout
open scoped Classical
open P11FullPacking J6Mesh J6OrientedHost J6RecursiveOrientation J6R14LayoutCost
open J6R24LegalLayout J6R28GeneratedRootFrame J6R27PrescribedProbe
open A1R10 AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul
open J6R12CollisionEdges
set_option maxHeartbeats 9000000
set_option maxRecDepth 1900

def countRecords (q : ℕ) {D : Type*} (one : Word q) (before : Word q) :
    List D→Meter (Word q)
  | [] => ⟨before,4⟩
  | _::xs =>
    let inc := addWord before one
    let rest := countRecords q one inc.result xs
    ⟨rest.result,inc.steps+rest.steps+6⟩

theorem count_records_exact (q : ℕ) {D : Type*} (hq : 0<q)
    (j : ℕ) (xs : List D) (fit : j+xs.length<2^q) :
    let A := countRecords q (wordOne q) (encoded q j) xs
    A.result=encoded q (j+xs.length) ∧ A.steps=4+xs.length*(12*q+6) := by
  induction xs generalizing j with
  | nil => simp [countRecords]
  | cons x xs ih =>
    have hj : j+1<2^q := by simp only [List.length_cons] at fit; omega
    have ht : (j+1)+xs.length<2^q := by simp only [List.length_cons] at fit; omega
    obtain ⟨r,c⟩ := encoded_succ q j hq hj
    obtain ⟨s,t⟩ := ih (j+1) ht
    simp only [countRecords,r,c,s,t,List.length_cons,Nat.succ_mul]
    constructor
    · congr 1
      omega
    · omega

theorem zero_prefix_value (n : ℕ) (xs : List Bool) :
    bitsValue (List.replicate n false++xs)=2^n*bitsValue xs := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ,List.cons_append,bitsValue,ih,pow_succ]
    simp only [Bool.toNat_false,zero_add]
    ring

theorem zero_symbols (n : ℕ) :
    symbolTape (List.replicate n (0:Fin 64))=List.replicate (6*n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change symbol 0++symbolTape (List.replicate n (0:Fin 64))=_
    rw [show symbol (0:Fin 64)=List.replicate 6 false by decide,ih,
      ←List.replicate_add]
    congr 1
    omega

theorem zero_diagonal_cell_bits (m : ℕ) :
    wordCell (diagonal (constantRootWord m))=
      (List.replicate (6*a m) false,List.replicate (6*a m) false) := by
  have H : coordinateLabel (constantRootWord m)=List.replicate (6*a m) false := by
    unfold coordinateLabel constantRootWord
    rw [List.ofFn_const,zero_symbols]
  exact Prod.ext H H

theorem root_count_high_fit (m : ℕ) : m<2^(printedRankWidth m-a m) := by
  obtain ⟨_,ha,hp⟩ := printed_rank_width m
  have T : K m*2^(a m)<2^(printedRankWidth m-a m)*2^(a m) := by
    rw [←pow_add,Nat.sub_add_cancel ha]
    exact hp
  have Q := (Nat.mul_le_mul_right (2^(a m)) (printed_room m)).trans_lt T
  exact Nat.lt_of_mul_lt_mul_right Q

def RootKey (m : ℕ) := printedRankWidth m-a m

def HeaderFee (m : ℕ) := 4+m*(12*RootKey m+6)+32*a m+12*RootKey m+24

structure RootHeader where
  diagonal : CellWord
  cutoff : List Bool

def rootHeader (m : ℕ) {D : Type*} (literal : List D) : Meter RootHeader :=
  let k := RootKey m
  let n := countRecords k (wordOne k) (encoded k 0) literal
  let z := List.replicate (6*a m) false
  let tr := List.replicate (a m) false++n.result.val
  ⟨⟨(z,z),tr⟩,n.steps+32*a m+12*k+24⟩

theorem root_header_exact (m : ℕ) {D : Type*} (literal : List D) (hl : literal.length=m) :
    let H := rootHeader m literal
    H.result.diagonal=wordCell (diagonal (constantRootWord m)) ∧
    H.result.cutoff=encodeBits (printedRankWidth m) (m*2^a m) ∧
    H.steps=HeaderFee m := by
  let k := RootKey m
  have hFit : m<2^k := root_count_high_fit m
  have hk : 0<k := by unfold k RootKey printedRankWidth; omega
  have h0 : 0+literal.length<2^k := by rwa [Nat.zero_add,hl]
  obtain ⟨r,c⟩ := count_records_exact k hk 0 literal h0
  have hm : m*2^a m<2^printedRankWidth m := by
    have h := Nat.mul_le_mul_right (2^a m) (printed_room m)
    exact h.trans_lt (printed_rank_width m).2.2
  have g : a m+k=printedRankWidth m := by
    unfold k RootKey
    have A := (printed_rank_width m).2.1
    omega
  refine ⟨(zero_diagonal_cell_bits m).symm,?_,?_⟩
  · change List.replicate (a m) false++
      (countRecords k (wordOne k) (encoded k 0) literal).result.val=_
    rw [r,Nat.zero_add,hl]
    apply J6R29BinaryFieldSearch.equal_width_inj
    · rw [List.length_append,List.length_replicate,(encoded k m).property,
        encodeBits_length,g]
    · rw [zero_prefix_value,encodeBits_exact _ _ hm]
      change (2:ℕ)^(a m)*bitsValue (encodeBits k m)=_
      rw [encodeBits_exact _ _ hFit,Nat.mul_comm]
  · change (countRecords k (wordOne k) (encoded k 0) literal).steps+32*a m+12*k+24=_
    rw [c,hl]
    rfl

noncomputable abbrev actualWires (m : ℕ) :=
  orderedWires (constantRootWord m) (printed_room m) (printed_half_correct m)

theorem actual_wires_count (m : ℕ) : (actualWires m).length=M m := by
  unfold actualWires orderedWires
  rw [List.length_map,complete_rank_tape_length,printed_menu_identity m]
  exact mesh_product m

def generatedAnchors (m : ℕ) {D : Type*} (literal : List D) : Meter (List MarkedAnchor) :=
  let label := rootHeader m literal
  let r := compactSeatTape (a m) (K m) (printedRankWidth m) label.result.diagonal label.result.cutoff
  ⟨r.result,label.steps+r.steps+4⟩

def anchorsFee (m : ℕ) :=
  HeaderFee m+printedSeatBudget m+M m*(markFee (a m) (printedRankWidth m)+4)+12

theorem generated_anchors_exact (m : ℕ) {D : Type*} (literal : List D) (hl : literal.length=m) :
    let R := generatedAnchors m literal
    R.result=(actualWires m).map (fun e=>MarkedAnchor.mk
      (anchorAt (printedRankWidth m) (placedRank (constantRootWord m)
        (printed_room m) (printed_half_correct m) e)) (isPlanted e)) ∧
    R.result.length=M m ∧ R.steps≤anchorsFee m := by
  obtain ⟨hq,ha,cap⟩ := printed_rank_width m
  obtain ⟨k,c,f⟩ := root_header_exact m literal hl
  obtain ⟨eq,cost⟩ := compact_seat_tape_exact hq ha cap (constantRootWord m)
    (printed_room m) (printed_half_correct m)
  change (compactSeatTape _ _ _ (rootHeader m literal).result.diagonal
     (rootHeader m literal).result.cutoff).result=_ ∧ _ ∧ _
  have E := eq
  change (compactSeatTape (a m) (K m) (printedRankWidth m)
    (wordCell (diagonal (constantRootWord m))) (encodeBits (printedRankWidth m) (m*2^a m))).result=_ at E
  rw [k,c]
  refine ⟨E,?_,?_⟩
  · change (compactSeatTape (a m) (K m) (printedRankWidth m)
       (rootHeader m literal).result.diagonal (rootHeader m literal).result.cutoff).result.length=M m
    rw [k,c,E,List.length_map,actual_wires_count]
  · change (rootHeader m literal).steps+(compactSeatTape (a m) (K m) (printedRankWidth m)
       (rootHeader m literal).result.diagonal (rootHeader m literal).result.cutoff).steps+4≤_
    change (compactSeatTape (a m) (K m) (printedRankWidth m)
      (wordCell (diagonal (constantRootWord m))) (encodeBits (printedRankWidth m) (m*2^a m))).steps≤
      completeSeatFee (a m) (K m) (printedRankWidth m)+
        (actualWires m).length*(markFee (a m) (printedRankWidth m)+4)+8 at cost
    rw [actual_wires_count] at cost
    rw [k,c,f]
    unfold anchorsFee
    have B := physical_complete_seat_budget m
    omega

#print axioms count_records_exact
#print axioms zero_diagonal_cell_bits
#print axioms root_count_high_fit
#print axioms root_header_exact
#print axioms generated_anchors_exact
end J6R30GeneratedRootLayout
