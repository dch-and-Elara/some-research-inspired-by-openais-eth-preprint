import J6R68ActiveInputsProducer
import J6R75RawPeakStockScanner

/-! Bit encodings of the actual R14/R12 raw layout tapes. The
charging units below are fields, not pointers or unencoded proofs.
One presence bit is allowed for a replicated endpoint label. -/
namespace J6R75RawPeak
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionPacking
open J6R14LayoutCost J6R12CollisionMenu J6R68ActiveInputs P11FullPacking

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000
set_option maxRecDepth 3900
set_option Elab.async false

def rawLayoutBits {A : Type*} (view : A→ℕ) (xs : List A) : ℕ := (xs.map view).sum

theorem raw_layout_bits_append {A : Type*} (view : A→ℕ) (a b : List A) :
    rawLayoutBits view (a++b)=rawLayoutBits view a+rawLayoutBits view b := by
  simp [rawLayoutBits,List.map_append,List.sum_append]

theorem raw_layout_bits_fixed {A : Type*} (view : A→ℕ) (width : ℕ) (xs : List A)
    (h : ∀ x∈xs,view x=width) :
    rawLayoutBits view xs=width*xs.length := by
  induction xs with
  | nil=>simp [rawLayoutBits]
  | cons x xs ih=>
    change view x+rawLayoutBits view xs=width*(xs.length+1)
    rw [h x List.mem_cons_self,ih (fun y hY=>h y (List.mem_cons_of_mem _ hY)),Nat.mul_succ,Nat.add_comm]

def rawEndLayoutBits (x : EndTape) : ℕ :=
  x.addr.length+1+(x.label.map List.length).getD 0

def rawEdgeLayoutBits (x : EdgeTape) : ℕ :=
  rawEndLayoutBits x.row+rawEndLayoutBits x.col

def rawTaggedLayoutBits (x : Tagged) : ℕ :=
  x.serial.length+rawEdgeLayoutBits x.edge

def rawCellLayoutBits (k : CellWord) : ℕ :=
  k.1.length+k.2.length

def rawBoxLayoutBits (b : Box Tagged) : ℕ :=
  rawCellLayoutBits b.key+b.count.length+rawLayoutBits rawTaggedLayoutBits b.rows

def rawAxisLayoutBits (x : AxisWord) : ℕ :=
  x.low.length+x.high.length+2

def rawAddressLayoutBits (x : SeatWords) : ℕ :=
  x.slot.length+x.selector.length+x.page.length

def rawSeatedLayoutBits (x : Seated) : ℕ :=
  rawTaggedLayoutBits x.tag+rawAddressLayoutBits x.address

def rawExportLayoutBits (x : ExportBox) : ℕ :=
  rawCellLayoutBits x.key+rawLayoutBits rawAxisLayoutBits x.axes+
    2*x.flags.length+rawLayoutBits rawSeatedLayoutBits x.rows

def fullEdgeLayoutWidth (kr kc b : ℕ) : ℕ := kr+kc+2*b+2

section Labeled
variable {E R C A : Type*} [Fintype E] [Fintype A]
variable (F : Format E R C A) (z : R⊕C→A)

theorem source_graph_layout_record_has_actual_fixed_width
    (e : EdgeTape) (mem : e∈F.graph (fun x=>some (z x))) :
    rawEdgeLayoutBits e=fullEdgeLayoutWidth F.kR F.kC F.b := by
  obtain ⟨wire,_,rfl⟩ := List.mem_map.mp mem
  simp only [rawEdgeLayoutBits,rawEndLayoutBits,packEdge,packEnd,Option.map_some,Option.getD_some,
    encodeBits_length,fullEdgeLayoutWidth]
  omega

theorem source_graph_layout_bytes_are_exact :
    rawLayoutBits rawEdgeLayoutBits (F.graph (fun x=>some (z x)))=
      fullEdgeLayoutWidth F.kR F.kC F.b*Fintype.card E := by
  rw [raw_layout_bits_fixed _ _ _ (source_graph_layout_record_has_actual_fixed_width F z)]
  simp only [Format.graph,List.length_map,F.graphEdges]

theorem source_tag_width_of_real_occurrence (q : ℕ) (t : Tagged)
    (hit : t∈tagSpec q 0 (F.graph (fun x=>some (z x)))) :
    rawTaggedLayoutBits t=q+fullEdgeLayoutWidth F.kR F.kC F.b := by
  have edge : t.edge∈F.graph (fun x=>some (z x)) := by
    rw [← tagSpec_edge q 0 (F.graph (fun x=>some (z x)))]
    exact List.mem_map_of_mem hit
  have width (j : ℕ) (es : List EdgeTape)
      (h : t∈tagSpec q j es) : t.serial.length=q := by
    induction es generalizing j with
    | nil=>simp [tagSpec] at h
    | cons b bs ih=>
      simp only [tagSpec,List.mem_cons] at h
      rcases h with eq|tail
      · subst t
        exact encodeBits_length _ _
      · exact ih _ tail
  unfold rawTaggedLayoutBits
  rw [width 0 _ hit,source_graph_layout_record_has_actual_fixed_width F z t.edge edge]

theorem entire_source_tag_tape_has_actual_bit_width (q : ℕ) :
    rawLayoutBits rawTaggedLayoutBits (tagSpec q 0 (F.graph (fun x=>some (z x))))=
      (q+fullEdgeLayoutWidth F.kR F.kC F.b)*Fintype.card E := by
  rw [raw_layout_bits_fixed _ _ _ (source_tag_width_of_real_occurrence F z q),tagSpec_length]
  simp only [Format.graph,List.length_map,F.graphEdges]
end Labeled

theorem actual_pair_key_table_bits (b : ℕ) :
    rawLayoutBits rawCellLayoutBits (allPairsMachine b).result=(2*b)*(2^b*2^b) := by
  rw [(allPairsMachine_exact b).1]
  have key (k : CellWord) (mem : k∈allPairs b) : rawCellLayoutBits k=2*b := by
    obtain ⟨l,r⟩ := (allPairs_mem b k).mp mem
    unfold rawCellLayoutBits
    omega
  rw [raw_layout_bits_fixed _ _ _ key,allPairs_len]

theorem actual_stock_layout_row_counts_encode_once
    (cells : List (Box Tagged)) (b q w : ℕ)
    (heads : ∀ B∈cells,rawCellLayoutBits B.key=2*b ∧ B.count.length=q)
    (rows : ∀ B∈cells,∀ t∈B.rows,rawTaggedLayoutBits t=w) :
    rawLayoutBits rawBoxLayoutBits cells=(2*b+q)*cells.length+w*rowsOnTape cells := by
  induction cells with
  | nil=>simp [rawLayoutBits,rowsOnTape]
  | cons cell todo ih=>
    obtain ⟨left,right⟩ := heads cell List.mem_cons_self
    have qRows := raw_layout_bits_fixed rawTaggedLayoutBits w cell.rows (rows cell List.mem_cons_self)
    have eq := ih (fun x hx=>heads x (List.mem_cons_of_mem _ hx))
      (fun x hx=>rows x (List.mem_cons_of_mem _ hx))
    change rawBoxLayoutBits cell+rawLayoutBits rawBoxLayoutBits todo=
      (2*b+q)*(todo.length+1)+w*rowsOnTape (cell::todo)
    have sum : rowsOnTape (cell::todo)=cell.rows.length+rowsOnTape todo := by simp [rowsOnTape]
    rw [rawBoxLayoutBits,left,right,qRows,eq,sum,Nat.mul_succ,Nat.mul_add]
    omega

section Native
variable {E R C : Type*} [Fintype E] {a : ℕ}
variable (F : Format E R C (Fin a→Fin 64)) (z : R⊕C→Fin a→Fin 64)

theorem actual_source_boxes_have_their_grouped_word_width (q : ℕ) :
    rawLayoutBits rawBoxLayoutBits (sourceBoxes F z q)=
      (2*F.b+q)*(2^F.b*2^F.b)+(q+fullEdgeLayoutWidth F.kR F.kC F.b)*Fintype.card E := by
  have shape (B : Box Tagged) (mem : B∈sourceBoxes F z q) :
      rawCellLayoutBits B.key=2*F.b ∧ B.count.length=q := by
    unfold sourceBoxes at mem
    obtain ⟨k,there,rfl⟩ := List.mem_map.mp mem
    obtain ⟨l,r⟩ := (allPairs_mem F.b k).mp there
    refine ⟨?_,encodeBits_length _ _⟩
    change k.1.length+k.2.length=2*F.b
    rw [l,r]
    omega
  have tags (B : Box Tagged) (mem : B∈sourceBoxes F z q)
      (t : Tagged) (hit : t∈B.rows) :
      rawTaggedLayoutBits t=q+fullEdgeLayoutWidth F.kR F.kC F.b := by
    unfold sourceBoxes at mem
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp mem
    apply source_tag_width_of_real_occurrence F z q t
    exact (List.mem_filter.mp hit).1
  obtain ⟨n,bits⟩ := sourceBoxes_counts F z q
  rw [actual_stock_layout_row_counts_encode_once _ F.b q _ shape tags,n,bits]
end Native

#print axioms raw_layout_bits_fixed
#print axioms source_graph_layout_bytes_are_exact
#print axioms entire_source_tag_tape_has_actual_bit_width
#print axioms actual_pair_key_table_bits
#print axioms actual_source_boxes_have_their_grouped_word_width
end J6R75RawPeak
