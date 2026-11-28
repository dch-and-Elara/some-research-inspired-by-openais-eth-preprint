import J6R53PeakAddonPath
import J6R34RootAtlasOccurrence

/-! A separate selected field of the top-level StoredSite.input record:
the physical PortRow tape read by the mount. This is not the raw
addon tape under StoredSite.site.input, nor the whole OccurrenceInput
record, nor a claim about allocating its dependent Lean fields. -/
namespace J6R54PeakInput
open scoped Polynomial
open AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R16ModeCost J6R33GeneratedChildSite J6R34RootAtlas J6R36ChildFramedRoute
open J6R41StructuredAllPaths J6R50SourceProducer J6R51Peak J6R51Online J6R51ParentFrames J6R53PeakAddon

set_option autoImplicit false
set_option maxRecDepth 3750
set_option maxHeartbeats 19500000
noncomputable section

def physicalPortWords {w : ℕ} (x : PortRow w) : List Bool :=
  x.address.bits++x.group.bits++x.body

theorem physical_port_words_exact {w : ℕ} (x : PortRow w) :
    (physicalPortWords x).length=w+6+x.body.length := by
  simp only [physicalPortWords,List.length_append,x.address.size,x.group.size,Nat.add_assoc]

theorem raw_port_tape_uniform {w : ℕ} (xs : List (PortRow w)) (body : ℕ)
    (fits : ∀ x∈xs,x.body.length≤body) :
    (xs.flatMap physicalPortWords).length≤xs.length*(w+6+body) := by
  apply flat_words_bound
  intro x hx
  rw [physical_port_words_exact]
  exact Nat.add_le_add_left (fits x hx) _

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}
local notation "P" => (Plan sel)

def birthPhysicalBitTape (B : Birth T v key prec tw bw page) : List Bool :=
  B.native.physical.raw.flatMap physicalPortWords

def sourcePhysicalBitTape (I : OccurrenceInput T v key prec tw bw page) : List Bool :=
  I.native.result.physical.raw.flatMap physicalPortWords

theorem page_width_cast_does_not_change_physical_port_tape {a b : ℕ} (h : a=b)
    (Q : Birth T v key prec tw bw a) :
    birthPhysicalBitTape (h ▸ Q : Birth T v key prec tw bw b)=birthPhysicalBitTape Q := by
  cases h
  rfl

theorem compiled_occurrence_uses_same_physical_port_tape
    (I : OccurrenceInput T v key prec tw bw page) :
    birthPhysicalBitTape (compileOccurrence I)=sourcePhysicalBitTape I := by
  let real := Classical.choice (occurrence_real_receipt I)
  let issued := padCost I.issued (I.native.steps+I.physical.steps+I.words.steps+4)
  let Q := issuedBirth I.native.result issued I.words.result I.hOld real
  change birthPhysicalBitTape (I.width ▸ Q : Birth T v key prec tw bw page)=_
  exact page_width_cast_does_not_change_physical_port_tape I.width Q

theorem actual_mount_consumes_the_same_ordered_port_file
    (X : StoredSite T v key prec tw bw page) (bank : AddonRows X.site) :
    let B := X.birth
    paidParentFrames X.site bank=
      selectedFrame B.native.gWord B.native.physical.raw bank B.issuance.result B.native.receiving ∧
    (B.native.physical.raw.flatMap physicalPortWords)=sourcePhysicalBitTape X.input := by
  exact ⟨rfl,compiled_occurrence_uses_same_physical_port_tape X.input⟩

theorem counted_actual_port_file_has_two_rows_per_parent_edge
    (X : StoredSite T v key prec tw bw page) :
    X.birth.native.physical.raw.length=2*v.parent.edges := by
  let P0 := X.birth.native.physical
  have aligned : X.site.input.length=P0.order.length := by
    rw [X.site.aligned,List.length_map]
    rfl
  have n : P0.order.length=2*v.parent.edges :=
    aligned.symm.trans (actual_addon_tapes_count_both_half_ports X.site).1
  change P0.raw.length=_
  rw [P0.source,List.length_map,n]

theorem actual_demanded_occurrence_port_bits_uniform
    (M : OnlineMachine T key prec tw bw page q) (fixed addr seed : ℕ)
    (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed)
    (p : Path sel r c) (w : (P).Slot c) :
    (sourcePhysicalBitTape (sourceState M p w).input).length≤
      (2*c.edges)*(addr+sourceBodyCap s C seed) := by
  let X := sourceState M p w
  let P0 := X.birth.native.physical
  let U := sourceBodyCap s C seed
  have payload : P0.raw.flatMap physicalPortWords=sourcePhysicalBitTape X.input :=
    compiled_occurrence_uses_same_physical_port_tape X.input
  have bound := raw_port_tape_uniform P0.raw U (fun row mem=>by
    rw [P0.source] at mem
    obtain ⟨h,_,eq⟩ := List.mem_map.mp mem
    rw [←eq]
    exact actual_demanded_body_fits M seed boot p w h)
  have n : P0.raw.length=2*c.edges := counted_actual_port_file_has_two_rows_per_parent_edge X
  have H : X.birth.port+6≤addr := (sizes p w).2
  rw [payload,n] at bound
  exact bound.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right H _))

#print axioms physical_port_words_exact
#print axioms raw_port_tape_uniform
#print axioms page_width_cast_does_not_change_physical_port_tape
#print axioms compiled_occurrence_uses_same_physical_port_tape
#print axioms actual_mount_consumes_the_same_ordered_port_file
#print axioms counted_actual_port_file_has_two_rows_per_parent_edge
#print axioms actual_demanded_occurrence_port_bits_uniform
end
end J6R54PeakInput
