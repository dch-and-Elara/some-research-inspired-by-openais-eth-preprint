
import J6R30GeneratedRootLayoutPorts
import J6R26StablePreparedRootSelector

/-! The serialized records use the same stable physical chart installed
at the R26–R29 root. The proof does not identify a different arbitrary
packing. Positive initial binary precision and the unused V dimension
can both be chosen to be one for this legal J6 instance. -/
namespace J6R30GeneratedRootLayout
open scoped Classical Polynomial
open Polynomial Std.Sat
open P11FullPacking J6Mesh J6OrientedHost J6R14LayoutCost J6R24LegalLayout
open J6R28GeneratedRootFrame J6R29BinaryFieldSearch A1R10 AOracleMachineTime AOracleMachineTimeTape
open J1PPrinted J6R26StablePreparedRoot
set_option maxHeartbeats 11000000
set_option maxRecDepth 1900

theorem root_key_width_exact (m : ℕ) : RootKey m=524184*b m+1 := by
  unfold RootKey printedRankWidth K
  rw [Nat.clog_pow 2 _ (by decide)]
  omega

theorem serialized_same_stable_seat {V : Type} [Fintype V] {m n r c d : ℕ}
    {T : Plant V m n} (P : LiteralPortFile T r c d) (e : RootWire m) :
    let raw := (trueMounted P e).base.anchor.anchor.physical.seat
    let shape := printed_rank_width m
    let chart := stableRootPacking m (printedHalf m) n (printedRankWidth m) T
      (constantRootWord m) (printed_room m) (printed_half_correct m) shape.2.1 shape.2.2.le
    ∃ h : bitsValue raw.page<K m,
      decodePhysical (rankAt m e).1 raw h=chart.seat e := by
  exact anchor_decodes (printed_rank_width m).2.1 (printed_rank_width m).2.2.le (rankAt m e)

theorem serialized_cell_same_stable {V : Type} [Fintype V] {m n r c d : ℕ}
    {T : Plant V m n} (P : LiteralPortFile T r c d) (e : RootWire m) :
    let shape := printed_rank_width m
    let chart := stableRootPacking m (printedHalf m) n (printedRankWidth m) T
      (constantRootWord m) (printed_room m) (printed_half_correct m) shape.2.1 shape.2.2.le
    (trueMounted P e).base.anchor.anchor.cell=
      wordCell (physicalCell (fun _ _ _=>false) (chart.seat e)) := by
  have H := deterministic_legal_cell (printed_rank_width m).2.1 (printed_rank_width m).2.2.le
    (constantRootWord m) (printed_room m) (printed_half_correct m) e
  exact congrArg wordCell H.symm

noncomputable def rootWireOrder (m : ℕ) : Fin (M m)≃RootWire m :=
  Equiv.ofBijective (fun i : Fin (M m)=>
    (actualWires m).get (Fin.cast (actual_wires_count m).symm i)) (by
      have C := ordered_wires_exact (constantRootWord m) (printed_room m) (printed_half_correct m)
      constructor
      · intro i j H
        have eq := C.1.get_inj_iff.mp H
        exact Fin.ext (congrArg (fun x : Fin (actualWires m).length=>x.val) eq)
      · intro e
        obtain ⟨i,h⟩ := List.mem_iff_get.mp (C.2 e)
        refine ⟨Fin.cast (actual_wires_count m) i,?_⟩
        convert h using 1)

theorem root_wire_order_exact (m : ℕ) :
    List.ofFn (rootWireOrder m)=actualWires m := by
  apply List.ext_getElem (by rw [List.length_ofFn,actual_wires_count m])
  intro i h₁ h₂
  rw [List.getElem_ofFn]
  rfl

noncomputable def stableWireKeyWord (m : ℕ) (e : RootWire m) :
    J6R15ModeCost.Word (12*a m+printedRankWidth m) :=
  ⟨(expectedBase m e).key,base_key_width m e⟩

theorem stable_wire_key_injective (m : ℕ) : Function.Injective (stableWireKeyWord m) := by
  intro x y h
  exact base_key_injective m (congrArg J6R15ModeCost.Word.bits h)

theorem root_file_indexed {V : Type*} {m n r c d : ℕ} {T : Plant V m n}
    (P : LiteralPortFile T r c d) :
    let o := rootWireOrder m
    (generatedPaddedPorts m P.raw).result=List.ofFn (fun j=>trueMounted P (o j)) ∧
      ((generatedPaddedPorts m P.raw).result.map fun x=>x.base.key) =
        List.ofFn (fun j=>(stableWireKeyWord m (o j)).bits) := by
  have h := (generated_padded_ports_exact P).1
  rw [←root_wire_order_exact m,List.map_ofFn] at h
  exact ⟨h,by rw [h,List.map_ofFn];rfl⟩

theorem literal_port_bits_decode {V : Type*} {m n r c d : ℕ}
    (T : Plant V m n) (C : LiteralCodec T r c d) (u : Fin m) :
    let raw := plantHalfPort T C u
    let x := T.rowPort.symm u
    let y := T.colPort.symm u
    raw.row=C.rowCode x.1 ∧ bitsValue raw.leg.val=x.2.val ∧
      bitsValue raw.column.val=y.1.val ∧ raw.side=y.2 ∧ raw.flag=flagAt (T.old x.1) x.2 := by
  refine ⟨rfl,?_,?_,rfl,rfl⟩
  · exact encodeBits_exact _ _ ((T.rowPort.symm u).2.isLt.trans_le (C.portFit _))
  · exact encodeBits_exact _ _ ((T.colPort.symm u).1.isLt.trans_le C.columnFit)

variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V}
local notation "ms" => J7R10Readout.mCNF
local notation "inp" => J7R10Readout.H

noncomputable abbrev CNFPortFile (F : CNF V) (r c d : ℕ) :=
  LiteralPortFile (J7R10Plant.physicalPlant (inp F)) r c d

omit [Nonempty V] in
theorem generated_cnf_layout_file {r c d : ℕ} (P : CNFPortFile F r c d) :
    let run := generatedPaddedPorts (ms F) P.raw
    run.result=(actualWires (ms F)).map (trueMounted P) ∧ run.result.length=M (ms F) ∧
      (run.result.map (fun row=>row.base.key)).Nodup ∧ run.steps≤paddedPortsFee (ms F) r c d :=
  generated_padded_ports_exact P

def unitRootGuard (F : CNF V) (h3 : ∀ c∈F,c.length≤3)
    (large : (2*epsDen)^30*(2:ℕ)^10≤Nat.clog 2 (physicalSize (ms F) (literalNativeSize F))) :
    PrintedRootGuard F 1 :=
  ⟨by decide,h3,large⟩

theorem unit_precision_literal_count (F : CNF V) (h3 : ∀ c∈F,c.length≤3)
    (large : (2*epsDen)^30*(2:ℕ)^10≤Nat.clog 2 (physicalSize (ms F) (literalNativeSize F)))
    (children : (generatedField (unitRootGuard F h3 large)).result.children 1) :
    let R := countBySearchedField (unitRootGuard F h3 large) 1 (by decide) children
    bitsValue R.result.val=PinnedCNF.modelCount F :=
  (literal_searched_field_count (unitRootGuard F h3 large) 1 (by decide) children).1

#print axioms root_key_width_exact
#print axioms serialized_same_stable_seat
#print axioms serialized_cell_same_stable
#print axioms root_wire_order_exact
#print axioms stable_wire_key_injective
#print axioms root_file_indexed
#print axioms literal_port_bits_decode
#print axioms generated_cnf_layout_file
#print axioms unit_precision_literal_count
end J6R30GeneratedRootLayout
