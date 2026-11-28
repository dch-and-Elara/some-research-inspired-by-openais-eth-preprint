import J6R75RawPeakStockScanner
import J6R75RawPeakStockRegisters

/-! Selected stock-preparation phases on the actual grid, height,
row producer and margin. Retain the real raw grid conservatively
across the row scan and margin. Each cap allows duplicate views;
it is not a statement about automatic physical release. -/
namespace J6R75RawPeak
open AOracleMachineTime A1R10 J6R68ActiveInputs J6R22RootReadout
open J6R52FreshExterior J6R12CollisionMenu J6R12CollisionBits AOracleMachineTimeTape

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3550
set_option maxHeartbeats 8500000
set_option Elab.async false

def stockCoreSetupRoof (a u q : ℕ) : ℕ :=
  a+u+((a+1)*2^(a+1)+(2^(a+1)+2*((a+1+q)*2^(a+1))))+(a+u+16*q+8)

def StockCoreObservation {q : ℕ} (hq : 0<q) (a u : ℕ) (edge taper : J6R15ModeCost.Word q)
    (resident roof : ℕ) : Prop :=
  let A := (ticks a).result
  let U := (ticks u).result
  let G := (signedGridTape a).result
  let H := (heightWord hq edge taper).result
  let zero := (constantRegister q []).result
  let values := scanOrders zero H A U G
  let out := paidStockAndMargin hq a u edge taper
  let read := readOrder zero H A U
  let keep := resident+(A.length+U.length)
  let room := roof+stockCoreSetupRoof a u q
  out.result.rows=values.result ∧
  out.result.margin=(stockMarginFields a (modeWordAsA edge) H).2.result ∧
  keep+(gridMemoryBits G+qBankWords (stockHeightFields hq edge taper).1)≤room ∧
  keep+(gridMemoryBits G+(stockRowsBits out.result.rows+qBankWords (stockMarginFields a (modeWordAsA edge) H).1))≤room ∧
  (∀ (pre : List (List Bool)) (bits : List Bool) (post : List (List Bool)),
    G=pre++bits::post →
    values=(pre.map read).foldr stockReturn (stockReturn (read bits) (scanOrders zero H A U post)) ∧
    let live := scanOrderLiveWords zero H A U G pre bits post
    let captured := edge.bits.length+taper.bits.length+H.val.length+zero.val.length
    keep+(live+captured)≤room ∧
    ∀ (level : List Bool), (rawSignedLevel A bits).result=some level →
      let left := dropTicks U level
      let acc := accumulateTicks zero H left.result
      let test := sameBits acc.result.val zero.val
      read bits=⟨if test.result then none else some ⟨bits,acc.result⟩,
        (rawSignedLevel A bits).steps+left.steps+acc.steps+test.steps+7⟩ ∧
      keep+((live+captured)+(level.length+left.result.length+acc.result.val.length+1))≤room)

theorem true_stock_producer_has_the_named_internal_phase_bounds
    {q : ℕ} (hq : 0<q) (a u : ℕ) (edge taper : J6R15ModeCost.Word q)
    (resident roof : ℕ) (fit : resident≤roof) :
    StockCoreObservation hq a u edge taper resident roof := by
  let A := (ticks a).result
  let U := (ticks u).result
  let G := (signedGridTape a).result
  let H := (heightWord hq edge taper).result
  let zero := (constantRegister q []).result
  let out := paidStockAndMargin hq a u edge taper
  let keep := resident+(A.length+U.length)
  let Q := 2^(a+1)
  let grid := (a+1)*Q
  let rows := (a+1+q)*Q
  let room := roof+stockCoreSetupRoof a u q
  have widthA : A.length=a := (ticks_exact a).1
  have widthU : U.length=u := (ticks_exact u).1
  have gl : G.length=Q := (congrArg List.length (paid_grid_exact a).1).trans (binary_length (a+1))
  have gw (x : List Bool) (mem : x∈G) : x.length=a+1 :=
    (binary_mem _ x).1 ((paid_grid_exact a).1 ▸ mem)
  have gBits : gridMemoryBits G=grid := by rw [uniform_grid_bits (a+1) G gw,gl]
  have b := stock_filtered_rows_exact_bit_width zero H A U (a+1) G gw
  have rawRows : stockRowsBits out.result.rows≤rows := by
    change stockRowsBits (scanOrders zero H A U G).result≤rows
    rw [raw_stock_scan_returns_only_actual_row_results,b.1]
    exact Nat.mul_le_mul_left _ (b.2.trans_eq gl)
  have hbits := (actual_stock_height_has_the_selected_fixed_words hq edge taper).2
  have mbits := (actual_stock_margin_has_the_selected_fixed_words a (modeWordAsA edge) H).2
  have keepFit : keep≤roof+(a+u) := by
    unfold keep
    rw [widthA,widthU]
    exact Nat.add_le_add_right fit _
  have asBudget : room=(roof+(a+u))+(grid+(Q+2*rows)+(a+u+16*q+8)) := by
    simp only [room,stockCoreSetupRoof,grid,Q,rows]
    omega
  refine ⟨rfl,rfl,?_,?_,?_⟩
  · change keep+(gridMemoryBits G+qBankWords (stockHeightFields hq edge taper).1)≤room
    rw [gBits,hbits,asBudget]
    exact Nat.add_le_add keepFit (by omega)
  · change keep+(gridMemoryBits G+(stockRowsBits out.result.rows+_))≤room
    rw [gBits,mbits,asBudget]
    exact Nat.add_le_add keepFit (by omega)
  · intro pre bits post split
    change G=pre++bits::post at split
    obtain ⟨scan,fitScan⟩ := actual_stock_scan_retains_only_its_named_grid_and_row_words
      zero H A U (a+1) G pre bits post split gw
    rw [gl] at fitScan
    let live := scanOrderLiveWords zero H A U G pre bits post
    have words : edge.bits.length+taper.bits.length+H.val.length+zero.val.length=4*q := by
      rw [edge.size,taper.size,H.property,zero.property]
      omega
    have endFit : keep+(live+4*q)≤(roof+(a+u))+(grid+(Q+2*rows)+(a+u+16*q+8)) :=
      Nat.add_le_add keepFit (by change live≤grid+Q+2*rows at fitScan; omega)
    refine ⟨scan,?_,?_⟩
    · change keep+(live+(edge.bits.length+taper.bits.length+H.val.length+zero.val.length))≤room
      rwa [words,asBudget]
    · intro level lev
      have inG : bits∈G := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
      have signed := (signed_raw_valuation_is_exact a A bits widthA (gw bits inG)).1
      have onLevel : (rawSignedLevel A bits).result=some level := lev
      rw [onLevel] at signed
      have valMax : padicValInt 2 (offsetCentre a bits)≤a := by
        simpa only [sub_zero] using P1DyadicGrid.grid_difference_valuation_le
          (offset_word_in_printed_grid a bits (gw bits inG))
          (P1DyadicGrid.zero_mem_grid a) signed.1
      have levelFit : level.length≤a := signed.2.trans_le valMax
      have leftFit : (dropTicks U level).result.length≤u :=
        (drop_ticks_exact U level).1.trans_le ((Nat.sub_le _ _).trans_eq widthU)
      refine ⟨?_,?_⟩
      · unfold readOrder
        dsimp only
        rw [lev]
      · change keep+((live+(edge.bits.length+taper.bits.length+H.val.length+zero.val.length))+
          (level.length+(dropTicks U level).result.length+
            (accumulateTicks zero H (dropTicks U level).result).result.val.length+1))≤room
        rw [words,(accumulateTicks zero H (dropTicks U level).result).result.property,asBudget]
        exact Nat.add_le_add keepFit (by change live≤grid+Q+2*rows at fitScan; omega)

#print axioms true_stock_producer_has_the_named_internal_phase_bounds
end J6R75RawPeak
