import J6R75RawPeakStockScanner

/-! Real signed-grid production as a recursive two-prefix builder.
At one actual return we allow its prior table, both returned halves,
and the concatenated output to coexist. This does not infer release of
any helper's private map/append closure. -/
namespace J6R75RawPeak
open AOracleMachineTime AOracleMachineTimeTape J6R68ActiveInputs
open J6R12CollisionMenu J6R12CollisionEdges J6R12CollisionGreedyStep

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3300
set_option maxHeartbeats 6500000
set_option Elab.async false

inductive StockGridUnwind : ℕ → ℕ → Prop where
  | now (b : ℕ) : StockGridUnwind (b+1) b
  | inside {n b : ℕ} : StockGridUnwind n b → StockGridUnwind (n+1) b

theorem real_stock_grid_unwind_width_le {n b : ℕ} (cut : StockGridUnwind n b) : b<n := by
  induction cut with
  | now b=>exact Nat.lt_succ_self b
  | inside cut ih=>exact ih.trans (Nat.lt_succ_self _)

theorem emitted_menu_grid_bit_width_is_exact (b : ℕ) :
    gridMemoryBits (menuMachine b).result=b*2^b := by
  have eq := (menuMachine_exact b).1
  rw [uniform_grid_bits b (menuMachine b).result (fun x hx=>(binary_mem b x).1 (eq ▸ hx)),
    eq,binary_length]

private theorem prefix_grid_is_the_actual_map (b : ℕ) (v : Bool) (G : List (List Bool)) :
    (prefixMeter b v G).result=G.map (v::·) :=
  (mapMeter_exact (fun q : List Bool=>⟨v::q,2*b+5⟩) (v::·) (2*b+5) G
    (fun _ _=>⟨rfl,le_rfl⟩)).1

theorem actual_grid_return_holds_two_halves_and_one_result
    (a b : ℕ) (actual : StockGridUnwind (a+1) b)
    (resident roof : ℕ) (fit : resident≤roof) :
    let earlier := menuMachine b
    let zero := prefixMeter b false earlier.result
    let one := prefixMeter b true earlier.result
    let result := menuMachine (b+1)
    signedGridTape a=menuMachine (a+1) ∧
    result=⟨zero.result++one.result,
      earlier.steps+zero.steps+one.steps+4*earlier.result.length+8⟩ ∧
    resident+(gridMemoryBits earlier.result+gridMemoryBits zero.result+
      gridMemoryBits one.result+gridMemoryBits result.result)≤roof+3*((a+1)*2^(a+1)) := by
  let earlier := menuMachine b
  let zero := prefixMeter b false earlier.result
  let one := prefixMeter b true earlier.result
  let result := menuMachine (b+1)
  have exactEarlier := emitted_menu_grid_bit_width_is_exact b
  have exactResult := emitted_menu_grid_bit_width_is_exact (b+1)
  have size : earlier.result.length=2^b := (congrArg List.length (menuMachine_exact b).1).trans (binary_length b)
  have half (v : Bool) : gridMemoryBits (prefixMeter b v earlier.result).result=(b+1)*2^b := by
    rw [prefix_grid_is_the_actual_map]
    have eq := (menuMachine_exact b).1
    have row (x : List Bool) (hit : x∈earlier.result.map (v::·)) : x.length=b+1 := by
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hit
      exact congrArg (·+1) ((binary_mem b y).1 (eq ▸ hy))
    rw [uniform_grid_bits _ _ row,List.length_map,size]
  have le : b≤a := Nat.lt_succ_iff.mp (real_stock_grid_unwind_width_le actual)
  have gridLe : (b+1)*2^b≤(a+1)*2^a :=
    Nat.mul_le_mul (Nat.succ_le_succ le) (Nat.pow_le_pow_right (by decide) le)
  have older : b*2^b≤(a+1)*2^a := (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans gridLe
  have output : (b+1)*2^(b+1)≤(a+1)*2^(a+1) :=
    Nat.mul_le_mul (Nat.succ_le_succ le) (Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ le))
  refine ⟨rfl,rfl,Nat.add_le_add fit ?_⟩
  change gridMemoryBits earlier.result+gridMemoryBits zero.result+
    gridMemoryBits one.result+gridMemoryBits result.result≤3*((a+1)*2^(a+1))
  rw [show gridMemoryBits earlier.result=b*2^b from exactEarlier,
    show gridMemoryBits zero.result=(b+1)*2^b from half false,
    show gridMemoryBits one.result=(b+1)*2^b from half true,
    show gridMemoryBits result.result=(b+1)*2^(b+1) from exactResult]
  have twice : (a+1)*2^(a+1)=2*((a+1)*2^a) := by rw [pow_succ]; ring
  omega

#print axioms real_stock_grid_unwind_width_le
#print axioms emitted_menu_grid_bit_width_is_exact
#print axioms actual_grid_return_holds_two_halves_and_one_result
end J6R75RawPeak
