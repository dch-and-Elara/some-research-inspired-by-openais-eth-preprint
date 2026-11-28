import J6R68ActiveInputsBaseCurrent

/-! Selected storage of the real recursive scan of the emitted signed
grid for an active stock. The prefix is its actual selected row stack,
not a free slice or a second runtime computation. -/
namespace J6R75RawPeak
open AOracleMachineTime AOracleMachineTimeTape A1R10 J6R68ActiveInputs
open J6R22RootReadout J6R12CollisionMenu

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3100
set_option maxHeartbeats 6000000
set_option Elab.async false

def stockRowBits {q : ℕ} (row : RawCentre q) : ℕ :=
  row.key.length+row.multiplicity.val.length

def stockRowsBits {q : ℕ} (rows : List (RawCentre q)) : ℕ :=
  (rows.map stockRowBits).sum

def gridMemoryBits (bits : List (List Bool)) : ℕ :=
  (bits.map List.length).sum

def stockReturn {q : ℕ} (row : Meter (Option (RawCentre q)))
    (later : Meter (List (RawCentre q))) : Meter (List (RawCentre q)) :=
  ⟨row.result.toList++later.result,row.steps+later.steps+5⟩

theorem raw_stock_scan_reenters_its_original_row_continuation
    {q : ℕ} (zero h : Word q) (axis taper : List Bool)
    (pre : List (List Bool)) (bits : List Bool) (post : List (List Bool)) :
    let read := readOrder zero h axis taper
    scanOrders zero h axis taper (pre++bits::post)=
      (pre.map read).foldr stockReturn
        (stockReturn (read bits) (scanOrders zero h axis taper post)) := by
  induction pre with
  | nil=>rfl
  | cons b bs ih=>
    change stockReturn (readOrder zero h axis taper b) (scanOrders zero h axis taper (bs++bits::post))=_
    rw [ih]
    rfl

theorem raw_stock_scan_returns_only_actual_row_results
    {q : ℕ} (zero h : Word q) (axis taper : List Bool) (keys : List (List Bool)) :
    (scanOrders zero h axis taper keys).result=keys.filterMap (fun b=>(readOrder zero h axis taper b).result) := by
  induction keys with
  | nil=>rfl
  | cons k ks ih=>
    rw [show (scanOrders zero h axis taper (k::ks)).result=
      (readOrder zero h axis taper k).result.toList++(scanOrders zero h axis taper ks).result from rfl,ih]
    cases eq : (readOrder zero h axis taper k).result <;> simp [eq]

private theorem returned_order_key {q : ℕ} (zero h : Word q) (axis taper bits : List Bool)
    (row : RawCentre q) (hit : (readOrder zero h axis taper bits).result=some row) :
    row.key=bits := by
  unfold readOrder at hit
  dsimp only at hit
  cases val : (rawSignedLevel axis bits).result with
  | none=>simp [val] at hit
  | some level=>
    simp only [val] at hit
    split at hit
    · contradiction
    · cases hit
      rfl

private theorem full_list_field_width {A : Type*} (len : A→ℕ) (m : ℕ) (L : List A)
    (fit : ∀ x∈L,len x=m) :
    (L.map len).sum=m*L.length := by
  induction L with
  | nil=>simp
  | cons a as ih=>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ]
    rw [fit a List.mem_cons_self,ih (fun x hx=>fit x (List.mem_cons_of_mem _ hx)),Nat.add_comm]

theorem uniform_grid_bits (width : ℕ) (G : List (List Bool)) (ok : ∀ b∈G,b.length=width) :
    gridMemoryBits G=width*G.length :=
  full_list_field_width List.length width G ok

theorem stock_filtered_rows_exact_bit_width
    {q : ℕ} (zero h : Word q) (axis taper : List Bool)
    (width : ℕ) (keys : List (List Bool)) (keyW : ∀ k∈keys,k.length=width) :
    let out := keys.filterMap (fun x=>(readOrder zero h axis taper x).result)
    stockRowsBits out=(width+q)*out.length ∧ out.length≤keys.length := by
  let out := keys.filterMap (fun x=>(readOrder zero h axis taper x).result)
  have w (r : RawCentre q) (hr : r∈out) : stockRowBits r=width+q := by
    obtain ⟨k,mem,got⟩ := List.mem_filterMap.mp hr
    unfold stockRowBits
    rw [returned_order_key zero h axis taper k r got,keyW k mem,r.multiplicity.property]
  exact ⟨full_list_field_width stockRowBits (width+q) out w,List.length_filterMap_le _ _⟩

def scanOrderLiveWords {q : ℕ} (zero h : Word q) (axis taper : List Bool)
    (G pre : List (List Bool)) (bits : List Bool) (post : List (List Bool)) : ℕ :=
  let read := readOrder zero h axis taper
  let pending := pre.filterMap (fun x=>(read x).result)
  let now := read bits
  let later := scanOrders zero h axis taper post
  let joined := stockReturn now later
  -- One tag per earlier decision plus the current decision. Keep the full
  -- original grid and conservatively allow the returned tail and assembled row
  -- to coexist with the current result.
  gridMemoryBits G+(pre.length+1)+stockRowsBits pending+
    stockRowsBits now.result.toList+stockRowsBits later.result+stockRowsBits joined.result

theorem actual_stock_scan_retains_only_its_named_grid_and_row_words
    {q : ℕ} (zero h : Word q) (axis taper : List Bool)
    (width : ℕ) (G pre : List (List Bool)) (bits : List Bool) (post : List (List Bool))
    (theCut : G=pre++bits::post) (widths : ∀ b∈G,b.length=width) :
    let read := readOrder zero h axis taper
    scanOrders zero h axis taper G=
      (pre.map read).foldr stockReturn (stockReturn (read bits) (scanOrders zero h axis taper post)) ∧
    scanOrderLiveWords zero h axis taper G pre bits post≤
      width*G.length+G.length+2*((width+q)*G.length) := by
  have widths' (b : List Bool) (mem : b∈pre++bits::post) : b.length=width :=
    widths b (theCut.symm ▸ mem)
  let read := readOrder zero h axis taper
  let pending := pre.filterMap (fun x=>(read x).result)
  let now := read bits
  let later := scanOrders zero h axis taper post
  let final := stockReturn now later
  have seen : G.length=pre.length+1+post.length := by
    rw [theCut,List.length_append,List.length_cons]
    omega
  have before := stock_filtered_rows_exact_bit_width zero h axis taper width pre
    (fun x m=>widths' x (List.mem_append_left _ m))
  have after := stock_filtered_rows_exact_bit_width zero h axis taper width (bits::post)
    (fun x m=>widths' x (List.mem_append_right _ m))
  change stockRowsBits pending=(width+q)*pending.length ∧ _ at before
  have allNow : final.result=(bits::post).filterMap (fun x=>(read x).result) :=
    raw_stock_scan_returns_only_actual_row_results zero h axis taper (bits::post)
  have finalBits : stockRowsBits final.result≤(width+q)*(1+post.length) := by
    rw [allNow,after.1]
    exact Nat.mul_le_mul_left _ (after.2.trans_eq (by simp [Nat.add_comm]))
  have merged : stockRowsBits now.result.toList+stockRowsBits later.result=stockRowsBits final.result := by
    simp only [final,stockReturn,stockRowsBits,List.map_append,List.sum_append]
  have preceding : stockRowsBits pending≤(width+q)*pre.length :=
    before.1.trans_le (Nat.mul_le_mul_left _ before.2)
  have raw : gridMemoryBits G=width*G.length := uniform_grid_bits width G widths
  have comb : stockRowsBits pending+stockRowsBits final.result≤(width+q)*G.length := by
    rw [seen,Nat.add_assoc,Nat.mul_add]
    exact Nat.add_le_add preceding finalBits
  have outBound : stockRowsBits final.result≤(width+q)*G.length := by
    exact (Nat.le_add_left _ _).trans comb
  have tagBound : pre.length+1≤G.length := by omega
  refine ⟨theCut.symm ▸ raw_stock_scan_reenters_its_original_row_continuation zero h axis taper pre bits post,?_⟩
  change gridMemoryBits G+(pre.length+1)+stockRowsBits pending+
    stockRowsBits now.result.toList+stockRowsBits later.result+stockRowsBits final.result≤_
  rw [raw]
  calc
    _ = (width*G.length+(pre.length+1))+
          ((stockRowsBits pending+stockRowsBits final.result)+stockRowsBits final.result) := by
      rw [←merged]
      ac_rfl
    _ ≤ width*G.length+G.length+((width+q)*G.length+(width+q)*G.length) :=
      Nat.add_le_add (Nat.add_le_add_left tagBound _) (Nat.add_le_add comb outBound)
    _ = _ := by omega

#print axioms raw_stock_scan_reenters_its_original_row_continuation
#print axioms raw_stock_scan_returns_only_actual_row_results
#print axioms stock_filtered_rows_exact_bit_width
#print axioms actual_stock_scan_retains_only_its_named_grid_and_row_words
end J6R75RawPeak
