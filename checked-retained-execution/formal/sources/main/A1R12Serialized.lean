import A1R12Numeric

/-! Production entry point on literal fixed-coordinate lists. Only the
proof uses the Fin-indexed Ports model; there is no unpriced lookup
of a numerical coefficient or coordinate function inside this runner. -/

namespace A1R12
open A1R10 A1R11 AOracleMachineTime AOracleSuccinctPacket

theorem mapMeter_map {A B C : Type*} (g : B → Meter C) (d : ℕ) (k : A → B) (xs : List A) :
    mapMeter g d (xs.map k)=mapMeter (fun x => g (k x)) d xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons,mapMeter,ih]

theorem mapMeter_ofFn {A B : Type*} {n : ℕ} (g : A → Meter B) (d : ℕ) (k : Fin n → A) :
    mapMeter g d (List.ofFn k)=vectorMap (fun x => g (k x)) d := by
  have h : (List.finRange n).map k=List.ofFn k := by simp [List.finRange,Function.comp_def]
  rw [← h,mapMeter_map,vectorMap]

def numericOnSlots {p ell packets G a i : ℕ} (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell)
    (t : ℤ) (rows cols : List (Fin (2^a))) (modes : List (Mode packets G i p)) :
    Meter (Numeric f ell) :=
  let w := uvWidth f.length ell p
  let L := mapMeter (fun x => mapMeter (fun y =>
      padCost (modularGen hp he hv z a t ((y.val:ℤ)-(x.val:ℤ))) (8*(a+3)^2)) w cols) 0 rows
  let C := mapMeter (fun x => mapMeter (fun k : Mode packets G i p =>
      crossingGen hp he hv z a i k.exponent.val t x.val k.tile.val) w modes) 0 rows
  let Q := mapMeter (quotientGen p a i) p cols
  ⟨⟨L.result,C.result,Q.result⟩,L.steps+C.steps+Q.steps+6⟩

theorem numericOnSlots_model {p ell r c m packets G a i : ℕ} (hp : 0<p)
    {f : List (A1R10.Word p)} (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell)
    (t : ℤ) (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p) :
    numericOnSlots hp he hv z t (List.ofFn row.slot) (List.ofFn col.slot) (List.ofFn modes)
      = numericGen hp he hv z t row col modes := by
  simp only [numericOnSlots,numericGen,mapMeter_ofFn,matrixMap,crossCellGen]
  rfl

#print axioms mapMeter_ofFn
#print axioms numericOnSlots_model
end A1R12

