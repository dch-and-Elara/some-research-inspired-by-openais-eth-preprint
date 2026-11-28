import J9EndMoment

/-! Exact tensor factorization of the literal equality CNF on the original
two-port rows, including the signed change at a single original port. -/
namespace J9LayoutTransfer

open scoped BigOperators Classical
open LiteralPortCompiler
noncomputable section
variable {R K : Type*} [Fintype R] [DecidableEq R] [CommRing K]

abbrev Port (R : Type*) := R × Bool

def listedRows (s : List R) : CNF (Port R) :=
  s.flatMap fun r => equality (r,false) (r,true)

def allRows : CNF (Port R) := listedRows (Finset.univ : Finset R).toList

def equalWeight (u v : Bool) : K := if u = v then 1 else 0

omit [Fintype R] [DecidableEq R] in
theorem listedRows_truth (s : List R) (a : Port R → Bool) :
    (truth (listedRows s) a : K) =
      (s.map (fun r => equalWeight (a (r,false)) (a (r,true)))).prod := by
  induction s with
  | nil => simp [listedRows, truth, satisfied, indicator]
  | cons r s ih =>
    change (truth (equality (r,false) (r,true) ++ listedRows s) a : K) = _
    rw [truth_append, ih, truth_equality]
    rfl

omit [DecidableEq R] in
theorem allRows_truth (a : Port R → Bool) :
    (truth (allRows (R:=R)) a : K) = ∏ r, equalWeight (a (r,false)) (a (r,true)) := by
  rw [allRows, listedRows_truth, Finset.prod_map_toList]

def rowLocal (entry : Port R → Bool → K) (r : R) (x : Bool → Bool) : K :=
  equalWeight (x false) (x true) *
    (entry (r,false) (x false) * entry (r,true) (x true))

/-- An exact bijection of assignment sets: compiler ports become the two
ordered legs of each original row; no equality constraints are dropped. -/
theorem original_rows_reindex (entry : Port R → Bool → K) :
    (∑ a : Port R → Bool, (truth (allRows (R:=R)) a : K) * ∏ p, entry p (a p)) =
      ∏ r, ∑ x : Bool → Bool, rowLocal entry r x := by
  classical
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.curry R Bool Bool) _ _ ?_
  intro a
  rw [allRows_truth, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r _
  rw [Fintype.prod_bool]
  simp only [rowLocal, Equiv.curry_apply, Function.curry_apply, mul_comm (entry (r,true) _)]

omit [Fintype R] [DecidableEq R] in
theorem rowLocal_pairs (entry : Port R → Bool → K) (r : R) :
    (∑ x : Bool → Bool, rowLocal entry r x) =
      ∑ p : Bool × Bool, equalWeight p.1 p.2 *
        (entry (r,false) p.1 * entry (r,true) p.2) := by
  exact Fintype.sum_equiv (Equiv.boolArrowEquivProd Bool) _ _ (fun _ => rfl)

def selectEntry (base : Port R → K) (mark : Port R) (k : K) (q : Port R) (bit : Bool) : K :=
  if q = mark then LiteralPortCompiler.slope bit * k else affine bit (base q)

omit [Fintype R] in
theorem unmarked_row (base : Port R → K) (mark : Port R) (k : K) (r : R) (h : r ≠ mark.1) :
    (∑ x : Bool → Bool, rowLocal (selectEntry base mark k) r x) =
      TargetDerivative.equality (base (r,false)) (base (r,true)) := by
  rw [rowLocal_pairs, Fintype.sum_prod_type]
  have hl : ((r,false) : Port R) ≠ mark := fun e => h (congrArg Prod.fst e)
  have hr : ((r,true) : Port R) ≠ mark := fun e => h (congrArg Prod.fst e)
  simp [selectEntry, hl, hr, equalWeight, affine, TargetDerivative.equality, add_comm]

omit [Fintype R] in
theorem marked_row (base : Port R → K) (mark : Port R) (k : K) :
    (∑ x : Bool → Bool, rowLocal (selectEntry base mark k) mark.1 x) =
      k * (-1 + 2 * base (mark.1,!mark.2)) := by
  obtain ⟨r,b⟩ := mark
  rw [rowLocal_pairs, Fintype.sum_prod_type]
  cases b <;> simp [selectEntry, equalWeight, LiteralPortCompiler.slope, affine] <;> ring

/-- A single literal selection at the real target port yields the signed
difference; all other existing rows contribute their unmarked table. -/
theorem contracted_mark (base : Port R → K) (mark : Port R) (k : K) :
    (∑ a : Port R → Bool, (truth (allRows (R:=R)) a : K) *
        ∏ p, selectEntry base mark k p (a p)) =
      k * (-1 + 2 * base (mark.1,!mark.2)) *
        ∏ r ∈ (Finset.univ : Finset R).erase mark.1,
          TargetDerivative.equality (base (r,false)) (base (r,true)) := by
  rw [original_rows_reindex]
  let f := fun r => ∑ x : Bool → Bool, rowLocal (selectEntry base mark k) r x
  have he := Finset.prod_erase_mul (Finset.univ : Finset R) f (Finset.mem_univ mark.1)
  rw [← he, mul_comm]
  change f mark.1 * _ = _
  rw [show f mark.1 = _ from marked_row base mark k]
  congr 1
  exact Finset.prod_congr rfl fun r hr => unmarked_row base mark k r (Finset.mem_erase.mp hr).1

#print axioms original_rows_reindex
#print axioms marked_row
#print axioms contracted_mark
end
end J9LayoutTransfer

