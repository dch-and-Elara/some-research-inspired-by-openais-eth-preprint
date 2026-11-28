
import J9R18CompiledCost

/-! Actual sparse old CNF truth is obtained by literal reads, not an
entry oracle. The instrument counts both visited clauses and literals.
The assignment scanner is indexed by the physical port incidence list. -/
namespace J9R18Compiled
open scoped BigOperators Classical
open J8Physical LiteralPortCompiler
set_option linter.unusedSectionVars false

def countedClause {I : Type*} (x : I→Bool) : List (Lit I) → Bool × ℕ
  | [] => (false,0)
  | q::qs => if lit x q then (true,1) else
    let z := countedClause x qs
    (z.1,z.2+1)

def countedCNF {I : Type*} (x : I→Bool) : CNF I → Bool × ℕ
  | [] => (true,0)
  | c::cs =>
    let z := countedClause x c
    if z.1 then let w := countedCNF x cs; (w.1,z.2+1+w.2) else (false,z.2+1)

def cnfWork {I : Type*} (F : CNF I) : ℕ := F.length+(F.map List.length).sum

theorem countedClause_exact {I : Type*} (x : I→Bool) (c : List (Lit I)) :
    (countedClause x c).1 = c.any (lit x) := by
  induction c with
  | nil => rfl
  | cons q qs ih =>
    cases h : lit x q <;> simp [countedClause, h, ih]

theorem countedClause_work {I : Type*} (x : I→Bool) (c : List (Lit I)) :
    (countedClause x c).2 ≤ c.length := by
  induction c with
  | nil => simp [countedClause]
  | cons q qs ih =>
    cases h : lit x q
    · simp [countedClause,h]; omega
    · simp [countedClause,h]

theorem countedCNF_exact {I : Type*} (x : I→Bool) (F : CNF I) :
    (countedCNF x F).1 = satisfied F x := by
  induction F with
  | nil => rfl
  | cons c cs ih =>
    have e := countedClause_exact x c
    cases h : (countedClause x c).1
    · simp [countedCNF,h,← e,satisfied]
    · simpa [countedCNF,h,← e,satisfied] using ih

theorem countedCNF_work {I : Type*} (x : I→Bool) (F : CNF I) :
    (countedCNF x F).2 ≤ cnfWork F := by
  induction F with
  | nil => simp [countedCNF,cnfWork]
  | cons c cs ih =>
    have hClause := countedClause_work x c
    unfold cnfWork at ih
    cases h : (countedClause x c).1 <;> simp [countedCNF,cnfWork,h] <;> omega

noncomputable section
variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

/-- Upon filling the lookup table from the literal seats, an original
column's weight has at most one matched row factor, independently of the
number of visits to its Boolean truth table. -/
theorem shiftedRows_per_original_column (e : EndpointSeating d) (he : Even L)
    (g : G) (v : LocalColumn d g) :
    Fintype.card {r : LocalRow d g // (groupWiring d e he g).dest r = some v} ≤ 1 := by
  let Q := {r : LocalRow d g // (groupWiring d e he g).dest r = some v}
  have hi : Function.Injective (fun _ : Q => ()) := by
    intro r t _
    exact Subtype.ext (group_dest_at_most_one d e he v r.val t.val r.property t.property)
  simpa using Fintype.card_le_of_injective _ hi

def literalScanWeight (e : EndpointSeating d) (he : Even L) (F : OldTables d) (g : G)
    (mark : Option (LocalRow d g × Bool)) (v : LocalColumn d g) (z : LocalPort d v → Bool) : ℚ :=
  let w := groupWiring d e he g
  indicator ℚ (countedCNF z (F g v)).1 *
    ∏ r : {r : LocalRow d g // w.dest r = some v},
      J8SourceMoment.localRow mark r.val (w.leg r.val)
        (outerAmplitude L * NativeChildRealization.bitValue ℚ (z (w.port r.val v r.property)))

theorem literalScanWeight_exact (e : EndpointSeating d) (he : Even L)
    (F : OldTables d) (g : G) (mark : Option (LocalRow d g × Bool))
    (v : LocalColumn d g) (z : LocalPort d v→Bool) :
    literalScanWeight d e he F g mark v z = localWeight d e he F g mark v z := by
  unfold literalScanWeight
  rw [countedCNF_exact]
  rfl

theorem massAt_from_literal_scan (e : EndpointSeating d) (he : Even L)
    (F : OldTables d) (g : G) (mark : Option (LocalRow d g × Bool))
    (v : LocalColumn d g) (k : ℕ) (numbering : Fin k≃LocalPort d v) :
    massAt d e he F g mark v = scan k (fun x =>
      literalScanWeight d e he F g mark v (x ∘ numbering.symm)) := by
  rw [scan_local_table, massAt]
  simp only [literalScanWeight_exact]

#print axioms countedClause_exact
#print axioms countedClause_work
#print axioms countedCNF_exact
#print axioms countedCNF_work
#print axioms shiftedRows_per_original_column
#print axioms literalScanWeight_exact
#print axioms massAt_from_literal_scan

end
end J9R18Compiled
