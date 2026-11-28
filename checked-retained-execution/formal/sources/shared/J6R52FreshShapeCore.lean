import J6R51IngressRootLayout
import J6R51IngressRawGraph
import J6R28GeneratedRootFrameGuards

/-! Genuine printed setup for the fresh chosen guarded CNF.
All layout facts and gate bounds are derived from the source.
The arithmetic size guard and field degree are visible, as in R28.
The native parameter may be the subdivision count or the actual
variable-plus-clause size. The logged schedules agree, not necessarily
the underlying physicalSize numbers. -/
namespace J6R52FreshShape
open scoped Classical Polynomial
open Polynomial Std.Sat J6Mesh J6OrientedHost
open J6R51Ingress J6R24LegalLayout J6R26StablePreparedRoot J6R28GeneratedRootFrame
open J6R49RootIngress J1PPrinted J7R10Plant J7R9Compiler J7R9Subdivision
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 14000000
set_option maxRecDepth 2800

theorem subdivision_native_fits {V : Type*} [DecidableEq V] [Fintype V] (H : CNF V) :
    nSubdiv H≤nWires H := by rw [twice_subdiv]; omega

noncomputable def sourceNative {V : Type*} [Fintype V] (H : CNF V) : ℕ :=
  Fintype.card V+H.length

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V]
variable (F : CNF V) (s : DeclaredOrder V)
local notation "H" => (guardedInOrder F s.roster)
local notation "S" => (guardRoster s)
local notation "m" => (nWires H)
local notation "n" => (nSubdiv H)
local notation "T" => (freshPlant H S)

theorem fresh_guard_nonempty_rows : ∀ row∈H,0<row.length := by
  intro row hx
  exact J7R9SourceInput.nonempty_clauses F row
    ((ordered_guard_perm F s.roster s.distinct s.complete).mem_iff.mp hx)

theorem source_native_fits [Nonempty V] (h3 : ∀ row∈F,row.length≤3) :
    sourceNative H≤m := by
  obtain ⟨lo,_⟩ := J7R9Size.source_size H 4 (fresh_guard_allOccur F s.roster s.complete)
    (fresh_guard_nonempty_rows F s) (fresh_guard_width F s h3)
  exact lo

theorem actual_fresh_degree_four (h3 : ∀ row∈F,row.length≤3) (v : OrderedOld H) :
    (T).degree v≤4 :=
  ordered_width H 4 (fresh_guard_width F s h3) v

def printedGuard (wireCount native : ℕ) : Prop :=
  (2*epsDen)^30*(2:ℕ)^10≤Nat.clog 2 (physicalSize wireCount native)

theorem same_logged_printed_schedule (wireCount n₁ n₂ : ℕ) (h₁ : n₁≤wireCount) (h₂ : n₂≤wireCount) :
    Nat.clog 2 (physicalSize wireCount n₁)=Nat.clog 2 (physicalSize wireCount n₂) := by
  rw [(physicalSize_ceiling wireCount n₁ h₁).2.2,(physicalSize_ceiling wireCount n₂ h₂).2.2]
theorem chosen_source_schedule_same [Nonempty V] (h3 : ∀ row∈F,row.length≤3) :
    Nat.clog 2 (physicalSize m n)=Nat.clog 2 (physicalSize m (sourceNative H)) :=
  same_logged_printed_schedule m n (sourceNative H) (subdivision_native_fits H) (source_native_fits F s h3)

def shapeFromLegalNative (f : ℤ[X]) (base native : ℕ) (h3 : ∀ row∈F,row.length≤3)
    (fit : native≤m) (field : f.natDegree=4*Nat.clog 2 (physicalSize m native))
    (large : printedGuard m native) :
    RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m) := by
  have degree := root_delta_at_least_four f m n base native T (constantRootWord m) fit large
  refine ⟨printed_room m,printed_half_correct m,fit,
    (printed_rank_width m).2.1,(printed_rank_width m).2.2,field,large,?_⟩
  intro v
  exact (actual_fresh_degree_four F s h3 v).trans degree

/-- The requested fresh shape, specialized to the actual chosen
subdivision count, without a supplied degree or native-size bound. -/
def subdivisionRootShape (f : ℤ[X]) (base : ℕ) (h3 : ∀ row∈F,row.length≤3)
    (field : f.natDegree=4*Nat.clog 2 (physicalSize m n))
    (large : printedGuard m n) :
    RootShape f m (printedHalf m) base n (printedRankWidth m) T (constantRootWord m) :=
  shapeFromLegalNative F s f base n h3 (subdivision_native_fits H) field large

/-- Keep the variable-plus-clause measure when the consuming statement
uses the printed source size literally rather than just its log. -/
def literalRootShape [Nonempty V] (f : ℤ[X]) (base : ℕ) (h3 : ∀ row∈F,row.length≤3)
    (field : f.natDegree=4*Nat.clog 2 (physicalSize m (sourceNative H)))
    (large : printedGuard m (sourceNative H)) :
    RootShape f m (printedHalf m) base (sourceNative H) (printedRankWidth m) T (constantRootWord m) :=
  shapeFromLegalNative F s f base (sourceNative H) h3 (source_native_fits F s h3) field large

#print axioms subdivision_native_fits
#print axioms fresh_guard_nonempty_rows
#print axioms source_native_fits
#print axioms actual_fresh_degree_four
#print axioms same_logged_printed_schedule
#print axioms chosen_source_schedule_same
#print axioms shapeFromLegalNative
#print axioms subdivisionRootShape
#print axioms literalRootShape
end
end J6R52FreshShape
