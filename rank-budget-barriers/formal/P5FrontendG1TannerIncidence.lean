import P5FrontendG1TannerModel
import P5FrontendG1TannerSchedule
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! The actual initial Tanner rows and the double count of sign incidences.
There is no hypothesis separating row values or the groups owning rows. -/
namespace Paper5.FrontendG1.Tanner
open scoped BigOperators

theorem edge_card (ell d : ℕ) : Fintype.card (Edge ell d)=2^ell*d := by
  simp [Edge,Word,F₂]

theorem row_card (ell c : ℕ) : Fintype.card (Row ell c)=2*2^ell*c := by
  simp [Row,Word,F₂]
  ring

abbrev PrintEdges (B m : ℕ) := Edge (sourceEll B m) (sourceDegree B m)
abbrev PrintRows (B m : ℕ) := Row (sourceEll B m) (sourceLocalRows B m)

section FiniteInputs
variable (C : Type*) [Fintype C] (B : ℕ)

theorem printed_kept_columns_exist (hB : 0<B) (hm : 0<Fintype.card C) :
    Nonempty (C↪PrintEdges B (Fintype.card C)) := by
  apply Function.Embedding.nonempty_of_card_le
  rw [edge_card]
  exact source_q_covers hB hm

end FiniteInputs

/-- A concrete finite input to the source's shortening stage. The distance
certificate concerns the actual local matrix, not its number of rows. The
entrywise conclusions hold for every shift tuple, in particular the one
selected by the printed bias tests. -/
structure PrintedInput (C : Type*) [Fintype C] (B : ℕ) where
  shifts : Fin (sourceDegree B (Fintype.card C))→Word (sourceEll B (Fintype.card C))
  checks : Matrix (Fin (sourceLocalRows B (Fintype.card C))) (Fin (sourceDegree B (Fintype.card C))) F₂
  kept : C↪PrintEdges B (Fintype.card C)
  distance : LocalDistance checks (sourceMinDistance B (Fintype.card C))

def PrintedInput.initial {C : Type*} [Fintype C] {B : ℕ} (P : PrintedInput C B) :
    Matrix (PrintRows B (Fintype.card C)) C F₂ := shortened P.shifts P.checks P.kept

theorem printed_initial_row_width {C : Type*} [Fintype C] {B : ℕ} (P : PrintedInput C B)
    (r : PrintRows B (Fintype.card C)) :
    weight (P.initial r)≤sourceD B (Fintype.card C) :=
  (indexed_row_width P.shifts P.checks P.kept r).trans (Nat.min_le_right _ _)

theorem printed_initial_row_count {C : Type*} [Fintype C] (B : ℕ) :
    Fintype.card (PrintRows B (Fintype.card C))=
      2*sourceQ B (Fintype.card C)*sourceLocalRows B (Fintype.card C) := row_card _ _

theorem printed_initial_small_prefix {C : Type*} [Fintype C] {B : ℕ} (hB : 0<B)
    (hm : 0<Fintype.card C) (hq : 1<sourceQ B (Fintype.card C)) :
    Fintype.card (PrintRows B (Fintype.card C))*B<Fintype.card C := by
  rw [printed_initial_row_count]
  exact source_indexed_rows_strict hB hm hq

theorem printed_opposite_endpoints {C : Type*} [Fintype C] {B : ℕ} (P : PrintedInput C B)
    (hB : 0<B) (hm : 0<Fintype.card C) (hq : 1<sourceQ B (Fintype.card C)) (i : C) :
    ∃ j : Fin (sourceLocalRows B (Fintype.card C)),
      let r₁ : PrintRows B (Fintype.card C) := .inl ((P.kept i).1,j)
      let r₂ : PrintRows B (Fintype.card C) := .inr (rightEndpoint P.shifts (P.kept i),j)
      r₁≠r₂ ∧ P.initial r₁ i=1 ∧ P.initial r₂ i=1 :=
  opposite_indexed_rows P.shifts P.checks P.kept _ (source_distance_gt_one hB hm hq) P.distance i

section SignDegrees
variable {V R : Type*} [Fintype V] [Fintype R] {E : Finset (V×V)}

abbrev pinIndex (v : V) : GuardIndex E := .inr (.inl v)

def signsRead (A : Matrix R (GuardIndex E) F₂) (r : R) : Finset V :=
  Finset.univ.filter fun v=>A r (pinIndex v)=1

def rowsReading (A : Matrix R (GuardIndex E) F₂) (v : V) : Finset R :=
  Finset.univ.filter fun r=>A r (pinIndex v)=1

omit [Fintype V] in
theorem two_rows_card (A : Matrix R (GuardIndex E) F₂) (v : V)
    {u w : R} (hne : u≠w) (hU : A u (pinIndex v)=1) (hW : A w (pinIndex v)=1) :
    2≤(rowsReading A v).card := by
  classical
  have hsub : ({u,w}:Finset R)⊆rowsReading A v := by
    intro r hr
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with rfl|rfl
    · simp [rowsReading,hU]
    · simp [rowsReading,hW]
  simpa only [Finset.card_pair hne] using Finset.card_le_card hsub

theorem incidence_double_count (A : Matrix R (GuardIndex E) F₂) :
    (∑ r : R,(signsRead A r).card)=(∑ v : V,(rowsReading A v).card) := by
  simp only [signsRead,rowsReading,Finset.card_filter]
  exact Finset.sum_comm

/-- More than 4B/7 signs on one indexed row, with integer arithmetic and
no rounding in the statement. -/
theorem some_row_many_signs (A : Matrix R (GuardIndex E) F₂) {m B : ℕ}
    (hC : 2*m=7*Fintype.card V) (hPrefix : Fintype.card R*B<m)
    (hTwo : ∀ v : V, 2≤(rowsReading A v).card) :
    ∃ r : R, 4*B<7*(signsRead A r).card := by
  by_contra! h
  have hlow : 2*Fintype.card V≤∑ r : R,(signsRead A r).card := by
    rw [incidence_double_count,Nat.mul_comm]
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      (Finset.sum_le_sum fun (v : V) (_ : v∈Finset.univ) => hTwo v)
  have hUpper : 7*(∑ r : R,(signsRead A r).card)≤4*(Fintype.card R*B) := by
    rw [Finset.mul_sum,show 4*(Fintype.card R*B)=Fintype.card R*(4*B) by ring]
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      (Finset.sum_le_sum fun (r : R) (_ : r∈Finset.univ) => h r)
  omega

end SignDegrees

section ActualGuard
variable {V : Type*} [Fintype V] [DecidableEq V] {E : Finset (V×V)}

omit [DecidableEq V] in
theorem guard_index_card (E : Finset (V×V)) :
    Fintype.card (GuardIndex E)=2*Fintype.card V+E.card := by
  simp [GuardIndex,Nat.two_mul]
  omega

theorem guard_index_cubic (E : Finset (V×V)) (hG : ∀ v,GraphCutMoments.degree E v=3) :
    2*Fintype.card (GuardIndex E)=7*Fintype.card V := by
  have hc := GraphCutMoments.regular_edge_count E 3 hG
  rw [guard_index_card]
  omega

omit [DecidableEq V] in
theorem printed_pin_two_rows {B : ℕ} (P : PrintedInput (GuardIndex E) B)
    (hB : 0<B) (hm : 0<Fintype.card (GuardIndex E))
    (hq : 1<sourceQ B (Fintype.card (GuardIndex E))) (v : V) :
    2≤(rowsReading P.initial v).card := by
  obtain ⟨j,hneq,hL,hR⟩ := printed_opposite_endpoints P hB hm hq (pinIndex v)
  exact two_rows_card P.initial v hneq hL hR

theorem printed_some_row_many_signs {B : ℕ} (P : PrintedInput (GuardIndex E) B)
    (hB : 0<B) (hm : 0<Fintype.card (GuardIndex E))
    (hq : 1<sourceQ B (Fintype.card (GuardIndex E)))
    (hC : ∀v,GraphCutMoments.degree E v=3) :
    ∃ r : PrintRows B (Fintype.card (GuardIndex E)),4*B<7*(signsRead P.initial r).card :=
  some_row_many_signs P.initial (guard_index_cubic E hC)
    (printed_initial_small_prefix hB hm hq) (printed_pin_two_rows P hB hm hq)

end ActualGuard

#print axioms edge_card
#print axioms row_card
#print axioms printed_kept_columns_exist
#print axioms printed_initial_row_width
#print axioms printed_initial_row_count
#print axioms printed_initial_small_prefix
#print axioms printed_opposite_endpoints
#print axioms two_rows_card
#print axioms incidence_double_count
#print axioms some_row_many_signs
#print axioms guard_index_card
#print axioms guard_index_cubic
#print axioms printed_pin_two_rows
#print axioms printed_some_row_many_signs
end Paper5.FrontendG1.Tanner