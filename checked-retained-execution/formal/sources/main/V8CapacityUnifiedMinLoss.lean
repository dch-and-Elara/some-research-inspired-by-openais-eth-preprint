import V8CapacityUnifiedCoordinates

/-! U4 on literal residue target matrices: minimum loss across all
receiver columns; no finite loss for an outside component. No basis
independence is assumed, and the invariant also detects impossibility. -/
namespace V8CapacityUnified
open scoped Classical
open V8CapacityCRTJet V8CapacitySmith

noncomputable section
set_option linter.unusedSectionVars false

variable {O X I Y : Type*} [CommRing O] [IsDomain O] [Fintype X] [Fintype I] [Fintype Y]
variable {π : O} {E : Submodule O (X → O)} {n : ℕ}
variable (p : ℕ) (S : Powered π E I n)

local notation "B" => BaseMod O π p

def matrixRead (L : ℕ) (v : Y → X → B) : Prop :=
  ∀ y, v y∈attainable π L p E

def outsideZero (v : Y → X → B) : Prop :=
  ∀ y (j : I), j∉Set.range S.chart.f → smithResidue p S (v y) j=0

def coordOrder (v : Y → X → B) (i : Fin n) (y : Y) :=
  truncatedOrder π p (smithResidue p S (v y) (S.chart.f i))

def demand (v : Y → X → B) (i : Fin n) (y : Y) : ℕ :=
  if coordOrder p S v i y<p then S.exponent i-coordOrder p S v i y else 0

def minimumLoss (v : Y → X → B) : ℕ :=
  Finset.univ.sup (fun iy : Fin n × Y => demand p S v iy.1 iy.2)

theorem demand_iff (v : Y → X → B) (i : Fin n) (y : Y) (L : ℕ) :
    min p (S.exponent i-L) ≤ coordOrder p S v i y ↔ demand p S v i y≤L := by
  have h : coordOrder p S v i y≤p := order_le_precision π p _
  unfold demand
  split <;> omega

theorem U4_feasible_iff (hπ : π≠0) (v : Y → X → B) (L : ℕ) :
    matrixRead (E:=E) p L v ↔ outsideZero p S v ∧ minimumLoss p S v≤L := by
  unfold matrixRead outsideZero minimumLoss
  rw [Finset.sup_le_iff]
  simp only [Finset.mem_univ,forall_true_left,Prod.forall]
  constructor
  · intro hv
    refine ⟨fun y => ((U3_membership p S hπ L (v y)).mp (hv y)).2,fun i y => ?_⟩
    exact (demand_iff p S v i y L).mp (((U3_membership p S hπ L (v y)).mp (hv y)).1 i)
  · rintro ⟨hout,hd⟩ y
    exact (U3_membership p S hπ L (v y)).mpr
      ⟨fun i => (demand_iff p S v i y L).mpr (hd i y),hout y⟩

theorem U4_impossible_iff (hπ : π≠0) (v : Y → X → B) :
    (¬∃ L, matrixRead (E:=E) p L v) ↔ ¬outsideZero p S v := by
  constructor
  · intro h ho
    exact h ⟨minimumLoss p S v,
      (U4_feasible_iff p S hπ v _).mpr ⟨ho,le_rfl⟩⟩
  · rintro h ⟨L,hr⟩
    exact h ((U4_feasible_iff p S hπ v L).mp hr).1

theorem U4_is_least (hπ : π≠0) (v : Y → X → B) (ho : outsideZero p S v) :
    IsLeast {L : ℕ | matrixRead (E:=E) p L v} (minimumLoss p S v) := by
  exact ⟨(U4_feasible_iff p S hπ v _).mpr ⟨ho,le_rfl⟩,
    fun L hL => ((U4_feasible_iff p S hπ v L).mp hL).2⟩

theorem U4_native_receiver {G : Type*} (hπ : π≠0) (v : Y → X → O) (L : ℕ)
    (read : G → X → O) (hE : Set.range read=↑E) :
    (∃ recv : Y → G, ∀ y x, π^(L+p)∣read (recv y) x-π^L*v y x) ↔
      outsideZero p S (fun y => residueRows π p (v y)) ∧
        minimumLoss p S (fun y => residueRows π p (v y))≤L := by
  rw [U1_receiver_columns π L p E read hE v]
  exact U4_feasible_iff p S hπ _ L

def exactBudget (v : Y → X → B) : Option ℕ :=
  if outsideZero p S v then some (minimumLoss p S v) else none

variable {I' : Type*} [Fintype I'] {n' : ℕ}
variable (S' : Powered π E I' n')

/-- Numeric minimum, including the no-finite-loss case, is invariant
under any two genuine Smith presentations of the same numerator lattice. -/
theorem U4_basis_independent (hπ : π≠0) (v : Y → X → B) :
    exactBudget p S v = exactBudget p S' v := by
  have hOut : outsideZero p S v ↔ outsideZero p S' v := by
    have h := (U4_impossible_iff p S hπ v).symm.trans (U4_impossible_iff p S' hπ v)
    tauto
  unfold exactBudget
  by_cases ho : outsideZero p S v
  · have ho' := hOut.mp ho
    rw [if_pos ho,if_pos ho']
    exact congrArg some ((U4_is_least p S hπ v ho).unique (U4_is_least p S' hπ v ho'))
  · rw [if_neg ho,if_neg (fun h => ho (hOut.mpr h))]

#print axioms demand_iff
#print axioms U4_feasible_iff
#print axioms U4_impossible_iff
#print axioms U4_is_least
#print axioms U4_native_receiver
#print axioms U4_basis_independent
end
end V8CapacityUnified
