import J6R51IngressFreshPlant

/-! Meaning of the actual fresh chart: source gates read the same
logical half-assignment, and the source conjunction, including its
guard, has the original count. No frozen root-location equality. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat J7R9Compiler J7R9Subdivision J7R10Ports J7R10Plant
open J7R9EqualityTree J6OrientedHost J6OrientedHostEval J6RecursivePortCube
open J6R49RootIngress
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 14000000
noncomputable section

variable {V : Type*} [DecidableEq V] [Fintype V] (H : CNF V)
variable (s : DeclaredOrder V)

def rankAssignment : (Fin (nWires H)→Bool) ≃ (Half H→Bool) :=
  (halfRank H s).symm.arrowCongr (Equiv.refl Bool)

theorem fresh_assignment_at (x : Fin (nWires H)→Bool) (p : Half H) :
    rankAssignment H s x p=x (halfRank H s p) := rfl

theorem fresh_row_transport (p : OrderedPort H) :
    (freshPlant H s).rowPort p=halfRank H s (rowHalf H p) := rfl

theorem fresh_col_transport (w : Wire H) (b : Bool) :
    (freshPlant H s).colPort (wireRank H s w,b)=halfRank H s (w,b) := by
  change halfRank H s ((wireRank H s).symm (wireRank H s w),b)=_
  rw [Equiv.symm_apply_apply]

theorem fresh_defines_new_equality (x : Fin (nWires H)→Bool) :
    coreB (freshPlant H s) x=true ↔ J7R9Subdivision.newOK H (rankAssignment H s x) := by
  unfold coreB good J7R9Subdivision.newOK
  simp only [decide_eq_true_eq,fresh_assignment_at]
  constructor
  · intro h w
    have z := h (wireRank H s w)
    rwa [fresh_col_transport H s w false,fresh_col_transport H s w true] at z
  · intro h j
    obtain ⟨w,rfl⟩ := (wireRank H s).surjective j
    rw [fresh_col_transport H s w false,fresh_col_transport H s w true]
    exact h w

def orderedOldOK (u : Half H→Bool) : Prop :=
  physicalClause H u ∧ ∀ v g,g∈orderedVar H v → agrees u g

theorem fresh_defines_old_gates (x : Fin (nWires H)→Bool) :
    coreA (freshPlant H s) x=true ↔ orderedOldOK H (rankAssignment H s x) := by
  unfold coreA good
  rw [decide_eq_true_eq]
  change (∀ v : OrderedOld H,
    (orderedGate H v).eval (fun j => x ((freshPlant H s).rowPort ⟨v,j⟩))=true) ↔ _
  let u := rankAssignment H s x
  change (∀ v : OrderedOld H,(orderedGate H v).eval (fun j=>u (orderedPort H v j))=true) ↔
    orderedOldOK H u
  unfold orderedOldOK physicalClause
  constructor
  · intro all
    refine ⟨fun i=>?_,fun v g hg=>?_⟩
    · simpa only [orderedGate,Gate.eval,orderedPort,decide_eq_true_eq] using all (.inl i)
    · obtain ⟨j,rfl⟩ := List.get_of_mem hg
      apply (agrees_of_positions u _).mpr
      exact of_decide_eq_true (all (.inr ⟨v,j⟩))
  · rintro ⟨ha,hb⟩ v
    cases v with
    | inl i => exact decide_eq_true (ha i)
    | inr p => exact decide_eq_true ((agrees_of_positions u _).mp (hb p.1 _ (List.get_mem _ p.2)))

theorem fresh_bipolar_same (u : Half H→Bool) (h : J7R9Subdivision.newOK H u) :
    orderedOldOK H u ↔ physicalOldOK H u := by
  rw [← lift_collapse H u h]
  unfold orderedOldOK physicalOldOK
  apply Iff.and Iff.rfl
  apply forall_congr'
  intro v
  exact ordered_boolean_tree H v (collapse H u)

theorem fresh_plant_exact (x : Fin (nWires H)→Bool) :
    (coreA (freshPlant H s) x=true ∧ coreB (freshPlant H s) x=true) ↔
      bipolarOK H (rankAssignment H s x) := by
  rw [fresh_defines_old_gates,fresh_defines_new_equality,bipolarOK]
  exact ⟨fun ⟨ha,hb⟩=>⟨(fresh_bipolar_same H _ hb).mp ha,hb⟩,
    fun ⟨ha,hb⟩=>⟨(fresh_bipolar_same H _ hb).mpr ha,hb⟩⟩

def acceptingRanks :
    {x : Fin (nWires H)→Bool //
      coreA (freshPlant H s) x=true ∧ coreB (freshPlant H s) x=true} ≃
      {u : Half H→Bool // bipolarOK H u} :=
  (rankAssignment H s).subtypeEquiv (fresh_plant_exact H s)

theorem fresh_model_count (h : AllOccur H) :
    Nat.card {x : Fin (nWires H)→Bool //
      coreA (freshPlant H s) x=true ∧ coreB (freshPlant H s) x=true} =
        PinnedCNF.modelCount H := by
  rw [Nat.card_congr (acceptingRanks H s),subdivision_count H h]

theorem fresh_guarded_count [Nonempty V] (F : CNF V) (d : DeclaredOrder (Option V)) :
    Nat.card {x : Fin (nWires (guarded F))→Bool //
      coreA (freshPlant (guarded F) d) x=true ∧ coreB (freshPlant (guarded F) d) x=true} =
        1+PinnedCNF.modelCount F := by
  rw [fresh_model_count (guarded F) d (guard_allOccur (J7R9Clause.clean F))]
  exact J7R9Clause.guarded_clean_count F

#print axioms fresh_assignment_at
#print axioms fresh_row_transport
#print axioms fresh_col_transport
#print axioms fresh_defines_new_equality
#print axioms fresh_defines_old_gates
#print axioms fresh_bipolar_same
#print axioms fresh_plant_exact
#print axioms fresh_model_count
#print axioms fresh_guarded_count
end
end J6R51Ingress
