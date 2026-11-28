import J6R25StableCensusOuter

/-! The exterior signed interpolation on an arbitrary fixed planted
chart evaluates its own layer at one; no comparison of deformed
samples on differently ranked plants is needed. -/
namespace J6R52PublicSlot
open scoped Classical Polynomial BigOperators
open Polynomial J6Mesh J6NativeHeightMesh J6IntegerLayers
open J6OrientedHost J6OrientedHostEval J6R22RootReadout J6R25StableCensus
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2200
set_option maxHeartbeats 17000000
set_option linter.unusedSectionVars false
set_option Elab.async false

variable {V : Type} [Fintype V]
variable (m n : ℕ) (T : Plant V m n)

theorem layer_at_one_is_physical_acceptance :
    (J7R10Readout.layer m n T).eval 1=
      (Nat.card {x : Fin m→Bool // coreA T x=true ∧ coreB T x=true}:ℚ) := by
  change (LayerRecovery.layerPolynomial
    (J6OrientedPlantValue.wt (coreA T)) (J6OrientedPlantValue.wt (coreB T))).eval 1=_
  rw [LayerRecovery.layerPolynomial_eval_one,←Fintype.card_eq_nat_card,
    Fintype.card_subtype,Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  unfold J6OrientedPlantValue.wt
  cases coreA T x <;> cases coreB T x <;> simp

theorem actual_outer_at_one_is_physical_acceptance :
    (outerAtOne m (sampleNum m) (sampleDen m) (rootOldNumerator m n T)).value=
      (Nat.card {x : Fin m→Bool // coreA T x=true ∧ coreB T x=true}:ℚ) := by
  let f := J7R10Readout.layer m n T
  let a := fun i : J6Recovery.Addr m=>
    ((rootOldNumerator m n T i:ℤ):ℚ)/(sampleDen m i:ℚ)^m
  have points : (fun i : J6Recovery.Addr m=>(sampleNum m i:ℚ)/sampleDen m i)=point m :=
    funext fun i=>(mesh_fraction m i).symm
  have E := outer_at_one_exact m (sampleNum m) (sampleDen m) (rootOldNumerator m n T)
    (fun j=>(mesh_bounds m j).1.ne') (source_mesh_injective m)
  rw [points] at E
  have hn : f.natDegree < (Finset.univ : Finset (J6Recovery.Addr m)).card := by
    have hdeg := LayerRecovery.layerPolynomial_degree
      (J6OrientedPlantValue.wt (coreA T)) (J6OrientedPlantValue.wt (coreB T))
    simp only [Fintype.card_fin] at hdeg
    change f.natDegree≤m at hdeg
    simp [Finset.card_univ]
    omega
  have hdegree : f.degree < ↑(Finset.univ : Finset (J6Recovery.Addr m)).card :=
    Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hn)
  have polynomial : f=Lagrange.interpolate Finset.univ (point m) a :=
    Lagrange.eq_interpolate_of_eval_eq a (negative_distinct_points m).2.injOn hdegree
      (fun j _=>(old_fold_sample m n T j).symm)
  rw [E]
  change (Lagrange.interpolate Finset.univ (point m) a).eval 1=_
  rw [←polynomial]
  exact layer_at_one_is_physical_acceptance m n T

theorem actual_outer_at_one_guarded_count (answer : ℕ)
    (physicalCount : Nat.card {x : Fin m→Bool // coreA T x=true ∧ coreB T x=true}=1+answer) :
    (outerAtOne m (sampleNum m) (sampleDen m) (rootOldNumerator m n T)).value-1=(answer:ℚ) := by
  rw [actual_outer_at_one_is_physical_acceptance m n T,physicalCount]
  push_cast
  ring

#print axioms layer_at_one_is_physical_acceptance
#print axioms actual_outer_at_one_is_physical_acceptance
#print axioms actual_outer_at_one_guarded_count
end J6R52PublicSlot
