
import J6R22RootReadoutOuter
import J6R22RootReadoutNativeFactor
import J7R10Readout

/-! Outer interpolation from the true old integer numerators, without
any raw sample from another physical layout appearing in the proof. -/
namespace J6R25StableCensus
open scoped BigOperators Classical Polynomial
open Polynomial Std.Sat J6Mesh J6NativeHeightMesh J6IntegerLayers
open J6OrientedHost J6OrientedHostEval J7R10Plant J6R22RootReadout
set_option maxHeartbeats 18000000
set_option linter.unusedSectionVars false

theorem old_fold_sample {V : Type*} [Fintype V] (m q : ℕ) (T : Plant V m q)
    (i : J6Recovery.Addr m) :
    ((rootOldNumerator m q T i:ℤ):ℚ)/(sampleDen m i:ℚ)^m=
        (J7R10Readout.layer m q T).eval (point m i) := by
  have d := (mesh_bounds m i).1.ne'
  have p : (sampleDen m i:ℚ)^m≠0 := pow_ne_zero _ (by exact_mod_cast d)
  unfold rootOldNumerator
  rw [oldLayer_cast _ _ _ _ d,Fintype.card_fin,←mesh_fraction,mul_div_cancel_left₀ _ p]
  rfl

theorem exact_plain_outer_count {V : Type*} [DecidableEq V] [Fintype V] [Nonempty V] (F : CNF V) :
    let m := J7R10Readout.mCNF F
    let q := J7R10Readout.qCNF F
    let T := physicalPlant (J7R10Readout.H F)
    (outerAtOne m (sampleNum m) (sampleDen m) (rootOldNumerator m q T)).value-1=
      (PinnedCNF.modelCount F:ℚ) := by
  let m := J7R10Readout.mCNF F
  let q := J7R10Readout.qCNF F
  let T := physicalPlant (J7R10Readout.H F)
  let f := J7R10Readout.layer m q T
  let a := fun i : J6Recovery.Addr m=>
    ((rootOldNumerator m q T i:ℤ):ℚ)/(sampleDen m i:ℚ)^m
  have points : (fun i : J6Recovery.Addr m=>(sampleNum m i:ℚ)/sampleDen m i)=point m :=
    funext fun i=>(mesh_fraction m i).symm
  have E := outer_at_one_exact m (sampleNum m) (sampleDen m) (rootOldNumerator m q T)
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
  have interpolation : f=Lagrange.interpolate Finset.univ (point m) a :=
    Lagrange.eq_interpolate_of_eval_eq a (negative_distinct_points m).2.injOn hdegree
      (fun j _=>(old_fold_sample m q T j).symm)
  change (outerAtOne m (sampleNum m) (sampleDen m) (rootOldNumerator m q T)).value-1=_
  rw [E]
  change (Lagrange.interpolate Finset.univ (point m) a).eval 1-1=_
  rw [←interpolation]
  change (LayerRecovery.layerPolynomial _ _).eval 1-1=_
  rw [guarded_origin_exact F]
  push_cast
  ring

#print axioms old_fold_sample
#print axioms exact_plain_outer_count
end J6R25StableCensus
