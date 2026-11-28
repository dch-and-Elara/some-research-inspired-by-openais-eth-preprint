import J3R60ActualTrace
import J3R60Operations
import J3R60BackWidth

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

/-! Actual MAIN J3 chosen addresses: exact solution, denominator clearing,
ordered count, and all forward/backwards integer widths from the numerical
height of this very augmented input. No external width table is passed. -/
namespace J3R60
open J3R59
open scoped BigOperators

def rationalMagnitude (q : ℚ) : ℕ := max q.num.natAbs q.den

def dataMax {I : Type*} [Fintype I] {n : ℕ} (A : I → Fin n → ℚ) (b : I → ℚ) : ℕ :=
  max ((Finset.univ : Finset (I × Fin n)).sup (fun ij => rationalMagnitude (A ij.1 ij.2)))
      ((Finset.univ : Finset I).sup (fun i => rationalMagnitude (b i)))

def inputBits {I : Type*} [Fintype I] {n : ℕ} (A : I → Fin n → ℚ) (b : I → ℚ) : ℕ :=
  Nat.clog 2 (dataMax A b)

theorem actual_data_covers {I : Type*} [Fintype I] {n : ℕ} (A : I → Fin n → ℚ) (b : I → ℚ) :
    (∀ i j, inputHeight (inputBits A b) (A i j)) ∧
      (∀ i, inputHeight (inputBits A b) (b i)) := by
  have hpow := Nat.le_pow_clog (by decide : 1 < 2) (dataMax A b)
  have hq (q : ℚ) (h : rationalMagnitude q ≤ dataMax A b) : inputHeight (inputBits A b) q := by
    exact ⟨(le_max_left _ _).trans (h.trans hpow), (le_max_right _ _).trans (h.trans hpow)⟩
  constructor
  · intro i j
    have hA : rationalMagnitude (A i j) ≤
        (Finset.univ : Finset (I × Fin n)).sup (fun ij => rationalMagnitude (A ij.1 ij.2)) :=
      Finset.le_sup (f := fun ij : I×Fin n => rationalMagnitude (A ij.1 ij.2))
        (Finset.mem_univ (i,j))
    exact hq _ (hA.trans (le_max_left _ _))
  · intro i
    have hb : rationalMagnitude (b i) ≤
        (Finset.univ : Finset I).sup (fun i => rationalMagnitude (b i)) :=
      Finset.le_sup (f := fun i : I => rationalMagnitude (b i)) (Finset.mem_univ i)
    exact hq _ (hb.trans (le_max_right _ _))

theorem ordered_length {I : Type*} [Fintype I] (rows : List I) (hn : rows.Nodup)
    (allRows : ∀ i, i ∈ rows) : rows.length = Fintype.card I := by
  classical
  have h : rows.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall (fun i => List.mem_toFinset.mpr (allRows i))
  exact (List.toFinset_card_of_nodup hn).symm.trans (by rw [h]; rfl)

/-- General same-run join on a true bit solution. All widths are computed
from this input, then proved along the actual first-pivot recurrence. -/
theorem true_bit_solver_budget {I : Type*} [Fintype I] (rows : List I)
    (allRows : ∀ i, i ∈ rows) {n : ℕ} (A : I → Fin n → ℚ) (b : I → ℚ)
    (inj : ∀ x : Fin n → ℚ, (∀ i, dot (A i) x = 0) → x = 0)
    (x : Fin n → ℚ) (hbit : ∀ j, x j=0 ∨ x j=1) (exactInput : ∀ i, dot (A i) x=b i) :
    let B := inputBits A b
    let D : ℚ := (clearDen rows A b : ℚ)
    let A' := fun i j => D*A i j
    let b' := fun i => D*b i
    let cap := minorCap (2^(B + B*((n+1)*rows.length))) (n+1)
    let run := measuredScaled rows A b
    run.1 = some x ∧
      ForwardBound rows cap n A' b' 1 ∧ BackBound rows cap n A' b' 1 x ∧
      2*run.2.forwardCells = rows.length*(n*(n+1)) ∧
      2*run.2.backTerms = n*(n-1) ∧ run.2.backPivots = n ∧
      run.2.pivotTests ≤ n*rows.length := by
  dsimp only
  let D : ℚ := (clearDen rows A b : ℚ)
  have hD : D ≠ 0 := Nat.cast_ne_zero.mpr (clearDen_nonzero rows A b)
  let A' : I → Fin n → ℚ := fun i j => D*A i j
  let b' : I → ℚ := fun i => D*b i
  have hdot (y : Fin n → ℚ) (i : I) : dot (A' i) y = D * dot (A i) y := by
    simp only [dot, A', Finset.mul_sum, mul_assoc]
  have he (i : I) : dot (A' i) x = b' i := by rw [hdot,exactInput]
  have hinj (y : Fin n → ℚ) (hy : ∀ i, dot (A' i) y=0) : y=0 := by
    apply inj
    intro i
    have h := hy i
    rw [hdot] at h
    exact (mul_eq_zero.mp h).resolve_left hD
  have h := actual_data_covers A b
  have hfw := cleared_actual_forward rows allRows A b h.1 h.2
  have hb := true_bit_back_width rows allRows _ n A' b' 1 one_ne_zero hinj x hbit he hfw
  have hsol : (measuredScaled rows A b).1 = some x :=
    (measuredScaled_result rows A b).trans (solveScaled_exact rows allRows A b inj x exactInput)
  have hsuccess : (measuredSolve rows n A' b' 1).1.isSome = true := by
    change (measuredScaled rows A b).1.isSome = true
    rw [hsol]; rfl
  obtain ⟨hf,hb',hp,hv⟩ := measured_success_counts rows n A' b' 1 hsuccess
  have hf' : 2 * (measuredScaled rows A b).2.forwardCells = rows.length*(n*(n+1)) := by
    change 2 * (measuredSolve rows n A' b' 1).2.forwardCells = _
    rw [hf, ← eliminationTriangle_exact n]
    ring
  have ht' : 2 * (measuredScaled rows A b).2.backTerms = n*(n-1) := by
    change 2 * (measuredSolve rows n A' b' 1).2.backTerms = _
    rw [hb', backTriangle_exact]
  exact ⟨hsol,hfw,hb,hf',ht',hp,hv⟩

open J3R38LiteralSingleton
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber
open scoped Classical
noncomputable section

variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J R : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

/-- End-to-end integer budget of the original R40 signed MAIN system.
Incoming width is derived from the actual public matrix and normalized
native readouts, not supplied by the caller. The source-barrier guard is
exactly the graph-only full rank test, not a bound on any pivot data. -/
theorem original_J3_actual_budget (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (hr : 2 ≤ r) (hR : 1 ≤ R) (hfit : 6*R ≤ Q)
    (Aset : Finset (Address W Q)) (ok : ∀ a ∈ Aset, Admissible hreg Prow a.1)
    (hRank : (graphMatrix hreg Prow Aset).rank=Fintype.card W)
    (rows : List {a // a ∈ Aset}) (hn : rows.Nodup) (allRows : ∀ a, a ∈ rows)
    (cols : Fin (Fintype.card W) ≃ W) (s : W → Bool) :
    let n := Fintype.card W
    let A : {a // a ∈ Aset} → Fin n → ℚ := fun a j => graphEntry hreg Prow a.val (cols j)
    let b : {a // a ∈ Aset} → ℚ := fun a =>
      normalize P R hJ Prow a.val (rawJet P R hJ Prow a.val s)
    let B := inputBits A b
    let D : ℚ := (clearDen rows A b : ℚ)
    let A' := fun i j => D*A i j
    let b' := fun i => D*b i
    let cap := minorCap (2^(B + B*((n+1)*rows.length))) (n+1)
    let run := measuredScaled rows A b
    let x : Fin n → ℚ := fun j => JointContraction.bitScalar ℚ (s (cols j))
    rows.length = Aset.card ∧ Aset.card ≤ Q*(4*n) ∧
      run.1 = some x ∧ ForwardBound rows cap n A' b' 1 ∧ BackBound rows cap n A' b' 1 x ∧
      2*run.2.forwardCells = rows.length*(n*(n+1)) ∧
      2*run.2.backTerms = n*(n-1) ∧ run.2.backPivots = n ∧
      run.2.pivotTests ≤ n*rows.length := by
  dsimp only
  let n := Fintype.card W
  let G (a : {a // a ∈ Aset}) (v : W) : ℚ := graphEntry hreg Prow a.val v
  let A := fun (a : {a // a ∈ Aset}) (j : Fin n) => G a (cols j)
  let b := fun (a : {a // a ∈ Aset}) =>
    normalize P R hJ Prow a.val (rawJet P R hJ Prow a.val s)
  let M := graphMatrix hreg Prow Aset
  have hdim : M.rank + Module.finrank ℚ (LinearMap.ker M.mulVecLin) = n := by
    simpa only [Matrix.rank,Module.finrank_pi] using
      (LinearMap.finrank_range_add_finrank_ker M.mulVecLin)
  have hm : M.rank = n := hRank
  have hk : LinearMap.ker M.mulVecLin = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    omega
  have reindex (a : {a // a ∈ Aset}) (z : W → ℚ) :
      dot (A a) (fun j => z (cols j)) = ∑ v, G a v*z v := by
    apply Fintype.sum_equiv cols
    exact fun _ => rfl
  have hi (x : Fin n → ℚ) (hx : ∀ a, dot (A a) x=0) : x=0 := by
    let y := fun v => x (cols.symm v)
    have hy : (fun j => y (cols j))=x := by funext j; simp [y]
    have hz : M.mulVecLin y=0 := by
      funext a
      change (∑ v, G a v * y v) = 0
      rw [← reindex a y,hy,hx]
    have h0 := (LinearMap.ker_eq_bot.mp hk) (show M.mulVecLin y = M.mulVecLin 0 by
      rw [map_zero]; exact hz)
    funext j
    simpa [y] using congrFun h0 (cols j)
  let z := fun v => JointContraction.bitScalar ℚ (s v)
  have he (a : {a // a ∈ Aset}) : dot (A a) (fun j => z (cols j))=b a :=
    (reindex a z).trans (original_J3_equation P Prow hJ hr hR hfit a.val (ok _ a.property) s).2.symm
  have hbit (j : Fin n) : z (cols j)=0 ∨ z (cols j)=1 := by
    cases h : s (cols j) <;> simp [z,JointContraction.bitScalar,h]
  exact ⟨by simpa only [Fintype.card_coe] using ordered_length rows hn allRows,
    menu_size Aset,true_bit_solver_budget rows allRows A b hi _ hbit he⟩

#print axioms actual_data_covers
#print axioms ordered_length
#print axioms true_bit_solver_budget
#print axioms original_J3_actual_budget

end
end J3R60
