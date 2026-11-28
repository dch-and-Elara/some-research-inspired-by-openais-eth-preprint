import V8CapacityMatrixImage

/-! Discarding invisible Smith directions gives the actual separated
fraction-field upper witness in A3 over any attained sender subset. -/
namespace V8CapacityWidthUpper
open scoped Classical BigOperators
open Module V8CapacitySmith

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

variable {O M I : Type*} [CommRing O] [IsDomain O]
variable [AddCommGroup M] [Module O M] [Fintype I]
variable {π : O} {N : Submodule O M} {n : ℕ}
variable (S : Powered π N I n)

abbrev Active (P : ℕ) := {i : Fin n // S.exponent i<P}

def retained (P : ℕ) (x : N) : N :=
  ∑ i : Active S P, S.chart.bN.repr x i • S.chart.bN i

theorem eval_raw (e : M →ₗ[O] O) (x : N) :
    e x = ∑ i : Fin n, S.chart.bN.repr x i * e (S.chart.bN i) := by
  let g := e.comp N.subtype
  simpa only [map_sum,map_smul,smul_eq_mul,LinearMap.comp_apply,Submodule.subtype_apply] using
    (congrArg g (S.chart.bN.sum_repr x)).symm

theorem eval_retained (P : ℕ) (e : M →ₗ[O] O) (x : N) :
    e (retained S P x) = ∑ i : Active S P, S.chart.bN.repr x i * e (S.chart.bN i) := by
  simp [retained,map_sum]

theorem discard_mod (P : ℕ) (e : M →ₗ[O] O) (x : N) :
    π^P∣ e x-e (retained S P x) := by
  rw [eval_raw S e x,eval_retained S P]
  let f (j : Fin n) := S.chart.bN.repr x j * e (S.chart.bN j)
  let a := Finset.univ.filter (fun i : Fin n => S.exponent i<P)
  let b := Finset.univ.filter (fun i : Fin n => ¬ S.exponent i<P)
  have ht : (∑ i : Active S P, f i) = ∑ i ∈ a, f i := by
    symm
    exact Finset.sum_subtype a (by simp [a]) f
  change π^P∣ (∑ i : Fin n, f i)-(∑ i : Active S P, f i)
  rw [ht,← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin n => S.exponent i<P) f]
  change π^P∣ ((∑ i ∈ a, f i)+(∑ i ∈ b, f i))-(∑ i ∈ a, f i)
  rw [add_sub_cancel_left]
  refine Finset.dvd_sum (fun i hi => ?_)
  have h : P≤S.exponent i := Nat.le_of_not_gt (Finset.mem_filter.mp hi).2
  unfold f
  rw [S.chart.snf,S.powerDiag,map_smul,smul_eq_mul]
  exact dvd_mul_of_dvd_right
    (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow π h) _) _) _

variable {K F A C : Type*} [Field K] [Algebra O K] [IsFractionRing O K] [Fintype F]
variable (hπ : π≠0)

include hπ in
theorem divided_diff (L p : ℕ) (u v : O) (h : π^(L+p)∣u-v) :
    ∃ δ : O, (algebraMap O K u)/(algebraMap O K (π^L))-
      (algebraMap O K v)/(algebraMap O K (π^L)) = algebraMap O K (π^p*δ) := by
  obtain ⟨δ,hδ⟩ := h
  refine ⟨δ,?_⟩
  rw [← sub_div,← map_sub,hδ,pow_add,mul_assoc]
  have hn : algebraMap O K (π^L)≠0 :=
    fun h => (pow_ne_zero _ hπ) ((IsFractionRing.injective O K) (h.trans (map_zero _).symm))
  rw [map_mul]
  field_simp

include hπ in
/-- Number of separated terms is exactly the finite product of the
fiber types and the active Smith coordinates. No restriction is made
on the shape of the actual sender set A or receiver set C. -/
theorem separated_fraction_upper (L p : ℕ) (fiber : A → F)
    (obs : A → (M →ₗ[O] O)) (col : F → C → N) :
    ∃ l : A → F × Active S (L+p) → K, ∃ r : F × Active S (L+p) → C → K,
      ∀ a c, ∃ δ : O,
        algebraMap O K (obs a (col (fiber a) c))/(algebraMap O K (π^L))-
          (∑ i : F × Active S (L+p), l a i*r i c)=algebraMap O K (π^p*δ) := by
  let l := fun (a : A) (i : F × Active S (L+p)) =>
    if i.1=fiber a then
      algebraMap O K (obs a (S.chart.bN i.2))/(algebraMap O K (π^L)) else 0
  let r := fun (i : F × Active S (L+p)) (c : C) =>
    algebraMap O K (S.chart.bN.repr (col i.1 c) i.2)
  refine ⟨l,r,fun a c => ?_⟩
  have hδ := divided_diff (K:=K) hπ L p
    (obs a (col (fiber a) c)) (obs a (retained S (L+p) (col (fiber a) c)))
    (discard_mod S (L+p) (obs a) (col (fiber a) c))
  obtain ⟨δ,hδ⟩ := hδ
  refine ⟨δ,?_⟩
  rw [Fintype.sum_prod_type]
  have houter :
      (∑ i : F, ∑ j : Active S (L+p), l a (i,j)*r (i,j) c) =
      ∑ j : Active S (L+p), l a (fiber a,j)*r (fiber a,j) c :=
    Finset.sum_eq_single_of_mem (fiber a) (Finset.mem_univ _)
      (fun i _ hi => by simp [l,hi])
  rw [houter]
  convert hδ using 2
  rw [eval_retained S, map_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [l,r,if_pos rfl,map_mul]
  ring

#print axioms eval_raw
#print axioms eval_retained
#print axioms discard_mod
#print axioms divided_diff
#print axioms separated_fraction_upper
end
end V8CapacityWidthUpper

