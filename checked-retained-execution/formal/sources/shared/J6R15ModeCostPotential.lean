import J6R15ModeCostEnum
import Mathlib.Algebra.BigOperators.Ring.List

/-! A finite rational generating-product bound for the same exact
strict tuples. This is cardinality only, not DFS delay or child
multiplicity. No exp/log or infinite series enters this kernel. -/
namespace J6R15ModeCost

def weightSum (r : ℚ) (ws : List ℕ) (K : ℕ) : ℚ :=
  ((enumerate ws K).map (fun xs => r^weightedDegree ws xs)).sum

def geometric (r : ℚ) (n : ℕ) : ℚ := ((List.range n).map (fun j => r^j)).sum

def potential (r : ℚ) (ws : List ℕ) : ℚ := (ws.map (fun w => (1-r^w)⁻¹)).prod

theorem ratSum_cmp {A : Type*} (f g : A→ℚ) (xs : List A)
    (h : ∀ x∈xs,f x≤g x) : (xs.map f).sum≤(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem weightedFlatSum {A : Type*} (f : A→List ℚ) (xs : List A) :
    (xs.flatMap f).sum=(xs.map (fun x=>(f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih => rw [List.flatMap_cons,List.sum_append,ih,List.map_cons,List.sum_cons]

theorem geometric_product (r : ℚ) (n : ℕ) :
    (1-r)*geometric r n=1-r^n := by
  induction n with
  | zero => simp [geometric]
  | succ n ih =>
    have H : geometric r (n+1)=geometric r n+r^n := by
      rw [geometric,List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
      rfl
    rw [H,mul_add,ih,pow_succ]
    ring

theorem geometric_le (r : ℚ) (hr : 0≤r) (hR : r<1) (n : ℕ) :
    geometric r n≤(1-r)⁻¹ := by
  rw [← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hR)).mpr
  rw [mul_comm,geometric_product]
  have h := pow_nonneg hr n
  linarith

theorem weightSum_cons (r : ℚ) (w : ℕ) (ws : List ℕ) (K : ℕ) :
    weightSum r (w::ws) K=
      ((List.range (K/w+1)).map (fun a=>(r^w)^a*weightSum r ws (K-w*a))).sum := by
  unfold weightSum
  rw [enumerate,List.map_flatMap,weightedFlatSum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  simp only [List.map_map,Function.comp_def,weightedDegree,pow_add,pow_mul,List.sum_map_mul_left]

theorem potential_nonneg (r : ℚ) (hr : 0≤r) (hR : r<1)
    (ws : List ℕ) (hp : ∀ w∈ws,0<w) : 0≤potential r ws := by
  induction ws with
  | nil => simp [potential]
  | cons w ws ih =>
    change 0≤(1-r^w)⁻¹*potential r ws
    exact mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr
      (pow_lt_one₀ hr hR (hp w List.mem_cons_self).ne').le))
      (ih (fun v hv=>hp v (List.mem_cons_of_mem _ hv)))

theorem weightSum_potential (r : ℚ) (hr : 0≤r) (hR : r<1) (ws : List ℕ)
    (hp : ∀ w∈ws,0<w) (K : ℕ) :
    weightSum r ws K≤potential r ws := by
  induction ws generalizing K with
  | nil => simp [weightSum,enumerate,potential,weightedDegree]
  | cons w ws ih =>
    have hw := hp w List.mem_cons_self
    have hp' : ∀ v∈ws,0<v := fun v hv => hp v (List.mem_cons_of_mem _ hv)
    have hP := potential_nonneg r hr hR ws hp'
    have hN := pow_nonneg hr w
    have hW := pow_lt_one₀ hr hR hw.ne'
    rw [weightSum_cons]
    calc
      _≤((List.range (K/w+1)).map (fun a=>(r^w)^a*potential r ws)).sum :=
        ratSum_cmp _ _ _ (fun a _ => mul_le_mul_of_nonneg_left (ih hp' _) (pow_nonneg hN _))
      _=geometric (r^w) (K/w+1)*potential r ws := by
        rw [geometric,List.sum_map_mul_right]
      _≤potential r (w::ws) := by
        unfold potential
        change geometric (r^w) (K/w+1)*potential r ws≤(1-r^w)⁻¹*potential r ws
        exact mul_le_mul_of_nonneg_right (geometric_le _ hN hW _) hP

theorem constRat_sum {A : Type*} (c : ℚ) (xs : List A) :
    (xs.map (fun _=>c)).sum=(xs.length:ℚ)*c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,ih,List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

theorem tuple_potential (r : ℚ) (hr : 0<r) (hR : r<1) (ws : List ℕ)
    (hp : ∀ w∈ws,0<w) (K : ℕ) :
    ((enumerate ws K).length:ℚ)≤potential r ws/(r^K) := by
  apply (le_div_iff₀ (pow_pos hr _)).mpr
  rw [← constRat_sum]
  apply le_trans (b:=weightSum r ws K) _ (weightSum_potential r hr.le hR ws hp K)
  unfold weightSum
  apply ratSum_cmp
  intro es he
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le ((enumerate_mem hp K es).mp he).2
  rw [hj,pow_add]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hR.le) (pow_nonneg hr.le _)).trans_eq (mul_one _)

theorem strict_tuple_potential (r : ℚ) (hr : 0<r) (hR : r<1) (ws : List ℕ)
    (hp : ∀ w∈ws,0<w) (p : ℕ) (hp' : 0<p) :
    ((strictTuples ws p).length:ℚ)≤potential r ws/(r^(p-1)) := by
  rw [strictTuples,if_neg hp'.ne']
  exact tuple_potential r hr hR ws hp (p-1)

#print axioms geometric_le
#print axioms weightSum_potential
#print axioms strict_tuple_potential
end J6R15ModeCost



