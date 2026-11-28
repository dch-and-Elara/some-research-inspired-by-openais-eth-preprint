import J7LiteralGraph

/-! # Quantitative expansion preservation by the literal triangle replacement -/

open scoped BigOperators Classical

namespace J7LiteralGraphExpansion
open J7LiteralGraph J7SourceLabels

noncomputable section
set_option maxHeartbeats 2200000

private def bit (p : Prop) : ℕ := if p then 1 else 0
private def xcut (p q : Prop) : ℕ := bit (¬ (p ↔ q))

private theorem bit_le_one (p : Prop) : bit p ≤ 1 := by by_cases h : p <;> simp [bit,h]

private theorem count_filter {X : Type*} [Fintype X] (p : X → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ x : X, bit (p x) := by
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => by by_cases h : p x <;> simp [bit,h]

variable {V : Type*} [LinearOrder V] (H : SimpleGraph V) [Fintype V] [DecidableRel H.Adj]
variable (cubic : Cubic H)

def fiber (S : Finset (V × Fin 3)) (v : V) : Finset (Fin 3) := Finset.univ.filter fun i => (v,i) ∈ S

def full (S : Finset (V × Fin 3)) : Finset V := Finset.univ.filter fun v => (fiber S v).card = 3

def mixedClouds (S : Finset (V × Fin 3)) : Finset V :=
  Finset.univ.filter fun v => 0 < (fiber S v).card ∧ (fiber S v).card < 3

omit [Fintype V] in
private theorem fiber_bound (S : Finset (V × Fin 3)) (v : V) : (fiber S v).card ≤ 3 := by
  have hh := Finset.card_le_card (Finset.subset_univ (fiber S v))
  simpa using hh

private theorem sum_fibers (S : Finset (V × Fin 3)) :
    (∑ v : V, (fiber S v).card) = S.card := by
  have hh : (Finset.univ : Finset (V × Fin 3)).filter (· ∈ S) = S := by
    ext x; simp
  calc
    _ = ∑ v : V, ∑ i : Fin 3, bit ((v,i) ∈ S) :=
      Finset.sum_congr rfl fun v _ => count_filter _
    _ = ∑ q : V × Fin 3, bit (q ∈ S) := (Fintype.sum_prod_type (fun q : V × Fin 3 => bit (q ∈ S))).symm
    _ = S.card := (count_filter _).symm.trans (congrArg Finset.card hh)

private theorem full_partial_sandwich (S : Finset (V × Fin 3)) :
    3*(full S).card ≤ S.card ∧ S.card ≤ 3*(full S).card+2*(mixedClouds S).card := by
  have hu (v : V) : (fiber S v).card ≤ 3*bit ((fiber S v).card=3) +
      2*bit (0 < (fiber S v).card ∧ (fiber S v).card < 3) := by
    have hb := fiber_bound S v
    by_cases h : (fiber S v).card=3
    · simp [bit,h]
    · by_cases h0 : (fiber S v).card=0
      · simp [bit,h0]
      · have h' : 0 < (fiber S v).card ∧ (fiber S v).card < 3 := by omega
        simp only [bit,if_neg h,if_pos h']
        omega
  have hl (v : V) : 3*bit ((fiber S v).card=3) ≤ (fiber S v).card := by
    by_cases h : (fiber S v).card=3 <;> simp [bit,h]
  constructor
  · unfold full
    rw [count_filter,Finset.mul_sum,←sum_fibers S]
    exact Finset.sum_le_sum fun v _ => hl v
  · unfold full mixedClouds
    rw [count_filter,count_filter,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,←sum_fibers S]
    exact Finset.sum_le_sum fun v _ => hu v

private theorem membership_not_partial (S : Finset (V × Fin 3)) (v : V) (i : Fin 3)
    (hv : v ∉ mixedClouds S) : ((v,i) ∈ S ↔ v ∈ full S) := by
  have hb := fiber_bound S v
  have hn : ¬ (0 < (fiber S v).card ∧ (fiber S v).card < 3) := by
    simpa only [mixedClouds,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have alt : (fiber S v).card=0 ∨ (fiber S v).card=3 := by omega
  rcases alt with h | h
  · have he := Finset.card_eq_zero.mp h
    have hi : i ∉ fiber S v := by rw [he]; simp
    have hj : (v,i) ∉ S := by simpa only [fiber,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    simp [full,h,hj]
  · have he : fiber S v = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simp [h]
    have hi : i ∈ fiber S v := by rw [he]; simp
    have hj : (v,i) ∈ S := by simpa only [fiber,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    simp [full,h,hj]

def baseCut (F : Finset V) : ℕ :=
  ∑ e : Edge H, xcut (e.val.1 ∈ F) (e.val.2 ∈ F)

def point (e : TEdge H) (b : Bool) : V × Fin 3 := pinToTriangle H cubic (endPin H cubic e b)

def exteriorCut (S : Finset (V × Fin 3)) : ℕ :=
  ∑ e : Edge H, xcut (point H cubic (.inl e) false ∈ S) (point H cubic (.inl e) true ∈ S)

def internalCut (S : Finset (V × Fin 3)) : ℕ :=
  ∑ q : V × Fin 3, xcut (point H cubic (.inr q) false ∈ S) (point H cubic (.inr q) true ∈ S)

def triangleCut (S : Finset (V × Fin 3)) : ℕ :=
  ∑ e : TEdge H, xcut (point H cubic e false ∈ S) (point H cubic e true ∈ S)

theorem cut_split (S : Finset (V × Fin 3)) :
    triangleCut H cubic S = exteriorCut H cubic S + internalCut H cubic S := by
  unfold triangleCut exteriorCut internalCut
  exact Fintype.sum_sum_type _

/-- Exact finite three-bit calculation of the boundary within one cloud. -/
private theorem triangle_bits (z : Fin 3 → Bool) :
    (∑ i : Fin 3, if z i ≠ z (rot i) then 1 else 0 : ℕ) =
      if 0 < (∑ i : Fin 3, if z i then 1 else 0 : ℕ) ∧
        (∑ i : Fin 3, if z i then 1 else 0 : ℕ) < 3 then 2 else 0 := by
  revert z
  decide

theorem mixed_triangles (S : Finset (V × Fin 3)) :
    internalCut H cubic S = 2*(mixedClouds S).card := by
  unfold internalCut mixedClouds
  rw [Fintype.sum_prod_type,count_filter,Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  let z : Fin 3 → Bool := fun i => decide ((v,i)∈S)
  have hf : (fiber S v).card = ∑ i : Fin 3, if z i then 1 else 0 := by
    unfold fiber
    rw [count_filter]
    exact Finset.sum_congr rfl fun i _ => by by_cases h : (v,i) ∈ S <;> simp [bit,z,h]
  have hs (i : Fin 3) : xcut (point H cubic (.inr (v,i)) false ∈ S)
      (point H cubic (.inr (v,i)) true ∈ S) = if z i ≠ z (rot i) then 1 else 0 := by
    unfold point
    rw [inside_owners,inside_owners]
    change xcut ((v,i)∈S) ((v,rot i)∈S) = _
    by_cases h : (v,i) ∈ S <;> by_cases h' : (v,rot i) ∈ S <;> simp [bit,xcut,z,h,h']
  simp only [hs,hf]
  rw [triangle_bits]
  unfold bit
  by_cases h : (0 < (∑ i : Fin 3, if z i then 1 else 0 : ℕ) ∧
      (∑ i : Fin 3, if z i then 1 else 0 : ℕ) < 3)
  · simp only [h.1,h.2,true_and,if_true,mul_one]
  · simp only [h,if_false,mul_zero]

include cubic in
private theorem count_owner (P : Finset V) :
    (∑ e : Edge H, (bit (e.val.1 ∈ P) + bit (e.val.2 ∈ P))) = 3*P.card := by
  let A := (Equiv.prodCongr (Equiv.refl (Edge H)) finSide).trans (pinToTriangle H cubic)
  have h₀ : (∑ eb : Edge H × Bool, bit ((A eb).1 ∈ P)) =
      ∑ q : V × Fin 3, bit (q.1 ∈ P) := Fintype.sum_equiv A _ _ fun _ => rfl
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type] at h₀
  have h₁ (e : Edge H) : (∑ b : Bool, bit ((A (e,b)).1 ∈ P)) =
      bit (e.val.1 ∈ P) + bit (e.val.2 ∈ P) := by
    have hl : (A (e,false)).1 = e.val.1 := (outside_owners H cubic e).1
    have hr : (A (e,true)).1 = e.val.2 := (outside_owners H cubic e).2
    simp [hl,hr,Nat.add_comm]
  simp only [h₁,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h₀
  rw [h₀,←Finset.mul_sum]
  congr 1
  have h := count_filter (fun v : V => v ∈ P)
  have he : (Finset.univ : Finset V).filter (· ∈ P) = P := by ext x; simp
  rw [he] at h
  exact h.symm

theorem charge_base_edges (S : Finset (V × Fin 3)) :
    baseCut H (full S) ≤ exteriorCut H cubic S + 3*(mixedClouds S).card := by
  unfold baseCut exteriorCut
  rw [← count_owner H cubic (mixedClouds S),←Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  by_cases l : e.val.1 ∈ mixedClouds S
  · have h := bit_le_one (¬ (e.val.1 ∈ full S ↔ e.val.2 ∈ full S))
    simp only [xcut,bit,if_pos l] at *
    omega
  by_cases r : e.val.2 ∈ mixedClouds S
  · have h := bit_le_one (¬ (e.val.1 ∈ full S ↔ e.val.2 ∈ full S))
    simp only [xcut,bit,if_pos r] at *
    omega
  have left : point H cubic (.inl e) false ∈ S ↔ e.val.1 ∈ full S := by
    let q := point H cubic (.inl e) false
    have hq : q.1 = e.val.1 := (outside_owners H cubic e).1
    exact (membership_not_partial S q.1 q.2 (by rw [hq]; exact l)).trans (by rw [hq])
  have right : point H cubic (.inl e) true ∈ S ↔ e.val.2 ∈ full S := by
    let q := point H cubic (.inl e) true
    have hq : q.1 = e.val.2 := (outside_owners H cubic e).2
    exact (membership_not_partial S q.1 q.2 (by rw [hq]; exact r)).trans (by rw [hq])
  by_cases hc : e.val.1 ∈ full S ↔ e.val.2 ∈ full S <;>
    simp [xcut,bit,left,right,l,r,hc]

/-- Quantified expansion on the literal indexed edges. A lower bound h
for the starting cubic graph gives h/(5+h) here (in crossing edges per
vertex). The expander family itself is an input, not asserted to exist. -/
theorem preserves_expansion (h : ℚ) (hpos : 0 < h)
    (base_expands : ∀ F : Finset V, 2*F.card ≤ Fintype.card V → h*(F.card:ℚ) ≤ baseCut H F)
    (S : Finset (V × Fin 3)) (size : 2*S.card ≤ 3*Fintype.card V) :
    (h/(5+h))*(S.card:ℚ) ≤ triangleCut H cubic S := by
  have hs := full_partial_sandwich S
  have hsmall : 2*(full S).card ≤ Fintype.card V := by omega
  have hbase := base_expands (full S) hsmall
  have charge := charge_base_edges H cubic S
  have mixed := mixed_triangles H cubic S
  have ht := cut_split H cubic S
  have hsQ : (S.card:ℚ) ≤ 3*((full S).card:ℚ)+2*((mixedClouds S).card:ℚ) := by exact_mod_cast hs.2
  have hcQ : (baseCut H (full S):ℚ) ≤ (exteriorCut H cubic S:ℚ)+3*((mixedClouds S).card:ℚ) := by exact_mod_cast charge
  have hM : (internalCut H cubic S:ℚ) = 2*((mixedClouds S).card:ℚ) := by exact_mod_cast mixed
  have hT : (triangleCut H cubic S:ℚ) =
      (exteriorCut H cubic S:ℚ)+(internalCut H cubic S:ℚ) := by exact_mod_cast ht
  have hp : 2*((mixedClouds S).card:ℚ) ≤ (triangleCut H cubic S:ℚ) := by
    rw [hT,hM]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hsize' := mul_le_mul_of_nonneg_left hsQ hpos.le
  have hsp := mul_le_mul_of_nonneg_left hp hpos.le
  have he : 0 ≤ (exteriorCut H cubic S:ℚ) := by positivity
  have hpar : 0 ≤ ((mixedClouds S).card:ℚ) := by positivity
  have hl : h*(S.card:ℚ) ≤ (5+h)*(triangleCut H cubic S:ℚ) := by nlinarith
  have hz : 0 < 5+h := by linarith
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hz).2 (by linarith)

#print axioms cut_split
#print axioms mixed_triangles
#print axioms charge_base_edges
#print axioms preserves_expansion

end
end J7LiteralGraphExpansion
