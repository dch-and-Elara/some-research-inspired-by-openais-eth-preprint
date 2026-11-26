import P5MainBalanceM6Grade

/-! Actual 1+2j affine-factor expansion underlying the sparse
source e_j(L) h(L)^j. All outputs remain lists of the same typed
ports as the input L; this is a semantic expansion, not a claim that
the native algorithm enumerates these lists when compiling. -/
namespace P5MainBalance.M6.Sparse
open scoped BigOperators Classical

variable {A K : Type*} [CommRing K]

def letters (m : List A) (Y : A→K) : K := (m.map Y).prod

theorem letters_append (m n : List A) (Y : A→K) :
    letters (m++n) Y=letters m Y*letters n Y := by
  simp only [letters,List.map_append,List.prod_append]

theorem letters_ofFn {j : ℕ} (M : Fin j→List A) (Y : A→K) :
    letters (List.ofFn M).flatten Y=∏ i,letters (M i) Y := by
  unfold letters
  rw [List.map_flatten,List.prod_flatten,List.map_ofFn,List.map_ofFn,List.prod_ofFn]
  rfl

theorem length_ofFn_flatten {j : ℕ} (M : Fin j→List A) :
    (List.ofFn M).flatten.length=∑ i,(M i).length := by
  rw [List.length_flatten,List.map_ofFn,List.sum_ofFn]
  rfl

def extended {c : ℕ} (ms : Fin c→List A) : Fin (c+1)→List A := Fin.cases [] ms

def affineWeight {c : ℕ} (w : Fin c→ℚ) (a b : ℚ) : Fin (c+1)→ℚ :=
  Fin.cases a (fun i=>b*w i)

noncomputable def sumMonomials {c : ℕ} (ms : Fin c→List A) (w : Fin c→ℚ)
    (ι : ℚ→+*K) (Y : A→K) : K :=
  ∑ i,ι (w i)*letters (ms i) Y

theorem affine_sum {c : ℕ} (ms : Fin c→List A) (w : Fin c→ℚ) (ι : ℚ→+*K)
    (Y : A→K) (a b : ℚ) :
    ∑ i,ι (affineWeight w a b i)*letters (extended ms i) Y =
      ι a+ι b*sumMonomials ms w ι Y := by
  rw [Fin.sum_univ_succ]
  simp only [affineWeight,extended,Fin.cases_zero,letters,List.map_nil,List.prod_nil,mul_one,
    Fin.cases_succ,map_mul,sumMonomials,Finset.mul_sum,mul_assoc]

abbrev Choice (c j : ℕ) := Fin (c+1) × (Fin j→Fin (c+1)×Fin (c+1))

def modeTerms {c j : ℕ} (ms : Fin c→List A) (q : Choice c j) : List A :=
  extended ms q.1 ++
    (List.ofFn (fun k=>extended ms (q.2 k).1 ++ extended ms (q.2 k).2)).flatten

noncomputable def modeWeight {c j : ℕ} (w : Fin c→ℚ) (a b : ℚ) (q : Choice c j) : ℚ :=
  affineWeight w a b q.1 * ∏ k,affineWeight w 0 1 (q.2 k).1*affineWeight w (-1) 1 (q.2 k).2

theorem modeTerms_length {c j : ℕ} (ms : Fin c→List A) (q : Choice c j)
    (h : ∀ i,(ms i).length≤2) :
    (modeTerms ms q).length≤2+4*j := by
  have h' (i : Fin (c+1)) : (extended ms i).length≤2 := by
    refine Fin.cases ?_ (fun k=>?_) i
    · simp [extended]
    · exact h k
  unfold modeTerms
  rw [List.length_append,length_ofFn_flatten]
  simp only [List.length_append]
  have hsum : (∑ k : Fin j,((extended ms (q.2 k).1).length+(extended ms (q.2 k).2).length))≤∑ _k : Fin j,4 := by
    apply Finset.sum_le_sum
    intro k _
    have := h' (q.2 k).1
    have := h' (q.2 k).2
    omega
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin] at hsum
  change (∑ k : Fin j,((extended ms (q.2 k).1).length+(extended ms (q.2 k).2).length)) ≤ j*4 at hsum
  exact (Nat.add_le_add (h' q.1) hsum).trans (by rw [Nat.mul_comm j 4])

set_option maxHeartbeats 9000000 in
theorem mode_sum {c j : ℕ} (ms : Fin c→List A) (w : Fin c→ℚ) (ι : ℚ→+*K)
    (Y : A→K) (a b : ℚ) :
    ∑ q : Choice c j,ι (modeWeight w a b q)*letters (modeTerms ms q) Y =
      (ι a+ι b*sumMonomials ms w ι Y)*
        (sumMonomials ms w ι Y*(sumMonomials ms w ι Y-1))^j := by
  let s (u v : ℚ) (i : Fin (c+1)) := ι (affineWeight w u v i)*letters (extended ms i) Y
  let p (q : Fin (c+1)×Fin (c+1)) := s 0 1 q.1*s (-1) 1 q.2
  have hterm (q : Choice c j) :
      ι (modeWeight w a b q)*letters (modeTerms ms q) Y =
        s a b q.1 * ∏ k,p (q.2 k) := by
    unfold modeWeight modeTerms
    simp only [map_mul,map_prod,letters_append,letters_ofFn,s,p]
    calc
      _ = (ι (affineWeight w a b q.1)*letters (extended ms q.1) Y)*
          ((∏ x : Fin j,ι (affineWeight w 0 1 (q.2 x).1)*ι (affineWeight w (-1) 1 (q.2 x).2))*
           (∏ x : Fin j,letters (extended ms (q.2 x).1) Y*letters (extended ms (q.2 x).2) Y)) := by ring
      _ = _ := by
        rw [←Finset.prod_mul_distrib]
        congr 1
        exact Finset.prod_congr rfl (fun _ _=>by ring)
  have hpair :
      (∑ q : Fin (c+1)×Fin (c+1),p q)=
        sumMonomials ms w ι Y*(sumMonomials ms w ι Y-1) := by
    rw [Fintype.sum_prod_type]
    change (∑ i,∑ k,s 0 1 i*s (-1) 1 k)=_
    simp_rw [←Finset.mul_sum]
    rw [←Finset.sum_mul]
    unfold s
    rw [affine_sum,affine_sum]
    simp only [map_zero,map_one,map_neg,one_mul,zero_add]
    ring
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  change (∑ i : Fin (c+1),∑ q : Fin j→Fin (c+1)×Fin (c+1),s a b i*∏ k,p (q k))=_
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul,←Fintype.prod_sum (fun (_k : Fin j) => p)]
  simp only [hpair,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  unfold s
  rw [affine_sum]

#print axioms letters_ofFn
#print axioms length_ofFn_flatten
#print axioms affine_sum
#print axioms modeTerms_length
#print axioms mode_sum
end P5MainBalance.M6.Sparse
