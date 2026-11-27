import GrenetPaper
import Mathlib.Data.Rat.Floor

open Matrix GrenetMcCoy Round4Transfer

namespace GrenetRational

variable {R ι : Type*}

/-- Scaling every node by a regular element preserves injectivity on every
finite support, even when that element is not a unit. -/
theorem scaled_evaluation_iff [CommRing R] (E : Finset ℕ) (x : ι → R)
    (b : R) (hb : b ∈ nonZeroDivisors R) :
    Function.Injective (evaluationMatrix (fun i => b * x i) E).mulVec ↔
      Function.Injective (evaluationMatrix x E).mulVec := by
  classical
  let d := E.sup id
  have reg (j : ℕ) (v : R) (h : b^j * v = 0) : v = 0 :=
    (mem_nonZeroDivisors_iff_right.mp (pow_mem hb j)) v (by rwa [mul_comm])
  constructor
  · intro h u v huv
    let y (w : E → R) (e : E) := b^(d-e.val) * w e
    have hy (w : E → R) (i : ι) :
        ((evaluationMatrix (fun i => b*x i) E).mulVec (y w)) i =
          b^d * ((evaluationMatrix x E).mulVec w) i := by
      change (∑ e : E, (b*x i)^e.val * (b^(d-e.val) * w e)) =
        b^d * (∑ e : E, (x i)^e.val * w e)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [mul_pow]
      calc
        _ = (b^e.val * b^(d-e.val)) * ((x i)^e.val * w e) := by ring
        _ = _ := by
          have he : e.val ≤ d := Finset.le_sup (f := id) e.property
          rw [← pow_add, Nat.add_sub_of_le he]
    have he : y u = y v := h (funext fun i => by rw [hy, hy, congrFun huv i])
    funext e
    apply sub_eq_zero.mp
    apply reg (d-e.val)
    rw [mul_sub]
    exact sub_eq_zero.mpr (congrFun he e)
  · intro h u v huv
    let y (w : E → R) (e : E) := b^e.val * w e
    have hy (w : E → R) (i : ι) :
        ((evaluationMatrix x E).mulVec (y w)) i =
          ((evaluationMatrix (fun i => b*x i) E).mulVec w) i := by
      change (∑ e : E, (x i)^e.val * (b^e.val * w e)) =
        (∑ e : E, (b*x i)^e.val * w e)
      apply Finset.sum_congr rfl
      intro e _
      rw [mul_pow]
      ac_rfl
    have he : y u = y v := h (funext fun i => by rw [hy, hy, congrFun huv i])
    funext e
    apply sub_eq_zero.mp
    apply reg e.val
    rw [mul_sub]
    exact sub_eq_zero.mpr (congrFun he e)

private theorem int_regular [CommRing R] [IsAddTorsionFree R] {n : ℤ} (hn : n ≠ 0) :
    (n : R) ∈ nonZeroDivisors R := by
  apply mem_nonZeroDivisors_iff_right.mpr
  intro x hx
  apply zsmul_right_injective hn
  simpa [zsmul_eq_mul, mul_comm] using hx

private theorem integer_nodes_nonzero_minor {S : Type*}
    [CommRing S] [Nontrivial S] [IsAddTorsionFree S] (E : Finset ℕ) (n : ι → ℤ) :
    Function.Injective (evaluationMatrix (fun i => (n i : S)) E).mulVec ↔
      ∃ rows : E → ι, ((evaluationMatrix n E).submatrix rows id).det ≠ 0 := by
  classical
  let M := evaluationMatrix n E
  have hmap : M.map (Int.castRingHom S) = evaluationMatrix (fun i => (n i : S)) E := by
    ext i e
    exact map_pow (Int.castRingHom S) (n i) e.val
  rw [← hmap, mulVec_injective_iff_full_minor_annihilator]
  constructor
  · intro h
    by_contra! hz
    have hone := h 1 (fun rows => by
      rw [← map_fullMinor, hz rows, map_zero, mul_zero])
    exact one_ne_zero hone
  · rintro ⟨rows, hm⟩ a ha
    have hz := ha rows
    rw [← map_fullMinor] at hz
    have hr : ((M.submatrix rows id).det : S) ∈ nonZeroDivisors S :=
      int_regular (R := S) hm
    exact (mem_nonZeroDivisors_iff_right.mp hr) a hz

/-- Integer nodes have the same successful supports over the rationals
and over any nonzero integer-torsion-free ring. -/
theorem integer_nodes_iff [CommRing R] [Nontrivial R] [IsAddTorsionFree R]
    (E : Finset ℕ) (n : ι → ℤ) :
    Function.Injective (evaluationMatrix (fun i => (n i : R)) E).mulVec ↔
      Function.Injective (evaluationMatrix (fun i => (n i : ℚ)) E).mulVec :=
  (integer_nodes_nonzero_minor (S := R) E n).trans
    (integer_nodes_nonzero_minor (S := ℚ) E n).symm

def normalizedNode (z : ℚ) (i : ℕ) : ℚ := z + i

def ringPrefix [CommRing R] (a b : R) (m : ℕ) : Fin m → R :=
  progression (fun i : Fin m => i.val) a b

def normalizedPrefix (z : ℚ) (m : ℕ) : Fin m → ℚ :=
  fun i => normalizedNode z i.val

/-- Exact rank transfer at a fixed rational ratio A/B. It covers each
finite exponent set and any list of natural offsets. -/
theorem rational_ratio_support_iff [CommRing R] [Nontrivial R] [IsAddTorsionFree R]
    (offset : ι → ℕ) (E : Finset ℕ) (a b : R) (A : ℤ) (B : ℕ)
    (hB : B ≠ 0) (hb : b ∈ nonZeroDivisors R)
    (hRatio : (B : R)*a = (A : R)*b) :
    Function.Injective (evaluationMatrix (progression offset a b) E).mulVec ↔
      Function.Injective
        (evaluationMatrix (fun i => normalizedNode (A / (B : ℚ)) (offset i)) E).mulVec := by
  let n (i : ι) : ℤ := A + (B : ℤ) * (offset i : ℤ)
  have hBR : (B : R) ∈ nonZeroDivisors R := by
    simpa using (int_regular (R := R) (n := (B : ℤ)) (by exact_mod_cast hB))
  have hBQ : (B : ℚ) ∈ nonZeroDivisors ℚ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast hB)
  have hR (i : ι) : (B : R) * progression offset a b i = b * (n i : R) := by
    simp only [progression, n, Int.cast_add, Int.cast_mul, Int.cast_natCast, mul_add, hRatio]
    ring
  have hQ (i : ι) : (B : ℚ) * normalizedNode (A / (B : ℚ)) (offset i) = (n i : ℚ) := by
    simp only [normalizedNode, n, Int.cast_add, Int.cast_mul, Int.cast_natCast, mul_add]
    congr 1
    rw [mul_comm, div_mul_cancel₀ _ (by exact_mod_cast hB : (B : ℚ) ≠ 0)]
  rw [← scaled_evaluation_iff E (progression offset a b) B hBR,
      ← scaled_evaluation_iff E (fun i => normalizedNode (A / (B : ℚ)) (offset i)) B hBQ]
  simp_rw [hR, hQ]
  rw [scaled_evaluation_iff E _ b hb]
  exact integer_nodes_iff E n

theorem determines_iff_supports [CommRing R] (x : ι → R) (t : ℕ) :
    DeterminesUnboundedSparse x t ↔
      ∀ E : Finset ℕ, E.card ≤ 2*t → Function.Injective (evaluationMatrix x E).mulVec := by
  constructor
  · intro h E hc
    let d := E.sup id
    have he : E ⊆ Finset.range (d+1) :=
      fun e hj => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))
    apply (determinesSparse_iff_support_matrices x d t).mp _ E he hc
    intro f g hf hg hs
    exact h f g hf.2 hg.2 hs
  · intro h f g hf hg he
    let d := max f.natDegree g.natDegree
    have hd := (determinesSparse_iff_support_matrices x d t).mpr (fun E _ hE => h E hE)
    exact hd f g ⟨le_max_left .., hf⟩ ⟨le_max_right .., hg⟩ he

/-- Identifiability itself transfers in both directions, for every prefix. -/
theorem rational_ratio_prefix_iff [CommRing R] [Nontrivial R] [IsAddTorsionFree R]
    (a b : R) (A : ℤ) (B : ℕ) (hB : B ≠ 0) (hb : b ∈ nonZeroDivisors R)
    (hRatio : (B : R)*a = (A : R)*b) (t m : ℕ) :
    DeterminesUnboundedSparse (ringPrefix a b m) t ↔
      DeterminesUnboundedSparse (normalizedPrefix (A / (B : ℚ)) m) t := by
  rw [determines_iff_supports, determines_iff_supports]
  exact forall_congr' fun E => imp_congr_right fun _ =>
    rational_ratio_support_iff (fun i : Fin m => i.val) E a b A B hB hb hRatio

end GrenetRational
