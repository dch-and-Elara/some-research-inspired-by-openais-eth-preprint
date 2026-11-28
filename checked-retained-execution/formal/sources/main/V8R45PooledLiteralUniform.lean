import V8R45PooledLiteralScale

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
set_option maxRecDepth 2400

/-! Uniform form of the manuscript's o(N) conclusion, with any allowed
precision vector at each size. -/
namespace V8R45PooledLiteral
open V8PooledMenu V8PooledMenu.FiveCopy

theorem C4_uniform_vanishing_ratio (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℕ, ∀ (V : Type) [Fintype V], K≤Fintype.card V →
      ∀ P : PublicPrecision V,
        (pooledBits (rootA V) (rootU V) P.prec : ℝ)/(Fintype.card V : ℝ) < ε := by
  obtain ⟨K,hK⟩ := exists_nat_gt (16/ε^2)
  refine ⟨K+1,?_⟩
  intro V _ hN P
  let N := Fintype.card V
  let B := pooledBits (rootA V) (rootU V) P.prec
  have hn : 0 < N := by change K+1≤N at hN; omega
  have hn' : (0:ℝ) < N := by exact_mod_cast hn
  have hK' : 16/ε^2 < (N:ℝ) :=
    hK.trans_le (by exact_mod_cast (by change K+1≤N at hN; omega : K≤N))
  have hm : (16:ℝ)<(N:ℝ)*ε^2 := (div_lt_iff₀ (by positivity : 0<ε^2)).mp hK'
  have hSize : rootSize V ≤ 16*N := by
    change 25*N/2+3 ≤ 16*N
    omega
  have hB2 : (B:ℝ)^2 < (16:ℝ)*(N:ℝ) := by
    have h := (C4_square_strictly_sublinear V P).trans_le hSize
    exact_mod_cast h
  have hx : (16:ℝ)*(N:ℝ) < (ε*(N:ℝ))^2 := by
    have h := mul_lt_mul_of_pos_right hm hn'
    nlinarith
  change (B:ℝ)/(N:ℝ) < ε
  rw [div_lt_iff₀ hn']
  by_contra! hb
  have he : (ε*(N:ℝ))^2 ≤ (B:ℝ)^2 := pow_le_pow_left₀ (by positivity) hb 2
  exact (not_lt_of_ge he) (hB2.trans hx)

#print axioms C4_uniform_vanishing_ratio
end V8R45PooledLiteral