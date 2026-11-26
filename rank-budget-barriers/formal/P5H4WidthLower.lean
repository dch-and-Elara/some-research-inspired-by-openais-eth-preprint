import RBLocalProfile

/-! The lower half of the exact H4 inner-rank assertion. It argues with
literal quotient factors, whose entries lift individually; unit cancellation
happens only over the polynomial domain or its field of fractions. -/
namespace P5H4
open Polynomial Matrix
open scoped Classical BigOperators

variable {K n r : Type*} [Field K] [Fintype n] [DecidableEq n] [Fintype r]

/-- Stated polynomial representative form of a genuine factorization in
the indicated quotient. The lifting equivalence is proved below. -/
def Factors (q : K[X]) (P : Matrix n n K[X]) (r : Type*) [Fintype r] : Prop :=
  ∃ (A : Matrix n r K[X]) (B : Matrix r n K[X]) (E : Matrix n n K[X]),
    P = q • E + A * B

omit [Fintype n] [DecidableEq n] in
theorem factors_iff_quotient (q : K[X]) (P : Matrix n n K[X]) :
    Factors q P r ↔ ∃ U : Matrix n r (AdjoinRoot q), ∃ V : Matrix r n (AdjoinRoot q),
      P.map (AdjoinRoot.mk q) = U * V := by
  constructor
  · rintro ⟨A,B,E,h⟩
    refine ⟨A.map (AdjoinRoot.mk q), B.map (AdjoinRoot.mk q),?_⟩
    rw [← Matrix.map_mul, h]
    ext i j
    change AdjoinRoot.mk q (q * E i j + (A*B) i j) = _
    rw [map_add, map_mul, AdjoinRoot.mk_eq_zero.mpr (dvd_refl q), zero_mul, zero_add]
    rfl
  · rintro ⟨U,V,h⟩
    choose a ha using fun i j => AdjoinRoot.mk_surjective (U i j)
    choose b hb using fun i j => AdjoinRoot.mk_surjective (V i j)
    let A : Matrix n r K[X] := Matrix.of a
    let B : Matrix r n K[X] := Matrix.of b
    have hA : A.map (AdjoinRoot.mk q) = U := Matrix.ext ha
    have hB : B.map (AdjoinRoot.mk q) = V := Matrix.ext hb
    have hAB : (A*B).map (AdjoinRoot.mk q) = U*V := by
      rw [Matrix.map_mul,hA,hB]
    have hd (i j : n) : q ∣ P i j-(A*B) i j := by
      apply AdjoinRoot.mk_eq_zero.mp
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun M : Matrix n n (AdjoinRoot q) => M i j) (h.trans hAB.symm)
    choose e he using hd
    refine ⟨A,B,Matrix.of e, Matrix.ext fun i j => ?_⟩
    change P i j = q * e i j + (A*B) i j
    linear_combination he i j

/-- Strip exactly the true root order; the remaining diagonal entry is
a unit at the sampled center. -/
theorem cofactor_at_root {p : K[X]} (hp : p ≠ 0) (t : K) :
    ∃ b : K[X], p = (X-C t)^rootMultiplicity t p * b ∧ b.eval t ≠ 0 := by
  obtain ⟨b,hb⟩ := pow_rootMultiplicity_dvd p t
  have hbn : b ≠ 0 := by
    intro hn
    exact hp (by simpa [hn] using hb)
  have hsum : rootMultiplicity t p = rootMultiplicity t p + rootMultiplicity t b := by
    calc
      _ = rootMultiplicity t ((X-C t)^rootMultiplicity t p * b) := congrArg _ hb
      _ = _ := by
        rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero t)) hbn),
          rootMultiplicity_X_sub_C_pow]
  have hz : rootMultiplicity t b = 0 := by omega
  refine ⟨b,hb,?_⟩
  intro hc
  have hpos := (rootMultiplicity_pos hbn).2 (show IsRoot b t from hc)
  omega

private theorem card_le_of_det_mul_ne_zero (A : Matrix n r K[X]) (B : Matrix r n K[X])
    (hab : (A*B).det ≠ 0) : Fintype.card n ≤ Fintype.card r := by
  let φ : K[X] →+* FractionRing K[X] := algebraMap ..
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hn : ((A*B).map φ).det ≠ 0 := by
    change (φ.mapMatrix (A*B)).det ≠ 0
    rw [← RingHom.map_det]
    exact fun h => hab (hφ (h.trans (map_zero φ).symm))
  obtain ⟨u,hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hn.isUnit
  have hc : ((A*B).map φ).rank = Fintype.card n := hu ▸ Matrix.rank_unit u
  rw [Matrix.map_mul] at hc
  rw [← hc]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

set_option maxHeartbeats 3500000 in
/-- Every quotient factorization has at least one channel per surviving
diagonal, even when all these entries vanish at the residue point. -/
theorem diagonal_width_lower (a : n → K[X]) (ha : ∀ i, a i ≠ 0) (t : K) (k : ℕ)
    (h : Factors ((X-C t)^k) (diagonal a) r) :
    Fintype.card {i : n // rootMultiplicity t (a i) < k} ≤ Fintype.card r := by
  obtain ⟨A,B,E,he⟩ := h
  let z : K[X] := X-C t
  let e : n → ℕ := fun i => rootMultiplicity t (a i)
  let I := {i : n // e i < k}
  choose b hb hb' using fun i => cofactor_at_root (ha i) t
  let A' : Matrix I r K[X] := A.submatrix Subtype.val id
  let B' : Matrix r I K[X] := B.submatrix id Subtype.val
  let R : Matrix I I K[X] := Matrix.of fun i j =>
    (if i = j then b i.1 else 0) - z^(k-e i.1) * E i.1 j.1
  let D : Matrix I I K[X] := diagonal (fun i => z^e i.1)
  have hmul (i j : I) : (A'*B') i j = (A*B) i.1 j.1 := by
    rfl
  have hnorm : D * R = A'*B' := Matrix.ext fun i j => by
    have h₀ := congrArg (fun M : Matrix n n K[X] => M i.1 j.1) he
    change (diagonal a) i.1 j.1 = z^k * E i.1 j.1 + (A*B) i.1 j.1 at h₀
    rw [hmul, Matrix.diagonal_mul]
    change z^e i.1 * ((if i=j then b i.1 else 0) - z^(k-e i.1) * E i.1 j.1) = _
    rw [mul_sub, ← mul_assoc, ← pow_add, Nat.add_sub_of_le i.property.le]
    by_cases hij : i=j
    · subst j
      have ha0 : z^e i.1 * b i.1 = a i.1 := (hb i.1).symm
      rw [if_pos rfl,ha0]
      rw [Matrix.diagonal_apply_eq] at h₀
      linear_combination h₀
    · have hin : i.1 ≠ j.1 := fun hx => hij (Subtype.ext hx)
      rw [Matrix.diagonal_apply_ne _ hin] at h₀
      rw [if_neg hij, mul_zero]
      linear_combination h₀
  have hRmat : R.map (evalRingHom t) = diagonal (fun i => (b i.1).eval t) := by
    ext i j
    have hpos : 0 < k-e i.1 := Nat.sub_pos_of_lt i.property
    change eval t ((if i=j then b i.1 else 0) - z^(k-e i.1) * E i.1 j.1) = _
    rw [eval_sub, eval_mul, eval_pow]
    have hz : eval t z = 0 := by simp [z]
    rw [hz, zero_pow hpos.ne', zero_mul, sub_zero]
    by_cases hij : i=j
    · subst j
      simp
    · simp [hij]
  have hR : R.det ≠ 0 := by
    intro hel
    have hn : (R.map (evalRingHom t)).det ≠ 0 := by
      rw [hRmat, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hb' i.1)
    apply hn
    change ((evalRingHom t).mapMatrix R).det = 0
    rw [← RingHom.map_det,hel,map_zero]
  have hD : D.det ≠ 0 := by
    change (diagonal (fun i : I => z^e i.1)).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => pow_ne_zero _ (X_sub_C_ne_zero t))
  apply card_le_of_det_mul_ne_zero A' B'
  rw [← hnorm,Matrix.det_mul]
  exact mul_ne_zero hD hR

#print axioms factors_iff_quotient
#print axioms cofactor_at_root
#print axioms diagonal_width_lower
end P5H4
