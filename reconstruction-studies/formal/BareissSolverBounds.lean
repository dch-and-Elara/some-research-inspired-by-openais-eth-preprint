import BareissSolverTrace

open scoped BigOperators

namespace Reconstruction.BareissSolver

/-- Uniform magnitude-bit bound on ordered minors of the augmented table. -/
def minorBits (m n b : ℕ) : ℕ := min m (n+1) * (b+min m (n+1)) + 1

/-- Products and the longest partial dot product fit within this operand cap. -/
def traceBits (m n b : ℕ) : ℕ := 2*minorBits m n b+n+3

theorem HasMinor.lt_height {m n b k : ℕ} {Z : IntegerAugment m n} {v : ℤ}
    (he : ∀ i j, (Z i j).natAbs ≤ 2^b) (hk : k ≤ min m (n+1)) (h : HasMinor Z k v) :
    v.natAbs < 2^minorBits m n b := by
  obtain ⟨rs,cs,rfl⟩ := h
  have hh := BareissHeight.minor_lt_pow Z rs cs b he
  rw [Fintype.card_fin] at hh
  exact hh.trans_le (Nat.pow_le_pow_right (by decide) (by unfold minorBits; gcongr))

private theorem natAbs_mul_le {a b : ℤ} {H : ℕ} (ha : a.natAbs ≤ H) (hb : b.natAbs ≤ H) :
    (a*b).natAbs ≤ H*H := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul ha hb

private theorem natAbs_sub_bound (a b : ℤ) : (a-b).natAbs ≤ a.natAbs+b.natAbs := by
  simpa only [sub_eq_add_neg, Int.natAbs_neg] using Int.natAbs_add_le a (-b)

private theorem height_le_square {H : ℕ} (h : 1 ≤ H) : H ≤ H*H := by
  simpa using Nat.mul_le_mul_left H h

private theorem forwardTrace_bounds {m n H C : ℕ} {M : IntegerAugment (m+1) (n+1)} {d : ℤ}
    {i : Fin (m+1)} {j : Fin (n+1)} (hH : 1 ≤ H) (hC : 2*(H*H) ≤ C)
    (hM : ∀ u v, (M u v).natAbs ≤ H) (hd : d.natAbs ≤ H) (hd0 : d ≠ 0)
    (hexact : ∀ u v, d ∣ forwardDividend M i j u v) :
    ∀ op ∈ forwardTrace M d i j, op.Within C ∧ op.DivisionExact := by
  intro op hop
  obtain ⟨u,_,hu⟩ := List.mem_flatMap.mp hop
  obtain ⟨v,_,hv⟩ := List.mem_flatMap.mp hu
  have hHC : H ≤ C := (height_le_square hH).trans (by omega)
  have hp := (hM i (some j)).trans hHC
  have ha := (hM (i.succAbove u) (v.map j.succAbove)).trans hHC
  have hc := (hM (i.succAbove u) (some j)).trans hHC
  have hr := (hM i (v.map j.succAbove)).trans hHC
  have hl := natAbs_mul_le (hM i (some j)) (hM (i.succAbove u) (v.map j.succAbove))
  have hright := natAbs_mul_le (hM (i.succAbove u) (some j)) (hM i (v.map j.succAbove))
  have hdiv : (forwardDividend M i j u v).natAbs ≤ C := by
    unfold forwardDividend
    exact (natAbs_sub_bound _ _).trans (by omega)
  simp only [forwardCellTrace, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · simp [ScalarOp.Within, ScalarOp.operands, ScalarOp.DivisionExact, hp, ha]
  · simp [ScalarOp.Within, ScalarOp.operands, ScalarOp.DivisionExact, hc, hr]
  · have h1 := hl.trans (show H*H ≤ C by omega)
    have h2 := hright.trans (show H*H ≤ C by omega)
    simp [ScalarOp.Within, ScalarOp.operands, ScalarOp.DivisionExact, h1, h2]
  · simp [ScalarOp.Within, ScalarOp.operands, ScalarOp.DivisionExact, hdiv, hd.trans hHC, hd0, hexact]

private theorem dotTrace_bounds {l : List (ℤ × ℤ)} {H C : ℕ} {acc : ℤ}
    (hsmall : ∀ p ∈ l, p.1.natAbs ≤ H ∧ p.2.natAbs ≤ H) (hH : H ≤ H*H)
    (hC : H*H ≤ C) (hacc : acc.natAbs+l.length*(H*H) ≤ C) :
    ∀ op ∈ dotTrace acc l, op.Within C ∧ op.DivisionExact := by
  induction l generalizing acc with
  | nil => simp [dotTrace]
  | cons p l ih =>
    obtain ⟨a,b⟩ := p
    intro op hop
    have hpair := hsmall (a,b) (by simp)
    have hp := natAbs_mul_le hpair.1 hpair.2
    simp only [List.length_cons, Nat.add_mul, one_mul] at hacc
    simp only [dotTrace, List.mem_cons] at hop
    rcases hop with rfl | rfl | hop
    · simp [ScalarOp.Within, ScalarOp.operands, ScalarOp.DivisionExact,
        hpair.1.trans (hH.trans hC), hpair.2.trans (hH.trans hC)]
    · simp [ScalarOp.Within, ScalarOp.operands, ScalarOp.DivisionExact,
        (show acc.natAbs ≤ C by omega), hp.trans hC]
    · apply ih (fun p hp => hsmall p (List.mem_cons_of_mem _ hp)) _ op hop
      have hz := (Int.natAbs_add_le acc (a*b)).trans (Nat.add_le_add_left hp acc.natAbs)
      omega

private theorem dotValue_bound {l : List (ℤ × ℤ)} {H : ℕ} {acc : ℤ}
    (hsmall : ∀ p ∈ l, p.1.natAbs ≤ H ∧ p.2.natAbs ≤ H) :
    (l.foldl (fun s p => s+p.1*p.2) acc).natAbs ≤ acc.natAbs+l.length*(H*H) := by
  induction l generalizing acc with
  | nil => simp
  | cons p l ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.add_mul, one_mul]
    have hp := hsmall p (by simp)
    have hh := ih (acc := acc + p.1*p.2) (fun q hq => hsmall q (List.mem_cons_of_mem p hq))
    have hz := (Int.natAbs_add_le acc (p.1*p.2)).trans (Nat.add_le_add_left (natAbs_mul_le hp.1 hp.2) acc.natAbs)
    omega

private theorem backwardTrace_bounds {m n H C : ℕ} {M : IntegerAugment (m+1) (n+1)}
    {i : Fin (m+1)} {j : Fin (n+1)} {s : ScaledSolution n}
    (hH : 1 ≤ H) (hC : (n+1)*(H*H) ≤ C) (hM : ∀ u v, (M u v).natAbs ≤ H)
    (hD : s.denominator.natAbs ≤ H) (hs : ∀ j, (s.numerator j).natAbs ≤ H)
    (hp : M i (some j) ≠ 0) (hexact : M i (some j) ∣ backwardDividend M i j s) :
    ∀ op ∈ backwardTrace M i j s, op.Within C ∧ op.DivisionExact := by
  let ys := (List.finRange n).map fun v => (M i (some (j.succAbove v)),s.numerator v)
  let S := (List.finRange n).foldl (fun acc v => acc+M i (some (j.succAbove v))*s.numerator v) 0
  have hy (p : ℤ × ℤ) (hp' : p ∈ ys) : p.1.natAbs ≤ H ∧ p.2.natAbs ≤ H := by
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hp'
    exact ⟨hM ..,hs v⟩
  have hlen : ys.length = n := by simp [ys]
  have hS : S.natAbs ≤ n*(H*H) := by
    have hh := dotValue_bound (acc := 0) hy
    simpa only [ys, List.foldl_map, Function.comp_apply, hlen, Int.natAbs_zero, zero_add, List.length_map,
      List.length_finRange] using hh
  have hP := natAbs_mul_le hD (hM i none)
  have hQ : H*H ≤ C := by rw [Nat.add_mul, one_mul] at hC; omega
  have hBase : H ≤ C := (height_le_square hH).trans hQ
  have hdiv : (backwardDividend M i j s).natAbs ≤ C := by
    change (s.denominator*M i none-S).natAbs ≤ C
    rw [Nat.add_mul, one_mul] at hC
    exact (natAbs_sub_bound _ _).trans (by omega)
  intro op hop
  change op ∈ (.mul s.denominator (M i none) :: dotTrace 0 ys) ++
    [.sub (s.denominator*M i none) S,.exactDiv (backwardDividend M i j s) (M i (some j))] at hop
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | hd | rfl | rfl
  · simp [ScalarOp.Within, ScalarOp.operands, ScalarOp.DivisionExact, hD.trans hBase, (hM i none).trans hBase]
  · apply dotTrace_bounds hy (height_le_square hH) hQ _ op hd
    rw [hlen, Int.natAbs_zero, zero_add]
    rw [Nat.add_mul, one_mul] at hC
    omega
  · have hSC : S.natAbs ≤ C := by rw [Nat.add_mul, one_mul] at hC; omega
    simp [ScalarOp.Within, ScalarOp.operands, ScalarOp.DivisionExact, hP.trans hQ, hSC]
  · simp [ScalarOp.Within, ScalarOp.operands, ScalarOp.DivisionExact, hdiv, (hM i (some j)).trans hBase, hp, hexact]

private theorem trace_cap (m n b : ℕ) :
    (n+2)*(2^minorBits m n b * 2^minorBits m n b) ≤ 2^traceBits m n b := by
  have hn : n+2 ≤ (2:ℕ)^(n+3) := Nat.succ_le_of_lt ((Nat.lt_two_pow_self (n := n+1)).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega)))
  calc
    _ ≤ 2^(n+3)*(2^minorBits m n b * 2^minorBits m n b) := Nat.mul_le_mul_right _ hn
    _ = _ := by rw [← pow_add, ← pow_add]; unfold traceBits; congr 1; omega

private theorem table_height {m₀ n₀ m n depth b₀ : ℕ} {Z : IntegerAugment m₀ n₀} {d : ℤ}
    {A : Coefficients m n} {b : Column m} {M : IntegerAugment m n}
    (F : MinorFrame Z depth d A b) (E : Represents M d A b)
    (hm : depth+m = m₀) (hn : depth+n = n₀) (he : ∀ i j, (Z i j).natAbs ≤ 2^b₀) :
    d.natAbs < 2^minorBits m₀ n₀ b₀ ∧ ∀ i j, (M i j).natAbs < 2^minorBits m₀ n₀ b₀ := by
  refine ⟨HasMinor.lt_height he (le_min (by omega) (by omega)) F.denominator_minor, ?_⟩
  intro i j
  obtain ⟨v,hv,hval⟩ := F.entry i j
  have hi := i.isLt
  have heq : v = M i j := by exact_mod_cast hval.trans (E i j).symm
  exact heq ▸ HasMinor.lt_height he (le_min (by omega) (by omega)) hv

private theorem solve_height {m₀ n₀ m n depth b₀ : ℕ} {Z : IntegerAugment m₀ n₀} {d : ℤ}
    {A : Coefficients m n} {b : Column m} {s : ScaledSolution n}
    (F : MinorFrame Z depth d A b) (V : ValidResult Z depth d A b s)
    (hm : depth+m = m₀) (hn : depth+n = n₀) (he : ∀ i j, (Z i j).natAbs ≤ 2^b₀) :
    s.denominator.natAbs < 2^minorBits m₀ n₀ b₀ ∧
      ∀ j, (s.numerator j).natAbs < 2^minorBits m₀ n₀ b₀ := by
  obtain ⟨k,hk,hD,hN⟩ := V.minors F
  have hsize : depth+k ≤ min m₀ (n₀+1) := by
    have hk₁ := hk.trans (min_le_left m n)
    have hk₂ := hk.trans (min_le_right m n)
    exact le_min (by omega) (by omega)
  refine ⟨HasMinor.lt_height he hsize hD, fun j => ?_⟩
  rcases hN j with hj | hj
  · rw [hj, Int.natAbs_zero]
    positivity
  · exact HasMinor.lt_height he hsize hj

private theorem zeroTrace_bounds {m n C : ℕ} {M : IntegerAugment m n}
    (h : ∀ i j, (M i j).natAbs ≤ C) : ∀ op ∈ zeroTrace M, op.Within C ∧ op.DivisionExact := by
  intro op hop
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hop
  simp [ScalarOp.Within, ScalarOp.operands, ScalarOp.DivisionExact, h]

private theorem pivotTrace_bounds {m n C : ℕ} {M : IntegerAugment m n}
    (h : ∀ i j, (M i j).natAbs ≤ C) : ∀ op ∈ pivotTrace M, op.Within C ∧ op.DivisionExact := by
  intro op hop
  obtain ⟨ij, _, rfl⟩ := List.mem_map.mp hop
  simp [ScalarOp.Within, ScalarOp.operands, ScalarOp.DivisionExact, h]

private theorem arithmeticTrace_bounds {m₀ n₀ b₀ : ℕ} {Z : IntegerAugment m₀ n₀}
    (he : ∀ i j, (Z i j).natAbs ≤ 2^b₀) (m n depth : ℕ) (d : ℤ)
    (A : Coefficients m n) (b : Column m) (M : IntegerAugment m n)
    (F : MinorFrame Z depth d A b) (E : Represents M d A b)
    (hm : depth+m = m₀) (hn : depth+n = n₀) :
    ∀ op ∈ arithmeticTrace m n M d, op.Within (2^traceBits m₀ n₀ b₀) ∧ op.DivisionExact := by
  let H : ℕ := 2^minorBits m₀ n₀ b₀
  let C : ℕ := 2^traceBits m₀ n₀ b₀
  have hH : 1 ≤ H := Nat.succ_le_of_lt (pow_pos (by decide) _)
  have hC : (n₀+2)*(H*H) ≤ C := trace_cap m₀ n₀ b₀
  have hC₂ : 2*(H*H) ≤ C := (Nat.mul_le_mul_right _ (by omega : 2 ≤ n₀+2)).trans hC
  have hHC : H ≤ C := (height_le_square hH).trans (by omega)
  induction m generalizing n depth d with
  | zero => simp [arithmeticTrace]
  | succ m ih =>
    obtain ⟨hd,hM⟩ := table_height F E hm hn he
    have hMC (i j) : (M i j).natAbs ≤ C := (hM i j).le.trans hHC
    intro op hop
    cases n with
    | zero => exact zeroTrace_bounds hMC op hop
    | succ n =>
      have hop' : op ∈ pivotTrace M ∨ op ∈ (match integerPivot M with
          | none => zeroTrace M
          | some (i,j) =>
            let M' := forwardStep M d i j
            let p := M i (some j)
            let sub := runInt m n M' p
            forwardTrace M d i j ++ arithmeticTrace m n M' p ++
              sub.result.toList.flatMap (fun x => backwardTrace M i j x)) :=
        List.mem_append.mp hop
      rcases hop' with hop' | hop'
      · exact pivotTrace_bounds hMC op hop'
      cases hp : integerPivot M with
      | none => exact zeroTrace_bounds hMC op (by simpa only [hp] using hop')
      | some p =>
        obtain ⟨i,j⟩ := p
        let M' := forwardStep M d i j
        let p := M i (some j)
        have hp' := (integerPivot_eq F.denominator_ne E).symm.trans hp
        have ha := firstPivot_ne_zero hp'
        obtain ⟨F', E', hx⟩ := forwardStep_spec F E ha
        have hm' : depth+1+m = m₀ := by omega
        have hn' : depth+1+n = n₀ := by omega
        have hop'' : op ∈ forwardTrace M d i j ++ arithmeticTrace m n M' p ++
            (runInt m n M' p).result.toList.flatMap (fun x => backwardTrace M i j x) := by
          simpa only [hp] using hop'
        rcases List.mem_append.mp hop'' with hr | hb
        · rcases List.mem_append.mp hr with hf | hc
          · exact forwardTrace_bounds hH hC₂ (fun u v => (hM u v).le) hd.le F.denominator_ne
              (fun u v => (hx u v).1) op hf
          · exact ih n (depth+1) p _ _ M' F' E' hm' hn' op hc
        obtain ⟨s, hs, hbs⟩ := List.mem_flatMap.mp hb
        have hsr : (runInt m n M' p).result = some s := by simpa using hs
        have hv := (runInt_correct m n (depth+1) p _ _ M' F' E').2 s hsr
        have hex := (backwardStep_spec F E ha hv).1
        obtain ⟨hD, hN⟩ := solve_height F' hv hm' hn' he
        have hbC : (n+1)*(H*H) ≤ C := (Nat.mul_le_mul_right _ (by omega : n+1 ≤ n₀+2)).trans hC
        exact backwardTrace_bounds hH hbC (fun u v => (hM u v).le) hD.le (fun j => (hN j).le)
          F'.denominator_ne hex op hbs

/-- Every scalar operand of the charged run has polynomial bit size. Every
division in the trace is by a nonzero divisor with zero remainder. -/
theorem solveInt_trace_height {m n b : ℕ} (Z : IntegerAugment m n)
    (he : ∀ i j, (Z i j).natAbs ≤ 2^b) :
    ∀ op ∈ solveIntTrace Z, op.Within (2^traceBits m n b) ∧ op.DivisionExact :=
  arithmeticTrace_bounds he m n 0 1 _ _ _ (MinorFrame.initial Z) (represents_initial Z) (zero_add _) (zero_add _)

theorem solveInt_output_height {m n b : ℕ} (Z : IntegerAugment m n)
    (he : ∀ i j, (Z i j).natAbs ≤ 2^b) {s : ScaledSolution n}
    (hs : (solveIntScaled Z).result = some s) :
    s.denominator.natAbs < 2^minorBits m n b ∧ ∀ j, (s.numerator j).natAbs < 2^minorBits m n b := by
  have hv := (runInt_correct m n 0 1 (integerCoefficients Z) (integerRhs Z) (denseAugment Z)
    (MinorFrame.initial Z) (represents_initial Z)).2 s hs
  exact solve_height (MinorFrame.initial Z) hv (zero_add _) (zero_add _) he

/-- The bound for rational inputs includes the RHS denominator of each row. -/
theorem clear_entry_height {m n B : ℕ} (A : Coefficients m n) (b : Column m)
    (hA : ∀ i j, BareissHeight.RatHeight B (A i j))
    (hb : ∀ i, BareissHeight.RatHeight B (b i)) :
    ∀ i j, (clear A b i j).natAbs ≤ 2^(B*(n+1)) := by
  have h (i : Fin m) (j : Option (Fin n)) :
      BareissHeight.RatHeight B (BareissHeight.augment A b i j) := by
    cases j with
    | none => exact hb i
    | some j => exact hA i j
  intro i j
  simpa using BareissHeight.clearRows_natAbs_le (BareissHeight.augment A b) B h i j

theorem solve_trace_height {m n B : ℕ} (A : Coefficients m n) (b : Column m)
    (hA : ∀ i j, BareissHeight.RatHeight B (A i j))
    (hb : ∀ i, BareissHeight.RatHeight B (b i)) :
    ∀ op ∈ solveIntTrace (clear A b), op.Within (2^traceBits m n (B*(n+1))) ∧ op.DivisionExact :=
  solveInt_trace_height _ (clear_entry_height A b hA hb)

end Reconstruction.BareissSolver
