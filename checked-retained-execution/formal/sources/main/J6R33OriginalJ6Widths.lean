import J6R33OriginalJ6Sizes

/-! Bound every public root bit width by a fixed polynomial in the
explicit enlargement M and the literal wire count m. No evaluator
of a completed slot contributes to these bounds. -/
namespace J6R33OriginalJ6
open scoped Polynomial
open J6Mesh J6R28GeneratedRootFrame J6R24LegalLayout J6R22RootReadout
set_option maxHeartbeats 5000000

theorem source_clog_coarse (m : ℕ) : b m≤m+2 := by
  have all : ∀ n : ℕ,n≤(2:ℕ)^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have p : 0<(2:ℕ)^n := by positivity
      rw [pow_succ]
      omega
  exact (Nat.clog_le_iff_le_pow (by decide)).mpr (all (m+2))

theorem root_bits_small (m native : ℕ) (good : native≤m) :
    a m≤8*(m+2) ∧ u m≤4*(m+2) ∧
    printedFieldWidth m native≤2097152*(m+2) ∧
    printedRankWidth m≤524296*(m+2)+1 ∧
    literalPadCount m≤M m := by
  have hb := source_clog_coarse m
  have ha : a m≤8*(m+2) := Nat.mul_le_mul_left _ hb
  have hu : u m≤4*(m+2) := Nat.mul_le_mul_left _ hb
  have he : printedFieldWidth m native=2097152*b m := by
    unfold printedFieldWidth
    rw [(physicalSize_ceiling _ _ good).2.2,lambda,←mul_assoc]
    rfl
  have hk := (cell_pair_loop_is_source_polynomial m).2.2.2.1
  have wc : Nat.clog 2 (K m) ≤ lambda m :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr hk
  have k : printedRankWidth m ≤ 524296*(m+2)+1 := by
    unfold printedRankWidth
    have s : a m+lambda m = 524296*b m := by
      unfold a lambda
      ring
    calc
      _ ≤ a m+lambda m+1 := Nat.add_le_add_right (Nat.add_le_add_left wc _) _
      _ = 524296*b m+1 := congrArg (·+1) s
      _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ hb) _
  have c := literal_pad_count_source m
  have h : M m-m*L m≤M m := Nat.sub_le _ _
  exact ⟨ha,hu,he ▸ Nat.mul_le_mul_left _ hb,k,by omega⟩

def precisionEnvelope (m base : ℕ) : ℕ :=
  base+8*(3*M m+4*(m+2))*M m+8*M m*(8*(m+2)+1)

theorem actual_root_precision_poly (m base : ℕ) :
    J6SourcePrecision.printed m base≤precisionEnvelope m base := by
  have Z := root_bits_small m 0 (Nat.zero_le m)
  have L0 := (cell_pair_loop_is_source_polynomial m).2.2.2.2
  have div0 : J6SourcePrecision.h m≤3*M m+4*(m+2) := by
    unfold J6SourcePrecision.h
    exact (Nat.div_le_self _ _).trans
      ((Nat.sub_le _ _).trans (Nat.add_le_add_left Z.2.1 _))
  unfold J6SourcePrecision.printed precisionEnvelope
  gcongr
  exact Z.1

def meshWordEnvelope (m : ℕ) : ℕ := (2*m+1)*(8*(m+2)+1)

theorem root_readout_widths_poly (m q base : ℕ) :
    printedFactorWidth m q≤
      meshWordEnvelope m*((2*m+1)*m)+q*(2*m+1)+(2*meshWordEnvelope m+3)*M m+2 ∧
    printedAnswerWidth m base≤
      (precisionEnvelope m base+meshWordEnvelope m*m+(2*meshWordEnvelope m+1)*m+1)*(m+1)+3 := by
  have Z := root_bits_small m 0 (Nat.zero_le m)
  have H : outerMeshWidth m≤meshWordEnvelope m := by
    unfold outerMeshWidth meshWordEnvelope
    gcongr
    exact Z.1
  have P := actual_root_precision_poly m base
  have C := Z.2.2.2.2
  constructor
  · unfold printedFactorWidth publicFactorWidth
    gcongr
  · unfold printedAnswerWidth baseTermWidth
    gcongr

#print axioms source_clog_coarse
#print axioms root_bits_small
#print axioms actual_root_precision_poly
#print axioms root_readout_widths_poly
end J6R33OriginalJ6
