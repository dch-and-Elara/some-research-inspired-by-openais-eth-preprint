import A4R45FullCell
import A4R45PrintedLoad
import J9PrintedSchedule

/-! The padded sparse formula, not a dummy source size parameter, gives
the printed root logarithm and an active root. -/
namespace A4R45SourceSchedule
open A4R45LiteralNetwork A4R45FullCell A4R45PrintedLoad
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

variable {V₂ V₃ : Type*} [Fintype V₂] [Fintype V₃]
variable {U : Type*} [Fintype U]

noncomputable def sourceSize (V₂ V₃ U : Type*) [Fintype V₂] [Fintype V₃] [Fintype U] : ℕ :=
  Fintype.card (Var V₂ V₃ U)+(formula (V₂:=V₂) (V₃:=V₃) (U:=U)).length

theorem padded_formula_increments {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (diag : Cell) (half core : ℕ) :
    sourceSize V₂ V₃ (U ⊕ Filler diag half core) =
      sourceSize V₂ V₃ U+2*Fintype.card (Filler diag half core) := by
  unfold sourceSize
  rw [formula_clause_count,formula_clause_count,
    Fintype.card_congr (paddedVars diag half core)]
  simp only [Fintype.card_sum]
  omega

theorem literal_formula_sets_printed_scale {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (diag : Cell) (half core : ℕ) {m : ℕ}
    (wired : Fintype.card (Wire V₂ V₃ U)=m)
    (small : sourceSize V₂ V₃ U≤m)
    (filled : Fintype.card (Wire V₂ V₃ (U ⊕ Filler diag half core))=wireCount (scale m)) :
    sourceSize V₂ V₃ (U ⊕ Filler diag half core) = wireCount (scale m) -
        (m-sourceSize V₂ V₃ U) ∧
      Nat.clog 2 (sourceSize V₂ V₃ (U ⊕ Filler diag half core))=scale m := by
  have h := padded_formula_increments (U:=U) (V₂:=V₂) (V₃:=V₃) diag half core
  rw [Fintype.card_prod,Fintype.card_bool,
      Fintype.card_congr (paddedVars diag half core),Fintype.card_sum] at filled
  rw [Fintype.card_prod,Fintype.card_bool] at wired
  have s := (printed_square_growth m).1
  have hsize : sourceSize V₂ V₃ (U ⊕ Filler diag half core) = wireCount (scale m) -
      (m-sourceSize V₂ V₃ U) := by omega
  refine ⟨hsize,?_⟩
  rw [hsize]
  exact padded_clog_unchanged m _ (Nat.sub_le _ _)

theorem genuine_root_is_active (s M ell : ℕ) (hs : s≤M) (hm : 2≤M) (he : 4≤ell) :
    J9PrintedSchedule.leafThreshold s ell < M := by
  have roots : 2≤ell.sqrt := Nat.le_sqrt.mpr (by omega)
  have h₁ : ell.sqrt≤2*(ell.sqrt-1) := by omega
  have h₂ := h₁.trans (Nat.mul_le_mul_right (ell.sqrt-1) hm)
  have h₃ : M+ell.sqrt≤M*ell.sqrt := by
    calc
      _ ≤ M+M*(ell.sqrt-1) := Nat.add_le_add_left h₂ _
      _ = M*(1+(ell.sqrt-1)) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.add_sub_of_le (by omega : 1≤ell.sqrt)]
  unfold J9PrintedSchedule.leafThreshold
  apply (Nat.div_lt_iff_lt_mul (by omega : 0<ell.sqrt)).2
  omega

theorem literal_printed_coordinates {s m : ℕ}
    (same : Nat.clog 2 s=scale m) :
    J9PrintedSchedule.rootA (Nat.clog 2 s)=A4R45PrintedLoad.bits (scale m) 131072 ∧
      J9PrintedSchedule.rootL (Nat.clog 2 s)=2^(A4R45PrintedLoad.bits (scale m) 131072) := by
  rw [same]
  exact ⟨rfl,rfl⟩

theorem actual_p_cap (p₀ h D M a : ℕ) (nonempty : 0<M) :
    2*M < J9PrintedSchedule.precision p₀ h D M a := by
  have lo : 8*M≤8*M*(a+1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold J9PrintedSchedule.precision
  omega

#print axioms padded_formula_increments
#print axioms literal_formula_sets_printed_scale
#print axioms genuine_root_is_active
#print axioms literal_printed_coordinates
#print axioms actual_p_cap
end A4R45SourceSchedule
