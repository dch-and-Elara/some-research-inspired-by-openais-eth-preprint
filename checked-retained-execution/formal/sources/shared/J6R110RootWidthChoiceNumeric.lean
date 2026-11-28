import J6R52FreshExteriorWordsMenu
import J6R49CostDimensions

/-! Choose the genuine R54 root register widths from the printed mesh.
The numeric code is small by the selection formula, not by virtue of
its storage word. No previously issued native/ancestor slot is changed. -/
namespace J6R110RootWidthChoice
open J6Mesh J6R52FreshExterior J6R49Cost
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 9000000

def chosenQ (m : ℕ) : ℕ := 2*lambda m+6
def chosenPrec (m : ℕ) : ℕ := chosenQ m
def chosenCode (m : ℕ) : ℕ := expandedCodeWidth m (chosenQ m)
def chosenBW (m : ℕ) : ℕ := chosenCode m

theorem code_is_explicit (m : ℕ) : chosenCode m=3*lambda m+7 := by
  unfold chosenCode expandedCodeWidth chosenQ
  omega

theorem chosen_widths_are_on_true_source_mesh (m native : ℕ) (nativeFit : native≤m) :
    let s := physicalSize m native
    chosenQ m=2*Nat.clog 2 s+6 ∧ chosenPrec m=2*Nat.clog 2 s+6 ∧
      chosenCode m=3*Nat.clog 2 s+7 ∧ chosenBW m=3*Nat.clog 2 s+7 := by
  have h := (physicalSize_ceiling m native nativeFit).2.2
  dsimp only
  rw [h]
  exact ⟨rfl,rfl,code_is_explicit m,code_is_explicit m⟩

theorem chosen_q_above_one (m : ℕ) : 1<chosenQ m := by
  unfold chosenQ
  omega

theorem chosen_bw_positive (m : ℕ) : 0<chosenBW m := by
  change 0<chosenCode m
  rw [code_is_explicit]
  omega

theorem chosen_code_fits_storage (m : ℕ) : chosenCode m<2^chosenBW m :=
  Nat.lt_pow_self (by decide)

theorem true_copy_count_below_mesh (m : ℕ) : K m≤M m := by
  unfold K M lambda
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem true_printed_roster_code_fits_expanded_code (m base q : ℕ)
    (atLeastOne : 1≤q) (printedFit : J6SourcePrecision.printed m base<2^q) :
    rootCodeWidth m base≤expandedCodeWidth m q := by
  unfold rootCodeWidth expandedCodeWidth
  apply (Nat.clog_le_iff_le_pow (show 1<(2:ℕ) by decide)).2
  have prod : M m*(J6SourcePrecision.printed m base-1)≤(2:ℕ)^(lambda m+q) := by
    rw [pow_add,←show M m=2^lambda m from rfl]
    exact Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans printedFit.le)
  have twice : 2≤(2:ℕ)^(lambda m+q) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0<(2:ℕ) by decide)
      (show 1≤lambda m+q by omega)
  rw [pow_succ]
  omega

theorem chosen_precision_width_never_truncates (m native base : ℕ) (nativeFit : native≤m)
    (baseFit : base≤(physicalSize m native)^2) :
    let p := J6SourcePrecision.printed m base
    base<2^chosenQ m ∧ K m<2^chosenQ m ∧ p<2^chosenQ m ∧ p<2^chosenPrec m ∧
      rootCodeWidth m base≤chosenCode m := by
  have ms : physicalSize m native≤M m := (physicalSize_ceiling m native nativeFit).2.1
  have bM : base≤(M m)^2 := baseFit.trans (Nat.pow_le_pow_left ms _)
  have cap : J6SourcePrecision.printed m base≤41*(M m)^2 := by
    calc
      _ ≤ base+40*(M m)^2 := printed_precision_quadratic m base
      _ ≤ (M m)^2+40*(M m)^2 := Nat.add_le_add_right bM _
      _ = _ := by ring
  have sqEq : (2:ℕ)^chosenQ m=64*(M m)^2 := by
    unfold chosenQ M
    rw [pow_add,mul_comm 2 (lambda m),pow_mul]
    norm_num
    ring
  have mpos : 0<M m := by unfold M; positivity
  have pFit : J6SourcePrecision.printed m base<2^chosenQ m := by
    rw [sqEq]
    exact cap.trans_lt (Nat.mul_lt_mul_of_pos_right (by decide) (by positivity))
  have copy : K m<2^chosenQ m := by
    have qlarge : lambda m<chosenQ m := by unfold chosenQ; omega
    exact (true_copy_count_below_mesh m).trans_lt (Nat.pow_lt_pow_right (by decide) qlarge)
  have baseLe : base≤J6SourcePrecision.printed m base := by
    unfold J6SourcePrecision.printed
    omega
  exact ⟨baseLe.trans_lt pFit,copy,pFit,pFit,
    true_printed_roster_code_fits_expanded_code m base (chosenQ m) (chosen_q_above_one m).le pFit⟩

theorem source_base_domain_implies_square_bound {base C s : ℕ}
    (fit : base≤C*s) (small : C≤s) : base≤s^2 := by
  rw [pow_two]
  exact fit.trans (Nat.mul_le_mul_right _ small)

#print axioms code_is_explicit
#print axioms chosen_widths_are_on_true_source_mesh
#print axioms chosen_code_fits_storage
#print axioms true_copy_count_below_mesh
#print axioms true_printed_roster_code_fits_expanded_code
#print axioms chosen_precision_width_never_truncates
#print axioms source_base_domain_implies_square_bound
end J6R110RootWidthChoice

