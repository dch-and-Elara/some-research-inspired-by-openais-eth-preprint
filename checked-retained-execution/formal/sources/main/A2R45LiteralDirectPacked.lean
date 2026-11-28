import A2R45LiteralDirectDegrees
import A2R45LiteralDirectRegister
import A1R43LiteralGeneralEstimate

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 11000000
set_option maxRecDepth 2300
set_option linter.unusedSectionVars false

/-! Use exactly the source A1/A2 full-seat layout on the direct
clause/equality-path network. No arbitrary pairing or rank oracle. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial Std.Sat J7R9Compiler
open A1R43Literal A1R43Literal.General J6R10Repack J6R12Repack J6R11Integral

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] (F : CNF V)

abbrev directM := Nat.card (DirectWire F)

theorem actual_direct_linear_size :
    directM F≤6*Fintype.card (Occurrence F) := by
  have wl : Fintype.card (DirectLink F)≤Fintype.card (Occurrence F) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact direct_path_literal_size F
  have wo : (∑ c : ClauseIndex F, (F.get c).length)=Fintype.card (Occurrence F) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
  unfold directM
  rw [Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.sum_sum_type]
  simp only [a3_row_card,directArity]
  rw [←Finset.mul_sum,wo,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change 2*Fintype.card (Occurrence F)+Fintype.card (DirectLink F)*4≤6*Fintype.card (Occurrence F)
  omega

abbrev DirectPlan := PairPlan (directNetwork F) (smallA (directM F)) (copies (directM F))

theorem direct_actual_plan_exists (width : ∀ cl∈F,cl.length≤3) (guard : PrintedMargins (directM F)) :
    Nonempty (DirectPlan F) := by
  obtain ⟨hrow,hcol⟩ := direct_concrete_network_degrees F width
  exact printed_general_pair_plan (directNetwork F) 6 guard le_rfl hrow
    (fun k=>(hcol k).trans (by decide))

variable (W : DirectPlan F)
abbrev DirectPad := Spare (directNetwork F) W

def directPadFinite : Fintype (DirectPad F W) := Fintype.ofFinite _

theorem actual_direct_packing_uses_pair_seats :
    letI : Fintype (DirectPad F W) := directPadFinite F W
    pairedDirect F (fullPacking (directNetwork F) W) :=
  full_seat_predecessor (directNetwork F) W

def directEffectiveRegister (f : ℤ[X]) (p : ℕ) (hf : f.Monic) : J6R9Recursive.Box f 1 p :=
  letI : Fintype (DirectPad F W) := directPadFinite F W
  let m := directM F
  let i : Fin (smallA m+1) := ⟨0,Nat.succ_pos _⟩
  ∏ g : Fin 64, J6R9Recursive.reduce p f 1
    (actualChildTruth (fullPacking (directNetwork F) W) i
      (by decide : (-1:ℤ)≠0) (minus_one_odd_index (smallA m+1) i rfl)
      p 0 (directNativeFile F f (Fintype.card V+1)) hf 0 g)

theorem direct_effective_register_count (occurs : AllOccur F)
    (f : ℤ[X]) (p : ℕ) (hp : Fintype.card V+1≤p)
    (hf : f.Monic) (hd : 0<f.natDegree) :
    boxNatural f 1 p hf (directEffectiveRegister F W f p hf)=PinnedCNF.modelCount F := by
  unfold directEffectiveRegister
  letI : Fintype (DirectPad F W) := directPadFinite F W
  exact direct_literal_completed_integer F (fullPacking (directNetwork F) W) _ rfl f p hp hf hd
    (actual_direct_packing_uses_pair_seats F W) occurs

theorem source_degree_six_paired_register (width : ∀ cl∈F,cl.length≤3)
    (guard : PrintedMargins (directM F)) (occurs : AllOccur F)
    (f : ℤ[X]) (p : ℕ) (hp : Fintype.card V+1≤p)
    (hf : f.Monic) (hd : 0<f.natDegree) :
    ∃ W : DirectPlan F,
      boxNatural f 1 p hf (directEffectiveRegister F W f p hf)=PinnedCNF.modelCount F := by
  obtain ⟨W⟩ := direct_actual_plan_exists F width guard
  exact ⟨W,direct_effective_register_count F W occurs f p hp hf hd⟩

#print axioms actual_direct_linear_size
#print axioms direct_actual_plan_exists
#print axioms actual_direct_packing_uses_pair_seats
#print axioms direct_effective_register_count
#print axioms source_degree_six_paired_register
end
end A2R45Literal
