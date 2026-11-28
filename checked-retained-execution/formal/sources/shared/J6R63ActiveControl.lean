import J6R63ActivePrecision
import J6R62ActivePrepSite
import J6R17ModeTapeLayout

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9000000
set_option maxRecDepth 2250
set_option Elab.async false

/-! Numeric controls and the retained selected-layout copy word.
The chosen layout is not rerun; these operations consume an already
published copy-count field. -/
namespace J6R63Active
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10
open J6R14LayoutCost J6R17ModeTape J6R52FreshExterior
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted

abbrev ModeWord := J6R15ModeCost.Word

def taperRegister (q u : ℕ) : Meter (ModeWord q) :=
  let z := constantRegister q []
  let o := constantRegister q [true]
  let p := timesAddRegister z.result o.result u
  ⟨aWordAsMode p.result,z.steps+o.steps+p.steps+4⟩

def taperFee (q u : ℕ) : ℕ :=
  2*(4*q+4)+2+u*(wordArithmeticRoof q+5)+4

theorem taper_register_value {q u : ℕ} (fits : u<2^q) :
    (taperRegister q u).result.val=u := by
  have zero : wordRead (constantRegister q []).result=0 :=
    by norm_num [constant_register_read,bitsValue]
  have one : wordRead (constantRegister q [true]).result=1 :=
    by norm_num [constant_register_read,bitsValue,Bool.toNat]
  change bitsValue (timesAddRegister (constantRegister q []).result
    (constantRegister q [true]).result u).result.val=u
  apply exact_nat_of_register_read _ fits
  rw [times_add_register_read,zero,one,mul_one,zero_add]

theorem taper_register_budget {q : ℕ} (hq : 0<q) (u : ℕ) :
    (taperRegister q u).steps≤taperFee q u := by
  have hRec := repeated_add_register_fee_le hq (constantRegister q []).result
    (constantRegister q [true]).result u
  simp only [taperRegister,taperFee,constant_register_fee]
  omega

def copyOfLayout {a copies q₀ M : ℕ}
    (q : ℕ) (L : LayoutReceipt a copies q₀ M) : Meter (ModeWord q) :=
  retainAtWidth q L.copies

theorem retained_layout_copy_word {a copies q₀ M q : ℕ}
    (L : LayoutReceipt a copies q₀ M) (fit : copies<2^q) :
    (copyOfLayout q L).result.val=copies ∧ (copyOfLayout q L).steps=2*q₀+4*q+5 := by
  have F : L.copies.val<2^q := L.copiesMeaning.symm ▸ fit
  obtain ⟨word,fee⟩ := retain_at_width_exact q L.copies F
  exact ⟨word.trans L.copiesMeaning,fee⟩

/-- The exact copy field emitted by the physical packing can be handed
off as bits.  This is a source receipt for the same packed object, not
a second invocation of packGreedy. -/
theorem raw_packing_copy_handoff {a copies q₀ M q : ℕ}
    (raw : GreedyPackedTape) (L : LayoutReceipt a copies q₀ M)
    (same : L.copies.bits=raw.copies) (fit : copies<2^q) :
    let w : ModeWord q₀ := ⟨raw.copies,same ▸ L.copies.size⟩
    retainAtWidth q w=copyOfLayout q L ∧
      (retainAtWidth q w).result.val=copies ∧ (retainAtWidth q w).steps=2*q₀+4*q+5 := by
  have inject : Function.Injective (fun w : ModeWord q₀=>w.bits) := by
    rintro ⟨bits,h⟩ ⟨bits',h'⟩ eq
    change bits=bits' at eq
    subst bits'
    rfl
  have matchWord : (⟨raw.copies,same ▸ L.copies.size⟩ : ModeWord q₀)=L.copies :=
    inject same.symm
  dsimp only
  rw [matchWord]
  exact ⟨rfl,retained_layout_copy_word L fit⟩

noncomputable section
variable {f : ℤ[X]} {ell s q : ℕ} {c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem printed_precision_at_same_centre
    (d : Ready S (sourceDelta s) c) (t : Center S c) :
    precisionAt ((S).levelBits c.depth) (centerIndex d t).val c.prec c.edges ((S).levelWidth c.depth)=
      registerPrecision S c t := by
  unfold precisionAt registerPrecision childPrecision
  have i : (centerIndex d t).val≤(S).levelBits c.depth := (centerIndex d t).isLt.le
  rw [show padicValInt 2 t.val=(centerIndex d t).val from rfl,
    J6R15ModeCost.native_tile_scale _ _ i]

theorem header_words_fit_when_receiver_fits
    (d : Ready S (sourceDelta s) c) (t : Center S c)
    (small : (S).levelWidth c.depth≤c.edges)
    (resultFit : registerPrecision S c t<2^q) :
    c.prec<2^q ∧ c.edges<2^q ∧ (S).levelWidth c.depth<2^q ∧
      3*c.edges+(S).levelWidth c.depth-1<2^q := by
  let a := (S).levelBits c.depth
  let u := (S).levelWidth c.depth
  let D := 8*c.edges*(a+1)
  have hD : D≤registerPrecision S c t := by
    rw [←printed_precision_at_same_centre d t]
    unfold precisionAt J9PrintedSchedule.precision
    exact Nat.le_add_left _ _
  have base : c.prec≤registerPrecision S c t := by
    rw [←printed_precision_at_same_centre d t]
    unfold precisionAt J9PrintedSchedule.precision
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have term : 8*c.edges≤D :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos a)
  have M : c.edges≤8*c.edges := Nat.le_mul_of_pos_left _ (by decide : 0 < (8:ℕ))
  have mass : 3*c.edges+u-1≤4*c.edges := by
    change u≤c.edges at small
    omega
  have seven : 4*c.edges≤8*c.edges := Nat.mul_le_mul_right _ (by decide)
  have hM := M.trans (term.trans hD)
  exact ⟨base.trans_lt resultFit,hM.trans_lt resultFit,small.trans_lt (hM.trans_lt resultFit),
    mass.trans_lt ((seven.trans (term.trans hD)).trans_lt resultFit)⟩

#print axioms taper_register_value
#print axioms taper_register_budget
#print axioms retained_layout_copy_word
#print axioms raw_packing_copy_handoff
#print axioms printed_precision_at_same_centre
#print axioms header_words_fit_when_receiver_fits
end
end J6R63Active

