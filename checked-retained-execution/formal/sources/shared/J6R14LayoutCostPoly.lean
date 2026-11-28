import J6R14LayoutCostFixed

/-! The full ordered-key menu is dense, but under the printed
packing-size hypothesis it is no larger than the real edge list.
This gives an explicit quadratic bound in the number of edges for
grouping and address writing, isolating the earlier collision scorer. -/
namespace J6R14LayoutCost

theorem source_menu_size (a b : ℕ) (hb : b=6*a) :
    2^b*2^b=J9PrintedSchedule.arrayCard a := by
  rw [hb,← pow_add,J9PrintedSchedule.arrayCard,show (64:ℕ)=2^6 by decide,← pow_mul]
  congr 1
  omega

theorem source_menu_fit (a b M : ℕ) (hb : b=6*a)
    (hS : 2^a*J9PrintedSchedule.arrayCard a≤M) :
    2^b*2^b≤M := by
  rw [source_menu_size a b hb]
  exact (Nat.le_mul_of_pos_left _ (by positivity)).trans hS

theorem alphabet_fit_menu (b : ℕ) : 2^b≤2^b*2^b :=
  Nat.le_mul_of_pos_right _ (by positivity)

def menuPoly (b M : ℕ) : ℕ := (16*(b+1)+4)*M+(8*b+22)*M+4

theorem allPairsCap_poly (b M : ℕ) (hd : 2^b*2^b≤M) :
    allPairsCap b≤menuPoly b M := by
  have hl := (alphabet_fit_menu b).trans hd
  calc
    allPairsCap b=(16*(b+1)+4)*2^b+(8*b+22)*(2^b*2^b)+4 := by
      unfold allPairsCap
      ring
    _≤menuPoly b M :=
      Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ hl) (Nat.mul_le_mul_left _ hd)) _

def fixedPoly (kR kC b q a M : ℕ) : ℕ :=
  M*tagStepCap kR kC b q+q+2+menuPoly b M+
    (q+2+M*boxStepCap kR kC b q M)+6+roundCap a q+4+
    exportTapeCap kR kC b q a M M+6

theorem packFixedCap_poly (kR kC b q a M : ℕ) (hd : 2^b*2^b≤M) :
    packFixedCap kR kC b q a M≤fixedPoly kR kC b q a M := by
  have ha := allPairsCap_poly b M hd
  have hg := Nat.mul_le_mul_right (boxStepCap kR kC b q M) hd
  have he := Nat.mul_le_mul_right (headerCap a+2*b+q+18) hd
  unfold packFixedCap fixedPoly orderedTapeCap exportTapeCap
  omega

#print axioms source_menu_size
#print axioms source_menu_fit
#print axioms packFixedCap_poly
end J6R14LayoutCost

