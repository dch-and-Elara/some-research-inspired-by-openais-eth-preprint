import J1R43LiteralIntegerScore

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7100000
set_option linter.unusedSectionVars false

/-! Bound all actual integer score words by explicit positive polynomial
expressions. Magnitudes here are numbers, not oracle calls or bytes. -/
namespace J1R43Literal
open scoped BigOperators
open J1MainSourceLabels
noncomputable section

section Abs
variable {T : Type*}

theorem abs_sum_bounded (s : Finset T) (f : T→ℤ) (b : ℕ)
    (h : ∀ i∈s,(f i).natAbs≤b) : (∑ i∈s,f i).natAbs≤s.card*b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a u ha ih =>
    rw [Finset.sum_insert ha,Finset.card_insert_of_notMem ha,Nat.add_mul,one_mul]
    exact (Int.natAbs_add_le _ _).trans
      ((Nat.add_le_add (h a (Finset.mem_insert_self ..))
        (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))).trans_eq (Nat.add_comm _ _))

theorem abs_big_sum_bounded [Fintype T] (f : T→ℤ) (b : ℕ)
    (hf : ∀ i,(f i).natAbs≤b) : (∑ i,f i).natAbs≤Fintype.card T*b := by
  simpa only [Finset.card_univ] using abs_sum_bounded Finset.univ f b (fun i _ => hf i)

theorem abs_diff_bound (x y : ℤ) {bx byy : ℕ} (hx : x.natAbs≤bx) (hy : y.natAbs≤byy) :
    (x-y).natAbs≤bx+byy :=
  (Int.natAbs_sub_le _ _).trans (Nat.add_le_add hx hy)

theorem abs_three_bound (x y z : ℤ) {bx byy bz : ℕ} (hx : x.natAbs≤bx)
    (hy : y.natAbs≤byy) (hz : z.natAbs≤bz) :
    (x+y+z).natAbs≤bx+byy+bz :=
  (Int.natAbs_add_le _ _).trans (Nat.add_le_add
    ((Int.natAbs_add_le _ _).trans (Nat.add_le_add hx hy)) hz)

end Abs

def intHeightBound (m n h q r scale weight : ℕ) : ℕ :=
  (q*n)*h^2*(m^2*(2*scale)) + (5*m)*h^2*(q*n^2*(2*scale)) +
    (5*m)*(q*n)*8*(q*r*(h^2*scale*(weight+1)^2))

section Statement

variable {V F B I S E A : Type*}
  [Fintype V] [Fintype F] [Fintype B] [Fintype I] [Fintype S] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq F] [DecidableEq B] [DecidableEq I] [DecidableEq S] [Nonempty S]
variable (t : I) (tag : F → Option B) (var : E → V) (fac : E → F) (pin : A → E)
    (known : Primitive V F B I → Option S)

local notation "q" => Fintype.card I
local notation "r" => Fintype.card S
local notation "m" => Fintype.card E
local notation "n" => Fintype.card V
local notation "h" => Fintype.card A
local notation "R" => r^(4*q)
local notation "W" => r^(q+1)

theorem eventInt_height (j : ScoreVisit E V A I S) :
    (eventInt t tag var fac pin known j).natAbs≤R := by
  unfold eventInt
  simpa only [Int.natAbs_ofNat'] using (actual_visit_scaled t tag var fac pin j known).2

theorem phiInt_height :
    (phiInt t tag var fac pin known).natAbs≤m^2*(2*R) := by
  unfold phiInt
  have hr : 0<r := Fintype.card_pos
  have hc : r^(2*q)≤R := Nat.pow_le_pow_right hr (by omega)
  rw [show m^2=Fintype.card (E×E) by rw [Fintype.card_prod,pow_two]]
  apply abs_big_sum_bounded
  intro j
  have he := eventInt_height t tag var fac pin known (.inl j)
  have hv := abs_diff_bound _ ((r^(2*q):ℕ):ℤ) he (show (((r^(2*q):ℕ):ℤ).natAbs≤R) by
    simpa only [Int.natAbs_natCast] using hc)
  exact hv.trans_eq (by ring)

theorem xiInt_height :
    (xiInt t tag var fac pin known).natAbs≤q*n^2*(2*R) := by
  unfold xiInt
  have hr : 0<r := Fintype.card_pos
  have hc : r^(4*q-1)≤R := Nat.pow_le_pow_right hr (Nat.sub_le _ _)
  rw [show q*n^2*(2*R)=q*(Fintype.card (V×V)*(2*R)) by rw [Fintype.card_prod,pow_two]; ring]
  apply abs_big_sum_bounded
  intro i
  apply abs_big_sum_bounded
  intro j
  have he := eventInt_height t tag var fac pin known (.inr (.inl (i,j)))
  have hv := abs_diff_bound _ ((r^(4*q-1):ℕ):ℤ) he
    (show (((r^(4*q-1):ℕ):ℤ).natAbs≤R) by simpa only [Int.natAbs_natCast] using hc)
  exact hv.trans_eq (by ring)

theorem pairInt_height (j : I×S) :
    (pairInt t tag var fac pin known j).natAbs≤h^2*R := by
  unfold pairInt
  rw [show h^2=Fintype.card (A×A) by rw [Fintype.card_prod,pow_two]]
  exact abs_big_sum_bounded _ _ fun e=>eventInt_height t tag var fac pin known (.inr (.inr (j,.inl e)))

theorem singleInt_height (j : I×S) :
    (singleInt t tag var fac pin known j).natAbs≤h*R := by
  unfold singleInt
  exact abs_big_sum_bounded _ _ fun a=>eventInt_height t tag var fac pin known (.inr (.inr (j,.inr a)))

theorem varInt_height (j : I×S) :
    (varInt t tag var fac pin known j).natAbs≤h^2*R*(W+1)^2 := by
  unfold varInt
  let x : ℤ := ((W:ℕ):ℤ)^2 * pairInt t tag var fac pin known j
  let y : ℤ := (2:ℤ)*(W:ℕ)*(h:ℕ)*singleInt t tag var fac pin known j
  let z : ℤ := ((h:ℕ):ℤ)^2*(R:ℕ)
  change (x-y+z).natAbs≤_
  have hx : x.natAbs≤W^2*(h^2*R) := by
    unfold x
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (pairInt_height t tag var fac pin known j)
  have hy : y.natAbs≤2*W*h*(h*R) := by
    unfold y
    simp only [Int.natAbs_mul,Int.natAbs_natCast ]
    exact Nat.mul_le_mul_left _ (singleInt_height t tag var fac pin known j)
  have hz : z.natAbs≤h^2*R := by
    simp [z,Int.natAbs_mul]
  exact ((Int.natAbs_add_le _ _).trans
    (Nat.add_le_add (abs_diff_bound x y hx hy) hz)).trans_eq (by ring)

theorem integerScore_height :
    (integerScore t tag var fac pin known).natAbs ≤ intHeightBound m n h q r R W := by
  unfold integerScore intHeightBound
  let x : ℤ := ((q*n:ℕ):ℤ)*(h:ℕ)^2*phiInt t tag var fac pin known
  let y : ℤ := ((5*m:ℕ):ℤ)*(h:ℕ)^2*xiInt t tag var fac pin known
  let z : ℤ := ((5*m:ℕ):ℤ)*(q*n:ℕ)*8*∑ j : I×S,varInt t tag var fac pin known j
  change (x+y+z).natAbs≤_
  have hx : x.natAbs≤q*n*h^2*(m^2*(2*R)) := by
    unfold x
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (phiInt_height t tag var fac pin known)
  have hy : y.natAbs≤5*m*h^2*(q*n^2*(2*R)) := by
    unfold y
    simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (xiInt_height t tag var fac pin known)
  have hz : z.natAbs≤(5*m)*(q*n)*8*(q*r*(h^2*R*(W+1)^2)) := by
    unfold z
    simp only [Int.natAbs_mul,Int.natAbs_natCast ]
    apply Nat.mul_le_mul_left
    rw [← Fintype.card_prod I S]
    exact abs_big_sum_bounded _ _ (varInt_height t tag var fac pin known)
  exact abs_three_bound x y z hx hy hz

end Statement

#print axioms abs_sum_bounded
#print axioms abs_big_sum_bounded
#print axioms eventInt_height
#print axioms phiInt_height
#print axioms xiInt_height
#print axioms pairInt_height
#print axioms singleInt_height
#print axioms varInt_height
#print axioms integerScore_height

end
end J1R43Literal