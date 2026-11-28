import ACompactLayoutParameters
import AAcquisitionCostSeats
import Mathlib.Logic.Equiv.Fin.Basic

/-! Executable in-class ordering for A4's single planted diagonal class.
Each named hard occurrence has one preceding designated port and one
remaining old-variable wire; the tail consists of actual filler wires.
-/

namespace ACompactLayout

abbrev DiagonalWire (t pad : ℕ) := (Fin t × Bool) ⊕ (Fin t ⊕ Fin pad)

def diagonalAddress {t pad : ℕ} : DiagonalWire t pad → Fin (3*t+pad)
  | .inl (i,b) => ⟨2*i.val+(if b then 1 else 0), by have hf := i.isLt; cases b <;> simp <;> omega⟩
  | .inr (.inl i) => ⟨2*t+i.val, by have hf := i.isLt; omega⟩
  | .inr (.inr i) => ⟨3*t+i.val, by have hf := i.isLt; omega⟩

def diagonalWire {t pad : ℕ} (i : Fin (3*t+pad)) : DiagonalWire t pad :=
  if h : i.val < 2*t then
    .inl (⟨i.val/2,by omega⟩,decide (i.val%2=1))
  else if h' : i.val < 3*t then
    .inr (.inl ⟨i.val-2*t,by omega⟩)
  else .inr (.inr ⟨i.val-3*t,by have hi := i.isLt; omega⟩)

theorem diagonal_left {t pad : ℕ} (w : DiagonalWire t pad) :
    diagonalWire (diagonalAddress w) = w := by
  rcases w with ⟨i,b⟩ | (i | i)
  · have hi := i.isLt
    cases b with
    | false =>
      have h : (2*i.val : ℕ) < 2*t := by omega
      have hv : (2*i.val : ℕ)/2 = i.val := by omega
      have hm : (2*i.val : ℕ)%2 = 0 := by omega
      simp [diagonalWire,diagonalAddress,h,hv,hm]
    | true =>
      have h : (2*i.val+1 : ℕ) < 2*t := by omega
      have hv : (2*i.val+1 : ℕ)/2 = i.val := by omega
      have hm : (2*i.val+1 : ℕ)%2 = 1 := by omega
      simp [diagonalWire,diagonalAddress,h,hv,hm]
  · have hi := i.isLt
    have h₁ : ¬2*t+i.val < 2*t := by omega
    have h₂ : 2*t+i.val < 3*t := by omega
    simp [diagonalWire,diagonalAddress,h₁,h₂]
  · have h₁ : ¬3*t+i.val < 2*t := by omega
    have h₂ : ¬3*t+i.val < 3*t := by omega
    simp [diagonalWire,diagonalAddress,h₁,h₂]

theorem diagonal_right {t pad : ℕ} (i : Fin (3*t+pad)) :
    diagonalAddress (diagonalWire i) = i := by
  apply Fin.ext
  unfold diagonalWire
  split <;> rename_i h
  · have hmod := Nat.mod_lt i.val (by decide : 0 < 2)
    by_cases hpar : i.val%2=1
    · simp only [diagonalAddress, hpar, decide_true, if_true]
      omega
    · simp only [diagonalAddress, hpar, decide_false, Bool.false_eq_true, if_false]
      omega
  · split <;> simp only [diagonalAddress] <;> omega

def diagonalOrder (t pad : ℕ) : DiagonalWire t pad ≃ Fin (3*t+pad) :=
  ⟨diagonalAddress,diagonalWire,diagonal_left,diagonal_right⟩

def diagonalSeat {t pad b L : ℕ} (eq : 3*t+pad=b*L) :
    DiagonalWire t pad ≃ Fin b × Fin L :=
  (diagonalOrder t pad).trans ((finCongr eq).trans finProdFinEquiv.symm)

theorem even_pair_page (L i : ℕ) (hpos : 0 < L) (heven : Even L) :
    (2*i+1)/L=(2*i)/L ∧ (2*i+1)%L=(2*i)%L+1 := by
  obtain ⟨n,hn⟩ := heven
  have hL : L=2*n := by omega
  have hp : 0 < n := by omega
  have hpp : 0 < 2*n := by omega
  have hr := Nat.mod_lt i hp
  have hev : 2*i = 2*(i%n)+(2*n)*(i/n) := by rw [Nat.mul_assoc,← Nat.mul_add,Nat.mod_add_div]
  have hod : 2*i+1 = (2*(i%n)+1)+(2*n)*(i/n) := by omega
  have hdiv0 : (2*i)/L = i/n := by
    rw [hL,hev,Nat.add_mul_div_left _ _ hpp,Nat.div_eq_of_lt (by omega),Nat.zero_add]
  have hdiv1 : (2*i+1)/L = i/n := by
    rw [hL,hod,Nat.add_mul_div_left _ _ hpp,Nat.div_eq_of_lt (by omega),Nat.zero_add]
  refine ⟨hdiv1.trans hdiv0.symm,?_⟩
  have H0 := Nat.mod_add_div (2*i) L
  have H1 := Nat.mod_add_div (2*i+1) L
  rw [hdiv0] at H0
  rw [hdiv1] at H1
  omega

theorem planted_predecessor {t pad b L : ℕ} (eq : 3*t+pad=b*L)
    (hpos : 0 < L) (heven : Even L) (i : Fin t) :
    AAcquisitionCost.wirePred (diagonalSeat eq) (.inl (i,true)) = some (.inl (i,false)) := by
  apply (AAcquisitionCost.wirePred_spec _ _ _).2
  have h := even_pair_page L i.val hpos heven
  refine ⟨?_,?_⟩
  · apply Fin.ext
    exact h.1
  · change (((2*i.val)%L : ℕ):ℤ)+1 = (((2*i.val+1)%L : ℕ):ℤ)
    exact_mod_cast h.2.symm

def diagonalPadding (w : ℕ) : ℕ := perCell w - w

theorem diagonal_fits (t : ℕ) :
    3*t+diagonalPadding (3*t)=packetCopies (3*t)*packetLength (3*t) := by
  have h := common_load (3*t)
  unfold diagonalPadding
  rw [← h.2.1]
  omega

def printedDiagonalSeat (t : ℕ) :
    DiagonalWire t (diagonalPadding (3*t)) ≃
      Fin (packetCopies (3*t)) × Fin (packetLength (3*t)) :=
  diagonalSeat (diagonal_fits t)

theorem printedDiagonal_pred (t : ℕ)
    (hU : 1 ≤ J9PrintedSchedule.rootU (lambda (3*t))) (j : Fin t) :
    AAcquisitionCost.wirePred (printedDiagonalSeat t) (.inl (j,true)) = some (.inl (j,false)) :=
  planted_predecessor (diagonal_fits t) (by unfold packetLength; positivity)
    (packetLength_even _ hU) j

def emitAddresses (t pad : ℕ) : List (DiagonalWire t pad) :=
  (List.finRange (3*t+pad)).map diagonalWire

theorem emitAddresses_index (t pad : ℕ) (i : Fin (3*t+pad)) :
    (emitAddresses t pad)[i.val]? = some (diagonalWire i) := by
  simp [emitAddresses,i.isLt]

theorem emitAddresses_length (t pad : ℕ) : (emitAddresses t pad).length=3*t+pad := by
  simp [emitAddresses]

#print axioms diagonal_left
#print axioms diagonal_right
#print axioms even_pair_page
#print axioms planted_predecessor
#print axioms printedDiagonal_pred
#print axioms emitAddresses_index
#print axioms emitAddresses_length

end ACompactLayout
