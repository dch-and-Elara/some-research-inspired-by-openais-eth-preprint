import J6R49CostActive
import A1R10Budget
import J6R16ModeCostUniform

/-! Polynomial caps on the literal bit arithmetic and weighted-mode
cursor. These costs are not unit-cost ring-gate counts. -/
namespace J6R57ActiveFee
open A1R10 A1R11 A1R12 J6R49Cost
open J6R15ModeCost (delayCap transitionCap scanCap)

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
set_option maxRecDepth 2400
set_option Elab.async false

private theorem raisePow (K a b : ℕ) (h : a≤b) : (K+1)^a≤(K+1)^b :=
  Nat.pow_le_pow_right (Nat.succ_pos K) h

theorem uvWidth_physical_poly {e ell p K : ℕ} (he : e≤K) (hℓ : ell≤K) (hp : p≤K) :
    uvWidth e ell p≤5*(K+1)^3 := by
  have H : uvWidth e ell p≤K*(K*K+1)+4 := by unfold uvWidth; gcongr
  refine H.trans ?_
  have E : 5*(K+1)^3=(K*(K*K+1)+4)+(4*K^3+15*K^2+14*K+1) := by ring
  rw [E]
  exact Nat.le_add_right _ _

theorem addCap_physical_poly {e ell p K : ℕ} (h : 0<p)
    (he : e≤K) (hℓ : ell≤K) (hp : p≤K) :
    addCap e ell p h≤428*(K+1)^5 := by
  have ug : uBudgetGates e p h≤424*(K+1)^4 := by
    refine (uBudgetGates_poly e p h).trans ?_
    calc
      _≤424*((K+1)^2*(K+1)^2) := by gcongr
      _=_ := by ring
  have pe : e*p+1≤(K+1)^2 := by
    have a : e*p+1≤K*K+1 := by gcongr
    have eq : (K+1)^2=(K*K+1)+2*K := by ring
    rw [eq]
    exact a.trans (Nat.le_add_right _ _)
  have q := pe.trans (raisePow K 2 4 (by decide))
  have ellCap : ell≤K+1 := hℓ.trans (Nat.le_succ K)
  unfold addCap
  calc
    _≤(K+1)*(424*(K+1)^4+4*(K+1)^4) := by gcongr
    _=_ := by ring

theorem mulCap_physical_poly {e ell p K : ℕ} (he : e≤K) (hℓ : ell≤K) (hp : p≤K) :
    mulCap e ell p≤3432*(K+1)^6 := by
  unfold mulCap
  calc
    _≤3432*((K+1)^2*(K+1)^2*(K+1)^2) := by gcongr
    _=_ := by ring

theorem delayCap_physical_poly {q n K : ℕ} (hq : q≤K) (hn : n≤K) :
    delayCap q n≤128*(K+1)^4 := by
  have H : delayCap q n≤delayCap K K := by unfold delayCap transitionCap scanCap; gcongr
  refine H.trans ?_
  have E : 128*(K+1)^4=delayCap K K+
      (96*K^4+336*K^3+362*K^2+177*K+42) := by unfold delayCap transitionCap scanCap; ring
  rw [E]
  exact Nat.le_add_right _ _

theorem mode_phase_physical_poly {e ell p q n K : ℕ} (h : 0<p)
    (he : e≤K) (hℓ : ell≤K) (hp : p≤K) (hq : q≤K) (hn : n≤K) :
    perModeArithmetic e ell p h+delayCap q n≤250000*(K+1)^6 := by
  have u := (uvWidth_physical_poly he hℓ hp).trans
    (Nat.mul_le_mul_left _ (raisePow K 3 6 (by decide)))
  have a := (addCap_physical_poly h he hℓ hp).trans
    (Nat.mul_le_mul_left _ (raisePow K 5 6 (by decide)))
  have m := mulCap_physical_poly he hℓ hp
  have d := (delayCap_physical_poly hq hn).trans
    (Nat.mul_le_mul_left _ (raisePow K 4 6 (by decide)))
  have k : 1≤(K+1)^6 := Nat.one_le_pow _ _ (Nat.succ_pos K)
  unfold perModeArithmetic
  omega

#print axioms uvWidth_physical_poly
#print axioms addCap_physical_poly
#print axioms mulCap_physical_poly
#print axioms delayCap_physical_poly
#print axioms mode_phase_physical_poly
end J6R57ActiveFee
