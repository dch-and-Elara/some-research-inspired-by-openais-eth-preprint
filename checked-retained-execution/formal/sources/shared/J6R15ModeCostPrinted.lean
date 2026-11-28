import P11FullPackingPlacement
import Mathlib.Tactic

/-! Arithmetic for the literal printed node precision. The inherited
precision estimate and the scale comparison u(a+1)≤D are kept
explicit; this does not reprove their global threshold on a path. -/
namespace J6R15ModeCost
open P11FullPacking

def nodePrecision (a M u D inherited : ℕ) : ℕ :=
  inherited+8*ceilCopies u (3*M)*D+8*M*(a+1)

theorem nodePrecision_lower (a M u D inherited : ℕ) :
    6*M≤nodePrecision a M u D inherited := by
  unfold nodePrecision
  have H := Nat.mul_le_mul_left (8*M) (show 1≤a+1 by omega)
  simp only [Nat.mul_one] at H
  omega

theorem nodePrecision_upper (a M u D inherited c : ℕ) (hu : 0<u) (hM : u≤M)
    (hParent : inherited*u≤c*M*D) (hGeom : u*(a+1)≤D) :
    nodePrecision a M u D inherited*u≤(c+40)*M*D := by
  have hceil := (rounded_capacity u (3*M) hu).2
  have hH : ceilCopies u (3*M)*u≤4*M := by omega
  have h₁ := Nat.mul_le_mul_left (8*D) hH
  have h₂ := Nat.mul_le_mul_left (8*M) hGeom
  calc
    nodePrecision a M u D inherited*u=
        inherited*u+(8*D)*(ceilCopies u (3*M)*u)+(8*M)*(u*(a+1)) := by
      unfold nodePrecision
      ring
    _≤c*M*D+(8*D)*(4*M)+(8*M)*D := Nat.add_le_add (Nat.add_le_add hParent h₁) h₂
    _=_ := by ring

theorem native_tile_scale (a i : ℕ) (hi : i≤a) : 2^a/2^i=2^(a-i) := by
  have H : 2^(a-i)*2^i=(2:ℕ)^a := by rw [← pow_add,Nat.sub_add_cancel hi]
  rw [← H]
  exact Nat.mul_div_cancel _ (by positivity)

#print axioms nodePrecision_lower
#print axioms nodePrecision_upper
#print axioms native_tile_scale
end J6R15ModeCost

