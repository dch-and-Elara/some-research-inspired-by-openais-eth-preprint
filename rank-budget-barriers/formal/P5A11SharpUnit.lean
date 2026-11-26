import P5A11FiniteLocal
import Mathlib.RingTheory.Nilpotent.Basic

/-! The actual finite receiving ring for the distinct-residue sharp
example. All roots except the node's own map to real units; the same
node contributes its exact power of the receiving root. -/
namespace Paper5
open Polynomial Matrix
open scoped BigOperators Polynomial Classical

variable {R T : Type*} [CommRing R]

theorem nativeObs_factor_shift (π t b α : R) (P k : ℕ) :
    nativeObs π t α P k (X-C b) = algebraMap R (LocalJet π P k) (t-b) +
      algebraMap R (LocalJet π P k) α * AdjoinRoot.root (X^k : (Cyclic π P)[X]) := by
  rw [map_sub,nativeObs_X,nativeObs_coefficient,map_sub]
  ring

theorem localJet_canonical_root_nil (π : R) (P k : ℕ) :
    (AdjoinRoot.root (X^k : (Cyclic π P)[X]))^k=0 := by
  change (AdjoinRoot.mk (X^k) X : LocalJet π P k)^k=0
  rw [←map_pow,AdjoinRoot.mk_self]

theorem unit_plus_mul_nilpotent {S : Type*} [CommRing S] (c d x : S)
    (hc : IsUnit c) (hx : IsNilpotent x) : IsUnit (c+d*x) := by
  obtain ⟨u,rfl⟩ := hc
  let dd : S := (↑u⁻¹:S)*d
  have hx' : IsNilpotent (dd*x) := by
    obtain ⟨k,hk⟩ := hx
    exact ⟨k,by rw [mul_pow,hk,mul_zero]⟩
  have hUnit : IsUnit (dd*x+1) := hx'.isUnit_add_one
  have hEq : (↑u:S)*(dd*x+1) = (↑u:S)+d*x := by
    dsimp [dd]
    rw [mul_add,mul_one,←mul_assoc,←mul_assoc,Units.mul_inv,one_mul]
    ring
  rw [←hEq]
  exact u.isUnit.mul hUnit

theorem nativeObs_other_root_unit (π t b α : R) (P k : ℕ)
    (h : IsUnit (t-b)) : IsUnit (nativeObs π t α P k (X-C b)) := by
  rw [nativeObs_factor_shift]
  exact unit_plus_mul_nilpotent _ _ _
    (h.map (algebraMap R (LocalJet π P k))) ⟨k,localJet_canonical_root_nil π P k⟩

theorem nativeObs_own_root (π t α : R) (P k : ℕ) :
    nativeObs π t α P k (X-C t) =
      algebraMap R (LocalJet π P k) α * AdjoinRoot.root (X^k : (Cyclic π P)[X]) := by
  rw [nativeObs_factor_shift,sub_self,map_zero,zero_add]

variable [Fintype T] [IsLocalRing R]

noncomputable def sharpScalar (t : T→R) (l : T→ℕ) : R[X] :=
  ∏ u,(X-C (t u))^(l u)

set_option maxHeartbeats 8000000 in
theorem sharp_scalar_native_shape (π : R) (t α : T→R) (P k l : T→ℕ)
    (ht : Function.Injective ((IsLocalRing.residue R)∘t))
    (ha : ∀ u,IsUnit (α u)) (u : T) :
    ∃ v : (LocalJet π (P u) (k u))ˣ,
      nativeObs π (t u) (α u) (P u) (k u) (sharpScalar t l) =
        (v:LocalJet π (P u) (k u))*(AdjoinRoot.root (X^(k u) : (Cyclic π (P u))[X]))^(l u) := by
  let S := LocalJet π (P u) (k u)
  let z : S := AdjoinRoot.root (X^(k u) : (Cyclic π (P u))[X])
  let m := nativeObs π (t u) (α u) (P u) (k u)
  let f (s : T) : S := (m (X-C (t s)))^(l s)
  let U : Finset T := Finset.univ.erase u
  have hu (S' : Finset T) (hf : ∀ s∈S',IsUnit (f s)) : IsUnit (∏ s∈S',f s) := by
    induction S' using Finset.induction_on with
    | empty => simp
    | @insert a' A' ha' ih =>
      rw [Finset.prod_insert ha']
      exact (hf a' (Finset.mem_insert_self _ _)).mul (ih fun j hj=>hf j (Finset.mem_insert_of_mem hj))
  have hprod : IsUnit (∏ s∈U,f s) := by
    apply hu
    intro s hs
    have hne : s≠u := Finset.ne_of_mem_erase hs
    have h0 : (IsLocalRing.residue R) (t u-t s)≠0 := by
      rw [map_sub,sub_ne_zero]
      intro hh
      exact hne ((ht hh).symm)
    exact (nativeObs_other_root_unit π (t u) (t s) (α u) (P u) (k u)
      ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp h0)).pow _
  have hUnit : IsUnit ((algebraMap R S (α u))^(l u)*(∏ s∈U,f s)) :=
    ((ha u).map (algebraMap R S)).pow _ |>.mul hprod
  obtain ⟨v,hv⟩ := hUnit
  refine ⟨v,?_⟩
  change m (sharpScalar t l)=(v:S)*z^(l u)
  rw [hv]
  unfold sharpScalar
  rw [map_prod]
  simp only [map_pow]
  change (∏ s,f s)=_
  rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ u)]
  change f u*(∏ s∈U,f s)=_
  unfold f
  change (nativeObs π (t u) (α u) (P u) (k u) (X-C (t u)))^(l u)*_ = _
  rw [nativeObs_own_root,mul_pow]
  ring

#print axioms nativeObs_factor_shift
#print axioms localJet_canonical_root_nil
#print axioms nativeObs_other_root_unit
#print axioms sharp_scalar_native_shape
end Paper5
