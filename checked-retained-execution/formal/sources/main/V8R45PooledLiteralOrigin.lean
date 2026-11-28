import V8PooledMenuRoot
import J6R12BlueprintReach

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
set_option maxRecDepth 2400

/-! The root of C4 is the lowered C6 formula itself.  Its signed tables
are frozen at the same creation precision used by the completed-slot
menu. No independent raw host or separately asserted target is used. -/
namespace V8R45PooledLiteral
open scoped BigOperators Classical Polynomial
open Polynomial V8PooledRange V8PooledRange.NativeOrigin
open V8PooledMenu.FiveCopy
open J6R10Repack J6R9Recursive J6R11Blueprint J6R11Repack
open J6R12Blueprint J6ActiveRun

noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]
variable (G : Graph V E) (p : ThreePorts G) (f : ℤ[X])

def rawHost (s : V → Bool) : PhysicalHost f 1 :=
  physicalHost (network G p) (file f G p s)

def originCall (s : V → Bool) : Call (PhysicalHost f 1) :=
  ⟨rawHost G p f s, 0, wireSize V, rootPrec V⟩

theorem literal_root_network (s s' : V → Bool) :
    (rawHost G p f s).network = (rawHost G p f s').network := rfl

theorem literal_root_edgeCount (s : V → Bool) :
    (originCall G p f s).host.edgeCount = (originCall G p f s).edges :=
  (wires_card G p)

theorem literal_root_creation_tags (s : V → Bool) :
    GoodTags (originCall G p f s).host (originCall G p f s).prec :=
  fun _ => Nat.le_refl _

private theorem product_indicator {I R : Type*} [DecidableEq I] [CommMonoidWithZero R]
    (T : Finset I) (P : I → Prop) [DecidablePred P] :
    (∏ j ∈ T, if P j then (1:R) else 0) = if ∀ j ∈ T, P j then 1 else 0 := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
      rw [Finset.prod_insert hj,ih]
      by_cases hj' : P j <;> by_cases hT : ∀ z ∈ T, P z <;> simp [hj',hT]

theorem literal_root_exact_contraction (s : V → Bool) (hf : f.Monic) (hd : 0<f.natDegree) :
    (rawHost G p f s).contract hf =
      ((originCount G p s : ℕ) : IntRing f 1) := by
  classical
  change (∑ x : Edge V E → Bool, ∏ v : RawOld V E ⊕ Occ V E,
    ((file f G p s) v).frozen hf (assignment (network G p) x v)) = _
  let W : Finset (Edge V E → Bool) := Finset.univ.filter (Satisfied G p s)
  have hW : W.card = originCount G p s := by
    unfold originCount
    rw [Fintype.card_subtype]
  rw [←hW,Finset.card_eq_sum_ones,Nat.cast_sum]
  simp only [Nat.cast_one, W, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hrow : ∀ v : RawOld V E ⊕ Occ V E,
      ((file f G p s) v).frozen hf (assignment (network G p) x v) =
        if flags G p s v (assignment (network G p) x v) = true then
          (1 : IntRing f 1) else 0 := by
    intro v
    change canonicalLift (rootPrec V) f hf 1
      (if flags G p s v (assignment (network G p) x v) then 1 else 0) = _
    exact J6R12Repack.canonical_lift_bool _ (rootPrec_pos V) f hf hd _ (by decide) _
  simp only [hrow]
  rw [product_indicator]
  simp only [Finset.mem_univ,true_implies,flags_eq_origin]

theorem literal_root_exact_CNF (s : V → Bool) (hf : f.Monic) (hd : 0<f.natDegree) :
    (rawHost G p f s).contract hf = ((satCount G p s : ℕ) : IntRing f 1) := by
  rw [literal_root_exact_contraction G p f s hf hd,originCount_eq]

theorem literal_count_fits_creation (s : V → Bool) :
    originCount G p s < 2^(originCall G p f s).prec := by
  rw [originCount_eq]
  exact physical_terminal_precision G p s

#print axioms literal_root_network
#print axioms literal_root_edgeCount
#print axioms literal_root_creation_tags
#print axioms literal_root_exact_contraction
#print axioms literal_root_exact_CNF
#print axioms literal_count_fits_creation
end
end V8R45PooledLiteral