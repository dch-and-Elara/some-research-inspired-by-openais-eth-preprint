import J6NativeHeightMesh
import J6PackingAssembly
import Mathlib.Tactic

/-! Specialize the cleared integer to the physical no-hole packet
layout. Each row reads its exact same-packet shifted column seat;
a missing seat reads zero. The definition fixes the layout for all odd nodes. -/
namespace J6NativeHeightPort
open J6PhysicalPacking J6Mesh
open J6NativeHeightClearing J6NativeHeightMesh
variable {C : Type*} [DecidableEq C]

noncomputable def shiftedWire (rho : C) (m K l : ℕ) (h : m ≤ K) (t : ℕ)
    (p : Wire rho m K l) : Option (Wire rho m K l) :=
  let s := place rho m K l h p
  if ht : s.2.2.val+t<2*l then
    some ((placement rho m K l h).symm (s.1,s.2.1,⟨s.2.2.val+t,ht⟩))
  else none

theorem shifted_iff_reaches (rho : C) (m K l : ℕ) (h : m ≤ K) (t : ℕ)
    (p q : Wire rho m K l) :
    shiftedWire rho m K l h t p = some q ↔
      reaches t (place rho m K l h p) (place rho m K l h q) := by
  classical
  let s := place rho m K l h p
  let r := place rho m K l h q
  let e := placement rho m K l h
  change (if ht : s.2.2.val+t<2*l then
    some (e.symm (s.1,s.2.1,⟨s.2.2.val+t,ht⟩)) else none) = some q ↔ reaches t s r
  split_ifs with ht
  · rw [Option.some.injEq]
    constructor
    · intro hp
      have hS := congrArg e hp
      rw [e.apply_symm_apply] at hS
      have h₁ := congrArg (fun a : Slot C K l => a.1) hS
      have h₂ := congrArg (fun a : Slot C K l => a.2.1) hS
      have h₃ := congrArg (fun a : Slot C K l => a.2.2.val) hS
      exact ⟨h₁,h₂,h₃⟩
    · rintro ⟨ha,hb,hc⟩
      apply e.injective
      rw [e.apply_symm_apply]
      exact Prod.ext ha (Prod.ext hb (Fin.ext hc))
  · constructor
    · simp
    · rintro ⟨_,_,hc⟩
      exfalso
      exact ht (hc ▸ r.2.2.isLt)

noncomputable def packedRead (rho : C) (m K l : ℕ) (h : m ≤ K) (t : ℕ)
    (p : Wire rho m K l) (x : Wire rho m K l → Bool) : Bool :=
  ((shiftedWire rho m K l h t p).map x).getD false

theorem planted_read (rho : C) (m K l : ℕ) (h : m ≤ K) (t : ℕ)
    (i : Fin m) (j : Fin (2*l)) (x : Wire rho m K l → Bool) :
    packedRead rho m K l h t (.inl (i,j)) x =
      if ht : j.val+t<2*l then x (.inl (i,⟨j.val+t,ht⟩)) else false := by
  unfold packedRead
  split_ifs with ht
  · have hS : shiftedWire rho m K l h t (.inl (i,j)) =
        some (.inl (i,⟨j.val+t,ht⟩)) :=
      (shifted_iff_reaches _ _ _ _ _ _ _ _).mpr
        ((reaches_plant_plant _ _ _ _ _ _ _ _ _ _).mpr ⟨rfl,rfl⟩)
    rw [hS]
    rfl
  · simp [shiftedWire,place,ht]

/-- This existence statement chooses one packing, not a new one per
address. Its signed integer lift fits at every requested odd address. -/
theorem one_packing_centered [Fintype C] (m base : ℕ) (rho : C)
    (hC : Fintype.card C = D m) :
    ∃ l : ℕ, ∃ h : m ≤ K m, 2*l = L m ∧
      ∀ (A B : (Wire rho m (K m) l → Bool) → Bool) (i : Fin (m+1)),
        ∃ z : ℤ, (z : ℚ) = (sampleDen m i : ℚ)^M m *
          rationalSlot A B (packedRead rho m (K m) l h (index m i)) (point m i) ∧
          2*|z| < (↑((2:ℕ)^J6SourcePrecision.printed m base):ℤ) := by
  obtain ⟨l,h,hl,_,hh,_,_⟩ := J6PackingAssembly.literal_assembly m 0 (Nat.zero_le _) rho hC
  refine ⟨l,h,hl,?_⟩
  exact fun A B i => mesh_centered_numerator m base i hh A B
    (packedRead rho m (K m) l h (index m i))

#print axioms shifted_iff_reaches
#print axioms planted_read
#print axioms one_packing_centered
end J6NativeHeightPort
