import J6R10ReachablePadding
import Mathlib.Data.Fintype.Sigma

/-! A finite common alphabet for a genuinely dependent native plan:
each call may have its own type of slots and each centre its own type
of modes. Strict descent and finite child menus yield a finite set of
reachable records. A disjoint union over only those records supplies a
common alphabet to the R9 program, with the exact padding isomorphism.
No global enumeration of arbitrary raw Host records is used. -/
namespace J6R10Reachable
open scoped BigOperators

universe u v w x

structure FinitePlan (C : Type u) where
  size : C → ℕ
  Slot : C → Type v
  finiteSlot : ∀ c, Fintype (Slot c)
  child : ∀ c, Slot c → C
  smaller : ∀ c w, size (child c w) < size c

variable {C : Type u}

inductive NativeReach (P : FinitePlan C) : C → C → Prop
  | reflexive (c : C) : NativeReach P c c
  | step {c d : C} (slot : P.Slot c) (tail : NativeReach P (P.child c slot) d) :
      NativeReach P c d

noncomputable def allSites (P : FinitePlan C) (c : C) : Finset C := by
  classical
  letI : Fintype (P.Slot c) := P.finiteSlot c
  exact insert c (Finset.univ.biUnion (fun w => allSites P (P.child c w)))
termination_by P.size c
decreasing_by exact P.smaller c w

theorem of_mem_allSites (P : FinitePlan C) (c d : C) (h : d ∈ allSites P c) :
    NativeReach P c d := by
  classical
  rw [allSites,Finset.mem_insert,Finset.mem_biUnion] at h
  rcases h with he | ⟨slot,_,tail⟩
  · subst d
    exact NativeReach.reflexive _
  · exact NativeReach.step slot (of_mem_allSites P (P.child c slot) d tail)
termination_by P.size c
decreasing_by exact P.smaller c slot

theorem mem_of_nativeReach (P : FinitePlan C) {c d : C} (h : NativeReach P c d) :
    d ∈ allSites P c := by
  classical
  induction h with
  | reflexive c =>
    rw [allSites]
    exact Finset.mem_insert_self _ _
  | @step c d slot tail ih =>
    rw [allSites]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    exact ⟨slot,@Finset.mem_univ _ (P.finiteSlot c) slot,ih⟩

theorem mem_allSites_iff (P : FinitePlan C) (c d : C) :
    d ∈ allSites P c ↔ NativeReach P c d :=
  ⟨of_mem_allSites P c d,mem_of_nativeReach P⟩

variable (P : FinitePlan C) (root : C)
variable (T : C → Type w) (Local : ∀ c, T c → Type x)

/-- Tagged names prevent accidental sharing between different call/centre
mode inventories. The carrier remembers both tags even when a local
mode label otherwise has the same name. -/
abbrev Alphabet := Σ c : (allSites P root), Σ t : T c.val, Local c.val t

noncomputable instance alphabetFintype [∀ c, Fintype (T c)]
    [∀ c t, Fintype (Local c t)] : Fintype (Alphabet P root T Local) := by
  unfold Alphabet
  infer_instance

noncomputable def nativeMode (c : C) (hc : NativeReach P root c) (t : T c) :
    Local c t ↪ Alphabet P root T Local where
  toFun z := ⟨⟨c,(mem_allSites_iff P root c).mpr hc⟩,⟨t,z⟩⟩
  inj' := by intro a b h; cases h; rfl

theorem reachable_menu_exact [∀ c, Fintype (T c)] [∀ c t, Fintype (Local c t)]
    [∀ c t, DecidableEq (Local c t)] [DecidableEq (Alphabet P root T Local)]
    (c : C) (hc : NativeReach P root c) (t : T c)
    (p : ℕ) (hp : 0 < p) (w : Local c t → ℕ) (hw : ∀ i, 0 < w i) :
    (J6RecursiveMenu.menu p w).map (modeEmbedding (nativeMode P root T Local c hc t)) =
      J6RecursiveMenu.menu p (paddedWeight p (nativeMode P root T Local c hc t) w) :=
  padded_menu p hp _ w hw

/-- A finite envelope exists even if the ambient call space or the
set of potential raw layouts is infinite. -/
theorem reachable_finite (P : FinitePlan C) (c : C) :
    {d : C | NativeReach P c d}.Finite := by
  have he : {d : C | NativeReach P c d} = ↑(allSites P c) := by
    ext d
    exact (mem_allSites_iff P c d).symm
  rw [he]
  exact (allSites P c).finite_toSet

#print axioms mem_allSites_iff
#print axioms nativeMode
#print axioms reachable_menu_exact
#print axioms reachable_finite
end J6R10Reachable