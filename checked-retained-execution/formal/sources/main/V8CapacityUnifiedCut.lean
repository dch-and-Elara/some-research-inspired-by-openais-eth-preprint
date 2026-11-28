import V8CapacityUnifiedObservation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi

/-! Exact geometry of the common matching restriction in U7/S6.
Transposition is chosen separately for each source cut, while the
physical sender/receiver computation direction never changes. -/
namespace V8CapacityUnified.U7

open scoped Classical
noncomputable section
set_option linter.unusedSectionVars false

abbrev Bits (m : ℕ) := Fin m → Bool

structure Cut (m : ℕ) where
  pa : Finset (Fin m)
  pb : Finset (Fin m)
  /-- Receiver-visible private sender bits. -/
  oa : Finset (Fin m)
  ob : Finset (Fin m)
  /-- Sender-visible private receiver bits. -/
  ia : Finset (Fin m)
  ib : Finset (Fin m)
  oa_sub : oa⊆pa
  ob_sub : ob⊆pb
  ia_disjoint : Disjoint pa ia
  ib_disjoint : Disjoint pb ib

variable {m : ℕ} (C : Cut m)

def Cut.delta : ℕ := max (C.pa.card-C.pb.card) (C.pb.card-C.pa.card)

def Cut.hazard : ℕ :=
  if C.pb.card≤C.pa.card then C.oa.card+C.ib.card else C.ia.card+C.ob.card

def Cut.rowFixed : Finset (Fin m) :=
  if C.pb.card≤C.pa.card then (Finset.univ \ C.pa)∪C.oa else C.pa∪C.ia

def Cut.colFixed : Finset (Fin m) :=
  if C.pb.card≤C.pa.card then C.pb∪C.ib else (Finset.univ \ C.pb)∪C.ob

theorem diff_overlap_disjoint {S T : Finset (Fin m)} (h : T⊆S) :
    Disjoint (Finset.univ \ S) T := by
  apply Finset.disjoint_left.mpr
  intro i hD hT
  exact (Finset.mem_sdiff.mp hD).2 (h hT)

theorem Cut.fixed_card :
    C.rowFixed.card+C.colFixed.card=m-C.delta+C.hazard := by
  have ha : C.pa.card≤m := by simpa using Finset.card_le_univ C.pa
  have hb : C.pb.card≤m := by simpa using Finset.card_le_univ C.pb
  have hda : (Finset.univ \ C.pa).card=m-C.pa.card := by
    simpa using (Finset.card_sdiff_of_subset (Finset.subset_univ C.pa))
  have hdb : (Finset.univ \ C.pb).card=m-C.pb.card := by
    simpa using (Finset.card_sdiff_of_subset (Finset.subset_univ C.pb))
  unfold Cut.delta Cut.hazard Cut.rowFixed Cut.colFixed
  by_cases h : C.pb.card≤C.pa.card
  · rw [if_pos h,if_pos h,if_pos h,Finset.card_union_of_disjoint (diff_overlap_disjoint C.oa_sub),
      Finset.card_union_of_disjoint C.ib_disjoint,hda]
    omega
  · rw [if_neg h,if_neg h,if_neg h,Finset.card_union_of_disjoint C.ia_disjoint,
      Finset.card_union_of_disjoint (diff_overlap_disjoint C.ob_sub),hdb]
    omega

abbrev Fiber (C : Cut m) := ((↑C.rowFixed) → Bool) × ((↑C.colFixed) → Bool)

theorem Cut.fiber_card : Fintype.card (Fiber C)=2^(m-C.delta+C.hazard) := by
  rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fun,Fintype.card_bool,
    Fintype.card_coe,Fintype.card_coe,← pow_add,Cut.fixed_card]

def rowFiber (f : Fiber C) (a : Bits m) : Prop :=
  (fun i : ↑C.rowFixed => a i.val)=f.1

def colFiber (f : Fiber C) (b : Bits m) : Prop :=
  (fun i : ↑C.colFixed => b i.val)=f.2

def fiberOf (a b : Bits m) : Fiber C :=
  (fun i => a i.val,fun i => b i.val)

theorem fiber_iff_eq (f : Fiber C) (a b : Bits m) :
    rowFiber C f a ∧ colFiber C f b ↔ fiberOf C a b=f := by
  cases f
  simp [rowFiber,colFiber,fiberOf]

def agrees (P : Finset (Fin m)) (x y : Bits m) : Prop :=
  ∀ i∈P, x i=y i

theorem same_row_fiber (f : Fiber C) (x y : Bits m)
    (hx : rowFiber C f x) (hy : rowFiber C f y) : agrees C.rowFixed x y := by
  intro i hi
  exact (congrFun hx ⟨i,hi⟩).trans (congrFun hy ⟨i,hi⟩).symm

theorem same_col_fiber (f : Fiber C) (x y : Bits m)
    (hx : colFiber C f x) (hy : colFiber C f y) : agrees C.colFixed x y := by
  intro i hi
  exact (congrFun hx ⟨i,hi⟩).trans (congrFun hy ⟨i,hi⟩).symm

def senderLocal {T : Type*} (u : Bits m → Bits m → T) : Prop :=
  ∀ a a' b b', agrees (C.pa∪C.ia) a a' → agrees (C.pb∪C.ib) b b' → u a b=u a' b'

def receiverLocal {T : Type*} (v : Bits m → Bits m → T) : Prop :=
  ∀ a a' b b', agrees ((Finset.univ \ C.pa)∪C.oa) a a' →
    agrees ((Finset.univ \ C.pb)∪C.ob) b b' → v a b=v a' b'

/-- On the literal rectangular fiber every legal sender value and
receiver coefficient depend on opposite physical axes. The choice of
orientation never changes which side is the computation's sender. -/
theorem fiber_views {S R : Type*} {u : Bits m → Bits m → S} {v : Bits m → Bits m → R}
    (hs : senderLocal C u) (hr : receiverLocal C v) (f : Fiber C) :
    if C.pb.card≤C.pa.card then
      (∀ a b b', colFiber C f b → colFiber C f b' → u a b=u a b') ∧
      (∀ a a' b, rowFiber C f a → rowFiber C f a' → v a b=v a' b)
    else
      (∀ a a' b, rowFiber C f a → rowFiber C f a' → u a b=u a' b) ∧
      (∀ a b b', colFiber C f b → colFiber C f b' → v a b=v a b') := by
  split_ifs with h
  · constructor
    · intro a b b' hb hb'
      apply hs a a b b' (fun _ _ => rfl)
      simpa only [Cut.colFixed,if_pos h] using same_col_fiber C f b b' hb hb'
    · intro a a' b ha ha'
      apply hr a a' b b _ (fun _ _ => rfl)
      simpa only [Cut.rowFixed,if_pos h] using same_row_fiber C f a a' ha ha'
  · constructor
    · intro a a' b ha ha'
      apply hs a a' b b _ (fun _ _ => rfl)
      simpa only [Cut.rowFixed,if_neg h] using same_row_fiber C f a a' ha ha'
    · intro a b b' hb hb'
      apply hr a a b b' (fun _ _ => rfl)
      simpa only [Cut.colFixed,if_neg h] using same_col_fiber C f b b' hb hb'

#print axioms Cut.fixed_card
#print axioms Cut.fiber_card
#print axioms fiber_iff_eq
#print axioms same_row_fiber
#print axioms same_col_fiber
#print axioms fiber_views
end
end V8CapacityUnified.U7
