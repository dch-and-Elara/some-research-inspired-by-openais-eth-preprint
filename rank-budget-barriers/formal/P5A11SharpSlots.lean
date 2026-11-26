import P5A11SharpDet
import Mathlib.Data.Finset.Sort

/-! Select the actual d most precise slots, not an assumed
per-layer allocation. Ties are broken by type-preserving node order. -/
namespace Paper5
open OrderDual
open scoped BigOperators Classical

theorem filter_take_sorted_length {A : Type*} (p : A→Bool) (xs : List A)
    (h : xs.Pairwise (fun a b=>p b=true→p a=true)) (d : ℕ) :
    ((xs.take d).filter p).length=min d (xs.filter p).length := by
  induction xs generalizing d with
  | nil => simp
  | cons a xs ih =>
    cases d with
    | zero => simp
    | succ d =>
      rcases List.pairwise_cons.mp h with ⟨hHead,hTail⟩
      cases hp : p a with
      | false =>
        have hz : xs.filter p=[] := by
          apply List.filter_eq_nil_iff.mpr
          intro b hb
          cases hpb : p b
          · simp
          · have hh := hHead b hb hpb
            rw [hp] at hh
            exact False.elim (Bool.noConfusion hh)
        have hzf : ((xs.take d).filter p).length=0 := by
          rw [ih hTail d,hz]
          simp
        simp [hp,hz,hzf]
      | true =>
        simp only [List.take_succ_cons,List.filter_cons,hp,if_true,List.length_cons]
        rw [ih hTail d,Nat.succ_min_succ]

theorem filtered_toFinset_card {A : Type*} [DecidableEq A] (xs : List A) (h : xs.Nodup)
    (p : A→Prop) [DecidablePred p] :
    (xs.toFinset.filter p).card=(xs.filter (fun x=>decide (p x))).length := by
  have hEq : xs.toFinset.filter p=(xs.filter (fun x=>decide (p x))).toFinset := by
    ext x
    simp
  rw [hEq]
  exact List.toFinset_card_of_nodup (h.filter _)

variable {T : Type*} [Fintype T] [LinearOrder T]

def precisionKey (P k : T→ℕ) (x : NodeOrder k) : ℕᵒᵈ ×ₗ (T ×ₗ ℕ) :=
  toLex (toDual (P x.1),nodeKey x)

omit [Fintype T] [LinearOrder T] in
theorem precisionKey_injective (P k : T→ℕ) : Function.Injective (precisionKey P k) := by
  intro x y h
  apply nodeKey_injective
  exact congrArg Prod.snd (congrArg ofLex h)

omit [Fintype T] in
theorem precisionKey_order (P k : T→ℕ) {x y : NodeOrder k}
    (h : precisionKey P k x ≤ precisionKey P k y) : P y.1≤P x.1 := by
  rcases lt_or_eq_of_le h with h|h
  · change Prod.Lex (· < ·) (· < ·) (toDual (P x.1), nodeKey x)
      (toDual (P y.1),nodeKey y) at h
    rw [Prod.lex_def] at h
    rcases h with h|⟨e,_⟩
    · exact Nat.le_of_lt h
    · exact (congrArg ofDual e).symm.le
  · rcases precisionKey_injective P k h with rfl
    exact le_rfl

noncomputable def slotsSorted (P k : T→ℕ) : List (NodeOrder k) :=
  letI : LinearOrder (NodeOrder k) := LinearOrder.lift' (precisionKey P k) (precisionKey_injective P k)
  Finset.univ.sort (· ≤ ·)

theorem slotsSorted_nodup (P k : T→ℕ) : (slotsSorted P k).Nodup := by
  unfold slotsSorted
  apply Finset.sort_nodup

theorem slotsSorted_covers (P k : T→ℕ) : (slotsSorted P k).toFinset=Finset.univ := by
  unfold slotsSorted
  apply Finset.sort_toFinset

theorem slotsSorted_priority (P k : T→ℕ) :
    (slotsSorted P k).Pairwise (fun x y=>P y.1≤P x.1) := by
  letI : LinearOrder (NodeOrder k) := LinearOrder.lift' (precisionKey P k) (precisionKey_injective P k)
  change (Finset.univ.sort (· ≤ ·) : List (NodeOrder k)).Pairwise (fun x y=>P y.1≤P x.1)
  have hh : List.Pairwise (· ≤ ·) (Finset.univ.sort (· ≤ ·) : List (NodeOrder k)) :=
    Finset.sort_sorted _ _
  exact hh.imp (fun h=>precisionKey_order P k h)

noncomputable def topSlots (P k : T→ℕ) (d : ℕ) : Finset (NodeOrder k) :=
  ((slotsSorted P k).take d).toFinset

set_option maxHeartbeats 6500000 in
theorem topSlots_filter_count (P k : T→ℕ) (d j : ℕ) :
    ((topSlots P k d).filter (fun x=>j<P x.1)).card =
      min d (Finset.univ.filter (fun x : NodeOrder k=>j<P x.1)).card := by
  let xs := slotsSorted P k
  let p (x : NodeOrder k) := decide (j<P x.1)
  have hp : xs.Pairwise (fun x y=>p y=true→p x=true) := by
    refine (slotsSorted_priority P k).imp ?_
    intro x y h hy
    exact decide_eq_true (lt_of_lt_of_le (of_decide_eq_true hy) h)
  unfold topSlots
  rw [filtered_toFinset_card _ ((slotsSorted_nodup P k).take : ((slotsSorted P k).take d).Nodup),
    filter_take_sorted_length p xs hp d,
    ←filtered_toFinset_card _ (slotsSorted_nodup P k),slotsSorted_covers]

#print axioms filter_take_sorted_length
#print axioms filtered_toFinset_card
#print axioms slotsSorted_priority
#print axioms topSlots_filter_count
end Paper5
