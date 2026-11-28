
import J9R18CompiledReadout
import Mathlib.Data.Fin.Tuple.Basic

/-! Literal local enumeration and an exact count of the local truth-
table visits charged by the compiled formulas. This is not a bit-machine
model and is not a cost bound for separate nonzero-probe slots. -/
namespace J9R18Compiled
open scoped BigOperators Classical
open J8Physical
set_option linter.unusedSectionVars false

/-- Executable vector enumeration. Its length is the local, not joined,
Boolean dimension. After renumbering one original vertex's ports by an
ordered incidence list, the ring accumulator simply folds this list. -/
def localBits : (n : ℕ) → List (Fin n → Bool)
  | 0 => [fun i => Fin.elim0 i]
  | n+1 => (localBits n).flatMap (fun x => [Fin.cons false x, Fin.cons true x])

theorem localBits_length (n : ℕ) : (localBits n).length = 2^n := by
  induction n with
  | zero => simp [localBits]
  | succ n ih =>
    simp only [localBits, List.length_flatMap, List.length_cons, List.length_nil, Nat.zero_add,
      List.map_const', List.sum_replicate, ih, pow_succ, nsmul_eq_mul, Nat.cast_id]

def scan {K : Type*} [AddMonoid K] (n : ℕ) (fn : (Fin n → Bool) → K) : K :=
  ((localBits n).map fn).sum

theorem scan_zero {K : Type*} [AddMonoid K] (fn : (Fin 0 → Bool) → K) :
    scan 0 fn = fn (fun i => Fin.elim0 i) := by simp [scan,localBits]

set_option maxHeartbeats 1800000 in
theorem scan_exact {K : Type*} [AddCommMonoid K] (n : ℕ) (fn : (Fin n → Bool) → K) :
    scan n fn = ∑ x : Fin n → Bool, fn x := by
  induction n with
  | zero =>
    rw [scan_zero]
    have h : (fun i : Fin 0 => (Fin.elim0 i : Bool)) = default := by
      funext i
      exact Fin.elim0 i
    rw [h]
    simp
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    let he : ((Fin (n+1) → Bool)) ≃ Bool × (Fin n→Bool) :=
      (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).symm
    have hs : ∑ x : Fin n→Bool, (fn (Fin.cons false x) + fn (Fin.cons true x)) =
        ∑ x : Fin (n+1)→Bool, fn x := by
      calc
        _ = (∑ t : Bool × (Fin n→Bool), fn (he.symm t)) := by
          rw [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
          first | rfl | apply add_comm
        _ = _ := he.symm.sum_comp fn
    rw [← hs,← ih]
    simp only [scan,localBits,List.map_flatMap,List.map_cons,List.map_nil]
    generalize localBits n = xs
    induction xs with
    | nil => rfl
    | cons z zs ih' => simp [List.flatMap_cons,add_assoc,ih']

theorem scan_local_table {I K : Type*} [Fintype I] [AddCommMonoid K]
    (n : ℕ) (numbering : Fin n≃I) (f : (I→Bool)→K) :
    scan n (fun x => f (x ∘ numbering.symm)) = ∑ y : I→Bool, f y := by
  let e : (Fin n→Bool) ≃ (I→Bool) :=
    ⟨fun x => x ∘ numbering.symm, fun y => y ∘ numbering,
      fun x => by funext q; simp, fun y => by funext q; simp⟩
  rw [scan_exact]
  exact e.sum_comp f

noncomputable section
variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

/-- Baseline, marked, or one unnormalised marginal: one indexed read
of every assignment in each local old (nonpin) column. The marked
unmatched scalar does not visit any old assignments. -/
def groupVisits (g : G) : ℕ := ∑ v : LocalColumn d g, 2^Fintype.card (LocalPort d v)

theorem groupVisits_bound (Δ : ℕ) (degree : ∀ v, Fintype.card (P v)≤Δ) (g : G) :
    groupVisits d g ≤ Fintype.card V * 2^Δ := by
  unfold groupVisits
  calc
    _ ≤ ∑ _v : LocalColumn d g, 2^Δ := Finset.sum_le_sum fun v _ =>
      Nat.pow_le_pow_right (by omega) (degree v.1)
    _ = Fintype.card (LocalColumn d g) * 2^Δ := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
    _ ≤ _ := Nat.mul_le_mul_right _ (Fintype.card_le_of_injective (f:=Subtype.val) Subtype.val_injective)

theorem oldTile_card_le_wire_card (a : S) :
    Fintype.card (OldTile d a) ≤ Fintype.card (Wire R) := by
  apply Fintype.card_le_of_injective (fun q : OldTile d a => ordinaryWire d q.1)
  intro q q' h
  exact Subtype.ext (Sum.inr.inj (d.column.symm.injective h))

theorem groupedTargets_card_le_wire_card (a : S) :
    (groupedTargets d a).card ≤ Fintype.card (Wire R) := by
  rw [← Fintype.card_coe]
  apply Fintype.card_le_of_injective (fun q : {q // q ∈ groupedTargets d a} =>
    (q.val.1.val,q.val.2))
  intro q q' h
  exact Subtype.ext (Prod.ext (Subtype.ext (congrArg Prod.fst h)) (congrArg (fun y : Wire R => y.2) h))

/-- Exact old-assignment visits of unshared evaluation of one first
coefficient: siblings, target masses, source baseline, and an old-port
numerator for each occupied tile port. Pins are read directly. -/
def orderVisits (a : S) : ℕ :=
  (∑ g ∈ ((Finset.univ : Finset G).erase (d.pinLabel a)).erase (d.rowLabel (pinWire d a).1),
    groupVisits d g) +
  (∑ _j ∈ groupedTargets d a, groupVisits d (d.rowLabel (pinWire d a).1)) +
  (Fintype.card (OldTile d a)+1) * groupVisits d (d.pinLabel a)

theorem orderVisits_bound (Δ : ℕ) (degree : ∀ v, Fintype.card (P v)≤Δ) (a : S) :
    orderVisits d a ≤
      (Fintype.card G + 2*Fintype.card (Wire R) + 1)*(Fintype.card V * 2^Δ) := by
  let B := Fintype.card V * 2^Δ
  let W := Fintype.card (Wire R)
  let t := ((Finset.univ : Finset G).erase (d.pinLabel a)).erase (d.rowLabel (pinWire d a).1)
  have hc : t.card ≤ Fintype.card G := Finset.card_le_univ _
  have b0 : (∑ g ∈ t, groupVisits d g) ≤ Fintype.card G * B := by
    calc
      _ ≤ ∑ _g ∈ t, B := Finset.sum_le_sum fun g _ => groupVisits_bound d Δ degree g
      _ = t.card*B := by rw [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
      _ ≤ _ := Nat.mul_le_mul_right B hc
  have b1 : (∑ _j ∈ groupedTargets d a, groupVisits d (d.rowLabel (pinWire d a).1)) ≤ W*B := by
    rw [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
    exact Nat.mul_le_mul (groupedTargets_card_le_wire_card d a) (groupVisits_bound d Δ degree _)
  have b2 : (Fintype.card (OldTile d a)+1)*groupVisits d (d.pinLabel a) ≤ (W+1)*B :=
    Nat.mul_le_mul (Nat.add_le_add_right (oldTile_card_le_wire_card d a) 1)
      (groupVisits_bound d Δ degree _)
  unfold orderVisits
  calc
    _ ≤ Fintype.card G * B + W*B + (W+1)*B := Nat.add_le_add (Nat.add_le_add b0 b1) b2
    _ = _ := by dsimp [B,W]; ring

/-- An uncached run computes a compiled oracle value and the public
scale/background for each order. Both can instead share the same
quantities from the first run; the factor two here does not assume this. -/
def compiledVisits : ℕ :=
  ∑ w : J9R17AllPins.Orders d, 2 * orderVisits d (J9R17AllPins.anchor d w.1)

theorem compiledVisits_bound (Δ : ℕ) (degree : ∀ v, Fintype.card (P v)≤Δ) :
    compiledVisits d ≤ 2*Fintype.card S *
      ((Fintype.card G + 2*Fintype.card (Wire R)+1)*(Fintype.card V*2^Δ)) := by
  let C := (Fintype.card G+2*Fintype.card (Wire R)+1)*(Fintype.card V*2^Δ)
  unfold compiledVisits
  calc
    _ ≤ ∑ _w : J9R17AllPins.Orders d, 2*C :=
      Finset.sum_le_sum fun w _ => Nat.mul_le_mul_left 2 (orderVisits_bound d Δ degree _)
    _ = _ := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,
        Fintype.card_congr (J9R17AllPins.orderPin d)]
      ring

#print axioms localBits_length
#print axioms scan_exact
#print axioms scan_local_table
#print axioms groupVisits_bound
#print axioms oldTile_card_le_wire_card
#print axioms groupedTargets_card_le_wire_card
#print axioms orderVisits_bound
#print axioms compiledVisits_bound

end
end J9R18Compiled
