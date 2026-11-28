import P5OuterCenterFiber
import P5HybridClosureTriangle

set_option warningAsError true
set_option maxHeartbeats 6000000
namespace Paper5.OuterCenters
open scoped BigOperators Classical Polynomial
open P11FullPacking J6R10Repack HybridDUncloned HybridClosure

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v = 3)
variable {G : Type} [LinearOrder G] [Fintype G] {a : ℕ}
local notation "NW" => network F cubic

private def slot (P : PhysicalPacking NW a G) (v : W) : ℕ :=
  (P.seat (pinWire F v)).2.val

private def edgeSlot (P : PhysicalPacking NW a G) (K : ℕ)
    (v : {v : W // ¬ robustPin F cubic P K v}) : Fin (2 * K) :=
  if h : slot F cubic P v.val < K then ⟨slot F cubic P v.val, by omega⟩
  else ⟨K+(slot F cubic P v.val+K-2^a), by
    have hs : slot F cubic P v.val < 2^a := (P.seat (pinWire F v.val)).2.isLt
    have hn := v.property
    change ¬ (K ≤ slot F cubic P v.val ∧ slot F cubic P v.val + K < 2^a) at hn
    omega⟩

theorem exceptions_packet_bound (P : PhysicalPacking NW a G) (K : ℕ) :
    (Finset.univ.filter fun v => ¬ robustPin F cubic P K v).card * 2^a ≤
      (6 * Fintype.card (Wire F)) * K := by
  classical
  let f : {v : W // ¬ robustPin F cubic P K v} → Page a P.copies G × Fin (2*K) :=
    fun v => ((P.seat (pinWire F v.val)).1, edgeSlot F cubic P K v)
  have hf : Function.Injective f := by
    intro v w h
    have hpage := congrArg Prod.fst h
    have hslot := congrArg (fun (p : Page a P.copies G × Fin (2*K)) => p.2.val) h
    have hv := v.property
    have hw := w.property
    change ¬ (K ≤ slot F cubic P v.val ∧ slot F cubic P v.val + K < 2^a) at hv
    change ¬ (K ≤ slot F cubic P w.val ∧ slot F cubic P w.val + K < 2^a) at hw
    have hs : slot F cubic P v.val = slot F cubic P w.val := by
      change (edgeSlot F cubic P K v).val = (edgeSlot F cubic P K w).val at hslot
      unfold edgeSlot at hslot
      by_cases hv' : slot F cubic P v.val < K
      · by_cases hw' : slot F cubic P w.val < K
        · rw [dif_pos hv',dif_pos hw'] at hslot
          exact hslot
        · rw [dif_pos hv',dif_neg hw'] at hslot
          change slot F cubic P v.val = K + (slot F cubic P w.val + K - 2^a) at hslot
          omega
      · by_cases hw' : slot F cubic P w.val < K
        · rw [dif_neg hv',dif_pos hw'] at hslot
          change K + (slot F cubic P v.val + K - 2^a) = slot F cubic P w.val at hslot
          omega
        · rw [dif_neg hv',dif_neg hw'] at hslot
          change K + (slot F cubic P v.val + K - 2^a) = K + (slot F cubic P w.val + K - 2^a) at hslot
          omega
    apply Subtype.ext
    apply real_pin_injective F
    apply P.seat.injective
    exact Prod.ext hpage (Fin.ext hs)
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_subtype, Fintype.card_prod, Fintype.card_fin] at hcard
  have hp := physical_packet_count P
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hp
  calc
    _ ≤ (Fintype.card (Page a P.copies G) * (2*K)) * 2^a := Nat.mul_le_mul_right _ hcard
    _ = (Fintype.card (Page a P.copies G) * 2^a) * (2*K) := by ac_rfl
    _ ≤ (3 * Fintype.card (Wire F)) * (2*K) := Nat.mul_le_mul_right _ hp
    _ = _ := by ring

theorem budget_from_printed_packets (P : PhysicalPacking NW a (Fin 64)) (K : ℕ)
    (hK : 1024*K ≤ 2^a) (ha : 512*a < Fintype.card W) :
    2 * ((bad (robustPin F cubic P K) (pinOwner F cubic P)).card) < Fintype.card W := by
  classical
  have hcard := bad_card_bound (robustPin F cubic P K) (pinOwner F cubic P)
  rw [Fintype.card_fin, Fintype.card_fin] at hcard
  have hex := exceptions_packet_bound F cubic P K
  rw [physical_wire_count F cubic] at hex
  let B := (Finset.univ.filter fun v => ¬ robustPin F cubic P K v).card
  let n := Fintype.card W
  have hB : 1024*B ≤ 60*n := by
    change B*2^a ≤ (6*(10*n))*K at hex
    apply Nat.le_of_mul_le_mul_right (c := 2^a) _ (pow_pos (by decide) _)
    calc
      (1024*B)*2^a = 1024*(B*2^a) := by ring
      _ ≤ 1024*((6*(10*n))*K) := Nat.mul_le_mul_left _ hex
      _ = (60*n)*(1024*K) := by ring
      _ ≤ (60*n)*2^a := Nat.mul_le_mul_left _ hK
  change _ ≤ B+2*a*64 at hcard
  change 512*a < n at ha
  change _ < n
  omega

variable {V : Type} [Fintype V] [DecidableEq V]

private def swapBits (E : Finset (V × V)) : (E × Bool) ≃ (E × Bool) where
  toFun t := (t.1,!t.2)
  invFun t := (t.1,!t.2)
  left_inv := by rintro ⟨e,b⟩; cases b <;> rfl
  right_inv := by rintro ⟨e,b⟩; cases b <;> rfl

noncomputable def exteriorMate (E : Finset (V × V)) (c : ∀ v,GraphCutMoments.degree E v=3) :
    TriVertex V ≃ TriVertex V :=
  ((exteriorPort E c).symm.trans (swapBits E)).trans (exteriorPort E c)

theorem exteriorMate_edge (E : Finset (V × V)) (c : ∀ v,GraphCutMoments.degree E v=3)
    (x : TriVertex V) :
    (x,exteriorMate E c x) ∈ replacedEdges E c ∨
      (exteriorMate E c x,x) ∈ replacedEdges E c := by
  classical
  obtain ⟨⟨e,b⟩,rfl⟩ := (exteriorPort E c).surjective x
  cases b
  · left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, by
      simp [outerEdge,exteriorMate,swapBits]⟩
  · right
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, by
      simp [outerEdge,exteriorMate,swapBits]⟩

#print axioms exceptions_packet_bound
#print axioms budget_from_printed_packets
#print axioms exteriorMate_edge
end Paper5.OuterCenters

