import J6R9PacketTiles
import J6R14SpecializedBoxFactors
import J8PhysicalKernel

/-! The source feature is the same literal tile moment in the printed
J6 mode, including every real pin and ordinary column. Both evaluate
the very same physical wire assignment; no table or feature callback
is compared extensionally as a premise. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open J8Physical J8EndToEnd DyadicProbeCompiler
noncomputable section

variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [(v : V)→Fintype (P v)]
variable [DecidableEq Packet]

def tileWeight (u : S) (n : ℕ) (X : Wire R→Bool) (x : Wire R) : Source :=
  if SameTile d x (pinWire d u) then (ordinal d x:Source)^n * sourceBit (X x) else 0

set_option linter.unusedSectionVars false in
theorem same_tile_moment_literal (u : S) (b : Fin (Fintype.card (PinTile d u)))
    (X : Wire R→Bool) :
    J6R9PacketTiles.L (fun x => (d.seat x).1) (fun x => (d.seat x).2.val) 0
      (d.seat (pinWire d u)).1 ((d.seat (pinWire d u)).2.val%2) b.val X =
    integralFeature d u b
      (fun s => X (pinWire d s.val),localBitsFromWire d (d.pinLabel u) X) := by
  classical
  have hl : J6R9PacketTiles.L (fun x => (d.seat x).1) (fun x => (d.seat x).2.val) 0
      (d.seat (pinWire d u)).1 ((d.seat (pinWire d u)).2.val%2) b.val X =
      ∑ x : Wire R, tileWeight d u b.val X x := by
    unfold J6R9PacketTiles.L J6R9PacketTiles.columns
    rw [Finset.sum_filter]
    simp [tileWeight,SameTile,ordinal,sourceBit,J6R9PacketTiles.tile,J6R9PacketTiles.coord,J6R9PacketTiles.bit]
  have hc : (∑ x : Wire R, tileWeight d u b.val X x) =
      ∑ q : ColPort S P, tileWeight d u b.val X (d.column.symm q) :=
    Fintype.sum_equiv d.column _ _ (fun q => by rw [Equiv.symm_apply_apply])
  have hp : (∑ q : S, tileWeight d u b.val X (pinWire d q)) =
      ∑ q : PinTile d u, (ordinal d (pinWire d q.val):Source)^b.val * sourceBit (X (pinWire d q.val)) := by
    let p : S→Prop := fun q => SameTile d (pinWire d q) (pinWire d u)
    let w : S→Source := fun q => (ordinal d (pinWire d q):Source)^b.val * sourceBit (X (pinWire d q))
    calc
      _ = ∑ q, if p q then w q else 0 := by
        refine Finset.sum_congr rfl ?_
        intro q _
        by_cases h : p q <;> simp [p,w] at h ⊢ <;> simp [tileWeight,h]
      _ = _ := ((Finset.sum_filter (s:=Finset.univ) p w).symm).trans
        (Finset.sum_subtype (Finset.univ.filter p) (by simp [p]) w)
  have ho : (∑ q : Sigma P, tileWeight d u b.val X (ordinaryWire d q)) =
      ∑ q : OldTile d u, (ordinal d (ordinaryWire d q.val):Source)^b.val *
        sourceBit (X (ordinaryWire d q.val)) := by
    let p : Sigma P→Prop := fun q => SameTile d (ordinaryWire d q) (pinWire d u)
    let w : Sigma P→Source := fun q => (ordinal d (ordinaryWire d q):Source)^b.val * sourceBit (X (ordinaryWire d q))
    calc
      _ = ∑ q, if p q then w q else 0 := by
        refine Finset.sum_congr rfl ?_
        intro q _
        by_cases h : p q <;> simp [p,w] at h ⊢ <;> simp [tileWeight,h]
      _ = _ := ((Finset.sum_filter (s:=Finset.univ) p w).symm).trans
        (Finset.sum_subtype (Finset.univ.filter p) (by simp [p]) w)
  rw [hl,hc,Fintype.sum_sum_type]
  change (∑ q : S, tileWeight d u b.val X (pinWire d q)) +
    (∑ q : Sigma P, tileWeight d u b.val X (ordinaryWire d q)) = _
  rw [hp,ho,add_comm,integralFeature]
  congr 1
  exact Fintype.sum_equiv (pinEnumeration d u).symm _ _ (fun q => by
    rw [Equiv.apply_symm_apply]
    exact mul_comm _ _)

#print axioms same_tile_moment_literal
end
end J6R14SpecializedBox
