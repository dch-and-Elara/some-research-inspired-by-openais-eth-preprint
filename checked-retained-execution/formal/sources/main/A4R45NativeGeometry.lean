import AAcquisitionCostSeats
import V8NativeMessageN7LiteralSupportFlat

namespace A4R45NativeGeometry
open AAcquisitionCost J6R9Recursive J6R10Repack P11FullPacking
open V8NativeMessage.N7LiteralSupport
set_option autoImplicit false
set_option warningAsError true

variable {E A B G : Type} {a : ℕ} [LinearOrder G] [Fintype G] {N : Network E A B}
variable (P : PhysicalPacking N a G)
variable (seat : E ≃ Physical a P.copies G) (same : ∀ w : E,P.seat w=seat w)
variable {K : Type} [CommRing K]
include same

theorem predecessor (r q : E) :
    wirePred seat r=some q ↔ Matches P (-1) r q := by
  rw [AAcquisitionCost.wirePred_spec]
  unfold AAcquisitionCost.packetOf AAcquisitionCost.positionOf Matches
  simp only [same]
  constructor
  · rintro ⟨h,eq⟩
    exact ⟨h.symm,by omega⟩
  · rintro ⟨h,eq⟩
    exact ⟨h.symm,by omega⟩

theorem read_actual [Fintype E] (X Y : E→Bool) (r : E) :
    wholeShiftBit P K (-1) (Sum.elim Y X) r =
      Acquisition.bit (K:=K) (Acquisition.readPredecessor (wirePred seat r) X) := by
  cases h : wirePred seat r with
  | none =>
    have none : ∀ q, ¬Matches P (-1) r q := by
      intro q fit
      have test := (predecessor P seat same r q).2 fit
      rw [h] at test
      cases test
    rw [literal_unmatched_port_zero P (-1) (Sum.elim Y X) r none]
    rfl
  | some q =>
    rw [literal_port_bit_unique P (-1) (Sum.elim Y X) r q ((predecessor P seat same r q).1 h)]
    rfl

theorem wire_lag [Fintype E] (X Y : E→Bool) (r : E) :
    LiteralPortCompiler.affine (Y r) ((-1:K)*wholeShiftBit P K (-1) (Sum.elim Y X) r) =
      Acquisition.lag (Y r) (-Acquisition.bit (Acquisition.readPredecessor (wirePred seat r) X)) := by
  rw [read_actual P seat same X Y r,neg_one_mul]
  cases Y r <;> rfl

#print axioms predecessor
#print axioms read_actual
#print axioms wire_lag
end A4R45NativeGeometry
