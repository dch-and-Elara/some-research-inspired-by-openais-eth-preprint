import J6R51DispatchResident

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7700000
set_option maxRecDepth 2400

/-! The chosen replay destination is the actual installed physical mode
tape, not a stipulation that two supplied lists have the same order.
This view only provides the mathematical names already covered by
that tape's paid byte producer. -/
namespace J6R51Dispatch
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost
open J6R32ChildResidentTransfer J6R33GeneratedChildSite

variable {f : ℤ[X]} {ell q : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}

def residentLiteralTape (d : Ready S Δ c) (t : Center S c)
    {R : ChildResidents (S.levelBits c.depth) q}
    (H : ResidentReceipt (packing sel d) (centerIndex d t) (registerPrecision S c t) R) :
    SiteTape sel d t (q+1) :=
  ⟨H.modes,H.modesUnique,H.modesAll,R.raw.roster.weights,R.raw.roster.precision,H.weights,H.prec⟩

theorem resident_acted_exactly_destination_vector
    (d : Ready S Δ c) (w : NativeAddress (shape S Δ sel) c)
    {R : ChildResidents (S.levelBits c.depth) q}
    (H : ResidentReceipt (packing sel d) (centerIndex d w.1) (registerPrecision S c w.1) R) :
    H.modes.map (fun m=>siteTuple sel d w ((packet_mode_equiv (packing sel d).mask
          (centerIndex d w.1) (registerPrecision S c w.1)).symm m)) =
      vectorKey sel d w.1 (residentLiteralTape d w.1 H) w.2.2.1 := by
  unfold vectorKey residentLiteralTape
  exact List.map_congr_left (fun m _=>true_site_tuple_reads_encoded_variable d w m)

#print axioms residentLiteralTape
#print axioms resident_acted_exactly_destination_vector
end J6R51Dispatch

