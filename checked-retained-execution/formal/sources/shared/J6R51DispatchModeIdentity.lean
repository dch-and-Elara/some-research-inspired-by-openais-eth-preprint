import J6R25PreparedSupplyModeDecode
import J6R17ModeTapeCodec

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000

/-! Same actual typed mode before and after the packet-side projection
used by the native R25 child compiler. This is a semantic identity,
not an implementation of the typed projection. -/
namespace J6R51Dispatch
open scoped Polynomial
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R17ModeTape

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}

theorem true_site_tuple_reads_encoded_variable
    (d : Ready S Δ c) (w : NativeAddress (shape S Δ sel) c)
    (m : NativeRoster sel d w.1) :
    siteTuple sel d w ((packet_mode_equiv (packing sel d).mask (centerIndex d w.1)
      (registerPrecision S c w.1)).symm m) =
        w.2.2.1.val ((site_mode_equiv sel d w.1).symm m) := by
  let E := Equiv.cast (modeAt_eq S Δ sel d w.1)
  let z := (packet_mode_equiv (packing sel d).mask (centerIndex d w.1)
      (registerPrecision S c w.1)).symm m
  let F := Finsupp.embDomain E.toEmbedding w.2.2.1.val
  change F z=w.2.2.1.val (E.symm z)
  calc
    F z = F (E (E.symm z)) := congrArg F (E.apply_symm_apply z).symm
    _ = _ := Finsupp.embDomain_apply _ _ _

#print axioms true_site_tuple_reads_encoded_variable
end J6R51Dispatch

