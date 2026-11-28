
import J6R24LegalLayoutTensor
import J6RecursiveCrossing

/-! The completed zero-mode polynomial on the new legal packing uses
the very same local kernel and typed EntryFile. This is a fresh raw
register identity for the new layout, not a cross-layout equality. -/
namespace J6R24LegalLayout
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6Mesh J6OrientedHost J6R9Recursive
open J6R11Repack J6R10Integral J6R11Integral J6R15PlantedIdentity
set_option maxHeartbeats 19000000
set_option maxRecDepth 1800
set_option linter.unusedSectionVars false

theorem odd_axis_available (m : ℕ) : 0<a m := by
  have h := address_index m 0
  by_contra hf
  have e : a m=0 := by omega
  have hi := h.2.2.2
  rw [J6Mesh.L,e,pow_zero] at hi
  have h0 := h.1
  omega

def oddAxis (m : ℕ) : Fin (a m) := ⟨0,odd_axis_available m⟩

theorem completed_stable_zero_expansion {V : Type} [Fintype V]
    (f : ℤ[X]) (ell base p m l q width : ℕ)
    (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (ha : a m≤width) (cap : K m*L m≤2^width)
    (hf : f.Monic) (hbase : 0<base) (hp : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (i : J6Recovery.Addr m) :
    let C := deterministicLegal ha cap w hm hL
    let P := stableRootPacking m l q width T w hm hL ha cap
    (J6R14ZeroMode.polynomial P (oddAxis m) (index m i:ℤ) p
      (rootEntryFile f ell base T w) hf).eval 0 =
      J6ZeroTransport.reduceAt p (box_two_nil p f ell) (chartScalar m l q T w hm hL C i) := by
  let P := stableRootPacking m l q width T w hm hL ha cap
  have nz : (index m i:ℤ)≠0 := by
    exact_mod_cast (address_index m i).1.ne'
  have val : padicValInt 2 (index m i:ℤ)=(oddAxis m).val :=
    (J6RecursiveCrossing.odd_center_valuation m i).2.1
  exact (zero_eq_parentJet P (oddAxis m) (centre_in_grid m i) nz val p hp
    (rootEntryFile f ell base T w) hf).trans
      (stable_root_at_odd_zero f ell base p m l q width T w hm hL ha cap hf hbase hF hℓ i)

#print axioms odd_axis_available
#print axioms completed_stable_zero_expansion
end J6R24LegalLayout
