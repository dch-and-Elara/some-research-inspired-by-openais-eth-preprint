import J6R12RepackProvider
import J6R12RepackRootProbe
import J6R12BlueprintGuards
import J6R11Threshold

/-! Initial readiness is established for the actual planted root and the
same printed schedule as the native factory, not assumed for an
independently chosen call or layout. -/
namespace J6R12Repack
open scoped Polynomial
open J6Mesh P11FullPacking J6OrientedHost J1PPrinted
open J6ActiveRun J6R11Repack J6R12Blueprint J6R11Threshold
open J6R10Reachable J6R11Blueprint
variable {f : ℤ[X]} {ell : ℕ} {V : Type} [Fintype V]

noncomputable def exactJ6Selector (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m) :
    Selector (rootParams f ell m native) (sourceDelta (physicalSize m native)) :=
  actualJ6Selector _ _ p m l q T w mask hm hL (mesh_root_bits m native hn)

set_option maxHeartbeats 1900000 in
/-- The literal root edges, vertex degree, original creation precision and
all acquisition guards of the source. The numerical size threshold and
the initial gate degree cap remain visible hypotheses. -/
theorem exact_j6_root_ready (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
    (hfield : f.natDegree = 4*Nat.clog 2 (physicalSize m native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize m native))
    (hdeg : ∀ v, T.degree v ≤ sourceDelta (physicalSize m native)) :
    Ready (rootParams f ell m native) (sourceDelta (physicalSize m native))
      (physicalRootCall f ell p m l q T w) := by
  let s := physicalSize m native
  let c := physicalRootCall f ell p m l q T w
  obtain ⟨_,hCs,hu⟩ := printed_size_implies_numeric_guards s 2 (by decide) hsize
  have hacts := actual_printed_root_ready_size f ell p m l q native T w mask hm hL
    (Fintype.card_fin 64) hn (0:Fin 64)
  have hactive : (printedParams (f:=f) (ell:=ell) s).cutoff < c.edges := hacts.2.2.1
  have hdepth : 8^c.depth * c.edges ≤ 2*s := by
    change 8^0 * M m ≤ 2*s
    simpa only [pow_zero,one_mul] using (mesh_root_linear_bound m native hn)
  have hpacket := (source_packing_conditions s c.edges c.depth hu hactive).2.2
  have hpos : 1 ≤ stepL (Nat.clog 2 s) c.depth := by
    unfold stepL
    exact Nat.succ_le_of_lt (by positivity)
  have hmul : 2 ≤ 2*stepL (Nat.clog 2 s) c.depth := by
    simpa only [mul_one] using Nat.mul_le_mul_left 2 hpos
  have h2 : 2 ≤ sourceDelta s := hmul.trans hpacket
  exact ready_of_size s 2 c (by decide) hCs hfield hu hsize hactive hdepth
    (actual_root_edges f ell p m l q T w hm hL (Fintype.card_fin 64))
    (actual_root_good_degree f ell p m l q T w _ h2 hdeg)
    (actual_root_good_tags f ell p m l q T w)

#print axioms exactJ6Selector
#print axioms exact_j6_root_ready
end J6R12Repack
