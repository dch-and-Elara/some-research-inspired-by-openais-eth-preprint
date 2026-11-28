import J6R14ZeroModeFallback
import J6R12RepackLiteralRun

/-! Put the fallback on the very same printed, oriented J6 root, using
the same selector and the same list of odd active centres. -/
namespace J6R14ZeroMode
open scoped Classical Polynomial BigOperators
open Polynomial J6ActiveRun J6R9Recursive J6OrientedHost J6Mesh P11FullPacking
open J6R12Blueprint J6R11Blueprint J6R10Reachable J6R11Repack J6R12Repack J1PPrinted
noncomputable section

abbrev literalDegree (m native : ℕ) : ℕ :=
  J9PrintedSchedule.degreeBound (M m) (2^stepA (Nat.clog 2 (physicalSize m native)) 0)

theorem literal_degree_eq (m native : ℕ) (h : native ≤ m) :
    literalDegree m native = M m*(2*L m-1) := by
  unfold literalDegree
  rw [mesh_root_bits m native h]
  rfl

variable {f : ℤ[X]} {ell : ℕ} {V : Type} [Fintype V]

set_option maxHeartbeats 4000000 in
theorem literal_fallback_at_odd_center (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
    (hfield : f.natDegree = 4*Nat.clog 2 (physicalSize m native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize m native))
    (hdeg : ∀ v, T.degree v ≤ sourceDelta (physicalSize m native))
    (hf : f.Monic) (hF : 0 < f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (W : Prescribed f (literalDegree m native)) (j : Fin (m+1)) :
    let sel := exactJ6Selector (f:=f) (ell:=ell) p m l q native T w mask hm hL hn
    let d := exact_j6_root_ready (f:=f) (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg
    let t := oddRootCenter f ell p m l q native T w hn j
    fallback sel d t hf W = zeroRuntime sel d t hf 0 := by
  dsimp only
  exact fallback_exact _ _ _ (exact_j6_root_bounds (f:=f) m native hfield hsize)
    (exact_j6_root_stable (f:=f) (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg)
    hf hF W

theorem literal_prescribed_addresses (m native : ℕ) (h : native ≤ m) :
    Nat.card (Fin (m+1) × Fin (literalDegree m native+1) × Fin 64) =
      (m+1)*((M m*(2*L m-1)+1)*64) := by
  rw [literal_degree_eq m native h,Nat.card_prod,Nat.card_prod,Nat.card_fin,Nat.card_fin,Nat.card_fin]

#print axioms literal_degree_eq
#print axioms literal_fallback_at_odd_center
#print axioms literal_prescribed_addresses
end
end J6R14ZeroMode
