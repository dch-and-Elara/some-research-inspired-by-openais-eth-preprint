import J6R12RepackSelection
import J6R11RepackRootHost
import J6R11RepackRootAdmissible

/-! At the distinguished exact J6 root we keep the repaired planting
instead of relabelling and accidentally changing its special physical
mesh. The root layout still has the source's minimum rounded padding. -/
namespace J6R12Repack
open scoped Classical Polynomial
open J6R10Repack J6R11Repack J6R11Blueprint P11FullPacking J6OrientedHost
open J6Mesh J6RecursiveOrientation
variable {S V : Type} [LinearOrder S] [Fintype S] [Fintype V]

noncomputable def actualSelectedRoot (f : ℤ[X]) (ell p m l q : ℕ)
    (T : Plant V m q) (w : Fin (a m) → S)
    (mask : MaskFamily (a m) (K m) S) (hm : m≤K m) (hL : 2*l=L m)
    (hS : Fintype.card S=64) :
    Selected (physicalRootCall f ell p m l q T w).host (a m) S :=
  ⟨rootPacking m l q T w mask hm hL hS,root_minimal_rounding m l q T w mask hm hL hS⟩

noncomputable def actualSelectedAtSchedule (f : ℤ[X]) (ell p m l q : ℕ)
    (T : Plant V m q) (w : Fin (a m) → S)
    (mask : MaskFamily (a m) (K m) S) (hm : m≤K m) (hL : 2*l=L m)
    (hS : Fintype.card S=64) (bits : ℕ → ℕ) (hbits : bits 0=a m) :
    Selected (physicalRootCall f ell p m l q T w).host
      (bits (physicalRootCall f ell p m l q T w).depth) S :=
  hbits.symm ▸ actualSelectedRoot f ell p m l q T w mask hm hL hS

theorem actualSelected_seat (f : ℤ[X]) (ell p m l q : ℕ)
    (T : Plant V m q) (w : Fin (a m) → S)
    (mask : MaskFamily (a m) (K m) S) (hm : m≤K m) (hL : 2*l=L m)
    (hS : Fintype.card S=64) (e : Wire w m (K m) l) :
    (actualSelectedRoot f ell p m l q T w mask hm hL hS).packing.seat e =
      oriented mask w m l hm hL e := rfl

theorem actual_root_good_degree (f : ℤ[X]) (ell p m l q : ℕ)
    (T : Plant V m q) (w : Fin (a m) → S)
    (Δ : ℕ) (hΔ : 2 ≤ Δ) (hT : ∀ v, T.degree v ≤ Δ) :
    GoodDegree (physicalRootCall f ell p m l q T w).host Δ :=
  root_max_degree T w Δ hΔ hT

theorem actual_root_good_tags (f : ℤ[X]) (ell p m l q : ℕ)
    (T : Plant V m q) (w : Fin (a m) → S) :
    GoodTags (physicalRootCall f ell p m l q T w).host p := by
  intro v
  have hv : ((physicalRootCall f ell p m l q T w).host.file v).created = p :=
    actual_root_tags f ell p m l q T w v
  omega

#print axioms actualSelectedRoot
#print axioms actualSelectedAtSchedule
#print axioms actualSelected_seat
#print axioms actual_root_good_degree
#print axioms actual_root_good_tags
end J6R12Repack
