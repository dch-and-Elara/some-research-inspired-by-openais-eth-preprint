import J6ProfileMenu

namespace J6PacketFold
open scoped Classical BigOperators

variable {R M K G : Type*} [CommRing R] [Fintype M] [Fintype K]

/-- Inside a single retained group, repack source moments by the physical
packet that owns each mode, then multiply that packet's target coefficient. -/
theorem fold_source_by_packet (source : M → G × K) (g : G)
    (moment : M → R) (coeff : K → R) :
    (∏ m ∈ Finset.univ.filter (fun m => (source m).1 = g), moment m) *
      (∏ k, coeff k) =
    ∏ k, coeff k * ∏ m ∈ Finset.univ.filter (fun m => source m = (g,k)), moment m := by
  classical
  let S := (Finset.univ : Finset M).filter (fun m => (source m).1 = g)
  have h : ∏ k, ∏ m ∈ S.filter (fun m => (source m).2 = k), moment m =
      ∏ m ∈ S, moment m :=
    Finset.prod_fiberwise S (fun m => (source m).2) moment
  change (∏ m ∈ S, moment m) * _ = _
  rw [← h, mul_comm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  have he : S.filter (fun m => (source m).2 = k) =
      Finset.univ.filter (fun m => source m = (g,k)) := by
    ext m
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
  change coeff k * (∏ m ∈ S.filter (fun m => (source m).2 = k), moment m) = _
  rw [he]
#print axioms fold_source_by_packet
end J6PacketFold
