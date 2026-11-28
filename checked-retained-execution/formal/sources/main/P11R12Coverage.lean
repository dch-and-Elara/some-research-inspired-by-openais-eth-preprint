import P11R12Choice

namespace P11R12Coverage
open scoped Classical BigOperators
open P11FullPacking P11R12Choice OuterNodePacking
variable {K W : Type*} [LinearOrder K] [Fintype W] {a b : ℕ}

noncomputable def typeLoad (f : W → Cell (Fin a) K) (k : Key (Fin a) K) : ℕ :=
  ((Finset.univ : Finset W).filter (fun w => key (f w)=k)).card

theorem picked_le_typeLoad (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a)
    (side : W → Bool) (k : Key (Fin a) K) :
    (picked ω f cap side k).card ≤ typeLoad f k := by
  classical
  apply Finset.card_le_card
  intro w hw
  simpa [typeLoad] using (picked_exact ω f cap side k w).mp hw |>.1

theorem exact_sum_typeLoad [Fintype (Key (Fin a) K)] (f : W → Cell (Fin a) K) :
    (∑ k : Key (Fin a) K, typeLoad f k) = Fintype.card W := by
  classical
  symm
  simpa only [typeLoad, Finset.card_univ] using
    (Finset.card_eq_sum_card_fiberwise (f := key ∘ f)
      (s := (Finset.univ : Finset W)) (t := (Finset.univ : Finset (Key (Fin a) K)))
        (fun _ _ => Finset.mem_univ _))

theorem selected_in_unique_type (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a)
    (side : W → Bool) (w : W) :
    (∃! k : Key (Fin a) K, w ∈ picked ω f cap side k) ↔
      (seat ω f cap w).2 = endpointIndex a (side w) := by
  classical
  constructor
  · rintro ⟨k,hp,_⟩
    exact (Finset.mem_filter.mp hp).2.2
  · intro h
    refine ⟨key (f w), Finset.mem_filter.mpr ⟨Finset.mem_univ w, rfl, h⟩, ?_⟩
    intro k hk
    exact ((Finset.mem_filter.mp hk).2.1).symm

variable {E : Type*} [Fintype E] [Nonempty E] [DecidableEq E] [Fintype K]

omit [DecidableEq E] [Fintype K] in
/-- No unused seat becomes a real column, including at a padded endpoint.
Old vertex ownership comes from the same sampled injection. -/
theorem actual_cover (ω : Draw a b K) (f : E×Bool → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) :
    P11SourceGeometry.fullPortFiber Finset.univ (fun e s => seat ω f cap (e,s))
      (realSlot (seat ω f cap)) (vertexOwner (seat ω f cap)) :=
  real_fullPortFiber (seat ω f cap)

theorem actual_all_nonzero_shifts [DecidableEq (Page a b K)]
    (ω : Draw a b K) (f : E×Bool → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (t : ℤ) (ht : t≠0)
    (packets : Finset (Page a b K)) :
    min (P11SourceGeometry.seated Finset.univ
      (fun e s => seat ω f cap (e,s)) false).card
       (P11SourceGeometry.seated Finset.univ (fun e s => seat ω f cap (e,s)) true).card ≤
    (untouched Finset.univ (vertexOwner (seat ω f cap))
      (matchedColumns packets (realSlot (seat ω f cap)) (realSlot (seat ω f cap)) t)).card :=
  real_all_shifts (commonMask (masks ω)) f cap (orders ω) t ht packets

#print axioms picked_le_typeLoad
#print axioms exact_sum_typeLoad
#print axioms selected_in_unique_type
#print axioms actual_cover
#print axioms actual_all_nonzero_shifts
end P11R12Coverage
