import J6R12BlueprintPacket

namespace J6R11Blueprint
open scoped Polynomial BigOperators Classical
open Polynomial J6R10Repack P11FullPacking J6R9PacketScopes J6R9Recursive
variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
    [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

set_option maxHeartbeats 2200000 in
theorem actualPacketHost_receive (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p : ℕ)
    (hnil : (2:Residue f ell p)^p=0) (z : Residue f ell p)
    (old : EntryFile f ell N) (β : Mode i p P.mask →₀ ℕ) (g : G) (hf : f.Monic) :
    reduce p f ell ((actualPacketHost P i ht hv p hnil z old β g).contract hf) =
      ∑ v : PhysicalState P i g, oldState P i g p old hf v *
        ∏ k, actualPacket P i ht hv p hnil z β g k v := by
  have h := actual_physical_child P i ht hv p hnil z old hf β g
  refine Eq.trans ?_ (Eq.trans h ?_)
  · apply congrArg (reduce p f ell)
    unfold actualPacketHost physicalChildHost physicalHost PhysicalHost.contract trueContraction
    refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun x _ => ?_)
    exact Finset.prod_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun _ _ => rfl)
  · exact Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun _ _ => rfl)

#print axioms actualPacketHost_receive
end J6R11Blueprint