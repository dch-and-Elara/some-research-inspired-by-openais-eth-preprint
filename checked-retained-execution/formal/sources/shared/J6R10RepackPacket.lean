import J6R10RepackPacketScope
import J6R11RowFormula

namespace J6R10Repack
open scoped Polynomial BigOperators Classical
open P11FullPacking J6R9PacketScopes J6R9PacketChild J6R9Recursive J6R10RowPrinted
variable {E A B G : Type*} [LinearOrder G] [Fintype G] {a : ℕ}
variable {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

set_option maxHeartbeats 1200000 in
/-- Identifies a child value appearing in the printed mode sum with the
truth of the literal new network, not merely with a postulated local
function. The child starts at precisely the receiving precision p. -/
theorem printed_child_realized [Fintype E] [Fintype A] [Fintype B]
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ} (ht : t≠0)
    (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hnil : (2:Residue f ell p)^p=0) (z : Residue f ell p)
    (oldFile : EntryFile f ell N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (g : G) :
    let F := actualPacket P i ht hv p hnil z β g
    reduce p f ell (trueContraction (child N (atGroup P i) (atPacket P) g)
      (compileChild N (atGroup P i) (atPacket P) g oldFile p (compiledPacket P i g p F)) hf) =
    reconstructedChild (fun e => P.seat e) (fun e => P.seat e) P.mask i ht hv p hnil z
      (fun g' v => oldState P i g' p oldFile hf v) β g := by
  try dsimp only
  refine (actual_physical_child P i ht hv p hnil z oldFile hf β g).trans ?_
  rw [J6R11RowFormula.reconstructedChild_formula]
  unfold J6R11RowFormula.canonicalChild J6RecursiveModes.child
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun v _ => ?_)
  congr 1
  refine Finset.prod_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun k _ => ?_)
  unfold actualPacket
  congr 1
  all_goals first
    | exact Subsingleton.elim _ _
    | funext m
      by_cases h : source P.mask i m = g
      · simp only [stateMoment,J6R10RowPrinted.sourceGP,dif_pos h]
      · simp only [stateMoment,J6R10RowPrinted.sourceGP,dif_neg h]
    | ext e; simp [J6R10PacketAssembly.actualRows,childBlock,J6R10RowPrinted.block]

#print axioms printed_child_realized
end J6R10Repack
