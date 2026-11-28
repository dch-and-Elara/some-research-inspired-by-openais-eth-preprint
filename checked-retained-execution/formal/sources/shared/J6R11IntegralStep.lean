import J6R11IntegralPrintedStep
import J6R10RepackPacket

/-! A literal active-point equality, from the parent integral Taylor
polynomial directly to the sum of the physically constructed child
networks. The old tensors here use their stored creation precision. -/
namespace J6R11Integral
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking P1DyadicGrid J6R9Recursive
open J6R10Repack J6R10Integral J6R9PacketScopes J6R9PacketChild J6R10RowAffine

variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

noncomputable def actualChildTruth (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t ≠ 0) (hv : padicValInt 2 t = i.val)
    (p : ℕ) (z : Box f ell p)
    (file : EntryFile f ell N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (g : G) : IntRing f ell :=
  let F := actualPacket P i ht hv p (box_two_nil p f ell) z β g
  trueContraction (child N (atGroup P i) (atPacket P) g)
    (compileChild N (atGroup P i) (atPacket P) g file p (compiledPacket P i g p F)) hf

theorem native_finite_step (P : PhysicalPacking N a G)
    (i : Fin a) {t : ℤ} (htM : t ∈ grid a) (ht : t ≠ 0) (hv : padicValInt 2 t = i.val)
    (p : ℕ) (hp : 0 < p) (z : Box f ell p)
    (file : EntryFile f ell N) (hf : f.Monic) :
    ((parentJet P file hf t).map (reduce p f ell)).eval z =
      ∑ β ∈ J6RecursiveMenu.menu p (weight i p P.mask), ∏ g,
        reduce p f ell (actualChildTruth P i ht hv p z file hf β g) := by
  classical
  refine (actual_parent_probe P i htM ht hv p hp z file hf).trans ?_
  refine Finset.sum_congr rfl (fun β _ => ?_)
  refine Finset.prod_congr rfl (fun g _ => ?_)
  exact (printed_child_realized P i ht hv p (box_two_nil p f ell) z file hf β g).symm

#print axioms actualChildTruth
#print axioms native_finite_step
end J6R11Integral
