import J6R11IntegralRetained

namespace J6R11Integral
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Repack J6R10Integral P11FullPacking
open J6ActiveUniqueness J6ActivePrintedHermite P1DyadicGrid

variable {E A B G : Type*} [LinearOrder G] [Fintype G] {a : ℕ}
variable [Fintype E] [Fintype A] [Fintype B]
variable {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

def parentAtlas (P : PhysicalPacking N a G) : Atlas E (Page a P.copies G) a :=
  physicalAtlas P.seat P.seat.injective

noncomputable def parentF (P : PhysicalPacking N a G)
    (file : EntryFile f ell N) (hf : f.Monic) : (RatRing f ell)[X] :=
  globalNetwork f ell (parentAtlas P) (rowProduct N file hf) (colProduct N file hf)

noncomputable def parentJet (P : PhysicalPacking N a G)
    (file : EntryFile f ell N) (hf : f.Monic) (t : ℤ) : (IntRing f ell)[X] :=
  integralNetwork f ell (parentAtlas P) t (rowProduct N file hf) (colProduct N file hf)

theorem parentF_degree (P : PhysicalPacking N a G) (file : EntryFile f ell N) (hf : f.Monic) :
    (parentF P file hf).natDegree ≤ J9PrintedSchedule.degreeBound (Fintype.card E) (2^a) :=
  network_degree f ell _ _ _

theorem parentF_local (P : PhysicalPacking N a G) (file : EntryFile f ell N) (hf : f.Monic)
    {t : ℤ} (ht : t ∈ grid a) :
    (parentJet P file hf t).map (embed f ell) =
      atNode (dyadicUnit a) (t:RatRing f ell) (parentF P file hf) :=
  network_embed f ell _ ht _ _

theorem parentF_origin (P : PhysicalPacking N a G) (file : EntryFile f ell N) (hf : f.Monic) :
    (parentF P file hf).eval 0 = embed f ell (trueContraction N file hf) := by
  rw [parentF,network_origin,trueContraction]
  congr 1
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun x _ => ?_)
  exact mixed_diagonal N file hf x

#print axioms parentF_degree
#print axioms parentF_local
#print axioms parentF_origin
end J6R11Integral
