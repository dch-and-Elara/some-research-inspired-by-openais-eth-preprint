import J6ActiveRun
import J6ActiveInterpolation
import J6ActiveNormalizer

/-! Finite active call: child slots (t,ζ,β,g) feed the printed
weighted mode sum, then unit-separated binary interpolation, then the
truncated local quotient. The only premise at this stage is the exact
identity of the grouped child values with the intended native sample. -/
namespace J6R9Recursive
open scoped BigOperators Polynomial
open Polynomial J6ActiveRun J6ActiveSchedule

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]

abbrev Box (f : ℤ[X]) (ell p : ℕ) := J6ActiveInterpolation.Ring p f ell

abbrev Responses (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host) :=
  ∀ w : Address S c, Box f ell (registerPrecision S c w.t)

abbrev ProofFit (S : Shape Host Mode) (f : ℤ[X]) (c : Call Host) :=
  J9PrintedSchedule.probeCount c.edges (2^S.levelBits c.depth) ≤ 2^f.natDegree

noncomputable def groupedSample (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ)
    (c : Call Host) (answers : Responses S f ell c) (t : Center S c) (z : Probe S c) :
    Box f ell (registerPrecision S c t) :=
  ∑ β : (J6RecursiveMenu.menu (registerPrecision S c t) (S.weight c t.val)),
    ∏ g : Fin 64, answers ⟨t,z,β,g⟩

noncomputable def sampleNode (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ)
    (c : Call Host) (fit : ProofFit S f c) (t : Center S c) (z : Probe S c) :
    Box f ell (registerPrecision S c t) :=
  J6ActiveInterpolation.node (registerPrecision S c t) f ell
    (J9PrintedSchedule.probeCount c.edges (2^S.levelBits c.depth)) fit z

noncomputable def decodedAt (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ)
    (c : Call Host) (fit : ProofFit S f c) (answers : Responses S f ell c) (t : Center S c) :
    (Box f ell (registerPrecision S c t))[X] :=
  J6ActiveInterpolation.decoded (sampleNode S f ell c fit t) (groupedSample S f ell c answers t)

theorem decodedAt_exact (S : Shape Host Mode) (f : ℤ[X]) (hf : f.Monic)
    (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (ell : ℕ) (c : Call Host) (fit : ProofFit S f c) (answers : Responses S f ell c)
    (t : Center S c) (hp : 0 < registerPrecision S c t)
    (localPoly : (Box f ell (registerPrecision S c t))[X])
    (hd : localPoly.natDegree ≤ J9PrintedSchedule.degreeBound c.edges (2^S.levelBits c.depth))
    (correct : ∀ z, groupedSample S f ell c answers t z =
      localPoly.eval (sampleNode S f ell c fit t z)) :
    decodedAt S f ell c fit answers t = localPoly := by
  unfold decodedAt
  rw [show groupedSample S f ell c answers t =
      (fun z => localPoly.eval (sampleNode S f ell c fit t z)) from funext correct]
  exact J6ActiveInterpolation.printed_probe_reconstruct (registerPrecision S c t) hp
    f hf hF ell c.edges (2^S.levelBits c.depth) fit localPoly hd

noncomputable def quotientAt (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ)
    (c : Call Host) (fit : ProofFit S f c) (answers : Responses S f ell c) (t : Center S c)
    (normal : (Box f ell (registerPrecision S c t))[X]) :
    (Box f ell (registerPrecision S c t))[X] :=
  J6ActiveNormalizer.quotientJet (order c.edges (S.levelWidth c.depth) t.val) normal
    (decodedAt S f ell c fit answers t)

theorem quotientAt_exact {A : Type*} [CommRing A] (S : Shape Host Mode)
    (f : ℤ[X]) (hf : f.Monic) (hF : 0 < f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (ell : ℕ) (c : Call Host) (fit : ProofFit S f c) (answers : Responses S f ell c)
    (t : Center S c) (hp : 0 < registerPrecision S c t)
    (reduce : A →+* Box f ell (registerPrecision S c t))
    (normal localPoly : A[X])
    (hd : localPoly.natDegree ≤ J9PrintedSchedule.degreeBound c.edges (2^S.levelBits c.depth))
    (correct : ∀ z, groupedSample S f ell c answers t z =
      (localPoly.map reduce).eval (sampleNode S f ell c fit t z)) :
    quotientAt S f ell c fit answers t (normal.map reduce) =
      (J6ActiveNormalizer.quotientJet (order c.edges (S.levelWidth c.depth) t.val)
        normal localPoly).map reduce := by
  unfold quotientAt
  rw [decodedAt_exact S f hf hF ell c fit answers t hp _ (natDegree_map_le.trans hd) correct]
  exact (J6ActiveNormalizer.quotientJet_map reduce _ normal localPoly).symm

#print axioms groupedSample
#print axioms decodedAt_exact
#print axioms quotientAt_exact
end J6R9Recursive