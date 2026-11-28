import NativeProbeRing
import NativeInterpolation
import J9PrintedSchedule

/-! The actual finite receiving ring at positive precisions and arbitrary
additional truncation order ell. Binary-coordinate probe values are
mapped along the constant embedding into the V^ell quotient. -/
namespace J6ActiveInterpolation
open scoped BigOperators Polynomial
open Polynomial

abbrev Ring (p : ℕ) (f : ℤ[X]) (ell : ℕ) :=
  AdjoinRoot ((X : (NativeProbeRing.Scalar p f)[X])^ell)

noncomputable def scalarIn (p : ℕ) (f : ℤ[X]) (ell : ℕ) : NativeProbeRing.Scalar p f →+* Ring p f ell :=
  AdjoinRoot.of ((X : (NativeProbeRing.Scalar p f)[X])^ell)

noncomputable def node (p : ℕ) (f : ℤ[X]) (ell d : ℕ) (fit : d ≤ 2^f.natDegree)
    (i : Fin d) : Ring p f ell :=
  scalarIn p f ell (NativeProbeRing.probe p f
    (NativeProbeRing.chosenRep f.natDegree d fit i))

theorem node_pair_units (p : ℕ) (hp : 0 < p) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (ell d : ℕ) (fit : d ≤ 2^f.natDegree) (i j : Fin d) (hij : i ≠ j) :
    IsUnit (node p f ell d fit j - node p f ell d fit i) := by
  unfold node
  rw [← map_sub]
  exact (NativeProbeRing.chosenProbes_units p hp f hf hd d fit i j hij).map (scalarIn p f ell)

noncomputable def decoded {R : Type*} [CommRing R] {d : ℕ}
    (nodes samples : Fin (d+1) → R) : R[X] :=
  ∑ i, monomial i.val (NativeInterpolation.decode nodes samples i)

theorem decoded_exact {R : Type*} [CommRing R] {d : ℕ}
    (nodes : Fin (d+1) → R) (f : R[X]) (hdeg : f.natDegree ≤ d)
    (hunit : ∀ i j, i ≠ j → IsUnit (nodes j - nodes i)) :
    decoded nodes (fun i => f.eval (nodes i)) = f := by
  unfold decoded
  rw [NativeInterpolation.decode_eval f hdeg nodes hunit]
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => monomial j (f.coeff j)) (d+1)).trans
    (Polynomial.as_sum_range' f (d+1) (by omega)).symm

/-- The entire integral Taylor-local polynomial is recovered at
precision p_t from the printed count M(2L-1)+1 of binary probes.
This theorem takes the sample values of the stipulated polynomial.
The recursive evaluation that produces those values is separate. -/
theorem printed_probe_reconstruct (p : ℕ) (hp : 0 < p) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (ell M L : ℕ) (fit : J9PrintedSchedule.probeCount M L ≤ 2^f.natDegree)
    (F : (Ring p f ell)[X]) (hdeg : F.natDegree ≤ J9PrintedSchedule.degreeBound M L) :
    let x := node p f ell (J9PrintedSchedule.probeCount M L) fit
    decoded x (fun i => F.eval (x i)) = F := by
  dsimp only
  apply decoded_exact _ F hdeg
  exact node_pair_units p hp f hf hd ell _ fit

#print axioms node_pair_units
#print axioms decoded_exact
#print axioms printed_probe_reconstruct
end J6ActiveInterpolation