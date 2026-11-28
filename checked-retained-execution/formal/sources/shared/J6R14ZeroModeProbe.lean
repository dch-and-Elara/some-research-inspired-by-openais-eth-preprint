import NativeProbeRing
import J6ActiveInterpolation

/-! A prescribed source probe set is a listing of distinct actual binary
words, not necessarily the canonical prefix. At positive precision these
lifts have pairwise unit differences in the actual receiving ring. -/
namespace J6R14ZeroMode
open scoped Classical Polynomial
open Polynomial NativeProbeRing J6ActiveInterpolation
noncomputable section

structure Prescribed (f : ℤ[X]) (D : ℕ) where
  word : Fin (D+1) → Fin f.natDegree → Bool
  distinct : Function.Injective word
  excludesZero : ∀ j, word j ≠ fun _ => false

def prescribedNode {f : ℤ[X]} {D : ℕ} (W : Prescribed f D) (p ell : ℕ)
    (j : Fin (D+1)) : Ring p f ell :=
  scalarIn p f ell (probe p f (W.word j))

theorem prescribed_units {f : ℤ[X]} {D : ℕ} (W : Prescribed f D) (p ell : ℕ)
    (hp : 0 < p) (hf : f.Monic) (hF : 0 < f.natDegree)
    [Fact (Irreducible (residuePoly f))] :
    ∀ i j, i ≠ j → IsUnit (prescribedNode W p ell j - prescribedNode W p ell i) := by
  intro i j h
  unfold prescribedNode
  rw [← map_sub]
  apply IsUnit.map (scalarIn p f ell)
  apply unit_of_residue p hp f hf
  rw [map_sub,sub_ne_zero]
  intro he
  exact h (W.distinct ((binary_residues_injective p hp f hf hF) he.symm))

theorem actual_probe_zero (p : ℕ) (f : ℤ[X]) :
    probe p f (fun _ => false) = 0 := by
  simp [probe,binaryPoly]

theorem prescribed_not_zero {f : ℤ[X]} {D : ℕ} (W : Prescribed f D) (p ell : ℕ)
    (hp : 0 < p) (hℓ : 0 < ell) (hf : f.Monic) (hF : 0 < f.natDegree)
    (i : Fin (D+1)) : prescribedNode W p ell i ≠ 0 := by
  let q : (Scalar p f)[X] := X^ell
  have hq : q.eval₂ (RingHom.id _) 0 = 0 := by simp [q,zero_pow hℓ.ne']
  let out : Ring p f ell →+* Scalar p f := AdjoinRoot.lift (RingHom.id _) 0 hq
  have hout (a : Scalar p f) : out (scalarIn p f ell a) = a := by
    change AdjoinRoot.lift (RingHom.id (Scalar p f)) 0 hq (AdjoinRoot.of q a) = a
    simp
  intro he
  have hz := congrArg out he
  rw [prescribedNode,hout,map_zero] at hz
  rw [← actual_probe_zero p f] at hz
  exact W.excludesZero i ((binary_residues_injective p hp f hf hF)
    (congrArg (residueMap p hp f) hz))

#print axioms prescribedNode
#print axioms prescribed_units
#print axioms actual_probe_zero
#print axioms prescribed_not_zero
end
end J6R14ZeroMode
