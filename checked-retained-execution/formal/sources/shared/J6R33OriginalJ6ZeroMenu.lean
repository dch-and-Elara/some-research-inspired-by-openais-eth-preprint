import J6R33OriginalJ6Zero

/-! The direct branch's zero-coordinate request can be included in
a legal full binary probe set; it is not a forbidden exceptional
point of the native source ring. -/
namespace J6R33OriginalJ6
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R14ZeroMode J6R27PrescribedProbe
open NativeProbeRing J6ActiveInterpolation
set_option maxHeartbeats 3000000

def zeroPrefix (e d : ℕ) (i : Fin (d+1)) : Fin e→Bool := bitAt e i.val

theorem zero_prefix_distinct (e d : ℕ) (fit : d+1≤2^e) :
    Function.Injective (zeroPrefix e d) := by
  intro i j h
  have b := congrArg List.ofFn h
  change List.ofFn (bitAt e i.val)=List.ofFn (bitAt e j.val) at b
  rw [bit_word_exact,bit_word_exact] at b
  apply Fin.ext
  have out : bitsValue (encodeBits e i.val)=bitsValue (encodeBits e j.val) := congrArg bitsValue b
  rw [encodeBits_exact _ _ (i.isLt.trans_le fit),encodeBits_exact _ _ (j.isLt.trans_le fit)] at out
  exact out

theorem encode_zero (e : ℕ) : encodeBits e 0=List.replicate e false := by
  induction e with
  | zero => rfl
  | succ e ih => simp [encodeBits,ih,List.replicate_succ]

theorem zero_prefix_first (e d : ℕ) : zeroPrefix e d 0=(fun _=>false) := by
  have b : List.ofFn (zeroPrefix e d 0)=List.replicate e false := by
    change List.ofFn (bitAt e 0)=_
    rw [bit_word_exact]
    exact encode_zero e
  ext i
  have h : (List.ofFn (zeroPrefix e d 0))[i.val]?=(List.replicate e false)[i.val]? :=
    congrArg (fun L : List Bool=>L[i.val]?) b
  simpa only [List.getElem?_ofFn,i.isLt,dif_pos,List.getElem?_replicate,if_pos,Option.some.injEq] using h

theorem available_legal_zero_probe {f : ℤ[X]} (p ell d : ℕ) (hp : 0<p)
    (hf : f.Monic) (hF : 0<f.natDegree) [Fact (Irreducible (residuePoly f))]
    (fit : d+1≤2^f.natDegree) :
    let word := zeroPrefix f.natDegree d
    let z := fun i=>scalarIn p f ell (probe p f (word i))
    z 0=0 ∧ (∀ i j,i≠j→IsUnit (z j-z i)) := by
  let word := zeroPrefix f.natDegree d
  let z := fun i=>scalarIn p f ell (probe p f (word i))
  constructor
  · change z 0=0
    change scalarIn p f ell (probe p f (zeroPrefix f.natDegree d 0))=0
    rw [zero_prefix_first,actual_probe_zero,map_zero]
  · intro i j ne
    change IsUnit (scalarIn p f ell _-scalarIn p f ell _)
    rw [←map_sub]
    apply IsUnit.map (scalarIn p f ell)
    apply unit_of_residue p hp f hf
    rw [map_sub,sub_ne_zero]
    intro H
    exact ne ((zero_prefix_distinct f.natDegree d fit)
      (binary_residues_injective p hp f hf hF H.symm))

#print axioms zero_prefix_distinct
#print axioms zero_prefix_first
#print axioms available_legal_zero_probe
end J6R33OriginalJ6
