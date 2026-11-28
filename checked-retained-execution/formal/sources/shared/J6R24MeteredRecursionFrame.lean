import J6R21AncestorIntegrated
import J6R23ScheduleWeightPass

/-! Machine registers shared by all parent and child arithmetic. The
coefficient-modulus frame is prepared; converting an encoded leaf into
that shared frame uses the checked and paid R19 canonical resize. -/
namespace J6R24MeteredRecursion
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime J6R9Recursive
open J6R19Retained J6R22Active J6R21Ancestor J6R18ChildWrite

structure Frame (f : ℤ[X]) (p : ℕ) where
  hp : 0<p
  words : List (Word p)
  sizePos : 0<words.length
  exactMod : Modulus p hp words=NativeProbeRing.liftPoly p f

abbrev Bank (f : ℤ[X]) := ∀ p : ℕ, 0<p→Frame f p

abbrev Block {f : ℤ[X]} {p : ℕ} (F : Frame f p) (ell : ℕ) := UVBlock F.words ell

noncomputable def Frame.decode {f : ℤ[X]} {p ell : ℕ} (F : Frame f p) (x : Block F ell) :
    Box f ell p :=
  boxTransport F.exactMod (uvRead F.hp F.words ell x)

theorem Frame.natDegree {f : ℤ[X]} {p : ℕ} (hf : f.Monic) (F : Frame f p) :
    F.words.length=f.natDegree :=
  size_of_monic_words F.hp hf F.exactMod

def convertLeaf {f : ℤ[X]} {ell : ℕ} {hf : f.Monic}
    {c : J6ActiveRun.Call (J6R11Blueprint.PhysicalHost f ell)}
    (D : EncodedLeaf hf c) (F : Frame f c.prec) : Meter (Block F ell) :=
  let R := D.run
  let v := resizeUV ((size_of_monic_words D.hp hf D.modulus).trans (F.natDegree hf).symm) R.result
  ⟨v.result,R.steps+v.steps+4⟩

theorem convertLeaf_receipt {f : ℤ[X]} {ell : ℕ} {hf : f.Monic}
    (he : 0<f.natDegree) {c : J6ActiveRun.Call (J6R11Blueprint.PhysicalHost f ell)}
    (D : EncodedLeaf hf c) (F : Frame f c.prec) :
    F.decode (convertLeaf D F).result=castBox D.modulus (uvRead D.hp D.fw ell D.run.result) ∧
    D.run.steps≤(convertLeaf D F).steps ∧
    (convertLeaf D F).steps≤D.run.steps+boxFee f.natDegree ell c.prec c.prec+4 := by
  let Rus := resizeUV ((size_of_monic_words D.hp hf D.modulus).trans (F.natDegree hf).symm)
    D.run.result
  have h := native_resizeUV D.hp F.hp hf he D.modulus F.exactMod D.run.result
  refine ⟨?_,?_,?_⟩
  · change boxTransport F.exactMod (uvRead F.hp F.words ell Rus.result)=_
    rw [boxTransport_cast,h.1]
    exact canonicalLift_spec c.prec f hf ell _
  · change _≤D.run.steps+Rus.steps+4
    omega
  · change D.run.steps+Rus.steps+4≤_
    have h' : Rus.steps≤boxFee f.natDegree ell c.prec c.prec := h.2
    omega

#print axioms Frame.natDegree
#print axioms convertLeaf_receipt
end J6R24MeteredRecursion

