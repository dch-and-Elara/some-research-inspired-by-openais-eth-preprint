import V8NativeMessageN6DState
import V8NativeMessageN6DSupport
import P5D1LiteralField

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6400000

/-! The direct list consists of actual complete child edge vectors,
with sign-independent weights in the integral word carrier. The
readout is genuine reduction of these integral words to the source
characteristic-two field, not a field-valued callback for a child. -/
namespace V8NativeMessage.N6D
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R11Blueprint J6R9Recursive J6R9PacketScopes
open P11FullPacking Paper5.D1Literal Paper5.HybridClosure
noncomputable section

def parityMap (f : ℤ[X]) : IntRing f 1 →+* NativeProbeRing.Residue f :=
  ((NativeProbeRing.residueMap 1 (by decide) f).comp
    (zeroCoordinate (NativeProbeRing.Scalar 1 f))).comp (reduce 1 f 1)

def parityOfWord (f : ℤ[X]) (hf : f.Monic) (p : ℕ)
    (x : Residue f 1 p) : NativeProbeRing.Residue f :=
  parityMap f (canonicalLift p f hf 1 x)

theorem parityOfWord_reduce (f : ℤ[X]) (hf : f.Monic) (p : ℕ) (positive : 1≤p)
    (x : IntRing f 1) :
    parityOfWord f hf p (reduce p f 1 x)=parityMap f x := by
  have h : (2 : IntRing f 1)^p ∣ canonicalLift p f hf 1 (reduce p f 1 x)-x := by
    apply (reduce_zero_iff p f hf 1 _).mp
    rw [map_sub,canonicalLift_spec,sub_self]
  have d := root_congruence_reduces_mod_two f hf 1 p positive h
  exact congrArg ((NativeProbeRing.residueMap 1 (by decide) f).comp
    (zeroCoordinate (NativeProbeRing.Scalar 1 f))) d

section General
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
variable {a : ℕ} (P : PhysicalPacking (dNetwork F cubic) a (Fin 64))
variable (i : Fin a) {f : ℤ[X]} (hf : f.Monic) (p₀ : ℕ)
variable {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
variable (p : ℕ) (hnil : (2 : Residue f 1 p)^p=0) (z : Residue f 1 p)
variable (β : Mode i p P.mask →₀ ℕ)

def integralList {n : ℕ} (g : Fin 64) (words : Fin n→AllState F cubic P i g)
    (weight : Fin n→IntRing f 1) (σ : W→Bool) : IntRing f 1 :=
  ∑ j, weight j * trueTerm F cubic P i g hf p₀ ht hv p hnil z β σ (words j)

theorem parity_integral_list {n : ℕ} (g : Fin 64) (words : Fin n→AllState F cubic P i g)
    (weight : Fin n→IntRing f 1) (σ : W→Bool) :
    parityMap f (integralList F cubic P i hf p₀ ht hv p hnil z β g words weight σ) =
      ∑ j, parityMap f (weight j * trueTerm F cubic P i g hf p₀ ht hv p hnil z β σ (words j)) := by
  rw [integralList,map_sum]

theorem word_of_integral_list {n : ℕ} (g : Fin 64) (words : Fin n→AllState F cubic P i g)
    (weight : Fin n→IntRing f 1) (σ : W→Bool) :
    reduce p f 1 (integralList F cubic P i hf p₀ ht hv p hnil z β g words weight σ) =
      ∑ j, reduce p f 1 (weight j) *
        reduce p f 1 (trueTerm F cubic P i g hf p₀ ht hv p hnil z β σ (words j)) := by
  simp only [integralList,map_sum,map_mul]

theorem parity_of_actual_full_child (positive : 1≤p) (g : Fin 64) (σ : W→Bool) :
    parityOfWord f hf p (reduce p f 1
      ((actualPacketHost P i ht hv p hnil z (oldRowFile F cubic f p₀ σ) β g).contract hf)) =
      ∑ x : AllState F cubic P i g, parityMap f
        (trueTerm F cubic P i g hf p₀ ht hv p hnil z β σ x) := by
  rw [parityOfWord_reduce f hf p positive,actual_child_is_complete_sum F cubic P i g hf p₀ ht hv p hnil z β σ,map_sum]

end General

section PhysicalLists
variable {V : Type} [Fintype V] [DecidableEq V]

def actualLists (F : Finset (TriVertex V×TriVertex V))
    (cubic : ∀ v, GraphCutMoments.degree F v=3)
    {a : ℕ} (P : PhysicalPacking (dNetwork F cubic) a (Fin 64))
    (i : Fin a) {f : ℤ[X]} (hf : f.Monic) (p₀ : ℕ)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hnil : (2 : Residue f 1 p)^p=0) (z : Residue f 1 p)
    (β : Mode i p P.mask →₀ ℕ)
    (len : Fin 64→ℕ) (words : ∀ g, Fin (len g)→AllState F cubic P i g)
    (weight : ∀ g, Fin (len g)→IntRing f 1) :
    DirectLists (NativeProbeRing.Residue f) (pinOwner F cubic P i) where
  len := len
  entry g j σ := parityMap f (weight g j * trueTerm F cubic P i g hf p₀ ht hv p hnil z β σ (words g j))
  supportWord g j := pattern F cubic P i g (words g j)
  locality := by
    intro g j σ τ same
    have h := trueTerm_group_local F cubic P i g hf p₀ ht hv p hnil z β σ τ (words g j)
      (fun v => same v.val v.property)
    exact congrArg (fun v => parityMap f (weight g j*v)) h
  onlyWord := by
    intro g j σ nonzero
    have h : trueTerm F cubic P i g hf p₀ ht hv p hnil z β σ (words g j)≠0 := by
      intro h
      exact nonzero (by rw [h,mul_zero,map_zero])
    exact trueTerm_support F cubic P i g hf p₀ ht hv p hnil z β σ (words g j) h

variable (F : Finset (TriVertex V×TriVertex V))
    (cubic : ∀ v, GraphCutMoments.degree F v=3)
    {a : ℕ} (P : PhysicalPacking (dNetwork F cubic) a (Fin 64))
    (i : Fin a) {f : ℤ[X]} (hf : f.Monic) (p₀ : ℕ)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hnil : (2 : Residue f 1 p)^p=0) (z : Residue f 1 p)
    (β : Mode i p P.mask →₀ ℕ)
    (len : Fin 64→ℕ) (words : ∀ g, Fin (len g)→AllState F cubic P i g)
    (weight : ∀ g, Fin (len g)→IntRing f 1)

theorem actualLists_received (positive : 1≤p) (g : Fin 64) (σ : TriVertex V→Bool) :
    groupValue (pinOwner F cubic P i) (actualLists F cubic P i hf p₀ ht hv p hnil z β len words weight) g σ =
      parityOfWord f hf p (reduce p f 1
        (integralList F cubic P i hf p₀ ht hv p hnil z β g (words g) (weight g) σ)) := by
  rw [parityOfWord_reduce f hf p positive,parity_integral_list]
  rfl

end PhysicalLists

#print axioms parityOfWord_reduce
#print axioms parity_integral_list
#print axioms word_of_integral_list
#print axioms parity_of_actual_full_child
#print axioms actualLists
#print axioms actualLists_received

end
end V8NativeMessage.N6D
