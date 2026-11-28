import J6R50NonModeScratchNative
import J6R24MeteredRecursionFrame
import A1R12Combine

/-! Read the scratch from the actual left-operand suffix of mulM.
Its second operand is the returned group word, not a freely
substituted buffer. The five selected convolution arrays do not
include nested U-gate scratch or a whole evaluator heap. -/
namespace J6R57LiveSpace
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R21Leaf
open J6R24MeteredRecursion J6R50NonModeScratch
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 6000000

variable {f : ℤ[X]} {p ell : ℕ}

def selectedVScratch (F : Frame f p) (x : UBlock F.words)
    (xs : List (UBlock F.words)) (right : Block F ell) : ℕ :=
  (encodeArrays scalarPayload (combineArrays (uGates F.hp F.words) x xs right.val)).length

theorem actual_mulM_retains_its_true_five_suffix_arrays
    (F : Frame f p) (hf : f.Monic) (left : Block F ell) (right : Meter (Block F ell))
    (pre : List (UBlock F.words)) (x : UBlock F.words) (xs : List (UBlock F.words))
    (whole : left.val=pre++(x::xs)) :
    (mulM F.hp ⟨left,0⟩ right).result.val=
      (convolve (uGates F.hp F.words) left.val right.result.val).result.drop ell ∧
    (combineArrays (uGates F.hp F.words) x xs right.result.val).getLast?=
      some (convolve (uGates F.hp F.words) (x::xs) right.result.val).result ∧
    selectedVScratch F x xs right.result≤(10*ell)*(f.natDegree*p) := by
  have h := native_v_convolution_scratch F.hp left right.result pre x xs whole
  rw [F.natDegree hf] at h
  exact ⟨rfl,combine_arrays_actual_output _ _ _ _,h⟩

#print axioms actual_mulM_retains_its_true_five_suffix_arrays
end J6R57LiveSpace
