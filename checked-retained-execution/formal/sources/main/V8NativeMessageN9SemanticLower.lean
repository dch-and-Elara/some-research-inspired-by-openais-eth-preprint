import V8NativeMessageN9Representative

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

namespace V8NativeMessage.Five
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Repack V8PooledMenu V8PooledMenu.FiveCopy
open V8PooledRange V8PooledRange.NativeOrigin
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}
variable (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (i : Fin (rootU V)) (chosen : Finset (FixedSites hu huM (rootA V) i))

abbrev FixedSemanticChildrenMenu (f : ℤ[X]) :=
  (t : ↥chosen) → SemanticChildAddress P hu huM t.val.val → Residue f 1 1

def semanticFixedChildren (probes : Probes V f) (hf : f.Monic) (s : V→Bool) :
    FixedSemanticChildrenMenu P hu huM i chosen f :=
  fun t q => rawParityChild P hu huM t.val.val probes hf s q.val.1 q.val.2

def extendTagged (menu : FixedChildrenMenu P hu huM i chosen f) :
    FixedSemanticChildrenMenu P hu huM i chosen f :=
  fun t q => menu t (relevantRepresentative P hu huM t.val.val q.val.1 q.val.2)

theorem semanticFixed_eq (probes : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree) (s : V→Bool) :
    semanticFixedChildren P hu huM i chosen probes hf s =
      extendTagged P hu huM i chosen (fixedChildren P hu huM i chosen probes hf s) := by
  funext t q
  exact N9_representative P hu huM t.val.val probes hf hd s q

/-- The full N9 communication bound is unchanged if distinct labels
denote the same function of all local Boolean assignments. -/
theorem N9_semantic_needs_bits {m b : ℕ} (M : Pairs G m) (T : Finset (Fin 64))
    (probes : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree)
    (cross : Crosses M P i T)
    (aux : (Fin m→Bool) → Fin b→Bool)
    (dec : (Fin m→Bool) → (Fin b→Bool) → FixedMenu P hu huM i (parityPrecision V) f →
      FixedSemanticChildrenMenu P hu huM i chosen f → ZMod 2)
    (correct : ∀ x y, dec y (aux x)
        (fixedNative P hu huM i (parityPrecision V) probes hf (activeSigns M x y))
        (semanticFixedChildren P hu huM i chosen probes hf (activeSigns M x y)) =
      (originCount G p (activeSigns M x y):ZMod 2)) :
    m ≤ (2^rootA V / 2^i.val) + chosen.card *
      (64+(12*wireSize V)/(2^rootA V / 2^i.val)) + b := by
  apply N9_needs_bits M P hu huM i T chosen probes hf hd cross aux
    (fun y a pool children => dec y a pool (extendTagged P hu huM i chosen children))
  intro x y
  rw [← semanticFixed_eq P hu huM i chosen probes hf hd]
  exact correct x y

#print axioms semanticFixed_eq
#print axioms N9_semantic_needs_bits
end
end V8NativeMessage.Five