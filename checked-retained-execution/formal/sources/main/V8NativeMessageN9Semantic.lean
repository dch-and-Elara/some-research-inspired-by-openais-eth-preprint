import V8NativeMessageN9
import V8NativeMessageChildSemantic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

namespace V8NativeMessage.Five
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Integral J6R10Repack V8PooledMenu
open V8PooledMenu.FiveCopy V8PooledRange V8PooledRange.NativeOrigin
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}

/-- Same actual child output at a raw printed address, with no change to
the mode menu when semantic rather than tagged eligibility is tested. -/
def rawParityChild (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (t : Site V) (probes : Probes V f) (hf : f.Monic) (s : V → Bool)
    (q : Address P hu huM t) (g : Fin 64) : Residue f 1 1 :=
  projectedChild (S:=Residue f 1 1) P (rootIndex hu huM t) (nonzero_site hu huM t) (rootIndex_val hu huM t)
    (high t) (box_two_nil (high t) f 1) (readProbe f (high t) (probes.word t q.probeIdx))
    (file f G p s) hf q.beta g (observe f (high t) 1 (precision_fits hu huM (parityPrecision V) t))

theorem N9_same_raw_child (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (t : Site V) (probes : Probes V f) (hf : f.Monic) (s : V → Bool)
    (q : ChildAddress P hu huM t) :
    actualChildMenu P hu huM t probes hf s q=rawParityChild P hu huM t probes hf s q.val.1 q.val.2 := rfl

theorem N9_semantic_native (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (t : Site V) (probes : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree) (s : V → Bool)
    (q : Address P hu huM t) (g : Fin 64)
    (eligible : RestrictedSemantic P (rootIndex hu huM t) q.beta g) :
    rawParityChild P hu huM t probes hf s q g =
      decodeChild P (rootIndex hu huM t) q.beta g
        (encodeChildren P (rootIndex hu huM t) t.val (flags G p s)) (parityBox f) := by
  exact N9_semantic_child P (rootIndex hu huM t)
    (nonzero_site hu huM t) (rootIndex_val hu huM t) (high t) (box_two_nil (high t) f 1)
    _ (rootPrec V) (rootPrec_pos V) hf hd (flags G p s) q.beta g _ (parityBox f) eligible

#print axioms N9_same_raw_child
#print axioms N9_semantic_native
end
end V8NativeMessage.Five