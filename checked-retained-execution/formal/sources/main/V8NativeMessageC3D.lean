import V8NativeMessageReceive
import V8NativeMessageChildProjection
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

/-! D operand of C3: public separate scalar lifts of the real individual
hi-precision child views remain rank one on the common finite cut.
This statement does not replace the lift of the completed product. -/
namespace V8NativeMessage
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes J6R10Integral
open V8PooledMenu J6R11Blueprint

noncomputable section
section Native
variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G]
  [Fintype G] {a : ℕ} {N : Network E A B} {f : ℤ[X]} {S : Type*} [CommRing S]

theorem high_child_local (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hp : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (p₀ : ℕ) (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree)
    (flag flag' : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (ψ : Residue f 1 p →+* S)
    (agrees : ∀ (u : A ⊕ B), atGroup P i u=g → ∀ q, flag u q=flag' u q) :
    projectedChild P i ht hv p hp z (binaryFile f p₀ flag) hf β g ψ =
      projectedChild P i ht hv p hp z (binaryFile f p₀ flag') hf β g ψ := by
  rw [projectedChild_eq,projectedChild_eq]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have old : oldScalar P i g flag v=oldScalar P i g flag' v := by
    unfold oldScalar
    refine Finset.prod_congr rfl (fun u _ => ?_)
    rw [agrees u.val u.property]
  rw [← oldScalar_map P i g p₀ p hp₀ hf hd flag v (J6ZeroTransport.reduceAt p hp),
    ← oldScalar_map P i g p₀ p hp₀ hf hd flag' v (J6ZeroTransport.reduceAt p hp),old]

def highChildRaw (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hp : (2:Residue f 1 p)^p=0) (z : Residue f 1 p) (file : EntryFile f 1 N) (hf : f.Monic)
    (β : Mode i p P.mask→₀ℕ) (g : G) : Residue f 1 p :=
  reduce p f 1 ((actualPacketHost P i ht hv p hp z file β g).contract hf)

theorem high_child_raw_local (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hp : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (p₀ : ℕ) (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree)
    (flag flag' : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool)
    (β : Mode i p P.mask →₀ ℕ) (g : G)
    (agrees : ∀ (u : A ⊕ B), atGroup P i u=g → ∀ q, flag u q=flag' u q) :
    highChildRaw P i ht hv p hp z (binaryFile f p₀ flag) hf β g =
      highChildRaw P i ht hv p hp z (binaryFile f p₀ flag') hf β g := by
  unfold highChildRaw
  rw [actualPacketHost_receive P i ht hv p hp z _ β g hf,
    actualPacketHost_receive P i ht hv p hp z _ β g hf]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have old : oldScalar P i g flag v=oldScalar P i g flag' v := by
    unfold oldScalar
    refine Finset.prod_congr rfl (fun u _ => ?_)
    rw [agrees u.val u.property]
  rw [← oldScalar_map P i g p₀ p hp₀ hf hd flag v (J6ZeroTransport.reduceAt p hp),
    ← oldScalar_map P i g p₀ p hp₀ hf hd flag' v (J6ZeroTransport.reduceAt p hp),old]

end Native
namespace Five
open V8PooledMenu.FiveCopy V8PooledRange V8PooledRange.NativeOrigin

variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}
variable (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
  (i : Fin (rootU V)) (T : Finset (Fin 64))

abbrev HighChildView (f : ℤ[X]) :=
  (t : FixedSites hu huM (rootA V) i) →
    Address P hu huM t.val → Residue f 1 (high t.val)

def highChildView (probes : Probes V f) (hf : f.Monic) (s : V → Bool) (g : Fin 64) :
    HighChildView P hu huM i f := fun t q =>
  highChildRaw P (rootIndex hu huM t.val) (nonzero_site hu huM t.val)
    (rootIndex_val hu huM t.val) (high t.val) (box_two_nil (high t.val) f 1)
    (readProbe f (high t.val) (probes.word t.val q.probeIdx)) (file f G p s) hf q.beta g

theorem highChildView_local (probes : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree)
    (s s' : V → Bool) (g : Fin 64) (eq : ∀ v, switchGroup P (physIndex i) v=g → s v=s' v) :
    highChildView P hu huM i probes hf s g=highChildView P hu huM i probes hf s' g := by
  funext t q
  unfold highChildView file
  apply high_child_raw_local _ _ _ _ _ _ _ _ (rootPrec_pos V) hf hd
  intro u hu₀ a
  apply flags_only_switch
  intro v he
  apply eq v
  change atGroup P (physIndex i) (switchVertex v)=g
  rw [← actual_index hu huM i t,← he]
  exact hu₀

variable {K : Type*} [CommRing K]
variable (probes : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree)
  (lift : Fin 64 → HighChildView P hu huM i f → K)

include hd in
theorem C3_D_separate_lifts (x : RowWords P i T) (y : ColWords P i T) :
    (∏ g, lift g (highChildView P hu huM i probes hf (signs P i T x y) g)) =
      (∏ g∈T, lift g (highChildView P hu huM i probes hf (rowFill P i T x) g)) *
      (∏ g∈Tᶜ, lift g (highChildView P hu huM i probes hf (colFill P i T y) g)) := by
  rw [← Finset.prod_mul_prod_compl T
    (fun g => lift g (highChildView P hu huM i probes hf (signs P i T x y) g))]
  apply congrArg₂ (· * ·)
  · refine Finset.prod_congr rfl (fun g hg => ?_)
    apply congrArg (lift g)
    apply highChildView_local P hu huM i probes hf hd
    intro v hv
    have h : switchGroup P (physIndex i) v∈T := hv ▸ hg
    simp only [signs,rowFill,dif_pos h]
  · refine Finset.prod_congr rfl (fun g hg => ?_)
    apply congrArg (lift g)
    apply highChildView_local P hu huM i probes hf hd
    intro v hv
    have hg' := Finset.mem_compl.mp hg
    have h : switchGroup P (physIndex i) v∉T := hv ▸ hg'
    simp only [signs,colFill,dif_neg h]

#print axioms high_child_local
#print axioms high_child_raw_local
#print axioms highChildView_local
#print axioms C3_D_separate_lifts
end Five
end
end V8NativeMessage