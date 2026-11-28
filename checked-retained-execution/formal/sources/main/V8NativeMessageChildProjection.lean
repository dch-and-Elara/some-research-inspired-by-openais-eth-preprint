import V8NativeMessagePacketAlgebra
import V8PooledMenuRoot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

/-! Single real child, not the complete product over all children.
The first-step semantic receipt uses the actual printed child network. -/
namespace V8NativeMessage
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
open J6R10RowIdentity J6R10PacketAssembly J6R11Blueprint
open V8PooledMenu
noncomputable section

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G]
  [Fintype G] {a : ℕ} {N : Network E A B} {f : ℤ[X]}
variable {S : Type*} [CommRing S]

def parityMap (h : (2:S)=0) : ZMod 2 →+* S :=
  TruncatedProbeMenu.residueCast (p:=1) (by simpa using h)

def parityBase : DenominatorBudget.TwoLocal →+* ZMod 2 :=
  J6ZeroTransport.reduceBase 1

theorem base_map_parity (p : ℕ) (h₂ : (2:Residue f 1 p)^p=0)
    (ψ : Residue f 1 p →+* S) (hc : (2:S)=0) :
    ψ.comp (J6ZeroTransport.reduceAt p h₂) = (parityMap hc).comp parityBase :=
  J6ZeroTransport.ringHom_unique _ _

def projectedChild (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (file : EntryFile f 1 N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (ψ : Residue f 1 p →+* S) : S :=
  ψ (reduce p f 1 ((actualPacketHost P i ht hv p h₂ z file β g).contract hf))

theorem projectedChild_eq (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (file : EntryFile f 1 N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (ψ : Residue f 1 p →+* S) :
    projectedChild P i ht hv p h₂ z file hf β g ψ =
      ∑ v : PhysicalState P i g,
        ψ (oldState P i g p file hf v) *
        ∏ k, ψ (actualPacket P i ht hv p h₂ z β g k v) := by
  rw [projectedChild,actualPacketHost_receive P i ht hv p h₂ z file β g hf,map_sum]
  exact Finset.sum_congr rfl (fun _ _ => by rw [map_mul,map_prod])

omit [Fintype E] [Fintype A] [Fintype B] in
theorem cross_parity_zero (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (ψ : Residue f 1 p →+* S) (hc : (2:S)=0) :
    (fun (r : E) (m : Mode i p P.mask) => ψ (scaledRow P.mask i ht hv p h₂ z (P.seat r) m)) =
    fun _ _ => 0 := by
  funext r m
  apply project_cross_zero ψ P.mask i ht hv p h₂ z (P.seat r) m (q:=1)
  · have := i.isLt
    omega
  · simpa using hc

/-- Any positive mode targeting the selected child erases that child
itself after parity projection. A positive mode targeting other
children does not enter this statement. -/
theorem target_child_zero (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (file : EntryFile f 1 N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (ψ : Residue f 1 p →+* S) (hc : (2:S)=0)
    (m : Mode i p P.mask) (hm : (childTarget P i m).1=g) (hmβ : β m≠0) :
    projectedChild P i ht hv p h₂ z file hf β g ψ=0 := by
  rw [projectedChild_eq]
  apply Finset.sum_eq_zero
  intro v _
  let k := (childTarget P i m).2
  have hk : childTarget P i m=(g,k) := Prod.ext hm rfl
  have hpacket : ψ (actualPacket P i ht hv p h₂ z β g k v)=0 := by
    rw [actualPacket,packet_map,cross_parity_zero P i ht hv p h₂ z ψ hc]
    exact J6RecursiveModes.packet_positive_target_zero _ _ _ _ _ _ _ _ _
      (filtered_nonzero β _ m hk hmβ)
  rw [Finset.prod_eq_zero (Finset.mem_univ k) hpacket,mul_zero]

def packetBase (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ) (g : G)
    (k : Page a P.copies G) (v : PhysicalState P i g) : ZMod 2 :=
  ∏ r ∈ actualRows (childBlock P i) g k, parityBase ((affineScaled P i t g v r).coeff 0)

omit [Fintype A] [Fintype B] in
theorem packet_projection (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (k : Page a P.copies G) (v : PhysicalState P i g)
    (ψ : Residue f 1 p →+* S) (hc : (2:S)=0)
    (hTarget : ∀ m, (childTarget P i m).1=g → β m=0) :
    ψ (actualPacket P i ht hv p h₂ z β g k v) =
      parityMap hc (packetBase P i t g k v) *
      ∏ m∈Finset.univ.filter (fun m => childSource P i m=(g,k)),
        ψ (stateMoment P i g p v m) ^ β m := by
  rw [actualPacket,packet_map,cross_parity_zero P i ht hv p h₂ z ψ hc]
  rw [packet_factor _ _ _ _ _ _ _ _ _ (fun m h => hTarget m (congrArg Prod.fst h))]
  unfold packetBase
  rw [map_prod]
  apply congrArg (· * _)
  refine Finset.prod_congr rfl (fun r _ => ?_)
  have he := (affineScaled_eval P i t g v r p h₂ z ψ).symm
  rw [hc,zero_mul,eval₂_at_zero,base_map_parity p h₂ ψ hc] at he
  exact he

omit [Fintype E] in
theorem binary_old_projection (P : PhysicalPacking N a G) (i : Fin a) (g : G) (p₀ p : ℕ)
    (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree)
    (flag : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool) (v : PhysicalState P i g)
    (h₂ : (2:Residue f 1 p)^p=0) (ψ : Residue f 1 p →+* S) (hc : (2:S)=0) :
    ψ (oldState P i g p (binaryFile f p₀ flag) hf v) =
      parityMap hc (parityBase (oldScalar P i g flag v)) := by
  rw [← oldScalar_map P i g p₀ p hp₀ hf hd flag v (J6ZeroTransport.reduceAt p h₂)]
  exact DFunLike.congr_fun (base_map_parity p h₂ ψ hc) _

#print axioms base_map_parity
#print axioms projectedChild_eq
#print axioms cross_parity_zero
#print axioms target_child_zero
#print axioms packet_projection
#print axioms binary_old_projection

end
end V8NativeMessage