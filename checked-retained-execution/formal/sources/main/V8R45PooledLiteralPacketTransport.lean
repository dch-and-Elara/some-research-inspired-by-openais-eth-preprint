import V8R45PooledLiteralDispatch
import J6R12IntegralClosedCore

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option maxRecDepth 2700

/-! Proof-index changes between the paper's root parameters and the
recursive root cannot change the physical host, stored file, or exponent. -/
namespace V8R45PooledLiteral
open scoped Classical Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketScopes J6R11Blueprint
noncomputable section
variable {E A B : Type} [Fintype E] [Fintype A] [Fintype B]
variable {N : Network E A B} {f : ℤ[X]} {a a' p p' : ℕ}

def movePacking (h : a=a') (P : PhysicalPacking N a (Fin 64)) :
    PhysicalPacking N a' (Fin 64) :=
  cast (congrArg (fun a => PhysicalPacking N a (Fin 64)) h) P

def moveMode (ha : a=a') (hp : p=p') (P : PhysicalPacking N a (Fin 64)) (i : Fin a) :
    Mode i p P.mask ≃ Mode (Fin.cast ha i) p' (movePacking ha P).mask := by
  subst a'
  subst p'
  exact Equiv.refl _

omit [Fintype E] [Fintype A] [Fintype B] in
theorem moveMode_weight (ha : a=a') (hp : p=p') (P : PhysicalPacking N a (Fin 64))
    (i : Fin a) (m : Mode i p P.mask) :
    J6R10RowAffine.weight (Fin.cast ha i) p' (movePacking ha P).mask (moveMode ha hp P i m) =
      J6R10RowAffine.weight i p P.mask m := by
  subst a'
  subst p'
  rfl

omit [Fintype E] [Fintype A] [Fintype B] in
theorem same_mode_mem_after_transport (ha : a=a') (hp : p=p')
    (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (β : Mode i p P.mask →₀ ℕ) :
    Finsupp.embDomain (moveMode ha hp P i).toEmbedding β ∈
      J6RecursiveMenu.menu p' (J6R10RowAffine.weight (Fin.cast ha i) p' (movePacking ha P).mask) ↔
    β ∈ J6RecursiveMenu.menu p (J6R10RowAffine.weight i p P.mask) := by
  subst a'
  subst p'
  have hβ : Finsupp.embDomain (moveMode rfl rfl P i).toEmbedding β = β := by
    ext m
    exact Finsupp.embDomain_apply (Equiv.refl _).toEmbedding β m
  rw [hβ]
  rfl

theorem actual_packet_host_transport (ha : a=a') (hp : p=p')
    (P : PhysicalPacking N a (Fin 64)) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (z : Residue f 1 p) (F : EntryFile f 1 N) (β : Mode i p P.mask →₀ ℕ)
    (g : Fin 64) :
    actualPacketHost (movePacking ha P) (Fin.cast ha i) ht (hv.trans rfl)
      p' (J6R10Integral.box_two_nil p' f 1) (cast (congrArg (Residue f 1) hp) z) F
      (Finsupp.embDomain (moveMode ha hp P i).toEmbedding β) g =
    actualPacketHost P i ht hv p (J6R10Integral.box_two_nil p f 1) z F β g := by
  subst a'
  subst p'
  have hβ : Finsupp.embDomain (moveMode rfl rfl P i).toEmbedding β = β := by
    ext m
    exact Finsupp.embDomain_apply (Equiv.refl _).toEmbedding β m
  rw [hβ]
  rfl

#print axioms moveMode_weight
#print axioms same_mode_mem_after_transport
#print axioms actual_packet_host_transport
end
end V8R45PooledLiteral