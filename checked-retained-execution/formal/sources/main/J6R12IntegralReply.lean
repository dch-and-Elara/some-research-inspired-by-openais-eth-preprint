import J6R12BlueprintPacket
import J6R11IntegralStep

/-! The actual child's host contains the very entry file in the physical
source theorem. Identify its exact odd-local contraction before
reducing it; no oracle-produced child value is assumed. -/
namespace J6R12Integral
open scoped Classical BigOperators Polynomial
open Polynomial J6R11Blueprint J6R11Integral J6R10Integral
open J6R9Recursive J6R10Repack P11FullPacking J6R9PacketScopes

variable {f : ℤ[X]} {ell : ℕ}
variable {E A B K G : Type} [Fintype E] [Fintype A] [Fintype B] [Fintype K] [DecidableEq G]

set_option maxHeartbeats 2200000 in
theorem physicalChildHost_contract (N : Network E A B) (group : A ⊕ B → G)
    (packet : E → K) (g : G) (oldFile : EntryFile f ell N) (p : ℕ)
    (packetValue : ∀ k : K, (PacketPorts N group packet g k → Bool) → Residue f ell p)
    (hf : f.Monic) :
    (physicalChildHost N group packet g oldFile p packetValue).contract hf =
      trueContraction (child N group packet g)
        (compileChild N group packet g oldFile p packetValue) hf := by
  unfold physicalChildHost physicalHost PhysicalHost.contract trueContraction
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun x _ => ?_)
  exact Finset.prod_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun _ _ => rfl)

section Physical
variable {H : Type} [LinearOrder H] [Fintype H]
variable {a : ℕ} {N : Network E A B}

theorem actualPacketHost_truth (P : PhysicalPacking N a H) (i : Fin a) {t : ℤ}
    (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p : ℕ)
    (z : Box f ell p) (file : EntryFile f ell N) (hf : f.Monic)
    (β : Mode i p P.mask →₀ ℕ) (g : H) :
    (actualPacketHost P i ht hv p (box_two_nil p f ell) z file β g).contract hf =
      actualChildTruth P i ht hv p z file hf β g :=
  physicalChildHost_contract N (atGroup P i) (atPacket P) g file p _ hf
end Physical

#print axioms physicalChildHost_contract
#print axioms actualPacketHost_truth
end J6R12Integral
