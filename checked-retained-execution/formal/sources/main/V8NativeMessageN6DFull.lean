import V8NativeMessageN6DConcrete

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5100000

/-! The co-location branch on the actual full child product, with
no direct-list hypothesis. This is not a separate estimate on how
the child contraction is acquired. -/
namespace V8NativeMessage.N6D
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Blueprint J6R9Recursive J6R9PacketScopes P11FullPacking
open Paper5.HybridClosure Paper5.D1Literal
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀ v, GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
local notation "F" => replacedEdges E baseCubic
local notation "hF" => replaced_cubic E baseCubic loopless
variable {a : ℕ}
variable (P : PhysicalPacking (dNetwork (replacedEdges E baseCubic)
  (replaced_cubic E baseCubic loopless)) a (Fin 64)) (i : Fin a)
variable {f : ℤ[X]} (hf : f.Monic)
variable {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
variable (p : ℕ) (positive : 1≤p) (z : Residue f 1 p)
variable (β : ↥(J6RecursiveMenu.menu p (J6R10RowAffine.weight i p P.mask)))
local notation "p₀" => 4*Fintype.card (TriVertex V)+1
local notation "hnil" => J6R10Integral.box_two_nil p f 1
local notation "own" => pinOwner F hF P i

def fullPacketWord (g : Fin 64) (σ : TriVertex V→Bool) : Residue f 1 p :=
  reduce p f 1
    ((actualPacketHost P i ht hv p hnil z (oldRowFile F hF f p₀ σ) β.val g).contract hf)

def fullPacketParity (g : Fin 64) (σ : TriVertex V→Bool) : NativeProbeRing.Residue f :=
  parityOfWord f hf p (fullPacketWord E baseCubic loopless P i hf ht hv p z β g σ)

theorem fullPacketParity_local :
    UsesOnly own (fullPacketParity E baseCubic loopless P i hf ht hv p z β) := by
  intro g σ τ same
  unfold fullPacketParity fullPacketWord
  rw [oldRow_child_group_local F hF p₀ P i ht hv p hnil z β.val g σ τ
    (fun u => same u.val u.property)]

include positive in
theorem fullPacketParity_complete (g : Fin 64) (σ : TriVertex V→Bool) :
    fullPacketParity E baseCubic loopless P i hf ht hv p z β g σ =
      ∑ x : AllState F hF P i g, parityMap f
        (trueTerm F hF P i g hf p₀ ht hv p hnil z β.val σ x) := by
  unfold fullPacketParity fullPacketWord
  rw [parity_of_actual_full_child F hF P i hf p₀ ht hv p hnil z β.val positive g σ]
  refine Finset.sum_congr (Finset.ext (fun x => by simp only [Finset.mem_univ])) ?_
  exact fun _ _ => rfl

theorem actual_full_product_colocation [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (correct : ∀ σ, (∏ g, fullPacketParity E baseCubic loopless P i hf ht hv p z β g σ)=
       UD E baseCubic (NativeProbeRing.Residue f) σ) :
    ∀ e : E, own (seat E baseCubic e false)=own (seat E baseCubic e true) :=
  exterior_pair_same_group E baseCubic own (fullPacketParity E baseCubic loopless P i hf ht hv p z β)
    (fullPacketParity_local E baseCubic loopless P i hf ht hv p z β) correct

#print axioms fullPacketParity_local
#print axioms fullPacketParity_complete
#print axioms actual_full_product_colocation
end
end V8NativeMessage.N6D
