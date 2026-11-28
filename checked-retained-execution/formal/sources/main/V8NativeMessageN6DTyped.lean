import V8NativeMessageN6DConcrete

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5200000

/-! Literal state/list theorem at a legal fixed high mode and finite
sample in the real four-clone carrier, independent of the recursive
executor's particular way of enumerating the prescribed addresses. -/
namespace V8NativeMessage.N6D
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R9Recursive J6R9PacketScopes P11FullPacking
open Paper5.HybridClosure
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀ v, GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
local notation "F" => replacedEdges E baseCubic
local notation "hF" => replaced_cubic E baseCubic loopless
variable {a : ℕ}
variable (P : PhysicalPacking (dNetwork (replacedEdges E baseCubic)
  (replaced_cubic E baseCubic loopless)) a (Fin 64))
variable (i : Fin a) {f : ℤ[X]} (hf : f.Monic)
variable {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
variable (p : ℕ) (positive : 1≤p) (z : Residue f 1 p)
variable (β : ↥(J6RecursiveMenu.menu p (J6R10RowAffine.weight i p P.mask)))
variable (len : Fin 64→ℕ)
variable (words : ∀g, Fin (len g)→AllState (replacedEdges E baseCubic)
  (replaced_cubic E baseCubic loopless) P i g)
variable (weight : ∀ g, Fin (len g)→IntRing f 1)
local notation "p₀" => 4*Fintype.card (TriVertex V)+1
local notation "hnil" => J6R10Integral.box_two_nil p f 1
local notation "own" => pinOwner F hF P i

def physicalListWord (g : Fin 64) (σ : TriVertex V→Bool) : Residue f 1 p :=
  reduce p f 1 (integralList F hF P i hf p₀ ht hv p hnil z β.val g (words g) (weight g) σ)

include positive in
theorem actual_lists_UD [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (correct : ∀ σ, (∏ g, parityOfWord f hf p
      (physicalListWord E baseCubic loopless P i hf ht hv p z β len words weight g σ))=
       UD E baseCubic (NativeProbeRing.Residue f) σ) :
    (∀ e : E, own (seat E baseCubic e false)=own (seat E baseCubic e true)) ∧
      (∀ g, 3^(Fintype.card (LocalPairs E baseCubic own g))≤len g) ∧
      ∃ g, Fintype.card (TriVertex V)≤128*Fintype.card (LocalPairs E baseCubic own g) ∧
        3^(Fintype.card (LocalPairs E baseCubic own g))≤len g := by
  let L := actualLists F hF P i hf p₀ ht hv p hnil z β.val len words weight
  have hc : ∀ σ, (∏ g, groupValue own L g σ)=UD E baseCubic (NativeProbeRing.Residue f) σ := by
    intro σ
    calc
      _ = ∏ g, parityOfWord f hf p
          (physicalListWord E baseCubic loopless P i hf ht hv p z β len words weight g σ) := by
        apply Finset.prod_congr rfl
        intro g _
        exact actualLists_received F hF P i hf p₀ ht hv p hnil z β.val len words weight positive g σ
      _ = _ := correct σ
  have hm := exterior_pair_same_group E baseCubic own (groupValue own L) (groupValue_local own L) hc
  have hb := direct_list_capacity E baseCubic own L hc
  obtain ⟨g,hg⟩ := many_group_pairs E baseCubic own
  exact ⟨hm,hb,⟨g,by simpa only [Fintype.card_fin] using hg,hb g⟩⟩

#print axioms actual_lists_UD
end
end V8NativeMessage.N6D
