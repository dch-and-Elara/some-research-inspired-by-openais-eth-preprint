import V8NativeMessageC3MainList
import V8NativeMessageC3ArbitraryCut

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3800000

namespace V8NativeMessage.C3.RawMain
open scoped Classical BigOperators Polynomial
open Polynomial V8PooledMenu.FiveCopy V8PooledRange V8PooledRange.NativeOrigin V8NativeMessage.Five
noncomputable section

variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ] {G : Graph V E} {p : ThreePorts G}
variable (F : FiveFile (Γ:=Γ) G p) (a : Address F.layout) (κ : ℕ)

/-- The full native register is a special case of the legal graph-fixed
lists. Fintype enumeration is an extensional identity, not a cost proof. -/
def exhaustiveLists : NativePrivateLists F a κ
    (fun g => Fintype.card (Fibre F.layout a g)) where
  point g k := (Fintype.equivFin (Fibre F.layout a g)).symm k
  weight _ _ := 1

theorem complete_fibre_register (s : V→Bool) :
    actualRegister F a κ (exhaustiveLists F a κ) s =
      ∏ g, ∑ x : Fibre F.layout a g, actualPoint F a κ s g x := by
  unfold actualRegister
  refine Finset.prod_congr rfl (fun g _ => ?_)
  simp only [exhaustiveLists,one_mul]
  exact Equiv.sum_comp (Fintype.equivFin (Fibre F.layout a g)).symm _

namespace Combined
variable {f : ℤ[X]} {m : ℕ} (M : Pairs G m) (P : Packing G p)
variable (hu : 0<rootU V) (huM : rootU V≤wireSize V) (i : Fin (rootU V)) (T : Finset (Fin 64))
variable (probes : Probes V f) (hf : f.Monic)
variable {H O : Type*} [Fintype H] [CommRing O] [Algebra O ℚ]
variable (χ : O→+*ZMod 2) (hinj : Function.Injective (algebraMap O ℚ))
variable (files : H→FiveFile (Γ:=Γ) G p)
    (adr : ∀ h, Address (files h).layout) (last : ∀ h, Fin (order (files h).layout)) (b : H→Γ→ℕ)

def kept (h : H) : ℕ := (last h).val+1

variable (lists : ∀ h, NativePrivateLists (files h) (adr h) (kept files last h) (b h))
variable (read : ∀ h, C3.Jet ℚ (kept files last h) →ₗ[ℚ] ℚ)
variable (lift : H → Fin 64 → HighChildView P hu huM i f → ℚ)

def actualProduct (h : H) (s : V→Bool) : ℚ :=
  read h (actualRegister (files h) (adr h) (kept files last h) (lists h) s) *
    ∏ g, lift h g (highChildView P hu huM i probes hf s g)

include hinj in
/-- Original C3 fixed-list bound over the rational scalar field, now
consuming legal MAIN addresses and their actual fibre points and
App. D individual true high slots on the same source five-copy CNF.
The layout itself is supplied and certified; its construction is not
claimed to run in paid time. -/
theorem C3_source_readout_rank (hd : 0<f.natDegree) (cross : Crosses M P i T)
    (correct : ∀ x y, ∃ o : O, algebraMap O ℚ o=
      (∑ h, actualProduct P hu huM i probes hf files adr last b lists read lift h (activeSigns M x y)) ∧
        χ o=(originCount G p (activeSigns M x y):ZMod 2)) :
    2^m≤∑ h, kept files last h * ∏g, b h g := by
  let fixed (h : H) :=
    toFixedLists (files h) (adr h) (kept files last h) (lists h)
  apply C3_literal_factor_cut M P hu huM i T probes hf χ hinj (kept files last) b
    (fun h => C3.jetBasis ℚ (kept files last h)) fixed read lift hd cross
  intro x y
  simpa only [C3.sourceBlock,fixed,native_private_register,actualProduct] using correct x y

#print axioms complete_fibre_register
#print axioms C3_source_readout_rank
end Combined
end
end V8NativeMessage.C3.RawMain