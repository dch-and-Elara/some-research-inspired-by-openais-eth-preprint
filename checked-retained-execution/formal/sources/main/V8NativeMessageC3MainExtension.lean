import V8NativeMessageC3MainSource

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3300000

/-! The raw MAIN source lives over the rationals. Its genuine quotient
jets can be extended to the common characteristic-zero field used for
the D lifts, without introducing graph- or sign-dependent coefficients. -/
namespace V8NativeMessage.C3.RawMain
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive
open V8PooledMenu.FiveCopy V8PooledRange V8PooledRange.NativeOrigin V8NativeMessage.Five
noncomputable section

def extendJet (K : Type*) [Field K] [CharZero K] (k : ℕ) : C3.Jet ℚ k →+* C3.Jet K k :=
  adjoinMap (algebraMap ℚ K) ((X:ℚ[X])^k) ((X:K[X])^k) (by simp)

section RingMap
variable {V Γ A B : Type*} [Fintype V] [Fintype Γ] [CommRing A] [CommRing B] {b : Γ→ℕ}

theorem map_source_switch (ψ : A→+*B) (s : Bool) (x y : A) :
    ψ (C3.switch s x y)=C3.switch s (ψ x) (ψ y) := by
  cases s <;> simp [C3.switch]

def mapLists (ψ : A→+*B) (l : MainLists (V:=V) (J:=A) b) : MainLists (V:=V) (J:=B) b where
  owner := l.owner
  fixed g k := ψ (l.fixed g k)
  θ₁ g k v := ψ (l.θ₁ g k v)
  θ₂ g k v := ψ (l.θ₂ g k v)

omit [Fintype Γ] in
theorem mapped_point (ψ : A→+*B) (l : MainLists (V:=V) (J:=A) b)
    (s : V→Bool) (g : Γ) (k : Fin (b g)) :
    mainPoint (mapLists ψ l) s g k = ψ (mainPoint l s g k) := by
  simp only [mainPoint,mapLists,map_mul,map_prod,map_source_switch]

theorem mapped_completion (ψ : A→+*B) (l : MainLists (V:=V) (J:=A) b) (s : V→Bool) :
    mainCompleted (mapLists ψ l) s = ψ (mainCompleted l s) := by
  simp only [mainCompleted,map_prod,map_sum,mapped_point]

end RingMap
namespace CommonField
variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ] {G : Graph V E} {p : ThreePorts G}
variable {f : ℤ[X]} {m : ℕ} (M : Pairs G m) (P : Packing G p)
variable (hu : 0<rootU V) (huM : rootU V≤wireSize V) (i : Fin (rootU V)) (T : Finset (Fin 64))
variable (probes : Probes V f) (hf : f.Monic)
variable {H O K : Type*} [Fintype H] [Field K] [CharZero K] [CommRing O] [Algebra O K]
variable (χ : O→+*ZMod 2) (hinj : Function.Injective (algebraMap O K))
variable (files : H→FiveFile (Γ:=Γ) G p)
    (adr : ∀ h, Address (files h).layout) (last : ∀ h, Fin (order (files h).layout)) (b : H→Γ→ℕ)

local notation "len" => Combined.kept files last
variable (lists : ∀ h, NativePrivateLists (files h) (adr h) (Combined.kept files last h) (b h))
variable (read : ∀ h, C3.Jet K (Combined.kept files last h) →ₗ[K] K)
variable (lift : H → Fin 64 → HighChildView P hu huM i f → K)

def actualProduct (h : H) (s : V→Bool) : K :=
  read h (extendJet K (len h) (actualRegister (files h) (adr h) (len h) (lists h) s)) *
    ∏ g, lift h g (highChildView P hu huM i probes hf s g)

include hinj in
theorem C3_source_common_field (hd : 0<f.natDegree) (cross : Crosses M P i T)
    (correct : ∀ x y, ∃ o : O, algebraMap O K o=
      (∑ h, actualProduct P hu huM i probes hf files adr last b lists read lift h (activeSigns M x y)) ∧
        χ o=(originCount G p (activeSigns M x y):ZMod 2)) :
    2^m≤∑ h, len h * ∏g, b h g := by
  let fixed (h : H) :=
    mapLists (extendJet K (len h)) (toFixedLists (files h) (adr h) (len h) (lists h))
  apply C3_literal_factor_cut M P hu huM i T probes hf χ hinj len b
    (fun h => C3.jetBasis K (len h)) fixed read lift hd cross
  intro x y
  simpa only [C3.sourceBlock,fixed,mapped_completion,native_private_register,actualProduct] using correct x y

#print axioms map_source_switch
#print axioms mapped_point
#print axioms mapped_completion
#print axioms C3_source_common_field
end CommonField
end
end V8NativeMessage.C3.RawMain