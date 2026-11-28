import V8CapacityUnifiedScalarUpper
import V8CapacityUnifiedLocalViews

/-! Directly use the actual public-congruence scalar capacity in
U7/S6, with the receiver's actual integral polynomial coefficients. -/
namespace V8CapacityUnified.Scalar
open scoped Classical
open V8CapacityDigits V8CapacityUnified.U7

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1050000

variable {O K H : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
variable [IsFractionRing O K] [Fintype H]
variable {π : O} {q : ℕ} (D : Digits π q) (hq : 0<q)
variable (hq₂ : 2≤q) (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (s : PublicClass (O:=O) (H:=H)) (L : ℕ)

include D hq hq₂ h0 hπ in
theorem S2_bipartite_public :
    bipartite π (fun (u : {t : H → O // permitted π s t})
      (C : MvPolynomial H O) => scalarOutput (K:=K) π L u.val C)
      (Nat.card (S2Raw q (L+1) s.depth)) := by
  intro X Y _ _ u recv
  obtain ⟨A,ha,h⟩ := S2_fractional_upper (K:=K) D hq hq₂ h0 hπ s L 1
    (fun x => (u x).val) (fun x => (u x).property) recv
  refine ⟨A,ha,fun x y => ?_⟩
  simpa only [pow_one] using h x y

#print axioms S2_bipartite_public
end
end V8CapacityUnified.Scalar
