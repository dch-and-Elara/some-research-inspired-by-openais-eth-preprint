import V8CapacityNativeMatrix
import V8CapacityJetChart

/-! Glue the actual source A1 receipt, finite active feature matrix and
CRT across every constant residue word. The theorem works on the whole
digit domain, not just on the witnesses used for width lower bounds. -/
namespace V8CapacityNativeCRT
open scoped Polynomial Classical BigOperators
open V8CapacityCRT V8CapacityCRTJet V8CapacityTranslation
open V8CapacityFeatures V8CapacityFeatureSpan V8CapacitySymbolic V8CapacityJetChart
open V8CapacityNativeMatrix V8CapacityMonicBasis V8CapacityIntegrated

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000

variable {O H : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [Fintype H]
variable [Fintype (IsLocalRing.ResidueField O)]
variable {π : O} {q : ℕ} (D : V8CapacityDigits.Digits π q) (hq : 0<q)
variable (P k : ℕ)

local notation "κ" => IsLocalRing.ResidueField O
local notation "E" => Digits H k
local notation "rdeg" => (@rowDegree E _ (DegreeCap P k))

-- Exactly the scalar A1 numerator before division by π^L.
theorem source_column_iff (hP : 0<P) (hk : 0<k)
    (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O))
    (goal : (H → κ) → (E → O) → BaseMod O π P) :
    (∃ F : MvPolynomial H (Jet O k), ∀ a x,
      coeffMod O π P (sourceTop π k d a x F)=goal a x) ↔
    (∀ a : H → κ, ∃ w : Columns H π P k → O, ∀ x : E → O,
      coeffMod O π P (rawAt D hq rdeg (monicC π P k D hq) w x)=goal a x) := by
  let d' : κ → Jet O k := fun a => constJet O k (d a)
  let u (a : H → κ) (x : E → O) : H → FiniteJet O π P k :=
    digitInput O π P k d a (asInput x)
  have hsep : ∀ a b, a≠b → IsUnit (d' a-d' b) := by
    intro a b hab
    change IsUnit (constJet O k (d a)-constJet O k (d b))
    rw [← map_sub]
    exact (residue_diff_unit O d hd hab).map (constJet O k)
  have hx (a : H → κ) (x : E → O) (i : H) :
      (u a x i - (reduceJet O π P k) (d' (a i)))^(P+k-1)=0 := by
    unfold u d' digitInput
    rw [reduceJet_const,add_sub_cancel_left]
    exact two_ideal_power _ _ _ _ P k (p_nil O π P k) (zJet_nil (BaseMod O π P) k)
  simp_rw [native_top_reduce]
  change (∃ F : MvPolynomial H (Jet O k), ∀ a x,
      coefficient (BaseMod O π P) k (k-1)
        (MvPolynomial.eval₂Hom (reduceJet O π P k) (u a x) F)=goal a x) ↔ _
  rw [raw_fiber_product (reduceJet O π P k) d' hsep (P+k-1) u
    (coefficient (BaseMod O π P) k (k-1)) goal hx]
  apply forall_congr'
  intro a
  have hshift (x : E → O) : u a x =
      fun i => digitShift O π P k (asInput x) i+(reduceJet O π P k) (d' (a i)) := by
    funext i
    exact exact_shift_input O π P k d a _ i
  simp_rw [hshift]
  refine (shifted_range (reduceJet O π P k) (fun i => d' (a i))
    (fun x => digitShift O π P k (asInput x))
    (coefficient (BaseMod O π P) k (k-1)) (goal a)).trans ?_
  exact centered_source_iff π P k D hq hP hk (goal a)

#print axioms source_column_iff
end
end V8CapacityNativeCRT

