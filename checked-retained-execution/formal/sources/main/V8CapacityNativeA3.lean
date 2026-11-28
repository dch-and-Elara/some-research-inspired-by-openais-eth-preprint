import V8CapacityNativeCRT
import V8CapacityWidthGrid
import V8CapacityGridOrder
import V8CapacityLift

/-! The actual A1 source numerator, arbitrary jet input maps, and the
native A2 matrix give the separated upper bound in A3. -/
namespace V8CapacityNativeA3
open scoped Classical BigOperators
open V8CapacityFeatures V8CapacitySymbolic V8CapacityJetChart V8CapacityCRTJet
open V8CapacityNativeMatrix V8CapacityNativeCRT V8CapacityIntegrated
open V8CapacityMonicBasis V8CapacityGridOrder V8CapacityNewtonGrid V8CapacitySmith
open V8CapacityWidthGrid V8CapacityWidthUpper V8CapacityActiveWitness

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000

variable {O K H A Y : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [IsPrincipalIdealRing O] [Fintype H] [Fintype (IsLocalRing.ResidueField O)]
variable [Field K] [Algebra O K] [IsFractionRing O K]
variable {π : O} {q : ℕ}
variable (D : V8CapacityDigits.Digits π q) (hq : 0<q) (hq₂ : 2≤q)
variable (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (L p k : ℕ)

local notation "κ" => IsLocalRing.ResidueField O
local notation "F" => (H → κ)
local notation "P" => (L+p)
local notation "E" => Digits H k
local notation "I" => Grid H P k
local notation "C" => Columns H π P k
local notation "rdeg" => (@rowDegree E _ (DegreeCap P k))
local notation "CM" => monicC π P k D hq
local notation "M" => weighted π q rdeg CM
local notation "SR" => actualSmith hMax q rdeg CM
local notation "IndexType" => Index SR L p F

def origNumerator (U : H → Jet O k) (F₀ : MvPolynomial H (Jet O k)) : O :=
  coefficient O k (k-1) (MvPolynomial.eval₂Hom (RingHom.id _) U F₀)

def evalLin (x : E → O) : (I → O) →ₗ[O] O where
  toFun w := evalNormalized D hq hq₂ h0 hπ rdeg w x
  map_add' u v := by
    simp only [evalNormalized,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' a u := by
    simp only [evalNormalized,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem mod_same (u v : O) (he : coeffMod O π P u=coeffMod O π P v) : π^P∣u-v := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change coeffMod O π P (u-v)=0
  rw [map_sub,he,sub_self]

theorem active_cardinality (e : Fin q ≃ κ) :
    Fintype.card IndexType = q^(Fintype.card H)*Fintype.card (Active SR P) := by
  have ch := Fintype.card_congr e
  simp only [Fintype.card_fin] at ch
  rw [Fintype.card_prod,Fintype.card_fun,← ch]

include hq₂ h0 hπ in
/-- The actual A1 source on any chosen inputs of A^h has the A3
separated K lift, with one term per residue word and per active
direction of the actual weighted matrix A2. -/
theorem actual_K_upper (hk : 0<k) (hp : 0<p)
    (d : κ → O) (hd : Function.RightInverse d (IsLocalRing.residue O))
    (U : A → H → Jet O k) (receiver : Y → MvPolynomial H (Jet O k)) :
    ∃ l : A → IndexType → K, ∃ r : IndexType → Y → K, ∀ a y, ∃ err : O,
      algebraMap O K (origNumerator k (U a) (receiver y))/(algebraMap O K (π^L))-
        (∑ i : IndexType, l a i*r i y)=algebraMap O K (π^p*err) := by
  letI : LinearOrder I := gridOrder
  choose fiber x hx using (fun a : A => source_chart_surjective π k hk hMax d hd (U a))
  have hw (y : Y) : ∀ f : F, ∃ a : C → O, ∀ v : E → O,
      coeffMod O π P (rawAt D hq rdeg CM a v)=
        coeffMod O π P (sourceTop π k d f v (receiver y)) := by
    apply (source_column_iff D hq P k (by omega) hk d hd _).mp
    exact ⟨receiver y,fun _ _ => rfl⟩
  choose coeffs hc using hw
  let col (f : F) (y : Y) : matrixImage M :=
    ⟨(M).mulVec (coeffs y f),⟨coeffs y f,rfl⟩⟩
  obtain ⟨l,r,hlr⟩ := separated_fraction_upper (S:=SR) (K:=K) hπ L p
    fiber (fun a => evalLin D hq hq₂ h0 hπ L p k (x a)) col
  refine ⟨l,r,fun a y => ?_⟩
  obtain ⟨err,herr⟩ := hlr a y
  have key : coeffMod O π P (origNumerator k (U a) (receiver y))=
      coeffMod O π P ((evalLin D hq hq₂ h0 hπ L p k (x a)) (col (fiber a) y)) := by
    rw [← hx a]
    change coeffMod O π P (sourceTop π k d (fiber a) (x a) (receiver y))=
      coeffMod O π P (evalNormalized D hq hq₂ h0 hπ rdeg
        ((M).mulVec (coeffs y (fiber a))) (x a))
    rw [← rawAt_normalized D hq hq₂ h0 hπ]
    exact (hc y (fiber a) (x a)).symm
  obtain ⟨err',herr'⟩ := divided_diff (K:=K) hπ L p _ _ (mod_same L p _ _ key)
  refine ⟨err+err',?_⟩
  rw [mul_add,map_add]
  linear_combination herr+herr'

#print axioms active_cardinality
#print axioms actual_K_upper
end
end V8CapacityNativeA3

