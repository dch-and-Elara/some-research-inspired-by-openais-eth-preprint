import J6R108FreshFieldRateShared
import J6R57PublicRequestImage

/-! Read the charged field from the very fresh shared inputs consumed
by the selected outer request image. The true frame is retained and
the search/padding bill occurs once, not once per query/group. -/
namespace J6R108FreshFieldRate
open scoped Polynomial Classical
open Polynomial Std.Sat AOracleMachineTime
open J6Mesh J6OrientedHost J7R9Compiler J7R9Subdivision J7R10Plant
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R30GeneratedRootLayout J6R51Ingress
open J6R49RootIngress J6R50RootIngress J6R52FreshShape J6R52FreshExterior J6R15ModeCost
open J6R27PrescribedProbe J6R54PublicFamily J6R57PublicRequest

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
set_option maxSynthPendingDepth 12

noncomputable section
section Bill
variable {U₀ : Type} [Fintype U₀]
variable {f : ℤ[X]} {m₀ n₀ base₀ native₀ : ℕ} {T : Plant U₀ m₀ n₀}
variable {G : RootShape f m₀ (printedHalf m₀) base₀ native₀
  (printedRankWidth m₀) T (constantRootWord m₀)}
variable {ell₀ q₀ r₀ c₀ d₀ prec₀ kp₀ bw₀ tc₀ tj₀ tw₀ ew₀ : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem image_charges_the_shared_frame_once
    (I : SharedInputs G ell₀ q₀ r₀ c₀ d₀ prec₀ kp₀ bw₀)
    (U : Widths m₀ native₀ tc₀ tj₀ tw₀ ew₀) :
    let R := buildRequestImage U I
    let after := (buildRequestInputs (prepareShared I).result U).steps
    let reg := (computeExteriorRegisters m₀ prec₀ I.baseWord).steps
    R.result.compiled.frame=I.field.result ∧
      R.steps=I.literal.steps+I.field.steps+reg+ordinalFee bw₀ I.code+11+after+3 := by
  exact ⟨rfl,congrArg (fun v : ℕ=>v+(buildRequestInputs (prepareShared I).result U).steps+3)
    (prepare_shared_exact_cost I)⟩
end Bill

section Bound
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

/-- Reuse the exact local field bound in the genuine summed startup
charge. The accepted fresh field supplies this premise, never an
arbitrary replacement of the Meter. -/
theorem actual_request_image_uses_the_proved_local_field_bound
    (I : SharedInputs G ell q rr cc dd prec kp bw)
    (U : Widths m native tc tj tw edgew) (cap : ℕ) (fieldBound : I.field.steps≤cap) :
    let R := buildRequestImage U I
    let after := (buildRequestInputs (prepareShared I).result U).steps
    let reg := (computeExteriorRegisters m prec I.baseWord).steps
    R.result.compiled.frame=I.field.result ∧
      R.steps≤I.literal.steps+cap+reg+ordinalFee bw I.code+11+after+3 := by
  obtain ⟨frame,cost⟩ := image_charges_the_shared_frame_once I U
  refine ⟨frame,cost.le.trans ?_⟩
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left fieldBound I.literal.steps)
      ((computeExteriorRegisters m prec I.baseWord).steps)) (ordinalFee bw I.code))
        11) ((buildRequestInputs (prepareShared I).result U).steps)) 3
end Bound

#print axioms image_charges_the_shared_frame_once
#print axioms actual_request_image_uses_the_proved_local_field_bound
end
end J6R108FreshFieldRate

