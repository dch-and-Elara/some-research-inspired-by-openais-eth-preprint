
import J6R28GeneratedRootFrameCore
import J6R28GeneratedRootFrameGuards
import J6R28GeneratedRootFrameWidth
import J6R27PrescribedProbeRoot

/-! The physical source field is presented as exactly e raw lower bits
plus its implicit leading one, not as an oracle for integer coefficients.
Only the accepted candidate is input here; factor-search is separate. -/
namespace J6R28GeneratedRootFrame
open scoped Polynomial
open Polynomial Std.Sat A1R10 AOracleMachineTime
open J6Mesh J6OrientedHost J7R10Plant J6R24LegalLayout
open J6R24MeteredRecursion J6R26StablePreparedRoot J6R27PrescribedProbe J1PPrinted
open J6ActiveRun J6R12Repack J6R11Repack
set_option maxHeartbeats 5800000
set_option maxRecDepth 1800
set_option linter.unusedSectionVars false

noncomputable def chosenBinaryPolynomial {e : ℕ} (lower : Word e) : ℤ[X] :=
  binaryPolynomial ℤ lower.val

def chosenPresentation {e : ℕ} (lower : Word e) : LiteralPresentation (chosenBinaryPolynomial lower) :=
  ⟨lower.val,rfl⟩

theorem chosen_field_degree {e : ℕ} (lower : Word e) :
    (chosenBinaryPolynomial lower).natDegree=e :=
  (chosenPresentation lower).size.trans lower.property

theorem chosen_field_monic {e : ℕ} (lower : Word e) :
    (chosenBinaryPolynomial lower).Monic :=
  (chosenPresentation lower).monic

def printedFieldWidth (m native : ℕ) := 4*Nat.clog 2 (physicalSize m native)

theorem printed_field_width_positive (m native : ℕ) (hn : native≤m) :
    0<printedFieldWidth m native := by
  rw [printedFieldWidth,(physicalSize_ceiling m native hn).2.2]
  unfold lambda
  have h := b_pos m
  positivity

section Source
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
local notation "inp" => J7R10Readout.H

structure FieldInput (F : CNF V) (base : ℕ) where
  lower : Word (printedFieldWidth (ms F) (literalNativeSize F))
  irreducible : Irreducible (NativeProbeRing.residuePoly (chosenBinaryPolynomial lower))
  initialPositive : 0<base
  three : ∀ c∈F,c.length≤3
  large : (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize (ms F) (literalNativeSize F))

variable {F : CNF V} {base : ℕ} (S : FieldInput F base)

noncomputable abbrev FieldInput.f := chosenBinaryPolynomial S.lower

noncomputable def FieldInput.presentation : LiteralPresentation S.f := chosenPresentation S.lower

theorem FieldInput.e : S.f.natDegree=printedFieldWidth (ms F) (literalNativeSize F) :=
  chosen_field_degree S.lower

theorem FieldInput.ePositive : 0<S.f.natDegree :=
  S.e.symm ▸ printed_field_width_positive (ms F) (literalNativeSize F) (literal_native_fits F S.three)

def constantRootWord (m : ℕ) : Fin (a m)→Fin 64 := fun _=>0

noncomputable def FieldInput.rootShape :
    RootShape S.f (ms F) (printedHalf (ms F)) base (literalNativeSize F)
      (printedRankWidth (ms F)) (physicalPlant (inp F)) (constantRootWord (ms F)) :=
  guarded_printed_root_shape F S.three S.f base (constantRootWord (ms F)) S.e S.large

noncomputable def FieldInput.frame : Meter (Frame S.f (J6SourcePrecision.printed (ms F) base)) :=
  printedFrame S.presentation S.ePositive (ms F) base

theorem FieldInput.actual_frame_receipt :
    let z := S.frame
    z.result.words=S.lower.val.map (zeroExtend (J6SourcePrecision.printed (ms F) base)) ∧
    z.result.words.length=printedFieldWidth (ms F) (literalNativeSize F) ∧
    z.steps=frameBuildFee (printedFieldWidth (ms F) (literalNativeSize F)) (J6SourcePrecision.printed (ms F) base) := by
  obtain ⟨h,n,c⟩ := printed_frame_exact S.presentation S.ePositive (ms F) base
  exact ⟨h,n.trans S.e,c.trans (congrArg (fun e=>frameBuildFee e _) S.e)⟩


theorem FieldInput.odd_receiving_precision (ell : ℕ) (i : J6Recovery.Addr (ms F)) :
    registerPrecision (rootParams S.f ell (ms F) (literalNativeSize F))
      (physicalRootCall S.f ell base (ms F) (printedHalf (ms F)) (qs F)
        (physicalPlant (inp F)) (constantRootWord (ms F))) (S.rootShape.centre ell i) =
      J6SourcePrecision.printed (ms F) base :=
  S.rootShape.precision ell i

noncomputable abbrev FieldInput.children (ell : ℕ) : Type 1 :=
  ∀ i,GeneratedChildren (ell:=ell) S.rootShape S.presentation.monic i
end Source

#print axioms chosen_field_degree
#print axioms chosen_field_monic
#print axioms printed_field_width_positive
#print axioms FieldInput.rootShape
#print axioms FieldInput.actual_frame_receipt
#print axioms FieldInput.odd_receiving_precision
end J6R28GeneratedRootFrame
