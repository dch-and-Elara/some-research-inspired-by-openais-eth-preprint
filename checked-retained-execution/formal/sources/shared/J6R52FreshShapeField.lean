import Paper6SourceSize
import J6R52FreshShapeCore
import J6R29BinaryFieldSearchRoot

/-! The same new RootShape can use an actual paid binary-field search,
and the selected coefficient words are read into the real printed
frame. Irreducibility and the field degree do not become callbacks. -/
namespace J6R52FreshShape
open scoped Classical Polynomial
open Polynomial Std.Sat A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6R28GeneratedRootFrame J6R29BinaryFieldSearch J6R24LegalLayout J6R24MeteredRecursion
open J6OrientedHost J6R26StablePreparedRoot J6R51Ingress J7R10Plant
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 15000000
set_option maxRecDepth 2900

structure AcceptedNativeField (m native : ℕ) where
  lower : Word (printedFieldWidth m native)
  irreducible : Irreducible (NativeProbeRing.residuePoly (chosenBinaryPolynomial lower))

noncomputable def generateNativeField (m native : ℕ) (fit : native≤m) :
    Meter (AcceptedNativeField m native) :=
  let e := printedFieldWidth m native
  let he := printed_field_width_positive m native fit
  let r := acceptedField e he
  ⟨⟨r.result,(accepted_field_receipt e he).1⟩,r.steps⟩

section
noncomputable section

noncomputable abbrev AcceptedNativeField.f {m native : ℕ} (P : AcceptedNativeField m native) :=
  chosenBinaryPolynomial P.lower

theorem native_field_degree {m native : ℕ} (P : AcceptedNativeField m native) :
    P.f.natDegree=4*Nat.clog 2 (physicalSize m native) :=
  chosen_field_degree P.lower

theorem native_field_monic {m native : ℕ} (P : AcceptedNativeField m native) :
    P.f.Monic := chosen_field_monic P.lower

theorem generated_native_field_receipt (m native : ℕ) (fit : native≤m) :
    let e := printedFieldWidth m native
    let run := generateNativeField m native fit
    (fieldSearch e).result=some run.result.lower ∧
      run.steps≤fieldSearchFee e+6 := by
  let e := printedFieldWidth m native
  let he := printed_field_width_positive m native fit
  exact ⟨(Option.some_get (field_search_is_some e he)).symm,(accepted_field_receipt e he).2⟩

theorem generated_native_field_poly (m native : ℕ) (fit : native≤m) :
    (generateNativeField m native fit).steps≤(1024*9^2*2*2^6)*(physicalSize m native)^8+6 := by
  let S := physicalSize m native
  have hS : 1<S := by
    by_contra bad
    have z : Nat.clog 2 S=0 := Nat.clog_of_right_le_one (Nat.le_of_not_gt bad) 2
    have p : 0<4*Nat.clog 2 S := printed_field_width_positive m native fit
    rw [z,Nat.mul_zero] at p
    exact (Nat.lt_irrefl 0 p)
  exact (generated_native_field_receipt m native fit).2.trans
    (Nat.add_le_add_right (printed_field_search_polynomial S hS) 6)

noncomputable def nativeGeneratedFrame {m native : ℕ} (P : AcceptedNativeField m native)
    (fit : native≤m) (base : ℕ) :
    Meter (Frame P.f (J6SourcePrecision.printed m base)) :=
  printedFrame (chosenPresentation P.lower)
    (by rw [native_field_degree]; exact printed_field_width_positive m native fit) m base

theorem native_generated_frame_actual {m native : ℕ} (P : AcceptedNativeField m native)
    (fit : native≤m) (base : ℕ) :
    let run := nativeGeneratedFrame P fit base
    run.result.words=P.lower.val.map (zeroExtend (J6SourcePrecision.printed m base)) ∧
      run.result.words.length=printedFieldWidth m native ∧
      run.steps=frameBuildFee (printedFieldWidth m native) (J6SourcePrecision.printed m base) := by
  obtain ⟨w,l,c⟩ := printed_frame_exact (chosenPresentation P.lower)
    (show 0<P.f.natDegree from by rw [native_field_degree]; exact printed_field_width_positive m native fit) m base
  exact ⟨w,l.trans (chosen_field_degree P.lower),
    c.trans (congrArg (fun e=>frameBuildFee e _) (chosen_field_degree P.lower))⟩

variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable (F : CNF V) (order : DeclaredOrder V)
local notation "H" => (guardedInOrder F order.roster)
local notation "S" => (guardRoster order)
local notation "m" => (nWires H)
local notation "n" => (Paper6SourceSize.sourceNativeSize F order)

theorem fresh_source_native_fits : Paper6SourceSize.sourceNativeSize F order ≤ m := by
  have vars := J7R9Size.variables_le_occurrence H (fresh_guard_allOccur F order.roster order.complete)
  have rows := J7R9Size.clauses_le_occurrence H (fresh_guard_nonempty_rows F order)
  have wires := (J7R9Size.half_bounds H).1
  simp only [Paper6SourceSize.sourceNativeSize, J7R10Plant.nWires]
  omega

noncomputable def freshFieldSearch : Meter (AcceptedNativeField m n) :=
  generateNativeField m n (fresh_source_native_fits F order)

noncomputable abbrev freshFieldResult : AcceptedNativeField m n := (freshFieldSearch F order).result

local notation "N" => (freshFieldResult F order)

def freshSearchedRootShape (base : ℕ) (three : ∀ row∈F,row.length≤3)
    (large : printedGuard m n) :
    RootShape (N).f m (printedHalf m) base n (printedRankWidth m)
      (freshPlant H S) (constantRootWord m) :=
  shapeFromLegalNative F order (N).f base n three (fresh_source_native_fits F order)
    (native_field_degree N) large

noncomputable def freshFieldFrame (base : ℕ) :
    Meter (Frame (N).f (J6SourcePrecision.printed m base)) :=
  nativeGeneratedFrame N (fresh_source_native_fits F order) base

theorem fresh_searched_frame_receipt (base : ℕ) :
    let R := freshFieldSearch F order
    let A := freshFieldFrame F order base
    let e := printedFieldWidth m n
    (fieldSearch e).result=some R.result.lower ∧
      R.steps≤fieldSearchFee e+6 ∧
      A.result.words=R.result.lower.val.map (zeroExtend (J6SourcePrecision.printed m base)) ∧
      A.result.words.length=e ∧ A.steps=frameBuildFee e (J6SourcePrecision.printed m base) := by
  obtain ⟨s,c⟩ := generated_native_field_receipt m n (fresh_source_native_fits F order)
  obtain ⟨fr,len,fee⟩ := native_generated_frame_actual N (fresh_source_native_fits F order) base
  exact ⟨s,c,fr,len,fee⟩

#print axioms native_field_degree
#print axioms native_field_monic
#print axioms generated_native_field_receipt
#print axioms generated_native_field_poly
#print axioms native_generated_frame_actual
#print axioms fresh_source_native_fits
#print axioms freshSearchedRootShape
#print axioms fresh_searched_frame_receipt
end
end
end J6R52FreshShape
