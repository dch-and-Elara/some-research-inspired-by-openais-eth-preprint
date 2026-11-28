
import J6R29BinaryFieldSearchCost
import J6R28GeneratedRootFrameCount

/-! Feed the actual exhaustive-search result into the existing literal,
stable, same-chart count driver. Prepared descendants are still inputs,
typed by the generated polynomial itself, not a separate polynomial. -/
namespace J6R29BinaryFieldSearch
open scoped Polynomial
open Polynomial Std.Sat A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6R28GeneratedRootFrame J6R22RootReadout J1PPrinted J6Mesh
set_option maxHeartbeats 7100000
set_option maxRecDepth 1700

theorem field_search_is_some (e : ℕ) (he : 0<e) : (fieldSearch e).result.isSome := by
  obtain ⟨w,hw,_,_⟩ := field_search_success e he
  simp [hw]

def acceptedField (e : ℕ) (he : 0<e) : Meter (Word e) :=
  let r := fieldSearch e
  ⟨r.result.get (field_search_is_some e he),r.steps+6⟩

theorem accepted_field_receipt (e : ℕ) (he : 0<e) :
    Irreducible (NativeProbeRing.residuePoly (chosenBinaryPolynomial (acceptedField e he).result)) ∧
      (acceptedField e he).steps≤fieldSearchFee e+6 := by
  obtain ⟨w,hw,hi,hfee⟩ := field_search_success e he
  have z : (acceptedField e he).result=w := Option.get_of_eq_some (field_search_is_some e he) hw
  rw [z]
  exact ⟨hi,Nat.add_le_add_right hfee 6⟩

variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {base : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "pm" => J6SourcePrecision.printed

structure PrintedRootGuard (F : CNF V) (base : ℕ) where
  initialPositive : 0<base
  three : ∀ c∈F,c.length≤3
  large : (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize (ms F) (literalNativeSize F))

noncomputable def generatedField (G : PrintedRootGuard F base) : Meter (FieldInput F base) :=
  let e := printedFieldWidth (ms F) (literalNativeSize F)
  let positive := printed_field_width_positive _ _ (literal_native_fits F G.three)
  let r := acceptedField e positive
  ⟨⟨r.result,(accepted_field_receipt e positive).1,G.initialPositive,G.three,G.large⟩,r.steps⟩

theorem generated_field_receipt (G : PrintedRootGuard F base) :
    let e := printedFieldWidth (ms F) (literalNativeSize F)
    let r := generatedField G
    (fieldSearch e).result=some r.result.lower ∧
      r.steps≤fieldSearchFee e+6 := by
  let e := printedFieldWidth (ms F) (literalNativeSize F)
  let pos := printed_field_width_positive _ _ (literal_native_fits F G.three)
  refine ⟨?_,(accepted_field_receipt e pos).2⟩
  exact (Option.some_get (field_search_is_some e pos)).symm

theorem actual_generated_field_polynomial_fee (G : PrintedRootGuard F base) :
    let s := physicalSize (ms F) (literalNativeSize F)
    (generatedField G).steps≤(1024*9^2*2*2^6)*s^8+6 := by
  let s := physicalSize (ms F) (literalNativeSize F)
  have hs : 1<s := by
    by_contra bad
    have z : Nat.clog 2 s=0 := Nat.clog_of_right_le_one (Nat.le_of_not_gt bad) 2
    have p : 0<4*Nat.clog 2 s :=
      printed_field_width_positive _ _ (literal_native_fits F G.three)
    rw [z,Nat.mul_zero] at p
    exact (Nat.lt_irrefl 0 p)
  exact (generated_field_receipt G).2.trans
    (Nat.add_le_add_right (printed_field_search_polynomial s hs) 6)

noncomputable def countBySearchedField (G : PrintedRootGuard F base) (ell : ℕ) (hv : 0<ell)
    (children : (generatedField G).result.children ell) :
    Meter (Word (printedAnswerWidth (ms F) base)) :=
  let A := generatedField G
  let R := countWithGeneratedFrame A.result ell hv children
  ⟨R.result,A.steps+R.steps+4⟩

theorem literal_searched_field_count (G : PrintedRootGuard F base) (ell : ℕ) (hv : 0<ell)
    (children : (generatedField G).result.children ell) :
    let R := countBySearchedField G ell hv children
    bitsValue R.result.val=PinnedCNF.modelCount F ∧
      R.steps≤fieldSearchFee (printedFieldWidth (ms F) (literalNativeSize F))+
        6+ (generated_frame_root_fee (generatedField G).result ell hv children+
          frameBuildFee (printedFieldWidth (ms F) (literalNativeSize F)) (pm (ms F) base)+4)+4 := by
  let S := generatedField G
  have C := literal_generated_frame_count S.result ell hv children
  have A := (generated_field_receipt G).2
  refine ⟨C.1,?_⟩
  change S.steps+(countWithGeneratedFrame S.result ell hv children).steps+4≤_
  exact Nat.add_le_add_right (Nat.add_le_add A C.2) _

#print axioms accepted_field_receipt
#print axioms generated_field_receipt
#print axioms actual_generated_field_polynomial_fee
#print axioms literal_searched_field_count
end J6R29BinaryFieldSearch
