import J6R110RootWidthChoiceNumeric
import J6R54PublicFamilyFresh
import J6R54PublicFamilyWords
import J6R52FreshExteriorWordsFee

/-! One actual source-sized R54 FreshWords record. Either build its
base word by a paid ripple emission, or safely retain an already metered
base word. The existing R54 prepareShared emits the chosen code once;
neither builder here bills a second code emission. -/
namespace J6R110RootWidthChoice
open J6Mesh AOracleMachineTime J6R15ModeCost J6R52FreshExterior J6R54PublicFamily J6R49Cost
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 3300
set_option maxHeartbeats 12000000

def fromExactBaseWord (m native base : ℕ) (nativeFit : native≤m)
    (baseFit : base≤(physicalSize m native)^2)
    {kp : ℕ} (mark : Word kp) (w : Word (chosenQ m)) (tag : w.val=base) :
    FreshWords m base (chosenQ m) (chosenPrec m) kp (chosenBW m) :=
  let guard := chosen_precision_width_never_truncates m native base nativeFit baseFit
  { baseWord := w
    baseTag := tag
    copyFit := guard.2.1
    preFit := guard.2.2.1
    birthFit := guard.2.2.2.1
    code := chosenCode m
    codeBound := guard.2.2.2.2
    codeFit := chosen_code_fits_storage m
    codePositive := chosen_bw_positive m
    mark := mark }

def makeFreshWords (m native base : ℕ) (nativeFit : native≤m)
    (baseFit : base≤(physicalSize m native)^2) {kp : ℕ} (mark : Word kp) :
    Meter (FreshWords m base (chosenQ m) (chosenPrec m) kp (chosenBW m)) :=
  let w := emitOrdinal (chosenQ m) base
  let fits := (chosen_precision_width_never_truncates m native base nativeFit baseFit).1
  let E := emitted_ordinal_exact (chosenQ m) base (Nat.zero_lt_one.trans (chosen_q_above_one m)) fits
  ⟨fromExactBaseWord m native base nativeFit baseFit mark w.result E.1,w.steps⟩

theorem made_fresh_words_has_actual_base_and_numeric_code (m native base : ℕ)
    (nativeFit : native≤m) (baseFit : base≤(physicalSize m native)^2) {kp : ℕ} (mark : Word kp) :
    let s := physicalSize m native
    let out := makeFreshWords m native base nativeFit baseFit mark
    out.result.baseWord=(emitOrdinal (chosenQ m) base).result ∧
      out.result.baseWord.val=base ∧ out.result.mark=mark ∧
      out.result.code=3*Nat.clog 2 s+7 ∧
      out.steps=ordinalFee (chosenQ m) base := by
  have dim := chosen_widths_are_on_true_source_mesh m native nativeFit
  have fit := (chosen_precision_width_never_truncates m native base nativeFit baseFit).1
  have H := emitted_ordinal_exact (chosenQ m) base (Nat.zero_lt_one.trans (chosen_q_above_one m)) fit
  exact ⟨rfl,H.1,rfl,dim.2.2.1,H.2⟩

/-- The original code-write expression `emitOrdinal bw I.code`, on
these real words, preserves the explicit numeric code and real fee.
It has not already been charged by `makeFreshWords`. -/
theorem chosen_words_use_the_actual_r54_code_word (m native base : ℕ)
    (nativeFit : native≤m) (baseFit : base≤(physicalSize m native)^2) {kp : ℕ} (mark : Word kp) :
    let out := makeFreshWords m native base nativeFit baseFit mark
    let E := emitOrdinal (chosenBW m) out.result.code
    E.result.val=chosenCode m ∧ E.steps=ordinalFee (chosenBW m) (chosenCode m) :=
  emitted_ordinal_exact (chosenBW m) (chosenCode m) (chosen_bw_positive m) (chosen_code_fits_storage m)

def retainFreshWords (m native base : ℕ) (nativeFit : native≤m)
    (baseFit : base≤(physicalSize m native)^2) {kp inputWidth : ℕ}
    (mark : Word kp) (input : Meter (Word inputWidth)) (tag : input.result.val=base) :
    Meter (FreshWords m base (chosenQ m) (chosenPrec m) kp (chosenBW m)) :=
  let R := retainAtWidth (chosenQ m) input.result
  have range : input.result.val<2^chosenQ m :=
    tag.symm ▸ (chosen_precision_width_never_truncates m native base nativeFit baseFit).1
  let exactV := (retain_at_width_exact (chosenQ m) input.result range).1
  ⟨fromExactBaseWord m native base nativeFit baseFit mark R.result (exactV.trans tag),input.steps+R.steps⟩

theorem retained_fresh_words_does_not_erase_input_fee (m native base : ℕ) (nativeFit : native≤m)
    (baseFit : base≤(physicalSize m native)^2) {kp inputWidth : ℕ}
    (mark : Word kp) (input : Meter (Word inputWidth)) (tag : input.result.val=base) :
    let out := retainFreshWords m native base nativeFit baseFit mark input tag
    out.result.baseWord=(retainAtWidth (chosenQ m) input.result).result ∧
      out.result.baseWord.val=base ∧ out.result.mark=mark ∧ out.result.code=chosenCode m ∧
      out.steps=input.steps+(2*inputWidth+4*chosenQ m+5) := by
  have range : input.result.val<2^chosenQ m :=
    tag.symm ▸ (chosen_precision_width_never_truncates m native base nativeFit baseFit).1
  obtain ⟨value,fee⟩ := retain_at_width_exact (chosenQ m) input.result range
  exact ⟨rfl,value.trans tag,rfl,rfl,congrArg (input.steps+·) fee⟩

theorem chosen_root_storage_polynomial_ceiling (m native : ℕ) (nativeFit : native≤m) :
    let s := physicalSize m native
    chosenQ m≤4*s+6 ∧ chosenBW m≤6*s+7 := by
  have lam : lambda m≤2*physicalSize m native :=
    (Nat.lt_pow_self (n:=lambda m) (a:=2) (by decide)).le.trans
      (source_wires_le_twice_input m native nativeFit)
  change chosenQ m≤4*physicalSize m native+6 ∧ chosenCode m≤6*physicalSize m native+7
  rw [chosenQ,code_is_explicit]
  omega

theorem ordinal_fee_mono_dimensions {w v i j : ℕ} (width : w≤v) (value : i≤j) :
    ordinalFee w i≤ordinalFee v j := by
  unfold ordinalFee
  gcongr

theorem actual_fresh_base_and_code_emissions_have_polynomial_bills (m native base : ℕ)
    (nativeFit : native≤m) (baseFit : base≤(physicalSize m native)^2) {kp : ℕ} (mark : Word kp) :
    let s := physicalSize m native
    let out := makeFreshWords m native base nativeFit baseFit mark
    out.steps≤ordinalFee (4*s+6) (s^2) ∧
      (emitOrdinal (chosenBW m) out.result.code).steps≤ordinalFee (6*s+7) (6*s+7) := by
  have fitting := chosen_root_storage_polynomial_ceiling m native nativeFit
  have first := (made_fresh_words_has_actual_base_and_numeric_code m native base nativeFit baseFit mark).2.2.2.2
  have next := (chosen_words_use_the_actual_r54_code_word m native base nativeFit baseFit mark).2
  exact ⟨first.le.trans (ordinal_fee_mono_dimensions fitting.1 baseFit),
    next.le.trans (ordinal_fee_mono_dimensions fitting.2 fitting.2)⟩

/-- All three register words are computed by the existing R52 circuit,
with the actual finite fit guards carried by the chosen R54 inputs. -/
theorem chosen_base_registers_feed_the_original_primitive (m native base : ℕ)
    (nativeFit : native≤m) (baseFit : base≤(physicalSize m native)^2) {kp : ℕ} (mark : Word kp) :
    let I := (makeFreshWords m native base nativeFit baseFit mark).result
    let Z := computeExteriorRegisters m (chosenPrec m) I.baseWord
    Z.result.copies.val=K m ∧ Z.result.pre.val=J6SourcePrecision.printed m base ∧
      Z.result.birth.val=J6SourcePrecision.printed m base ∧
      Z.steps≤precisionFromBaseFee m (chosenQ m)+
        exteriorRegistersFee (chosenQ m) (chosenQ m) (chosenPrec m)+4 := by
  let I := (makeFreshWords m native base nativeFit baseFit mark).result
  have H := computed_exterior_registers_exact m base (chosenPrec m) I.baseWord I.baseTag
    I.copyFit I.preFit I.birthFit
  exact ⟨H.1,H.2.1,H.2.2.1,computed_exterior_registers_fee_le m (chosenPrec m)
    (Nat.zero_lt_one.trans (chosen_q_above_one m)) I.baseWord⟩

#print axioms fromExactBaseWord
#print axioms makeFreshWords
#print axioms made_fresh_words_has_actual_base_and_numeric_code
#print axioms chosen_words_use_the_actual_r54_code_word
#print axioms retainFreshWords
#print axioms retained_fresh_words_does_not_erase_input_fee
#print axioms chosen_root_storage_polynomial_ceiling
#print axioms actual_fresh_base_and_code_emissions_have_polynomial_bills
#print axioms chosen_base_registers_feed_the_original_primitive
end J6R110RootWidthChoice

