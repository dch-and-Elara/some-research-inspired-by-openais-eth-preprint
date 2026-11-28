import J6R88ScopeCodeBounds
import J6R88ScopeCodeTrace
import J6R54PublicFamilyWords

/-! Here only the type-erased, *unpublished* input encoding is chosen.
The selector, source ticket, probe, resident mode order, exponents and
previous ancestor records are not changed. This is not an equality of
old and newly encoded bytes, and not an edit to an installed packet. -/
namespace J6R88ScopeCode
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R26DescriptorTree J6R34RootAtlas
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R51Online J6R50SourceProducer
open J6R30ProducedGateRegistry J6R33GeneratedChildSite J6R54PublicFamily

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4200
set_option maxHeartbeats 16700000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}

def emitWidthBeforePublication (I : OccurrenceInput T v key prec tw bw page)
    (n : ℕ) (bwPos : 0<bw) (room : n<2^bw) (npos : 0<n)
    (valid : 1+I.geometry.modes.length<2^n) : OccurrenceInput T v key prec tw bw page :=
  let E := emitOrdinal bw n
  { I with
    code := n
    words := ⟨{ I.words.result with
      context := {I.words.result.context with codeWidth:=E.result} },I.words.steps+E.steps+3⟩
    group := I.group
    clock := I.clock
    centre := I.centre
    codeExact := (emitted_ordinal_exact bw n bwPos room).1
    codePos := npos
    codeFit := valid
    acted := I.acted
    probe := I.probe }

theorem emitted_width_keeps_literal_native_arguments (I : OccurrenceInput T v key prec tw bw page)
    (n : ℕ) (bwPos : 0<bw) (room : n<2^bw) (npos : 0<n)
    (valid : 1+I.geometry.modes.length<2^n) :
    let J := emitWidthBeforePublication I n bwPos room npos valid
    J.code=n ∧ HEq J.native I.native ∧ HEq J.physical I.physical ∧
      J.geometry.modes=I.geometry.modes ∧
      HEq J.words.result.exponents I.words.result.exponents ∧
      J.words.result.axis=I.words.result.axis ∧ J.words.result.group=I.words.result.group ∧
      J.words.result.coordinates.val=I.words.result.coordinates.val ∧
      J.words.result.context.center=I.words.result.context.center ∧
      J.words.steps=I.words.steps+ordinalFee bw n+3 := by
  refine ⟨rfl,HEq.rfl,HEq.rfl,rfl,HEq.rfl,rfl,rfl,rfl,rfl,?_⟩
  change I.words.steps+(emitOrdinal bw n).steps+3=_
  rw [(emitted_ordinal_exact bw n bwPos room).2]

/-- Even holding the encoded code number's storage width fixed, its
value may reach the largest representable number, with every mode
and actual coordinate unchanged. The *new* atlas really pays for it. -/
theorem source_valid_code_can_be_maximum_without_more_input_bits
    (I : OccurrenceInput T v key prec tw bw page) :
    ∃ J : OccurrenceInput T v key prec tw bw page,
      J.code=2^bw-1 ∧ HEq J.native I.native ∧ HEq J.physical I.physical ∧
        J.geometry.modes=I.geometry.modes ∧
        J.words.result.context.center=I.words.result.context.center ∧
        J.words.result.context.codeWidth.bits.length=I.words.result.context.codeWidth.bits.length ∧
        3*(2^bw-1)≤(compileOccurrence J).compilePages.steps := by
  have oldRoom : I.code<2^bw := by rw [←I.codeExact]; exact val_lt I.words.result.context.codeWidth
  have width : 0<bw := by
    by_contra h
    have z : bw=0 := by omega
    have pos := I.codePos
    simp only [z,pow_zero] at oldRoom
    omega
  let maxCode := 2^bw-1
  have maxFit : I.code≤maxCode := by unfold maxCode; omega
  have positive : 0<maxCode := I.codePos.trans_le maxFit
  have room : maxCode<2^bw := by
    unfold maxCode
    exact Nat.sub_lt (Nat.pow_pos (by decide)) (by decide)
  have fit : 1+I.geometry.modes.length<2^maxCode :=
    I.codeFit.trans_le (Nat.pow_le_pow_right (by decide) maxFit)
  let J := emitWidthBeforePublication I maxCode width room positive fit
  refine ⟨J,rfl,HEq.rfl,HEq.rfl,rfl,rfl,?_,actual_atlas_build_really_writes_full_numeric_code J⟩
  exact J.words.result.context.codeWidth.size.trans I.words.result.context.codeWidth.size.symm

theorem one_may_choose_the_printed_small_encoding_before_publication
    (p : Path sel r c) (w : (Plan sel).Slot c)
    (I : OccurrenceInput T (p.ticket w) key prec tw bw page)
    (bwPos : 0<bw) (room : canonicalSourceCode s C r.prec<2^bw) :
    ∃ J : OccurrenceInput T (p.ticket w) key prec tw bw page,
      J.code=canonicalSourceCode s C r.prec ∧
      J.geometry.modes=I.geometry.modes ∧ HEq J.physical I.physical ∧
      J.words.result.coordinates.val=I.words.result.coordinates.val ∧
      HEq J.words.result.exponents I.words.result.exponents ∧
      J.words.steps=I.words.steps+ordinalFee bw (canonicalSourceCode s C r.prec)+3 := by
  let n := canonicalSourceCode s C r.prec
  let fit := (exact_native_roster_code_lower_and_choice p w I).2.2
  let pos : 0<n := least_roster_code_positive _
  let J := emitWidthBeforePublication I n bwPos room pos fit
  exact ⟨J,rfl,rfl,HEq.rfl,rfl,HEq.rfl,
    (emitted_width_keeps_literal_native_arguments I n bwPos room pos fit).2.2.2.2.2.2.2.2.2⟩

#print axioms emitWidthBeforePublication
#print axioms emitted_width_keeps_literal_native_arguments
#print axioms source_valid_code_can_be_maximum_without_more_input_bits
#print axioms one_may_choose_the_printed_small_encoding_before_publication
end
end J6R88ScopeCode
