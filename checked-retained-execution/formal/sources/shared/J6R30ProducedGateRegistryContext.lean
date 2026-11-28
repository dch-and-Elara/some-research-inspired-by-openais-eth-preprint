
import J6R27OriginalGateModeInput
import J6R26DescriptorTreeTags

/-! Resident signed-centre and code-width fields in the creation
record. These are independent of the four R26 address coordinates:
a centre's ordinal is not its signed physical value. -/
namespace J6R30ProducedGateRegistry
open AOracleMachineTime J6R15ModeCost J6R26DescriptorTree J6R27OriginalGate

structure CentreContext (tw bw : ℕ) where
  negative : Bool
  magnitude : Word tw
  codeWidth : Word bw

def CentreContext.center {tw bw : ℕ} (h : CentreContext tw bw) : ℤ :=
  if h.negative then -(h.magnitude.val:ℤ) else (h.magnitude.val:ℤ)

def contextCopyFee (tw bw : ℕ) := 3*tw+3*bw+13

def copyContext {tw bw : ℕ} (h : CentreContext tw bw) : Meter (CentreContext tw bw) :=
  let t := duplicateWord h.magnitude
  let b := duplicateWord h.codeWidth
  ⟨⟨h.negative,t.result,b.result⟩,t.steps+b.steps+5⟩

theorem copy_context_exact {tw bw : ℕ} (h : CentreContext tw bw) :
    copyContext h=⟨h,contextCopyFee tw bw⟩ := by
  cases h with
  | mk s t b =>
    simp only [copyContext,duplicate_word_exact,contextCopyFee]
    congr 1
    omega

def readContextFee (tw bw : ℕ) := 1+tw*(8*tw+10)+(1+bw*(8*bw+10))+3*tw+8

def readContext {tw bw : ℕ} (h : CentreContext tw bw) : Meter (ℤ×ℕ) :=
  let t := readNatWord tw h.magnitude.bits
  let b := readNatWord bw h.codeWidth.bits
  ⟨(if h.negative then -(t.result:ℤ) else (t.result:ℤ),b.result),t.steps+b.steps+3*tw+8⟩

theorem read_context_exact {tw bw : ℕ} (h : CentreContext tw bw) :
    readContext h=⟨(h.center,h.codeWidth.val),readContextFee tw bw⟩ := by
  obtain ⟨_,hi,hiFee⟩ := ordinal_word_fits h.magnitude
  obtain ⟨_,hb,hbFee⟩ := ordinal_word_fits h.codeWidth
  simp only [readContext,hi,hiFee,hb,hbFee,CentreContext.center,readContextFee]

#print axioms copy_context_exact
#print axioms read_context_exact
end J6R30ProducedGateRegistry

