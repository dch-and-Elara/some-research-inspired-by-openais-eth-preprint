import J6R52FreshExteriorWordsComputedShell
import J6R52FreshExteriorWordsFee

/-! One shared accepted chart, native field frame and word material.
A site borrows this compiled frame, it does not import a concealed
per-group copy of either the frame generator or the CNF serializer. -/
namespace J6R54PublicFamily
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6Mesh J6OrientedHost J6R15ModeCost
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R30GeneratedRootLayout J6R52FreshExterior
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13000000

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw : ℕ}

structure SharedInputs (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m))
    (ell q rr cc dd prec kp bw : ℕ) where
  positive : 0<ell
  hf : f.Monic
  literal : Meter (LiteralPortFile T rr cc dd)
  field : Meter (Frame f (J6SourcePrecision.printed m base))
  baseWord : Word q
  baseTag : baseWord.val=base
  copyFit : K m<2^q
  preFit : J6SourcePrecision.printed m base<2^q
  birthFit : J6SourcePrecision.printed m base<2^prec
  code : ℕ
  codeBound : rootCodeWidth m base≤code
  codeFit : code<2^bw
  codeWordWidthPositive : 0<bw
  mark : Word kp

structure Compiled (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m))
    (ell q rr cc dd prec kp bw : ℕ) where
  positive : 0<ell
  hf : f.Monic
  literal : LiteralPortFile T rr cc dd
  frame : Frame f (J6SourcePrecision.printed m base)
  regs : ExteriorRegisters q prec
  copiesOK : regs.copies.val=K m
  preOK : regs.pre.val=J6SourcePrecision.printed m base
  birthOK : regs.birth.val=J6SourcePrecision.printed m base
  code : ℕ
  codeBound : rootCodeWidth m base≤code
  codeTape : Word bw
  codeTruth : codeTape.val=code
  mark : Word kp

def prepShared (I : SharedInputs G ell q rr cc dd prec kp bw)
    (emit : Meter (Word bw)) (codeTruth : emit.result.val=I.code) :
    Meter (Compiled G ell q rr cc dd prec kp bw) :=
  let R := computeExteriorRegisters m prec I.baseWord
  let ok := computed_exterior_registers_exact m base prec I.baseWord I.baseTag I.copyFit I.preFit I.birthFit
  ⟨⟨I.positive,I.hf,I.literal.result,I.field.result,R.result,ok.1,ok.2.1,ok.2.2.1,
    I.code,I.codeBound,emit.result,codeTruth,I.mark⟩,
    I.literal.steps+I.field.steps+R.steps+emit.steps+11⟩

theorem shared_uses_compiled_data (I : SharedInputs G ell q rr cc dd prec kp bw)
    (emit : Meter (Word bw)) (codeTruth : emit.result.val=I.code) :
    let P := prepShared I emit codeTruth
    P.result.literal=I.literal.result ∧ P.result.frame=I.field.result ∧
      P.result.regs=(computeExteriorRegisters m prec I.baseWord).result ∧
      P.result.codeTape=emit.result ∧
      P.steps=I.literal.steps+I.field.steps+(computeExteriorRegisters m prec I.baseWord).steps+emit.steps+11 :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem shared_paid_roof (I : SharedInputs G ell q rr cc dd prec kp bw)
    (emit : Meter (Word bw)) (codeTruth : emit.result.val=I.code) :
    (prepShared I emit codeTruth).steps≤
      I.literal.steps+I.field.steps+precisionFromBaseFee m q+
      exteriorRegistersFee q q prec+emit.steps+15 := by
  have hq : 0<q := Nat.zero_lt_one.trans (copy_width_above_one I.copyFit)
  have H := computed_exterior_registers_fee_le m prec hq I.baseWord
  change I.literal.steps+I.field.steps+(computeExteriorRegisters m prec I.baseWord).steps+emit.steps+11≤_
  omega

#print axioms prepShared
#print axioms shared_uses_compiled_data
#print axioms shared_paid_roof
end
end J6R54PublicFamily

