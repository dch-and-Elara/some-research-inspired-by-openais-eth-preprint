import J6R50ModeDispatchCore
import J6R26DescriptorTreeNative

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6100000

/-! The actual R26 NativeJob address register. Field words are provided
to the metered emitter; this does not price creation of a catalogue or
assign a stock ordinal absent the explicit order agreement. -/
namespace J6R50ModeDispatch
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion

variable {f : ℤ[X]} {ell s C q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}

theorem paid_native_descriptor_address {port edge dep prec tc tz tm : ℕ}
    (D : NativeJob T v port edge dep prec tc tz tm)
    (a : ℕ) (roster : List (RawMode q)) (words : List (Word q)) (len : roster.length=words.length)
    (ordinal : Word tm) (ht : 0<tm) (fit : ordinal.val+1<2^tm)
    (same : ordinal.val=modeOrdinal T v) :
    let U := prepareMode a roster words ordinal
    ∃ openWord : OpenMode q tm,U.result=some openWord ∧
      openWord.support=supportSpec roster words ∧
      openWord.next.val=ordinal.val+1 ∧
      (issueGroup D.tWord D.zWord openWord D.gWord).result.bits=D.coordinates ∧
      U.steps+(issueGroup D.tWord D.zWord openWord D.gWord).steps=
        roster.length*dispatchStride a q+13*tm+13+6*(tc+(tz+(tm+6)))+10 := by
  obtain ⟨out,nxt,ct⟩ := prepare_emitted_mode_exact a roster words ordinal len ht fit
  let M : OpenMode q tm := ⟨ordinal,(increment ordinal).result,supportSpec roster words⟩
  obtain ⟨get,fee⟩ := issue_group_is_billed D.tWord D.zWord M D.gWord
  have m : ordinal=D.mWord :=
    (valued_word ordinal).symm.trans ((congrArg word (same.trans D.mExact.symm)).trans (valued_word D.mWord))
  refine ⟨M,out,rfl,nxt,?_,?_⟩
  · rw [get]
    change (joinKey D.tWord (joinKey D.zWord (joinKey ordinal D.gWord))).bits=D.coordinates
    rw [m]
    rfl
  · rw [ct,fee]
    omega

#print axioms paid_native_descriptor_address
end J6R50ModeDispatch

