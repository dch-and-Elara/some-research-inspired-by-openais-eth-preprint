import J6R53OldOwnerBits
import J6R33GeneratedChildSiteFrames
import J6R34RootAtlasOccurrence
import J6R50SourceProducerReplay

/-! Exact price and literal data preservation for the first occurrence's
small native headers, modulus and active words. The physical file here is
retained by reference, then R55's actual writer replaces it. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R26DescriptorTree J6R33GeneratedChildSite J6R53OldOwner J6R34RootAtlas
open J6R50SourceProducer J6R32ChildResidentTransfer J6R17ModeTape J6R30ProducedGateRegistry
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3300
set_option maxHeartbeats 14000000
set_option Elab.async false
noncomputable section

def copyModWord {p : ℕ} (x : A1R10.Word p) : Meter (A1R10.Word p) :=
  let y := copyFixed (⟨x.val,x.property⟩ : Word p)
  ⟨⟨y.result.bits,y.result.size⟩,y.steps⟩

theorem copy_mod_word_exact {p : ℕ} (x : A1R10.Word p) :
    copyModWord x=⟨x,3*p+1⟩ := by
  exact congrArg (fun y : Meter (Word p) => (⟨⟨y.result.bits,y.result.size⟩,y.steps⟩ : Meter (A1R10.Word p)))
    (copy_fixed_exact (⟨x.val,x.property⟩ : Word p))

def copyModulus {p : ℕ} : List (A1R10.Word p)→Meter (List (A1R10.Word p))
  | [] => ⟨[],3⟩
  | x::xs =>
    let h := copyModWord x
    let t := copyModulus xs
    ⟨h.result::t.result,h.steps+t.steps+4⟩

theorem copy_modulus_exact {p : ℕ} (xs : List (A1R10.Word p)) :
    copyModulus xs=⟨xs,3+(3*p+5)*xs.length⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [copyModulus,copy_mod_word_exact,ih,List.length_cons,Nat.mul_succ]
    congr 1
    omega

def copyActiveFields {p q tw bw : ℕ} {fw : List (A1R10.Word p)}
    (x : ActiveWords fw q tw bw) : Meter (ActiveWords fw q tw bw) :=
  let c := copyContext x.context
  let i := copyBytes x.axis
  let g := copyFixed x.group
  let ex := copyGateKeys x.exponents
  let z := copyCoordinates x.coordinates
  ⟨⟨c.result,i.result,g.result,ex.result,z.result⟩,c.steps+i.steps+g.steps+ex.steps+z.steps+8⟩

def activeFieldsFee (q tw bw a deg modes : ℕ) : ℕ :=
  contextCopyFee tw bw+3*a+3*deg+(3*q+5)*modes+32

theorem copy_active_fields_exact {p q tw bw : ℕ} {fw : List (A1R10.Word p)}
    (x : ActiveWords fw q tw bw) :
    copyActiveFields x=⟨x,activeFieldsFee q tw bw x.axis.length fw.length x.exponents.length⟩ := by
  cases x
  simp only [copyActiveFields,copy_context_exact,copyBytes_exact,copy_fixed_exact,
    copy_gate_keys_exact,copy_coordinates_exact,activeFieldsFee]
  congr 1
  omega

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}
variable {port edge dep tc tz tm : ℕ}

def nativeFieldsFee (tc tz tm dep prec : ℕ) : ℕ :=
  3*(tc+tz+tm+dep+prec)+32

def copyFirstNative (J : NativeJob T v port edge dep prec tc tz tm) :
    Meter (NativeJob T v port edge dep prec tc tz tm) :=
  let t := copyFixed J.tWord
  let z := copyFixed J.zWord
  let m := copyFixed J.mWord
  let g := copyFixed J.gWord
  let d := copyFixed J.oldDepth
  let p := copyFixed J.receiving
  ⟨{ J with
      tWord := t.result
      zWord := z.result
      mWord := m.result
      gWord := g.result
      oldDepth := d.result
      receiving := p.result
      tExact := (congrArg Word.val (congrArg Meter.result (copy_fixed_exact J.tWord))).trans J.tExact
      zExact := (congrArg Word.val (congrArg Meter.result (copy_fixed_exact J.zWord))).trans J.zExact
      mExact := (congrArg Word.val (congrArg Meter.result (copy_fixed_exact J.mWord))).trans J.mExact
      gExact := (congrArg Word.val (congrArg Meter.result (copy_fixed_exact J.gWord))).trans J.gExact
      depthExact := (congrArg Word.val (congrArg Meter.result (copy_fixed_exact J.oldDepth))).trans J.depthExact
      receiveExact := (congrArg Word.val (congrArg Meter.result (copy_fixed_exact J.receiving))).trans J.receiveExact },
    t.steps+z.steps+m.steps+g.steps+d.steps+p.steps+8⟩

theorem copy_first_native_exact (J : NativeJob T v port edge dep prec tc tz tm) :
    copyFirstNative J=⟨J,nativeFieldsFee tc tz tm dep prec⟩ := by
  cases J
  simp only [copyFirstNative,copy_fixed_exact,nativeFieldsFee]
  congr 1
  omega

#print axioms copy_mod_word_exact
#print axioms copy_modulus_exact
#print axioms copy_active_fields_exact
#print axioms copy_first_native_exact
end
end J6R68RateJoint.RootWords

