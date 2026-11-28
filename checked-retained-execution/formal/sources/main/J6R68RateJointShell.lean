import J6R68RateJointScopeWords
import J6R52DispatchShell
import J6R15ModeCostCursor

/-! On the real selected shell load the issue, native inbound copy and
active context copy are bounded directly by word lengths. The route
and selected replay terms are the actual source-level finite tariffs
from ScopeWords, not caller-supplied whole scope costs. -/
namespace J6R68RateJoint
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R48RawRoute
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34RootAtlas J6R30ProducedGateRegistry
open J6R24MeteredRecursion J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6ActiveRun J6ActiveSchedule J6R50SourceProducer J6R51Online J6R52Dispatch J6R57ScopeFee

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3950
set_option maxHeartbeats 29000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}
variable {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child}
variable {U : ExplicitSelectedWords X.site w q} (Y : Replayed X.site w q U)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "nx" => (successorTicket v w)
local notation "d" => (ticketReady T (successorTicket v w))

theorem actual_shell_source_words_from_finite_copy_widths
    (B : PayloadShell Y) (D : DirectorySeed Y B)
    {tc tz tm : ℕ} (ct : Word tc) (zz : Word tz) (mm : Word tm) (gg : Word 6)
    (ht : ct.val=centerOrdinal T nx) (hz : zz.val=(nx).probeAt.val)
    (hm : mm.val=modeOrdinal T nx) (hg : gg.val=(nx).groupAt.val)
    (exponents : List (Word (q+1))) (acted : exponents.map Word.val=liveExponentSpec Y)
    (issued : B.issued=increment X.birth.job.identifier)
    (keyPos : 0<key) (keyRoom : X.birth.job.identifier.val+1<2^key)
    (K : ℕ) (keyW : key≤K) (depthW : B.dep≤K) (precW : prec≤K) (timeW : tw≤K)
    (codeW : bw≤K) (lamW : Nat.clog 2 s≤K) :
    let L := loadFromShell Y B D ct zz mm gg ht hz hm hg exponents acted
    measuredWordProducers L.advance.next.input≤
      nextPortWordsTariff (X:=X) q+selectedResidentWordsTariff (X:=X) (w:=w) U+(40*K+45) := by
  let Y0 := loadFromShell Y B D ct zz mm gg ht hz hm hg exponents acted
  obtain ⟨_,_,_,_,_,native,words⟩ :=
    shell_really_uses_input_fields Y B D ct zz mm gg ht hz hm hg exponents acted
  change Y0.event.native.steps=(3*B.dep+1)+(3*prec+1)+8 at native
  change Y0.event.words.steps=contextCopyFee tw bw+(3*B.axis.length+1)+(3*B.fw.length+1)+8 at words
  have issue : Y0.event.issued.steps=13*key+4 := by
    change B.issued.steps=_
    rw [issued,(increment_exact keyPos X.birth.job.identifier keyRoom).2]
  let F : Frame f (registerPrecision SP v.child (nx).centerAt) :=
    ⟨register_positive d (nx).centerAt,B.fw,B.hOld,B.hMod⟩
  have fields : B.fw.length=4*Nat.clog 2 s :=
    (F.natDegree hf).trans cfg.coefficient
  have axis : B.axis.length≤Nat.clog 2 s := by
    rw [B.clock]
    exact (centerIndex d (nx).centerAt).isLt.le.trans (bits_le_lam _ _)
  have billed := actual_local_load_source_words_from_paid_parts Y0
  rw [native,words,issue,fields] at billed
  change measuredWordProducers Y0.advance.next.input≤_
  apply billed.trans
  change 13*key+4+((3*B.dep+1)+(3*prec+1)+8)+nextPortWordsTariff (X:=X) q+
    selectedResidentWordsTariff (X:=X) (w:=w) U+
      (contextCopyFee tw bw+(3*B.axis.length+1)+(3*(4*Nat.clog 2 s)+1)+8)+8≤_
  unfold contextCopyFee
  omega

#print axioms actual_shell_source_words_from_finite_copy_widths
end
end J6R68RateJoint
