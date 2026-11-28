
import J6R30ProducedGateRegistryHeader
import J6R25PreparedSupplyChildStage

/-! A separate marked external branch for the actual R26 zero child.
The ticket's physical half-port count depends on the chart and group,
not the chosen numerical probe. Thus an exterior address never needs
to be retagged as an ordinal of the native Plan prefix. -/
namespace J6R32RootGeneratedRegistryInputs
open AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R25PreparedSupply J6R30ProducedGateRegistry
set_option maxHeartbeats 2500000
set_option maxRecDepth 2200

structure ExternalAddress (tc tj pagew : ℕ) where
  center : Word tc
  sample : Word tj
  group : Word 6
  page : Word pagew

def ExternalAddress.bytes {tc tj pagew : ℕ} (A : ExternalAddress tc tj pagew) : List Bool :=
  true::(A.center.bits++(A.sample.bits++(A.group.bits++A.page.bits)))

def externalAddrWidth (tc tj pagew : ℕ) := 1+(tc+(tj+(6+pagew)))

theorem external_address_width {tc tj pagew : ℕ} (A : ExternalAddress tc tj pagew) :
    A.bytes.length=externalAddrWidth tc tj pagew := by
  simp only [ExternalAddress.bytes,externalAddrWidth,List.length_cons,List.length_append,
    A.center.size,A.sample.size,A.group.size,A.page.size]
  omega

def externalHeaderJob {tc tj pagew w b dep prec : ℕ} (A : ExternalAddress tc tj pagew)
    (receive : Word prec) (oldDepth : Word dep) (physical : List (PortRow w)) :
    J6R26DescriptorTree.Job w b dep prec :=
  ⟨A.bytes,A.group,receive,oldDepth,physical⟩


theorem literal_header_exact {tc tj pagew w b dep prec key : ℕ}
    (A : ExternalAddress tc tj pagew) (raw : List (PortRow w)) (receive : Word prec)
    (oldDepth : Word dep) (issue : Meter (Word key)) (hd : 0<dep)
    (depthFit : oldDepth.val+1<2^dep) (hb : 0<b)
    (hitFit : (raw.filter (fun row=>(cmpAddr A.group row.group).result)).length<2^b) :
    let J := externalHeaderJob (b:=b) A receive oldDepth raw
    let E := J.make issue
    let selected := (raw.filter (fun row=>(cmpAddr A.group row.group).result))
    E.result.id=issue.result ∧
      E.result.bytes=A.bytes++childHeaderBytes receive (word (q:=dep) (oldDepth.val+1))
        (word (q:=b) selected.length) (selected.flatMap rowBytes) ∧
      loadAt prec (externalAddrWidth tc tj pagew) E.result.bytes=
        ⟨some receive,headerReadFee prec (externalAddrWidth tc tj pagew)⟩ := by
  let J := externalHeaderJob (b:=b) A receive oldDepth raw
  let E := J.make issue
  let pick := (raw.filter (fun row=>(cmpAddr A.group row.group).result))
  let R := childPortsWithCount (b:=b) A.group raw
  let d := increment oldDepth
  obtain ⟨G,P,_⟩ := ports_counted hb A.group raw hitFit
  change R.result.1=pick at G
  change R.result.2.val=R.result.1.length at P
  have dt := (increment_exact hd oldDepth depthFit).1
  have dw : d.result=word (q:=dep) (oldDepth.val+1) :=
    (valued_word _).symm.trans (congrArg word dt)
  have qw : R.result.2=word (q:=b) pick.length :=
    (valued_word _).symm.trans (congrArg word (P.trans (congrArg List.length G)))
  have content : E.result.bytes=A.bytes++childHeaderBytes receive (word (q:=dep) (oldDepth.val+1))
      (word (q:=b) pick.length) (pick.flatMap rowBytes) := by
    rw [J.make_bytes issue]
    change A.bytes++(childStage (b:=b) issue A.group receive oldDepth raw).result.bytes=_
    rw [(child_stage_exact (b:=b) issue A.group receive oldDepth raw).2.1]
    change A.bytes++childHeaderBytes receive d.result R.result.2 (R.result.1.flatMap rowBytes)=_
    rw [dw,qw,G]
  refine ⟨J.make_id issue,content,?_⟩
  rw [←external_address_width A,content,childHeaderBytes]
  let rest := (word (q:=dep) (oldDepth.val+1)).bits++(word (q:=b) pick.length).bits++pick.flatMap rowBytes
  simpa only [List.append_assoc,rest] using load_at_boundary A.bytes receive rest

#print axioms external_address_width
#print axioms literal_header_exact
end J6R32RootGeneratedRegistryInputs
