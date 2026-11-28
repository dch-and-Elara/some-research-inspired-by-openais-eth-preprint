import J6R32RootGeneratedRegistryInputsHeader

/-! The all-page exterior record is keyed by one real invocation,
not by a particular target Page. The marked raw (centre, sample,
group) header remains exterior and keeps the real child precision. -/
namespace J6R34RootAtlas
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6R26DescriptorTree J6R25PreparedSupply J6R30ProducedGateRegistry
open J6R15ModeCost J6R21Ancestor J6R24MeteredRecursion J6R26StablePreparedRoot J6R14ZeroMode
open J6R12Blueprint J6R11Blueprint J6R10Repack J6ActiveRun J6ActiveSchedule J1PPrinted P11FullPacking
open J6R32RootGeneratedRegistryInputs

structure OccurrenceAddress (tc tj : ℕ) where
  centre : Word tc
  sample : Word tj
  group : Word 6

def OccurrenceAddress.marked {tc tj : ℕ} (A : OccurrenceAddress tc tj) : ExternalAddress tc tj 0 :=
  ⟨A.centre,A.sample,A.group,word 0⟩

theorem no_page_in_outer_header {tc tj : ℕ} (A : OccurrenceAddress tc tj) :
    A.marked.bytes=true::(A.centre.bits++(A.sample.bits++A.group.bits)) := by
  have nilPage : A.marked.page.bits=[] := List.length_eq_zero_iff.mp A.marked.page.size
  change true::(A.centre.bits++(A.sample.bits++(A.group.bits++A.marked.page.bits)))=_
  rw [nilPage,List.append_nil]

def makeOccurrence {tc tj key w b dep prec : ℕ} (A : OccurrenceAddress tc tj)
    (receive : Word prec) (old : Word dep) (raw : List (PortRow w)) (issued : Meter (Word key)) :
    Meter (DirRow key) :=
  (externalHeaderJob (b:=b) A.marked receive old raw).make issued

section Native
variable {f : ℤ[X]} {ell s : ℕ} {c : Call (PhysicalHost f ell)}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)

set_option maxHeartbeats 4200000 in
theorem true_occurrence_header {tc tj w b dep prec key : ℕ}
    (D : @PhysicalPorts f ell s sel c d t w) (W : Prescribed f (externalProbeDegree s c))
    (j : Fin (externalProbeDegree s c+1)) (g : Fin 64)
    (A : OccurrenceAddress tc tj) (trueT : (A.centre.val:ℤ)=t.val)
    (trueJ : A.sample.val=j.val) (trueG : A.group.val=g.val)
    (issued : Meter (Word key)) (receive : Word prec)
    (recv : receive.val=registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)
    (old : Word dep) (oldExact : old.val=c.depth)
    (depPos : 0<dep) (depFit : c.depth+1<2^dep)
    (edgePos : 0<b) (edgeFit : (@externalZeroCall f ell s sel c d t W j g).edges<2^b) :
    let E := makeOccurrence (b:=b) A receive old D.raw issued
    let child := @externalZeroCall f ell s sel c d t W j g
    E.result.id=issued.result ∧
    E.result.bytes=(true::(A.centre.bits++(A.sample.bits++A.group.bits)))++childHeaderBytes receive
      (word (q:=dep) child.depth) (word (q:=b) child.edges)
      (((D.physicalSelected g).map D.record).flatMap rowBytes) ∧
    loadAt prec (externalAddrWidth tc tj 0) E.result.bytes=
      ⟨some receive,headerReadFee prec (externalAddrWidth tc tj 0)⟩ ∧
    receive.val=child.prec := by
  obtain ⟨own,raw,tag,exactPrec,_,_,_⟩ := make_external_header_exact sel d t D W j g A.marked
    trueT trueJ trueG issued receive recv old oldExact depPos depFit edgePos edgeFit
  rw [no_page_in_outer_header A] at raw
  exact ⟨own,raw,tag,exactPrec⟩
end Native

#print axioms no_page_in_outer_header
#print axioms true_occurrence_header
end J6R34RootAtlas
