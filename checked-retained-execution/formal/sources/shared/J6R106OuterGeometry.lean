import J6R106OuterHeader
import J6R106OuterPublication

namespace J6R106OuterGeometry
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R34RootAtlas J6R35GatewayPreparation
open J6R33PageIndexedBirth J6R32ChildResidentTransfer J6R32RootGeneratedRegistryInputs
open J6R54PublicFamily J6R57PublicRequest J6R75OuterTime
open J6R105OuterPublication J6R106OuterPublication J6R106OuterHeader
open J6R30GeneratedRootLayout J6R10Repack P11FullPacking J6Mesh J6OrientedHost J6R24LegalLayout J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R31RootResidentTables
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4700
set_option maxHeartbeats 21000000

def exteriorHeaderBits (m tc tj prec edgeWidth : ℕ) : ℕ :=
  encodedBytes (externalAddrWidth tc tj 0) prec 1 edgeWidth (rootHalfWidth m)
    (pageKeyWidth m+a m) (2*M m)

def exteriorHeaderOps (m tc tj prec edgeWidth key : ℕ) : ℕ :=
  headerClock (6*key+10) (externalAddrWidth tc tj 0) prec 1 edgeWidth key
    (rootHalfWidth m) (pageKeyWidth m+a m) (2*M m) (2*M m)

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]}
variable {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd edgew tc tj key prec tw bw kp : ℕ}

theorem root_half_header_body_size (p : Port (RootWire m)) :
    (expectedHalfRow T (oddAxis m) p).body.length=pageKeyWidth m+a m := by
  simp only [expectedHalfRow,halfPortSpec,List.length_append,Word.size]

theorem shared_header_caps_use_actual_closed_parent
    (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
    (S : ActualRootPreparation G ell q) (aligned : S=(rootPreparationFor X).result)
    (issuer : X.issue.steps≤6*key+10) :
    let E := headerUsingShared X S
    E.result.bytes.length≤exteriorHeaderBits m tc tj prec edgew ∧
      E.steps≤exteriorHeaderOps m tc tj prec edgew key := by
  let J := externalHeaderJob (b:=edgew) X.address.marked X.birth (word (q:=1) 0) S.parents
  let A := selectPorts J.group J.ports
  have parent : S.parents=(rootHalfOrder m).map (expectedHalfRow T (oddAxis m)) := by
    subst S
    exact (actual_root_half_tape X.source (oddAxis m) [] rfl).1
  have Hn : J.ports.length=2*M m := by
    change S.parents.length=_
    rw [parent,List.length_map,(root_half_order_complete m).2.2]
  have shape : ∀ row ∈ J.ports, row.body.length=pageKeyWidth m+a m := by
    intro row h
    change row∈S.parents at h
    rw [parent,List.mem_map] at h
    obtain ⟨p,_,rfl⟩ := h
    exact root_half_header_body_size (T:=T) p
  have clock := actual_job_fee_and_bytes_from_the_scanned_parent J X.issue
    (pageKeyWidth m+a m) shape
  have cLen : J.coordinates.length=externalAddrWidth tc tj 0 :=
    external_address_width X.address.marked
  have hits : A.result.length≤2*M m := clock.2.2.trans_eq Hn
  change (J.make X.issue).result.bytes.length≤_ ∧ (J.make X.issue).steps≤_
  rw [clock.1,clock.2.1,cLen,Hn]
  unfold exteriorHeaderBits exteriorHeaderOps
  constructor
  · unfold encodedBytes
    gcongr
  · unfold headerClock encodedBytes
    gcongr

#print axioms shared_header_caps_use_actual_closed_parent
end
end J6R106OuterGeometry
