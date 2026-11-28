import J6R58BootScopeResidentProgram

/-! The joined first-slot debit contains the actual physical writer
exactly once, then the read-only mount and the actual addon emission.
Issuance carries the copied result, not another physical-writer fee.
These are the local boot charges, not a billed whole DFS. -/
namespace J6R58BootScope
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner J6R41StructuredAllPaths J6R51Online J6R55TerminalOrigin J6R54TerminalBoot J6R55BootBodies
open J6R55TerminalBootJoined J6R57ScopeFee J6R48GeneratedAddons J6R53OldOwner
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000
set_option maxRecDepth 6100
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own rate : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)




local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "InputAt" => (fun w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))=>
  OccurrenceInput T ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
    (exteriorChild G ell X.centre X.sample X.group)).ticket w) key prec tw bw (pageKeyWidth m+pad))

variable (K : ResidentFirstTemplates X pad T)
variable (L : BootLaneTape X gate pad)
variable (D : OwnerWordsAtBodies X gate pad root (firstBodiesFromPaidBootCache X gate pad K L))
variable (Q : ∀ w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)),ResidentBootQueries (D.ports w))

theorem paid_first_precursor_bill_from_resident_input_lengths (w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))) :
    let A := firstBodiesFromPaidBootCache X gate pad K L
    let I := (bodyAtActualSlot X gate pad A w).result
    let D' := paidFirstOwnerWords X gate pad root K L D Q
    firstRawReadDebit X gate pad root A D' w≤
      rawFirstInputGeometry K.keyWidth K.raw.length own root.order.length
        (D.width w) ((D.keys w).dest.result.length) (D.ports w).seatWidth (D.ports w).seats.result.length
        (dim ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group)).ticket w)) Pg (compileOccurrence I).port (Ext).edges := by
  let A := firstBodiesFromPaidBootCache X gate pad K L
  let I := (bodyAtActualSlot X gate pad A w).result
  let D' := paidFirstOwnerWords X gate pad root K L D Q
  let dy := dim ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group)).ticket w)
  let y := (D.ports w).seatWidth
  let t := ((D.keys w).dest.result).length
  let sr := (D.ports w).seats.result.length
  let po := (compileOccurrence I).port
  let qi := bootAddressBill (paidResidentBootPorts (D.ports w) (Q w)) (compileOccurrence I).native.physical.order
  have ptr : (A.old w).steps≤locateFee K.keyWidth K.raw.length+3*K.keyWidth+5 :=
    (checked_boot_handle_retains_actual_source K.raw (K.keys w) w (K.template w) (K.hit w)).2
  have seatsZero : (A.seats w).made.steps=0 := rfl
  have heads : ((D'.keys w).headers).steps=3+(3*own+26)*root.order.length := by
    change (copyBootHeaders (D.keys w).headers.result).steps=_
    rw [copy_boot_headers_exact,(D.keys w).headerExact,List.length_map]
  have dest : ((D'.keys w).dest).steps=3+(3*D.width w+5)*t :=
    congrArg Meter.steps (copy_gate_keys_exact _)
  have seat : ((D'.ports w).seats).steps=3+(3*y+3*dy+3*Pg+48)*sr :=
    congrArg Meter.steps (paid_boot_seat_input_same_bytes (D.ports w) (Q w))
  have query : qi≤(2*(Ext).edges)*(locateFee po (2*(Ext).edges)+3*po+3*D.width w+3*y+9) :=
    paid_boot_query_bill_from_actual_port_tape (D.ports w) (Q w)
  change (A.old w).steps+(A.seats w).made.steps+((D'.keys w).headers).steps+
    ((D'.keys w).dest).steps+((D'.ports w).seats).steps+qi≤_
  unfold rawFirstInputGeometry
  change _≤(locateFee K.keyWidth K.raw.length+3*K.keyWidth+5)+
    (3+(3*own+26)*root.order.length)+(3+(3*D.width w+5)*t)+
    (3+(3*y+3*dy+3*Pg+48)*sr)+
    (2*(Ext).edges)*(locateFee po (2*(Ext).edges)+3*po+3*D.width w+3*y+9)
  omega

end
#print axioms paid_first_precursor_bill_from_resident_input_lengths
end J6R58BootScope
