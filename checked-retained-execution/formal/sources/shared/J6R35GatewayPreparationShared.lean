import J6R34OfficialGatewayCompose
import J6R32RootGeneratedRegistryInputsTypedPorts

/-! Shared physically produced data of the fixed odd root, before
an exterior occurrence has been issued. Only immutable files belong
here, not a descendant route, key freshener or ready ledger. -/
namespace J6R35GatewayPreparation
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R15ModeCost
open J6R25PreparedSupply J6R17ModeTape J6R27OriginalGate J6R18ChildWrite
open J6R34RootAtlas J6R33OriginalJ6
set_option maxHeartbeats 10000000
set_option maxRecDepth 2200
set_option linter.unusedSectionVars false

def emitStoredHalfRows (m : ℕ) (seats : List (SeatField (a m) (pageKeyWidth m))) :
    Meter (List (PortRow (rootHalfWidth m))) :=
  flatMeter (halfPairFee m) (encodeHalfPair m) seats

def storedHalfRowsFee (m : ℕ) : ℕ := M m*(halfPairFee m+halfPairFee m*2+8)

theorem stored_half_rows_paid (m : ℕ) (seats : List (SeatField (a m) (pageKeyWidth m)))
    (count : seats.length=M m) :
    (emitStoredHalfRows m seats).steps≤storedHalfRowsFee m := by
  let H (F : SeatField (a m) (pageKeyWidth m)) := [halfPortSpec m false F,halfPortSpec m true F]
  have E := flatMeter_exact (halfPairFee m) (halfPairFee m) 2 (encodeHalfPair m) H seats
    (fun S _=>by rw [half_pair_exact m S]; exact ⟨rfl,le_rfl,rfl⟩)
  simpa only [emitStoredHalfRows,storedHalfRowsFee,count] using E.2.2

section Root
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m))

structure ActualRootPreparation (ell q : ℕ) where
  frame : Frame f (J6SourcePrecision.printed m base)
  probes : SuppliedProbeBits (rootPreset G ell) f.natDegree
  resident : Resident m q
  parents : List (PortRow (rootHalfWidth m))

/-- Build the four literal immutable root files once. The given field
Meter can be specialized to the actual R28 constructor (or the
R29-selected modulus field), not a bound on an arbitrary producer. -/
noncomputable def prepareSharedRoot
    {r c d q : ℕ} (source : LiteralPortFile T r c d) (ell : ℕ)
    (field : Meter (Frame f (J6SourcePrecision.printed m base)))
    (hq : 0<q) (copies receive : Word q) : Meter (ActualRootPreparation G ell q) :=
  let bank := buildRootBitBank G ell
  let resident := writeResidents m hq (oddAxis m) copies receive source.raw
  let parents := emitStoredHalfRows m resident.result.seats
  ⟨⟨field.result,bank.result,resident.result,parents.result⟩,
    field.steps+bank.steps+resident.steps+parents.steps+6⟩

theorem actual_shared_parent_file {r c d q : ℕ}
    (source : LiteralPortFile T r c d) (ell : ℕ)
    (field : Meter (Frame f (J6SourcePrecision.printed m base)))
    (hq : 0<q) (copies receive : Word q)
    (i : J6Recovery.Addr m) :
    let S := prepareSharedRoot G source ell field hq copies receive
    S.result.parents=(makeTypedRootParent G source ell i).result.raw ∧
      S.result.parents.length=2*M m := by
  have h := generated_typed_parent_receipt G source ell i
  refine ⟨h.1.symm,?_⟩
  change (makeHalfTape m [] source.raw).result.length=2*M m
  rw [←h.1]
  exact h.2.1

theorem actual_shared_paid {r c d q : ℕ}
    (source : LiteralPortFile T r c d) (ell : ℕ)
    (field : Meter (Frame f (J6SourcePrecision.printed m base)))
    (hq : 0<q) (hQ : 1<q) (copies receive : Word q)
    (copyOK : copies.val=K m) (precisionOK : receive.val=J6SourcePrecision.printed m base) :
    let S := prepareSharedRoot G source ell field hq copies receive
    let Dg := literalDegree m native
    S.steps=field.steps+(buildRootBitBank G ell).steps+
      (writeResidents m hq (oddAxis m) copies receive source.raw).steps+
      (emitStoredHalfRows m (S.result.resident.seats)).steps+6 ∧
    S.steps≤field.steps+(positiveTapeFee f.natDegree (Dg+1)+3)+
      residentsFee m q 0 (J6SourcePrecision.printed m base) r c d+
      storedHalfRowsFee m+6 ∧
    (∀ j : Fin (Dg+1),
      (S.result.probes.read j).result.val=encodeBits f.natDegree (j.val+1) ∧
      (S.result.probes.read j).steps≤(Dg+1)*(f.natDegree+2)) ∧
    S.result.resident.axis=[] ∧
    S.result.resident.seats=(actualWires m).map (physicalSeatField (rootChart T) (oddAxis m) (residentPageKey m)) ∧
    S.result.resident.mask=(orderedRootPages m).map (encodeMaskRow (rootChart T).mask) ∧
    S.result.resident.roster.precision.val=J6SourcePrecision.printed m base ∧
    S.result.resident.roster.modes.Nodup := by
  let S := prepareSharedRoot G source ell field hq copies receive
  let R := writeResidents m hq (oddAxis m) copies receive source.raw
  let H := emitStoredHalfRows m R.result.seats
  let B := buildRootBitBank G ell
  have h := printed_odd_residents source hq hQ copies receive copyOK precisionOK
  obtain ⟨axis,seat,mask,rprec,unique,_,bill⟩ := h
  have actualCount : R.result.seats.length=M m := by
    change R.result.seats=_ at seat
    rw [seat,List.length_map,actual_wires_count]
  have bank := build_root_probe_receipt G ell
  have hb : B.steps=positiveTapeFee f.natDegree (literalDegree m native+1)+3 := bank.1
  have hp : H.steps≤storedHalfRowsFee m := stored_half_rows_paid m R.result.seats actualCount
  have hr : R.steps≤residentsFee m q 0 (J6SourcePrecision.printed m base) r c d := bill
  refine ⟨rfl,?_,bank.2,axis,seat,mask,rprec,unique⟩
  change field.steps+B.steps+R.steps+H.steps+6≤field.steps+
    (positiveTapeFee f.natDegree (literalDegree m native+1)+3)+
    residentsFee m q 0 (J6SourcePrecision.printed m base) r c d+storedHalfRowsFee m+6
  omega

end Root

#print axioms stored_half_rows_paid
#print axioms actual_shared_parent_file
#print axioms actual_shared_paid
end J6R35GatewayPreparation
