import J6R58BootScopeResidentLedger
import J6R58BootScopeIntegrate

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
open J6R55TerminalBootJoined J6R57ScopeFee J6R48GeneratedAddons J6R53OldOwner J6R16ModeCost
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
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (D : OwnerWordsAtBodies X gate pad root (firstBodiesFromPaidBootCache X gate pad K L))
variable (Q : ∀ w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)),ResidentBootQueries (D.ports w))
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (inj : Function.Injective rootName)
local notation "A₀" => (firstBodiesFromPaidBootCache X gate pad K L)
local notation "D₀" => (paidFirstOwnerWords X gate pad root K L D Q)

/-- The only added uniform inputs are actual destination-list count
and physical port-key width. These are byte/row extents, not assumed
cost envelopes. -/
structure FirstResidentFit extends FirstBootWordFits where
  destRows : ℕ
  portWidth : ℕ

theorem raw_boot_input_geometry_monotone
    {k n own R o O d D v V x X dim DIM pg p P e : ℕ}
    (hoo : o≤O) (hdd : d≤D) (hvv : v≤V) (hxx : x≤X) (hii : dim≤DIM) (hpp : p≤P) :
    rawFirstInputGeometry k n own R o d v x dim pg p e≤
      rawFirstInputGeometry k n own R O D V X DIM pg P e := by
  unfold rawFirstInputGeometry
  have d₁ := Nat.mul_le_mul (show 3*o+5≤3*O+5 by omega) hdd
  have d₂ := Nat.mul_le_mul
    (show 3*v+3*dim+3*pg+48≤3*V+3*DIM+3*pg+48 by omega) hxx
  have pq := locate_fee_mono_width_tables hpp (Nat.le_refl (2*e))
  have d₃ := Nat.mul_le_mul_left (2*e)
    (show locateFee p (2*e)+3*p+3*o+3*v+9≤locateFee P (2*e)+3*P+3*O+3*V+9 by omega)
  omega

def rawGeometryBudget (sourceKey sources own heads dim pg edges : ℕ) (U : FirstResidentFit) : ℕ :=
  rawFirstInputGeometry sourceKey sources own heads U.ownerWidth U.destRows U.seatLookupWidth
    U.seatLookupRows dim pg U.portWidth edges

theorem bound_first_boot_on_source_cache_without_assumed_loader_cost
    (d : ℕ) (hDegree : ∀ u,P.degree u≤d) (F : FirstResidentFit)
    (hFit : ∀ w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)),
      (A₀).width w≤F.laneCodeWidth ∧ D.width w≤F.ownerWidth ∧
        (D.ports w).seatWidth≤F.seatLookupWidth ∧ (D.ports w).seats.result.length≤F.seatLookupRows ∧
        (D.keys w).dest.result.length≤F.destRows ∧ (compileOccurrence (bodyAtActualSlot X gate pad A₀ w).result).port≤F.portWidth) :
    ∀ w : ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)), ((withJoinedBoot X gate pad root M A₀ D₀ B live inj).initial w).steps≤
      firstScopeProducerBudget (s:=s) X gate pad root B
        (rawGeometryBudget K.keyWidth K.raw.length own root.order.length (Nat.clog 2 s) Pg (Ext).edges F)
        d F.toFirstBootWordFits := by
  apply boot_scene_from_first_producer X gate pad root M A₀ D₀ B live inj _ d hDegree F.toFirstBootWordFits
  · intro w
    obtain ⟨a,b,c,e,_,_⟩ := hFit w
    have sameTape : ((D₀).ports w).seats.result=(D.ports w).seats.result := by
      change (paidResidentBootPorts (D.ports w) (Q w)).seats.result=(D.ports w).seats.result
      rw [paid_boot_seat_input_same_bytes]
    have sameSeats := congrArg List.length sameTape
    exact ⟨a,b,c,sameSeats.le.trans e⟩
  · intro w
    obtain ⟨_,b,c,e,z,p⟩ := hFit w
    have dimLe : dim ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group)).ticket w)≤Nat.clog 2 s := bits_le_lam _ _
    exact (paid_first_precursor_bill_from_resident_input_lengths X gate pad root K L D Q w).trans
      (raw_boot_input_geometry_monotone b z c e dimLe p)

end
#print axioms raw_boot_input_geometry_monotone
#print axioms rawGeometryBudget
#print axioms bound_first_boot_on_source_cache_without_assumed_loader_cost
end J6R58BootScope
