import J6R57LiveSpaceCachedStack
import J6R57LiveSpaceBootBits
import J6R55TerminalBootJoinedCore
import J6R55CachedLedgerContraction
import J6R55SelectedPeakWords

/-! The same generated exterior machine returns the exact physical
contraction. At each real cached path count the one already shared
boot tape, the actual live scoped state, and the cached suspensions.
Byte bounds on the remaining caller-supplied records are explicit. -/
namespace J6R57LiveSpace
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R55TerminalBootJoined J6R54PeakInput J6R55SelectedPeak
open J6R10Reachable J6R16ModeCost J6R30ProducedGateRegistry
open J6R48DFS J6R52Peak J6R52CacheWhole J6R53PeakAddon J6R49LiveBits J6R55CachedLedger
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner J6R41StructuredAllPaths J6R51Online J6R55TerminalOrigin J6R54TerminalBoot J6R55BootBodies
open J6R51Peak
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
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



variable (M : (OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate))

variable (A : FirstBodyProgram X gate pad T)


variable (D : OwnerWordsAtBodies X gate pad root A)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
local notation "Start" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Mlive" => (withJoinedBoot X gate pad root M A D B live rootInj)
/-- These two explicitly shared source fields are charged once for a
whole exterior call, independently of how many first slots it visits. -/
def sharedLiteralStartBits : ℕ := sharedBootBits X A.lanes+(indexedOwnerTape root.raw).length
local notation "BootBytes" => (sharedLiteralStartBits X gate pad root A)

theorem actual_joined_boot_cached_value_and_same_path_space
    (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
    (legal : ReadyOnStack (borns Mlive) B)
    (leaves : letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) Start) :=
      J6R24MeteredRecursion.sourceDecision sel Start; LeafAgreement Mlive B)
    (rootFit : (Start).depth≤pathLimit s C)
    (fits : rate≤uniformWidth s C) (pageBound high fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit Mlive pageBound) (hi : ActualHighFit Mlive high)
    (sizes : EntryWidths Mlive fixed addr) (body : BootBodyWidth Mlive seed)
    (ownFit : OwnerWidth Mlive owner) :
    let out := runCachedRootSingleEmission Mlive retire B
    (T.frame (Path.root : Path sel Start Start).reached).decode out.result.1=
        J6R9Recursive.reduce (Start).prec f ell ((Start).host.contract X.hf) ∧ out.result.2=B ∧
    BootBytes=(orderedExteriorEdges X).length*rootLaneRowBits m key prec pad+
        (ownerTape (root.raw.map RefRow.payload)).length+root.raw.length*own ∧
    (∀ {c : Call (PhysicalHost f ell)} (p : Path sel Start c),
      ∃ bits,CachedPausePath Mlive retire B p bits ∧
        selectedCachedStackBits BootBytes Mlive B p bits≤
          BootBytes+actualOnlineRoof (s:=s) (C:=C) B (Start).edges (Start).prec pageBound high fixed addr seed+
            cachedIngressRoof (Start).edges s C addr seed owner key prec (pageKeyWidth m+pad)) := by
  have value := same_single_emission_exact_contraction_and_actual_occurrence_bill
    Mlive retire B legal leaves rootFit
  have common : BootBytes=(orderedExteriorEdges X).length*rootLaneRowBits m key prec pad+
      (ownerTape (root.raw.map RefRow.payload)).length+root.raw.length*own := by
    unfold sharedLiteralStartBits
    rw [exact_shared_boot_file_width X A.lanes,indexed_owner_tape_adds_address_width,Nat.add_assoc]
  exact ⟨value.1,value.2.1,common,fun p=>
    all_named_fields_on_same_cached_path_have_joint_cap BootBytes Mlive retire B
      fits pageBound high fixed addr seed owner pageFit hi sizes body ownFit legal p⟩

#print axioms actual_joined_boot_cached_value_and_same_path_space
end
end J6R57LiveSpace
