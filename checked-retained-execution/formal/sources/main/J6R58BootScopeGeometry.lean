import J6R55TerminalBootJoinedFee
import J6R58BootScopeMount
import J6R58BootScopeWriter

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
open J6R55TerminalBootJoined J6R57ScopeFee J6R48GeneratedAddons J6R16ModeCost J6R51Peak
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


/-- The retained root cache is shared. The position/shape template,
optional reordered seat export, header/destination tapes, and exact
finite per-half-port query remain the only measured source inputs to
the first-scope builder. No lane build, root Gate file build, or Page
atlas installation is performed inside this scope. -/
def firstRawReadDebit (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) : ℕ :=
  (A.old w).steps+(A.seats w).made.steps+(D.keys w).headers.steps+(D.keys w).dest.steps+
    (D.ports w).seats.steps+
    bootAddressBill (D.ports w) (compileOccurrence (bodyAtActualSlot X gate pad A w).result).native.physical.order

structure FirstBootWordFits where
  laneCodeWidth : ℕ
  ownerWidth : ℕ
  seatLookupWidth : ℕ
  seatLookupRows : ℕ

def actualBootGeometry (m s edges own key prec pg oldRows pages bankRows d : ℕ)
    (U : FirstBootWordFits) : ℕ :=
  (12+edges*bootCopyStride m (Nat.clog 2 s) U.laneCodeWidth)+
    bootMountGeometry own U.ownerWidth (J6R53OldOwnerRoot.SuffixWordWidth m) key prec pg oldRows pages bankRows (max d 2)+
    (3+(oldRows+pages)*(6*U.ownerWidth+8+originWidthFee key prec pg))+
    bootEmitGeometry (2*edges) U.ownerWidth (Nat.clog 2 s) key prec pg U.seatLookupWidth
      (oldRows+pages) U.seatLookupRows

theorem boot_mount_geometry_mono_destination {own w W gw key p pg o pages bk d : ℕ}
    (h : w≤W) :
    bootMountGeometry own w gw key p pg o pages bk d≤bootMountGeometry own W gw key p pg o pages bk d := by
  unfold bootMountGeometry
  have hh := Nat.mul_le_mul_right (o+pages) (show 3*w+6≤3*W+6 by omega)
  omega

theorem actual_joined_boot_scope_fee_from_retained_words
    (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
    (d : ℕ) (hDegree : ∀ u,P.degree u≤d) (U : FirstBootWordFits)
    (hLane : A.width w≤U.laneCodeWidth) (hOwner : D.width w≤U.ownerWidth)
    (hSeatWidth : (D.ports w).seatWidth≤U.seatLookupWidth)
    (hSeatRows : (D.ports w).seats.result.length≤U.seatLookupRows) :
    ((withJoinedBoot X gate pad root M A D B live rootInj).initial w).steps≤
      firstRawReadDebit X gate pad root A D w+
        actualBootGeometry m s (exteriorChild G ell X.centre X.sample X.group).edges own key prec
          (pageKeyWidth m+pad) root.order.length (stagePageOrder X).length B.records.length d U := by
  let E := exteriorChild G ell X.centre X.sample X.group
  let t := (Path.root : Path sel E E).ticket w
  let Y := (joinedSlots X gate pad root A D) w
  let K := D.keys w
  let W := D.ports w
  let R := mountFirstOwners X gate pad root B live K rootInj
  let writer := readFirstPhysical X gate pad A.lanes (A.seats w)
  let order := (compileOccurrence (bodyAtActualSlot X gate pad A w).result).native.physical.order
  let e := J6R48GeneratedAddons.emit (readBootAddon W R.result) order
  let owners := root.order.length+(stagePageOrder X).length
  have aDim : dim t≤Nat.clog 2 s := bits_le_lam _ _
  have shape : J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) (exteriorChild G ell X.centre X.sample X.group).depth≤Nat.clog 2 s := aDim
  have writerBound : writer.steps≤(A.seats w).made.steps+8+
      E.edges*bootCopyStride m (Nat.clog 2 s) U.laneCodeWidth := by
    have qW := actual_first_writer_uses_exact_resident_geometry X gate pad A w
    change writer.steps=_ at qW
    rw [qW]
    refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
    unfold bootCopyStride
    omega
  have localOwners : R.result.raw.length≤owners :=
    (actual_boot_mount_count_from_live_records X gate pad root K B live rootInj).2
  have mountBound : R.steps≤K.headers.steps+K.dest.steps+
      bootMountGeometry own U.ownerWidth (SuffixWordWidth m) key prec (pageKeyWidth m+pad) root.order.length
        (stagePageOrder X).length B.records.length (max d 2) := by
    exact (actual_live_boot_mount_ceiling X gate pad root K B live rootInj d hDegree).trans
      (Nat.add_le_add_left (boot_mount_geometry_mono_destination hOwner) _)
  have typeBound : (projectOriginTape R.result.raw).steps≤
      3+owners*(6*U.ownerWidth+8+originWidthFee key prec (pageKeyWidth m+pad)) := by
    refine (origin_tape_fee_by_actual_length R.result.raw).trans ?_
    apply Nat.add_le_add_left
    exact Nat.mul_le_mul localOwners (by omega)
  have pairSize : order.length=2*E.edges :=
    boot_native_half_port_count (bodyAtActualSlot X gate pad A w).result
  have emitBound : e.steps≤bootAddressBill W order+
      bootEmitGeometry (2*E.edges) U.ownerWidth (Nat.clog 2 s) key prec (pageKeyWidth m+pad) U.seatLookupWidth
        owners U.seatLookupRows :=
    (original_boot_tag_emit_from_word_tables W R.result order).trans (Nat.add_le_add_left
      (boot_emit_geometry_monotone pairSize.le hOwner aDim hSeatWidth localOwners hSeatRows) _)
  have first := (joined_initial_body_and_mount_charged_once X gate pad root M A D B live rootInj w).1
  change ((withJoinedBoot X gate pad root M A D B live rootInj).initial w).steps=
    ((A.old w).steps+writer.steps+4)+R.steps+W.seats.steps+(projectOriginTape R.result.raw).steps+e.steps at first
  rw [first]
  unfold firstRawReadDebit actualBootGeometry
  change _≤((A.old w).steps+(A.seats w).made.steps+K.headers.steps+K.dest.steps+
      W.seats.steps+bootAddressBill W order)+
    ((12+E.edges*bootCopyStride m (Nat.clog 2 s) U.laneCodeWidth)+
    bootMountGeometry own U.ownerWidth (SuffixWordWidth m) key prec (pageKeyWidth m+pad) root.order.length
        (stagePageOrder X).length B.records.length (max d 2)+
    (3+owners*(6*U.ownerWidth+8+originWidthFee key prec (pageKeyWidth m+pad)))+
    bootEmitGeometry (2*E.edges) U.ownerWidth (Nat.clog 2 s) key prec (pageKeyWidth m+pad) U.seatLookupWidth
        owners U.seatLookupRows)
  omega

end
#print axioms firstRawReadDebit
#print axioms boot_mount_geometry_mono_destination
#print axioms actual_joined_boot_scope_fee_from_retained_words
end J6R58BootScope
