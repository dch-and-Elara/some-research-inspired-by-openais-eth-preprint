import J6R82LeafTimeContext

/-! Same-path stopped-leaf prices. The printed source exponent is unchanged.
The scalar uses actual encoded widths; these are not inferred from mere
value-equivalence of an arbitrary replacement chart. -/
namespace J6R82LeafTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R51Leaf J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
set_option maxRecDepth 8000
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
local notation "deg" => (4*Nat.clog 2 s)
local notation "ch" => (p.ticket w).child

variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
variable (gateWidth : gate.created.val=base)
variable {body arity significant directory : ℕ}


include boot gateWidth in
theorem actual_retained_row_has_uniform_price
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (A : OwnerTerminalInput X p w (sourceState M p w))
    (live : StoppedReadGeometry X M p w B)
    (W : StoppedReadWidths X M p w B A body arity significant directory)
    (u : OldAt T (p.ticket w)) (cmd : Cmd)
    (hit : (compileByOwnerData (ch).edges (cachedBook (sourceState M p w) A.saved).result A.saved.rows
      ((sourceState M p w).site.oldKey u.val)
      (parentData (sourceState M p w) (gateHistory T (bootGates X) p) u.val)).result=some cmd) :
    readCmdFee B deg (ch).prec (ch).edges cmd≤(2^(6*leafH s)*stoppedRowPrefix s C ell key prec tw bw (pageKeyWidth m+pad) body arity significant directory) := by
  let Y := sourceState M p w
  let book := (cachedBook Y A.saved).result
  let who := Y.site.oldKey u.val
  let origin := Y.origins u.val
  let walk := Path.step p w
  obtain ⟨ex,pCap,eCap,_⟩ := stopped_native_sizes X M p w B live
  have k := actual_old_sources_from_one_printed_boot X M gate boot p w gateWidth u
  dsimp only [compileByOwnerData,parentData] at hit
  cases k with
  | original x tr eq code =>
    rw [code] at hit
    obtain ⟨g,rfl,gArity⟩ := compiled_old_gate_has_its_actual_width_and_arity (ch).edges book A.saved.rows who _ cmd hit
    let K := commonSize s C body arity significant directory
    have kEq : K=1+deg+regulator s C+3*(C*s)+3*(C*s)*regulator s C+2*s+
        body+arity+significant+directory := rfl
    have nK : (ch).edges≤K := by omega
    have pK : (ch).prec≤K := by omega
    have observed := actual_input_gate_has_observed_arity X M p w A u _ code
    have gK : gatePorts g≤K := (gArity.trans_le (observed.trans W.gates)).trans (by omega)
    have row :=
      true_gate_fits_the_same_uniform_scalar B deg (ch).prec (ch).edges (ch).edges g
        (Nat.clog 2 s) K (commonSize_pos s C body arity significant directory)
        (by omega) pK nK nK gK
    exact row.trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide : 0 < (2 : ℕ))))
  | exterior k tr tag eq noGate =>
    rw [noGate] at hit
    obtain ⟨pg,dep,wires,h,rfl⟩ := retained_page_compile_address book A.saved.rows who origin cmd hit
    have localRead := actual_kept_page_limited_by_its_paid_book X M p w A u origin.stamp.creator pg dep wires hit
    have price : ∀ rc : CurrentPacketReceipt B origin.stamp.creator pg s C deg (ch).prec (ch).edges dep wires,
        readCmdFee B deg (ch).prec (ch).edges (.packet origin.stamp.creator pg dep wires)≤(2^(6*leafH s)*stoppedRowPrefix s C ell key prec tw bw (pageKeyWidth m+pad) body arity significant directory) :=
      fun rc=>same_stopped_packet_price X M p w B A live W _ _ _ _ rc localRead.1 localRead.2.1 localRead.2.2
    apply price
    change origin=_ at tag
    rw [tag] at h ⊢
    have pgEq := Option.some.inj h
    rw [←pgEq]
    exact Classical.choice (true_exterior_creator_for_this_address X live.nativeSize live.printedSize
      live.rootBase pad k B live.rootLive deg (ch).prec (ch).edges dep wires cfg)
  | native anc noGate =>
    rw [noGate] at hit
    obtain ⟨pg,dep,wires,h,rfl⟩ := retained_page_compile_address book A.saved.rows who origin cmd hit
    have localRead := actual_kept_page_limited_by_its_paid_book X M p w A u origin.stamp.creator pg dep wires hit
    have price : ∀ rc : CurrentPacketReceipt B origin.stamp.creator pg s C deg (ch).prec (ch).edges dep wires,
        readCmdFee B deg (ch).prec (ch).edges (.packet origin.stamp.creator pg dep wires)≤(2^(6*leafH s)*stoppedRowPrefix s C ell key prec tw bw (pageKeyWidth m+pad) body arity significant directory) :=
      fun rc=>same_stopped_packet_price X M p w B A live W _ _ _ _ rc localRead.1 localRead.2.1 localRead.2.2
    apply price
    have tag := anc.tag
    change origin=_ at tag
    rw [tag] at h ⊢
    have pgEq := Option.some.inj h
    rw [←pgEq]
    let O := sourceState M anc.atHome anc.slot
    have used : OnPath (borns M) (compileOccurrence O.input).job walk := .inherited p w anc.own
    exact Classical.choice (real_native_creator_for_this_address anc.atHome anc.slot O.input anc.pageId
      walk (borns M) used (IsLive (X.seed pad)) B live.livePath ex deg (ch).prec (ch).edges dep wires)

theorem actual_fresh_row_has_uniform_price
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (A : OwnerTerminalInput X p w (sourceState M p w))
    (live : StoppedReadGeometry X M p w B)
    (W : StoppedReadWidths X M p w B A body arity significant directory)
    (k : PageAt T (p.ticket w)) :
    readCmdFee B deg (ch).prec (ch).edges (freshWord (sourceState M p w) k)≤(2^(6*leafH s)*stoppedRowPrefix s C ell key prec tw bw (pageKeyWidth m+pad) body arity significant directory) := by
  let Y := sourceState M p w
  let ws : List WireRead := (freshList Y k).map
    (fun h=>⟨freshBody h,List.replicate (freshOrdinal Y k h).val true⟩)
  have ex := (stopped_native_sizes X M p w B live).1
  have used : OnPath (borns M) (compileOccurrence Y.input).job (.step p w) := .youngest p w rfl
  obtain ⟨rc⟩ := real_native_creator_for_this_address p w Y.input k (.step p w) (borns M)
    used (IsLive (X.seed pad)) B live.livePath ex deg (ch).prec (ch).edges 0 ws
  have opens := actual_fresh_page_limited_by_its_paid_book X M p w A k
  exact same_stopped_packet_price X M p w B A live W _ _ 0 ws rc (Nat.zero_le _) opens.1 opens.2

#print axioms actual_retained_row_has_uniform_price
#print axioms actual_fresh_row_has_uniform_price
end
end J6R82LeafTime