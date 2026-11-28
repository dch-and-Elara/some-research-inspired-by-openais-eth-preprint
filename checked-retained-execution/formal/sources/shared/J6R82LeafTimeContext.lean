import J6R82LeafTimeUniform
import J6R65LeafRatePositive
import J6R66LeafTariffRegistry
import J6R58LeafScalePrecision

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
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
set_option maxRecDepth 5500
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

def stoppedRowPrefix (s C ell key prec tw bw page body arity significant directory : ℕ) : ℕ :=
  rowPrefix ell key prec tw bw page (Nat.clog 2 s) (commonSize s C body arity significant directory)
    (commonSize_pos s C body arity significant directory)

structure StoppedReadWidths (B : Bank) (A : OwnerTerminalInput X p w (sourceState M p w))
    (body arity significant directory : ℕ) : Prop where
  frame : observedFrameWidth A.saved.rows≤body
  gates : observedGateWidth A.roster.raw≤arity
  encoding : ActualEncodingFits B significant
  records : B.records.length≤directory

structure StoppedReadGeometry (B : Bank) : Prop where
  nativeSize : native≤m
  printedSize : s=physicalSize m native
  rootBase : base≤C*s
  rootLive : IsLive (X.seed pad) B
  livePath : opened (borns M) (IsLive (X.seed pad)) (.step p w) B

theorem stopped_native_sizes (B : Bank) (live : StoppedReadGeometry X M p w B) :
    (ext).prec≤161*C*s^2 ∧ (ch).prec≤regulator s C ∧ (ch).edges≤C*s ∧ 1<s := by
  have ample : 1024≤Nat.clog 2 s := by rw [live.printedSize]; exact physical_exterior_source_lambda_large m native live.nativeSize
  have s₀ : 1<s := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).1
    (show 0<Nat.clog 2 s from (by decide : (0:ℕ)<1024).trans_le ample)
  have b : base≤C*physicalSize m native := by simpa only [←live.printedSize] using live.rootBase
  have ex : (ext).prec≤161*C*s^2 := by
    simpa only [←live.printedSize] using
      literal_exterior_start_precision_quadratic X live.nativeSize cfg.constPos b
  have pmax := (actual_leaf_field_width_and_vertices (T:=T) (Path.step p w)).2.1
  have pp : (ch).prec≤regulator s C := calc
    _≤(ext).prec+160*C*s^2 := pmax
    _≤161*C*s^2+160*C*s^2 := Nat.add_le_add_right ex _
    _=_ := by unfold regulator; ring
  exact ⟨ex,pp,actual_source_path_edges_le (cfg:=cfg) sel T.rootStable (.step p w),s₀⟩

include cfg in
theorem same_stopped_packet_price
    (B : Bank) (A : OwnerTerminalInput X p w (sourceState M p w))
    (live : StoppedReadGeometry X M p w B)
    {body arity significant directory : ℕ}
    (W : StoppedReadWidths X M p w B A body arity significant directory)
    (addr : Word key) (pg : Word (pageKeyWidth m+pad))
    (dep : ℕ) (wires : List WireRead)
    (src : CurrentPacketReceipt B addr pg s C deg (ch).prec (ch).edges dep wires)
    (hdep : dep≤observedFrameWidth A.saved.rows) (num : wires.length≤(ch).edges)
    (raw : ∀ a, rawWireFee (dep+a+2) wires≤(ch).edges*(3*(observedFrameWidth A.saved.rows)+
      4*(ch).edges+(observedFrameWidth A.saved.rows+a+2)+12)) :
    readCmdFee B deg (ch).prec (ch).edges (.packet addr pg dep wires)≤
      2^(6*leafH s)*stoppedRowPrefix s C ell key prec tw bw (pageKeyWidth m+pad)
        body arity significant directory := by
  obtain ⟨_,bound,edge,sz⟩ := stopped_native_sizes X M p w B live
  exact generated_command_bounded_at_its_real_page B addr pg s C deg (ch).prec (ch).edges dep wires
    src X.hf cfg.coefficient sz body arity significant directory W.encoding W.records
    bound edge (hdep.trans W.frame) num (fun a=>(raw a).trans (by gcongr <;> exact W.frame))

#print axioms stopped_native_sizes
#print axioms same_stopped_packet_price
end
end J6R82LeafTime