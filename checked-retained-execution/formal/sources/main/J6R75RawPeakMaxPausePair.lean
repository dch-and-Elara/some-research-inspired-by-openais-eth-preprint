import J6R75RawPeakMaxPauseRun

/-! A concrete maximum with the old publication/mount/return cuts;
no free choice of an "old payload" is needed at this endpoint. -/
namespace J6R75RawPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R62Leaf J6R54TerminalBoot J6R52Terminal J6R22Active J6R53TerminalGate
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R30ProducedGateRegistry J6R68.RecursivePeak J6R68ActiveInputs.Sweep
open J6R62ActivePrep J6R68ActiveInputs J6R68.LeafPeak.Packet J6R18ChildWrite
open J6R52Peak J6R54PeakInput J6R51Peak J6R57ScopeFee J6R66.BootPeak J6R50Peak
open J6R68.RetireScratch J6R72SameRunLocalPeak J6R12CollisionEdges J6R12CollisionGraphScore
open J6R12CollisionGreedyStep J6R12CollisionMenu J6R12CollisionSource J6R14LayoutCost J6R10Repack
open J6R12CollisionPacking P11FullPacking V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 37000000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams

def GreedyWindowAtOldMaximum {E R C : Type*} [Fintype E] [Fintype R] [Fintype C]
    {a : ℕ} {N : Network E R C} (I : Full64Input N a) (W : Ingress I)
    (pre : List (R⊕C)) (target : R⊕C) (post : List (R⊕C))
    (resident roof oldBits oldRoom : ℕ) : Prop :=
  let F := I.format
  let start := initGraph F.kR F.kC W.paid.result.2
  let out := drive F.e F.kR F.kC F.b W.paid.result.1 start.result
  ∃ (first : Fin a→Fin 64) (rest : List (Fin a→Fin 64)),
    let ordered := J6R12CollisionRun.run F.width F.kR F.kC F.b F.literals (F.label first) (rest.map F.label)
    let previous := ordered (pre.map F.target) start.result
    let p := (J6R12CollisionRun.spec F first rest pre (fun _=>none)).1
    let choose := chooseAndWrite F.width F.kR F.kC F.b F.literals previous.result.1 (F.target target)
      (F.label first) (rest.map F.label)
    let next := ordered (post.map F.target) choose.result.1
    let held := resident+(rawLayoutBits rawLayoutTargetBits W.paid.result.1+
      rawLayoutBits rawIncidenceLayoutBits W.paid.result.2+rawLayoutBits rawEdgeLayoutBits start.result+
      gridMemoryBits (menuMachine F.b).result+gridMemoryBits previous.result.2)
    let room := roof+candidateIngressRoom F.kR F.kC F.b I.order.length (Fintype.card E) pre.length
    let maximum := max oldRoom
      (room+candidateControlWords F.b F.width+candidateTallyRoom F.kR F.kC F.b F.width (Fintype.card E))
    out=⟨(next.result.1,previous.result.2++choose.result.2::next.result.2),
      (menuMachine F.b).steps+(literalSeed F.width F.b).steps+(previous.steps+choose.steps+next.steps+2*F.b+6)+8⟩ ∧
    previous.result.1=F.graph p ∧
    ∀ label : Fin a→Fin 64, ∃ control,
      ((label=first ∧ control=layoutEntryWidth
          ⟨F.label first,(computeCandidate F.width F.kR F.kC F.b F.literals previous.result.1
            (F.target target) (F.label first)).result⟩) ∨
        ∃ prior suffix, rest=prior++label::suffix ∧
          control=actualLaterCandidateControls F p target first prior label) ∧
      control≤candidateControlWords F.b F.width ∧
      ∀ left x right,candidatePairTape F p target label=left++x::right →
        max oldBits (held+control+candidateTallyPayload F p target label left x right)≤maximum

theorem actual_controlled_layout_combines_with_the_given_bounded_cut
    {E R C : Type*} [Fintype E] [Fintype R] [Fintype C]
    {a : ℕ} {N : Network E R C} {I : Full64Input N a} {W : Ingress I}
    {pre : List (R⊕C)} {target : R⊕C} {post : List (R⊕C)}
    {resident roof oldBits oldRoom : ℕ}
    (greedy : ControlledGreedyIngressWindow I W pre target post resident roof)
    (oldFit : oldBits≤oldRoom) :
    GreedyWindowAtOldMaximum I W pre target post resident roof oldBits oldRoom := by
  obtain ⟨first,rest,ran,prior,got⟩ := greedy
  refine ⟨first,rest,ran,prior,?_⟩
  intro label
  obtain ⟨_,_,control,observed,cap,cuts⟩ := got label
  refine ⟨control,?_,cap,?_⟩
  · rcases observed with human|after
    · refine Or.inl ⟨human.1,?_⟩
      rw [prior]
      exact human.2
    · exact Or.inr after
  · intro left x right split
    exact (cuts left x right split).2 oldBits oldRoom oldFit

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Pg" => (pageKeyWidth m+pad)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Mach" => (OnlineMachine T key prec tw bw Pg rate)
local notation "JetReserve" => (pathLimit s C*rawAncestorJetRoof
  s C ell f.natDegree (absolutePrecision s (Ext).edges (Ext).prec))

theorem actual_raw_scope_and_actual_layout_tally_share_the_maximum_of_their_pauses
    (M : Mach) (basePos : 0<base) (ord : Fin (Ext).edges≃(Ext).host.Edge)
    (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
    (D : CurrentLayoutSources T key prec tw bw Pg rank X.header.result)
    (fit : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (on : (SP).cutoff<c.edges),
      InputFits sel (readyAtPath T p on) rate)
    (chart : MountedChart T) {width : ℕ} (tails : SavedDirectoryTails width)
    (B : Bank) (own : OwnsHeader X.header.result B) (shared pageBound fixed addr seed owner : ℕ)
    (observed : ActualRawExteriorMaximalNamedPause X M basePos ord ownerInputs D fit chart tails B own
      shared pageBound fixed addr seed owner) :
    let R := withPaidOwnerLeaves X M basePos ord ownerInputs
    let F := D.retained fit
    let E := D.rootInputs (readExterior X)
    let baseRoof := rawCarrierRoof shared B Ext pageBound fixed addr seed owner s C rate
    ∃ carry : ∀ {j : Call (PhysicalHost f ell)},Path sel Ext j→ℕ,
    ∀ {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (on : (SP).cutoff<c.edges)
      (w : (P).Slot c) (_active : (SP).cutoff<((P).child c w).edges)
      (j u : ℕ) (point : ChildWritePoint),
      letI := c.host.finiteEdge
      letI := c.host.finiteRow
      letI := c.host.finiteCol
      let next := Path.step p w
      let input := literalStockCapturesAt R F E B own p on
      let words := input.2.1.result
      let W := D.atPath R B own p on
      let carrier := recursiveResidentBits shared R B p (carry p)+exactAncestorJetWidth R F chart E B own p
      let held := carrier+(words.precision.bits.length+words.edges.bits.length+gridMemoryBits chart.table.raw)
      let room := (baseRoof+JetReserve)+(prec+input.1+f.natDegree*chart.count)
      let k := carry next
      let oldBits := max (recursiveStagingBits R B p w shared k point)
        (max (max (filterBits R B p w shared k j) (framePrefixBits R B p w shared k u))
          (trueRawReturnWithCarry R B p w shared k (⟨tails,tails⟩ : TailCopyObservation width)))+
        exactAncestorJetWidth R F chart E B own next
      let oldRoom := baseRoof+max ((2*(C*s))*(addr+sourceBodyCap s C seed)) (4*width)+JetReserve
      input.2.2=W.run ∧
      ∀ pre target post,W.input.order=pre++target::post →
        GreedyWindowAtOldMaximum W.input W.bytes pre target post held room oldBits oldRoom := by
  obtain ⟨_,_,carry,paths,slots⟩ := observed
  refine ⟨carry,?_⟩
  intro c p on w active j u point
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  obtain ⟨exactRun,go⟩ := (paths p).2.2.2.2 on
  have scope := (slots p w).1
  have bounded := (scope.2.2.2.2.2 active j u point).2
  refine ⟨exactRun,?_⟩
  intro pre target post split
  exact actual_controlled_layout_combines_with_the_given_bounded_cut (go pre target post split).2 bounded

#print axioms actual_controlled_layout_combines_with_the_given_bounded_cut
#print axioms actual_raw_scope_and_actual_layout_tally_share_the_maximum_of_their_pauses
end
end J6R75RawPeak
