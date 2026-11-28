import J6R102FinalPhaseHeldJoin

/-! Merge the genuinely held positive branch with the two original
small stop readers. The only retained root/zero budgets concern their
actual command reads and zero-book setup, never the whole leaf Meter. -/
namespace J6R102FinalPhase
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
open J6R52CacheWhole J6R82LeafTime J6R9Recursive J6R16ModeCost J6R94HeldOwnerProvider
open J6R102FinalPhase.HeldWiring
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 29000000
set_option maxRecDepth 4900
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
variable (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local instance stoppingDecision : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) (Ext)) :=
  J6R24MeteredRecursion.sourceDecision sel Ext
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (provide : OwnerInputProvider (T:=T) (pad:=pad) X)
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges ≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
variable (gateWidth : gate.created.val=base)
local notation "R" => (withPaidOwnerLeaves X M basePos ord provide)
local notation "Height" => (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))

include boot gateWidth in
theorem all_literal_stops_from_original_readers_and_held_owners
    (live : IsLive (X.seed pad) initial) (legal : ReadyOnStack (borns M) initial)
    (K body arity significant : ℕ)
    (hn : native ≤ m) (hs : s=physicalSize m native) (baseFit : base ≤ C*s)
    (positive : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (w : (Plan sel).Slot c)
      (stop : ((Plan sel).child c w).edges ≤ (SP).cutoff),
      0<((Plan sel).child c w).edges →
        Nonempty (HeldAtStop X M initial provide p w stop K body arity significant))
    (rootWords : (Ext).edges ≤ (SP).cutoff →
      rootLiteralBill X M basePos ord initial ≤ stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X
        body arity significant (initial.records.length+pathLimit s C)*2^(6*Height))
    (zeroWords : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (w : (Plan sel).Slot c),
      ((Plan sel).child c w).edges=0 →
        zeroBookSetup p w (sourceState M p w) ≤ stoppedPreparationCoefficient (pad:=pad) (s:=s) (C:=C) X K K body arity ∧
        zeroLiteralBill X M basePos p w initial ≤ stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X
          body arity significant (initial.records.length+pathLimit s C)*2^(6*Height)) :
    let provider := localOwnerBudget K (vertexCount (Ext).host+4*(C*s))
    let prep := stoppedPreparationCoefficient (pad:=pad) (s:=s) (C:=C) X K K body arity
    let reader := stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
      (initial.records.length+pathLimit s C)
    HasMeasuredOwnerInputs X M provide ∧ ∀ (z : Sigma (Path sel Ext)) (stop : z.1.edges ≤ (SP).cutoff),
      (readLeaf R initial z.2 stop).steps ≤ combinedLeafBound (s:=s) (C:=C) X provider prep reader 6 := by
  let ar := sourceArithmetic s C (Ext)
  let provider := localOwnerBudget K (vertexCount (Ext).host+4*(C*s))
  let prep := stoppedPreparationCoefficient (pad:=pad) (s:=s) (C:=C) X K K body arity
  let reader := stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
    (initial.records.length+pathLimit s C)
  have sameSupply : HasMeasuredOwnerInputs X M provide := by
    intro c p w stop pos
    obtain ⟨A⟩ := positive p w stop pos
    exact selected_held_provider_returns_the_real_owner_data X M initial provide p w stop A
  refine ⟨sameSupply,?_⟩
  rintro ⟨_,path⟩ stop
  cases path with
  | root =>
    have fee := actual_root_run_has_printed_leaf_factor X M basePos ord provide initial live stop
    have m := structural_leaf_fee_into_printed_rate (provider:=0) (setup:=0)
      (bill:=rootLiteralBill X M basePos ord initial) (arithmetic:=ar) (H:=Height)
      (Bprep:=prep) (Bread:=reader) (K:=6) (Nat.zero_le _) (rootWords stop)
    simp only [finiteStopFee,Nat.zero_add] at m
    exact (fee.trans m).trans (Nat.le_add_left _ _)
  | step p w =>
    by_cases empty : ((Plan sel).child _ w).edges=0
    · have fee := actual_zero_leaf_pays_true_book_and_one_assignment X M basePos ord provide
        p w initial live legal stop empty
      obtain ⟨ps,rb⟩ := zeroWords p w empty
      let setup := zeroBookSetup p w (sourceState M p w)
      let bill := zeroLiteralBill X M basePos p w initial
      have basic : setup+bill+ar ≤ finiteStopFee 0 setup bill ar Height := by
        unfold finiteStopFee
        simp only [Nat.zero_add,Nat.add_assoc]
        exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by positivity)) _
      have m := structural_leaf_fee_into_printed_rate (provider:=0) (arithmetic:=ar)
        (H:=Height) (setup:=setup) (bill:=bill) (Bprep:=prep) (Bread:=reader) (K:=6) ps rb
      simp only [Nat.zero_add] at m
      exact ((fee.trans basic).trans m).trans (Nat.le_add_left _ _)
    · have pos := Nat.pos_of_ne_zero empty
      obtain ⟨A⟩ := positive p w stop pos
      exact the_real_positive_stop_has_the_R94_tariff X M initial provide p w stop basePos ord
        gate boot gateWidth live legal pos A hn hs baseFit

#print axioms all_literal_stops_from_original_readers_and_held_owners
end
end J6R102FinalPhase

