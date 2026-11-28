import J6R94HeldOwnerProviderSameScope
import J6R94HeldOwnerProviderFinalStop
import J6R65LeafRateCombine

namespace J6R94HeldOwnerProvider
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

open J6R52CacheWhole J6R51ParentFrames J6R82LayoutDebit J6R82LeafTime
open J6R9Recursive J6R58LeafScale J6R16ModeCost J6R14LayoutCost J6R68ActiveInputs
open V8NativeMessage.N2DLabels J6R10Repack
local instance finalScopeEdge : Fintype c.host.Edge := c.host.finiteEdge

open J6R59Public J6R27OriginalGate J6R30ProducedGateRegistry J6R52CacheSource

/-- The extra complete-roster acquisition is uniformly cubic in the
common physical-width envelope used by the outer phase profile. -/
theorem kept_owner_budget_is_cubic {K V₀ s C : ℕ} (hV : V₀≤K) (hs : s≤K) (hC : C≤K) :
    keptOwnerBudget K (V₀+4*(C*s))≤(536+5*(fitWord 6 []).steps)*(K+1)^3 := by
  let F := (fitWord 6 []).steps
  have hCs := Nat.mul_le_mul hC hs
  have vv : V₀+4*(C*s)≤5*(K+1)^2 := by nlinarith
  have coeff : 3*K+6+groupHeaderUnit K K≤(53+F)*(K+1) := by
    calc
      _ = 22*K+(53+F) := by unfold groupHeaderUnit F; ring
      _ ≤ (53+F)*K+(53+F) := Nat.add_le_add_right (Nat.mul_le_mul_right K (by omega)) _
      _ = (53+F)*(K+1) := by ring
  have const₁ : 1≤(K+1)^3 := Nat.succ_le_of_lt (by positivity)
  have const15 : 15≤15*(K+1)^3 := by simpa using Nat.mul_le_mul_left 15 const₁
  unfold keptOwnerBudget
  calc
    _ ≤ 256*(K+1)^3+15*(K+1)^3+((53+F)*(K+1))*(5*(K+1)^2) :=
      Nat.add_le_add (Nat.add_le_add_left const15 _) (Nat.mul_le_mul coeff vv)
    _ = (536+5*(fitWord 6 []).steps)*(K+1)^3 := by unfold F; ring

section ActualNext
variable (u : (Plan sel).Slot (p.ticket w).child)
variable (K : Meter (HeldOwnerLoad (sourceState M p w) (u:=u) (gateHistory T (bootGates X) p)))
variable (cache : CachedParentFrames (sourceState M p w).site)
variable (keys : NativeCreationOwnerContext (sourceState M p w) K.result.load)
variable (picked : K.result.load=(M.demand (sourceState M p w) u).result)
variable (inj : Function.Injective (sourceState M (.step p w) u).site.oldKey)
local instance finalScopeChildEdge : Fintype (p.ticket w).child.host.Edge := (p.ticket w).child.host.finiteEdge
variable (I : CallFormat (printedParams (f:=f) (ell:=ell) s) (p.ticket w).child)
variable (W : Ingress I) (units : ℕ) {a cp wid edges : ℕ}
variable (raw : KeptLayoutWords a cp wid edges) (axisBits : List Bool)
variable (same : ExistingRosterLabels (sourceState M (.step p w) u) (gateHistory T (bootGates X) (.step p w))
  (rosterActuallyCarriedToNext X M p w u K cache keys picked) I W units raw.rawView axisBits)

variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (bad : Meter (Block (T.frame (Path.step (Path.step p w) u).reached) ell))

/-- A single true successful child scope. Paid producer charges and the
actual reader use one live child Bank; only the matched geometry and
previously held input tapes are premises. -/
theorem actual_published_kept_positive_scope_is_correct_with_a_uniform_leaf_tariff
    (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
    (gateWidth : gate.created.val=base) (hBase : 0<base)
    (initial : Bank) (live : IsLive (X.seed pad) initial) (legal : ReadyOnStack (borns M) initial)
    (ready : JobsReady (stackBank (borns M) initial (.step p w))
      [(cachedAdvance (sourceState M p w) u K.result.load cache).next.birth.job])
    (stop : ((Plan sel).child (p.ticket w).child u).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (positive : 0<((Plan sel).child (p.ticket w).child u).edges)
    {K0 body arity significant : ℕ}
    (widths : LocalOwnerGeometry X (.step p w) u (sourceState M (.step p w) u) K0)
    (bodyFit : observedFrameWidth (mountResident (sourceState M (.step p w) u)
      (moveResidentToSource (X:=X) (prior_held_load_is_same_next_source X M p w u K cache picked)
        (installResidentBank (cachedAdvance (sourceState M p w) u K.result.load cache).next).result)).result.rows≤body)
    (gateFit : observedGateWidth (rosterActuallyCarriedToNext X M p w u K cache keys picked).raw≤arity)
    (encoding : ActualEncodingFits (stackBank (borns M) initial (.step (.step p w) u)) significant)
    (hn : native≤m) (hs : s=physicalSize m native) (baseFit : base≤C*s) :
    let B := stackBank (borns M) initial (.step p w)
    let next := (cachedAdvance (sourceState M p w) u K.result.load cache).next
    let job := next.birth.job
    let write := J6R48GeneratedAddons.emit (K.result.load.directory.read (sourceState M p w) K.result.load.event)
      next.birth.native.physical.order
    let resident := installResidentBank next
    let output := visitActualHeldPositiveRead X M p w u K cache keys picked inj I W units raw axisBits same retire bad B
    let prep := stoppedPreparationCoefficient (pad:=pad) (s:=s) (C:=C) X K0 K0 body arity
    let reader := stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
      (initial.records.length+pathLimit s C)
    let leaf := combinedLeafBound (s:=s) (C:=C) X
      (keptOwnerBudget K0 (vertexCount (ext).host+4*(C*s))) prep reader 6
    let child := (p.ticket w).child
    let target := (Plan sel).child child u
    (T.frame (Path.step (Path.step p w) u).reached).decode output.result.1=
      reduce target.prec f ell (target.host.contract X.hf) ∧ output.result.2=B ∧
      output.steps≤(K.steps+(write.steps+resident.steps))+
        (publishFee B job.entry job.offset job.built+(leaf+6)+retire job+4) := by
  let next := (cachedAdvance (sourceState M p w) u K.result.load cache).next
  let resident := (installResidentBank next).result
  let atOwn := moveResidentToSource (X:=X) (prior_held_load_is_same_next_source X M p w u K cache picked) resident
  let owners := rosterActuallyCarriedToNext X M p w u K cache keys picked
  have h := executed_scope_feeds_the_real_R65_positive_reader X M p w u K cache keys picked inj I W units raw
    axisBits same retire bad initial ready
  have fee := direct_actual_R65_kept_stop_correct_at_uniform_tariff X M (.step p w) u gate boot gateWidth hBase initial live legal stop positive atOwn owners inj I W units raw axisBits same widths bodyFit gateFit encoding hn hs baseFit
  dsimp only at h ⊢
  rw [h]
  exact ⟨fee.1,rfl,Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.add_le_add_right fee.2 6) _) _) 4) _⟩

end ActualNext
#print axioms kept_owner_budget_is_cubic
#print axioms actual_published_kept_positive_scope_is_correct_with_a_uniform_leaf_tariff
end
end J6R94HeldOwnerProvider