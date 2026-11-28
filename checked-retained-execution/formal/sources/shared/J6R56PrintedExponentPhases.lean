import J6R56PrintedExponentLedger
import J6R55CachedLedgerContraction

/-! Explicit conditional caps for the actual cached callbacks. No cap
here is inferred from value correctness, and no fee table is supplied. -/
namespace J6R56PrintedExponent
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R49Cost
open J6R51Online J6R52CacheWhole J6R52Peak J6R53PeakAddon J6R54PeakInput
open J6R55CachedLedger

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3900
set_option maxHeartbeats 26000000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "H" => (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))

structure CachedThreePhaseCaps (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (fixed arithmetic perScope : ℕ) : Prop where
  leaf : ∀ (z : Sigma (Path sel r)) (stop : z.1.edges≤(S).cutoff),
    (readLeaf M initial z.2 stop).steps≤fixed
  active : ∀ (z : Sigma (Path sel r)) (a : (S).cutoff<z.1.edges),
    let A := preparedActive M z.2 a
    cacheMountFee M z.2+A.steps+
      streamActiveTariff A.result (reachable_positive T z.2.reached) T.vPositive≤
      fixed+arithmetic*Nat.card ((P).Slot z.1)
  scope : ∀ (z : Sigma (Path sel r)) (w : (P).Slot z.1),
    cachedScopeOwn M retire initial z.2 w≤perScope

theorem actual_cached_affine_from_phase_caps
    (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (fixed arithmetic perScope : ℕ)
    (caps : CachedThreePhaseCaps M retire initial fixed arithmetic perScope) :
    ∀ z : Sigma (Path sel r),
      cachedOwn M retire initial z≤fixed+(arithmetic+perScope)*Nat.card ((P).Slot z.1) := by
  intro z
  by_cases stop : z.1.edges≤(S).cutoff
  · rw [cachedOwn,dif_pos stop]
    exact (caps.leaf z stop).trans (Nat.le_add_right _ _)
  · letI : Fintype ((P).Slot z.1) := (P).finiteSlot z.1
    have hScope : (∑ w : (P).Slot z.1,cachedScopeOwn M retire initial z.2 w)≤
        perScope*Nat.card ((P).Slot z.1) := by
      calc
        _≤∑ _ : (P).Slot z.1,perScope := Finset.sum_le_sum (fun w _=>caps.scope z w)
        _=_ := by
          rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.mul_comm]
          rfl
    rw [cachedOwn,dif_neg stop]
    exact (Nat.add_le_add (caps.active z (Nat.lt_of_not_ge stop)) hScope).trans (le_of_eq (by ring))

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem actual_cached_physical_output_and_compressed_rate_under_three_phase_caps
    (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L)
    (legal : ReadyOnStack (borns M) initial)
    (leaves : letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) :=
      J6R24MeteredRecursion.sourceDecision sel r; LeafAgreement M initial)
    (fit : r.depth≤pathLimit s C)
    {anchor : Call (PhysicalHost f ell)}
    (stable : Stable s C anchor) (zero : anchor.depth=0) (anchorPrec : anchor.prec≤C*s)
    (link : NativeReach (Plan sel) anchor r)
    (fixed arithmetic perScope scale localPower : ℕ)
    (caps : CachedThreePhaseCaps M retire initial fixed arithmetic perScope)
    (localBound : fixed+(arithmetic+perScope)≤scale*2^(localPower*H)) :
    let out := runCachedRootSingleEmission M retire initial
    (T.frame (Path.root : Path sel r r).reached).decode out.result.1=
      reduce r.prec f ell (r.host.contract hf) ∧ out.result.2=initial ∧
      out.steps≤(pathLimit s C-r.depth+1)*scale*2^((fullPrefixConstant C+localPower)*H) := by
  obtain ⟨value,bank,_⟩ := same_single_emission_exact_contraction_and_actual_occurrence_bill
    M retire initial legal leaves fit
  refine ⟨value,bank,?_⟩
  have ht := actual_cached_absolute_meter_compressed M retire initial legal fit stable zero anchorPrec link
    fixed (arithmetic+perScope) (actual_cached_affine_from_phase_caps M retire initial fixed arithmetic perScope caps)
  refine ht.trans ?_
  calc
    _≤(pathLimit s C-r.depth+1)*(scale*2^(localPower*H))*2^(fullPrefixConstant C*H) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ localBound)
    _=_ := by rw [Nat.add_mul (fullPrefixConstant C) localPower H,pow_add]; ring

#print axioms CachedThreePhaseCaps
#print axioms actual_cached_affine_from_phase_caps
#print axioms actual_cached_physical_output_and_compressed_rate_under_three_phase_caps
end
end J6R56PrintedExponent
