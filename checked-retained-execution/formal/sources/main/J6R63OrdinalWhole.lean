import J6R63OrdinalDescendants

/-! One ranked descendant runner. It actually consumes the words of
each inside-pulse callback to acquire a checked local child packet,
then uses the original single-emission scoped transition. The root
boot and stopping leaf operations are the previous source operations.
The computational interface has no old demand or whole tuple menu. -/
namespace J6R63Ordinal
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active J6R15ModeCost J6R16ModeCost
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R48RawRoute
open J6R51ParentFrames J6R51Online J6R52CacheWhole J6R54PeakInput
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4900
set_option maxHeartbeats 10000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q b : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "PlanAt" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Here" => (Path.root : Path sel r r)

variable {B : Base T key prec tw bw page (q+1)}

def runRoot (D : Program B b) (retire : J→ℕ) :
    SM L (Block (T.frame (Here).reached) ell) :=
  fun bank=>
    if stop : r.edges≤(SP).cutoff then
      let v := B.leafRoot stop bank
      ⟨(v.result,bank),v.steps⟩
    else
      let on := Nat.lt_of_not_ge stop
      let d := ready_reachable cfg sel (Here).reached T.rootStable on
      let A := B.activeRoot on
      let out := A.result.eval B.modeWidth (reachable_positive T (Here).reached) T.vPositive hf
        (fun t z β g=>
          let w := addressed (sel:=sel) d t z β g
          project (bootBankDemand (B.initial w) retire (runFrom D retire r Here w)
            (zeroM (T.bank (registerPrecision SP r t) (register_positive d t)).hp) bank))
      ⟨(out.result,bank),A.steps+out.steps⟩

theorem ranked_root_restores_the_same_bank (D : Program B b) (retire : J→ℕ) (bank : L) :
    (runRoot D retire bank).result.2=bank := by
  by_cases stop : r.edges≤(SP).cutoff
  · rw [runRoot,dif_pos stop]
  · rw [runRoot,dif_neg stop]

#print axioms runRoot
#print axioms ranked_root_restores_the_same_bank
end
end J6R63Ordinal
