import J6R26DescriptorTreeWhole
import J6R25PreparedSupplyWhole

/-! Add the same actual chronological byte stage to the R25 mode-funded
runner. Only the real header assembly/acquisition, original prepared
arithmetic and R25 produced catalogue/dispatch are billed here. -/
namespace J6R26DescriptorTree
open scoped Polynomial BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R25PreparedSupply J6R16ModeCost

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Input cfg sel r hf)
variable {w b dep p tc tz tm : ℕ}
variable (L : ByteSupply T.prepared w b dep p tc tz tm)

noncomputable def fundedSchedule {key : ℕ} (seed : LedgerState key) :
    Meter (LedgerState key×Option (Block (T.prepared.frame (.reflexive _)) ell)) :=
  scheduleThenRun seed (preparedJobs T.prepared L) (fun _=>T.run r (.reflexive _))

variable [DecidableEq (Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

set_option maxHeartbeats 2900000 in
theorem funded_descriptor_tree {key : ℕ} (hk : 0<key) (seed : LedgerState key) (good : seed.good)
    (fit : seed.last.val+(preparedJobs T.prepared L).length<2^key) :
    let run := fundedSchedule T L seed
    let core := T.run r (.reflexive _)
    let N := preparedJobs T.prepared L
    run.result.2=some core.result ∧
      (T.prepared.frame (.reflexive _)).decode core.result=reduce r.prec f ell (r.host.contract hf) ∧
      run.result.1.bank=(historyRows seed.last N).reverse++seed.bank ∧
      run.steps=scheduleFee seed.last (fetchFee seed.bank) N+
        (∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r T.prepared.localAt j)+
        (∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r T.modeAt j)+4 := by
  let Q := preparedJobs T.prepared L
  have h := queue_exact hk seed Q good fit
  have exactRun := sequence_success seed Q (fun _=>T.run r (.reflexive _)) h.ok
  have hs := whole_produced_modes T
  dsimp only [fundedSchedule]
  rw [exactRun]
  refine ⟨rfl,hs.1,h.rows,?_⟩
  have H := relative_prepared_bill T.prepared
  change (emitJobs seed Q).steps+(T.run r (.reflexive _)).steps+4=_
  rw [h.paid,hs.2,H]
  dsimp only [Q]
  omega

#print axioms funded_descriptor_tree
end J6R26DescriptorTree

