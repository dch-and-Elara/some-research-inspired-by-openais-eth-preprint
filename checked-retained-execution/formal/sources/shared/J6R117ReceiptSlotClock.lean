import J6R117ReceiptOuterClock

/-! The physical group operation is a metered, verified receipt on
the same original point and frame. This interface supports the new
kept-owner continuation without equating its running time to the old
machine. No proof-side group or value is run a second time. -/
namespace J6R114PrescribedReceipts
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath J6R35GatewayPreparation
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R66.BootPeak
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R36SharedGateway J6R19Retained AOracleMachineTimeTape A1R10 A1R12
open J6R34OfficialGateway J6R68AbsolutePrescribed
open J6R33OriginalJ6 J6R25StableCensus J6R22RootReadout J6R11Repack J6OrientedHostEval
open J6R63Active J6R62ActivePrep J6R14ZeroMode


set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 26000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)

variable (frame : Frame f (J6SourcePrecision.printed m base)) (hv : 0<ell)

variable (executeGroups : ActualGroupReceipts (W:=W) D)

open J6R75OuterTime

def actualReceiptSlotRoof (groupCap : ℕ) : ℕ :=
  let p := J6SourcePrecision.printed m base
  headRoof m native tc tj tw+
    64*(groupCap+boxFee f.natDegree ell p p+4)+tupleExtra f.natDegree ell p 64+3

theorem the_same_outer_slots_cost_their_actual_groups_and_arithmetic
    (groupCap : ℕ)
    (cap : ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
      (executeGroups i j g (prepareHead W i j).result rfl).run.steps≤groupCap)
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (raw : List Bool) :
    (actualReceiptSlot (W:=W) D frame hv executeGroups i j raw).steps≤
      actualReceiptSlotRoof (m:=m) (native:=native) (tc:=tc) (tj:=tj) (tw:=tw)
        (f:=f) (base:=base) (ell:=ell) groupCap := by
  let H := prepareHead W i j
  let R := fun g=>executeGroups i j g H.result rfl
  let E := SiteFrame G ell frame i
  let p := J6SourcePrecision.printed m base
  let B := groupCap+boxFee f.natDegree ell p p+4
  have head : H.steps≤headRoof m native tc tj tw := by
    have fee := query_head_exact_fee W i j
    change H.steps=_ at fee
    rw [fee,headRoof]
    have indexBound : index m i ≤ 2*m+1 := by
      have h := i.isLt
      unfold index
      omega
    have first := ordinal_fee_monotone tc indexBound
    have next := ordinal_fee_monotone tj (Nat.le_of_lt_succ j.isLt)
    omega
  let groups := fun g=>groupOnSite G D.hf frame i j g (R g)
  have each (g : Fin 64) : (groups g).steps≤B := by
    have copy := (group_on_site_exact G D.hf frame i j g (R g)).2
    change (groups g).steps≤(R g).run.steps+
      boxFee f.natDegree ell (exteriorChild G ell i j g).prec (exteriorChild G ell i j g).prec+4 at copy
    have tariff := congrArg (fun n : Nat=>boxFee f.natDegree ell n n)
      (show (exteriorChild G ell i j g).prec=p from G.precision ell i)
    change boxFee f.natDegree ell (exteriorChild G ell i j g).prec (exteriorChild G ell i j g).prec=
      boxFee f.natDegree ell p p at tariff
    rw [tariff] at copy
    exact copy.trans (Nat.add_le_add_right (Nat.add_le_add_right (cap i j g) _) _)
  have summed : bill groups (groupOrder 64)≤64*B := by
    rw [bill,groupOrder,List.map_ofFn,List.sum_ofFn]
    exact (Finset.sum_le_sum (fun g _=>each g)).trans (le_of_eq (by simp))
  have h := (one_head_and_each_actual_group_meter_are_charged (W:=W) D frame hv executeGroups i j raw).2
  change (actualReceiptSlot (W:=W) D frame hv executeGroups i j raw).steps≤H.steps+
     bill groups (groupOrder 64)+tupleExtra E.words.length ell (exteriorChild G ell i j (0:Fin 64)).prec 64+3 at h
  have extra : tupleExtra E.words.length ell (exteriorChild G ell i j (0:Fin 64)).prec 64=
      tupleExtra f.natDegree ell p 64 :=
    by rw [show E.words.length=f.natDegree from E.natDegree D.hf,
      show (exteriorChild G ell i j (0:Fin 64)).prec=p from G.precision ell i]
  rw [extra] at h
  exact h.trans (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add head summed) _) _)

#print axioms actualReceiptSlotRoof
#print axioms the_same_outer_slots_cost_their_actual_groups_and_arithmetic
end
end J6R114PrescribedReceipts

