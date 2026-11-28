import J6R102NativeCodeMeterCore
import J6R92NativeWidthDemand

/-! Apply the executable count selector to the actual resident receipt.
All output-width fits are inherited from the original legal descriptor;
no assumption on the size of its (possibly padded) numeric old code. -/
namespace J6R102NativeCodeMeter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34RootAtlas
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R24MeteredRecursion J6R51Online J6R50SourceProducer J6R49SourceLayout
open J6R30ProducedGateRegistry J6R54PublicFamily J6R57ScopeFee J6R88ScopeCode
open J6R33GeneratedChildSite J6R92NativeWidth J6R17ModeTape J6R14LayoutCost
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5000
set_option maxHeartbeats 22000000
set_option maxSynthPendingDepth 12
open P11FullPacking J6R32ChildResidentTransfer J6R10Repack J6R9PacketScopes

noncomputable section
theorem actual_raw_mode_rows_have_literal_key_width {Row Col Edge : Type}
    {N : Network Edge Row Col} {a q p : ℕ} {P : PhysicalPacking N a (Fin 64)} {i : Fin a}
    {R : ChildResidents a q} (H : ResidentReceipt P i p R) :
    ∀ x∈R.raw.roster.modes,x.key.1.length=6*a ∧ x.key.2.length=6*a := by
  intro x hx
  rw [H.rawModes] at hx
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
  exact ⟨coordinateLabel_len _,coordinateLabel_len _⟩

theorem actual_raw_roster_scan_is_affine {Row Col Edge : Type}
    {N : Network Edge Row Col} {a q p : ℕ} {P : PhysicalPacking N a (Fin 64)} {i : Fin a}
    {R : ChildResidents a q} (H : ResidentReceipt P i p R) :
    (countModes R.raw.roster.modes).steps≤11+(24*a+6*(q+1)+21)*H.modes.length := by
  rw [←raw_roster_clock H]
  exact actual_counter_bit_cost _ _ (actual_raw_mode_rows_have_literal_key_width H)

theorem selected_native_code_is_legal {q bw n old : ℕ} (xs : List (RawMode q))
    (lengthEq : xs.length=n) (oldPos : 0<old) (room : old<2^bw) (valid : 1+n<2^old) :
    let T := selectCode bw xs
    T.result.k=leastRosterCode xs.length ∧ T.result.write=emitOrdinal bw (leastRosterCode xs.length) ∧
      T.result.write.result.val=T.result.k ∧ 0<T.result.k ∧ 1+n<2^T.result.k := by
  have vv : 1+xs.length<2^old := by rwa [lengthEq]
  obtain ⟨bwPos,codeRoom,codePos,legal⟩ := smallest_code_fits_current_word oldPos room vv
  have exactCode := selected_code_is_old_word xs bwPos codeRoom
  have v : (selectCode bw xs).result.k=leastRosterCode xs.length := exactCode.1
  refine ⟨v,exactCode.2.1,rfl,?_,?_⟩
  · rw [v]
    exact codePos
  · rw [v,←lengthEq]
    exact legal

#print axioms actual_raw_mode_rows_have_literal_key_width
#print axioms actual_raw_roster_scan_is_affine
#print axioms selected_native_code_is_legal
end
end J6R102NativeCodeMeter

