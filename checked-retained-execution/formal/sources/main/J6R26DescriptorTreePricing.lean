import J6R26DescriptorTreeSchedule

/-! A closed expression for the chronological comparison/copy overhead.
A row installed once still costs a scan on every later fresh insertion.
There is no table lookup oracle and no repeated charge in the Boolean
reference proof. Variable header widths are retained in the exact sum. -/
namespace J6R26DescriptorTree
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply

def intrinsicCharge {w b d p key : ℕ} (last : Word key) :
    List (Job w b d p)→ℕ
  | [] => 0
  | j::js =>
    let n := increment last
    let E := j.make n
    (E.steps+3*E.result.bytes.length+3*key+20+rowFee E.result)+intrinsicCharge n.result js

def olderScanCharge (fees : List ℕ) : ℕ :=
  match fees with
  | [] => 0
  | fee::tail => tail.length*fee+olderScanCharge tail

theorem history_rows_length {w b d p key : ℕ} (last : Word key) (jobs : List (Job w b d p)) :
    (historyRows last jobs).length=jobs.length := by
  induction jobs generalizing last with
  | nil => rfl
  | cons j js ih => simp only [historyRows,List.length_cons,ih]

theorem exact_prefix_scan_bill {w b d p key : ℕ} (last : Word key) (f : ℕ)
    (jobs : List (Job w b d p)) :
    scheduleFee last f jobs =
      2+jobs.length*f+intrinsicCharge last jobs+
        olderScanCharge ((historyRows last jobs).map rowFee) := by
  induction jobs generalizing last f with
  | nil => simp only [scheduleFee,intrinsicCharge,historyRows,olderScanCharge,List.map_nil,
                         List.length_nil,Nat.zero_mul,Nat.add_zero]
  | cons j js ih =>
    simp only [scheduleFee,ih,intrinsicCharge,historyRows,List.map_cons,List.length_cons,olderScanCharge,
      List.length_map,history_rows_length]
    ring

#print axioms history_rows_length
#print axioms exact_prefix_scan_bill
end J6R26DescriptorTree
