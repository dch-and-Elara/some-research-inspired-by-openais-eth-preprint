import J6R49CostProbeBill

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12500000
set_option maxRecDepth 2500

/-! Indexed bill of the actual legal native probe: the proof-side mode
list contributes exactly one entry for each native tuple and each stock
group. Distinct addresses with the same semantic child remain separate. -/
namespace J6R49Cost
open scoped Polynomial BigOperators Classical
open AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply J6R32StatefulArithmetic
open J6R48DFS J6R49DFS

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}
local notation "M" => NativeMenu (shape S Δ sel) c t
local notation "pₜ" => registerPrecision S c t

noncomputable def actualProbeChildBill (F : Frame f pₜ)
    (child : M → Fin 64 → Meter (Block F ell)) : ℕ :=
  letI := nativeMenuFinite (shape S Δ sel) c t
  ∑ β : M, ∑ g : Fin 64, (child β g).steps

theorem exact_probe_child_census (F : Frame f pₜ) (child : M → Fin 64 → Meter (Block F ell))
    (order : List M) (nd : order.Nodup) (all : ∀ b,b∈order) :
    probeEntryBill order child=actualProbeChildBill F child ∧
      order.length=Nat.card M := by
  letI := nativeMenuFinite (shape S Δ sel) c t
  constructor
  · unfold probeEntryBill actualProbeChildBill
    rw [complete_sum order nd all]
    apply Finset.sum_congr rfl
    intro β _
    unfold bill groupOrder
    rw [List.map_ofFn,List.sum_ofFn]
    simp only [Function.comp_apply]
  · rw [Nat.card_eq_fintype_card,←Finset.card_univ,←List.toFinset_card_of_nodup nd]
    congr 1
    ext b
    simp [all b]

theorem actual_streamed_probe_indexed_bill (F : Frame f pₜ) (I : SiteTape sel d t q)
    (hq : 0<q) (hv : 0<ell) (child : M → Fin 64 → Meter (Block F ell)) :
    (runProbe F I hq hv child).steps ≤ actualProbeChildBill F child+
      ((16*q+14+4*(I.words.length+1)*(q+1))+
        uvWidth F.words.length ell pₜ+
        Nat.card M*perModeArithmetic F.words.length ell pₜ F.hp+
        (Nat.card M+1)*J6R15ModeCost.delayCap q I.words.length) := by
  obtain ⟨order,nd,all,cost⟩ := actual_streamed_probe_arithmetic_bill F I hq hv child
  obtain ⟨hEntry,hSize⟩ := exact_probe_child_census F child order nd all
  rw [hEntry,hSize] at cost
  omega

#print axioms actualProbeChildBill
#print axioms exact_probe_child_census
#print axioms actual_streamed_probe_indexed_bill
end J6R49Cost

