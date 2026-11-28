import J6R110ScopeWordRatesNative
import J6R58BootScopeReads
import J6R57ScopeFeeCaps
import J6R82LayoutDebitCore

/-! An independently supplied R55 request is not assumed cheap. This
adapter applies when the query actually invokes the already implemented
raw keyed reader on that occurrence's stored physical row bank. -/
namespace J6R110ScopeWordRates
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R48RawRoute
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R49SourceLayout J6R50SourceProducer J6R51Online
open J6R52Dispatch J6R53Dispatch J6R54Dispatch J6R55Dispatch J6R55Public J6R54PublicFamily
open J6R57ScopeFee J6R68RateJoint J6R88ScopeCode J6R92NativeWidth J6R102NativeCodeMeter
open J6R51Peak J6R58BootScope J6R82LayoutDebit J6R27OriginalGate J6R10Repack

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
set_option maxRecDepth 4800
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-- The scan bound prices both a hit and a miss of the actual reader;
the native directory separately certifies that its own routes are valid. -/
theorem raw_query_reader_cost_from_actual_rows {k a b : ℕ}
    (tape : List (RefRow k (Word a×Word b×Bool))) (address : Word k) :
    (readBootQueryRow tape address).steps≤locateFee k tape.length+3*k+3*a+3*b+9 := by
  have search := locate_bound address tape
  unfold readBootQueryRow
  simp only [copy_fixed_exact]
  omega

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child}

theorem selected_sidecar_scans_two_actual_half_ports_per_edge (K : LocalLoad X w) :
    K.advance.next.birth.native.physical.order.length=2*v.child.edges := by
  let S := K.advance.next.site
  have h := (actual_addon_tapes_count_both_half_ports S).1
  rw [S.aligned,List.length_map] at h
  exact h

theorem selected_sidecar_bill_from_real_query_bound (K : LocalLoad X w) (per : ℕ)
    (fee : ∀ h : Port v.child.host.Edge,(K.directory.queries h).steps≤per) :
    sidecarQueryBill K≤(2*v.child.edges)*per := by
  unfold sidecarQueryBill
  dsimp only
  have each := sum_mapped_bounded K.advance.next.birth.native.physical.order
    (fun h=>(K.directory.queries h).steps) per (fun h _=>fee h)
  rw [selected_sidecar_scans_two_actual_half_ports_per_edge K,Nat.mul_comm per] at each
  exact each

/-- This is the same whole stored callback result at the physical query,
not a repricing of the entire selected demand. R102 only changes code,
not the directory query program. -/
theorem measured_selected_request_keeps_its_exact_query_meter
    (I : Meter (FixedRequest X w)) (h : Port v.child.host.Edge) :
    let orig := (meteredSelectedDemand I).result
    let K := (measureLocalLoad orig).result
    HEq (K.directory.queries h) (I.result.directory.queries h) := HEq.rfl

/-- If this actual selected R55 request uses the raw resident reader,
its charged R102 query line is bounded by actual tape census/widths.
`invokes` identifies the full Meter, including scan steps. -/
theorem R102_selected_sidecar_query_from_the_actual_keyed_read
    (I : Meter (FixedRequest X w)) {addr : ℕ}
    (tape : List (RefRow addr (Word I.result.directory.k1×Word I.result.directory.k2×Bool)))
    (address : Port v.child.host.Edge→Word addr)
    (invokes : ∀ h,I.result.directory.queries h=readBootQueryRow tape (address h))
    (K N E : ℕ) (addrW : addr≤K) (ownW : I.result.directory.k1≤K)
    (seatW : I.result.directory.k2≤K) (rows : tape.length≤N) (edges : v.child.edges≤E) :
    sidecarQueryBill (measureLocalLoad (meteredSelectedDemand I).result).result≤
      (2*E)*(locateFee K N+9*K+9) := by
  let A := (measureLocalLoad (meteredSelectedDemand I).result).result
  have each (h : Port v.child.host.Edge) : (A.directory.queries h).steps≤locateFee K N+9*K+9 := by
    change (I.result.directory.queries h).steps≤_
    rw [invokes h]
    have bill := raw_query_reader_cost_from_actual_rows tape (address h)
    have grow := locate_fee_mono_width_tables addrW rows
    omega
  exact (selected_sidecar_bill_from_real_query_bound A _ each).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 edges))

end
#print axioms raw_query_reader_cost_from_actual_rows
#print axioms selected_sidecar_scans_two_actual_half_ports_per_edge
#print axioms selected_sidecar_bill_from_real_query_bound
#print axioms measured_selected_request_keeps_its_exact_query_meter
#print axioms R102_selected_sidecar_query_from_the_actual_keyed_read
end J6R110ScopeWordRates