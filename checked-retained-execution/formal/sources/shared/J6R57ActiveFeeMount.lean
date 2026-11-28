import J6R55CachedLedgerCore
import J6R52PeakCachedStack
import J6R36RouteConservationGroups

/-! Price the once-per-active-descendant cache mount by the actual
parent-tape scan and the selected child rows. No boot/sidecar install
or child visit fee is counted here. -/
namespace J6R57ActiveFee
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6ActiveRun J6R10Repack J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute
open J6R36RouteConservation J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer
open J6R51Online J6R51ParentFrames J6R51Peak J6R52CacheWhole J6R52Peak J6R55CachedLedger

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 3250
set_option linter.unusedSectionVars false
set_option Elab.async false

theorem map_fee_bound {A : Type*} (rows : List A) (fee : A→ℕ) (unitFee : ℕ)
    (bound : ∀ row ∈ rows, fee row ≤ unitFee) : (rows.map fee).sum ≤ rows.length*unitFee := by
  induction rows with
  | nil => simp
  | cons row tail ih =>
      have b := bound row List.mem_cons_self
      have e := ih (fun x h=>bound x (List.mem_cons_of_mem _ h))
      simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm] using Nat.add_le_add b e

def frameMountCap (parentEdges childEdges port owner dim key prec page body : ℕ) : ℕ :=
  16+(2*parentEdges)*(2*port+3*body+81)+childEdges*visitFee port owner dim key prec page (2*parentEdges) body true

theorem visitFee_body_and_presence {w owner dim key prec page n old body : ℕ}
    (h : old ≤ body) (present : Bool) :
    visitFee w owner dim key prec page n old present ≤ visitFee w owner dim key prec page n body true := by
  unfold visitFee frameFee originFee
  cases present <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega

theorem frameMountCap_polynomial {parentEdges childEdges port owner dim key prec page body K : ℕ}
    (hp : parentEdges ≤ K) (hc : childEdges ≤ K) (ha : port ≤ K) (ho : owner ≤ K) (hd : dim ≤ K)
    (hk : key ≤ K) (hprec : prec ≤ K) (hpg : page ≤ K) (hb : body ≤ K) :
    frameMountCap parentEdges childEdges port owner dim key prec page body ≤ 256*(K+1)^3 := by
  have H : frameMountCap parentEdges childEdges port owner dim key prec page body ≤ frameMountCap K K K K K K K K K := by
    unfold frameMountCap visitFee locateFee frameFee originFee
    simp only [if_true]
    gcongr
  refine H.trans ?_
  unfold frameMountCap visitFee locateFee frameFee originFee
  simp only [if_true]
  have h :
      256*(K+1)^3=
        (16+(2*K)*(2*K+3*K+81)+K*(locateFee K (2*K)+frameFee K K K K K K K true+9))+
        (230*K^3+699*K^2+515*K+240) := by
    unfold locateFee frameFee originFee
    simp only [if_true]
    ring
  have ok := Nat.le_add_right
    (16+(2*K)*(2*K+3*K+81)+K*(locateFee K (2*K)+frameFee K K K K K K K true+9))
    (230*K^3+699*K^2+515*K+240)
  rw [←h] at ok
  exact ok

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

theorem exact_root_has_no_cache_mount (M : OnlineMachine T key prec tw bw page q) :
    cacheMountFee M (Path.root : Path sel r r)=0 := rfl

theorem actual_descendant_cache_cap (M : OnlineMachine T key prec tw bw page q)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c) (body : ℕ)
    (hc : ∀ h : Port c.host.Edge,((sourceState M p w).birth.native.physical.record h).body.length ≤ body) :
    let X := sourceState M p w
    cacheMountFee M (Path.step p w) ≤ frameMountCap c.edges ((Plan sel).child c w).edges X.birth.port X.site.ownerWidth
        (J6R36ChildFramedRoute.dim (p.ticket w)) key prec page body := by
  let X := sourceState M p w
  let B := (installResidentBank X).result
  let D := X.birth.native.physical
  have rawLen : D.raw.length=2*c.edges := real_parent_tape_has_two_records_per_edge T (p.ticket w) D
  have bankLen : B.rows.length=2*c.edges := by
    have H : B.rows.length=D.order.length := by
      rw [B.exactRows,X.site.bank_exact,List.length_map]
      rfl
    rw [D.source,List.length_map] at rawLen
    exact H.trans rawLen
  have hscan : (D.raw.map rowScanFee).sum ≤ (2*c.edges)*(2*X.birth.port+3*body+81) := by
    have bd : ∀ row∈D.raw,rowScanFee row ≤ 2*X.birth.port+3*body+81 := by
      intro row hr
      rw [D.source] at hr
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
      exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hc i)) _) _
    exact (map_fee_bound D.raw rowScanFee _ bd).trans_eq (by rw [rawLen])
  let rows := halfOrder T (p.ticket w) D
  let fee := fun h : HalfAt T (p.ticket w)=>visitFee X.birth.port X.site.ownerWidth
      (J6R36ChildFramedRoute.dim (p.ticket w)) key prec page B.rows.length
      (D.record h.val).body.length (X.site.aux h.val).oldOrigin.pageKey.isSome
  have hread : (rows.map fee).sum ≤ ((Plan sel).child c w).edges*
      visitFee X.birth.port X.site.ownerWidth (J6R36ChildFramedRoute.dim (p.ticket w))
        key prec page (2*c.edges) body true := by
    have H := map_fee_bound rows fee _ (fun h _=>visitFee_body_and_presence (hc h.val) _)
    change (rows.map fee).sum ≤ rows.length*visitFee X.birth.port X.site.ownerWidth
      (J6R36ChildFramedRoute.dim (p.ticket w)) key prec page B.rows.length body true at H
    rwa [show rows.length=((Plan sel).child c w).edges from half_order_length T (p.ticket w) D,bankLen] at H
  have paid := paid_parent_frames_local_cap X.site B.rows B.exactRows
  change (paidParentFrames X.site B.rows).steps ≤ 11+(D.raw.map rowScanFee).sum+(rows.map fee).sum at paid
  change (sourceMounted (M:=M) p w).steps ≤ _
  rw [(actual_active_mount_has_exact_typed_rows_and_fee M p w).1]
  change (paidParentFrames X.site B.rows).steps+3+2 ≤
    16+(2*c.edges)*(2*X.birth.port+3*body+81)+((Plan sel).child c w).edges*
      visitFee X.birth.port X.site.ownerWidth (J6R36ChildFramedRoute.dim (p.ticket w))
        key prec page (2*c.edges) body true
  omega

theorem actual_descendant_cache_cap_from_boot (M : OnlineMachine T key prec tw bw page q)
    (seed : ℕ) (boot : ∀ (w : (Plan sel).Slot r) h,
      ((M.initial w).result.birth.native.physical.record h).body.length ≤ seed)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c) :
    let X := sourceState M p w
    cacheMountFee M (Path.step p w) ≤ frameMountCap c.edges ((Plan sel).child c w).edges X.birth.port X.site.ownerWidth
        (J6R36ChildFramedRoute.dim (p.ticket w)) key prec page (sourceBodyCap s C seed) :=
  actual_descendant_cache_cap M p w _ (actual_demanded_body_fits M seed boot p w)

#print axioms map_fee_bound
#print axioms frameMountCap_polynomial
#print axioms exact_root_has_no_cache_mount
#print axioms actual_descendant_cache_cap
#print axioms actual_descendant_cache_cap_from_boot
end
end J6R57ActiveFee
