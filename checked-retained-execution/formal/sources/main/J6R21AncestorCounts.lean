import J6R21LeafVertexBound
import J6R17ModeTapeSupply

/-! Source-native leaf entry-visit budget over actual address
occurrences. This counts calls of an entry routine, not an assumed
unit-time entry oracle or a proof of preparing all descriptors. -/
namespace J6R21Ancestor
open scoped BigOperators Polynomial Classical
open J1PPrinted J6ActiveRun J6R10Reachable J6R12Blueprint J6R11Blueprint J6R16ModeCost J6R21Leaf

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))

noncomputable def leafVisits (cutoff : ℕ) (c : Call (PhysicalHost f ell)) : ℕ :=
  if c.edges≤cutoff then 2^c.edges*vertexCount c.host else 0

include cfg in
theorem leaf_occurrence_bound {r c : Call (PhysicalHost f ell)}
    (walk : NativeReach (Plan sel) r c) (hr : Stable s C r) :
    leafVisits (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)) c≤
      2^(J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))*(vertexCount r.host+4*r.edges) := by
  unfold leafVisits
  split
  · rename_i h
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) h) (native_vertex_cap cfg sel walk hr)
  · exact Nat.zero_le _

include cfg in
theorem total_leaf_visits {r : Call (PhysicalHost f ell)}
    (hr : Stable s C r) (d0 : r.depth=0) (p0 : r.prec≤C*s) :
    let lam := Nat.clog 2 s
    let H := pathLimit s C
    let cap := J9PrintedSchedule.leafThreshold s lam
    (∑ j∈Finset.range (H+1),((occurrences (Plan sel) r j).map (leafVisits cap)).sum)≤
       (H+1)*(vertexCount r.host+4*r.edges)*2^((prefixConstant C+1)*cap) := by
  let lam := Nat.clog 2 s
  let H := pathLimit s C
  let cap := J9PrintedSchedule.leafThreshold s lam
  let e := branchBits lam*H+24*depthScale s C lam (siteConstant C)
  let V := vertexCount r.host+4*r.edges
  let visits := 2^cap*V
  have hOcc := total_native_occurrences cfg sel hr d0 p0
  have hComp : e≤prefixConstant C*cap :=
    compress_exponent s C cfg.constPos cfg.size (root_lambda_large cfg)
  change _≤(H+1)*V*2^((prefixConstant C+1)*cap)
  calc
    _≤∑ j∈Finset.range (H+1),(occurrences (Plan sel) r j).length*visits := by
      apply Finset.sum_le_sum
      intro j _
      apply list_sum_cap
      intro c hc
      obtain ⟨walk,_⟩ := exact_depth_occurrence sel d0 j c hc
      exact leaf_occurrence_bound cfg sel walk hr
    _=(∑ j∈Finset.range (H+1),(occurrences (Plan sel) r j).length)*visits := by rw [Finset.sum_mul]
    _≤((H+1)*2^e)*visits := Nat.mul_le_mul_right _ hOcc
    _≤((H+1)*2^(prefixConstant C*cap))*visits :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hComp))
    _=(H+1)*V*2^((prefixConstant C+1)*cap) := by
      rw [show (prefixConstant C+1)*cap=prefixConstant C*cap+cap by ring,pow_add]
      unfold visits
      ring

#print axioms leaf_occurrence_bound
#print axioms total_leaf_visits
end J6R21Ancestor





