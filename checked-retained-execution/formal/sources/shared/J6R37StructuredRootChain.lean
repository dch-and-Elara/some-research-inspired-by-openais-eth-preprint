import J6R37StructuredRootPorts
import J6R35RootOriginsChain

/-! The inherited body survives every actual typed retention. This
is the body-and-origin invariant, not a claim that recharting, group
labels, or addon arrays are supplied by the original program. -/
namespace J6R37StructuredRoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R21Ancestor J6R34ChildPath J6R35RootOrigins
open J6R36ChildFramedRoute J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R31RootResidentTables J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack
open J6R26StablePreparedRoot J6R11Repack J6R25PreparedSupply
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17500000
set_option maxRecDepth 2900

def carryBody : ℕ → List Bool → Meter (List Bool)
  | 0,bs=>⟨bs,0⟩
  | n+1,bs=>
    let prior := carryBody n bs
    let next := retainHeader prior.result
    ⟨next.result,prior.steps+next.steps⟩

theorem carry_body_exact (n : ℕ) (bs : List Bool) :
    (carryBody n bs).result=List.replicate n false++bs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [carryBody,ih,retain_header_exact,List.replicate_succ,List.cons_append]

theorem continuation_starts_at_same_port {f : ℤ[X]} {ell : ℕ} {old here cur : Point f ell}
    (first : Trace old here) (tail : Trace here cur) (seed : PortAt old→List Bool) (p : PortAt cur) :
    (carryBody tail.depth (first.literal seed (tail.back p))).result=(concatenate first tail).literal seed p := by
  rw [carry_body_exact,first.literal_exact,(concatenate first tail).literal_exact,
    concatenate_depth,concatenate_back,Equiv.trans_apply,←List.append_assoc,←List.replicate_add,
    Nat.add_comm tail.depth first.depth]

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)

theorem actual_gate_seed_continues (gate : J6R26DescriptorTree.Stamp key prec)
    (fits : gate.created.val=base) (pad : ℕ)
    (u : exteriorRows (G.selector ell) (G.ready ell) (G.centre ell X.centre) X.group)
    {cur : Point f ell} (tail : Trace (firstRetained X u).next cur) (p : PortAt cur) :
    let M := firstRetained X u
    let first : Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) (T:=T) u.val) M.next :=
      .keep .start M
    let A := actualLane X gate pad (M.back (tail.back p)).val
    A∈(outerLanes X gate pad).result.lanes ∧
      (carryBody tail.depth A.gate.body).result=(concatenate first tail).literal (rootGateBody (f:=f) (ell:=ell) (base:=base) (T:=T) u.val) p ∧
      A.gate.origin.pageKey=none ∧ A.gate.origin.stamp.created.val=(entry cur).created := by
  obtain ⟨member,body,tag,valid⟩ := actual_kept_root_seed X gate fits pad u (tail.back p)
  dsimp only
  refine ⟨member,?_,congrArg Origin.pageKey tag,valid.trans tail.tag.symm⟩
  rw [body]
  exact continuation_starts_at_same_port (.keep .start (firstRetained X u)) tail (rootGateBody (f:=f) (ell:=ell) (base:=base) (T:=T) u.val) p

theorem actual_page_seed_continues (gate : J6R26DescriptorTree.Stamp key prec) (pad : ℕ) (k : CanonicalPage m)
    {cur : Point f ell} (tail : Trace (stableBorn X k) cur) (p : PortAt cur) :
    let A := actualLane X gate pad (packetRootHalf X k (tail.back p))
    A∈(outerLanes X gate pad).result.lanes ∧
      (carryBody tail.depth A.packet.body).result=tail.literal (originSeed (rootChart T) (oddAxis m) X.group k) p ∧
      A.packet.origin.stamp=(X.seed pad).immutable.payload.stamp ∧
      A.packet.origin.stamp.created.val=(entry cur).created ∧
      A.packet.origin.pageKey=some (widened pad (residentPageKey m k)).result := by
  obtain ⟨member,body,stamp,_,precision,page,_⟩ := actual_exterior_packet_seed X gate pad k (tail.back p)
  dsimp only
  refine ⟨member,?_,stamp,precision.trans tail.tag.symm,page⟩
  rw [body,carry_body_exact,tail.literal_exact]

#print axioms carry_body_exact
#print axioms continuation_starts_at_same_port
#print axioms actual_gate_seed_continues
#print axioms actual_page_seed_continues
end J6R37StructuredRoot