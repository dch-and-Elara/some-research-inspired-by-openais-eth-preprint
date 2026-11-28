import J6R49LeafRowRecord
import J6R21AncestorOriginReads
import J6R21LeafSerial

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11000000
set_option maxRecDepth 2650

/-! Compile a real retained original gate at its current half-ports,
not a gate denotation supplied by the caller. Generated recipes use
the same finite port enumeration and the exact traced unary lanes. -/
namespace J6R49Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J6R9Recursive J6R10Repack J6R11Blueprint J6R21Ancestor J6R20Ancestor
open J6ActiveRun J6R21Leaf J6R22Active J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48Leaf
noncomputable section

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ} {c : Call (PhysicalHost f ell)}
local notation "BankAt" => Bank f ell key prec tw bw page

def atVertex (c : Call (PhysicalHost f ell)) (v : Vertex c) : Point f ell := ⟨c.host,v⟩

def portFintype (v : Vertex c) : Fintype (PortAt (atVertex c v)) := by
  change Fintype (ParentPorts c.host.network v)
  letI : Fintype c.host.Edge := c.host.finiteEdge
  exact Fintype.ofFinite _

def portList (v : Vertex c) : List (PortAt (atVertex c v)) :=
  (@Finset.univ _ (portFintype v)).toList

theorem portList_complete (v : Vertex c) (u : PortAt (atVertex c v)) : u∈portList v :=
  Finset.mem_toList.mpr (@Finset.mem_univ _ (portFintype v) u)

def literalWires {root : Point f ell} (v : Vertex c)
    (tr : Trace root (atVertex c v)) (seed : PortAt root→List Bool)
    (ord : Fin c.edges≃c.host.Edge) : List WireRead :=
  (portList v).map (fun u=>⟨tr.literal seed u,List.replicate (ord.symm (edge u.val)).val true⟩)

def originalRow {f : ℤ[X]} {ell key prec tw bw page : ℕ} {c : Call (PhysicalHost f ell)}
    {V G : Type} [Fintype V] [LinearOrder G] [Fintype G]
    {m n l base width : ℕ} (T : Plant V m n) (word : Fin (a m)→G)
    (hf : f.Monic) (F : Frame f c.prec) (pos : 0<ell)
    (ord : Fin c.edges≃c.host.Edge) (vertex : Vertex c)
    (live : PageBank f ell key prec tw bw page→Prop)
    (hBase : 0<base)
    (v : PlantNode (b:=J6Mesh.K m) (l:=l) T word)
    (tr : Trace (actualOriginalPoint (f:=f) (ell:=ell) (created:=base) T word v) (atVertex c vertex))
    (fit : c.edges≤2^width) :
    @RowAt f ell key prec tw bw page c hf F pos ord vertex live where
  code := .original width (gateTape fit (tracedSlot tr ord ∘ (originalPortGate T word v).port)
    (originalPortGate T word v).gate)
  value B _ bits := by
    have hF : 0<f.natDegree := F.natDegree hf ▸ F.sizePos
    have e := (original_through_trace T word hf hBase F.hp hF pos F.sizePos F.exactMod
      v tr ord fit _ rfl bits).1
    exact (boxTransport_cast F.exactMod _).trans e
  format _ _ := True.intro

#print axioms portList_complete
#print axioms literalWires
#print axioms originalRow
end
end J6R49Leaf
