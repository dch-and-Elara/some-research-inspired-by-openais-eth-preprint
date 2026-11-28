import J6R33StatefulArithmeticPageProjection

/-! Direct leaf tape for a paged resident plan. A generated instruction
carries two actual words (occurrence and Page); the runtime does not
instantiate a new table per leaf, change an origin's precision, or
supply a cached coefficient standing in for a Gate. -/
namespace J6R33StatefulArithmeticPage
open scoped Polynomial
open AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J6ActiveRun J6R10Repack J6R11Blueprint J6R24MeteredRecursion
open J6R21Ancestor J6R21Leaf J6R32StatefulArithmetic

inductive PageReadCode (edges key page : ℕ) where
  | original (width : ℕ) (tape : OriginalGateTape edges width)
  | generated (addr : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page)
      (depth : ℕ) (wires : List WireRead)

def PageReadCode.run {f : ℤ[X]} {p ell m key prec tw bw page : ℕ} (C : PageReadCode m key page)
    (hf : f.Monic) (F : Frame f p) (hEll : 0<ell) (B : PageBank f ell key prec tw bw page)
    (bits : List Bool) : Meter (Block F ell) :=
  match C with
  | .original _ tape => uvGate F.hp F.sizePos hEll tape bits
  | .generated addr pg dep wires => readPage hf F hEll addr pg dep wires bits B

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
structure PagedLeaf (c : Call (PhysicalHost f ell)) (key page : ℕ) where
  sameEdges : c.host.edgeCount=c.edges
  clock : List Unit
  clockShape : clock.length=c.edges
  nodes : List (c.host.Row⊕c.host.Col)
  unique : nodes.Nodup
  complete : ∀ v,v∈nodes
  route : (c.host.Row⊕c.host.Col)→PageReadCode c.edges key page

variable {c : Call (PhysicalHost f ell)}
def PagedLeaf.query (D : PagedLeaf c key page) (hf : f.Monic) (F : Frame f c.prec) (hEll : 0<ell)
    (B : PageBank f ell key prec tw bw page) (v : c.host.Row⊕c.host.Col) (bits : List Bool) :
    Meter (Block F ell) := (D.route v).run hf F hEll B bits

def PagedLeaf.execute (D : PagedLeaf c key page) (hf : f.Monic) (F : Frame f c.prec) (hEll : 0<ell)
    (B : PageBank f ell key prec tw bw page) : Meter (Block F ell) :=
  clockDFS F.hp (readProduct F.hp F.sizePos hEll D.nodes (D.query hf F hEll B)) D.clock []

theorem paid_paged_leaf (D : PagedLeaf c key page) (hf : f.Monic) (F : Frame f c.prec) (hEll : 0<ell)
    (B : PageBank f ell key prec tw bw page) :
    let bill := leafEntryBill c.edges D.nodes (D.query hf F hEll B)
    bill≤(D.execute hf F hEll B).steps ∧
    (D.execute hf F hEll B).steps≤bill+
      2^c.edges*(uvWidth F.words.length ell c.prec+D.nodes.length*(mulCap F.words.length ell c.prec+2)+reverseFee c.edges)+
      (2^c.edges-1)*innerFee F.words.length ell c.prec F.hp := by
  dsimp only
  rw [PagedLeaf.execute,clocked_leaf_is_native_enumerator F.hp F.sizePos hEll D.nodes _ D.clock D.clockShape]
  exact leafCompute_bills_every_entry F.hp F.sizePos hEll c.edges D.nodes (D.query hf F hEll B)

theorem paged_leaf_value (D : PagedLeaf c key page) (hf : f.Monic) (F : Frame f c.prec) (hEll : 0<ell)
    (B : PageBank f ell key prec tw bw page)
    (entryLaw : ∀ (x : Fin c.edges→Bool) v, F.decode (D.query hf F hEll B v (List.ofFn x)).result=
      (c.host.file v).read hf c.prec (assignment c.host.network (x∘c.host.edgeOrder c.edges D.sameEdges) v)) :
    F.decode (D.execute hf F hEll B).result=J6R9Recursive.reduce c.prec f ell (c.host.contract hf) := by
  rw [PagedLeaf.execute,clocked_leaf_is_native_enumerator F.hp F.sizePos hEll D.nodes _ D.clock D.clockShape]
  have e (x : Fin c.edges→Bool) (v : c.host.Row⊕c.host.Col) :
    J6R18ChildWrite.castBox F.exactMod (uvRead F.hp F.words ell (D.query hf F hEll B v (List.ofFn x)).result)=
      (c.host.file v).read hf c.prec (assignment c.host.network (x∘c.host.edgeOrder c.edges D.sameEdges) v) :=
    (boxTransport_cast F.exactMod _).symm.trans (entryLaw x v)
  exact (boxTransport_cast F.exactMod _).trans
    (actual_leaf_exact c F.hp F.sizePos hEll F.exactMod hf D.sameEdges D.nodes D.unique D.complete _ e)

#print axioms paid_paged_leaf
#print axioms paged_leaf_value
end J6R33StatefulArithmeticPage
