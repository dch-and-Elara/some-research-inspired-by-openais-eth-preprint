import J6R48LeafSourceBind

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6500000

namespace J6R49Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime
open J6ActiveRun J6R9Recursive J6R10Repack J6R11Blueprint
open J6R22Active J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48Leaf

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
abbrev Vertex (c : Call (PhysicalHost f ell)) := c.host.Row⊕c.host.Col
abbrev Bank (f : ℤ[X]) (ell key prec tw bw page : ℕ) := PageBank f ell key prec tw bw page
local notation "BankAt" => Bank f ell key prec tw bw page

structure RowAt {c : Call (PhysicalHost f ell)} (hf : f.Monic) (F : Frame f c.prec) (pos : 0<ell)
    (ord : Fin c.edges≃c.host.Edge) (vertex : Vertex c)
    (live : BankAt→Prop) where
  code : PageReadCode c.edges key page
  value : ∀ B,live B→∀ bits : Fin c.edges→Bool,
    F.decode (code.run hf F pos B (List.ofFn bits)).result=
      (c.host.file vertex).read hf c.prec (assignment c.host.network (bits∘ord.symm) vertex)
  format : ∀ B,live B→ResidentReadForm B code

#print axioms RowAt
end J6R49Leaf