import J6R14SpecializedBoxRing

/-! The actual J9 source, target and sibling factors can be evaluated
over the native J6 receiving algebra on their *unchanged* assignments.
No statement here changes the J6 root's entry chart or lets a callback
stand in for a weighted physical contraction. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial NativeProbeRing DyadicProbeCompiler J6R9Recursive
open J8Physical J8EndToEnd J8J9Grouped

noncomputable section
variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

set_option linter.unusedSectionVars false in
theorem group_box_same_assignments (q : ℕ) (f : ℤ[X]) (ell : ℕ) (z : Scalar q f)
    (F : OldTables d) (base : IntegralArguments d) (sign : S→Bool) (g : G)
    (mark : Option (LocalRow d g × Bool))
    (feat : ((LocalPin d g→Bool) × LocalBits d g) → Source) :
    evalBox q f ell z (liftedGroup d F base sign g mark feat) =
      ∑ x : LocalBits d g, ∑ bits : LocalPin d g→Bool,
        evalBox q f ell z (C (pinWeightSource (fun i : LocalPin d g => sign i.1) bits)) *
        (evalBox q f ell z (C (physicalTableWeight d F g x)) *
         evalBox q f ell z (C (feat (bits,x)))) *
        ∏ r : LocalRow d g, J8SourceMoment.rowFactor (J8SourceMoment.marker mark r)
          (evalBox q f ell z (base g (bits,x) r false))
          (evalBox q f ell z (base g (bits,x) r true)) := by
  simp only [liftedGroup,integralChild,map_sum,map_mul,map_prod,J8SourceMoment.map_rowFactor]

set_option linter.unusedSectionVars false in
theorem sibling_box_same_factors (q : ℕ) (f : ℤ[X]) (ell : ℕ) (z : Scalar q f)
    (a : S) (F : OldTables d) (base : IntegralArguments d) (sign : S→Bool) :
    evalBox q f ell z (liftedPublic d a F base sign) =
      ∏ g ∈ ((Finset.univ : Finset G).erase (d.pinLabel a)).erase (d.rowLabel (pinWire d a).1),
        evalBox q f ell z (liftedGroup d F base sign g none (fun _ => 1)) := by
  simp only [liftedPublic,map_prod]

set_option linter.unusedSectionVars false in
theorem high_observation_same_box (e : EndpointSeating d) (even : Even L) (hL : 2<L)
    (a : S) (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a→Source[X])
    (k q ell : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree→Bool) :
    let z := probe q f addr
    J6ActiveInterpolation.scalarIn q f ell (highObservation d e even hL a F sign tail b kt k q f addr) =
      (2:Box f ell q)^(k+1+(b:ℕ))*J6ActiveInterpolation.scalarIn q f ell z*
        (evalBox q f ell z (groupedPublic d e even a F sign tail) *
         evalBox q f ell z (groupedSource d e even a F sign tail b) *
         ∑ j ∈ groupedTargets d a,
            evalBox q f ell z (physicalKernel d a even hL (J9FactorBounds.kernel L) b kt j) *
            evalBox q f ell z (groupedTarget d e even a F sign tail j)) := by
  exact groupedProbe_box q f ell _ _ _ _ _ _ _

#print axioms group_box_same_assignments
#print axioms sibling_box_same_factors
#print axioms high_observation_same_box
end
end J6R14SpecializedBox
