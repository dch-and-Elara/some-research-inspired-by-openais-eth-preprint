import AffineCostMatrix

namespace AffineCost.Checks

open Bit

private def labels : List Fraction :=
  [⟨⟨[],[false,true]⟩,⟨[true,true],[]⟩⟩,
   ⟨⟨[true,true,true],[]⟩,⟨[false,false,true],[]⟩⟩]

/- At q=2 the answer must be the constant identity. Test all slots of
the dense output with the nonintegral labels -2/3 and 7/4. -/
#eval
  let r := matrixRun labels 2
  let expected : List ℚ := (tasks 2).map fun t =>
    if t.2.2.val = 0 ∧ wordEqual t.1 t.2.1 = true then 1 else 0
  (r.value.length, r.value.map Fraction.rat == expected, r.steps)

#eval labels.head?.any fun a => (readFraction ((emitFraction a).value ++ [true,false])).isSome

/- At q=3 this diagonal entry is genuinely linear. -/
#eval
  let labels : List Fraction :=
    [⟨⟨[false,true],[]⟩,⟨[true],[]⟩⟩,
     ⟨⟨[true,false,true],[]⟩,⟨[true],[]⟩⟩,
     ⟨⟨[false,false,false,true],[]⟩,⟨[true],[]⟩⟩]
  let u : AffineEdge.Word 3 := (fun i => i == 0, fun _ => true)
  (List.finRange 3).map fun k => (coefficientRun labels (u,u,k)).value.rat

#print axioms explicit_rowSystem
#print axioms coefficientExpr_eval
#print axioms Bit.add_value
#print axioms Bit.mul_value
#print axioms Expr.execute_rat
#print axioms Expr.execute_steps
#print axioms Bit.readFraction_emit
#print axioms matrixRun_step_bound
#print axioms runCompiled_bound
#print axioms runCompiled_correct
#print axioms runCompiledOutput_eq
#print axioms runCompiledOutput_correct
#print axioms runCompiledOutput_bound
#print axioms runCompiledOutput_valid

end AffineCost.Checks
