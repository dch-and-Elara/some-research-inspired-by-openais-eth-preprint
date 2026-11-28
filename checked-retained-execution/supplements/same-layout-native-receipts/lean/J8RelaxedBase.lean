import J8RelaxedRecovery
import J8EndToEndConstants
set_option warningAsError true
namespace J8Physical.Relaxed
open scoped Polynomial BigOperators Classical
open Polynomial NativeProbeRing DyadicProbeCompiler J8EndToEnd
noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]
omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [DecidableEq V] [Fintype G] [DecidableEq Packet] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem physicalWeight_agreement (e : RowEndpointSeating d) (even : Even L)
    (F : OldTables d) (g : G) (x : LocalBits d g) :
    rationalMap (physicalTableWeight d F g x) =
      (localChild d e even g (outerAmplitude L) (F g)).oldWeight x := by
  simp only [physicalTableWeight, map_prod, LiteralPortCompiler.map_truth, localChild,
    J8SourceMoment.literalChild]

def ArgsAgree (e : RowEndpointSeating d) (even : Even L)
    (F : OldTables d) (base : IntegralArguments d) : Prop :=
  ∀ g x r leg, rationalMap ((base g x r leg).coeff 0) =
    J8SourceMoment.input0 (localChild d e even g (outerAmplitude L) (F g)) x.2 r leg

omit [Fintype G] [DecidableEq Packet] in
theorem liftedGroup_matches (e : RowEndpointSeating d) (even : Even L) (F : OldTables d)
    (base : IntegralArguments d) (sign : S → Bool) (higher : RestArguments d)
    (agree : ArgsAgree d e even F base) (g : G) (mark : Option (LocalRow d g × Bool))
    (feat : ((LocalPin d g → Bool) × LocalBits d g) → Source)
    (rationalFeat : ((LocalPin d g → Bool) × LocalBits d g) → ℚ)
    (feat_eq : ∀ x, rationalMap (feat x) = rationalFeat x) :
    rationalMap ((liftedGroup d F base sign g mark feat).coeff 0) =
      (J8SourceMoment.genuineChild (localChild d e even g (outerAmplitude L) (F g))
        (fun i : LocalPin d g => sign i.1) (higher g) mark rationalFeat).coeff 0 :=
  child_const_matches _ _ _ _ _ _ _ _ (physicalWeight_agreement d e even F g) feat_eq (agree g)

omit [DecidableEq Packet] in
theorem liftedPublic_matches (e : RowEndpointSeating d) (even : Even L) (a : S) (F : OldTables d)
    (base : IntegralArguments d) (sign : S → Bool) (higher : RestArguments d)
    (agree : ArgsAgree d e even F base) :
    rationalMap ((liftedPublic d a F base sign).coeff 0) =
      (publicSiblings d e even a F higher sign).coeff 0 := by
  simp only [liftedPublic, publicSiblings, Polynomial.coeff_zero_prod, map_prod]
  exact Finset.prod_congr rfl (fun g _ =>
    liftedGroup_matches d e even F base sign higher agree g none _ _ (fun _ => map_one _))

def physicalBase (e : RowEndpointSeating d) (even : Even L) (c : ℤ)
    (tail : IntegralArguments d) : IntegralArguments d :=
  fun g x r leg =>
    C (((localHit d e even r).map fun p =>
        if p.1 = leg then (c : Source) * sourceBit (x.2 p.2.1 p.2.2) else 0).getD 0) +
      X * tail g x r leg

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [DecidableEq V] [Fintype G] [DecidableEq Packet] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem constructed_base_agrees (e : RowEndpointSeating d) (even : Even L) (c : ℤ)
    (hc : (c : ℚ) = outerAmplitude L) (F : OldTables d) (tail : IntegralArguments d) :
    ArgsAgree d e even F (physicalBase d e even c tail) := by
  intro g x r leg
  simp only [physicalBase, Polynomial.coeff_add, Polynomial.coeff_C_zero,
    Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, add_zero]
  cases hh : localHit d e even r with
  | none =>
    simp only [Option.map_none, Option.getD_none, map_zero, localChild,
      J8SourceMoment.input0, J8SourceMoment.literalChild, groupWiring,
      wiringOfOption_read_none _ _ hh]
  | some v =>
    simp only [Option.map_some, Option.getD_some, localChild,
      J8SourceMoment.input0, J8SourceMoment.literalChild, groupWiring,
      wiringOfOption_read_some _ _ _ _ hh]
    by_cases eq : v.1 = leg
    · simp only [if_pos eq, map_mul, map_intCast, hc, sourceBit_agreement]
      rfl
    · simp only [if_neg eq, map_zero]

#print axioms constructed_base_agrees
#print axioms liftedGroup_matches
#print axioms liftedPublic_matches
end
end J8Physical.Relaxed