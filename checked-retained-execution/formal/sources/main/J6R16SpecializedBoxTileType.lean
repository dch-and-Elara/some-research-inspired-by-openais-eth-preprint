import J6R15SpecializedBoxFrame

/-! The pin enumeration uses the printed finite subtype, with a fixed
proof-time page equality instance. Avoid transporting a native degree
through an unrelated cardinal presentation. -/
namespace J6R14SpecializedBox
open scoped BigOperators Classical Polynomial
open P11FullPacking J8Physical J8EndToEnd J8J9Grouped NativeProbeRing DyadicProbeCompiler
noncomputable section
set_option linter.unusedSectionVars false

variable {G R S V : Type*} [LinearOrder G] {U : V→Type*} {a b : ℕ}
variable (d : Layout (Page a b G) R S V G U (2^a))
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [(v : V)→Fintype (U v)]

def canonicalPinTile (s : S) : Fintype (PinTile d s) := by
  letI : DecidableEq (Page a b G) := Classical.decEq _
  exact @Subtype.fintype S _ (instDecidablePredSameTilePinWire d s) _

set_option maxHeartbeats 1200000 in
theorem canonicalPinTile_crossing_check (e : EndpointSeating d) (he : Even (2^a:ℕ))
    (hL : 2<2^a) (s : S) (F : OldTables d) (sign : S→Bool)
    (tail : IntegralArguments d) (kk : TargetPorts d s→Source[X])
    (n : Fin (@Fintype.card (PinTile d s) (canonicalPinTile d s))) (p : ℕ) (f : ℤ[X])
    (adr : Fin f.natDegree→Bool) :
    ∃ x : Scalar p f, highObservation d e he hL s F sign tail n kk a p f adr = x :=
  ⟨_,rfl⟩

#print axioms canonicalPinTile
#print axioms canonicalPinTile_crossing_check
end
end J6R14SpecializedBox