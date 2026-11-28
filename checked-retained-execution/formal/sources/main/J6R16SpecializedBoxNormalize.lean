import J6R14SpecializedBoxRing

/-! The same high observation composed with scalar embedding at the
literal compiler site. This theorem is deliberately generic in both the
packet and group types, so there is no accidental change to the
proof-time enumerations of that compiler. -/
namespace J6R14SpecializedBox
open scoped Classical BigOperators Polynomial
open Polynomial LiteralPortCompiler J8Physical J8EndToEnd J8J9Grouped
open J9R13PhysicalFusion J9LayoutTransfer DyadicProbeCompiler NativeProbeRing
noncomputable section
set_option linter.unusedSectionVars false

local instance (priority := 10000) normalizedFinDecEq (n : ℕ) : DecidableEq (Fin n) :=
  fun i j => Classical.propDecidable (i=j)

variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

theorem scalar_high_is_compiled
    (e : EndpointSeating d) (he : Even L) (hL : 2<L)
    (s : S) (off : d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (idx : Wire R≃Fin M) (F : OldTables d) (sign : S→Bool)
    (tail : IntegralArguments d) (n : Fin (Fintype.card (PinTile d s)))
    (kt : TargetPorts d s→Source[X]) (a p ell : ℕ) (f : ℤ[X])
    (adr : Fin f.natDegree→Bool) :
    let z := probe p f adr
    J6ActiveInterpolation.scalarIn p f ell (highObservation d e he hL s F sign tail n kt a p f adr) =
      (2 : J6ActiveInterpolation.Ring p f ell)^(a+1+n.val) *
        J6ActiveInterpolation.scalarIn p f ell z *
        evalBox p f ell z (MvPolynomial.coeff β (completed (literalSystem d idx F sign)
          (literalBase d e he s idx tail n) (literalKernel d (M:=M) he hL s n kt))) := by
  dsimp only
  rw [← observation_is_physical_child_product d e he hL s off idx F sign tail n kt a p f adr,
    observation_eval,map_mul]
  change J6ActiveInterpolation.scalarIn p f ell ((2:Scalar p f)^(a+1+n.val)*probe p f adr) * _ = _
  rw [map_mul,map_pow,map_ofNat]
  rfl

#print axioms scalar_high_is_compiled
end
end J6R14SpecializedBox