import J8J9GroupedSigns
import J9R13ChartFirst

/-! The algebraic tile decoder is public: not even the sibling
constant can depend on unknown pin signs. The first coefficient from
the R13 chart is exactly the original physical tile moment. -/
namespace J9R17AllPins
open scoped Polynomial BigOperators Classical
open Polynomial NativeProbeRing DyadicProbeCompiler J8Physical J8EndToEnd J8J9Grouped
open J9R13PhysicalFusion J9R13PhysicalTables J9R13ChartFirst LiteralPortCompiler
noncomputable section
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

theorem publicSiblings_constant_independent
    (e : EndpointSeating d) (he : Even L) (a : S) (F : OldTables d)
    (sign sign' : S→Bool) (tail tail' : RestArguments d) :
    (publicSiblings d e he a F tail sign).coeff 0 =
      (publicSiblings d e he a F tail' sign').coeff 0 := by
  simp only [publicSiblings,Polynomial.coeff_zero_prod]
  refine Finset.prod_congr rfl ?_
  intro g _
  exact physicalMarked_sign_independent d e he g _ (F g) _ _ _ _ none

theorem tile_decoder_public
    (e : EndpointSeating d) (he : Even L) (a : S) (F : OldTables d)
    (sign sign' : S→Bool) (tail tail' : RestArguments d)
    (obs : Fin (Fintype.card (PinTile d a))→ℚ) :
    tileSignReadout d e he a F sign tail obs =
      tileSignReadout d e he a F sign' tail' obs := by
  simp only [tileSignReadout,J8SourceMoment.completedScale,
    publicSiblings_constant_independent d e he a F sign sign' tail tail']

set_option maxHeartbeats 2700000 in
theorem chart_first_equals_physical_coeff
    (e : EndpointSeating d) (he : Even L) (hL : 2<L) (k : ℕ) (hpow : L=2^k)
    (a : S) (off : d.rowLabel (pinWire d a).1≠d.pinLabel a)
    (idx : Wire R≃Fin M) (F : OldTables d) (sign : S→Bool)
    (tail : IntegralArguments d) (higher : RestArguments d)
    (n : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a→Source[X])
    (rest : TargetPorts d a→ℚ[X])
    (rows : (Fin M→Bool)→R→Bool→ℚ[X]) (cross : Fin L→ℚ[X]) (source : (Fin M→Bool)→ℚ[X]) :
    (J9End.literalCompleted (J9End.chart d a idx (satisfied (globalCNF d idx F sign)))
      n rows cross source).coeff 1 =
      physicalCoeff d e he a F sign higher n rest := by
  exact (exactFirst_from_seated_children d e he hL a off idx F sign tail n kt k hpow rows cross source).symm.trans
    (physical_first_derived d e he hL a off idx F sign tail higher n kt rest k hpow)

theorem exact_physical_tile_from_receipts
    (e : EndpointSeating d) (he : Even L) (hL : 2<L)
    (a : S) (off : d.rowLabel (pinWire d a).1≠d.pinLabel a)
    (F : OldTables d) (sign : S→Bool)
    (sat : ∀ g v, ∃ x, satisfied (F g v) x=true)
    (obs : Fin (Fintype.card (PinTile d a))→ℚ)
    (hObs : ∀ n, obs n = physicalCoeff d e he a F sign (fun _ _ _ _ => 0) n (fun _ => 0)) :
    tileSignReadout d e he a F (fun _ => false) (fun _ _ _ _ => 0) obs =
      (fun i => sign (pinEnumeration d a i).val) := by
  have eObs : obs = fun n => physicalCoeff d e he a F sign (fun _ _ _ _ => 0) n (fun _ => 0) :=
    funext hObs
  rw [← tile_decoder_public d e he a F sign (fun _ => false) (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) obs,eObs]
  exact recover_physical_tile_exact d e he a hL off F (fun _ _ _ _ => 0) sign sat (fun _ _ => 0)

#print axioms publicSiblings_constant_independent
#print axioms tile_decoder_public
#print axioms chart_first_equals_physical_coeff
#print axioms exact_physical_tile_from_receipts
end
end J9R17AllPins