import J8RelaxedRecovery
import J9R17AllPinsDecode
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace J8Physical.Relaxed
open scoped Polynomial BigOperators Classical
open Polynomial J9R17AllPins LiteralPortCompiler
noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
def physicalCoeff (e : RowEndpointSeating d) (even : Even L) (a : S) (F : OldTables d)
    (sign : S → Bool) (higher : RestArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (rest : TargetPorts d a → ℚ[X]) : ℚ :=
  let gs := d.pinLabel a
  let gt := d.rowLabel (pinWire d a).1
  let src := localChild d e even gs (outerAmplitude L) (F gs)
  let tgt := localChild d e even gt (outerAmplitude L) (F gt)
  (J8SourceMoment.completedTile (publicSiblings d e even a F higher sign) src tgt
    (fun i => sign i.1) (fun i => sign i.1) (higher gs) (higher gt)
    (fun i => tilePinInSource d (pinEnumeration d a i)) (coordinates d a)
    (fun b => tileBackground d a b) (groupedTargets d a) (2*(L:ℚ))
    (physicalDenominator d a) rest b).coeff 1

def tileSignReadout (e : RowEndpointSeating d) (even : Even L) (a : S) (F : OldTables d)
    (sign : S → Bool) (higher : RestArguments d)
    (obs : Fin (Fintype.card (PinTile d a)) → ℚ) : Fin (Fintype.card (PinTile d a)) → Bool :=
  let gs := d.pinLabel a
  let gt := d.rowLabel (pinWire d a).1
  let src := localChild d e even gs (outerAmplitude L) (F gs)
  let tgt := localChild d e even gt (outerAmplitude L) (F gt)
  let scale := fun b : Fin (Fintype.card (PinTile d a)) =>
    J8SourceMoment.completedScale (publicSiblings d e even a F higher sign) src tgt
      (groupedTargets d a) (2*(L:ℚ)) (physicalDenominator d a) b
  NativeMomentReconstruction.decodeBits (coordinates d a) scale
    (J8SourceMoment.nonpinBackground src (fun b => tileBackground d a b)) obs

theorem publicSiblings_constant_independent
    (e : RowEndpointSeating d) (he : Even L) (a : S) (F : OldTables d)
    (sign sign' : S→Bool) (tail tail' : RestArguments d) :
    (publicSiblings d e he a F tail sign).coeff 0 =
      (publicSiblings d e he a F tail' sign').coeff 0 := by
  simp only [publicSiblings,Polynomial.coeff_zero_prod]
  refine Finset.prod_congr rfl ?_
  intro g _
  exact physicalMarked_sign_independent d e he g _ (F g) _ _ _ _ none

theorem tile_decoder_public
    (e : RowEndpointSeating d) (he : Even L) (a : S) (F : OldTables d)
    (sign sign' : S→Bool) (tail tail' : RestArguments d)
    (obs : Fin (Fintype.card (PinTile d a))→ℚ) :
    tileSignReadout d e he a F sign tail obs =
      tileSignReadout d e he a F sign' tail' obs := by
  simp only [tileSignReadout,J8SourceMoment.completedScale,
    publicSiblings_constant_independent d e he a F sign sign' tail tail']

theorem exact_physical_tile_from_receipts
    (e : RowEndpointSeating d) (he : Even L) (hL : 2<L)
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

def publicAllPinDecoder (e : RowEndpointSeating d) (he : Even L) (F : OldTables d)
    (obs : Orders d→ℚ) : S→Bool :=
  fun s =>
    let j := (orderPin d).symm s
    tileSignReadout d e he (anchor d j.1) F (fun _ => false) (fun _ _ _ _ => 0)
      (fun n => obs ⟨j.1,n⟩) j.2

theorem publicAllPinDecoder_exact
    (e : RowEndpointSeating d) (he : Even L) (hL : 2<L) (F : OldTables d) (sign : S→Bool)
    (off : ∀ s, d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (sat : ∀ g v, ∃ x, satisfied (F g v) x=true)
    (obs : Orders d→ℚ)
    (hObs : ∀ w : Orders d, obs w =
      physicalCoeff d e he (anchor d w.1) F sign (fun _ _ _ _ => 0) w.2 (fun _ => 0)) :
    publicAllPinDecoder d e he F obs = sign := by
  unfold publicAllPinDecoder
  refine gather_all_bits d (fun k => tileSignReadout d e he (anchor d k) F
    (fun _ => false) (fun _ _ _ _ => 0) (fun n => obs ⟨k,n⟩)) sign ?_
  intro k i
  exact congrFun (exact_physical_tile_from_receipts d e he hL (anchor d k) (off _) F sign sat
    (fun n => obs ⟨k,n⟩) (fun n => hObs ⟨k,n⟩)) i

#print axioms tile_decoder_public
#print axioms exact_physical_tile_from_receipts
#print axioms publicAllPinDecoder_exact
end
end J8Physical.Relaxed