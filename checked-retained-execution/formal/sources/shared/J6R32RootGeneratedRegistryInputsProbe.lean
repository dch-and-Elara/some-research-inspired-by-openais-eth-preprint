
import J6R31RootResidentTablesCapsule
import J6R30ProducedGateRegistryFrames
import J6R27PrescribedProbeRoot

/-! A native prefix ordinal and a prescribed exterior ordinal are
different types. The immutable payload below is decoded directly
from its actual prescribed coordinate word. Native-prefix transport
is valid exactly when the full words match, not by their lengths. -/
namespace J6R32RootGeneratedRegistryInputs
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open A1R10 J6R22Active J6R14ZeroMode J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R27PrescribedProbe J6R27OriginalGate J6R30ProducedGateRegistry
open J6R21Ancestor J6R15ModeCost
set_option maxHeartbeats 11500000
set_option maxRecDepth 2100

theorem scalar_injective {p ell : ℕ} (f : ℤ[X]) (hℓ : 0<ell) :
    Function.Injective (J6ActiveInterpolation.scalarIn p f ell) := by
  let C := NativeProbeRing.Scalar p f
  have vanish : Polynomial.eval₂ (RingHom.id C) 0 ((X:C[X])^ell)=0 := by
    simp [Nat.ne_of_gt hℓ]
  let out := AdjoinRoot.lift (RingHom.id C) 0 vanish
  have law (x : C) : out (J6ActiveInterpolation.scalarIn p f ell x)=x := by
    change AdjoinRoot.lift (RingHom.id C) 0 vanish (AdjoinRoot.of ((X:C[X])^ell) x)=x
    rw [AdjoinRoot.lift_of]
    rfl
  intro x y h
  exact (law x).symm.trans ((congrArg out h).trans (law y))

theorem probe_equal_iff_literal_word {f : ℤ[X]} {D N p ell : ℕ}
    (hp : 0<p) (hv : 0<ell) (hf : f.Monic) (he : 0<f.natDegree)
    (W : Prescribed f D) (j : Fin (D+1)) (fit : N≤2^f.natDegree) (z : Fin N) :
    prescribedNode W p ell j=J6ActiveInterpolation.node p f ell N fit z ↔
      W.word j=NativeProbeRing.chosenRep f.natDegree N fit z := by
  change J6ActiveInterpolation.scalarIn p f ell (NativeProbeRing.probe p f (W.word j))=
    J6ActiveInterpolation.scalarIn p f ell (NativeProbeRing.probe p f
      (NativeProbeRing.chosenRep f.natDegree N fit z)) ↔ _
  refine ⟨fun h=>?_,fun h=>congrArg (fun u=>J6ActiveInterpolation.scalarIn p f ell
    (NativeProbeRing.probe p f u)) h⟩
  exact NativeProbeRing.binary_residues_injective p hp f hf he
    (congrArg (NativeProbeRing.residueMap p hp f) (scalar_injective f hv h))

theorem native_zero_cannot_match {f : ℤ[X]} {D N p ell : ℕ}
    (hp : 0<p) (hv : 0<ell) (hf : f.Monic) (he : 0<f.natDegree)
    (W : Prescribed f D) (j : Fin (D+1)) (fit : N≤2^f.natDegree) (z : Fin N)
    (zero : NativeProbeRing.chosenRep f.natDegree N fit z=fun _=>false) :
    prescribedNode W p ell j≠J6ActiveInterpolation.node p f ell N fit z := by
  intro h
  exact W.excludesZero j (((probe_equal_iff_literal_word hp hv hf he W j fit z).mp h).trans zero)

def outerCoordinate {f : ℤ[X]} {D p : ℕ} {W : Prescribed f D}
    (F : Frame f p) (hf : f.Monic)
    (bank : SuppliedProbeBits W f.natDegree) (j : Fin (D+1)) :
    Meter {x : List Bool // x.length=F.words.length} :=
  (changeReaderWidth (F.natDegree hf).symm bank).read j

theorem outer_coordinate_exact {f : ℤ[X]} {D p : ℕ} {W : Prescribed f D}
    (F : Frame f p) (hf : f.Monic) (bank : SuppliedProbeBits W f.natDegree) (j : Fin (D+1)) :
    (outerCoordinate F hf bank j).result.val=List.ofFn (W.word j) ∧
      (outerCoordinate F hf bank j).steps=(bank.read j).steps :=
  ⟨bank.consistent j,rfl⟩

theorem generated_outer_coordinate {f : ℤ[X]} {D p ell : ℕ}
    (F : Frame f p) (hf : f.Monic) (hv : 0<ell) (fit : D+1<2^f.natDegree) (j : Fin (D+1)) :
    let W := canonicalPrescribed f D fit
    let B := generatedProbeBits f D f.natDegree rfl fit
    let X := outerCoordinate F hf B.result j
    let V := encodeProbe F.hp hv X.result
    X.result.val=encodeBits f.natDegree (j.val+1) ∧
      boxTransport F.exactMod (uvRead F.hp F.words ell V.result)=prescribedNode W p ell j ∧
      B.steps=positiveTapeFee f.natDegree (D+1)+3 ∧
      X.steps≤(D+1)*(f.natDegree+2) := by
  let B := generatedProbeBits f D f.natDegree rfl fit
  obtain ⟨A,Bill⟩ := generated_probe_bits_receipt f D f.natDegree rfl fit
  have q := outer_coordinate_exact F hf B.result j
  exact ⟨(reader_width_is_free (F.natDegree hf).symm B.result j).1.trans (Bill j).1,
    encodeProbe_is_literal F.hp hv F.exactMod (outerCoordinate F hf B.result j).result _ q.1,
    A,(q.2 ▸ (Bill j).2)⟩

theorem frames_with_prescribed_probe
    {f : ℤ[X]} {D p ell a q codew pagew : ℕ} {i : Fin a} {fw : List (A1R10.Word p)}
    (hp : 0<p) (hv : 0<ell) (hMod : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    (W : Prescribed f D) (j : Fin (D+1))
    (R : Frames fw a q codew pagew) (hCoord : R.coordinates.val=List.ofFn (W.word j))
    (hfit : i.val+1≤q)
    (ms : List (J6R18ChildWrite.ModeInput a p i q))
    (compiled : (compileModes i p hfit R.axis R.owner R.group R.start R.raw R.sparse R.masks).result=some ms) :
    let S := selectedSlots R.seatKey R.group R.seats
    let C := Frames.compile R hp hv hfit
    ∃ out, C.result=some out ∧
      boxTransport hMod (uvRead hp fw ell out.probe)=prescribedNode W p ell j ∧
      out.rows=S.result.1 ∧ out.cols=S.result.2 ∧ out.modes=ms ∧
      C.steps=fw.length*(p+6)+A1R11.uvWidth fw.length ell p+2+probeCopyFee p ell fw.length+
        S.steps+(compileModes i p hfit R.axis R.owner R.group R.start R.raw R.sparse R.masks).steps+10 := by
  let S := selectedSlots R.seatKey R.group R.seats
  let M := compileModes i p hfit R.axis R.owner R.group R.start R.raw R.sparse R.masks
  let X := encodeProbe hp hv R.coordinates
  let F : OriginFields a p ell q fw i := ⟨X.result,S.result.1,S.result.2,ms⟩
  have h := origin_fields_written X.result S M ms compiled
  have b := encodeProbe_cost hp hv R.coordinates
  refine ⟨F,?_,encodeProbe_is_literal hp hv hMod R.coordinates _ hCoord,rfl,rfl,rfl,?_⟩
  · change (assembleOriginFields X.result S M).result=some F
    rw [h]
  · change X.steps+(assembleOriginFields X.result S M).steps+4=
      fw.length*(p+6)+A1R11.uvWidth fw.length ell p+2+probeCopyFee p ell fw.length+S.steps+M.steps+10
    change X.steps=_ at b
    rw [h,b]
    dsimp only
    omega

#print axioms scalar_injective
#print axioms probe_equal_iff_literal_word
#print axioms native_zero_cannot_match
#print axioms generated_outer_coordinate
#print axioms frames_with_prescribed_probe
end J6R32RootGeneratedRegistryInputs
