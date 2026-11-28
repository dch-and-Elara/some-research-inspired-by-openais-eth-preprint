
import J6R27OriginalGateCapsule
import J6R22ActiveBinary

/-! The capsule's probe is compiled from its actual finite binary
coordinate tape, rather than a supplied ring coefficient value. The
chosen interpolation enumeration's raw coordinates remain resident
input: this does not assume its ordinal-to-monomial conversion is free. -/
namespace J6R27OriginalGate
open scoped Polynomial
open AOracleMachineTime A1R10 A1R11 J6R21Ancestor J6R18ChildWrite J6R22Active

def assembleFromProbeBits {a p ell q : ℕ} {fw : List (A1R10.Word p)} {i : Fin a}
    (hp : 0<p) (vell : 0<ell) (coord : {bs : List Bool // bs.length=fw.length})
    (slots : Meter (List (J6R15ModeCost.Word a)×List (J6R15ModeCost.Word a)))
    (modes : Meter (Option (List (ModeInput a p i q)))) :
    Meter (Option (OriginFields a p ell q fw i)) :=
  let raw := encodeProbe hp vell coord
  let out := assembleOriginFields raw.result slots modes
  ⟨out.result,raw.steps+out.steps+4⟩

set_option maxHeartbeats 3000000 in
theorem actual_probe_capsule {a p ell q n : ℕ} {fw : List (A1R10.Word p)} {i : Fin a}
    (hp : 0<p) (vell : 0<ell) {f : ℤ[X]}
    (hF : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    (fit : n≤2^f.natDegree) (z : Fin n) (coord : {bs : List Bool // bs.length=fw.length})
    (literal : coord.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree n fit z))
    (slots : Meter (List (J6R15ModeCost.Word a)×List (J6R15ModeCost.Word a)))
    (modes : Meter (Option (List (ModeInput a p i q)))) (ms : List (ModeInput a p i q))
    (hModes : modes.result=some ms) :
    let op := assembleFromProbeBits hp vell coord slots modes
    ∃ fields, op.result=some fields ∧
      boxTransport hF (uvRead hp fw ell fields.probe)=J6ActiveInterpolation.node p f ell n fit z ∧
      fields.rows=slots.result.1 ∧ fields.cols=slots.result.2 ∧ fields.modes=ms ∧
      op.steps=fw.length*(p+6)+uvWidth fw.length ell p+2+probeCopyFee p ell fw.length+
        slots.steps+modes.steps+10 := by
  let enc := encodeProbe hp vell coord
  let fields : OriginFields a p ell q fw i := ⟨enc.result,slots.result.1,slots.result.2,ms⟩
  have C := origin_fields_written enc.result slots modes ms hModes
  have W := encodeProbe_is_literal hp vell hF coord _ literal
  have F := encodeProbe_cost hp vell coord
  refine ⟨fields,?_,W,rfl,rfl,rfl,?_⟩
  · change (assembleOriginFields enc.result slots modes).result=some fields
    rw [C]
  · change enc.steps+(assembleOriginFields enc.result slots modes).steps+4=_
    rw [C,F]
    dsimp only
    omega

#print axioms actual_probe_capsule
end J6R27OriginalGate


