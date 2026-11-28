import J6R50ModeDispatchCore
import J6R49DFSVisitMath

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4800000
set_option maxRecDepth 2300

/-! On an actual R49 pulse the measured sparse writer uses exactly
the canonical raw bits of the unique legal mode. The returned counter
is physical; the typed identity is a proof-only result. -/
namespace J6R50ModeDispatch
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R48DFS J6R49DFS J6R22Active A1R12

variable {f : ℤ[X]} {ell q tm : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}
local notation "M" => NativeMenu (shape S Δ sel) c t

theorem actual_pulse_sparse_and_increment
    (F : Frame f (registerPrecision S c t)) (I : SiteTape sel d t q) (hq : 0<q) (hv : 0<ell)
    (child : M → Fin 64 → Meter (Block F ell))
    (startState : Pending q I.words.length) (start : (startingCursor I hq).result=some startState)
    (now : Pending q I.words.length) (outer : Block F ell) (fee : ℕ)
    (previous : ModePrefix (modeUpdate F I hv child) startState
      (zeroM (ell:=ell) (f:=F.words) F.hp).result
      ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I hq).steps) now outer fee)
    (raw : List (Word q)) (nextState : State q) (emit : now.pulse.result=.emit raw nextState)
    (roster : List (RawMode q)) (rs : roster.length=I.modes.length)
    (ordinal : Word tm) (ht : 0<tm) (fit : ordinal.val+1<2^tm) :
    let a := S.levelBits c.depth
    let m := prepareMode a roster raw ordinal
    ∃ β : M,decodeAt I raw=some β ∧
      ∃ o : OpenMode q tm,m.result=some o ∧
      o.support=supportSpec roster ((vectorKey sel d t I β).map word) ∧
      o.next.val=ordinal.val+1 ∧ m.steps=roster.length*dispatchStride a q+13*tm+13 := by
  obtain ⟨β,hβ,key⟩ := legal_emission_from_real_probe F I hq hv child startState start now outer fee previous raw nextState emit
  have rawExact : (vectorKey sel d t I β).map word=raw := by
    rw [key]
    exact canonical_tuple_words raw
  have length : roster.length=raw.length := by
    have h := congrArg List.length rawExact
    rw [rs]
    simpa only [List.length_map,vectorKey] using h
  obtain ⟨res,valuation,cost⟩ :=
    prepare_emitted_mode_exact (S.levelBits c.depth) roster raw ordinal length ht fit
  refine ⟨β,hβ,⟨ordinal,(increment ordinal).result,supportSpec roster raw⟩,res,?_,valuation,cost⟩
  rw [rawExact]

#print axioms actual_pulse_sparse_and_increment
end J6R50ModeDispatch

