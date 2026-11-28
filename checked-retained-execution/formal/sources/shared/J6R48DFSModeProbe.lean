import J6R48DFSGroupFold
import J6R17ModeTapeReach

/-! Bind a single streaming probe to its actual printed weight tape
and actual 64 child slots. Exactness metering is independent of how
the raw child callback gets its answer; the correspondence required
of it is stated on the same center/probe/mode/group, not on unrelated
valid graphs. The whole resident recursive run is a separate file. -/
namespace J6R48DFS
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R17ModeTape J6R25PreparedSupply J6R18ChildWrite

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 11000000

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell)) (hf : f.Monic)
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem streamed_native_probe (c : Call (PhysicalHost f ell))
    (hReach : NativeReach (Plan sel) r c) (d : Ready S (sourceDelta s) c)
    (t : Center S c) (z : Probe S c) {q : ℕ} (hq : 0<q)
    (I : SiteTape sel d t q)
    {fw : List (A1R10.Word (registerPrecision S c t))} (he : 0<fw.length) (hv : 0<ell)
    (hF : Modulus (registerPrecision S c t) (register_positive d t) fw=
      NativeProbeRing.liftPoly (registerPrecision S c t) f)
    (raw : List (J6R15ModeCost.Word q)→Fin 64→Meter (UVBlock fw ell))
    (hRead : ∀ β g,
      castBox hF (uvRead (register_positive d t) fw ell
        (raw ((vectorKey sel d t I β).map J6R15ModeCost.word) g).result)=
      (sourceBlueprint sel r hf).program.run ((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩)) :
    let B := sourceBlueprint sel r hf
    let reads : Responses (paddedShape (N sel) (Childs sel) r) f ell c :=
      fun a=>B.program.run (B.program.child c a)
    let hp := register_positive d t
    let init := zeroM (ell:=ell) (f:=fw) hp
    let op := modeAddition hp he hv raw
    let X := J6R15ModeCost.strictTuples (I.modes.map J6R15ModeCost.modeWeight) (registerPrecision S c t)
    ∃ P : Pending q I.words.length,
      (J6R15ModeCost.start I.words I.precision).result=.again P.state ∧
      let out := modeDrain op P init.result ((J6R15ModeCost.start I.words I.precision).steps+init.steps)
      out.result.2=true ∧
      castBox hF (uvRead hp fw ell out.result.1)=
        groupedSample (paddedShape (N sel) (Childs sel) r) f ell c reads t z ∧
      out.steps≤
        (16*q+14+4*(I.words.length+1)*(q+1))+init.steps+
          (foldExpected op X init.result).steps+(X.length+1)*J6R15ModeCost.delayCap q I.words.length := by
  let hp := register_positive d t
  let init := zeroM (ell:=ell) (f:=fw) hp
  let op := modeAddition hp he hv raw
  let X := J6R15ModeCost.strictTuples (I.modes.map J6R15ModeCost.modeWeight) (registerPrecision S c t)
  have hP : 0<I.precision.val := I.precisionMeaning ▸ hp
  have hPos (w : J6R15ModeCost.Word q) (hw : w∈I.words) : 0<w.val := by
    have hit : w.val∈I.words.map J6R15ModeCost.Word.val := List.mem_map_of_mem hw
    rw [I.weightMeaning] at hit
    obtain ⟨m,_,hm⟩ := List.mem_map.mp hit
    rw [←hm]
    exact (J6R15ModeCost.modeWeight_bounds m).1
  obtain ⟨_,hStart⟩ := J6R15ModeCost.stream_all_exact hq I.words I.precision hPos
  obtain ⟨w,hRun,hr⟩ := hStart hP.ne'
  have hWF : (J6R15ModeCost.State.enter I.words w []).wellFormed I.words.length := by
    simp [J6R15ModeCost.State.wellFormed,J6R15ModeCost.StackShape]
  rw [I.weightMeaning,I.precisionMeaning] at hr
  let P : Pending q I.words.length := ⟨.enter I.words w [],hWF,⟨X,hr⟩⟩
  let fee := (J6R15ModeCost.start I.words I.precision).steps+init.steps
  let out := modeDrain op P init.result fee
  obtain ⟨v,cost⟩ := halt_driven_fold_exact P X hr op init.result fee
  refine ⟨P,hRun,?_,?_,?_⟩
  · change out.result.2=true
    change out.result=((foldExpected op X init.result).result,true) at v
    rw [v]
  · have e : out.result.1=(foldExpected op X init.result).result := congrArg Prod.fst v
    change castBox hF (uvRead hp fw ell out.result.1)=_
    rw [e,show op=modeAddition hp he hv raw from rfl,mode_fold_value,
      show uvRead hp fw ell init.result=0 from zeroM_read hp,zero_add]
    obtain ⟨order,hN,hAll,hOrder⟩ := native_mode_order sel d t I
    change castBox hF (List.map (fun a=>∏ g : Fin 64,
      uvRead hp fw ell (raw (a.map J6R15ModeCost.word) g).result) X).sum=_
    rw [show X=order.map (vectorKey sel d t I) from hOrder.symm,List.map_map]
    letI : Fintype (NativeMenu (N sel) c t) := nativeMenuFinite (N sel) c t
    rw [complete_sum order hN hAll,grouped_run_reindex sel r hf c hReach d.active t z]
    rw [← boxTransport_cast,map_sum]
    apply Finset.sum_congr rfl
    intro β _
    simp only [Function.comp_apply]
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro g _
    exact (boxTransport_cast hF _).trans (hRead β g)
  · have startCost := (J6R15ModeCost.start_exact hq I.words I.precision).2
    exact cost.trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right startCost _) _) _)

#print axioms streamed_native_probe
end J6R48DFS
