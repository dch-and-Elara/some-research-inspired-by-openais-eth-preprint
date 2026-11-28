import J6R68OrdinalPeakMergeScope
import J6R63OrdinalObservedRun
import J6R66ActiveRun

/-! A ranked callback at the actual R66 live-header entry. It consumes
the current pulse, then uses the very same scoped publication,
sidecar and incoming-header continuation as R66. The new supplier is
an explicitly metered current request, not a supplied LocalLoad. -/
namespace J6R68.OrdinalPeakMerge
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active J6R15ModeCost J6R16ModeCost J6R25PreparedSupply
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R21Ancestor J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R48RawRoute J6R49DFS
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52Dispatch J6R52CacheWhole
open J6R62ActivePrep J6R58OrdinalSpace J6R63Ordinal J6R63Active J6R64Active J6R66Active
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4550
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 14000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "E" => (Entered T key prec tw bw page)
local notation "MK" => (OnlineMachine T key prec tw bw page (q+1))
local notation "Configure" => (RetainedAfter T key prec tw bw page (q+1) cw)

abbrev nowPath (x : Entered T key prec tw bw page) := Path.step x.path x.slot

abbrev atActive (M : MK) (F : Configure) (x : E) (on : (SP).cutoff<x.call.edges) :=
  preparedAfter M F.live x.path x.slot x.site x.bank x.owner on

def atAddress (x : E) (on : (SP).cutoff<x.call.edges)
    (t : Center SP x.call) (z : Probe SP x.call) (β : NativeMenu (N sel) x.call t)
    (g : Fin 64) : (@Plan f ell s sel).Slot x.call :=
  addressed (sel:=sel) (readyAtPath T (nowPath x) on) t z β g

structure RankedRequests (M : MK) (F : Configure) (b : ℕ) where
  positive : 0<b
  archive : ∀ (x : E) (on : (SP).cutoff<x.call.edges) (t : Center SP x.call),
    HonestArchive ((atActive M F x on).result.tape t).tape.result
      (centreArchiveOrdinal T (nowPath x) on t) b
  current : ∀ (x : E) (_cache : CachedParentFrames x.site.site) (on : (SP).cutoff<x.call.edges) (t : Center SP x.call)
      (z : Probe SP x.call) (β : NativeMenu (N sel) x.call t) (g : Fin 64)
      (_raw : List (Word (q+1))),
    Meter (Request (X:=x.site) (w:=atAddress x on t z β g) (q:=q)
      ((atActive M F x on).result.tape t).tape.result)

variable {M : OnlineMachine T key prec tw bw page (q+1)}
variable {F : RetainedAfter T key prec tw bw page (q+1) cw} {b : ℕ}

def rankedLoad (R : RankedRequests M F b) (x : E) (cache : CachedParentFrames x.site.site)
    (on : (SP).cutoff<x.call.edges)
    (t : Center SP x.call) (z : Probe SP x.call) (β : NativeMenu (N sel) x.call t)
    (raw : List (Word (q+1))) (i : Word b)
    (wordExact : raw.map Word.val=vectorKey sel (readyAtPath T (nowPath x) on) t
      ((atActive M F x on).result.tape t).tape.result β)
    (rankExact : i.val=centreArchiveOrdinal T (nowPath x) on t β) (g : Fin 64) :
    Meter (LocalLoad x.site (atAddress x on t z β g)) :=
  acceptCurrent (R.current x cache on t z β g raw) raw i wordExact
    (rankExact.trans (centre_archive_word_is_original_ticket_ordinal T (nowPath x) on t z β g))

abbrev StateContinuation (x : Entered T key prec tw bw page) :=
  (y : Entered T key prec tw bw page) → y.call.edges<x.call.edges → EntryOut y

def rankedHeaderReader (R : RankedRequests M F b) (retire : J → ℕ)
    (x : E) (cache : CachedParentFrames x.site.site) (on : (SP).cutoff<x.call.edges)
    (recur : StateContinuation x) :
    ActiveReader (atActive M F x on).result (centreArchiveOrdinal T (nowPath x) on) b := by
  let d := readyAtPath T (nowPath x) on
  intro t z β raw i rlaw ilaw g
  let w := atAddress x on t z β g
  let req := rankedLoad R x cache on t z β raw i rlaw ilaw g
  exact project (openOnce req cache retire
    (fun next res bank own=>
      recur ⟨x.call,nowPath x,w,next,res,bank,own⟩ ((@Plan f ell s sel).smaller x.call w))
    (zeroM (T.bank (registerPrecision SP x.call t) (register_positive d t)).hp) x.bank)

def oldHeaderReader (retire : J → ℕ) (x : E) (cache : CachedParentFrames x.site.site)
    (on : (SP).cutoff<x.call.edges)
    (recur : StateContinuation x) :
    ActiveChild (sel:=sel) (d:=readyAtPath T (nowPath x) on) T.bank :=
  fun t z β g=>
    let d := readyAtPath T (nowPath x) on
    let w := atAddress x on t z β g
    project (openOnce (M.demand x.site w) cache retire
      (fun next res bank own=>
        recur ⟨x.call,nowPath x,w,next,res,bank,own⟩ ((@Plan f ell s sel).smaller x.call w))
      (zeroM (T.bank (registerPrecision SP x.call t) (register_positive d t)).hp) x.bank)

#print axioms atActive
#print axioms RankedRequests
#print axioms rankedLoad
#print axioms rankedHeaderReader
#print axioms oldHeaderReader
end
end J6R68.OrdinalPeakMerge

