import J6R63OrdinalObservedWords

/-! Follow the actual ranked drain, with its actual accumulation and
fee, from the first cursor through a genuine prefix. This does not
conflate equality of returned banks with a heap-liveness theorem. -/
namespace J6R63Ordinal
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active J6R15ModeCost J6R16ModeCost J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R49DFS J6R58OrdinalSpace
set_option autoImplicit false
set_option maxRecDepth 3200
set_option maxHeartbeats 6300000
set_option Elab.async false

variable {q n b : ℕ} {A : Type*}

theorem clock_prefix_follows_actual_meter
    (Inv : Pending q n → Word b → Prop) (Admit : List (Word q) → Word b → Prop)
    (law : EmissionLaw Inv Admit)
    (send : A → (raw : List (Word q)) → (i : Word b) → Admit raw i → Meter A)
    {first p : Pending q n} {i : Word b}
    (history : ClockPrefix first p i)
    (begins : Inv first (firstOrdinal b).result) (acc : A) (paid : ℕ) :
    ∃ (atP : Inv p i) (value : A) (paidSoFar : ℕ),
      checkedDrain Inv Admit law send first (firstOrdinal b).result begins acc paid =
        checkedDrain Inv Admit law send p i atP value paidSoFar := by
  induction history with
  | initial => exact ⟨begins,acc,paid,rfl⟩
  | @next p i raw st trace event ih =>
    obtain ⟨ready,value,bill,same⟩ := ih
    let receipt := law.next p i raw st event ready
    let out := send value raw i receipt.1
    exact ⟨receipt.2,out.result,bill+p.pulse.steps+(increment i).steps+3+out.steps,
      same.trans (checked_drain_sends_literal_row_and_rank_once Inv Admit law send p i ready value bill event)⟩

noncomputable section
variable {f : ℤ[X]} {ell s : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c}
variable (F : Frame f (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t))
variable (I : SiteTape sel d t q) (ordinal : NativeMenu (N sel) c t → ℕ)

theorem ranked_probe_reaches_its_actual_suffix_meter
    (hq : 0<q) (hb : 0<b) (hv : 0<ell) (archive : HonestArchive I ordinal b)
    (child : RankedChild F I ordinal b) {first p : Pending q I.words.length} {i : Word b}
    (began : (startingCursor I hq).result=some first) (history : ClockPrefix first p i) :
    ∃ (live : SuffixFits I ordinal p i) (value : Block F ell) (paid : ℕ),
      let out := checkedDrain _ _ (native_paid_emit_law I ordinal hb)
        (updateRanked F I ordinal hv child) p i live value paid
      runProbeRanked F I ordinal hq hb hv archive child=⟨out.result.1,out.steps⟩ := by
  let u := zeroM (ell:=ell) (f:=F.words) F.hp
  let k := u.steps+(startingCursor I hq).steps+(firstOrdinal b).steps
  have head := real_cursor_starts_with_checked_archival_rank I ordinal hq archive first began
  obtain ⟨live,v,bill,same⟩ := clock_prefix_follows_actual_meter _ _
    (native_paid_emit_law I ordinal hb) (updateRanked F I ordinal hv child)
    history head u.result k
  refine ⟨live,v,bill,?_⟩
  dsimp only
  rw [ranked_probe_is_one_paid_cursor_loop F I ordinal hq hb hv archive child first began,same]

#print axioms clock_prefix_follows_actual_meter
#print axioms ranked_probe_reaches_its_actual_suffix_meter
end
end J6R63Ordinal
