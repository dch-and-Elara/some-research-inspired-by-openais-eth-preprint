import J6R52DispatchProbe
import J6R30ProducedGateRegistryContext

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9500000
set_option maxRecDepth 2400

/-! The real centre context carries a signed value, not R26's arbitrary
centre ordinal. Keep the installed signed key list explicit and find
its ordinal by actual comparison, without computing an old centre term. -/
namespace J6R52Dispatch
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R27OriginalGate
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R25PreparedSupply J6R51Dispatch J6R26DescriptorTree J6R24MeteredRecursion
open J6R30ProducedGateRegistry

def signedKey (tw : ℕ) (negative : Bool) (magnitude : Word tw) : Word (1+tw) :=
  joinKey (⟨[negative],rfl⟩ : Word 1) magnitude

def signedSpec (tw : ℕ) (z : ℤ) : Word (1+tw) :=
  signedKey tw (decide (z<0)) (word z.natAbs)

theorem exact_signed_context {tw bw : ℕ} (ctx : CentreContext tw bw)
    (canonical : ctx.negative=true → 0<ctx.magnitude.val) :
    signedKey tw ctx.negative ctx.magnitude = signedSpec tw ctx.center := by
  cases h : ctx.negative
  · have nn : ¬ctx.center<0 := by simp [CentreContext.center,h]
    have mag : ctx.center.natAbs=ctx.magnitude.val := by simp [CentreContext.center,h]
    simp only [signedSpec,decide_eq_false nn,mag,valued_word]
  · have hn : ctx.center<0 := by
      have pos := canonical h
      simp only [CentreContext.center,h,ite_true]
      omega
    have mag : ctx.center.natAbs=ctx.magnitude.val := by simp [CentreContext.center,h]
    simp only [signedSpec,decide_eq_true hn,mag,valued_word]

theorem signed_spec_inj_of_fit {tw : ℕ} {x y : ℤ}
    (hx : x.natAbs<2^tw) (hy : y.natAbs<2^tw) (eq : signedSpec tw x=signedSpec tw y) : x=y := by
  obtain ⟨L,R⟩ := join_key_equality eq
  have s : decide (x<0)=decide (y<0) := by
    have f := congrArg Word.bits L
    exact List.cons.inj f |>.1
  have m : x.natAbs=y.natAbs := by
    have f := congrArg Word.val R
    simpa only [word_val hx,word_val hy] using f
  by_cases xl : x<0
  · have yl : y<0 := of_decide_eq_true (s.symm.trans (decide_eq_true xl))
    rcases Int.natAbs_eq_natAbs_iff.mp m with e|e
    · exact e
    · omega
  · have yl : ¬y<0 := of_decide_eq_false (s.symm.trans (decide_eq_false xl))
    rcases Int.natAbs_eq_natAbs_iff.mp m with e|e
    · exact e
    · omega

def readCentreOrdinal {tw bw tc : ℕ} (context : CentreContext tw bw)
    (file : List (List (Word (1+tw)))) : Meter (Option (Word tc)) :=
  let current := copyFixed (signedKey tw context.negative context.magnitude)
  let ord := readPriorOrdinal (tm:=tc) [current.result] file
  ⟨ord.result,current.steps+ord.steps+5⟩

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

noncomputable def centreTable {tw : ℕ} (T : Prepared cfg sel root hf) (v : Ticket sel root) :
    List (List (Word (1+tw))) :=
  (ticketActive T v).centres.map (fun x=>[signedSpec tw x.val])

theorem paid_actual_centre_ordinal {tw bw tc : ℕ} (T : Prepared cfg sel root hf) (v : Ticket sel root)
    (ctx : CentreContext tw bw) (atCentre : ctx.center=v.centerAt.val)
    (canonical : ctx.negative=true → 0<ctx.magnitude.val)
    (fits : ∀ t : Center S v.parent,t.val.natAbs<2^tw)
    (file : List (List (Word (1+tw)))) (fileExact : file=centreTable (tw:=tw) T v)
    (ht : 0<tc) (room : file.length<2^tc) :
    let out := readCentreOrdinal (tc:=tc) ctx file
    out.result=some (word (centerOrdinal T v)) ∧
      (word (q:=tc) (centerOrdinal T v)).val=centerOrdinal T v ∧
      out.steps≤3*(1+tw)+1+(3*tc+7+file.length*(10*(1+tw)+9+13*tc+12))+5 := by
  let codes := fun x : Center S v.parent=>[signedSpec tw x.val]
  have inj : Function.Injective codes := by
    intro x y e
    exact Subtype.ext (signed_spec_inj_of_fit (fits x) (fits y) (List.cons.inj e).1)
  have current : [signedKey tw ctx.negative ctx.magnitude]=codes v.centerAt := by
    rw [exact_signed_context ctx canonical,atCentre]
  have present : [signedKey tw ctx.negative ctx.magnitude]∈file := by
    rw [current,fileExact]
    exact List.mem_map_of_mem (f:=codes) ((ticketActive T v).centreComplete v.centerAt)
  have idx : file.idxOf [signedKey tw ctx.negative ctx.magnitude]=centerOrdinal T v := by
    rw [current,fileExact]
    unfold centreTable
    refine (idx_of_real_beq_encoding codes inj v.centerAt (ticketActive T v).centres).trans ?_
    unfold centerOrdinal
    apply same_index_for_lawful_comparators <;> infer_instance
  obtain ⟨seen,fee⟩ := read_prior_ordinal_correct (tm:=tc)
    [signedKey tw ctx.negative ctx.magnitude] file ht room present
  have bound : centerOrdinal T v<2^tc := idx ▸ (List.idxOf_lt_length_iff.mpr present).trans room
  rw [idx] at seen
  simp only [readCentreOrdinal,copy_fixed_exact]
  refine ⟨seen,word_val bound,?_⟩
  simp only [List.length_singleton,one_mul] at fee
  omega

#print axioms exact_signed_context
#print axioms signed_spec_inj_of_fit
#print axioms paid_actual_centre_ordinal
end J6R52Dispatch

