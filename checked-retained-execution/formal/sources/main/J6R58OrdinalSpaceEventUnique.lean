import J6R52DispatchAccept

/-! For one genuine occurrence, checked fixed-width metadata and
receiver-order exponent bytes are unique. Therefore any two paid
implementations delivering that checked event feed the same real
source payload shell/directory, regardless of their different fees. -/
namespace J6R58OrdinalSpace
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J1PPrinted J6R12Blueprint J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R50SourceProducer J6R51Online J6R52Dispatch
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 3500
set_option maxHeartbeats 19000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

theorem unsigned_word_value_injective {w : ℕ} :
    Function.Injective (@Word.val w) := by
  intro x y eq
  rw [←valued_word x,←valued_word y,eq]

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
variable {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q} (R : Replayed X.site w q U)
variable {tc tz tm : ℕ}

theorem checked_occurrence_bytes_are_unique {e e' : EventBytes (q+1) tc tz tm}
    (G : EventGood R e) (G' : EventGood R e') : e=e' := by
  have data := List.map_injective_iff.mpr unsigned_word_value_injective
    (G.exponents.trans G'.exponents.symm)
  have centre := unsigned_word_value_injective (G.centre.trans G'.centre.symm)
  have probe := unsigned_word_value_injective (G.probe.trans G'.probe.symm)
  have mode := unsigned_word_value_injective (G.mode.trans G'.mode.symm)
  have group := unsigned_word_value_injective (G.group.trans G'.group.symm)
  cases e
  cases e'
  simp only [EventBytes.mk.injEq]
  exact ⟨data,centre,probe,mode,group⟩

theorem genuine_acceptance_depends_on_event_not_its_search_fee
    (shell : PayloadShell R) (directory : DirectorySeed R shell)
    (left right : Meter (Option (EventBytes (q+1) tc tz tm)))
    (goodFrom : CheckedEvent R left) (goodTo : CheckedEvent R right) :
    (acceptLocalLoad R shell directory left goodFrom).result=
      (acceptLocalLoad R shell directory right goodTo).result := by
  have same : left.result=right.result := by
    obtain ⟨a,ha,ga⟩ := goodFrom
    obtain ⟨b,hb,gb⟩ := goodTo
    rw [ha,hb,checked_occurrence_bytes_are_unique R ga gb]
  cases left with
  | mk result fee =>
    cases right with
    | mk result' fee' =>
      change result=result' at same
      subst result'
      rfl

#print axioms unsigned_word_value_injective
#print axioms checked_occurrence_bytes_are_unique
#print axioms genuine_acceptance_depends_on_event_not_its_search_fee
end
end J6R58OrdinalSpace
