import J6R63OrdinalSite
import J6R58OrdinalSpacePermutation
import J6R32StatefulArithmeticPath

/-! Actual R26 Ticket names on a real R32 path, kept out of the
reusable cursor driver so no path descriptor is a runtime argument. -/
namespace J6R63Ordinal
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R58OrdinalSpace J6R26DescriptorTree J6R25PreparedSupply
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 6000000
set_option Elab.async false
noncomputable section
variable {f : ℤ[X]} {ell s C q b : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)

variable {root : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel root hf)

noncomputable def centreArchiveOrdinal (p : J6R32StatefulArithmetic.Path sel root c)
    (a : (SP).cutoff<c.edges) (t : Center SP c) (β : NativeMenu (N sel) c t) : ℕ :=
  ((T.active c p.reached a).tape t).modes.idxOf β

theorem centre_archive_word_is_original_ticket_ordinal
    (p : J6R32StatefulArithmetic.Path sel root c) (a : (SP).cutoff<c.edges)
    (t : Center SP c) (z : Probe SP c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let ticket := p.ticket (addressed (sel:=sel) d t z β g)
    centreArchiveOrdinal T p a t β=modeOrdinal T ticket := by
  dsimp only
  rw [actual_mode_ordinal_is_index]
  all_goals rfl

theorem original_archive_agrees_on_this_actual_site
    (p : J6R32StatefulArithmetic.Path sel root c) (a : (SP).cutoff<c.edges)
    (t : Center SP c) (I : SiteTape sel (ready_reachable cfg sel p.reached T.rootStable a) t q)
    (fits : ((T.active c p.reached a).tape t).modes.length<2^b)
    (same : ((T.active c p.reached a).tape t).modes.map (vectorKey sel
      (ready_reachable cfg sel p.reached T.rootStable a) t I)=tupleSpec I) :
    HonestArchive I (centreArchiveOrdinal T p a t) b := by
  classical
  let tape := (T.active c p.reached a).tape t
  exact ⟨tape.modes,fits,prefix_names_from_a_lawful_archival_index
    (centreArchiveOrdinal T p a t) tape.modes tape.modeUnique (fun _=>rfl),same⟩

#print axioms centre_archive_word_is_original_ticket_ordinal
#print axioms original_archive_agrees_on_this_actual_site
end
end J6R63Ordinal
