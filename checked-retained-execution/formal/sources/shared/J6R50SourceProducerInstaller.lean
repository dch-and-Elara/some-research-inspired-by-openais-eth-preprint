import J6R50SourceProducerStep
import J6R48GeneratedAddonsBill

/-! No incoming SiteInputs table for the new occurrence. The exact
next physical file and typed inherited origins are used to read and
install the actual half-port sidecar online. The per-port query tape
and resident owner/seat banks remain explicit local inputs. -/
namespace J6R50SourceProducer
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes J6R11Repack
open J6R32ChildResidentTransfer J6R48RawRoute J6R33GeneratedChildSite J6R49SourceLayout
open J6R34RootAtlas J6R16ModeCost J6R48GeneratedAddons
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3250
set_option maxHeartbeats 11900000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (X : StoredSite T v key prec tw bw page)
variable {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q}
variable {H : Replayed X.site w q U}
variable (W : NativeEventOnly H)
local notation "nx" => (successorTicket v w)
local notation "actual" => (compileOccurrence (localEventInput W))
local notation "canonical" => (occurrencePageWord (localEventInput W))

structure LocalDirectory where
  k1 : ℕ
  k2 : ℕ
  ow : ℕ
  oldKey : v.child.host.Row⊕v.child.host.Col→Word ow
  owners : List (RefRow k1 (Word ow × Origin key prec page))
  seats : List (RefRow k2 (SeatField (dim nx) page))
  queries : Port v.child.host.Edge→Meter (Word k1 × Word k2 × Bool)
  fallback : Addon ow (dim nx) key prec page
  valid : NativeTables X.childOrigins oldKey canonical owners seats queries

def LocalDirectory.read (D : LocalDirectory X W) (h : Port v.child.host.Edge) :
    Meter (Addon D.ow (dim nx) key prec page) :=
  witnessedReader D.owners D.seats D.queries D.fallback h

theorem directory_row_reads_true_origin (D : LocalDirectory X W) (h : Port v.child.host.Edge) :
    ((D.read X W) h).result=addonAt T nx D.oldKey X.childOrigins canonical h := by
  simp only [LocalDirectory.read,witnessedReader,
    no_raw_row_miss X.childOrigins D.oldKey canonical D.owners D.seats D.queries D.valid h,Option.getD_some]

def siteFromProducedOccurrence (D : LocalDirectory X W) :
    SiteInputs actual X.childOrigins :=
  J6R48GeneratedAddons.SiteInputs.fromReader actual X.childOrigins D.oldKey canonical
    (D.read X W) (directory_row_reads_true_origin X W D)

def prepareOnlineAdvance (D : LocalDirectory X W) : Advance X w :=
  fromSelected X w W (siteFromProducedOccurrence X W D) rfl

theorem locality_without_presupplied_next_site (D : LocalDirectory X W) :
    let next := prepareOnlineAdvance X W D
    next.next.birth=actual ∧ next.next.origins=X.childOrigins ∧
      next.next.site.pageKey=canonical ∧
      (∀ h,(next.next.birth.native.physical.record h).body=
        (X.site.issuedLane (childHalves T v (edge h)) (side h)).body) := by
  let new := prepareOnlineAdvance X W D
  exact ⟨rfl,new.liveOrigins,new.next.canonical,new.exactBody⟩

theorem actual_generated_sidecar_has_measured_read_cost (D : LocalDirectory X W) :
    let bank := emit (D.read X W) (actual).native.physical.order
    let site := siteFromProducedOccurrence X W D
    site.install.result=some ((actual).native.physical.order.map
      (fun h=>⟨((actual).native.physical.record h).address,
        addonAt T nx D.oldKey X.childOrigins canonical h⟩)) ∧
      bank.steps+site.install.steps=8+
        ((actual).native.physical.order.map (fun h=>((D.read X W) h).steps+
          addonFee D.ow (dim nx) key prec page ((D.read X W) h).result.oldOrigin.pageKey.isSome+4)).sum+
        (bank.result.map (fun x=>3*(actual).port+11+
          addonFee D.ow (dim nx) key prec page x.oldOrigin.pageKey.isSome)).sum :=
  generated_install_exact actual X.childOrigins D.oldKey canonical (D.read X W)
    (directory_row_reads_true_origin X W D)

section Existence
variable {W}

theorem single_demand_is_producible_without_a_prebuilt_child
    (supply : ∀ R : Replayed X.site w q U, ∃ V : NativeEventOnly R, Nonempty (LocalDirectory X V)) :
    Nonempty (Advance X w) := by
  obtain ⟨R,_⟩ := replay_actual_selected_from_parent_frames X.site w q U
  obtain ⟨V,⟨D⟩⟩ := supply R
  exact ⟨prepareOnlineAdvance X V D⟩
end Existence

#print axioms directory_row_reads_true_origin
#print axioms locality_without_presupplied_next_site
#print axioms actual_generated_sidecar_has_measured_read_cost
#print axioms single_demand_is_producible_without_a_prebuilt_child
end
end J6R50SourceProducer