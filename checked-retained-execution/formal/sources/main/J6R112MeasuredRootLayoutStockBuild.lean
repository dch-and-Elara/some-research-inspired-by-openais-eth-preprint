import J6R112MeasuredRootLayoutStockTapes
import J6R52CacheSourceReplay

/-! A root layout stock is now the result of actual measured work.
Both outside inputs are held physical products of the same rooted
chart: the stable-key suffix bank and the ordered physical half tape.
Here we charge the actual owner join and the actual physical-order
name read/copier, not a guessed callback tariff. -/
namespace J6R112MeasuredRootLayoutStock
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R36ChildFramedRoute J6R27OriginalGate
open J6OrientedHost J6Mesh J6R10Repack J6R11Repack J6R21Leaf
open J6R24LegalLayout J6R28GeneratedRootFrame J6R52CacheSource
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R53OldOwnerRoot J6R53OldOwner J6R53TerminalGate
open J6R54ExteriorOwner J6R94ExteriorDebit

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 5500000
set_option maxRecDepth 4500
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V] {m n : ℕ} (P : Plant V m n)
structure HeldPhysicalHalves where
  raw : List (PortRow (rootHalfWidth m))
  exactOrder : raw=(rootHalfOrder m).map (expectedHalfRow P (oddAxis m))

/-- Fallback if the original scanner did not retain its result. This
actually re-emits the original physical half tape and bills its Meter. -/
def emitPhysicalHalves {r c d : ℕ} (literal : LiteralPortFile P r c d) :
    Meter (HeldPhysicalHalves P) :=
  let A := makeHalfTape m [] literal.raw
  ⟨⟨A.result,(actual_root_half_tape literal (oddAxis m) [] rfl).1⟩,A.steps⟩

variable {r c d own rank width key prec page : ℕ}
variable (literal : LiteralPortFile P r c d) (axis : List Bool) (clock : axis.length=(oddAxis m).val)
variable {name : (SourceVertex P)→Word own} {payload : (SourceVertex P)→OwnerData width key prec page}
variable (actual : CompleteRoster name payload) (inj : Function.Injective name)
variable {origin : (SourceVertex P)→Origin key prec page} {choice : (SourceVertex P)→HeadChoice rank}
variable (plans : List (OwnerPlan own rank (SuffixKeyWidth m) key prec page))
variable (planned : plans=actual.order.map (rootPlanWord P name origin choice))
variable (suffixes : SuffixBank m) (suffixOK : suffixes=(paidRootSuffixBank m axis literal.raw).result)
variable (halves : HeldPhysicalHalves P)

include literal axis clock planned suffixOK in
theorem actual_paid_old_names_and_scopes_are_the_checked_tapes :
    (compileActualOwnerTapes P suffixes actual.order actual.raw plans).result=
      some (actual.order.map (fun u=>(name u,trueRootRole u)),candidateNames P name actual.order) := by
  rw [actual.exactRows,planned]
  exact actual_order_and_scopes_emit_both_original_tapes P literal axis clock suffixes suffixOK
    name payload origin choice actual.order

def layoutStockOnHeldTapes : Meter (RootLayoutStock P name) :=
  let raw := compileActualOwnerTapes P suffixes actual.order actual.raw plans
  let receipt := actual_paid_old_names_and_scopes_are_the_checked_tapes
    P literal axis clock actual plans planned suffixes suffixOK
  have hi : raw.result.isSome := by
    change (compileActualOwnerTapes P suffixes actual.order actual.raw plans).result.isSome
    rw [receipt]
    rfl
  let both := unwrapSuccess raw hi
  have ex : both.result=_ := congrArg Meter.result (unwrap_success_exact raw hi _ receipt)
  have roles : both.result.1=actual.order.map (fun u=>(name u,trueRootRole u)) := congrArg Prod.fst ex
  have candidate : both.result.2=candidateNames P name actual.order := congrArg Prod.snd ex
  let finish := bookInPhysicalOrder m both.result.2 halves.raw
  have done := original_physical_order_enumerates_same_words P name actual.order actual.complete
    both.result.2 candidate halves.raw halves.exactOrder
  have has : finish.result.isSome := by
    change (bookInPhysicalOrder m both.result.2 halves.raw).result.isSome
    rw [done]
    rfl
  let names := unwrapSuccess finish has
  have named : names.result=_ := congrArg Meter.result (unwrap_success_exact finish has _ done)
  ⟨⟨actual.order,actual.unique,actual.complete,both.result.1,roles,names.result,named,inj⟩,
    both.steps+names.steps+5⟩

theorem same_complete_order_including_every_isolated_owner :
    let out := layoutStockOnHeldTapes P literal axis clock actual inj plans planned suffixes suffixOK halves
    out.result.order=actual.order ∧ (∀ u,u∈out.result.order) := ⟨rfl,actual.complete⟩

theorem actual_stock_fee_is_the_owner_join_then_one_wire_read :
    let out := layoutStockOnHeldTapes P literal axis clock actual inj plans planned suffixes suffixOK halves
    let raw := compileActualOwnerTapes P suffixes actual.order actual.raw plans
    let candidate := (raw.result.map Prod.snd).getD []
    out.steps=raw.steps+(bookInPhysicalOrder m candidate halves.raw).steps+5 := by
  let raw := compileActualOwnerTapes P suffixes actual.order actual.raw plans
  have ex := actual_paid_old_names_and_scopes_are_the_checked_tapes
    P literal axis clock actual plans planned suffixes suffixOK
  have someRaw : raw.result.isSome := by
    change (compileActualOwnerTapes P suffixes actual.order actual.raw plans).result.isSome
    rw [ex]
    rfl
  have E := unwrap_success_exact raw someRaw _ ex
  have C : (raw.result.map Prod.snd).getD []=candidateNames P name actual.order := by
    change ((compileActualOwnerTapes P suffixes actual.order actual.raw plans).result.map Prod.snd).getD []=_
    rw [ex]
    rfl
  unfold layoutStockOnHeldTapes
  dsimp only
  change raw.steps+(bookInPhysicalOrder m (unwrapSuccess raw someRaw).result.2 halves.raw).steps+5=_
  rw [E,C]

/-- If neither physical precursor was kept, use two genuine source
scans and pay them. The already received owner roster/plan is not
rebuilt. The shared-image specialization avoids these repeated scans. -/
def layoutStockByPaidRescan : Meter (RootLayoutStock P name) :=
  let suffix := paidRootSuffixBank m axis literal.raw
  let phys := emitPhysicalHalves P literal
  let stock := layoutStockOnHeldTapes P literal axis clock actual inj plans planned
    suffix.result rfl phys.result
  ⟨stock.result,suffix.steps+phys.steps+stock.steps+4⟩

theorem the_reconstruction_bills_both_actual_source_emitters :
    let suffix := paidRootSuffixBank m axis literal.raw
    let phys := emitPhysicalHalves P literal
    let stock := layoutStockOnHeldTapes P literal axis clock actual inj plans planned
      suffix.result rfl phys.result
    (layoutStockByPaidRescan P literal axis clock actual inj plans planned).steps=
      suffix.steps+phys.steps+stock.steps+4 := rfl


#print axioms emitPhysicalHalves
#print axioms actual_paid_old_names_and_scopes_are_the_checked_tapes
#print axioms layoutStockOnHeldTapes
#print axioms same_complete_order_including_every_isolated_owner
#print axioms actual_stock_fee_is_the_owner_join_then_one_wire_read
#print axioms the_reconstruction_bills_both_actual_source_emitters
end
end J6R112MeasuredRootLayoutStock

