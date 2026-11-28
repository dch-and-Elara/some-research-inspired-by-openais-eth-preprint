import J6R112MeasuredRootLayoutStockBuild
import J6R57PublicRequestImage

/-! Bind the two outputs to the one actual R57 request image. In
particular borrow the returned image's charged parent half tape;
we do not evaluate its proof normal form to obtain a second file. -/
namespace J6R112MeasuredRootLayoutStock
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R36ChildFramedRoute J6R27OriginalGate
open J6OrientedHost J6Mesh J6R10Repack J6R11Repack J6R21Leaf
open J6R24LegalLayout J6R28GeneratedRootFrame J6R52CacheSource
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R53OldOwnerRoot J6R53OldOwner J6R53TerminalGate
open J6R54ExteriorOwner J6R94ExteriorDebit
open J6R26StablePreparedRoot J6R34RootAtlas J6R35GatewayPreparation
open J6R54PublicFamily J6R57PublicRequest J6R14ZeroMode J6R52FreshExterior J6R27PrescribedProbe

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 8500000
set_option maxRecDepth 4900
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V] {m n base native : ℕ} {P : Plant V m n}
variable {f : ℤ[X]}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q r c d prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q r c d prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (image : RequestImage W I)

theorem held_parent_rows_are_the_real_physical_order :
    image.tables.root.parents=(rootHalfOrder m).map (expectedHalfRow P (oddAxis m)) := by
  let C := image.compiled
  have copy : 0<q :=
    Nat.zero_lt_one.trans (copy_width_above_one (by rw [←C.copiesOK]; exact val_lt C.regs.copies))
  have held := congrArg ActualRootPreparation.parents image.tables.exactRoot
  have physical := (actual_shared_parent_file G C.literal ell ⟨C.frame,0⟩ copy C.regs.copies C.regs.pre
    (⟨0,Nat.succ_pos _⟩ : J6Recovery.Addr m)).1
  have actual := (actual_root_half_tape C.literal (oddAxis m) [] rfl).1
  exact held.trans (physical.trans actual)

def halfTapeFromImage : HeldPhysicalHalves P :=
  ⟨image.tables.root.parents,held_parent_rows_are_the_real_physical_order image⟩

section Source
variable {own rank key gp page width : ℕ}
variable (axis : List Bool) (clock : axis.length=(oddAxis m).val)
variable {name : SourceVertex P→Word own}
variable {value : SourceVertex P→OwnerData width key gp page}
variable (root : CompleteRoster name value) (inj : Function.Injective name)
variable {origin : SourceVertex P→Origin key gp page}
variable {choice : SourceVertex P→HeadChoice rank}
variable (plans : List (OwnerPlan own rank (SuffixKeyWidth m) key gp page))
variable (aligned : plans=root.order.map (rootPlanWord P name origin choice))

/-- The same returned request image already owns its half geometry.
If the earlier owner mount did not retain its stable suffix table,
only that one missing tape is really generated again. -/
def stockOnHeldImageWithOneSuffixScan : Meter (RootLayoutStock P name) :=
  let suffix := paidRootSuffixBank m axis image.compiled.literal.raw
  let bytes := layoutStockOnHeldTapes P image.compiled.literal axis clock root inj
    plans aligned suffix.result rfl (halfTapeFromImage image)
  ⟨bytes.result,suffix.steps+bytes.steps+4⟩

theorem one_paid_suffix_scan_on_the_same_image_and_roster :
    let suffix := paidRootSuffixBank m axis image.compiled.literal.raw
    let bytes := layoutStockOnHeldTapes P image.compiled.literal axis clock root inj
      plans aligned suffix.result rfl (halfTapeFromImage image)
    let made := stockOnHeldImageWithOneSuffixScan image axis clock root inj plans aligned
    made=⟨bytes.result,suffix.steps+bytes.steps+4⟩ ∧ made.result.order=root.order := ⟨rfl,rfl⟩

#print axioms stockOnHeldImageWithOneSuffixScan
#print axioms one_paid_suffix_scan_on_the_same_image_and_roster
end Source

#print axioms held_parent_rows_are_the_real_physical_order
#print axioms halfTapeFromImage
end
end J6R112MeasuredRootLayoutStock
