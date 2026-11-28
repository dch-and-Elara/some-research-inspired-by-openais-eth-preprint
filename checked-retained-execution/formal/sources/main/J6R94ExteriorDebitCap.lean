import J6R94ExteriorDebitInput

/-! A finite bound for the literal marked ingress. Only structural
word widths, file extents, and the actual resident bank size are
assumed; no cap on a complete phase or byte supplier is assumed. -/
namespace J6R94ExteriorDebit
open scoped Classical Polynomial
open J6R64Active J6R32StatefulArithmetic J6R35RootOrigins
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R19Retained
open J6R25PreparedSupply J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R31RootResidentTables
open J6R27OriginalGate J6Mesh J6R49SourceLayout J6R54ExteriorOwner J6R55BootBodies
open J6R30GeneratedRootLayout J6R28GeneratedRootFrame J6R26StablePreparedRoot
open J6R10Repack J6OrientedHost J6R24LegalLayout J6R26DescriptorTree
open J6R32ChildResidentTransfer J6R12CollisionGreedyStep J6R68ActiveInputs
open V8NativeMessage.N2DLabels J6R33StatefulArithmeticPage J6R30ProducedGateRegistry

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 11000000
set_option maxRecDepth 4200
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V] {m n base native : ℕ} {P : Plant V m n}
variable {f : ℤ[X]}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co dep edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co dep edgew tc tj key prec tw bw)
variable (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Bank" => (PageBank f ell key prec tw bw Pg)
local instance capEdge : Fintype (Ext).host.Edge := (Ext).host.finiteEdge

variable {name : SourceVertex P→Word own}
variable (S : RootLayoutStock P name)
variable (buf : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) (live : IsLive (X.seed pad) buf) (ownHead : OwnsHeader X.header.result buf)

structure ExteriorInputWidths (K₀ : ℕ) : Prop where
  owner : own≤K₀
  page : Pg≤K₀
  bankKey : key≤K₀
  prefixWidth : liveReadPrefixWidth tc tj prec edgew≤K₀
  halfAddr : rootHalfWidth m≤K₀
  body : pageKeyWidth m+a m≤K₀
  halfBook : 2*M m≤K₀
  wires : (orderedExteriorEdges X).length≤K₀
  wholeOwners : S.order.length≤K₀
  oldRows : (stageOldOrder X S.order).length≤K₀
  pages : (stagePageOrder X).length≤K₀
  records : buf.records.length≤K₀

private theorem locateFee_mono {w w' n n' : ℕ} (hw : w≤w') (hn : n≤n') :
    locateFee w n≤locateFee w' n' := by
  unfold locateFee
  exact Nat.add_le_add_right (Nat.mul_le_mul hn (by omega)) 2

def installedExteriorTargetRoof (K : ℕ) :=
  (9+(25*K+163)*K)+((16*K+20)*K+10)+((9*K+35)*K+4)+5

def installedExteriorIncidenceRoof (K : ℕ) :=
  (6*K+12+(12*K+52)*K)+(3+(K*(13*K+13)+12*K+24)*K)+4

def installedExteriorRawRoof (K : ℕ) :=
  installedExteriorTargetRoof K+installedExteriorIncidenceRoof K+4

theorem installed_exterior_raw_roof_polynomial (K : ℕ) :
    installedExteriorRawRoof K=13*K^3+87*K^2+300*K+51 := by
  unfold installedExteriorRawRoof installedExteriorTargetRoof installedExteriorIncidenceRoof
  ring

include ownHead in
theorem installed_exterior_incidence_uses_explicit_actual_sizes (K₀ : ℕ)
    (F : ExteriorInputWidths X pad S buf K₀) :
    (writeExteriorIncidences X pad S buf).steps≤ installedExteriorIncidenceRoof K₀ := by
  have h := (true_exterior_incidence_after_named_stock X pad S buf ownHead).2
  have cut := F.prefixWidth
  have width := F.halfAddr
  have body := F.body
  have ho := F.owner
  have page := F.page
  have pag : pageKeyWidth m≤K₀ := by omega
  have slice : publishedPortDebit m tc tj prec edgew (orderedExteriorEdges X).length≤
      6*K₀+12+(12*K₀+52)*K₀ := by
    unfold publishedPortDebit
    have ex : decodeWireFee (rootHalfWidth m) (pageKeyWidth m+a m)+3≤12*K₀+52 := by
      unfold decodeWireFee cutWordFee
      omega
    have read := Nat.mul_le_mul ex F.wires
    unfold cutWordFee
    omega
  have tt : halfPairLimit m pad own (2*M m)≤K₀*(13*K₀+13)+12*K₀+24 := by
    have t := locateFee_mono F.halfAddr F.halfBook
    unfold halfPairLimit pullPageFee cutWordFee wideningFee
    change locateFee (rootHalfWidth m) (2*M m)≤K₀*(13*K₀+13)+2 at t
    omega
  exact h.trans (Nat.add_le_add_right (Nat.add_le_add slice
    (Nat.add_le_add_left (Nat.mul_le_mul tt F.wires) 3)) 4)

include live in
theorem installed_exterior_targets_use_explicit_actual_sizes (K₀ : ℕ)
    (F : ExteriorInputWidths X pad S buf K₀) :
    (writeExteriorTargets X pad S buf).steps≤ installedExteriorTargetRoof K₀ := by
  let H := emitRootHeaders [] S.roles
  let L := trueOldKeyScan X S
  let R := currentPageKeys X pad buf
  let cmds := writeTargets L.result ((R.result.map Prod.snd).getD [])
  have ho := F.owner
  have pw := F.page
  have role : S.roles.length≤K₀ :=
    (complete_stock_uses_exact_number_of_half_ports P S).2.le.trans F.wholeOwners
  have hb : H.steps≤3+(19*K₀+85)*K₀ :=
    actual_header_writer_width_cap [] S.roles ho (Nat.zero_le _) role
  have old : L.steps≤9+(25*K₀+163)*K₀ := by
    have pay := (real_old_roster_from_stock X S).2
    change L.steps=H.steps+3+(3+(3*own+77)*S.order.length+(3*own+1)*(stageOldOrder X S.order).length) at pay
    rw [pay]
    have z := Nat.mul_le_mul (by omega : 3*own+77≤3*K₀+77) F.wholeOwners
    have y := Nat.mul_le_mul (by omega : 3*own+1≤3*K₀+1) F.oldRows
    have fixed : (19*K₀+85)*K₀+(3*K₀+77)*K₀+(3*K₀+1)*K₀=(25*K₀+163)*K₀ := by ring
    omega
  have pp := read_same_live_exterior_page_words X pad buf live
  have pg : R.steps≤(16*K₀+20)*K₀+10 := by
    have dec := pp.2
    change R.steps=_ at dec
    rw [dec]
    have find := (locate_bound (X.seed pad).identifier buf.records).trans (locateFee_mono F.bankKey F.records)
    have pagepay := Nat.mul_le_mul (by omega : 3*Pg+7≤3*K₀+7) F.pages
    unfold locateFee at find
    have fixed : K₀*(13*K₀+13)+(3*K₀+7)*K₀=(16*K₀+20)*K₀ := by ring
    omega
  have tar : cmds.steps≤(9*K₀+35)*K₀+4 := by
    have cost := (targets_exact L.result ((R.result.map Prod.snd).getD [])).2
    change cmds.steps≤_ at cost
    have hl := (real_old_roster_from_stock X S).1
    change L.result=_ at hl
    have hp := pp.1
    change R.result=_ at hp
    rw [hl,hp] at cost
    simp only [Option.map_some,Option.getD_some,List.length_map] at cost
    have l := Nat.mul_le_mul (by omega : 6*own+22≤6*K₀+22) F.oldRows
    have r := Nat.mul_le_mul (by omega : 3*Pg+13≤3*K₀+13) F.pages
    have fixed : (6*K₀+22)*K₀+(3*K₀+13)*K₀=(9*K₀+35)*K₀ := by ring
    omega
  change L.steps+R.steps+cmds.steps+5≤_
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add old pg) tar) 5

theorem actual_installed_exterior_rawDebit_from_widths (rank a₀ K₀ : ℕ)
    (fit : Fintype.card (Ext).host.Edge<2^rank)
    (F : ExteriorInputWidths X pad S buf K₀) :
    (exteriorIngress X pad S buf live ownHead rank a₀ fit).paid.steps≤ installedExteriorRawRoof K₀ := by
  rw [exact_exterior_ingress_bill]
  exact Nat.add_le_add_right (Nat.add_le_add
    (installed_exterior_targets_use_explicit_actual_sizes X pad S buf live K₀ F)
    (installed_exterior_incidence_uses_explicit_actual_sizes X pad S buf ownHead K₀ F)) 4

theorem same_paid_root_operand_has_derived_rawDebit (rank a₀ K₀ : ℕ)
    (fit : Fintype.card (Ext).host.Edge<2^rank)
    (F : ExteriorInputWidths X pad S buf K₀)
    (paid : Meter IngressBytes)
    (literal : paid=(exteriorIngress X pad S buf live ownHead rank a₀ fit).paid) :
    paid.steps≤ installedExteriorRawRoof K₀ :=
  (congrArg Meter.steps literal).trans_le
    (actual_installed_exterior_rawDebit_from_widths X pad S buf live ownHead rank a₀ K₀ fit F)

#print axioms installed_exterior_raw_roof_polynomial
#print axioms installed_exterior_incidence_uses_explicit_actual_sizes
#print axioms installed_exterior_targets_use_explicit_actual_sizes
#print axioms actual_installed_exterior_rawDebit_from_widths
#print axioms same_paid_root_operand_has_derived_rawDebit
end
end J6R94ExteriorDebit
