import J6R112MeasuredRootLayoutStockChart
import J6R53OldOwnerRootBasis

/-! Reverse the already held owner scope into physical half-addresses.
The edge suffix is read from the actual physical suffix emitter. The
owner name is copied from its already paid roster word, not computed
from the possibly opaque naming map. -/
namespace J6R112MeasuredRootLayoutStock
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R36ChildFramedRoute J6R27OriginalGate
open J6OrientedHost J6Mesh J6R10Repack J6R11Repack J6R21Leaf
open J6R14LayoutCost J6R24LegalLayout J6R28GeneratedRootFrame
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R53OldOwnerRoot J6R53TerminalGate J6R54ExteriorOwner
open J6R94ExteriorDebit

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 5200000
set_option maxRecDepth 4400
set_option Elab.async false
noncomputable section

abbrev HalfBook (m own : ℕ) := List (RefRow (rootHalfWidth m) (Word own))

def signedPhysicalWord (m : ℕ) (side : Bool) (suffix : Word (SuffixWordWidth m)) :
    Word (rootHalfWidth m) :=
  ⟨side::suffix.bits,by simp only [List.length_cons,suffix.size,rootHalfWidth,SuffixWordWidth,Nat.add_comm]⟩

def writeHalfName (m : ℕ) {own : ℕ}
    (side : Bool) (name : Word own) (suffix : Word (SuffixWordWidth m)) :
    Meter (RefRow (rootHalfWidth m) (Word own)) :=
  let key := copyFixed suffix
  let data := copyFixed name
  ⟨⟨signedPhysicalWord m side key.result,data.result⟩,key.steps+data.steps+4⟩

theorem half_name_keeps_actual_paid_bits (m : ℕ) {own : ℕ}
    (side : Bool) (name : Word own) (suffix : Word (SuffixWordWidth m)) :
    writeHalfName m side name suffix=
      ⟨⟨signedPhysicalWord m side suffix,name⟩,(3*SuffixWordWidth m+1)+(3*own+1)+4⟩ := by
  unfold writeHalfName
  simp only [copy_fixed_exact]

def writeAllHalfNames (m : ℕ) {own : ℕ} (side : Bool) (name : Word own) :
    List (Word (SuffixWordWidth m))→Meter (HalfBook m own)
  | []=>⟨[],3⟩
  | suffix::tail=>
    let here := writeHalfName m side name suffix
    let rest := writeAllHalfNames m side name tail
    ⟨here.result::rest.result,here.steps+rest.steps+4⟩

theorem all_half_names_keep_the_same_bytes (m : ℕ) {own : ℕ} (side : Bool) (name : Word own)
    (suffixes : List (Word (SuffixWordWidth m))) :
    (writeAllHalfNames m side name suffixes).result=
      suffixes.map (fun s=>⟨signedPhysicalWord m side s,name⟩) := by
  induction suffixes with
  | nil=>rfl
  | cons s ss ih=>simp only [writeAllHalfNames,half_name_keeps_actual_paid_bits,ih,List.map_cons]

def resolveOwnerHalves (m : ℕ) {own : ℕ} (bank : SuffixBank m)
    (side : Bool) (name : Word own) (scope : List (Word (SuffixKeyWidth m))) :
    Meter (Option (HalfBook m own)) :=
  let out := readScope bank scope
  match out.result with
  | none=>⟨none,out.steps+4⟩
  | some xs=>
    let stamped := writeAllHalfNames m side name xs
    ⟨some stamped.result,out.steps+stamped.steps+5⟩

variable {V : Type} [Fintype V] {m n r c d : ℕ}
variable (P : Plant V m n)
local notation "U" => (SourceVertex P)
local notation "W" => (constantRootWord m)

def scopedHalfNames {own : ℕ} (name : Word own) (u : U) : HalfBook m own :=
  List.ofFn (fun i : Fin (rootLocalGate P u).degree=>
    ⟨(expectedHalfRow P (oddAxis m) ((rootLocalGate P u).port i).val).address,name⟩)

theorem suffix_with_actual_side_is_the_original_half_key (u : U) (p : PlantPorts P W u) :
    signedPhysicalWord m (ownerSide P u) (rootOperand P u p)=
      (expectedHalfRow P (oddAxis m) p.val).address := by
  apply word_bits_inj
  change ownerSide P u::(rootWireSuffix P (edge p.val)).bits=
    side p.val::(rootWireSuffix P (edge p.val)).bits
  rw [every_local_port_has_its_actual_side P u p]

theorem resolve_actual_scope_recovers_each_original_half
    {own rank key prec page : ℕ} (literal : LiteralPortFile P r c d)
    (axis : List Bool) (clock : axis.length=(oddAxis m).val)
    (name : U→Word own) (origin : U→Origin key prec page)
    (choice : U→HeadChoice rank) (u : U) :
    let plan := rootPlanWord P name origin choice u
    let bank := (paidRootSuffixBank m axis literal.raw).result
    (resolveOwnerHalves m bank (ownerSide P u) plan.addr plan.scopes).result=
      some (scopedHalfNames P (name u) u) := by
  let G := rootLocalGate P u
  let scopes := fun i : Fin G.degree=>stableWireKeyWord m (edge (G.port i).val)
  let suffixes := fun i : Fin G.degree=>rootOperand P u (G.port i)
  let bank := (paidRootSuffixBank m axis literal.raw).result
  let I := List.ofFn (fun i : Fin G.degree=>i)
  have hit (i : Fin G.degree) (_ : i∈I) :
      (locate (scopes i) bank).result=some (suffixes i) :=
    actual_suffix_bank_covers_original_wire literal axis clock _
  have read := congrArg Meter.result (read_scope_exact bank scopes suffixes I hit)
  simp only [I,List.map_ofFn,Function.comp_def] at read
  change (resolveOwnerHalves m bank (ownerSide P u) (name u) (List.ofFn scopes)).result=_
  unfold resolveOwnerHalves
  dsimp only
  rw [read]
  dsimp only
  rw [all_half_names_keep_the_same_bytes]
  simp only [scopedHalfNames,List.map_ofFn,Function.comp_def]
  apply congrArg some
  apply congrArg List.ofFn
  funext i
  exact congrArg (fun a=>RefRow.mk a (name u)) (suffix_with_actual_side_is_the_original_half_key P u (G.port i))

#print axioms half_name_keeps_actual_paid_bits
#print axioms all_half_names_keep_the_same_bytes
#print axioms suffix_with_actual_side_is_the_original_half_key
#print axioms resolve_actual_scope_recovers_each_original_half
end
end J6R112MeasuredRootLayoutStock

