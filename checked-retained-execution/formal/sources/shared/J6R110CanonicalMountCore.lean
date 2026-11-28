import J6R109CanonicalProbeTableBits

/-! An R109 paid binary counter produces the actual bytes. For the
unchanged R58 consumer, ordered field-word equality is required; injectivity
alone does not imply this. The R58 installation copies these rows once. -/
namespace J6R110CanonicalMount
open AOracleMachineTime J6R58ActivePrep J6R109CanonicalProbeTable J6R33OriginalJ6

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 5000000

/-- This is equality of coefficient masks in the order actually read.
It is not inferred from distinctness of the two point sets. -/
def SameOrder (e d : ℕ) (fit : d+1≤2^e) : Prop :=
  ∀ j : Fin (d+1), zeroPrefix e d j=NativeProbeRing.chosenRep e (d+1) fit j

noncomputable def OldOrderedBytes (e d : ℕ) (fit : d+1≤2^e) : List (List Bool) :=
  List.ofFn (fun j : Fin (d+1)=>List.ofFn (NativeProbeRing.chosenRep e (d+1) fit j))

theorem actual_canonical_bytes_of_same_order (e d : ℕ) (he : 0<e) (fit : d+1≤2^e)
    (same : SameOrder e d fit) : (canonicalTable e (d+1)).result=OldOrderedBytes e d fit := by
  rw [(actual_canonical_table_is_paid_binary_prefix e d he fit).1]
  unfold OldOrderedBytes
  apply congrArg List.ofFn
  funext j
  rw [same j]

/-- Real generation and one real physical table install. The `bytes` proof
only certifies the already produced raw table, not an additional copy. -/
def mountCanonicalTable (e d : ℕ) (fit : d+1≤2^e)
    (bytes : (canonicalTable e (d+1)).result=OldOrderedBytes e d fit) :
    Meter (MaskTable e (d+1) fit) :=
  let generated := canonicalTable e (d+1)
  let certified : MaskTable e (d+1) fit := ⟨generated.result,bytes⟩
  let mounted := certified.install
  ⟨mounted.result,generated.steps+mounted.steps+4⟩

theorem actual_mount_is_one_counter_and_one_copy (e d : ℕ) (he : 0<e) (fit : d+1≤2^e)
    (bytes : (canonicalTable e (d+1)).result=OldOrderedBytes e d fit) :
    let mounted := mountCanonicalTable e d fit bytes
    mounted.result.raw=(canonicalTable e (d+1)).result ∧
      mounted.steps=canonicalTableFee e (d+1)+(2+(d+1)*(3*e+5))+4 := by
  let generated := canonicalTable e (d+1)
  let src : MaskTable e (d+1) fit := ⟨generated.result,bytes⟩
  change src.install.result.raw=generated.result ∧
    generated.steps+src.install.steps+4=canonicalTableFee e (d+1)+(2+(d+1)*(3*e+5))+4
  rw [MaskTable.installed_exact,show generated.steps=canonicalTableFee e (d+1) from
    (actual_canonical_table_is_paid_binary_prefix e d he fit).2]
  exact ⟨rfl,rfl⟩

/-- Every later raw scan reads the mounted table. The paid row scan
is exactly the existing R58 protocol, with no call to the counter. -/
theorem canonical_mount_serves_actual_prefix_scans (e d : ℕ) (fit : d+1≤2^e)
    (bytes : (canonicalTable e (d+1)).result=OldOrderedBytes e d fit)
    {n : ℕ} (small : n≤2^e) (nested : n≤d+1) (j : Fin n) :
    (mountCanonicalTable e d fit bytes).result.readRaw nested j=
      ⟨List.ofFn (NativeProbeRing.chosenRep e n small j),(j.val+1)*(3*e+5)⟩ :=
  MaskTable.read_raw_exact _ nested j

#print axioms actual_canonical_bytes_of_same_order
#print axioms actual_mount_is_one_counter_and_one_copy
#print axioms canonical_mount_serves_actual_prefix_scans
end J6R110CanonicalMount