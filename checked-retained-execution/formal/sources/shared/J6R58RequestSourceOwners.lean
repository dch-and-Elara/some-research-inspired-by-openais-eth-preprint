import J6R58RequestSourceNames

/-! Seed the next local ownership table from actual paid retained
owners and the current all-page birth. This step does not require an
`Advance` or its directory, avoiding a circular dependence. -/
namespace J6R58RequestSource
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R50SourceProducer
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R51ParentFrames J6R49SourceLayout J6R48RawRoute J6ActiveRun
open J6R53OldOwner J6R57PublicRequest J6R52CacheSource
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
set_option maxRecDepth 4600
set_option Elab.async false

def writeOriginRow {w gate key prec page : ℕ} (x : RefRow w (OwnerData gate key prec page)) :
    Meter (RefRow w (Word w × Origin key prec page)) :=
  let label := copyFixed x.address
  let data := copyOrigin x.payload.origin
  ⟨⟨label.result,(label.result,data.result)⟩,label.steps+data.steps+5⟩

def ownerOriginView {w gate key prec page : ℕ} (x : RefRow w (OwnerData gate key prec page)) :
    RefRow w (Word w × Origin key prec page) := ⟨x.address,(x.address,x.payload.origin)⟩

theorem actual_origin_row_is_metered {w gate key prec page : ℕ}
    (x : RefRow w (OwnerData gate key prec page)) :
    writeOriginRow x=⟨ownerOriginView x,3*w+1+
      originFee key prec page x.payload.origin.pageKey.isSome+5⟩ := by
  simp only [writeOriginRow,ownerOriginView,copy_fixed_exact,copy_origin_exact]

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page gwidth : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (X : StoredSite T v key prec tw bw page)
variable (gate : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gwidth)))
variable (source : CompleteRoster X.site.oldKey (parentData X gate))
variable (H : ParentOwnerHeaders X.site) (inj : Function.Injective X.site.oldKey)
local notation "ow" => (1+(X.site.ownerWidth+page))
local notation "names" => (nameCurrentOwner X)
local notation "contents" => (childData X gate)
local notation "vertices" => (bornOwnerOrder X H)

def rawCurrentOwners : Meter (Option (RawRoster ow gwidth key prec page)) :=
  let K := actualOwnerNameTape X H
  let R := rekeyPaid (bornOwnerData X gate source H) K.result
  ⟨R.result,K.steps+R.steps+4⟩

include inj in
theorem raw_current_owners_exact :
    let N := actualOwnerNameTape X H
    let R := bornOwnerData X gate source H
    rawCurrentOwners X gate source H=⟨some ((vertices).map fun y=>⟨names y,contents y⟩),
      N.steps+R.steps+(3+(3*ow+6)*(vertices).length)+5+4⟩ := by
  let N := actualOwnerNameTape X H
  let B := bornOwnerData X gate source H
  have values : B.result=some ((vertices).map contents) := by
    have out := born_owner_data_actual X gate source H inj
    exact congrArg Meter.result out
  have nameWords : N.result=(vertices).map names := (actual_child_names_have_no_missing_owner X H).1
  have real := paid_rekey_actual B N.result vertices names contents values nameWords
  change (⟨(rekeyPaid B N.result).result,N.steps+(rekeyPaid B N.result).steps+4⟩ :
    Meter (Option (RawRoster ow gwidth key prec page))) = _
  rw [real]
  dsimp only
  congr 1
  have nfee : (actualOwnerNameTape X H).steps=N.steps := rfl
  have bfee : (bornOwnerData X gate source H).steps=B.steps := rfl
  omega

def openCurrentOwners : Meter (CompleteRoster names contents) :=
  let K := rawCurrentOwners X gate source H
  let exact := raw_current_owners_exact X gate source H inj
  let got := unwrapSuccess K (by
    change (rawCurrentOwners X gate source H).result.isSome
    rw [exact]
    rfl)
  let ord := born_owner_order_full X H
  ⟨⟨vertices,ord.1,ord.2,got.result,
      congrArg Meter.result (unwrap_success_exact _ _ _ (congrArg Meter.result exact))⟩,
    got.steps+3⟩

def buildOriginBank :
    Meter (List (RefRow ow (Word ow × Origin key prec page))) :=
  let before := openCurrentOwners X gate source H inj
  let out := emitRows writeOriginRow before.result.raw
  ⟨out.result,before.steps+out.steps+4⟩

theorem actual_origin_bank_all_owners_and_fee :
    let S := openCurrentOwners X gate source H inj
    let R := buildOriginBank X gate source H inj
    R.result=(vertices).map (fun y=>⟨names y,(names y,X.childOrigins y)⟩) ∧
      R.steps=S.steps+2+(S.result.raw.map (fun x=>(writeOriginRow x).steps+4)).sum+4 := by
  let S := openCurrentOwners X gate source H inj
  have rows := emitted_rows_exact writeOriginRow S.result.raw
  refine ⟨?_, by
    change S.steps+(emitRows writeOriginRow S.result.raw).steps+4=
      S.steps+2+(S.result.raw.map (fun x=>(writeOriginRow x).steps+4)).sum+4
    rw [rows.2]
    omega⟩
  change (emitRows writeOriginRow S.result.raw).result=_
  rw [rows.1,S.result.exactRows,List.map_map]
  simp only [actual_origin_row_is_metered,Function.comp_def,ownerOriginView,childData]
  rfl

#print axioms actual_origin_row_is_metered
#print axioms raw_current_owners_exact
#print axioms openCurrentOwners
#print axioms actual_origin_bank_all_owners_and_fee
end
end J6R58RequestSource
