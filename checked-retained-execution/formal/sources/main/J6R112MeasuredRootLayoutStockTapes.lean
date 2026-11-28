import J6R112MeasuredRootLayoutStockRole
import J6R112MeasuredRootLayoutStockOrder

/-! Read the actual ordered owner descriptors and physical scope words in
lockstep. The original address is obtained from the paid complete roster,
not by evaluating its logical name function; the value of the old Gate is
untouched. Padding roles are read from the true scoped key, not supplied. -/
namespace J6R112MeasuredRootLayoutStock
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R36ChildFramedRoute J6R27OriginalGate
open J6OrientedHost J6Mesh J6R10Repack J6R11Repack J6R21Leaf
open J6R24LegalLayout J6R28GeneratedRootFrame
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R53OldOwnerRoot J6R53TerminalGate J6R54ExteriorOwner
open J6R94ExteriorDebit

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 5500000
set_option maxRecDepth 4500
set_option Elab.async false
noncomputable section

def appendHalfBook {A : Type*} : List A→List A→Meter (List A)
  | [],r=>⟨r,2⟩
  | x::xs,r=>
    let tail := appendHalfBook xs r
    ⟨x::tail.result,tail.steps+4⟩

theorem append_half_book_exact {A : Type*} (a b : List A) :
    appendHalfBook a b=⟨a++b,2+4*a.length⟩ := by
  induction a with
  | nil=>rfl
  | cons top tail ih=>
    simp only [appendHalfBook,List.cons_append,List.length_cons,ih,Nat.mul_succ,Nat.add_assoc]

abbrev UnsortedTapes (m own : ℕ) := List (Word own×BootRole) × HalfBook m own

variable {V : Type} [Fintype V] {m n : ℕ} (P : Plant V m n)
local notation "U" => (SourceVertex P)

def compileActualOwnerTapes {D : Type*} {own rank key prec page : ℕ} (bank : SuffixBank m) :
    List U→List (RefRow own D)→List (OwnerPlan own rank (SuffixKeyWidth m) key prec page)→
      Meter (Option (UnsortedTapes m own))
  | [],[],[]=>⟨some ([],[]),3⟩
  | u::us,row::rs,pl::pls=>
    let k := copyFixed row.address
    let role := roleFromActualScopes P u pl.scopes
    let sides := resolveOwnerHalves m bank (ownerSide P u) row.address pl.scopes
    match sides.result with
    | none=>⟨none,k.steps+role.steps+sides.steps+4⟩
    | some named=>
      let rest := compileActualOwnerTapes bank us rs pls
      match rest.result with
      | none=>⟨none,k.steps+role.steps+sides.steps+rest.steps+7⟩
      | some tail=>
        let glued := appendHalfBook named tail.2
        ⟨some ((k.result,role.result)::tail.1,glued.result),
          k.steps+role.steps+sides.steps+rest.steps+glued.steps+9⟩
  | _,_,_=>⟨none,4⟩

theorem actual_order_and_scopes_emit_both_original_tapes
    {D : Type*} {r c d own rank key prec page : ℕ}
    (literal : LiteralPortFile P r c d) (axis : List Bool) (clock : axis.length=(oddAxis m).val)
    (bank : SuffixBank m) (physicalBank : bank=(paidRootSuffixBank m axis literal.raw).result)
    (name : U→Word own) (payload : U→D) (origin : U→Origin key prec page)
    (choice : U→HeadChoice rank) (order : List U) :
    (compileActualOwnerTapes P bank order (order.map (fun u=>⟨name u,payload u⟩))
      (order.map (rootPlanWord P name origin choice))).result=
      some (order.map (fun u=>(name u,trueRootRole u)),candidateNames P name order) := by
  induction order with
  | nil=>rfl
  | cons u us ih=>
    have h := resolve_actual_scope_recovers_each_original_half P literal axis clock name origin choice u
    have got : (resolveOwnerHalves m bank (ownerSide P u) (name u)
      (rootPlanWord P name origin choice u).scopes).result=some (scopedHalfNames P (name u) u) := by
      rw [physicalBank]
      exact h
    have role := the_original_scope_plan_produces_true_role P name origin choice u
    simp only [List.map_cons,compileActualOwnerTapes,copy_fixed_exact,got,role,ih,
      append_half_book_exact,candidateNames,List.flatMap_cons]

#print axioms append_half_book_exact
#print axioms compileActualOwnerTapes
#print axioms actual_order_and_scopes_emit_both_original_tapes
end
end J6R112MeasuredRootLayoutStock

