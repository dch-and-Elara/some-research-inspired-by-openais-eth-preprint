import J6R50LeafSource

/-! A fee bound for the actual owner-row compiler derived from serialized
input. Unlike taking a bound on buildOwner as a premise, this prices its
failed scan prefix and the concrete original/retained syntax. -/
namespace J6R57LeafCap
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Leaf J6R21Ancestor
open J6R34ChildPath J6R36ChildFramedRoute J6R33StatefulArithmeticPage
open J6R25PreparedSupply J6R26DescriptorTree J6R20Ancestor J6R27OriginalGate J6OrientedHost
open J6R48Leaf J6R50Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000

def storedWirePrepFee (w : ℕ) (r : WireRead) : ℕ :=
  sourceWireFee w r.lane.length r.header.length

def rowSyntaxBuildFee {N own w key prec page : ℕ} (b : ℕ)
    (lines : List (ResidentPort own w)) (table : OriginTable own w key prec page)
    (owner : Word own) (cmd : PageReadCode N key page) : ℕ :=
  locateFee own table.length+9+
    match cmd with
    | .original _ tape => currentGateFee w b N (originalDegree tape)
    | .generated _ _ ticks wires => pageBuildFee owner lines key prec page ticks
        (wires.map (storedWirePrepFee w)).sum

private theorem orig_body_from_literal_tape {N own w key prec page d b : ℕ}
    (hb : 0<b) (keys : List (Word w)) (keyAt : Fin N→Word w)
    (inj : Function.Injective keyAt) (real : keys=List.ofFn keyAt)
    (owner : Word own) (lines : List (ResidentPort own w))
    (slot : Fin d→Fin N) (gate : Gate d) (fit : N≤2^b) :
    (buildBody (key:=key) (prec:=prec) (page:=page) N b keys owner lines
      (.old (encodeGate (keyAt∘slot) gate))).steps≤
      currentGateFee w b N (originalDegree (gateTape fit slot gate))+5 := by
  cases gate with
  | free => simp [buildBody,encodeGate,compileCurrentGate,currentGateFee,gateTape,originalDegree]
  | equal =>
    simpa only [gateTape,originalDegree,List.length_map,List.length_ofFn] using
      (paid_original_body (key:=key) (prec:=prec) (page:=page)
        keys keyAt inj real owner lines slot Gate.equal hb fit).2
  | clause signs =>
    simpa only [gateTape,originalDegree,List.length_map,List.length_ofFn] using
      (paid_original_body (key:=key) (prec:=prec) (page:=page)
        keys keyAt inj real owner lines slot (.clause signs) hb fit).2

theorem actual_owner_prep_has_literal_size_fee {N own w key prec page b : ℕ}
    (hb : 0<b) (keys : List (Word w)) (keyAt : Fin N→Word w)
    (inj : Function.Injective keyAt) (real : keys=List.ofFn keyAt)
    (lines : List (ResidentPort own w)) (table : OriginTable own w key prec page)
    (owner : Word own) {cmd : PageReadCode N key page}
    (checked : SourceCommand b keyAt lines table owner cmd) :
    (buildOwner N b keys lines table owner).steps≤rowSyntaxBuildFee b lines table owner cmd := by
  cases checked with
  | old slot gate fit listed =>
    have scan := (bought_owner_record N b keys lines table owner _
      listed.appears listed.same).2
    have prep := orig_body_from_literal_tape (key:=key) (prec:=prec) (page:=page)
      hb keys keyAt inj real owner lines slot gate fit
    unfold rowSyntaxBuildFee
    dsimp only at scan ⊢
    omega
  | paged site born pg ports headers slot tag listed actual =>
    have scan := (bought_owner_record N b keys lines table owner _
      listed.appears listed.same).2
    have prep := (paid_page_body (b:=b) keys keyAt inj real owner lines site born pg tag
      ports headers slot actual).2
    have wireEq : ((ports.map (fun u=>(⟨headers u,List.replicate (slot u).val true⟩ : WireRead))).map
        (storedWirePrepFee w)).sum=
        (ports.map (fun u=>sourceWireFee w (slot u).val (headers u).length)).sum := by
      simp only [List.map_map,Function.comp_def,storedWirePrepFee,List.length_replicate]
    unfold rowSyntaxBuildFee
    dsimp only at scan prep ⊢
    rw [wireEq]
    omega

#print axioms rowSyntaxBuildFee
#print axioms actual_owner_prep_has_literal_size_fee
end J6R57LeafCap
