import J6R50RootIngressRankSyntax
import J6R50RootIngressRankFee

/-! Cumulative fee for the actual categorized ingress, rather than a
fee only for a passed-in Position atlas. Setup that selected the half
ranks is still external, and never charged as zero here. -/
namespace J6R50RootIngress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime J6R49RootIngress J6R30GeneratedRootLayout
open J6OrientedHost J7R10Ports J7R10Plant
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

variable {V : Type} [DecidableEq V] [Fintype V]

def categorizedFee {w r h : ℕ} (c d n vw Flen vars Glen : ℕ)
    (lit eqs : List (BareRankRow w r)) (R : List (RowBook w r h)) (cols : ColBook w) : ℕ :=
  fullIngressFee vw 3 Flen vars+(1+n*signFee r c d h 4 (Flen+vars))+8+
    (tapeFee h Glen+9+lit.length*(9+4*(r+h))+eqs.length*(8+4*r))+
      recoveredFee c d n R cols

theorem compile_categorized_rank_fee (F : CNF V)
    (code : V→List Bool) (inj : Function.Injective code) {w r c d h vw : ℕ}
    (C : LiteralCodec (physicalPlant (guarded F)) r c d)
    (hw : 0<w) (hd : 0<d) (hc : 0<c) (hh : 0<h)
    (rankFit : nWires (guarded F)≤2^w) (clauseFit : (guarded F).length≤2^h)
    (degree : ∀ a∈F,a.length≤3) (wordWidth : ∀ v,(code v).length=vw)
    (lit eqs : List (BareRankRow w r)) (cols : ColBook w)
    (eqOrder : List (TreeIndex (guarded F))) (ex : ∀ j,j∈eqOrder)
    (hl : lit=List.ofFn (fun i : J7R9Compiler.ClauseIndex (guarded F) =>
      bareRankSpec (guarded F) C (.inl i)))
    (he : eqs=eqOrder.map (fun i => bareRankSpec (guarded F) C (.inr i)))
    (exactCol : cols=colSpec (guarded F)) :
    let n := nWires (guarded F)
    let run := compileParsedRoles (c:=c) (d:=d) (h:=h) n
      ((Finset.univ : Finset V).toList.map code) (codeCNF code F) lit eqs cols
    run.steps≤categorizedFee (h:=h) c d n vw F.length (Fintype.card V) (guarded F).length
      lit eqs ((oldOrder (guarded F) eqOrder).map (rowSpec (guarded F) C)) cols := by
  let keys := (Finset.univ : Finset V).toList.map code
  let raw := codeCNF code F
  let G := guardedMeter keys raw
  let Y := G.result
  let R := roleRows (h:=h) Y lit eqs
  let n := nWires (guarded F)
  let A := recoveredAtlas (c:=c) (d:=d) n R.result cols
  let pos := List.ofFn (positionForWire (guarded F) C : Fin n→Position r c d h)
  have gy : Y=codeCNF (guardCode code) (guarded F) := paid_guard_original_syntax code inj F
  have ylen : Y.length=(guarded F).length := by rw [gy,codeCNF,List.length_map]
  have hr : R.result=(oldOrder (guarded F) eqOrder).map (rowSpec (guarded F) C) := by
    change (roleRows (h:=h) Y lit eqs).result=_
    rw [gy]
    exact role_rows_exact (guarded F) C (guardCode code) hh clauseFit eqOrder lit eqs hl he
  have ha : A.result=some pos := recovered_actual_unsigned_atlas (guarded F) C hw rankFit hd hc
    R.result cols (oldOrder (guarded F) eqOrder) (oldOrder_exhaustive (guarded F) eqOrder ex) hr exactCol
  have dfit : ∀ s∈R.result,s.ranks.length≤2^d := by
    rw [hr]
    intro s hs
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hs
    simpa only [rowSpec,List.length_ofFn] using C.portFit v
  have cfit : cols.length≤2^c := by rw [exactCol,colSpec,List.length_ofFn]; exact C.columnFit
  have K : A.steps≤recoveredFee c d n R.result cols :=
    recovered_atlas_fee n R.result cols hw hd hc rankFit dfit cfit
  rw [hr] at K
  have J : R.steps≤tapeFee h Y.length+9+lit.length*(9+4*(r+h))+eqs.length*(8+4*r) :=
    role_row_fee Y lit eqs hh (by rwa [ylen])
  rw [ylen] at J
  have B := paid_full_ingress_fee F code inj vw wordWidth degree pos
  have L : pos.length=n := List.length_ofFn
  rw [L] at B
  change G.steps+(signAtlas Y pos).steps+5≤_ at B
  change (match A.result with
    | none => (⟨none,G.steps+R.steps+A.steps+7⟩ : Meter (Option (List (SignedHalfPort r c d))))
    | some p => ⟨(signAtlas Y p).result,G.steps+R.steps+A.steps+(signAtlas Y p).steps+8⟩).steps ≤ _
  rw [ha]
  dsimp only [categorizedFee]
  dsimp only [n] at B K
  omega

#print axioms compile_categorized_rank_fee
end J6R50RootIngress
