import J6R54PublicFamilyCount
import J6R54PublicFamilyFresh
import J6R53PublicMountFreshReadout

/-! On exactly the submitted guarded-CNF chart the returned unsigned
word is the submitted model count. The separately stated exact fee
delta of runPreparedCount still includes its one real source/field
preflight and every genuine address in the original readout. -/
namespace J6R54PublicFamily
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R22RootReadout
open J6R51Ingress J6R52FreshShape J7R9Compiler J7R9Subdivision J7R10Plant
open J6R53PublicMount J6R49RootIngress J6R50RootIngress
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3300
set_option maxHeartbeats 13500000
set_option linter.unusedSectionVars false
set_option Elab.async false
attribute [local irreducible] J6R51Ingress.freshPlant J6R51Ingress.guardedInOrder
attribute [local irreducible] runMountedCount runPreparedCount

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable (F : CNF V) (order : DeclaredOrder V)
variable {f : ℤ[X]} {base native ell q rr cc dd edgew tc tj prec tw bw rate pad kp : ℕ}
variable (G : RootShape f (nWires (guardedInOrder F order.roster))
  (printedHalf (nWires (guardedInOrder F order.roster))) base native
  (printedRankWidth (nWires (guardedInOrder F order.roster)))
  (freshPlant (guardedInOrder F order.roster) (guardRoster order))
  (constantRootWord (nWires (guardedInOrder F order.roster))))
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (I : SharedInputs G ell q rr cc dd prec kp bw)
variable (W : Widths (nWires (guardedInOrder F order.roster)) native tc tj tw edgew)
variable (jobs : PublicJobs W (prepareShared I).result rate pad)

theorem actual_prepared_fresh_CNF_word (basePos : 0<base) :
    bitsValue (runPreparedCount W I jobs).result.val=PinnedCNF.modelCount F := by
  let S := prepareShared I
  let P := plainFamily W S.result jobs
  have word := (prepared_count_same_word_and_exact_full_bill W I jobs).1
  have exactOld := fresh_mounted_public_count_word F order G S.result.hf S.result.frame S.result.positive P basePos
  exact (congrArg (fun w : A1R10.Word (printedAnswerWidth (nWires (guardedInOrder F order.roster)) base)=>
    bitsValue w.val) word).trans exactOld

end

noncomputable section ExplicitRaw
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable (F : CNF V) (order : DeclaredOrder V)
variable {h d j r c e base ell q prec kp bw tc tj tw edgew rate pad : ℕ}
variable (basePos : 0<base) (positive : 0<ell) (three : ∀ row∈F,row.length≤3)
variable (large : printedGuard (nWires (guardedInOrder F order.roster)) (Paper6SourceSize.sourceNativeSize F order))
variable (size : Widths (nWires (guardedInOrder F order.roster)) (Paper6SourceSize.sourceNativeSize F order)
  tc tj tw edgew)
variable (W : FreshWords (nWires (guardedInOrder F order.roster)) base q prec kp bw)
variable (guards : SerialGuards F order h d j r c e)
variable (code : V→List Bool) (inj : Function.Injective code)
variable (declared : List (List Bool)) (body : BitsCNF)
variable (declaredExact : declared=order.roster.map code) (bodyExact : body=codeCNF code F)

include basePos in
theorem actual_raw_shared_CNF_count
    (jobs :
      letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
        ⟨(generated_fresh_field_is_permitted F order).2⟩
      PublicJobs size (prepareShared (freshSharedInputs F order base ell q prec kp bw three large positive W
        guards code inj declared body declaredExact bodyExact)).result rate pad) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let I := freshSharedInputs F order base ell q prec kp bw three large positive W
      guards code inj declared body declaredExact bodyExact
    bitsValue (runPreparedCount size I jobs).result.val=PinnedCNF.modelCount F := by
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  exact actual_prepared_fresh_CNF_word F order (freshSearchedRootShape F order base three large) _ size jobs basePos

#print axioms actual_prepared_fresh_CNF_word
#print axioms actual_raw_shared_CNF_count
end ExplicitRaw
end J6R54PublicFamily

