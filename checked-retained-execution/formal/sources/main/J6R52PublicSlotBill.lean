import J6R52PublicSlotQuery

/-! Payment for each of the 64 actual group executions is present in
the literal folded product, not merely an upper bound by their cost. -/
namespace J6R52PublicSlot
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R33OriginalJ6 J6R34OfficialGateway
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2850
set_option maxHeartbeats 15500000
set_option linter.unusedSectionVars false
set_option Elab.async false

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native ell key prec tw bw page speed : ℕ}
variable {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)) (hf : f.Monic)
variable (F : Frame f (J6SourcePrecision.printed m base)) (hv : 0<ell)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (R : GroupPrograms G hf ell key prec tw bw page speed)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1))

theorem all_online_group_bills_are_paid :
    (∑ g : Fin 64,(groupRun G hf i j g (R i j g)).steps) ≤ (slotBody G hf F hv R i j).steps := by
  let E := SiteFrame G ell F i
  let read := fun g=>groupOnSite G hf F i j g (receiptsAt G hf F R i j g)
  have count : bill read (groupOrder 64)≤(slotBody G hf F hv R i j).steps :=
    (prodM_steps E.hp E.sizePos hv read (groupOrder 64)).1
  refine le_trans ?_ count
  unfold bill groupOrder
  rw [List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply]
  apply Finset.sum_le_sum
  intro g _
  change (groupRun G hf i j g (R i j g)).steps≤
    (groupRun G hf i j g (R i j g)).steps+_+4
  exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

#print axioms all_online_group_bills_are_paid
end J6R52PublicSlot
