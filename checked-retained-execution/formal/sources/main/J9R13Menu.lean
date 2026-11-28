import J9R13PhysicalFusion

/-!
# Observation of a singleton in an arbitrary full mode menu

Restriction to the selected unit menu is a theorem for the entire
literal compiler, not the assumption that other native modes were
removed from the input.
-/

namespace J9R13Menu
open scoped Polynomial Classical BigOperators
open LiteralPortCompiler J9LayoutTransfer NativeProbeRing DyadicProbeCompiler
open J8Physical J8EndToEnd J8J9Grouped J9R13PhysicalFusion

noncomputable section
variable {A K H : Type*} [Fintype A] [DecidableEq A] [Fintype H] [DecidableEq H] [CommRing K]

theorem select_singleton (F : CNF A) (u : (A→Bool)→A→K) (v : (A→Bool)→A→H→K) (m : H) :
    MvPolynomial.coeff (Finsupp.single m 1) (completed F u v) =
      MvPolynomial.coeff β (completed F u (fun a p (_ : Unit) => v a p m)) := by
  rw [β,singleton_coeff,singleton_coeff]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.prod_congr rfl
  intro q _
  by_cases h : q=p <;> simp [portTerm,atPort,h]

omit [CommRing K] in
theorem select_observation (q : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree→Bool) (F : CNF A)
    (u : (A→Bool)→A→Source[X]) (v : (A→Bool)→A→H→Source[X]) (w : H→ℕ) (m : H) :
    J9End.observation q f addr F u v w m =
      J9End.observation q f addr F u (fun a p (_ : Unit) => v a p m) (fun _ => w m) () := by
  unfold J9End.observation
  exact select_singleton _ _ _ _

-- Match the equality choice of the physical compiler on its left cube.
local instance (priority := 10000) literalFinDecEq (n : ℕ) : DecidableEq (Fin n) :=
  fun i j => Classical.propDecidable (i=j)

variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

omit [Fintype A] [DecidableEq A] [CommRing K] in
/-- Other complete-menu entries can be arbitrary and may overlap the
same physical row legs. The selected native column remains fixed. -/
theorem observation_with_other_modes (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
    (a : S) (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a)
    (idx : Wire R ≃ Fin M) (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a→Source[X])
    (m : H) (other : (Site M R→Bool)→Site M R→H→Source[X])
    (v : H→ℕ) (k q : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree→Bool) :
    J9End.observation q f addr (literalSystem d idx F sign)
      (literalBase d e even a idx tail b)
      (fun bits p j => if j=m then literalKernel d (M:=M) even hL a b kt bits p () else other bits p j)
      (fun j => if j=m then k+1+(b:ℕ) else v j) m =
      highObservation d e even hL a F sign tail b kt k q f addr := by
  rw [select_observation]
  simp only [if_true]
  change J9End.observation q f addr (literalSystem d idx F sign)
    (literalBase d e even a idx tail b) (literalKernel d (M:=M) even hL a b kt)
    (fun _ => k+1+(b:ℕ)) () = _
  exact observation_is_physical_child_product d e even hL a off idx F sign tail b kt k q f addr

#print axioms select_singleton
#print axioms select_observation
#print axioms observation_with_other_modes

end
end J9R13Menu
