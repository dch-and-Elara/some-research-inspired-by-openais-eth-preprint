import J9R13Compiler
import J8J9GroupedCube

/-!
# The actual seated column truth tables on the global wire cube

Every real pin and every old column clause uses its physical index.
The identity uses the existing physical owner/cube bijection, not
a hypothesis that a newly supplied table equals the child truth.
-/

namespace J9R13PhysicalTables
open scoped Classical BigOperators
open J8Physical J8J9Grouped LiteralPortCompiler J9R13Compiler

noncomputable section

theorem truth_flatMap {I T K : Type*} [CommRing K] (xs : List T)
    (F : T→CNF I) (x : I→Bool) :
    (truth (xs.flatMap F) x : K) = (xs.map (fun i => (truth (F i) x : K))).prod := by
  induction xs with
  | nil => simp [truth,satisfied,indicator]
  | cons a xs ih =>
    rw [List.flatMap_cons,List.map_cons,List.prod_cons,truth_append,ih]

variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G]
variable [∀ v, Fintype (P v)]

def localCNF (idx : Wire R ≃ Fin M) (F : OldTables d) (sign : S→Bool) (g : G) : CNF (Fin M) :=
  ((Finset.univ : Finset (LocalPin d g)).toList.flatMap
    (fun i => pin (idx (pinWire d i.1)) (sign i.1))) ++
  ((Finset.univ : Finset (LocalColumn d g)).toList.flatMap
    (fun v => relabel (fun q : P v.1 => idx (ordinaryWire d ⟨v.1,q⟩)) (F g v)))

def globalCNF (idx : Wire R ≃ Fin M) (F : OldTables d) (sign : S→Bool) : CNF (Fin M) :=
  (Finset.univ : Finset G).toList.flatMap (localCNF d idx F sign)

omit [Fintype R] [Fintype S] [Fintype V] [Fintype G] [(v : V) → Fintype (P v)] in
theorem indexed_pin (idx : Wire R ≃ Fin M) (x : Cube d) (g : G) (p : LocalPin d g) :
    cubeEquiv d idx x (idx (pinWire d p.1)) = (x g).1 p := by
  have h := congrArg (fun y : Assignment d g => y.1 p) (cubeLabels_local d x g)
  change cubeLabels d x (idx.symm (idx (pinWire d p.1))) = _
  rw [Equiv.symm_apply_apply]
  exact h

omit [Fintype R] [Fintype S] [Fintype V] [Fintype G] [(v : V) → Fintype (P v)] in
theorem indexed_old (idx : Wire R ≃ Fin M) (x : Cube d) (g : G) (v : LocalColumn d g) :
    (cubeEquiv d idx x) ∘ (fun q : P v.1 => idx (ordinaryWire d ⟨v.1,q⟩)) = (x g).2 v := by
  funext q
  have h := congrArg (fun y : Assignment d g => y.2 v q) (cubeLabels_local d x g)
  change cubeLabels d x (idx.symm (idx (ordinaryWire d ⟨v.1,q⟩))) = _
  rw [Equiv.symm_apply_apply]
  exact h

omit [Fintype R] [Fintype G] [(v : V) → Fintype (P v)] in
theorem local_truth {K : Type*} [CommRing K] (idx : Wire R ≃ Fin M)
    (F : OldTables d) (sign : S→Bool) (x : Cube d) (g : G) :
    (truth (localCNF d idx F sign g) (cubeEquiv d idx x) : K) =
      (∏ p : LocalPin d g, truth (pin p (sign p.1)) (x g).1) *
        ∏ v : LocalColumn d g, truth (F g v) ((x g).2 v) := by
  rw [localCNF,truth_append,truth_flatMap,truth_flatMap,
    Finset.prod_map_toList,Finset.prod_map_toList]
  congr 1
  · apply Finset.prod_congr rfl
    intro p _
    rw [truth_pin,truth_pin,indexed_pin d idx x g p]
  · apply Finset.prod_congr rfl
    intro v _
    rw [truth_relabel,indexed_old d idx x g v]

omit [Fintype R] [(v : V) → Fintype (P v)] in
theorem global_truth {K : Type*} [CommRing K] (idx : Wire R ≃ Fin M)
    (F : OldTables d) (sign : S→Bool) (x : Cube d) :
    (truth (globalCNF d idx F sign) (cubeEquiv d idx x) : K) =
      ∏ g : G, (∏ p : LocalPin d g, truth (pin p (sign p.1)) (x g).1) *
        ∏ v : LocalColumn d g, truth (F g v) ((x g).2 v) := by
  rw [globalCNF,truth_flatMap,Finset.prod_map_toList]
  exact Finset.prod_congr rfl (fun g _ => local_truth d idx F sign x g)

#print axioms truth_flatMap
#print axioms indexed_pin
#print axioms indexed_old
#print axioms global_truth

end
end J9R13PhysicalTables
