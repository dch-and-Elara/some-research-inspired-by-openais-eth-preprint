import J6PhysicalAssignment

namespace J6OldEntries
open scoped Classical BigOperators
open J6BlockFactor J6PhysicalAssignment
variable {P G V R : Type*} [Fintype P] [Fintype G] [Fintype V] [CommRing R]
variable {B : P → Type*}

/-- Port owner determines the group of every old tensor port. For a vertex
with repeated or zero ports the definition still uses exactly its incidence
data. -/
def readVertex (owner : P → V) (bucket : V → G) (v : V)
    (x : ∀ i : rows (bucket ∘ owner) (bucket v), B i.val) :
    (i : {p : P // owner p = v}) → B i.val :=
  fun i => x ⟨i.val, congrArg bucket i.property⟩

omit [Fintype P] [Fintype G] [Fintype V] [CommRing R] in
theorem original_reads (owner : P → V) (bucket : V → G) (v : V)
    (x : ∀ i, B i) (i : {p : P // owner p = v}) :
    readVertex owner bucket v (restrictEquiv (bucket ∘ owner) x (bucket v)) i = x i.val := rfl

omit [Fintype P] in
/-- The product of literal old entries equals separate products of the old
vertices in each group, with each old entry evaluated on retained ports. -/
theorem group_old (owner : P → V) (bucket : V → G)
    (entry : ∀ v, ((i : {p : P // owner p = v}) → B i.val) → R)
    (x : ∀ i, B i) :
    (∏ v, entry v (fun i => x i.val)) =
      ∏ g, ∏ v : rows bucket g, entry v.val
        (readVertex owner bucket v.val
          (v.property.symm ▸ (restrictEquiv (bucket ∘ owner) x) g)) := by
  classical
  rw [prod_rows bucket (fun v => entry v (fun i => x i.val))]
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro v _
  rcases v with ⟨v, hv⟩
  change bucket v = g at hv
  subst g
  rfl

#print axioms original_reads
#print axioms group_old
end J6OldEntries
