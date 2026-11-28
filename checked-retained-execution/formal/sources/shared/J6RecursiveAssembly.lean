import J6RecursiveModes
import Mathlib.Tactic

/-! Source child contraction over literal retained tables and packet rows.
The Boolean cube is partitioned by the *actual* owners of each port.
The only incidence hypothesis is that each retained table uses ports
in its owner's group; shifted matched ports are likewise local. -/
namespace J6RecursiveAssembly
open scoped BigOperators
open LiteralPortCompiler J6RecursiveModes
variable {R G K V P : Type*} [CommRing R] [Fintype G] [DecidableEq G]
  [Fintype K] [DecidableEq K] [Fintype P] [DecidableEq P] [Fintype V]

abbrev GroupCube (group : Sum P P → G) (g : G) :=
  ({p : Sum P P // group p=g} → Bool)

def restrict (group : Sum P P → G) (g : G) (x : Sum P P → Bool) :
    GroupCube group g := fun p => x p.val

def extend (group : Sum P P → G) (g : G) (z : GroupCube group g)
    (p : Sum P P) : Bool := if h : group p=g then z ⟨p,h⟩ else false

def assignmentIso (group : Sum P P → G) :
    (∀ g, GroupCube group g) ≃ (Sum P P → Bool) where
  toFun z p := z (group p) ⟨p,rfl⟩
  invFun z g := restrict group g z
  left_inv z := by
    funext g p
    obtain ⟨x,h⟩ := p
    subst g
    rfl
  right_inv _ := rfl

omit [Fintype G] [Fintype P] [DecidableEq P] in
theorem extend_restrict_hit (group : Sum P P → G) (g : G) (x : Sum P P → Bool)
    (p : Sum P P) (hp : group p=g) :
    extend group g (restrict group g x) p = x p := by
  simp [extend,restrict,hp]

def read (shift : P → Option P) (x : Sum P P → Bool) (p : P) : Bool :=
  ((shift p).map fun q => x (.inr q)).getD false

def value (c : R) (x : Bool) : R := if x then c else 0

def addresses (group : Sum P P → G) (seat : P → K) (g : G) (k : K) : Finset P :=
  (Finset.univ.filter (fun p => group (.inl p)=g)).filter (fun p => seat p=k)

noncomputable def retained (group : Sum P P → G) (scope : V → Type*)
    (port : ∀ v, scope v → Sum P P) (owner : V → G)
    (table : ∀ v, (scope v → Bool) → R) (g : G) (y : GroupCube group g) : R :=
  ∏ v ∈ (Finset.univ.filter (fun v => owner v=g)), table v (fun j => extend group g y (port v j))

noncomputable def wholeContraction (scope : V → Type*)
    (port : ∀ v, scope v → Sum P P) (table : ∀ v, (scope v → Bool) → R)
    (shift : P → Option P) (c : R) : R :=
  ∑ x : Sum P P → Bool, (∏ v, table v (fun j => x (port v j))) *
    ∏ p, affine (x (.inl p)) (value c (read shift x p))

omit [Fintype G] [Fintype P] [DecidableEq P] in
theorem local_read (group : Sum P P → G) (shift : P → Option P)
    (hL : ∀ p q, shift p = some q → group (.inl p)=group (.inr q))
    (g : G) (x : Sum P P → Bool) (p : P) (hp : group (.inl p)=g) :
    read shift (extend group g (restrict group g x)) p = read shift x p := by
  cases h : shift p with
  | none => simp [read,h]
  | some q =>
    have hh := (hL p q h).symm.trans hp
    simp [read,h,extend_restrict_hit group g x (.inr q) hh]

/-- Printed zero-mode child folding for actual grouped retained scopes,
packet fibers, and a partial shift. It is a contraction identity, not a
claim that a specific recursive evaluator implements it. -/
theorem physical_child_assembly (group : Sum P P → G) (seat : P → K)
    (scope : V → Type*) (port : ∀ v, scope v → Sum P P) (owner : V → G)
    (table : ∀ v, (scope v → Bool) → R) (shift : P → Option P) (c : R)
    (hOwner : ∀ v j, group (port v j)=owner v)
    (hLocal : ∀ p q, shift p=some q → group (.inl p)=group (.inr q)) :
    (∏ g, ∑ x : GroupCube group g, retained group scope port owner table g x *
      ∏ k, ∏ p ∈ addresses group seat g k,
        affine (extend group g x (.inl p)) (value c (read shift (extend group g x) p))) =
    wholeContraction scope port table shift c := by
  classical
  rw [Fintype.prod_sum,wholeContraction]
  apply Fintype.sum_equiv (assignmentIso group)
  intro y
  let x := assignmentIso group y
  have hx (g : G) : y g = restrict group g x :=
    congrFun ((assignmentIso group).left_inv y).symm g
  change (∏ g, retained group scope port owner table g (y g) *
      ∏ k, ∏ p ∈ addresses group seat g k,
        affine (extend group g (y g) (.inl p)) (value c (read shift (extend group g (y g)) p))) =
    (∏ v, table v (fun j => x (port v j))) * ∏ p, affine (x (.inl p)) (value c (read shift x p))
  simp only [hx,Finset.prod_mul_distrib]
  congr 1
  · unfold retained
    calc
      _ = ∏ g, ∏ v ∈ (Finset.univ.filter (fun v => owner v=g)), table v (fun j => x (port v j)) := by
        refine Finset.prod_congr rfl (fun g _ => Finset.prod_congr rfl (fun v hv => ?_))
        have hv' := (Finset.mem_filter.mp hv).2
        congr 1
        funext j
        exact extend_restrict_hit group g x _ ((hOwner v j).trans hv')
      _ = _ := Finset.prod_fiberwise _ owner _
  · calc
      _ = ∏ g, ∏ k, ∏ p ∈ addresses group seat g k,
            affine (x (.inl p)) (value c (read shift x p)) := by
        refine Finset.prod_congr rfl (fun g _ => Finset.prod_congr rfl (fun k _ =>
          Finset.prod_congr rfl (fun p hp => ?_)))
        have hg := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        rw [extend_restrict_hit group g x _ hg,local_read group shift hLocal g x p hg]
      _ = _ := by
        simp only [addresses,Finset.prod_fiberwise]

#print axioms local_read
#print axioms physical_child_assembly
end J6RecursiveAssembly
