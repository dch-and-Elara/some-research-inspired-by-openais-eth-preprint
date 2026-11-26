import GroupProducts
import P5MainIteratorSource

/-! Exact native product of fiber sums. The cut used by a macro is the
factor-sign grouping, while the summed Boolean variables have their own
assignment grouping; the proof does not identify these two partitions. -/
namespace P5MainBalance
open scoped BigOperators Classical

variable {X V B I R : Type*} [Fintype X] [Fintype B] [DecidableEq B] [CommSemiring R]

abbrev GroupBits (a : X→B) (g : B) := {x : X // a x=g} → Bool

def restrictGroup (a : X→B) (x : X→Bool) (g : B) : GroupBits a g :=
  fun u=>x u.val

def combineGroups (a : X→B) (x : ∀ g,GroupBits a g) : X→Bool :=
  fun v=>x (a v) ⟨v,rfl⟩

omit [Fintype X] [Fintype B] [DecidableEq B] in
theorem restrict_combine_group (a : X→B) (x : ∀ g,GroupBits a g) (g : B) :
    restrictGroup a (combineGroups a x) g=x g := by
  funext u
  rcases u with ⟨v,h⟩
  subst g
  rfl

def Fiber (a : X→B) (ok : ∀ g, GroupBits a g→Prop) (g : B) :=
  {x : GroupBits a g // ok g x}

def CombinedFiber (a : X→B) (ok : ∀ g, GroupBits a g→Prop) :=
  {x : X→Bool // ∀ g,ok g (restrictGroup a x g)}

noncomputable instance (a : X→B) (ok : ∀ g,GroupBits a g→Prop) (g : B) :
    Fintype (Fiber a ok g) := by unfold Fiber; infer_instance

noncomputable instance (a : X→B) (ok : ∀ g,GroupBits a g→Prop) :
    Fintype (CombinedFiber a ok) := by unfold CombinedFiber; infer_instance

def fibreEquiv (a : X→B) (ok : ∀ g,GroupBits a g→Prop) :
    CombinedFiber a ok ≃ (∀ g,Fiber a ok g) where
  toFun x g := ⟨restrictGroup a x.1 g,x.2 g⟩
  invFun v := ⟨combineGroups a (fun g=>(v g).val),
    fun g=>by rw [restrict_combine_group]; exact (v g).property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv v := by
    funext g
    apply Subtype.ext
    exact restrict_combine_group a (fun g=>(v g).val) g

/-- Fixed y and E are checked separately in every group. All factors
are already grouped by their source factor labels at the chosen node. -/
noncomputable def actualFibreMacro (L : V→I→B) (t : I)
    (a : X→B) (ok : ∀ g,GroupBits a g→Prop)
    (localFactor : ∀ g, ({v : V//L v t=g}→Bool)→GroupBits a g→R) :
    GroupProducts.GroupTerm L R where
  coordinate := t
  coeff := 1
  factor g s := ∑ x : Fiber a ok g,localFactor g s x.val

theorem exact_grouped_fibre_update (L : V→I→B) (t : I)
    (a : X→B) (ok : ∀ g,GroupBits a g→Prop)
    (localFactor : ∀ g, ({v : V//L v t=g}→Bool)→GroupBits a g→R) (σ : V→Bool) :
    (actualFibreMacro L t a ok localFactor).value σ =
      ∑ x : CombinedFiber a ok,∏ g,localFactor g (fun v=>σ v.val) (restrictGroup a x.val g) := by
  unfold GroupProducts.GroupTerm.value
  change 1*(∏ g,∑ x : Fiber a ok g,localFactor g (fun v=>σ v.val) x.val)=_
  rw [one_mul,Fintype.prod_sum (fun g (x : Fiber a ok g)=>localFactor g (fun v=>σ v.val) x.val)]
  exact (fibreEquiv a ok).sum_comp (fun x=>∏ g,localFactor g (fun v=>σ v.val) (x g).val) |>.symm

#print axioms restrict_combine_group
#print axioms fibreEquiv
#print axioms exact_grouped_fibre_update
end P5MainBalance
