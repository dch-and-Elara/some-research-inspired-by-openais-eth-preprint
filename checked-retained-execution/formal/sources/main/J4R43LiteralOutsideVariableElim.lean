import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! Finite induced-width step used by J4. Each factor is actually a
table on a specified local scope. An elimination step materializes
only a table on the union of the participating scopes minus the
eliminated Boolean coordinate. -/
namespace J4R43LiteralOutside.VE
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {V R : Type} [Fintype V] [DecidableEq V] [CommRing R]

structure Factor (V R : Type) where
  scope : Finset V
  table : (scope→Bool)→R

def extend (s : Finset V) (z : s→Bool) (v : V) : Bool :=
  if e : v∈s then z ⟨v,e⟩ else false

theorem restrict_extend (s : Finset V) (z : s→Bool) (v : s) : extend s z v=z v := by
  simp [extend,v.property]

def Factor.eval (F : Factor V R) (w : V→Bool) : R :=
  F.table (fun v=>w v)

theorem evaluate_congr (F : Factor V R) {x y : V→Bool}
    (h : ∀ v∈F.scope,x v=y v) : F.eval x=F.eval y := by
  unfold Factor.eval
  congr 1
  funext j
  exact h j j.property

def fromScope (s : Finset V) (f : (V→Bool)→R) : Factor V R :=
  ⟨s,fun x=>f (extend s x)⟩

theorem fromScope_exact (s : Finset V) (f : (V→Bool)→R)
    (locality : ∀ x y, (∀ v∈s,x v=y v)→f x=f y) (z : V→Bool) :
    (fromScope s f).eval z=f z := by
  apply locality
  intro v hv
  exact restrict_extend s (fun p=>z p) ⟨v,hv⟩

def prodAt (F : List (Factor V R)) (x : V→Bool) : R :=
  (F.map (fun f=>f.eval x)).prod

theorem product_scope_congr (F : List (Factor V R)) {x y : V→Bool}
    (h : ∀ f∈F,∀ v∈f.scope,x v=y v) :
    prodAt F x = prodAt F y := by
  induction F with
  | nil => rfl
  | cons f fs ih =>
    change f.eval x*prodAt fs x=f.eval y*prodAt fs y
    rw [evaluate_congr f (h f (List.mem_cons_self ..)),
      ih (fun g hg=>h g (List.mem_cons_of_mem _ hg))]

def inside (v : V) (fs : List (Factor V R)) :=
  fs.filter (fun f=>decide (v∈f.scope))

def outside (v : V) (fs : List (Factor V R)) :=
  fs.filter (fun f=>decide (v∉f.scope))

theorem owns_factor (v : V) (fs : List (Factor V R)) (f : Factor V R) :
    f∈inside v fs ↔ f∈fs ∧ v∈f.scope := by simp [inside]

theorem misses_factor (v : V) (fs : List (Factor V R)) (f : Factor V R) :
    f∈outside v fs ↔ f∈fs ∧ v∉f.scope := by simp [outside]

theorem partition_value (v : V) (fs : List (Factor V R)) (w : V→Bool) :
    prodAt fs w=prodAt (inside v fs) w*prodAt (outside v fs) w := by
  induction fs with
  | nil => simp [prodAt,inside,outside]
  | cons f fs ih =>
    simp only [prodAt,inside,outside] at ih
    by_cases h : v∈f.scope <;>
      simp [prodAt,inside,outside,h,ih,mul_assoc,mul_left_comm,mul_comm]

def bucketScope (v : V) (fs : List (Factor V R)) : Finset V :=
  Finset.univ.filter fun u=>u≠v ∧ ∃ f∈fs,v∈f.scope ∧ u∈f.scope

theorem mem_bucket (v : V) (fs : List (Factor V R)) (u : V) :
    u∈bucketScope v fs ↔ u≠v ∧ ∃ f∈inside v fs,u∈f.scope := by
  simp only [bucketScope,Finset.mem_filter,Finset.mem_univ,true_and,owns_factor]
  constructor
  · rintro ⟨ne,f,h,c,z⟩; exact ⟨ne,f,⟨h,c⟩,z⟩
  · rintro ⟨ne,f,⟨h,c⟩,z⟩; exact ⟨ne,f,h,c,z⟩

def updateFactor (v : V) (fs : List (Factor V R)) : Factor V R :=
  ⟨bucketScope v fs,fun z=>
    prodAt (inside v fs) (Function.update (extend (bucketScope v fs) z) v false)+
    prodAt (inside v fs) (Function.update (extend (bucketScope v fs) z) v true)⟩

def eliminate (v : V) (fs : List (Factor V R)) : List (Factor V R) :=
  updateFactor v fs :: outside v fs

theorem local_update (v : V) (fs : List (Factor V R)) (w : V→Bool) (b : Bool) :
    prodAt (inside v fs) (Function.update (extend (bucketScope v fs) (fun u=>w u)) v b)=
      prodAt (inside v fs) (Function.update w v b) := by
  apply product_scope_congr
  intro f h u hu
  by_cases eq : u=v
  · subst u
    simp
  · have H := (mem_bucket v fs u).mpr ⟨eq,f,h,hu⟩
    simp [Function.update_of_ne eq,extend,H]

theorem nonparticipant_update (v : V) (fs : List (Factor V R)) (w : V→Bool) (b : Bool) :
    prodAt (outside v fs) (Function.update w v b)=prodAt (outside v fs) w := by
  apply product_scope_congr
  intro f hf u hu
  apply Function.update_of_ne
  intro eq
  exact (misses_factor v fs f).mp hf |>.2 (eq ▸ hu)

theorem local_eliminate_identity (v : V) (fs : List (Factor V R)) (w : V→Bool) :
    prodAt (eliminate v fs) w =
      prodAt fs (Function.update w v false)+prodAt fs (Function.update w v true) := by
  simp only [eliminate,prodAt,List.map_cons,List.prod_cons]
  change (updateFactor v fs).eval w * prodAt (outside v fs) w=
    prodAt fs (Function.update w v false)+prodAt fs (Function.update w v true)
  rw [partition_value v fs (Function.update w v false),partition_value v fs (Function.update w v true),
    nonparticipant_update,nonparticipant_update,←add_mul]
  change (prodAt (inside v fs) (Function.update (extend (bucketScope v fs) _) v false)+
    prodAt (inside v fs) (Function.update (extend (bucketScope v fs) _) v true))*_=_
  exact congrArg (fun z=>z*prodAt (outside v fs) w)
    (congrArg₂ (·+·) (local_update v fs w false) (local_update v fs w true))

def activeSum (active : Finset V) (fs : List (Factor V R)) : R :=
  ∑ z : active→Bool,prodAt fs (extend active z)

def splitBit (active : Finset V) (v : V) (inV : v∈active) :
    (active→Bool) ≃ ((active.erase v→Bool)×Bool) where
  toFun z := (fun u=>z ⟨u,(Finset.mem_erase.mp u.property).2⟩,z ⟨v,inV⟩)
  invFun q u := if e : u.val=v then q.2 else
    q.1 ⟨u,Finset.mem_erase.mpr ⟨e,u.property⟩⟩
  left_inv z := by
    funext u
    by_cases e : u.val=v
    · have hu : (⟨v,inV⟩ : active)=u := Subtype.ext e.symm
      simp [e,hu]
    · simp [e]
  right_inv q := by
    apply Prod.ext
    · funext u
      simp [(Finset.mem_erase.mp u.property).1]
    · simp

theorem split_extend (active : Finset V) (v : V) (inV : v∈active)
    (z : active.erase v→Bool) (b : Bool) :
    extend active ((splitBit active v inV).symm (z,b))=
      Function.update (extend (active.erase v) z) v b := by
  funext w
  by_cases e : w=v
  · subst w
    simp [extend,splitBit,inV]
  · by_cases h : w∈active
    · have a : w∈active.erase v := Finset.mem_erase.mpr ⟨e,h⟩
      simp [extend,splitBit,e,h,a,Function.update_of_ne]
    · have a : w∉active.erase v := fun x=>h (Finset.mem_erase.mp x).2
      simp [extend,e,h,a,Function.update_of_ne]

theorem active_eliminate_exact (active : Finset V) (v : V) (inV : v∈active)
    (fs : List (Factor V R)) :
    activeSum active fs = activeSum (active.erase v) (eliminate v fs) := by
  unfold activeSum
  let e := splitBit active v inV
  calc
    _ = ∑ q : (active.erase v→Bool)×Bool,prodAt fs (extend active (e.symm q)) :=
      Fintype.sum_equiv e _ _ (fun z=>by rw [Equiv.symm_apply_apply])
    _ = _ := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun z _=>?_
      rw [Fintype.sum_bool]
      change prodAt fs (extend active ((splitBit active v inV).symm (z,true)))+
        prodAt fs (extend active ((splitBit active v inV).symm (z,false)))=_
      rw [split_extend,split_extend,local_eliminate_identity]
      exact add_comm _ _

theorem bucket_entries (v : V) (fs : List (Factor V R)) (w : ℕ)
    (width : (bucketScope v fs).card≤w) :
    Fintype.card ((bucketScope v fs)→Bool)≤2^w := by
  rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe]
  exact Nat.pow_le_pow_right (by decide) width

#print axioms fromScope_exact
#print axioms partition_value
#print axioms local_eliminate_identity
#print axioms split_extend
#print axioms active_eliminate_exact
#print axioms bucket_entries
end
end J4R43LiteralOutside.VE

