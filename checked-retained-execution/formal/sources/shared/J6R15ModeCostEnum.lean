import Mathlib.Tactic
import Mathlib.Data.List.Nodup

/-! Exact feasible-mode catalogue at strict precision p. We enumerate
branches by ascending exponent, with the *inclusive* remaining budget
initialized to p-1 only when p>0. No zero or illegal prefixes enter
the search tree. This file models counts, not bit traffic. -/
namespace J6R15ModeCost

def weightedDegree : List ℕ → List ℕ → ℕ
  | w::ws,e::es => w*e+weightedDegree ws es
  | _,_ => 0

def feasible (ws : List ℕ) (K : ℕ) (es : List ℕ) : Prop :=
  es.length=ws.length ∧ weightedDegree ws es≤K

def enumerate : List ℕ → ℕ → List (List ℕ)
  | [],_ => [[]]
  | w::ws,K =>
    (List.range (K/w+1)).flatMap fun a =>
      (enumerate ws (K-w*a)).map (List.cons a)

def strictTuples (ws : List ℕ) (p : ℕ) : List (List ℕ) :=
  if p=0 then [] else enumerate ws (p-1)

theorem enumerate_mem {ws : List ℕ} (hpos : ∀ w∈ws,0<w) (K : ℕ) (es : List ℕ) :
    es∈enumerate ws K ↔ feasible ws K es := by
  induction ws generalizing K es with
  | nil => simp [enumerate,feasible,weightedDegree]
  | cons w ws ih =>
    have hw := hpos w List.mem_cons_self
    have hs : ∀ x∈ws,0<x := fun x h => hpos x (List.mem_cons_of_mem _ h)
    cases es with
    | nil => simp [enumerate,feasible]
    | cons a es =>
      simp only [enumerate,List.mem_flatMap,List.mem_range,List.mem_map,List.cons.injEq,
        feasible,List.length_cons,Nat.succ.injEq,weightedDegree]
      constructor
      · rintro ⟨b,hb,y,hy,hba,hye⟩
        subst b
        subst y
        have hB := (Nat.le_div_iff_mul_le hw).mp (Nat.le_of_lt_succ hb)
        obtain ⟨hL,hD⟩ := (ih hs _ _).mp hy
        change es.length=ws.length at hL
        change weightedDegree ws es≤K-w*a at hD
        rw [Nat.mul_comm] at hB
        exact ⟨hL,by omega⟩
      · rintro ⟨hL,hD⟩
        have hh : w*a≤K := by omega
        have ha : a≤K/w := (Nat.le_div_iff_mul_le hw).mpr (by simpa [Nat.mul_comm a w] using hh)
        exact ⟨a,Nat.lt_succ_of_le ha,es,(ih hs _ _).mpr ⟨hL,by omega⟩,
          rfl,rfl⟩

theorem enumerate_nodup (ws : List ℕ) (K : ℕ) :
    (enumerate ws K).Nodup := by
  induction ws generalizing K with
  | nil => simp [enumerate]
  | cons w ws ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro a _
      exact (ih _).map (fun _ _ h => (List.cons.inj h).2)
    · have hR : (List.range (K/w+1)).Nodup := List.nodup_range
      apply hR.imp
      intro a b hab zs ha hb
      obtain ⟨x,_,hx⟩ := List.mem_map.mp ha
      obtain ⟨y,_,hy⟩ := List.mem_map.mp hb
      exact hab (List.cons.inj (hx.trans hy.symm)).1

theorem zeros_feasible (ws : List ℕ) (K : ℕ) :
    feasible ws K (List.replicate ws.length 0) := by
  refine ⟨by simp,?_⟩
  suffices h : weightedDegree ws (List.replicate ws.length 0)=0 by simp [h]
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons,List.replicate_succ,weightedDegree,Nat.mul_zero,Nat.zero_add,ih]

theorem enum_nonempty {ws : List ℕ} (h : ∀ w∈ws,0<w) (K : ℕ) :
    1≤(enumerate ws K).length :=
  List.length_pos_of_mem ((enumerate_mem h K _).mpr (zeros_feasible ws K))

theorem strictTuples_exact (ws : List ℕ) (p : ℕ) (hpos : ∀ w∈ws,0<w) :
    (strictTuples ws p).Nodup ∧
    ∀ es,es∈strictTuples ws p ↔ es.length=ws.length ∧ weightedDegree ws es<p := by
  by_cases hp : p=0
  · simp [strictTuples,hp]
  · refine ⟨by simpa only [strictTuples,if_neg hp] using enumerate_nodup ws (p-1),?_⟩
    intro es
    rw [strictTuples,if_neg hp,enumerate_mem hpos]
    unfold feasible
    omega

def nodeCount : List ℕ → ℕ → ℕ
  | [],_ => 1
  | w::ws,K => 1+((List.range (K/w+1)).map (fun a => nodeCount ws (K-w*a))).sum

theorem list_sum_mul_bound {A : Type*} (c : ℕ) (f g : A→ℕ) (xs : List A)
    (h : ∀ x∈xs,f x≤c*g x) :
    (xs.map f).sum≤c*(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,Nat.mul_add]
    exact Nat.add_le_add (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem nodeCount_le {ws : List ℕ} (hpos : ∀ w∈ws,0<w) (K : ℕ) :
    nodeCount ws K≤(ws.length+1)*(enumerate ws K).length := by
  induction ws generalizing K with
  | nil => simp [nodeCount,enumerate]
  | cons w ws ih =>
    have hp : ∀ w∈ws,0<w := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    let A := List.range (K/w+1)
    let L := (enumerate (w::ws) K).length
    have hl : L=(A.map (fun a=>(enumerate ws (K-w*a)).length)).sum := by
      simp only [L,A,enumerate,List.length_flatMap,List.length_map]
    have hL : 1≤L := enum_nonempty hpos K
    have h := list_sum_mul_bound (ws.length+1) (fun a=>nodeCount ws (K-w*a))
      (fun a=>(enumerate ws (K-w*a)).length) A (fun a _ => ih hp _)
    change 1+(A.map (fun a=>nodeCount ws (K-w*a))).sum≤_
    rw [← hl] at h
    change 1+(A.map (fun a=>nodeCount ws (K-w*a))).sum≤((w::ws).length+1)*L
    rw [List.length_cons,show ws.length+1+1=(ws.length+1)+1 from rfl,Nat.add_mul,Nat.one_mul]
    omega

#print axioms enumerate_mem
#print axioms strictTuples_exact
#print axioms nodeCount_le
end J6R15ModeCost




