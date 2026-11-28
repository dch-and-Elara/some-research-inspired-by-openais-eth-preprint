import J6R12CollisionEdges
import J6R12CollisionAccumulator

/-!
# Metered ordered-pair traversal of one encoded graph

At each candidate the only mutable state is the graph edge list.
Every ordered pair is emitted by a sequential two-loop traversal;
both repetitions and literal tape copying are explicitly charged.
The resulting score is an exact natural number, not a residue.
-/

namespace J6R12CollisionGraphScore
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionBits J6R12CollisionEdges J6R12CollisionAccumulator J6R11CollisionCost

def copyBudget (kR kC b : ℕ) : ℕ := 4*kR+4*kC+8*b+16

def emitOne (cost : ℕ) (e : EdgeTape) : List EdgeTape → Meter (List PairTape) :=
  mapMeter (fun t => ⟨pair e t,cost⟩)

def emitPairs (cost : ℕ) (inner : List EdgeTape) : List EdgeTape→Meter (List PairTape)
  | [] => ⟨[],0⟩
  | e::outer =>
    let a := emitOne cost e inner
    let s := emitPairs cost inner outer
    ⟨a.result++s.result,a.steps+s.steps+4*a.result.length+4⟩

theorem emitOne_exact (cost : ℕ) (e : EdgeTape) (l : List EdgeTape) :
    (emitOne cost e l).result=l.map (pair e) ∧ (emitOne cost e l).steps=(cost+6)*l.length := by
  induction l with
  | nil => simp [emitOne,mapMeter]
  | cons t l ih =>
    change pair e t :: (emitOne cost e l).result = _ ∧
      cost + (emitOne cost e l).steps + 6 = _
    rw [ih.1,ih.2,List.map_cons,List.length_cons,Nat.mul_succ]
    exact ⟨rfl,by omega⟩

theorem emitPairs_exact (cost : ℕ) (l r : List EdgeTape) :
    (emitPairs cost r l).result=(l.product r).map (fun t => pair t.1 t.2) ∧
      (emitPairs cost r l).steps=((cost+10)*r.length+4)*l.length := by
  induction l with
  | nil => simp [emitPairs,List.product]
  | cons e es ih =>
    obtain ⟨hr,hc⟩ := emitOne_exact cost e r
    refine ⟨?_,?_⟩
    · simp [emitPairs,hr,ih.1,List.product,List.map_append,List.map_map,Function.comp_apply]
    · change (emitOne cost e r).steps+(emitPairs cost r es).steps+
        4*(emitOne cost e r).result.length+4=((cost+10)*r.length+4)*(es.length+1)
      rw [hc,ih.2,hr,List.length_map,Nat.mul_succ]
      ring

private theorem pairs_map {X Y Z : Type*} (c : X→Y) (f : Y→Y→Z)
    (l r : List X) :
    ((l.map c).product (r.map c)).map (fun t => f t.1 t.2) =
      (l.product r).map (fun t => f (c t.1) (c t.2)) := by
  induction l with
  | nil => simp [List.product]
  | cons x xs ih =>
    simp [List.product,List.map_map,List.map_append] at ih ⊢
    exact congrArg ((r.map fun y => f (c x) (c y)) ++ ·) ih

def scoreGraph (w kR kC b : ℕ) (L : Literals) (es : List EdgeTape) : Meter (List Bool) :=
  let q := emitPairs (copyBudget kR kC b) es es
  let s := scoreTape w kR kC b L q.result
  ⟨s.result,q.steps+s.steps+8⟩

def scoreGraphBudget (w kR kC b M : ℕ) : ℕ :=
  ((copyBudget kR kC b+10)*M+4)*M +
  (w+(pairBudget kR kC b w+14*w+8)*M^2)+8

theorem scoreGraph_exact {E R C A : Type*} [Fintype E] [Fintype A] [Nonempty A]
    (w kR kC b : ℕ) (rCode : R→ℕ) (cCode : C→ℕ) (aCode : A→ℕ)
    (hr : Function.Injective rCode) (hc : Function.Injective cCode) (ha : Function.Injective aCode)
    (hR : ∀ i, rCode i<2^kR) (hC : ∀ i, cCode i<2^kC) (hA : ∀ i, aCode i<2^b)
    (h₁ : 1<2^w) (hB : Fintype.card A<2^w) (hBB : (Fintype.card A)^2<2^w)
    (row : E→R) (col : E→C) (p : R⊕C→Option A)
    (edges : List E) (hn : edges.Nodup) (hs : ∀ e : E, e ∈ edges)
    (hfit : integerScore row col p<2^w) :
    let z := scoreGraph w kR kC b (makeLiterals w (Fintype.card A))
      (edges.map (packEdge kR kC b rCode cCode aCode row col p))
    z.result.length=w ∧ bitsValue z.result=integerScore row col p ∧
      z.steps≤scoreGraphBudget w kR kC b (Fintype.card E) := by
  let F := packEdge kR kC b rCode cCode aCode row col p
  let p' := emitPairs (copyBudget kR kC b) (edges.map F) (edges.map F)
  obtain ⟨hR',hc'⟩ := emitPairs_exact (copyBudget kR kC b) (edges.map F) (edges.map F)
  have hl : edges.length=Fintype.card E := by
    rw [← List.toFinset_card_of_nodup hn]
    have hset : edges.toFinset=Finset.univ := by ext e; simp [hs e]
    rw [hset,Finset.card_univ]
  let P := edges.product edges
  have hP : p'.result=P.map (packPair kR kC b rCode cCode aCode row col p) := by
    change (emitPairs (copyBudget kR kC b) (edges.map F) (edges.map F)).result=_
    rw [hR',pairs_map]
    rfl
  let C := scoreTape w kR kC b (makeLiterals w (Fintype.card A))
  have hz := scoreTape_exact w kR kC b rCode cCode aCode hr hc ha hR hC hA h₁ hB hBB row col p
    P (hn.product hn) (fun ef => List.mem_product.mpr ⟨hs ef.1,hs ef.2⟩) hfit
  change (C (P.map _)).result.length=w ∧ bitsValue (C (P.map _)).result=integerScore row col p ∧
    (C (P.map _)).steps≤_ at hz
  change (C p'.result).result.length=w ∧ bitsValue (C p'.result).result=integerScore row col p ∧
    p'.steps+(C p'.result).steps+8≤_
  rw [hP]
  refine ⟨hz.1,hz.2.1,?_⟩
  change p'.steps=_ at hc'
  rw [hc',List.length_map,hl]
  exact Nat.add_le_add_right (Nat.add_le_add_left hz.2.2 _) _

/-- The actual tape padding. The extra bit also fits constants for
empty graphs; no score can reach the modular wraparound point. -/
def scoreWidth (e b : ℕ) : ℕ := 2*(e+b)+1

theorem scoreWidth_fits (B e b : ℕ) (hB : B≤2^b) :
    1<2^(scoreWidth e b) ∧ B<2^(scoreWidth e b) ∧ B^2<2^(scoreWidth e b) := by
  have h1 : 0<(2:ℕ)^(2*(e+b)) := by positivity
  have hw : (2:ℕ)^(2*(e+b))<2^(scoreWidth e b) := by
    rw [scoreWidth,pow_succ]
    omega
  have hbe : (2:ℕ)^b≤2^(e+b) := by
    rw [pow_add]
    have h2 : 1≤(2:ℕ)^e := Nat.succ_le_of_lt (by positivity)
    simpa only [one_mul] using Nat.mul_le_mul_right ((2:ℕ)^b) h2
  have hx : (2:ℕ)^(e+b)≤2^(2*(e+b)) := by
    rw [Nat.mul_comm 2 (e+b),pow_mul,pow_two]
    exact Nat.le_mul_self _
  have hsq : B^2≤2^(2*(e+b)) := by
    rw [Nat.mul_comm 2 (e+b),pow_mul,pow_two,pow_two]
    exact Nat.mul_le_mul (hB.trans hbe) (hB.trans hbe)
  exact ⟨(Nat.succ_le_of_lt h1).trans_lt hw,((hB.trans hbe).trans hx).trans_lt hw,hsq.trans_lt hw⟩

#print axioms emitOne_exact
#print axioms emitPairs_exact
#print axioms scoreGraph_exact
#print axioms scoreWidth_fits

end J6R12CollisionGraphScore
