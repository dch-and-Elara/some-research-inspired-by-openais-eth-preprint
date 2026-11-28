import J6R12CollisionBits

/-!
# A sequentially read graph tape with replicated endpoint labels

One endpoint label is stored with each incidence record. Assigning a
candidate visits every edge record and rewrites all matching copies.
This replaces any unit-cost query to an abstract marginal table by a
charged sequential pass over the encoded graph. Isolated vertices
correctly cause no change to the score graph.
-/

namespace J6R12CollisionEdges
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionBits

structure EdgeTape where
  row : EndTape
  col : EndTape

def packEdge {E R C A : Type*} (kR kC b : ℕ) (rCode : R→ℕ) (cCode : C→ℕ) (aCode : A→ℕ)
    (row : E→R) (col : E→C) (p : R⊕C→Option A) (e : E) : EdgeTape :=
  ⟨packEnd kR b rCode aCode (fun i => p (.inl i)) (row e),
   packEnd kC b cCode aCode (fun i => p (.inr i)) (col e)⟩

def pair (x y : EdgeTape) : PairTape := ⟨x.row,y.row,x.col,y.col⟩

def writeEnd (k b : ℕ) (id lab : List Bool) (e : EndTape) : Meter EndTape :=
  let s := sameBits id e.addr
  ⟨⟨e.addr,if s.result then some lab else e.label⟩,s.steps+2*k+2*b+8⟩

theorem writeEnd_exact {I A : Type*} (k b : ℕ) (code : I→ℕ) (aCode : A→ℕ)
    (hcode : Function.Injective code) (hf : ∀ i, code i<2^k)
    (p : I→Option A) (i j : I) (lab : A) :
    let s := writeEnd k b (encodeBits k (code i)) (encodeBits b (aCode lab))
      (packEnd k b code aCode p j)
    s.result=packEnd k b code aCode (Function.update p i (some lab)) j ∧
    s.steps=12*k+2*b+8 := by
  let q := sameBits (encodeBits k (code i)) (encodeBits k (code j))
  have H := sameBits_exact (encodeBits k (code i)) (encodeBits k (code j)) (by simp [encodeBits_length])
  have he : q.result=true ↔ i=j := by
    simpa only [q,encodeBits_exact _ _ (hf _),hcode.eq_iff] using H.1
  have hs : q.steps=10*k := H.2.trans (by simp [encodeBits_length])
  refine ⟨?_,?_⟩
  · change EndTape.mk (encodeBits k (code j)) (if q.result then some (encodeBits b (aCode lab)) else _) = _
    by_cases h : i=j
    · subst j
      simp [he.mpr rfl,packEnd]
    · have hq := he.not.mpr h
      simp [hq,packEnd,Function.update_of_ne (Ne.symm h)]
  · change q.steps+2*k+2*b+8=_
    omega

inductive RegisterWrite
  | row (id lab : List Bool)
  | col (id lab : List Bool)

def writeEdge (kR kC b : ℕ) (cmd : RegisterWrite) (e : EdgeTape) : Meter EdgeTape :=
  match cmd with
  | .row i l =>
    let v := writeEnd kR b i l e.row
    ⟨⟨v.result,e.col⟩,v.steps+2*kC+2*b+8⟩
  | .col i l =>
    let v := writeEnd kC b i l e.col
    ⟨⟨e.row,v.result⟩,v.steps+2*kR+2*b+8⟩

def writeBudget (kR kC b : ℕ) : ℕ := 12*kR+12*kC+4*b+16

def encodeWrite {R C A : Type*} (kR kC b : ℕ) (rCode : R→ℕ) (cCode : C→ℕ) (aCode : A→ℕ)
    (q : R⊕C) (lab : A) : RegisterWrite :=
  match q with
  | .inl i => .row (encodeBits kR (rCode i)) (encodeBits b (aCode lab))
  | .inr i => .col (encodeBits kC (cCode i)) (encodeBits b (aCode lab))

private theorem update_left {R C A : Type*} (p : R⊕C→Option A) (i : R) (lab : A) :
    (fun j : R => Function.update p (.inl i) (some lab) (.inl j)) =
      Function.update (fun j : R => p (.inl j)) i (some lab) := by
  funext j
  by_cases h : j=i
  · subst j
    simp
  · have hc : (Sum.inl j : R⊕C) ≠ .inl i := by simpa using h
    rw [Function.update_of_ne hc,Function.update_of_ne h]

private theorem update_right {R C A : Type*} (p : R⊕C→Option A) (i : C) (lab : A) :
    (fun j : C => Function.update p (.inr i) (some lab) (.inr j)) =
      Function.update (fun j : C => p (.inr j)) i (some lab) := by
  funext j
  by_cases h : j=i
  · subst j
    simp
  · have hc : (Sum.inr j : R⊕C) ≠ .inr i := by simpa using h
    rw [Function.update_of_ne hc,Function.update_of_ne h]

theorem writeEdge_exact {E R C A : Type*} (kR kC b : ℕ) (rCode : R→ℕ) (cCode : C→ℕ)
    (aCode : A→ℕ) (hr : Function.Injective rCode) (hc : Function.Injective cCode)
    (hR : ∀ i, rCode i<2^kR) (hC : ∀ i, cCode i<2^kC)
    (row : E→R) (col : E→C) (p : R⊕C→Option A) (q : R⊕C) (lab : A) (e : E) :
    let z := writeEdge kR kC b (encodeWrite kR kC b rCode cCode aCode q lab)
      (packEdge kR kC b rCode cCode aCode row col p e)
    z.result=packEdge kR kC b rCode cCode aCode row col (Function.update p q (some lab)) e ∧
    z.steps≤writeBudget kR kC b := by
  cases q with
  | inl i =>
    have hh := writeEnd_exact kR b rCode aCode hr hR (fun j => p (.inl j)) i (row e) lab
    dsimp only [encodeWrite,writeEdge,packEdge]
    rw [hh.1,hh.2,update_left]
    have he : (fun j : C => Function.update p (.inl i) (some lab) (.inr j)) = fun j => p (.inr j) := by
      funext j
      exact Function.update_of_ne (by simp : (Sum.inr j : R⊕C) ≠ .inl i) _ _
    rw [he]
    exact ⟨rfl,by unfold writeBudget; omega⟩
  | inr i =>
    have hh := writeEnd_exact kC b cCode aCode hc hC (fun j => p (.inr j)) i (col e) lab
    dsimp only [encodeWrite,writeEdge,packEdge]
    rw [hh.1,hh.2,update_right]
    have he : (fun j : R => Function.update p (.inr i) (some lab) (.inl j)) = fun j => p (.inl j) := by
      funext j
      exact Function.update_of_ne (by simp : (Sum.inl j : R⊕C) ≠ .inr i) _ _
    rw [he]
    exact ⟨rfl,by unfold writeBudget; omega⟩

def mapMeter {X Y : Type*} (f : X→Meter Y) : List X→Meter (List Y)
  | [] => ⟨[],0⟩
  | x::xs =>
    let q := f x
    let tail := mapMeter f xs
    ⟨q.result::tail.result,q.steps+tail.steps+6⟩

theorem mapMeter_exact {X Y : Type*} (f : X→Meter Y) (g : X→Y) (B : ℕ) (xs : List X)
    (hs : ∀ x ∈ xs, (f x).result=g x ∧ (f x).steps≤B) :
    (mapMeter f xs).result=xs.map g ∧ (mapMeter f xs).steps≤(B+6)*xs.length := by
  induction xs with
  | nil => simp [mapMeter]
  | cons x xs ih =>
    obtain ⟨hr,hc⟩ := hs x List.mem_cons_self
    obtain ⟨hrr,hcc⟩ := ih (fun y hy => hs y (List.mem_cons_of_mem _ hy))
    refine ⟨?_,?_⟩
    · simp [mapMeter,hr,hrr]
    · change (f x).steps+(mapMeter f xs).steps+6≤(B+6)*(xs.length+1)
      rw [Nat.mul_succ]
      omega

def writeGraph (kR kC b : ℕ) (cmd : RegisterWrite) : List EdgeTape→Meter (List EdgeTape) :=
  mapMeter (writeEdge kR kC b cmd)

theorem writeGraph_exact {E R C A : Type*} (kR kC b : ℕ) (rCode : R→ℕ) (cCode : C→ℕ)
    (aCode : A→ℕ) (hr : Function.Injective rCode) (hc : Function.Injective cCode)
    (hR : ∀ i, rCode i<2^kR) (hC : ∀ i, cCode i<2^kC)
    (row : E→R) (col : E→C) (p : R⊕C→Option A) (q : R⊕C) (lab : A) (es : List E) :
    let z := writeGraph kR kC b (encodeWrite kR kC b rCode cCode aCode q lab)
      (es.map (packEdge kR kC b rCode cCode aCode row col p))
    z.result=es.map (packEdge kR kC b rCode cCode aCode row col (Function.update p q (some lab))) ∧
    z.steps≤(writeBudget kR kC b+6)*es.length := by
  let f := packEdge kR kC b rCode cCode aCode row col p
  let g := packEdge kR kC b rCode cCode aCode row col (Function.update p q (some lab))
  let M := writeEdge kR kC b (encodeWrite kR kC b rCode cCode aCode q lab)
  have hg : mapMeter M (es.map f) = mapMeter (fun e => M (f e)) es := by
    induction es with
    | nil => rfl
    | cons e es ih => simp only [List.map_cons,mapMeter,ih]
  change (mapMeter M (es.map f)).result=es.map g ∧
    (mapMeter M (es.map f)).steps≤(writeBudget kR kC b+6)*es.length
  rw [hg]
  exact mapMeter_exact _ g _ es (fun e _ =>
    writeEdge_exact kR kC b rCode cCode aCode hr hc hR hC row col p q lab e)

#print axioms writeEnd_exact
#print axioms writeEdge_exact
#print axioms mapMeter_exact
#print axioms writeGraph_exact

end J6R12CollisionEdges
