import J6R12CollisionSource
import A1R9Blocks

/-! Stable ordered-cell grouping on the actual written R12 edge tape.
The routine compares literal endpoint label words and emits entire
incidence records, in order, with a ripple count. No abstract label
lookup, process of choosing a vertex word, or free filter is used. -/

namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits
open J6R12CollisionEdges J6R12CollisionMenu

abbrev CellWord := List Bool × List Bool

def rawCell (e : EdgeTape) : Option CellWord :=
  e.row.label.bind (fun l => e.col.label.map (fun r => (l,r)))

def labelWidths (b : ℕ) (e : EdgeTape) : Prop :=
  (∀ u, e.row.label=some u → u.length=b) ∧
  (∀ v, e.col.label=some v → v.length=b)

def sameCell (b : ℕ) (k : CellWord) (e : EdgeTape) : Meter Bool :=
  match e.row.label,e.col.label with
  | some u,some v =>
    let l := sameBits k.1 u
    let r := sameBits k.2 v
    ⟨l.result && r.result,l.steps+r.steps+4*b+8⟩
  | _,_ => ⟨false,8⟩

theorem sameCell_exact (b : ℕ) (k : CellWord) (e : EdgeTape)
    (hL : k.1.length=b) (hR : k.2.length=b) (he : labelWidths b e) :
    ((sameCell b k e).result=true ↔ rawCell e=some k) ∧
    (sameCell b k e).steps≤24*b+8 := by
  cases hu : e.row.label with
  | none => simp [sameCell,rawCell,hu]
  | some u =>
    cases hv : e.col.label with
    | none => simp [sameCell,rawCell,hu,hv]
    | some v =>
      have hU := hL.trans (he.1 u hu).symm
      have hV := hR.trans (he.2 v hv).symm
      obtain ⟨hl,hlc⟩ := sameBits_exact k.1 u hU
      obtain ⟨hr,hrc⟩ := sameBits_exact k.2 v hV
      have hS (x y : List Bool) (h : x.length=y.length) :
          bitsValue x=bitsValue y ↔ x=y :=
        ⟨equal_width_inj h,fun H => congrArg bitsValue H⟩
      simp only [sameCell,rawCell,hu,hv,Option.bind_some,Option.map_some,
        Bool.and_eq_true,hl,hr,hlc,hrc,hL,hR,Option.some.injEq]
      rw [hS _ _ hU,hS _ _ hV]
      constructor
      · exact ⟨fun h => Prod.ext h.1.symm h.2.symm, fun h =>
          ⟨(congrArg Prod.fst h).symm,(congrArg Prod.snd h).symm⟩⟩
      · omega

def recordTraffic (kR kC b q : ℕ) : ℕ := 4*(kR+kC+2*b+q+4)+8

def scanStepCap (kR kC b q : ℕ) : ℕ :=
  24*b+8+12*q+recordTraffic kR kC b q

def bucket {X : Type*} (view : X → EdgeTape) (k : CellWord) (edges : List X) : List X :=
  edges.filter (fun e => decide (rawCell (view e)=some k))

def groupOne {X : Type*} (view : X → EdgeTape) (kR kC b q : ℕ) (k : CellWord) :
    List X → Meter (List X × List Bool)
  | [] => ⟨([],List.replicate q false),q+2⟩
  | e::es =>
    let s := sameCell b k (view e)
    let t := groupOne view kR kC b q k es
    if s.result then
      let v := addBits t.result.2 (encodeBits q 1)
      ⟨(e::t.result.1,v.result),s.steps+t.steps+v.steps+recordTraffic kR kC b q⟩
    else
      ⟨t.result,s.steps+t.steps+recordTraffic kR kC b q⟩

theorem groupOne_exact {X : Type*} (view : X → EdgeTape) (kR kC b q : ℕ) (hq : 0<q) (k : CellWord) (edges : List X)
    (hL : k.1.length=b) (hR : k.2.length=b)
    (hf : edges.length<2^q) (he : ∀ e∈edges,labelWidths b (view e)) :
    let s := groupOne view kR kC b q k edges
    s.result.1=bucket view k edges ∧ s.result.2.length=q ∧
    bitsValue s.result.2=(bucket view k edges).length ∧
    s.steps≤q+2+edges.length*scanStepCap kR kC b q := by
  induction edges with
  | nil =>
    simp [groupOne,bucket,AOracleMachineTimeMul.value_zero]
  | cons e es ih =>
    have htail : es.length<2^q := by simp only [List.length_cons] at hf; omega
    obtain ⟨hr,hv,hl,hc⟩ := ih htail (fun x hx => he x (List.mem_cons_of_mem _ hx))
    obtain ⟨hs,hsc⟩ := sameCell_exact b k (view e) hL hR (he e List.mem_cons_self)
    let s := sameCell b k (view e)
    let t := groupOne view kR kC b q k es
    change t.result.1=_ at hr
    change t.result.2.length=q at hv
    change bitsValue t.result.2=_ at hl
    change t.steps≤_ at hc
    change (s.result=true ↔ _) at hs
    change s.steps≤_ at hsc
    by_cases H : rawCell (view e)=some k
    · have A := addBits_exact t.result.2 (encodeBits q 1)
        (hv.trans (encodeBits_length _ _).symm)
      have hbucket : (bucket view k es).length≤es.length := List.length_filter_le _ _
      have hk : (bucket view k es).length+1<2^q := by
        simp only [List.length_cons] at hf
        omega
      have hp : 1<(2:ℕ)^q := one_lt_pow₀ (by decide) hq.ne'
      refine ⟨?_,?_,?_,?_⟩
      · change (if s.result then _ else _ : Meter (List X × List Bool)).result.1=_
        rw [if_pos (hs.mpr H)]
        change e::t.result.1=bucket view k (e::es)
        rw [hr]
        simp [bucket,H]
      · simpa only [groupOne,show (sameCell b k (view e)).result=true from hs.mpr H,if_true] using
          A.1.trans hv
      · change bitsValue (if s.result then _ else _ : Meter (List X × List Bool)).result.2=_
        rw [if_pos (hs.mpr H)]
        change bitsValue (addBits t.result.2 (encodeBits q 1)).result=_
        rw [A.2.1,hv,hl,encodeBits_exact _ _ hp,Nat.mod_eq_of_lt hk]
        simp [bucket,H]
      · change (if s.result then _ else _ : Meter (List X × List Bool)).steps≤_
        rw [if_pos (hs.mpr H),List.length_cons,Nat.succ_mul es.length]
        change s.steps+t.steps+(addBits t.result.2 (encodeBits q 1)).steps+recordTraffic kR kC b q≤_
        rw [A.2.2,hv]
        unfold scanStepCap at hc ⊢
        omega
    · have hs' : s.result=false := Bool.eq_false_iff.mpr (fun H' => H (hs.mp H'))
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [groupOne,show (sameCell b k (view e)).result=false from hs',
          Bool.false_eq_true,if_false,bucket,List.filter_cons,H,decide_false] using hr
      · simpa only [groupOne,show (sameCell b k (view e)).result=false from hs',Bool.false_eq_true,if_false] using hv
      · simpa only [groupOne,show (sameCell b k (view e)).result=false from hs',Bool.false_eq_true,
          if_false,bucket,List.filter_cons,H,decide_false] using hl
      · change (if s.result then _ else _ : Meter (List X × List Bool)).steps≤_
        rw [hs',if_neg Bool.false_ne_true,List.length_cons,Nat.succ_mul es.length]
        change s.steps+t.steps+recordTraffic kR kC b q≤_
        unfold scanStepCap at hc ⊢
        omega

#print axioms sameCell_exact
#print axioms groupOne_exact
end J6R14LayoutCost


