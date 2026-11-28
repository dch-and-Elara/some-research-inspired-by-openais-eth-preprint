import J6R68ActiveInputsBaseTape
import J6R23ScheduleWeightRoster

/-! At a genuinely emitted centre, the retained rows are the same
literal stock tape with that key removed, in the same order. This
supplies exactly the R23 numerator and denominator operands. -/
namespace J6R68ActiveInputs
open scoped BigOperators
open AOracleMachineTime A1R10 J6R12CollisionBits
open J6ActiveSchedule J6R23ScheduleWeight P1DyadicGrid HermiteLoss

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15500000
set_option maxRecDepth 3600
set_option Elab.async false

def eraseCentreKey {q : ℕ} (x : RawCentre q) : List (RawCentre q) → Meter (List (RawCentre q))
  | []=>⟨[],3⟩
  | y::ys=>
    let same := sameBits x.key y.key
    let tail := eraseCentreKey x ys
    ⟨if same.result then tail.result else y::tail.result,same.steps+tail.steps+5⟩

theorem erase_centre_key_matches_printed_subsequence {q a : ℕ} (x : RawCentre q)
    (rows : List (RawCentre q)) (w : x.key.length=a+1)
    (width : ∀ y∈rows,y.key.length=a+1) :
    let reader := eraseCentreKey x rows
    reader.result=rows.filter (fun y=>decide (offsetCentre a y.key≠offsetCentre a x.key)) ∧
      reader.steps=(10*(a+1)+5)*rows.length+3 := by
  induction rows with
  | nil => simp [eraseCentreKey]
  | cons y ys ih =>
    have wy := width y List.mem_cons_self
    have hw := sameBits_exact x.key y.key (w.trans wy.symm)
    have hv : bitsValue x.key=bitsValue y.key ↔ offsetCentre a y.key=offsetCentre a x.key := by
      unfold offsetCentre
      omega
    have eq := hw.1.trans hv
    have tailLaw := ih (fun z m=>width z (List.mem_cons_of_mem _ m))
    have hf : (sameBits x.key y.key).steps=10*(a+1) := hw.2.trans (congrArg (10*·) w)
    constructor
    · dsimp only [eraseCentreKey]
      rw [tailLaw.1]
      by_cases p : offsetCentre a y.key=offsetCentre a x.key
      · simp [eq.mpr p,p]
      · have b : (sameBits x.key y.key).result≠true := fun yes=>p (eq.mp yes)
        simp [b,p]
    · change (sameBits x.key y.key).steps+(eraseCentreKey x ys).steps+5=
        (10*(a+1)+5)*(ys.length+1)+3
      rw [hf,tailLaw.2,Nat.mul_succ (10*(a+1)+5) ys.length]
      omega

structure StockTapeCorrect {q : ℕ} (a M u : ℕ) (rows : List (RawCentre q)) : Prop where
  distinct : (rows.map (fun x=>offsetCentre a x.key)).Nodup
  complete : (rows.map (fun x=>offsetCentre a x.key)).toFinset=active a M u
  words : ∀ x∈rows,x.key.length=a+1
  orders : ∀ x∈rows,bitsValue x.multiplicity.val=order M u (offsetCentre a x.key)

theorem paid_base_has_roster_receipt {q a M u : ℕ} (hq : 0<q)
    (edge taper : J6R15ModeCost.Word q) (e : edge.val=M) (v : taper.val=u) (hu : 0<u)
    (hm : u ≤ M) (num : 3*M+u-1<2^q) (fit : 4*M<2^q) :
    StockTapeCorrect a M u (paidBaseTape hq a u edge taper).result := by
  have spec := actual_base_tape_has_stock_census (a:=a) hq edge taper e v hu hm num fit
  dsimp only at spec
  rw [List.map_map] at spec
  exact ⟨spec.1,spec.2.1,fun r mem=>(spec.2.2.1 r mem).1,
    fun r mem=>(spec.2.2.1 r mem).2⟩

def rosterForEmittedCentre {q a M u : ℕ} {rows : List (RawCentre q)}
    (C : StockTapeCorrect a M u rows) (x : RawCentre q) (live : x∈rows) :
    Meter (Roster a M u (offsetCentre a x.key)) := by
  let R := eraseCentreKey x rows
  have checked := erase_centre_key_matches_printed_subsequence x rows (C.words x live) C.words
  let pred := fun (y : RawCentre q)=>decide (offsetCentre a y.key≠offsetCentre a x.key)
  have eq : R.result=rows.filter pred := checked.1
  refine ⟨⟨R.result.map (centreRowValue a),?_,?_,?_⟩,R.steps⟩
  · rw [List.map_map,eq]
    exact ((List.filter_sublist (p:=pred) (l:=rows)).map (fun y => offsetCentre a y.key)).nodup C.distinct
  · rw [List.map_map,eq]
    ext z
    rw [Finset.mem_erase,←C.complete,List.mem_toFinset,List.mem_toFinset]
    simp only [List.mem_map,List.mem_filter,Function.comp_apply]
    constructor
    · rintro ⟨y,⟨h1,h2⟩,rfl⟩
      exact ⟨of_decide_eq_true h2,⟨y,h1,rfl⟩⟩
    · rintro ⟨different,y,mem,rfl⟩
      exact ⟨y,⟨mem,decide_eq_true different⟩,rfl⟩
  · intro y mem
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp mem
    have h : r∈rows := (List.mem_filter.mp (eq ▸ hr)).1
    exact C.orders r h

theorem exactly_paid_R23_roster {q a M u : ℕ} {rows : List (RawCentre q)}
    (C : StockTapeCorrect a M u rows) (x : RawCentre q) (live : x∈rows) (b : Side) :
    let R := rosterForEmittedCentre C x live
    let t := offsetCentre a x.key
    intParts t b R.result.rows=
      ∏ v∈others a t, signedFactor t b v^HermiteLoss.taper u (HermiteLoss.sourceH M u) (HermiteLoss.level v) ∧
      R.steps=(10*(a+1)+5)*rows.length+3 := by
  refine ⟨(rosterForEmittedCentre C x live).result.baseProduct b,?_⟩
  exact (erase_centre_key_matches_printed_subsequence x rows (C.words x live) C.words).2

#print axioms erase_centre_key_matches_printed_subsequence
#print axioms paid_base_has_roster_receipt
#print axioms exactly_paid_R23_roster
end J6R68ActiveInputs
