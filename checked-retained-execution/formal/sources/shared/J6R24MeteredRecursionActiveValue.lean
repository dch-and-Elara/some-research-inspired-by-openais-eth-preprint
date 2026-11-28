import J6R24MeteredRecursionTermValue

/-! The checked strip on the high accumulator succeeds on the native
centre stream. The integer centre-keyed function below is proof-side
only; no centre lookup, per-term centre recomputation, or free jet
directory is part of the paid algorithm. -/
namespace J6R24MeteredRecursion
open scoped Polynomial
open Polynomial A1R10 A1R12 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R19Retained J6R22Active J6R23ScheduleWeight J6R21Ancestor HermiteLoss

theorem sum_raw_congr {A : Type*} {p ell : ℕ} {fw : List (Word p)} (hp : 0<p)
    (g h : A→Meter (UVBlock fw ell)) (xs : List A)
    (eq : ∀ x∈xs,(g x).result=(h x).result) :
    (sumM hp g xs).result=(sumM hp h xs).result := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have he := eq x List.mem_cons_self
    have ht := ih (fun u hu=>eq u (List.mem_cons_of_mem _ hu))
    simp only [sumM,addM,he,ht]

theorem sum_map_key {A B : Type*} {p ell : ℕ} {fw : List (Word p)} (hp : 0<p)
    (key : A→B) (g : B→Meter (UVBlock fw ell)) (xs : List A) :
    sumM hp (g ∘ key) xs=sumM hp g (xs.map key) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,sumM,Function.comp_apply,ih]

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell)) (hf : f.Monic)
variable [DecidableEq (Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "Sh" => (paddedShape (N sel) (Childs sel) r)
variable {c : Call (PhysicalHost f ell)}
variable (hc : NativeReach (Plan sel) r c)
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
local notation "Alev" => (Shape.levelBits S (Call.depth c))
local notation "Ulev" => (Shape.levelWidth S (Call.depth c))
variable {bank : Bank f}

def centreKey (t : Center S c) : ℤ×ℕ :=
  (t.val,order c.edges Ulev t.val)

include cfg hc in
set_option maxHeartbeats 7500000 in
theorem actual_active_decoded (hr : Stable s C r)
    (D : ActiveDesc sel d bank) (hp : 0<c.prec) (hv : 0<ell)
    (child : ActiveChild (sel:=sel) (d:=d) bank)
    (hChild : ∀ t z β g,(bank (registerPrecision S c t) (register_positive d t)).decode
      (child t z β g).result=(J6R12Blueprint.sourceBlueprint sel r hf).program.run
        ((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩)) :
    ∃ x, (D.finish hp hv hf child).result=some x ∧ (D.eval hp hv hf child).result=x ∧
      (bank c.prec hp).decode x=(J6R12Blueprint.sourceBlueprint sel r hf).program.run c := by
  classical
  let H := D.high hp
  let L := bank c.prec hp
  let B := D.extraPrecision
  let xs := D.centres.map (centreKey (s:=s) (c:=c))
  let actual (t : Center S c) (j : ℕ) : Meter (Block H ell) :=
    let jet := ((D.tape t).site hv (child t)).run Alev t.val
    (D.tape t).term hv hf H B jet.result j
  let term (t : ℤ) (j : ℕ) : Meter (Block H ell) :=
    if ht : t∈active Alev c.edges Ulev then actual ⟨t,ht⟩ j else zeroM H.hp
  have eKey (t : Center S c) : term t.val=actual t := by
    funext j
    exact dif_pos t.property
  let F := J6R12Integral.actualF sel d hf
  let J := J6R12Integral.actualJet sel d hf
  let out := c.host.contract hf
  have he : 0<f.natDegree := L.natDegree hf ▸ L.sizePos
  have taper := (J6R12Integral.printedGuards cfg sel r hr).taper c hc d.active
  have nd : (xs.map Prod.fst).Nodup := by
    change ((D.centres.map (centreKey (s:=s) (c:=c))).map Prod.fst).Nodup
    rw [List.map_map]
    exact D.centreUnique.map (fun _ _ h=>Subtype.ext h)
  have cv : (xs.map Prod.fst).toFinset=active Alev c.edges Ulev := by
    ext t
    rw [List.mem_toFinset]
    change t∈(D.centres.map (centreKey (s:=s) (c:=c))).map Prod.fst ↔ _
    rw [List.map_map,List.mem_map]
    exact ⟨fun ⟨τ,_,h⟩=>h ▸ τ.property,fun h=>⟨⟨t,h⟩,D.centreComplete _,rfl⟩⟩
  have co : ∀ t∈xs,t.2=order c.edges Ulev t.1 := by
    intro z hz
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hz
    rfl
  have hcRaw : (D.highRun hp hv hf child).result=(allTerms H.hp term xs).result := by
    let read := centreTerms H.hp term
    have hLocal (t : Center S c) :
        ((D.tape t).centre hv hf H B (child t)).result=(read (centreKey (s:=s) t)).result := by
      change (sumM H.hp (actual t) (List.range (order c.edges Ulev t.val))).result=
        (sumM H.hp (term t.val) (List.range (order c.edges Ulev t.val))).result
      rw [eKey]
    change (sumM H.hp (fun t=>(D.tape t).centre hv hf H B (child t)) D.centres).result=_
    rw [sum_raw_congr H.hp _ (read ∘ centreKey (s:=s) (c:=c)) _ (fun t _=>hLocal t),
      sum_map_key]
    rfl
  have hTerm (z : ℤ×ℕ) (hz : z∈xs) (j : ℕ) (hj : j<z.2) :
      H.decode (term z.1 j).result=
        J6R9Recursive.reduce (c.prec+B) f ell (localScalar f ell
          (scaledWeight Alev Ulev (sourceH c.edges Ulev) B j z.1)*
          approxJet Sh f ell c d.fit (sourceReplies sel r hf c) z.1 j) := by
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hz
    change H.decode (term t.val j).result=_
    rw [eKey]
    exact centre_scaled_term sel r hf hc d hv H (D.tape t) (child t) taper.1 taper.2
      D.enough hj (hChild t)
  have hHigh := (actual_active_high Sh hf he ell c d.fit B taper.1 taper.2 D.enough
    (sourceReplies sel r hf c) F (J6R12Integral.actualF_degree sel d hf)
    J (fun t ht=>J6R12Integral.actualJet_local sel d hf ⟨t,ht⟩)
    out (J6R12Integral.actualF_origin sel d hf)
    (source_parent_sample cfg sel r hf he hr hc d) H.hp H.exactMod xs nd cv co term hTerm).1
  have hHigh' : H.decode (D.highRun hp hv hf child).result=
      (2:Box f ell (c.prec+B))^B*J6R9Recursive.reduce (c.prec+B) f ell out := by
    rw [hcRaw]
    exact hHigh
  obtain ⟨x,hStrip,hRead,_⟩ := restore_native_box L.hp H.hp hf he hv H.exactMod L.exactMod
    (D.highRun hp hv hf child).result _ hHigh'
  have hFin : (D.finish hp hv hf child).result=some x := hStrip
  refine ⟨x,hFin,?_,?_⟩
  · simp only [ActiveDesc.eval,checkedWord,hFin]
  · have hInt : L.decode x=J6R9Recursive.reduce c.prec f ell out :=
      hRead.trans (lowerUV_reduction _ _ _ f ell out)
    have hSem : (J6R12Blueprint.sourceBlueprint sel r hf).program.run c=
        J6R9Recursive.reduce c.prec f ell out := by
      rw [source_active_value sel r hf d]
      exact assemble_exact Sh f hf he ell c d.fit taper.1 taper.2 F
        (J6R12Integral.actualF_degree sel d hf) J
        (fun t ht=>J6R12Integral.actualJet_local sel d hf ⟨t,ht⟩)
        out (J6R12Integral.actualF_origin sel d hf) _ (source_parent_sample cfg sel r hf he hr hc d)
    exact hInt.trans hSem.symm

#print axioms sum_raw_congr
#print axioms actual_active_decoded
end J6R24MeteredRecursion


