import J6R15ModeCostEnum
import J6R15ModeCostDelay

/-! Output-sensitive exactness of the executable DFS, not merely a
positive-degree abstract range. A proof Run records the output words
only to state their meaning; the executable step does not keep them. -/
namespace J6R15ModeCost
open AOracleMachineTime

inductive Runs {q : ℕ} (n : ℕ) : State q → List (List ℕ) → State q → Prop where
  | done (s) : Runs n s [] s
  | quiet {s t u xs} : (step n s).result=.again t → Runs n t xs u → Runs n s xs u
  | emit {s t u ws xs} : (step n s).result=.emit ws t →
      Runs n t xs u → Runs n s (ws.map Word.val::xs) u

theorem Runs.concat {q n : ℕ} {s t u : State q} {xs ys : List (List ℕ)}
    (r : Runs n s xs t) (r' : Runs n t ys u) : Runs n s (xs++ys) u := by
  induction r with
  | done => exact r'
  | quiet h _ ih => exact .quiet h (ih r')
  | emit h _ ih => exact .emit h (ih r')

def writtenPrefix {q : ℕ} (fs : List (Frame q)) : List ℕ := (writeTuple fs).map Word.val

theorem writtenPrefix_push {q : ℕ} (f : Frame q) (fs : List (Frame q)) :
    writtenPrefix (f::fs)=writtenPrefix fs++[f.cursor.counter.val] := by
  simp [writtenPrefix,writeTuple]

def frameAt {q : ℕ} (w : Word q) (ws : List (Word q)) (c : Cursor q) : Frame q :=
  ⟨w,ws,c⟩

def branchOutput (pre ws : List ℕ) (w K j : ℕ) : List (List ℕ) :=
  (enumerate ws (K-w*j)).map (fun v => pre++j::v)

def tailOutput (pre ws : List ℕ) (w K j R : ℕ) : List (List ℕ) :=
  (List.range' j (R/w+1)).flatMap (branchOutput pre ws w K)

theorem div_sub_one (w r : ℕ) (hw : 0<w) (h : w≤r) :
    (r-w)/w+1=r/w := by
  have hr : w*1+(r-w)=r := by simp only [Nat.mul_one]; omega
  calc
    (r-w)/w+1 = (w*1+(r-w))/w := by rw [Nat.mul_add_div hw,Nat.add_comm]
    _ = r/w := by rw [hr]

theorem branchEmission {q : ℕ} (W : Word q) (ws : List (Word q)) (K : Word q)
    (fs : List (Frame q)) (c : Cursor q) (h : c.need W=K.val) :
    (enumerate (ws.map Word.val) c.rem.val).map
        (fun v => writtenPrefix (frameAt W ws c::fs)++v) =
      branchOutput (writtenPrefix fs) (ws.map Word.val) W.val K.val c.counter.val := by
  rw [writtenPrefix_push,branchOutput]
  have hc : K.val-W.val*c.counter.val=c.rem.val := by
    change W.val*c.counter.val+c.rem.val=K.val at h
    omega
  rw [hc]
  simp [List.append_assoc,frameAt]

theorem runSubtree_exact {q : ℕ} (hq : 0<q) (n : ℕ)
    (ws : List (Word q)) (hw : ∀ w∈ws,0<w.val)
    (K : Word q) (fs : List (Frame q)) :
    Runs n (.enter ws K fs)
      ((enumerate (ws.map Word.val) K.val).map (fun v => writtenPrefix fs++v))
      (.ascend fs) := by
  induction ws generalizing K fs with
  | nil =>
    simp only [List.map_nil,enumerate,List.map_cons,List.append_nil]
    exact .emit rfl (.done _)
  | cons W ws ih =>
    have hp : 0<W.val := hw W List.mem_cons_self
    have hs : ∀ w∈ws,0<w.val := fun w h => hw w (List.mem_cons_of_mem _ h)
    have siblings : ∀ r : ℕ, ∀ c : Cursor q, c.rem.val=r →
        c.need W=K.val →
        Runs n (.enter ws c.rem (frameAt W ws c::fs))
          (tailOutput (writtenPrefix fs) (ws.map Word.val) W.val K.val c.counter.val c.rem.val)
          (.ascend fs) := by
      intro r
      induction r using Nat.strong_induction_on with
      | h r ihR =>
        intro c hrc hc
        let F := frameAt W ws c
        have hB : c.need W<2^q := hc ▸ val_lt K
        obtain ⟨hN,hA⟩ := advance_exact hq W c hp hB
        have hChild := ih hs c.rem (F::fs)
        rw [branchEmission W ws K fs c hc] at hChild
        unfold tailOutput
        rw [List.range'_succ,List.flatMap_cons]
        apply hChild.concat
        have hN' : ((advance W c).result=none ↔ c.rem.val<W.val) := hN
        cases hm : (advance W c).result with
        | none =>
          have hr : c.rem.val/W.val=0 := Nat.div_eq_of_lt (hN'.mp hm)
          rw [hr,List.range'_zero,List.flatMap_nil]
          exact .quiet (by simp [step,F,frameAt,hm]) (.done _)
        | some c' =>
          obtain ⟨h1,h2,h3,h4⟩ := hA c' hm
          have hlt : c'.rem.val<r := hrc ▸ h4
          have hn : W.val≤c.rem.val := by
            apply Nat.le_of_not_gt
            intro H
            have J := hN'.mpr H
            rw [hm] at J
            contradiction
          have hd : c'.rem.val/W.val+1=c.rem.val/W.val := by
            rw [h2]
            exact div_sub_one _ _ hp hn
          have hNext := ihR c'.rem.val hlt c' rfl (h3.trans hc)
          rw [tailOutput,h1,hd] at hNext
          exact .quiet (by simp [step,F,frameAt,hm]) hNext
    let c : Cursor q := ⟨K,zeroWord q⟩
    have he : c.need W=K.val := by simp [c,Cursor.need,zeroWord_val]
    have r := siblings K.val c rfl he
    have hc0 : c.counter.val=0 := zeroWord_val q
    change Runs n (.enter ws K (frameAt W ws c::fs))
      (tailOutput (writtenPrefix fs) (ws.map Word.val) W.val K.val c.counter.val K.val)
      (.ascend fs) at r
    rw [tailOutput,hc0,← List.range_eq_range'] at r
    refine .quiet (by rfl) ?_
    simpa only [List.map_cons,enumerate,List.map_flatMap,List.map_map,branchOutput,Function.comp_def]
      using r

theorem stream_all_exact {q : ℕ} (hq : 0<q) (ws : List (Word q)) (p : Word q)
    (hp : ∀ w∈ws,0<w.val) :
    ((start ws p).result=.halt ↔ p.val=0) ∧
    (p.val≠0 → ∃ r : Word q,
      (start ws p).result=.again (.enter ws r []) ∧
      Runs ws.length (.enter ws r []) (strictTuples (ws.map Word.val) p.val) (.ascend [])) := by
  obtain ⟨⟨hs,hP⟩,_⟩ := start_exact hq ws p
  refine ⟨hs,?_⟩
  intro h
  obtain ⟨r,hR,hn⟩ := hP h
  refine ⟨r,hn,?_⟩
  have H := runSubtree_exact hq ws.length ws hp r []
  rw [strictTuples,if_neg h,← hR]
  simpa [writtenPrefix,writeTuple] using H

#print axioms Runs.concat
#print axioms div_sub_one
#print axioms runSubtree_exact
#print axioms stream_all_exact
end J6R15ModeCost


