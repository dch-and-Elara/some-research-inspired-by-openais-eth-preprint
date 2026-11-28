import J6R33OriginalJ6Budget

/-! The nested centre/probe loops are the original list order:
one completed slot per pair, not one per group and not quadratic
many calls merely because interpolation rereads public nodes. -/
namespace J6R33OriginalJ6
open J6R22Active

theorem trace_nodup (m d : ℕ) : (requestTrace m d).Nodup := by
  unfold requestTrace
  apply List.nodup_flatMap.mpr
  refine ⟨fun i _=>(probeOrder_nodup (d+1)).map
    (fun x y eq=>congrArg Prod.snd eq),?_⟩
  apply List.Pairwise.imp _ (probeOrder_nodup (m+1))
  intro i k ne a ai ak
  obtain ⟨x,_,xe⟩ := List.mem_map.mp ai
  obtain ⟨y,_,ye⟩ := List.mem_map.mp ak
  exact ne (congrArg Prod.fst (xe.trans ye.symm))

theorem request_each_once (m d : ℕ) (i : Fin (m+1)) (j : Fin (d+1)) :
    (requestTrace m d).count (i,j)=1 := by
  have mem : (i,j)∈requestTrace m d :=
    List.mem_flatMap.mpr ⟨i,probeOrder_mem i,List.mem_map.mpr ⟨j,probeOrder_mem j,rfl⟩⟩
  rw [(trace_nodup m d).count,if_pos mem]

#print axioms trace_nodup
#print axioms request_each_once
end J6R33OriginalJ6
