(** Election function used by the partition *)
Definition scheduler(N:nat)  : RT ((option nat)*bool) :=
  do p <- update_entries N ;
  update_counters N ;;
  ret p.

Definition update_entries(N : nat) : RT ((option nat)* bool) :=
  do new_jobs <- jobs_arriving N ; (* get all jobs arrving at current time, having id < N *)
  do finished <- job_terminating;  (* does a job finish at current time ? *)
  do expired <- job_expired;      (*is the job expired ? *)
  do late <- job_late ;(* did the job exceed its deadline ?*)             
  (if finished && (negb expired) then (* i remove its entry (NB the first one) from active list*)
    remove_first
  else
    ret tt)
  ;;

  insert_entries (* insert new entries generated from the new incoming jobs in the active list *)
    (map (fun j =>
          mk_Entry j (Jobs j).(budget) (S((Jobs j).(deadline)-(Jobs j).(arrival)))) 
         new_jobs) ;; 

  do r <- get_running ; (* obtain id of the running job (possibly none) from head of active list*)
  ret (r,late).
    (*  return the job id (if any) that has beed running, and whether or not the job was late   *)


Definition update_counters(N: nat) : RT unit :=
  decrease_cnt_first;; (* decrease cnt field of first entry corresponding to the running job*)
  remove_first_if_expired;; (* if field became 0 the budget's job is 0 : remove it from actve list *)
  decrease_all_del ;;
  inc_time_counter.