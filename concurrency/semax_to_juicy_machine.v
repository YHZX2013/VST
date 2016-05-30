Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import msl.eq_dec.
Require Import veric.initial_world.
Require Import veric.juicy_mem.
Require Import veric.semax_prog.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.initial_world.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import concurrency.semax_conc.
Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.
Require Import semax_ext_oracle.

Ltac eassert :=
  let mp := fresh "mp" in
  pose (mp := fun {goal Q : Type} (x : goal) (y : goal -> Q) => y x);
  eapply mp; clear mp.

(* Instantiation of modules *)
Module ClightSEM <: Semantics.
  Definition G := genv.
  Definition C := corestate.
  Definition M := Mem.mem.
  Definition Sem := cl_core_sem.
End ClightSEM.

Module JuicyMachineShell_ClightSEM := Concur.JuicyMachineShell ClightSEM.
Module ListScheduler_NatTID := ListScheduler NatTID.
Module JuicyMachine:= CoarseMachine (ListScheduler_NatTID) (JuicyMachineShell_ClightSEM).

Definition join_list := JuicyMachineShell_ClightSEM.join_list.
Definition schedule := ListScheduler_NatTID.schedule.
Definition threads_and_lockpool := JuicyMachine.SIG.ThreadPool.t.
Module Machine := JuicyMachineShell_ClightSEM.ThreadPool.

Definition cm_state := (Mem.mem * genv * (schedule * threads_and_lockpool))%type.

(* Module JTP:=JuicyMachine.SIG.ThreadPool. *)

(* debugging *)
Axiom HOLE : forall {A}, A.
Open Scope string_scope.

(* before removing the resource invariant from the lock pool
Inductive cohere_res_lock : forall (resv : option (mpred * option rmap)) (wetv : resource) (dryv : memval), Prop :=
| cohere_notlock wetv dryv:
    (forall R, ~islock_pred R wetv) ->
    cohere_res_lock None wetv dryv
| cohere_locked R wetv :
    islock_pred R wetv ->
    cohere_res_lock (Some (R, None)) wetv (Byte (Integers.Byte.zero))
| cohere_unlocked R phi wetv :
    islock_pred R wetv ->
    R phi ->
    cohere_res_lock (Some (R, Some phi)) wetv (Byte (Integers.Byte.one)).
 *)

Inductive cohere_res_lock : forall (resv : option (option rmap)) (wetv : resource) (dryv : memval), Prop :=
| cohere_notlock wetv dryv:
    (forall R, ~islock_pred R wetv) ->
    cohere_res_lock None wetv dryv
| cohere_locked R wetv :
    islock_pred R wetv ->
    cohere_res_lock (Some None) wetv (Byte (Integers.Byte.zero))
| cohere_unlocked R phi wetv :
    islock_pred R wetv ->
    R phi ->
    cohere_res_lock (Some (Some phi)) wetv (Byte (Integers.Byte.one)).

Definition state_invariant {Z} (Jspec : juicy_ext_spec Z) (n : nat) (state : cm_state) : Prop :=
  match state with
  | (m, ge, (sch, Machine.mk nthds thds phis lockset as sss)) =>
    
    (* joinability condition *)
    (exists phi_all,
        JuicyMachineShell_ClightSEM.join_all sss phi_all
        /\
        
        (* coherence between locks (dry, wet, and lockset) *)
        (forall lock : Address.address,
            cohere_res_lock
              (@addressFiniteMap.AMap.find _ lock lockset)
              (phi_all @ lock)
              (contents_at m lock)))
    /\
    
    (* safety of each thread *)
    (forall i pr_i phi jmi (ora : Z),
        (* why is the i implicit?*)
        @Machine.getThreadR i sss pr_i = phi ->
        m_dry jmi = m ->
        m_phi jmi = phi ->
        match @Machine.getThreadC i sss pr_i with
        | Krun q
        | Kblocked q
        | Kresume q _ =>
          semax.jsafeN Jspec ge n ora q jmi
        | Kinit _ _ => True
        end)
    /\
    
    (* if one thread is running, it has to be the one being scheduled *)
    (* except if there is only one, then we don't require anything *)
    (lt 1 nthds.(pos.n) -> forall i pr_i q (ora : Z),
        @Machine.getThreadC i sss pr_i = Krun q ->
        exists sch', sch = i :: sch')
  end.

Lemma jsafeN_proof_irrelevance Z OK_spec prog oracle c jm jm' :
  m_dry jm = m_dry jm' ->
  m_phi jm = m_phi jm' ->
  @jsafeN Z OK_spec (globalenv prog) (level jm) oracle c jm ->
  @jsafeN Z OK_spec (globalenv prog) (level jm') oracle c jm'.
Admitted.

Section Initial_State.
  Variables
    (CS : compspecs) (V : varspecs) (G : funspecs)
    (ext_link : string -> ident) (prog : program) 
    (all_safe : semax_prog (Concurrent_Espec CS ext_link) prog V G)
    (init_mem_not_none : Genv.init_mem prog <> None).

  Definition Jspec := @OK_spec (Concurrent_Espec CS ext_link).
  
  Definition init_m : { m | Genv.init_mem prog = Some m } :=
    match Genv.init_mem prog as y return (y <> None -> {m : mem | y = Some m}) with
    | Some m => fun _ => exist _ m eq_refl
    | None => fun H => (fun Heq => False_rect _ (H Heq)) eq_refl
    end init_mem_not_none.
  
  Definition initial_state (n : nat) (sch : schedule) : cm_state :=
    (proj1_sig init_m,
     globalenv prog,
     (sch,
      let spr := semax_prog_rule
                   (Concurrent_Espec CS ext_link) V G prog
                   (proj1_sig init_m) all_safe (proj2_sig init_m) in
      let q : corestate := projT1 (projT2 spr) in
      let jm : juicy_mem := proj1_sig (snd (projT2 (projT2 spr)) n) in
      Machine.mk
        (pos.mkPos (le_n 1))
        (fun _ => Kresume q Vundef)
        (fun _ => m_phi jm)
        (addressFiniteMap.AMap.empty _)
     )
    ).
  
  Lemma initial_invariant n sch : state_invariant Jspec n (initial_state n sch).
  Proof.
    unfold initial_state.
    destruct init_m as [m Hm]; simpl proj1_sig; simpl proj2_sig.
    set (spr := semax_prog_rule (Concurrent_Espec CS ext_link) V G prog m all_safe Hm).
    set (q := projT1 (projT2 spr)).
    set (jm := proj1_sig (snd (projT2 (projT2 spr)) n)).
    
    split; [exists (m_phi jm);split | split].
    - (* joining condition *)
      admit.
    (* Questions:
      - why is emp better that "empty_rmap"? it requires "identity", but I thought we had no identity?
      - isn't core the corresponding neutral element? I can't find a lemma about that
     *)
    (* exists (empty_rmap n); split. *)
    (* destruct spr as (b' & q' & Hb & JS); simpl proj1_sig in *; simpl proj2_sig in *. *)
    (* unfold join. *)
    (* now admit (* join with empty_rmap -- doable *). *)
    (* now admit. *)
    
    - (* cohere_res_lock (there are no locks at first) *)
      intros lock.
      replace (
      addressFiniteMap.AMap.find (elt:=option rmap) lock
                                 (addressFiniteMap.AMap.empty (option rmap))
        ) with (@None (option rmap)) by admit.
      constructor.
      intros.
      unfold jm.
      match goal with |- context [proj1_sig ?x] => destruct x as (jm' & jmm & lev & S & notlock) end.
      intro.
      eapply notlock; eexists; eauto.
    
    - (* safety of the only thread *)
      intros i pr_i phi jmi ora Ephi.
      destruct (Machine.getThreadC pr_i) as [c|c|c v|v1 v2] eqn:Ec; try discriminate.
      intros Edry Ewet.
      destruct i as [ | [ | i ]]. 2: now inversion pr_i. 2:now inversion pr_i.
      simpl in Ephi, Ec.
      destruct spr as (b' & q' & Hb & JS); simpl proj1_sig in *; simpl proj2_sig in *.
      destruct (JS n) as (jm' & jmm & lev & S & notlock); simpl proj1_sig in *; simpl proj2_sig in *.
      subst.
      replace c with q in * by congruence.
      replace (level jm') with (level jmi).
      eapply jsafeN_proof_irrelevance; [ | | apply (S ora) ]; auto.
      { destruct jmi eqn:Ei, jm' eqn:E'.
        simpl; simpl in Ewet.
        congruence. }
      
    - (* only one thread running *)
      intros F; exfalso. simpl in F. omega.
  Admitted.

End Initial_State.

Section Simulation.
  Variables
    (CS : compspecs)
    (* (V : varspecs) (G : funspecs) *)
    (ext_link : string -> ident)
    (* (prog : program)  *)
    (* (all_safe : semax_prog (CEspec CS ext_link) prog V G) *)
    (* (init_mem_not_none : Genv.init_mem prog <> None) *)
  .

  Definition Jspec' := (@OK_spec (Concurrent_Espec CS ext_link)).

  Inductive state_step : cm_state -> cm_state -> Prop :=
  | state_step_empty_sched ge m jstate :
      state_step
        (m, ge, (nil, jstate))
        (m, ge, (nil, jstate))
  
  | state_step_bad_sched ge m i sch jstate :
      ~ Machine.containsThread jstate i ->
      state_step
        (m, ge, (i :: sch, jstate))
        (m, ge, (i :: sch, jstate))
  
  | state_step_internal
      ge m m' i sch jstate jstate'
      (contains_thread_i : Machine.containsThread jstate i)
      (mem_compat : JuicyMachineShell_ClightSEM.mem_compatible jstate m) :
      @JuicyMachineShell_ClightSEM.juicy_step
        ge i
        jstate m
        contains_thread_i
        mem_compat
        jstate' m' ->
      state_step
        (m, ge, (i :: sch, jstate))
        (m', ge, (i :: sch, jstate'))
  
  | state_step_concurrent
      ge m m' i sch jstate jstate'
      (contains_thread_i : Machine.containsThread jstate i)
      (mem_compat : JuicyMachineShell_ClightSEM.mem_compatible jstate m) :
      @JuicyMachineShell_ClightSEM.syncStep'
        ge i
        jstate m
        contains_thread_i
        mem_compat
        jstate' m' ->
      state_step
        (m, ge, (sch, jstate))
        (m', ge, (i :: sch, jstate'))
  .
  
  
  Require Import veric.semax_ext.
  
  Lemma state_invariant_step n :
    forall state,
      state_invariant Jspec' (S n) state ->
      exists state',
        state_step state state' /\
        state_invariant Jspec' n state'.
  Proof.
    intros ((m & ge) & sch & sss).
    destruct sss as (nthreads, thds, phis, lset) eqn:Esss.
    intros ((phi_all & J & lock_coh) & safe & single).
    rewrite <-Esss in *.
    destruct sch as [ | i sch ].
    
    (* empty schedule *)
    {
      exists (m, ge, (nil, sss)); subst; split.
      - constructor.
      - split; eauto.
        split; [ | now intuition ].
        intros i pr_i phi jmi ora E_phi di wi.
        eassert.
        + eapply safe; eauto.
        + destruct (Machine.getThreadC pr_i) as [c|c|c v|v1 v2] eqn:Ec; auto;
            intros Safe; eapply safe_downward1, Safe; auto.
    }
    
    destruct (i < nthreads.(pos.n)) eqn:Ei.
    
    (* bad schedule *)
    Focus 2.
    {
      exists (m, ge, (i :: sch, sss)); subst; split.
      - constructor. unfold Machine.containsThread; simpl. rewrite Ei. auto.
      - split; eauto.
        split; [ | now intuition ].
        intros j pr_j phi jmj ora E_phi di wi.
        eassert.
        + eapply safe; eauto.
        + destruct (Machine.getThreadC pr_j) as [c|c|c v|v1 v2] eqn:Ec; auto;
            intros Safe; eapply safe_downward1, Safe; auto.
    }
    Unfocus.
    
    (* the schedule selected one thread *)
    assert (pr_i : Machine.containsThread sss i).
    { rewrite Esss. apply Ei. }
    remember (Machine.getThreadC pr_i) as c_i eqn:Ec_i; symmetry in Ec_i.
    remember (Machine.getThreadR pr_i) as phi_i eqn:Ephi_i; symmetry in Ephi_i.
    
    (* several situations:
     - Krun (we should need the hypothesis that there is no other Krun)
       - at_ex
       - not at_ex
     - Klock
     - Kresume
     *)
    
    destruct c_i as [ c_i | c_i | c_i v | v1 v2 ].
    
    (* thread[i] is running *)
    {
      assert (Hjmi : exists jmi, m_dry jmi = m /\ m_phi jmi = phi_i).
      { admit (* "slice" lemma for juicy memory *). }
      
      (* get next state through "jsafeN" with: an arbitrary oracle and the next state *)
      destruct Hjmi as [jm_i [jm_i_m jm_i_phi_i]].
      pose proof (safe i pr_i phi_i jm_i (* oracle= *)nil ltac:(assumption)) as safe_i.
      rewrite Ec_i in safe_i.
      specialize (safe_i ltac:(assumption) ltac:(assumption)).
      
      destruct c_i as [ve te k | ef sig args lid ve te k] eqn:Heqc.
      
      (* thread[i] is running and some internal step *)
      {
        assert (next: exists c_i' jm_i',
                   corestep (juicy_core_sem cl_core_sem) ge c_i jm_i c_i' jm_i'
                   /\ forall ora, jsafeN Jspec' ge (S n) ora c_i' jm_i').
        {
          admit.
          (* there is this next state (use jsafeN) with trivial oracle *)
          (* the next state is safe for all oracle *)
        }
        
        destruct next as (c_i' & jm_i' & step_i & safe_i').
        pose (m' := m_dry jm_i' (* TODO update cur *)).
        pose (sss' := @Machine.updThread i sss pr_i (Krun c_i') (m_phi jm_i')).
        pose (state' := (m', ge, (i :: sch, sss'))).
        exists state'.
        split.
        - assert (mem_compat : JuicyMachineShell_ClightSEM.mem_compatible sss m).
          { admit. }
          apply state_step_internal with (contains_thread_i := pr_i) (mem_compat := mem_compat).
          apply JuicyMachineShell_ClightSEM.step_juicy with (c := c_i) (jm := jm_i) (c' := c_i') (jm' := jm_i').
          + admit (* mem_compat *).
          + admit (* mem coherence *).
          + congruence.
          + apply step_i.
          + reflexivity.
          + reflexivity.
        - split;[|split].
          + admit (* get phi_all from the mem_compat, too? *).
          + intros i0 pr_i0 q phi jmi ora.
            (* safety for all oracle : use the fact the oracle does not change after one step *)
            admit.
          + intros H i0 pr_i0 q ora H0.
            exists sch.
            (* use the fact that there is at most one Krun on the previous step and this step did not add any *)
            admit.
      }
      (* end of internal step *)
      
      (* thread[i] is running and about to call an external *)
      {
        unfold jsafeN, juicy_safety.safeN in safe_i.
        inversion safe_i.
        (* impossible case of the corestep from an ExtCall *)
        {
          subst.
          inversion H0.
          now inversion H.
        }
        
        (* interesting case of the at_external *)
        {
          subst.
          simpl in H0.
          simpl in x.
          revert x H1 H2.
          
          assert (ext_link_not_1 :
                    ext_link "acquire" <> 1%positive /\
                    ext_link "release" <> 1%positive /\
                    ext_link "makelock" <> 1%positive /\
                    ext_link "freelock" <> 1%positive /\
                    ext_link "spawn" <> 1%positive).
            by admit.
            
            destruct e;
              try solve [
                    intros x; exfalso; revert x;
                    repeat (match goal with
                            | |- context [ ident_eq ?a ?b ] => destruct (ident_eq a b)
                            end; try tauto) ].
            simpl ef_id.
            simpl (ext_spec_pre _).
            simpl (ext_spec_post _).
            unfold semax_ext_oracle.funspecOracle2pre.
            unfold semax_ext_oracle.funspecOracle2post.
            unfold ext_spec_pre, ext_spec_post.
            destruct (ident_eq (ext_link "acquire") (semax_ext_oracle.ef_id ext_link (EF_external name sg))).

            (* the case of acquire *)
            {
              intros (phi, (ora, p, sh, R)).
              admit.
              
              (* First:
                - integrate the oracle in the semax_conc definitions
                - sort out this dependent type problem
                Then hopefully we will be able to exploit the jsafeN_.
                
                Then, the proof should go as follows (it is not clear
                yet whether this happens now or if we set up things in
                the invariant /now/ and we deal with that in the
                Krunnable/Kblocked):
                
                - acquire (locked): nothing will happen (probably
                  happens after)
                
                - acquire (unlocked): the invariant guarantees that the
                  rmap in the lockset satisfies the invariant.  We can
                  give this rmap as a first step to the oracle.  We
                  again have to recover the fact that all oracles after
                  this step will be fine as well.  (Let's write
                  simulation lemmas about this, probably)
                 
                - release: this time, the jsafeN_ will explain how to
                  split the current rmap.
               *)
            }
            
            (* other cases (release, spawn, ...) ignored for now *)
            
            (* end of case analysis over [acquire; release; ...] *)
            {
              now intros [].
            }
        } (* end of:  at_external *)
        
        { (* case of halted *)
          match goal with
            [ H : halted _ _ = Some _ |- _ ] => inversion H
          end.
        } (* end of:  halted *)
      } (* thread[i] is running and at external *)
    } (* thread[i] is Krun *)

    (* thread[i] is in Kblocked *)
    {
      (* goes to Kres c_i' according to the rules of conc_step  *)
      admit.
    }
    (* thread[i] is in Kblocked *)
    
    (* thread[i] is in Kresume *)
    {
      (* goes to Krun c_i' according with after_ex c_i = c_i'  *)
      admit.
    }
    
    (* thread[i] is in Kinit *)
    {
      admit.
    }
  Admitted.
  
(* old pieces of proofs
  
      set (phis := (map snd thd ++ filter_option_list (map snd (map snd res)))%list).
      destruct (jm_slice phis i phi jm Hj) as (jmi & phi_jmi & dry_jmi).
      { apply nth_error_app_Some.
        rewrite list_map_nth, Heqthd_i.
        reflexivity. }
      assert (X: exists c' jmi', corestep (juicy_core_sem cl_core_sem) env (State ve te k) jmi c' jmi'). {
        specialize (safe _ _ _ tt Heqthd_i).
        inversion safe; subst.
        - (* we should state safety of each thread in this jmi, hence
        write the relationship between jm/jmi/phis/phi should have a
        external definition *)
          
          replace jmi with 
          - inversion H0.
        - inversion H.
      }
      destruct X as (c' & jm' & step & decay & lev).
      
      (* todo: make thd' the aged version of all rmaps *)
      pose (thd' := map (fun x : _ * rmap => let (c, phi) := x in (c, age1 phi)) thd).
      pose (res' := map (fun x : _ * (_ * option rmap) => match x with (a, (R, phi)) => (a, R, option_map age1 phi) end) res).


      (* ah, to build phi' we need to project m_phi jm' on phi -- where
    is the piece of information that says "an action from c is an
    action at phi" ?  ...............*)
      
      (* building the jm2 out of the jm and phi2 : state a lemma *)
      
      (* oracle : first, replace sig with ex.  Then, either define
    another definition of jsafe or use a dummy oracle and then say (∀Ω
    safe(Ω,c,m)) ∧ (c,m→c',m') → (∀Ω safe(Ω,c',m')) *)
      
      (* also MAX is for compcert to know we're not messing with e.g.
    constant propagation, and CUR is for the caller to know compcert
    is not writing in temporarily read-only variables sometimes *)
      
      (* todo the differences between interaction semantics and trace
    semantics *)
      
      (* build new state *)
      pose (thd'' := update_nth i (c', m_phi jm') thd').
      
      exists (build_cm env jm' res thd''), (i :: sch).
      split.
      - (* find jm, jmi, ..., then use safety to get one step from jsafe *)
      (* apply cm_step_internal with c c'.
      inversion step.
      + rewrite Heqthd_i, Heqc.
        inversion H.
        Require Import semax_congruence.
        unfold jsafeN, juicy_safety.safeN in Hsafe.
        pose proof (proj1 (safeN_step_jsem_spec _ _ _ _ _ _ _ _) Hsafe).
        apply (proj1 (safeN_step_jsem_spec _ _ _ _ _ _ _ _)) in Hsafe.
       destruct k as [ | [ s | s1 s2 | s1 s2 | | ret f e' te' ] ks].
       *)

(*    
Lemma safeN_step_jsem_spec: forall gx vx tx n k jm,
        (forall ora,
            @safeN_
              _ _ _ _ (fun x => Genv.genv_symb (genv_genv x)) juicy_safety.Hrel
              (juicy_core_sem cl_core_sem) OK_spec
              gx (S n) ora (State vx tx k) jm) ->
        exists c' m', (cl_step gx (State vx tx k) (m_dry jm) c' (m_dry m') /\
                  resource_decay (Mem.nextblock (m_dry jm)) (m_phi jm) (m_phi m') /\
                  level jm = S (level m') /\
                  forall ora,
                    @safeN_
                      _ _ _ _ (fun x => Genv.genv_symb (genv_genv x)) juicy_safety.Hrel
                      (juicy_core_sem cl_core_sem) OK_spec gx n ora c' m').
 *)
Admitted.
*)
End Simulation.