Require Import POCS.
Require Import Lab1.VariablesAPI.


Definition read_count_spec : Specification _ _ unit _ :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      StateCount state' = StateCount state /\
      r = StateCount state;
    recovered := fun _ _ => False
  |}.

Definition write_count_spec val : Specification _ _ unit _ :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      r = tt /\ StateCount state' = val;
    recovered := fun _ _ => False
  |}.


Definition read_sum_spec : Specification _ _ unit _ :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      StateSum state' = StateSum state /\
      r = StateSum state;
    recovered := fun _ _ => False
  |}.

Definition write_sum_spec val : Specification _ _ unit _ :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      r = tt /\ StateSum state' = val;
    recovered := fun _ _ => False
  |}.


Axiom twopar : proc unit -> proc unit -> proc unit.

Definition twopar_spec S (p1spec p2spec : Specification _ _ unit S) : Specification _ _ unit S :=
  fun (_ : unit) state => {|
    pre := pre (p1spec tt state) /\ pre (p2spec tt state);
    post := fun r state' =>
      r = tt /\
      post (p1spec tt state) r state' /\
      post (p2spec tt state) r state';
    recovered := fun _ _ => False
  |}.

Axiom twopar_ok : forall S recover abstr (p1spec p2spec : Specification _ _ unit S) p1 p2,
  proc_spec p1spec p1 recover abstr ->
  proc_spec p2spec p2 recover abstr ->
  proc_spec (twopar_spec p1spec p2spec) (twopar p1 p2) recover abstr.

Hint Resolve twopar_ok.


Module Combine (v : VarsAPI).

  Definition recover := v.recover.
  Definition abstr := v.abstr.

  Definition read_count := r <- v.read VarCount; Ret r.
  Definition write_count val := _ <- v.write VarCount val; Ret tt.

  Theorem read_count_ok : proc_spec read_count_spec read_count recover abstr.
  Proof.
    unfold read_count.
    step_proc.
    step_proc.
  Qed.

  Theorem write_count_ok : forall val, proc_spec (write_count_spec val) (write_count val) recover abstr.
  Proof.
    unfold write_count.
    step_proc.
    step_proc.
  Qed.


  Definition read_sum := r <- v.read VarSum; Ret r.
  Definition write_sum val := _ <- v.write VarSum val; Ret tt.

  Theorem read_sum_ok : proc_spec read_sum_spec read_sum recover abstr.
  Proof.
    unfold read_sum.
    step_proc.
    step_proc.
  Qed.

  Theorem write_sum_ok : forall val, proc_spec (write_sum_spec val) (write_sum val) recover abstr.
  Proof.
    unfold write_sum.
    step_proc.
    step_proc.
  Qed.


  Hint Resolve read_count_ok.
  Hint Resolve write_count_ok.
  Hint Resolve read_sum_ok.
  Hint Resolve write_sum_ok.


  Definition p1 :=
    x <- read_count;
    _ <- write_count (x+1);
    Ret tt.

  Definition p2 :=
    y <- read_sum;
    _ <- write_sum (y+1);
    Ret tt.

  Definition example_prog :=
    twopar p1 p2.

  Definition p1_spec : Specification _ _ unit _ :=
    fun (_ : unit) state => {|
      pre := True;
      post := fun r state' =>
        r = tt /\
        StateCount state' = StateCount state + 1;
      recovered := fun _ _ => False
    |}.

  Definition p2_spec : Specification _ _ unit _ :=
    fun (_ : unit) state => {|
      pre := True;
      post := fun r state' =>
        r = tt /\
        StateSum state' = StateSum state + 1;
      recovered := fun _ _ => False
    |}.

  Theorem p1_ok : proc_spec p1_spec p1 recover abstr.
  Proof.
    unfold p1.
    step_proc.
    step_proc.
    step_proc.
  Qed.

  Theorem p2_ok : proc_spec p2_spec p2 recover abstr.
  Proof.
    unfold p2.
    step_proc.
    step_proc.
    step_proc.
  Qed.

  Definition example_spec : Specification _ _ unit _ :=
    fun (_ : unit) state => {|
      pre := True;
      post := fun r state' =>
        r = tt /\
        StateCount state' = StateCount state + 1 /\
        StateSum state' = StateSum state + 1;
      recovered := fun _ _ => False
    |}.

  Theorem example_ok : proc_spec example_spec example_prog recover abstr.
  Proof.
    unfold example_prog.
    eapply proc_spec_weaken.
    eapply twopar_ok.
    apply p1_ok.
    apply p2_ok.
    unfold spec_impl; simpl; intros.
    exists tt.
    intuition.
  Qed.

End Combine.
