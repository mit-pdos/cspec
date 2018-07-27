Require Import Spec.ConcurExec.
Require Import Spec.Equiv.Execution.

Require Import ProofAutomation.
Require Import Helpers.Instances.
Require Import Morphisms.
Require Import List.

Section OpSemantics.

  Context {Op:Type -> Type}.
  Context {State:Type}.
  Variable op_step: OpSemantics Op State.

  Local Obligation Tactic := try RelInstance_t.

  (** A strong notion of equivalence for programs inside atomic sections.
    Basically the same as above, but defined as an underlying [atomic_exec]
    rather than [exec]. *)

  Local Definition atomic_equiv `(p1 : proc Op T) p2 :=
    forall (s s' : State) r tid evs,
      atomic_exec op_step p1 tid s r s' evs <->
      atomic_exec op_step p2 tid s r s' evs.

  Global Program Instance atomic_equiv_equivalence :
    Equivalence (@atomic_equiv T).

  Global Instance atomic_equiv_proper :
    Proper (atomic_equiv ==> atomic_equiv ==> iff) (@atomic_equiv T).
  Proof.
    typeclasses eauto.
  Qed.

  Theorem atomic_equiv_ret_bind : forall `(v : T) `(p : T -> proc Op T'),
      atomic_equiv (Bind (Ret v) p) (p v).
  Proof.
    split; intros.
    - atomic_exec_inv.
      invert H9.
    - rewrite <- app_nil_l.
      eauto.
  Qed.

  (* unused *)
  Local Theorem atomic_equiv_bind_ret : forall `(p : proc Op T),
      atomic_equiv (Bind p Ret) p.
  Proof.
    split; intros.
    - atomic_exec_inv.
      invert H10.
      rewrite app_nil_r.
      eauto.
    - rewrite <- app_nil_r.
      eauto.
  Qed.

  Local Theorem atomic_equiv_bind_bind : forall `(p1 : proc Op T1) `(p2 : T1 -> proc Op T2) `(p3 : T2 -> proc Op T3),
      atomic_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
  Proof.
    split; intros.
    - atomic_exec_inv.
      invert H9.
      rewrite <- app_assoc.
      eauto.
    - atomic_exec_inv.
      invert H10.
      rewrite app_assoc.
      eauto.
  Qed.

  Local Theorem atomic_equiv_bind_congruence : forall T (p1 p2: proc Op T) T' (rx1 rx2: T -> proc Op T'),
      atomic_equiv p1 p2 ->
      (forall x, atomic_equiv (rx1 x) (rx2 x)) ->
      atomic_equiv (Bind p1 rx1) (Bind p2 rx2).
  Proof.
    split; intros; atomic_exec_inv.
    - apply H in H11.
      apply H0 in H12.
      eauto.
    - apply H in H11.
      apply H0 in H12.
      eauto.
  Qed.

  Global Instance Bind_proper_atomic_equiv :
    Proper (atomic_equiv ==>
                         pointwise_relation T atomic_equiv ==>
                         @atomic_equiv TR) Bind.
  Proof.
    unfold Proper, respectful, pointwise_relation; intros.
    apply atomic_equiv_bind_congruence; auto.
  Qed.

  Global Instance Atomic_proper_atomic_equiv :
    Proper (atomic_equiv ==> exec_equiv_rx op_step (T:=T)) Atomic.
  Proof.
    intros.
    intros p1 p2 H.
    eapply exec_equiv_rx_proof_helper; intros;
      repeat exec_tid_inv.
    - apply H in H9.
      ExecPrefix tid tid'.
    - apply H in H9.
      ExecPrefix tid tid'.
  Qed.

End OpSemantics.
