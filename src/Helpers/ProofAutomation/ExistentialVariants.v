(** * Additional support for evar-creating versions of tactics *)

(* safe version of repeat eexists (which will unfold definitions) *)
Ltac descend :=
  repeat match goal with
         | |- exists _, _ => eexists
         end.

Ltac especialize H :=
  match type of H with
  | forall (x:?T), _ =>
    let x := fresh x in
    evar (x:T);
    specialize (H x);
    subst x
  end.

Local Ltac _especialize H :=
  lazymatch type of H with
  | forall (x:?T), _ => let x := fresh x in
                  lazymatch type of T with
                  | Prop => unshelve (evar (x:T);
                        specialize (H x);
                        subst x)
                  | _ => evar (x:T);
                        specialize (H x);
                        subst x
                  end
  end.

Ltac epose_proof H :=
  let H' := fresh in
  pose proof H as H';
  repeat (_especialize H').
