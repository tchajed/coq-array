Require Import Array.Array.

From Coq Require Import List.
From Coq Require Import Omega.
Require Init.Nat.

From SimpleClasses Require Import Classes.
Import EqualDecNotation.

Set Implicit Arguments.

Section Array.
  Context (A:Type).
  Context {def: Default A}.
  Notation array := (list A).
  Implicit Types (l:array) (n:nat) (x:A).
  Notation assign := (Array.assign (A:=A)).

  Fixpoint massign l (ws: list (nat*A)) : array :=
    match ws with
    | nil => l
    | (n, v)::ws' => massign (assign l n v) ws'
    end.

  Fixpoint ws_lookup (ws: list (nat*A)) n : option A :=
    match ws with
    | nil => None
    | (n', v)::ws' => match ws_lookup ws' n with
                     | Some v' => Some v' (* prefer later writes *)
                     | None => if n == n' then Some v else None
                     end
    end.

  Theorem massign_not_in ws : forall l n,
      ws_lookup ws n = None ->
      index (massign l ws) n = index l n.
  Proof.
    induction ws; simpl; intros; auto.
    destruct a as [a v].
    destruct_with_eqn (ws_lookup ws n); try congruence.
    destruct (n == a); try congruence.
    erewrite IHws; eauto; array.
  Qed.

  Theorem length_massign ws : forall l,
      length (massign l ws) = length l.
  Proof.
    induction ws; simpl; intros; auto.
    destruct a.
    rewrite IHws; array.
  Qed.

  Hint Rewrite length_massign : length.

  Theorem massign_oob ws : forall l n,
      n >= length l ->
      index (massign l ws) n = None.
  Proof.
    induction ws; simpl; intros; array.
    destruct a.
    rewrite IHws; array.
  Qed.

  Theorem massign_in ws l n v :
    n < length l ->
    ws_lookup ws n = Some v ->
    index (massign l ws) n = Some v.
  Proof.
    generalize dependent v.
    generalize dependent n.
    generalize dependent l.
    induction ws; simpl; intros.
    - congruence.
    - destruct a as [a v'].
      destruct_with_eqn (ws_lookup ws n).
      inversion H0; subst; clear H0.
      erewrite IHws; eauto; array.
      destruct (n == a); subst; try congruence.
      inversion H0; subst; clear H0.
      rewrite massign_not_in by auto; array.
  Qed.

  Theorem massign_idempotent l ws :
    massign (massign l ws) ws = massign l ws.
  Proof.
    apply index_ext_eq; intros.
    destruct (index_dec l n); (intuition idtac).
    destruct_with_eqn (ws_lookup ws n).
    erewrite ?massign_in by (eauto; array); auto.
    rewrite ?massign_not_in by auto; auto.
    rewrite ?massign_oob by array; auto.
  Qed.

End Array.

Hint Rewrite length_massign : length.
Hint Rewrite massign_not_in using solve [ auto; congruence ] : array.
(* massign_in requires erewriting *)
