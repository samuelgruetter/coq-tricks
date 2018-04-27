
(* Parsing precedence between custom notations and semicolon *)

Tactic Notation "myrewrite" uconstr(c) "by" tactic(t) :=
   rewrite c by t.

Lemma foo: forall x, x = 2 -> 1 + 1 = x. intros. subst. reflexivity. Qed.

Goal False -> 1 + 1 + 1 = 2 + 2.
  intros.
  rewrite (foo 2) by reflexivity; exfalso.
  (* Goal is False, as expected *)
Abort.

Goal False -> 1 + 1 + 1 = 2 + 2.
  intros.
  myrewrite (foo 2) by reflexivity; exfalso.
  (* Surprise: Goal is "2 + 1 = 2 + 2", exfalso did not run, because it was parsed
     as part of the "by" clause.  *)
Abort.

Goal False -> 1 + 1 + 1 = 2 + 2.
  intros.
  (myrewrite (foo 2) by reflexivity); exfalso.
  (* Now the goal is False again, as expected, but how can I avoid the parentheses?  *)
Abort.

Tactic Notation "myrewrite3" uconstr(c) "by" tactic3(t) :=
   rewrite c by t.

Goal False -> 1 + 1 + 1 = 2 + 2.
  intros.
  myrewrite3 (foo 2) by reflexivity; exfalso.
  (* SUCCESS: Goal is False, as expected! *)
Abort.
