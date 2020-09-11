Require Import Coq.PArith.BinPos.
Require Import Coq.Lists.List. Import ListNotations.

Set Universe Polymorphism.

Inductive option{A : Type}: Type :=
| Some(a: A)
| None.

Arguments option: clear implicits.

Section NATMAP.
  Context {V: Type}.

  (* TODO if there are trailing None's map extensionality doesn't hold, can we fix that? *)
  Definition natmap := list (option V).

  Definition head(m: natmap): option V :=
    match m with
    | nil => None
    | o :: _ => o
    end.

  Fixpoint skip(n: nat)(m: natmap): natmap :=
    match n with
    | O => m
    | S n' => tail (skip n' m)
    end.

  Definition get(m: natmap)(n: nat): option V := head (skip n m).

  (* m2 overrides m1. Simplifies best if m2 is concrete *)
  Fixpoint merge(m1 m2: natmap): natmap :=
    match m2 with
    | nil => m1
    | cons h t => cons (match h with
                        | Some v => Some v
                        | None => head m1
                        end)
                       (merge (tail m1) t)
    end.

  Fixpoint singleton(k: nat)(v: V): natmap :=
    match k with
    | O => Some v :: nil
    | S n => None :: singleton n v
    end.

  Definition put(m: natmap)(k: nat)(v: V): natmap := merge m (singleton k v).

  Definition putmany: natmap -> list (nat * V) -> natmap :=
    List.fold_right (fun '(k, v) res => put res k v).

End NATMAP.

Arguments natmap: clear implicits.

Section NATMAP_TESTS.
  Context (unknown: natmap nat).

  Goal get (Some 10 :: Some 11 :: None :: Some 13 :: unknown) 3 =
  Some 13.
  Proof. reflexivity. Qed.

  Goal merge (Some 10 :: Some 11 :: None :: Some 13 :: unknown)
       (Some 100 :: None :: Some 120 :: nil) =
  (Some 100 :: Some 11 :: Some 120 :: Some 13 :: unknown).
  Proof. reflexivity. Qed.

  Goal merge (Some 10 :: Some 11 :: unknown)
       (Some 100 :: None :: Some 120 :: None :: Some 140 :: nil) =
  (Some 100 :: Some 11 :: Some 120 :: get unknown 1 :: Some 140 :: skip 3 unknown).
  Proof. reflexivity. Qed.

  Goal put (put unknown 2 20) 5 50 = put (put unknown 5 50) 2 20.
  Proof. reflexivity. Qed.

  Goal putmany unknown [(3, 33); (1, 11); (4, 44)] = putmany unknown [(1, 11); (3, 33); (4, 44)].
  Proof. reflexivity. Qed.

End NATMAP_TESTS.

Definition forcetype(o: option Type): Type :=
  match o with
  | Some T => T
  | None => unit
  end.

Inductive hnatmap: natmap Type -> Type :=
| HNil: hnatmap nil
| HCons{OV: option Type}{T: natmap Type}(v: forcetype OV)(t: hnatmap T): hnatmap (cons OV T).

Definition hhead{T: natmap Type}(m: hnatmap T): forcetype (head T) :=
  match m with
  | HNil => tt
  | HCons v _ => v
  end.

Definition htail{T: natmap Type}(m: hnatmap T): hnatmap (tail T) :=
  match m with
  | HNil => HNil
  | HCons _ t => t
  end.

Fixpoint hskip(n: nat){T: natmap Type}(m: hnatmap T): hnatmap (skip n T) :=
  match n with
  | 0 => m
  | S n' => htail (hskip n' m)
  end.

Definition hget{T: natmap Type}(m: hnatmap T)(n: nat): forcetype (get T n) := hhead (hskip n m).

(* m2 overrides m1 *)
Fixpoint hmerge{T1 T2: natmap Type}(m1: hnatmap T1)(m2: hnatmap T2): hnatmap (merge T1 T2).
  refine (match m2 with
          | HNil => m1
          | @HCons OV T2Tail v t => @HCons (match OV with
                                            | Some V => Some V
                                            | None => head T1
                                            end)
                                           (merge (tail T1) T2Tail)
                                           _
                                           (hmerge _ _ (htail m1) t)
          end).
  destruct OV as [V|].
  - exact v.
  - exact (hhead m1).
Defined.

Fixpoint hsingleton{V: Type}(k: nat)(v: V){struct k}: hnatmap (singleton k V) :=
  match k with
  | 0 => @HCons (Some V) [] v HNil
  | S n => @HCons None (singleton n V) tt (hsingleton n v)
  end.

Definition hset(k: nat){V: Type}(v: V){T: natmap Type}(m: hnatmap T): hnatmap (put T k V) :=
  hmerge m (hsingleton k v).

Section HNATMAP_TESTS.
  Context (UnknownFields: natmap Type).
  Context (unknown: hnatmap UnknownFields).

  Goal hget (hset 2 true (hset 4 44 (hset 3 false (hset 4 (@nil nat) unknown)))) 4 = 44.
  Proof. reflexivity. Qed.

  Goal (hset 2 true (hset 4 44 unknown)) = (hset 4 44 (hset 2 true unknown)).
  Proof. reflexivity. Qed.

  Goal (hset 2 true (hset 4 44 (hset 3 false (hset 4 (@nil nat) unknown)))) =
       (hset 4 44 (hset 3 false (hset 2 true unknown))).
  Proof. reflexivity. Qed.
End HNATMAP_TESTS.

Definition commonVal := 4.

Module File1. Section __.
  Definition flag1 := 3.
  Context (UnknownFields: natmap Type).
  Definition Fields: natmap Type := putmany UnknownFields [(flag1, bool: Type); (commonVal, nat: Type)].
  Definition State: Type := hnatmap Fields.

  Definition op(s: State): State := hset commonVal (hget s commonVal + 2) (hset flag1 false s).
End __. End File1.

Module File2. Section __.
  Definition flag2 := 0.
  Context (UnknownFields: natmap Type).
  Definition Fields: natmap Type := putmany UnknownFields [(flag2, bool: Type); (commonVal, nat: Type)].
  Definition State: Type := hnatmap Fields.

  Definition op(s: State): State := hset flag2 true (hset commonVal (hget s commonVal + 3) (hset flag2 false s)).
End __. End File2.

Module File3. Section __.
  Context (UnknownFields: natmap Type).
  Definition Fields: natmap Type :=
    putmany UnknownFields [
              (File1.flag1, bool: Type);
              (File2.flag2, bool: Type);
              (commonVal, nat: Type)
            ].
  Definition State: Type := hnatmap Fields.

  Goal File1.State (putmany UnknownFields [(File2.flag2, bool: Type)]) = State.
  Proof. reflexivity. Qed.

  Definition op1: State -> State :=
    File1.op (putmany UnknownFields [(File2.flag2, bool: Type)]).

  Definition op2: State -> State :=
    File2.op (putmany UnknownFields [(File1.flag1, bool: Type)]).

  Goal forall s: State,
      hget (op1 (op2 s)) commonVal = hget s commonVal + 5.
  Proof.
    intros.
    unfold op1, op2, File1.op, File2.op, hget, hset.
    simpl.
    rewrite <- PeanoNat.Nat.add_assoc.
    reflexivity.
  Qed.
End __. End File3.
