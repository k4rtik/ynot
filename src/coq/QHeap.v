(* Copyright (c) 2008, Harvard University
 * All rights reserved.
 *
 * Author: Adam Chlipala
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - The names of contributors may not be used to endorse or promote products
 *   derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

Require Import Ynot.Axioms.

Set Implicit Arguments.

Axiom axiom_qbit : Set.

Definition qbit := axiom_qbit.

Axiom axiom_qbit_eq_dec : forall (a b : qbit), {a = b} + {a <> b}.

Definition qbit_eq_dec := axiom_qbit_eq_dec.
(** Definition qbit := nat. ** possible, like in QIO **)

Definition qheap := qbit -> option dynamic. (* should be a boolean perhaps *)

Declare Scope qheap_scope.
Bind Scope qheap_scope with qheap.
Delimit Scope qheap_scope with qheap.

Local Open Scope qheap_scope.

Definition empty : qheap := fun _ => None. (* or "initial" heap *)
Definition singleton (q : qbit) (v : dynamic) : qheap :=
  fun q' => if qbit_eq_dec q' q then Some v else None.
Definition lookup (h : qheap) (q : qbit) : option dynamic := h q.
Definition update (h : qheap) (q : qbit) (v : dynamic) : qheap :=
  fun q' => if qbit_eq_dec q' q then Some v else h q'.
Definition forget (h : qheap) (q : qbit) : qheap :=
  fun q' => if qbit_eq_dec q' q then None else h q'.

Infix "|-->" := singleton (at level 35, no associativity) : qheap_scope.
Notation "a # b" := (lookup a b) (at level 55, no associativity) : qheap_scope.
Notation "h ## q <- v" := (update h q v) (no associativity, at level 60, q at next level) : qheap_scope.
Infix "###" := forget (no associativity, at level 60) : qheap_scope.

Definition join (h1 h2 : qheap) : qheap :=
  (fun q => match h1 q with
         | None => h2 q
         | v => v
         end).

Infix "*" := join (at level 40, left associativity) : qheap_scope.


(** * Theorems *)

Theorem join_id1 : forall h, empty * h = h.
  intros.
  unfold qheap; ext_eq.
  trivial.
Qed.

Theorem join_id2 : forall h, h * empty = h.
  intros.
  unfold qheap; ext_eq.
  unfold join.
  destruct (h x); trivial.
Qed.

Hint Resolve join_id1 join_id2 : Ynot.
Hint Rewrite join_id1 join_id2 : Ynot.

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ => idtac
  end.


Theorem lookup_empty : forall p,
  empty # p = None.
  trivial.
Qed.

Theorem lookup_singleton_same : forall q v,
  (q |--> v) # q = Some v.
  unfold lookup, singleton; intros.
  destruct (qbit_eq_dec q q); tauto.
Qed.

Theorem lookup_singleton_diff : forall q v q',
  q' <> q
  -> (q |--> v) # q' = None.
  unfold lookup, singleton; intros.
  destruct (qbit_eq_dec q' q); tauto.
Qed.

Theorem lookup_update_same : forall h q v,
  (h ## q <- v) # q = Some v.
  unfold lookup, update; intros.
  destruct (qbit_eq_dec q q); tauto.
Qed.

Theorem lookup_update_diff : forall h q v q',
  q' <> q
  -> (h ## q <- v) # q' = h # q'.
  unfold lookup, update; intros.
  destruct (qbit_eq_dec q' q); tauto.
Qed.

Hint Rewrite lookup_empty lookup_singleton_same lookup_update_same : Ynot.
Hint Rewrite lookup_singleton_diff lookup_update_diff using (auto; fail) : Ynot.

Hint Extern 1 (_ # _ = _) => autorewrite with Ynot in * : Ynot.
