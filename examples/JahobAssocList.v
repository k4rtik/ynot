
Module Type NONDEP_ASSOCIATION.
  (* This is weaker than the real ynot finite map because the
     type of a value does not depend on its key.
     However, it corresponds to Jahob when V := ptr. *) 
  Variables K V : Set.
  Variable  eqK : forall (k1 k2: K), {k1 = k2} + {k1 <> k2}.
End NONDEP_ASSOCIATION.

Module NondepAssocListModel(A : NONDEP_ASSOCIATION).
 Export A.
 Require Export List.
 Set Implicit Arguments.

 (* This model is slightly different from Jahob's model
    using sets.  We expose lists, but with the with unique 
    keys invariant, these operations can implement
    the same list mutations that Jahob gets using set deletion 
    and union. *)  

 Fixpoint update l (k: K) (v: V)             :=  match l with  | nil => nil
   | (k', v')::b => if eqK k k'  then (k, v) :: b else (k', v') :: update b k v end.

 Fixpoint delete (l: list (prod K V)) (k: K) :=  match l with  | nil => nil
   | (k', v')::b => if eqK k k'  then delete b k  else (k',v') :: (delete b k)  end.

 Fixpoint insert l (k: K) (v: V)             :=  match l with  | nil => (k, v)::nil
   | (k', v')::b => if eqK k k'  then (k, v) :: b else (k', v') :: insert b k v end.

 Fixpoint lookup l (k: K) : option V         :=  match l with  | nil => None
  | (k', v)::b   => if eqK k k'  then Some v      else lookup b k               end.

 Definition head (ls : list (prod K V)) := match ls with | nil => None | x :: _ => Some x end.

 Definition tail (ls : list (prod K V)) := match ls with | nil => nil  | _ :: ls' => ls'  end.

End NondepAssocListModel.

(* This is the interface for the Jahob AssocList example,
   as expressed in Y0. *)
Module Type JAHOB_ASSOC_LIST.
 Require Export List.
 Declare Module A  : NONDEP_ASSOCIATION.
 Module AL := NondepAssocListModel(A).
 Import AL.

 Require Export Ynot.
 Open Scope hprop_scope.

 Parameter t   : Set.
 Parameter rep : t -> list (prod K V) -> hprop.

 Parameter new : STsep __ (fun r => rep r nil).
 Parameter free: forall (p: t),
   STsep (rep p nil) (fun _: unit => __).

 Parameter containsKey: forall k (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m)
         (fun r:bool => m ~~ rep p m * if r then Exists v :@ V, [In (k,v) m] 
                                            else [lookup m k = None]).
 Parameter add: forall k v (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m * [lookup m k = None])
         (fun _:unit => m ~~ rep p ((k,v)::m)).

 Parameter put: forall k v (p: t) (m: [list (prod K V)]), 
   STsep (m ~~ rep p m)
         (fun r => m ~~ [r = lookup m k] * rep p (insert m k v)).

 Parameter get: forall k   (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m)
         (fun r:option V => m ~~ rep p m * [r = lookup m k] ).

(* todo [~ Exists v @: V, In m (k, v) (maybe switch to forall v, ~ In k v ? *)

 Parameter isEmpty: forall (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m) (fun r:bool => m ~~ rep p m * if r then [m = nil] else [m <> nil]).

 Parameter remove : forall k (p: t) (m: [list (prod K V)]),
                     STsep (m ~~ rep p m * Exists v :@ V, [lookup m k = Some v]) 
                (fun r:V => m ~~ rep p (delete m k) *     [lookup m k = Some r]).

 Parameter replace: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~             rep p m * Exists v0 :@ V, [lookup m k = Some v0]   )
        (fun r:V => m ~~  rep p m *                 [lookup m k = Some r ] * rep p ((k,v)::(delete m k))).

(* todo: classical logic -> proof irrelevence -> inconsistency *)

(* technically want rep -> uniq lemma *)

End JAHOB_ASSOC_LIST.

(* This uses the same implementation code as Jahob *)
Module JahobAssocList(A : NONDEP_ASSOCIATION) : JAHOB_ASSOC_LIST with Module A := A.
 Module A := A.
 Module AL := NondepAssocListModel(A).
 Require Import Ynot.
 Import AL.

 Open Scope hprop_scope.

(* Representation ***********************************************)

  Definition t : Set := ptr.
 
  Record Node : Set := node {
    key  : K;
    value: V;
    next : option ptr
  }.

  Fixpoint rep' (op: option ptr) m {struct m} :=
    match op with
      | None => [m = nil] 
      | Some h => match m with
                    | (k,v) :: b =>  Exists nxt :@ option ptr,
                          h --> node k v nxt * rep' nxt b * [lookup b k = None]
                    | nil => [False]
                   end
    end.

  Definition rep p m : hprop :=
    Exists n :@ option ptr, p --> n * rep' n m.

(* Reasoning **************************************************)

Ltac simplr := repeat (try discriminate;
  match goal with
    | [ H : head ?x = Some _ |- _ ] =>
      destruct x; simpl in *; [
        discriminate
        | injection H; clear H; intros; subst
      ]
    | [ |- match ?v with
             | Some _ => _
             | None   => _
           end ==> _] => destruct v
    | [ H : _ :: _ = _ :: _ |- _ ] => injection H; clear H; intros; subst
    | [ H : next _ = _ |- _ ] => rewrite -> H
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    | [  H : ?a = ?b -> False , HH : (if (eqK ?a ?b) then Some _ else None) = Some _  |- _ ] => destruct (eqK a b) ; [ contradiction | discriminate ] 
    | [  HH : (if (eqK ?a ?b) then Some _ else _) = None  |- _ ] => destruct (eqK a b) ; [ discriminate | idtac ]
    | [  H : ?a = ?b -> False , HH : (if (eqK ?a ?b) then Some _ else Some ?v1) = Some ?v  |- context[Some ?v1 = Some ?v] ] => 
           destruct (eqK a b) ; [ try congruence | try contradiction ] 
    | [ _ : ?a = ?b -> False ,  HH : (if (eqK ?a ?b) then _ else ?c) = ?d  |- _ ] => destruct (eqK a b) ; [ contradiction | idtac ]
    | [ |- context[ if eqK ?a ?a then _ else _ ] ] => destruct (eqK a a) 
    | [ H : ?a = ?b -> False |- context[ if eqK ?a ?b then _ else _ ] ] => destruct (eqK a b); [ contradiction | idtac ] 
    | [  H : next ?nn = ?a |- ?n = node (key ?nn) (value ?nn) ?a ] => rewrite <- H; destruct n; reflexivity
    | [ _ : (if eqK ?a ?b then Some _ else None) = Some _ |- _ ] => destruct (eqK a b); [ idtac | discriminate ] 
    | [ _ : (if eqK ?a ?a then _ else _) = _ |- _ ] => destruct (eqK a a); [ idtac | intuition ] 
  (*  | [ |- context[ if (eqK ?v1 ?v2) then _ else _ ] ] => destruct (eqK v1 v2) *)
  end).

Ltac t := unfold rep; unfold rep'; sep fail simplr.
Ltac f := fold rep'; fold rep.

Lemma eta_node : forall fn, fn = node (key fn) (value fn) (next fn).
  destruct fn; reflexivity.
Qed.

Hint Resolve eta_node.

Lemma ll_concat : forall nde a b c hd, Some (key nde, value nde) = head a ->
  rep' (next nde) (tail a ++ b :: c) * hd --> nde * [lookup (tail a ++ b :: c) (key nde) = None] ==> rep' (Some hd) (a ++ b :: c)  .
  induction a; t.
Qed.

Hint Resolve ll_concat.
Lemma cons_nil : forall l2 x0 x, rep' l2 x0 * rep' None x ==> rep' l2 (x ++ x0).
  destruct x; t.
Qed.
Lemma node_next : forall nde p,  next nde = p -> nde = node (key nde) (value nde) p.
  destruct nde; simpl; congruence.
Qed.

Hint Resolve cons_nil.
Hint Resolve node_next.

Lemma lkup: forall m k x, 
 lookup m x = None -> lookup (delete m k) x = None.
  intros. induction m. trivial. simpl in *. destruct a. destruct (eqK x k0). discriminate. destruct (eqK k k0). apply IHm. assumption.
   induction m. t. t. Qed.

(* Hint Resolve lkup. *)

Theorem rep'_None : forall ls,
  rep' None ls ==> [ls = nil].
  destruct ls; sep fail idtac.
Qed.

Theorem rep'_Some : forall ls hd,
  rep' (Some hd) ls ==> Exists k :@ K, Exists v :@ V, Exists t :@ list (prod K V), Exists p :@ option ptr,
  [ls = (k,v) :: t] * hd --> node k v p * [lookup t k = None] * rep' p t.
  destruct ls; sep fail ltac:(try discriminate).
Qed.

Lemma node_eta : forall fn k v x,
  [fn = node k v x] ==> [key fn = k] * [value fn = v] * [next fn = x].
  destruct fn; sep fail ltac:(try congruence).
Qed.

Lemma cons_eta : forall x h t,
  [x = h :: t] ==> [head x = Some h] * [tail x = t].
  destruct x; sep fail ltac:(try congruence).
Qed.

Lemma rep'_eq : forall m x v0 v1 x0 fn,
  m = [x]%inhabited
  -> (m ~~~ tail m) = [x0]%inhabited
  -> tail x = v0
  -> next fn = v1
  -> rep' v1 v0 ==> rep' (next fn) x0.
  t.
Qed.

Hint Resolve rep'_eq.

Theorem rep_rep' : forall m p, rep p m ==>
  Exists n :@ option ptr, p --> n * rep' n m. t. Qed.

Hint Resolve rep_rep'.

Ltac simp_prem :=
  simpl_IfNull;
  repeat simpl_prem ltac:(apply rep'_None || apply rep'_Some || apply node_eta || apply cons_eta || apply rep_rep');
    unpack_conc.

Ltac destr := match goal with [ x : list (prod K V) |- context[rep' None ?x] ] => destruct x; try t end.

Ltac t'' := unfold rep; fold rep'; sep simp_prem simplr.

Ltac t' := match goal with
             | [ |- _ ==> ?P ] =>
               match P with
                 | context[rep' (next _) _] =>
                   inhabiter; simp_prem;
                   intro_pure; simpl_prem ltac:(solve [ eauto ]); unintro_pure; canceler; t''
               end
             | _ => t''
           end.

(* Implementation ***************************************************)

  Open Scope stsepi_scope.

  Definition new : STsep __ (fun r => rep r nil).
    refine {{ New (@None ptr) }}; t. Qed.

  Definition free  p: STsep (rep p nil) (fun _:unit => __).
  intros; refine {{ Free p }}; t. Qed.   

  (* This is get duplicated, so I'm going to defer until get is nicer *)
  Parameter containsKey: forall k (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m)
         (fun r:bool => m ~~ rep p m * if r then Exists v :@ V, [In (k,v) m] 
                                            else [lookup m k = None]).

  Definition add: forall k v (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m * [lookup m k = None])
         (fun _:unit => m ~~ rep p ((k,v)::m)).
   intros. refine ( op <- ! p ;
                    n  <- New (node k v op) ;
                    {{ p ::= (Some n) }} ); t. Qed.

 (* Put           *********)

 Parameter put: forall k v (p: t) (m: [list (prod K V)]), 
   STsep (m ~~ rep p m)
         (fun r => m ~~ [r = lookup m k] * rep p (insert m k v)).

 (* Get           **********)

 Definition get' (k: K) (hd: option ptr) (m: [list (prod K V)]):
    STsep (m ~~ rep' hd m) (fun r => m ~~ [r = lookup m k] * rep' hd m).
  intro k.
  refine (Fix2
    (fun hd m => m ~~ rep' hd m)
    (fun hd m o => m ~~ [o = lookup m k] * rep' hd m)
    (fun self hd m =>  
      IfNull hd
      Then  {{ Return None }}
      Else  fn <- ! hd ;
            if eqK k (key fn) 
            then {{ Return (Some (value fn)) }} 
            else {{ self (next fn) (m ~~~ tail m) <@> _ }})); t'. Qed. 

  Definition get (k: K) (p: ptr) (m: [list (prod K V)]) :
    STsep (m ~~ rep p m)
          (fun r:option V => m ~~ rep p m * [r = lookup m k] ).
  intros; refine (hd <- !p;
                  Assert (p --> hd * (m ~~ rep' hd m));;
                  {{get' k hd m <@> _}}); t. Qed.

 (* isEmpty         ********)

 Definition isEmpty: forall (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m) (fun r:bool => m ~~ rep p m * if r then [m = nil] else [m <> nil]).
   intros; refine ( ohd <- SepRead p (fun ohd => m ~~ rep' ohd m) ;
                    IfNull ohd 
                    Then  {{ Return true  }}
                    Else  {{ Return false }} ); t'. Qed.

 (* Remove         *********)


Definition remove_pre k v prev ls := 
(Exists pk :@ K, Exists pv :@ V, Exists ck :@ K, Exists cv :@ V,  Exists t :@ list (prod K V), Exists cur :@ ptr, Exists nxt :@ option ptr,
 [lookup t pk = None] * [ls = (pk,pv) :: (ck, cv) :: t] * [pk <> k] * [pk <> ck] * [lookup t ck = None] *
 prev --> node pk pv (Some cur) * cur --> node ck cv nxt  * rep' nxt t * [lookup ((ck, cv)::t) k = Some v]).

Definition remove_post k v prev ls :=
(fun r:V => Exists pk :@ K, Exists pv :@ V, Exists x :@ list (prod K V), 
          [ls = (pk,pv) :: x] * rep' (Some prev) ((pk,pv)::(delete x k)) * [r = v]).

Definition remove'' k v (prev: ptr) (ls: list (prod K V)) : 
   STsep (remove_pre k v prev ls)
         (remove_post k v prev ls).             
intros k v. refine (Fix2 (remove_pre k v) (remove_post k v) 
 (fun self prev ls =>        
   pn <- ! prev ;
   IfNull (next pn) As cur
   Then {{ !!! }}
   Else n <- SepRead cur (fun n => Exists t :@ list (prod K V), [key pn <> k] * [lookup t (key pn) = None] * [next pn = Some cur] *
                [ls = (key pn, value pn) :: (key n, value n) :: t] * [key pn <> key n] * [lookup t (key n) = None] *
                 prev --> node (key pn) (value pn) (Some cur) * rep' (next n) t * [lookup ((key n, value n)::t) k = Some v]) ;  
         if eqK k (key n)  
         then Free cur ;;
              prev ::= node (key pn) (value pn) (next n) ;;  
              {{ Return (value n) }}
         else IfNull (next n) As nt 
        Then  {{ !!! }} 
        Else {{ self cur (tail ls) <@>  ( Exists t :@ list (prod K V), [lookup t (key pn) = None] * 
                                          [ls = (key pn, value pn) :: (key n, value n) :: t] *
                                         [key pn <> key n] * prev --> node (key pn) (value pn) (Some cur) ) }} )); 
unfold remove_pre; unfold remove_post; try solve [ pose lkup; t | t' ]. Admitted.

 Definition remove' : forall k v (p: t) (m: list (prod K V)),
                     STsep (                        [lookup m k = Some v] * rep p m) 
                         (fun r:V =>                [lookup m k = Some r] * rep p (delete m k)).
 intros. refine ( 
  hdptr <- ! p ;
  IfNull hdptr 
  Then {{ !!! }} 
  Else hd <- SepRead hdptr  (fun hd => Exists tl :@ list (prod K V), p --> Some hdptr * [lookup m k = Some v] *
                                      [m = (key hd, value hd)::tl] * rep' (next hd) tl * [lookup tl (key hd) = None])  ;
          if eqK k (key hd)
          then Free hdptr ;;
               p ::= next hd ;; 
               {{ Return (value hd) }}
          else IfNull (next hd) As nt 
               Then {{ !!! }}
               Else {{ remove'' k v hdptr m <@>  (Exists ck :@ K, Exists cv :@ V, Exists t :@ list (prod K V), 
                                                  [m = (key hd, value hd)::(ck, cv)::t] *  
                                                  p --> Some hdptr *  [lookup m k = Some v] )   }}                            
  ); unfold remove_pre; unfold remove_post; try solve [ t | t' ]. t'. Admitted.

 Definition remove : forall k (p: t) (m: [list (prod K V)]),
                     STsep (m ~~ rep p m * Exists v :@ V, [lookup m k = Some v]) 
                (fun r:V => m ~~ rep p (delete m k) *     [lookup m k = Some r]). Admitted.

 (* Replace        **********)


 Definition replace: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~             rep p m * Exists v0 :@ V, [lookup m k = Some v0]   )
        (fun r:V => m ~~  rep p m *                 [lookup m k = Some r ] * rep p ((k,v)::(delete m k))).
 intros. refine ( Assert (m ~~ rep p m * Exists v0 :@ V, [lookup m k = Some v0]) ;;
                  x <- remove k p m ;
                  Assert (m ~~ rep p (delete m k) * [lookup (delete m k) k = None] * [lookup m k = Some x] ) ;;
                  add k v p m ;;
                  Assert (m ~~ rep p ((k,v)::delete m k) * [lookup (delete m k) k = None] * [lookup m k = Some x]) ;;
                  {{ Return x }} ). Admitted. (*  sep fail auto. instantiate (1 := v0). t. t.
instantiate (1:=v2). t. t. instantiate (1:= v1). t. t. pose lkup. t. 
 t'. destruct x0. t. t. destruct p0. t. t 
 hdestruct m. t. destruct (lookup m k). t. t. t. sep fail auto.  Set Printing All.

 Parameter add: forall k v (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m * [lookup m k = None])
         (fun _:unit => m ~~ rep p ((k,v)::m)). *)


(* todo switch to [ ] types in remove *)

(* ******************************************************************************************************************************************* *)


(* Equivalence to Jahob interface *)

  Definition add0: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep p m * [forall v0, ~ In (k,v0) m])
        (fun _:unit => m ~~ rep p ((k,v)::m)). Admitted. (*
  intros. refine ( {{ add k v p m }}). hdestruct m. t. sep fail auto.
   destruct (eqK k a). pose (H b). destruct f. subst. left. reflexivity.
                       induction m. t. destruct a0. simpl. destruct (eqK k k0).
   subst. pose (H v0). destruct f. right. simpl. left. reflexivity. apply (IHm).
    intros. destruct H0. assert (a = k). congruence. subst. elim n. reflexivity.
    pose (H v1). destruct f. right. simpl. right. assumption. t. Qed. *)

  Definition get0: forall k   (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m)
         (fun r => m ~~ rep p m * match r with
                                    | None => [lookup m k = None]
                                    | Some v => [In (k, v) m]
                                  end). Admitted.
  (* intros; refine ( {{ get k p m }} ); try solve [ t | intro v; destruct v; pose lkup; t ]. t. Qed.  *)

 Parameter remove0: forall k (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep p m * Exists v :@ V, [In (k,v) m])
        (fun r:V => m ~~ [In (k, r) m] * rep p (delete m k)).
  (* need to get witness *)

 Parameter containsKey0: forall k (p: t) (m: [list (prod K V)]),
   STsep (m ~~ rep p m)
         (fun r:bool => m ~~ rep p m * if r then Exists v :@ V, [In (k,v) m] 
                                            else [lookup m k = None]).
 (* todo: ~ Exists v, In (k,v) m] *)

 Parameter replace0: forall k v (p: t) (m: [list (prod K V)]),
  STsep (m ~~ rep p m * Exists v0 :@ V, [In (k,v0) m] )
        (fun r:V => m ~~ [In (k, r) m] * rep p ((k,v)::(delete m k))).

(* todo [~ Exists v @: V, In m (k, v) (maybe switch to forall v, ~ In k v ? *)

(* todo: classical logic -> proof irrelevence -> inconsistency *)

(* technically want rep -> uniq lemma *)

 (* The Jahob put operation traverses the list several times.  
    This implements a faster, in-place put that isn't found in Jahob. *)
(* This hasn't been updated for the uniqueness part of the invariant 
 Definition putFast' (k: K) (v: V) (hdptr: ptr) (m: [list (prod K V)]) :
  STsep (m ~~ rep' m (Some hdptr))
        (fun r => m ~~ [r = lookup m k] * rep' (insert m k v) (Some hdptr)).
intros k v. 
refine (Fix2 
    (fun hdptr m => m ~~ rep' m (Some hdptr))
    (fun hdptr m r => m ~~ [r = lookup m k] * rep' (insert m k v) (Some hdptr))
    (fun F hdptr m => Assert (m ~~ Exists fn :@ Node, [head m = Some (key fn, value fn)] * hdptr --> fn * rep' (tail m) (next fn)) ;; 
                      fn <- !hdptr ;     
                      if eqK k (key fn) 
                      then  hdptr ::= node k v (next fn)  ;;
                           {{ Return Some (value fn) }} 
                      else  IfNull (next fn) As nxt
                           Then xx <- New (node k v None);
                                hdptr ::= node (key fn) (value fn) (Some xx) ;; 
                                {{ Return None }}
                           Else {{ F nxt (m ~~~ tail m) <@> (m ~~ hdptr --> fn  * [head m = Some (key fn, value fn)]) }} )); 
 try solve [ t | progress (hdestruct m; t) | destruct fn; hdestruct m; t; destruct m; t; t ]. Defined. 


Definition putFast (k: K) (v: V) (p : ptr) (m : [list (prod K V)])  :
  STsep (m ~~ rep m p)
        (fun r => m ~~ [r = lookup m k] * rep (insert m k v) p ).
intros; refine(
   opthd <- !p ;
   IfNull opthd
   Then xx <- New (node k v None) ;
        p ::= Some xx ;;
        {{ Return None }}
   Else {{ putFast' k v opthd m <@> _ }} );
 try solve [ t | progress (hdestruct m; t) | destruct fn; hdestruct m; t; destruct m; t; t ]. Defined.

*)

End JahobAssocList.


 
