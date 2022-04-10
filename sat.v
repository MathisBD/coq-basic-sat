From Coq Require Import String Ascii Permutation.
From mathcomp Require Import all_ssreflect zify.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac inv H := inversion H ; subst ; clear H.

(* ================================================== *)
(* CNF Definition and Manipulation *)
(* ================================================== *)

(* A literal is consists in :
   - a variable identifier (nat)
   - a boolean : true represent the literal V and false not(V) *)
Record lit := L { var : nat ; sign : bool }.

Definition notl (l : lit) : lit := 
  let (i, b) := l in L i (~~b).

Notation clause := (seq lit).

Notation cnf := (seq clause).

(* the list of variables in f, with potential duplicates *)
Fixpoint cnf_domain (f : cnf) : seq nat :=
  match f with 
  | [::] => [::]
  | c :: f' => (map var c) ++ (cnf_domain f')
  end.

Definition max_var (f : cnf) : nat := 
  foldr max 0 (cnf_domain f).
  
(* ================================================== *)
(* CNF printing *)
(* ================================================== *)

Open Scope char_scope.
Definition nat_to_digit (n : nat) : ascii :=
  match n with 
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | _ => "9"
  end.
Close Scope char_scope.

Fixpoint write_nat_aux (time n : nat) (acc : string) : string :=
  let acc' := String (nat_to_digit (n %% 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n %/ 10 with
        | 0 => acc'
        | n' => write_nat_aux time' n' acc'
      end
  end.

Definition write_nat n := write_nat_aux n n "".

Open Scope string_scope.
Definition write_lit (l : lit) := 
  let (id, b) := l in 
    (if b then "" else "-") ++ (write_nat id).

Fixpoint write_clause (c : clause) :=
  match c with 
  | nil => ""
  | l :: nil => write_lit l
  | l :: c' => (write_lit l) ++ " " ++ (write_clause c')
  end.

Fixpoint write_cnf (f : cnf) :=
  match f with
  | nil => ""
  | c :: nil => write_clause c
  | c :: f' => (write_clause c) ++ " /\ " ++ (write_cnf f')
  end.
Close Scope string_scope.

Definition example_cnf : cnf :=
  [:: [:: L 3 false ; L 2 true] ;
    [:: L 1 true ; L 2 false]].
(*Compute write_cnf example_cnf.*)


(* ================================================== *)
(* Model definition and basic manipulations *)
(* ================================================== *)

(* A model is a (partial) map from variables to bools. *)
Notation model := (seq (nat * bool)).

(* returns None if 'id' is not binded in 'm',
 * or the first binding corresponding to 'id' otherwise. *)
Fixpoint model_get (m : model) (i : nat) : option bool :=
  match m with 
  | [::] => None 
  | (i', b) :: m' => if i == i' then Some b else model_get m' i
  end.

Lemma model_getE m i : 
  model_get m i = 
    match m with 
    | [::] => None 
    | (i', b) :: m' => if i == i' then Some b else model_get m' i
    end.
Proof. by case: m. Qed.

Definition model_def m i : bool := model_get m i != None.

Lemma model_def_eq m i b : model_def ((i, b) :: m) i.
Proof. rewrite /model_def => /=. case: ifP ; by [|lia]. Qed.

Lemma model_def_neq m i k b : 
  i != k -> model_def ((i, b) :: m) k = model_def m k.
Proof. rewrite /model_def model_getE. case: ifP ; by [lia|]. Qed.

Definition model_domain (m : model) : seq nat := map fst m.

Lemma model_dom_def m i : model_def m i = (i \in model_domain m).
Proof.
  elim: m => [|[k b] m IH] //=.
  rewrite /model_def model_getE in_cons.
  case: ifP => [/eqP ->|/eqP] //=.
Qed.

Definition satisf_lit (m : model) (l : lit) :=
  let (i, b) := l in
  match model_get m i with 
  | Some b' => b == b'
  | _ => false
  end.

Definition satisf_clause (m : model) (c : clause) :=
  has (satisf_lit m) c.

Definition satisf_cnf (m : model) (f : cnf) : bool :=
  all (satisf_clause m) f.

Definition model_incl (m m' : model) : Prop := 
  forall i : nat, (model_get m i == None) || (model_get m i == model_get m' i).

Lemma model_incl_refl m :
  model_incl m m.
Proof. move=> i. by rewrite eq_refl orbT. Qed.

Lemma model_incl_trans m2 m1 m3 : 
  model_incl m1 m2 -> model_incl m2 m3 -> model_incl m1 m3.
Proof.
  move=> incl incl' i. move: (incl i) (incl' i). 
  move=> /orP [|/eqP] -> //.
Qed.

Lemma satisf_lit_incl l m m' : 
  satisf_lit m l -> model_incl m m' -> satisf_lit m' l.
Proof.
  case: l => i neg /=.
  case E: (model_get m i) => //= /eqP H_neg /(_ i). 
  symmetry in H_neg ; subst.
  by rewrite E => /= /eqP <-.
Qed.

Lemma satisf_clause_incl c m m' : 
  satisf_clause m c -> model_incl m m' -> satisf_clause m' c.
Proof.
  elim: c => [|l c IH] //= /orP [sat_ml|sat_mc] incl ; apply /orP.
  - by left ; eapply satisf_lit_incl ; eauto.
  - by right ; apply IH.
Qed.

Lemma satisf_cnf_incl f m m' : 
  satisf_cnf m f -> model_incl m m' -> satisf_cnf m' f.
Proof.
  elim: f => [|c f IH] //= /andP [sat_mc sat_mf] incl.
  apply /andP. intuition ; clear H0 sat_mf.
  by eapply satisf_clause_incl ; eauto.
Qed.

Lemma model_extend m k:
  exists m', model_incl m m' /\ forall i, i < k -> model_def m' i.
Proof.
  elim: k m => [m | k IH m] //=.
    exists m ; split ; [by apply model_incl_refl | by lia].
  move: IH => /(_ m) [m' [IH_incl IH_def]].
  case E: (model_get m' k).
  - exists m' ; split => //= i le_ik. 
    case: (ltngtP i k) ; [by apply IH_def | by lia |] => eq_ik.
    by rewrite eq_ik /model_def E.
  - exists ((k, true) :: m') ; split.
    + apply (@model_incl_trans m') => //= i.
      case: (@eqP _ i k) => [-> | /= neq_ik] ; first by rewrite E.
      apply /orP ; right. case: ifP ; by [lia|].
    + clear E IH_incl m => i. case: (ltngtP i k) ; try lia.
      * rewrite /model_def model_getE. case: ifP ; try lia ; move=> _ lt_ik _. 
        by apply IH_def.
      * move=> -> _. rewrite /model_def => /=. by rewrite eq_refl.
Qed.

Lemma model_incl_cons m m' i b : 
  model_incl m m' -> model_get m' i = Some b -> model_incl ((i, b) :: m) m'.
Proof. 
  move=> incl get k. case: (@eqP _ i k) get => [->|neq_ik] get /=.
  - by rewrite eq_refl get eq_refl orbT.
  - case: ifP ; by [lia | rewrite incl].
Qed.

Lemma incl_def_satisf_lit l m mS : 
  model_incl m mS -> satisf_lit mS l -> model_def m (var l) ->
     satisf_lit m l.
Proof. 
  case: l => [i b] /=.
  by rewrite /model_def => /(_ i) /orP [|] /eqP ->.
Qed.

(*Lemma incl_def_satisf_clause c m mS : 
  model_incl m mS -> satisf_clause mS c -> 
  (forall k', k' <= (max_var c) -> model_def m k') ->
     satisf_clause m c.
Proof. Admitted.*)

Lemma incl_def_satisf f m mS : 
  model_incl m mS -> satisf_cnf mS f -> 
  (forall k', k' <= (max_var f) -> model_def m k') ->
     satisf_cnf m f.
Proof. Admitted.

(* ================================================== *)
(* A dummy solver *)
(* ================================================== *)

Fixpoint solve_rec f m k : option model :=
  if k is k'.+1 then 
    match solve_rec f ((k', false) :: m) k' with 
    | Some m' => Some m'
    | None    => solve_rec f ((k', true) :: m) k'
    end
  else 
    if satisf_cnf m f then Some m
    else None.

Definition solve f := solve_rec f [::] (max_var f).+1.

Lemma solve_rec_correct f k m m' :
  solve_rec f m k = Some m' -> satisf_cnf m' f.
Proof.
  elim: k m m' => [m m' /= | k IH m m' /=].
    case: ifP => //=.
    by move=> H_sat eq_mm' ; inv eq_mm'.
  case E: (solve_rec f ((k, false) :: m) k).
    by move=> H ; inv H ; eapply IH ; eauto.
  by apply IH.
Qed.

Theorem solve_correct f m : 
  solve f = Some m -> satisf_cnf m f.
Proof. 
  by apply solve_rec_correct.
Qed.

Lemma solve_rec_complete f k m mS :
  model_incl m mS -> satisf_cnf mS f -> k <= (max_var f).+1 ->
  (forall k', k <= k' <= max_var f -> model_def m k') ->
    (exists m' : model, solve_rec f m k = Some m').
Proof.
  elim: k m mS => [|k IH] m mS H_incl mS_sat le_kmf m_def /=.
    rewrite (@incl_def_satisf f m mS) => //= ; eauto.
  (* We show that WLOG, we can have mS be defined on all the variables of f *)
  have mS_def : exists mS', 
    model_incl mS mS' /\ (forall k', k' <= max_var f -> model_def mS' k')
  by apply (@model_extend mS (max_var f).+1).
  move: mS_def => [mS' [mS_incl mS_def]].
  have incl : model_incl m mS' by apply (@model_incl_trans mS).
  have sat : satisf_cnf mS' f by apply (@satisf_cnf_incl _ mS).
  clear H_incl mS_sat mS_incl mS. rename mS' into mS.
  (* We now examine the value of mS on variable k *)
  case mS_k : (model_get mS k) => [b|] ; last first. 
    move : (mS_def k le_kmf). by rewrite /model_def mS_k. clear mS_def.
  move: (@model_incl_cons m mS k b incl mS_k). clear mS_k.
  case: b => incl_ext ; case E: (solve_rec f ((k, false) :: m) k) ; try eauto.
  - apply (@IH _ mS) => //= ; try lia ; move => k'. 
    case: (ltngtP k k') => [lt_kk' le_k'mf | // | -> le_k'mf] ; 
      last by rewrite model_def_eq.
    rewrite model_def_neq ; [apply m_def|] ; lia.
  - have H : exists m' : model, solve_rec f ((k, false) :: m) k = Some m'.
    apply (@IH _ mS) => //= ; try lia.
    move=> k' /andP []. case: (ltngtP k k') => [lt_kk' _ le_k'mf | // | ->] ; 
      last by rewrite model_def_eq.
    rewrite model_def_neq ; [apply m_def|] ; lia.
    move: H => [m' H]. by rewrite H in E.
Qed.


Theorem solve_complete f :
  (exists m, satisf_cnf m f) -> (exists m', solve f = Some m').
Proof.
  move=> [mS H_sat] ; rewrite /solve. 
  apply (@solve_rec_complete f _ _ mS) => //= ; lia.
Qed.

(* ================================================== *)
(* A naive DPLP solver *)
(* ================================================== *)

Inductive prod3 (A B C : Type) := triple : A -> B -> C -> prod3 A B C.

(* partitions a clause into (true, false, undefined) literals *)
Fixpoint partition_tfu (c : clause) (m : model) :=
  match c with 
  | [::] => triple [::] [::] [::]
  | L i b :: c' => 
    let (t, f, u) := partition_tfu c' m in 
      match model_get m i with 
      | None => triple t f (L i b :: u)
      | Some b' => if b' == b 
          then triple (L i b :: t) f u 
          else triple t (L i b :: f) u
      end  
  end.

Inductive greedy_action := 
  | Force (i : nat) (b : bool) (* the assignment i -> b is forced *)
  | FFalse                     (* the formula is already false *)
  | Undef.                     (* there is no immediate action to perform *)

Fixpoint greedy (f : cnf) (m : model) : greedy_action :=
  match f with 
  | [::] => Undef
  | c :: f' => 
    let (t, f, u) := partition_tfu c m in
    if size f == size c then FFalse
    else if size f == (size c).-1 then 
      match u with 
      | L i b :: _ => Force i b 
      | [::] => greedy f' m
      end
    else greedy f' m 
  end.

Inductive sat_res := 
  | Unsat
  | Sat (m : model)
  | Error.

Print iota.

(* returns all the undefined variables of m in range [x..x+k] *)
Definition undef_var_aux x k (m : model) : seq nat :=
  filter (fun i => ~~(model_def m i)) (iota x k.+1).

(* finds a variable in f that is not defined in m *)
Definition undef_var (f : cnf) (m : model) : option nat := 
  match undef_var_aux 0 (max_var f) m with
  | [::] => None
  | i :: _ => Some i
  end.

Lemma in_size_gt0 (T : eqType) (x : T) (s : seq T) : 
  x \in s -> size s > 0.
Proof. by elim: s. Qed.

Section SeqIncl.
  Variables T : eqType.
  
  Definition seq_incl (s1 s2 : seq T) := all (mem_seq s2) s1.

  Lemma seq_inclE s1 s2 : seq_incl s1 s2 =
    match s1 with 
    | [::] => true
    | x :: s1' => (x \in s2) && (seq_incl s1' s2)
    end. 
  Proof. by case: s1. Qed.

  Lemma mem_seq_perm x (s s' : seq T) : 
    Permutation s s' -> (x \in s) = (x \in s').
  Proof. 
    elim => //= ; try lia.
    - move=> y l l' P IH. by rewrite !in_cons IH.
    - move=> y z l. rewrite !in_cons. by lia.
  Qed.
  
  Lemma seq_incl_perm (s1 s2 s2' : seq T) :
    Permutation s2 s2' -> seq_incl s1 s2 = seq_incl s1 s2'.
  Proof. 
    elim: s1 => [|x s1 IH] //= P.
    rewrite IH => //.
    rewrite -[mem_seq s2 x]/(x \in s2) (@mem_seq_perm _ s2 s2') => //.
  Qed. 

  Lemma seq_incl_cons (s1 s2 : seq T) x :
    x \notin s1 -> seq_incl s1 (x :: s2) = seq_incl s1 s2.
  Proof. 
    elim: s1 => [|y s1 IH] //=.
    rewrite in_cons negb_or => /andP [/eqP neq_xy nin_xs1].
    rewrite IH => //. congr (fun X => X && seq_incl s1 s2). 
    case E: (y == x) => //=. move: E => /eqP E. symmetry in E. by [].
  Qed.

  Lemma seq_in_decomp (s : seq T) x :
    x \in s -> exists s1 s2, s = s1 ++ x :: s2.
  Proof.
    elim: s => [|a s IH] //=.
    rewrite in_cons. case E: (x == a) => /=.
    - move: E => /eqP -> _. exists [::]. by exists s.
    - intuition. move: H0 => [s1 [s2 ->]]. 
      exists (a :: s1). exists s2. by rewrite cat_cons.
  Qed.
 
  Lemma Perm_cons_app (s1 s2 : seq T) x : 
    Permutation (s1 ++ x :: s2) (x :: s1 ++ s2).
  Proof. elim: s1 => [|y s1 IH] //=. by rewrite perm_swap IH. Qed.   

  Lemma Perm_size (s1 s2 : seq T) :
    Permutation s1 s2 -> size s1 = size s2.
  Proof. elim => //= ; try lia. Qed.

  Lemma seq_incl_size (s1 s2 : seq T) : 
    seq_incl s1 s2 -> uniq s1 -> size s1 <= size s2.
  Proof. 
    elim: s1 s2 => [|x s1 IH] //= s2 /andP [in_xs2 incl_s1s2] /andP [nin_xs1 uniq_s1].
    move: (seq_in_decomp in_xs2) => [s3 [s4 decomp]]. subst.
    rewrite (@Perm_size (s3 ++ x :: s4) (x :: s3 ++ s4)) => /=.
      apply IH => //. rewrite -(@seq_incl_cons _ _ x) => //.
      rewrite (@seq_incl_perm _ _ (s3 ++ x :: s4)) => //. 
      symmetry ; apply Perm_cons_app.
    apply Perm_cons_app.
  Qed.
      

  Lemma iotaE m n : iota m n =
    match n with
    | 0 => [::]
    | n'.+1 => m :: iota m.+1 n'
    end.
  Proof. by case: n. Qed.
End SeqIncl.

Lemma undef_var_aux_find x k m :
  size (model_domain m) <= k -> undef_var_aux x k m != [::].
Proof.
  apply contraLR. rewrite negbK -ltnNge => H.
  have: forall i, x <= i <= x+k -> model_def m i.
    elim: k x H => [|k IH] x H i /andP [in1 in2].
    - have E: x = i by lia. move: H.
      rewrite -E /undef_var_aux => /=.
      case: ifP => //= ; lia.
    - case: (ltngtP x i) ; try lia ; 
      move: H ; rewrite /undef_var_aux => /= ; 
      case: ifP => // ; last by move=> def _ <- ; lia.
      move=> _ H in3. apply (@IH x.+1) ; try lia.
      by rewrite /undef_var_aux. 
  clear H => H.
  have: seq_incl (iota x k.+1) (model_domain m). 
    elim: k x H => [/=|k IH] x H.
      have : model_def m x by apply H ; lia.
      by rewrite model_dom_def andbT.
    rewrite iotaE seq_inclE. apply /andP ; split.
      by rewrite -model_dom_def ; apply H ; lia.
    apply IH => i ineq. apply H ; lia.
  move=> /(@seq_incl_size _). rewrite size_iota iota_uniq.
  by intuition.
Qed.

Lemma undef_var_find f m : 
  size (model_domain m) <= max_var f -> undef_var f m <> None.
Proof. 
  rewrite /undef_var => H. move: (@undef_var_aux_find 0 (max_var f) m H).
  case: (undef_var_aux 0 (max_var f) m) => //.
Qed.

Fixpoint solveN_rec f m k : sat_res :=
  if k is k'.+1 then
    match greedy f m with 
    | Force i b => solveN_rec f ((i, b) :: m) k'
    | FFalse => Unsat
    | Undef => 
      if undef_var f m is Some i then 
        match solveN_rec f ((i, false) :: m) k' with 
        | Sat m' => Sat m'
        | Unsat  => solveN_rec f ((i, true) :: m) k'
        | Error => Error
        end
      else Error (* this case should never happen *)
    end
  else 
    if satisf_cnf m f then Sat m else Unsat.

Definition solveN f := solveN_rec f [::] (max_var f).+1.

Theorem solveN_rec_correct f m m' k :
  solveN_rec f m k = Sat m' -> satisf_cnf m' f.
Proof.
  elim: k m m' => [|k IH] m m' /=.
    by case: ifP => [sat [<-]|].
  case: (greedy f m) => [i b sat|//|] ; first by eauto.
  case: (undef_var f m) => [i|//].
  case E: (solveN_rec f ((i, false) :: m) k) => [|m''|//].
    by eauto.
  by move=> [] <- ; eauto.
Qed.

Theorem solveN_correct f m :
  solveN f = Sat m -> satisf_cnf m f.
Proof. eauto using solveN_rec_correct. Qed.

Print leq.

(* I could even use size (undup (model_domain m)) = ... 
   as the precondition, but this is enough. *)
Theorem solveN_rec_noerr f m k :
  k <= (max_var f).+1 -> size (model_domain m) = (max_var f).+1 - k -> 
    solveN_rec f m k <> Error.
Proof.
  elim: k m => [|k IH] m pre1 pre2 /=.
    by case: ifP.
  case: (greedy f m) => [i b|//|].
    apply (@IH ((i, b) :: m)) => /= ; try lia.
  have: undef_var f m <> None by apply undef_var_find ; lia.    
  case E: (undef_var f m) => [i|//]. move=> _.
  case E1: (solveN_rec f ((i, false) :: m) k) => [|//|].
    by apply IH => /= ; lia.
  have: solveN_rec f ((i, false) :: m) k <> Error.
    by apply IH => /= ; lia.
  by [].
Qed.

Theorem solveN_noerr f : solveN f <> Error.
Proof. by apply solveN_rec_noerr => /= ; lia. Qed.

Theorem solveN_complete f m :
  satisf_cnf m f -> (exists m', solveN f = Sat m').
Proof. Admitted.



Definition c : cnf := [:: 
      [:: L 0 true ] ; 
      [:: L 1 true ] ;
      [:: L 0 false ; L 1 false]
  ].
Compute (write_cnf c, solve c).














