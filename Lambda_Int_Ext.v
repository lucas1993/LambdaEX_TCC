Set Implicit Arguments.

Require Import Metatheory LambdaES_Defs LambdaESLab_Defs LambdaES_Infra LambdaES_FV.
Require Import Rewriting.
Require Import Equation_C Lambda Lambda_Ex.



(*Inductive lab_x_e: pterm -> pterm -> Prop :=*)
(*| xe_left_app : forall t1 t2 t1', *)
        (*lab_term(pterm_app t1 t2) ->*)
        (*t1 ->_Bx t1' ->*)
        (*lab_x_e (pterm_app t1 t2) (pterm_app t1' t2) *)
(*| xe_right_app : forall t1 t2 t2', *)
        (*lab_term(pterm_app t1 t2) ->*)
        (*t2 ->_Bx t2' ->*)
        (*lab_x_e (pterm_app t1 t2) (pterm_app t1 t2') *)
(*| xe_in_lamb : forall t1 t1' L, *)
        (*lab_term (pterm_abs t1) -> *)
        (*(forall x, x \notin L ->  (t1 ^ x) ->_Bx (t1' ^ x)) -> *)
        (*lab_x_e (pterm_abs t1) (pterm_abs t1') *)
(*| xe_in_es_ext : forall t t' u,*)
        (*lab_term (t [u]) ->*)
        (*t ->_Bx t' ->*)
        (*lab_x_e (t [u]) (t' [u])*)
(*| xe_in_es_int : forall t t' u,*)
        (*lab_term (u [t]) ->*)
        (*t ->_Bx t' ->*)
        (*lab_x_e (u [t]) (u [t'])*)
(*| xe_in_les : forall t t' u,*)
        (*lab_term (t [[u]]) ->*)
        (*t ->_Bx t' ->*)
        (*lab_x_e (t [[u]]) (t' [[u]])*)
(*.*)

Inductive ext_lab_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
| lab_redex : forall t s, Red t s -> ext_lab_contextual_closure Red t s
| lab_app_left : forall t t' u, lab_term u -> ext_lab_contextual_closure Red t t' -> 
	  		        ext_lab_contextual_closure Red (pterm_app t u) (pterm_app t' u)
| lab_app_right : forall t u u', lab_term t -> ext_lab_contextual_closure Red u u' -> 
	  		         ext_lab_contextual_closure Red (pterm_app t u) (pterm_app t u')
| lab_abs_in : forall t t' L, (forall x, x \notin L -> ext_lab_contextual_closure Red (t^x) (t'^x)) 
                              -> ext_lab_contextual_closure Red (pterm_abs t) (pterm_abs t')
| lab_subst_left : forall t t' u L, lab_term u -> 
	  	                    (forall x, x \notin L -> ext_lab_contextual_closure Red (t^x) (t'^x)) -> 
	                            ext_lab_contextual_closure Red  (t[u]) (t'[u])
| lab_subst_right : forall t u u', lab_body t -> ext_lab_contextual_closure Red u u' -> 
	  	                   ext_lab_contextual_closure Red  (t[u]) (t[u']) 
| lab_subst'_ext : forall t t' u L, term u -> SN lex u ->
	  	                    (forall x, x \notin L -> ext_lab_contextual_closure Red (t^x) (t'^x)) -> 
	                            ext_lab_contextual_closure Red  (t[[u]]) (t'[[u]])
.

Inductive lab_x_i: pterm -> pterm -> Prop :=
| xi_from_bx_in_les: forall t1 t2 t2', 
                       lab_term (t1 [[ t2 ]]) ->
                       (t2 -->lex t2') ->
                       lab_x_i (t1 [[ t2 ]]) (t1 [[ t2' ]])
| xi_from_x : forall t t', 
                lab_term t ->
                lab_sys_x t t' -> 
                lab_x_i t t'. 

Definition lab_x_i_eq (t: pterm) (u : pterm) := 
    exists t' u', (t =EE t')/\(ext_lab_contextual_closure lab_x_i t' u')/\(u' =EE u).

Definition lab_x_e_eq (t: pterm) (u : pterm) := 
    exists t' u', (t =EE t')/\((ext_lab_contextual_closure sys_Bx) t' u')/\(u' =EE u).

Notation "t -->[lx_i] u" := (lab_x_i_eq t u) (at level 59, left associativity).
Notation "t -->[lx_e] u" := (lab_x_e_eq t u) (at level 59, left associativity).

Lemma lab_sys_x_i_e: forall t t' x x', lab_term t -> (x =EE t) -> (t' =EE x') -> lab_sys_lx t t' -> (x -->[lx_i] x' \/ x -->[lx_e] x').
Proof.
    intros.
    induction H2.  
    constructor 2. exists t u. split*. split. constructor 1. constructor 1. auto. auto. 
    constructor 2. exists t u. split*. split. constructor 1. constructor 2. auto. auto. 
    constructor 1. exists t u. split*. split. constructor 1. auto. constructor 2. auto. auto. auto.
Qed.

(*Lemma lab_x_i_sys_lx: forall t t', lab_x_i t t' -> lab_sys_lx t t'.*)
(*Proof.*)
    (*intros.*)
    (*induction H.*)
    (*destruct H0.  destruct H0.*)
    (*destruct H0.*)
    (*destruct H1.*)
    (*induction H1.*)
(*Qed.*)

Lemma eqcc_lab_term: forall t t', lab_term t -> t =ee t' -> lab_term t'.
Proof.
    intros. induction H0. inversion H0; subst. 
    apply term''_to_lab_term.
    apply lab_term_to_term'' in H. unfold term'' in *. simpl.
    simpl in H. destruct H. destruct H. split. split. admit. admit. admit. 

    inversion H0; subst.
    apply term''_to_lab_term.
    apply lab_term_to_term'' in H. unfold term'' in *. simpl.
    simpl in H. destruct H. destruct H3. destruct H4. 
    split. split. apply lc_at_weaken_ind with 0. auto. auto. 
    split*.  admit. admit. 

    inversion H0; subst.
    apply term''_to_lab_term.
    apply lab_term_to_term'' in H. unfold term'' in *. simpl.
    simpl in H. destruct H. destruct H. destruct H4. 
    split. apply term_to_term' in H5; unfold term' in *; auto. 
    split*. split. admit.
    admit. 


    inversion H0; subst.
    apply term''_to_lab_term.
    apply lab_term_to_term'' in H. unfold term'' in *. simpl.
    simpl in H. destruct H. destruct H3. destruct H4. destruct H6. 
    split. apply term_to_term' in H5; unfold term' in *; auto. 
    split*. split. apply lc_at_weaken_ind with 0. auto. auto. 
    split*.
    admit. 
Qed.

Lemma star_ctx_eqcc_sym: forall t u, t =EE u -> u =EE t.
Proof.
    Admitted.

Lemma star_ctx_eqcc_lab_term: forall t t', lab_term t -> t =EE t' -> lab_term t'.
Proof.
    Admitted.

Lemma pterm_app_EE_inversion: forall t u v, (pterm_app t u) =EE v -> exists t' u', v = (pterm_app t' u') /\ (t =EE t') /\ (u =EE u').
Proof.
    Admitted.

Lemma star_lab_closure_app_left: forall R t t' u, lab_term u -> star_closure (lab_contextual_closure R) t t' -> star_closure (lab_contextual_closure R) (pterm_app t u) (pterm_app t' u).
Proof.
    intros.
    induction H0.
    constructor.
    constructor 2.
    induction H0.
    constructor. constructor 2; auto.
    constructor 2 with (pterm_app u0 u); auto. 
Qed.

Lemma star_lab_closure_app_right: forall R t t' u, lab_term u -> star_closure (lab_contextual_closure R) t t' -> star_closure (lab_contextual_closure R) (pterm_app u t) (pterm_app u t').
Proof.
    intros.
    induction H0.
    constructor.
    constructor 2.
    induction H0.
    constructor. constructor 3; auto.
    constructor 2 with (pterm_app u u0); auto.
Qed.

Lemma pterm_abs_EE_inversion: forall t v, (pterm_abs t) =EE v -> exists t', v = (pterm_abs t') /\ (t =EE t').
Proof.
    Admitted.

Lemma lx_i_open_abs: forall x x0 L, (forall y : VarSet.elt, y \notin L -> x0 ^ y-->[lx_i]x ^ y) -> pterm_abs x0-->[lx_i]pterm_abs x.
Proof.
    Admitted.

Lemma term_EE_open: forall t t' x, t =EE t' -> (t ^ x) =EE (t' ^ x).
Proof.
    Admitted.

Lemma lab_ex_eq_i_e: forall t t', lab_term t -> (t -->[lex] t' <-> (t -->[lx_i] t' \/ t -->[lx_e] t')).
Proof.
    split.
    intro.
    destruct H0.  destruct H0. destruct H0.  destruct H1.
    generalize dependent t.
    generalize dependent t'.
    induction H1; intros.

    (* Base *)
    apply lab_sys_x_i_e with t s; auto. apply star_ctx_eqcc_lab_term with t0; auto*.

    (* app left *)
    assert (H4 := pterm_app_EE_inversion H2).
    apply star_ctx_eqcc_sym in H3.
    assert (H5 := pterm_app_EE_inversion H3).
    destruct H4.  destruct H4.  destruct H4.  destruct H6.  
    destruct H5.  destruct H5.  destruct H5.  destruct H8.
    subst. inversion H0; subst.  apply star_ctx_eqcc_sym in H8.
    assert (x1-->[lx_i]x \/ x1-->[lx_e]x).  apply IHlab_contextual_closure; auto.
    destruct H4. left. 
    destruct H4. destruct H4. destruct H4. destruct H5.
    exists (pterm_app x3 u) (pterm_app x4 u).
    split. apply star_closure_composition with (pterm_app x1 u).
    apply star_lab_closure_app_right. auto. apply star_ctx_eqcc_sym in H9. auto.
    apply star_lab_closure_app_left. auto. auto.
    split. constructor 2; auto. apply star_closure_composition with (pterm_app x u).
    apply star_lab_closure_app_left; auto. apply star_lab_closure_app_right; auto.
    admit.
    right.
    destruct H4. destruct H4. destruct H4. destruct H5.
    exists (pterm_app x3 u) (pterm_app x4 u).
    split. apply star_closure_composition with (pterm_app x1 u).
    apply star_lab_closure_app_right. auto. apply star_ctx_eqcc_sym in H9. auto.
    apply star_lab_closure_app_left. auto. auto.
    split. constructor 2; auto. apply star_closure_composition with (pterm_app x u).
    apply star_lab_closure_app_left; auto. apply star_lab_closure_app_right; auto.
    admit.

    (* app right *)
    assert (H4 := pterm_app_EE_inversion H2).
    apply star_ctx_eqcc_sym in H3.
    assert (H5 := pterm_app_EE_inversion H3).
    destruct H4.  destruct H4.  destruct H4.  destruct H6.  
    destruct H5.  destruct H5.  destruct H5.  destruct H8.
    subst. inversion H0; subst.  apply star_ctx_eqcc_sym in H9.
    assert (x2-->[lx_i]x0 \/ x2-->[lx_e]x0).  apply IHlab_contextual_closure; auto.
    destruct H4. left. 
    destruct H4. destruct H4. destruct H4. destruct H5.
    exists (pterm_app t x3) (pterm_app t x4).
    split. apply star_closure_composition with (pterm_app x1 x3).
    apply star_lab_closure_app_right. auto.  auto.
    apply star_lab_closure_app_left. admit. apply star_ctx_eqcc_sym in H8. auto. 
    split. constructor 3; auto. apply star_closure_composition with (pterm_app x x4).
    apply star_lab_closure_app_left; auto. admit. apply star_lab_closure_app_right; auto.
    admit.
    right.
    destruct H4. destruct H4. destruct H4. destruct H5.
    exists (pterm_app t x3) (pterm_app t x4).
    split. apply star_closure_composition with (pterm_app x1 x3).
    apply star_lab_closure_app_right. auto.  auto.
    apply star_lab_closure_app_left. admit. apply star_ctx_eqcc_sym in H8. auto. 
    split. constructor 3; auto. apply star_closure_composition with (pterm_app x x4).
    apply star_lab_closure_app_left; auto. admit. apply star_lab_closure_app_right; auto.
    admit.

    (* abs *)
    assert (H4 := pterm_abs_EE_inversion H2).
    apply star_ctx_eqcc_sym in H3.
    assert (H5 := pterm_abs_EE_inversion H3).
    destruct H4.  destruct H4. 
    destruct H5.  destruct H5. 
    subst. inversion H1; subst. 
    (*assert (forall y, y \notin (L \u L0) -> x0 ^ y -->[lx_i] x ^ y ).*)
    (*intros.*)
    (*apply term_EE_open with t' x y in H6.*)
    (*apply term_EE_open with t x0 y in H7.*)
    (*apply notin_union in H4. destruct H4.*)
    (*pose proof (H5 y H8); auto.*)
    (*apply star_ctx_eqcc_sym in H7.*)
    (*pose proof (H0 y H4 (x ^ y) H6 (x0 ^ y) H9 H7). admit.*)
    (*left. *)
    assert (forall y, y \notin (L \u L0) -> x0 ^ y -->[lx_i] x ^ y \/  x0 ^ y -->[lx_e] x ^ y ).
    intros.
    apply term_EE_open with t' x y in H6.
    apply term_EE_open with t x0 y in H7.
    apply notin_union in H4. destruct H4.
    pose proof (H5 y H8); auto.
    apply star_ctx_eqcc_sym in H7.
    pose proof (H0 y H4 (x ^ y) H6 (x0 ^ y) H9 H7). auto.
    (*assert ((forall y : VarSet.elt, y \notin L \u L0 -> x0 ^ y-->[lx_i]x ^ y) \/ (forall y : VarSet.elt, y \notin L \u L0 -> x0 ^ y-->[lx_e]x ^ y)). admit.*)
    (*destruct H8. left. apply lx_i_open_abs with (L \u L0). auto.*)
    (*exists (pterm_abs x0) (pterm_abs x). *)
    (*split. constructor 1. split. constructor 4 with (L \u L0). intros. *)
    (*pose proof ( H8 x1 H9 ). destruct H10. destruct H10.*)


    (*inversion H2; subst. inversion H4; subst. inversion H4; subst.*)
    (*inversion H2; subst. inversion H4; subst. inversion H4; subst.*)
    (*inversion H2; subst. inversion H4; subst. inversion H4; subst.*)
    (*inversion H2; subst. inversion H5; subst.*)

    (*Focus 7.*)
    (*intros. destruct H0; destruct H0; destruct H0; destruct H0; destruct H1; induction H1.*)
    (*exists t0 s. split*. split*. constructor 1; auto. constructor.*)
    (*exists (t1 [[t2]]) (t1 [[t2']]). split*. split. constructor 8. inversion H1. *)
    (*exists L; auto. inversion H1; auto.  inversion H3. constructor 1; auto.*)
    (*constructor 2; auto. auto. *)



Qed.
