Set Implicit Arguments.

Require Import Metatheory LambdaES_Defs LambdaESLab_Defs LambdaES_Infra LambdaES_FV.
Require Import Rewriting.
Require Import Equation_C Lambda Lambda_Ex.



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
                       (sys_Bx t2 t2') ->
                       lab_x_i (t1 [[ t2 ]]) (t1 [[ t2' ]])
| xi_from_x : forall t t', 
                lab_term t ->
                lab_sys_x t t' -> 
                lab_x_i t t'. 

Definition lab_EE_ctx_red (R: pterm -> pterm -> Prop) (t: pterm) (u : pterm) := 
    exists t' u', (t =EE t')/\(lab_contextual_closure R t' u')/\(u' =EE u).

Definition ext_lab_EE_ctx_red (R: pterm -> pterm -> Prop) (t: pterm) (u : pterm) := 
    exists t' u', (t =EE t')/\(ext_lab_contextual_closure R t' u')/\(u' =EE u).


Definition lab_x_i_eq := ext_lab_EE_ctx_red lab_x_i.

Definition lab_x_e_eq := ext_lab_EE_ctx_red sys_Bx.

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

Lemma term_EE_open: forall t t' x, (t ^ x) =EE t' -> exists u, t' = u ^ x.
Proof.
    Admitted.


(* ----------------------------------------------------- RED REGULAR *)

Lemma red_rename_lab_ctx: forall R, red_rename R -> red_rename (lab_contextual_closure R).
Proof.
    Admitted.

Lemma red_rename_eqcc: red_rename eqcc.
Proof.
   unfold red_rename.
   intros.
   induction H1. 
   pose proof red_rename_eqc.  unfold red_rename in H2.
   constructor 1.
   apply H2 with x; auto.
   admit. (* RED_RENAME LAB_EQC *)
Qed.

Lemma close_var_spec : forall t x, term t -> 
  exists u, t = u ^ x /\ body u /\ x \notin (fv u).
Proof.
    Admitted.

Lemma red_rename_EE: red_rename star_ctx_eqcc.
Proof.
    unfold red_rename. intros. 
    remember (t ^ x) as u.  remember (t' ^ x) as u'.
    induction H1; subst.
    apply open_var_inj in Hequ'.
    rewrite Hequ'; auto. constructor 1; auto. auto. auto.
    remember (t ^ x) as u.  remember (t' ^ x) as u'.
    generalize dependent t.
    generalize dependent t'.
    induction H1; intros; subst.
    admit.
    assert (term u). admit.
    pose proof (@close_var_spec u x H1).
    destruct H2 as [ u0 [ H3 [ H4 H5 ] ] ].
    apply star_closure_composition with (u0 ^ y).
    apply IHtrans_closure1; auto. 
    apply IHtrans_closure2; auto. 
Qed.

(* ----------------------------------------------------- RED RENAME *)

Lemma red_rename_lab_lex: red_rename lab_eqc.
Proof.
    Admitted.

Lemma red_rename_lab_xi_eq: red_rename lab_x_i_eq.
Proof.
    Admitted.

Lemma red_rename_lab_xe_eq: red_rename lab_x_e_eq.
Proof.
    Admitted.

Lemma red_rename_lab_lex: red_rename lab_lex.
Proof.
    Admitted.


(* ------------------------------------------------------- star_lab clos *)

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


Lemma trans_lab_closure_abs: forall R t t' L, red_rename R -> (forall y : VarSet.elt, y \notin L -> trans_closure (lab_contextual_closure R) (t ^ y) (t' ^ y)) -> trans_closure (lab_contextual_closure R) (pterm_abs t) (pterm_abs t').
Proof.
    intros.
    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H1. destruct H1.
    pose proof (H0 z H1).
    remember (t ^ z) as u.  remember (t' ^ z) as u'.
    generalize dependent t. generalize dependent t'.
    induction H4; intros; subst.
    constructor 1. constructor 4 with L. intros. 
    apply red_rename_lab_ctx in H. unfold red_rename in H. apply H with z; auto.
    (*apply open_var_inj in Hequ; subst; auto. constructor 1; auto. *)
Admitted.

Lemma star_lab_closure_abs: forall R t t' L, (forall y : VarSet.elt, y \notin L -> star_closure (lab_contextual_closure R) (t ^ y) (t' ^ y)) -> star_closure (lab_contextual_closure R) (pterm_abs t) (pterm_abs t').
Proof.
    intros.
    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H0. destruct H0.
    pose proof (H z H0).
    remember (t ^ z) as u.  remember (t' ^ z) as u'.
    generalize dependent t. generalize dependent t'.
    induction H3; intros; subst.
    apply open_var_inj in Hequ; subst; auto. constructor 1; auto. 
Admitted.

(* -------------------------------------------------------------  EE clos *)

Lemma EE_clos_app_left: forall R t t' u, lab_term u -> ((lab_EE_ctx_red R) t t') -> ((lab_EE_ctx_red R) (pterm_app t u) (pterm_app t' u)).
Proof.
    intros.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    exists (pterm_app x u) (pterm_app x0 u).
    split. apply star_lab_closure_app_left; auto.
    split*. constructor 2; auto.
    apply star_lab_closure_app_left; auto.

Qed.

Lemma EE_clos_app_right: forall R t t' u, lab_term u -> ((lab_EE_ctx_red R) t t') -> ((lab_EE_ctx_red R) (pterm_app u t) (pterm_app u t')).
Proof.
    intros.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    exists (pterm_app u x) (pterm_app u x0).
    split. apply star_lab_closure_app_right; auto.
    split*. constructor 3; auto.
    apply star_lab_closure_app_right; auto.

Qed.

Lemma EE_clos_abs: forall R x x0 L, (forall y : VarSet.elt, y \notin L -> (lab_EE_ctx_red R) (x0 ^ y) (x ^ y)) -> (lab_EE_ctx_red R) (pterm_abs x0) (pterm_abs x).
Proof.
    intros.
    pick_fresh z.
    apply notin_union in Fr. destruct Fr.
    apply notin_union in H0. destruct H0.
    pose proof (H z H0).
    destruct H3.  destruct H3.  destruct H3.  destruct H4.
    pose proof H3;  apply (term_EE_open ) in H3.
    pose proof H5;  apply star_ctx_eqcc_sym in H5;  apply (term_EE_open ) in H5.
    destruct H3; subst.  destruct H5; subst.
    exists (pterm_abs x3) (pterm_abs x1).
    split. apply star_lab_closure_abs with (L := L); auto.
    intros. apply red_rename_EE with z; auto.
Admitted.

Lemma EE_clos_outer_sub: forall R t t' u L, (forall y : VarSet.elt, y \notin L -> (lab_EE_ctx_red R) (t ^ y) (t' ^ y)) -> (lab_EE_ctx_red R) (t[u]) (t'[u]).
Proof.
    Admitted.

Lemma EE_clos_inner_sub: forall R t u u', (lab_EE_ctx_red R) (u) (u') -> (lab_EE_ctx_red R) (t[u]) (t[u']).
Proof.
    Admitted.

Lemma EE_clos_outer_lsub: forall R t t' u L, (forall y : VarSet.elt, y \notin L -> (lab_EE_ctx_red R) (t ^ y) (t' ^ y)) -> (lab_EE_ctx_red R) (t[[u]]) (t'[[u]]).
Proof.
    Admitted.

Lemma EE_clos_inner_lsub: forall R t u u', (lab_EE_ctx_red R) (u) (u') -> (lab_EE_ctx_red R) (t[[u]]) (t[[u']]).
Proof.
    Admitted.

(* -------------------------------------------------------------  EE ext_clos *)

Lemma EE_ext_clos_app_left: forall R t t' u, lab_term u -> ((ext_lab_EE_ctx_red R) t t') -> ((ext_lab_EE_ctx_red R) (pterm_app t u) (pterm_app t' u)).
Proof.
    intros.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    exists (pterm_app x u) (pterm_app x0 u).
    split. apply star_lab_closure_app_left; auto.
    split*. constructor 2; auto.
    apply star_lab_closure_app_left; auto.

Qed.

Lemma EE_ext_clos_app_right: forall R t t' u, lab_term u -> ((ext_lab_EE_ctx_red R) t t') -> ((ext_lab_EE_ctx_red R) (pterm_app u t) (pterm_app u t')).
Proof.
    intros.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H1.
    exists (pterm_app u x) (pterm_app u x0).
    split. apply star_lab_closure_app_right; auto.
    split*. constructor 3; auto.
    apply star_lab_closure_app_right; auto.

Qed.

Lemma EE_ext_clos_abs: forall R x x0 L, (forall y : VarSet.elt, y \notin L -> (ext_lab_EE_ctx_red R) (x0 ^ y) (x ^ y)) -> (ext_lab_EE_ctx_red R) (pterm_abs x0) (pterm_abs x).
Proof.
    Admitted.

Lemma EE_ext_clos_outer_sub: forall R t t' u L, (forall y : VarSet.elt, y \notin L -> (ext_lab_EE_ctx_red R) (t ^ y) (t' ^ y)) -> (ext_lab_EE_ctx_red R) (t[u]) (t'[u]).
Proof.
    Admitted.

Lemma EE_ext_clos_inner_sub: forall R t u u', (ext_lab_EE_ctx_red R) (u) (u') -> (ext_lab_EE_ctx_red R) (t[u]) (t[u']).
Proof.
    Admitted.

Lemma EE_ext_clos_outer_lsub: forall R t t' u L, (forall y : VarSet.elt, y \notin L -> (ext_lab_EE_ctx_red R) (t ^ y) (t' ^ y)) -> (ext_lab_EE_ctx_red R) (t[[u]]) (t'[[u]]).
Proof.
    Admitted.

Lemma EE_ext_clos_inner_lsub: forall R t u u', (ext_lab_EE_ctx_red R) (u) (u') -> (ext_lab_EE_ctx_red R) (t[[u]]) (t[[u']]).
Proof.
    Admitted.

(* ------------------- *)


(*Lemma pterm_abs_EE_inversion: forall t v, (pterm_abs t) =EE v -> exists t', v = (pterm_abs t') /\ (t =EE t').*)
(*Proof.*)
    (*Admitted.*)

(*Lemma pterm_sub_EE_inversion: forall t u v, (t[u]) =EE v -> (exists t', v = (t'[u])) \/ (exists t' u', v = (t'[u'])) \/ (exists t' u', v = (t'[[u']])).*)
(*Proof.*)
    (*Admitted.*)

(*Lemma lx_i_open_abs: forall x x0 L, (forall y : VarSet.elt, y \notin L -> x0 ^ y-->[lx_i]x ^ y) -> pterm_abs x0-->[lx_i]pterm_abs x.*)
(*Proof.*)
    (*Admitted.*)

(*Lemma lx_e_open_abs: forall x x0 L, (forall y : VarSet.elt, y \notin L -> x0 ^ y-->[lx_e]x ^ y) -> pterm_abs x0-->[lx_e]pterm_abs x.*)
(*Proof.*)
    (*Admitted.*)


Lemma EE_lab_term : forall t t', lab_term t -> t =EE t' -> lab_term t'.
Proof.
    Admitted.

Lemma lab_sys_lx_term_is_sys_Bx : forall t t', term t -> lab_sys_lx t t' -> sys_Bx t t'.
Proof.
    Admitted.



(* ------------------------------------------------------------  EE presv reductions *)

Lemma EE_presv_ie: forall t t' u u', t =EE u -> u' =EE t' -> ((u -->[lx_i] u' \/ u -->[lx_e] u') -> (t -->[lx_i] t' \/ t -->[lx_e] t')).
Proof.
    intros.

    destruct H1.  destruct H1.  destruct H1.  destruct H1. destruct H2.
    left.  
    exists x x0.
    split*.
    apply star_closure_composition with u; auto.
    split*.
    apply star_closure_composition with u'; auto.

    destruct H1.  destruct H1.  destruct H1.  destruct H2.
    right.  
    exists x x0.
    split*.
    apply star_ctx_eqcc_sym in H.
    apply star_ctx_eqcc_sym in H.
    apply star_closure_composition with u; auto.
    split*.
    apply star_closure_composition with u'; auto.
Qed.

Lemma EE_presv_lab_lex: forall t t' u u', t =EE u -> u' =EE t' -> ((u -->[lex] u') -> (t -->[lex] t')).
Proof.
    intros.
    destruct H1.
    destruct H1.
    destruct H1.
    destruct H2.
    exists x x0.
    split. apply star_closure_composition with u; auto.
    split*. apply star_closure_composition with u'; auto.
Qed.

(* ------------------------------------------------------------- IE <-> LEX (um passo) *)

Lemma lab_ex_impl_i_e: forall t t', lab_term t -> t -->[lex] t' -> (t -->[lx_i] t' \/ t -->[lx_e] t').
Proof.
    intros.
    destruct H0.  destruct H0. destruct H0.  destruct H1.
    generalize dependent t.
    generalize dependent t'.
    induction H1; intros.

    (* Base *)
    apply lab_sys_x_i_e with t s; auto. apply EE_lab_term with t0; auto*.

    (* app_left *)
    apply EE_presv_ie with (u := (pterm_app t u)) (u' := (pterm_app t' u)); auto.
    assert  (t-->[lx_i]t' \/ t-->[lx_e]t').
    apply IHlab_contextual_closure; auto. constructor 1; auto. admit. constructor 1; auto.
    destruct H4. 
    left. apply EE_ext_clos_app_left. admit. auto.
    right. apply EE_ext_clos_app_left. admit. auto.

    (* app_right *)
    apply EE_presv_ie with (u := (pterm_app t u)) (u' := (pterm_app t u')); auto.
    assert  (u-->[lx_i]u' \/ u-->[lx_e]u').
    apply IHlab_contextual_closure; auto. constructor 1; auto. admit. constructor 1; auto.
    destruct H4. 
    left. apply EE_ext_clos_app_right. admit. auto.
    right. apply EE_ext_clos_app_right. admit. auto.

    (* abs *)
    apply EE_presv_ie with (u := pterm_abs t) (u' := pterm_abs t'); auto.
    pick_fresh z.
    assert  (t^z-->[lx_i]t'^z \/ t^z-->[lx_e]t'^z).
    apply H0 with z; auto. constructor 1; auto. admit. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H5; destruct H5.
    apply notin_union in H5; destruct H5.
    apply notin_union in H5; destruct H5.
    destruct H4.
    left. apply EE_ext_clos_abs with L.
    intros. pose proof red_rename_lab_xi_eq. apply H11 with z; auto.
    right. apply EE_ext_clos_abs with L.
    intros. pose proof red_rename_lab_xe_eq. apply H11 with z; auto.

    (* outer sub *)
    apply EE_presv_ie with (u := t[u]) (u' := t'[u]); auto.
    pick_fresh z.
    assert  (t^z-->[lx_i]t'^z \/ t^z-->[lx_e]t'^z).
    apply H1 with z; auto. constructor 1; auto. admit. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H6; destruct H6.
    apply notin_union in H6; destruct H6.
    apply notin_union in H6; destruct H6.
    apply notin_union in H6; destruct H6.
    destruct H5.
    left. apply EE_ext_clos_outer_sub with L.
    intros. pose proof red_rename_lab_xi_eq. apply H13 with z; auto.
    right. apply EE_ext_clos_outer_sub with L.
    intros. pose proof red_rename_lab_xe_eq. apply H13 with z; auto.

    (* inner sub *)
    apply EE_presv_ie with (u := t[u]) (u' := t[u']); auto.
    assert (u' =EE u'). constructor 1; auto.
    assert (u =EE u). constructor 1; auto.
    apply EE_lab_term in H3. inversion H3; subst.
    pose proof (IHlab_contextual_closure u' H4 u H9 H5).
    destruct H6. 
    left. apply EE_ext_clos_inner_sub; auto.
    right. apply EE_ext_clos_inner_sub; auto.
    auto.

    (* outer lsub *)
    apply EE_presv_ie with (u := t[[u]]) (u' := t'[[u]]); auto.
    pick_fresh z.
    assert  (t^z-->[lx_i]t'^z \/ t^z-->[lx_e]t'^z).
    apply H1 with z; auto. constructor 1; auto. admit. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H6; destruct H6.
    apply notin_union in H6; destruct H6.
    apply notin_union in H6; destruct H6.
    apply notin_union in H6; destruct H6.
    destruct H5.
    left. apply EE_ext_clos_outer_lsub with L.
    intros. pose proof red_rename_lab_xi_eq. apply H13 with z; auto.
    right. apply EE_ext_clos_outer_lsub with L.
    intros. pose proof red_rename_lab_xe_eq. apply H13 with z; auto.

    (* inner lsub *)
    left. exists (t [[u]]) (t [[u']]). split. auto.
    split*. 
    apply EE_lab_term in H3.
    inversion H3; subst.
    apply lab_sys_lx_term_is_sys_Bx in H0; auto.
    inversion H0; subst.
    constructor 1.  constructor 1. auto. auto.
    constructor 1.  constructor 1. auto. constructor 2; auto. 
    auto.

Qed.

Lemma lab_ie_impl_ex: forall t t', lab_term t -> (t -->[lx_i] t' \/ t -->[lx_e] t') -> t -->[lex] t'.
Proof.
    intros. destruct H0; destruct H0; destruct H0; destruct H0; destruct H1; generalize dependent t; generalize dependent t'; induction H1; intros.

    (*[> ------------------  Interna <]*)
    (*[> Base <]*)

    exists t s.
    split*. split*. 
    inversion H; subst. 
    constructor 8. admit. inversion H4; subst.
    constructor 1; auto.  constructor 2; subst. auto. 
    constructor 1; auto. constructor 3; auto.

    (* app_left *)
    apply EE_presv_lab_lex with (u := (pterm_app t u)) (u' := (pterm_app t' u)); auto.
    apply EE_clos_app_left. admit. 
    apply IHext_lab_contextual_closure; auto. constructor 1; auto. admit. constructor 1; auto.

    (* app_right *)
    apply EE_presv_lab_lex with (u := (pterm_app t u)) (u' := (pterm_app t u')); auto.
    apply EE_clos_app_right. admit. 
    apply IHext_lab_contextual_closure; auto. constructor 1; auto. admit. constructor 1; auto.

    (* abs *)
    apply EE_presv_lab_lex with (u := pterm_abs t) (u' := pterm_abs t'); auto.
    pick_fresh z.
    assert  (t^z-->[lex]t'^z).
    apply H0 with z; auto. constructor 1; auto. admit. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H5; destruct H5.
    apply notin_union in H5; destruct H5.
    apply notin_union in H5; destruct H5.
    apply EE_clos_abs with L.
    intros. pose proof red_rename_lab_lex. apply H11 with z; auto.

    (* outer sub *)
    apply EE_presv_lab_lex with (u := t[u]) (u' := t'[u]); auto.
    pick_fresh z.
    assert  (t^z-->[lex]t'^z).
    apply H1 with z; auto. constructor 1; auto. admit. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H6; destruct H6.
    apply notin_union in H6; destruct H6.
    apply notin_union in H6; destruct H6.
    apply notin_union in H6; destruct H6.
    apply EE_clos_outer_sub with L.
    intros. pose proof red_rename_lab_lex. apply H13 with z; auto.

    (* inner sub *)
    apply EE_presv_lab_lex with (u := t[u]) (u' := t[u']); auto.
    assert (u' =EE u'). constructor 1; auto.
    assert (u =EE u). constructor 1; auto.
    apply EE_lab_term in H3. inversion H3; subst.
    pose proof (IHext_lab_contextual_closure u' H4 u H9 H5).
    apply EE_clos_inner_sub; auto.
    auto.


    (* outer lsub *)
    apply EE_presv_lab_lex with (u := t[[u]]) (u' := t'[[u]]); auto.
    pick_fresh z.
    assert  (t^z-->[lex]t'^z).
    apply H2 with z; auto. constructor 1; auto. admit. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply EE_clos_outer_lsub with L.
    intros. pose proof red_rename_lab_lex. apply H14 with z; auto.

    (*[> -------------------------------------------------------  Externa <]*)
    (*[> Base <]*)
    exists (t) (s).  split*. split*.  
    inversion H; subst. 
    constructor 1.  constructor 1; auto.  
    constructor 1.  constructor 2; auto.  

    (* app_left *)
    apply EE_presv_lab_lex with (u := (pterm_app t u)) (u' := (pterm_app t' u)); auto.
    apply EE_clos_app_left. admit. 
    apply IHext_lab_contextual_closure; auto. constructor 1; auto. admit. constructor 1; auto.

    (* app_right *)
    apply EE_presv_lab_lex with (u := (pterm_app t u)) (u' := (pterm_app t u')); auto.
    apply EE_clos_app_right. admit. 
    apply IHext_lab_contextual_closure; auto. constructor 1; auto. admit. constructor 1; auto.

    (* abs *)
    apply EE_presv_lab_lex with (u := pterm_abs t) (u' := pterm_abs t'); auto.
    pick_fresh z.
    assert  (t^z-->[lex]t'^z).
    apply H0 with z; auto. constructor 1; auto. admit. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H5; destruct H5.
    apply notin_union in H5; destruct H5.
    apply notin_union in H5; destruct H5.
    apply EE_clos_abs with L.
    intros. pose proof red_rename_lab_lex. apply H11 with z; auto.

    (* outer sub *)
    apply EE_presv_lab_lex with (u := t[u]) (u' := t'[u]); auto.
    pick_fresh z.
    assert  (t^z-->[lex]t'^z).
    apply H1 with z; auto. constructor 1; auto. admit. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H6; destruct H6.
    apply notin_union in H6; destruct H6.
    apply notin_union in H6; destruct H6.
    apply notin_union in H6; destruct H6.
    apply EE_clos_outer_sub with L.
    intros. pose proof red_rename_lab_lex. apply H13 with z; auto.

    (* inner sub *)
    apply EE_presv_lab_lex with (u := t[u]) (u' := t[u']); auto.
    assert (u' =EE u'). constructor 1; auto.
    assert (u =EE u). constructor 1; auto.
    apply EE_lab_term in H3. inversion H3; subst.
    pose proof (IHext_lab_contextual_closure u' H4 u H9 H5).
    apply EE_clos_inner_sub; auto.
    auto.


    (* outer lsub *)
    apply EE_presv_lab_lex with (u := t[[u]]) (u' := t'[[u]]); auto.
    pick_fresh z.
    assert  (t^z-->[lex]t'^z).
    apply H2 with z; auto. constructor 1; auto. admit. constructor 1; auto. 
    apply notin_union in Fr; destruct Fr.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply notin_union in H7; destruct H7.
    apply EE_clos_outer_lsub with L.
    intros. pose proof red_rename_lab_lex. apply H14 with z; auto.
Qed.

Lemma lab_ex_eq_i_e: forall t t', lab_term t -> (t -->[lex] t' <-> (t -->[lx_i] t' \/ t -->[lx_e] t')).
Proof.
    split.
    intros; apply lab_ex_impl_i_e; auto.
    intros; apply lab_ie_impl_ex; auto.
Qed.

