(***************************************************************************
* Formalization of SN for the lambda_ex calculus			   *
*									   *
* General rewriting definitions	for explicit substitutions		   * 
*									   *
* Fabien Renaud & St\u00e9phane Zimmerman, 2011				   *
* Flavio L. C. de Moura & Daniel L. Ventura & Washington R. Segundo, 2016  *
***************************************************************************)

Require Import Metatheory.
Require Import LambdaES_Defs.
Require Import List.

(** Given a relation Red, constructs its contextual closure. The contextual closure of a reduction is build in such a way that regularity is preserved. In particular, note the condition requiring that only terms can be introduced by the constructors for applications and explicit substitutions. *)
Inductive L_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | L_redex : forall t s, Red t s -> L_contextual_closure Red t s
  | L_app_left : forall t t' u, L_contextual_closure Red t t' -> Lterm u ->
	  		      L_contextual_closure Red (pterm_app t u) (pterm_app t' u)
  | L_app_right : forall t u u', L_contextual_closure Red u u' -> Lterm t ->
	  		       L_contextual_closure Red (pterm_app t u) (pterm_app t u')
  | L_abs_in : forall t t' L, (forall x, x \notin L -> L_contextual_closure Red (t^x) (t'^x)) ->
                            L_contextual_closure Red (pterm_abs t) (pterm_abs t').

Inductive ES_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | ES_redex : forall t s, Red t s -> ES_contextual_closure Red t s
  | ES_app_left : forall t t' u, ES_contextual_closure Red t t' -> term u ->
	  		      ES_contextual_closure Red (pterm_app t u) (pterm_app t' u)
  | ES_app_right : forall t u u', ES_contextual_closure Red u u' -> term t ->
	  		       ES_contextual_closure Red (pterm_app t u) (pterm_app t u')
  | ES_abs_in : forall t t' L, (forall x, x \notin L -> ES_contextual_closure Red (t^x) (t'^x)) ->
                            ES_contextual_closure Red (pterm_abs t) (pterm_abs t')
  | ES_subst_left : forall t t' u L, (forall x, x \notin L -> ES_contextual_closure Red (t^x) (t'^x)) -> 
	        term u -> ES_contextual_closure Red  (pterm_sub t u) (pterm_sub t' u)
  | ES_subst_right : forall t u u', ES_contextual_closure Red u u' -> term t ->
	  	ES_contextual_closure Red  (pterm_sub t u) (pterm_sub t u').

Inductive ESlab_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
| ESlab_redex : forall t s, Red t s -> ESlab_contextual_closure Red t s
| ESlab_app_left : forall t t' u, ESlab_contextual_closure Red t t' -> term u ->
	  		          ESlab_contextual_closure Red (pterm_app t u) (pterm_app t' u)
| ESlab_app_right : forall t u u', ESlab_contextual_closure Red u u' -> term t ->
	  		           ESlab_contextual_closure Red (pterm_app t u) (pterm_app t u')
| ESlab_abs_in : forall t t' L, (forall x, x \notin L -> ESlab_contextual_closure Red (t^x) (t'^x)) ->
                                ESlab_contextual_closure Red (pterm_abs t) (pterm_abs t')
| ESlab_subst_left : forall t t' u L, (forall x, x \notin L -> ESlab_contextual_closure Red (t^x) (t'^x)) -> 
	                              term u -> ESlab_contextual_closure Red  (pterm_sub t u) (pterm_sub t' u)
| ESlab_subst_right : forall t u u', ESlab_contextual_closure Red u u' -> term t ->
	  	                     ESlab_contextual_closure Red  (pterm_sub t u) (pterm_sub t u')
| ESlab_lsubst_left : forall t t' u L, (forall x, x \notin L -> ESlab_contextual_closure Red (t^x) (t'^x)) -> 
	                               term u -> ESlab_contextual_closure Red  (pterm_sub t u) (pterm_sub t' u)
| ESlab_lsubst_right : forall t u u', ESlab_contextual_closure Red u u' -> term t -> 
	  	                      ESlab_contextual_closure Red  (pterm_sub' t u) (pterm_sub' t u').

(** Given a relation Red, constructs its parallel contextual closure *)
Inductive L_p_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | L_p_redex : forall t s, Red t s -> L_p_contextual_closure Red t s
  | L_p_app : forall t t' u u', L_p_contextual_closure Red t t' -> L_p_contextual_closure Red u u' ->
	  		L_p_contextual_closure Red (pterm_app t u) (pterm_app t' u')
  | L_p_abs_in : forall t t' L, (forall x, x \notin L -> L_p_contextual_closure Red (t^x) (t'^x)) -> 
               L_p_contextual_closure Red (pterm_abs t) (pterm_abs t').

Inductive ES_p_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | ES_p_redex : forall t s, Red t s -> ES_p_contextual_closure Red t s
  | ES_p_app : forall t t' u u', ES_p_contextual_closure Red t t' -> ES_p_contextual_closure Red u u' ->
	  		ES_p_contextual_closure Red (pterm_app t u) (pterm_app t' u')
  | ES_p_abs_in : forall t t' L, (forall x, x \notin L -> ES_p_contextual_closure Red (t^x) (t'^x)) -> 
               ES_p_contextual_closure Red (pterm_abs t) (pterm_abs t')
  | ES_p_subst : forall t t' u u' L, (forall x, x \notin L -> ES_p_contextual_closure Red (t^x) (t'^x)) -> 
              ES_p_contextual_closure Red u u' -> 
	      ES_p_contextual_closure Red  (pterm_sub t u) (pterm_sub t' u').

Inductive ESlab_p_contextual_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | ESlab_p_redex : forall t s, Red t s -> ESlab_p_contextual_closure Red t s
  | ESlab_p_app : forall t t' u u', ESlab_p_contextual_closure Red t t' -> ESlab_p_contextual_closure Red u u' ->
	  		          ESlab_p_contextual_closure Red (pterm_app t u) (pterm_app t' u')
  | ESlab_p_abs_in : forall t t' L, (forall x, x \notin L -> ESlab_p_contextual_closure Red (t^x) (t'^x)) -> 
                                  ESlab_p_contextual_closure Red (pterm_abs t) (pterm_abs t')
  | ESlab_p_subst : forall t t' u u' L, (forall x, x \notin L -> ESlab_p_contextual_closure Red (t^x) (t'^x)) -> 
                                      ESlab_p_contextual_closure Red u u' -> 
	                              ESlab_p_contextual_closure Red  (pterm_sub t u) (pterm_sub t' u')
  | ESlab_p_lsubst : forall t t' u u' L, (forall x, x \notin L -> ESlab_p_contextual_closure Red (t^x) (t'^x)) -> 
                                       ESlab_p_contextual_closure Red u u' -> 
	                               ESlab_p_contextual_closure Red (t[[u]]) (t'[[u']]).

Hint Constructors L_contextual_closure ES_contextual_closure ESlab_contextual_closure L_p_contextual_closure ES_p_contextual_closure ESlab_p_contextual_closure.

(** Given a relation Red, constructs its transitive closure *)
Inductive trans_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | one_step_reduction : forall t u, Red t u -> trans_closure Red t u
  | transitive_reduction : forall t u v, Red t u -> trans_closure Red u v -> trans_closure Red t v.

(** Given a relation Red, constructs its transitive reflexive closure *)
Inductive star_closure (Red : pterm -> pterm -> Prop) : pterm -> pterm -> Prop :=
  | reflexive_reduction : forall t, star_closure Red t t
  | star_trans_reduction : forall t u, trans_closure Red t u -> star_closure Red t u.

(** Given a reduction, the composition of two star closure is still a star closure *)
Lemma star_transitive_closure:
    forall (Red: pterm -> pterm -> Prop) (t u v : pterm), 
     Red t u -> star_closure Red u v -> star_closure Red t v.
Proof. 
 intros Red t u v H0 H1.
 induction H1. 
   apply star_trans_reduction.
   apply one_step_reduction.
   assumption.
   apply star_trans_reduction.
   apply transitive_reduction with (u := t0); trivial.
Qed.

Lemma transitive_closure_composition : 
    forall Red t u v, trans_closure Red t u -> trans_closure Red u v -> trans_closure Red t v.
Proof.
  intros.
  induction H.
    apply transitive_reduction with (u := u); trivial.
    apply transitive_reduction with (u := u) ; auto.
Qed.

Lemma star_transitive_closure_composition_1 :
    forall Red t u v, trans_closure Red t u -> star_closure Red u v -> star_closure Red t v.
Proof.
  intros.
  induction H0. 
    apply star_trans_reduction; trivial.
    apply star_trans_reduction.
    apply transitive_closure_composition with (u := t0); trivial.
Qed.
  
Lemma star_transitive_closure_composition_2 :
    forall Red t u v, star_closure Red t u -> trans_closure Red u v -> star_closure Red t v.
Proof.
  intros.
  induction H.
    apply star_trans_reduction; trivial.
    apply star_trans_reduction.
    apply transitive_closure_composition with (u := u); trivial.
Qed.
    
Lemma star_closure_composition:
    forall Red t u v, star_closure Red t u -> star_closure Red u v -> star_closure Red t v.
Proof.
  intros.
  induction H.
  assumption.
  apply star_transitive_closure_composition_1 with (u := u); assumption.
Qed.

Lemma transitive_star_derivation: 
    forall (Red : pterm -> pterm -> Prop) (t v: pterm), 
    trans_closure Red t v -> exists u, Red t u /\  star_closure Red u v.
Proof.
  intros.
  case H. intros t' u' H0.
  exists u'. split; trivial.
  apply reflexive_reduction.
  intros t' u' v' H0 H1. exists u'.
  split; trivial.
  apply star_trans_reduction; trivial.
Qed.

Lemma transitive_star_derivation': 
    forall (Red : pterm -> pterm -> Prop) (t v: pterm), 
    trans_closure Red t v <-> (Red t v \/ (exists u, Red t u /\  (exists u', star_closure Red u u' /\ Red u' v))).
Proof.
 intros. split. intros. destruct H.
 left; trivial. right. exists u. split; trivial. 
 clear H. induction H0. exists t0. split; trivial.
 apply reflexive_reduction. destruct IHtrans_closure.
 exists x. split. apply star_transitive_closure with (u := u); trivial.
 apply H1. apply H1. intros. case H. intro.
 apply one_step_reduction; trivial. intro.
 destruct H0. destruct H0. destruct H1. destruct H1. destruct H1.
 apply transitive_reduction with (u := t0); trivial.
 apply one_step_reduction; trivial.
 apply transitive_reduction with (u := t0); trivial. 
 apply transitive_closure_composition with (u := u); trivial.
 apply one_step_reduction; trivial.
Qed.

Lemma star_transitive_derivation: forall (Red : pterm -> pterm -> Prop) (t u: pterm), 
      star_closure Red t u <-> (t = u \/ trans_closure Red t u).
Proof.
 intros. split. intro. destruct H.
 left. reflexivity. right; trivial.
 intro. case H. 
 clear H. intro H. rewrite H. apply reflexive_reduction.
 clear H. intro H. apply star_trans_reduction; trivial.
Qed.

Lemma trans_R1_R2 : forall (R1 R2: pterm -> pterm -> Prop), 
                           (forall t t', R1 t t' -> R2 t t') -> 
                           (forall t t', trans_closure R1 t t' -> trans_closure R2 t t').
Proof.
 intros R1 R2 H t t' H'. induction H'.
 apply one_step_reduction. apply H; trivial.
 apply transitive_reduction with (u := u); trivial.
 apply H; trivial.
Qed.

Lemma star_R1_R2: forall (R1 R2: pterm -> pterm -> Prop), 
                           (forall t t', R1 t t' -> R2 t t') -> 
                           (forall t t', star_closure R1 t t' -> star_closure R2 t t').
Proof.
 intros R1 R2 H t t' H'. induction H'.
 apply reflexive_reduction.
 apply star_trans_reduction.
 apply trans_R1_R2 with (R1 := R1); trivial.
Qed.
