Require Import Bool.
Require Import List.

Theorem my_first_proof__again__again : (forall A : Prop, A -> A).
Proof.
  intros A.
  intros proof_of_A.
  exact proof_of_A.
Qed.

Theorem forward_small : (forall A B : Prop, A -> (A->B) -> B).
Proof.
 intros A.
 intros B.
 intros proof_of_A.
 intros A_implies_B.
 pose (proof_of_B := A_implies_B proof_of_A).
 exact proof_of_B.
Qed.

Theorem backward_small : (forall A B : Prop, A -> (A->B)->B).
Proof.
 intros A B.
 intros proof_of_A A_implies_B.
 refine (A_implies_B _).
   exact proof_of_A.
Qed.

Theorem backward_large : (forall A B C : Prop, A -> (A->B) -> (B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B B_implies_C.
 refine (B_implies_C _).
   refine (A_implies_B _).
     exact proof_of_A.
Qed.

Theorem backward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
  intros A B C.
  intros proof_of_A A_implies_B A_imp_B_imp_C.
  refine (A_imp_B_imp_C _ _).
      exact proof_of_A.

      refine (A_implies_B _).
          exact proof_of_A.
Qed.

Theorem False_cannot_be_proven__again : ~False.
Proof.
  intros proof_of_False.
  case proof_of_False.
Qed.


Theorem absurd2 : forall A C : Prop, A -> ~ A -> C.
Proof.
  intros A C.
  intros proof_of_A proof_that_A_cannot_be_proven.
  unfold not in proof_that_A_cannot_be_proven.
  pose (proof_of_False := proof_that_A_cannot_be_proven proof_of_A).
  case proof_of_False.
Qed.

Theorem and_commutes : (forall A B, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  case A_and_B.
    intros proof_of_A proof_of_B.
    refine (conj _ _).
      exact proof_of_B.

      exact proof_of_A.
Qed.

Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
    intros H.
    case a, b.
      simpl.
      refine (or_introl _).
        exact I.

      simpl.
      exact (or_introl I).

      exact (or_intror I).

      simpl in H.
      case H.

    intros H.
    case a, b.
      simpl.
      exact I.

      exact I.

      exact I.

      case H.
         intros A.
         simpl in A.
         case A.

         intros B.
         simpl in B.
         case B.
Qed.


Theorem negb_is_not : (forall a, Is_true (negb a) <-> (~(Is_true a))).
Proof.
  intros a.
  unfold iff.
  refine (conj _ _).
    case a.
      simpl.
      intros F.
      case F.

      simpl.
      unfold not.
      intros T F.
      case F.

    case a.
      simpl.
      unfold not.
      intros Impl.
      pose (F := Impl I).
      case F.

      simpl.
      unfold not.
      intros Impl.
      exact I.
Qed.

Theorem forall_exists : (forall P : Set->Prop, (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
  intros P.
  intros forall_x_not_Px.
  unfold not.
  intros exists_x_Px.
  destruct exists_x_Px as [ witness proof_of_Pwitness].
  pose (not_Pwitness := forall_x_not_Px witness).
  unfold not in not_Pwitness.
  pose (proof_of_False := not_Pwitness proof_of_Pwitness).
  case proof_of_False.
Qed.

Theorem thm_eq_sym : (forall x y : Set, x = y -> y = x).
Proof.
  intros x y.
  intros x_y.
  destruct x_y as [].
  exact (eq_refl x).
Qed.

Theorem thm_eq_trans__again : (forall x y z: Set, x = y -> y = z -> x = z).
Proof.
  intros x y z.
  intros x_y y_z.
  rewrite x_y.
  rewrite <- y_z.
  exact (eq_refl y).
Qed.

Theorem neq_nega: (forall a, a <> (negb a)).
Proof.
  intros a.
  unfold not.
  case a.
    intros a_eq_neg_a.
    simpl in a_eq_neg_a.
    discriminate a_eq_neg_a.

    intros a_eq_neg_a.
    simpl in a_eq_neg_a.
    discriminate a_eq_neg_a.
Qed.

Theorem plus_n_O : (forall n, n + O = n).
Proof.
  intros n.
  elim n.
    simpl.
    exact (eq_refl O).

    intros n'.
    intros inductive_hypothesis.
    simpl.
    rewrite inductive_hypothesis.
    exact (eq_refl (S n')).
Qed.

Theorem plus_sym: (forall n m, n + m = m + n).
Proof.
  intros n m.
  elim n.
    elim m.
      exact (eq_refl (O + O)).

      intros m0.
      intros hyp.
      simpl.
      rewrite <- hyp.
      simpl.
      exact (eq_refl (S m0)).

      intros n'.
      intros inductive_hyp_n.
      simpl.
      rewrite inductive_hyp_n.
      elim m.
        simpl.
        exact (eq_refl (S n')).

        intros m'.
        intros inductive_hyp_m.
        simpl.
        rewrite inductive_hyp_m.
        simpl.
        exact (eq_refl (S (m' + S n'))).
Qed.

Theorem cons_adds_one_to_length : 
   (forall A:Type, 
   (forall (x : A) (lst : list A), 
   length (x :: lst) = (S (length lst)))).
Proof.
  intros A.
  intros x lst.
  simpl.
  exact (eq_refl (S (length lst))).
Qed.

Theorem nonEmptyCons :
    (forall A:Type,
    (forall (x: A) (lst : list A),
        (x :: lst) <> nil)).
Proof.
  intros A.
  intros x lst.
  unfold not.
  intros premise.  
  discriminate premise.
Qed.

Theorem app_nil_l : (forall A:Type, (forall l:list A, nil ++ l = l)).
Proof.
  intros A.
  intros lst.
  simpl.
  exact (eq_refl (lst)).
Qed.

Theorem app_nil_r : (forall A:Type, (forall l:list A, l ++ nil = l)).
Proof.
  intros A lst.
  elim lst.
    simpl.
    exact (eq_refl _).

    intros a lst' hyp.
    simpl.
    rewrite hyp.
    exact (eq_refl _).
Qed.

Theorem app_comm_cons : forall A (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
Proof.
  intros A x y a.
  simpl.
  exact (eq_refl _).
Qed.

Theorem app_assoc : forall A (l m n:list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  elim l.
    simpl.
    exact (eq_refl _).

    intros a l0 hyp.
    simpl.
    rewrite hyp.
    exact (eq_refl _).
Qed.