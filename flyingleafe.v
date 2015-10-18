Inductive Bool : Set :=
  true' : Bool
  | false' : Bool.

Definition if' (C:Bool -> Set) (b:Bool) (c1:C true') (c2:C false') :=
                  match b with
                    true' => c1
                    | false' => c2
end.

Definition or' (a b: Bool) :=
  if a then true' else b.
Definition and' (a b: Bool) :=
  if a then b else false'.

Infix "||" := or' : My_scope.
Infix "&&" := and' : My_scope.

Local Open Scope My_scope.

Section Elim_rule.
  Variable C: Bool -> Set.
  Variable c1: C true'.
  Variable c2: C false'.
  
  Theorem elim_rule_bool : (if' C true' c1 c2) = c1 /\ (if' C false' c1 c2) = c2.
  Proof.
    simpl.
    exact (conj (eq_refl c1) (eq_refl c2)).
  Qed.

End Elim_rule.

Inductive True' : Prop := I' : True'.
Inductive False' : Prop := .

Definition not' (A: Prop) := A -> False'.
Notation "~' A" := (not' A) (at level 75, right associativity) : My_scope.

Definition Is_true (a: Bool) : Prop :=
  match a with
    true' => True'
    | false' => False'
  end.

Theorem or_comm : forall (a b : Bool), Is_true(a || b) -> Is_true(b || a).
Proof.
  intros a b.
  case a, b.
    simpl.
    intros T.
    exact I'.

    simpl.
    intros T.
    exact I'.

    simpl.
    intros T.
    exact I'.

    simpl.
    intros F.
    case F.
Qed.

Inductive Empty: Set := .

Inductive Nat : Set :=
  zero : Nat
| succ : Nat -> Nat.

Fixpoint natrec (C: Nat -> Set) (d: C zero)
           (e: forall (x: Nat) (y: C x), C (succ x))
           (n: Nat) : C n
  := match n with
       zero => d
     | succ n' => e n' (natrec C d e n')
     end.

(* natrec definition works poorly with simpl. *)

(*Definition plus' (a b : Nat) : Nat := natrec (fun x => Nat) a
                                            (fun _ y => succ y) b.
Definition mul' (n m: Nat) : Nat := natrec (fun _ => Nat) zero
                                           (fun _ y => plus' y n) m.*)

Fixpoint plus' (a b : Nat) :=
  match b with
    zero => a
  | (succ b_) => succ (plus' a b_)
  end.

Fixpoint mul' (a b : Nat) :=
  match b with
    zero => zero
  | (succ b_) => plus' (mul' a b_) a
  end.

Infix "+" := plus' : My_scope.
Infix "*" := mul' : My_scope.

Inductive Id {A: Type} (x: A) : A -> Type :=
  id : Id x x.

Infix "==" := Id (at level 60) : My_scope.
Notation "x /= y" := (~(x == y)) (at level 60) : My_scope.

Inductive And (A B : Prop) : Prop :=
  conj' : A -> B -> And A B.
Inductive Or (A B : Prop) : Prop :=
  inl' : A -> Or A B
| inr' : B -> Or A B.

Infix "/.\" := And (at level 80) : My_scope.
Infix "\./" := Or (at level 85) : My_scope.
Arguments conj'.
Arguments inl'.
Arguments inr'.

Theorem zero_neutral_right : forall n, Id (n + zero) n.
Proof.
  intros n.
  unfold plus'.
  simpl.
  exact (id _).
Qed.

Theorem zero_neutral_left : forall n, Id  (zero + n) n.
Proof.
  intros n.
  unfold plus'.
  elim n.
    simpl.
    exact (id _).

    simpl.
    intros n0 ind_hyp.
    rewrite ind_hyp.
    exact (id _).
Qed.

Theorem plus_comm : forall n m, Id  (n + m) (m + n).
Proof.
  intros n m.
  elim n.
    (* base n *)
    elim m.
      (* base m *)
      exact (id _).

      (* inductive m *)
      intros n0.
      unfold plus'.
      simpl.
      intros h.
      rewrite h.
      exact (id _).

    intros n0.
    unfold plus'.  
    intros hyp_n.
    simpl.
    rewrite <- hyp_n.
    (* inductive n *)
    elim m.
      (* base m *)
      simpl.
      exact (id _).

      (* inductive m *)
      intros n1.
      simpl.
      intros hyp_m.
      rewrite hyp_m.
      exact (id _).
Qed.

Theorem plus_assoc : forall a b c : Nat, Id  ((a + b) + c) (a + (b + c)).
Proof.
  intros a b c.
  unfold plus'.
  elim c.
    simpl.
    exact (id _).

    intros n hyp.
    simpl.
    rewrite hyp.
    exact (id _).
Qed.

Theorem mul_comm : forall a b c : Nat, Id (a * b) (b * a).
Proof.
  intros a b c.
  elim a.
    unfold mul'.
    simpl.
    elim b.
      intuition.
      intuition.
      
    intros n hyp.
    simpl.
    rewrite <- hyp.
    elim b.
      simpl.
      exact (id _).

      intros n0 hyp1.
      (* here natrec version doesn't work properly *)
      simpl.
      rewrite hyp1.
      rewrite (plus_assoc (n * n0) n0 n).
      rewrite (plus_comm n0 n).
      rewrite <- (plus_assoc (n * n0) n n0).
      exact (id _).
Qed.

Inductive Pi (A : Set) (B : A -> Set) : Set :=
  lambda : (forall x : A, B x) -> Pi A B.

Definition apply' (A : Set) (B: A -> Set) (y: Pi A B) (x: A) :=
  match y with
    (lambda f) => f x
  end.

Notation "A ~> B" := (Pi A (fun _ => B)) (at level 60, right associativity) : My_scope.
Notation "~' A" := (A ~> Empty) : My_scope.

Definition lambda' (A B : Set) (f : A -> B) : A ~> B :=
  lambda A (fun _ => B) f.
Definition apply'' (A B : Set) (f : A ~> B) (x : A) :=
  apply' A (fun _ => B) f x.

Theorem add_double_not : forall A : Set, A ~> ~' ~' A.
Proof.
  intros A.
  pose (f := lambda' A (~' ~' A) (fun x => lambda' (~' A) Empty (fun y => apply'' A Empty y x))).
  exact (f).
Qed.

Inductive orS (A B : Set) : Set :=
  inlS : A -> orS A B
| inrS : B -> orS A B.

Definition when (A B : Set) (C : orS A B -> Set) (p : orS A B) (f : forall x : A, C (inlS A B x) ) (g : forall y : B, C (inrS A B y)) :=
  match p with
    (inlS a) => f a
  | (inrS b) => g b
  end.

Inductive Sigma (A : Set) (B : A -> Set) : Set :=
  pair : forall (a : A) (b : B a), Sigma A B.

Definition split' (A : Set) (B : A -> Set) (C : Sigma A B -> Set) (p : Sigma A B) (f : forall (x : A) (y : B x), C (pair A B x y)): C(p) :=
  match p with
    (pair x y) => f x y end.
                                        

Definition fst' (A : Set) (B : A -> Set) (p : Sigma A B) : A :=
  split' A B (fun _ => A) p (fun a _ => a).

Definition snd' (A : Set) (B : A -> Set) (p : Sigma A B) : B (fst' A B p) :=
  split' A B (fun x => B(fst' A B x)) p (fun _ b => b).

Theorem forall_is_exists : forall (A : Set) (B : A -> Set),
    (Pi A (fun x => ~' (B x)) ~> ~' (Sigma A B)).
Proof.
  admit.
Qed.

Inductive List (A : Set) : Set :=
  null : List A
| new : A -> List A -> List A.

Definition head (A : Set) (def : A) (l : List A) : A :=
  match l with
    null => def
  | (new a tail) => a
  end.

Definition headP (A : Set) (lst : List A) (proof : lst /= null A) : A :=
  (match lst as b return (lst == b -> A) with
   | null => (fun foo : lst == null A =>
                match (proof foo) return A with
                end)
   | (new a tail) => (fun foo : lst == (new A a tail) => a)
  end) (id _).

Definition tail (A : Set) (l : List A) : List A :=
  match l with
    null => l
  | (new x xs) => xs
  end.

Fixpoint foldr (A : Set) (C : List A -> Set) (c : C (null A)) (l : List A) (f : forall (x: A) (lst : List A) (c : C lst), C(new A x lst)) : C (l) :=
  match l with
    null => c
  | (new x xs) => f x xs (foldr A C c xs f)
  end.
  
Section Relation_definitions.
  Variable A : Type.
  Definition Relation (S : Type) := S -> S -> Prop.
  Variable R : Relation A.
  Section General_properties.
    Definition reflexive : Prop := forall a, R a a.
    Definition symmetric : Prop := forall a b, R a b -> R b a.
    Definition transitive : Prop := forall a b c, R a b -> R b c -> R a c.
    Definition equiv : Prop := reflexive /.\ symmetric /.\ transitive.
  End General_properties.
  
  Section Meta_relations.
    Definition inclusion (R1 R2 : Relation A) : Prop := forall x y : A, R1 x y -> R2 x y.
    Definition equal_rels (R1 R2 : Relation A) : Prop :=
      inclusion R1 R2 /.\ inclusion R2 R1.
    Definition minimal_refl : Prop :=
      forall (S : Relation A), reflexive -> inclusion R S. 
  End Meta_relations.
End Relation_definitions.

Section Extensionality_definition.
  Variable A B : Type.
  Variable R1 : Relation A.
  Variable R2 : Relation B.

  Definition extensional (f : A -> B) : Prop := forall x y, R1 x y -> R2 (f x) (f y).
End Extensionality_definition.

Section Theorem_about_min_refl_relation.
  Variable A : Type.
  Variable R : Relation A.
  Hypothesis reflR : reflexive A R.
  Hypothesis minR : minimal_refl A R.
  Theorem min_reflex_rel_is_equiv_and_ext  :
    (equiv A R) /.\ forall (B : Type) (R2 : Relation B), equiv B R2 -> forall f: A -> B, extensional A B R R2 f.
  Proof.
    admit.
  Qed.
End Theorem_about_min_refl_relation.
