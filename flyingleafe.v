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
    (Pi A (fun x => ((B x) -> Empty)) ~> ~' (Sigma A B)).
Proof.
  intros A B.
  intuition.
  case x.
  exact b.
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
    Definition equiv : Prop := reflexive /\ symmetric /\ transitive.
  End General_properties.
  
  Section Meta_relations.
    Definition inclusion (R1 R2 : Relation A) : Prop := forall x y : A, R1 x y -> R2 x y.
    Definition equal_rels (R1 R2 : Relation A) : Prop :=
      inclusion R1 R2 /\ inclusion R2 R1.
  End Meta_relations.
End Relation_definitions.

Section Extensionality_definition.
  Variable A B : Type.
  Variable R1 : Relation A.
  Variable R2 : Relation B.

  Definition extensional (f : A -> B) : Prop := forall x y, R1 x y -> R2 (f x) (f y).
End Extensionality_definition.

(* minimal_refl shouldn't be written as forall (S : Relation A), reflexive R -> inclusion R S.
Section Absurd_min_refl.
  Variable A : Type.
  Variable x : A.
  Variable R : Relation A.
  Hypothesis reflR : reflexive A R.
  Hypothesis minR: minimal_refl A R.

  Theorem min_refl : False.
  Proof.
    pose (S (x y : A) := False).
    unfold minimal_refl in minR.
    pose (RS := minR S reflR).
    unfold inclusion in RS.
    unfold S in RS.
    pose (notR := RS x x).
    
    absurd (R x x).
    unfold not.
      exact notR.
      unfold reflexive in reflR.
      exact (reflR x).
  Qed.
End Absurd_min_refl. *)

Section Theorem_about_min_refl_relation.
  Variable A : Type.
  Variable R : Relation A.
  Hypothesis reflR : reflexive A R.
  (* minimal reflexive relation *)
  Hypothesis minR : forall S : Relation A, reflexive A S -> inclusion A R S.

  Theorem min_reflex_rel_is_equiv_and_ext  :
    (equiv A R) /\ forall (B : Type) (R2 : Relation B), equiv B R2 -> forall f: A -> B, extensional A B R R2 f.
  Proof.
    refine (conj _ _).
      (* equiv *)
      unfold equiv.
      (* reflexive *)
      refine (conj _ _).
      exact reflR.
      refine (conj _ _).
        (* symmetric *)
        unfold symmetric.
        unfold inclusion in minR.
        pose (S x y := R y x).
        pose (R_symm := minR S reflR).
        unfold S in R_symm.
        exact R_symm.
        (* transitive *)
        unfold transitive.
        pose (S x y := forall z, R y z -> R x z).
        assert (reflS : reflexive A S).
          unfold reflexive, S.
          intuition.
        pose (RS := minR S reflS).
        unfold inclusion, S in RS.
        intros a b c R_ab.
        exact (RS a b R_ab c).
        
      (* ext *)
      intros B R2 eq.
      unfold extensional.
      unfold inclusion in minR.
      intros f x y.
      pose (S x y := R2 (f x) (f y)).
      assert (reflS : reflexive A S).
        unfold reflexive.
        unfold S.
        unfold equiv in eq.
        pose (reflR2 := proj1 eq).
        unfold reflexive in reflR2.
        intros a.
        exact (reflR2 (f a)).
      pose (RS := minR S reflS).
      unfold S in RS.
      exact (RS x y).
  Qed.
End Theorem_about_min_refl_relation.

Fixpoint eq_nat (n : nat) (m : nat) : Bool :=
  match n with
    O => match m with
           O => true'
         | S _ => false'
         end
  | S n' => match m with
              O => false'
            | S m' => eq_nat n m'
            end
  end.

Theorem th2 : forall (x y : nat), x == y <-> Is_true (eq_nat x y).
Proof.
  intros x y.
  unfold iff.
  refine (conj _ _).
    case x.
      case y.
      simpl.
      intuition.

      intros n.
      simpl.
      
  (* => *)
  intros x_y.
  rewrite x_y.
  elim x.
    simpl.
    simpl.

  (* <= *)
  intros eq_true.
  elim x.
    elim y.
      simpl. (* y = 0, eq_nat (0, 0) *)
      case False. (* y !=0 => Id (Nat, x, y) *)
    (* forall y, Is_true(eq_nat(x, y)) -> Id(N, x, y) *)
      (* forall y, Is_true(eq_nat((succ x), y)) -> Id(N, (succ x), y) *)
      elim y.
        (* y = 0 *)
        simpl.
        case False.
        (* y = succ u *)
        intros smth. (* *)
        simpl. (* forall y, Is_true(eq_nat(x, u)) -> Id(N, x, u) *)
        (* succ is extensional => Id(Nat, x, y) -> Id(Nat, succ x, succ y) *)
Qed.

(* Аксиомы выбора *)
(* (forall X: X != Empty) & (forall y in X: y != Empty) => Декартово произведение семейства x != Empty *)
(* S_w, (w in W) - семейство => (exists f: w -> Union[S, w in W]): (forall w in W) f(w) in S_w *)

Section TT.
  Definition Relation' (S T : Set) := S -> T -> Prop.
  Variable S T : Set.
  Variable R : Relation' S T.
  
  (* аксиома выбора *)
  (* Построим ans: Pi(S, [x] Sigma (T, R(x))) -> Sigma(S -> T, [f] Pi(S, [x]R(x, f(x))))
     Рассмотрим z in Pi(S, [x] Sigma(T, R(x)))
     x in S => z(x) in Sigma(T, R(x))
     fst(z(x)) in T
     snd(z(x)) in R(x, fst(z(x)))
     Заметим, что fst(z(x)) = (\x. fst(z(x))) (x)
     \y. snd(z(y)) in Pi(S, [z]R(z, (\x. fst(z(x))) (z)))
     \x. fst(z(x)) in S -> T
     pair (\x. fst(z(x)), \f. \y. snd(z(y))) in Sigma (f in (Pi (x in A) T(x))) Pi (x in S) R(x, f(x)) *)
  Theorem TT : forall (x : S), exists (y: T), R x y -> exists (f: S -> T), forall (x : S), R x (f x).
  Proof.
(*    intros x.
    assert (ans : Pi S (fun x => (Sigma T (R x))) -> Sigma (S -> T) (fun f => Pi S (fun x => (R x (f x))))).
      intros z.
      pose (zx := apply' _ _ z x).
      unfold apply' in zx.
      pose (fst_zx := fst' _ _ zx).
      pose (snd_zx := snd' _ _ zx).
      pose (lambdaX := fun x => fst' _ _ (apply' _ _ z x)).
      pose (tmp := snd' _ _ (apply' _ _ z x)).
      unfold apply' in tmp.
      pose (lambdaY := tmp).*)
    admit.
  Qed.
End TT.

(* Сетоид - пара из сета и отношения экв. на нем: (S, =_s) *)
(* R(x, y) [x in A : Setoid, y in B : Setoid], если forall x, y in A, u, v, in B: (R(x, u) /\ x =_A y /\ u =_B v) -> R(y, v) *)
(* ZF - аксиома выбора
   A, B - сетоиды, R - экст. отношение
   (forall x in A) (exists y in B) : R(x, y) -> (exists экстенц. f in A -> B) (forall x) R(x, f(x)) *)
(* Аксиома уникального выбора
   A, B - сетоиды, R - экст. отношение
   (forall x in A) (exists единственный y in B) : R(x, y) -> (exists экстенц. f in A -> B) (forall x) R(x, f(x))
   Proof.
     Возьмем f in TT.
     Рассмотрим x in A: R(x, f(x)).
     Рассмотрим u in A: R(u, f(u)).
     x =_A u => R(x, f(u)) => f(x) =_B f(u). *)

(* f, g: A -> B - экст. функции на сетоидах
   f и g экстенционально эквивалентны (f =_ext g), если (forall x in A) f(x) =_A = g(x) *)
(* |f| - сетоид без экв. (т.е. Set)
   f - (|f| : |A| -> |B|, ex_proof: extensional A B f) *)
(* f: B -> C, g: A -> B => f . g : A -> C = (h, ext_n),
   h = |f| . |g|, ext_n  = {x =_A y -> g(x) =_B g(y) -> f(g(x)) =_C f(g(y))}}; *)
(* Св-ва: f =_ext h => g =_ext k => f . g =_ext h . k
          h . (g  . f) =_ext (h . g) . f
          forall X, Y, f: X -> Y: f . id_X =_ext f & id_Y =_ext f *)
(* f: X -> Y инъективно, если forall x, y in X: f(x) =_Y f(y) => x = y *)
(* f: X -> Y сюръективно, если foral y in Y exists x in X f(x) =_Y y*)
(* биективно = инъективно /\ сюръективно *)