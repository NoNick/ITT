Module Basics.

(* Для начала, как обычно, заново определим ложь, конъюнкцию и дизъюнкцию *)
(* Наши определения будут немного отличаться от предыдущих *)

Definition False : Prop := forall P:Prop, P.

Definition not : Prop -> Prop := fun A:Prop => A -> False.

Notation "~' x" := (not x) (at level 75, right associativity).

(* Конъюнкция *)
Definition and : Prop->Prop->Prop := fun A B:Prop => forall P:Prop, (A -> B -> P) -> P.

Notation "A /_\ B" := (and A B) (at level 80).

(* Аксиома A → B → A /\ B *)
Theorem andI : forall (A B : Prop), A -> B -> A /_\ B.
Proof.
    exact (fun A B a b P H => H a b).
    (* Также можно доказать так:
    intros A B a b.
    unfold and.
    intros P H.
    exact (H a b).
    *)
Qed.

(* Дизъюнция *)
Definition or : Prop->Prop->Prop := fun (A B : Prop) => forall P:Prop, (A -> P) -> (B -> P) -> P.

Notation "A \_/ B" := (or A B) (at level 85).

(* Аксиома A → A \/ B *)
Theorem orIL : forall (A B : Prop), A -> A \_/ B.
Proof.
    exact (fun A B a P H1 H2 => H1 a).
Qed.

(* Аксиома B → A \/ B *)
Theorem orIR : forall (A B : Prop), B -> A \_/ B.
Proof.
    exact (fun A B b P H1 H2 => H2 b).
Qed.

(* Эквивалентность через конъюнкцию *)
Definition iff : Prop->Prop->Prop := fun (A B:Prop) => (A -> B) /_\ (B -> A).

Notation "A <=> B" := (iff A B) (at level 95).


(* Теперь начнем развлекаться со множествами *)

(* Для начала определим множество *)
Parameter set : Type.

(* Равенство двух множеств *)
(* Любое суждение, верное для одного множества, верно и для другого *)
Definition eq : set->set->Prop := fun (x y : set) => forall Q:set -> Prop, Q x -> Q y.

Notation "x == y" := (eq x y) (at level 70).
Notation "x /= y" := (~' x == y) (at level 70).

(* Докажем рефлексивность такого равенства *)
Theorem eqI : forall x:set, x == x.
Proof.
    exact (fun x q H => H).
Qed.

Require Coq.Setoids.Setoid.

(* И симметричность *)
Theorem eq_sym : forall x y:set, x == y -> y == x.
Proof.
  intros.
  unfold eq.
  pose (Q := fun y => y == x).
  pose (ret := H Q).
  assert (Q x).
    exact (eqI x).
  exact (ret H0). 
Qed.

(* Определим квантор существования для set *)
Definition ex : (set->Prop)->Prop := fun P:set->Prop => forall Q:Prop, (forall x, P x -> Q) -> Q.

Notation "'exists' x , p" := (ex (fun x => p))
  (at level 200, x ident).

(* P x -> \exists x P x *)
Theorem exI : forall P:set->Prop, forall x:set, P x -> exists x, P x.
Proof.
    exact (fun P x H1 Q H2 => H2 x H1).
Qed.

(* Такой же квантор существования, только для функций вида set → set *)
Definition ex_f : ((set->set)->Prop)->Prop := fun P:(set->set)->Prop => forall Q:Prop, (forall x, P x -> Q) -> Q.

Notation "'existsf' x , p" := (ex_f (fun x => p))
  (at level 200, x ident).

Theorem exI_f : forall P:(set->set)->Prop, forall F:set->set, P F -> existsf F, P F.
Proof.
    exact (fun P x H1 Q H2 => H2 x H1).  
Qed.

(* Квантор единственного существования *)
Definition exu : (set->Prop)->Prop := fun P:set->Prop => (exists x, P x) /_\ (forall x y:set, P x -> P y -> x == y).

Notation "'exists!' x , p" := (exu (fun x => p))
  (at level 200, x ident).

Theorem exuI : forall P:set->Prop, (exists x, P x) -> (forall x y:set, P x -> P y -> x == y) -> exists! x, P x.
Proof.
  intros.
  unfold exu, and.
  intros.
  exact (H1 H H0).
Qed.

(* Оператор описания множества *)
(* Пригодится позже в доказательствах, пока можно пропустить *)
Parameter Descr : ((set->Prop)->set).

Axiom DescrR : forall P:set->Prop, (exists! x, P x) -> P (Descr P).


(* Определим базовые отношения, свойства и операции над множествами *)

(* In - отношение "x принадлежит множеству y" *)

Parameter In : set->set->Prop.

Notation "x ':e' y" := (In x y) (at level 70).
Notation "x '/:e' y" := (~' (In x y)) (at level 70).

(* Subq - отношение "A вложено в B" *)

Definition Subq : set->set->Prop :=
fun X Y => forall x:set, x :e X -> x :e Y.

Notation "X 'c=' Y" := (Subq X Y) (at level 70).
Notation "X '/c=' Y" := (~' (Subq X Y)) (at level 70).

Lemma Subq_ref : forall X:set, X c= X.
Proof.
    intros X x H1. exact H1.
Qed.

Lemma Subq_tra : forall X Y Z:set, X c= Y -> Y c= Z -> X c= Z.
Proof.
  intros X Y Z.
  unfold Subq.
  intros.
  pose (tmp := H x H1).
  exact (H0 x tmp).
Qed.

(* Равенство множеств - это вложенность множеств друг в друга *)

Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X == Y.

(* Равенство в другую сторону *)

Theorem set_ext_inv : forall X Y:set, X == Y -> (X c= Y /_\ Y c= X).
Proof.
  intros.
  unfold eq in H.
  refine (andI (X c= Y) (Y c= X) _ _).
    unfold Subq.
    intros.
    pose (P Z := x :e Z).
    pose (tmp := H P).
    unfold P in tmp.
    exact (tmp H0).

    unfold Subq.
    intros.
    pose (Q := fun Z => x :e Z -> x :e X).
    pose (H' := H Q).
    unfold Q in H'.
    assert (x :e X -> x :e X).
      exact (fun smth => smth).
    exact (H' H1 H0).
Qed.

(* Индукция по множеству *)

Axiom In_ind : forall P:set->Prop, (forall X:set, (forall x, x :e X -> P x) -> P X) -> forall X:set, P X.

Parameter Empty : set.

Axiom EmptyAx : ~' exists x, x :e Empty.

Lemma EmptyE : forall x:set, x /:e Empty.
Proof.
  unfold not.
  intros.
  pose (ax := EmptyAx).
  unfold not in ax.
  pose (tmp := exI (fun x => x :e Empty) x H).
  exact (ax tmp).
Qed.

(* Union(X) - операция объединения всех подмножеств X *)
(* То есть Union(X) = {x | \exists Y: x \in Y, Y \in X} *)

Parameter Union : set->set.

Axiom UnionEq : forall X:set, forall x:set, x :e Union X <=> exists Y, x :e Y /_\ Y :e X.

(* A /_\ B → A *)
Theorem andIA : forall (A B : Prop), A /_\ B -> A.
Proof.
  intros.
  unfold and in H.
  pose (H' := H A).
  intuition.
Qed.

Theorem andIB : forall (A B : Prop), A /_\ B -> B.
Proof.
  intros.
  unfold and in H.
  pose (H' := H B).
  intuition.
Qed.
                                       
Lemma UnionE :
forall X x:set, x :e (Union X) -> exists Y, x :e Y /_\ Y :e X.
Proof.
  intros.
  unfold ex.
  intros.
  pose (ax := UnionEq X x).
  unfold iff in ax.
  pose (exY := (andIA _ _ ax) H Q).
  exact (exY H0).
Qed.

Lemma UnionI :
forall X x Y:set, x :e Y -> Y :e X -> x :e (Union X).
Proof.
  intros.
  unfold ex.
  intros.
  pose (ax := UnionEq X x).
  unfold iff in ax.
  pose (xInUn := andIB _ _ ax).
  assert (exists Y0, x :e Y0 /_\ Y0 :e X).
    unfold ex.
    intros.
    assert (x :e Y /_\ Y :e X).
      unfold and.
      intros.
      exact (H2 H H0).
    exact (H1 Y H2).
  exact (xInUn H1).
Qed.

(* Power(X) - множество всех подмножеств X *)

Parameter Power : set->set.

Axiom PowerEq : forall X Y:set, Y :e Power X <=> Y c= X.

Lemma PowerE : forall X Y:set, Y :e Power X -> Y c= X.
Proof.
  pose (ax := PowerEq).
  unfold iff in ax.
  intros X Y.
  exact (andIA _ _ (ax X Y)).
Qed.

Lemma PowerI : forall X Y:set, Y c= X -> Y :e (Power X).
Proof.
  pose (ax := PowerEq).
  unfold iff in ax.
  intros X Y.
  exact (andIB _ _ (ax X Y)).
Qed.

Lemma In_Power : forall X:set, X :e Power X.
Proof.
  intros.
  pose (refl := Subq_ref X).
  exact (PowerI X X refl).
Qed.

(* Sep(X, P) = {x | x :e X, P x} *)

Parameter Sep : set -> (set -> Prop) -> set.

Notation "{ x :i X | P }" := (Sep X (fun x:set => P)).

Axiom SepEq : forall X:set, forall P:set -> Prop, forall x, x :e {z :i X | P z} <=> x :e X /_\ P x.

Lemma SepI : forall X:set, forall P:set -> Prop, forall x:set,
 x :e X -> P x -> x :e {z :i X|P z}.
Proof.
  intros.
  pose (ax := SepEq).
  unfold iff in ax.
  pose (tmp := andIB _ _ (ax X P x)).
  assert (x :e X /_\ P x).
    unfold and.
    intros.
    exact (H1 H H0).
  exact (tmp H1).
Qed.

Lemma SepE : forall X:set, forall P:set -> Prop, forall x:set,
 x :e {z :i X|P z} -> x :e X /_\ P x.
Proof.
  intros.
  pose (ax := SepEq).
  unfold iff in ax.
  pose (tmp := andIA _ _ (ax X P x)).
  exact (tmp H).
Qed.

Lemma SepE1 : forall X:set, forall P:set -> Prop, forall x:set,
 x :e {z :i X|P z} -> x :e X.
Proof.
  intros.
  exact (andIA _ _ (SepE X P x H)).
Qed.

Lemma SepE2 : forall X:set, forall P:set -> Prop, forall x:set,
 x :e {z :i X|P z} -> P x.
Proof.
  intros.
  exact (andIB _ _ (SepE X P x H)).
Qed.

(* Repl(X, F) = {F x | x :e X} *)

Parameter Repl : set->(set->set)->set.

Notation "{ F | x :i X }" := (Repl X (fun x:set => F)).

Axiom ReplEq :
forall X:set, forall F:set->set, forall y:set, y :e {F z|z :i X} <=> exists x, x :e X /_\ y == F x.

Lemma ReplE :
forall X:set, forall F:set->set, forall y:set, y :e {F z|z :i X} -> exists x, x :e X /_\ y == F x.
Proof.
  intros.
  pose (ax := ReplEq X F y).
  unfold iff in ax.
  pose (tmp := andIA _ _ ax).
  exact (tmp H).
Qed.

Lemma ReplI :
forall X:set, forall F:set->set, forall x:set, x :e X -> F x :e {F x|x :i X}.
Proof.
  intros.
  pose (ax := ReplEq X F (F x)).
  unfold iff in ax.
  pose (tmp := andIB _ _ ax).
  assert (exists x0, x0 :e X /_\ F x == F x0).
    unfold ex.
    intros.
    assert (x :e X /_\ F x == F x).
      unfold and.
      intros.
      exact (H1 H (eqI (F x))).
    exact (H0 x H1).
  exact (tmp H0).
Qed.

(* Прикольные леммки для разных операций над пустыми множествами *)
(* Пригодятся позже, когда определим ординалы *)

Lemma Subq_Empty : forall X:set, Empty c= X.
Proof.
  unfold Subq.
  intros.
  pose (xNotInE := EmptyE x).
  unfold not in xNotInE.
  pose (false := xNotInE H).
  exact (false (x :e X)).
Qed.

Lemma Empty_Power : forall X:set, Empty :e Power X.
Proof.
  intros.
  exact (PowerI X Empty (Subq_Empty X)).
Qed.

Lemma Repl_Empty : forall F:set -> set, {F x|x :i Empty} == Empty.
Proof.
  intros.
  unfold eq.
  intros.



    (* HW *)
    admit.
Qed.

(* Неупорядоченная пара *)

Definition TSet : set := {X :i Power (Power Empty) | Empty :e X \_/ Empty /:e X}.
Definition UPair : set->set->set :=
 fun y z:set =>
 {Descr (fun w:set => forall p:set->Prop, (Empty /:e X -> p y) -> (Empty :e X  -> p z) -> p w)|X :i TSet}.

Notation "{ x , y }" := (UPair x y).

Lemma UPairE :
forall x y z:set, x :e {y,z} -> x == y \_/ x == z.
Proof.
  intros.
  unfold UPair in H.
  unfold eq.
  unfold TSet in H.
    (* HW *)
    admit.
Qed.

Lemma UPairI1 :
forall y z:set, y :e {y,z}.
Proof.
    (* HW *)
    admit.
Qed.

Lemma UPairI2 :
forall y z:set, z :e {y,z}.
Proof.
    (* HW *)
    admit.
Qed.

Lemma UPairEq :
forall x y z, x :e {y,z} <=> x == y \_/ x == z.
Proof.
    (* CW *)
    admit.
Qed.

(* sing(Y) = {Y, Y} *)

Definition Sing : set->set := fun y:set => {y,y}.

Notation "{| y |}" := (Sing y).

Lemma SingI : forall y, y :e {| y |}.
Proof.
  intros y. unfold Sing. apply UPairI1.
Qed.

Lemma SingE : forall x y, x :e {| y |} -> x == y.
Proof.
  intros x y H1. apply (UPairE _ _ _ H1). exact (fun H => H). exact (fun H => H).
Qed.

Lemma SingEq : forall x y, x :e {| y |} <=> x == y.
Proof.
    (* CW *)
    admit.
Qed.

(* binunion(X, Y) = Union({X, Y}) *)

Definition binunion : set -> set -> set := fun X Y => Union {X,Y}.

Notation "X :u: Y" := (binunion X Y) (at level 40).

Lemma binunionI1 : forall X Y z, z :e X -> z :e X :u: Y.
Proof.
    (* CW *)
    admit.
Qed.

Lemma binunionI2 : forall X Y z, z :e Y -> z :e X :u: Y.
Proof.
    (* CW *)
    admit.
Qed.

Lemma binunionE : forall X Y z, z :e X :u: Y -> z :e X \_/ z :e Y.
Proof.
    (* HW *)
    admit.
Qed.

Lemma binunionEq : forall X Y z, z :e X :u: Y <=> z :e X \_/ z :e Y.
Proof.
    (* CW *)
    admit.
Qed.

(* TODO : setminus, famunion, ordinals, more and more fun to follow *)

End Basics.

Export Basics.
