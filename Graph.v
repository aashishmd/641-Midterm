(** * Stlc: The Simply Typed Lambda-Calculus *)

Require Export Types.



Module Graph.


(** Vertex and Edges **)
Inductive Vertex : Set :=
  vertex : nat -> Vertex.

Inductive Edge : Set :=
  edge : Vertex -> Vertex -> nat -> Edge.

Definition Edge_tail (e : Edge) := match e with
                               | edge x y _ => x
                               end.

Definition Edge_head (e : Edge) := match e with
                               | edge x y _ => y
                               end.

Inductive exp : Set -> Type :=
  |  add_v : forall v : Set, v -> exp v
  |  add_e : forall e : Set, e -> exp e
  | remove_v : forall v : Set, v -> exp v
  | remove_e : forall e : Set, e -> exp e.

(********************************)
(** Vertex and Edges Sets**)
Definition Edge_set := Edge -> Prop.
Definition Vertex_set := Vertex -> Prop.

Inductive Empty_E : Edge_set :=.
Inductive Empty_V : Vertex_set :=.
Inductive Full_E : Edge_set :=
    In_full_E : forall x : Edge, Full_E x.
Inductive Full_V : Vertex_set :=
    In_full_V : forall x : Vertex, Full_V x.

Axiom V_set_eq : forall v1 v2 : Vertex_set, (forall x : Vertex, v1 x <-> v2 x) -> v1 = v2.

Lemma V_empty_nothing : forall x : Vertex, ~ Empty_V x.
Proof.
        tauto.
Qed.

(********************************)
(** Set operations**)
Inductive Union_V (a b : Vertex_set) : Vertex_set :=
  | union_v : forall x : Vertex, Union_V a b x.

Inductive Union_E (a b : Edge_set) : Edge_set :=
  | union_e : forall x : Edge, Union_E a b x.

(** Sanity proofs**)
Lemma Union_eq :
 forall a b a' b': Vertex_set, a = a' -> b = b' -> Union_V a b = Union_V a' b'.
Proof.
        intros; elim H.
        elim H0; trivial.
Qed.

Lemma Union_assoc :
forall v1 v2 v3 : Vertex_set, Union_V (Union_V v1 v2) v3 = Union_V v1 (Union_V v2 v3).
Proof.
        intros; apply V_set_eq; split; intros.
        inversion H.
        inversion H0.
        apply union_v; trivial.
        apply union_v; apply In_left; trivial.
Qed.

Inductive Inter_V (a b : Vertex_set) : Vertex_set :=
    inter_v : forall x : Vertex, a x -> b x -> Inter_V a b x.

Inductive Inter_E (a b : Edge_set) : Edge_set :=
    inter_e : forall x : Edge, a x -> b x -> Inter_E a b x.
(********************************)

(** Single vertex and edge sets**)
Inductive Single_V (x: Vertex) : Vertex_set :=
  | single_v : Single_V x x.
Inductive Single_E (x: Edge) : Edge_set :=
  | single_e : Single_E x x.

Definition List_V := list Vertex.
Definition List_E := list Edge.
(********************************)

(**Graph**)
Inductive Graph : Vertex_set -> Edge_set -> Prop :=
  | graph_empty : Graph Empty_V Empty_E
  | graph_add_vertex : forall (v:Vertex_set) (e:Edge_set) (g : Graph v e) (x : Vertex),
    (Inter_V (Single_V x) v) = Empty_V -> Graph (Union_V  (Single_V x) v) e
  | graph_add_edge : forall (v:Vertex_set) (e:Edge_set) (g : Graph v e) (v1 v2 : Vertex) (x : Edge) (n: nat) ,
    x = (edge v1 v2 n) -> ~(Inter_V (Single_V v1) v) = Empty_V -> ~(Inter_V (Single_V v2) v) = Empty_V 
        -> Graph v (Union_E  (Single_E x) e)
  | graph_remove_vertex : forall (v v':Vertex_set) (e:Edge_set) (g : Graph v e) (x v1 v2: Vertex) (a : Edge) (n: nat),
    a = (edge v1 v2 n) -> (~(Inter_V (Single_V v1) v) = Empty_V) + (~(Inter_V (Single_V v2) v) = Empty_V) ->
  (Inter_V v' (Single_V x)) = Empty_V ->  (Inter_E e (Single_E a)) = Empty_E -> Graph v' e
  | graph_remove_edge : forall (v:Vertex_set) (e e':Edge_set) (g : Graph v e) (x : Edge),
    (Inter_E e' (Single_E x)) = Empty_E -> Graph v e'.



(** testing::::::::
Lemma G_v_dec :
forall (v : Vertex_set) (e : Edge_set) (g : Graph v e) (x : Vertex), {v x} + {~ v x}.
Proof.
        intros v a g; intros.
        induction g.
        right. apply V_empty_nothing.
        case (H x0); intros.
        left; apply V_in_right; trivial.
        case (V_eq_dec x x0); intros.
        left; apply V_in_left; rewrite e; apply V_in_single.
        right; red in |- *; intros; inversion H0.
        elim n1; inversion H1; trivial.
        elim n0; trivial.
        auto.
        case (H x); intros.
        left; elim e; trivial.
        right; elim e; trivial.
Qed. 
**)


Inductive Graph_Mutate : Vertex_set -> Edge_set -> List_V -> List_E -> Vertex_set -> Edge_set -> Prop :=
 | 