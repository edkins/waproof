Definition pre_valid {V:Set} {S:Set} (f:V -> S -> V -> S -> Prop) : Prop :=
  forall t r u s, f t r u s -> f t r t r.

Definition post_valid {V:Set} {S:Set} (f:V -> S -> V -> S -> Prop) : Prop :=
  forall t r u s, f t r u s -> f u s u s.

Definition trans_valid {V:Set} {S:Set} (f:V -> S -> V -> S -> Prop) : Prop :=
  forall t r u s v q, f t r u s -> f u s v q -> f t r v q.

Inductive Typ (V:Set) (S:Set) :=
  | MkTyp (f : V -> S -> V -> S -> Prop) : pre_valid f -> post_valid f -> trans_valid f -> Typ V S.

Inductive Op (V:Set) (W:Set) (X:Set) :=
  | MkOp (op: V -> W -> X) (oleft: X -> V) (oright: X -> W) :
    (forall x, op (oleft x) (oright x) = x)
    -> Op V W X.

Definition left {V:Set} {W:Set} {X:Set} (op:Op V W X) : X -> V :=
  match op with
    | MkOp _ _ _ _ oleft _  _ => oleft
  end.

Definition right {V:Set} {W:Set} {X:Set} (op:Op V W X) : X -> W :=
  match op with
    | MkOp _ _ _ _ _ oright _ => oright
  end.

Definition concatf {V:Set} {W:Set} {X:Set} {S:Set} (O:Op V W X)
  (f:V -> S -> V -> S -> Prop)
  (g:W -> S -> W -> S -> Prop)
  (x:X) (r:S) (y:X) (s:S) : Prop :=
let t := left O x in
let u := right O x in
let a := left O y in
let b := right O y in
f t r a s /\
g u r b s /\
(forall c q, f t r c q -> g u q u q) /\
(forall c q, f a s c q -> g b q b q) /\
(forall d q, g u r d q -> f t q t q) /\
(forall d q, g b s d q -> f a q a q).

Lemma pre_valid_concatf
  {V:Set} {W:Set} {X:Set} {S:Set} (O:Op V W X)
  (f:V -> S -> V -> S -> Prop)
  (g:W -> S -> W -> S -> Prop)
  : pre_valid f -> pre_valid g -> pre_valid (concatf O f g).
Proof.
unfold pre_valid. intros.
unfold concatf in H1.
destruct H1. destruct H2. destruct H3. destruct H4. destruct H5.
unfold concatf. intuition.
exact (H (left O t) r (left O u) s H1).
exact (H0 (right O t) r (right O u) s H2).
Qed.

Lemma post_valid_concatf
  {V:Set} {W:Set} {X:Set} {S:Set} (O:Op V W X)
  (f:V -> S -> V -> S -> Prop)
  (g:W -> S -> W -> S -> Prop)
  : post_valid f -> post_valid g -> post_valid (concatf O f g).
Proof.
unfold post_valid. intros.
unfold concatf in H1.
destruct H1. destruct H2. destruct H3. destruct H4. destruct H5.
unfold concatf. intuition.
exact (H (left O t) r (left O u) s H1).
exact (H0 (right O t) r (right O u) s H2).
Qed.

Lemma trans_valid_concatf
  {V:Set} {W:Set} {X:Set} {S:Set} (O:Op V W X)
  (f:V -> S -> V -> S -> Prop)
  (g:W -> S -> W -> S -> Prop)
  : trans_valid f -> trans_valid g -> trans_valid (concatf O f g).
Proof.
unfold trans_valid. intros.
unfold concatf in H1. destruct H1. destruct H3. destruct H4. destruct H5. destruct H6.
unfold concatf in H2. destruct H2. destruct H8. destruct H9. destruct H10. destruct H11.
unfold concatf. intuition.
- apply (H _ _ (left O u) s _ _). trivial. trivial.
- apply (H0 _ _ (right O u) s _ _). trivial. trivial.
Qed.

Definition type_concat {V:Set} {W:Set} {X:Set} {S:Set} (O:Op V W X) (T:Typ V S) (U:Typ W S) : Typ X S :=
  match (T,U) with
    | (MkTyp _ _ f pf qf tf, MkTyp _ _ g pg qg tg) =>
      MkTyp _ _
      (concatf O f g)
      (pre_valid_concatf O f g pf pg)
      (post_valid_concatf O f g qf qg)
      (trans_valid_concatf O f g tf tg)
  end.


Definition tr {V:Set} {S:Set} (T:Typ V S) : V -> S -> V -> S -> Prop :=
  match T with
    | MkTyp _ _ f _ _ _ => f
  end.


Definition subtype {V:Set} {S:Set} (T:Typ V S) (U:Typ V S) : Prop :=
  forall t r u s, tr T t r u s -> tr U t r u s.

Lemma subtype_refl {V:Set} {S:Set} (T:Typ V S) : subtype T T.
Proof.
unfold subtype.
trivial.
Qed.

Lemma subtype_trans {V:Set} {S:Set} (T:Typ V S) (U:Typ V S) (W:Typ V S) (tu:subtype T U) (uw:subtype U W) : subtype T W.
Proof.
unfold subtype.
intros.
pose (tu t r u s H).
exact (uw t r u s t0).
Qed.

Lemma tr_concat {V:Set} {W:Set} {X:Set} {S:Set} (O:Op V W X) (T:Typ V S) (U:Typ W S)
  : tr (type_concat O T U) = concatf O (tr T) (tr U).
Proof.
destruct T.
destruct U.
trivial.
Qed.

Lemma subtype_concatl {V:Set} {W:Set} {X:Set} {S:Set} (O:Op V W X) (T0:Typ V S) (T1:Typ V S) (U:Typ W S)
  : subtype T0 T1 -> subtype (type_concat O T0 U) (type_concat O T1 U).
unfold subtype.
rewrite tr_concat. rewrite tr_concat.
unfold concatf.
intros.
destruct H0. destruct H1. destruct H2. destruct H3. destruct H4.
intuition.
apply (H2 (left O u)).
