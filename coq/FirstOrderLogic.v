Require Import List.

Inductive Vocab :=
  | MkVocab : list nat -> list nat -> Vocab.

Inductive UpTo (n:nat) :=
  | Below i : i < n -> UpTo n.

Section Formulas.

Variable V:Vocab.

Definition pred_count :=
  match V with
    | MkVocab ps _ => length ps
  end.

Definition func_count :=
  match V with
    | MkVocab _ fs => length fs
  end.

Inductive Pred :=
  | FindPred : UpTo pred_count -> Pred.

Inductive Func :=
  | FindFunc : UpTo func_count -> Func.

Definition p_arity (f:Pred) :=
  match V,f with
    | MkVocab ps _, FindPred (Below _ i _) => nth i ps 0
  end.

Definition f_arity (f:Func) :=
  match V,f with
    | MkVocab _ fs, FindFunc (Below _ i _) => nth i fs 0
  end.

Inductive Expr : nat -> Type :=
  | Var {d} : UpTo d -> Expr d
  | Fun {d} (f:Func) : (UpTo (f_arity f) -> Expr d) -> Expr d.

Inductive Formula : nat -> Type :=
  | Pre {d} (p:Pred) : (UpTo (p_arity p) -> Expr d) -> Formula d
  | Imp {d} : Formula d -> Formula d -> Formula d
  | Not {d} : Formula d -> Formula d
  | ForAll {d} : d > 0 -> Formula (pred d) -> Formula d.

Fixpoint generalize (d:nat) (t:nat) (A:Formula (d+t)) : Formula t :=
  match d with
  | 0 => A
  | S c => ForAll (S_gt_0) (generalize c A)
  end.

Definition schema1 {d:nat} (A:Formula d) (B:Formula d) := Imp A (Imp B A).
Definition schema2 {d:nat} (A:Formula d) (B:Formula d) (C:Formula d)
  := Imp (Imp A (Imp B C)) (Imp (Imp A B) (Imp B C)).
Definition schema3 {d:nat} (A:Formula d) := Imp (Not (Not A)) A.
Definition schema4 {d:nat} (A:Formula d) (B:Formula d) :=
  Imp (ForAll (Imp A B)) (Imp (ForAll A) (ForAll B)).
