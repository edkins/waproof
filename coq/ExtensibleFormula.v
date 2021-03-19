Require Import NArith.
Require Import List.

Inductive Const := MkConst : N -> Const.
Inductive Var := MkVar : N -> Var.
Inductive Typ := MkType : N -> Typ.

Definition Env := list (Var * Typ).

Definition TBool := MkType 0.
Definition TNat := MkType 1.
Definition CFalse := MkConst 0.
Definition CImp := MkConst 1.

Fixpoint not_in_env (x:Var) (e:Env) : Prop :=
  match e with
  | nil => True
  | ((y,_) :: ys) => ~(x = y) /\ not_in_env x ys
  end.

Theorem not_in_env_nil (x:Var) : not_in_env x nil.
unfold not_in_env.
trivial.
Qed.

Theorem not_in_env_cons (x:Var) (y:Var) (t:Typ) (e:Env)
  : (x <> y) -> not_in_env x e -> not_in_env x ((y,t) :: e).
unfold not_in_env.
intuition.
Qed.

Theorem not_not_in_env_cons (x:Var) (t:Typ) (e:Env)
  : ~not_in_env x ((x,t) :: e).
unfold not_in_env.
intuition.
Qed.

Fixpoint in_env (x:Var) (t:Typ) (e:Env) : Prop :=
  match e with
  | nil => False
  | ((y,u) :: ys) => (x = y /\ t = u) \/ in_env x t ys
  end.

Inductive ConstType :=
| MkConstType : Typ -> ConstType
| MkFuncType : Typ -> ConstType -> ConstType.

Definition CBool := MkConstType TBool.

Definition ct_in_env (x:Var) (ct:ConstType) (e:Env) : Prop :=
  match ct with
  | MkConstType t => in_env x t e
  | MkFuncType _ _ => False
  end.

Definition GEnv := list (Const * ConstType).

Fixpoint in_genv (x:Const) (t:ConstType) (e:GEnv) : Prop :=
  match e with
  | nil => False
  | ((y,u) :: ys) => (x = y /\ t = u) \/ in_genv x t ys
  end.

Inductive Expr (g:GEnv) (e:Env) (t:ConstType) :=
| VarExpr (x:Var) : ct_in_env x t e -> Expr g e t
| ConstExpr (c:Const) : in_genv c t g -> Expr g e t
| CallExpr (u:Typ) (f:Expr g e (MkFuncType u t)) (x:Expr g e (MkConstType u)) : Expr g e t
| ForAllExpr (x:Var) (xt:Typ) (f:Expr g ((x,xt)::e) CBool) : not_in_env x e -> Expr g e t.





