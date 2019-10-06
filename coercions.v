(* There are three situations: *)

(*** At function application *)

(* We first give an example of coercion between atomic inductive types. *)
Definition bool_in_nat (b:bool) := if b then 0 else 1.
Coercion bool_in_nat : bool >-> nat.
Check (0 = true).
Set Printing Coercions.
Check (0 = true).
Unset Printing Coercions.

(* We give an example of coercion between classes with parameters. *)

Parameters (C : nat -> Set) (D : nat -> bool -> Set) (E : bool -> Set).
Parameter f : forall n:nat, C n -> D (S n) true.
Coercion f : C >-> D.

Parameter g : forall (n:nat) (b:bool), D n b -> E b.
Coercion g : D >-> E.

Parameter c : C 1.
Parameter T : E true -> nat.
Check (T c).
Set Printing Coercions.
Check (T c).
Unset Printing Coercions.

(* We give now an example using identity coercions. *)

Definition D' (b:bool) := D 1 b.
Identity Coercion IdD'D : D' >-> D.
Parameter d' : D' true.
Check (IdD'D true d').
Print IdD'D.
Check (T d').
Set Printing Coercions.
Check (T d').
Unset Printing Coercions.

(* In the case of functional arguments, we use the monotonic rule of
sub-typing. To coerce :g:`t : forall x : A, B` towards
:g:`forall x : A', B'`, we have to coerce ``A'`` towards ``A`` and ``B``
towards ``B'``. An example is given below:  *)

Parameters (A B : Set) (h : A -> B).
Coercion h : A >-> B.
Parameter U : (A -> E true) -> nat.
Parameter t : B -> C 0.
Check (U t).
Set Printing Coercions.
Check (U t).
Unset Printing Coercions.

(* Remark the changes in the result following the modification of the
previous example. *)

Parameter U' : (C 0 -> B) -> nat.
Parameter t' : E true -> A.
Check (U' t').
Set Printing Coercions.
Check (U' t').
Unset Printing Coercions.

(*** To a type *)

(* An assumption ``x:A`` when ``A`` is not a type, is ill-typed.  It is 
replaced by ``x:A'`` where ``A'`` is the result of the application to
``A`` of the coercion path between the class of ``A`` and
``Sortclass`` if it exists.  This case occurs in the abstraction
:g:`fun x:A => t`, universal quantification :g:`forall x:A,B`, global
variables and parameters of (co-)inductive definitions and
functions. In :g:`forall x:A,B`, such a coercion path may also be applied
to ``B`` if necessary. *)

Parameter Graph : Type.
Parameter Node : Graph -> Type.
Coercion Node : Graph >-> Sortclass.
Parameter G : Graph.
Parameter Arrows : G -> G -> Type.
Check Arrows.
Parameter fg : G -> G.
Check fg.
Set Printing Coercions.
Check fg.
Unset Printing Coercions.

(*** To a function *)

(* ``f a`` is ill-typed because ``f:A`` is not a function. The term
``f`` is replaced by the term obtained by applying to ``f`` the
coercion path between ``A`` and ``Funclass`` if it exists.  *)

Parameter bij : Set -> Set -> Set.
Parameter ap : forall A B:Set, bij A B -> A -> B.
Coercion ap : bij >-> Funclass.
Parameter b : bij nat nat.
Check (b 0).
Set Printing Coercions.
Check (b 0).
Unset Printing Coercions.

