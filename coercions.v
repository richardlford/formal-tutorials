(* These notes were extracted from the Coq Reference manual. *)

(*** Implicit Coercions *)
(* :Author: Amokrane Saïbi

General Presentation
---------------------

This section describes the inheritance mechanism of |Coq|. In |Coq| with
inheritance, we are not interested in adding any expressive power to
our theory, but only convenience. Given a term, possibly not typable,
we are interested in the problem of determining if it can be well
typed modulo insertion of appropriate coercions. We allow to write:

 * f a where f:(forall x:A,B) and a:A' when A' can
   be seen in some sense as a subtype of A.
 * x:A when A is not a type, but can be seen in
   a certain sense as a type: set, group, category etc.
 * f a when f is not a function, but can be seen in a certain sense
   as a function: bijection, functor, any structure morphism etc.


Classes
-------

A class with n parameters is any defined name with a type
forall (ident__1 : type__1)..(ident__n:type__n), sort.  Thus a class with
parameters is considered as a single class and not as a family of
classes.  An object of a class is any term of type class term__1 .. term__n.
In addition to these user-defined classes, we have two built-in classes:


  * Sortclass, the class of sorts; its objects are the terms whose type is a
    sort (e.g. Prop or Type).
  * Funclass, the class of functions; its objects are all the terms with 
    a functional type, i.e. of form forall x:A,B.

Formally, the syntax of classes is defined as:

   class: `qualid`
        | Sortclass
        | Funclass


Coercions
---------

A name f can be declared as a coercion between a source user-defined class
C with n parameters and a target class D if one of these
conditions holds:

 * D is a user-defined class, then the type of f must have the form
   forall (x₁:A₁)..(xₙ:Aₙ)(y:C x₁..xₙ), D u₁..uₘ where m
   is the number of parameters of D.
 * D is Funclass, then the type of f must have the form
   forall (x₁:A₁)..(xₙ:Aₙ)(y:C x₁..xₙ)(x:A), B.
 * D is Sortclass, then the type of f must have the form
   forall (x₁:A₁)..(xₙ:Aₙ)(y:C x₁..xₙ), s with s a sort.

We then write f : C >-> D. The restriction on the type
of coercions is called *the uniform inheritance condition*.

Note: The built-in class Sortclass can be used as a source class, but
          the built-in class Funclass cannot.

To coerce an object t:C t₁..tₙ of C towards D, we have to
apply the coercion f to it; the obtained term f t₁..tₙ t is
then an object of D.


Identity Coercions
-------------------

Identity coercions are special cases of coercions used to go around
the uniform inheritance condition. Let C and D be two classes
with respectively `n` and `m` parameters and
f:forall (x₁:T₁)..(xₖ:Tₖ)(y:C u₁..uₙ), D v₁..vₘ a function which
does not verify the uniform inheritance condition. To declare f as
coercion, one has first to declare a subclass C' of C:

  C' := fun (x₁:T₁)..(xₖ:Tₖ) => C u₁..uₙ

We then define an *identity coercion* between C' and C:

  Id_C'_C  := fun (x₁:T₁)..(xₖ:Tₖ)(y:C' x₁..xₖ) => (y:C u₁..uₙ)

We can now declare f as coercion from C' to D, since we can
"cast" its type as
forall (x₁:T₁)..(xₖ:Tₖ)(y:C' x₁..xₖ),D v₁..vₘ.

The identity coercions have a special status: to coerce an object
t:C' t₁..tₖ
of C' towards C, we do not have to insert explicitly Id_C'_C
since Id_C'_C t₁..tₖ t is convertible with t.  However we
"rewrite" the type of t to become an object of C; in this case,
it becomes C uₙ'..uₖ' where each uᵢ' is the result of the
substitution in uᵢ of the variables xⱼ by tⱼ.

Inheritance Graph
------------------

Coercions form an inheritance graph with classes as nodes.  We call
*coercion path* an ordered list of coercions between two nodes of
the graph.  A class C is said to be a subclass of D if there is a
coercion path in the graph from C to D; we also say that C
inherits from D. Our mechanism supports multiple inheritance since a
class may inherit from several classes, contrary to simple inheritance
where a class inherits from at most one class.  However there must be
at most one path between two classes. If this is not the case, only
the *oldest* one is valid and the others are ignored. So the order
of declaration of coercions is important.

We extend notations for coercions to coercion paths. For instance
[f₁;..;fₖ] : C >-> D is the coercion path composed
by the coercions f₁..fₖ.  The application of a coercion path to a
term consists of the successive application of its coercions.


Declaring Coercions
-------------------
[See reference manual for details.]

Command: Coercion qualid : class >-> class

  Declares the construction denoted by qualid as a coercion between
  the two given classes.


assumption::=assumption_keyword assums .
assums::=simple_assums| (simple_assums) ... (simple_assums)
simple_assums::=ident ... ident :[>] term

If the extra `>` is present before the type of some assumptions, 
these assumptions are declared as coercions.

Similarly, constructors of inductive types can be declared as coercions at
definition time of the inductive type. This extends and modifies the
grammar of inductive types from Figure vernacular as follows:

.. productionlist::
   inductive : Inductive `ind_body` with ... with `ind_body`
             : CoInductive `ind_body` with ... with `ind_body`
   ind_body : `ident` [ `binders` ] : `term` := [[|] `constructor` | ... | `constructor` ]
   constructor : `ident` [ `binders` ] [:[>] `term` ]

Especially, if the extra > is present in a constructor
declaration, this constructor is declared as a coercion.

Command: Identity Coercion ident : class >-> class

   If C is the source `class` and D the destination, we check
   that C is a constant with a body of the form
   fun (x₁:T₁)..(xₙ:Tₙ) => D t₁..tₘ where `m` is the
   number of parameters of D.  Then we define an identity
   function with type forall (x₁:T₁)..(xₙ:Tₙ)(y:C x₁..xₙ),D t₁..tₘ,
   and we declare it as an identity coercion between C and D.

   Error: class must be a transparent constant.
 
   Variant: Local Identity Coercion ident : ident >-> ident

      Same as Identity Coercion but locally to the current section.

   Variant: SubClass ident := type
      :name: SubClass

      If type is a class ident' applied to some arguments then
      ident is defined and an identity coercion of name
      Id_ident_ident' is
      declared. Otherwise said, this is an abbreviation for

      Definition ident := type.
      Identity Coercion Id_ident_ident' : ident >-> ident'.

   Variant: Local SubClass ident := type

      Same as before but locally to the current section.


Displaying Available Coercions
-------------------------------

Command: Print Classes

   Print the list of declared classes in the current context.

Command: Print Coercions

   Print the list of declared coercions in the current context.

Command: Print Graph

   Print the list of valid coercion paths in the current context.

Command: Print Coercion Paths class class

   Print the list of valid coercion paths between the two given classes.

Activating the Printing of Coercions
-------------------------------------

.. flag:: Printing Coercions

   When on, this option forces all the coercions to be printed.
   By default, coercions are not printed.

.. table:: Printing Coercion qualid
   :name: Printing Coercion

   Specifies a set of qualids for which coercions are always displayed.  Use the
   Add table and Remove table commands to update the set of qualids.

.. _coercions-classes-as-records:

Classes as Records
------------------

.. index:: :> (coercion)

We allow the definition of *Structures with Inheritance* (or classes as records)
by extending the existing Record macro. Its new syntax is:

Variant: Record {? >} ident {? binders} : sort := {? ident} { {+; ident :{? >} term } }

   The first identifier ident is the name of the defined record and
   sort is its type. The optional identifier after := is the name
   of the constructor (it will be Build_ident if not given).
   The other identifiers are the names of the fields, and term
   are their respective types. If :> is used instead of : in
   the declaration of a field, then the name of this field is automatically
   declared as a coercion from the record name to the class of this
   field type. Note that the fields always verify the uniform
   inheritance condition. If the optional > is given before the
   record name, then the constructor name is automatically declared as
   a coercion from the class of the last field type to the record name
   (this may fail if the uniform inheritance condition is not
   satisfied).

Variant: Structure {? >} ident {? binders} : sort := {? ident} { {+; ident :{? >} term } }
   :name: Structure

   This is a synonym of Record.


Coercions and Sections
----------------------

The inheritance mechanism is compatible with the section
mechanism. The global classes and coercions defined inside a section
are redefined after its closing, using their new value and new
type. The classes and coercions which are local to the section are
simply forgotten.
Coercions with a local source class or a local target class, and
coercions which do not verify the uniform inheritance condition any longer
are also forgotten.

Coercions and Modules
---------------------

The coercions present in a module are activated only when the module is
explicitly imported.

Examples
--------

There are three situations: *)


(*** Coercion at function application *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

f a is ill-typed where f:forall x:A,B and a:A'. If there is a
coercion path between A' and A, then f a is transformed into
f a' where a' is the result of the application of this
coercion path to a.

We first give an example of coercion between atomic inductive types

.. coqtop:: all *)

  Definition bool_in_nat (b:bool) := if b then 0 else 1.
  Coercion bool_in_nat : bool >-> nat.
  Check (0 = true).
  Set Printing Coercions.
  Check (0 = true).
  Unset Printing Coercions.


(* .. warning::

  Note that Check (true = O) would fail. This is "normal" behavior of
  coercions. To validate true=O, the coercion is searched from
  nat to bool. There is none.

We give an example of coercion between classes with parameters.

.. coqtop:: all *)

  Parameters (C : nat -> Set) (D : nat -> bool -> Set) (E : bool -> Set).
  Parameter f : forall n:nat, C n -> D (S n) true.
  Coercion f : C >-> D.
  Parameter g : forall (n:nat) (b:bool), D n b -> E b.
  Coercion g : D >-> E.
  Parameter c : C 0.
  Parameter T : E true -> nat.
  Check (T c).
  Set Printing Coercions.
  Check (T c).
  Unset Printing Coercions.

(* We give now an example using identity coercions.

.. coqtop:: all *)

  Definition D' (b:bool) := D 1 b.
  Identity Coercion IdD'D : D' >-> D.
  Print IdD'D.
  Parameter d' : D' true.
  Check (T d').
  Set Printing Coercions.
  Check (T d').
  Unset Printing Coercions.


(* In the case of functional arguments, we use the monotonic rule of
sub-typing. To coerce t : forall x : A, B towards
forall x : A', B', we have to coerce A' towards A and B
towards B'. An example is given below:

.. coqtop:: all *)

  Parameters (A B : Set) (h : A -> B).
  Coercion h : A >-> B.
  Parameter U : (A -> E true) -> nat.
  Parameter t : B -> C 0.
  Check (U t).
  Set Printing Coercions.
  Check (U t).
  Unset Printing Coercions.

(* Remark the changes in the result following the modification of the
previous example.

.. coqtop:: all *)

  Parameter U' : (C 0 -> B) -> nat.
  Parameter t' : E true -> A.
  Check (U' t').
  Set Printing Coercions.
  Check (U' t').
  Unset Printing Coercions.


(*** Coercion to a type *)
(* ~~~~~~~~~~~~~~~~~~

An assumption x:A when A is not a type, is ill-typed.  It is
replaced by x:A' where A' is the result of the application to
A of the coercion path between the class of A and
Sortclass if it exists.  This case occurs in the abstraction
fun x:A => t, universal quantification forall x:A,B, global
variables and parameters of (co-)inductive definitions and
functions. In forall x:A,B, such a coercion path may also be applied
to B if necessary.

.. coqtop:: all *)

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


(*** Coercion to a function *)
(* ~~~~~~~~~~~~~~~~~~~~~~

f a is ill-typed because f:A is not a function. The term
f is replaced by the term obtained by applying to f the
coercion path between A and Funclass if it exists.

.. coqtop:: all *)

  Parameter bij : Set -> Set -> Set.
  Parameter ap : forall A B:Set, bij A B -> A -> B.
  Coercion ap : bij >-> Funclass.
  Parameter b : bij nat nat.
  Check (b 0).
  Set Printing Coercions.
  Check (b 0).
  Unset Printing Coercions.

(* Let us see the resulting graph after all these examples.

.. coqtop:: all *)

  Print Graph.

  (*
    [bool_in_nat] : bool >-> nat
    [f] : C >-> D
    [f; g] : C >-> E
    [g] : D >-> E
    [IdD'D] : D' >-> D
    [IdD'D; g] : D' >-> E
    [h] : A >-> B
    [Node] : Graph >-> Sortclass
    [ap] : bij >-> Funclass
   *)
  
  Print Classes.
  (* Sortclass Funclass A B C D D' E Graph bij bool nat  *)
  
  Print Coercions.
  (* f g h ap Node IdD'D bool_in_nat *)
  
