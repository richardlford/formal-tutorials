(* This was extracted from the Coq reference manual. 

Canonical structures
~~~~~~~~~~~~~~~~~~~~

A canonical structure is an instance of a record/structure type that
can be used to solve unification problems involving a projection
applied to an unknown structure instance (an implicit argument) and a
value. The complete documentation of canonical structures can be found
in :ref:`canonicalstructures`; here only a simple example is given.

.. cmd:: Canonical {? Structure } @qualid

   This command declares :token:`qualid` as a canonical instance of a
   structure (a record).

   Assume that :token:`qualid` denotes an object ``(Build_struct`` |c_1| … |c_n| ``)`` in the
   structure :g:`struct` of which the fields are |x_1|, …, |x_n|.
   Then, each time an equation of the form ``(``\ |x_i| ``_)`` |eq_beta_delta_iota_zeta| |c_i| has to be
   solved during the type checking process, :token:`qualid` is used as a solution.
   Otherwise said, :token:`qualid` is canonically used to extend the field |c_i|
   into a complete structure built on |c_i|.

   Canonical structures are particularly useful when mixed with coercions
   and strict implicit arguments.

   .. example::

      Here is an example.

      .. coqtop:: all *)

         Require Import Relations.

         Require Import EqNat.

         Set Implicit Arguments.

         Unset Strict Implicit.

         Structure Setoid : Type := {Carrier :> Set; Equal : relation Carrier;
                                     (* [canonical(false)] *)
                                     Prf_equiv : equivalence Carrier Equal}.

         Definition is_law (A B:Setoid) (f:A -> B) := forall x y:A, Equal x y -> Equal (f x) (f y).

         Axiom eq_nat_equiv : equivalence nat eq_nat.

         Definition nat_setoid : Setoid := Build_Setoid eq_nat_equiv.

         Canonical Structure nat_setoid.
         Print Canonical Projections.

      (*
      Thanks to :g:`nat_setoid` declared as canonical, the implicit arguments :g:`A`
      and :g:`B` can be synthesized in the next statement.

      .. coqtop:: all abort *)

         Lemma is_law_S : is_law S.
           unfold is_law.
           auto.
           
   (*
   .. note::
      If a same field occurs in several canonical structures, then
      only the structure declared first as canonical is considered.

   .. note::
      To prevent a field from being involved in the inference of canonical instances,
      its declaration can be annotated with the :g:`#[canonical(false)]` attribute.

      .. example::

         For instance, when declaring the :g:`Setoid` structure above, the
         :g:`Prf_equiv` field declaration could be written as follows.

         .. coqdoc::

            #[canonical(false)] Prf_equiv : equivalence Carrier Equal

      See :ref:`canonicalstructures` for a more realistic example.

   .. cmdv:: Canonical {? Structure } @ident {? : @type } := @term

      This is equivalent to a regular definition of :token:`ident` followed by the
      declaration :n:`Canonical @ident`.

.. cmd:: Print Canonical Projections

   This displays the list of global names that are components of some
   canonical structure. For each of them, the canonical structure of
   which it is a projection is indicated.

   .. example::

      For instance, the above example gives the following output:

      .. coqtop:: all *)

         Print Canonical Projections.

      (*
      .. note::

         The last line would not show up if the corresponding projection (namely
         :g:`Prf_equiv`) were annotated as not canonical, as described above.
      *)
