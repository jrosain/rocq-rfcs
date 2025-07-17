- Title: Elimination Constraints for Bounded Sort Polymorphism

- Drivers: Johann Rosain (@jrosain), Tomàs Dìaz (@TDiazT)

----

# Summary

Sort polymorphism has been implemented in Rocq since version 8.19. However, it suffers
from a lack of expressiveness, examplified by the impossibility to generate a single
eliminator for sort-polymorphic inductives or to infer a principal type.

In this RFC, we propose to solve these issues by implementing *bounded sort polymorphism*
using elimination constraints. In particular, we:
1. Expose a new API for elimination using an elimination constraint graph.
2. Add elimination constraints to the parser.
3. Update the `Set Universe Polymorphism` flag to elaborate elimination constraints (which
   give the principal type of a term).
4. Replace the old `Type` syntax with a new one (e.g., 𝒰 or simply `U` or
   `Sort`) so that it's clear that the sort gets elaborated.
5. Relax the conditions on enabling the $\eta$ rule for sort-polymorphic records.

# Motivation

In Rocq's Corelib, we can find duplicated inductive types, *e.g.*:
```coq
Inductive sig (A:Type) (P:A -> Prop) : Type :=
  exist : forall x:A, P x -> sig P.

Inductive sigT (A:Type) (P:A -> Type) : Type :=
  existT : forall x:A, P x -> sigT P.

Inductive ex (A:Type) (P:A -> Prop) : Prop :=
  ex_intro : forall x:A, P x -> ex (A:=A) P.
```
Since Coq 8.19 and the introduction of sort polymorphism, these different inductives can
be factorized to:
```coq
Inductive sigma@{s1 s2 s3;l1 l2} (A:Type@{s1;l1}) (P:A -> Type@{s2;l2}) : Type@{s3;max(l1,l2)} :=
  exist : forall x:A, P x -> sigma P.
```
Given a dependent pair built with a carrier type in `Type`, one cannot project it unless
the pair itself lives in `Type`, the only way to ensure this rule is
to use the same sort variable for both the carrier type and the resulting type:
```coq
Definition proj1@{s1 s2;l1 l2} {A:Type@{s1;l1}} {P:A -> Type@{s2;l2}} (p:sigma@{s1 s2 s1}
A P) : A :=
	match p with
	| exist x _ => x
	end.
```
Moreover, the same mechanism applies for the second projection, i.e., `proj2` can only be
defined on dependent pairs featuring a single sort variable. This issue is even more
problematic on negative types, as a primitive record must follow both restrictions at its
definition, i.e., only the following record is allowed:
```coq
#[projections(primitive=yes)]
Record Prod@{s;l1 l2} (A:Type@{s;l1}) (P:A -> Type@{s;l2}) : Type@{s;max(l1,l2)} :=
  pair { fst: A; snd: P fst }.
```

# Detailed design

We introduce a notation of elimination constraints between sorts `s1 ~> s2` which lets us
write the generic projection:
```coq
Definition proj1@{s1 s2 s3;l1 l2|s3 ~> s1} {A:Type@{s1;l1}} {P:A -> Type@{s2;l2}} (p:sigma@{s1 s2 s3}
A P) : A :=
	match p with
	| exist x _ => x
	end.

#[projections(primitive=yes)]
Record Prod@{s1 s2 s3;l1 l2|s3 ~> s1, s3 ~> s2} (A:Type@{s1;l1}) (P:A -> Type@{s2;l2}) : Type@{s3;max(l1,l2)} :=
  pair { fst: A; snd: P fst }.
```

This is achieved by collecting elimination constraints inside a directed graph (using the
generic interface of `AcyclicGraph`). Using the acyclic graph allows an automated
management of transitivity, easily catching and prohibiting definitions such as the following:
```coq
Definition proj1'@{s;|SProp ~> s, s ~> Type} (A:Type) (P:A -> Type) (p:sigma@{Type Type
SProp} A P) : Type :=
  match (match p return exist@{Type Type s;_ _} with exist x p => exist x p end) with
  | exist x _ => x
  end.
```

## Side Effects

Allowing `g ~> s` for `g` a ground sort makes `s` inherit properties of `g`. For instance,
having `SProp ~> s` and `s` not proof irrelevant breaks the decidability of typing, as
illustrated by the following example:
```coq
Definition f@{s;l|SProp ~> s} (b:bool@{SProp;}) (A:Type@{s;l}) (x y:A) : A :=
  if b then x else y.
```
Here, `f true@{SProp;} x y` is definitionally equal to `f false@{SProp;} x y` by the congruence
rule for the application, thus `x` should be definitionally equal to `y`.

In a more generic fashion, any specific symbols together with defitional equalities
introduced by a ground sort should be inherited through elimination constraints, e.g.,
introducing `Exn` as a ground sort of exceptions, every `s` such that `Exn ~> s` must have
a `raise` and the associated definitional equalities.

As this issue touches conversion, we plan to forbid the constraint `SProp ~> s` until we
update the conversion to get back decidability of type-checking.

A similar problem arises if we have two ground sorts `g ~> s` and `g' ~> s` with different
conversion rules. In this case, `s` is not instantiable and the constraint set becomes
invalid. But an invalid set of constraints featuring `g ~> s` and `g' ~> s` can become
valid further down the line. Our plan is to start by eagerly checking for that kind of
constraints while exposing the check function in the API of the elimination constraints
graph. Subsequently, we will refine the system to avoid eager checking, which will enable
adding more constraints and possibly making the constraint set valid again.

Another side effect comes from primitive records with the $\eta$ rule. For instance,
records in `Prop` or `Type` having all fields in `SProp` do not have $\eta$:
```coq
Record Pair:Type := { fst:SProp; snd:SProp }.
```
Otherwise, for `p,q:Pair`, we have by $\eta$ that `p = {| fst := fst p; snd := snd p |} = {| fst
:= fst q; snd = snd q |} = q`, which introduces proof irrelevance in `Type`. The current
strategy for unbounded sort polymorphism is to provide $\eta$ only to records having the
same sort, which by conservativity cannot go wrong.
However, this greatly constrains the possible records with $\eta$. We fix this by delaying the
decision of the $\eta$ rule at the time of conversion. For instance, when trying to
convert a pair of the following type:
```coq
Record Pair@{s1 s2 s3;l1 l2|s3 ~> s1, s3 ~> s2} (A:Type@{s1|l1}) (B:Type@{s2|l2}) : Type@{s3|max(l1,l2)} :=
  pair { fst: A; snd: B }.
```
$\eta$ will be allowed if e.g., the instance is `Prop, SProp, Type`, but disallowed if the
instance is e.g., `SProp, SProp, Type`.

## Backward compatibility

In order to be backward compatible with sort polymorphism, we start by hard-wiring `Type ~> s`
and reflexivity of sort variables w.r.t. elimination constraints. As this issue gets
solved by elaboration, we proceed to remove these static constraints from the kernel.

## Recap & planified PRs

We plan to introduce elimination constraints in Rocq in multiple PRs, that:
1. Contains the API for the elimination constraint graph and will start to make
   use of it in the kernel and, marginally, in the elaboration.
2. Makes elimination constraints available for the user via an update of the
   parsing and elaboration process.
3. Provides an update of the `Set Universe Polymorphism` flag to allow inference of
   elimination constraints.
4. Introduces a new notation that replaces `Type` to make it clearer that the sort gets
   elaborated.
5. Implements the dynamic $\eta$ conversion check.
6. Updates the conversion to enable `SProp ~> s` and definitional proof-irrelevance for
   `s`.
