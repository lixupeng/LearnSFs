(** * Basics: Functional Programming in Coq *)

(* REMINDER:

          #####################################################
          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
          #####################################################

   (See the [Preface] for why.)
*)

(* ################################################################# *)
(** * Introduction *)

(** The functional programming style is founded on simple, everyday
    mathematical intuition: If a procedure or method has no side
    effects, then (ignoring efficiency) all we need to understand
    about it is how it maps inputs to outputs -- that is, we can think
    of it as just a concrete method for computing a mathematical
    function.  This is one sense of the word "functional" in
    "functional programming."  The direct connection between programs
    and simple mathematical objects supports both formal correctness
    proofs and sound informal reasoning about program behavior.

    The other sense in which functional programming is "functional" is
    that it emphasizes the use of functions (or methods) as
    _first-class_ values -- i.e., values that can be passed as
    arguments to other functions, returned as results, included in
    data structures, etc.  The recognition that functions can be
    treated as data gives rise to a host of useful and powerful
    programming idioms.

    Other common features of functional languages include _algebraic
    data types_ and _pattern matching_, which make it easy to
    construct and manipulate rich data structures, and sophisticated
    _polymorphic type systems_ supporting abstraction and code reuse.
    Coq offers all of these features.

    The first half of this chapter introduces the most essential
    elements of Coq's functional programming language, called
    _Gallina_.  The second half introduces some basic _tactics_ that
    can be used to prove properties of Coq programs. *)

(* ################################################################# *)
(** * Data and Functions *)
(* ================================================================= *)
(** ** Enumerated Types *)

(** One notable aspect of Coq is that its set of built-in
    features is _extremely_ small.  For example, instead of providing
    the usual palette of atomic data types (booleans, integers,
    strings, etc.), Coq offers a powerful mechanism for defining new
    data types from scratch, with all these familiar types as
    instances.

    Naturally, the Coq distribution comes preloaded with an extensive
    standard library providing definitions of booleans, numbers, and
    many common data structures like lists and hash tables.  But there
    is nothing magic or primitive about these library definitions.  To
    illustrate this, we will explicitly recapitulate all the
    definitions we need in this course, rather than just getting them
    implicitly from the library. *)

(* ================================================================= *)
(** ** Days of the Week *)

(** To see how this definition mechanism works, let's start with
    a very simple example.  The following declaration tells Coq that
    we are defining a new set of data values -- a _type_. *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(** The type is called [day], and its members are [monday],
    [tuesday], etc.  The second and following lines of the definition
    can be read "[monday] is a [day], [tuesday] is a [day], etc."

    Having defined [day], we can write functions that operate on
    days. *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(** One thing to note is that the argument and return types of
    this function are explicitly declared.  Like most functional
    programming languages, Coq can often figure out these types for
    itself when they are not given explicitly -- i.e., it can do _type
    inference_ -- but we'll generally include them to make reading
    easier. *)

(** Having defined a function, we should check that it works on
    some examples.  There are actually three different ways to do this
    in Coq.  First, we can use the command [Compute] to evaluate a
    compound expression involving [next_weekday]. *)

Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

(** (We show Coq's responses in comments, but, if you have a
    computer handy, this would be an excellent moment to fire up the
    Coq interpreter under your favorite IDE -- either CoqIde or Proof
    General -- and try this for yourself.  Load this file, [Basics.v],
    from the book's Coq sources, find the above example, submit it to
    Coq, and observe the result.)

    Second, we can record what we _expect_ the result to be in the
    form of a Coq example: *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(** This declaration does two things: it makes an
    assertion (that the second weekday after [saturday] is [tuesday]),
    and it gives the assertion a name that can be used to refer to it
    later.  Having made the assertion, we can also ask Coq to verify
    it, like this: *)

Proof. simpl. reflexivity.  Qed.

(** The details are not important for now (we'll come back to
    them in a bit), but essentially this can be read as "The assertion
    we've just made can be proved by observing that both sides of the
    equality evaluate to the same thing, after some simplification."

    Third, we can ask Coq to _extract_, from our [Definition], a
    program in some other, more conventional, programming
    language (OCaml, Scheme, or Haskell) with a high-performance
    compiler.  This facility is very interesting, since it gives us a
    way to go from proved-correct algorithms written in Gallina to
    efficient machine code.  (Of course, we are trusting the
    correctness of the OCaml/Haskell/Scheme compiler, and of Coq's
    extraction facility itself, but this is still a big step forward
    from the way most software is developed today.) Indeed, this is
    one of the main uses for which Coq was developed.  We'll come back
    to this topic in later chapters. *)

(* ================================================================= *)
(** ** Homework Submission Guidelines *)

(** If you are using Software Foundations in a course, your instructor
    may use automatic scripts to help grade your homework assignments.
    In order for these scripts to work correctly (so that you get full
    credit for your work!), please be careful to follow these rules:
      - The grading scripts work by extracting marked regions of the
        .v files that you submit.  It is therefore important that you
        do not alter the "markup" that delimits exercises: the
        Exercise header, the name of the exercise, the "empty square
        bracket" marker at the end, etc.  Please leave this markup
        exactly as you find it.
      - Do not delete exercises.  If you skip an exercise (e.g.,
        because it is marked Optional, or because you can't solve it),
        it is OK to leave a partial proof in your .v file, but in this
        case please make sure it ends with [Admitted] (not, for
        example [Abort]).
      - It is fine to use additional definitions (of helper functions,
        useful lemmas, etc.) in your solutions.  You can put these
        between the exercise header and the theorem you are asked to
        prove. *)

(* ================================================================= *)
(** ** Booleans *)

(** In a similar way, we can define the standard type [bool] of
    booleans, with members [true] and [false]. *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(** Although we are rolling our own booleans here for the sake
    of building up everything from scratch, Coq does, of course,
    provide a default implementation of the booleans, together with a
    multitude of useful functions and lemmas.  (Take a look at
    [Coq.Init.Datatypes] in the Coq library documentation if you're
    interested.)  Whenever possible, we'll name our own definitions
    and theorems so that they exactly coincide with the ones in the
    standard library.

    Functions over booleans can be defined in the same way as
    above: *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** The last two of these illustrate Coq's syntax for
    multi-argument function definitions.  The corresponding
    multi-argument application syntax is illustrated by the following
    "unit tests," which constitute a complete specification -- a truth
    table -- for the [orb] function: *)

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(** We can also introduce some familiar syntax for the boolean
    operations we have just defined. The [Notation] command defines a new
    symbolic notation for an existing definition. *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** _A note on notation_: In [.v] files, we use square brackets
    to delimit fragments of Coq code within comments; this convention,
    also used by the [coqdoc] documentation tool, keeps them visually
    separate from the surrounding text.  In the html version of the
    files, these pieces of text appear in a [different font].

    The command [Admitted] can be used as a placeholder for an
    incomplete proof.  We'll use it in exercises, to indicate the
    parts that we're leaving for you -- i.e., your job is to replace
    [Admitted]s with real proofs. *)

(** **** Exercise: 1 star (nandb)  *)
(** Remove "[Admitted.]" and complete the definition of the following
    function; then make sure that the [Example] assertions below can
    each be verified by Coq.  (Remove "[Admitted.]" and fill in each
    proof, following the model of the [orb] tests above.) The function
    should return [true] if either or both of its inputs are
    [false]. *)
 
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => (negb b2)
  | false => true
  end.

Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star (andb3)  *)
(** Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => (andb b2 b3)
  | false => false
  end.

Example test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** Function Types *)

(** Every expression in Coq has a type, describing what sort of
    thing it computes. The [Check] command asks Coq to print the type
    of an expression. *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and
    they are written with arrows. *)

Check negb.
(* ===> negb : bool -> bool *)

(** The type of [negb], written [bool -> bool] and pronounced
    "[bool] arrow [bool]," can be read, "Given an input of type
    [bool], this function produces an output of type [bool]."
    Similarly, the type of [andb], written [bool -> bool -> bool], can
    be read, "Given two inputs, both of type [bool], this function
    produces an output of type [bool]." *)

(* ================================================================= *)
(** ** Compound Types *)

(** The types we have defined so far are examples of "enumerated
    types": their definitions explicitly enumerate a finite set of
    elements, each of which is just a bare constructor.  Here is a
    more interesting type definition, where one of the constructors
    takes an argument: *)

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb -> color.

(** Let's look at this in a little more detail.

    Every inductively defined type ([day], [bool], [rgb], [color],
    etc.) contains a set of _constructor expressions_ built from
    _constructors_ like [red], [primary], [true], [false], [monday],
    etc.  The definitions of [rgb] and [color] say how expressions in
    the sets [rgb] and [color] can be built:

    - [red], [green], and [blue] are the constructors of [rgb];
    - [black], [white], and [primary] are the constructors of [color];
    - the expression [red] belongs to the set [rgb], as do the
      expressions [green] and [blue];
    - the expressions [black] and [white] belong to the set [color];
    - if [p] is an expression belonging to the set [rgb], then
      [primary p] (pronounced "the constructor [primary] applied to
      the argument [p]") is an expression belonging to the set
      [color]; and
    - expressions formed in these ways are the _only_ ones belonging
      to the sets [rgb] and [color]. *)

(** We can define functions on colors using pattern matching just as
    we have done for [day] and [bool]. *)

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

(** Since the [primary] constructor takes an argument, a pattern
    matching [primary] should include either a variable (as above) or
    a constant of appropriate type (as below). *)

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

(** The pattern [primary _] here is shorthand for "[primary] applied
    to any [rgb] constructor except [red]."  (The wildcard pattern [_]
    has the same effect as the dummy pattern variable [p] in the
    definition of [monochrome].) *)

(* ================================================================= *)
(** ** Modules *)

(** Coq provides a _module system_, to aid in organizing large
    developments.  In this course we won't need most of its features,
    but one is useful: If we enclose a collection of declarations
    between [Module X] and [End X] markers, then, in the remainder of
    the file after the [End], these definitions are referred to by
    names like [X.foo] instead of just [foo].  We will use this
    feature to introduce the definition of the type [nat] in an inner
    module so that it does not interfere with the one from the
    standard library (which we want to use in the rest because it
    comes with a tiny bit of convenient special notation).  *)

Module NatPlayground.

(* ================================================================= *)
(** ** Numbers *)

(** An even more interesting way of defining a type is to allow its
    constrctors to take arguments from the very same type -- that is,
    to allow the rules describing its elements to be _inductive_.

    For example, we can define (a unary representation of) natural
    numbers as follows: *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(** The clauses of this definition can be read:
      - [O] is a natural number (note that this is the letter "[O],"
        not the numeral "[0]").
      - [S] can be put in front of a natural number to yield another
        one -- if [n] is a natural number, then [S n] is too. *)

(** Again, let's look at this in a little more detail.  The definition
    of [nat] says how expressions in the set [nat] can be built:

    - [O] and [S] are constructors;
    - the expression [O] belongs to the set [nat];
    - if [n] is an expression belonging to the set [nat], then [S n]
      is also an expression belonging to the set [nat]; and
    - expressions formed in these two ways are the only ones belonging
      to the set [nat]. *)

(** The same rules apply for our definitions of [day], [bool],
    [color], etc.

    The above conditions are the precise force of the [Inductive]
    declaration.  They imply that the expression [O], the expression
    [S O], the expression [S (S O)], the expression [S (S (S O))], and
    so on all belong to the set [nat], while other expressions built
    from data constructors, like [true], [andb true false], [S (S
    false)], and [O (O (O S))] do not.

    A critical point here is that what we've done so far is just to
    define a _representation_ of numbers: a way of writing them down.
    The names [O] and [S] are arbitrary, and at this point they have
    no special meaning -- they are just two different marks that we
    can use to write down numbers (together with a rule that says any
    [nat] will be written as some string of [S] marks followed by an
    [O]).  If we like, we can write essentially the same definition
    this way: *)

Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' -> nat'.

(** The _interpretation_ of these marks comes from how we use them to
    compute. *)

(** We can do this by writing functions that pattern match on
    representations of natural numbers just as we did above with
    booleans and days -- for example, here is the predecessor
    function: *)

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** The second branch can be read: "if [n] has the form [S n']
    for some [n'], then return [n']."  *)

End NatPlayground.

(** Because natural numbers are such a pervasive form of data,
    Coq provides a tiny bit of built-in magic for parsing and printing
    them: ordinary arabic numerals can be used as an alternative to
    the "unary" notation defined by the constructors [S] and [O].  Coq
    prints numbers in arabic form by default: *)

Check (S (S (S (S O)))).
  (* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute (minustwo 4).
  (* ===> 2 : nat *)

(** The constructor [S] has the type [nat -> nat], just like 
    [pred] and functions like [minustwo]: *)

Check S.
Check pred.
Check minustwo.

(** These are all things that can be applied to a number to yield a
    number.  However, there is a fundamental difference between the
    first one and the other two: functions like [pred] and [minustwo]
    come with _computation rules_ -- e.g., the definition of [pred]
    says that [pred 2] can be simplified to [1] -- while the
    definition of [S] has no such behavior attached.  Although it is
    like a function in the sense that it can be applied to an
    argument, it does not _do_ anything at all!  It is just a way of
    writing down numbers.  (Think about standard arabic numerals: the
    numeral [1] is not a computation; it's a piece of data.  When we
    write [111] to mean the number one hundred and eleven, we are
    using [1], three times, to write down a concrete representation of
    a number.)

    For most function definitions over numbers, just pattern matching
    is not enough: we also need recursion.  For example, to check that
    a number [n] is even, we may need to recursively check whether
    [n-2] is even.  To write such functions, we use the keyword
    [Fixpoint]. *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** We can define [oddb] by a similar [Fixpoint] declaration, but here
    is a simpler definition: *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    oddb 1 = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    oddb 4 = false.
Proof. simpl. reflexivity.  Qed.

(** (You will notice if you step through these proofs that
    [simpl] actually has no effect on the goal -- all of the work is
    done by [reflexivity].  We'll see more about why that is shortly.)

    Naturally, we can also define multi-argument functions by
    recursion.  *)

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** Adding three to two now gives us five, as we'd expect. *)

Compute (plus 3 2).

(** The simplification that Coq performs to reach this conclusion can
    be visualized as follows: *)

(*  [plus (S (S (S O))) (S (S O))]
==> [S (plus (S (S O)) (S (S O)))]
      by the second clause of the [match]
==> [S (S (plus (S O) (S (S O))))]
      by the second clause of the [match]
==> [S (S (S (plus O (S (S O)))))]
      by the second clause of the [match]
==> [S (S (S (S (S O))))]
      by the first clause of the [match]
*)

(** As a notational convenience, if two or more arguments have
    the same type, they can be written together.  In the following
    definition, [(n m : nat)] means just the same as if we had written
    [(n : nat) (m : nat)]. *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.

(** You can match two expressions at once by putting a comma
    between them: *)

Fixpoint minus (n m:nat) : nat :=
  match (n, m) with
  | (O   , _)    => O
  | (S _ , O)    => n
  | (S n', S m') => minus n' m'
  end.

(** Again, the _ in the first line is a _wildcard pattern_.  Writing
    [_] in a pattern is the same as writing some variable that doesn't
    get used on the right-hand side.  This avoids the need to invent a
    variable name. *)

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(** **** Exercise: 1 star (factorial)  *)
(** Recall the standard mathematical factorial function:

       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

    Translate this into Coq. *)

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
  end.

Example test_factorial1:          (factorial 3) = 6.
Proof. simpl. reflexivity.  Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity.  Qed.
(** [] *)

(** We can make numerical expressions a little easier to read and
    write by introducing _notations_ for addition, multiplication, and
    subtraction. *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

(** (The [level], [associativity], and [nat_scope] annotations
    control how these notations are treated by Coq's parser.  The
    details are not important for our purposes, but interested readers
    can refer to the optional "More on Notation" section at the end of
    this chapter.)

    Note that these do not change the definitions we've already made:
    they are simply instructions to the Coq parser to accept [x + y]
    in place of [plus x y] and, conversely, to the Coq pretty-printer
    to display [plus x y] as [x + y]. *)

(** When we say that Coq comes with almost nothing built-in, we really
    mean it: even equality testing for numbers is a user-defined
    operation!  We now define a function [beq_nat], which tests
    [nat]ural numbers for [eq]uality, yielding a [b]oolean.  Note the
    use of nested [match]es (we could also have used a simultaneous
    match, as we did in [minus].) *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(** The [leb] function tests whether its first argument is less than or
  equal to its second argument, yielding a boolean. *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1:             (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:             (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:             (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

(** **** Exercise: 1 star (blt_nat)  *)
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined function. *)

Definition blt_nat (n m : nat) : bool :=
  match (beq_nat n m) with
  | true => false
  | false => leb n m
  end.

Example test_blt_nat1:             (blt_nat 2 2) = false.
Proof. simpl. reflexivity.  Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
Proof. simpl. reflexivity.  Qed.
(** [] *)

(* ################################################################# *)
(** * Proof by Simplification *)

(** Now that we've defined a few datatypes and functions, let's
    turn to stating and proving properties of their behavior.
    Actually, we've already started doing this: each [Example] in the
    previous sections makes a precise claim about the behavior of some
    function on some particular inputs.  The proofs of these claims
    were always the same: use [simpl] to simplify both sides of the
    equation, then use [reflexivity] to check that both sides contain
    identical values.

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    [0] is a "neutral element" for [+] on the left can be proved just
    by observing that [0 + n] reduces to [n] no matter what [n] is, a
    fact that can be read directly off the definition of [plus].*)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  Qed.

(** (You may notice that the above statement looks different in
    the [.v] file in your IDE than it does in the HTML rendition in
    your browser, if you are viewing both. In [.v] files, we write the
    [forall] universal quantifier using the reserved identifier
    "forall."  When the [.v] files are converted to HTML, this gets
    transformed into an upside-down-A symbol.)

    This is a good place to mention that [reflexivity] is a bit
    more powerful than we have admitted. In the examples we have seen,
    the calls to [simpl] were actually not needed, because
    [reflexivity] can perform some simplification automatically when
    checking that two sides are equal; [simpl] was just added so that
    we could see the intermediate state -- after simplification but
    before finishing the proof.  Here is a shorter proof of the
    theorem: *)

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(** Moreover, it will be useful later to know that [reflexivity]
    does somewhat _more_ simplification than [simpl] does -- for
    example, it tries "unfolding" defined terms, replacing them with
    their right-hand sides.  The reason for this difference is that,
    if reflexivity succeeds, the whole goal is finished and we don't
    need to look at whatever expanded expressions [reflexivity] has
    created by all this simplification and unfolding; by contrast,
    [simpl] is used in situations where we may have to read and
    understand the new goal that it creates, so we would not want it
    blindly expanding definitions and leaving the goal in a messy
    state.

    The form of the theorem we just stated and its proof are almost
    exactly the same as the simpler examples we saw earlier; there are
    just a few differences.

    First, we've used the keyword [Theorem] instead of [Example].
    This difference is mostly a matter of style; the keywords
    [Example] and [Theorem] (and a few others, including [Lemma],
    [Fact], and [Remark]) mean pretty much the same thing to Coq.

    Second, we've added the quantifier [forall n:nat], so that our
    theorem talks about _all_ natural numbers [n].  Informally, to
    prove theorems of this form, we generally start by saying "Suppose
    [n] is some number..."  Formally, this is achieved in the proof by
    [intros n], which moves [n] from the quantifier in the goal to a
    _context_ of current assumptions.

    The keywords [intros], [simpl], and [reflexivity] are examples of
    _tactics_.  A tactic is a command that is used between [Proof] and
    [Qed] to guide the process of checking some claim we are making.
    We will see several more tactics in the rest of this chapter and
    yet more in future chapters. *)

(** Other similar theorems can be proved with the same pattern. *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(** The [_l] suffix in the names of these theorems is
    pronounced "on the left." *)

(** It is worth stepping through these proofs to observe how the
    context and the goal change.  You may want to add calls to [simpl]
    before [reflexivity] to see the simplifications that Coq performs
    on the terms before checking that they are equal. *)

(* ################################################################# *)
(** * Proof by Rewriting *)

(** This theorem is a bit more interesting than the others we've
    seen: *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

(** Instead of making a universal claim about all numbers [n] and [m],
    it talks about a more specialized property that only holds when [n
    = m].  The arrow symbol is pronounced "implies."

    As before, we need to be able to reason by assuming we are given such
    numbers [n] and [m].  We also need to assume the hypothesis
    [n = m]. The [intros] tactic will serve to move all three of these
    from the goal into assumptions in the current context.

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Coq to
    perform this replacement is called [rewrite]. *)

Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity.  Qed.

(** The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the name [H].
    The third tells Coq to rewrite the current goal ([n + n = m + m])
    by replacing the left side of the equality hypothesis [H] with the
    right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes.) *)

(** **** Exercise: 1 star (plus_id_exercise)  *)
(** Remove "[Admitted.]" and fill in the proof. *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros nm mo.
  rewrite -> nm.
  rewrite -> mo.
  reflexivity.
Qed.
(** [] *)

(** The [Admitted] command tells Coq that we want to skip trying
    to prove this theorem and just accept it as a given.  This can be
    useful for developing longer proofs, since we can state subsidiary
    lemmas that we believe will be useful for making some larger
    argument, use [Admitted] to accept them on faith for the moment,
    and continue working on the main argument until we are sure it
    makes sense; then we can go back and fill in the proofs we
    skipped.  Be careful, though: every time you say [Admitted] you
    are leaving a door open for total nonsense to enter Coq's nice,
    rigorous, formally checked world! *)

(** We can also use the [rewrite] tactic with a previously proved
    theorem instead of a hypothesis from the context. If the statement
    of the previously proved theorem involves quantified variables,
    as in the example below, Coq tries to instantiate them
    by matching with the current goal. *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(** **** Exercise: 2 stars (mult_S_1)  *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m m_n.
  rewrite -> plus_1_l.
  rewrite <- m_n.
  reflexivity.
Qed.
  

  (* (N.b. This proof can actually be completed without using [rewrite],
     but please do use [rewrite] for the sake of the exercise.) *)
(** [] *)

(* ################################################################# *)
(** * Proof by Case Analysis *)

(** Of course, not everything can be proved by simple
    calculation and rewriting: In general, unknown, hypothetical
    values (arbitrary numbers, booleans, lists, etc.) can block
    simplification.  For example, if we try to prove the following
    fact using the [simpl] tactic as above, we get stuck.  (We then
    use the [Abort] command to give up on it for the moment.)*)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl.  (* does nothing! *)
Abort.

(** The reason for this is that the definitions of both
    [beq_nat] and [+] begin by performing a [match] on their first
    argument.  But here, the first argument to [+] is the unknown
    number [n] and the argument to [beq_nat] is the compound
    expression [n + 1]; neither can be simplified.

    To make progress, we need to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [beq_nat (n + 1) 0] and check that it is, indeed, [false].  And
    if [n = S n'] for some [n'], then, although we don't know exactly
    what number [n + 1] yields, we can calculate that, at least, it
    will begin with one [S], and this is enough to calculate that,
    again, [beq_nat (n + 1) 0] will yield [false].

    The tactic that tells Coq to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [destruct]. *)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.   Qed.

(** The [destruct] generates _two_ subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem. The
    annotation "[as [| n']]" is called an _intro pattern_.  It tells
    Coq what variable names to introduce in each subgoal.  In general,
    what goes between the square brackets is a _list of lists_ of
    names, separated by [|].  In this case, the first component is
    empty, since the [O] constructor is nullary (it doesn't have any
    arguments).  The second component gives a single name, [n'], since
    [S] is a unary constructor.

    The [-] signs on the second and third lines are called _bullets_,
    and they mark the parts of the proof that correspond to each
    generated subgoal.  The proof script that comes after a bullet is
    the entire proof for a subgoal.  In this example, each of the
    subgoals is easily proved by a single use of [reflexivity], which
    itself performs some simplification -- e.g., the first one
    simplifies [beq_nat (S n' + 1) 0] to [false] by first rewriting
    [(S n' + 1)] to [S (n' + 1)], then unfolding [beq_nat], and then
    simplifying the [match].

    Marking cases with bullets is entirely optional: if bullets are
    not present, Coq simply asks you to prove each subgoal in
    sequence, one at a time. But it is a good idea to use bullets.
    For one thing, they make the structure of a proof apparent, making
    it more readable. Also, bullets instruct Coq to ensure that a
    subgoal is complete before trying to verify the next one,
    preventing proofs for different subgoals from getting mixed
    up. These issues become especially important in large
    developments, where fragile proofs lead to long debugging
    sessions.

    There are no hard and fast rules for how proofs should be
    formatted in Coq -- in particular, where lines should be broken
    and how sections of the proof should be indented to indicate their
    nested structure.  However, if the places where multiple subgoals
    are generated are marked with explicit bullets at the beginning of
    lines, then the proof will be readable almost no matter what
    choices are made about other aspects of layout.

    This is also a good place to mention one other piece of somewhat
    obvious advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or writing entire proofs on one line.  Good style lies somewhere
    in the middle.  One reasonable convention is to limit yourself to
    80-character lines.

    The [destruct] tactic can be used with any inductively defined
    datatype.  For example, we use it next to prove that boolean
    negation is involutive -- i.e., that negation is its own
    inverse. *)


Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.  Qed.

(** Note that the [destruct] here has no [as] clause because
    none of the subcases of the [destruct] need to bind any variables,
    so there is no need to specify any names.  (We could also have
    written [as [|]], or [as []].)  In fact, we can omit the [as]
    clause from _any_ [destruct] and Coq will fill in variable names
    automatically.  This is generally considered bad style, since Coq
    often makes confusing choices of names when left to its own
    devices.

    It is sometimes useful to invoke [destruct] inside a subgoal,
    generating yet more proof obligations. In this case, we use
    different kinds of bullets to mark goals on different "levels."
    For example: *)


Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

(** Each pair of calls to [reflexivity] corresponds to the
    subgoals that were generated after the execution of the [destruct c]
    line right above it. *)

(** Besides [-] and [+], we can use [*] (asterisk) as a third kind of
    bullet.  We can also enclose sub-proofs in curly braces, which is
    useful in case we ever encounter a proof that generates more than
    three levels of subgoals: *)

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

(** Since curly braces mark both the beginning and the end of a
    proof, they can be used for multiple subgoal levels, as this
    example shows. Furthermore, curly braces allow us to reuse the
    same bullet shapes at multiple levels in a proof: *)

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

(** Before closing the chapter, let's mention one final convenience.  
    As you may have noticed, many proofs perform case analysis on a variable 
    right after introducing it:

       intros x y. destruct y as [|y].

    This pattern is so common that Coq provides a shorthand for it: we
    can perform case analysis on a variable when introducing it by
    using an intro pattern instead of a variable name. For instance,
    here is a shorter proof of the [plus_1_neq_0] theorem above. *)

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.  Qed.

(** If there are no arguments to name, we can just write [[]]. *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** **** Exercise: 2 stars (andb_true_elim2)  *)
(** Prove the following claim, marking cases (and subcases) with
    bullets when you use [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros H. destruct c.
    + reflexivity.
    + rewrite -> H. reflexivity.
Qed.

(** **** Exercise: 1 star (zero_nbeq_plus_1)  *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros [| n'].
  - reflexivity.
  - simpl. reflexivity.
Qed.

(* ================================================================= *)
(** ** More on Notation (Optional) *)

(** (In general, sections marked Optional are not needed to follow the
    rest of the book, except possibly other Optional sections.  On a
    first reading, you might want to skim these sections so that you
    know what's there for future reference.)

    Recall the notation definitions for infix plus and times: *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

(** For each notation symbol in Coq, we can specify its _precedence
    level_ and its _associativity_.  The precedence level [n] is
    specified by writing [at level n]; this helps Coq parse compound
    expressions.  The associativity setting helps to disambiguate
    expressions containing multiple occurrences of the same
    symbol. For example, the parameters specified above for [+] and
    [*] say that the expression [1+2*3*4] is shorthand for
    [(1+((2*3)*4))]. Coq uses precedence levels from 0 to 100, and
    _left_, _right_, or _no_ associativity.  We will see more examples
    of this later, e.g., in the [Lists]
    chapter.

    Each notation symbol is also associated with a _notation scope_.
    Coq tries to guess what scope is meant from context, so when it
    sees [S(O*O)] it guesses [nat_scope], but when it sees the
    cartesian product (tuple) type [bool*bool] (which we'll see in
    later chapters) it guesses [type_scope].  Occasionally, it is
    necessary to help it out with percent-notation by writing
    [(x*y)%nat], and sometimes in what Coq prints it will use [%nat]
    to indicate what scope a notation is in.

    Notation scopes also apply to numeral notation ([3], [4], [5],
    etc.), so you may sometimes see [0%nat], which means [O] (the
    natural number [0] that we're using in this chapter), or [0%Z],
    which means the Integer zero (which comes from a different part of
    the standard library).

    Pro tip: Coq's notation mechanism is not especially powerful.
    Don't expect too much from it! *)

(* ================================================================= *)
(** ** Fixpoints and Structural Recursion (Optional) *)

(** Here is a copy of the definition of addition: *)

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.

(** When Coq checks this definition, it notes that [plus'] is
    "decreasing on 1st argument."  What this means is that we are
    performing a _structural recursion_ over the argument [n] -- i.e.,
    that we make recursive calls only on strictly smaller values of
    [n].  This implies that all calls to [plus'] will eventually
    terminate.  Coq demands that some argument of _every_ [Fixpoint]
    definition is "decreasing."

    This requirement is a fundamental feature of Coq's design: In
    particular, it guarantees that every function that can be defined
    in Coq will terminate on all inputs.  However, because Coq's
    "decreasing analysis" is not very sophisticated, it is sometimes
    necessary to write functions in slightly unnatural ways. *)

(** **** Exercise: 2 stars, optional (decreasing)  *)
(** To get a concrete sense of this, find a way to write a sensible
    [Fixpoint] definition (of a simple function on numbers, say) that
    _does_ terminate on all inputs, but that Coq will reject because
    of this restriction. *)

(* FILL IN HERE *)
(** [] *)

(* ################################################################# *)
(** * More Exercises *)

(** **** Exercise: 2 stars (boolean_functions)  *)
(** Use the tactics you have learned so far to prove the following
    theorem about boolean functions. *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

(** Now state and prove a theorem [negation_fn_applied_twice] similar
    to the previous one but where the second hypothesis says that the
    function [f] has the property that [f x = negb x].*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, optional (andb_eq_orb)  *)
(** Prove the following theorem.  (Hint: This one can be a bit tricky,
    depending on how you approach it.  You will probably need both
    [destruct] and [rewrite], but destructing everything in sight is
    not the best way.) *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b.
  - simpl. intros H. rewrite -> H. reflexivity.
  - simpl. intros. rewrite -> H. reflexivity. 
Qed.

(** [] *)

(** **** Exercise: 3 stars (binary)  *)
(** Consider a different, more efficient representation of natural
    numbers using a binary rather than unary system.  That is, instead
    of saying that each natural number is either zero or the successor
    of a natural number, we can say that each binary number is either

      - zero,
      - twice a binary number, or
      - one more than twice a binary number.

    (a) First, write an inductive definition of the type [bin]
        corresponding to this description of binary numbers.

        (Hint: Recall that the definition of [nat] above,

         Inductive nat : Type := | O : nat | S : nat -> nat.

        says nothing about what [O] and [S] "mean."  It just says "[O]
        is in the set called [nat], and if [n] is in the set then so
        is [S n]."  The interpretation of [O] as zero and [S] as
        successor/plus one comes from the way that we _use_ [nat]
        values, by writing functions to do things with them, proving
        things about them, and so on.  Your definition of [bin] should
        be correspondingly simple; it is the functions you will write
        next that will give it mathematical meaning.)

        One caveat: If you use [O] or [S] as constructor names in your
        definition, it will confuse the auto-grader script in
        BasicsTest.v.  Please choose different names.

    (b) Next, write an increment function [incr] for binary numbers,
        and a function [bin_to_nat] to convert binary numbers to unary
        numbers.

    (c) Write five unit tests [test_bin_incr1], [test_bin_incr2], etc.
        for your increment and binary-to-unary functions.  (A "unit
        test" in Coq is a specific [Example] that can be proved with
        just [reflexivity], as we've done for several of our
        definitions.)  Notice that incrementing a binary number and
        then converting it to unary should yield the same result as
        first converting it to unary and then incrementing. *)

Inductive bin : Type :=
  | Z : bin
  | D : bin -> bin
  | C : bin -> bin.
  
Fixpoint incr (b : bin) : bin :=
  match b with
  | Z => C Z
  | D b' => C b'
  | C b' => D (incr b')
  end.
  
Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
  | Z => O
  | D b' => (bin_to_nat b') + (bin_to_nat b')
  | C b' => S ((bin_to_nat b') + (bin_to_nat b'))
  end.
  
Example test_bin_incr0 : bin_to_nat Z = 0.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr1 : bin_to_nat (incr Z) = 1.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : bin_to_nat (incr (incr Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : bin_to_nat (incr (incr (incr Z))) = 3.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (incr (incr (incr (incr Z)))) = 4.
Proof. simpl. reflexivity. Qed.
(** [] *)

(** $Date: 2018-01-10 21:47:50 -0500 (Wed, 10 Jan 2018) $ *)



(** * Induction: Proof by Induction *)

(** Before getting started, we need to import all of our
    definitions from the previous chapter: *)

(** For the [Require Export] to work, you first need to use
    [coqc] to compile [Basics.v] into [Basics.vo].  This is like
    making a .class file from a .java file, or a .o file from a .c
    file.  There are two ways to do it:

     - In CoqIDE:

         Open [Basics.v].  In the "Compile" menu, click on "Compile
         Buffer".

     - From the command line: Either

         [make Basics.vo]

       (assuming you've downloaded the whole LF directory and have a
       working 'make' command) or

         [coqc Basics.v]

       (which should work from any terminal window).

   If you have trouble (e.g., if you get complaints about missing
   identifiers later in the file), it may be because the "load path"
   for Coq is not set up correctly.  The [Print LoadPath.] command may
   be helpful in sorting out such issues.

   In particular, if you see a message like

      [Compiled library Foo makes inconsistent assumptions over
      library Coq.Init.Bar]

   you should check whether you have multiple installations of Coq on
   your machine.  If so, it may be that commands (like [coqc]) that
   you execute in a terminal window are getting a different version of
   Coq than commands executed by Proof General or CoqIDE.

   One more tip for CoqIDE users: If you see messages like "Error:
   Unable to locate library Basics," a likely reason is
   inconsistencies between compiling things _within CoqIDE_ vs _using
   coqc_ from the command line.  This typically happens when there are
   two incompatible versions of coqc installed on your system (one
   associated with coqide, and one associated with coqc from the
   terminal).  The workaround for this situation is compiling using
   coqIDE only (i.e. choosing "make" from the menu), and avoiding
   using coqc directly at all. *)
(* ################################################################# *)
(** * Proof by Induction *)

(** We proved in the last chapter that [0] is a neutral element
    for [+] on the left, using an easy argument based on
    simplification.  We also observed that proving the fact that it is
    also a neutral element on the _right_... *)

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.

(** ... can't be done in the same simple way.  Just applying
  [reflexivity] doesn't work, since the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(** And reasoning by cases using [destruct n] doesn't get us much
    further: the branch of the case analysis where we assume [n = 0]
    goes through fine, but in the branch where [n = S n'] for some [n'] we
    get stuck in exactly the same way. *)

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* ...but here we are stuck again *)
Abort.

(** We could use [destruct n'] to get one step further, but,
    since [n] can be arbitrarily large, if we just go on like this
    we'll never finish. *)

(** To prove interesting facts about numbers, lists, and other
    inductively defined sets, we usually need a more powerful
    reasoning principle: _induction_.

    Recall (from high school, a discrete math course, etc.) the
    _principle of induction over natural numbers_: If [P(n)] is some
    proposition involving a natural number [n] and we want to show
    that [P] holds for all numbers [n], we can reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Coq, the steps are the same: we begin with the goal of proving
    [P(n)] for all [n] and break it down (by applying the [induction]
    tactic) into two separate subgoals: one where we must show [P(O)]
    and another where we must show [P(n') -> P(S n')].  Here's how
    this works for the theorem at hand: *)

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.

(** Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  Since there are two subgoals, the [as...] clause
    has two parts, separated by [|].  (Strictly speaking, we can omit
    the [as...] clause and Coq will choose names for us.  In practice,
    this is a bad idea, as Coq's automatic choices tend to be
    confusing.)

    In the first subgoal, [n] is replaced by [0].  No new variables
    are introduced (so the first part of the [as...] is empty), and
    the goal becomes [0 = 0 + 0], which follows by simplification.

    In the second subgoal, [n] is replaced by [S n'], and the
    assumption [n' + 0 = n'] is added to the context with the name
    [IHn'] (i.e., the Induction Hypothesis for [n']).  These two names
    are specified in the second part of the [as...] clause.  The goal
    in this case becomes [S n' = (S n') + 0], which simplifies to
    [S n' = S (n' + 0)], which in turn follows from [IHn']. *)


Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** (The use of the [intros] tactic in these proofs is actually
    redundant.  When applied to a goal that contains quantified
    variables, the [induction] tactic will automatically move them
    into the context as needed.) *)

(** **** Exercise: 2 stars, recommended (basic_induction)  *)
(** Prove the following using induction. You might need previously
    proven results. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.
  

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - intros m. simpl. rewrite -> IHn'. reflexivity.
Qed.
(* GRADE_THEOREM 0.5: plus_n_Sm *)


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [|n' IHn'].
  - intros m. rewrite <- plus_n_O. reflexivity.
  - intros m. rewrite <- plus_n_Sm. simpl. rewrite -> IHn'. reflexivity.
Qed.
(* GRADE_THEOREM 0.5: plus_comm *)

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - intros m p. simpl. rewrite -> IHn'. reflexivity.
Qed.
(* GRADE_THEOREM 0.5: plus_assoc *)
(** [] *)

(** **** Exercise: 2 stars (double_plus)  *)
(** Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. 
    rewrite <- plus_n_Sm. reflexivity.
Qed.
    
(** [] *)

(** **** Exercise: 2 stars, optional (evenb_S)  *)
(** One inconvenient aspect of our definition of [evenb n] is the
    recursive call on [n - 2]. This makes proofs about [evenb n]
    harder when done by induction on [n], since we may need an
    induction hypothesis about [n - 2]. The following lemma gives an
    alternative characterization of [evenb (S n)] that works better
    with induction: *)
    

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. rewrite -> negb_involutive. reflexivity.
Qed.
    
(** [] *)

(** **** Exercise: 1 star (destruct_induction)  *)
(** Briefly explain the difference between the tactics [destruct]
    and [induction].

(* FILL IN HERE *)
*)
(** [] *)

(* ################################################################# *)
(** * Proofs Within Proofs *)

(** In Coq, as in informal mathematics, large proofs are often
    broken into a sequence of theorems, with later proofs referring to
    earlier theorems.  But sometimes a proof will require some
    miscellaneous fact that is too trivial and of too little general
    interest to bother giving it its own top-level name.  In such
    cases, it is convenient to be able to simply state and prove the
    needed "sub-theorem" right at the point where it is used.  The
    [assert] tactic allows us to do this.  For example, our earlier
    proof of the [mult_0_plus] theorem referred to a previous theorem
    named [plus_O_n].  We could instead use [assert] to state and
    prove [plus_O_n] in-line: *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (We can also name the assertion with [as] just as
    we did above with [destruct] and [induction], i.e., [assert (0 + n
    = n) as H].)  Note that we surround the proof of this assertion
    with curly braces [{ ... }], both for readability and so that,
    when using Coq interactively, we can see more easily when we have
    finished this sub-proof.  The second goal is the same as the one
    at the point where we invoke [assert] except that, in the context,
    we now have the assumption [H] that [0 + n = n].  That is,
    [assert] generates one subgoal where we must prove the asserted
    fact and a second subgoal where we can use the asserted fact to
    make progress on whatever we were trying to prove in the first
    place. *)

(** Another example of [assert]... *)

(** For example, suppose we want to prove that [(n + m) + (p + q)
    = (m + n) + (p + q)]. The only difference between the two sides of
    the [=] is that the arguments [m] and [n] to the first inner [+]
    are swapped, so it seems we should be able to use the
    commutativity of addition ([plus_comm]) to rewrite one into the
    other.  However, the [rewrite] tactic is not very smart about
    _where_ it applies the rewrite.  There are three uses of [+] here,
    and it turns out that doing [rewrite -> plus_comm] will affect
    only the _outer_ one... *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrote the wrong plus! *)
Abort.

(** To use [plus_comm] at the point where we need it, we can introduce
    a local lemma stating that [n + m = m + n] (for the particular [m]
    and [n] that we are talking about here), prove this lemma using
    [plus_comm], and then use it to do the desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.  Qed.

(* ################################################################# *)
(** * Formal vs. Informal Proof *)

(** "_Informal proofs are algorithms; formal proofs are code_." *)

(** What constitutes a successful proof of a mathematical claim?
    The question has challenged philosophers for millennia, but a
    rough and ready definition could be this: A proof of a
    mathematical proposition [P] is a written (or spoken) text that
    instills in the reader or hearer the certainty that [P] is true --
    an unassailable argument for the truth of [P].  That is, a proof
    is an act of communication.

    Acts of communication may involve different sorts of readers.  On
    one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is that [P] can be mechanically
    derived from a certain set of formal logical rules, and the proof
    is a recipe that guides the program in checking this fact.  Such
    recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    and will thus necessarily be _informal_.  Here, the criteria for
    success are less clearly specified.  A "valid" proof is one that
    makes the reader believe [P].  But the same proof may be read by
    many different readers, some of whom may be convinced by a
    particular way of phrasing the argument, while others may not be.
    Some readers may be particularly pedantic, inexperienced, or just
    plain thick-headed; the only way to convince them will be to make
    the argument in painstaking detail.  But other readers, more
    familiar in the area, may find all this detail so overwhelming
    that they lose the overall thread; all they want is to be told the
    main ideas, since it is easier for them to fill in the details for
    themselves than to wade through a written presentation of them.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.

    In practice, however, mathematicians have developed a rich set of
    conventions and idioms for writing about complex mathematical
    objects that -- at least within a certain community -- make
    communication fairly reliable.  The conventions of this stylized
    form of communication give a fairly clear standard for judging
    proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can
    completely forget about informal ones!  Formal proofs are useful
    in many ways, but they are _not_ very efficient ways of
    communicating ideas between human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coq is perfectly happy with this.  For a human, however, it
    is difficult to make much sense of it.  We can use comments and
    bullets to show the structure a little more clearly... *)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** ... and if you're used to Coq you may be able to step
    through the tactics one after the other in your mind and imagine
    the state of the context and goal stack at each point, but if the
    proof were even a little bit more complicated this would be next
    to impossible.

    A (pedantic) mathematician might write the proof something like
    this: *)

(** - _Theorem_: For any [n], [m] and [p],

      n + (m + p) = (n + m) + p.

    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show

        0 + (m + p) = (0 + m) + p.

      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where

        n' + (m + p) = (n' + m) + p.

      We must show

        (S n') + (m + p) = ((S n') + m) + p.

      By the definition of [+], this follows from

        S (n' + (m + p)) = S ((n' + m) + p),

      which is immediate from the induction hypothesis.  _Qed_. *)

(** The overall form of the proof is basically similar, and of
    course this is no accident: Coq has been designed so that its
    [induction] tactic generates the same sub-goals, in the same
    order, as the bullet points that a mathematician would write.  But
    there are significant differences of detail: the formal proof is
    much more explicit in some ways (e.g., the use of [reflexivity])
    but much less explicit in others (in particular, the "proof state"
    at any given point in the Coq proof is completely implicit,
    whereas the informal proof reminds the reader several times where
    things stand). *)

(** **** Exercise: 2 stars, advanced, recommended (plus_comm_informal)  *)
(** Translate your solution for [plus_comm] into an informal proof:

    Theorem: Addition is commutative.

    Proof: (* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, optional (beq_nat_refl_informal)  *)
(** Write an informal proof of the following theorem, using the
    informal proof of [plus_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!

    Theorem: [true = beq_nat n n] for any [n].

    Proof: (* FILL IN HERE *)
*)
(** [] *)

(* ################################################################# *)
(** * More Exercises *)

(** **** Exercise: 3 stars, recommended (mult_comm)  *)
(** Use [assert] to help prove this theorem.  You shouldn't need to
    use induction on [plus_swap]. *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: m + p = p + m). 
    { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  rewrite -> plus_assoc.
  rewrite -> plus_comm.
  reflexivity.
Qed.
  
(** Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.  You may find that [plus_swap] comes in
    handy.) *)
    
Theorem mult_n_Sm : forall n m : nat,
  n * S m = n * m + n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. intros m. rewrite -> IHn'. 
    rewrite <- plus_n_Sm. rewrite -> plus_assoc. reflexivity.
Qed.
    

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  induction m as [| m' IHm'].
  - intros n. rewrite <- mult_n_O. reflexivity.
  - simpl. intros n.
    rewrite -> mult_n_Sm. rewrite -> plus_comm. 
    rewrite -> IHm'. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (more_exercises)  *)
(** Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before you hack!) *)

Check leb.

Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  (* induction n *) 
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.


Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  (* simpl *) 
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* simpl *) 
  intros b.
  rewrite <- andb_commutative.
  reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  (* induction p *)
  intros n m.
  induction p as [|p' IHp'].
  - intros H. 
    rewrite -> plus_O_n. rewrite -> plus_O_n.
    rewrite -> H.
    reflexivity.
  - intros H. simpl. rewrite -> IHp'.
    + reflexivity.
    + rewrite -> H. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* simpl *)
  reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* simpl *) 
  intros n.
  simpl. rewrite -> plus_n_O. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* destruct *)
  intros b c.
  destruct b,c.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* induction *)
  intros n m.
  induction p as [|p' IHp'].
  - rewrite -> mult_0_r.
    rewrite -> mult_0_r.
    rewrite -> mult_0_r.
    reflexivity.
  - rewrite -> mult_n_Sm. 
    rewrite -> mult_n_Sm.
    rewrite -> mult_n_Sm.
    rewrite -> IHp'.
    rewrite -> plus_assoc.
    rewrite -> plus_assoc.
    assert(H : n * p' + m * p' + n = n * p' + n + m * p').
    { 
      rewrite <- plus_assoc.
      rewrite <- plus_swap.
      rewrite -> plus_comm.
      reflexivity.
    }
    rewrite -> H.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* induction *)
  induction n as [|n' IHn'].
  - reflexivity.
  - intros m p. simpl. rewrite -> mult_plus_distr_r.
    rewrite -> IHn'. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (beq_nat_refl)  *)
(** Prove the following theorem.  (Putting the [true] on the left-hand
    side of the equality may look odd, but this is how the theorem is
    stated in the Coq standard library, so we follow suit.  Rewriting
    works equally well in either direction, so we will have no problem
    using the theorem no matter which way we state it.) *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (plus_swap')  *)
(** The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to: [replace (t) with (u)]
   replaces (all copies of) expression [t] in the goal by expression
   [u], and generates [t = u] as an additional subgoal. This is often
   useful when a plain [rewrite] acts on the wrong part of the goal.

   Use the [replace] tactic to do a proof of [plus_swap'], just like
   [plus_swap] but without needing [assert (n + m = m + n)]. *)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  replace (m + p) with (p + m).
  rewrite -> plus_assoc.
  rewrite -> plus_comm.
  reflexivity.
  rewrite -> plus_comm.
  reflexivity.
Qed.
  
(** [] *)

(** **** Exercise: 3 stars, recommended (binary_commute)  *)
(** Recall the [incr] and [bin_to_nat] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that the following diagram commutes:

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    That is, incrementing a binary number and then converting it to
    a (unary) natural number yields the same result as first converting
    it to a natural number and then incrementing.
    Name your theorem [bin_to_nat_pres_incr] ("pres" for "preserves").

    Before you start working on this exercise, copy the definitions
    from your solution to the [binary] exercise here so that this file
    can be graded on its own.  If you want to change your original
    definitions to make the property easier to prove, feel free to
    do so! *)

Theorem bin_to_nat_pres_incr:
  forall bn : bin, bin_to_nat(incr bn) = S (bin_to_nat bn).
Proof.
  induction bn as [|bn' IHbn'|bn'' IHbn''].  
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> IHbn''. simpl. 
    rewrite -> plus_n_Sm.
    rewrite -> plus_n_Sm.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.


(** [] *)

(** **** Exercise: 5 stars, advanced (binary_inverse)  *)
(** This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    there to complete this one; please copy them to this file to make
    it self contained for grading.

    (a) First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.

    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, this is not true!
        Explain what the problem is.

    (c) Define a "direct" normalization function -- i.e., a function
        [normalize] from binary numbers to binary numbers such that,
        for any binary number b, converting to a natural and then back
        to binary yields [(normalize b)].  Prove it.  (Warning: This
        part is tricky!)

    Again, feel free to change your earlier definitions if this helps
    here. *)
    
    
Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat:
  forall n : nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> bin_to_nat_pres_incr. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint normalize (b : bin) : bin :=
  match b with
  | Z => Z
  | D b' => 
      match (normalize b') with
      | Z => Z
      | D b'' => D (D b'')
      | C b'' => D (C b'')
      end
  | C b' => C (normalize b')
  end.
  
Lemma NN_to_bin: forall n:nat, nat_to_bin (n + n) = match (nat_to_bin n) with
                                                    | Z => Z 
                                                    | D b => D (D b) 
                                                    | C b => D (C b) 
                                                    end.
Proof.
  induction n. 
  - reflexivity. 
  - simpl. rewrite <- plus_n_Sm. simpl. rewrite -> IHn. 
    destruct (nat_to_bin n).
    + reflexivity. + reflexivity. + reflexivity.
Qed.
Lemma bin_inverse_Z: forall b:bin, nat_to_bin (bin_to_nat b) = Z -> 
                            nat_to_bin (bin_to_nat b + bin_to_nat b) = Z.
Proof.
  intros b. destruct (bin_to_nat b).
  - reflexivity. 
  - simpl. destruct (nat_to_bin n).
    * simpl. intros H. inversion H.
    * simpl. intros H. inversion H.
    * simpl. intros H. inversion H.
Qed.

Theorem binary_inverse:
  forall b : bin, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  induction b.
  - reflexivity.
  - simpl. destruct (normalize b).
    + apply bin_inverse_Z. apply IHb. 
    + rewrite -> NN_to_bin. rewrite -> IHb. reflexivity.
    + rewrite -> NN_to_bin. rewrite -> IHb. reflexivity. 
  - simpl. destruct (normalize b).
    + replace (nat_to_bin (bin_to_nat b + bin_to_nat b)) with Z.
      reflexivity. symmetry. apply bin_inverse_Z. apply IHb. 
    + rewrite -> NN_to_bin. rewrite -> IHb. reflexivity. 
    + rewrite -> NN_to_bin. rewrite -> IHb. reflexivity. 
Qed.
    

(** [] *)


(** $Date: 2017-11-15 22:55:41 -0500 (Wed, 15 Nov 2017) $ *)


(** * Lists: Working with Structured Data *)

Module NatList.

(* ################################################################# *)
(** * Pairs of Numbers *)

(** In an [Inductive] type definition, each constructor can take
    any number of arguments -- none (as with [true] and [O]), one (as
    with [S]), or more than one, as here: *)

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

(** This declaration can be read: "There is just one way to
    construct a pair of numbers: by applying the constructor [pair] to
    two arguments of type [nat]." *)

Check (pair 3 5).

(** Here are two simple functions for extracting the first and
    second components of a pair.  The definitions also illustrate how
    to do pattern matching on two-argument constructors. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(** Since pairs are used quite a bit, it is nice to be able to
    write them with the standard mathematical notation [(x,y)] instead
    of [pair x y].  We can tell Coq to allow this with a [Notation]
    declaration. *)

Notation "( x , y )" := (pair x y).

(** The new pair notation can be used both in expressions and in
    pattern matches (indeed, we've actually seen this already in the
    [Basics] chapter, in the definition of the [minus] function --
    this works because the pair notation is also provided as part of
    the standard library): *)

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** Let's try to prove a few simple facts about pairs.

    If we state things in a particular (and slightly peculiar) way, we
    can complete proofs with just reflexivity (and its built-in
    simplification): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(** But [reflexivity] is not enough if we state the lemma in a more
    natural way: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

(** We have to expose the structure of [p] so that [simpl] can
    perform the pattern match in [fst] and [snd].  We can do this with
    [destruct]. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

(** Notice that, unlike its behavior with [nat]s, [destruct]
    generates just one subgoal here.  That's because [natprod]s can
    only be constructed in one way. *)

(** **** Exercise: 1 star (snd_fst_is_swap)  *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, optional (fst_swap_is_snd)  *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p. reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Lists of Numbers *)

(** Generalizing the definition of pairs, we can describe the
    type of _lists_ of numbers like this: "A list is either the empty
    list or else a pair of a number and another list." *)

Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

(** For example, here is a three-element list: *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** As with pairs, it is more convenient to write lists in
    familiar programming notation.  The following declarations
    allow us to use [::] as an infix [cons] operator and square
    brackets as an "outfix" notation for constructing lists. *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** It is not necessary to understand the details of these
    declarations, but in case you are interested, here is roughly
    what's going on.  The [right associativity] annotation tells Coq
    how to parenthesize expressions involving several uses of [::] so
    that, for example, the next three declarations mean exactly the
    same thing: *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** The [at level 60] part tells Coq how to parenthesize
    expressions that involve both [::] and some other infix operator.
    For example, since we defined [+] as infix notation for the [plus]
    function at level 50,

  Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

   the [+] operator will bind tighter than [::], so [1 + 2 :: [3]]
   will be parsed, as we'd expect, as [(1 + 2) :: [3]] rather than [1
   + (2 :: [3])].

   (Expressions like "[1 + 2 :: [3]]" can be a little confusing when
   you read them in a .v file.  The inner brackets, around 3, indicate
   a list, but the outer brackets, which are invisible in the HTML
   rendering, are there to instruct the "coqdoc" tool that the bracketed
   part should be displayed as Coq code rather than running text.)

   The second and third [Notation] declarations above introduce the
   standard square-bracket notation for lists; the right-hand side of
   the third one illustrates Coq's syntax for declaring n-ary
   notations and translating them to nested sequences of binary
   constructors. *)

(* ----------------------------------------------------------------- *)
(** *** Repeat *)

(** A number of functions are useful for manipulating lists.
    For example, the [repeat] function takes a number [n] and a
    [count] and returns a list of length [count] where every element
    is [n]. *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(* ----------------------------------------------------------------- *)
(** *** Length *)

(** The [length] function calculates the length of a list. *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* ----------------------------------------------------------------- *)
(** *** Append *)

(** The [app] function concatenates (appends) two lists. *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** Actually, [app] will be used a lot in some parts of what
    follows, so it is convenient to have an infix operator for it. *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Head (with default) and Tail *)

(** Here are two smaller examples of programming with lists.
    The [hd] function returns the first element (the "head") of the
    list, while [tl] returns everything but the first
    element (the "tail").
    Of course, the empty list has no first element, so we
    must pass a default value to be returned in that case.  *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.


(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 2 stars, recommended (list_funs)  *)
(** Complete the definitions of [nonzeros], [oddmembers] and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => 
      match h with
      | O => nonzeros t
      | S _ => h :: (nonzeros t)
      end
  end.
  

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.
(* GRADE_THEOREM 0.5: NatList.test_nonzeros *)

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => 
      match (evenb h) with
      | true => oddmembers t
      | false => h :: (oddmembers t)
      end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.
(* GRADE_THEOREM 0.5: NatList.test_oddmembers *)

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (alternate)  *)
(** Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.

    Note: one natural and elegant way of writing [alternate] will fail
    to satisfy Coq's requirement that all [Fixpoint] definitions be
    "obviously terminating."  If you find yourself in this rut, look
    for a slightly more verbose solution that considers elements of
    both lists at the same time.  (One possible solution requires
    defining a new kind of pairs, but this is not the only way.)  *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], [] => []
  | h::t, [] => l1
  | [], h::t => l2
  | h1::t1, h2::t2 => h1::h2::(alternate t1 t2)
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Bags via Lists *)

(** A [bag] (or [multiset]) is like a set, except that each element
    can appear multiple times rather than just once.  One possible
    implementation is to represent a bag of numbers as a list. *)

Definition bag := natlist.

(** **** Exercise: 3 stars, recommended (bag_functions)  *)
(** Complete the following definitions for the functions
    [count], [sum], [add], and [member] for bags. *)

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | [] => O
  | h::t => 
      match (beq_nat h v) with
      | true => S (count v t)
      | false => count v t
      end
  end.

(** All these proofs can be done just by [reflexivity]. *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.
(* GRADE_THEOREM 0.5: NatList.test_count2 *)

(** Multiset [sum] is similar to set [union]: [sum a b] contains all
    the elements of [a] and of [b].  (Mathematicians usually define
    [union] on multisets a little bit differently -- using max instead
    of sum -- which is why we don't use that name for this operation.)
    For [sum] we're giving you a header that does not give explicit
    names to the arguments.  Moreover, it uses the keyword
    [Definition] instead of [Fixpoint], so even if you had names for
    the arguments, you wouldn't be able to process them recursively.
    The point of stating the question this way is to encourage you to
    think about whether [sum] can be implemented in another way --
    perhaps by using functions that have already been defined.  *)

Definition sum : bag -> bag -> bag := app.
  

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.
(* GRADE_THEOREM 0.5: NatList.test_sum1 *)

Definition add (v:nat) (s:bag) : bag := (cons v s).

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.
(* GRADE_THEOREM 0.5: NatList.test_add1 *)
(* GRADE_THEOREM 0.5: NatList.test_add2 *)

Definition member (v:nat) (s:bag) : bool := negb (beq_nat (count v s) 0).

Example test_member1:             member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
(* GRADE_THEOREM 0.5: NatList.test_member1 *)
(* GRADE_THEOREM 0.5: NatList.test_member2 *)

Example test_member2:             member 2 [1;4;1] = false.
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (bag_more_functions)  *)
(** Here are some more bag functions for you to practice with. *)

(** When remove_one is applied to a bag without the number to remove,
   it should return the same bag unchanged. *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | [] => []
  | h::t =>
      match (beq_nat v h) with
      | true => t
      | false => h::(remove_one v t)
      end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | [] => []
  | h::t =>
      match (beq_nat v h) with
      | true => (remove_all v t)
      | false => h::(remove_all v t)
      end
  end.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | [] => true
  | h::t =>
      match (count h s2) with
      | O => false
      | S _ => subset t (remove_one h s2)
      end
  end.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars, recommended (bag_theorem)  *)
(** Write down an interesting theorem [bag_theorem] about bags
    involving the functions [count] and [add], and prove it.  Note
    that, since this problem is somewhat open-ended, it's possible
    that you may come up with a theorem which is true, but whose proof
    requires techniques you haven't learned yet.  Feel free to ask for
    help if you get stuck! *)

(*
Theorem bag_theorem : ...
Proof.
  ...
Qed.
*)

(** [] *)

(* ################################################################# *)
(** * Reasoning About Lists *)

(** As with numbers, simple facts about list-processing
    functions can sometimes be proved entirely by simplification.  For
    example, the simplification performed by [reflexivity] is enough
    for this theorem... *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** ... because the [[]] is substituted into the
    "scrutinee" (the expression whose value is being "scrutinized" by
    the match) in the definition of [app], allowing the match itself
    to be simplified. *)

(** Also, as with numbers, it is sometimes helpful to perform case
    analysis on the possible shapes (empty or non-empty) of an unknown
    list. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.

(** Here, the [nil] case works because we've chosen to define
    [tl nil = nil]. Notice that the [as] annotation on the [destruct]
    tactic here introduces two names, [n] and [l'], corresponding to
    the fact that the [cons] constructor for lists takes two
    arguments (the head and tail of the list it is constructing). *)

(** Usually, though, interesting theorems about lists require
    induction for their proofs. *)

(* ----------------------------------------------------------------- *)
(** *** Micro-Sermon *)

(** Simply reading example proof scripts will not get you very far!
    It is important to work through the details of each one, using Coq
    and thinking about what each step achieves.  Otherwise it is more
    or less guaranteed that the exercises will make no sense when you
    get to them.  'Nuff said. *)

(* ================================================================= *)
(** ** Induction on Lists *)

(** Proofs by induction over datatypes like [natlist] are a
    little less familiar than standard natural number induction, but
    the idea is equally simple.  Each [Inductive] declaration defines
    a set of data values that can be built up using the declared
    constructors: a boolean can be either [true] or [false]; a number
    can be either [O] or [S] applied to another number; a list can be
    either [nil] or [cons] applied to a number and a list.

    Moreover, applications of the declared constructors to one another
    are the _only_ possible shapes that elements of an inductively
    defined set can have, and this fact directly gives rise to a way
    of reasoning about inductively defined sets: a number is either
    [O] or else it is [S] applied to some _smaller_ number; a list is
    either [nil] or else it is [cons] applied to some number and some
    _smaller_ list; etc. So, if we have in mind some proposition [P]
    that mentions a list [l] and we want to argue that [P] holds for
    _all_ lists, we can reason as follows:

      - First, show that [P] is true of [l] when [l] is [nil].

      - Then show that [P] is true of [l] when [l] is [cons n l'] for
        some number [n] and some smaller list [l'], assuming that [P]
        is true for [l'].

    Since larger lists can only be built up from smaller ones,
    eventually reaching [nil], these two arguments together establish
    the truth of [P] for all lists [l].  Here's a concrete example: *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Notice that, as when doing induction on natural numbers, the
    [as...] clause provided to the [induction] tactic gives a name to
    the induction hypothesis corresponding to the smaller list [l1']
    in the [cons] case. Once again, this Coq proof is not especially
    illuminating as a static written document -- it is easy to see
    what's going on if you are reading the proof in an interactive Coq
    session and you can see the current goal and context at each
    point, but this state is not visible in the written-down parts of
    the Coq proof.  So a natural-language proof -- one written for
    human readers -- will need to include more explicit signposts; in
    particular, it will help the reader stay oriented if we remind
    them exactly what the induction hypothesis is in the second
    case. *)

(** For comparison, here is an informal proof of the same theorem. *)

(** _Theorem_: For all lists [l1], [l2], and [l3],
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Proof_: By induction on [l1].

   - First, suppose [l1 = []].  We must show

       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

     which follows directly from the definition of [++].

   - Next, suppose [l1 = n::l1'], with

       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)

     (the induction hypothesis). We must show

       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

     By the definition of [++], this follows from

       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

     which is immediate from the induction hypothesis.  [] *)

(* ----------------------------------------------------------------- *)
(** *** Reversing a List *)

(** For a slightly more involved example of inductive proof over
    lists, suppose we use [app] to define a list-reversing function
    [rev]: *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [rev] *)

(** Now let's prove some theorems about our newly defined [rev].
    For something a bit more challenging than what we've seen, let's
    prove that reversing a list does not change its length.  Our first
    attempt gets stuck in the successor case... *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving [++], but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

(** So let's take the equation relating [++] and [length] that
    would have enabled us to make progress and prove it as a separate
    lemma. *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Note that, to make the lemma as general as possible, we
    quantify over _all_ [natlist]s, not just those that result from an
    application of [rev].  This should seem natural, because the truth
    of the goal clearly doesn't depend on the list having been
    reversed.  Moreover, it is easier to prove the more general
    property. *)

(** Now we can complete the original proof. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'. reflexivity.  Qed.

(** For comparison, here are informal proofs of these two theorems:

    _Theorem_: For all lists [l1] and [l2],
       [length (l1 ++ l2) = length l1 + length l2].

    _Proof_: By induction on [l1].

    - First, suppose [l1 = []].  We must show

        length ([] ++ l2) = length [] + length l2,

      which follows directly from the definitions of
      [length] and [++].

    - Next, suppose [l1 = n::l1'], with

        length (l1' ++ l2) = length l1' + length l2.

      We must show

        length ((n::l1') ++ l2) = length (n::l1') + length l2).

      This follows directly from the definitions of [length] and [++]
      together with the induction hypothesis. [] *)

(** _Theorem_: For all lists [l], [length (rev l) = length l].

    _Proof_: By induction on [l].

      - First, suppose [l = []].  We must show

          length (rev []) = length [],

        which follows directly from the definitions of [length]
        and [rev].

      - Next, suppose [l = n::l'], with

          length (rev l') = length l'.

        We must show

          length (rev (n :: l')) = length (n :: l').

        By the definition of [rev], this follows from

          length ((rev l') ++ [n]) = S (length l')

        which, by the previous lemma, is the same as

          length (rev l') + length [n] = S (length l').

        This follows directly from the induction hypothesis and the
        definition of [length]. [] *)

(** The style of these proofs is rather longwinded and pedantic.
    After the first few, we might find it easier to follow proofs that
    give fewer details (which can easily work out in our own minds or
    on scratch paper if necessary) and just highlight the non-obvious
    steps.  In this more compressed style, the above proof might look
    like this: *)

(** _Theorem_:
     For all lists [l], [length (rev l) = length l].

    _Proof_: First, observe that [length (l ++ [n]) = S (length l)]
     for any [l] (this follows by a straightforward induction on [l]).
     The main property again follows by induction on [l], using the
     observation together with the induction hypothesis in the case
     where [l = n'::l']. [] *)

(** Which style is preferable in a given situation depends on
    the sophistication of the expected audience and how similar the
    proof at hand is to ones that the audience will already be
    familiar with.  The more pedantic style is a good default for our
    present purposes. *)



(* ================================================================= *)
(** ** [Search] *)

(** We've seen that proofs can make use of other theorems we've
    already proved, e.g., using [rewrite].  But in order to refer to a
    theorem, we need to know its name!  Indeed, it is often hard even
    to remember what theorems have been proven, much less what they
    are called.

    Coq's [Search] command is quite helpful with this.  Typing
    [Search foo] will cause Coq to display a list of all theorems
    involving [foo].  For example, try uncommenting the following line
    to see a list of theorems that we have proved about [rev]: *)

(*  Search rev. *)

(** Keep [Search] in mind as you do the following exercises and
    throughout the rest of the book; it can save you a lot of time!

    If you are using ProofGeneral, you can run [Search] with [C-c
    C-a C-a]. Pasting its response into your buffer can be
    accomplished with [C-c C-;]. *)

(* ================================================================= *)
(** ** List Exercises, Part 1 *)

(** **** Exercise: 3 stars (list_exercises)  *)
(** More practice with lists: *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| h t].
  - reflexivity.
  - simpl. rewrite -> IHt. reflexivity.
Qed.
(* GRADE_THEOREM 0.5: NatList.app_nil_r *)

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| h t IHl].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl. rewrite -> app_assoc. reflexivity.
Qed.
(* GRADE_THEOREM 0.5: NatList.rev_app_distr *)

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  induction l as [|h t IHl].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl. reflexivity.
Qed.
(* GRADE_THEOREM 0.5: NatList.rev_involutive *)

(** There is a short solution to the next one.  If you find yourself
    getting tangled up, step back and try to look for a simpler
    way. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros a b c d.
  rewrite -> app_assoc. 
  rewrite -> app_assoc. 
  reflexivity.
Qed.
(* GRADE_THEOREM 0.5: NatList.app_assoc4 *)

(** An exercise about your implementation of [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| h t IHl].
  - reflexivity.
  - destruct h.
    + simpl. rewrite -> IHl. reflexivity.
    + simpl. rewrite -> IHl. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars (beq_natlist)  *)
(** Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ => false
  | _, [] => false
  | h1::t1, h2::t2 => andb (beq_nat h1 h2) (beq_natlist t1 t2)
  end.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros l. induction l.
  - reflexivity.
  - simpl. rewrite <- IHl. replace (beq_nat n n) with true. reflexivity.
    induction n. + reflexivity. + simpl. rewrite <- IHn. reflexivity.
Qed.
(** [] *)

(* ================================================================= *)
(** ** List Exercises, Part 2 *)

(** Here are a couple of little theorems to prove about your
    definitions about bags above. *)

(** **** Exercise: 1 star (count_member_nonzero)  *)
Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  intros s. simpl. reflexivity.
Qed.
(** [] *)

(** The following lemma about [leb] might help you in the next exercise. *)

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

(** **** Exercise: 3 stars, advanced (remove_decreases_count)  *)
Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s. induction s.
  - reflexivity. 
  - destruct n.
    + simpl. rewrite -> ble_n_Sn. reflexivity.
    + simpl. rewrite -> IHs. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (bag_count_sum)  *)
(** Write down an interesting theorem [bag_count_sum] about bags
    involving the functions [count] and [sum], and prove it using
    Coq.  (You may find that the difficulty of the proof depends on
    how you defined [count]!) *)
(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced (rev_injective)  *)
(** Prove that the [rev] function is injective -- that is,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

(There is a hard way and an easy way to do this.) *)

Theorem rev_injective:
  forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2.
  rewrite <- rev_involutive with (l:=l1).
  rewrite <- rev_involutive with (l:=l2).
  remember (rev l1) as a.
  remember (rev l2) as b.
  rewrite -> rev_involutive with (l:=a).
  rewrite -> rev_involutive with (l:=b).
  intros H.
  rewrite -> H.
  reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Options *)

(** Suppose we want to write a function that returns the [n]th
    element of some list.  If we give it type [nat -> natlist -> nat],
    then we'll have to choose some number to return when the list is
    too short... *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

(** This solution is not so good: If [nth_bad] returns [42], we
    can't tell whether that value actually appears on the input
    without further processing. A better alternative is to change the
    return type of [nth_bad] to include an error value as a possible
    outcome. We call this type [natoption]. *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(** We can then change the above definition of [nth_bad] to
    return [None] when the list is too short and [Some a] when the
    list has enough members and [a] appears at position [n]. We call
    this new function [nth_error] to indicate that it may result in an
    error. *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(** (In the HTML version, the boilerplate proofs of these
    examples are elided.  Click on a box if you want to see one.)

    This example is also an opportunity to introduce one more small
    feature of Coq's programming language: conditional
    expressions... *)


Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.

(** Coq's conditionals are exactly like those found in any other
    language, with one small generalization.  Since the boolean type
    is not built in, Coq actually supports conditional expressions over
    _any_ inductively defined type with exactly two constructors.  The
    guard is considered true if it evaluates to the first constructor
    in the [Inductive] definition and false if it evaluates to the
    second. *)

(** The function below pulls the [nat] out of a [natoption], returning
    a supplied default in the [None] case. *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** Exercise: 2 stars (hd_error)  *)
(** Using the same idea, fix the [hd] function from earlier so we don't
    have to pass a default element for the [nil] case.  *)

Definition hd_error (l : natlist) : natoption :=
  match l with
  | [] => None
  | h::t => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star, optional (option_elim_hd)  *)
(** This exercise relates your new [hd_error] to the old [hd]. *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default.
  destruct l.
  - reflexivity.
  - reflexivity.
Qed.        
(** [] *)

End NatList.

(* ################################################################# *)
(** * Partial Maps *)

(** As a final illustration of how data structures can be defined in
    Coq, here is a simple _partial map_ data type, analogous to the
    map or dictionary data structures found in most programming
    languages. *)

(** First, we define a new inductive datatype [id] to serve as the
    "keys" of our partial maps. *)

Inductive id : Type :=
  | Id : nat -> id.

(** Internally, an [id] is just a number.  Introducing a separate type
    by wrapping each nat with the tag [Id] makes definitions more
    readable and gives us the flexibility to change representations
    later if we wish. *)

(** We'll also need an equality test for [id]s: *)

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

(** **** Exercise: 1 star (beq_id_refl)  *)
Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  intros x. destruct x. simpl. replace (beq_nat n n) with true. reflexivity.
  induction n. - reflexivity. - simpl. rewrite <- IHn. reflexivity.
Qed.
(** [] *)

(** Now we define the type of partial maps: *)

Module PartialMap.
Export NatList.
  
Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.

(** This declaration can be read: "There are two ways to construct a
    [partial_map]: either using the constructor [empty] to represent an
    empty partial map, or by applying the constructor [record] to
    a key, a value, and an existing [partial_map] to construct a
    [partial_map] with an additional key-to-value mapping." *)

(** The [update] function overrides the entry for a given key in a
    partial map (or adds a new entry if the given key is not already
    present). *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(** Last, the [find] function searches a [partial_map] for a given
    key.  It returns [None] if the key was not found and [Some val] if
    the key was associated with [val]. If the same key is mapped to
    multiple values, [find] will return the first one it
    encounters. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.


(** **** Exercise: 1 star (update_eq)  *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl. replace (beq_id x x) with true. reflexivity.
  destruct x. simpl.   
  induction n. - reflexivity. - simpl. rewrite <- IHn. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star (update_neq)  *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o H.
  simpl. rewrite -> H. reflexivity.
Qed.
(** [] *)
End PartialMap.

(** **** Exercise: 2 stars (baz_num_elts)  *)
(** Consider the following inductive definition: *)

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

(** How _many_ elements does the type [baz] have?
    (Explain your answer in words, preferrably English.)

(* FILL IN HERE *)
*)
(** [] *)

(** $Date: 2017-11-16 01:44:48 -0500 (Thu, 16 Nov 2017) $ *)


(** * Poly: Polymorphism and Higher-Order Functions *)

(* Final reminder: Please do not put solutions to the exercises in
   publicly accessible places.  Thank you!! *)

(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".

(*** Polymorphism *)

(** In this chapter we continue our development of basic
    concepts of functional programming.  The critical new ideas are
    _polymorphism_ (abstracting functions over the types of the data
    they manipulate) and _higher-order functions_ (treating functions
    as data).  We begin with polymorphism. *)

(* ================================================================= *)
(** ** Polymorphic Lists *)

(** For the last couple of chapters, we've been working just
    with lists of numbers.  Obviously, interesting programs also need
    to be able to manipulate lists with elements from other types --
    lists of strings, lists of booleans, lists of lists, etc.  We
    _could_ just define a new inductive datatype for each of these,
    for example... *)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(** ... but this would quickly become tedious, partly because we
    have to make up different constructor names for each datatype, but
    mostly because we would also need to define new versions of all
    our list manipulating functions ([length], [rev], etc.) for each
    new datatype definition. *)

(** To avoid all this repetition, Coq supports _polymorphic_
    inductive type definitions.  For example, here is a _polymorphic
    list_ datatype. *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

(** This is exactly like the definition of [natlist] from the
    previous chapter, except that the [nat] argument to the [cons]
    constructor has been replaced by an arbitrary type [X], a binding
    for [X] has been added to the header, and the occurrences of
    [natlist] in the types of the constructors have been replaced by
    [list X].  (We can re-use the constructor names [nil] and [cons]
    because the earlier definition of [natlist] was inside of a
    [Module] definition that is now out of scope.)

    What sort of thing is [list] itself?  One good way to think
    about it is that [list] is a _function_ from [Type]s to
    [Inductive] definitions; or, to put it another way, [list] is a
    function from [Type]s to [Type]s.  For any particular type [X],
    the type [list X] is an [Inductive]ly defined set of lists whose
    elements are of type [X]. *)

Check list.
(* ===> list : Type -> Type *)

(** The parameter [X] in the definition of [list] becomes a parameter
    to the constructors [nil] and [cons] -- that is, [nil] and [cons]
    are now polymorphic constructors, that need to be supplied with
    the type of the list they are building. As an example, [nil nat]
    constructs the empty list of type [nat]. *)

Check (nil nat).
(* ===> nil nat : list nat *)

(** Similarly, [cons nat] adds an element of type [nat] to a list of
    type [list nat]. Here is an example of forming a list containing
    just the natural number 3.*)

Check (cons nat 3 (nil nat)).
(* ===> cons nat 3 (nil nat) : list nat *)

(** What might the type of [nil] be? We can read off the type [list X]
    from the definition, but this omits the binding for [X] which is
    the parameter to [list]. [Type -> list X] does not explain the
    meaning of [X]. [(X : Type) -> list X] comes closer. Coq's
    notation for this situation is [forall X : Type, list X]. *)

Check nil.
(* ===> nil : forall X : Type, list X *)

(** Similarly, the type of [cons] from the definition looks like
    [X -> list X -> list X], but using this convention to explain the
    meaning of [X] results in the type [forall X, X -> list X -> list
    X]. *)

Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(** (Side note on notation: In .v files, the "forall" quantifier
    is spelled out in letters.  In the generated HTML files and in the
    way various IDEs show .v files (with certain settings of their
    display controls), [forall] is usually typeset as the usual
    mathematical "upside down A," but you'll still see the spelled-out
    "forall" in a few places.  This is just a quirk of typesetting:
    there is no difference in meaning.) *)

(** Having to supply a type argument for each use of a list
    constructor may seem an awkward burden, but we will soon see
    ways of reducing that burden. *) 

Check (cons nat 2 (cons nat 1 (nil nat))).

(** (We've written [nil] and [cons] explicitly here because we haven't
    yet defined the [ [] ] and [::] notations for the new version of
    lists.  We'll do that in a bit.) *)

(** We can now go back and make polymorphic versions of all the
    list-processing functions that we wrote before.  Here is [repeat],
    for example: *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

(** As with [nil] and [cons], we can use [repeat] by applying it
    first to a type and then to an element of this type (and a number): *)

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.

(** To use [repeat] to build other kinds of lists, we simply
    instantiate it with an appropriate type parameter: *)

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity.  Qed.


Module MumbleGrumble.

(** **** Exercise: 2 stars (mumble_grumble)  *)
(** Consider the following two inductively defined types. *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?
      X [d (b a 5)]
      ! [d mumble (b a 5)]
      ! [d bool (b a 5)]
      ! [e bool true]
      ! [e mumble (b c 0)]
      X [e bool (b c 0)]
      X [c]
*)

Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
Check c.


(** [] *)

End MumbleGrumble.

(* ----------------------------------------------------------------- *)
(** *** Type Annotation Inference *)

(** Let's write the definition of [repeat] again, but this time we
    won't specify the types of any of the arguments.  Will Coq still
    accept it? *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** Indeed it will.  Let's see what type Coq has assigned to [repeat']: *)

Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)

(** It has exactly the same type type as [repeat].  Coq was able
    to use _type inference_ to deduce what the types of [X], [x], and
    [count] must be, based on how they are used.  For example, since
    [X] is used as an argument to [cons], it must be a [Type], since
    [cons] expects a [Type] as its first argument; matching [count]
    with [0] and [S] means it must be a [nat]; and so on.

    This powerful facility means we don't always have to write
    explicit type annotations everywhere, although explicit type
    annotations are still quite useful as documentation and sanity
    checks, so we will continue to use them most of the time.  You
    should try to find a balance in your own code between too many
    type annotations (which can clutter and distract) and too
    few (which forces readers to perform type inference in their heads
    in order to understand your code). *)

(* ----------------------------------------------------------------- *)
(** *** Type Argument Synthesis *)

(** To use a polymorphic function, we need to pass it one or
    more types in addition to its other arguments.  For example, the
    recursive call in the body of the [repeat] function above must
    pass along the type [X].  But since the second argument to
    [repeat] is an element of [X], it seems entirely obvious that the
    first argument can only be [X] -- why should we have to write it
    explicitly?

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write the "implicit argument"
    [_], which can be read as "Please try to figure out for yourself
    what belongs here."  More precisely, when Coq encounters a [_], it
    will attempt to _unify_ all locally available information -- the
    type of the function being applied, the types of the other
    arguments, and the type expected by the context in which the
    application appears -- to determine what concrete type should
    replace the [_].

    This may sound similar to type annotation inference -- indeed, the
    two procedures rely on the same underlying mechanisms.  Instead of
    simply omitting the types of some arguments to a function, like

      repeat' X x count : list X :=

    we can also replace the types with [_]

      repeat' (X : _) (x : _) (count : _) : list X :=

    to tell Coq to attempt to infer the missing information.

    Using implicit arguments, the [repeat] function can be written like
    this: *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(** In this instance, we don't save much by writing [_] instead of
    [X].  But in many cases the difference in both keystrokes and
    readability is nontrivial.  For example, suppose we want to write
    down a list containing the numbers [1], [2], and [3].  Instead of
    writing this... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...we can use argument synthesis to write this: *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ----------------------------------------------------------------- *)
(** *** Implicit Arguments *)

(** We can go further and even avoid writing [_]'s in most cases by
    telling Coq _always_ to infer the type argument(s) of a given
    function.

    The [Arguments] directive specifies the name of the function (or
    constructor) and then lists its argument names, with curly braces
    around any arguments to be treated as implicit.  (If some
    arguments of a definition don't have a name, as is often the case
    for constructors, they can be marked with a wildcard pattern
    [_].) *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

(** Now, we don't have to supply type arguments at all: *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(** Alternatively, we can declare an argument to be implicit
    when defining the function itself, by surrounding it in curly
    braces instead of parens.  For example: *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(** (Note that we didn't even have to provide a type argument to the
    recursive call to [repeat''']; indeed, it would be invalid to
    provide one!)

    We will use the latter style whenever possible, but we will
    continue to use explicit [Argument] declarations for [Inductive]
    constructors.  The reason for this is that marking the parameter
    of an inductive type as implicit causes it to become implicit for
    the type itself, not just for its constructors.  For instance,
    consider the following alternative definition of the [list]
    type: *)

Inductive list' {X:Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.

(** Because [X] is declared as implicit for the _entire_ inductive
    definition including [list'] itself, we now have to write just
    [list'] whether we are talking about lists of numbers or booleans
    or anything else, rather than [list' nat] or [list' bool] or
    whatever; this is a step too far. *)

(** Let's finish by re-implementing a few other standard list
    functions on our new polymorphic lists... *)

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity.  Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Supplying Type Arguments Explicitly *)

(** One small problem with declaring arguments [Implicit] is
    that, occasionally, Coq does not have enough local information to
    determine a type argument; in such cases, we need to tell Coq that
    we want to give the argument explicitly just this time.  For
    example, suppose we write this: *)

Fail Definition mynil := nil.

(** (The [Fail] qualifier that appears before [Definition] can be
    used with _any_ command, and is used to ensure that that command
    indeed fails when executed. If the command does fail, Coq prints
    the corresponding error message, but continues processing the rest
    of the file.)

    Here, Coq gives us an error because it doesn't know what type
    argument to supply to [nil].  We can help it by providing an
    explicit type declaration (so that Coq has more information
    available when it gets to the "application" of [nil]): *)

Definition mynil : list nat := nil.

(** Alternatively, we can force the implicit arguments to be explicit by
   prefixing the function name with [@]. *)

Check @nil.

Definition mynil' := @nil nat.

(** Using argument synthesis and implicit arguments, we can
    define convenient notation for lists, as before.  Since we have
    made the constructor type arguments implicit, Coq will know to
    automatically infer these when we use the notations. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** Now lists can be written just the way we'd hope: *)

Definition list123''' := [1; 2; 3].

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 2 stars, optional (poly_exercises)  *)
(** Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Complete the proofs below. *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l. 
  induction l. 
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity. 
Qed.


Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l.
  - reflexivity. 
  - simpl. rewrite -> IHl. reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1. 
  - reflexivity.
  - simpl. rewrite -> IHl1. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (more_poly_exercises)  *)
(** Here are some slightly more interesting ones... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1.
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1. rewrite <- app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l.
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl. reflexivity.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Polymorphic Pairs *)

(** Following the same pattern, the type definition we gave in
    the last chapter for pairs of numbers can be generalized to
    _polymorphic pairs_, often called _products_: *)

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

(** As with lists, we make the type arguments implicit and define the
    familiar concrete notation. *)

Notation "( x , y )" := (pair x y).

(** We can also use the [Notation] mechanism to define the standard
    notation for product _types_: *)

Notation "X * Y" := (prod X Y) : type_scope.

(** (The annotation [: type_scope] tells Coq that this abbreviation
    should only be used when parsing types.  This avoids a clash with
    the multiplication symbol.) *)

(** It is easy at first to get [(x,y)] and [X*Y] confused.
    Remember that [(x,y)] is a _value_ built from two other values,
    while [X*Y] is a _type_ built from two other types.  If [x] has
    type [X] and [y] has type [Y], then [(x,y)] has type [X*Y]. *)

(** The first and second projection functions now look pretty
    much as they would in any functional programming language. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(** The following function takes two lists and combines them
    into a list of pairs.  In other functional languages, it is often
    called [zip]; we call it [combine] for consistency with Coq's
    standard library. *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(** **** Exercise: 1 star, optional (combine_checks)  *)
(** Try answering the following questions on paper and
    checking your answers in coq:
    - What is the type of [combine] (i.e., what does [Check
      @combine] print?)
    - What does

        Compute (combine [1;2] [false;false;true;true]).

      print? *)
Check @combine.
Compute (combine [1;2] [false;false;true;true]).
(** [] *)

(** **** Exercise: 2 stars, recommended (split)  *)
(** The function [split] is the right inverse of [combine]: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called [unzip].

    Fill in the definition of [split] below.  Make sure it passes the
    given unit test. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] =>  ( [] , [] )
  | (x,y)::t => ( x::(fst (split t)) , y::(snd (split t)) )
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** Polymorphic Options *)

(** One last polymorphic type for now: _polymorphic options_,
    which generalize [natoption] from the previous chapter: *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

(** We can now rewrite the [nth_error] function so that it works
    with any type of lists. *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(** **** Exercise: 1 star, optional (hd_error_poly)  *)
(** Complete the definition of a polymorphic version of the
    [hd_error] function from the last chapter. Be sure that it
    passes the unit tests below. *)

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | h::t => Some h
  end.

(** Once again, to force the implicit arguments to be explicit,
    we can use [@] before the name of the function. *)

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
Proof. reflexivity. Qed.
(** [] *)

(* ################################################################# *)
(** * Functions as Data *)

(** Like many other modern programming languages -- including
    all functional languages (ML, Haskell, Scheme, Scala, Clojure,
    etc.) -- Coq treats functions as first-class citizens, allowing
    them to be passed as arguments to other functions, returned as
    results, stored in data structures, etc.*)

(* ================================================================= *)
(** ** Higher-Order Functions *)

(** Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** The argument [f] here is itself a function (from [X] to
    [X]); the body of [doit3times] applies [f] three times to some
    value [n]. *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ================================================================= *)
(** ** Filter *)

(** Here is a more useful higher-order function, taking a list
    of [X]s and a _predicate_ on [X] (a function from [X] to [bool])
    and "filtering" the list, returning a new list containing just
    those elements for which the predicate returns [true]. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** For example, if we apply [filter] to the predicate [evenb]
    and a list of numbers [l], it returns a list containing just the
    even members of [l]. *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** We can use [filter] to give a concise version of the
    [countoddmembers] function from the [Lists] chapter. *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ================================================================= *)
(** ** Anonymous Functions *)

(** It is arguably a little sad, in the example just above, to
    be forced to define the function [length_is_1] and give it a name
    just to be able to pass it as an argument to [filter], since we
    will probably never use it again.  Moreover, this is not an
    isolated example: when using higher-order functions, we often want
    to pass as arguments "one-off" functions that we will never use
    again; having to give each of these functions a name would be
    tedious.

    Fortunately, there is a better way.  We can construct a function
    "on the fly" without declaring it at the top level or giving it a
    name. *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(** The expression [(fun n => n * n)] can be read as "the function
    that, given a number [n], yields [n * n]." *)

(** Here is the [filter] example, rewritten to use an anonymous
    function. *)

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** **** Exercise: 2 stars (filter_even_gt7)  *)
(** Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7. *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (leb 7 n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity.  Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity.  Qed.
(** [] *)

(** **** Exercise: 3 stars (partition)  *)
(** Use [filter] to write a Coq function [partition]:

      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X

   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list. *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X :=
  ( filter test l , filter (fun l => negb (test l)) l ).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity.  Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity.  Qed.
(** [] *)

(* ================================================================= *)
(** ** Map *)

(** Another handy higher-order function is called [map]. *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** It takes a function [f] and a list [ l = [n1, n2, n3, ...] ]
    and returns the list [ [f n1, f n2, f n3,...] ], where [f] has
    been applied to each element of [l] in turn.  For example: *)

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** The element types of the input and output lists need not be
    the same, since [map] takes _two_ type arguments, [X] and [Y]; it
    can thus be applied to a list of numbers and a function from
    numbers to booleans to yield a list of booleans: *)

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

(** It can even be applied to a list of numbers and
    a function from numbers to _lists_ of booleans to
    yield a _list of lists_ of booleans: *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 3 stars (map_rev)  *)
(** Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)
    
Lemma map_app_distr : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y F l1 l2.
  induction l1.
  - reflexivity.
  - simpl. rewrite -> IHl1. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l.
  - reflexivity.
  - simpl. rewrite -> map_app_distr. rewrite -> IHl. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, recommended (flat_map)  *)
(** The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:

        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X) 
                   : (list Y) :=
  match l with
  | [] => []
  | h::t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity.  Qed.
(** [] *)

(** Lists are not the only inductive type that we can write a
    [map] function for.  Here is the definition of [map] for the
    [option] type: *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(** **** Exercise: 2 stars, optional (implicit_args)  *)
(** The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  (This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.) 
*)
(** [] *)

(* ================================================================= *)
(** ** Fold *)

(** An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** Intuitively, the behavior of the [fold] operation is to
    insert a given binary operator [f] between every pair of elements
    in a given list.  For example, [ fold plus [1;2;3;4] ] intuitively
    means [1+2+3+4].  To make this precise, we also need a "starting
    element" that serves as the initial second input to [f].  So, for
    example,

       fold plus [1;2;3;4] 0

    yields

       1 + (2 + (3 + (4 + 0))).

    Some more examples: *)

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(** **** Exercise: 1 star, advanced (fold_types_different)  *)
(** Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different? *)

(* FILL IN HERE *)
(** [] *)

(* ================================================================= *)
(** ** Functions That Construct Functions *)

(** Most of the higher-order functions we have talked about so
    far take functions as arguments.  Let's look at some examples that
    involve _returning_ functions as the results of other functions.
    To begin, here is a function that takes a value [x] (drawn from
    some type [X]) and returns a function from [nat] to [X] that
    yields [x] whenever it is called, ignoring its [nat] argument. *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** In fact, the multiple-argument functions we have already
    seen are also examples of passing functions as data.  To see why,
    recall the type of [plus]. *)

Check plus.
(* ==> nat -> nat -> nat *)

(** Each [->] in this expression is actually a _binary_ operator
    on types.  This operator is _right-associative_, so the type of
    [plus] is really a shorthand for [nat -> (nat -> nat)] -- i.e., it
    can be read as saying that "[plus] is a one-argument function that
    takes a [nat] and returns a one-argument function that takes
    another [nat] and returns a [nat]."  In the examples above, we
    have always applied [plus] to both of its arguments at once, but
    if we like we can supply just the first.  This is called _partial
    application_. *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ################################################################# *)
(** * Additional Exercises *)

Module Exercises.

(** **** Exercise: 2 stars (fold_length)  *)
(** Many common functions on lists can be implemented in terms of
   [fold].  For example, here is an alternative definition of [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(** Prove the correctness of [fold_length]. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l. induction l.
  - reflexivity.
  - unfold fold_length. simpl. unfold fold_length in IHl.
    rewrite -> IHl. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars (fold_map)  *)
(** We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x ly => (f x)::ly) l [].
  

(** Write down a theorem [fold_map_correct] in Coq stating that
   [fold_map] is correct, and prove it. *)
Theorem fold_map_correct: forall X Y (f : X->Y ) (l : list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l.
  induction l.
  - reflexivity.
  - unfold fold_map. simpl. unfold fold_map in IHl. rewrite -> IHl. reflexivity.
Qed.

(** [] *)

(** **** Exercise: 2 stars, advanced (currying)  *)
(** In Coq, a function [f : A -> B -> C] really has the type [A
    -> (B -> C)].  That is, if you give [f] a value of type [A], it
    will give you function [f' : B -> C].  If you then give [f'] a
    value of type [B], it will return a value of type [C].  This
    allows for partial application, as in [plus3].  Processing a list
    of arguments with functions that return functions is called
    _currying_, in honor of the logician Haskell Curry.

    Conversely, we can reinterpret the type [A -> B -> C] as [(A *
    B) -> C].  This is called _uncurrying_.  With an uncurried binary
    function, both arguments must be given at once as a pair; there is
    no partial application. *)

(** We can define currying as follows: *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
    f (fst p) (snd p).

(** As a (trivial) example of the usefulness of currying, we can use it
    to shorten one of the examples that we saw above: *)

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(** Thought exercise: before running the following commands, can you
    calculate the types of [prod_curry] and [prod_uncurry]? *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  unfold prod_uncurry. unfold prod_curry. reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
    unfold prod_uncurry. unfold prod_curry. 
    unfold fst. unfold snd. destruct p. reflexivity.
Qed.

(** [] *)

(** **** Exercise: 2 stars, advanced (nth_error_informal)  *)
(** Recall the definition of the [nth_error] function:

   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
     end.

   Write an informal proof of the following theorem:

   forall X n l, length l = n -> @nth_error X l n = None

(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (church_numerals)  *)
(** This exercise explores an alternative way of defining natural
    numbers, using the so-called _Church numerals_, named after
    mathematician Alonzo Church.  We can represent a natural number
    [n] as a function that takes a function [f] as a parameter and
    returns [f] iterated [n] times. *)

Module Church.
Definition nat := forall X : Type, (X -> X) -> X -> X.

(** Let's see how to write some numbers with this notation. Iterating
    a function once should be the same as just applying it.  Thus: *)

Definition one : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** Similarly, [two] should apply [f] twice to its argument: *)

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** Defining [zero] is somewhat trickier: how can we "apply a function
    zero times"?  The answer is actually simple: just return the
    argument untouched. *)

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** More generally, a number [n] can be written as [fun X f x => f (f
    ... (f x) ...)], with [n] occurrences of [f].  Notice in
    particular how the [doit3times] function we've defined previously
    is actually just the Church representation of [3]. *)

Definition three : nat := @doit3times.

(** Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity]. *)

(** Successor of a natural number: *)

Definition succ (n : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.

Example succ_2 : succ one = two.
Proof. reflexivity. Qed.

Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

(** Addition of two natural numbers: *)

Definition plus (n m : nat) : nat :=
  fun (X : Type) (f : X->X) (x : X) => n X f (m X f x).
  

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(** Multiplication: *)

Definition mult (n m : nat) : nat :=
  fun (X : Type) (f : X->X) (x : X) => n X (m X f) x.

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

(** Exponentiation: *)

(** (_Hint_: Polymorphism plays a crucial role here.  However,
    choosing the right type to iterate over can be tricky.  If you hit
    a "Universe inconsistency" error, try iterating over a different
    type: [nat] itself is usually problematic.) *)


Definition exp (n m : nat) : nat :=
  fun X f x => (m (X->X) (n X) f) x.

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

Example exp_3 : exp three zero = one.
Proof. reflexivity. Qed.

End Church.
(** [] *)

End Exercises.

(** $Date: 2018-01-23 21:16:07 -0500 (Tue, 23 Jan 2018) $ *)







