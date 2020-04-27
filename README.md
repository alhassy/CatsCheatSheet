<h1> CatsCheatSheet </h1>

This project is to contain a listing of common theorems in elementary category theory.

**The repo contains other articles I've written on Category Theory;**
**which may be read in a blog-format at:**
<https://alhassy.github.io/blog/categories/#categorytheory>

**The listing sheet, as PDF, can be found [here](https://github.com/alhassy/CatsCheatSheet/blob/master/CheatSheet.pdf)**,
while below is an unruly html rendition.

This reference sheet is built around the system <https://github.com/alhassy/CheatSheet>


# Table of Contents

1.  [Categories](#org190f6a8)
2.  [“Gluing” Morphisms Together](#org417a0df)
3.  [Functors](#org42710d1)
4.  [Naturality](#orgd826582)
5.  [Adjunctions](#org18cc334)
6.  [Constant Combinators](#orge6a49a5)
7.  [Monics and Epics](#org61d71cb)
8.  [Isos](#orgbb74ee3)
9.  [Skolemisation](#org4b4d8fd)
10. [Initiality](#org1176ce5)
11. [Colimits](#orgbbe90f6)
12. [Limits](#orgc00a537)
13. [Sums](#orgd3b4147)
14. [Products](#org52f269b)
15. [Finitary Sums and Products](#org6d13b13)
16. [Mixing products and coproducts](#org08ec4d2)
17. [References](#org824df47)
18. [To Read](#orgf2ec4a5)
19. [Monoidal and Closed Categories](#org53fdf4f)
20. [Enrichment & Internal Algebraic Structures](#org08ad92a)














<a id="org190f6a8"></a>

# Categories

A **category** 𝒞 consists of a collection of “objects” \(\Obj\, 𝒞\),
  a collection of  “(homo)morphisms” \(\Hom_𝒞(a,b)\) for any \(a,b : \Obj\,𝒞\)
  &#x2014;also denoted “\(a \,\to_𝒞\, b\)”&#x2014;,
  an operation \(\Id\) associating a morphism \(\Idₐ : \Hom(a,a)\) to each object \(a\),
  and a dependently-typed “composition” operation
  \(\_∘\_ : ∀\{A \, B \, C : \Obj\} → \Hom(B,C) → \Hom(A,B) → \Hom(A,C)\)
  that is required to be associative with \(\Id\) as identity.

It is convenient to define a pair of operations \(\src, \tgt\) from morphisms to objects
as follows:

\begin{flalign*}
    f : X \to_𝒞 Y \quad\equiv\quad \mathsf{src}\; f = X \;\land\; \mathsf{tgt}\; f = Y
   &&
   \tag*{$\src,\tgt$-Definition}
   \label{src-tgt-Definition}
\end{flalign*}

Instead of \(\Hom_𝒞\) we can instead assume primitive a ternary relation
\(\_:\_→_𝒞\_\) and regain \(\Hom_𝒞\) precisely when the relation is functional
in its last two arguments:
\eqn{type-Unique}{f : A \to_𝒞 B \;\;\land\;\; f : A' \to_𝒞 B' \;\implies\; A=A' \;\land\; B=B'}
When this condition is dropped, we obtain a *pre-category*; e.g., the familiar *Sets*
is a pre-category that is usually treated as a category by making morphisms
contain the information about their source and target: \((A, f, B) : A → B\)
rather than just \(f\).
\newline
 *This is sometimes easier to give than Hom! C.f. Alg(F).*
\room

Here's an equivalence-preserving property that is useful in algebraic calculations,

Examples:

-   [Linear Algebra:](https://arxiv.org/abs/1312.4818) Matrices with real number values determine a category whose objects are the natural numbers,
    morphisms \(n → m\) are \(n × m\) matrices, \(\Id\) is the identity matrix, and composition
    is matrix multiplication.

-   Each preorder determines a category: The objects are the elements
    and there is a morphism \(a → b\) named, say, “\((a, b)\)”, precisely when \(a \leq b\);
    composition boils down to transitivity of \(\leq\).

-   Each monoid \((M, ⊕, e)\) gives rise to a category: The objects and the arrows
    are both the elements of\(M\), and \(k : m → n \;≡\; k ⊕ m = n\).
    E.g., \((ℕ, ×, 1)\) gives rise to a category whose products are gcd's
    and so properties of products are thus gcd theorems!

-   Each digraph determines a category: The objects are the nodes
    and the paths are the morphisms typed with their starting and ending node.
    Composition is catenation of paths and identity is the empty path.

-   Suppose we have an \`interface', in the programming sense,
    of constant, function, and relation symbols &#x2014;this is also called a *signature*.

    Let 𝒯 be any collection of sentences in the first-order language of signature \(\Sigma\).
    Then we can define a category \(\mathsf{Mod}\,𝒯\) whose objects are
    implementations of interface \(\Sigma\) satisfying constraints 𝒯, and whose morphisms
    are functions that preserve the \(\Sigma\) structure.
    Ignoring constraints 𝒯 gives us \`functor algebras'.

    Particular examples include monoids and structure-preserving maps between them;
    likewise digraphs, posets, rings, etc and their homomorphisms.

\room

Even when morphisms are functions, the objects need not be sets:
Sometimes the objects are *operations* &#x2014;with an appropriate definition
of typing for the functions. The categories of *F*-algebras are an example
of this.


<a id="org417a0df"></a>

# “Gluing” Morphisms Together

Traditional function application is replaced by the more generic concept of
functional *composition* suggested by morphism-arrow chaining:

Whenever we have two morphisms such that the target type of one
of them, say \(g : B ← A\) is the same as the source type of the other,
say \(f : C ← B\) then “\(f\) after \(g\)”, their *composite morphism*,
\(f ∘ g : C ← A\) can be defined. It “glues” \(f\) and \(g\) together,
“sequentially”:

Composition is the basis for gluing morphisms together to build more complex morphisms.
However, not every two morphisms can be glued together by composition.

\room

Types provide the interface for putting morphisms together to obtain more complex functions.

\room

A *split* arises wherever two morphisms do not compose but share the same source.

-   Since they share the same source, their outputs can be paired: \(c ↦ (f\, c, g\, c)\).
-   This duplicates the input so that the functions can be executed in “parallel” on it.

\room

A *product* appears when there is no explicit relationship between the types of the morphisms.

-   We regard their sources as projections of a product, whence they can be seen as *splits*.
-   This \((c, d) ↦ (f\, c, g\, d)\) corresponds to the “parallel” application of \(f\) and \(g\),
    each with its *own* input.

\room

An *either* arises wherever two morphisms do not compose but share the same target.

-   Apply \(f\) if the input is from the “\(A\) side” or apply \(g\) if it is from the “\(B\) side”.
-   This is a “case analysis” of the input with branches being either \(f\) or \(g\).

\room

A *sum* appears when there is no explicit relationship between the types of the morphisms.

-   We regard their targets as injections into a sum, whence they can be seen as *eithers*.

\room

A *transpose* arises when we need to combine a binary morphism with a unary morphism.

-   I.e., it arises when a composition chain is interrupted by an extra product argument.
-   Express \(f\) as a *C*-indexed family, \(f_c : A → B\), of morphisms such that applying a function at any index
    behaves like \(f\); i.e., \(f_c \, a = f(c, a)\). Each \(f_c\) can now be composed with \(g\).
    Let \(\transpose{(\;)}\) denote the operation \(f ↦ f_c\).

\vspace{-0.5em}

\vspace{1em}


<a id="org42710d1"></a>

# Functors

A **functor** *F : 𝒜 → ℬ* is a pair of mappings, denoted by one name,
from the objects, and morphisms, of 𝒜 to those of ℬ such that
it respects the categorical structure:

\vspace{1em}

The two axioms are equivalent to the single statement that
*functors distribute over finite compositions, with \(\Id\) being the empty composition:*
\[ F(f_0 ∘ \cdots ∘ f_{n-1}) \;=\; F\, f_0 ∘ \cdots ∘ F\, f_{n-1} \]

Use of Functors.

-   In the definition of a category, “objects” are “just things” for which no internal
    structure is observable by categorical means &#x2014;composition, identities, morphisms, typing.
    *Functors form the tool to deal with “structured” objects.*

    Indeed in 𝒮ℯ𝓉 the aspect of a structure is that it has “constituents”, and that it is possible
    to apply a function to all the individual constituents; this is done by
    *F f : F A → F B*.

-   For example, let \(\bin A = A × A\) and \(\bin f = (x, y) ↦ (f\, x, f\, y)\).
    So \(\bin\) is or represents the structure of pairs; \(\bin\, A\) is the set of pairs of *A*,
    and \(\bin\, f\) is the function that applies *f* to each constituent of a pair.
    -   A *binary operation on A* is then just a function \(\bin A → A\);
        in the same sense we obtain *F-ary operations*.

-   Also, *Seq* is or represents the structure of sequences; *Seq A* is the structure of sequences
    over *A*, and *Seq f* is the function that applies *f* to each constituent of a sequence.

-   Even though *F A* is still just an object, a thing with no observable internal structure, the
    functor properties enable to exploit the “structure” of *F A* by allowing us to “apply”
    an *f* to each “constituent” by using *F f*.

\vspace{1em}

Category \(𝒜lℊ(F)\)

-   For a functor *F : 𝒜 → 𝒟*, this category has *F-algebras*, *F*-ary operations in 𝒟 as, objects
    &#x2014; i.e., objects are 𝒟-arrows \(F\, A → A\) &#x2014;
    and *F*-homomorphisms as morphisms, and it inherits composition and identities from 𝒟.

    Note that category axiom \eqref{unique-Type} is not fulfilled since a function can be
    a homomorphism between several distinct operations. However, we pretend it is a category
    in the way discussed earlier, and so the carrier of an algebra is fully determined by
    the operation itself, so that the operation itself can be considered the algebra.

    <div class="org-center">
    *\ref{comp-Homomorhism} renders a semantic property as a syntactic condition!*
    </div>

\vspace{1em}

-   A **contravariant functor** 𝒞 → 𝒟 is just a functor *𝒞ᵒᵖ → 𝒟*.
-   A **bifunctor** from 𝒞 to 𝒟 is just a functor *𝒞² → 𝒟*.


<a id="orgd826582"></a>

# Naturality

A natural transformation is nothing but a structure preserving map between functors.
“Structure preservation” makes sense, here, since we've seen already that a functor
is, or represents, a structure that objects might have.

\room

As discussed before for the case *F : 𝒞 → 𝒮ℯ𝓉*, each *F A* denotes a structured set
and *F* denotes the structure itself.

\hspace{-1em}:
\(\bin\) is the structure of pairs, *Seq* is the structure of sequences,
*Seq Seq* the structure of sequences of sequences,
\(\bin \, Seq\) the structure of pairs of sequences &#x2014;which is naturally isomorphic
to \(Seq \, \bin\) the structure of sequences of pairs!&#x2014;, and so on.

\room

A “transformation” from structure *F* to structure *G* is a family of functions \newline
\(η : ∀\{A\} → F\, A → G\, A\); and it is “natural” if each \(η_A\) doesn't affect the *constituents*
of the structured elements in *F A* but only reshapes the structure of the elements,
from an *F*-structure to a *G*-structure.

\vspace{0em}

<div class="org-center">
*Reshaping the structure by η commutes with subjecting the constituents to an arbitrary morphism.*
</div>

\vspace{-2em}

This is \`naturally' remembered: Morphism \(η_{\tgt\, f}\) has type \(F (\tgt\, f) → G(\tgt\, f)\) and therefore
appears at the target side of an occurrence of *f*; similarly \(η_{\src\, f}\) occurs at the source side of an *f*.
*Moreover* since η is a transformation *from* *F* to *G*, functor *F* occurs at the source side of an η
and functor *G* at the target side.

\room

-   One also says *ηₐ is natural in* its parameter *a*.

-   If we take \(G = \Id\), then natural transformations are *F*-homomorphisms.
    Thus, naturality is a kind of homomorphism condition.

-   Indeed, a natural transformation is a sort-of homomorphism in that the image of a morphism
    after reshaping is the same as the reshaping of the image.

\room

Example natural transformations

-   *rev : Seq →̣ Seq : [a₁, …, aₙ] ↦ [aₙ, …, a₁]*
    reverses its argument thereby reshaping a sequence structure into a sequence structure without affecting the constituents.

-   *inits : Seq →̣ Seq Seq : [a₁, …, aₙ] ↦ [[], [a₁], ⋯, [a₁, …, aₙ]]*
    yields all initial parts of its argument
    thereby reshaping a sequence structure into a sequence of sequences structure, not affecting
    the constituents of its argument.

\room

\room

**Category ℱ𝓊𝓃𝒸(𝒞, 𝒟)**
consists of functors *𝒞 → 𝒟* as objects and natural transformations between them as arrows.
The identity transformation is indeed an identity for transformation composition, which is associative.

\room

**Heuristic** To prove \(φ = φ₁ ∘ ⋯ ∘ φₙ : F →̣ G\) is a natural transformation, it suffices
to show that each \(φᵢ\) is a natural transformation.
E.g., without even knowing the definitions, naturality of
*tails = Seq rev ∘ inits ∘ rev* can be proven &#x2014;just type checking!

\iffalse

-   Theorem \eqref{ntrf-Compose} renders proofs of semantic properties to be trivial type checking!
-   E.g., It's trivial to prove *tails = rev ﹔ inits ﹔ Seq rev* is a natural transformation
    by type checking, but to prove the naturality equation by using the naturality equations of
    *rev* and *inits* &#x2014;no definitions required&#x2014; necessitates more writing, and worse: Actual thought!

\fi


<a id="org18cc334"></a>

# Adjunctions

An adjunction is a particular one-one correspondence between different kinds of
morphisms in different categories.

\room

An **adjunction** consists of two functors \(L : 𝒜 → ℬ\) and \(R : ℬ → 𝒜\),
as well as two (not necessarily natural!) transformations
\(η : \Id → RL\) and \(ε : LR → \Id\) such that

\vspace{-1em}

Reading right-to-left: In the equation \(ε_B ∘ L f = g\) there is a unique solution to the unknown \(f\).
Dually for the other direction.

\room

That is,
*each L-algebra g is uniquely determined &#x2014;as an L-map followed by an ε-reduce---*
*by its restriction to the adjunction's unit η.*

\room

A famous example is “Free ⊣ Forgetful”, e.g. to *define* the list datatype, for which the above
becomes: Homomorphisms on lists are uniquely determined, as a map followed by a reduce,
by their restriction to the singleton sequences.

\room

We may call \(f\) the restriction, or lowering, of \(g\) to the “unital case”
and write \(f = ⌊g⌋ = R g ∘ η_A\). Also, we may call \(g\) the extension, or raising,
of \(f\) to an *L*-homomorphism and write \(g = ⌈f⌉ = ε_B ∘ L f\). The above equivalence
now reads:

\room
\vspace{1ex}
Note that ⌈ is like \`r' and the argument to ⌈⌉ must involve the *R*-ight adjoint in its type;

\room

This equivalence expresses that \`lad' \(⌊⌋\), from \emph{l}eft \emph{ad}jungate,
and \`rad' \(⌈⌉\), from \emph{r}ight \emph{ad}jungate, are each other's inverses
and constitute a correspondence between certain morphisms.
*Being a bijective pair, lad and rad are injective, surjective, and undo one another.*

\room

We may think of ℬ as having all complicated problems so we abstract
away some difficulties by \emph{r}aising up to a cleaner, simpler, domain
via rad ⌈⌉; we then solve our problem there, then go back \emph{down} to
the more complicated concrete issue via ⌊⌋, lad.
\newline
( E.g., ℬ is the category of monoids, and 𝒜 is the category of sets; \(L\) is the list functor. )

Also,

-   Left adjoints preserve colimits such as initial objects and sums.
-   Right adjoints preserve limits such as terminal objects and products.


<a id="orge6a49a5"></a>

# Constant Combinators

Opposite to the identity functions which do not lose any information,
we find functions which lose all, or almost all, information.
Regardless of their input, the output of these functions is always the
same value.

\(\K : 𝒞 → ℱ𝓊𝓃𝒸(𝒟,𝒞)\)

-   For objects \(x\), the \`\`constant functor'':
    \(\K{x}\, y = x\) and \(\K{x}\, f = \Id_x\) for objects \(y\) and morphisms \(f\).
-   For morphisms \(f\), the \`\`constant natural transformation'':
    \(\K{f} : \K{(\src f)} →̣ \K{(\tgt f)}\)
    sending objects \(y\) to morphism \(\K{f}\, y = f\).

\room
Sometimes it is convenient to notate \(\const{c} = \K \, c\)
and refer to this as the *everywhere c* operation.

The following property defines constant functors at the \`pointfree level':

Constant functors force any difference in behaviour for any two
functors to disappear:

Interestingly, functor composition and application
are bridged explicitly by the constant functor:


<a id="org61d71cb"></a>

# Monics and Epics

Identity functions and constant functions are limit points of the
functional spectrum with respect to information preservation.
All the other functions are in-between: They “lose” some information,
which is regarded as uninteresting for some reason.

\room

How do functions lose information?
Basically in two ways: They may be “blind” enough to confuse different
inputs, by mapping them to the same output, or they may ignore values
of their target. For instance, \(\const{c}\) confuses all inputs
by mapping them all onto \(c\). Moreover, it ignores all values of its
target apart from \(c\).

\room

Functions which do not confuse their inputs are called *monics*:
They are “post-cancellable”:

Functions which do not ignore values of their target are called
*epics*: They are “pre-cancellable”:

Intuitively, \(h = k\) on all points of their source precisely when
they are equal on all image points of \(f\), since \(f\) being epic means
it outputs all values of their source.

\room

It is easy to check that “the” identity function is monic and epic,
while any constant function \(\const{c}\) is not monic and is only
epic when its target consists only of \(c\).


<a id="orgbb74ee3"></a>

# Isos

An arrow is an *iso* iff it is invertible; i.e., there is an “inverse” morphism
\(f\inverse\) with
\eqn{inverse-Char}{ f ∘ f\inverse = \Id \landS f\inverse ∘ f = \Id}

To *construct* \(f\inverse\), we begin by identifying its type which may give
insight into its necessary \`shape' &#x2014;e.g., as a sum or a product&#x2014;
then we pick one of these equations and try to reduce it as much as possible
until we arrive at a definition of \(f˘\), or its \`components'.

-   E.g.,
    \(coassocr = [\Id + \inl, \inr ∘ \inr]\) of type \((A + B) + C ≅ A + (B + C)\),
    its inverse  *coassocl* must be of the shape \([x, [y, z]]\) for unknowns
    \(x,y,z\) which can be calculated
    by solving the equation \([x, [y, z]] ∘ coassocr = \Id\) &#x2014;Do it!

\room

The following rules can be of help if \(f\inverse\) is found handier than isomorphism \(f\)
in reasoning,

\begineqns

\eqn{inverse-Shunting1}{ f ∘ x = y \equivS x = f\inverse ∘ y}

\eqn{inverse-Shunting2}{ x ∘ f = y \equivS x = y ∘ f\inverse}

\endeqns

\room
\room

Isos are necessarily monic and epic, but in general the other way
around is not true.

\room

Isomorphisms are very important because they convert data from one
“format”, say \(A\), to another format, say \(B\), without losing
information. So \(f\) and \(f˘\) are faithful protocols between the two
formats \(A\) and \(B\).
Of course, these formats contain the same “amount” of information
although the same data adopts a “different” shape in each of them.
─c.f. \nameref{SeqPair-is-Pair-Seq}.

\room

Isomorphic data domains are regarded as “abstractly” the same;
then one write \(A ≅ B\).

Finally, note that all classes of functions referred to so far
&#x2014;identities, constants, epics, monics, and isos&#x2014;
are closed under composition.

Monics to the initial object are necessarily isos!


<a id="org4b4d8fd"></a>

# Skolemisation

If a property \(P\) holds for precisely one class of isomorphic objects,
and for any two objects in the same class there is precisely one
isomorphism from one to the other, then we say that
*the P-object is unique up to unique isomorphism*.
For example, in 𝒮ℯ𝓉 the one-point set is unique up to a unique isomorphism,
but the two-point set is not.

\room

For example, an object *A* is \`\`initial'' iff
\(∀ B  \;•\;  ∃₁ f  \;•\;  f : A → B\), and such objects are unique
up to unique isomorphism &#x2014;prove it!
The formulation of the definition is clear but it's not very well suited for *algebraic manipulation*.

\room

A convenient formulation is obtained by \`skolemisation': An assertion of the form
\[ ∀ x \;•\; ∃₁ y \;•\; R \, x \, y \]
is equivalent to: There's a function ℱ such that
\[ \, \hspace{13em} ∀ x, y \;•\; R \, x \, y \;≡\; y = ℱ\, x  \hspace{8em}\text{\sc(ℱ-Char)} \]
In the former formulation it is the existential quantification “\(∃ y\)” inside the scope of a universal
one that hinders effective calculation. In the latter formulation the existence claim is brought to a
more global level: A reasoning need no longer be interrupted by the declaration and naming of the
existence of a unique \(y\) that depends on \(x\); it can be denoted just \(ℱ\, x\).
As usual, the final universal quantification can be omitted, thus simplifying the formulation once more.

\room

In view of the important role of the various \(y\)'s, these \(y\)'s deserve a particular notation that
triggers the reader of their particular properties. We employ bracket notation such as \(⦇ x ⦈\)
for such \(ℱ\, x\): An advantage of the bracket notation is that no extra parentheses are needed
for composite arguments \(x\), which we expect to occur often.

\room

The formula *characterising* \(ℱ\) may be called \`ℱ-Char' and it immediately give us some results
by truthifying each side, namely \`Self' and \`Id'. A bit more on the naming:

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<tbody>
<tr>
<td class="org-left">Type</td>
<td class="org-left">Possibly non-syntactic constraint on notation being well-formed</td>
</tr>


<tr>
<td class="org-left">Self</td>
<td class="org-left">It, itself, is a solution</td>
</tr>


<tr>
<td class="org-left">Id</td>
<td class="org-left">How \(\Id\) can be expressed using it</td>
</tr>


<tr>
<td class="org-left">Uniq</td>
<td class="org-left">Its problem has a unique solution</td>
</tr>


<tr>
<td class="org-left">Fusion</td>
<td class="org-left">How it behaves with respect to composition</td>
</tr>


<tr>
<td class="org-left">Composition</td>
<td class="org-left">How two instances, in full subcategories, compose</td>
</tr>
</tbody>
</table>

Note that the last 3 indicate how the concept interacts with the categorical structure:
\(=, ﹔, \Id\). Also note that Self says there's at least one solution and Uniq says there is
at most one solution, so together they are equivalent to ℱ-Char &#x2014;however those two proofs
are usually not easier nor more elegant than a proof of ℱ-Char directly.

\room

**Proving ℱ-Char** is straightforwardly accomplished by providing a definition for ℱ
and establishing ℱ-Char &#x2014;these two steps can be done in parallel! Almost every such
proof has the following format, or a circular implication thereof: For arbitrary \(x\) and \(y\),

<div class="calculation">
R \kern0.5ex x \kern0.5ex y
\step[≡]{}
⋮
\step[≡]{}
y = \text{“an expression not involving $y$”}
\step[≡]{ 𝒹ℯ𝒻𝒾𝓃ℯ $ℱ \, x$ to be the right side of the previous equation }
y = ℱ \kern0.5ex x

</div>


<a id="org1176ce5"></a>

# Initiality

An object *0 is initial* if there's a mapping \(⦇-⦈\), from objects to morphisms,
such that \ref{initial-Char} holds; from which we obtain a host of useful corollaries.
Alternative notations for \(⦇ B ⦈\) are \(\text{!`}_B\), or \(⦇0 → B⦈\) to make the
dependency on 0 explicit.

\vspace{1em}

These laws become much more interesting when the category is built upon another
one and the typing is expressed as one or more equations in the underlying
category. In particular the importance of fusion laws cannot be over-emphasised;
it is proven by a strengthening step of the form
\(f ∘ ⦇B⦈ : 0 → C \providedS ⦇B⦈ : 0 → B \lands f : B → C\).

\room

For example, it can be seen that the datatype of sequences is \`the' initial object
in a suitable category, and the mediator \(⦇-⦈\) captures
“definitions by induction on the structure”! Hence induction arguments
can be replaced by initiality arguments! Woah!


<a id="orgbbe90f6"></a>

# Colimits

Each colimit is a certain initial object, and each initial object is a certain colimit.

-   A *diagram in 𝒞* is a functor \(D : 𝒟 → 𝒞\).

-   Recall \nameref{constant-combinator} yielding a functor on objects ---\(\const{C}\, x = C\) for objects \(x\) and
    \(\const{C}\, f = \Id_C\) for morphisms *f*&#x2014; and a natural transformation on arrows
    ---\(\const{g} = x \mapsto g : \const{A} →̣ \const{B}\) for morphism \(g : A → B\).

-   The category \(⋁D\), built upon 𝒞, has objects \(γ : D →̣ \const{C}\) called “co-cones”, for
    some object \(C =: \tgt\, γ\), and a morphism from \(γ\) to \(δ\) is a 𝒞-morphism \(x\) such that \(\const{x} ∘ γ = δ\).

    *\`Cones' sit upright on their base, \(D\), on a table; \`CoCones' sit upright on a co-table!*

-   A *colimit for D* is an initial object in \(⋁ D\); which may or may not exist.

\room

Writing \(-╱γ\) for \(⦇-⦈\) and working out the definition of co-cone in terms of equations in 𝒞,
  we obtain: *\(γ : Obj(⋁D)\) is a colimit for \(D\)* if there is a mapping \(-╱γ\) such that *╱-Type* and
*╱-Char* hold.

\room
\room

Let \(()_x : \varnothing →̣ \K{x}\) be the natural transformation from the
empty functor \(\varnothing : \mathbf{0} \to 𝒞\) to the constant functor.
\vspace{-0.8em}

Cocones under \(D\) correspond one-to-one with arrows from its colimit:
\vspace{-0.8em}


<a id="orgc00a537"></a>

# Limits

Dually, the category \(⋀D\) has objects being “cones” \(γ : \const{C} →̣ D\) where \(C =: \src\, γ\)
is a 𝒞-object, and a morphism to \(γ\) *from* \(δ\) is a 𝒞-morphism \(x\) such that \(γ ∘ \const{x} = δ\).
In terms of 𝒞, *\(γ : Obj(⋀ D)\) is a limit for \(D\)* if there is a mapping \(γ╲-\) such that
the following ╲-Type and ╲-Char hold, from which we obtain a host of corollaries.
As usual, there is the implicit well-formedness condition.

\vspace{-1em}

\newpage


<a id="orgd3b4147"></a>

# Sums

Take \(D\) and \(𝒟\) as suggested by \(D𝒟 = \left( \overset{A}{•} \;\;\; \overset{B}{•} \right)\).
Then a cocone δ for \(D\) is a two-member family \(δ = (f, g)\) with
\(f : A → C\) and \(g : B → C\), where \(C = \tgt\, δ\).

\room

Let \(γ=(\inl, \inr)\) be a colimit for \(D\), let \(A + B = \tgt\,γ\), and write
\([f, g]\) in-place of \(γ╲(f, g)\), then the ╲-laws yield:
*\((\inl, \inr, A+B)\) form a sum of \(A\) and \(B\)* if there is a mapping \([-,-]\)
such that \ref{[]-Type} and \ref{[]-Char} hold.

\room
\room

In the pointwise setting, notice that the cancellation law serves to define the casing construct [-,-].
Then that casing is a form of conditional can be read from the characterisation.
With this view, fusion, post-distributivity of composition over casing is just
the usual law that function application distributes over conditionals
and the casing extensionality law is the body-idempotency of conditionals.

\room

For categories in which sums exist, we define for \(f : A → B\) and \(g : C → D\),

\begineqns

\eqn{+-Definition}{ f + g = [ \inl ∘ f, \inr ∘ g] : A + C → B + D}

\eqn{Injections-Naturality}{ (f + g) ∘ \inl = f ∘ \inl \landS (f + g) ∘ \inr = \inr ∘ g }

\eqn{Extensionality}{ [h ∘ \inl , h ∘ \inr] = h}

\eqn{Absorption}{ [h, j] ∘ (f + g) = [h ∘ f, j ∘ g] }

\eqn{+-BiFunctoriality}{ \Id + \Id = \Id \landS (f + g) ∘ (h + j) = (f ∘ h) + (g ∘ j)}

\eqn{Structural Equality}{ [f,g] = [h, j] \equivS f = h \lands g = j }

\endeqns

\newpage


<a id="org52f269b"></a>

# Products

Take \(D\) and \(𝒟\) as suggested by \(D𝒟 = \left( \overset{A}{•} \;\;\; \overset{B}{•} \right)\).
Then a cone δ for \(D\) is a two-member family \(δ = (f, g)\) with
\(f : C → A\) and \(g : C → B\), where \(C = \tgt\, δ\).

\room

Let \(γ=(\fst, \snd)\) be a limit for \(D\), let \(A + B = \tgt\,γ\), and write
\(⟨f, g⟩\) in-place of \((f, g)╱γ\), then the ╱-laws yield:
*\((\fst, \snd, A × B)\) form a product of A and B* if there is an operation
\(⟨-,-⟩\) satisfying the Char and Type laws below; from which we obtain a host of corollaries.

\room
\room

The characterisation says that the essential properties of ordered pairs
is that their components are retrievable and they are
completely determined by their components.

\room

Notice that the cancellation rule is essentially the *definitions of projections* in the pointwise setting;
likewise absorption is akin to the pointwise definition of the product bi-map.

\room

The fusion laws give us a pointfree rendition of their usual pointwise
definitions: All applications have been lifted to compositions!

\room

For categories in which products exist, we define for \(f : A → B\) and \(g : C → D\),

\begineqns

\eqn{x-Definition}{ f × g = ⟨ f ∘ \fst, g ∘ \snd ⟩ : A × C → B × D}

\eqn{Projections-Naturality}{ \fst ∘ (f × g) = f ∘ \fst \landS \snd ∘ (f × g) = g ∘ \snd }

\eqn{Extensionality}{ ⟨\fst ∘ h, \snd ∘ h⟩ = h}

\eqn{Absorption}{ (f × g) ∘ ⟨h, j⟩ = ⟨f ∘ h, g ∘ j⟩ }

\eqn{x-BiFunctoriality}{ \Id × \Id = \Id \landS (f × g) ∘ (h × j) = (f ∘ h) × (g ∘ j)}

\eqn{Structural Equality}{ ⟨f,g⟩ = ⟨h, j⟩ \equivS f = h \lands g = j }

\endeqns


<a id="org6d13b13"></a>

# Finitary Sums and Products

All properties studied for binary *splits* and binary *eithers* extend to the
finitary case. For the particular situation \(n = 1\), we will have \(⟨f⟩=[f]=f\)
and \(\inl = \fst = \Id\), of course.

\room

For the particular situation \(n = 0\),
finitary products “degenerate” to terminal object 1 and finitary sums “degenerate” to initial object 0.
The standard notation for the empty split \(⟨⟩\) is \(!_C\), where \(C\) is the source.
Dually, the standard notation for the empty either \([]\) is \(?_C\).

\eqn{Empty Exchange Rule}{ ⟨⟩_0 = []_1 }


<a id="org08ec4d2"></a>

# Mixing products and coproducts

Any \(f : A + B → C × D\) can be expressed alternatively as an *either*
or as a *split*. It turns out that both formats are identical:

\vspace{-1.5em}
\eqn{Exchange Rule}{ ⟨[f,g], [h,j]⟩ = [⟨f,h⟩,⟨g,j⟩] }

E.g., \(\mathsf{undistr}  = ⟨[\fst, \fst], \snd + \snd⟩ = [\Id × \inl, \Id × \inr] : (A × B) + (A × C) → A × (B + C)\).

\begineqns

\eqn{Cool-Property}{ [f × g, h × k] \;=\; ⟨ [f, h] ∘ (\fst + \fst), [g, k] ∘ (\snd + \snd)⟩ }

\eqn{Co-cool-Property}{ ⟨f + g, h + k⟩ \;=\; [ (\inl × \inl) ∘ ⟨f, h⟩, (\inr × \inr) ∘ ⟨g, k⟩] }

\endeqns

\room

Also, since constants ignore their inputs,


<a id="org824df47"></a>

# References

[A Gentle Introduction to Category Theory ─ the calculational approach](https://maartenfokkinga.github.io/utwente/mmf92b.pdf)
\newline
by [Maarten Fokkinga](https://maartenfokkinga.github.io/utwente/)

\vspace{1em}

An excellent introduction to category theory with examples motivated from programming, in-particular
working with sequences. All steps are shown in a calculational style &#x2014;which Fokkinga
has made [available](https://ctan.org/tex-archive/macros/latex/contrib/calculation) for use with LaTeX&#x2014; thereby making it suitable for self-study.

\vspace{1em}

Clear, concise, and an illuminating read.

\vspace{1em}

I've deviated from his exposition by using backwards composition \`∘' rather
than diagrammatic composition \`;', as such my limit notation is his colimit notation! Be careful.

\vspace{1em}

I've also consulted the delightful read [Program Design by Calculation](http://www4.di.uminho.pt/~jno/ps/pdbc_part.pdf) of [José Oliveira](http://www4.di.uminho.pt/~jno/).

\vspace{0.5em}

Very accessible for anyone who wants an introduction to functional programming!
The category theory is mostly implicit, but presented elegantly!

\vspace{-0.5em}


<a id="orgf2ec4a5"></a>

# To Read

-   [Toposes, Triples and Theories](http://www.cwru.edu/artsci/math/wells/pub/ttt.html) by Michael Barr and Charles Wells
-   [Seven Sketches in Compositionality: An Invitation to Applied Category Theory](https://arxiv.org/pdf/1803.05316.pdf)
-   [Frobenius algebras and ambidextrous adjunctions](https://arxiv.org/abs/math/0502550) by Aaron Lauda
-   [Functorial Semantics of Algebraic Theories](http://www.tac.mta.ca/tac/reprints/articles/5/tr5.pdf) by F. William Lawvere
-   [Basic Concepts of Enriched Category Theory](http://www.tac.mta.ca/tac/reprints/articles/10/tr10.pdf) by G.M. Kelly
-   [Rosetta Stone](http://golem.ph.utexas.edu/category/2008/03/physics_topology_logic_and_com.html)
-   [Category Theory for Computing Science &#x2013; Michael Barr and Charles Wells](http://www.math.mcgill.ca/triples/Barr-Wells-ctcs.pdf)

Monoidal:

-   [Elementary remarks on units in monoidal categories](https://arxiv.org/pdf/math/0507349.pdf)
-   [ASSOCIATIVITY CONSTRAINTS IN MONOIDAL CATEGORIES](http://math.uchicago.edu/~may/TQFT/Boyarchenko%20on%20associativity.pdf)
-   [Tensor Categories](http://mtm.ufsc.br/~ebatista/2016-2/tensor_categories.pdf)

\newpage


<a id="org53fdf4f"></a>

# Monoidal and Closed Categories

It is rather common that we have a notion of pairing for types for which there is a unit type.
Examples include products with the initial object, sums with the terminal object, or for
the category of endofunctors: Functor composition with the identity functor.

\room

A *monoidal category* *(𝒞, ⊗, I, α, λ, ρ)* consists of a category 𝒞 with bifunctor
\newline
\(\_{}⊗\_{} : 𝒞^2 → 𝒞\) and object *I : Obj 𝒞*
&#x2014;referred to as the ‘tensor product’ and ‘tensor unit&#x2014;
and three natural isomorphisms:
\newline
The ‘(right-to-left) associator’ *α<sub>A, B, C</sub> : A ⊗ (B ⊗ C) ≅ (A ⊗ B) ⊗ C* and
\newline
the ‘unitors’  *λ<sub>A</sub> : I ⊗ A ≅ A* and *ρ<sub>A</sub> : A ⊗ I ≅ A* such that:

1.  The order of re-parensization, outer-most or inner-most first, does not matter; i.e.,
    the two obvious maps witnessing \(A ⊗ (B ⊗ (C ⊗ D)) → ((A ⊗ B) ⊗ C) ⊗ D\) are identical:
    \(α_{A ⊗ B, C, D} \;∘\; α_{A, B, C ⊗ D} \eqs α_{A, B, C} ⊗ \Id_D \;∘\; α_{A, B ⊗ C, D}\;∘\; \Id_A ⊗ α_{B, C, D}\).

2.  Unit elimination paths are the same even if unnecessary associtivity is performed; i.e.,
    the two obvious maps witnessing \(A ⊗ (I ⊗ B) → A ⊗ B\) are identical:
    \newline
    \(\Id_A ⊗ λ_B \eqs (ρ_A ⊗ \Id_B) \;∘\; α_{A, I, B}\).

Mnemonic: λ, ‘L’ambda, is for ‘L’eft unitor; ρ, ‘R’ho, is for ‘R’ight unitor.

\room

Unfolding some of that up yields:

-   \(\Id ⊕ \Id = \Id\) and \((f ∘ g) ⊗ (h ∘ k) = (f ⊗ h) ∘ (g ⊗ k)\)
-   \(α ∘ (f ⊗ (g ⊗ h)) = ((f ⊗ g) ⊗ h) ∘ α\)
-   \(λ ∘ (\Id ⊗ f) = f ∘ λ\)
-   \(ρ ∘ (f ⊗ \Id) = f ∘ ρ\)

**Mac Lane's coherence theorem:** Any well-typed diagram built from ⊗, α, λ, ρ commutes.

\room

\eqn{Unit-Equivalence-Left}{ \Id ⊗ f = \Id ⊗ g  \equivS  f = g }
\eqn{Unit-Equivalence-Right}{ f ⊗ \Id = g ⊗ \Id \equivS  f = g }

\room

The apparent complexity of the definition of monoidal categories vanishes
when a [geometrical notation](https://qchu.wordpress.com/2012/11/05/introduction-to-string-diagrams/) is used &#x2014;the coherence laws simply become
expected geometric operations on the plane.
The geometric interpretation is sound and complete
&#x2014;i.e., equal morphisms yield ‘equal’ pictures, and conversely.

( [A survey of graphical languages for monoidal categories](https://www.mathstat.dal.ca/~selinger/papers/graphical-2up.pdf) )

\room

Examples

-   Common examples include preordered monoids thought of as monoidal categories.
-   Functor categories \(𝒞^𝒞\) with tensor being functor composition.
-   Any category with finite co/products is monoidal using sums or products; e.g., 𝒮ℯ𝓉.
-   ℛℯ𝓁 with Cartesian product is monoidal, even though this is *not*
    a categorical product.
-   The ‘free strict monoidal category’ on 𝒞 has objects being
    finite lists of 𝒞-objects where an arrow exists only between equal length
    lists and it is a list of 𝒞-morphisms between the corresponding components;
    tensor is catenation with the empty list as the unit object.
-   Symmetric monoidal categories are closed under products, and this has a right
    adjoint yielding functor categories of sym. mon. cats.
    -   (Mat(K), ⊗, 1): The category whose objects are natural numbers and whose arrows M : m → n are n × m matrices taking values in field K. Composition is matrix multiplication, the monoidal

product is multiplication of natural numbers (on objects) and the [Kronecker product](https://en.wikipedia.org/wiki/Kronecker_product#Definition) of matrices (on arrows). This category is essentially the category of finite-dimensional vector spaces over K, with a chosen basis for all of its objects.

\room

Interestingly, tensor distributes over sums: `(A + B) ⊗ C ≅ (A ⊗ C) + (B ⊗ C)`.

\room

A **lax monoidal functor** \(F : 𝒱 ⟶ 𝒱′\) is a functor that sub-factors over product:
\(F \, x_0 ⊗ ⋯ ⊗ F\, x_n ⟶̇ F(x₀ ⊗ ⋯ ⊗ x_n)\).

\room

\room
A **Cartesian-closed category** is a monoidal category where the tensor
is categorical product and all exponentials exist.
These categories are in correspondence with the models of simply typed
lambda-calculus. If it has all finite sums as well, then it's known as
**bicartesian closed**, in which case products necessarily distribute over sums.

𝒱 is **semicartesian** if any of the following equivalent statements is true.

1.  Unit object \(I\) is terminal; in which case one says 𝒱 is **semicartesian.**
2.  It has a natural ‘deletion’ \(‼_X : X ⟶ I\) with \(‼_I = \Id_I\).
3.  It has natural ‘projections’ \(πᵢ : X₁ ⊗ X₂ ⟶ Xᵢ\) with \(π₁ : I ⊗ I ≅ I : λ˘\).

If in addition it is symmetric with (natural involution) \(σ : X ⊗ Y ⟶ Y ⊗ X\)
and has a natural ‘diagonal’ \(Δ_X : X ⟶ X ⊗ X\)
such that the obvious maps \(X ⟶ X\) coincide
&#x2014; i.e., \(λ ∘ (! ⊗ Id) ∘ Δ = Id = ρ ∘ (Id ⊗ !) ∘ Δ\),
“duplicating data, then deleting a copy, is the same as doing nothing”&#x2014;
then it is necessairly cartesian!

\room

An *exponential for Y* is characterised by the following adjoint isomorphism
that is natural in *Y* and *Z:*

\room

-   Note that ⌊\_⌋ generalises currying, and ⌈\_⌉ generalises uncurrying.
-   The counit \(\eval_Z = ⌈\Id_{Y ➩ z}⌉ : (Y ➩ Z) ⊗ Y → Z\) is called the *evaluation morphism.*

\room
When exponentials always exists, one refers to \(\_{}➩\_{} : 𝒞 × 𝒞^{op} → 𝒞\)
as *the internal hom* and says *(𝒞, ⊗, I, α, λ, ρ, ➩)* is a **closed monoidal category**.

\room
In the cartesian case, the *entire* collection of morphisms \(X → Y\)
is encoded by the *single* object \(X ➩ Y\). That is, \(X → Y \quad≅\quad 1 → (X ➩ Y)\) in 𝒮ℯ𝓉.

\room

\room
More generally, a **closed category** is a category 𝒞 with a bifunctor
\(\_{}➩\_{}\) and two ‘coherent’ transformations as above.

\room

It is common to notate \(X ➩ Y, ⌊f⌋\) by \(Y^X, \transpose{f}\).


<a id="org08ad92a"></a>

# Enrichment & Internal Algebraic Structures

A **Category 𝒳 enriched in a monoidal category 𝒱** or a **𝒱-category**
  is essentially a category but its hom-types are objects of 𝒱.
  Formally, there is a collection `Obj 𝒳` and for each pair `A, B`
  of such ‘objects’ there is a ‘hom-object’ `𝒳(A, B)` in 𝒱,
  and there are two 𝒱-morphisms:

1.  Composition: \(μ_{A, B, C} : 𝒳(B, C) ⊗ 𝒳(A, B) ⟶ 𝒳(A, C)\)
    -   Associativity: The two obvious ways \((𝒳(C, D) ⊗ 𝒳(B, C)) ⊗ 𝒳(A, B) ⟶ 𝒳(A, D)\)
        coincide.
2.  Identities:  \(η_A : I ⟶ 𝒳(A, A)\).
    -   Unity: The obvious maps \(I ⊗ 𝒳(A, B) ⟶ 𝒳(A, B)\) coincide,
        as do the obvious maps \(𝒳(A, B) ⊗ I ⟶ 𝒳(A, B)\).

\room
A usual category is just a 𝒮ℯ𝓉-category.

\room
A *monoid in 𝒱* is an object \(M\) along with two morphisms
\(μ : M ⊗ M ⟶ M, η : I ⟶ M\) such that the former is associative
and has the latter as unit. Notice that monoids *in* 𝒱 are ‘untyped’
analogues of 𝒱-categories. A ‘monad’ is a monoid in a category
of endofunctors with composition as tensor.

-   If M is a monoid in 𝒱 and F : 𝒱 ⟶ 𝒲 is a monoidal functor,
    then F M is a monoid in 𝒲. Woah!

\room
In a monoidal category with natural transformations ‘discard’
\(!_X : X ⟶̇ I\) and ‘duplicate’ \(Δ_X : X ⟶̇ X ⊗ X\),
such as Cartesian monoidal categories, a *group* is like a monoid but with
an additional morphism \(i : M ⟶ M\) such that the inverse axioms
hold; e.g., \(e = x · x^{-1}\) takes the point-free shape
\(η ∘ !_M = μ ∘ (\Id ⊗ i) ∘ Δ\).
In an arbitrary monoidal category, a *Hopf algebra* is like a group
where \(Δ_M\) and \(!_M\) exist for our specific \(M\). These generalise groups.
