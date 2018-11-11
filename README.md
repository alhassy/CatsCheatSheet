<h1> CatsCheatSheet </h1>

This project is to contain a listing of common theorems in elementary category theory.

**The listing sheet, as PDF, can be found [here](https://github.com/alhassy/CatsCheatSheet/blob/master/CheatSheet.pdf)**, 
while below is an unruly html rendition.

This reference sheet is built around the system <https://github.com/alhassy/CheatSheet>


# Table of Contents

1.  [Categories](#org69263f2)
2.  [“Gluing” Morphisms Together](#org829ecfc)
3.  [Functors](#orgb8b4347)
4.  [Naturality](#org05185f6)
5.  [Adjunctions](#orgf3a4eba)
6.  [Constant Combinators](#org4c4a333)
7.  [Monics and Epics](#orgd5bf600)
8.  [Isos](#org4851634)
9.  [Skolemisation](#orgf7013cf)
10. [Initiality](#org2ef1a81)
11. [Colimits](#orge2e4bbc)
12. [Limits](#org77f3ebd)
13. [Sums](#org558d8a1)
14. [Products](#orgc84e29e)
15. [Finitary Sums and Products](#orgb913442)
16. [Mixing products and coproducts](#org4ca9cb9)
17. [Coequaliser](#orgc3f340b)
18. [References](#orge041012)












<a id="org69263f2"></a>

# Categories

A **category** 𝒞 consists of a collection of “objects” \(\Obj\, 𝒞\),
  a collection of  “(homo)morphisms” \(\Hom_𝒞(a,b)\) for any \(a,b : \Obj\,𝒞\)
  &#x2013;also denoted “\(a \,\to_𝒞\, b\)”&#x2013;,
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

Example Categories.

-   Matrices with real number values determine a category whose objects are the natural numbers,
    morphisms \(n → m\) are \(n × m\) matrices, \(\Id\) is the identity matrix, and composition
    is matrix multiplication.
-   Each preorder determines a category: The objects are the elements
    and there is a morphism \(a → b\) named, say, “\((a, b)\)”, precisely when \(a \leq b\);
    composition boils down to transitivity of \(\leq\).
-   Each digraph determines a category: The objects are the nodes
    and the paths are the morphisms typed with their starting and ending node.
    Composition is catenation of paths and identity is the empty path.
-   Suppose we have an \`interface', in the programming sense,
    of constant, function, and relation symbols &#x2013;this is also called a *signature*.
    
    Let 𝒯 be any collection of sentences in the first-order language of signature \(\Sigma\).
    Then we can define a category \(\mathsf{Mod}\,𝒯\) whose objects are
    implementations of interface \(\Sigma\) satisfying constraints 𝒯, and whose morphisms
    are functions that preserve the \(\Sigma\) structure. 
    Ignoring 𝒯, gives us \`functor algebras'.
    
    Particular examples include monoids and structure-preserving maps between them;
    likewise digraphs, posets, rings, etc and their homomorphisms.

\room

Even when morphisms are functions, the objects need not be sets:
Sometimes the objects are *operations* &#x2013;with an appropriate definition
of typing for the functions. The categories of *F*-algebras are an example
of this.

\newpage


<a id="org829ecfc"></a>

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


<a id="orgb8b4347"></a>

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
    structure is observable by categorical means &#x2013;composition, identities, morphisms, typing.
    
    Functors form the tool to deal with “structured” objects
    
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
    a *f* to each “constituent” by using *F f*.

\vspace{1em}

Category \(𝒜lℊ(F)\)

-   For a functor *F : 𝒜 → 𝒟*, this category has *F-algebras*, *F*-ary operations in 𝒟 as, objects
    &#x2013; i.e., objects are 𝒟-arrows \(F\, A → A\) &#x2013;
    and *F*-homomorphisms as morphisms, and it inherits composition and identities from 𝒟.
    
    Note that category axiom \eqref{unique-Type} is not fulfilled since a function can be
    a homomorphism between several distinct operations. However, we pretend it is a category
    in the way discussed earlier, and so the carrier of an algebra is fully determined by
    the operation itself, so that the operation itself can be considered the algebra.
    
    <div class="org-center">
    *\ref{comp-Homomorhism} renders a semantic property as a syntactic condition!*
    </div>

\vspace{1em}

-   A **contravariant functor** 𝒞 → 𝒟 is just a functor *𝒞ᵒᵖ → 𝒟ᵒᵖ*.
-   A **bifunctor** from 𝒞 to 𝒟 is just a functor *𝒞² → 𝒟*.


<a id="org05185f6"></a>

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
\(\bin \, Seq\) the structure of pairs of sequences &#x2013;which is naturally isomorphic
to \(Seq \, \bin\) the structure of sequences of pairs!&#x2013;, and so on.

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

-   If we take \(G = \Id\), then natural transformations \(F →̣ \Id\) are precisely *F*-homomorphisms.
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
consists of functors *𝒞 → 𝒟* as objects and natrual transformations between them as objects.
The identity transformation is indeed an identity for transformation composition, which is associative. 

\room

**Heuristic** To prove \(φ = φ₁ ∘ ⋯ ∘ φₙ : F →̣ G\) is a natural transformation, it suffices
to show that each \(φᵢ\) is a natural transformation.
E.g., without even knowing the definitions, naturality of
*tails = Seq rev ∘ inits ∘ rev* can be proven &#x2013;just type checking!

\iffalse

-   Theorem \eqref{ntrf-Compose} renders proofs of semantic properties to be trivial type checking!
-   E.g., It's trivial to prove *tails = rev ﹔ inits ﹔ Seq rev* is a natural transformation
    by type checking, but to prove the naturality equation by using the naturality equations of
    *rev* and *inits* &#x2013;no definitions required&#x2013; necessitates more writing, and worse: Actual thought!

\fi


<a id="orgf3a4eba"></a>

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
*each L-algebra g is uniquely determined &#x2013;as an L-map followed by an ε-reduce--*
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


<a id="org4c4a333"></a>

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

The following property defines constant functions at the \`pointfree level':

Constant functions force any difference in behaviour for any two
functions to disappear:

Interestingly in 𝒮ℯ𝓉, composition and application
are bridged explicitly by the constant functions:

\newpage


<a id="orgd5bf600"></a>

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


<a id="org4851634"></a>

# Isos

An arrow is an *iso* iff it is invertible; i.e., there is an “inverse” morphism
\(f\inverse\) with
\eqn{inverse-Char}{ f ∘ f\inverse = \Id \landS f\inverse ∘ f = \Id}

To *construct* \(f\inverse\), we begin by identifying its type which may give
insight into its necessary \`shape' &#x2013;e.g., as a sum or a product&#x2013;
then we pick one of these equations and try to reduce it as much as possible
until we arrive at a definition of \(f˘\), or its \`components'.

-   E.g., \(coassocr = [\Id + \inl, \inr ∘ \inr] : (A + B) + C ≅ A + (B + C)\), its inverse
    *coassocl* must be of the shape \([x, [y, z]]\) for unknowns \(x,y,z\) which can be calculated
    by solving the equation \([x, [y, z]] ∘ coassocr = \Id\) &#x2013;Do it!

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


<a id="orgf7013cf"></a>

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
up to unique isomorphism &#x2013;prove it!
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
at most one solution, so together they are equivalent to ℱ-Char &#x2013;however those two proofs
are usually not easier nor more elegant than a proof of ℱ-Char directly.

\room

**Proving ℱ-Char** is straightforwardly accomplished by providing a definition for ℱ
and establishing ℱ-Char &#x2013;these two steps can be done in parallel! Almost every such
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

\newpage


<a id="org2ef1a81"></a>

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


<a id="orge2e4bbc"></a>

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


<a id="org77f3ebd"></a>

# Limits

Dually, the category \(⋀D\) has objects being “cones” \(γ : \const{C} →̣ D\) where \(C =: \src\, γ\)
is a 𝒞-object, and a morphism to \(γ\) *from* \(δ\) is a 𝒞-morphism \(x\) such that \(γ ∘ \const{x} = δ\).
In terms of 𝒞, *\(γ : Obj(⋀ D)\) is a limit for \(D\)* if there is a mapping \(γ╲-\) such that
the following ╲-Type and ╲-Char hold, from which we obtain a host of corollaries.
As usual, there is the implicit well-formedness condition. 

\vspace{-1em}

\newpage


<a id="org558d8a1"></a>

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


<a id="orgc84e29e"></a>

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

\eqn{$\times$-Definition}{ f × g = ⟨ f ∘ \fst, g ∘ \snd ⟩ : A × C → B × D}

\eqn{Projections-Naturality}{ \fst ∘ (f × g) = f ∘ \fst \landS \snd ∘ (f × g) = g ∘ \snd }

\eqn{Extensionality}{ ⟨\fst ∘ h, \snd ∘ h⟩ = h}

\eqn{Absorption}{ (f × g) ∘ ⟨h, j⟩ = ⟨f ∘ h, g ∘ j⟩ }

\eqn{$\times$-BiFunctoriality}{ \Id × \Id = \Id \landS (f × g) ∘ (h × j) = (f ∘ h) × (g ∘ j)}

\eqn{Structural Equality}{ ⟨f,g⟩ = ⟨h, j⟩ \equivS f = h \lands g = j }

\endeqns

\newpage


<a id="orgb913442"></a>

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


<a id="org4ca9cb9"></a>

# Mixing products and coproducts

Any \(f : A + B → C × D\) can be expressed alternatively as an *either*
or as a *split*. It turns out that both formats are identical: 

\vspace{-1.5em}
\eqn{Exchange Rule}{ ⟨[f,g], [h,j]⟩ = [⟨f,h⟩,⟨g,j⟩] }

E.g., \(\mathsf{undistr}  = ⟨[\fst, \fst], \snd + \snd⟩ = [\Id × \inl, \Id × \inr] : (A × B) + (A × C) → A × (B + C)\).

\begineqns

\eqn{Cool-Property}{ [f × g, h × k] \;=\; ⟨ [f, h] ∘ (\fst + \fst), [g, k] ∘ (\snd + \snd)⟩ }

\eqn{Co-cool-Property}{ ⟨f + g, h + k⟩ \;=\; [ ⟨f, h⟩ ; (\inl × \inl), ⟨g, k⟩ ; (\inr × \inr)] }

\endeqns

\room

Also, since constants ignore their inputs,

\newpage


<a id="orgc3f340b"></a>

# Coequaliser

Take \(D\) and \(𝒟\) as suggested by \(D𝒟 = \left( \overset{A}{•} \rightrightarrows^f_g \overset{B}{•} \right)\);
where \(f,g : A → B\) are given. 
Then a cocone δ for \(D\) is a two-member family \(δ = (q', q)\)
with \(q' : A → C, q : B → C, C = \tgt\,\delta\) and \(δ_A ∘ \const{C} h = D h ∘ δ_B\); in-particular
\(q' = f ∘ q = g ∘ q\) whence \(q'\) is fully-determined by \(q\) alone.

Let \(γ = (p', p) : Obj(⋁D)\) be a colimit for \(D\) and write \(-p╱\) in-place of \(-╱γ\), then the ╱-laws
yield: *\(p\) is a coequaliser of \((f,g)\)* if there is a mapping \(-╱p\) such that *CoEq-Type* and
*CoEq-Char* hold.

\vfill

\iffalse

Taking \(D\) and \(\mathcal{D}\) as suggested by
\(D\,\mathcal{D}:\)
$ \raisebox{6pt}{$\spot$}
\overset{ \overset{f}{\text{\tiny$\longrightarrow$}}
  }{ \overset{\longrightarrow}{\text{\tiny$g$}}  }
\raisebox{6pt}{$\spot$}
$

Now call the category \(\bigvee D\) by the name \(\bigvee(f \,|\!|\, g)\):
it has objects morphisms that post-equalise \(f\) and \(g\), and morphisms
\(x : p \to q \equivS x : \tgt p \to \tgt q \lands p \fcmp x \eqs q\) 

A \emph{coequaliser} of \(f,g\) is an initial object in
\(\bigvee(f \,|\!|\, g)\).

\fi


<a id="orge041012"></a>

# References

[A Gentle Introduction to Category Theory ─ the calculational approach](https://maartenfokkinga.github.io/utwente/mmf92b.pdf)
\newline
by [Maarten Fokkinga](https://maartenfokkinga.github.io/utwente/)

\vspace{1em}

An excellent introduction to category theory with examples motivated from programming, in-particular
working with sequences. All steps are shown in a calculational style &#x2013;which Fokkinga
has made [available](https://ctan.org/tex-archive/macros/latex/contrib/calculation) for use with LaTeX&#x2013; thereby making it suitable for self-study.

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

