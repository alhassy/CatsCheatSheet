<h1> CatsCheatSheet </h1>

This project is to contain a listing of common theorems in elementary category theory.

**The listing sheet, as PDF, can be found [here](https://github.com/alhassy/CatsCheatSheet/blob/master/CheatSheet.pdf)**, while below is a quick-n-dirty html rendition.

This reference sheet is built around the system <https://github.com/alhassy/CheatSheet>

<object width="600" height="400" data="CheatSheet.pdf"></object>

<hr> <hr> <hr>


# Table of Contents

1.  [Categories](#org17d7f98)
2.  [Functors](#orgedb080a)
3.  [Naturality](#orgc68e019)
4.  [Adjunctions](#orgd825596)
5.  [More](#orga1470f5)
6.  [∞ Further Reads](#org7d0dd5d)













<a id="org17d7f98"></a>

# Categories

A **category** 𝒞 consists of a collection of “objects” `Obj 𝒞,` a collection of
  “morphisms” `Mor 𝒞`, an operation `Id` associating a morphism `Idₐ : a → a` to each object `a`,
  a parallel pair of functions `src, tgt : Mor 𝒞 → Obj 𝒞`, and a “composition”
  operation `_﹔_ : ∀{A B C : Obj} → (A → B) → (B → C) → (A → C)`
  where for objects `X` and `Y` we define the *type* `X → Y`
  as follows

\begin{flalign*}
    f : X \to Y \quad\equiv\quad \mathsf{src}\; f = X \;\land\; \mathsf{tgt}\; f = Y 
   &&
   \tag*{defn-Type}
   \label{defn-Type}
\end{flalign*}

Moreover composition is required to be associative with `Id` as identity.

Instead of `src` and `tgt` we can instead assume primitive a ternary relation
`_:_→_` and regain the operations precisely when the relation is functional
in its last two arguments:
\eqn{unique-Type}{f : A \to B \;\land\; f : A' \to B' \;\implies\; A=A' \;\land\; B=B'}
When this condition is dropped, we obtain a *pre-category*; e.g., the familiar *Sets*
is a pre-category that is usually treated as a category by making morphisms
contain the information about their source and target: `(A, f, B) : A → B`
rather than just `f`. *This is sometimes easier to give, then src and tgt! C.f. Alg(F).*

\vspace{1em}

A categorical statement is an expression built from notations for objects,
typing, morphisms, composition, and identities by means of the usual logical
connectives and quantifications and equality.

\vspace{1em}

Even when morphisms are functions, the objects need not be sets:
Sometimes the objects are *operations* &#x2013;with an appropriate definition
of typing for the functions. The categories of F-algebras are an example
of this.

\vspace{1em}

Example Categories.

-   Each digraph determines a category: The objects are the nodes
    and the paths are the morphisms typed with their starting and ending node.
    Composition is catenation of paths and identity is the empty path.
-   Each preorder determines a category: The objects are the elements
    and there is a morphism `a → b` named, say, `(a, b),` precisely when \(a ≤ b\).


<a id="orgedb080a"></a>

# Functors

A **functor** *F : 𝒜 → ℬ* is a pair of mappings, denoted by one name,
from the objects, and morphisms, of 𝒜 to those of ℬ such that
it respects the categorical structure:

\vspace{1em}

The two axioms are equivalent to the single statement that 
*functors distribute over finite compositions, with \(\Id\) being the empty composition*
\[ F(f ﹔ \cdots ﹔ g) \;=\; F\, f ﹔ \cdots ﹔ F\, g \]

Use of Functors.

-   In the definition of a category, “objects” are “just things” for which no internal
    structure is observable by categorical means &#x2013;composition, identities, morphisms, typing.
    
    Functors form the tool to deal with “structured” objects
    
    Indeed in 𝒮ℯ𝓉 the aspect of a structure is that it has “constituents”, and that it is possible
    to apply a function to all the individual constituents; this is done by
    *F f : F A → F B*.

-   For example, let *𝑰 A = A × A* and *𝑰 f = (x, y) ↦ (f x, f y).*
    So 𝑰 is or represents the structure of pairs; *𝑰 A* is the set of pairs of *A*,
    and *𝑰 f* is the function that applies *f* to each constituent of a pair.
    -   A *binary operation on A* is then just a function *𝑰 A → A;*
        in the same sense we obtain “F-ary operations”.

-   Also, *Seq* is or represents the structure of sequences; *Seq A* is the structure of sequences
    over *A*, and *Seq f* is the function that applies *f* to each constituent of a sequence.

-   Even though *F A* is still just an object, a thing with no observable internal structure, the
    functor properties enable to exploit the “structure” of *F A* by allowing us to “apply”
    a *f* to each “constituent” by using *F f*.

\vspace{1em}

Category \(𝒜lℊ(F)\)

-   For a functor *F : 𝒜 → 𝒟*, this category has “F-algebras”, F-ary operations in 𝒟 as, objects
    &#x2013; i.e., objects are 𝒟-arrows \(F\, A → A\) &#x2013;
    and *F*-homomorphisms as morphisms, and it inherits composition and identities from 𝒟.
    
    Note that category axiom \eqref{unique-Type} is not fulfilled since a function can be
    a homomorphism between several distinct operations. However, we pretend it is a category
    in the way discussed earlier, and so the carrier of an algebra is fully determined by
    the operation itself, so that the operation itself can be considered the algebra.
    
    <div class="org-center">
    *Theorem \eqref{comp-Homomorhism} renders a semantic property as a syntactic condition!*
    </div>

\vspace{1em}

-   A **contravariant functor** 𝒞 → 𝒟 is just a functor *𝒞ᵒᵖ → 𝒟ᵒᵖ*.
-   A **bifunctor** from 𝒞 to 𝒟 is just a functor *𝒞² → 𝒟*.


<a id="orgc68e019"></a>

# Naturality

A natural transformation is nothing but a structure preserving map between functors.
“Structure preservation” makes sense, here, since we've seen already that a functor
is, or represents, a structure that objects might have.

\vspace{1em}

As discussed before for the case *F : 𝒞 → 𝒮ℯ𝓉*, each *F A* denotes a structured set
and *F* denotes the structure itself.

\vspace{1em}

For example, 𝑰 is the structure of pairs, *Seq* is the structure of sequences,
*𝑰 Seq* the structure of pairs of sequences, *Seq Seq* the structure of sequences of
sequences, and so on.

\vspace{1em}

A “transformation” from structure *F* to structure *G* is a family of functions
*η : ∀{A} → F A → G A*; and it is “natural” if each *ηₐ* doesn't affect the *constituents*
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

\vspace{1em}

-   One also says *ηₐ is natural in* its parameter *a*.

-   If we take \(G = \Id\), then natural transformations \(F →̣ \Id\) are precisely *F*-homomorphisms.
-   Indeed, a natural transformation is a sort-of homomorphism in that the image of a morphism
    after reshaping is the same as the reshaping of the image.

\vspace{1em}

Example natrual transformations

-   *rev : Seq →̣ Seq : [a₁, …, aₙ] ↦ [aₙ, …, a₁]*
    reverses its argument thereby reshaping a sequence structure into a sequence structure without affecting the constituents.

-   *inits : Seq →̣ Seq Seq : [a₁, …, aₙ] ↦ [[], [a₁], ⋯, [a₁, …, aₙ]]*
    yields all initial parts of its argument
    thereby reshaping a sequence structure into a sequence of sequences structure, not affecting
    the constituents of its argument.

\vspace{1em}

\vspace{1em}

**Category ℱ𝓊𝓃𝒸(𝒞, 𝒟)**
consists of functors *𝒞 → 𝒟* as objects and natrual transformations between them as objects.
The identity transformation is indeed an identity for transformation composition, which is associative. 

\vspace{1em}

**Heuristic** To prove \(φ = φ₁ ﹔ ⋯ ﹔ φₙ : F →̣ G\) is a natural transformation, it suffices
to show that each \(φᵢ\) is a natural transformation.

-   Theorem \eqref{ntrf-Compose} renders proofs of semantic properties to be trivial type checking!
-   E.g., It's trivial to prove *tails = rev ﹔ inits ﹔ Seq rev* is a natural transformation
    by type checking, but to prove the naturality equation by using the naturality equations of
    *rev* and *inits* &#x2013;no definitions required&#x2013; necessitates more writing, and worse: Actual thought!


<a id="orgd825596"></a>

# Adjunctions

An adjunction is a particular one-one correspondence between different kinds of
morphisms in different categories.

\vspace{1em}

An **adjunction** consists of two functors \(L : 𝒜 → ℬ\) and \(R : ℬ → 𝒜\),
as well as two (not necessarily natural!) transformations
\(η : \Id → RL\) and \(ε : LR → \Id\) such that

\vspace{-1em}

Reading right-to-left: In the equation \(L f ﹔ ε_B = g\) there is a unique solution to the unknown \(f\).
Dually for the other direction.

\vspace{1em}

That is,
*each L-algebra g is uniquely determined &#x2013;as an L-map followed by an ε-reduce--*
*by its restriction to the adjunction's unit η.*

\vspace{1em}

A famous example is “Free ⊣ Forgetful”, e.g. to *define* lists for which the above
becomes: Homomorphisms on lists are uniquely determined, as a map followed by a reduce,
by its restriction to the singleton sequences.

\vspace{1em}

We may call \(f\) the restriction, or lowering, of \(g\) to the “unital case”
and write \(f = ⌊g⌋ = η_A ﹔ R g\). Also, we may call \(g\) the extension, or raising,
of \(f\) to an *L*-homomorphism and write \(g = ⌈f⌉ = L f ﹔ ε_B\). The above equivalence
now reads:

\vspace{1em}

Note that ⌈ is like \`r' and the argument to ⌈⌉ must involve the *R*-ight adjoint in its type;

{\textbf L}ad takes morphisms involving the {\textbf L}eft adjoint ;)

\vspace{1em}

This equivalence expresses that \`lad' \(⌊⌋\), from \emph{l}eft \emph{ad}jungate,
and \`rad' \(⌈⌉\), from \emph{r}ight \emph{ad}jungate, are each other's inverses
and constitute a correspondence between certain morphisms.
*Being a bijective pair, lad and rad are injective, surjective, and undo one another.*

\vspace{1em}

We may think of ℬ as having all complicated problems so we abstract
away some difficulties by \emph{r}aising up to a cleaner, simpler, domain
via rad ⌈⌉; we then solve our problem there, then go back \emph{down} to
the more complicated concrete issue via ⌊⌋, lad.
( E.g., ℬ is the category of monoids, and 𝒜 is the category of sets; L is list functor. )

(“zig-zag laws”) The unit has a post-inverse while the counit has a pre-inverse:

Also,

-   Left adjoints preserve colimits such as initial objects and sums.
-   Right adjoints preserve limits such as terminal objects and products.


<a id="orga1470f5"></a>

# More

Nice Stuff ⌣̈ 


<a id="org7d0dd5d"></a>

# ∞ Further Reads

-   Roland Backhouse
-   Grant Malcolm
-   Lambert Meertens
-   Jaap van der Woude

-   *Adjunctions* by Fokkinga and Meertens

\newpage

