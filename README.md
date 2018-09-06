<h1> CatsCheatSheet </h1>

This project is to contain a listing of common theorems in elementary category theory.

**The listing sheet, as PDF, can be found [here](https://github.com/alhassy/CheatSheet/blob/master/CatsCheatSheet.pdf)**, while below is a quick-n-dirty html rendition.

This reference sheet is built around the system <https://github.com/alhassy/CheatSheet>

<object width="600" height="400" data="CheatSheet.pdf"></object>

<hr> <hr> <hr>


# Table of Contents

1.  [Categories](#org0691569)
2.  [Functors](#org900cfc3)
3.  [Naturality](#org26e324c)
4.  [∞ Further Reads](#org39bdc24)












<a id="org0691569"></a>

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


<a id="org900cfc3"></a>

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


<a id="org26e324c"></a>

# Naturality

A natural transformation is nothing but a structure preserving map between functors.
“Structure preservation” makes sense, here, since we've seen already that a functor
is, or represents, a structure that objects might have.


<a id="org39bdc24"></a>

# ∞ Further Reads

-   Roland Backhouse
-   Grant Malcolm
-   Lambert Meertens
-   Jaap van der Woude

\newpage

