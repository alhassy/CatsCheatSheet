#+TITLE: Graphs are to categories as lists are to monoids
#+DATE: 2018-12-24
#+AUTHOR: Musa Al-hassy
#+EMAIL: alhassy@gmail.com
#+DESCRIPTION: A fast-paced introduction to Category Theory based on the notion of graphs.
#+DESCRIPTION: Claims are proven in the Haskell-like proof assistant Agda.
#+STARTUP: indent
#+CATEGORIES: CategoryTheory
#+OPTIONS: html-postamble:nil toc:nil d:nil
#+IMAGE: ../assets/img/PathCat.png
#+SOURCE: https://raw.githubusercontent.com/alhassy/CatsCheatSheet/master/PathCat.lagda

#+INCLUDE: ~/alhassy.github.io/content/MathJaxPreamble.org

# Begin server
#
# cd ~/alhassy.github.io/ ; bundle exec jekyll serve
#
# (preview-article)

* Abstract                                                           :ignore:
#+BEGIN_CENTER
*Abstract*
#+END_CENTER
Numbers are the lengths of lists which are the flattenings of trees which are
the spannings of graphs.
Unlike the first three, graphs have /two/ underlying types of interest
--the vertices and the edges-- and it is getting to grips with this complexity
that we attempt to tackle by considering their ‘algebraic’ counterpart: Categories.

# trees are just those graphs for which arbitrary points are connected by a unique undirected path.

In our exploration of what graphs could possibly be and their relationships to lists are,
we shall /mechanise,/ or /implement,/ our claims since there will be many details and it is easy
to make mistakes --moreover as a self-learning project, I'd feel more confident to make
*bold* claims when I have a proof assistant checking my work ;-)

Assuming slight familiarity with the Agda programming language, we motivate the need for
basic concepts of category theory with the aim of discussing adjunctions with
a running example of a detailed construction and proof of a free functor.
Moreover, the article contains a host of ~exercises~ whose solutions can be found in the
literate source file. Raw Agda code can be found [[https://github.com/alhassy/CatsCheatSheet/blob/master/PathCat.agda][here.]]

Since the read time for this article is more than two hours, excluding the interspersed
exercises, it may help to occasionally consult a [[https://github.com/alhassy/CatsCheatSheet/blob/master/CheatSheet.pdf][Reference Sheet For Elementary Category Theory]].

Coming from a background in order theory, I love Galois Connections and so
our categorical hammer will not be terminal objects nor limits, but rather adjunctions.
As such, /everything is an adjunction/ is an apt slogan for us :-)

# ?universal algebra: signatures, graphs, monoids, cats

# ?However, similar to nearly everything else in this document, we can leave the setoid-approach as an exercises
# for the reader, which of course has solutions being in the literate source.

# ?instance resolution, difference from typeclass, look at tp.

#
# The approach taken here is to motivate categories from posets and the main
# tools used there are indirect reasoning (yoneda) and galois connections (adjunctions).

# \tableofcontents

#+BEGIN_SRC :tangle "PathCat.agda" 
-- This file has been extracted from https://alhassy.github.io/PathCat/
-- Type checks with Agda version 2.6.0.
#+END_SRC
* Photograph Credit                                                  :ignore:

#+LaTeX: \iffalse
#+HTML: <small> <center>
( Photo by
[[https://unsplash.com/@miklevasilyev][Mikhail Vasilyev]]
on [[https://unsplash.com/][Unsplash]] )
#+HTML: </center> </small>
#+LaTeX: \fi

# "Download free do whatever you want high-resolution photos from Unsplash."

* Introduction
:PROPERTIES:
:header-args: :tangle "PathCat.agda" 
:END:

** Motivation                                                       :ignore:

Lists give free monoids $ℒ\, A = (\List\, A, +\!+, [])$
---a monoid $𝒮 = (S, ⊕, 0_⊕)$ is a triple consisting of a set $S$ with a binary operation 
$⊕$ on it that is associative and has a unit, $0_⊕$.
That it is ‘free’ means that to define a structure-preserving map between monoids
$(\List\, A, +\!+, []) \,⟶\, (S, ⊕, 0_⊕)$ it suffices to only provide a map between their
carriers $\List\, A → S$ ---freedom means that plain old maps between types freely,
at no cost or effort, give rise to maps that preserve monoid structure.
Moreover, the converse also holds and in-fact we have a bijection:
\[
  (ℒ\, A ⟶ 𝒮) \qquad≅\qquad (A ⟶ 𝒰\, 𝒮)
\]
Where we write $𝒰\, (S, ⊕, 0_⊕) = S$ for the operation that gives us the 𝒰nderlying carrier
of a monoid.

Loosely put, one says we have an ‘adjunction’, written $ℒ ⊣ 𝒰$.

Observe that natural numbers ~ℕ ≅ List Unit~ are a monoid whose operation is commutative.
By using different kinds of elements ~A~ --and, importantly, still not imposing any equations--
we lose commutativity with ~List A~.
Then by generalising further to binary trees ~BinTree A~, we lose associtivity and identity
are are only left with a set and an operation on it ---a structure called a ‘magma’.

This is the order that one usually learns about these inductively built structures.
One might be curious as to what the next step up is in this hierarchy of generalisations.
It is a non-inductive type called a ‘graph’ and in this note we investigate them by
comparison to lists.
Just as we shifted structures in the hierarchy, we will
move to a setting called a ‘category’ ---such are more structured than magmas
but less restrictive than monoids.

For those who know category theory, this article essentially formalises the
often seen phrase “consider the category generated by this diagram, or graph”.
Indeed every category is essentially a free category over a graph but with
additional equations that ‘confuse’ two paths thereby declaring, e.g., that
one edge is the composition of two other edges.

** Imports
:PROPERTIES:
:UNNUMBERED: t
:END:

In our exploration of what graphs could possibly be and their relationships to lists are,
we shall /mechanise/ or /implement/ our claims since there will be many details and it is easy
to make mistakes --moreover as a self-learning project, I'd feel more confident to make
*bold* claims when I have a proof assistant checking my work ;-)

Before reading any further please ingrain into your mind that the Agda keyword
~Set~ is read “type”! This disparity is a historical accident.

Since the Agda prelude is so simple, the core language doesn’t even come with Booleans or numbers by default
---they must be imported from the standard library. This is a pleasant feature.
As a result, Agda code tends to begin with a host of imports.

#+BEGIN_SRC agda
module PathCat where

open import Level using (Level) renaming (zero to ℓ₀ ; suc to ℓsuc ; _⊔_ to _⊍_)

-- Numbers
open import Data.Fin
  using (Fin ; toℕ ; fromℕ ; fromℕ≤ ; reduce≥ ; inject≤)
  renaming (_<_ to _f<_ ; zero to fzero ; suc to fsuc)
open import Data.Nat
open import Relation.Binary using (module DecTotalOrder)
open import Data.Nat.Properties using(≤-decTotalOrder ; ≤-refl)
open DecTotalOrder Data.Nat.Properties.≤-decTotalOrder

-- Z-notation for sums
open import Data.Product using (Σ ; proj₁ ; proj₂ ; _×_ ; _,_)
Σ∶• : {a b : Level} (A : Set a) (B : A → Set b) → Set (a ⊍ b)
Σ∶• = Σ
infix -666 Σ∶•
syntax Σ∶• A (λ x → B) = Σ x ∶ A • B

-- Equalities
open import Relation.Binary.PropositionalEquality using (_≗_ ; _≡_)
  renaming (sym to ≡-sym ; refl to ≡-refl ; trans to _⟨≡≡⟩_ 
           ; cong to ≡-cong ; cong₂ to ≡-cong₂ 
           ; subst to ≡-subst ; subst₂ to ≡-subst₂ ; setoid to ≡-setoid)
#+END_SRC

Notice that we renamed transitivity to be an infix combinator.

Let us make equational-style proofs available for any type.
#+BEGIN_SRC agda
module _ {i} {S : Set i} where
    open import Relation.Binary.EqReasoning (≡-setoid S) public
#+END_SRC

We intend our proofs to be sequences of formulae interleaved with
justifications for how the formulae are related. At times, the justifications
are by definition and so may be omitted, but we may want to mention them
for presentational --pedagogical?-- purposes. Hence, we introduce the
combinator notation ~lhs ≡⟨" by definition of something "⟩′ rhs~.
# --note that this combinator is intended to only be used in calculations.

#+BEGIN_SRC agda
open import Agda.Builtin.String

defn-chasing : ∀ {i} {A : Set i} (x : A) → String → A → A
defn-chasing x reason supposedly-x-again = supposedly-x-again

syntax defn-chasing x reason xish = x ≡⟨ reason ⟩′ xish

infixl 3 defn-chasing
#+END_SRC

While we’re making synonyms for readability, let’s make another:
#+BEGIN_SRC agda
_even-under_ : ∀ {a b} {A : Set a} {B : Set b} {x y} → x ≡ y → (f : A → B) → f x ≡ f y 
_even-under_ = λ eq f → ≡-cong f eq
#+END_SRC

Example usage would be to prove
~mor G (mor F Id) ≡ mor G Id~ directly by ~≡-cong (mor G) (id F)~ 
which can be written more clearly as
~functor F preserves-identities even-under (mor G)~, 
while longer it is also much clearer and easier to read and understand
--self-documenting in some sense.

Interestingly, our first calculational proof is in section 5 when
we introduced an large 𝒞𝒶𝓉egory.

* /Graph me to the moon!/
:PROPERTIES:
:header-args: :tangle "PathCat.agda" 
:END:

#+BEGIN_CENTER
/What's a graph? Let's motivate categories!/
#+END_CENTER

** Intro                                                            :ignore:
A ‘graph’ is just a parallel-pair of maps,
#+BEGIN_SRC agda
record Graph₀ : Set₁ where
  field
    V   : Set
    E   : Set
    src : E → V
    tgt : E → V
#+END_SRC
This of-course captures the usual notion of a set of nodes ~V~ and a set of directed and labelled
edges ~E~ where an edge ~e~ begins at ~src e~ and concludes at ~tgt e~.

What is good about this definition is that it can be phrased in any category: ~V~ and ~E~ are
any two objects and ~src, tgt~ are a parallel pair of morphisms between them.
How wonderful! We can study the notion of graphs in arbitrary categories!
---This idea will be made clearer when categories and functors are formally introduced.

However, the notion of structure-preserving map between graphs, or ‘graph-maps’ for short,
then becomes:

#+BEGIN_SRC agda
record _𝒢⟶₀_ (G H : Graph₀) : Set₁ where
  open Graph₀
  field
    vertex : V(G) → V(H)
    edge   : E(G) → E(H)
    src-preservation : ∀ e → src(H) (edge e) ≡  vertex (src(G) e)
    tgt-preservation : ∀ e → tgt(H) (edge e) ≡  vertex (tgt(G) e)
#+END_SRC
( The fancy 𝒢 and ⟶ are obtained in Agda input mode by ~\McG~ and ~\-->~, respectively. )

This is a bit problematic in that we have two proof obligations and at a first glance it is not
at all clear their motivation besides ‘‘structure-preserving’’.

However, our aim is in graphs in usual type theory, and as such we can use a definition that is
equivalent in this domain: A graph is a
type ~V~ of vertices and a ‘type’ ~v ⟶ v’~ of edges for each pair of vertices ~v~ and ~v’~.
#+BEGIN_SRC agda
-- ‘small graphs’ , since we are not using levels
record Graph : Set₁ where
  field
    V    : Set
    _⟶_ : V → V → Set

-- i.e., Graph ≈ Σ V ∶ Set • (V → V)
-- Graphs are a dependent type!
#+END_SRC

Now the notion of graph-map, and the meaning of structure-preserving, come to the forefront:

#+BEGIN_SRC agda
record GraphMap (G H : Graph) : Set₁ where    
    private
      open Graph using (V)
      _⟶g_ = Graph._⟶_ G
      _⟶h_ = Graph._⟶_ H
    field
      ver  : V(G) → V(H)                                -- vertex morphism
      edge : {x y : V(G)} → (x ⟶g y) → (ver x ⟶h ver y) -- arrow preservation

open GraphMap
#+END_SRC

Note ~edge~ essentially says that ~mor~ ‘shifts’, or ‘translates’, types
~x ⟶g y~ into types ~ver x ⟶h ver y~.

While equivalent, this two-piece definition is preferable over the four-piece one given
earlier since it means less proof-obligations and less constructions in general, but the same
expressiblity. Yay!

Before we move on, let us give an example of a simple chain-graph.
For clarity, we present it in both variations.
#+BEGIN_SRC agda
-- embedding: j < n ⇒ j < suc n
`_ : ∀{n} → Fin n → Fin (suc n)
` j = inject≤ j (≤-step ≤-refl) where open import Data.Nat.Properties using (≤-step)
#+END_SRC
This' an example of a ‘forgetful functor’, keep reading!

#+BEGIN_SRC agda
[_]₀ : ℕ → Graph₀
[ n ]₀ = record 
    { V = Fin (suc n)                  -- ≈ {0, 1, ..., n - 1, n}
    ; E = Fin n                        -- ≈ {0, 1, ..., n - 1}
    ; src = λ j → ` j
    ; tgt = λ j → fsuc j
    }
#+END_SRC
That is, we have ~n+1~ vertices named ~0, 1, …, n~ and ~n~ edges named ~0, 1, …, n-1~
with one typing axiom being ~j : j ⟶ (j+1)~. Alternatively,

#+BEGIN_SRC agda
[_] : ℕ → Graph
[ n ] = record {V = Fin (suc n) ; _⟶_ = λ x y → fsuc x ≡ ` y }
#+END_SRC

** Types Require Casting
However, we must admit that a slight downside of the typed approach
--the two-piece definition-- is now
we may need to use the following ‘shifting’ combinators: 
They shift, or slide, the edge types.

#+BEGIN_EXAMPLE
-- casting
_⟫_ : ∀{x y y’} →  (x ⟶ y) → (y ≡ y’) → (x ⟶ y’)
e ⟫ ≡-refl = e

-- Casting leaves the edge the same, only type information changes
≅-⟫ : ∀{x y y’} {e : x ⟶ y} (y≈y’ : y ≡ y’) → e ≅ (e ⟫ y≈y’)
≅-⟫ ≡-refl = ≅-refl
#+END_EXAMPLE

Such is the cost of using a typed-approach.

Even worse, if we use homogeneous equality then we’d have the ghastly operator
#+BEGIN_EXAMPLE
≡-⟫ : ∀{x y y’} {e : x ⟶ y} (y≈y’ : y ≡ y’) → e ⟫ y≈y’ ≡ (≡-subst (λ ω → x ⟶ ω) y≈y’ e)
#+END_EXAMPLE

However, it seems that our development does not even make use of these.
Lucky us! However, it is something to be aware of.

** Signatures

A /signature/ consists of ‘sort symbols’ and ‘function symbols’ each of which is associated source-sorts
and a target-sort --essentially it is an interface in the programming sense of the word thereby providing
a lexicon for a language.
A /model/ or /algebra/ of a language is an interpretation of the sort symbols as sets and an interpretation of the
function symbols as functions between those sets; i.e., it is an /implementation/ in programming terms.
Later you may note that instead of sets and functions we may use the objects and morphisms of
a fixed category instead, and so get a model in that category.

#+BEGIN_CENTER
| _Math_           | ≅ | _Coding_                             |
| Signature      |   | Interface, record type, class      |
| Algebra        |   | Implementation, instance, object   |
| Language Term  |   | Syntax                             |
| Interpretation |   | Semantics, i.e., an implementation |
#+END_CENTER

Formally, one-sorted signatures are defined:
#+BEGIN_SRC agda
open import Data.Vec 
  using (Vec) 
  renaming (_∷_ to _,,_ ; [] to nil) -- , already in use for products :/
  
-- one sorted
record Signature : Set where
    field
     𝒩 : ℕ        -- How many function symbols there are
     ar : Vec ℕ 𝒩 -- Their arities: lookup i ar == arity of i-th function symbol

open Signature ⦃...⦄ -- 𝒩 now refers to the number of function symbols in a signature
#+END_SRC

For example, the signature of monoids consists of a single sort symbol ~C~ --which can be
interpreted as the carrier of the monoid-- and two function symbols ~m , u~
--which can be interpreted as the monoid multiplication and unit-- with source-target
sort lists ~((),C) , ((C,C), C)~ ---some would notate this by ~u :→ C , m : C × C → C~.
#+BEGIN_SRC agda
MonSig : Signature
MonSig = record { 𝒩 = 2 ; ar = 0 ,, 2 ,, nil }
-- unit u : X⁰ → X and multiplication m : X² → X
#+END_SRC

Generalising on monoids by typing the multiplication we obtain
the signature of categories which consists of three sort symbols ~O, A, C~ --which can be
interepreted as objects, arrows, and composable pairs of arrows-- and four function symbols
~⨾ , src, tgt, id~ with source-target sort lists ~(C,A) , (A,O) , (A,O) , (O,A)~
---notice that only a language of symbols
has been declared without any properties besides those of typing. If we discard ~C, ⨾, id~ we
then obtain the signature of graphs. Without knowing what categories are, we have seen that their
signatures are similar to both the graph and monoid signatures and so expect their logics to
also be similar. Moreover we now have a few slogans,
\[\color{green}{\text{Categories are precisely typed monoids!}}\]
\[\color{green}{\text{Categories are precisely graphs with a monoidal structure!}}\]
\[\color{green}{\text{Categories are precisely coherently constructive lattices!}}\]

( The last one is completely unmotivated from our discussion, but it's a good place for the slogan and
  will be touched on when we look at examples of categories. )

A signature can be visualised in the plane by associating a dot for each sort symbol and an arrow
for each function symbol such that the arrow has a tail from each sort in the associated function
symbols source sorts list and the end of the arrow is the target sort of the sort symbol.
That is, a signature can be visualised as a hyper-graph.

+ A signature whose function symbols each have only one sort symbol for source-sorts is called a
  ‘graph signature’ since it corresponds to ---or can be visualised as--- a graph.

+ Then a model of a graph (signature) ~𝒢~ is an interpreation/realisation of the graph’s vertices
  as sets and the graph’s edges as functions between said sets.

+  A model of ~𝒢~ is nothing more than a graph morphism
   ~𝒢 ⟶ 𝒮e𝓉~, where ~𝒮e𝓉~ is the graph with vertices being sets and edges being functions.

Notice that a ~Graph₀~ is precisely a model of the graph ~• ⇉ •~, which consists of 
two vertices and two edges from the first vertex to the second vertex. 
We will return to this point ;-)

Before we move on, it is important to note that a signature does not capture any
constraints required on the symbols --e.g., a monoid is the monoid signature as well
as the constraint that the 2-arity operation is associative and the 0-arity operation is its unit.
More generally, a /specification/ consists of a signature declaring symbols of interest,
along with a set of sentences over it that denote axioms or constraints.
In programming parlance, this is an interface consisting of types and functions
that need to be provided and implemented, along with constraints that are usually documented in comments.
Unsurprisingly, models of specifications also form categories.

* /Cats but no alligators/
:PROPERTIES:
:header-args: :tangle "PathCat.agda" 
:END:

# Category and functor defns
# {A poor-man’s definition of Category}

In this section we introduce the notion of a ‘‘poor-man’s category’’ along with the notion of
structure preserving transformations and structure preserving transformations between such
transformations. The former are called /functors/ and the latter are known as /natural transformations/
and are considered one of the most important pieces of the fundamentals of category theory; 
as such, we discuss them at length. 
Afterwards, we relate this section back to our motivating discussion of graphs.

** Strict Categories
A category, like a monoid, is a a few types and operations for which some equations hold.
However, to discuss equations a notion of equality is needed and rather than enforce one
outright it is best to let it be given. This is a ‘set’ in constructive mathematics:
A type with an ~E~-quivalence relation on it ---also called a /setoid/ or an ~E~-set.
However, then the structure must have a few added axioms: The operations must be congruences,
i.e., preserve the equivalence relation, and structure-preserving maps must also be congruences.

For our purposes we will use propositional equality and point-wise propositional equality,
and as such most of the proofs fall out of the fact that propositional equality is an equivalence.
However, this setoid structure becomes a bit of a noise, without providing any real insight for our uses, 
and the issues of equivalences will be a distraction from the prime focus. 
Instead, for our two cases where we use point-wise propositional,
we will postulate two forms of extensionality. Without question this is not a general approach
---then again, our aim is not to develope a library for category theory, which has already been
done so elegantly by Kahl who calls it the [[http://relmics.mcmaster.ca/RATH-Agda/RATH-Agda-2.0.0.pdf][RATH-Agda]] project.

#+BEGIN_SRC agda
module _ where -- An anyonomous module for categorial definitions
    
 record Category {i j : Level} : Set (ℓsuc (i ⊍ j)) where
  infixr 10 _⨾_
  field
    Obj      : Set i
    _⟶_     : Obj → Obj → Set j
    _⨾_      : ∀ {A B C : Obj} → A ⟶ B → B ⟶ C → A ⟶ C
    assoc    : ∀ {A B C D} {f : A ⟶ B}{g : B ⟶ C} {h : C ⟶ D} → (f ⨾ g) ⨾ h ≡ f ⨾ (g ⨾ h)
    Id       : ∀ {A : Obj} → A ⟶ A
    leftId   : ∀ {A B : Obj} {f : A ⟶ B} → Id ⨾ f ≡ f
    rightId  : ∀ {A B : Obj} {f : A ⟶ B} → f ⨾ Id ≡ f

 open Category using (Obj)
 open Category ⦃...⦄ hiding (Obj)

 -- Some sugar for times when we must specify the category
 -- “colons associate to the right” ;-)
 
 arr = Category._⟶_ 
 syntax arr 𝒞 x y  =  x ⟶ y ∶ 𝒞    -- “ghost colon”

 cmp = Category._⨾_
 syntax cmp 𝒞 f g  =  f ⨾ g ∶ 𝒞    -- “ghost colon”
#+END_SRC

However, similar to nearly everything else in this document, we can leave the setoid-approach as an excercise
for the reader, which of course has solutions being in the literate source.
#
# I've moved the setoid-based theory to an appendix at the end, 
# it seems I must enforce setoid structure at the outset
# and I really do not think it is worth it for my intended purposes; moreover, 
# it adds noise to the presentation without giving enough insight.

Moreover, lest you’re not convinced that my usage of extensionality is at all acceptable,
then note that others have used it to simplify their presentations; e.g.,
[[http://cs.ioc.ee/~tarmo/papers/jfr14.pdf][Relative monads formalised]].
Such ‘appeal to authority’ is for the lazy reader who dares not think for him- or her-self,
otherwise one ought to read up on the [[https://ncatlab.org/nlab/show/principle+of+equivalence][evils]]
of using equality instead of equivalence relations so as to understand
[[http://www.math.harvard.edu/~mazur/preprints/when_is_one.pdf][when one thing is really another]].

The diligent reader may be interest to know that Maarten Fokkinga has written a very
[[http://maartenfokkinga.github.io/utwente/mmf92b.pdf][gentle introduction to category theory using the calculational approach]]; I highly recommend it!

Anyhow, in place of strict equality, one uses categorical isomorphism instead.
#+BEGIN_SRC agda
 open Category using (Obj) public
 
 record Iso {i} {j} (𝒞 : Category {i} {j}) (A B : Obj 𝒞) : Set j where
   private instance 𝒞′ : Category ; 𝒞′ = 𝒞
   field
     to   : A ⟶ B
     from : B ⟶ A
     lid  : to ⨾ from ≡ Id
     rid  : from ⨾ to ≡ Id
     
 syntax Iso 𝒞 A B = A ≅ B within 𝒞
#+END_SRC

Interestingly, we shall later encounter a rather large category named
𝒞𝒶𝓉 possessing the special property of being a [[https://ncatlab.org/nlab/show/2-category][“2-Category”]]: 
It has morphisms between objects, as expected, which are now called “1-morphism”,
and it has morphisms between 1-morphisms, also called 2-morphisms.

That is, it has morphisms between morphisms.

Above we argued that equality should be deferred in favour of isomorphism
at the morphism level. Hence, in a 2-Category, it is only reasonable to defer
an equation involving 1-morphisms to be up to isomorphism of 2-morphisms
---this is then called an “equivalence”.
#+BEGIN_EXAMPLE
ℒHS ≃ ℛHS  ⇔  Σ F ∶ ℒHS ⟶ ℛHS • Σ G ∶ ℛHS ⟶ ℒHS • F ⨾ G ≅ G ⨾ F ≅ Id
#+END_EXAMPLE

Hence when it comes to categories themselves, one usually speaks in terms of 
equivalences rather than isomorphisms.

# E.g., ~𝒮e𝓉 ^ S ≃ 𝒮e𝓉 / S~, where ~S~ is construed as a discrete category 
# on the lhs but a set on the rhs.

# also :: every category is equivalent to a skeletal subcategory

For example, let 𝒫𝒶𝓇 be the supercategory of 𝒮e𝓉 with morphisms being 
‘partial functions’ ~(A ⟶ B) = (A → B + 𝟙)~ where the extra element of
 ~𝟙 = { * }~ represents ‘undefined’
---also known as the ~Partial~, ~Option~, or ~Maybe~ monads.
Moreover, let 𝒫𝒮ℯ𝓉 be the category of sets with an elected point.
Then, ~𝒫𝒶𝓇 ≃ 𝒫𝒮e𝓉~ is witnessed by ~(A ⟶ B) ↦ ( (A + 𝟙, *) ⟶ (B + 𝟙, *) )~
and conversely ~( (A , a) ⟶ (B , b) ) ↦ ( A - a ⟶ B - b)~ where
~X - x ≡ Σ y ∶ X • ¬(x ≡ y)~. Exercise: Work out the remaining details
for the equivalence.

:ParSetup:
\begin{spec}
_⟶_ : Set → Set → Set
A ⟶ B = A → B ⊎ ⊤

_⟶’_ : ∀ {a} (AA BB : Σ X ∶ Set a • X) → Set _
(A , a) ⟶’ (B , b) = Σ f ∶ (A → B) • f a ≡ b

∣_∣ : ∀ {A B} → A ⟶ B → ((A ⊎ ⊤) , inj₂ tt) ⟶’ ((B ⊎ ⊤) , inj₂ tt)
∣_∣ {A} {B} f = f’ , refl
  where f’ : A ⊎ ⊤ → B ⊎ ⊤
        f’ (inj₂ tt) = inj₂ tt
        f’ (inj₁ x) with f x
        ...~ inj₁ x₁ = inj₁ x₁
        ...~ inj₂ tt = inj₂ tt
#+END_EXAMPLE
:End:

** COMMENT arrows in a particular category :syntax:

 arr-in-cat : ∀{i j} (𝒞 : Category {i} {j}) (A B : Obj 𝒞) → Set j
 arr-in-cat = Category._⟶_
 infix -66 arr-in-cat
 syntax arr-in-cat 𝒞 A B  =  A ⟶ B ∶ 𝒞 -- note the “ghost colon”
  
 -- open Category ⦃...⦄ hiding (Obj)
 open Category using (Id)

** Familiar ~𝒮ℯ𝓉~-tings
Let us give some elementary examples of the notion of a category to exhibit its ubiquity.

*** 𝒮ℯ𝓉's
The collection of small, say level ~i~, types and functions between them and usual function composition
with usual identity form a category and this is not at all difficult to see:
#+BEGIN_SRC agda
 instance
  𝒮e𝓉 : ∀ {i} → Category {ℓsuc i} {i} -- this is a ‘big’ category
  𝒮e𝓉 {i} = record {
      Obj = Set i
    ; _⟶_ = λ A B → (A → B)
    ; _⨾_ = λ f g → (λ x → g (f x))
    ; assoc = ≡-refl
    ; Id = λ x → x
    ; leftId = ≡-refl
    ; rightId = ≡-refl
    }
#+END_SRC
Sadly, this category is traditionally used to motivate constructions in arbitrary categories
and as such people usually think of objects in an arbitrary category as nothing more than
sets with extra datum ---which is completely false.

For example, the category ~Div~ consists of objects /and/ arrows both being numbers ℕ
and there is an arrow $k : m → n$ precisely when ~k × m = n~, so that an arrow is a
constructive witness that $m$ divides $n$. Notice that besides ℕ, no sets nor functions
were involved in the making of this useful number-theoretic category.
# --if you know some category theory, convince yourself that this category is interesting
# by showing, for example, that multiplication distributes over gcd where gcd is the 
# categorial product construction.

*** Sets are trivial categories

Recall that a type, or set, is nothing more than a specified collection of values.

Every set is also a category: There is a formal syntactic object associated with each element, the only morphisms are (formal)
identities, and composition is constantly a syntactic identity.
Some define a set to be a category with only identity morphisms; also called a
‘discrete category’ when one wants to distance themself from set theory ;)
---less loosely, a discrete category over a type ~S~ has ~Obj = S~ and ~(x ⟶ y) = (x ≡ y)~,
where the equivalence is classical, having two possible members /true/ or /false/.

Discrete categories are quite an important space for [[http://homotopytypetheory.org/][hott]] people ... 
that’s right, attractive people are interested in these things.

Observe that all arrows are invertible! ---due to the symmetry of equality.
Categories with this property are known as /groupoids/.

*** Categories are typed monoids

Recall that a monoid ~(M, ⊕, e)~ is a type ~M~ with an associative operation ~⊕ : M × M → M~
that has a unit ~e~.

Every monoid is also a category: There is one object, call it ~★~, the morphisms are the monoid
elements, and composition is the monoid operation. 
---less loosely, for a monoid ~(M, ⊕, e)~ we take ~Obj = {★} , _⟶_ = M~.

In fact, some would define a monoid to be a one-object category!
--I'm looking at you [[https://books.google.ca/books/about/Categories_Allegories.html?id=fCSJRegkKdoC&printsec=frontcover&source=kp_read_button&redir_esc=y#v=onepage&q&f=false][Freyd & Scedrov]] =)

*** Categories are coherently preordered sets

[[http://www.cs.utexas.edu/~EWD/ewd11xx/EWD1102.PDF][Recall]] that a preordered set, or preset, is a type ~P~ with a relation ~≤~ on 
it that satisfies /indirect inequality from above/:
\[
  ∀ x , y •\qquad x ≤ y \quad⇔\quad (∀ z •\; y ≤ z ⇒ x ≤ z)
\]
Equivalently, if it satisfies /indirect equality from below/:
\[ ∀ x , y •\qquad x ≤ y \quad⇔\quad (∀ z •\; z ≤ x ⇒ z ≤ y) \]
If we also have $∀ x , y •\; x ≤ y \,∧\, y ≤ x \;⇒\; x = y$, 
then we say ~(P, ≤)~ is a ‘poset’ or an ‘ordered set’.

Every (pre)ordered set is also a category:
The objects are the elements, 
the morphisms are the order-relations, 
identities are the relfexitivity of ~≤~, 
and composition is transitivity of ~≤~.
To see this more clearly, suppose you have a group
$(M, ⊕, \_{}⁻¹, e)$ and you define $x ≤ y \;⇔\; (∃ m : M •\; m ⊕ x = y)$
then the this is a preorder whose induced category has a morphism 
$m : x → y$ precicely when $m ⊕ x = y$
--now sit down and define the remaining categorical structure of this
‘constructive’ preorder associated to the group.
# and check that this category has $e$ for identity maps and $⊕$
# for composition of morphisms.
#
# Preorder:
# If m ⊕ x = y  and n ⊕ y = x
# Then x = n ⊕ y = n ⊕ m ⊕ x whence e = n ⊕ m, whence we have isos not necessarily equality.

Traditionally, classically, the relation ~≤~ is precicely a function ~P × P ⟶ 𝔹 = {true, flase}~
and thus there is at-most one morphism between any two objects
--consequently, categories with this property are called /poset categories/.

In the constructive setting, the relation ~≤~ is typed ~P × P → Set~ and then
for a preset ~(P, ≤)~ we take ~Obj = P, _⟶_ = a ≤ b~ and insist
on ‘proof-irrelevance’ ~∀ {a b} (p q : a ≤ b) → p ≡ q~ so that there is at most one morphism
between any two objects.
The restriction is not needed if we were using actual categories-with-setoids since then we would
/define/ morphism equality to be \\
~((a, b, p) ≈ (a’, b’, q) )  =  (a ≡ a’  ×  b ≡ b’)~.

Observe that in the case we have a poset, every isomorphism is an equality:
\[
  ∀ x, y •\qquad x ≅ y ⇔ x ≡ y
\]
Categories with this property are called /skeletal/.
Again, hott people like this; so much so, that they want it, more-or-less, to be a
[[http://arxiv.org/abs/1302.4731][foundational axiom]]!

Poset categories are a wonderful and natural motivator for many constructions and definitions in
category theory. This idea is so broad-reaching that it would not be an exaggeration to think of
[[http://www.cs.nott.ac.uk/~psarb2/papers/abstract.html#CatTheory][categories as coherently constructive lattices]]!

*** Groupoids
Equivalence relations are relations that are symmetric, reflexive, and transitive.
Alternatively, they are preorder categories where every morphism is invertible ---this is the
symmetry property. But categories whose morphisms are invertible are groupoids!

Hence, groupoids can be thought of as generalized equivalence relations.
Better yet, as “constructive” equivalence relations: there might be more than one morphism/construction
witnessing the equivalence of two items.

Some insist that a /true/ ‘set’ is a type endowed with an equivalence relation, that is a setoid.
However, since groupoids generalise equivalence relations, others might insist on a true set to be
a "groupoid". However, in the constructive setting of dependent-type theory, these notions
coincide!

*** Rule of Thumb

It’s been said that the aforementioned categories should be consulted whenever one learns a new
concept of category theory.
Indeed, these examples show that a category is a generalisation of a system of processes,
a system of compositionality, and an ordered system.

* /Endowing Structure with Functors/
:PROPERTIES:
:header-args: :tangle "PathCat.agda" 
:END:

** Definition :ignore:
Now the notion of structure-preserving maps, for categories, is just that of graphs 
but with attention to the algebraic portions as well.

#+BEGIN_SRC agda
 record Functor {i j k l} (𝒞 : Category {i} {j}) (𝒟 : Category {k} {l}) 
  : Set (ℓsuc (i ⊍ j ⊍ k ⊍ l)) where
  private
    instance
      𝒞′ : Category ;  𝒞′ = 𝒞
      𝒟′ : Category ;  𝒟′  = 𝒟
  field
    -- Usual graph homomorphism structure: An object map, with morphism preservation
    obj   : Obj 𝒞 → Obj 𝒟                           
    mor   : ∀{x y : Obj 𝒞} → x ⟶ y → obj x ⟶ obj y
    -- Interaction with new algebraic structure: Preservation of identities & composition
    id    : ∀{x   : Obj 𝒞} → mor (Id {A = x}) ≡ Id       -- identities preservation
    comp  : ∀{x y z} {f : x ⟶ y} {g : y ⟶ z} → mor (f ⨾ g) ≡ mor f ⨾ mor g

  -- Aliases for readability
  functor_preserves-composition = comp
  functor_preserves-identities  = id

 open Functor public hiding (id ; comp)
#+END_SRC

For a functor ~F~, it is common practice to denote both ~obj F~ and ~mor F~ by ~F~ and this is usually
not an issue since we can use type inference to deduce which is meant. However, in the Agda formalization
we will continue to use the names ~mor , obj~. Incidentally in the Haskell community, ~mor~
is known as ~fmap~ but we shall avoid that name or risk asymmetry in the definition of
a functor, as is the case in Haskell which turns out to be pragmatically useful.

A functor can be thought of as endowing an object with some form of structure
---since categories are intrinsically structureless in category theory---
and so the morphism component of a functor can be thought of as preserving relations:
~f : a ⟶ b ⇒ F f : F a ⟶ F b~ can be read as, ‘‘if ~a~ is related to ~b~ (as witnessed by ~f~)
then their structured images are also related (as witness by ~F f~)’’.
Recall the category ~Div~ for constructive divisibility relationships ;-)

** COMMENT Synonyms for Readability

While we’re close to the definition, let’s introduce some synonyms for readability
#+BEGIN_EXAMPLE
 module _ {i j k l} {𝒞 : Category {i} {j}} {𝒟 : Category {k} {l}} {F : Functor 𝒞 𝒟}
  where

    functors-preserve-composition = Functor.comp F
    functors-preserve-identities  = Functor.id F
#+END_EXAMPLE
We make these as synonyms rather than names in the record since we do not want to use such lengthy
identifiers when realizing functor instances. The reason we do not make these synonyms in the
record but rather in a public dummy module is to make the functor in question found from the ambient
context via the implicit declaration ~{F : Functor 𝒞 𝒟}~.

Musa: Apparently, the above intention did not work as desired.
Most of the time, I had to supply the functor anyways.

** COMMENT Functor Conventions
In informal mathematics a functor ~F = (obj , mor, preservation proofs)~
is usually presented as \\ /F = (F₀, F₁) is a functor (exercise to reader)/.

“endo”-morphism is a morphism with the
same source and target, an “auto”-morphism
is an isomorphism with the same source and
target.

Say “co”-functor as short for “co”ntravariant
functor. Notice that the composition of
cofunctors is a covaraint functor ---cf the multiplication of negative numbers is a positive functor.
 
** Examples

A functor among monoids --construed as categories-- is just a monoid homomorphism;
i.e., an identity and multiplication preserving function of the carriers.
\[ (M, ⊕, e) ⟶ (N, ⊗, d) \quad=\quad Σ h ∶ M → N \;•\; ∀ x,y \;•\; h(x ⊕ y) = h x ⊗ h y \;∧\; h e = d \]
# By induction, ~h~ preserves all finite multiplications:
# ~h (⊕ i ∶ 1..n • xᵢ) = (⊗ i ∶ 1..n • h xᵢ)~ where
# ~(★ i ∶ 1..n • yᵢ) ≔ e ★ y₁ ★ y₂ ⋯ ★ yₙ~.
# More generally, 
By induction, ~h~ preserves all finite ⊕-multiplication and, more generally,
functors preserve finite compositions:
\[ F (f₀ ⨾ f₁ ⨾ ⋯ ⨾ fₙ) \;\;=\;\; F\,f₀ ⨾ F\,f₁ ⨾ ⋯ ⨾ F\,fₙ \]
Cool beans :-)
# ~F (⨾ i ∶ 1..n • fᵢ) = (⨾ i ∶ 1..n • F fᵢ)~
In the same way, sit down and check your understanding!
+ A functor among discrete categories is just a function of the associated sets.
+ A functor among poset categories is an order-preserving function.

Two examples of functors from a poset (category) to a monoid (category):

+ ~monus : (ℕ, ≤) ⟶ (ℕ,+, 0)~ is a functor defined on morphisms by
  \[ i ≤ j \quad⇒\quad \mathsf{monus}(i,j) ≔ j - i\] 
  Then the functor laws become  ~i - i = 0~ and ~(k - j) + (j - i) = k - i~.

+ ~div : (ℕ⁺, ≤) → (ℚ, ×, 1)~ is defined on morphisms by
  \[i ≤ j \quad⇒\quad \mathsf{div}(i,j) ≔ j / i\]
  The functor laws become ~i / i = 1~ and ~(k / j) × (j / i) = k / i~.

Hey, these two seem alarmingly similar! What gives!
Well, they’re both functors from posets to monoids ;)
Also, they are instances of ‘residuated po-monoids’.
Non-commutative monoids may have not have a general inverse operation,
but instead might have left- and right- inverse operations known as residuals
---we’ll mention this word again when discussing adjunctions and are 
categorically seen as kan extensions.
Alternatively, they’re are instances of [[http://link.springer.com.libaccess.lib.mcmaster.ca/article/10.1007/s10773-004-7710-7][‘(Kopka) Difference-posets’]].


For more examples of categories, we will need to reason
by extensionality --two things are ‘equal’ when they have
equivalent properties ... recall Leibniz and his 
[[https://en.wikipedia.org/wiki/Identity_of_indiscernibles][law of indiscernibles]] ;p

# Functors are not determined by where they send objects
# e.g., https://math.stackexchange.com/a/3026355/80406
* /The four postulates of the apocalypse/
:PROPERTIES:
:header-args: :tangle "PathCat.agda" 
:END:

** Intro :ignore:
Categories have objects and morphisms between them, functors are morphisms between categories,
and then we can go up another level and consider morphisms between functors.
These ‘level 2 morphisms’ are pretty cool, so let’s touch on them briefly.

Recall that a poset ordering is extended to (possibly non-monotone) functions $f , g$ pointwise
\[f \overset{.}{≤} g \quad\iff\quad (∀ x •\; f\, x \,≤\, g\, x)\]
As such, with posets as our guide, we extend the notion of ‘morphism between functors’ 
to be a ‘witness’ of these orderings $η : ∀ {X} → F\, X ⟶ G\, X$
--this is a dependent type, note that the second arrow notates category morphisms, whereas
the first acts as a separator from the implicit parameter $X$; sometimes one sees $η_X$
for each component/instance of such an operation.
# http://www.jmilne.org/not/Mamscd.pdf
#+BEGIN_CENTER
$\require{AMScd}$
\begin{CD}
\color{navy}{F\, A} @>\color{fuchsia}{η_A}>>      \color{teal}{G\, A}    \\
@V\color{navy}{F\, f}VV    \!=                    @VV\color{teal}{G\, f}V \\
\color{navy}{F\, B} @>>\color{fuchsia}{η_B}>      \color{teal}{G\, B}
\end{CD}
#+END_CENTER

However, then for any morphism $f : A ⟶ B$ we have two ways to get from $F\, A$ to $G\, B$ via
~F f ⨾ η {B}~ and ~η {A} ⨾ G f~ and rather than choose one or the other, we request that they
are identical ---similar to the case of associativity.
#+BEGIN_SRC agda
 NatTrans : ∀ {i j i’ j’}  ⦃ 𝒞 : Category {i} {j} ⦄ ⦃ 𝒟 : Category {i’} {j’} ⦄ 
            (F G : Functor 𝒞 𝒟) → Set (j’ ⊍ i ⊍ j)
 NatTrans ⦃ 𝒞 = 𝒞 ⦄ ⦃ 𝒟 ⦄ F G =
   Σ η ∶ (∀ {X : Obj 𝒞} → (obj F X) ⟶ (obj G X))
       • (∀ {A B} {f : A ⟶ B} → mor F f ⨾ η {B} ≡ η {A} ⨾ mor G f)
#+END_SRC
The naturality condition is remembered by placing the target component ~η {B}~ /after/
lifting ~f~ using the /source/ functor ~F~;
likewise placing the source component /before/ applying the target functor.

Another way to remember it:
~η : F ⟶̇ G~ starts at ~F~ and ends at ~G~, so the naturality also starts with ~F~ and ends
with ~G~; i.e., ~F f ⨾ η {B} = η {A} ⨾ G f~ :-)

It is at this junction that aforementioned problem with our definition
of category comes to light: Function equality is extensional by definition 
and as such we cannot prove it.
Right now we have two function-like structures for which we will postulate a 
form of extensionality,
#+BEGIN_SRC agda
 -- function extensionality
 postulate extensionality : ∀ {i j} {A : Set i} {B : A → Set j} 
                              {f g : (a : A) → B a}
                          → (∀ {a} → f a ≡ g a) → f ≡ g

 -- functor extensionality
 postulate funcext : ∀ {i j k l} ⦃ 𝒞 : Category {i} {j} ⦄ ⦃ 𝒟 : Category {k} {l} ⦄
                       {F G : Functor 𝒞 𝒟} 
                     → (oeq : ∀ {o} → obj F o ≡ obj G o)
                     → (∀ {X Y} {f : X ⟶ Y}
                        → mor G f  ≡  ≡-subst₂ (Category._⟶_ 𝒟) oeq oeq (mor F f))
                     → F ≡ G

 -- graph map extensionality
 postulate graphmapext : {G H : Graph } {f g : GraphMap G H} 
                       → (veq : ∀ {v} → ver f v ≡ ver g v)
                       → (∀ {x y} {e : Graph._⟶_ G x y} 
                          → edge g e ≡ ≡-subst₂ (Graph._⟶_ H) veq veq (edge f e))
                       → f ≡ g

 -- natural transformation extensionality
 postulate nattransext : ∀ {i j i’ j’} {𝒞 : Category {i} {j} } {𝒟 : Category {i’} {j’} } 
                         {F G : Functor 𝒞 𝒟} (η γ : NatTrans F G)
                       → (∀ {X} → proj₁ η {X} ≡ proj₁ γ {X})
                       → η ≡ γ
#+END_SRC

Natural transformations are too cool to end discussing so briefly
and so we go on to discuss their usage is mathematics later on.

** A very big ~𝒞𝒶𝓉~

With the notions of categories, functors, and extensionality in-hand we can now discus the
notion of the category of small categories and the category of small graphs. 
Afterwards we give another example of a functor that says how every category can be 
construed as a graph.

First the category of /smaller/ categories,
#+BEGIN_QUOTE
~𝒞𝒶𝓉~ is a category of kind ~(ℓsuc m, ℓsuc m)~, where ~m = i ⊍ j~, and its objects
are categories of kind ~(i , j)~ and so it is not an object of itself.

Thank-you Russel and friends!

( You may proceed to snicker at the paradoxical and size issues encountered 
  by those who use set theory.
  ---Then again, I’ve never actually learned, nor even attempted to learn, 
  any ‘‘formal set theory’’;
  what I do know of set theory is usually couched in the language of type theory; 
  I heart [[https://www.springer.com/gp/book/9780387941158][LADM]]!
)
#+END_QUOTE

#+BEGIN_SRC agda
 instance
  𝒞𝒶𝓉 : ∀ {i j} → Category {ℓsuc (i ⊍ j)} {ℓsuc (i ⊍ j)}
  𝒞𝒶𝓉 {i} {j} = record {
      Obj = Category {i} {j}
    ; _⟶_ = Functor
    ; _⨾_ = λ {𝒞} {𝒟} {ℰ} F G →
        let instance
                   𝒞′ : Category ; 𝒞′ = 𝒞
                   𝒟′ : Category ; 𝒟′ = 𝒟  
                   ℰ′ : Category ; ℰ′ = ℰ
        in record
        { obj  =  obj F ⨾ obj G -- this compositon lives in 𝒮e𝓉
        ; mor  =  mor F ⨾ mor G
        ; id   =  λ {x} → begin
              (mor F ⨾ mor G) (Id ⦃ 𝒞 ⦄ {A = x})
            ≡⟨ "definition of function composition" ⟩′
              mor G (mor F Id)
            ≡⟨ functor F preserves-identities even-under (mor G) ⟩
              mor G Id
            ≡⟨ functor G preserves-identities ⟩
              Id
            ∎ 
        ; comp = λ {x y z f g} →             
             begin
               (mor F ⨾ mor G) (f ⨾ g)
            ≡⟨ "definition of function composition" ⟩′
               mor G (mor F (f ⨾ g))
             ≡⟨ functor F preserves-composition even-under mor G ⟩
               mor G (mor F f ⨾ mor F g)
             ≡⟨ functor G preserves-composition ⟩
               (mor F ⨾ mor G) f ⨾ (mor F ⨾ mor G) g
             ∎
        }
    ; assoc    =  λ {a b c d f g h} → funcext ≡-refl ≡-refl
    ; Id       =  record { obj = Id ; mor = Id ; id = ≡-refl ; comp = ≡-refl }
    ; leftId   =  funcext ≡-refl ≡-refl
    ; rightId  =  funcext ≡-refl ≡-refl
    }
#+END_SRC

Some things to note,

+ First off: ~functor F preserves-composition even-under mor G~ is a real line of code!
  It consists of actual function calls and is merely an alias for
  ~≡-cong (mor G) (mor F)~ but it sure is far more readable than this form!

+ We could have written ~id = ≡-cong (mor G) (id F) ⟨≡≡⟩ id G~,
  but this is not terribly clear what is going on.
  Especially since we introduced categories not too long ago,
  we choose to elaborate the detail.

  Likewise, ~comp = (≡-cong (mor G) (comp F)) ⟨≡≡⟩ (comp G)~.

+ ~assoc~ is trivial since function composition is, by definition, associative.
  Likewise ~leftId, rightId~ hold since functional identity is, by definition, unit of function composition.

# + The definition of composition immediately gives us that ~obj , mor~ distributes over composition:
#   \[ \eqn{𝒞𝒶𝓉 $\obj$ Distributivity}{\obj\, (F ⨾ G) \quad=\quad \obj\, F \;⨾\; \obj\, G}\]
#   \[ \eqn{𝒞𝒶𝓉 $\mor$ Distributivity}{\mor\, (F ⨾ G) \quad=\quad \mor\, F \;⨾\; \mor\, G}\]
# 
** ~𝒢𝓇𝒶𝓅𝒽~
In a nearly identical way, just ignoring the algebraic datum, we can show that
~Graph~'s with ~GraphMap~'s form a graph
#+BEGIN_EXAMPLE
  𝒢𝓇𝒶𝓅𝒽 : Category
  𝒢𝓇𝒶𝓅𝒽 = {! exercise !}
#+END_EXAMPLE

:Solution:
#+BEGIN_SRC agda
  𝒢𝓇𝒶𝓅𝒽 : Category
  𝒢𝓇𝒶𝓅𝒽 =
   record
    { Obj   = Graph ; _⟶_ = GraphMap
    ; _⨾_   = λ f g → record { ver = ver f ⨾ ver g ; edge = edge f ⨾ edge g } -- using ~𝒮et~
    ; assoc = ≡-refl  -- function composition is associtive, by definition
    ; Id    = record { ver = Id ; edge = Id } ; leftId = ≡-refl ; rightId = ≡-refl
    -- functional identity is no-op, by definition
    }
    where open GraphMap
#+END_SRC
:End:
 
** ~𝒞𝒶𝓉~'s are ~𝒢𝓇𝒶𝓅𝒽~'s
#+BEGIN_CENTER
/Forgive and forget: The 𝒰nderlying functor./
#+END_CENTER

Let’s formalise what we meant earlier when we said graphs are categories 
but ignoring the algebraic data.

Given a category, we ignore the algebraic structure to obtain a graph,
#+BEGIN_SRC agda
 𝒰₀ : Category → Graph
 𝒰₀ 𝒞 = record { V = Obj 𝒞 ; _⟶_ = Category._⟶_ 𝒞 }
#+END_SRC

Likewise, given a functor we ‘forget’ the property that the map of morphisms needs to preserve all
finite compositions to obtain a graph map:
#+BEGIN_SRC agda
 𝒰₁ : {𝒞 𝒟 : Category} → 𝒞 ⟶ 𝒟 → 𝒰₀ 𝒞 ⟶ 𝒰₀ 𝒟
 𝒰₁ F = record { ver = obj F ; edge = mor F }
#+END_SRC
This says that ~𝒰₁~ turns ~ver, edge~ into ~obj , mor~
--~𝒰₁ ⨾ ver  ≡ obj~ and ~𝒰₁ ⨾ edge ≡ mor~-- reassuring us that ~𝒰₁~ acts
as a bridge between the graph structures: ~ver , edge~ of graphs and
~obj , mor~ of categories.

Putting this together, we obtain a functor.
#+BEGIN_SRC agda
-- Underlying/forgetful functor: Every category is a graph
 𝒰 : Functor 𝒞𝒶𝓉 𝒢𝓇𝒶𝓅𝒽
 𝒰 = record { obj = 𝒰₀ ; mor = 𝒰₁ ; id = ≡-refl ; comp = ≡-refl }
#+END_SRC
We forget about the extra algebraic structure of a category and of a functor to
arrive at a graph and graph-map, clearly --~≡-refl~-- such ‘forgetfullness’ preserves identities
and composition since it does not affect them at all!

Those familiar with category theory may exclaim that just as I have mentioned
the names ‘underlying functor’ and ‘forgetful functor’ I ought to mention
‘stripping functor’ as it is just as valid since it brings about connotations of
‘stripping away’ extra structure.
I’m assuming the latter is less popular due to its usage for
poor mathematical jokes and puns.

Before we move on, the curious might wonder if ‘‘categories are graphs’’ 
then what is the analgoue to ‘‘$X$ are hypergraphs’’,
it is [[http://arxiv.org/PS_cache/math/pdf/0305/0305049v1.pdf#page=178][multicategories]].

Now the remainder of these notes is to build-up the material
needed to realise the notion of ‘free’ which is, in some sense,
/the best-possible approximate inverse/ to ‘forgetful’
--however, forgetting is clearly not invertible since it can easily
confuse two categories as the same graph!

* /How natural is naturality?/
:PROPERTIES:
:header-args: :tangle "PathCat.agda" 
:END:

# commutative diagrams with MathJax
# http://www.jmilne.org/not/Mamscd.pdf

** Intro                                                            :ignore:
Recall, that a natural transformation $η : F \natTo G$ is a family
$∀ \{X \,:\, \Obj 𝒞\} \,→\, F\, X ⟶ G\, X$ that satisfies the naturality condition:
$∀ \{A \; B\} \{f \,:\, A ⟶ B\} \,→\, F f ⨾ η {B} \;≡\; η {A} ⨾ G f$.

  + In the type of η, note that the first /show/ arrow ‘→’ acts as a separator from the
    the ∀-quantified variable $X$, whereas the second /longer/ arrow ‘⟶’ denotes the
    morphism type in the category 𝒞.

  + We will freely interchange the informal mathematical rendition $(η_x : F\, X → G\, X)_{x ∈ \Obj 𝒞}$
    with the aforementioned formal Agda forms ~∀{X : Obj 𝒞} → F X → G → X~ and invocation ~η {X}~.

#+BEGIN_CENTER
$\require{AMScd}$
\begin{CD}
\color{navy}{F\, A} @>\color{fuchsia}{η_A}>>      \color{teal}{G\, A}    \\
@V\color{navy}{F\, f}VV    \!=                    @VV\color{teal}{G\, f}V \\
\color{navy}{F\, B} @>>\color{fuchsia}{η_B}>      \color{teal}{G\, B}
\end{CD}
#+END_CENTER
Let us look at this from a few different
angles; in particular, [[http://mathoverflow.net/questions/56938/what-does-the-adjective-natural-actually-mean/56956][what does the adjective ‘natural’ actually mean?]] 
It’s been discussed on many forums and we collect a few of the key points here.

** Identification of possible paths ---contraction of choices

Given two functors $F , G$, for any object $~x$ we obtain two objects $F\, x\, , \, G\, x$ and so a morphism
from $F$ to $G$ ought to map such $F\,x$ to $G\, x$. That is, a morphsim of functors is a family \\
$η \,:\, ∀ \{x : \Obj 𝒞\} \,→\, F \,x ⟶ G \,x$. Now for any $f : a → b$ there are two ways to form a morphism
$F\, a → G\, b$: $F f ⨾ η \{b\}$ and $η \{a\} ⨾ G\, f$. Rather than make a choice each time we want such
a morphism, we eliminate the choice all together by insisting that they are identical.
This is the naturality condition.

This is similar to when we are given three morphisms $f : a → b , g : b → c , h : c → d$,
then there are two ways to form a morphism $a → d$; namely $(f ⨾ g) ⨾ h$ and $f ⨾ (g ⨾ h)$.
Rather than make a choice each time we want such a morphism, we eliminate the choice all together
by insisting that they are identical. This is the associativity condition for categories.

Notice that if there’s no morphism $F\, x ⟶ G\, x$ for some $x$, they by definition there’s no
possible natural transformation $F \natTo G$.

** No Choice --free will is only an illusion

\begin{align*}
     & \quad\text{the natural $X$}
\\ = & \quad\text{the $X$ which requires no arbitrary choices}
\\ = & \quad\text{the canonical/standard $X$}
\end{align*}

That is,
\begin{align*}
     & \quad \text{it is a natural construction/choice}
\\ = & \quad \text{distinct people would arrive at the same construction;}
\\   & \quad \text{ (no arbitrary choice or cleverness needed) }
\\ = & \quad \text{ there is actually no choice, i.e., only one possiility, }
\\   & \quad \text{ and so two people are expected to arrive at the same ‘choice’}
\end{align*}

Thus, if a construction every involves having to decide between distinct routes, then chances are
the result is not formally natural.
Sometimes this ‘inution’ is developed from working in a field for some time; 
sometimes it just “feel”" natural.
# "natural" = "resonable or expected in the ambient context" ; 

[[http://math.stackexchange.com/questions/939404/do-natural-transformations-make-god-given-precise?rq=1][Some would even say]]: /Natural = God-given/.

** COMMENT Common Properties                            :this_looks_suspect:
"natural solution" = "has properties of all other solutions"

[To consider: is a natural solution then just an initial solution? That is, an intial
transformation?]

{\sc add this to todo’s list}

** Natural means polymorphic without type inspection

#  nattrans are polyfuncs

A natural transformation can be thought of as a polymorphic function
~∀ {X} → F X ⟶ G X~ /where/ we restrict ourselves to avoid inspecting any ~X~.

+ Recall that a ~mono~-morphic operation makes no use of type variables in its signature,
  whereas a ~poly~-morphic operation uses type variables in its signature.

+ For example, in C# one can ask if one type ~is~ a subclass of another thereby
  obtaining specific information, whereas there is no such mechanism in Haskell.
 
Inspecting type parameters or not leads to the distinction of ad hoc plymorphism vs. parametric
polymorphism ---the later is the kind of polymorphism employed in functional language like Haskell
and friends and so such functions are natural transformations by default!
[[http://ecee.colorado.edu/ecen5533/fall11/reading/free.pdf][Theorems for free!]]

For example,
#+BEGIN_EXAMPLE
-- Let 𝒦 x y ≔ Id {x} for morphisms, and 𝒦 x y ≔ x for objects.

size : ∀ {X} → List X → 𝒦 ℕ X   
size [x₁, …, xₙ] = n
#+END_EXAMPLE
is a polymorphic function and so naturality follows and is easily shown --show it dear reader!
So we have always have
\[List\; f \;⨾\; size \quad=\quad size\]
Since ~𝒦 ℕ f = Id~, then by extensionality: ~size : List ⟶̇ 𝒦~.
:Solution:
for any ~f : A ⟶ B~ we have
#+BEGIN_EXAMPLE
  (List f ⨾ size) [x₁, …, xₙ]
=
  size (List f [x₁, …, xₙ])
=
  size [f x₁, …, f xₙ]
=
  n
=
  Id n
=                  
  (𝒦 ℕ f) n
=  
  (𝒦 ℕ f) (size [x₁ , …, xₙ])
=  
  (size ⨾ 𝒦 ℕ f) [x₁, …, xₙ]
#+END_EXAMPLE
Hence, ~size : List ⟶̇ 𝒦~.
:End:

On the other hand, the polymorphic function
#+BEGIN_EXAMPLE
whyme : ∀ {X} → List X → 𝒦 Int X
whyme {X} [x₁,…,xₙ] = If X = ℕ then 1729 else n
#+END_EXAMPLE
is not natural: The needed equation ~F f ⨾ η {B} = η {A} ⨾ G f~
for any ~f : A → B~ breaks as witnessed by
~f = (λ x → 0) : ℝ → ℕ~ and any list with length ~n ≠ 1729~,
and this is easily shown --do so!
:Solution:
#+BEGIN_EXAMPLE
  (List f ⨾ whyme) [x₁, …, xₙ]
=
  whyme (List f [x₁, …, xₙ])
=
  whyme [f x₁, …, f xₙ]
=
  if ℕ = ℕ then 1729 else n
=
  1729
≠
  n
=  
  if ℝ = ℕ then 1729 else n
=
  (𝒦 ℕ f) (whyme [x₁, …, xₙ])
=
  (whyme ⨾ 𝒦 Int f) [x₁, …, xₙ]
#+END_EXAMPLE
:End:

One might exclaim, /hey! this only works ’cuz you’re using Ramanujan’s taxi-cab number!/
/1729 is the smallest number expressible as a sum of 2 cubes in 2 ways:/
/$1729 = 12³ + 1³ = 10³ + 9 ³$./ I assure you that this is not the reason that naturality breaks,
and I commend you on your keen observation.

Notice that it is natural if we exclude the type inspected, ℕ.
That is, if we only consider $f : A → B$ with $A ≠ ℕ ≠ B$.
In general, is it the case that a transformation can be made natural by excluding
the types that were inspected?

Before we move on, observe that a solution in $h$ to the absorptive-equation $F f ⨾ h = h$
is precisely a natural transformation from $F$ to the aforementioned ‘diagonal functor’:
\[F f ⨾ h \;=\; h \qquad⇔\qquad ∃ X : Obj \;•\; h ∈ F \overset{.}{⟶} 𝒦 X ~\]
#
# Recall that →̇ is a Σ-type for which membership is defined as follows: 
#
# ~(x ∈ Σ y ∶ Y • P y) =  (Σ y ∶ Y • y ≡ x ∧ P y)~.
#
# {\sc add to todo’s: formalise ~∈~; trickier than it looks ;) }

# since ~g ⨾ (λ _ → e) = (λ x → (λ _ → e) (g x) ) = (λ x → e)~
In particular, due to the constant-fusion property $g \,⨾\, 𝒦\, e \;=\; 𝒦\, e$, we have that
\[∀ \{F\} \{X\} \{e \,:\, X\} \;→\; (𝒦\, e) \,∈\, F \overset{.}{⟶} 𝒦\, X \]
Is the converse also true? If $h ∈ F ⟶̇ 𝒦 X$ then $h \,=\, 𝒦\, e$ for some $e$?

** COMMENT monomorphic funcs are natural                  :possibly_harmful:

Notice that that monomorphic functions are always natural!

Given ~m : X → Y~ we can consture this as ~m : ∀ {Z} → 𝒦 X Z → 𝒦 Y Z~ and then we obtain
naturality: given ~f : A → B~,
#+BEGIN_EXAMPLE
  m ⨾ 𝒦 X f
= m ⨾ Id
= m
= Id ⨾ m
= 𝒦 Y f ⨾ m
#+END_EXAMPLE

this is probably less insightful, and probably a damaging observation...

** Natural means no reference to types

The idea that a natural transformation cannot make reference to the type variable at all can be
seen by yet another example.

#+BEGIN_EXAMPLE
  data 𝟙 : Set where ★ : 𝟙

  -- Choice function: For any type X, it yields an argument of that type.
  postulate ε : (X : Set) → X

  nay : ∀ {X} → X → X
  nay {X} _ = ε X
#+END_EXAMPLE

Now naturality $\Id \, f ⨾ nay_B \;=\; nay_A ⨾ \Id \, f$ breaks as witnessed by
$f \;=\; (λ _ → εℕ + 1) \;:\; 𝟙 → ℕ$ --and provided $εℕ ≠ 0$, otherwise
we could use an $f$ with no fix points.

:Solution:
#+BEGIN_EXAMPLE
  Id f ⨾ nay {ℕ}
=
  f ⨾ (λ _ → ε ℕ)
=
  λ _ → ε ℕ
≠
  λ _ → ε ℕ + 1
=
  λ _ → f (ε 𝟙)
=
  nay {𝟙} ⨾ Id f
#+END_EXAMPLE
:End:

From this we may hazard the following:
If we have natural transformations $ηᵢ \,:\, ∀ {X : Objᵢ} →\, F X \overset{.}{⟶} G X$
where the $Objᵢ$ partition the objects available --- i.e., $Obj \;=\; Σ i \,•\, Objᵢ$ ---
then the transformation $η_{(i, X)} \;=\; ηᵢ$ is generally unnatural since it clearly makes choices,
for each partition.

** Natural means uniformly and simultaneously defined

A family of morphisms is /natural in x/ precisely when it is defined
/simultaneously/ for all /x/ ---there is no inspection of some particular /x/ here and there,
no, it is uniform! With this view, the naturality condition is thought of as a ‘simultaneity’
condition. [[https://www.google.ca/webhp?sourceid=chrome-instant&ion=1&espv=2&ie=UTF-8&client=ubuntu#q=general%20theory%20of%20natural%20equivalences][Rephrasing GToNE]].

The idea of naturality as uniformly-definable is pursued by [[http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.107.2336&rep=rep1&type=pdf][Hodges and Shelah]].

** Naturality is restructure-modify commutativity

Recall that a functor can be thought of as endowing an object with structure.
Then a transformation can be thought of as a restructuring operation and naturality means
that it doesn’t matter whether we restructure or modify first, as long as we do both.

** Natural means obvious

It may help to think of /there’s a natural transformation from F to G/ to mean
/there’s an obvious/standard/canconical way to transform F structure into G structure/.

Likewise, /F is naturally isomorphic to G/ may be read /F is obviously isomorphic to G/.
For example, *TODO* seq-pair or pair-seq ;-)

Sometimes we can show ‘‘F X is isomorphic to G X, if we make a choice dependent on X’’
and so the isomorphism is not obvious, since a choice must be made.

** Naturality is promotion

+ I think Richard Bird refers to the naturality condition as a promotion law where the functors
  involved are thought of as (list) constructions.

+ The nomenclature is used [[https://www.cs.ox.ac.uk/files/3378/PRG56.pdf][to express the idea than operation on a compound structure
  can be ‘promoted’ into its components.]]
   # http://www.cs.ox.ac.uk/files/3390/PRG69.pdf, orginal source, is a dead link.
   
+ Reading ~F f ⨾ η {B} = η {A} ⨾ G f~ from left to right:
   Mapping $f$ over a complicated structure then handling the result
   /is the same as/
   handling the complex datum then mapping $f$ over the result.

   - `Handling' can be thought of as `processing' or as `reshaping'.
   
Lists give many examples of natural transformations by considering
[[https://link.springer.com/chapter/10.1007/3-540-51305-1_24][a categorical approach to the theory of lists.]]

** Naturality as a rewrite rule

The naturality condition can be seen as a rewrite rule that let’s us replace a complicated or
inefficient side with a simplier or more efficient yet equivalent expression.
I think I first learned this view of equations at the insistence of
[[https://www.amazon.com/Algebra-Programming-Prentice-hall-International-Computer/dp/013507245X][Richard Bird and Oege de Moor]] 
--whose text can be found [[http://themattchan.com/docs/algprog.pdf][here]], albeit the legitimacy of the link may be suspect.

For example, recall the 𝒦onstant functor now construed only as a polymorphic binary operation:
#+BEGIN_EXAMPLE
_⟪_    :  ∀{A B : Set} → A → B → A
a ⟪ b  =  a
#+END_EXAMPLE

The above is a constant time operation, whereas the next two are linear time operations; i.e.,
they take ~n~ steps to compute, where ~n~ is the length of the given list.

#+BEGIN_EXAMPLE
-- This' map for List's; i.e., the mor of the List functor 
map    : ∀ {A B : Set} (f : A → B) → List A → List B
map f []         =  []
map f (x ∷ xs)  =  f x ∷ map f xs

-- Interpret syntax `x₀∷⋯∷xₙ₋₁` semantically as `x₀ ⊕ ⋯ ⊕ xₙ₋₁`, where ⊕ = cons.
fold  : ∀ {A B : Set} (cons : A → B → B) (nil : B) → List A → B
fold cons nil [] = nil
fold cons nil (x ∷ xs) = cons x (fold cons nil xs)
#+END_EXAMPLE

By /Theorems for Free/, or a simple proof, we have that ~fold~ is a natural
transformation $List \overset{.}{→} \Id$:
\[ List\; f \;⨾\; fold \; cons_B \; nil_B \qquad=\qquad fold \; cons_A \; nil_A \;⨾\; f \]
Note that here we are ranging over objects $X$ equipped with $nil_X : X, \; cons_X : X → X → X$;
as such the equation is not valid when this is not the case.

Now we map compute,
#+BEGIN_EXAMPLE
postulate A B : Set
postulate nil-B : B
postulate f : A → B -- possibly expensive operation

head  :  List B → B
head  =  fold _⟪_ nil-B

compute  :  List A → B
compute  =  map f  ⨾  head
#+END_EXAMPLE

That is,
#+BEGIN_EXAMPLE
  compute [x₀, …, xₙ₋₁]
= head (map f [x₀, …, xₙ₋₁])
= head [f x₀, …, f xₙ₋₁]
= f x₀  ⟪  f x₁ ⟪ ⋯ ⟪ ⋯ f xₙ₋₁ ⟪ nil-B 
= f x₀
#+END_EXAMPLE

However this approach performs the potentially expensive operation $f$ a total of 
$n = \text{“length of input”}$ times! In spite of that, it only needs the first element of
the list and performs the operation only once! Indeed, by the naturality of ~fold~ we have
an equivalent, and more efficient, formulation:
#+BEGIN_EXAMPLE
compute  =  head  ⨾  f
#+END_EXAMPLE

This operation only performs the potentially costly ~f~ once!

A more concrete and realistic example is to produce an efficient version of the function
that produces the ~average xs = div (sum xs, length xs)~ of a list of numbers: This operation
traverses the input list twice, yet we can keep track of the length as we sum-along the list
to obtain an implementation that traverses the list only once!

[[https://scss.tcd.ie/publications/tech-reports/reports.99/TCD-CS-1999-74.pdf][Indeed]],
#+BEGIN_EXAMPLE
div : ℕ × ℕ → ℕ
div (0, 0) = 0
div (m, n) = m ÷ n

average     :  List ℕ → ℕ
average xs  =  div (fold _⊕_ 𝟘 xs)  
  where  𝟘 = (0 , 0) 
         _⊕_  : ℕ → (ℕ × ℕ) → ℕ
         a ⊕ (b , n) = (a + b , n + 1)
#+END_EXAMPLE

** Naturality is just model morphism

Given two functors $F , G : 𝒞 ⟶ 𝒟$ let us construe them as only graph homomorphisms.
Then each is a model of the graph $𝒰₀ \; 𝒞$ ---each intereprets the nodes and edges of ~𝒰₀ 𝒞~ as
actual objects and morphisms of 𝒟--- and a natrual transformation is then nothing
more than a morphism of models.

# {\sc was the notion of model morphisms mentioned earlier when
# models were introduced?}

** Naturality yields pattern matching

In the setting of types and functions, ~η : F ⟶̇ G~ means we have ~η (F f x) = G f (η x)~
which when read left-to-right says that ~η~ is defined by pattern-matching on its argument
to obtain something of the form ~F f x~ then it is defined recursively by examining ~x~ and then
applying ~G f~ to the result ---of course there’s some base case ~F~ definitions as well.

Alternatively, the input to ~η~ is of the form ~F …~ and its
output is of the form ~G …~ --mind blown!

# Hence, in a pointwise setting, to /define/ a natural transformation η
# we need to define it at components of the input shape $η_{F \, f \, x}$
# to have the output shape $G \, f \, η_{x}$.

For example, I want to define a transformation $\mathsf{List} ⟶̇ \mathsf{List}$.
0. So let me suppose the input is of the shape $\List \, f\, x$, more concretely
   it is of the shape 
   \\ ~[f x₀, f x₁, …, f xₙ₋₁]~ --for arbitrary $f : A → B$.
1. Then the output shape must be $\List \, f\, (η \, x)$, more concretely
   it is of the shape \\ ~[f y₀, f y₁, …, f yₘ₋₁]~ where $y \,=\, η\,x$.
2. So my /only/ choices are $y : \List A$ and $m : ℕ$

   Here are some possibilities and the resulting η:
   + $y, m = x, n$ :: Identity function
   + $y, m = x, 0$ :: Constantly empty list ~[]~ function
   + $y, m = x, 1$ :: The first element, ‘head’, function
   + $y, m = x, k$ :: The first $k < n$ elements function
   + $m = n$ with $yᵢ = xₙ₋ᵢ$ :: List reversal function
   + $y, m = \mathsf{reverse}(x), k$ :: The last $k < n$ elements, in reverse, function
        - Here we applied an already known natural transformation
          and indeed the composition of naturally transformation is itself natural.

** Examples

+ Pointwise Monotonicity ::

   A functor among poset categories is an order-preserving function and a natural transformation
   $f \natTo g$ is a proof that $f \overset{.}{≤} g$ pointwise: $∀ x \,•\, f\, x \;≤\; g\, x$ 
   ---all the other pieces for a natural
   transformation are automatic from the definition of begin a poset category.
   
+ conjugation ::
  
  A functor among monoids --construed as categories-- is just a monoid homomorphism:
  \begin{align*}
             & (M, ⊕, e) ⟶ (N, ⊗, d) 
  \\ ≅ \quad & Σ h ∶ M → N • ∀ \{x \, y \} •\; h(x ⊕ y) = h x ⊗ h y \lands h e = d
  \end{align*}
  A natural transformation ~(f, prf) ⟶ (g, prf’)~ is a point $n : N$ with
  $∀ x ∶ M \;•\; f x ⊗ n \,=\, n ⊗ g x$, a so-called ‘conjugation’ by $n$ that takes $f$ to $g$.
  :Solution:
    η ∈ (f , prf) ⟶ (g , prf’)
  =                               { defn of natural transformation }
    η ∈ ∀ {x} → f x ⟶ g x in M
    with ∀ m • f m ⨾ η = η ⨾ g m
  =                               { arrows in monoid categories }
    η ∈ N with ∀ x ∶ M • f x ⨾ η = η ⨾ g x
  =                               { composition in monoid categories }
    η ∈ N with ∀ x ∶ M • f x ⊗ η = η ⊗ g x
  :End:
    
+ fold ::
    
    Recall from the introduction $𝒰(S, ⊕, e) \;=\; S$ was the underlying functor from monoids to sets.

    Let $𝒰 × 𝒰$ be the functor that for objects $M \;↦\; 𝒰\, M \,×\, 𝒰\, M$ and for morphisms
    $h \;↦\; λ (x,y) → (h\, x, h\, y)$. Then the monoid multiplication (of each monoid) is a natural
    transformation $𝒰 × 𝒰 \natTo 𝒰$, where naturality says that for any monoid homomorphism $h$, the
    application of $𝒰\, h$ to the (monoid) multiplication of two elements is the same as the
    (monoid) multiplication of the $𝒰\, h$ images of the two elements, 
    and this is evident from the homomorphism condition.
    
    Extending to finite products, $ℒ \;≔\; (Σ n ∶ ℕ • ∏ i ∶ 1..n • 𝒰)$, the natural transformation
    $ℒ \natTo 𝒰$ is usually called /fold, reduce, or cata/ and ~ℒ~ is known as the
    /free monoid functor/ with notations $A* \;=\; \List A \;=\; ℒ\, A$.
    
    Loosely put,
    #+BEGIN_EXAMPLE
    ℒ₀    :  Monoid → Set
    ℒ₀ M  =  Σ n ∶ ℕ • ∏ i : 1..n • 𝒰 M   -- finite sequences of elements from M
    
    ℒ₁ : ∀ {M N : Monoid} → (M ⟶ N) → ℒ₀ M → ℒ₀ N
    ℒ₁ (h , prf) = λ (n , x₁, …, xₙ) → (n , h x₁ , … , h xₙ)
    
    fold : ∀ {M : Monoid} → ℒ₀ M → 𝒰₀ M
    fold {(M, ⊕, e)} = λ (n , x₁, …, xₙ) → x₁ ⊕ ⋯ ⊕ xₙ
#+END_EXAMPLE
    
    --The reader would pause to consider implementing this formally using Agda's ~Data.Fin~ and ~Data.Vec~ ;-)--

    Now for any monoid homomorphism ~h~, applying induction, yields
    #+BEGIN_EXAMPLE
    h₀(x₁ ⊕ ⋯ ⊕ xₙ)  =  h₀ x₁ ⊕ ⋯ ⊕ h₀ xₙ  where  h₀ = 𝒰 (h₀, prf) = 𝒰 h
#+END_EXAMPLE
    Which is easily seen to be just naturality -- if we use backwards composition $f ⨾ g \;=\; g ∘ f$ --
    #+BEGIN_EXAMPLE
    𝒰 h ∘ fold {M}  =  fold {N} ∘ ℒ h
#+END_EXAMPLE    
    Woah!
    
+ Every operation in any multisorted algebraic structure gives a natural transformation ::

   This is mentioned in the [[http://www.math.mcgill.ca/triples/Barr-Wells-ctcs.pdf][Barr and Wells' /Category Theory for Computing Science/ text]], citing
   Linton, 1969a-b.
    
   For example, ~src, tgt~ ---from the graph signature--- give natural transformations
   $V \natTo E$ from the vertex functor to the edge functor ... keep reading ;)
   
+ Representability ::
   
   Recall that $V(G)$ is essentially $ℙ₀ ⟶ G$ where
   $ℙₙ$ is the graph of $n$ edges on $n+1$ vertices named $0..n$ with typing $i \,:\, i-1 ⟶ i$,
   which I like to call /the path graph of length n/; and in particular $ℙ₀$ is the graph of
   just one dot, called 0, and no edges. ---Earlier I used the notation ~[n]~, but I’m using $ℙ$ since
   I like the view point of ℙaths.
   
   What does it mean to say that /V(G) is essentially ℙ₀ ⟶ G/?

   It means that the vertices functor 
   -- $𝒱 \;:\; 𝒢𝓇𝒶𝓅𝒽 ⟶ 𝒮ℯ𝓉$ that takes objects $G ↦ V(G)$ and morphisms $h ↦ \mathsf{ver}\, h$ -- 
   can be ‘represented’ as the Hom functor $(ℙ₀ ⟶ \_{})$, that is to say
   \[𝒱 \quad≅\quad (ℙ₀ ⟶ \_{}) \;\mathsf{within \; Func} \; 𝒢𝓇𝒶𝓅𝒽 \; 𝒮ℯ𝓉\] 
   --~Func~-tor categories will be defined in the next section!--

   Notice that we arrived at this expression by
   ‘eta-reducing’ the phrase /V(G) is essentially ℙ₀ ⟶ G/! ;)
   
   More generally, we have the functor $ℙₙ ⟶ \_{}$ which yields all paths of length $n$
   for a given graph.
   
   Observe --i.e., show-- that we also have an edges functor.
   :Solution:
   Recall the ‘untyped edges’, or arrows, ~A(G) ≔ Σ x ∶ V(G) • Σ y ∶ V(G) • (x ⟶ y)~,
   then (arrows) ~𝒜 : Graph ⟶ Set~ takes objects ~G ↦ A(G)~ and morphisms
   ~h ↦ λ (x,y,e) → (ver h x, ver h y, edge h e)~.
   :End:
* /Functor Categories/
:PROPERTIES:
:header-args: :tangle "PathCat.agda" 
:END:

** Intro :ignore:
With a notion of morphisms between functors, one is led inexorably to ask
whether functors as objects and natural transformations as morphisms constitute
a category?
They do!
However, we leave their definition to the reader ---as usual, if the reader is ever so desperate
for solutions, they can be found as comments in the unruliness that is the source file.
#+BEGIN_EXAMPLE
 instance
  Func       :  ∀ {i j i’ j’} (𝒞 : Category {i} {j}) (𝒟 : Category {i’} {j’}) → Category _
  Func 𝒞 𝒟  =  {! exercise !}
#+END_EXAMPLE

+ A hint: The identity natural transformation is the obvious way to get from $F\, X$ to $F\, X$,
  for any $X$ given $F$ ---well the only way to do so, without assuming anything else about the
  functor $F$, is simply $\Id_{F X}$. This is the ‘natural’ choice, any other choice would be
  ‘unnatural’ as it would require some ‘cleverness’. 

+ Another hint: The obvious way to define $η ⨾ γ$ to get $F\, X ⟶ H\, X$ from 
  $F\, X ⟶ G\, X ⟶ H\, X$ is composition of morphisms in the category!
  That is, pointwise composition. Nothing ‘clever’, just using the obvious candidates!

:Solution:
#+BEGIN_SRC agda
 instance
  Func : ∀ {i j i’ j’} (𝒞 : Category {i} {j}) (𝒟 : Category {i’} {j’}) → Category {ℓsuc (i ⊍ j ⊍ i’ ⊍ j’)} {j’ ⊍ i ⊍ j}
  Func {i} {j} {i’} {j’} 𝒞 𝒟 = record {
      Obj = Functor 𝒞 𝒟
    ; _⟶_ = NatTrans
    ; _⨾_ = λ {A B C} η γ → comp {A} {B} {C} η γ
    ; assoc = λ {F G H K η γ ω} → nattransext {i} {j} {i’} {j’} {𝒞} {𝒟} {F} {K} (comp {F} {H} {K} (comp {F} {G} {H} η γ) ω) (comp {F} {G} {K} η (comp {G} {H} {K} γ ω)) assoc
    ; Id = λ {F} → iden F
    ; leftId = λ {F G η} → nattransext {i} {j} {i’} {j’} {𝒞} {𝒟} {F} {G} (comp {F} {F} {G} (iden F) η) η leftId
    ; rightId = λ {F G η} → nattransext {i} {j} {i’} {j’} {𝒞} {𝒟} {F} {G} (comp {F} {G} {G} η (iden G)) η rightId
    }
    where
      instance
        𝒟′ : Category
        𝒟′ = 𝒟

      iden : (A : Functor 𝒞 𝒟) → NatTrans A A
      iden A = Id , (rightId ⟨≡≡⟩ ≡-sym leftId)

      -- To avoid long wait times, we avoid instance resolution by
      -- making an alias.
      _⨾′_ = Category._⨾_ 𝒟
      infixr 6 _⨾′_

      comp : {A B C : Functor 𝒞 𝒟} → NatTrans A B → NatTrans B C → NatTrans A C
      comp {F} {G} {H} (η , nat) (γ , nat′) = (λ {X} → η {X} ⨾′ γ {X}) , (λ {A B f} → begin
           mor F f ⨾′ η {B} ⨾′ γ {B}
          ≡⟨ ≡-sym assoc ⟨≡≡⟩ (≡-cong₂ _⨾′_ nat ≡-refl ⟨≡≡⟩ assoc) ⟩
            η {A} ⨾′ mor G f ⨾′ γ {B}
          ≡⟨ ≡-cong₂ _⨾′_ ≡-refl nat′ ⟨≡≡⟩ ≡-sym assoc ⟩
            (η {A} ⨾′ γ {A}) ⨾′ mor H f
          ∎)
#+END_SRC          
:End:

This is a good exercise as it will show you that there is an identity functor and that composition of functors
is again a functor. Consequently, functors are in abundance: Given any two, we can form [possibly] new ones by composition.

# https://math.stackexchange.com/questions/627676/equivalence-of-categories-and-of-their-functor-categories

It is a common construction that when a type $Y$ is endowed with some structure, then we can endow
the function space $X → Y$, where $X$ is any type, with the same structure and we do so
‘pointwise’. This idea is formalised by functor categories.
Alternatively, one can say we have ‘categorified’ the idea; where
/categorification/ is the process of replacing types and functions with categories and
functors and possibly adding some coherence laws.

There are people who like to make a show about how ‘big’ 𝒞𝒶𝓉 or ~Func 𝒞 𝓓~ are;
these people adhere to something called ‘set theory’ which is essentialy type theory but
ignoring types, loosely put they work only with the datatype
#+BEGIN_EXAMPLE
data SET : Set where
  Elem : ∀ {A : Set} → A → SET
#+END_EXAMPLE
Such heathens delegate types-of-types into ‘classes’ of ‘small’ and ‘big’ sets and it’s not
uniform enough for me.
Anyhow, such people would say that functor categories ‘‘cannot be constructed (as sets)’’ unless
one of the categories involved is ‘‘small’’. Such shenanigans is ignored due to the hierarchy of
types we are using :-)

We must admit that at times the usage of a single type, a ‘uni-typed theory’ if you will can be
used when one wants to relise types in an extrinsic fashion rather than think of data as
intrinsically typed --E.g., graphs with ~src, tgt~ /then/ deriving a notion of ‘type’ with ~_⟶_~.
Everything has its place ... nonetheless, I prefer (multi)typed settings!

** Examples

*** All Categories are Functor Categories
Let ~𝟙 ≔ [ • ]~ be the discrete category of one object (and only the identity arrow on it).

Then ~𝒞 ≅ Func 𝟙 𝒞~.

*** Powers of Categories are Functor Categories
Let ~𝟚₀ ≔ [• •]~ be the discrete category of two objects.
  Then the /𝒞-squared/ category can be defined ~𝒞 ⊗ 𝒞 ∶≅ Func 𝟚₀ 𝒞~:
  This category essentially consists of pairs of 𝒞-objects with pairs of 𝒞-arrows
  between them.

  The subscript 0 is commonly used for matters associated with objects and
  the name ~𝟚₀~ is suggestive of the category of 2 objects only.
  
  More generally, if 𝒩 is the discrete category of $n$ objects, then
  the /n/-fold product category is defined by
  ~(∏ i ∶ 1..n • 𝒞) ∶≅ Func 𝒩 𝒞~.

These are also commonly denoted $𝒞^2$ and $𝒞^𝒩$ since they are essentially
products, and more generally ~Func 𝒳 𝒴~ is also denoted 𝒴^𝒳 and referred.
 
*** Arrow Categories
We can add an arrow to ~𝟚₀~ to obtain another category...
  
Let ~𝟚 ≔ • ⟶ •~ be the category of two objects, call them 0 and 1, with one arrow between them.
  Then a functor ~𝟚 ⟶ 𝒞~ is precisely a morphism of 𝒞 and a natural transformation
~f ⟶ g~ boils down to just a pair of morphisms ~(h,k)~ with ~h ⨾ g = f ⨾ k~.

Hence, the /arrow category of 𝒞/ is $𝒞^𝟚 \;≅\; 𝒞^→ \;≅\; \mathsf{Func}\, 𝟚 𝒞$;
which is essentially the category with objects being 𝒞-morphisms and morphisms being /commutative squares/.
  
Notice that a functor can be used to 
+ /select/ two arbitrary 𝒞 objects --if it's source is 𝟚₀
+ /select/ two arbitrary 𝒞 objects with a 𝒞 arrow between them --if it's source is 𝟚
+ /select/ an arbitrary 𝒞 arrow --if it's source is 𝟚

Likewise, a natural transformation can be used to /select/ a commutative diagram.

*** Understand 𝒞 by looking at Functor Categories
It is a common heuristic that when one suspects the /possibility/ of a category ~𝒞~, then one
can make /probes/ to discover its structure. The objects are just functors ~𝟙 ⟶ 𝒞~ and the
morphisms are just functors ~𝟚 ⟶ 𝒞~.

*** Presheaves -- delegating work to 𝒮ℯ𝓉
  
The /category of presheaves of 𝒞/ is the category ~PSh 𝒞 ≔ Func (𝒞 ᵒᵖ) 𝒮e𝓉~.
  
This is a pretty awesome category since it allows nearly all constructions in 𝒮ℯ𝓉 to be
realised! Such as subsets, truth values, and even powersets! All these extra goodies make it
a ‘topos’ aka ‘power allegory’ ---the first is a category that has all finite limits and
a notion of powerset while the second, besides the power part, looks like a totally different beast;
the exhilaration!
  
*** Slice Categories
The /slice category of 𝒞 over B : Obj 𝒞/ is the category ~𝒞 / B ≔ Σ F ∶ Func 𝟚 𝒞 • (F 1 = B)~. 

Essentially it is the category of objects being 𝒞-morphisms with target $B$ 
and morphisms $f ⟶ g$ being $(h,k)$ with $h ⨾ g = f ⨾ k$ but a natural choice for
$k : B ⟶ B$ is $\Id_B$ and so we can use morphism type
$(f ⟶’ g) \;≔\; Σ h : \src f ⟶ \src g \;•\; h ⨾ g = f$.

This is seen by the observation \[(h, k) \;∈\; f ⟶ g \qquad⇔\qquad h \;∈\; (f ⨾ k) ⟶’ g\] 
Of course a formal justification is obtained by showing
\[\_{}⟶\_{} \quad≅\quad \_{}⟶’\_{} \quad \mathsf{within \; Func }\; (𝒞 ᵒᵖ ⊗ 𝒞) 𝒮e𝓉 \]
...which I have not done and so may be spouting gibberish!
   
:Solution:
    The isomorphism is witnessed as follows.
    
    To :: ~(h,k) : f ⟶ g ⇒ h : (f ⨾ k) ⟶’ g~,
    
    from :: ~h : f ⟶’ g ⇒ (h, Id) : f ⟶ g~.
    
    Rid ::
    #+BEGIN_EXAMPLE
        (h , k) : f ⟶ g
    ⇒  h : f ⨾ k ⟶’ g
    ⇒ (h, Id) : f ⨾ k ⟶ g
    ≡ (h , k) : f ⟶ g
    #+END_EXAMPLE
    where the equivalence is just
   ~(h,k) ∈ f ⟶ g ⇔ (h , Id) ∈ (f ⨾ k) ⟶ g~.
    
    Lid ::
    #+BEGIN_EXAMPLE
       h : f ⟶’ g
    ⇒ (h, Id) : f ⟶ g
    ⇒ h : f ⨾ Id ⟶’ g
    ≡ h : f ⟶’ g
    #+END_EXAMPLE
    
    Of course none of this is formal(ly in Agda) and so should be taken with great precaution!
    ---since it may be all wrong!
:End:
    
Just as the type ~Σ x ∶ X • P x~ can be included in the type ~X~, by forgetting the second
component, so too the category ~Σ F ∶ 𝟚 ⟶ 𝒞 • F 1 ≈ B~ can be included into the category
𝒞 and we say it is a /subcategory/ of 𝒞.
    
The notation ~Σ o ∶ Obj 𝒞 • P o~ defines the subcategory of 𝒞 obtained by deleting
all objects not satisfying predicate ~P~ and deleting all morphisms incident to such objects; i.e.,
it is the category 𝒟 with
\[ \Obj 𝒟 \quad≡\quad Σ o ∶ \Obj 𝒞 \,•\, P o    
   \qquad\text{ and }\qquad
   (o , prf) ⟶_𝒟 (o' , prf') \quad≡\quad o ⟶_𝒞 o'
\]
This is the largest/best/universal subcategory of 𝒞 whose objects satisfy $P$.
\\ Formalise this via a universal property ;)

*** Slices of ~𝒮e𝓉~ are Functor Categories

# fibres
\[ \Func \; S \; 𝒮e𝓉  \qquad≅\qquad  𝒮e𝓉 / S \]
Where S in the left is construed as a discrete category and in the right
is construed as an object of 𝒮e𝓉.
    
This is because a functor from a discrete category need only be a function of objects since
there are no non-identity morphisms. That is, a functor $f : S ⟶ 𝒮ℯ𝓉$ 
is determined by giving a set $f\,s$ for each element $s ∈ S$ ---since there are no non-identity morphisms.
Indeed a functor $f : S ⟶ Set$ yields an /S/-targeted
function
\[ (Σ s ∶ S \,•\, f\, s) → S  \quad:\quad λ (s , fs) → s \]
Conversely a function $g : X → S$ yields a functor by sending elements to their pre-image sets:
\[ S ⟶ Set \quad:\quad λ s → (Σ x ∶ X \,•\, g\, x ≡ s)\]
    
Because of this example, ~𝒞 / B~ can be thought of as ‘𝒞-objects indexed by B’
--extending this idea further leads to /fibred categories/.

*** Natural transformations as functor categories
   
In a similar spirit, we can identify natural transformations as functors!
\[\Func \, 𝒞 \, (𝒟 ^ 𝟚) \qquad≅\qquad (Σ F , G ∶ 𝒞 ⟶ 𝒟 \;•\; \mathsf{NatTrans}\, F\, G)\]
   
A functor $N : 𝒞 ⟶ 𝒟 ^ 𝟚$ gives, for each object $C : \Obj 𝒞$ an object in $𝒟 ^ 𝟚$ which
is precisely an arrow in $𝒟$, rewrite it as $N_C : F\,C ⟶ G\,C$ where $F\,C \,≔\, N\, C\, 0$
and $G\, C \,≔\, N\, C\, 1$.

Likewise, for each arrow $f : A ⟶ B$ in 𝒞 we obtain an arrow $N\, f \,:\, N\, A ⟶ N\, B$ 
in $𝒟 ^ 𝟚$ which is precisely a commutative square in 𝒟;
that is, a pair of 𝒟-arrows $(F\,f , G\,f) ≔ N\,f$ 
with $N_A ⨾ G\,f \;=\; F\,f ⨾ N_B$.

Notice that we have implicitly defined two functors $F, G : 𝒞 ⟶ 𝒟$.
Their object and morphism mappings are clear, but what about functoriality? 
We prove it for both $F, G$ together.
   
# \begin{multicols}{2}

_Identity:_
\begin{calc}   
     (F \,\Id \, , \, G\, \Id)
\step{ definition of $F$ and $G$ }
     N \, \Id
\step{ $N$ is a functor }
     \Id \,∶\, 𝒟 ^ 𝟚
\step{ identity in arrow categories }
     (\Id , \Id)
\end{calc}
#   \columnbreak
_Composition:_
\begin{calc}   
     ( F (f ⨾ g) , G (f ⨾ g) )
   \step{ definition of $F$ and $G$ }
     N\, (f ⨾ g)
   \step{ $N$ is a functor }
     N\, f  ⨾  N\, g
   \step{ definition of $F$ and $G$ }
     (F\, f, G\, f) ⨾ (F\,g , G\,g)
   \step{ composition in arrow categories }
     (F\,f ⨾ F\,g , G\,f ⨾ G\,g)
\end{calc}
  # \end{multicols}
   
Sweet!
   
Conversely, given a natural transformation $η : F \overset{.}{⟶} G$
we define a functor $N : 𝒞 ⟶ 𝒟 ^ 𝟚$ by sending objects $C$ to $η_C : F\, C ⟶ G\, C$, 
which is an object is $𝒟 ^ 𝟚$, and sending morphisms $f : A ⟶ B$ to pairs $(G f , F f)$, 
which is a morphism in $𝒟 ^ 𝟚$ due to naturality of η; namely
$η_A ⨾ G\, f \;=\; F\, f ⨾ η_B$. 
It remains to show that $N$ preserves identities and composition --Exercise!
   
Now it remains to show that these two processes are inverses 
and the isomorphism claim is complete. Woah!
   
Similarly, to show
\[ \Func\, (𝟚 ⊗ 𝒞) \, 𝒟 \qquad≅\qquad (Σ F₀ , F₁ ∶ 𝒞 ⟶ 𝒟 • \mathsf{NatTrans}\, F₁ \, F₂)\] 
# It suffices to show that ‘‘the universal property of exponentiation’’
# ~𝒳 ⟶ (𝒵 ^ 𝒴) ≅ (𝒳 ⊗ 𝒴 ⟶ 𝒵~, or more
#   directly: to/from direction obtained 
By setting $H\, i \;=\; Fᵢ$ on objects and likewise for morphisms
but with $H(\Id, 1) \;=\; η$ where $1 : 0 ⟶ 1$ is the non-identity arrow of ~𝟚~.
   
(Spoilers! Alternatively: ~Arr (Func 𝒞 𝒟) ≅ 𝟚 ⟶ 𝒞 ^ 𝒟 ≅ 𝒞 × 𝟚 ⟶ 𝒟~ since ~𝒞𝒶𝓉~ has exponentials,
   and so the objects are isomorphic; i.e., natural transformations correspond to functors ~𝒞×𝟚⟶𝒟~)
   
   Why are we mentioning this alternative statement? Trivia knowledge of-course!

   On a less relevant note, if you’re familiar with the theory of stretching-without-tearing,
   formally known as topology which is pretty awesome, then you might’ve heard of paths and
   deformations of paths are known as homotopies which are just continuous functions
   $H : X × I ⟶ Y$ for topological spaces $X, Y,$ and $I \,=\, [0,1]$ being the unit interval in ℝ.
   Letting $𝒥 = 𝟚$ be the ‘categorical interval’ we have that functors $𝒞 × 𝒥 ⟶ 𝒟$
   are, by the trivia-relevant result, the same as natural transformations.
   That is, /natural transformations extend the notion of homotopies, or path-deformations./
   
On [[http://mathoverflow.net/a/75686/42716][mathoverflow]], the above is recast succinctly as:
   A natural transformation from $F$ to $G$ is a functor, 
   targeting an arrow category, whose ‘source’
   is $F$ and whose ‘target’ is $G$.
   \[
       \hspace{-2em} F \overset{.}{⟶} G : 𝒞 ⟶ 𝒟 \qquad≅\qquad 
       Σ η ∶ 𝒞 ⟶ \mathsf{Arr}\, 𝒟 •\; \mathsf{Src} ∘ η = F \;\;∧\;\; \mathsf{Tgt} ∘ η = G
   \]
   Where, the projection functors
   \begin{align*}
      \mathsf{Src}&                              &:& \mathsf{Arr}\, 𝒟 ⟶ 𝒟
   \\ \mathsf{Src}& (A₁ , A₂ , f)                &=& A₁
   \\ \mathsf{Src}& (f  , g  , h₁ , h₂ , proofs) &=& h₁
   \end{align*}
   with $\mathsf{Tgt}$ returning the other indexed items.
   
** Graphs as functors

We give an example of a functor by building on our existing graphs setup.
After showing that graphs correspond to certain functors, we then
mention that the notion of graph-map is nothing more than the associated
natural transformations!

#+BEGIN_SRC agda
 module graphs-as-functors where
#+END_SRC

Let us construct our formal graph category, which contains the ingredients for
a graph and a category and nothing more than the equations needed of a category.
The main ingredients of a two-sorted graph are two sort-symbols ~E, V~, along with
two function-symbols ~s, t~ from ~E~ to ~V~ ---this is also called ‘the signature
of graphs’. To make this into a category, we need function-symbols ~id~ and a composition
for which it is a unit.
#+BEGIN_SRC agda
  -- formal objects
  data 𝒢₀ : Set where E V : 𝒢₀

  -- formal arrows
  data 𝒢₁ : 𝒢₀ → 𝒢₀ → Set where
     s t : 𝒢₁ E V              
     id  : ∀ {o} → 𝒢₁ o o 

  -- (forward) composition
  fcmp : ∀ {a b c} → 𝒢₁ a b → 𝒢₁ b c → 𝒢₁ a c
  fcmp f id = f
  fcmp id f = f
#+END_SRC

Putting it all together,
#+BEGIN_SRC agda
  instance
   𝒢 : Category
   𝒢 = record
        { Obj     = 𝒢₀
        ; _⟶_     = 𝒢₁
        ; _⨾_     = fcmp
        ; assoc   = λ {a b c d f g h} → fcmp-assoc f g h
        ; Id      = id
        ; leftId  = left-id
        ; rightId = right-id
        }
    where
       -- exercises: prove associativity, left and right unit laws
#+END_SRC

:Solution:
#+BEGIN_SRC agda
       -- proofs are just C-c C-a after some casing

       fcmp-assoc : ∀ {a b c d} (f : 𝒢₁ a b) (g : 𝒢₁ b c) (h : 𝒢₁ c d) → fcmp (fcmp f g) h ≡ fcmp f (fcmp g h)
       fcmp-assoc s id id = ≡-refl
       fcmp-assoc t id id = ≡-refl
       fcmp-assoc id s id = ≡-refl
       fcmp-assoc id t id = ≡-refl
       fcmp-assoc id id s = ≡-refl
       fcmp-assoc id id t = ≡-refl
       fcmp-assoc id id id = ≡-refl

       right-id : ∀ {a b} {f : 𝒢₁ a b} → fcmp f id ≡ f
       right-id {f = s} = ≡-refl
       right-id {f = t} = ≡-refl
       right-id {f = id} = ≡-refl

       left-id : ∀ {a b} {f : 𝒢₁ a b} → fcmp id f ≡ f
       left-id {f = s} = ≡-refl
       left-id {f = t} = ≡-refl
       left-id {f = id} = ≡-refl
#+END_SRC
:End:
 
Now we can show that every graph ~G~ gives rise to a functor: A semantics of ~𝒢~ in ~𝒮e𝓉~.
#+BEGIN_SRC agda
  toFunc : Graph → Functor 𝒢 𝒮e𝓉
  toFunc G = record 
    { obj  = ⟦_⟧₀ 
    ; mor  = ⟦_⟧₁ 
    ; id   = ≡-refl 
    ; comp = λ {x y z f g} → fcmp-⨾ {x} {y} {z} {f} {g}
    }
    where
      ⟦_⟧₀ : Obj 𝒢 → Obj 𝒮e𝓉
      ⟦ 𝒢₀.V ⟧₀ = Graph.V G
      ⟦ 𝒢₀.E ⟧₀ = Σ x ∶ Graph.V G • Σ y ∶ Graph.V G • Graph._⟶_ G x y
          
      ⟦_⟧₁ : ∀ {x y : Obj 𝒢} → x ⟶ y → (⟦ x ⟧₀ → ⟦ y ⟧₀) 
      ⟦ s ⟧₁ (src , tgt , edg) = src
      ⟦ t ⟧₁ (src , tgt , edg) = tgt
      ⟦ id ⟧₁ x = x

      -- Exercise: fcmp is realised as functional composition
      fcmp-⨾ : ∀{x y z} {f : 𝒢₁ x y} {g : 𝒢₁ y z} → ⟦ fcmp f g ⟧₁ ≡ ⟦ f ⟧₁ ⨾ ⟦ g ⟧₁
#+END_SRC
:Solution:
#+BEGIN_SRC agda
      fcmp-⨾ {f = s} {id} = ≡-refl
      fcmp-⨾ {f = t} {id} = ≡-refl
      fcmp-⨾ {f = id} {s} = ≡-refl
      fcmp-⨾ {f = id} {t} = ≡-refl
      fcmp-⨾ {f = id} {id} = ≡-refl
#+END_SRC
:End:

Conversely, every such functor gives a graph whose vertices and edges are the sets
associated with the sort-symbols ~V~ and ~E~, respectively.
#+BEGIN_SRC agda
  fromFunc : Functor 𝒢 𝒮e𝓉 → Graph
  fromFunc F = record {
      V      = obj F 𝒢₀.V
    ; _⟶_    = λ x y → Σ e ∶ obj F 𝒢₀.E • src e ≡ x × tgt e ≡ y
             -- the type of edges whose source is x and target is y
    }
    where tgt src : obj F 𝒢₀.E → obj F 𝒢₀.V
          src = mor F 𝒢₁.s
          tgt = mor F 𝒢₁.t
#+END_SRC

It is to be noted that we can define ‘‘graphs over 𝒞’’ to be the category ~Func 𝒢 𝒞~.
Some consequences are as follows: Notion of graph in any category, the notion of graph-map
is the specialisation of natural transformation (!), and most importantly, all the power of functor categories
is avaiable for the study of graphs.

In some circles, you may hear people saying an ‘algebra over the signature of graphs’ is an interpretation
domain (~𝒞~) and an operation (~Functor 𝒢 𝒞~) interpreting the symbols. /Nice!/

# We no longer make use of this two-sorted approach to graphs.
#
# Yes, I do: To motivate, rather find, my definition of graphs!
* A few categorical constructions
:PROPERTIES:
:header-args: :tangle "PathCat.agda" 
:END:

We briefly take a pause to look at the theory of category theory.
In particular, we show a pair of constructions to get new categories from old ones,
interpret these constructions from the view of previously mentioned categories, and
discuss how to define the morphism type ~_⟶_~ on morphisms themselves, thereby
yielding a functor.

** Opposite
The ‘dual’ or ‘opposite’ category 𝒞ᵒᵖ is the category constructed from 𝒞 by
reversing arrows: $(A ⟶_{𝒞ᵒᵖ} B) \;≔\; (B ⟶_𝒞 A)$, then necessarily
$(f ⨾_{𝒞ᵒᵖ} g) \;≔\; g ⨾_𝒞 f$.
A ‘contravariant functor’, or ‘cofunctor’, is a functor F from an opposite category and so
there is a reversal of compositions: $F(f \,⨾\, g) \;=\; F g \,⨾\, F f$.
#+BEGIN_EXAMPLE
 _ᵒᵖ : ∀ {i j} → Category {i} {j} → Category
 𝒞 ᵒᵖ = {! exercise !}
#+END_EXAMPLE
:Solution:
#+BEGIN_SRC agda
 _ᵒᵖ : ∀ {i j} → Category {i} {j} → Category {i} {j}
 𝒞 ᵒᵖ         = record {
      Obj     = Obj 𝒞
    ; _⟶_     = λ A B → (B ⟶ A)
    ; _⨾_     = λ f g → (g ⨾ f)
    ; assoc   = ≡-sym assoc
    ; Id      = Id
    ; leftId  = rightId
    ; rightId = leftId
    }
    where instance 𝒞′ : Category ; 𝒞′ = 𝒞
#+END_SRC
:End:

Notice that $(𝒞 ᵒᵖ) ᵒᵖ \;=\; 𝒞$ and $𝒞 ᵒᵖ \;≅\; 𝒞$
--one may have an intuitive idea of what this isomorphsim means,
but formally it is only meaningful in the context of an ambient category; keep reading ;)

We must admit that for categories, the notion of isomorphism is considered less useful
than that of equivalence which weakens the condition of the to-from functors being
inverses to just being naturally isomorphic to identities; C.f., ‘evil’ above.

Some interpretations:

+  𝒮e𝓉ᵒᵖ is usual sets and functions but with ‘backwards composition’:
   #+BEGIN_SRC agda
 infix 10 _∘_
 _∘_ : ∀ {i j } ⦃ 𝒞 : Category {i} {j}⦄ {A B C : Obj 𝒞} → B ⟶ C →  A ⟶ B → A ⟶ C
 f ∘ g = g ⨾ f
#+END_SRC
   Indeed, we have ~g ⨾ f within 𝒞  =  f ∘ g within 𝒞 ᵒᵖ~; which is how these composition operators
    are usually related in informal mathematics (without mention of the ambient categories of course).
   
   On a more serious note, the opposite of 𝒮e𝓉 is clearly 𝓉ℯ𝒮 haha
   ---technically for the purposes of this pun we identify the words ‘opposite’ and ‘reverse’.
   
+
  For a discrete category, its opposite is itself.
  
+
  For a monoid (viewed as a category), its opposite is itself if the monoid operation is commutative, otherwise
  it is the ‘dual monoid’.

+
  For a poset (viewed as a category), its opposite is the ‘dual poset’: $(P, ⊑)ᵒᵖ \;=\; (P, ⊒)$.

  In particular, the ‘least upper bound’, or ‘supremum’ in $(P, ⊑)$ of two elements
  $x,y$ is an element $s$ with the ‘universal property’: $∀ z •\; x ⊑ z ∧ y ⊑ z \;≡\; s ⊑ z$.
  However, switching ⊑ with ⊒ gives us the notion of ‘infimum’, ‘greatest upper bound’!
  So any theorems about supremums automatically hold for infimums since the infifum is nothing
  more than the supremum in the dual category of the poset.

  It is not difficult to see that this idea of “2 for the price of 1” for theorems holds for all
  categories.

+ *Stone Duality:*
  ~FinBoolAlg ≃ FinSets ᵒᵖ~ , witnessed by considering the collection of 
  atoms of a Boolean Algebra in one direction and the power set in the other.
  Finiteness can be removed at the cost of completeness and atomicitiy,
  ~CompleteAtomicBoolAlg ≃ 𝒮ℯ𝓉 ᵒᵖ~.

+ What about the category of functors and natural transformations?

Speaking of functors, we can change the type of a functor by ~ᵒᵖ~-ing its source and target,
while leaving it alone,
#+BEGIN_SRC agda
 -- this only changes type
 opify : ∀ {i j i’ j’} {𝒞 : Category {i} {j}} {𝒟 : Category {i’} {j’}} 
      → Functor 𝒞 𝒟 → Functor (𝒞 ᵒᵖ) (𝒟 ᵒᵖ)
 opify F = record { obj   =  obj F 
                  ; mor   =  mor F 
                  ; id    =  Functor.id F 
                  ; comp  =  Functor.comp F 
                  }
#+END_SRC

#+BEGIN_QUOTE
Category Theory is the ‘op’ium of the people!

--- Karl Marx might say it had cats existed in his time
#+END_QUOTE

This two definitions seem to indicate that we have some form of opposite-functor … ;)
---keep reading!

~opify~ seems to show that ~Functor 𝒞 𝒟 ≡ Functor (𝒞 ᵒᵖ) (𝒟 ᵒᵖ)~, or alternatively a
functor can have ‘two different types’ ---this is akin to using the integers as reals
without writing out the inclusion formally, leaving it implicit; however, in the Agda mechanization
everything must be made explicit ---the type system doesn’t let you get away with such things.
Professor Maarten Fokkinga has informed me that
the formalization allowing multiple-types is called a
[[http://maartenfokkinga.github.io/utwente/mmf92b.pdf][pre-category]].
 
*** ah-yeah: ∂ and dagger categories

With ~𝒞𝒶𝓉~ in-hand, we can formalise the opposite, or ∂ual, functor:
#+BEGIN_SRC agda
 ∂ : ∀ {i j} → Functor (𝒞𝒶𝓉 {i} {j}) 𝒞𝒶𝓉
 ∂ = record { obj = _ᵒᵖ ; mor = opify ; id = ≡-refl ; comp = ≡-refl }
#+END_SRC

Conjecture: Assuming categories are equipped with a contravariant involutionary functor
that is identity on objects, we can show that the identity functor is naturally isomorphic 
to the opposite functor.

#+BEGIN_SRC agda
 ah-yeah : ∀ {i j} (let Cat = Obj (𝒞𝒶𝓉 {i} {j}))
     -- identity on objects cofunctor, sometimes denoted _˘
     → (dual : ∀ (𝒞 : Cat) {x y : Obj 𝒞}  →  x ⟶ y ∶ 𝒞  →  y ⟶ x ∶ 𝒞)
     → (Id˘ : ∀ ⦃ 𝒞 : Cat ⦄ {x : Obj 𝒞} → dual 𝒞 Id  ≡  Id {A = x})
     → (⨾-˘ : ∀ ⦃ 𝒞 : Cat ⦄ {x y z : Obj 𝒞} {f : x ⟶ y} {g : y ⟶ z}
            → dual 𝒞 (f ⨾ g ∶ 𝒞)  ≡  (dual 𝒞 g) ⨾ (dual 𝒞 f) ∶ 𝒞)
     -- which is involutionary
     → (˘˘ : ∀ ⦃ 𝒞 : Cat ⦄ {x y : Obj 𝒞} {f : x ⟶ y} → dual 𝒞 (dual 𝒞 f) ≡ f)
     -- which is respected by other functors
     → (respect : ⦃ 𝒞 𝒟 : Cat ⦄ {F : 𝒞 ⟶ 𝒟} {x y : Obj 𝒞} {f : x ⟶ y}
                → mor F (dual 𝒞 f) ≡ dual 𝒟 (mor F f))
     -- then
     → ∂ ≅ Id within Func (𝒞𝒶𝓉 {i} {j}) 𝒞𝒶𝓉     
#+END_SRC
#+BEGIN_EXAMPLE
 ah-yeah = {! exercise !}
#+END_EXAMPLE
:Solution:
#+BEGIN_SRC agda
 ah-yeah {i} {j} _˘ Id˘ ⨾-˘ ˘˘ respect = record
   { to = II
   ; from = JJ
   ; lid = nattransext {𝒞 = 𝒞𝒶𝓉} {𝒞𝒶𝓉} {∂} {∂} (Category._⨾_ 𝒩𝓉 {∂} {Id} {∂} II JJ) (Category.Id 𝒩𝓉 {∂}) λ {𝒞} → funcext ≡-refl (≡-sym (˘˘ ⦃ 𝒞 ⦄ ))
   ; rid = nattransext {𝒞 = 𝒞𝒶𝓉} {𝒞𝒶𝓉} {Id} {Id} (Category._⨾_ 𝒩𝓉 {Id} {∂} {Id} JJ II) (Category.Id 𝒩𝓉 {Id}) λ {𝒞} → funcext ≡-refl (≡-sym (˘˘ ⦃ 𝒞 ⦄))
   }
   where
   
     𝒩𝓉 = Func (𝒞𝒶𝓉 {i} {j}) (𝒞𝒶𝓉 {i} {j}) -- the category of ~𝒩~atural transormations as morphisms
     
     I : ⦃ 𝒞 : Category {i} {j} ⦄ → Functor (obj ∂ 𝒞) 𝒞
     I ⦃ 𝒞 ⦄ = record { obj = Id ; mor = _˘ 𝒞 ; id = Id˘ ; comp = ⨾-˘ }

     _⨾f_ = Category._⨾_ (𝒞𝒶𝓉 {i} {j})

     Inat : ⦃ 𝒞 𝒟 : Category {i} {j} ⦄ {F : Functor 𝒞 𝒟} → mor ∂ F ⨾f I ⦃ 𝒟 ⦄  ≡  I ⦃ 𝒞 ⦄ ⨾f F
     Inat ⦃ 𝒞 ⦄ ⦃ 𝒟 ⦄ {F} = funcext ⦃ 𝒞 = 𝒞 ᵒᵖ ⦄ ⦃ 𝒟 ⦄ { mor ∂ F ⨾f I ⦃ 𝒟 ⦄ } { I ⦃ 𝒞 ⦄ ⨾f F } ≡-refl λ {x} {y} {f} → respect ⦃ 𝒞 ⦄ ⦃ 𝒟 ⦄ {F} {y} {x} {f}

     II : NatTrans ∂ Id
     II = I , (λ {𝒞} {𝒟} {F} → Inat ⦃ 𝒞 ⦄ ⦃ 𝒟 ⦄ {F})

     J : ⦃ 𝒞 : Category {i} {j} ⦄ → 𝒞 ⟶ obj ∂ 𝒞
     J ⦃ 𝒞 ⦄ = record { obj = Id ; mor = _˘ 𝒞 ; id = Id˘ ; comp = ⨾-˘ }

     Jnat : ⦃ 𝒞 𝒟 : Category {i} {j} ⦄ {F : 𝒞 ⟶ 𝒟}  →  F ⨾f J ⦃ 𝒟 ⦄  ≡  J ⦃ 𝒞 ⦄ ⨾f mor ∂ F
     Jnat ⦃ 𝒞 ⦄ ⦃ 𝒟 ⦄ {F} = funcext ⦃ 𝒞 = 𝒞 ⦄ ⦃ 𝒟 ᵒᵖ ⦄ {F ⨾f J ⦃ 𝒟 ⦄} {J ⦃ 𝒞 ⦄ ⨾f mor ∂ F} ≡-refl (λ {x y f} → respect ⦃ 𝒞 ⦄ ⦃ 𝒟 ⦄ {F} {x} {y} {f})

     JJ : NatTrans ⦃ 𝒞𝒶𝓉 {i} {j} ⦄ ⦃ 𝒞𝒶𝓉 ⦄ Id ∂
     JJ = J , (λ {𝒞} {𝒟} {F} → Jnat ⦃ 𝒞 ⦄ ⦃ 𝒟 ⦄ {F})
#+END_SRC
:End:

Some things to note.

+
  Categories whose morphisms are all isomorphisms are called ‘groupoids’ ---groups are just one-object groupoids.
  Consequently, restricted to groupoids the opposite functor is naturally isomorphic to the identity functor!
  
  In fact, the group case was the motivator for me to conjecture the theorem, which took a while to prove since I hadn’t
  a clue what I needed to assume. Here we’d use ~a ˘ ≔ a ⁻¹~.
   
+
  Consider the category ~Rel~ whose objects are sets and whose morphisms are ‘typed-relations’ $(S, R, T)$, 
  where $R$ is a relation from set $S$ to set $T$, and
  composition is just relational composition
  ---the notion of ‘untyped’, or multi-typed, morphisms is formalized as pre-categories;
  see [[http://maartenfokkinga.github.io/utwente/mmf92b.pdf][Fokkinga]].
  Then we can define an endofunctor by taking ~-˘~ to be relational converse: $x \,(R ˘)\, y \;≡\; y \,R\, x$.
  Consequently, restricted to the category ~Rel~ we have that the opposite functor is naturally isomorphic to the identity functor.
  
  :NeatObservation:
  Indeed, in the proof above, all quantification’s become over a unit type: only possibility is
  ~Rel~.
  
  Then, ~I : Rel ᵒᵖ ⟶ Rel~ and ~J : Rel ⟶ Rel ᵒᵖ~, and the lid-rid proofs amount to saying that
  the two are inverses.
  :End:
  
The above items are instance of a more general concept, of course.

A category with an involutionary contravariant endofunctor that is the identity on objects
is known as /a dagger category, an involutive/star category, or a category with converse/
---and the functor is denoted as a superscript suffix by ~†, *, ˘~, respectively.
The dagger notation probably comes from
the Hilbert space setting while the converse notation comes from the relation algebra setting.
As far as I know, the first two names are more widely known.
A dagger category bridges the gap between arbitrary categories and groupoids.

Just as matrices with matrix multiplication do not form a monoid but rather a category, we have
that not all matrices are invertible but they all admit transposition and so we have a dagger
category. In the same vein, relations admit converse and so give rise to a category with converse.

Besides relations and groupoids, other examples include:
+ discrete categories with the dagger being the identity functor
+ every monoid with an anti-involution is trivially a dagger category; e.g.,
   lists with involution being reverse.
+ commutative monoids are anti-involutive monoids with anti-involution being identity

Spoilers!! Just as the category of categories is carestian closed, so too is the category of dagger
categories and dagger preserving functors --c.f.,the ~respect~ premise above.

:PseudoHeaps:
a pseudoheap is a set H with an binary-operation assigning function  ⟨_⟩ : H → (H × H → H)
such that
mutual-assoc:  (a ⟨b⟩ c) ⟨d⟩ e = a ⟨b⟩ (c ⟨d⟩ e)
commutative: x ⟨a⟩ y = y ⟨a⟩ x

Every involutive monoid is a pseudoheap: x ⟨y⟩ z ≔ x · y ˘ · z
:End:

** Products

For any two categories 𝒞 and 𝒟 we can construct their ‘product’ category
$𝒞 ⊗ 𝒟$ whose objects and morphisms are pairs with components from 𝒞 and 𝒟:
$\Obj\, (𝒞 ⊗ 𝒟) \;\;=\;\; \Obj\, 𝒞 \,×\, \Obj\, 𝒟$ and
$(A , X) ⟶_{𝒞 ⊗ 𝒟} (B , Y) \;\;=\;\; (A ⟶_𝒞 B) \,×\, (X ⟶_𝒟 Y)$.
#+BEGIN_EXAMPLE
 -- we cannot overload symbols in Agda and so using ‘⊗’ in-place of more common ‘×’.
 _⊗_ : ∀ {i j i’ j’} → Category {i} {j} → Category {i’} {j’} → Category
 𝒞 ⊗ 𝒟 = {! exercise !}
#+END_EXAMPLE
:Solution:
#+BEGIN_SRC agda
 infix 5 _⊗_
 _⊗_ : ∀ {i j i’ j’} → Category {i} {j} → Category {i’} {j’} → Category {i ⊍ i’} {j ⊍ j’}
 𝒞 ⊗ 𝒟 = record
           { Obj = Obj 𝒞 × Obj 𝒟
           ; _⟶_ = λ{ (A , X) (B , Y)  →  (A ⟶ B) × (X ⟶ Y) }
           ; _⨾_ = λ{ (f , k) (g , l) → (f ⨾ g , k ⨾ l) }
           ; assoc = assoc ≡×≡ assoc
           ; Id = Id , Id
           ; leftId = leftId ≡×≡ leftId
           ; rightId = rightId ≡×≡ rightId
           }
           where
             _≡×≡_ : ∀ {i j} {A : Set i} {B : Set j} {a a’ : A} {b b’ : B} → a ≡ a’ → b ≡ b’ → (a , b) ≡ (a’ , b’)
             ≡-refl ≡×≡ ≡-refl = ≡-refl
             instance
               𝒞′ : Category
               𝒞′ = 𝒞
               𝒟′ : Category
               𝒟′ = 𝒟
#+END_SRC
:End:

Observe that in weaker languages, a category is specified by its objects, morphisms, and composition
---the proof obligations are delegated to comments, if they are realized at all.
In such settings, one would need to prove that this construction actually produces a full-fledged
category. Even worse, this proof may be a distance away in some documentation.
With dependent types, our proof obligation is nothing more than another component of the program,
a piece of the category type.

In a similar fashion we can show that the sum of two categories is again a category and in general
we have the same for quantified variants: ~Π 𝒞 ∶ Family • 𝒞~, likewise for ‘Σ’.
For the empty family, the empty sum yields the category ~𝟘~ with no objects and
the empty product yields the category ~𝟙~ of one object.
One can then show the usual ‘laws of arithmetic’ ---i.e., ×,+ form a commutative monoid, up to isomorphism---
hold in this setting: Letting ~★ ∈ {+,×}~, we have
associtivity ~A ★ (B ★ C) ≅ (A ★ B) ★ C~, symmetry ~A ★ B ≅ B ★ A~,
unit ~𝟙 × A ≅ 𝟘 + A ≅ A~, and zero ~𝟘 × A ≅ 𝟘~.
These notions can be defined for any category though the objects may or may not exist
--- in ~𝒮e𝓉~ and ~𝒢𝓇𝒶𝓅𝒽~, for example, they do exist ;) ---and these associated arithmetical
laws also hold.

/Question!/ What of the distributivity law,
~A × (B + C) ≅ (A × B) + (A × C)~, does it hold in the mentioned cases?
Let ~𝒫𝒮e𝓉~ be the category of sets with a distinguished point, i.e.,  ~Σ S : Obj 𝒮e𝓉 • S~, and
functions that preserve the ‘point’, one can then show ---if he or she so desires, and is not
lazy--- that this category has notions of product and sum but distributivity fails.

Some interpretations:
+ 
  For discrete categories, this is the usual Cartesian product.
+
  For monoid (or poset) categories, this says that the product of two monoids (or posets) is again
  a monoid (respectively poset. This follows since the product does not affect the number of
  objects and so the product is again a one-object category, i.e., a monoid (poset respectively).
+ Interestingly, the /sum/ of two monoids is *not* formed by their disjoint union: Instead
  it is the set of all alternating lists of elements from the two given monoids.
  Exercise: Find the associated operation ;-)

As expected, we have projections,
#+BEGIN_SRC agda
 Fst : ∀ {i j i’ j’} {𝒞 : Category {i} {j}} {𝒟 : Category {i’} {j’}} 
     → Functor (𝒞 ⊗ 𝒟) 𝒞
 Fst = record { obj = proj₁ ; mor = proj₁ ; id = ≡-refl ; comp = ≡-refl }

 Snd : ∀ {i j i’ j’} {𝒞 : Category {i} {j}} {𝒟 : Category {i’} {j’}} 
     → Functor (𝒞 ⊗ 𝒟) 𝒟
 Snd = record { obj = proj₂ ; mor = proj₂ ; id = ≡-refl ; comp = ≡-refl }
#+END_SRC

*** Currying

For types we have \[ (𝒳 × 𝒴 ⟶ 𝒵) \quad≅\quad (𝒳 ⟶ 𝒵 ^ 𝒴) \quad≅\quad (𝒴 ⟶ 𝒵 ^ 𝒳)\]
Since categories are essentially types endowed with nifty structure,
we expect it to hold in that context as well.
#+BEGIN_EXAMPLE
  -- Everyone usually proves currying in the first argument,
  -- let’s rebel and do so for the second argument
 curry₂ : ∀ {ix jx iy jy iz jz}
          {𝒳 : Category {ix} {jx}} {𝒴 : Category {iy} {jy}} {𝒵 : Category {iz} {jz}}
        → Functor (𝒳 ⊗ 𝒴) 𝒵 → Functor 𝒴 (Func 𝒳 𝒵)
 curry₂ = {! exercise !}
#+END_EXAMPLE
:Solution:
#+BEGIN_SRC agda
 curry₂ : ∀ {ix jx iy jy iz jz} ⦃ 𝒳 : Category {ix} {jx} ⦄ ⦃ 𝒴 : Category {iy} {jy} ⦄ ⦃ 𝒵 : Category {iz} {jz} ⦄
         → Functor (𝒳 ⊗ 𝒴) 𝒵 → Functor 𝒴 (Func 𝒳 𝒵)
 curry₂ ⦃ 𝒳 = 𝒳 ⦄ ⦃ 𝒴 ⦄ ⦃ 𝒵 ⦄ F = record {
    obj =  funcify
  ; mor =  natify
  ; id =  λ {x} → nattransext {F = funcify x} {funcify x} (natify (Id {A = x})) (Category.Id (Func 𝒳 𝒵) {A = funcify x}) (Functor.id F)
  ; comp =  λ {x y z f g} → nattransext {F = funcify x} {funcify z} (natify (f ⨾ g)) ( Category._⨾_ (Func 𝒳 𝒵) {A = funcify x} {B = funcify y} {C = funcify z} (natify f) (natify g) ) (begin
             mor F (Id , f 𝒴.⨾ g)
           ≡⟨ ≡-cong (λ e → mor F (e , f 𝒴.⨾ g)) (≡-sym 𝒳.rightId) ⟩
             mor F (Id 𝒳.⨾ Id , f 𝒴.⨾ g)
           ≡⟨ functor F preserves-composition ⟩
             mor F (Id , f) 𝒵.⨾ mor F (Id , g)
           ∎) }
  where
        module 𝒳 = Category 𝒳
        module 𝒴 = Category 𝒴
        module 𝒵 = Category 𝒵
        funcify : (y : Obj 𝒴) → Functor 𝒳 𝒵
        funcify = λ Y → record {
            obj = λ X → obj F (X , Y)
          ; mor = λ f → mor F (f , Id ⦃ 𝒴 ⦄ {A = Y})
          ; id = Functor.id F
          ; comp = λ {x y z f g} → begin
                mor F (f 𝒳.⨾ g , Id ⦃ 𝒴 ⦄)
              ≡⟨ ≡-cong (λ x → mor F (f 𝒳.⨾ g , x)) (≡-sym 𝒴.rightId) ⟩
                mor F (f 𝒳.⨾ g , Id 𝒴.⨾ Id)
              ≡⟨ Functor.comp F ⟩
                mor F (f , Id ⦃ 𝒴 ⦄) 𝒵.⨾ mor F (g , Id ⦃ 𝒴 ⦄)
              ∎ }
        
        natify : {x y : Obj 𝒴} → x 𝒴.⟶ y → NatTrans (funcify x) (funcify y)
        natify {x} {y} f = (λ {z} → mor F (Id {A = z} , f)) , (λ {a b g} → begin
                mor F (g , Id) 𝒵.⨾ mor F (Id , f)
              ≡⟨ ≡-sym (functor F preserves-composition) ⟩
                 mor F (g 𝒳.⨾ Id , Id 𝒴.⨾ f)
              ≡⟨ ≡-cong₂ (λ x y → mor F (x , y)) 𝒳.rightId 𝒴.leftId ⟩
                 mor F (g , f)
              ≡⟨ ≡-sym (≡-cong₂ (λ x y → mor F (x , y)) 𝒳.leftId 𝒴.rightId) ⟩
                 mor F (Id 𝒳.⨾ g , f 𝒴.⨾ Id)
              ≡⟨ functor F preserves-composition ⟩
                mor F (Id , f) 𝒵.⨾ mor F (g , Id)
              ∎)
#+END_SRC
:End:

** Pointwise extensions and the hom functor
Just as addition can be extended to number-valued functions pointwise, $f + g \;≔\; λ x → f x + g x$,
we can do the same thing with functors.
#+BEGIN_EXAMPLE
 -- For bifunctor ‘⊕’ and functors ‘F, G’, we have a functor ‘λ x → F x ⊕ G x’
 pointwise : ∀ {ic jc id jd ix jx iy jy}
   {𝒞 : Category {ic} {jc}} {𝒟 : Category {id} {jd}} {𝒳 : Category {ix} {jx}} {𝒴 : Category {iy} {jy}}
   → Functor (𝒳 ⊗ 𝒴) 𝒟 → Functor 𝒞 𝒳 → Functor 𝒞 𝒴
   → Functor 𝒞 𝒟
 pointwise = {! exercise !}
#+END_EXAMPLE
:Solution:
#+BEGIN_SRC agda
 pointwise : ∀ {ic jc id jd ix jx iy jy} {𝒞 : Category {ic} {jc}} {𝒟 : Category {id} {jd}}
   {𝒳 : Category {ix} {jx}} {𝒴 : Category {iy} {jy}}
   (_⊕_ : Functor (𝒳 ⊗ 𝒴) 𝒟) (F : Functor 𝒞 𝒳) (G : Functor 𝒞 𝒴) → Functor 𝒞 𝒟
 pointwise {𝒞 = 𝒞} {𝒟} {𝒳} {𝒴} Bi F G =
   let module 𝒳 = Category 𝒳
       module 𝒴 = Category 𝒴
       module 𝒞 = Category 𝒞
       module 𝒟 = Category 𝒟
   in record {
     obj = λ C → obj Bi (obj F C , obj G C)
   ; mor = λ {x y} x→y → mor Bi (mor F x→y , mor G x→y)
   ; id = λ {x} → begin
          mor Bi (mor F 𝒞.Id , mor G 𝒞.Id)
        ≡⟨ ≡-cong₂ (λ f g → mor Bi (f , g)) (Functor.id F) (Functor.id G) ⟩
          mor Bi (𝒳.Id , 𝒴.Id)
        ≡⟨ functor Bi preserves-identities ⟩
          𝒟.Id
        ∎
   ; comp = λ {x y z x⟶y y⟶z} → begin
       mor Bi (mor F (x⟶y 𝒞.⨾ y⟶z) , mor G (x⟶y 𝒞.⨾ y⟶z))
     ≡⟨ ≡-cong₂ (λ f g → mor Bi (f , g)) (Functor.comp F) (Functor.comp G) ⟩
       mor Bi (mor F x⟶y 𝒳.⨾ mor F y⟶z , mor G x⟶y 𝒴.⨾ mor G y⟶z)
     ≡⟨ functor Bi preserves-composition ⟩
      (mor Bi (mor F x⟶y , mor G x⟶y)) 𝒟.⨾ (mor Bi (mor F y⟶z , mor G y⟶z))
     ∎
     }
#+END_SRC
:End:

By ‘extensionality’ ~p ≡ (proj₁ p , proj₂ p)~, we have that the pointwise extension along the projections
is the orginal operation.
#+BEGIN_SRC agda
 exempli-gratia : ∀ {𝒞 𝒟 𝒳 𝒴 : Category {ℓ₀} {ℓ₀}} (⊕ : Functor (𝒳 ⊗ 𝒴) 𝒟)
                → let _⟨⊕⟩_ = pointwise ⊕
                   in
                      Fst ⟨⊕⟩ Snd ≡ ⊕
 exempli-gratia Bi = funcext (≡-cong (obj Bi) ≡-refl) (≡-cong (mor Bi) ≡-refl)
#+END_SRC

An example bifunctor is obtained by extending the ‘⟶’ to morphisms:
Given ~f : A ⟶ B , g : C ⟶ D~ we define ~(f ⟶ g) : (B ⟶ C) → (A ⟶ C)~ by
~λ h → f ⨾ h ⨾ g~ as this is the only way to define it so as to meet the type requirements.
#+BEGIN_SRC agda
 Hom : ∀ {i j} {𝒞 : Category {i} {j} } → Functor (𝒞 ᵒᵖ ⊗ 𝒞) (𝒮e𝓉 {j})
   -- hence contravariant in ‘first arg’ and covaraint in ‘second arg’
 Hom {𝒞 = 𝒞} =
   let
     module 𝒞 = Category 𝒞
     instance 𝒞′ : Category ; 𝒞′ = 𝒞
     ⨾-cong₂ : ∀ {A B C : Obj 𝒞} {f : A 𝒞.⟶ B} {g g’ : B 𝒞.⟶ C}
             → g ≡ g’ → f 𝒞.⨾ g ≡ f 𝒞.⨾ g’
     ⨾-cong₂  q  =  ≡-cong₂ 𝒞._⨾_ ≡-refl q
   in record {
     obj = λ{ (A , B) →  A ⟶ B }
   ; mor = λ{ (f , g) → λ h → f ⨾ h ⨾ g }
   ; id = extensionality (λ {h} → begin
        Id 𝒞.⨾ h 𝒞.⨾ Id
      ≡⟨ leftId ⟩
        h 𝒞.⨾ Id
      ≡⟨ rightId ⟩
        h
      ∎)
   ; comp =  λ {x y z fg fg’} →
       let (f , g) = fg ; (f’ , g’) = fg’ in extensionality (λ {h} → begin
            (f’ 𝒞.⨾ f) 𝒞.⨾ h 𝒞.⨾ (g 𝒞.⨾ g’)
          ≡⟨ assoc ⟩
            f’ 𝒞.⨾ (f 𝒞.⨾ (h 𝒞.⨾ (g 𝒞.⨾ g’)))
          ≡⟨ ⨾-cong₂ (≡-sym assoc) ⟩
            f’ 𝒞.⨾ ((f 𝒞.⨾ h) 𝒞.⨾ (g 𝒞.⨾ g’))
          ≡⟨ ⨾-cong₂ (≡-sym assoc) ⟩
            f’ 𝒞.⨾ ((f 𝒞.⨾ h) 𝒞.⨾ g) 𝒞.⨾ g’
          ≡⟨ ⨾-cong₂ (≡-cong₂ 𝒞._⨾_ assoc ≡-refl) ⟩
            f’ 𝒞.⨾ (f 𝒞.⨾ h 𝒞.⨾ g) 𝒞.⨾ g’
          ∎)
     }           
#+END_SRC
The naming probably comes from the algebra/monoid case where the functors are
monoid ~hom~-omorphisms. Some prefer to use the name ~Mor~, short for ~mor~-phisms,
and that’s cool too. While Haskell programmers might call this the ~Reader~ functor.

Usual notation for this functor is ~Hom~, but I like Fokkinga’s much better.
He uses ~(_⟶_)~ and writes ~(f ⟶ g) = λ h • f ⨾ h ⨾ g~
---the first argument of Hom is the first argument of the composition and the last
argument to Hom is the last argument of the resulting composition :-)
* 𝒮implicity 𝒰nderlies 𝒞omplexity
:PROPERTIES:
:header-args: :tangle "PathCat.agda"
:END:

** Intro :ignore:

#+BEGIN_QUOTE
One way is to make it so 𝒮imple that there are obviously no deficiencies, and the other way is to
make it so 𝒞omplicated that there are no obvious deficiencies. The first method is far more
difficult. It demands the same skill, devotion, insight, and even inspiration as the discovery of
the simple physical laws which 𝒰nderlie the complex phenomena of nature.

─[[https://en.wikiquote.org/wiki/C._A._R._Hoare][C.A.R. Hoare]]
#+END_QUOTE

#+HTML: <small>
#+BEGIN_CENTER
( The 𝒞omplex philosophy behinds games such as Chess and
[[http://playgo.to/iwtg/en/][Go]] arise from some 𝒮imple board game rules.
)
#+END_CENTER
#+HTML: </small>

In this section we discuss what it means to be a ‘forgetful functor’?
--Also called an `𝒰nderlying functor'.

The modifier ‘forgetful’ is meaningful when there’s a notion of extra structure.
Indeed any functor /F : 𝒞 ⟶ 𝒮/ can be thought of as forgetful by construing the objects of
𝒞 as objects of 𝒮 with extra structure.
Mostly: /You know it (to be forgetful) when you see it!/

** Being forgetful: from injections to faithful functors

A common example from set theory is the ‘inclusion’ of a subset $A$ of $B$, the injection
$ι : A ↪ B : a ↦ a$ ---it is essentially a form of ‘type casting’: $a ∈ A$ and $ι a \;=\; a ∈ B$.
Such injections ‘forget’ the property that the argument is actually a member of a specified
subset. Indeed, construing sets as categories then functions becomes functors and inclusions
are then forgetful functors!

Since a functor /F/ consists of two maps /(F₀, F₁) ≔ (obj F, mor F)/ and some properties, we can speak about properties of the
functor and about properties of either of its maps.
The common definitions are a functor $F$ is:
+ faithful :: If its operation on morphisms is /injective/, and it is
+ full     :: If morphisms starting and ending at /F/ are a result of applying $F$; \\
              i.e., /F₁/ is surjective /on/ the image of /F₀/: \\
              $∀ x,y ∶ Obj \;•\; ∀ g ∶ F₀ x ⟶ F₀ y \;•\; ∃ f ∶ x ⟶ y \;•\; F₁ f = g$.

Now we can generalize the previous example.
Every faithful functor /F : 𝒞 ⟶ 𝒟/ can be construed as forgetful:
The 𝒞-maps can be embedded into the 𝒟-maps, since F is faithful, and so can be thought of
as a special sub-collection of the 𝒟-maps; then $F$ ‘forgets’ the property of being in this
special sub-collection.

Are faithful functors in abundance? Well any functor forgetting only axioms
(and/or structure) is faithful:

  0. Suppose 𝒞 consists of 𝒟 objects satisfying some axioms and 𝒟 maps preserving this structure.
  1. That is, 𝒞 has pairs of 𝒟 objects/morphisms with a proof that it satisfies the axioms/preserves-structure.
  2. Then “$F : 𝒞 ⟶ 𝒟$ forgets only axioms” means $F\, (f, \mathsf{proof}) \;=\; f$.
  3. Now given, $F (f , prf) = F (g , prf) \;⇔\; f = g \;⇔\; (f , prf) = (g , prf)$
     -- equality does not (extensionally) depend on proof components.
  
     Hence, faithful :-)

    (Likewise for forgetting extra structure).

Of course we’re not saying all forgetful functors are necessarily faithful.
A simple counterexample is the absolute value function:
Given a real number $x$ it’s absolute value $∣x∣$ is obtained by totally ignoring its sign
---of course $x$ and $∣x∣$ are equidistant from 0, the relation equidistant-from-0 is an equivalence
relation --Exercise!--, and so the the two are isomorphic in some sense.

:Solution:
E is an equivalence, where x E y ≡ ∣ x - y ∣ = 0

+ Refl: x E x ⇐ ∣ x - x ∣ = 0 ⇐ ⊤
+ Sym:  x E y ⇒ ∣x - y∣ = 0 ⇒ ∣y - x∣ = 0 ⇒ y E x
+ Trans: x E y E z ⇒ ∣x - y∣ = ∣y - z∣ = 0 ⇒ ∣x - z∣ = ∣x - y + y - z∣ ≤ ∣x - y∣ + ∣y - z∣ = 0 + 0 = 0

A simpler definition of E is x E y ≡ ∣x∣ = ∣y∣
and that is the kernel of the absolute function and so an equivalence.
:End:

Motivated by this, given a set $S$ it’s size is denoted $∣ S ∣$ which totally forgets about the
elements of the set ---of course it can be shown that two sets are isomorphic precisely if they are
equinumerous.

I assume it is with these as motivators, some people write $∣·∣$ for a forgetful functor.

( Exercise: A functor ~F : 𝒞 ≃ 𝒟~ is (part of) an equivalence iff it is full, 
faithful, and ‘‘essentially surjective on objects’’:
 ~∀ D : Obj 𝒟 • Σ C : Obj 𝒞 • F C ≅ D~ ---note the iso. )

** Of basis vectors
If you’ve ever studied abstract algebra ---the math with vector spaces--- then you may recall that
a collection of vectors ℬ is called a ‘basis’ if every vector can be written as a linear
combination of these vectors: For any vector $v$, there are scalars $c₁, …, cₙ$ and vectors
$b₁, …, bₙ$ in ℬ with $v \;=\; c₁·b₁ + ⋯ + cₙ·bₙ$. That is, a basis is a collection of ‘building
blocks’ for the vector space. Then any function $f$ between basis sets immediately lifts to a
linear transformation (think vector space morphism) $F$ as follows: Given a vector $v$, since we
have a basis, we can express it as $c₁·b₁ + ⋯ + cₙ·bₙ$, now define
$F v \;≔\; c₁·(f\, b₁) + ⋯ + cₙ·(f\, bₙ)$. 

Sweet! 

Thus, to define a complicated linear transformation of vector
spaces, it more than suffices to define a plain old simple function of basis sets.
Moreover, by definition, such $F$ maps basis vectors to basis vectors: $f \;=\; ι ⨾ F$ where
$ι : ℬ ↪ 𝒱$ is the inclusion that realises basis vectors as just usual vectors in the vector
space 𝒱.  *Slogan:* 
/Vector space maps are determined by where they send their basis, and basis-vectors
are preserved./

In the case of ~(List A, ++, [])~ we may consider ~A~ to be a ‘basis’ of the monoid ---indeed,
every list can be written as a linear combination of elements of ~A~, given list
~[x₁, …, xₙ] : List A~ we have ~[x₁, …, xₙ] = x₁ + ⋯ + xₙ~ where ~x + y ≔ [x] ++ [y]~.
Reasoning similarly as above, or if you have familiarity with ~foldr , reduce~, we have a *slogan:*
/Monoid homomorphisms from lists are determined by where they send their basis and basis-vectors are preserved./

Now the general case: /$F ⊣ U$ is a (free-forgetful) ‘adjunction’/ means
for functors ‘forget’ $U : 𝒞 ⟶ 𝒮$ and ‘free’ $F : 𝒮 → 𝒞$, we have that
for a given 𝒮imple-object $S$ there’s 𝒮imple-map $ι : S ⟶_𝒮 U\,(F\, S)$ ---a way to realise ‘basis
vectors’--- such that for any 𝒞omplicated-object $C$ and 𝒮imple-maps $φ : S ⟶_𝒮 U\, C$, there is a
unique 𝒞omplicated-map $Φ : F\, S ⟶_𝒞 C$ that preserves the basis vectors: $φ = ι ⨾ U Φ$.

By analogy to the previous two cases, we may
consider $U\, X$ to be a ‘basis’, and make the *slogan*: 
𝒞omplicated-maps from free objects are
determined by where they send their basis and ‘basis vectors’ are preserved.

[ In more categorical lingo, one says $ι$ is the ‘insertion of generators’.
  
  Question: Does the way we took $ι$ in the previous graph show that it is a natural
  transformation $ι : \Id ⟶ F ⨾ U$?
  ---The naturality just says that a ‘homomorphism’ $F f$ on the free object is 
  completely determined by what $f$ does to the generators ;-)
]
 
** Of adjunctions

An adjunction $L ⊣ U$, where the ~L~-ower adjoint is from 𝒮 to 𝒞 and the ~U~-pper adjoint is in
the opposite direction, lends itself to an elemntary interpretation if we consider 𝒞 
to be some universe of 𝒞omplicated items of study, while 𝒮 to be a universe of 𝒮imple
items of study. Then adjointness implies that given a simple-object $S$ and a complicated-object
$C$, a simple-map $X ⟶ U\, C$ corresponds to a complicated-map $L\, S ⟶ C$. To work with
complicated-maps it is more than enough to work with simple-maps!

Formally this correspondence, saying $F : 𝒞 ⟶ 𝒟$ is adjoint to $G : 𝒟 ⟶ 𝒞$, written $F ⊣ G$,
holds precisely when $(F ∘ X ⟶ Y) \;≅\; (X ⟶ G ∘ Y)$ in a functor category:

#+BEGIN_SRC agda
 _⊣₀_ : ∀ {i j} {𝒞 𝒟 : Category {i} {j}} → Functor 𝒞 𝒟 → Functor 𝒟 𝒞 → Set (i ⊍ j)
 _⊣₀_ {𝒞 = 𝒞} {𝒟} F G 
    =
      (F ′ ∘ X  ⟶ₙₐₜ Y)  ≅  (X ⟶ₙₐₜ G ∘ Y)  within  Func (𝒞 ᵒᵖ ⊗ 𝒟) 𝒮e𝓉
   where
     X = Fst ; Y = Snd ; _′ = opify -- only changes types
          
     infix 5 _⟶ₙₐₜ_
     _⟶ₙₐₜ_ : ∀ {i j} {𝒜 : Category {i} {j}} →
            Functor (𝒞 ᵒᵖ ⊗ 𝒟) (𝒜 ᵒᵖ) → Functor (𝒞 ᵒᵖ ⊗ 𝒟) 𝒜 → Functor (𝒞 ᵒᵖ ⊗ 𝒟) 𝒮e𝓉
     _⟶ₙₐₜ_ {i} {j} {𝒜} = pointwise (Hom {i} {j} {𝒜})
#+END_SRC
Note that if we use Agda's built-in rewrite mechanism to add the rule,
#+BEGIN_EXAMPLE
{𝒞 𝒟 : Category {ℓ₀} {ℓ₀}} → Functor (𝒞 ᵒᵖ) (𝒟 ᵒᵖ) ≡ Functor 𝒞 𝒟
#+END_EXAMPLE
then we might be able to get away without using ~opify~.

Anyhow, this says for any objects $X$ and $Y$, the collection of morphisms $(F\, A ⟶ B)$ 
is isomorphic to the collection $(A ⟶ G\, B)$ and naturally so in $A$ and $B$.

Unfolding it, we have
#+BEGIN_SRC agda
 record _⊣_ {i j i’ j’} {𝒞 : Category {i} {j}} {𝒟 : Category {i’} {j’}} 
        (F : Functor 𝒞 𝒟) (G : Functor 𝒟 𝒞)
        : Set (j’ ⊍ i’ ⊍ j ⊍ i) where

   open Category 𝒟 renaming (_⨾_ to _⨾₂_)
   open Category 𝒞 renaming (_⨾_ to _⨾₁_)
   field
     -- ‘left-adjunct’  L ≈ ⌊  and  ‘right-adjunct’  r ≈ ⌈
     ⌊_⌋ : ∀ {X Y} →   obj F X ⟶ Y ∶ 𝒟   →   X ⟶ obj G Y ∶ 𝒞
     ⌈_⌉ : ∀ {X Y} →   X ⟶ obj G Y ∶ 𝒞   →   obj F X ⟶ Y ∶ 𝒟

     -- Adjuncts are inverse operations
     lid : ∀ {X Y} {d : obj F X ⟶ Y ∶ 𝒟} → ⌈ ⌊ d ⌋ ⌉ ≡ d
     rid : ∀ {X Y} {c : X ⟶ obj G Y ∶ 𝒞} → ⌊ ⌈ c ⌉ ⌋ ≡ c

     -- That for a fixed argument, are natural transformations between Hom functors
     lfusion : ∀ {A B C D} {f : A ⟶ B ∶ 𝒞} {ψ : obj F B ⟶ C ∶ 𝒟} {g : C ⟶ D ∶ 𝒟}
             →  ⌊ mor F f ⨾₂ ψ ⨾₂ g ⌋  ≡  f ⨾₁ ⌊ ψ ⌋ ⨾₁ mor G g
     rfusion : ∀ {A B C D} {f : A ⟶ B ∶ 𝒞} {ψ : B ⟶ obj G C ∶ 𝒞} {g : C ⟶ D ∶ 𝒟}
             →  ⌈ f ⨾₁ ψ ⨾₁ mor G g ⌉  ≡  mor F f ⨾₂ ⌈ ψ ⌉ ⨾₂ g
#+END_SRC

# It is interesting to note that here if we omit the types of ~A, B, C, D~ in ~rfusion~
# they can be inffered but that takes too much time for my taste, so I've annotated the types everywhere.
# The more likely to be more costly in terms of resolution time is the composition operation.

This is easier for verifying an adjunction, while the former is easier for remembering and understanding what an adjunction actually is.

:RecallingTypes:
#+BEGIN_EXAMPLE
  Hom : {𝒞 : Category {ℓ₀} {ℓ₀} } → Functor (𝒞 ᵒᵖ ⊗ 𝒞) 𝒮e𝓉
  Y : ∀ {𝒞 𝒟} → Functor (𝒞 ⊗ 𝒟) 𝒟
  X : ∀ {𝒞 𝒟} → Functor (𝒞 ⊗ 𝒟) 𝒞
   pointwise : ∀ {𝒞 𝒳 𝒴 : Category {ℓ₀} {ℓ₀}} {i j} {𝒟 : Category {i} {j}}
   (_⊕_ : Functor (𝒳 ⊗ 𝒴) 𝒟) (F : Functor 𝒞 𝒳) (G : Functor 𝒞 𝒴) → Functor 𝒞 𝒟

  Hom {𝒜} : 𝒜 ᵒᵖ ⊗ 𝒜 ⟶ 𝒮e𝓉
  F : 𝒞 ᵒᵖ ⟶ 𝒟
  X : 𝒞 ᵒᵖ × 𝒟 ⟶ 𝒞 ᵒᵖ
  X ⨾ F : 𝒞 ᵒᵖ × 𝒟 ⟶ 𝒟
  Y : 𝒞 ᵒᵖ × 𝒟 ⟶ 𝒟
#+END_EXAMPLE
:End:

As the slogan goes ‘adjunctions are everywhere’.
They can be said to capture the notions of optimization and efficiency, but also that of simplicity.

For example, the supremum of a function is defined to be an upper bound of its image set and the least such bound.
Formally, this definition carries a few quantifiers and so a bit lengthy.
More elegantly, we can say the supremum operation is left-adjoint to the constant function: \[ \mathsf{sup} ⊣ 𝒦 \]
which means \[ ∀ z •\qquad \mathsf{sup}\, f \,≤\, z \quad⇔\quad f \overset{.}{≤} 𝒦\, z\] 
Where $𝒦\, x\, y \,=\, x$ and the $\overset{.}{≤}$ on the right is the point-wise ordering on functions.
This formulation of supremum is not only shorter to write but easier to use in calculational proofs.

For the efficiency bit, recall that it is efficient to specify a 𝒮imple-map, then use the adjuction, to obtain
a 𝒞omplicated-map. Recall in the last paragraph how we define the super complicated notion of supremum of a function
in terms of the most elementary constant function!

Adjunctions over poset categories are called ‘Galois connections’ and a good wealth of
material on them can be found in nearly any writing by [[http://www.cs.nott.ac.uk/~psarb2/papers/papers.html][Backhouse et. al.]],
while a very accessible introduction is by [[http://www.cs.nott.ac.uk/~psarb2/MPC/galois.ps.gz][Aarts]],
and there is also an Agda mechanisation by [[http://relmics.mcmaster.ca/RATH-Agda/AContext-2.1.pdf][Kahl & Al-hassy]].

Regarding forgetful functors:
Generally, but not always, forgetful functors are faithful and have left adjoints
---because the notion of ‘forget’ ought to have a corresponding notion of ‘free’.
An exception to this is the category of fields, which has a forgetful functor to the
category of sets with no left adjoint. 
# [Source: Wikipedia]
 
** Adjunctions and Representable Functors

Another awesome thing about adjunctions ~L ⊣ U~ is that they give us ‘representable functors’,
  a.k.a. ‘the best kind of functors’, when terminal objects exist.

  - An object ~𝟙~ is ‘terminal’ if for any object ~A~ there is a unique morphism ~! {A} : A ⟶ 𝟙~. 
    In 𝒮ℯ𝓉 we have ~(A ⟶ 𝟙) ≅ 𝟙~ and ~(𝟙 ⟶ A) ≅ A~. 

  - Specialising the adjunction, where ~U : 𝒞 ⟶ 𝒮e𝓉~, to
    a given set ~A~ and ~𝟙~ we obtain ~(L 𝟙 ⟶ A) ≅ (𝟙 ⟶ U A) ≅ U A~ and so one says
    ‘ ~U~ is represented by ~L 𝟙~ ’. 

  - In particular, if 𝒞 is built on 𝒮ℯ𝓉 by adding some structure
    and we are interested in utilising the elements of an object ~A~ 
    then it suffices to utilise the maps ~L 𝟙 ⟶ A~.
  
In the case of a free-forgetful adjunction, this says that 
  /a forgetful functor is represented by the free object with generator ~𝟙~./
  
For example, for monoids the one-point monoid is the terminal object: ~𝟙 ≔ ({*}, ⊕, *)~ with ~x ⊕ y ≔ ⋆~.
Then every monoid-homomorphism from ~𝟙~ just picks out an element of the carrier of a monoid and so
~(𝟙 ⟶ M) ≅ 𝒰 M~ where ~𝒰~ is the forgetful functor for monoids mentioned in the introduction.

** Concluding remarks
A final note about ‘free objects’ ---arising from an adjoint to a forgetful functor.

*‘‘The free object is generic’’*: The only truths provable for the free
object are precisely those that hold for every complicated-object.

(Begin squinting eyes)
\\
This follows from the
definition of adjunction which says we can construct a unique morphism between complicated-objects
from a simple-map and by naturality we may transport any proof for the free object to any
complicated object.
\\
(Feel ‘free’ to stop squinting your eyes)
 

For futher reading consider reading the adjoint article at [[http://www.comicbooklibrary.org/articles/Left_adjoint][the comic book library]]
and for more on the adjective ‘forgetful’ see [[https://ncatlab.org/nlab/show/forgetful+functor][ncatlab]] or [[http://mathworld.wolfram.com/ForgetfulFunctor.html][mathworld]]
A nice list of common free objects can be found on [[https://en.wikipedia.org/wiki/Free_object#List_of_free_objects][wikipedia]].

# ⟦ Challenge; true or false: For forgetful $U : 𝒞 ⟶ 𝒮ℯ𝓉$, 
# a free functor exists when 𝒞 is a monad category over 𝒮ℯ𝓉? ⟧

You might be asking,
 /musa, when am I ever going to encounter this in daily life? In a popular setting?/ 
This concept is everywhere, even inclusions as mentioned earlier are an
instance. For the second question, enjoy listening to
[[https://www.youtube.com/watch?v=BipvGD-LCjU][this lovely musical group]] --they use the words ‘forgetful functors’ ;)

The remainder of this document can be seen as one fully-worked out example of constructing a
free functor for the forgetful 𝒰 defined above from 𝒞𝒶𝓉 to 𝒢𝓇𝒶𝓅𝒽.

** COMMENT Free first-order logics                               :Abandoned:

#+BEGIN_EXAMPLE
module RSD where

  data 𝟙 : Set where ⋆ : 𝟙

  open import Data.Vec renaming (_∷_ to _,,_) -- , already in use for products :/

  data Term (𝒮 : Signature) (Carrier : Set) (Var : Set) : Set where
    var : Var → Term 𝒮 Carrier Var
    con : Carrier → Term 𝒮 Carrier Var
    app : (i : Fin ar) → Vec (Term 𝒮 Carrier Var) (lookup i ar) → Term 𝒮 Carrier Var
    -- ~app i [t₁, …, tₖ]~ read as: apply i-th function-symbol ~fᵢ~ to ~k = arity (fᵢ)~ terms ~t₁, …, tₖ~

  infix 10 _≈_
  _≈_ : {A B : Set} → A → B → A × B
  _≈_ = _,_
  
  record Logic (𝒮 : Signature) (Carrier : Set) (Var : Set) : Set where
    field
      #Eqns : ℕ
      eqns : Vec ((Term 𝒮 Carrier Var) × (Term 𝒮 Carrier Var)) #Eqns

  -- use integers as varaibles
  MyVars = ℕ
  x y z : MyVars
  x = 0
  y = 1
  z = 2
  -- alternative is to parameterise module by a universe of variables.

  MonoidThry : {X : Set} → Logic MonSig X MyVars
  MonoidThry {X} = record { #Eqns = 3 ;
    eqns = ε · var x ≈ var x
      ,, var x · ε ≈ var x
      ,, (var x · var y) · var z ≈ var x · (var y · var z)
      ,, [] }
    where
      -- the function symbols
      u = fromℕ≤ {0} {2} (s≤s z≤n)
      m = fromℕ≤ {1} {2} (s≤s (s≤s z≤n))

      -- conventional monoid notation
      ε : Term MonSig X MyVars
      ε = app u []
      _·_ : (l r : Term MonSig X MyVars) → Term MonSig X MyVars
      _·_ = λ l r → app m (l ,, r ,, [])
#+END_EXAMPLE
* Designing Paths
:PROPERTIES:
:header-args: :tangle "PathCat.agda" 
:END:

# Path definition

#+BEGIN_CENTER
/The “right” definition is hard to obtain!/
#+END_CENTER

** Intro :ignore:

We can now define a ‘path’ of length ~n~ in a graph ~G~ to be a graph-map
~[ n ] ⟶ G~.

#+BEGIN_SRC agda
Path₀ : ℕ → Graph₀ → Set (ℓsuc ℓ₀)
Path₀ n G = [ n ]₀ 𝒢⟶₀ G
#+END_SRC

Unfolding the definition of graph-morphisms, this just says that a path of length ~n~
consists of a sequence ~[v₀, v₁, v₂,  …, vₙ]~ of vertices of ~G~ and a sequence ~[e₀, e₁, …, eₙ₋₁]~ 
of edges of ~G~ with typing ~eᵢ : vᵢ ⟶ vᵢ₊₁~.

The definition is pretty slick! However, as the name suggests, perhaps we can concatenate paths
and it’s not at all clear how to do this for the vertex- and edge- morphisms of the graph-maps
involved, whereas it’s immediately clear how to do this with sequences: We just concatenate the
sequences and ensure the result is coherent.

Since the vertices can be obtained from the edges via ~src~ and ~tgt~, we can dispense with them
and use the definition as outlined above.

#+BEGIN_SRC agda
open import Data.Vec using (Vec ; lookup)

record Path₁ (n : ℕ) (G : Graph₀) : Set (ℓsuc ℓ₀) where
  open Graph₀
  field
    edges     : Vec (E G) (suc n)
    coherency : {i : Fin n} → tgt G (lookup (` i) edges) ≡ src G (lookup (fsuc i) edges)
#+END_SRC
That is, edges ~[e₀, …, eₙ]~ with coherency ~tgt eᵢ ≡ src eᵢ₊₁~.

Great, we’ve cut the definition of ~Path₀~ in half but that fact that we get a raw list of edges
and then need coherency to ensure that it is a well-formed path is still not terribly lovely.
After all, we’re in Agda, we’re among kings, we should be able to form the list in such a way that
the end result is a path. Let’s do that!

Enough of this repetition, let us fix a graph ~G~,
#+BEGIN_SRC agda
module Path-definition-2 (G : Graph₀) where
  open Graph₀ G

  mutual
    data Path₂ : Set where
      _!   : V → Path₂
      cons : (v : V) (e : E) (ps : Path₂) (s : v ≡ src e) (t : tgt e ≡ head₂ ps) → Path₂

    head₂ : Path₂ → V
    head₂ (v !) = v
    head₂ (cons v e p s t) = v
#+END_SRC

Defining paths for the parallel-pair approach to graphs leaves us with the need to carry
proofs around, and this is a tad too clunky in this case. Let's try yet again.

#+BEGIN_SRC agda
module Path-definition-3 (G : Graph) where

  open Graph G

  -- handy dandy syntax
  infixr 5 cons
  syntax cons v ps e = v ⟶[ e ]⟶ ps -- v goes, by e, onto path ps

  -- we want well-formed paths
  mutual
    data Path₃ : Set where
      _!   : (v : V) → Path₃
      cons : (v : V) (ps : Path₃) (e : v ⟶ head₃ ps) → Path₃

    head₃ : Path₃ → V
    head₃ (v !) = v
    head₃ (v ⟶[ e ]⟶ ps) = v

  -- motivation for the syntax declaration above
  example : (v₁ v₂ v₃ : V) (e₁ : v₁ ⟶ v₂) (e₂ : v₂ ⟶ v₃) → Path₃
  example v₁ v₂ v₃ e₁ e₂ = v₁ ⟶[ e₁ ]⟶ v₂ ⟶[ e₂ ]⟶ v₃ !

  end₃ : Path₃ → V
  end₃ (v !) = v
  end₃ (v ⟶[ e ]⟶ ps) = end₃ ps

  -- typed paths; squigarrowright
  record _⇝_ (x y : V) : Set where
    field
      path   : Path₃
      start  : head₃ path ≡ x
      finish : end₃ path  ≡ y
#+END_SRC
This seems great, but there’s always room for improvement:


- Since the ~cons~ constructor's third argument depends on its first, we must
  use a syntax declaration to get the desired look. Such aesthetic is not only
  pleasing but reminiscent of diagrammatic paths;
  moreover, it’s guaranteed to be an actual path and not just an
  alternating lists of vertices and edges.
  Using the clunky ~Path₂~, we’d write
  #+BEGIN_EXAMPLE
  v₁ ⟶[ v₁≈se₁ , e₁ , te₁≈v₂ ]⟶ v₂ ⟶[ v₂≈se₂ , e₂ , te₂≈v₃ ]⟶ v₃ !
  where
  syntax cons v e ps s t = v ⟶[ s , e , t ]⟶ ps
#+END_EXAMPLE
  yuck!

  Finally, the syntax-declaration does not make the emacs agda-mode auto-case using
  the syntax, and so I have to write it out by hand, each time I want to use the syntax.

- Again since ~cons~'s third argument depends on the second argument, we need a mutual
  definition to extract the item of the dependence. Perhaps if we embed this item at
  the type level we may avoid the need of an auxiliary mutually-defined function.

- By defining what the start and finish of a path are, we can assign types to it.
  However, this approach is reminiscent of the parallel-pair approach to graphs,
  as in ~Graph₀~, which we argued is less preferable to the typed-approach to graphs.
  Perhaps defining paths with types by default, we can reap the benefits and simplicity
  of the typed-approach to graphs.

#+BEGIN_SRC agda
module TypedPaths (G : Graph) where

  open Graph G hiding(V)
  open Graph   using (V)
  
  data _⇝_ : V G → V G → Set where
    _!      : ∀ x → x ⇝ x
    _⟶[_]⟶_ : ∀ x {y ω} (e : x ⟶ y) (ps : y ⇝ ω) → x ⇝ ω
#+END_SRC

One might think that since we can write
#+BEGIN_EXAMPLE
  src : {x y : V G} (e : x ⟶ y) → V G
  src {x} {y} e = x
#+END_EXAMPLE
we can again ignore vertices and it suffices to just keep a coherent list of edges.
Then what is an empty path at a vertex? This’ enough to keep vertices around
---moreover, the ensuing terms look like diagrammatic paths! Cool!

#+BEGIN_CENTER
Finding this definitional /form/ was a major hurdle in this endeavour.
#+END_CENTER

** Aside: An Adjunction between 𝒮ℯ𝓉 and 𝒞𝒶𝓉

With paths in hand, we can now consider a neat sequence of [[https://math.stackexchange.com/questions/1640298/coforgetful-functors][exercises]] :-)

0. Show that graphmaps preserve paths: ~(f : G ⟶ H)  → x ⇝ y → fᵥ x ⇝ fᵥ y~;
   this is nothing more than type-preservation for ~f~ to be a functor ~𝒫G ⟶ 𝒫H~ ;)
   
   Hint: This is ~lift~ from the next section.

1. Define
  #+BEGIN_EXAMPLE
a connected b  ≡  (a ⇝ b) ⊎ (b ⇝ a)  --  path “between” a and b; not ‘from a to b’.
#+END_EXAMPLE

2. This is an equivalence relation whose equivalence classes are called /the connected components of G/;
   denote them by ~𝒦G~.

3.  For any category ~𝒞~, define ~𝒦 𝒞 ≔ 𝒦 (𝒰₀ 𝒞)~ which is a subcategory of ~𝒞~.

4.  Phrase the connected components subcategory using a universal property,
   thereby avoiding the need for quotient types.

5. Since graphmaps preserve paths, every graph map can be extended to connected components,
  ~𝒦f : 𝒦G ⟶ 𝒦H : (connected component of x) ↦ (connected component of fᵥ x)~.

7. Hence, we have a functor ~𝒦 : Graph ⟶ Set~.

8. Then there is a natural transformation ~𝒱 ⟶ 𝒦~, where 𝒱 is the vertices functor.

  Hint: Such a transformation means we can realise vertices as connected components and this suggests
  taking assigning a vertex to the connected-component block that contains it.

  :Solution:

Such a transformation means we can realise vertices as connected components and this suggests
taking ~βG : 𝒱G → 𝒦G~ which takes a vertix to the connected-component βlock that contains it.
Then given graph map ~f : G ⟶ H~,
#+BEGIN_EXAMPLE
  𝒱 f ⨾ βG
≡ λ a → the block containing fᵥ a
≡ λ a → 𝒦f (the block containg a)
≡ βH ⨾ 𝒦f
#+END_EXAMPLE
:End:

  yeah!

Finally, if we let ~𝒟 : 𝒮ℯ𝓉 → 𝒞𝒶𝓉~ be the free category functor that associates each set with
the discrete category over it, then we have ~𝒦~ is the associated forgetful functor.

:Solution:

Given a set map ~f : S ⟶ 𝒦 C~, this assigns a connected component for each s of S.
Let ~R c~ be a choice of Representative for an equivalence block, then
f can be made iinto a functor by sending each s, now construed as an object, to the ~C~-object
~R (f s)~.

given a functor ~F : 𝒟 S ⟶ C~, define a set-map that sends each s to the connected component
that contains it, ie ~β~.

now verify the needed laws.

I saw this someplace on stack exchange for the adjoint to the free category functor.
Anyhow, should consider the intution(?) behind this construction since it’s not immediately clear
why the connected components, that or cuz is nearly 6 in the morning and i am needs of sleep.

src :: \url{http://math.stackexchange.com/questions/1640298/coforgetful-functors}

:End:

** Equality Combinators for Paths

Here's a handy-dandy combinator for forming certain equality proofs of paths.
#+BEGIN_SRC agda
  -- Preprend preserves path equality
  ⟶-≡ : ∀{x y ω} {e : x ⟶ y} {ps qs : y ⇝ ω} 
      → ps ≡ qs → (x ⟶[ e ]⟶ ps) ≡ (x ⟶[ e ]⟶ qs)
  ⟶-≡ {x} {y} {ω} {e} {ps} {qs} eq = ≡-cong (λ r → x ⟶[ e ]⟶ r) eq
#+END_SRC
Less usefully, we leave as exercises:
#+BEGIN_EXAMPLE
  edges : ∀ {x ω} (p : x ⇝ ω) → List (Σ s ∶ V G • Σ t ∶ V G • s ⟶ t)
  edges = {! exercise !}

  path-eq : ∀ {x y} {p q : x ⇝ y} → edges p ≡ edges q → p ≡ q
  path-eq = {! exercise !}
#+END_EXAMPLE
Given time, ~path-eq~ could be rewritten so as to be more easily applicable.
For now, two path equality proofs occur in the document and both are realised by
quick-and-easy induction.

:Solution:
#+BEGIN_SRC agda
  open import Data.List using (List ; [] ; _∷_)
  edges : ∀ {x ω} (p : x ⇝ ω) → List (Σ s ∶ V G • Σ t ∶ V G • s ⟶ t)
  edges {x} (.x !) = []
  edges {x} (.x ⟶[ e ]⟶ ps) = (x , _ , e) ∷ edges ps

  path-eq : ∀ {x y} {p q : x ⇝ y} → edges p ≡ edges q → p ≡ q
  path-eq {x} {p = .x !} {q = .x !} pf = ≡-refl
  path-eq {x} {p = .x !} {q = .x ⟶[ e ]⟶ q} ()
  path-eq {x} {p = .x ⟶[ e ]⟶ p} {q = .x !} ()
  path-eq {x} {p = .x ⟶[ e ]⟶ p} {q = .x ⟶[ e₁ ]⟶ q} pf with edges p | pf
  path-eq {x} {p = .x ⟶[ e ]⟶ p} {q = .x ⟶[ .e ]⟶ q} pf | .(edges q) | ≡-refl = ⟶-≡ (path-eq (uncons pf))
    where uncons : ∀{A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
          uncons {A} {x} {.x} {xs} {.xs} ≡-refl = ≡-refl
#+END_SRC            
:End:

** Category of paths over a graph

Now we turn back to the problem of [[https://english.stackexchange.com/a/125659/327685][catenating]] two paths.
#+BEGIN_SRC agda
  infixr 5 _++_

  _++_ : ∀{x y z} → x ⇝ y → y ⇝ z → x ⇝ z
  x ! ++ q           = q                         -- left unit
  (x ⟶[ e ]⟶ p) ++ q = x ⟶[ e ]⟶ (p ++ q)     -- mutual-associativity
#+END_SRC
Notice that the the base case indicate that ~!~ forms a left-unit for ~++~,
while the inductive case says that path-formation associates with path catenation.
Both observations also hold for the definition of list catenation ;-)

If we had not typed our paths, as in ~Path₂~, we would need to carry around a
proof that paths are compatible for concatenation:
#+BEGIN_EXAMPLE
  catenate : (p q : Path) (coh : end p ≡ head q) → Path
  syntax catenate p q compatibility = p ++[ compatibility ] q
#+END_EXAMPLE
Even worse, to show ~p ++[ coh ] q ≡ p ++[ coh’ ] q~ we need to invoke proof-irrelevance of
identity proofs to obtain ~coh ≡ coh’~, each time we want such an equality! Moving the proof
obligation to the type level removes this need.

As can be seen, being type-less is a terrible ordeal.

Just as the first clause of ~_++_~ indicates ~_!~ is a left unit,
#+BEGIN_SRC agda
  leftId : ∀ {x y} {p : x ⇝ y} → x ! ++ p ≡ p
  leftId = ≡-refl
#+END_SRC
Is it also a right identity?
#+BEGIN_SRC agda
  rightId : ∀ {x y} {p : x ⇝ y} → p ++ y ! ≡ p
  rightId {x} {.x} {.x !} = ≡-refl
  rightId {x} {y } {.x ⟶[ e ]⟶ ps} = ≡-cong (λ q → x ⟶[ e ]⟶ q) rightId
#+END_SRC

Is this operation associative?
#+BEGIN_SRC agda
  assoc : ∀{x y z ω} {p : x ⇝ y} {q : y ⇝ z} {r : z ⇝ ω} 
        → (p ++ q) ++ r ≡ p ++ (q ++ r)
  assoc {x} {p = .x !} = ≡-refl
  assoc {x} {p = .x ⟶[ e ]⟶ ps} {q} {r} = ≡-cong (λ s → x ⟶[ e ]⟶ s) (assoc {p = ps})
#+END_SRC
 
Hence, we’ve shown that the paths over a graph ~G~ constitute a category! Let’s call it ~𝒫 G~.

** The 𝒫ath to freedom
In the last section, we showed that the paths over a graph make a category,
#+BEGIN_SRC agda
𝒫₀ : Graph → Category
𝒫₀ G = let open TypedPaths G in
    record
      { Obj     = Graph.V G
      ; _⟶_     = _⇝_
      ; _⨾_     = _++_
      ; assoc   = λ {x y z ω p q r} → assoc {p = p}
      ; Id      = λ {x} → x !
      ; leftId  = leftId
      ; rightId = rightId
      }
#+END_SRC

Can we make ~𝒫~ into a functor by defining it on morphisms?
That is, to lift graph-maps to category-maps, i.e., functors.

#+BEGIN_SRC agda
𝒫₁ : ∀ {G H} → GraphMap G H → Functor (𝒫₀ G) (𝒫₀ H)
𝒫₁ {G} {H} f = record 
    { obj  = ver f 
    ; mor  = amore
    ; id   = ≡-refl 
    ; comp = λ {x} {y} {z} {p} → comp {p = p} 
    }
    where
      open TypedPaths ⦃...⦄ public
      instance G' : Graph ; G' = G
               H' : Graph ; H' = H

      amore : {x y : Graph.V G} →  x ⇝ y → (ver f x) ⇝ (ver f y)
      amore (x !) = ver f x !
      amore (x ⟶[ e ]⟶ p) = ver f x ⟶[ edge f e ]⟶ amore p

      comp : {x y z : Graph.V G} {p : x ⇝ y} {q : y ⇝ z} 
          →  amore (p ++ q)  ≡  amore p ++ amore q
      comp {x} {p = .x !} = ≡-refl    -- since ! is left unit of ++
      comp {x} {p = .x ⟶[ e ]⟶ ps} = ⟶-≡ (comp {p = ps})
#+END_SRC
Sweet!

With these two together, we have that ~𝒫~ is a functor.

#+BEGIN_SRC agda
𝒫 : Functor 𝒢𝓇𝒶𝓅𝒽 𝒞𝒶𝓉
𝒫 = record { obj   = 𝒫₀ 
            ; mor  = 𝒫₁ 
            ; id   = λ {G} → funcext ≡-refl (id ⦃ G ⦄) 
            ; comp = funcext ≡-refl comp 
            }
    where
      open TypedPaths ⦃...⦄
      open Category   ⦃...⦄

      module 𝒞𝒶𝓉   = Category 𝒞𝒶𝓉
      module 𝒢𝓇𝒶𝓅𝒽 = Category 𝒢𝓇𝒶𝓅𝒽

      id : ∀ ⦃ G ⦄ {x y} {p : x ⇝ y} 
        →   mor (𝒞𝒶𝓉.Id {𝒫₀ G}) p  ≡  mor (𝒫₁ (𝒢𝓇𝒶𝓅𝒽.Id)) p
      id {p = x !} = ≡-refl
      id {p = x ⟶[ e ]⟶ ps} = ⟶-≡ (id {p = ps})

      comp : {G H K : Graph} {f : GraphMap G H} {g : GraphMap H K}
           → {x y : Graph.V G} {p : TypedPaths._⇝_ G x y}
           →  mor (𝒫₁ f 𝒞𝒶𝓉.⨾ 𝒫₁ g) p  ≡  mor (𝒫₁ (f 𝒢𝓇𝒶𝓅𝒽.⨾ g)) p
      comp {p = x !} = ≡-refl
      comp {p = x ⟶[ e ]⟶ ps} = ⟶-≡ (comp {p = ps})
#+END_SRC

It seemed prudent in this case to explicitly delimit where the compositions lives
---this is for clarity, since Agda can quickly resolve the appropriate category instances.

Exercise: Show that we have a natural transformation ~Id ⟶ 𝒰 ∘ 𝒫~.
* Free at last 
:PROPERTIES:
:header-args: :tangle "PathCat.agda" 
:END:

** Intro                                                            :ignore:
#+BEGIN_QUOTE 
Free at last, free at last, thank God almighty we are free at last.

-- Martin Luther King Jr.
#
# Martin Luther King Jr., I Have a Dream: Writings and Speeches That Changed the World
#+END_QUOTE

Recall why lists give the ‘free monoid’: We can embed a type $A$ into $\List A$ by the map $[\_{}]$,
and we can lift any map $f : A ⟶ B$ to a monoid map
\[\foldr \; (λ a b → f\, a ⊕ b)\; e \;:\; (\List A ,\_{}++\_{} , []) \,⟶\, (B,\_{}⊕\_{} , e)\]
I.e., $[a₁, …, aₖ] \;↦\; f\, a₁ ⊕ ⋯ ⊕ f\, aₖ$. Moreover
this ‘preserves the basis’ $A$
-- i.e., $∀ a •\; f\, a \,=\, \foldr \,f \,e \, [ a ]$ --
and this lifted map is unique.

Likewise, let us show that $𝒫G$ is the ‘free category’ over the graph $G$.
This amounts to saying that there is a way, a graph-map, say $ι$, that embeds $G$ into $𝒫G$,
and a way to lift any graph-map $f \,:\, G \,𝒢⟶\, 𝒰₀ 𝒞$ to a functor $\mathsf{lift}\, f : 𝒫G ⟶ 𝒞$
that ‘preserves the basis’ $f \;=\; ι ⨾ 𝒰₁ (\mathsf{lift}\, f)$ and uniquely so.

Let’s begin!

#+BEGIN_SRC agda
module freedom (G : Obj 𝒢𝓇𝒶𝓅𝒽) {𝒞 : Category {ℓ₀} {ℓ₀} } where

  open TypedPaths G using (_! ; _⟶[_]⟶_ ;  _⇝_ ; _++_)
  open Category ⦃...⦄

  module 𝒢𝓇𝒶𝓅𝒽 = Category 𝒢𝓇𝒶𝓅𝒽
  module 𝒮ℯ𝓉 = Category (𝒮e𝓉 {ℓ₀})
  module 𝒞 = Category 𝒞
  instance 𝒞′ : Category ; 𝒞′ = 𝒞
#+END_SRC

** Defining the needed operations
The only obvious, and most natural, way to embed a graph into its ‘graph of paths’ is to send
vertices to vertices and edges to paths of length 1.

#+BEGIN_SRC agda
  ι : G ⟶ 𝒰₀ (𝒫₀ G)
  ι = record { ver = Id ; edge = λ {x} {y} e  →  x ⟶[ e ]⟶ (y !) }
#+END_SRC

Given a graph map $f$, following the list-analagoue of $[a₁, …, aₖ] \;↦\; f\, a₁ ⊕ ⋯ ⊕ f\, aₖ$
we attempt to lift the map onto paths by taking the edges $e₁, …, eₖ$ of a path
to a morphism $\edge\, f\, e₁ ⨾ ⋯ ⨾ \edge\, f\, eₖ$.
That is, a path of the form
\[x_0 \xrightarrow{e_1} x_1 \xrightarrow{e_2} x_2 \xrightarrow{e_3} ⋯ \xrightarrow{e_k} x_k \]
Is lifted to the composition of morphisms
\[\mathsf{ver}\, f\, x_0 \xrightarrow{\edge\, f\, e_1} 
   \mathsf{ver}\, f\, x_1 \xrightarrow{\edge\, f\, e_2} 
   \mathsf{ver}\, f\, x_2 \xrightarrow{\edge\, f\, e_3} ⋯ \xrightarrow{\edge\, f\, e_k} 
   \mathsf{ver}\, f\, x_k \]

Of course, we then need to verify that this construction is indeed
functorial.

#+BEGIN_SRC agda
  lift : G ⟶ 𝒰₀ 𝒞  →  𝒫₀ G ⟶ 𝒞
  lift f = record 
     { obj  = λ v → ver f v -- Only way to obtain an object of 𝒞; hope it works!
     ; mor  = fmap 
     ; id   = ≡-refl 
     ; comp = λ {x y z p q} → proof {x} {y} {z} {p} {q}
     }
     where
          fmap : ∀ {x y} → x ⇝ y → ver f x 𝒞.⟶ ver f y
          fmap (y !) = 𝒞.Id
          fmap (x ⟶[ e ]⟶ p) = edge f e 𝒞.⨾ fmap p

          -- homomorphism property
          proof : ∀{x y z} {p : x ⇝ y} {q : y ⇝ z} → fmap (p ++ q) ≡ fmap p 𝒞.⨾ fmap q
          proof {p = ._ !} = ≡-sym 𝒞.leftId
          proof {p = ._ ⟶[ e ]⟶ ps} =  ≡-cong (λ m → edge f e 𝒞.⨾ m) (proof {p = ps}) 
                                     ⟨≡≡⟩ ≡-sym assoc
                                     -- Exercise: Rewrite this calculationally!
#+END_SRC

Now we have the embedding and the lifting, it remains to show that the aforementioned
‘preserves basis’ property holds as does uniqueness.

** Realising the proof-obligations

Let's begin with the ‘basis preservation’ property:

#+BEGIN_SRC agda
  property : ∀{f : G ⟶ 𝒰₀ 𝒞}  →  f  ≡  (ι 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ (lift f))
  property {f} = graphmapext
    -- Proving: ∀ {v} → ver f v ≡ ver (ι 𝒞.⨾ 𝒰₁ (lift f)) v
    -- by starting at the complicated side and simplifying
    (λ {v} → ≡-sym (begin
              ver (ι 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ (lift f)) v
            ≡⟨" definition of ver on composition "⟩′
              (ver ι 𝒮ℯ𝓉.⨾ ver (𝒰₁ (lift f))) v
            ≡⟨" definition of 𝒰₁ says: ver (𝒰₁ F) = obj F "⟩′ 
              (ver ι 𝒮ℯ𝓉.⨾ obj (lift f)) v
            ≡⟨" definition of lift says: obj (lift f) = ver f "⟩′
              (ver ι 𝒮ℯ𝓉.⨾ ver f) v
            ≡⟨" definition of ι on vertices is identity "⟩′
              ver f v
            ∎))
    
    -- Proving: edge (ι ⨾g 𝒰₁ (lift f)) e ≡ edge f e
    (λ {x} {y} {e} → begin
               edge (ι 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ (lift f)) e
             ≡⟨" definition of edge on composition "⟩′
               (edge ι 𝒮ℯ𝓉.⨾ edge (𝒰₁ (lift f))) e
             ≡⟨" definition of 𝒰 says: edge (𝒰₁ F) = mor F "⟩′
               (edge ι 𝒮ℯ𝓉.⨾ mor (lift f)) e
             ≡⟨" definition chasing gives: mor (lift f) (edge ι e) = edge f e ⨾ Id "⟩′
               edge f e 𝒞.⨾ Id
             ≡⟨ 𝒞.rightId ⟩
               edge f e
             ∎)
#+END_SRC

Observe that we simply chased definitions and as such ~graphmapext ≡-refl rightId~ suffices as a proof,
but it’s not terribly clear why, for human consumption, and so we choose to elaborate with the
detail.

Finally, it remains to show that there is a unique way to preserve ‘basis’:

#+BEGIN_SRC agda 
  uniqueness : ∀{f : G ⟶ 𝒰₀ 𝒞} {F : 𝒫₀ G ⟶ 𝒞} → f ≡ (ι 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F) → lift f ≡ F
  uniqueness {.(ι 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F)} {F} ≡-refl = funcext ≡-refl (≡-sym pf)
    where
      pf : ∀{x y} {p : x ⇝ y} →  mor (lift (ι 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F)) p  ≡  mor F p
      pf {x} {.x} {p = .x !} = ≡-sym (Functor.id F)
      pf {x} {y} {p = .x ⟶[ e ]⟶ ps} = begin
         mor (lift (ι 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F)) (x ⟶[ e ]⟶ ps)
       ≡⟨" definition of mor on lift, the inductive clause "⟩′       
         edge (ι 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F) e 𝒞.⨾ mor (lift (ι 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F)) ps
       ≡⟨ ≡-cong₂ 𝒞._⨾_ ≡-refl (pf {p = ps}) ⟩ -- inductive step
         edge (ι 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F) e 𝒞.⨾ mor F ps
       ≡⟨" definition of edge says it preserves composition "⟩′
         (edge ι 𝒮ℯ𝓉.⨾ edge (𝒰₁ F)) e 𝒞.⨾ mor F ps
       ≡⟨" definition of 𝒰 gives: edge (𝒰₁ F) = mor F "⟩′
         (edge ι 𝒮ℯ𝓉.⨾ mor F) e 𝒞.⨾ mor F ps
       ≡⟨" definition of functional composition 𝒮ℯ𝓉 "⟩′
          mor F (edge ι e) 𝒞.⨾ mor F ps
       ≡⟨ ≡-sym (Functor.comp F) {- i.e., functors preserve composition -} ⟩
          mor F (edge ι e ++ ps)
       ≡⟨" definition of embedding and concatenation "⟩′
         mor F (x ⟶[ e ]⟶ ps)
       ∎
#+END_SRC

Challenge:
Define graph-map equality ‘≈g’ by /extensionality/ --two graph maps are equal iff
their vertex /and/ edge maps are extensionally equal. This is far more relaxed
than using propositional equality ‘≡’. Now show the stronger uniqueness claim:
#+BEGIN_EXAMPLE
∀{f : G ⟶ 𝒰₀ 𝒞} {F : 𝒫₀ G ⟶ 𝒞}   →   f  ≈g  (ι ⨾ 𝒰₁ F)   →   lift f  ≡  F
#+END_EXAMPLE

:Solution:
Below is the uniqueness proof before making postulates.

Before postulating extensionality, I used the following notions.

To talk of equations, we need appropriate equalities.

#+BEGIN_SRC agda
  _≈g_ : ∀{G H : Graph} (f g : G ⟶ H) → Set
  _≈g_ {G} {H} f g = Σ veq ∶ (∀ {v} → ver f v ≡ ver g v) •
    (∀ {x y e} → edge g {x} {y} e ≡ ≡-subst₂ (λ a b → Graph._⟶_ H a b) veq veq (edge f {x} {y} e))

  _≋_ : ∀{𝒞 𝒟 : Category} (f g : 𝒞 ⟶ 𝒟) → Set
  F ≋ G = 𝒰₁ F ≈g 𝒰₁ G   -- proofs (x , y) now replaced with: funcext x y
#+END_SRC

Spelled-out:
#+BEGIN_EXAMPLE
_≋_ {G} {H} f g = Σ veq ∶ (∀ {v} → obj f v ≡ obj g v) •
  (∀ {x y e} → mor g {x} {y} e ≡ ≡-subst₂ (λ a b → Category._⟶_ H a b) veq veq (mor f e))
#+END_EXAMPLE

#+BEGIN_SRC agda
-- Since equality of functors makes use of ~subst~s all over the place, we will need
-- a lemma about how ~subst~ factors/distributes over an operator composition.
  subst-dist : ∀ {S : Set} {v v’ : S → Category.Obj 𝒞} (veq : ∀ {z} → v z ≡ v’ z)
         → ∀ x t y {ec : v x 𝒞.⟶ v t} {psc : v t 𝒞.⟶ v y}
         →  
           ≡-subst₂ 𝒞._⟶_ veq veq ec 𝒞.⨾ ≡-subst₂ 𝒞._⟶_ veq veq psc
         ≡ ≡-subst₂ 𝒞._⟶_ veq veq (ec 𝒞.⨾ psc)
  subst-dist veq x t y rewrite veq {x} | veq {t} | veq {y} = ≡-refl

  uniquenessOld : ∀{f : G ⟶ 𝒰₀ 𝒞} {F : 𝒫₀ G ⟶ 𝒞} → f ≈g (ι ⨾ 𝒰₁ F) → lift f ≡ F
  uniquenessOld {f} {F} (veq , eeq) = funcext veq pf
    where
    
      𝒮 : ∀{x y} → ver f x 𝒞.⟶ ver f y → obj F x 𝒞.⟶ obj F y
      𝒮 m = ≡-subst₂ 𝒞._⟶_ veq veq m
      
      pf : ∀{x y} {p : x ⇝ y} → mor F p ≡ 𝒮( mor (lift f) p )
      pf {x} {.x} {.x !} rewrite (veq {x})= Functor.id F
      pf {x} {y}  {.x ⟶[ e ]⟶ ps} rewrite (eeq {e = e}) =  begin
          mor F (x ⟶[ e ]⟶ ps)
       ≡⟨" definition of embedding and concatenation "⟩′
          mor F (edge ι e ++ ps)
       ≡⟨ functor F preserves-composition ⟩
          mor F (edge ι e) 𝒞.⨾ mor F ps
       ≡⟨ ≡-cong₂ 𝒞._⨾_ eeq (pf {p = ps}) ⟩ -- inductive step
          𝒮(edge f e) 𝒞.⨾ 𝒮(mor (lift f) ps)
       ≡⟨ subst-dist veq x _ y ⟩
          𝒮( edge f e 𝒞.⨾ mor (lift f) ps )
       ≡⟨" definition of “mor” on “lift”, the inductive clause "⟩′
          𝒮( mor (lift f) (x ⟶[ e ]⟶ ps) )
       ∎
#+END_SRC       
:End:

** Another freedom proof

However, saying each graph-map gives rise to exactly one unique functor is tantamount to
saying the type ~GraphMap G (𝒰₀ 𝒞)~ is isomorphic to ~Functor (𝒫₀ G) 𝒞~, that is
~(𝒫₀ G ⟶ 𝒞) ≅ (G ⟶ 𝒰₀ 𝒞)~ ---observe that this says we can ‘move’ ~𝒫₀~ from the left to
the right of an arrow at the cost of it (and the arrow) changing.

A few healthy exercises,

#+BEGIN_EXAMPLE
  lift˘ : Functor 𝒫G 𝒞 → GraphMap G (𝒰₀ 𝒞)
  lift˘ F = ι ⨾g 𝒰₁ F  --  i.e., record {ver = obj F , edge = mor F ∘ edge ι}

  rid : ∀{f : GraphMap G (𝒰₀ 𝒞)} → ∀{x y} {e : x ⟶g y} → lift˘ (lift f) ≡ f
  rid = {! exercise !}

  lid : ∀{F : Functor 𝒫G 𝒞} → lift (lift˘ F) ≡ F
  lid = {! exercise !}
#+END_EXAMPLE

One can of course obtain these proofs from the other ones without recourse to definitions,
however for comprehension one would do well to prove them from first principles.
The worked out solutions are available in the literate source file of this document.

:Solutions:
#+BEGIN_SRC agda
  lift˘ : Functor (𝒫₀ G) 𝒞 → GraphMap G (𝒰₀ 𝒞)
  lift˘ F =  ι ⨾ 𝒰₁ F  -- ≡ record {ver = obj F , edge = mor F ∘ edge ι}

  rid₀ : ∀ {f : GraphMap G (𝒰₀ 𝒞)} → ver (lift˘ (lift f)) ≡ ver f
  rid₀ {f} = begin
      ver (lift˘ (lift f))
    ≡⟨" ver of lift˘ ; defn of lift˘ "⟩′ 
      obj (lift f)
    ≡⟨" defn of lift.obj "⟩′
      ver f
    ∎
-- note that ≡-refl would have suffcied, but we show all the steps for clarity, for human consumption!

  open Graph G renaming (_⟶_ to _⟶g_)
  rid₁ : ∀{f : GraphMap G (𝒰₀ 𝒞)} → ∀{x y} {e : x ⟶g y} → edge (lift˘ (lift f)) e ≡ edge f e
  rid₁ {f} {x} {y} {e} = begin
      edge (lift˘ (lift f)) e
    ≡⟨ "lift˘.edge definition" ⟩′
      mor (lift f) (edge ι e)
    ≡⟨ "lift.mor~ on an edge; i.e., the inductive case of fmap" ⟩′
      edge f e 𝒞.⨾ Id
    ≡⟨ 𝒞.rightId ⟩
      edge f e
    ∎

  rid : ∀{f : GraphMap G (𝒰₀ 𝒞)} → lift˘ (lift f) ≡ f
  rid {f} = graphmapext ≡-refl (≡-sym (rid₁ {f}))

  lid₀ : ∀{F : Functor (𝒫₀ G) 𝒞} → obj (lift (lift˘ F)) ≡ obj F
  lid₀ {F} =  begin
      obj (lift (lift˘ F))
    ≡⟨ "obj of lift" ⟩′
      ver (lift˘ F)
    ≡⟨ "ver of lift˘" ⟩′
       obj F
    ∎

  lid₁ : ∀{F : Functor (𝒫₀ G) 𝒞} → ∀ {x y} {p : x ⇝ y} → mor (lift (lift˘ F)) p ≡ mor F p
  lid₁ {F} {x} {.x} {p = (.x) !} = begin
      mor (lift (lift˘ F)) (x !)
    ≡⟨ "mor of lift on !" ⟩′
      𝒞.Id
    ≡⟨ ≡-sym (Functor.id F) ⟩ -- ! is identity path in ~𝒫G~ and functor preserve identites
       mor F (x !)
    ∎
  lid₁ {F} {x} {y} {p = .x ⟶[ e ]⟶ ps} = begin
      mor (lift (lift˘ F)) (x ⟶[ e ]⟶ ps)
    ≡⟨⟩ -- mor on lift on inductive case
      edge (lift˘ F) e 𝒞.⨾ mor (lift (lift˘ F)) ps
    ≡⟨  ≡-cong (λ w → edge (lift˘ F) e 𝒞.⨾ w) (lid₁ {F}) ⟩
      edge (lift˘ F) e 𝒞.⨾ mor F ps
    ≡⟨ "edge on lift˘" ⟩′
      mor F (edge ι e) 𝒞.⨾ mor F ps
    ≡⟨ ≡-sym (Functor.comp F) ⟩ -- factor out Functor.mor
      mor F (edge ι e ++ ps)
    ≡⟨ "defn of ++" ⟩′
      mor F (x ⟶[ e ]⟶ ps)
    ∎

  lid : ∀ {F : Functor (𝒫₀ G) 𝒞} → lift (lift˘ F) ≡ F
  lid  {F} = funcext ≡-refl (≡-sym (lid₁ {F}))

  -- old version
  lift-≈ : ∀{f f’ : GraphMap G (𝒰₀ 𝒞)} → f ≈g f’ → lift f ≋ lift f’
  lift-≈  {f} {f’} (veq , eeq) = veq , (λ {x} {y} {p} → pf {x} {y} {p})
    where
      pf : {x y : V} {p : x ⇝ y} → mor (lift f’) p ≡ ≡-subst₂ 𝒞._⟶_ veq veq (mor (lift f) p)
      pf {x} {.x} {p = .x !} rewrite (veq {x}) = ≡-refl
      pf {x} {y} {p = .x ⟶[ e ]⟶ ps} = begin 
           mor (lift f’) (x ⟶[ e ]⟶ ps)
         ≡⟨⟩
           edge f’ e 𝒞.⨾ mor (lift f’) ps
         ≡⟨ ≡-cong₂ 𝒞._⨾_ eeq (pf {p = ps}) ⟩
           ≡-subst₂ 𝒞._⟶_ veq veq (edge f e) 𝒞.⨾ ≡-subst₂ 𝒞._⟶_ veq veq (mor (lift f) ps) 
         ≡⟨ subst-dist veq x _ y ⟩
            ≡-subst₂ 𝒞._⟶_ veq veq (mor (lift f) (x ⟶[ e ]⟶ ps))
         ∎
#+END_SRC    
:End:
 
We can then provide an alternative, and more succinct, proof of uniqueness for ‘basis preservation’:

#+BEGIN_SRC agda
  uniqueness’  :  ∀{f h}   →    f  ≡  (ι 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ h)   →   lift f  ≡  h
  uniqueness’ {f} {h} f≈ι⨾𝒰₁h = begin
      lift f
    ≡⟨ ≡-cong lift f≈ι⨾𝒰₁h ⟩
      lift (ι 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ h)
    ≡⟨" definition of lift˘ "⟩′
      lift (lift˘ h)
    ≡⟨ lid ⟩
      h
    ∎
#+END_SRC

The difference between this proof and the original one is akin
to the difference between heaven and earth! That or it's much more elegant ;-)
 
** ~𝒫 ⊣ 𝒰~

:RecallingDefinitions:
Following is probably full of type errors, since it’s all by hand!

Anyhow, let’s recall the notion of natural isomorphism, then apply it to adjunctions then to our
particular adjunction for paths.

~F ≅ G~ means ~∀ A : Obj 𝒞 • ∃ Φ : F A ≅ G A • ∀ X Y : Obj 𝒞 • ∀ f : X ⟶ Y • F f ⨾ Φ {Y} ≈ Φ {X} ⨾ G f~
Given f we have two ways to get from F X to G Y:
first lift f to ~F f : F X → F Y~ then shift to ~F f ⨾ Φ {Y} : F X → G Y~,
alternatively we shift then lift to obtain ~Φ {X} ⨾ G f : F X → G Y~
and ideally we’d like to avoid having to make a choice and so request
these two approaches to be the same.

For the case ~F ⊣ G~.

FF := F _ ⟶ _ : 𝒞ᵒᵖ×𝒟 → 𝒟’ : λ (A , B) → F A ⟶ B ; where 𝒟’ is the cats of arrows of ~𝒟~.
                            : λ (m : Mor 𝒞, n : Mor 𝒟) → λ k : F (Tgt m) ⟶𝒟 Src n → F m ⨾ k ⨾ n 


Given m : Xₘ ⟶𝒞 Yₘ and n : Xₙ ⟶𝒟 Yₙ, we have ~(m , n) : (Yₘ , Xₙ) ⟶ (Xₘ , Yₙ)~ is an arrow of ~𝒞ᵒᵖ × 𝒟~.
we have FF (m , n) : (F Yₘ ⟶𝒟 Xₙ) → (F Xₘ ⟶𝒟 Yₙ)
        Φ {A} {B} : (F A ⟶𝒟 B) ≅ (A ⟶𝒞 G B)
then
FF (m , n) ⨾ Φ {Yₘ} {Xₙ} : (F Yₘ ⟶𝒟 Xₙ) → (Xₘ ⟶𝒟 G Yₙ) : k ↦ Φ {Yₘ} {Xₙ} (F m ⨾ k ⨾ n)

Likewise,
GG (m, n) : (Yₘ ⟶𝒞 G Xₙ) → (Xₘ ⟶𝒟 G Yₙ) : k ↦ m ⨾ k ⨾ G n
and thus
Φ {Xₘ} {Yₙ} ⨾ GG (m, n) : (F Yₘ ⟶𝒟 Xₙ) → (Xₘ ⟶𝒟 G Yₙ) : k ↦ m ⨾ Φ {Yₘ} {Xₙ} k ⨾ G n

Hence we need,
~∀ k : F Yₘ ⟶𝒟 Xₙ • Φ {Yₘ} {Xₙ} (F m ⨾ k ⨾ n) ≈ m ⨾ Φ {Yₘ} {Xₙ} k ⨾ G n~

For our case ~𝒫 ⊣ 𝒰~.
Naturality becomes, using ~𝒢~ for ~𝒢𝓇𝒶𝓅𝒽~ and ~𝒞~ for ~𝒞𝒶𝓉~,
~∀ G H : Obj 𝒢𝓇𝒶𝓅𝒽 • ∀ 𝒞 𝒟 : Obj 𝒞𝒶𝓉 • ∀ g : GraphMap G H • ∀ F : Functor 𝒞 𝒟 • 
∀ k : Functor (𝒫 H) 𝒞 • lift˘ {G} {𝒞} (𝒫 g ⨾ k ⨾ F) ≈ g ⨾ lift˘ {H} {𝒞} k ⨾ 𝒰 F~

That is, for every graph map g and functor F, for appropriate functor k we have
~lift˘ (𝒫 g ⨾ k ⨾ F) ≈ g ⨾ lift˘ k ⨾ 𝒰 F~ in the category of graphs.
:End:
 
Thus far, we have essentially shown 
\[(𝒫₀\, G \,⟶\, 𝒞) \quad≅\quad (G \,⟶\, 𝒰₀\, 𝒞)\]
We did so by finding a pair of inverse maps:

#+BEGIN_EXAMPLE
lift   :  (    G ⟶ 𝒰₀ 𝒞)  →  (𝒫₀ G ⟶     𝒞)
lift˘  :  (𝒫₀ G  ⟶    𝒞)  →  (   G ⟶  𝒰₀ 𝒞)
#+END_EXAMPLE

This is nearly ~𝒫 ⊣ 𝒰~ which implies ~𝒫~ is a ‘free-functor’ since it is left-adjoint to a forgetful-functor.

‘Nearly’ since we need to exhibit naturality:
For every graph map ~g~ and functors ~F, k~ we have
~lift˘ (𝒫 g ⨾ k ⨾ F) ≈ g ⨾ lift˘ k ⨾ 𝒰 F~ in the category of graphs.

[[http://maartenfokkinga.github.io/utwente/mmf92b.pdf][Fokkinga (Theorem A.4)]], among others, would call these laws ‘fusion’ 
instead since they inform us how to compose, or ‘fuse’, a morphism with a
~lift˘~-ed morphism: Taking ~F~ to be the identity and remembering that functors preserve
identities, we have that ~g ⨾ lift˘ K ≡ lift˘( 𝒫₁ g ⨾ K)~ --we can push a morphism into a ~lift˘~
at the cost of introducing a ~𝒫₁~; dually for ~lift~-ed morphisms.

First the setup,
#+BEGIN_SRC agda
module _ {G H : Graph} {𝒞 𝒟 : Category {ℓ₀} {ℓ₀}} 
          (g : GraphMap G H) (F : Functor 𝒞 𝒟) where

  private
    lift˘ = λ {A} {C} B → freedom.lift˘ A {C} B
    lift = λ {A} {C} B → freedom.lift A {C} B
  open Category ⦃...⦄

  module 𝒞     = Category 𝒞
  module 𝒟     = Category 𝒟
  module 𝒢𝓇𝒶𝓅𝒽 = Category 𝒢𝓇𝒶𝓅𝒽
  module 𝒞𝒶𝓉   = Category (𝒞𝒶𝓉 {ℓ₀} {ℓ₀})
  module 𝒮ℯ𝓉   = Category (𝒮e𝓉 {ℓ₀})
#+END_SRC

Just as we needed to prove two inverse laws for ~lift~ and ~lift˘~, 
we need two naturality proofs.

#+BEGIN_SRC agda
  naturality˘ : ∀ {K : Functor (𝒫₀ H) 𝒞} 
              →  lift˘ (𝒫₁ g 𝒞𝒶𝓉.⨾ K 𝒞𝒶𝓉.⨾ F)  ≡  (g 𝒢𝓇𝒶𝓅𝒽.⨾ lift˘ K 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F)
  naturality˘ = graphmapext ≡-refl ≡-refl
#+END_SRC

That was easier than assumed! 
Hahaha: Hard to formalise but so easy to prove lolz!
It says we can ‘shunt’ ~lift˘~ into certain compositions at the cost
of replacing functor instances.

Now for the other proof:
#+BEGIN_SRC agda
  naturality : ∀ {k : GraphMap H (𝒰₀ 𝒞)} →     lift (g 𝒢𝓇𝒶𝓅𝒽.⨾ k 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F) 
                                              ≡  (𝒫₁ g 𝒞𝒶𝓉.⨾ lift k 𝒞𝒶𝓉.⨾ F)
  naturality {k} = funcext ≡-refl (λ {x y p} → proof {x} {y} {p})
    where
      open TypedPaths ⦃...⦄
      instance G′ : Graph ; G′ = G
               H′ : Graph ; H′ = H
      proof : ∀ {x y : Graph.V G} {p : x ⇝ y}
            →    mor (𝒫₁ g 𝒞𝒶𝓉.⨾ lift {H} {𝒞} k 𝒞𝒶𝓉.⨾ F) p 
               ≡  mor (lift {G} {𝒟} (g 𝒢𝓇𝒶𝓅𝒽.⨾ k 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F)) p
      proof {p = _ !} = functor (𝒫₁ g 𝒞𝒶𝓉.⨾ lift {H} {𝒞} k 𝒞𝒶𝓉.⨾ F) preserves-identities
      proof {p = x ⟶[ e ]⟶ ps} = begin
            mor (𝒫₁ g 𝒞𝒶𝓉.⨾ lift {H} {𝒞} k 𝒞𝒶𝓉.⨾ F) (x ⟶[ e ]⟶ ps)
         ≡⟨" By definition, “mor” distributes over composition "⟩′
            (mor (𝒫₁ g) 𝒮ℯ𝓉.⨾ mor (lift {H} {𝒞} k) 𝒮ℯ𝓉.⨾ mor F) (x ⟶[ e ]⟶ ps)
         ≡⟨" Definitions of function composition and “𝒫₁ ⨾ mor” "⟩′
            mor F (mor (lift {H} {𝒞} k) (mor (𝒫₁ g) (x ⟶[ e ]⟶ ps)))
                                                  -- This explicit path is in G
         ≡⟨" Lifting graph-map “g” onto a path "⟩′
            mor F (mor (lift {H} {𝒞} k) (ver g x ⟶[ edge g e ]⟶ mor (𝒫₁ g) ps))
                                                  -- This explicit path is in H
         ≡⟨" Definition of “lift ⨾ mor” on inductive case for paths "⟩′
            mor F (edge k (edge g e) 𝒞.⨾ mor (lift {H} {𝒞} k) (mor (𝒫₁ g) ps))
         ≡⟨ functor F preserves-composition ⟩
                mor F (edge k (edge g e))
           𝒟.⨾  mor F (mor (lift {H} {𝒞} k) (mor (𝒫₁ g) ps))
         ≡⟨" Definition of function composition, for top part "⟩′            
               (edge g 𝒮ℯ𝓉.⨾ edge k 𝒮ℯ𝓉.⨾ mor F) e  -- ≈ mor F ∘ edge k ∘ edge g
           𝒟.⨾ (mor (𝒫₁ g) 𝒮ℯ𝓉.⨾ mor (lift {H} {𝒞} k) 𝒮ℯ𝓉.⨾ mor F) ps
         ≡⟨" “𝒰₁ ⨾ edge = mor” and “edge” and “mor” are functorial by definition "⟩′
                edge (g 𝒢𝓇𝒶𝓅𝒽.⨾ k 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F) e 
           𝒟.⨾  mor (𝒫₁ g 𝒞𝒶𝓉.⨾ lift {H} {𝒞} k 𝒞𝒶𝓉.⨾ F) ps
         ≡⟨ {- Inductive Hypothesis: -} ≡-cong₂ 𝒟._⨾_ ≡-refl (proof {p = ps}) ⟩
                edge (g 𝒢𝓇𝒶𝓅𝒽.⨾ k 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F) e 
           𝒟.⨾  mor (lift {G} {𝒟} (g 𝒢𝓇𝒶𝓅𝒽.⨾ k 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F)) ps
         ≡⟨" Definition of “lift ⨾ mor” on inductive case for paths "⟩′
            mor (lift {G} {𝒟} (g 𝒢𝓇𝒶𝓅𝒽.⨾ k 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F)) (x ⟶[ e ]⟶ ps)
         ∎
#+END_SRC        

Formally, we now have an adjunction:
#+BEGIN_SRC agda
𝒫⊣𝒰 : 𝒫 ⊣ 𝒰
𝒫⊣𝒰 = record{
    ⌊_⌋ = lift˘
  ; ⌈_⌉ = lift
  ; lid = lid
  ; rid = λ {G 𝒞 c} → rid {G} {𝒞} {c}
  ; lfusion = λ {G H 𝒞 𝒟 f F K} → naturality˘ {G} {H} {𝒞} {𝒟} f K {F}
  ; rfusion = λ {G H 𝒞 𝒟 f k F} → naturality {G} {H} {𝒞} {𝒟} f F {k} }
  where
    module _ {G : Graph} {𝒞 : Category} where open freedom G {𝒞} public
#+END_SRC
* Folds Over Paths
:PROPERTIES:
:header-args: :tangle "PathCat.agda" 
:END:

** Intro :ignore:
Observe that for the freedom proof we recalled
that ists determine a form of quantification, ‘folding’:
given an operation ⊕, we may form the operation ~[x₁, …, xₖ] ↦ x₁ ⊕ ⋯ ⊕ xₖ~.
Then used that to define our operation ~lift~, whose core was essentially,
#+BEGIN_SRC agda
module folding (G : Graph) where
  open TypedPaths G
  open Graph G
                                              -- Given:
  fold : {X : Set} (v : V → X)               -- realise G's vertices as X elements
         (f : ∀ x {y} (e : x ⟶ y) → X → X) -- realise paths as X elements
       → (∀ {a b} → a ⇝ b → X)            -- Then: Any path is an X value
  fold v f (b !) = v b
  fold v f (x ⟶[ e ]⟶ ps) = f x e (fold v f ps)  
#+END_SRC            

For example, what is the length of a path?
#+BEGIN_SRC agda
  length : ∀{x y} → x ⇝ y → ℕ
  length = fold (λ _ → 0)          -- single walks are length 0.
                (λ _ _ n → 1 + n)  -- edges are one more than the 
                                    -- length of the remaining walk
#+END_SRC
Let’s verify that this is actually what we intend by the length of a path.
#+BEGIN_SRC agda
  length-! : ∀{x} → length (x !) ≡ 0
  length-! = ≡-refl
  -- True by definition of “length”: The first argument to the “fold”

  length-ind : ∀ {x y ω} {e : x ⟶ y} {ps : y ⇝ ω} 
            →  length (x ⟶[ e ]⟶ ps)  ≡  1 + length ps
  length-ind = ≡-refl 
  -- True by definition of “length”: The second-argument to the “fold”
#+END_SRC

Generalising on ~length~, suppose we have a ‘cost function’ ~c~ that assigns a cost of traversing
an edge. Then we can ask what is the total cost of a path:
#+BEGIN_SRC agda
  path-cost : (c : ∀{x y}(e : x ⟶ y) → ℕ) → ∀{x y}(ps : x ⇝ y) → ℕ
  path-cost c = fold (λ _ → 0)           -- No cost on an empty path.
                     (λ x e n → c e + n) -- Cost of current edge plus 
                                          -- cost of remainder of path.
#+END_SRC
Now, we have ~length = path-cost (λ _ → 1)~: Length is just assigning a cost of 1 to each edge.

Under suitable conditions, list fold distributes over list catenation, can we find an analogue
for paths? Yes. Yes, we can:
#+BEGIN_SRC agda
  fold-++ :  ∀{X : Set} {v : V → X} {g : ∀ x {y} (e : x ⟶ y) → X}
          → (_⊕_ : X → X → X)
          → ∀{x y z : V} {p : x ⇝ y} {q : y ⇝ z}
          → (unitl : ∀{x y} → y ≡ v x ⊕ y)        -- Image of ‘v’ is left unit of ⊕
          → (assoc : ∀ {x y z} → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z )  -- ⊕ is associative 
          → let f : ∀ x {y} (e : x ⟶ y) → X → X
                f = λ x e ps → g x e ⊕ ps
             in
               fold v f (p ++ q) ≡ fold v f p ⊕ fold v f q
  fold-++ {g = g} _⊕_ {x = x} {p = .x !} unitl assoc =  unitl
  fold-++ {g = g} _⊕_ {x = x} {p = .x ⟶[ e ]⟶ ps} unitl assoc =
    ≡-cong (λ exp → g x e ⊕ exp) (fold-++ _⊕_ {p = ps} unitl assoc) ⟨≡≡⟩ assoc
#+END_SRC

Compare this with the proof-obligation of ~lift~.

** Lists are special kinds of paths
We called our path catenation ~_++_~, why the same symbol as that for 
list catenation?

How do we interpret a list over $A$ as a graph? 
Well the vertices can be any element of $A$
and an edge $x ⟶ y$ merely indicates that 
‘‘the item after $x$ in the list is the element $y$’’,
so we want it to be always true; or always inhabited 
without distinction of the inhabitant:
So we might as well use a unit type.
#+BEGIN_SRC agda
module lists (A : Set) where

  open import Data.Unit

  listGraph : Graph
  listGraph = record { V = A ; _⟶_ = λ a a’ → ⊤ }
#+END_SRC
I haven’t a clue if this works, you read my reasoning above.

The only thing we can do is test our hypothesis by looking at the 
typed paths over this graph. In particular, we attempt to show every 
non-empty list of $A$’s corresponds to a path. Since a typed path needs
a priori the start and end vertes, let us construe
~List A  ≅  Σ n ∶ ℕ • Fin n → A~ 
--later note that ~Path G  ≅  Σ n ∶ ℕ • [n] 𝒢⟶ G~.
#+BEGIN_SRC agda
  open TypedPaths listGraph
  open folding listGraph

  -- Every non-empty list [x₀, …, xₖ] of A’s corresonds to a path x₀ ⇝ xₖ.
  toPath : ∀{n} (list : Fin (suc n) → A) →  list fzero ⇝ list (fromℕ n)
  toPath {zero} list = list fzero !
  toPath {suc n} list = list fzero ⟶[ tt ]⟶ toPath {n} (λ i → list(fsuc i))
    -- Note that in the inductive case, “list : Fin (suc (suc n)) → A” 
    -- whereas “suc ⨾ list : Fin (suc n) → A”.
    --
    -- For example, if “list ≈ [x , y , z]” yields
    --          “fsuc ⨾ list ≈ [y , z ]” and
    --   “fsuc ⨾ fsuc ⨾ list ≈ [z]”.
#+END_SRC
Hm! Look at that, first guess and it worked! Sweet.

Now let’s realize the list fold as an instance of path fold,
#+BEGIN_SRC agda
  -- List type former
  List = λ (X : Set) → Σ n ∶ ℕ • (Fin n → X)

  -- Usual list folding, but it's in terms of path folding.
  foldr : ∀{B : Set} (f : A → B → B) (e : B) → List A → B
  foldr f e (zero , l) = e
  foldr f e (suc n , l) = fold (λ a → f a e) (λ a _ rem → f a rem) (toPath l)

  -- example
  listLength : List A → ℕ -- result should clearly be “proj₁” of the list, anyhow:
  listLength = foldr 
    (λ a rem → 1 + rem) -- Non-empty list has length 1 more than the remainder.
    0                    -- Empty list has length 0.
#+END_SRC

Let’s prepare for a more useful example
#+BEGIN_SRC agda
  -- Empty list
  [] : ∀{X : Set} → List X
  [] = 0 , λ ()

  -- Cons for lists
  _∷_ : ∀{X : Set} → X → List X → List X
  _∷_ {X} x (n , l) = 1 + n , cons x l
    where
      -- “cons a l  ≈  λ i : Fin (1 + n) → if i ≈ 0 then a else l i”
      cons : ∀{n} → X → (Fin n → X) → (Fin (suc n) → X)
      cons x l fzero = x
      cons x l (fsuc i) = l i
  
  map : ∀ {B} (f : A → B) → List A → List B
  map f =  foldr (λ a rem → f a ∷ rem) []  -- looks like the usual map don’t it ;)

  -- list concatenation
  _++ℓ_ : List A → List A → List A
  l ++ℓ r = foldr _∷_ r l -- fold over ‘l’ by consing its elements infront of ‘r’

  -- Exercise: Write path catenation as a path-fold.
#+END_SRC

These few adventures would suggest that much of list theory can be
brought over to the world of paths. It looks promising, let me know
dear reader if you make progress on related explorations!
* That was fun; Bye! 
:PROPERTIES:
:header-args: :tangle "PathCat.agda" 
:END:

This note took longer to write than I had initally assumed; perhaps I should have taken into
account 
+ Hofstadter’s Law :: 
  It always takes longer than you expect, even when you take into account Hofstadter’s Law.

  ─[[https://en.wikipedia.org/wiki/G%C3%B6del,_Escher,_Bach][Gödel, Escher, Bach: An Eternal Golden Braid]]

Lessons learned:

+ In Agda, Use implicits when possible in-favour of instance variables
  since the former can be inferred from the local context,
  whereas the latter must be resolved using the entire global context
  thereby incurring possibly more unification problems to solve
  thereby costing more time.

+ If you really want to learn something, teach it to someone:
  A proof assistant wont let you get away with skipping over anything!

+ Coming up with the right data representation for the tasks being tackled
  is a matter of discovery!

The astute reader may have noticed that the tone of writing sometimes 
changes drastically. This is because some of this article was written
by me in March 2016 and I wished to preserve interesting writing style
I then had --if anything to contrast with my now somewhat semi-formal style.

This article was motivated while I was reading [[https://www.amazon.ca/Conceptual-Mathematics-First-Introduction-Categories/dp/052171916X][Conceptual Mathematics]]
for fun. One of the problems was to show that paths over a graph form
a category and do so freely. It took me about 20 minutes on paper and pencil,
but this resulting mechanisation took much more time --but it was also
much more fun!

I had fun writing this up & I hope you enjoy it too :-)

+ Highly Recommended Read ::  
  The diligent reader may be interested to know that Maarten Fokkinga has written a very
  accessible and [[http://maartenfokkinga.github.io/utwente/mmf92b.pdf][gentle introduction to category theory using the calculational approach]].

#+HTML: <small>
#+BEGIN_CENTER
( This article is not yet ‘done’, but good enough for now. )
#+END_CENTER
#+HTML: </small>

* COMMENT Setoid Approach                                         :solutions:
Herein are the solutions to a setoid approach going all the way to the
lifting of graphmaps to functors.

I wrote this rushedly; very rough solutions.

#+BEGIN_EXAMPLE
module _ where -- category definitions
 record Category’ {i j k : Level} : Set (ℓsuc (i ⊍ j ⊍ k)) where
  infixr 10 _⨾_
  infix 5 _≈_
  field
    -- graph structure
    Obj’  : Set i
    _⟶_ : Obj’ → Obj’ → Set j

    -- setoid structure
    _≈_  : ∀ {A B} (f g : A ⟶ B) → Set k
    ≈-refl  : ∀ {A B} {f : A ⟶ B} → f ≈ f
    ≈-sym   : ∀ {A B} {f g : A ⟶ B} → f ≈ g → g ≈ f
    ≈-trans : ∀ {A B} {f g h : A ⟶ B} → f ≈ g → g ≈ h → f ≈ h

    -- typed-monoid-like structure
    _⨾_     : ∀{A B C : Obj’} → A ⟶ B → B ⟶ C → A ⟶ C
    ⨾-cong  : ∀ {A B C} {f f’ : A ⟶ B} {g g’ : B ⟶ C} → f ≈ f’ → g ≈ g’ → f ⨾ g ≈ f’ ⨾ g’  
    assoc   : ∀{A B C D} {f : A ⟶ B}{g : B ⟶ C} {h : C ⟶ D} → (f ⨾ g) ⨾ h ≈ f ⨾ (g ⨾ h)
    Id      : ∀{A : Obj’} → A ⟶ A
    leftId  : ∀ {A B} {f : A ⟶ B} → Id ⨾ f ≈ f
    rightId : ∀ {A B} {f : A ⟶ B} → f ⨾ Id ≈ f
 open Category’ ⦃...⦄ renaming (_⟶_ to _⟶’_ ; _⨾_ to _⨾’_ ; Id to Id’ ; leftId to leftId’ ; rightId to rightId’ ; assoc to assoc’ ; _≈_ to _≈’_) public

 record Functor’ {i j k i’ j’ k’} (𝒞 : Category’ {i} {j} {k}) (𝒟 : Category’ {i’} {j’} {k’}) : Set (ℓsuc (i ⊍ j ⊍ k ⊍ i’ ⊍ j’ ⊍ k’)) where
  field
    -- graph-map structure
    obj’  : Category’.Obj’ 𝒞 → Category’.Obj’ 𝒟                               -- object map
    mor’  : ∀{x y : Category’.Obj’ 𝒞} → x ⟶’ y → obj’ x ⟶’ obj’ y    -- morphism preservation

    -- interaction with setoid structure
    cong : ∀ {x y : Category’.Obj’ 𝒞} {f g : x ⟶’ y} → f ≈’ g → mor’ f ≈’ mor’ g

    -- preservation of finite compositions
    id   : ∀{x : Category’.Obj’ 𝒞} → mor’ (Id’ {A = x}) ≈’ Id’       -- identities preservation
    comp : ∀{x y z : Category’.Obj’ 𝒞} {f : x ⟶’ y} {g : y ⟶’ z} → mor’ (f ⨾’ g) ≈’ mor’ f ⨾’ mor’ g  -- composition preservation

 subst-sym : ∀ {a} {A : Set a} (P : A → A → Set) {x x’ y y’ : A} (xeq : x ≡ x’) (yeq : y ≡ y’) {p : P x y} {q : P x’ y’} → q ≡ ≡-subst₂ P xeq yeq p → p ≡ ≡-subst₂ P (≡-sym xeq) (≡-sym yeq) q
 subst-sym P ≡-refl ≡-refl {p} {.p} ≡-refl = ≡-refl

 subst-trans : ∀ {a} {A : Set a} (P : A → A → Set) {x x’ x’’ y y’ y’’ : A} (xeq : x ≡ x’) (yeq : y ≡ y’) (xeq’ : x’ ≡ x’’) (yeq’ : y’ ≡ y’’) {p : P x y} {q : P x’ y’} {r : P x’’ y’’} → r ≡ ≡-subst₂ P xeq’ yeq’ q → q ≡ ≡-subst₂ P xeq yeq p → r ≡ ≡-subst₂ P (xeq ⟨≡≡⟩ xeq’) (yeq ⟨≡≡⟩ yeq’) p
 subst-trans P ≡-refl ≡-refl ≡-refl ≡-refl {p} {.p} {.p} ≡-refl ≡-refl = ≡-refl

       -- this’ like subst-dist, with ~≡-cong~ of two equations using subst
 subst-compose : ∀ {a} {A : Set a} (P : A → A → Set) {x x’ y y’ z z’ : A} (xeq : x ≡ x’) (yeq : y ≡ y’) (zeq : z ≡ z’) (p : P x y) (p’ : P x’ y’) (q : P y z) (q’ : P y’ z’) → (_◇_  : ∀{m n k} → P m n → P n k → P m k) → p’ ≡ ≡-subst₂ P xeq yeq p → q’ ≡ ≡-subst₂ P yeq zeq q → (p’ ◇ q’) ≡ ≡-subst₂ P xeq zeq (p ◇ q)
 subst-compose P ≡-refl ≡-refl ≡-refl p .p q .q _◇_ ≡-refl ≡-refl = ≡-refl
       -- taking cases ~p’ = subst ... p~ and ~q’ = subst ... q~ gives subst-dist ?

 subst-cong : ∀ {a} {A : Set a} (P : A → A → Set) {x x’ y y’ : A} (xeq : x ≡ x’) (yeq : y ≡ y’) {p : P x y} {p’ : P x’ y’} → p’ ≡ ≡-subst₂ P xeq yeq p →
                    ∀ {b} {B : Set b} (Q : B → B → Set) {f₀ : A → B} (f : ∀ {m n} → P m n → Q (f₀ m) (f₀ n)) {f’₀ : A → B} {f’ : ∀ {m n} → P m n → Q (f’₀ m) (f’₀ n)}
                    → (eq₀ : ∀ {x} → f₀ x ≡ f’₀ x) (eq : ∀ {m n} {r : P m n} → f’ r ≡ ≡-subst₂ Q eq₀ eq₀ (f r)) 
                    → f’ p’ ≡ ≡-subst₂ Q (≡-cong f₀ xeq ⟨≡≡⟩ eq₀) (≡-cong f₀ yeq ⟨≡≡⟩ eq₀) (f p)
 subst-cong P ≡-refl ≡-refl {p} {.p} ≡-refl Q f eq₀ eq rewrite eq {r = p} = ≡-refl

 open import Function using (_∘_)
 instance
  𝒞𝒶𝓉’ : Category’ {ℓsuc ℓ₀} {ℓsuc ℓ₀} {_}
  𝒞𝒶𝓉’ =
   record
     { Obj’ = Category’ {ℓ₀} {ℓ₀} {_}
     ; _⟶_ = Functor’
     ; _≈_ = λ {𝒞} {𝒟} F G → Σ oeq ∶ (∀ {o} → Functor’.obj’ F o ≡ Functor’.obj’ G o) • ((∀ {X Y} {f : X ⟶’ Y} → Functor’.mor’ G f ≡ ≡-subst₂ _⟶’_ oeq oeq (Functor’.mor’ F f)))
     ; ≈-refl = ≡-refl , ≡-refl
     ; ≈-sym = λ pf → let (oeq , meq) = pf in ≡-sym oeq , subst-sym _⟶’_ oeq oeq meq
     ; ≈-trans = λ pf1 pf2 → let (oeq₁ , meq₁) = pf1 ; (oeq₂ , meq₂) = pf2 in oeq₁ ⟨≡≡⟩ oeq₂ , subst-trans _⟶’_ oeq₁ oeq₁ oeq₂ oeq₂ meq₂ meq₁
     ; _⨾_ = λ {A} {B} {C} F G → record { obj’ = Functor’.obj’ G ∘ Functor’.obj’ F ; mor’ = Functor’.mor’ G ∘ Functor’.mor’ F ; cong = Functor’.cong G ∘ Functor’.cong F ; id = λ {x} → Category’.≈-trans C (Functor’.cong G (Functor’.id F)) (Functor’.id G) ; comp = Category’.≈-trans C (Functor’.cong G (Functor’.comp F)) (Functor’.comp G) }
     ; ⨾-cong = λ {C D A} {F} {F’} {G} {G’} feq geq → let (oeq₁ , meq₁) = feq ; (oeq₂ , meq₂) = geq in ≡-cong (Functor’.obj’ G) oeq₁ ⟨≡≡⟩ oeq₂ , subst-cong (Category’._⟶_ D) oeq₁ oeq₁ meq₁ (Category’._⟶_ A) (Functor’.mor’ G) oeq₂ meq₂
     ; assoc = ≡-refl , ≡-refl
     ; Id = record { obj’ = λ x → x ; mor’ = λ x → x ; cong = λ {x} {y} {f} {g} z → z ; id = ≈-refl ; comp = ≈-refl }
     ; leftId = ≡-refl , ≡-refl
     ; rightId = ≡-refl , ≡-refl
     }
     where

 instance
  𝒮et’ : Category’
  𝒮et’ =
    record
      { Obj’ = Set
      ; _⟶_ = λ A B → (A → B)
      ; _≈_ = λ f g → ∀ {x} → f x ≡ g x
      ; ≈-refl = ≡-refl
      ; ≈-sym = λ eq → ≡-sym eq
      ; ≈-trans = λ f≈g g≈h → f≈g ⟨≡≡⟩ g≈h
      ; _⨾_ = λ f g → g ∘ f
      ; ⨾-cong = λ {A B C} {f f’} {g g’} f≈f’ g≈g’ → ≡-cong g f≈f’ ⟨≡≡⟩ g≈g’
      ; assoc = ≡-refl
      ; Id = λ x → x
      ; leftId = ≡-refl
      ; rightId = ≡-refl
      }

  -- make this as an excercise, since it is essentially CAT but without extra proof obligations for functors
  𝒢𝓇𝒶𝓅𝒽’ : Category’
  𝒢𝓇𝒶𝓅𝒽’ =
    record
      { Obj’ = Graph
      ; _⟶_ = GraphMap
      ; _≈_ = λ {G} {H} f g → Σ veq ∶ (∀ {v} → ver f v ≡ ver g v) •
    (∀ {x y e} → edge g {x} {y} e ≡ ≡-subst₂ (λ a b → Graph._⟶_ H a b) veq veq (edge f {x} {y} e))
      ; ≈-refl = ≡-refl , ≡-refl
      ; ≈-sym = λ f≈g → let (veq , eeq) = f≈g in ≡-sym veq , subst-sym (Graph._⟶_ _) veq veq eeq
      ; ≈-trans = λ f≈g g≈h → let (veq₁ , eeq₁) = f≈g ; (veq₂ , eeq₂) = g≈h in veq₁ ⟨≡≡⟩ veq₂ , subst-trans (Graph._⟶_ _) veq₁ veq₁ veq₂ veq₂ eeq₂ eeq₁
      ; _⨾_ = λ f g → record { ver = ver f ⨾’ ver g ; edge = edge f ⨾’ edge g } -- using ~𝒮et~
      ; ⨾-cong = λ {G} {H} {K} {f} {f’} {g} {g’} f≈f’ g≈g’ → let (veq₁ , eeq₁) = f≈f’ ; (veq₂ , eeq₂) = g≈g’ in ≡-cong (ver g) veq₁ ⟨≡≡⟩ veq₂ , subst-cong (Graph._⟶_ _) veq₁ veq₁ eeq₁ (Graph._⟶_ _) (edge g) veq₂ eeq₂
      ; assoc = ≡-refl , ≡-refl
      ; Id = record { ver = Category’.Id 𝒮et’ ; edge = Category’.Id 𝒮et’ }
      ; leftId = ≡-refl , ≡-refl
      ; rightId = ≡-refl , ≡-refl
      }

  𝒰’ : Functor’ 𝒞𝒶𝓉’ 𝒢𝓇𝒶𝓅𝒽’
  𝒰’ =  record {
     obj’ = λ 𝒞 → record { V = Category’.Obj’ 𝒞 ; _⟶_ = Category’._⟶_ 𝒞 }
   ; mor’ = λ F  → record { ver = Functor’.obj’ F ; edge = Functor’.mor’ F }
   ; cong = λ f≈g → f≈g ; id = ≡-refl , ≡-refl ; comp = λ {x} {y} {z} {f} {g} → ≡-refl , ≡-refl }


𝒫’₀ : Graph → Category’
𝒫’₀ G = let open TypedPaths G in 
  record
    { Obj’ = Graph.V G
    ; _⟶_ = _⇝_
    ; _≈_ = _≡_
    ; ≈-refl = ≡-refl
    ; ≈-sym = ≡-sym
    ; ≈-trans = _⟨≡≡⟩_
    ; _⨾_ = _++_
    ; ⨾-cong = λ p≈p’ q≈q’ → ≡-cong₂ _++_ p≈p’ q≈q’
    ; assoc = λ {x y z ω p q r} → assoc {p = p}
    ; Id = λ {x} → x !
    ; leftId = leftId
    ; rightId = rightId
    }

𝒫₁’ : ∀{G H} → GraphMap G H → Functor’ (𝒫’₀ G) (𝒫’₀ H)
𝒫₁’ {G} {H} f = record { obj’ = ver f ; mor’ = fmap ; cong = ≡-cong fmap ; id = ≡-refl ; comp = λ {x} {y} {z} {p} → comp {p = p} }
    where
      open TypedPaths ⦃...⦄ public

      fmap : {x y : Graph.V G} →  x ⇝ y → (ver f x) ⇝ (ver f y)
      fmap (x !) = ver f x !
      fmap (x ⟶[ e ]⟶ p) = ver f x ⟶[ edge f e ]⟶ fmap p

      comp : {x y z : Graph.V G} {p : x ⇝ y} {q : y ⇝ z} → fmap (p ++ q) ≡ fmap p ++ fmap q
      comp {x} {p = .x !} = ≡-refl -- since ! is left unit of ++
      comp {x} {p = .x ⟶[ e ]⟶ ps} = ⟶-≡ (comp {p = ps})

𝒫’ : Functor’ 𝒢𝓇𝒶𝓅𝒽’ 𝒞𝒶𝓉’
𝒫’ = record { obj’ = 𝒫’₀ ; mor’ = 𝒫₁’ ; cong = λ f≈g → proj₁ f≈g ,  gg f≈g ; id = ≡-refl , idm ; comp = ≡-refl , compmor }
    where
      open TypedPaths ⦃...⦄ public
         
      idm : ∀ {G} {x y} {p : x ⇝ y} → Functor’.mor’ (Category’.Id 𝒞𝒶𝓉’ {𝒫’₀ G}) p ≡ Functor’.mor’ (𝒫₁’ (Category’.Id 𝒢𝓇𝒶𝓅𝒽’)) p
      idm {G} {x} {p = .x !} = ≡-refl
      idm {G} {x} {p = .x ⟶[ e ]⟶ ps} = ⟶-≡ (idm {p = ps})    

      -- general version of gelping, keep it around, possibly as an excercise
      helping : ∀ {a b} {A : Set a} (B : A → A → Set b) (P : A → A → Set) (cons : (s : A) (i : A) → B s i → (t : A) → P i t → P s t) →
                  {x x’ i i’ t t’ : A} {e : B x i} {e’ : B x’ i’} {ps : P i’ t’}
                  (eqi : i’ ≡ i) (eqt : t’ ≡ t) (eqx : x’ ≡ x) (eqe : e’ ≡ ≡-subst₂ B (≡-sym eqx) (≡-sym eqi) e)
                → cons x i e t (≡-subst₂ P eqi eqt ps) ≡ ≡-subst₂ P eqx eqt (cons x’ i’ e’ t’ ps) 
      helping B P cons ≡-refl ≡-refl ≡-refl ≡-refl = ≡-refl

      gelping :  {G : Graph} {x x’ i i’ t t’ : Graph.V G} {e : Graph._⟶_ G x i} {e’ : Graph._⟶_ G x’ i’} {ps : i’ ⇝ t’}
                  (eqi : i’ ≡ i) (eqt : t’ ≡ t) (eqx : x’ ≡ x) (eqe : e’ ≡ ≡-subst₂ (Graph._⟶_ G) (≡-sym eqx) (≡-sym eqi) e)
                → x ⟶[ e ]⟶ (≡-subst₂ _⇝_ eqi eqt ps) ≡ ≡-subst₂ _⇝_ eqx eqt (x’ ⟶[ e’ ]⟶ ps) -- read right-to-left this says we can shunt a subst over the inductive path constructor
      gelping ≡-refl ≡-refl ≡-refl ≡-refl = ≡-refl

      -- or in the case of graph maps
      gelpingg : {G H : Graph} {f g : GraphMap G H} {x i t : Graph.V G} {e : Graph._⟶_ G x i} {ps : ver f i ⇝ ver f t}
                 (eq : Category’._≈_ 𝒢𝓇𝒶𝓅𝒽’ f g)
                → let veq = proj₁ eq in
                  ver g x ⟶[ edge g e ]⟶ (≡-subst₂ _⇝_ veq veq ps) ≡ ≡-subst₂ _⇝_ veq veq (ver f x ⟶[ edge f e ]⟶ ps)
      gelpingg (veq , eeq) = gelping veq veq veq (subst-sym (Graph._⟶_ _) veq veq eeq)

      gg : ∀ {x y} {f g : GraphMap x y} (f≈g : Category’._≈_ 𝒢𝓇𝒶𝓅𝒽’ f g) {X Y : Category’.Obj’ (𝒫’₀ x)} {p : (𝒫’₀ x Category’.⟶ X) Y}
         → Functor’.mor’ (𝒫₁’ g) p ≡ ≡-subst₂ (Category’._⟶_ (𝒫’₀ y)) (proj₁ f≈g) (proj₁ f≈g) (Functor’.mor’ (𝒫₁’ f) p)
      gg eq {X = X} {p = .X !} rewrite (proj₁ eq) {X} = ≡-refl
      gg eq {X = X} {p = .X ⟶[ e ]⟶ ps} rewrite gg eq {p = ps} = gelpingg eq

      open Category ⦃...⦄
      compmor : ∀ {G H K} {f : G ⟶ H} {g : H ⟶ K} {x y} {p : x ⇝ y} → Functor’.mor’ (𝒫₁’ f ⨾’ 𝒫₁’ g) p ≡ Functor’.mor’(𝒫₁’ (f ⨾’ g)) p
      compmor {x = x} {p = .x !} = ≡-refl
      compmor {x = x} {p = .x ⟶[ e ]⟶ ps} = ⟶-≡ (compmor {p = ps})

module freedom’ (G : Obj 𝒢𝓇𝒶𝓅𝒽) {𝒞’ : Category’ {ℓ₀} {ℓ₀} {ℓ₀} } where

  open TypedPaths G using (_! ; _⟶[_]⟶_ ;  _⇝_ ; _++_)
  open Category ⦃...⦄

  ι’ : G ⟶ Functor’.obj’ 𝒰’ (𝒫’₀ G)
  ι’ = record { ver = Id ; edge = λ {x} {y} e → x ⟶[ e ]⟶ y ! }

  lift’ : G ⟶ (Functor’.obj’ 𝒰’) 𝒞’ → 𝒫’₀ G ⟶’ 𝒞’
  lift’ f = record { obj’ = λ v → ver f v ; mor’ = toMap ; cong = cong ; id = ≈-refl ; comp = λ {x y z p q} → proof {x} {y} {z} {p} {q} }
     where
          toMap : ∀ {x y} → x ⇝ y → ver f x ⟶’ ver f y
          toMap (y !) = Id’
          toMap (x ⟶[ e ]⟶ p) = edge f e ⨾’ toMap p
          cong : ∀ {x y} {p q : x ⇝ y} → p ≡ q → Category’._≈_ 𝒞’ (toMap p) (toMap q)
          cong ≡-refl = ≈-refl

          proof : ∀{x y z} {p : x ⇝ y} {q : y ⇝ z} → Category’._≈_ 𝒞’ (toMap (p ++ q)) (toMap p ⨾’ toMap q)
          proof {p = ._ !} = ≈-sym leftId’ -- ≡-sym (Category’.leftId {!!})
          proof {p = ._ ⟶[ e ]⟶ ps} = ≈-trans (⨾-cong ≈-refl (proof {p = ps})) (≈-sym (Category’.assoc 𝒞’))
{-
  property’ : ∀{f : G ⟶ (Functor’.obj’ 𝒰’) 𝒞’} → Category’._≈_ 𝒢𝓇𝒶𝓅𝒽’ f (ι’ ⨾’ (Functor’.mor’ 𝒰’) (lift’ f))
  property’ {f} = ≡-refl , {!now need to add setoid structure to graphs!}
-}
#+END_EXAMPLE

* COMMENT Random thoughts on: Relations ≅ Graph Paths
Can we turn any relation into a category? Well we know that preorder relations yield categories,
so let’s consider transforming arbitrary relations to preorders.

Suppose we have a relation ~R : X → X → Set~ and we want it to be a preorder such as
~≤ : ℕ → ℕ → Set~. Then we need it to be reflexive and transitivie; that is,
~∀ x ∶ X • R x x~, ~∀ x y ∶ X • R x y → R y x~, and ~∀ x y z ∶ X • R x y → R y z → R x z~ are
provable, respectively.

(As it stands, this relation is precicely a graph-path!
If we want a relation in the traditional sense of ordered pairs, then we want a simple-graph.
#+BEGIN_EXAMPLE
simple : ∀ {x y} (p q : R x y) → p ≡ q    -- at most one edge between any two pair
#+END_EXAMPLE
)


[[

above when defined poset category, or rather after hom is defined,

mention how intervals a..b are realised in the cat, say via hom??

]]

Then, ~≤R~ is a partial order.
#+BEGIN_EXAMPLE
data _≤R : X → X → Set where
  embed : ∀ {x y} → R x y → x ≤R y                      -- existing edges
  refl  : ∀ {x} → x ≤R x                                 -- empty path
  trans : ∀ {x y z} → x ≤R y → y ≤R z → x ≤R z         -- path concatenation
#+END_EXAMPLE
Observe that ~embed~ says that the order ~≤R~ contains ~R~. 

(~≤R~ is also known as the "reachiability poset of R" ??)

Usual definition is ~≤R ≔ R* = λ x y → Σ n ∶ ℕ • Rⁿ x y~ where
~R⁰ x y = (x ≡ y)~ and ~Rⁿ⁺¹ x y ≡ Σ i • R x y ∧ Rⁿ i y~; the reflexive transitive closure of
~R~. While this is more compact, the Agda version is easier to work with and it is equivalent
since ~embed~ corresponds to ~n=1~, ~refl~ corresponds to ~n = 0~, and ~trans~ corresponds to
the ‘multiplication’ operation since ~Rⁿ⁺¹ x y ⇔ Σ a,b ∶ ℕ • a + b ≡ n ∧ Σ i • Rᵃ x i ∧ Rᵇ i y~
---or so I claim!

For example, if ~R = { (1,2) , (3,4) }~ then
#+BEGIN_EXAMPLE
≤R =
{
  (1,2) , (3,2),               -- embed
  (1,1), (2,2), (3,3),         -- refl
  -- trans gives no new pairs
}
#+END_EXAMPLE
An example algorithm for finding the transitive closure is Warshall’s algorithm.

Notice that if ~R~ reflexive or transitive, then we do not have uniqunenss of proofs for
~≤R~. In particular, suppose ~R~ is reflexive and such proofs are constructed by ~r_~.
Then a proof of ~x ≤R x~ can be obtained in two ways: ~refl {x}~ or ~embed (r x)~.

Now the resulting category can be thought of as the free-category on ~R~; what’s the associated
adjunctin to this claim o mine? That is, functors from this free cat correspond to relational
homomorphisms?? Consider consulting Schmidt and Strohnelin.

Is this is the least preorder relation on R?
#+BEGIN_EXAMPLE
suppose ⊑ is a reflexive relation that contains R, then

given p : x ≤R y  --ignoring transitivity
there are two cases.

Case p = embed q. Then q yields a proof of x ⊑ y since ⊑ contians R and q is an R proof.
Case p = refl {x}. Then x ⊑ x holds since ⊑ is relfexive.

Hence, ≤R (ignoring transitivity) is the least reflexive relation contianing R.

Suppose ⊑ is also transitive.

Then the only remaining case is

Case p = trans q r, where q : x ≤R y, r : y ≤R z, Then by induction we have proofs
  x ⊑ y ⊑ z, but ⊑ is transitive and so we have a proof of x ⊑ z.

Thus, ≤R is the least preorder containing R!! Woah! Awesome!

#+END_EXAMPLE


Every preorder can be obtained as the closure of its Hasse/covers relation:
~∀ R preorder • R ≅ ≤[ R ] ≅ ≤[ Covers R ]~ (in the category of relations and relation homomorphisms),
where ~Covers R x y ≡ x ≠ y ∧ x R y ∧ ¬ Σ z • z ≠ x R z R y ≠ z~. ?? Is this true, or do I just
think it to be true...

In particular, taking ~R = ℙₙ~, which is a hasse relation, yields the free preorder on R
which is essentially the free category on the poset ~≤[ R ]~.


----

Now R can be thought of as a directed graph.
If we take ~R = { (i, i+1) ∣ i ∈ 0..n-1} ~
then ~≤R~ is the free graph on ~ℙₙ~, right??

moreover it is a total order: we can show
#+BEGIN_EXAMPLE
total : ∀ {x y} → x ≤R y ⊎ y ≤R x
antisym : ∀ {x y} → x ≤R y → y ≤R x → x ≡ y
#+END_EXAMPLE 
Also such categories of paths are known as simplicies??

\url{https://ncatlab.org/nlab/show/simplex+category}

\url{http://mathoverflow.net/questions/159989/internal-logic-of-the-topos-of-simplicial-sets}

* COMMENT Kopka D-poset                    :CategoryTheory:Functors:Examples:
They’re also instances of a structure known
as a \emph{Kopka D-poset}, or Kopka difference-poset:
such a structure ~(D, ≤, ∸, *, 0, 1)~ consists of a poset ~(D, ≤)~ with least element ~0~,
greates element ~1~, abelian po-monoid ~(D, ≤, *, 1)~, and a binary operation
~_∸_ : D × D → D~ satisfying
begin{itemize}
\item ~a ≤ b ⇒ b ∸ a~ is defined  %% contravariance.
\item ~a ∸ 0 = a~ %% since ~0 ≤ a~ and what??
\item ~a ≤ b ≤ c ⇒ c - b ≤ c - a~ %% contravariance.
\item ~a ≤ b ≤ c ⇒ (c ∸ a) ∸ (c ∸ b) = b ∸ a~ %% composition via functoricality?
\item ~a ∸ (a * b) ≤ 1 ∸ b~, compare with $\frac{y}{y \times x} = \frac{1}{x}$.
\end{itemize}

The similarity is obtained as follows:
#+BEGIN_EXAMPLE
Assuming

(A0) a ∸ 0 = a, for all a
(A1) a ≤ b ≤ c ⇒ c ∸ b ≤ c ∸ a
(A2) a ≤ b ≤ c ⇒ (c ∸ a) ∸ (c ∸ b) = b ∸ a

(i)
   a ≤ b
⇒ 0 ≤ a ≤ b         0 is bottom
⇒ b ∸ a ≤ b ∸ 0     (A1)
⇒ b ∸ a ≤ b         (A0)

(ii) a ∸ a = 0
Proof.
  Suffices to show a ∸ a ≤ 0, since 0 is bottom element.

    a ∸ a
  = (a ∸ 0) ∸ (a ∸ 0)   (A0)
  = 0 ∸ 0               (A2) since 0 ≤ 0 ≤ a , since 0 bottom
  = 0                   (A0)
#+END_EXAMPLE

* COMMENT footer

(org-babel-tangle)

---

Note the existence of: (agda2-restart)

eval: (progn (org-babel-goto-named-src-block "make-readme") (org-babel-execute-src-block) (outline-hide-sublevels 1))

NOTE that AlBasmala calls the source file NAME.org, so below we change that to
this file’s name.

*WARNING* To use agda-mode to convert agda blocks to org blocks,
the blocks cannot contain any ~\~ within them!

(makunbound ’agda2-include-dirs)

# Local Variables:
# eval: (visual-line-mode t)
# eval: (load-file "~/alhassy.github.io/content/AlBasmala.el")
# eval: (setq NAMEorg (buffer-name))
# eval: (setq pdfsLocation "~/alhassy.github.io/assets/pdfs/")
# eval: (setq SOURCE "https://raw.githubusercontent.com/alhassy/CatsCheatSheet/master/PathCat.lagda")
# compile-command: (preview-article)
# eval: (org-mode)
# eval: (load-file "~/Projects/org-agda-mode/literate.el")
# End:
