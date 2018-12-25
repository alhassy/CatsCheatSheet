-- This file has been extracted from https://alhassy.github.io/PathCat/
-- Type checks with Agda version 2.6.0.

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

module _ {i} {S : Set i} where
    open import Relation.Binary.EqReasoning (≡-setoid S) public

open import Agda.Builtin.String

defn-chasing : ∀ {i} {A : Set i} (x : A) → String → A → A
defn-chasing x reason supposedly-x-again = supposedly-x-again

syntax defn-chasing x reason xish = x ≡⟨ reason ⟩′ xish

infixl 3 defn-chasing

_even-under_ : ∀ {a b} {A : Set a} {B : Set b} {x y} → x ≡ y → (f : A → B) → f x ≡ f y 
_even-under_ = λ eq f → ≡-cong f eq

record Graph₀ : Set₁ where
  field
    V   : Set
    E   : Set
    src : E → V
    tgt : E → V

record _𝒢⟶₀_ (G H : Graph₀) : Set₁ where
  open Graph₀
  field
    vertex : V(G) → V(H)
    edge   : E(G) → E(H)
    src-preservation : ∀ e → src(H) (edge e) ≡  vertex (src(G) e)
    tgt-preservation : ∀ e → tgt(H) (edge e) ≡  vertex (tgt(G) e)

-- ‘small graphs’ , since we are not using levels
record Graph : Set₁ where
  field
    V    : Set
    _⟶_ : V → V → Set

-- i.e., Graph ≈ Σ V ∶ Set • (V → V)
-- Graphs are a dependent type!

record GraphMap (G H : Graph) : Set₁ where    
    private
      open Graph using (V)
      _⟶g_ = Graph._⟶_ G
      _⟶h_ = Graph._⟶_ H
    field
      ver  : V(G) → V(H)                                   -- vertex morphism
      edge : {x y : V(G)} → (x ⟶g y) → (ver x ⟶h ver y) -- arrow preservation

open GraphMap

-- embedding: j < n ⇒ j < suc n
`_ : ∀{n} → Fin n → Fin (suc n)
` j = inject≤ j (≤-step ≤-refl) where open import Data.Nat.Properties using (≤-step)

[_]₀ : ℕ → Graph₀
[ n ]₀ = record 
    { V = Fin (suc n)                  -- ≈ {0, 1, ..., n - 1, n}
    ; E = Fin n                        -- ≈ {0, 1, ..., n - 1}
    ; src = λ j → ` j
    ; tgt = λ j → fsuc j
    }

[_] : ℕ → Graph
[ n ] = record {V = Fin (suc n) ; _⟶_ = λ x y → fsuc x ≡ ` y }

open import Data.Vec 
  using (Vec) 
  renaming (_∷_ to _,,_ ; [] to nil) -- , already in use for products :/
  
-- one sorted
record Signature : Set where
    field
     𝒩 : ℕ        -- How many function symbols there are
     ar : Vec ℕ 𝒩 -- Their arities: lookup i ar == arity of i-th function symbol

open Signature ⦃...⦄ -- 𝒩 now refers to the number of function symbols in a signature

MonSig : Signature
MonSig = record { 𝒩 = 2 ; ar = 0 ,, 2 ,, nil }
-- unit u : X⁰ → X and multiplication m : X² → X

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

 open Category using (Obj) public
 
 record Iso {i} {j} (𝒞 : Category {i} {j}) (A B : Obj 𝒞) : Set j where
   private instance 𝒞′ : Category ; 𝒞′ = 𝒞
   field
     to   : A ⟶ B
     from : B ⟶ A
     lid  : to ⨾ from ≡ Id
     rid  : from ⨾ to ≡ Id
     
 syntax Iso 𝒞 A B = A ≅ B within 𝒞

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

 NatTrans : ∀ {i j i’ j’}  ⦃ 𝒞 : Category {i} {j} ⦄ ⦃ 𝒟 : Category {i’} {j’} ⦄ 
            (F G : Functor 𝒞 𝒟) → Set (j’ ⊍ i ⊍ j)
 NatTrans ⦃ 𝒞 = 𝒞 ⦄ ⦃ 𝒟 ⦄ F G =
   Σ η ∶ (∀ {X : Obj 𝒞} → (obj F X) ⟶ (obj G X))
       • (∀ {A B} {f : A ⟶ B} → mor F f ⨾ η {B} ≡ η {A} ⨾ mor G f)

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

 𝒰₀ : Category → Graph
 𝒰₀ 𝒞 = record { V = Obj 𝒞 ; _⟶_ = Category._⟶_ 𝒞 }

 𝒰₁ : {𝒞 𝒟 : Category} → 𝒞 ⟶ 𝒟 → 𝒰₀ 𝒞 ⟶ 𝒰₀ 𝒟
 𝒰₁ F = record { ver = obj F ; edge = mor F }

-- Underlying/forgetful functor: Every category is a graph
 𝒰 : Functor 𝒞𝒶𝓉 𝒢𝓇𝒶𝓅𝒽
 𝒰 = record { obj = 𝒰₀ ; mor = 𝒰₁ ; id = ≡-refl ; comp = ≡-refl }

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

 module graphs-as-functors where

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

      fcmp-⨾ {f = s} {id} = ≡-refl
      fcmp-⨾ {f = t} {id} = ≡-refl
      fcmp-⨾ {f = id} {s} = ≡-refl
      fcmp-⨾ {f = id} {t} = ≡-refl
      fcmp-⨾ {f = id} {id} = ≡-refl

  fromFunc : Functor 𝒢 𝒮e𝓉 → Graph
  fromFunc F = record {
      V      = obj F 𝒢₀.V
    ; _⟶_    = λ x y → Σ e ∶ obj F 𝒢₀.E • src e ≡ x × tgt e ≡ y
             -- the type of edges whose source is x and target is y
    }
    where tgt src : obj F 𝒢₀.E → obj F 𝒢₀.V
          src = mor F 𝒢₁.s
          tgt = mor F 𝒢₁.t

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

 infix 10 _∘_
 _∘_ : ∀ {i j } ⦃ 𝒞 : Category {i} {j}⦄ {A B C : Obj 𝒞} → B ⟶ C →  A ⟶ B → A ⟶ C
 f ∘ g = g ⨾ f

 -- this only changes type
 opify : ∀ {i j i’ j’} {𝒞 : Category {i} {j}} {𝒟 : Category {i’} {j’}} 
      → Functor 𝒞 𝒟 → Functor (𝒞 ᵒᵖ) (𝒟 ᵒᵖ)
 opify F = record { obj   =  obj F 
                  ; mor   =  mor F 
                  ; id    =  Functor.id F 
                  ; comp  =  Functor.comp F 
                  }

 ∂ : ∀ {i j} → Functor (𝒞𝒶𝓉 {i} {j}) 𝒞𝒶𝓉
 ∂ = record { obj = _ᵒᵖ ; mor = opify ; id = ≡-refl ; comp = ≡-refl }

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

 Fst : ∀ {i j i’ j’} {𝒞 : Category {i} {j}} {𝒟 : Category {i’} {j’}} 
     → Functor (𝒞 ⊗ 𝒟) 𝒞
 Fst = record { obj = proj₁ ; mor = proj₁ ; id = ≡-refl ; comp = ≡-refl }

 Snd : ∀ {i j i’ j’} {𝒞 : Category {i} {j}} {𝒟 : Category {i’} {j’}} 
     → Functor (𝒞 ⊗ 𝒟) 𝒟
 Snd = record { obj = proj₂ ; mor = proj₂ ; id = ≡-refl ; comp = ≡-refl }

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

 exempli-gratia : ∀ {𝒞 𝒟 𝒳 𝒴 : Category {ℓ₀} {ℓ₀}} (⊕ : Functor (𝒳 ⊗ 𝒴) 𝒟)
                → let _⟨⊕⟩_ = pointwise ⊕
                   in
                      Fst ⟨⊕⟩ Snd ≡ ⊕
 exempli-gratia Bi = funcext (≡-cong (obj Bi) ≡-refl) (≡-cong (mor Bi) ≡-refl)

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

Path₀ : ℕ → Graph₀ → Set (ℓsuc ℓ₀)
Path₀ n G = [ n ]₀ 𝒢⟶₀ G

open import Data.Vec using (Vec ; lookup)

record Path₁ (n : ℕ) (G : Graph₀) : Set (ℓsuc ℓ₀) where
  open Graph₀
  field
    edges     : Vec (E G) (suc n)
    coherency : {i : Fin n} → tgt G (lookup (` i) edges) ≡ src G (lookup (fsuc i) edges)

module Path-definition-2 (G : Graph₀) where
  open Graph₀ G

  mutual
    data Path₂ : Set where
      _!   : V → Path₂
      cons : (v : V) (e : E) (ps : Path₂) (s : v ≡ src e) (t : tgt e ≡ head₂ ps) → Path₂

    head₂ : Path₂ → V
    head₂ (v !) = v
    head₂ (cons v e p s t) = v

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

module TypedPaths (G : Graph) where

  open Graph G hiding(V)
  open Graph   using (V)
  
  data _⇝_ : V G → V G → Set where
    _!      : ∀ x → x ⇝ x
    _⟶[_]⟶_ : ∀ x {y ω} (e : x ⟶ y) (ps : y ⇝ ω) → x ⇝ ω

  -- Preprend preserves path equality
  ⟶-≡ : ∀{x y ω} {e : x ⟶ y} {ps qs : y ⇝ ω} 
      → ps ≡ qs → (x ⟶[ e ]⟶ ps) ≡ (x ⟶[ e ]⟶ qs)
  ⟶-≡ {x} {y} {ω} {e} {ps} {qs} eq = ≡-cong (λ r → x ⟶[ e ]⟶ r) eq

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

  infixr 5 _++_

  _++_ : ∀{x y z} → x ⇝ y → y ⇝ z → x ⇝ z
  x ! ++ q           = q                         -- left unit
  (x ⟶[ e ]⟶ p) ++ q = x ⟶[ e ]⟶ (p ++ q)     -- mutual-associativity

  leftId : ∀ {x y} {p : x ⇝ y} → x ! ++ p ≡ p
  leftId = ≡-refl

  rightId : ∀ {x y} {p : x ⇝ y} → p ++ y ! ≡ p
  rightId {x} {.x} {.x !} = ≡-refl
  rightId {x} {y } {.x ⟶[ e ]⟶ ps} = ≡-cong (λ q → x ⟶[ e ]⟶ q) rightId

  assoc : ∀{x y z ω} {p : x ⇝ y} {q : y ⇝ z} {r : z ⇝ ω} 
        → (p ++ q) ++ r ≡ p ++ (q ++ r)
  assoc {x} {p = .x !} = ≡-refl
  assoc {x} {p = .x ⟶[ e ]⟶ ps} {q} {r} = ≡-cong (λ s → x ⟶[ e ]⟶ s) (assoc {p = ps})

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

module freedom (G : Obj 𝒢𝓇𝒶𝓅𝒽) {𝒞 : Category {ℓ₀} {ℓ₀} } where

  open TypedPaths G using (_! ; _⟶[_]⟶_ ;  _⇝_ ; _++_)
  open Category ⦃...⦄

  module 𝒢𝓇𝒶𝓅𝒽 = Category 𝒢𝓇𝒶𝓅𝒽
  module 𝒮ℯ𝓉 = Category (𝒮e𝓉 {ℓ₀})
  module 𝒞 = Category 𝒞
  instance 𝒞′ : Category ; 𝒞′ = 𝒞

  ι : G ⟶ 𝒰₀ (𝒫₀ G)
  ι = record { ver = Id ; edge = λ {x} {y} e  →  x ⟶[ e ]⟶ (y !) }

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

  _≈g_ : ∀{G H : Graph} (f g : G ⟶ H) → Set
  _≈g_ {G} {H} f g = Σ veq ∶ (∀ {v} → ver f v ≡ ver g v) •
    (∀ {x y e} → edge g {x} {y} e ≡ ≡-subst₂ (λ a b → Graph._⟶_ H a b) veq veq (edge f {x} {y} e))

  _≋_ : ∀{𝒞 𝒟 : Category} (f g : 𝒞 ⟶ 𝒟) → Set
  F ≋ G = 𝒰₁ F ≈g 𝒰₁ G   -- proofs (x , y) now replaced with: funcext x y

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

  naturality˘ : ∀ {K : Functor (𝒫₀ H) 𝒞} 
              →  lift˘ (𝒫₁ g 𝒞𝒶𝓉.⨾ K 𝒞𝒶𝓉.⨾ F)  ≡  (g 𝒢𝓇𝒶𝓅𝒽.⨾ lift˘ K 𝒢𝓇𝒶𝓅𝒽.⨾ 𝒰₁ F)
  naturality˘ = graphmapext ≡-refl ≡-refl

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

module folding (G : Graph) where
  open TypedPaths G
  open Graph G
                                              -- Given:
  fold : {X : Set} (v : V → X)               -- realise G's vertices as X elements
         (f : ∀ x {y} (e : x ⟶ y) → X → X) -- realise paths as X elements
       → (∀ {a b} → a ⇝ b → X)            -- Then: Any path is an X value
  fold v f (b !) = v b
  fold v f (x ⟶[ e ]⟶ ps) = f x e (fold v f ps)

  length : ∀{x y} → x ⇝ y → ℕ
  length = fold (λ _ → 0)          -- single walks are length 0.
                (λ _ _ n → 1 + n)  -- edges are one more than the 
                                    -- length of the remaining walk

  length-! : ∀{x} → length (x !) ≡ 0
  length-! = ≡-refl
  -- True by definition of “length”: The first argument to the “fold”

  length-ind : ∀ {x y ω} {e : x ⟶ y} {ps : y ⇝ ω} 
            →  length (x ⟶[ e ]⟶ ps)  ≡  1 + length ps
  length-ind = ≡-refl 
  -- True by definition of “length”: The second-argument to the “fold”

  path-cost : (c : ∀{x y}(e : x ⟶ y) → ℕ) → ∀{x y}(ps : x ⇝ y) → ℕ
  path-cost c = fold (λ _ → 0)           -- No cost on an empty path.
                     (λ x e n → c e + n) -- Cost of current edge plus 
                                          -- cost of remainder of path.

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

module lists (A : Set) where

  open import Data.Unit

  listGraph : Graph
  listGraph = record { V = A ; _⟶_ = λ a a’ → ⊤ }

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
