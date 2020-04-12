-- Seminario encuentro 1
-- 09/04/2020

{- [Abstract]
La idea es expresar la teoria de fundamentos univalentes iniciada por Voevodsky [1] en Agda.


Que es la "univalent foundations"?

Voevodsky plantea utilizar una teoria basada en teoria de tipos, con rasgos homotopicos, para poder
expresar los fundamentos de las matematicas. Toma la teoria de tipos de Martin-Lof, y le agrega un par de cosas.

a b ∈ X

p : [0 ; 1] -> X
p(0) = a
p(1) = b
p es continua

f, g ∈ X -> Y

h : [0 ; 1] x X -> Y
h(0, x) = f(x)
h(1, x) = g(x)
h continua


Que es Agda?

Es un lenguaje de programacion funcional con tipos dependientes. Lo que lo hace un candidato para expresar
(y verificar) demostraciones matematicas.


[1]: https://www.ams.org/journals/bull/2018-55-04/S0273-0979-2018-01616-9/
-}

{- [Introduction]

A que nos referimos con una teoria de tipos univalente?
Que diferencias tiene con las teorias matematicas mas comunes?

Principales diferencias:
 1- Los objetos que tomamos como primitivos
   * tipos (o grupoide de alto orden ), en vez de conjuntos
   * en particular, un conjunto va a ser un 0-grupoide
 2- Como reflejamos la logica
   * tipos, en vez de propocisiones
   * valores de verdad son un tipo particular, (-1)-grupoide
 3- Como tratamos la igualdad
   * la igualdad es un tipo especial (tipo identidad), que no necesariamente
     es un valor de verdad

Introducidas por Voevodsky (no perdamos mucho tiempo):
 4- niveles de tipos, clasificandolos como n-grupoides
 5- una definicion de equivalencia de tipos uniforme para todos los niveles
 6- al axioma univalente en MLTT (Martin-Lof Type Theory)
-}

{- MLTT in Agda -}

{- [What is Agda?]

Asumo que ya se vio bastante, pero la idea es que es un lenguaje de programacion
funcional con tipos dependientes, lo que nos permite expresar
nociones/propiedades/formulacions matematicas y chequear que son correctas.

Le voy a dar un uso muy rustico, corrijanme si algo va mal
-}

{- [A spartan Martin-Lof type theory (MLTT)]

spartan ~ rustico

Cosas que nuestra teoria de tipos va a tener:

 - un tipo vacio            𝟘
 - un tipo trivial          𝟙
 - un tipo de naturales     ℕ
 - +, Π, Σ e Id, formadores de tipos
 - Universos, 𝓤, 𝓥, 𝓦

El tutorial tambien es rustico con el uso de Agda, asi que
parenme si se les ocurre una mejora. Si piensan "esto es una idiotez,
seguro Teo ya la penso y no la uso por X", les aseguro que no la pense.
-}

{-# OPTIONS --without-K --exact-split --safe #-}

module HoTT-UF-Agda where
-- HoTT : Homotopy Type Theory
-- UF : Univalent Foundations

{- [Type Universes] Pablo, corregime

Los universos es una idea que nos permite zafar de la tipica paradoja en
conjuntos "el conjunto que tiene como miembro a todos los conjuntos que
no se tienen a si mismo". 

Un universo es un tipo de tipos, nos permite, por ejemplo, definir
familias de tipos como funciones normales
  X → 𝓤

La pregunta es si 𝓤 es un tipo, en que universo vive. Vamos a tener una
secuencia de universos: 𝓤₀, 𝓤₁, 𝓤₂, ...

En el texto (y aca) se diferencian los universos con un puntito arriba:
𝓤₁ ̇

Tenemos que:

𝟙  : 𝓤₀
𝓤₀ : 𝓤₁
𝓤₁ : 𝓤₂  
 ⋮

X : 𝓤ᵢ  implica X : 𝓤ᵢ₊₁

Que pasa si asumimos 𝓤₀ : 𝓤₀, introducimos una paradoja...

Un par de operaciones:
 𝓤⁺ es el proximo, ej. 𝓤₁⁺ es 𝓤₂
 𝓤 ⊔ 𝓥 es el least upper bound (minima cota superior)
 
𝓤ᵢ ⊔ 𝓤ⱼ  defeq  𝓤\_max{i, j}

-}

open import Universes public

-- Universos a partir de Set

variable
 𝓤 𝓥 𝓦 𝓣 : Universe

{- [The one element type 𝟙]

Este es el tipo trivial, tiene solo un elemento.
En Haskell es (), a veces unit, la declaracion es exactamente esto.

-}

data 𝟙 : 𝓤₀ ̇ where
 ⋆ : 𝟙

-- 𝟙 ~ ()
-- ⋆ ~ ()

{-
Ahora, esto es la sintaxis de los habitantes de 𝟙, necesitamos un
significado. Como estamos trabajando en algo matematico, pensemos que
necesitamos una forma de chequear que todo elemento en 𝟙 satisface alguna
propiedad A(x):

 1- La propiedad es una funcion A : 𝟙 → 𝓤
 2- A(x) (de ahora en mas A x), no necesariamente es un valor de verdad,
    puede ser cualquier tipo.
 3- Acordemonos que en MLTT las expresiones matematicas son tipos:
    Π A : 𝟙 → 𝓤, A ⋆ → Π x : 𝟙, A x
 4- Esto lo leemos como siempre, para cualquier propiedad A sobre
    elementos de tipo 𝟙, si A ⋆ es valido (de ahora en mas, esta habitado),
    entonces sigue que A x vale para cualquier x : 𝟙
 5- en Agda
      (A : 𝟙 → 𝓤 ̇) → A ⋆ → ((x : 𝟙) → A x)
-}

𝟙-induction : (A : 𝟙 → 𝓤 ̇) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a
-- notar que estamos haciendo pattern matching,
-- Agda entiende que no hay mas casos

𝟙-recursion : (B : 𝓤 ̇) → B → (𝟙 → B)
𝟙-recursion B = 𝟙-induction (λ x → B)

-- Notar que estamos demostrando algo, en particular, que para
-- cualquier formula/tipo B, vale que B -> (True -> B)

!𝟙' : (X : 𝓤 ̇) → X → 𝟙
!𝟙' X x = ⋆

!𝟙 : {X : 𝓤 ̇} → X → 𝟙
!𝟙 x = ⋆

{- [The empty type 𝟘]

Es el tipo imposible, bottom, no tiene ningun habitante (o no deberia).
En Haskell creo que es Void.

Se lo puede pensar como el conjunto vacio,
o como el valor falso (donde 𝟙 es true)

-}

data 𝟘 : 𝓤₀ ̇ where

𝟘-induction : (A : 𝟘 → 𝓤 ̇) → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : (A : 𝓤 ̇) → 𝟘 → A
𝟘-recursion A = 𝟘-induction λ _ → A

-- !𝟙 : (A : 𝓤 ̇) → A → 𝟙
-- f : A -> 𝟙, g : A -> 𝟙, f = g

-- C, Obj y flechas entre objetos
-- A B, A ∧ B,  D , pr1 : D -> A, pr2 : D -> B
-- E, f : E -> A, g : E -> B
-- h : E -> D, f = h ∘ pr1, g = h ∘ pr2

-- notacion categorica
!𝟘 : (A : 𝓤 ̇) → 𝟘 → A
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ X = X → 𝟘

{- 

En logica intuicionista, al not (¬ X) se lo puede definir como X → 𝟘,
es decir, mostrando que si tengo un habitante de X, consigo un habitante
de 𝟘. Esto tambien es como decir que el tipo esta vacio (no tiene habitantes).
En teoria de tipos, un tipo vale cuando tiene algun habitante
(una demostracion).

Notamos que por 𝟘-induction siempre tenemos una
funcion 𝟘 → X, entonces si tenemos una X → 𝟘 hay como un "isomorfismo".
Y, con univalencia, vamos a poder demostrar que X ≃ 𝟘

-}

{- [The type ℕ of natural numbers]

Vamos a hacerlo a lo Peano, pero ahora solo una parte, porque todavia no
tenemos equiv para todos los axiomas

-}

data ℕ : 𝓤₀ ̇ where
  zero : ℕ
  succ : ℕ → ℕ

-- nos permite escribir 3 en vez de succ (succ (succ zero))
{-# BUILTIN NATURAL ℕ #-}


-- La induccion es muy similar a induccion sobre los naturales, veamos
ℕ-induction : (A : ℕ → 𝓤 ̇)
            → A zero
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n

ℕ-induction A a₀ f = h
 where
  h : (n : ℕ) → A n
  h zero     = a₀
  h (succ n) = f n (h n)

ℕ-recursion : (X : 𝓤 ̇)
            → X
            → (ℕ → X → X)
            → ℕ → X
            
ℕ-recursion X = ℕ-induction (λ _ → X)

ℕ-iteration : (X : 𝓤 ̇)
            → X
            → (X → X)
            → ℕ → X

ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)

-- ℕ-iteration _ true f 4 = f (f (f (f true))) 

module Arithmetic where
  _+_ _×_ : ℕ → ℕ → ℕ

  x + 0      = x
  x + succ y = succ (x + y)

  x × 0      = 0
  x × succ y = x + x × y

  infixl 20 _+_
  infixl 21 _×_

-- esto es medio trampa, nos deberia alcanzar con ℕ-induction

module Arithmetic' where
  _+_ _×_ : ℕ → ℕ → ℕ

  x + y = ℕ-iteration ℕ x succ y

  x × y = ℕ-iteration ℕ 0 (x +_) y

  infixl 20 _+_
  infixl 21 _×_



module ℕ-order where
  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇

  0      ≤ y      = 𝟙
  succ _ ≤ 0      = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x

  infix 10 _≤_
  infix 10 _≥_

{- [ejercicios]
 * redefinir con ℕ-induction
 * cuando tengamos Σ y ≡ probar:
   x ≤ y iff Σ z : ℕ, x + z ≡ y
 * y cuando tengamos univalencia:
   (x ≤ y) ≡ (Σ z : ℕ, x + z ≡ y)

 Nota: que el iff puede extenderse a una igualdad solo vale para
 tipos que sean subsingleton (ya vamos a ver)

 Nota: se puede definir ℕ con una representacion binaria, estaria bueno verlo
  cuando entendamos mas de HoTT
-}


{- [The binary sum type constructor _+_]

Vamos a definir la union disjunta.

Es una union, pero nos acordamos de donde viene el elemento.

A + A ≠ A

Ademas, la pregunta interesante es en que universo vive A + B

-}

data _+_ {𝓤 𝓥} (X : 𝓤 ̇) (Y : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
  inl : X → X + Y
  inr : Y → X + Y

--Pensemos la induction y su tipo

+-induction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : X + Y → 𝓦 ̇)
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → (z : X + Y) → A z

+-induction A dl dr (inl x) = dl x
+-induction A dl dr (inr x) = dr x

+-recursion : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : 𝓦 ̇)
            → (X → A)
            → (Y → A)
            → X + Y → A

+-recursion A = +-induction (λ _ → A)


-- Despues vamos a ver que se puede truncar un tipo, para que tenga un solo
-- valor o ninguno. Por ahora no importa

-- Pensemos entre todos que es 𝟙 + 𝟙 (o 𝟚, Bool) ≠ 𝟙
-- inl ⋆
-- inr ⋆

-- !𝟙 : (X : 𝓤 ̇) → X → 𝟙
-- !𝟚 : (X : 𝓤 ̇) → (x : X) → (y : X) → X → 𝟚
-- !𝟚 X x y x = inl ⋆


{- [Σ types]
   | tipo existencial
   | Producto dependiente

La idea es dados X : 𝓤 y Y : X → 𝓥, construir el tipo habitado por
demostraciones de elementos de X que cumplen la propiedad Y (aka, que
Y x esta habitado).

-}

record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
  constructor
   _,_
  field
   x : X
   y : Y x
   
-- pregunta al publico, que onda este record?

pr₁ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x → y) = Σ x ꞉ X , y
-- notar que es otro : \:4 (inserte rant)

--Hagamos la induccion nosotros
Σ-induction : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : Σ Y → 𝓦 ̇}
            → ((x : X) → (y : Y x) → A (x , y)) 
            → ((σ : Σ Y) → A σ)
Σ-induction f (x , y) = f x y

-- curry : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : Σ Y → 𝓦 ̇}
--       → ((σ : Σ Y) → A σ)
--       → ((x : X) → (y : Y x) → A (x , y)) 
    

-- hagamos la inversa, y nombremosla

-- Un caso particular es el producto cartesiano
_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y

-- Seminario encuentro 2
-- 16/04/2020

{- [Π types]
-}

Π : {X : 𝓤 ̇} (A : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y

syntax -Π A (λ x → b) = Π x ꞉ A , b

id : {X : 𝓤 ̇} → X → X
id x = x

-- Definamos la composicion _∘_


-- El tipo que nos quedo, leamoslo matematicamente


-- un par de funciones utiles

domain : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X


{- [The identity type former Id, also written _≡_]
-}

data Id {𝓤} (X : 𝓤 ̇) : X → X → 𝓤 ̇ where
  refl : (x : X) → Id X x x

{-
  Estamos definiendo el tipo de igualdades entre elementos de tipo X,
  segun esta def, solo puedo crear una igualdad entre el mismo
  elemento (refleccion)

  notar que a diferencia de las otras definiciones de tipos con data
  aca no definimos un tipo, sino una familia de tipos, indexada por
  elementos de X
-}

_≡_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
x ≡ y = Id _ x y

{-
En general, no podemos probar que haya un solo elemento en el tipo x ≡ y,
excepto para algunos tipos, como ℕ, para los cuales si vale.
Estos tipos se los llama conjuntos.
-}

-- ≡-induction le vamos a decir 𝕁

𝕁 : (X : 𝓤 ̇) (A : (x y : X) → x ≡ y → 𝓥 ̇)
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y) → A x y p

𝕁 = {!!}


-- Aca terminamos el MLTT rustico
