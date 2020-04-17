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

+-recursion : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇}
            → (X → A)
            → (Y → A)
            → X + Y → A

+-recursion {𝓤} {𝓥} {𝓦} {X} {Y} {A} = +-induction (λ _ → A)


-- Despues vamos a ver que se puede truncar un tipo, para que tenga un solo
-- valor o ninguno. Por ahora no importa

-- Pensemos entre todos que es 𝟙 + 𝟙 (o 𝟚, Bool) ≠ 𝟙
-- inl ⋆
-- inr ⋆

-- !𝟙 : (X : 𝓤 ̇) → X → 𝟙
-- !𝟚 : (X : 𝓤 ̇) → (x : X) → (y : X) → X → 𝟚
-- !𝟚 X x y x = inl ⋆


-- Agrego lo de aca abajo, porque viene bien
𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

𝟚-induction : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁

𝟚-induction' : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction' A a₀ a₁ = +-induction A
                         (𝟙-induction (λ (x : 𝟙) → A (inl x)) a₀)
                         (𝟙-induction (λ (y : 𝟙) → A (inr y)) a₁)

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
-- 17/04/2020

{- [Π types]
 -}

Π : {X : 𝓤 ̇} (A : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y

syntax -Π A (λ x → b) = Π x ꞉ A , b

id : {X : 𝓤 ̇} → X → X
id x = x

𝑖𝑑 : (X : 𝓤 ̇) → X → X
𝑖𝑑 X = id

-- (b -> c) -> (a -> b) -> a -> c

-- Definamos la composicion _∘_
_∘_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : Y → 𝓦 ̇}
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)


-- El tipo que nos quedo, leamoslo matematicamente

-- Aca podriamos probar reescribir lo de arriba con la sintaxis Π

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
  elementos de X.

  Despues vamos a entrar mas en detalle (espero) pero el tipo Id es raro,
  porque no podemos probar que Id X x y tenga un solo elemento, aunque
  querriamos poder decir que si.
-}

_≡_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
x ≡ y = Id _ x y
-- Esta    ^ notacion le deja inferir a Agda ese tipo

{-
En general, no podemos probar que haya un solo elemento en el tipo x ≡ y,
excepto para algunos tipos, como ℕ, para los cuales si vale.
Estos tipos se los llama conjuntos. 0-grupoide
-}

-- ≡-induction le vamos a decir 𝕁

𝕁 : (X : 𝓤 ̇) (A : (x y : X) → x ≡ y → 𝓥 ̇)
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y) → A x y p

𝕁 X A f x x (refl x) = f x

-- Ademas, tenemos otra induccion, base induction o ℍ, que nos puede
-- ser de utilidad y es isomorfica a 𝕁

ℍ : {X : 𝓤 ̇} (x : X) (B : ((y : X) → x ≡ y → 𝓥 ̇))
  → B x (refl x)
  → (y : X) (p : x ≡ y) → B y p
ℍ x B b x (refl x) = b

-- Ej redefinir 𝕁 y ℍ en funcion del otro

𝕁' : (X : 𝓤 ̇) (A : (x y : X) → x ≡ y → 𝓥 ̇)
   → ((x : X) → A x x (refl x))
   → (x y : X) (p : x ≡ y) → A x y p
𝕁' X A ar x y p = ℍ x (λ y' p' → A x y' p') (ar x) y p

-- Aca terminamos el MLTT rustico, estaria bueno discutir un
-- poquito mas sobre Id

{- [Basic constructions with the identity type]
-}

-- Transportar
transport : {X : 𝓤 ̇} (A : X → 𝓥 ̇) {x y : X}
          → x ≡ y → A x → A y

-- transport A (refl x) = 𝑖𝑑 (A x)
transport {𝓤} {𝓥} {X} A {x} {y} p  = ℍ x (λ y' p' → (A x → A y')) (𝑖𝑑 (A x)) y p
-- si hay ganas rescribamos con 𝕁 o ℍ

-- y pensemos como pasar (algoritmicamente) de pattern matching
-- a induction


lhs : {X : 𝓤 ̇} {x y : X} → x ≡ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇} {x y : X} → x ≡ y → X
rhs {𝓤} {X} {x} {y} p = y


-- Composicion de caminos (o transitividad)

_∙_ : {X : 𝓤 ̇} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = transport ((lhs p) ≡_) q p


-- Ej (ni lo pense) se puede redefinir para que transporte por p?
-- dan los mismos resultados?

-- Definimos otro operador para componer (y que sea mas lindo)

_≡⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇ } (x : X) → x ≡ x
x ∎ = refl x

{- Entonces, podemos escribir p ∙ q como:
  x ≡⟨ p ⟩
  y ≡⟨ q ⟩
  z ∎ : x ≡ z
-}

-- el inverso (simetrica)

_⁻¹ : {X : 𝓤 ̇} {x y : X} → x ≡ y → y ≡ x
-- (refl x) ⁻¹ = refl x
p ⁻¹ = transport (λ z → z ≡ lhs p) p (refl (lhs p))
-- A alguien se le ocurre algo mas facil?

-- Ahora si, escribamos una composicion alternativa y veamos que son iguales
_∙'_ : {X : 𝓤 ̇} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙' q = transport (_≡ rhs q) (p ⁻¹) q

∙agreement : {X : 𝓤 ̇} {x y z : X} (p : x ≡ y) (q : y ≡ z)
           → (p ∙' q) ≡ (p ∙ q)

∙agreement (refl x) (refl x) = refl (refl x)

-- refl y es definicionalmente neutro para cada uno, pero en lados distintos
-- (del lado donde hago el transport)

rdnel : {X : 𝓤 ̇} {x y : X} (p : x ≡ y)
      → (p ∙ refl y) ≡ p

rdnel p = refl p

rdner : {X : 𝓤 ̇} {y z : X} (q : y ≡ z)
      → (refl y ∙' q) ≡ q

rdner q = refl q

-- Como uno esperaria, refl y es el nuetro en los otros lados tambien, pero
-- no definicionalmente (hay que usar induccion)
-- hay ganas?


-- Aplicacion de una funcion a una Id (Functor)

ap : {X : 𝓤 ̇} {Y : 𝓥 ̇} (f : X → Y) {x x' : X}
   → x ≡ x' → f x ≡ f x'

ap {X} {Y} f {x} {x} (refl x) = refl (f x)
-- ap f {x} {x'} p = transport (λ y → f x ≡ f y) p (refl (f x))


-- Vamos a definir igualdad punto a punto de funciones,
-- con univalencia esto va a ser una forma de definir igualdades

_~_ : {X : 𝓤 ̇} {A : X → 𝓥 ̇} → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
f ~ g = ∀ x → f x ≡ g x
-- Esto ^ es una notacion para Π (mas rant)

{- [Reasoning with negation]
-}

--Notacion

¬¬ ¬¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬ A = ¬ (¬ A)
¬¬¬ A = ¬ (¬¬ A)

-- A → 𝟘
--                     ↓ (A → 𝟘) → 𝟘
dni : (A : 𝓤 ̇) → A → ¬¬ A
dni A a u = u a

contrapositive : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → (¬ B → ¬ A)
contrapositive f v a = v (f a)

-- Seguro vale la pena leer esto (es re corto)
-- http://math.andrej.com/2010/03/29/proof-of-negation-and-proof-by-contradiction/

tno : (A : 𝓤 ̇) → ¬¬¬ A → ¬ A
tno A = contrapositive (dni A)

{-
Theorem. Absurdity of absurdity of absurdity is equivalent to absurdity.

Proof. Firstly, since implication of the assertion 𝑦 by the assertion 𝑥
implies implication of absurdity of 𝑥 by absurdity of 𝑦, the implication
of absurdity of absurdity by truth (which is an established fact)
implies the implication of absurdity of truth, that is to say of
absurdity, by absurdity of absurdity of absurdity. 
Secondly, since truth of an assertion implies absurdity of its absurdity,
in particular truth of absurdity implies absurdity of absurdity of absurdity.
-}

-- Definamos equivalencia logica como:

_⇔_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ⇔ Y = (X → Y) × (Y → X)

lr-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ⇔ Y) → (X → Y)
lr-implication = pr₁

rl-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ⇔ Y) → (Y → X)
rl-implication = pr₂

absurdity³-is-absurdity : {A : 𝓤 ̇ } → ¬¬¬ A ⇔ ¬ A
absurdity³-is-absurdity {𝓤} {A} = firstly , secondly
 where
  firstly : ¬¬¬ A → ¬ A
  firstly = contrapositive (dni A)

  secondly : ¬ A → ¬¬¬ A
  secondly = dni (¬ A)


_≢_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
x ≢ y = ¬(x ≡ y)

≢-sym : {X : 𝓤 ̇ } {x y : X} → (x ≢ y) → (y ≢ x)
≢-sym {𝓤} {X} {x} {y} u = λ (p : y ≡ x) → u (p ⁻¹)

-- Notemos y definamos
--  Esta es la igualdad  ‌↓ en 𝓤 
Id→Fun : {X Y : 𝓤 ̇} → X ≡ Y → X → Y
Id→Fun {𝓤} = transport (𝑖𝑑 (𝓤 ̇))

-- Demostremos
𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
𝟙-is-not-𝟘 p = Id→Fun p ⋆

-- 𝟚 = 𝟙 + 𝟙
-- ₀ ₁ : 𝟚
-- Teniendo eso, podemos mostrar que los elementos de 𝟚 son distintos
₁-is-not-₀ : ₁ ≢ ₀
₁-is-not-₀ p = 𝟙-is-not-𝟘 q
 where
  f : 𝟚 → 𝓤₀ ̇
  f ₀ = 𝟘
  f ₁ = 𝟙

  q : 𝟙 ≡ 𝟘
  q = ap f p

-- Que significa que algo sea decidible??
-- todo esto es copy paste..

-- ¬¬ A → A
-- A ∨ ¬ A
decidable : 𝓤 ̇ → 𝓤 ̇
decidable A = A + ¬ A

has-decidable-equality : (X : 𝓤 ̇ ) → 𝓤 ̇
has-decidable-equality X = (x y : X) → decidable (x ≡ y)

𝟚-has-decidable-equality : has-decidable-equality 𝟚
𝟚-has-decidable-equality ₀ ₀ = inl (refl ₀)
𝟚-has-decidable-equality ₀ ₁ = inr (≢-sym ₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₀ = inr ₁-is-not-₀
𝟚-has-decidable-equality ₁ ₁ = inl (refl ₁)

not-zero-is-one : (n : 𝟚) → n ≢ ₀ → n ≡ ₁
not-zero-is-one ₀ f = !𝟘 (₀ ≡ ₁) (f (refl ₀))
not-zero-is-one ₁ f = refl ₁

--               La igualdad es sobre X + Y                             ↓
-- ¬ (Id (X + Y) (inl x) (inr y))
inl-inr-disjoint-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → inl x ≢ inr y
inl-inr-disjoint-images {𝓤} {𝓥} {X} {Y} p = 𝟙-is-not-𝟘 q
 where
  f : X + Y → 𝓤₀ ̇
  f (inl x) = 𝟙
  f (inr y) = 𝟘

  q : 𝟙 ≡ 𝟘
  q = ap f p


right-fails-gives-left-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → P + Q → ¬ Q → P
right-fails-gives-left-holds (inl p) _ = p
right-fails-gives-left-holds (inr q) u = !𝟘 _ (u q)

{- [Example: formulation of the twin-prime conjecture]
-}

module twin-primes where
-- existen infinitos pares de primos de la forma (p, p + 2)
 open Arithmetic renaming (_×_ to _*_ ; _+_ to _∔_)
 open ℕ-order

 is-prime : ℕ → 𝓤₀ ̇
 is-prime n = (n ≥ 2) × ((x y : ℕ) → x * y ≡ n → (x ≡ 1) + (x ≡ n))

 twin-prime-conjecture : 𝓤₀ ̇
 twin-prime-conjecture = (n : ℕ) → Σ p ꞉ ℕ , ((p ≥ n)
                                           × (is-prime p
                                           × is-prime (p ∔ 2)))


-- Seminario encuentro 3
-- 24/04/2020

{- [Remaining Peano axioms and basic arithmetic]
-}


positive-not-zero : (x : ℕ) → succ x ≢ 0
positive-not-zero x p = 𝟙-is-not-𝟘 (g p)
 where
  f : ℕ → 𝓤₀ ̇
  f 0        = 𝟘
  f (succ x) = 𝟙

  g : succ x ≡ 0 → 𝟙 ≡ 𝟘
  g = ap f

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-lc : {x y : ℕ} → succ x ≡ succ y → x ≡ y
succ-lc = ap pred
-- Aca ya tenemos todos los axiomas de peano

-- Podemos que la igualdad en ℕ es decidible sin LEM
ℕ-has-decidable-equality : has-decidable-equality ℕ
ℕ-has-decidable-equality 0 0               = inl (refl 0)
ℕ-has-decidable-equality 0 (succ y)        = inr (≢-sym (positive-not-zero y))
ℕ-has-decidable-equality (succ x) 0        = inr (positive-not-zero x)
ℕ-has-decidable-equality (succ x) (succ y) = f (ℕ-has-decidable-equality x y)
 where
  f : decidable (x ≡ y) → decidable (succ x ≡ succ y)
  f (inl p) = inl (ap succ p)
  f (inr k) = inr (λ (s : succ x ≡ succ y) → k (succ-lc s))



-- La idea ahora es demostrar props sobre la aritmetica
module basic-arithmetic-and-order where

  open ℕ-order public
  open Arithmetic renaming (_+_ to _∔_) hiding (_×_)


  +-assoc : (x y z : ℕ) → (x ∔ y) ∔ z ≡ x ∔ (y ∔ z)

  +-assoc x y zero     = (x ∔ y) ∔ 0 ≡⟨ refl _ ⟩
                         x ∔ (y ∔ 0) ∎

  +-assoc x y (succ z) = (x ∔ y) ∔ succ z   ≡⟨ refl _     ⟩
                         succ ((x ∔ y) ∔ z) ≡⟨ ap succ IH ⟩
                         succ (x ∔ (y ∔ z)) ≡⟨ refl _     ⟩
                         x ∔ (y ∔ succ z)   ∎
   where
    IH : (x ∔ y) ∔ z ≡ x ∔ (y ∔ z)
    IH = +-assoc x y z

-- Notar que aca usamos muchas veces igualdad definicional, que no es
-- verdaderamente necesaria, pero clarifica las cosas.
-- Esta es la version sin nada

  +-assoc' : (x y z : ℕ) → (x ∔ y) ∔ z ≡ x ∔ (y ∔ z)
  +-assoc' x y zero     = refl _
  +-assoc' x y (succ z) = ap succ (+-assoc' x y z)


-- Lo de arriba sale facil, porque + esta definido recursivamente en
-- la segunda variable. Ahora veamos algo sobre la primera, que
-- complica un toque las cosas
  +-base-on-first : (x : ℕ) → 0 ∔ x ≡ x

  +-base-on-first 0        = refl 0

  +-base-on-first (succ x) = 0 ∔ succ x   ≡⟨ refl _     ⟩
                             succ (0 ∔ x) ≡⟨ ap succ IH ⟩
                             succ x       ∎
   where
    IH : 0 ∔ x ≡ x
    IH = +-base-on-first x


  +-step-on-first : (x y : ℕ) → succ x ∔ y ≡ succ (x ∔ y)

  +-step-on-first x zero     = refl (succ x)

  +-step-on-first x (succ y) = succ x ∔ succ y   ≡⟨ refl _     ⟩
                               succ (succ x ∔ y) ≡⟨ ap succ IH ⟩
                               succ (x ∔ succ y) ∎
   where
    IH : succ x ∔ y ≡ succ (x ∔ y)
    IH = +-step-on-first x y


  +-comm : (x y : ℕ) → x ∔ y ≡ y ∔ x

  +-comm 0 y = 0 ∔ y ≡⟨ +-base-on-first y ⟩
               y     ≡⟨ refl _ ⟩
               y ∔ 0 ∎

  +-comm (succ x) y = succ x ∔ y  ≡⟨ +-step-on-first x y ⟩
                      succ(x ∔ y) ≡⟨ ap succ IH          ⟩
                      succ(y ∔ x) ≡⟨ refl _              ⟩
                      y ∔ succ x  ∎
    where
     IH : x ∔ y ≡ y ∔ x
     IH = +-comm x y


  +-lc : (x y z : ℕ) → x ∔ y ≡ x ∔ z → y ≡ z

  +-lc 0        y z p = y     ≡⟨ (+-base-on-first y)⁻¹ ⟩
                        0 ∔ y ≡⟨ p                     ⟩
                        0 ∔ z ≡⟨ +-base-on-first z     ⟩
                        z     ∎

  +-lc (succ x) y z p = IH
   where
    q = succ (x ∔ y) ≡⟨ (+-step-on-first x y)⁻¹ ⟩
        succ x ∔ y   ≡⟨ p                       ⟩
        succ x ∔ z   ≡⟨ +-step-on-first x z     ⟩
        succ (x ∔ z) ∎

    IH : y ≡ z
    IH = +-lc x y z (succ-lc q)

-- Veamos que (x ≤ y) ⇔ Σ z ꞉ ℕ , x + z ≡ y.

-- Primero damos una def alternativa

  _≼_ : ℕ → ℕ → 𝓤₀ ̇
  x ≼ y = Σ z ꞉ ℕ , x ∔ z ≡ y

-- Y ahora vemos que son la misma cosa


  ≤-gives-≼ : (x y : ℕ) → x ≤ y → x ≼ y
  ≤-gives-≼ 0 0               l = 0 , refl 0
  ≤-gives-≼ 0 (succ y)        l = succ y , +-base-on-first (succ y)
  ≤-gives-≼ (succ x) 0        l = !𝟘 (succ x ≼ zero) l
  ≤-gives-≼ (succ x) (succ y) l = γ
   where
    IH : x ≼ y
    IH = ≤-gives-≼ x y l

    z : ℕ
    z = pr₁ IH

    p : x ∔ z ≡ y
    p = pr₂ IH

    γ : succ x ≼ succ y
    γ = z , (succ x ∔ z   ≡⟨ +-step-on-first x z ⟩
             succ (x ∔ z) ≡⟨ ap succ p           ⟩
             succ y       ∎)


  ≼-gives-≤ : (x y : ℕ) → x ≼ y → x ≤ y

  ≼-gives-≤ 0 0               (z , p) = ⋆

  ≼-gives-≤ 0 (succ y)        (z , p) = ⋆

  ≼-gives-≤ (succ x) 0        (z , p) = positive-not-zero (x ∔ z) q
   where
    q = succ (x ∔ z) ≡⟨ (+-step-on-first x z)⁻¹ ⟩
        succ x ∔ z   ≡⟨ p                       ⟩
        zero         ∎

  ≼-gives-≤ (succ x) (succ y) (z , p) = IH
   where
    q = succ (x ∔ z) ≡⟨ (+-step-on-first x z)⁻¹ ⟩
        succ x ∔ z   ≡⟨ p                       ⟩
        succ y       ∎

    IH : x ≤ y
    IH = ≼-gives-≤ x y (z , succ-lc q)
-- Despues vamos a ver que (x ≤ y) ≡ Σ z ꞉ ℕ , x + z ≡ y, pero todavia no podemos.

-- Props sobre ≤

  ≤-refl : (n : ℕ) → n ≤ n
  ≤-refl zero     = ⋆
  ≤-refl (succ n) = ≤-refl n

  ≤-trans : (l m n : ℕ) → l ≤ m → m ≤ n → l ≤ n
  ≤-trans zero m n p q = ⋆
  ≤-trans (succ l) zero n p q = !𝟘 (succ l ≤ n) p
  ≤-trans (succ l) (succ m) zero p q = q
  ≤-trans (succ l) (succ m) (succ n) p q = ≤-trans l m n p q

  ≤-anti : (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
  ≤-anti zero zero p q = refl zero
  ≤-anti zero (succ n) p q = !𝟘 (zero ≡ succ n) q
  ≤-anti (succ m) zero p q = !𝟘 (succ m ≡ zero) p
  ≤-anti (succ m) (succ n) p q = ap succ (≤-anti m n p q)

  ≤-succ : (n : ℕ) → n ≤ succ n
  ≤-succ zero     = ⋆
  ≤-succ (succ n) = ≤-succ n

  zero-minimal : (n : ℕ) → zero ≤ n
  zero-minimal n = ⋆

  -- :(
  unique-minimal : (n : ℕ) → n ≤ zero → n ≡ zero
  unique-minimal zero p = refl zero
  unique-minimal (succ n) p = !𝟘 (succ n ≡ zero) p

  ≤-split : (m n : ℕ) → m ≤ succ n → (m ≤ n) + (m ≡ succ n)
  ≤-split zero n l = inl l
  ≤-split (succ m) zero l = inr (ap succ (unique-minimal m l))
  ≤-split (succ m) (succ n) l = +-recursion inl (inr ∘ ap succ) (≤-split m n l)

  _<_ : ℕ → ℕ → 𝓤₀ ̇
  x < y = succ x ≤ y

  infix 10 _<_

  not-<-gives-≥ : (m n : ℕ) → ¬(n < m) → m ≤ n
  not-<-gives-≥ zero n u = zero-minimal n
  not-<-gives-≥ (succ m) zero = dni (zero < succ m) (zero-minimal m)
  not-<-gives-≥ (succ m) (succ n) = not-<-gives-≥ m n

  bounded-∀-next : (A : ℕ → 𝓤 ̇ ) (k : ℕ)
                 → A k
                 → ((n : ℕ) → n < k → A n)
                 → (n : ℕ) → n < succ k → A n
  bounded-∀-next A k a φ n l = +-recursion f g s
   where
    s : (n < k) + (succ n ≡ succ k)
    s = ≤-split (succ n) k l

    f : n < k → A n
    f = φ n

    g : succ n ≡ succ k → A n
    g p = transport A ((succ-lc p)⁻¹) a


-- Las raices de una funcion
  root : (ℕ → ℕ) → 𝓤₀ ̇
  root f = Σ n ꞉ ℕ , f n ≡ 0

  _has-no-root<_ : (ℕ → ℕ) → ℕ → 𝓤₀ ̇
  f has-no-root< k = (n : ℕ) → n < k → f n ≢ 0

  is-minimal-root : (ℕ → ℕ) → ℕ → 𝓤₀ ̇
  is-minimal-root f m = (f m ≡ 0) × (f has-no-root< m)


  at-most-one-minimal-root : (f : ℕ → ℕ) (m n : ℕ)
                           → is-minimal-root f m → is-minimal-root f n → m ≡ n

  at-most-one-minimal-root f m n (p , φ) (q , ψ) = c m n a b
   where
    a : ¬(m < n)
    a u = ψ m u p

    b : ¬(n < m)
    b v = φ n v q

    c : (m n : ℕ) → ¬(m < n) → ¬(n < m) → m ≡ n
    c m n u v = ≤-anti m n (not-<-gives-≥ m n v) (not-<-gives-≥ n m u)


  minimal-root : (ℕ → ℕ) → 𝓤₀ ̇
  minimal-root f = Σ m ꞉ ℕ , is-minimal-root f m

  minimal-root-is-root : ∀ f → minimal-root f → root f
  minimal-root-is-root f (m , p , _) = m , p

  bounded-ℕ-search : ∀ k f → (minimal-root f) + (f has-no-root< k)
  bounded-ℕ-search zero f = inr (λ n → !𝟘 (f n ≢ 0))
  bounded-ℕ-search (succ k) f = +-recursion φ γ (bounded-ℕ-search k f)
   where
    A : ℕ → (ℕ → ℕ) → 𝓤₀ ̇
    A k f = (minimal-root f) + (f has-no-root< k)

    φ : minimal-root f → A (succ k) f
    φ = inl

    γ : f has-no-root< k → A (succ k) f
    γ u = +-recursion γ₀ γ₁ (ℕ-has-decidable-equality (f k) 0)
     where
      γ₀ : f k ≡ 0 → A (succ k) f
      γ₀ p = inl (k , p , u)

      γ₁ : f k ≢ 0 → A (succ k) f
      γ₁ v = inr (bounded-∀-next (λ n → f n ≢ 0) k v u)


  root-gives-minimal-root : ∀ f → root f → minimal-root f
  root-gives-minimal-root f (n , p) = γ
   where
    g : ¬(f has-no-root< (succ n))
    g φ = φ n (≤-refl n) p

    γ : minimal-root f
    γ = right-fails-gives-left-holds (bounded-ℕ-search (succ n) f) g




--infix   0 _∼_
infixr 50 _,_
infixr 30 _×_
infixr 20 _+_
infixl 70 _∘_
infix   0 Id
infix   0 _≡_
infix  10 _⇔_
infixl 30 _∙_
infixr  0 _≡⟨_⟩_
infix   1 _∎
infix  40 _⁻¹
--infix  10 _◁_
--infixr  0 _◁⟨_⟩_
--infix   1 _◀
--infix  10 _≃_
--infixl 30 _●_
--infixr  0 _≃⟨_⟩_
--infix   1 _■
--infix  40 _∈_
--infix  30 _[_,_]
infixr -1 -Σ
infixr -1 -Π
--infixr -1 -∃!
