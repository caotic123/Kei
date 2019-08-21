# Kei Language

Kei is a depenedent language with small and expressive core based on λΠ-calculus modulo rewriting.

# The Core
The core of key is based on a type theory called Lambda-Pi-Calculus Modulo Calculus. Despite the core being very experimental, Kei is able to prove
somes properties through a encoding of typed rules.

Rules of static symbols are defined as in [Dedukti](https://github.com/Deducteam/Dedukti), for example a sized list vector can be defined like :

```
Rule Vector : (forall (n : nat) -> (Vector n)).
Rule Cons : (forall (n : nat) -> (_ : type) -> (Vector n) -> (Vector (S n))).
```

Rewriting Rules is expressed like :

```
add = (\(forall (n : nat) (y : nat) -> nat) | n y => [n of nat
  |{x}(S x) => (S (add n x))
  |{}Z => y]).
```

One of most interesting property of Kei is you can combine statics symbols with rewriting rules to create another logic system, like COC. In λΠ-calculus modulo the conversion of terms is avaliable between β-reduction and Γ-Reduction, this means that a type can be changed through a type relation of a rewriting rule. Of course, if there is a well-typed substuition rule σ(x). 

# Working

As example let's define a syntactically equality :

```
Rule type : Type.
Rule ≡ : (forall (n : type) (n' : type) -> Type).
Rule refl : (forall (n : type) -> (≡ n n)).
```

Extend the symbols with a static type with scheme for proving :
```
Rule eq_rect : (forall (n : type)
                       (n' : type)
                       (x : (≡ n n'))
                       (a : type)
                       (f : (forall (a : type) (a' : type) -> Type))
                       (H : (f a n))
                       ->
                       (f a n')).   
```

After that, prove that ≡ hold a symmetry property

```
f_sym = (\(forall (x : type) (y : type) -> Type) | x y => (≡ y x)).
symmetry = (\(forall (x : type) (y : type) (H' : (≡ x y)) -> (≡ y x)) | x y H' => (eq_rect x y H' x f_sym (refl x))).
```

# Installation

You may need GHC and...
```
git clone https://github.com/caotic123/Kei
cd src
ghc --make Checker.hs -o Kei
put in your enviroment export PATH="$PATH:~/.../Kei Language/src"
```

Before that, check if everything is okay going to example folder and ...

```
Kei foo
```

