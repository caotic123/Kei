# Kei Language

Kei is a dependent language with a small and expressive core based on λΠ-calculus modulo rewriting.

# Checking if everything is okay

Go to folder examples and runs in that folder :

```
Kei foo
```

If everything is okay you should see a message like this:

```
Bar : Just Foo.
```

The "Just" is *just* that Kei can infer the construction evaluated. So, when you check the terms Kei automatically eval the EVAL expression and return the value.

# Basic

As an example let's define syntactical equality :

```
Rule type : Type.
Rule ≡ : (forall (n : type) (n' : type) -> Type).
Rule refl : (forall (n : type) -> (≡ n n)).
```

Extend the symbols with a static type with a scheme for proving :
```
Rule eq_rect : (forall (n : type)
                       (n' : type)
                       (x : (≡ n n'))
                       (a : type)
                       (f : (forall (a : type) (a' : type) -> Type))
                       (H : (f a n))
                       ->
                       (f a n')).   

f_sym = (\(forall (x : type) (y : type) -> Type) | x y => (≡ y x)).
symmetry = (\(forall (x : type) (y : type) (H' : (≡ x y)) -> (≡ y x)) 
   | x y H' => (eq_rect x y H' x f_sym (refl x))).
```

You could ask yourself if you need always specific a symbol scheme for proving. The idea is that you able to working
with different approaches and logic system, however, the small core of Kei is expressive enough for represent trivial and more complex proofs like induction proofs with a few numbers of statics symbols and rewriting rules through of composition of rules.

# The Core
The core of Key is based on a type theory called Lambda-Pi-Calculus Modulo Calculus. Despite the core being very experimental, Kei can prove
some properties through an encoding of a typed rule.

Rules of static symbols are defined as in [Dedukti](https://github.com/Deducteam/Dedukti), for example, a sized list vector can be defined like :

```
Rule Vector : (forall (x : nat) -> Type).
Rule Nil : (Vector Z).
Rule Cons : (forall (x : nat) (y : A) (H : (Vector x)) -> (Vector (S x))).
```

Rewriting Rules is expressed like :

```
tail = (\(forall (n' : nat) (vec : (Vector n')) -> Maybe) | x vec => [
  vec of Maybe
    |{x' y H}(Cons x' y H) => (Surely x' H)
    |{}Nil => Nothing
]).
```


One of the most interesting properties of Kei is you can combine statics symbols with rewriting rules to create another logic system, like COC. In λΠ-calculus modulo the conversion of terms is available between β-reduction and Γ-Reduction, this means that a type can be changed through a type relation of a rewriting rule. Of course, if there is a well-typed substitution rule σ(x). 

# Installation

You may need GHC and...
```
git clone https://github.com/caotic123/Kei
cd src
ghc --make Checker.hs -o Kei
*put in your enviroment* 
export PATH="$PATH:~/.../Kei Language/src"
```

Before that, check if everything is okay just going to example folder and ...

```
Kei foo
```

# Rules

![Rules](https://i.imgur.com/zdBnyGI.jpg)

# What wasn't implemented

- Totally Checker
- Confluent Pattern Matching (avoid non Left-Linear Rules), this topic is a bit complicate Dedukti do a optimization of -  patterns matching to solve this.
- Impossible clause
- Patterns matching clauses checking
- Confluent Checker
- A backend :)
- *Fast* type checking


# Sources

This work is very influenced by :  
Typechecking in the lambda-Pi-Calculus Modulo : Theory and Practice (Ronan Saillard).  
The λΠ-calculus Modulo as a Universal Proof Language (Mathieu Boespflug1, Quentin Carbonneaux2 and Olivier Hermant3).  
Dedukti: a Logical Framework based on the λΠ-Calculus Modulo Theory (Ali Assaf1, et al).  

Besides the designer language like syntax was defined with the help of thoughts of [Lucas](https://github.com/luksamuk) and [Davidson](https://github.com/davidsonbrsilva).


```
