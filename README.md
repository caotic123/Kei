# Kei Language

Kei is a depenedent language with small and expressive core based on λΠ-calculus modulo rewriting.

#The Core
The core of key is based on a type theory called Lambda-Pi-Calculus Modulo Calculus. Despite the core being very experimental, Kei is able to prove
somes properties through a encoding of typed rules.

Rules are defined as in [Dedukti](https://github.com/Deducteam/Dedukti), for example a sized list vector can be defined like :

```
Rule Vector : (forall (n : nat) -> (Vector n)).
Rule Cons : (forall (n : nat) -> (_ : type) -> (Vector n) -> (Vector (S n))).
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

