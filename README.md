# LLIO
Proving Non-interference with Liquid Haskell

Mechanization in Liquid Haskell of the proofs from https://cseweb.ucsd.edu/~dstefan/pubs/stefan:2017:flexible.pdf


# How to run 

- Install Liquid Haskell

```
cabal install liquidhaskell
```

- Check src/LLIO

```
liquid src/LLIO.hs
```

Or use cabal test

```
cabal configure --enable-tests
cabal build
cabal test
```