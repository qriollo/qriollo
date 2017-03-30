Qriollo
=======

El lenguaje de programación más boludo del mundo.

[http://qriollo.github.io](http://qriollo.github.io)


## Instalar en Debian 

Primero instalamos las dependencias 
```
sudo apt-get install libncurses5-dev haskell-platform
sudo cabal update
cabal install haskeline

```
Clonamos 

```
git clone https://github.com/qriollo/qriollo.git
cd qriollo/

```

Copilamos

```
ghc -isrc --make src/Main.hs -o qr -rtsopts
```

Probamos 

```
$ ./qr HolaMundo.q
Hola mundo

```
