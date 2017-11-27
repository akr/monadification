# monadification plugin for Coq

This software provides Coq commands to convert Gallina definitions into
monadic style.
The converted definitions enable us to prove various properties which is
not possible to prove in direct style: integer overflow is not occur, for example.

## Home page

https://github.com/akr/monadification

## Requiements

- Coq 8.7 (Coq 8.6 doesn't work)

## How to build and install

    make
    make install

## How to run

    coqide sample/pow.v

## How to use

See sample/ directory.

## Authors

- Tanaka Akira
- Reynald Affeldt
- Jacques Garrigue

## Acknowledgment

This work is supported by JSPS KAKENHI Grant Number 15K12013.

## Copyright

Copyright (C) 2016- National Institute of Advanced Industrial Science and Technology (AIST)
"monadification plugin for Coq"
AIST program registration number: H29PRO-2091

## License

GNU Lesser General Public License Version 2.1 or later
