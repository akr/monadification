# monadification plugin for Coq

This software provides Coq commands to convert Gallina definitions into
monadic style.
The converted definitions enable us to prove various properties which is
not possible to prove in direct style: integer overflow is not occur, for example.

## Home page

https://github.com/akr/monadification

## Requiements

- Coq 8.6 (Coq 8.5 doesn't work)

## How to build

    make

## How to run

    coqide -I src -Q theories Monadification sample/pow.v

## How to use

See sample/ directory.

## Authors

- Tanaka Akira
- Reynald Affeldt
- Jacques Garrigue

## Copyright

Copyright (C) 2016- National Institute of Advanced Industrial Science and Technology (AIST)
"monadification plugin for Coq"
AIST program registration number: H29PRO-2091

## License

GNU Lesser General Public License Version 2.1 or later
