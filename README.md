Implementation of a solver for [Rummy](https://en.wikipedia.org/wiki/Rummy)

Due to me growing up with a different version, this is using colors and numbers 1 to 13 instead of normal playing cards.

When called with a file containing a card specification like:
```
REQUIRED:
red 1
red 2
red 3

OPTIONAL:
yellow 4
red 4
blue 4
yellow 5
yellow 6
```

It will output the best possible arrangements using as many OPTIONAL cards as possible and all REQUIRED cards.
