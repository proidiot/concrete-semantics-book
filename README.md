# concrete-semantics-book
Working on problems from [Concrete Semantics by Nipkow and Klein](http://concrete-semantics.org/).

There are a few ways to get the book, but I bought it [on Amazon](https://www.amazon.com/Concrete-Semantics-Isabelle-Tobias-Nipkow/dp/3319105418/).

This repo certainly isn't going to be pretty as I'm still learning the language,
but hopefully things will look better as I progress father into the book.

## Try it out!
It should be possible to open the various `foo.thy` files in the Isabelle IDE.

To build the sessions and resulting PDFs from the comand line, set
`ISABELLE=path/to/bin/isabelle` appropriately (wheether as an exported
environemt variable or as an inline `make` variable) and run `make`.

If you need to add a new theory file to an directory, unfortunately you
currently need to manually edit the `ROOT` file. If you need to create a new
directory, unfortunately you currently need to manually run
`${ISABELLE} mkroot -A "${LATEX_AUTHOR}" -T "${LATEX_TITLE}"` from within the
new directory and add the theory entries as described.
_TODO_ Have the `Makefile` handle the `ROOT` files for us.

## Better resources than this repo if you're stuck
Once you get to part 2 of the book, the base definitions for the IMP language
as described are [included in the Isabelle source code itself](https://github.com/isabelle-prover/mirror-isabelle/tree/master/src/HOL/IMP).
During my own attempts to construct these definitions, there were some aspects
that had been lost on me, such as [cleaning the search space](https://github.com/isabelle-prover/mirror-isabelle/blob/46ea8b8edd51a64f374206fa672d8ce26631ad78/src/HOL/IMP/Big_Step.thy#L62-L66)
and [manipulating the schema](https://github.com/isabelle-prover/mirror-isabelle/blob/46ea8b8edd51a64f374206fa672d8ce26631ad78/src/HOL/IMP/Big_Step.thy#L73-L84).
As such, if you too wish to attempt to construct these definitions for yourself
as you proceed through the examples in order to maximize your understanding of
the system, it would likely be worth digging through this official
implementation definition if you get stuck.

If you would also like the get the CLI stuff working,
[the system manual](https://isabelle.in.tum.de/doc/system.pdf) is likely the
correct place to look.

If you need help with more advanced function construction (for example, I wanted
to take an approach that seemed easier to conceptualize but needed a non-default
termination proof), then Alexander Krauss'
[function tutorial](https://isabelle.in.tum.de/doc/functions.pdf) may be exactly
what you need as well.

Once you are into Isar territory,
[the Isar reference](https://isabelle.in.tum.de/doc/isar-ref.pdf) will probably
be worthing keeping on hand.

Two other examples I've seen of folks going through this book which might prove
more useful than my own efforts are:
- [EduPH/concrete-semantics-Sols](https://github.com/EduPH/concrete-semantics-Sols)
- [kolya-vasiliev/concrete-semantics](https://github.com/kolya-vasiliev/concrete-semantics)

## Bugs/Suggestions/"Why on earth did you make such a dumb proof?!"
Much of what is in this repo is just whatever tired Charlie slapped together
while trying to figure out why the tools didn't behave as expected a few minutes
before going to sleep. However, I do very much welcome feedback as the whole
point of this effort is to learn the material. Rather than trying to contact me
by other more diplomatic means, please do leave public feedback (if you are
comfortable with that) in the form of a GitHub issue.
