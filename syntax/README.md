# The Souther syntax contract

This directory states what Souther source is, for any implementation that reads it. The compiler
in this repository is one such implementation and is tested against what is here; it is not where
this comes from.

- `grammar.ebnf` is the grammar, and it is normative. Its head defines the notation: ISO EBNF with
  `@node` marking the productions that are nodes of the contract syntax tree, two grammatical
  parameters, and restrictions for what plain EBNF does not say — a line break before an argument
  list, which `match` a `|` belongs to, and the readings a prefix commits to.
- `vocabulary.json` lists the reserved words, the contextual words, the fixed spellings and the open
  token classes the grammar is written in.
- `corpus/` holds sources in tree-sitter's test format. A case either gives the contract tree its
  source is, or is marked `:error` and says only that the source is not Souther. Where a reading of
  a refused source stops, and what it recovers, is not part of the contract.

`corpus/line-terminators.txt` writes LF, CR LF and a CR on its own where each case needs one, and is
kept byte for byte (see `.gitattributes`).

## What is stable

The name of a production marked `@node` is the identifier of that node, and the spellings in
`vocabulary.json` are the language's tokens. Renaming or removing either is a breaking change.
Productions without `@node` name parts of rules and may be renamed or refactored freely, and the
compiler's own syntax kinds are not part of this contract.

`formatVersion` in `vocabulary.json` versions how that file is laid out, not the language. The
language is versioned by the release this directory is part of.
