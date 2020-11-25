# Outline:

## Preface

This book provides an overview of the data format definition language Parsley. Within this book, we motivate the problems that Parsley aims to tackle, provide the requisite background to understand Parsley's contributions, explain and justify design decisions, and, perhaps of greatest utility to the parser-writing practitioner, we provide documentation, tutorials, and examples to get the reader up and running with Parsley.

This book corresponds to version x of Parsley. For this iteration, we have a working type-checker, to which we will still make modifications. We have not yet implemented the Parsley compiler.

## Summary/Abstract
- Explain book in a nutshell

## Introduction:
- What is Parsley?
- What is PVS?
- What tools are we building?
- What is in this book?

## The Parsley Language (primer; similar to Parsley paper but focus on theory... also provide primers on key related topics such as attribute grammars and PEGs that are cursorily discussed in paper):
- What is the problem?
- Briefly discuss related work and differentiate Parsley
- What does Parsley do to address problems?
- What are the key features of Parsley?
- How does PVS fit in?
- PEGs
  - BNF
  - EBNF
  - Ordered Choice
- Attribute Grammars
  - Inherited Attributes
  - Synthesized Attributes
  - A visualization (perhaps using a parse tree)
- Guards
- Modularization

## The Parsley Type Checker:
- Present the general approach to type checking (Prashant M is probably best-suited to do this)
- Present progressively more complex aspects of Parsley with progressively more complex examples. We can start w/ toy examples or extremely simple specifications, such as PBM or PGM, and go from there.
- Provide some real-world challenges and discuss how we can tackle them using Parsley
  - E.g., present Parsley programming idioms used to tackle common parsing challenges (e.g., call w/ Drew highlighted the need to address having optional fields in a packet)


## The Parsley Compiler:
- Tbd

## Collection of other topics:
- future work
- how to get in contact w/ Parsley folks.
- solicit feedback? where/how do readers provide feedback?
