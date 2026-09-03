package souther.compiler.check;

import souther.compiler.core.DeclaredOperation;

/**
 * A fact about an operation, once it has been held to the library that declares one.
 *
 * <p>What {@link souther.compiler.semantics.OperationFacts} states is written in the vocabulary
 * somebody authors a fact in: a {@link souther.compiler.types.ValueName} for the operation it is
 * about, an {@link souther.compiler.semantics.ArgumentRef} for an argument it names, another name
 * for an operation it relates this one to. None of those says the library has such an operation, or
 * that it takes an argument there, or that the two signatures let one stand for the other. That is
 * what {@link OperationFactBinder} settles against {@link souther.compiler.stdlib.Stdlib}.
 *
 * <p>This is what a fact comes to once it has. A reader below the binding holds one of these and
 * asks nothing further: the operations it names have been read against their declarations, so what
 * is left to do with one is to use it. A reader handed the authoring value instead would have the
 * name and the table and could put the same question again — and would get an answer that agrees
 * with the binder's for exactly as long as nobody changes either.
 *
 * <p><b>One arm so far.</b> Every other kind of fact is still read from the authoring index below
 * the binding, and what holds those up is that the binder walks them all and refuses a declaration
 * that does not match. That is a check and not a carrier: the fact a reader goes on to read is the
 * one that was authored, not the one that was held.
 */
sealed interface BoundOperationFact {

    /**
     * An emptiness check and the size it means, each read against its declaration.
     *
     * <p>What this carries that the authoring fact cannot: the two operations take the same
     * argument, and the second answers a number where the first answers a truth. A reader rewriting
     * one call into the other moves the arguments across unchanged, so those are the conditions
     * under which such a rewrite says the same thing — asked once, where both declarations are in
     * hand, rather than by the reader that has a call and a name.
     */
    record MeansTheSameAsSizeOfNought(DeclaredOperation predicate, DeclaredOperation size)
            implements BoundOperationFact {}
}
