package souther.compiler.meta;

import souther.compiler.ast.Ast;
import souther.compiler.types.ValueName;
import souther.compiler.check.Scoping;
import java.util.List;

import java.util.Map;
import java.util.Set;

/**
 * A module this compiler restored from an artifact and then checked: everything an importer needs to
 * build against it, and nothing that was still being worked out.
 *
 * <p>Holding one is holding a module whose import lines have been read. There is no value for a
 * module that was decoded and not checked, and none for a module that was never read at all — the
 * only implementation is {@link ModuleReadback}'s, and only a reading that answered
 * {@link Readback.Ready} builds one. So the reader that took the module and left the table behind
 * cannot be written, which is what it did, leaving an invariant's bare names resolving against
 * nothing in every project but the one that wrote it.
 *
 * <p>Sealed rather than a record, because a record is a constructor. Read anywhere, built in one
 * place: outside {@code souther.compiler.meta} nothing can make one at all, and inside it the one
 * implementation is the readback's own.
 *
 * <p>The three are one fact and travel together. The module no longer says what its bare names mean
 * — the lines that said so are dropped once read — so {@link #libraryNames()} is the only thing that
 * does. Which behaviors are injection targets is not written in any declaration and does not survive
 * as source, so it cannot be worked out again from the module either.
 *
 * <p>Told apart from {@link PublishedUniverse.Read}, which is a stage further on: that one holds a
 * module every name of which has been answered, against a universe of other modules. This is what
 * one artifact gives before any of that is asked.
 */
public sealed interface ReadableModule permits ModuleReadback.AsRead {

    /** The module as the front end read it, with its library import lines dropped. */
    Ast.Module module();

    /**
     * What it declares, by the name written there — indexed once, where it was read.
     *
     * <p>Here rather than worked out by whoever needs it, because indexing is a step of the reading
     * and can refuse: a set of declarations one module may not have is an artifact this compiler
     * will not read ({@link Readback.Failure.InvalidDeclarations}). A reader that indexed for itself
     * would be asking, after the fact, a question the reading has already answered — and would have
     * to decide what to do when the answer is no, which is how a known failure came to travel as a
     * raise out of a lookup.
     */
    Map<String, Ast.Def> declarations();

    /** The behaviors this module publishes no implementation for. */
    Set<String> injectedBehaviors();

    /** What its library import lines brought in, which the module itself no longer says. */
    List<Scoping.Claim> libraryNames();
}
