package souther.compiler.query;

/**
 * A key whose answer is given rather than computed: the text of a source, the module path a compile
 * resolves against. These are the leaves of the graph and the only part of a compilation that
 * changes from outside — everything else is a function of them.
 *
 * <p>An input nobody gave a value for is absent, not an error. A compile is often asked about a
 * file that is not there: an import naming a module the workspace does not contain, an
 * {@code examples for} file whose target was never opened. The key that asked sees the absence and
 * reports it where the author can act on it, which is not here.
 *
 * <p><b>What one of these answers with is what was supplied, and its equality is a detector.</b>
 * {@link Key} says what a question this compiler computes may answer with, and this is the other
 * quantity: nothing computes one of these, so the equality of what is here decides whether the
 * outside changed rather than whether a compile came to the same thing. What it costs is that
 * supplying a new one reads as a change, which says more work than was needed and never less.
 *
 * <p><b>What this compilation was told, and never how one machine carries it out.</b> The sources,
 * the path they resolve against, the terms a run is held to — every caller of this compiler has one
 * of those, whatever runs its programs. The arrangement that keeps a term on a particular machine —
 * a thread, a stack, a wall clock — is not something a compilation was told and means nothing to an
 * execution that is not that machine's. It is offered where that implementation is named, which is
 * {@code Compilation.withJvmExampleDeadlines}, and an input carrying one is how the boundary came
 * to state a wait the run was not being given.
 */
public interface Input<T> extends Key<T> {

    @Override
    default Answer<T> compute(Db db) {
        return Answer.absent();
    }
}
