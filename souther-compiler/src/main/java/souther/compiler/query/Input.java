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
 * outside changed rather than whether a compile came to the same thing. A way of running something
 * — how a module is found, how long a piece of work gets — is supplied that way, and no compute
 * could build it instead. What it costs is that supplying a new one reads as a change, which says
 * more work than was needed and never less.
 */
public interface Input<T> extends Key<T> {

    @Override
    default Answer<T> compute(Db db) {
        return Answer.absent();
    }
}
