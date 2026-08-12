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
 */
public interface Input<T> extends Key<T> {

    @Override
    default Answer<T> compute(Db db) {
        return Answer.absent();
    }
}
