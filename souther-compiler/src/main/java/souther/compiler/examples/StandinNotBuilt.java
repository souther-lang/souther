package souther.compiler.examples;

import souther.compiler.types.ValueName;

/**
 * A stand-in the answerer was asked for and could not make into something the implementation can be
 * constructed with.
 *
 * <p>Not an answerer declining to take stand-ins. Which stand-ins an answerer is asked for is settled
 * where the execution domain is ({@link Answering}), so an answerer is never handed one it has no
 * business with. This is that answerer trying and the making failing — the dependency's base class not
 * being there, its {@code apply} not being found, the subclass not defining.
 *
 * <p>Raised from {@link Answerer#applying} and never from {@link Answerer.Applying#to}. Where a row
 * stops decides what its outcome records, and a row whose stand-ins could not be made never applied
 * the behavior: it stops where a row with no fake for a dependency stops, and says the same thing
 * about itself.
 */
public final class StandinNotBuilt extends RuntimeException {

    private static final long serialVersionUID = 1L;

    /** Transient because a behavior is not a serializable value and this is never written out: it
     *  is raised and caught inside one compile, between an answerer and the row that asked it. */
    private final transient ValueName.Behavior dependency;

    public StandinNotBuilt(ValueName.Behavior dependency, String why) {
        super(why);
        this.dependency = dependency;
    }

    /**
     * The dependency whose stand-in could not be made, as the declaration it is.
     *
     * <p>The behavior and not the name this module reaches it by. What could not be made is an
     * instance of the base generated where the behavior is declared, which is not always the module
     * the row is written in, and a reader deciding where to send an author needs to know which.
     */
    public ValueName.Behavior dependency() {
        return dependency;
    }
}
