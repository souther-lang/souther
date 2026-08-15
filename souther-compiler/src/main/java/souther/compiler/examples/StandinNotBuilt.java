package souther.compiler.examples;

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

    private final String dependency;

    public StandinNotBuilt(String dependency, String why) {
        super(why);
        this.dependency = dependency;
    }

    /** The dependency whose stand-in could not be made, as the module names it. */
    public String dependency() {
        return dependency;
    }
}
