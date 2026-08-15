package souther.compiler.examples;

import souther.compiler.generated.MemoryClassLoader;

/**
 * Where a run's answerer comes from, and what makes the answerer and the values it is handed one
 * execution domain.
 *
 * <p>A run owns the loader its values are built in. It has to: a row's fixtures are decoded and held
 * to their invariants whether or not there is anything to run them against, so the classes a compile
 * generated are a fact about the compile and not about whoever applies a behavior. An answerer that
 * applies those same classes is therefore one that is <em>given</em> that loader, and an answerer that
 * brings its own ignores it.
 *
 * <p>That is what this is for. An answerer taken as a value beside a loader would let a compile's own
 * implementation be paired with a run whose values are some other loader's — and the two would not
 * disagree at the boundary, because a behavior's {@code apply} is erased, but inside the behavior where
 * the first cast is. Made here, the pairing cannot be stated wrongly.
 *
 * <p>It settles the stand-ins as well, which is the same question one step further in. A behavior's
 * stand-ins are made into instances the implementation's constructor can take, so the implementation
 * and the stand-ins are in one loader or the behavior has no stand-ins at all. {@link #generatedHere}
 * is the first: the loader, the {@code $Impl} and the stand-ins are one compile's. An implementation
 * supplied from outside is the second: it is supplied for an injected behavior, and an injected
 * behavior has no requirements, so no stand-in ever crosses to it.
 */
@FunctionalInterface
public interface Answering {

    /**
     * The answerer for a run over {@code module}, whose values are built in {@code compiled}.
     *
     * @param module   the module whose rows are being evaluated
     * @param compiled the classes this compile generated, defined once
     */
    Answerer over(String module, MemoryClassLoader compiled);

    /** The compile's own: the {@code $Impl} it emitted, constructed with the row's stand-ins and
     *  applied, all in the loader the run built. */
    static Answering generatedHere() {
        return GeneratedImplementation::new;
    }
}
