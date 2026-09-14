package souther.compiler.examples;

import souther.compiler.check.Sig;
import souther.compiler.generated.GeneratedImplementations;
import souther.compiler.generated.MemoryClassLoader;

import java.util.Map;
import java.util.Set;

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
     * The answerer for a run over the module {@code generated} is of, whose values are built in
     * {@code compiled}.
     *
     * <p>What the compile generated an implementation for is handed over rather than worked out from
     * either of the things here. Not from the declarations, because how a behavior is written is not
     * what a run can apply — that is the question this seam exists to own. And not from the loader:
     * a class that is not in it is a class that could not be reached, which is a failure, and reading
     * membership for this would answer that failure with "nothing applies this behavior", which is
     * not a failure at all.
     *
     * @param generated what the compile emitted an implementation for, and which module of
     * @param compiled  the classes that compile generated, defined once
     */
    Answerer over(GeneratedImplementations generated, MemoryClassLoader compiled);

    /** The compile's own: the {@code $Impl} it emitted, constructed with the row's stand-ins and
     *  applied, all in the loader the run built. */
    static Answering generatedHere() {
        return GeneratedImplementation::new;
    }

    /**
     * {@code implementation} for the behaviors {@code answersFor} names, and {@link #generatedHere}
     * for every other.
     *
     * <p>Which declarations it reads values by is worked out from the instance, by its own loader's
     * class files, so a caller cannot state it wrongly. Which behaviors it answers for is not: it is
     * handed over, because it is the caller's statement of what this instance is being supplied for.
     *
     * <p>Whether a behavior may be supplied for at all is a rule of whoever admits a binding and not
     * of this seam. {@link SoutherExamples#bind} takes an instance and admits it only for behaviors
     * written without a body, those being the ones whose rows had nothing to run them. This seam is
     * lower down and answers the question it is asked: a run may be given an answerer that applies
     * anything, which is what an answerer bringing a second loader's classes for a bodied behavior
     * already does.
     *
     * <p>{@code sigs} is the module's, and is what a value crossing to the instance's classes is
     * read as. It is the run's answer and not the instance's: what a row states is of the module the
     * rows are written for, and holding that module's declarations against the instance's is
     * {@code DeclarationAgreement}'s, done before any row is handed over.
     *
     * <p>{@code applied} is where the instance is applied. It is handed over rather than decided
     * here because an implementation supplied from outside answers in the world the caller called
     * from, and which world that is belongs to whoever arranged the run.
     */
    static Answering bound(Object implementation, Set<String> answersFor, Map<String, Sig> sigs,
                           CallerApplication applied) {
        return (generated, compiled) -> new BoundImplementation(implementation, answersFor, sigs,
                new GeneratedImplementation(generated, compiled), generated.module(), applied);
    }
}
