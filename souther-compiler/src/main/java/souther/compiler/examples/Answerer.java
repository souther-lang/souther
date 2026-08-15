package souther.compiler.examples;

import souther.compiler.observe.Applied;

import java.util.List;

/**
 * What applies a behavior for a row.
 *
 * <p>Everything about a row that is a fact about the loader its values live in is on this side of the
 * boundary: which classes the implementation is, how it is constructed, how a stand-in becomes
 * something that constructor can take, and how the behavior is entered. Everything that is a fact
 * about what a row <em>means</em> stays on the other: which value a fixture states, which row of a
 * fake's table answers, what an answer is compared against, what a failure is reported as, what the
 * row is held to.
 *
 * <p>One implementation today, {@link Answering#generatedHere}: the {@code $Impl} this compile emitted,
 * constructed with the row's stand-ins and applied through the loader the run built. An implementation
 * supplied from outside a compile is the second, and it brings its own classes.
 *
 * <p>Nothing here reports anything. A diagnostic is a statement about a row and this is not about a
 * row, so what an answerer cannot do it raises and the row says what that means. Three things can go
 * wrong and they are three because what they say is not the same: {@link StandinNotBuilt} is a
 * stand-in that could not be made, {@link ImplementationNotReached} is the implementation not being
 * reachable at all, and {@link InvocationFailure} is the applied code coming back with a failure. Only
 * the last is about the model.
 */
public interface Answerer {

    /**
     * What a row's outcome records as having applied the behavior.
     *
     * <p>One answer for the whole of this answerer, the same for every row it runs. Something that
     * chooses between several answerers per row — one that routes, one that falls back to another —
     * does not have one answer here, and for such a thing the question belongs to the application
     * rather than to the answerer and moves to {@link Applying}.
     */
    Applied applied();

    /**
     * What will apply {@code behavior} for this row, with {@code standins} answering for what it
     * depends on.
     *
     * <p>Separate from applying it because the two are separate things to have got as far as. Making a
     * stand-in into an instance is building the environment the behavior runs in, and a row that could
     * not get an environment never entered the behavior — which is what its outcome has to be able to
     * say. So this is where a stand-in that could not be made is raised, and
     * {@link Applying#to} is where the behavior running is.
     *
     * @throws StandinNotBuilt where a stand-in could not be made into something the implementation can
     *                         be constructed with
     */
    Applying applying(String behavior, List<DependencyStandin> standins);

    /** A behavior, in the environment one row gives it. */
    interface Applying {

        /**
         * Applies it to {@code arguments} and answers with what it answered.
         *
         * <p>The answer is of whatever classes this answerer applies, and is read by the one reading a
         * run has: by the name its class carries and the accessor every data has, neither of which is
         * a class identity. So an answer from another loader needs nothing done to it.
         *
         * @throws InvocationFailure       where the applied code came back with a failure. What that
         *                                 failure means for the row is the row's to say. What
         *                                 {@link Handed#neutral} throws is not one of these and must
         *                                 be let out as it stands
         * @throws ImplementationNotReached where the implementation could not be reached to apply
         */
        Object to(List<Handed> arguments);
    }
}
