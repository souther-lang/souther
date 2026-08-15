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
 * <p>Asked per behavior, and what it answers with says of itself what applied the row
 * ({@link Applying#applied}). A module declares behaviors with a body and behaviors without one, and
 * only the second can have an implementation supplied for it — so which of them applies is settled
 * one behavior at a time, and an answerer that resolves between them has an answer for each.
 *
 * <p>Whether anything applies a behavior at all is answered here too ({@link #of}), and answered
 * rather than raised. Having nothing to apply is not something an answerer failed to do — it is what
 * a run over a behavior nothing implements is, and the row it belongs to is right and complete as far
 * as it goes. Where it is decided is what makes it this one's: a run's rows are held to what that run
 * was given, and a reader deciding it from how the behavior is written would go on answering from the
 * declaration once something other than a compile can supply an implementation.
 *
 * <p>Nothing here reports anything. A diagnostic is a statement about a row and this is not about a
 * row, so what an answerer cannot do it raises and the row says what that means. Three things can go
 * wrong and they are three because what they say is not the same: {@link StandinNotBuilt} is a
 * stand-in that could not be made, {@link ImplementationNotReached} is the implementation not being
 * reachable at all, and {@link InvocationFailure} is the applied code coming back with a failure. Only
 * the last is about the model. None of them is having nothing to apply, which is why that is a value.
 */
public interface Answerer {

    /**
     * What this answerer has for {@code behavior}.
     *
     * <p>Asked before a row states anything and before its stand-ins are gathered, because whether
     * anything applies a behavior does not depend on either. A row that nothing applies is still held
     * to everything it can be held to without being run, and asking this first is what lets it be: an
     * answer of {@link Answer.Nothing} is reached with the row's fixtures already built and validated.
     *
     * <p>Fixed for the run. Two rows about one behavior get the same answer, so nothing about what a
     * row means depends on when it was asked.
     */
    Answer of(String behavior);

    /**
     * Whether anything applies a behavior, and if something does, what.
     *
     * <p>A sum and not a nullable one: a reader that has to tell the two apart states it as a
     * {@code switch}, so an answer it did not consider is a compile error rather than a branch that
     * silently takes the other way. That is what this is for — the arms may come to say more than they
     * do here (an implementation supplied from outside a compile is #695), and a reader written
     * against {@code instanceof} would keep working while meaning something else.
     */
    sealed interface Answer {

        /**
         * Something here applies the behavior.
         *
         * <p>What it is is not said. Which of several things applied a row is recorded from the
         * application itself ({@link Applying#applied}), so a reader of this needs nothing from it
         * but that it can be applied.
         */
        @FunctionalInterface
        non-sealed interface Something extends Answer {

            /**
             * It, with {@code standins} answering for what the behavior depends on.
             *
             * <p>Separate from applying it because the two are separate things to have got as far as.
             * Making a stand-in into an instance is building the environment the behavior runs in, and
             * a row that could not get an environment never entered the behavior — which is what its
             * outcome has to be able to say. So this is where a stand-in that could not be made is
             * raised, and {@link Applying#to} is where the behavior running is.
             *
             * @throws StandinNotBuilt where a stand-in could not be made into something the
             *                         implementation can be constructed with
             */
            Applying applying(List<DependencyStandin> standins);
        }

        /**
         * Nothing this run was given applies the behavior.
         *
         * <p>Not a failure and not an absence of an answer. The row is recorded rather than run: what
         * it holds the behavior to is on the record from the day it is written, and it begins being
         * run by itself the moment something applies that behavior.
         */
        record Nothing() implements Answer {}
    }

    /** A behavior, in the environment one row gives it. */
    interface Applying {

        /**
         * What a row's outcome records as having applied the behavior.
         *
         * <p>Here and not on the answerer, because which of several things applies a behavior is
         * settled per behavior and not per compile. An answerer that resolves between what a compile
         * generated and an implementation supplied from outside has both in one evaluation — a module
         * declares behaviors of both kinds — and asked once for the whole of itself it could only
         * name one of them.
         *
         * <p>Read where the row entered the behavior and nowhere else. A row that could not be given
         * an environment never reached this, and one that never entered says nothing applied it.
         */
        Applied applied();

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
