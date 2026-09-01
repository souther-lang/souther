package souther.compiler.observe;

import souther.compiler.diag.Region;

import java.time.Duration;
import java.util.List;

/**
 * What a module's written statements about its behaviors say, and where a reading of them stopped.
 *
 * <p>A {@code fake} row and an {@code example} row can both state what one behavior answers, and
 * they are two written statements about one thing. Reading them means building the values they
 * name, which is running what the compile generated; but what the reading came to is about the
 * module and not about whatever ran it, so it is said here rather than in the package that runs it.
 *
 * <p>Its own place for the reason the row outcomes have one. Something that asks whether two
 * statements agree has to be able to read the answer without compiling against the implementation
 * that produced it.
 */
public final class WrittenStatements {

    private WrittenStatements() {}

    /**
     * One written statement about what a behavior answers, and where it is written.
     *
     * <p>{@code answer} is rendered here rather than at the report, because reading it needs the
     * decoders and the module's classes and the report has neither.
     */
    public record Statement(Region region, String answer) {}

    /**
     * One input for which two written statements about a behavior answer differently.
     *
     * <p>Neither side is derived from the other: the recorded row says what the behavior will owe, the
     * stand-in says what it answers while some other behavior's row runs. Which is right is not
     * readable here — a model being migrated onto may run against a stand-in while the real answer is
     * still being harvested, and that is written the way a mistake is. So both are named and neither
     * is ranked.
     *
     * <p>Independent of which source is being reported: one disagreement is projected onto both of the
     * sources its two statements are written in.
     *
     * @param viaWith whether the stand-in is a {@code with} rather than a {@code fake} row — the
     *                report names the form the author wrote, so it has to be told which one it is
     */
    public record Disagreement(String behavior, Statement recorded, Statement standIn,
                               boolean viaWith) {}

    /**
     * A fake whose table did not finish being built within the budget, so what it states and what the
     * rows recorded for the behavior state were never compared.
     *
     * <p>Carries what it takes to report it. The stretch of source is taken here, where the text is,
     * the way a {@link Statement}'s is; the budget is the one the wait was actually held to, rather
     * than a second reading of the setting taken later, which a budget that stops being one number
     * for the whole compile would make wrong with nothing to say so.
     *
     * <p>The region and not a position with a width beside it. A target may be written through the
     * module that declares the behavior, and how far such a name reaches is not its canonical
     * length: a qualifier, the dots, and whatever the author put between them are all part of what
     * the marker covers, which is why {@link souther.compiler.ast.WrittenName} keeps the stretch
     * rather than deriving one.
     *
     * @param at where the fake names the behavior it stands in for, which is what the report marks
     */
    public record UnreadFake(String target, Region at, Unread why) {}

    /**
     * Why a written statement was not read.
     *
     * <p>Two things a report must not say in one voice. Spending the budget is an answer about the
     * statements, reached the same way on every host; not answering is an answer about the host, and
     * a model it is said of may be perfectly good. A single "it timed out" made a reader guess which,
     * and the guess was usually the wrong one for the model.
     */
    public sealed interface Unread {

        /** The reading spent the counted budget the policy allows. */
        record Overspent(FailurePhase which, long limit) implements Unread {}

        /** The stack ran out before the counted depth limit was reached. */
        record StackRanOut(int depthLimit) implements Unread {}

        /** The reading did not answer within the wait it was given. Not a budget in the sense
         *  {@link Overspent} names one: those are spent by the code that ran, and this is time the
         *  compiler spent without answering. A length, so that what unit a reader sees is decided
         *  where a report is written and not on the way here. */
        record DidNotAnswer(Duration within) implements Unread {}

        /** {@link Overspent} for whichever budget {@code which} names. */
        static Unread overspending(FailurePhase which, long limit) {
            return new Overspent(which, limit);
        }

        /**
         * Which of the three this is, as the middle of a message key.
         *
         * <p>Three messages rather than one with a reason substituted in, because the sentence is
         * mostly about what to do and that differs: a loop is bounded, a recursion is made
         * structural, and an evaluation that stopped answering is not the model's fault at all.
         *
         * <p>Callers spell out the whole key rather than build it from this, so that every key the
         * compiler names can be found by looking for it. What this saves them is the choosing.
         */
        default boolean isDepth() {
            return this instanceof Overspent(FailurePhase which, long _)
                    && which == FailurePhase.DEPTH_LIMIT;
        }

        default boolean isSteps() {
            return this instanceof Overspent(FailurePhase which, long _)
                    && which == FailurePhase.STEP_LIMIT;
        }

        default boolean isStack() {
            return this instanceof StackRanOut;
        }

        /** The limit, as written rather than as a number a locale groups: {@code 2,000} is not a
         * budget anyone set, and the settings that name these take the ungrouped form. */
        default String limitShown() {
            return switch (this) {
                case Overspent(FailurePhase _, long limit) -> Long.toString(limit);
                case StackRanOut(int depthLimit) -> Integer.toString(depthLimit);
                case DidNotAnswer(Duration within) -> WaitShown.of(within);
            };
        }
    }

    /**
     * What reading a module's written statements against each other came to.
     *
     * <p>Both lists, because a reading that did not finish and a reading that found nothing are
     * different answers and an empty list of disagreements is what the second one looks like. Which
     * of the two a compile got can otherwise turn on machine load, between a build and the next
     * keystroke in the editor.
     */
    public record Readings(List<Disagreement> disagreements, List<UnreadFake> unread) {

        public static final Readings NONE = new Readings(List.of(), List.of());

        public Readings {
            disagreements = List.copyOf(disagreements);
            unread = List.copyOf(unread);
        }
    }
}
