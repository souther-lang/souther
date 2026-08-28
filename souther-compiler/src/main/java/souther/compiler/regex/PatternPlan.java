package souther.compiler.regex;

/**
 * Everything one answer needs of the patterns that reach it, compiled at once or not at all.
 *
 * <p>The whole of a question and never one pattern of it. What a pattern costs to answer about is
 * not a property of the pattern: two that are small on their own have a meet the size of their
 * product, and a bound put on each of them says nothing about the two together. Admitted one at a
 * time, a language enters an answer and the work that turns out to be unaffordable happens later —
 * where the only thing left to do is fail in the middle of an operation that is supposed to be
 * total.
 *
 * <p>So this is where the resource question lives, and it is asked once. What comes back is either
 * a {@link Language} every operation on which is within the envelope, or nothing — and the caller
 * has an answer it can act on before anything has been built into evidence.
 *
 * <p><b>Not a promise about every language.</b> What is admitted is this plan: the patterns it
 * names, met and joined the way it says. A language of this plan met with one from another answer is
 * work nobody has counted, which is why a plan is per answer and an answer holds the one language
 * that came out of it.
 */
public final class PatternPlan {

    /**
     * How much a plan is allowed.
     *
     * <p>States, because that is what everything here costs: a pattern is its states, a meet is the
     * product of two, and what a walk over any of them takes is bounded by them. Counted over the
     * whole of the plan and not per pattern — a plan is admitted as a whole or not at all, so what
     * it is charged is everything it builds.
     *
     * @param mostStates the largest machine a step of the plan may make
     * @param mostBuilt  how many states the plan may make in all, the intermediate ones counted.
     *                   Beside the first because a plan of many small meets is affordable at each
     *                   step and not as a whole
     */
    public record Budget(int mostStates, int mostBuilt) {

        public Budget {
            if (mostStates <= 0 || mostBuilt <= 0) {
                throw new IllegalArgumentException("a budget allows something");
            }
        }

        /**
         * What the values one position finally admits are allowed to cost.
         *
         * <p>The whole of that and not one rule of it. Every rule about a position pays into the
         * same machine — two patterns of one clause meet, and so do two written in separate rules of
         * one declaration — so an allowance per rule would be one nobody could hold the product to.
         *
         * <p>Large enough for the formats a model writes — the longest of them is a couple of dozen
         * characters of classes and counts, which is a few hundred states — and small enough that a
         * pattern nobody meant to write is refused rather than waited for. What it is not is a
         * measurement of anything: it is the size past which this compiler would rather say it did
         * not answer.
         */
        public static final Budget OF_ADMITTED_VALUES = new Budget(50_000, 200_000);
    }

    /** What one step of a plan does. */
    private sealed interface Step {

        /** A pattern, as the strings it accepts. */
        record Of(PatternSyntax syntax) implements Step {}

        /** The strings two steps both hold. */
        record Both(Step one, Step other) implements Step {}

        /** The strings either of them holds. */
        record Either(Step one, Step other) implements Step {}

        /** The strings one holds and the other does not. */
        record Less(Step one, Step other) implements Step {}
    }

    private final Step step;

    private PatternPlan(Step step) {
        this.step = step;
    }

    /** The plan that is one pattern. */
    public static PatternPlan of(PatternSyntax syntax) {
        if (syntax == null) {
            throw new IllegalArgumentException("a plan is of some pattern");
        }
        return new PatternPlan(new Step.Of(syntax));
    }

    /** The plan for what both hold. */
    public PatternPlan and(PatternPlan other) {
        return new PatternPlan(new Step.Both(step, other.step));
    }

    /** The plan for what either holds. */
    public PatternPlan or(PatternPlan other) {
        return new PatternPlan(new Step.Either(step, other.step));
    }

    /** The plan for what this holds and that does not. */
    public PatternPlan less(PatternPlan other) {
        return new PatternPlan(new Step.Less(step, other.step));
    }

    /**
     * The language this plan comes to, or null where building it would cost more than
     * {@code budget} allows.
     *
     * <p>Null and never a smaller language. What a plan says is which strings the answer is about,
     * and a language of fewer states is a different set — handed one, a reader would be measuring a
     * model against something this compiler made up because the real answer was expensive.
     *
     * <p>Everything is built here, the intermediate machines among them. A caller holding what comes
     * back may ask it anything, because the asking is what has already been paid for.
     */
    public Language compile(Budget budget) {
        try {
            int[] left = new int[] {budget.mostBuilt()};
            // Made canonical here and not by whoever holds it. A language is the one machine that
            // accepts its strings, and turning a machine into that one is the largest thing this
            // does — left to the reader, it would happen inside whichever question was asked first,
            // where there is no allowance and nobody counting.
            return new Language(charged(
                    built(step, budget, left).canonical(budget.mostStates()), budget, left));
        } catch (TooMuch _) {
            return null;
        }
    }

    /**
     * One step, with what is left of the plan's allowance.
     *
     * <p>No {@code default}: a step added and not built stops the compile rather than arriving here
     * as whichever operation is nearest.
     */
    private static Automaton built(Step step, Budget budget, int[] left) {
        return switch (step) {
            case Step.Of it -> charged(Automaton.of(it.syntax(), budget.mostStates()), budget, left);
            case Step.Both it -> charged(built(it.one(), budget, left)
                    .and(built(it.other(), budget, left)), budget, left);
            case Step.Either it -> charged(built(it.one(), budget, left)
                    .or(built(it.other(), budget, left)), budget, left);
            // What one holds and the other does not, which is the one step that has to make a
            // machine deterministic. Charged as everything else is: the complement is a machine and
            // its states are what it costs.
            case Step.Less it -> {
                Automaton mine = built(it.one(), budget, left);
                Automaton theirs = charged(built(it.other(), budget, left).not(), budget, left);
                yield charged(mine.and(theirs), budget, left);
            }
        };
    }

    /** The machine, once what it cost has been taken off what the plan had left. */
    private static Automaton charged(Automaton made, Budget budget, int[] left) {
        if (made == null || made.size() > budget.mostStates()) {
            throw new TooMuch();
        }
        left[0] -= made.size();
        if (left[0] < 0) {
            throw new TooMuch();
        }
        return made;
    }

    /** More than the plan was allowed, carried to the one place that answers for it. */
    private static final class TooMuch extends RuntimeException {

        private static final long serialVersionUID = 1L;

        TooMuch() {
            super(null, null, false, false);
        }
    }
}
