package souther.compiler.check;

/**
 * One question a rule raises, and what it is about.
 *
 * <p>The subject is here because the obligations do not share one. What values may stand somewhere
 * is about a position; where a line falls is about a number taken of one, and a {@code String}
 * bounded on its length raises both — the values are the string's and the line is on the length. A
 * report holding one subject for a rule names the wrong thing for at least one of its questions, and
 * that is how a line about a length came to be printed as a fact about which strings may stand
 * there.
 *
 * <p>Which subject each obligation has follows from the obligation and is settled where the question
 * is raised, so no reader downstream chooses between a path and a term.
 *
 * @param obligation what has to be answered
 * @param subject    what it is about
 */
public record Owed(CoverageObligation obligation, Subject subject) {

    public Owed {
        if (obligation == null || subject == null) {
            throw new IllegalArgumentException("a question with no subject is not one");
        }
    }

    /**
     * What a question is about, as the reading that raised it names it.
     *
     * <p>A position of the value, a number taken of one, or the place two numbers hold one count.
     * The first two are the same pair the reading of ends already carries, so that a question and
     * the end that answers it are about the same thing by construction rather than by two spellings
     * agreeing.
     *
     * <p>The second is not a position at all, and it is not a place written out either.
     * {@code r.a <= r.b + 1} draws a line where the two sides meet; it is on neither of them, and
     * filing it under either would name a place that rule never stopped. Nor is it spelled: writing
     * the place out needs both sides in a vocabulary this compiler has, and it does not have one for
     * {@code r.b + 1} — so a spelled subject is how far a pretty-printer got rather than what the
     * question is about, and {@code r.b + 1} and {@code r.b + 2} come out as one place. The
     * comparison that drew the line is what the question is about, and that this compiler can always
     * name exactly.
     */
    public sealed interface Subject {

        /**
         * A position of the value, or a number taken of one.
         *
         * @param path     where in the value it sits, {@link FieldDomains#THE_VALUE} for the value
         *                 itself
         * @param measured whether it is a count taken of the position rather than the position's
         *                 own value
         */
        record OfAPosition(String path, boolean measured) implements Subject {

            public OfAPosition {
                if (path == null) {
                    throw new IllegalArgumentException("a subject sits somewhere in the value");
                }
            }

            @Override
            public String toString() {
                // The value itself is at no path, which reads as nothing at all where it is printed.
                String where = path.isEmpty() ? "the value" : path;
                return measured ? "count of " + where : where;
            }
        }

        /**
         * The place a comparison of two moving things draws, named by that comparison.
         *
         * <p>Where the two sides hold one count, which is on neither of them. Named rather than
         * written out, so that what the question is about does not move when this compiler learns to
         * print one more shape of expression — and so that two rules drawing two lines are two
         * subjects however little of either can be spelled.
         *
         * <p>Beside {@link RuleCitation} and not a copy of it. A citation is how a reader finds the
         * rule, which for a {@code guard} is the fork it is written in and for an {@code ensures} is
         * the clause's name; this is which comparison inside it drew the line. They coincide often
         * and mean different things, and a clause stating two comparisons has one citation and two
         * of these.
         */
        record OfComparison(souther.compiler.diag.Citation at) implements Subject {

            public OfComparison {
                if (at == null) {
                    throw new IllegalArgumentException("a comparison is somewhere");
                }
            }

            @Override
            public String toString() {
                return "where the relation changes";
            }
        }

        /** The position's own value. */
        static Subject at(String path) {
            return new OfAPosition(path, false);
        }

        /** Whether this is a count taken of a position rather than a position's own value. */
        default boolean measured() {
            return this instanceof OfAPosition it && it.measured();
        }
    }
}
