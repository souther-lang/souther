package souther.compiler.inputs;

import java.util.List;

/**
 * The distinctions at a position that rows are owed, which is what every measure counts against.
 *
 * <p>Derived from {@link ReadingResult} and never beside it. The reading says what the rules came
 * to; this says what is done about it, and the one conversion between them ({@link #of}) is where
 * every conservative choice is written down. Made at each reader instead, the same fallback was
 * inside the producer with nothing to say it had been applied — a position whose rules refuse every
 * value came back looking exactly like one whose rules refuse none.
 */
public sealed interface ObligationDomain {

    /** The distinctions rows are owed. */
    List<Case> cases();

    /** What the rules left, taken as it stands. */
    record Exact(List<Case> cases) implements ObligationDomain {

        public Exact {
            cases = List.copyOf(cases);
        }
    }

    /**
     * More than the rules left, because what they left could not be acted on.
     *
     * <p>A widening this compiler chose, named as one. Which is the difference that matters to a
     * reader: the cases here are not what the model states about the position, so nothing may be
     * concluded from one of them being present — a body declaring such a case cannot arrive is not
     * refuted by a case that is only here because the reading was set aside.
     */
    record Conservative(List<Case> cases, Reason why) implements ObligationDomain {

        public Conservative {
            cases = List.copyOf(cases);
            if (why == null) {
                throw new IllegalArgumentException(
                        "a widening with no reason is what the rules left");
            }
        }
    }

    /** Why the reading was set aside. */
    enum Reason {

        /**
         * The rules leave the position no value at all.
         *
         * <p>Which is a declaration nothing can construct, refused where it is written (E1013) and
         * a rule this compiler does not yet reach in every domain (issue #780). Read as an empty
         * partition it comes back as a position the model divides no way — the sentence the reading
         * protocol exists to stop — so the declared distinctions are handed back until the
         * declaration itself is refused everywhere it should be.
         */
        EMPTY_DOMAIN_POLICY_PENDING
    }

    /**
     * What rows are owed at a position, from what the reading of it came to.
     *
     * <p>The one place the two are related. {@code declared} is what the position's declarations
     * state before any rule was crossed with them, and it is handed back exactly where the crossing
     * left nothing to count — a position that states no distinctions at all is not that, and stays
     * the empty answer it read as.
     */
    static ObligationDomain of(ReadingResult reading, List<Case> declared) {
        if (!reading.kept().isEmpty() || declared.isEmpty()) {
            return new Exact(reading.kept());
        }
        return new Conservative(declared, Reason.EMPTY_DOMAIN_POLICY_PENDING);
    }
}
