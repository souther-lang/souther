package souther.compiler.check;

import souther.compiler.core.Core;

/**
 * Which authored part of which rule a reading was asked to leave out.
 *
 * <p>Beside {@link RulesLeftOut} and not a finer setting of it. That one leaves out every rule some
 * declaration wrote, and what it is asked with is a declaration; this leaves out one conjunct of one
 * rule, and what it is asked with is that rule together with the node the conjunct was written as.
 * The two are different questions about different things, and a reading told to leave out "a part"
 * with no rule beside it would leave out whatever else happened to be written the same way.
 *
 * <p>What such a reading is for is not here. A reader comparing what a value's rules leave with and
 * without one conjunct is asking what that conjunct was holding; nothing about the comparison
 * belongs to the reading that answers it.
 */
sealed interface PartsLeftOut {

    /** Every part of every rule is read. */
    PartsLeftOut NONE = new Nothing();

    /** Whether this reading was asked to leave {@code part} of {@code rule} out. */
    boolean excludes(RuleRef.Invariant rule, Core part);

    /** What the parts a reading takes in come to for one rule. */
    Predicates.PartsToRead of(RuleRef.Invariant rule);

    /** Nothing is left out. */
    record Nothing() implements PartsLeftOut {

        @Override
        public boolean excludes(RuleRef.Invariant rule, Core part) {
            return false;
        }

        @Override
        public Predicates.PartsToRead of(RuleRef.Invariant rule) {
            return Predicates.PartsToRead.ALL;
        }
    }

    /**
     * One conjunct of one rule is left out.
     *
     * <p>The node and not a number. Which conjunct of a clause a part is is counted by more than one
     * reading, and they count alike only where a clause is read positively — so what is named here
     * is the node itself, which is the identity a part already has everywhere it is recorded. Held
     * as a value: a reading asked to leave a part out types the clause again, and what it walks is
     * a node equal to the one named here rather than the same one.
     */
    record OnePart(RuleRef.Invariant rule, Core part) implements PartsLeftOut {

        public OnePart {
            if (rule == null || part == null) {
                throw new IllegalArgumentException("a part left out is some rule's own");
            }
        }

        @Override
        public boolean excludes(RuleRef.Invariant of, Core each) {
            return rule.equals(of) && part.equals(each);
        }

        @Override
        public Predicates.PartsToRead of(RuleRef.Invariant of) {
            return rule.equals(of) ? Predicates.PartsToRead.without(part)
                    : Predicates.PartsToRead.ALL;
        }
    }

    /** Every part but {@code part} of {@code rule}. */
    static PartsLeftOut without(RuleRef.Invariant rule, Core part) {
        return new OnePart(rule, part);
    }
}
