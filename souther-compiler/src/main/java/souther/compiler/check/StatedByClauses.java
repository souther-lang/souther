package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.types.Type;
import souther.compiler.values.AdmissibleValues;

import java.util.List;
import java.util.Map;

/**
 * What the clauses of one value say, in each of the languages a clause is read in.
 *
 * <p>Two languages and one reading. Which values a position may take is a set, and where a position
 * stops is a range, and neither says what the other says — an ordering names no finite set, and a
 * set of values has no word for what lies between two of them. So a clause reaches whichever of them
 * has a word for it, and some clauses reach both.
 *
 * <p><b>The connectives are over this and not over either of them.</b> A choice between two
 * alternatives is a choice between two readings of the whole value, so an alternative that cannot be
 * taken is dropped by asking the whole of what is known about it ({@link #holdsNothing}). Applied
 * inside each language on its own, the drop happened only where the language doing the joining was
 * also the one that could show the branch impossible: {@code s < "" || (b == true && b == false)}
 * has a branch no order admits beside a branch no set of values admits, and each language, joining
 * alone, found nothing wrong with the branch the other one had refused. The same shape appears
 * inside one language across two positions, since a join keeps only what both sides spoke about.
 *
 * <p><b>Two of the four domains of {@link ConstraintState} are not here, and it is not an
 * oversight.</b> The interval algebra and the predicates are what a construction owes
 * ({@link Predicates}), which is a different question about the same clause: an alternative owes a
 * construction nothing a guard could discharge, so neither of them ever reads a branch of a choice.
 * A branch impossible only by an arithmetic relation between two positions is one nothing here can
 * drop, and giving those two a reading of alternatives is its own change with its own reason.
 */
record StatedByClauses(AdmissibleValues<Term> values, OrderedIntervals<Term> ordered) {

    /** Nothing read, so nothing ruled out. */
    static StatedByClauses top() {
        return new StatedByClauses(AdmissibleValues.top(), OrderedIntervals.top());
    }

    /**
     * What {@code clauses} leave, all of them holding at once.
     *
     * @param byName the type at each position, keyed by what that position is called
     */
    static StatedByClauses of(List<Core> clauses, Terms terms, Denotations at,
                              Map<Term, Type> byName, Symbols symbols) {
        Reading reading = new Reading(AdmissibleReading.of(terms, at, byName, symbols),
                OrderedReading.of(terms, at, byName, symbols));
        StatedByClauses out = top();
        for (Core clause : clauses) {
            out = out.meet(reading.read(clause, true));
        }
        return out;
    }

    /**
     * Whether nothing satisfies what has been read.
     *
     * <p>Either language, because each can hold the whole answer on its own: what one of them cannot
     * express it leaves alone. This is the question a choice is settled by, which is why it is here
     * and not on the two of them separately.
     */
    boolean holdsNothing() {
        return values.isBottom() || ordered.isBottom();
    }

    private StatedByClauses meet(StatedByClauses other) {
        return new StatedByClauses(values.meet(other.values), ordered.meet(other.ordered));
    }

    /** The two readings of one clause tree, run together so that the connectives are the clause's. */
    private record Reading(AdmissibleReading values, OrderedReading ordered)
            implements ClauseReading<StatedByClauses> {

        @Override
        public StatedByClauses nothingSaid() {
            return top();
        }

        @Override
        public StatedByClauses leaf(Core e, boolean positive) {
            return new StatedByClauses(values.leaf(e, positive), ordered.leaf(e, positive));
        }

        @Override
        public StatedByClauses both(StatedByClauses one, StatedByClauses other) {
            return one.meet(other);
        }

        /**
         * Either alternative holding, an alternative that admits nothing being one nobody can take.
         *
         * <p>Asked of the pair and not of each language, which is the whole point of reading them
         * together. Dropping a branch takes its unread rules with it, and rightly: no value
         * satisfies that branch, so what could not be read inside it narrows nothing that a value
         * of this type is under.
         */
        @Override
        public StatedByClauses either(StatedByClauses one, StatedByClauses other) {
            if (one.holdsNothing()) {
                return other;
            }
            if (other.holdsNothing()) {
                return one;
            }
            return new StatedByClauses(values.either(one.values, other.values),
                    ordered.either(one.ordered, other.ordered));
        }
    }
}
