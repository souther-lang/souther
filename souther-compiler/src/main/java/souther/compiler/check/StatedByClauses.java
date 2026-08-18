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
record StatedByClauses(AdmissibleValues<FactSubject> values, OrderedIntervals<FactSubject> ordered) {

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
                              Map<FactSubject, Type> byName, Symbols symbols) {
        Reading reading = readingOf(terms, at, byName, symbols);
        StatedByClauses out = top();
        for (Core clause : clauses) {
            out = out.meet(reading.read(clause, true));
        }
        return out;
    }

    /** The reading of one value's positions, made once and used over however many clauses reach it.
     *  Built per clause, this walk paid for a pair of readers at every clause of every value. */
    static Reading readingOf(Terms terms, Denotations at, Map<FactSubject, Type> byName,
                             Symbols symbols) {
        java.util.Set<FactSubject> adopted = new java.util.LinkedHashSet<>();
        return new Reading(AdmissibleReading.of(terms, at, byName, symbols, adopted),
                OrderedReading.of(terms, at, byName, symbols, adopted), adopted);
    }

    /**
     * What one clause says on its own.
     *
     * <p>The same reading as {@link #of}, run over one clause, so that a caller can tell which
     * clauses a reading took in rather than which positions it ended up short of. The two are
     * different questions and reading the second for the first is what let one clause's failure
     * spoil the account of every clause beside it: {@code value >= 1} leaves the reading of values
     * short at a position, and {@code value == 7} written beside it was taken in whole.
     */
    static StatedByClauses ofOne(Core clause, Terms terms, Denotations at,
                                 Map<FactSubject, Type> byName, Symbols symbols) {
        return readingOf(terms, at, byName, symbols).read(clause, true);
    }

    /**
     * Where the readings took {@code clause} in, said by them.
     *
     * <p>A reading of its own, so the set holds what this clause was adopted at and not what
     * everything before it was.
     */
    static java.util.Set<FactSubject> adoptedIn(Core clause, Terms terms, Denotations at,
                                                Map<FactSubject, Type> byName, Symbols symbols) {
        Reading reading = readingOf(terms, at, byName, symbols);
        reading.read(clause, true);
        return reading.adopted();
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

    StatedByClauses meet(StatedByClauses other) {
        return new StatedByClauses(values.meet(other.values), ordered.meet(other.ordered));
    }

    /**
     * The two readings of one clause tree, run together so that the connectives are the clause's,
     * and where they took a leaf in.
     *
     * <p>{@code adopted} is filled by the readings as they read, and is theirs to say. Read off
     * what a reading leaves a position instead, a clause it took in whole and narrowed nothing by
     * comes back unread: {@code value == 5 || value /= 5} is read at both leaves and joins to every
     * value there is. That is the same reconstruction {@code Predicates.Assumed} keeps a field of
     * its own to avoid, and the one this accounting was written against.
     */
    record Reading(AdmissibleReading values, OrderedReading ordered,
                   java.util.Set<FactSubject> adopted)
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
         * together.
         *
         * <p><b>Every alternative impossible is not one alternative impossible.</b> Where one of
         * them cannot be taken, the answer is the other and the first one's evidence goes with it —
         * nothing satisfies it, so what it said narrows nothing a value of this type is under, its
         * unread rules included. Where <em>all</em> of them cannot be taken, no one of them speaks
         * for the rest: taking the first to be found impossible out of the answer would settle the
         * proof by the order the operands were written in, and the same model written two ways would
         * be refused two ways.
         *
         * <p>Nor may they be met. A meet is a conjunction and the alternatives were never stated
         * together: {@code (a < "" && b == 0) || (a < "" && b == 1)} is impossible because of
         * {@code a}, and met it is a {@code b} bounded at 0 and at 1 — a contradiction neither
         * alternative contains, at a position the rules are fine with, and one the refusal would
         * then be written about.
         *
         * <p>So each side is taken as leaving nothing ({@link AdmissibleValues#leavingNothing},
         * {@link OrderedIntervals#leavingNothing}) and the languages are joined as they are for any
         * other choice. What each of them says the choice leaves empty is what <em>every</em>
         * alternative leaves empty, and where that is no position, the choice admits nothing with
         * none of them at fault. That is the rule {@link Emptiness.AcrossEveryCase} states for a
         * sum — what proves it has none is the whole list — arrived at here for the same reason.
         */
        @Override
        public StatedByClauses either(StatedByClauses one, StatedByClauses other) {
            if (one.holdsNothing() && other.holdsNothing()) {
                return new StatedByClauses(
                        values.either(one.values.leavingNothing(), other.values.leavingNothing()),
                        ordered.either(one.ordered.leavingNothing(),
                                other.ordered.leavingNothing()));
            }
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
