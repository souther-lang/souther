package souther.compiler.check;

import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.values.AdmissibleValues;

import java.util.Map;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;

/**
 * What the rules say, in each of the languages this reading has for saying it.
 *
 * <p>Several domains and one state. A clause relates numbers, or bounds one position on its order,
 * or names the values a position may take, or settles a predicate that relates to nothing, and each
 * of those is written where something can be reasoned about it — but what a caller asks of them
 * together is one question, and it is whether anything at all satisfies what has been taken in. That
 * is {@link #isBottom}, and it is asked of the whole because a reader that asked one domain would
 * answer that a value exists whenever the domain it happened to ask had nothing to say.
 * {@code value == "A"} beside {@code value /= "A"} reaches no number and leaves the predicates
 * contradictory, and a count taken from the numbers alone called that type inhabited.
 *
 * <p><b>What each domain is for, and that they overlap on purpose.</b>
 *
 * <pre>
 *     numbers    affine relations between positions a model adds and subtracts
 *     ordered    one position bounded against a written value, on whatever order it has
 *     values     which values a position may take, as a finite set or a finite exclusion
 *     facts      a predicate about a position, settled one way or the other
 * </pre>
 *
 * <p>Two of them answering for one clause is not two meanings of it. {@code value > 5} is an affine
 * relation and a bound on an order, and each domain abstracts it in a way that is safe on its own:
 * the numbers can relate it to a sibling position and the ordering cannot, the ordering holds it
 * over a date and the numbers cannot. Where both hold it, both are right, and neither is the other's
 * copy. What must not happen is a rule reaching none of them and being read as a rule that said
 * nothing, which is what an exception list — this domain covers the positions that one does not —
 * arranges the first time a type falls between the two.
 *
 * <p>The parts are readable, and only in one direction. A reader wanting the numbers may have them —
 * an interval is what a bound is read off, and nothing else answers that — but a reader asking
 * whether a value exists asks here and never assembles the answer out of the parts. A domain added
 * later is a component of this and an arm of {@link #isBottom}, and every such reader has it without
 * being touched.
 *
 * <p>Two questions are asked here and they are one answer. Whether any value of a declaration
 * exists, and whether a path a construction stands on is reached, are both whether anything at all
 * satisfies what has been taken in — so both are {@link #isBottom}, under the name each context
 * reads it by ({@link FieldDomains#infeasible}, {@link Known#reachesNothing}). They were once two
 * readers of two domains, and each of them answered that there was something wherever the domain it
 * happened to ask had nothing to say.
 */
record ConstraintState(NumericDomain<Term> numbers, PredicateFacts facts,
                       AdmissibleValues<Term> values, OrderedIntervals<Term> ordered) {

    /** Nothing taken in, so nothing ruled out. */
    static ConstraintState top() {
        return new ConstraintState(NumericDomain.top(), PredicateFacts.none(),
                AdmissibleValues.top(), OrderedIntervals.top());
    }

    /**
     * Whether nothing satisfies what has been taken in.
     *
     * <p>Every domain, because each of them can hold the whole state's contradiction on its own: what
     * one of them cannot express it leaves alone, so a contradiction found anywhere is a
     * contradiction, and one found nowhere is only what these readings were able to show.
     */
    boolean isBottom() {
        return numbers.isBottom() || facts.isBottom() || values.isBottom() || ordered.isBottom();
    }

    /**
     * Why nothing satisfies what has been taken in, or empty where something may.
     *
     * <p>Asked of the state, as {@link #isBottom} is, and for the same reason: which domain holds
     * the contradiction is not something a caller can be left to work out by asking them one at a
     * time. Where more than one does, the more particular proof is written
     * ({@link Emptiness#preferred}) — a state whose answer turned on which domain a reader happened
     * to ask first would refuse one declaration two ways.
     *
     * @param positions where each position of the value sits, <em>in the order the value declares
     *                  them</em>. A proof that names a place needs one to name, and the order is
     *                  what settles it where the rules leave several positions empty at once: read
     *                  off the state's own map, the place named would be the one whose clause was
     *                  read first, and moving a clause would move the refusal
     */
    Optional<Emptiness> holdsNothing(SequencedMap<Term, String> positions) {
        Emptiness why = isBottom() ? new Emptiness.ConflictingRules() : null;
        // A position whose ends cross, which is nearer than the general form: it says not only that
        // the rules contradict but where they leave nothing.
        //
        // Only where there is a position to name. A state can hold nothing without any one position
        // being what holds nothing — a choice every alternative of which is impossible is one, and
        // the alternatives may fail at different positions — and the particular proof is particular
        // by naming a place. Written without one, the sentence read off it would name whatever place
        // the reader happened to be at, which is the declaration's own value.
        Set<Term> empty = ordered.holdingNothing();
        for (Map.Entry<Term, String> each : positions.entrySet()) {
            if (empty.contains(each.getKey())) {
                why = Emptiness.preferred(why, new Emptiness.AtAField(each.getValue(),
                        new Emptiness.EmptyOrderedInterval()));
                break;
            }
        }
        return Optional.ofNullable(why);
    }

    /** This, with {@code f rel 0} taken as holding. */
    ConstraintState taking(LinearForm<Term> f, Rel rel, Map<Term, Granularity> kinds) {
        return new ConstraintState(numbers.assume(f, rel, kinds), facts, values, ordered);
    }

    /** This, with the predicate {@code key} taken as holding, or as failing. */
    ConstraintState taking(Term key, boolean positive) {
        return new ConstraintState(numbers, facts.assume(key, positive), values, ordered);
    }

    /** This, with {@code admitted} taken as holding of the positions it speaks about. */
    ConstraintState taking(AdmissibleValues<Term> admitted) {
        return new ConstraintState(numbers, facts, values.meet(admitted), ordered);
    }

    /** This, with {@code bounded} taken as holding of the positions it bounds. */
    ConstraintState taking(OrderedIntervals<Term> bounded) {
        return new ConstraintState(numbers, facts, values, ordered.meet(bounded));
    }
}
