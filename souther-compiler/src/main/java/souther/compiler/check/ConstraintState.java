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
record ConstraintState(NumericDomain<FactSubject> numbers, PredicateFacts facts,
                       AdmissibleValues<FactSubject> values, OrderedIntervals<FactSubject> ordered,
                       boolean shown) {

    /** Nothing taken in, so nothing ruled out. */
    static ConstraintState top() {
        return new ConstraintState(NumericDomain.top(), PredicateFacts.none(),
                AdmissibleValues.top(), OrderedIntervals.top(), false);
    }

    /**
     * Whether nothing satisfies what has been taken in.
     *
     * <p>Every domain, because each of them can hold the whole state's contradiction on its own: what
     * one of them cannot express it leaves alone, so a contradiction found anywhere is a
     * contradiction, and one found nowhere is only what these readings were able to show.
     *
     * <p>And {@code shown}, which is a caller having shown it by an argument none of the domains
     * makes: a condition no case of what it is written over satisfies is one nothing enters, and
     * what says so is a reading of the cases rather than anything an interval or a predicate holds.
     * It is another piece of evidence for the one answer and not a second answer — a state that
     * carried its own reachability beside the domains would be two records to keep in step, and the
     * first domain added without touching the second would put them out of agreement.
     */
    boolean isBottom() {
        return shown || numbers.isBottom() || facts.isBottom() || values.isBottom()
                || ordered.isBottom();
    }

    /**
     * This, with nothing satisfying it, shown by an argument outside the domains.
     *
     * <p>Written here rather than as a contradiction lodged in one of them. Said as {@code 1 <= 0}
     * in the numbers, which is how it read before, the claim came out as an arithmetic one: a reader
     * asking why a state holds nothing was told the rules about numbers conflict, and a reader
     * asking whether a path is reached was pulled back to {@code numbers.isBottom()} — which is the
     * reading this question came apart along.
     */
    ConstraintState shownToHoldNothing() {
        return shown ? this : new ConstraintState(numbers, facts, values, ordered, true);
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
    Optional<Emptiness> holdsNothing(SequencedMap<FactSubject, String> positions) {
        Emptiness why = isBottom() ? new Emptiness.ConflictingRules() : null;
        // A position whose ends cross, which is nearer than the general form: it says not only that
        // the rules contradict but where they leave nothing.
        //
        // Only where there is a position to name. A state can hold nothing without any one position
        // being what holds nothing — a choice every alternative of which is impossible is one, and
        // the alternatives may fail at different positions — and the particular proof is particular
        // by naming a place. Written without one, the sentence read off it would name whatever place
        // the reader happened to be at, which is the declaration's own value.
        Set<FactSubject> empty = ordered.holdingNothing();
        for (Map.Entry<FactSubject, String> each : positions.entrySet()) {
            if (empty.contains(each.getKey())) {
                why = Emptiness.preferred(why, new Emptiness.AtAField(each.getValue(),
                        new Emptiness.EmptyOrderedInterval()));
                break;
            }
        }
        return Optional.ofNullable(why);
    }

    /** This, with {@code f rel 0} taken as holding. */
    ConstraintState taking(LinearForm<FactSubject> f, Rel rel, Map<FactSubject, Granularity> kinds) {
        return new ConstraintState(numbers.assume(f, rel, kinds), facts, values, ordered, shown);
    }

    /** This, with the predicate {@code key} taken as holding, or as failing. */
    ConstraintState taking(FactSubject key, boolean positive) {
        return new ConstraintState(numbers, facts.assume(key, positive), values, ordered, shown);
    }

    /**
     * This, with the clauses of one declaration read into its values.
     *
     * <p><b>Not two readings combined.</b> What stands here is what nothing read leaves until this
     * is called, and it is called once — so the answer is the same either way today. Written
     * against that rather than against what the state happens to hold, because a reading is a union
     * of alternatives and a conjunction of two of them is the union of the pairs: two readings met
     * here would be two declarations' alternatives multiplied outside the budget either of them was
     * admitted under, and the budget is what makes the reading of one declaration bounded at all.
     *
     * <p>Met with what nothing read leaves rather than assigned, which is not the same answer. A
     * reading a choice reached across two positions promises nothing about whole values, and a
     * conjunction with one of those promises nothing anywhere — so the meet gives up a lower bound
     * that an assignment would keep. That is {@link AdmissibleValues#guaranteedAt}'s rule about
     * conjunctions firing on a side that read nothing, and lifting it is about which rules went
     * unread rather than about how the alternatives are held.
     */
    ConstraintState takingValuesRead(AdmissibleValues<FactSubject> read) {
        // Said once, and what stands here until it is said is what nothing read leaves. Saying it
        // twice would keep the second reading and drop the first without a word, which is the one
        // way this can be got wrong now that it cannot combine two of them. An assertion because a
        // throw would be caught by the fail-open around the reading and leave it silently dropped.
        assert values.equals(AdmissibleValues.<FactSubject>top())
                : "the values of a state are read once, and these were read over " + values;
        return new ConstraintState(numbers, facts, AdmissibleValues.<FactSubject>top().meet(read),
                ordered, shown);
    }

    /** This, with {@code bounded} taken as holding of the positions it bounds. */
    ConstraintState taking(OrderedIntervals<FactSubject> bounded) {
        return new ConstraintState(numbers, facts, values, ordered.meet(bounded), shown);
    }

    /**
     * The same rules with one atom settled at a value.
     *
     * <p>The one place a settling is stated, so that a reading made with one and a reading settled
     * after it was made say the same thing. Written twice, the second would be free to state it
     * under a different spacing and answer a position differently while both stayed sound.
     */
    static ConstraintState settling(ConstraintState state, FactSubject atom,
                                    souther.compiler.numeric.Count at,
                                    souther.compiler.numeric.Granularity spacing) {
        return state.taking(
                NumericDomain.LinearForm.<FactSubject>atom(atom)
                        .minus(NumericDomain.LinearForm.<FactSubject>constant(at.at())),
                NumericDomain.Rel.EQ, java.util.Map.of(atom, spacing));
    }
}
