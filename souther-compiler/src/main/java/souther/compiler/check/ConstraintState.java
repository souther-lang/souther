package souther.compiler.check;

import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.values.AdmissibleValues;
import souther.compiler.values.ConjoinedAdmissibleValues;

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
public record ConstraintState<A>(NumericDomain<A> numbers, PredicateFacts<A> facts,
                                 ConjoinedAdmissibleValues<A> values, OrderedIntervals<A> ordered,
                                 boolean shown) {

    /** Nothing taken in, so nothing ruled out. */
    public static <A> ConstraintState<A> top() {
        return new ConstraintState<>(NumericDomain.top(), PredicateFacts.none(),
                ConjoinedAdmissibleValues.top(), OrderedIntervals.top(), false);
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
    public boolean isBottom() {
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
    ConstraintState<A> shownToHoldNothing() {
        return shown ? this : new ConstraintState<>(numbers, facts, values, ordered, true);
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
    public Optional<Emptiness> holdsNothing(SequencedMap<A, String> positions) {
        Emptiness why = isBottom() ? new Emptiness.ConflictingRules() : null;
        // A position whose ends cross, which is nearer than the general form: it says not only that
        // the rules contradict but where they leave nothing.
        //
        // Only where there is a position to name. A state can hold nothing without any one position
        // being what holds nothing — a choice every alternative of which is impossible is one, and
        // the alternatives may fail at different positions — and the particular proof is particular
        // by naming a place. Written without one, the sentence read off it would name whatever place
        // the reader happened to be at, which is the declaration's own value.
        Set<A> empty = ordered.holdingNothing();
        for (Map.Entry<A, String> each : positions.entrySet()) {
            if (empty.contains(each.getKey())) {
                why = Emptiness.preferred(why, new Emptiness.AtAField(each.getValue(),
                        new Emptiness.EmptyOrderedInterval()));
                break;
            }
        }
        return Optional.ofNullable(why);
    }

    /**
     * Both readings holding at once.
     *
     * <p>Every domain, and the same domain on both sides. What a conjunction of two readings leaves
     * is what each domain's conjunction leaves, because the domains do not talk to each other: a
     * rule reaches whichever of them has a word for it and stays there, so two readings are said
     * together by saying each language's half together. And {@code shown} is either side's, an
     * argument outside the domains being no less an argument for the pair.
     *
     * <p>Written here rather than by whoever needs it. A conjunction is what this record means, so a
     * caller assembling one out of {@link #numbers} and the rest would be deciding for itself which
     * domains a conjunction reaches — and a domain added later would be left out of every such
     * caller without a word. Added here, it is in all of them.
     *
     * <p><b>One of the four is not additive, and that is why it is a conjunction rather than a
     * reading.</b> Rules union, predicates union, ranges merge at a position — three representations
     * that grow by what is added to them. Admissible values are a union of products, so a
     * conjunction of two distributes: {@code m} alternatives against {@code n} are {@code m × n},
     * and over vocabularies that share no position not one of those products is ever dropped. Ten
     * parameters of a record leaving two alternatives would be a thousand and twenty-four, outside
     * the budget that admitted each reading and counted per declaration. So that component holds the
     * readings apart ({@link ConjoinedAdmissibleValues}) and pays the product only where two of them
     * name the same position.
     *
     * <p>Both sides have to be said in one vocabulary already. Two readings of two values name their
     * positions the way each value declares them, and met without being renamed first they would
     * hold each other's rules — which is {@link #renamed} and not this.
     */
    public ConstraintState<A> meet(ConstraintState<A> other) {
        return new ConstraintState<>(numbers.meet(other.numbers), facts.meet(other.facts),
                values.meet(other.values), ordered.meet(other.ordered), shown || other.shown);
    }

    /**
     * The same rules about the same subjects, said in the vocabulary {@code naming} gives them.
     *
     * <p>What one reading calls a position is what the value it read declares it. A caller relating
     * several values has names of its own, and this is how a reading crosses into them — so that two
     * of them can be met, and so that a rule relating two of them has somewhere to be said at all.
     *
     * <p><b>A change of vocabulary and not a fold.</b> {@link NumericDomain#over} adds the
     * coefficients of two atoms arriving at one name, which is right of a form a caller wrote in two
     * spellings of one number and wrong of a state: two positions under one name would bound each
     * other, hold each other's values, and settle each other's predicates. So what is taken is an
     * {@link InjectiveRenaming} rather than a function, and it is one renaming for all four domains
     * — a subject may sit in one of them and no other, so a naming that is injective on each domain
     * read alone can still put two subjects under one name, and only something that sees the whole
     * vocabulary can refuse that.
     *
     * <p>What may not collide is every subject of the conjunction and not of each reading in turn.
     * Where the names a caller gives do not themselves say which reading a subject came from, pass
     * one renaming to every state that will be met, and it holds that for all of them. Where they
     * do — a name carrying which of several values it is a position of — the readings are kept apart
     * by the shape of the names, and a renaming of its own for each is enough. Whichever it is, it
     * is the caller's to say, and to say where the names are made rather than here.
     */
    public <B> ConstraintState<B> renamed(InjectiveRenaming<A, B> naming) {
        // The fold in `over` cannot fire: `naming` refuses a second subject at a name some other
        // subject already has, so no two atoms of this state reach one name to be added together.
        return new ConstraintState<>(numbers.over(naming::apply), facts.renamed(naming::apply),
                values.renamed(naming::apply), ordered.renamed(naming::apply), shown);
    }

    /** This, with {@code f rel 0} taken as holding. */
    public ConstraintState<A> taking(LinearForm<A> f, Rel rel, Map<A, Granularity> kinds) {
        return new ConstraintState<>(numbers.assume(f, rel, kinds), facts, values, ordered, shown);
    }

    /** This, with the predicate {@code key} taken as holding, or as failing. */
    ConstraintState<A> taking(A key, boolean positive) {
        return new ConstraintState<>(numbers, facts.assume(key, positive), values, ordered, shown);
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
    ConstraintState<A> takingValuesRead(AdmissibleValues<A> read,
                                        souther.compiler.values.Allowance<A> sets) {
        // The allowance the reading was worked out under, and not a fresh one. What this state
        // holds is that reading, and what a later reader builds out of it is more of the same
        // answer at the same positions — given an allowance of its own, a position would be allowed
        // its machine again for every phase that touched it, and the bound would be on a phase
        // rather than on what the model is finally told.
        // Said once, and what stands here until it is said is what nothing read leaves. Saying it
        // twice would keep the second reading and drop the first without a word, which is the one
        // way this can be got wrong now that it cannot combine two of them. An assertion because a
        // throw would be caught by the fail-open around the reading and leave it silently dropped.
        assert !values.hasReadings()
                : "the values of a state are read once, and these were read over " + values;
        // The reading met with what nothing read leaves, and then held as a conjunction of one.
        // Met and not assigned, which is not the same answer, and the difference is a reading of one
        // declaration's clauses — so it is worked out here and the conjunction takes what it comes
        // to. Written the other way round, a factor would be a reading nobody had met with top.
        return new ConstraintState<>(numbers, facts,
                ConjoinedAdmissibleValues.of(AdmissibleValues.<A>top().meet(read, sets), sets),
                ordered, shown);
    }

    /**
     * The same state, its values spending what {@code sets} allows.
     *
     * <p>For a caller building one answer out of several. Two states read from two declarations
     * were each put together under their own allowance, and what they come to met is a third
     * admitted set that neither of them paid for — so the caller that is building it says where
     * that is charged, and the states are taken under it before they are met.
     */
    public ConstraintState<A> under(souther.compiler.values.Allowance<A> sets) {
        return new ConstraintState<>(numbers, facts, values.under(sets), ordered, shown);
    }

    /** This, with {@code bounded} taken as holding of the positions it bounds. */
    ConstraintState<A> taking(OrderedIntervals<A> bounded) {
        return new ConstraintState<>(numbers, facts, values, ordered.meet(bounded), shown);
    }

    /**
     * The same rules with one atom settled at a value.
     *
     * <p>The one place a settling is stated, so that a reading made with one and a reading settled
     * after it was made say the same thing. Written twice, the second would be free to state it
     * under a different spacing and answer a position differently while both stayed sound.
     */
    static <A> ConstraintState<A> settling(ConstraintState<A> state, A atom,
                                           souther.compiler.numeric.Count at,
                                           souther.compiler.numeric.Granularity spacing) {
        return state.taking(
                NumericDomain.LinearForm.<A>atom(atom)
                        .minus(NumericDomain.LinearForm.<A>constant(at.at())),
                NumericDomain.Rel.EQ, java.util.Map.of(atom, spacing));
    }
}
