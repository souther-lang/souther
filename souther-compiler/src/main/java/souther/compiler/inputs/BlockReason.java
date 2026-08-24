package souther.compiler.inputs;

import souther.compiler.check.CoverageObligation;

/**
 * Why a derivation did not finish, in this compiler's own terms.
 *
 * <p>Not {@link UndividedPosition.Reason}. That one is the vocabulary an adequacy document writes,
 * which is a promise to whoever reads the document about which cases they can tell apart; this one
 * is a record of what this compiler could not do. The two are deliberately not the same set, and
 * keeping them the same type is what froze this one: a reason could not be made more precise
 * without widening a published vocabulary, so the pressure was always back towards a word coarse
 * enough to already exist.
 *
 * <p>Split apart, the two move at their own speeds. A capability gained here removes a case here
 * and need not remove a word out there, which other cases may still be reaching; and a distinction
 * worth recording here need not be a distinction the document promises.
 *
 * <p>This knows nothing about how it is reported. Which word a document writes for one of these is
 * {@link ReportedReason}'s, so a second surface may say more of the same reason without this having
 * an opinion, and so the direction stays one way: a published vocabulary does not reach back into
 * what this compiler is allowed to know.
 */
public sealed interface BlockReason {

    /**
     * A rule this read and could not use, which is a reason there is always a rule to name.
     *
     * <p>Whose rule it is, is the producer's to carry. What this says is that there is one: a
     * comparison was written, a reader took it apart as far as it goes, and what stopped it is a
     * fact about that rule and this compiler. So a finding built on one of these owes an identity
     * for the rule, and the type is what makes owing it unavoidable.
     */
    sealed interface AboutARule extends BlockReason {

        /**
         * Whether {@code measure} is thereby short of something.
         *
         * <p>Not every rule a reading set aside was one it fell short of, and the ones that were
         * are not all short of the same measure. A comparison in a form no reader takes apart may
         * have divided the position or bounded it, and nothing knows which — so both.
         *
         * <p>Relating two positions leaves neither, and not because a line is always drawn from
         * such a rule: an invariant clause that relates two positions raises no question either
         * measure answers, and a body's comparison that places a relational border has that border
         * accounted for by the reading that placed it. Either way nothing is missing here, which is
         * what this answers.
         *
         * <p><b>Two switches and no {@code default} on either.</b> Asked per measure rather than
         * answered with a set of them: a set is open at the measure end, so a third measure would
         * be one every reason had silently answered "not short of" — which is the shape this whole
         * arrangement is against, a new measure inheriting what two others happened to share. This
         * way a reason added fails the inner switch and a measure added fails the outer, and
         * whichever axis grows has to be answered for.
         */
        default boolean leavesShort(CoverageObligation.Measure measure) {
            return switch (measure) {
                case PARTITION -> switch (this) {
                    case UnreadComparisonForm _, UnreadComparisonDomain _, RuleAboutADerivedValue _,
                         UnreadValueRule _, CompetingCoordinates _ -> true;
                    // The rule was read and it divides neither position, which is what it says and
                    // not something missing here. Nor does a rule read to the end whose quantity is
                    // empty: there was no line in it, so none is owed.
                    case ComparisonBetweenPositions _, ComparisonCuttingNothing _ -> false;
                };
                case BOUNDARY -> switch (this) {
                    case UnreadComparisonForm _, UnreadComparisonDomain _, RuleAboutADerivedValue _,
                         UnreadValueRule _, CompetingCoordinates _ -> true;
                    // Whatever line such a rule places is placed by the reading that reaches it, and
                    // where none is placed none was owed. A rule whose quantity is empty places
                    // none either, and for the same reason: there was nothing in it to place.
                    case ComparisonBetweenPositions _, ComparisonCuttingNothing _ -> false;
                };
            };
        }
    }

    /**
     * A rule a reading stopped on, which is the half of {@link AboutARule} that says this compiler
     * fell short.
     *
     * <p>Told apart by the type because the two halves are opposite sentences and were one set. A
     * reading that stopped leaves whatever the rule states unknown; a rule read to the end that
     * divides no one position states what it states, and nothing is missing. Held alike, a rule
     * about a pair of positions the carrier could not be read for was described as a rule that
     * relates two positions — which is true of it, and says nothing fell short, and something did.
     *
     * <p>Which is why a reading's own answer for having stopped may only be one of these. What such
     * a rule would have raised is exactly the part that was not read, so an obligation cannot be
     * built from it; that the model is thereby short of something is what {@link #leavesShort} says
     * instead, and only these arms answer it with anything.
     */
    sealed interface ReadingStopped extends AboutARule {}

    /**
     * The reading did not get to the rules of the position, so there is no rule to name.
     *
     * <p>Not a rule read and found wanting. A depth, a shape nothing reaches into, a type that
     * could not be worked out, a gathering that stopped — none of them is about any one thing an
     * author wrote, and a finding built on one names the position and nothing else. Told apart from
     * the above by the type, because the two used to be one set and a report could name a rule for
     * some of them and not the rest with nothing saying which was which.
     */
    sealed interface AboutThePosition extends BlockReason {}

    /**
     * What a value reading's account of a rule it could not use comes to here.
     *
     * <p>The one place the two vocabularies meet, so a reader holding a reading's completeness and
     * one holding a block reason cannot come to different words for one stop. A relation between
     * two positions is what {@link ComparisonBetweenPositions} already says, whichever rule wrote
     * it: a {@code guard} comparing two inputs and an {@code invariant} relating two fields leave a
     * reader the same thing to know. The other is its own, because what would lift it is different
     * work — a reader for a form rather than a gathering that reaches further.
     *
     * <p>{@link souther.compiler.values.UnreadReason#NOT_REACHED} is refused rather than answered.
     * A reading that never arrived at the rules of a position is holding no rule for this to be
     * about, so a caller here would be naming one it does not have — which is the whole of what
     * {@link AboutThePosition} is beside this for.
     */
    static AboutARule ofARuleTheValueReadingLeft(souther.compiler.values.UnreadReason why) {
        return switch (why) {
            case RELATES_TWO_POSITIONS -> new ComparisonBetweenPositions();
            case FORM_NOT_READ, ALTERNATIVE_NOT_READ -> new UnreadValueRule();
            case NOT_REACHED -> throw new IllegalArgumentException(
                    "a reading that did not reach the rules of a position holds no rule to say"
                            + " this of");
        };
    }

    /**
     * The same, for a caller that has to answer for every way a value reading can be short.
     *
     * <p>What a position is left with, and not a finding: both authorities are legitimate answers
     * to "why is there nothing here", and which of them it is decides what a report may go on to
     * say rather than whether the reading stopped. Written in terms of the one above, so the
     * classification is stated once.
     */
    static BlockReason of(souther.compiler.values.UnreadReason why) {
        return why == souther.compiler.values.UnreadReason.NOT_REACHED
                ? new ValueRulesNotReached() : ofARuleTheValueReadingLeft(why);
    }

    /**
     * The type at the position could not be interpreted: a name denoting no declaration, or a
     * declaration reachable from itself. Such a model compiles, so this is a position a report is
     * asked about and cannot be answered for.
     */
    record TypeUnresolved() implements AboutThePosition {}

    /** The walk stopped before reaching what is under the position. */
    record DepthLimit() implements AboutThePosition {}

    /**
     * The shape at the position holds values this cannot reach into, and which reaching is missing
     * is which of {@link Traversal} it is.
     *
     * <p>Held apart rather than made one word, because what would lift each is a different piece of
     * work: choosing among however many elements a sequence holds, choosing whether an optional
     * holds one, and deciding what part of a mapping a rule is even about. Reporting them alike
     * would let one of them being implemented read as all three.
     */
    record UnsupportedTraversal(Traversal traversal) implements AboutThePosition {}

    /**
     * A comparison naming the position is written in a form no reader here takes apart: the
     * position inside an expression the terms do not name, or a threshold written as something
     * other than a constant.
     *
     * <p>Whichever rule wrote it. An invariant's clause and a {@code guard}'s comparison are two
     * producers of one kind of evidence (spec §example-partition), and what stopped each of them is
     * the same fact about this compiler.
     */
    record UnreadComparisonForm() implements ReadingStopped {}

    /** A comparison naming the position is against values no line is drawn on here — the carrier,
     *  asked of the carrier. */
    record UnreadComparisonDomain() implements ReadingStopped {}

    /**
     * A rule is written about a value that came from the position rather than about the position.
     *
     * <p>An operation answered what a closure made of what stands here, and a rule was written about
     * that. Where the values came from is known; what the rule says about the values <em>here</em>
     * is not, and working it out means inverting whatever the closure did — which is a different
     * capability and not one this compiler has.
     *
     * <p>Its own case and not {@link UnreadComparisonForm}. The form was read perfectly well and the
     * position it is about was found; an author told the first would go looking for a syntax that
     * is not the difficulty. It is here at all so that such a rule is not silent: read as nothing,
     * a model whose predicate this cannot follow is one that states no rule.
     */
    record RuleAboutADerivedValue() implements ReadingStopped {}

    /**
     * A rule naming which values the position may hold is written in a form no reader here takes
     * apart as a set of them: a call, a pattern, a comparison against something other than a value
     * written out.
     *
     * <p>Its own case beside {@link UnreadComparisonForm}, which is about a rule stating where the
     * values stop. The two are read by different readers of the same clause and would be lifted by
     * different work — one wants a wider fragment of comparison forms, and one wants a reading of
     * values that follows a rule into a shape it does not enter today.
     */
    record UnreadValueRule() implements ReadingStopped {}

    /**
     * The reading of what the position may hold never reached the rules about it.
     *
     * <p>Not a rule it read and could not use. The walk that gathers a value's clauses stopped
     * somewhere — at a depth, at a type it had already been through, at one with no declaration to
     * read — or a clause could not be typed and so arrived nowhere. None of those is a fact about
     * the rule, and all of them leave the same hole: what is written about this position is not
     * known to have been read.
     */
    record ValueRulesNotReached() implements AboutThePosition {}

    /**
     * Each of two rules is read, and they are about different coordinates of one position, so
     * neither can be the one it is measured at.
     *
     * <p>Nothing is wrong with either rule. A {@code String} is the one thing that can be measured
     * two ways — its own order, and the length of it — and which of them a position is measured at
     * is settled by whichever the model wrote about. Where the position's own type chose neither
     * and the value it sits in states an end on each, choosing either would put a line the author
     * can read beside one they cannot see, so both go unread and each says so.
     *
     * <p>Its own case and not {@link UnreadComparisonForm}. The forms were read: what is missing is
     * not a reader for an expression but a rule for which coordinate wins, and an author told the
     * first would go looking for a syntax this compiler handles perfectly well.
     */
    record CompetingCoordinates() implements ReadingStopped {}

    /**
     * The comparison was read to the end and cuts no quantity at all.
     *
     * <p>{@code a - a > 0} names a position and states nothing about its values: what it compares
     * is a number the position does not appear in. Nothing here fell short — the form was read
     * completely, and there was no line in it to draw.
     *
     * <p>Its own case beside {@link UnreadComparisonForm}, which is the answer for a form that was
     * not read. The two were one absence and so one word, and a rule this compiler had read from
     * end to end was reported as one whose spelling defeated it.
     */
    record ComparisonCuttingNothing() implements AboutARule {}

    /**
     * The comparison relates two positions rather than dividing one.
     *
     * <p>Nothing is missing from the carrier: both sides are ordered, and a line drawn on either
     * against a number would be read. What is missing is a class about two positions, which a
     * partition of one is not — so a line like this is settled beside the partition rather than in
     * it, and the position it names is left with no class of its own from this rule.
     */
    record ComparisonBetweenPositions() implements AboutARule {}

    /**
     * What a derivation would have to be able to reach into.
     *
     * <p>What it can reach into is not here. The elements of a {@code List} or a {@code Set} were,
     * and are positions of the input now — a word for a reaching that is made says a reader can
     * still meet it, and the next one to read this would take its presence for evidence that a
     * sequence is where the walk stops.
     */
    enum Traversal {

        /** The value an {@code Option} holds when it holds one. */
        OPTIONAL_VALUE,

        /**
         * What a {@code Map} holds. One case and not two, because which of a key and a value a rule
         * would be about has not been decided — and a distinction invented here would be a promise
         * about a semantics nobody has written.
         */
        MAPPING_CONTENT
    }

}
