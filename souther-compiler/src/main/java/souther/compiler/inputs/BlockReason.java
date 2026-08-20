package souther.compiler.inputs;

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
     * A reason a derivation stopped, which is what every one of these was until it was not.
     *
     * <p>The two below divide it, and what they divide is narrower than this file: a reading may
     * also run to the end and be unable to hold what it read, which stops nothing and is
     * {@link AlternativesNotSeparated}. Named so that the channels carrying a stop can say so — a
     * position is left with a stop, a document writes a word for one — and so that a reason which
     * is not one cannot arrive there to be classified as though it were.
     */
    sealed interface Stopped extends BlockReason {}

    /**
     * A rule this read and could not use, which is a reason there is always a rule to name.
     *
     * <p>Whose rule it is, is the producer's to carry. What this says is that there is one: a
     * comparison was written, a reader took it apart as far as it goes, and what stopped it is a
     * fact about that rule and this compiler. So a finding built on one of these owes an identity
     * for the rule, and the type is what makes owing it unavoidable.
     */
    sealed interface AboutARule extends Stopped {}

    /**
     * The reading did not get to the rules of the position, so there is no rule to name.
     *
     * <p>Not a rule read and found wanting. A depth, a shape nothing reaches into, a type that
     * could not be worked out, a gathering that stopped — none of them is about any one thing an
     * author wrote, and a finding built on one names the position and nothing else. Told apart from
     * the above by the type, because the two used to be one set and a report could name a rule for
     * some of them and not the rest with nothing saying which was which.
     */
    sealed interface AboutThePosition extends Stopped {}

    /**
     * Every rule about the position was read, and the reading could not hold what they say together.
     *
     * <p>Neither of the two above, which is the whole of why it is written beside them. There is no
     * rule to name — a choice reaching across two positions is answered by the clauses of the
     * declaration taken together, and by the limit this compiler reads them under, so no one clause
     * is answerable for the width. And nothing went unreached: every rule arrived and every rule was
     * taken in.
     *
     * <p>What it costs is that the values reported at the position may be wider than the rules
     * leave it, so an absence of classes here is not the model dividing the position no way.
     */
    record AlternativesNotSeparated() implements BlockReason {}

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
    static Stopped of(souther.compiler.values.UnreadReason why) {
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
    record UnreadComparisonForm() implements AboutARule {}

    /** A comparison naming the position is against values no line is drawn on here — the carrier,
     *  asked of the carrier. */
    record UnreadComparisonDomain() implements AboutARule {}

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
    record UnreadValueRule() implements AboutARule {}

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
    record CompetingCoordinates() implements AboutARule {}

    /**
     * The comparison relates two positions rather than dividing one.
     *
     * <p>Nothing is missing from the carrier: both sides are ordered, and a line drawn on either
     * against a number would be read. What is missing is a class about two positions, which a
     * partition of one is not — so a line like this is settled beside the partition rather than in
     * it, and the position it names is left with no class of its own from this rule.
     */
    record ComparisonBetweenPositions() implements AboutARule {}

    /** What a derivation would have to be able to reach into. */
    enum Traversal {

        /** The elements of a {@code List} or a {@code Set} (issue #626). */
        SEQUENCE_ELEMENT,

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
