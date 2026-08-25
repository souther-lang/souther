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
     * This compiler fell short of something, whatever it was short of.
     *
     * <p>Two questions and not one tree. "Is there a rule to name?" and "did this compiler get to
     * the end of what it was reading?" are asked by different callers about the same set of
     * reasons, and the answers cut across each other: a rule this got partway through is both a
     * rule with no line and a shortfall, a rule read from end to end that divides nothing is the
     * first and not the second, and a position whose rules were never reached is the second and not
     * the first. Written as one hierarchy, whichever question the tree was shaped by, the other one
     * has to be asked by reading the reason and deciding — and a caller that decides wrong cannot
     * be stopped by anything.
     *
     * <p>So the two are capabilities and a reason implements what is true of it. A parameter typed
     * here takes exactly the reasons a reading that stopped can produce, and
     * {@link RuleWithoutLineReason} takes exactly the ones that leave a rule without a line. What
     * used to be a comment saying which reasons a caller must not be handed is now the parameter
     * type.
     */
    sealed interface ReadingStopReason extends BlockReason {}

    /**
     * A rule of the model that is no line at a position it is about, however that came about.
     *
     * <p>Whose rule it is, is the producer's to carry. What this says is that there is one: a
     * comparison was written, a reader took it apart, and what came of it is a fact about that rule
     * — either about how far this compiler got with it, or about what the rule itself places. So a
     * finding built on one of these owes an identity for the rule, and the type is what makes owing
     * it unavoidable.
     *
     * <p><b>Named for what is true of every one of them, and not for either cause.</b> The two
     * halves under this are opposite sentences about this compiler, and a name taken from one of
     * them made the other unsayable: carried as rules this could not read, a rule read from end to
     * end went out under a word meaning nobody had managed to read it. What they share is the
     * observable predicate — this rule has no line here — and that is what the name says.
     */
    sealed interface RuleWithoutLineReason extends BlockReason {

        /**
         * Whether {@code measure} is thereby short of something.
         *
         * <p>Which of the two halves the reason is in answers most of it. A reading that stopped
         * leaves what the rule states unknown, and what it would have divided or bounded is exactly
         * the part that was not read; a rule read to the end that divided no position states what
         * it states, and nothing is missing. So the second half answers alike and the first is asked
         * per reason.
         */
        boolean leavesShort(CoverageObligation.Measure measure);
    }

    /**
     * A rule a reading stopped on, which is the half of {@link RuleWithoutLineReason} that says
     * this compiler fell short.
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
     * instead.
     *
     * <p><b>The one reason in both capabilities.</b> A rule this got partway through is a rule with
     * no line here, and it is also this compiler having fallen short — so it is the only member of
     * {@link ReadingStopReason} that names a rule, and the only member of
     * {@link RuleWithoutLineReason} a caller asking about a stop may be handed.
     */
    sealed interface RuleReadingStopped extends RuleWithoutLineReason, ReadingStopReason {

        /**
         * <p><b>Two switches and no {@code default} on either.</b> Asked per measure rather than
         * answered with a set of them: a set is open at the measure end, so a third measure would
         * be one every reason had silently answered "not short of" — which is the shape this whole
         * arrangement is against, a new measure inheriting what two others happened to share. This
         * way a reason added fails the inner switch and a measure added fails the outer, and
         * whichever axis grows has to be answered for.
         */
        @Override
        default boolean leavesShort(CoverageObligation.Measure measure) {
            return switch (measure) {
                // A comparison in a form no reader takes apart may have divided the position or
                // bounded it, and nothing knows which — so both.
                case PARTITION -> switch (this) {
                    case UnreadComparisonForm _, UnreadComparisonDomain _, RuleAboutADerivedValue _,
                         UnreadValueRule _, CompetingCoordinates _ -> true;
                };
                case BOUNDARY -> switch (this) {
                    case UnreadComparisonForm _, UnreadComparisonDomain _, RuleAboutADerivedValue _,
                         UnreadValueRule _, CompetingCoordinates _ -> true;
                };
            };
        }
    }

    /**
     * A rule read to the end that left no position divided, which is the other half.
     *
     * <p>Three ways for that to happen and they are three: the quantity the rule cuts is empty, the
     * quantity is a form over several positions and divides none of them on its own, and the line
     * falls where the quantity never runs. Each is a fact about the rule rather than about this
     * compiler — the reading finished — and each is still worth saying, because a position nothing
     * is said about comes back as one the model states nothing about, and the model states this.
     *
     * <p>No measure is short of anything here, and that is what makes them one half rather than
     * three reasons that happen to agree. A rule that was read has had whatever it places placed by
     * the reading that placed it, and where it places none there is none to be owed.
     *
     * <p><b>Not a {@link ReadingStopReason}, and that is the whole of what the type is for.</b>
     * Nothing here is a stop, so nothing here may reach a caller asking what stopped a reading —
     * an accounting that calls such a rule unanswered, a claim that calls it unread, a value
     * reading that reports itself partial on its account. Each of those was reachable while one
     * type stood for both halves.
     */
    sealed interface ReadToEndWithoutLine extends RuleWithoutLineReason {

        @Override
        default boolean leavesShort(CoverageObligation.Measure measure) {
            return false;
        }
    }

    /**
     * The reading did not get to the rules of the position, so there is no rule to name.
     *
     * <p>Not a rule read and found wanting. A depth, a shape nothing reaches into, a type that
     * could not be worked out, a gathering that stopped — none of them is about any one thing an
     * author wrote, and a finding built on one names the position and nothing else. Told apart from
     * the above by the type, because the two used to be one set and a report could name a rule for
     * some of them and not the rest with nothing saying which was which.
     *
     * <p>Every one of these is a stop. There is no reading that arrives at the end of a position's
     * rules and reports one of these, so this whole half sits inside {@link ReadingStopReason} and
     * the two questions meet only at {@link RuleReadingStopped}.
     */
    sealed interface AboutThePosition extends ReadingStopReason {}

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
    static RuleWithoutLineReason ofARuleTheValueReadingLeft(souther.compiler.values.UnreadReason why) {
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
    record UnreadComparisonForm() implements RuleReadingStopped {}

    /** A comparison naming the position is against values no line is drawn on here — the carrier,
     *  asked of the carrier. */
    record UnreadComparisonDomain() implements RuleReadingStopped {}

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
    record RuleAboutADerivedValue() implements RuleReadingStopped {}

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
    record UnreadValueRule() implements RuleReadingStopped {}

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
    record CompetingCoordinates() implements RuleReadingStopped {}

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
    record ComparisonCuttingNothing() implements ReadToEndWithoutLine {}

    /**
     * The comparison was read to the end, the quantity it cuts was found, and the line it draws
     * falls where that quantity never runs.
     *
     * <p>Three times a length is never negative, so {@code List.length(xs) <= -1} has no value
     * either side of its line for a row to be owed at and divides the position into nothing.
     *
     * <p>Its own case beside {@link ComparisonCuttingNothing}, which is the answer where the
     * quantity itself is empty. The two are opposite halves of one shape: there the rule has no
     * quantity to cut, and here it has one and cuts outside it. Read as a rule this compiler could
     * not take in, an author was sent after a limit that is not there.
     */
    record ComparisonCuttingOutsideDomain() implements ReadToEndWithoutLine {}

    /**
     * The comparison relates two positions rather than dividing one.
     *
     * <p>Nothing is missing from the carrier: both sides are ordered, and a line drawn on either
     * against a number would be read. What is missing is a class about two positions, which a
     * partition of one is not — so a line like this is settled beside the partition rather than in
     * it, and the position it names is left with no class of its own from this rule.
     */
    record ComparisonBetweenPositions() implements ReadToEndWithoutLine {}

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
