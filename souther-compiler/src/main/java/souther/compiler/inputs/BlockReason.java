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
     * A reading that ran to the end of the rules and could not work out what they leave.
     *
     * <p>The third kind of stop, beside a rule this could not use and a position whose rules it
     * never reached. Every rule arrived and every one of them was understood; what was not worked
     * out is the answer they come to between them, and no rule is answerable for that — two that
     * are cheap apart can have an answer that is not.
     *
     * <p>Its own capability because what a caller may do with it differs. One of these carries no
     * rule and never will: a reader asking which rule to name gets nothing, and that is the fact
     * rather than a gap. Put among the reasons that do name one, every such reader would have to
     * remember which arms are the exception, and the day one forgot it would name a rule that
     * nothing was wrong with.
     */
    sealed interface AnswerRealizationStopped extends ReadingStopReason {}

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
     * A shortfall about a rule of the model, whatever became of the reading of it.
     *
     * <p>The third capability, and it cuts across the other two the way they cut across each other.
     * A rule a reading held and gave up on is one of these and is also a stop and also a rule with
     * no line; a rule no reading claimed is one of these and is neither of those — nothing stopped,
     * because nothing started, and no reader is answerable for a line it never drew.
     *
     * <p>What a caller typed here is promised is that there is a rule to name. That is what the
     * question a rule raises needs and all it needs: {@link souther.compiler.inputs.StandingQuestion}
     * carries the rule already, and what it is short of is about that rule rather than about the
     * place it stands at. Typed by {@link RuleReadingStopped} instead, a question no reading claimed
     * had to be answered with some reading's account of stopping — and every reader downstream that
     * takes a stop, a line that came to nothing, or a position's verdict would take that answer as
     * well.
     */
    sealed interface AboutARule extends BlockReason {}

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
     * <p><b>The one reason in all three capabilities.</b> A rule this got partway through is a rule
     * with no line here, it is this compiler having fallen short, and it is about a rule — so it is
     * the only member of {@link ReadingStopReason} that names a rule, and the only member of
     * {@link RuleWithoutLineReason} a caller asking about a stop may be handed.
     */
    sealed interface RuleReadingStopped extends RuleWithoutLineReason, ReadingStopReason,
            AboutARule {

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
                // And a pattern whose machine was not made is a rule that leaves no line, which is
                // what every other reason here is. What the position holds is wider than the rule
                // says, so a division the rule implies is not made and an end it states is not
                // found — short of both, and short of them because of this rule.
                //
                // What is not here is the answer nobody could work out. That leaves the position
                // short of the same two things and is not a rule without a line, because it is not
                // about a rule at all — a caller asking which of an author's rules has no line
                // would be handed one that is not the matter.
                case PARTITION -> switch (this) {
                    case UnreadComparisonForm _, UnreadComparisonDomain _, RuleAboutADerivedValue _,
                         UnreadValueRule _, ValueRuleRelatingTwoPositions _, PatternTooCostly _,
                         PatternTooDeeplyNested _,
                         CompetingCoordinates _, CasePairingNotDetermined _ -> true;
                };
                case BOUNDARY -> switch (this) {
                    case UnreadComparisonForm _, UnreadComparisonDomain _, RuleAboutADerivedValue _,
                         UnreadValueRule _, ValueRuleRelatingTwoPositions _, PatternTooCostly _,
                         PatternTooDeeplyNested _,
                         CompetingCoordinates _, CasePairingNotDetermined _ -> true;
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
     * <p><b>Every one of them is a stop, and that is a fact about this reading rather than about
     * the rule.</b> What is held at a position is a set of its own values, and every arm of
     * {@link souther.compiler.values.UnreadReason} widens it — a position carrying one of them
     * admits what the reading arrived at and may admit fewer. So a caller here is being told this
     * compiler fell short, whichever rule shape it fell short on.
     *
     * <p>Which is why a relation between two positions is {@link ValueRuleRelatingTwoPositions}
     * here and {@link ComparisonBetweenPositions} where a line is drawn. One rule, two readings,
     * two answers, and both are true: the reading of ends took {@code a < b} in completely and
     * placed no line, and the reading of values could not turn it into a set of one position's
     * values at all. Written as one reason, the second was reported in the words of the first —
     * that nothing fell short — over a position whose values are an upper bound. A word out there
     * is not what splits: {@link ReportedReason} sends both to the one the document has, so a
     * reader holding either still meets one vocabulary.
     *
     * <p>{@link souther.compiler.values.UnreadReason#NOT_REACHED} is refused rather than answered.
     * A reading that never arrived at the rules of a position is holding no rule for this to be
     * about, so a caller here would be naming one it does not have — which is the whole of what
     * {@link AboutThePosition} is beside this for.
     */
    static RuleReadingStopped ofARuleTheValueReadingLeft(souther.compiler.values.UnreadReason why) {
        // Whether there is a rule to name is the reason's own answer and not a list kept here.
        // Kept here, this was a third place saying which reasons are about a rule, and three
        // answers to one question are three chances for two of them to disagree.
        if (why.about() != souther.compiler.values.UnreadReason.About.A_RULE) {
            throw new IllegalArgumentException(
                    "a reason about " + why.about() + " holds no rule to say this of: " + why);
        }
        return switch (why) {
            case RELATES_TWO_POSITIONS -> new ValueRuleRelatingTwoPositions();
            case FORM_NOT_READ, ALTERNATIVE_NOT_READ -> new UnreadValueRule();
            case PATTERN_TOO_COSTLY -> new PatternTooCostly();
            case PATTERN_TOO_DEEPLY_NESTED -> new PatternTooDeeplyNested();
            // Refused above, each of them, and named here so that a reason added to the vocabulary
            // stops this rather than arriving as whichever arm is nearest.
            case EXACT_VALUES_TOO_COSTLY, NOT_REACHED -> throw new IllegalStateException(
                    "refused above: " + why);
        };
    }

    /**
     * The same, for a caller that has to answer for every way a value reading can be short.
     *
     * <p>What a position is left with, and not a finding: both authorities are legitimate answers
     * to "why is there nothing here", and which of them it is decides what a report may go on to
     * say rather than whether the reading stopped. Written in terms of the one above, so the
     * classification is stated once.
     *
     * <p>A stop either way, which the type says. A value reading has no way of finishing and
     * leaving a rule without a line — that is the reading of ends' answer to give — so nothing this
     * returns may reach a caller as a rule read from end to end.
     */
    static ReadingStopReason of(souther.compiler.values.UnreadReason why) {
        return switch (why) {
            case NOT_REACHED -> new ValueRulesNotReached();
            // The one a reading can be short of that is about no rule at all, and the reason this
            // answers a wider type than the one below. A caller here is asking what stopped the
            // reading of a position, which this is; asking which rule it was is the other question
            // and has no answer.
            case EXACT_VALUES_TOO_COSTLY -> new ExactValuesTooCostly();
            default -> ofARuleTheValueReadingLeft(why);
        };
    }

    /**
     * The type at the position could not be interpreted: a name denoting no declaration, or a
     * newtype whose {@code value} the walk over the names could not reach. Such a model compiles, so
     * this is a position a report is asked about and cannot be answered for.
     */
    record TypeUnresolved() implements AboutThePosition {}

    /**
     * Reading on would open a declaration this path has already opened, so what is under the
     * position is not unfolded again.
     *
     * <p><b>Not that the declaration is recursive.</b> A type that names itself is an ordinary
     * thing to declare and an ordinary thing to hold a value of; what this says is that one
     * derivation does not unfold one declaration twice on one path, which is a bound this reading
     * puts on itself. Named the other way, an author would read a report of their model where there
     * is a report of this compiler.
     *
     * @param declaration what the input returned to
     * @param openedAt    where the path opened it the first time, which is the far end of the cycle
     */
    record RecursiveExpansion(souther.compiler.types.TypeSymbol declaration, TermPath openedAt)
            implements AboutThePosition {

        public RecursiveExpansion {
            if (declaration == null || openedAt == null) {
                throw new IllegalArgumentException(
                        "a return to nowhere is not one: " + declaration + " at " + openedAt);
            }
        }
    }

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
     * A rule naming a set of strings whose machine is more than this compiler will make.
     *
     * <p>Its own case beside {@link UnreadValueRule}, and the difference is what an author can do
     * about it. That one says a rule is written in a shape no reader here enters, and what lifts it
     * is a wider reading. This says the shape was entered and the rule is simply large — a pattern
     * is a machine as big as it is written — so an author told the other would go looking for a
     * syntax that was never the difficulty.
     *
     * <p>A rule all the same, which is why it is here and not beside the one below. Somebody wrote
     * this pattern and could write it differently.
     */
    record PatternTooCostly() implements RuleReadingStopped {}

    /**
     * A rule written more deeply nested than this compiler reads.
     *
     * <p>Its own case beside the two above, and the difference is again what an author does about
     * it. {@link UnreadValueRule} sends them to the construct nothing here enters, and every
     * construct in this one is entered; {@link PatternTooCostly} says the machine would be too
     * large, and this never reached one. What is left is the brackets, which is something they can
     * write differently.
     */
    record PatternTooDeeplyNested() implements RuleReadingStopped {}

    /**
     * The rules about this position were followed, every one of them became the set it names, and
     * what those sets come to between them is more than this compiler will build.
     *
     * <p><b>About the answer and about none of the rules.</b> Two patterns each small on its own
     * have a meet the size of their product, and two rules of one declaration meet at a position as
     * surely as two halves of one clause do. So what ran out is the allowance for what the position
     * finally admits, and naming one of the rules would say that rule is why — which for a product
     * of two is false of each of them.
     *
     * <p>So it carries no rule and is not among the reasons that do ({@link
     * AnswerRealizationStopped}). A reader here has nothing to send an author to, and that is the
     * answer rather than something missing from it.
     */
    record ExactValuesTooCostly() implements AnswerRealizationStopped {}

    /**
     * Every reading was asked about the rule at this position and none of them took it in, and none
     * of them wrote down why.
     *
     * <p>Its own case because it names no reading. The others are one reading's account of where it
     * gave up, and a question left standing by nobody has no such account to give — answered with
     * one of them, an author is told which reader fell short of their clause, and the named reader
     * may be one that has no word for such a rule at all and never claimed it.
     *
     * <p>What produces it is the accounting, from the two answers coming apart: a rule no reading
     * adopted, at a position no reading recorded a reason for. A helper that reads a field of a
     * value the readings do not know the positions of is one — the clause is about that field, and
     * every reader here passed over it.
     *
     * <p>Nothing is claimed about which capability would lift it, which is what makes it different
     * from every case above. What a document writes for it is the same word it writes for a rule
     * written in a form nothing here reads, because that is the whole of what is known: no reading
     * of this compiler has a word for the rule.
     *
     * <p><b>Not a {@link ReadingStopReason} and not a {@link RuleWithoutLineReason}.</b> Nothing
     * stopped here, because nothing started; and no reading drew a line this could be the absence
     * of. So it reaches neither the readers that ask what stopped a derivation nor the account of
     * the rules a position was left with, and a {@link RuleWithoutALine} cannot be built carrying
     * it. What is true of it is that there is a rule to name, which is {@link AboutARule}.
     */
    record NoReadingTookItIn() implements AboutARule {}

    /**
     * A rule about the position says how it stands against another position, and what is held here
     * is a set of this position's own values.
     *
     * <p>The reading of values could not turn the rule into one, so what it arrived at is an upper
     * bound: a value it holds may be one no row can take, and a value it does not hold is still
     * one no rule admits. That is a stop, and every arm of
     * {@link souther.compiler.values.UnreadReason} is one for the same reason.
     *
     * <p><b>Its own case and not {@link ComparisonBetweenPositions}, which is the other reading's
     * answer for the same rule.</b> Nothing about {@code a < b} was beyond the reading of ends: it
     * took the rule in whole and placed no line, and no measure is short of anything on its
     * account. The reading of values met the same rule and got nothing it could hold. One reason
     * for both said the second in the words of the first — that the rule was read and nothing is
     * missing — over a position whose values this compiler cannot state.
     */
    record ValueRuleRelatingTwoPositions() implements RuleReadingStopped {}

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
     * The rule was read, it draws a line, and where each of the names it is between stands is known
     * — and which of those positions go together is not.
     *
     * <p>This compiler getting partway and no further, which is what puts it here rather than beside
     * a rule read to the end that divides nothing. The comparison was taken apart, a line came out
     * of it, and every name it is between reached positions; what was not reached is the pairing.
     *
     * <p><b>Not about how many sums are on the way.</b> Two names narrowed by one value are narrowed
     * together and two names under separate choices are not, and which of the two this is is a fact
     * about the model. Said as a shape this compiler does not read, an author would go looking for
     * another way to write a comparison it reads perfectly well.
     */
    record CasePairingNotDetermined() implements RuleReadingStopped {}

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
     * The comparison was read to the end, the quantity runs as far as the line it draws — and no
     * row that arrives at the comparison holds a value at the line.
     *
     * <p>{@code guard value >= 10} above {@code guard value >= 5} leaves the second guard's line
     * with nothing against it: every row that gets there is already past it. The line is inside
     * what the declarations leave, so this is not {@link ComparisonCuttingOutsideDomain} — an
     * author reading that one would look at the rule for a line their declarations refuse, and
     * what refuses it is the conditions on the way to the comparison.
     *
     * <p>Said only on a proof. The values that arrive were read off the paths, and either nothing
     * arrives at all or what arrives stops short of the line; a comparison whose arrival nothing
     * could read keeps its line and its rows.
     */
    record ComparisonNothingArrivesAtItsLine() implements ReadToEndWithoutLine {}

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
     * The comparison draws its line on a number taken over a run of values, which divides no
     * position.
     *
     * <p>Its own word and not {@link ComparisonBetweenPositions}. Nothing here is between two
     * positions: there is one number and one line, and the values it is read from stand at a place
     * inside a sequence. Two lines of sixty and forty are on the boundary of a hundred as surely as
     * one of a hundred is, so there is no class of that place for the rule to have drawn — and a
     * reader told the rule relates two positions would go looking for the pair.
     *
     * <p>Not a limit of this compiler either. The rule was read to the end and its border is drawn;
     * what is absent is a partition, because the model divides no position by it.
     */
    record ComparisonOverARun() implements ReadToEndWithoutLine {}

    /**
     * What a derivation would have to be able to reach into.
     *
     * <p>What it can reach into is not here. The elements of a {@code List} or a {@code Set} were,
     * and are positions of the input now; so was the value an {@code Option} holds, which is a
     * branch of the position under the narrowing that it holds one. A word for a reaching that is
     * made says a reader can still meet it, and the next one to read this would take its presence
     * for evidence that a sequence, or an optional, is where the walk stops.
     */
    enum Traversal {

        /**
         * What a {@code Map} holds. One case and not two, because which of a key and a value a rule
         * would be about has not been decided — and a distinction invented here would be a promise
         * about a semantics nobody has written.
         */
        MAPPING_CONTENT
    }

}
