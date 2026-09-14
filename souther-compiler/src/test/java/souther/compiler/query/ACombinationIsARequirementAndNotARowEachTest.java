package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A combination is something a row is owed for, and not something owed a row of its own.
 *
 * <p>What #967 settled was that a row composed for a pair of classes moves two positions at once
 * and says nothing about which of them the answer turned on. That is an argument about how a search
 * composes rows, and it was written down here as the other sentence — that a combination is nothing
 * a row is owed at. The two come apart as soon as the combinations are the body's own: a criterion
 * states requirements, and a test set meets one where some row settles it, whichever requirement
 * that row was composed for.
 *
 * <p>So what this file holds is the half that survives. A combination of the decisions a body
 * settles a value by is a requirement; nothing composes a row for one; and a requirement something
 * already settles is not work anybody is behind on.
 *
 * <p>Held over the types rather than over the words, for the reason the walk below gives: a name
 * says what somebody called an arm and not what it is about.
 */
class ACombinationIsARequirementAndNotARowEachTest {

    /**
     * Every kind of gap this compiler can find, named, and one of them is about a combination.
     *
     * <p>The kinds are written out rather than matched on their names. A name says what somebody
     * called an arm and not what it is about, so a finding about a combination added under another
     * word would pass a sweep for the word.
     *
     * <p>So an arm added to {@link About} arrives here as a kind nobody has said anything about,
     * and whoever adds it says which of the two it is: something the model owes a row for, or
     * something this compiler is short of. What it may not be is added without saying.
     */
    @Test
    void everyKindOfGapIsOneOfTheseAndOneIsAboutACombination() {
        List<String> every = new ArrayList<>();
        walk(About.class, every);

        // Two of them twice: a rule with no line and a rule nothing classified are each reached
        // under two of the seals above, and the walk says so rather than folding what it found.
        assertEquals(List.of(
                "ACaseNoRowExpects", "ACaseNothingWasSeenToProduce", "ACaseNoRowAppliesItTo",
                "AClassNoRowIsIn",
                // One combination of the decisions a body settles one value by, which is a
                // requirement of the interaction criterion.
                "ACombinationNoRowMakes",
                "APointOfABorder", "APointOfADeclaredBorder",
                // An arm and a row at it: what a row is owed at is the arm either way, and the
                // second says the row is written and its answer is not.
                "AnArmNoRowGoesThrough",
                // A way through the body no row takes. Not a combination: a rule says what a run
                // consulted and how each of those came out, and a condition the run never reached
                // is absent from it — so a rule constrains the positions its own way turns on and
                // says nothing about the rest, which is the whole of what a combination is about.
                "ARuleNoRowTakes",
                "ARowAtAnArmAwaitsItsAnswer",
                "ARuleWithoutALine", "ARuleNothingClassified",
                "AQuestionNothingAnswered", "ARuleWithoutALine", "ARuleNothingClassified",
                "APositionThisCouldNotRead", "APositionNoLineDivides",
                "APositionReadWiderThanItsRules", "APositionWhoseRulesWereNotReached",
                // A row owed an answer, which is owed at the row. What it is owed at is the thing
                // somebody wrote, so it is no more about a combination than an arm is — and it is
                // the one kind here that is read off the source rather than measured.
                "AnUnansweredRow"), every,
                "a kind of gap this compiler finds that this law says nothing about");
    }

    /** Every kind under {@code from}, however many seals deep it is written. */
    private static void walk(Class<?> from, List<String> into) {
        if (from.isSealed()) {
            for (Class<?> arm : from.getPermittedSubclasses()) {
                walk(arm, into);
            }
            return;
        }
        into.add(from.getSimpleName());
    }

    /**
     * What a row can be offered for now names two combinations, and nothing raises either yet.
     *
     * <p>The universe gained the combination of a body's decisions and the fallback pair, which is
     * what a criterion states requirements in. What no measure does yet is raise one: the findings
     * above have no arm about a combination, so nothing puts one in front of an author.
     *
     * <p>Written out, so that the two halves are asked separately. A reader of this file is owed
     * the difference between a shape that exists to be asked about and a shape something asks
     * about — and the day a measure raises one, the walk above is where it says so.
     */
    @Test
    void whatARowCanBeOfferedForNamesACombinationAndNothingRaisesOne() {
        List<String> every = new ArrayList<>();
        walk(souther.compiler.partition.ObligationIdentity.class, every);

        assertEquals(
                List.of("OfALine", "OfAnArm", "OfADecisionRule", "OfACombinationOfDecisions",
                        "OfAFallbackPairCell", "OfAClass", "OfAnInputCase"),
                every, "a thing a row can be offered for that this law says nothing about");
    }

    /**
     * And the pair space carries no finding of its own.
     *
     * <p>The other half. A measure may answer for gaps it did not name — the classes measure finds
     * a class no row is in — so what says a combination is owed nothing is that the space itself
     * hands none over.
     */
    @Test
    void thePairSpaceHandsOverNoFinding() {
        for (java.lang.reflect.RecordComponent part
                : PartitionEvidence.PairSpace.class.getRecordComponents()) {
            assertFalse(Adequacy.Finding.class.isAssignableFrom(part.getType()),
                    () -> "the pair space carries " + part.getName() + ", which is a finding");
        }
    }
}
