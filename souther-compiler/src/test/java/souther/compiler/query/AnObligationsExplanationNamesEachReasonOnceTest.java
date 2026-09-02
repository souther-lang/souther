package souther.compiler.query;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import souther.compiler.check.BehaviorContract;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.RuleRef;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.Target;
import souther.compiler.partition.Border;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.Level;
import souther.compiler.partition.LineFacts;
import souther.compiler.partition.OriginRef;
import souther.compiler.partition.ReadingGap;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * What an obligation nobody can decide says about itself, and what it leaves to the readings.
 *
 * <p>One line is read at every position that carries the type, each reading is measured on its own,
 * and what weakened the measurement is keyed on the border the reading was made at — one fact per
 * line a module could not read, which is what a module's account of itself counts. The explanation
 * of one point is the other question about the same readings, and the border is no part of its
 * answer: the readings are named under the point, one to a line, so a clause said once per reading
 * counts the paths a fact arrived by (spec §an-obligations-explanation-names-each-distinct-reason-once).
 *
 * <p>So the crossing from one to the other is what these hold to. The same reason met at any number
 * of readings is one reason; two readings stopped in two ways are two; and neither which border a
 * reading was made at nor the order the readings were walked in reaches the answer.
 */
class AnObligationsExplanationNamesEachReasonOnceTest {

    private static final Incompleteness.Code A_LIMIT = Incompleteness.Code.VALUE_TRUNCATED;
    private static final Incompleteness.Code NOTHING_COULD_READ_IT =
            Incompleteness.Code.VALUE_UNREADABLE;

    /**
     * One reason met at any number of readings is said once.
     *
     * <p>Adding a reading that meets a reason already met leaves the explanation where it was.
     * Measured at four widths, because an answer that repeats a clause per reading agrees with this
     * one at a width of one.
     */
    @ParameterizedTest
    @ValueSource(ints = {1, 2, 3, 7})
    void oneReasonMetAtAnyNumberOfReadingsIsSaidOnce(int readings) {
        List<Weakening> met = new ArrayList<>();
        for (int i = 0; i < readings; i++) {
            met.add(new Weakening.BorderValueUnreadable(border("t" + i), ReadingGap.of(A_LIMIT)));
        }

        assertEquals(new ReadingReasons(List.of(ReadingGap.of(A_LIMIT))), explanationOf(met),
                () -> readings + " readings met one reason, which is one thing to tell an author");
    }

    /**
     * Which borders the readings were made at does not reach the explanation.
     *
     * <p>The design boundary, said as an equality. A border is where a reading was made, it is what
     * tells one fact of a module's account from another, and what an author is told about this
     * point is the same whichever lines carried it.
     */
    @Test
    void theBordersTheReadingsWereMadeAtDoNotReachTheExplanation() {
        ReadingReasons here = explanationOf(List.of(
                new Weakening.BorderValueUnreadable(border("first"), ReadingGap.of(A_LIMIT)),
                new Weakening.BorderValueUnreadable(border("second"), ReadingGap.of(A_LIMIT))));
        ReadingReasons elsewhere = explanationOf(List.of(
                new Weakening.BorderValueUnreadable(border("third"), ReadingGap.of(A_LIMIT)),
                new Weakening.BorderValueUnreadable(border("fourth"), ReadingGap.of(A_LIMIT))));

        assertEquals(here, elsewhere,
                "a border is where a reading was made, not what an author is told about the point");
    }

    /**
     * The order the readings were walked in does not reach the explanation.
     *
     * <p>Equal as values and not merely as sets: what a reader compares against the last run is a
     * line of text, so two runs that met the same reasons write the same sentence whichever order
     * the readings arrived in.
     */
    @Test
    void theOrderTheReadingsWereWalkedInDoesNotReachTheExplanation() {
        ReadingReasons oneWay = explanationOf(List.of(
                new Weakening.BorderValueUnreadable(border("a"), ReadingGap.of(A_LIMIT)),
                new Weakening.BorderValueUnreadable(border("b"), ReadingGap.NO_VALUE),
                new Weakening.BorderValueUnreadable(border("c"),
                        ReadingGap.of(NOTHING_COULD_READ_IT))));
        ReadingReasons theOther = explanationOf(List.of(
                new Weakening.BorderValueUnreadable(border("c"),
                        ReadingGap.of(NOTHING_COULD_READ_IT)),
                new Weakening.BorderValueUnreadable(border("b"), ReadingGap.NO_VALUE),
                new Weakening.BorderValueUnreadable(border("a"), ReadingGap.of(A_LIMIT))));

        assertEquals(oneWay, theOther,
                "the order the readings were found in is the walk's and not the point's");
        assertEquals(List.of(ReadingGap.of(NOTHING_COULD_READ_IT), ReadingGap.of(A_LIMIT),
                        ReadingGap.NO_VALUE),
                oneWay.eachKindOnce(),
                "and the order they are said in is written down rather than met");
    }

    /**
     * Two reasons that are not one reason stay two.
     *
     * <p>The other side of saying a reason once. A fold that answered one reason for every reading
     * that could not be read would pass everything above and tell an author that a value nothing
     * could decode and a value a limit shortened are the same news.
     */
    @Test
    void reasonsThatDifferAreKeptApart() {
        assertEquals(2, explanationOf(List.of(
                        new Weakening.BorderValueUnreadable(border("a"), ReadingGap.of(A_LIMIT)),
                        new Weakening.BorderValueUnreadable(border("b"), ReadingGap.NO_VALUE)))
                .eachKindOnce().size(),
                "a limit that shortened a value and a walk that reached none are two reasons");
        assertEquals(2, explanationOf(List.of(
                        new Weakening.BorderValueUnreadable(border("a"), ReadingGap.of(A_LIMIT)),
                        new Weakening.BorderValueUnreadable(border("b"),
                                ReadingGap.of(NOTHING_COULD_READ_IT))))
                .eachKindOnce().size(),
                "and two observations that stopped for different reasons are two");
    }

    /**
     * Reasons of both kinds at several readings each come to one of each.
     *
     * <p>The row that separates saying each reason once from counting the readings: five readings,
     * two reasons, and neither number is the other.
     */
    @Test
    void severalReadingsOfEachOfTwoReasonsComeToTwo() {
        List<Weakening> met = new ArrayList<>();
        for (int i = 0; i < 3; i++) {
            met.add(new Weakening.BorderValueUnreadable(border("a" + i), ReadingGap.of(A_LIMIT)));
        }
        for (int i = 0; i < 2; i++) {
            met.add(new Weakening.BorderValueUnreadable(border("b" + i),
                    ReadingGap.of(NOTHING_COULD_READ_IT)));
        }

        assertEquals(new ReadingReasons(List.of(ReadingGap.of(NOTHING_COULD_READ_IT),
                        ReadingGap.of(A_LIMIT))),
                explanationOf(met),
                "five readings met two reasons, and what the point says is the two");
    }

    /**
     * The order holds every reason a reading can meet, and nothing twice.
     *
     * <p>The one property a written sequence cannot say for itself, and so the only one here a
     * check has to carry: a reason the order leaves out is one an obligation could be undecided
     * for and no report anywhere would name. Repeats, pairs out of order and two reasons in one
     * place are all impossible in a sequence and are not what this is about.
     *
     * <p>The population is read off the types rather than written beside them. A list written here
     * would be a copy of the order, agreeing with it exactly when nothing has changed.
     */
    @Test
    void theOrderHoldsEveryReasonAReadingCanMeet() {
        Set<ReadingGap> everyReason = new LinkedHashSet<>();
        for (Class<?> arm : ReadingGap.class.getPermittedSubclasses()) {
            if (arm.equals(ReadingGap.Observation.class)) {
                for (Incompleteness.Code code : Incompleteness.Code.values()) {
                    everyReason.add(ReadingGap.of(code));
                }
            } else if (arm.equals(ReadingGap.NoValue.class)) {
                everyReason.add(ReadingGap.NO_VALUE);
            } else {
                fail(arm.getSimpleName() + " is a reason a reading can meet, and this check does"
                        + " not know what values it has: say them here and place them in the order");
            }
        }

        assertEquals(new ArrayList<>(everyReason).size(), ReadingReasons.everyReason().size(),
                "the order says every reason and says none of them twice");
        assertTrue(ReadingReasons.everyReason().containsAll(everyReason),
                () -> "and a reason the order leaves out is one nothing would report: "
                        + everyReason.stream()
                                .filter(each -> !ReadingReasons.everyReason().contains(each))
                                .toList());
    }

    /**
     * A value that was put in order by whoever built it is refused rather than mended.
     *
     * <p>What keeps the projection the one place a canonical value is made. A constructor that
     * repaired what it was handed would pass every test above while the boundary moved to whoever
     * called it, so the refusals are held here directly and not through the fold.
     */
    @Test
    void aListNobodyPutInOrderIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> new ReadingReasons(List.of(ReadingGap.of(A_LIMIT), ReadingGap.of(A_LIMIT))),
                "a reason said twice is the thing this exists to stop");
        assertThrows(IllegalArgumentException.class,
                () -> new ReadingReasons(List.of(ReadingGap.NO_VALUE, ReadingGap.of(A_LIMIT))),
                "and an order of somebody's own is not the order a report says them in");
    }

    /**
     * A reason said where it happened is not said here.
     *
     * <p>A row nothing read at all leaves every line of the module short and is reported where the
     * row stopped. So the point is undecided and has no reason of its own to give, which is an
     * answer the projection reaches by classifying every way a measurement is weakened rather than
     * by matching the one kind it knows how to say.
     */
    @Test
    void aReasonSaidWhereItHappenedIsNotSaidAgainHere() {
        ReadingReasons met = explanationOf(List.of(new Weakening.ObservationIncomplete(
                new Incompleteness(Incompleteness.Code.OBSERVATION_ABSENT,
                        new Target.OfModule("example"), Optional.empty()))));

        assertEquals(List.of(), met.eachKindOnce(),
                "a row that never ran bears on every line, and is said where the row stopped");
    }

    /**
     * The open questions are held to the same order, and to holding every question there is.
     *
     * <p>The other place an order was written, and the same three refusals. Said of one of them
     * and not the other, the rule would be half a rule and the next order written would be a
     * number again.
     */
    @Test
    void theOpenQuestionsAreHeldToTheirOwnOrder() {
        assertEquals(Set.of(ObligationDisposition.Uncertainty.class.getPermittedSubclasses()),
                Set.copyOf(ObligationDisposition.Undecided.everyQuestion()),
                "the order says every question that can be open about an obligation");

        ObligationDisposition.Uncertainty there =
                new ObligationDisposition.Uncertainty.WhetherARowIsThere(
                        new ReadingReasons(List.of(ReadingGap.NO_VALUE)));
        ObligationDisposition.Uncertainty written =
                new ObligationDisposition.Uncertainty.WhetherARowCanBeWritten(prevented());

        assertThrows(IllegalArgumentException.class,
                () -> new ObligationDisposition.Undecided(List.of(written, there)),
                "the question an author can act on is said first");
        assertThrows(IllegalArgumentException.class,
                () -> new ObligationDisposition.Undecided(List.of(there, there)),
                "and one question is one entry, whatever left it open");
    }

    /** A showing this compiler was stopped from making, for the second of the two questions. */
    private static WritabilityKnowledge.Prevented prevented() {
        return WritabilityKnowledge.Prevented.by(
                new EstablishmentGap.Observation(Set.of(A_LIMIT)));
    }

    /** What the point says about whether a row is at it, out of what its readings went without. */
    private static ReadingReasons explanationOf(List<Weakening> met) {
        ObligationDisposition disposition = ObligationDisposition.of(
                new ObligationCoverage.Undecided(WeakeningSet.ofAll(met)),
                new WritabilityKnowledge.NoEvidence());
        ObligationDisposition.Undecided undecided =
                assertInstanceOf(ObligationDisposition.Undecided.class, disposition,
                        "a point whose readings did not run out is one nobody can decide");
        return assertInstanceOf(ObligationDisposition.Uncertainty.WhetherARowIsThere.class,
                undecided.because().getFirst(),
                "and the question the readings left open is whether a row is there").met();
    }

    /** A line on one term of one behavior, which differs from the next only in the term. */
    private static Border border(String term) {
        Carrier carrier = new Carrier.Whole();
        NumericTerm.ValueOf value = new NumericTerm.ValueOf(TermPath.of(term));
        BoundaryTarget target = BoundaryTarget.at(
                new BorderQuantity.OfACoordinate("cap", value,
                        TermOrdersFixtures.itself(value, carrier)),
                new Level.OnACarrier(carrier, Count.of(100)));
        OriginRef origin = new OriginRef.EnsuresOrigin(
                new RuleRef.Ensures(new BehaviorContract.RuleId(null, 0, 0, null), "cap"),
                0, new LineFacts(new ComparisonClaim.Cut(Towards.BELOW, true)));
        return Border.at(target, origin, new NumericDomain.Bounds(null, null));
    }
}
