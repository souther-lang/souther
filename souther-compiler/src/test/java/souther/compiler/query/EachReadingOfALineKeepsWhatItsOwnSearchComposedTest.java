package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.partition.Border;
import souther.compiler.partition.Demand;
import souther.compiler.partition.DomainPoint;
import souther.compiler.partition.Generator;
import souther.compiler.partition.QuantityKey;
import souther.compiler.partition.WayToTheBorder;
import souther.compiler.numeric.Towards;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two readings of one line each keep what their own search for a distinguishing row came to.
 *
 * <p>A helper called from two places is one line read twice, and each reading is reached under its
 * caller's own conditions — so each searches a region of its own, and the place a row stands is
 * written in the positions <em>that</em> reading names. What the two readings say about which lines
 * the rows leave standing is one answer, because that is about the line and the rows; where a row
 * may be composed is not, and a merge that kept one of the two was throwing away both halves of
 * that: the region a row was composed in, and the positions its place is written at.
 *
 * <p><b>Held at the merge itself.</b> What a model has to look like for two readings to compose
 * different rows is a helper whose call sites leave different regions, and a report over one is a
 * long way from the rule being asked about here. This asks the rule.
 */
class EachReadingOfALineKeepsWhatItsOwnSearchComposedTest {

    private static final NumericTerm.ValueOf X = new NumericTerm.ValueOf(TermPath.of("x"));

    private static final NumericTerm.ValueOf Y = new NumericTerm.ValueOf(TermPath.of("y"));

    /** The line the rows leave standing beside the one the fixture draws. */
    private static final AnotherLineTheRowsAllow.OneDoes BESIDE = beside();

    @Test
    void whatEachReadingSearchedSurvivesTheMerge() {
        Border line = TheLinesBesideABorder.aLineOverTwoPositions();
        List<BorderAssessment> merged = Coverages.merged(new LineReadings(List.of(
                reading(line, lookedAndComposedNothing()), reading(line, composedAt(1, 3)))));

        assertEquals(1, merged.size(), "two readings of one line are one line");
        assertEquals(2, merged.getFirst().toldApart().each().size(),
                () -> "and each of them keeps what its own search came to: "
                        + merged.getFirst().toldApart());
    }

    @Test
    void andTheRowOfferedIsTheOneTheReadingThatComposedItHolds() {
        Border line = TheLinesBesideABorder.aLineOverTwoPositions();
        ARowTellingTheLinesApart made = composedAt(1, 3);
        BorderAssessment merged = Coverages.merged(new LineReadings(List.of(
                reading(line, lookedAndComposedNothing()), reading(line, made)))).getFirst();

        ARowTellingTheLinesApart.AtOneReading candidate =
                merged.toldApart().firstComposed().orElseThrow();
        assertSame(made.each().getFirst().reading(), candidate.reading(),
                "the row is held beside the reading that composed it, and not beside whichever"
                        + " reading the merge kept");
        assertEquals(at(1, 3), candidate.composedAt(),
                "and the input named for it is the one that search composed at");
    }

    /** A reading of {@code line} that composed nothing says nothing about the other's region. */
    @Test
    void aReadingThatComposedNothingIsNotAnAnswerAboutTheOthersRegion() {
        Border line = TheLinesBesideABorder.aLineOverTwoPositions();
        BorderAssessment merged = Coverages.merged(new LineReadings(List.of(
                reading(line, composedAt(1, 3)),
                reading(line, lookedAndComposedNothing())))).getFirst();

        assertTrue(merged.toldApart().firstComposed().isPresent(),
                "a reading that found nowhere to compose does not take away the row another one"
                        + " composed: the two looked in two regions");
    }

    /** One reading of the line, with what a search for a distinguishing row came to at it. */
    private static BorderAssessment reading(Border line, ARowTellingTheLinesApart toldApart) {
        Map<DomainPoint, ItemAssessment> items = new LinkedHashMap<>();
        line.answers().keySet().forEach(point -> items.put(point,
                line.demand(point) instanceof Demand.NotOwed not
                        ? new ItemAssessment.NotOwed(not.reason())
                        : new ItemAssessment.Owed(line.demand(point).criterion(),
                                new Measurement.NotMeasured<>(
                                        ItemAssessment.Coverage.NotAsked.NO_ROWS),
                                ItemAssessment.WritabilityProjection.NOT_COMPUTED,
                                SearchOutcomes.none())));
        return new BorderAssessment(line, items, BESIDE, toldApart);
    }

    /** A search of one reading that composed a row standing at {@code x, y}. */
    private static ARowTellingTheLinesApart composedAt(int x, int y) {
        return new ARowTellingTheLinesApart(List.of(new ARowTellingTheLinesApart.AtOneReading(
                TheLinesBesideABorder.aLineOverTwoPositions(), at(x, y),
                SearchOutcomes.of(ItemAssessment.Attempt.Built.certified(
                        new Generator.GeneratedRow(new Generator.Purpose.Unstated(), List.of()),
                        WayToTheBorder.UNTOUCHED)))));
    }

    /** A search of one reading that ran and had nowhere to compose. */
    private static ARowTellingTheLinesApart lookedAndComposedNothing() {
        return new ARowTellingTheLinesApart(List.of(new ARowTellingTheLinesApart.AtOneReading(
                TheLinesBesideABorder.aLineOverTwoPositions(), null,
                SearchOutcomes.of(new ItemAssessment.Attempt.Unresolved(
                        new Generator.UnresolvedCombination(List.of("-2 * x + y = 0"),
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE),
                        WayToTheBorder.UNTOUCHED)))));
    }

    private static Map<NumericTerm, Place> at(int x, int y) {
        Map<NumericTerm, Place> values = new LinkedHashMap<>();
        values.put(X, Count.of(x));
        values.put(Y, Count.of(y));
        return values;
    }

    /** {@code y <= 3 * x}, which is the line the fixture's rows leave standing beside its own. */
    private static AnotherLineTheRowsAllow.OneDoes beside() {
        Map<NumericTerm, BigDecimal> direction = new LinkedHashMap<>();
        direction.put(X, BigDecimal.valueOf(-3));
        direction.put(Y, BigDecimal.ONE);
        return new AnotherLineTheRowsAllow.OneDoes(new QuantityKey(direction), BigDecimal.ZERO,
                Towards.BELOW, at(1, 3));
    }
}
