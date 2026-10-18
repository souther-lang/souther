package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.partition.Border;
import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.Demand;
import souther.compiler.partition.SaidOnTheWay;
import souther.compiler.publish.PublicationOrders;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrences;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;
import souther.compiler.partition.DomainPoint;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.Generator;
import souther.compiler.partition.QuantityKey;
import souther.compiler.partition.WayToTheBorder;
import souther.compiler.numeric.Towards;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;

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
    private static final AnotherLineTheRowsAllow.Stands BESIDE = beside();

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

        List<ARowTellingTheLinesApart.AtOneReading> candidates =
                merged.toldApart().composed(BESIDE.direction());
        assertEquals(1, candidates.size(), () -> "one search composed a row: " + candidates);
        ARowTellingTheLinesApart.AtOneReading candidate = candidates.getFirst();
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

        assertFalse(merged.toldApart().composed(BESIDE.direction()).isEmpty(),
                "a reading that found nowhere to compose does not take away the row another one"
                        + " composed: the two looked in two regions");
    }

    /**
     * Two searches that each composed a row hand both rows to the offering, and neither is chosen
     * here.
     *
     * <p>A row composed is a candidate: it may come back unread, or arrive somewhere that settles
     * nothing. Which of the two answers the line is said once each is read back, where every offered
     * row is weighed — so a generation handed only the first would have made that choice before the
     * rows were read, and a line the second row settles would go without it.
     */
    @Test
    void everyRowComposedForTheLineIsACandidateTheOfferingWeighs() {
        Border line = TheLinesBesideABorder.aLineOverTwoPositions();
        BorderAssessment merged = Coverages.merged(new LineReadings(List.of(
                reading(line, composedAt(1, 3)), reading(line, composedAt(2, 7))))).getFirst();

        assertInstanceOf(GenerationOutcome.Generated.class,
                merged.toldApart().outcome(BESIDE.direction()));
        assertEquals(2, ((GenerationOutcome.Generated) merged.toldApart()
                        .outcome(BESIDE.direction())).candidates().size(),
                "both rows go to the offering, which keeps whichever of them it needs");
    }

    /**
     * A search stopped at one call of a helper is, after the readings of its line are put
     * together, still stopped at that call and not at the other.
     *
     * <p>One authored line at one target, read at two calls: the search made for the first call's
     * reading stopped at a figure, and the one made for the second ran and composed nothing. Put
     * together, the point is stopped where the first call read it. Said of the line
     * after the merge, the stop would be at both calls — and a reader would look at the second for
     * a figure nothing there met.
     */
    @Test
    void aSearchStoppedAtOneCallIsStoppedAtThatCallAfterTheReadingsArePutTogether() {
        Border line = TheLinesBesideABorder.aLineOverTwoPositions();
        ModelOccurrence first = call(1);
        ModelOccurrence second = call(2);
        BorderAssessment merged = Coverages.merged(new LineReadings(List.of(
                searchedAt(line, first, new ItemAssessment.Attempt.Stopped(
                        new Generator.UnresolvedCombination(List.of("x = 1"),
                                Generator.UnresolvedCombination.Reason.wordFor(
                                        Set.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS))),
                        WayToTheBorder.UNTOUCHED, CompositionAccount.NOTHING,
                        PublicationOrders.COMPOSITION_BUDGETS.keep(
                                EnumSet.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS)),
                        PublicationOrders.COMPOSITION_REPERTOIRES.keep(List.of()),
                        PublicationOrders.COMPOSITION_CAPACITIES.keep(List.of()))),
                searchedAt(line, second, new ItemAssessment.Attempt.Unresolved(
                        new Generator.UnresolvedCombination(List.of("x = 1"),
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE),
                        WayToTheBorder.UNTOUCHED))))).getFirst();

        assertEquals(List.of(first, second), merged.readAt().inOrder(),
                "one line, read at both calls");
        // Through the point the line is owed at, which is where the readings of a point are put
        // together for a reader.
        List<BorderObligationPointAssessment> points =
                BorderObligationPointAssessment.across(List.of(merged), _ -> List.of(),
                        _ -> List.of());
        assertFalse(points.isEmpty(), "the line owes rows at its points");
        for (BorderObligationPointAssessment point : points) {
            WritabilityKnowledge.Prevented stopped = assertInstanceOf(
                    WritabilityKnowledge.Prevented.class, WritabilityKnowledge.of(
                            ItemAssessment.WritabilityEvidence.of(Set.of()),
                            point.owed().searches()));
            assertEquals(List.of(first),
                    stopped.readAt(stopped.by().written().getFirst()).inOrder(),
                    "stopped at the call whose search stopped, and only there");
        }
    }

    /** One reading of {@code line} read at {@code copy}, whose search at every point it owes came
     *  to {@code attempt}, said where that reading's searches are its own. */
    private static BorderAssessment searchedAt(Border line, ModelOccurrence copy,
                                               ItemAssessment.Attempt attempt) {
        Map<DomainPoint, ItemAssessment> items = new LinkedHashMap<>();
        line.answers().keySet().forEach(point -> items.put(point,
                line.demand(point) instanceof Demand.NotOwed not
                        ? new ItemAssessment.NotOwed(not.reason())
                        : new ItemAssessment.Owed(line.demand(point).criterion(),
                                new Measurement.NotMeasured<>(
                                        ItemAssessment.Coverage.NotAsked.NO_ROWS),
                                ItemAssessment.WritabilityProjection.NOT_COMPUTED,
                                SearchOutcomes.of(attempt).readAt(ModelOccurrences.of(copy)))));
        return new BorderAssessment(line, items,
                new AnotherLineTheRowsAllow.ByDirection(List.of(BESIDE)),
                ARowTellingTheLinesApart.notAsked(), ModelOccurrences.of(copy), SaidOnTheWay.NONE);
    }

    /** The {@code n}th call of a helper, as a copy of its code. */
    private static ModelOccurrence call(int n) {
        return new ModelOccurrence(SourceConstructOrigin.written(
                new WrittenOwner.Body("m", "f"), n, SourceConstruct.CALL),
                ExpansionLineage.ORIGINAL);
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
        return new BorderAssessment(line, items,
                new AnotherLineTheRowsAllow.ByDirection(List.of(BESIDE)), toldApart);
    }

    /** A search of one reading that composed a row standing at {@code x, y}. */
    private static ARowTellingTheLinesApart composedAt(int x, int y) {
        return new ARowTellingTheLinesApart(List.of(new ARowTellingTheLinesApart.AtOneReading(
                TheLinesBesideABorder.aLineOverTwoPositions(), BESIDE.direction(), at(x, y),
                SearchOutcomes.of(ItemAssessment.Attempt.Built.certified(
                        new Generator.GeneratedRow(new Generator.Purpose.Unstated(), List.of()),
                        WayToTheBorder.UNTOUCHED)))));
    }

    /** A search of one reading that ran and had nowhere to compose. */
    private static ARowTellingTheLinesApart lookedAndComposedNothing() {
        return new ARowTellingTheLinesApart(List.of(new ARowTellingTheLinesApart.AtOneReading(
                TheLinesBesideABorder.aLineOverTwoPositions(), BESIDE.direction(), null,
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
    private static AnotherLineTheRowsAllow.Stands beside() {
        Map<NumericTerm, ExactRatio> direction = new LinkedHashMap<>();
        direction.put(X, ExactRatio.of(-3));
        direction.put(Y, ExactRatio.ONE);
        return new AnotherLineTheRowsAllow.Stands(new QuantityKey(direction),
                ExactRatio.ZERO, null, Towards.BELOW, at(1, 3));
    }
}
