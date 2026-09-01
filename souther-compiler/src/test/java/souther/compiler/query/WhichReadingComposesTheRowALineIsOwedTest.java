package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.Criterion;
import souther.compiler.partition.Generator;
import souther.compiler.partition.Level;
import souther.compiler.query.BorderObligationPointAssessment.Reading;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line is owed one row, and which reading composes it is a search over the readings.
 *
 * <p>Held on the resolution alone, with the evidence handed in. What each reading came to is one
 * question and what may be concluded from all of them is another, and a test that had to arrange a
 * compilation to ask the second could only reach the conclusions some model happened to produce —
 * so the two halves that matter most here, a row being enough from any one reading and a terminal
 * answer taking all of them, would be tested by whatever the corpus offered.
 *
 * <p>The asymmetry is the whole of it. A row is an existence claim and one reading settles it; that
 * no row can be written is a claim about every reading, and a walk that could not see one of them
 * has not made it.
 */
class WhichReadingComposesTheRowALineIsOwedTest {

    private static final String SAID = "String.length(value) = 1";

    private static final Carrier WHOLE = new Carrier.Whole();

    /**
     * A walk stops at the first reading that composed a row.
     *
     * <p>Which is what makes it a search rather than a fold: what the two points against a line ask
     * is the same at every reading of it, so a row standing at one of them stands at the line and
     * the readings past it are work nobody needs done.
     */
    @Test
    void theFirstReadingThatComposedARowAnswers() {
        List<String> asked = new java.util.ArrayList<>();
        PointResolution resolved = PointResolver.resolveAt(owed(),
                List.of(at("held"), at("anywhere"), at("further")), reading -> {
                    asked.add(reading.behavior());
                    return searched(reading.behavior().equals("held")
                            ? notComposed() : built(reading.behavior()));
                });

        assertInstanceOf(PointResolution.Generated.class, resolved);
        assertEquals("anywhere", ((PointResolution.Generated) resolved).composedBy(),
                "the second reading composed one, and the first composing nothing is not the line"
                        + " composing nothing");
        assertEquals(List.of("held", "anywhere"), asked,
                "and the reading past it was never asked: a row anywhere settles the line");
    }

    /** In the order the readings were handed over, which is the order the module declares them. */
    @Test
    void theReadingsAreWalkedInTheOrderTheyWereGiven() {
        List<String> asked = new java.util.ArrayList<>();
        PointResolver.resolveAt(owed(),
                List.of(at("a"), at("b"), at("c")), reading -> {
                    asked.add(reading.behavior());
                    return searched(notComposed());
                });

        assertEquals(List.of("a", "b", "c"), asked);
    }

    /**
     * A walk that composed nothing accounts for every reading, including the ones it never asked
     * about.
     *
     * <p>What an empty answer is worth turns entirely on how much of the line was looked at, and
     * read off a map of what happened to be searched that difference is an absence.
     */
    @Test
    void aWalkThatComposedNothingAccountsForEveryReading() {
        PointResolution resolved = PointResolver.resolveAt(owed(),
                List.of(at("here"), at("elsewhere")),
                reading -> reading.behavior().equals("here") ? searched(notComposed())
                        : new PointResolver.ReadingEvidence.OutOfScope());

        SearchCoverage coverage = assertInstanceOf(PointResolution.Unresolved.class, resolved)
                .coverage();
        assertEquals(List.of(at("here"), at("elsewhere")), List.copyOf(coverage.came().keySet()));
        assertInstanceOf(SearchCoverage.ReadingSearch.Attempted.class,
                coverage.came().get(at("here")));
        assertInstanceOf(SearchCoverage.ReadingSearch.OutOfScope.class,
                coverage.came().get(at("elsewhere")));
    }

    /**
     * The claim a reader may act on takes every reading walked to the end, and every one of them
     * proving it.
     *
     * <p>Never the shape of the request. A line one behavior carries is walked entirely by a request
     * about that behavior, and a rule that read which scope this was would refuse it the answer its
     * own evidence supports.
     */
    @Test
    void onlyAWalkThatSawEveryReadingSaysTheLineCannotBeWritten() {
        SearchCoverage everyOne = coverageOf(Map.of(
                at("here"), new SearchCoverage.ReadingSearch.Attempted(nothingThere()),
                at("elsewhere"), new SearchCoverage.ReadingSearch.Attempted(nothingThere())),
                List.of(at("here"), at("elsewhere")));
        SearchCoverage oneLeftOut = coverageOf(Map.of(
                at("here"), new SearchCoverage.ReadingSearch.Attempted(nothingThere()),
                at("elsewhere"), new SearchCoverage.ReadingSearch.OutOfScope()),
                List.of(at("here"), at("elsewhere")));
        SearchCoverage oneUnanswered = coverageOf(Map.of(
                at("here"), new SearchCoverage.ReadingSearch.Attempted(nothingThere()),
                at("elsewhere"), new SearchCoverage.ReadingSearch.Unavailable()),
                List.of(at("here"), at("elsewhere")));
        SearchCoverage oneOfThemMerelyRefused = coverageOf(Map.of(
                at("here"), new SearchCoverage.ReadingSearch.Attempted(nothingThere()),
                at("elsewhere"), new SearchCoverage.ReadingSearch.Attempted(refused())),
                List.of(at("here"), at("elsewhere")));

        assertTrue(everyOne.provesTheLineCannotBeWritten());
        assertFalse(oneLeftOut.provesTheLineCannotBeWritten(),
                "a reading the request never asked about may be where the row is");
        assertFalse(oneUnanswered.provesTheLineCannotBeWritten(),
                "and so may one this run could not search");
        assertFalse(oneOfThemMerelyRefused.provesTheLineCannotBeWritten(),
                "every value tried being refused is a fact about the values tried");
    }

    /**
     * Two readings in one behavior are two readings, and one of them proving nothing is enough.
     *
     * <p>The carrier is one behavior and the line is met twice in it — {@code { a: Code, b: Code }}
     * — so a walk that took the behavior as the unit would hold one of the two answers, chosen by
     * the order it walked. Where the one it kept is the reading that proves there is nothing at its
     * own position, the line is reported as unwritable over a position that was merely refused.
     */
    @Test
    void twoReadingsInOneBehaviorAreTwoReadings() {
        Reading first = new Reading(aLineAt("one", "x.a"));
        Reading second = new Reading(aLineAt("one", "x.b"));
        SearchCoverage coverage = coverageOf(Map.of(
                        first, new SearchCoverage.ReadingSearch.Attempted(nothingThere()),
                        second, new SearchCoverage.ReadingSearch.Attempted(refused())),
                List.of(first, second));

        assertTrue(coverage.walkedEveryReading(), "both were searched");
        assertFalse(coverage.provesTheLineCannotBeWritten(),
                "and the second proves nothing about the line, whatever the first proved of its"
                        + " own position");
    }

    /** One reading is enough for the claim where the line has one reading, whoever asked. */
    @Test
    void aLineWithOneReadingIsWalkedToTheEndByOneReading() {
        SearchCoverage alone = coverageOf(
                Map.of(at("only"), new SearchCoverage.ReadingSearch.Attempted(nothingThere())),
                List.of(at("only")));

        assertTrue(alone.walkedEveryReading());
        assertTrue(alone.provesTheLineCannotBeWritten());
    }

    /**
     * A reading this run could not search is carried to whoever reads the answer.
     *
     * <p>The coverage is total so that "the request never asked" and "it asked and got no answer"
     * are states rather than an absence. A projection that took only the readings that answered
     * would put that absence straight back: a reader sees the readings that said something and no
     * sign that another was asked. The one the request never asked about may be left out, because
     * the scope already says it.
     */
    @Test
    void aReadingThisRunCouldNotSearchIsCarriedOver() {
        Reading answered = at("here");
        Reading silent = at("elsewhere");
        Reading unasked = at("further");

        SearchCoverage coverage = coverageOf(Map.of(
                        answered, new SearchCoverage.ReadingSearch.Attempted(refused()),
                        silent, new SearchCoverage.ReadingSearch.Unavailable(),
                        unasked, new SearchCoverage.ReadingSearch.OutOfScope()),
                List.of(answered, silent, unasked));

        BorderAccount.Unmet unmet = BorderAccount.unmet("Code", SAID,
                new PointResolution.Unresolved(coverage));

        List<BorderAccount.At> came = assertInstanceOf(
                BorderAccount.Unmet.WhatTheReadingsCameTo.class, unmet).came();
        assertEquals(List.of(answered, silent), came.stream().map(BorderAccount.At::reading).toList(),
                "the reading that answered and the one that could not be searched");
        assertInstanceOf(BorderAccount.At.Searched.class, came.get(0));
        assertInstanceOf(BorderAccount.At.CouldNotBeSearched.class, came.get(1));
    }

    /**
     * A coverage whose readings are in another order than the line's cannot be made.
     *
     * <p>The order is half the contract: it is what makes "the first that composed a row" one
     * answer rather than whichever the walk reached. Checked as a set, that half was a convention
     * and a walk that came back in its own order would have been accepted as the line's.
     */
    @Test
    void aCoverageOutOfTheReadingsOrderIsRefused() {
        SequencedMap<Reading, SearchCoverage.ReadingSearch> backwards = new LinkedHashMap<>();
        backwards.put(at("elsewhere"), new SearchCoverage.ReadingSearch.Attempted(refused()));
        backwards.put(at("here"), new SearchCoverage.ReadingSearch.Attempted(refused()));

        assertThrows(IllegalStateException.class,
                () -> new SearchCoverage(List.of(at("here"), at("elsewhere")), backwards));
    }

    /** A coverage that leaves one of the line's readings out cannot be made. */
    @Test
    void aCoverageShortOfAReadingIsRefused() {
        assertThrows(IllegalStateException.class, () -> coverageOf(
                Map.of(at("here"), new SearchCoverage.ReadingSearch.Attempted(refused())),
                List.of(at("here"), at("elsewhere"))));
    }

    /**
     * A point the measurement says needs no search is not one a walk was made at.
     *
     * <p>Told apart from a search that found nothing, and not by degree: those readings were looked
     * at and this point was not, because looking would tell nobody anything.
     */
    @Test
    void aPointARowAlreadyStandsAtIsNotSearchedFor() {
        PointResolution resolved = PointResolver.resolveAt(
                new ObligationAssessment(new Criterion.AtTheLevel(Level.ACount.of(1)),
                        new ObligationCoverage.Witnessed(),
                        ItemAssessment.WritabilityProjection.PROVEN, null),
                List.of(at("anywhere")), _ -> {
                    throw new AssertionError("nothing is searched at a point a row stands at");
                });

        assertEquals(new PointResolution.NoSearch(
                PointResolution.Cause.A_ROW_ALREADY_STANDS), resolved);
    }

    private static SearchCoverage coverageOf(Map<Reading, SearchCoverage.ReadingSearch> came,
                                             List<Reading> readings) {
        SequencedMap<Reading, SearchCoverage.ReadingSearch> ordered = new LinkedHashMap<>();
        readings.forEach(reading -> {
            if (came.containsKey(reading)) {
                ordered.put(reading, came.get(reading));
            }
        });
        return new SearchCoverage(readings, ordered);
    }

    /** A reading of the line: one behavior at its one position carrying the type. */
    private static Reading at(String behavior) {
        return new Reading(aLineAt(behavior, behavior + ".value"));
    }

    /** Where a line was read: one position of one behavior, cut at one value. */
    private static BoundaryTarget aLineAt(String behavior, String path) {
        return BoundaryTarget.at(
                new BorderQuantity.OfACoordinate(new AxisId(behavior, path),
                        new NumericTerm.ValueOf(TermPath.of(path)), TermOrdersFixtures.itself(WHOLE)),
                new Level.OnACarrier(WHOLE, Count.of(1)));
    }

    /** A point a row is owed at, measured and missed, so a search of it would tell somebody
     *  something. */
    private static ObligationAssessment owed() {
        return new ObligationAssessment(new Criterion.AtTheLevel(Level.ACount.of(1)),
                new ObligationCoverage.Missed(),
                ItemAssessment.WritabilityProjection.PROVEN, null);
    }

    private static PointResolver.ReadingEvidence searched(ItemAssessment.Attempt attempt) {
        return new PointResolver.ReadingEvidence.Searched(attempt);
    }

    private static ItemAssessment.Attempt built(String carrier) {
        return new ItemAssessment.Attempt.Built(new Generator.GeneratedRow(
                new Generator.Purpose.ForAPoint(carrier + ": " + SAID), List.of()), null);
    }

    /** The same, as what a reading holds at the point. */
    private static ItemAssessment.Attempt notComposed() {
        return new ItemAssessment.Attempt.Unresolved(refused(), null);
    }

    /** A search that ran and settled nothing, which is what most of them come to. */
    private static Generator.UnresolvedCombination refused() {
        return new Generator.UnresolvedCombination(List.of(SAID),
                Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED);
    }

    /** A search that walked what the rules leave and found there is nothing there — the one kind of
     *  answer a reader may act on (ADR-0091). */
    private static Generator.UnresolvedCombination nothingThere() {
        return new Generator.UnresolvedCombination(List.of(SAID),
                Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE);
    }
}
