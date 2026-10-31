package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.diag.Citation;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.BlockReason;
import souther.compiler.meaning.AuthoredPointMapping;
import souther.compiler.meaning.DecidingCase;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Spelling;
import souther.compiler.meaning.WhereAnApplicationIsMade;
import souther.compiler.meaning.WhereEachLineDecides;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Towards;
import souther.compiler.observe.Figure;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.reach.ComparisonArrival;

import souther.compiler.check.PathReachability;
import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.Runs;
import souther.compiler.coverage.SeenConditionOutcome;
import souther.compiler.types.ConstructOccurrence;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line goes only where every place it is watched at proved nothing reaches it.
 *
 * <p>One rule may be written into the tree that runs more than once — a library operation
 * evaluating a closure it was handed twice writes the comparison twice — so what arrives at the
 * line is answered once per place. The rule is one: a run through any of the copies is a run
 * through it, so the line is what the model states about all of them.
 *
 * <p><b>Dropped by a proof and never by the absence of one.</b> A walk that could not project what
 * arrives says so ({@link ComparisonArrival.NoProjection}) and restricts nothing beyond what the
 * declarations and the way leave; read as a place where nothing arrives, it would take a line away
 * because this compiler did not look.
 *
 * <p><b>Which is why the quantifier is the whole of this.</b> Every model written today watches
 * each rule in one place, and there the two quantifiers answer alike — so the rule is held here,
 * over the arrivals themselves, rather than waiting for a corpus that happens to write one twice.
 */
class ALineIsDroppedByAProofAtEveryPlaceItIsWatchedTest {

    private static final Carrier WHOLE = new Carrier.Whole();

    /** One position with nothing declared about it, so the declarations reach every line. */
    private static final String ONE = """
            module g

            data Ok

            behavior read : (n: Int) -> Ok
            """;

    private static final Read READ = read();

    private static final TermPath N = READ.input().positions().stream().map(Position::path)
            .filter(each -> each.toString().equals("n")).findFirst().orElseThrow();

    /** {@code n > 10}, read as a line on the values at {@code n}. */
    private static ComparisonAssessment.AtAPosition line() {
        return lineAt(BigDecimal.TEN);
    }

    /** {@code n > at}, read as a line on the values at {@code n}. */
    private static ComparisonAssessment.AtAPosition lineAt(BigDecimal at) {
        NumericTerm.FromOnePosition n = new NumericTerm.ValueOf(N);
        Cutting cutting = new Cutting(
                new BorderQuantity.OfACoordinate("f", n,
                        TermOrdersFixtures.itself(n, WHOLE)),
                new Level.OnACarrier(WHOLE, new Count(at)),
                new ComparisonClaim.Cut(Towards.BELOW, false), null);
        return new ComparisonAssessment.AtAPosition(cutting, n, null,
                ComparisonAssessment.Places.AT_NO_VALUE, new AuthoredPointMapping.Proven(
                        WrittenLine.THE_COMPARISON, cutting.claim(),
                        Derivation.AComparisonRead.Facing.NOTHING_WRITTEN, true),
                UndividedByARelation.Working.NOTHING);
    }

    /** Nothing on the way, over what the declarations leave. */
    private static Reachability untouched() {
        return Reachability.untouched(region());
    }

    /**
     * The ways to cases that come to what {@code wayTo} says of each condition: each case puts a
     * condition of its own on the way, settled, which asks nothing of a row and is no other case's.
     */
    private static WaysToACase waysTo(Function<Proposition, Reachability> wayTo) {
        Map<Proposition, List<OnTheWay>> put = new LinkedHashMap<>();
        Map<List<OnTheWay>, Proposition> putBy = new LinkedHashMap<>();
        return new WaysToACase(List.of(), decides -> put.computeIfAbsent(decides, _ -> {
            List<OnTheWay> its = List.of(settled(put.size()));
            putBy.put(its, decides);
            return its;
        }), onTheWay -> wayTo.apply(putBy.get(onTheWay)));
    }

    /** The condition numbered {@code ordinal}, settled the way the walk went. */
    private static OnTheWay.Settled settled(int ordinal) {
        ConditionOccurrence condition =
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, ordinal);
        return new OnTheWay.Settled(condition,
                new ConditionReportAnchor.WhereTheReadingMetIt("m", condition), true);
    }

    /** Values that stop short of the line, which is a proof that nothing reaches it. */
    private static ComparisonArrival misses() {
        return new ComparisonArrival.Values(N,
                new NumericDomain.Bounds(null,
                        new Endpoint(new Count(BigDecimal.ONE), true)));
    }

    @Test
    void oneProofAmongSeveralPlacesTakesNoLineAway() {
        ComparisonAssessment read = line();

        assertEquals(read, ComparisonAssessment.narrowedByWhatArrives(read, untouched(),
                        waysTo(_ -> untouched()),
                        List.of(new ComparisonArrival.NothingArrives(),
                                new ComparisonArrival.NoProjection()),
                        false, reading(), CountWitnesses.Lookup.NONE),
                "one place nobody could look at is not a place nothing arrives at");
    }

    @Test
    void everyPlaceProvingItTakesTheLineAway() {
        assertInstanceOf(ComparisonAssessment.NothingArrivesAtItsLine.class,
                ComparisonAssessment.narrowedByWhatArrives(line(), untouched(),
                        waysTo(_ -> untouched()), List.of(new ComparisonArrival.NothingArrives(), misses()), false,
                        reading(), CountWitnesses.Lookup.NONE),
                "no run answers through the rule at any place it is watched");
    }

    @Test
    void onePlaceReachingItKeepsTheLine() {
        ComparisonAssessment read = line();

        assertEquals(read, ComparisonAssessment.narrowedByWhatArrives(read, untouched(),
                        waysTo(_ -> untouched()),
                        List.of(new ComparisonArrival.NothingArrives(),
                                new ComparisonArrival.Values(N, NumericDomain.Bounds.OPEN)),
                        false, reading(), CountWitnesses.Lookup.NONE),
                "a run reaches the line at one of the places the rule is watched at");
    }

    /** A relation to another value, which draws no line of its own. */
    private static ComparisonAssessment.AgainstAnotherValue relation() {
        return new ComparisonAssessment.AgainstAnotherValue(line().cutting().over(), List.of(),
                Set.of(), List.of(), Optional.of(new ComparisonAssessment.DrawnBeside("f",
                        Citation.of(new SourcePos(1, 1)), WrittenLine.THE_COMPARISON,
                        Optional.empty())), Map.of(), Set.of(), Map.of(), Map.of());
    }

    private static final Reachability NOT_TAKEN = new Reachability.NothingReaches(
            new Reachability.TwoAtOnce.Truths(N));

    @Test
    void aRelationEveryPlaceProvesNothingArrivesAtIsDroppedAsALineIs() {
        ComparisonAssessment narrowed = ComparisonAssessment.narrowedByWhatArrives(relation(),
                untouched(), waysTo(_ -> untouched()), List.of(new ComparisonArrival.NothingArrives()),
                false, reading(), CountWitnesses.Lookup.NONE);

        assertEquals(new ComparisonAssessment.NothingArrivesAtItsRelation(
                line().cutting().over()), narrowed);
        assertEquals(ComparisonAssessment.atEachOf(line().cutting().over(),
                        new BlockReason.ComparisonRelationNothingArrivesAt()).entrySet().stream()
                        .map(each -> new ComparisonAssessment.LeftAt(each.getKey(),
                                each.getValue())).toList(),
                narrowed.whatEachPlaceIsLeftWith());
    }

    private static DecidingCase caseNamed(String name) {
        return DecidingCase.alone(new Proposition.Truth(
                new DecisionSubject.AnInput(TermPath.of(name)), true));
    }

    private static List<ComparisonAssessment.Several.Part> partsOf(
            List<DecidingCase> cases,
            Map<Proposition, ComparisonAssessment.InACase> inCases) {
        return ComparisonAssessment.partsOfARelation(new ComparisonAssessment.Several.Part(
                new PlaceOfALine(PartOfAComparison.of(WrittenLine.THE_COMPARISON),
                        Spelling.of("relation")),
                relation(), cases), relation(), inCases::get);
    }

    /** What a relation parts in a case is that case's: cases are said for several only past it. */
    @Test
    void casesPartingARelationByDifferentLinesAreReadEachByItsOwn() {
        DecidingCase low = caseNamed("low");
        DecidingCase high = caseNamed("high");
        DecidingCase none = caseNamed("none");
        List<ComparisonAssessment.Several.Part> parts = partsOf(List.of(low, high, none), Map.of(
                low.condition(), new ComparisonAssessment.InACase(true,
                        List.of(lineAt(BigDecimal.ONE))),
                high.condition(), new ComparisonAssessment.InACase(true,
                        List.of(lineAt(BigDecimal.TEN))),
                none.condition(), new ComparisonAssessment.InACase(true, List.of())));

        assertEquals(List.of(List.of(low), List.of(high), List.of()),
                parts.stream().map(ComparisonAssessment.Several.Part::cases).toList(),
                "a line in the case it parts, and the relation beside them for the one it does not");
        assertEquals(List.of(List.of(lineAt(BigDecimal.ONE)), List.of(lineAt(BigDecimal.TEN)),
                        List.of()),
                parts.stream().map(part -> ((ComparisonAssessment.AgainstAnotherValue) part.line())
                        .settling()).toList());
    }

    /** More cases than are said one by one are said as one only among those one line parts. */
    @Test
    void casesAreSaidForSeveralOnlyAmongThoseThatShareTheirLines() {
        int most = WhereEachLineDecides.MOST_CASES;
        List<DecidingCase> cases = new ArrayList<>();
        Map<Proposition, ComparisonAssessment.InACase> inCases = new LinkedHashMap<>();
        for (int i = 0; i <= most; i++) {
            DecidingCase each = caseNamed("c" + i);
            cases.add(each);
            inCases.put(each.condition(), new ComparisonAssessment.InACase(true,
                    List.of(lineAt(i % 2 == 0 ? BigDecimal.ONE : BigDecimal.TEN))));
        }

        List<ComparisonAssessment.Several.Part> parts = partsOf(cases, inCases);

        assertEquals(List.of(most / 2 + 1, most / 2),
                parts.stream().map(part -> part.cases().size()).toList(),
                "each line's own cases, none of them said for several by their number together");
    }

    /** More cases than are said one by one, all parted by one line, are said as one. */
    @Test
    void casesSharingTheirLinesPastTheMostSaidOneByOneAreSaidAsOne() {
        List<DecidingCase> cases = new ArrayList<>();
        Map<Proposition, ComparisonAssessment.InACase> inCases = new LinkedHashMap<>();
        for (int i = 0; i <= WhereEachLineDecides.MOST_CASES; i++) {
            DecidingCase each = caseNamed("c" + i);
            cases.add(each);
            inCases.put(each.condition(), new ComparisonAssessment.InACase(true,
                    List.of(lineAt(BigDecimal.ONE))));
        }

        List<ComparisonAssessment.Several.Part> parts = partsOf(cases, inCases);

        assertEquals(1, parts.size());
        assertEquals(List.of(DecidingCase.saidInAsFewAsMay(cases).getFirst()),
                parts.getFirst().cases());
        assertEquals(1, parts.getFirst().cases().size());
    }

    @Test
    void aRelationNoRowIsInAnyCaseOfItsPartIsOneTheStatementNeverTurnsOn() {
        PlaceOfALine at = new PlaceOfALine(PartOfAComparison.of(WrittenLine.THE_COMPARISON),
                Spelling.of("relation"));
        ComparisonAssessment.Several read = new ComparisonAssessment.Several(List.of(
                new ComparisonAssessment.Several.Part(at, relation(),
                        List.of(DecidingCase.alone(WhereAnApplicationIsMade.nothingAsked())))));

        for (Reachability toTheCase : List.of(NOT_TAKEN, untouched())) {
            ComparisonAssessment.Several narrowed = assertInstanceOf(
                    ComparisonAssessment.Several.class,
                    ComparisonAssessment.narrowedByWhatArrives(read, untouched(),
                            waysTo(_ -> toTheCase), List.of(misses()), false,
                            reading(), CountWitnesses.Lookup.NONE));
            // Rows arrive at the comparison in both. Where none is in the case the relation turns
            // nothing; where one is, it is a relation with no line read for it.
            assertEquals(toTheCase == NOT_TAKEN
                            ? new ComparisonAssessment.RelationTurnsNothing(
                                    line().cutting().over())
                            : relation(),
                    narrowed.parts().getFirst().line());
            assertEquals(toTheCase == NOT_TAKEN, narrowed.whatEachPlaceIsLeftWith().isEmpty(),
                    "a relation turning nothing leaves its places nothing, and one left without"
                            + " a line says so");
        }
    }

    /**
     * A line of several whose cases nobody worked out is neither kept nor dropped: it is a line
     * where it decides was not worked out, naming the figure, and the line beside it in the same
     * statement is read as it would be alone.
     *
     * <p>Rows reach the condition the cases were said as on both sides of the line, so the
     * condition is no proof that the line turns nothing; and nothing showed that it turns
     * anything in any one of the cases.
     */
    @Test
    void aLineWhoseCasesWereNotWorkedOutIsNeitherKeptNorDropped() {
        Proposition anywhere = WhereAnApplicationIsMade.nothingAsked();
        ComparisonAssessment.Several read = new ComparisonAssessment.Several(List.of(
                new ComparisonAssessment.Several.Part(new PlaceOfALine(
                        PartOfAComparison.of(WrittenLine.THE_COMPARISON), Spelling.of("unworked")),
                        line(),
                        List.of(new DecidingCase(anywhere,
                                new DecidingCase.Cases.NotTakenApart(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO)))),
                new ComparisonAssessment.Several.Part(new PlaceOfALine(
                        PartOfAComparison.of(WrittenLine.THE_COMPARISON), Spelling.of("worked")),
                        line(),
                        List.of(DecidingCase.alone(anywhere)))));

        ComparisonAssessment.Several narrowed = assertInstanceOf(
                ComparisonAssessment.Several.class,
                ComparisonAssessment.narrowedByWhatArrives(read, untouched(),
                        waysTo(_ -> untouched()), List.of(new ComparisonArrival.NoProjection()), false,
                        reading(), CountWitnesses.Lookup.NONE));
        ComparisonAssessment.Unread unread = assertInstanceOf(ComparisonAssessment.Unread.class,
                narrowed.parts().getFirst().line(), "the line whose cases nobody took apart");
        assertEquals(List.of(new BlockReason.WhereALineDecidesNotWorkedOut(
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.figure())),
                List.copyOf(unread.why().values()), "and the figure that left them whole");
        assertEquals(List.of(), narrowed.parts().getFirst().cases(),
                "and read in no case: none of them is taken for one it turns in");
        assertEquals(read.parts().getLast(), narrowed.parts().getLast(),
                "the line beside it is read as it would be alone");
        // And the statement says so at the place, though the line beside it divides that place:
        // a line nobody worked out may divide it further, so the place's classes are not settled
        // by the one that was.
        assertEquals(unread.why().entrySet().stream()
                        .map(each -> new ComparisonAssessment.LeftAt(each.getKey(),
                                each.getValue()))
                        .toList(),
                narrowed.whatEachPlaceIsLeftWith(),
                "what the statement leaves its place is what stopped the reading there");
    }

    /**
     * A line one of whose cases showed it decides is the line it is in that case, whatever became
     * of another case of it: the case nobody worked out is the line not worked out there, beside
     * it, naming the figure — neither owed rows nor dropped. Whichever of the two is asked first,
     * the answer is the same.
     */
    @Test
    void aLineAnotherCaseShowsDecidesIsTheLineThereAndNotWorkedOutBeside() {
        PlaceOfALine both = new PlaceOfALine(PartOfAComparison.of(WrittenLine.THE_COMPARISON),
                Spelling.of("both"));
        DecidingCase unworked = new DecidingCase(
                new Proposition.Truth(new DecisionSubject.AnInput(N), true),
                new DecidingCase.Cases.NotTakenApart(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO));
        DecidingCase shown = DecidingCase.alone(WhereAnApplicationIsMade.nothingAsked());
        for (List<DecidingCase> cases : List.of(List.of(unworked, shown),
                List.of(shown, unworked))) {
            ComparisonAssessment.Several read = new ComparisonAssessment.Several(List.of(
                    new ComparisonAssessment.Several.Part(both, line(), cases)));

            ComparisonAssessment.Several narrowed = assertInstanceOf(
                    ComparisonAssessment.Several.class,
                    ComparisonAssessment.narrowedByWhatArrives(read, untouched(),
                            waysTo(_ -> untouched()),
                            List.of(new ComparisonArrival.NoProjection()), false, reading(),
                            CountWitnesses.Lookup.NONE));
            assertEquals(List.of(new ComparisonAssessment.Several.Part(both, line(),
                                    List.of(shown)),
                            new ComparisonAssessment.Several.Part(both,
                                    new ComparisonAssessment.Unread(ComparisonAssessment.atEachOf(
                                            line().cutting().over(),
                                            new BlockReason.WhereALineDecidesNotWorkedOut(
                                                    CompositionBudget
                                                            .CASES_A_LINE_IS_TAKEN_APART_INTO
                                                            .figure())),
                                            WhereAReadingStopped.ELSEWHERE),
                                    List.of())),
                    narrowed.parts(),
                    () -> "the line in the case that showed it, and not worked out in the other,"
                            + " asked in the order " + cases);
        }
    }

    /**
     * One case said for several, of which one divides rows, one divides none, and the rest nobody
     * took apart: the line is the line in the one that divides rows and in no other, and beside it
     * the line is not worked out, said at its places. A row in the one that divides rows is asked
     * for; no row is asked to be in the others; and the place is not settled, since the cases
     * nobody worked out may divide it further.
     */
    @Test
    void aCaseOfWhichSomeDivideSomeDoNotAndSomeStoppedIsTheLineInThoseThatDivide() {
        PlaceOfALine at = new PlaceOfALine(PartOfAComparison.of(WrittenLine.THE_COMPARISON),
                Spelling.of("mixed"));
        Proposition dividing = new Proposition.Truth(new DecisionSubject.AnInput(
                TermPath.of("a")), true);
        Proposition dividingNone = new Proposition.Truth(new DecisionSubject.AnInput(
                TermPath.of("b")), true);
        Proposition said = new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("s")),
                true);
        DecidingCase mixed = new DecidingCase(said, new DecidingCase.Cases.EachOf(List.of(
                new DecidingCase.Cases.One(dividing), new DecidingCase.Cases.One(dividingNone),
                new DecidingCase.Cases.NotTakenApart(
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO))));
        Set<Proposition> reached = Set.of(said, dividing);
        ComparisonAssessment.Several read = new ComparisonAssessment.Several(List.of(
                new ComparisonAssessment.Several.Part(at, line(), List.of(mixed))));

        ComparisonAssessment.Several narrowed = assertInstanceOf(
                ComparisonAssessment.Several.class,
                ComparisonAssessment.narrowedByWhatArrives(read, untouched(),
                        waysTo(condition -> reached.contains(condition) ? untouched()
                                : new Reachability.NothingReaches(
                                        new Reachability.TwoAtOnce.Truths(N))),
                        List.of(new ComparisonArrival.NoProjection()), false, reading(),
                        CountWitnesses.Lookup.NONE));
        BlockReason.WhereALineDecidesNotWorkedOut stopped =
                new BlockReason.WhereALineDecidesNotWorkedOut(
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.figure());
        assertEquals(List.of(
                        new ComparisonAssessment.Several.Part(at, line(),
                                List.of(DecidingCase.alone(dividing))),
                        new ComparisonAssessment.Several.Part(at, new ComparisonAssessment.Unread(
                                ComparisonAssessment.atEachOf(line().cutting().over(), stopped),
                                WhereAReadingStopped.ELSEWHERE),
                                List.of())),
                narrowed.parts(), "the line in the case that divides rows, and not worked out");
        assertEquals(List.of(new WhereAPartDecides(at, dividing)),
                narrowed.parts().stream().flatMap(part -> part.readings().stream()).toList(),
                "a row is asked to be in the one case that divides rows and in no other");
        assertTrue(narrowed.whatEachPlaceIsLeftWith().stream()
                        .anyMatch(left -> left.why().equals(stopped)),
                () -> "and the place says it was not worked out: "
                        + narrowed.whatEachPlaceIsLeftWith());
    }

    /**
     * Two cases of a line stopped at two different figures are the line not worked out at both,
     * whichever is asked first, and the statement says both at the place: neither figure is hidden
     * by the other having been met first.
     */
    @Test
    void casesOfALineStoppedAtTwoFiguresSayBothInEitherOrder() {
        PlaceOfALine both = new PlaceOfALine(PartOfAComparison.of(WrittenLine.THE_COMPARISON),
                Spelling.of("both"));
        DecidingCase notTakenApart = new DecidingCase(
                new Proposition.Truth(new DecisionSubject.AnInput(N), true),
                new DecidingCase.Cases.NotTakenApart(
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO));
        // No more cases than are taken apart, each chosen through four parts of its own, and none
        // of them one any row reaches though rows reach every part short of the last: the asking
        // runs out of steps before it finds that none divides rows.
        int depth = 4;
        List<DecidingCase.Cases> each = new ArrayList<>();
        for (int i = 0; i < CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum() - 1; i++) {
            List<DecidingCase.Cases> parts = new ArrayList<>();
            for (int at = 0; at < depth; at++) {
                parts.add(new DecidingCase.Cases.One(new Proposition.Truth(
                        new DecisionSubject.AnInput(TermPath.of("t" + i + "." + at)), true)));
            }
            each.add(new DecidingCase.Cases.Together(parts));
        }
        DecidingCase.Cases deep = new DecidingCase.Cases.EachOf(each);
        DecidingCase tooMany = new DecidingCase(deep.holdingInSome(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum()).orElseThrow(), deep);
        Function<Proposition, Reachability> reachingOnlyEveryRow = condition ->
                condition instanceof Proposition.All all && all.parts().size() == depth
                        ? new Reachability.NothingReaches(new Reachability.TwoAtOnce.Truths(N))
                        : untouched();
        List<Figure> figures = Figure.inOrder(List.of(
                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.figure(),
                CompositionBudget.CASES_A_LINE_IS_ASKED_IN.figure()));
        for (List<DecidingCase> cases : List.of(List.of(notTakenApart, tooMany),
                List.of(tooMany, notTakenApart))) {
            ComparisonAssessment.Several read = new ComparisonAssessment.Several(List.of(
                    new ComparisonAssessment.Several.Part(both, line(), cases)));

            ComparisonAssessment.Several narrowed = assertInstanceOf(
                    ComparisonAssessment.Several.class,
                    ComparisonAssessment.narrowedByWhatArrives(read, untouched(),
                            waysTo(reachingOnlyEveryRow),
                            List.of(new ComparisonArrival.NoProjection()), false, reading(),
                            CountWitnesses.Lookup.NONE));
            assertEquals(1, narrowed.parts().size(), () -> "one part: " + narrowed);
            ComparisonAssessment.Unread unread = assertInstanceOf(
                    ComparisonAssessment.Unread.class, narrowed.parts().getFirst().line());
            assertEquals(List.of(new BlockReason.WhereALineDecidesNotWorkedOut(figures)),
                    List.copyOf(unread.why().values()),
                    () -> "not worked out at both figures, asked in the order " + cases);
            assertEquals(List.of(), narrowed.parts().getFirst().cases(),
                    "and no row is asked to be in either");
            assertEquals(List.of(figures), narrowed.whatEachPlaceIsLeftWith().stream()
                            .map(left -> assertInstanceOf(BlockReason.RuleReadingStopped.class,
                                    left.why()).figures())
                            .toList(),
                    "and the statement says both at the place, as a reading that stopped at both");
        }
    }

    /**
     * What a body is divided by is the reading as the rows corrected it. A row at a comparison
     * shows wrong a proof that nothing arrives there ({@link
     * souther.compiler.check.PathReachability.Answers#asRunWith}), and a division made from the
     * reading before the run would drop the line by the proof the run took back.
     */
    @Test
    void aBodyIsDividedByWhatArrivesOnceTheRowsHaveRun() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module g

                data Small
                data Large

                behavior size : (n: Int) -> Small | Large
                let size (n) = if n > 10 then Large else Small
                """), ModulePath.EMPTY);
        String module = compilation.modules().get(0);

        assertNotNull(compilation.db().ask(new Adequacy.Divided(module, "size")).value(),
                "the body is divided");
        assertTrue(compilation.db().isComputed(new Adequacy.ArrivedAtLines(module)),
                "by what arrives once the rows have run, where lines are drawn and nowhere else");
    }

    /**
     * An application's line is dropped by what arrives at it as a comparison's is, and a row
     * recorded answering there came to it. So a proof that nothing arrives at it is taken back
     * like a comparison's, though an application files no way out of it among the places.
     */
    @Test
    void aRowAtAnApplicationTakesBackThatNothingArrivesThere() {
        PathReachability.Answers.AsRun run = APPLIED.proving(
                new ComparisonArrival.NothingArrives())
                .asRunWith(Runs.evidenceOf(Set.of(), APPLIED.aRowCame(), Set.of()));

        assertEquals(Set.of(APPLIED.construct()), run.contradicted().emptyArrivals(),
                "a row answered there, so it came there");
        assertInstanceOf(ComparisonArrival.NoProjection.class,
                run.answers().arrivals().arrivalAt(APPLIED.construct()),
                "and what arrives restricts nothing");
    }

    /**
     * What the run takes back is what the line is assessed by. A line dropped because nothing
     * arrives where it is drawn is kept once a row has come there, and a line dropped because what
     * arrives does not reach it stays dropped: the run says a row came, not which values did.
     */
    @Test
    void aLineIsKeptWhereARowCameToWhatWasProvenEmptyAndOnlyThere() {
        ComparisonArrival proven = APPLIED.proving(new ComparisonArrival.NothingArrives())
                .arrivals().arrivalAt(APPLIED.construct());
        ComparisonArrival ran = APPLIED.proving(new ComparisonArrival.NothingArrives())
                .asRunWith(Runs.evidenceOf(Set.of(), APPLIED.aRowCame(), Set.of())).answers().arrivals()
                .arrivalAt(APPLIED.construct());
        ComparisonArrival missedAndRan = APPLIED.proving(misses())
                .asRunWith(Runs.evidenceOf(Set.of(), APPLIED.aRowCame(), Set.of())).answers().arrivals()
                .arrivalAt(APPLIED.construct());

        assertInstanceOf(ComparisonAssessment.NothingArrivesAtItsLine.class,
                assessedOn(proven), "before the run nothing arrives, and the line goes");
        assertEquals(line(), assessedOn(ran),
                "a row came there, so the proof the line went by is gone and the line stays");
        assertInstanceOf(ComparisonAssessment.NothingArrivesAtItsLine.class,
                assessedOn(missedAndRan),
                "and what arrives stopping short of the line still takes it away");
    }

    /** {@link #line()} as the one place it is watched at has {@code arrives} arriving there. */
    private static ComparisonAssessment assessedOn(ComparisonArrival arrives) {
        return ComparisonAssessment.narrowedByWhatArrives(line(), untouched(),
                waysTo(_ -> untouched()), List.of(arrives), false, reading(),
                CountWitnesses.Lookup.NONE);
    }

    /**
     * An application a line is drawn at — the emptiness check in the behavior the model below
     * states — read off a compile, with what arrives at it set by hand.
     *
     * @param read      the reading the compile made
     * @param construct the application, which files no way out of it among the places
     * @param site      where a row coming to it is recorded
     */
    private record Applied(PathReachability.Answers read, ConstructOccurrence construct,
                           ConditionOutcomeSite site) {

        /** The reading with {@code arriving} at the application, as the compile made it
         *  everywhere else. */
        PathReachability.Answers proving(ComparisonArrival arriving) {
            PathReachability.Arrivals compiled = read.arrivals();
            Map<ConstructOccurrence, ComparisonArrival> arrivals =
                    new LinkedHashMap<>(compiled.arriving());
            arrivals.put(construct, arriving);
            return new PathReachability.Answers(read.numbering(), read.found(),
                    new PathReachability.Arrivals(compiled.numbering(), arrivals,
                            compiled.recordedAt(), compiled.stopsBefore(),
                            compiled.walksHeldToOneAtMost()));
        }

        /** A row recorded answering there. */
        Set<SeenConditionOutcome> aRowCame() {
            return Set.of(new SeenConditionOutcome(site, false));
        }
    }

    private static final Applied APPLIED = applied();

    private static Applied applied() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module g

                data Small
                data Large

                behavior size : (xs: List<Int>) -> Small | Large
                let size (xs) = if List.isEmpty(xs) then Small else Large
                """), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        PathReachability.Answers read =
                compilation.db().ask(new Adequacy.PathReached(module)).value().get("size");
        Set<ConstructOccurrence> comparisons = new LinkedHashSet<>();
        read.found().keySet().forEach(place -> {
            if (place instanceof ControlPlace.Outcome outcome) {
                comparisons.add(outcome.occurrence());
            }
        });
        Map.Entry<ConstructOccurrence, ConditionOutcomeSite> application =
                read.arrivals().recordedAt().entrySet().stream()
                        .filter(each -> !comparisons.contains(each.getKey()))
                        .findFirst().orElseThrow(() -> new AssertionError(
                                "the emptiness check is an application: "
                                        + read.arrivals().recordedAt()));
        return new Applied(read, application.getKey(), application.getValue());
    }

    /**
     * The way to a case is worked out once however many lines ask it, and whether rows cross a line
     * in a case once however many lines cut at the same place: two lines reached along different
     * arms are two lines with a cutting that is equal. A line cutting somewhere else, or a case
     * that is another, is another question.
     */
    @Test
    void aCaseIsWorkedOutOnceForEveryLineThatCutsWhereTheOthersDo() {
        List<Proposition> asked = new ArrayList<>();
        WaysToACase toCases = waysTo(condition -> {
            asked.add(condition);
            return untouched();
        });
        Proposition one = new Proposition.Always(true);
        Proposition other = new Proposition.Always(false);

        assertEquals(toCases.apply(one), toCases.apply(one));
        assertEquals(List.of(one), asked, "the way to a case is read once");
        toCases.apply(other);
        assertEquals(List.of(one, other), asked, "and once for another case");

        List<String> crossings = new ArrayList<>();
        assertTrue(toCases.crossed(line().cutting(), one, reading(),
                        (_, _) -> crossings.add("first")),
                "the answer is the one the first ask gave");
        assertTrue(toCases.crossed(line().cutting(), one, reading(),
                        (_, _) -> !crossings.add("again")),
                "an equal cutting in the same case is the same question");
        assertEquals(List.of("first"), crossings);
        assertFalse(toCases.crossed(lineAt(BigDecimal.ONE).cutting(), one, reading(),
                (_, _) -> !crossings.add("another cutting")), "a cutting somewhere else is asked");
        assertFalse(toCases.crossed(line().cutting(), other, reading(),
                (_, _) -> !crossings.add("another case")),
                "and so is the same cutting in another case");
        assertEquals(List.of("first", "another cutting", "another case"), crossings);
        assertEquals(List.of(one, other), asked,
                "and each is asked along the way to its own case, read once");
    }

    private static final ConditionOccurrence OCCURRENCE =
            new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0);

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m", OCCURRENCE);

    private static final TermPath T = TermPath.of("t");

    private static final TermPath R = TermPath.of("r");

    /** That the {@code Bool} at {@code at} is {@code held}, put on the way. */
    private static OnTheWay truth(TermPath at, boolean held) {
        return new OnTheWay.TakenIn(WHERE, new RowDemand.ATruth(at, held));
    }

    /** A condition this reading has no words for, which may ask anything of a row. */
    private static OnTheWay declined() {
        ConditionOccurrence condition =
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 1);
        return new OnTheWay.Declined(condition,
                new ConditionReportAnchor.WhereTheReadingMetIt("m", condition),
                new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER));
    }

    /**
     * Whether rows cross a line in each of two cases that put {@code first} and {@code second}
     * on {@code way} — {@code beside} put on beside each — and how many questions that was: how
     * many times rows were asked to cross, each along the way it was asked along.
     */
    private static List<List<OnTheWay>> questionsOf(List<OnTheWay> way, List<OnTheWay> beside,
                                                    OnTheWay first, OnTheWay second) {
        Proposition one = new Proposition.Always(true);
        Proposition other = new Proposition.Always(false);
        Map<Proposition, List<OnTheWay>> put = Map.of(one, withBeside(beside, first),
                other, withBeside(beside, second));
        List<List<OnTheWay>> readAlong = new ArrayList<>();
        WaysToACase toCases = new WaysToACase(way, put::get, onTheWay -> {
            readAlong.add(onTheWay);
            return untouched();
        });
        List<List<OnTheWay>> questions = new ArrayList<>();
        for (Proposition each : List.of(one, other)) {
            toCases.crossed(line().cutting(), each, reading(), (_, _) -> {
                questions.add(readAlong.getLast());
                return true;
            });
        }
        return questions;
    }

    private static List<OnTheWay> withBeside(List<OnTheWay> beside, OnTheWay entry) {
        List<OnTheWay> out = new ArrayList<>(beside);
        out.add(entry);
        return out;
    }

    /**
     * Two cases that differ only in a truth nothing else on the way to them turns on ask the
     * regions the same, and are one question: a {@code Bool} is in no region, and asked once it
     * closes nothing. Asked along the way without the truth, which is what the regions are of.
     */
    @Test
    void casesThatDifferOnlyInATruthNothingElseTurnsOnAreOneQuestion() {
        assertEquals(List.of(List.of(settled(0))),
                questionsOf(List.of(), List.of(settled(0)), truth(T, true), truth(T, false)));
        assertEquals(List.of(List.of(settled(0))),
                questionsOf(List.of(), List.of(settled(0)),
                        truth(R.element(), true), truth(R.element(), false)),
                "and so do two that differ only in a truth of an element: truths are put"
                        + " together by their positions alone");
    }

    /**
     * And they are two where something else asks the truth's position, which may close a way one
     * of them takes: the way to the comparison, another part of the case, a position around it, or
     * a condition this reading has no words for, which may ask anything.
     */
    @Test
    void casesThatDifferInATruthSomethingElseMayTurnOnAreTwoQuestions() {
        OnTheWay held = truth(T, true);
        OnTheWay failing = truth(T, false);
        assertEquals(2, questionsOf(List.of(truth(T, true)), List.of(), held, failing).size(),
                "asked on the way to the comparison");
        assertEquals(2, questionsOf(List.of(), List.of(truth(R, true)),
                        truth(R.then("t"), true), truth(R.then("t"), false)).size(),
                "asked around it by the case");
        assertEquals(2, questionsOf(List.of(), List.of(truth(R.then("t"), true)),
                        truth(R, true), truth(R, false)).size(),
                "asked under it by the case");
        assertEquals(2, questionsOf(List.of(OnTheWay.OneOf.of(OCCURRENCE, WHERE,
                        List.of(List.of(truth(T, true)), List.of(settled(0))), Optional.empty())),
                        List.of(), held, failing).size(),
                "asked by an alternative on the way, which one of them may close");
        assertEquals(2, questionsOf(List.of(new OnTheWay.Counted(OCCURRENCE, WHERE,
                        List.of(new OnTheWay.Counted.Statement(1, List.of(truth(T, true)),
                                List.of(truth(T, false)))), List.of(1),
                        Proposition.SoManyHold.counting(List.of(new Proposition.Truth(
                                new DecisionSubject.AnInput(T), true)), List.of(1), List.of(1)))),
                        List.of(), held, failing).size(),
                "asked by a statement a count on the way counts");
        assertEquals(2, questionsOf(List.of(), List.of(declined()), held, failing).size(),
                "beside a condition that may ask anything");
        assertEquals(2, questionsOf(List.of(declined()), List.of(), held, failing).size(),
                "on the way, beside a condition that may ask anything");
    }

    private static InputReading reading() {
        return READ.input().reading(READ.rules());
    }

    private static SearchRegion region() {
        return READ.input().quantities(READ.rules()).region();
    }

    /** The model read once for the whole class: a region is made of the input and its rules. */
    private record Read(InputDomain input, RuleReadingSource rules) {}

    private static Read read() {
        Compilation compilation = Compilation.ofSources(List.of(ONE), ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext context =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return new Read(InputDomain.of(sigs.get("read"), context,
                TypeCardinality.Counts.workedOutIn(context), Membership.none()), rules);
    }
}
