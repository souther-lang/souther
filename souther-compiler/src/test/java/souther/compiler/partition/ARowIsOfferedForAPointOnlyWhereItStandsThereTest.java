package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Prepared;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Shapes;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row is offered for a point only where the value that was built stands there.
 *
 * <p>What was asked for and what was built are two things, and the generator answered with the
 * first. A row composed to put a term at a number went out labelled for that number whatever the
 * value came to — so a row that reached the point and a row that did not were reported alike, as
 * {@code Generated}, and an author reading the report was told a shortfall had been answered when
 * it had not (issue #1063).
 *
 * <p><b>Held against a construction that answers with something else, because that is the case the
 * check is for.</b> {@code TermRealizations} states of itself that every value built there reads
 * back as the number it was built for, and names the way it would break: "a row offered at an edge
 * it does not stand on". The generator's own arithmetic meeting that is what the other tests here
 * are about; this one is about what happens when something between the candidate and the value does
 * not — a decoder that narrows, a construction that clamps — which is exactly what nothing was
 * asking.
 */
class ARowIsOfferedForAPointOnlyWhereItStandsThereTest {

    private static final String BOUNDED = """
            module example.bounded

            data Amount = Int
                invariant value >= 0 && value <= 100
            data Req = { cost: Amount }
            data Res = { n: Int }

            behavior f : (r: Req) -> Res
            """;

    /**
     * A construction that answers with a value away from the point offers no row for it.
     *
     * <p>And says which of the two it is: nothing was refused by the model, so reporting it as a
     * value the rules turned away would send an author looking at their invariant.
     */
    @Test
    void aValueThatLandsElsewhereIsNoWitness() {
        Generator.BoundaryAttempt attempt = attemptAt(Count.of(100), always(7));

        Generator.BoundaryAttempt.Unresolved no = assertInstanceOf(
                Generator.BoundaryAttempt.Unresolved.class, attempt,
                "a value that reads back at 7 is no row for the point at 100");
        assertEquals(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS,
                no.why().reason());
    }

    /** And one that answers with the value it was built for is the row. */
    @Test
    void aValueThatLandsOnThePointIsTheWitness() {
        Generator.BoundaryAttempt attempt = attemptAt(Count.of(100), always(100));

        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, attempt,
                "a value that reads back at 100 stands at the point");
        assertEquals(List.of("Req { cost = Amount(100) }"),
                built.row().inputs().stream().map(FixtureTemplate::text).toList());
    }

    /**
     * And where nothing built the candidate, the row is offered as it was composed.
     *
     * <p>The fail-open half, and the reason it is one: there is no runtime to put a candidate
     * through, so nothing here can say where it went — and refusing every row wherever a build is
     * unavailable would answer a question nobody asked with the worst of the two answers.
     */
    @Test
    void whereNothingBuiltItTheRowIsOfferedAsComposed() {
        assertInstanceOf(Generator.BoundaryAttempt.Built.class,
                attemptAt(Count.of(100), Generator.CandidateCheck.ANY),
                "nothing ran the candidate, so nothing says it stands anywhere else");
    }

    /** Two parameters, and a second position under the first that offers two values — so its
     *  search has two candidates, which is what lets a parameter refuse one and still succeed. */
    private static final String TWO = """
            module example.bounded

            data Amount = Int
                invariant value >= 0 && value <= 100
            data Note = String
                invariant String.matches("[0-9a-z]+", value)
            data Req = { cost: Amount, note: Note }
            data Other = { n: Int }
            data Res = { n: Int }

            behavior g : (r: Req, o: Other) -> Res
            """;

    /**
     * What one parameter's search found out is not said of another's.
     *
     * <p>A candidate turned away for standing elsewhere is news about the parameter it was built
     * for. Kept for the whole row, the first parameter certifying its second candidate would name
     * the reason a later parameter failed for — and the later one was refused by the model, which is
     * the opposite answer: one says every value the rules allow was turned away, and the other says
     * what was built did not stand where it was built for.
     */
    @Test
    void whatOneParametersSearchFoundOutIsNotSaidOfAnothers() {
        List<String> first = new ArrayList<>();
        Generator.BoundaryAttempt attempt = attemptOver(TWO, "g", Count.of(100),
                (parameter, candidate) -> {
                    if (parameter == 0) {
                        first.add(candidate.text());
                    }
                    if (parameter != 0) {
                        return new Generator.CandidateCheck.Built.Refused("the model refuses it");
                    }
                    // The first candidate stands away from the point and the other stands on it, so
                    // this parameter refuses one and succeeds all the same. Said of each candidate
                    // and not of how often it was asked: a check answers the same value the same way.
                    return new Generator.CandidateCheck.Built.Value(
                            reqWith(candidate.text().contains("Note(\"0\")") ? 7 : 100));
                });

        assertEquals(2, first.stream().distinct().count(),
                "the first parameter refused one candidate and took another: " + first);
        Generator.BoundaryAttempt.Unresolved no = assertInstanceOf(
                Generator.BoundaryAttempt.Unresolved.class, attempt,
                "no value of `o` was allowed, so no row builds");
        assertEquals(Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
                no.why().reason(),
                "the second parameter's every candidate was refused by the model, which the first"
                        + " parameter's uncertified candidate says nothing about");
    }

    /** A check answering every candidate with a {@code Req} whose cost is {@code n}, whatever was
     *  asked for — a construction that does not answer with what it was given. */
    private static Generator.CandidateCheck always(int n) {
        return (_, _) -> new Generator.CandidateCheck.Built.Value(reqWith(n));
    }

    private static ObservedValue reqWith(int n) {
        return new ObservedValue.Constructed(declared("Req"), Map.of("cost",
                new ObservedValue.Constructed(declared("Amount"),
                        Map.of("value", new ObservedValue.Integer(n))),
                "note", new ObservedValue.Text("")));
    }

    private static souther.compiler.types.TypeSymbol declared(String name) {
        return souther.compiler.types.TypeSymbols.declared(
                new souther.compiler.types.TypeKey("example.bounded", name));
    }

    private static Generator.BoundaryAttempt attemptAt(souther.compiler.numeric.Place at,
                                                       Generator.CandidateCheck check) {
        return attemptOver(BOUNDED, "f", at, check);
    }

    private static Generator.BoundaryAttempt attemptOver(String source, String behavior,
                                                         souther.compiler.numeric.Place at,
                                                         Generator.CandidateCheck check) {
        return attemptOver(source, behavior, at, check, Generator.Trial.NOTHING_RUNS);
    }

    private static Generator.BoundaryAttempt attemptOver(String source, String behavior,
                                                         souther.compiler.numeric.Place at,
                                                         Generator.CandidateCheck check,
                                                         Generator.Trial trial) {
        return attemptOver(source, behavior, at, check, trial, java.util.Optional.empty());
    }

    private static Generator.BoundaryAttempt attemptOver(String source, String behavior,
                                                         souther.compiler.numeric.Place at,
                                                         Generator.CandidateCheck check,
                                                         Generator.Trial trial,
                                                         java.util.Optional<Generator.RowJudge> judge) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(each -> each.name().equals(behavior)).findFirst().orElseThrow();
        InputDomain domain = compilation.db()
                .ask(new souther.compiler.query.Adequacy.Inputs(module)).value().get(spec.name());
        assertNotNull(domain, "the model under test compiles");
        Partitions.Partitioning partitioning =
                Partitions.of(spec.name(), domain.reading(rules), ReadAs.THE_COMPILATION_DOES);

        List<String> names = new ArrayList<>();
        spec.params().forEach(each -> names.add(each.name()));
        MeasuredInput subject =
                MeasuredInput.of(spec.name(), domain.reading(rules), partitioning);

        Axis axis = partitioning.axes().stream()
                .filter(each -> each.path().toString().equals("r.cost")).findFirst().orElseThrow();
        return Generator.probeFixing(subject, "r.cost = " + at,
                Map.of(new RealizationTarget.AtOnePosition(axis.term()), at),
                NumbersAskedFor.of(LevelRegion.point(new Level.OnACarrier(
                        domain.quantities(rules).ordersOf(axis.term()).answered(), at))),
                Reachability.untouched(domain.quantities(rules).region()), check,
                StandInAttempt.REQUIRING_NOTHING, trial, judge);
    }

    /** A trial whose run of the {@code n}-th row it is handed (from 1) is {@code answered}. */
    private static Generator.Trial running(java.util.function.IntPredicate answered,
                                           List<List<String>> handed) {
        return row -> {
            handed.add(row.inputs().stream().map(FixtureTemplate::text).toList());
            return new Generator.ObservedRun(new Generator.Watched.NoAccount(),
                    answered.test(handed.size())
                            ? new AnswerObservation.Answered(new ObservedValue.Integer(0))
                            : new AnswerObservation.NotAnswered());
        };
    }

    /** Rows run and none answering, with nothing else left untried, are no witness. */
    @Test
    void rowsThatNoneAnsweredAreNoWitnessAndNotAPointNoRowReaches() {
        Generator.BoundaryAttempt.Unresolved no = assertInstanceOf(
                Generator.BoundaryAttempt.Unresolved.class, Generator.noRowAnswered("p",
                        SearchShortfall.NONE, false, CompositionAccount.NOTHING));

        assertEquals(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS,
                no.why().reason());
    }

    /** A figure that stopped the search is said as the figure beside the rows that did not answer,
     *  because the rows past it were never composed. */
    @Test
    void aFigureTheSearchWasStoppedAtIsSaidBesideRowsThatNoneAnswered() {
        Generator.BoundaryAttempt.Stopped stopped = assertInstanceOf(
                Generator.BoundaryAttempt.Stopped.class, Generator.noRowAnswered("p",
                        SearchShortfall.of(CompositionShortfall.of(List.of(
                                CompositionBudget.ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW))),
                        false, CompositionAccount.NOTHING));

        assertEquals(Set.of(CompositionBudget.ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW),
                stopped.met().figures());
    }

    /** What the search could not enumerate is not dropped for the figure, or for the word. */
    @Test
    void aPopulationTheSearchCouldNotEnumerateIsKeptBesideTheRows() {
        CompositionShortfall both = CompositionShortfall.of(
                List.of(CompositionBudget.ROWS_A_WALK_HANDS_THE_CHOICE_OF_A_ROW),
                List.of(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED), List.of());

        Generator.BoundaryAttempt.Stopped stopped = assertInstanceOf(
                Generator.BoundaryAttempt.Stopped.class, Generator.noRowAnswered("p",
                        SearchShortfall.of(both), false, CompositionAccount.NOTHING));
        Generator.BoundaryAttempt.Unexhausted unexhausted = assertInstanceOf(
                Generator.BoundaryAttempt.Unexhausted.class, Generator.noRowAnswered("p",
                        SearchShortfall.of(CompositionShortfall.writing(
                                List.of(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED))),
                        false, CompositionAccount.NOTHING));

        assertEquals(both, stopped.met());
        assertEquals(Set.of(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED),
                unexhausted.met().populations());
    }

    /** And so is the rule an offer was short of. */
    @Test
    void theRuleAnOfferWasShortOfIsKeptBesideTheRows() {
        SequencedMap<TermPath, StringOfferShortfall> offered = new LinkedHashMap<>();
        offered.put(TermPath.of("r"), StringOfferShortfall.NONE);

        Generator.BoundaryAttempt.Unresolved no = assertInstanceOf(
                Generator.BoundaryAttempt.Unresolved.class, Generator.noRowAnswered("p",
                        SearchShortfall.of(CompositionShortfall.NONE, offered),
                        false, CompositionAccount.NOTHING));

        assertEquals(offered, no.why().alsoShort());
    }

    /** A row whose run aborts is passed over for the next one composed, which answers. */
    @Test
    void aFirstRowThatAbortsIsPassedOverForTheNextThatAnswers() {
        List<List<String>> handed = new ArrayList<>();
        Generator.BoundaryAttempt attempt = attemptOver(TWO, "g", Count.of(100),
                (parameter, candidate) -> new Generator.CandidateCheck.Built.Value(reqWith(100)),
                running(n -> n > 1, handed));

        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, attempt,
                "the second row composed answers, and stands at the point");
        assertEquals(handed.get(1),
                built.row().inputs().stream().map(FixtureTemplate::text).toList(),
                "and it is the row offered, not the first");
        assertNotEquals(handed.get(0), handed.get(1));
    }

    /**
     * A row the judge refuses is passed over inside the walk, and the walk goes on to the next
     * assignment, which the judge accepts.
     *
     * <p>Asked of the rows after the walk had taken one, there was no next row to go on to: the
     * first candidate decided. What a way cannot say — a case turning on what every node below the
     * start comes to — is for a run to say, and a run saying no has to send the search on.
     */
    @Test
    void aRowTheJudgeRefusesIsPassedOverForTheNextTheJudgeAccepts() {
        // A function of the row alone, as a judge is: the walk asks it again of a row it reaches
        // along another way, and the answer is the same.
        List<List<String>> asked = new ArrayList<>();
        Generator.BoundaryAttempt attempt = attemptOver(TWO, "g", Count.of(100),
                (parameter, candidate) -> new Generator.CandidateCheck.Built.Value(reqWith(100)),
                Generator.Trial.NOTHING_RUNS, java.util.Optional.of(row -> {
                    asked.add(row.inputs().stream().map(FixtureTemplate::text).toList());
                    return !row.inputs().getLast().text().equals("Other { n = 0 }");
                }));

        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, attempt,
                "a row past the one the judge refused is accepted");
        assertEquals(List.of("Req { cost = Amount(100), note = Note(\"0\") }", "Other { n = 1 }"),
                built.row().inputs().stream().map(FixtureTemplate::text).toList(),
                "and it is the row offered, not the first");
        assertTrue(asked.stream().anyMatch(row -> row.getLast().equals("Other { n = 0 }")),
                () -> "the first row was asked about and refused: " + asked);
    }

    /** Where the judge refuses every row, nothing was found, which is not that no row can be. */
    @Test
    void aJudgeThatRefusesEveryRowLeavesNoWitnessAndNotAnUnreachablePoint() {
        Generator.BoundaryAttempt attempt = attemptOver(TWO, "g", Count.of(100),
                (parameter, candidate) -> new Generator.CandidateCheck.Built.Value(reqWith(100)),
                Generator.Trial.NOTHING_RUNS, java.util.Optional.of(_ -> false));

        Generator.BoundaryAttempt.Unresolved no = assertInstanceOf(
                Generator.BoundaryAttempt.Unresolved.class, attempt);
        assertEquals(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS,
                no.why().reason());
    }

    /** Where every row composed aborts, the point is one this compiler composed no answering row
     *  for, and not one no row reaches. */
    @Test
    void aPointEveryRowOfWhichAbortsIsNoWitnessAndNotUnreachable() {
        Generator.BoundaryAttempt attempt = attemptOver(TWO, "g", Count.of(100),
                (parameter, candidate) -> new Generator.CandidateCheck.Built.Value(reqWith(100)),
                running(_ -> false, new ArrayList<>()));

        Generator.BoundaryAttempt.Unresolved no = assertInstanceOf(
                Generator.BoundaryAttempt.Unresolved.class, attempt);
        assertEquals(Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS,
                no.why().reason());
    }
}
