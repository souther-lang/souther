package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.coverage.AlignedObservation;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.Observation;
import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.Generator;
import souther.compiler.partition.ObservedInputs;
import souther.compiler.partition.RulesTaken;
import souther.compiler.partition.RunPlacement;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A Bool input passed straight to a field of what a body answers is a condition of the rule, and a
 * row is seen taking it by the value the row wrote.
 *
 * <p>No construct of the model answers such a truth, so no run is recorded at it. The rows are the
 * only account there is of which way it came out, and a rule through it is placed from them rather
 * than left out of every reading of the run. A value is evidence only of a run that answered: a row
 * stopped before the behavior was applied has the same values and its account is of the fixtures.
 */
class ABoolPassedStraightToAFieldIsReadOffTheRowTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String BODY = """
            module ql4

            data Q = { flag: Bool }
            data Below = { n: Int }

            behavior qual : (rawScore: Int, flag: Bool) -> Q | Below
                constructs Q, Below
            let qual (rawScore, flag) = {
                guard rawScore >= 60 else Below { n = 0 }
                Q { flag = flag }
            }

            example qual
            """;

    /** A body whose every rule is a Bool input and nothing else. */
    private static final String ECHO = """
            module echo

            data Q = { flag: Bool }

            behavior echo : (flag: Bool) -> Q
            let echo (flag) = Q { flag = flag }

            example echo
                | "yes" : (true) -> Q { flag = true }
            """;

    private static final String SIXTY_TRUE = "    | \"sixty\" : (60, true) -> Q { flag = true }\n";
    private static final String SIXTY_FALSE =
            "    | \"sixty-false\" : (60, false) -> Q { flag = false }\n";
    private static final String FIFTY_NINE_TRUE =
            "    | \"fifty-nine\" : (59, true) -> Below { n = 0 }\n";
    private static final String FIFTY_NINE_FALSE =
            "    | \"fifty-nine-false\" : (59, false) -> Below { n = 0 }\n";

    @Test
    void theRowsOfTheReportedModelAreEachPlacedAndTheUntakenRuleIsLeftUntaken() {
        DecisionEvidence.RowsPlaced read = readOf(SIXTY_TRUE + FIFTY_NINE_TRUE);
        assertEquals(2, read.rowsPlaced(), () -> "both rows took a rule: " + read);
        assertEquals(0, read.rowsNotPlaced(), () -> "and none went unplaced: " + read);
        assertEquals(2, read.rules().size(),
                () -> "two of the three rules, not the one with flag false: " + read);
    }

    @Test
    void aRowWithTheFlagFalseTakesTheRuleTheFlagTrueRowDoesNot() {
        DecisionEvidence.RowsPlaced read =
                readOf(SIXTY_TRUE + SIXTY_FALSE + FIFTY_NINE_TRUE);
        assertEquals(3, read.rowsPlaced(), () -> "every row took a rule: " + read);
        assertEquals(3, read.rules().size(), () -> "and each took a different one: " + read);
    }

    @Test
    void aRowThatStopsAtTheGuardTakesNoRuleOfTheFlag() {
        DecisionEvidence.RowsPlaced read = readOf(FIFTY_NINE_FALSE);
        assertEquals(1, read.rowsPlaced(), () -> "the row took a rule: " + read);
        assertEquals(1, read.rules().size(),
                () -> "the one the guard decides, whatever the flag was: " + read);
        assertTrue(read.everyRowWasWatched(), () -> "and it was watched: " + read);
    }

    /** What the report said of the reported model, which is what the issue is about. */
    @Test
    void theReportNoLongerSaysTheRowsCouldNotBeRead() {
        Compilation measured = measured(BODY + SIXTY_TRUE + FIFTY_NINE_TRUE);
        JsonNode document = JSON.readTree(AdequacyReport.of(measured)
                .json(SourceRendering.namedByIdentity(measured.texts())));
        JsonNode decision = document.get("modules").get(0).get("behaviors").get(0).get("decision");
        List<String> said = new ArrayList<>();
        JsonNode coverage = decision.get("coverage");
        if (coverage.has("weakening")) {
            coverage.get("weakening").forEach(each -> said.add(each.asString()));
        }
        assertFalse(said.contains("decision_of_row_unreadable"),
                () -> "every row was placed, so none was unreadable: " + decision);
    }

    /**
     * The values of a row that never applied the behavior are not evidence of a rule.
     *
     * <p>The account of such a row is of the fixtures it built, and it is an account all the same;
     * the flag it was given is the one it would have passed on had it got that far.
     */
    @Test
    void aRowThatDidNotAnswerTakesNoRuleByItsValues() {
        Compilation compilation = measured(ECHO);
        RunPlacement placing = placementOf(compilation);
        Generator.Watched.Ran account = new Generator.Watched.Ran(nothingSeen(compilation));
        List<ObservedValue> flag = List.of(new ObservedValue.Bool(true));

        assertEquals(new RulesTaken.WhichRule.CouldNotTell(
                        RulesTaken.WhichRule.Why.NO_RECOGNISABLE_RULE_MATCHES),
                placing.takenBy(new ObservedInputs(flag, account,
                        new AnswerObservation.NotAnswered())),
                "the fixtures were built and the behavior was not applied");
        assertEquals(new RulesTaken.WhichRule.CouldNotTell(
                        RulesTaken.WhichRule.Why.NO_RECOGNISABLE_RULE_MATCHES),
                placing.takenBy(new ObservedInputs(flag, account,
                        new AnswerObservation.RanOut())),
                "and a run that spent its budget went down no whole path");
        assertInstanceOf(RulesTaken.WhichRule.TookThis.class,
                placing.takenBy(new ObservedInputs(flag, account,
                        new AnswerObservation.Answered(new ObservedValue.Bool(true)))),
                "the control: the same values and account, answered");
    }

    private static DecisionEvidence.RowsPlaced readOf(String rows) {
        Compilation compilation = measured(BODY + rows);
        DecisionEvidence evidence = compilation.db()
                .ask(new Adequacy.Decides(compilation.modules().get(0))).value().get("qual");
        return evidence.took().made()
                .orElseThrow(() -> new AssertionError("the rows were read: " + evidence.took()));
    }

    private static RunPlacement placementOf(Compilation compilation) {
        String module = compilation.modules().get(0);
        DecisionEvidence evidence =
                compilation.db().ask(new Adequacy.Decides(module)).value().get("echo");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        return new RunPlacement(
                RulesTaken.of(evidence.read(), checked.behaviorBodies().get("echo"),
                        checked.plan()),
                InputsOfTheBody.of(compilation, "echo"));
    }

    private static AlignedObservation nothingSeen(
            Compilation compilation) {
        CoverageSites.Plan plan = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value().plan();
        return plan.numbering().align(
                new Observation(plan.numbering().identity(), Set.of(), Set.of()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
