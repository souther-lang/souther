package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ClauseName;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.Figure;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A way whose conditions some input brings out, and every such input of which a construction on
 * the way refuses, is a way every run of which stops there — and not a way no input takes. Only a
 * way whose own conditions leave no input is that, whatever it goes through.
 *
 * <p>The check of a body refuses a construction its invariant fails wherever it is built (E2010),
 * and every model written so far that would put such a way in a body is refused there. The reading
 * is asked here at its owner instead: the body of a model the check accepts, read under the rules of
 * declarations of the same names whose invariants the way's conditions contradict. What the reading
 * is held to is what it makes of a way and a construction, which is the same whichever model the
 * rules came from.
 */
class AWayEveryRunOfWhichStopsIsNotAWayNoInputTakesTest {

    /** The model the bodies are read off, each construction one its invariants admit. */
    private static final String BODIES = """
            module demo

            data Positive = { n: Int }
                invariant n >= 1

            data Small = { n: Int }
                invariant n <= 1000

            data No

            behavior one : (n: Int) -> Positive | No
                constructs Positive
            let one (n) = if n > 5 then Positive { n = n } else No

            behavior two : (n: Int) -> Small | No
                constructs Positive, Small
            let two (n) = if n > 5 then {
                let p = Positive { n = n }
                Small { n = p.n }
            } else No

            data Bounded = { n: Int }
                invariant positive = n >= 1
                invariant small = n <= 1000

            behavior three : (n: Int) -> Bounded | No
                constructs Bounded
            let three (n) = if n > 5 && n < 100 then Bounded { n = n } else No
            """;

    /** The same declarations, the first held to what no number past five is, and the first clause
     *  of the third. */
    private static final String RULES = """
            module demo

            data Positive = { n: Int }
                invariant n < 0

            data Small = { n: Int }
                invariant n <= 1000

            data No

            data Bounded = { n: Int }
                invariant positive = n < 0
                invariant small = n <= 1000
            """;

    /** A figure of conditions taken in that the proof of `two`'s way through both its
     *  constructions fits in and the proof without the second does not. */
    private static final int SPENT_AT = 8;

    /** The review's model: a construction every run fails, refused by the check of the body. */
    @Test
    void aConstructionEveryRunFailsIsRefusedByTheCheckOfTheBody() {
        Compilation compilation = Compilation.ofSource("""
                module broken

                data Positive = { n: Int }
                    invariant n >= 1

                behavior wrap : (n: Int) -> Positive
                    constructs Positive
                let wrap (n) = Positive { n = 0 }
                """, "Main");
        compilation.db().ask(new Bodies.Checked("broken"));

        assertEquals(List.of("E2010"), compilation.errors().stream()
                .map(said -> said.diagnostic().code().toString()).toList());
    }

    @Test
    void aWayEveryInputOfWhichAConstructionRefusesStopsThere() {
        Compilation bodies = Compilation.ofSource(BODIES, "Main");
        DecisionReading read = readUnderTheOtherRules(bodies, "one");

        assertEquals(List.of(), read.impossible(), "some input brings `n > 5` out true");
        assertEquals(1, read.everyRunStops().size(), () -> "the way into the construction: "
                + read.everyRunStops());
        assertEquals(List.of(lineOf("Positive { n = n }", 0)),
                lines(bodies, read.everyRunStops().getFirst()));
        assertEquals(1, read.found().size(), () -> "and the way past `else` is a rule: "
                + read.found());
    }

    /** Of two constructions on the way, the one its inputs get past is not said. */
    @Test
    void ofTwoConstructionsOnAWayOnlyTheOneEveryRunStopsAtIsNamed() {
        Compilation bodies = Compilation.ofSource(BODIES, "Main");
        DecisionReading read = readUnderTheOtherRules(bodies, "two");

        assertEquals(1, read.everyRunStops().size(), () -> "one way: " + read.everyRunStops());
        assertEquals(List.of(lineOf("Positive { n = n }", 1)),
                lines(bodies, read.everyRunStops().getFirst()));
    }

    /** Of two clauses of one construction, only the one the way's inputs break is named: the
     *  other holds of every one of them. */
    @Test
    void ofTwoClausesOfAConstructionOnlyTheOneTheWayBreaksIsNamed() {
        Compilation bodies = Compilation.ofSource(BODIES, "Main");
        DecisionReading read = readUnderTheOtherRules(bodies, "three");

        assertEquals(1, read.everyRunStops().size(), () -> "one way: " + read.everyRunStops());
        DecisionReading.EveryRunStops way = read.everyRunStops().getFirst();
        assertEquals(List.of(Optional.of("positive")), way.stoppedAt().stream()
                .map(each -> assertInstanceOf(ClauseOfAConstruction.Held.class, each.clause())
                        .clause().name().map(ClauseName::value)).toList());
        assertEquals(List.of(lineOf("Bounded { n = n }", 0)), lines(bodies, way));
    }

    /** A way whose conditions clash goes through a construction, and it is a way no input takes:
     *  the least proof is had without the construction. */
    @Test
    void aWayWhoseConditionsClashIsOneNoInputTakesWhateverItGoesThrough() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Positive = { n: Int }
                    invariant n >= 1

                data No

                behavior c : (n: Int) -> Positive | No
                    constructs Positive
                let c (n) = if n < 0 && n > 0 then Positive { n = n } else No
                """, "Main");
        DecisionReading read = readingOf(compilation, RuleReadings.of(compilation, "demo"), "c");

        assertEquals(List.of(), read.everyRunStops());
        assertEquals(1, read.impossible().size(), () -> "the one way: " + read.impossible());
        assertEquals(List.of(), read.impossible().getFirst().way().passed(),
                "proved of the conditions alone");
    }

    /**
     * A way whose proof without one of its constructions the figure of conditions taken in left
     * unanswered is neither of the two: the reading does not know whether some input brings the
     * way's conditions out, so it is said with the figure and the constructions still in the
     * proof, and never as a way no input takes.
     */
    @Test
    void aWayWhoseSmallerProofTheFigureLeftUnansweredIsUndecided() {
        Compilation bodies = Compilation.ofSource(BODIES, "Main");
        Allowances allowing = Allowances.DECLARED
                .with(CompositionBudget.CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE, SPENT_AT);
        DecisionReading read = allowing.over(() -> readUnderTheOtherRules(bodies, "two"));

        assertEquals(List.of(), read.impossible(), "not a way no input takes");
        assertEquals(List.of(), read.everyRunStops(), "nor one every run of which stops");
        assertEquals(1, read.undecided().size(), () -> "the way into the construction: "
                + read.excluded());
        DecisionReading.UndecidedAtAFigure way = read.undecided().getFirst();
        assertEquals(new Figure.Budget(CompositionBudget.CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE,
                SPENT_AT), way.figure());
        assertEquals(List.of(lineOf("Positive { n = n }", 1), lineOf("Small { n = p.n }", 0)),
                way.stoppedAt().stream()
                        .map(each -> bodies.texts().resolve(each.at()).line()).toList());
        assertEquals(1, read.found().size(), () -> "and the way past `else` is a rule: "
                + read.found());
    }

    /**
     * A construction whose invariant was not reached states only that it was not read, which
     * proves no contradiction, so a least proof keeping it and nothing else is no proof that every
     * run along the way stops there.
     */
    @Test
    void aWayWhoseProofKeepsOnlyAnInvariantNotReachedIsNotOneEveryRunOfWhichStops() {
        DecisionReading.Ruled way = new DecisionReading.Ruled(new DecisionRule(Map.of()),
                List.of(), true, List.of(new PassedConstruction(List.of(), null,
                        new ClauseOfAConstruction.NotReached())));
        NoInputTakesIt why = new NoInputTakesIt.TheConditionsClash(
                new NoInputTakesIt.Clash.TwoAtOnce(
                        new Reachability.TwoAtOnce.Counts(TermPath.of("xs"))));

        assertThrows(IllegalArgumentException.class,
                () -> new DecisionReading.EveryRunStops(way, why));
    }

    /** The body of {@code behavior} of {@link #BODIES}, read under the rules of {@link #RULES}. */
    private static DecisionReading readUnderTheOtherRules(Compilation bodies, String behavior) {
        Compilation rules = Compilation.ofSource(RULES, "Main");
        return readingOf(bodies, RuleReadings.of(rules, "demo"), behavior);
    }

    /** The line of {@link #BODIES} the {@code nth} {@code text} in it is on, from one. */
    private static int lineOf(String text, int nth) {
        int at = -1;
        for (int i = 0; i <= nth; i++) {
            at = BODIES.indexOf(text, at + 1);
        }
        return (int) BODIES.substring(0, at).chars().filter(c -> c == '\n').count() + 1;
    }

    private static DecisionReading readingOf(Compilation compilation, RuleReadingSource rules,
                                             String behavior) {
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertEquals(List.of(), compilation.errors(), "the model the bodies are read off compiles");
        assertNotNull(checked, "and its bodies were checked");
        Map<String, InputDomain> inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value();
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        InputDomain domain = inputs.get(behavior);
        return DecisionReading.of(behavior, analysis, domain.reading(rules),
                InputReads.ofParametersWhereCallsStand(domain.parameterReads(),
                        domain.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                        domain.dependencies()));
    }

    /** The line each construction every run along {@code way} stops at is written on. */
    private static List<Integer> lines(Compilation bodies, DecisionReading.EveryRunStops way) {
        return way.stoppedAt().stream().map(each -> bodies.texts().resolve(each.at()).line())
                .toList();
    }
}
