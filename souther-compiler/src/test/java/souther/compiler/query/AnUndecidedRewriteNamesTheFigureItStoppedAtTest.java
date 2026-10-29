package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.execute.EvaluationPolicy;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.observe.WorkFigure;
import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.Budgets;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.regex.PatternPlan;
import souther.compiler.report.AdequacyReport;

import java.time.Duration;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rewrite a search was stopped from deciding names the figure that stopped it, carried from the
 * place the search was compared against it.
 *
 * <p>Two places, each read off a run of the compiler rather than a value made here: the runs one
 * rewrite may take, which a policy hands the run, and the composing's own figures, which are
 * fixed.
 */
class AnUndecidedRewriteNamesTheFigureItStoppedAtTest {

    /** An arm whose one row answers as its sibling would, so the rewrite is searched for a row. */
    private static final String AN_ARM_ITS_ROW_DOES_NOT_TELL = """
            module example.runs

            data Ok = { big: Bool }

            behavior f : (x: Int) -> Ok
                constructs Ok

            let f (x) = if x > 0 then Ok { big = x > 1000 } else Ok { big = false }

            example f
                | (5) -> Ok { big = false }
            """;

    /**
     * A search allowed one run spends it on the body and has none for the rewrite: the way it was
     * left open names how many runs a rewrite may take, at the number this run was handed.
     */
    @Test
    void aSearchOutOfRunsNamesTheRunsItWasAllowed() {
        ReplacementEvidence.Undecided.Way spent = wayOf(
                undecided(compiled(List.of(AN_ARM_ITS_ROW_DOES_NOT_TELL), 1)),
                ReplacementEvidence.Undecided.Why.RUNS_SPENT);

        assertEquals(ReplacementEvidence.Undecided.Way.atFigures(
                        ReplacementEvidence.Undecided.Why.RUNS_SPENT,
                        List.of(WorkFigure.RUNS_REPLACING_AN_ARM.at(1))), spent,
                "the runs it was allowed, as they stood on this run");
    }

    /**
     * The line a reader gets for a rewrite left open at a figure says that a row telling it apart
     * may exist past the figure: nothing was proven about a region the search did not look in.
     */
    @Test
    void theLineForARewriteStoppedAtAFigureSaysARowMayExistPastIt() {
        Compilation compilation = compiled(List.of("""
                module example.throws

                data Throw = List<Int>

                behavior score : (throws: List<Throw>) -> Int

                let score (throws) =
                    List.fold((acc, t) -> acc + List.length(t.value), 0, throws)

                example score
                    | ([]) -> 0
                    | ([Throw([])]) -> 0
                    | ([Throw([12])]) -> 1
                    | ([Throw([1, 2])]) -> 2
                    | ([Throw([1, 2, 3])]) -> 3
                    | ([Throw([5, 8])]) -> 2
                """), 1);

        String page = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));

        assertTrue(page.contains("a row that tells the rewrite apart may exist past it"), page);
    }

    /**
     * A search with runs to spare, cut short by a bound a search for a row holds itself to: four
     * positions of four cases each are more candidates than a walk repairing a row builds, and that
     * is named at the number written where the walk compared against it. Nothing the body answers
     * tells the rewrite apart, so the walk runs to the bound.
     */
    @Test
    void aSearchCutShortByItsOwnBoundNamesTheBound() {
        ReplacementEvidence.Undecided.Way reached = wayOf(
                undecided(compiled(List.of("""
                        module example.runs

                        data Ok = { odd: Bool }
                        data P
                        data Q
                        data R
                        data S
                        data C = P | Q | R | S

                        behavior f : (a: C, b: C, c: C, d: C, x: Int) -> Ok
                            constructs Ok

                        let f (a, b, c, d, x) = Ok { odd = x * x == 2 }

                        example f
                            | (P, P, P, P, 5) -> Ok { odd = false }
                        """), Budgets.measures().rewriteRuns())),
                ReplacementEvidence.Undecided.Why.A_COMPOSING_FIGURE_REACHED);

        assertEquals(ReplacementEvidence.Undecided.Way.atFigures(
                        ReplacementEvidence.Undecided.Why.A_COMPOSING_FIGURE_REACHED,
                        List.of(WorkFigure.CANDIDATES_A_REPAIR_BUILDS.at(64))), reached);
    }

    /**
     * A body asking whether a list holds more than this compiler composes for one: composing stops
     * at what a proposed collection holds, and that is the figure named.
     */
    @Test
    void aSearchWhoseComposingStoppedNamesTheComposingsFigure() {
        ReplacementEvidence.Undecided.Way reached = wayOf(undecided(compiled(List.of("""
                module example.many

                data Ok = { many: Bool }

                behavior f : (xs: List<Int>) -> Ok
                    constructs Ok

                let f (xs) = Ok { many = List.length(xs) >= 1000 }

                example f
                    | ([]) -> Ok { many = false }
                    | ([1, 2]) -> Ok { many = false }
                """), Budgets.measures().rewriteRuns())),
                ReplacementEvidence.Undecided.Why.A_COMPOSING_FIGURE_REACHED);

        assertTrue(reached.figures().contains(
                        CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS.figure()),
                () -> "what a proposed collection holds is what stopped it: " + reached.figures());
        assertEquals(RunSensitivity.MAY_CHANGE, reached.runSensitivity());
    }

    /**
     * A rewrite under which the row's run goes round until it has spent its steps: the run did not
     * come back, and the way it was left open names the steps a run may take, at the number this
     * run held it to.
     */
    @Test
    void aRunThatSpentItsStepsNamesTheSteps() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module example.loops
                data N = Int
                data Out = Int
                partial let spin (n: Int): Int = if n == 0 then 0 else spin(n - 1)
                behavior f : (n: N) -> Out constructs Out
                let f (n) = if n.value > 0 then Out(spin(n.value)) else Out(0)
                example f
                  | "below nought": (N(-2)) -> Out(0)
                """), ModulePath.EMPTY)
                .withEvaluationPolicy(EvaluationPolicy.of(100_000)
                        .withCompilerTimeout(Duration.ofSeconds(30)));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        ReplacementEvidence its = compilation.db()
                .ask(new Replacements.Measured(compilation.modules().getFirst())).value()
                .get("f");

        List<ReplacementEvidence.Undecided.Way> notBack = its.measured().made()
                .orElseThrow(() -> new AssertionError("the rewrites were measured: " + its))
                .rewrites().stream()
                .map(ReplacementEvidence.Rewrite::outcome)
                .filter(ReplacementEvidence.Undecided.class::isInstance)
                .map(ReplacementEvidence.Undecided.class::cast)
                .flatMap(each -> each.why().ways().stream())
                .filter(each -> each.why()
                        == ReplacementEvidence.Undecided.Why.A_RUN_DID_NOT_COME_BACK)
                .toList();
        assertEquals(List.of(ReplacementEvidence.Undecided.Way.atFigures(
                        ReplacementEvidence.Undecided.Why.A_RUN_DID_NOT_COME_BACK,
                        List.of(WorkFigure.EVALUATION_STEPS.at(100_000)))), notBack,
                () -> "the rewrite that loops names the steps it spent: " + its);
    }

    private static ReplacementEvidence.Undecided.Way wayOf(ReplacementEvidence.Undecided open,
                                                         ReplacementEvidence.Undecided.Why why) {
        return open.why().ways().stream().filter(each -> each.why() == why).findFirst()
                .orElseThrow(() -> new AssertionError(why + " is among the ways: " + open));
    }

    /** The one rewrite left undecided, of the one behavior. */
    private static ReplacementEvidence.Undecided undecided(Compilation compilation) {
        ReplacementEvidence its = compilation.db()
                .ask(new Replacements.Measured(compilation.modules().getFirst())).value()
                .get("f");
        List<ReplacementEvidence.Undecided> open = its.measured().made()
                .orElseThrow(() -> new AssertionError("the rewrites were measured: " + its))
                .rewrites().stream()
                .map(ReplacementEvidence.Rewrite::outcome)
                .filter(ReplacementEvidence.Undecided.class::isInstance)
                .map(ReplacementEvidence.Undecided.class::cast)
                .toList();
        assertEquals(1, open.size(), () -> "one rewrite left open: " + its);
        return open.getFirst();
    }

    private static Compilation compiled(List<String> sources, int rewriteRuns) {
        Compilation compilation = Compilation.ofSources(sources, ModulePath.EMPTY)
                .withAdequacyPolicy(new AdequacyPolicy(
                        new AdequacyPolicy.OfTheMeasures(Budgets.measures().pairSpace(),
                                Budgets.measures().cellsPerGroup(),
                                PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS, rewriteRuns),
                        Budgets.generation()));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
