package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.observe.WorkFigure;
import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.Budgets;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.regex.PatternPlan;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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

        assertEquals(new ReplacementEvidence.Undecided.Way.AtFigures(
                        ReplacementEvidence.Undecided.Why.RUNS_SPENT,
                        List.of(WorkFigure.RUNS_REPLACING_AN_ARM.at(1))), spent,
                "the runs it was allowed, as they stood on this run");
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

        ReplacementEvidence.Undecided.Way.AtFigures named = assertInstanceOf(
                ReplacementEvidence.Undecided.Way.AtFigures.class, reached,
                "a figure of the composing's own stopped it, and it is carried");
        assertTrue(named.figures().contains(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS),
                () -> "what a proposed collection holds is what stopped it: " + named.figures());
        assertEquals(RunSensitivity.MAY_CHANGE, named.runSensitivity());
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
