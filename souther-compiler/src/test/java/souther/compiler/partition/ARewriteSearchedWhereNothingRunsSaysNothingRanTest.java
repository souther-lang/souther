package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowRef;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Shapes;
import souther.compiler.reading.CoverageRead;
import souther.compiler.source.SourceId;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A rewrite looked for where nothing can run a row is said to be one nothing ran, however the way
 * of running rows it was handed is wrapped.
 *
 * <p>Nothing running a row is a fact about where the search is, and not a search that came to
 * nothing: a reader of an undecided rewrite told that no row answered differently would go looking
 * for a row that nothing here could have run.
 */
class ARewriteSearchedWhereNothingRunsSaysNothingRanTest {

    private static final String DOUBLED = """
            module example.doubled

            data Points = Int

            behavior doubled : (earned: Points) -> Points

            let doubled (earned) = Points(earned.value * 2)
            """;

    @Test
    void aWayToRunRowsThatRunsNothingSaysNothingRan() {
        assertEquals(new ReplacementDisposition.NoneFound(
                        ReplacementDisposition.Ended.NOTHING_RAN),
                searchedWith(Generator.Trial.NOTHING_RUNS));
    }

    @Test
    void andSoDoesOneThatRunsEachRowOnceOverNothing() {
        assertEquals(new ReplacementDisposition.NoneFound(
                        ReplacementDisposition.Ended.NOTHING_RAN),
                searchedWith(Generator.once(Generator.Trial.NOTHING_RUNS)));
    }

    /** What looking for a row the body answering zero always is told apart on came to. */
    private static ReplacementDisposition searchedWith(Generator.Trial trial) {
        Compilation compilation = Compilation.ofSource(DOUBLED, "Main");
        String module = compilation.modules().getFirst();
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(prepared);
        assertNotNull(checked);
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("doubled")).findFirst().orElseThrow();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value()
                .get("doubled");
        assertNotNull(inputs, "the behavior's inputs were read");
        Core body = checked.behaviorBodies().get("doubled");
        assertNotNull(body, "the behavior under test has a body");
        MeasuredInput subject = MeasuredInput.of(spec.name(), inputs.reading(rules),
                Partitions.of(spec.name(), inputs.reading(rules), ReadAs.THE_COMPILATION_DOES));
        CoverageRead.Read read = CoverageRead.of(spec.name(), checked.run(spec.name()),
                inputs.reading(rules));
        ReplacementOwed owed = new ReplacementOwed.ByOneAnswer(new Replacement.ByOneAnswer(
                new ObservedValue.Integer(0),
                new RowRef("doubled", new SourceId("m.sou"), new RowIdentity.Unnamed(1))));
        FillResult filled = Generator.fill(GenerationPlan.of(subject, List.of(), List.of(),
                        List.of(), List.of(), List.of(owed),
                        new RewriteSearch(RewriteSearch.For.THE_MEASURE, 8)),
                List.of(), Generator.CandidateCheck.ANY, read, trial, List.of(),
                AnswersStoodIn.REQUIRING_NOTHING, HeldOutcome.Of.NOTHING,
                WhereNothingIsAnswered.of(subject.behavior(), read, subject.axes()),
                Budgets.generation());
        return filled.discharge().at(owed);
    }
}
