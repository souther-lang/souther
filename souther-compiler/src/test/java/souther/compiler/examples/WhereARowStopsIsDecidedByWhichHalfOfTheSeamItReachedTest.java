package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.msg.ExampleMessage;
import souther.compiler.observe.Applied;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What applies a behavior is asked in two steps, and which of them a row got through is what its
 * outcome says about it.
 *
 * <p>Making a stand-in into something the behavior can be constructed with is building the environment
 * the behavior runs in. A row that could not get one never entered the behavior, and says so: it stops
 * where a row whose dependency has nothing standing in for it stops, and nothing applied it. A row
 * that did get one and then met a failure entered the behavior, and says that instead.
 *
 * <p>Held here because the two steps are what keeps that true. Asked as one call, a stand-in that could
 * not be made would be found after the row had already been recorded as having entered the behavior,
 * and every reader of the outcome would be told a row ran that never did.
 */
class WhereARowStopsIsDecidedByWhichHalfOfTheSeamItReachedTest {

    private static final String MODEL = """
            module example.twohalves

            data 会員ID = String
            data 見つかった = { id: 会員ID }
            data 見つからない = { なぜ: String }

            data 注文 = { by: 会員ID }
            data 受理 = { by: 会員ID }
            data 拒否 = { なぜ: String }

            behavior 会員を探す : (id: 会員ID) -> 見つかった | 見つからない

            behavior 受け付ける : (注文: 注文) -> 受理 | 拒否
                depends on 会員を探す
                constructs 受理, 拒否

            let 受け付ける (注文, 会員を探す) = match 会員を探す(注文.by) with
                | 見つかった  -> 受理 { by = 注文.by }
                | 見つからない -> 拒否 { なぜ = "unknown" }

            fake 会員を探す
              | (会員ID("m-1")) -> 見つかった { id = 会員ID("m-1") }

            example 受け付ける
              | "a member that is known" : (注文 { by = 会員ID("m-1") }) -> 受理 { by = 会員ID("m-1") }
            """;

    /** The row states a stand-in, and it could not be made. Nothing was applied. */
    @Test
    void aStandinThatCouldNotBeMadeStopsTheRowBeforeItEntersTheBehavior() {
        ExampleVerifier.Observations observed = evaluated(new Refusing());

        RowOutcome row = only(observed);
        assertEquals(Stage.FIXTURES_VALIDATED, row.stage(),
                "the fixtures were validated and the behavior was never entered");
        assertEquals(Disposition.FAILED, row.disposition());
        assertEquals(FailurePhase.FAKE_RESOLUTION, row.failurePhase(),
                "the same place a row whose dependency has no fake stops");
        assertInstanceOf(Applied.Nothing.class, row.run().applied(),
                "a row that did not enter the behavior says nothing applied it");
        assertEquals(1, observed.failures().size());
        ExampleMessage.TheFakeCouldNotBeBuilt said = assertInstanceOf(
                ExampleMessage.TheFakeCouldNotBeBuilt.class, observed.failures().get(0).said(),
                "said as a fake that could not be built, where the fake is written");
        assertEquals("会員を探す", said.dependency(), "naming the dependency it stood in for");
        assertTrue(said.why().contains("said by the test"),
                "and carrying the answerer's reason rather than one made up here");
    }

    /** The stand-in was made, and the behavior it was made for failed. The row entered it. */
    @Test
    void aFailureFromTheBehaviorStopsTheRowInsideIt() {
        ExampleVerifier.Observations observed = evaluated(new Failing());

        RowOutcome row = only(observed);
        assertEquals(Stage.INVOKED, row.stage(), "the behavior was entered");
        assertEquals(Disposition.FAILED, row.disposition());
        assertEquals(FailurePhase.INVOCATION, row.failurePhase());
        assertInstanceOf(Applied.GeneratedHere.class, row.run().applied(),
                "and what entered it is on the record");
    }

    /**
     * The implementation could not be reached, so nothing applied the row.
     *
     * <p>The other half of the same invariant. A row is marked as having entered the behavior before
     * the answerer is asked, because that is the one thing a reader of a row that never comes back
     * can be given; an answerer that comes back saying it never got in takes the mark with it.
     */
    @Test
    void anImplementationThatCouldNotBeReachedLeavesTheRowHavingAppliedNothing() {
        ExampleVerifier.Observations observed = evaluated(new Unreachable());

        RowOutcome row = only(observed);
        assertEquals(Stage.FIXTURES_VALIDATED, row.stage(), "it never got in");
        assertInstanceOf(Applied.Nothing.class, row.run().applied(),
                "so nothing is recorded as having applied it");
        assertEquals(Disposition.FAILED, row.disposition());
        assertEquals(FailurePhase.INVOCATION, row.failurePhase());
        assertEquals(1, observed.failures().size(),
                "and the row is told, in the words it was told while this and the applied code"
                        + " failing arrived as one throw");
    }

    /**
     * The row could not be put in the form the answerer reads, so it is undecided.
     *
     * <p>What {@link Handed#neutral} raises, let out by the answerer as the contract says. Nothing
     * about the row was established, so no diagnostic is said about a model that may be right — and
     * it does not take the module's evaluation down with it, which is what it did while nothing
     * caught it.
     */
    @Test
    void aRowThatCouldNotBeHandedOverIsUndecidedRatherThanFailed() {
        ExampleVerifier.Observations observed = evaluated(new Uncrossable());

        RowOutcome row = only(observed);
        assertEquals(Stage.FIXTURES_VALIDATED, row.stage(), "it was never handed over");
        assertEquals(Disposition.INCOMPLETE, row.disposition(),
                "so nothing about it was established");
        assertEquals(FailurePhase.INFRASTRUCTURE, row.failurePhase());
        assertInstanceOf(Applied.Nothing.class, row.run().applied());
        assertEquals(List.of(), observed.failures(),
                "and nothing is said about the model, which may be right");
        assertEquals(1, observed.incompleteness().size(),
                "the row is reported as one that could not be decided");
    }

    /** A stand-in the answerer will not make. What it could not make is the whole of what it says. */
    private static final class Refusing implements Answerer {

        @Override
        public Applied applied() {
            return new Applied.GeneratedHere();
        }

        @Override
        public Applying applying(String behavior, List<DependencyStandin> standins) {
            assertEquals(1, standins.size(), "the row does state a stand-in");
            throw new StandinNotBuilt(standins.get(0).dependency(),
                    "its base subclass could not be built: (said by the test)");
        }
    }

    /** A behavior that stops itself. Read the way the applied code stopping itself is always read. */
    private static final class Failing implements Answerer {

        @Override
        public Applied applied() {
            return new Applied.GeneratedHere();
        }

        @Override
        public Applying applying(String behavior, List<DependencyStandin> standins) {
            return _ -> {
                throw new InvocationFailure(new IllegalStateException("it stopped itself"));
            };
        }
    }

    /** An answerer whose implementation is not where it looked. */
    private static final class Unreachable implements Answerer {

        @Override
        public Applied applied() {
            return new Applied.GeneratedHere();
        }

        @Override
        public Applying applying(String behavior, List<DependencyStandin> standins) {
            return _ -> {
                throw new ImplementationNotReached("no class of that name (said by the test)",
                        new ClassNotFoundException(behavior));
            };
        }
    }

    /**
     * An answerer that reads a value it cannot put in its own form.
     *
     * <p>Raises what {@link Handed#neutral} raises rather than reading one, because a row's input is
     * built by this compile's decoders and always readable back. What is being held is what the row
     * does with it, which is the same whichever of the two produced it.
     */
    private static final class Uncrossable implements Answerer {

        @Override
        public Applied applied() {
            return new Applied.GeneratedHere();
        }

        @Override
        public Applying applying(String behavior, List<DependencyStandin> standins) {
            return _ -> {
                throw new FixtureException("`x` is a Nothing, which is not a type this example"
                        + " can read");
            };
        }
    }

    private static RowOutcome only(ExampleVerifier.Observations observed) {
        assertEquals(1, observed.rows().size());
        return observed.rows().get(0);
    }

    /** The row, evaluated the way the query asks it, against an answerer the test chooses. */
    private static ExampleVerifier.Observations evaluated(Answerer answerer) {
        Compilation c = Compilation.ofSource(MODEL, "Main");
        c.db().ask(new Output.All());
        String name = c.modules().get(0);
        Map<String, byte[]> classes = c.db()
                .ask(new Output.EvaluationLinked(name, Output.CoverageMode.NONE)).value();
        return ExampleVerifier.check(
                c.db().ask(new Shapes.Prepared(name)).value().forExamples(),
                c.db().ask(new Shapes.Scope(name)).value(),
                c.db().ask(new Bodies.Signatures(name)).value(),
                classes,
                c.db().ask(new Bodies.Requirements(name)).value(),
                ExampleVerifier.class.getClassLoader(),
                c.db().ask(new Bodies.ModuleDefinitions(name)).value(),
                "Main",
                Deadline.ofMillis(EvaluationPolicy.DEFAULT.outerTimeout().toMillis()),
                EvaluationPolicy.DEFAULT,
                (module, compiled) -> answerer);
    }
}
