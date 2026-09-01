package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A measure of a module that answered answers for every behavior the module declares.
 *
 * <p>Whether a query answers at all is the query's own business: a compile that never reached what
 * it reads has nothing to say, and says so by being absent. What it may not do is answer and leave
 * a behavior out. A key that is sometimes there carries part of the answer, and the readers of
 * these maps read a missing one three ways — a composition with no subject, a compile that did not
 * get that far, and this compiler disagreeing with itself. Two of those are wrong about a behavior
 * whose boundary did not work out, and the third stopped the report on it.
 *
 * <p>Held over every measure of a behavior and not over the one the report crashed on. Two of the
 * four were total already and by two different arrangements — the reading of the rows through a
 * total accessor, the arms through a loop with no way out of it — and the other two each dropped
 * the key. One of them crashed and one went quiet, which is the same defect and one report.
 */
class AnAnsweredMeasureAnswersForEveryBehaviorTest {

    /**
     * A module with a behavior of every shape this has words for: one measured, a composition
     * measured at its stages, an injected behavior with no body of its own, and one whose
     * declaration rests on a name nothing resolved.
     */
    private static final String EVERY_SHAPE = """
            module example.shapes
            import nothing.here ( Money )

            data A = { n: Int }
            data B = { n: Int }
            data C = { n: Int }

            behavior one : (a: A) -> B
                constructs B
            let one (a) = B { n = a.n }

            behavior two : (b: B) -> C
                constructs C
            let two (b) = C { n = b.n }

            behavior both = one >-> two

            behavior injected : (a: A) -> B

            behavior priced : (m: Money) -> B
                constructs B
            let priced (m) = B { n = 1 }
            """;

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(EVERY_SHAPE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static List<String> declared(Compilation compilation) {
        Prepared prepared = compilation.db().ask(new Shapes.Prepared("example.shapes")).value();
        assertNotNull(prepared, "the declarations were read");
        return prepared.behaviors().stream().map(Hir.BehaviorDef::name).toList();
    }

    /** Every measure of a behavior, under the name the report knows it by. */
    private static Map<String, Map<String, ?>> measures(Compilation compilation) {
        return Map.of(
                "witnesses", compilation.db().ask(new Adequacy.Witnesses("example.shapes")).value(),
                "coverage", compilation.db().ask(new Adequacy.Coverage("example.shapes")).value(),
                "branch", compilation.db().ask(new Adequacy.BranchCoverage("example.shapes"))
                        .value());
    }

    /**
     * The key set is the behaviors, in the order they are declared, and every answer is one.
     *
     * <p>An equality and not a containment. A measure that answered for something the module does
     * not declare is as wrong as one that left a behavior out, and only one of the two is what
     * anybody was looking for when this was written.
     */
    @Test
    void everyMeasureAnswersForEveryBehaviorAndNothingElse() {
        Compilation compilation = measured();
        List<String> behaviors = declared(compilation);
        measures(compilation).forEach((measure, answered) -> {
            assertNotNull(answered, () -> measure + " answered");
            assertEquals(behaviors, List.copyOf(answered.keySet()),
                    () -> measure + " answers for the behaviors the module declares");
            answered.forEach((behavior, evidence) ->
                    assertNotNull(evidence, () -> measure + " of " + behavior));
        });
    }

    /**
     * And the reading of the rows, which is total by an accessor rather than by a key set.
     *
     * <p>Asked of the thing that answers it. The reading is kept under whatever wrote a row, so its
     * map is not keyed by the behaviors at all and an equality over its keys would be a rule about
     * a different set. What it owes is an answer per behavior, and that is what is held here.
     */
    @Test
    void theReadingOfTheRowsAnswersForEveryBehaviorToo() {
        Compilation compilation = measured();
        Map<String, Adequacy.RowReading> rows =
                compilation.db().ask(new Adequacy.RowReadings("example.shapes")).value();
        assertNotNull(rows, "the rows were read for or against");
        for (String behavior : declared(compilation)) {
            assertNotNull(Adequacy.RowReadings.readingFor(rows, behavior),
                    () -> "how far the rows of " + behavior + " were read");
        }
    }

    /**
     * The producer has nowhere to drop one.
     *
     * <p>The loop is the helper's and the caller writes what one behavior comes to, so a caller
     * that has nothing to say has to say that rather than return. What that used to be written as
     * is a {@code continue}, and there is no longer a loop to write it in.
     */
    @Test
    void aMapperThatAnswersNothingIsRefused() {
        Prepared prepared =
                measured().db().ask(new Shapes.Prepared("example.shapes")).value();
        assertThrows(NullPointerException.class,
                () -> Adequacy.answerEveryBehavior(prepared,
                        behavior -> behavior.name().equals("one") ? null : behavior.name()),
                "a behavior with no answer is not a behavior to leave out");
    }
}
