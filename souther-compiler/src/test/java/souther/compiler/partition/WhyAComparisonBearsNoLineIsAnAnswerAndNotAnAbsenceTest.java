package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A comparison that bears no line says which of the reasons it is.
 *
 * <p>They are not one answer. A truth nothing reads is one the behavior draws no boundary on at all,
 * and a report that stayed silent about it is right. A comparison one run passes more than once is
 * one the behavior may well draw a boundary on and this cannot show a row to have met: a recording
 * holds that a place was passed and not how many times, so two outcomes of one comparison in one run
 * cannot be told from two rows' outcomes. Folded into one {@code false}, the second becomes silence
 * that reads like the first.
 *
 * <p>What tells the passes apart is a position for what is passed. A step applied once per element
 * of a container the input walk names is passed once per element of that container, and the row's
 * own values there say which pass came out which way — so that one is a line, and it is the same
 * comparison, written the same way, as the one below it whose container the walk names nothing at.
 * The two stand together here because the difference between them is the whole of the reason.
 */
class WhyAComparisonBearsNoLineIsAnAnswerAndNotAnAbsenceTest {

    private static final String MODEL = """
            module example.why
            import List ( filter )

            data Temp = Int

            behavior read : (temp: Temp, xs: List<Int>) -> List<Int>
            let read (temp, xs) = {
                let cold = temp.value < 240
                let unread = temp.value < 100
                let kept = filter(x -> x < 50, xs)
                let fixed = filter(y -> y < 70, [ 1, 2, 3 ])

                if cold then kept else fixed
            }
            """;

    /** What this policy says about the comparison written on {@code line}. */
    private static BoundaryPolicy.Standing standingAt(int line) {
        BoundaryPolicy.Standing said = classified().get(line);
        assertNotNull(said, () -> "the model under test writes a comparison on line " + line);
        return said;
    }

    /** Every comparison of the body, by the line of the source it is written on. */
    private static Map<Integer, BoundaryPolicy.Standing> classified() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get("read");
        assertNotNull(body);
        CoverageSites.Plan plan = CoverageSites.of(checked.behaviorBodies());
        souther.compiler.inputs.InputDomain inputs = compilation.db()
                .ask(new Adequacy.Inputs(module)).value().get("read");

        souther.compiler.check.Symbols symbols =
                souther.compiler.query.Scopes.derived(compilation.db(), module).value();

        Map<Integer, BoundaryPolicy.Standing> byLine = new LinkedHashMap<>();
        for (ComparisonReadings.Reading each
                : ComparisonReadings.of(body, plan,
                        InputReads.of(inputs, checked.elementBindings().get("read")),
                        symbols).all()) {
            byLine.put(each.comparison().pos().line(), each.standing());
        }
        return byLine;
    }

    /** A truth a fork below reads is a line. */
    @Test
    void aTruthSomethingReadsBearsALine() {
        assertEquals(BoundaryPolicy.Standing.DrawsALine.class,
                standingAt(8).getClass());
    }

    /** A truth nothing reads is not a boundary of the behavior at all. */
    @Test
    void aTruthNothingReadsIsNotABoundaryOfTheBehavior() {
        assertEquals(NotABoundary.NOTHING_READS_IT, whyOf(standingAt(9)));
    }

    /** A truth one run reaches once per element of an input bears a line at that element. */
    @Test
    void aTruthReachedOncePerElementOfAnInputBearsALine() {
        assertEquals(BoundaryPolicy.Standing.DrawsALine.class,
                standingAt(10).getClass(),
                "each pass is one occurrence of a position, so a row can be read at it");
    }

    /**
     * The same comparison over a container the input walk names nothing at is a boundary nothing can
     * measure a row against.
     */
    @Test
    void aTruthOneRunReachesMoreThanOnceIsOneNothingCanMeasure() {
        assertEquals(NotABoundary.REPEATED_IN_ONE_RUN, whyOf(standingAt(11)));
    }

    private static NotABoundary whyOf(BoundaryPolicy.Standing standing) {
        return standing instanceof BoundaryPolicy.Standing.DrawsNone none ? none.why() : null;
    }
}
