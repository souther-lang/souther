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
 * that reads like the first — and the day the reading of a collection's elements arrives, whoever
 * widens it has to work out again why this was ever left out.
 *
 * <p>Asked of the policy and not of a report. No report can tell these apart today: the position a
 * repeated comparison names is one the reading of the inputs stops at for its own reasons, so the
 * two arrive downstream as the same emptiness. That is exactly why the distinction is kept where it
 * is decided.
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

                if cold then kept else xs
            }
            """;

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
                : ComparisonReadings.of(body, plan, InputReads.of(inputs), symbols).all()) {
            byLine.put(each.comparison().pos().line(), each.standing());
        }
        return byLine;
    }

    /** A truth a fork below reads is a line. */
    @Test
    void aTruthSomethingReadsBearsALine() {
        assertEquals(BoundaryPolicy.Standing.DrawsALine.class,
                classified().get(8).getClass());
    }

    /** A truth nothing reads is not a boundary of the behavior at all. */
    @Test
    void aTruthNothingReadsIsNotABoundaryOfTheBehavior() {
        assertEquals(NotABoundary.NOTHING_READS_IT, whyOf(classified().get(9)));
    }

    /** A truth one run reaches once per element is a boundary nothing can measure a row against. */
    @Test
    void aTruthOneRunReachesMoreThanOnceIsOneNothingCanMeasure() {
        assertEquals(NotABoundary.REPEATED_IN_ONE_RUN, whyOf(classified().get(10)));
    }

    private static NotABoundary whyOf(BoundaryPolicy.Standing standing) {
        return standing instanceof BoundaryPolicy.Standing.DrawsNone none ? none.why() : null;
    }
}
