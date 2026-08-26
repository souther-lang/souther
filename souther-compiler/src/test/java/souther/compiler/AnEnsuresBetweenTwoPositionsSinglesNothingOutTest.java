package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The other producer of the same claim, held to the same reading of it.
 *
 * <p>A clause of an {@code ensures} states a comparison the way a body's condition does, so what it
 * places and what it places it about are read the same way. Fixed here as well as for a guard because
 * two producers of one classification are how the classification stops being one.
 */
class AnEnsuresBetweenTwoPositionsSinglesNothingOutTest {

    private static AdequacyReport.BehaviorReport measured(String clause) {
        Compilation compilation = Compilation.ofSource("""
                module m

                data R = { a: Int, other: Int }
                data Ok
                data No

                behavior f : (r: R) -> Ok | No
                    ensures No -> %s
                let f (r) = No

                example f
                    | "one" : (R { a = 1, other = 2 }) -> No
                """.formatted(clause), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().get(0).behaviors().get(0);
    }

    /** The classes the clause divides the behavior's positions into. */
    private static List<String> classes(String clause) {
        return measured(clause).partition().axes().stream()
                .flatMap(each -> each.classes().stream()).toList();
    }

    /** A rule over a pair singles nothing out at either of them. */
    @Test
    void anEqualityBetweenTwoPositionsDividesNeitherOfThem() {
        assertEquals(List.of(), classes("r.a == r.other"));
        assertEquals(List.of(), classes("r.a /= r.other"));
        // The measure's own answer and not a count read off it, which nought would also be where
        // nobody measured: what the rule leaves is no line for a row to be at.
        assertInstanceOf(souther.compiler.query.Measure.NotApplicable.class,
                measured("r.a == r.other").boundaryReadings(),
                "and it is not a line either: the values either side of the place they meet are"
                        + " one class");
    }

    /** While one about a single position still puts the value in a class of its own. */
    @Test
    void andOneAboutASinglePositionStillDoes() {
        assertEquals(List.of("r.a/= 20", "r.a//= 20"), classes("r.a == 20"));
    }

    /**
     * And a clause is read the same way wherever it is written.
     *
     * <p>The guard of the same shape divides the same position into the same two classes. Two
     * producers coming to one answer is the whole of what this file is for, so the two are compared
     * rather than each held to a list somebody wrote out twice.
     */
    @Test
    void andTheSameComparisonInABodyDividesItAlike() {
        Compilation compilation = Compilation.ofSource("""
                module m

                data R = { a: Int, other: Int }
                data Ok
                data No

                behavior f : (r: R) -> Ok | No
                let f (r) = if r.a == 20 then Ok else No

                example f
                    | "one" : (R { a = 1, other = 2 }) -> No
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(classes("r.a == 20"),
                AdequacyReport.of(compilation).modules().get(0).behaviors().get(0)
                        .partition().axes().stream()
                        .flatMap(each -> each.classes().stream()).toList());
    }
}
