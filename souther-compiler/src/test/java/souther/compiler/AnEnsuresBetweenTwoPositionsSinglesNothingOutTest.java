package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Border;
import souther.compiler.partition.DomainPoint;
import souther.compiler.partition.PointRole;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

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

    /**
     * A rule over a pair singles nothing out at either of them, and is a line over the two.
     *
     * <p>The line the guard of the same shape draws, point for point and role for role: the place
     * the two meet and the nearest rows either side of it.
     */
    @Test
    void anEqualityBetweenTwoPositionsDividesNeitherOfThem() {
        assertEquals(List.of(), classes("r.a == r.other"));
        assertEquals(List.of(), classes("r.a /= r.other"));
        for (String clause : List.of("r.a == r.other", "r.a /= r.other")) {
            Map<DomainPoint, PointRole> guarded = rolesOf(AdequacyReport.of(guarded(clause))
                    .modules().get(0).behaviors().get(0));
            assertEquals(5, guarded.size(), () -> clause + ": " + guarded);
            assertEquals(guarded, rolesOf(measured(clause)), clause);
        }
    }

    /** The role of every point of the one line a behavior's rules draw. */
    private static Map<DomainPoint, PointRole> rolesOf(AdequacyReport.BehaviorReport behavior) {
        List<BorderAssessment> lines = behavior.lines();
        assertEquals(1, lines.size(), () -> "one line: " + lines);
        Border border = lines.get(0).border();
        Map<DomainPoint, PointRole> out = new LinkedHashMap<>();
        border.answers().keySet().forEach(point -> out.put(point, border.roleOf(point)));
        return out;
    }

    /** The same comparison as a body's guard, the other producer of the line. */
    private static Compilation guarded(String condition) {
        Compilation compilation = Compilation.ofSource("""
                module m

                data R = { a: Int, other: Int }
                data Ok
                data No

                behavior f : (r: R) -> Ok | No
                let f (r) = if %s then No else Ok

                example f
                    | "one" : (R { a = 1, other = 2 }) -> Ok
                """.formatted(condition), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
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
