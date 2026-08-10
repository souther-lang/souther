package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A position this could not read a line at is not a position the model draws no line through.
 *
 * <p>What a reader does not read, it reports as absent, and the two are different things to tell an
 * author. This one names the positions a comparison in the body is written about and this did not
 * turn into a line, so that whatever answers for the position afterwards is not left inferring the
 * model from an empty list.
 *
 * <p>Noticing only. Nothing here is a threshold, and nothing derived from this may become one: which
 * arm witnesses a comparison inside a conjunction is a separate question, and a line recorded without
 * it would be an obligation nobody could meet.
 */
class AComparisonThisDoesNotReadIsStillNoticedTest {

    private static GuardThresholds.Guards read(String condition) {
        return read("n: Count", condition);
    }

    private static GuardThresholds.Guards read(String parameter, String condition) {
        String source = """
                module example.guarded

                data Count = Int
                    invariant range = value >= 0 && value <= 10

                data Low
                data High

                behavior pick : (PARAMETER) -> Low | High
                    constructs Low, High

                let pick (NAME) =
                    if CONDITION
                        then High
                        else Low
                """.replace("PARAMETER", parameter)
                        .replace("NAME", parameter.substring(0, parameter.indexOf(':')).trim())
                        .replace("CONDITION", condition);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Ast.Module prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        TypeChecker.Checked checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, () -> "the model under test compiles: " + condition);
        Ast.SpecBehavior spec = (Ast.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("pick")).findFirst().orElseThrow();
        Core body = checked.behaviorBodies().get("pick");
        assertNotNull(body);
        CoverageSites.Plan plan = CoverageSites.of("m.sou", checked.behaviorBodies());
        return GuardThresholds.of("pick", body, plan,
                spec.params().stream().map(Ast.Param::name).toList(), symbols);
    }

    /** A comparison this reads is not also reported as one it did not. */
    @Test
    void aComparisonThatBecameALineIsNotReportedAsUnread() {
        GuardThresholds.Guards guards = read("n.value <= 5");

        assertEquals(1, guards.thresholds().size());
        assertEquals(List.of(), guards.unread());
    }

    /** A comparison inside a conjunction is read, so it is not one this did not read. */
    @Test
    void aComparisonInsideAConjunctionIsReadRatherThanNamed() {
        GuardThresholds.Guards guards = read("n.value >= 1 && n.value <= 5");

        assertEquals(2, guards.thresholds().size(), guards.thresholds().toString());
        assertEquals(List.of(), guards.unread());
    }

    /**
     * A comparison whose operator draws no line, which is what an equality is.
     *
     * <p>Read as far as naming a position and no further. Whether the two classes an equality divides
     * the values into can be held at all is a separate question; that they are divided is this one.
     */
    @Test
    void anEqualityIsNamedToo() {
        assertEquals(List.of(TermPath.of("n")), read("n.value == 3").unread());
    }

    /**
     * And a comparison whose constant is not a number, which is what a line on a date is.
     *
     * <p>{@code Date} is one of the ordered primitives, so the comparison is ordinary and the branch
     * is real. Nothing downstream can draw a line on it today, which is a fact about the reader.
     */
    @Test
    void aLineDrawnOnADateIsNamedToo() {
        assertEquals(List.of(TermPath.of("on")),
                read("on: Date", "on < Date(\"2026-01-01\")").unread());
    }

    /** One position said once, however many comparisons in the body name it. */
    @Test
    void aPositionIsNamedOnceRatherThanPerComparison() {
        assertEquals(List.of(TermPath.of("n")),
                read("n.value == 1 || n.value /= 3").unread());
    }
}
