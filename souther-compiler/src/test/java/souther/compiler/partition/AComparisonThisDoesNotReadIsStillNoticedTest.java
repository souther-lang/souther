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

                data Pair = { x: Int, y: Int }

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
    void anEqualityIsReadRatherThanNamed() {
        GuardThresholds.Guards guards = read("n.value == 3");

        assertEquals(List.of(), guards.unread());
        assertEquals(1, guards.singled().size(), guards.singled().toString());
    }

    /**
     * And a comparison on a carrier whose step is not settled, which a date-time is.
     *
     * <p>A date counts days and is read. A date-time carries a finer step whose size is a decision
     * nobody has taken, and one carrier cannot be both — so the line is left unread, and said as
     * that rather than as a position the model divides no way.
     */
    @Test
    void aLineDrawnOnADateTimeIsNamedToo() {
        assertEquals(List.of(new GuardThresholds.Guards.Unread(TermPath.of("at"),
                        UndividedPosition.Reason.UNSUPPORTED_DOMAIN)),
                read("at: DateTime", "at < DateTime(\"2026-01-01T00:00:00\")").unread());
    }

    /** One position said once, however many comparisons in the body name it. */
    @Test
    void aPositionIsNamedOnceRatherThanPerComparison() {
        assertEquals(1, read("at: DateTime",
                "at < DateTime(\"2026-01-01T00:00:00\")"
                        + " || at > DateTime(\"2020-01-01T00:00:00\")").unread().size());
    }

    /**
     * A position named inside an expression the reader does not model is still named.
     *
     * <p>Discovery and derivation are different questions and must not share a reader. What decides
     * whether a line can be drawn is whether the number compared is one the terms name; what decides
     * whether the model says anything here is whether a comparison mentions the position at all.
     * Asked of the first, `+p.x + 1 < 10+` reports a position the model divides no way, two tokens
     * from a comparison about it.
     */
    @Test
    void aPositionNamedInsideAnExpressionIsStillNoticed() {
        assertEquals(List.of(new GuardThresholds.Guards.Unread(TermPath.of("p").then("x"),
                        UndividedPosition.Reason.UNSUPPORTED_SYNTAX)),
                read("p: Pair", "p.x + 1 < 10").unread());
    }

    /**
     * Two positions compared with each other, which is a relation and not a partition of either.
     *
     * <p>Nothing is wrong with the carrier — both are `+Int+`, ordered, and a line drawn on either
     * against a number would be read. What is missing is a class that is about two positions at
     * once, and saying "no line can be drawn on these values" would send a reader after a carrier.
     */
    @Test
    void twoPositionsComparedWithEachOtherSayWhichLimitThatIs() {
        assertEquals(List.of(
                        new GuardThresholds.Guards.Unread(TermPath.of("p").then("x"),
                                UndividedPosition.Reason.UNSUPPORTED_PARTITION_SHAPE),
                        new GuardThresholds.Guards.Unread(TermPath.of("p").then("y"),
                                UndividedPosition.Reason.UNSUPPORTED_PARTITION_SHAPE)),
                read("p: Pair", "p.x < p.y").unread());
    }
}
