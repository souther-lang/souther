package souther.compiler.semantics;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The cases a definition is written in are taken as every way the operation answers only where
 * some one of them is reached however the arguments stand.
 *
 * <p>A reader of the cases reads the operation case by case and nothing else, so a list leaving a
 * way out would have the call read as one of the cases where it is none of them.
 */
class ACaseListIsADefinitionOnlyWhereItCoversEveryWayTest {

    @Test
    void aRelationAndItsDenialCoverEveryWay() {
        assertTrue(DefinitionCase.coverEveryWay(List.of(
                answers("a", List.of(ArgumentsStand.of("a", Rel.LT, "b"))),
                answers("b", List.of(ArgumentsStand.of("a", Rel.GE, "b"))))), "min");
        assertTrue(DefinitionCase.coverEveryWay(List.of(
                answers("a", List.of(ArgumentsStand.of("b", Rel.GT, "a"))),
                answers("b", List.of(ArgumentsStand.of("a", Rel.GE, "b"))))),
                "`b > a` is `a < b`, written the other way round");
        assertTrue(DefinitionCase.coverEveryWay(List.of(
                answers("n", List.of(against("n", Rel.LT, 0))),
                answers("n", List.of(against("n", Rel.GE, 0))))), "abs");
    }

    @Test
    void casesDeniedOneAfterAnotherCoverEveryWay() {
        assertTrue(DefinitionCase.coverEveryWay(List.of(
                answers("lo", List.of(ArgumentsStand.of("n", Rel.LT, "lo"))),
                answers("hi", List.of(ArgumentsStand.of("n", Rel.GE, "lo"),
                        ArgumentsStand.of("n", Rel.GT, "hi"))),
                answers("n", List.of(ArgumentsStand.of("n", Rel.GE, "lo"),
                        ArgumentsStand.of("n", Rel.LE, "hi"))))), "clamp");
    }

    @Test
    void aWayLeftOutIsNoDefinition() {
        assertFalse(DefinitionCase.coverEveryWay(List.of(
                answers("a", List.of(ArgumentsStand.of("a", Rel.LT, "b"))))),
                "min with one case");
        assertFalse(DefinitionCase.coverEveryWay(List.of(
                answers("n", List.of(against("n", Rel.LT, 0))),
                answers("n", List.of(against("n", Rel.GT, 0))))), "nought is reached by neither");
        assertFalse(DefinitionCase.coverEveryWay(List.of(
                answers("lo", List.of(ArgumentsStand.of("n", Rel.LT, "lo"))),
                answers("n", List.of(ArgumentsStand.of("n", Rel.GE, "lo"),
                        ArgumentsStand.of("n", Rel.LE, "hi"))))), "clamp without its middle case");
    }

    private static DefinitionCase<String> answers(String argument,
                                                  List<ArgumentsStand<String>> given) {
        return new DefinitionCase<>(LinearForm.atom(argument), given);
    }

    private static ArgumentsStand<String> against(String argument, Rel rel, long constant) {
        return new ArgumentsStand<>(LinearForm.atom(argument), rel,
                LinearForm.constant(ExactRatio.of(constant)));
    }
}
