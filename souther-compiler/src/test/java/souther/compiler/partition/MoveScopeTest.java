package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which positions a search over what a body answers moves is decided by the parameter a position
 * is under, and by nothing about the names: the parameters left standing are the ones asked for and
 * every position under one of them stands, whichever order the parameters are declared in.
 */
class MoveScopeTest {

    private static final String FLAGS = """
            module example.m

            data On
            data Off
            data Flag = On | Off
            data Pair = { left: Flag, right: Flag }

            behavior f : (%s) -> Flag

            let f (%s) = %s
            """;

    private static List<Axis> axesOf(List<String> parameters) {
        StringBuilder declared = new StringBuilder();
        StringBuilder names = new StringBuilder();
        for (String each : parameters) {
            declared.append(declared.isEmpty() ? "" : ", ").append(each).append(": ")
                    .append(each.equals("pair") ? "Pair" : "Flag");
            names.append(names.isEmpty() ? "" : ", ").append(each);
        }
        Compilation compilation = ACompiledModel.answered(
                FLAGS.formatted(declared, names, "On"));
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingContext context =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain domain = InputDomain.of(sigs.get("f"), context,
                TypeCardinality.Counts.workedOutIn(context), Membership.none());
        return Partitions.of("f", domain.reading(rules), ReadAs.THE_COMPILATION_DOES).axes();
    }

    private static Set<String> movedUnder(MoveScope scope, List<Axis> axes) {
        Set<String> moved = new TreeSet<>();
        for (Axis axis : axes) {
            if (scope.moves(axis)) {
                moved.add(axis.path().head());
            }
        }
        return moved;
    }

    @Test
    void whereNothingIsKnownEveryPositionIsMoved() {
        List<Axis> axes = axesOf(List.of("a", "b", "c"));

        assertEquals(Set.of("a", "b", "c"), movedUnder(MoveScope.EVERYTHING, axes));
        assertSame(MoveScope.EVERYTHING, MoveScope.leavingStanding(Set.of()),
                "a body no parameter is known unread of leaves nothing standing");
    }

    @Test
    void thePositionsUnderAParameterTheBodyDoesNotReadStand() {
        List<Axis> axes = axesOf(List.of("a", "b", "c"));

        assertEquals(Set.of("a", "c"),
                movedUnder(MoveScope.leavingStanding(Set.of("b")), axes));
        assertEquals(Set.of(),
                movedUnder(MoveScope.leavingStanding(Set.of("a", "b", "c")), axes));
    }

    @Test
    void everyPositionUnderOneParameterStandsTogether() {
        List<Axis> axes = axesOf(List.of("a", "pair"));
        long underPair = axes.stream().filter(axis -> axis.path().head().equals("pair")).count();

        assertTrue(underPair > 1, "a parameter with two fields has a position for each");
        assertEquals(Set.of("a"),
                movedUnder(MoveScope.leavingStanding(Set.of("pair")), axes));
    }

    @Test
    void whichPositionsStandDoesNotTurnOnTheOrderTheParametersAreDeclaredIn() {
        List<String> names = new ArrayList<>(List.of("a", "b", "c", "d"));
        Set<String> expected = Set.of("a", "d");
        MoveScope scope = MoveScope.leavingStanding(Set.of("b", "c"));

        assertEquals(expected, movedUnder(scope, axesOf(names)));
        Collections.reverse(names);
        assertEquals(expected, movedUnder(scope, axesOf(names)));
        names.add(names.remove(0));
        assertEquals(expected, movedUnder(scope, axesOf(names)));
    }
}
