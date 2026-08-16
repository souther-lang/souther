package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * The classes of a position are the values it can hold, and evidence only ever tells them apart
 * more finely.
 *
 * <p>Two rules, and they are the same rule read in the two directions the classes can move in.
 *
 * <p>What a type declares and what a position can hold are separate facts, crossed where the
 * position is read: {@code data StageI = Stage invariant value == Qualified} declares three cases
 * and holds one, and the other two are rows nobody can write (E1903). That crossing was made
 * against the intervals alone, so the same rule written as an ordering took the cases away and the
 * same rule written as an equality did not — which is a partition that turns on how a rule is
 * spelled rather than on what it says.
 *
 * <p>And evidence arriving later refines: a body comparing a position it already has classes for
 * draws a line among them rather than replacing them. Replacement is how a class the model states
 * would come to be lost to a rule the body writes, and the loss reads as the model never having
 * stated it.
 */
class AClassIsOneThePositionCanHoldAndNothingTakesItAwayTest {

    private record Read(Compilation compilation, String module, Hir.SpecBehavior spec, Sig sig,
                        Symbols symbols) {}

    private static Read of(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Symbols symbols = compilation.db().ask(new Shapes.Scope(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
        return new Read(compilation, module, spec, sigs.get(behavior), symbols);
    }

    /** The classes of the one position, off the declarations alone. */
    private static List<String> declared(String source, String behavior) {
        Read read = of(source, behavior);
        return classesOf(Partitions.of(read.spec(), read.sig(), read.symbols(), Exclusions.NONE));
    }

    /** And the same with what the behavior's own body draws taken in. */
    private static List<String> withBody(String source, String behavior) {
        Read read = of(source, behavior);
        Bodies.Elaborated checked =
                read.compilation().db().ask(new Bodies.Checked(read.module())).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        GuardThresholds.Guards guards = GuardThresholds.of(behavior, body,
                CoverageSites.of(checked.behaviorBodies()),
                read.spec().params().stream().map(Hir.Param::name).toList(), read.symbols());
        Partitions.Partitioning base =
                Partitions.of(read.spec(), read.sig(), read.symbols(), Exclusions.NONE);
        return classesOf(Partitions.withThresholds(base, guards.thresholds(), read.symbols(),
                guards.unread(), guards.singled(), guards.between()));
    }

    private static List<String> classesOf(Partitions.Partitioning partitioning) {
        assertEquals(1, partitioning.axes().size(), partitioning.axes().toString());
        return partitioning.axes().get(0).classes().stream().map(PartitionClass::id).toList();
    }

    /**
     * A case the position cannot hold is not one of its classes, whichever way the rule is written.
     *
     * <p>{@code >= Qualified} already took the case away, through the intervals. The equality says
     * the same thing about the same position and left all three, so a row was asked for at two
     * values the constructor refuses.
     */
    @Test
    void anEqualityOverCasesTakesTheOnesItRefusesAway() {
        String model = """
                module g

                data Prospecting
                data Qualified
                data Won
                data Stage = Prospecting | Qualified | Won

                data StageI = Stage
                    invariant value == Qualified

                data Accepted = { at: String }

                behavior classify : (s: StageI) -> Accepted
                """;

        assertEquals(List.of("Qualified"), declared(model, "classify"));
    }

    /** And the same of a boolean, which has two values and a rule can leave one. */
    @Test
    void anEqualityOverABooleanLeavesTheValueItNames() {
        assertEquals(List.of("true"), declared("""
                module g

                data Yes = Bool
                    invariant value == true

                data Accepted = { at: String }

                behavior classify : (y: Yes) -> Accepted
                """, "classify"));
    }

    /** A case the rule leaves is still a class, so the crossing takes away only what it must. */
    @Test
    void aRuleThatRefusesNothingLeavesEveryCase() {
        assertEquals(List.of("Prospecting", "Qualified", "Won"), declared("""
                module g

                data Prospecting
                data Qualified
                data Won
                data Stage = Prospecting | Qualified | Won

                data StageI = Stage

                data Accepted = { at: String }

                behavior classify : (s: StageI) -> Accepted
                """, "classify"));
    }

    /**
     * A line a body draws on a position that already has classes leaves them where they are.
     *
     * <p>The classes the model states are finer than the ranges either side of a line — every value
     * of the position is one of them — so ranges rebuilt from the line would take away distinctions
     * the model already made. The line is still a line and still owes its rows.
     */
    @Test
    void anOrderingInABodyDoesNotReplaceTheClassesTheModelStates() {
        String model = """
                module g

                data Small = Int
                    invariant value == 1 || value == 2

                data Accepted = { at: String }
                data Refused = { at: String }

                behavior classify : (n: Small) -> Accepted | Refused
                    constructs Accepted, Refused

                let classify (n) =
                    if n.value >= 2 then Accepted { at = "x" } else Refused { at = "y" }
                """;

        assertEquals(List.of("1", "2"), declared(model, "classify"));
        assertEquals(List.of("1", "2"), withBody(model, "classify"));
    }

    /** And neither does a body singling a value out: the value already has a class of its own, and
     *  the rest of the position is the other classes rather than one lump of everything else. */
    @Test
    void singlingAValueOutInABodyDoesNotReplaceThemEither() {
        String model = """
                module g

                data Small = Int
                    invariant value == 1 || value == 2

                data Accepted = { at: String }
                data Refused = { at: String }

                behavior classify : (n: Small) -> Accepted | Refused
                    constructs Accepted, Refused

                let classify (n) =
                    if n.value == 1 then Accepted { at = "x" } else Refused { at = "y" }
                """;

        assertEquals(List.of("1", "2"), withBody(model, "classify"));
    }
}
