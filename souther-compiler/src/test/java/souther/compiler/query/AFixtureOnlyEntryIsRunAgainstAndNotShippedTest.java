package souther.compiler.query;

import souther.compiler.check.FixtureValueEntries;
import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.observe.ArmObservation;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fixture's own entry — a private baseline's, or a current-module relay to one another module
 * publishes — is a method a row's own operand is, for the same reason: {@code OperandRunner} is its
 * only caller. What ships carries it no more than it carries a row's operand's own method.
 */
class AFixtureOnlyEntryIsRunAgainstAndNotShippedTest {

    private static final String MODEL = """
            module demo exposing ( settle, Order, Amount, Accepted, Rejected )

            data Amount = Decimal
            data Order = { total: Amount }
            data Accepted
            data Rejected

            let baseline = Order { total = Amount(1.5m) }

            behavior settle : (o: Order) -> Accepted | Rejected

            let settle (o) = if o.total == Amount(1.5m) then Accepted else Rejected

            example settle
                | "a baseline" : (baseline) -> Accepted
            """;

    @Test
    void aPrivateBaselinesFixtureEntryRunsAgainstAndIsNotShipped() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.db().allReports().stream().map(String::valueOf).toList(),
                "the model under test compiles");

        Map<String, ClassFileImage> ships = compilation.db().ask(new Output.Classes("demo")).value();
        EvaluationArtifact runs =
                compilation.db().ask(new Output.Evaluated("demo", ArmObservation.OMIT)).value();
        assertNotNull(ships, "the model under test compiles");
        assertNotNull(runs, "the model under test compiles");

        String fns = SoutherJvmAbi.nameOf(new GeneratedClass.Helpers("demo")).binaryName();
        // The backend writes a `.` in a minted name as `$`, the same as it does for a row's own
        // `$row.0` (`$row$0` on the class); the source-level name stays the address `FixtureReader`
        // looks the entry up by, and this is what it becomes on the method table.
        String entry = FixtureValueEntries.methodFor("demo.baseline").replace('.', '$');

        assertTrue(methodNamesOf(runs.classes().get(fns)).contains(entry),
                "the fixture entry runs where a row's own operand does: "
                        + methodNamesOf(runs.classes().get(fns)));
        assertFalse(methodNamesOf(ships.get(fns)).contains(entry),
                "and does not ship, the same as a row's own operand does not: "
                        + methodNamesOf(ships.get(fns)));
    }

    private static List<String> methodNamesOf(ClassFileImage image) {
        if (image == null) {
            return List.of();
        }
        return ClassFile.of().parse(image.bytes()).methods().stream()
                .map(method -> method.methodName().stringValue())
                .toList();
    }
}
