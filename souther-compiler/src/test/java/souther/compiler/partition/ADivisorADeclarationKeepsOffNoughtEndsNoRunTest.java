package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A remainder ends a run only on a divisor of nought. Where the declarations hold the divisor to
 * numbers that leave nought out, above it or below it, the comparison of the remainder is read; where
 * they leave nought in, whether the divisor is any {@code Int} or a bounded few, it is unread for a
 * run that may stop.
 */
class ADivisorADeclarationKeepsOffNoughtEndsNoRunTest {

    private static final String BEHAVIOR = """

            behavior %1$s : (eaches: Eaches, pack: %2$s) -> Whole | Part
            let %1$s (eaches, pack) = {
                let leftover = Int.floorMod(eaches.value, pack.value)
                guard leftover == 0 else Part { left = leftover }
                Whole { n = 1 }
            }
            """;

    /** Each behavior by name, with the type its divisor is, which declares what it holds it to. */
    private static final Map<String, String> DIVISORS = Map.of(
            "above", "data PackSize = Int\n    invariant value >= 1",
            "below", "data PackSize = Int\n    invariant value <= -1",
            "any", "data PackSize = Int",
            "aroundNought", "data PackSize = Int\n    invariant value >= -1 && value <= 1");

    /** What the reading of each behavior left unread, by behavior: one model of four behaviors,
     *  compiled and read once for the class. */
    private static final Map<String, PartitionEvidence> READ = read();

    private static Map<String, PartitionEvidence> read() {
        StringBuilder source = new StringBuilder("""
                module m1

                data Eaches = Int
                    invariant value >= 0
                data Whole = { n: Int }
                data Part = { left: Int }
                """);
        DIVISORS.forEach((name, declaration) -> {
            // Each behavior its own divisor type: the module declares each once, under its name.
            String type = "Pack" + name;
            source.append('\n').append(declaration.replace("PackSize", type)).append('\n');
            source.append(BEHAVIOR.formatted(name, type));
        });
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(new Adequacy.Asked(Adequacy.Level.OFF, false));
        ACompiledModel.compiles(compilation);
        Map<String, PartitionEvidence> out =
                compilation.db().ask(new Adequacy.Coverage("m1")).value();
        assertNotNull(out, "the model under test compiles");
        return out;
    }

    private static List<UndividedPosition.Reason> unreadFor(String behavior) {
        PartitionEvidence evidence = READ.get(behavior);
        assertNotNull(evidence, () -> behavior + " is read");
        return evidence.notRead().stream().map(PartitionEvidence.NotRead::reason).distinct()
                .toList();
    }

    @Test
    void aDivisorDeclaredAboveOrBelowNoughtLeavesTheRemainderRead() {
        assertEquals(List.of(), unreadFor("above"));
        assertEquals(List.of(), unreadFor("below"));
    }

    @Test
    void aDivisorDeclaredWithNoughtInItLeavesTheRemainderUnreadForAStop() {
        assertTrue(unreadFor("any").contains(UndividedPosition.Reason.EVALUATION_STOPS_NOT_FULLY_READ));
        assertTrue(unreadFor("aroundNought")
                .contains(UndividedPosition.Reason.EVALUATION_STOPS_NOT_FULLY_READ));
    }
}
