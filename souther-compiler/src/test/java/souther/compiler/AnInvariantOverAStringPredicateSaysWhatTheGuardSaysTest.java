package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Severity;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A predicate over a string says the same of its length whether it stands in a guard or in the
 * invariant of the type of the string: what the guard takes where the predicate comes out true, the
 * invariant takes of every value of the type, and no more.
 *
 * <p>Each row is a type held to a predicate and a construction over a value of it, owed or not.
 * The pairs are the boundary and one past it, so a row that is not owed is not owed for saying
 * nothing, and the row beside it that is owed says the length was not taken further than the
 * predicate gave it.
 */
class AnInvariantOverAStringPredicateSaysWhatTheGuardSaysTest {

    private record Row(String invariant, String body, boolean owed) {}

    private static final List<Row> ROWS = List.of(
            new Row("String.matches(\"[0-9]{3}\", value)", "String.length(c.value) - 3", false),
            new Row("String.matches(\"[0-9]{3}\", value)", "String.length(c.value) - 4", true),
            new Row("String.matches(\"[0-9]{3}\", value)", "3 - String.length(c.value)", false),
            new Row("String.matches(\"[0-9]{3}\", value)", "2 - String.length(c.value)", true),
            new Row("String.matches(\"[0-9]+\", value)", "String.length(c.value) - 1", false),
            new Row("String.matches(\"[0-9]+\", value)", "String.length(c.value) - 2", true),
            new Row("String.matches(\"[0-9]*\", value)", "String.length(c.value) - 1", true),
            new Row("String.matches(\"[A-Z]{2,4}\", value)", "String.length(c.value) - 2", false),
            new Row("String.matches(\"[A-Z]{2,4}\", value)", "4 - String.length(c.value)", false),
            new Row("String.matches(\"[A-Z]{2,4}\", value)", "3 - String.length(c.value)", true),
            new Row("String.startsWith(\"JP\", value)", "String.length(c.value) - 2", false),
            new Row("String.startsWith(\"JP\", value)", "String.length(c.value) - 3", true),
            new Row("String.contains(\"JP\", value)", "String.length(c.value) - 2", false),
            new Row("String.endsWith(\"JP\", value)", "String.length(c.value) - 2", false),
            // A predicate the type does not hold says nothing of the length.
            new Row("String.length(value) >= 0", "String.length(c.value) - 1", true));

    @Test
    void eachRowIsOwedWhatThePredicateLeavesOpen() {
        List<String> wrong = new ArrayList<>();
        for (Row row : ROWS) {
            boolean owed = owedBy(row);
            if (owed != row.owed()) {
                wrong.add(row.invariant() + " | " + row.body() + ": owed " + owed
                        + ", expected " + row.owed());
            }
        }
        assertEquals(List.of(), wrong, "each row is owed exactly what its predicate leaves open");
    }

    private static boolean owedBy(Row row) {
        String source = """
                module demo

                data Digit = Int
                    invariant atLeastNought = value >= 0

                data Code = String
                    invariant %s

                behavior f : (c: Code) -> Digit
                    constructs Digit
                let f (c) =
                    Digit(%s)
                """.formatted(row.invariant(), row.body());
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        List<String> refused = compilation.errors().stream()
                .filter(each -> !"E2010".equals(each.diagnostic().code()))
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().values()).toList();
        assertTrue(refused.isEmpty(), () -> row + " compiles: " + refused);
        return compilation.errors().size() > refused.size()
                || compilation.warnings().stream().anyMatch(each ->
                each.diagnostic().severity() == Severity.WARNING
                        && "E2011".equals(each.diagnostic().code()));
    }
}
