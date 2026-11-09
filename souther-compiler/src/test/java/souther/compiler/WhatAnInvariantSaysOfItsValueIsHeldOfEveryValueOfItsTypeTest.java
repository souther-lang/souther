package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.diag.Severity;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An invariant written as a call of the library says of the value what the law of the call says
 * where it holds, so whoever is handed a value of the type holds that of it.
 *
 * <p>Read the way a guard is read: a string a pattern accepts has as many code points as the
 * strings of the pattern do, and a string that starts with another is no shorter than it. Each row
 * is a body over such values, and says whether the discharge owes it anything. The row beside each
 * moves the number by one, so that neither a type that says nothing nor one that says too much
 * passes by it.
 */
class WhatAnInvariantSaysOfItsValueIsHeldOfEveryValueOfItsTypeTest {

    private record Row(String body, boolean owed) {}

    private static final List<Row> ROWS = List.of(
            // A pattern of one length is that length, and of several is between the least and
            // the most of them.
            new Row("Digit(String.length(three.value) - 3)", false),
            new Row("Digit(3 - String.length(three.value))", false),
            new Row("Digit(String.length(three.value) - 4)", true),
            new Row("Digit(4 - String.length(three.value))", false),
            new Row("Digit(2 - String.length(three.value))", true),
            new Row("Digit(String.length(letters.value) - 2)", false),
            new Row("Digit(String.length(letters.value) - 3)", true),
            new Row("Digit(4 - String.length(letters.value))", false),
            new Row("Digit(3 - String.length(letters.value))", true),
            // What starts with something is no shorter than it.
            new Row("Digit(String.length(prefixed.value) - 2)", false),
            new Row("Digit(String.length(prefixed.value) - 3)", true),
            // A type with no rule of this kind says nothing of its length.
            new Row("Digit(String.length(plain.value) - 1)", true),
            // What one of them says of itself is not said of the other.
            new Row("Digit(String.length(three.value) + 1 - String.length(letters.value))", false),
            new Row("Digit(String.length(three.value) - String.length(letters.value))", true));

    private static final String MODEL = """
            module demo

            data Digit = Int
                invariant atLeastNought = value >= 0

            data Three = String
                invariant digits = String.matches("[0-9]{3}", value)

            data Letters = String
                invariant capitals = String.matches("[A-Z]{2,4}", value)

            data Prefixed = String
                invariant japanese = String.startsWith("JP", value)

            data Plain = String

            behavior f : (three: Three, letters: Letters, prefixed: Prefixed, plain: Plain)
                -> Digit
                constructs Digit
            let f (three, letters, prefixed, plain) =
                %s
            """;

    @Test
    void eachRowIsOwedWhatTheInvariantsLeaveOpen() {
        List<String> wrong = new ArrayList<>();
        for (Row row : ROWS) {
            boolean owed = owedBy(row.body());
            if (owed != row.owed()) {
                wrong.add(row.body() + " is owed: " + owed);
            }
        }
        assertEquals(List.of(), wrong, "each row is owed exactly what the invariants leave open");
    }

    /** Whether the discharge leaves anything owed of a behavior with {@code body}. */
    private static boolean owedBy(String body) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(body), "Main");
        compilation.answerEverything();
        List<Located> refused = compilation.errors().stream()
                .filter(each -> !"E2010".equals(each.diagnostic().code())).toList();
        assertTrue(refused.isEmpty(), () -> body + " compiles: "
                + refused.stream().map(each -> each.diagnostic().code() + " "
                        + each.diagnostic().values()).toList());
        return compilation.errors().size() > refused.size()
                || compilation.warnings().stream().anyMatch(each ->
                each.diagnostic().severity() == Severity.WARNING
                        && "E2011".equals(each.diagnostic().code()));
    }
}
