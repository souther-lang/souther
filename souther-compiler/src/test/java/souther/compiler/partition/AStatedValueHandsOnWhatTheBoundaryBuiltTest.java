package souther.compiler.partition;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A field of a value the model states, handed to a container of another parameter, is written as
 * the value the boundary built there — of every shape a field can have.
 *
 * <p>Held by the guard and not by the text alone. The row names the stated value and the set is to
 * hold its key, which nothing in the row writes; the row is past the guard only where what the set
 * was written holding is, once built, the value the key has. A field written back as another value
 * — a decimal at a different number, a record with its fields swapped, a case of another type —
 * leaves the row stopping at the guard, and the text beside it is what a reader is shown.
 *
 * <p>And written the one way. Each value is stated in a spelling a row would not use — a decimal
 * with a trailing zero, a record's fields out of their declared order, a set out of order — and
 * comes back in the spelling every other writer of that value uses, which is what lets two values
 * written apart be compared by their text.
 */
class AStatedValueHandsOnWhatTheBoundaryBuiltTest {

    /** A field's type, the declarations it needs, the value the model states it at, and that
     *  value as a row writes it. */
    record Field(String type, String declared, String stated, String written) {

        @Override
        public String toString() {
            return type + " " + stated;
        }
    }

    static Stream<Field> fields() {
        return Stream.of(
                new Field("Int", "", "7", "7"),
                new Field("Bool", "", "true", "true"),
                new Field("Decimal", "", "1.50m", "1.5m"),
                new Field("String", "", "\"a\\\"b\\\\c\\n\"", "\"a\\\"b\\\\c\\n\""),
                new Field("Date", "", "Date(\"2024-02-29\")", "Date(\"2024-02-29\")"),
                new Field("Code", """
                        data Code = Int
                            invariant value >= 0
                        """, "Code(3)", "Code(3)"),
                new Field("Outer", """
                        data Inner = Int
                        data Outer = Inner
                        """, "Outer(Inner(4))", "Outer(Inner(4))"),
                new Field("Point", "data Point = { x: Int, y: Int }",
                        "Point { y = 2, x = 1 }", "Point { x = 1, y = 2 }"),
                new Field("Colour", """
                        data Red
                        data Blue
                        data Colour = Red | Blue
                        """, "Blue", "Blue"),
                new Field("Size", """
                        data Small = { n: Int }
                        data Large = { n: Int, wide: Bool }
                        data Size = Small | Large
                        """, "Large { wide = true, n = 4 }", "Large { n = 4, wide = true }"),
                new Field("List<Int>", "", "[3, 1, 2]", "[3, 1, 2]"));
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("fields")
    void theFieldIsHandedOnAsBuiltAndTheRowIsPastTheGuard(Field field) {
        Offered offered = offeredFor(field);
        assertEquals("usual", offered.row().get(2),
                () -> "the request is the stated value, written by its name: " + offered);
        Matcher allowed = Pattern.compile("allowed = \\[(.*)]").matcher(offered.row().get(1));
        assertTrue(allowed.find(), () -> "the set is written: " + offered);
        // Among what it holds: a set of a type that divides into cases is filled beside it.
        String holding = ", " + allowed.group(1) + ", ";
        assertTrue(holding.contains(", " + field.written() + ", "),
                () -> "the set holds the key as a row writes it, " + field.written() + ": "
                        + offered);
        assertNull(offered.stop(), () -> "and the row is past the guard: " + offered);
    }

    /** The row offered for one class the guard is not about, and why it stops where it stops. */
    private record Offered(List<String> row, RepairShortfall stop) {}

    private static Offered offeredFor(Field field) {
        String source = """
                module example.settle

                data Plain
                data Express
                data Kind = Plain | Express

                %s

                data Request = { key: %s, note: Int }

                data Other = { allowed: Set<%s> }

                data Done = { n: Int }
                data Refused

                let usual = Request { key = %s, note = 1 }

                behavior settle : (kind: Kind, other: Other, request: Request) -> Done | Refused
                    constructs Done

                let settle (kind, other, request) = {
                    guard Set.contains(request.key, other.allowed) else Refused
                    match kind with
                        | Plain -> Done { n = 2 }
                        | Express -> Done { n = 3 }
                }
                """.formatted(field.declared(), field.type(), field.type(), field.stated());
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all =
                Adequacy.generatedOf(compilation.db(), "example.settle");
        assertNotNull(all, () -> "the model compiles: " + compilation.diagnostics());
        for (FillResult.Offer offer : all.get("settle").composed().offers()) {
            for (Generator.Purpose purpose : offer.row().purposes()) {
                if (purpose instanceof Generator.Purpose.ForAClass forAClass
                        && forAClass.label().equals("kind=Plain")) {
                    return new Offered(
                            offer.row().inputs().stream().map(FixtureTemplate::text).toList(),
                            offer.stop());
                }
            }
        }
        throw new AssertionError("no row is offered for the kind");
    }
}
